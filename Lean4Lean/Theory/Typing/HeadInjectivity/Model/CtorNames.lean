import Lean4Lean.Theory.Inductive.CompilationNames

/-! # Distinct constructor names of a normalized signature

The constructors of a compiled signature have pairwise distinct names (`ctor_index_inj`), from
the duplicate-free names of the expanded declaration. -/

namespace Lean4Lean.InductiveSignature

theorem flatMap_range_filter_perm {α : Type} (l : List α) (f : α → Nat) :
    ∀ n, ((List.range n).flatMap fun i => l.filter (fun a => f a = i)).Perm
      (l.filter (fun a => f a < n))
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ((flatMap_range_filter_perm l f n).append_right _).trans ?_
    have := List.filter_append_perm (fun a => decide (f a < n)) (l.filter fun a => f a < n + 1)
    refine List.Perm.trans ?_ this
    rw [List.filter_filter, List.filter_filter]
    apply List.Perm.of_eq
    congr 1
    · congr 1; funext a; by_cases h : f a < n <;> simp [h] <;> omega
    · congr 1; funext a; by_cases h : f a < n <;> simp [h] <;> omega

theorem declaration_ctorNames_perm (s : InductiveSignature) :
    (s.declaration.types.flatMap fun t => t.ctors.map (·.name)).Perm
      (s.constructors.toList.map (·.name)) := by
  have e : (s.declaration.types.flatMap fun t => t.ctors.map (·.name)) =
      (List.range s.families.size).flatMap fun i =>
        (s.constructors.toList.filter fun c => c.owner.val = i).map (·.name) := by
    simp only [declaration, List.flatMap_map]
    have h1 : ∀ i : Nat, (s.constructors.toList.filterMap fun ctor =>
        if ctor.owner.val = i then
          some ({ uvars := s.uvars, type := s.constructorType ctor, name := ctor.name } : VConstVal)
        else none).map (·.name) =
        (s.constructors.toList.filter fun c => c.owner.val = i).map (·.name) := by
      intro i
      induction s.constructors.toList with
      | nil => rfl
      | cons c cs ih =>
        simp only [List.filterMap_cons, List.filter_cons]
        by_cases hc : c.owner.val = i
        · simp [hc, ih]
        · simp [hc, ih]
    simp only [h1]
    have h2 : ∀ (l : List Family) (g : Nat → List Name),
        (l.zipIdx.flatMap fun a => g a.2) = (List.range l.length).flatMap g := by
      intro l g
      rw [List.flatMap_def, List.flatMap_def,
        show (l.zipIdx.map fun a => g a.2) = (l.zipIdx.map Prod.snd).map g by
          rw [List.map_map]; rfl, List.zipIdx_map_snd]
      rw [List.range_eq_range']
    rw [h2 s.families.toList (fun i => (s.constructors.toList.filter
      fun c => c.owner.val = i).map (·.name))]
    simp
  rw [e]
  have h := (flatMap_range_filter_perm s.constructors.toList (fun c => c.owner.val)
    s.families.size).map (·.name)
  rw [List.map_flatMap] at h
  refine h.trans (List.Perm.of_eq ?_)
  congr 1
  rw [List.filter_eq_self.2]
  intro c _; simp [c.owner.isLt]


theorem ctor_index_inj {s : InductiveSignature} (hnd : (familyNames s.declaration.types).Nodup)
    {i j : Fin s.constructors.size} (h : s.constructors[i].name = s.constructors[j].name) :
    i = j := by
  have h1 := (familyNames_perm s.declaration.types).nodup_iff.1 hnd
  have h2 := (List.nodup_append.1 h1).2.1
  have h3 := (declaration_ctorNames_perm s).nodup_iff.1 h2
  apply Fin.ext
  have hp := List.pairwise_iff_getElem.1 h3
  have hi : i.val < (s.constructors.toList.map (·.name)).length := by simp
  have hj : j.val < (s.constructors.toList.map (·.name)).length := by simp
  have he : (s.constructors.toList.map (·.name))[i.val] =
      (s.constructors.toList.map (·.name))[j.val] := by simpa using h
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact absurd he (hp _ _ hi hj hlt)
  · exact heq
  · exact absurd he.symm (hp _ _ hj hi hgt)

theorem CompilationData.ctor_index_inj {s : InductiveSignature} {g : Instance s}
    {env : VEnv} {source expanded : VInductDecl} {aux : List ContainerSpecialization}
    {block : VInductBlock} (C : CompilationData env source expanded s g aux block)
    {i j : Fin s.constructors.size} (h : s.constructors[i].name = s.constructors[j].name) :
    i = j :=
  InductiveSignature.ctor_index_inj
    (by rw [C.model.familyNames]; exact familyNames_nodup C.expandedWF.2.1) h

end Lean4Lean.InductiveSignature
