import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Inductive.CaseTypeClosed

/-! Generic facts used to match the case eliminator of a nested declaration's lowered
recursor-checking environment with the restored schema registered by the source block
(`VEnv.RestoredEliminator`): restoration succeeds on the generic case equations of a restoration-free schema whenever it
succeeds on its generic case type (`CaseSchema.genericEquations_restorable`): the equations
are built from the pieces of the case type. -/

namespace Lean4Lean

namespace EnvTables
open InductiveSignature VExpr

theorem restorable_wrapLams (r : Restoration) (doms : List VExpr) (body : VExpr) :
    Restorable r (VExpr.wrapLams doms body) 0 ↔
      (∀ d ∈ doms, Restorable r d 0) ∧ Restorable r body 0 := by
  induction doms with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons] at ih ⊢
    simp only [Restorable, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem restorable_insertBinders {r : Restoration} {l : List VExpr} {k : Nat} :
    (∀ d ∈ insertBinders l k, Restorable r d 0) ↔ ∀ x ∈ l, Restorable r x 0 := by
  constructor
  · intro h x hx
    obtain ⟨j, hj⟩ := mem_insertBinders hx k
    exact (restorable_liftN r k x j 0).mp (h _ hj)
  · intro h d hd
    obtain ⟨⟨x, j⟩, hx, rfl⟩ := List.mem_map.mp hd
    exact (restorable_liftN r k x j 0).mpr (h x (List.fst_mem_of_mem_zipIdx hx))

theorem constructorApp_restorable_iff {s : InductiveSignature} (g : Instance s)
    {r : Restoration} (ctor : Constructor s.families.size) (extra below : Nat) :
    Restorable r (g.constructorApp ctor extra below) 0 ↔
      Restorable r (.const ctor.name g.levels) (s.params.length + ctor.fields.length) := by
  unfold Instance.constructorApp
  rw [restorable_mkApps]
  constructor
  · intro h
    simpa [vars] using h.2
  · intro h
    refine ⟨fun a ha => ?_, by simpa [vars] using h⟩
    rcases List.mem_append.mp ha with ha | ha <;> exact restorable_vars r _ _ a ha

/-- **Restoration succeeds on the generated equations of a constructor without recursive
fields** (in abstract head mode) whenever it succeeds on a generated recursor type: the
equations are built from the parameters, motives and minor premises of the recursor type and
the field types, indices and constructor application of the constructor's minor premise. -/
theorem equation_restorable_of_recursorType {s : InductiveSignature} (g : Instance s)
    {r : Restoration} (owner : Fin s.families.size)
    (h : Restorable r (g.recursorType owner) 0) (index : Fin s.constructors.size)
    (hrec : Instance.recursiveFields s.constructors[index] = []) (block : Name) (first : Nat) :
    Restorable r (g.equation index (.elim block first)).lhs 0 ∧
      Restorable r (g.equation index (.elim block first)).rhs 0 ∧
      Restorable r (g.equation index (.elim block first)).type 0 := by
  unfold Instance.recursorType at h
  rw [restorable_wrapForalls] at h
  obtain ⟨hdoms, -⟩ := h
  have hparams : ∀ p ∈ g.params, Restorable r p 0 := fun p hp => hdoms p (by simp [hp])
  have hmotives : ∀ m ∈ g.motives, Restorable r m 0 := fun m hm => hdoms m (by simp [hm])
  have hminors : ∀ m ∈ g.minors, Restorable r m 0 := fun m hm => hdoms m (by simp [hm])
  have hmem : (s.constructors[index], index.val) ∈ s.constructors.toList.zipIdx := by
    have := mem_zipIdx_getElem s.constructors.toList index.val (by simp)
    simpa using this
  have hminor : Restorable r (g.minor s.constructors[index] index.val) 0 :=
    hminors _ (List.mem_map.2 ⟨_, hmem, rfl⟩)
  simp only [Instance.minor] at hminor
  rw [restorable_wrapForalls, restorable_mkApps] at hminor
  obtain ⟨hfdoms, hargs, -⟩ := hminor
  have hfields : ∀ d ∈ insertBinders ((s.fieldTypes s.constructors[index]).map
      (·.instL g.levels)) (s.families.size + s.constructors.size), Restorable r d 0 := by
    refine restorable_insertBinders.mpr fun x hx => ?_
    have := restorable_insertBinders.mp
      (fun d hd => hfdoms d (List.mem_append_left _ hd)) x hx
    exact this
  have hindices : ∀ e ∈ s.constructors[index].indices, Restorable r (e.instL g.levels) 0 := by
    intro e he
    have := hargs _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    rwa [restorable_liftN, restorable_liftN] at this
  have hctor : Restorable r (.const s.constructors[index].name g.levels)
      (s.params.length + s.constructors[index].fields.length) :=
    (constructorApp_restorable_iff g _ _ _).mp
      (hargs _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hdomains : ∀ d ∈ g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + s.constructors.size), Restorable r d 0 := by
    intro d hd
    simp only [List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact hparams d hd
    · exact hmotives d hd
    · exact hminors d hd
    · exact hfields d hd
  have hidx : ∀ a ∈ s.constructors[index].indices.map fun e =>
      (e.instL g.levels).liftN (s.families.size + s.constructors.size)
        s.constructors[index].fields.length, Restorable r a 0 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    rw [restorable_liftN]
    exact hindices e he
  have hmajor : Restorable r (g.constructorApp s.constructors[index]
      (s.families.size + s.constructors.size) 0) 0 :=
    (constructorApp_restorable_iff g _ _ _).mpr hctor
  unfold Instance.equation
  simp only [hrec, List.map_nil, List.append_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [restorable_wrapLams, restorable_mkApps]
    refine ⟨hdomains, fun a ha => ?_, trivial⟩
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact restorable_vars r _ _ a ha
    · exact hidx a ha
    · exact hmajor
  · rw [restorable_wrapLams, restorable_mkApps]
    exact ⟨hdomains, fun a ha => restorable_vars r _ _ a ha, trivial⟩
  · rw [restorable_wrapForalls, restorable_mkApps]
    refine ⟨hdomains, fun a ha => ?_, trivial⟩
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hidx a ha
    · exact hmajor

end EnvTables

namespace InductiveSignature.CaseSchema
open EnvTables

/-- **Restoration succeeds on the generic case equations of a restoration-free schema whose
generic case type it restores.** -/
theorem genericEquations_restorable {schema : CaseSchema} (h0 : schema.restoration = {})
    {r : Restoration} (block : Name) (owner : Fin schema.signature.families.size)
    (htype : ∀ type, schema.genericType owner = some type → (r.expr type).isSome)
    {rules : List VDefEq} (h : schema.genericEquations block owner = some rules) :
    ∀ df ∈ rules, (r.equation df).isSome := by
  simp only [genericEquations, CaseSchema.equations, h0] at h
  have hrules : ∀ (l rules : List VDefEq), l.mapM ({} : Restoration).equation = some rules →
      rules = l := by
    intro l
    induction l with
    | nil => intro rules h; simpa using h.symm
    | cons a l ih =>
      intro rules h
      rw [List.mapM_cons, Restoration.equation_empty] at h
      cases hl : l.mapM ({} : Restoration).equation with
      | none => simp [hl] at h
      | some l' =>
        simp [hl] at h
        subst h
        rw [ih l' hl]
  intro df hdf
  rw [hrules _ _ h] at hdf
  unfold Instance.equations at hdf
  obtain ⟨index, -, rfl⟩ := List.mem_map.1 hdf
  have ht := htype ((schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0)).recursorType (schema.viewOwner owner))
    (by simp only [genericType, CaseSchema.type, h0, Restoration.expr_empty])
  have hOK : Restorable r ((schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0)).recursorType (schema.viewOwner owner)) 0 := by
    simpa using (restore_go_isSome r _ []).mp ht
  have hrec : Instance.recursiveFields (schema.view owner).constructors[index] = [] := by
    have hmemc : (schema.view owner).constructors[index] ∈
        (schema.view owner).constructors.toList := Array.getElem_mem_toList _
    obtain ⟨c, -, -, hc⟩ := view_constructors_mem hmemc
    rw [hc]
    exact InductiveSignature.CaseSchema.caseConstructor_recursiveFields c
  obtain ⟨hl, hr, hty⟩ := equation_restorable_of_recursorType _ _ hOK index hrec
    block owner.val
  have hl' := (restore_go_isSome r _ []).mpr (by simpa using hl)
  have hr' := (restore_go_isSome r _ []).mpr (by simpa using hr)
  have hty' := (restore_go_isSome r _ []).mpr (by simpa using hty)
  obtain ⟨l', hl''⟩ := Option.isSome_iff_exists.mp hl'
  obtain ⟨r', hr''⟩ := Option.isSome_iff_exists.mp hr'
  obtain ⟨t', ht''⟩ := Option.isSome_iff_exists.mp hty'
  change (Restoration.expr r _).isSome = true at *
  simp [Restoration.equation, Restoration.expr, hl'', hr'', ht'']

end InductiveSignature.CaseSchema

end Lean4Lean
