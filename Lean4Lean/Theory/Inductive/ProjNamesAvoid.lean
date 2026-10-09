import Lean4Lean.Theory.Inductive.CaseFormation

/-! # Avoided projection names of generated terms

`VExpr.projNamesAvoid names e`: no projection node of `e` is out of a name in `names`; and how the
signature generator's constructions preserve it. -/

namespace Lean4Lean
open InductiveSignature

namespace VExpr

/-- No projection type name of the term is in `names`. -/
def projNamesAvoid (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ | .const .. | .elim .. => true
  | .app f a | .lam f a | .forallE f a => f.projNamesAvoid names && a.projNamesAvoid names
  | .proj n _ e => !names.contains n && e.projNamesAvoid names

theorem ProjNamesOK.and {ok ok' : Name → Prop} :
    ∀ {e : VExpr}, e.ProjNamesOK ok → e.ProjNamesOK ok' →
      e.ProjNamesOK fun s => ok s ∧ ok' s
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .elim .., _, _ => trivial
  | .app _ _, h, h' => ⟨ProjNamesOK.and h.1 h'.1, ProjNamesOK.and h.2 h'.2⟩
  | .lam _ _, h, h' => ⟨ProjNamesOK.and h.1 h'.1, ProjNamesOK.and h.2 h'.2⟩
  | .forallE _ _, h, h' => ⟨ProjNamesOK.and h.1 h'.1, ProjNamesOK.and h.2 h'.2⟩
  | .proj _ _ _, h, h' => ⟨⟨h.1, h'.1⟩, ProjNamesOK.and h.2 h'.2⟩

theorem ProjNamesOK.projNamesAvoid {ok : Name → Prop} {names : List Name}
    (hok : ∀ s, ok s → s ∉ names) :
    ∀ {e : VExpr}, e.ProjNamesOK ok → e.projNamesAvoid names = true
  | .bvar _, _ | .sort _, _ | .const .., _ | .elim .., _ => rfl
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true]
    exact ⟨ProjNamesOK.projNamesAvoid hok h.1, ProjNamesOK.projNamesAvoid hok h.2⟩
  | .proj _ _ _, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by simpa using hok _ h.1, ProjNamesOK.projNamesAvoid hok h.2⟩

/-! #### `projNamesAvoid` under the generator's constructions -/

@[simp] theorem projNamesAvoid_liftN (names : List Name) (n : Nat) :
    ∀ (e : VExpr) (k : Nat), (e.liftN n k).projNamesAvoid names = e.projNamesAvoid names
  | .bvar _, _ | .sort _, _ | .const .., _ | .elim .., _ => rfl
  | .app f a, k | .lam f a, k | .forallE f a, k => by
    simp [VExpr.liftN, VExpr.projNamesAvoid, projNamesAvoid_liftN]
  | .proj _ _ e, k => by
    simp [VExpr.liftN, VExpr.projNamesAvoid, projNamesAvoid_liftN]

@[simp] theorem projNamesAvoid_instL (names : List Name) (ls : List VLevel) :
    ∀ e : VExpr, (e.instL ls).projNamesAvoid names = e.projNamesAvoid names
  | .bvar _ | .sort _ | .const .. | .elim .. => rfl
  | .app f a | .lam f a | .forallE f a => by
    simp [VExpr.instL, VExpr.projNamesAvoid, projNamesAvoid_instL]
  | .proj _ _ e => by
    simp [VExpr.instL, VExpr.projNamesAvoid, projNamesAvoid_instL]

theorem projNamesAvoid_mkApps_iff {names : List Name} (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).projNamesAvoid names = true ↔
      fn.projNamesAvoid names = true ∧ ∀ a ∈ args, a.projNamesAvoid names = true := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
    rw [show VExpr.mkApps fn (arg :: args) = VExpr.mkApps (.app fn arg) args by rfl, ih]
    simp [projNamesAvoid, and_assoc]

theorem projNamesAvoid_wrapForalls_iff {names : List Name} {domains : List VExpr}
    {body : VExpr} :
    (VExpr.wrapForalls domains body).projNamesAvoid names = true ↔
      (∀ d ∈ domains, d.projNamesAvoid names = true) ∧ body.projNamesAvoid names = true := by
  induction domains with
  | nil => simp [VExpr.wrapForalls]
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at ih ⊢
    simp [projNamesAvoid, ih, and_assoc]

theorem projNamesAvoid_wrapLams_iff {names : List Name} {domains : List VExpr}
    {body : VExpr} :
    (VExpr.wrapLams domains body).projNamesAvoid names = true ↔
      (∀ d ∈ domains, d.projNamesAvoid names = true) ∧ body.projNamesAvoid names = true := by
  induction domains with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons] at ih ⊢
    simp [projNamesAvoid, ih, and_assoc]

theorem projNamesAvoid_mono {names names' : List Name} (hsub : ∀ n ∈ names', n ∈ names) :
    ∀ {e : VExpr}, e.projNamesAvoid names = true → e.projNamesAvoid names' = true
  | .bvar _, _ | .sort _, _ | .const .., _ | .elim .., _ => rfl
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true] at h ⊢
    exact ⟨projNamesAvoid_mono hsub h.1, projNamesAvoid_mono hsub h.2⟩
  | .proj _ _ _, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at h ⊢
    exact ⟨fun hm => h.1 (hsub _ hm), projNamesAvoid_mono hsub h.2⟩

end VExpr

/-! ### Generated equations from generated recursor types

The pieces of every generated equation (parameters, motives, minor premises,
field types, constructor indices, and the induction-hypothesis binders and
indices of the recursive calls) all occur in every generated recursor type,
up to lifting and universe instantiation, which keep projection names. -/

namespace InductiveSignature

private theorem forall_zipIdx_map_iff {α : Type} {P : VExpr → Prop} {Q : α → Prop}
    {f : α × Nat → VExpr} (h : ∀ a i, P (f (a, i)) ↔ Q a) :
    ∀ (l : List α) (k : Nat), (∀ d ∈ (l.zipIdx k).map f, P d) ↔ ∀ a ∈ l, Q a
  | [], _ => by simp
  | a :: l, k => by
    simp only [List.zipIdx_cons, List.map_cons, List.mem_cons, forall_eq_or_imp, h a k,
      forall_zipIdx_map_iff h l (k + 1)]

private theorem exists_mem_zipIdx {α : Type} {a : α} :
    ∀ {l : List α} (k : Nat), a ∈ l → ∃ i, (a, i) ∈ l.zipIdx k
  | [], _, h => by simp at h
  | b :: l, k, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨k, by simp⟩
    · obtain ⟨i, hi⟩ := exists_mem_zipIdx (k + 1) h
      exact ⟨i, by simp [hi]⟩

private theorem mem_zipIdx_getElem {α : Type} :
    ∀ (l : List α) (k i : Nat) (hi : i < l.length), (l[i], k + i) ∈ l.zipIdx k
  | [], _, _, hi => by simp at hi
  | a :: l, k, 0, _ => by simp
  | a :: l, k, i + 1, hi => by
    simp only [List.zipIdx_cons, List.getElem_cons_succ, List.mem_cons]
    right
    have := mem_zipIdx_getElem l (k + 1) i (by simpa using hi)
    rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem vars_projNamesAvoid {names : List Name} (count below : Nat) :
    ∀ e ∈ vars count below, e.projNamesAvoid names = true := by
  intro e he
  simp only [vars, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  rfl

theorem insertBinders_projNamesAvoid_iff {names : List Name} {domains : List VExpr}
    {count : Nat} :
    (∀ d ∈ insertBinders domains count, d.projNamesAvoid names = true) ↔
      ∀ e ∈ domains, e.projNamesAvoid names = true := by
  unfold insertBinders
  refine forall_zipIdx_map_iff (P := fun d => d.projNamesAvoid names = true)
    (Q := fun e => e.projNamesAvoid names = true) (fun a i => ?_) domains 0
  simp

namespace Instance

variable {s : InductiveSignature} (g : Instance s) {names : List Name}

/-- The pieces of a recursive field avoid `names`. -/
def RecursiveAvoids (names : List Name) (g : Instance s) (r : Recursive s.families.size) :
    Prop :=
  (∀ b ∈ r.binders, (b.instL g.levels).projNamesAvoid names = true) ∧
    ∀ x ∈ r.indices, (x.instL g.levels).projNamesAvoid names = true

theorem hypothesis_projNamesAvoid_iff (ctor : Constructor s.families.size)
    (priorMinors priorIHs field : Nat) (r : Recursive s.families.size) :
    (g.hypothesis ctor priorMinors priorIHs field r).projNamesAvoid names = true ↔
      RecursiveAvoids names g r := by
  dsimp only [hypothesis, RecursiveAvoids, underFields]
  rw [VExpr.projNamesAvoid_wrapForalls_iff, VExpr.projNamesAvoid_mkApps_iff]
  simp only [VExpr.projNamesAvoid, true_and, List.mem_append, List.mem_singleton]
  refine and_congr ?_ ?_
  · refine forall_zipIdx_map_iff (P := fun d => d.projNamesAvoid names = true)
      (Q := fun b => (b.instL g.levels).projNamesAvoid names = true)
      (fun a i => ?_) r.binders 0
    simp
  · constructor
    · intro h x hx
      have := h _ (.inl (List.mem_map_of_mem hx))
      simpa using this
    · intro h a ha
      rcases ha with ha | rfl
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        simpa using h x hx
      · exact (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, vars_projNamesAvoid _ _⟩

theorem recursiveCall_projNamesAvoid (ctor : Constructor s.families.size) (field : Nat)
    (r : Recursive s.families.size) (mode : HeadMode) (h : RecursiveAvoids names g r) :
    (g.recursiveCall ctor field r mode).projNamesAvoid names = true := by
  dsimp only [recursiveCall, underFields]
  rw [VExpr.projNamesAvoid_wrapLams_iff, VExpr.projNamesAvoid_mkApps_iff]
  refine ⟨(forall_zipIdx_map_iff (P := fun d => d.projNamesAvoid names = true)
      (Q := fun b => (b.instL g.levels).projNamesAvoid names = true)
      (fun a i => by simp) r.binders 0).2 h.1, ?_, ?_⟩
  · cases mode <;> rfl
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact vars_projNamesAvoid _ _ a ha
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      simpa using h.2 x hx
    · exact (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, vars_projNamesAvoid _ _⟩

theorem constructorApp_projNamesAvoid (ctor : Constructor s.families.size)
    (extra below : Nat) : (g.constructorApp ctor extra below).projNamesAvoid names = true := by
  unfold constructorApp
  refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, fun a ha => ?_⟩
  rcases List.mem_append.1 ha with ha | ha <;> exact vars_projNamesAvoid _ _ a ha

/-- The pieces of a constructor avoid `names`. -/
structure CtorAvoids (names : List Name) (g : Instance s) (ctor : Constructor s.families.size) :
    Prop where
  fields : ∀ e ∈ s.fieldTypes ctor, (e.instL g.levels).projNamesAvoid names = true
  indices : ∀ e ∈ ctor.indices, (e.instL g.levels).projNamesAvoid names = true
  recursive : ∀ p ∈ recursiveFields ctor, RecursiveAvoids names g p.2

theorem ctorAvoids_of_minor (ctor : Constructor s.families.size) (prior : Nat)
    (h : (g.minor ctor prior).projNamesAvoid names = true) : CtorAvoids names g ctor := by
  dsimp only [minor] at h
  rw [VExpr.projNamesAvoid_wrapForalls_iff, VExpr.projNamesAvoid_mkApps_iff] at h
  obtain ⟨hdoms, -, hargs⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := insertBinders_projNamesAvoid_iff.1 fun d hd => hdoms d (List.mem_append_left _ hd)
    intro e he
    simpa using this _ (List.mem_map_of_mem he)
  · intro e he
    have := hargs _ (List.mem_append_left _ (List.mem_map_of_mem he))
    simpa using this
  · intro p hp
    obtain ⟨i, hi⟩ := exists_mem_zipIdx 0 hp
    obtain ⟨field, r⟩ := p
    have := hdoms _ (List.mem_append_right _ (List.mem_map.2 ⟨((field, r), i), hi, rfl⟩))
    exact (hypothesis_projNamesAvoid_iff g ctor prior i field r).1 this

theorem recursorType_domains (owner : Fin s.families.size)
    (h : (g.recursorType owner).projNamesAvoid names = true) :
    (∀ p ∈ g.params, p.projNamesAvoid names = true) ∧
      (∀ m ∈ g.motives, m.projNamesAvoid names = true) ∧
      ∀ m ∈ g.minors, m.projNamesAvoid names = true := by
  unfold recursorType at h
  rw [VExpr.projNamesAvoid_wrapForalls_iff] at h
  exact ⟨fun p hp => h.1 p (by simp [hp]), fun m hm => h.1 m (by simp [hm]),
    fun m hm => h.1 m (by simp [hm])⟩

/-- **Generated equations avoid the projection names avoided by a generated
recursor type.** -/
theorem equation_projNamesAvoid_of_recursorType (owner : Fin s.families.size)
    (h : (g.recursorType owner).projNamesAvoid names = true)
    (index : Fin s.constructors.size) (mode : HeadMode) :
    (g.equation index mode).lhs.projNamesAvoid names = true ∧
      (g.equation index mode).rhs.projNamesAvoid names = true ∧
      (g.equation index mode).type.projNamesAvoid names = true := by
  obtain ⟨hparams, hmotives, hminors⟩ := g.recursorType_domains owner h
  have hmem : (s.constructors[index], 0 + index.val) ∈ s.constructors.toList.zipIdx 0 := by
    have := mem_zipIdx_getElem s.constructors.toList 0 index.val (by simp)
    simpa using this
  have hminor : (g.minor s.constructors[index] index.val).projNamesAvoid names = true :=
    hminors _ (List.mem_map.2 ⟨_, hmem, by simp⟩)
  have C := g.ctorAvoids_of_minor _ _ hminor
  have hdomains : ∀ d ∈ g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + s.constructors.size), d.projNamesAvoid names = true := by
    intro d hd
    simp only [List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact hparams d hd
    · exact hmotives d hd
    · exact hminors d hd
    · refine insertBinders_projNamesAvoid_iff.2 ?_ d hd
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      exact C.fields e0 he0
  have hindices : ∀ e ∈ s.constructors[index].indices.map fun e =>
      (e.instL g.levels).liftN (s.families.size + s.constructors.size)
        s.constructors[index].fields.length, e.projNamesAvoid names = true := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    simpa using C.indices e0 he0
  have hmajor := g.constructorApp_projNamesAvoid (names := names) s.constructors[index]
    (s.families.size + s.constructors.size) 0
  unfold equation
  refine ⟨?_, ?_, ?_⟩
  · refine VExpr.projNamesAvoid_wrapLams_iff.2 ⟨hdomains, ?_⟩
    refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨by cases mode <;> rfl, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact vars_projNamesAvoid _ _ a ha
    · exact hindices a ha
    · exact hmajor
  · refine VExpr.projNamesAvoid_wrapLams_iff.2 ⟨hdomains, ?_⟩
    refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, ?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact vars_projNamesAvoid _ _ a ha
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact g.recursiveCall_projNamesAvoid _ _ _ _ (C.recursive p hp)
  · refine VExpr.projNamesAvoid_wrapForalls_iff.2 ⟨hdomains, ?_⟩
    refine (VExpr.projNamesAvoid_mkApps_iff _ _).2 ⟨rfl, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hindices a ha
    · exact hmajor

end Instance

end InductiveSignature


end Lean4Lean
