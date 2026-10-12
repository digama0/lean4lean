import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Theory.Typing.RestorationShapes

/-! Totality of restoration on generated syntax (`Restoration.SpineOK`,
`Instance.restoredEquations_isSome`). -/

namespace Lean4Lean
namespace InductiveSignature

/-! ### Totality of restoration

`Restoration.expr` fails exactly at a restoration head applied to fewer
arguments than its parameter count, or at the wrong universe arity.
`Restoration.SpineOK r e k` states that neither happens in `e` when `e` is
applied to `k` further arguments. -/

/-- No restoration head of `e`, applied to `k` further arguments, is partially
applied or at the wrong universe arity. -/
def Restoration.SpineOK (r : Restoration) : VExpr → Nat → Prop
  | .app f a, k => r.SpineOK f (k + 1) ∧ r.SpineOK a 0
  | .const name levels, k => ∀ h, r.heads.find? (fun h => h.auxiliary == name) = some h →
      levels.length = h.uvars ∧ h.nparams ≤ k
  | .lam d b, _ => r.SpineOK d 0 ∧ r.SpineOK b 0
  | .forallE d b, _ => r.SpineOK d 0 ∧ r.SpineOK b 0
  | .proj _ _ e, _ => r.SpineOK e 0
  | .bvar _, _ => True
  | .sort _, _ => True

theorem Restoration.go_isSome_of_spineOK (r : Restoration) :
    ∀ (e : VExpr) (args : List VExpr), r.SpineOK e args.length →
      ∃ v, Restoration.expr.go r e args = some v
  | .bvar i, args, _ => ⟨_, rfl⟩
  | .sort u, args, _ => ⟨_, rfl⟩
  | .app f a, args, H => by
    obtain ⟨a', ha⟩ := r.go_isSome_of_spineOK a [] H.2
    obtain ⟨v, hv⟩ := r.go_isSome_of_spineOK f (a' :: args) H.1
    exact ⟨v, by simp only [Restoration.expr.go, ha, Option.bind_eq_bind,
      Option.bind_some, hv]⟩
  | .const name levels, args, H => by
    simp only [Restoration.expr.go]
    cases hf : r.heads.find? (fun h => h.auxiliary == name) with
    | none => exact ⟨_, rfl⟩
    | some h =>
      obtain ⟨hl, hn⟩ := H h hf
      simp only [HeadSpecialization.apply, hl, bne_self_eq_false, Bool.false_or]
      have : ¬ args.length < h.nparams := by omega
      simp [this]
  | .lam d b, args, H => by
    obtain ⟨d', hd⟩ := r.go_isSome_of_spineOK d [] H.1
    obtain ⟨b', hb⟩ := r.go_isSome_of_spineOK b [] H.2
    exact ⟨_, by simp only [Restoration.expr.go, hd, hb, Option.bind_eq_bind,
      Option.bind_some]; rfl⟩
  | .forallE d b, args, H => by
    obtain ⟨d', hd⟩ := r.go_isSome_of_spineOK d [] H.1
    obtain ⟨b', hb⟩ := r.go_isSome_of_spineOK b [] H.2
    exact ⟨_, by simp only [Restoration.expr.go, hd, hb, Option.bind_eq_bind,
      Option.bind_some]; rfl⟩
  | .proj n i e, args, H => by
    obtain ⟨e', he⟩ := r.go_isSome_of_spineOK e [] H
    exact ⟨_, by simp only [Restoration.expr.go, he, Option.bind_eq_bind,
      Option.bind_some]; rfl⟩

theorem Restoration.spineOK_of_go (r : Restoration) :
    ∀ (e : VExpr) (args : List VExpr) (v : VExpr),
      Restoration.expr.go r e args = some v → r.SpineOK e args.length
  | .bvar i, args, _, _ => by simp [Restoration.SpineOK]
  | .sort u, args, _, _ => by simp [Restoration.SpineOK]
  | .app f a, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases ha : Restoration.expr.go r a [] with
    | none => simp [ha] at H
    | some a' =>
      simp only [ha, Option.bind_some] at H
      exact ⟨r.spineOK_of_go f (a' :: args) v H, r.spineOK_of_go a [] a' ha⟩
  | .const name levels, args, v, H => by
    intro h hf
    simp only [Restoration.expr.go, hf, HeadSpecialization.apply] at H
    by_cases hl : levels.length = h.uvars
    · by_cases hn : args.length < h.nparams
      · simp [hl, hn] at H
      · exact ⟨hl, by omega⟩
    · simp [hl] at H
  | .lam d b, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases hd : Restoration.expr.go r d [] with
    | none => simp [hd] at H
    | some d' =>
      cases hb : Restoration.expr.go r b [] with
      | none => simp [hd, hb] at H
      | some b' => exact ⟨r.spineOK_of_go d [] d' hd, r.spineOK_of_go b [] b' hb⟩
  | .forallE d b, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases hd : Restoration.expr.go r d [] with
    | none => simp [hd] at H
    | some d' =>
      cases hb : Restoration.expr.go r b [] with
      | none => simp [hd, hb] at H
      | some b' => exact ⟨r.spineOK_of_go d [] d' hd, r.spineOK_of_go b [] b' hb⟩
  | .proj n i e, args, v, H => by
    simp only [Restoration.expr.go, Option.bind_eq_bind] at H
    cases he : Restoration.expr.go r e [] with
    | none => simp [he] at H
    | some e' => exact r.spineOK_of_go e [] e' he

/-- Restoration is defined exactly on the expressions without partially
applied restoration heads. -/
theorem Restoration.expr_isSome_iff (r : Restoration) (e : VExpr) :
    (∃ v, r.expr e = some v) ↔ r.SpineOK e 0 :=
  ⟨fun ⟨v, h⟩ => r.spineOK_of_go e [] v h, fun h => r.go_isSome_of_spineOK e [] h⟩

theorem Restoration.spineOK_mkApps (r : Restoration) :
    ∀ (f : VExpr) (args : List VExpr) (k : Nat),
      r.SpineOK (VExpr.mkApps f args) k ↔
        r.SpineOK f (k + args.length) ∧ ∀ a ∈ args, r.SpineOK a 0
  | f, [], k => by simp [VExpr.mkApps]
  | f, a :: as, k => by
    have hm : VExpr.mkApps f (a :: as) = VExpr.mkApps (.app f a) as := rfl
    rw [hm, r.spineOK_mkApps (.app f a) as k]
    simp only [Restoration.SpineOK, List.mem_cons, forall_eq_or_imp, List.length_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by rwa [show k + (as.length + 1) = k + as.length + 1 by omega], h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by rwa [show k + (as.length + 1) = k + as.length + 1 by omega] at h1, h2⟩, h3⟩

theorem Restoration.spineOK_wrapForalls (r : Restoration) :
    ∀ (ds : List VExpr) (b : VExpr),
      r.SpineOK (VExpr.wrapForalls ds b) 0 ↔ (∀ d ∈ ds, r.SpineOK d 0) ∧ r.SpineOK b 0
  | [], b => by simp [VExpr.wrapForalls]
  | d :: ds, b => by
    have := r.spineOK_wrapForalls ds b
    simp only [VExpr.wrapForalls, List.foldr_cons] at this ⊢
    simp only [Restoration.SpineOK, this, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem Restoration.spineOK_wrapLams (r : Restoration) :
    ∀ (ds : List VExpr) (b : VExpr),
      r.SpineOK (VExpr.wrapLams ds b) 0 ↔ (∀ d ∈ ds, r.SpineOK d 0) ∧ r.SpineOK b 0
  | [], b => by simp [VExpr.wrapLams]
  | d :: ds, b => by
    have := r.spineOK_wrapLams ds b
    simp only [VExpr.wrapLams, List.foldr_cons] at this ⊢
    simp only [Restoration.SpineOK, this, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem Restoration.spineOK_liftN (r : Restoration) (n : Nat) :
    ∀ (e : VExpr) (j k : Nat), r.SpineOK (e.liftN n j) k ↔ r.SpineOK e k
  | .bvar i, j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .sort u, j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .const c us, j, k => by simp [VExpr.liftN, Restoration.SpineOK]
  | .app f a, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n f, r.spineOK_liftN n a]
  | .proj m i e, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n e]
  | .lam d b, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n d, r.spineOK_liftN n b]
  | .forallE d b, j, k => by
    simp only [VExpr.liftN, Restoration.SpineOK, r.spineOK_liftN n d, r.spineOK_liftN n b]

theorem Restoration.spineOK_vars (r : Restoration) (n below : Nat) :
    ∀ a ∈ vars n below, r.SpineOK a 0 := by
  intro a ha
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at ha
  obtain ⟨_, _, rfl⟩ := ha
  trivial


theorem Restoration.spineOK_insertBinders (r : Restoration) (ds : List VExpr) (c : Nat) :
    (∀ d ∈ insertBinders ds c, r.SpineOK d 0) ↔ ∀ d ∈ ds, r.SpineOK d 0 := by
  simp only [insertBinders, List.mem_map, Prod.exists, forall_exists_index, and_imp]
  constructor
  · intro H d hd
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    have := H _ d i (List.mk_mem_zipIdx_iff_getElem?.mpr hi) rfl
    exact (r.spineOK_liftN c d i 0).mp this
  · rintro H _ d i hdi rfl
    exact (r.spineOK_liftN c d i 0).mpr (H d (List.fst_mem_of_mem_zipIdx hdi))

theorem mem_zipIdx_of_mem {l : List α} {x : α} (h : x ∈ l) :
    ∃ i, (x, i) ∈ l.zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i, List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩

theorem Restoration.spineOK_constructorApp (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (ctor : Constructor s.families.size) (extra below : Nat) :
    r.SpineOK (g.constructorApp ctor extra below) 0 ↔
      r.SpineOK (.const ctor.name g.levels) (s.params.length + ctor.fields.length) := by
  rw [Instance.constructorApp, r.spineOK_mkApps]
  simp only [List.length_append, vars, List.length_map, List.length_reverse,
    List.length_range, Nat.zero_add]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at ha
    rcases ha with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

/-- The pieces of a minor premise whose restoration determines the
restoration of the corresponding equation. -/
structure Restoration.MinorPiecesOK (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (ctor : Constructor s.families.size) : Prop where
  fields : ∀ d ∈ (s.fieldTypes ctor).map (·.instL g.levels), r.SpineOK d 0
  indices : ∀ e ∈ ctor.indices, r.SpineOK (e.instL g.levels) 0
  head : r.SpineOK (.const ctor.name g.levels) (s.params.length + ctor.fields.length)
  binders : ∀ fr ∈ Instance.recursiveFields (s := s) ctor, ∀ e ∈ fr.2.binders, r.SpineOK (e.instL g.levels) 0
  recIndices : ∀ fr ∈ Instance.recursiveFields (s := s) ctor, ∀ e ∈ fr.2.indices,
    r.SpineOK (e.instL g.levels) 0

theorem Restoration.minorPiecesOK (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (ctor : Constructor s.families.size) (prior : Nat)
    (H : r.SpineOK (g.minor ctor prior) 0) : r.MinorPiecesOK g ctor := by
  simp only [Instance.minor] at H
  rw [r.spineOK_wrapForalls, r.spineOK_mkApps] at H
  obtain ⟨Hdoms, -, Hargs⟩ := H
  have Hfields : ∀ d ∈ insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
      (s.families.size + prior), r.SpineOK d 0 :=
    fun d hd => Hdoms d (List.mem_append_left _ hd)
  rw [r.spineOK_insertBinders] at Hfields
  have Hihs : ∀ fr ∈ Instance.recursiveFields (s := s) ctor, ∃ i,
      r.SpineOK (g.hypothesis ctor prior i fr.1 fr.2) 0 := by
    intro fr hfr
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hfr
    refine ⟨i, Hdoms _ (List.mem_append_right _ ?_)⟩
    exact List.mem_map.mpr ⟨(fr, i), hi, rfl⟩
  refine ⟨Hfields, ?_, ?_, ?_, ?_⟩
  · intro e he
    have := Hargs _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    rwa [r.spineOK_liftN, r.spineOK_liftN] at this
  · have := Hargs _ (List.mem_append_right _ List.mem_cons_self)
    exact (r.spineOK_constructorApp g ctor _ _).mp this
  · intro fr hfr e he
    obtain ⟨i, Hi⟩ := Hihs fr hfr
    simp only [Instance.hypothesis] at Hi
    rw [r.spineOK_wrapForalls] at Hi
    obtain ⟨j, hj⟩ := mem_zipIdx_of_mem he
    have := Hi.1 _ (List.mem_map.mpr ⟨(e, j), hj, rfl⟩)
    simp only [Instance.underFields] at this
    rwa [r.spineOK_liftN, r.spineOK_liftN] at this
  · intro fr hfr e he
    obtain ⟨i, Hi⟩ := Hihs fr hfr
    simp only [Instance.hypothesis] at Hi
    rw [r.spineOK_wrapForalls, r.spineOK_mkApps] at Hi
    have := Hi.2.2 _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    simp only [Instance.underFields] at this
    rwa [r.spineOK_liftN, r.spineOK_liftN] at this

/-- A generated recursor name that is not a restoration head is restorable at
any spine length. -/
theorem Restoration.spineOK_const_of_find_none (r : Restoration) {name : Name}
    {levels : List VLevel} (h : r.heads.find? (fun h => h.auxiliary == name) = none)
    (k : Nat) : r.SpineOK (.const name levels) k := by
  intro h' hf
  rw [h] at hf
  cases hf

/-- **Totality of equation restoration.** If restoration is defined on the
generated recursor types and no generated recursor name is a restoration
head, restoration is defined on every generated equation. -/
theorem Instance.restoredEquations_isSome (r : Restoration) {s : InductiveSignature}
    (g : Instance s)
    (hrec : ∀ owner, ∃ t, r.expr (g.recursorType owner) = some t)
    (hnames : ∀ owner, r.heads.find? (fun h => h.auxiliary == g.recursorName owner) = none) :
    ∃ rules, g.restoredEquations r = some rules := by
  have Hequation : ∀ index : Fin s.constructors.size,
      ∃ e, r.equation (g.equation index) = some e := by
    intro index
    let ctor := s.constructors[index]
    obtain ⟨t, ht⟩ := hrec ctor.owner
    obtain ⟨pre, major, hpre, -, -⟩ := r.expr_recursorType_eq_some ht
    have Hpre : ∀ d ∈ g.recursorPrefix ctor.owner, r.SpineOK d 0 := by
      intro d hd
      obtain ⟨d', -, hd'⟩ := Lean4Lean.List.Forall₂.forall_exists_l
        (List.mapM_eq_some.mp hpre) d hd
      exact (r.expr_isSome_iff d).mp ⟨d', hd'⟩
    simp only [Instance.recursorPrefix, List.mem_append] at Hpre
    have Hparams : ∀ d ∈ g.params, r.SpineOK d 0 := fun d hd => Hpre d (.inl (.inl (.inl hd)))
    have Hmotives : ∀ d ∈ g.motives, r.SpineOK d 0 :=
      fun d hd => Hpre d (.inl (.inl (.inr hd)))
    have Hminors : ∀ d ∈ g.minors, r.SpineOK d 0 := fun d hd => Hpre d (.inl (.inr hd))
    have hminor : g.minor ctor index.val ∈ g.minors := by
      refine List.mem_map.mpr ⟨(ctor, index.val), ?_, rfl⟩
      refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
      simp [ctor]
    have M := r.minorPiecesOK g ctor index.val (Hminors _ hminor)
    have Hdomains : ∀ d ∈ g.params ++ g.motives ++ g.minors ++
        insertBinders ((s.fieldTypes ctor).map (·.instL g.levels))
          (s.families.size + s.constructors.size), r.SpineOK d 0 := by
      intro d hd
      simp only [List.mem_append] at hd
      rcases hd with ((hd | hd) | hd) | hd
      · exact Hparams d hd
      · exact Hmotives d hd
      · exact Hminors d hd
      · exact (r.spineOK_insertBinders _ _).mpr M.fields d hd
    have Hindices : ∀ a ∈ ctor.indices.map (fun e => (e.instL g.levels).liftN
        (s.families.size + s.constructors.size) ctor.fields.length), r.SpineOK a 0 := by
      intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [r.spineOK_liftN]
      exact M.indices e he
    have Hmajor : r.SpineOK (g.constructorApp ctor
        (s.families.size + s.constructors.size) 0) 0 :=
      (r.spineOK_constructorApp g ctor _ _).mpr M.head
    have Hcalls : ∀ fr ∈ Instance.recursiveFields (s := s) ctor,
        r.SpineOK (g.recursiveCall ctor fr.1 fr.2) 0 := by
      intro fr hfr
      simp only [Instance.recursiveCall, recursorHead]
      rw [r.spineOK_wrapLams, r.spineOK_mkApps]
      refine ⟨?_, r.spineOK_const_of_find_none (hnames _) _, ?_⟩
      · intro d hd
        simp only [List.mem_map, Prod.exists] at hd
        obtain ⟨e, j, hej, rfl⟩ := hd
        simp only [Instance.underFields]
        rw [r.spineOK_liftN, r.spineOK_liftN]
        exact M.binders fr hfr e (List.fst_mem_of_mem_zipIdx hej)
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with (ha | ha) | rfl
        · exact r.spineOK_vars _ _ a ha
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
          simp only [Instance.underFields]
          rw [r.spineOK_liftN, r.spineOK_liftN]
          exact M.recIndices fr hfr e he
        · rw [r.spineOK_mkApps]
          exact ⟨trivial, r.spineOK_vars _ _⟩
    have Hlhs : r.SpineOK (g.equation index).lhs 0 := by
      simp only [Instance.equation, recursorHead]
      rw [r.spineOK_wrapLams, r.spineOK_mkApps]
      refine ⟨Hdomains, r.spineOK_const_of_find_none (hnames _) _, ?_⟩
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · exact r.spineOK_vars _ _ a ha
      · exact Hindices a ha
      · exact Hmajor
    have Hrhs : r.SpineOK (g.equation index).rhs 0 := by
      simp only [Instance.equation]
      rw [r.spineOK_wrapLams, r.spineOK_mkApps]
      refine ⟨Hdomains, trivial, ?_⟩
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact r.spineOK_vars _ _ a ha
      · obtain ⟨fr, hfr, rfl⟩ := List.mem_map.mp ha
        exact Hcalls fr hfr
    have Htype : r.SpineOK (g.equation index).type 0 := by
      simp only [Instance.equation]
      rw [r.spineOK_wrapForalls, r.spineOK_mkApps]
      refine ⟨Hdomains, trivial, ?_⟩
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact Hindices a ha
      · exact Hmajor
    obtain ⟨lhs, hlhs⟩ := (r.expr_isSome_iff _).mpr Hlhs
    obtain ⟨rhs, hrhs⟩ := (r.expr_isSome_iff _).mpr Hrhs
    obtain ⟨type, htype⟩ := (r.expr_isSome_iff _).mpr Htype
    exact ⟨{ g.equation index with lhs := lhs, rhs := rhs, type := type },
      by simp [Restoration.equation, hlhs, hrhs, htype]⟩
  have key : ∀ l : List (Fin s.constructors.size),
      ∃ rules, (l.map (fun index => g.equation index)).mapM r.equation = some rules := by
    intro l
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons a l ih =>
      obtain ⟨rules, hrules⟩ := ih
      obtain ⟨e, he⟩ := Hequation a
      exact ⟨e :: rules, by simp [List.mapM_cons, he, hrules]⟩
  exact key _

end InductiveSignature
end Lean4Lean
