import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationDataConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorTypes
import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Whnf

/-! Restored recursor list of the restored block of a validated nested run.

The recursor entries of `restoredBlock` are the translations of the
restored recursors of the executable restoration folds: the source recursors
selected by the source family translations (`SourceFamilyTranslations`), then the
auxiliary recursors selected by the auxiliary fold (`AuxiliaryRecursorRuleBatches`).
Each of these is the abstract restoration
(`Restoration.recursor`) of the generated recursor of the same owner, so the
`recursors` field of `NestedCompilationRestorationFacts` holds. -/


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
  | .elim .., _ => True

theorem Restoration.go_isSome_of_spineOK (r : Restoration) :
    ∀ (e : VExpr) (args : List VExpr), r.SpineOK e args.length →
      ∃ v, Restoration.expr.go r e args = some v
  | .bvar i, args, _ => ⟨_, rfl⟩
  | .sort u, args, _ => ⟨_, rfl⟩
  | .elim .., args, _ => ⟨_, rfl⟩
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
  | .bvar i, args, _, _ => trivial
  | .sort u, args, _, _ => trivial
  | .elim .., args, _, _ => trivial
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
  | .elim .., j, k => by simp [VExpr.liftN, Restoration.SpineOK]
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

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-! ### The recursor steps selected by the restoration folds -/

/-- The data of a restored recursor step fixing its translated constant. -/
def RecursorRestorationStepValue (env : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv) (w : VConstVal) : Prop :=
  w.name = Hstep.restored.newRecName ∧
    Hstep.restored.newInfo.levelParams.length = w.uvars ∧
    TrExprS env Hstep.restored.newInfo.levelParams []
      Hstep.restored.newInfo.type w.type

/-- The source recursors of `SourceFamilyTranslations`, one per source family,
each the translation of the restored recursor at the family's recursor name. -/
theorem SourceFamilyTranslations.recursorSteps
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    List.Forall₂ (fun (indType : InductiveType) (w : VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
          auxRec allIndNames (Lean.mkRecName indType.name) s t),
          RecursorRestorationStepValue envCtors Hstep w)
      types recursors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    refine .cons ⟨_, _, Hstep.restored.recursor, Hrecursor.name, ?_, ?_⟩ ih
    · rw [Hstep.restored.recursor.restored.restoration.levelParams]
      exact Hrecursor.uvars
    · rw [Hstep.restored.recursor.restored.restoration.levelParams]
      exact Hrecursor.type

/-- The auxiliary recursors of `AuxiliaryRecursorRuleBatches`, one per restored
recursor name, each the translation of the restored recursor at that name. -/
theorem AuxiliaryRecursorRuleBatches.recursorSteps
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    (H : AuxiliaryRecursorRuleBatches safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules) :
    ∃ added, finalRecursors = priorRecursors ++ added ∧
      List.Forall₂ (fun (name : Name) (w : VConstVal) =>
          ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
            auxRec allIndNames name s t),
            RecursorRestorationStepValue trEnv Hstep w)
        names added := by
  induction H with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons Hstep Htail Hsemantic Hrest ih =>
    obtain ⟨added, hfinal, Hadded⟩ := ih
    obtain ⟨⟨_, huvars, htype⟩, hname⟩ := Hsemantic.translated
    refine ⟨Hsemantic.recursor :: added, by simp [hfinal], .cons ⟨_, _, Hstep,
      ?_, huvars, htype⟩ Hadded⟩
    rw [← Hstep.restored.restoration.name]
    exact hname.symm

/-- The auxiliary recursors of `AuxiliaryRecursorTranslations`, one per restored
recursor name, each the translation of the restored recursor at that name. -/
theorem AuxiliaryRecursorTranslations.recursorSteps
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    (H : AuxiliaryRecursorTranslations safety trEnv recursorEnv Htrace
      priorRecursors finalRecursors) :
    ∃ added, finalRecursors = priorRecursors ++ added ∧
      List.Forall₂ (fun (name : Name) (w : VConstVal) =>
          ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
            auxRec allIndNames name s t),
            RecursorRestorationStepValue trEnv Hstep w)
        names added := by
  induction H with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons Hstep Htail Hhead Hrest ih =>
    obtain ⟨added, hfinal, Hadded⟩ := ih
    obtain ⟨⟨_, huvars, htype⟩, hname⟩ := Hhead.translated
    refine ⟨Hhead.recursor :: added, by simp [hfinal], .cons ⟨_, _, Hstep,
      ?_, huvars, htype⟩ Hadded⟩
    rw [← Hstep.restored.restoration.name]
    exact hname.symm

/-! ### One restored recursor -/

/-- The lowered recursor read back by a restoration step at a generated
owner's recursor name has the owner's generated recursor metadata. -/
theorem NestedRun.recursorMetadataOfStep
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    RecursorMetadata E.lowered.recursors.canonicalGeneration
      E.lowered.recursors.outVEnv owner Hstep.oldInfo := by
  rcases E.lowered.recursors.trMetadata owner with
    ⟨rec, hrec, _, M⟩
  have hlen : owner.val < E.lowered.recursors.entries.length := by
    rw [show E.lowered.recursors.entries =
      E.lowered.recursors.entries from rfl,
      E.lowered.recursors.entries_length_eq]
    exact owner.isLt
  have hmem := List.getElem_mem (l := E.lowered.recursors.entries)
    (n := owner.val) hlen
  have hfind := E.lowered.recursors.findRecursorOfMem
    (info := (E.lowered.recursors.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.lowered.recursors.entries[owner.val]'hlen).1 = .recInfo rec := hrec
  rw [hrec'] at hfind
  change E.loweredEnv.find? rec.name = some (.recInfo rec) at hfind
  have h2 : some (ConstantInfo.recInfo rec) = some (.recInfo Hstep.oldInfo) := by
    rw [← hfind, M.name]
    exact Hstep.lookup
  have heq : rec = Hstep.oldInfo := by
    injection h2 with h
    injection h
  rw [heq] at M
  exact M

/-- **One restored recursor.** The translation of the restored recursor of a
restoration step at a generated owner's lowered recursor name is the abstract
restoration (`Restoration.recursor`) of the owner's generated recursor, given
the parameter uniformity of the lowered recursor type and the freshness of the
restorable names in the translation environment. -/
theorem NestedRun.restoredRecursor_of_step
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {oldRecName : Name} {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) oldRecName stepSource stepTarget)
    (hname : oldRecName =
      E.lowered.recursors.canonicalGeneration.recursorName owner)
    (Hshape : Expr.ParamUniformTele
      ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary))
      result.nparams (lparams.map Level.param) Hstep.oldInfo.type)
    {targetEnv : VEnv}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      targetEnv.constants n = none)
    {w : VConstVal} (Hw : RecursorRestorationStepValue targetEnv Hstep w) :
    (compilationRestoration sourceDecl auxiliaries).recursor
      (E.lowered.recursors.canonicalGeneration.recursor owner) =
        some w := by
  subst hname
  obtain ⟨hwname, hwuvars, Ht⟩ := Hw
  have M := E.recursorMetadataOfStep owner Hstep
  have Hs := M.type
  rcases E.loweredRecursorParameterTelescope owner Hstep with ⟨suffix, Htel⟩
  have hclosed : Closed Hstep.oldInfo.type := by
    simpa [VLCtx.bvars] using Hs.closed
  have Hinput : Hstep.oldInfo.type.FVarsIn fun _ => False :=
    Hs.fvarsIn.mono fun _ h => by simp [VLCtx.fvars] at h
  have htype : (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.recursors.canonicalGeneration.recursorType owner) =
        some w.type :=
    Hstep.restored.restoration.typeRestorationCommutes hparamsSize
      (D.agreement targetEnv _) hscoped.argumentsClosed Hfresh Hshape
      (fun Hopen => Hopen.restoredBody_closed D Htel hclosed) Htel Hinput hclosed Hs Ht
  have hrecName : (compilationRestoration sourceDecl auxiliaries).recursorName
      (E.lowered.recursors.canonicalGeneration.recursorName owner) =
        w.name := by
    rw [D.recursorName, hwname, Hstep.restored.mappedName]
    exact (nameMap_getD_eq _ _ _).symm
  have huvars : E.lowered.recursors.canonicalGeneration.uvars = w.uvars := by
    rw [← M.uvars, ← hwuvars, Hstep.restored.restoration.levelParams]
  simp only [Restoration.recursor, InductiveSignature.Instance.recursor, htype,
    Option.bind_eq_bind, Option.pure_def, Option.bind_some, hrecName]
  rcases w with ⟨⟨wu, wt⟩, wn⟩
  simp only at huvars
  rw [huvars]

/-! ### Freshness of the restorable names in the source constructor environment -/

/-- The source constructor names are constructor names of the source prefix of
the lowered declaration. -/
theorem RestoredBlockBase.sourceConstructorNames
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (B : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :
    ∀ c ∈ decl.constructorConstants,
      c.name ∈ familyNames (B.lowered.loweredDecl.types.take decl.types.length) := by
  intro c hc
  obtain ⟨src, hsrc, hcsrc⟩ := List.mem_flatMap.mp hc
  have HT := List.forall₂_take B.formationAssembly.types decl.types.length
  rw [List.take_left' rfl, B.formationExpanded] at HT
  obtain ⟨t, ht, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT src hsrc
  obtain ⟨c', hc', hcc⟩ := Lean4Lean.List.Forall₂.forall_exists_l hT.constructors c hcsrc
  rw [← hcc.name]
  exact mem_familyNames_of_ctor ht hc'

/-- The restorable names of the compilation restoration of a validated nested
run are fresh in the source constructor environment. -/
theorem NestedRun.restorableNames_fresh_ctors
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hctorNames : ∀ c ∈ sourceDecl.constructorConstants,
      c.name ∈ familyNames (E.lowered.loweredDecl.types.take sourceDecl.types.length))
    {envCtors : VEnv}
    (hctors : envTypes.addConstVals sourceDecl.constructorConstants = some envCtors) :
    ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      envCtors.constants name = none := by
  have hfreshTypes := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfamNodup : (familyNames (E.lowered.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  intro name hname
  cases hc : envCtors.constants name with
  | none => rfl
  | some ci =>
    exfalso
    rcases VEnv.addConstVals_lookup_cases hctors hc with hbase | ⟨entry, hentry, hn, -⟩
    · rw [hfreshTypes name hname] at hbase; cases hbase
    · have hsrc := hctorNames entry hentry
      rw [hn] at hsrc
      rcases List.mem_append.mp hname with h | h
      · rw [hheadNames] at h
        exact (List.nodup_append.mp hfamNodup).2.2 _ hsrc _ h rfl
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        have hp1 : p.1 ∈ auxiliaries.map (fun a => a.auxiliary.str "rec") := by
          rw [← compilationRestoration_recursors_fst]
          exact List.mem_map_of_mem hp
        obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp1
        have haux : a.auxiliary ∈
            (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
          rw [← auxiliarySpecializations_names Haux Hexpansion]
          exact List.mem_map_of_mem ha
        obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
        have h1 : p.1 ∈ familyNames E.lowered.loweredDecl.types := by
          have : familyNames (E.lowered.loweredDecl.types.take sourceDecl.types.length) ⊆
              familyNames E.lowered.loweredDecl.types := by
            intro x hx
            obtain ⟨t', ht', hx'⟩ := mem_familyNames.mp hx
            exact mem_familyNames.mpr ⟨t', List.mem_of_mem_take ht', hx'⟩
          exact this hsrc
        have h2 : p.1 ∈ E.lowered.loweredDecl.types.map
            (fun t => t.name.str "rec") := by
          rw [← hpa, ← hta]
          exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
            (List.mem_of_mem_drop ht)
        exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl

/-! ### The order of the restored recursors -/

theorem forall₂_map_eq {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hR : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → l.map f = r.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.map_cons, hR _ _ h, forall₂_map_eq hR t]

/-- The generated recursor names, in owner order, are the recursor names of
the source families followed by the auxiliary recursor names restored by the
executable auxiliary fold. -/
theorem NestedRun.recursorNames_order
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnonempty : sourceTypes ≠ []) :
    (List.finRange
        E.lowered.recursors.generationSignature.families.size).map
        E.lowered.recursors.canonicalGeneration.recursorName =
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
  let P := E.lowered
  have hentries : P.recursors.entries.length = P.indTypes.toList.length := by
    rw [P.recursors.generated.length, P.recursors.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length P.constructors.core]
  -- generated names in owner order
  have hgen : (List.finRange
        E.lowered.recursors.generationSignature.families.size).map
        E.lowered.recursors.canonicalGeneration.recursorName =
      P.indTypes.toList.map (fun t => Lean.mkRecName t.name) := by
    have hN : E.lowered.recursors.generationSignature.families.size =
        P.indTypes.toList.length := by
      rw [← E.lowered.recursors.entries_length_eq]
      exact hentries
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange]; exact hN
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      have hiE : i < P.recursors.entries.length := by
        rw [hentries]; simpa using hi'
      obtain ⟨owner, hown, h⟩ := E.recursorOwnerOfEntry hiE
      have : owner = ⟨i, by simpa using hi⟩ := Fin.ext hown
      subst this
      rw [← h]
      congr 2
      have hi'' : i < P.indTypes.size := by simpa using hi'
      rw [getElem!_pos P.indTypes i hi'', Array.getElem_toList]
  -- source and lowered names
  have hloweredNames : P.indTypes.toList.map (·.name) =
      P.loweredDecl.types.map (·.name) :=
    forall₂_map_eq (fun a b h => h.header.name.symm) P.constructors.core.types
  have hsourceNames : sourceTypes.map (·.name) =
      (P.loweredDecl.types.take sourceTypes.length).map (·.name) :=
    forall₂_map_eq (fun a b h => h.name.symm) E.sourceCore.sourceHeaders
  have hsplit : P.indTypes.toList.map (·.name) =
      sourceTypes.map (·.name) ++
        (P.indTypes.toList.drop sourceTypes.length).map (·.name) := by
    rw [hsourceNames, List.map_take, ← hloweredNames, ← List.map_take,
      ← List.map_append, List.take_append_drop]
  -- the auxiliary recursor names
  obtain ⟨main, rest, rfl⟩ : ∃ main rest, sourceTypes = main :: rest := by
    cases sourceTypes with
    | nil => exact absurd rfl hnonempty
    | cons main rest => exact ⟨main, rest, rfl⟩
  obtain ⟨o, os, hos⟩ : ∃ o os, P.indTypes.toList = o :: os := by
    cases h : P.indTypes.toList with
    | nil => rw [h] at hsplit; simp at hsplit
    | cons o os => exact ⟨o, os, rfl⟩
  have hoName : o.name = main.name := by
    rw [hos] at hsplit
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at hsplit
    exact hsplit.1
  have Hc : ContextWF P.c := by
    rw [E.lowered_c]; exact E.contextWF
  obtain ⟨info, hfind, -, hall⟩ := P.recursors.findSourceHeader Hc
    (owner := o) (by rw [hos]; exact List.mem_cons_self)
  rw [hoName] at hfind
  have haux : (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1 =
      (P.indTypes.toList.drop (main :: rest).length).map
        (fun t => Lean.mkRecName t.name) := by
    by_cases hlength : (main :: rest).length < info.all.length
    · rw [mkAuxRecNameMap_recNames main rest E.loweredEnv info hfind hlength, hall,
        ← List.map_drop, List.map_map]
      rfl
    · have hlength' : ¬ rest.length + 1 < info.all.length := by
        simpa using hlength
      have hnil : (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1 = [] := by
        simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength']
        rfl
      rw [hnil]
      have : P.indTypes.toList.drop (main :: rest).length = [] := by
        apply List.drop_eq_nil_of_le
        have := congrArg List.length hall
        simp only [List.length_map] at this
        omega
      rw [this]; rfl
  rw [hgen, haux]
  conv => lhs; rw [← List.take_append_drop (main :: rest).length P.indTypes.toList]
  rw [List.map_append]
  congr 1
  have h := congrArg (List.take (main :: rest).length) hsplit
  rw [List.take_left' (by simp), ← List.map_take] at h
  have h2 := congrArg (List.map Lean.mkRecName) h
  simpa only [List.map_map, Function.comp_def] using h2

/-! ### The restored recursor list -/

/-- The recursor entries of the restored block, in owner order:
each is the abstract restoration of the owner's generated recursor and the
translation of the restored recursor of a restoration step at the owner's
lowered recursor name. -/
theorem NestedRun.restoredRecursorEntries_of_paramUniform
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (B : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.lowered = E.lowered)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    List.Forall₂ (fun owner w =>
        (compilationRestoration sourceDecl auxiliaries).recursor
          (E.lowered.recursors.canonicalGeneration.recursor owner) = some w ∧
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.lowered.recursors.canonicalGeneration.recursorName owner) s t),
          RecursorRestorationStepValue
            ((B.install.venvCtors.addEliminators B.install.eliminators).addProjections
              sourceDecl.projectionEntries) Hstep w)
      (List.finRange
        E.lowered.recursors.generationSignature.families.size)
      (B.sourceRecursors ++ B.auxiliaryRecursors) := by
  let r := compilationRestoration sourceDecl auxiliaries
  let trEnv := (B.install.venvCtors.addEliminators B.install.eliminators).addProjections sourceDecl.projectionEntries
  -- freshness of the restorable names in the translation environment
  have htypesEq : B.install.venvTypes = envTypes := by
    have h := B.install.abstract_types
    rw [B.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some B.install.venvCtors := by
    have h := B.install.abstract_ctors
    rwa [B.constructorValues, htypesEq] at h
  have hctorNames := B.sourceConstructorNames
  rw [hB] at hctorNames
  have Hfresh : ∀ n ∈ r.restorableNames, trEnv.constants n = none := by
    intro n hn
    simp only [trEnv, VEnv.addEliminators_constants, VEnv.addProjections_constants]
    exact E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup hctorNames
      hctorsAdded n hn
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  -- the recursor steps selected by the two folds
  have Hprimary := B.sourceTranslations.recursorSteps
  obtain ⟨added, hadded', Hadded⟩ := B.auxiliaryRecursorTrace.recursorSteps
  simp only [List.nil_append] at hadded'
  rw [← hadded'] at Hadded
  have Hall : List.Forall₂ (fun (name : Name) (w : VConstVal) =>
      ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) name s t),
        RecursorRestorationStepValue trEnv Hstep w)
      ((List.finRange
          E.lowered.recursors.generationSignature.families.size).map
          E.lowered.recursors.canonicalGeneration.recursorName)
      (B.sourceRecursors ++ B.auxiliaryRecursors) := by
    have hnonempty : sourceTypes ≠ [] := B.sourceNonempty
    rw [E.recursorNames_order hnonempty]
    exact Lean4Lean.List.Forall₂.append_of_left (by
        rw [List.length_map]; exact Lean4Lean.List.Forall₂.length_eq Hprimary) |>.mpr
      ⟨List.forall₂_map_left_iff.mpr Hprimary, Hadded⟩
  rw [List.forall₂_map_left_iff] at Hall
  refine Lean4Lean.List.Forall₂.imp ?_ Hall
  rintro owner w ⟨s, t, Hstep, Hw⟩
  have Hshape := (E.recursorParamUniform_of_wfCore wf Hsources owner Hstep).1
  rw [← hheads] at Hshape
  exact ⟨E.restoredRecursor_of_step hparamsSize D hscoped owner Hstep rfl Hshape
    Hfresh Hw, s, t, Hstep, Hw⟩



/-- The restored generated recursor list of the lowered declaration is the
recursor list of a `RestoredBlockBase`, for the specializations of
`restorationTablesRestoringAll` (via `NestedRun.recursorParamUniform_of_wfCore`). -/
theorem NestedRun.restoredRecursorList_of_paramUniform
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (B : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.lowered = E.lowered)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    E.lowered.generatedInstance.restoredRecursors
        (compilationRestoration sourceDecl auxiliaries) =
      some (B.sourceRecursors ++ B.auxiliaryRecursors) := by
  have Hrec := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1)
    (E.restoredRecursorEntries_of_paramUniform B hB wf Hsources hadded Haux Hexpansion hnodup
      hparamsSize D hscoped)
  show List.mapM _ ((List.finRange _).map _) = _
  rw [List.mapM_map]
  exact List.mapM_eq_some.mpr Hrec

/-- **The `recursors` field of `NestedCompilationRestorationFacts`.** For the
specializations of `restorationTablesRestoringAll`, the restored generated
recursor list of the lowered declaration is exactly the recursor list of the
restored block (via `NestedRun.recursorParamUniform_of_wfCore`). -/
theorem NestedRun.restoredRecursors_of_paramUniform
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : RestoredBlockDerivation E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    E.lowered.generatedInstance.restoredRecursors
        (compilationRestoration sourceDecl auxiliaries) =
      some (restoredBlock sourceDecl C.sourceRecursors
        C.auxiliaryRecursors C.sourceRules C.auxiliaryRules).recursors :=
  E.restoredRecursorList_of_paramUniform C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped

/-- Two restoration steps at the same lowered recursor name read back the
same lowered recursor and restore it to the same recursor. -/
theorem RestoredRecursorStep.info_eq
    (H₁ : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s₁ t₁)
    (H₂ : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s₂ t₂) :
    H₁.oldInfo = H₂.oldInfo ∧ H₁.restored.newInfo = H₂.restored.newInfo := by
  have h : some (ConstantInfo.recInfo H₁.oldInfo) = some (.recInfo H₂.oldInfo) :=
    H₁.lookup.symm.trans H₂.lookup
  have hold : H₁.oldInfo = H₂.oldInfo := by
    injection h with h
    injection h
  refine ⟨hold, ?_⟩
  rw [H₁.restored.produced, H₂.restored.produced, hold]

/-- **Shape fields of the restored recursors.** For every generated owner and
every restoration step at the owner's lowered recursor name, the abstract
recursor environment of the `RestoredBlockBase` stores the restored recursor at
the abstract restoration of the owner's generated recursor type, and the
restored recursor's parameter, index, motive and minor counts are the
signature's. These are the `type`, `numParams`, `numIndices`, `numMotives`
and `numMinors` clauses of `RestoredRecursorShape`. -/
theorem NestedRun.restoredRecursorShapeFields
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (B : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.lowered = E.lowered)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped) :
    ∀ (owner : Fin E.lowered.recursors.generationSignature.families.size)
      {s t : Environment}
      (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name))
        (E.lowered.recursors.canonicalGeneration.recursorName owner) s t),
      (∃ type, (compilationRestoration sourceDecl auxiliaries).expr
          (E.lowered.recursors.canonicalGeneration.recursorType owner) =
            some type ∧
        B.recursorVEnv.constants Hstep.restored.newInfo.name =
          some ⟨Hstep.restored.newInfo.levelParams.length, type⟩) ∧
      Hstep.restored.newInfo.numParams =
        E.lowered.recursors.generationSignature.params.length ∧
      Hstep.restored.newInfo.numIndices =
        E.lowered.recursors.generationSignature.families[owner].indices.length ∧
      Hstep.restored.newInfo.numMotives =
        E.lowered.recursors.generationSignature.families.size ∧
      Hstep.restored.newInfo.numMinors =
        E.lowered.recursors.generationSignature.constructors.size := by
  intro owner s t Hstep
  have Hentries := E.restoredRecursorEntries_of_paramUniform B hB wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  obtain ⟨w, hw, hrec, s', t', Hstep', hwname, hwuvars, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l Hentries owner (List.mem_finRange owner)
  obtain ⟨hold, hnew⟩ := Hstep'.info_eq Hstep
  have M := E.recursorMetadataOfStep owner Hstep
  have R := Hstep.restored.restoration
  refine ⟨?_, R.numParams.trans M.numParams, R.numIndices.trans M.numIndices,
    R.numMotives.trans M.numMotives, R.numMinors.trans M.numMinors⟩
  have hadd := B.install.recursorsAdded.abstract
  rw [B.recursorValues] at hadd
  have hconst := VEnv.addConstVals_get hadd hw
  simp only [Restoration.recursor, InductiveSignature.Instance.recursor,
    Option.bind_eq_bind, Option.pure_def] at hrec
  cases ht : (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.recursors.canonicalGeneration.recursorType owner) with
  | none => simp [ht] at hrec
  | some type =>
    simp only [ht, Option.bind_some, Option.some.injEq] at hrec
    refine ⟨type, rfl, ?_⟩
    have hname : Hstep.restored.newInfo.name = w.name := by
      rw [hwname, ← hnew, Hstep'.restored.restoration.name]
    have hwtype : w.type = type := by rw [← hrec]
    rw [hname, hconst, ← hnew, hwuvars, ← hwtype]

/-! ### `CompilationData` with an arbitrary equation list

`NestedRun.compilationData_of_specializations`
(`Nested/Restoration/CompilationData.lean`), with the rule lists of the
restored block arbitrary: no field of `CompilationData` but `equations`
mentions the block's rules. -/


/-! ### Generated recursor names are not restoration heads -/

/-- Every generated recursor name is the recursor name of a lowered family. -/
theorem NestedRun.recursorName_mem_lowered
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.lowered.recursors.generationSignature.families.size) :
    E.lowered.recursors.canonicalGeneration.recursorName owner ∈
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec") := by
  have hiE : owner.val < E.lowered.recursors.entries.length := by
    rw [show E.lowered.recursors.entries =
      E.lowered.recursors.entries from rfl,
      E.lowered.recursors.entries_length_eq]
    exact owner.isLt
  obtain ⟨owner', hown, h⟩ := E.recursorOwnerOfEntry hiE
  have : owner' = owner := Fin.ext hown
  subst this
  rw [← h]
  have hloweredNames : E.lowered.indTypes.toList.map (·.name) =
      E.lowered.loweredDecl.types.map (·.name) :=
    forall₂_map_eq (fun a b h => h.header.name.symm) E.lowered.constructors.core.types
  have hlt : owner'.val < E.lowered.indTypes.size := by
    have := E.lowered.recursors.generated.length
    rw [E.lowered.recursors.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        E.lowered.constructors.core] at this
    rw [this] at hiE
    simpa using hiE
  have hmem : E.lowered.indTypes[owner'.val]!.name ∈
      E.lowered.indTypes.toList.map (·.name) := by
    rw [getElem!_pos E.lowered.indTypes owner'.val hlt]
    exact List.mem_map_of_mem (Array.getElem_mem_toList hlt)
  rw [hloweredNames] at hmem
  obtain ⟨t, ht, hname⟩ := List.mem_map.mp hmem
  rw [← hname]
  exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec") ht

/-- No generated recursor name is a restoration head. -/
theorem NestedRun.recursorName_not_head
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (owner : Fin E.lowered.recursors.generationSignature.families.size) :
    (compilationRestoration sourceDecl auxiliaries).heads.find?
        (fun h => h.auxiliary ==
          E.lowered.recursors.canonicalGeneration.recursorName owner) =
      none := by
  apply List.find?_eq_none.mpr
  intro h hh heq
  have heq' : h.auxiliary =
      E.lowered.recursors.canonicalGeneration.recursorName owner := by
    simpa using heq
  have hmem : h.auxiliary ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
      (·.auxiliary) := List.mem_map_of_mem hh
  rw [compilationRestoration_heads_auxiliary,
    auxiliarySpecializations_headNames Haux Hexpansion] at hmem
  have h1 : h.auxiliary ∈ familyNames E.lowered.loweredDecl.types := by
    obtain ⟨t, ht, hx⟩ := mem_familyNames.mp hmem
    exact mem_familyNames.mpr ⟨t, List.mem_of_mem_drop ht, hx⟩
  have h2 := E.recursorName_mem_lowered owner
  rw [← heq'] at h2
  exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl

/-! ### `CompilationData` of a validated nested run -/

end VerifyInductive
end Lean4Lean
