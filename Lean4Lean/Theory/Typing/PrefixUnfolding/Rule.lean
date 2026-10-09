import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation
import Lean4Lean.Theory.Typing.PrefixUnfolding.SpineDefEq
import Lean4Lean.Theory.Typing.BVarConversion
import Batteries.Tactic.OpenPrivate

/-! Singleton unfolding is checked at a recursor prefix. Supplied
arguments are instantiated; all remaining binders, including the major, are
opened before the generated constructor is checked at the major's type.
This distinguishes Eq.rec at aligned endpoints from Eq.rec at arbitrary
endpoints, including during eta expansion.

The complementary recursor iota guard is negated source equivalence to zero.
It is stable under equivalent universes and term substitution, but not under
arbitrary universe substitution. Equation coverage must therefore be given
freshly at every universe specialization. No ParRed.instL is assumed.
-/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- Every datum of the unfolding check is fixed by the generated unfolding. These are the
ordinary typing and syntactic checks of the actual stored equation, not a
caller-provided proof that an arbitrary replacement computes correctly. -/
structure UnfoldingCheck (env : VEnv) (U : Nat) (Γ : List VExpr)
    (source : VExpr) (program : RecursorData.PrefixUnfolding) : Prop where
  source_typed : HasType env U Γ source program.type
  remaining_nonempty : program.domains ≠ []
  equation_present : env.defeqs program.equation
  equation_body : CaseSchema.EquationBody.extract program.equation.lhs
    program.equation.rhs program.equation.type = some program.equationBody
  levels_wf : ∀ level ∈ program.levels, level.WF U
  levels_length : program.levels.length = program.equation.uvars
  captures_length : program.captures.length = program.equationBody.domains.length
  captures_typed : ∀ j (hj : j < program.captures.length)
      (hd : j < program.equationBody.domains.length),
    HasType env U (program.domains.reverse ++ Γ) program.captures[j]
      ((program.equationBody.domains[j].instL program.levels).instOuter
        (program.captures.take j))
  major_prop : ∃ majorType,
    HasType env U (program.domains.reverse ++ Γ) majorType (.sort .zero) ∧
    HasType env U (program.domains.reverse ++ Γ) (.bvar 0) majorType ∧
    HasType env U (program.domains.reverse ++ Γ) program.constructor majorType
  recursor_lhs : ConstSpineDefEq env U (program.domains.reverse ++ Γ)
    (.app (etaOpen (program.domains.length - 1) source).lift program.constructor)
    ((program.equationBody.lhs.instL program.levels).instOuter program.captures)

/-- An aligned prefix of the actual finite singleton unfolding. All remaining
binders are opened before checking its reconstructed constructor. -/
inductive PrefixUnfold (env : VEnv) (U : Nat)
    (registry : Name → Option RecursorData) (Γ : List VExpr) :
    Name → List VLevel → List VExpr → VExpr → Prop where
  | intro {data : RecursorData} {program : RecursorData.PrefixUnfolding} :
      registry name = some data → RecursorRegistered env data → data.name = name →
      data.largeTarget = true → (∀ level ∈ levels, level.WF U) →
      data.sourceLevel levels ≈ .zero →
      data.singletonUnfolding env U levels arguments = some program →
      UnfoldingCheck env U Γ (VExpr.mkApps (.const name levels) arguments) program →
      PrefixUnfold env U registry Γ name levels arguments program.rhs

/-- With the same supplied prefix, unfolding generation is deterministic.
Different prefix lengths may unfold the same larger application; those
steps require a beta-join, not literal equality of one-step outputs. -/
theorem PrefixUnfold.unique
    (H : PrefixUnfold env U registry Γ name levels arguments rhs)
    (H' : PrefixUnfold env U registry Γ name levels arguments rhs') : rhs = rhs' := by
  cases H with | intro hl _ _ _ _ _ hg _ =>
    cases H' with | intro hl' _ _ _ _ _ hg' _ =>
      cases Option.some.inj (hl.symm.trans hl')
      cases RecursorData.singletonUnfolding_unique hg hg'
      rfl

/-- Applying the installed equation under the fresh telescope is sound.
The proof uses only ordinary equation application, beta, eta, and proof
irrelevance at the explicitly checked major proposition. -/
theorem UnfoldingCheck.defeq (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : UnfoldingCheck env U Γ source program) :
    IsDefEq env U Γ source program.rhs program.type := by
  have heta := H.source_typed.etaOpen_defeq henv hΓ
  obtain ⟨hctx, hopen⟩ := H.source_typed.etaOpen_wf henv.ordered hΓ
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  have hetaBody : etaOpen program.domains.length source =
      .app (etaOpen (program.domains.length - 1) source).lift (.bvar 0) := by
    have hlen : program.domains.length = (program.domains.length - 1) + 1 := by omega
    conv => lhs; rw [hlen]
    exact etaOpen_succ _ _
  rw [hetaBody] at hopen
  obtain ⟨domain, result, hf, hm⟩ := hopen.app_inv henv hctx
  obtain ⟨majorType, hp, hmajor, hctor⟩ := H.major_prop
  have hmajorEq := IsDefEq.proofIrrel hp hmajor hctor
  have hreplace := IsDefEq.appDF hf
    (hmajorEq.transport_bvar henv.ordered hctx hmajor hm)
  obtain ⟨hl, hr, ht⟩ := CaseSchema.EquationBody.extract_sound H.equation_body
  have hiota := IsDefEq.extra_instOuter henv hctx H.equation_present H.levels_wf
    H.levels_length hl.symm hr.symm ht.symm H.captures_length H.captures_typed
  have halign := H.recursor_lhs.defeq henv hctx hreplace.hasType.2
  have hbody := IsDefEqU.of_l henv hctx
    ((IsDefEqU.trans henv hctx ⟨_, hreplace⟩ halign).trans henv hctx ⟨_, hiota⟩) hopen
  rw [← hetaBody] at hbody
  simpa only [RecursorData.PrefixUnfolding.rhs, RecursorData.PrefixUnfolding.type, instantiateParams_eq_instOuter] using
    heta.trans (hbody.etaOpen_wrapLams hΓ hctx)

theorem PrefixUnfold.defeq (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : PrefixUnfold env U registry Γ name levels arguments rhs) :
    IsDefEqU env U Γ (VExpr.mkApps (.const name levels) arguments) rhs := by
  cases H with | intro _ _ _ _ _ _ _ replay => exact ⟨_, replay.defeq henv hΓ⟩

theorem UnfoldingCheck.defeqDFC (henv : env.WF)
    (hΓ : OnCtx Γ₀ (env.IsType U))
    (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (H : UnfoldingCheck env U Γ₁ source program) :
    UnfoldingCheck env U Γ₂ source program := by
  have hctx := (H.source_typed.etaOpen_wf henv.ordered (W.isType' hΓ)).1
  have extend {xs : List VExpr} (h : OnCtx (xs ++ Γ₁) (env.IsType U)) :
      IsDefEqCtx env U Γ₀ (xs ++ Γ₁) (xs ++ Γ₂) := by
    induction xs with
    | nil => exact W
    | cons _ _ ih => obtain ⟨_, hd⟩ := h.2; exact .succ (ih h.1) hd
  have W' := extend hctx
  refine { H with source_typed := H.source_typed.defeqDFC henv W
                  captures_typed := fun j hj hd => (H.captures_typed j hj hd).defeqDFC henv W'
                  recursor_lhs := H.recursor_lhs.defeqDFC henv W'
                  major_prop := ?_ }
  obtain ⟨majorType, hp, hm, hc⟩ := H.major_prop
  exact ⟨majorType, hp.defeqDFC henv W', hm.defeqDFC henv W', hc.defeqDFC henv W'⟩

theorem PrefixUnfold.defeqDFC (henv : env.WF)
    (hΓ : OnCtx Γ₀ (env.IsType U)) (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (H : PrefixUnfold env U registry Γ₁ name levels arguments rhs) :
    PrefixUnfold env U registry Γ₂ name levels arguments rhs := by
  cases H with | intro hl hr hn ht hw hp hg replay =>
    exact .intro hl hr hn ht hw hp hg (replay.defeqDFC henv hΓ W)

open private closed_wrapLams_body closed_wrapForalls_domain
  from Lean4Lean.Theory.Typing.CaseReduction

/-- Installed equation syntax bounds all unfolding captures and their domains. -/
theorem UnfoldingCheck.templateScope (henv : env.WF)
    (H : UnfoldingCheck env U Γ source program) :
    program.equationBody.lhs.ClosedN program.captures.length ∧
      program.equationBody.rhs.ClosedN program.captures.length ∧
      ∀ j (hj : j < program.equationBody.domains.length),
        program.equationBody.domains[j].ClosedN j := by
  have hwf := henv.ordered.defEqWF H.equation_present
  have hl : program.equation.lhs.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env program.equation.uvars [] _ from ⟨_, hwf.1⟩) trivial
  have hr : program.equation.rhs.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env program.equation.uvars [] _ from ⟨_, hwf.2⟩) trivial
  have hleft : env.HasType program.equation.uvars [] program.equation.lhs program.equation.type := hwf.1
  obtain ⟨u, ht⟩ := hleft.isType henv.ordered (show OnCtx [] (env.IsType program.equation.uvars) from trivial)
  have ht : program.equation.type.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env program.equation.uvars [] _ from ⟨_, ht⟩) trivial
  obtain ⟨hlhs, hrhs, htype⟩ := CaseSchema.EquationBody.extract_sound H.equation_body
  rw [← hlhs] at hl
  rw [← hrhs] at hr
  rw [← htype] at ht
  exact ⟨by simpa only [Nat.zero_add, H.captures_length] using closed_wrapLams_body hl,
    by simpa only [Nat.zero_add, H.captures_length] using closed_wrapLams_body hr,
    fun j hj => by simpa only [Nat.zero_add] using closed_wrapForalls_domain ht hj⟩


end Lean4Lean.VEnv
