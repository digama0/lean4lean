import Lean4Lean.Theory.Typing.Confluence.QuotPrefixTyping
import Lean4Lean.Theory.Typing.Confluence.QuotPatterns
import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VLevel
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Inductive.QuotPrefixUnfolding
import Lean4Lean.Theory.Typing.QuotPropInhabitant
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Meta
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.CaseReduction

/-! Concrete coverage of the installed quotient equation, including the
proof-source closed delta and its proof-irrelevant result alignment. -/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

theorem QuotRegistered.zero_application_join
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : QuotRegistered env)
    (hu : u.WF univs) (hv : v.WF univs) (hz : u ≈ .zero)
    (H : VExpr.WF env univs Γ (mkApps (.const ``Quot.lift [u,v]) [alpha, relation, beta, fn, compat]))
    (ha : env.HasType univs Γ alpha (.sort u))
    (hrel : env.HasType univs Γ relation (.forallE alpha (.forallE alpha.lift (.sort .zero))))
    (hf : env.HasType univs Γ fn (.forallE alpha beta.lift))
    (hval : env.HasType univs Γ value alpha) :
    ∃ out,
      FullReduction Γ (mkApps (.const ``Quot.lift [u,v])
        [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u]) [alpha, relation, value]]) out ∧
      NormalEq Γ out (.app fn value) := by
  have hd := QuotPrefixUnfold.atFive henv hΓ hr hu hv hz H
  let major := mkApps (.const ``Quot.mk [u]) [alpha, relation, value]
  have hmajor : env.HasType univs Γ major (mkApps (.const ``Quot [u]) [alpha, relation]) := by
    have h1 := (HasType.const hr.constructor (ls := [u]) (by simpa using hu) rfl).app ha
    have h2 := h1.app (by simpa [instL, inst, VLevel.inst] using hrel)
    have h3 := h2.app (by simpa [instL, inst, VLevel.inst, inst_lift, ← lift_instN_lo] using hval)
    simpa [major, mkApps, instL, inst, VLevel.inst, inst_lift, ← lift_instN_lo] using h3
  have hp := hr.propInhabitant_app hu hz ha hrel hmajor
  refine ⟨.app fn (mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha, relation, major]), ?_, ?_⟩
  · have hb : (VExpr.app fn.lift (mkApps (QuotPrefixUnfolding.propInhabitant u)
        [alpha.lift, relation.lift, .bvar 0])).inst major =
        VExpr.app fn (mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha, relation, major]) := by
      simp only [inst, inst_mkApps, inst_lift]
      rw [(QuotPrefixUnfolding.propInhabitant_closed u).instN_eq (Nat.zero_le _)]
      simp [inst, inst_lift]
    rw [← hb]
    exact .tail (.tail .rfl (.app (.quotDelta hd) .rfl)) (.core (.beta .rfl .rfl))
  · exact .appDF hf hf hp hval (.refl hf)
      (.proofIrrel (IsDefEq.defeq (IsDefEq.sortDF hu (by trivial) hz) ha) hp hval)

private theorem join_wrapLams (domains : List VExpr)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs))
    (H : ∃ out, FullReduction (domains.reverse ++ Γ) left out ∧
      NormalEq (domains.reverse ++ Γ) out right) :
    ∃ out, FullReduction Γ (wrapLams domains left) out ∧ NormalEq Γ out (wrapLams domains right) := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons domain ds ih =>
    have hctx' : OnCtx (ds.reverse ++ domain :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
    have H' : ∃ out, FullReduction (ds.reverse ++ domain :: Γ) left out ∧
        NormalEq (ds.reverse ++ domain :: Γ) out right := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H
    obtain ⟨out, hr, he⟩ := ih hctx' H'
    obtain ⟨_, hd⟩ := (OnCtx.of_append hctx').2
    exact ⟨.lam domain out, .lam .rfl hr, .lamDF hd hd he⟩

theorem QuotRegistered.zero_equation_join
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : QuotRegistered env)
    (hu : u.WF univs) (hv : v.WF univs) (hz : u ≈ .zero) :
    ∃ out, FullReduction Γ (quotDefEq.lhs.instL [u,v]) out ∧
      NormalEq Γ out (quotDefEq.rhs.instL [u,v]) := by
  let ds := (((quotDefEq.type.takeForalls 6).getD ([], .bvar 0)).1).map (instL [u,v])
  have hex := IsDefEq.extra (Γ := Γ) hr.equation
    (ls := [u,v]) (by simpa using And.intro hu hv) rfl
  have htyped : env.HasType univs Γ (wrapLams ds (quotDefEq.lhs.stripLams.instL [u,v]))
      (wrapForalls ds (.bvar 3)) := hex.hasType.1
  obtain ⟨hctx, hbody⟩ := HasType.wrapLams_inv henv hΓ htyped
  have hprefix : VExpr.WF env univs (ds.reverse ++ Γ)
      (mkApps (.const ``Quot.lift [u,v]) [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]) := by
    obtain ⟨_, _, hf, _⟩ := hbody.app_inv henv hctx
    exact ⟨_, hf⟩
  have ha : env.HasType univs (ds.reverse ++ Γ) (.bvar 5) (.sort u) := by type_tac
  have hrel : env.HasType univs (ds.reverse ++ Γ) (.bvar 4)
      (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by type_tac
  have hf : env.HasType univs (ds.reverse ++ Γ) (.bvar 2)
      (.forallE (.bvar 5) (.bvar 4)) := by type_tac
  have hval : env.HasType univs (ds.reverse ++ Γ) (.bvar 0) (.bvar 5) := by type_tac
  have hj := hr.zero_application_join hctx hu hv hz hprefix ha hrel hf hval
  exact join_wrapLams ds hctx hj

private theorem PatternReductionTrace.of_quotient
    (hpattern : Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (H : PatternReductionTrace env univs (QuotPattern env) Γ left right) :
    PatternReductionTrace env univs Pat Γ left right := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih ih' => exact .trans ih ih'
  | pattern hp hm hc => cases hp; exact .pattern hpattern hm hc
  | schema h => exact .schema h
  | beta => exact .beta
  | app _ _ ih ih' => exact .app ih ih'
  | lam _ ih => exact .lam ih

/-- The actual primitive quotient equation is covered at every universe
specialization by concrete computation and normal equality of the outputs. -/
theorem QuotRegistered.equation_covered
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : QuotRegistered env)
    (hpattern : Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hw : ∀ level ∈ levels, level.WF univs) (hl : levels.length = quotDefEq.uvars) :
    ∃ left' right', FullReduction Γ (quotDefEq.lhs.instL levels) left' ∧
      FullReduction Γ (quotDefEq.rhs.instL levels) right' ∧ NormalEq Γ left' right' := by
  change levels.length = 2 at hl
  obtain ⟨u, v, rfl⟩ : ∃ u v, levels = [u,v] := by
    rcases levels with _ | ⟨u, _ | ⟨v, tail⟩⟩ <;> simp_all
  by_cases hz : u ≈ .zero
  · obtain ⟨out, hred, he⟩ := hr.zero_equation_join hΓ
      (hw u (by simp)) (hw v (by simp)) hz
    exact ⟨out, _, hred, .rfl, he⟩
  · have htrace := (QuotPattern.equation_trace (v := v) (Γ := Γ) (U := univs) hr hz).of_quotient hpattern
    exact ⟨_, _, htrace.parRedS.full, .rfl,
      .refl (IsDefEq.extra (Γ := Γ) hr.equation hw hl).hasType.2⟩
end Lean4Lean.VEnv
