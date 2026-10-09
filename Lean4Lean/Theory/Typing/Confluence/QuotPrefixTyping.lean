import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.PrefixUnfolding.Weakening
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.RecursorPrefixUnfolding
import Lean4Lean.Theory.Typing.PrefixUnfolding.Rule
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.PrefixUnfolding.SpineDefEq
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Inductive.QuotPrefixUnfolding
import Lean4Lean.Theory.Typing.EtaOpening
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.Meta
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.QuotPropInhabitant
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Typing.PrefixUnfolding.Renaming
import Lean4Lean.Theory.Inductive.SignatureData

namespace Lean4Lean.VEnv
open InductiveSignature
theorem QuotRegistered.mono (h : env ≤ env') (H : QuotRegistered env) : QuotRegistered env' :=
  ⟨h.constants H.quotient, h.constants H.constructor, h.constants H.lift,
    h.constants H.induction, h.defeqs H.equation⟩
theorem QuotRegistered.of_addQuot {env env' : VEnv} (h : env.addQuot = some env') : QuotRegistered env' :=
  ⟨addQuot_quot h, addQuot_quotMk h, addQuot_quotLift h, addQuot_quotInd h, addQuot_defeq h⟩
/-- The quotient generator and registration discharge every structural
replay check; only the occurrence's ordinary typing checks remain. -/
theorem QuotPrefixUnfold.ofGenerated
    (hr : QuotRegistered env) (hw : ∀ level ∈ levels, level.WF U)
    (hz : levels[0]?.getD .zero ≈ .zero)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (hsource : HasType env U Γ (VExpr.mkApps (.const ``Quot.lift levels) args) program.type)
    (hcaptures : ∀ j (hj : j < program.captures.length)
        (hd : j < program.equationBody.domains.length),
      HasType env U (program.domains.reverse ++ Γ) program.captures[j]
        ((program.equationBody.domains[j].instL program.levels).instOuter (program.captures.take j)))
    (hmajor : ∃ proposition,
      HasType env U (program.domains.reverse ++ Γ) proposition (.sort .zero) ∧
      HasType env U (program.domains.reverse ++ Γ) (.bvar 0) proposition ∧
      HasType env U (program.domains.reverse ++ Γ) program.constructor proposition)
    (hmatch : ConstSpineDefEq env U (program.domains.reverse ++ Γ)
      (.app (etaOpen (program.domains.length - 1)
        (VExpr.mkApps (.const ``Quot.lift levels) args)).lift program.constructor)
      ((program.equationBody.lhs.instL program.levels).instOuter program.captures)) :
    QuotPrefixUnfold env U Γ levels args program.rhs := by
  obtain ⟨hl, _, hn, hlevels, heq, hbody, hcapturesLength⟩ := QuotPrefixUnfolding.generate_spec hg
  refine .intro hr hw hz hg {
    source_typed := hsource
    remaining_nonempty := hn
    equation_present := heq.symm ▸ hr.equation
    equation_body := hbody
    levels_wf := hlevels ▸ hw
    levels_length := ?_
    captures_length := hcapturesLength
    captures_typed := hcaptures
    major_prop := hmajor
    recursor_lhs := hmatch }
  rw [hlevels, heq]
  exact hl
end Lean4Lean.VEnv

namespace Lean4Lean.VEnv
open VExpr
set_option maxHeartbeats 1000000
/-- The actual Quot.mk reconstruction is definitionally equal to its major. -/
theorem QuotRegistered.reconstruct_major {env : VEnv} (H : QuotRegistered env)
    (hu : u.WF U) (hz : u ≈ .zero)
    (ha : env.HasType U Γ alpha (.sort u))
    (hr : env.HasType U Γ relation (.forallE alpha (.forallE alpha.lift (.sort .zero))))
    (hq : env.HasType U Γ major (mkApps (.const ``Quot [u]) [alpha, relation])) :
    env.IsDefEq U Γ major
      (mkApps (.const ``Quot.mk [u])
        [alpha, relation, mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha, relation, major]])
      (mkApps (.const ``Quot [u]) [alpha, relation]) := by
  have hw := H.propInhabitant_app hu hz ha hr hq
  have hc := HasType.const (Γ := Γ) H.constructor (ls := [u]) (by simpa using hu) rfl
  have h1 := HasType.app hc ha
  simp [inst, instL] at h1
  have h2 := HasType.app h1 hr
  simp [inst, inst_lift, ← lift_instN_lo] at h2
  have h3 := HasType.app h2 hw
  have hq1 := HasType.app (HasType.const (Γ := Γ) H.quotient
    (ls := [u]) (by simpa using hu) rfl) ha
  simp [inst, instL] at hq1
  have hq2 := HasType.app hq1 hr
  simp [inst] at hq2
  apply IsDefEq.proofIrrel (IsDefEq.defeq (IsDefEq.sortDF (l' := .zero) hu trivial hz) hq2) hq
  change env.HasType U Γ _ _
  simpa only [mkApps, List.foldl_cons, List.foldl_nil, inst, inst_lift, VLevel.inst, List.getD_cons_zero] using h3
end Lean4Lean.VEnv

/-! The concrete five-argument quotient prefix and its total typed replay. -/

namespace Lean4Lean
open VExpr InductiveSignature InductiveSignature.RecursorData
namespace QuotPrefixUnfolding

def atFive (u v : VLevel) (alpha relation beta fn compat : VExpr) : PrefixUnfolding :=
  let domain := mkApps (.const ``Quot [u]) [alpha, relation]
  let proof := mkApps (propInhabitant u) [alpha.lift, relation.lift, .bvar 0]
  { domains := [domain], result := beta.lift,
    constructor := mkApps (.const ``Quot.mk [u]) [alpha.lift, relation.lift, proof]
    equation := quotDefEq
    equationBody := ⟨((quotDefEq.type.takeForalls 6).getD ([], .bvar 0)).1,
      quotDefEq.lhs.stripLams, quotDefEq.rhs.stripLams, .bvar 3⟩
    captures := [alpha.lift, relation.lift, beta.lift, fn.lift, compat.lift, proof]
    levels := [u,v] }

theorem generate_atFive : QuotPrefixUnfolding.generate [u,v] [alpha, relation, beta, fn, compat] =
    some (atFive u v alpha relation beta fn compat) := by
  simp [QuotPrefixUnfolding.generate, atFive, supplyType, quotLiftConst, instL, inst, VLevel.inst,
    inst_lift, ← lift_instN_lo, VExpr.takeForalls, vars, mkApps,
    quotDefEq, CaseSchema.EquationBody.extract,
    VExpr.takeForalls, stripLams]

theorem atFive_rhs : (atFive u v alpha relation beta fn compat).rhs =
    .lam (mkApps (.const ``Quot [u]) [alpha, relation])
      (.app fn.lift (mkApps (propInhabitant u) [alpha.lift, relation.lift, .bvar 0])) := by
  simp [atFive, PrefixUnfolding.rhs, instantiateParams, quotDefEq, stripLams,
    instL, VExpr.subst, wrapLams]
end QuotPrefixUnfolding
namespace VEnv

private theorem InstForallsC.nil_result (H : InstForallsC env U Γ type [] result) :
    result = type := by cases H; rfl

/-- Every well-formed five-argument quotient-lift prefix at a proof source
has its concrete closed-delta replay, with no caller-supplied captures. -/
theorem QuotPrefixUnfold.atFive (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero)
    (H : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v]) [alpha, relation, beta, fn, compat])) :
    QuotPrefixUnfold env U Γ [u,v] [alpha, relation, beta, fn, compat]
      (.lam (mkApps (.const ``Quot [u]) [alpha, relation])
        (.app fn.lift (mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha.lift, relation.lift, .bvar 0]))) := by
  obtain ⟨result, hw, hsource⟩ := HasType.mkApps_telescope henv hΓ
    (HasType.const hr.lift (ls := [u,v]) (by simpa using And.intro hu hv) rfl) H (by rfl)
  cases hw with | cons ha hw =>
    cases hw with | cons hrel hw =>
      cases hw with | cons hbeta hw =>
        cases hw with | cons hf hw =>
          cases hw with | cons hcompat hw =>
            rw [hw.nil_result] at hsource
            simp [instL, inst, VLevel.inst, inst_lift, ← lift_instN_lo] at ha hrel hbeta hf hcompat hsource
            let domain := mkApps (.const ``Quot [u]) [alpha, relation]
            have haq : env.HasType U (domain :: Γ) alpha.lift (.sort u) := ha.weak henv
            have hrq : env.HasType U (domain :: Γ) relation.lift
                (.forallE alpha.lift (.forallE alpha.lift.lift (.sort .zero))) := by
              simpa only [HasType, lift, liftN, ← lift_liftN'] using hrel.weak henv.ordered (B := domain)
            have hmajor : env.HasType U (domain :: Γ) (.bvar 0)
                (mkApps (.const ``Quot [u]) [alpha.lift, relation.lift]) := .bvar .zero
            have hproof := hr.propInhabitant_app hu hz haq hrq hmajor
            have hconstructor := (hr.reconstruct_major hu hz haq hrq hmajor).hasType.2
            have hquot : env.HasType U Γ domain (.sort u) := by
              have h1 := (HasType.const hr.quotient (ls := [u]) (by simpa using hu) rfl).app ha
              have h2 := h1.app (by simpa [instL, inst, VLevel.inst] using hrel)
              simpa [domain, mkApps, instL, inst, inst_lift, VLevel.inst] using h2
            have hquotP := IsDefEq.defeq (IsDefEq.sortDF hu (by trivial) hz) hquot
            rw [← QuotPrefixUnfolding.atFive_rhs]
            apply QuotPrefixUnfold.ofGenerated (levels := [u,v]) hr (by simpa using And.intro hu hv) hz
              QuotPrefixUnfolding.generate_atFive
            · exact hsource
            · intro j hj hd
              have hj' : j < 6 := hj
              match j with
              | 0 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixUnfolding.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst] using haq
              | 1 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixUnfolding.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hrq
              | 2 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixUnfolding.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hbeta.weak henv.ordered (B := domain)
              | 3 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixUnfolding.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hf.weak henv.ordered (B := domain)
              | 4 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixUnfolding.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hcompat.weak henv.ordered (B := domain)
              | 5 => simpa [HasType, domain, lift, liftN, ← lift_liftN', QuotPrefixUnfolding.atFive, quotDefEq, VExpr.takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hproof
              | _ + 6 => omega
            · exact ⟨domain.lift, hquotP.weak henv, hmajor, hconstructor⟩
            · let args := [alpha.lift, relation.lift, beta.lift, fn.lift, compat.lift,
                mkApps (.const ``Quot.mk [u]) [alpha.lift, relation.lift,
                  mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha.lift, relation.lift, .bvar 0]]]
              have hm : ConstSpineDefEq env U (domain :: Γ)
                  (mkApps (.const ``Quot.lift [u,v]) args)
                  (mkApps (.const ``Quot.lift [u,v]) args) :=
                ⟨_, _, _, _, _, rfl, rfl, by simpa using And.intro hu hv,
                  by simpa using And.intro hu hv,
                  .cons (.refl _) (.cons (.refl _) .nil),
                  .cons ⟨_, haq⟩ (.cons ⟨_, hrq⟩ (.cons ⟨_, hbeta.weak henv.ordered⟩
                    (.cons ⟨_, hf.weak henv.ordered⟩ (.cons ⟨_, hcompat.weak henv.ordered⟩
                      (.cons ⟨_, hconstructor⟩ .nil)))))⟩
              simpa [QuotPrefixUnfolding.atFive, args, domain, etaOpen,
                quotDefEq, stripLams, instL, instOuter, inst, VLevel.inst,
                mkApps, lift, liftN, ← lift_instN_lo, inst_lift] using hm
end VEnv
end Lean4Lean
