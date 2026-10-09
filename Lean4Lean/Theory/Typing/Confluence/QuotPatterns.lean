import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaOverlap
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.PrefixUnfolding.SpineDefEq
import Lean4Lean.Theory.Typing.QuotLiftTelescope
import Lean4Lean.Theory.Typing.QuotPropInhabitant
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.Injectivity

/-! The concrete primitive quotient iota pattern. Parameter guards compare
actual captured terms; the source-universe guard leaves proof-source
computation to the closed quotient prefix program. -/

namespace Lean4Lean.VEnv

abbrev quotPattern : Pattern := (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern

def quotPatternRHS : quotPattern.RHS :=
  .app (.var (.inl (some none))) (.var (.inr none))

def quotPatternCheck : quotPattern.Check :=
  .nonzero (.param 0)
    (.defeq (.var (.inl (some (some (some (some none))))))
      (.var (.inr (some (some none))))
      (.defeq (.var (.inl (some (some (some none)))))
        (.var (.inr (some none))) .true))

inductive QuotPattern (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop where
  | intro : QuotRegistered env → QuotPattern env quotPattern (quotPatternRHS, quotPatternCheck)

namespace QuotPattern

theorem simple (H : QuotPattern env p rhs) : ∃ s : SimplePattern, p = s.toPattern := by
  cases H
  exact ⟨.iota _ _ _ _, rfl⟩

theorem origin (H : QuotPattern env p rhs) : PatternHeadsStoredRule env p := by
  cases H with
  | intro hr => exact ⟨quotDefEq, ``Quot.lift, [.param 0, .param 1], hr.equation, rfl, rfl⟩

theorem shape (H : QuotPattern env p rhs) : p = quotPattern := by cases H; rfl

theorem registered (H : QuotPattern env
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) :
    QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, rhs.2 = .nonzero (.param 0) rest := by
  have he : (SimplePattern.iota recursor major ctor fields).toPattern = quotPattern := H.shape
  have hi : (SimplePattern.iota recursor major ctor fields).toPattern.inter quotPattern =
      some quotPattern := by rw [he]; exact Pattern.inter_self _
  simp only [quotPattern, SimplePattern.toPattern, Pattern.inter, bind,
    Option.bind_eq_some_iff] at hi
  obtain ⟨left, hl, right, hr, _⟩ := hi
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hl
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hr
  cases H with
  | intro hr => exact ⟨hr, rfl, rfl, rfl, rfl, _, rfl⟩

theorem unique (H : QuotPattern env p rhs) (H' : QuotPattern env q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  cases H
  cases H'
  obtain ⟨he, _⟩ := SimplePattern.iota_overlap (by intros; rfl) (by decide) hs hi
  exact ⟨rfl, he.symm, HEq.rfl⟩

theorem app_l (H : QuotPattern env p rhs) (hs : Subpattern (.app fn arg) p) :
    ¬Subpattern (.app left right) fn := by
  cases H
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  exact Subpattern.constVarN_noapp

theorem app_l_uniq (H : QuotPattern env p rhs) (H' : QuotPattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  cases H
  cases H'
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  obtain ⟨rfl, rfl⟩ := hs'.iota_app
  exact SimplePattern.iota_app_l_uniq (by intros; rfl) hb

theorem app_uniq (H : QuotPattern env p rhs) (H' : QuotPattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hr : Subpattern right arg') : left.inter right = none := by
  cases H
  cases H'
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  obtain ⟨rfl, rfl⟩ := hs'.iota_app
  exact SimplePattern.iota_app_uniq (by decide) hl hr

end QuotPattern

theorem QuotRegistered.definition_names (henv : env.WF) (H : QuotRegistered env)
    (hd : DefinitionRegistered env value) : value.name ≠ ``Quot.lift ∧ value.name ≠ ``Quot.mk := by
  have hm : quotDefEq.HasConstructorMajor ``Quot.mk :=
    ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
  constructor
  · intro hn
    exact hd.not_constructor_equation henv H.equation (by rw [hn]; rfl) hm
  · intro hn
    apply henv.installed_constructor_rigid H.equation hm value.toDefEq hd.2 (VLevel.params value.uvars)
    change VExpr.const value.name _ = VExpr.const ``Quot.mk _
    rw [hn]

def DefinitionQuotPattern (env : VEnv) (registry : Name → Option VDefVal)
    (p : Pattern) (rhs : p.RHS × p.Check) : Prop :=
  DefinitionPattern registry p rhs ∨ QuotPattern env p rhs

namespace DefinitionQuotPattern

theorem unique (henv : env.WF)
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionQuotPattern env registry p rhs) (H' : DefinitionQuotPattern env registry q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  rcases H with H | H <;> rcases H' with H' | H'
  · exact H.unique H' hs hi
  · cases H
    cases H'
    cases hs
    contradiction
  · cases H with
    | intro hr =>
      cases H' with
      | @intro value hl hc =>
        cases sub <;> try contradiction
        rename_i name
        simp only [Pattern.inter, Option.ite_none_right_eq_some, Option.some.injEq] at hi
        have hn := hs.iota_const
        have hd := hr.definition_names henv (hregistry _ _ hl)
        exact (hn.elim (fun he => hd.1 (hi.1.trans he))
          (fun he => hd.2 (hi.1.trans he))).elim
  · exact H.unique H' hs hi

end DefinitionQuotPattern
theorem QuotPattern.equation_trace (hr : QuotRegistered env) (hn : ¬ u ≈ .zero) :
    PatternReductionTrace env U (QuotPattern env) Γ
      (quotDefEq.lhs.instL [u,v]) (quotDefEq.rhs.instL [u,v]) := by
  apply PatternReductionTrace.lam
  apply PatternReductionTrace.lam
  apply PatternReductionTrace.lam
  apply PatternReductionTrace.lam
  apply PatternReductionTrace.lam
  apply PatternReductionTrace.lam
  refine .pattern (QuotPattern.intro hr)
    (.app (.var (.var (.var (.var (.var .const))))) (.var (.var (.var .const)))) ?_
  exact ⟨hn, ⟨_, HasType.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))⟩,
    ⟨_, HasType.bvar (.succ (.succ (.succ (.succ .zero))))⟩, trivial⟩

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv
open VExpr
set_option maxHeartbeats 1000000
private theorem quotient_sound_spine (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hu' : u'.WF U)
    (H : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u']) [alpha', relation', value]]))
    (hae : env.IsDefEqU U Γ alpha alpha') (hre : env.IsDefEqU U Γ relation relation') :
    env.IsDefEqU U Γ
      (mkApps (.const ``Quot.lift [u,v])
        [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u']) [alpha', relation', value]])
      (.app fn value) := by
  obtain ⟨result, hw⟩ := quotient_walk henv hΓ hr hu hv H
  cases hw with | cons ha hw =>
    cases hw with | cons hrel hw =>
      cases hw with | cons hbeta hw =>
        cases hw with | cons hf hw =>
          cases hw with | cons hcompat hw =>
            cases hw with | cons hmajor hw =>
              simp [instL, inst, VLevel.inst, inst_lift, ← lift_instN_lo] at ha hrel hbeta hf hcompat hmajor
              obtain ⟨_, hcw, _⟩ := HasType.mkApps_telescope henv hΓ
                (HasType.const hr.constructor (ls := [u']) (by simpa using hu') rfl)
                (show VExpr.WF env U Γ _ from ⟨_, hmajor⟩) (by rfl)
              cases hcw with | cons hca hcw =>
                cases hcw with | cons hcr hcw =>
                  cases hcw with | cons hvalue _ =>
                    simp [instL, inst, VLevel.inst, inst_lift] at hca hcr hvalue
                    have hvalue' := hvalue.defeqU_r henv hΓ hae.symm
                    have hue : u' ≈ u :=
                      (hca.uniqU henv hΓ (ha.defeqU_l henv hΓ hae)).sort_inv henv hΓ
                    have hmatch : ConstSpineDefEq env U Γ
                        (mkApps (.const ``Quot.mk [u']) [alpha', relation', value])
                        (mkApps (.const ``Quot.mk [u]) [alpha, relation, value]) :=
                      ⟨_, _, _, _, _, rfl, rfl, by simpa using hu', by simpa using hu,
                        .cons hue .nil, .cons hae.symm (.cons hre.symm (.cons ⟨_, hvalue⟩ .nil))⟩
                    have hm := hmatch.defeq henv hΓ hmajor
                    obtain ⟨A, B, hp, hmj⟩ := H.app_inv henv.ordered hΓ
                    have hreplace : env.IsDefEqU U Γ
                        (mkApps (.const ``Quot.lift [u,v])
                          [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u']) [alpha', relation', value]])
                        (mkApps (.const ``Quot.lift [u,v])
                          [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u]) [alpha, relation, value]]) :=
                      ⟨_, hp.appDF (hm.of_l henv hΓ hmj)⟩
                    let ds := ((quotDefEq.type.takeForalls 6).getD ([], .bvar 0)).1
                    have he := IsDefEq.extra_instOuter henv hΓ hr.equation
                      (ls := [u,v]) (by simpa using And.intro hu hv) rfl
                      (doms := ds) (lhsBody := quotDefEq.lhs.stripLams)
                      (rhsBody := quotDefEq.rhs.stripLams) (typeBody := .bvar 3)
                      rfl rfl rfl (args := [alpha, relation, beta, fn, compat, value]) rfl ?_
                    · refine hreplace.trans henv hΓ ⟨beta, ?_⟩
                      simpa [quotDefEq, stripLams, instL, instOuter, inst,
                        VLevel.inst, ← lift_instN_lo, inst_lift, mkApps] using he
                    · intro j hj hd
                      have hj' : j < 6 := hj
                      match j with
                      | 0 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst] using ha
                      | 1 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hrel
                      | 2 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hbeta
                      | 3 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hf
                      | 4 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hcompat
                      | 5 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hvalue'
                      | _ + 6 => omega
theorem QuotPattern.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotPattern env p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type)
    (hcheck : rhs.2.OK (env.IsDefEqU U Γ) levels values) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) := by
  cases H with
  | intro hr =>
    cases hm with
    | app hf hc =>
      cases hf with | var hf =>
        cases hf with | var hf =>
          cases hf with | var hf =>
            cases hf with | var hf =>
              cases hf with | var hf =>
                cases hf
                cases hc with | var hc =>
                  cases hc with | var hc =>
                    cases hc with | var hc =>
                      cases hc
                      rename_i ctorLevels compat fn beta relation alpha value relation' alpha'
                      change env.HasType U Γ (mkApps (.const ``Quot.lift levels)
                        [alpha, relation, beta, fn, compat,
                          mkApps (.const ``Quot.mk ctorLevels) [alpha', relation', value]]) type at ht
                      have hh := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
                      obtain ⟨ci, hci, hw, hl⟩ := hh.const_inv henv.ordered hΓ
                      cases Option.some.inj (hci.symm.trans hr.lift)
                      change levels.length = 2 at hl
                      obtain ⟨u, v, rfl⟩ : ∃ u v, levels = [u,v] := by
                        rcases levels with _ | ⟨u, _ | ⟨v, tail⟩⟩ <;> simp_all
                      obtain ⟨_, _, _, hc⟩ := (show VExpr.WF env U Γ _ from ⟨_, ht⟩).app_inv henv.ordered hΓ
                      have hch := VExpr.WF.of_mkApps henv.ordered hΓ
                        (show VExpr.WF env U Γ (mkApps (.const ``Quot.mk ctorLevels) _) from ⟨_, hc⟩)
                      obtain ⟨ci, hci, hwc, hlc⟩ := hch.const_inv henv.ordered hΓ
                      cases Option.some.inj (hci.symm.trans hr.constructor)
                      change ctorLevels.length = 1 at hlc
                      obtain ⟨u', rfl⟩ : ∃ u', ctorLevels = [u'] := by
                        rcases ctorLevels with _ | ⟨u', tail⟩ <;> simp_all
                      simp only [quotPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at hcheck
                      have hresult := quotient_sound_spine henv hΓ hr
                        (hw u (by simp)) (hw v (by simp)) (hwc u' (by simp))
                        ⟨_, ht⟩ hcheck.2.1 hcheck.2.2.1
                      exact hresult
end Lean4Lean.VEnv
