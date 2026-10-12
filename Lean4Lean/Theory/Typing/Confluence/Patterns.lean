import Lean4Lean.Theory.Typing.Confluence.Registry
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaOverlap
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.QuotLiftTelescope
import Lean4Lean.Theory.Typing.PrefixUnfolding.SpineDefEq
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.WFFacts
import Lean4Lean.Theory.Typing.IotaReductTyped

/-! # The pattern table of a well-formed environment

The computational patterns of the confluence engine (`Params.Pat`) for a well-formed
environment (`ConcretePattern`): the δ rules of the registered definitions
(`DefinitionPattern`), the primitive quotient rule (`QuotPattern`, with its universe guard and
its parameter alignment checks), and the registered ι rules of `VEnv.pats` with the universe
guard of their recursor (`GuardedIotaPattern`): a large-eliminating recursor's rule is a
pattern step only where the source of its major is not `Prop`; at `Prop` sources the singleton
prefix unfolding computes instead (`FullReduction`). This file proves the non-overlap and
soundness facts of the table that `Params` asks for; the structure facts are in
`Confluence/StructureMajor.lean`.

An ι entry is a registered rule, and its soundness is the rule `IsDefEq.pat`, whose reduct
typing is `VEnv.WF.iotaReductTyped`. -/

namespace Lean4Lean.VEnv
open InductiveSignature

variable {env : VEnv}

/-! ## Definitions -/

namespace DefinitionPattern

variable {registry : Name → Option VDefVal}

theorem simple (H : DefinitionPattern registry p rhs) :
    ∃ shape : SimplePattern, p = shape.toPattern := by
  cases H with | intro _ _ => exact ⟨.defn _, rfl⟩

theorem origin
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionPattern registry p rhs) : PatternHeadsStoredRule env p := by
  cases H with
  | @intro value hl hc =>
    exact ⟨value.name, rfl, .inl ⟨value.toDefEq, VLevel.params value.uvars,
      (hregistry _ _ hl).2, rfl⟩⟩

theorem not_iota (H : DefinitionPattern registry
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) : False := by
  cases H

theorem unique (H : DefinitionPattern registry p rhs)
    (H' : DefinitionPattern registry q rhs') (hs : Subpattern sub p)
    (hi : q.inter sub = some intersection) : p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  cases H with
  | @intro value hl hc =>
    cases H' with
    | @intro value' hl' hc' =>
      cases hs
      simp only [Pattern.inter] at hi
      split at hi <;> try contradiction
      rename_i hname
      have hn : value'.name = value.name := by simpa using hname
      rw [hn] at hl'
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl, HEq.rfl⟩

theorem no_app_subpattern (H : DefinitionPattern registry p rhs)
    (hs : Subpattern (.app fn arg) p) : False := by
  cases H
  cases hs

/-- Soundness uses the installed equation at the occurrence's actual universe list, recovered
from its typing and constant lookup. -/
theorem sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionPattern registry p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) := by
  cases H with
  | @intro value hl hc =>
    cases hm
    obtain ⟨constant, hconstant, hlevels, hlength⟩ := ht.const_inv henv.orderedStrong hΓ
    have hregistered := hregistry _ _ hl
    cases Option.some.inj (hconstant.symm.trans hregistered.1)
    have he := IsDefEq.extra (Γ := Γ) hregistered.2 hlevels hlength
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlength,
      Pattern.RHS.apply] using (show env.IsDefEqU U Γ _ _ from ⟨_, he⟩)

/-- Every definition equation has a one-step pattern trace. -/
theorem equation_trace {value : VDefVal} {levels : List VLevel}
    (hlookup : registry value.name = some value)
    (hclosed : value.value.Closed) (hlength : levels.length = value.uvars) :
    PatternReductionTrace env U (DefinitionPattern registry) Γ
      (value.toDefEq.lhs.instL levels) (value.toDefEq.rhs.instL levels) := by
  simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlength]
  exact .pattern (DefinitionPattern.intro hlookup hclosed) .const trivial

end DefinitionPattern

/-! ## The quotient -/

abbrev quotPattern : Pattern := (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern

def quotPatternRHS : quotPattern.RHS :=
  .app (.var (.inl (some none))) (.var (.inr none))

def quotPatternCheck : quotPattern.Check :=
  .nonzero (.param 0)
    (.defeq (.var (.inl (some (some (some (some none))))))
      (.var (.inr (some (some none))))
      (.defeq (.var (.inl (some (some (some none)))))
        (.var (.inr (some none))) .true))

/-- The primitive quotient rule, guarded at `Prop` sources and with its parameter alignment
checks. -/
inductive QuotPattern (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop where
  | intro : QuotRegistered env → QuotPattern env quotPattern (quotPatternRHS, quotPatternCheck)

/-- `Quot.mk` is rigid once the quotient is declared. -/
theorem QuotRegistered.quotMk_rigid' (henv : env.WF) (hq : QuotRegistered env) :
    env.Rigid ``Quot.mk :=
  henv.quotMk_rigid hq.equation

/-- `Quot.lift` heads the stored quotient rule. -/
theorem QuotRegistered.lift_head (hq : QuotRegistered env) :
    quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift [.param 0, .param 1] ∧
      env.defeqs quotDefEq :=
  ⟨rfl, hq.equation⟩

/-- `Quot.lift` is not rigid once the quotient is declared. -/
theorem QuotRegistered.lift_not_rigid (hq : QuotRegistered env) : ¬env.Rigid ``Quot.lift :=
  fun hr => hr.defeqs _ hq.equation _ rfl

namespace QuotPattern

theorem simple (H : QuotPattern env p rhs) : ∃ s : SimplePattern, p = s.toPattern := by
  cases H
  exact ⟨.iota _ _ _ _, rfl⟩

theorem origin (H : QuotPattern env p rhs) : PatternHeadsStoredRule env p := by
  cases H with
  | intro hr => exact ⟨``Quot.lift, rfl, .inl ⟨quotDefEq, [.param 0, .param 1], hr.equation, rfl⟩⟩

theorem shape (H : QuotPattern env p rhs) : p = quotPattern := by cases H; rfl

theorem registered (H : QuotPattern env
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) :
    QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, rhs.2 = .nonzero (.param 0) rest := by
  have he : (SimplePattern.iota recursor major ctor fields).toPattern = quotPattern := H.shape
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SimplePattern.iota_toPattern_inj he
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

theorem equation_trace (hr : QuotRegistered env) (hn : ¬ u ≈ .zero) :
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

end QuotPattern

section
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
                (args := [alpha', relation', value])
                (show VExpr.WF env U Γ (mkApps (.const ``Quot.mk [u']) [alpha', relation', value])
                  from ⟨_, hmajor⟩) (by rfl)
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
                    obtain ⟨A, B, hp, hmj⟩ := H.app_inv henv.orderedStrong hΓ
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
                      have hh := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, ht⟩
                      obtain ⟨ci, hci, hw, hl⟩ := hh.const_inv henv.orderedStrong hΓ
                      cases Option.some.inj (hci.symm.trans hr.lift)
                      change levels.length = 2 at hl
                      obtain ⟨u, v, rfl⟩ : ∃ u v, levels = [u,v] := by
                        rcases levels with _ | ⟨u, _ | ⟨v, tail⟩⟩ <;> simp_all
                      obtain ⟨_, _, _, hc⟩ := (show VExpr.WF env U Γ _ from ⟨_, ht⟩).app_inv
                        henv.orderedStrong hΓ
                      have hch := VExpr.WF.of_mkApps henv.orderedStrong hΓ
                        (show VExpr.WF env U Γ (mkApps (.const ``Quot.mk ctorLevels) _) from ⟨_, hc⟩)
                      obtain ⟨ci, hci, hwc, hlc⟩ := hch.const_inv henv.orderedStrong hΓ
                      cases Option.some.inj (hci.symm.trans hr.constructor)
                      change ctorLevels.length = 1 at hlc
                      obtain ⟨u', rfl⟩ : ∃ u', ctorLevels = [u'] := by
                        rcases ctorLevels with _ | ⟨u', tail⟩ <;> simp_all
                      simp only [quotPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at hcheck
                      exact quotient_sound_spine henv hΓ hr
                        (hw u (by simp)) (hw v (by simp)) (hwc u' (by simp))
                        ⟨_, ht⟩ hcheck.2.1 hcheck.2.2.1
end

/-! ## Registered ι rules under the universe guard -/

/-- The universe guard of a registered recursor's ι rules: a large-eliminating recursor
computes by its rules only where the source sort of its owner is not `Prop`. -/
def _root_.Lean4Lean.InductiveSignature.RecursorData.guard (data : RecursorData)
    (p : Pattern) : p.Check :=
  if data.largeTarget then .nonzero (data.schema.sourceLevel data.owner data.levels) .true
  else .true

/-- A registered ι rule (`VEnv.pats`), with the universe guard of its recursor's registry
entry. -/
inductive GuardedIotaPattern (env : VEnv) : (p : Pattern) → p.RHS × p.Check → Prop where
  | intro {recN ctor : Name} {major fields : Nat}
      {rhs : (SimplePattern.iota recN major ctor fields).toPattern.RHS} {data : RecursorData} :
      env.pats (SimplePattern.iota recN major ctor fields).toPattern (rhs, .true) →
      env.recursorRegistry recN = some data →
      GuardedIotaPattern env (SimplePattern.iota recN major ctor fields).toPattern
        (rhs, data.guard _)

/-- Every registered pattern of a well-formed environment is registered unguarded (`.true`). -/
theorem WF.pats_true (henv : env.WF) {p : Pattern} {r : p.RHS × p.Check} (hp : env.pats p r) :
    r.2 = .true ∧ ∃ recN major ctor fields, p = (SimplePattern.iota recN major ctor fields).toPattern := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨decl, ds₀, env₀, env₁, -, -, -, -, -, rec, -, ru, -, hc, rfl, hr⟩ := H.pats_origin hp
  subst hr
  exact ⟨rfl, _, _, _, _, rfl⟩

/-- Every registered pattern is an unguarded ι rule of the table's form. -/
theorem WF.pats_guarded (henv : env.WF) {p : Pattern} {r : p.RHS × p.Check} (hp : env.pats p r) :
    ∃ recN major ctor fields data, p = (SimplePattern.iota recN major ctor fields).toPattern ∧
      env.recursorRegistry recN = some data ∧ RecursorEntry env recN data ∧
      data.majorOffset = major ∧ GuardedIotaPattern env p (r.1, data.guard p) := by
  obtain ⟨htrue, recN, major, ctor, fields, rfl⟩ := henv.pats_true hp
  obtain ⟨data, hl, he, hm⟩ := henv.pat_recursorRegistry hp
  refine ⟨recN, major, ctor, fields, data, rfl, hl, he, hm, ?_⟩
  obtain ⟨rhs, ck⟩ := r
  cases htrue
  exact .intro hp hl

namespace GuardedIotaPattern

theorem simple (H : GuardedIotaPattern env p rhs) : ∃ s : SimplePattern, p = s.toPattern := by
  cases H
  exact ⟨.iota _ _ _ _, rfl⟩

theorem origin (H : GuardedIotaPattern env p rhs) : PatternHeadsStoredRule env p := by
  cases H with
  | intro hp _ => exact ⟨_, Pattern.constHead_eq _, .inr ⟨_, _, hp, rfl⟩⟩

theorem pats (H : GuardedIotaPattern env p rhs) : env.pats p (rhs.1, .true) := by
  cases H with | intro hp _ => exact hp

theorem shape (H : GuardedIotaPattern env p rhs) :
    ∃ recN major ctor fields, p = (SimplePattern.iota recN major ctor fields).toPattern := by
  cases H; exact ⟨_, _, _, _, rfl⟩

theorem registered (henv : env.WF) {recursor ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    (H : GuardedIotaPattern env (SimplePattern.iota recursor major ctor fields).toPattern r) :
    ∃ data, RecursorRegistered env data ∧ data.name = recursor ∧ data.majorOffset = major ∧
      env.recursorRegistry recursor = some data ∧
      (∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner) ∧
      (data.largeTarget = true → ∃ rest,
        r.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest) := by
  have key : ∀ {P : Pattern} {r : P.RHS × P.Check}, GuardedIotaPattern env P r →
      (hP : P = (SimplePattern.iota recursor major ctor fields).toPattern) →
      ∃ data, RecursorRegistered env data ∧ data.name = recursor ∧ data.majorOffset = major ∧
        env.recursorRegistry recursor = some data ∧
        (∃ index : Fin data.schema.signature.constructors.size,
          data.schema.signature.constructors[index].owner = data.owner) ∧
        (data.largeTarget = true → ∃ rest,
          (hP ▸ r).2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest) := by
    intro P r H hP
    cases H with
    | @intro recN ctor' major' fields' rhs data hpat hl =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := SimplePattern.iota_toPattern_inj hP
      have hentry := recursorRegistry_entry hl
      have hreg := hentry.registered
      have hname := hentry.name_eq
      have hindex := hentry.index
      refine ⟨data, hreg, hname, henv.recursorEntry_majorOffset hpat (recursorRegistry_entry hl),
        hl, hindex, fun hlarge => ⟨.true, ?_⟩⟩
      simp [RecursorData.guard, hlarge]
  exact key H rfl

/-- The recursor of a registered ι rule is never the constructor of a registered ι rule. -/
theorem rec_ne_ctor (henv : env.WF)
    (H : GuardedIotaPattern env (SimplePattern.iota recursor major ctor fields).toPattern r)
    (H' : GuardedIotaPattern env (SimplePattern.iota recursor' major' ctor' fields').toPattern r') :
    recursor ≠ ctor' :=
  henv.patsIota.rec_ne_ctor H.pats H'.pats

theorem arity (henv : env.WF)
    (H : GuardedIotaPattern env (SimplePattern.iota recursor major ctor fields).toPattern r)
    (H' : GuardedIotaPattern env (SimplePattern.iota recursor' major' ctor' fields').toPattern r')
    (h : recursor = recursor') : major = major' := by
  subst h; exact henv.patsIota.arity H.pats H'.pats

theorem unique (henv : env.WF) (H : GuardedIotaPattern env p rhs)
    (H' : GuardedIotaPattern env q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  have H0 := H
  have H0' := H'
  cases H with
  | @intro recN ctor major fields rhs data hp hl =>
    cases H' with
    | @intro recN' ctor' major' fields' rhs' data' hp' hl' =>
      obtain ⟨hsub, hn, hm, hc, hf⟩ := SimplePattern.iota_overlap
        (fun h => arity henv H0' H0 h)
        (rec_ne_ctor henv H0' H0) hs hi
      subst hn hm hc hf
      cases henv.patsIota.functional hp hp'
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, hsub.symm, HEq.rfl⟩

theorem app_l (H : GuardedIotaPattern env p rhs) (hs : Subpattern (.app fn arg) p) :
    ¬Subpattern (.app left right) fn := by
  cases H
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  exact Subpattern.constVarN_noapp

theorem app_l_uniq (henv : env.WF) (H : GuardedIotaPattern env p rhs)
    (H' : GuardedIotaPattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  have H0 := H
  have H0' := H'
  cases H
  cases H'
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  obtain ⟨rfl, rfl⟩ := hs'.iota_app
  exact SimplePattern.iota_app_l_uniq (fun h => arity henv H0 H0' h) hb

theorem app_uniq (henv : env.WF) (H : GuardedIotaPattern env p rhs)
    (H' : GuardedIotaPattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hr : Subpattern right arg') : left.inter right = none := by
  have H0 := H
  have H0' := H'
  cases H
  cases H'
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  obtain ⟨rfl, rfl⟩ := hs'.iota_app
  exact SimplePattern.iota_app_uniq (rec_ne_ctor henv H0 H0') hl hr

/-- A registered ι rule is sound at every instance, guarded or not: it is `IsDefEq.pat`. -/
theorem sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (H : GuardedIotaPattern env p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) :=
  ⟨_, IsDefEq.pat (r := (rhs.1, Pattern.Check.true)) (chk := []) H.pats hm ht
    (henv.iotaReductTyped hΓ H.pats hm ht) trivial (by simp)⟩

theorem ctor_rigid (henv : env.WF)
    (H : GuardedIotaPattern env (SimplePattern.iota recursor major ctor fields).toPattern r) :
    env.Rigid ctor :=
  henv.patCtor_rigid' ⟨_, _, recursor, major, fields, H.pats, rfl⟩

/-- The recursor of a registered ι rule heads a registered pattern, so is not rigid. -/
theorem rec_not_rigid
    (H : GuardedIotaPattern env (SimplePattern.iota recursor major ctor fields).toPattern r) :
    ¬env.Rigid recursor := fun hr =>
  hr.pats _ _ H.pats (SimplePattern.iota_headConst _ _ _ _)

end GuardedIotaPattern

/-! ## The table -/

/-- The concrete pattern table of a well-formed environment. -/
def ConcretePattern (env : VEnv) (p : Pattern) (rhs : p.RHS × p.Check) : Prop :=
  DefinitionPattern env.definitionRegistry p rhs ∨ QuotPattern env p rhs ∨
    GuardedIotaPattern env p rhs

section
variable (henv : env.WF)
include henv

omit henv in
private theorem definitionRegistry_registered' :
    ∀ name value, env.definitionRegistry name = some value → DefinitionRegistered env value :=
  fun _ _ h => (definitionRegistry_registered h).1

theorem ConcretePattern.simple (H : ConcretePattern env p rhs) :
    ∃ s : SimplePattern, p = s.toPattern := by
  rcases H with H | H | H
  · exact H.simple
  · exact H.simple
  · exact H.simple

theorem ConcretePattern.origin (H : ConcretePattern env p rhs) : PatternHeadsStoredRule env p := by
  rcases H with H | H | H
  · exact H.origin (definitionRegistry_registered')
  · exact H.origin
  · exact H.origin

/-- A registered quotient lift is not a recursor. -/
theorem ConcretePattern.recursor_quot (hq : QuotRegistered env) :
    env.recursorRegistry ``Quot.lift = none := by
  apply recursorRegistry_none
  intro data hentry
  obtain ⟨p, r, hp, hh⟩ := hentry.pat
  exact henv.defeq_head_not_pat hq.equation rfl hp hh

theorem ConcretePattern.recursor {recursor ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    (H : ConcretePattern env (SimplePattern.iota recursor major ctor fields).toPattern r) :
    (∃ data, RecursorRegistered env data ∧ data.name = recursor ∧
      data.majorOffset = major ∧ env.recursorRegistry recursor = some data ∧
      (∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner) ∧
      (data.largeTarget = true → ∃ rest,
        r.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest)) ∨
    (QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, r.2 = .nonzero (.param 0) rest) := by
  rcases H with H | H | H
  · exact H.not_iota.elim
  · exact .inr H.registered
  · exact .inl (H.registered henv)

/-- Definition heads are neither the recursors nor the constructors of ι rules. -/
theorem ConcretePattern.definition_iota
    (hd : DefinitionPattern env.definitionRegistry (.const c) rd)
    (hn : GuardedIotaPattern env p rn) (hs : Subpattern (.const c) p) : False := by
  cases hd with
  | @intro value hl _ =>
    have hv := (definitionRegistry_registered hl).1
    have hdh : value.toDefEq.lhs.stripLams.getAppFnArgs.1 =
        .const value.name (VLevel.params value.uvars) := rfl
    cases hn with
    | intro hp hlk =>
      rcases hs.iota_const with h | h
      · exact henv.defeq_head_not_pat hv.2 hdh hp (by rw [SimplePattern.iota_headConst, h])
      · have hrigid := henv.patCtor_rigid' ⟨_, _, _, _, _, hp, rfl⟩
        exact hrigid.defeqs _ hv.2 _ (by rw [hdh, h])

/-- The recursor of a ι rule is neither `Quot.lift` nor `Quot.mk`, and its constructor is not
`Quot.lift`. -/
theorem ConcretePattern.recursor_quot_names (hq : QuotRegistered env)
    (H : GuardedIotaPattern env p rhs) :
    ∃ rc mr cc kc, p = (SimplePattern.iota rc mr cc kc).toPattern ∧
      rc ≠ ``Quot.lift ∧ rc ≠ ``Quot.mk ∧ cc ≠ ``Quot.lift := by
  have H0 := H
  cases H with
  | @intro recN ctor major fields rhs data hp hl =>
    refine ⟨_, _, _, _, rfl, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact henv.defeq_head_not_pat hq.equation rfl hp (by rw [SimplePattern.iota_headConst, h])
    · exact H0.rec_not_rigid (h ▸ hq.quotMk_rigid' henv)
    · exact hq.lift_not_rigid (h ▸ H0.ctor_rigid henv)

theorem ConcretePattern.uniq (H : ConcretePattern env p rhs)
    (H' : ConcretePattern env q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  rcases H with H | H | H <;> rcases H' with H' | H' | H'
  · exact H.unique H' hs hi
  · cases H; cases H'; cases hs; contradiction
  · cases H; cases hs; cases H'; simp [SimplePattern.toPattern, Pattern.inter] at hi
  · cases H with
    | intro hr =>
      cases H' with
      | @intro value hl hc =>
        cases sub <;> try contradiction
        rename_i name
        simp only [Pattern.inter, Option.ite_none_right_eq_some, Option.some.injEq] at hi
        have hv := (definitionRegistry_registered hl).1
        rcases hs.iota_const with he | he
        · exact (henv.quotLift_not_definition hr.equation hv.2 (VLevel.params value.uvars)
            (by simp [VDefVal.toDefEq, hi.1, he])).elim
        · exact ((hr.quotMk_rigid' henv).defeqs _ hv.2 (VLevel.params value.uvars)
            (by show VExpr.const value.name _ = _
                rw [show value.name = ``Quot.mk from hi.1.trans he])).elim
  · exact H.unique H' hs hi
  · have hq : QuotRegistered env := by cases H; assumption
    obtain ⟨rc, mr, cc, kc, rfl, hrc, hrm, _⟩ := ConcretePattern.recursor_quot_names henv hq H'
    cases H
    obtain ⟨_, he, _⟩ := SimplePattern.iota_overlap (fun h => (hrc h).elim) hrm hs hi
    exact (hrc he).elim
  · have H'' := H'
    cases H' with
    | @intro value _ _ =>
      cases sub <;> simp only [Pattern.inter, reduceCtorEq, Option.ite_none_right_eq_some] at hi
      obtain ⟨rfl, -⟩ := hi
      exact (ConcretePattern.definition_iota henv H'' H hs).elim
  · have hq : QuotRegistered env := by cases H'; assumption
    obtain ⟨rc, mr, cc, kc, rfl, hrc, _, hcq⟩ := ConcretePattern.recursor_quot_names henv hq H
    cases H'
    obtain ⟨_, he, _⟩ := SimplePattern.iota_overlap (fun h => (hrc h.symm).elim)
      (fun h => hcq h.symm) hs hi
    exact (hrc he.symm).elim
  · exact H.unique henv H' hs hi

theorem ConcretePattern.app_l (H : ConcretePattern env p rhs)
    (hs : Subpattern (.app fn arg) p) : ¬Subpattern (.app left right) fn := by
  rcases H with H | H | H
  · exact (H.no_app_subpattern hs).elim
  · exact H.app_l hs
  · exact H.app_l hs

theorem ConcretePattern.app_l_uniq (H : ConcretePattern env p rhs)
    (H' : ConcretePattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  rcases H with H | H | H
  · exact (H.no_app_subpattern hs).elim
  · rcases H' with H' | H' | H'
    · exact (H'.no_app_subpattern hs').elim
    · exact H.app_l_uniq H' hs hs' hb
    · have hq : QuotRegistered env := by cases H; assumption
      obtain ⟨rc, mr, cc, kc, rfl, hrc, -, -⟩ := ConcretePattern.recursor_quot_names henv hq H'
      cases H
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      exact SimplePattern.iota_app_l_uniq (fun h => (hrc h.symm).elim) hb
  · rcases H' with H' | H' | H'
    · exact (H'.no_app_subpattern hs').elim
    · have hq : QuotRegistered env := by cases H'; assumption
      obtain ⟨rc, mr, cc, kc, rfl, hrc, -, -⟩ := ConcretePattern.recursor_quot_names henv hq H
      cases H'
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      exact SimplePattern.iota_app_l_uniq (fun h => (hrc h).elim) hb
    · exact H.app_l_uniq henv H' hs hs' hb

theorem ConcretePattern.app_uniq (H : ConcretePattern env p rhs)
    (H' : ConcretePattern env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hr : Subpattern right arg') : left.inter right = none := by
  rcases H with H | H | H
  · exact (H.no_app_subpattern hs).elim
  · rcases H' with H' | H' | H'
    · exact (H'.no_app_subpattern hs').elim
    · exact H.app_uniq H' hs hs' hl hr
    · have hq : QuotRegistered env := by cases H; assumption
      obtain ⟨rc, mr, cc, kc, rfl, -, -, hcq⟩ := ConcretePattern.recursor_quot_names henv hq H'
      cases H
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      exact SimplePattern.iota_app_uniq (fun h => hcq h.symm) hl hr
  · rcases H' with H' | H' | H'
    · exact (H'.no_app_subpattern hs').elim
    · have hq : QuotRegistered env := by cases H'; assumption
      obtain ⟨rc, mr, cc, kc, rfl, -, hrm, -⟩ := ConcretePattern.recursor_quot_names henv hq H
      cases H'
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      exact SimplePattern.iota_app_uniq hrm hl hr
    · exact H.app_uniq henv H' hs hs' hl hr

theorem ConcretePattern.const_not_unfolding (H : ConcretePattern env (.const c) rhs) :
    env.recursorRegistry c = none ∧ (QuotRegistered env → c ≠ ``Quot.lift) := by
  rcases H with H | H | H
  · cases H with
    | @intro value hl _ =>
      have hv := (definitionRegistry_registered hl).1
      have hdh : value.toDefEq.lhs.stripLams.getAppFnArgs.1 =
          .const value.name (VLevel.params value.uvars) := rfl
      refine ⟨recursorRegistry_none fun data hentry => ?_, fun hq hn => ?_⟩
      · obtain ⟨p, r, hp, hh⟩ := hentry.pat
        exact henv.defeq_head_not_pat hv.2 hdh hp hh
      · exact henv.quotLift_not_definition hq.equation hv.2 (VLevel.params value.uvars)
          (by simp [VDefVal.toDefEq, hn])
  · cases H
  · cases H

theorem ConcretePattern.ctor_rigid
    (H : ConcretePattern env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r) :
    env.Rigid cc := by
  have key : ∀ {P r}, ConcretePattern env P r →
      P = (SimplePattern.iota rc mr cc kc).toPattern → env.Rigid cc := by
    intro P r H hp
    rcases H with H | H | H
    · cases H; cases hp
    · cases H with
      | intro hq =>
        obtain ⟨-, -, rfl, -⟩ := SimplePattern.iota_toPattern_inj hp.symm
        exact hq.quotMk_rigid' henv
    · subst hp; exact H.ctor_rigid henv
  exact key H rfl

theorem ConcretePattern.sound (hΓ : OnCtx Γ (env.IsType U)) (H : ConcretePattern env p r)
    (hm : p.Matches e m1 m2) (ht : env.HasType U Γ e A)
    (hc : r.2.OK (env.IsDefEqU U Γ) m1 m2) : env.IsDefEqU U Γ e (r.1.apply m1 m2) := by
  rcases H with H | H | H
  · exact DefinitionPattern.sound henv hΓ (definitionRegistry_registered') H hm ht
  · exact QuotPattern.sound henv hΓ H hm ht hc
  · exact H.sound henv hΓ hm ht

end

end Lean4Lean.VEnv
