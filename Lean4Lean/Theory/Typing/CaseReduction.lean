import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Inductive.CaseCapture
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.EtaOpening
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality

/-! Concrete applied reduction from declaration-generated abstract case rules.
Its endpoints are the exact restored templates specialized at one full typed
argument telescope. Neither replacement bodies nor reduction callbacks occur
in the relation. -/

namespace Lean4Lean
open Lean4Lean
namespace VEnv

open InductiveSignature InductiveSignature.CaseSchema

/-- Case right sides contain only the selected minor and field variables,
applied in order. They introduce no additional head computation. -/
inductive VariableApplications : VExpr → Prop where
  | bvar : VariableApplications (.bvar i)
  | app : VariableApplications fn → VariableApplications arg → VariableApplications (.app fn arg)

theorem VariableApplications.instL_eq (H : VariableApplications e) : e.instL levels = e := by
  induction H with
  | bvar => rfl
  | app _ _ ihf iha => simp only [VExpr.instL, ihf, iha]

private theorem VariableApplications.mkApps (hf : VariableApplications fn)
    (ha : ∀ arg ∈ args, VariableApplications arg) : VariableApplications (VExpr.mkApps fn args) := by
  induction args generalizing fn with
  | nil => exact hf
  | cons arg args ih => exact ih (.app hf (ha _ (by simp))) fun a h => ha a (by simp [h])

/-- The major premise follows the declaration's common parameters, motive,
minors, and selected family's indices. -/
def caseMajorArity (schema : CaseSchema) (owner : Fin schema.signature.families.size) : Nat :=
  schema.signature.params.length + 1 + (schema.view owner).constructors.size +
    schema.signature.families[owner].indices.length

/-- An installed abstract family fixes where evaluation may enter its major
premise, including families with no constructors. -/
def IsCaseMajorPremise (env : VEnv) (e : VExpr) : Prop :=
  ∃ (schema : CaseSchema) (block : Name) (owner : Fin schema.signature.families.size)
      (levels : List VLevel) (args : List VExpr),
    env.eliminators block schema ∧ e = VExpr.mkApps (.elim block owner.val levels) args ∧
      args.length = caseMajorArity schema owner

/-- A prefix up to, but excluding, an installed family's major premise. -/
def IsCasePrefix (env : VEnv) (e : VExpr) : Prop :=
  ∃ (schema : CaseSchema) (block : Name) (owner : Fin schema.signature.families.size)
      (levels : List VLevel) (args : List VExpr),
    env.eliminators block schema ∧ e = VExpr.mkApps (.elim block owner.val levels) args ∧
      args.length ≤ caseMajorArity schema owner

theorem IsCaseMajorPremise.toPrefix (H : IsCaseMajorPremise env e) : IsCasePrefix env e := by
  obtain ⟨schema, block, owner, levels, args, hl, he, hn⟩ := H
  exact ⟨schema, block, owner, levels, args, hl, he, Nat.le_of_eq hn⟩

/-- The arguments of a case equation, typed at each specialized domain of its
actual generated telescope. This includes motive, minors and constructor
fields; specialized constructor parameters remain in the left template. -/
def CaseArguments (env : VEnv) (U : Nat) (Γ : List VExpr)
    (rule : AppliedRule) (levels : List VLevel) (arguments : List VExpr) : Prop :=
  arguments.length = rule.body.domains.length ∧
  ∀ j (hj : j < arguments.length) (hd : j < rule.body.domains.length),
    env.HasType U Γ arguments[j]
      (instantiateParams (rule.body.domains[j].instL levels) (arguments.take j))

/-- A concrete case computation, applied to the full equation telescope. The
closed typing premises are exactly those of `IsDefEq.elimIota`; the argument
premise is ordinary dependent telescope typing. -/
inductive CaseStep (env : VEnv) (U : Nat) (Γ : List VExpr) :
    AppliedRule → List VLevel → List VExpr → Prop where
  | iota {schema : CaseSchema} {owner : Fin schema.signature.families.size}
      {rule : AppliedRule} :
    env.eliminators block schema →
    schema.Generates block owner rule →
    RuleClosed rule.equation →
    schema.Permission U owner levels target →
    env.HasType U Γ (rule.equation.lhs.instL (target :: levels))
      (rule.equation.type.instL (target :: levels)) →
    env.HasType U Γ (rule.equation.rhs.instL (target :: levels))
      (rule.equation.type.instL (target :: levels)) →
    CaseArguments env U Γ rule (target :: levels) arguments →
    CaseStep env U Γ rule (target :: levels) arguments

theorem CaseStep.generates (H : CaseStep env U Γ rule levels arguments) :
    ∃ (schema : CaseSchema) (block : Name) (owner : Fin schema.signature.families.size),
      env.eliminators block schema ∧ schema.Generates block owner rule := by
  cases H with
  | iota hl hg => exact ⟨_, _, _, hl, hg⟩

private theorem closed_wrapLams_body {domains : List VExpr} {body : VExpr}
    (h : (VExpr.wrapLams domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapLams domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private theorem closed_wrapForalls_body {domains : List VExpr} {body : VExpr}
    (h : (VExpr.wrapForalls domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapForalls domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Every open template is scoped exactly under its full generated telescope. -/
theorem CaseStep.closed (H : CaseStep env U Γ rule levels arguments) :
    rule.body.lhs.ClosedN arguments.length ∧
    rule.body.rhs.ClosedN arguments.length ∧ rule.body.type.ClosedN arguments.length := by
  cases H with
  | iota _ hgen hc _ _ _ ha =>
    obtain ⟨hl, hr, ht⟩ := hgen.body_exact
    unfold RuleClosed at hc
    rw [← hl, ← hr, ← ht] at hc
    exact ⟨by simpa [ha.1] using closed_wrapLams_body hc.1,
      by simpa [ha.1] using closed_wrapLams_body hc.2.1,
      by simpa [ha.1] using closed_wrapForalls_body hc.2.2⟩

theorem CaseStep.length (H : CaseStep env U Γ rule levels arguments) :
    arguments.length = rule.body.domains.length := by
  cases H with | iota _ _ _ _ _ _ ha => exact ha.1

/-- Substitution into actual arguments commutes with simultaneous application
of a scoped template. -/
theorem instantiateParams_subst {body : VExpr} (hc : body.ClosedN arguments.length)
    (σ : VExpr.Subst) :
    (instantiateParams body arguments).subst σ =
      instantiateParams body (arguments.map (·.subst σ)) := by
  change (body.subst (VExpr.Subst.ofList arguments)).subst σ =
    body.subst (VExpr.Subst.ofList (arguments.map (·.subst σ)))
  rw [VExpr.subst_subst]
  apply VExpr.subst_congr_closedN hc
  intro i hi
  simp [VExpr.Subst.comp, VExpr.Subst.ofList, hi]

theorem instantiateParams_lift' {body : VExpr} (hc : body.ClosedN arguments.length)
    (ρ : Lift) :
    (instantiateParams body arguments).lift' ρ =
      instantiateParams body (arguments.map (·.lift' ρ)) := by
  change (body.subst (VExpr.Subst.ofList arguments)).lift' ρ =
    body.subst (VExpr.Subst.ofList (arguments.map (·.lift' ρ)))
  rw [VExpr.lift'_subst]
  apply VExpr.subst_congr_closedN hc
  intro i hi
  simp [VExpr.Subst.lift_r, VExpr.Subst.ofList, hi]

theorem instantiateParams_liftN {body : VExpr} (hc : body.ClosedN arguments.length) :
    (instantiateParams body arguments).liftN n k =
      instantiateParams body (arguments.map fun arg => arg.liftN n k) := by
  simpa only [VExpr.lift'_consN_skipN] using
    instantiateParams_lift' hc (.consN (.skipN .refl n) k)

theorem instantiateParams_instN {body : VExpr} (hc : body.ClosedN arguments.length) :
    (instantiateParams body arguments).inst value k =
      instantiateParams body (arguments.map fun arg => arg.inst value k) := by
  simpa only [← VExpr.instN_eq] using
    instantiateParams_subst hc (VExpr.Subst.liftN (VExpr.Subst.one value) k)

private theorem closed_wrapForalls_domain {domains : List VExpr} {body : VExpr}
    (hc : (VExpr.wrapForalls domains body).ClosedN k)
    (hi : i < domains.length) : domains[i].ClosedN (k + i) := by
  induction domains generalizing k i with
  | nil => cases hi
  | cons domain domains ih =>
    cases i with
    | zero => exact hc.1
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih hc.2 (Nat.lt_of_succ_lt_succ hi)

theorem CaseStep.domains_closed (H : CaseStep env U Γ rule levels arguments)
    (hi : i < rule.body.domains.length) : rule.body.domains[i].ClosedN i := by
  cases H with
  | iota _ hgen hc =>
    have ht := hgen.body_exact.2.2
    have hc := hc.2.2
    rw [← ht] at hc
    simpa using closed_wrapForalls_domain hc hi

def CaseApplicationMap (actual : Application) (f : VExpr → VExpr) : Application :=
  { actual with arguments := actual.arguments.map f, ctorArguments := actual.ctorArguments.map f }

@[simp] theorem case_application_map_levels (actual : Application) (f : VExpr → VExpr) :
    (CaseApplicationMap actual f).levels = actual.levels := rfl

@[simp] theorem case_capture_map (rule : AppliedRule) (actual : Application) (f : VExpr → VExpr) :
    rule.capture (CaseApplicationMap actual f) = (rule.capture actual).map f := by
  simp [AppliedRule.capture, CaseApplicationMap, List.map_append, List.map_take, List.map_drop]

@[simp] theorem case_application_liftN (actual : Application) :
    (CaseApplicationMap actual fun e => e.liftN n k).expr = actual.expr.liftN n k := by
  simp [CaseApplicationMap, Application.expr, VExpr.liftN]

@[simp] theorem case_application_lift' (actual : Application) :
    (CaseApplicationMap actual fun e => e.lift' ρ).expr = actual.expr.lift' ρ := by
  simp [CaseApplicationMap, Application.expr, VExpr.lift', VExpr.lift'_mkApps]

@[simp] theorem case_application_instN (actual : Application) :
    (CaseApplicationMap actual fun e => e.inst value k).expr = actual.expr.inst value k := by
  simp [CaseApplicationMap, Application.expr, VExpr.inst]

private theorem spine_lift' (e : VExpr) :
    (e.lift' ρ).getAppFnArgs =
      (e.getAppFnArgs.1.lift' ρ, e.getAppFnArgs.2.map fun e => e.lift' ρ) := by
  suffices ∀ args, VExpr.getAppFnArgs.go (e.lift' ρ) (args.map fun e => e.lift' ρ) =
      ((VExpr.getAppFnArgs.go e args).1.lift' ρ,
        (VExpr.getAppFnArgs.go e args).2.map fun e => e.lift' ρ) from this []
  induction e with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

private theorem case_application_extract (actual : Application) :
    Application.extract actual.expr = some actual := by
  cases actual
  simp [Application.extract, Application.expr, VExpr.getAppFnArgs,
    VExpr.getAppFnArgs_go_mkApps, VExpr.getAppFnArgs.go]

theorem case_elim_spine_lift'_inv
    (h : VExpr.mkApps (.elim block owner packed) args = e.lift' ρ) :
    ∃ originalArgs, e = VExpr.mkApps (.elim block owner packed) originalArgs ∧
      args = originalArgs.map (fun e => e.lift' ρ) := by
  have hs := congrArg VExpr.getAppFnArgs h
  rw [spine_mkApps_exact _ _ rfl, spine_lift'] at hs
  have hh := congrArg Prod.fst hs
  cases hf : e.getAppFnArgs.1 <;> simp only [hf, VExpr.lift'] at hh <;> try contradiction
  cases hh
  refine ⟨e.getAppFnArgs.2, ?_, congrArg Prod.snd hs⟩
  simpa only [hf] using (VExpr.mkApps_getAppFnArgs e).symm

theorem case_application_injective {a b : Application} (h : a.expr = b.expr) : a = b := by
  have he := congrArg Application.extract h
  rw [case_application_extract, case_application_extract] at he
  exact Option.some.inj he

theorem case_application_spine (a : Application) :
    a.expr.getAppFnArgs = (.elim a.block a.owner a.levels,
      a.arguments ++ [VExpr.mkApps (.const a.ctorName a.ctorLevels) a.ctorArguments]) := by
  have he : a.expr = VExpr.mkApps (.elim a.block a.owner a.levels)
      (a.arguments ++ [VExpr.mkApps (.const a.ctorName a.ctorLevels) a.ctorArguments]) := by
    simp [Application.expr, VExpr.mkApps, List.foldl_append]
  rw [he]
  exact spine_mkApps_exact _ _ rfl

theorem CaseStep.weakN (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (H : CaseStep env U Γ rule levels arguments) :
    CaseStep env U Γ' rule levels (arguments.map fun e => e.liftN n k) := by
  have hdomains : ∀ i (hi : i < rule.body.domains.length), rule.body.domains[i].ClosedN i :=
    fun _ hi => H.domains_closed hi
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp ht hr ha =>
    have ht' := ht.weakN henv.ordered W
    have hr' := hr.weakN henv.ordered W
    simp only [hc.1.instL.liftN_eq (Nat.zero_le _),
      hc.2.1.instL.liftN_eq (Nat.zero_le _), hc.2.2.instL.liftN_eq (Nat.zero_le _)] at ht' hr'
    refine .iota hl hg hc hp ht' hr' ⟨by simpa using ha.1, ?_⟩
    intro i hi hd
    have hi' : i < arguments.length := by simpa using hi
    have hcl : (rule.body.domains[i].instL (target :: levels)).ClosedN (arguments.take i).length := by
      simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi')] using (hdomains i hd).instL
    have hty := (ha.2 i hi' hd).weakN henv.ordered W
    rw [instantiateParams_liftN hcl] at hty
    simpa only [List.getElem_map, List.map_take] using hty

theorem CaseStep.weak' (henv : env.WF) (W : Ctx.Lift' ρ Γ Γ')
    (H : CaseStep env U Γ rule levels arguments) :
    CaseStep env U Γ' rule levels (arguments.map fun e => e.lift' ρ) := by
  have hdomains : ∀ i (hi : i < rule.body.domains.length), rule.body.domains[i].ClosedN i :=
    fun _ hi => H.domains_closed hi
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp ht hr ha =>
    have ht' := ht.weak' henv.ordered W
    have hr' := hr.weak' henv.ordered W
    simp only [hc.1.instL.lift'_eq .zero,
      hc.2.1.instL.lift'_eq .zero, hc.2.2.instL.lift'_eq .zero] at ht' hr'
    refine .iota hl hg hc hp ht' hr' ⟨by simpa using ha.1, ?_⟩
    intro i hi hd
    have hi' : i < arguments.length := by simpa using hi
    have hcl : (rule.body.domains[i].instL (target :: levels)).ClosedN (arguments.take i).length := by
      simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi')] using (hdomains i hd).instL
    have hty := (ha.2 i hi' hd).weak' henv.ordered W
    rw [instantiateParams_lift' hcl ρ] at hty
    simpa only [List.getElem_map, List.map_take] using hty

theorem CaseStep.instN (henv : env.WF) (hvalue : env.HasType U Γ₀ value valueType)
    (W : Ctx.InstN Γ₀ value valueType k Γ Γ') (H : CaseStep env U Γ rule levels arguments) :
    CaseStep env U Γ' rule levels (arguments.map fun e => e.inst value k) := by
  have hdomains : ∀ i (hi : i < rule.body.domains.length), rule.body.domains[i].ClosedN i :=
    fun _ hi => H.domains_closed hi
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp ht hr ha =>
    have ht' := ht.instN henv.ordered W hvalue
    have hr' := hr.instN henv.ordered W hvalue
    simp only [hc.1.instL.instN_eq (Nat.zero_le _),
      hc.2.1.instL.instN_eq (Nat.zero_le _), hc.2.2.instL.instN_eq (Nat.zero_le _)] at ht' hr'
    refine .iota hl hg hc hp ht' hr' ⟨by simpa using ha.1, ?_⟩
    intro i hi hd
    have hi' : i < arguments.length := by simpa using hi
    have hcl : (rule.body.domains[i].instL (target :: levels)).ClosedN (arguments.take i).length := by
      simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi')] using (hdomains i hd).instL
    have hty := (ha.2 i hi' hd).instN henv.ordered W hvalue
    rw [instantiateParams_instN hcl] at hty
    simpa only [List.getElem_map, List.map_take] using hty

/-- Matching keeps a fixed abstract head, constructor and arities. The
complete generated left template is checked at deterministically recovered
arguments, including restored parameter specializations and dependent indices.
The equality check permits duplicated occurrences to reduce independently. -/
structure CaseRedex (env : VEnv) (U : Nat) (Γ : List VExpr)
    (rule : AppliedRule) (actual : Application) : Prop where
  source : CaseStep env U Γ rule actual.levels (rule.capture actual)
  block_eq : actual.block = rule.application.block
  owner_eq : actual.owner = rule.application.owner
  ctor_eq : actual.ctorName = rule.application.ctorName
  arguments_length : actual.arguments.length = rule.application.arguments.length
  ctorArguments_length : actual.ctorArguments.length = rule.application.ctorArguments.length
  levels_eq : List.Forall₂ (· ≈ ·) actual.levels
    (rule.application.levels.map (·.inst actual.levels))
  ctorLevels_eq : List.Forall₂ (· ≈ ·) actual.ctorLevels
    (rule.application.ctorLevels.map (·.inst actual.levels))
  guard : env.IsDefEqU U Γ actual.expr (rule.lhs actual.levels (rule.capture actual))

/-- Pointwise movement of the two spines preserves their fixed symbols and
universe spines. Repeated term occurrences may move independently. -/
structure CaseApplicationRelated (R : VExpr → VExpr → Prop) (a b : Application) : Prop where
  block_eq : a.block = b.block
  owner_eq : a.owner = b.owner
  levels_eq : a.levels = b.levels
  ctor_eq : a.ctorName = b.ctorName
  ctorLevels_eq : a.ctorLevels = b.ctorLevels
  arguments : List.Forall₂ R a.arguments b.arguments
  ctorArguments : List.Forall₂ R a.ctorArguments b.ctorArguments

private theorem case_forall₂_take (h : List.Forall₂ R xs ys) :
    List.Forall₂ R (xs.take n) (ys.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h _ ih => cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih (n := n))

private theorem case_forall₂_drop (h : List.Forall₂ R xs ys) :
    List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction h generalizing n with
  | nil => simp
  | cons h ht ih => cases n with
    | zero => exact .cons h ht
    | succ n => exact ih (n := n)

theorem case_forall₂_get (h : List.Forall₂ R xs ys) (hi : i < xs.length) (hi' : i < ys.length) :
    R xs[i] ys[i] := by
  induction h generalizing i with
  | nil => cases hi
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih (by simpa using hi) (by simpa using hi')

theorem CaseApplicationRelated.capture {rule : AppliedRule} (H : CaseApplicationRelated R a b) :
    List.Forall₂ R (rule.capture a) (rule.capture b) := by
  unfold AppliedRule.capture
  rw [H.ctorArguments.length_eq]
  exact List.Forall₂.append' (case_forall₂_take H.arguments) (case_forall₂_drop H.ctorArguments)

theorem CaseStep.arguments_typed (H : CaseStep env U Γ rule levels arguments)
    (h : e ∈ arguments) : ∃ type, env.HasType U Γ e type := by
  rcases List.mem_iff_getElem.mp h with ⟨j, hj, rfl⟩
  cases H with
  | iota _ _ _ _ _ _ ha => exact ⟨_, ha.2 j hj (by simpa [← ha.1] using hj)⟩

theorem CaseRedex.weakN (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (H : CaseRedex env U Γ rule actual) :
    CaseRedex env U Γ' rule (CaseApplicationMap actual fun e => e.liftN n k) where
  source := by simpa only [case_capture_map, case_application_map_levels] using H.source.weakN henv W
  block_eq := H.block_eq
  owner_eq := H.owner_eq
  ctor_eq := H.ctor_eq
  arguments_length := by simpa [CaseApplicationMap] using H.arguments_length
  ctorArguments_length := by simpa [CaseApplicationMap] using H.ctorArguments_length
  levels_eq := H.levels_eq
  ctorLevels_eq := H.ctorLevels_eq
  guard := by
    have h := H.guard.weakN henv.ordered W
    simpa only [case_application_liftN, case_capture_map, case_application_map_levels, AppliedRule.lhs,
      instantiateParams_liftN H.source.closed.1.instL] using h

theorem CaseRedex.weak' (henv : env.WF) (W : Ctx.Lift' ρ Γ Γ')
    (H : CaseRedex env U Γ rule actual) :
    CaseRedex env U Γ' rule (CaseApplicationMap actual fun e => e.lift' ρ) where
  source := by simpa only [case_capture_map, case_application_map_levels] using H.source.weak' henv W
  block_eq := H.block_eq
  owner_eq := H.owner_eq
  ctor_eq := H.ctor_eq
  arguments_length := by simpa [CaseApplicationMap] using H.arguments_length
  ctorArguments_length := by simpa [CaseApplicationMap] using H.ctorArguments_length
  levels_eq := H.levels_eq
  ctorLevels_eq := H.ctorLevels_eq
  guard := by
    have h := H.guard.weak' henv.ordered W
    simpa only [case_application_lift', case_capture_map, case_application_map_levels, AppliedRule.lhs,
      instantiateParams_lift' H.source.closed.1.instL ρ] using h

theorem CaseRedex.instN (henv : env.WF) (hvalue : env.HasType U Γ₀ value valueType)
    (W : Ctx.InstN Γ₀ value valueType k Γ Γ') (H : CaseRedex env U Γ rule actual) :
    CaseRedex env U Γ' rule (CaseApplicationMap actual fun e => e.inst value k) where
  source := by simpa only [case_capture_map, case_application_map_levels] using H.source.instN henv hvalue W
  block_eq := H.block_eq
  owner_eq := H.owner_eq
  ctor_eq := H.ctor_eq
  arguments_length := by simpa [CaseApplicationMap] using H.arguments_length
  ctorArguments_length := by simpa [CaseApplicationMap] using H.ctorArguments_length
  levels_eq := H.levels_eq
  ctorLevels_eq := H.ctorLevels_eq
  guard := by
    have h := H.guard.instN henv.ordered W hvalue
    simpa only [case_application_instN, case_capture_map, case_application_map_levels, AppliedRule.lhs,
      instantiateParams_instN H.source.closed.1.instL] using h

theorem CaseRedex.capture_typed (H : CaseRedex env U Γ rule actual)
    (h : e ∈ rule.capture actual) : ∃ type, env.HasType U Γ e type :=
  H.source.arguments_typed h

private noncomputable def below_mkApps_head {motive : VExpr → Prop} {fn : VExpr} {args : List VExpr}
    (h : VExpr.below (motive := motive) (VExpr.mkApps fn args)) :
    VExpr.below (motive := motive) fn := by
  induction args generalizing fn with
  | nil => exact h
  | cons arg args ih => exact (ih h).1.2

private theorem below_mkApps_args {motive : VExpr → Prop} {fn : VExpr} {args : List VExpr}
    (h : VExpr.below (motive := motive) (VExpr.mkApps fn args)) :
    ∀ arg ∈ args, motive arg := by
  induction args generalizing fn with
  | nil => simp
  | cons arg args ih =>
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (below_mkApps_head (fn := .app fn value) h).2.1
    · exact ih h value hv

/-- Every captured equation argument is a proper subexpression of the case
redex, so complete development can recurse on the source expression. -/
theorem below_case_capture {motive : VExpr → Prop} {rule : AppliedRule} {actual : Application}
    (h : VExpr.below (motive := motive) actual.expr) :
    ∀ arg ∈ rule.capture actual, motive arg := by
  intro arg ha
  rcases List.mem_append.mp ha with ha | ha
  · exact below_mkApps_args h.1.2 arg (List.mem_of_mem_take ha)
  · exact below_mkApps_args h.2.2 arg (List.mem_of_mem_drop ha)

/-- Existential closure of a matched generated rule at its computed endpoints. -/
inductive CaseIota (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → VExpr → Prop where
  | iota : CaseRedex env U Γ rule actual →
    CaseIota env U Γ actual.expr (rule.rhs actual.levels (rule.capture actual))

theorem instantiateParams_eq_instOuter (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

/-- Applying a generated closed equation is justified by the existing typing
rule and beta conversion, with no extra environment rule or assumption. -/
theorem CaseStep.defeq
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments) :
    env.IsDefEqU U Γ (rule.lhs levels arguments) (rule.rhs levels arguments) := by
  cases H with
  | @iota block levels target arguments schema owner rule hlookup hgen hclosed
      hperm hleft hright hargs =>
    have hbody := hgen.body_exact
    obtain ⟨equations, hequations, hmem, _⟩ := hgen
    have heq := IsDefEq.elimIota hlookup hequations hmem hclosed hperm hleft hright
    obtain ⟨hl, hr, ht⟩ := hbody
    rw [← hl, ← hr, ← ht, VExpr.instL_wrapLams, VExpr.instL_wrapLams,
      VExpr.instL_wrapForalls] at heq
    have hty : ∀ j (hj : j < arguments.length)
        (hd : j < (rule.body.domains.map (VExpr.instL (target :: levels))).length),
        env.HasType U Γ arguments[j]
          ((rule.body.domains.map (VExpr.instL (target :: levels)))[j].instOuter
            (arguments.take j)) := by
      intro j hj hd
      rw [List.getElem_map]
      simpa only [instantiateParams_eq_instOuter] using hargs.2 j hj (by simpa using hd)
    have hlength : arguments.length =
        (rule.body.domains.map (VExpr.instL (target :: levels))).length := by
      simpa using hargs.1
    have happ := IsDefEq.mkApps_congr (args := arguments) (args' := arguments)
      heq hlength rfl fun j hj hd _ => hty j hj hd
    have hbetaL := IsDefEq.mkApps_wrapLams henv hΓ heq.hasType.1 hlength hty
    have hbetaR := IsDefEq.mkApps_wrapLams henv hΓ heq.hasType.2 hlength hty
    refine ⟨(rule.body.type.instL (target :: levels)).instOuter arguments, ?_⟩
    simpa only [AppliedRule.lhs, AppliedRule.rhs, instantiateParams_eq_instOuter] using
      hbetaL.symm.trans (happ.trans hbetaR)

/-- The literal specialization of every installed generated equation is a
concrete match. Certification makes its designated capture positions exact. -/
theorem CaseStep.canonicalMatch (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments) :
    CaseRedex env U Γ rule (rule.application.specialize levels arguments) := by
  have Hsaved := H
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp ht hr ha =>
    obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ := henv.eliminator_installed hl
    have hcapture := hcert.capture_specialize hg ha.1 (levels := target :: levels)
    have hlevels := hg.application_levels_inst (levels := target :: levels)
      (by simp only [List.length_cons, hg.equation_uvars, genericUvars, hp.length])
    have hactuallevels : (rule.application.specialize (target :: levels) arguments).levels = target :: levels := hlevels
    refine {
      source := ?_
      block_eq := rfl
      owner_eq := rfl
      ctor_eq := rfl
      arguments_length := by simp [Application.specialize]
      ctorArguments_length := by simp [Application.specialize]
      levels_eq := ?_
      ctorLevels_eq := ?_
      guard := ?_ }
    · simpa only [hcapture, hactuallevels] using Hsaved
    · simp only [Application.specialize, hlevels]
      exact List.Forall₂.rfl fun _ _ => rfl
    · simp only [Application.specialize, hlevels]
      exact List.Forall₂.rfl fun _ _ => rfl
    · rw [hcapture, hactuallevels, ← hg.lhs_exact]
      obtain ⟨type, he⟩ := Hsaved.defeq henv hΓ
      exact ⟨type, he.hasType.1⟩

/-- Open a generated equation under its actual binder telescope. The bound
variables form the complete typed argument list for its applied reduction. -/
theorem generated_case_body (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hlookup : env.eliminators block schema)
    (hgen : schema.Generates block owner rule) (hclosed : RuleClosed rule.equation)
    (hpermission : schema.Permission U owner levels target)
    (hleft : env.HasType U Γ (rule.equation.lhs.instL (target :: levels))
      (rule.equation.type.instL (target :: levels)))
    (hright : env.HasType U Γ (rule.equation.rhs.instL (target :: levels))
      (rule.equation.type.instL (target :: levels))) :
    let domains := rule.body.domains.map (VExpr.instL (target :: levels))
    OnCtx (domains.reverse ++ Γ) (env.IsType U) ∧
      CaseIota env U (domains.reverse ++ Γ)
        (rule.body.lhs.instL (target :: levels)) (rule.body.rhs.instL (target :: levels)) := by
  dsimp only
  let domains := rule.body.domains.map (VExpr.instL (target :: levels))
  let args := VExpr.bvarRange domains.length domains.length
  have hleftBody := hleft
  obtain ⟨hl, hr, ht⟩ := hgen.body_exact
  rw [← hl, ← ht, VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hleftBody
  obtain ⟨hctx, _⟩ := HasType.wrapLams_inv henv hΓ hleftBody
  have W : Ctx.LiftN domains.length 0 Γ (domains.reverse ++ Γ) := .zero _ (by simp)
  have hleft' := hleft.weakN henv.ordered W
  have hright' := hright.weakN henv.ordered W
  simp only [hclosed.1.instL.liftN_eq (Nat.zero_le _),
    hclosed.2.1.instL.liftN_eq (Nat.zero_le _),
    hclosed.2.2.instL.liftN_eq (Nat.zero_le _)] at hleft' hright'
  have hdomain : ∀ i (hi : i < rule.body.domains.length), rule.body.domains[i].ClosedN i := by
    intro i hi
    have hc := hclosed.2.2
    rw [← ht] at hc
    simpa only [Nat.zero_add] using closed_wrapForalls_domain hc hi
  have H : CaseStep env U (domains.reverse ++ Γ) rule (target :: levels) args := by
    refine .iota hlookup hgen hclosed hpermission hleft' hright' ⟨by simp [args, domains], ?_⟩
    intro i hi hd
    have hi' : i < domains.length := by simpa [args] using hi
    have hty : env.HasType U (domains.reverse ++ Γ) (.bvar (domains.length - 1 - i))
        (domains[i].liftN (domains.length - i)) := .bvar (Lookup.reverse_append domains Γ i hi')
    rw [instantiateParams_eq_instOuter]
    simp only [args, VExpr.bvarRange_take _ _ _ (Nat.le_of_lt hi')]
    rw [VExpr.bvarRange_getElem domains.length domains.length i hi']
    rw [VExpr.instOuter_range_bvar' _ _ _ (hdomain i hd).instL (Nat.le_of_lt hi')]
    simpa only [domains, List.getElem_map] using hty
  have hmatch := H.canonicalMatch henv hctx
  have hstep := CaseIota.iota hmatch
  have hcapture := henv.eliminator_installed hlookup
  obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ := hcapture
  rw [hcert.capture_specialize hgen H.length] at hstep
  have hlevels := hgen.application_levels_inst (levels := target :: levels)
    (by simp only [List.length_cons, hgen.equation_uvars, genericUvars, hpermission.length])
  change CaseIota env U _ (rule.application.specialize (target :: levels) args).expr
    (rule.rhs ((rule.application.specialize (target :: levels) args).levels) args) at hstep
  have hactuallevels : (rule.application.specialize (target :: levels) args).levels = target :: levels := hlevels
  rw [hactuallevels, ← hgen.lhs_exact] at hstep
  have hcL : (rule.body.lhs.instL (target :: levels)).ClosedN domains.length := by
    simpa [args] using H.closed.1.instL (ls := target :: levels)
  have hcR : (rule.body.rhs.instL (target :: levels)).ClosedN domains.length := by
    simpa [args] using H.closed.2.1.instL (ls := target :: levels)
  simp only [AppliedRule.lhs, AppliedRule.rhs, instantiateParams_eq_instOuter, args,
    VExpr.instOuter_range_bvar' _ _ _ hcL (Nat.le_refl _),
    VExpr.instOuter_range_bvar' _ _ _ hcR (Nat.le_refl _), Nat.sub_self, VExpr.liftN_zero] at hstep
  exact ⟨hctx, hstep⟩

theorem CaseStep.rhs_congr (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments)
    (hlength : arguments'.length = arguments.length)
    (heq : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      env.IsDefEqU U Γ arguments[i] arguments'[i]) :
    env.IsDefEqU U Γ (rule.rhs levels arguments) (rule.rhs levels arguments') := by
  cases H with
  | @iota block levels target arguments schema owner rule _ hgen _ _ _ hr ha =>
    obtain ⟨_, hrule, htype⟩ := hgen.body_exact
    rw [← hrule, ← htype, VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hr
    have hty : ∀ i (hi : i < arguments.length)
        (hd : i < (rule.body.domains.map (VExpr.instL (target :: levels))).length),
        env.HasType U Γ arguments[i]
          ((rule.body.domains.map (VExpr.instL (target :: levels)))[i].instOuter (arguments.take i)) := by
      intro i hi hd
      rw [List.getElem_map]
      simpa only [instantiateParams_eq_instOuter] using ha.2 i hi (by simpa using hd)
    have hlen : arguments.length = (rule.body.domains.map (VExpr.instL (target :: levels))).length := by
      simpa using ha.1
    have happ := IsDefEq.mkApps_congr hr hlen hlength.symm fun i hi hd hi' =>
      (heq i hi hi').of_l henv hΓ (hty i hi hd)
    have hnew := HasType.mkApps_wrapForalls henv hΓ hr ⟨_, happ.hasType.2⟩
      (hlength.trans hlen)
    have hl := IsDefEq.mkApps_wrapLams henv hΓ hr hlen hty
    have hr := IsDefEq.mkApps_wrapLams henv hΓ hr (hlength.trans hlen) hnew.1
    have result := (IsDefEqU.trans henv hΓ ⟨_, hl.symm⟩ ⟨_, happ⟩).trans henv hΓ ⟨_, hr⟩
    simpa only [AppliedRule.rhs, instantiateParams_eq_instOuter] using result

theorem CaseStep.lhs_congr (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments)
    (hlength : arguments'.length = arguments.length)
    (heq : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      env.IsDefEqU U Γ arguments[i] arguments'[i]) :
    env.IsDefEqU U Γ (rule.lhs levels arguments) (rule.lhs levels arguments') := by
  cases H with
  | @iota block levels target arguments schema owner rule _ hgen _ _ hr _ ha =>
    obtain ⟨hrule, _, htype⟩ := hgen.body_exact
    rw [← hrule, ← htype, VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hr
    have hty : ∀ i (hi : i < arguments.length)
        (hd : i < (rule.body.domains.map (VExpr.instL (target :: levels))).length),
        env.HasType U Γ arguments[i]
          ((rule.body.domains.map (VExpr.instL (target :: levels)))[i].instOuter (arguments.take i)) := by
      intro i hi hd
      rw [List.getElem_map]
      simpa only [instantiateParams_eq_instOuter] using ha.2 i hi (by simpa using hd)
    have hlen : arguments.length = (rule.body.domains.map (VExpr.instL (target :: levels))).length := by
      simpa using ha.1
    have happ := IsDefEq.mkApps_congr hr hlen hlength.symm fun i hi hd hi' =>
      (heq i hi hi').of_l henv hΓ (hty i hi hd)
    have hnew := HasType.mkApps_wrapForalls henv hΓ hr ⟨_, happ.hasType.2⟩
      (hlength.trans hlen)
    have hl := IsDefEq.mkApps_wrapLams henv hΓ hr hlen hty
    have hr := IsDefEq.mkApps_wrapLams henv hΓ hr (hlength.trans hlen) hnew.1
    have result := (IsDefEqU.trans henv hΓ ⟨_, hl.symm⟩ ⟨_, happ⟩).trans henv hΓ ⟨_, hr⟩
    simpa only [AppliedRule.lhs, instantiateParams_eq_instOuter] using result

theorem CaseStep.congr (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments)
    (hlength : arguments'.length = arguments.length)
    (heq : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      env.IsDefEqU U Γ arguments[i] arguments'[i]) :
    CaseStep env U Γ rule levels arguments' := by
  cases H with
  | @iota block levels target arguments schema owner rule hlookup hgen hclosed hpermission hleft hr ha =>
    obtain ⟨_, hrule, htype⟩ := hgen.body_exact
    rw [← hrule, ← htype, VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hr
    have hty : ∀ i (hi : i < arguments.length)
        (hd : i < (rule.body.domains.map (VExpr.instL (target :: levels))).length),
        env.HasType U Γ arguments[i]
          ((rule.body.domains.map (VExpr.instL (target :: levels)))[i].instOuter (arguments.take i)) := by
      intro i hi hd
      rw [List.getElem_map]
      simpa only [instantiateParams_eq_instOuter] using ha.2 i hi (by simpa using hd)
    have hlen : arguments.length = (rule.body.domains.map (VExpr.instL (target :: levels))).length := by
      simpa using ha.1
    have happ := IsDefEq.mkApps_congr hr hlen hlength.symm fun i hi hd hi' =>
      (heq i hi hi').of_l henv hΓ (hty i hi hd)
    have hnew := HasType.mkApps_wrapForalls henv hΓ hr ⟨_, happ.hasType.2⟩
      (hlength.trans hlen)
    refine .iota hlookup hgen hclosed hpermission hleft ?_ ⟨hlength.trans ha.1, ?_⟩
    · simpa only [← hrule, ← htype, VExpr.instL_wrapLams, VExpr.instL_wrapForalls] using hr
    · intro i hi hd
      have hty := hnew.1 i hi (by simpa only [List.length_map] using hd)
      rw [List.getElem_map] at hty
      simpa only [instantiateParams_eq_instOuter] using hty

/-- Registered case families have one major-premise position across all
constructors. In particular a proper prefix cannot be another case redex. -/
theorem CaseStep.rhs_variables (H : CaseStep env U Γ rule levels arguments) :
    VariableApplications rule.body.rhs := by
  cases H with
  | iota _ hg =>
    obtain ⟨minor, nf, hshape⟩ := hg.rhs_shape
    rw [hshape]
    apply VariableApplications.mkApps .bvar
    intro arg harg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp harg
    exact .bvar

theorem CaseStep.arity_eq (henv : env.WF)
    (H : CaseStep env U Γ rule levels arguments)
    (H' : CaseStep env U' Γ' rule' levels' arguments')
    (hblock : rule.application.block = rule'.application.block)
    (howner : rule.application.owner = rule'.application.owner) :
    rule.application.arguments.length = rule'.application.arguments.length := by
  cases H with
  | @iota block levels target arguments schema owner rule hl hg =>
    cases H' with
    | @iota block' levels' target' arguments' schema' owner' rule' hl' hg' =>
      obtain ⟨hb, ho⟩ := hg.owned
      obtain ⟨hb', ho'⟩ := hg'.owned
      have hkey : block = block' := hb.symm.trans (hblock.trans hb')
      rw [← hkey] at hl' hg'
      cases henv.eliminators_unique hl hl'
      have hslot : owner = owner' := Fin.ext (ho.symm.trans (howner.trans ho'))
      cases hslot
      obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ := henv.eliminator_installed hl
      exact hcert.arguments_length_eq hg hg'

theorem CaseRedex.not_elim_prefix (henv : env.WF)
    (H : CaseStep env U Γ rule levels arguments)
    (H' : CaseRedex env U' Γ' rule' actual)
    (he : actual.expr = VExpr.mkApps (.elim rule.application.block rule.application.owner packed) prefixArgs)
    (hlen : prefixArgs.length ≤ rule.application.arguments.length) : False := by
  have hs := congrArg VExpr.getAppFnArgs he
  rw [case_application_spine, spine_mkApps_exact _ _ rfl] at hs
  have hh := congrArg Prod.fst hs
  obtain ⟨hb, ho, _⟩ := VExpr.elim.inj hh
  have harity := H.arity_eq henv H'.source (hb.symm.trans H'.block_eq)
    (ho.symm.trans H'.owner_eq)
  have hlength := congrArg (fun p : VExpr × List VExpr => p.2.length) hs
  simp only [List.length_append, List.length_singleton] at hlength
  have ha := H'.arguments_length
  omega

theorem CaseStep.rule_unique (henv : env.WF)
    (H : CaseStep env U Γ rule levels arguments)
    (H' : CaseStep env U' Γ' rule' levels' arguments')
    (hblock : rule.application.block = rule'.application.block)
    (howner : rule.application.owner = rule'.application.owner)
    (hctor : rule.application.ctorName = rule'.application.ctorName) : rule = rule' := by
  cases H with
  | @iota block levels target arguments schema owner rule hl hg =>
    cases H' with
    | @iota block' levels' target' arguments' schema' owner' rule' hl' hg' =>
      obtain ⟨hb, ho⟩ := hg.owned
      obtain ⟨hb', ho'⟩ := hg'.owned
      have hkey : block = block' := hb.symm.trans (hblock.trans hb')
      rw [← hkey] at hl' hg'
      cases henv.eliminators_unique hl hl'
      have hslot : owner = owner' := Fin.ext (ho.symm.trans (howner.trans ho'))
      cases hslot
      exact henv.case_rule_unique hl hg hg' hctor

theorem CaseRedex.rule_unique (henv : env.WF)
    (H : CaseRedex env U Γ rule actual) (H' : CaseRedex env U Γ rule' actual) :
    rule = rule' :=
  H.source.rule_unique henv H'.source (H.block_eq.symm.trans H'.block_eq)
    (H.owner_eq.symm.trans H'.owner_eq) (H.ctor_eq.symm.trans H'.ctor_eq)

theorem CaseRedex.congr (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseRedex env U Γ rule actual)
    (hspine : CaseApplicationRelated (env.IsDefEqU U Γ) actual actual')
    (he : env.IsDefEqU U Γ actual.expr actual'.expr) :
    CaseRedex env U Γ rule actual' := by
  have hcapture := hspine.capture (rule := rule)
  have hlen := hcapture.length_eq.symm
  have hargs := fun (i : Nat) hi hi' => case_forall₂_get (i := i) hcapture hi hi'
  refine {
    source := ?_
    block_eq := hspine.block_eq.symm.trans H.block_eq
    owner_eq := hspine.owner_eq.symm.trans H.owner_eq
    ctor_eq := hspine.ctor_eq.symm.trans H.ctor_eq
    arguments_length := hspine.arguments.length_eq.symm.trans H.arguments_length
    ctorArguments_length := hspine.ctorArguments.length_eq.symm.trans H.ctorArguments_length
    levels_eq := ?_
    ctorLevels_eq := ?_
    guard := ?_ }
  · rw [← hspine.levels_eq]
    exact H.source.congr henv hΓ hlen hargs
  · simpa only [← hspine.levels_eq] using H.levels_eq
  · simpa only [← hspine.levels_eq, ← hspine.ctorLevels_eq] using H.ctorLevels_eq
  · rw [← hspine.levels_eq]
    exact (he.symm.trans henv hΓ H.guard).trans henv hΓ (H.source.lhs_congr henv hΓ hlen hargs)

theorem CaseStep.defeqDFC (henv : env.WF)
    (W : IsDefEqCtx env U Γ₀ Γ Γ') (H : CaseStep env U Γ rule levels arguments) :
    CaseStep env U Γ' rule levels arguments := by
  cases H with
  | iota hl hg hc hp ht hr ha =>
    exact .iota hl hg hc hp (ht.defeqDFC henv W) (hr.defeqDFC henv W)
      ⟨ha.1, fun i hi hd => (ha.2 i hi hd).defeqDFC henv W⟩

theorem CaseRedex.defeqDFC (henv : env.WF)
    (W : IsDefEqCtx env U Γ₀ Γ Γ') (H : CaseRedex env U Γ rule actual) :
    CaseRedex env U Γ' rule actual :=
  { H with source := H.source.defeqDFC henv W, guard := H.guard.defeqDFC henv W }

theorem CaseIota.defeq
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseIota env U Γ lhs rhs) : env.IsDefEqU U Γ lhs rhs := by
  cases H with | iota h => exact h.guard.trans henv hΓ (h.source.defeq henv hΓ)

theorem CaseIota.defeqDFC (henv : env.WF)
    (W : IsDefEqCtx env U Γ₀ Γ Γ') (H : CaseIota env U Γ lhs rhs) :
    CaseIota env U Γ' lhs rhs := by
  cases H with | iota hm => exact .iota (hm.defeqDFC henv W)

theorem CaseIota.weak' (henv : env.WF) (W : Ctx.Lift' ρ Γ Γ')
    (H : CaseIota env U Γ lhs rhs) :
    CaseIota env U Γ' (lhs.lift' ρ) (rhs.lift' ρ) := by
  cases H with
  | iota hm =>
    have h := CaseIota.iota (hm.weak' henv W)
    simpa only [case_application_lift', case_capture_map, case_application_map_levels,
      AppliedRule.rhs, instantiateParams_lift' hm.source.closed.2.1.instL ρ] using h

theorem CaseIota.instN (henv : env.WF)
    (hvalue : env.HasType U Γ₀ value valueType) (W : Ctx.InstN Γ₀ value valueType k Γ Γ')
    (H : CaseIota env U Γ lhs rhs) :
    CaseIota env U Γ' (lhs.inst value k) (rhs.inst value k) := by
  cases H with
  | iota hm =>
    have h := CaseIota.iota (hm.instN henv hvalue W)
    simpa only [case_application_instN, case_capture_map, case_application_map_levels,
      AppliedRule.rhs, instantiateParams_instN hm.source.closed.2.1.instL] using h

theorem IsCaseMajorPremise.head (H : IsCaseMajorPremise env e) :
    ∃ block owner levels, e.getAppFnArgs.1 = .elim block owner levels := by
  obtain ⟨schema, block, owner, levels, args, _, rfl, _⟩ := H
  exact ⟨block, owner.val, levels, congrArg Prod.fst (spine_mkApps_exact _ _ rfl)⟩

theorem IsCaseMajorPremise.not_lam (H : IsCaseMajorPremise env (.lam A body)) : False := by
  obtain ⟨schema, block, owner, levels, args, _, he, _⟩ := H
  exact VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm

theorem IsCaseMajorPremise.lift' : IsCaseMajorPremise env (e.lift' ρ) ↔ IsCaseMajorPremise env e := by
  constructor
  · rintro ⟨schema, block, owner, levels, args, hl, he, hlen⟩
    obtain ⟨args', he', hargs⟩ := case_elim_spine_lift'_inv he.symm
    exact ⟨schema, block, owner, levels, args', hl, he', by simpa [hargs] using hlen⟩
  · rintro ⟨schema, block, owner, levels, args, hl, rfl, hlen⟩
    exact ⟨schema, block, owner, levels, args.map (fun e => e.lift' ρ), hl,
      VExpr.lift'_mkApps _ _ _, by simpa using hlen⟩

theorem IsCaseMajorPremise.instN (H : IsCaseMajorPremise env e) :
    IsCaseMajorPremise env (e.inst value k) := by
  obtain ⟨schema, block, owner, levels, args, hl, rfl, hlen⟩ := H
  exact ⟨schema, block, owner, levels, args.map (fun e => e.inst value k), hl,
    by simp [VExpr.inst], by simpa using hlen⟩

theorem IsCasePrefix.head (H : IsCasePrefix env e) :
    ∃ block owner levels, e.getAppFnArgs.1 = .elim block owner levels := by
  obtain ⟨schema, block, owner, levels, args, _, rfl, _⟩ := H
  exact ⟨block, owner.val, levels, congrArg Prod.fst (spine_mkApps_exact _ _ rfl)⟩

theorem IsCasePrefix.not_lam (H : IsCasePrefix env (.lam A body)) : False := by
  obtain ⟨schema, block, owner, levels, args, _, he, _⟩ := H
  exact VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm

theorem case_spine_app (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs = (fn.getAppFnArgs.1, fn.getAppFnArgs.2 ++ [arg]) := by
  have go : ∀ e args, VExpr.getAppFnArgs.go e args =
      (e.getAppFnArgs.1, e.getAppFnArgs.2 ++ args) := by
    intro e
    induction e with
    | app fn a ih _ =>
      intro args
      change VExpr.getAppFnArgs.go fn (a :: args) = _
      rw [ih]
      change _ = ((VExpr.getAppFnArgs.go fn [a]).1, (VExpr.getAppFnArgs.go fn [a]).2 ++ args)
      rw [ih]
      simp
    | _ => intros; rfl
  exact go fn [arg]

theorem IsCasePrefix.app_left (H : IsCasePrefix env (.app fn arg)) : IsCasePrefix env fn := by
  obtain ⟨schema, block, owner, levels, args, hl, he, hn⟩ := H
  have hs := congrArg VExpr.getAppFnArgs he
  rw [case_spine_app, spine_mkApps_exact _ _ rfl] at hs
  have hh := congrArg Prod.fst hs
  change fn.getAppFnArgs.1 = VExpr.elim block owner.val levels at hh
  have ha := congrArg (fun p : VExpr × List VExpr => p.2.length) hs
  refine ⟨schema, block, owner, levels, fn.getAppFnArgs.2, hl, ?_, ?_⟩
  · simpa only [hh] using (VExpr.mkApps_getAppFnArgs fn).symm
  · simp only [List.length_append, List.length_singleton] at ha
    omega

theorem IsCaseMajorPremise.not_strict_prefix (henv : env.WF)
    (H : IsCaseMajorPremise env fn) (H' : IsCasePrefix env (.app fn arg)) : False := by
  obtain ⟨schema, block, owner, levels, args, hl, he, hn⟩ := H
  obtain ⟨schema', block', owner', levels', args', hl', he', hn'⟩ := H'
  have hs := congrArg VExpr.getAppFnArgs he'
  rw [case_spine_app, he, spine_mkApps_exact _ _ rfl, spine_mkApps_exact _ _ rfl] at hs
  obtain ⟨hb, ho, _⟩ := VExpr.elim.inj (congrArg Prod.fst hs)
  cases hb
  cases henv.eliminators_unique hl hl'
  cases Fin.ext ho
  have ha := congrArg (fun p : VExpr × List VExpr => p.2.length) hs
  simp only [List.length_append, List.length_singleton] at ha
  omega

theorem IsCasePrefix.not_reduction (henv : env.WF) (hm : IsCasePrefix env e)
    (H : CaseIota env U Γ e out) : False := by
  rcases hm with ⟨schema, block, owner, levels, args, hlookup, he, hlen⟩
  cases H with
  | iota hmatch =>
    have hs := congrArg VExpr.getAppFnArgs he
    rw [case_application_spine, spine_mkApps_exact _ _ rfl] at hs
    have hh := congrArg Prod.fst hs
    obtain ⟨hb, ho, _⟩ := VExpr.elim.inj hh
    have harity := hmatch.arguments_length
    obtain ⟨schema', block', owner', hl, hg⟩ := hmatch.source.generates
    obtain ⟨hgb, hgo⟩ := hg.owned
    have hk : block' = block := hgb.symm.trans (hmatch.block_eq.symm.trans hb)
    rw [hk] at hl hg
    cases henv.eliminators_unique hlookup hl
    have hslot : owner' = owner := Fin.ext (hgo.symm.trans (hmatch.owner_eq.symm.trans ho))
    cases hslot
    obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ := henv.eliminator_installed hlookup
    have hn := hcert.arguments_length hg
    have hargs := congrArg (fun p : VExpr × List VExpr => p.2.length) hs
    simp only [List.length_append, List.length_singleton] at hargs
    unfold caseMajorArity at hlen
    omega

theorem CaseRedex.majorPremise (henv : env.WF)
    (H : CaseRedex env U Γ rule actual) :
    IsCaseMajorPremise env (VExpr.mkApps (.elim actual.block actual.owner actual.levels) actual.arguments) := by
  obtain ⟨schema, block, owner, hl, hg⟩ := H.source.generates
  obtain ⟨hb, ho⟩ := hg.owned
  obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ := henv.eliminator_installed hl
  refine ⟨schema, block, owner, actual.levels, actual.arguments, hl, ?_, ?_⟩
  · rw [H.block_eq, H.owner_eq, hb, ho]
  · exact H.arguments_length.trans (hcert.arguments_length hg)

theorem CaseIota.determ (henv : env.WF)
    (H : CaseIota env U Γ lhs rhs) (H' : CaseIota env U Γ lhs rhs') :
    rhs = rhs' := by
  cases H with
  | @iota rule actual hm =>
    generalize he : actual.expr = source at H'
    cases H' with
    | iota hm' =>
      cases case_application_injective he
      cases hm.rule_unique henv hm'
      rfl

theorem CaseIota.head (H : CaseIota env U Γ lhs rhs) :
    ∃ block owner levels, lhs.getAppFnArgs.1 = .elim block owner levels := by
  cases H with | iota h => exact ⟨_, _, _, Application.head _⟩

theorem CaseIota.not_stored_match
    (H : CaseIota env U Γ lhs rhs) {pattern : SimplePattern}
    {values : pattern.toPattern.Path → VExpr}
    (hm : pattern.toPattern.Matches lhs levels values) : False := by
  obtain ⟨_, _, _, hhead⟩ := H.head
  obtain ⟨_, hnative⟩ := CaseSchema.recursor_pattern_head hm
  rw [hhead] at hnative
  cases hnative

open VExpr in
theorem CaseStep.congr_levels (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments)
    (hwf : ∀ level ∈ levels', level.WF U)
    (heq : List.Forall₂ (· ≈ ·) levels levels') :
    CaseStep env U Γ rule levels' arguments := by
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    cases heq with
    | cons htarget hlevels =>
      rename_i target' levels'
      have hp' := hp.congr hwf (.cons htarget hlevels)
      have heq := List.Forall₂.cons htarget hlevels
      have htypeEq := (hright.isType henv.ordered hΓ)
      obtain ⟨typeLevel, htype⟩ := htypeEq
      have htypeEq := htype.eqUpToLevels henv.ordered hΓ
        (EqUpToLevels.instL_expr _ hp.packedWF hwf heq)
      have hleftEq := hleft.eqUpToLevels henv.ordered hΓ
        (EqUpToLevels.instL_expr _ hp.packedWF hwf heq)
      have hrightEq := hright.eqUpToLevels henv.ordered hΓ
        (EqUpToLevels.instL_expr _ hp.packedWF hwf heq)
      have hleft' := htypeEq.defeq hleftEq.hasType.2
      have hright' := htypeEq.defeq hrightEq.hasType.2
      refine .iota hl hg hc hp' hleft' hright' ?_
      have htypeShape := hg.body_exact.2.2
      rw [← htypeShape, instL_wrapForalls] at hrightEq hright'
      have hlen : arguments.length =
          (rule.body.domains.map (instL (target :: levels))).length := by simpa using ha.1
      have happ := IsDefEq.mkApps_congr (args := arguments) (args' := arguments) hrightEq hlen rfl
        (fun i hi hd _ => by
          rw [List.getElem_map]
          simpa only [instantiateParams_eq_instOuter, HasType] using ha.2 i hi (by simpa using hd))
      have hnew := HasType.mkApps_wrapForalls henv hΓ hright' ⟨_, happ.hasType.2⟩
        (by simpa using ha.1)
      refine ⟨ha.1, ?_⟩
      intro i hi hd
      have h := hnew.1 i hi (by simpa using hd)
      rw [List.getElem_map] at h
      simpa only [instantiateParams_eq_instOuter] using h

private theorem levels_inst_forall₂ (levels : List VLevel)
    (H : List.Forall₂ (· ≈ ·) substitution substitution') :
    List.Forall₂ (· ≈ ·) (levels.map (·.inst substitution))
      (levels.map (·.inst substitution')) := by
  exact List.forall₂_map_left_iff.mpr <| List.forall₂_map_right_iff.mpr <|
    List.Forall₂.rfl fun _ _ => VLevel.inst_congr rfl H

theorem CaseRedex.congr_levels (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseRedex env U Γ rule actual)
    (hwf : ∀ level ∈ levels', level.WF U)
    (heq : List.Forall₂ (· ≈ ·) actual.levels levels')
    (hctorEq : List.Forall₂ (· ≈ ·) actual.ctorLevels ctorLevels')
    (he : env.IsDefEqU U Γ actual.expr
      ({ actual with levels := levels', ctorLevels := ctorLevels' } : Application).expr) :
    CaseRedex env U Γ rule
      { actual with levels := levels', ctorLevels := ctorLevels' } := by
  have hs := H.source.congr_levels henv hΓ hwf heq
  have hbody : rule.rhs actual.levels (rule.capture actual) =
      rule.rhs levels' (rule.capture actual) := by
    simp only [AppliedRule.rhs, H.source.rhs_variables.instL_eq]
  refine {
    source := hs
    block_eq := H.block_eq
    owner_eq := H.owner_eq
    ctor_eq := H.ctor_eq
    arguments_length := H.arguments_length
    ctorArguments_length := H.ctorArguments_length
    levels_eq := ?_
    ctorLevels_eq := ?_
    guard := ?_ }
  · exact List.Forall₂.trans (fun _ _ _ h h' => h.trans h')
      (List.Forall₂.trans (fun _ _ _ h h' => h.trans h')
        (Lean4Lean.List.forall₂_symm (fun _ _ h => h.symm) heq) H.levels_eq)
      (levels_inst_forall₂ _ heq)
  · exact List.Forall₂.trans (fun _ _ _ h h' => h.trans h')
      (List.Forall₂.trans (fun _ _ _ h h' => h.trans h')
        (Lean4Lean.List.forall₂_symm (fun _ _ h => h.symm) hctorEq) H.ctorLevels_eq)
      (levels_inst_forall₂ _ heq)
  · have hleft := H.source.defeq henv hΓ
    have hright := hs.defeq henv hΓ
    rw [hbody] at hleft
    exact ((he.symm.trans henv hΓ H.guard).trans henv hΓ hleft).trans henv hΓ hright.symm


end VEnv
end Lean4Lean
