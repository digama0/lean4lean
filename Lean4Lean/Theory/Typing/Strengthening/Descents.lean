import Lean4Lean.Theory.Typing.Strengthening.Closures

/-! # Typing strengthening: the guard descents

Direction F. The reduction of `Cancel` to
`TypedFront` (`EtaClosure.lean`, `cancel_iff_typedFront_B3`) assumes that the guards of the
replayed steps descend from lifted data to the source typed below. This file discharges the
case-iota guard:

* `caseRedexDescends : CaseRedexDescends` from `TypedFrontN` and `GenericRulesTyped₀`: the closed
  rule typings of `CaseStep.iota` come from the generic equations (`caseStep_premises`); the
  captures are arguments of the typed application below (`case_capture_wf`), typed at their
  specialized domains by strong induction on the position (each domain is a type below by
  telescope instantiation, `IsType.instOuter_telescope`, from the specialized domain telescope
  `caseRule_domains_ctx`) and retyped from above (`TypedFrontN.retype`); the alignment guard
  compares two terms typed below (`TypedFrontN.independent`). -/

namespace Lean4Lean.VEnv.StrengtheningDescents
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningClosures
  InductiveSignature InductiveSignature.CaseSchema

variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr}

/-- Every captured argument of a typed case application is well formed: the captures are
arguments of the two spines of the application. -/
theorem case_capture_wf (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    {rule : AppliedRule} {actual : Application} {T : VExpr}
    (he : env.HasType U Γ actual.expr T) : ∀ e ∈ rule.capture actual, VExpr.WF env U Γ e := by
  intro e hmem
  obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
  rcases List.mem_append.mp hmem with h | h
  · exact VExpr.WF.args_of_mkApps henv hΓ ⟨_, hf⟩ _ (List.mem_of_mem_take h)
  · exact VExpr.WF.args_of_mkApps henv hΓ ⟨_, ha⟩ _ (List.mem_of_mem_drop h)

/-- The specialized domain telescope of a generated rule is well formed in `Γ`, from the closed
typing of its left-hand side (`body_exact`). -/
theorem caseRule_domains_ctx (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {block : Name} {owner : Fin schema.signature.families.size}
    {rule : AppliedRule} {lv : List VLevel} (hgen : schema.Generates block owner rule)
    (hleft : env.HasType U Γ (rule.equation.lhs.instL lv) (rule.equation.type.instL lv)) :
    OnCtx ((rule.body.domains.map (·.instL lv)).reverse ++ Γ) (env.IsType U) := by
  have ht := hgen.body_exact.2.2
  obtain ⟨u, hT⟩ := hleft.isType henv.ordered hΓ
  rw [← ht, VExpr.instL_wrapForalls] at hT
  exact (IsType.wrapForalls_inv henv hΓ ⟨_, hT⟩).1

section
open VEnv.Params
variable [VEnv.Params]

/-- The case-iota guard descends from `TypedFrontN` and the closed generic rule typings. -/
theorem caseRedexDescends (hTF : TypedFrontN Params.env) (hRules : GenericRulesTyped₀ Params.env) :
    CaseRedexDescends := by
  intro k Γ Γ' rule actual T W hΓ hΓ' he hm
  have hsrc := hm.source
  simp only [case_capture_map, case_application_map_levels] at hsrc
  have hdomcl : ∀ i (hi : i < rule.body.domains.length), rule.body.domains[i].ClosedN i :=
    fun i hi => hsrc.domains_closed hi
  generalize hcaps : rule.capture actual = caps at hsrc
  generalize hlv : actual.levels = lv at hsrc
  cases hsrc with
  | @iota _ levels target _ schema owner _ hl hgen hclosed hperm _ _ hargs =>
  obtain ⟨hleft₀, hright₀⟩ := hRules.caseStep_premises henv hl hgen hperm Γ
  have hctx := caseRule_domains_ctx henv hΓ hgen hleft₀
  have hcapwf := case_capture_wf (rule := rule) henv.ordered hΓ he
  have hlen : caps.length = rule.body.domains.length := by simpa using hargs.1
  have hdom : ∀ j (hj : j < caps.length) (hd : j < rule.body.domains.length),
      Params.env.HasType univs Γ caps[j]
        (instantiateParams (rule.body.domains[j].instL (target :: levels)) (caps.take j)) := by
    intro j
    induction j using Nat.strongRecOn with
    | _ j ih =>
    intro hj hd
    have hD : Params.env.IsType univs Γ
        (instantiateParams (rule.body.domains[j].instL (target :: levels)) (caps.take j)) := by
      rw [instantiateParams_eq_instOuter]
      have hj' : j < (rule.body.domains.map (·.instL (target :: levels))).length := by simpa using hd
      have hA := (OnCtx.getElem_reverse_append hctx j hj').2
      rw [List.getElem_map] at hA
      refine IsType.instOuter_telescope henv
        (doms := (rule.body.domains.map (·.instL (target :: levels))).take j) hA
        (by simp [List.length_take]; omega) ?_
      intro i hi hi'
      simp only [List.length_take] at hi hi'
      have hi₁ : i < j := by omega
      rw [List.getElem_take, List.getElem_take, List.getElem_map, List.take_take,
        Nat.min_eq_left (Nat.le_of_lt hi₁), ← instantiateParams_eq_instOuter]
      exact ih i hi₁ (by omega) (by omega)
    have hab := hargs.2 j (by simpa using hj) hd
    have htake : (caps.map (·.liftN 1 k)).take j = (caps.take j).map (·.liftN 1 k) :=
      (List.map_take ..).symm
    rw [List.getElem_map, htake, ← instantiateParams_liftN (by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      exact (hdomcl j hd).instL)] at hab
    obtain ⟨A, hA⟩ := hcapwf _ (by rw [hcaps]; exact List.getElem_mem hj)
    obtain ⟨u, hDu⟩ := hD
    exact hTF.retype henv W hΓ hΓ' hA hDu hab
  have hsrc₀ : CaseStep Params.env univs Γ rule actual.levels (rule.capture actual) := by
    rw [hlv, hcaps]
    exact .iota hl hgen hclosed hperm hleft₀ hright₀ ⟨hlen, hdom⟩
  refine { source := hsrc₀, block_eq := hm.block_eq, owner_eq := hm.owner_eq, ctor_eq := hm.ctor_eq
           arguments_length := by simpa [CaseApplicationMap] using hm.arguments_length
           ctorArguments_length := by simpa [CaseApplicationMap] using hm.ctorArguments_length
           levels_eq := hm.levels_eq, ctorLevels_eq := hm.ctorLevels_eq, guard := ?_ }
  have hg := hm.guard
  simp only [case_application_liftN, case_capture_map, case_application_map_levels,
    AppliedRule.lhs, ← instantiateParams_liftN hsrc₀.closed.1.instL] at hg
  obtain ⟨_, hlhs⟩ := hsrc₀.defeq henv hΓ
  exact hTF.independent henv W hΓ hΓ' he hlhs.hasType.1 hg

end

end Lean4Lean.VEnv.StrengtheningDescents
