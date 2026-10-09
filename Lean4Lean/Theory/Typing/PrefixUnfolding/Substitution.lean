import Lean4Lean.Theory.Typing.PrefixUnfolding.Supply
import Lean4Lean.Theory.Typing.SingletonExtraction.Recursor
import Lean4Lean.Theory.Typing.PrefixUnfolding.Rule
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Batteries.Tactic.OpenPrivate

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr VEnv

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv CaseSchema
variable {levels : List VLevel} {type : VExpr}

theorem supplyType_inst (H : supplyType args type = some output) :
    supplyType (args.map (·.inst arg k)) (type.inst arg k) = some (output.inst arg k) := by
  induction args generalizing type with
  | nil => cases H; rfl
  | cons a args ih =>
    cases type <;> try contradiction
    simp only [supplyType, List.map_cons, VExpr.inst, ← VExpr.inst0_inst_hi]
    exact ih H

/-- Substitute an outer term through the remaining dependent telescope. -/
def PrefixUnfolding.instN (program : PrefixUnfolding) (arg : VExpr) (k : Nat) : PrefixUnfolding :=
  { program with
    domains := instDomains program.domains arg k
    result := program.result.inst arg (k + program.domains.length)
    constructor := program.constructor.inst arg (k + program.domains.length)
    captures := program.captures.map (·.inst arg (k + program.domains.length)) }

@[simp] theorem PrefixUnfolding.type_instN (program : PrefixUnfolding) :
    (program.instN arg k).type = program.type.inst arg k := by
  simp only [PrefixUnfolding.instN, PrefixUnfolding.type, wrapForalls_inst]


theorem PrefixUnfolding.rhs_instN (program : PrefixUnfolding)
    (hclosed : program.equationBody.rhs.ClosedN program.captures.length) :
    (program.instN arg k).rhs = program.rhs.inst arg k := by
  simp only [PrefixUnfolding.instN, PrefixUnfolding.rhs, wrapLams_inst,
    InductiveSignature.instantiateParams_inst (hclosed.instL (ls := program.levels))]

private theorem vars_inst_above (n k : Nat) (arg : VExpr) :
    (vars n 0).map (·.inst arg (k+n)) = vars n 0 := by
  conv => rhs; rw [← List.map_id (l := vars n 0)]
  apply List.map_congr_left
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact (show (VExpr.bvar (0+i)).ClosedN n from by simpa only [VExpr.ClosedN, Nat.zero_add] using hi).instN_eq (j := k+n) (by omega)

theorem singletonUnfolding_inst {data : RecursorData} {recType : VExpr} {env : VEnv}
    {packed : List VLevel} (henv : env.WF) (hr : VEnv.RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (htype : data.recursorType = some recType) (hclosed : recType.Closed)
    (H : data.singletonUnfolding env U levels args = some program) :
    data.singletonUnfolding env U levels (args.map (·.inst arg k)) = some (program.instN arg k) := by
  unfold singletonUnfolding at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, htype, Option.bind_some, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, ⟨constructor, fields⟩, hrecon,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptureCount
  cases H
  have hlen := VExpr.takeForalls_domains_length htake
  have hsupply' := supplyType_inst (arg := arg) (k := k) hsupply
  rw [(hclosed.instL (ls := levels)).instN_eq (Nat.zero_le _)] at hsupply'
  have htake' := takeForalls_instDomains (arg := arg) (k := k) htake
  have hn : args.length ≤ data.majorOffset := by
    by_cases hn : args.length ≤ data.majorOffset
    · exact hn
    · exact (hguard (by simp [show data.majorOffset < args.length by omega])).elim
  let remaining := data.majorOffset + 1 - args.length
  have hall :
      (args.map (·.inst arg k)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (·.inst arg (k + remaining)) := by
    simp only [List.map_append, List.map_map, Function.comp_def, vars_inst_above,
      liftN_instN_lo _ _ _ _ _ (Nat.zero_le _), Nat.add_comm remaining k]
  have hvarslen (n j : Nat) : (vars n j).length = n := by simp [vars]
  have hallLen : (args.map (·.liftN remaining) ++ vars remaining 0).length = data.majorOffset + 1 := by
    simp only [List.length_append, List.length_map, hvarslen]; omega
  have hrecon' := singletonReconstruction_inst (a := arg) (K := k + remaining) henv hr hlarge hzero hallLen (by omega) hrecon
  rw [← hall] at hrecon'
  dsimp only [remaining] at hrecon'
  simp only [bind, htype, Option.bind_some, hsupply', htake', hrecon', hequation, hbody,
    List.length_map, List.length_append, List.length_take, hvarslen] at hcaptureCount ⊢
  rw [if_neg hcaptureCount]
  simp only [Option.pure_def, Option.some.injEq, PrefixUnfolding.instN, PrefixUnfolding.mk.injEq,
    hlen, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_take]

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.RecursorData

theorem etaOpen_instN (source arg : VExpr) (n k : Nat) :
    (etaOpen n source).inst arg (k+n) = etaOpen n (source.inst arg k) := by
  induction n generalizing source k with
  | zero => rfl
  | succ n ih =>
    simp only [etaOpen]
    rw [show k + (n+1) = (k+1)+n by omega, ih]
    congr 1
    simp only [VExpr.inst]
    rw [← lift_instN_lo]
    simp [instVar]

theorem ConstSpineDefEq.instN (henv : env.WF)
    (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A) (H : ConstSpineDefEq env U Γ₁ actual expected) :
    ConstSpineDefEq env U Γ (actual.inst arg k) (expected.inst arg k) := by
  obtain ⟨name, levels, levels', args, args', rfl, rfl, hw, hw', heq, hargs⟩ := H
  refine ⟨name, levels, levels', args.map (·.inst arg k), args'.map (·.inst arg k),
    inst_mkApps .., inst_mkApps .., hw, hw', heq, ?_⟩
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.instN henv.ordered W harg) hargs

theorem UnfoldingCheck.instN (henv : env.WF)
    (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A) (H : UnfoldingCheck env U Γ₁ source program) :
    UnfoldingCheck env U Γ (source.inst arg k) (program.instN arg k) := by
  have Wext := Ctx.InstN.reverse program.domains W
  rw [Nat.add_comm program.domains.length k] at Wext
  have hscope := H.templateScope henv
  have hn : 0 < program.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  refine {
    source_typed := ?_
    remaining_nonempty := ?_
    equation_present := H.equation_present
    equation_body := H.equation_body
    levels_wf := H.levels_wf
    levels_length := H.levels_length
    captures_length := ?_
    captures_typed := ?_
    major_prop := ?_
    recursor_lhs := ?_ }
  · rw [PrefixUnfolding.type_instN]
    exact H.source_typed.instN henv.ordered W harg
  · intro he
    have he' := congrArg List.length he
    simp only [PrefixUnfolding.instN, instDomains_length, List.length_nil] at he'
    omega
  · simpa only [PrefixUnfolding.instN, List.length_map] using H.captures_length
  · intro j hj hd
    have hj₀ : j < program.captures.length := by simpa only [PrefixUnfolding.instN, List.length_map] using hj
    have ht := (H.captures_typed j hj₀ hd).instN henv.ordered Wext harg
    have hclosed : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj₀)] using
        (hscope.2.2 j hd).instL (ls := program.levels)
    rw [← instantiateParams_eq_instOuter, InductiveSignature.instantiateParams_inst hclosed] at ht
    simp only [PrefixUnfolding.instN, List.getElem_map, List.map_take, instantiateParams_eq_instOuter] at ht ⊢
    exact ht
  · obtain ⟨proposition, hp, hm, hc⟩ := H.major_prop
    refine ⟨proposition.inst arg (k+program.domains.length), hp.instN henv.ordered Wext harg, ?_,
      hc.instN henv.ordered Wext harg⟩
    have hm' := hm.instN henv.ordered Wext harg
    simpa only [PrefixUnfolding.instN, VExpr.inst, instVar, if_pos (show 0 < k + program.domains.length by omega)] using hm'
  · have hm := H.recursor_lhs.instN henv Wext harg
    rw [← instantiateParams_eq_instOuter, InductiveSignature.instantiateParams_inst (hscope.1.instL (ls := program.levels))] at hm
    have hlength : k + program.domains.length = (k + (program.domains.length-1)) + 1 := by omega
    simp only [VExpr.inst] at hm
    rw [hlength, ← lift_instN_lo, etaOpen_instN] at hm
    simpa only [PrefixUnfolding.instN, instDomains_length, instantiateParams_eq_instOuter, ← hlength] using hm

theorem PrefixUnfold.instN {name : Name} {levels : List VLevel}
    (henv : env.WF) (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A)
    (H : PrefixUnfold env U registry Γ₁ name levels args rhs) :
    PrefixUnfold env U registry Γ name levels (args.map (·.inst arg k)) (rhs.inst arg k) := by
  cases H with
  | @intro data program hl hr hn ht hw hz hg replay =>
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold singletonUnfolding at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    have hg' := singletonUnfolding_inst henv hr ht hz htype (hr.recursorType_closed henv htype) hg (arg := arg) (k := k)
    have replay' := replay.instN henv W harg
    simp only [inst_mkApps, VExpr.inst] at replay'
    rw [← PrefixUnfolding.rhs_instN program (replay.templateScope henv).2.1]
    exact .intro hl hr hn ht hw hz hg' replay'

end Lean4Lean.VEnv


namespace Lean4Lean.QuotPrefixUnfolding
open VExpr VEnv InductiveSignature InductiveSignature.RecursorData

private theorem getD_map_inst (args : List VExpr) (i : Nat) (arg : VExpr) (k : Nat) :
    (args.map (·.inst arg k))[i]?.getD default = (args[i]?.getD default).inst arg k := by
  simp only [List.getElem?_map]
  cases args[i]? <;> rfl

theorem generate_inst {levels : List VLevel}
    (H : generate levels args = some program) :
    generate levels (args.map (·.inst arg k)) = some (program.instN arg k) := by
  unfold generate at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, hbody, H⟩ := H
  cases H
  have hclosed : quotLiftConst.type.Closed := by decide
  have hsupply' := supplyType_inst (arg := arg) (k := k) hsupply
  rw [(hclosed.instL (ls := levels)).instN_eq (Nat.zero_le _)] at hsupply'
  have htake' := takeForalls_instDomains (arg := arg) (k := k) htake
  have hlen := VExpr.takeForalls_domains_length htake
  simp only [bind, hsupply', Option.bind_some, htake', hbody, Option.pure_def,
    Option.some.injEq, PrefixUnfolding.instN, PrefixUnfolding.mk.injEq, hlen]
  have hall : (args.map (fun e => (e.inst arg k).liftN (6 - args.length)) ++ vars (6 - args.length) 0) =
      (args.map (·.liftN (6 - args.length)) ++ vars (6 - args.length) 0).map
        (·.inst arg (k + (6 - args.length))) := by
    simp only [List.map_append, List.map_map, Function.comp_def, vars_inst_above,
      liftN_instN_lo _ _ _ _ _ (Nat.zero_le _), Nat.add_comm (6 - args.length) k]
  simp only [List.map_map, Function.comp_def]
  rw [hall]
  simp only [getD_map_inst]
  simp only [inst_mkApps, List.map_cons, List.map_nil, List.map_append,
    List.map_take, VExpr.inst, (propInhabitant_closed _).instN_eq (Nat.zero_le _), and_self]

end Lean4Lean.QuotPrefixUnfolding

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.RecursorData

theorem QuotPrefixUnfold.instN {levels : List VLevel}
    (henv : env.WF) (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A) (H : QuotPrefixUnfold env U Γ₁ levels args rhs) :
    QuotPrefixUnfold env U Γ levels (args.map (·.inst arg k)) (rhs.inst arg k) := by
  cases H with
  | @intro program hr hw hz hg replay =>
    have hg' := QuotPrefixUnfolding.generate_inst (arg := arg) (k := k) hg
    have replay' := replay.instN henv W harg
    simp only [inst_mkApps, VExpr.inst] at replay'
    rw [← PrefixUnfolding.rhs_instN program (replay.templateScope henv).2.1]
    exact .intro hr hw hz hg' replay'

end Lean4Lean.VEnv
