import Lean4Lean.Theory.Typing.PrefixUnfolding.Supply
import Lean4Lean.Theory.Typing.PrefixUnfolding.NormalCongruence

/-! # Supplying arguments to generated prefix unfoldings

Prefix generation succeeds at every admissible prefix length once it succeeds
at one, and supplying further arguments to a generated right-hand side beta
reduces to the unfolding generated at the longer prefix.
-/

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr

theorem singletonUnfolding_anyArity {data : RecursorData} {levels : List VLevel} {env : VEnv}
    (H : data.singletonUnfolding env U levels args = some program)
    (hargs : args'.length ≤ data.majorOffset) :
    ∃ program', data.singletonUnfolding env U levels args' = some program' := by
  have hbound := (singletonUnfolding_spec H).1
  unfold singletonUnfolding at H ⊢
  split at H <;> try contradiction
  rename_i hguard
  have hguard' : ¬((levels.length != data.uvars || args'.length > data.majorOffset) = true) := by
    simp at hguard ⊢; exact ⟨hguard.1, hargs⟩
  rw [if_neg hguard']
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨recType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, hrecon, equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptures
  obtain ⟨doms, tail, hshape, hlen⟩ := recursorType_telescope htype
  have hbound' : args'.length ≤ (doms.map (VExpr.instL levels)).length := by simp; omega
  obtain ⟨residual', domains', result', hsupply', hshape', hlen'⟩ :=
    supplyType_wrapForalls_exists (body := tail.instL levels) hbound'
  simp only [bind, htype, Option.bind_some]
  rw [hshape, VExpr.instL_wrapForalls]
  simp only [hsupply', Option.bind_some, hshape']
  have hlen'' : domains'.length = data.majorOffset + 1 - args'.length := by
    simpa only [List.length_map, hlen] using hlen'
  have htake' := takeForalls_wrapForalls domains' result'
  rw [hlen''] at htake'
  have hrecon' : ∃ p, data.singletonReconstruction env levels
      (args'.map (·.liftN (data.majorOffset + 1 - args'.length)) ++
        vars (data.majorOffset + 1 - args'.length) 0) = some p := by
    have h := singletonReconstruction_isSome env data levels
      (args'.map (·.liftN (data.majorOffset + 1 - args'.length)) ++
        vars (data.majorOffset + 1 - args'.length) 0)
      (args.map (·.liftN (data.majorOffset + 1 - args.length)) ++
        vars (data.majorOffset + 1 - args.length) 0)
    rw [hrecon] at h
    cases hg : data.singletonReconstruction env levels
        (args'.map (·.liftN (data.majorOffset + 1 - args'.length)) ++
          vars (data.majorOffset + 1 - args'.length) 0) with
    | none => rw [hg] at h; cases h
    | some p => exact ⟨p, rfl⟩
  obtain ⟨⟨ctor', fields'⟩, hrecon'⟩ := hrecon'
  obtain ⟨S1, hS1, hf1⟩ := singletonReconstruction_fields_length hrecon
  obtain ⟨S2, hS2, hf2⟩ := singletonReconstruction_fields_length hrecon'
  cases hS1.symm.trans hS2
  simp only [Option.bind_some, htake', hrecon',
    hequation, hbody]
  have hl1 : (args.map (·.liftN (data.majorOffset + 1 - args.length)) ++
      vars (data.majorOffset + 1 - args.length) 0).length = data.majorOffset + 1 := by
    simp only [List.length_append, List.length_map, vars, List.length_reverse, List.length_range]
    omega
  have hl2 : (args'.map (·.liftN (data.majorOffset + 1 - args'.length)) ++
      vars (data.majorOffset + 1 - args'.length) 0).length = data.majorOffset + 1 := by
    simp only [List.length_append, List.length_map, vars, List.length_reverse, List.length_range]
    omega
  simp only [List.length_append, List.length_take, hl1, hf1] at hcaptures
  simp only [List.length_append, List.length_take, hl2, hf2]
  rw [if_neg hcaptures]
  exact ⟨_, rfl⟩

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.QuotPrefixUnfolding
open VExpr InductiveSignature InductiveSignature.RecursorData VEnv

/-- Quotient prefix generation succeeds at every admissible prefix length. -/
theorem generate_anyArity {levels : List VLevel} (H : generate levels args = some program)
    (hlen : args'.length ≤ 5) :
    ∃ program', generate levels args' = some program' := by
  obtain ⟨hlevels, _, _⟩ := generate_spec H
  obtain ⟨domains, body, hshape, hcount⟩ : ∃ domains body,
      quotLiftConst.type = wrapForalls domains body ∧ domains.length = 6 := by
    exact ⟨(quotLiftConst.type.takeForalls 6).getD ([], .bvar 0) |>.1,
      (quotLiftConst.type.takeForalls 6).getD ([], .bvar 0) |>.2, by decide, by decide⟩
  have hbound : args'.length ≤ (domains.map (VExpr.instL levels)).length := by
    simp only [List.length_map, hcount]
    omega
  obtain ⟨residual, remaining, result, hsupply, hresidual, hremaining⟩ :=
    supplyType_wrapForalls_exists (body := body.instL levels) hbound
  have hremaining' : remaining.length = 6 - args'.length := by
    simpa only [List.length_map, hcount] using hremaining
  have htake := RecursorData.takeForalls_wrapForalls remaining result
  rw [hremaining'] at htake
  unfold generate
  rw [if_neg (by simp [hlevels]; omega)]
  rw [hshape, VExpr.instL_wrapForalls]
  simp only [bind, hsupply, Option.bind_some, hresidual, htake]
  exact ⟨_, rfl⟩

private theorem getD_inst (l : List VExpr) (i : Nat) :
    (l[i]?.getD default).inst arg k = (l.map (·.inst arg k))[i]?.getD default := by
  rw [List.getElem?_map]; cases l[i]? <;> rfl

/-- Adjacent quotient prefixes meet by one beta step. -/
theorem generate_supply_one {levels : List VLevel} {args : List VExpr}
    {early late : PrefixUnfolding}
    (hEarly : generate levels args = some early)
    (hLate : generate levels (args ++ [arg]) = some late)
    (hclosed : early.equationBody.rhs.ClosedN early.captures.length) :
    ∃ domain body, early.rhs = .lam domain body ∧ body.inst arg = late.rhs := by
  have hbound := (generate_spec hLate).2.1
  simp only [List.length_append, List.length_singleton] at hbound
  let n := 5 - args.length
  have hn : 0 < n := by dsimp [n]; omega
  have hearlyLen : 6 - args.length = n + 1 := by dsimp [n]; omega
  have hlateLen : 6 - (args ++ [arg]).length = n := by
    simp only [List.length_append, List.length_singleton]; dsimp [n]; omega
  unfold generate at hEarly hLate
  split at hEarly <;> try contradiction
  split at hLate <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hEarly
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, eqbody, hbody, hEarly⟩ := hEarly
  cases hEarly
  rw [hearlyLen] at htake
  cases residual <;> try contradiction
  rename_i domain residualBody
  simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at htake
  obtain ⟨⟨ds, body⟩, htake, he⟩ := htake
  cases he
  have hds := VExpr.takeForalls_domains_length htake
  have htake' := takeForalls_instDomains (arg := arg) (k := 0) htake
  simp only [Nat.zero_add] at htake'
  simp only [bind, supplyType_append, hsupply, supplyType, hlateLen, htake',
    hbody, Option.bind_some] at hLate
  cases hLate
  refine ⟨domain, _, rfl, ?_⟩
  change (wrapLams ds _).inst arg = wrapLams (instDomains ds arg 0) _
  rw [wrapLams_inst, Nat.zero_add, hds, InductiveSignature.instantiateParams_inst hclosed.instL]
  congr 2
  have hall : ((args.map (·.liftN (6 - args.length)) ++ vars (6 - args.length) 0).map
      (·.inst arg n)) = (args ++ [arg]).map (·.liftN (6 - (args ++ [arg]).length)) ++
        vars (6 - (args ++ [arg]).length) 0 := by
    rw [hearlyLen, hlateLen]
    simp only [List.map_append, List.map_map, Function.comp_def, inst_liftN_lo,
      InductiveSignature.vars_inst_last, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append]
  simp only [List.map_append, List.map_take, List.map_cons, List.map_nil, hall]
  rw [hlateLen] at hall ⊢
  congr 2
  rw [inst_mkApps, (propInhabitant_closed _).instN_eq (Nat.zero_le _)]
  simp only [List.map_cons, List.map_nil, getD_inst, hall, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

end Lean4Lean.QuotPrefixUnfolding
