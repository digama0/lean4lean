import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation
import Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution

namespace Lean4Lean.InductiveSignature
open VExpr

theorem Restoration.wrapForalls_shape {r : Restoration}
    (H : r.expr (VExpr.wrapForalls domains body) = some output) :
    ∃ domains' body', output = VExpr.wrapForalls domains' body' ∧ domains'.length = domains.length := by
  induction domains generalizing output with
  | nil => exact ⟨[], output, rfl, rfl⟩
  | cons domain domains ih =>
    change (do let domain' ← r.expr domain; let body' ← r.expr (VExpr.wrapForalls domains body)
               pure (.forallE domain' body')) = some output at H
    simp only [bind, Option.bind_eq_some_iff] at H
    obtain ⟨domain', _, out, hout, H⟩ := H
    cases H
    obtain ⟨domains', body', rfl, hlen⟩ := ih hout
    exact ⟨domain' :: domains', body', rfl, congrArg Nat.succ hlen⟩

namespace RecursorData

theorem recursorType_telescope {data : RecursorData}
    (H : data.recursorType = some type) :
    ∃ domains body, type = VExpr.wrapForalls domains body ∧ domains.length = data.majorOffset + 1 := by
  unfold recursorType Instance.recursorType at H
  obtain ⟨domains, body, htype, hlen⟩ := Restoration.wrapForalls_shape H
  refine ⟨domains, body, htype, hlen.trans ?_⟩
  simp [Instance.params, Instance.motives, Instance.minors, insertBinders,
    majorOffset, indexOffset, numParams, numIndices, Nat.add_assoc]


theorem supplyType_wrapForalls_exists (hbound : args.length ≤ domains.length) :
    ∃ residual doms tail, supplyType args (VExpr.wrapForalls domains body) = some residual ∧
      residual = VExpr.wrapForalls doms tail ∧ doms.length = domains.length - args.length := by
  induction args generalizing domains body with
  | nil => exact ⟨_, domains, body, rfl, rfl, by simp⟩
  | cons arg args ih =>
    cases domains with
    | nil => simp at hbound
    | cons d ds =>
      have hn : args.length ≤ (VExpr.instDomains ds arg 0).length := by simp; simp at hbound; omega
      obtain ⟨residual, doms, tail, hsupply, hshape, hlen⟩ := ih
        (body := body.inst arg ds.length) hn
      refine ⟨residual, doms, tail, ?_, hshape, ?_⟩
      · change supplyType args ((VExpr.wrapForalls ds body).inst arg) = some residual
        rw [VExpr.wrapForalls_inst, Nat.zero_add]
        exact hsupply
      · simpa only [VExpr.instDomains_length, List.length_cons, Nat.add_sub_add_right] using hlen

theorem takeForalls_wrapForalls (domains : List VExpr) (body : VExpr) :
    VExpr.takeForalls domains.length (VExpr.wrapForalls domains body) = some (domains, body) := by
  induction domains with
  | nil => rfl
  | cons d ds ih =>
    change (do let p ← VExpr.takeForalls ds.length (VExpr.wrapForalls ds body); pure (d :: p.1, p.2)) = _
    rw [ih]
    rfl

theorem singletonUnfolding_sameArity {data : RecursorData} {levels : List VLevel} {env : VEnv}
    (H : data.singletonUnfolding env U levels args = some program) (hargs : args'.length = args.length) :
    ∃ program', data.singletonUnfolding env U levels args' = some program' := by
  have hbound := (singletonUnfolding_spec H).1
  unfold singletonUnfolding at H ⊢
  simp only [hargs]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
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
  have hlen'' : domains'.length = data.majorOffset + 1 - args.length := by
    simpa only [List.length_map, hlen, hargs] using hlen'
  have htake' := takeForalls_wrapForalls domains' result'
  rw [hlen''] at htake'
  have hrecon' : ∃ p, data.singletonReconstruction env levels
      (args'.map (·.liftN (data.majorOffset + 1 - args.length)) ++
        vars (data.majorOffset + 1 - args.length) 0) = some p := by
    have h := singletonReconstruction_isSome env data levels
      (args'.map (·.liftN (data.majorOffset + 1 - args.length)) ++
        vars (data.majorOffset + 1 - args.length) 0)
      (args.map (·.liftN (data.majorOffset + 1 - args.length)) ++
        vars (data.majorOffset + 1 - args.length) 0)
    rw [hrecon] at h
    cases hg : data.singletonReconstruction env levels
        (args'.map (·.liftN (data.majorOffset + 1 - args.length)) ++
          vars (data.majorOffset + 1 - args.length) 0) with
    | none => rw [hg] at h; cases h
    | some p => exact ⟨p, rfl⟩
  obtain ⟨⟨ctor', fields'⟩, hrecon'⟩ := hrecon'
  obtain ⟨S1, hS1, hl1⟩ := singletonReconstruction_fields_length hrecon
  obtain ⟨S2, hS2, hl2⟩ := singletonReconstruction_fields_length hrecon'
  cases hS1.symm.trans hS2
  simp only [Option.bind_some, htake', hrecon',
    hequation, hbody]
  simp only [List.length_append, List.length_map, List.length_take, hargs, hl1, hl2] at hcaptures ⊢
  rw [if_neg hcaptures]
  exact ⟨_, rfl⟩

end RecursorData
end Lean4Lean.InductiveSignature
