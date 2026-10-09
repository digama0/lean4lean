import Lean4Lean.Theory.Typing.PrefixUnfolding.Renaming

/-! Supplying the next recursor argument specializes the generated residual
lambda term. This is the concrete overlap between two recursor prefixes. -/

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr CaseSchema VEnv
variable {type : VExpr} {levels : List VLevel}

theorem supplyType_append (args tail : List VExpr) (type : VExpr) :
    supplyType (args ++ tail) type = (supplyType args type).bind (supplyType tail) := by
  induction args generalizing type with
  | nil => rfl
  | cons arg args ih => cases type <;> simp [supplyType, ih]

theorem takeForalls_instDomains
    (H : VExpr.takeForalls count type = some (domains, result)) :
    VExpr.takeForalls count (type.inst arg k) =
      some (instDomains domains arg k, result.inst arg (k + count)) := by
  induction count generalizing type domains result k with
  | zero => cases H; rfl
  | succ n ih =>
    cases type <;> try contradiction
    simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, ht, he⟩ := H
    cases he
    simp only [VExpr.inst, VExpr.takeForalls, bind, ih ht, Option.bind_some,
      Option.pure_def, instDomains, Nat.add_assoc, Nat.add_comm 1]

theorem _root_.Lean4Lean.InductiveSignature.instantiateParams_inst {body : VExpr} {captures : List VExpr}
    (hclosed : body.ClosedN captures.length) :
    (instantiateParams body captures).inst arg k =
      instantiateParams body (captures.map (·.inst arg k)) := by
  rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
    instOuter_eq_subst, instOuter_eq_subst, instN_eq, subst_subst]
  apply subst_congr_closedN hclosed
  intro i hi
  simp only [Subst.comp, Subst.ofList, List.length_map, dif_pos hi,
    List.getElem_map, ← instN_eq]

theorem singletonUnfolding_supply_one {data : RecursorData} {env : VEnv}
    {args : List VExpr} {early late : PrefixUnfolding}
    {packed : List VLevel} (henv : env.WF) (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (hEarly : data.singletonUnfolding env U levels args = some early)
    (hLate : data.singletonUnfolding env U levels (args ++ [arg]) = some late)
    (hclosed : early.equationBody.rhs.ClosedN early.captures.length) :
    ∃ domain body, early.rhs = .lam domain body ∧ body.inst arg = late.rhs := by
  have hbound := (singletonUnfolding_spec hLate).1
  simp only [List.length_append, List.length_singleton] at hbound
  let n := data.majorOffset - args.length
  have hn : 0 < n := by dsimp [n]; omega
  have hearlyLen : data.majorOffset + 1 - args.length = n + 1 := by dsimp [n]; omega
  have hlateLen : data.majorOffset + 1 - (args ++ [arg]).length = n := by
    simp only [List.length_append, List.length_singleton]; dsimp [n]; omega
  unfold singletonUnfolding at hEarly hLate
  dsimp only at hEarly hLate
  split at hEarly <;> try contradiction
  split at hLate <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hEarly
  obtain ⟨recType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, hrecon, equation, hequation, eqbody, hbody, hEarly⟩ := hEarly
  split at hEarly <;> try contradiction
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
  have hallLen : (args.map (·.liftN (n + 1)) ++ vars (n + 1) 0).length = data.majorOffset + 1 := by
    simp [vars]; omega
  rw [hearlyLen] at hrecon
  have hrecon' := singletonReconstruction_inst (a := arg) (K := n) henv hr hlarge hzero hallLen hn hrecon
  have hall : (args.map (·.liftN (n + 1)) ++ vars (n + 1) 0).map (·.inst arg n) =
      (args ++ [arg]).map (·.liftN n) ++ vars n 0 := by
    simp only [List.map_append, List.map_map, Function.comp_def, inst_liftN_lo, InductiveSignature.vars_inst_last,
      List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  rw [hall] at hrecon'
  simp only [bind, htype, Option.bind_some, supplyType_append, hsupply,
    supplyType, hlateLen, htake', hrecon',
    hequation, hbody] at hLate
  split at hLate <;> try contradiction
  cases hLate
  refine ⟨domain, _, rfl, ?_⟩
  change (wrapLams ds _).inst arg = wrapLams (instDomains ds arg 0) _
  rw [wrapLams_inst, Nat.zero_add, hds, instantiateParams_inst hclosed.instL]
  congr 2
  simp only [hearlyLen, List.map_append, List.map_take,
    List.map_map, Function.comp_def, inst_liftN_lo, InductiveSignature.vars_inst_last,
    List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

end Lean4Lean.InductiveSignature.RecursorData
