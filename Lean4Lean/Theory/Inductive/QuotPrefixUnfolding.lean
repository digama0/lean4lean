import Lean4Lean.Theory.Inductive.RecursorPrefixUnfolding
import Lean4Lean.Theory.Quot

/-! Prefix unfolding of `Quot.lift` (section 4.2 of the design notes): quotient
reconstruction at a Prop-valued source, where `Quot.ind` recovers a proof of the source
proposition from the quotient major. The unfolding retains the primitive quotient equation
`quotDefEq` for its typing. -/

namespace Lean4Lean.QuotPrefixUnfolding
open VExpr InductiveSignature InductiveSignature.RecursorData

/-- A closed selector. It is typable when `level` is equivalent to zero;
that occurrence guard belongs to the typed quotient reduction rule. -/
def propInhabitant (level : VLevel) : VExpr :=
  let alpha := VExpr.bvar 2
  let relation := VExpr.bvar 1
  let major := VExpr.bvar 0
  let quotient := mkApps (.const ``Quot [level]) [alpha, relation]
  wrapLams [ .sort level,
    .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    mkApps (.const ``Quot [level]) [.bvar 1, .bvar 0] ]
    (mkApps (.const ``Quot.ind [level]) [alpha, relation,
      .lam quotient alpha.lift, .lam alpha (.bvar 0), major])

theorem propInhabitant_closed (level : VLevel) : (propInhabitant level).Closed := by
  simp [propInhabitant, VExpr.wrapLams, VExpr.mkApps, VExpr.Closed, VExpr.ClosedN, VExpr.lift, VExpr.liftN]

/-- Open the remaining quotient-lift prefix, reconstruct its major, and
retain the exact six captures of the primitive equation. -/
def generate (levels : List VLevel) (arguments : List VExpr) : Option PrefixUnfolding := do
  if levels.length != 2 || arguments.length > 5 then none else
  let residual ← supplyType arguments (quotLiftConst.type.instL levels)
  let remaining := 6 - arguments.length
  let (domains, result) ← VExpr.takeForalls remaining residual
  let allArguments := arguments.map (·.liftN remaining) ++ vars remaining 0
  let alpha := allArguments[0]?.getD default
  let relation := allArguments[1]?.getD default
  let major := allArguments[5]?.getD default
  let level := levels[0]?.getD .zero
  let proof := mkApps (propInhabitant level) [alpha, relation, major]
  let constructor := mkApps (.const ``Quot.mk [level]) [alpha, relation, proof]
  let captures := allArguments.take 5 ++ [proof]
  let body ← CaseSchema.EquationBody.extract quotDefEq.lhs quotDefEq.rhs quotDefEq.type
  return ⟨domains, result, constructor, quotDefEq, body, captures, levels⟩

theorem generate_unique {levels : List VLevel} (h : generate levels args = some p)
    (h' : generate levels args = some p') : p = p' :=
  Option.some.inj (h.symm.trans h')

/-- Generation retains the quotient equation and its exact telescope
arity; no structural checks need be supplied by the caller. -/
theorem generate_spec {levels : List VLevel} (H : generate levels args = some program) :
    levels.length = 2 ∧ args.length ≤ 5 ∧ program.domains ≠ [] ∧
    program.levels = levels ∧ program.equation = quotDefEq ∧
    CaseSchema.EquationBody.extract program.equation.lhs program.equation.rhs
      program.equation.type = some program.equationBody ∧
    program.captures.length = program.equationBody.domains.length := by
  unfold generate at H
  split at H <;> try contradiction
  rename_i hguard
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, _, ⟨domains, result⟩, htake, body, hbody, H⟩ := H
  cases H
  simp at hguard
  have hlevels : levels.length = 2 := by simpa using hguard.1
  have hargs : args.length ≤ 5 := by simpa using hguard.2
  have hlen := VExpr.takeForalls_domains_length htake
  have hbodylen : body.domains.length = 6 := by
    have hh : (CaseSchema.EquationBody.extract quotDefEq.lhs quotDefEq.rhs quotDefEq.type).map
        (fun b => b.domains.length) = some 6 := by decide
    rw [hbody] at hh
    exact Option.some.inj hh
  refine ⟨hlevels, hargs, ?_, rfl, rfl, hbody, ?_⟩
  · intro hn
    change domains = [] at hn
    simp only [hn, List.length_nil] at hlen
    omega
  · simp only [List.length_append, List.length_take, List.length_map, List.length_cons,
      List.length_nil, vars, List.length_reverse, List.length_range, hbodylen]
    omega

end Lean4Lean.QuotPrefixUnfolding
