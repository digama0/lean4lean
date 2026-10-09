import Lean4Lean.Theory.Inductive

/-! Constructor index arity read off the literal checked constructor tail. This
uses only telescope syntax and the executable result-application count; no
typing uniqueness or sort/Pi separation is involved. -/
namespace Lean4Lean.InductiveSignature
open VExpr

/-- An exact constructor tail already records its result argument count.
Semantic equivalence of independently selected types is not used to recover
that structural fact. -/
theorem constructor_indices_length_of_rawTail
    {decl : VInductDecl} {s : InductiveSignature}
    {ctor : Constructor s.families.size} {target : VInductiveType}
    {tail : VExpr} {depth : Nat}
    (names : (decl.types.map (·.name)).Nodup)
    (targetMember : target ∈ decl.types)
    (params : s.params.length = decl.nparams)
    (family : s.families[ctor.owner].indices.length = target.numIndices)
    (raw : ∃ domains result, tail = wrapForalls domains result ∧
      decl.RawIndAppAt (some target.name) (depth + domains.length) result ∧
      result.getAppFnArgs.1 = .const target.name (VLevel.params decl.uvars))
    (literal : tail = wrapForalls (s.fieldTypes ctor)
      (s.familyApp ctor.owner (VLevel.params s.uvars)
        (vars s.params.length ctor.fields.length) ctor.indices)) :
    ctor.indices.length = s.families[ctor.owner].indices.length := by
  obtain ⟨domains, result, original, app, head⟩ := raw
  have resultZero : result.forallArity = 0 :=
    forallArity_eq_zero_of_getAppFnArgs (by rw [← head])
  have targetZero : (s.familyApp ctor.owner (VLevel.params s.uvars)
      (vars s.params.length ctor.fields.length) ctor.indices).forallArity = 0 :=
    forallArity_eq_zero_of_getAppFnArgs (getAppFnArgs_mkApps_const _ _ _)
  have lengths := congrArg VExpr.forallArity (original.symm.trans literal)
  simp only [forallArity_wrapForalls, resultZero, targetZero, Nat.add_zero] at lengths
  have result_eq := (wrapForalls_inj_of_length lengths (original.symm.trans literal)).2
  obtain ⟨actual, member, selected, levels, _, _, count, _⟩ := app
  have sameName : actual.name = target.name := by
    rcases selected with impossible | selected
    · cases impossible
    · exact (Option.some.inj selected).symm
  have same : actual = target := List.eq_of_mem_of_nodup_map names member targetMember sameName
  subst actual
  change result.getAppFnArgs.2.length = decl.nparams + target.numIndices at count
  rw [result_eq] at count
  simp only [familyApp, getAppFnArgs_mkApps_const, List.length_append,
    vars, List.length_map, List.length_reverse, List.length_range] at count
  omega

end Lean4Lean.InductiveSignature
