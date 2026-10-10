import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Lowered
import Lean4Lean.Verify.Inductive.Nested.Restoration.Run

/-! # Parameter uniformity of a nested run's recursors (owner: Restoration-A)

The `NestedRun` section of the source branch's `Nested/Restoration/Uniform/Recursors.lean`:
the auxiliary heads of a run, and the parameter uniformity of the lowered recursor read back by
any restoration step (`NestedRun.recursorParamUniform`), over Restoration-B's `NestedRun`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! ### Validated nested runs -/

/-- The auxiliary heads of a nested run: the names of the lowered families after
the source families, each followed by the names of its constructors. This is
the head list `auxiliaries.flatMap (·.headNames)` of the run's container
specialisations (`NestedRun.loweredConstructorLevels_heads`).
The theorems below are stated for an arbitrary head list; this is the intended
instance. -/
def NestedRun.auxHeads
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  InductiveSignature.familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)

section Run

variable {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)

/-- The lowered run's statistics carry the declaration's universe parameters. -/
theorem NestedRun.statsLevels :
    E.lowered.stats.levels = lparams.map Level.param := by
  have h := E.lowered.headers.statsWF.levelParams
  rwa [E.lowered_c, E.context_lparams] at h

/-- The lowered run's statistics carry exactly `result.nparams` parameters. -/
theorem NestedRun.statsParamsSize :
    E.lowered.stats.params.size = result.nparams := by
  obtain ⟨_, Hrun, _, _⟩ := E.lowering
  rw [Hrun.resultNParams, E.lowered.recursors.cardinality.params,
    E.lowered.constructors.core.nparams, E.lowered_nparams]

/-- The generated entry of an owner is the recursor read back by any
restoration step at the owner's recursor name. -/
theorem NestedRun.generatedEntryOfStep
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    ∃ hi : owner.val < E.lowered.recursors.entries.length,
      (E.lowered.recursors.generated.entry owner.val hi).info =
        Hstep.oldInfo := by
  rcases E.lowered.recursors.trMetadata owner with
    ⟨rec, hrec, _, M⟩
  have hlen : owner.val < E.lowered.recursors.entries.length := by
    rw [E.lowered.recursors.entries_length_eq]
    exact owner.isLt
  refine ⟨hlen, ?_⟩
  have hmem := List.getElem_mem (l := E.lowered.recursors.entries)
    (n := owner.val) hlen
  have hfind := E.lowered.recursors.installed.findOfMem E.lowered.recursors.ctorMapWF
    (info := (E.lowered.recursors.entries[owner.val]'hlen).1)
    (value := (E.lowered.recursors.entries[owner.val]'hlen).2) hmem
  have hrec' : (E.lowered.recursors.entries[owner.val]'hlen).1 = .recInfo rec := hrec
  rw [hrec'] at hfind
  change E.loweredEnv.find? rec.name = some (.recInfo rec) at hfind
  have h2 : some (ConstantInfo.recInfo rec) = some (.recInfo Hstep.oldInfo) := by
    rw [← hfind, M.name]
    exact Hstep.lookup
  have heq : rec = Hstep.oldInfo := by
    injection h2 with h
    injection h
  have hG := (E.lowered.recursors.generated.entry owner.val hlen).source_eq
  rw [hrec] at hG
  injection hG with hG
  rw [← heq, hG]

/-- **Parameter uniformity of the lowered recursor type and rule right-hand sides of a
validated nested run.** For every generated owner and every executable
restoration step at the owner's lowered recursor name, the stored recursor type
and every stored rule right-hand side are closed parameter telescopes of
`result.nparams` binders whose body is parameter-uniform in bound-variable form for the
heads `heads` at the levels `lparams.map Level.param`.

Hypotheses: `W` (`whnf` preserves parameter uniformity, see
`WhnfPreservesParamUniform`) and `I` (the non-`whnf` hypotheses, see
`RecursorConstruction.ParamUniformDeclarations`). Both are discharged at
`heads := E.uniformHeads` in `Nested/Restoration/Uniform/Whnf.lean`
(`NestedRun.recursorParamUniform_of_wfCore`). -/
theorem NestedRun.recursorParamUniform
    {heads : List Name}
    (I : E.lowered.recursors.toRecursorConstruction.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads E.lowered.stats.params.toList (lparams.map Level.param)
      E.lowered.recursors.localContext.env)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.ParamUniformTele heads result.nparams (lparams.map Level.param) Hstep.oldInfo.type ∧
      ∀ rule ∈ Hstep.oldInfo.rules,
        Expr.ParamUniformTele heads result.nparams (lparams.map Level.param) rule.rhs := by
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  rw [← E.statsLevels] at W ⊢
  rw [← E.statsParamsSize]
  have H := E.lowered.recursors.generatedParamUniform I W owner.val hi
  rw [hinfo] at H
  exact H

end Run


end VerifyInductive
end Lean4Lean
