import Lean4Lean.Verify.Inductive.Constructor.Tails
import Lean4Lean.Verify.Inductive.HeaderData  -- WAVE 2 install COMPAT

/-! # The constructor check: `checkConstructors`

`AddInductive.checkConstructors` walks every constructor type of the block in the header
environment, against the cached common parameters, checks the universe and positivity of
every field and the validity of the result, and returns the field classifications.
`ConstructorsChecked` is what a successful run establishes, for the declaration whose
constructor types are the translations of the source ones; `AddInductive.checkConstructors.WF`
is the refinement theorem.

The refinement theorem is the named stub `AddInductive.checkConstructors.WF` (`STUBS.md`,
"Wave 2 ctor"). On the source branch it is `checkConstructors.loopTypes.refinesChecked`
(`Constructor/CheckedConstructors.lean`) over `Constructor/{Positivity,Normalization,
RawTranslation,Translation}.lean`, `Recursor/Binders/ParameterPrefixes.lean` and the owner
normal forms of `Recursor/Context/FVarArrays.lean`; those proofs walk the checker's context
frames (`withUnannotatedCheckedLocalDecl`, `paramCheckLCtx`) through the header phase's
parameter scope (`HeaderStatsWF`: `parameterSuffix`, `normalizedShapes`, `paramsContext`),
which the header agent ports beneath `HeaderEnvironment`/`HeaderPhase` (`Context/**`,
`Header/**`). The statement below asks only for the header interface. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- What a successful constructor check establishes for the declaration `decl` (whose header
data the header environment `H` installed), with the classifications `classes` it returned:
the translation of every source constructor in the header environment, the formation
certificates of the constructors, their checked tails, and the concrete telescopes the recursor
construction re-walks. -/
structure ConstructorsChecked {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool} {depth : Nat} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv : Environment}
    -- WAVE 2 install COMPAT: stated over the header data (no header `ContextWF`)
    (H : HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv)
    (classes : List (List (List Bool))) : Prop where
  /-- Every source constructor translates to the declaration's constructor, in the header
  environment. -/
  ctorTr : List.Forall₂ (fun (source : InductiveType) (target : VInductiveType) =>
      List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
        TrSourceConst H.context.venv c.lparams ctor.name ctor.type ctor')
        source.ctors target.ctors)
    indTypes.toList decl.types
  parameterShapes : ConstructorParameterCertificate H.context.venv decl H.headers.params
  shapes : ConstructorCertificate sourceEnv decl H.context.venv H.headers.params
  rawShapes : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor
  types : ∀ ctor ∈ decl.constructorConstants, H.context.venv.IsType decl.uvars [] ctor.type
  classes_length : classes.length = indTypes.size
  tails : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
    CheckedCtorTail H.context.venv decl H.headers.params decl.types[i]
      decl.types[i].ctors[j] (classes[i]![j]!)
  /-- The concrete parameter prefixes and forall spines of the kernel constructor types. -/
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  /-- The concrete checked tails, in the header environment's parameter scope. -/
  constructorTails : ConstructorTails H.context.venv c.lparams H.statsWF.parameterScope
    stats decl indTypes classes
  /-- The owner normal forms of the kernel constructor types. -/
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes

end VerifyInductive
end Lean4Lean
