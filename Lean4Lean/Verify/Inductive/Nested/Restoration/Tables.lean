import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope

/-! The restoration table data of a nested run: the executable facts that fix the
executable restoration tables relative to an abstract specialisation list
(`RestorationTablesAgree`). It is stated separately from the nested installation so that
`RestoredBlockDerivation` can record the specialisation list of its restored case eliminators. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace InductiveSignature

/-- Names claimed by the restoration heads of one specialisation: the
auxiliary family followed by its constructors. -/
def ContainerSpecialization.headNames (a : ContainerSpecialization) : List Name :=
  a.auxiliary :: a.source.ctors.map a.constructorName

end InductiveSignature

namespace VerifyInductive

/-- The recorded container application of one auxiliary, abstracted over the
lowering parameters, is the container family applied to arguments whose
translations in the parameter telescope are the specialisation arguments. -/
def AuxiliaryContainerApp (result : Lean4Lean.ElimNestedInductive.Result) (Us₀ : List Name)
    (nested : Expr) (a : InductiveSignature.ContainerSpecialization) : Prop :=
  ∃ (envS : VEnv) (domains : List VExpr) (lvls : List Level) (Ys : List Expr),
    domains.length = result.nparams ∧
    nested.abstract result.params = Expr.mkAppList (.const a.source.name lvls) Ys ∧
    lvls.mapM (VLevel.ofLevel Us₀) = some a.levels ∧
    List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys a.arguments

/-- `AuxiliaryContainerApp` in a fixed environment, with parameter domains
definitionally equal to the context `ctx`. -/
def AuxiliaryContainerAppAt (envS : VEnv) (ctx : List VExpr)
    (result : Lean4Lean.ElimNestedInductive.Result) (Us₀ : List Name)
    (nested : Expr) (a : InductiveSignature.ContainerSpecialization) : Prop :=
  ∃ (domains : List VExpr) (lvls : List Level) (Ys : List Expr),
    domains.length = result.nparams ∧
    VEnv.IsDefEqCtx envS Us₀.length [] domains.reverse ctx ∧
    nested.abstract result.params = Expr.mkAppList (.const a.source.name lvls) Ys ∧
    lvls.mapM (VLevel.ofLevel Us₀) = some a.levels ∧
    List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys a.arguments

/-- Executable facts about one run that fix the executable restoration
tables relative to the abstract specialisation list `auxiliaries`. -/
structure RestorationTablesAgree (decl : VInductDecl)
    (auxiliaries : List InductiveSignature.ContainerSpecialization)
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (auxRec : NameMap Name) (Us₀ : List Name) : Prop where
  headNodup : (auxiliaries.flatMap (·.headNames)).Nodup
  uvars : decl.uvars = Us₀.length
  nparams : decl.nparams = result.nparams
  paramsFVars : ∃ xs : List FVarId, result.params = ⟨xs.map .fvar⟩
  recursorName : ∀ c,
    (InductiveSignature.compilationRestoration decl auxiliaries).recursorName c =
    (auxRec.find? c).getD c
  recursorNotHead : ∀ c new, auxRec.find? c = some new →
    c ∉ auxiliaries.flatMap (·.headNames)
  familyKey : ∀ c nested, result.aux2nested.find? c = some nested →
    ∃ a ∈ auxiliaries, a.auxiliary = c ∧ AuxiliaryContainerApp result Us₀ nested a
  familyLookup : ∀ a ∈ auxiliaries, ∃ nested,
    result.aux2nested.find? a.auxiliary = some nested
  ctorLookup : ∀ c info, env.find? c = some (.ctorInfo info) →
    ∀ a ∈ auxiliaries, info.induct = a.auxiliary →
      ∃ ctor ∈ a.source.ctors, c = a.constructorName ctor
  ctorInstalled : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors, ∃ info,
    env.find? (a.constructorName ctor) = some (.ctorInfo info) ∧
      info.induct = a.auxiliary
  ctorRenamed : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
    a.constructorName ctor ≠ ctor.name

end VerifyInductive
end Lean4Lean
