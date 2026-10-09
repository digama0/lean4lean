import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl

/-!
# Syntactic shapes of inductive declarations

Pure definitions describing the shapes of inductive headers and constructors.
They are separated from `Lean4Lean.Theory.Inductive` so that the environment
well-formedness predicates in `Lean4Lean.Theory.Typing.Lemmas` can record
declaration-level facts when projection metadata is registered.
-/

namespace Lean4Lean

def VInductDecl.ParamsDefEq (env : VEnv) (decl : VInductDecl)
    (params params' : List VExpr) : Prop :=
  VEnv.IsDefEqCtx env decl.uvars [] params.reverse params'.reverse

/-- Constant support inherited from source syntax. Projection owner names are
metadata rather than expression subterms, matching `Expr.findAny`. -/
inductive VExpr.SourceConstFree (names : List Name) : VExpr → Prop
  | bvar (index : Nat) : SourceConstFree names (.bvar index)
  | sort (level : VLevel) : SourceConstFree names (.sort level)
  | const (name : Name) (levels : List VLevel) (fresh : name ∉ names) :
      SourceConstFree names (.const name levels)
  | elim (block : Name) (owner : Nat) (levels : List VLevel) :
      SourceConstFree names (.elim block owner levels)
  | proj (typeName : Name) (index : Nat) :
      SourceConstFree names struct →
      SourceConstFree names (.proj typeName index struct)
  | app : SourceConstFree names fn → SourceConstFree names arg →
      SourceConstFree names (.app fn arg)
  | lam : SourceConstFree names domain → SourceConstFree names body →
      SourceConstFree names (.lam domain body)
  | forallE : SourceConstFree names domain →
      SourceConstFree names body → SourceConstFree names (.forallE domain body)

/-- Raw constructor-result skeleton. It records the owner, universe arity,
argument count, and literal common-parameter variables. Positivity and absence
of recursive constants in indices belong to `ValidIndAppAt`, separately. -/
def VInductDecl.RawIndAppAt (decl : VInductDecl) (target : Option Name)
    (depth : Nat) (e : VExpr) : Prop :=
  let (fn, args) := e.getAppFnArgs
  ∃ type ∈ decl.types, (target = none ∨ target = some type.name) ∧
    ∃ levels,
      fn = .const type.name levels ∧
      levels.length = decl.uvars ∧
      args.length = decl.nparams + type.numIndices ∧
      args.take decl.nparams = decl.paramVars depth

/-- A fully applied occurrence of one of the simultaneously declared types.
Recursive occurrences use precisely the common parameter variables, and their
indices contain no recursive occurrence. -/
def VInductDecl.ValidIndAppAt (decl : VInductDecl) (target : Option Name)
    (depth : Nat) (e : VExpr) : Prop :=
  let (fn, args) := e.getAppFnArgs
  ∃ type ∈ decl.types, (target = none ∨ target = some type.name) ∧
    ∃ levels,
      fn = .const type.name levels ∧
      levels.length = decl.uvars ∧
      args.length = decl.nparams + type.numIndices ∧
      args.take decl.nparams = decl.paramVars depth ∧
      ∀ arg ∈ args.drop decl.nparams,
        arg.SourceConstFree (decl.types.map (·.name))

theorem VInductDecl.ValidIndAppAt.raw {decl : VInductDecl}
    (h : decl.ValidIndAppAt target depth e) : decl.RawIndAppAt target depth e := by
  obtain ⟨type, hmem, htarget, levels, hfn, hlevels, hargs, hparams, _⟩ := h
  exact ⟨type, hmem, htarget, levels, hfn, hlevels, hargs, hparams⟩

/-- A positive normal form with the uniform recursive universe spine still
attached. Executable source checking supplies this stronger certificate. -/
def VInductDecl.UniformFieldNormalForm (decl : VInductDecl) (levels : List VLevel)
    (depth : Nat) (e : VExpr) : Prop :=
  e.SourceConstFree (decl.types.map (·.name)) ∨
  ∃ domains result, e = VExpr.wrapForalls domains result ∧
    (∀ domain ∈ domains, domain.SourceConstFree (decl.types.map (·.name))) ∧
    decl.ValidIndAppAt none (depth + domains.length) result ∧
    ∃ family ∈ decl.types, result.getAppFnArgs.1 = .const family.name levels

/-- The family-free branch of `UniformFieldNormalForm`: the normal form of a field on which the
recursor does not recurse. -/
def VInductDecl.FamilyFreeNormalForm (decl : VInductDecl) (e : VExpr) : Prop :=
  e.SourceConstFree (decl.types.map (·.name))

/-- The recursive branch of `UniformFieldNormalForm`: a telescope over family-free domains ending
in a valid application of one of the families, at the universes `levels`. -/
def VInductDecl.RecursiveNormalForm (decl : VInductDecl) (levels : List VLevel)
    (depth : Nat) (e : VExpr) : Prop :=
  ∃ domains result, e = VExpr.wrapForalls domains result ∧
    (∀ domain ∈ domains, domain.SourceConstFree (decl.types.map (·.name))) ∧
    decl.ValidIndAppAt none (depth + domains.length) result ∧
    ∃ family ∈ decl.types, result.getAppFnArgs.1 = .const family.name levels

/-- The branch of `UniformFieldNormalForm` selected by a recursive/non-recursive
classification: `true` selects `RecursiveNormalForm`, `false` selects
`FamilyFreeNormalForm`. -/
def VInductDecl.ClassifiedFieldNormalForm (decl : VInductDecl) (levels : List VLevel)
    (depth : Nat) : Bool → VExpr → Prop
  | false, e => decl.FamilyFreeNormalForm e
  | true, e => decl.RecursiveNormalForm levels depth e

theorem VInductDecl.ClassifiedFieldNormalForm.uniform {decl : VInductDecl}
    {levels : List VLevel} {depth : Nat} {recursive : Bool} {e : VExpr}
    (H : decl.ClassifiedFieldNormalForm levels depth recursive e) :
    decl.UniformFieldNormalForm levels depth e := by
  cases recursive
  · exact .inl H
  · exact .inr H

theorem VInductDecl.UniformFieldNormalForm.classified {decl : VInductDecl}
    {levels : List VLevel} {depth : Nat} {e : VExpr}
    (H : decl.UniformFieldNormalForm levels depth e) :
    ∃ recursive, decl.ClassifiedFieldNormalForm levels depth recursive e := by
  rcases H with H | H
  · exact ⟨false, H⟩
  · exact ⟨true, H⟩

/-- Shape of one inductive type after normalization: common parameters,
exactly the recorded indices, and the recorded result sort. -/
def VInductDecl.TypeShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (type : VInductiveType) : Prop :=
  ∃ normalized ownParams afterParams indices result exprType,
    env.IsDefEq decl.uvars [] type.type normalized exprType ∧
    normalized.takeForalls decl.nparams = some (ownParams, afterParams) ∧
    afterParams.takeForalls type.numIndices = some (indices, result) ∧
    decl.ParamsDefEq env params ownParams ∧
    env.IsDefEq decl.uvars (indices.reverse ++ ownParams.reverse)
      result (.sort type.resultLevel) (.sort (.succ type.resultLevel))

/-- Raw common-parameter shape of one constructor before normalization.
This is separate from `CtorShape`: normalization may change the visible
forall prefix, while the executable checker compares the source prefix
directly with the mutual header parameters. -/
def VInductDecl.CtorParameterShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (ctor : VConstVal) : Prop :=
  ∃ ownParams tail,
    ctor.type.takeForalls decl.nparams = some (ownParams, tail) ∧
    decl.ParamsDefEq env params ownParams

/-- Raw syntactic shape of a source constructor: exactly the telescope walked
by the executable constructor check.  The constructor type is a syntactic
forall telescope covering the common parameters, whose codomain is a valid
application of the owning family beneath the field binders, at the
declaration's own universe parameters. -/
def VInductDecl.RawCtorShape (decl : VInductDecl) (type : VInductiveType)
    (ctor : VConstVal) : Prop :=
  ∃ doms result,
    ctor.type = VExpr.wrapForalls doms result ∧
    decl.nparams ≤ doms.length ∧
    decl.RawIndAppAt (some type.name) (doms.length - decl.nparams) result ∧
    result.getAppFnArgs.1 = .const type.name (VLevel.params decl.uvars)

/-- Source-facing common-parameter formation retained by both ordinary and
nested declarations.  The family headers identify the shared semantic
parameter telescope, while every source constructor retains its raw
pre-normalization prefix against that same telescope. -/
def VInductDecl.SourceParameterWF (env : VEnv)
    (decl : VInductDecl) : Prop :=
  ∃ params envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    (∀ type ∈ decl.types, decl.TypeShape env params type) ∧
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
      decl.CtorParameterShape envTypes params ctor) ∧
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor

end Lean4Lean
