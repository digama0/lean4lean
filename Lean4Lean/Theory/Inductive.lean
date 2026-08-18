import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

/-- Checkable well-formedness of an inductive declaration: every type former,
constructor, and recursor is well-typed under the declaration's universe
parameters, and every recursor rule's reduct template is closed. Does not yet
enforce strict positivity, universe constraints, or the recursor/rule shape. -/
structure VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop where
  types_wf : ∀ t ∈ decl.types, env.IsType decl.uvars [] t.type
  ctors_wf : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env.IsType decl.uvars [] c.type
  recs_wf : ∀ r ∈ decl.recs, env.IsType r.uvars [] r.type
  rules_closed : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.rhs.Closed

/-- Register recursor rule `ru` (of recursor `r`) as an ι rule: redex `r`'s spine
applied to `ru.ctor`'s spine, reduct `SimplePattern.iotaRHS`. Fails if `ru.rhs`
is not closed. -/
def VEnv.addRecRule (env : VEnv) (r : VRecursor) (ru : VRecRule) : Option VEnv :=
  if h : ru.rhs.Closed then
    some <| env.addPat
      (SimplePattern.iota r.name (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        ru.ctor (r.numParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.nfields ru.rhs h, .true)
  else none

/-- Extend `env` with the type formers, constructors, and recursors of `decl`
(as constants) and its ι-reduction rules (as `pats`), or `none` on a name clash
or a non-closed rule reduct. -/
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := do
  let env ← decl.types.foldlM (init := env) fun e t =>
    e.addConst t.name t.toVConstVal.toVConstant
  let env ← decl.types.foldlM (init := env) fun e t =>
    t.ctors.foldlM (init := e) fun e c => e.addConst c.name c.toVConstant
  let env ← decl.recs.foldlM (init := env) fun e r =>
    e.addConst r.name r.toVConstVal.toVConstant
  decl.recs.foldlM (init := env) fun e r =>
    r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru
