import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

/-!
# Adding inductive declarations to the model environment

`VEnv.addInduct` registers, for a `VInductDecl`, its inductive type formers,
its constructors, and its recursors as constants, and installs one ι-reduction
rule (`VEnv.addPat`) per recursor rule. The ι rule's redex is a recursor spine
applied to a constructor spine (`SimplePattern.iota`) and its reduct is built by
`SimplePattern.iotaRHS`, mirroring the executable kernel's `inductiveReduceRec`.
-/

/-- Well-formedness of an inductive declaration. Records the checkable
conditions: every type former, constructor, and recursor is well-typed under
the declaration's universe parameters, and every recursor rule's reduct
template is closed (needed to install it as a schematic rule).

Note: a fully faithful predicate would additionally enforce strict positivity
of constructors, the universe constraints `imax(ℓ',ℓ) ≤ ℓ`, and the
large-elimination conditions (Carneiro, *The Type Theory of Lean*, §2.6.1–2.6.2),
and would pin the recursor/rule *shape* to the one `addInduct` reduces with.
Those are not yet enforced here; strengthening this predicate is future work and
does not affect the correctness of the ι *rule statement* installed below. -/
structure VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop where
  types_wf : ∀ t ∈ decl.types, env.IsType decl.uvars [] t.type
  ctors_wf : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env.IsType decl.uvars [] c.type
  recs_wf : ∀ r ∈ decl.recs, env.IsType r.uvars [] r.type
  rules_closed : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ru.rhs.Closed

/-- Register a single recursor rule `ru` (of recursor `r`) as a schematic ι
rule: its redex pattern is `r`'s spine applied to `ru.ctor`'s spine, and its
reduct is `SimplePattern.iotaRHS`. Fails only if `ru.rhs` is not closed. -/
def VEnv.addRecRule (env : VEnv) (r : VRecursor) (ru : VRecRule) : Option VEnv :=
  if h : ru.rhs.Closed then
    some <| env.addPat
      (SimplePattern.iota r.name (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        ru.ctor (r.numParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.nfields ru.rhs h, .true)
  else none

/-- Extend `env` with the type formers, constructors, and recursors of `decl`
(as constants) and its ι-reduction rules (as `pats`). Returns `none` if any
name clashes with an existing constant or any rule reduct is not closed. -/
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := do
  let env ← decl.types.foldlM (init := env) fun e t =>
    e.addConst t.name t.toVConstVal.toVConstant
  let env ← decl.types.foldlM (init := env) fun e t =>
    t.ctors.foldlM (init := e) fun e c => e.addConst c.name c.toVConstant
  let env ← decl.recs.foldlM (init := env) fun e r =>
    e.addConst r.name r.toVConstVal.toVConstant
  decl.recs.foldlM (init := env) fun e r =>
    r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru
