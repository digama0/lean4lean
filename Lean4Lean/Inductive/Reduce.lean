import Lean.Structure
import Lean4Lean.Expr

namespace Lean

section
variable [Monad m] (env : Environment)
    (whnf : Expr → m Expr) (inferType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool)

def getFirstCtor (dName : Name) : Option Name := do
  let some (.inductInfo info) := env.find? dName | none
  info.ctors.head?

def mkNullaryCtor (type : Expr) (nparams : Nat) : Option Expr :=
  type.withApp fun d args => do
  let .const dName ls := d | none
  let name ← getFirstCtor env dName
  return mkAppRange (.const name ls) 0 nparams args

/--
When `e` has the type of a K-like inductive, converts it into a constructor
application.

For instance if we have `e : Eq a a`, it is converted into `Eq.refl a` (which
it is definitionally equal to by proof irrelevance). Note that the indices of
`e`'s type must match those of the constructor application (for instance,
`e : Eq a b` cannot be converted if `a` and `b` are not defeq).
-/
def toCtorWhenK (rval : RecursorVal) (e : Expr) : m Expr := do
  assert! rval.k
  let appType ← whnf (← inferType e)
  let .const appTypeI _ := appType.getAppFn | return e
  if appTypeI != rval.getInduct then return e
  if appType.hasExprMVar then
    let appTypeArgs := appType.getAppArgs
    for h : i in [rval.numParams:appTypeArgs.size] do
      if (appTypeArgs[i]'h.2).hasExprMVar then return e
  let some newCtorApp := mkNullaryCtor env appType rval.numParams | return e
  -- check that the indices of types of `e` and `newCtorApp` match
  unless ← isDefEq appType (← inferType newCtorApp) do return e
  return newCtorApp

def expandEtaStruct (eType e : Expr) : Expr :=
  eType.withApp fun I args => Id.run do
  let .const I ls := I | return e
  let some ctor := getFirstCtor env I | return e
  let some (.ctorInfo info) := env.find? ctor | unreachable!
  let mut result := mkAppRange (.const ctor ls) 0 info.numParams args
  for i in [:info.numFields] do
    result := .app result (.proj I i e)
  pure result

/--
When `e` is of struct type, converts it into a constructor application using
projections.

For instance if we have `e : String`, it is converted into
`String.mk (String.data e)` (which is definitionally equal to `e` by struct
eta).
-/
def toCtorWhenStruct (inductName : Name) (e : Expr) : m Expr := do
  if !isStructureLike env inductName || (e.isConstructorApp?' env).isSome then
    return e
  let eType ← whnf (← inferType e)
  if !eType.getAppFn.isConstOf inductName then return e
  if (← whnf (← inferType eType)) == .prop then return e
  return expandEtaStruct env eType e

def getRecRuleFor (rval : RecursorVal) (major : Expr) : Option RecursorRule := do
  let .const fn _ := major.getAppFn | none
  rval.rules.find? (·.ctor == fn)

/--
Performs recursor reduction on `e` (returning `none` if not applicable).

For recursor reduction to occur, `e` must be a recursor application where the
major premise is either a complete constructor application or of a K- or
structure-like inductive type (in which case it is converted into an equivalent
constructor application). The reduction is done by applying the
`RecursorRule.rhs` associated with the constructor to the parameters from the
recursor application and the fields of the constructor application.
-/
def inductiveReduceRec [Monad m] (env : Environment) (e : Expr)
    (whnf : Expr → m Expr) (inferType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool) :
    m (Option Expr) := do
  let .const recFn ls := e.getAppFn | return none
  let some (.recInfo info) := env.find? recFn | return none
  let recArgs := e.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major := recArgs[majorIdx]? | return none
  let mut major := major
  if info.k then
    major ← toCtorWhenK env whnf inferType isDefEq info major
  match ← whnf major with
  | .lit l => major := l.toConstructor
  | e => major ← toCtorWhenStruct env whnf inferType info.getInduct e
  let some rule := getRecRuleFor info major | return none
  let majorArgs := major.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  -- get parameters from recursor application (recursor rules don't need the indices,
  -- as these are determined by the constructor and its parameters/fields)
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx recArgs
  -- get fields from constructor application
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs
  if majorIdx + 1 < recArgs.size then
    rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
  return rhs

end
