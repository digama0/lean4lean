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

def toCtorWhenK (rval : RecursorVal) (e : Expr) : m Expr := do
  assert! rval.k
  let appType ← whnf (← inferType e)
  let .const appTypeI _ := appType.getAppFn | return e
  if appTypeI != rval.getMajorInduct then return e
  if appType.hasExprMVar then
    let appTypeArgs := appType.getAppArgs
    for h : i in [rval.numParams:appTypeArgs.size] do
      if (appTypeArgs[i]'h.2).hasExprMVar then return e
  let some newCtorApp := mkNullaryCtor env appType rval.numParams | return e
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
  | e => major ← toCtorWhenStruct env whnf inferType info.getMajorInduct e
  let some rule := getRecRuleFor info major | return none
  let majorArgs := major.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx recArgs
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs
  if majorIdx + 1 < recArgs.size then
    rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
  return rhs

end
