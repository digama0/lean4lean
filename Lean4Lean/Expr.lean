import Lean.Environment

namespace Lean.Expr

def prop : Expr := .sort .zero

def arrow (d b : Expr) : Expr := .forallE `a d b .default

namespace ReplaceImpl

abbrev ReplaceT := StateT Cache

@[inline]
unsafe def cacheT [Monad m] (key : Expr) (result : Expr) : ReplaceT m Expr := do
  modify (·.store key result)
  pure result

@[specialize]
unsafe def replaceUnsafeT [Monad m] (f? : Expr → m (Option Expr)) (e : Expr) : ReplaceT m Expr := do
  let rec @[specialize] visit (e : Expr) := do
    if (← get).hasResultFor e then
      return (← get).getResultFor e
    else match ← f? e with
      | some eNew => cacheT e eNew
      | none      => match e with
        | Expr.forallE _ d b _   => cacheT e <| e.updateForallE! (← visit d) (← visit b)
        | Expr.lam _ d b _       => cacheT e <| e.updateLambdaE! (← visit d) (← visit b)
        | Expr.mdata _ b         => cacheT e <| e.updateMData! (← visit b)
        | Expr.letE _ t v b _    => cacheT e <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | Expr.app f a           => cacheT e <| e.updateApp! (← visit f) (← visit a)
        | Expr.proj _ _ b        => cacheT e <| e.updateProj! (← visit b)
        | e                      => pure e
  visit e

@[inline]
unsafe def replaceUnsafe' [Monad m] (f? : Expr → m (Option Expr)) (e : Expr) : m Expr :=
  (replaceUnsafeT f? e).run' (Cache.new e)

end ReplaceImpl

/- TODO: use withPtrAddr, withPtrEq to avoid unsafe tricks above.
   We also need an invariant at `State` and proofs for the `uget` operations. -/

@[specialize]
def replaceNoCacheT [Monad m] (f? : Expr → m (Option Expr)) (e : Expr) : m Expr := do
  match ← f? e with
  | some eNew => pure eNew
  | none => match e with
    | .forallE _ d b _ =>
      return e.updateForallE! (← replaceNoCacheT f? d) (← replaceNoCacheT f? b)
    | .lam _ d b _ =>
      return e.updateLambdaE! (← replaceNoCacheT f? d) (← replaceNoCacheT f? b)
    | .mdata _ b =>
      return e.updateMData! (← replaceNoCacheT f? b)
    | .letE _ t v b _ =>
      return e.updateLet! (← replaceNoCacheT f? t) (← replaceNoCacheT f? v) (← replaceNoCacheT f? b)
    | .app f a =>
      return e.updateApp! (← replaceNoCacheT f? f) (← replaceNoCacheT f? a)
    | .proj _ _ b =>
      return e.updateProj! (← replaceNoCacheT f? b)
    | e => return e

@[implemented_by ReplaceImpl.replaceUnsafe']
partial def replaceM [Monad m] (f? : Expr → m (Option Expr)) (e : Expr) : m Expr :=
  e.replaceNoCacheT f?

def natZero : Expr := .const ``Nat.zero []
def natSucc : Expr := .const ``Nat.succ []

def isConstructorApp?' (env : Environment) (e : Expr) : Option Name := do
  let .const fn _ := e.getAppFn | none
  let .ctorInfo _ ← env.find? fn | none
  return fn

def natLitToConstructor : Nat → Expr
  | 0 => natZero
  | n+1 => .app natSucc (.lit (.natVal n))

def strLitToConstructor (s : String) : Expr :=
  let char := .const ``Char []
  let listNil := .app (.const ``List.nil [.zero]) char
  let listCons := .app (.const ``List.cons [.zero]) char
  let stringMk := .const ``String.mk []
  let charOfNat := .const ``Char.ofNat []
  .app stringMk <| s.foldr (init := listNil) fun c e =>
    .app (.app listCons <| .app charOfNat (.lit (.natVal c.toNat))) e

end Expr

def Literal.toConstructor : Literal → Expr
  | .natVal n => .natLitToConstructor n
  | .strVal s => .strLitToConstructor s
