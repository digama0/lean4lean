import Lean.Environment

namespace Lean
namespace Expr

def prop : Expr := .sort .zero

def arrow (d b : Expr) : Expr := .forallE `a d b .default

def lam0 (ty e : Expr) : Expr := .lam `_ ty e default

/-- Transparent, root-first expression search used by the verified checker.
Unlike Lean's opaque `Expr.find?`, this exposes its traversal to proofs. -/
def findAny (p : Expr → Bool) : Expr → Bool
  | e@(.app fn arg) => p e || findAny p fn || findAny p arg
  | e@(.lam _ ty body _) => p e || findAny p ty || findAny p body
  | e@(.forallE _ ty body _) => p e || findAny p ty || findAny p body
  | e@(.letE _ ty value body _) =>
    p e || findAny p ty || findAny p value || findAny p body
  | e@(.mdata _ inner) => p e || findAny p inner
  | e@(.proj _ _ inner) => p e || findAny p inner
  | e => p e

/-- Transparent reference implementation of the outer annotation erasure used
by the verified checker. Like `Expr.consumeTypeAnnotations` (and the C++
`consume_type_annotations`), it strips `optParam α d`, `autoParam α s`,
`outParam α` and `semiOutParam α` to `α`, repeatedly; unlike them, it strips an
application only if `ok` accepts its head. The inductive checker passes
`Kernel.Environment.isTypeAnnotationWrapper env`, so a wrapper is stripped only
when the environment declares it as the prelude's identity-like definition. -/
def consumeTypeAnnotationsVerified (ok : Name → Bool) : Expr → Expr
  | e@(.app (.app (.const name _) type) _) =>
    if (name == ``optParam || name == ``autoParam) && ok name then
      consumeTypeAnnotationsVerified ok type
    else e
  | e@(.app (.const name _) type) =>
    if (name == ``outParam || name == ``semiOutParam) && ok name then
      consumeTypeAnnotationsVerified ok type
    else e
  | e => e

end Expr

namespace Kernel.Environment

/-- The prelude's type-annotation wrappers, as stored by the kernel:

* `@[reducible] def optParam.{u} (α : Sort u) (default : α) : Sort u := α`,
* `def autoParam.{u} (α : Sort u) (tactic : Lean.Syntax) : Sort u := α`,
* `@[reducible] def outParam.{u} (α : Sort u) : Sort u := α`, and `semiOutParam` likewise.

`isTypeAnnotationWrapper env name` holds if `env` declares `name` as one of these: a safe
definition whose universe parameters, type and value are exactly the prelude's (binder names
and binder infos included). The value is also matched structurally, since its shape
`fun α _ => α` is what makes stripping an application sound. -/
def isTypeAnnotationWrapper (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.defnInfo v) =>
    let u := Level.param `u
    let s := Expr.sort u
    v.safety == .safe && v.levelParams == [`u] &&
    if name == ``optParam || name == ``autoParam then
      let (argName, argType) := if name == ``optParam then (`default, Expr.bvar 0)
        else (`tactic, Expr.const ``Lean.Syntax [])
      match v.value with
      | .lam _ _ (.lam _ _ (.bvar 1) _) _ =>
        v.type.equal (.forallE `α s (.forallE argName argType s .default) .default) &&
        v.value.equal (.lam `α s (.lam argName argType (.bvar 1) .default) .default)
      | _ => false
    else if name == ``outParam || name == ``semiOutParam then
      match v.value with
      | .lam _ _ (.bvar 0) _ =>
        v.type.equal (.forallE `α s s .default) &&
        v.value.equal (.lam `α s (.bvar 0) .default)
      | _ => false
    else false
  | _ => false

end Kernel.Environment

namespace Expr

namespace ReplaceImpl

unsafe abbrev ReplaceT := StateT (PtrMap Expr Expr)

@[inline]
unsafe def cacheT [Monad m] (key : Expr) (result : Expr) : ReplaceT m Expr := do
  modify (·.insert key result)
  pure result

@[specialize]
unsafe def replaceUnsafeT [Monad m] (f? : Expr → m (Option Expr)) (e : Expr) : ReplaceT m Expr := do
  let rec @[specialize] visit (e : Expr) := do
    if let some result := (← get).find? e then
      return result
    match ← f? e with
    | some eNew => cacheT e eNew
    | none      => match e with
      | Expr.forallE _ d b _   => cacheT e <| e.updateForallE! (← visit d) (← visit b)
      | Expr.lam _ d b _       => cacheT e <| e.updateLambdaE! (← visit d) (← visit b)
      | Expr.mdata _ b         => cacheT e <| e.updateMData! (← visit b)
      | Expr.letE _ t v b nd   => cacheT e <| e.updateLet! (← visit t) (← visit v) (← visit b) nd
      | Expr.app f a           => cacheT e <| e.updateApp! (← visit f) (← visit a)
      | Expr.proj _ _ b        => cacheT e <| e.updateProj! (← visit b)
      | e                      => pure e
  visit e

@[inline]
unsafe def replaceUnsafe' [Monad m] (f? : Expr → m (Option Expr)) (e : Expr) : m Expr :=
  (replaceUnsafeT f? e).run' mkPtrMap

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
    | .letE _ t v b nd =>
      return e.updateLet!
        (← replaceNoCacheT f? t) (← replaceNoCacheT f? v) (← replaceNoCacheT f? b) nd
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

def isConstructorApp?' (env : Kernel.Environment) (e : Expr) : Option Name := do
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
  let stringMk := .const ``String.ofList []
  let charOfNat := .const ``Char.ofNat []
  .app stringMk <| s.toList.foldr (init := listNil) fun c e => -- TODO: use String.foldr
    .app (.app listCons <| .app charOfNat (.lit (.natVal c.toNat))) e

end Expr

namespace Literal

def toConstructor : Literal → Expr
  | .natVal n => .natLitToConstructor n
  | .strVal s => .strLitToConstructor s

/-- Return the type of a literal value. -/
def typeName : Literal → Name
  | .natVal _ => ``Nat
  | .strVal _ => ``String

end Literal
