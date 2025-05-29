import Lean.Expr
import Lean.LocalContext

namespace Lean
namespace Expr

def cheapBetaReduce (e : Expr) : Expr := Id.run do
  if !e.isApp then return e
  let fn := e.getAppFn
  if !fn.isLambda then return e
  let args := e.getAppArgs
  let rec cont i fn :=
    if !fn.hasLooseBVars then
      mkAppRange fn i args.size args
    else if let .bvar n := fn then
      assert! n < i
      mkAppRange args[i - n - 1]! i args.size args
    else
      e
  let rec loop i fn : Id Expr :=
    if i < args.size then
      match fn with
      | .lam _ _ body .. => loop (i + 1) body
      | _ => cont i fn
    else cont i fn
  loop 0 fn

/--
  Lift loose bound variables `>= s` in `e` by `d`. -/
@[implemented_by liftLooseBVars]
def liftLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  match e with
  | .bvar i => .bvar (if i < s then i else i + d)
  | .mdata m e => .mdata m (liftLooseBVars' e s d)
  | .proj n i e => .proj n i (liftLooseBVars' e s d)
  | .app f a => .app (liftLooseBVars' f s d) (liftLooseBVars' a s d)
  | .lam n t b bi => .lam n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (liftLooseBVars' t s d) (liftLooseBVars' v s d) (liftLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/--
Lower the loose bound variables `>= s` in `e` by `d`.
That is, a loose bound variable `bvar i` with `i >= s` is mapped to `bvar (i-d)`.

Remark: if `s < d`, then the result is `e`.
-/
@[implemented_by lowerLooseBVars]
def lowerLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  if s < d then e else
  match e with
  | .bvar i => .bvar (if i < s then i else i - d)
  | .mdata m e => .mdata m (lowerLooseBVars' e s d)
  | .proj n i e => .proj n i (lowerLooseBVars' e s d)
  | .app f a => .app (lowerLooseBVars' f s d) (lowerLooseBVars' a s d)
  | .lam n t b bi => .lam n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (lowerLooseBVars' t s d) (lowerLooseBVars' v s d) (lowerLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/--
Instantiates loose bound variable `0` in `e` using the expression `subst`,
where in particular a loose `Expr.bvar i` at binding depth `d` is instantiated with `subst` if `i = d`,
and otherwise it is replaced with `Expr.bvar (i - 1)`; non-loose bound variables are not touched.
-/
@[implemented_by instantiate1]
def instantiate1' (e : @& Expr) (subst : @& Expr) : Expr :=
  go e 0
where
  go : Expr → Nat → Expr
  | e@(.bvar i), d =>
    if i < d then e else if i = d then subst.liftLooseBVars' 0 d else .bvar (i - 1)
  | .mdata m e, d => .mdata m (go e d)
  | .proj s i e, d => .proj s i (go e d)
  | .app f a, d => .app (go f d) (go a d)
  | .lam n t b bi, d => .lam n (go t d) (go b (d+1)) bi
  | .forallE n t b bi, d => .forallE n (go t d) (go b (d+1)) bi
  | .letE n t v b bi, d => .letE n (go t d) (go v d) (go b (d+1)) bi
  | e@(.const ..), _
  | e@(.sort _), _
  | e@(.fvar _), _
  | e@(.mvar _), _
  | e@(.lit _), _ => e

@[simp] def instantiateList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => instantiateList (instantiate1'.go a e k) as k

/--
Instantiates the loose bound variables in `e` using the `subst` array,
where a loose `Expr.bvar i` at "binding depth" `d` is instantiated with `subst[i - d]` if `0 <= i - d < subst.size`,
and otherwise it is replaced with `Expr.bvar (i - subst.size)`; non-loose bound variables are not touched.
-/
@[implemented_by instantiate]
def instantiate' (e : @& Expr) (subst : @& Array Expr) : Expr :=
  instantiateList e subst.toList

@[implemented_by instantiateRev]
def instantiateRev' (e : @& Expr) (subst : @& Array Expr) : Expr :=
  e.instantiate' subst.reverse

@[implemented_by instantiateRange]
def instantiateRange' (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr :=
  e.instantiate' (subst.extract beginIdx endIdx)

@[implemented_by instantiateRevRange]
def instantiateRevRange' (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr :=
  e.instantiateRev' (subst.extract beginIdx endIdx)

def abstractFVar (v : FVarId) : Expr → (k :_:= 0) → Expr
  | .bvar i, d => .bvar (if i < d then i else i + 1)
  | e@(.fvar v'), d => if v == v' then .bvar d else e
  | .mdata m e, d => .mdata m (abstractFVar v e d)
  | .proj s i e, d => .proj s i (abstractFVar v e d)
  | .app f a, d => .app (abstractFVar v f d) (abstractFVar v a d)
  | .lam n t b bi, d => .lam n (abstractFVar v t d) (abstractFVar v b (d+1)) bi
  | .forallE n t b bi, d => .forallE n (abstractFVar v t d) (abstractFVar v b (d+1)) bi
  | .letE n t val b bi, d =>
    .letE n (abstractFVar v t d) (abstractFVar v val d) (abstractFVar v b (d+1)) bi
  | e@(.const ..), _
  | e@(.sort _), _
  | e@(.mvar _), _
  | e@(.lit _), _ => e

-- this can be defined but it's not used in the kernel
opaque abstract1Other : Expr → Expr → (k :_:= 0) → Expr

def abstract1 (e : Expr) : Expr → (k :_:= 0) → Expr
  | .fvar a, k => abstractFVar a e k
  | a, k => abstract1Other a e k

@[simp] def abstractList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => abstractList (abstract1 e a k) as k

@[simp] def abstractRevList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => abstract1 (abstractRevList e as k) a k

/-- Replace free (or meta) variables `xs` with loose bound variables,
with `xs` ordered from outermost to innermost de Bruijn index.

For example, `e := f x y` with `xs := #[x, y]` goes to `f #1 #0`,
whereas `e := f x y` with `xs := #[y, x]` goes to `f #0 #1`. -/
@[implemented_by abstract]
def abstract' (e : @& Expr) (xs : @& Array Expr) : Expr :=
  e.abstractList xs.toList

/-- Similar to `abstract`, but consider only the first `min n xs.size` entries in `xs`. -/
@[implemented_by abstractRange]
def abstractRange' (e : @& Expr) (n : @& Nat) (xs : @& Array Expr) : Expr :=
  e.abstract' (xs.extract 0 n)

@[implemented_by hasLooseBVar]
def hasLooseBVar' : (e : @& Expr) → (bvarIdx : @& Nat) → Bool
  | .bvar i, d => i = d
  | .mdata _ e, d
  | .proj _ _ e, d => hasLooseBVar' e d
  | .app f a, d => hasLooseBVar' f d || hasLooseBVar' a d
  | .lam _ t b _, d
  | .forallE _ t b _, d => hasLooseBVar' t d || hasLooseBVar' b (d+1)
  | .letE _ t v b _, d => hasLooseBVar' t d || hasLooseBVar' v d || hasLooseBVar' b (d+1)
  | .const .., _
  | .sort _, _
  | .fvar _, _
  | .mvar _, _
  | .lit _, _ => false

end Expr

@[inline] def LocalContext.mkBinding' (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  let b := b.abstract' xs
  xs.size.foldRev (init := b) fun i _ b =>
    let x := xs[i]
    match lctx.findFVar? x with
    | some (.cdecl _ _ n ty bi _)  =>
      let ty := ty.abstractRange' i xs
      if isLambda then
        Lean.mkLambda n bi ty b
      else
        Lean.mkForall n bi ty b
    | some (.ldecl _ _ n ty val nonDep _) =>
      if b.hasLooseBVar' 0 then
        let ty  := ty.abstractRange' i xs
        let val := val.abstractRange' i xs
        mkLet n ty val b nonDep
      else
        b.lowerLooseBVars' 1 1
    | none => panic! "unknown free variable"

/-- Creates the expression `fun x₁ .. xₙ => b` for free variables `xs = #[x₁, .., xₙ]`,
suitably abstracting `b` and the types for each of the `xᵢ`. -/
def LocalContext.mkLambda' (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  mkBinding' true lctx xs b

/-- Creates the expression `(x₁:α₁) → .. → (xₙ:αₙ) → b` for free variables `xs = #[x₁, .., xₙ]`,
suitably abstracting `b` and the types for each of the `xᵢ`, `αᵢ`. -/
def LocalContext.mkForall' (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  mkBinding' false lctx xs b
