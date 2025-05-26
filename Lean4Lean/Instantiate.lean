import Lean.Expr

namespace Lean
namespace Expr

def cheapBetaReduce (e : Expr) : Expr := Id.run do
  if !e.isApp then return e
  let fn := e.getAppFn
  if !fn.isLambda then return e
  let args := e.getAppArgs
  let cont i fn :=
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

/--
Instantiates the loose bound variables in `e` using the `subst` array,
where a loose `Expr.bvar i` at "binding depth" `d` is instantiated with `subst[i - d]` if `0 <= i - d < subst.size`,
and otherwise it is replaced with `Expr.bvar (i - subst.size)`; non-loose bound variables are not touched.
-/
@[implemented_by instantiate]
def instantiate' (e : @& Expr) (subst : @& Array Expr) : Expr :=
  go e subst.toList
where
  go : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => go (e.instantiate1' a) as

@[implemented_by instantiateRev]
def instantiateRev' (e : @& Expr) (subst : @& Array Expr) : Expr :=
  e.instantiate' subst.reverse

@[implemented_by instantiateRange]
def instantiateRange' (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr :=
  e.instantiate' (subst.extract beginIdx endIdx)

@[implemented_by instantiateRevRange]
def instantiateRevRange' (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr :=
  e.instantiateRev' (subst.extract beginIdx endIdx)

theorem instantiateRev_push {e : Expr} {subst a} :
    instantiateRev' e (subst.push a) = instantiateRev' (e.instantiate1' a) subst := by
  let ⟨subst⟩ := subst; simp [instantiateRev', instantiate', instantiate'.go]
