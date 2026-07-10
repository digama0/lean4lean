import Lean.Expr
import Lean.LocalContext
import Lean.Util.InstantiateLevelParams
import Lean.Declaration

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
  let rec loop i fn :=
    if i < args.size then
      match fn with
      | .lam _ _ body .. => loop (i + 1) body
      | _ => cont i fn
    else cont i fn
  return loop 0 fn

end Expr

/-!
Copies of `Lean.Level`'s `mkLevelMaxCore` / `mkLevelIMaxCore` and
`Lean.Expr.instantiateLevelParams` chain, patched to match the C++ kernel's
`mk_max` / `mk_imax` (`src/kernel/level.cpp:81`, `:112`) exactly.

The stdlib versions diverge on two cases:
  * stdlib's `subsumes` includes `v.isExplicit && u.getOffset ≥ v.getOffset`,
    which C++ lacks; this causes e.g. `max (succ u_1) 1 → succ u_1` in Lean but
    `max (succ u_1) 1` (unchanged) in C++.
  * stdlib's `mkLevelIMaxCore` lacks the `imax 1 u = u` case that C++ has.

We keep the L4L copies so lean4lean-side substitution paths (`inferConstant`,
`unfoldDefinitionCore`, `Inductive.Reduce`, ...) produce the same `Expr` hashes
as C++ during type inference.
-/

/-- Copy of `Lean.mkLevelMaxCore` with the `v.isExplicit && offset ≥ offset` rule
    removed to match C++ `mk_max`. -/
@[inline] def mkLevelMaxCoreCpp (u v : Level) (elseK : Unit → Level) : Level :=
  let subsumes : Level → Level → Bool := fun u v =>
    match u with
    | Level.max u₁ u₂ => v == u₁ || v == u₂
    | _ => false
  if u == v then u
  else if u.isZero then v
  else if v.isZero then u
  else if subsumes u v then u
  else if subsumes v u then v
  else if u.getLevelOffset == v.getLevelOffset then
    if u.getOffset ≥ v.getOffset then u else v
  else
    elseK ()

/-- Copy of `Lean.mkLevelMax'` using `mkLevelMaxCoreCpp`. -/
def mkLevelMaxCpp (u v : Level) : Level := mkLevelMaxCoreCpp u v fun _ => mkLevelMax u v

/-- Copy of `Lean.mkLevelIMaxCore` with the `imax 1 u = u` case added to match
    C++ `mk_imax`. -/
@[inline] def mkLevelIMaxCoreCpp (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMaxCpp u v
  else if v.isZero then v
  else if u.isZero || u == .succ .zero then v  -- extra: imax 1 u = u
  else if u == v then u
  else elseK ()

/-- Copy of `Lean.mkLevelIMax'` using `mkLevelIMaxCoreCpp`. -/
def mkLevelIMaxCpp (u v : Level) : Level := mkLevelIMaxCoreCpp u v fun _ => mkLevelIMax u v

/-- Copy of `Lean.Level.substParams` using `mkLevelMaxCpp`/`mkLevelIMaxCpp`. -/
@[specialize] def Level.substParamsCpp (u : Level) (s : Name → Option Level) : Level :=
  go u
where
  go (u : Level) : Level :=
    match u with
    | .zero       => u
    | .succ v     => if u.hasParam then .succ (go v) else u
    | .max v₁ v₂  => if u.hasParam then mkLevelMaxCpp  (go v₁) (go v₂) else u
    | .imax v₁ v₂ => if u.hasParam then mkLevelIMaxCpp (go v₁) (go v₂) else u
    | .param n    => match s n with
      | some u' => u'
      | none    => u
    | u => u

/-- Copy of `Lean.Expr.instantiateLevelParamsCore` using our patched `substParamsCpp`. -/
@[specialize] def Expr.instantiateLevelParamsCoreCpp (s : Name → Option Level) (e : Expr) : Expr :=
  e.replace replaceFn
where
  @[specialize] replaceFn (e : Expr) : Option Expr :=
    if !e.hasLevelParam then e else match e with
    | .const _ us => e.updateConst! (us.map fun u => Level.substParamsCpp u s)
    | .sort u     => e.updateSort!  (Level.substParamsCpp u s)
    | _ => none

/-- Copy of `Lean.Expr.instantiateLevelParams` using our patched core. -/
def Expr.instantiateLevelParamsCpp (e : Expr) (paramNames : List Name) (lvls : List Level) : Expr :=
  if paramNames.isEmpty || lvls.isEmpty then e else
    let rec go : List Name → List Level → Name → Option Level
      | p::ps, u::us, p' => if p == p' then some u else go ps us p'
      | _,     _,     _  => none
    e.instantiateLevelParamsCoreCpp (go paramNames lvls)

/-- Analog of `ConstantInfo.instantiateTypeLevelParams` using C++-matching rules. -/
def ConstantInfo.instantiateTypeLevelParamsCpp (info : ConstantInfo) (ls : List Level) : Expr :=
  Expr.instantiateLevelParamsCpp info.type info.levelParams ls

/-- Analog of `ConstantInfo.instantiateValueLevelParams!` using C++-matching rules. -/
def ConstantInfo.instantiateValueLevelParams!Cpp (info : ConstantInfo) (ls : List Level) : Expr :=
  Expr.instantiateLevelParamsCpp info.value?.get! info.levelParams ls
