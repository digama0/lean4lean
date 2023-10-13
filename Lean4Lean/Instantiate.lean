import Lean.Expr

namespace Lean

def Expr.cheapBetaReduce (e : Expr) : Expr := Id.run do
  if !e.isApp then return e
  let fn := e.getAppFn
  if !fn.isLambda then return e
  let args := e.getAppArgs
  let cont i e :=
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
      | .lam _ _ dom .. => loop (i + 1) dom
      | _ => cont i fn
    else cont i fn
  loop 0 fn
