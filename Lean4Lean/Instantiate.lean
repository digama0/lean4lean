import Lean.Expr
import Lean.LocalContext
import Lean.Util.InstantiateLevelParams

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
