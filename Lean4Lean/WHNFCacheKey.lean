import Lean.Expr

namespace Lean4Lean
open Lean

/-- Whether `whnf` caches its result for `e`: only applications, constants, lambdas and
projections, whose strict translations cannot already be a dependent function type. Let
bindings and local definitions are normalized directly and are not cached. This keeps the
cache invariant within reach of the translation (section 7.2 of the design notes). -/
def whnfCacheKey : Expr → Bool
  | .app .. | .const .. | .lam .. | .proj .. => true
  | _ => false

end Lean4Lean
