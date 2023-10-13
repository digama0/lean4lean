import Lean.Expr
import Lean.Util.MonadCache

/-!
This is the same as `Expr.forEach` but it uses `StateT` instead of `StateRefT` to avoid opaques.
-/
namespace Lean
variable {ω : Type} {m : Type → Type} [Monad m]

namespace ForEachExprV
def visit (g : Expr → m Bool) (e : Expr) : MonadStateCacheT Expr Unit m Unit :=
  checkCache e fun _ => do
    if (← g e) then
      match e with
      | Expr.forallE _ d b _   => do visit g d; visit g b
      | Expr.lam _ d b _       => do visit g d; visit g b
      | Expr.letE _ t v b _    => do visit g t; visit g v; visit g b
      | Expr.app f a           => do visit g f; visit g a
      | Expr.mdata _ b         => visit g b
      | Expr.proj _ _ b        => visit g b
      | _                      => pure ()

end ForEachExprV

/-- Apply `f` to each sub-expression of `e`. If `f t` returns false, then t's children are not visited. -/
@[inline] def Expr.forEachV' (e : Expr) (f : Expr → m Bool) : m Unit :=
  (ForEachExprV.visit f e).run

@[inline] def Expr.forEachV (e : Expr) (f : Expr → m Unit) : m Unit :=
  e.forEachV' fun e => do f e; pure true
