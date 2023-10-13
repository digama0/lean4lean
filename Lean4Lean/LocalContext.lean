import Lean.LocalContext

namespace Lean

class MonadLocalNameGenerator (m : Type u → Type v) where
  withFreshId : (Name → m α) → m α
export MonadLocalNameGenerator (withFreshId)

instance [MonadLocalNameGenerator m] : MonadLocalNameGenerator (ReaderT ρ m) where
  withFreshId f c := withFreshId (f · c)

@[inline] def withLocalDecl [Monad m] [MonadLocalNameGenerator m] [MonadWithReaderOf LocalContext m]
    (name : Name) (ty : Expr) (bi : BinderInfo) (k : Expr → m α) : m α :=
  withFreshId fun id => do
  withReader (·.mkLocalDecl ⟨id⟩ name ty bi) <| k <| .fvar ⟨id⟩

@[inline] def withLetDecl [Monad m] [MonadLocalNameGenerator m] [MonadWithReaderOf LocalContext m]
    (name : Name) (ty val : Expr) (k : Expr → m α) : m α :=
  withFreshId fun id => do
  withReader (·.mkLetDecl ⟨id⟩ name ty val) <| k <| .fvar ⟨id⟩
