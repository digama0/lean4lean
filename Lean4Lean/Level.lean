import Lean.Level
import Lean4Lean.List

namespace Lean.Level

def forEach [Monad m] (l : Level) (f : Level → m Bool) : m Unit := do
  if !(← f l) then return
  match l with
  | .succ l => l.forEach f
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.forEach f; l₂.forEach f
  | .zero | .param .. | .mvar .. => pure ()

/--
Returns `some n` if level parameter `n` appears in `l` and `n ∉ ps`.
-/
def getUndefParam (l : Level) (ps : List Name) : Option Name := Id.run do
  (·.2) <$> StateT.run (s := none) do
    l.forEach fun l => do
      if !l.hasParam || (← get).isSome then
        return false
      if let .param n := l then
        if n ∉ ps then
          set (some n)
      return true

def isEquivList : List Level → List Level → Bool := List.all2 isEquiv

def geq' (u v : Level) : Bool := -- pending lean4#2689
  go u.normalize v.normalize
where
  go (u v : Level) : Bool :=
    u == v ||
    let k := fun () =>
      match v with
      | imax v₁ v₂ => go u v₁ && go u v₂
      | _          =>
        let v' := v.getLevelOffset
        (u.getLevelOffset == v' || v'.isZero)
        && u.getOffset ≥ v.getOffset
    match u, v with
    | _,          zero      => true
    | u,          max v₁ v₂ => go u v₁ && go u v₂
    | max u₁ u₂,  v         => go u₁ v || go u₂ v || k ()
    | imax _  u₂, v         => go u₂ v
    | succ u,     succ v    => go u v
    | _,          _         => k ()
  termination_by (u, v)
