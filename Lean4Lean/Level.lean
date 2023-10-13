import Lean.Level
import Lean4Lean.List

namespace Lean.Level

def forEach [Monad m] (l : Level) (f : Level → m Bool) : m Unit := do
  if !(← f l) then return
  match l with
  | .succ l => l.forEach f
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.forEach f; l₂.forEach f
  | .zero | .param .. | .mvar .. => pure ()

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

mutual -- FIXME: partial

partial def isGECore (l1 l2 : Level) : Bool := Id.run do
  if l1 == l2 || l2.isZero then return true
  if let .max a2 b2 := l2 then return l1.isGE a2 && l2.isGE b2
  if let .max a1 b1 := l1 then if a1.isGE l2 || b1.isGE l2 then return true
  if let .imax a2 b2 := l2 then return l1.isGE a2 && l2.isGE b2
  if let .imax _ b1 := l1 then return b1.isGE l2
  let n1 := l1.getOffset; let l1' := l1.getLevelOffset
  let n2 := l2.getOffset; let l2' := l2.getLevelOffset
  if l1' == l2' || l2'.isZero then return n1 ≥ n2
  n1 == n2 && n1 > 0 && isGE l1' l2'

partial def isGE (l1 l2 : Level) : Bool := isGECore l1.normalize l2.normalize

end
