import Batteries.Data.UnionFind.Basic

namespace Lean

abbrev EquivManager.NodeRef := Nat
open EquivManager

structure EquivManager where
  uf : Batteries.UnionFind := {}
  toNodeMap : ExprMap NodeRef := {}

namespace EquivManager

def find (n : NodeRef) : StateM EquivManager NodeRef := fun m =>
  if h : n < m.uf.size then
    let ⟨uf, root, _⟩ := m.uf.find ⟨n, h⟩
    (root, { m with uf })
  else (n, m)

def merge (m : EquivManager) (n1 n2 : NodeRef) : EquivManager :=
  if h1 : n1 < m.uf.size then
    if h2 : n2 < m.uf.size then
      { m with uf := m.uf.union ⟨n1, h1⟩ ⟨n2, h2⟩ }
    else m
  else m

def toNode (e : Expr) : StateM EquivManager NodeRef := fun m => do
  if let some r := m.toNodeMap[e]? then
    return (r, m)
  let { uf, toNodeMap } := m
  let r := uf.size
  (r, { uf := uf.push, toNodeMap := toNodeMap.insert e r })

variable (useHash : Bool) in
def isEquiv (e1 e2 : Expr) : StateM EquivManager Bool := do
  -- FIXME: find a way to do this with withPtrEq or benchmark how important it is
  if unsafe ptrEq e1 e2 then return true
  if useHash && e1.hash != e2.hash then return false
  if e1.isBVar && e2.isBVar then return e1.bvarIdx! == e2.bvarIdx!
  let r1 ← find (← toNode e1)
  let r2 ← find (← toNode e2)
  if r1 == r2 then return true
  let result ←
    match e1, e2 with
    | .const c1 l1, .const c2 l2 => pure <| c1 == c2 && l1 == l2
    | .mvar a1, .mvar a2 | .fvar a1, .fvar a2
    | .sort a1, .sort a2 | .lit a1, .lit a2 => pure <| a1 == a2
    | .app f1 a1, .app f2 a2 => isEquiv f1 f2 <&&> isEquiv a1 a2
    | .lam _ d1 b1 _, .lam _ d2 b2 _ => isEquiv d1 d2 <&&> isEquiv b1 b2
    | .mdata _ a1, .mdata _ a2 => isEquiv a1 a2
    | .forallE _ d1 b1 _, .forallE _ d2 b2 _ => isEquiv d1 d2 <&&> isEquiv b1 b2
    | .proj _ i1 e1, .proj _ i2 e2 => pure (i1 == i2) <&&> isEquiv e1 e2
    | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ => isEquiv t1 t2 <&&> isEquiv v1 v2 <&&> isEquiv b1 b2
    | _, _ => return false
  if result then
    modify (merge · r1 r2)
  return result

def addEquiv (m : EquivManager) (e1 e2 : Expr) : EquivManager :=
  let (r1, m) := toNode e1 m
  let (r2, m) := toNode e2 m
  merge m r1 r2
