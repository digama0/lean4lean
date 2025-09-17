import Lean
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

/-!
## Level normalization

Based on Yoan Géran, "A Canonical Form for Universe Levels in Impredicative Type Theory"
<https://lmf.cnrs.fr/downloads/Perso/long.pdf>.
-/

namespace Normalize

local instance : Ord Name := ⟨Name.cmp⟩

structure VarNode where
  var : Name
  offset : Nat
  deriving BEq, Ord, Repr

structure Node where
  path : List Name := []
  const : Nat := 0
  var : List VarNode := []
  deriving Repr, Inhabited

instance : BEq Node where
  beq n₁ n₂ := n₁.const == n₂.const && n₁.var == n₂.var
instance : Ord Node where
  compare n₁ n₂ := compare n₁.const n₂.const |>.then <| compare n₁.var n₂.var

def subset (cmp : α → α → Ordering) : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    match cmp x y with
    | .lt => false
    | .eq => subset cmp xs ys
    | .gt => subset cmp (x :: xs) ys

def orderedInsert (cmp : α → α → Ordering) (a : α) : List α → Option (List α)
  | [] => some [a]
  | b :: l =>
    match cmp a b with
    | .lt => some (a :: b :: l)
    | .eq => none
    | .gt => (orderedInsert cmp a l).map (b :: ·)

def NormLevel := Std.TreeMap (List Name) Node compare
  deriving Repr

instance : BEq NormLevel where
  beq l₁ l₂ :=
    (l₁.all fun p n => l₂.get? p == some n) &&
    (l₂.all fun p n => l₁.get? p == some n)

def VarNode.addVar (v : Name) (k : Nat) : List VarNode → List VarNode
  | [] => [⟨v, k⟩]
  | v' :: l =>
    match Name.cmp v v'.var with
    | .lt => ⟨v, k⟩ :: v' :: l
    | .eq => ⟨v, v'.offset.max k⟩ :: l
    | .gt => v' :: addVar v k l

def NormLevel.addVar (v : Name) (k : Nat) (path' : List Name) (s : NormLevel) : NormLevel :=
  s.modify path' fun n => { n with var := VarNode.addVar v k n.var }

def NormLevel.addNode (v : Name) (path' : List Name) (s : NormLevel) : NormLevel :=
  s.alter path' fun
    | none => some { var := [⟨v, 0⟩] }
    | some n => some { n with var := VarNode.addVar v 0 n.var }

def NormLevel.addConst (k : Nat) (path : List Name) (acc : NormLevel) : NormLevel :=
  if k = 0 || k = 1 && !path.isEmpty then acc else
  acc.modify path fun n => { n with const := k.max n.const }

def normalizeAux (l : Level) (path : List Name) (k : Nat) (acc : NormLevel) : NormLevel :=
  match l with
  | .zero | .imax _ .zero => acc.addConst k path
  | .succ u => normalizeAux u path (k+1) acc
  | .max u v => normalizeAux u path k acc |> normalizeAux v path k
  | .imax u (.succ v) => normalizeAux u path k acc |> normalizeAux v path (k+1)
  | .imax u (.max v w) =>
    normalizeAux (.imax u v) path k acc |> normalizeAux (.imax u w) path k
  | .imax u (.imax v w) =>
    normalizeAux (.imax u w) path k acc |> normalizeAux (.imax v w) path k
  | .imax u (.param v) =>
    match orderedInsert Name.cmp v path with
    | some path' => acc.addNode v path' |> normalizeAux u path' k
    | none => normalizeAux u path k acc
  | .mvar _ | .imax _ (.mvar _) => acc -- unreachable
  | .param v =>
    match orderedInsert Name.cmp v path with
    | some path' =>
      let acc := acc.addConst k path |>.addNode v path'
      if k = 0 then acc else acc.addVar v k path'
    | none => if k = 0 then acc else acc.addVar v k path

def subsumeVars : List VarNode → List VarNode → List VarNode
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y :: ys =>
    match Name.cmp x.var y.var with
    | .lt => x :: subsumeVars xs (y :: ys)
    | .eq => if x.offset ≤ y.offset then subsumeVars xs ys else x :: subsumeVars xs ys
    | .gt => subsumeVars (x :: xs) ys

def findParent (f : List Name → Bool) : (l₁ l₂ : List Name) → List Name
  | _, [] => []
  | l₁, a :: l₂ => if f (l₁.reverseAux l₂) then [a] else findParent f (a :: l₁) l₂

def NormLevel.subsumption (acc : NormLevel) (paths := false) : NormLevel :=
  acc.foldl (init := acc) fun acc p₁ n₁ =>
    let n₁ := acc.foldl (init := n₁) fun n₁ p₂ n₂ =>
      if !subset compare p₂ p₁ then n₁ else
      let same := p₁.length == p₂.length
      let n₁ :=
        if n₁.const = 0 ||
          (same || n₁.const > n₂.const) &&
          (n₂.var.isEmpty || n₁.const > n₁.var.foldl (·.max ·.offset) 0 + 1)
        then n₁ else { n₁ with const := 0 }
      if same || n₂.var.isEmpty then n₁ else { n₁ with var := subsumeVars n₁.var n₂.var }
    let n₁ := if paths then
      let path := findParent acc.contains [] p₁
      let var := if let [v] := path then subsumeVars n₁.var [⟨v, 0⟩] else n₁.var
      { n₁ with path, var }
    else n₁
    acc.insert p₁ n₁

def normalize (l : Level) (paths := false) : NormLevel :=
  Normalize.normalizeAux l [] 0 (.insert {} [] default) |>.subsumption paths

def leVars : List VarNode → List VarNode → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    match Name.cmp x.var y.var with
    | .lt => false
    | .eq => x.offset ≤ y.offset && leVars xs ys
    | .gt => leVars (x :: xs) ys

def NormLevel.le (l₁ l₂ : NormLevel) : Bool :=
  l₁.all fun p₁ n₁ =>
    if n₁.const = 0 && n₁.var.isEmpty then true else
    l₂.any fun p₂ n₂ =>
      (!n₂.var.isEmpty || n₁.var.isEmpty) &&
      subset compare p₂ p₁ &&
      (n₂.const ≤ n₁.const || n₂.var.any (n₂.const ≤ ·.offset + 1)) &&
      leVars n₁.var n₂.var

def NormLevel.buildPaths : StateM NormLevel Unit := do
  (← get).foldlM (init := ()) fun _ p _ => do
    let n := (← get).get! p
    if let [v] := n.path then
      let l ← getPath (p.erase v) p.length
      setPath p (v :: l)
where
  setPath (p path : List Name) : StateM NormLevel Unit :=
    modify (·.modify p ({ · with path }))

  getPath (p : List Name) (depth : Nat) : StateM NormLevel (List Name) := do
    let n := (← get).get! p
    if let [v] := n.path then
      if let depth + 1 := depth then
        let l ← getPath (p.erase v) depth
        setPath p (v :: l)
        return v :: l
    return n.path

structure Tree where
  const : Nat
  var : List VarNode
  child : List (Name × Tree)
  deriving Inhabited

def modifyAt [Inhabited α] (f : α → α) (n : Name) : List (Name × α) → List (Name × α)
  | [] => [(n, f default)]
  | (x, v) :: l =>
    match Name.cmp n x with
    | .lt => (n, f default) :: (x, v) :: l
    | .eq => (x, f v) :: l
    | .gt => (x, v) :: modifyAt f n l

def Tree.modify (path : List Name) (f : Tree → Tree) (t : Tree) : Tree :=
  match path with
  | [] => f t
  | a :: p => modify p (t := t) fun t => { t with child := modifyAt f a t.child }

def NormLevel.toTree (acc : NormLevel) : Tree :=
  (buildPaths.run acc).run.2.foldl (init := ⟨0, [], []⟩) fun t _ n =>
    t.modify n.path fun t => { t with const := n.const, var := n.var }

def treeVarDedup : List VarNode → List (Name × Tree) → List VarNode
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y :: ys =>
    match Name.cmp x.1 y.1 with
    | .lt => x :: treeVarDedup xs (y :: ys)
    | .eq => if x.2 = 0 then treeVarDedup xs ys else x :: treeVarDedup xs ys
    | .gt => treeVarDedup (x :: xs) ys

def Tree.reify : Tree → Level
  | { const, var, child } =>
    let l := child.foldr mkChild none
    let l := (treeVarDedup var child).foldr (init := l) fun n r =>
      some (mkMax (addOffset (.param n.var) n.offset) r)
    match l with
    | none => ofNat const
    | some l => if const = 0 then l else max (ofNat const) l
where
  mkMax (l : Level) : Option Level → Level
  | none => l
  | some u => max l u
  mkChild
  | (n, t), r =>
    match reify t with
    | .zero => mkMax (.param n) r
    | t => mkMax (imax t (.param n)) r

end Normalize

def normalize' (l : Level) : Level := (Normalize.normalize l (paths := true)).toTree.reify

def isEquiv' (u v : Level) : Bool := u == v || Normalize.normalize u == Normalize.normalize v

def isEquivList : List Level → List Level → Bool := List.all2 isEquiv'

def geq' (u v : Level) : Bool := (Normalize.normalize v).le (Normalize.normalize u)

-- local elab "normalize " l:level : command => do
--   Elab.Command.runTermElabM fun _ => do
--     logInfo m!"{normalize' (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l) }"

-- universe u v w
-- /-- info: max 1 u -/
-- #guard_msgs in normalize max u 1
-- /-- info: u -/
-- #guard_msgs in normalize imax 1 u
-- /-- info: max 1 (imax (u+1) u) -/
-- #guard_msgs in normalize u+1
-- /-- info: imax 2 u -/
-- #guard_msgs in normalize imax 2 u
-- /-- info: max v (imax (imax u v) w) -/
-- #guard_msgs in normalize max w (imax (imax u w) v)
-- /-- info: max v (imax (imax u v) w) -/
-- #guard_msgs in normalize max (imax (imax u v) w) (imax (imax u w) v)
-- /-- info: u -/
-- #guard_msgs in normalize imax u u
-- /-- info: max 1 (imax (u+1) u) -/
-- #guard_msgs in normalize imax u (u+1)
