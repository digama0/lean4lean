import Lean
import Lean4Lean.List

namespace Lean.Level

def forEach [Monad m] (l : Level) (f : Level → m Bool) : m Unit := do
  if !(← f l) then return
  match l with
  | .succ l => l.forEach f
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.forEach f; l₂.forEach f
  | .zero | .param .. | .mvar .. => pure ()

/-- Returns `some n` if level parameter `n` appears in `l` and `n ∉ ps`. -/
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

/-- represents v+n -/
structure VarNode where
  var : Name
  offset : Nat
  deriving BEq, Ord, Repr

/-- A key-value pair `vs => { const, var }` in NormLevel represents
the max of `C(vs, const)` and `V(vs, v, n)` for each `v+n ∈ var`, using the `C` and `V` sublevel
functions from <https://lmf.cnrs.fr/downloads/Perso/long.pdf>. -/
structure Node where
  const : Nat := 0
  var : List VarNode := []
  deriving Repr, Inhabited

instance : BEq Node where
  beq n₁ n₂ := n₁.const == n₂.const && n₁.var == n₂.var
instance : Ord Node where
  compare n₁ n₂ := compare n₁.const n₂.const |>.then <| compare n₁.var n₂.var

def Node.isEmpty (n : Node) : Bool := n.const == 0 && n.var.isEmpty

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

@[reducible] def NormLevel := Std.TreeMap (List Name) Node compare
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

def NormLevel.addNode (v : Name) (k : Nat) (path' : List Name) (s : NormLevel) : NormLevel :=
  s.alter path' fun
    | none => some { var := [⟨v, k⟩] }
    | some n => some { n with var := VarNode.addVar v k n.var }

def NormLevel.addConst (k : Nat) (path : List Name) (acc : NormLevel) : NormLevel :=
  if k = 0 || k = 1 && !path.isEmpty then acc else
  acc.alter path fun
    | none => some { const := k }
    | some n => some { n with const := k.max n.const }

def normalizeAux (l : Level) (path : List Name) (k : Nat) (acc : NormLevel) : NormLevel :=
  match l with
  | .zero | .imax _ .zero => acc.addConst k path
  | .succ u => normalizeAux u path (k+1) acc
  | .max u v => normalizeAux u path k acc |> normalizeAux v path k
  | .imax u (.succ v) => normalizeAux u path k acc |> normalizeAux v path (k+1)
  | .imax u (.max v w) => normalizeAux (.imax u v) path k acc |> normalizeAux (.imax u w) path k
  | .imax u (.imax v w) => normalizeAux (.imax u w) path k acc |> normalizeAux (.imax v w) path k
  | .imax u (.param v) =>
    match orderedInsert Name.cmp v path with
    | some path' => acc.addConst k path |>.addNode v k path' |> normalizeAux u path' k
    | none =>
      let acc := if k = 0 then acc else acc.addVar v k path
      normalizeAux u path k acc
  | .mvar _ | .imax _ (.mvar _) => acc -- unreachable
  | .param v =>
    match orderedInsert Name.cmp v path with
    | some path' => acc.addConst k path |>.addNode v k path'
    | none => if k = 0 then acc else acc.addVar v k path

def subsumeVars : List VarNode → List VarNode → List VarNode
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y :: ys =>
    match Name.cmp x.var y.var with
    | .lt => x :: subsumeVars xs (y :: ys)
    | .eq => if x.offset ≤ y.offset then subsumeVars xs ys else x :: subsumeVars xs ys
    | .gt => subsumeVars (x :: xs) ys

/-- Remove from `n₁` the sublevels dominated by `n₂`, whose condition set is a subset of
`n₁`'s: `C(c)` is dominated by `C(c')` when `c ≤ c'` and by `V(x+k)` when `c ≤ k + 1`, and
`V(x+k)` is dominated by `V(x+k')` when `k ≤ k'`.

`same` says the two sit at the *same* condition set, where a variable may still discharge the
constant but the variables must not discharge themselves. -/
def Node.subsumeBy (same : Bool) (n₁ n₂ : Node) : Node :=
  let n₁ :=
    if n₁.const = 0 ||
      (same || n₁.const > n₂.const) &&
      (n₂.var.isEmpty || n₁.const > n₂.var.foldl (·.max ·.offset) 0 + 1)
    then n₁ else { n₁ with const := 0 }
  if same || n₂.var.isEmpty then n₁ else { n₁ with var := subsumeVars n₁.var n₂.var }

/-- Remove the parts of the sublevels at `(p₁, n₁)` that are dominated by the sublevels
at `(p₂, n₂)`. -/
def Node.subsume (p₁ : List Name) (n₁ : Node) (p₂ : List Name) (n₂ : Node) : Node :=
  if subset compare p₂ p₁ then n₁.subsumeBy (p₁.length == p₂.length) n₂ else n₁

/-- Remove the parts of the sublevels at `(p₁, n₁)` dominated by other entries of the map. -/
def NormLevel.minimize (acc : NormLevel) (p₁ : List Name) (n₁ : Node) : Node :=
  acc.foldl (init := n₁) (Node.subsume p₁)

def NormLevel.subsumption (acc : NormLevel) : NormLevel :=
  acc.foldl (init := acc) fun acc p₁ n₁ =>
    let n := acc.minimize p₁ n₁
    if n.isEmpty then acc.erase p₁ else acc.insert p₁ n

def normalize (l : Level) : NormLevel :=
  Normalize.normalizeAux l [] 0 {} |>.subsumption

/-- Sublevel comparison, following Theorem 39 of the paper: `l₁ ≤ l₂` iff every sublevel
of `l₁` is dominated by some sublevel of `l₂`, where
`C(E, L) ≤ C(F, K) ↔ F ⊆ E ∧ L ≤ K`, `C(E, L) ≤ V(F, x, K) ↔ F ⊆ E ∧ L ≤ K + 1`,
and `V(E, x, L) ≤ V(F, y, K) ↔ F ⊆ E ∧ x = y ∧ L ≤ K`.

Each sublevel picks its own dominator, and a node bundles several of them, so it is not
enough to look for a single entry of `l₂` dominating a whole node of `l₁`: for
`imax 2 v ≤ max 2 v` the constant is dominated at `∅` and the variable at `{v}`. Instead
each entry of `l₂` discharges what it can from the sublevels of `n₁` that are still
outstanding, which is the same `subsumeBy` step minimization uses; the node is dominated
once nothing is left, and the fold stops there. -/
def NormLevel.le (l₁ l₂ : NormLevel) : Bool :=
  l₁.all fun p₁ n₁ =>
    -- `none` means nothing is left to discharge, which stops the fold
    Option.isNone <| l₂.foldlM (init := n₁) (m := Option) fun n p₂ n₂ =>
      if subset compare p₂ p₁ then
        let n := n.subsumeBy false n₂
        if n.isEmpty then none else some n
      else some n

/-!
Reconstruction of a `Level` from a `NormLevel`.

The paper's canonical form is a set of sublevels `C(S, k)`, `V(S, v+k)`; it does not address
which such sets are expressible as level expressions. Reifying a sublevel with conditions `S`
requires nesting it under an imax chain `imax (… imax (imax (_) v₁) …) vₙ` where
`{v₁, …, vₙ} = S`, and each edge of such a chain itself contributes the sublevel
`V(S', vᵢ, 0)` where `S'` is the set of conditions up to that point. So a chain order is
admissible only if each such edge contribution is dominated by the canonical form, i.e.
there is some `V(T, vᵢ+k)` with `T ⊆ S'` among the sublevels. Canonical forms produced by
`normalizeAux` always admit at least one such order for every key
(each key is the condition set of some `imax` chain suffix of the input, whose edges put
the required `V` entries at subsets of the key, and subsumption only moves coverage to
smaller sets).

To make the output canonical, the choice of chain must depend only on the canonical
sublevels, not on incidental map keys (which record which `imax` chains appeared
syntactically in the input). For each key we take the lexicographically least admissible
chain, computed greedily. This is well-defined: domination of `V(S', v, 0)` is monotone
in `S'`, so extending the set of conditions added so far never invalidates other elements,
and a greedy choice never needs to be revisited (checking that the remainder stays
completable before committing to each element). -/

/-- Is the edge contribution `V(acc ∪ {a}, a, 0)` dominated by the normal form?
True iff some `V(T, a+k)` with `T ⊆ acc ∪ {a}` is present. -/
def NormLevel.addable (s : NormLevel) (a : Name) (acc : List Name) : Bool :=
  s.any fun p n => n.var.any (·.var == a) && subset compare (p.erase a) acc

/-- Can the elements of `rem` be added to the condition set `acc` one at a time, each
addition being `addable` at that point? Since `addable` is monotone in `acc`, adding any
addable element preserves completability, so a greedy check is complete. -/
def NormLevel.feasible (s : NormLevel) (acc rem : List Name) : Bool :=
  go rem.length acc rem
where
  go : Nat → List Name → List Name → Bool
  | 0, _, rem => rem.isEmpty
  | fuel+1, acc, rem =>
    match rem.find? (s.addable · acc) with
    | none => rem.isEmpty
    | some a => go fuel ((orderedInsert Name.cmp a acc).getD acc) (rem.erase a)

/-- The lexicographically least admissible imax chain building the condition set `p`,
listed innermost (last-added) first: at each step, remove the least element that is
`addable` on top of the rest and whose remainder is still completable.
This depends only on the sublevels of `s`, not on its key set, so equal normal forms
reify to equal levels. (The fallback returns the remaining set in sorted order;
it is not reachable for normal forms produced by `normalizeAux`.) -/
def NormLevel.lexChain (s : NormLevel) : Nat → List Name → List Name
  | 0, p => p
  | fuel+1, p =>
    match p.find? fun a => s.addable a (p.erase a) && s.feasible [] (p.erase a) with
    | some a => a :: s.lexChain fuel (p.erase a)
    | none => p

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
  acc.foldl (init := ⟨0, [], []⟩) fun t p n =>
    let path := acc.lexChain p.length p
    -- the edge into this tree node already contributes `V(p, v, 0)` for the innermost
    -- chain element `v`, so an explicit `v+0` entry would be redundant
    let var := if let v :: _ := path then subsumeVars n.var [⟨v, 0⟩] else n.var
    t.modify path fun t => { t with const := n.const, var }

/-- If the subtree behind an edge labelled `a` holds nothing but the sublevel `V(_, a, k)`,
return `k`.

Such an edge contributes `imax (a+k) a`, which differs from the plain `a+k` only at `a = 0`,
where the plain form gives `k` instead of `0`. So the guard may be dropped, and the child
written as just `a+k`, whenever the node's constant is at least `k` — and if the constant is
*exactly* `k`, it may then be dropped itself, since `a+k ≥ k`. Without this, `u+1` would reify
to `max 1 (imax (u+1) u)` rather than to itself, and the canonical form would be roughly twice
the size of the input on typical levels. -/
def Tree.plainOffset? (a : Name) : Tree → Option Nat
  | ⟨0, [], []⟩ => some 0
  | ⟨0, [v], []⟩ => if v.var == a then some v.offset else none
  | _ => none

def Tree.reify : Tree → Level
  | { const, var, child } =>
    let l := child.foldr (mkChild const) none
    let l := var.foldr (init := l) fun n r =>
      some (mkMax (addOffset (.param n.var) n.offset) r)
    match l with
    | none => ofNat const
    | some l =>
      if const == 0 || child.any fun c => plainOffset? c.1 c.2 == some const then l
      else max (ofNat const) l
where
  mkMax (l : Level) : Option Level → Level
  | none => l
  | some u => max l u
  mkChild (const : Nat)
  | (n, t), r =>
    match plainOffset? n t with
    | some k =>
      if k ≤ const then mkMax (addOffset (.param n) k) r
      else mkMax (imax (reify t) (.param n)) r
    | none => mkMax (imax (reify t) (.param n)) r

end Normalize

def normalize' (l : Level) : Level := (Normalize.normalize l).toTree.reify

/-- Core's `isEquiv` is sound but incomplete, so it can be used as a fast path: when it
accepts, the levels really are equivalent, and when it rejects we fall back to the complete
check. Over the 261k level comparisons performed while checking Lean+Std+Batteries this
filter decided every single real equivalence, leaving only the genuinely inequivalent 0.1%
to the fallback — and it is roughly 20× cheaper than normalizing. -/
def isEquiv' (u v : Level) : Bool :=
  isEquiv u v || Normalize.normalize u == Normalize.normalize v

def isEquivList : List Level → List Level → Bool := List.all2 isEquiv

/-- Core's `geq` as a fast path, on the same grounds as `isEquiv'`. -/
def geq' (u v : Level) : Bool :=
  geq u v || (Normalize.normalize v).le (Normalize.normalize u)

-- local elab "normalize " l:level : command => do
--   Elab.Command.runTermElabM fun _ => do
--     logInfo m!"{normalize' (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l) }"

-- local elab "normalize " l:level " ≤ " l':level : command => do
--   Elab.Command.runTermElabM fun _ => do
--     logInfo m!"{geq' (← Elab.Term.elabLevel l') (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l')}"

-- universe u v w
-- /-- info: max 1 u -/
-- #guard_msgs in normalize max u 1
-- /-- info: u -/
-- #guard_msgs in normalize imax 1 u
-- /-- info: max 1 (imax (u + 1) u) -/
-- #guard_msgs in normalize u+1
-- /-- info: imax 2 u -/
-- #guard_msgs in normalize imax 2 u
-- /-- info: max v (imax (imax u v) w) -/
-- #guard_msgs in normalize max w (imax (imax u w) v)
-- /-- info: max v (imax (imax u v) w) -/
-- #guard_msgs in normalize max (imax (imax u v) w) (imax (imax u w) v)
-- /-- info: u -/
-- #guard_msgs in normalize imax u u
-- /-- info: max 1 (imax (u + 1) u) -/
-- #guard_msgs in normalize imax u (u+1)
-- /-- info: max 1 (imax (max (v + 1) (imax (u + 1) u)) v) -/
-- #guard_msgs in normalize imax u v + 1
