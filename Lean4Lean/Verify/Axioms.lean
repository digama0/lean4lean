import Batteries.Tactic.OpenPrivate
import Lean4Lean.Std.Basic
import Lean4Lean.Std.NodupKeys

open scoped List
namespace Lean

noncomputable def PersistentArrayNode.toList' : PersistentArrayNode α → List α :=
  PersistentArrayNode.rec
    (motive_1 := fun _ => List α) (motive_2 := fun _ => List α) (motive_3 := fun _ => List α)
    (node := fun _ => id) (leaf := (·.toList)) (fun _ => id) [] (fun _ _ a b => a ++ b)

namespace PersistentArray

inductive WF : PersistentArray α → Prop where
  | empty : WF .empty
  | push : WF arr → WF (arr.push x)

noncomputable def toList' (arr : PersistentArray α) : List α :=
  arr.root.toList' ++ arr.tail.toList

@[simp] theorem toList'_empty : (.empty : PersistentArray α).toList' = [] := rfl

/-- We cannot prove this because `insertNewLeaf` is partial -/
@[simp] axiom toList'_push {α} (arr : PersistentArray α) (x : α) :
    (arr.push x).toList' = arr.toList' ++ [x]

@[simp] theorem size_empty : (.empty : PersistentArray α).size = 0 := rfl

@[simp] theorem size_push {α} (arr : PersistentArray α) (x : α) :
    (arr.push x).size = arr.size + 1 := by
  simp [push]; split <;> [rfl; (simp [mkNewTail]; split <;> rfl)]

@[simp] theorem WF.toList'_length (h : WF arr) : arr.toList'.length = arr.size := by
  induction h <;> simp [*]

end PersistentArray

namespace PersistentHashMap

noncomputable def Node.toList' : Node α β → List (α × β) :=
  Node.rec
    (motive_1 := fun _ => List (α × β)) (motive_2 := fun _ => List (α × β))
    (motive_3 := fun _ => List (α × β)) (motive_4 := fun _ => List (α × β))
    (entries := fun _ => id) (collision := fun ks xs _ => ks.toList.zip xs.toList)
    (mk := fun _ => id)
    (nil := []) (cons := fun _ _ l1 l2 => l1 ++ l2)
    (entry := fun a b => [(a, b)]) (ref := fun _ => id) (null := [])

noncomputable def toList' [BEq α] [Hashable α] (m : PersistentHashMap α β) :
    List (α × β) := m.root.toList'

@[simp] theorem toList'_empty [BEq α] [Hashable α] :
    (.empty : PersistentHashMap α β).toList' = [] := by
  have this n : @Node.toList' α β (.entries ⟨.replicate n .null⟩) = [] := by
    simp [Node.toList']
    induction n <;> simp [*, List.replicate_succ]
  apply this

inductive WF [BEq α] [Hashable α] : PersistentHashMap α β → Prop where
  | empty : WF .empty
  | insert : m.find? a = none → WF m → WF (m.insert a b)

/-- We can't prove this because `Lean.PersistentHashMap.insertAux` is opaque -/
axiom WF.toList'_insert {α β} [BEq α] [Hashable α]
    [PartialEquivBEq α] [Batteries.HashMap.LawfulHashable α]
    {m : PersistentHashMap α β} (_ : WF m) (a : α) (b : β) :
    m.toList'.lookup a = none → (m.insert a b).toList' ~ (a, b) :: m.toList'

/-- We can't prove this because `Lean.PersistentHashMap.findAux` is opaque -/
axiom WF.find?_eq {α β} [BEq α] [Hashable α]
    [PartialEquivBEq α] [Batteries.HashMap.LawfulHashable α]
    {m : PersistentHashMap α β} (_ : WF m) (a : α) : m.find? a = m.toList'.lookup a

/-- We can't prove this because `Lean.PersistentHashMap.{findAux, containsAux}` are opaque -/
axiom findAux_isSome {α β} [BEq α] {node : Node α β} (i : USize) (a : α) :
    containsAux node i a = (findAux node i a).isSome

theorem find?_isSome {α β} [BEq α] [Hashable α]
    (m : PersistentHashMap α β) (a : α) : m.contains a = (m.find? a).isSome := findAux_isSome ..

theorem WF.nodupKeys [BEq α] [Hashable α]
    [LawfulBEq α] [Batteries.HashMap.LawfulHashable α]
    {m : PersistentHashMap α β} (h : WF m) : m.toList'.NodupKeys := by
  induction h with
  | empty => simp; exact .nil
  | insert h1 h2 ih =>
    rw [h2.find?_eq] at h1
    refine (h2.toList'_insert _ _ h1).nodupKeys_iff.2 (List.nodupKeys_cons.2 ⟨?_, ih⟩)
    rintro ⟨a, b⟩ h3 rfl
    cases h1.symm.trans (ih.lookup_eq_some.2 h3)

end PersistentHashMap

-- FIXME: lean4#8464
open private mkAppRangeAux from Lean.Expr in
axiom Expr.mkAppRangeAux.eq_def (n : Nat) (args : Array Expr) (i : Nat) (e : Expr) :
  mkAppRangeAux n args i e =
    if i < n then mkAppRangeAux n args (i + 1) (mkApp e args[i]!) else e

namespace Expr

def Safe : Expr → Prop
  | .bvar i => i < 2^20 - 1
  | .const ..
  | .sort _ -- TODO: should this use Level.Safe?
  | .fvar _
  | .mvar _
  | .lit _ => True
  | .mdata _ e
  | .proj _ _ e => e.Safe
  | .app e1 e2
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => e1.Safe ∧ e2.Safe
  | .letE _ e1 e2 e3 _ => e1.Safe ∧ e2.Safe ∧ e3.Safe

/--
Lean has some incorrect bound variable handling above 2^20. We use an axiom here
to keep track of places where we are using the assumption that bound variables
don't go too large.
-/
axiom safeSorry (e : Expr) : e.Safe

end Expr

namespace Level

def realDepth : Level → Nat
  | .zero
  | .param _
  | .mvar _ => 0
  | .succ u => u.realDepth + 1
  | .max u v
  | .imax u v => u.realDepth.max v.realDepth + 1

def Safe (l : Level) : Prop := l.realDepth < 2 ^ 24

/--
Level expressions with depth higher than 2^24 currently have unsound behavior, see
[zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Soundness.20bug.3A.20hasLooseBVars.20is.20not.20conservative/near/521286338).
-/
axiom safeSorry (e : Level) : e.Safe

end Level
