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

inductive WF [BEq α] [Hashable α] : PersistentHashMap α β → Prop where
  | empty : WF .empty
  | insert : WF m → WF (m.insert a b)

/-- We can't prove this because `Lean.PersistentHashMap.insertAux` is opaque -/
axiom WF.toList'_insert {α β} [BEq α] [Hashable α]
    [PartialEquivBEq α] [LawfulHashable α]
    {m : PersistentHashMap α β} (_ : WF m) (a : α) (b : β) :
    (m.insert a b).toList' ~ (a, b) :: m.toList'.filter (¬a == ·.1)

/-- We can't prove this because `Lean.PersistentHashMap.findAux` is opaque -/
axiom WF.find?_eq {α β} [BEq α] [Hashable α]
    [PartialEquivBEq α] [LawfulHashable α]
    {m : PersistentHashMap α β} (_ : WF m) (a : α) : m.find? a = m.toList'.lookup a

/-- We can't prove this because `Lean.PersistentHashMap.{findAux, containsAux}` are opaque -/
axiom findAux_isSome {α β} [BEq α] {node : Node α β} (i : USize) (a : α) :
    containsAux node i a = (findAux node i a).isSome

end PersistentHashMap

-- FIXME: lean4#8464
open private mkAppRangeAux from Lean.Expr in
axiom Expr.mkAppRangeAux.eq_def (n : Nat) (args : Array Expr) (i : Nat) (e : Expr) :
  mkAppRangeAux n args i e =
    if i < n then mkAppRangeAux n args (i + 1) (mkApp e args[i]!) else e

namespace Level

def mkData' (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data :=
  if depth > Nat.pow 2 24 - 1 then panic! "universe level depth is too big"
  else
    h.toUInt32.toUInt64 +
    hasMVar.toUInt64.shiftLeft 32 +
    hasParam.toUInt64.shiftLeft 33 +
    depth.toUInt64.shiftLeft 40

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkData_eq : @mkData = @mkData'

def hasParam' : Level → Bool
  | .param .. => true
  | .zero | .mvar .. => false
  | .succ l => l.hasParam'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasParam' || l₂.hasParam'

/-- This is currently false, see bug lean4#8554 -/
@[simp] axiom hasParam_eq (l : Level) : l.hasParam = l.hasParam'

def hasMVar' : Level → Bool
  | .mvar .. => true
  | .zero | .param .. => false
  | .succ l => l.hasMVar'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasMVar' || l₂.hasMVar'

/-- This is currently false, see bug lean4#8554 -/
@[simp] axiom hasMVar_eq (l : Level) : l.hasMVar = l.hasMVar'

/-- This is because the `BEq` instance is implemented in C++ -/
@[instance] axiom instLawfulBEqLevel : LawfulBEq Level

@[inline] private def mkIMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero || u matches .succ .zero then v
  else if u == v then u
  else elseK ()

open private mkLevelIMaxCore from Lean.Level in
/-- Workaround for https://github.com/leanprover/lean4/pull/7631#issuecomment-3289800246 -/
@[simp] axiom mkLevelIMaxCore_eq (e : Expr) (n : Nat) : mkLevelIMaxCore = mkIMaxCore

end Level

namespace Expr

def mkData'
    (h : UInt64) (looseBVarRange : Nat := 0) (approxDepth : UInt32 := 0)
    (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false)
    : Expr.Data :=
  let approxDepth : UInt8 := if approxDepth > 255 then 255 else approxDepth.toUInt8
  assert! (looseBVarRange ≤ Nat.pow 2 20 - 1)
  h.toUInt32.toUInt64 +
  approxDepth.toUInt64.shiftLeft 32 +
  hasFVar.toUInt64.shiftLeft 40 +
  hasExprMVar.toUInt64.shiftLeft 41 +
  hasLevelMVar.toUInt64.shiftLeft 42 +
  hasLevelParam.toUInt64.shiftLeft 43 +
  looseBVarRange.toUInt64.shiftLeft 44

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkData_eq : @mkData = @mkData'

@[inline] def mkAppData' (fData : Data) (aData : Data) : Data :=
  let depth          := max fData.approxDepth.toUInt16 aData.approxDepth.toUInt16 + 1
  let approxDepth    := if depth > 255 then 255 else depth.toUInt8
  let looseBVarRange := max fData.looseBVarRange aData.looseBVarRange
  let hash           := mixHash fData aData
  let fData : UInt64 := fData
  let aData : UInt64 := aData
  assert! looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32
  (fData ||| aData) &&& (15 : UInt64) <<< (40 : UInt64) |||
  hash.toUInt32.toUInt64 |||
  approxDepth.toUInt64 <<< (32 : UInt64) |||
  looseBVarRange.toUInt64 <<< (44 : UInt64)

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkAppData_eq : @mkAppData = @mkAppData'

def hasFVar' : Expr → Bool
  | .fvar _ => true
  | .const ..
  | .bvar _
  | .sort _
  | .mvar _
  | .lit _ => false
  | .mdata _ e => e.hasFVar'
  | .proj _ _ e => e.hasFVar'
  | .app e1 e2
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => e1.hasFVar' || e2.hasFVar'
  | .letE _ t v b _ => t.hasFVar' || v.hasFVar' || b.hasFVar'

/-- This is currently false, see bug lean4#8554 -/
axiom hasFVar_eq (e : Expr) : e.hasFVar = e.hasFVar'

def hasExprMVar' : Expr → Bool
  | .mvar _ => true
  | .const ..
  | .bvar _
  | .sort _
  | .fvar _
  | .lit _ => false
  | .mdata _ e => e.hasExprMVar'
  | .proj _ _ e => e.hasExprMVar'
  | .app e1 e2
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => e1.hasExprMVar' || e2.hasExprMVar'
  | .letE _ t v b _ => t.hasExprMVar' || v.hasExprMVar' || b.hasExprMVar'

/-- This is currently false, see bug lean4#8554 -/
@[simp] axiom hasExprMVar_eq (e : Expr) : e.hasExprMVar = e.hasExprMVar'

def hasLevelMVar' : Expr → Bool
  | .const _ ls => ls.any (·.hasMVar)
  | .sort u => u.hasMVar
  | .bvar _
  | .fvar _
  | .mvar _
  | .lit _ => false
  | .mdata _ e => e.hasLevelMVar'
  | .proj _ _ e => e.hasLevelMVar'
  | .app e1 e2
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => e1.hasLevelMVar' || e2.hasLevelMVar'
  | .letE _ t v b _ => t.hasLevelMVar' || v.hasLevelMVar' || b.hasLevelMVar'

/-- This is currently false, see bug lean4#8554 -/
@[simp] axiom hasLevelMVar_eq (e : Expr) : e.hasLevelMVar = e.hasLevelMVar'

def hasLevelParam' : Expr → Bool
  | .const _ ls => ls.any (·.hasParam)
  | .sort u => u.hasParam
  | .bvar _
  | .fvar _
  | .mvar _
  | .lit _ => false
  | .mdata _ e => e.hasLevelParam'
  | .proj _ _ e => e.hasLevelParam'
  | .app e1 e2
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => e1.hasLevelParam' || e2.hasLevelParam'
  | .letE _ t v b _ => t.hasLevelParam' || v.hasLevelParam' || b.hasLevelParam'

/-- This is currently false, see bug lean4#8554 -/
@[simp] axiom hasLevelParam_eq (e : Expr) : e.hasLevelParam = e.hasLevelParam'

def looseBVarRange' : Expr → Nat
  | .bvar i => i + 1
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => 0
  | .mdata _ e
  | .proj _ _ e => e.looseBVarRange'
  | .app e1 e2 => max e1.looseBVarRange' e2.looseBVarRange'
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => max e1.looseBVarRange' (e2.looseBVarRange' - 1)
  | .letE _ e1 e2 e3 _ => max (max e1.looseBVarRange' e2.looseBVarRange') (e3.looseBVarRange' - 1)

/-- This is currently false, see bug lean4#8554 -/
@[simp] axiom looseBVarRange_eq (e : Expr) : e.looseBVarRange = e.looseBVarRange'

/-- This could be an `@[implemented_by]` -/
@[simp] axiom replace_eq (e : Expr) (f) : e.replace f = e.replaceNoCache f

def liftLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  match e with
  | .bvar i => .bvar (if i < s then i else i + d)
  | .mdata m e => .mdata m (liftLooseBVars' e s d)
  | .proj n i e => .proj n i (liftLooseBVars' e s d)
  | .app f a => .app (liftLooseBVars' f s d) (liftLooseBVars' a s d)
  | .lam n t b bi => .lam n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (liftLooseBVars' t s d) (liftLooseBVars' v s d) (liftLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/-- This could be an `@[implemented_by]` -/
@[simp] axiom liftLooseBVars_eq (e : Expr) (s d) : e.liftLooseBVars s d = e.liftLooseBVars' s d

def lowerLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  if s < d then e else
  match e with
  | .bvar i => .bvar (if i < s then i else i - d)
  | .mdata m e => .mdata m (lowerLooseBVars' e s d)
  | .proj n i e => .proj n i (lowerLooseBVars' e s d)
  | .app f a => .app (lowerLooseBVars' f s d) (lowerLooseBVars' a s d)
  | .lam n t b bi => .lam n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (lowerLooseBVars' t s d) (lowerLooseBVars' v s d) (lowerLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/-- This could be an `@[implemented_by]` -/
@[simp] axiom lowerLooseBVars_eq (e : Expr) (s d) : e.lowerLooseBVars s d = e.lowerLooseBVars' s d

def instantiate1' (e : Expr) (subst : Expr) (d := 0) : Expr :=
  match e with
  | .bvar i => if i < d then e else if i = d then subst.liftLooseBVars' 0 d else .bvar (i - 1)
  | .mdata m e => .mdata m (instantiate1' e subst d)
  | .proj s i e => .proj s i (instantiate1' e subst d)
  | .app f a => .app (instantiate1' f subst d) (instantiate1' a subst d)
  | .lam n t b bi => .lam n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .forallE n t b bi => .forallE n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .letE n t v b bi =>
    .letE n (instantiate1' t subst d) (instantiate1' v subst d) (instantiate1' b subst (d+1)) bi
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => e

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiate1_eq (e : Expr) (subst) : e.instantiate1 subst = e.instantiate1' subst

@[simp] def instantiateList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => instantiateList (instantiate1' e a k) as k

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiate_eq (e : Expr) (subst) :
    e.instantiate subst = e.instantiateList subst.toList

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiateRev_eq (e : Expr) (subst) :
    e.instantiateRev subst = e.instantiate subst.reverse

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiateRange_eq (e : Expr) (subst) :
    e.instantiateRange start stop subst = e.instantiate (subst.extract start stop)

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiateRevRange_eq (e : Expr) (subst) :
    e.instantiateRevRange start stop subst = e.instantiateRev (subst.extract start stop)

def abstract1 (v : FVarId) : Expr → (k :_:= 0) → Expr
  | .bvar i, d => .bvar (if i < d then i else i + 1)
  | e@(.fvar v'), d => if v == v' then .bvar d else e
  | .mdata m e, d => .mdata m (abstract1 v e d)
  | .proj s i e, d => .proj s i (abstract1 v e d)
  | .app f a, d => .app (abstract1 v f d) (abstract1 v a d)
  | .lam n t b bi, d => .lam n (abstract1 v t d) (abstract1 v b (d+1)) bi
  | .forallE n t b bi, d => .forallE n (abstract1 v t d) (abstract1 v b (d+1)) bi
  | .letE n t val b bi, d =>
    .letE n (abstract1 v t d) (abstract1 v val d) (abstract1 v b (d+1)) bi
  | e@(.const ..), _
  | e@(.sort _), _
  | e@(.mvar _), _
  | e@(.lit _), _ => e

@[simp] def abstractList : Expr → List FVarId → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => abstractList (abstract1 a e k) as k

/-- This could be an `@[implemented_by]` -/
@[simp] axiom abstract_eq (e : Expr) (xs : List FVarId) :
    e.abstract ⟨xs.map .fvar⟩ = e.abstractList xs

/-- This could be an `@[implemented_by]` -/
@[simp] axiom abstractRange_eq (e : Expr) (n : Nat) (xs : Array Expr) :
    e.abstractRange n xs = e.abstract (xs.extract 0 n)

def hasLooseBVar' : (e : @& Expr) → (bvarIdx : @& Nat) → Bool
  | .bvar i, d => i = d
  | .mdata _ e, d
  | .proj _ _ e, d => hasLooseBVar' e d
  | .app f a, d => hasLooseBVar' f d || hasLooseBVar' a d
  | .lam _ t b _, d
  | .forallE _ t b _, d => hasLooseBVar' t d || hasLooseBVar' b (d+1)
  | .letE _ t v b _, d => hasLooseBVar' t d || hasLooseBVar' v d || hasLooseBVar' b (d+1)
  | .const .., _
  | .sort _, _
  | .fvar _, _
  | .mvar _, _
  | .lit _, _ => false

/-- This could be an `@[implemented_by]` -/
@[simp] axiom hasLooseBVar_eq (e : Expr) (n : Nat) : e.hasLooseBVar n = e.hasLooseBVar' n

end Expr
