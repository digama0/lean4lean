import Batteries.Tactic.OpenPrivate
import Lean4Lean.Std.Basic
import Lean4Lean.Std.NodupKeys

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

/-- https://github.com/leanprover/lean4/issues/12798 -/
axiom all_eq_all_toList {p : α → β → Bool} :
    t.all p = t.toList.all fun a => p a.1 a.2

/-- https://github.com/leanprover/lean4/issues/12798 -/
axiom any_eq_any_toList {p : α → β → Bool} :
    t.any p = t.toList.any fun a => p a.1 a.2

end Std.TreeMap

open scoped _root_.List
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

namespace Syntax

def structEq' : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node _ k args, .node _ k' args' => k == k' &&
    (args.size == args'.size &&
      (args.toList.attach.zip args'.toList.attach).all fun (a, b) =>
        have := Array.mem_toList_iff.1 a.2; structEq' a b)
  | .atom _ val, .atom _ val' => val == val'
  | .ident _ rawVal val preresolved, Syntax.ident _ rawVal' val' preresolved' =>
    rawVal == rawVal' && val == val' && preresolved == preresolved'
  | _, _ => false
termination_by x _ => x

theorem structEq'_node :
    structEq' (.node _x k args) (.node _y k' args') = (k == k' && args.isEqv args' structEq') := by
  unfold structEq'; simp; congr 1
  by_cases h : args.size = args'.size <;> [simp [h]; simp [Array.isEqv, h]]
  let ⟨args⟩ := args; let ⟨args'⟩ := args'; simp at h ⊢
  have' : ((args.attach.map (·.1)).zip (args'.attach.map (·.1))).all
      (fun x => x.1.structEq' x.2) = _ := by
    simp only [List.zip_map_left, List.zip_map_right]; simp [Function.comp_def]; rfl
  rw [← this]; simp; clear this
  induction args generalizing args' <;> cases args' <;> simp at h <;> simp [List.isEqv, *]

/-- This is a `partial` because it is not obviously terminating. The `structEq'_node` theorem
shows that a definition with the same clauses can be defined manually. -/
@[simp] axiom structEq_eq : structEq a b = structEq' a b
end Syntax

namespace Level

/-!
### A total copy of `Lean.Level.normalize`

`Lean.Level.normalize` and four of its helpers are `partial def`s, so they are opaque and nothing
can be proved about them. The `Total` namespace below is a clause-by-clause copy of
[Lean's `Lean/Level.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Level.lean#L319-L404),
under the same names, with the termination proofs supplied. That makes `normalize_eq` below a
purely syntactic trust assumption, checkable by reading the two definitions side by side;
`Lean4Lean.Tests.LevelStd` also checks it on a finite corpus of levels.
-/
namespace Total

/-- The structural size of a level, used as the termination measure for `normalize`. -/
def size : Level → Nat
  | .zero | .param _ | .mvar _ => 1
  | .succ l => size l + 1
  | .max l₁ l₂ => size l₁ + size l₂ + 1
  | .imax l₁ l₂ => size l₁ + size l₂ + 2

/-- Secondary termination measure for `normalize`: in the `imax` branch it recurses on
`mkLevelMax l₁ l₂`, which has the same `size` as `imax l₁ l₂` but a smaller `tag`. -/
private def tag (l : Level) : Nat :=
  match l.getLevelOffset with
  | .imax .. => 1
  | _ => 0

private theorem tag_le (l : Level) : tag l ≤ 1 := by unfold tag; split <;> omega

theorem one_le_size (l : Level) : 1 ≤ size l := by cases l <;> simp [size]

private theorem getOffsetAux_eq (l : Level) (k) : getOffsetAux l k = getOffsetAux l 0 + k := by
  induction l generalizing k with
  | succ l ih => rw [getOffsetAux, ih (k+1), getOffsetAux, ih 1]; omega
  | _ => simp [getOffsetAux]

theorem size_getLevelOffset (l : Level) :
    size l.getLevelOffset + l.getOffset = size l := by
  simp only [getOffset]
  induction l with | succ l ih => ?_ | _ => rfl
  show size l.getLevelOffset + getOffsetAux l 1 = size l + 1
  rw [getOffsetAux_eq l 1]; omega

end Total
open private accMax mkIMaxAux mkMaxAux skipExplicit isExplicitSubsumedAux
  isExplicitSubsumed from Lean.Level

def Total.mkMaxAux (lvls : Array Level) (extraK : Nat) (i : Nat)
    (prev : Level) (prevK : Nat) (result : Level) : Level :=
  if h : i < lvls.size then
    let lvl   := lvls[i]
    let curr  := lvl.getLevelOffset
    let currK := lvl.getOffset
    if curr == prev then mkMaxAux lvls extraK (i+1) curr currK result
    else mkMaxAux lvls extraK (i+1) curr currK (accMax result prev (extraK + prevK))
  else accMax result prev (extraK + prevK)

/-- Patch for `partial def Lean.Level.mkMaxAux`. -/
@[simp] axiom mkMaxAux_eq : mkMaxAux = Total.mkMaxAux

def Total.skipExplicit (lvls : Array Level) (i : Nat) : Nat :=
  if h : i < lvls.size then
    if lvls[i].getLevelOffset.isZero then skipExplicit lvls (i+1) else i
  else i

/-- Patch for `partial def Lean.Level.skipExplicit`. -/
@[simp] axiom skipExplicit_eq : skipExplicit = Total.skipExplicit

def Total.isExplicitSubsumedAux (lvls : Array Level) (maxExplicit : Nat) (i : Nat) : Bool :=
  if h : i < lvls.size then
    if lvls[i].getOffset ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (i+1)
  else false

/-- Patch for `partial def Lean.Level.isExplicitSubsumedAux`. -/
@[simp] axiom isExplicitSubsumedAux_eq : isExplicitSubsumedAux = Total.isExplicitSubsumedAux

mutual

/-- A total copy of `partial def Lean.Level.normalize`. -/
def Total.normalize (l : Level) : Level :=
  if isAlreadyNormalizedCheap l then l else
  let k := l.getOffset
  match h : l.getLevelOffset with
  | .max l₁ l₂ =>
    let lvls  := getMaxArgsAux l₁ false #[]
    let lvls  := getMaxArgsAux l₂ false lvls
    let lvls  := lvls.qsort normLt
    let firstNonExplicit := skipExplicit lvls 0
    let i := if isExplicitSubsumed lvls firstNonExplicit then firstNonExplicit
              else firstNonExplicit - 1
    let lvl₁  := lvls[i]!
    let prev  := lvl₁.getLevelOffset
    let prevK := lvl₁.getOffset
    mkMaxAux lvls k (i+1) prev prevK Level.zero
  | .imax l₁ l₂ =>
    if l₂.isNeverZero then addOffset (normalize (mkLevelMax l₁ l₂)) k
    else addOffset (mkIMaxAux (normalize l₁) (normalize l₂)) k
  | _ => unreachable!
termination_by (1, 3 * size l + tag l)
decreasing_by all_goals
  refine .right _ ?_
  have hsz := size_getLevelOffset l
  rw [h] at hsz
  simp only [size] at hsz
  have := one_le_size l₁
  have := one_le_size l₂
  have := tag_le l₁
  have := tag_le l₂
  first
  | omega
  | have ht : tag l = 1 := by simp [tag, h]
    have e1 : size (mkLevelMax l₁ l₂) = size l₁ + size l₂ + 1 := rfl
    have e2 : tag (mkLevelMax l₁ l₂) = 0 := rfl
    omega

def Total.getMaxArgsAux : Level → Bool → Array Level → Array Level
  | .max l₁ l₂, norm, lvls => getMaxArgsAux l₂ norm (getMaxArgsAux l₁ norm lvls)
  | l, false, lvls => getMaxArgsAux (normalize l) true lvls
  | l, true, lvls => lvls.push l
termination_by l b => (if b then 0 else 1, 3 * size l + tag l + 1)
decreasing_by
  any_goals cases norm
  any_goals first | refine .right _ ?_ | exact .left _ _ (by decide)
  all_goals first
  | omega
  | have e1 : size (Level.max l₁ l₂) = size l₁ + size l₂ + 1 := rfl
    have e2 : tag (Level.max l₁ l₂) = 0 := rfl
    have := one_le_size l₁
    have := one_le_size l₂
    have := tag_le l₁
    have := tag_le l₂
    omega

end

/-- `Lean.Level.normalize` is a `partial def`, so it is opaque;
`Total.normalize` above is a total copy of it. -/
axiom normalize_eq : normalize = Total.normalize

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

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
@[simp] axiom hasParam_eq (l : Level) : l.hasParam = l.hasParam'

def hasMVar' : Level → Bool
  | .mvar .. => true
  | .zero | .param .. => false
  | .succ l => l.hasMVar'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasMVar' || l₂.hasMVar'

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
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

open private mkLevelMaxCore from Lean.Level in
theorem mkLevelMax'_hasMVar_false (u v : Level) :
    u.hasMVar' = false → v.hasMVar' = false →
      (mkLevelMax' u v).hasMVar' = false := by
  intro hu hv
  unfold Lean.mkLevelMax'
  unfold mkLevelMaxCore
  repeat' first | split
  all_goals simp_all
  all_goals repeat' first | split
  all_goals simp_all [Lean.mkLevelMax]
  all_goals repeat' first | split
  all_goals simp_all [hasMVar']

open private mkLevelIMaxCore from Lean.Level in
theorem mkLevelIMax'_hasMVar_false (u v : Level) :
    u.hasMVar' = false → v.hasMVar' = false →
      (mkLevelIMax' u v).hasMVar' = false := by
  intro hu hv
  unfold Lean.mkLevelIMax'
  unfold mkLevelIMaxCore
  repeat' first | split
  all_goals simp_all [mkLevelMax'_hasMVar_false, hasMVar', Lean.mkLevelIMax]

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

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
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

instance : LawfulBEq FVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Name) h; rfl
  rfl := BEq.rfl (α := Name)

/-- Distance from the end of `xs` of the last occurrence of `v` (`0` for the last element). -/
def lastRevIdx? (v : FVarId) : List FVarId → Option Nat
  | [] => none
  | a :: as =>
    match lastRevIdx? v as with
    | some r => some r
    | none => if a == v then some as.length else none

theorem lastRevIdx?_eq_none_of_not_mem {v : FVarId} : ∀ {xs : List FVarId}, v ∉ xs →
    lastRevIdx? v xs = none
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.mem_cons, not_or] at h
    simp [lastRevIdx?, lastRevIdx?_eq_none_of_not_mem h.2, Ne.symm h.1]

theorem lastRevIdx?_eq_none_iff {v : FVarId} : ∀ {xs : List FVarId},
    lastRevIdx? v xs = none ↔ v ∉ xs
  | [] => by simp [lastRevIdx?]
  | a :: as => by
    simp only [lastRevIdx?, List.mem_cons, not_or]
    constructor
    · intro h
      split at h
      · cases h
      · rename_i hnone
        have := lastRevIdx?_eq_none_iff.1 hnone
        refine ⟨fun hv => ?_, this⟩
        subst hv; simp at h
    · rintro ⟨hv, has⟩
      rw [lastRevIdx?_eq_none_of_not_mem has]
      simp [Ne.symm hv]

/-- Simultaneous abstraction of a list of free variables, the model of Lean's `Expr.abstract`
(C++ `abstract`): under `d` binders, `xs[i]` becomes `bvar (d + xs.length - 1 - i)`; when a
variable occurs more than once the last occurrence wins; and loose bound variables are left
unchanged. The sequential `abstractList` instead shifts every loose bound variable at or above
the cutoff once per abstracted variable, so the two agree only on expressions without such
variables (`abstractN_eq_abstractList`); `abstract_eq` carries that hypothesis. -/
def abstractN (xs : List FVarId) : Expr → (k :_:= 0) → Expr
  | e@(.bvar _), _ => e
  | e@(.fvar v), d =>
    match lastRevIdx? v xs with
    | some r => .bvar (d + r)
    | none => e
  | .mdata m e, d => .mdata m (abstractN xs e d)
  | .proj s i e, d => .proj s i (abstractN xs e d)
  | .app f a, d => .app (abstractN xs f d) (abstractN xs a d)
  | .lam n t b bi, d => .lam n (abstractN xs t d) (abstractN xs b (d+1)) bi
  | .forallE n t b bi, d => .forallE n (abstractN xs t d) (abstractN xs b (d+1)) bi
  | .letE n t val b bi, d =>
    .letE n (abstractN xs t d) (abstractN xs val d) (abstractN xs b (d+1)) bi
  | e@(.const ..), _
  | e@(.sort _), _
  | e@(.mvar _), _
  | e@(.lit _), _ => e

/-- This could be an `@[implemented_by]`. `abstract` is modelled by the simultaneous
`abstractN`, not by the sequential `abstractList`: the two differ in general, since
`(Expr.bvar 0).abstract #[.fvar x] = .bvar 0` while `abstractList` returns `.bvar 1`. -/
@[simp] axiom abstractN_eq (e : Expr) (xs : List FVarId) :
    e.abstract ⟨xs.map .fvar⟩ = e.abstractN xs

theorem abstractList_bvar_lt (xs : List FVarId) (h : i < k) :
    abstractList (.bvar i) xs k = .bvar i := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [abstractList, abstract1, h, ih]

theorem abstractList_bvar_ge' (xs : List FVarId) (h : k ≤ i) :
    abstractList (.bvar i) xs k = .bvar (i + xs.length) := by
  induction xs generalizing i with
  | nil => rfl
  | cons a as ih =>
    simp only [abstractList, abstract1, if_neg (by omega : ¬ i < k)]
    rw [ih (by omega)]; simp; omega

theorem abstractList_fvar (xs : List FVarId) (hnd : xs.Nodup) (v : FVarId) (k : Nat) :
    abstractList (.fvar v) xs k =
      match lastRevIdx? v xs with
      | some r => .bvar (k + r)
      | none => .fvar v := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.nodup_cons] at hnd
    simp only [abstractList, abstract1, lastRevIdx?]
    by_cases hv : a = v
    · subst hv
      simp only [beq_self_eq_true, ite_true, lastRevIdx?_eq_none_of_not_mem hnd.1]
      rw [abstractList_bvar_ge' _ (Nat.le_refl _)]
    · have hne : (a == v) = false := by simpa using hv
      simp only [hne, Bool.false_eq_true, ite_false]
      rw [ih hnd.2]
      split <;> simp_all

theorem abstractList_mdata :
    abstractList (.mdata m e) xs k = .mdata m (abstractList e xs k) := by
  induction xs generalizing e <;> simp_all [abstractList, abstract1]
theorem abstractList_proj :
    abstractList (.proj s i e) xs k = .proj s i (abstractList e xs k) := by
  induction xs generalizing e <;> simp_all [abstractList, abstract1]
theorem abstractList_app :
    abstractList (.app f a) xs k = .app (abstractList f xs k) (abstractList a xs k) := by
  induction xs generalizing f a <;> simp_all [abstractList, abstract1]
theorem abstractList_lam : abstractList (.lam n t b bi) xs k =
    .lam n (abstractList t xs k) (abstractList b xs (k+1)) bi := by
  induction xs generalizing t b <;> simp_all [abstractList, abstract1]
theorem abstractList_forallE : abstractList (.forallE n t b bi) xs k =
    .forallE n (abstractList t xs k) (abstractList b xs (k+1)) bi := by
  induction xs generalizing t b <;> simp_all [abstractList, abstract1]
theorem abstractList_letE : abstractList (.letE n t v b bi) xs k =
    .letE n (abstractList t xs k) (abstractList v xs k) (abstractList b xs (k+1)) bi := by
  induction xs generalizing t v b <;> simp_all [abstractList, abstract1]
theorem abstractList_const : abstractList (.const c ls) xs k = .const c ls := by
  induction xs <;> simp_all [abstractList, abstract1]
theorem abstractList_sort' : abstractList (.sort u) xs k = .sort u := by
  induction xs <;> simp_all [abstractList, abstract1]
theorem abstractList_mvar' : abstractList (.mvar m) xs k = .mvar m := by
  induction xs <;> simp_all [abstractList, abstract1]
theorem abstractList_lit' : abstractList (.lit l) xs k = .lit l := by
  induction xs <;> simp_all [abstractList, abstract1]

/-- On expressions with no loose bound variables at or above `k`, simultaneous abstraction of
a duplicate-free list agrees with the sequential model. -/
theorem abstractN_eq_abstractList {xs : List FVarId} (hnd : xs.Nodup) :
    ∀ (e : Expr) (k : Nat), e.looseBVarRange' ≤ k → abstractN xs e k = abstractList e xs k
  | .bvar i, k, h => by
    simp only [looseBVarRange'] at h
    rw [abstractN, abstractList_bvar_lt _ (by omega)]
  | .fvar v, k, _ => by rw [abstractN, abstractList_fvar _ hnd]
  | .mdata m e, k, h => by
    rw [abstractN, abstractList_mdata, abstractN_eq_abstractList hnd e k h]
  | .proj s i e, k, h => by
    rw [abstractN, abstractList_proj, abstractN_eq_abstractList hnd e k h]
  | .app f a, k, h => by
    simp only [looseBVarRange', Nat.max_le] at h
    rw [abstractN, abstractList_app, abstractN_eq_abstractList hnd f k h.1,
      abstractN_eq_abstractList hnd a k h.2]
  | .lam n t b bi, k, h => by
    simp only [looseBVarRange', Nat.max_le] at h
    rw [abstractN, abstractList_lam, abstractN_eq_abstractList hnd t k h.1,
      abstractN_eq_abstractList hnd b (k+1) (by omega)]
  | .forallE n t b bi, k, h => by
    simp only [looseBVarRange', Nat.max_le] at h
    rw [abstractN, abstractList_forallE, abstractN_eq_abstractList hnd t k h.1,
      abstractN_eq_abstractList hnd b (k+1) (by omega)]
  | .letE n t v b bi, k, h => by
    simp only [looseBVarRange', Nat.max_le] at h
    rw [abstractN, abstractList_letE, abstractN_eq_abstractList hnd t k h.1.1,
      abstractN_eq_abstractList hnd v k h.1.2, abstractN_eq_abstractList hnd b (k+1) (by omega)]
  | .const c ls, k, _ => by rw [abstractN, abstractList_const]
  | .sort u, k, _ => by rw [abstractN, abstractList_sort']
  | .mvar m, k, _ => by rw [abstractN, abstractList_mvar']
  | .lit l, k, _ => by rw [abstractN, abstractList_lit']

/-- Lean's `abstract` agrees with the sequential model on locally closed expressions and
duplicate-free variable lists. -/
theorem abstract_eq_of_closed (e : Expr) (xs : List FVarId) (hnd : xs.Nodup)
    (h : e.looseBVarRange' = 0) : e.abstract ⟨xs.map .fvar⟩ = e.abstractList xs := by
  rw [abstractN_eq]; exact abstractN_eq_abstractList hnd e 0 (by omega)



/-- Abstracting a single variable from a locally closed expression. -/
theorem abstractN_singleton (h : e.looseBVarRange' ≤ k) :
    abstractN [a] e k = abstract1 a e k :=
  abstractN_eq_abstractList (by simp) e k h

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

def eqv' : (e1 e2 : Expr) → (strict : Bool := false) → Bool
  | .bvar i, .bvar i', _
  | .lit i, .lit i', _
  | .mvar i, .mvar i', _
  | .fvar i, .fvar i', _
  | .sort i, .sort i', _ => i == i'
  | .mdata d e, .mdata d' e', st => e.eqv' e' st && d.entries == d'.entries
  | .proj s i e, .proj s' i' e', st => e.eqv' e' st && s == s' && i == i'
  | .const n ls, .const n' ls', _ => n == n' && ls == ls'
  | .app f a, .app f' a', st => f.eqv' f' st && a.eqv' a' st
  | .lam n t b bi, .lam n' t' b' bi', st
  | .forallE n t b bi, .forallE n' t' b' bi', st =>
    t.eqv' t' st && b.eqv' b' st && (!st || (n == n' && bi == bi'))
  | .letE n t v b nd, .letE n' t' v' b' nd', st =>
    t.eqv' t' st && v.eqv' v' st && b.eqv' b' st && nd == nd' && (!st || n == n')
  | _, _, _ => false

/-- This could be an `@[implemented_by]` -/
@[simp] axiom eqv_eq (e1 e2 : Expr) : e1.eqv e2 = e1.eqv' e2

/-- This could be an `@[implemented_by]` -/
@[simp] axiom equal_eq (e1 e2 : Expr) : e1.equal e2 = e1.eqv' e2 (strict := true)

/-- Abstracting one more variable, placed outermost, is a later abstraction at the binder
depth of the inner variables. -/
theorem abstractN_cons (h : a ∉ xs) : ∀ (e : Expr) (d : Nat),
    abstractN (a :: xs) e d = abstractN [a] (abstractN xs e d) (d + xs.length)
  | .bvar _, _ => rfl
  | .fvar v, d => by
    simp only [abstractN, lastRevIdx?]
    cases hr : lastRevIdx? v xs with
    | some r => simp [abstractN]
    | none =>
      by_cases hv : a = v
      · subst hv; simp [abstractN, lastRevIdx?]
      · have : (a == v) = false := by simpa using hv
        simp [abstractN, lastRevIdx?, this]
  | .mdata _ e, d => by simp [abstractN, abstractN_cons h e d]
  | .proj _ _ e, d => by simp [abstractN, abstractN_cons h e d]
  | .app f a', d => by simp [abstractN, abstractN_cons h f d, abstractN_cons h a' d]
  | .lam _ t b _, d => by
    simp [abstractN, abstractN_cons h t d, abstractN_cons h b (d+1), Nat.add_right_comm]
  | .forallE _ t b _, d => by
    simp [abstractN, abstractN_cons h t d, abstractN_cons h b (d+1), Nat.add_right_comm]
  | .letE _ t v b _, d => by
    simp [abstractN, abstractN_cons h t d, abstractN_cons h v d, abstractN_cons h b (d+1),
      Nat.add_right_comm]
  | .const .., _ | .sort _, _ | .mvar _, _ | .lit _, _ => rfl

theorem lastRevIdx?_lt_length {v : FVarId} : ∀ {xs : List FVarId} {r : Nat},
    lastRevIdx? v xs = some r → r < xs.length
  | [], _, h => by cases h
  | a :: as, r, h => by
    simp only [lastRevIdx?] at h
    split at h
    · rename_i hr
      have := lastRevIdx?_lt_length hr
      cases h; simp; omega
    · split at h
      · cases h; simp
      · cases h

theorem abstractN_nil : ∀ (e : Expr) (d : Nat), abstractN [] e d = e
  | .bvar _, _ => rfl
  | .fvar v, d => by simp [abstractN, lastRevIdx?]
  | .mdata _ e, d => by simp [abstractN, abstractN_nil e d]
  | .proj _ _ e, d => by simp [abstractN, abstractN_nil e d]
  | .app f a', d => by simp [abstractN, abstractN_nil f d, abstractN_nil a' d]
  | .lam _ t b _, d => by simp [abstractN, abstractN_nil t d, abstractN_nil b (d+1)]
  | .forallE _ t b _, d => by simp [abstractN, abstractN_nil t d, abstractN_nil b (d+1)]
  | .letE _ t v b _, d => by
    simp [abstractN, abstractN_nil t d, abstractN_nil v d, abstractN_nil b (d+1)]
  | .const .., _ | .sort _, _ | .mvar _, _ | .lit _, _ => rfl

/-- Abstraction at depth `d + 1` never creates or removes an occurrence of `bvar 0`. -/
theorem abstractN_hasLooseBVar_zero (xs : List FVarId) : ∀ (e : Expr) (d : Nat),
    (abstractN xs e (d + 1)).hasLooseBVar' 0 = e.hasLooseBVar' 0 := by
  suffices ∀ (e : Expr) (d i : Nat), i < d →
      (abstractN xs e d).hasLooseBVar' i = e.hasLooseBVar' i from
    fun e d => this e (d + 1) 0 (by omega)
  intro e
  induction e with
  | bvar _ => intros; rfl
  | fvar v =>
    intro d i hi
    simp only [abstractN]
    split <;> simp [hasLooseBVar']; omega
  | mdata _ e ih | proj _ _ e ih => intro d i hi; simp [abstractN, hasLooseBVar', ih d i hi]
  | app f a ihf iha => intro d i hi; simp [abstractN, hasLooseBVar', ihf d i hi, iha d i hi]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    intro d i hi; simp [abstractN, hasLooseBVar', iht d i hi, ihb (d+1) (i+1) (by omega)]
  | letE _ t v b _ iht ihv ihb =>
    intro d i hi
    simp [abstractN, hasLooseBVar', iht d i hi, ihv d i hi, ihb (d+1) (i+1) (by omega)]
  | const _ _ => intros; rfl
  | sort _ => intros; rfl
  | mvar _ => intros; rfl
  | lit _ => intros; rfl

/-- Lowering an unused innermost variable commutes with later abstraction. -/
theorem abstractN_lower (xs : List FVarId) : ∀ (e : Expr) (d : Nat), e.hasLooseBVar' 0 = false →
    abstractN xs (e.lowerLooseBVars' 1 1) d = (abstractN xs e (d + 1)).lowerLooseBVars' 1 1 := by
  suffices ∀ (e : Expr) (d k : Nat), k ≤ d → e.hasLooseBVar' k = false →
      abstractN xs (e.lowerLooseBVars' (k + 1) 1) d =
        (abstractN xs e (d + 1)).lowerLooseBVars' (k + 1) 1 from
    fun e d h => this e d 0 (Nat.zero_le _) h
  intro e
  induction e with
  | bvar i =>
    intro d k hk h
    simp [hasLooseBVar'] at h
    simp [abstractN, lowerLooseBVars']
  | fvar v =>
    intro d k hk h
    cases hr : lastRevIdx? v xs with
    | some r =>
      have h1 : ¬ (k + 1 < 1) := by omega
      have h2 : ¬ (d + 1 + r < k + 1) := by omega
      simp only [abstractN, hr, lowerLooseBVars', h1, h2, ite_false]
      congr 1; omega
    | none => simp [abstractN, hr, lowerLooseBVars']
  | mdata _ e ih | proj _ _ e ih =>
    intro d k hk h; simp [hasLooseBVar'] at h; simp [abstractN, lowerLooseBVars', ih d k hk h]
  | app f a ihf iha =>
    intro d k hk h; simp [hasLooseBVar'] at h
    simp [abstractN, lowerLooseBVars', ihf d k hk h.1, iha d k hk h.2]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    intro d k hk h; simp [hasLooseBVar'] at h
    simp [abstractN, lowerLooseBVars', iht d k hk h.1, ihb (d+1) (k+1) (by omega) h.2]
  | letE _ t v b _ iht ihv ihb =>
    intro d k hk h; simp [hasLooseBVar'] at h
    simp [abstractN, lowerLooseBVars', iht d k hk h.1.1, ihv d k hk h.1.2,
      ihb (d+1) (k+1) (by omega) h.2]
  | const _ _ => intros; simp [abstractN, lowerLooseBVars']
  | sort _ => intros; simp [abstractN, lowerLooseBVars']
  | mvar _ => intros; simp [abstractN, lowerLooseBVars']
  | lit _ => intros; simp [abstractN, lowerLooseBVars']

end Expr
