import Batteries.Tactic.OpenPrivate
import Std.Tactic.BVDecide
import Lean4Lean.Std.Basic
import Lean4Lean.Std.NodupKeys

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

/-- https://github.com/leanprover/lean4/issues/12798 -/
axiom all_eq_all_toList {p : α → β → Bool} :
    t.all p = t.toList.all fun a => p a.1 a.2

end Std.TreeMap

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

theorem Data.looseBVarRange_le :
    (Data.looseBVarRange d).toNat ≤ 2 ^ 20 - 1 := by
  rw [Data.looseBVarRange]
  suffices (UInt64.shiftRight d 44).toNat ≤ 2 ^ 20 - 1 by simp; omega
  show d.toBitVec >>> 44#64 ≤ 0xfffff#64
  bv_decide

private theorem Data.flag_eq_getLsbD (d : Data) (n : UInt64) (hn : n < 64) :
    ((d.shiftRight n).land 1 == 1) = d.toBitVec.getLsbD n.toNat := by
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  have hmod : UInt64.mod n 64 = n := UInt64.mod_eq_of_lt hn
  constructor
  · intro h
    have hb := congrArg UInt64.toBitVec h
    simp [UInt64.shiftRight, UInt64.land, hmod] at hb
    have := congrArg (fun x : BitVec 64 => x.getLsbD 0) hb
    simpa using this
  · intro h
    apply UInt64.toBitVec_inj.mp
    simp [UInt64.shiftRight, UInt64.land, hmod]
    ext i
    by_cases hi : i = 0
    · subst i
      simpa using h
    · simp [hi]

private theorem Data.hasFVar_eq_getLsbD (d : Data) :
    d.hasFVar = d.toBitVec.getLsbD 40 := by
  simpa [Data.hasFVar] using Data.flag_eq_getLsbD d 40 (by decide)

private theorem Data.hasExprMVar_eq_getLsbD (d : Data) :
    d.hasExprMVar = d.toBitVec.getLsbD 41 := by
  simpa [Data.hasExprMVar] using Data.flag_eq_getLsbD d 41 (by decide)

private theorem Data.hasLevelMVar_eq_getLsbD (d : Data) :
    d.hasLevelMVar = d.toBitVec.getLsbD 42 := by
  simpa [Data.hasLevelMVar] using Data.flag_eq_getLsbD d 42 (by decide)

private theorem Data.hasLevelParam_eq_getLsbD (d : Data) :
    d.hasLevelParam = d.toBitVec.getLsbD 43 := by
  simpa [Data.hasLevelParam] using Data.flag_eq_getLsbD d 43 (by decide)

private def flagAt (fv ev lv lp : Bool) : Nat → Bool
  | 0 => fv
  | 1 => ev
  | 2 => lv
  | 3 => lp
  | _ => false

private theorem mkData_flags (H : br ≤ 2 ^ 20 - 1) :
    (mkData h br d fv ev lv lp).hasFVar = fv ∧
    (mkData h br d fv ev lv lp).hasExprMVar = ev ∧
    (mkData h br d fv ev lv lp).hasLevelMVar = lv ∧
    (mkData h br d fv ev lv lp).hasLevelParam = lp := by
  rw [mkData_eq, mkData', if_pos H]
  simp [Data.hasFVar, Data.hasExprMVar, Data.hasLevelMVar, Data.hasLevelParam,
    (· == ·), ← UInt64.toBitVec_inj]
  have hh : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 :=
    Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have hfv := hb fv
  have hev := hb ev
  have hlv := hb lv
  have hlp := hb lp
  have hnat : br.toUInt64.toNat = br := by simp; omega
  have hbr : br.toUInt64.toBitVec ≤ 0xfffff#64 := (hnat ▸ H :)
  let depth : UInt8 := if d > 255 then 255 else d.toUInt8
  have hd : depth.toUInt64.toBitVec ≤ 0xff#64 := Nat.le_of_lt_succ depth.1.1.2
  let data :=
    h.toUInt32.toUInt64.toBitVec +
    depth.toUInt64.toBitVec <<< 32#64 +
    fv.toUInt64.toBitVec <<< 40#64 +
    ev.toUInt64.toBitVec <<< 41#64 +
    lv.toUInt64.toBitVec <<< 42#64 +
    lp.toUInt64.toBitVec <<< 43#64 +
    br.toUInt64.toBitVec <<< 44#64
  change
    decide (data >>> 40#64 &&& 1#64 = 1#64) = fv ∧
    decide (data >>> 41#64 &&& 1#64 = 1#64) = ev ∧
    decide (data >>> 42#64 &&& 1#64 = 1#64) = lv ∧
    decide (data >>> 43#64 &&& 1#64 = 1#64) = lp
  bv_decide

private theorem mkData_hasFVar (H : br ≤ 2 ^ 20 - 1) :
    (mkData h br d fv ev lv lp).hasFVar = fv := by
  exact (mkData_flags H).1

private theorem mkData_hasExprMVar (H : br ≤ 2 ^ 20 - 1) :
    (mkData h br d fv ev lv lp).hasExprMVar = ev := by
  exact (mkData_flags H).2.1

private theorem mkData_hasLevelMVar (H : br ≤ 2 ^ 20 - 1) :
    (mkData h br d fv ev lv lp).hasLevelMVar = lv := by
  exact (mkData_flags H).2.2.1

private theorem mkData_hasLevelParam (H : br ≤ 2 ^ 20 - 1) :
    (mkData h br d fv ev lv lp).hasLevelParam = lp := by
  exact (mkData_flags H).2.2.2

private theorem mkData_flags_of_false (br d h) :
    (mkData h br d false false false false).hasFVar = false ∧
    (mkData h br d false false false false).hasExprMVar = false ∧
    (mkData h br d false false false false).hasLevelMVar = false ∧
    (mkData h br d false false false false).hasLevelParam = false := by
  by_cases H : br ≤ 2 ^ 20 - 1
  · exact mkData_flags H
  · rw [mkData_eq, mkData', if_neg H]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem mkData_hasFVar_of_false (br d h) :
    (mkData h br d false false false false).hasFVar = false :=
  (mkData_flags_of_false br d h).1

private theorem mkData_hasExprMVar_of_false (br d h) :
    (mkData h br d false false false false).hasExprMVar = false :=
  (mkData_flags_of_false br d h).2.1

private theorem mkData_hasLevelMVar_of_false (br d h) :
    (mkData h br d false false false false).hasLevelMVar = false :=
  (mkData_flags_of_false br d h).2.2.1

private theorem mkData_hasLevelParam_of_false (br d h) :
    (mkData h br d false false false false).hasLevelParam = false :=
  (mkData_flags_of_false br d h).2.2.2

private theorem mkAppData_flag (i : Nat) (hi : i < 4) :
    (mkAppData fData aData).toBitVec.getLsbD (40 + i) = flagAt
      (fData.hasFVar || aData.hasFVar)
      (fData.hasExprMVar || aData.hasExprMVar)
      (fData.hasLevelMVar || aData.hasLevelMVar)
      (fData.hasLevelParam || aData.hasLevelParam) i := by
  have hm : max fData.looseBVarRange aData.looseBVarRange ≤
      (Nat.pow 2 20 - 1).toUInt32 := by
    dsimp +instances [instMaxUInt32, maxOfLe]
    split <;> exact Data.looseBVarRange_le
  rw [mkAppData_eq, mkAppData', if_pos hm]
  generalize (mixHash fData aData).toUInt32 = hash
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · simp [flagAt, Data.hasFVar_eq_getLsbD]
  · simp [flagAt, Data.hasExprMVar_eq_getLsbD]
  · simp [flagAt, Data.hasLevelMVar_eq_getLsbD]
  · simp [flagAt, Data.hasLevelParam_eq_getLsbD]

private theorem mkAppData_hasFVar :
    (mkAppData fData aData).hasFVar = (fData.hasFVar || aData.hasFVar) := by
  rw [Data.hasFVar_eq_getLsbD]
  exact mkAppData_flag 0 (by decide)

private theorem mkAppData_hasExprMVar :
    (mkAppData fData aData).hasExprMVar = (fData.hasExprMVar || aData.hasExprMVar) := by
  rw [Data.hasExprMVar_eq_getLsbD]
  exact mkAppData_flag 1 (by decide)

private theorem mkAppData_hasLevelMVar :
    (mkAppData fData aData).hasLevelMVar = (fData.hasLevelMVar || aData.hasLevelMVar) := by
  rw [Data.hasLevelMVar_eq_getLsbD]
  exact mkAppData_flag 2 (by decide)

private theorem mkAppData_hasLevelParam :
    (mkAppData fData aData).hasLevelParam = (fData.hasLevelParam || aData.hasLevelParam) := by
  rw [Data.hasLevelParam_eq_getLsbD]
  exact mkAppData_flag 3 (by decide)

private theorem binder_looseBVarRange_le (ty body : Expr) :
    max ty.data.looseBVarRange.toNat (body.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
  have hty := Data.looseBVarRange_le (d := ty.data)
  have hbody := Data.looseBVarRange_le (d := body.data)
  omega

private theorem let_looseBVarRange_le (ty val body : Expr) :
    max (max ty.data.looseBVarRange.toNat val.data.looseBVarRange.toNat)
      (body.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
  have hty := Data.looseBVarRange_le (d := ty.data)
  have hval := Data.looseBVarRange_le (d := val.data)
  have hbody := Data.looseBVarRange_le (d := body.data)
  omega

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

/-- The cached `hasFVar` bit agrees with structural traversal. -/
theorem hasFVar_eq (e : Expr) : e.hasFVar = e.hasFVar' := by
  change e.data.hasFVar = e.hasFVar'
  induction e with
  | bvar => simp [Expr.data, hasFVar', mkData_hasFVar_of_false]
  | fvar | mvar | sort | const | lit =>
    simp only [Expr.data, hasFVar']
    apply mkData_hasFVar
    omega
  | app _ _ ih1 ih2 =>
    simp only [Expr.data, hasFVar']
    rw [mkAppData_hasFVar, ih1, ih2]
  | lam _ ty body _ ihty ihbody | forallE _ ty body _ ihty ihbody =>
    simp only [Expr.data, mkDataForBinder, hasFVar']
    rw [mkData_hasFVar (binder_looseBVarRange_le ty body), ihty, ihbody]
  | letE _ ty val body _ ihty ihval ihbody =>
    simp only [Expr.data, mkDataForLet, hasFVar']
    rw [mkData_hasFVar (let_looseBVarRange_le ty val body), ihty, ihval, ihbody]
  | mdata _ e ih | proj _ _ e ih =>
    simp only [Expr.data, hasFVar']
    rw [mkData_hasFVar (Data.looseBVarRange_le (d := e.data)), ih]

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

/-- The cached `hasExprMVar` bit agrees with structural traversal. -/
@[simp] theorem hasExprMVar_eq (e : Expr) : e.hasExprMVar = e.hasExprMVar' := by
  change e.data.hasExprMVar = e.hasExprMVar'
  induction e with
  | bvar => simp [Expr.data, hasExprMVar', mkData_hasExprMVar_of_false]
  | fvar | mvar | sort | const | lit =>
    simp only [Expr.data, hasExprMVar']
    apply mkData_hasExprMVar
    omega
  | app _ _ ih1 ih2 =>
    simp only [Expr.data, hasExprMVar']
    rw [mkAppData_hasExprMVar, ih1, ih2]
  | lam _ ty body _ ihty ihbody | forallE _ ty body _ ihty ihbody =>
    simp only [Expr.data, mkDataForBinder, hasExprMVar']
    rw [mkData_hasExprMVar (binder_looseBVarRange_le ty body), ihty, ihbody]
  | letE _ ty val body _ ihty ihval ihbody =>
    simp only [Expr.data, mkDataForLet, hasExprMVar']
    rw [mkData_hasExprMVar (let_looseBVarRange_le ty val body), ihty, ihval, ihbody]
  | mdata _ e ih | proj _ _ e ih =>
    simp only [Expr.data, hasExprMVar']
    rw [mkData_hasExprMVar (Data.looseBVarRange_le (d := e.data)), ih]

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

/-- The cached `hasLevelMVar` bit agrees with structural traversal. -/
@[simp] theorem hasLevelMVar_eq (e : Expr) : e.hasLevelMVar = e.hasLevelMVar' := by
  change e.data.hasLevelMVar = e.hasLevelMVar'
  induction e with
  | bvar => simp [Expr.data, hasLevelMVar', mkData_hasLevelMVar_of_false]
  | fvar | mvar | sort | const | lit =>
    simp only [Expr.data, hasLevelMVar']
    apply mkData_hasLevelMVar
    omega
  | app _ _ ih1 ih2 =>
    simp only [Expr.data, hasLevelMVar']
    rw [mkAppData_hasLevelMVar, ih1, ih2]
  | lam _ ty body _ ihty ihbody | forallE _ ty body _ ihty ihbody =>
    simp only [Expr.data, mkDataForBinder, hasLevelMVar']
    rw [mkData_hasLevelMVar (binder_looseBVarRange_le ty body), ihty, ihbody]
  | letE _ ty val body _ ihty ihval ihbody =>
    simp only [Expr.data, mkDataForLet, hasLevelMVar']
    rw [mkData_hasLevelMVar (let_looseBVarRange_le ty val body), ihty, ihval, ihbody]
  | mdata _ e ih | proj _ _ e ih =>
    simp only [Expr.data, hasLevelMVar']
    rw [mkData_hasLevelMVar (Data.looseBVarRange_le (d := e.data)), ih]

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

/-- The cached `hasLevelParam` bit agrees with structural traversal. -/
@[simp] theorem hasLevelParam_eq (e : Expr) : e.hasLevelParam = e.hasLevelParam' := by
  change e.data.hasLevelParam = e.hasLevelParam'
  induction e with
  | bvar => simp [Expr.data, hasLevelParam', mkData_hasLevelParam_of_false]
  | fvar | mvar | sort | const | lit =>
    simp only [Expr.data, hasLevelParam']
    apply mkData_hasLevelParam
    omega
  | app _ _ ih1 ih2 =>
    simp only [Expr.data, hasLevelParam']
    rw [mkAppData_hasLevelParam, ih1, ih2]
  | lam _ ty body _ ihty ihbody | forallE _ ty body _ ihty ihbody =>
    simp only [Expr.data, mkDataForBinder, hasLevelParam']
    rw [mkData_hasLevelParam (binder_looseBVarRange_le ty body), ihty, ihbody]
  | letE _ ty val body _ ihty ihval ihbody =>
    simp only [Expr.data, mkDataForLet, hasLevelParam']
    rw [mkData_hasLevelParam (let_looseBVarRange_le ty val body), ihty, ihval, ihbody]
  | mdata _ e ih | proj _ _ e ih =>
    simp only [Expr.data, hasLevelParam']
    rw [mkData_hasLevelParam (Data.looseBVarRange_le (d := e.data)), ih]

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

end Expr
