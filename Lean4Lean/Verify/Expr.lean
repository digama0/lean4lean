import Lean4Lean.Std.Basic
import Lean4Lean.Verify.Axioms
import Lean4Lean.Expr
import Lean4Lean.Instantiate
import Lean

namespace Lean
namespace Expr

theorem mkData_looseBVarRange (H : br ≤ 2^20 - 1) :
    (mkData h br d fv ev lv lp).looseBVarRange.toNat = br := by
  rw [mkData, if_pos H]; dsimp only [Data.looseBVarRange, -Nat.reducePow]
  have : br.toUInt64.toUInt32.toNat = br := by simp; omega
  refine .trans ?_ this; congr 2
  refine UInt64.eq_of_toBitVec_eq ?_
  have : br.toUInt64.toNat = br := by simp; omega
  have : br.toUInt64.toBitVec ≤ 0xfffff#64 := (this ▸ H :)
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 :=
    show h.toUInt32.toNat ≤ 2^32-1 by simp; omega
  have : (if d > 255 then 255 else d.toUInt8).toUInt64.toBitVec ≤ 0xff#64 :=
    Nat.le_of_lt_succ (if d > 255 then 255 else d.toUInt8).1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb fv; have := hb ev; have := hb lv; have := hb lp
  change
    (h.toUInt32.toUInt64.toBitVec +
      (if d > 255 then 255 else d.toUInt8).toUInt64.toBitVec <<< 32#64 +
      fv.toUInt64.toBitVec <<< 40#64 +
      ev.toUInt64.toBitVec <<< 41#64 +
      lv.toUInt64.toBitVec <<< 42#64 +
      lp.toUInt64.toBitVec <<< 43#64 +
      br.toUInt64.toBitVec <<< 44#64) >>> 44#64 =
    br.toUInt64.toBitVec
  bv_decide

theorem Data.looseBVarRange_le : (Data.looseBVarRange d).toNat ≤ 2^20 - 1 := by
  rw [Data.looseBVarRange]
  suffices (UInt64.shiftRight d 44).toNat ≤ 2 ^ 20 - 1 by simp; omega
  show d.toBitVec >>> 44#64 ≤ 0xfffff#64
  bv_decide

theorem looseBVarRange_le : looseBVarRange e ≤ 2^20 - 1 := Data.looseBVarRange_le

theorem _root_.UInt32.max_toNat (a b : UInt32) : (max a b).toNat = max a.toNat b.toNat := by
  simp only [instMaxUInt32, maxOfLe, UInt32.le_iff_toNat_le, Nat.instMax]; split <;> rfl

theorem mkAppData_looseBVarRange :
    (mkAppData fData aData).looseBVarRange = max fData.looseBVarRange aData.looseBVarRange := by
  have hm : max fData.looseBVarRange aData.looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32 := by
    dsimp [instMaxUInt32, maxOfLe]; split <;> exact Data.looseBVarRange_le
  rw [mkAppData, if_pos hm]
  simp [Data.looseBVarRange] at hm
  dsimp only [Data.looseBVarRange, -Nat.reducePow]
  generalize (max .. : UInt32) = m at *
  have : m.toUInt64.toUInt32 = m := by simp [UInt64.toUInt32]
  refine .trans ?_ this; congr 2
  generalize (ite (_ > (255 : UInt16)) _ _ : UInt8) = a
  generalize HOr.hOr (α := UInt64) fData _ = b
  generalize UInt64.toUInt32 _ = c
  apply UInt64.eq_of_toBitVec_eq
  change m.toUInt64.toBitVec ≤ 0xfffff#64 at hm
  have : c.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ c.1.1.2
  have : a.toUInt64.toBitVec ≤ 0xff#64 := Nat.le_of_lt_succ a.1.1.2
  change
    (b.toBitVec &&& 15#64 <<< 40#64 |||
      c.toUInt64.toBitVec |||
      a.toUInt64.toBitVec <<< 32#64 |||
      m.toUInt64.toBitVec <<< 44#64) >>> 44#64 =
    m.toUInt64.toBitVec
  bv_decide

theorem Safe.looseBVarRange_eq :
    ∀ {e}, Safe e → e.looseBVarRange = e.realLooseBVarRange
  | .bvar i, e => by simp [looseBVarRange, data]; rw [mkData_looseBVarRange e]; rfl
  | .const .., _
  | .sort _, _
  | .fvar _, _
  | .mvar _, _
  | .lit _, _ => mkData_looseBVarRange (Nat.zero_le _)
  | .mdata _ e, h
  | .proj _ _ e, h =>
    (mkData_looseBVarRange looseBVarRange_le).trans <| h.looseBVarRange_eq (e := e)
  | .app e1 e2, ⟨h1, h2⟩ => by
    simp [looseBVarRange, Expr.data, mkAppData_looseBVarRange, UInt32.max_toNat,
      realLooseBVarRange, ← h1.looseBVarRange_eq, ← h2.looseBVarRange_eq]
  | .lam _ e1 e2 _, ⟨h1, h2⟩
  | .forallE _ e1 e2 _, ⟨h1, h2⟩ => by
    simp [looseBVarRange, Expr.data, Expr.mkDataForBinder, realLooseBVarRange]
    rw [mkData_looseBVarRange, ← h1.looseBVarRange_eq, ← h2.looseBVarRange_eq]; · rfl
    exact Nat.max_le.2 ⟨looseBVarRange_le, Nat.le_trans (Nat.sub_le ..) looseBVarRange_le⟩
  | .letE _ e1 e2 e3 _, ⟨h1, h2, h3⟩ => by
    simp [looseBVarRange, Expr.data, Expr.mkDataForLet, realLooseBVarRange]
    rw [mkData_looseBVarRange, ← h1.looseBVarRange_eq, ← h2.looseBVarRange_eq,
      ← h3.looseBVarRange_eq]; · rfl
    exact Nat.max_le.2 ⟨
      Nat.max_le.2 ⟨looseBVarRange_le, looseBVarRange_le⟩,
      Nat.le_trans (Nat.sub_le ..) looseBVarRange_le⟩

theorem Safe.getAppFn {e} (h : Safe e) : Safe e.getAppFn := by
  unfold Expr.getAppFn; split
  · exact h.1.getAppFn
  · exact h

def getAppArgsRevList : Expr → List Expr
  | .app f a => a :: f.getAppArgsRevList
  | _ => []

open private getAppNumArgsAux getAppArgsAux mkAppRangeAux from Lean.Expr

theorem getAppNumArgs_eq : getAppNumArgs e = (getAppArgsRevList e).length := by
  let rec loop e n : getAppNumArgsAux e n = (getAppArgsRevList e).length + n := by
    unfold getAppNumArgsAux getAppArgsRevList; split <;> simp
    rw [loop]; omega
  rw [getAppNumArgs, loop]; rfl

theorem getAppArgs_toList : (getAppArgs e).toList = (getAppArgsRevList e).reverse := by
  let rec loop {e l₁ l₂ args} (h1 : args.toList = l₁ ++ l₂) :
      l₁.length = (getAppArgsRevList e).length →
      (getAppArgsAux e args ((getAppArgsRevList e).length - 1)).toList =
      (getAppArgsRevList e).reverse ++ l₂ := by
    unfold getAppArgsAux getAppArgsRevList; split
    · rename_i f a; intro h2
      obtain rfl | ⟨l₁, u, rfl⟩ := List.eq_nil_or_concat l₁; · cases h2
      simp at h2 ⊢; refine loop ?_ h2
      simp [← h2, h1]
    · simp; rintro ⟨⟩; simpa using h1
  simp [getAppArgs, getAppNumArgs_eq]
  exact (loop (List.append_nil _).symm (by simp)).trans (by simp)

theorem getAppArgs_eq : getAppArgs e = (getAppArgsRevList e).reverse.toArray := by
  simp [← getAppArgs_toList]

@[simp] def mkAppRevList : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => .app (mkAppRevList e as) a

theorem mkAppRevList_eq_foldr : mkAppRevList e es = es.foldr (fun a e => .app e a) e := by
  induction es <;> simp [mkAppRevList, *]

@[simp] theorem mkAppRevList_append :
    mkAppRevList e (es₁ ++ es₂) = mkAppRevList (mkAppRevList e es₂) es₁ := by
  simp [mkAppRevList_eq_foldr]

theorem mkAppRevList_getAppArgsRevList (e) :
    mkAppRevList e.getAppFn (getAppArgsRevList e) = e := by
  unfold getAppFn getAppArgsRevList; split <;> simp
  congr 1; exact mkAppRevList_getAppArgsRevList _

theorem mkAppRange_eq (h1 : args.toList = l₁ ++ l₂ ++ l₃)
    (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = j) :
    mkAppRange e i j args = mkAppRevList e l₂.reverse := loop h1 h2 h3 where
  loop {n i e l₁ l₂} (h1 : args.toList = l₁ ++ l₂ ++ l₃)
      (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = n) :
      mkAppRangeAux n args i e = mkAppRevList e l₂.reverse := by
    rw [mkAppRangeAux.eq_def]; split
    · simp [Array.get!, ← Array.getElem?_toList, h1]
      obtain _ | ⟨a, l₂⟩ := l₂; · simp_all
      rw [List.getElem?_append_right (by simp [h2])]
      simp [h2]
      rw [loop (l₁ := l₁ ++ [a]) (l₂ := l₂)] <;> simp [h1, h2, h3, mkApp]
    · simp at h3
      have : l₂.length = 0 := by omega
      simp at this; simp [this]

@[simp] def instantiateList : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => instantiateList (e.instantiate1' a) as
