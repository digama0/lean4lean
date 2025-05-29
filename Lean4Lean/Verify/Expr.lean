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

theorem liftLooseBVars_eq_self : e.realLooseBVarRange ≤ s → liftLooseBVars' e s d = e := by
  induction e generalizing s <;>
    simp +contextual [*, realLooseBVarRange, liftLooseBVars', Nat.max_le, Nat.le_add_of_sub_le]
  omega

@[simp] theorem liftLooseBVars_zero : liftLooseBVars' e s 0 = e := by
  induction e generalizing s <;> simp [*, liftLooseBVars']

theorem liftLooseBVars_liftLooseBVars {e : Expr} {n1 n2 k1 k2 : Nat}
    (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    liftLooseBVars' (liftLooseBVars' e k1 n1) k2 n2 = liftLooseBVars' e k1 (n1+n2) := by
  induction e generalizing k1 k2 with simp [liftLooseBVars', ← Nat.add_assoc, *]
  | bvar i =>
    split <;> rename_i h
    · rw [if_pos (Nat.lt_of_lt_of_le h h1)]
    · rw [if_neg (by omega), Nat.add_assoc]

theorem liftLooseBVars_add {e : Expr} {n1 n2 k : Nat} :
    liftLooseBVars' (liftLooseBVars' e k n1) k n2 = liftLooseBVars' e k (n1+n2) := by
  induction e generalizing k with simp [liftLooseBVars', Nat.add_assoc, *]
  | bvar i =>
    split; · rfl
    rw [if_neg (by omega), Nat.add_assoc]

theorem liftLooseBVars_comm (e : Expr) (n1 n2 k1 k2 : Nat) (h : k2 ≤ k1) :
    liftLooseBVars' (liftLooseBVars' e k1 n1) k2 n2 =
    liftLooseBVars' (liftLooseBVars' e k2 n2) (n2+k1) n1 := by
  induction e generalizing k1 k2 with
    simp [liftLooseBVars', Nat.add_assoc, Nat.succ_le_succ, *]
  | bvar i =>
    split <;> rename_i h'
    · rw [if_pos (c := _ < n2 + k1)]; split
      · exact Nat.lt_add_left _ h'
      · omega
    · have := mt (Nat.lt_of_lt_of_le · h) h'
      rw [if_neg (by omega), if_neg this, if_neg (by omega), Nat.add_right_comm]

theorem instantiate1'_go_eq_self : e.realLooseBVarRange ≤ k → instantiate1'.go a e k = e := by
  induction e generalizing k <;>
    simp +contextual [*, realLooseBVarRange, instantiate1'.go, Nat.max_le, Nat.le_add_of_sub_le]
  omega

theorem instantiate1'_eq_self (H : e.realLooseBVarRange = 0) : instantiate1' e a = e :=
  instantiate1'_go_eq_self (Nat.le_zero.2 H)

theorem instantiateList_eq_self (h : e.realLooseBVarRange = 0) : instantiateList e as = e := by
  induction as <;> simp [instantiateList, instantiate1'_go_eq_self, *]

theorem instantiate1'_go_liftLooseBVars :
    instantiate1'.go a (liftLooseBVars' e s (d + 1)) (s + d) = e.liftLooseBVars' s d := by
  induction e generalizing s <;>
    simp [*, instantiate1'.go, liftLooseBVars', Nat.add_right_comm _ _ 1]
  rename_i i; split; · simp; omega
  · rw [if_neg (by omega), if_neg (by omega)]; rfl

theorem instantiate1'_go_liftLooseBVars_0 (e1 e2 : Expr) :
    instantiate1'.go e2 (liftLooseBVars' e1 k 1) k = e1 :=
  (instantiate1'_go_liftLooseBVars (d := 0)).trans liftLooseBVars_zero

theorem instantiate1'_instantiate1'_go (e1 e2 e3 j) :
    instantiate1'.go e3 (instantiate1'.go e2 e1 (j+1)) j =
    instantiate1'.go e2 (instantiate1'.go (e3.liftLooseBVars' 0 1) e1 j) j := by
  induction e1 generalizing j with simp [liftLooseBVars', instantiate1'.go, *]
  | bvar i => ?_
  | _ => rename_i IH; exact IH (j+1)
  split <;> rename_i h
  · split <;> rename_i h1
    · simp [instantiate1'.go, h1]
    split <;> rename_i h1'
    · subst i
      simp [instantiate1'.go]; rw [liftLooseBVars_comm (h := Nat.zero_le _)]
      exact (instantiate1'_go_liftLooseBVars_0 ..).symm
    · have hj := Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1')
      let i+1 := i
      simp [instantiate1'.go, h1, h1', Nat.lt_of_succ_lt_succ h]
  split <;> rename_i h'
  · subst i
    rw [if_neg (by omega), if_neg (by omega)]
    simp [instantiate1'.go]
    suffices liftLooseBVars' _ _ (j+1) = _ by
      rw [this]; exact instantiate1'_go_liftLooseBVars_0 ..
    exact (liftLooseBVars_liftLooseBVars (Nat.zero_le _) (Nat.le_refl _)).symm
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    have hk := Nat.lt_of_add_lt_add_right hk
    simp [instantiate1'.go, hk]
    -- have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [instantiate1'.go]
    rw [if_neg (Nat.lt_asymm hk), if_neg (Nat.ne_of_gt hk)]

theorem instantiateList_append :
    instantiateList e (es₁ ++ es₂) k = instantiateList (instantiateList e es₁ k) es₂ k := by
  induction es₁ generalizing e <;> simp [*]

theorem instantiateList_lam : instantiateList (.lam n ty body bi) as =
    .lam n (instantiateList ty as) (instantiateList body as 1) bi := by
  induction as generalizing ty body <;> simp [instantiate1'.go, *]

theorem instantiateList_instantiate1_comm (h : a.realLooseBVarRange = 0) :
    (instantiateList e as 1).instantiate1' a =
    instantiateList (e.instantiate1' a) as := by
  induction as generalizing e <;> simp [instantiate1'.go, *]
  congr 1; refine (instantiate1'_instantiate1'_go (j := 0) ..).trans ?_
  rw [liftLooseBVars_eq_self (by simp [h])]; rfl

theorem instantiateRev_push {e : Expr} {subst a} :
    instantiateRev' e (subst.push a) = instantiateRev' (e.instantiate1' a) subst := by
  let ⟨subst⟩ := subst; simp [instantiateRev', instantiate', instantiateList, instantiate1']

theorem abstractList_eq_foldl {e : Expr} {as k} :
    abstractList e as k = List.foldl (abstract1 · · k) e as := by
  induction as generalizing e <;> simp_all

theorem abstractRevList_eq_foldr {e : Expr} {as k} :
    abstractRevList e as k = List.foldr (fun a e => abstract1 e a k) e as := by
  induction as <;> simp_all

theorem abstractList_reverse {e : Expr} {as k} :
    abstractList e as.reverse k = abstractRevList e as k := by
  simp [abstractList_eq_foldl, abstractRevList_eq_foldr]

theorem abstractRevList_reverse {e : Expr} {as k} :
    abstractRevList e as.reverse k = abstractList e as k := by
  simp [abstractList_eq_foldl, abstractRevList_eq_foldr]

theorem abstractList_append {e : Expr} {as k} :
    abstractList e (as ++ as') k = abstractList (abstractList e as k) as' k := by
  simp [abstractList_eq_foldl]

theorem abstractFVar_comm {e : Expr} {k} (h : a ≠ b) :
    abstractFVar a (abstractFVar b e k) k =
    abstractFVar b (abstractFVar a e k) (k+1) := by
  induction e generalizing k with simp_all [abstractFVar]
  | bvar => split <;> [rw [if_pos]; simp [*]] <;> omega
  | fvar => split <;> split <;> simp_all [abstractFVar]

theorem abstractFVar_abstractList {e : Expr} {as : List FVarId} {k} (H : a ∉ as) :
    abstractFVar a (abstractList e (as.map .fvar) k) k =
    abstractList (abstractFVar a e k) (as.map .fvar) (k+1) := by
  induction as generalizing e <;> simp_all [abstract1, abstractFVar_comm]

theorem abstractFVar_abstractList' {e : Expr} {as : List FVarId} {k} (H : (a :: as).Nodup) :
    abstractFVar a (abstractList e (as.map .fvar) k) (k + as.length) =
    abstractList (abstractFVar a e k) (as.map .fvar) k := by
  induction as generalizing e a with
  | nil => simp
  | cons b as ih =>
    simp [abstract1] at *; simp [H] at ih
    rw [← ih H.2.1, ← Nat.add_assoc, ← abstractFVar_comm (.symm H.1.1), ih H.1.2, ih H.2.1]

theorem abstractFVar_hasLooseBVar (a e k i) :
    (abstractFVar a e k).hasLooseBVar' (if i < k then i else i+1) =
    e.hasLooseBVar' i := by
  have (i k) : (if i < k then i else i + 1) + 1 = if i + 1 < k + 1 then i + 1 else i + 1 + 1 := by
    simp; split <;> rfl
  induction e generalizing i k with simp only [hasLooseBVar', abstractFVar, *]
  | bvar j =>
    by_cases h : j = i <;> simp [h]
    split <;> split <;> omega
  | fvar b =>
    split <;> simp [hasLooseBVar']
    split <;> omega

theorem abstractFVar_lower {e : Expr} (h : e.hasLooseBVar' k₁ = false) (hk : k₁ ≤ k₂) :
    Expr.abstractFVar a (e.lowerLooseBVars' (k₁ + 1) 1) k₂ =
    (Expr.abstractFVar a e (k₂ + 1)).lowerLooseBVars' (k₁ + 1) 1 := by
  induction e generalizing k₁ k₂ with simp_all [abstractFVar, lowerLooseBVars', hasLooseBVar']
  | bvar i =>
    split <;> [skip; split]
    · rw [if_pos (c := i < k₂ + 1) (by omega), if_pos (by omega)]; simp [*]
    · rw [if_pos (c := i < _) (by omega)]; simp [*]
    · rw [if_neg (c := i < _) (by omega), if_neg (by omega)]; omega
  | fvar b =>
    split <;> simp [lowerLooseBVars']
    rw [if_neg (by omega)]
