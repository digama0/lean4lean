import Lean4Lean.Std.Basic
import Lean4Lean.Verify.Axioms
import Lean4Lean.Verify.Level
import Lean4Lean.Expr
import Lean4Lean.Instantiate
import Batteries.Data.String.Lemmas
import Std.Tactic.BVDecide

namespace Lean

namespace Name
open Std

instance : TransCmp Name.quickCmp where
  eq_swap {a b} := by
    simp [quickCmp]
    rw [OrientedOrd.eq_swap]
    cases compare b.hash a.hash <;> simp
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      rw [OrientedOrd.eq_swap]
      cases compare b₂ a₂ <;> simp [ih]
  isLE_trans {a b c} := by
    have {α} [Ord α] [TransOrd α] {a₁ b₁ c₁ : α} {a₂ b₂ c₂}
        (H : (quickCmpAux a₂ b₂).isLE → (quickCmpAux b₂ c₂).isLE → (quickCmpAux a₂ c₂).isLE) :
        ((compare a₁ b₁).then (quickCmpAux a₂ b₂)).isLE →
        ((compare b₁ c₁).then (quickCmpAux b₂ c₂)).isLE →
        ((compare a₁ c₁).then (quickCmpAux a₂ c₂)).isLE := by
      simp [Ordering.isLE_then_iff_and]
      intro h1 h2 h3 h4
      refine ⟨TransCmp.isLE_trans h1 h3, ?_⟩
      refine h2.elim (fun h2 => .inl <| TransCmp.lt_of_lt_of_isLE h2 h3) fun h2 => ?_
      refine h4.elim (fun h4 => .inl <| TransCmp.lt_of_isLE_of_lt h1 h4) fun h4 => .inr (H h2 h4)
    apply this
    induction a generalizing b c with
      obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux] at * <;>
      obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;> simp [quickCmpAux] at *
    | str a₁ a₂ ih | num a₁ a₂ ih => apply this ih

instance : LawfulBEqCmp Name.quickCmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨fun h => ?_, fun h => h ▸ ReflCmp.compare_self⟩
    replace h := (Ordering.then_eq_eq.1 h).2; revert h
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun _ => ih

end Name

instance : LawfulBEq FVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Name) h; rfl
  rfl := BEq.rfl (α := Name)

instance : LawfulBEq MVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Name) h; rfl
  rfl := BEq.rfl (α := Name)

instance : LawfulBEq LBool where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} := by cases a <;> cases b <;> simp +decide

namespace Substring

open private substrEq.loop from Init.Data.String.Basic in
nonrec theorem beq_symm {s t : Substring} : s == t → t == s := by
  let ⟨s, ⟨b⟩, e⟩ := s
  let ⟨s2, ⟨b2⟩, e2⟩ := t
  simp +contextual [(· == ·), Substring.beq, Substring.bsize, String.substrEq]
  let rec loop {s s' b b' i n} :
      substrEq.loop s s' ⟨b + i⟩ ⟨b' + i⟩ ⟨b + n⟩ ↔
      substrEq.loop s' s ⟨b' + i⟩ ⟨b + i⟩ ⟨b' + n⟩ := by
    unfold substrEq.loop; simp [beq_comm, Decidable.or_iff_not_imp_left]
    refine imp_congr_right fun h1 => and_congr_right fun h2 => ?_
    simp [h2, instHAddPosChar, Nat.add_assoc]
    have := Char.utf8Size_pos (s'.get ⟨b'+i⟩)
    exact Bool.eq_iff_iff.2 loop
  termination_by b + n - (b + i)
  intro h1 h2 h3
  have loop := @loop (i := 0); simp at loop
  simp [loop]

open private substrEq.loop from Init.Data.String.Basic in
nonrec theorem beq_trans {s t : Substring} : s == t → t == u → s == u := by
  let ⟨s, ⟨b⟩, e⟩ := s
  let ⟨s2, ⟨b2⟩, e2⟩ := t
  let ⟨s3, ⟨b3⟩, e3⟩ := u
  simp +contextual [(· == ·), Substring.beq, Substring.bsize, String.substrEq]
  intro h1 h2 h3 h4 h5 h6 h7 h8
  constructor; · omega
  simp [h5] at h4
  let rec loop {s₁ s₂ s₃ b₁ b₂ b₃ i n} :
      (h : substrEq.loop s₁ s₂ ⟨b₁ + i⟩ ⟨b₂ + i⟩ ⟨b₁ + n⟩) →
      (substrEq.loop s₁ s₃ ⟨b₁ + i⟩ ⟨b₃ + i⟩ ⟨b₁ + n⟩ ↔
       substrEq.loop s₂ s₃ ⟨b₂ + i⟩ ⟨b₃ + i⟩ ⟨b₂ + n⟩) := by
    unfold substrEq.loop; simp [Decidable.or_iff_not_imp_left]
    refine fun h1 => imp_congr_right fun h => ?_; let ⟨h1, h2⟩ := h1 h
    simp [h1]; intro h3; simp [h1, h3, instHAddPosChar, Nat.add_assoc] at h2 ⊢
    have := Char.utf8Size_pos (s₃.get ⟨b₃+i⟩)
    refine Bool.eq_iff_iff.2 (loop h2)
  termination_by n - i
  have loop := @loop (i := 0) (h := h4); simp at loop
  simpa [loop] using h8

instance : EquivBEq Substring where
  symm := beq_symm
  trans := beq_trans
  rfl := beq_refl _

end Substring

namespace Syntax

namespace Preresolved

protected theorem beq_iff_eq {m n : Preresolved} : m == n ↔ m = n := by
  simp only [(· == ·)]; cases m <;> cases n <;> simp! <;> grind only [cases Or]

instance : LawfulBEq Preresolved where
  eq_of_beq := Preresolved.beq_iff_eq.1
  rfl := Preresolved.beq_iff_eq.2 rfl

instance : DecidableEq Preresolved :=
  fun a b => if h : a == b then .isTrue (by simp_all) else .isFalse (by simp_all)

end Preresolved

theorem structEq_refl (s : Syntax) : s.structEq' s := by
  unfold structEq'
  cases s with
  | node i k args =>
    let ⟨args⟩ := args; simp; intro x _ _ _
    have IH := structEq_refl x
    induction args.attach <;> simp
    rintro (⟨rfl, ⟨⟩⟩ | h) <;> [skip; solve_by_elim]
    simpa using IH
  | _ => simp

attribute [-simp] List.all_eq_true in
theorem structEq_euc {s : Syntax} (H : s.structEq' t) : s.structEq' u = t.structEq' u := by
  unfold structEq' at H; split at H
  case h_1 => simp
  case h_5 => cases H
  all_goals
    revert H; simp; intros; subst_vars
    unfold structEq'; cases u <;> simp <;> rw [Bool.eq_iff_iff] <;> simp [*]
  -- all_goals intros; subst_vars
  case ident => intros; apply BEq.congr_left ‹_›
  case node args₁ _ _ args₂ eq H _ _ args₃ =>
    rintro rfl eq'; revert H
    have IH {a} (h : a ∈ args₁) := @structEq_euc (s := a)
    let ⟨args₁⟩ := args₁; let ⟨args₂⟩ := args₂; let ⟨args₃⟩ := args₃
    revert eq eq'; simp at IH ⊢
    simp only [← args₁.length_attach, ← args₂.length_attach, ← args₃.length_attach]
    generalize args₁.attach = l₁, args₂.attach = l₂, args₃.attach = l₃
    induction l₁ generalizing l₂ l₃ with cases l₂ <;> simp <;> cases l₃ <;> simp | cons a l₁ ih
    intros _ _ H; rw [IH a.2 _ _ H, Bool.eq_iff_iff]; simp [*]; grind
termination_by s

theorem structEq_symm {s : Syntax} (H : s.structEq' t) : t.structEq' s :=
  structEq_euc H ▸ structEq_refl _

theorem structEq_trans {s : Syntax} (H : s.structEq' t) (H2 : t.structEq' u) : s.structEq' u :=
  structEq_euc H ▸ H2

theorem beq_def : (a == b) = structEq' a b := structEq_eq

instance : EquivBEq Syntax where
  symm := by simp [beq_def]; exact structEq_symm
  trans := by simp [beq_def]; exact structEq_trans
  rfl := by simp [beq_def]; exact structEq_refl _

end Syntax

namespace DataValue

instance : EquivBEq DataValue where
  symm {a b} := by simp [(· == ·)]; cases a <;> cases b <;> simp! [beq_comm]
  trans {a b c} := by
    simp [(· == ·)]; cases a <;> cases b <;> simp! [beq_comm] <;> try rintro rfl; simp
    cases c <;> simp!; exact BEq.trans
  rfl {a} := by simp [(· == ·)]; cases a <;> simp!

end DataValue

namespace Literal
open Expr in
theorem toConstructor_hasLevelParam :
    (Literal.toConstructor l).hasLevelParam' = false := by
  cases l with simp [Literal.toConstructor]
  | natVal n => cases n <;> simp [natLitToConstructor, hasLevelParam', natZero, natSucc]
  | strVal s =>
    let ⟨l⟩ := s
    simp [strLitToConstructor, hasLevelParam', String.foldr_eq]
    induction l <;> simp_all [hasLevelParam', Level.hasParam']

protected theorem beq_iff_eq {m n : Literal} : m == n ↔ m = n := by
  cases m <;> cases n <;> simp! [(· == ·)]

instance : LawfulBEq Literal where
  eq_of_beq := Literal.beq_iff_eq.1
  rfl := Literal.beq_iff_eq.2 rfl

instance : DecidableEq Literal :=
  fun a b => if h : a == b then .isTrue (by simp_all) else .isFalse (by simp_all)

@[simp] theorem mkConst_typeName {l : Literal} : .const l.typeName [] = l.type := by
  cases l <;> simp [typeName, type, mkConst]

end Literal

namespace Expr

attribute [simp] mkConst mkBVar mkSort mkFVar mkMVar mkMData mkProj mkApp mkLambda mkForall mkLet
  updateApp! updateFVar! updateConst! updateSort! updateMData! updateProj!
  updateForall! updateForallE! updateLambda! updateLambdaE! updateLetE! updateLet!

theorem mkData_looseBVarRange (H : br ≤ 2^20 - 1) :
    (mkData h br d fv ev lv lp).looseBVarRange.toNat = br := by
  rw [mkData_eq, mkData', if_pos H]; dsimp only [Data.looseBVarRange, -Nat.reducePow]
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
  rw [mkAppData_eq, mkAppData', if_pos hm]
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

def getAppArgsList : Expr → (r : List Expr := []) → List Expr
  | .app f a, r => f.getAppArgsList (a :: r)
  | _, r => r

def getAppArgsRevList : Expr → List Expr
  | .app f a => a :: f.getAppArgsRevList
  | _ => []

theorem getAppArgsRevList_reverse : (getAppArgsRevList e).reverse = getAppArgsList e := by
  let rec loop {e r} : getAppArgsList e r = (getAppArgsRevList e).reverse ++ r := by
    unfold getAppArgsList getAppArgsRevList; split <;> simp; exact loop
  simp [loop]

theorem getAppArgsList_reverse : (getAppArgsList e).reverse = getAppArgsRevList e := by
  rw [← getAppArgsRevList_reverse]; simp

open private getAppNumArgsAux getAppArgsAux mkAppRangeAux from Lean.Expr

theorem getAppNumArgs_eq : getAppNumArgs e = (getAppArgsRevList e).length := by
  let rec loop e n : getAppNumArgsAux e n = (getAppArgsRevList e).length + n := by
    unfold getAppNumArgsAux getAppArgsRevList; split <;> simp
    rw [loop]; omega
  rw [getAppNumArgs, loop]; rfl

theorem getAppArgs_toList_rev : (getAppArgs e).toList = (getAppArgsRevList e).reverse := by
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

theorem getAppArgs_toList : (getAppArgs e).toList = getAppArgsList e := by
  rw [getAppArgs_toList_rev, getAppArgsRevList_reverse]

theorem getAppArgs_eq_rev : getAppArgs e = (getAppArgsRevList e).reverse.toArray := by
  simp [← getAppArgs_toList_rev]

theorem getAppArgs_eq : getAppArgs e = (getAppArgsList e).toArray := by
  simp [← getAppArgs_toList]

open private getAppRevArgsAux from Lean.Expr in
theorem getAppRevArgs_toList : (getAppRevArgs e).toList = getAppArgsRevList e := by
  simp [getAppRevArgs, loop]
where
  loop {e args} : (getAppRevArgsAux e args).toList = args.toList ++ getAppArgsRevList e := by
    unfold getAppRevArgsAux getAppArgsRevList; split <;> [(rw [loop]; simp); simp]

theorem getAppRevArgs_eq : getAppRevArgs e = (getAppArgsRevList e).toArray := by
  simp [← getAppRevArgs_toList]

@[simp] theorem withApp_eq {e : Expr} : e.withApp f = f e.getAppFn e.getAppArgs := loop where
  loop {e arr n} : withAppAux f e arr n = f e.getAppFn (getAppArgsAux e arr n) := by
    unfold withAppAux getAppArgsAux; split <;> [exact loop; simp [getAppFn]]

open private withAppRevAux getAppRevArgsAux from Lean.Expr in
@[simp] theorem withRevApp_eq {e : Expr} :
    e.withAppRev f = f e.getAppFn e.getAppRevArgs := loop where
  loop {e arr} : withAppRevAux f e arr = f e.getAppFn (getAppRevArgsAux e arr) := by
    unfold withAppRevAux getAppRevArgsAux; split <;> [exact loop; simp [getAppFn]]

@[simp] def mkAppList : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => mkAppList (.app e a) as

theorem mkAppList_eq_foldl : mkAppList e es = es.foldl .app e := by
  induction es generalizing e <;> simp [mkAppList, *]

@[simp] theorem mkAppList_append :
    mkAppList e (es₁ ++ es₂) = mkAppList (mkAppList e es₁) es₂ := by
  simp [mkAppList_eq_foldl]

@[simp] def mkAppRevList : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => .app (mkAppRevList e as) a

theorem mkAppRevList_eq_foldr : mkAppRevList e es = es.foldr (fun a e => .app e a) e := by
  induction es <;> simp [mkAppRevList, *]

@[simp] theorem mkAppRevList_append :
    mkAppRevList e (es₁ ++ es₂) = mkAppRevList (mkAppRevList e es₂) es₁ := by
  simp [mkAppRevList_eq_foldr]

theorem mkAppList_reverse : mkAppList e es.reverse = mkAppRevList e es := by
  simp [mkAppList_eq_foldl, mkAppRevList_eq_foldr]

theorem mkAppRevList_reverse : mkAppRevList e es.reverse = mkAppList e es := by
  simp [mkAppList_eq_foldl, mkAppRevList_eq_foldr]

theorem mkAppRevList_getAppArgsRevList (e) :
    mkAppRevList e.getAppFn (getAppArgsRevList e) = e := by
  unfold getAppFn getAppArgsRevList; split <;> simp
  congr 1; exact mkAppRevList_getAppArgsRevList _

theorem mkAppList_getAppArgsList (e) :
    mkAppList e.getAppFn (getAppArgsList e) = e := by
  rw [← mkAppRevList_reverse, getAppArgsList_reverse, mkAppRevList_getAppArgsRevList]

theorem mkAppRange_eq (h1 : args.toList = l₁ ++ l₂ ++ l₃)
    (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = j) :
    mkAppRange e i j args = mkAppList e l₂ := loop h1 h2 h3 where
  loop {n i e l₁ l₂} (h1 : args.toList = l₁ ++ l₂ ++ l₃)
      (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = n) :
      mkAppRangeAux n args i e = mkAppList e l₂ := by
    rw [mkAppRangeAux.eq_def]; split
    · simp [Array.getElem!_eq_getD, ← Array.getElem?_toList, h1]
      obtain _ | ⟨a, l₂⟩ := l₂; · simp_all
      rw [List.getElem?_append_right (by simp [h2])]
      simp [h2]
      rw [loop (l₁ := l₁ ++ [a]) (l₂ := l₂)] <;> simp [h1, h2, h3]
    · simp at h3
      have : l₂.length = 0 := by omega
      simp_all

theorem mkAppRange_eq_rev (h1 : args.toList = l₁ ++ l₂ ++ l₃)
    (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = j) :
    mkAppRange e i j args = mkAppRevList e l₂.reverse := by
  rw [mkAppRange_eq h1 h2 h3, mkAppRevList_reverse]

open private mkAppRevRangeAux from Lean.Expr in
theorem mkAppRevRange_eq(h1 : args.toList = l₁ ++ l₂ ++ l₃)
      (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = j) :
    mkAppRevRange e i j args = mkAppList e l₂.reverse := by
  simpa using loop l₁ l₂.reverse l₃ [] (by simpa using h1) h2 (by simpa using h3)
where
  loop {start i} (l₁ l₂ l₃ l₄) (h1 : args.toList = l₁ ++ l₂.reverse ++ l₃)
      (h2 : l₁.length = start) (h3 : l₁.length + List.length l₂ = i) :
      mkAppRevRangeAux args start (mkAppRevList e l₄) i = mkAppList (mkAppRevList e l₄) l₂ := by
    rw [mkAppRevRangeAux.eq_def]; split
    · have : l₂.length = 0 := by omega
      simp_all
    · have : 0 < l₂.length := by omega
      let a::l₂ := l₂; simp [← Nat.add_assoc] at h3
      let i+1 := i; simp at h3
      simp [Array.getElem!_eq_getD, ← Array.getElem?_toList, h1]
      rw [List.getElem?_append_right (by omega)]
      simp at h1; simp [← List.append_assoc] at h1
      simp [← h3]; rw [h3]
      simpa using loop l₁ l₂ (a :: l₃) (a :: l₄) (by simp [h1]) h2 h3

theorem mkAppRevRange_eq_rev (h1 : args.toList = l₁ ++ l₂ ++ l₃)
    (h2 : l₁.length = i) (h3 : (l₁ ++ l₂).length = j) :
    mkAppRevRange e i j args = mkAppRevList e l₂ := by
  rw [mkAppRevRange_eq h1 h2 h3, mkAppList_reverse]

theorem liftLooseBVars_eq_self : e.looseBVarRange' ≤ s → liftLooseBVars' e s d = e := by
  induction e generalizing s <;>
    simp +contextual [*, looseBVarRange', liftLooseBVars', Nat.max_le]
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
  induction e generalizing k with simp [liftLooseBVars', *]
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

theorem liftLooseBVars_looseBVarRange :
    (liftLooseBVars' e k n).looseBVarRange' ≤ e.looseBVarRange' + n := by
  induction e generalizing k <;> simp [*, looseBVarRange', liftLooseBVars'] <;> grind

theorem instantiate1'_looseBVarRange
    (he : e.looseBVarRange' ≤ n + k + 1) (ha : a.looseBVarRange' ≤ n) :
    (instantiate1' e a k).looseBVarRange' ≤ n + k := by
  induction e generalizing k with
    simp_all [looseBVarRange', instantiate1', Nat.max_le]
  | bvar =>
    split <;> [skip; split] <;> try simp [looseBVarRange'] at he ⊢; omega
    have := @liftLooseBVars_looseBVarRange a 0 k; omega
  | _ => grind

theorem instantiateList_looseBVarRange
    (he : e.looseBVarRange' ≤ n + k + as.length) (ha : ∀ a ∈ as, a.looseBVarRange' ≤ n) :
    (instantiateList e as k).looseBVarRange' ≤ n + k := by
  induction as generalizing e with simp_all | cons _ _ ih
  apply ih; rw [Nat.add_right_comm]; apply instantiate1'_looseBVarRange <;> omega

theorem instantiate1'_eq_self : e.looseBVarRange' ≤ k → instantiate1' e a k = e := by
  induction e generalizing k <;>
    simp +contextual [*, looseBVarRange', instantiate1', Nat.max_le]
  omega

theorem instantiate1_eq_self (H : e.looseBVarRange' = 0) : instantiate1' e a = e := by
  simpa using instantiate1'_eq_self (e := e) (Nat.le_zero.2 H)

theorem instantiateList'_eq_self (h : e.looseBVarRange' ≤ k) : instantiateList e as k = e := by
  induction as <;> simp [instantiateList, instantiate1'_eq_self, *]

theorem instantiateList_eq_self (h : e.looseBVarRange' = 0) : instantiateList e as = e := by
  induction as <;> simp [instantiateList, instantiate1_eq_self, *]

theorem instantiate1'_liftLooseBVars :
    instantiate1' (liftLooseBVars' e s (d + 1)) a (s + d) = e.liftLooseBVars' s d := by
  induction e generalizing s <;>
    simp [*, instantiate1', liftLooseBVars', Nat.add_right_comm _ _ 1]
  rename_i i; split; · simp; omega
  · rw [if_neg (by omega), if_neg (by omega)]; rfl

theorem instantiate1'_liftLooseBVars_0 (e1 e2 : Expr) :
    instantiate1' (liftLooseBVars' e1 k 1) e2 k = e1 := by
  simpa using (instantiate1'_liftLooseBVars (d := 0)).trans liftLooseBVars_zero

theorem instantiate1'_instantiate1' (e1 e2 e3 j) :
    instantiate1' (instantiate1' e1 e2 (j+1)) e3 j =
    instantiate1' (instantiate1' e1 (e3.liftLooseBVars' 0 1) j) e2 j := by
  induction e1 generalizing j with simp [instantiate1', *] | bvar i
  split <;> rename_i h
  · split <;> rename_i h1
    · simp [instantiate1', h1]
    split <;> rename_i h1'
    · subst i
      simp [instantiate1']; rw [liftLooseBVars_comm (h := Nat.zero_le _)]
      exact (instantiate1'_liftLooseBVars_0 ..).symm
    · have hj := Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1')
      let i+1 := i
      simp [instantiate1', h1, h1', Nat.lt_of_succ_lt_succ h]
  split <;> rename_i h'
  · subst i
    rw [if_neg (by omega), if_neg (by omega)]
    simp [instantiate1']
    suffices liftLooseBVars' _ _ (j+1) = _ by
      rw [this]; exact instantiate1'_liftLooseBVars_0 ..
    exact (liftLooseBVars_liftLooseBVars (Nat.zero_le _) (Nat.le_refl _)).symm
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    have hk := Nat.lt_of_add_lt_add_right hk
    simp [instantiate1']
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [instantiate1']
    rw [if_neg (Nat.lt_asymm hk), if_neg (Nat.ne_of_gt hk)]

@[simp] def instantiateRevList (e : Expr) : List Expr → (k :_:= 0) → Expr
  | [], _ => e
  | a :: as, k => instantiate1' (instantiateRevList e as k) a k

theorem instantiateList_eq_foldl :
    instantiateList e as k = as.foldl (instantiate1' · · k) e := by
  induction as generalizing e <;> simp [*]

theorem instantiateRevList_eq_foldr :
    instantiateRevList e as k = as.foldr (fun a e => instantiate1' e a k) e := by
  induction as <;> simp [*]

theorem instantiateList_append :
    instantiateList e (es₁ ++ es₂) k = instantiateList (instantiateList e es₁ k) es₂ k := by
  simp [instantiateList_eq_foldl]

theorem instantiateRevList_append :
    instantiateRevList e (es₁ ++ es₂) k =
    instantiateRevList (instantiateRevList e es₂ k) es₁ k := by
  simp [instantiateRevList_eq_foldr]

theorem instantiateList_reverse :
    instantiateList e as.reverse k = instantiateRevList e as k := by
  simp [instantiateList_eq_foldl, instantiateRevList_eq_foldr]

theorem instantiateRevList_reverse :
    instantiateRevList e as.reverse k = instantiateList e as k := by
  simp [instantiateList_eq_foldl, instantiateRevList_eq_foldr]

@[simp]
theorem instantiateRevList_lam : instantiateRevList (.lam n ty body bi) as k =
    .lam n (instantiateRevList ty as k) (instantiateRevList body as (k + 1)) bi := by
  induction as <;> simp [instantiate1', *]

@[simp]
theorem instantiateList_lam : instantiateList (.lam n ty body bi) as k =
    .lam n (instantiateList ty as k) (instantiateList body as (k + 1)) bi := by
  simp [← instantiateRevList_reverse, instantiateRevList_lam]

@[simp]
theorem instantiateRevList_app : instantiateRevList (.app f a) as k =
    .app (instantiateRevList f as k) (instantiateRevList a as k) := by
  induction as <;> simp [instantiate1', *]

@[simp]
theorem instantiateList_app : instantiateList (.app f a) as k =
    .app (instantiateList f as k) (instantiateList a as k) := by
  simp [← instantiateRevList_reverse, instantiateRevList_app]

@[simp]
theorem instantiateList_forallE : instantiateList (.forallE n ty body bi) as k =
    .forallE n (instantiateList ty as k) (instantiateList body as (k + 1)) bi := by
  induction as generalizing ty body <;> simp [instantiate1', *]

@[simp]
theorem instantiateList_letE : instantiateList (.letE n ty val body nd) as k =
    .letE n (instantiateList ty as k) (instantiateList val as k)
      (instantiateList body as (k + 1)) nd := by
  induction as generalizing ty val body <;> simp [instantiate1', *]

theorem instantiateList_instantiate1_comm (h : a.looseBVarRange' = 0) :
    (instantiateList e as 1).instantiate1' a =
    instantiateList (e.instantiate1' a) as := by
  induction as generalizing e <;> simp [*]
  congr 1; refine (instantiate1'_instantiate1' (j := 0) ..).trans ?_
  rw [liftLooseBVars_eq_self (by simp [h])]

theorem instantiateRev_push {e : Expr} {subst a} :
    instantiateRev e (subst.push a) = instantiateRev (e.instantiate1' a) subst := by
  let ⟨subst⟩ := subst; simp [instantiateList]

theorem abstractList_eq_foldl {e : Expr} {as k} :
    abstractList e as k = List.foldl (fun e a => abstract1 a e k) e as := by
  induction as generalizing e <;> simp_all

@[simp] def abstractRevList : Expr → List FVarId → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => abstract1 a (abstractRevList e as k) k

theorem abstractRevList_eq_foldr {e : Expr} {as k} :
    abstractRevList e as k = List.foldr (abstract1 · · k) e as := by
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

theorem abstract1_comm {e : Expr} {k} (h : a ≠ b) :
    abstract1 a (abstract1 b e k) k =
    abstract1 b (abstract1 a e k) (k+1) := by
  induction e generalizing k with simp_all [abstract1]
  | bvar => split <;> [rw [if_pos]; simp [*]] <;> omega
  | fvar => split <;> split <;> simp_all [abstract1]

theorem abstract1_abstractList {e : Expr} {as : List FVarId} {k} (H : a ∉ as) :
    abstract1 a (abstractList e as k) k =
    abstractList (abstract1 a e k) as (k+1) := by
  induction as generalizing e <;> simp_all [abstract1_comm]

theorem abstract1_abstractList' {e : Expr} {as : List FVarId} {k} (H : (a :: as).Nodup) :
    abstract1 a (abstractList e as k) (k + as.length) =
    abstractList (abstract1 a e k) as k := by
  induction as generalizing e a with
  | nil => simp
  | cons b as ih =>
    simp at *; simp [H] at ih
    rw [← ih H.2.1, ← Nat.add_assoc, ← abstract1_comm (.symm H.1.1), ih H.1.2, ih H.2.1]

theorem abstract1_hasLooseBVar (a e k i) :
    (abstract1 a e k).hasLooseBVar' (if i < k then i else i+1) = e.hasLooseBVar' i := by
  have (i) k : (if i < k then i else i + 1) + 1 = if i + 1 < k + 1 then i + 1 else i + 1 + 1 := by
    simp; split <;> rfl
  induction e generalizing i k with simp only [hasLooseBVar', abstract1, *]
  | bvar j =>
    by_cases h : j = i <;> simp [h]
    split <;> split <;> omega
  | fvar b =>
    split <;> simp [hasLooseBVar']
    split <;> omega

theorem abstract1_eq_liftLooseBVars (h : (abstract1 a e k).hasLooseBVar' k = false) :
    abstract1 a e k = liftLooseBVars' e k 1 := by
  induction e generalizing k <;> grind [abstract1, hasLooseBVar', liftLooseBVars']

-- theorem abstract1_looseBVarRange_le :
--     (abstract1 a e k).looseBVarRange' ≤ max k e.looseBVarRange' + 1 := by
--   have H {k a b c d} (h1 : a ≤ max k c + 1) (h2 : b ≤ max k d + 1) :
--       max a b ≤ max k (max c d) + 1 := by
--     rw [Nat.max_le]; simp [Nat.max_def]; split <;> split <;> omega
--   have {k a b c d} (h1 : a ≤ max k c + 1) (h2 : b ≤ max (k+1) d + 1) :
--       max a (b - 1) ≤ max k (max c (d - 1)) + 1 := by apply H <;> omega
--   induction e generalizing k with simp [abstract1, looseBVarRange', *] <;> try solve_by_elim
--   | bvar => split <;> omega
--   | fvar => split <;> simp [looseBVarRange']

theorem lowerLooseBVars_eq_instantiate (h : e.hasLooseBVar' k = false) :
    e.lowerLooseBVars' (k + 1) 1 = instantiate1' e v k := by
  induction e generalizing k with simp_all [hasLooseBVar', lowerLooseBVars', instantiate1']
  | bvar j => split <;> [rw [if_pos (by omega)]; rw [if_neg (by omega)]]

theorem hasLooseBVar_of_ge_looseBVarRange {e : Expr} (h : e.looseBVarRange' ≤ k) :
    e.hasLooseBVar' k = false := by
  induction e generalizing k with simp_all [hasLooseBVar', looseBVarRange', Nat.max_le]
  | bvar j => omega

theorem abstract1_lower {e : Expr} (h : e.hasLooseBVar' k₁ = false) (hk : k₁ ≤ k₂) :
    Expr.abstract1 a (e.lowerLooseBVars' (k₁ + 1) 1) k₂ =
    (Expr.abstract1 a e (k₂ + 1)).lowerLooseBVars' (k₁ + 1) 1 := by
  induction e generalizing k₁ k₂ with simp_all [abstract1, lowerLooseBVars', hasLooseBVar']
  | bvar i =>
    split <;> [skip; split]
    · rw [if_pos (c := i < k₂ + 1) (by omega), if_pos (by omega)]; simp [*]
    · rw [if_pos (c := i < _) (by omega)]; simp [*]
    · rw [if_neg (c := i < _) (by omega), if_neg (by omega)]; omega
  | fvar b =>
    split <;> simp [lowerLooseBVars', -right_eq_ite_iff]
    rw [if_neg (by omega)]

variable (red : Bool) (s : Name → Level) in
def instantiateLevelParamsCore' : Expr → Expr
  | .const c ls => .const c (ls.map (·.substParams' s red))
  | .sort u => .sort (u.substParams' s red)
  | .mdata m e => .mdata m (instantiateLevelParamsCore' e)
  | .proj n i e => .proj n i (instantiateLevelParamsCore' e)
  | .app f a => .app (instantiateLevelParamsCore' f) (instantiateLevelParamsCore' a)
  | .lam n t b bi => .lam n (instantiateLevelParamsCore' t) (instantiateLevelParamsCore' b) bi
  | .forallE n t b bi =>
    .forallE n (instantiateLevelParamsCore' t) (instantiateLevelParamsCore' b) bi
  | .letE n t v b bi => .letE n (instantiateLevelParamsCore' t)
      (instantiateLevelParamsCore' v) (instantiateLevelParamsCore' b) bi
  | e@(.bvar _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

theorem instantiateLevelParamsCore_eq_self (h : e.hasLevelParam' = false) :
    instantiateLevelParamsCore' red s e = e := by
  induction e <;> simp_all [instantiateLevelParamsCore', hasLevelParam', Level.substParams_eq_self]
  exact List.map_id''' _ fun _ h' => Level.substParams_eq_self (h _ h')

theorem instantiateLevelParamsCore_id {e : Expr} :
    instantiateLevelParamsCore' false .param e = e := by
  induction e <;> simp_all [instantiateLevelParamsCore', Level.substParams_id]

open private instantiateLevelParamsCore.replaceFn from Lean.Util.InstantiateLevelParams in
theorem instantiateLevelParamsCore_eq :
    instantiateLevelParamsCore s e =
    instantiateLevelParamsCore' true (fun x => (s x).getD (.param x)) e := by
  simp [instantiateLevelParamsCore]
  have (e) (H : e.hasLevelParam' = true →
        replaceNoCache (instantiateLevelParamsCore.replaceFn s) e =
        instantiateLevelParamsCore' true (fun x => (s x).getD (Level.param x)) e) :
      replaceNoCache (instantiateLevelParamsCore.replaceFn s) e =
      instantiateLevelParamsCore' true (fun x => (s x).getD (Level.param x)) e := by
    cases eq : e.hasLevelParam' <;> [skip; exact H eq]
    rw [instantiateLevelParamsCore_eq_self eq]
    suffices ∀ f, f e = some e → replaceNoCache f e = e by
      apply this; simp [instantiateLevelParamsCore.replaceFn, eq]
    intro f eq; cases e <;> simp only [replaceNoCache, eq]
  induction e <;> (
    refine this _ fun h => ?_
    simp only [replaceNoCache, instantiateLevelParamsCore.replaceFn]
    simp [h]; clear this h
    simp_all [instantiateLevelParamsCore'])

open private getParamSubst from Lean.Util.InstantiateLevelParams in
theorem instantiateLevelParams_eq {e ps ls} :
    instantiateLevelParams e ps ls =
    instantiateLevelParamsCore' (!ps.isEmpty && !ls.isEmpty)
      (fun x => ((ps.idxOf? x).bind (ls[·]?)).getD (.param x)) e := by
  simp only [instantiateLevelParams]; rw [← Bool.not_or];
  cases eq : ps.isEmpty || ls.isEmpty <;> simp
  · clear eq
    simp [instantiateLevelParamsCore_eq, List.idxOf?]; congr; ext n; congr
    induction ps generalizing ls <;> cases ls <;> simp [getParamSubst]
    split <;> simp [*, List.findIdx?_cons]; cases List.findIdx? .. <;> simp
  · refine instantiateLevelParamsCore_id.symm.trans ?_; congr; ext n
    cases ps <;> simp_all

theorem eqv_sort {e : Expr} : e == .sort u ↔ e = .sort u := by
  conv => lhs; simp [(· == ·)]
  cases e <;> simp [eqv']

theorem eqv_const {e : Expr} : e == .const c ls ↔ e = .const c ls := by
  conv => lhs; simp [(· == ·)]
  cases e <;> simp [eqv']

theorem eqv_refl (e : Expr) : e == e := by
  simp [(· == ·)]; induction e <;> simp [eqv', *]

theorem eqv_euc {e₁ e₂ e₃ : Expr} : e₁ == e₂ → e₁ == e₃ → e₂ == e₃ := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ e₃
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [eqv']; intros; subst_vars; try simp [*]
  all_goals
    revert ‹Expr.eqv' .. = _›
    cases e₃ <;> try change false = _ → _; rintro ⟨⟩
    simp +contextual [eqv', *]
  simp [BEq.congr_left ‹_›]

instance : EquivBEq Expr where
  symm h := eqv_euc h (eqv_refl _)
  trans h1 h2 := eqv_euc (eqv_euc h1 (eqv_refl _)) h2
  rfl := eqv_refl _

theorem data_eq {e₁ e₂ : Expr} : e₁ == e₂ → e₁.data = e₂.data := by
  simp [(· == ·)]; induction e₁ generalizing e₂
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [eqv']; intros; subst_vars; try simp [*]
  all_goals simp [Expr.data]; grind

instance : LawfulHashable Expr where
  hash_eq e₁ e₂ h := by simp [hash, Expr.hash, data_eq h]

theorem instantiate1_eqv {e₁ e₂ : Expr} :
    e₁ == e₂ → e₁.instantiate1' a k == e₂.instantiate1' a k := by
  simp [(· == ·)]; induction e₁ generalizing e₂ k
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [instantiate1', eqv']
  all_goals intros; subst_vars; try simp [*]
  split <;> [skip; split] <;> simpa [(· == ·)] using eqv_refl _

theorem instantiateList_eqv {e₁ e₂ : Expr} (h : e₁ == e₂) :
    e₁.instantiateList as k == e₂.instantiateList as k := by
  induction as generalizing e₁ e₂ <;> simp [instantiate1_eqv, *]
