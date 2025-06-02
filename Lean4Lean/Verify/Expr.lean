import Lean4Lean.Std.Basic
import Lean4Lean.Verify.Axioms
import Lean4Lean.Verify.Level
import Lean4Lean.Expr
import Lean4Lean.Instantiate
import Batteries.Data.String.Lemmas
import Std.Tactic.BVDecide

namespace Lean

open Expr in
theorem Literal.toConstructor_hasLevelParam :
    (Literal.toConstructor l).hasLevelParam' = false := by
  cases l with simp [Literal.toConstructor]
  | natVal n => cases n <;> simp [natLitToConstructor, hasLevelParam', natZero, natSucc]
  | strVal s =>
    let ⟨l⟩ := s
    simp [strLitToConstructor, hasLevelParam', String.foldr_eq]
    induction l <;> simp_all [hasLevelParam', Level.hasParam']

namespace Expr

attribute [simp] mkConst mkBVar mkSort mkFVar mkMVar mkMData mkProj mkApp mkLambda mkForall mkLet
  updateApp! updateFVar! updateConst! updateSort! updateMData! updateProj!
  updateForall! updateForallE! updateLambda! updateLambdaE! updateLet!

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
    · simp [Array.getElem!_eq_getD, ← Array.getElem?_toList, h1]
      obtain _ | ⟨a, l₂⟩ := l₂; · simp_all
      rw [List.getElem?_append_right (by simp [h2])]
      simp [h2]
      rw [loop (l₁ := l₁ ++ [a]) (l₂ := l₂)] <;> simp [h1, h2, h3, mkApp]
    · simp at h3
      have : l₂.length = 0 := by omega
      simp at this; simp [this]

theorem liftLooseBVars_eq_self : e.looseBVarRange' ≤ s → liftLooseBVars' e s d = e := by
  induction e generalizing s <;>
    simp +contextual [*, looseBVarRange', liftLooseBVars', Nat.max_le, Nat.le_add_of_sub_le]
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

theorem instantiate1'_eq_self : e.looseBVarRange' ≤ k → instantiate1' e a k = e := by
  induction e generalizing k <;>
    simp +contextual [*, looseBVarRange', instantiate1', Nat.max_le, Nat.le_add_of_sub_le]
  omega

theorem instantiate1_eq_self (H : e.looseBVarRange' = 0) : instantiate1' e a = e := by
  simpa using instantiate1'_eq_self (e := e) (Nat.le_zero.2 H)

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
  induction e1 generalizing j with simp [liftLooseBVars', instantiate1', *]
  | bvar i => ?_
  | _ => rename_i IH; exact IH (j+1)
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
    simp [instantiate1', hk]
    -- have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [instantiate1']
    rw [if_neg (Nat.lt_asymm hk), if_neg (Nat.ne_of_gt hk)]

theorem instantiateList_append :
    instantiateList e (es₁ ++ es₂) k = instantiateList (instantiateList e es₁ k) es₂ k := by
  induction es₁ generalizing e <;> simp [*]

theorem instantiateList_lam : instantiateList (.lam n ty body bi) as =
    .lam n (instantiateList ty as) (instantiateList body as 1) bi := by
  induction as generalizing ty body <;> simp [instantiate1', *]

theorem instantiateList_forallE : instantiateList (.forallE n ty body bi) as =
    .forallE n (instantiateList ty as) (instantiateList body as 1) bi := by
  induction as generalizing ty body <;> simp [instantiate1', *]

theorem instantiateList_instantiate1_comm (h : a.looseBVarRange' = 0) :
    (instantiateList e as 1).instantiate1' a =
    instantiateList (e.instantiate1' a) as := by
  induction as generalizing e <;> simp [instantiate1', *]
  congr 1; refine (instantiate1'_instantiate1' (j := 0) ..).trans ?_
  rw [liftLooseBVars_eq_self (by simp [h])]

theorem instantiateRev_push {e : Expr} {subst a} :
    instantiateRev e (subst.push a) = instantiateRev (e.instantiate1' a) subst := by
  let ⟨subst⟩ := subst; simp [instantiateList, instantiate1']

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
  induction as generalizing e <;> simp_all [abstract1, abstract1_comm]

theorem abstract1_abstractList' {e : Expr} {as : List FVarId} {k} (H : (a :: as).Nodup) :
    abstract1 a (abstractList e as k) (k + as.length) =
    abstractList (abstract1 a e k) as k := by
  induction as generalizing e a with
  | nil => simp
  | cons b as ih =>
    simp [abstract1] at *; simp [H] at ih
    rw [← ih H.2.1, ← Nat.add_assoc, ← abstract1_comm (.symm H.1.1), ih H.1.2, ih H.2.1]

theorem abstract1_hasLooseBVar (a e k i) :
    (abstract1 a e k).hasLooseBVar' (if i < k then i else i+1) =
    e.hasLooseBVar' i := by
  have (i k) : (if i < k then i else i + 1) + 1 = if i + 1 < k + 1 then i + 1 else i + 1 + 1 := by
    simp; split <;> rfl
  induction e generalizing i k with simp only [hasLooseBVar', abstract1, *]
  | bvar j =>
    by_cases h : j = i <;> simp [h]
    split <;> split <;> omega
  | fvar b =>
    split <;> simp [hasLooseBVar']
    split <;> omega

theorem lowerLooseBVars_eq_instantiate (h : e.hasLooseBVar' k = false) :
    e.lowerLooseBVars' (k + 1) 1 = instantiate1' e v k := by
  induction e generalizing k with simp_all [hasLooseBVar', lowerLooseBVars', instantiate1']
  | bvar j => split <;> [rw [if_pos (by omega)]; rw [if_neg (by omega)]]

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
    split <;> simp [lowerLooseBVars']
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
    simp only [replaceNoCache]
    rw [instantiateLevelParamsCore.replaceFn.eq_def]
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
    split <;> simp [*]; cases List.findIdx? .. <;> simp
  · refine instantiateLevelParamsCore_id.symm.trans ?_; congr; ext n
    cases ps <;> simp_all
