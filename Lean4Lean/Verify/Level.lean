module

public import Lean4Lean.Theory.VLevel
public import Lean4Lean.Level
public import Lean4Lean.Verify.Axioms
public import Std.Tactic.BVDecide
public import Std.Data.TreeMap.Lemmas

@[expose] public section

namespace Lean

namespace Name
open Std

instance : TransCmp cmp := by
  have eq_swap {a b : Name} : a.cmp b = (b.cmp a).swap := by
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      rw [ih]; cases b₁.cmp a₁ <;> simp [← OrientedOrd.eq_swap]
  refine { eq_swap, isLE_trans {a b c} := ?_ }
  have {α} [Ord α] [TransOrd α] {a₁ b₁ c₁} {a₂ b₂ c₂ : α}
      (H1 : (cmp a₁ b₁).isLE → (cmp b₁ c₁).isLE → (cmp a₁ c₁).isLE)
      (H2 : (cmp c₁ a₁).isLE → (cmp a₁ b₁).isLE → (cmp c₁ b₁).isLE)
      (H3 : (cmp b₁ c₁).isLE → (cmp c₁ a₁).isLE → (cmp b₁ a₁).isLE) :
      ((cmp a₁ b₁).then (compare a₂ b₂)).isLE →
      ((cmp b₁ c₁).then (compare b₂ c₂)).isLE →
      ((cmp a₁ c₁).then (compare a₂ c₂)).isLE := by
    simp [Ordering.isLE_then_iff_and]
    intro h1 h2 h3 h4
    refine have := H1 h1 h3; ⟨this, ?_⟩
    obtain eq | eq := Ordering.isLE_iff_eq_lt_or_eq_eq.1 this; · exact .inl eq
    obtain h2 | h2 := h2
    · rw [@eq_swap c₁, eq, @eq_swap _ a₁, h2] at H3; simp [h3] at H3
    obtain h4 | h4 := h4
    · rw [eq_swap, eq, @eq_swap c₁, h4] at H2; simp [h1] at H2
    exact .inr (TransCmp.isLE_trans h2 h4)
  refine (?_ : _ ∧ ((cmp c a).isLE → (cmp a b).isLE → (cmp c b).isLE) ∧
    ((cmp b c).isLE → (cmp c a).isLE → (cmp b a).isLE)).1
  induction a generalizing b c with
    obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp] at * <;>
    obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;> simp [cmp] at *
  | str a₁ a₂ ih | num a₁ a₂ ih =>
    let ⟨h1, h2, h3⟩ := @ih b₁ c₁
    exact ⟨this h1 h2 h3, this h2 h3 h1, this h3 h1 h2⟩

instance : LawfulBEqCmp cmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨?_, fun h => h ▸ ReflCmp.compare_self⟩
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun h _ => ih h

instance : TransCmp quickCmp where
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

instance : LawfulBEqCmp quickCmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨fun h => ?_, fun h => h ▸ ReflCmp.compare_self⟩
    replace h := (Ordering.then_eq_eq.1 h).2; revert h
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun _ => ih

end Name

namespace Level
open Lean4Lean

attribute [simp] mkLevelSucc mkLevelMax mkLevelIMax updateSucc! updateMax! updateIMax!

-- variable (ls : List Name) in
-- def _root_.Lean4Lean.VLevel.toLevel : VLevel → Level
--   | .zero => .zero
--   | .succ l => .succ l.toLevel
--   | .max l₁ l₂ => .max l₁.toLevel l₂.toLevel
--   | .imax l₁ l₂ => .imax l₁.toLevel l₂.toLevel
--   | .param n => match ls.get? n with
--     | some l => .param l
--     | none => .zero

-- theorem toLevel_inj {ls : List Name} (d : ls.Nodup)
--     {l₁ l₂ : VLevel} (eq : l₁.toLevel ls = l₂.toLevel ls) : l₁ = l₂ := sorry

@[simp] def getOffset' : Level → Nat
  | succ u => getOffset' u + 1
  | _      => 0

@[simp] theorem getOffset_eq (u : Level) : u.getOffset = u.getOffset' := go _ 0 where
  go (u : Level) (i) : u.getOffsetAux i = u.getOffset' + i := by
    unfold getOffsetAux getOffset'; split <;> simp
    rw [go]; simp [Nat.add_right_comm, Nat.add_assoc]

theorem mkData_depth (H : d < 2 ^ 24) : (mkData h d hmv hp).depth.toNat = d := by
  rw [mkData_eq, mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H)), Data.depth]
  have : d.toUInt64.toUInt32.toNat = d := by simp; omega
  refine .trans ?_ this; congr 2
  rw [← UInt64.toBitVec_inj]
  have : d.toUInt64.toNat = d := by simp; omega
  have : d.toUInt64.toBitVec ≤ 0xffffff#64 := (this ▸ Nat.le_sub_one_of_lt H :)
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  change (
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 40#64 = d.toUInt64.toBitVec
  bv_decide

theorem mkData_hasParam (H : d < 2 ^ 24) : (mkData h d hmv hp).hasParam = hp := by
  rw [mkData_eq, mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasParam, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 33#64) &&& 1#64
  change decide (L = 1#64) = hp
  rw [show L = hp.toUInt64.toBitVec by bv_decide]
  cases hp <;> decide

theorem mkData_hasMVar (H : d < 2 ^ 24) : (mkData h d hmv hp).hasMVar = hmv := by
  rw [mkData_eq, mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasMVar, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 32#64) &&& 1#64
  change decide (L = 1#64) = hmv
  rw [show L = hmv.toUInt64.toBitVec by bv_decide]
  cases hmv <;> decide

theorem ofLevel_of_not_hasParam (Us) {l : Level}
    (hl : l.hasParam' = false) (hmv : l.hasMVar' = false) :
    ∃ u', VLevel.ofLevel Us l = some u' := by
  induction l <;> simp_all [hasParam', hasMVar', VLevel.ofLevel, exists_comm]

def getUndefParam.F (ps : List Name) (l : Level) : StateT (Option Name) Id Bool := do
  if !l.hasParam || (← get).isSome then
    return false
  if let .param n := l then
    if n ∉ ps then
      set (some n)
  return true

theorem getUndefParam_none {l : Level} (hmv : l.hasMVar' = false) :
    l.getUndefParam Us = none → ∃ u', VLevel.ofLevel Us l = some u' := by
  suffices ∀ s, ((l.forEach (getUndefParam.F Us)).run s).run.snd = none → s = none ∧ _ from
    (this _ · |>.2)
  have {l} (hmv : l.hasMVar' = false)
      {g} (H : ∀ {s'}, (g.run s').run.snd = none → s' = none ∧
        (((getUndefParam.F Us l).run none).run = (true, none) →
          ∃ u', VLevel.ofLevel Us l = some u')) (s) :
      ((do if (!(← getUndefParam.F Us l)) = true then pure PUnit.unit else g)
        |>.run s).run.snd = none →
      s = none ∧ ∃ u', VLevel.ofLevel Us l = some u' := by
    simp; split <;> rename_i h
    · simp; revert h
      simp [getUndefParam.F]; split <;> [simp; split <;> [split <;> simp; simp]]
      rintro rfl; simp at *
      exact ofLevel_of_not_hasParam Us ‹_› hmv
    · refine fun h' => let ⟨h1, h2⟩ := H h'; have := ?_; ⟨this, h2 ?_⟩
      · revert h h1
        simp [getUndefParam.F]; split <;> [simp; split <;> [split <;> simp; simp]]
      · revert h h1; subst s
        cases (getUndefParam.F Us l).run none; simp; rintro rfl rfl; rfl
  have lt {n a} : n + 1 < a → n < a := by omega
  induction l with (
    refine this hmv fun h => ?_; clear this
    simp [hasMVar', VLevel.ofLevel, *] at *)
  | succ _ ih =>
    have ⟨h, _, h1⟩ := ih hmv _ h
    exact ⟨h, fun _ => ⟨_, _, h1, rfl⟩⟩
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 =>
    have ⟨h, _, h2⟩ := ih2 hmv.2 _ h
    have ⟨h, _, h1⟩ := ih1 hmv.1 _ h
    exact ⟨h, fun _ => ⟨_, _, h1, _, h2, rfl⟩⟩
  | param =>
    simp [getUndefParam.F, hasParam', List.idxOf_lt_length_iff, *]
    split <;> simp [*]
  | _ => simp [*]

variable (s : Name → Level) in
def substParams' (red : Bool) : Level → Level
  | .zero       => .zero
  | .succ v     => .succ (substParams' (v.hasParam ∧ red) v)
  | .max v₁ v₂  =>
    let red := (v₁.hasParam ∨ v₂.hasParam) ∧ red
    (if red then mkLevelMax' else .max) (substParams' red v₁) (substParams' red v₂)
  | .imax v₁ v₂ =>
    let red := (v₁.hasParam ∨ v₂.hasParam) ∧ red
    (if red then mkLevelIMax' else .imax) (substParams' red v₁) (substParams' red v₂)
  | .param n => s n
  | u => u

theorem substParams_eq_self {u : Level} (h : u.hasParam' = false) :
    substParams' s red u = u := by
  induction u generalizing red <;> simp_all [substParams', hasParam']

open private substParams.go from Lean.Level in
@[simp] theorem substParams_eq (u : Level) (s : Name → Option Level) :
    substParams u s = substParams' (fun x => (s x).getD (.param x)) true u := by
  unfold substParams
  induction u <;> simp [substParams.go, substParams', hasParam', ← Bool.or_eq_true] <;>
    split <;> simp [*, substParams_eq_self] <;> simp_all [substParams_eq_self]

theorem substParams_id {u : Level} :
    substParams' .param false u = u := by induction u <;> simp_all [substParams']

local notation "max'" => Max.max

namespace Normalize

attribute [local instance] Lean.Level.Normalize.instOrdName_lean4Lean

local instance : Std.TransCmp (α := Name) compare := inferInstanceAs (Std.TransCmp Name.cmp)
local instance : Std.LawfulBEqCmp (α := List Name) compare :=
  inferInstanceAs (Std.LawfulBEqCmp (List.compareLex Name.cmp))

instance : LawfulBEq VarNode where
  rfl {a} := by cases a <;> simp! +instances [instBEqVarNode]
  eq_of_beq {a b} := by cases a <;> cases b <;> simp! +instances [instBEqVarNode]

@[reducible] local instance : Membership (List Name) NormLevel :=
  inferInstanceAs (Membership _ (Std.TreeMap _ _ compare))

@[reducible] local instance : GetElem? NormLevel (List Name) Node (fun m a => a ∈ m) :=
  inferInstanceAs (GetElem? (Std.TreeMap _ _ compare) ..)

section
variable (ls : List Name) (ρ : List Nat) in
def evalParam (x : Name) : Nat :=
let i := ls.idxOf x; if i < ls.length then ρ[i]?.getD 0 else 0

theorem evalParam_eq (hv : ls.idxOf x < ls.length) :
    evalParam ls ρ x = ρ[List.idxOf x ls]?.getD 0 := if_pos hv

variable (ls : List Name) (ρ : List Nat) in
def VarNode.eval (l : VarNode) : Nat := evalParam ls ρ l.var + l.offset

variable (ls : List Name) (ρ : List Nat) in
def Node.eval (l : Node) : Nat :=
  l.var.foldl (init := l.const) fun n v => max' n (v.eval ls ρ)

theorem Node.eval_le : eval ls ρ l ≤ n ↔
    l.const ≤ n ∧ ∀ v ∈ l.var, v.eval ls ρ ≤ n := by
  simp [eval, ← List.foldr_reverse]; simp only [← l.var.mem_reverse]
  induction l.var.reverse with simp | cons a l
  simp [Nat.max_le, and_comm, and_left_comm, *]

variable (ls : List Name) (ρ : List Nat) in
def allNZ (path : List Name) : Bool := path.all (0 < evalParam ls ρ ·)

theorem allNZ_cons : allNZ ls ρ (a :: path) ↔
    0 < evalParam ls ρ a ∧ allNZ ls ρ path := by simp [allNZ]

theorem allNZ_mono (H : ∀ x ∈ path, x ∈ path') : allNZ ls ρ path' → allNZ ls ρ path := by
  simp [allNZ]; grind

variable (ls : List Name) (ρ : List Nat) in
def evalPath (path : List Name) (n : Nat) : Nat :=
  if allNZ ls ρ path then n else 0

theorem evalPath_cons : evalPath ls ρ (a :: path) n =
    evalPath ls ρ path (if 0 < evalParam ls ρ a then n else 0) := by
  by_cases h : 0 < evalParam ls ρ a <;> simp [evalPath, allNZ_cons, h]

theorem evalPath_max :
    evalPath ls ρ path (max' m n) = max' (evalPath ls ρ path m) (evalPath ls ρ path n) := by
  simp [evalPath]; split <;> simp

theorem evalPath_mono (h : n ≤ m) :
    evalPath ls ρ path n ≤ evalPath ls ρ path m := by
  simp [evalPath]; split <;> simp [*]

theorem evalPath_le : evalPath ls ρ path n ≤ m ↔ (allNZ ls ρ path → n ≤ m) := by
  simp [evalPath]; split <;> simp [*]

variable (ls : List Name) (ρ : List Nat) in
inductive EvalPaths : List Name → Nat → Prop
  | nil : EvalPaths [] n
  | insert : orderedInsert Name.cmp a path = some path' →
    evalPath ls ρ path (evalParam ls ρ a) ≤ n → EvalPaths path n → EvalPaths path' n

theorem EvalPaths.mono (h : n ≤ n') : EvalPaths ls ρ path n → EvalPaths ls ρ path n'
  | .nil => .nil
  | .insert h1 h2 h3 => .insert h1 (Nat.le_trans h2 h) (h3.mono h)

theorem EvalPaths.max : EvalPaths ls ρ path n → EvalPaths ls ρ path (max' n m) :=
  .mono (Nat.le_max_left ..)

variable (ls : List Name) (ρ : List Nat) in
def NormLevel.eval (l : NormLevel) : Nat :=
  l.foldl (init := 0) fun n a b => max' n (evalPath ls ρ a (b.eval ls ρ))

theorem NormLevel.eval_le : eval ls ρ l ≤ n ↔
    ∀ a b, l.get? a = some b → evalPath ls ρ a (b.eval ls ρ) ≤ n := by
  simp [eval, Std.TreeMap.foldl_eq_foldl_toList, ← List.foldr_reverse]
  simp only [← Std.TreeMap.mem_toList_iff_getElem?_eq_some, ← l.toList.mem_reverse]
  induction l.toList.reverse with simp | cons a l; let (a, b) := a
  simp [or_imp, forall_and, Nat.max_le, and_comm, *]

end

theorem NormLevel.addVar_contains (H : acc.contains x) : (addVar v k path acc).contains x := by
  simp_all [addVar, Std.TreeMap.mem_modify]

theorem NormLevel.addNode_contains (H : acc.contains x) : (addNode v k path acc).contains x := by
  simp [addNode, Std.TreeMap.mem_alter] at *; split <;> simp [*]

theorem NormLevel.addNode_contains_self : (addNode v k path acc).contains path := by
  simp [addNode]; split <;> simp

theorem NormLevel.addConst_contains (H : acc.contains x) : (addConst k path acc).contains x := by
  simp [addConst] at *; split <;> simp [H, Std.TreeMap.mem_modify]

theorem normalizeAux_contains (H : acc.contains x) : (normalizeAux u path k acc).contains x := by
  unfold normalizeAux; split
  · exact NormLevel.addConst_contains H
  · exact NormLevel.addConst_contains H
  · exact normalizeAux_contains H
  · exact normalizeAux_contains (normalizeAux_contains H)
  · exact normalizeAux_contains (normalizeAux_contains H)
  · exact normalizeAux_contains (normalizeAux_contains H)
  · exact normalizeAux_contains (normalizeAux_contains H)
  · split <;> [skip; (dsimp; split)]
    · exact normalizeAux_contains (NormLevel.addNode_contains (NormLevel.addConst_contains H))
    · exact normalizeAux_contains H
    · exact normalizeAux_contains (NormLevel.addVar_contains H)
  · exact H
  · exact H
  · split <;> [skip; split]
    · exact NormLevel.addNode_contains (NormLevel.addConst_contains H)
    · exact H
    · exact NormLevel.addVar_contains H

theorem imax_max : Nat.imax a (max' b c) = max' (Nat.imax a b) (Nat.imax a c) := by
  simp [Nat.imax]; symm; split <;> simp [*]; split <;> simp [*, Nat.max_eq_max]
  rw [Nat.max_left_comm b, ← Nat.max_assoc, Nat.max_self]

theorem imax_imax : Nat.imax a (Nat.imax b c) = max' (Nat.imax a c) (Nat.imax b c) := by
  simp [Nat.imax]; by_cases h : c = 0 <;> simp [*, Nat.max_eq_max]
  rw [Nat.max_left_comm c, Nat.max_self]

theorem mem_orderedInsert [BEq α] [LawfulBEq α] [Std.LawfulBEqCmp (α := α) cmp] :
    b ∈ (orderedInsert cmp a ls).getD ls ↔ b = a ∨ b ∈ ls := by
  induction ls <;> simp [orderedInsert]; split <;> simp_all [or_left_comm]

theorem allNZ_orderedInsert :
    allNZ ls ρ ((orderedInsert Name.cmp a path).getD path) = allNZ ls ρ (a :: path) := by
  rw [Bool.eq_iff_iff]; simp [allNZ, mem_orderedInsert]

theorem evalPath_orderedInsert :
    evalPath ls ρ ((orderedInsert Name.cmp a path).getD path) = evalPath ls ρ (a :: path) := by
  ext n; simp [evalPath, allNZ_orderedInsert]

theorem EvalPaths.of_mem (hm : v ∈ path) (H : EvalPaths ls ρ path n) :
    ∃ path₁ path₂, (∀ x ∈ path₁, x ∈ path) ∧
      orderedInsert Name.cmp v path₁ = some path₂ ∧
      evalPath ls ρ path₁ (evalParam ls ρ v) ≤ n ∧
      EvalPaths ls ρ path₁ n := by
  induction H with | nil => cases hm | insert h1 h2 h3 ih
  obtain rfl | hm := (h1 ▸ mem_orderedInsert).1 hm
  · exact ⟨_, _, fun _ h => (h1 ▸ mem_orderedInsert).2 (.inr h), h1, h2, h3⟩
  · let ⟨_, _, a1, a2, a3, a4⟩ := ih hm
    exact ⟨_, _, fun _ h => (h1 ▸ mem_orderedInsert).2 (.inr (a1 _ h)), a2, a3, a4⟩

theorem ext_le {n m : Nat} (H : ∀ x, n ≤ x ↔ m ≤ x) : n = m :=
  Nat.le_antisymm ((H _).2 (Nat.le_refl _)) ((H _).1 (Nat.le_refl _))

theorem le_ext_le {n m : Nat} (H : ∀ x, n ≤ x → m ≤ x) : m ≤ n := H _ (Nat.le_refl _)

theorem NormLevel.addConst_eval
    (H : acc.contains path) (le : EvalPaths ls ρ path (acc.eval ls ρ)) :
    (addConst k path acc).eval ls ρ = max' (acc.eval ls ρ) (evalPath ls ρ path k) := by
  simp [addConst]; split <;> rename_i h
  · obtain rfl | ⟨rfl, _⟩ := h
    · simp [evalPath]
    · let a::path := path; let .insert h1 le h3 := le
      have := h1 ▸ evalPath_orderedInsert (ls := ls) (ρ := ρ); simp at this
      rw [this, Nat.max_eq_left]; simp [evalPath]; split <;> [rename_i h; simp]
      let ⟨h1, h2⟩ := allNZ_cons.1 h; exact Nat.le_trans h1 (evalPath_le.1 le h2)
  · refine ext_le fun x => ?_
    rw [← Std.TreeMap.isSome_getElem?_eq_contains, Option.isSome_iff_exists] at H; let ⟨v, H⟩ := H
    simp [eval_le, Nat.max_le, Std.TreeMap.getElem?_modify, evalPath_le, Node.eval_le, H]
    refine ⟨fun h1 => ?_, fun ⟨h1, h2⟩ a b => ?_⟩
    · have := h1 path; simp [Nat.max_le] at this
      refine ⟨fun a b h3 h4 => ?_, fun h => (this h).1.1⟩
      specialize h1 a; split at h1
      · subst a; cases H.symm.trans h3; exact ⟨(this h4).1.2, (this h4).2⟩
      · exact h1 _ h3 h4
    · split
      · subst a; rintro ⟨⟩ nz; simp [Nat.max_le, nz, h2]; exact h1 _ _ H nz
      · exact h1 _ _

theorem VarNode.addVar_le : (∀ vn ∈ VarNode.addVar v k l, vn.eval ls ρ ≤ x) ↔
    evalParam ls ρ v + k ≤ x ∧ (∀ vn ∈ l, vn.eval ls ρ ≤ x) := by
  simp [eval]; induction l with simp [VarNode.addVar] | cons vn l ih; split <;> simp [*]
  · simp at *; subst v
    rw [← and_assoc, ← Nat.max_le, Nat.add_max_add_left, Nat.max_comm, Nat.max_eq_max]
  · rw [and_left_comm]

theorem NormLevel.addNode_eval : (addNode v k path acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (evalParam ls ρ v + k)) := by
  refine ext_le fun x => ?_
  simp [addNode, eval_le, Std.TreeMap.getElem?_alter, evalPath_le, Node.eval_le, Nat.max_le]
  refine ⟨fun H => ⟨fun a b h nz => ?_, fun nz => ?_⟩, fun ⟨H1, H2⟩ a b h nz => ?_⟩
  · have := H a; split at this
    · subst a; simp_all [VarNode.addVar_le]
    · exact this _ h nz
  · have := H path; simp at this; split at this <;> specialize this _ rfl nz
    · simp_all [VarNode.eval]
    · simp_all [VarNode.addVar_le]
  · split at h
    · subst a; split at h <;> cases h
      · simp_all [VarNode.eval]
      · simp_all [VarNode.addVar_le]; grind
    · grind

theorem NormLevel.addVar_eval (H : acc.contains path) : (addVar v k path acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (evalParam ls ρ v + k)) := by
  refine ext_le fun x => ?_
  rw [← Std.TreeMap.isSome_getElem?_eq_contains, Option.isSome_iff_exists] at H; let ⟨v, H⟩ := H
  simp [addVar, eval_le, Nat.max_le, Std.TreeMap.getElem?_modify, evalPath_le, Node.eval_le, H]
  refine ⟨fun H => ⟨fun a b h nz => ?_, fun nz => ?_⟩, fun ⟨H1, H2⟩ a b h nz => ?_⟩
  · have := H a; split at this
    · subst a; simp_all [VarNode.addVar_le]
    · exact this _ h nz
  · have := H path; simp at this; specialize this nz; simp_all [VarNode.addVar_le]
  · split at h
    · subst a; cases h; simp_all [VarNode.addVar_le]; grind
    · grind

theorem normalizeAux_eval (hu : VLevel.ofLevel ls u = some u')
    (H : acc.contains path) (le : EvalPaths ls ρ path (acc.eval ls ρ)) :
    (normalizeAux u path k acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (u'.eval ρ + k)) := by
  unfold normalizeAux; split
  · cases hu; simp [NormLevel.addConst_eval H le, VLevel.eval]
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    simp [VLevel.eval, Nat.imax, NormLevel.addConst_eval H le]
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    rw [normalizeAux_eval hu H le, Nat.add_succ, ← Nat.succ_add]; rfl
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, hv, rfl⟩ := hu
    rw [normalizeAux_eval hv (normalizeAux_contains H)] <;> rw [normalizeAux_eval hu H le]
    · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; rfl
    · exact le.max
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval hv (normalizeAux_contains H)] <;> rw [normalizeAux_eval hu H le]
    · rw [Nat.max_assoc, Nat.add_succ, ← Nat.succ_add, ← evalPath_max, Nat.add_max_add_right]; rfl
    · exact le.max
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval
        (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) (normalizeAux_contains H)] <;>
      rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hv, rfl⟩) H le]
    · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; simp [VLevel.eval, imax_max]
    · exact le.max
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hv, _, hw, rfl⟩)
        (normalizeAux_contains H)] <;>
      rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) H le]
    · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; simp [VLevel.eval, imax_imax]
    · exact le.max
  · rename_i u v
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨hv, rfl⟩, rfl⟩ := hu
    have := @evalPath_orderedInsert ls ρ v path
    split <;> rename_i h <;> simp [h] at this
    · rw [normalizeAux_eval hu NormLevel.addNode_contains_self] <;>
        rw [NormLevel.addNode_eval, NormLevel.addConst_eval H le, Nat.max_assoc]
      · rw [Nat.max_assoc, ← evalPath_max, this, evalPath_cons, ← evalPath_max,
          Nat.add_max_add_right]; congr 2
        simp [VLevel.eval, ← evalParam_eq hv, Nat.imax]
        cases evalParam .. <;> simp [Nat.max_eq_max, Nat.max_comm]
      · refine .insert h (Nat.le_trans ?_ (Nat.le_max_right ..)) le.max
        rw [this, evalPath_cons, ← evalPath_max]; apply evalPath_mono; grind
    · dsimp; split
      · rw [normalizeAux_eval hu H le]
        simp [evalPath]; split <;> [rename_i nz; simp]
        have hm := (h ▸ mem_orderedInsert).2 (.inl rfl)
        have ⟨p1, p2, a1, a2, a3, a4⟩ := le.of_mem hm
        have := evalPath_le.1 a3 (allNZ_mono a1 nz)
        simp [allNZ] at nz; specialize nz _ hm
        simp [VLevel.eval, Nat.imax]; simp [← evalParam_eq hv]
        revert this nz; cases evalParam .. <;> simp
        rw [Nat.max_eq_max, Nat.max_comm (a := VLevel.eval ..), ← Nat.add_max_add_right, ← Nat.max_assoc]
        intro h; rw [Nat.max_eq_left (b := _+1+k)]; omega
      · rw [normalizeAux_eval hu (NormLevel.addVar_contains H)] <;> rw [NormLevel.addVar_eval H]
        · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right, this,
            evalPath_cons, evalPath_cons]; congr 2; split <;> simp [VLevel.eval, Nat.imax]
          rename_i h; revert h; simp [← evalParam_eq hv]
          cases evalParam .. <;> simp [Nat.max_eq_max, Nat.max_comm]
        · exact le.max
  · cases hu
  · simp [VLevel.ofLevel] at hu
  · rename_i v; simp [VLevel.ofLevel] at hu; obtain ⟨hv, rfl⟩ := hu
    have := @evalPath_orderedInsert ls ρ v path
    split <;> rename_i h <;> simp [h] at this
    · rw [NormLevel.addNode_eval, NormLevel.addConst_eval H le, Nat.max_assoc,
        this, evalPath_cons, ← evalPath_max]
      simp [VLevel.eval, ← evalParam_eq hv]; congr 2; split <;> simp; omega
    · split
      · simp [evalPath]; split <;> [rename_i nz; simp]
        have hm := (h ▸ mem_orderedInsert).2 (.inl rfl)
        have ⟨p1, p2, a1, a2, a3, a4⟩ := le.of_mem hm
        have := evalPath_le.1 a3 (allNZ_mono a1 nz)
        simp [allNZ] at nz; specialize nz _ hm
        simp [VLevel.eval, ← evalParam_eq hv]
        revert this nz; cases evalParam .. <;> simp; omega
      · rw [NormLevel.addVar_eval H, this, evalPath_cons, evalPath_cons]
        congr 2; split <;> simp [VLevel.eval, ← evalParam_eq hv]

theorem NormLevel.subsumption_eval {s : NormLevel} :
    s.subsumption.eval ls ρ = s.eval ls ρ := by
  sorry

theorem normalize_eval (hu : VLevel.ofLevel ls u = some u') :
    (normalize u).eval ls ρ = u'.eval ρ := by
  simp [normalize, NormLevel.subsumption_eval]
  exact normalizeAux_eval hu (by simp) .nil

theorem Node.eval_congr {a b : Node} (H : a == b) : a.eval ls ρ = b.eval ls ρ := by
  simp +instances [instBEqNode] at H; simp [H, eval]

theorem NormLevel.eval_congr {a b : NormLevel} (H : a == b) : a.eval ls ρ = b.eval ls ρ := by
  simp +instances only [instBEqNormLevel, Std.TreeMap.all_eq_all_toList,
    Bool.and_eq_true, List.all_eq_true] at H
  suffices ∀ {a b : NormLevel}, (∀ x ∈ a.toList, b.get? x.1 == some x.2) →
      a.eval ls ρ ≤ b.eval ls ρ from Nat.le_antisymm (this H.1) (this H.2)
  clear a b H; intro a b H
  simp only [eval, Std.TreeMap.foldl_eq_foldl_toList]
  rw [← a.toList.reverse_reverse] at H ⊢; generalize a.toList.reverse = a at H ⊢
  simp only [List.mem_reverse, Std.TreeMap.get?_eq_getElem?, List.foldl_reverse] at H ⊢
  induction a with | nil => exact Nat.zero_le _ | cons p l ih; let (x, y) := p
  simp only [List.mem_cons, or_imp, forall_and, forall_eq, List.foldr_cons] at H ⊢
  refine Nat.max_le.2 ⟨ih H.2, ?_⟩
  let ⟨y', h1, h2⟩ := Option.beq_some_iff.1 H.1
  have H := Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 h1
  rw [← b.toList.reverse_reverse] at H ⊢; generalize b.toList.reverse = b at H ⊢
  simp only [List.mem_reverse, List.foldl_reverse] at H ⊢
  induction b with | nil => cases H | cons p l ih; let (x, y) := p
  simp; obtain ⟨⟩ | ⟨_, (H : _ ∈ l)⟩ := H
  · exact Node.eval_congr h2 ▸ Nat.le_max_right ..
  · exact Nat.le_trans (ih H) (Nat.le_max_left ..)

end Normalize

theorem isEquiv'_wf (h : isEquiv' u v)
    (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v') : u' ≈ v' := by
  simp [isEquiv'] at h; obtain rfl | h := h
  · cases hu.symm.trans hv; rfl
  refine VLevel.equiv_def.2 fun ls' => ?_
  rw [← Normalize.normalize_eval hu, ← Normalize.normalize_eval hv]
  exact Normalize.NormLevel.eval_congr h

theorem isEquivList_wf (H : Level.isEquivList us vs) :
    List.mapM (VLevel.ofLevel Us) us = some us' →
    List.mapM (VLevel.ofLevel Us) vs = some vs' → us'.Forall₂ (· ≈ ·) vs' := by
  simp [Level.isEquivList] at H; revert us' vs'
  induction us generalizing vs with cases vs <;> simp [List.all2] at H <;> simp | cons u us ih
  rename_i v vs; rintro _ _ u' hu us' hus rfl v' hv vs' hvs rfl
  exact .cons (isEquiv'_wf H.1 hu hv) (ih H.2 hus hvs)
