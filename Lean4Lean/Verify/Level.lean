import Lean4Lean.Theory.VLevel
import Lean4Lean.Level
import Lean4Lean.Verify.Name
import Lean4Lean.Verify.LevelStd
import Lean4Lean.Verify.Axioms
import Std.Tactic.BVDecide
import Std.Data.TreeMap.Lemmas

namespace Lean

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

set_option allowUnsafeReducibility true
attribute [local reducible] Data

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
  have {l} (hmv : l.hasMVar' = false) {g}
      (H : ∀ {s'}, (g.run s').run.snd = none → s' = none ∧
        (((getUndefParam.F Us l).run none).run = (true, none) →
          ∃ u', VLevel.ofLevel Us l = some u')) (s) :
      ((do if !(← getUndefParam.F Us l) then pure () else g) |>.run s).run.snd = none →
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
local instance : Std.LawfulBEqCmp (α := Name) compare :=
  inferInstanceAs (Std.LawfulBEqCmp Name.cmp)
local instance : Std.LawfulBEqCmp (α := List Name) compare :=
  inferInstanceAs (Std.LawfulBEqCmp (List.compareLex Name.cmp))

instance : LawfulBEq VarNode where
  rfl {a} := by cases a <;> simp! +instances [instBEqVarNode]
  eq_of_beq {a b} := by cases a <;> cases b <;> simp! +instances [instBEqVarNode]

@[reducible] local instance : Membership (List Name) NormLevel :=
  inferInstanceAs (Membership _ (Std.TreeMap _ _ compare))

@[reducible] local instance : GetElem? NormLevel (List Name) Node (fun m a => a ∈ m) :=
  inferInstanceAs (GetElem? (Std.TreeMap _ _ compare) ..)

inductive Extend1 : List α → α → List α → Prop
  | mk : Extend1 (l₁ ++ l₂) v (l₁ ++ v :: l₂)

theorem Extend1.base : Extend1 l v (v::l) := .mk (l₁ := [])
theorem Extend1.cons (H : Extend1 l v l') : Extend1 (a::l) v (a::l') :=
  let .mk := H; .mk (l₁ := _::_)

theorem Extend1.mem (H : Extend1 p a p') : b ∈ p' ↔ b = a ∨ b ∈ p := by cases H; simp [or_left_comm]

theorem Extend1.length (H : Extend1 p a p') : p'.length = p.length + 1 := by
  cases H; simp [Nat.add_assoc]

theorem Extend1.of_mem (h : a ∈ p') : ∃ p, Extend1 p a p' := by
  obtain ⟨_, _, rfl, _⟩ := List.eq_append_cons_of_mem h; exact ⟨_, .mk⟩

theorem Extend1.orderedInsert (H : orderedInsert cmp v p = some p') : Extend1 p v p' := by
  induction p generalizing p' with simp [Normalize.orderedInsert] at H
  | nil => exact H ▸ .base
  | cons _ _ ih =>
    split at H <;> [(cases H; exact .base); cases H; skip]
    simp at H; obtain ⟨_, H, rfl⟩ := H; exact (ih H).cons

inductive Extend? : List α → α → List α → Prop
  | mk1 : Extend1 l v l' → Extend? l v l'
  | mk0 : v ∈ l → Extend? l v l

theorem Extend?.cons (H : Extend? l v l') : Extend? (a::l) v (a::l') := by
  cases H with
  | mk1 H => exact .mk1 H.cons
  | mk0 H => exact .mk0 (.tail _ H)

theorem Extend?.mem (H : Extend? p a p') : b ∈ p' ↔ b = a ∨ b ∈ p := by
  cases H with
  | mk1 H => exact H.mem
  | mk0 H => simp; rintro rfl; exact H

theorem Extend?.orderedInsert [BEq α] [LawfulBEq α] [Std.LawfulBEqCmp (α := α) cmp] :
    Extend? p v ((orderedInsert cmp v p).getD p) := by
  induction p with simp [Normalize.orderedInsert]
  | nil => exact .mk1 .base
  | cons _ _ ih =>
    split
    · exact .mk1 .base
    · simp_all; exact .mk0 (.head _)
    · revert ih; cases Normalize.orderedInsert .. <;> exact .cons

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
  simp [addConst] at *; split <;> simp [H, Std.TreeMap.mem_alter]; split <;> simp

theorem NormLevel.addConst_contains_self (h : k ≠ 0) (h2 : ¬(k = 1 ∧ path ≠ [])) :
    (addConst k path acc).contains path := by
  simp [addConst, h, h2]; split <;> simp

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

theorem imax_max : Lean.Nat.imax a (max' b c) = max' (Lean.Nat.imax a b) (Lean.Nat.imax a c) := by
  simp [Lean.Nat.imax]; symm; split <;> simp [*]; split <;> simp [*, Nat.max_eq_max]
  rw [Nat.max_left_comm b, ← Nat.max_assoc, Nat.max_self]

theorem imax_imax : Lean.Nat.imax a (Lean.Nat.imax b c) =
    max' (Lean.Nat.imax a c) (Lean.Nat.imax b c) := by
  simp [Lean.Nat.imax]; by_cases h : c = 0 <;> simp [*, Nat.max_eq_max]
  rw [Nat.max_left_comm c, Nat.max_self]

protected theorem Extend?.allNZ (H : Extend? p a p') : allNZ ls ρ p' = allNZ ls ρ (a :: p) := by
  rw [Bool.eq_iff_iff]; simp [allNZ, H.mem]

protected theorem Extend?.evalPath (H : Extend? p a p') :
    evalPath ls ρ p' = evalPath ls ρ (a :: p) := by ext n; simp [evalPath, H.allNZ]

theorem ext_le {n m : Nat} (H : ∀ x, n ≤ x ↔ m ≤ x) : n = m :=
  Nat.le_antisymm ((H _).2 (Nat.le_refl _)) ((H _).1 (Nat.le_refl _))

theorem le_ext_le {n m : Nat} (H : ∀ x, n ≤ x → m ≤ x) : m ≤ n := H _ (Nat.le_refl _)

/-- Condition sets are strictly sorted, which is what makes `subset` a decision procedure
for inclusion: it is built up by `orderedInsert` from the empty set. -/
def Sorted (l : List Name) : Prop := l.Pairwise (compare · · = .lt)

nonrec theorem Sorted.nil : Sorted [] := .nil

theorem Sorted.of_cons (h : Sorted (a :: l)) : Sorted l := (List.pairwise_cons.1 h).2

theorem Sorted.head (h : Sorted (a :: l)) : ∀ b ∈ l, compare a b = .lt :=
  (List.pairwise_cons.1 h).1

theorem Sorted.erase (h : Sorted l) : Sorted (l.erase a) := h.sublist (List.erase_sublist ..)

theorem Sorted.nodup (h : Sorted l) : l.Nodup :=
  h.imp <| by rintro _ _ hab rfl; rw [Std.ReflOrd.compare_self] at hab; cases hab

theorem Sorted.orderedInsert (h : Sorted l) (he : orderedInsert Name.cmp a l = some l') :
    Sorted l' := by
  induction l generalizing l' with | nil => cases he; exact .cons (by simp) .nil | cons b l ih
  simp only [Normalize.orderedInsert] at he
  split at he <;> rename_i hab
  · cases he
    refine .cons (fun c hc => ?_) h
    obtain rfl | hc := List.mem_cons.1 hc
    · exact hab
    · exact Std.TransCmp.lt_trans hab (h.head _ hc)
  · cases he
  · simp only [Option.map_eq_some_iff] at he
    obtain ⟨l'', he, rfl⟩ := he
    refine .cons (fun c hc => ?_) (ih h.of_cons he)
    -- `c` is either `a`, which is above `b`, or an element of `l`
    obtain rfl | hc := (Extend1.orderedInsert he).mem.1 hc
    · exact Std.OrientedCmp.lt_of_gt hab
    · exact h.head _ hc

/-- The well-formedness invariant of the `NormLevel` maps produced by `normalizeAux`:
every variable recorded at a key is an element of that key, and every nonempty key `p`
extends another key of the map by a single variable that is recorded at `p`.
The latter is what makes the sublevels expressible by `imax` chains (see the reconstruction
comment in `Lean4Lean.Level`), and it lets `addConst` drop `C(p, 1)` for `p ≠ []`. -/
def NormLevel.WF (s : NormLevel) : Prop :=
  ∀ p n, s.get? p = some n →
    (p ≠ [] → ∃ v p', Extend1 p' v p ∧ (p' = [] ∨ s.contains p') ∧ ∃ x ∈ n.var, x.var = v) ∧
    (∀ v ∈ n.var, v.var ∈ p) ∧ Sorted p

theorem NormLevel.WF.of_mem (hm : v ∈ path) (H : WF s) (hp : s.contains path) :
    ∃ path₁ path₂ n, (∀ x ∈ path₁, x ∈ path) ∧
      Extend1 path₁ v path₂ ∧ (path₁ = [] ∨ s.contains path₁) ∧ s.get? path₂ = some n ∧
      ∃ x ∈ n.var, x.var = v := by
  generalize eq : path.length = n
  induction n generalizing path with | zero => simp at eq; subst path; cases hm | succ n ih
  have ⟨_, hp'⟩ := Option.isSome_iff_exists.1 (Std.TreeMap.isSome_getElem?_eq_contains.trans hp)
  have ⟨_, _, a1, a2, a3⟩ := (H _ _ hp').1 (by rintro rfl; cases hm)
  obtain rfl | hm := a1.mem.1 hm
  · exact ⟨_, _, _, fun _ h => a1.mem.2 (.inr h), a1, a2, hp', a3⟩
  · -- the parent is in the map, since `v` occurs in it and so it is not the root
    have ⟨_, _, _, b1, b2⟩ := ih hm (a2.resolve_left (by rintro rfl; cases hm))
      (by cases a1; simp at eq ⊢; exact Nat.succ_inj.1 eq)
    exact ⟨_, _, _, fun _ h => a1.mem.2 (.inr (b1 _ h)), b2⟩

theorem NormLevel.WF.sortedOf {s : NormLevel} (wf : s.WF) (H : path = [] ∨ s.contains path) :
    Sorted path := by
  obtain rfl | h := H
  · exact Sorted.nil
  · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (Std.TreeMap.isSome_getElem?_eq_contains.trans h)
    exact (wf _ _ hn).2.2

theorem VarNode.mem_addVar :
    (∃ x ∈ VarNode.addVar v k l, x.var = u) ↔ v = u ∨ (∃ x ∈ l, x.var = u) := by
  induction l with simp [addVar] | cons x l ih; split <;> simp_all [or_left_comm]

theorem NormLevel.addVar_wf (hv : v ∈ path) (wf : acc.WF) :
    (addVar v k path acc).WF := by
  simp [addVar, WF, Std.TreeMap.getElem?_modify, Std.TreeMap.mem_modify] at wf ⊢
  intro p n; split <;> [simp; apply wf]
  subst p; rintro _ h rfl; have ⟨a1, a2, a3⟩ := wf _ _ h
  refine ⟨fun h => ?_, fun _ h => ?_, a3⟩
  · have ⟨_, _, b1, b2, b3⟩ := a1 h; exact ⟨_, _, b1, b2, VarNode.mem_addVar.2 (.inr b3)⟩
  · obtain eq | ⟨_, h, eq⟩ := VarNode.mem_addVar.1 ⟨_, h, rfl⟩
    · exact eq ▸ hv
    · exact eq ▸ a2 _ h

theorem NormLevel.addNode_wf (H : Extend1 path v path') (hs : Sorted path')
    (hacc : path = [] ∨ acc.contains path) (wf : acc.WF) : (addNode v k path' acc).WF := by
  simp [addNode, WF, Std.TreeMap.getElem?_alter, Std.TreeMap.mem_alter] at *
  intro p n; split
  · subst p; split <;> rintro ⟨⟩ <;> simp
    · exact ⟨fun _ => ⟨_, _, H, hacc.imp id fun h _ => h, rfl⟩, H.mem.2 (.inl rfl), hs⟩
    · obtain ⟨a1, a2, a3⟩ := wf _ _ ‹_›; refine ⟨fun h => ?_, fun _ h => ?_, a3⟩
      · have ⟨_, _, b1, b2, b3⟩ := a1 h
        exact ⟨_, _, b1, b2.imp id fun h _ => h, VarNode.mem_addVar.2 (.inr b3)⟩
      · obtain eq | ⟨_, h, eq⟩ := VarNode.mem_addVar.1 ⟨_, h, rfl⟩
        · exact H.mem.2 (.inl eq.symm)
        · exact eq ▸ a2 _ h
  · intro h; have ⟨a1, a2, a3⟩ := wf _ _ h; refine ⟨fun h => ?_, a2, a3⟩
    have ⟨_, _, b1, b2, b3⟩ := a1 h; refine ⟨_, _, b1, ?_, b3⟩
    split <;> [split <;> simp; exact b2]

/-- `WF` survives an update that only adds keys and preserves each node's variables, provided
any key it adds is the root, where the parent condition is vacuous. -/
theorem NormLevel.WF.update {s s' : NormLevel} (wf : s.WF)
    (hk : ∀ q, s.contains q → s'.contains q)
    (hv : ∀ p n, s'.get? p = some n →
      (∃ n₀, s.get? p = some n₀ ∧ n.var = n₀.var) ∨ (p = [] ∧ n.var = [])) : s'.WF := by
  intro p n hn
  rcases hv p n hn with ⟨n₀, h₀, hvar⟩ | ⟨rfl, hvar⟩
  · obtain ⟨a1, a2, a3⟩ := wf _ _ h₀
    refine ⟨fun h => ?_, fun v hv => a2 v (hvar ▸ hv), a3⟩
    obtain ⟨v, p', b1, b2, b3⟩ := a1 h
    exact ⟨v, p', b1, b2.imp id (hk _), hvar ▸ b3⟩
  · exact ⟨absurd rfl, by simp [hvar], Sorted.nil⟩

theorem NormLevel.addConst_wf (hp : path = [] ∨ acc.contains path) (H : acc.WF) :
    (addConst k path acc).WF := by
  simp only [addConst]; split <;> [exact H; skip]
  refine H.update (fun q hq => ?_) fun p n hn => ?_
  · rw [Std.TreeMap.contains_alter]; split <;> [split <;> simp; simp [hq]]
  · rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_alter] at hn
    split at hn <;> [rename_i hpe; exact .inl ⟨n, hn, rfl⟩]
    cases eq_of_beq (Std.LawfulBEqCmp.compare_eq_iff_beq.1 hpe)
    -- `alter` creates a node only at the root, since otherwise `path` is already a key
    match hpath : acc[path]?, hp with
    | some n', _ => rw [hpath] at hn; cases hn; exact .inl ⟨n', hpath, rfl⟩
    | none, .inl hr => rw [hpath] at hn; cases hn; exact .inr ⟨hr, rfl⟩
    | none, .inr h => simp [Std.TreeMap.mem_iff_isSome_getElem?, hpath] at h

theorem normalizeAux_wf (H : path = [] ∨ acc.contains path) (wf : acc.WF) :
    (normalizeAux u path k acc).WF := by
  unfold normalizeAux; split
  · exact NormLevel.addConst_wf H wf
  · exact NormLevel.addConst_wf H wf
  · exact normalizeAux_wf H wf
  · exact normalizeAux_wf (H.imp id normalizeAux_contains) (normalizeAux_wf H wf)
  · exact normalizeAux_wf (H.imp id normalizeAux_contains) (normalizeAux_wf H wf)
  · exact normalizeAux_wf (H.imp id normalizeAux_contains) (normalizeAux_wf H wf)
  · exact normalizeAux_wf (H.imp id normalizeAux_contains) (normalizeAux_wf H wf)
  · split <;> rename_i eq <;> [skip; (dsimp; split)]
    · exact normalizeAux_wf (.inr NormLevel.addNode_contains_self)
        (NormLevel.addNode_wf (.orderedInsert eq) ((wf.sortedOf H).orderedInsert eq)
        (H.imp id NormLevel.addConst_contains) (NormLevel.addConst_wf H wf))
    · exact normalizeAux_wf H wf
    · refine normalizeAux_wf (H.imp id NormLevel.addVar_contains) (NormLevel.addVar_wf ?_ wf)
      exact (eq ▸ Extend?.orderedInsert).mem.2 (.inl rfl)
  · exact wf
  · exact wf
  · split <;> rename_i eq <;> [skip; split]
    · exact NormLevel.addNode_wf (.orderedInsert eq) ((wf.sortedOf H).orderedInsert eq)
        (H.imp id NormLevel.addConst_contains) (NormLevel.addConst_wf H wf)
    · exact wf
    · exact NormLevel.addVar_wf ((eq ▸ Extend?.orderedInsert).mem.2 (.inl rfl)) wf

theorem NormLevel.addConst_eval (H : path = [] ∨ acc.contains path) (wf : acc.WF) :
    (addConst k path acc).eval ls ρ = max' (acc.eval ls ρ) (evalPath ls ρ path k) := by
  simp [addConst]; split <;> rename_i h
  · obtain rfl | ⟨rfl, hne⟩ := h
    · simp [evalPath]
    · -- `C(p, 1)` for `p ≠ []` is already dominated: `WF` puts a variable of `p` at `p`,
      -- and along a nonzero path that variable is at least 1
      rw [Nat.max_eq_left]; refine evalPath_le.2 fun nz => le_ext_le fun n le => ?_
      have H := H.resolve_left hne
      rw [← Std.TreeMap.isSome_getElem?_eq_contains, Option.isSome_iff_exists] at H
      let ⟨v, H⟩ := H; have ⟨_, _, a1, a2, _, a3, rfl⟩ := (wf _ _ H).1 ‹_›
      have := (Node.eval_le.1 (evalPath_le.1 (eval_le.1 le _ _ H) nz)).2 _ a3
      simp [allNZ] at nz
      exact Nat.le_trans (nz _ (a1.mem.2 (.inl rfl))) (Nat.le_of_add_right_le this)
  · refine ext_le fun x => ?_
    simp [eval_le, Nat.max_le, Std.TreeMap.getElem?_alter, evalPath_le, Node.eval_le]
    refine ⟨fun H => ⟨fun a b h nz => ?_, fun nz => ?_⟩, fun ⟨H1, H2⟩ a b h nz => ?_⟩
    · have := H a; split at this
      · subst a; rw [h] at this
        obtain ⟨hc, hv⟩ := this _ rfl nz
        exact ⟨Nat.le_trans (Nat.le_max_right ..) hc, hv⟩
      · exact this _ h nz
    · have := H path; rw [if_pos rfl] at this; split at this <;>
        refine Nat.le_trans ?_ ((this _ rfl nz).1)
      · exact Nat.le_refl _
      · exact Nat.le_max_left ..
    · split at h
      · subst a; split at h <;> cases h <;> [exact ⟨H2 nz, by simp⟩; rename_i n hn]
        obtain ⟨hc, hv⟩ := H1 _ _ hn nz
        exact ⟨Nat.max_le.2 ⟨H2 nz, hc⟩, hv⟩
      · exact H1 _ _ h nz

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

/-- The invariant threaded through `normalizeAux`: the current path is either the root, which
`addConst` creates on demand, or already a key of the map, created by an earlier `addNode`.
`addVar` is only reached in the second case, since it runs only when `path` already contains
the variable being added. -/
theorem normalizeAux_eval (hu : VLevel.ofLevel ls u = some u')
    (H : path = [] ∨ acc.contains path) (wf : acc.WF) :
    (normalizeAux u path k acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (u'.eval ρ + k)) := by
  unfold normalizeAux; split
  · cases hu; simp [NormLevel.addConst_eval H wf, VLevel.eval]
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    simp [VLevel.eval, Lean.Nat.imax, NormLevel.addConst_eval H wf]
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    rw [normalizeAux_eval hu H wf, Nat.add_succ, ← Nat.succ_add]; rfl
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, hv, rfl⟩ := hu
    rw [normalizeAux_eval hv (H.imp id normalizeAux_contains) (normalizeAux_wf H wf),
      normalizeAux_eval hu H wf, Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; rfl
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval hv (H.imp id normalizeAux_contains) (normalizeAux_wf H wf),
      normalizeAux_eval hu H wf, Nat.max_assoc, Nat.add_succ, ← Nat.succ_add,
      ← evalPath_max, Nat.add_max_add_right]; rfl
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩)
        (H.imp id normalizeAux_contains) (normalizeAux_wf H wf),
      normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hv, rfl⟩) H wf,
      Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; simp [VLevel.eval, imax_max]
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hv, _, hw, rfl⟩)
        (H.imp id normalizeAux_contains) (normalizeAux_wf H wf),
      normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) H wf,
      Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; simp [VLevel.eval, imax_imax]
  · rename_i u v
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨hv, rfl⟩, rfl⟩ := hu
    have := Extend?.orderedInsert (cmp := Name.cmp) (p := path) (v := v)
    split <;> rename_i h <;> simp [h] at this
    · rw [normalizeAux_eval hu (.inr NormLevel.addNode_contains_self)
        (NormLevel.addNode_wf (.orderedInsert h) ((wf.sortedOf H).orderedInsert h)
          (H.imp id NormLevel.addConst_contains) (NormLevel.addConst_wf H wf)),
        NormLevel.addNode_eval, NormLevel.addConst_eval H wf, Nat.max_assoc,
        Nat.max_assoc, ← evalPath_max, this.evalPath, evalPath_cons, ← evalPath_max,
          Nat.add_max_add_right]; congr 2
      simp [VLevel.eval, ← evalParam_eq hv, Lean.Nat.imax]
      cases evalParam .. <;> simp [Nat.max_eq_max, Nat.max_comm]
    · have hne : path ≠ [] := by rintro rfl; simp [orderedInsert] at h
      dsimp; split
      · rw [normalizeAux_eval hu H wf]
        simp [evalPath]; split <;> [rename_i nz; simp]
        have hm := this.mem.2 (.inl rfl)
        obtain ⟨p1, p2, w1, a1, a2, a3, a4, z, a5, rfl⟩ := wf.of_mem hm (H.resolve_left hne)
        refine ext_le fun n => ?_; simp [Nat.max_le, NormLevel.eval_le]; intro he
        have := Node.eval_le.1 (evalPath_le.1 (he _ _ a4)
          (allNZ_mono (fun _ h => (a2.mem.1 h).elim (· ▸ hm) (a1 _)) nz)) |>.2 _ a5
        simp [allNZ] at nz; specialize nz _ hm
        simp [VLevel.eval, Lean.Nat.imax]; simp [← evalParam_eq hv, VarNode.eval] at this ⊢
        revert this nz; cases evalParam .. <;> simp [Nat.max_eq_max]; omega
      · rw [normalizeAux_eval hu (H.imp id NormLevel.addVar_contains)
            (NormLevel.addVar_wf (this.mem.2 (.inl rfl)) wf),
          NormLevel.addVar_eval (H.resolve_left hne), Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right,
          this.evalPath, evalPath_cons, evalPath_cons]; congr 2
        split <;> simp [VLevel.eval, Lean.Nat.imax]
        rename_i h; revert h; simp [← evalParam_eq hv]
        cases evalParam .. <;> simp [Nat.max_eq_max, Nat.max_comm]
  · cases hu
  · simp [VLevel.ofLevel] at hu
  · rename_i v; simp [VLevel.ofLevel] at hu; obtain ⟨hv, rfl⟩ := hu
    have := Extend?.orderedInsert (cmp := Name.cmp) (p := path) (v := v)
    split <;> rename_i h <;> simp [h] at this
    · rw [NormLevel.addNode_eval, NormLevel.addConst_eval H wf, Nat.max_assoc,
        this.evalPath, evalPath_cons, ← evalPath_max]
      simp [VLevel.eval, ← evalParam_eq hv]; congr 2; split <;> simp; omega
    have hne : path ≠ [] := by rintro rfl; simp [orderedInsert] at h
    split
    · simp [evalPath]; split <;> [rename_i nz; simp]
      have hm := this.mem.2 (.inl rfl)
      obtain ⟨p1, p2, w1, a1, a2, a3, a4, z, a5, rfl⟩ := wf.of_mem hm (H.resolve_left hne)
      refine ext_le fun n => ?_; simp [Nat.max_le, NormLevel.eval_le]; intro he
      have := Node.eval_le.1 (evalPath_le.1 (he _ _ a4)
        (allNZ_mono (fun _ h => (a2.mem.1 h).elim (· ▸ hm) (a1 _)) nz)) |>.2 _ a5
      simp [allNZ] at nz; specialize nz _ hm
      simp [VLevel.eval]; simp [← evalParam_eq hv, VarNode.eval] at this ⊢
      revert this nz; cases evalParam .. <;> simp; omega
    · rw [NormLevel.addVar_eval (H.resolve_left hne), this.evalPath, evalPath_cons,
        evalPath_cons]
      congr 2; split <;> simp [VLevel.eval, ← evalParam_eq hv]

theorem subset_length (H : subset cmp l₁ l₂) : l₁.length ≤ l₂.length := by
  induction l₂ generalizing l₁ with | nil => cases l₁ <;> simp_all [subset] | cons y l₂ ih
  cases l₁ with | nil => simp | cons x l₁
  simp only [subset] at H; split at H
  · cases H
  · have := ih H; simp only [List.length_cons]; omega
  · have := ih H; simp only [List.length_cons] at this ⊢; omega

theorem subset_mem [BEq α] [LawfulBEq α] [Std.LawfulBEqCmp (α := α) cmp]
    (H : subset cmp l₁ l₂) (h : a ∈ l₁) : a ∈ l₂ := by
  induction l₂ generalizing l₁ with | nil => cases l₁ <;> simp_all [subset] | cons y l₂ ih
  cases l₁ with| nil => cases h | cons x l₁
  simp only [subset] at H; split at H
  · cases H
  · rename_i h'; rw [Std.LawfulBEqCmp.compare_eq_iff_beq] at h'
    cases eq_of_beq h'
    rcases List.mem_cons.1 h with rfl | h
    · exact .head _
    · exact .tail _ (ih H h)
  · exact .tail _ (ih H h)

theorem subset_eq [BEq α] [LawfulBEq α] [Std.LawfulBEqCmp (α := α) cmp]
    (H : subset cmp l₁ l₂) (hl : l₁.length = l₂.length) : l₁ = l₂ := by
  induction l₂ generalizing l₁ with | nil => cases l₁ <;> simp_all [subset] | cons y l₂ ih
  cases l₁ with | nil => cases hl | cons x l₁
  simp only [subset] at H; simp only [List.length_cons] at hl
  split at H
  · cases H
  · rename_i h'; rw [Std.LawfulBEqCmp.compare_eq_iff_beq] at h'
    cases eq_of_beq h'; rw [ih H (by omega)]
  · exact absurd (subset_length H) (by simp only [List.length_cons]; omega)

/-- On sorted lists, `subset` decides inclusion. -/
theorem subset_of_sorted (h₁ : Sorted l₁) (h₂ : Sorted l₂) (h : ∀ x ∈ l₁, x ∈ l₂) :
    subset compare l₁ l₂ := by
  induction l₂ generalizing l₁ with
  | nil => cases l₁ with | nil => rfl | cons x l₁ => cases h x (.head _)
  | cons y l₂ ih
  cases l₁ with | nil => rfl | cons x l₁
  simp only [subset]
  have hxy := h x (.head _)
  split <;> rename_i hc
  · -- `x < y` is impossible: `x` is in `y :: l₂`, whose elements are all `≥ y`
    obtain rfl | hx := List.mem_cons.1 hxy
    · rw [Std.ReflOrd.compare_self] at hc; cases hc
    · exact absurd (h₂.head _ hx) (by rw [Std.OrientedCmp.gt_of_lt hc]; simp)
  · rw [Std.LawfulBEqCmp.compare_eq_iff_beq] at hc
    cases eq_of_beq hc
    refine ih h₁.of_cons h₂.of_cons fun z hz => ?_
    obtain rfl | hz' := List.mem_cons.1 (h z (.tail _ hz))
    · exact absurd (h₁.head _ hz) (by rw [Std.ReflOrd.compare_self]; simp)
    · exact hz'
  · refine ih h₁ h₂.of_cons fun z hz => ?_
    obtain rfl | hz' := List.mem_cons.1 (h z hz)
    · obtain rfl | hz := List.mem_cons.1 hz
      · exact absurd hc (by rw [Std.ReflOrd.compare_self]; simp)
      · exact absurd (h₁.head _ hz) (by
          rw [Std.OrientedCmp.gt_of_lt (Std.OrientedCmp.lt_of_gt hc)]; simp)
    · exact hz'

theorem subsumeVars_subset (h : x ∈ subsumeVars vs₁ vs₂) : x ∈ vs₁ := by
  induction vs₁ generalizing vs₂ with | nil => simp_all [subsumeVars] | cons a vs₁ ih
  induction vs₂ with | nil => simp_all [subsumeVars] | cons b vs₂ ih₂
  simp only [subsumeVars] at h; split at h
  · obtain rfl | h := List.mem_cons.1 h
    · exact .head _
    · exact .tail _ (ih h)
  · split at h <;> [exact .tail _ (ih h); skip]
    obtain rfl | h := List.mem_cons.1 h
    · exact .head _
    · exact .tail _ (ih h)
  · exact ih₂ h

theorem subsumeVars_dominated (h₁ : x ∈ vs₁) (h₂ : x ∉ subsumeVars vs₁ vs₂) :
    ∃ y ∈ vs₂, y.var = x.var ∧ x.offset ≤ y.offset := by
  induction vs₁ generalizing vs₂ with | nil => cases h₁ | cons a vs₁ ih
  induction vs₂ with | nil => exact absurd h₁ (by simpa [subsumeVars] using h₂) | cons b vs₂ ih₂
  simp only [subsumeVars] at h₂; split at h₂
  · obtain rfl | h₁ := List.mem_cons.1 h₁
    · cases h₂ (.head _)
    · have ⟨y, hy, e, le⟩ := ih h₁ fun h => h₂ (.tail _ h)
      exact ⟨y, hy, e, le⟩
  · rename_i heq; split at h₂
    · obtain rfl | h₁ :=  List.mem_cons.1 h₁
      · rw [Std.LawfulBEqCmp.compare_eq_iff_beq] at heq
        exact ⟨b, .head _, (eq_of_beq heq).symm, ‹_›⟩
      · have ⟨y, hy, e, le⟩ := ih h₁ h₂
        exact ⟨y, .tail _ hy, e, le⟩
    · obtain rfl | h₁ :=  List.mem_cons.1 h₁
      · cases h₂ (.head _)
      · have ⟨y, hy, e, le⟩ := ih h₁ fun h => h₂ (.tail _ h)
        exact ⟨y, .tail _ hy, e, le⟩
  · have ⟨y, hy, e, le⟩ := ih₂ h₂
    exact ⟨y, .tail _ hy, e, le⟩

theorem le_foldl_max {vs : List VarNode}
    (h : c ≤ vs.foldl (·.max ·.offset) n + 1) : c ≤ n + 1 ∨ ∃ y ∈ vs, c ≤ y.offset + 1 := by
  induction vs generalizing n with | nil => exact .inl h | cons x vs ih
  obtain h | ⟨y, hy, h⟩ := ih h
  · refine (Nat.le_total x.offset n).imp (fun h' => ?_) (fun h' => ⟨x, .head _, ?_⟩)
    · simp [Nat.max_eq_left h'] at h; omega
    · simp [Nat.max_eq_right h'] at h; omega
  · exact .inr ⟨y, .tail _ hy, h⟩

theorem Node.const_le_eval {l : Node} : l.const ≤ Node.eval ls ρ l :=
  (Node.eval_le.1 (Nat.le_refl _)).1

theorem Node.var_le_eval {l : Node} (h : x ∈ l.var) :
    VarNode.eval ls ρ x ≤ Node.eval ls ρ l :=
  (Node.eval_le.1 (Nat.le_refl _)).2 _ h

theorem Node.eval_empty {l : Node} (H : l.isEmpty) : Node.eval ls ρ l = 0 := by
  simp [Node.isEmpty] at H; simp [eval, H.1, H.2]

theorem NormLevel.eval_filter {m : NormLevel} :
    NormLevel.eval ls ρ (m.filter fun _ n => !n.isEmpty) = m.eval ls ρ := by
  refine ext_le fun x => ?_
  simp only [eval_le, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_filter]
  refine ⟨fun H a b h => ?_, fun H a b h => ?_⟩
  · by_cases he : b.isEmpty
    · simp [evalPath_le, Node.eval_empty he]
    · exact H a b (by simp [h, he])
  · exact H _ _ (Option.eq_some_of_pfilter_eq_some h)

theorem subsumeVars_eval (H : ∀ v ∈ vs₂, VarNode.eval ls ρ v ≤ n) :
    (∀ v ∈ subsumeVars vs₁ vs₂, VarNode.eval ls ρ v ≤ n) ↔
    ∀ v ∈ vs₁, VarNode.eval ls ρ v ≤ n := by
  refine ⟨fun h v hv => ?_, fun h v hv => h _ (subsumeVars_subset hv)⟩
  by_cases hs : v ∈ subsumeVars vs₁ vs₂ <;> [exact h _ hs; skip]
  have ⟨y, hy, e, le⟩ := subsumeVars_dominated hv hs
  exact Nat.le_trans (by simp [VarNode.eval, e]; omega) (H _ hy)

theorem Node.subsumeBy_const_eq {same : Bool} {n₁ n₂ : Node} :
    (n₁.subsumeBy same n₂).const =
    if n₁.const = 0 ||
      (same || n₁.const > n₂.const) &&
      (n₂.var.isEmpty || n₁.const > n₂.var.foldl (·.max ·.offset) 0 + 1)
    then n₁.const else 0 := by
  simp only [Node.subsumeBy]; split <;> split <;> rfl

theorem Node.subsumeBy_var_eq {same : Bool} {n₁ n₂ : Node} :
    (n₁.subsumeBy same n₂).var =
    if same || n₂.var.isEmpty then n₁.var else subsumeVars n₁.var n₂.var := by
  simp only [Node.subsumeBy]; split <;> split <;> simp

theorem Node.subsumeBy_var_subset {same : Bool}
    (h : x ∈ (Node.subsumeBy same n₁ n₂).var) : x ∈ n₁.var := by
  rw [Node.subsumeBy_var_eq] at h; split at h <;> [exact h; exact subsumeVars_subset h]

theorem Node.subsumeBy_const_cases {same : Bool} (n₁ n₂ : Node) :
    (n₁.subsumeBy same n₂).const = n₁.const ∨ (n₁.subsumeBy same n₂).const = 0 := by
  rw [Node.subsumeBy_const_eq]; split <;> [exact .inl rfl; exact .inr rfl]

theorem Node.subsumeBy_eval_le {same : Bool} :
    Node.eval ls ρ (n₁.subsumeBy same n₂) ≤ Node.eval ls ρ n₁ := by
  refine Node.eval_le.2 ⟨?_, fun v h => Node.var_le_eval (Node.subsumeBy_var_subset h)⟩
  obtain h | h := Node.subsumeBy_const_cases (same := same) n₁ n₂
  · exact h ▸ Node.const_le_eval
  · simp [h]

/-- If `subsumeBy` dropped the constant, the drop was justified: the constant is dominated
by the constant of `n₂` (only possible when the two keys differ), or by a variable of `n₂`. -/
theorem Node.subsumeBy_const_drop {same : Bool}
    (h : (Node.subsumeBy same n₁ n₂).const ≠ n₁.const) :
    same = false ∧ n₁.const ≤ n₂.const ∨ ∃ y ∈ n₂.var, n₁.const ≤ y.offset + 1 := by
  rw [Node.subsumeBy_const_eq] at h
  split at h <;> [cases h rfl; rename_i hc]
  rw [Bool.or_eq_true, not_or] at hc
  obtain ⟨-, hc⟩ := hc
  rw [Bool.and_eq_true, Decidable.not_and_iff_not_or_not] at hc
  obtain hc | hc := hc <;> rw [Bool.or_eq_true, not_or] at hc <;> obtain ⟨h1, h2⟩ := hc
  · exact .inl ⟨by simpa using h1, by simpa [Nat.not_lt] using h2⟩
  · have hne : n₂.var ≠ [] := fun e => h1 (by simp [e])
    have h2 : n₁.const ≤ n₂.var.foldl (·.max ·.offset) 0 + 1 := by
      simpa [Nat.not_lt] using h2
    obtain h | h := le_foldl_max (c := n₁.const) (n := 0) h2
    · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
      exact .inr ⟨y, hy, by omega⟩
    · exact .inr h

/-- The domination step is exact against a node bounded by `m`: everything `subsumeBy`
drops from `n₁` is dominated by a sublevel of `n₂`, and `n₂` evaluates to at most `m`.
Domination of the constant by a variable needs that variable to evaluate to at least its
offset plus one, which is why the condition set must be all-nonzero (`hnz`). -/
theorem Node.subsumeBy_eval_iff {same : Bool} {n₁ n₂ : Node} {m : Nat}
    (hnz : ∀ v ∈ n₂.var, 0 < evalParam ls ρ v.var) (h₂ : Node.eval ls ρ n₂ ≤ m) :
    Node.eval ls ρ (n₁.subsumeBy same n₂) ≤ m ↔ Node.eval ls ρ n₁ ≤ m := by
  have hvar₂ v (hv : v ∈ n₂.var) : VarNode.eval ls ρ v ≤ m :=
    Nat.le_trans (Node.var_le_eval hv) h₂
  refine ⟨fun h => ?_, fun h => Nat.le_trans Node.subsumeBy_eval_le h⟩
  rw [Node.eval_le] at h ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · by_cases hc : (n₁.subsumeBy same n₂).const = n₁.const
    · exact hc ▸ h.1
    obtain ⟨-, hle⟩ | ⟨y, hy, hle⟩ := Node.subsumeBy_const_drop hc
    · exact Nat.le_trans hle (Nat.le_trans Node.const_le_eval h₂)
    · refine Nat.le_trans ?_ (hvar₂ _ hy)
      have := hnz _ hy; simp only [VarNode.eval]; omega
  · rw [Node.subsumeBy_var_eq] at h
    split at h
    · exact h.2 _ hx
    · exact (subsumeVars_eval hvar₂).1 h.2 _ hx

theorem Node.subsume_const_eq : (Node.subsume p₁ n₁ p₂ n₂).const =
    if !subset compare p₂ p₁ ||
      (n₁.const = 0 ||
      (p₁.length == p₂.length || n₁.const > n₂.const) &&
      (n₂.var.isEmpty || n₁.const > n₂.var.foldl (·.max ·.offset) 0 + 1))
    then n₁.const else 0 := by
  simp only [Node.subsume]
  cases hs : subset compare p₂ p₁ <;>
    simp only [reduceIte, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or]
  · rfl
  · exact subsumeBy_const_eq

theorem Node.subsume_var_eq : (Node.subsume p₁ n₁ p₂ n₂).var =
    if !subset compare p₂ p₁ || (p₁.length == p₂.length || n₂.var.isEmpty)
    then n₁.var else subsumeVars n₁.var n₂.var := by
  simp only [Node.subsume]
  cases hs : subset compare p₂ p₁ <;>
    simp only [reduceIte, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or]
  · rfl
  · exact subsumeBy_var_eq

theorem Node.subsume_var_subset (h : x ∈ (Node.subsume p₁ n₁ p₂ n₂).var) : x ∈ n₁.var := by
  rw [Node.subsume] at h; split at h <;> [exact subsumeBy_var_subset h; exact h]

theorem Node.subsume_const_cases (p₁ n₁ p₂ n₂) :
    (Node.subsume p₁ n₁ p₂ n₂).const = n₁.const ∨ (Node.subsume p₁ n₁ p₂ n₂).const = 0 := by
  rw [Node.subsume]; split <;> [exact subsumeBy_const_cases ..; exact .inl rfl]

theorem Node.subsume_eval_le :
    Node.eval ls ρ (Node.subsume p₁ n₁ p₂ n₂) ≤ Node.eval ls ρ n₁ := by
  rw [Node.subsume]; split <;> [exact subsumeBy_eval_le; exact Nat.le_refl _]

/-- If `subsume` dropped the constant, the drop was justified: the constant is dominated
by the constant of `n₂` at a strictly smaller key, or by a variable of `n₂`. -/
theorem Node.subsume_const_drop (h : (Node.subsume p₁ n₁ p₂ n₂).const ≠ n₁.const) :
    subset compare p₂ p₁ ∧
    (p₁.length ≠ p₂.length ∧ n₁.const ≤ n₂.const ∨ ∃ y ∈ n₂.var, n₁.const ≤ y.offset + 1) := by
  rw [Node.subsume] at h
  split at h <;> [skip; cases h rfl]
  refine ⟨‹_›, (subsumeBy_const_drop h).imp_left fun ⟨he, hc⟩ => ⟨fun e => ?_, hc⟩⟩
  simp [e] at he

/-- If `subsume` changed the variable list, the change was `subsumeVars` against the
variables of `n₂` at a strictly smaller key. -/
theorem Node.subsume_var_cases (p₁ n₁ p₂ n₂) :
    (Node.subsume p₁ n₁ p₂ n₂).var = n₁.var ∨
    (subset compare p₂ p₁ ∧ p₁.length ≠ p₂.length ∧
     (Node.subsume p₁ n₁ p₂ n₂).var = subsumeVars n₁.var n₂.var) := by
  rw [Node.subsume_var_eq]; split
  · exact .inl rfl
  · rename_i hc
    rw [Bool.or_eq_true, Bool.or_eq_true, not_or, not_or] at hc
    obtain ⟨hs, hlen, -⟩ := hc
    have hsub : subset compare p₂ p₁ := by revert hs; cases subset compare p₂ p₁ <;> simp
    exact .inr ⟨hsub, fun e => hlen (by simp [e]), rfl⟩

theorem NormLevel.minimize_var_subset {acc : NormLevel}
    (h : x ∈ (acc.minimize p₁ n₁).var) : x ∈ n₁.var := by
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList] at h
  generalize acc.toList = l at h
  induction l generalizing n₁ with | nil => exact h | cons a l ih
  exact Node.subsume_var_subset (ih h)

theorem NormLevel.minimize_eval_le {acc : NormLevel} :
    Node.eval ls ρ (acc.minimize p₁ n₁) ≤ n₁.eval ls ρ := by
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList]
  generalize acc.toList = l
  induction l generalizing n₁ with | nil => exact Nat.le_refl _ | cons a l ih
  exact Nat.le_trans (ih (n₁ := Node.subsume p₁ n₁ a.1 a.2)) Node.subsume_eval_le

/-- Minimizing a node against the rest of the map preserves its contribution to the total,
assuming every other entry's contribution is already bounded by `m`. -/
theorem NormLevel.minimize_eval_iff {acc : NormLevel} {p₁ : List Name} {n₁ : Node} {m : Nat}
    (wfa : ∀ p n, acc.get? p = some n → ∀ v ∈ n.var, v.var ∈ p)
    (h₁ : acc.get? p₁ = some n₁)
    (hacc : ∀ p n, p ≠ p₁ → acc.get? p = some n → evalPath ls ρ p (Node.eval ls ρ n) ≤ m)
    (nz : allNZ ls ρ p₁) :
    Node.eval ls ρ (acc.minimize p₁ n₁) ≤ m ↔ Node.eval ls ρ n₁ ≤ m := by
  have wf₁ := wfa _ _ h₁
  have evalq p₂ n₂ (hne : p₂ ≠ p₁) (h₂ : acc.get? p₂ = some n₂) (hsub : subset compare p₂ p₁) :
      Node.eval ls ρ n₂ ≤ m := by
    have := hacc _ _ hne h₂
    rw [evalPath_le] at this
    exact this (allNZ_mono (fun _ h => subset_mem hsub h) nz)
  -- a variable dominated at a different key of the map is bounded by `m`
  have domle (x : VarNode) : (∃ p₂ n₂ y, p₂ ≠ p₁ ∧ acc.get? p₂ = some n₂ ∧
      subset compare p₂ p₁ ∧ y ∈ n₂.var ∧ y.var = x.var ∧ x.offset ≤ y.offset) →
      VarNode.eval ls ρ x ≤ m := fun ⟨p₂, n₂, y, hne, h₂, hsub, hy, e, le⟩ => by
    refine Nat.le_trans ?_ (Nat.le_trans (Node.var_le_eval hy) (evalq _ _ hne h₂ hsub))
    simp only [VarNode.eval, ← e]; omega
  refine ⟨fun hf => ?_, fun h => Nat.le_trans minimize_eval_le h⟩
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList] at hf
  have hmem pn (h : pn ∈ acc.toList) : acc.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  generalize acc.toList = l at hf hmem
  -- fold invariant: vars of the current node come from `n₁`; the constant is intact or
  -- justifiably dropped; every original variable is dominated by a current one or elsewhere
  suffices ∀ n1, (∀ x ∈ n1.var, x ∈ n₁.var) →
      (n1.const = n₁.const ∨ (n1.const = 0 ∧
        ((∃ y ∈ n₁.var, n₁.const ≤ y.offset + 1) ∨
         ∃ p₂ n₂, p₂ ≠ p₁ ∧ acc.get? p₂ = some n₂ ∧ subset compare p₂ p₁ ∧
           n₁.const ≤ Node.eval ls ρ n₂))) →
      (∀ x ∈ n₁.var, (∃ y ∈ n1.var, y.var = x.var ∧ x.offset ≤ y.offset) ∨
        ∃ p₂ n₂ y, p₂ ≠ p₁ ∧ acc.get? p₂ = some n₂ ∧ subset compare p₂ p₁ ∧
          y ∈ n₂.var ∧ y.var = x.var ∧ x.offset ≤ y.offset) →
      Node.eval ls ρ (List.foldl (fun n1 pn => Node.subsume p₁ n1 pn.1 pn.2) n1 l) ≤ m →
      Node.eval ls ρ n₁ ≤ m from
    this n₁ (fun _ => id) (.inl rfl) (fun x h => .inl ⟨x, h, rfl, Nat.le_refl _⟩) hf
  clear hf
  induction l with intro n1 hL hK hJ hf
  | nil =>
    refine Node.eval_le.2 ⟨?_, fun x hx => ?_⟩
    · obtain hK | ⟨-, hK | ⟨p₂, n₂, hne, h₂, hsub, hc⟩⟩ := hK
      · exact Nat.le_trans (hK ▸ Node.const_le_eval) hf
      · obtain ⟨y, hy, hc⟩ := hK
        obtain ⟨y', hy', e, le⟩ | hd := hJ _ hy
        · refine Nat.le_trans ?_ (Nat.le_trans (Node.var_le_eval hy') hf)
          have : 0 < evalParam ls ρ y'.var := by
            simp [allNZ] at nz; exact nz _ (wf₁ _ (hL _ hy'))
          simp only [VarNode.eval]; omega
        · refine Nat.le_trans ?_ (domle _ hd)
          obtain ⟨p₂, n₂, y', hne, h₂, hsub, hy', e, le⟩ := hd
          have : 0 < evalParam ls ρ y'.var := by
            simp [allNZ] at nz; exact nz _ (subset_mem hsub (wfa _ _ h₂ _ hy'))
          simp only [VarNode.eval, ← e]; omega
      · exact Nat.le_trans hc (evalq _ _ hne h₂ hsub)
    · obtain ⟨y, hy, e, le⟩ | hd := hJ _ hx
      · refine Nat.le_trans ?_ (Nat.le_trans (Node.var_le_eval hy) hf)
        simp only [VarNode.eval, ← e]; omega
      · exact domle _ hd
  | cons pn l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hmem
    obtain ⟨h₂, hmem'⟩ := hmem
    refine ih hmem' _ (fun x h => hL _ (Node.subsume_var_subset h)) ?_ (fun x hx => ?_) hf
    · by_cases hc : (Node.subsume p₁ n1 pn.1 pn.2).const = n1.const
      · rw [hc]; exact hK
      obtain ⟨hsub, hd⟩ := Node.subsume_const_drop hc
      obtain heq | hzero := Node.subsume_const_cases p₁ n1 pn.1 pn.2
      · cases hc heq
      have hc1 : n1.const = n₁.const := by
        rcases hK with h | ⟨h, -⟩
        · exact h
        · cases hc (hzero.trans h.symm)
      refine .inr ⟨hzero, ?_⟩
      by_cases hpe : pn.1 = p₁
      · subst hpe
        have : pn.2 = n₁ := by cases h₁.symm.trans h₂; rfl
        subst this
        obtain ⟨hne', -⟩ | ⟨y, hy, hle⟩ := hd
        · exact absurd rfl hne'
        · exact .inl ⟨y, hy, hc1 ▸ hle⟩
      · refine .inr ⟨pn.1, pn.2, hpe, h₂, hsub, ?_⟩
        obtain ⟨-, hle⟩ | ⟨y, hy, hle⟩ := hd
        · exact hc1 ▸ Nat.le_trans hle Node.const_le_eval
        · refine hc1 ▸ Nat.le_trans hle ?_
          have : 0 < evalParam ls ρ y.var := by
            simp [allNZ] at nz
            exact nz _ (subset_mem hsub (wfa _ _ h₂ _ hy))
          refine Nat.le_trans ?_ (Node.var_le_eval hy)
          simp only [VarNode.eval]; omega
    · obtain ⟨y, hy, e, le⟩ | hd := hJ _ hx <;> [skip; exact .inr hd]
      obtain hv | ⟨hsub, hlen, hv⟩ := Node.subsume_var_cases p₁ n1 pn.1 pn.2
      · exact .inl ⟨y, hv ▸ hy, e, le⟩
      by_cases hy' : y ∈ (Node.subsume p₁ n1 pn.1 pn.2).var
      · exact .inl ⟨y, hy', e, le⟩
      obtain ⟨z, hz, ez, lez⟩ := subsumeVars_dominated hy (hv ▸ hy')
      have hpe : pn.1 ≠ p₁ := fun h => hlen (h ▸ rfl)
      exact .inr ⟨pn.1, pn.2, z, hpe, h₂, hsub, hz, ez.trans e, Nat.le_trans le lez⟩

/-- One step of `subsumption`: the key being minimized is updated, or erased if it drained,
and no other key changes. -/
theorem NormLevel.subsumption_step_get? (acc : NormLevel) (n₁ : Node) (p₁ p : List Name) :
    (if (acc.minimize p₁ n₁).isEmpty then acc.erase p₁
     else acc.insert p₁ (acc.minimize p₁ n₁)).get? p =
    if p₁ = p then (if (acc.minimize p₁ n₁).isEmpty then none else some (acc.minimize p₁ n₁))
    else acc.get? p := by
  split <;>
    simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase,
      Std.TreeMap.getElem?_insert] <;>
    split <;> split <;> simp_all

/-- `subsumption` only shrinks the variable lists, at unchanged keys, so it preserves the
half of `WF` saying that every variable recorded at a key is an element of it. -/
theorem NormLevel.subsumption_vars {s : NormLevel} (wf : s.WF) :
    ∀ p n, s.subsumption.get? p = some n → (∀ v ∈ n.var, v.var ∈ p) ∧ Sorted p := by
  rw [subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  have hmem pn (h : pn ∈ s.toList) : s.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  generalize s.toList = l at hmem
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (∀ pn ∈ l, s.get? pn.1 = some pn.2) →
      (∀ p n, acc.get? p = some n → (∀ v ∈ n.var, v.var ∈ p) ∧ Sorted p) →
      ∀ p n, (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).get? p = some n →
        (∀ v ∈ n.var, v.var ∈ p) ∧ Sorted p from this _ _ hmem fun p n h => (wf p n h).2
  clear hmem; intro l
  induction l with | nil => exact fun _ _ => id | cons pn l ih
  intro acc hl hacc
  refine ih _ (fun _ h => hl _ (.tail _ h)) fun p n h => ?_
  rw [subsumption_step_get?] at h
  split at h
  · split at h <;> [cases h; skip]
    cases h; rename_i hp _; subst hp
    have := (wf _ _ (hl _ (.head _))).2
    exact ⟨fun v hv => this.1 _ (minimize_var_subset hv), this.2⟩
  · exact hacc _ _ h

/-- A variable that minimization drops is dropped in favour of one with the same name at a
strictly smaller key. -/
theorem NormLevel.minimize_var_dominated {acc : NormLevel} {p₁ n₁ x}
    (hx : x ∈ n₁.var) (h : x ∉ (acc.minimize p₁ n₁).var) :
    ∃ p₂ n₂ y, acc.get? p₂ = some n₂ ∧ y ∈ n₂.var ∧ y.var = x.var ∧
      p₂ ≠ p₁ ∧ ∀ z ∈ p₂, z ∈ p₁ := by
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList] at h
  have hmem pn (h : pn ∈ acc.toList) : acc.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  generalize acc.toList = l at h hmem
  suffices ∀ (l : List (List Name × Node)) (n : Node),
      (∀ pn ∈ l, acc.get? pn.1 = some pn.2) → x ∈ n.var →
      x ∉ (List.foldl (fun n pn => Node.subsume p₁ n pn.1 pn.2) n l).var →
      ∃ p₂ n₂ y, acc.get? p₂ = some n₂ ∧ y ∈ n₂.var ∧ y.var = x.var ∧
        p₂ ≠ p₁ ∧ ∀ z ∈ p₂, z ∈ p₁ from this _ _ hmem hx h
  clear hx h hmem; intro l
  induction l with
  | nil => exact fun n _ hx h => absurd hx h
  | cons pn l ih =>
    intro n hl hx h
    by_cases hx' : x ∈ (Node.subsume p₁ n pn.1 pn.2).var
    · exact ih _ (fun _ h => hl _ (.tail _ h)) hx' h
    · obtain heq | ⟨hsub, hlen, heq⟩ := Node.subsume_var_cases p₁ n pn.1 pn.2
      · rw [heq] at hx'; exact absurd hx hx'
      · rw [heq] at hx'
        obtain ⟨y, hy, e, -⟩ := subsumeVars_dominated hx hx'
        exact ⟨pn.1, pn.2, y, hl _ (.head _), hy, e,
          fun he => hlen (by rw [he]), fun _ hz => subset_mem hsub hz⟩

/-- `s'` covers `s`: every variable recorded in `s` is still recorded in `s'`, at a subset of
its key. This is all of a map that `Dom`, hence `Feas`, looks at. -/
def NormLevel.Covers (s' s : NormLevel) : Prop :=
  ∀ p n x, s.get? p = some n → x ∈ n.var →
    ∃ q m y, s'.get? q = some m ∧ y ∈ m.var ∧ y.var = x.var ∧ ∀ z ∈ q, z ∈ p

/-- `subsumption` only removes variables from a node, and never the last witness for a name:
a removed one is still recorded at a strictly smaller key, possibly after further removals
there. So the subsumed map covers the original, and its entries are entries of it. -/
theorem NormLevel.subsumption_covers {s : NormLevel} :
    (∀ p n, s.subsumption.get? p = some n →
      ∃ n₀, s.get? p = some n₀ ∧ ∀ x ∈ n.var, x ∈ n₀.var) ∧ s.subsumption.Covers s := by
  rw [subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  have hmem pn (h : pn ∈ s.toList) : s.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  generalize s.toList = l at hmem
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (∀ pn ∈ l, s.get? pn.1 = some pn.2) →
      (∀ p n, acc.get? p = some n → ∃ n₀, s.get? p = some n₀ ∧ ∀ x ∈ n.var, x ∈ n₀.var) →
      acc.Covers s →
      (∀ p n, (List.foldl (fun acc pn =>
          let n := acc.minimize pn.1 pn.2
          if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).get? p = some n →
        ∃ n₀, s.get? p = some n₀ ∧ ∀ x ∈ n.var, x ∈ n₀.var) ∧
      (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).Covers s from
    this _ _ hmem (fun p n h => ⟨n, h, fun _ => id⟩)
      (fun p n x h hx => ⟨p, n, x, h, hx, rfl, fun _ => id⟩)
  clear hmem; intro l
  induction l with | nil => exact fun _ _ h1 h2 => ⟨h1, h2⟩ | cons pn l ih
  obtain ⟨p₁, n₁⟩ := pn
  intro acc hl hsub hcov
  have h₁ : s.get? p₁ = some n₁ := hl _ (.head _)
  refine ih _ (fun _ h => hl _ (.tail _ h)) (fun p n h => ?_) (fun p n x hp hx => ?_)
  · rw [subsumption_step_get?] at h
    split at h
    · split at h <;> [cases h; skip]
      cases h; rename_i hp _; subst hp
      exact ⟨n₁, h₁, fun x hx => minimize_var_subset hx⟩
    · exact hsub _ _ h
  · obtain ⟨q, m, y, hq, hy, e, hqp⟩ := hcov _ _ _ hp hx
    by_cases hqp₁ : q = p₁
    · subst hqp₁
      -- the write lands on the key covering `x`: either the variable survives it, or it is
      -- dominated at a smaller key, which this step leaves alone
      obtain ⟨n₀, h₀, hy₀⟩ := hsub _ _ hq
      cases h₀.symm.trans h₁
      by_cases hmin : y ∈ (acc.minimize q n₁).var
      · refine ⟨q, _, y, ?_, hmin, e, hqp⟩
        rw [subsumption_step_get?, if_pos rfl, if_neg]
        simp only [Node.isEmpty, Bool.and_eq_true, List.isEmpty_iff, not_and]
        rintro - he; simp [he] at hmin
      · obtain ⟨p₂, n₂, z, h₂, hz, e₂, hne, hp₂⟩ := minimize_var_dominated (hy₀ _ hy) hmin
        exact ⟨p₂, n₂, z, by rw [subsumption_step_get?, if_neg (Ne.symm hne)]; exact h₂,
          hz, e₂.trans e, fun w hw => hqp _ (hp₂ _ hw)⟩
    · exact ⟨q, m, y, by rw [subsumption_step_get?, if_neg (Ne.symm hqp₁)]; exact hq,
        hy, e, hqp⟩

theorem NormLevel.subsumption_eval {s : NormLevel} (wf : s.WF) :
    s.subsumption.eval ls ρ = s.eval ls ρ := by
  rw [subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  have hmem pn (h : pn ∈ s.toList) : s.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  have nd : (s.toList.map Prod.fst).Nodup := by simpa using Std.TreeMap.nodup_keys (t := s)
  generalize s.toList = l at hmem nd
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (l.map Prod.fst).Nodup →
      (∀ p n, (p, n) ∈ l → acc.get? p = some n) →
      (∀ p n, acc.get? p = some n → ∀ v ∈ n.var, v.var ∈ p) →
      eval ls ρ acc = eval ls ρ s →
      eval ls ρ (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l) = eval ls ρ s from
    this _ _ nd (fun _ _ => hmem _) (fun _ _ h => (wf _ _ h).2.1) rfl
  clear hmem nd; intro l
  induction l with | nil => exact fun acc _ _ _ eq => eq | cons pn l ih
  have ⟨p₁, n₁⟩ := pn; intro acc nd hl wfa eq
  simp only [List.map_cons, List.nodup_cons] at nd
  have h₁ := hl _ _ (.head _)
  -- a drained key is erased rather than kept, which is the same for `eval`
  have hins := subsumption_step_get? acc n₁ p₁
  have hmin_le m
      (H : ∀ a b, (if (acc.minimize p₁ n₁).isEmpty then acc.erase p₁
        else acc.insert p₁ (acc.minimize p₁ n₁)).get? a = some b →
        evalPath ls ρ a (Node.eval ls ρ b) ≤ m)
      (nz : allNZ ls ρ p₁) : Node.eval ls ρ (acc.minimize p₁ n₁) ≤ m := by
    by_cases he : (acc.minimize p₁ n₁).isEmpty
    · simp [Node.isEmpty, List.isEmpty_iff] at he; simp [Node.eval, he.1, he.2]
    · have hget : (if (acc.minimize p₁ n₁).isEmpty then acc.erase p₁
          else acc.insert p₁ (acc.minimize p₁ n₁)).get? p₁ = some (acc.minimize p₁ n₁) := by
        rw [hins p₁, if_pos rfl, if_neg he]
      have := H _ _ hget
      rw [evalPath_le] at this; exact this nz
  refine ih _ nd.2 (fun p n h => ?_) (fun p n h v hv => ?_) ((ext_le fun m => ?_).trans eq)
  · have hne : p₁ ≠ p := fun e => nd.1 (by rw [e]; exact List.mem_map_of_mem h)
    exact (hins p).trans (if_neg hne) ▸ hl _ _ (.tail _ h)
  · rw [hins p] at h; split at h
    · split at h <;> [cases h; skip]
      cases h; rename_i hp _; subst hp
      exact wfa _ _ h₁ _ (minimize_var_subset hv)
    · exact wfa _ _ h _ hv
  · simp only [eval_le]; constructor <;> intro H p n h
    · by_cases hp : p = p₁
      · subst hp; cases h₁.symm.trans h
        refine evalPath_le.2 fun nz => ?_
        refine (minimize_eval_iff wfa h₁ (fun q nq hne hq => ?_) nz).1 (hmin_le _ H nz)
        exact H _ _ ((hins q).trans (if_neg hne.symm) ▸ hq)
      · exact H p n ((hins p).trans (if_neg (Ne.symm hp)) ▸ h)
    · rw [hins p] at h; split at h <;> [skip; exact H _ _ h]
      split at h <;> [cases h; skip]
      cases h; rename_i hp _; subst hp
      refine evalPath_le.2 fun nz => ?_
      have := H _ _ h₁; rw [evalPath_le] at this
      exact Nat.le_trans minimize_eval_le (this nz)

theorem normalize_eval (hu : VLevel.ofLevel ls u = some u') :
    (normalize u).eval ls ρ = u'.eval ρ := by
  simp [normalize]
  refine have h1 := ?_; by
    rw [NormLevel.subsumption_eval (normalizeAux_wf (by simp) h1)]
    exact normalizeAux_eval hu (by simp) h1
  simp [NormLevel.WF]

theorem normalize_vars_sorted : ∀ p n, (normalize u).get? p = some n →
    (∀ v ∈ n.var, v.var ∈ p) ∧ Sorted p :=
  NormLevel.subsumption_vars (normalizeAux_wf (by simp) (by simp [NormLevel.WF]))

theorem normalize_vars : ∀ p n, (normalize u).get? p = some n → ∀ v ∈ n.var, v.var ∈ p :=
  fun _ _ h => (normalize_vars_sorted _ _ h).1

theorem normalize_sorted : ∀ p n, (normalize u).get? p = some n → Sorted p :=
  fun _ _ h => (normalize_vars_sorted _ _ h).2

/-- Soundness of `NormLevel.le`, Theorem 39 of the paper: it reports `true` only when every
sublevel of `l₁` is dominated. Each entry of `l₁` is compared against a fold over `l₂`,
where every entry discharges from the node what it can, and the fold stops (returning
`none`) once nothing is left to discharge; so the fold ends in `none` only if the node is
bounded by the total of `l₂`. -/
theorem NormLevel.le_eval {l₁ l₂ : NormLevel}
    (wf₂ : ∀ p n, l₂.get? p = some n → ∀ v ∈ n.var, v.var ∈ p)
    (h : l₁.le l₂) : l₁.eval ls ρ ≤ l₂.eval ls ρ := by
  refine NormLevel.eval_le.2 fun p₁ n₁ h₁ => evalPath_le.2 fun nz => ?_
  -- an entry of `l₂` at a key below `p₁` is bounded by the total, on a live condition set
  have hbd p₂ n₂ (h₂ : l₂.get? p₂ = some n₂) (hsub : subset compare p₂ p₁) :
      (∀ v ∈ n₂.var, 0 < evalParam ls ρ v.var) ∧ Node.eval ls ρ n₂ ≤ l₂.eval ls ρ := by
    have hnz : allNZ ls ρ p₂ := allNZ_mono (fun _ h => subset_mem hsub h) nz
    refine ⟨fun v hv => ?_, ?_⟩
    · simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnz
      exact hnz _ (wf₂ _ _ h₂ _ hv)
    · have := evalPath_le.1 (NormLevel.eval_le.1 (Nat.le_refl (l₂.eval ls ρ)) _ _ h₂)
      exact this hnz
  rw [NormLevel.le, Std.TreeMap.all_eq_all_toList, List.all_eq_true] at h
  have hf := h (p₁, n₁) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 (by simpa using h₁))
  simp only [Std.TreeMap.foldlM_eq_foldlM_toList, Option.isNone_iff_eq_none] at hf
  have hmem pn (h : pn ∈ l₂.toList) : l₂.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  clear h₁ h
  generalize l₂.toList = l at hf hmem
  induction l generalizing n₁ with
  | nil => simp at hf
  | cons pn l ih =>
    simp only [List.foldlM_cons] at hf
    simp only [List.mem_cons, forall_eq_or_imp] at hmem
    by_cases hs : subset compare pn.1 p₁
    · refine (Node.subsumeBy_eval_iff (same := false) (n₂ := pn.2)
        (hbd _ _ hmem.1 hs).1 (hbd _ _ hmem.1 hs).2).1 ?_
      by_cases he : (n₁.subsumeBy false pn.2).isEmpty
      · simp [Node.eval_empty he]
      · exact ih _ (by simpa [hs, he] using hf) hmem.2
    · exact ih _ (by simpa [hs] using hf) hmem.2

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

/-!
### Reconstruction

The value of a `Tree` is the value of the level it reifies to: a tree node contributes its
own sublevels, and every child contributes under the `imax` guard of the variable labelling
the edge into it. That edge guard is what makes the tree shape meaningful — a node at path
`[a₁, …, aₙ]` (innermost first) is guarded by all of `a₁, …, aₙ` — and it is also what makes
the tree carry sublevels of its own, since `imax x a` is at least `a` when `a ≠ 0`.
-/

mutual

def Tree.eval (ls : List Name) (ρ : List Nat) : Tree → Nat
  | ⟨const, var, child⟩ => max' (Node.eval ls ρ ⟨const, var⟩) (Tree.evalChild ls ρ child)

def Tree.evalChild (ls : List Name) (ρ : List Nat) : List (Name × Tree) → Nat
  | [] => 0
  | (a, t) :: l =>
    max' (Lean.Nat.imax (Tree.eval ls ρ t) (evalParam ls ρ a)) (Tree.evalChild ls ρ l)

end

/-- The value of the optional level accumulated by `reify`. -/
def evalOpt (ρ : Name → Nat) (μ : LMVarId → Nat) : Option Level → Nat
  | none => 0
  | some l => Level.eval ρ μ l

@[simp] theorem evalOpt_none : evalOpt ρ μ none = 0 := rfl
@[simp] theorem evalOpt_some : evalOpt ρ μ (some l) = Level.eval ρ μ l := rfl

theorem imax_eq_ite : Lean.Nat.imax a b = if b = 0 then 0 else max' a b := rfl

theorem imax_zero_left : Lean.Nat.imax 0 a = a := by rw [imax_eq_ite]; split <;> omega

theorem Node.eval_const {var : List VarNode} :
    Node.eval ls ρ ⟨c, var⟩ = max' c (Node.eval ls ρ ⟨0, var⟩) :=
  ext_le fun x => by simp [Node.eval_le, Nat.max_le]

theorem Node.eval_cons {var : List VarNode} :
    Node.eval ls ρ ⟨c, a :: var⟩ = max' (VarNode.eval ls ρ a) (Node.eval ls ρ ⟨c, var⟩) :=
  ext_le fun x => by simp [Node.eval_le, Nat.max_le, and_left_comm]

theorem eval_mkMax :
    Level.eval ρ μ (Tree.reify.mkMax l o) = max' (Level.eval ρ μ l) (evalOpt ρ μ o) := by
  cases o <;> simp [Tree.reify.mkMax, evalOpt, Level.eval]

theorem eval_addOffset : Level.eval ρ μ (l.addOffset k) = Level.eval ρ μ l + k := by
  simp only [Level.addOffset]
  induction k generalizing l with
  | zero => rfl
  | succ k ih => rw [Level.addOffsetAux, ih]; simp [Level.eval]; omega

theorem eval_ofNat : Level.eval ρ μ (Level.ofNat k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Level.ofNat, Level.eval, ih]

theorem eval_varFold (var : List VarNode) (o : Option Level) :
    evalOpt (evalParam ls ρ) μ (var.foldr (init := o) fun n r =>
      some (Tree.reify.mkMax (Level.addOffset (.param n.var) n.offset) r)) =
    max' (Node.eval ls ρ ⟨0, var⟩) (evalOpt (evalParam ls ρ) μ o) := by
  induction var with | nil => simp [Node.eval] | cons a var ih
  simp only [List.foldr_cons, evalOpt_some, eval_mkMax, eval_addOffset, Level.eval, ih,
    Node.eval_cons, VarNode.eval]; omega

mutual

theorem Tree.reify_eval (t : Tree) : t.reify.eval (evalParam ls ρ) μ = t.eval ls ρ := by
  obtain ⟨const, var, child⟩ := t
  rw [eval]
  simp only [reify]
  have h1 := eval_varFold (ls := ls) (ρ := ρ) (μ := μ) var (child.foldr reify.mkChild none)
  rw [reifyChild_eval] at h1
  rw [Node.eval_const (c := const)]
  split <;> [rename_i heq; rename_i l heq]
  · rw [heq, evalOpt_none] at h1
    rw [eval_ofNat]; omega
  · rw [heq, evalOpt_some] at h1
    split
    · subst const; omega
    · simp only [Level.eval, eval_ofNat, h1]; exact (Nat.max_assoc ..).symm

theorem Tree.reifyChild_eval (child : List (Name × Tree)) :
    evalOpt (evalParam ls ρ) μ (child.foldr reify.mkChild none) = evalChild ls ρ child := by
  match child with
  | [] => rfl
  | (n, t) :: child =>
    rw [List.foldr_cons, evalChild, reify.mkChild]
    have ht := reify_eval (ls := ls) (ρ := ρ) (μ := μ) t
    have ih := reifyChild_eval (ls := ls) (ρ := ρ) (μ := μ) child
    split <;> rename_i h
    · rw [h] at ht
      simp only [evalOpt_some, eval_mkMax, Level.eval, ih, ← ht, imax_zero_left]
    · simp only [evalOpt_some, eval_mkMax, Level.eval, ih, ht]

end

/-- `Tree.At t p t'` says `t'` is the subtree of `t` at path `p`, listed innermost first,
the way `Tree.modify` takes it. -/
inductive Tree.At : Tree → List Name → Tree → Prop
  | nil : At t [] t
  | cons (h : At t p t') (hm : (a, t'') ∈ t'.child) : At t (a :: p) t''

theorem Tree.eval_eq (t : Tree) :
    eval ls ρ t = max' (Node.eval ls ρ ⟨t.const, t.var⟩) (evalChild ls ρ t.child) := by
  cases t; rw [eval]

theorem Tree.At.append (h : At t' q t'') (hm : (a, t') ∈ t.child) :
    At t (q ++ [a]) t'' := by
  induction h with
  | nil => exact .cons .nil hm
  | cons _ hm' ih => exact .cons ih hm'

/-- A path passes through all of its tails. -/
theorem Tree.At.suffix {t : Tree} : ∀ {path t' q}, At t path t' → q <:+ path → ∃ t'', At t q t'' := by
  intro path
  induction path with
  | nil => intro t' q _ hq; cases List.suffix_nil.1 hq; exact ⟨t, .nil⟩
  | cons a p ih =>
    intro t' q h hq
    obtain rfl | hq := List.suffix_cons_iff.1 hq
    · exact ⟨t', h⟩
    · cases h; rename_i t₁ h _; exact ih h hq

theorem Tree.At.nil_inv (h : At t [] t') : t' = t := by cases h; rfl

/-- Inverting `At.append`: a nonempty path is a child of the root followed by the rest. -/
theorem Tree.At.append_inv : ∀ {q t t''}, At t (q ++ [a]) t'' →
    ∃ t₁, (a, t₁) ∈ t.child ∧ At t₁ q t'' := by
  intro q
  induction q with
  | nil =>
    intro t t'' h
    cases h; rename_i t₁ h hm
    cases h.nil_inv
    exact ⟨t'', hm, .nil⟩
  | cons b q ih =>
    intro t t'' h
    simp only [List.cons_append] at h
    cases h; rename_i t₁ h hm
    obtain ⟨t₂, hm₂, h₂⟩ := ih h
    exact ⟨t₂, hm₂, .cons h₂ hm⟩

/-- Paths only look at the children, so replacing the root's own data leaves them all in
place; only the empty path sees the difference. -/
theorem Tree.At.of_child_eq {t u : Tree} (hc : u.child = t.child) :
    ∀ {p t'}, At t p t' → At u p t' ∨ (p = [] ∧ t' = t) := by
  intro p
  induction p with
  | nil => intro t' h; exact .inr ⟨rfl, h.nil_inv⟩
  | cons a q ih =>
    intro t'' h
    cases h; rename_i t₁ h hm
    obtain h' | ⟨rfl, rfl⟩ := ih h
    · exact .inl (.cons h' hm)
    · exact .inl (.cons .nil (by rw [hc]; exact hm))

theorem Tree.mem_le {l : List (Name × Tree)} (hm : (a, t) ∈ l) :
    Lean.Nat.imax (eval ls ρ t) (evalParam ls ρ a) ≤ evalChild ls ρ l := by
  induction l with
  | nil => cases hm
  | cons b l ih =>
    obtain ⟨b, t'⟩ := b
    rw [evalChild]
    obtain h | hm := List.mem_cons.1 hm
    · cases h; exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hm) (Nat.le_max_right ..)

theorem evalPath_cons_imax :
    evalPath ls ρ (a :: p) c ≤ evalPath ls ρ p (Lean.Nat.imax c (evalParam ls ρ a)) := by
  rw [evalPath_cons]
  exact evalPath_mono <| by
    by_cases h : evalParam ls ρ a = 0 <;>
      simp [imax_eq_ite, h, Nat.pos_of_ne_zero, Nat.le_max_left]

theorem evalPath_cons_edge :
    evalPath ls ρ (a :: p) (evalParam ls ρ a) ≤
      evalPath ls ρ p (Lean.Nat.imax c (evalParam ls ρ a)) := by
  rw [evalPath_cons]
  exact evalPath_mono <| by
    by_cases h : evalParam ls ρ a = 0 <;>
      simp [imax_eq_ite, h, Nat.pos_of_ne_zero, Nat.le_max_right]

theorem evalPath_append_single (ha : evalParam ls ρ a ≠ 0) :
    evalPath ls ρ (p ++ [a]) c = evalPath ls ρ p c := by
  simp [evalPath, allNZ, List.all_append, Nat.pos_of_ne_zero ha]

theorem Tree.At.le (h : At t p t') :
    evalPath ls ρ p (eval ls ρ t') ≤ eval ls ρ t := by
  induction h with
  | nil => simp [evalPath, allNZ]
  | cons _ hm ih =>
    refine Nat.le_trans evalPath_cons_imax (Nat.le_trans (evalPath_mono ?_) ih)
    exact Nat.le_trans (mem_le hm) (eval_eq _ ▸ Nat.le_max_right ..)

theorem Tree.At.edge_le (h : At t (a :: p) t') :
    evalPath ls ρ (a :: p) (evalParam ls ρ a) ≤ eval ls ρ t := by
  cases h with | @cons _ t'' _ _ h' hm => ?_
  refine Nat.le_trans (evalPath_cons_edge (c := eval ls ρ t'))
    (Nat.le_trans (evalPath_mono ?_) h'.le)
  exact Nat.le_trans (mem_le hm) (eval_eq t'' ▸ Nat.le_max_right ..)

mutual

/-- A tree is bounded by `m` as soon as all the sublevels it reifies to are: the ones
recorded at its nodes, and the `V(p, a, 0)` contributed by the edge into each node. -/
theorem Tree.eval_le_of (t : Tree)
    (h1 : ∀ p t', At t p t' → evalPath ls ρ p (Node.eval ls ρ ⟨t'.const, t'.var⟩) ≤ m)
    (h2 : ∀ a p t', At t (a :: p) t' → evalPath ls ρ (a :: p) (evalParam ls ρ a) ≤ m) :
    eval ls ρ t ≤ m := by
  obtain ⟨const, var, child⟩ := t
  rw [eval]
  refine Nat.max_le.2 ⟨h1 [] _ .nil, evalChild_le_of child ?_ ?_ ?_⟩
  · exact fun a t' hm p t'' hat => h1 _ _ (hat.append hm)
  · exact fun a t' hm b p t'' hat => h2 _ _ _ (hat.append hm)
  · exact fun a t' hm => h2 a [] t' (.cons .nil hm)

theorem Tree.evalChild_le_of : ∀ (l : List (Name × Tree)),
    (∀ a t', (a, t') ∈ l → ∀ p t'', At t' p t'' →
      evalPath ls ρ (p ++ [a]) (Node.eval ls ρ ⟨t''.const, t''.var⟩) ≤ m) →
    (∀ a t', (a, t') ∈ l → ∀ b p t'', At t' (b :: p) t'' →
      evalPath ls ρ ((b :: p) ++ [a]) (evalParam ls ρ b) ≤ m) →
    (∀ a t', (a, t') ∈ l → evalPath ls ρ [a] (evalParam ls ρ a) ≤ m) →
    evalChild ls ρ l ≤ m
  | [], _, _, _ => by rw [evalChild]; exact Nat.zero_le _
  | (a, t) :: l, h1, h2, h3 => by
    rw [evalChild]
    refine Nat.max_le.2 ⟨?_, evalChild_le_of l
      (fun a t' hm => h1 a t' (.tail _ hm)) (fun a t' hm => h2 a t' (.tail _ hm))
      (fun a t' hm => h3 a t' (.tail _ hm))⟩
    by_cases ha : evalParam ls ρ a = 0
    · simp [imax_eq_ite, ha]
    · have hle : evalParam ls ρ a ≤ m := by
        have := h3 a t (.head _)
        simpa [evalPath, allNZ, Nat.pos_of_ne_zero ha] using this
      have ht : eval ls ρ t ≤ m :=
        eval_le_of t
          (fun p t'' hat => evalPath_append_single ha ▸ h1 a t (.head _) p t'' hat)
          (fun b p t'' hat => evalPath_append_single ha ▸ h2 a t (.head _) b p t'' hat)
      rw [imax_eq_ite]; split <;> omega

end

/-- A tree is bounded by `m` exactly when all the sublevels it reifies to are: the ones
recorded at its nodes, and the one each edge contributes. -/
theorem Tree.eval_le_iff {t : Tree} {m : Nat} :
    eval ls ρ t ≤ m ↔
    (∀ p t', At t p t' → evalPath ls ρ p (Node.eval ls ρ ⟨t'.const, t'.var⟩) ≤ m) ∧
    (∀ a p t', At t (a :: p) t' → evalPath ls ρ (a :: p) (evalParam ls ρ a) ≤ m) := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => eval_le_of t h1 h2⟩
  refine ⟨fun _ t' hp => ?_, fun _ _ _ hp => Nat.le_trans hp.edge_le h⟩
  exact Nat.le_trans (Nat.le_trans (evalPath_mono (eval_eq t' ▸ Nat.le_max_left ..)) hp.le) h

/-!
### Admissible chains

Reifying the sublevels at a key `p` means nesting them under an `imax` chain whose variables
are the elements of `p`; the chain contributes the sublevel `V(q, a, 0)` for every one of its
edges, where `q` is the set of conditions from the outside up to and including that edge. The
level is therefore equivalent to the normal form only if every such edge is *dominated*
(`Dom`), and a key is expressible only if its elements can be ordered so that all of them are
(`Feas`). `lexChain` searches for such an order greedily; `feasible` is its lookahead.
-/

/-- The edge adding `a` to the conditions `acc` contributes `V(acc ∪ {a}, a, 0)`, which the
normal form dominates when it has some `V(T, a+k)` with `T ⊆ acc ∪ {a}`. -/
def NormLevel.Dom (s : NormLevel) (a : Name) (acc : List Name) : Prop :=
  ∃ p n, s.get? p = some n ∧ (∃ x ∈ n.var, x.var = a) ∧ ∀ y ∈ p, y = a ∨ y ∈ acc

theorem NormLevel.Dom.mono {s : NormLevel}
    (h : s.Dom a acc) (hs : ∀ x ∈ acc, x ∈ acc') : s.Dom a acc' :=
  let ⟨p, n, h1, h2, h3⟩ := h
  ⟨p, n, h1, h2, fun y hy => (h3 y hy).imp id (hs _)⟩

/-- A dominated edge contributes nothing beyond the normal form. -/
theorem NormLevel.Dom.le {s : NormLevel} (h : s.Dom a acc) :
    evalPath ls ρ (a :: acc) (evalParam ls ρ a) ≤ s.eval ls ρ := by
  refine evalPath_le.2 fun nz => ?_
  rw [allNZ_cons] at nz
  obtain ⟨p, n, h1, ⟨x, hx, hxa⟩, h3⟩ := h
  have hnz : allNZ ls ρ p := by
    simp only [allNZ, List.all_eq_true, decide_eq_true_eq]
    refine fun y hy => (h3 y hy).elim (fun e => e ▸ nz.1) fun hy => ?_
    simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at nz
    exact nz.2 _ hy
  refine Nat.le_trans ?_ (Nat.le_trans (Node.var_le_eval hx)
    (evalPath_le.1 (NormLevel.eval_le.1 (Nat.le_refl _) _ _ h1) hnz))
  simp only [VarNode.eval, ← hxa]; omega

theorem NormLevel.addable_sound {s : NormLevel} (h : s.addable a acc) : s.Dom a acc := by
  simp only [addable, Std.TreeMap.any_eq_any_toList, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨p, n⟩, hm, ⟨x, hx, hxa⟩, hsub⟩ := h
  refine ⟨p, n, Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hm,
    ⟨x, hx, hxa⟩, fun y hy => ?_⟩
  by_cases hya : y = a
  · exact .inl hya
  · exact .inr (subset_mem hsub ((List.mem_erase_of_ne hya).2 hy))

theorem NormLevel.addable_complete {s : NormLevel} (hs : ∀ p n, s.get? p = some n → Sorted p)
    (hacc : Sorted acc) (h : s.Dom a acc) : s.addable a acc := by
  obtain ⟨p, n, h1, ⟨x, hx, hxa⟩, h3⟩ := h
  simp only [addable, Std.TreeMap.any_eq_any_toList, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq]
  refine ⟨(p, n), Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 (by simpa using h1),
    ⟨x, hx, hxa⟩, subset_of_sorted (hs _ _ h1).erase hacc fun y hy => ?_⟩
  refine (h3 y (List.mem_of_mem_erase hy)).resolve_left fun e => ?_
  exact absurd (e ▸ hy) ((hs _ _ h1).nodup.not_mem_erase)

/-- The conditions `rem` can be added to `acc` one at a time, each addition dominated. -/
inductive NormLevel.Feas (s : NormLevel) : List Name → List Name → Prop
  | nil {acc} : Feas s acc []
  | cons {acc a rem} : a ∈ rem → s.Dom a acc → Feas s (a :: acc) (rem.erase a) → Feas s acc rem

theorem NormLevel.Feas.mono {s : NormLevel} (hs : ∀ x ∈ acc, x ∈ acc')
    (h : Feas s acc rem) : Feas s acc' rem := by
  induction h generalizing acc' with | nil => exact .nil | cons hm hd _ ih
  refine .cons hm (hd.mono hs) <| ih fun x hx => ?_
  obtain rfl | hx := List.mem_cons.1 hx
  · exact .head _
  · exact .tail _ (hs _ hx)

/-- Greedy exchange: a dominated element can always be taken first. -/
theorem NormLevel.Feas.exchange {s : NormLevel} (h : Feas s acc rem) :
    ∀ {a}, a ∈ rem → s.Dom a acc → Feas s (a :: acc) (rem.erase a) := by
  induction h with | nil => nofun | @cons acc b rem hmb hdb H ih
  intro a hm hd
  by_cases hab : a = b <;> [(subst hab; exact H); skip]
  refine .cons ((List.mem_erase_of_ne (Ne.symm hab)).2 hmb) (hdb.mono fun x hx => .tail _ hx) ?_
  rw [List.erase_comm]
  refine ih ((List.mem_erase_of_ne hab).2 hm) (hd.mono fun x hx => .tail _ hx)
    |>.mono fun x hx => ?_
  obtain rfl | hx := List.mem_cons.1 hx
  · exact .tail _ (.head _)
  · obtain rfl | hx := List.mem_cons.1 hx
    · exact .head _
    · exact .tail _ (.tail _ hx)

/-- Peel off the element added last: it is dominated by all the others. -/
theorem NormLevel.Feas.peel {s : NormLevel} (h : Feas s acc rem) (nd : rem.Nodup) (hne : rem ≠ []) :
    ∃ a ∈ rem, s.Dom a (acc ++ rem.erase a) ∧ Feas s acc (rem.erase a) := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons acc b rem hmb hdb H ih =>
    by_cases he : rem.erase b = []
    · exact ⟨b, hmb, hdb.mono fun x hx => List.mem_append_left _ hx, he ▸ .nil⟩
    obtain ⟨a, hma, hda, hfa⟩ := ih (nd.erase _) he
    have hab : a ≠ b := by rintro rfl; exact absurd hma nd.not_mem_erase
    have hmb' : b ∈ rem.erase a := (List.mem_erase_of_ne (Ne.symm hab)).2 hmb
    refine ⟨a, List.mem_of_mem_erase hma, hda.mono fun x hx => ?_, ?_⟩
    · simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
      obtain rfl | hx | hx := hx
      · exact .inr hmb'
      · exact .inl hx
      · rw [List.erase_comm] at hx; exact .inr (List.mem_of_mem_erase hx)
    · exact .cons hmb' hdb <| by rw [List.erase_comm]; exact hfa

theorem NormLevel.feasible_go_sound {s : NormLevel} :
    ∀ {fuel acc rem}, NormLevel.feasible.go s fuel acc rem → s.Feas acc rem
  | 0, _, rem, h => by simp [feasible.go, List.isEmpty_iff] at h; exact h ▸ .nil
  | fuel+1, acc, rem, h => by
    rw [feasible.go] at h
    split at h <;> [(let [] := rem; exact .nil); rename_i a ha]
    have hm := List.mem_of_find?_eq_some ha
    have hd := addable_sound (List.find?_eq_some_iff_getElem.1 ha).1
    refine .cons hm hd ((feasible_go_sound h).mono fun x hx => ?_)
    exact List.mem_cons.2 ((Extend?.orderedInsert (cmp := Name.cmp) (v := a) (p := acc)).mem.1 hx)

theorem NormLevel.feasible_sound {s : NormLevel} (h : s.feasible acc rem) : s.Feas acc rem :=
  feasible_go_sound h

theorem NormLevel.feasible_go_complete {s : NormLevel} (hs : ∀ p n, s.get? p = some n → Sorted p) :
    ∀ {fuel acc rem}, rem.length ≤ fuel → Sorted acc → s.Feas acc rem → feasible.go s fuel acc rem
  | 0, _, rem, hf, _, _ => by
    rw [feasible.go]; cases rem with | nil => rfl | cons => cases hf
  | fuel+1, acc, rem, hf, hacc, h => by
    rw [feasible.go]
    split <;> [rename_i ha; rename_i a ha]
    · -- the first element of the chain is addable, so `find?` cannot fail
      cases h with | nil => rfl | @cons b _ _ hm hd
      exact absurd (addable_complete hs hacc hd) (by simpa using List.find?_eq_none.1 ha _ hm)
    · have hm := List.mem_of_find?_eq_some ha
      have hd := addable_sound (List.find?_eq_some_iff_getElem.1 ha).1
      have hext := Extend?.orderedInsert (cmp := Name.cmp) (v := a) (p := acc)
      refine feasible_go_complete hs ?_ ?_ ((h.exchange hm hd).mono fun x hx => hext.mem.2 ?_)
      · rw [List.length_erase_of_mem hm]; omega
      · match he : Normalize.orderedInsert Name.cmp a acc with
        | none => exact hacc
        | some acc' => exact hacc.orderedInsert he
      · exact List.mem_cons.1 hx

theorem NormLevel.feasible_complete {s : NormLevel} (hs : ∀ p n, s.get? p = some n → Sorted p)
    (hacc : Sorted acc) (h : s.Feas acc rem) : s.feasible acc rem :=
  feasible_go_complete hs (Nat.le_refl _) hacc h

theorem NormLevel.Feas.perm {s : NormLevel} (h : Feas s acc rem) (hp : rem.Perm rem') :
    Feas s acc rem' := by
  induction h generalizing rem' with
  | nil => cases hp.nil_eq; exact .nil
  | cons hm hd _ ih => exact .cons (hp.mem_iff.1 hm) hd (ih (hp.erase _))

/-- Extend a chain on the inside: the new element's conditions are all the others. -/
theorem NormLevel.Feas.cons_last {s : NormLevel} (h : Feas s acc rem) (hnm : a ∉ rem)
    (hd : s.Dom a (acc ++ rem)) : Feas s acc (a :: rem) := by
  induction h with
  | nil => exact .cons (.head _) (by simpa using hd) (by simpa using Feas.nil)
  | @cons acc b rem hmb hdb _ ih =>
    have hab : b ≠ a := fun e => hnm (e ▸ hmb)
    refine .cons (.tail _ hmb) hdb ?_
    rw [List.erase_cons_tail (by simpa using Ne.symm hab)]
    refine ih (fun h => hnm (List.mem_of_mem_erase h)) (hd.mono fun x hx => ?_)
    -- everything outside `a` is still there: `b` moved into the accumulator
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
    obtain hx | hx := hx
    · exact .inr (.inl hx)
    · by_cases hxb : x = b
      · exact .inl hxb
      · exact .inr (.inr ((List.mem_erase_of_ne hxb).2 hx))

/-- Every key of a well-formed normal form admits a chain: its `WF` parent is a key with one
condition fewer, and the variable relating them dominates the edge between them. -/
theorem NormLevel.WF.feas {s : NormLevel} (wf : s.WF) : ∀ {p}, s.contains p → s.Feas [] p := by
  intro p
  generalize eq : p.length = len
  induction len generalizing p with
  | zero => cases List.eq_nil_of_length_eq_zero eq; exact fun _ => .nil
  | succ len ih =>
    intro hp
    have hne : p ≠ [] := by rintro rfl; cases eq
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (Std.TreeMap.isSome_getElem?_eq_contains.trans hp)
    obtain ⟨v, p', h1, h2, x, hx, hxv⟩ := (wf _ _ hn).1 hne
    have hperm : p.Perm (v :: p') := by cases h1; exact List.perm_middle
    have hnm : v ∉ p' := by
      have := (wf.sortedOf (.inr hp)).nodup
      rw [hperm.nodup_iff] at this
      exact (List.nodup_cons.1 this).1
    refine Feas.perm ?_ hperm.symm
    refine Feas.cons_last (h2.elim (fun e => by subst e; exact .nil) (fun h => ih (by
      have := h1.length; omega) h)) hnm ⟨p, n, hn, ⟨x, hx, hxv⟩, fun y hy => ?_⟩
    simpa using (h1.mem.1 hy).imp id id

/-- Domination only reads off variable names and their keys, so a map that covers another
dominates whatever it does. -/
theorem NormLevel.Dom.mono_map {s s' : NormLevel} (h : s'.Covers s) (hd : s.Dom a acc) :
    s'.Dom a acc := by
  obtain ⟨p, n, hp, ⟨x, hx, hxa⟩, hcond⟩ := hd
  obtain ⟨q, m, y, hq, hy, e, hsub⟩ := h _ _ _ hp hx
  exact ⟨q, m, hq, ⟨y, hy, e.trans hxa⟩, fun z hz => hcond _ (hsub _ hz)⟩

theorem NormLevel.Feas.mono_map {s s' : NormLevel} (h : s'.Covers s) :
    ∀ {acc rem}, s.Feas acc rem → s'.Feas acc rem
  | _, _, .nil => .nil
  | _, _, .cons hm hd H => .cons hm (hd.mono_map h) (Feas.mono_map h H)

/-- Every key of the normal form admits a chain. `WF.feas` gives this for the map `normalizeAux`
builds; subsumption keeps it because it covers that map, dropping a variable only in favour of
one with the same name at a smaller key. -/
theorem normalize_feas : ∀ p, (normalize u).contains p → (normalize u).Feas [] p := by
  intro p hp
  have wf : (normalizeAux u [] 0 {}).WF := normalizeAux_wf (by simp) (by simp [NormLevel.WF])
  refine NormLevel.Feas.mono_map NormLevel.subsumption_covers.2 (wf.feas ?_)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (Std.TreeMap.isSome_getElem?_eq_contains.trans hp)
  obtain ⟨n₀, h₀, -⟩ := NormLevel.subsumption_covers.1 p n
    (by rw [Std.TreeMap.get?_eq_getElem?]; exact hn)
  exact Std.TreeMap.isSome_getElem?_eq_contains.symm.trans
    (by simp [Std.TreeMap.get?_eq_getElem?] at h₀; simp [h₀])

/-- An admissible chain, innermost first: each element is dominated relative to the
conditions outside it. -/
def NormLevel.Adm (s : NormLevel) : List Name → Prop
  | [] => True
  | a :: l => s.Dom a l ∧ s.Adm l

/-- `lexChain` always reorders its input, even in the fallback branch. -/
theorem NormLevel.lexChain_perm {s : NormLevel} : ∀ {fuel p}, (s.lexChain fuel p).Perm p
  | 0, p => by rw [lexChain]
  | fuel+1, p => by
    rw [lexChain]
    split
    · rename_i a ha
      exact .trans (.cons _ lexChain_perm)
        (List.perm_cons_erase (List.mem_of_find?_eq_some ha)).symm
    · exact .refl _

/-- Whenever a key admits some chain, `lexChain` returns one: it reorders the key, and
every edge of the resulting `imax` chain is dominated. -/
theorem NormLevel.lexChain_spec {s : NormLevel} (hs : ∀ p n, s.get? p = some n → Sorted p) :
    ∀ {fuel p}, p.length ≤ fuel → Sorted p → s.Feas [] p →
      (s.lexChain fuel p).Perm p ∧ s.Adm (s.lexChain fuel p)
  | 0, p, hf, _, _ => by
    rw [lexChain]; cases p with | nil => exact ⟨.refl _, trivial⟩ | cons => cases hf
  | fuel+1, p, hf, hp, h => by
    rw [lexChain]
    split
    · rename_i a ha
      have hm := List.mem_of_find?_eq_some ha
      have hpred := List.find?_eq_some_iff_getElem.1 ha |>.1
      simp only [Bool.and_eq_true] at hpred
      have hlen : (p.erase a).length ≤ fuel := by
        rw [List.length_erase_of_mem hm]; omega
      obtain ⟨hperm, hadm⟩ :=
        lexChain_spec hs hlen hp.erase (feasible_sound hpred.2)
      refine ⟨.trans (.cons _ hperm) (List.perm_cons_erase hm).symm, ?_, hadm⟩
      exact (addable_sound hpred.1).mono fun x hx => hperm.mem_iff.2 hx
    · rename_i hnone
      -- the chain that exists ends somewhere, and `find?` would have found that element
      refine ⟨.refl _, ?_⟩
      match p, h with
      | [], _ => exact trivial
      | b :: p, h =>
        obtain ⟨a, hm, hd, hfa⟩ := h.peel hp.nodup (by simp)
        have h1 : s.addable a ((b :: p).erase a) :=
          addable_complete hs hp.erase (by simpa using hd)
        have h2 : s.feasible [] ((b :: p).erase a) := feasible_complete hs Sorted.nil hfa
        have hnot := List.find?_eq_none.1 hnone _ hm
        simp [h1, h2] at hnot

theorem NormLevel.Adm.suffix {s : NormLevel} : ∀ {l}, s.Adm l → a :: q <:+ l → s.Dom a q
  | [], _, h => by simp at h
  | b :: l, ⟨h1, h2⟩, h => by
    obtain ⟨l', he⟩ := h
    match l' with
    | [] => cases he; exact h1
    | c :: l' => exact Adm.suffix h2 ⟨l', by cases he; rfl⟩

/-! ### Building the tree -/

theorem evalPath_le_self : evalPath ls ρ path c ≤ c := by rw [evalPath]; split <;> simp

theorem evalPath_perm (h : p.Perm p') : evalPath ls ρ p c = evalPath ls ρ p' c := by
  simp only [evalPath, show allNZ ls ρ p = allNZ ls ρ p' from Bool.eq_iff_iff.2
    ⟨allNZ_mono fun _ hx => h.symm.mem_iff.1 hx, allNZ_mono fun _ hx => h.mem_iff.1 hx⟩]

theorem evalPath_singleton :
    evalPath ls ρ [a] c = if 0 < evalParam ls ρ a then c else 0 := by simp [evalPath, allNZ]

theorem evalPath_single : evalPath ls ρ p (evalPath ls ρ [a] c) = evalPath ls ρ (a :: p) c := by
  rw [evalPath_singleton, ← evalPath_cons]

theorem imax_eq_evalPath : Lean.Nat.imax c (evalParam ls ρ a) =
    max' (evalPath ls ρ [a] c) (evalPath ls ρ [a] (evalParam ls ρ a)) := by
  by_cases h : evalParam ls ρ a = 0 <;>
    simp [imax_eq_ite, evalPath_singleton, h, Nat.pos_of_ne_zero]

/-- `modify` read from the outside in, matching the way `Tree.At` extends a path: the
shallowest element of the path selects a child, and the rest is modified inside it. -/
theorem Tree.modify_append (path : List Name) (g : Tree → Tree) (b : Name) (t : Tree) :
    Tree.modify (path ++ [b]) g t =
    { t with child := modifyAt (Tree.modify path g) b t.child } := by
  induction path generalizing t g with
  | nil => rfl
  | cons a p ih => rw [List.cons_append, Tree.modify, ih]; rfl

/-- All that matters about `modifyAt`: it replaces one entry with key `a` by `f` of it, or
inserts `(a, f default)` somewhere if there is none, and leaves the rest of the list alone. -/
theorem modifyAt_eq (f : Tree → Tree) (a : Name) (l : List (Name × Tree)) :
    ∃ l₁ l₂ y, modifyAt f a l = l₁ ++ (a, f y) :: l₂ ∧
      (l = l₁ ++ l₂ ∧ y = default ∨ l = l₁ ++ (a, y) :: l₂) := by
  induction l with
  | nil => exact ⟨[], [], default, rfl, .inl ⟨rfl, rfl⟩⟩
  | cons b l ih =>
    obtain ⟨b, t⟩ := b
    match he : Name.cmp a b with
    | .lt => exact ⟨[], (b, t) :: l, default, by simp [modifyAt, he], .inl ⟨rfl, rfl⟩⟩
    | .eq =>
      rw [Std.LawfulBEqCmp.compare_eq_iff_beq (cmp := Name.cmp)] at he
      cases eq_of_beq he
      exact ⟨[], l, t, by
        simp [modifyAt, Std.ReflCmp.compare_self (cmp := Name.cmp)], .inr rfl⟩
    | .gt =>
      obtain ⟨l₁, l₂, y, h1, h2⟩ := ih
      exact ⟨(b, t) :: l₁, l₂, y, by simp [modifyAt, he, h1],
        h2.imp (fun ⟨h, hy⟩ => ⟨by simp [h], hy⟩) fun h => by simp [h]⟩

theorem mem_modifyAt_self (f : Tree → Tree) (a : Name) (l : List (Name × Tree)) :
    ∃ y, (a, f y) ∈ modifyAt f a l := by
  obtain ⟨l₁, l₂, y, h, -⟩ := modifyAt_eq f a l
  exact ⟨y, by rw [h]; simp⟩

/-- The node `modify` writes is there to be found, and its data does not depend on what was
at the path before: the payload of a key is what sits at the end of its chain. -/
theorem Tree.At_modify_self (path : List Name) (g : Tree → Tree) (t : Tree) :
    ∃ t₀, Tree.At (t.modify path g) path (g t₀) := by
  suffices ∀ (r : List Name) (g : Tree → Tree) (t : Tree),
      ∃ t₀, Tree.At (Tree.modify r.reverse g t) r.reverse (g t₀) by
    simpa using this path.reverse g t
  clear path g t; intro r
  induction r with
  | nil => exact fun g t => ⟨t, .nil⟩
  | cons b r ih =>
    intro g t
    rw [List.reverse_cons, Tree.modify_append]
    obtain ⟨x, hx⟩ := mem_modifyAt_self (f := Tree.modify r.reverse g) b t.child
    obtain ⟨t₀, ht₀⟩ := ih g x
    exact ⟨t₀, ht₀.append hx⟩

/-- Nothing is lost: an entry either survives `modifyAt` untouched, or is the one it modifies.
(The second case does not need the entry to be the *first* one with its key, so no
duplicate-freedom assumption is needed here or below.) -/
theorem mem_modifyAt {f : Tree → Tree} {l : List (Name × Tree)} (hm : (c, x) ∈ l) :
    (c, x) ∈ modifyAt f a l ∨ (c = a ∧ (c, f x) ∈ modifyAt f a l) := by
  obtain ⟨l₁, l₂, y, h, h'⟩ := modifyAt_eq f a l
  rw [h]
  obtain ⟨rfl, -⟩ | rfl := h'
  · obtain hm | hm := List.mem_append.1 hm
    · exact .inl (List.mem_append.2 (.inl hm))
    · exact .inl (List.mem_append.2 (.inr (.tail _ hm)))
  · obtain hm | hm := List.mem_append.1 hm
    · exact .inl (List.mem_append.2 (.inl hm))
    obtain heq | hm := List.mem_cons.1 hm
    · simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      exact .inr ⟨rfl, List.mem_append.2 (.inr (.head _))⟩
    · exact .inl (List.mem_append.2 (.inr (.tail _ hm)))

/-- A node written at one path survives a later write at a different path: the write only
replaces the data of the node it lands on, and every other node keeps its own. -/
theorem Tree.At_modify_of_ne_aux {g : Tree → Tree} (hg : ∀ t, (g t).child = t.child) :
    ∀ (r : List Name) {path t t'}, path ≠ r.reverse → At t path t' →
      ∃ t'', At (Tree.modify r.reverse g t) path t'' ∧
        t''.const = t'.const ∧ t''.var = t'.var := by
  intro r
  induction r with
  | nil =>
    intro path t t' hne h
    rw [List.reverse_nil, Tree.modify]
    obtain h' | ⟨rfl, rfl⟩ := h.of_child_eq (hg t)
    · exact ⟨t', h', rfl, rfl⟩
    · exact absurd rfl hne
  | cons b r ih =>
    intro path t t' hne h
    rw [List.reverse_cons, Tree.modify_append]
    obtain rfl | ⟨q, a, rfl⟩ := List.eq_nil_or_concat path
    · cases h.nil_inv; exact ⟨_, .nil, rfl, rfl⟩
    simp only [List.concat_eq_append, List.reverse_cons] at h hne ⊢
    obtain ⟨t₁, hm, h₁⟩ := h.append_inv
    obtain hm' | ⟨rfl, hm'⟩ := mem_modifyAt (f := Tree.modify r.reverse g) (a := b) hm
    · exact ⟨t', h₁.append hm', rfl, rfl⟩
    · have : q ≠ r.reverse := by rintro rfl; exact hne rfl
      obtain ⟨t'', h'', hc, hv⟩ := ih this h₁
      exact ⟨t'', h''.append hm', hc, hv⟩

theorem Tree.At_modify_of_ne {g : Tree → Tree} (hg : ∀ t, (g t).child = t.child)
    (hne : path ≠ path') (h : At t path t') :
    ∃ t'', At (Tree.modify path' g t) path t'' ∧ t''.const = t'.const ∧ t''.var = t'.var := by
  have := At_modify_of_ne_aux hg path'.reverse (path := path) (by rwa [List.reverse_reverse]) h
  rwa [List.reverse_reverse] at this

/-- Conversely, nothing appears from nowhere: an entry of `modifyAt` is an entry of the list,
or the modified one, which was an entry or is fresh. -/
theorem mem_modifyAt_inv {f : Tree → Tree} {l : List (Name × Tree)}
    (h : (c, x) ∈ modifyAt f a l) :
    (c, x) ∈ l ∨ (c = a ∧ ∃ y, x = f y ∧ (y = default ∨ (a, y) ∈ l)) := by
  induction l with
  | nil =>
    simp only [modifyAt, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, default, rfl, .inl rfl⟩
  | cons b l ih =>
    obtain ⟨b, t⟩ := b
    match he : Name.cmp a b with
    | .lt =>
      simp only [modifyAt, he] at h
      obtain h | h := List.mem_cons.1 h
      · cases h; exact .inr ⟨rfl, default, rfl, .inl rfl⟩
      · exact .inl h
    | .eq =>
      rw [Std.LawfulBEqCmp.compare_eq_iff_beq (cmp := Name.cmp)] at he
      cases eq_of_beq he
      simp only [modifyAt, Std.ReflCmp.compare_self (cmp := Name.cmp)] at h
      obtain h | h := List.mem_cons.1 h
      · cases h; exact .inr ⟨rfl, t, rfl, .inr (.head _)⟩
      · exact .inl (.tail _ h)
    | .gt =>
      simp only [modifyAt, he] at h
      obtain h | h := List.mem_cons.1 h
      · cases h; exact .inl (.head _)
      · exact (ih h).imp (.tail _) fun ⟨rfl, y, hy, h⟩ => ⟨rfl, y, hy, h.imp id (.tail _)⟩

theorem Tree.At.of_child_nil (hc : t.child = []) (h : At t p t') : p = [] ∧ t' = t := by
  obtain rfl | ⟨q, a, rfl⟩ := List.eq_nil_or_concat p
  · exact ⟨rfl, h.nil_inv⟩
  · rw [List.concat_eq_append] at h
    obtain ⟨t₁, hm, -⟩ := h.append_inv
    rw [hc] at hm; cases hm

theorem suffix_concat {α} {l₁ l₂ : List α} (h : l₁ <:+ l₂) (a : α) :
    l₁ ++ [a] <:+ l₂ ++ [a] := by
  obtain ⟨u, rfl⟩ := h; exact ⟨u, by rw [List.append_assoc]⟩

/-- Inverting a write: a path of the modified tree either ends at the node just written, or
is a tail of the written path whose node was created empty on the way, or was already there
carrying the same data. -/
theorem Tree.At_modify_inv_aux {g : Tree → Tree} (hg : ∀ t, (g t).child = t.child) :
    ∀ (r : List Name) {path t t'}, At (Tree.modify r.reverse g t) path t' →
      (path = r.reverse ∧ ∃ t₀, t' = g t₀) ∨
      (path <:+ r.reverse ∧ t'.const = 0 ∧ t'.var = []) ∨
      (∃ t'', At t path t'' ∧ t'.const = t''.const ∧ t'.var = t''.var) := by
  intro r
  induction r with
  | nil =>
    intro path t t' h
    rw [List.reverse_nil, Tree.modify] at h
    obtain h' | ⟨rfl, rfl⟩ := h.of_child_eq (hg t).symm
    · exact .inr (.inr ⟨t', h', rfl, rfl⟩)
    · exact .inl ⟨rfl, t, rfl⟩
  | cons b r ih =>
    intro path t t' h
    rw [List.reverse_cons, Tree.modify_append] at h
    obtain rfl | ⟨q, a, rfl⟩ := List.eq_nil_or_concat path
    · cases h.nil_inv; exact .inr (.inr ⟨t, .nil, rfl, rfl⟩)
    rw [List.concat_eq_append] at h ⊢
    obtain ⟨t₁, hm, h₁⟩ := h.append_inv
    obtain hm | ⟨rfl, y, rfl, hy⟩ := mem_modifyAt_inv hm
    · exact .inr (.inr ⟨t', h₁.append hm, rfl, rfl⟩)
    · obtain ⟨rfl, t₀, rfl⟩ | ⟨hs, hc, hv⟩ | ⟨t'', h'', hc, hv⟩ := ih h₁
      · exact .inl ⟨by rw [List.reverse_cons], t₀, rfl⟩
      · exact .inr (.inl ⟨by rw [List.reverse_cons]; exact suffix_concat hs _, hc, hv⟩)
      · obtain rfl | hy := hy
        · obtain ⟨rfl, rfl⟩ := h''.of_child_nil rfl
          exact .inr (.inl ⟨by rw [List.reverse_cons]; exact ⟨r.reverse, by simp⟩, hc, hv⟩)
        · exact .inr (.inr ⟨t'', h''.append hy, hc, hv⟩)

theorem Tree.At_modify_inv {g : Tree → Tree} (hg : ∀ t, (g t).child = t.child)
    (h : At (Tree.modify path' g t) path t') :
    (path = path' ∧ ∃ t₀, t' = g t₀) ∨
    (path <:+ path' ∧ t'.const = 0 ∧ t'.var = []) ∨
    (∃ t'', At t path t'' ∧ t'.const = t''.const ∧ t'.var = t''.var) := by
  have := At_modify_inv_aux hg path'.reverse (path := path)
    (by rwa [List.reverse_reverse]) (t' := t')
  rwa [List.reverse_reverse] at this

/-- Sorted lists with the same elements are equal, so distinct keys reify to distinct paths:
`lexChain` only permutes a key. -/
theorem Sorted.perm_eq (h₁ : Sorted l₁) (h₂ : Sorted l₂) (h : l₁.Perm l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact h.nil_eq
  | cons a l₁ ih =>
    match l₂, h₂, h with
    | [], _, h => simp at h
    | b :: l₂, h₂, h =>
      have hab : a = b := by
        -- each head is at most every element of the other list
        obtain rfl | ha := List.mem_cons.1 (h.mem_iff.1 (.head _))
        · rfl
        obtain rfl | hb := List.mem_cons.1 (h.symm.mem_iff.1 (.head _))
        · rfl
        exact absurd (h₂.head _ ha) (by
          rw [Std.OrientedCmp.gt_of_lt (h₁.head _ hb)]; simp)
      subst hab
      rw [ih h₁.of_cons h₂.of_cons ((List.perm_cons _).1 h)]

/-- The variables the reconstruction records for the entry `(p, n)`: those of `n`, except the
one the edge into the node already contributes. -/
def NormLevel.treeVar (s : NormLevel) (p : List Name) (n : Node) : List VarNode :=
  if let v :: _ := s.lexChain p.length p then subsumeVars n.var [⟨v, 0⟩] else n.var

/-- The entry `(p, n)` is recorded in `t`: at the end of `p`'s chain sits a node carrying
`n`'s constant and `treeVar p n`. -/
def NormLevel.WrittenAt (s : NormLevel) (t : Tree) (p : List Name) (n : Node) : Prop :=
  ∃ t', Tree.At t (s.lexChain p.length p) t' ∧ t'.const = n.const ∧ t'.var = s.treeVar p n

theorem NormLevel.WrittenAt.write {s : NormLevel} (t : Tree) (p : List Name) (n : Node) :
    s.WrittenAt (t.modify (s.lexChain p.length p)
      fun t => { t with const := n.const, var := s.treeVar p n }) p n :=
  let ⟨_, h⟩ := Tree.At_modify_self _ _ t
  ⟨_, h, rfl, rfl⟩

/-- Distinct keys get distinct chains, since `lexChain` only permutes a sorted key. -/
theorem NormLevel.lexChain_inj {s : NormLevel} (h₁ : Sorted p) (h₂ : Sorted p')
    (h : s.lexChain p.length p = s.lexChain p'.length p') : p = p' := by
  refine Sorted.perm_eq h₁ h₂ ((lexChain_perm (s := s) (fuel := p.length) (p := p)).symm.trans ?_)
  rw [h]; exact lexChain_perm

/-- Conversely, everything the tree contains comes from an entry: every nonempty path is a
tail of some key's chain, and the node at the end of a path is either empty scaffolding or
the entry whose chain leads there. -/
def NormLevel.Accounted (s : NormLevel) (t : Tree) : Prop :=
  ∀ path t', Tree.At t path t' →
    (path ≠ [] → ∃ p n, s.get? p = some n ∧ path <:+ s.lexChain p.length p) ∧
    (t'.const = 0 ∧ t'.var = [] ∨ ∃ p n, s.get? p = some n ∧
      path = s.lexChain p.length p ∧ t'.const = n.const ∧ t'.var = s.treeVar p n)

/-- The single pass over the map that both directions of soundness read off: after the fold
every entry is recorded at the end of its chain, and everything in the tree is accounted for
by an entry. A write puts its own entry there (`At_modify_self`) and leaves the others alone,
either because it lands on a different path — distinct keys have distinct chains — or because
it lands on the same key, and then writes the same data. -/
theorem NormLevel.toTree_spec {s : NormLevel} (hsort : ∀ p n, s.get? p = some n → Sorted p) :
    s.Accounted (toTree s) ∧ ∀ p n, s.get? p = some n → s.WrittenAt (toTree s) p n := by
  rw [toTree, Std.TreeMap.foldl_eq_foldl_toList]
  have hmem : ∀ pn : List Name × Node, pn ∈ s.toList ↔ s.get? pn.1 = some pn.2 := fun _ =>
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.trans (by rw [Std.TreeMap.get?_eq_getElem?])
  have hinit : s.Accounted ⟨0, [], []⟩ := fun path t' h => by
    obtain ⟨rfl, rfl⟩ := h.of_child_nil rfl
    exact ⟨fun h => absurd rfl h, .inl ⟨rfl, rfl⟩⟩
  suffices ∀ (l : List (List Name × Node)) (t : Tree),
      (∀ pn ∈ l, s.get? pn.1 = some pn.2) → s.Accounted t →
      s.Accounted (List.foldl (fun t pn =>
        let path := s.lexChain pn.1.length pn.1
        let var := if let v :: _ := path then subsumeVars pn.2.var [⟨v, 0⟩] else pn.2.var
        t.modify path fun t => { t with const := pn.2.const, var }) t l) ∧
      ∀ p n, s.get? p = some n → (s.WrittenAt t p n ∨ (p, n) ∈ l) →
      s.WrittenAt (List.foldl (fun t pn =>
        let path := s.lexChain pn.1.length pn.1
        let var := if let v :: _ := path then subsumeVars pn.2.var [⟨v, 0⟩] else pn.2.var
        t.modify path fun t => { t with const := pn.2.const, var }) t l) p n by
    have := this _ _ (fun pn h => (hmem pn).1 h) hinit
    exact ⟨this.1, fun p n hp => this.2 p n hp (.inr ((hmem (p, n)).2 hp))⟩
  clear hmem hinit; intro l
  induction l with
  | nil => exact fun _ _ h => ⟨h, fun _ _ _ h => h.resolve_right (by simp)⟩
  | cons pn l ih =>
    obtain ⟨p', n'⟩ := pn
    intro t hl hacc
    have hp' : s.get? p' = some n' := hl _ (.head _)
    refine (ih _ (fun _ h => hl _ (.tail _ h)) ?_).imp id fun H p n hp h => H p n hp ?_
    · -- nothing unaccounted for appears: the write adds its own node and empty scaffolding
      intro path t' h
      obtain ⟨rfl, t₀, rfl⟩ | ⟨hs, hc, hv⟩ | ⟨t'', h'', hc, hv⟩ :=
        Tree.At_modify_inv (g := fun t =>
          { t with const := n'.const, var := s.treeVar p' n' }) (fun _ => rfl) h
      · exact ⟨fun _ => ⟨p', n', hp', List.suffix_refl _⟩, .inr ⟨p', n', hp', rfl, rfl, rfl⟩⟩
      · exact ⟨fun _ => ⟨p', n', hp', hs⟩, .inl ⟨hc, hv⟩⟩
      · exact ⟨(hacc _ _ h'').1, by rw [hc, hv]; exact (hacc _ _ h'').2⟩
    · -- and nothing already written is lost
      obtain ⟨t', hat, hc, hv⟩ | h := h
      · refine .inl ?_
        by_cases hpp : p = p'
        · subst hpp; cases hp.symm.trans hp'; exact .write ..
        · obtain ⟨t'', hat', hc', hv'⟩ := Tree.At_modify_of_ne (g := fun t =>
            { t with const := n'.const, var := s.treeVar p' n' }) (fun _ => rfl)
            (fun he => hpp (lexChain_inj (hsort _ _ hp) (hsort _ _ hp') he)) hat
          exact ⟨t'', hat', hc' ▸ hc, hv' ▸ hv⟩
      · obtain h | h := List.mem_cons.1 h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inl (.write ..)
        · exact .inr h

/-- What the reconstruction contributes, as a biconditional: the tree is bounded by `m`
exactly when for every entry the node the tree records for it is, and so is every edge of its
chain. Nothing here is about domination, so no hypothesis on the chains is needed. -/
theorem NormLevel.toTree_le_iff {s : NormLevel} (hsort : ∀ p n, s.get? p = some n → Sorted p)
    {m : Nat} : Tree.eval ls ρ (toTree s) ≤ m ↔
      ∀ p n, s.get? p = some n →
        evalPath ls ρ (s.lexChain p.length p) (Node.eval ls ρ ⟨n.const, s.treeVar p n⟩) ≤ m ∧
        ∀ a q, a :: q <:+ s.lexChain p.length p →
          evalPath ls ρ (a :: q) (evalParam ls ρ a) ≤ m := by
  obtain ⟨hacc, hwr⟩ := toTree_spec hsort
  rw [Tree.eval_le_iff]
  refine ⟨fun ⟨h1, h2⟩ p n hp => ?_, fun H => ⟨fun path t' hat => ?_, fun a q t' hat => ?_⟩⟩
  · obtain ⟨t', hat, hc, hv⟩ := hwr p n hp
    refine ⟨by rw [← hc, ← hv]; exact h1 _ _ hat, fun a q hq => ?_⟩
    obtain ⟨t'', hat''⟩ := hat.suffix hq
    exact h2 _ _ _ hat''
  · obtain ⟨-, ⟨hc, hv⟩ | ⟨p, n, hp, rfl, hc, hv⟩⟩ := hacc _ _ hat
    · rw [show Node.eval ls ρ ⟨t'.const, t'.var⟩ = 0 from by simp [Node.eval, hc, hv]]
      simp [evalPath]
    · rw [hc, hv]; exact (H p n hp).1
  · obtain ⟨p, n, hp, hsuf⟩ := (hacc _ _ hat).1 (by simp)
    exact (H p n hp).2 _ _ hsuf

/-- Soundness of the reconstruction: the tree built from a normal form, hence the level it
reifies to, evaluates like the normal form. Below, because the node recorded for an entry
carries a subset of its sublevels and every edge is dominated, `lexChain` emitting only
admissible chains; above, because the one sublevel the node omits, `V(p, v, 0)` for the
innermost element of the chain, is what the edge into it contributes. -/
theorem NormLevel.toTree_eval {s : NormLevel} (hsort : ∀ p n, s.get? p = some n → Sorted p)
    (hfeas : ∀ p, s.contains p → s.Feas [] p) :
    Tree.eval ls ρ (toTree s) = s.eval ls ρ := by
  refine ext_le fun m => (toTree_le_iff hsort).trans (Iff.trans ?_ NormLevel.eval_le.symm)
  refine ⟨fun H p n hp => ?_, fun H p n hp => ⟨?_, fun a q hq => ?_⟩⟩
  · -- the entry is the node the tree records for it, plus the edge into that node
    rw [← evalPath_perm (lexChain_perm (s := s) (fuel := p.length) (p := p))]
    refine evalPath_le.2 fun nz => ?_
    have h1 := evalPath_le.1 (H p n hp).1 nz
    rw [Node.eval_le] at h1 ⊢
    refine ⟨h1.1, ?_⟩
    rw [NormLevel.treeVar] at h1
    split at h1
    · rename_i v q hch
      refine (subsumeVars_eval ?_).1 h1.2
      simp only [List.mem_singleton, VarNode.eval]
      rintro _ rfl
      exact evalPath_le.1 ((H p n hp).2 v q (by rw [hch]; exact List.suffix_refl _)) (hch ▸ nz)
    · exact h1.2
  · -- the recorded node is part of the entry
    rw [evalPath_perm (lexChain_perm (s := s) (fuel := p.length) (p := p))]
    refine Nat.le_trans (evalPath_mono ?_) (H p n hp)
    refine Node.eval_le.2 ⟨Node.const_le_eval (l := n), fun v hv => Node.var_le_eval ?_⟩
    revert hv; rw [NormLevel.treeVar]; split
    · exact subsumeVars_subset
    · exact id
  · -- and every edge of the chain is dominated by an entry
    have hcon : s.contains p := Std.TreeMap.isSome_getElem?_eq_contains.symm.trans
      (by simp [Std.TreeMap.get?_eq_getElem?] at hp; simp [hp])
    obtain ⟨-, hadm⟩ := lexChain_spec hsort (Nat.le_refl _) (hsort _ _ hp) (hfeas _ hcon)
    exact Nat.le_trans (hadm.suffix hq).le (NormLevel.eval_le.2 H)

/-!
### Completeness

`geq'` and `isEquiv'` are not only sound but complete: `NormLevel.le` detects every semantic
inequality between normal forms, and semantically equal levels have equal normal forms. The
key is a converse to Theorem 39 (`NormLevel.le_eval`): evaluating at a valuation tailored to
a single sublevel shows that a semantic bound forces a syntactic dominator among the
sublevels of the bounding form (`separation`). Completeness of `le` then follows because the
`subsumeBy` fold removes exactly the dominated sublevels, and canonicity because
`subsumption` leaves no sublevel dominated by another slot (`Reduced`), so mutual domination
forces the two maps to be equal.
-/

/-- The variable lists of nodes are strictly sorted by variable name. -/
def VarsSorted (l : List VarNode) : Prop := l.Pairwise (compare ·.var ·.var = .lt)

theorem VarsSorted.of_cons (h : VarsSorted (v :: l)) : VarsSorted l := (List.pairwise_cons.1 h).2

theorem VarsSorted.head (h : VarsSorted (v :: l)) : ∀ x ∈ l, compare v.var x.var = .lt :=
  (List.pairwise_cons.1 h).1

/-- In a sorted variable list, the name determines the entry. -/
theorem VarsSorted.eq_of_var_eq (h : VarsSorted l) (h₁ : x ∈ l) (h₂ : y ∈ l)
    (e : x.var = y.var) : x = y := by
  induction l with | nil => cases h₁ | cons v l ih
  obtain rfl | h₁' := List.mem_cons.1 h₁
  · obtain rfl | h₂' := List.mem_cons.1 h₂
    · rfl
    · have := h.head _ h₂'; rw [e, Std.ReflOrd.compare_self] at this; cases this
  · obtain rfl | h₂' := List.mem_cons.1 h₂
    · have := h.head _ h₁'; rw [← e, Std.ReflOrd.compare_self] at this; cases this
    · exact ih h.of_cons h₁' h₂'

theorem VarNode.mem_addVar' (h : x ∈ VarNode.addVar v k l) : x.var = v ∨ x ∈ l := by
  induction l with
  | nil => simp [addVar] at h; simp [h]
  | cons y l ih =>
    simp only [addVar] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h <;> simp [h]
    · rcases List.mem_cons.1 h with rfl | h <;> simp [h]
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact (ih h).imp_right (.tail _)

theorem VarNode.addVar_sorted (h : VarsSorted l) : VarsSorted (VarNode.addVar v k l) := by
  induction l with | nil => exact .cons (by simp) .nil | cons x l ih
  simp only [addVar]
  split <;> rename_i hc
  · refine .cons (fun y hy => ?_) h
    obtain rfl | hy := List.mem_cons.1 hy
    · exact hc
    · exact Std.TransCmp.lt_trans hc (h.head _ hy)
  · rw [Std.LawfulBEqCmp.compare_eq_iff_beq] at hc
    have e := eq_of_beq hc
    exact .cons (fun y hy => by rw [e]; exact h.head _ hy) h.of_cons
  · refine .cons (fun y hy => ?_) (ih h.of_cons)
    obtain e | hy := VarNode.mem_addVar' hy
    · rw [e]; exact Std.OrientedCmp.lt_of_gt hc
    · exact h.head _ hy

/-- Every node of the map has its variable list sorted by name. -/
def NormLevel.SortedVars (s : NormLevel) : Prop :=
  ∀ p n, s.get? p = some n → VarsSorted n.var

theorem NormLevel.addVar_sortedVars (h : acc.SortedVars) :
    (addVar v k path acc).SortedVars := by
  intro p n hn
  simp only [addVar, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_modify] at hn
  split at hn
  · obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.1 hn
    exact VarNode.addVar_sorted (h path n' (Std.TreeMap.get?_eq_getElem? .. ▸ hn'))
  · exact h _ _ (Std.TreeMap.get?_eq_getElem? .. ▸ hn)

theorem NormLevel.addNode_sortedVars (h : acc.SortedVars) :
    (addNode v k path acc).SortedVars := by
  intro p n hn
  simp only [addNode, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_alter] at hn
  split at hn
  · match e : acc[path]?, hn with
    | some n', hn =>
      cases hn; exact VarNode.addVar_sorted (h path n' (Std.TreeMap.get?_eq_getElem? .. ▸ e))
    | none, hn => cases hn; exact .cons (by simp) .nil
  · exact h _ _ (Std.TreeMap.get?_eq_getElem? .. ▸ hn)

theorem NormLevel.addConst_sortedVars (h : acc.SortedVars) :
    (addConst k path acc).SortedVars := by
  intro p n hn
  simp only [addConst] at hn; split at hn <;> [exact h _ _ hn; skip]
  simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_alter] at hn
  split at hn
  · match e : acc[path]?, hn with
    | some n', hn => cases hn; exact h path n' (Std.TreeMap.get?_eq_getElem? .. ▸ e)
    | none, hn => cases hn; exact .nil
  · exact h _ _ (Std.TreeMap.get?_eq_getElem? .. ▸ hn)

theorem normalizeAux_sortedVars (h : acc.SortedVars) :
    (normalizeAux u path k acc).SortedVars := by
  unfold normalizeAux; split
  · exact NormLevel.addConst_sortedVars h
  · exact NormLevel.addConst_sortedVars h
  · exact normalizeAux_sortedVars h
  · exact normalizeAux_sortedVars (normalizeAux_sortedVars h)
  · exact normalizeAux_sortedVars (normalizeAux_sortedVars h)
  · exact normalizeAux_sortedVars (normalizeAux_sortedVars h)
  · exact normalizeAux_sortedVars (normalizeAux_sortedVars h)
  · split <;> [skip; (dsimp; split)]
    · exact normalizeAux_sortedVars
        (NormLevel.addNode_sortedVars (NormLevel.addConst_sortedVars h))
    · exact normalizeAux_sortedVars h
    · exact normalizeAux_sortedVars (NormLevel.addVar_sortedVars h)
  · exact h
  · exact h
  · split <;> [skip; split]
    · exact NormLevel.addNode_sortedVars (NormLevel.addConst_sortedVars h)
    · exact h
    · exact NormLevel.addVar_sortedVars h

theorem subsumeVars_sublist : ∀ vs₁ vs₂ : List VarNode, List.Sublist (subsumeVars vs₁ vs₂) vs₁
  | [], _ => by simp [subsumeVars]
  | _ :: _, [] => by simp [subsumeVars]
  | x :: xs, y :: ys => by
    simp only [subsumeVars]; split
    · exact (subsumeVars_sublist xs (y :: ys)).cons_cons x
    · split
      · exact (subsumeVars_sublist xs ys).cons x
      · exact (subsumeVars_sublist xs ys).cons_cons x
    · exact subsumeVars_sublist (x :: xs) ys

theorem Node.subsume_var_sublist : List.Sublist (Node.subsume p₁ n₁ p₂ n₂).var n₁.var := by
  obtain h | ⟨-, -, h⟩ := Node.subsume_var_cases p₁ n₁ p₂ n₂ <;> rw [h]
  · exact List.Sublist.refl _
  · exact subsumeVars_sublist ..

theorem NormLevel.minimize_var_sublist {acc : NormLevel} :
    List.Sublist (acc.minimize p₁ n₁).var n₁.var := by
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList]
  generalize acc.toList = l
  induction l generalizing n₁ with | nil => exact List.Sublist.refl _ | cons a l ih
  exact (ih (n₁ := Node.subsume p₁ n₁ a.1 a.2)).trans Node.subsume_var_sublist

theorem NormLevel.subsumption_sortedVars {s : NormLevel} (hs : s.SortedVars) :
    s.subsumption.SortedVars := by
  rw [subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  have hmem pn (h : pn ∈ s.toList) : s.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  generalize s.toList = l at hmem
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (∀ pn ∈ l, s.get? pn.1 = some pn.2) → acc.SortedVars →
      ∀ p n, (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).get? p = some n →
        VarsSorted n.var from this _ _ hmem hs
  clear hmem; intro l
  induction l with | nil => exact fun _ _ => id | cons pn l ih
  intro acc hl hacc
  refine ih _ (fun _ h => hl _ (.tail _ h)) fun p n h => ?_
  rw [subsumption_step_get?] at h
  split at h
  · split at h <;> [cases h; skip]
    cases h; rename_i hp _; subst hp
    exact (hs _ _ (hl _ (.head _))).sublist minimize_var_sublist
  · exact hacc _ _ h

theorem normalize_sortedVars : (normalize u).SortedVars :=
  NormLevel.subsumption_sortedVars (normalizeAux_sortedVars fun p n h => by simp at h)

/-- `subsumption` erases a key rather than leaving an empty node behind. -/
theorem NormLevel.subsumption_nonempty {s : NormLevel} :
    ∀ p n, s.subsumption.get? p = some n → n.isEmpty = false := by
  rw [subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (∀ p n, acc.get? p = some n → n.isEmpty = false ∨ (p, n) ∈ l) →
      ∀ p n, (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).get? p = some n →
        n.isEmpty = false from
    this _ _ fun p n h => .inr (Std.TreeMap.mem_toList_iff_getElem?_eq_some.2
      (Std.TreeMap.get?_eq_getElem? .. ▸ h))
  intro l
  induction l with
  | nil => exact fun acc h p n hn => (h p n hn).resolve_right (by simp)
  | cons pn l ih =>
    intro acc hacc
    refine ih _ fun p n h => ?_
    rw [subsumption_step_get?] at h
    split at h <;> rename_i hp
    · split at h <;> [cases h; skip]
      cases h; rename_i he; exact .inl (by simpa using he)
    · refine (hacc _ _ h).imp_right fun hm => ?_
      obtain h' | h' := List.mem_cons.1 hm
      · exact absurd (congrArg Prod.fst h'.symm) hp
      · exact h'

theorem normalize_nonempty : ∀ p n, (normalize u).get? p = some n → n.isEmpty = false :=
  NormLevel.subsumption_nonempty

theorem NormLevel.addVar_keys (h : (addVar v k path acc).contains p) : acc.contains p := by
  simpa [addVar, Std.TreeMap.mem_modify] using h

theorem NormLevel.addNode_keys (h : (addNode v k path acc).contains p) :
    p = path ∨ acc.contains p := by
  rw [addNode, Std.TreeMap.contains_alter] at h
  split at h
  · rename_i hc
    exact .inl (eq_of_beq (Std.LawfulBEqCmp.compare_eq_iff_beq.1 hc)).symm
  · exact .inr h

theorem NormLevel.addConst_keys (h : (addConst k path acc).contains p) :
    p = path ∨ acc.contains p := by
  rw [addConst] at h; split at h <;> [exact .inr h; skip]
  rw [Std.TreeMap.contains_alter] at h
  split at h
  · rename_i hc
    exact .inl (eq_of_beq (Std.LawfulBEqCmp.compare_eq_iff_beq.1 hc)).symm
  · exact .inr h

/-- All keys of the map built by `normalizeAux` consist of level parameters, which are
in `ls` whenever `ofLevel` succeeds. -/
theorem normalizeAux_keys (hu : VLevel.ofLevel ls u = some u')
    (hpath : ∀ x ∈ path, x ∈ ls) (hacc : ∀ p, acc.contains p → ∀ x ∈ p, x ∈ ls) :
    ∀ p, (normalizeAux u path k acc).contains p → ∀ x ∈ p, x ∈ ls := by
  unfold normalizeAux; split
  · exact fun p h => (NormLevel.addConst_keys h).elim
      (fun e x hx => hpath x (e ▸ hx)) (hacc p)
  · exact fun p h => (NormLevel.addConst_keys h).elim
      (fun e x hx => hpath x (e ▸ hx)) (hacc p)
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    exact normalizeAux_keys hu hpath hacc
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, hv, rfl⟩ := hu
    exact normalizeAux_keys hv hpath (normalizeAux_keys hu hpath hacc)
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, rfl⟩, rfl⟩ := hu
    exact normalizeAux_keys hv hpath (normalizeAux_keys hu hpath hacc)
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    exact normalizeAux_keys (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) hpath
      (normalizeAux_keys (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hv, rfl⟩) hpath hacc)
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    exact normalizeAux_keys (by simpa [VLevel.ofLevel] using ⟨_, hv, _, hw, rfl⟩) hpath
      (normalizeAux_keys (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) hpath hacc)
  · rename_i u v
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨hv, rfl⟩, rfl⟩ := hu
    have hvls : v ∈ ls := List.idxOf_lt_length_iff.1 hv
    split <;> rename_i h
    · refine normalizeAux_keys hu (fun x hx => ?_) fun q hq => ?_
      · exact ((Extend1.orderedInsert h).mem.1 hx).elim (fun e => e.symm ▸ hvls) (hpath x)
      · obtain e | hq' := NormLevel.addNode_keys hq
        · exact fun x hx => by
            rcases (Extend1.orderedInsert h).mem.1 (e ▸ hx) with rfl | hx'
            · exact hvls
            · exact hpath x hx'
        · exact (NormLevel.addConst_keys hq').elim
            (fun e x hx => hpath x (e ▸ hx)) (hacc q)
    · dsimp; split
      · exact normalizeAux_keys hu hpath hacc
      · exact normalizeAux_keys hu hpath fun q hq => hacc q (NormLevel.addVar_keys hq)
  · exact hacc
  · exact hacc
  · rename_i v
    simp [VLevel.ofLevel] at hu; obtain ⟨hv, rfl⟩ := hu
    have hvls : v ∈ ls := List.idxOf_lt_length_iff.1 hv
    split <;> rename_i h
    · intro q hq
      obtain e | hq' := NormLevel.addNode_keys hq
      · exact fun x hx => by
          rcases (Extend1.orderedInsert h).mem.1 (e ▸ hx) with rfl | hx'
          · exact hvls
          · exact hpath x hx'
      · exact (NormLevel.addConst_keys hq').elim
          (fun e x hx => hpath x (e ▸ hx)) (hacc q)
    · split
      · exact hacc
      · exact fun q hq => hacc q (NormLevel.addVar_keys hq)

theorem normalize_keys (hu : VLevel.ofLevel ls u = some u') :
    ∀ p n, (normalize u).get? p = some n → ∀ x ∈ p, x ∈ ls := by
  intro p n h
  obtain ⟨n₀, h₀, -⟩ := NormLevel.subsumption_covers.1 p n h
  have hc : (normalizeAux u [] 0 {}).contains p :=
    Std.TreeMap.isSome_getElem?_eq_contains.symm.trans
      (by simp [Std.TreeMap.get?_eq_getElem?] at h₀; simp [h₀])
  exact normalizeAux_keys hu (by simp) (fun q hq => by simp at hq) p hc

/-- A single sublevel of the canonical form: `Sub.const p k` is `C(p, k)` and
`Sub.var p x k` is `V(p, x, k)`. -/
inductive Sub where
  | const (p : List Name) (k : Nat)
  | var (p : List Name) (x : Name) (k : Nat)

def Sub.path : Sub → List Name
  | .const p _ => p
  | .var p _ _ => p

/-- Domination of sublevels, following Theorem 39: `s.le t` when `t`'s value bounds `s`'s
value under every valuation. The dominator's condition set is a *subset*, so that it fires
whenever the dominated sublevel does; a constant is dominated by `V(F, x, K)` up to `K + 1`
since that sublevel is at least `K + 1` whenever its conditions hold; and a variable
sublevel is only dominated by the same variable at a larger offset. -/
protected def Sub.le : Sub → Sub → Prop
  | .const p k, .const q l => (∀ z ∈ q, z ∈ p) ∧ k ≤ l
  | .const p k, .var q _ l => (∀ z ∈ q, z ∈ p) ∧ k ≤ l + 1
  | .var _ _ _, .const _ _ => False
  | .var p x k, .var q y l => (∀ z ∈ q, z ∈ p) ∧ x = y ∧ k ≤ l

protected theorem Sub.le.trans : ∀ {a b c : Sub}, a.le b → b.le c → a.le c
  | .const _ _, .const _ _, .const _ _, ⟨s₁, h₁⟩, ⟨s₂, h₂⟩ =>
    ⟨fun z hz => s₁ _ (s₂ _ hz), Nat.le_trans h₁ h₂⟩
  | .const _ _, .const _ _, .var _ _ _, ⟨s₁, h₁⟩, ⟨s₂, h₂⟩ =>
    ⟨fun z hz => s₁ _ (s₂ _ hz), by omega⟩
  | .const _ _, .var _ _ _, .const _ _, _, h₂ => h₂.elim
  | .const _ _, .var _ _ _, .var _ _ _, ⟨s₁, h₁⟩, ⟨s₂, _, h₂⟩ =>
    ⟨fun z hz => s₁ _ (s₂ _ hz), by omega⟩
  | .var _ _ _, .const _ _, _, h₁, _ => h₁.elim
  | .var _ _ _, .var _ _ _, .const _ _, _, h₂ => h₂.elim
  | .var _ _ _, .var _ _ _, .var _ _ _, ⟨s₁, e₁, h₁⟩, ⟨s₂, e₂, h₂⟩ =>
    ⟨fun z hz => s₁ _ (s₂ _ hz), e₁.trans e₂, Nat.le_trans h₁ h₂⟩

theorem subset_antisymm (h₁ : Sorted l₁) (h₂ : Sorted l₂)
    (h : ∀ z ∈ l₁, z ∈ l₂) (h' : ∀ z ∈ l₂, z ∈ l₁) : l₁ = l₂ :=
  subset_eq (subset_of_sorted h₁ h₂ h) <|
    Nat.le_antisymm (subset_length (subset_of_sorted h₁ h₂ h))
      (subset_length (subset_of_sorted h₂ h₁ h'))

protected theorem Sub.le.antisymm : ∀ {a b : Sub}, Sorted a.path → Sorted b.path →
    a.le b → b.le a → a = b
  | .const p _, .const q _, ha, hb, ⟨s₁, h₁⟩, ⟨s₂, h₂⟩ => by
    rw [subset_antisymm (l₁ := p) (l₂ := q) ha hb s₂ s₁, Nat.le_antisymm h₁ h₂]
  | .const _ _, .var _ _ _, _, _, _, h₂ => h₂.elim
  | .var _ _ _, .const _ _, _, _, h₁, _ => h₁.elim
  | .var p _ _, .var q _ _, ha, hb, ⟨s₁, e₁, h₁⟩, ⟨s₂, e₂, h₂⟩ => by
    rw [subset_antisymm (l₁ := p) (l₂ := q) ha hb s₂ s₁, e₁, Nat.le_antisymm h₁ h₂]

/-- The sublevels recorded in a `NormLevel`: `C(p, n.const)` for nonzero constants and
`V(p, x, k)` for each recorded variable. -/
def NormLevel.HasSub (s : NormLevel) : Sub → Prop
  | .const p k => ∃ n, s.get? p = some n ∧ n.const = k ∧ k ≠ 0
  | .var p x k => ∃ n, s.get? p = some n ∧ ⟨x, k⟩ ∈ n.var

variable (ls : List Name) (ρ : List Nat) in
def Sub.eval : Sub → Nat
  | .const p k => evalPath ls ρ p k
  | .var p x k => evalPath ls ρ p (evalParam ls ρ x + k)

theorem NormLevel.HasSub.le_eval {s : NormLevel} : ∀ {t}, s.HasSub t →
    t.eval ls ρ ≤ s.eval ls ρ
  | .const _ _, ⟨_, hn, hk, _⟩ =>
    Nat.le_trans (evalPath_mono (hk ▸ Node.const_le_eval))
      (NormLevel.eval_le.1 (Nat.le_refl _) _ _ hn)
  | .var _ _ _, ⟨_, hn, hx⟩ =>
    Nat.le_trans (evalPath_mono (Node.var_le_eval hx))
      (NormLevel.eval_le.1 (Nat.le_refl _) _ _ hn)

theorem NormLevel.lt_eval {s : NormLevel} :
    m < eval ls ρ s ↔ ∃ p n, s.get? p = some n ∧ m < evalPath ls ρ p (Node.eval ls ρ n) := by
  refine ⟨fun h => ?_, fun ⟨p, n, hn, hlt⟩ =>
    Nat.lt_of_lt_of_le hlt (NormLevel.eval_le.1 (Nat.le_refl _) _ _ hn)⟩
  refine Classical.byContradiction fun hc => ?_
  exact absurd (eval_le.2 fun p n hn => Nat.not_lt.1 fun hlt => hc ⟨p, n, hn, hlt⟩)
    (Nat.not_le.2 h)

theorem Node.lt_eval {n : Node} :
    m < Node.eval ls ρ n ↔ m < n.const ∨ ∃ v ∈ n.var, m < VarNode.eval ls ρ v := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine Classical.byContradiction fun hc => ?_
    rw [not_or] at hc; obtain ⟨h₁, h₂⟩ := hc
    refine absurd (Node.eval_le.2 ⟨Nat.not_lt.1 h₁, fun v hv => Nat.not_lt.1 fun hlt => ?_⟩)
      (Nat.not_le.2 h)
    exact h₂ ⟨v, hv, hlt⟩
  · obtain h | ⟨v, hv, h⟩ := h
    · exact Nat.lt_of_lt_of_le h Node.const_le_eval
    · exact Nat.lt_of_lt_of_le h (Node.var_le_eval hv)

theorem lt_evalPath (h : m < evalPath ls ρ p n) : allNZ ls ρ p ∧ m < n := by
  rw [evalPath] at h; split at h
  · exact ⟨‹_›, h⟩
  · exact absurd h (Nat.not_lt_zero m)

theorem evalParam_map {f : Name → Nat} (hx : x ∈ ls) : evalParam ls (ls.map f) x = f x := by
  have hv : ls.idxOf x < ls.length := List.idxOf_lt_length_iff.2 hx
  rw [evalParam_eq hv, List.getElem?_map, List.getElem?_eq_getElem hv]
  simp [List.getElem_idxOf]

theorem evalParam_not_mem (hx : x ∉ ls) : evalParam ls ρ x = 0 := by
  simp only [evalParam]
  rw [if_neg fun h => hx (List.idxOf_lt_length_iff.1 h)]

theorem evalParam_map_pos {f : Name → Nat} (h : 0 < evalParam ls (ls.map f) z) :
    z ∈ ls ∧ 0 < f z := by
  by_cases hz : z ∈ ls
  · refine ⟨hz, ?_⟩; rwa [evalParam_map hz] at h
  · rw [evalParam_not_mem hz] at h; exact absurd h (Nat.lt_irrefl 0)

theorem evalParam_map_le {f : Name → Nat} (hb : f z ≤ c) :
    evalParam ls (ls.map f) z ≤ c := by
  by_cases hz : z ∈ ls
  · rw [evalParam_map hz]; exact hb
  · rw [evalParam_not_mem hz]; exact Nat.zero_le _

theorem foldl_max_le {f : α → Nat} {m : Nat} : ∀ {l : List α} {i : Nat},
    l.foldl (fun r a => max' r (f a)) i ≤ m ↔ i ≤ m ∧ ∀ a ∈ l, f a ≤ m
  | [], _ => by simp
  | a :: l, i => by simp [foldl_max_le (l := l), Nat.max_le, and_assoc]

/-- A bound on all the constants and offsets appearing in the map. -/
def Node.bound (n : Node) : Nat := n.var.foldl (fun r v => max' r v.offset) n.const

def NormLevel.bound (s : NormLevel) : Nat := s.foldl (fun r _ n => max' r n.bound) 0

theorem NormLevel.bound_spec {s : NormLevel} (h : s.get? p = some n) :
    n.const ≤ s.bound ∧ ∀ v ∈ n.var, v.offset ≤ s.bound := by
  have hmem := Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 (Std.TreeMap.get?_eq_getElem? .. ▸ h)
  have hb : n.bound ≤ s.bound := by
    rw [bound, Std.TreeMap.foldl_eq_foldl_toList]
    exact ((foldl_max_le (f := fun pn : List Name × Node => pn.2.bound)).1
      (Nat.le_refl _)).2 _ hmem
  exact (foldl_max_le (f := fun v : VarNode => v.offset)).1 hb

/-- The separation theorem, a converse to Theorem 39: if the value of `l₁` is bounded by the
value of `l₂` under every valuation, then every sublevel of `l₁` has a syntactic dominator
among the sublevels of `l₂`. The valuation exhibiting the dominator sets every variable of
the sublevel's condition set to `1`, the sublevel's own variable (if any) to a value `N`
larger than every constant and offset of `l₂`, and everything else to `0`: only entries of
`l₂` at condition sets below the sublevel's can contribute, and only a sublevel with the
same variable can reach `N`. -/
theorem NormLevel.separation {l₁ l₂ : NormLevel}
    (hls : ∀ p n, l₁.get? p = some n → ∀ x ∈ p, x ∈ ls)
    (wf₁ : ∀ p n, l₁.get? p = some n → ∀ v ∈ n.var, v.var ∈ p)
    (h : ∀ ρ, l₁.eval ls ρ ≤ l₂.eval ls ρ) :
    ∀ t, l₁.HasSub t → ∃ t', l₂.HasSub t' ∧ t.le t' := by
  intro t ht
  match t, ht with
  | .const p k, ⟨n, hn, hk, hk0⟩ =>
    have hnz : allNZ ls (ls.map fun z => if z ∈ p then 1 else 0) p := by
      simp only [allNZ, List.all_eq_true, decide_eq_true_eq]
      intro z hz
      rw [evalParam_map (hls _ _ hn _ hz)]; simp [hz]
    have h₁ : k ≤ l₁.eval ls (ls.map fun z => if z ∈ p then 1 else 0) :=
      Nat.le_trans (by simp [Sub.eval, evalPath, hnz])
        (HasSub.le_eval (t := .const p k) ⟨n, hn, hk, hk0⟩)
    have h₂ := NormLevel.lt_eval.1 (Nat.lt_of_lt_of_le (by omega : k - 1 < k)
      (Nat.le_trans h₁ (h _)))
    obtain ⟨q, m, hq, hlt⟩ := h₂
    obtain ⟨hnzq, hlt⟩ := lt_evalPath hlt
    have hsub : ∀ z ∈ q, z ∈ p := by
      intro z hz
      simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnzq
      have := (evalParam_map_pos (hnzq z hz)).2
      split at this
      · assumption
      · exact absurd this (Nat.lt_irrefl 0)
    obtain hc | ⟨v, hv, hvlt⟩ := Node.lt_eval.1 hlt
    · exact ⟨.const q m.const, ⟨m, hq, rfl, by omega⟩, hsub, by omega⟩
    · refine ⟨.var q v.var v.offset, ⟨m, hq, hv⟩, hsub, ?_⟩
      have hev : evalParam ls (ls.map fun z => if z ∈ p then 1 else 0) v.var ≤ 1 :=
        evalParam_map_le (by split <;> omega)
      simp only [VarNode.eval] at hvlt
      omega
  | .var p x k, ⟨n, hn, hx⟩ =>
    have hxp : x ∈ p := wf₁ _ _ hn _ hx
    have hxls : x ∈ ls := hls _ _ hn _ hxp
    have hnz : allNZ ls (ls.map fun z =>
        if z = x then l₂.bound + k + 2 else if z ∈ p then 1 else 0) p := by
      simp only [allNZ, List.all_eq_true, decide_eq_true_eq]
      intro z hz
      simp only [evalParam_map (hls _ _ hn _ hz)]
      split
      · omega
      · omega
    have h₁ : l₂.bound + k + 2 + k ≤ l₁.eval ls (ls.map fun z =>
        if z = x then l₂.bound + k + 2 else if z ∈ p then 1 else 0) := by
      refine Nat.le_trans ?_ (HasSub.le_eval (t := .var p x k) ⟨n, hn, hx⟩)
      simp [Sub.eval, evalPath, hnz, evalParam_map hxls]
    obtain ⟨q, m, hq, hlt⟩ := NormLevel.lt_eval.1
      (Nat.lt_of_lt_of_le (by omega : l₂.bound + k + 2 + k - 1 < l₂.bound + k + 2 + k)
        (Nat.le_trans h₁ (h _)))
    obtain ⟨hnzq, hlt⟩ := lt_evalPath hlt
    have hsub : ∀ z ∈ q, z ∈ p := by
      intro z hz
      simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnzq
      have := (evalParam_map_pos (hnzq z hz)).2
      split at this
      · rename_i hz'; subst hz'; exact hxp
      · split at this
        · assumption
        · exact absurd this (Nat.lt_irrefl 0)
    obtain hc | ⟨v, hv, hvlt⟩ := Node.lt_eval.1 hlt
    · exact absurd hc (by have := (bound_spec hq).1; omega)
    · by_cases hvx : v.var = x
      · refine ⟨.var q x v.offset, ⟨m, hq, by rw [← hvx]; exact hv⟩, hsub, rfl, ?_⟩
        simp [VarNode.eval, hvx, evalParam_map hxls] at hvlt
        omega
      · have hoff := (bound_spec hq).2 _ hv
        have hev : evalParam ls (ls.map fun z =>
            if z = x then l₂.bound + k + 2 else if z ∈ p then 1 else 0) v.var ≤ 1 :=
          evalParam_map_le (by rw [if_neg hvx]; split <;> omega)
        simp only [VarNode.eval] at hvlt
        exact absurd hvlt (by omega)

private theorem name_lt_ne {a b : Name} (h : compare a b = .lt) : a ≠ b := by
  rintro rfl; rw [Std.ReflOrd.compare_self] at h; cases h

/-- Exactness of `subsumeVars` on sorted lists: a surviving variable has no dominator
in the subtracted list. -/
theorem subsumeVars_complete {x y : VarNode} : ∀ {vs₁ vs₂ : List VarNode},
    VarsSorted vs₁ → VarsSorted vs₂ → x ∈ subsumeVars vs₁ vs₂ → y ∈ vs₂ →
    y.var = x.var → x.offset ≤ y.offset → False
  | [], _, _, _, hx, _ => by simp [subsumeVars] at hx
  | _ :: _, [], _, _, _, hy => nomatch hy
  | a :: vs₁, b :: vs₂, h₁, h₂, hx, hy => by
    intro e hle
    simp only [subsumeVars] at hx
    split at hx <;> rename_i hab
    · rcases List.mem_cons.1 hx with rfl | hx'
      · rcases List.mem_cons.1 hy with rfl | hy'
        · exact name_lt_ne hab e.symm
        · exact name_lt_ne (Std.TransCmp.lt_trans hab (h₂.head _ hy')) e.symm
      · exact subsumeVars_complete h₁.of_cons h₂ hx' hy e hle
    · have eab : a.var = b.var := eq_of_beq (Std.LawfulBEqCmp.compare_eq_iff_beq.1 hab)
      split at hx <;> rename_i hoff
      · rcases List.mem_cons.1 hy with rfl | hy'
        · exact name_lt_ne (h₁.head _ (subsumeVars_subset hx)) (eab.trans e)
        · exact subsumeVars_complete h₁.of_cons h₂.of_cons hx hy' e hle
      · rcases List.mem_cons.1 hx with rfl | hx'
        · rcases List.mem_cons.1 hy with rfl | hy'
          · exact hoff hle
          · exact name_lt_ne (h₂.head _ hy') (e.trans eab).symm
        · rcases List.mem_cons.1 hy with rfl | hy'
          · exact name_lt_ne (h₁.head _ (subsumeVars_subset hx')) (eab.trans e)
          · exact subsumeVars_complete h₁.of_cons h₂.of_cons hx' hy' e hle
    · rcases List.mem_cons.1 hy with rfl | hy'
      · have hbx : compare y.var x.var = .lt := by
          have hba := Std.OrientedCmp.lt_of_gt hab
          rcases List.mem_cons.1 (subsumeVars_subset hx) with rfl | hxv
          · exact hba
          · exact Std.TransCmp.lt_trans hba (h₁.head _ hxv)
        exact name_lt_ne hbx e
      · exact subsumeVars_complete h₁ h₂.of_cons hx hy' e hle

theorem le_foldl_max_self {vs : List VarNode} : ∀ {n : Nat}, n ≤ vs.foldl (·.max ·.offset) n := by
  induction vs with | nil => exact Nat.le_refl _ | cons a vs ih
  exact fun {n} => Nat.le_trans (Nat.le_max_left _ _) ih

theorem foldl_max_ge {vs : List VarNode} (hy : y ∈ vs) :
    ∀ {n : Nat}, y.offset ≤ vs.foldl (·.max ·.offset) n := by
  induction vs with | nil => cases hy | cons a vs ih
  rcases List.mem_cons.1 hy with rfl | hy'
  · exact fun {n} => Nat.le_trans (Nat.le_max_right _ _) le_foldl_max_self
  · exact fun {n} => ih hy'

/-- Exactness of the constant part of `subsumeBy`: a dominated constant is dropped. -/
theorem Node.subsumeBy_const_complete {same : Bool} {n₁ n₂ : Node}
    (h : (same = false ∧ n₁.const ≤ n₂.const) ∨ ∃ y ∈ n₂.var, n₁.const ≤ y.offset + 1) :
    (n₁.subsumeBy same n₂).const = 0 := by
  rw [Node.subsumeBy_const_eq]
  split <;> [rename_i hc; rfl]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
  obtain hc | ⟨hc1, hc2⟩ := hc
  · exact hc
  obtain ⟨rfl, hle⟩ | ⟨y, hy, hle⟩ := h
  · rcases hc1 with hc1 | hc1
    · cases hc1
    · omega
  · rcases hc2 with hc2 | hc2
    · rw [hc2] at hy; cases hy
    · have := foldl_max_ge hy (n := 0); omega

theorem Node.subsumeBy_var_sublist {same : Bool} {n₁ n₂ : Node} :
    List.Sublist (n₁.subsumeBy same n₂).var n₁.var := by
  rw [Node.subsumeBy_var_eq]; split
  · exact List.Sublist.refl _
  · exact subsumeVars_sublist ..

/-- Exactness of the variable part of `subsumeBy` at a different key: a dominated variable
is dropped. -/
theorem Node.subsumeBy_var_complete {n₁ n₂ : Node} (h₁ : VarsSorted n₁.var)
    (h₂ : VarsSorted n₂.var) (hx : x ∈ (n₁.subsumeBy false n₂).var) (hy : y ∈ n₂.var)
    (e : y.var = x.var) (hle : x.offset ≤ y.offset) : False := by
  rw [Node.subsumeBy_var_eq] at hx
  split at hx <;> rename_i hc
  · simp only [Bool.false_or, List.isEmpty_iff] at hc
    rw [hc] at hy; cases hy
  · exact subsumeVars_complete h₁ h₂ hx hy e hle

/-- Completeness of the discharging fold in `NormLevel.le`: if every sublevel of `n₁` has a
dominator among the entries of `l` at a subkey of `p₁`, the fold discharges everything and
returns `none`. -/
theorem NormLevel.le_fold_complete {p₁ : List Name} :
    ∀ (l : List (List Name × Node)) (n₁ : Node), VarsSorted n₁.var →
    (∀ pn ∈ l, VarsSorted pn.2.var) → n₁.isEmpty = false →
    (n₁.const ≠ 0 → ∃ pn ∈ l, subset compare pn.1 p₁ ∧
      (n₁.const ≤ pn.2.const ∨ ∃ y ∈ pn.2.var, n₁.const ≤ y.offset + 1)) →
    (∀ x ∈ n₁.var, ∃ pn ∈ l, subset compare pn.1 p₁ ∧
      ∃ y ∈ pn.2.var, y.var = x.var ∧ x.offset ≤ y.offset) →
    List.foldlM (m := Option) (fun n pn =>
      if subset compare pn.1 p₁ then
        if (n.subsumeBy false pn.2).isEmpty then none else some (n.subsumeBy false pn.2)
      else some n) n₁ l = none
  | [], n₁, _, _, hne, hconst, hvar => by
    rw [Node.isEmpty, Bool.and_eq_false_iff] at hne
    obtain h0 | hv := hne
    · obtain ⟨_, h, -⟩ := hconst (by simpa using h0)
      cases h
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (by simpa using hv)
      obtain ⟨_, h, -⟩ := hvar x hx
      cases h
  | pn :: l, n₁, hvs₁, hvsl, hne, hconst, hvar => by
    simp only [List.foldlM_cons]
    by_cases hs : subset compare pn.1 p₁
    · rw [if_pos hs]
      by_cases he : (n₁.subsumeBy false pn.2).isEmpty
      · rw [if_pos he]; rfl
      · rw [if_neg he]
        show List.foldlM _ _ l = none
        refine le_fold_complete l _ (hvs₁.sublist Node.subsumeBy_var_sublist)
          (fun pn h => hvsl _ (.tail _ h)) (by simpa using he) ?_ ?_
        · intro h0
          have hc : (n₁.subsumeBy false pn.2).const = n₁.const :=
            (Node.subsumeBy_const_cases ..).resolve_right h0
          obtain ⟨pn', hpn', hsub', hdom'⟩ := hconst (hc ▸ h0)
          rcases List.mem_cons.1 hpn' with rfl | hpn'
          · exact absurd (Node.subsumeBy_const_complete
              (hdom'.imp (fun h => ⟨rfl, h⟩) id)) h0
          · exact ⟨pn', hpn', hsub', hc ▸ hdom'⟩
        · intro x hx
          obtain ⟨pn', hpn', hsub', y, hy, e, hle⟩ := hvar x (Node.subsumeBy_var_subset hx)
          rcases List.mem_cons.1 hpn' with rfl | hpn'
          · exact (Node.subsumeBy_var_complete hvs₁ (hvsl _ (.head _)) hx hy e hle).elim
          · exact ⟨pn', hpn', hsub', y, hy, e, hle⟩
    · rw [if_neg hs]
      show List.foldlM _ _ l = none
      refine le_fold_complete l n₁ hvs₁ (fun pn h => hvsl _ (.tail _ h)) hne ?_ ?_
      · intro h0
        obtain ⟨pn', hpn', hsub', hdom'⟩ := hconst h0
        rcases List.mem_cons.1 hpn' with rfl | hpn'
        · exact absurd hsub' hs
        · exact ⟨pn', hpn', hsub', hdom'⟩
      · intro x hx
        obtain ⟨pn', hpn', hsub', hy⟩ := hvar x hx
        rcases List.mem_cons.1 hpn' with rfl | hpn'
        · exact absurd hsub' hs
        · exact ⟨pn', hpn', hsub', hy⟩

/-- Completeness of `NormLevel.le`: per-sublevel domination implies acceptance. -/
theorem NormLevel.le_complete {l₁ l₂ : NormLevel}
    (hvs₁ : l₁.SortedVars) (hvs₂ : l₂.SortedVars)
    (hne : ∀ p n, l₁.get? p = some n → n.isEmpty = false)
    (hsort₁ : ∀ p n, l₁.get? p = some n → Sorted p)
    (hsort₂ : ∀ p n, l₂.get? p = some n → Sorted p)
    (hdom : ∀ t, l₁.HasSub t → ∃ t', l₂.HasSub t' ∧ t.le t') :
    l₁.le l₂ := by
  rw [NormLevel.le, Std.TreeMap.all_eq_all_toList, List.all_eq_true]
  rintro ⟨p₁, n₁⟩ hmem
  have h₁ := Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hmem
  simp only [Std.TreeMap.foldlM_eq_foldlM_toList, Option.isNone_iff_eq_none]
  have hmem₂ : ∀ q m, l₂.get? q = some m → (q, m) ∈ l₂.toList := fun q m h =>
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 (Std.TreeMap.get?_eq_getElem? .. ▸ h)
  refine le_fold_complete l₂.toList n₁ (hvs₁ _ _ h₁)
    (fun pn h => hvs₂ _ _ <| Std.TreeMap.get?_eq_getElem? .. ▸
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h) (hne _ _ h₁) (fun h0 => ?_) (fun x hx => ?_)
  · obtain ⟨t', ht', hle⟩ := hdom (.const p₁ n₁.const) ⟨n₁, h₁, rfl, h0⟩
    match t', ht', hle with
    | .const q _, ⟨m, hq, hc, _⟩, ⟨hsub, hle⟩ =>
      exact ⟨(q, m), hmem₂ _ _ hq,
        subset_of_sorted (hsort₂ _ _ hq) (hsort₁ _ _ h₁) hsub, .inl (hc ▸ hle)⟩
    | .var q yv yk, ⟨m, hq, hyk⟩, ⟨hsub, hle⟩ =>
      exact ⟨(q, m), hmem₂ _ _ hq,
        subset_of_sorted (hsort₂ _ _ hq) (hsort₁ _ _ h₁) hsub, .inr ⟨⟨yv, yk⟩, hyk, hle⟩⟩
  · obtain ⟨t', ht', hle⟩ := hdom (.var p₁ x.var x.offset) ⟨n₁, h₁, hx⟩
    match t', ht', hle with
    | .const _ _, _, hle => exact hle.elim
    | .var q yv yk, ⟨m, hq, hyk⟩, ⟨hsub, hev, hle⟩ =>
      exact ⟨(q, m), hmem₂ _ _ hq,
        subset_of_sorted (hsort₂ _ _ hq) (hsort₁ _ _ h₁) hsub, ⟨yv, yk⟩, hyk, hev.symm, hle⟩

/-- The sublevels of a single node keyed at `p`. -/
def Node.HasSub (p : List Name) (n : Node) : Sub → Prop
  | .const q k => p = q ∧ n.const = k ∧ k ≠ 0
  | .var q x k => p = q ∧ ⟨x, k⟩ ∈ n.var

theorem NormLevel.hasSub_iff {s : NormLevel} {t} :
    s.HasSub t ↔ ∃ p n, s.get? p = some n ∧ Node.HasSub p n t := by
  match t with
  | .const p k =>
    constructor
    · rintro ⟨n, hn, hk, hk0⟩; exact ⟨p, n, hn, rfl, hk, hk0⟩
    · rintro ⟨q, n, hn, rfl, hk, hk0⟩; exact ⟨n, hn, hk, hk0⟩
  | .var p x k =>
    constructor
    · rintro ⟨n, hn, hx⟩; exact ⟨p, n, hn, rfl, hx⟩
    · rintro ⟨q, n, hn, rfl, hx⟩; exact ⟨n, hn, hx⟩

theorem Node.subsume_hasSub : ∀ {t}, Node.HasSub p₁ (Node.subsume p₁ n p₂ n₂) t →
    Node.HasSub p₁ n t
  | .const _ k, ⟨rfl, hck, hk0⟩ => by
    refine ⟨rfl, ?_, hk0⟩
    obtain h | h := Node.subsume_const_cases p₁ n p₂ n₂
    · rw [← h]; exact hck
    · rw [h] at hck; exact absurd hck.symm hk0
  | .var _ _ _, ⟨rfl, hxk⟩ => ⟨rfl, Node.subsume_var_subset hxk⟩

theorem NormLevel.minimize_hasSub {acc : NormLevel} {t}
    (h : Node.HasSub p₁ (acc.minimize p₁ n₁) t) : Node.HasSub p₁ n₁ t := by
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList] at h
  generalize acc.toList = l at h
  induction l generalizing n₁ with
  | nil => exact h
  | cons a l ih => exact Node.subsume_hasSub (ih h)

/-- A `subsumption` step only removes sublevels. -/
theorem NormLevel.subsumption_step_hasSub {acc : NormLevel} {p₁ : List Name} {n₁ : Node}
    (h₁ : acc.get? p₁ = some n₁) {t}
    (h : NormLevel.HasSub (if (acc.minimize p₁ n₁).isEmpty then acc.erase p₁
      else acc.insert p₁ (acc.minimize p₁ n₁)) t) : acc.HasSub t := by
  rw [hasSub_iff] at h ⊢
  obtain ⟨p, n, hp, hn⟩ := h
  rw [subsumption_step_get?] at hp
  split at hp <;> rename_i hpe
  · split at hp <;> [cases hp; skip]
    cases hp; subst hpe
    exact ⟨p₁, n₁, h₁, minimize_hasSub hn⟩
  · exact ⟨p, n, hp, hn⟩

/-- Exactness of minimization, fold form: a sublevel surviving the subtraction of every entry
in `l` is not (strictly) dominated by any of their sublevels — domination forces equality. -/
theorem NormLevel.minimize_exact_aux {acc : NormLevel} {p₁ : List Name} {n₁ : Node}
    (hsort : ∀ p n, acc.get? p = some n → Sorted p) (hvsa : acc.SortedVars)
    (h₁ : acc.get? p₁ = some n₁) (hs₁ : Sorted p₁) (hvs₁ : VarsSorted n₁.var) :
    ∀ (l : List (List Name × Node)) (n : Node),
      (∀ pn ∈ l, acc.get? pn.1 = some pn.2) →
      (∀ x ∈ n.var, x ∈ n₁.var) → (n.const ≠ 0 → n.const = n₁.const) → VarsSorted n.var →
      ∀ t, Node.HasSub p₁ (l.foldl (fun n pn => Node.subsume p₁ n pn.1 pn.2) n) t →
      Node.HasSub p₁ n t ∧
        ∀ pn ∈ l, ∀ t', Node.HasSub pn.1 pn.2 t' → t.le t' → t = t'
  | [], _, _, _, _, _, _, ht => ⟨ht, fun _ h => nomatch h⟩
  | (p₂, n₂) :: l, n, hl, hnvar, hnconst, hvs, t, ht => by
    simp only [List.foldl_cons] at ht
    have h₂ : acc.get? p₂ = some n₂ := hl _ (.head _)
    have hvs₂ : VarsSorted n₂.var := hvsa _ _ h₂
    have hs₂ : Sorted p₂ := hsort _ _ h₂
    obtain ⟨ht', hrest⟩ := minimize_exact_aux hsort hvsa h₁ hs₁ hvs₁ l
      (Node.subsume p₁ n p₂ n₂) (fun pn h => hl _ (.tail _ h))
      (fun x hx => hnvar _ (Node.subsume_var_subset hx))
      (fun h0 => by
        obtain hc | hc := Node.subsume_const_cases p₁ n p₂ n₂
        · rw [hc]; exact hnconst (hc ▸ h0)
        · exact absurd hc h0)
      (hvs.sublist Node.subsume_var_sublist) t ht
    refine ⟨Node.subsume_hasSub ht', ?_⟩
    rintro pn hpn t' ht'' hle
    rcases List.mem_cons.1 hpn with rfl | hpn
    · obtain ⟨q, k⟩ | ⟨q, x, k⟩ := t <;> obtain ⟨q', k'⟩ | ⟨q', y, k'⟩ := t'
      · -- const dominated by const
        obtain ⟨rfl, hck, hk0⟩ := ht'
        obtain ⟨rfl, hck', hk0'⟩ := ht''
        obtain ⟨hsub, hlek⟩ := hle
        have hgate : subset compare p₂ p₁ := subset_of_sorted hs₂ hs₁ hsub
        have hsu : Node.subsume p₁ n p₂ n₂ = n.subsumeBy (p₁.length == p₂.length) n₂ := by
          rw [Node.subsume, if_pos hgate]
        by_cases hlen : p₁.length = p₂.length
        · have hqq : p₂ = p₁ := subset_eq hgate hlen.symm
          have hn₂ : n₂ = n₁ := by
            rw [hqq] at h₂; cases h₂.symm.trans h₁; rfl
          have hkc : n.const = k := by
            obtain hc | hc := Node.subsume_const_cases p₁ n p₂ n₂
            · rw [← hc]; exact hck
            · rw [hc] at hck; exact absurd hck.symm hk0
          have hne0 : n.const ≠ 0 := fun h0 => hk0 (hkc.symm.trans h0)
          rw [hqq, show k = k' from by rw [← hck', hn₂, ← hnconst hne0, hkc]]
        · have hbeq : (p₁.length == p₂.length) = false := by simpa using hlen
          rw [hsu, hbeq] at hck
          have hkc : n.const = k := by
            obtain hc | hc := Node.subsumeBy_const_cases (same := false) n n₂
            · rw [← hc]; exact hck
            · rw [hc] at hck; exact absurd hck.symm hk0
          refine absurd hck ?_
          rw [Node.subsumeBy_const_complete (n₁ := n) (n₂ := n₂)
            (.inl ⟨rfl, by rw [hkc, hck']; exact hlek⟩)]
          exact fun h => hk0 h.symm
      · -- const dominated by a variable
        obtain ⟨rfl, hck, hk0⟩ := ht'
        obtain ⟨rfl, hyk⟩ := ht''
        obtain ⟨hsub, hlek⟩ := hle
        have hgate : subset compare p₂ p₁ := subset_of_sorted hs₂ hs₁ hsub
        have hsu : Node.subsume p₁ n p₂ n₂ = n.subsumeBy (p₁.length == p₂.length) n₂ := by
          rw [Node.subsume, if_pos hgate]
        rw [hsu] at hck
        have hkc : n.const = k := by
          obtain hc | hc := Node.subsumeBy_const_cases (same := p₁.length == p₂.length) n n₂
          · rw [← hc]; exact hck
          · rw [hc] at hck; exact absurd hck.symm hk0
        refine absurd hck ?_
        rw [Node.subsumeBy_const_complete (n₁ := n) (n₂ := n₂)
          (.inr ⟨⟨y, k'⟩, hyk, by rw [hkc]; exact hlek⟩)]
        exact fun h => hk0 h.symm
      · exact hle.elim
      · -- variable dominated by a variable
        obtain ⟨rfl, hxk⟩ := ht'
        obtain ⟨rfl, hyk⟩ := ht''
        obtain ⟨hsub, rfl, hlek⟩ := hle
        have hgate : subset compare p₂ p₁ := subset_of_sorted hs₂ hs₁ hsub
        have hsu : Node.subsume p₁ n p₂ n₂ = n.subsumeBy (p₁.length == p₂.length) n₂ := by
          rw [Node.subsume, if_pos hgate]
        by_cases hlen : p₁.length = p₂.length
        · have hqq : p₂ = p₁ := subset_eq hgate hlen.symm
          have hn₂ : n₂ = n₁ := by
            rw [hqq] at h₂; cases h₂.symm.trans h₁; rfl
          have hk : (⟨x, k⟩ : VarNode) = ⟨x, k'⟩ :=
            hvs₁.eq_of_var_eq (hnvar _ (Node.subsume_var_subset hxk)) (hn₂ ▸ hyk) rfl
          rw [hqq, show k = k' from congrArg VarNode.offset hk]
        · have hbeq : (p₁.length == p₂.length) = false := by simpa using hlen
          rw [hsu, hbeq] at hxk
          exact (Node.subsumeBy_var_complete hvs hvs₂ hxk hyk rfl hlek).elim
    · exact hrest _ hpn _ ht'' hle

theorem NormLevel.minimize_exact {acc : NormLevel} {p₁ : List Name} {n₁ : Node}
    (hsort : ∀ p n, acc.get? p = some n → Sorted p) (hvsa : acc.SortedVars)
    (h₁ : acc.get? p₁ = some n₁) :
    ∀ t t', Node.HasSub p₁ (acc.minimize p₁ n₁) t → acc.HasSub t' → t.le t' → t = t' := by
  intro t t' ht ht' hle
  rw [minimize, Std.TreeMap.foldl_eq_foldl_toList] at ht
  have hmem pn (h : pn ∈ acc.toList) : acc.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  obtain ⟨-, hexact⟩ := minimize_exact_aux hsort hvsa h₁ (hsort _ _ h₁) (hvsa _ _ h₁)
    acc.toList n₁ hmem (fun _ => id) (fun _ => rfl) (hvsa _ _ h₁) t ht
  obtain ⟨p₂, n₂, hp₂, hn₂⟩ := hasSub_iff.1 ht'
  exact hexact (p₂, n₂) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.2
    (Std.TreeMap.get?_eq_getElem? .. ▸ hp₂)) _ hn₂ hle

/-- A normal form is reduced when no sublevel is dominated by another: domination between
recorded sublevels forces them to be the same sublevel. -/
def NormLevel.Reduced (s : NormLevel) : Prop :=
  ∀ t t', s.HasSub t → s.HasSub t' → t.le t' → t = t'

/-- `subsumption` produces a reduced map: every entry is minimized against the (current)
whole map, minimization removes exactly the dominated sublevels, and later steps only
shrink the map, which cannot introduce new domination. -/
theorem NormLevel.subsumption_reduced {s : NormLevel}
    (hsort : ∀ p n, s.get? p = some n → Sorted p) (hvsa : s.SortedVars) :
    s.subsumption.Reduced := by
  have hmem pn (h : pn ∈ s.toList) : s.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  have nd : (s.toList.map Prod.fst).Nodup := by simpa using Std.TreeMap.nodup_keys (t := s)
  rw [Reduced, subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (l.map Prod.fst).Nodup →
      (∀ pn ∈ l, acc.get? pn.1 = some pn.2) →
      (∀ p n, acc.get? p = some n → Sorted p) → acc.SortedVars →
      (∀ p n, acc.get? p = some n → p ∉ l.map Prod.fst →
        ∀ t t', Node.HasSub p n t → acc.HasSub t' → t.le t' → t = t') →
      ∀ t t', (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).HasSub t →
      (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).HasSub t' →
      t.le t' → t = t' from
    this _ _ nd hmem hsort hvsa fun p n hp hnp => absurd
      (List.mem_map_of_mem (f := Prod.fst) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.2
        (Std.TreeMap.get?_eq_getElem? .. ▸ hp))) hnp
  clear hmem nd hsort hvsa; intro l
  induction l with
  | nil =>
    intro acc _ _ _ _ hred t t' ht ht' hle
    obtain ⟨p, n, hp, hnt⟩ := hasSub_iff.1 ht
    exact hred p n hp (by simp) t t' hnt ht' hle
  | cons pn l ih =>
    obtain ⟨p₂, n₂⟩ := pn
    intro acc nd hl hsorta hvsacc hred
    simp only [List.map_cons, List.nodup_cons] at nd
    have h₂ : acc.get? p₂ = some n₂ := hl _ (.head _)
    simp only [List.foldl_cons]
    have hstep := subsumption_step_get? acc n₂ p₂
    refine ih _ nd.2 (fun pn' h => ?_) (fun p n h => ?_) (fun p n h => ?_)
      (fun p n hp hnp t t' hnt ht' hle => ?_)
    · have hne : p₂ ≠ pn'.1 := fun e => nd.1 (e ▸ List.mem_map_of_mem (f := Prod.fst) h)
      rw [hstep, if_neg hne]
      exact hl _ (.tail _ h)
    · rw [hstep] at h; split at h <;> rename_i hpe
      · split at h <;> [cases h; skip]
        cases h; exact hpe ▸ hsorta _ _ h₂
      · exact hsorta _ _ h
    · rw [hstep] at h; split at h <;> rename_i hpe
      · split at h <;> [cases h; skip]
        cases h
        exact (hvsacc _ _ h₂).sublist minimize_var_sublist
      · exact hvsacc _ _ h
    · rw [hstep] at hp; split at hp <;> rename_i hpe
      · split at hp <;> [cases hp; skip]
        cases hp; subst hpe
        exact minimize_exact hsorta hvsacc h₂ t t' hnt (subsumption_step_hasSub h₂ ht') hle
      · refine hred p n hp ?_ t t' hnt (subsumption_step_hasSub h₂ ht') hle
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨fun e => hpe e.symm, hnp⟩

theorem normalize_reduced : (normalize u).Reduced := by
  refine NormLevel.subsumption_reduced ?_ (normalizeAux_sortedVars fun _ _ => by simp)
  exact fun p n h => (normalizeAux_wf (by simp) (by simp [NormLevel.WF]) p n h).2.2

/-! Canonicity: two reduced normal forms with the same semantics have the same sublevels,
and hence are equal maps. -/

instance : LawfulBEq Node where
  rfl {a} := by cases a <;> simp! +instances [instBEqNode]
  eq_of_beq {a b} h := by
    cases a; cases b
    simp! +instances [instBEqNode] at h
    simp [h.1, h.2]

theorem VarsSorted.eq_of_mem_iff : ∀ {l₁ l₂ : List VarNode}, VarsSorted l₁ → VarsSorted l₂ →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => nomatch (h _).2 (.head _)
  | _ :: _, [], _, _, h => nomatch (h _).1 (.head _)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    cases show a = b by
      rcases List.mem_cons.1 ((h a).1 (.head _)) with rfl | ha <;> [rfl; skip]
      rcases List.mem_cons.1 ((h b).2 (.head _)) with rfl | hb <;> [rfl; skip]
      exact absurd (h₂.head _ ha) (by rw [Std.OrientedCmp.gt_of_lt (h₁.head _ hb)]; simp)
    refine congrArg (a :: ·) (VarsSorted.eq_of_mem_iff h₁.of_cons h₂.of_cons
      fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.1 ((h x).1 (.tail _ hx)) with rfl | hx'
      · exact absurd (h₁.head _ hx) (by rw [Std.ReflOrd.compare_self]; simp)
      · exact hx'
    · rcases List.mem_cons.1 ((h x).2 (.tail _ hx)) with rfl | hx'
      · exact absurd (h₂.head _ hx) (by rw [Std.ReflOrd.compare_self]; simp)
      · exact hx'

theorem NormLevel.HasSub.path_sorted {s : NormLevel}
    (hsort : ∀ p n, s.get? p = some n → Sorted p) : ∀ {t}, s.HasSub t → Sorted t.path
  | .const _ _, ⟨_, hn, _⟩ => hsort _ _ hn
  | .var _ _ _, ⟨_, hn, _⟩ => hsort _ _ hn

/-- In reduced maps, mutual per-sublevel domination pins the sublevels to be equal: the
dominator of a sublevel is itself dominated by a sublevel of the first map, which by
reducedness is the sublevel we started from, and antisymmetry finishes. -/
theorem NormLevel.Reduced.hasSub_iff_hasSub {A B : NormLevel}
    (rA : A.Reduced) (rB : B.Reduced)
    (sortA : ∀ p n, A.get? p = some n → Sorted p)
    (sortB : ∀ p n, B.get? p = some n → Sorted p)
    (hAB : ∀ t, A.HasSub t → ∃ t', B.HasSub t' ∧ t.le t')
    (hBA : ∀ t, B.HasSub t → ∃ t', A.HasSub t' ∧ t.le t') :
    ∀ t, A.HasSub t ↔ B.HasSub t := by
  suffices ∀ {A B : NormLevel}, A.Reduced →
      (∀ p n, A.get? p = some n → Sorted p) → (∀ p n, B.get? p = some n → Sorted p) →
      (∀ t, A.HasSub t → ∃ t', B.HasSub t' ∧ t.le t') →
      (∀ t, B.HasSub t → ∃ t', A.HasSub t' ∧ t.le t') →
      ∀ t, A.HasSub t → B.HasSub t from
    fun t => ⟨this rA sortA sortB hAB hBA t, this rB sortB sortA hBA hAB t⟩
  clear rA rB sortA sortB hAB hBA
  intro A B rA sortA sortB hAB hBA t ht
  obtain ⟨t', ht', hle⟩ := hAB t ht
  obtain ⟨t'', ht'', hle'⟩ := hBA t' ht'
  cases rA t t'' ht ht'' (hle.trans hle')
  exact (hle.antisymm (HasSub.path_sorted sortA ht) (HasSub.path_sorted sortB ht') hle').symm ▸ ht'

/-- Two reduced normal forms with the same sublevels are equal as `NormLevel`s. -/
theorem NormLevel.eq_of_hasSub_iff {A B : NormLevel}
    (hvsA : A.SortedVars) (hvsB : B.SortedVars)
    (hneA : ∀ p n, A.get? p = some n → n.isEmpty = false)
    (hneB : ∀ p n, B.get? p = some n → n.isEmpty = false)
    (h : ∀ t, A.HasSub t ↔ B.HasSub t) : A == B := by
  suffices ∀ {A B : NormLevel}, A.SortedVars → B.SortedVars →
      (∀ p n, A.get? p = some n → n.isEmpty = false) →
      (∀ t, A.HasSub t ↔ B.HasSub t) →
      ∀ p n, A.get? p = some n → B.get? p = some n by
    have h1 := @this A B hvsA hvsB hneA h
    have h2 := @this B A hvsB hvsA hneB fun t => (h t).symm
    simp +instances only [instBEqNormLevel, Std.TreeMap.all_eq_all_toList,
      Bool.and_eq_true, List.all_eq_true]
    constructor <;> rintro ⟨p, n⟩ hpn
    · have := h1 p n (Std.TreeMap.get?_eq_getElem? .. ▸
        Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hpn)
      rw [Std.TreeMap.get?_eq_getElem?] at this
      simp [this]
    · have := h2 p n (Std.TreeMap.get?_eq_getElem? .. ▸
        Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hpn)
      rw [Std.TreeMap.get?_eq_getElem?] at this
      simp [this]
  clear hvsA hvsB hneA hneB h
  intro A B hvsA hvsB hneA h p n hp
  have hne := hneA _ _ hp
  rw [Node.isEmpty, Bool.and_eq_false_iff] at hne
  have hBp : ∃ m, B.get? p = some m := by
    obtain h0 | hv := hne
    · obtain ⟨m, hm, -⟩ := (h (.const p n.const)).1 ⟨n, hp, rfl, by simpa using h0⟩
      exact ⟨m, hm⟩
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (by simpa using hv)
      obtain ⟨m, hm, -⟩ := (h (.var p x.var x.offset)).1 ⟨n, hp, hx⟩
      exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := hBp
  have hconst : n.const = m.const := by
    by_cases h0 : n.const = 0
    · by_cases h0' : m.const = 0
      · rw [h0, h0']
      · obtain ⟨n', hn', hc, -⟩ := (h (.const p m.const)).2 ⟨m, hm, rfl, h0'⟩
        cases hn'.symm.trans hp
        exact absurd (h0 ▸ hc).symm h0'
    · obtain ⟨m', hm', hc, -⟩ := (h (.const p n.const)).1 ⟨n, hp, rfl, h0⟩
      cases hm'.symm.trans hm
      exact hc.symm
  have hvar : n.var = m.var := by
    refine VarsSorted.eq_of_mem_iff (hvsA _ _ hp) (hvsB _ _ hm)
      fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨m', hm', hx'⟩ := (h (.var p x.var x.offset)).1 ⟨n, hp, hx⟩
      cases hm'.symm.trans hm
      exact hx'
    · obtain ⟨n', hn', hx'⟩ := (h (.var p x.var x.offset)).2 ⟨m, hm, hx⟩
      cases hn'.symm.trans hp
      exact hx'
  obtain ⟨nc, nv⟩ := n
  obtain ⟨mc, mv⟩ := m
  cases hconst; cases hvar
  exact hm

/-- Semantically equal levels have `BEq`-equal normal forms. -/
theorem normalize_complete (hu : VLevel.ofLevel ls u = some u')
    (hv : VLevel.ofLevel ls v = some v') : normalize u == normalize v ↔ u' ≈ v' := by
  refine .trans ⟨fun h ls => ?_, fun h => ?_⟩ VLevel.equiv_def.symm
  · rw [← normalize_eval hu, NormLevel.eval_congr h, normalize_eval hv]
  have h₁ : ∀ ρ, (normalize u).eval ls ρ ≤ (normalize v).eval ls ρ := fun ρ => by
    rw [normalize_eval hu, normalize_eval hv, h ρ]; exact Nat.le_refl _
  have h₂ : ∀ ρ, (normalize v).eval ls ρ ≤ (normalize u).eval ls ρ := fun ρ => by
    rw [normalize_eval hu, normalize_eval hv, h ρ]; exact Nat.le_refl _
  exact NormLevel.eq_of_hasSub_iff normalize_sortedVars normalize_sortedVars
    normalize_nonempty normalize_nonempty
    (NormLevel.Reduced.hasSub_iff_hasSub normalize_reduced normalize_reduced
      normalize_sorted normalize_sorted
      (NormLevel.separation (normalize_keys hu) normalize_vars h₁)
      (NormLevel.separation (normalize_keys hv) normalize_vars h₂))

/-! `BEq`-equal maps have equal `toList`s, and the reconstruction depends on the map only
through `toList`, so equal normal forms reify to syntactically equal levels. (`TreeMap`
equality itself does not follow from `==`: the internal tree shape depends on insertion
order.) -/

private theorem listName_compare_self {p : List Name} : compare p p = .eq :=
  Std.LawfulBEqCmp.compare_eq_iff_beq.2 (by simp)

theorem sorted_pairs_eq : ∀ {l₁ l₂ : List (List Name × Node)},
    l₁.Pairwise (compare ·.1 ·.1 = .lt) → l₂.Pairwise (compare ·.1 ·.1 = .lt) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => nomatch (h _).2 (.head _)
  | _ :: _, [], _, _, h => nomatch (h _).1 (.head _)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have head₁ := (List.pairwise_cons.1 h₁).1
    have head₂ := (List.pairwise_cons.1 h₂).1
    cases show a = b by
      rcases List.mem_cons.1 ((h a).1 (.head _)) with rfl | ha <;> [rfl; skip]
      rcases List.mem_cons.1 ((h b).2 (.head _)) with rfl | hb <;> [rfl; skip]
      cases Std.OrientedCmp.not_lt_of_lt (head₁ _ hb) (head₂ _ ha)
    refine congrArg (a :: ·) (sorted_pairs_eq (List.pairwise_cons.1 h₁).2
      (List.pairwise_cons.1 h₂).2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.1 ((h x).1 (.tail _ hx)) with rfl | hx'
      · have := head₁ _ hx; rw [listName_compare_self] at this; cases this
      · exact hx'
    · rcases List.mem_cons.1 ((h x).2 (.tail _ hx)) with rfl | hx'
      · have := head₂ _ hx; rw [listName_compare_self] at this; cases this
      · exact hx'

theorem NormLevel.toList_eq {A B : NormLevel} (h : A == B) : A.toList = B.toList := by
  simp +instances only [instBEqNormLevel, Std.TreeMap.all_eq_all_toList,
    Bool.and_eq_true, List.all_eq_true] at h
  refine sorted_pairs_eq Std.TreeMap.ordered_keys_toList Std.TreeMap.ordered_keys_toList
    fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have := h.1 x hx
    rw [beq_iff_eq, Std.TreeMap.get?_eq_getElem?] at this
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 this
  · have := h.2 x hx
    rw [beq_iff_eq, Std.TreeMap.get?_eq_getElem?] at this
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 this

theorem NormLevel.addable_congr {A B : NormLevel} (h : A.toList = B.toList) :
    A.addable a acc = B.addable a acc := by
  rw [addable, addable, Std.TreeMap.any_eq_any_toList, Std.TreeMap.any_eq_any_toList, h]

theorem NormLevel.feasible_go_congr {A B : NormLevel} (h : A.toList = B.toList) :
    ∀ fuel acc rem, NormLevel.feasible.go A fuel acc rem = NormLevel.feasible.go B fuel acc rem
  | 0, _, _ => rfl
  | fuel+1, acc, rem => by
    simp only [feasible.go]
    rw [show (fun a => A.addable a acc) = fun a => B.addable a acc from
      funext fun a => addable_congr h]
    cases rem.find? fun a => B.addable a acc with
    | none => rfl
    | some a => exact feasible_go_congr h fuel _ _

theorem NormLevel.feasible_congr {A B : NormLevel} (h : A.toList = B.toList) :
    A.feasible acc rem = B.feasible acc rem := by
  simp only [feasible]; exact feasible_go_congr h ..

theorem NormLevel.lexChain_congr {A B : NormLevel} (h : A.toList = B.toList) :
    ∀ fuel p, A.lexChain fuel p = B.lexChain fuel p
  | 0, _ => rfl
  | fuel+1, p => by
    simp only [lexChain]
    rw [show (fun a => A.addable a (p.erase a) && A.feasible [] (p.erase a))
        = fun a => B.addable a (p.erase a) && B.feasible [] (p.erase a) from
      funext fun a => by rw [addable_congr h, feasible_congr h]]
    cases p.find? fun a => B.addable a (p.erase a) && B.feasible [] (p.erase a) with
    | none => rfl
    | some a => exact congrArg (a :: ·) (lexChain_congr h fuel _)

/-- The reconstruction depends only on the entry list of the map. -/
theorem NormLevel.toTree_congr {A B : NormLevel} (h : A.toList = B.toList) :
    A.toTree = B.toTree := by
  rw [toTree, toTree, Std.TreeMap.foldl_eq_foldl_toList, Std.TreeMap.foldl_eq_foldl_toList, h]
  congr 1
  funext t pn
  rw [lexChain_congr h]

end Normalize

theorem isEquiv'_wf (h : isEquiv' u v)
    (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v') : u' ≈ v' := by
  simp only [isEquiv', Bool.or_eq_true, beq_iff_eq] at h
  obtain rfl | h := h
  · cases hu.symm.trans hv; rfl
  · refine VLevel.equiv_def.2 fun ρ => ?_
    rw [← Normalize.normalize_eval (ρ := ρ) hu, ← Normalize.normalize_eval (ρ := ρ) hv]
    exact Normalize.NormLevel.eval_congr h

/-- Soundness of reification: the level `normalize'` reconstructs evaluates like the input
everywhere. Reification is `toTree` followed by `reify`, and both preserve the value: the
tree's `imax` chains contribute nothing the normal form does not already have, since every
key admits a chain (`normalize_feas`) and `lexChain` then picks an admissible one, and
nothing is lost, since every entry is recorded at the end of its chain. -/
theorem normalize'_eval (hu : VLevel.ofLevel ls u = some u') :
    Level.eval (Normalize.evalParam ls ρ) μ (normalize' u) = u'.eval ρ := by
  open Normalize in
  rw [normalize', Tree.reify_eval, NormLevel.toTree_eval normalize_sorted normalize_feas]
  exact normalize_eval hu

theorem geq'_wf (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v')
    (h : geq' u v) : v' ≤ u' := by
  intro ρ
  rw [← Normalize.normalize_eval (ρ := ρ) hv, ← Normalize.normalize_eval (ρ := ρ) hu]
  exact Normalize.NormLevel.le_eval Normalize.normalize_vars h

theorem isEquivList_wf (H : Level.isEquivList us vs) :
    List.mapM (VLevel.ofLevel Us) us = some us' →
    List.mapM (VLevel.ofLevel Us) vs = some vs' → us'.Forall₂ (· ≈ ·) vs' := by
  simp [Level.isEquivList] at H; revert us' vs'
  induction us generalizing vs with cases vs <;> simp [List.all2] at H <;> simp | cons u us ih
  rename_i v vs; rintro _ _ u' hu us' hus rfl v' hv vs' hvs rfl
  exact .cons (isEquiv_wf H.1 hu hv) (ih H.2 hus hvs)

/-- Canonicity of `normalize'`: semantically equal levels reconstruct to syntactically equal
levels. The normal forms are `BEq`-equal, hence have the same entry list, and the
reconstruction (`lexChain` and the tree fold) depends on the map only through its entry
list. -/
theorem normalize'_complete (hu : VLevel.ofLevel ls u = some u')
    (hv : VLevel.ofLevel ls v = some v') : normalize' u = normalize' v ↔ u' ≈ v' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine VLevel.equiv_def.2 fun ρ => ?_
    rw [← normalize'_eval (μ := fun _ => 0) hu, ← normalize'_eval hv, h]
  · simp only [normalize']
    rw [← Normalize.normalize_complete hu hv] at h
    rw [Normalize.NormLevel.toTree_congr (Normalize.NormLevel.toList_eq h)]

/-- Completeness of `isEquiv'`: semantically equal levels have equal normal forms. Both
normal forms are reduced (`subsumption_reduced`), mutually dominate each other's sublevels
(`separation`), and reduced forms with the same sublevels are the same map. -/
theorem isEquiv'_complete (hu : VLevel.ofLevel ls u = some u')
    (hv : VLevel.ofLevel ls v = some v') : isEquiv' u v ↔ u' ≈ v' := by
  simp [isEquiv', Normalize.normalize_complete hu hv]
  rintro rfl; cases hu.symm.trans hv; exact rfl

/-- Completeness of `geq'`: every valid semantic inequality is accepted. Every sublevel of
`normalize v` is semantically bounded by `normalize u`, hence syntactically dominated by one
of its sublevels (`separation`), which is exactly what the discharging fold in
`NormLevel.le` checks for. -/
theorem geq'_complete (hu : VLevel.ofLevel ls u = some u')
    (hv : VLevel.ofLevel ls v = some v') : geq' u v ↔ v' ≤ u' := by
  open Normalize in
  refine ⟨geq'_wf hu hv, fun h => ?_⟩
  refine NormLevel.le_complete normalize_sortedVars normalize_sortedVars normalize_nonempty
    normalize_sorted normalize_sorted ?_
  refine NormLevel.separation (normalize_keys hv) normalize_vars fun ρ => ?_
  rw [normalize_eval hv, normalize_eval hu]
  exact h ρ
