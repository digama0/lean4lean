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

/-- The well-formedness invariant of the `NormLevel` maps produced by `normalizeAux`:
every variable recorded at a key is an element of that key, and every nonempty key `p`
extends another key of the map by a single variable that is recorded at `p`.
The latter is what makes the sublevels expressible by `imax` chains (see the reconstruction
comment in `Lean4Lean.Level`), and it lets `addConst` drop `C(p, 1)` for `p ≠ []`. -/
def NormLevel.WF (s : NormLevel) : Prop :=
  ∀ p n, s.get? p = some n →
    (p ≠ [] → ∃ v p', Extend1 p' v p ∧ (p' = [] ∨ s.contains p') ∧ ∃ x ∈ n.var, x.var = v) ∧
    (∀ v ∈ n.var, v.var ∈ p)

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

theorem VarNode.mem_addVar :
    (∃ x ∈ VarNode.addVar v k l, x.var = u) ↔ v = u ∨ (∃ x ∈ l, x.var = u) := by
  induction l with simp [addVar] | cons x l ih; split <;> simp_all [or_left_comm]

theorem NormLevel.addVar_wf (hv : v ∈ path) (wf : acc.WF) :
    (addVar v k path acc).WF := by
  simp [addVar, WF, Std.TreeMap.getElem?_modify, Std.TreeMap.mem_modify] at wf ⊢
  intro p n; split <;> [simp; apply wf]
  subst p; rintro _ h rfl; have ⟨a1, a2⟩ := wf _ _ h; refine ⟨fun h => ?_, fun _ h => ?_⟩
  · have ⟨_, _, b1, b2, b3⟩ := a1 h; exact ⟨_, _, b1, b2, VarNode.mem_addVar.2 (.inr b3)⟩
  · obtain eq | ⟨_, h, eq⟩ := VarNode.mem_addVar.1 ⟨_, h, rfl⟩
    · exact eq ▸ hv
    · exact eq ▸ a2 _ h

theorem NormLevel.addNode_wf (H : Extend1 path v path')
    (hacc : path = [] ∨ acc.contains path) (wf : acc.WF) : (addNode v k path' acc).WF := by
  simp [addNode, WF, Std.TreeMap.getElem?_alter, Std.TreeMap.mem_alter] at *
  intro p n; split
  · subst p; split <;> rintro ⟨⟩ <;> simp
    · exact ⟨fun _ => ⟨_, _, H, hacc.imp id fun h _ => h, rfl⟩, H.mem.2 (.inl rfl)⟩
    · obtain ⟨a1, a2⟩ := wf _ _ ‹_›; refine ⟨fun h => ?_, fun _ h => ?_⟩
      · have ⟨_, _, b1, b2, b3⟩ := a1 h
        exact ⟨_, _, b1, b2.imp id fun h _ => h, VarNode.mem_addVar.2 (.inr b3)⟩
      · obtain eq | ⟨_, h, eq⟩ := VarNode.mem_addVar.1 ⟨_, h, rfl⟩
        · exact H.mem.2 (.inl eq.symm)
        · exact eq ▸ a2 _ h
  · intro h; have ⟨a1, a2⟩ := wf _ _ h; refine ⟨fun h => ?_, a2⟩
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
  · obtain ⟨a1, a2⟩ := wf _ _ h₀
    refine ⟨fun h => ?_, fun v hv => a2 v (hvar ▸ hv)⟩
    obtain ⟨v, p', b1, b2, b3⟩ := a1 h
    exact ⟨v, p', b1, b2.imp id (hk _), hvar ▸ b3⟩
  · exact ⟨absurd rfl, by simp [hvar]⟩

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
        (NormLevel.addNode_wf (.orderedInsert eq)
        (H.imp id NormLevel.addConst_contains) (NormLevel.addConst_wf H wf))
    · exact normalizeAux_wf H wf
    · refine normalizeAux_wf (H.imp id NormLevel.addVar_contains) (NormLevel.addVar_wf ?_ wf)
      exact (eq ▸ Extend?.orderedInsert).mem.2 (.inl rfl)
  · exact wf
  · exact wf
  · split <;> rename_i eq <;> [skip; split]
    · exact NormLevel.addNode_wf (.orderedInsert eq)
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
        (NormLevel.addNode_wf (.orderedInsert h)
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
theorem NormLevel.subsumption_vars {s : NormLevel}
    (wf : ∀ p n, s.get? p = some n → ∀ v ∈ n.var, v.var ∈ p) :
    ∀ p n, s.subsumption.get? p = some n → ∀ v ∈ n.var, v.var ∈ p := by
  rw [subsumption, Std.TreeMap.foldl_eq_foldl_toList]
  have hmem pn (h : pn ∈ s.toList) : s.get? pn.1 = some pn.2 :=
    Std.TreeMap.get?_eq_getElem? .. ▸ Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 h
  generalize s.toList = l at hmem
  suffices ∀ (l : List (List Name × Node)) (acc : NormLevel),
      (∀ pn ∈ l, s.get? pn.1 = some pn.2) →
      (∀ p n, acc.get? p = some n → ∀ v ∈ n.var, v.var ∈ p) →
      ∀ p n, (List.foldl (fun acc pn =>
        let n := acc.minimize pn.1 pn.2
        if n.isEmpty then acc.erase pn.1 else acc.insert pn.1 n) acc l).get? p = some n →
        ∀ v ∈ n.var, v.var ∈ p from this _ _ hmem wf
  clear hmem; intro l
  induction l with | nil => exact fun _ _ => id | cons pn l ih
  intro acc hl hacc
  refine ih _ (fun _ h => hl _ (.tail _ h)) fun p n h v hv => ?_
  rw [subsumption_step_get?] at h
  split at h
  · split at h <;> [cases h; skip]
    cases h; rename_i hp _; subst hp
    exact wf _ _ (hl _ (.head _)) _ (minimize_var_subset hv)
  · exact hacc _ _ h _ hv

theorem NormLevel.subsumption_eval {s : NormLevel} (wf : s.WF) :
    (s.subsumption).eval ls ρ = s.eval ls ρ := by
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
    this _ _ nd (fun _ _ => hmem _) (fun _ _ h => (wf _ _ h).2) rfl
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

theorem normalize_vars : ∀ p n, (normalize u).get? p = some n → ∀ v ∈ n.var, v.var ∈ p :=
  NormLevel.subsumption_vars fun _ _ h =>
    (normalizeAux_wf (by simp) (by simp [NormLevel.WF]) _ _ h).2

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

end Normalize

theorem isEquiv'_wf (h : isEquiv' u v)
    (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v') : u' ≈ v' := by
  simp only [isEquiv', Bool.or_eq_true, beq_iff_eq] at h
  obtain rfl | h := h
  · cases hu.symm.trans hv; rfl
  · refine VLevel.equiv_def.2 fun ρ => ?_
    rw [← Normalize.normalize_eval (ρ := ρ) hu, ← Normalize.normalize_eval (ρ := ρ) hv]
    exact Normalize.NormLevel.eval_congr h

theorem geq'_wf (h : geq' u v)
    (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v') : v' ≤ u' := by
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
