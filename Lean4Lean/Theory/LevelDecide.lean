import Lean4Lean.Theory.VLevel

/-!
# Decidability of `VLevel` order and equivalence

A simple (exponential) decision procedure, meant to be easy to verify rather than fast.
Split on a *zeroness pattern* `σ`, saying which parameters are nonzero. On the region of
valuations with that pattern every `imax` is resolved, and a level flattens to a *max stack*:
a list of atoms `param i + k` (with `i` nonzero) and constants `k`. Then `s ≤ t` on the region
iff every atom of `s` is dominated by a single atom of `t`, since all nonzero parameters can be
`1` at once and any one of them can be sent to infinity.
-/

namespace Lean4Lean.VLevel

/-- An atom of a max stack: `(some i, k)` is `param i + k`, `(none, k)` is the constant `k`. -/
abbrev Atom := Option Nat × Nat

def Atom.eval (ls : List Nat) : Atom → Nat
  | (some i, k) => ls.getD i 0 + k
  | (none, k) => k

def Atom.succ : Atom → Atom | (i, k) => (i, k + 1)

/-- Domination of atoms, valid when all parameters are nonzero. -/
def Atom.le : Atom → Atom → Bool
  | (none, k), (none, k') => k ≤ k'
  | (none, k), (some _, k') => k ≤ k' + 1
  | (some i, k), (some j, k') => i = j ∧ k ≤ k'
  | (some _, _), (none, _) => false

/-- The value of a max stack (`0` for the empty stack). -/
def evalStack (ls : List Nat) (s : List Atom) : Nat := s.foldr (fun a m => Max.max (a.eval ls) m) 0

/-- A zeroness pattern: `σ.getD i false` says whether parameter `i` is nonzero. -/
def Region (n : Nat) (σ : List Bool) (ls : List Nat) : Prop :=
  ∀ i < n, (ls.getD i 0 ≠ 0 ↔ σ.getD i false)

/-- The atoms of a stack are nonzero parameters below `n` or positive constants. -/
def Atom.Valid (n : Nat) (σ : List Bool) : Atom → Prop
  | (some i, _) => i < n ∧ σ.getD i false
  | (none, k) => 0 < k

/-- Flatten `l` to a max stack, on the region of the zeroness pattern `σ`. -/
def flat (σ : List Bool) : VLevel → List Atom
  | .zero => []
  | .succ l => (none, 1) :: (flat σ l).map Atom.succ
  | .max l₁ l₂ => flat σ l₁ ++ flat σ l₂
  | .imax l₁ l₂ => let s := flat σ l₂; if s.isEmpty then [] else flat σ l₁ ++ s
  | .param i => if σ.getD i false then [(some i, 0)] else []

def leStack (s t : List Atom) : Bool := s.all fun a => t.any a.le

/-- All zeroness patterns of length `n`. -/
def patterns : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (patterns n).flatMap fun σ => [false :: σ, true :: σ]

/-- A strict upper bound on the parameters of a level. -/
def bound : VLevel → Nat
  | .zero => 0
  | .succ l => l.bound
  | .max l₁ l₂ | .imax l₁ l₂ => Max.max l₁.bound l₂.bound
  | .param i => i + 1

def leB (a b : VLevel) : Bool :=
  let n := Max.max a.bound b.bound
  (patterns n).all fun σ => leStack (flat σ a) (flat σ b)

theorem mem_patterns (σ : List Bool) : σ ∈ patterns σ.length := by
  induction σ with | nil => exact .head _ | cons b σ ih
  simp only [List.length_cons, patterns, List.mem_flatMap]; exact ⟨σ, ih, by cases b <;> simp⟩

theorem wf_bound (l : VLevel) : WF l.bound l := by
  induction l with
  | zero => trivial
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 =>
    exact ⟨ih1.mono (by simp only [bound]; omega), ih2.mono (by simp only [bound]; omega)⟩
  | param => exact Nat.lt_succ_self _

theorem evalStack_append : evalStack ls (s ++ t) = Max.max (evalStack ls s) (evalStack ls t) := by
  induction s with | nil => simp [evalStack] | cons a s ih
  simp only [evalStack] at *; simp only [List.cons_append, List.foldr_cons, ih]; omega

theorem evalStack_succ : Max.max 1 (evalStack ls (s.map Atom.succ)) = evalStack ls s + 1 := by
  induction s with | nil => rfl | cons a s ih
  simp only [evalStack] at *
  have : (Atom.succ a).eval ls = a.eval ls + 1 := by
    rcases a with ⟨_ | _, _⟩ <;> simp [Atom.succ, Atom.eval]; omega
  simp only [List.map_cons, List.foldr_cons, this]; omega

theorem le_evalStack (h : a ∈ s) : a.eval ls ≤ evalStack ls s := by
  induction s with | nil => cases h | cons b s ih
  simp only [evalStack, List.foldr_cons] at *
  rcases List.mem_cons.1 h with rfl | h
  · omega
  · have := ih h; omega

theorem evalStack_le : evalStack ls s ≤ m ↔ ∀ a ∈ s, a.eval ls ≤ m := by
  induction s with | nil => simp [evalStack] | cons a s ih
  simp only [evalStack, List.foldr_cons, List.forall_mem_cons] at *; rw [Nat.max_le, ih]

theorem evalStack_lt (hm : 0 < m) (h : ∀ a ∈ s, a.eval ls < m) : evalStack ls s < m := by
  induction s with | nil => exact hm | cons a s ih
  have := ih fun b hb => h b (.tail _ hb); have := h a (.head _)
  simp only [evalStack, List.foldr_cons] at *; omega

theorem Atom.Valid.pos (H : Region n σ ls) : ∀ {a : Atom}, a.Valid n σ → 0 < a.eval ls
  | (some i, _), ⟨h1, h2⟩ => by have := H i h1; simp_all [eval]; omega
  | (none, _), h => h

theorem evalStack_eq_zero (H : Region n σ ls) (hs : ∀ a ∈ s, a.Valid n σ) :
    evalStack ls s = 0 ↔ s = [] := by
  cases s with | nil => simp [evalStack] | cons a s
  have := (hs a (.head _)).pos H
  simp only [evalStack, List.foldr_cons, reduceCtorEq, iff_false]; omega

theorem flat_valid (hl : WF n l) (ha : a ∈ flat σ l) : a.Valid n σ := by
  induction l generalizing a with
  | zero => cases ha
  | succ l ih =>
    simp only [flat, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨⟨_ | i, k⟩, h, rfl⟩
    · exact Nat.one_pos
    · exact Nat.succ_pos _
    · exact (ih hl h :)
  | max l₁ l₂ ih1 ih2 =>
    rcases List.mem_append.1 ha with h | h
    · exact ih1 hl.1 h
    · exact ih2 hl.2 h
  | imax l₁ l₂ ih1 ih2 =>
    simp only [flat] at ha; split at ha; · cases ha
    rcases List.mem_append.1 ha with h | h
    · exact ih1 hl.1 h
    · exact ih2 hl.2 h
  | param i =>
    simp only [flat] at ha; split at ha <;> simp at ha
    subst a; exact ⟨hl, by assumption⟩

theorem eval_flat (hl : WF n l) (H : Region n σ ls) : l.eval ls = evalStack ls (flat σ l) := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [eval, flat, ih hl, ← evalStack_succ]; rfl
  | max l₁ l₂ ih1 ih2 => simp only [eval, flat, evalStack_append, ih1 hl.1, ih2 hl.2]
  | imax l₁ l₂ ih1 ih2 =>
    have := evalStack_eq_zero H fun _ => flat_valid (σ := σ) hl.2
    simp only [eval, flat, Lean.Nat.imax, ih1 hl.1, ih2 hl.2, List.isEmpty_iff, this]
    split; · rfl
    exact evalStack_append.symm
  | param i =>
    have := H i hl; simp only [eval, flat]
    split <;> simp_all [evalStack, Atom.eval]

theorem Atom.le_sound {a b : Atom} (H : Region n σ ls) (hb : b.Valid n σ) (h : a.le b) :
    a.eval ls ≤ b.eval ls := by
  match a, b, h with
  | (none, _), (none, _), h | (some _, _), (some _, _), h => simp_all [le, eval]
  | (none, _), (some j, _), h =>
    have := H j hb.1; simp_all [le, eval, Valid]; omega

theorem leB_iff : leB a b ↔ a ≤ b := by
  have ha := (wf_bound a).mono (Nat.le_max_left a.bound b.bound)
  have hb := (wf_bound b).mono (Nat.le_max_right a.bound b.bound)
  simp only [leB, List.all_eq_true]
  generalize Max.max a.bound b.bound = n at ha hb ⊢
  refine ⟨fun h ls => ?_, fun h σ _ => List.all_eq_true.2 fun x hx => ?_⟩
  · let σ := (List.range n).map fun i => ls.getD i 0 != 0
    have H : Region n σ ls := fun i hi => by simp [σ, List.getD_eq_getElem?_getD, hi]
    have h := List.all_eq_true.1 <| h σ (by simpa [σ] using mem_patterns σ)
    rw [eval_flat ha H, eval_flat hb H]
    refine evalStack_le.2 fun x hx => ?_
    have ⟨y, hy, hxy⟩ := List.any_eq_true.1 (h x hx)
    exact Nat.le_trans (Atom.le_sound H (flat_valid hb hy) hxy) (le_evalStack hy)
  refine Bool.of_not_eq_false fun hn => ?_
  have hxy := List.any_eq_false.1 hn
  let N := evalStack [] (flat σ b) + 2
  -- `1` on the nonzero parameters, except `N` on the parameter of `x`
  let ls := (List.range n).map fun j => if σ.getD j false then if x.1 = some j then N else 1 else 0
  have hls {i} (h : i < n) :
      ls.getD i 0 = if σ.getD i false then if x.1 = some i then N else 1 else 0 := by
    simp [ls, List.getD_eq_getElem?_getD, h]
  have H : Region n σ ls := by
    intro i h; rw [hls h]; cases σ.getD i false <;> simp; split <;> omega
  refine Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ?_ (h ls))
  rw [eval_flat ha H, eval_flat hb H]
  refine Nat.lt_of_lt_of_le ?_ (le_evalStack hx)
  refine evalStack_lt ((flat_valid ha hx).pos H) fun y hy => ?_
  have : y.2 ≤ y.eval [] := by rcases y with ⟨_ | _, _⟩ <;> simp [Atom.eval]
  have := le_evalStack (ls := []) hy
  match x, y, flat_valid ha hx, flat_valid hb hy, hxy y hy with
  | (none, _), (none, _), _, _, hxy => simp_all [Atom.le, Atom.eval]
  | (none, _), (some j, _), _, hy', hxy =>
    simp only [Atom.le, Atom.Valid, decide_eq_true_eq] at hy' hxy
    simp only [Atom.eval, hls hy'.1, hy'.2]; simp; omega
  | (some i, _), (none, _), hx', _, _ =>
    simp only [Atom.Valid] at hx'; simp only [Atom.eval, hls hx'.1, hx'.2]; simp; omega
  | (some i, _), (some j, _), hx', hy', hxy =>
    simp only [Atom.Valid, Atom.le, decide_eq_true_eq] at hx' hy' hxy
    simp only [Atom.eval, hls hx'.1, hls hy'.1, hx'.2, hy'.2, if_true, Option.some.injEq]
    by_cases e : i = j <;> simp_all <;> omega

instance : DecidableRel (α := VLevel) (· ≤ ·) := fun _ _ => decidable_of_iff _ leB_iff

instance : DecidableRel (α := VLevel) (· ≈ ·) := fun _ _ =>
  decidable_of_iff _ le_antisymm_iff.symm
