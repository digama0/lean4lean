import Lean4Lean.Theory.VLevel

/-!
# Universe level equivalence is coNP-hard

This file contains a polynomial-time reduction from CNF (un)satisfiability to `VLevel`
equivalence, showing that the problem solved by `Level.isEquiv` (and `Level.geq`) is
coNP-hard, and hence that no complete algorithm for it runs in polynomial time unless
P = NP.

## The complexity of `VLevel.Equiv`

Write `σ ∈ {0,1}^V` for a *zeroness pattern*, an assignment of "is zero"/"is nonzero" to
each parameter. The matching upper bound (not formalized here) is that the complement,
`¬(a ≈ b)`, is in NP:

* zeroness of a level is a *conjunction of parameter-zeroness*: `zero` is zero,
  `succ _` is not, `max a b` is zero iff both are, `imax a b` is zero iff `b` is.
  So a guessed `σ` decides every `imax` branch bottom-up in linear time;
* what remains after resolving the `imax`es is a `max`/`succ`/`param` expression, whose
  normal form is a *vector*: one best offset `c_x` per parameter plus a constant `K`
  (`max` is componentwise max, `succ` adds one to everything), computable bottom-up;
* two such vectors denote the same function on the region cut out by `σ` iff their
  offsets agree on every nonzero parameter (send that parameter to infinity) and either
  `K₁ = K₂` or both constants are dominated by the minimum of the variable part.

So: guess `σ`, check in polynomial time. Hardness is the content of this file, so the
problem is coNP-complete.

## The reduction

A formula `φ : CNF n` is over the variables `Fin n`, so that "`φ` only mentions variables
the levels provide rails for" is part of its type. Parameters are used in *dual rail*:
`i⁺ := param (yes i)` stands for "`xᵢ` is true" and `i⁻ := param (no i)` for "`xᵢ` is
false", where `yes i = 2*i` and `no i = 2*i+1`, with a rail read as "true" when it is
nonzero (see `rail`). Note that no level can compute a
negation — every level denotes a monotone function — so the negation needed for SAT enters
through a *failure of domination*: the constant `2` on the left of `≤` must exceed
everything the right side can offer.

The two levels are (see `big`, `small`):
```
small n := max (var 0) ⋯ (var (n-1))
big   φ := max (small n) (gates φ)
```
where `gates φ` is the constant `2` gated by each clause of `φ` (`imax _ c` with `c` the
`max` of the clause's rails), and `var i` is `max i⁺ (imax (imax 2 i⁺) i⁻)`, which is
`max i⁺ i⁻` unless both rails are nonzero, where it is `≥ 2`. So `small n` does double
duty: `small n ≤ 1` says exactly that the rails describe a consistent assignment with
values in `{0,1}`, and `small n` dominates every parameter, so values leaking out of the
gates of `gates φ` cannot create a spurious difference. `small ≤ big` holds structurally,
and the two differ exactly at a point where the rails describe a consistent satisfying
assignment with all values `≤ 1`:

* `equiv_iff_unsat : big φ ≈ small n ↔ ¬Sat φ`
* `le_iff_unsat : big φ ≤ small n ↔ ¬Sat φ`

and `size_big` records that the construction is linear in the size of `φ`.
-/

namespace Lean4Lean

namespace LevelSat

/-! ## CNF formulas -/

/-- A literal: a variable of `Fin n` together with the polarity it must have. Indexing the
variables by `Fin n` puts "`φ` mentions only the variables `small n` provides rails for"
into the type, so the reduction carries no side condition. -/
abbrev Lit (n : Nat) := Fin n × Bool
/-- A clause is a disjunction of literals. -/
abbrev Clause (n : Nat) := List (Lit n)
/-- A formula in conjunctive normal form, over the variables `Fin n`. -/
abbrev CNF (n : Nat) := List (Clause n)

variable {n : Nat}

/-- An assignment satisfies a clause if it agrees with one of its literals. -/
def ClauseSat (a : Fin n → Bool) (C : Clause n) : Prop := ∃ l ∈ C, a l.1 = l.2

/-- The satisfiability problem: this is the NP-complete predicate we reduce from. -/
def Sat (φ : CNF n) : Prop := ∃ a : Fin n → Bool, ∀ C ∈ φ, ClauseSat a C

/-- The parameter index of the rail `i⁺`, i.e. of "`xᵢ` is true". -/
abbrev yes (i : Nat) : Nat := 2 * i

/-- The parameter index of the rail `i⁻`, i.e. of "`xᵢ` is false". -/
abbrev no (i : Nat) : Nat := 2 * i + 1

/-- The dual-rail parameter index of a literal: the `yes` rail of its variable if it is
positive, the `no` rail if it is negative. -/
def rail (l : Lit n) : Nat := if l.2 then yes l.1.val else no l.1.val

theorem rail_lt {l : Lit n} : rail l < 2 * n := by
  have := l.1.isLt; unfold rail yes no; split <;> omega

theorem rail_pos {l : Lit n} (h : l.2 = true) : rail l = yes l.1.val := by simp [rail, h]

theorem rail_neg {l : Lit n} (h : l.2 = false) : rail l = no l.1.val := by simp [rail, h]

/-! ## The levels -/

/-- The constant level `2`. -/
def two : VLevel := .succ (.succ .zero)

/-- The disjunction of a clause, as the `max` of the rails of its literals. This is
nonzero exactly when the dual-rail reading of the parameters satisfies the clause. -/
def clauseLvl (C : Clause n) : VLevel :=
  C.foldr (fun l acc => .max (.param (rail l)) acc) .zero

/-- The constant `2`, gated by every clause of `φ`. Its value is `max 2 (gate values)`
when every clause gate is nonzero, and is bounded by the gate values otherwise: the
constant `2` survives only if all clauses are satisfied. -/
def gates (φ : CNF n) : VLevel := (φ.map clauseLvl).foldl .imax two

/-- Writing `i⁺`, `i⁻` for the two rails of variable `i`, this is `max i⁺ (imax (imax 2 i⁺) i⁻)`,
which evaluates to `max i⁺ i⁻` unless both rails are nonzero, in which case it is
`max 2 (max i⁺ i⁻) ≥ 2` (see `eval_var_eq`). -/
def var (i : Nat) : VLevel :=
  .max (.param (yes i)) (.imax (.imax two (.param (yes i))) (.param (no i)))

/-- Rail inconsistency detector: evaluates to `≥ 2` as soon as both rails of some variable
`i < n` are nonzero, and to the largest rail value otherwise. So `small n ≤ 1` says exactly
that the rails describe a consistent assignment using only the values `0` and `1`: it is
both the source of negation in the reduction and the bound on every parameter. -/
def small : Nat → VLevel
  | 0 => .zero
  | i+1 => .max (small i) (var i)

/-- The larger of the two levels of the reduction: `small` together with the gated
constant `2`, which pokes above `small` exactly at a satisfying assignment. -/
def big (φ : CNF n) : VLevel := .max (small n) (gates φ)

/-! ## Evaluation lemmas

`VLevel.eval` is stated with `Nat.max` and `Lean.Nat.imax`; these restate it in terms of
`max` and `ite`, which is what `omega` and `split` understand. -/

variable {ls : List Nat}

@[simp] theorem eval_two : two.eval ls = 2 := rfl

theorem eval_clauseLvl_cons {l : Lit n} {C : Clause n} :
    (clauseLvl (l :: C)).eval ls = max (ls[rail l]?.getD 0) ((clauseLvl C).eval ls) := rfl

theorem eval_clauseLvl_le {C : Clause n} {c : Nat} (h : ∀ l ∈ C, ls[rail l]?.getD 0 ≤ c) :
    (clauseLvl C).eval ls ≤ c := by
  induction C with | nil => exact Nat.zero_le _ | cons l C ih
  rw [eval_clauseLvl_cons]
  have := ih fun l hl => h l (.tail _ hl)
  have := h l (.head _)
  omega

theorem eval_clauseLvl_ne_zero {C : Clause n} :
    (clauseLvl C).eval ls ≠ 0 ↔ ∃ l ∈ C, ls[rail l]?.getD 0 ≠ 0 := by
  induction C with | nil => simp [clauseLvl, VLevel.eval] | cons l C ih
  rw [eval_clauseLvl_cons]
  constructor
  · intro h
    obtain h0 | h0 :=Nat.eq_zero_or_pos (ls[rail l]?.getD 0)
    · have ⟨l', h1, h2⟩ := ih.1 (by omega)
      exact ⟨l', .tail _ h1, h2⟩
    · exact ⟨l, .head _, by omega⟩
  · rintro ⟨l', h1, h2⟩
    obtain rfl | h1 := List.mem_cons.1 h1
    · omega
    · have := ih.2 ⟨l', h1, h2⟩; omega

/-! ### The gate fold

The three facts about `gs.foldl imax b` that the reduction needs: it is bounded by the
accumulator and the gates; it loses the accumulator entirely once some gate is zero; and
it keeps the accumulator when no gate is zero. -/

theorem eval_foldl_imax_le {gs : List VLevel} (hg : ∀ g ∈ gs, g.eval ls ≤ c) (b : VLevel) :
    (gs.foldl .imax b).eval ls ≤ max (b.eval ls) c := by
  induction gs generalizing b with
  | nil => simp only [List.foldl_nil]; omega
  | cons g gs ih =>
    have h1 : (VLevel.imax b g).eval ls ≤ max (b.eval ls) c := by
      simp [VLevel.eval, Lean.Nat.imax, Nat.max_eq_max]; have := hg g (.head _); split <;> omega
    have h2 := ih (fun g hg' => hg g (.tail _ hg')) (.imax b g)
    rw [List.foldl_cons]; omega

theorem eval_foldl_imax_le_of_zero {gs : List VLevel} {c : Nat}
    (hg : ∀ g ∈ gs, g.eval ls ≤ c) (h0 : ∃ g ∈ gs, g.eval ls = 0) (b : VLevel) :
    (gs.foldl .imax b).eval ls ≤ c := by
  induction gs generalizing b with | nil => simp at h0 | cons g gs ih
  rw [List.foldl_cons]
  by_cases hz : g.eval ls = 0
  · have h1 : (VLevel.imax b g).eval ls = 0 := by rw [VLevel.eval, Lean.Nat.imax, if_pos hz]
    have h2 := eval_foldl_imax_le (ls := ls) (fun g hg' => hg g (.tail _ hg')) (.imax b g)
    omega
  · obtain ⟨g', h1, h2⟩ := h0
    refine ih (fun g hg' => hg g (.tail _ hg')) ?_ _
    obtain rfl | h1 := List.mem_cons.1 h1
    · exact absurd h2 hz
    · exact ⟨g', h1, h2⟩

theorem le_eval_foldl_imax {gs : List VLevel} (hg : ∀ g ∈ gs, g.eval ls ≠ 0) (b : VLevel) :
    b.eval ls ≤ (gs.foldl .imax b).eval ls := by
  induction gs generalizing b with | nil => exact Nat.le_refl _ | cons g gs ih
  have h1 : b.eval ls ≤ (VLevel.imax b g).eval ls := by
    rw [VLevel.eval, Lean.Nat.imax, Nat.max_eq_max]; have := hg g (.head _); split <;> omega
  exact Nat.le_trans h1 (ih (fun g hg' => hg g (.tail _ hg')) _)

/-! ### The variable summands -/

/-- The value of a single summand of `small`: the larger rail, pushed up to `2` when both
rails are nonzero. -/
theorem eval_var_eq {i : Nat} : (var i).eval ls =
    if ls[no i]?.getD 0 = 0 then ls[yes i]?.getD 0
    else if ls[yes i]?.getD 0 = 0 then ls[no i]?.getD 0
    else max 2 (max (ls[yes i]?.getD 0) (ls[no i]?.getD 0)) := by
  simp only [var, VLevel.eval, List.getD_eq_getElem?_getD, Lean.Nat.imax, Nat.max_eq_max, eval_two]
  by_cases h2 : ls[no i]?.getD 0 = 0 <;> by_cases h1 : ls[yes i]?.getD 0 = 0 <;>
    simp only [h1, h2, if_true, if_false] <;> omega

theorem yes_le_eval_var {i : Nat} : ls[yes i]?.getD 0 ≤ (var i).eval ls := by
  rw [eval_var_eq]; split <;> [omega; split <;> omega]

theorem no_le_eval_var {i : Nat} : ls[no i]?.getD 0 ≤ (var i).eval ls := by
  rw [eval_var_eq]; split <;> [omega; split <;> omega]

theorem two_le_eval_var {i : Nat}
    (h1 : ls[yes i]?.getD 0 ≠ 0) (h2 : ls[no i]?.getD 0 ≠ 0) : 2 ≤ (var i).eval ls := by
  rw [eval_var_eq, if_neg h2, if_neg h1]; omega

theorem eval_var_le_one {i : Nat}
    (hex : ls[yes i]?.getD 0 = 0 ∨ ls[no i]?.getD 0 = 0)
    (h1 : ls[yes i]?.getD 0 ≤ 1) (h2 : ls[no i]?.getD 0 ≤ 1) : (var i).eval ls ≤ 1 := by
  rw [eval_var_eq]
  split <;> [omega; skip]
  split <;> [omega; skip]
  cases hex <;> omega

/-- `small` bounds every parameter in play: this is the role `max`ing all the parameters
together would otherwise have to play. -/
theorem le_eval_small {n j : Nat} (h : j < 2*n) : ls[j]?.getD 0 ≤ (small n).eval ls := by
  induction n with | zero => omega | succ n ih
  simp only [small]; rw [VLevel.eval, Nat.max_eq_max]
  obtain h' | h' := Nat.lt_or_ge j (2*n)
  · have := ih h'; omega
  · obtain rfl | rfl : j = yes n ∨ j = no n := by unfold yes no; omega
    · have := yes_le_eval_var (ls := ls) (i := n); omega
    · have := no_le_eval_var (ls := ls) (i := n); omega

theorem two_le_eval_small {n i : Nat} (hi : i < n)
    (h1 : ls[yes i]?.getD 0 ≠ 0) (h2 : ls[no i]?.getD 0 ≠ 0) : 2 ≤ (small n).eval ls := by
  induction n with | zero => omega | succ n ih
  simp only [small]; rw [VLevel.eval, Nat.max_eq_max]
  obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 hi
  · have := ih h; omega
  · have := two_le_eval_var h1 h2; omega

theorem eval_small_le_one {n : Nat}
    (hex : ∀ i, i < n → ls[yes i]?.getD 0 = 0 ∨ ls[no i]?.getD 0 = 0)
    (h1 : ∀ j, j < 2*n → ls[j]?.getD 0 ≤ 1) : (small n).eval ls ≤ 1 := by
  induction n with | zero => exact Nat.zero_le _ | succ n ih
  simp only [small]; rw [VLevel.eval, Nat.max_eq_max]
  specialize ih (fun i hi => hex i (by omega)) (fun j hj => h1 j (by omega))
  have := eval_var_le_one (hex n (by omega)) (h1 (yes n) (by unfold yes; omega))
    (h1 (no n) (by unfold no; omega))
  omega

/-! ## The rail encoding of an assignment -/

/-- The value of rail `j` under the assignment `a`: `1` if the rail agrees with `a`,
else `0`. Even `j` is the rail `(j / 2)⁺`, odd `j` the rail `(j / 2)⁻`. -/
def railVal (a : Nat → Bool) (j : Nat) : Nat :=
  if a (j / 2) = decide (j % 2 = 0) then 1 else 0

/-- The point at which `big` and `small` differ, when `a` satisfies `φ`. -/
def railList (n : Nat) (a : Nat → Bool) : List Nat := (List.range (2*n)).map (railVal a)

/-- Read a `Fin n`-indexed assignment at an arbitrary index; the values outside `Fin n`
are never looked at. -/
def ofFin (a : Fin n → Bool) (i : Nat) : Bool := if h : i < n then a ⟨i, h⟩ else false

@[simp] theorem ofFin_val {a : Fin n → Bool} {i : Fin n} : ofFin a i.val = a i := by
  simp [ofFin, i.isLt]

theorem railVal_le {a : Nat → Bool} {j : Nat} : railVal a j ≤ 1 := by
  unfold railVal; split <;> omega

theorem railVal_yes {a : Nat → Bool} {i : Nat} :
    railVal a (yes i) = if a i = true then 1 else 0 := by
  have e1 : yes i / 2 = i := by unfold yes; omega
  have e2 : yes i % 2 = 0 := by unfold yes; omega
  simp [railVal, e1, e2]

theorem railVal_no {a : Nat → Bool} {i : Nat} :
    railVal a (no i) = if a i = false then 1 else 0 := by
  have e1 : no i / 2 = i := by unfold no; omega
  simp [railVal, e1]

theorem railVal_rail {a : Nat → Bool} {l : Lit n} :
    railVal a (rail l) = if a l.1.val = l.2 then 1 else 0 := by
  cases hb : l.2 with
  | true => rw [rail_pos hb, railVal_yes]
  | false => rw [rail_neg hb, railVal_no]

theorem getD_railList {a : Nat → Bool} {n j : Nat} :
    (railList n a)[j]?.getD 0 = if j < 2*n then railVal a j else 0 := by
  rw [railList, List.getElem?_map]
  split
  · rw [List.getElem?_range ‹_›]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem getD_railList_le {a : Nat → Bool} {n j : Nat} : (railList n a)[j]?.getD 0 ≤ 1 := by
  rw [getD_railList]; split <;> [exact railVal_le; omega]

theorem getD_railList_yes {a : Nat → Bool} {n i : Nat} (hi : i < n) :
    (railList n a)[yes i]?.getD 0 = if a i = true then 1 else 0 := by
  rw [getD_railList, if_pos (by unfold yes; omega), railVal_yes]

theorem getD_railList_no {a : Nat → Bool} {n i : Nat} (hi : i < n) :
    (railList n a)[no i]?.getD 0 = if a i = false then 1 else 0 := by
  rw [getD_railList, if_pos (by unfold no; omega), railVal_no]

theorem getD_railList_rail {a : Nat → Bool} {l : Lit n} :
    (railList n a)[rail l]?.getD 0 = if a l.1.val = l.2 then 1 else 0 := by
  rw [getD_railList, if_pos rail_lt, railVal_rail]

/-! ## The reduction -/

theorem small_le_big {φ : CNF n} : small n ≤ big φ := fun _ => Nat.le_max_left ..

/-- **The reduction.** Equivalence of the two levels is exactly unsatisfiability of `φ`,
so `VLevel.Equiv` is coNP-hard (and, being in coNP, coNP-complete). -/
theorem equiv_iff_unsat {φ : CNF n} : big φ ≈ small n ↔ ¬Sat φ := by
  constructor <;> intro H
  · -- a satisfying assignment gives a point at which the two levels differ: its rail
    -- encoding, where the rails are `0`/`1` and consistent, so `small` stays at `≤ 1`
    rintro ⟨a, ha⟩
    have H := VLevel.equiv_def.1 H (railList n (ofFin a))
    have hX : (small n).eval (railList n (ofFin a)) ≤ 1 := by
      refine eval_small_le_one (fun i hi => ?_) (fun _ _ => getD_railList_le)
      rw [getD_railList_yes hi, getD_railList_no hi]
      cases h : ofFin a i
      · exact .inl (by simp)
      · exact .inr (by simp)
    -- so it is enough that the gated constant `2` pokes above it
    suffices 2 ≤ (gates φ).eval (railList n (ofFin a)) by
      simp only [big, VLevel.eval, Nat.max_eq_max] at H; omega
    -- and it does: `a` satisfies every clause, so no clause gate is zero and the `2`
    -- survives the whole fold
    simp only [gates]
    refine Nat.le_trans (Nat.le_of_eq eval_two.symm)
      (le_eval_foldl_imax (List.forall_mem_map.2 fun C hC => ?_) two)
    obtain ⟨⟨i, l⟩, hl, hal⟩ := ha C hC; dsimp at hal; subst l
    refine eval_clauseLvl_ne_zero.2 ⟨_, hl, ?_⟩
    rw [getD_railList_rail, if_pos ofFin_val]; nofun
  · -- conversely, any point at which the two levels differ *is* a satisfying assignment
    refine VLevel.equiv_def.2 fun ls => Decidable.by_contra fun hlt => H ?_
    -- a clause level is a max of rails, and `small` dominates every parameter
    have hcl (C : Clause n) : (clauseLvl C).eval ls ≤ (small n).eval ls := by
      exact eval_clauseLvl_le fun l _ => le_eval_small rail_lt
    -- read the assignment off the `yes` rails
    refine ⟨fun i => ls[yes i.val]?.getD 0 ≠ 0, fun C hC => ?_⟩
    -- the difference can only be the gated `2` sticking out, so `small < gates`
    simp only [big, VLevel.eval, Nat.max_eq_max] at hlt
    -- hence no clause gate is zero: a zero gate loses the `2` and leaves `gates ≤ small`
    obtain ⟨l, hl, hlnz⟩ := eval_clauseLvl_ne_zero.1 fun hz => by
      have := eval_foldl_imax_le_of_zero (ls := ls)
        (List.forall_mem_map.2 fun C _ => hcl C) ⟨_, List.mem_map.2 ⟨_, hC, rfl⟩, hz⟩ two
      simp only [gates] at hlt; omega
    refine ⟨l, hl, ?_⟩
    -- a positive literal with a nonzero rail is read as true; for a negative one there is
    -- still the `yes` rail of its variable to rule out
    cases hb' : l.2 <;> simp_all [rail_pos, rail_neg]
    -- and it is zero: both rails nonzero would put `small` at `≥ 2`, collapsing the bound
    -- `gates ≤ max 2 small` to `gates ≤ small`
    refine Decidable.by_contra fun _ => ?_
    have : 2 ≤ (small n).eval ls := two_le_eval_small l.1.2 (by omega) (by omega)
    have hub : (gates φ).eval ls ≤ max 2 ((small n).eval ls) :=
      eval_foldl_imax_le (ls := ls) (List.forall_mem_map.2 fun C _ => hcl C) two
    omega

/-- The same for the `≤` test, i.e. for what `Level.geq` decides: since `small ≤ big`
always holds, deciding `big ≤ small` is deciding unsatisfiability. -/
theorem le_iff_unsat {φ : CNF n} : big φ ≤ small n ↔ ¬Sat φ := by
  rw [← equiv_iff_unsat, VLevel.le_antisymm_iff]
  exact ⟨fun h => ⟨h, small_le_big⟩, fun h => h.1⟩

/-! ## The reduction is linear

What makes the above a *hardness* result rather than a curiosity is that `big` and `small`
are computed from `φ` in linear time; `size_big` records the size half of that. -/

/-- Number of nodes of a level. -/
def size : VLevel → Nat
  | .zero | .param _ => 1
  | .succ l => size l + 1
  | .max a b | .imax a b => size a + size b + 1

/-- Size of a formula: one for each literal and one for each clause. -/
def cnfSize (φ : CNF n) : Nat := (φ.map fun C => C.length + 1).sum

theorem size_two : size two = 3 := rfl

theorem size_clauseLvl {C : Clause n} : size (clauseLvl C) = 2*C.length + 1 := by
  induction C <;> simp [clauseLvl, size] at *; omega

theorem size_foldl_imax {gs : List VLevel} (b) :
    size (gs.foldl .imax b) = size b + (gs.map fun g => size g + 1).sum := by
  induction gs generalizing b <;> simp [*, size]; omega

theorem size_gates {φ : CNF n} : size (gates φ) = 2 * cnfSize φ + 3 := by
  rw [gates, size_foldl_imax, size_two]
  suffices h : ((φ.map clauseLvl).map fun g => size g + 1).sum = 2 * cnfSize φ by omega
  induction φ <;> simp [cnfSize, size_clauseLvl] at *; omega

theorem size_var {i : Nat} : size (var i) = 9 := rfl

theorem size_small {n : Nat} : size (small n) = 10*n + 1 := by
  induction n <;> simp [small, size, size_var, *]; omega

theorem size_big {φ : CNF n} : size (big φ) = 10*n + 2 * cnfSize φ + 5 := by
  simp [big, size, size_small, size_gates]; omega

/-! ## Two worked instances

`x₀ ∧ ¬x₀` is unsatisfiable, so the two levels it produces are equivalent — this is the
case where the "obvious" reduction, reading each parameter directly as a SAT variable,
would wrongly report a difference: the rails `0⁺` and `0⁻` may perfectly well both be
nonzero, and `small` is what rules that point out. `x₀` on its own is satisfiable,
and the two levels differ at `[1, 0]`, the rail encoding of `x₀ := true`. -/

/-- `x₀ ∧ ¬x₀` is not Sat. -/
def selfContradiction : CNF 1 := [[(0, true)], [(0, false)]]

theorem not_sat_selfContradiction : ¬Sat selfContradiction := by
  rintro ⟨a, ha⟩
  obtain ⟨_, h1, h2⟩ := ha [(0, true)] (by simp [selfContradiction])
  obtain ⟨_, h3, h4⟩ := ha [(0, false)] (by simp [selfContradiction])
  simp at h1 h3
  subst h1; subst h3
  simp at h2 h4
  simp [h2] at h4

example : big selfContradiction ≈ small 1 :=
  equiv_iff_unsat.2 not_sat_selfContradiction

/-- `x₀` is Sat. -/
example : ¬(big ([[(0, true)]] : CNF 1) ≈ small 1) := fun h =>
  equiv_iff_unsat.1 h ⟨fun _ => true, by simp [ClauseSat]⟩

example : (big ([[(0, true)]] : CNF 1)).eval [1, 0] = 2 ∧ (small 1).eval [1, 0] = 1 :=
  ⟨rfl, rfl⟩
