import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.VLevel
import Lean4Lean.Verify.QSort
import Lean4Lean.Verify.NormLt

open private go in Lean.Level.geq
open private accMax mkIMaxAux isExplicitSubsumed from Lean.Level

namespace Lean.Level

open Lean4Lean

/-!
Semantic soundness of the universe-level operations in Lean's standard library.
`normalize` is an opaque `partial def`, so `Lean4Lean.Verify.Axioms` assumes it
equals the total copy `Lean.Level.Total.normalize` defined there; the semantic
behavior of that copy is `eval_normalize` below, which is still open. The exact
correspondence between `geqCore` below and the private recursion used by
`Lean.Level.geq` is proved.
-/

variable (ρ : Name → Nat) (μ : LMVarId → Nat) in
def eval : Level → Nat
  | .zero => 0
  | .param n => ρ n
  | .mvar n => μ n
  | .succ l => eval l + 1
  | .max l₁ l₂ => Nat.max (eval l₁) (eval l₂)
  | .imax l₁ l₂ => Nat.imax (eval l₁) (eval l₂)

private def offset : Level → Nat
  | .succ l => offset l + 1
  | _ => 0

private theorem getOffsetAux_eq_offset :
    l.getOffsetAux k = offset l + k := by
  induction l generalizing k with
  | succ l ih => simp only [Level.getOffsetAux, offset, ih]; omega
  | _ => simp [Level.getOffsetAux, offset]

private theorem getOffset_eq_offset : l.getOffset = offset l := by
  simp [Level.getOffset, getOffsetAux_eq_offset]

theorem eval_getLevelOffset :
    eval ρ μ l = eval ρ μ l.getLevelOffset + l.getOffset := by
  induction l with | succ l ih => ?_ | _ => rfl
  simp only [eval, Level.getLevelOffset, getOffset_eq_offset, offset, ih]
  omega

theorem fallback_sound
    (h : (u.getLevelOffset = v.getLevelOffset ∨ v.getLevelOffset.isZero = true) ∧
      v.getOffset ≤ u.getOffset) :
    eval ρ μ v ≤ eval ρ μ u := by
  rw [eval_getLevelOffset, eval_getLevelOffset (l := u)]
  rcases h with ⟨hv | hv, hk⟩
  · rw [← hv]; omega
  · have hv : v.getLevelOffset = .zero := by
      generalize hbase : v.getLevelOffset = base at hv
      cases base <;> simp_all [Level.isZero]
    simp [hv, eval]
    omega

def geqCore : Level → Level → Bool
  -- Keep this in the same source-shaped form as `go`'s `u == v || ...` prefix.
  -- The apparently redundant `|| true` is therefore deliberate.
  | u, .zero => u == .zero || true
  | u, .max v₁ v₂ => u == .max v₁ v₂ || (geqCore u v₁ && geqCore u v₂)
  | .max u₁ u₂, .imax v₁ v₂ =>
    (.max u₁ u₂ : Level) == .imax v₁ v₂ ||
      (geqCore u₁ (.imax v₁ v₂) || geqCore u₂ (.imax v₁ v₂) ||
        (geqCore (.max u₁ u₂) v₁ && geqCore (.max u₁ u₂) v₂))
  | .max u₁ u₂, v =>
    let u := .max u₁ u₂
    u == v || (geqCore u₁ v || geqCore u₂ v ||
      ((u.getLevelOffset == v.getLevelOffset || v.getLevelOffset.isZero) &&
        u.getOffset ≥ v.getOffset))
  | .imax u₁ u₂, v => (.imax u₁ u₂ : Level) == v || geqCore u₂ v
  | .succ u, .succ v => (.succ u : Level) == .succ v || geqCore u v
  | u, .imax v₁ v₂ => u == .imax v₁ v₂ || (geqCore u v₁ && geqCore u v₂)
  | u, v => u == v ||
    ((u.getLevelOffset == v.getLevelOffset || v.getLevelOffset.isZero) &&
      u.getOffset ≥ v.getOffset)
  termination_by u v => (u, v)

private theorem geqCore_eq_go : geqCore u v = go u v := by
  fun_induction go with | _ u v
  cases u <;> cases v <;> simp_all [geqCore, go]

theorem geqCore_sound (h : geqCore u v) : eval ρ μ v ≤ eval ρ μ u := by
  induction u, v using geqCore.induct with
    simp only [geqCore, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
  | case1 => simp [eval]
  | case2 _ _ _ ih₂ ih₁ =>
    rcases h with rfl | ⟨h₁, h₂⟩
    · exact Nat.le_refl _
    · exact (Nat.max_le).2 ⟨ih₂ h₁, ih₁ h₂⟩
  | case3 u₁ u₂ v₁ v₂ ih₄ ih₃ ih₂ ih₁ =>
    rcases h with heq | (h | h) | ⟨h₁, h₂⟩
    · exact Nat.le_of_eq (congrArg (eval ρ μ) heq).symm
    · exact Nat.le_trans (ih₄ h) (Nat.le_max_left ..)
    · exact Nat.le_trans (ih₃ h) (Nat.le_max_right ..)
    · simp only [eval, Nat.imax]
      split
      · exact Nat.zero_le _
      · exact (Nat.max_le).2 ⟨ih₂ h₁, ih₁ h₂⟩
  | case4 u₁ u₂ v _ _ _ ih₂ ih₁ =>
    rcases h with rfl | h
    · exact Nat.le_refl _
    · rcases h with (h | h) | h
      · exact Nat.le_trans (ih₂ h) (Nat.le_max_left ..)
      · exact Nat.le_trans (ih₁ h) (Nat.le_max_right ..)
      · exact fallback_sound h
  | case5 u₁ u₂ v _ _ ih =>
    rcases h with rfl | h
    · exact Nat.le_refl _
    · simp only [eval, Nat.imax]
      have hv := ih h
      split <;> rename_i hz
      · simpa [hz] using hv
      · exact Nat.le_trans hv (Nat.le_max_right ..)
  | case6 u v ih =>
    rcases h with heq | h
    · exact Nat.le_of_eq (congrArg (eval ρ μ) heq).symm
    · simpa [eval] using Nat.add_le_add_right (ih h) 1
  | case7 u v₁ v₂ _ _ ih₂ ih₁ =>
    rcases h with rfl | ⟨h₁, h₂⟩
    · exact Nat.le_refl _
    · simp only [eval, Nat.imax]
      split
      · exact Nat.zero_le _
      · exact (Nat.max_le).2 ⟨ih₂ h₁, ih₁ h₂⟩
  | case8 =>
    rcases h with heq | h
    · exact Nat.le_of_eq (congrArg (eval ρ μ) heq).symm
    · exact fallback_sound h

/-!
### Soundness of `normalize`

The proof is by strong induction on `Total.size`. The mutual recursion with
`getMaxArgsAux` is untangled by observing that `getMaxArgsAux l true` recurses only
structurally, and `getMaxArgsAux l false` calls `normalize` only on levels of size at
most `size l`, so both can be handled by standalone lemmas parameterized by the
induction hypothesis for `normalize`.

The `max` branch sorts the collected arguments with `qsort normLt` and then drops
dominated entries: `mkMaxAux` drops an entry when the next one has the same level base
(relying on offsets being sorted within a base class), and the explicit (constant)
entries in the sorted prefix are dropped when subsumed by the largest explicit or by
some offset to its right. All of this is justified by a single consequence of
sortedness: entries with equal `getLevelOffset` occur in order of `getOffset`
(`explicit` entries all have base `zero`, so this also orders the explicit prefix).
That fact, together with the fact that `qsort` permutes the array, are the only
properties of sorting used; they are `qsort_perm_toList` and `pairwise_qsort_normLt`
below, currently unproved because `Array.qsort` has no specification in the standard
library.
-/

theorem le_ext_le {n m : Nat} (H : ∀ x, n ≤ x → m ≤ x) : m ≤ n := H _ (Nat.le_refl _)

theorem nat_ext_le {n m : Nat} (H : ∀ x, n ≤ x ↔ m ≤ x) : n = m :=
  Nat.le_antisymm ((H _).2 (Nat.le_refl _)) ((H _).1 (Nat.le_refl _))

theorem eval_addOffset : eval ρ μ (addOffset l k) = eval ρ μ l + k := by
  suffices ∀ k l, eval ρ μ (addOffsetAux k l) = eval ρ μ l + k from this ..
  intro k; induction k with intro l
  | zero => rfl
  | succ k ih => rw [addOffsetAux, ih]; simp [eval, mkLevelSucc]; omega

theorem isZero_iff : isZero l ↔ l = .zero := by cases l <;> simp [Level.isZero]

theorem isNeverZero_sound (h : l.isNeverZero = true) : 0 < eval ρ μ l := by
  induction l with
  | zero | param | mvar => simp [isNeverZero] at h
  | succ l => simp [eval]
  | max l₁ l₂ ih₁ ih₂ =>
    simp only [isNeverZero, Bool.or_eq_true] at h
    simp only [eval, Nat.max_eq_max]
    obtain h | h := h
    · have := ih₁ h; omega
    · have := ih₂ h; omega
  | imax l₁ l₂ _ ih₂ =>
    simp only [isNeverZero] at h
    have := ih₂ h
    simp only [eval, Nat.imax, Nat.max_eq_max]; split <;> omega

theorem eval_accMax : eval ρ μ (accMax r p k) = Nat.max (eval ρ μ r) (eval ρ μ p + k) := by
  rw [accMax]; split <;> rename_i h
  · rw [isZero_iff.1 h, eval_addOffset]; simp [eval]
  · simp [mkLevelMax, eval, eval_addOffset]

theorem eval_mkIMaxAux :
    eval ρ μ (mkIMaxAux a b) = Nat.imax (eval ρ μ a) (eval ρ μ b) := by
  unfold mkIMaxAux; split
  · simp [eval, Nat.imax]
  · simp only [eval, Nat.imax]; split <;> [omega; simp]
  · simp only [eval, Nat.imax, Nat.max_eq_max]; split <;> [omega; rw [Nat.max_eq_right (by omega)]]
  · split <;> rename_i h
    · cases eq_of_beq h; simp only [Nat.imax, Nat.max_eq_max]
      split <;> [omega; rw [Nat.max_self]]
    · simp [mkLevelIMax, eval]

/-- The maximum of the evaluations of a list of levels. -/
def evalList (ρ : Name → Nat) (μ : LMVarId → Nat) (ls : List Level) : Nat :=
  ls.foldr (fun l n => Nat.max (eval ρ μ l) n) 0

theorem evalList_le_iff : evalList ρ μ ls ≤ n ↔ ∀ l ∈ ls, eval ρ μ l ≤ n := by
  induction ls with
  | nil => simp [evalList, Nat.zero_le]
  | cons l ls ih =>
    show Nat.max (eval ρ μ l) (evalList ρ μ ls) ≤ n ↔ _
    rw [Nat.max_eq_max, Nat.max_le, ih]; simp

theorem le_evalList (h : l ∈ ls) : eval ρ μ l ≤ evalList ρ μ ls :=
  evalList_le_iff.1 (Nat.le_refl _) _ h

theorem evalList_perm (h : ls₁.Perm ls₂) : evalList ρ μ ls₁ = evalList ρ μ ls₂ := by
  refine nat_ext_le fun _ => ?_; simp only [evalList_le_iff, h.mem_iff]

theorem evalList_append : evalList ρ μ (ls₁ ++ ls₂) =
    Nat.max (evalList ρ μ ls₁) (evalList ρ μ ls₂) := by
  induction ls₁ with | nil => simp [evalList] | cons l ls ih
  show Nat.max _ (evalList ρ μ (ls ++ ls₂)) = Nat.max (Nat.max _ (evalList ρ μ ls)) _
  rw [ih]; simp only [Nat.max_eq_max]; rw [Nat.max_assoc]

/-- `Array.qsort` returns a permutation of its input (`Array.qsort_perm`). -/
theorem qsort_perm (as : Array Level) : (as.qsort normLt).toList.Perm as.toList :=
  Array.perm_iff_toList_perm.1 (Array.qsort_perm normLt 0 (as.size - 1) as)

/-- Entries with equal level base come out of `qsort normLt` ordered by offset: a
consequence of sortedness (`Array.qsort_sorted`), since `normLt` compares levels with
equal bases by offset. -/
theorem pairwise_qsort (as : Array Level) :
    (as.qsort normLt).toList.Pairwise fun a b =>
      a.getLevelOffset = b.getLevelOffset → a.getOffset ≤ b.getOffset := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij hb
  simp only [Array.getElem_toList] at hb
  simpa [normLt_same_base hb.symm] using
    Array.qsort_sorted normLt normLt_asymm normLt_le_trans as i j hij hj

theorem offset_le_eval : l.getOffset ≤ eval ρ μ l := by
  rw [eval_getLevelOffset]; omega

theorem eval_of_isZero (h : l.getLevelOffset.isZero) : eval ρ μ l = l.getOffset := by
  rw [eval_getLevelOffset, isZero_iff.1 h]; simp [eval]

theorem skipExplicit_spec {lvls : Array Level} : i ≤ lvls.size →
    i ≤ Total.skipExplicit lvls i ∧ Total.skipExplicit lvls i ≤ lvls.size ∧
    ∀ j (_ : j < lvls.size), i ≤ j → j < Total.skipExplicit lvls i →
      lvls[j].getLevelOffset.isZero := by
  fun_induction Total.skipExplicit lvls i with
  | case1 i hi hz ih =>
    intro h
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    refine ⟨by omega, ih2, fun j hj hij hlt => ?_⟩
    rcases Nat.eq_or_lt_of_le hij with rfl | hij'
    · exact hz
    · exact ih3 j hj (by omega) hlt
  | case2 i hi hz => exact fun h => ⟨Nat.le_refl _, by omega, fun j hj hij hlt => by omega⟩
  | case3 i hi => exact fun h => ⟨Nat.le_refl _, by omega, fun j hj hij hlt => by omega⟩

theorem isExplicitSubsumedAux_spec {lvls : Array Level} :
    Total.isExplicitSubsumedAux lvls mx i = true ↔
      ∃ j, i ≤ j ∧ ∃ (_ : j < lvls.size), mx ≤ lvls[j].getOffset := by
  fun_induction Total.isExplicitSubsumedAux lvls mx i with
  | case1 i hi hge => simpa using ⟨i, Nat.le_refl _, hi, by omega⟩
  | case2 i hi hlt ih =>
    rw [ih]
    constructor <;> rintro ⟨j, hij, hj, hle⟩ <;> refine ⟨j, ?_, hj, hle⟩
    · omega
    · obtain rfl | h := Nat.eq_or_lt_of_le hij <;> omega
  | case3 i hi => simp; rintro j hij hj; omega

theorem eval_mkMaxAux {lvls : Array Level}
    (hs : ∀ (i j : Nat) (hi : i < lvls.size) (hj : j < lvls.size), i < j →
      lvls[i].getLevelOffset = lvls[j].getLevelOffset → lvls[i].getOffset ≤ lvls[j].getOffset)
    (hfuel : lvls.size ≤ i + fuel)
    (hi0 : 0 < i) (hile : i ≤ lvls.size)
    (hp : ∀ h : i - 1 < lvls.size, prev = lvls[i-1].getLevelOffset ∧ prevK = lvls[i-1].getOffset) :
    eval ρ μ (Total.mkMaxAux lvls extraK i prev prevK result) =
      Nat.max (eval ρ μ result) (evalList ρ μ (lvls.toList.drop (i-1)) + extraK) := by
  induction fuel generalizing i result prev prevK with
  | zero =>
    have hie : i = lvls.size := by omega
    obtain ⟨hp, hpk⟩ := hp (by omega)
    rw [Total.mkMaxAux.eq_def, dif_neg (by omega), eval_accMax]
    have hlast : i - 1 < lvls.size := by omega
    have hdrop : lvls.toList.drop (i-1) = [lvls[i-1]] := by
      rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; omega)]
      simp [hie]; omega
    have : eval ρ μ lvls[i-1] = eval ρ μ prev + prevK := by
      rw [eval_getLevelOffset (l := lvls[i-1]), hp, hpk]
    rw [hdrop]
    simp only [evalList, List.foldr_cons, List.foldr_nil, this, Nat.max_eq_max]
    omega
  | succ fuel ih =>
    rw [Total.mkMaxAux.eq_def]
    split <;> rename_i hlt
    · obtain ⟨hp, hpk⟩ := hp (by omega)
      have hlast : i - 1 < lvls.size := by omega
      have hdrop : lvls.toList.drop (i-1) = lvls[i-1] :: lvls.toList.drop i := by
        rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; omega)]
        simp; congr 1; omega
      have heval : eval ρ μ lvls[i-1] = eval ρ μ prev + prevK := by
        rw [eval_getLevelOffset (l := lvls[i-1]), hp, hpk]
      have hmem : eval ρ μ lvls[i] ≤ evalList ρ μ (lvls.toList.drop i) :=
        le_evalList (by rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; omega)]; exact .head _)
      dsimp only
      split <;> rename_i hbeq
      · -- equal bases: drop the previous entry
        rw [ih (i := i+1) (by omega) (by omega) (by omega) (fun h => by simp)]
        have hb : lvls[i].getLevelOffset = prev := eq_of_beq hbeq
        have hk : prevK ≤ lvls[i].getOffset := by
          rw [hpk]; exact hs (i-1) i hlast hlt (by omega) (by rw [hb, hp])
        have hle : eval ρ μ lvls[i-1] ≤ evalList ρ μ (lvls.toList.drop i) := by
          refine Nat.le_trans ?_ hmem
          rw [heval, eval_getLevelOffset (l := lvls[i]), hb, hp]
          omega
        rw [Nat.add_sub_cancel, hdrop]
        have : evalList ρ μ (lvls[i-1] :: lvls.toList.drop i) =
            evalList ρ μ (lvls.toList.drop i) := by
          exact Nat.max_eq_right hle
        rw [this]
      · -- new base: accumulate the previous entry
        rw [ih (i := i+1) (by omega) (by omega) (by omega) (fun h => by simp)]
        rw [Nat.add_sub_cancel, eval_accMax, hdrop]
        simp only [evalList, List.foldr_cons, Nat.max_eq_max, heval]
        omega
    · have hie : i = lvls.size := by omega
      obtain ⟨hp, hpk⟩ := hp (by omega)
      rw [eval_accMax]
      have hlast : i - 1 < lvls.size := by omega
      have hdrop : lvls.toList.drop (i-1) = [lvls[i-1]] := by
        rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; omega)]
        simp [hie]; omega
      have : eval ρ μ lvls[i-1] = eval ρ μ prev + prevK := by
        rw [eval_getLevelOffset (l := lvls[i-1]), hp, hpk]
      rw [hdrop]
      simp only [evalList, List.foldr_cons, List.foldr_nil, this, Nat.max_eq_max]
      omega

theorem size_lt_getMaxArgsAux_true :
    lvls.size < (Total.getMaxArgsAux l true lvls).size := by
  induction l generalizing lvls with
  | max _ _ ih₁ ih₂ => exact Total.getMaxArgsAux.eq_def .. ▸ Nat.lt_trans ih₁ ih₂
  | _ => rw [Total.getMaxArgsAux.eq_def]; simp

theorem size_lt_getMaxArgsAux_false :
    lvls.size < (Total.getMaxArgsAux l false lvls).size := by
  induction l generalizing lvls with
  | max _ _ ih₁ ih₂ => exact Total.getMaxArgsAux.eq_def .. ▸ Nat.lt_trans ih₁ ih₂
  | _ => exact Total.getMaxArgsAux.eq_def .. ▸ size_lt_getMaxArgsAux_true ..

theorem evalList_getMaxArgsAux_true :
    evalList ρ μ (Total.getMaxArgsAux l true lvls).toList =
      Nat.max (evalList ρ μ lvls.toList) (eval ρ μ l) := by
  induction l generalizing lvls with
  | max l₁ l₂ ih₁ ih₂ =>
    rw [Total.getMaxArgsAux, ih₂, ih₁]
    simp only [eval, Nat.max_eq_max]; omega
  | _ =>
    rw [Total.getMaxArgsAux.eq_def, Array.toList_push, evalList_append]
    simp only [evalList, List.foldr_cons, List.foldr_nil, Nat.max_eq_max]; omega

theorem evalList_getMaxArgsAux_false {l : Level}
    (IH : ∀ u, Total.size u ≤ Total.size l → eval ρ μ (Total.normalize u) = eval ρ μ u) :
    evalList ρ μ (Total.getMaxArgsAux l false lvls).toList =
      Nat.max (evalList ρ μ lvls.toList) (eval ρ μ l) := by
  induction l generalizing lvls with
  | max l₁ l₂ ih₁ ih₂ =>
    rw [Total.getMaxArgsAux.eq_def]
    show evalList ρ μ (Total.getMaxArgsAux l₂ false (Total.getMaxArgsAux l₁ false lvls)).toList = _
    rw [ih₂ (fun u hu => IH u (by simp only [Total.size] at *; omega)),
      ih₁ (fun u hu => IH u (by simp only [Total.size] at *; omega))]
    simp only [eval, Nat.max_eq_max]; omega
  | _ => rw [Total.getMaxArgsAux.eq_def, evalList_getMaxArgsAux_true, IH _ (Nat.le_refl _)]

/-- Dropping a dominated prefix does not change the maximum. -/
theorem evalList_drop_eq {ls : List Level} (hstart : start ≤ ls.length)
    (hdom : ∀ j (hj : j < ls.length), j < start →
      eval ρ μ ls[j] ≤ evalList ρ μ (ls.drop start)) :
    evalList ρ μ (ls.drop start) = evalList ρ μ ls := by
  refine nat_ext_le fun n => ?_
  simp only [evalList_le_iff]
  constructor <;> intro H l hl
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hl
    by_cases hjs : j < start
    · exact Nat.le_trans (hdom j hj hjs) (evalList_le_iff.2 H)
    · refine H _ (List.mem_iff_getElem.2 ⟨j - start, by simp; omega, ?_⟩)
      rw [List.getElem_drop]; congr 1; omega
  · exact H l (List.drop_subset _ _ hl)

/-- The level base of a level that is not already normalized is a `max` or an `imax`. -/
theorem base_of_not_cheap {l : Level} (h : ¬l.isAlreadyNormalizedCheap = true) :
    (∃ a b, l.getLevelOffset = .max a b) ∨ (∃ a b, l.getLevelOffset = .imax a b) := by
  induction l with
  | succ l ih => apply ih; simpa [isAlreadyNormalizedCheap] using h
  | max l₁ l₂ => exact .inl ⟨_, _, rfl⟩
  | imax l₁ l₂ => exact .inr ⟨_, _, rfl⟩
  | _ => simp [isAlreadyNormalizedCheap] at h

theorem eval_normalize_total {l : Level} : eval ρ μ (Total.normalize l) = eval ρ μ l := by
  generalize hn : Total.size l = n
  induction n using Nat.strongRecOn generalizing l with | _ n IH
  subst hn
  rw [Total.normalize.eq_def]
  split <;> [rfl; rename_i hcheap]
  have hsz := Total.size_getLevelOffset l
  split <;> [rename_i l₁ l₂ hbase; rename_i l₁ l₂ hbase; skip]
  · -- max
    rw [eval_getLevelOffset (l := l), hbase]
    rw [hbase] at hsz; simp only [Total.size] at hsz
    have hs₁ := Total.one_le_size l₁
    have hs₂ := Total.one_le_size l₂
    have IH₁ u (hu : Total.size u ≤ Total.size l₁) : eval ρ μ (Total.normalize u) = eval ρ μ u :=
      IH _ (by omega) rfl
    have IH₂ u (hu : Total.size u ≤ Total.size l₂) : eval ρ μ (Total.normalize u) = eval ρ μ u :=
      IH _ (by omega) rfl
    extract_lets k lvls₁ L1 L i₀ i lvl₁ prev prevK
    have hevalL1 : evalList ρ μ L1.toList = Nat.max (eval ρ μ l₁) (eval ρ μ l₂) := by
      rw [evalList_getMaxArgsAux_false IH₂, evalList_getMaxArgsAux_false IH₁]
      simp [evalList, Nat.max_eq_max]
    have hL1pos : 0 < L1.size :=
      Nat.lt_trans (size_lt_getMaxArgsAux_false (lvls := #[])) size_lt_getMaxArgsAux_false
    have hperm : L.toList.Perm L1.toList := qsort_perm L1
    have hpair : List.Pairwise _ L.toList := pairwise_qsort L1
    have hLsize : L.size = L1.size := by
      simpa [Array.length_toList] using hperm.length_eq
    have hLpos : 0 < L.size := hLsize ▸ hL1pos
    have hevalL : evalList ρ μ L.toList = Nat.max (eval ρ μ l₁) (eval ρ μ l₂) := by
      rw [evalList_perm hperm, hevalL1]
    have hs : ∀ (i j : Nat) (hi : i < L.size) (hj : j < L.size), i < j →
        L[i].getLevelOffset = L[j].getLevelOffset → L[i].getOffset ≤ L[j].getOffset := by
      intro i j hi hj hij hb
      have := (List.pairwise_iff_getElem.1 hpair) i j (by simpa using hi) (by simpa using hj) hij
      simpa using this (by simpa using hb)
    obtain ⟨-, hskle, hskz⟩ := skipExplicit_spec (lvls := L) (i := 0) (Nat.zero_le _)
    -- the start index and its bound
    have main i (hi : i < L.size)
        (hdom : ∀ j (hj : j < L.size), j < i → eval ρ μ L[j] ≤ evalList ρ μ (L.toList.drop i)) :
        eval ρ μ (Total.mkMaxAux L (l.getOffset) (i+1) L[i]!.getLevelOffset L[i]!.getOffset
          Level.zero) = Nat.max (eval ρ μ l₁) (eval ρ μ l₂) + l.getOffset := by
      rw [getElem!_pos L i hi,
        eval_mkMaxAux hs (fuel := L.size) (by omega) (by omega) (by omega) (fun _ => by simp),
        Nat.add_sub_cancel, evalList_drop_eq (by rw [Array.length_toList]; omega) hdom, hevalL]
      simp [eval, Nat.max_eq_max]
    subst i lvl₁ prevK prev; split <;> rename_i hsub
    · -- explicits subsumed: start at the first non-explicit
      rw [isExplicitSubsumed] at hsub
      split at hsub <;> [cases hsub; let (eq := eq) i'+1 := i₀]; subst i₀
      simp only [isExplicitSubsumedAux_eq, isExplicitSubsumedAux_spec] at hsub
      obtain ⟨j, hij, hjs, hmax⟩ := hsub; dsimp at hmax
      refine main (i'+1) (by omega) fun m hm hmi => ?_
      -- every dropped explicit is at most the witness entry
      have hzm : L[m].getLevelOffset.isZero := hskz m hm (Nat.zero_le _) (eq ▸ hmi)
      have hz₁ := hskz i' (by omega) (Nat.zero_le _) (by omega)
      have h2 : L[m].getOffset ≤ L[i'].getOffset := by
        rcases Nat.eq_or_lt_of_le (Nat.le_pred_of_lt hmi) with h | h
        · subst h; exact Nat.le_refl _
        · exact hs m i' hm (by omega) h (by rw [isZero_iff.1 hzm, isZero_iff.1 hz₁])
      have h3 : L[i'].getOffset ≤ eval ρ μ L[j] :=
        Nat.le_trans (getElem!_pos L i' (by omega) ▸ hmax) offset_le_eval
      refine eval_of_isZero hzm ▸ Nat.le_trans (Nat.le_trans h2 h3) (le_evalList ?_)
      refine List.mem_iff_getElem.2 ⟨j - (i' + 1), ?_, ?_⟩
      · simp only [List.length_drop, Array.length_toList]; omega
      · rw [List.getElem_drop]; simp only [Array.getElem_toList]; congr 1; omega
    · -- keep the largest explicit
      cases eq : i₀ with | zero => exact main 0 (by omega) (fun m hm hmi => by omega) | succ i'
      have hstart : i' < L.size := by omega
      refine main i' hstart fun m hm hmi => ?_
      have hzm : L[m].getLevelOffset.isZero := hskz m hm (Nat.zero_le _) (by omega)
      have hz₁ : L[i'].getLevelOffset.isZero :=
        hskz i' hstart (Nat.zero_le _) (by omega)
      refine eval_of_isZero hzm ▸ Nat.le_trans (hs m i' hm hstart (by omega) ?_) ?_
      · rw [isZero_iff.1 hzm, isZero_iff.1 hz₁]
      refine eval_of_isZero hz₁ ▸ le_evalList ?_
      rw [List.drop_eq_getElem_cons (by omega)]; exact .head _
  · -- imax
    rw [eval_getLevelOffset (l := l), hbase]
    rw [hbase] at hsz; simp only [Total.size] at hsz
    have hs₁ := Total.one_le_size l₁
    have hs₂ := Total.one_le_size l₂
    split <;> rename_i hnz
    · rw [eval_addOffset, IH (Total.size (mkLevelMax l₁ l₂))
        (by simp only [mkLevelMax, Total.size]; omega) rfl]
      have := isNeverZero_sound (ρ := ρ) (μ := μ) hnz
      simp only [mkLevelMax, eval, Nat.imax]
      rw [if_neg (by omega)]
    · rw [eval_addOffset, eval_mkIMaxAux, IH _ (by omega) rfl, IH _ (by omega) rfl]; rfl
  · grind [base_of_not_cheap]

theorem eval_normalize {ρ μ l} : eval ρ μ l.normalize = eval ρ μ l := by
  rw [normalize_eq]; exact eval_normalize_total

theorem geq_eq_core : geq u v = geqCore (normalize u) (normalize v) := by
  simp [geq, geqCore_eq_go]

theorem isEquiv_sound (h : isEquiv u v) : eval ρ μ u = eval ρ μ v := by
  simp only [Level.isEquiv, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h <;> [rfl; skip]
  rw [← eval_normalize (l := u), ← eval_normalize (l := v), h]

theorem geq_sound (h : geq u v) : eval ρ μ v ≤ eval ρ μ u := by
  rw [geq_eq_core] at h
  rw [← eval_normalize (l := u), ← eval_normalize (l := v)]
  exact geqCore_sound h

theorem eval_ofLevel (h : VLevel.ofLevel Us l = some l') :
    l'.eval ns = eval (fun n => ns.getD (Us.idxOf n) 0) μ l := by
  induction l generalizing l' with
  | zero => simp [VLevel.ofLevel] at h; cases h; rfl
  | succ l ih =>
    simp [VLevel.ofLevel, bind] at h
    obtain ⟨l', hl, rfl⟩ := h
    simp [VLevel.eval, eval, ih hl]
  | max l₁ l₂ ih₁ ih₂ | imax l₁ l₂ ih₁ ih₂ =>
    simp [VLevel.ofLevel, bind] at h
    obtain ⟨l₁', hl₁, l₂', hl₂, rfl⟩ := h
    simp [VLevel.eval, eval, ih₁ hl₁, ih₂ hl₂]
  | param n =>
    simp [VLevel.ofLevel] at h
    obtain ⟨hidx, rfl⟩ := h
    simp [VLevel.eval, eval]
  | mvar n => simp [VLevel.ofLevel] at h

theorem isEquiv_wf (h : isEquiv u v)
    (hu : VLevel.ofLevel Us u = some u') (hv : VLevel.ofLevel Us v = some v') : u' ≈ v' := by
  refine VLevel.equiv_def.2 fun ns => ?_
  rw [eval_ofLevel (μ := fun _ => 0) hu, eval_ofLevel (μ := fun _ => 0) hv]
  exact isEquiv_sound h

theorem geq_wf (h : geq u v)
    (hu : VLevel.ofLevel Us u = some u') (hv : VLevel.ofLevel Us v = some v') : v' ≤ u' := by
  intro ns
  rw [eval_ofLevel (μ := fun _ => 0) hv, eval_ofLevel (μ := fun _ => 0) hu]
  exact geq_sound h

end Lean.Level
