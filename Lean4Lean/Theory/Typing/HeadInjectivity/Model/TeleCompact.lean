import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Tele
import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.Typing

/-! # Typed finite sub-valuations of a telescope

A typed valuation `(argSubst as, Sx)` of a closed telescope `D` (outermost binder first) has,
below any finite demand on the observation sets of its variables, typed keys along `D`
whose observation lists are finite subsets of the sets of `Sx` (`Model.tele_compact`). The
keys are built from the innermost binder outwards: the last binder's list is the backed
closure of its demand; its members are typed at observations of the binder's domain, which
by compactness (`Obs.compact`, closedness of the domain) use finitely many observations of the
earlier variables; those are added to the earlier demands. -/

namespace Lean4Lean
namespace VEnv
namespace Model
open VExpr

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- Replace the first `G.length` observation sets by the finite lists of `G`. -/
def fillS (S : ObSets) (G : List (List Ob)) : ObSets :=
  fun m => if h : m < G.length then listSet G[m] else S m

/-- **Compactness at all free variables** of a list of observations of a term closed at
`k`: finitely many observations of each of the `k` variables suffice. -/
theorem Obs.compact_all {t : VExpr} {k : Nat} (ht : t.ClosedN k) {σ : VExpr.Subst} {S : ObSets}
    {τs : List Ob} (hτ : ∀ τ ∈ τs, Obs' σ S t τ) :
    ∃ G : List (List Ob), G.length = k ∧ (∀ m (hm : m < G.length), ∀ y ∈ G[m], S m y) ∧
      ∀ S' : ObSets, (∀ m (hm : m < G.length), ∀ y ∈ G[m], S' m y) →
        ∀ τ ∈ τs, Obs' σ S' t τ := by
  -- fill the first `j` sets, one index at a time
  have key : ∀ j, j ≤ k → ∃ G : List (List Ob), G.length = j ∧
      (∀ m (hm : m < G.length), ∀ y ∈ G[m], S m y) ∧ ∀ τ ∈ τs, Obs' σ (fillS S G) t τ := by
    intro j
    induction j with
    | zero =>
      have h0 : fillS S [] = S := by funext m; simp [fillS]
      exact fun _ => ⟨[], rfl, fun m hm => absurd hm (by simp),
        fun τ hτ' => h0 ▸ hτ τ hτ'⟩
    | succ j ih =>
      intro hj
      obtain ⟨G, hGl, hGS, hG⟩ := ih (by omega)
      obtain ⟨K, hK, hKτ⟩ := Obs.collect
        (Q := fun y => fillS S G j y)
        (P := fun K τ => Obs' σ ((fillS S G).update j (listSet K)) t τ)
        (fun _ _ _ hK h => h.mono (Obs.update_mono hK))
        (fun τ hτ' => Obs.compact (hG τ hτ') j)
      have hfj : ∀ y, fillS S G j y → S j y := by
        intro y hy; simpa [fillS, hGl] using hy
      have hfill : (fillS S G).update j (listSet K) = fillS S (G ++ [K]) := by
        funext m o
        simp only [ObSets.update, fillS, List.length_append, List.length_singleton]
        by_cases hm : m = j
        · subst hm; simp [hGl]
        · by_cases hm' : m < G.length
          · simp [hm, hm', List.getElem_append_left hm', show m < G.length + 1 by omega]
          · simp [hm, hm', show ¬ m < G.length + 1 by omega]
      refine ⟨G ++ [K], by simp [hGl], fun m hm y hy => ?_, fun τ hτ' => hfill ▸ hKτ τ hτ'⟩
      simp only [List.length_append, List.length_singleton] at hm
      by_cases hm' : m < G.length
      · rw [List.getElem_append_left hm'] at hy; exact hGS m hm' y hy
      · obtain rfl : m = G.length := by omega
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_singleton] at hy
        rw [hGl]; exact hfj y (hK y hy)
  obtain ⟨G, hGl, hGS, hG⟩ := key k (Nat.le_refl _)
  refine ⟨G, hGl, hGS, fun S' hS' τ hτ' => ?_⟩
  have h1 := (hG τ hτ').mono (S' := fun m => if m < k then S' m else S m) fun m o h => by
    simp only [fillS] at h
    split at h
    · rename_i hm; rw [if_pos (hGl ▸ hm)]; exact hS' m hm o h
    · rename_i hm; rw [if_neg (hGl ▸ hm)]; exact h
  exact (Obs.closed_iff ht (fun _ _ => rfl) fun m hm => by simp [hm]).1 h1

/-- A typed valuation of `A :: Γ` at `τ.cons a` splits into the typing of the observations of
the new variable and a typed valuation of `Γ`. -/
theorem TV.cons_inv {A : VExpr} {Γ : List VExpr} {τ : VExpr.Subst} {a : VExpr} {S : ObSets}
    (h : TV env U Δ (A :: Γ) (τ.cons a) S) :
    (∀ y, S 0 y → TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst τ)) a) τ
      (fun m => S (m + 1)) A y) ∧ TV env U Δ Γ τ (fun m => S (m + 1)) := by
  have hS : S = ObSets.cons (fun m => S (m + 1)) (S 0) := by
    funext i; cases i <;> rfl
  rw [hS] at h
  refine ⟨fun y hy => ?_, fun i => h.1 (i + 1), fun i B hL o ho => ?_⟩
  · obtain ⟨τs, h1, h2⟩ := h.2 0 _ .zero y hy
    rw [vcls_bvar_zero] at h2
    exact ⟨τs, fun x hx => Obs.lift_cons_iff.1 (h1 x hx), h2⟩
  · obtain ⟨τs, h1, h2⟩ := h.2 (i + 1) _ (.succ hL) o ho
    rw [vcls_bvar_succ] at h2
    exact ⟨τs, fun x hx => Obs.lift_cons_iff.1 (h1 x hx), h2⟩

/-- Extending typed keys by one binder at the inner end. -/
theorem TeleKeys.snoc {σ σ₁ : VExpr.Subst} {S S₁ : ObSets} {ds : List VExpr} {keys : List Key}
    (h : TeleKeys env U Δ σ S ds keys σ₁ S₁)
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ₁)) c) (hy : c y)
    (hK : ∀ k ∈ K, TypedAt env U Δ c σ₁ S₁ A k) (hb : Backed (listSet K)) :
    TeleKeys env U Δ σ S (ds ++ [A]) (keys ++ [(TyCls env U Δ (A.subst σ₁), c, K)])
      (σ₁.cons y) (S₁.cons (listSet K)) := by
  induction h with
  | nil => exact .cons hc hy hK hb .nil
  | cons hc' hy' hK' hb' _ ih => exact .cons hc' hy' hK' hb' (ih hc hK)

/-- The induction of `tele_compact`, on the length of the telescope. -/
theorem tele_compact_aux :
    ∀ (n : Nat) {D as : List VExpr} {Sx : ObSets}, D.length = n →
      (∀ i (hi : i < D.length), (D[i]).ClosedN i) → as.length = D.length →
      Ctx.SubstEq env U Δ (argSubst as) (argSubst as) D.reverse →
      TV env U Δ D.reverse (argSubst as) Sx →
      ∀ (F : List (List Ob)), F.length = D.length →
      (∀ i Fi, F[i]? = some Fi → ∀ y ∈ Fi, Sx (D.length - 1 - i) y) →
      ∃ (keys : List Key) (S' : ObSets),
        TeleKeys env U Δ .id .empty D keys (argSubst as) S' ∧ keys.length = D.length ∧
        (∀ m k, keys[D.length - 1 - m]? = some k → m < D.length → ∀ o, S' m o ↔ o ∈ k.2.2) ∧
        ∀ i k, keys[i]? = some k →
          (∀ Fi, F[i]? = some Fi → ∀ y ∈ Fi, y ∈ k.2.2) ∧
          (∀ y ∈ k.2.2, Sx (D.length - 1 - i) y) ∧
          ∃ a A, as[i]? = some a ∧ D[i]? = some A ∧
            k.2.1 = ElCls env U Δ (TyCls env U Δ (A.subst (argSubst (as.take i)))) a := by
  intro n
  induction n with
  | zero =>
    intro D as Sx hn _ has _ _ F _ _
    obtain rfl : D = [] := List.length_eq_zero_iff.mp hn
    obtain rfl : as = [] := List.length_eq_zero_iff.mp (by simpa using has)
    refine ⟨[], .empty, .nil, rfl, fun m k hk => by simp at hk, fun i k hk => by simp at hk⟩
  | succ n ih =>
    intro D as Sx hn hcl has W tv F hF hFS
    obtain ⟨D', A, rfl, hD'⟩ := List.exists_snoc_of_length_succ hn
    obtain ⟨as', a, rfl, has'⟩ := List.exists_snoc_of_length_succ (has.trans hn)
    simp only [List.length_append, List.length_singleton, hD', Nat.add_sub_cancel] at hF hFS ⊢
    rw [VExpr.argSubst_append_one] at W tv ⊢
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at W tv
    obtain ⟨htyA, tv'⟩ := TV.cons_inv tv
    cases W with
    | cons W' hA ha =>
    rw [VExpr.Subst.cons_tail] at W'
    rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail] at ha
    -- the last binder: the backed closure of its demand
    have hFn : F[n]? = some (F.getD n []) := by
      rw [List.getElem?_eq_getElem (by omega)]; simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show n < F.length by omega)]
    obtain ⟨KL, hKL1, hKL2, hKLb⟩ := Backed.close (tv.1 0) (K := F.getD n [])
      (fun y hy => by simpa using hFS n _ hFn y hy)
    have hKLt : ∀ k ∈ KL, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst (argSubst as'))) a)
        (argSubst as') (fun m => Sx (m + 1)) A k := fun k hk => htyA k (hKL2 k hk)
    obtain ⟨τs, hτs, hτK⟩ := TypedAt.merge hKLt
    have hclA : A.ClosedN n := by
      have := hcl D'.length (by simp)
      simp only [List.getElem_concat_length] at this
      rwa [hD'] at this
    obtain ⟨G, hGl, hGS, hG⟩ := Obs.compact_all hclA hτs
    -- the prefix, with the added demands
    let F' : List (List Ob) := (List.range n).map fun p => F.getD p [] ++ G.getD (n - 1 - p) []
    have hF'l : F'.length = D'.length := by simp [F', hD']
    have hF'S : ∀ i Fi, F'[i]? = some Fi → ∀ y ∈ Fi, Sx (D'.length - 1 - i + 1) y := by
      intro i Fi hi y hy
      simp only [F', List.getElem?_map] at hi
      by_cases hin : i < n
      · rw [List.getElem?_range hin] at hi
        cases hi
        rcases List.mem_append.mp hy with hy | hy
        · have hFi : F[i]? = some (F.getD i []) := by
            rw [List.getElem?_eq_getElem (by omega)]
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < F.length by omega)]
          have := hFS i _ hFi y hy
          rwa [show n - i = D'.length - 1 - i + 1 by omega] at this
        · have hGm : n - 1 - i < G.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hGm, Option.getD_some] at hy
          have := hGS _ hGm y hy
          rwa [show n - 1 - i + 1 = D'.length - 1 - i + 1 by omega] at this
      · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
    obtain ⟨keys', S₁, hT, hkl, hS₁, hkeys⟩ := ih (D := D') (as := as')
      (Sx := fun m => Sx (m + 1)) hD'
      (fun i hi => by
        have := hcl i (by simp; omega)
        rwa [List.getElem_append_left hi] at this)
      (has'.trans hD'.symm) W' tv' F' hF'l hF'S
    -- the last binder's keys are typed at the prefix sets
    have hτS₁ : ∀ τ ∈ τs, Obs' (argSubst as') S₁ A τ := by
      refine hG S₁ fun m hm y hy => ?_
      have hk : ∃ k, keys'[D'.length - 1 - m]? = some k :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨k, hk⟩ := hk
      refine (hS₁ m k hk (by omega) y).2 ?_
      refine (hkeys _ k hk).1 (F.getD (D'.length - 1 - m) [] ++
        G.getD (n - 1 - (D'.length - 1 - m)) []) ?_ y ?_
      · simp only [F', List.getElem?_map, List.getElem?_range (show D'.length - 1 - m < n by omega),
          Option.map_some]
      · refine List.mem_append_right _ ?_
        rw [List.getD_eq_getElem?_getD, show n - 1 - (D'.length - 1 - m) = m by omega,
          List.getElem?_eq_getElem hm, Option.getD_some]
        exact hy
    have hc := TypedElCls.of_hasType (env := env) (U := U) (Δ := Δ) ha
    refine ⟨keys' ++ [(TyCls env U Δ (A.subst (argSubst as')),
        ElCls env U Δ (TyCls env U Δ (A.subst (argSubst as'))) a, KL)],
      S₁.cons (listSet KL), hT.snoc hc .self (fun k hk => ⟨τs, hτS₁, hτK k hk⟩) hKLb,
      by simp [hkl, hD'], fun m k hk hm o => ?_, fun i k hk => ?_⟩
    · cases m with
      | zero =>
        rw [show n - 0 = keys'.length by omega, List.getElem?_append_right
          (Nat.le_refl _), Nat.sub_self] at hk
        cases hk; rfl
      | succ m =>
        rw [List.getElem?_append_left (by omega)] at hk
        exact hS₁ m k (by rw [show D'.length - 1 - m = n - (m + 1) by omega]; exact hk)
          (by omega) o
    · by_cases hi : i < keys'.length
      · rw [List.getElem?_append_left hi] at hk
        obtain ⟨h1, h2, a', A', h3, h4, h5⟩ := hkeys i k hk
        refine ⟨fun Fi hFi y hy => h1 (F.getD i [] ++ G.getD (n - 1 - i) []) ?_ y
            (List.mem_append_left (G.getD (n - 1 - i) []) ?_), fun y hy => ?_,
          a', A', by rw [List.getElem?_append_left (by omega)]; exact h3,
          by rw [List.getElem?_append_left (by omega)]; exact h4, ?_⟩
        · simp only [F', List.getElem?_map, List.getElem?_range (show i < n by omega),
            Option.map_some]
        · rw [List.getD_eq_getElem?_getD, hFi, Option.getD_some]; exact hy
        · have := h2 y hy
          rwa [show D'.length - 1 - i + 1 = n - i by omega] at this
        · rw [List.take_append_of_le_length (by omega)]; exact h5
      · have hi' : i = keys'.length := by
          have := (List.getElem?_eq_some_iff.mp hk).1; simp at this; omega
        subst hi'
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hk
        cases hk
        refine ⟨fun Fi hFi y hy => hKL1 y ?_, fun y hy => ?_, a, A, ?_, ?_, ?_⟩
        · rw [hkl, hD'] at hFi; rw [hFn] at hFi; cases hFi; exact hy
        · rw [show n - keys'.length = 0 by omega]; exact hKL2 y hy
        · rw [List.getElem?_append_right (by omega), show keys'.length - as'.length = 0 by omega]
          rfl
        · rw [List.getElem?_append_right (by omega), show keys'.length - D'.length = 0 by omega]
          rfl
        · rw [List.take_left' (by omega)]

/-- **Typed finite sub-valuation.** Below a finite demand `F` (`F[i]` for the `i`-th binder,
outermost first) on the observation sets of a typed valuation `(argSubst as, Sx)` of a closed
telescope `D`, there are typed keys along `D` at the anchor `argSubst as`, whose `i`-th
observation list contains the demand and lies in `Sx (D.length - 1 - i)`, and whose `i`-th
class is the element class of `as[i]` at the type class of the instantiated `i`-th domain.
The extended observation sets `S'` are the keys' lists (innermost binder at index `0`). -/
theorem tele_compact {D as : List VExpr} {Sx : ObSets}
    (hcl : ∀ i (hi : i < D.length), (D[i]).ClosedN i) (has : as.length = D.length)
    (W : Ctx.SubstEq env U Δ (argSubst as) (argSubst as) D.reverse)
    (tv : TV env U Δ D.reverse (argSubst as) Sx)
    (F : List (List Ob)) (hF : F.length = D.length)
    (hFS : ∀ i Fi, F[i]? = some Fi → ∀ y ∈ Fi, Sx (D.length - 1 - i) y) :
    ∃ (keys : List Key) (S' : ObSets),
      TeleKeys env U Δ .id .empty D keys (argSubst as) S' ∧ keys.length = D.length ∧
      (∀ m k, keys[D.length - 1 - m]? = some k → m < D.length → ∀ o, S' m o ↔ o ∈ k.2.2) ∧
      ∀ i k, keys[i]? = some k →
        (∀ Fi, F[i]? = some Fi → ∀ y ∈ Fi, y ∈ k.2.2) ∧
        (∀ y ∈ k.2.2, Sx (D.length - 1 - i) y) ∧
        ∃ a A, as[i]? = some a ∧ D[i]? = some A ∧
          k.2.1 = ElCls env U Δ (TyCls env U Δ (A.subst (argSubst (as.take i)))) a :=
  tele_compact_aux _ rfl hcl has W tv F hF hFS

end Model
end VEnv
end Lean4Lean
