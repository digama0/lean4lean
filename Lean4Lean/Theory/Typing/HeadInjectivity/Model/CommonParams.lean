import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Classes
import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.FamilyHeader

/-! # Transport of telescope instantiations across parameter conversions

Two telescopes `own` and `pdoms` that are both context-convertible to a common telescope
`params` (as the family header's and the constructor's parameter domains are, by
`VEnv.ProjDeclAt.familyTele_data`) are instantiated by the same arguments: a substitution
typed along a prefix of `own` is typed along the same prefix of `pdoms`, and the
instantiated domains have the same type class (`VEnv.Model.paramBridge`). Each domain is
related by two sort-typed links at possibly different sorts, `own_i ~ params_i ~ pdoms_i`,
which type classes absorb, so no uniqueness of types is needed. -/

namespace Lean4Lean
namespace VEnv
namespace Model
open VExpr

variable {env : VEnv} {U : Nat}

private theorem ctx_instL {U' : Nat} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    IsDefEqCtx env U' [] Γ₁ Γ₂ →
      IsDefEqCtx env U [] (Γ₁.map (·.instL ls)) (Γ₂.map (·.instL ls))
  | .zero => .zero
  | .succ h1 h2 => .succ (ctx_instL hls h1) (by simpa [VExpr.instL] using h2.instL hls)

private theorem ctx_drop {U' : Nat} :
    ∀ (j : Nat) {Γ₁ Γ₂ : List VExpr}, IsDefEqCtx env U' [] Γ₁ Γ₂ →
      IsDefEqCtx env U' [] (Γ₁.drop j) (Γ₂.drop j)
  | 0, _, _, H => by simpa using H
  | j + 1, _, _, .zero => by simpa using (IsDefEqCtx.zero : IsDefEqCtx env U' [] [] [])
  | j + 1, _, _, .succ H _ => by simpa using ctx_drop j H

private theorem ctx_snoc {U' : Nat} {A B : List VExpr} {a b : VExpr}
    (H : IsDefEqCtx env U' [] (A ++ [a]).reverse (B ++ [b]).reverse) :
    IsDefEqCtx env U' [] A.reverse B.reverse ∧ ∃ u, env.IsDefEq U' A.reverse a b (.sort u) := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at H
  cases H with
  | succ H h => exact ⟨H, _, h⟩

private theorem snoc_of_length {l : List VExpr} {n : Nat} (h : l.length = n + 1) :
    ∃ l' x, l = l' ++ [x] ∧ l'.length = n :=
  ⟨l.dropLast, l.getLast (by intro h'; simp [h'] at h),
    (List.dropLast_concat_getLast _).symm, by simp [h]⟩

/-- The core induction, over the arguments from the outermost binder. -/
theorem paramBridge_core (henv : env.OrderedStrong) {Δ : List VExpr}
    (hΔ : OnCtx Δ (env.IsType U)) :
    ∀ (n : Nat) (as P O D : List VExpr) (hn : as.length = n) (hP : P.length = as.length)
      (hO : O.length = as.length) (hD : D.length = as.length),
      IsDefEqCtx env U [] P.reverse O.reverse → IsDefEqCtx env U [] P.reverse D.reverse →
      Ctx.SubstEq env U Δ (argSubst as) (argSubst as) O.reverse →
      Ctx.SubstEq env U Δ (argSubst as) (argSubst as) P.reverse ∧
      Ctx.SubstEq env U Δ (argSubst as) (argSubst as) D.reverse ∧
      ∀ i (hi : i < as.length),
        TyCls env U Δ ((O[i]'(by omega)).subst (argSubst (as.take i))) =
          TyCls env U Δ ((D[i]'(by omega)).subst (argSubst (as.take i))) := by
  intro n
  induction n with
  | zero =>
    intro as P O D hn hP hO hD _ _ _
    obtain rfl : P = [] := List.length_eq_zero_iff.mp (hP.trans hn)
    obtain rfl : D = [] := List.length_eq_zero_iff.mp (hD.trans hn)
    exact ⟨.nil, .nil, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    intro as P O D hn hP hO hD h1 h2 W
    obtain ⟨as, a, rfl, hn'⟩ := snoc_of_length hn
    simp only [List.length_append, List.length_singleton] at hP hO hD
    rw [hn'] at hP hO hD
    obtain ⟨P', p, rfl, hP'⟩ := snoc_of_length hP
    obtain ⟨O', o, rfl, hO'⟩ := snoc_of_length hO
    obtain ⟨D', d, rfl, hD'⟩ := snoc_of_length hD
    obtain ⟨h1', u1, hpo⟩ := ctx_snoc h1
    obtain ⟨h2', u2, hpd⟩ := ctx_snoc h2
    rw [VExpr.argSubst_append_one] at W ⊢
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at W ⊢
    cases W with
    | cons W' hodom hhead =>
    rw [VExpr.Subst.cons_tail] at W'
    rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail] at hhead
    obtain ⟨WP, WD, hcls⟩ := ih as P' O' D' hn' (hP'.trans hn'.symm) (hO'.trans hn'.symm)
      (hD'.trans hn'.symm) h1' h2' W'
    have l1 := hpo.subst henv WP hΔ
    have l2 := hpd.subst henv WP hΔ
    simp only [VExpr.subst] at l1 l2
    have hp : env.IsDefEq U Δ a a (p.subst (argSubst as)) := .defeqDF l1.symm hhead
    have hd : env.IsDefEq U Δ a a (d.subst (argSubst as)) := .defeqDF l2 hp
    refine ⟨.cons (by rw [VExpr.Subst.cons_tail]; exact WP) hpo.hasType.1
        (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail]; exact hp),
      .cons (by rw [VExpr.Subst.cons_tail]; exact WD) (hpd.hasType.2.defeqDFC henv h2')
        (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_tail]; exact hd), fun i hi => ?_⟩
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < as.length
    · have := hcls i hlt
      rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
        List.take_append_of_le_length (by omega)]
      exact this
    · obtain rfl : i = as.length := by omega
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
        List.take_left' rfl]
      simp only [hO', hD', hn', Nat.sub_self, List.getElem_cons_zero]
      exact (TyCls.eq_of_defeq l1).symm.trans (TyCls.eq_of_defeq l2)

/-- **Parameter transport.** Along telescopes `own` and `pdoms` context-convertible to a common
`params`, a substitution typed along a prefix of `own` (at levels `ls`) is typed along the same
prefix of `pdoms`, and the instantiated domains have the same type class. -/
theorem paramBridge {E env : VEnv} (henv : env.OrderedStrong) (hE : E ≤ env) {Δ : List VExpr}
    (hΔ : OnCtx Δ (env.IsType U)) {u0 : Nat} {params own pdoms : List VExpr}
    (h1 : E.IsDefEqCtx u0 [] params.reverse own.reverse)
    (h2 : E.IsDefEqCtx u0 [] params.reverse pdoms.reverse) {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) {as : List VExpr} (hn : as.length ≤ own.length)
    (W : Ctx.SubstEq env U Δ (argSubst as) (argSubst as)
      ((own.map (·.instL ls)).take as.length).reverse) :
    Ctx.SubstEq env U Δ (argSubst as) (argSubst as)
      ((pdoms.map (·.instL ls)).take as.length).reverse ∧
    ∀ i (hi : i < as.length),
      TyCls env U Δ (((own[i]'(by omega)).instL ls).subst (argSubst (as.take i))) =
        TyCls env U Δ (((pdoms[i]'(by
          have := h1.length_eq; have := h2.length_eq
          simp only [List.length_reverse] at *; omega)).instL ls).subst
          (argSubst (as.take i))) := by
  have hl1 := h1.length_eq
  have hl2 := h2.length_eq
  simp only [List.length_reverse] at hl1 hl2
  have hpre : ∀ l : List VExpr, as.length ≤ l.length →
      ((l.map (·.instL ls)).take as.length).reverse =
        (l.reverse.map (·.instL ls)).drop (l.length - as.length) := by
    intro l hl
    rw [List.map_reverse, List.drop_reverse]; simp only [List.length_map]
    congr 2; omega
  have k1 : IsDefEqCtx env U [] ((params.map (·.instL ls)).take as.length).reverse
      ((own.map (·.instL ls)).take as.length).reverse := by
    rw [hpre own hn, hpre params (by omega), show params.length = own.length by omega]
    simpa using ctx_drop (own.length - as.length) (ctx_instL hls (h1.mono hE))
  have k2 : IsDefEqCtx env U [] ((params.map (·.instL ls)).take as.length).reverse
      ((pdoms.map (·.instL ls)).take as.length).reverse := by
    rw [hpre pdoms (by omega), hpre params (by omega), show params.length = pdoms.length by omega]
    simpa using ctx_drop (pdoms.length - as.length) (ctx_instL hls (h2.mono hE))
  obtain ⟨-, WD, hcls⟩ := paramBridge_core henv hΔ _ as _ _ _ rfl (by simp; omega)
    (by simp; omega) (by simp; omega) k1 k2 W
  refine ⟨WD, fun i hi => ?_⟩
  have := hcls i hi
  simpa using this

end Model
end VEnv
end Lean4Lean
