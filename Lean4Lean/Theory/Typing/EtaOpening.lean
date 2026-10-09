import Lean4Lean.Theory.Typing.EnvLemmas

/-! Exact telescope opening and eta use direct typing and substitution.
They are below uniqueness, equality inversion, and the reduction presentation. -/

namespace Lean4Lean.VEnv
open VExpr

/-- Open the unsupplied telescope with fresh variables in binder order. -/
def etaOpen : Nat → VExpr → VExpr
  | 0, fn => fn
  | n + 1, fn => etaOpen n (.app fn.lift (.bvar 0))

theorem etaOpen_succ (n : Nat) (fn : VExpr) :
    etaOpen (n + 1) fn = .app (etaOpen n fn).lift (.bvar 0) := by
  induction n generalizing fn with
  | zero => rfl
  | succ n ih => exact ih _

/-- Apply the known function type to fresh variables directly. No inversion
of a converted lambda type is needed to type the opened expression. -/
theorem HasType.etaOpen_wf (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : HasType env U Γ fn (wrapForalls domains result)) :
    OnCtx (domains.reverse ++ Γ) (env.IsType U) ∧
      HasType env U (domains.reverse ++ Γ) (etaOpen domains.length fn) result := by
  induction domains generalizing Γ fn with
  | nil => exact ⟨hΓ, H⟩
  | cons domain domains ih =>
    obtain ⟨u, hd⟩ := (IsType.forallE_inv henv (H.isType henv hΓ)).1
    have hbody := IsDefEq.appDF (H.weak henv (B := domain))
      (IsDefEq.bvar (Lookup.zero (Γ := Γ) (ty := domain)))
    simp only [lift, VExpr.inst_liftN_bvar] at hbody
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, etaOpen] using ih (Γ := domain :: Γ) ⟨hΓ, u, hd⟩ hbody

/-- Eta expansion through a dependent telescope preserves the exact type of
the term. Functional result types remain below the supplied telescope. -/
theorem HasType.etaOpen_defeq (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : HasType env U Γ fn (wrapForalls domains result)) :
    IsDefEq env U Γ fn (wrapLams domains (etaOpen domains.length fn))
      (wrapForalls domains result) := by
  induction domains generalizing Γ fn with
  | nil => exact H
  | cons domain domains ih =>
    have heta := IsDefEq.eta H
    obtain ⟨u, hd⟩ := (IsType.forallE_inv henv.ordered (H.isType henv.ordered hΓ)).1
    have hΓ' : OnCtx (domain :: Γ) (env.IsType U) := ⟨hΓ, u, hd⟩
    have hbody := IsDefEq.appDF (H.weak henv.ordered (B := domain))
      (IsDefEq.bvar (Lookup.zero (Γ := Γ) (ty := domain)))
    simp only [lift, VExpr.inst_liftN_bvar] at hbody
    have heq := ih hΓ' hbody
    exact heta.symm.trans (.lamDF hd heq)

/-- Close an equality proved under the remaining telescope. -/
theorem IsDefEq.etaOpen_wrapLams
    (hΓ : OnCtx Γ (env.IsType U))
    (hdomains : OnCtx (domains.reverse ++ Γ) (env.IsType U))
    (H : IsDefEq env U (domains.reverse ++ Γ) lhs rhs result) :
    IsDefEq env U Γ (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains result) := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons domain domains ih =>
    have hΓ' : OnCtx (domain :: Γ) (env.IsType U) := by
      have dropPrefix {xs ys : List VExpr} (h : OnCtx (xs ++ ys) (env.IsType U)) :
          OnCtx ys (env.IsType U) := by
        induction xs with | nil => exact h | cons _ _ ih => exact ih h.1
      apply dropPrefix (xs := domains.reverse)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hdomains
    obtain ⟨u, hd⟩ := hΓ'.2
    apply IsDefEq.lamDF hd
    apply ih hΓ'
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hdomains
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H

end Lean4Lean.VEnv
