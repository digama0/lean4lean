import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas

namespace Lean4Lean.VEnv
variable {env : Lean4Lean.VEnv} {U : Nat}

/-- A typed application whose head has a syntactic telescope ending in a sort
has supplied exactly that telescope when the application itself has sort type. -/
theorem HasType.mkApps_sort_arity (henv : env.WF)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {f : VExpr} {domains args : List VExpr} {u v : VLevel}
    (hf : env.HasType U Γ f (VExpr.wrapForalls domains (.sort u)))
    (ht : env.HasType U Γ (VExpr.mkApps f args) (.sort v)) :
    args.length = domains.length := by
  induction args generalizing f domains with
  | nil =>
    cases domains with
    | nil => rfl
    | cons domain domains =>
      have hdef := (hf.uniqU henv hΓ ht).symm
      exact (IsDefEqU.sort_forallE_inv henv hΓ hdef).elim
  | cons arg args ih =>
    have hfa : VExpr.WF env U Γ (.app f arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.ordered hΓ with ⟨A, B, hfun, harg⟩
    cases domains with
    | nil =>
      exact (IsDefEqU.sort_forallE_inv henv hΓ (hf.uniqU henv hΓ hfun)).elim
    | cons domain domains =>
      rcases (hf.uniqU henv hΓ hfun).forallE_inv henv hΓ with ⟨⟨_, hd⟩, _⟩
      have ha := harg.defeqU_r henv hΓ ⟨_, hd.symm⟩
      have hfa' := hf.app ha
      change env.HasType U Γ (.app f arg)
        ((VExpr.wrapForalls domains (.sort u)).inst arg) at hfa'
      rw [VExpr.wrapForalls_inst] at hfa'
      have hlen := ih hfa' ht
      simpa [VExpr.instDomains] using hlen

end Lean4Lean.VEnv
