import Lean4Lean.Theory.Typing.CaseMajorDomain
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration

/-! Exact motive applications produced by typed abstract case calls. -/

namespace Lean4Lean.InductiveSignature

namespace CaseSchema

end CaseSchema

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

private theorem caseResult_head_typed {type : VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (VExpr.mkApps fn args) type) :
    ∃ headType, env.HasType U Γ fn headType := by
  induction args generalizing fn with
  | nil => exact ⟨_, H⟩
  | cons a args ih =>
    obtain ⟨_, h⟩ := ih H
    obtain ⟨_, _, hf, _⟩ := h.app_inv henv hΓ
    exact ⟨_, hf⟩

/-- A typed lambda telescope has a type using its actual binder annotations. -/
theorem _root_.Lean4Lean.VExpr.WF.wrapLams_type (henv : env.WF) :
    ∀ {domains : List VExpr} {Γ : List VExpr} {body : VExpr},
      OnCtx Γ (env.IsType U) → VExpr.WF env U Γ (wrapLams domains body) →
      ∃ resultType, env.HasType U Γ (wrapLams domains body) (wrapForalls domains resultType) := by
  intro domains
  induction domains with
  | nil => intro Γ body _ h; exact h
  | cons domain domains ih =>
    intro Γ body hΓ h
    obtain ⟨⟨_, hd⟩, hb⟩ := h.lam_inv henv.ordered hΓ
    have hΓ' : OnCtx (domain :: Γ) (env.IsType U) := ⟨hΓ, _, hd⟩
    obtain ⟨resultType, ht⟩ := ih hΓ' hb
    exact ⟨resultType, .lam hd ht⟩

/-- Full beta reduction of a lambda telescope needs only typing of the
actual application, not a separately supplied type annotation. -/
theorem _root_.Lean4Lean.VExpr.WF.beta_wrapLams (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {domains args : List VExpr} {body : VExpr}
    (hlen : args.length = domains.length)
    (H : VExpr.WF env U Γ (mkApps (wrapLams domains body) args)) :
    env.IsDefEqU U Γ (mkApps (wrapLams domains body) args) (body.instOuter args) := by
  obtain ⟨_, ht⟩ := H
  obtain ⟨_, hf⟩ := caseResult_head_typed henv hΓ ht
  obtain ⟨resultType, hf⟩ := VExpr.WF.wrapLams_type henv hΓ ⟨_, hf⟩
  have hargs := (HasType.mkApps_wrapForalls henv hΓ hf ⟨_, ht⟩ hlen).1
  exact ⟨_, IsDefEq.mkApps_wrapLams henv hΓ hf hlen hargs⟩

end Lean4Lean.VEnv

/-! Typing of the actual lambda programs used by projection abbreviations. -/

namespace Lean4Lean
namespace VExpr

private theorem liftN_wrapLams_shape (domains : List VExpr) (body : VExpr) (n k : Nat) :
    ∃ domains', domains'.length = domains.length ∧
      (wrapLams domains body).liftN n k =
        wrapLams domains' (body.liftN n (k + domains.length)) := by
  induction domains generalizing k with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons domain domains ih =>
    obtain ⟨domains', hlen, heq⟩ := ih (k + 1)
    refine ⟨domain.liftN n k :: domains', by simp [hlen], ?_⟩
    change VExpr.lam (domain.liftN n k) ((wrapLams domains body).liftN n (k + 1)) = _
    rw [heq]
    simp only [wrapLams, List.foldr_cons, List.length_cons]
    congr 3 <;> omega

private theorem instOuter_liftN_same (body : VExpr) (n : Nat) :
    (body.liftN n n).instOuter (bvarRange n n) = body := by
  rw [instOuter_eq_subst, liftN_subst]
  conv => rhs; rw [← subst_id (e := body)]
  congr 1
  funext i
  simp only [Subst.lift_l, Lift.liftVar_consN_skipN]
  by_cases hi : i < n
  · rw [liftVar_lt hi, Subst.ofList_lt _ (by simpa using hi)]
    simp only [bvarRange_length]
    rw [bvarRange_getElem n n (n - 1 - i) (by omega)]
    change VExpr.bvar (n - 1 - (n - 1 - i)) = VExpr.bvar i
    congr 1
    omega
  · rw [liftVar_le (Nat.le_of_not_gt hi), Subst.ofList_ge _ (by simp)]
    simp [Subst.id]

end VExpr
namespace VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

/-- A lifted motive applied to the enclosing telescope variables returns its
original body. Both its beta equality and result typing come from the actual
application's typing. -/
theorem HasType.projectionMotive_result (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {domains : List VExpr} {body term : VExpr}
    (H : env.HasType U Γ term
      (mkApps ((wrapLams domains body).liftN domains.length)
        (bvarRange domains.length domains.length))) :
    env.HasType U Γ term body := by
  obtain ⟨domains', hlen, hshape⟩ := liftN_wrapLams_shape domains body domains.length 0
  obtain ⟨u, hmotive⟩ := H.isType henv.ordered hΓ
  have hwf : VExpr.WF env U Γ (mkApps
      (wrapLams domains' (body.liftN domains.length domains.length))
      (bvarRange domains.length domains.length)) := by
    simpa only [hshape, Nat.zero_add] using (show VExpr.WF env U Γ _ from ⟨_, hmotive⟩)
  have hbeta := hwf.beta_wrapLams henv hΓ (by simp [hlen])
  rw [instOuter_liftN_same] at hbeta
  apply H.defeqU_r henv hΓ
  simpa only [hshape, Nat.zero_add] using hbeta

end VEnv
end Lean4Lean
