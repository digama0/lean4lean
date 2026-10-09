import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.RestorationNaturality

/-!
# Structural equality up to universe levels

`VExpr.LEquiv U e e'` relates expressions that agree except for equivalent universe levels,
with the levels of `e'` well formed with respect to `U` universe parameters. It is what
survives when an expression whose universe levels have been instantiated and simplified on the
`Expr` side is compared with the syntactic level instantiation `VExpr.instL` on the abstract
side. Substitution and lifting are congruent for it, and it inverts along `forallE` telescopes.
-/

namespace Lean4Lean
namespace VExpr

inductive LEquiv (U : Nat) : VExpr → VExpr → Prop
  | refl : LEquiv U e e
  | sort : u ≈ v → v.WF U → LEquiv U (.sort u) (.sort v)
  | const : List.Forall₂ (· ≈ ·) us vs → (∀ v ∈ vs, v.WF U) → LEquiv U (.const c us) (.const c vs)
  | elim : List.Forall₂ (· ≈ ·) us vs → (∀ v ∈ vs, v.WF U) →
      LEquiv U (.elim block owner us) (.elim block owner vs)
  | app : LEquiv U f f' → LEquiv U a a' → LEquiv U (.app f a) (.app f' a')
  | proj : LEquiv U e e' → LEquiv U (.proj n i e) (.proj n i e')
  | lam : LEquiv U A A' → LEquiv U b b' → LEquiv U (.lam A b) (.lam A' b')
  | forallE : LEquiv U A A' → LEquiv U b b' → LEquiv U (.forallE A b) (.forallE A' b')

/-- The symmetric level relation used by strong typing implies this
one-sided relation used by concrete expression translation. -/
theorem LEquiv.of_eqUpToLevels (H : VEnv.EqUpToLevels U e e') : LEquiv U e e' := by
  induction H with
  | bvar => exact .refl
  | sort _ h2 h3 => exact .sort h3 h2
  | const _ h2 h3 => exact .const h3 h2
  | elim _ h2 h3 => exact .elim h3 h2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

/-- Specialization respects equivalent source and elimination universes in
all generated syntax, including abstract case heads. -/
theorem LEquiv.instL_expr (e : VExpr)
    (hus : ∀ u ∈ us, u.WF U) (hvs : ∀ v ∈ vs, v.WF U)
    (heq : List.Forall₂ (· ≈ ·) us vs) : LEquiv U (e.instL us) (e.instL vs) :=
  .of_eqUpToLevels (VEnv.EqUpToLevels.instL_expr e hus hvs heq)

theorem LEquiv.liftN (H : LEquiv U e e') : LEquiv U (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | sort h1 h2 => exact .sort h1 h2
  | const h1 h2 => exact .const h1 h2
  | elim h1 h2 => exact .elim h1 h2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

theorem LEquiv.inst (H : LEquiv U e e') (x : VExpr) (k : Nat) :
    LEquiv U (e.inst x k) (e'.inst x k) := by
  induction H generalizing k with
  | refl => exact .refl
  | sort h1 h2 => exact .sort h1 h2
  | const h1 h2 => exact .const h1 h2
  | elim h1 h2 => exact .elim h1 h2
  | app _ _ ih1 ih2 => exact .app (ih1 k) (ih2 k)
  | proj _ ih => exact .proj (ih k)
  | lam _ _ ih1 ih2 => exact .lam (ih1 k) (ih2 (k + 1))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 k) (ih2 (k + 1))

theorem LEquiv.instOuterAt (H : LEquiv U e e') (args : List VExpr) (k : Nat) :
    LEquiv U (e.instOuterAt args k) (e'.instOuterAt args k) := by
  induction args generalizing e e' with
  | nil => exact H
  | cons a as ih => exact ih (H.inst a _)

theorem LEquiv.instOuter (H : LEquiv U e e') (args : List VExpr) :
    LEquiv U (e.instOuter args) (e'.instOuter args) := by
  simp only [VExpr.instOuter_eq_instOuterAt]; exact H.instOuterAt args 0

theorem LEquiv.forallE_inv (H : LEquiv U T (.forallE A B)) :
    ∃ A₀ B₀, T = .forallE A₀ B₀ ∧ LEquiv U A₀ A ∧ LEquiv U B₀ B := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | forallE h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

theorem LEquiv.wrapForalls_inv (H : LEquiv U T (VExpr.wrapForalls ds b)) :
    ∃ ds₀ b₀, T = VExpr.wrapForalls ds₀ b₀ ∧ List.Forall₂ (LEquiv U) ds₀ ds ∧ LEquiv U b₀ b := by
  induction ds generalizing T with
  | nil => exact ⟨[], T, rfl, .nil, H⟩
  | cons d ds ih =>
    obtain ⟨A₀, B₀, rfl, h1, h2⟩ := H.forallE_inv
    obtain ⟨ds₀, b₀, rfl, h3, h4⟩ := ih h2
    exact ⟨A₀ :: ds₀, b₀, rfl, .cons h1 h3, h4⟩

theorem LEquiv.mkApps_fn (hf : LEquiv univs f f') (args : List VExpr) :
    LEquiv univs (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact hf
  | cons a args ih => exact ih (.app hf .refl)

end VExpr

namespace VEnv

/-- A well-formed expression is definitionally equal to any level-equivalent one. -/
theorem _root_.Lean4Lean.VExpr.LEquiv.defeq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (L : VExpr.LEquiv U e₁ e₂) (h : VExpr.WF env U Γ e₁) : env.IsDefEqU U Γ e₁ e₂ := by
  induction L generalizing Γ with
  | refl => exact h
  | sort h1 h2 =>
    have ⟨_, h⟩ := h
    exact ⟨_, .sortDF (HasType.sort_inv henv.ordered h) h2 h1⟩
  | const h1 h2 =>
    have ⟨_, h⟩ := h
    have ⟨_, h3, h4, h5⟩ := HasType.const_inv henv.ordered hΓ h
    exact ⟨_, .constDF h3 h4 h2 h5 h1⟩
  | elim h1 h2 =>
    obtain ⟨_, h⟩ := h
    obtain ⟨schema, owner, type, target, levels, typeLevel, rfl, rfl,
      hschema, htype, hclosed, hperm, _, htyped⟩ :=
      HasType.elim_inv henv.ordered hΓ h
    cases h1 with
    | cons htarget hlevels =>
      exact ⟨_, .elimDF hschema htype hclosed hperm h2 (.cons htarget hlevels) htyped⟩
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := VExpr.WF.app_inv henv.ordered hΓ h
    exact ⟨_, .appDF ((ih1 hΓ ⟨_, hf⟩).of_l henv hΓ hf) ((ih2 hΓ ⟨_, ha⟩).of_l henv hΓ ha)⟩
  | proj _ ih =>
    have ⟨_, h⟩ := h
    obtain ⟨info, ls, P, idx, sm, F, fl, hinfo, hls, huv, hP, hidx, hfield, hFty, hsm, hclosed,
      hguard⟩ := HasType.proj_inv henv.ordered hΓ h
    have hmaj := hsm.hasType.2
    exact ⟨_, .projDF hinfo hls huv hP hidx hfield hFty hsm
      (hsm.transU_l henv hΓ (ih hΓ ⟨_, hmaj⟩)) hclosed hguard⟩
  | lam _ _ ih1 ih2 =>
    have ⟨_, h⟩ := h
    have ⟨⟨_, hA⟩, hb⟩ := HasType.lam_inv henv.ordered hΓ h
    have hΓ' : OnCtx (_ :: Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
    have ⟨_, hb'⟩ := hb
    exact ⟨_, .lamDF ((ih1 hΓ ⟨_, hA⟩).of_l henv hΓ hA) ((ih2 hΓ' hb).of_l henv hΓ' hb')⟩
  | forallE _ _ ih1 ih2 =>
    have ⟨_, h⟩ := h
    have ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := HasType.forallE_inv henv.ordered h
    have hΓ' : OnCtx (_ :: Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
    exact ⟨_, .forallEDF ((ih1 hΓ ⟨_, hA⟩).of_l henv hΓ hA) ((ih2 hΓ' ⟨_, hB⟩).of_l henv hΓ' hB)⟩

end VEnv
end Lean4Lean

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

theorem EqUpToLevels.mkApps_args (H : EqUpToLevels U fn fn')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    EqUpToLevels U (VExpr.mkApps fn args) (VExpr.mkApps fn' args') := by
  induction ha generalizing fn fn' with
  | nil => exact H
  | cons h hs ih => exact ih (.app H h)

theorem EqUpToLevels.subst_args (H : EqUpToLevels U e e')
    (hσ : ∀ i, EqUpToLevels U (σ i) (σ' i)) :
    EqUpToLevels U (e.subst σ) (e'.subst σ') := by
  induction H generalizing σ σ' with
  | bvar => exact hσ _
  | const h1 h2 h3 => exact .const h1 h2 h3
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | proj _ ih => exact .proj (ih hσ)
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    constructor
    · exact ih1 hσ
    · apply ih2
      intro i
      cases i with
      | zero => exact .bvar
      | succ i => exact (hσ i).weakN

theorem EqUpToLevels.instantiateParams_args (H : EqUpToLevels U e e')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    EqUpToLevels U (instantiateParams e args) (instantiateParams e' args') := by
  apply H.subst_args
  intro i
  have hlen := Lean4Lean.List.Forall₂.length_eq ha
  simp only [← hlen]
  split
  · rename_i hi
    exact List.forall₂_getElem ha _ (by omega) (by omega)
  · exact .bvar

end Lean4Lean.VEnv
namespace Lean4Lean.InductiveSignature
open VEnv

end Lean4Lean.InductiveSignature
