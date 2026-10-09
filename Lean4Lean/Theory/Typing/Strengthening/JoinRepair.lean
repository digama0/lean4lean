import Lean4Lean.Theory.Typing.Strengthening.Cancel
import Lean4Lean.Theory.Typing.Confluence.WFParams

/-! # Strengthening as repair of a confluence witness

Under canonical `Eq`, `VEnv.WF.church_rosser` turns the hypothesis of `Cancel` (through
`Front`) into a join in `Q :: Γ`: both lifted sides reduce by `FullReduction` to normally
equal terms. `JoinRepair` is the statement that such a join of lifted, typed terms can be
replaced by a typed join in `Γ`; `cancel_iff_joinRepair` shows it is exactly equivalent to
`Cancel`, hence to `Strengthening`. Two parts of the repair are proved outright:

* an inhabitant of the removed binder repairs the whole reduction witness by substitution,
  side conditions included (`FullStep.instN`, `FullReduction.repair_inhabited`); so the
  uninhabited binder is the entire remaining problem;
* every installed equation has a join of support-preserving paths
  (`installed_equation_supported_join`).

Astra's second-opinion derivation (2026-10-08), kernel-checked outside this repository as
`StrengtheningContinuation_2026-10-08.lean`, adapted. -/

namespace Lean4Lean
namespace VEnv
open VExpr

section CertifiedRepair
open VEnv.Params
variable [VEnv.Params]


inductive DescendingStep {n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') : VExpr → VExpr → Prop where
  | lift {a b} : FullStep Γ a b →
      DescendingStep W (a.liftN n k) (b.liftN n k)

theorem DescendingStep.full {W : Ctx.LiftN n k Γ Γ'}
    {a b : VExpr} (h : DescendingStep W a b) : FullStep Γ' a b := by
  cases h with | lift h => exact h.weakN W

/-- Exact descent of certified steps uses only injectivity of syntax lifting. -/
theorem DescendingStep.down {W : Ctx.LiftN n k Γ Γ'} {a : VExpr}
    {b' : VExpr} (h : DescendingStep W (a.liftN n k) b') :
    ∃ b, b' = b.liftN n k ∧ FullStep Γ a b := by
  generalize hs : a.liftN n k = a' at h
  cases h with
  | @lift a₀ b h =>
    have : a₀ = a := VExpr.liftN_inj.mp hs.symm
    subst a₀
    exact ⟨b, rfl, h⟩

/-- Finite-path descent. The induction measure is the length of the path;
no induction on declarative equality is hidden here. -/
theorem descending_path_down {W : Ctx.LiftN n k Γ Γ'} {a : VExpr}
    {b' : VExpr} (h : ReflTransGen (DescendingStep W) (a.liftN n k) b') :
    ∃ b, b' = b.liftN n k ∧ FullReduction Γ a b := by
  induction h with
  | rfl => exact ⟨a, rfl, .rfl⟩
  | tail _ hs ih =>
    obtain ⟨b, rfl, hb⟩ := ih
    obtain ⟨c, rfl, hc⟩ := hs.down
    exact ⟨c, rfl, hb.tail hc⟩

theorem descending_path_up {W : Ctx.LiftN n k Γ Γ'} {a b : VExpr}
    (H : FullReduction Γ a b) :
    ReflTransGen (DescendingStep W) (a.liftN n k) (b.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ hs ih => exact ih.tail (.lift hs)

/-- Substitution of an actual inhabitant acts on ALL full steps, including
singleton/quotient unfolding and both eta rules. The induction is on the step
constructor; under binders Ctx.InstN.succ increases the insertion depth. -/
theorem fullStep_instN {Γ₀ Γ₁ Γ : List VExpr} {q Q a b : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ q Q k Γ₁ Γ) (hq : env.HasType univs Γ₀ q Q)
    (H : FullStep Γ₁ a b) : FullStep Γ (a.inst q k) (b.inst q k) := by
  induction H generalizing Γ k with
  | core h => exact .core (ParRed.instN .rfl hq W h)
  | delta h =>
    simpa only [VExpr.inst_mkApps, VExpr.inst] using FullStep.delta (h.instN henv W hq)
  | quotDelta h =>
    simpa only [VExpr.inst_mkApps, VExpr.inst] using FullStep.quotDelta (h.instN henv W hq)
  | projIota hi hs hf ht =>
    have hs' := hs.instN henv W hq
    simp only [VExpr.inst_mkApps, VExpr.inst] at hs' ⊢
    exact .projIota hi hs' (by simp [hf]) (ht.instN henv W hq)
  | structEta hi hl hn hs ht =>
    have hs' := hs.instN henv W hq
    have ht' := ht.instN henv W hq
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    exact .structEta hi (by simpa using hl) hn hs' ht'
  | funEta ht =>
    simpa only [VExpr.inst, ← VExpr.lift_instN_lo, VExpr.instVar_lower] using
      FullStep.funEta (ht.instN henv W hq)
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

/-- The path length is unchanged by substitution. -/
theorem fullReduction_instN {Γ₀ Γ₁ Γ : List VExpr} {q Q a b : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ q Q k Γ₁ Γ) (hq : env.HasType univs Γ₀ q Q)
    (H : FullReduction Γ₁ a b) : FullReduction Γ (a.inst q k) (b.inst q k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ hs ih => exact ih.tail (fullStep_instN W hq hs)

/-- Witness repair is complete for an inhabited removed binder: the new
endpoint is t[q], and every step carries its certificates in the smaller context.
This makes no claim that the old target t was supported. -/
theorem repair_reduction_inhabited {Γ : List VExpr} {q Q a t : VExpr}
    (hq : env.HasType univs Γ q Q) (H : FullReduction (Q :: Γ) a.lift t) :
    FullReduction Γ a (t.inst q) := by
  simpa only [VExpr.inst_lift] using fullReduction_instN Ctx.InstN.zero hq H

/-- A repaired join includes source typing. FullReduction alone does not
certify typing (it even has reflexive paths at arbitrary raw expressions). -/
def TypedJoin (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ A B x y, env.HasType univs Γ a A ∧ env.HasType univs Γ b B ∧
    FullReduction Γ a x ∧ FullReduction Γ b y ∧ NormalEq Γ x y

theorem TypedJoin.defeq {Γ : List VExpr} {a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (h : TypedJoin Γ a b) :
    env.IsDefEqU univs Γ a b := by
  obtain ⟨A, B, x, y, ha, hb, hx, hy, hn⟩ := h
  exact (IsDefEqU.trans henv hΓ ⟨A, hx.defeq hΓ ha⟩ (hn.defeq hΓ)).trans
    henv hΓ ⟨B, (hy.defeq hΓ hb).symm⟩

/-- This is the completeness interface actually needed by witness repair.
It replaces a JOIN, not an arbitrary terminal expression by the same expression.
Both original source typings may have types depending on the deleted binder. -/
def JoinRepair : Prop :=
  ∀ {Γ Q a b A B x y}, OnCtx (Q :: Γ) (env.IsType univs) →
    env.HasType univs (Q :: Γ) a.lift A →
    env.HasType univs (Q :: Γ) b.lift B →
    FullReduction (Q :: Γ) a.lift x → FullReduction (Q :: Γ) b.lift y →
    NormalEq (Q :: Γ) x y → TypedJoin Γ a b
end CertifiedRepair

theorem installed_equation_supported_join {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) {U n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    {df : VDefEq} {ls : List VLevel} (hdf : env.defeqs df)
    (hw : ∀ l ∈ ls, l.WF U) (hl : ls.length = df.uvars) :
    letI := henv.params U
    ∃ x y : VExpr,
      ReflTransGen (DescendingStep W) ((df.lhs.instL ls).liftN n k) (x.liftN n k) ∧
      ReflTransGen (DescendingStep W) ((df.rhs.instL ls).liftN n k) (y.liftN n k) ∧
      NormalEq Γ' (x.liftN n k) (y.liftN n k) := by
  letI := henv.params U
  have H : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) :=
    .extra hdf hw hl
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ H
  exact ⟨x, y, descending_path_up hx, descending_path_up hy, hn.weakN W⟩

/-- Every use of canonical Eq here is explicit: it supplies existing
Church-Rosser. This theorem DOES NOT prove the JoinRepair premise. -/
theorem front_of_joinRepair {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (repair : ∀ U, @JoinRepair (henv.params U)) : Front env := by
  intro U Γ Q a b hΓ H
  letI := henv.params U
  obtain ⟨T, H⟩ := H
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ H
  exact TypedJoin.defeq hΓ.1 (repair U hΓ H.hasType.1 H.hasType.2 hx hy hn)

/-- The converse establishes the exact logical strength of this repair
interface; it is not a weaker replacement for the unresolved theorem. -/
theorem joinRepair_of_front {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hf : Front env) (U : Nat) : @JoinRepair (henv.params U) := by
  letI := henv.params U
  intro Γ Q a b A B x y hΓ ha hb hx hy hn
  have h : env.IsDefEqU U (Q :: Γ) a.lift b.lift :=
    TypedJoin.defeq hΓ ⟨A, B, x, y, ha, hb, hx, hy, hn⟩
  obtain ⟨T, h⟩ := hf hΓ h
  obtain ⟨x, y, hx, hy, hn⟩ := henv.church_rosser heq hΓ.1 h
  exact ⟨T, T, x, y, h.hasType.1, h.hasType.2, hx, hy, hn⟩

theorem cancel_iff_joinRepair {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) :
    Cancel env ↔ ∀ U, @JoinRepair (henv.params U) := by
  constructor
  · exact fun hc => joinRepair_of_front henv heq (Front.of_cancel hc)
  · exact fun hr => Cancel.of_front henv (front_of_joinRepair henv heq hr)

theorem Strengthening.of_joinRepair {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (repair : ∀ U, @JoinRepair (henv.params U)) : env.Strengthening :=
  Strengthening.of_front henv (front_of_joinRepair henv heq repair)

end VEnv
end Lean4Lean
