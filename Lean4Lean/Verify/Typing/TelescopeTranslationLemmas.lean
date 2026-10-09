import Lean4Lean.Verify.Typing.TelescopeTranslation
import Lean4Lean.Verify.Typing.LevelEquiv
import Lean4Lean.Verify.Environment.RecursorAlignment

/-!
# Transport lemmas for telescope certificates

Syntactic facts about binders that a source body does not mention, and the transport of the
depth-bounded certificate `TelTrN` along environment extension (`TelTrN.mono`), level instantiation
(`TelTrN.instL_lequiv`), free-variable weakening (`TelTrN.weakFV`), substitution of a typed term
(`TelTrN.instN`, `TelTrN.inst`) and `Expr.eqv` (`TelTrN.eqv`). Each is the `TrSyn` lemma for the
syntax and a `TelWF` lemma for the typing; the delete branch of a binder is `TrSyn.lower` and
commutes with the operation at the other binders.
-/

namespace Lean.Expr

theorem liftLooseBVars'_inj {x y : Expr} {k d : Nat}
    (h : liftLooseBVars' x k d = liftLooseBVars' y k d) : x = y := by
  induction x generalizing y k with
  | bvar i =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    split at h <;> split at h <;> omega
  | app f a ihf iha =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam n t b bi iht ihb | forallE n t b bi iht ihb =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2⟩
  | letE n t v b nd iht ihv ihb =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, iht h.2.1, ihv h.2.2.1, ihb h.2.2.2.1, h.2.2.2.2⟩
  | mdata m e ih =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, ih h.2⟩
  | proj s i e ih =>
    cases y <;> simp [liftLooseBVars'] at h ⊢
    exact ⟨h.1, h.2.1, ih h.2.2⟩
  | _ => cases y <;> simp [liftLooseBVars'] at h ⊢; exact h

theorem hasLooseBVar'_liftLooseBVars'_of_lt {e : Expr} {k d i : Nat}
    (h1 : k ≤ i) (h2 : i < k + d) : (liftLooseBVars' e k d).hasLooseBVar' i = false := by
  induction e generalizing k i with
  | bvar j => simp [liftLooseBVars', hasLooseBVar']; split <;> omega
  | _ => simp_all [liftLooseBVars', hasLooseBVar'] <;> grind

theorem hasLooseBVar'_liftLooseBVars'_self {e : Expr} {k : Nat} :
    (liftLooseBVars' e k 1).hasLooseBVar' k = false :=
  hasLooseBVar'_liftLooseBVars'_of_lt (Nat.le_refl _) (Nat.lt_succ_self _)

theorem liftLooseBVars'_lower {e : Expr} {k : Nat} (h : e.hasLooseBVar' k = false) :
    liftLooseBVars' (lowerLooseBVars' e (k + 1) 1) k 1 = e := by
  have hk : ¬ (k + 1 < 1) := by omega
  induction e generalizing k with
  | bvar j =>
    simp [hasLooseBVar'] at h
    simp only [lowerLooseBVars', liftLooseBVars', if_neg hk]
    congr 1; split <;> split <;> omega
  | app _ _ ihf iha =>
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', liftLooseBVars', ihf h.1, iha h.2]
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', liftLooseBVars', iht h.1, ihb h.2]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', liftLooseBVars', iht h.1.1, ihv h.1.2, ihb h.2]
  | mdata _ _ ih | proj _ _ _ ih =>
    simp only [hasLooseBVar'] at h
    simp [lowerLooseBVars', liftLooseBVars', ih h]
  | _ => simp [lowerLooseBVars', liftLooseBVars']

theorem eq_liftLooseBVars'_lower {e : Expr} {k : Nat} (h : e.hasLooseBVar' k = false) :
    e = liftLooseBVars' (lowerLooseBVars' e (k + 1) 1) k 1 := (liftLooseBVars'_lower h).symm

theorem hasLooseBVar'_instantiate1'_of_le {e a : Expr} {i k : Nat} (hi : i ≤ k) :
    (e.instantiate1' a (k + 1)).hasLooseBVar' i = e.hasLooseBVar' i := by
  induction e generalizing i k with
  | bvar j =>
    simp only [instantiate1']
    split
    · rfl
    · split
      · subst j
        rw [hasLooseBVar'_liftLooseBVars'_of_lt (Nat.zero_le _) (by omega)]
        simp [hasLooseBVar']; omega
      · simp [hasLooseBVar']; omega
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp [instantiate1', hasLooseBVar', iht hi, ihb (Nat.succ_le_succ hi)]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp [instantiate1', hasLooseBVar', iht hi, ihv hi, ihb (Nat.succ_le_succ hi)]
  | _ => simp_all [instantiate1', hasLooseBVar']

theorem instantiate1'_liftLooseBVars'_lo {b a : Expr} {i k : Nat} (hi : i ≤ k) :
    (liftLooseBVars' b i 1).instantiate1' a (k + 1) =
      liftLooseBVars' (b.instantiate1' a k) i 1 := by
  induction b generalizing i k with
  | bvar j =>
    simp only [liftLooseBVars', instantiate1']
    by_cases hj : j < k
    · have : (if j < i then j else j + 1) < k + 1 := by split <;> omega
      simp only [if_pos this, if_pos hj, liftLooseBVars']
    · by_cases hjk : j = k
      · subst hjk
        have h1 : ¬ (if j < i then j else j + 1) < j + 1 := by split <;> omega
        have h2 : (if j < i then j else j + 1) = j + 1 := by split <;> omega
        simp only [h2, Nat.lt_irrefl, if_false, if_true,
          liftLooseBVars_liftLooseBVars (Nat.zero_le i) (by omega : i ≤ j + 0)]
      · have h1 : ¬ (if j < i then j else j + 1) < k + 1 := by split <;> omega
        have h2 : ¬ (if j < i then j else j + 1) = k + 1 := by split <;> omega
        have h3 : (if j < i then j else j + 1) = j + 1 := by split <;> omega
        simp only [h3, if_neg hj, if_neg hjk, liftLooseBVars']
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        congr 1; omega
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp [instantiate1', liftLooseBVars', iht hi, ihb (Nat.succ_le_succ hi)]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp [instantiate1', liftLooseBVars', iht hi, ihv hi, ihb (Nat.succ_le_succ hi)]
  | _ => simp_all [instantiate1', liftLooseBVars']

/-- Inverting a substitution above a binder that the result does not mention. -/
theorem instantiate1'_eq_liftLooseBVars' {b a c : Expr} {k : Nat}
    (h : b.instantiate1' a (k + 1) = liftLooseBVars' c 0 1) :
    ∃ b₀, b = liftLooseBVars' b₀ 0 1 ∧ c = b₀.instantiate1' a k := by
  have h0 : b.hasLooseBVar' 0 = false := by
    rw [← hasLooseBVar'_instantiate1'_of_le (a := a) (k := k) (Nat.zero_le _), h]
    exact hasLooseBVar'_liftLooseBVars'_self
  refine ⟨_, eq_liftLooseBVars'_lower h0, ?_⟩
  rw [eq_liftLooseBVars'_lower h0, instantiate1'_liftLooseBVars'_lo (Nat.zero_le _)] at h
  exact (liftLooseBVars'_inj h).symm

theorem instantiateLevelParamsCore'_liftLooseBVars' {e : Expr} {red s} {k d : Nat} :
    instantiateLevelParamsCore' red s (liftLooseBVars' e k d) =
      liftLooseBVars' (instantiateLevelParamsCore' red s e) k d := by
  induction e generalizing k <;> simp_all [instantiateLevelParamsCore', liftLooseBVars']

theorem hasLooseBVar'_instantiateLevelParamsCore' {e : Expr} {red s} {i : Nat} :
    (instantiateLevelParamsCore' red s e).hasLooseBVar' i = e.hasLooseBVar' i := by
  induction e generalizing i <;> simp_all [instantiateLevelParamsCore', hasLooseBVar']

theorem instantiateLevelParams_liftLooseBVars' {e : Expr} {ps ls} {k d : Nat} :
    (liftLooseBVars' e k d).instantiateLevelParams ps ls =
      liftLooseBVars' (e.instantiateLevelParams ps ls) k d := by
  simp only [instantiateLevelParams_eq, instantiateLevelParamsCore'_liftLooseBVars']

theorem instantiateLevelParams_eq_liftLooseBVars' {b c : Expr} {ps ls}
    (h : b.instantiateLevelParams ps ls = liftLooseBVars' c 0 1) :
    ∃ b₀, b = liftLooseBVars' b₀ 0 1 ∧ c = b₀.instantiateLevelParams ps ls := by
  have h0 : b.hasLooseBVar' 0 = false := by
    have := congrArg (hasLooseBVar' · 0) h
    simp only [instantiateLevelParams_eq, hasLooseBVar'_instantiateLevelParamsCore'] at this
    rw [this]; exact hasLooseBVar'_liftLooseBVars'_self
  refine ⟨_, eq_liftLooseBVars'_lower h0, ?_⟩
  rw [eq_liftLooseBVars'_lower h0, instantiateLevelParams_liftLooseBVars'] at h
  exact (liftLooseBVars'_inj h).symm

end Lean.Expr

namespace Lean4Lean
open Lean VEnv

theorem TrExprS.uniqueS {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Lean.Expr}
    {e₁ e₂ : VExpr} (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂ :=
  H1.unique_of_syn H2

/-! ### The typing certificate -/

namespace TelWF

theorem wf : TelWF env Us n Δ e e' → VExpr.WF env Us.length Δ.toCtx e'
  | .zero h _ | .succ h .. => h

theorem residual : TelWF env Us n Δ e e' → TrResidual env Us Δ e
  | .zero _ h | .succ _ h .. => h

theorem mono (henv : env ≤ env') (H : TelWF env Us n Δ e e') : TelWF env' Us n Δ e e' := by
  induction H with
  | zero h1 h2 => exact .zero (h1.mono henv) (h2.mono henv)
  | succ h1 h2 _ _ ih3 ih4 =>
    exact .succ (h1.mono henv) (h2.mono henv) ih3 fun _ _ hb hb' => ih4 _ _ hb hb'

/-- Free-variable weakening: the typing of each residual telescope is weakened, its syntax is
`TrSyn.weakFV`. No well-formed context is needed. -/
theorem weakFV (henv : env.Ordered) :
    TelWF env Us m Δ e e' → ∀ {Δ' : VLCtx} {dk n k}, VLCtx.FVLift Δ Δ' dk n k →
      Δ'.fvars.Nodup → TrSyn Us Δ e e' → TelWF env Us m Δ' e (e'.liftN n k) := by
  intro T
  induction T with
  | zero h1 h2 =>
    intro Δ' dk n k W hnd _
    exact .zero (let ⟨_, h⟩ := h1; ⟨_, h.weakN henv W.toCtx⟩) (h2.weakFV henv W hnd)
  | succ h1 h2 _ _ ih3 ih4 =>
    intro Δ' dk n k W hnd S
    let .forallE _ sb := S
    refine .succ (let ⟨_, h⟩ := h1; ⟨_, h.weakN henv W.toCtx⟩) (h2.weakFV henv W hnd)
      (ih3 (W.cons_bvar (.vlam _)) hnd sb) ?_
    intro c c' hc hc'
    subst hc
    obtain ⟨b₀', s, hb'⟩ := sb.lower
    change _ = VExpr.lift b₀' at hb'
    subst hb'
    rw [← VExpr.lift_liftN'] at hc'
    cases VExpr.liftN_inj.1 hc'
    exact ih4 _ _ rfl rfl W hnd s

/-- Substitution of a typed term for a variable of the context. The certified binders of the
spine are those of `e`; deletion at a binder commutes with substitution at the others. -/
theorem instN (henv : env.Ordered) (s₀ : TrSyn Us Δ₀ e₀ e₀') (r₀ : TrResidual env Us Δ₀ e₀)
    (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀) :
    TelWF env Us m Δ₁ e e' → ∀ {Δ : VLCtx} {dk k}, VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ →
      TrSyn Us Δ₁ e e' → TelWF env Us m Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
  intro T
  induction T with
  | zero h1 h2 =>
    intro Δ dk k W _
    exact .zero (let ⟨_, h⟩ := h1; ⟨_, HasType.instN henv W.toCtx h t₀⟩) (TrResidual.instN s₀ r₀ henv t₀ W h2)
  | succ h1 h2 _ _ ih3 ih4 =>
    intro Δ dk k W S
    let .forallE _ sb := S
    refine .succ (let ⟨_, h⟩ := h1; ⟨_, HasType.instN henv W.toCtx h t₀⟩) (TrResidual.instN s₀ r₀ henv t₀ W h2)
      (ih3 (W.succ (d := .vlam _)) sb) ?_
    intro c c' hc hc'
    obtain ⟨b₀, hb, rfl⟩ := Expr.instantiate1'_eq_liftLooseBVars' hc
    subst hb
    obtain ⟨b₀', s, hb'⟩ := sb.lower
    change _ = VExpr.lift b₀' at hb'
    subst hb'
    rw [← VExpr.lift_instN_lo] at hc'
    cases VExpr.liftN_inj.1 hc'
    exact ih4 _ _ rfl rfl W s

end TelWF

/-! ### The depth-bounded certificate -/

namespace TelTrN

theorem toTrTyped (H : TelTrN env Us n Δ e e') : TrTyped env Us Δ e e' :=
  ⟨H.syn, H.tel.wf, H.tel.residual⟩

theorem toTrExprS (henv : env.Ordered) (hΔ : Δ.WF env Us.length) (H : TelTrN env Us n Δ e e') :
    TrExprS env Us Δ e e' :=
  H.toTrTyped.toTrExprS henv hΔ

/-- At depth zero the certificate is a typed translation. -/
theorem zero (henv : env.Ordered) (hΔ : Δ.WF env Us.length) (H : TrExprS env Us Δ e e') :
    TelTrN env Us 0 Δ e e' :=
  ⟨H.toTrSyn, .zero (H.wf henv hΔ) H.residual⟩

theorem mono (henv : env ≤ env') (H : TelTrN env Us n Δ e e') : TelTrN env' Us n Δ e e' :=
  ⟨H.syn, H.tel.mono henv⟩

/-- A positive-depth certificate is a syntactic `forallE`. -/
theorem forallE_of_succ (H : TelTrN env Us (n + 1) Δ e e') :
    ∃ nm d b bi d' b', e = .forallE nm d b bi ∧ e' = .forallE d' b' := by
  cases H.tel; exact ⟨_, _, _, _, _, _, rfl, rfl⟩

theorem keep (H : TelTrN env Us (n + 1) Δ (.forallE nm d b bi) (.forallE d' b')) :
    TelTrN env Us n ((none, .vlam d') :: Δ) b b' := by
  obtain ⟨S, T⟩ := H
  let .forallE _ sb := S
  cases T with | succ _ _ h3 _ => exact ⟨sb, h3⟩

/-- The delete branch at the head binder, for a body without loose bound variables (the form in
which the executable meets it): the lowered translation and its relation to the body are
syntactic (`TrSyn.lower`), the certificate supplies the typing of the lowered telescope in the
smaller context. -/
theorem delete_closed (H : TelTrN env Us (n + 1) Δ (.forallE nm d b bi) (.forallE d' b'))
    (hb : b.looseBVarRange' ≤ 0) : ∃ b₀', b' = VExpr.lift b₀' ∧ TelTrN env Us n Δ b b₀' := by
  obtain ⟨S, T⟩ := H
  have e : b = Expr.liftLooseBVars' b 0 1 := (Expr.liftLooseBVars_eq_self hb).symm
  let .forallE _ sb := S
  rw [e] at sb
  obtain ⟨b₀', s, hb'⟩ := sb.lower
  cases T with
  | succ _ _ _ h4 => exact ⟨b₀', hb', s, h4 _ _ e hb'⟩

theorem weakFV (henv : env.Ordered) (W : VLCtx.FVLift Δ Δ' dk n k) (hnd : Δ'.fvars.Nodup)
    (H : TelTrN env Us m Δ e e') : TelTrN env Us m Δ' e (e'.liftN n k) :=
  ⟨H.syn.weakFV W hnd, H.tel.weakFV henv W hnd H.syn⟩

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀')
  (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀) in
/-- Substitution of a typed term for a variable of the context. -/
theorem instN (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TelTrN env Us m Δ₁ e e') :
    TelTrN env Us m Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) :=
  ⟨h₀.toTrSyn.instN W H.syn, H.tel.instN henv h₀.toTrSyn h₀.residual t₀ W H.syn⟩

variable! (henv : Ordered env) in
theorem inst {Δ : VLCtx} (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TelTrN env Us m ((none, .vlam A₀) :: Δ) e e') (h₀ : TrExprS env Us Δ e₀ e₀') :
    TelTrN env Us m Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  H.instN henv h₀ t₀ .zero

end TelTrN

theorem _root_.Lean.Expr.instantiateLevelParams_forallE {n : Name} {d b : Expr} {bi} {ps ls} :
    (Expr.forallE n d b bi).instantiateLevelParams ps ls =
      .forallE n (d.instantiateLevelParams ps ls) (b.instantiateLevelParams ps ls) bi := by
  simp [Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore']

section
variable {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (henv : VEnv.WF env)
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)

include henv Hls eq in
/-- Level instantiation, into any context definitionally equal to the instantiated one: the
syntactic translation of the instantiated source is certified. The typing at each node comes
from the typed translation of the source (`TrExprS.instL`); the keep branch follows the actual
translated domain of the instantiated binder; the delete branch is `TrSyn.lower`. -/
theorem TelWF.instL_core :
    TelWF env ps m Δ e e' → TrSyn ps Δ e e' → VLCtx.WF env ps.length Δ →
    ∀ {Δ₂ e₁}, VLCtx.IsDefEq env Us.length (Δ.instL ls') Δ₂ →
      TrSyn Us Δ₂ (e.instantiateLevelParams ps ls) e₁ →
      TelWF env Us m Δ₂ (e.instantiateLevelParams ps ls) e₁ := by
  have hlen : ls'.length = ps.length := by
    rw [eq]; exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 Hls)).symm
  have top : ∀ {Δ e e' Δ₂ e₁}, TrExprS env ps Δ e e' → VLCtx.WF env ps.length Δ →
      VLCtx.IsDefEq env Us.length (Δ.instL ls') Δ₂ →
      TrSyn Us Δ₂ (e.instantiateLevelParams ps ls) e₁ →
      TrExprS env Us Δ₂ (e.instantiateLevelParams ps ls) e₁ := by
    intro Δ e e' Δ₂ e₁ h hΔ hΔ₂ s
    obtain ⟨X, hX, -⟩ := h.instL henv (hlen ▸ hΔ) Hls eq
    obtain ⟨Y, hY⟩ := hX.defeqDFC henv hΔ₂
    cases hY.toTrSyn.unique s
    exact hY
  intro T
  induction T with
  | zero h1 h2 =>
    intro S hΔ Δ₂ e₁ hΔ₂ s
    have H₂ := top (TrTyped.toTrExprS henv.ordered hΔ ⟨S, h1, h2⟩) hΔ hΔ₂ s
    exact .zero (H₂.wf henv.ordered (hΔ₂.symm henv.ordered).wf) H₂.residual
  | @succ k Δ n d b bi d' b' h1 h2 _ _ ih3 ih4 =>
    intro S hΔ Δ₂ e₁ hΔ₂ s
    have h1' := TrTyped.toTrExprS henv.ordered hΔ ⟨S, h1, h2⟩
    have H₂ := top h1' hΔ hΔ₂ s
    have hΔ₂wf := (hΔ₂.symm henv.ordered).wf
    have hwf₂ := H₂.wf henv.ordered hΔ₂wf
    have hr₂ := H₂.residual
    rw [Expr.instantiateLevelParams_forallE] at H₂ hr₂ ⊢
    obtain ⟨d₁, b₁, rfl, hd₁T, hd₁, hb₁⟩ : ∃ d₁ b₁, e₁ = .forallE d₁ b₁ ∧
        env.IsType Us.length Δ₂.toCtx d₁ ∧
        TrExprS env Us Δ₂ (d.instantiateLevelParams ps ls) d₁ ∧
        TrExprS env Us ((none, .vlam d₁) :: Δ₂) (b.instantiateLevelParams ps ls) b₁ := by
      cases H₂ with | forallE h1 _ h3 h4 => exact ⟨_, _, rfl, h1, h3, h4⟩
    let .forallE hd'T _ hd _ := h1'
    let .forallE _ sb := S
    have hΔ' : VLCtx.WF env ls'.length Δ := hlen ▸ hΔ
    have hΓ := hΔ₂.wf.toCtx
    have hΓ₂ := (hΔ₂.symm henv.ordered).defeqCtx
    -- the instantiated domain agrees with the actual translated domain
    obtain ⟨X, hX, hXeq⟩ := hd.instL henv hΔ' Hls eq
    have hu : VEnv.IsDefEqU env Us.length (Δ.instL ls').toCtx (d'.instL ls') _ :=
      hXeq.symm.trans henv hΓ (hX.uniq henv hΔ₂ hd₁)
    obtain ⟨u, hd₁u⟩ := hd₁T.defeqDFC henv.ordered hΓ₂
    have hdd := (hu.symm.of_l henv hΓ hd₁u).symm
    have hΔ₂' : VLCtx.IsDefEq env Us.length
        (VLCtx.instL ((none, .vlam d') :: Δ) ls') ((none, .vlam d₁) :: Δ₂) :=
      .cons hΔ₂ (fun _ _ h => by cases h) (.vlam hdd)
    refine .succ hwf₂ hr₂ (ih3 sb ⟨hΔ, nofun, hd'T⟩ hΔ₂' hb₁.toTrSyn) ?_
    intro c c' hc hc'
    obtain ⟨b₀, hb, rfl⟩ := Expr.instantiateLevelParams_eq_liftLooseBVars' hc
    subst hb
    obtain ⟨b₀', s₀, hb'⟩ := sb.lower
    change _ = VExpr.lift b₀' at hb'
    subst hb'
    have sb₁ := hb₁.toTrSyn
    rw [hc] at sb₁
    obtain ⟨c₂, s₂, hc₂⟩ := sb₁.lower
    change _ = VExpr.lift c₂ at hc₂
    rw [hc₂] at hc'
    cases VExpr.liftN_inj.1 hc'
    exact ih4 _ _ rfl rfl s₀ hΔ hΔ₂ s₂

include henv Hls eq in
/-- Level instantiation of a closed certificate (mirrors `TrExprS.instL_lequiv`). -/
theorem TelTrN.instL_lequiv (H : TelTrN env ps m [] e e') :
    ∃ e₁, TelTrN env Us m [] (e.instantiateLevelParams ps ls) e₁ ∧
      VExpr.LEquiv Us.length e₁ (e'.instL ls') := by
  obtain ⟨e₁, h1, h2⟩ :=
    (H.toTrExprS henv.ordered (show VLCtx.WF env _ [] from trivial)).instL_lequiv Hls eq henv (Δ := []) trivial
  exact ⟨e₁, ⟨h1.toTrSyn, H.tel.instL_core henv Hls eq H.syn trivial .nil h1.toTrSyn⟩, h2⟩

end

theorem _root_.Lean4Lean.AddInductive.constructorArity_liftLooseBVars' {e : Expr} {s d : Nat} :
    AddInductive.constructorArity (Expr.liftLooseBVars' e s d) = AddInductive.constructorArity e := by
  induction e generalizing s <;> simp_all [Expr.liftLooseBVars', AddInductive.constructorArity]

/-! ### Certificates of the primitive constructor types -/

theorem TrExprS.const_wf {Γ : List VExpr} (H : TrExprS env Us Δ (.const c us) e) :
    VExpr.WF env Us.length Γ e := by
  cases H with
  | const h1 h2 h3 =>
    exact ⟨_, VEnv.HasType.const h1 (.of_mapM_ofLevel h2) ((Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 h2)).symm.trans h3)⟩

/-- A constant needs no certificate beyond its translation. -/
theorem TelTrN.const (H : TrExprS env Us Δ (.const c us) e) :
    TelTrN env Us (AddInductive.constructorArity (.const c us)) Δ (.const c us) e :=
  ⟨H.toTrSyn, .zero H.const_wf .const⟩

/-- A non-dependent arrow between constants (`Nat → Nat`) is certified along its spine. -/
theorem TelTrN.constArrow
    (H : TrExprS env Us Δ (.forallE n (.const a as) (.const c cs) bi) e) :
    TelTrN env Us (AddInductive.constructorArity (.forallE n (.const a as) (.const c cs) bi))
      Δ (.forallE n (.const a as) (.const c cs) bi) e := by
  cases H with
  | forallE h1 h2 hd hb =>
    have hbc := hb
    cases hbc
    have ⟨_, hT⟩ := VEnv.IsType.forallE h1 h2
    refine ⟨.forallE hd.toTrSyn hb.toTrSyn,
      .succ ⟨_, hT⟩ (.forallE hd.toTrSyn .const .const) (.zero hb.const_wf .const) ?_⟩
    intro b₀ b₀' e₀ e₀'
    have hb₀ : b₀ = .const c cs := by
      cases b₀ <;> simp [Expr.liftLooseBVars'] at e₀
      obtain ⟨rfl, rfl⟩ := e₀; rfl
    subst hb₀
    cases b₀' <;> simp [VExpr.lift, VExpr.liftN] at e₀'
    obtain ⟨rfl, rfl⟩ := e₀'
    exact .zero hb.const_wf .const

/-! ### The environment invariant -/

/-- The certificate of one constructor: the computed syntactic translation of its stored type,
with the typing-only certificate `TelWF` along its whole syntactic `forallE` spine. -/
def CtorTelescopeAt (venv : VEnv) (ci : ConstructorVal) : Prop :=
  ∃ T, trSyn? ci.levelParams [] ci.type = some T ∧
    TelWF venv ci.levelParams (AddInductive.constructorArity ci.type) [] ci.type T

theorem CtorTelescopeAt.iff_telTrN {venv : VEnv} {ci : ConstructorVal} :
    CtorTelescopeAt venv ci ↔
      ∃ T, TelTrN venv ci.levelParams (AddInductive.constructorArity ci.type) [] ci.type T :=
  ⟨fun ⟨T, h1, h2⟩ => ⟨T, .of_eval h1, h2⟩, fun ⟨T, H⟩ => ⟨T, H.syn.eval, H.tel⟩⟩

theorem CtorTelescopeAt.of_telTrN {venv : VEnv} {ci : ConstructorVal}
    (H : TelTrN venv ci.levelParams (AddInductive.constructorArity ci.type) [] ci.type T) :
    CtorTelescopeAt venv ci :=
  iff_telTrN.2 ⟨T, H⟩

theorem CtorTelescopeAt.mono (henv : venv ≤ venv') :
    CtorTelescopeAt venv ci → CtorTelescopeAt venv' ci
  | ⟨T, h1, h2⟩ => ⟨T, h1, h2.mono henv⟩

/-- Every constructor of the kernel environment `env` visible at `safety` is certified. This is
the environment invariant that the projection walk of `inferProj` reads at its non-dependent
fields (section 5.3 of the design notes). -/
def CtorTelescopes (safety : DefinitionSafety) (env : Lean.Kernel.Environment) (venv : VEnv) :
    Prop :=
  ∀ ⦃name : Name⦄ ⦃ci : ConstructorVal⦄, env.find? name = some (.ctorInfo ci) →
    safety ≤ (ConstantInfo.ctorInfo ci).safety → CtorTelescopeAt venv ci

theorem CtorTelescopes.mono (H : CtorTelescopes safety env venv) (henv : venv ≤ venv') :
    CtorTelescopes safety env venv' := fun _ _ h hs => (H h hs).mono henv

end Lean4Lean

/-! ### Transport along `Expr.eqv` (equality up to binder names and annotations) -/

namespace Lean.Expr

theorem hasLooseBVar'_eqv {e₁ e₂ : Expr} :
    e₁ == e₂ → e₁.hasLooseBVar' k = e₂.hasLooseBVar' k := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ k <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals (try simp [Expr.eqv', hasLooseBVar']) <;> (try intros) <;> (try subst_vars) <;>
    (try simp_all) <;> grind

theorem liftLooseBVars'_eqv_inv {x y : Expr} {k d : Nat} :
    liftLooseBVars' x k d == liftLooseBVars' y k d → x == y := by
  simp [(· == ·)]
  induction x generalizing y k <;> (cases y <;> simp [liftLooseBVars', Expr.eqv'])
  all_goals grind

end Lean.Expr

theorem Lean4Lean.AddInductive.constructorArity_eqv {e₁ e₂ : Lean.Expr} :
    e₁ == e₂ → AddInductive.constructorArity e₁ = AddInductive.constructorArity e₂ := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Lean.Expr.eqv', AddInductive.constructorArity]
  all_goals grind

namespace Lean4Lean
open Lean

theorem TelWF.eqv (henv : env.Ordered) :
    TelWF env Us n Δ e₁ e' → TrSyn Us Δ e₁ e' → Δ.WF env Us.length →
      ∀ {e₂ : Expr}, e₁ == e₂ → TelWF env Us n Δ e₂ e' := by
  intro T
  induction T with
  | zero h1 h2 =>
    intro S hΔ e₂ heq
    exact .zero h1 ((TrTyped.toTrExprS henv hΔ ⟨S, h1, h2⟩).eqv heq).residual
  | @succ k Δ nm d b bi d' b' h1 h2 _ _ ih3 ih4 =>
    intro S hΔ e₂ heq
    have hTop := TrTyped.toTrExprS henv hΔ ⟨S, h1, h2⟩
    let .forallE hd _ _ _ := hTop
    let .forallE _ sb := S
    cases e₂ with
    | forallE nm₂ d₂ b₂ bi₂ =>
      have hb : b == b₂ := by
        simp only [(· == ·)] at heq ⊢
        simp [Expr.eqv'] at heq ⊢; exact heq.2
      refine .succ h1 (hTop.eqv heq).residual (ih3 sb ⟨hΔ, nofun, hd⟩ hb) ?_
      intro c c' hc hc'
      have h0 : b.hasLooseBVar' 0 = false := by
        rw [Expr.hasLooseBVar'_eqv hb, hc]; exact Expr.hasLooseBVar'_liftLooseBVars'_self
      have hb0 := Expr.eq_liftLooseBVars'_lower h0
      have sb' : TrSyn Us ((none, .vlam d') :: Δ)
          (Expr.liftLooseBVars' (b.lowerLooseBVars' 1 1) 0 1) b' := by rw [← hb0]; exact sb
      obtain ⟨b₀', s₀, hb'⟩ := sb'.lower
      change _ = VExpr.lift b₀' at hb'
      cases VExpr.liftN_inj.1 (hc'.symm.trans hb')
      refine ih4 _ _ hb0 hb' s₀ hΔ (Expr.liftLooseBVars'_eqv_inv (k := 0) (d := 1) ?_)
      rw [← hb0, ← hc]; exact hb
    | _ => simp [(· == ·), Expr.eqv'] at heq

theorem TelTrN.eqv (henv : env.Ordered) (hΔ : Δ.WF env Us.length) {e₁ e₂ : Expr}
    (H : TelTrN env Us n Δ e₁ e') (heq : e₁ == e₂) : TelTrN env Us n Δ e₂ e' :=
  ⟨H.syn.eqv heq, H.tel.eqv henv H.syn hΔ heq⟩

/-- A closed constructor certificate moves along `Expr.eqv` with its depth. -/
theorem TelTrN.eqv_arity (henv : env.Ordered) {e₁ e₂ : Expr}
    (H : TelTrN env Us (AddInductive.constructorArity e₁) [] e₁ e') (heq : e₁ == e₂) :
    TelTrN env Us (AddInductive.constructorArity e₂) [] e₂ e' :=
  AddInductive.constructorArity_eqv heq ▸ H.eqv henv (show VLCtx.WF env _ [] from trivial) heq

end Lean4Lean
