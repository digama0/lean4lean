import Lean4Lean.Theory.Typing.Strengthening.EtaPostponement

/-! # Replay through eta-normal expansions

Direction B3. General infrastructure: descent of
eta-free parallel steps along any lift (`Ctx.Lift'`), peeling one insertion at a time with
well-formed intermediate contexts, and the renaming `Lift.insVar` of a bound variable to an
inserted variable. Not used by the current proof route (`EtaClosure.lean`), kept for the
lifted formulation of sources. -/

namespace Lean4Lean.VEnv.StrengtheningEtaReplay
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => Params.env.IsDefEq univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => Params.env.IsDefEqU univs Γ e1 e2

/-! ## Peeling one insertion off a lift, with well-formed intermediate context -/

theorem Ctx.Lift'.peel {l : Lift} : ∀ {k : Nat} {Γ₁ Γ₃ : List VExpr},
    Ctx.Lift' (Lift.consN (.skip l) k) Γ₁ Γ₃ → OnCtx Γ₁ (Params.env.IsType univs) →
    OnCtx Γ₃ (Params.env.IsType univs) →
    ∃ Γ₂, Ctx.Lift' (Lift.consN l k) Γ₁ Γ₂ ∧ Ctx.LiftN 1 k Γ₂ Γ₃ ∧
      OnCtx Γ₂ (Params.env.IsType univs) := by
  intro k
  induction k with
  | zero =>
    intro Γ₁ Γ₃ H hΓ₁ hΓ₃
    cases H with
    | skip H => exact ⟨_, H, .one, hΓ₃.1⟩
  | succ k ih =>
    intro Γ₁ Γ₃ H hΓ₁ hΓ₃
    cases H with
    | @cons l' Γ Γ' A H =>
      obtain ⟨Γ₂, h1, h2, hΓ₂⟩ := ih H hΓ₁.1 hΓ₃.1
      refine ⟨A.lift' (Lift.consN l k) :: Γ₂, .cons h1, ?_, hΓ₂, ?_⟩
      · have h2' := h2
        simp only [Ctx.liftN_iff_lift'] at h2' ⊢
        simpa [← VExpr.lift'_comp, ← Lift.consN_comp] using h2'.cons (A := lift' A (.consN l k))
      · obtain ⟨u, hA⟩ := hΓ₁.2
        exact ⟨u, hA.weak' henv.ordered h1⟩

omit [Params] in
theorem lift'_consN_skip (e : VExpr) (l : Lift) (k : Nat) :
    e.lift' (Lift.consN (.skip l) k) = (e.lift' (Lift.consN l k)).liftN 1 k := by
  rw [Lift.consN_skip_eq, lift'_comp]
  exact lift'_consN_skipN (n := 1)

/-! ## Descent of eta-free parallel steps along any lift -/

theorem ParRed.descend' (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2) :
    ∀ (n : Nat) {l : Lift} {Γ₀ Γ₁ : List VExpr} {e T out : VExpr}, l.depth = n →
      Ctx.Lift' l Γ₀ Γ₁ → OnCtx Γ₀ (Params.env.IsType univs) → OnCtx Γ₁ (Params.env.IsType univs) →
      Γ₀ ⊢ e : T → ParRed Γ₁ (e.lift' l) out → ∃ e', out = e'.lift' l ∧ ParRed Γ₀ e e' := by
  intro n
  induction n with
  | zero =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    cases W.depth_zero hd
    rw [lift'_depth_zero hd] at H
    exact ⟨out, (lift'_depth_zero hd).symm, H⟩
  | succ n ih =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    obtain ⟨l', k, hd', rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := Ctx.Lift'.peel W hΓ₀ hΓ₁
    rw [lift'_consN_skip] at H
    obtain ⟨e₁, rfl, H₁⟩ := ParRed.descend hTF hcase hcv W₂ hΓ₂ hΓ₁ (he.weak' henv.ordered W₁) H
    obtain ⟨e', rfl, H'⟩ := ih (by simpa using hd') W₁ hΓ₀ hΓ₂ he H₁
    exact ⟨e', (lift'_consN_skip e' l' k).symm, H'⟩

theorem DeltaPar.descend' (hTF : TypedFrontN Params.env) (hunfold : UnfoldingCheckDescends) :
    ∀ (n : Nat) {l : Lift} {Γ₀ Γ₁ : List VExpr} {e T out : VExpr}, l.depth = n →
      Ctx.Lift' l Γ₀ Γ₁ → OnCtx Γ₀ (Params.env.IsType univs) → OnCtx Γ₁ (Params.env.IsType univs) →
      Γ₀ ⊢ e : T → DeltaPar Γ₁ (e.lift' l) out → ∃ e', out = e'.lift' l ∧ DeltaPar Γ₀ e e' := by
  intro n
  induction n with
  | zero =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    cases W.depth_zero hd
    rw [lift'_depth_zero hd] at H
    exact ⟨out, (lift'_depth_zero hd).symm, H⟩
  | succ n ih =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    obtain ⟨l', k, hd', rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := Ctx.Lift'.peel W hΓ₀ hΓ₁
    rw [lift'_consN_skip] at H
    obtain ⟨e₁, rfl, H₁⟩ := DeltaPar.descend hTF hunfold W₂ hΓ₂ hΓ₁ (he.weak' henv.ordered W₁) H
    obtain ⟨e', rfl, H'⟩ := ih (by simpa using hd') W₁ hΓ₀ hΓ₂ he H₁
    exact ⟨e', (lift'_consN_skip e' l' k).symm, H'⟩

end

/-! ## Renaming a bound variable to an inserted variable

Dissolving the administrative redex `(λ D. t)↑ v` where `v` is an eta variable: the contractum is
`t` renamed by the lift that sends the bound variable to `v` and the free variables as before.
This is a lift (`Lift.insVar`) when `v` is below every image of the lift. -/

end Lean4Lean.VEnv.StrengtheningEtaReplay

namespace Lean4Lean.Lift

/-- The lift sending `0` to `v` and `i+1` to `l.liftVar i`, defined when `v < l.liftVar 0`. -/
def insVar : Lift → Nat → Lift
  | .skip l, 0 => .cons l
  | .skip l, v+1 => .skip (insVar l v)
  | l, _ => l

theorem liftVar_insVar_zero : ∀ {l : Lift} {v : Nat}, v < l.liftVar 0 →
    (l.insVar v).liftVar 0 = v
  | .refl, _, h => by simp at h
  | .cons _, _, h => by simp at h
  | .skip l, 0, _ => by simp [insVar]
  | .skip l, v+1, h => by
    simp only [Lift.liftVar] at h
    simp [insVar, liftVar_insVar_zero (Nat.lt_of_succ_lt_succ h)]

theorem liftVar_insVar_succ : ∀ {l : Lift} {v i : Nat}, v < l.liftVar 0 →
    (l.insVar v).liftVar (i+1) = l.liftVar i
  | .refl, _, _, h => by simp at h
  | .cons _, _, _, h => by simp at h
  | .skip l, 0, i, _ => by simp [insVar]
  | .skip l, v+1, i, h => by
    simp only [Lift.liftVar] at h
    simp [insVar, liftVar_insVar_succ (Nat.lt_of_succ_lt_succ h)]

theorem liftVar_consN : ∀ (l : Lift) (k i : Nat),
    (l.consN k).liftVar i = if i < k then i else l.liftVar (i - k) + k
  | l, 0, i => by simp
  | l, k+1, 0 => by simp
  | l, k+1, i+1 => by
    simp only [Lift.consN, Lift.liftVar, liftVar_consN l k i, Nat.add_sub_add_right]
    split <;> split <;> omega

end Lean4Lean.Lift

namespace Lean4Lean.VEnv.StrengtheningEtaReplay
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement

/-- Substituting an inserted variable for the bound variable of a renamed body is a renaming. -/
theorem lift'_cons_inst_bvar {l : Lift} {v : Nat} (h : v < l.liftVar 0) :
    ∀ (t : VExpr) (k : Nat), (t.lift' ((Lift.cons l).consN k)).inst (.bvar v) k =
      t.lift' ((l.insVar v).consN k) := by
  intro t
  induction t with
  | bvar i =>
    intro k
    simp only [lift', inst, instVar, Lift.liftVar_consN, liftN]
    by_cases hik : i < k
    · simp [hik]
    · simp only [hik, if_false]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + k := ⟨i - k, by omega⟩
      cases j with
      | zero =>
        simp [Lift.liftVar, Lift.liftVar_insVar_zero h, liftVar, Nat.add_comm]
      | succ j =>
        have h1 : ¬ (l.liftVar j + 1 + k < k) := by omega
        have h2 : ¬ (l.liftVar j + 1 + k = k) := by omega
        simp only [Nat.add_sub_cancel, Lift.liftVar, h1, h2, if_false, Lift.liftVar_insVar_succ h]
        congr 1
        omega
  | sort | const | elim => intro k; rfl
  | app f a ihf iha => intro k; simp [lift', inst, ihf, iha]
  | proj _ _ m ih => intro k; simp [lift', inst, ih]
  | lam A b ihA ihb =>
    intro k
    simp only [lift', inst, ihA]
    have := ihb (k+1)
    simpa [Lift.consN] using this
  | forallE A B ihA ihB =>
    intro k
    simp only [lift', inst, ihA]
    have := ihB (k+1)
    simpa [Lift.consN] using this

end Lean4Lean.VEnv.StrengtheningEtaReplay
