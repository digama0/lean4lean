import Lean4Lean.Theory.Typing.Confluence.JoinableTyping

/-! # Structural lemmas for joins

Joins in the full presentation (`FullCRDefEq`) are closed under substitution of a typed term
(`FullCRDefEq.instN`) and under application (`FullCRDefEq.mkApps`), and a join of two Π-types
joins their domains and their bodies (`FullCRDefEq.forallE_inv`). -/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

theorem FullCRDefEq.defeq (hΓ : OnCtx Γ (env.IsType univs)) (H : Γ ⊢ e₁ ≫≪ e₂) :
    Γ ⊢ e₁ ≡ e₂ := by
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, r1, r2, n⟩ := H
  exact IsDefEqU.trans henv hΓ (IsDefEqU.trans henv hΓ ⟨_, r1.defeq hΓ h1⟩ (n.defeq hΓ))
    ⟨_, (r2.defeq hΓ h2).symm⟩

/-! ## Substitution -/

theorem FullStep.instN (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ) (ha : Γ₀ ⊢ a : A₀)
    (H : FullStep Γ₁ e e') : FullStep Γ (e.inst a k) (e'.inst a k) := by
  induction H generalizing Γ k with
  | core h => exact .core (ParRed.instN .rfl ha W h)
  | delta h =>
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .delta (h.instN henv W ha)
  | quotDelta h =>
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .quotDelta (h.instN henv W ha)
  | projIota h1 hs h3 ht =>
    have hs' := hs.instN henv.ordered W ha
    simp only [VExpr.inst_mkApps, VExpr.inst] at hs' ⊢
    exact .projIota h1 hs' (by simp [h3]) (ht.instN henv.ordered W ha)
  | structEta h1 h2 h3 hs ht =>
    have hs' := hs.instN henv.ordered W ha
    have ht' := ht.instN henv.ordered W ha
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    exact .structEta h1 (by simpa using h2) h3 hs' ht'
  | funEta ht =>
    have := FullStep.funEta (ht.instN henv.ordered W ha)
    simpa only [VExpr.inst, lift_instN_lo, instVar, Nat.zero_lt_succ, if_true] using this
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

theorem FullReduction.instN (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ) (ha : Γ₀ ⊢ a : A₀)
    (H : FullReduction Γ₁ e e') : FullReduction Γ (e.inst a k) (e'.inst a k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (h.instN W ha)

theorem FullReduction.weakN (W : Ctx.LiftN n k Γ Γ') (H : FullReduction Γ e e') :
    FullReduction Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (h.weakN W)

theorem FullCRDefEq.instN (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ) (ha : Γ₀ ⊢ a : A₀)
    (H : Γ₁ ⊢ e₁ ≫≪ e₂) : Γ ⊢ e₁.inst a k ≫≪ e₂.inst a k := by
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, r1, r2, n⟩ := H
  exact ⟨⟨_, h1.instN henv.ordered W ha⟩, ⟨_, h2.instN henv.ordered W ha⟩, _, _,
    r1.instN W ha, r2.instN W ha, n.instN ha W⟩

theorem FullCRDefEq.inst0 (ha : Γ ⊢ a : A) (H : A :: Γ ⊢ e₁ ≫≪ e₂) :
    Γ ⊢ e₁.inst a ≫≪ e₂.inst a := H.instN .zero ha

theorem FullCRDefEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e₁ ≫≪ e₂) :
    Γ' ⊢ e₁.liftN n k ≫≪ e₂.liftN n k := by
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, r1, r2, nn⟩ := H
  exact ⟨⟨_, h1.weakN henv.ordered W⟩, ⟨_, h2.weakN henv.ordered W⟩, _, _,
    r1.weakN W, r2.weakN W, nn.weakN W⟩

/-! ## Application -/

theorem FullCRDefEq.app (hΓ : OnCtx Γ (env.IsType univs)) (hf : Γ ⊢ f ≫≪ f')
    (ha : Γ ⊢ a ≫≪ a') (ht : Γ ⊢ .app f a : T) : Γ ⊢ .app f a ≫≪ .app f' a' := by
  obtain ⟨A, B, hft, hat⟩ := ht.app_inv henv.orderedStrong hΓ
  have hf't : Γ ⊢ f' : .forallE A B := hft.defeqU_l henv hΓ (hf.defeq hΓ)
  have ha't : Γ ⊢ a' : A := hat.defeqU_l henv hΓ (ha.defeq hΓ)
  obtain ⟨-, -, _, _, f1, f2, fn⟩ := hf
  obtain ⟨-, -, _, _, a1, a2, an⟩ := ha
  exact ⟨⟨_, ht⟩, ⟨_, hf't.app ha't⟩, _, _, f1.app a1, f2.app a2,
    .appDF (f1.hasType hΓ hft) (f2.hasType hΓ hf't) (a1.hasType hΓ hat) (a2.hasType hΓ ha't)
      fn an⟩

theorem FullCRDefEq.mkApps (hΓ : OnCtx Γ (env.IsType univs)) (hf : Γ ⊢ f ≫≪ f')
    (hargs : List.Forall₂ (FullCRDefEq Γ) as as') (ht : Γ ⊢ VExpr.mkApps f as : T) :
    Γ ⊢ VExpr.mkApps f as ≫≪ VExpr.mkApps f' as' := by
  induction hargs generalizing f f' with
  | nil => exact hf
  | cons h _ ih =>
    obtain ⟨_, happ⟩ := HasType.mkApps_head henv.orderedStrong hΓ (f := .app f _) ht
    exact ih (hf.app hΓ h happ) ht

theorem FullCRDefEq.of_reduction (hΓ : OnCtx Γ (env.IsType univs)) (ht : Γ ⊢ e : T)
    (H : FullReduction Γ e e') : Γ ⊢ e ≫≪ e' :=
  ⟨⟨_, ht⟩, ⟨_, H.hasType hΓ ht⟩, _, _, H, .rfl, .refl (H.hasType hΓ ht)⟩

/-! ## Π-types -/

theorem HasType.forallE_not_struct (hΓ : OnCtx Γ (env.IsType univs))
    (h1 : Γ ⊢ .forallE X Y : T) (hl : env.projections family info)
    (h2 : Γ ⊢ .forallE X Y : VExpr.mkApps (.const family levels) params) : False := by
  have ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ := h1.forallE_inv henv.ordered
  have hs := HasType.forallE hX hY
  have hu := hs.uniqU henv hΓ h2
  have ⟨_, hS⟩ := hs.isType henv.ordered hΓ
  exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hl)
    (hu.typeChain henv hΓ (.sort (hS.sort_inv henv.ordered)))

theorem HasType.forallE_not_pi (hΓ : OnCtx Γ (env.IsType univs))
    (h1 : Γ ⊢ .forallE X Y : T) (h2 : Γ ⊢ .forallE X Y : .forallE D B) : False := by
  have ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ := h1.forallE_inv henv.ordered
  have hs := HasType.forallE hX hY
  exact IsDefEqU.sort_forallE_inv henv hΓ (hs.uniqU henv hΓ h2)

theorem HasType.forallE_not_proof (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Γ ⊢ p : .sort .zero) (h : Γ ⊢ .forallE X Y : p) : False := by
  have ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ := h.forallE_inv henv.ordered
  have hs := HasType.forallE hX hY
  have hu := h.uniqU henv hΓ hs
  have hS : Γ ⊢ .sort _ : .sort .zero := hp.defeqU_l henv hΓ hu
  have ⟨_, hS'⟩ := hs.isType henv.ordered hΓ
  have := IsDefEqU.sort_inv henv hΓ (IsDefEq.uniqU henv hΓ (HasType.sort (hS'.sort_inv henv.ordered)) hS)
  exact absurd (congrFun this []) (by simp [VLevel.eval])

theorem FullStep.forallE_inv (hΓ : OnCtx Γ (env.IsType univs)) (ht : Γ ⊢ .forallE X Y : T)
    (H : FullStep Γ (.forallE X Y) R) :
    ∃ X' Y', R = .forallE X' Y' ∧ FullStep Γ X X' ∧ FullStep (X :: Γ) Y Y' := by
  generalize he : VExpr.forallE X Y = e at H ht
  cases H with
  | core h =>
    cases h with
    | forallE h1 h2 => cases he; exact ⟨_, _, rfl, .core h1, .core h2⟩
    | extra hp hm =>
      obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
      subst he; simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at hh
    | _ => cases he
  | delta => exact absurd he.symm (VExpr.mkApps_ne_forallE (fn := .const _ _) (fun _ _ h => nomatch h) _)
  | quotDelta => exact absurd he.symm (VExpr.mkApps_ne_forallE (fn := .const _ _) (fun _ _ h => nomatch h) _)
  | structEta hl _ _ hs => subst he; exact (ht.forallE_not_struct hΓ hl hs).elim
  | funEta h => subst he; exact (ht.forallE_not_pi hΓ h).elim
  | forallE h1 h2 => cases he; exact ⟨_, _, rfl, h1, h2⟩
  | _ => cases he

theorem FullReduction.forallE_inv (hΓ : OnCtx Γ (env.IsType univs)) (ht : Γ ⊢ .forallE X Y : T)
    (H : FullReduction Γ (.forallE X Y) R) :
    ∃ X' Y', R = .forallE X' Y' ∧ FullReduction Γ X X' ∧ FullReduction (X :: Γ) Y Y' := by
  induction H with
  | rfl => exact ⟨_, _, rfl, .rfl, .rfl⟩
  | tail before step ih =>
    obtain ⟨X₀, Y₀, rfl, hX, hY⟩ := ih
    have ht₀ := FullReduction.hasType hΓ before ht
    obtain ⟨X₁, Y₁, rfl, sX, sY⟩ := step.forallE_inv hΓ ht₀
    have ⟨⟨_, hX₀⟩, ⟨_, hY₀⟩⟩ := ht₀.forallE_inv henv.ordered
    have ⟨⟨_, hX'⟩, _⟩ := ht.forallE_inv henv.ordered
    have hXX := FullReduction.defeq hΓ hX hX'
    exact ⟨_, _, rfl, .tail hX sX, .tail hY (sY.defeqDFC hΓ (.succ .zero hXX.symm) hY₀)⟩

theorem NormalEq.forallE_inv (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ (.forallE X₁ Y₁) (.forallE X₂ Y₂)) :
    NormalEq Γ X₁ X₂ ∧ NormalEq (X₁ :: Γ) Y₁ Y₂ := by
  obtain ⟨n, H⟩ := H
  generalize hl : VExpr.forallE X₁ Y₁ = l at H
  generalize hr : VExpr.forallE X₂ Y₂ = r at H
  cases H with
  | refl h =>
    subst hl; cases hr
    have ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ := h.forallE_inv henv.ordered
    exact ⟨.refl hX, .refl hY⟩
  | forallEDF hA hX hB hY =>
    cases hl; cases hr
    exact ⟨⟨_, hX⟩, ⟨_, hY.defeqDFC hΓ (.succ .zero hA)⟩⟩
  | proofIrrel h1 h2 _ => subst hl; exact (HasType.forallE_not_proof hΓ h1 h2).elim
  | etaBoth h1 _ _ =>
    subst hl
    have ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ := h1.forallE_inv henv.ordered
    exact ((HasType.forallE hX hY).forallE_not_pi hΓ h1).elim
  | _ => first | (cases hl; done) | (cases hr; done)

/-- **Injectivity of joins of Π-types.** -/
theorem FullCRDefEq.forallE_inv (hΓ : OnCtx Γ (env.IsType univs))
    (H : Γ ⊢ .forallE X Y ≫≪ .forallE X' Y') : Γ ⊢ X ≫≪ X' ∧ X :: Γ ⊢ Y ≫≪ Y' := by
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, r1, r2, n⟩ := H
  obtain ⟨X₁, Y₁, rfl, rX, rY⟩ := r1.forallE_inv hΓ h1
  obtain ⟨X₂, Y₂, rfl, rX', rY'⟩ := r2.forallE_inv hΓ h2
  obtain ⟨nX, nY⟩ := n.forallE_inv hΓ
  have ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ := h1.forallE_inv henv.ordered
  have ⟨⟨_, hX'⟩, ⟨_, hY'⟩⟩ := h2.forallE_inv henv.ordered
  have jX : Γ ⊢ X ≫≪ X' := ⟨⟨_, hX⟩, ⟨_, hX'⟩, _, _, rX, rX', nX⟩
  have dX : Γ ⊢ X ≡ X' : _ := (jX.defeq hΓ).of_l henv hΓ hX
  have dX₁ := rX.defeq hΓ hX
  have hY'' := hY'.defeqDFC henv.ordered (.succ .zero dX.symm)
  exact ⟨jX, ⟨_, hY⟩, ⟨_, hY''⟩, _, _, rY, rY'.defeqDFC hΓ (.succ .zero dX.symm) hY',
    nY.defeqDFC hΓ (.succ .zero dX₁.symm)⟩

/-! ## Equivalent universe levels -/

/-- Terms equal up to equivalent universe levels are normally equal. -/
theorem NormalEq.of_eqUpToLevels (H : EqUpToLevels univs e e') :
    ∀ {Γ T}, OnCtx Γ (env.IsType univs) → Γ ⊢ e : T → NormalEq Γ e e' := by
  induction H with
  | bvar => intro Γ T _ h; exact .refl h
  | const h1 h2 h3 =>
    intro Γ T hΓ h
    obtain ⟨ci, hc, hw, hl⟩ := h.const_inv henv.orderedStrong hΓ
    exact .constDF hc h1 h2 hl h3
  | sort h1 h2 h3 => intro Γ T _ _; exact .sortDF h1 h2 h3
  | app hf ha ihf iha =>
    intro Γ T hΓ h
    obtain ⟨A, B, hft, hat⟩ := h.app_inv henv.orderedStrong hΓ
    have hft' := (IsDefEq.eqUpToLevels henv.orderedStrong hΓ hft hf).hasType.2
    have hat' := (IsDefEq.eqUpToLevels henv.orderedStrong hΓ hat ha).hasType.2
    exact .appDF hft hft' hat hat' (ihf hΓ hft) (iha hΓ hat)
  | proj _ ih =>
    intro Γ T hΓ h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := h.proj_inv henv.orderedStrong hΓ
    exact .projDF h (ih hΓ hm.hasType.2)
  | lam hA hb ihA ihb =>
    intro Γ T hΓ h
    obtain ⟨⟨_, hAt⟩, _, hbt⟩ := h.lam_inv henv.orderedStrong hΓ
    have hAA := IsDefEq.eqUpToLevels henv.orderedStrong hΓ hAt hA
    exact .lamDF hAt hAA (ihb ⟨hΓ, _, hAt⟩ hbt)
  | forallE hA hB ihA ihB =>
    intro Γ T hΓ h
    obtain ⟨⟨_, hAt⟩, _, hBt⟩ := h.forallE_inv henv.ordered
    exact .forallEDF hAt (ihA hΓ hAt) hBt (ihB ⟨hΓ, _, hAt⟩ hBt)

/-- Instantiations of a typed term at equivalent universe levels join. -/
theorem FullCRDefEq.of_eqUpToLevels (hΓ : OnCtx Γ (env.IsType univs)) (H : EqUpToLevels univs e e')
    (h : Γ ⊢ e : T) : Γ ⊢ e ≫≪ e' :=
  .normalEq hΓ (NormalEq.of_eqUpToLevels H hΓ h)

end Lean4Lean.VEnv
