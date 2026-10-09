import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.PrefixUnfolding.Weakening
import Lean4Lean.Theory.Typing.PrefixUnfolding.RuleLevelCongruence
import Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution
import Lean4Lean.Theory.Typing.PrefixUnfolding.NormalCongruence
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLiftRenaming
import Lean4Lean.Theory.Typing.PrefixUnfolding.Supply
import Lean4Lean.Theory.Typing.ProjectionIndexBound
import Lean4Lean.Theory.Typing.ProjectionProofResult
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.RecursorMajorFamily

/-! The stored-rule/case-schema parallel calculus is the core of this presentation.
Singleton and quotient prefix unfolding extend it with declaration-generated
computation. Typed function and structure eta expansions allow computation
beneath extensional equalities. Different prefix lengths can require multiple
beta steps to join; the confluence obligation uses a global strip property.
-/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

/-- Concrete reduction, closed under syntax. The delta branch contains only
the deterministic finite program and its actual declaration replay checks. -/
inductive FullStep : List VExpr → VExpr → VExpr → Prop where
  | core : ParRed Γ source target → FullStep Γ source target
  | delta : PrefixUnfold env univs recursorData Γ name levels arguments rhs →
      FullStep Γ (VExpr.mkApps (.const name levels) arguments) rhs
  | quotDelta : QuotPrefixUnfold env univs Γ levels arguments rhs →
      FullStep Γ (VExpr.mkApps (.const ``Quot.lift levels) arguments) rhs
  | projIota : env.projections family info →
      HasType env univs Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) fieldType →
      args[info.nparams + index]? = some field → HasType env univs Γ field fieldType →
      FullStep Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) field
  | structEta : env.projections family info → params.length = info.nparams → info.nindices = 0 →
      HasType env univs Γ e (VExpr.mkApps (.const family levels) params) →
      HasType env univs Γ
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index e))
        (VExpr.mkApps (.const family levels) params) →
      FullStep Γ e
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index e))
  /-- Function eta expansion is an actual reduction in the full presentation.
  This lets structure and prefix computation proceed beneath eta binders. -/
  | funEta : HasType env univs Γ e (.forallE domain body) →
      FullStep Γ e (.lam domain (.app e.lift (.bvar 0)))
  | app : FullStep Γ fn fn' → FullStep Γ arg arg' →
      FullStep Γ (.app fn arg) (.app fn' arg')
  | proj : FullStep Γ major major' →
      FullStep Γ (.proj family index major) (.proj family index major')
  | lam : FullStep Γ domain domain' → FullStep (domain :: Γ) body body' →
      FullStep Γ (.lam domain body) (.lam domain' body')
  | forallE : FullStep Γ domain domain' → FullStep (domain :: Γ) body body' →
      FullStep Γ (.forallE domain body) (.forallE domain' body')

protected theorem FullStep.rfl : FullStep Γ e e := .core .rfl

theorem FullStep.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullStep Γ e e') (he : HasType env univs Γ e A) :
    IsDefEq env univs Γ e e' A := by
  induction H generalizing A with
  | core h => exact h.defeq hΓ he
  | delta h => exact (h.defeq henv hΓ).of_l henv hΓ he
  | quotDelta h => exact (h.defeq henv hΓ).of_l henv hΓ he
  | projIota hl hs hi ht => exact .trans_l henv hΓ he (.projIota hl hs hi ht)
  | structEta hl hp hi hs ht => exact .trans_l henv hΓ he (IsDefEq.structEta hl hp hi hs ht).symm
  | funEta ht => exact .trans_l henv hΓ he (IsDefEq.eta ht).symm
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .trans_l henv hΓ he (.appDF (ih1 hΓ h1) (ih2 hΓ h2))
  | proj _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := he.proj_inv henv hΓ
    have majorEq := ihMajor hΓ hmajor.hasType.2
    have projected := IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hmajor (hmajor.trans majorEq) hclosed hguard
    have ⟨_, typeToA⟩ := projected.hasType.1.uniq henv hΓ he
    exact .defeqDF typeToA projected
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact .trans_l henv hΓ he (.lamDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2))
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .trans_l henv hΓ he (.forallEDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2))

theorem FullStep.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullStep Γ e e') (he : HasType env univs Γ e A) :
    HasType env univs Γ e' A := (H.defeq hΓ he).hasType.2

theorem FullStep.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : FullStep Γ₁ e e') (he : HasType env univs Γ₁ e A) : FullStep Γ₂ e e' := by
  induction H generalizing Γ₂ A with
  | core h => exact .core (h.defeqDFC hΓ W he)
  | delta h => exact .delta (h.defeqDFC henv hΓ W)
  | quotDelta h => exact .quotDelta (h.defeqDFC henv hΓ W)
  | projIota hl hs hi ht => exact .projIota hl (hs.defeqDFC henv W) hi (ht.defeqDFC henv W)
  | structEta hl hp hi hs ht => exact .structEta hl hp hi (hs.defeqDFC henv W) (ht.defeqDFC henv W)
  | funEta ht => exact .funEta (ht.defeqDFC henv W)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hd) (ih2 (.succ W hd) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hd) (ih2 (.succ W hd) hb)

theorem FullStep.weakN (W : Ctx.LiftN n k Γ Γ') (H : FullStep Γ e e') :
    FullStep Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | core h => exact .core (h.weakN W)
  | delta h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .delta (h.weakN henv W)
  | quotDelta h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .quotDelta (h.weakN henv W)
  | projIota h1 hs h3 ht =>
    have hs' := hs.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at hs' ⊢
    exact .projIota h1 hs' (by simp [h3]) (ht.weakN henv W)
  | structEta h1 h2 h3 hs ht =>
    have hs' := hs.weakN henv W
    have ht' := ht.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def] at hs' ht' ⊢
    exact .structEta h1 (by simpa using h2) h3 hs' ht'
  | funEta ht =>
    simpa only [VExpr.liftN, ← VExpr.lift_liftN', liftVar_zero] using
      (FullStep.funEta (ht.weakN henv W))
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihd ihb => exact .lam (ihd W) (ihb W.succ)
  | forallE _ _ ihd ihb => exact .forallE (ihd W) (ihb W.succ)

def FullReduction (Γ : List VExpr) : VExpr → VExpr → Prop :=
  ReflTransGen (FullStep Γ)

theorem ParRedS.full (H : ParRedS Γ e e') : FullReduction Γ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.core h)

theorem FullReduction.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullReduction Γ e e') (he : HasType env univs Γ e A) :
    HasType env univs Γ e' A := by
  induction H with
  | rfl => exact he
  | tail _ h ih => exact h.hasType hΓ ih

theorem FullReduction.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : FullReduction Γ e e') (he : HasType env univs Γ e A) :
    IsDefEq env univs Γ e e' A := by
  induction H with
  | rfl => exact he
  | tail _ h ih => exact ih.trans (h.defeq hΓ ih.hasType.2)

theorem FullReduction.app (hf : FullReduction Γ f f') (ha : FullReduction Γ a a') :
    FullReduction Γ (.app f a) (.app f' a') := by
  have right : FullReduction Γ (.app f a) (.app f a') := by
    induction ha with
    | rfl => exact .rfl
    | tail _ h ih => exact .tail ih (.app .rfl h)
  refine right.trans ?_
  induction hf with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.app h .rfl)

theorem FullReduction.mkApps (head : FullReduction Γ fn fn')
    (args : List.Forall₂ (FullReduction Γ) arguments arguments') :
    FullReduction Γ (mkApps fn arguments) (mkApps fn' arguments') := by
  induction args generalizing fn fn' with
  | nil => exact head
  | cons ha _ ih => exact ih (head.app ha)

theorem FullReduction.lam (hd : FullReduction Γ d d')
    (hb : FullReduction (d :: Γ) b b') : FullReduction Γ (.lam d b) (.lam d' b') := by
  have body : FullReduction Γ (.lam d b) (.lam d b') := by
    induction hb with
    | rfl => exact .rfl
    | tail _ h ih => exact .tail ih (.lam .rfl h)
  refine body.trans ?_
  induction hd with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.lam h .rfl)

theorem FullReduction.proj (H : FullReduction Γ e e') :
    FullReduction Γ (.proj family index e) (.proj family index e') := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.proj h)

theorem FullReduction.forallE (hd : FullReduction Γ d d')
    (hb : FullReduction (d :: Γ) b b') : FullReduction Γ (.forallE d b) (.forallE d' b') := by
  have body : FullReduction Γ (.forallE d b) (.forallE d b') := by
    induction hb with
    | rfl => exact .rfl
    | tail _ h ih => exact .tail ih (.forallE .rfl h)
  refine body.trans ?_
  induction hd with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (.forallE h .rfl)

theorem FullReduction.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : FullReduction Γ₁ e e') (he : HasType env univs Γ₁ e A) : FullReduction Γ₂ e e' := by
  induction H with
  | rfl => exact .rfl
  | tail before h ih => exact .tail ih (h.defeqDFC hΓ W (FullReduction.hasType (W.isType' hΓ) before he))

/-- Structure expansion respects normal equality of the major. All field
projections are taken at the same concrete registry entry and parameter spine. -/
theorem NormalEq.fullStep_structEta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right)
    (hl : env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0)
    (hs : HasType env univs Γ right (mkApps (.const family levels) params))
    (ht : HasType env univs Γ
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj family index right))
      (mkApps (.const family levels) params)) :
    ∃ output, FullReduction Γ left output ∧
      NormalEq Γ output
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj family index right)) := by
  have hsleft := ((H.defeq hΓ).of_r henv hΓ hs).hasType.1
  have hargs := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, ht⟩
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  have hparams : List.Forall₂ (NormalEq Γ) params params := by
    apply List.forall₂_of_getElem rfl
    intro i hi hi'
    obtain ⟨_, h⟩ := hargs _ (List.mem_append_left _ (List.getElem_mem hi))
    exact .refl h
  have hfields : List.Forall₂ (NormalEq Γ)
      ((List.range info.numFields).map fun index => .proj family index right)
      ((List.range info.numFields).map fun index => .proj family index left) := by
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    have himem : i ∈ List.range info.numFields := by simpa using hi
    obtain ⟨_, h⟩ := hargs _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, himem, rfl⟩))
    simpa only [List.getElem_map, List.getElem_range] using
      (NormalEq.projDF h (H.symm hΓ))
  have hctorEq := NormalEq.mkApps_spine hΓ (.refl hhead) (List.Forall₂.append' hparams hfields) ht
  have htleft := ((hctorEq.defeq hΓ).of_l henv hΓ ht).hasType.2
  exact ⟨_, .tail .rfl (.structEta hl hp hi hsleft htleft), hctorEq.symm hΓ⟩


/-- The added function expansion is already one of the structural normal
eta equalities, so it is compatible with every normal-equality derivation. -/
theorem NormalEq.fullStep_funEta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (ht : HasType env univs Γ right (.forallE domain body)) :
    ∃ output, FullReduction Γ left output ∧
      NormalEq Γ output (.lam domain (.app right.lift (.bvar 0))) := by
  exact ⟨_, .rfl, H.trans hΓ (.etaR ht (.refl (.app (ht.weak henv) (.bvar .zero))))⟩

/-- Once normal equality has exposed the constructor argument spines,
projection computation selects the same pair of normally equal fields. -/
theorem NormalEq.fullStep_projIota_spine (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.projections family info)
    (hproj : HasType env univs Γ
      (.proj family index (mkApps (.const info.ctorName levels) args)) fieldType)
    (hargs : List.Forall₂ (NormalEq Γ) args args')
    (hfield : args'[info.nparams + index]? = some field')
    (ht : HasType env univs Γ field' fieldType) :
    ∃ field, FullReduction Γ
      (.proj family index (mkApps (.const info.ctorName levels) args)) field ∧
      NormalEq Γ field field' := by
  obtain ⟨hi', heq⟩ := List.getElem?_eq_some_iff.mp hfield
  have hi : info.nparams + index < args.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hargs]
    exact hi'
  have hnormal := Lean4Lean.List.Forall₂.getElem_of hargs (info.nparams + index) hi hi'
  rw [heq] at hnormal
  have hget : args[info.nparams + index]? = some args[info.nparams + index] := by simp [hi]
  have hleft := ht.defeqU_l henv hΓ (hnormal.defeq hΓ).symm
  exact ⟨_, .tail .rfl (.projIota hl hproj hget hleft), hnormal⟩

omit [Params] in
private theorem mkApps_ne_proj {fn : VExpr}
    (hf : ∀ n i e, fn ≠ .proj n i e) (args : List VExpr) :
    mkApps fn args ≠ .proj family index major := by
  induction args generalizing fn with
  | nil => exact hf _ _ _
  | cons _ _ ih => exact ih (fn := .app _ _) nofun

omit [Params] in
private theorem mkApps_ne_elim {fn : VExpr}
    (hf : ∀ n i levels, fn ≠ .elim n i levels) (args : List VExpr) :
    mkApps fn args ≠ .elim block owner levels := by
  induction args generalizing fn with
  | nil => exact hf _ _ _
  | cons _ _ ih => exact ih (fn := .app _ _) nofun

omit [Params] in
private theorem const_eq_mkApps (h : VExpr.const c ls = VExpr.mkApps (.const name levels) args) :
    c = name ∧ ls = levels ∧ args = [] := by
  have hh := congrArg VExpr.getAppFnArgs h
  rw [InductiveSignature.spine_mkApps_exact _ _ rfl] at hh
  change (VExpr.const c ls, ([] : List VExpr)) = (VExpr.const name levels, args) at hh
  cases hh
  exact ⟨rfl, rfl, rfl⟩

theorem NormalEq.fullStep_delta_levels (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF univs)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels univs) args args') :
    ∃ rhs', FullReduction Γ (VExpr.mkApps (.const name levels') args') rhs' ∧ NormalEq Γ rhs' rhs := by
  obtain ⟨rhs', hh, hr⟩ := H.congr_levels henv hΓ hw' he ha
  obtain ⟨type, hd⟩ := H.defeq henv hΓ
  exact ⟨_, .tail .rfl (.delta hh), (NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hr) hd.hasType.2).symm hΓ⟩

theorem NormalEq.fullStep_quotDelta_levels (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF univs)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels univs) args args') :
    ∃ rhs', FullReduction Γ (VExpr.mkApps (.const ``Quot.lift levels') args') rhs' ∧ NormalEq Γ rhs' rhs := by
  obtain ⟨rhs', hh, hr⟩ := H.congr_levels henv hΓ hw' he ha
  obtain ⟨type, hd⟩ := H.defeq henv hΓ
  exact ⟨_, .tail .rfl (.quotDelta hh), (NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hr) hd.hasType.2).symm hΓ⟩

section NormalParallel

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

omit [Params] in
private theorem eq_nil_or_snoc (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact .inl h
  · exact .inr ⟨L, b, by simpa using h⟩

omit [Params] in
private theorem mkApps_app_isApp (g c : VExpr) (bs : List VExpr) :
    ∃ f a, VExpr.mkApps (.app g c) bs = .app f a := by
  rcases eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, VExpr.mkApps_snoc ..⟩

omit [Params] in
private theorem lift_beta_spine (A e a : VExpr) (bs : List VExpr) :
    VExpr.app (VExpr.mkApps (.app (.lam A e) a) bs).lift (.bvar 0) =
      VExpr.mkApps (.app (.lam A.lift (e.liftN 1 1)) a.lift)
        (bs.map VExpr.lift ++ [.bvar 0]) := by
  rw [VExpr.mkApps_snoc]; simp [VExpr.liftN]

omit [Params] in
private theorem lift_beta_spine_result (e a : VExpr) (bs : List VExpr) :
    VExpr.mkApps ((e.liftN 1 1).inst a.lift) (bs.map VExpr.lift ++ [.bvar 0]) =
      VExpr.app (VExpr.mkApps (e.inst a) bs).lift (.bvar 0) := by
  rw [VExpr.mkApps_snoc, ← lift_inst_hi]; simp

private theorem FullReduction.beta_spine (A e a : VExpr) (bs : List VExpr) :
    FullReduction Γ (VExpr.mkApps (.app (.lam A e) a) bs) (VExpr.mkApps (e.inst a) bs) := by
  refine FullReduction.mkApps (.tail .rfl (.core (.beta .rfl .rfl))) ?_
  induction bs with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .rfl ih

/-- Beta computation through normal equality, by strong induction on the
comparison bound. The first component handles a left side normally equal to
an applied redex spine (eta and extensionality steps add a fresh variable to
the spine); the second handles a function normally equal to a lambda. Eta
expansion of the left side is a `FullStep.funEta` step. -/
private theorem NormalEqN.beta_aux (n : Nat) :
    (∀ {Γ A e a bs x T}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ x (VExpr.mkApps (.app (.lam A e) a) bs) → Γ ⊢ x : T →
      ∃ X, FullReduction Γ x X ∧ NormalEq Γ X (VExpr.mkApps (e.inst a) bs)) ∧
    (∀ {Γ A e f c T}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ f (.lam A e) → Γ ⊢ .app f c : T →
      ∃ X, FullReduction Γ (.app f c) X ∧ NormalEq Γ X (e.inst c)) := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  refine ⟨fun {Γ A e a bs x T} hΓ H hx => ?_, fun {Γ A e f c T} hΓ H hfc => ?_⟩
  · have hRt := hx.defeqU_l henv hΓ (H.defeq hΓ)
    have hred := FullReduction.beta_spine (Γ := Γ) A e a bs
    have hrt := hred.hasType hΓ hRt
    generalize hR : VExpr.mkApps (.app (.lam A e) a) bs = R at H hRt hred
    have ⟨_, _, happ⟩ := mkApps_app_isApp (.lam A e) a bs
    cases H with
    | refl _ => exact ⟨_, hred, .refl hrt⟩
    | proofIrrel l1 l2 l3 => exact ⟨_, .rfl, .proofIrrel l1 l2 (hred.hasType hΓ l3)⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF | etaR =>
      rw [happ] at hR; cases hR
    | appDF l1 l2 l3 l4 l5 l6 =>
      rcases eq_nil_or_snoc bs with rfl | ⟨bs', b, rfl⟩
      · cases hR
        obtain ⟨X, hX, hn⟩ := ((ih _ (by omega)).2 hΓ l5 hx)
        have ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
        have ⟨⟨_, u1⟩, _⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
        have hx2 := u1.symm.defeq l3
        exact ⟨X, hX, hn.trans hΓ (.instN_r (by exact ⟨hΓ, _, d1⟩) hx2 ⟨_, l6⟩ .zero d2)⟩
      · rw [VExpr.mkApps_snoc] at hR; cases hR
        obtain ⟨X, hX, hn⟩ := ((ih _ (by omega)).1 hΓ l5 l1)
        have hX' := hX.hasType hΓ l1
        rw [VExpr.mkApps_snoc]
        exact ⟨_, hX.app .rfl, .appDF hX' ((hn.defeq hΓ).of_l henv hΓ hX').hasType.2 l3 l4
          hn ⟨_, l6⟩⟩
    | etaL l1 l2 =>
      subst hR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      have ⟨_, _, hg⟩ := hx.lam_inv henv hΓ
      rw [lift_beta_spine] at l2
      obtain ⟨Y, hY, hn⟩ := (ih _ (by omega)).1 hΓ' l2 hg
      rw [lift_beta_spine_result] at hn
      exact ⟨_, .lam .rfl hY, .etaL (hred.hasType hΓ l1) hn⟩
    | etaBoth l1 l2 l3 =>
      subst hR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      rw [lift_beta_spine] at l3
      obtain ⟨Y, hY, hn⟩ := (ih _ (by omega)).1 hΓ' l3 ((l1.weakN henv .one).app (.bvar .zero))
      rw [lift_beta_spine_result] at hn
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl hY),
        .etaL (hred.hasType hΓ l2) hn⟩
  · have ⟨_, _, hf, hc⟩ := hfc.app_inv henv hΓ
    have hbeta {A₁ g} : FullStep Γ (.app (.lam A₁ g) c) (g.inst c) := .core (.beta .rfl .rfl)
    generalize hL : VExpr.lam A e = L at H
    cases H with
    | refl _ =>
      subst hL
      exact ⟨_, .tail .rfl hbeta, .refl (hbeta.hasType hΓ hfc)⟩
    | sortDF | constDF | elimDF | projDF | forallEDF | appDF => cases hL
    | lamDF a1 a2 a3 =>
      cases hL
      have ⟨⟨_, H3⟩, _, H4⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((H3.lam H4).uniqU henv hΓ hf).forallE_inv henv hΓ
      exact ⟨_, .tail .rfl hbeta,
        .instN (.defeq (.symm <| .trans_l henv hΓ a1 u1) hc) .zero ⟨_, a3⟩⟩
    | etaL a1 a2 =>
      subst hL
      have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
      have := a2.instN (u1.symm.defeq hc) .zero
      simp [VExpr.inst, inst_lift] at this
      obtain ⟨X, hX, hn⟩ := (ih _ (by omega)).1 (bs := []) hΓ this (hbeta.hasType hΓ hfc)
      exact ⟨X, (ReflTransGen.tail .rfl hbeta).trans hX, hn⟩
    | etaR a1 a2 =>
      cases hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a2.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at this
      exact ⟨_, .rfl, ⟨_, this⟩⟩
    | etaBoth a1 a2 a3 =>
      subst hL
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := a3.instN (.defeq u1 hc) .zero
      simp [VExpr.inst, inst_lift] at this
      exact (ih _ (by omega)).1 (bs := []) hΓ this hfc
    | proofIrrel a1 a2 a3 =>
      subst hL
      have hf' := a2.uniqU henv hΓ hf; have := a1.defeqU_l henv hΓ hf'
      have ⟨⟨_, b1⟩, _, b2⟩ := this.forallE_inv henv
      have := ((b1.forallE b2).uniqU henv hΓ this).sort_inv henv hΓ
      have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
      have b2 := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨⟨_, c1⟩, _, c2⟩ := a3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((c1.lam c2).uniqU henv hΓ a3).trans henv hΓ hf' |>.forallE_inv henv hΓ
      exact ⟨_, .rfl, .proofIrrel (b2.instN henv .zero hc) (hf.app hc)
        ((u2.defeq c2).instN henv .zero (u1.symm.defeq hc))⟩

/-- A function normally equal to a lambda computes, when applied, to the
instantiated lambda body up to normal equality. -/
theorem NormalEq.lam_beta (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ f (.lam A e)) (ht : Γ ⊢ .app f c : T) :
    ∃ X, FullReduction Γ (.app f c) X ∧ NormalEq Γ X (e.inst c) :=
  let ⟨n, H⟩ := H; (NormalEqN.beta_aux n).2 hΓ H ht

end NormalParallel

section SpineExposure

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- Heads that no structural comparison can rewrite: constants and abstract
eliminators. -/
inductive RigidHead : VExpr → Prop where
  | const : RigidHead (.const c ls)
  | elim : RigidHead (.elim block owner ls)

/-- The same rigid head up to equivalent universe levels. -/
inductive HeadEquiv : VExpr → VExpr → Prop where
  | const : List.Forall₂ (· ≈ ·) ls' ls → HeadEquiv (.const c ls') (.const c ls)
  | elim : List.Forall₂ (· ≈ ·) ls' ls → HeadEquiv (.elim block owner ls') (.elim block owner ls)

omit [Params] in
theorem RigidHead.equiv_rfl (h : RigidHead e) : HeadEquiv e e := by
  cases h with
  | const => exact .const (VLevel.forall₂_equiv_refl _)
  | elim => exact .elim (VLevel.forall₂_equiv_refl _)

omit [Params] in
theorem RigidHead.mkApps_eq_app (hh : RigidHead h)
    (H : VExpr.mkApps h targs = .app f a) :
    ∃ targs₀, targs = targs₀ ++ [a] ∧ f = VExpr.mkApps h targs₀ := by
  rcases eq_nil_or_snoc targs with rfl | ⟨targs₀, t, rfl⟩
  · cases hh <;> cases H
  · rw [VExpr.mkApps_snoc] at H; cases H; exact ⟨_, rfl, rfl⟩

omit [Params] in
theorem inst_lift_spine (h : VExpr) (targs : List VExpr) (b : VExpr) :
    (VExpr.app (VExpr.mkApps h targs).lift (.bvar 0)).inst b =
      VExpr.mkApps h (targs ++ [b]) := by
  rw [VExpr.mkApps_snoc]; simp only [VExpr.inst, VExpr.inst_lift]; simp [VExpr.instVar]

theorem NormalEqF.forall₂_refl (H : ∀ a ∈ l, ∃ A, Γ ⊢ a : A) : List.Forall₂ (NormalEqF η Γ) l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    obtain ⟨_, h⟩ := H a (List.mem_cons_self ..)
    exact .cons (.refl h) (ih fun b hb => H b (List.mem_cons_of_mem _ hb))

alias NormalEq.forall₂_refl := NormalEqF.forall₂_refl

theorem NormalEqF.forall₂_trans (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : List.Forall₂ (NormalEqF η Γ) l₁ l₂) (H2 : List.Forall₂ (NormalEqF η Γ) l₂ l₃) :
    List.Forall₂ (NormalEqF η Γ) l₁ l₃ :=
  Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans hΓ h') H1 H2

alias NormalEq.forall₂_trans := NormalEqF.forall₂_trans

theorem NormalEqF.forall₂_typed_right (hΓ : OnCtx Γ (env.IsType univs))
    (H : List.Forall₂ (NormalEqF η Γ) l₁ l₂) : ∀ a ∈ l₂, ∃ A, Γ ⊢ a : A := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨_, h⟩ := h.defeq hΓ; exact ⟨_, h.hasType.2⟩
    · exact ih a ha

alias NormalEq.forall₂_typed_right := NormalEqF.forall₂_typed_right

/-- An application spine headed by a proof is a proof. -/
theorem HasType.mkApps_proof (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Γ ⊢ P : .sort .zero) (hx : Γ ⊢ x : P) (ht : Γ ⊢ VExpr.mkApps x bs : T) :
    Γ ⊢ T : .sort .zero := by
  induction bs generalizing x P with
  | nil => exact hp.defeqU_l henv hΓ (hx.uniqU henv hΓ ht)
  | cons b bs ih =>
    obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app x b) ht
    obtain ⟨_, _, hf, hb⟩ := happ.app_inv henv hΓ
    have hP := hx.uniqU henv hΓ hf
    have hpi := hp.defeqU_l henv hΓ hP
    have ⟨⟨_, b1⟩, _, b2⟩ := hpi.forallE_inv henv
    have hz := ((b1.forallE b2).uniqU henv hΓ hpi).sort_inv henv hΓ
    have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
    have b2' := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 hz)) b2
    exact ih (b2'.instN henv .zero hb) (hf.app hb) ht

/-- Spine exposure. A term normally equal to a rigid-headed spine, applied
to arguments normally equal to further spine arguments, either is a proof,
reduces to a spine with an equivalent head and normally equal arguments, or
reduces to a lambda whose body is a bounded comparison with the eta
expansion of such a spine. -/
theorem NormalEqN.spine_expose (hΓ : OnCtx Γ (env.IsType univs)) (hh : RigidHead h) :
    ∀ n {x targs bs bs' T}, NormalEqN true n Γ x (VExpr.mkApps h targs) →
      List.Forall₂ (NormalEq Γ) bs bs' → Γ ⊢ VExpr.mkApps x bs : T →
      (Γ ⊢ T : .sort .zero) ∨
      (∃ h' targs', HeadEquiv h' h ∧ FullReduction Γ (VExpr.mkApps x bs) (VExpr.mkApps h' targs') ∧
        List.Forall₂ (NormalEq Γ) targs' (targs ++ bs')) ∨
      (∃ A g m targs₁ B, m < n ∧ FullReduction Γ (VExpr.mkApps x bs) (.lam A g) ∧
        NormalEqN true m (A :: Γ) g (.app (VExpr.mkApps h targs₁).lift (.bvar 0)) ∧
        List.Forall₂ (NormalEq Γ) targs₁ (targs ++ bs') ∧
        Γ ⊢ VExpr.mkApps h targs₁ : .forallE A B) := by
  intro n
  induction n using Nat.strongRecOn with | _ n ih => ?_
  intro x targs bs bs' T H hbs ht
  have hbs' := NormalEq.forall₂_typed_right hΓ hbs
  have htargsTyped : ∀ a ∈ targs, ∃ A, Γ ⊢ a : A := by
    obtain ⟨_, hd⟩ := H.defeq hΓ
    exact fun a ha => schema_mkApps_arg_type hΓ hd.hasType.2 ha
  have hrefl := NormalEqF.forall₂_refl (η := true) htargsTyped
  generalize hR : VExpr.mkApps h targs = R at H
  cases H with
  | refl _ =>
    subst hR
    refine .inr (.inl ⟨h, targs ++ bs, hh.equiv_rfl, ?_, List.Forall₂.append' hrefl hbs⟩)
    rw [VExpr.mkApps_append]; exact .rfl
  | proofIrrel l1 l2 _ => exact .inl (HasType.mkApps_proof hΓ l1 l2 ht)
  | constDF _ _ _ _ l5 =>
    cases hh with
    | elim => rcases eq_nil_or_snoc targs with rfl | ⟨_, _, rfl⟩ <;>
        [cases hR; (rw [VExpr.mkApps_snoc] at hR; cases hR)]
    | const =>
      rcases eq_nil_or_snoc targs with rfl | ⟨_, _, rfl⟩
      · cases hR
        exact .inr (.inl ⟨_, bs, .const l5, .rfl, hbs⟩)
      · rw [VExpr.mkApps_snoc] at hR; cases hR
  | elimDF _ l2 =>
    cases hh with
    | const => rcases eq_nil_or_snoc targs with rfl | ⟨_, _, rfl⟩ <;>
        [cases hR; (rw [VExpr.mkApps_snoc] at hR; cases hR)]
    | elim =>
      rcases eq_nil_or_snoc targs with rfl | ⟨_, _, rfl⟩
      · cases hR
        exact .inr (.inl ⟨_, bs, .elim l2, .rfl, hbs⟩)
      · rw [VExpr.mkApps_snoc] at hR; cases hR
  | appDF l1 l2 l3 l4 l5 l6 =>
    obtain ⟨targs₀, rfl, rfl⟩ := hh.mkApps_eq_app hR
    rcases ih _ (by omega) l5 (.cons ⟨_, l6⟩ hbs) ht with hp | ⟨h', targs', he, hr, hn⟩ |
        ⟨A, g, m, targs₁, B, hm, hr, hg, hn, hty⟩
    · exact .inl hp
    · exact .inr (.inl ⟨h', targs', he, hr, by simpa using hn⟩)
    · exact .inr (.inr ⟨A, g, m, targs₁, B, by omega, hr, hg, by simpa using hn, hty⟩)
  | @etaL _ _ A0 _ _ g l1 l2 =>
    subst hR
    cases hbs with
    | nil => exact .inr (.inr ⟨_, _, _, targs, _, by omega, .rfl, l2,
        by simpa using hrefl, l1⟩)
    | @cons b b' bs₀ bs₀' hb hbs₀ =>
      have hstep := FullReduction.beta_spine (Γ := Γ) A0 g b bs₀
      have ht' := hstep.hasType hΓ ht
      obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app (.lam A0 g) b) ht
      obtain ⟨_, _, hf, hbt⟩ := happ.app_inv henv hΓ
      have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
      have hb' := l2.instN (u1.symm.defeq hbt) .zero
      rw [inst_lift_spine] at hb'
      have hbs₁ : List.Forall₂ (NormalEq Γ) bs₀' bs₀' :=
        NormalEqF.forall₂_refl (η := true) fun a ha => hbs' a (List.mem_cons_of_mem _ ha)
      have hfix : List.Forall₂ (NormalEq Γ) ((targs ++ [b]) ++ bs₀') (targs ++ b' :: bs₀') := by
        rw [List.append_assoc, List.singleton_append]
        exact List.Forall₂.append' hrefl (.cons hb hbs₁)
      rcases ih _ (by omega) hb' hbs₀ ht' with hp | ⟨h', targs', he, hr, hn⟩ |
          ⟨A, g, m, targs₁, B, hm, hr, hg, hn, hty⟩
      · exact .inl hp
      · exact .inr (.inl ⟨h', targs', he, hstep.trans hr, NormalEq.forall₂_trans hΓ hn hfix⟩)
      · exact .inr (.inr ⟨A, g, m, targs₁, B, by omega, hstep.trans hr, hg,
          NormalEq.forall₂_trans hΓ hn hfix, hty⟩)
  | etaBoth l1 l2 l3 =>
    subst hR
    cases hbs with
    | nil => exact .inr (.inr ⟨_, _, _, targs, _, by omega, .tail .rfl (.funEta l1), l3,
        by simpa using hrefl, l2⟩)
    | @cons b b' bs₀ bs₀' hb hbs₀ =>
      obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app _ b) ht
      obtain ⟨_, _, hf, hbt⟩ := happ.app_inv henv hΓ
      have ⟨⟨_, u1⟩, _⟩ := (hf.uniqU henv hΓ l1).forallE_inv henv hΓ
      have hb' := l3.instN (u1.defeq hbt) .zero
      simp only [VExpr.inst, VExpr.inst_lift] at hb'
      simp only [VExpr.instVar, Nat.lt_irrefl, if_false, VExpr.liftN_zero] at hb'
      rw [← VExpr.mkApps_snoc] at hb'
      have hbs₁ : List.Forall₂ (NormalEq Γ) bs₀' bs₀' :=
        NormalEqF.forall₂_refl (η := true) fun a ha => hbs' a (List.mem_cons_of_mem _ ha)
      have hfix : List.Forall₂ (NormalEq Γ) ((targs ++ [b]) ++ bs₀') (targs ++ b' :: bs₀') := by
        rw [List.append_assoc, List.singleton_append]
        exact List.Forall₂.append' hrefl (.cons hb hbs₁)
      rcases ih _ (by omega) hb' hbs₀ ht with hp | ⟨h', targs', he, hr, hn⟩ |
          ⟨A, g, m, targs₁, B, hm, hr, hg, hn, hty⟩
      · exact .inl hp
      · exact .inr (.inl ⟨h', targs', he, hr, NormalEq.forall₂_trans hΓ hn hfix⟩)
      · exact .inr (.inr ⟨A, g, m, targs₁, B, by omega, hr, hg,
          NormalEq.forall₂_trans hΓ hn hfix, hty⟩)
  | sortDF => exact absurd hR (VExpr.mkApps_ne_sort (by cases hh <;> nofun) _)
  | lamDF => exact absurd hR (VExpr.mkApps_ne_lam (by cases hh <;> nofun) _)
  | etaR => exact absurd hR (VExpr.mkApps_ne_lam (by cases hh <;> nofun) _)
  | forallEDF => exact absurd hR (VExpr.mkApps_ne_forallE (by cases hh <;> nofun) _)
  | projDF => exact absurd hR (mkApps_ne_proj (by cases hh <;> nofun) _)

end SpineExposure

section SpineTransport

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

theorem ParRed.weak' (W : Ctx.Lift' ρ Γ Γ') (H : ParRed Γ e e') :
    ParRed Γ' (e.lift' ρ) (e'.lift' ρ) := by
  generalize hd : ρ.depth = d
  induction d generalizing ρ Γ' with
  | zero =>
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd, VExpr.lift'_depth_zero hd]; exact H
  | succ d ih =>
    obtain ⟨l, k, hl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨_, W1, W2⟩ := W.of_cons_skip
    have key (y : VExpr) : y.lift' (.consN (.skip l) k) = (y.lift' (.consN l k)).liftN 1 k := by
      rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← VExpr.lift'_consN_skipN]; rfl
    rw [key, key]
    exact (ih W1 (by simp [hl])).weakN W2

omit [Params] in
theorem lift_lift'_skip (y : VExpr) (ρ : Lift) : (y.lift' ρ).lift = y.lift' (.skip ρ) := by
  rw [VExpr.lift_eq_lift', ← VExpr.lift'_comp]; rfl

omit [Params] in
theorem lift_mkApps_lift' (y : VExpr) (ρ : Lift) (bs : List VExpr) :
    VExpr.app (VExpr.mkApps (y.lift' ρ) bs).lift (.bvar 0) =
      VExpr.mkApps (y.lift' (.skip ρ)) (bs.map VExpr.lift ++ [.bvar 0]) := by
  rw [VExpr.mkApps_snoc]; congr 1
  show VExpr.liftN 1 (VExpr.mkApps _ _) 0 = _
  rw [VExpr.liftN_mkApps]; congr 1; exact lift_lift'_skip ..

/-- Transport of normal equality along one fixed parallel step `e ≫ e'`, at
every renaming of its context and below every extra argument spine, for
comparison derivations of bound `n`. Eta comparisons extend the spine by a
fresh variable under a renaming, which is why both are quantified. -/
def SpineTransport (Γ : List VExpr) (e e' : VExpr) (n : Nat) : Prop :=
  ∀ {ρ Γ' bs x}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
    NormalEqN true n Γ' x (VExpr.mkApps (e.lift' ρ) bs) →
    ∃ X, FullReduction Γ' x X ∧ NormalEq Γ' X (VExpr.mkApps (e'.lift' ρ) bs)

private theorem forall₂_rfl_full : ∀ (bs : List VExpr), List.Forall₂ (FullReduction Γ) bs bs
  | [] => .nil
  | _ :: bs => .cons .rfl (forall₂_rfl_full bs)

theorem SpineTransport.same : SpineTransport Γ e e n :=
  fun _ _ H => ⟨_, .rfl, ⟨_, H⟩⟩

theorem SpineTransport.red (hstep : ParRed Γ e e') (W : Ctx.Lift' ρ Γ Γ') (bs : List VExpr) :
    FullReduction Γ' (VExpr.mkApps (e.lift' ρ) bs) (VExpr.mkApps (e'.lift' ρ) bs) :=
  FullReduction.mkApps (.tail .rfl (.core (hstep.weak' W))) (forall₂_rfl_full bs)

theorem SpineTransport.refl_case (hΓ : OnCtx Γ' (env.IsType univs))
    (hstep : ParRed Γ e e') (W : Ctx.Lift' ρ Γ Γ')
    (h : Γ' ⊢ VExpr.mkApps (e.lift' ρ) bs : A) :
    ∃ X, FullReduction Γ' (VExpr.mkApps (e.lift' ρ) bs) X ∧
      NormalEq Γ' X (VExpr.mkApps (e'.lift' ρ) bs) :=
  have hR := SpineTransport.red hstep W bs
  ⟨_, hR, .refl (hR.hasType hΓ h)⟩

theorem SpineTransport.proofIrrel_case (hΓ : OnCtx Γ' (env.IsType univs))
    (hstep : ParRed Γ e e') (W : Ctx.Lift' ρ Γ Γ')
    (l1 : Γ' ⊢ p : .sort .zero) (l2 : Γ' ⊢ x : p)
    (l3 : Γ' ⊢ VExpr.mkApps (e.lift' ρ) bs : p) :
    ∃ X, FullReduction Γ' x X ∧ NormalEq Γ' X (VExpr.mkApps (e'.lift' ρ) bs) :=
  ⟨_, .rfl, .proofIrrel l1 l2 ((SpineTransport.red hstep W bs).hasType hΓ l3)⟩

theorem SpineTransport.etaL_case (hΓ : OnCtx Γ' (env.IsType univs))
    (hstep : ParRed Γ e e') (W : Ctx.Lift' ρ Γ Γ') (ih : SpineTransport Γ e e' m)
    (l1 : Γ' ⊢ VExpr.mkApps (e.lift' ρ) bs : .forallE A B)
    (l2 : NormalEqN true m (A :: Γ') g (.app (VExpr.mkApps (e.lift' ρ) bs).lift (.bvar 0))) :
    ∃ X, FullReduction Γ' (.lam A g) X ∧ NormalEq Γ' X (VExpr.mkApps (e'.lift' ρ) bs) := by
  have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
  rw [lift_mkApps_lift'] at l2
  obtain ⟨Y, hY, hn⟩ := ih (by exact ⟨hΓ, _, hA⟩) W.skip l2
  rw [← lift_mkApps_lift'] at hn
  exact ⟨_, .lam .rfl hY, .etaL ((SpineTransport.red hstep W bs).hasType hΓ l1) hn⟩

theorem SpineTransport.etaBoth_case (hΓ : OnCtx Γ' (env.IsType univs))
    (hstep : ParRed Γ e e') (W : Ctx.Lift' ρ Γ Γ') (ih : SpineTransport Γ e e' m)
    (l1 : Γ' ⊢ x : .forallE A B) (l2 : Γ' ⊢ VExpr.mkApps (e.lift' ρ) bs : .forallE A B)
    (l3 : NormalEqN true m (A :: Γ') (.app x.lift (.bvar 0))
      (.app (VExpr.mkApps (e.lift' ρ) bs).lift (.bvar 0))) :
    ∃ X, FullReduction Γ' x X ∧ NormalEq Γ' X (VExpr.mkApps (e'.lift' ρ) bs) := by
  have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
  rw [lift_mkApps_lift'] at l3
  obtain ⟨Y, hY, hn⟩ := ih (by exact ⟨hΓ, _, hA⟩) W.skip l3
  rw [← lift_mkApps_lift'] at hn
  exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl hY),
    .etaL ((SpineTransport.red hstep W bs).hasType hΓ l2) hn⟩

/-- Strong induction on the comparison bound. Nonempty spines, eta and proof
irrelevance are handled uniformly; `hbase` treats the bare step. -/
theorem SpineTransport.induct (hstep : ParRed Γ e e')
    (hbase : ∀ n, (∀ m < n, SpineTransport Γ e e' m) →
      ∀ {ρ Γ' x}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      NormalEqN true n Γ' x (e.lift' ρ) →
      ∃ X, FullReduction Γ' x X ∧ NormalEq Γ' X (e'.lift' ρ)) :
    ∀ n, SpineTransport Γ e e' n := by
  intro n
  induction n using Nat.strongRecOn with | _ n ih => ?_
  intro ρ Γ' bs x hΓ W H
  rcases eq_nil_or_snoc bs with rfl | ⟨bs, b, rfl⟩
  · exact hbase n ih hΓ W H
  have hR := SpineTransport.red hstep W (bs ++ [b])
  generalize hRR : VExpr.mkApps (e.lift' ρ) (bs ++ [b]) = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case hΓ hstep W h
  | proofIrrel l1 l2 l3 => subst hRR; exact SpineTransport.proofIrrel_case hΓ hstep W l1 l2 l3
  | etaL l1 l2 => subst hRR; exact SpineTransport.etaL_case hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR; exact SpineTransport.etaBoth_case hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | appDF l1 l2 l3 l4 l5 l6 =>
    rw [VExpr.mkApps_snoc] at hRR; cases hRR
    obtain ⟨X, hX, hn⟩ := ih _ (by omega) hΓ W l5
    have hX' := hX.hasType hΓ l1
    rw [VExpr.mkApps_snoc]
    exact ⟨_, hX.app .rfl, .appDF hX' ((hn.defeq hΓ).of_l henv hΓ hX').hasType.2 l3 l4
      hn ⟨_, l6⟩⟩
  | sortDF | constDF | elimDF | projDF | lamDF | forallEDF | etaR =>
    rw [VExpr.mkApps_snoc] at hRR; cases hRR

theorem SpineTransport.app (hf : ParRed Γ f f') (ha : ParRed Γ a a')
    (ihf : ∀ n, SpineTransport Γ f f' n) (iha : ∀ n, SpineTransport Γ a a' n) :
    ∀ n, SpineTransport Γ (.app f a) (.app f' a') n := by
  refine SpineTransport.induct (.app hf ha) fun n ih ρ Γ' x hΓ W H => ?_
  have hstep : ParRed Γ (.app f a) (.app f' a') := .app hf ha
  generalize hRR : (VExpr.app f a).lift' ρ = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case (bs := []) hΓ hstep W h
  | proofIrrel l1 l2 l3 =>
    subst hRR; exact SpineTransport.proofIrrel_case (bs := []) hΓ hstep W l1 l2 l3
  | etaL l1 l2 =>
    subst hRR; exact SpineTransport.etaL_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR
    exact SpineTransport.etaBoth_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | appDF l1 l2 l3 l4 l5 l6 =>
    cases hRR
    obtain ⟨X1, a1, a2⟩ := ihf _ (bs := []) hΓ W l5
    obtain ⟨X2, b1, b2⟩ := iha _ (bs := []) hΓ W l6
    have r1 := (hf.weak' W).hasType hΓ l2
    have r2 := (ha.weak' W).hasType hΓ l4
    exact ⟨_, .app a1 b1,
      .appDF (a1.hasType hΓ l1) r1 (b1.hasType hΓ l3) r2 a2 b2⟩
  | sortDF | constDF | elimDF | projDF | lamDF | forallEDF | etaR => cases hRR

theorem SpineTransport.proj (hm : ParRed Γ major major')
    (ihm : ∀ n, SpineTransport Γ major major' n) :
    ∀ n, SpineTransport Γ (.proj family index major) (.proj family index major') n := by
  refine SpineTransport.induct (.proj hm) fun n ih ρ Γ' x hΓ W H => ?_
  have hstep : ParRed Γ (.proj family index major) (.proj family index major') := .proj hm
  generalize hRR : (VExpr.proj family index major).lift' ρ = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case (bs := []) hΓ hstep W h
  | proofIrrel l1 l2 l3 =>
    subst hRR; exact SpineTransport.proofIrrel_case (bs := []) hΓ hstep W l1 l2 l3
  | etaL l1 l2 =>
    subst hRR; exact SpineTransport.etaL_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR
    exact SpineTransport.etaBoth_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | projDF lproj l2 =>
    cases hRR
    obtain ⟨_, majorRed, majorNormal⟩ := ihm _ (bs := []) hΓ W l2
    exact ⟨_, majorRed.proj, .projDF (majorRed.proj.hasType hΓ lproj) majorNormal⟩
  | sortDF | constDF | elimDF | appDF | lamDF | forallEDF | etaR => cases hRR

theorem SpineTransport.lam (hA : ParRed Γ A A') (hb : ParRed (A :: Γ) b b')
    (ihb : ∀ n, SpineTransport (A :: Γ) b b' n) :
    ∀ n, SpineTransport Γ (.lam A b) (.lam A' b') n := by
  refine SpineTransport.induct (.lam hA hb) fun n ih ρ Γ' x hΓ W H => ?_
  have hstep : ParRed Γ (.lam A b) (.lam A' b') := .lam hA hb
  generalize hRR : (VExpr.lam A b).lift' ρ = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case (bs := []) hΓ hstep W h
  | proofIrrel l1 l2 l3 =>
    subst hRR; exact SpineTransport.proofIrrel_case (bs := []) hΓ hstep W l1 l2 l3
  | etaL l1 l2 =>
    subst hRR; exact SpineTransport.etaL_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR
    exact SpineTransport.etaBoth_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | lamDF l1 l2 l3 =>
    cases hRR
    have hΓ' : OnCtx (A.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ, _, l2.hasType.2⟩
    have l3' := l3.defeqDFC hΓ (.succ .zero l2)
    obtain ⟨Y, hY, hn⟩ := ihb _ (bs := []) hΓ' W.cons l3'
    have ⟨_, hg⟩ := l3'.defeq hΓ'
    have hAA := (hA.weak' W).defeq hΓ l2.hasType.2
    exact ⟨_, .lam .rfl (hY.defeqDFC hΓ (.succ .zero (l2.symm.trans l1)) hg.hasType.1),
      .lamDF l1 (l2.trans hAA) (hn.defeqDFC hΓ (.succ .zero l2.symm))⟩
  | etaR l1 l2 =>
    cases hRR
    have ⟨⟨_, hA'⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    obtain ⟨Y, hY, hn⟩ := ihb _ (bs := []) (by exact ⟨hΓ, _, hA'⟩) W.cons l2
    exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl hY),
      .lamDF hA' ((hA.weak' W).defeq hΓ hA') hn⟩
  | sortDF | constDF | elimDF | appDF | projDF | forallEDF => cases hRR

theorem SpineTransport.forallE (hA : ParRed Γ A A') (hB : ParRed (A :: Γ) B B')
    (ihA : ∀ n, SpineTransport Γ A A' n) (ihB : ∀ n, SpineTransport (A :: Γ) B B' n) :
    ∀ n, SpineTransport Γ (.forallE A B) (.forallE A' B') n := by
  refine SpineTransport.induct (.forallE hA hB) fun n ih ρ Γ' x hΓ W H => ?_
  have hstep : ParRed Γ (.forallE A B) (.forallE A' B') := .forallE hA hB
  generalize hRR : (VExpr.forallE A B).lift' ρ = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case (bs := []) hΓ hstep W h
  | proofIrrel l1 l2 l3 =>
    subst hRR; exact SpineTransport.proofIrrel_case (bs := []) hΓ hstep W l1 l2 l3
  | etaL l1 l2 =>
    subst hRR; exact SpineTransport.etaL_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR
    exact SpineTransport.etaBoth_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | forallEDF l1 l2 l3 l4 =>
    cases hRR
    obtain ⟨_, a1, a2⟩ := ihA _ (bs := []) hΓ W l2
    have hΓ' : OnCtx (_ :: Γ') (env.IsType univs) := ⟨hΓ, _, l1.hasType.1⟩
    have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ')
    have W' := l1.transU_l henv hΓ (l2.defeq hΓ)
    have hΓ'' : OnCtx (A.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ, _, W'.hasType.2⟩
    have l4' := l4.defeqDFC hΓ (.succ .zero W')
    obtain ⟨_, b1, b2⟩ := ihB _ (bs := []) hΓ'' W.cons l4'
    have hAA := (hA.weak' W).defeq hΓ W'.hasType.2
    have l3'' := l3.defeqDFC henv (.succ .zero W')
    have hB1 := (b1.hasType hΓ'' l3'').defeqDFC henv (.succ .zero W'.symm)
    have b1' := b1.defeqDFC hΓ (.succ .zero (W'.symm.trans l1)) l3''
    have b2' := b2.defeqDFC hΓ (.succ .zero W'.symm)
    exact ⟨_, .forallE a1 b1',
      .forallEDF (.transU_l henv hΓ (W'.trans hAA) (a2.defeq hΓ).symm) a2 hB1 b2'⟩
  | sortDF | constDF | elimDF | appDF | projDF | lamDF | etaR => cases hRR

theorem SpineTransport.beta (hb : ParRed (A :: Γ) b b') (ha : ParRed Γ a a')
    (ihb : ∀ n, SpineTransport (A :: Γ) b b' n) (iha : ∀ n, SpineTransport Γ a a' n) :
    ∀ n, SpineTransport Γ (.app (.lam A b) a) (b'.inst a') n := by
  have hstep : ParRed Γ (.app (.lam A b) a) (b'.inst a') := .beta hb ha
  have ihl := SpineTransport.lam (A := A) .rfl hb ihb
  refine SpineTransport.induct hstep fun n ih ρ Γ' x hΓ W H => ?_
  generalize hRR : (VExpr.app (.lam A b) a).lift' ρ = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case (bs := []) hΓ hstep W h
  | proofIrrel l1 l2 l3 =>
    subst hRR; exact SpineTransport.proofIrrel_case (bs := []) hΓ hstep W l1 l2 l3
  | etaL l1 l2 =>
    subst hRR; exact SpineTransport.etaL_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR
    exact SpineTransport.etaBoth_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | appDF l1 l2 l3 l4 l5 l6 =>
    cases hRR
    obtain ⟨f', a1, a2⟩ := ihl _ (bs := []) hΓ W l5
    obtain ⟨a'', b1, b2⟩ := iha _ (bs := []) hΓ W l6
    let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
    let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
    have hΓ' : OnCtx (A.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ, _, d1⟩
    have d2' := (hb.weak' W.cons).hasType hΓ' d2
    have l3' := b1.hasType hΓ (u1.symm.defeq l3)
    obtain ⟨_, h1, h2⟩ := NormalEq.lam_beta hΓ a2
      (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2')) l3')
    refine ⟨_, (a1.app b1).trans h1, h2.trans hΓ ?_⟩
    rw [VExpr.lift'_inst_hi]
    exact .instN_r hΓ' l3' b2 .zero d2'
  | sortDF | constDF | elimDF | projDF | lamDF | forallEDF | etaR => cases hRR

end SpineTransport

section CaseRedexMajor

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

omit [Params] in
/-- The constructor major of a matched generated case redex is never a
function: its type is an application of the registered family head, which is
rigid. -/
theorem CaseRedex.major_not_pi {E : VEnv} {U : Nat} (hE : E.WF)
    (hΓ : OnCtx Γ (E.IsType U)) (H : CaseRedex E U Γ rule actual) :
    ¬ E.HasType U Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
      actual.ctorArguments) (.forallE A B) := by
  intro hpi
  have hsource := H.source
  generalize hpacked : actual.levels = packed at hsource
  cases hsource with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ := hE.eliminator_installed hl
    have harity := hcert.arguments_length hg
    obtain ⟨hb, ho⟩ := hg.owned
    have hab : actual.block = block := H.block_eq.trans hb
    have hao : actual.owner = owner.val := H.owner_eq.trans ho
    have ht : VExpr.WF E U Γ (VExpr.mkApps
        (.elim block owner.val (target :: levels))
        (actual.arguments ++ [VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
          actual.ctorArguments])) := by
      obtain ⟨type, hguard⟩ := H.guard
      refine ⟨type, ?_⟩
      simpa only [HasType, InductiveSignature.CaseSchema.Application.expr, VExpr.mkApps,
        List.foldl_append, List.foldl_cons, List.foldl_nil, hab, hao, hpacked] using
        hguard.hasType.1
    obtain ⟨familyArgs, hmajor⟩ := HasType.caseMajor_type hE hΓ hl
      (H.arguments_length.trans harity) ht
    have hrigid := hE.case_family_head_rigid hl hg
    have ⟨_, hsort⟩ := hmajor.isType hE.ordered hΓ
    exact IsDefEqU.rigidApp_forallE_inv hE hΓ hrigid hsort (hmajor.uniqU hE hΓ hpi)

/-- The major of a matched recursor iota redex is never a function. -/
theorem Params.major_not_pi (hΓ : OnCtx Γ (env.IsType univs)) (hp : Pat p r)
    (hm : p.Matches (.app F M) m1 m2) (ht : HasType env univs Γ (.app F M) T) :
    ¬ HasType env univs Γ M (.forallE A B) := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hp
  cases sp with
  | defn c => cases hm
  | iota rc mr cc kc =>
    obtain ⟨F', M', lsc, g1, g2, hF, hM, hFe, hMe⟩ :
        ∃ F' M' lsc g1 g2, ((Pattern.const rc).varN mr).Matches F' m1 g1 ∧
          ((Pattern.const cc).varN kc).Matches M' lsc g2 ∧ F = F' ∧ M = M' := by
      cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
    subst hFe hMe
    have hFeq := hF.const_arguments
    have hMeq := hM.const_arguments
    rcases Params.pat_recursor hp with
      ⟨data, hreg, hname, hoff, _, ⟨index, hown⟩, _⟩ |
      ⟨hr, rfl, rfl, rfl, rfl, _⟩
    · subst hname
      rw [hFeq] at ht
      exact RecursorRegistered.major_not_pi henv hΓ hreg index hown ht
        (by simp [Pattern.argumentRHS_length, hoff])
    · intro hpi
      rw [hFeq] at ht
      generalize hxs : List.map _ _ = xs at ht
      have hxl : xs.length = 5 := by rw [← hxs]; simp [Pattern.argumentRHS_length]
      match xs, hxl with
      | [a, b, c, d, e], _ =>
      have hWF : VExpr.WF env univs Γ
          (VExpr.mkApps (.const ``Quot.lift m1) [a, b, c, d, e, M]) := ⟨_, ht⟩
      obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ hWF
      obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hc
      rw [hr.lift] at hci
      cases hci
      change m1.length = 2 at hl
      obtain ⟨u, v, rfl⟩ : ∃ u v, m1 = [u, v] := by
        rcases m1 with _ | ⟨u, _ | ⟨v, _ | _⟩⟩ <;> simp_all
      have hM := QuotRegistered.major_type henv hΓ hr (hw u (by simp)) (hw v (by simp)) hWF
      have ⟨_, hsort⟩ := hM.isType henv.ordered hΓ
      exact IsDefEqU.rigidApp_forallE_inv henv hΓ (hr.quot_rigid henv) hsort
        (hM.uniqU henv hΓ hpi)

/-- A matched recursor iota redex with a proof major is itself a proof: small
eliminators target Prop, and large ones carry a nonzero source-level check
that excludes proof majors. -/
theorem Params.major_proof (hΓ : OnCtx Γ (env.IsType univs)) (hp : Pat p r)
    (hm : p.Matches (.app F M) m1 m2) (hc : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (ht : HasType env univs Γ (.app F M) T)
    (hM : HasType env univs Γ M P) (hP : HasType env univs Γ P (.sort .zero)) :
    HasType env univs Γ T (.sort .zero) := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hp
  cases sp with
  | defn c => cases hm
  | iota rc mr cc kc =>
    obtain ⟨F', M', lsc, g1, g2, hF, hM', hFe, hMe⟩ :
        ∃ F' M' lsc g1 g2, ((Pattern.const rc).varN mr).Matches F' m1 g1 ∧
          ((Pattern.const cc).varN kc).Matches M' lsc g2 ∧ F = F' ∧ M = M' := by
      cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
    subst hFe hMe
    have hFeq := hF.const_arguments
    rcases Params.pat_recursor hp with
      ⟨data, hreg, hname, hoff, _, _, hlarge⟩ |
      ⟨hr, rfl, rfl, rfl, rfl, rest, hrest⟩
    · subst hname
      rw [hFeq] at ht
      have hvl : ((Pattern.const data.name).argumentRHS mr).length = data.majorOffset := by
        simp [Pattern.argumentRHS_length, hoff]
      cases hlt : data.largeTarget with
      | true =>
        obtain ⟨rest, hrest⟩ := hlarge hlt
        rw [hrest] at hc
        exact (RecursorRegistered.major_not_proof henv hΓ hreg ht
          (by simpa using hvl) hc.1 hM hP).elim
      | false =>
        have hsmall := hreg.small_target hlt
        generalize hxs : List.map _ _ = xs at ht
        have hxl : xs.length = data.majorOffset := by rw [← hxs]; simpa using hvl
        have happ : HasType env univs Γ (VExpr.mkApps (.const data.name m1) (xs ++ [M])) T := by
          simpa [VExpr.mkApps, List.foldl_append] using ht
        obtain ⟨T', hT', hsort⟩ := hreg.result_sort henv hΓ happ (by simp [hxl])
        have hz : data.target.inst m1 ≈ .zero := VLevel.inst_congr_l hsmall
        have hwf := let ⟨_, h⟩ := hsort.isType henv.ordered hΓ; h.sort_inv henv.ordered
        have hT'0 : HasType env univs Γ T' (.sort .zero) :=
          IsDefEq.defeqDF (.sortDF hwf (by trivial) hz) hsort
        exact hT'0.defeqU_l henv hΓ (hT'.uniqU henv hΓ happ)
    · exfalso
      rw [hrest] at hc
      rw [hFeq] at ht
      generalize hxs : List.map _ _ = xs at ht
      have hxl : xs.length = 5 := by rw [← hxs]; simp [Pattern.argumentRHS_length]
      match xs, hxl with
      | [a, b, c, d, e], _ =>
      have hWF : VExpr.WF env univs Γ
          (VExpr.mkApps (.const ``Quot.lift m1) [a, b, c, d, e, M]) := ⟨_, ht⟩
      obtain ⟨_, hcst⟩ := VExpr.WF.of_mkApps henv.ordered hΓ hWF
      obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hcst
      rw [hr.lift] at hci
      cases hci
      change m1.length = 2 at hl
      obtain ⟨u, v, rfl⟩ : ∃ u v, m1 = [u, v] := by
        rcases m1 with _ | ⟨u, _ | ⟨v, _ | _⟩⟩ <;> simp_all
      have hu : u.WF univs := hw u (by simp)
      have hMt := QuotRegistered.major_type henv hΓ hr hu (hw v (by simp)) hWF
      have hQ : HasType env univs Γ (.const ``Quot [u])
          (VExpr.wrapForalls [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))]
            (.sort u)) := HasType.const hr.quotient (by simpa using hu) rfl
      have ⟨_, hTs⟩ := hMt.isType henv.ordered hΓ
      have hsortT := (HasType.mkApps_wrapForalls henv hΓ hQ ⟨_, hTs⟩ rfl).2
      rw [VExpr.instOuter_sort] at hsortT
      have hP' := hP.defeqU_l henv hΓ (hM.uniqU henv hΓ hMt)
      have hzero := (hsortT.uniqU henv hΓ hP').sort_inv henv hΓ
      exact hc.1 hzero

omit [Params] in
/-- Transport a constant-spine match along a pointwise relation of arguments,
at arbitrary head levels. -/
theorem _root_.Lean4Lean.Pattern.Matches.constVarN_transport {R : VExpr → VExpr → Prop} :
    ∀ (k : Nat) {vs vs' : List VExpr} {ls ls' : List VLevel} {m2},
    ((Pattern.const c).varN k).Matches (VExpr.mkApps (.const c ls) vs) ls m2 →
    List.Forall₂ R vs' vs →
    ∃ m3, ((Pattern.const c).varN k).Matches (VExpr.mkApps (.const c ls') vs') ls' m3 ∧
      ∀ a, R (m3 a) (m2 a)
  | 0, vs, vs', ls, ls', m2, H, hR => by
    generalize hE : VExpr.mkApps (.const c ls) vs = E at H
    cases H
    rcases eq_nil_or_snoc vs with rfl | ⟨_, _, rfl⟩
    · cases hR; exact ⟨_, .const, nofun⟩
    · rw [VExpr.mkApps_snoc] at hE; cases hE
  | k + 1, vs, vs', ls, ls', m2, H, hR => by
    generalize hE : VExpr.mkApps (.const c ls) vs = E at H
    cases H with
    | var H' =>
      obtain ⟨vs₀, rfl, rfl⟩ := RigidHead.const.mkApps_eq_app hE
      obtain ⟨vs₀', v', rfl, hR₀, hv⟩ := List.forall₂_snoc_right hR
      obtain ⟨m3, hm, hm3⟩ := constVarN_transport k H' hR₀ (ls' := ls')
      refine ⟨fun x => Option.elim x v' m3, ?_, ?_⟩
      · rw [VExpr.mkApps_snoc]; exact .var hm
      · intro a; cases a with
        | none => exact hv
        | some a => exact hm3 a

theorem FullReduction.apply_rhs {p : Pattern} (r : p.RHS) {m3 m4 : p.Path → VExpr}
    (H : ∀ a, FullReduction Γ (m3 a) (m4 a)) :
    FullReduction Γ (r.apply ls m3) (r.apply ls m4) := by
  induction r with
  | fixed => exact .rfl
  | var a => exact H a
  | app _ _ ihf iha => exact .app ihf iha

theorem NormalEqF.apply_congr (hΓ : OnCtx Γ (env.IsType univs)) {p : Pattern} (r : p.RHS)
    {m3 m2 : p.Path → VExpr}
    (hls : List.Forall₂ (· ≈ ·) ls₁ ls) (hw₁ : ∀ l ∈ ls₁, l.WF univs) (hw : ∀ l ∈ ls, l.WF univs)
    (hv : ∀ a, NormalEqF η Γ (m3 a) (m2 a)) (ht : Γ ⊢ r.apply ls₁ m3 : A) :
    NormalEqF η Γ (r.apply ls₁ m3) (r.apply ls m2) := by
  induction r generalizing A with
  | fixed c hc => exact NormalEqF.of_levelEquiv hΓ (.instL_expr c hw₁ hw hls) ht
  | var a => exact hv a
  | app f a ihf iha =>
    simp only [Pattern.RHS.apply] at ht ⊢
    obtain ⟨_, _, h1, h2⟩ := ht.app_inv henv hΓ
    have n1 := ihf h1; have n2 := iha h2
    exact .appDF h1 ((n1.defeq hΓ).of_l henv hΓ h1).hasType.2 h2
      ((n2.defeq hΓ).of_l henv hΓ h2).hasType.2 n1 n2

alias NormalEq.apply_congr := NormalEqF.apply_congr

theorem _root_.Lean4Lean.Pattern.Check.OK.normal_congr (hΓ : OnCtx Γ (env.IsType univs)) {p : Pattern}
    {ck : p.Check} {m2 m3 : p.Path → VExpr}
    (H : ck.OK (IsDefEqU env univs Γ) ls m2)
    (hls : List.Forall₂ (· ≈ ·) ls ls₁) (hw : ∀ l ∈ ls, l.WF univs) (hw₁ : ∀ l ∈ ls₁, l.WF univs)
    (hv : ∀ a, NormalEqF η Γ (m2 a) (m3 a)) : ck.OK (IsDefEqU env univs Γ) ls₁ m3 := by
  induction ck with
  | true => trivial
  | nonzero level rest ih =>
    exact ⟨fun hz => H.1 ((VLevel.inst_congr rfl hls).trans hz), ih H.2⟩
  | defeq x y rest ih =>
    obtain ⟨⟨_, hd⟩, hr⟩ := H
    have hx := NormalEqF.apply_congr hΓ x hls hw hw₁ hv hd.hasType.1
    have hy := NormalEqF.apply_congr hΓ y hls hw hw₁ hv hd.hasType.2
    exact ⟨(hx.defeq hΓ).symm.trans henv hΓ (IsDefEqU.trans henv hΓ ⟨_, hd⟩ (hy.defeq hΓ)),
      ih hr⟩

theorem _root_.Lean4Lean.Pattern.Check.OK.weak' (W : Ctx.Lift' ρ Γ Γ') {p : Pattern}
    (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ') m1 fun x => (m2 x).lift' ρ := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.lift'_apply]
  exact h.weak' henv.ordered W

omit [Params] in
theorem _root_.Lean4Lean.Pattern.Check.OK.congr_values {df : VExpr → VExpr → Prop}
    {p : Pattern} {ck : p.Check} {m m' : p.Path → VExpr} (h : ∀ a, m a = m' a)
    (H : ck.OK df ls m) : ck.OK df ls m' := (funext h : m = m') ▸ H

/-- The argument of an applied lambda has the lambda's domain type. -/
theorem HasType.app_lam_arg (hΓ : OnCtx Γ (env.IsType univs))
    (H : Γ ⊢ .app (.lam A g) b : T) : Γ ⊢ b : A := by
  obtain ⟨_, _, hf, hb⟩ := H.app_inv henv hΓ
  have ⟨⟨_, c1⟩, _, c2⟩ := hf.lam_inv henv hΓ
  have ⟨⟨_, u1⟩, _⟩ := ((c1.lam c2).uniqU henv hΓ hf).forallE_inv henv hΓ
  exact u1.symm.defeq hb

end CaseRedexMajor

section SpineTransport2

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

theorem SpineTransport.stored_defn {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (hp : Pat (.const c) r) (hm : (Pattern.const c).Matches e m1 m2)
    (hc : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hstep : ParRed Γ e (r.1.apply m1 m2')) :
    ∀ n, SpineTransport Γ e (r.1.apply m1 m2') n := by
  cases hm
  refine SpineTransport.induct hstep fun n ih ρ Γ' x hΓ W H => ?_
  generalize hRR : (VExpr.const c m1).lift' ρ = R at H
  cases H with
  | refl h => subst hRR; exact SpineTransport.refl_case (bs := []) hΓ hstep W h
  | proofIrrel l1 l2 l3 =>
    subst hRR; exact SpineTransport.proofIrrel_case (bs := []) hΓ hstep W l1 l2 l3
  | etaL l1 l2 =>
    subst hRR; exact SpineTransport.etaL_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2
  | etaBoth l1 l2 l3 =>
    subst hRR
    exact SpineTransport.etaBoth_case (bs := []) hΓ hstep W (ih _ (by omega)) l1 l2 l3
  | constDF h1 h2 h3 h4 h5 =>
    cases hRR
    obtain ⟨out, hred, hn⟩ := NormalEq.const_stored_parallel hΓ h1 h2 h3 h4 h5 hp .const
      ((hc.weak' W).congr_values fun a => nomatch a)
      (values' := fun a => (m2' a).lift' ρ) (fun a => nomatch a)
    refine ⟨out, hred.full, ?_⟩
    simpa only [Pattern.RHS.lift'_apply] using hn
  | sortDF | elimDF | appDF | projDF | lamDF | forallEDF | etaR => cases hRR

omit [Params] in
private theorem forall₂_map_lift_lift' (vs : List VExpr) :
    (vs.map (·.lift' ρ)).map VExpr.lift = vs.map (·.lift' (.skip ρ)) := by
  simp [List.map_map, Function.comp_def, lift_lift'_skip]

theorem NormalEq.forall₂_weak (H : List.Forall₂ (NormalEq Γ) l₁ l₂) :
    List.Forall₂ (NormalEq (A :: Γ)) (l₁.map VExpr.lift) (l₂.map VExpr.lift) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.weakN .one) ih

omit [Params] in
private theorem lift_redex_spine (h : VExpr) (vs : List VExpr) (M : VExpr) (bs : List VExpr) :
    VExpr.app (VExpr.mkApps (.app (VExpr.mkApps h vs) M) bs).lift (.bvar 0) =
      VExpr.mkApps (.app (VExpr.mkApps h.lift (vs.map VExpr.lift)) M.lift)
        (bs.map VExpr.lift ++ [.bvar 0]) := by
  rw [VExpr.mkApps_snoc]; congr 1
  show VExpr.liftN 1 (VExpr.mkApps _ _) 0 = _
  rw [VExpr.liftN_mkApps]; congr 1
  show VExpr.app (VExpr.liftN 1 (VExpr.mkApps _ _) 0) _ = _
  rw [VExpr.liftN_mkApps]

/-- Transport along the computation of a redex `app (hd ls₀ vs) M` with a
rigid head. Normal equality may eta-expand the redex, split its spine, or
beta-reduce a function compared with a partial application; `fire` treats a
left-hand side already exposed as a head spine applied to a major. -/
theorem SpineTransport.redex {hd : List VLevel → VExpr} (hhd : ∀ ls, RigidHead (hd ls))
    (hlift : ∀ ls ρ, (hd ls).lift' ρ = hd ls)
    (hinv : ∀ {h' ls}, HeadEquiv h' (hd ls) → ∃ ls', h' = hd ls' ∧ List.Forall₂ (· ≈ ·) ls' ls)
    {ls₀ : List VLevel} {vs : List VExpr} {M tgt : VExpr}
    (fire : ∀ {ρ Γ' ls₁ vs₁ M₁ T Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ ls₀ → List.Forall₂ (NormalEq Γ') vs₁ (vs.map (·.lift' ρ)) →
      NormalEq Γ' M₁ (M.lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (hd ls₀) vs) M).lift' ρ : Tℓ →
      Γ' ⊢ .app (VExpr.mkApps (hd ls₁) vs₁) M₁ : T →
      ∃ X, FullReduction Γ' (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) X ∧
        NormalEq Γ' X (tgt.lift' ρ)) :
    ∀ n, SpineTransport Γ (.app (VExpr.mkApps (hd ls₀) vs) M) tgt n := by
  have main : ∀ n {ρ Γ' bs x ls₁ vs₁ M₁ Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ ls₀ → List.Forall₂ (NormalEq Γ') vs₁ (vs.map (·.lift' ρ)) →
      NormalEq Γ' M₁ (M.lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (hd ls₀) vs)
        M).lift' ρ : Tℓ →
      NormalEqN true n Γ' x (VExpr.mkApps (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) bs) →
      ∃ X, FullReduction Γ' x X ∧
        NormalEq Γ' X (VExpr.mkApps (tgt.lift' ρ) bs) := by
    intro n
    induction n using Nat.strongRecOn with | _ n ihn => ?_
    intro ρ Γ' bs x ls₁ vs₁ M₁ Tℓ hΓ W hls hvs hMr hEt H
    have hl : (hd ls₁).lift = hd ls₁ := by rw [VExpr.lift_eq_lift']; exact hlift _ _
    have ⟨_, hxd⟩ := H.defeq hΓ
    have hRt := hxd.hasType.2
    obtain ⟨_, hR₀t⟩ := schema_mkApps_head_type hΓ hRt
    obtain ⟨X₀, hX₀r, hX₀n⟩ := fire hΓ W hls hvs hMr hEt hR₀t
    have hbsT : ∀ a ∈ bs, ∃ A, Γ' ⊢ a : A := fun a ha => schema_mkApps_arg_type hΓ hRt ha
    have hspR := FullReduction.mkApps hX₀r (forall₂_rfl_full (Γ := Γ') bs)
    have hspT := FullReduction.hasType hΓ hspR hRt
    have hspN := NormalEq.mkApps_spine hΓ hX₀n (NormalEqF.forall₂_refl (η := true) hbsT) hspT
    have htyT : ∀ {P}, Γ' ⊢ VExpr.mkApps (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) bs : P →
        Γ' ⊢ VExpr.mkApps (tgt.lift' ρ) bs : P := fun h =>
      (FullReduction.hasType hΓ hspR h).defeqU_l henv hΓ (hspN.defeq hΓ)
    have lifted {A u} (hA : Γ' ⊢ A : .sort u) :
        OnCtx (A :: Γ') (env.IsType univs) ∧
        List.Forall₂ (NormalEq (A :: Γ')) (vs₁.map VExpr.lift) (vs.map (·.lift' (.skip ρ))) ∧
        NormalEq (A :: Γ') M₁.lift (M.lift' (.skip ρ)) ∧
        (A :: Γ') ⊢ (VExpr.app (VExpr.mkApps (hd ls₀) vs)
          M).lift' (.skip ρ) : Tℓ.lift := by
      refine ⟨⟨hΓ, _, hA⟩, ?_, ?_, ?_⟩
      · have := NormalEq.forall₂_weak (A := A) hvs
        rwa [forall₂_map_lift_lift'] at this
      · rw [← lift_lift'_skip]; exact hMr.weakN .one
      · rw [← lift_lift'_skip]; exact hEt.weakN henv .one
    generalize hRR : VExpr.mkApps (.app (VExpr.mkApps (hd ls₁) vs₁) M₁) bs = R at H
    cases H with
    | refl _ => subst hRR; exact ⟨_, hspR, hspN⟩
    | proofIrrel l1 l2 l3 => subst hRR; exact ⟨_, .rfl, .proofIrrel l1 l2 (htyT l3)⟩
    | etaL l1 l2 =>
      subst hRR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      obtain ⟨hΓ', hvs', hMr', hEt'⟩ := lifted hA
      rw [lift_redex_spine, hl] at l2
      obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ' W.skip hls hvs' hMr' hEt' l2
      rw [← lift_mkApps_lift'] at hn
      exact ⟨_, .lam .rfl hY, .etaL (htyT l1) hn⟩
    | etaBoth l1 l2 l3 =>
      subst hRR
      have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
      obtain ⟨hΓ', hvs', hMr', hEt'⟩ := lifted hA
      rw [lift_redex_spine, hl] at l3
      obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ' W.skip hls hvs' hMr' hEt' l3
      rw [← lift_mkApps_lift'] at hn
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta l1)).trans (FullReduction.lam .rfl hY),
        .etaL (htyT l2) hn⟩
    | @appDF _ x1 _ _ _ x2 _ _ _ _ l1 l2 l3 l4 l5 l6 =>
      rcases eq_nil_or_snoc bs with rfl | ⟨bs₀, b, rfl⟩
      · cases hRR
        have hxT := hxd.hasType.1
        have hx2M : NormalEq Γ' _ _ := NormalEq.trans hΓ ⟨_, l6⟩ hMr
        rcases NormalEqN.spine_expose hΓ (hhd _) _ l5 (bs := []) .nil l1 with
          hprop | ⟨h', vs₂, he, hred, hvs₂⟩ | ⟨A', g, m, targs₁, B', hm, hred, hg, hrel, _⟩
        · have hP := HasType.mkApps_proof hΓ hprop l1 (bs := [_]) hxT
          exact ⟨_, .rfl, .proofIrrel hP hxT (htyT hRt)⟩
        · obtain ⟨ls₂, rfl, hls₂⟩ := hinv he
          simp only [List.append_nil] at hvs₂
          have hred' : FullReduction Γ' (.app x1 x2) _ := FullReduction.app hred .rfl
          have hR₂t := FullReduction.hasType hΓ hred' hxT
          obtain ⟨X, hX, hn⟩ := fire hΓ W
            (Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') hls₂ hls)
            (NormalEq.forall₂_trans hΓ hvs₂ hvs) hx2M hEt hR₂t
          exact ⟨_, hred'.trans hX, by simpa only [VExpr.mkApps, List.foldl] using hn⟩
        · have hred' : FullReduction Γ' (.app x1 x2) (.app (.lam A' g) x2) :=
            FullReduction.app hred .rfl
          have happT := FullReduction.hasType hΓ hred' hxT
          have hx2A := HasType.app_lam_arg hΓ happT
          have hstepβ : FullStep Γ' (.app (.lam A' g) x2) (g.inst x2) := .core (.beta .rfl .rfl)
          have hg' := hg.instN hx2A .zero
          rw [inst_lift_spine, VExpr.mkApps_snoc] at hg'
          simp only [List.append_nil] at hrel
          obtain ⟨Y, hY, hn⟩ := ihn _ (by omega) hΓ W hls (NormalEq.forall₂_trans hΓ hrel hvs)
            hx2M hEt (bs := []) hg'
          exact ⟨_, (hred'.tail hstepβ).trans hY, hn⟩
      · rw [VExpr.mkApps_snoc] at hRR; cases hRR
        obtain ⟨X, hX, hn⟩ := ihn _ (by omega) hΓ W hls hvs hMr hEt l5
        have hX' := FullReduction.hasType hΓ hX l1
        rw [VExpr.mkApps_snoc]
        exact ⟨_, hX.app .rfl, .appDF hX' ((hn.defeq hΓ).of_l henv hΓ hX').hasType.2 l3 l4
          hn ⟨_, l6⟩⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF | etaR =>
      obtain ⟨_, _, happ⟩ := mkApps_app_isApp (VExpr.mkApps (hd ls₁) vs₁) M₁ bs
      rw [happ] at hRR; cases hRR
  intro n ρ Γ' bs x hΓ W H
  have ⟨_, hxd⟩ := H.defeq hΓ
  obtain ⟨_, hEt⟩ := schema_mkApps_head_type hΓ hxd.hasType.2
  have hEt' := hEt
  simp only [VExpr.lift', VExpr.lift'_mkApps, hlift] at hEt' H
  obtain ⟨_, _, hFt, hMt⟩ := hEt'.app_inv henv hΓ
  exact main n hΓ W (VLevel.forall₂_equiv_refl ls₀)
    (NormalEqF.forall₂_refl (η := true) fun a ha => schema_mkApps_arg_type hΓ hFt ha) (.refl hMt) hEt H


theorem SpineTransport.stored_iota
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hc : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hr : ∀ a, ParRed Γ (m2 a) (m2' a))
    (ih : ∀ a n, SpineTransport Γ (m2 a) (m2' a) n) :
    ∀ n, SpineTransport Γ e (r.1.apply m1 m2') n := by
  have hstep : ParRed Γ e (r.1.apply m1 m2') := .extra hp hm hc hr
  obtain ⟨F, M, lsc, g1, g2, hF, hM, rfl, rfl⟩ :
      ∃ F M lsc g1 g2, ((Pattern.const rc).varN mr).Matches F m1 g1 ∧
        ((Pattern.const cc).varN kc).Matches M lsc g2 ∧ e = .app F M ∧ m2 = Sum.elim g1 g2 := by
    cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
  obtain ⟨vsF, rfl⟩ : ∃ vs, F = VExpr.mkApps (.const rc m1) vs := ⟨_, hF.const_arguments⟩
  obtain ⟨fsM, rfl⟩ : ∃ fs, M = VExpr.mkApps (.const cc lsc) fs := ⟨_, hM.const_arguments⟩
  -- target of the step, lifted
  have fire : ∀ {ρ Γ' ls₁ vs₁ M₁ T Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ m1 → List.Forall₂ (NormalEq Γ') vs₁ (vsF.map (·.lift' ρ)) →
      NormalEq Γ' M₁ ((VExpr.mkApps (.const cc lsc) fsM).lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (.const rc m1) vsF) (VExpr.mkApps (.const cc lsc) fsM)).lift' ρ : Tℓ →
      Γ' ⊢ .app (VExpr.mkApps (.const rc ls₁) vs₁) M₁ : T →
      ∃ X, FullReduction Γ' (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁) X ∧
        NormalEq Γ' X ((r.1.apply m1 m2').lift' ρ) := by
    intro ρ Γ' ls₁ vs₁ M₁ T Tℓ hΓ W hls hvs hMr hEt ht
    simp only [VExpr.lift', VExpr.lift'_mkApps] at hEt hMr
    have hFℓ : ((Pattern.const rc).varN mr).Matches
        (VExpr.mkApps (.const rc m1) (vsF.map (·.lift' ρ))) m1 (fun a => (g1 a).lift' ρ) := by
      have := (Pattern.matches_lift' (ρ := ρ)).2 ⟨_, hF, fun _ => rfl⟩
      simpa only [VExpr.lift'_mkApps, VExpr.lift'] using this
    have hMℓ : ((Pattern.const cc).varN kc).Matches
        (VExpr.mkApps (.const cc lsc) (fsM.map (·.lift' ρ))) lsc (fun a => (g2 a).lift' ρ) := by
      have := (Pattern.matches_lift' (ρ := ρ)).2 ⟨_, hM, fun _ => rfl⟩
      simpa only [VExpr.lift'_mkApps, VExpr.lift'] using this
    have hval : (fun a => (Sum.elim g1 g2 a).lift' ρ) =
        Sum.elim (fun a => (g1 a).lift' ρ) (fun a => (g2 a).lift' ρ) := by
      funext a; cases a <;> rfl
    have hEℓ := Pattern.Matches.app hFℓ hMℓ
    have hcℓ := (hc.weak' W).congr_values
      (p := Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
      (m' := Sum.elim (fun a => (g1 a).lift' ρ) (fun a => (g2 a).lift' ρ))
      (fun a => by cases a <;> rfl)
    have hstepℓ := hstep.weak' W
    simp only [VExpr.lift', VExpr.lift'_mkApps] at hstepℓ
    -- typing and the comparison with the lifted redex
    obtain ⟨_, _, hft, hMt⟩ := ht.app_inv henv hΓ
    obtain ⟨_, _, hFt, hMℓt⟩ := hEt.app_inv henv hΓ
    obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ hft
    obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ hFt
    obtain ⟨ci, hci, hw₁, hlen₁⟩ := hh₁.const_inv henv hΓ
    obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
    have hhead : NormalEq Γ' (.const rc ls₁) (.const rc m1) := .constDF hci hw₁ hw hlen₁ hls
    have hnF := NormalEq.mkApps_spine hΓ hhead hvs hft
    have hFt' := ((hnF.defeq hΓ).of_l henv hΓ hft).hasType.2
    have hMt' := ((hMr.defeq hΓ).of_l henv hΓ hMt).hasType.2
    have hxE : NormalEq Γ' (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁) _ :=
      .appDF hft hFt' hMt hMt' hnF hMr
    have hxT : Γ' ⊢ .app (VExpr.mkApps (.const rc ls₁) vs₁) M₁ : Tℓ :=
      hEt.defeqU_l henv hΓ (hxE.defeq hΓ).symm
    have hrhsT := hstepℓ.hasType hΓ hEt
    obtain ⟨k, HM⟩ := hMr
    rcases NormalEqN.spine_expose hΓ .const k HM (bs := []) .nil hMt with
      hprop | ⟨h', fs₂, he, hred, hfs⟩ | ⟨A', g, m, targs₁, B', _, _, _, hrel, hty⟩
    · have hMℓP := hMt.defeqU_l henv hΓ (HM.defeq hΓ)
      have hTℓ := Params.major_proof hΓ hp hEℓ hcℓ hEt hMℓP hprop
      exact ⟨_, .rfl, .proofIrrel hTℓ hxT hrhsT⟩
    · obtain ⟨lsc₂, rfl, hlsc⟩ : ∃ lsc₂, h' = .const cc lsc₂ ∧ List.Forall₂ (· ≈ ·) lsc₂ lsc := by
        cases he with | const h => exact ⟨_, rfl, h⟩
      simp only [List.append_nil] at hfs
      obtain ⟨m3₁, hm3₁, hr₁⟩ := Pattern.Matches.constVarN_transport mr hFℓ hvs (ls' := ls₁)
      obtain ⟨m3₂, hm3₂, hr₂⟩ := Pattern.Matches.constVarN_transport kc hMℓ hfs (ls' := lsc₂)
      have hm₃ := Pattern.Matches.app hm3₁ hm3₂
      have hrel3 : ∀ a, NormalEq Γ' (Sum.elim m3₁ m3₂ a)
          (Sum.elim (fun a => (g1 a).lift' ρ) (fun a => (g2 a).lift' ρ) a) := by
        intro a; cases a with
        | inl a => exact hr₁ a
        | inr a => exact hr₂ a
      have hc₃ := hcℓ.normal_congr hΓ (ls₁ := ls₁)
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
        hw hw₁ (fun a => (hrel3 a).symm hΓ)
      have hred₃ : FullReduction Γ' (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁)
          (.app (VExpr.mkApps (.const rc ls₁) vs₁) (VExpr.mkApps (.const cc lsc₂) fs₂)) :=
        FullReduction.app .rfl hred
      have hfire := FullStep.core (ParRed.extra (Γ := Γ') hp hm₃ hc₃ fun _ => .rfl)
      have hcap : ∀ a, ∃ Y, FullReduction Γ' (Sum.elim m3₁ m3₂ a) Y ∧
          NormalEq Γ' Y ((m2' a).lift' ρ) := by
        intro a
        obtain ⟨ka, Ha⟩ := hrel3 a
        have Ha' : NormalEqN true ka Γ' (Sum.elim m3₁ m3₂ a)
            (VExpr.mkApps ((Sum.elim g1 g2 a).lift' ρ) []) := by cases a <;> exact Ha
        have hgoal := ih a ka hΓ W Ha'
        simpa only [VExpr.mkApps, List.foldl] using hgoal
      let m4 := fun a => Classical.choose (hcap a)
      have hm4r : ∀ a, FullReduction Γ' (Sum.elim m3₁ m3₂ a) (m4 a) :=
        fun a => (Classical.choose_spec (hcap a)).1
      have hm4n : ∀ a, NormalEq Γ' (m4 a) ((m2' a).lift' ρ) :=
        fun a => (Classical.choose_spec (hcap a)).2
      have htot := (hred₃.tail hfire).trans (FullReduction.apply_rhs r.1 hm4r (ls := ls₁))
      have hT4 := FullReduction.hasType hΓ htot ht
      refine ⟨_, htot, ?_⟩
      rw [Pattern.RHS.lift'_apply]
      exact NormalEq.apply_congr hΓ r.1 hls hw₁ hw hm4n hT4
    · exfalso
      simp only [List.append_nil] at hrel
      obtain ⟨_, hcc⟩ := schema_mkApps_head_type hΓ hty
      have hMℓ' := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
      have hpi := hty.defeqU_l henv hΓ (hMℓ'.defeq hΓ)
      exact Params.major_not_pi hΓ hp hEℓ hEt hpi
  have fire' : ∀ {ρ Γ' ls₁ vs₁ M₁ T Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ m1 → List.Forall₂ (NormalEq Γ') vs₁ (vsF.map (·.lift' ρ)) →
      NormalEq Γ' M₁ ((VExpr.mkApps (.const cc lsc) fsM).lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (.const rc m1) vsF)
        (VExpr.mkApps (.const cc lsc) fsM)).lift' ρ : Tℓ →
      Γ' ⊢ .app (VExpr.mkApps (.const rc ls₁) vs₁) M₁ : T →
      ∃ X, FullReduction Γ' (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁) X ∧
        NormalEq Γ' X ((r.1.apply m1 m2').lift' ρ) := fire
  exact SpineTransport.redex (hd := fun ls => .const rc ls) (fun _ => .const) (fun _ _ => rfl)
    (fun he => by cases he with | const h => exact ⟨_, rfl, h⟩) fire'

theorem SpineTransport.stored (hp : Pat p r) (hm : p.Matches e m1 m2)
    (hc : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hr : ∀ a, ParRed Γ (m2 a) (m2' a))
    (ih : ∀ a n, SpineTransport Γ (m2 a) (m2' a) n) :
    ∀ n, SpineTransport Γ e (r.1.apply m1 m2') n := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hp
  cases sp with
  | defn c => exact SpineTransport.stored_defn hp hm hc (.extra hp hm hc hr)
  | iota rc mr cc kc => exact SpineTransport.stored_iota hp hm hc hr ih

theorem HasType.elim_levels_wf (hΓ : OnCtx Γ (env.IsType univs))
    (H : Γ ⊢ .elim block slot packed : V) : ∀ l ∈ packed, l.WF univs := by
  obtain ⟨_, _, _, _, _, _, _, rfl, _, _, _, hp, _, _⟩ := H.elim_inv henv hΓ
  exact hp.packedWF

theorem NormalEq.instantiate_variables_full (hΓ : OnCtx Γ (env.IsType univs))
    (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      ∃ out, FullReduction Γ arguments[i] out ∧ NormalEq Γ out arguments'[i])
    (ht : Γ ⊢ InductiveSignature.instantiateParams body arguments : type) :
    ∃ out, FullReduction Γ (InductiveSignature.instantiateParams body arguments) out ∧
      NormalEq Γ out (InductiveSignature.instantiateParams body arguments') := by
  induction H generalizing type with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by omega) (by omega)
  | app hf ha ihf iha =>
    have ⟨_, _, hfn, harg⟩ := ht.app_inv henv hΓ
    obtain ⟨fn', hfnRed, hfnNormal⟩ := ihf hc.1 hfn
    obtain ⟨arg', hargRed, hargNormal⟩ := iha hc.2 harg
    have hfn' := hfnRed.hasType hΓ hfn
    have harg' := hargRed.hasType hΓ harg
    exact ⟨_, .app hfnRed hargRed, .appDF hfn'
      ((hfnNormal.defeq hΓ).of_l henv hΓ hfn').hasType.2
      harg' ((hargNormal.defeq hΓ).of_l henv hΓ harg').hasType.2 hfnNormal hargNormal⟩

theorem CaseStep.rhs_normalEq_full (hΓ : OnCtx Γ (env.IsType univs))
    (H : CaseStep env univs Γ rule levels arguments)
    (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      ∃ out, FullReduction Γ arguments[i] out ∧ NormalEq Γ out arguments'[i]) :
    ∃ out, FullReduction Γ (rule.rhs levels arguments) out ∧
      NormalEq Γ out (rule.rhs levels' arguments') := by
  have hvars := H.rhs_variables
  obtain ⟨type, ht⟩ := H.defeq henv hΓ
  simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at ht ⊢
  exact NormalEq.instantiate_variables_full hΓ hvars H.closed.2.1 hlen hargs ht.hasType.2

theorem SpineTransport.schema
    {rule : InductiveSignature.CaseSchema.AppliedRule}
    {actual : InductiveSignature.CaseSchema.Application}
    (hm : CaseRedex env univs Γ rule actual)
    (hl : arguments.length = (rule.capture actual).length)
    (hr : ∀ i (hi : i < (rule.capture actual).length),
      ParRed Γ (rule.capture actual)[i] (arguments[i]'(by omega)))
    (ih : ∀ i (hi : i < (rule.capture actual).length) n,
      SpineTransport Γ (rule.capture actual)[i] (arguments[i]'(by omega)) n) :
    ∀ n, SpineTransport Γ actual.expr (rule.rhs actual.levels arguments) n := by
  have hstep : ParRed Γ actual.expr (rule.rhs actual.levels arguments) := .schema hm hl hr
  show ∀ n, SpineTransport Γ (.app (VExpr.mkApps (.elim actual.block actual.owner actual.levels)
    actual.arguments) (VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
      actual.ctorArguments)) _ n
  refine SpineTransport.redex (hd := fun ls => .elim actual.block actual.owner ls)
    (fun _ => .elim) (fun _ _ => rfl) (fun he => by cases he with | elim h => exact ⟨_, rfl, h⟩) ?_
  intro ρ Γ' ls₁ vs₁ M₁ T Tℓ hΓ W hls hvs hMr hEt ht
  have hmℓ := hm.weak' henv W
  have hstepℓ := hstep.weak' W
  have hEℓ : Γ' ⊢ (CaseApplicationMap actual fun e => e.lift' ρ).expr : Tℓ := by
    rw [case_application_lift']; exact hEt
  have hrhsT := hstepℓ.hasType hΓ hEt
  have hEt0 := hEt
  simp only [VExpr.lift', VExpr.lift'_mkApps] at hEt hMr
  obtain ⟨_, _, hft, hMt⟩ := ht.app_inv henv hΓ
  obtain ⟨_, _, hFt, hMℓt⟩ := hEt.app_inv henv hΓ
  obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ hft
  obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ hFt
  have hw₁ := HasType.elim_levels_wf hΓ hh₁
  have hw := HasType.elim_levels_wf hΓ hh
  have hhead : NormalEq Γ' (.elim actual.block actual.owner ls₁)
      (.elim actual.block actual.owner actual.levels) :=
    .of_levelEquiv hΓ (.elim hls hw) hh₁
  have hnF := NormalEq.mkApps_spine hΓ hhead hvs hft
  have hFt' := ((hnF.defeq hΓ).of_l henv hΓ hft).hasType.2
  have hMt' := ((hMr.defeq hΓ).of_l henv hΓ hMt).hasType.2
  have hxE : NormalEq Γ' (.app (VExpr.mkApps (.elim actual.block actual.owner ls₁) vs₁) M₁) _ :=
    .appDF hft hFt' hMt hMt' hnF hMr
  have hxT := hEt.defeqU_l henv hΓ (hxE.defeq hΓ).symm
  obtain ⟨k, HM⟩ := hMr
  rcases NormalEqN.spine_expose hΓ .const k HM (bs := []) .nil hMt with
    hprop | ⟨h', cs₂, he, hred, hcs⟩ | ⟨A', g, m, targs₁, B', _, _, _, hrel, hty⟩
  · have hMℓP := hMt.defeqU_l henv hΓ (HM.defeq hΓ)
    obtain ⟨resultType, hres, hEres⟩ := hmℓ.result_prop_of_major_proof henv hΓ hprop
      (by simpa [CaseApplicationMap] using hMℓP)
    rw [case_application_lift'] at hEres
    have hsame := hEres.uniqU henv hΓ hEt0
    exact ⟨_, .rfl, .proofIrrel (hres.defeqU_l henv hΓ hsame) hxT hrhsT⟩
  · obtain ⟨ls₂, rfl, hls₂⟩ : ∃ ls₂, h' = .const actual.ctorName ls₂ ∧
        List.Forall₂ (· ≈ ·) ls₂ actual.ctorLevels := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    simp only [List.append_nil] at hcs
    have hct := FullReduction.hasType hΓ hred hMt
    obtain ⟨_, hch⟩ := schema_mkApps_head_type hΓ hct
    obtain ⟨_, _, hw₂, _⟩ := hch.const_inv henv hΓ
    let actualℓ := CaseApplicationMap actual fun e => e.lift' ρ
    let actual'' : InductiveSignature.CaseSchema.Application :=
      { actualℓ with levels := ls₁, ctorLevels := ls₂ }
    let actual₃ : InductiveSignature.CaseSchema.Application :=
      { actual'' with arguments := vs₁, ctorArguments := cs₂ }
    have hlsSymm : List.Forall₂ (· ≈ ·) actual.levels ls₁ :=
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls)
    have hls₂Symm : List.Forall₂ (· ≈ ·) actual.ctorLevels ls₂ :=
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls₂)
    have hL : VExpr.LEquiv univs actualℓ.expr actual''.expr :=
      .app (VExpr.LEquiv.mkApps_fn (.elim hlsSymm hw₁) _) (VExpr.LEquiv.mkApps_fn (.const hls₂Symm hw₂) _)
    have he' := (NormalEq.of_levelEquiv (η := true) hΓ hL hEℓ).defeq hΓ
    have hm' := hmℓ.congr_levels henv hΓ hw₁ hlsSymm hls₂Symm he'
    have hspine : CaseApplicationRelated (NormalEq Γ') actual₃ actual'' :=
      ⟨rfl, rfl, rfl, rfl, rfl, hvs, hcs⟩
    have hm₃ := CaseRedex.of_normalEq_spine hΓ hm' hspine
    have hred₃ : FullReduction Γ' (.app (VExpr.mkApps (.elim actual.block actual.owner ls₁) vs₁) M₁)
        actual₃.expr := FullReduction.app .rfl hred
    have hfire := FullStep.core (ParRed.schema (arguments := rule.capture actual₃) hm₃ rfl
      fun _ _ => .rfl)
    have hcap : List.Forall₂ (NormalEq Γ') (rule.capture actual₃)
        ((rule.capture actual).map fun e => e.lift' ρ) := by
      have := hspine.capture (rule := rule)
      rwa [show rule.capture actual'' = rule.capture actualℓ from rfl, case_capture_map] at this
    have hcapLen := Lean4Lean.List.Forall₂.length_eq hcap
    simp only [List.length_map] at hcapLen
    obtain ⟨out, hout, hn⟩ := CaseStep.rhs_normalEq_full hΓ hm₃.source
      (arguments' := arguments.map fun e => e.lift' ρ) (levels' := actual.levels)
      (by simp only [List.length_map]; omega) (by
        intro i hi hi'
        have h1 := case_forall₂_get hcap hi (by simp only [List.length_map]; omega)
        simp only [List.getElem_map] at h1 ⊢
        obtain ⟨ka, Ha⟩ := h1
        have := ih i (by omega) ka (bs := []) hΓ W Ha
        simpa only [VExpr.mkApps, List.foldl] using this)
    have hc : (rule.body.rhs.instL actual.levels).ClosedN arguments.length := by
      simpa [hl] using hm.source.closed.2.1.instL
    refine ⟨_, (hred₃.tail hfire).trans hout, ?_⟩
    simpa only [InductiveSignature.CaseSchema.AppliedRule.rhs, instantiateParams_lift' hc] using hn
  · exfalso
    simp only [List.append_nil] at hrel
    obtain ⟨_, hcc⟩ := schema_mkApps_head_type hΓ hty
    have hMℓ' := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
    have hpi := hty.defeqU_l henv hΓ (hMℓ'.defeq hΓ)
    exact CaseRedex.major_not_pi henv hΓ hmℓ (by simpa [CaseApplicationMap] using hpi)

theorem ParRed.spineTransport (H : ParRed Γ e e') : ∀ n, SpineTransport Γ e e' n := by
  induction H with
  | bvar | sort | const | elim => exact fun _ => SpineTransport.same
  | app hf ha ihf iha => exact SpineTransport.app hf ha ihf iha
  | proj hm ihm => exact SpineTransport.proj hm ihm
  | lam hA hb _ ihb => exact SpineTransport.lam hA hb ihb
  | forallE hA hB ihA ihB => exact SpineTransport.forallE hA hB ihA ihB
  | beta hb ha ihb iha => exact SpineTransport.beta hb ha ihb iha
  | extra hp hm hc hr ih => exact SpineTransport.stored hp hm hc hr ih
  | schema hm hl hr ih => exact SpineTransport.schema hm hl hr ih

/-- Normal equality respects one parallel step. Eta expansion of the left
side, needed for the eta and extensionality comparisons, is the full
presentation's `FullStep.funEta`. -/
theorem NormalEq.parRed (hΓ : OnCtx Γ (env.IsType univs)) (H1 : NormalEq Γ e₁ e₂)
    (H2 : ParRed Γ e₂ e₂') :
    ∃ e₁', FullReduction Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂' := by
  obtain ⟨n, H1⟩ := H1
  have := H2.spineTransport n (bs := []) hΓ .refl
    (by simp only [VExpr.lift'_refl, VExpr.mkApps, List.foldl]; exact H1)
  simpa only [VExpr.lift'_refl, VExpr.mkApps, List.foldl] using this

end SpineTransport2

section RigidRule

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

theorem eqUpToLevels_rfl (hΓ : OnCtx Γ (env.IsType univs)) (h : Γ ⊢ e : A) :
    EqUpToLevels univs e e :=
  (EqUpToLevels.refl (CtxStrong.strong henv.ordered hΓ).levelWF (IsDefEq.strong henv.ordered hΓ h)).1

theorem eqUpToLevels_forall₂_rfl (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {l : List VExpr}, (∀ a ∈ l, ∃ A, Γ ⊢ a : A) → List.Forall₂ (EqUpToLevels univs) l l
  | [], _ => .nil
  | _ :: _, H =>
    let ⟨_, h⟩ := H _ (List.mem_cons_self ..)
    .cons (eqUpToLevels_rfl hΓ h) (eqUpToLevels_forall₂_rfl hΓ fun b hb => H b (List.mem_cons_of_mem _ hb))

/-- Transport along a constant-headed computation rule (singleton prefix
unfolding or quotient lifting) through normal equality, by spine exposure.
An eta-expanded left side recurses at a smaller comparison bound on the
rule applied to the fresh variable. -/
theorem NormalEqN.fullStep_rigidRule {name : Name}
    (Rule : List VExpr → List VLevel → List VExpr → VExpr → Prop)
    (step : ∀ {Γ ls args rhs}, Rule Γ ls args rhs →
      FullStep Γ (VExpr.mkApps (.const name ls) args) rhs)
    (defeq : ∀ {Γ ls args rhs}, OnCtx Γ (env.IsType univs) → Rule Γ ls args rhs →
      Γ ⊢ VExpr.mkApps (.const name ls) args ≡ rhs)
    (congr : ∀ {Γ ls ls' args args' rhs}, OnCtx Γ (env.IsType univs) → Rule Γ ls args rhs →
      List.Forall₂ (· ≈ ·) ls ls' → (∀ l ∈ ls', l.WF univs) →
      List.Forall₂ (NormalEq Γ) args args' → (∀ a ∈ args', ∃ A, Γ ⊢ a : A) →
      ∃ rhs', Rule Γ ls' args' rhs' ∧ NormalEq Γ rhs' rhs)
    (ih : ∀ m < n, ∀ {Γ x y z}, OnCtx Γ (env.IsType univs) → NormalEqN true m Γ x y →
      FullStep Γ y z → ∃ X, FullReduction Γ x X ∧ NormalEq Γ X z)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN true n Γ x (VExpr.mkApps (.const name ls) args)) (hr : Rule Γ ls args rhs) :
    ∃ X, FullReduction Γ x X ∧ NormalEq Γ X rhs := by
  have ⟨_, hd⟩ := H.defeq hΓ
  have hx := hd.hasType.1
  have hrhs := hd.hasType.2.defeqU_l henv hΓ (defeq hΓ hr)
  rcases NormalEqN.spine_expose hΓ .const n H (bs := []) .nil hx with
    hprop | ⟨h', args', he, hred, hargs⟩ | ⟨A, g, m, targs₁, B, hm, hred, hg, hrel, hty⟩
  · exact ⟨_, .rfl, .proofIrrel hprop hx hrhs⟩
  · obtain ⟨ls', rfl, hls⟩ : ∃ ls', h' = .const name ls' ∧ List.Forall₂ (· ≈ ·) ls' ls := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    simp only [List.append_nil] at hargs
    have hT' := FullReduction.hasType hΓ hred hx
    obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ hT'
    obtain ⟨_, _, hw', _⟩ := hh.const_inv henv hΓ
    obtain ⟨rhs', hr', hn⟩ := congr hΓ hr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls)) hw'
      (Lean4Lean.List.Forall₂.imp (fun _ _ (h : NormalEq Γ _ _) => h.symm hΓ)
        (Lean4Lean.List.Forall₂.flip hargs))
      (fun a ha => schema_mkApps_arg_type hΓ hT' ha)
    exact ⟨_, hred.tail (step hr'), hn⟩
  · simp only [List.append_nil] at hrel
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := hty.isType henv hΓ; h.forallE_inv henv
    have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨rhs₁, hr₁, hn₁⟩ := congr hΓ hr (VLevel.forall₂_equiv_refl ls)
      (let ⟨_, h⟩ := schema_mkApps_head_type hΓ hd.hasType.2
       let ⟨_, _, hw, _⟩ := h.const_inv henv hΓ; hw)
      (Lean4Lean.List.Forall₂.imp (fun _ _ (h : NormalEq Γ _ _) => h.symm hΓ)
        (Lean4Lean.List.Forall₂.flip hrel))
      (fun a ha => schema_mkApps_arg_type hΓ hty ha)
    have hR' : FullStep (A :: Γ) (.app (VExpr.mkApps (.const name ls) targs₁).lift (.bvar 0))
        (.app rhs₁.lift (.bvar 0)) := .app (FullStep.weakN .one (step hr₁)) .rfl
    obtain ⟨Y, hY, hn⟩ := ih m hm hΓ' hg hR'
    have hrhs₁ := hty.defeqU_l henv hΓ (defeq hΓ hr₁)
    exact ⟨_, hred.trans (FullReduction.lam .rfl hY), (NormalEq.etaL hrhs₁ hn).trans hΓ hn₁⟩

theorem NormalEqN.fullStep_projIota (hΓ : OnCtx Γ (env.IsType univs))
    (lproj : Γ ⊢ .proj family index major : resultType)
    (lMajor : NormalEqN true k Γ major (VExpr.mkApps (.const info.ctorName levels) args))
    (hl : env.projections family info)
    (hproj : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName levels) args) : fieldType)
    (hget : args[info.nparams + index]? = some field) (hfield : Γ ⊢ field : fieldType) :
    ∃ X, FullReduction Γ (.proj family index major) X ∧ NormalEq Γ X field := by
  obtain ⟨info', levels', params, indexArgs, sourceMajor, fieldType', fieldLevel,
    hinfo, hlevels, huvars, hparams, hindices, hfieldTy, hfieldTyping,
    hmajor, hclosed, hguard⟩ := lproj.proj_inv henv hΓ
  have hmT := hmajor.hasType.2
  have hnormal := NormalEq.projDF lproj ⟨_, lMajor⟩
  have hright := ((hnormal.defeq hΓ).of_l henv hΓ lproj).hasType.2
  have hfield' : Γ ⊢ field : resultType :=
    HasType.defeqU_r henv hΓ (hproj.uniqU henv hΓ hright) hfield
  rcases NormalEqN.spine_expose hΓ .const k lMajor (bs := []) .nil hmT with
    hprop | ⟨h', args', he, hred, hargs⟩ | ⟨A, g, m, targs₁, B, _, _, _, hrel, hty⟩
  · have hprop' := lproj.proj_result_prop_of_major_proof henv hΓ hprop hmT
    have hout := (FullStep.projIota hl hproj hget hfield).hasType hΓ hright
    exact ⟨_, .rfl, .proofIrrel hprop' lproj hout⟩
  · obtain ⟨ls', rfl, -⟩ : ∃ ls', h' = .const info.ctorName ls' ∧
        List.Forall₂ (· ≈ ·) ls' levels := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    simp only [List.append_nil] at hargs
    have hred' : FullReduction Γ (.proj family index major)
        (.proj family index (VExpr.mkApps (.const info.ctorName ls') args')) := hred.proj
    obtain ⟨field₀, hf, hn⟩ := NormalEq.fullStep_projIota_spine hΓ hl
      (hred'.hasType hΓ lproj) hargs hget hfield'
    exact ⟨_, hred'.trans hf, hn⟩
  · exfalso
    simp only [List.append_nil] at hrel
    obtain ⟨_, hcc⟩ := schema_mkApps_head_type hΓ hty
    have hsp := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
    have hpi := hty.defeqU_l henv hΓ (hsp.defeq hΓ)
    have hfam := hmT.defeqU_l henv hΓ (lMajor.defeq hΓ)
    have ⟨_, hsort⟩ := hmajor.hasType.2.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hinfo) hsort
      (hfam.uniqU henv hΓ hpi)

end RigidRule

/-- Normal equality respects full reduction. The remaining proof obligations
are application-head and primitive projection exposure; constant unfolding
and the explicit function and structure eta cases are proved. -/
theorem NormalEqN.fullStep : ∀ n {Γ left right result},
    OnCtx Γ (env.IsType univs) → NormalEqN true n Γ left right → FullStep Γ right result →
    ∃ output, FullReduction Γ left output ∧ NormalEq Γ output result := by
  classical
  intro n
  induction n using Nat.strongRecOn with | _ n ihn => ?_
  intro Γ left right result hΓ H R
  cases H with
  | refl h => exact ⟨_, .tail .rfl R, .refl (R.hasType hΓ h)⟩
  | proofIrrel hp hl hr => exact ⟨_, .rfl, .proofIrrel hp hl (R.hasType hΓ hr)⟩
  | @sortDF l₁ l₂ _ _ hl hr he =>
    generalize hs : VExpr.sort l₂ = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.sortDF hl hr he).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.sortDF hl hr he).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.sortDF hl hr he).normalEq.fullStep_funEta hΓ hfun
    | delta h => exact False.elim (VExpr.mkApps_ne_sort (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_sort (by intros; intro h; cases h) _ hs.symm)
    | app => cases hs
    | proj => cases hs
    | projIota => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @lamDF _ A A₁ u A₂ _ _ body₁ body₂ l1 l2 l3 =>
    generalize hs : VExpr.lam A₂ body₂ = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.lamDF l1 l2 l3).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.lamDF l1 l2 l3).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.lamDF l1 l2 l3).normalEq.fullStep_funEta hΓ hfun
    | lam r1 r2 =>
      cases hs
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, l1.hasType.1⟩
      obtain ⟨_, h1⟩ := l3.defeq hΓ'
      have h2 := h1.hasType.1.defeqU_l henv hΓ' (l3.defeq hΓ')
      replace r2 := r2.defeqDFC hΓ (.succ .zero l2.symm) <| .defeqDFC henv (.succ .zero l2) h2
      obtain ⟨_, b1, b2⟩ := ihn _ (by omega) hΓ' l3 r2
      exact ⟨_, .lam .rfl (b1.defeqDFC hΓ (.succ .zero l1) h1.hasType.1),
        .lamDF l1 (.trans l2 (r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, l2⟩ l1.hasType.1))) b2⟩
    | delta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | app => cases hs
    | proj => cases hs
    | projIota => cases hs
    | forallE => cases hs
  | @forallEDF _ A A₁ u _ _ A₂ B₁ v _ B₂ l1 l2 l3 l4 =>
    generalize hs : VExpr.forallE A₂ B₂ = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.forallEDF l1 l2 l3 l4).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.forallEDF l1 l2 l3 l4).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.forallEDF l1 l2 l3 l4).normalEq.fullStep_funEta hΓ hfun
    | forallE r1 r2 =>
      cases hs
      obtain ⟨_, a1, a2⟩ := ihn _ (by omega) hΓ l2 r1
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, l1.hasType.1⟩
      have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ')
      have W := l1.transU_l henv hΓ (l2.defeq hΓ)
      replace r2 := r2.defeqDFC hΓ (.succ .zero W.symm) <| .defeqDFC henv (.succ .zero W) h2
      obtain ⟨_, b1, b2⟩ := ihn _ (by omega) hΓ' l4 r2
      have := r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, W⟩ l1.hasType.1)
      exact ⟨_, .forallE a1 (b1.defeqDFC hΓ (.succ .zero l1) l3),
        .forallEDF (.transU_l henv hΓ (W.trans this) (a2.defeq hΓ).symm) a2 (b1.hasType hΓ' l3) b2⟩
    | delta h => exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hs.symm)
    | app => cases hs
    | proj => cases hs
    | projIota => cases hs
    | lam => cases hs
  | @appDF _ f A B f₂ a b _ _ _ l1 l2 l3 l4 l5 l6 =>
    generalize hs : VExpr.app f₂ b = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.appDF l1 l2 l3 l4 l5 l6).normalEq.fullStep_funEta hΓ hfun
    | app r1 r2 =>
      cases hs
      obtain ⟨_, a1, a2⟩ := ihn _ (by omega) hΓ l5 r1
      obtain ⟨_, b1, b2⟩ := ihn _ (by omega) hΓ l6 r2
      exact ⟨_, .app a1 b1,
        .appDF (a1.hasType hΓ l1) (r1.hasType hΓ l2)
          (b1.hasType hΓ l3) (r2.hasType hΓ l4) a2 b2⟩
    | delta h =>
      have H' : NormalEqN true _ Γ (.app f a) _ := hs ▸ NormalEqN.appDF l1 l2 l3 l4 l5 l6
      exact NormalEqN.fullStep_rigidRule
        (fun Γ ls args rhs => PrefixUnfold env univs recursorData Γ _ ls args rhs)
        (fun h => .delta h) (fun hΓ h => PrefixUnfold.defeq henv hΓ h)
        (fun hΓ h hls hw hargs hT => by
          obtain ⟨rhs₁, hr₁, hn₁⟩ := PrefixUnfold.congr_normal hΓ h hargs
          obtain ⟨rhs₂, hr₂, hu⟩ := PrefixUnfold.congr_levels henv hΓ hr₁ hw hls
            (eqUpToLevels_forall₂_rfl hΓ hT)
          have ht₁ := (Exists.choose_spec (PrefixUnfold.defeq henv hΓ hr₁)).hasType.2
          exact ⟨rhs₂, hr₂, ((NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hu) ht₁).symm hΓ).trans
            hΓ (hn₁.symm hΓ)⟩)
        (fun m hm => ihn m (by omega)) hΓ H' h
    | quotDelta h =>
      have H' : NormalEqN true _ Γ (.app f a) _ := hs ▸ NormalEqN.appDF l1 l2 l3 l4 l5 l6
      exact NormalEqN.fullStep_rigidRule
        (fun Γ ls args rhs => QuotPrefixUnfold env univs Γ ls args rhs)
        (fun h => .quotDelta h) (fun hΓ h => QuotPrefixUnfold.defeq henv hΓ h)
        (fun hΓ h hls hw hargs hT => by
          obtain ⟨rhs₁, hr₁, hn₁⟩ := QuotPrefixUnfold.congr_normal hΓ h hargs
          obtain ⟨rhs₂, hr₂, hu⟩ := QuotPrefixUnfold.congr_levels henv hΓ hr₁ hw hls
            (eqUpToLevels_forall₂_rfl hΓ hT)
          have ht₁ := (Exists.choose_spec (QuotPrefixUnfold.defeq henv hΓ hr₁)).hasType.2
          exact ⟨rhs₂, hr₂, ((NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hu) ht₁).symm hΓ).trans
            hΓ (hn₁.symm hΓ)⟩)
        (fun m hm => ihn m (by omega)) hΓ H' h
    | proj => cases hs
    | projIota => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @projDF _ family index major resultType _ _ major' lproj lMajor =>
    generalize hs : VExpr.proj family index major' = source at R
    cases R with
    | core h =>
      cases hs
      exact (NormalEqN.projDF lproj lMajor).normalEq.parRed hΓ h
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.projDF lproj lMajor).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.projDF lproj lMajor).normalEq.fullStep_funEta hΓ hfun
    | proj rMajor =>
      cases hs
      obtain ⟨_, majorRed, majorNormal⟩ := ihn _ (by omega) hΓ lMajor rMajor
      have reducedAtLeft := majorRed.proj.hasType hΓ lproj
      exact ⟨_, majorRed.proj, .projDF reducedAtLeft majorNormal⟩
    | delta h => exact False.elim (mkApps_ne_proj (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (mkApps_ne_proj (by intros; intro h; cases h) _ hs.symm)
    | projIota hl hproj hget hfield =>
      cases hs
      exact NormalEqN.fullStep_projIota hΓ lproj lMajor hl hproj hget hfield
    | app => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @elimDF _ block owner levels levels' A _ h heq =>
    generalize hs : VExpr.elim block owner levels' = source at R
    cases R with
    | core r =>
      cases hs
      exact (NormalEqN.elimDF h heq).normalEq.parRed hΓ r
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.elimDF h heq).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.elimDF h heq).normalEq.fullStep_funEta hΓ hfun
    | delta h => exact False.elim (mkApps_ne_elim (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (mkApps_ne_elim (by intros; intro h; cases h) _ hs.symm)
    | proj => cases hs
    | projIota => cases hs
    | app => cases hs
    | lam => cases hs
    | forallE => cases hs
  | @constDF c ci ls ls' _ _ hc hl hr hlen heq =>
    generalize hs : VExpr.const c ls' = source at R
    cases R with
    | core r =>
      cases hs
      exact (NormalEqN.constDF hc hl hr hlen heq).normalEq.parRed hΓ r
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.constDF hc hl hr hlen heq).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.constDF hc hl hr hlen heq).normalEq.fullStep_funEta hΓ hfun
    | delta h =>
      obtain ⟨rfl, rfl, rfl⟩ := const_eq_mkApps hs
      exact NormalEq.fullStep_delta_levels hΓ h hl
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip heq)) .nil
    | quotDelta h =>
      obtain ⟨rfl, rfl, rfl⟩ := const_eq_mkApps hs
      exact NormalEq.fullStep_quotDelta_levels hΓ h hl
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip heq)) .nil
    | proj => cases hs
    | projIota => cases hs
    | app => cases hs
    | lam => cases hs
    | forallE => cases hs
  | etaL ht he =>
    have ⟨⟨_, hA⟩, _, _⟩ := (ht.isType henv hΓ).choose_spec.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨_, hr, hn⟩ := ihn _ (by omega) hΓ' he (.app (R.weakN .one) .rfl)
    exact ⟨_, .lam .rfl hr, .etaL (R.hasType hΓ ht) hn⟩
  | etaBoth hl hr' hb =>
    have ⟨⟨_, hA⟩, _, _⟩ := (hl.isType henv hΓ).choose_spec.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨_, hr, hn⟩ := ihn _ (by omega) hΓ' hb (.app (R.weakN .one) .rfl)
    exact ⟨_, (ReflTransGen.tail .rfl (.funEta hl)).trans (FullReduction.lam .rfl hr),
      .etaL (R.hasType hΓ hr') hn⟩
  | @etaR _ e A B _ body ht he =>
    generalize hs : VExpr.lam A body = source at R
    cases R with
    | core r =>
      cases hs
      exact (NormalEqN.etaR ht he).normalEq.parRed hΓ r
    | structEta h1 h2 h3 h4 h5 =>
      cases hs
      exact (NormalEqN.etaR ht he).normalEq.fullStep_structEta hΓ h1 h2 h3 h4 h5
    | funEta hfun =>
      cases hs
      exact (NormalEqN.etaR ht he).normalEq.fullStep_funEta hΓ hfun
    | lam rd rb =>
      cases hs
      obtain ⟨⟨_, hA⟩, _, _⟩ := (ht.isType henv hΓ).choose_spec.forallE_inv henv
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      obtain ⟨out, hr, hn⟩ := ihn _ (by omega) hΓ' he rb
      exact ⟨_, (ReflTransGen.tail .rfl (.funEta ht)).trans (FullReduction.lam .rfl hr),
        .lamDF hA (rd.defeq hΓ hA) hn⟩
    | delta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | quotDelta h => exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hs.symm)
    | proj => cases hs
    | projIota => cases hs
    | app => cases hs
    | forallE => cases hs

theorem NormalEq.fullStep (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (R : FullStep Γ right result) :
    ∃ output, FullReduction Γ left output ∧ NormalEq Γ output result :=
  let ⟨n, H⟩ := H; NormalEqN.fullStep n hΓ H R

theorem NormalEq.fullReduction (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ left right) (R : FullReduction Γ right result) :
    ∃ output, FullReduction Γ left output ∧ NormalEq Γ output result := by
  induction R with
  | rfl => exact ⟨_, .rfl, H⟩
  | tail _ step ih =>
    obtain ⟨mid, hmid, heq⟩ := ih
    obtain ⟨out, hout, heq'⟩ := heq.fullStep hΓ step
    exact ⟨out, hmid.trans hout, heq'⟩

/-- Every installed equation joins in the full presentation at each scoped
universe packing. The terminal comparison permits proof irrelevance: quotient
reconstruction can return a generated proof selector that is normally equal
to the original field without a primitive computation rule for that selector. -/
class FullEquationCoverage : Prop where
  equations : OnCtx Γ (env.IsType univs) → env.defeqs equation →
    (∀ level ∈ levels, level.WF univs) → levels.length = equation.uvars →
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right

end Lean4Lean.VEnv
