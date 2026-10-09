import Lean4Lean.Theory.Typing.HeadInjectivity.Model.QuotRule
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjSound
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Definitions

/-! # Soundness of the glued observation model

`theorem sound`: for a strong derivation `Γ ⊢ t ≡ t' : T` of an environment `E ≤ env` whose
rules, projection entries and eliminator rules are valid in the model of `env` (`RuleValid`,
`ProjValid`, `ElimsValid`; bundled as `EnvValid`), and every pair of related
anchors `σ ≡ σ'` from `Γ` into a well-formed target context `Δ` with observation sets `S`
typed for both anchors:

* every observation of `t` under `(σ, S)` is subsumed by one of `t'` under `(σ', S)`, and
  conversely (`Ob.Sub`, i.e. `Obs t ⊆ ↑Obs t'`);
* every observation of `t` (under `σ`) and of `t'` (under `σ'`) is typed at observations of
  `T` (the typing invariant, proved simultaneously, with the semantic typing derivations
  `HTS` of both sides).

Relating two anchors (rather than one) is what lets the `beta` case change the
representative of a key class: the key's representative and the actual argument are only
definitionally equal.

The cases: `appDF` uses the typing invariant of the
function to identify the domain class of its observations (`app_typed`, `Obs.piDom_mem`);
`lamDF`/`forallEDF` extend the anchors by a representative of the key class; `beta` uses
compactness, monotonicity and the substitution lemma; `eta` uses the typing invariant of
`e : Pi A B` (its observations are `app` observations with typed keys) and key enlargement
(`≼`); `proofIrrel` uses `TypedOb.not_prop`; `defeqDF` transfers typing along the
inclusions given by the type equality; `sortDF`/`constDF` see levels only through
`VLevel.eval`, and at a defined constant on level invariance of the value (`Obs.lvEq`);
`extra` is the validity of the rule (`RuleValid`: `RuleValid.delta` for delta rules of
definitions, using `DeltaRules`, `RuleValid.quot` for the quotient rule, and the recursor rules
of `Model/RecursorRule.lean` and `Model/RestoredRecursorRule.lean`); `elimIota` is the
validity of the generic case equation (`ElimValid`). The projection rules (`projDF`,
`projIota`, `structEta`, `unitLike`) are sound for entries valid in the model (`ProjValid`,
`Model/ProjSound.lean`). Validity of every environment of the declaration history is proved
in `Model/EnvValid.lean`. -/

namespace Lean4Lean
namespace VEnv

namespace Model


variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Typing helpers -/

theorem TypedElCls.eq_of_mem (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    c = ElCls env U Δ (TyCls env U Δ X₀) y :=
  let ⟨_, _, _, h⟩ := hc.mem henv hΔ hy; h

theorem imax_eval_zero {a b : Nat} (h : Lean.Nat.imax a b = 0) : b = 0 := by
  unfold Lean.Nat.imax at h
  split at h
  · assumption
  · rename_i hb
    exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hb) (Nat.le_max_right a b)))

/-- Observations typed at a Pi type are `app` observations. -/
theorem typed_pi_app (H : TypedOb env U Δ cv o τs) (hτ : ∀ τ ∈ τs, Obs' σ S (.forallE A B) τ) :
    ∃ D c K p, o = .app D c K p := by
  cases H with
  | app => exact ⟨_, _, _, _, rfl⟩
  | sort h | piDom h | piDomOb h | piCod h | piCodOb h | rigid h | rigidArg h | rigidArgOb h
    | fieldTy h | fieldDom h | fieldOb _ _ _ h => nomatch hτ _ h
  | ctorHead h | ctorArg h | ctorArgOb h =>
    obtain ⟨_, _, _, _, h, _⟩ := h; nomatch hτ _ h

/-- Enlarging the keys of a typed `app` observation by typed keys keeps it typed. -/
theorem TypedOb.app_enlarge (H : TypedOb env U Δ cv (.app D c K₁ p) τs) (hKK : Covers K K₁)
    (hd : ∀ x ∈ τd, Ob.piDomOb x ∈ τs) (hk : ∀ k ∈ K, TypedOb env U Δ c k τd)
    (hbK : Backed (· ∈ K)) :
    TypedOb env U Δ cv (.app D c K p) τs := by
  cases H with
  | app hD _ _ _ hc hC hcod hp =>
    exact .app hD hd hk hbK hc hC
      (fun x hx => let ⟨K₀, h1, h2⟩ := hcod x hx; ⟨K₀, h1, hKK.trans h2⟩) hp

/-- The `app` observations of a lambda are typed at its Pi type. -/
theorem lam_typed (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (hA : env.HasType U Γ A (.sort u))
    (ht : env.HasType U (A :: Γ) t B)
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c)
    (hK : ∀ k ∈ K, TypedAt env U Δ c σ S A k) (hbK : Backed (listSet K)) (hy : c y)
    (hp : TypedAt env U Δ (vcls env U Δ (σ.cons y) t B) (σ.cons y) (S.cons (listSet K)) B p) :
    TypedAt env U Δ (vcls env U Δ σ (.lam A t) (.forallE A B)) σ S (.forallE A B)
      (.app (TyCls env U Δ (A.subst σ)) c K p) := by
  obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK
  obtain ⟨τc, hτc, hpc⟩ := hp
  obtain ⟨τs, h1, h2⟩ := pi_list hc hy hτk hkk hbK hτc
  refine ⟨τs, h1, h2 _ _ ?_⟩
  rw [vcls_beta henv hΔ W hA ht hc hy]; exact hpc

/-- The observations of an application are typed at the instantiated codomain, given the
typing invariant of the function (which identifies the domain class) and soundness for
the codomain. -/
theorem app_typed (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hB : env.HasType U (A::Γ) B (.sort v))
    (ihB : SoundAt env U Δ (A::Γ) B B (.sort v)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hfT : env.HasType U Γ f (.forallE A B))
    (ha0 : env.HasType U Γ a A)
    (hf : ∀ o, Obs' σ S f o →
      TypedAt env U Δ (vcls env U Δ σ f (.forallE A B)) σ S (.forallE A B) o)
    (ho : Obs' σ S (.app f a) o) :
    TypedAt env U Δ (vcls env U Δ σ (.app f a) (B.inst a)) σ S (B.inst a) o := by
  have ha : env.HasType U Δ (a.subst σ) (A.subst σ) := ha0.substDF henv W.wf hΔ W
  obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 ho
  obtain ⟨τs, hτs, hty⟩ := hf _ hfo
  cases hty with
  | @app _ _ _ _ _ τc _ C _ hD _ _ _ _ hC hcod hoty =>
    have eD := Obs.piDom_mem (hτs _ hD); subst eD; subst hc
    have hca := TypedElCls.of_hasType ha
    have eC : C = TyCls env U Δ (B.subst (σ.cons (a.subst σ))) := by
      obtain ⟨-, z, hz, rfl⟩ := Obs.piCod_mem (hτs _ hC)
      have W' : Ctx.SubstEq env U Δ (σ.cons z) (σ.cons (a.subst σ)) (A :: Γ) :=
        .cons W hA (hca.defeq henv hΔ hz ElCls.self)
      exact TyCls.eq_of_defeq (hB.substDF henv W'.wf hΔ W')
    subst eC
    rw [← vcls_app henv hΔ W hfT ha0] at hoty
    have : ∀ x ∈ τc, ∃ x', Obs' σ S (B.inst a) x' ∧ x' ≼ x := by
      intro x hx
      obtain ⟨K₀, hm, hKK₀⟩ := hcod x hx
      obtain ⟨_, ⟨τk, hτk, hkk⟩, y, hy, hxB⟩ := Obs.piCodOb_mem (hτs _ hm)
      have hay : env.IsDefEq U Δ (a.subst σ) y (A.subst σ) := ElCls.collapse henv hΔ ha .self hy
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons (a.subst σ)) (A::Γ) :=
        .cons W hA hay.symm
      have tvK : ∀ k ∈ K₀, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (a.subst σ))
          σ S A k := fun k hk => ⟨τk, hτk, hkk k hk⟩
      have hbK₀ := Obs.piCodOb_backed (hτs _ hm)
      obtain ⟨x₁, hx₁, l₁⟩ := (ihB _ _ _ W' (tv.cons_cls henv hΔ hca hy hbK₀ tvK)
        (tv.cons_cls henv hΔ hca ElCls.self hbK₀ tvK)).1 x hxB
      obtain ⟨x₂, hx₂, l₂⟩ := hx₁.mono_le (S' := S.cons (Obs' σ S a)) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k, hk, l⟩ := hKK₀ o h
          obtain ⟨k', hk', l'⟩ := hcov k hk
          exact ⟨k', hK' k' hk', l'.trans l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨x₂, Obs.inst_iff.2 hx₂, l₂.trans l₁⟩
    obtain ⟨τc', h1, h2⟩ := exists_list_cover this
    exact ⟨τc', h1, hoty.strengthen h2⟩

/-! ## Soundness -/

/-- **Validity of a rule**: the `extra` case of
soundness for `df` in the model of `env`, given the soundness and semantic typing of its typing
premises. -/
def RuleValid (env : VEnv) (df : VDefEq) : Prop :=
  ∀ (U : Nat) (Δ Γ : List VExpr) (ls : List VLevel) (u : VLevel), OnCtx Δ (env.IsType U) →
    (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    env.IsDefEqStrong U [] (df.type.instL ls) (df.type.instL ls) (.sort u) →
    SoundAt env U Δ [] (df.type.instL ls) (df.type.instL ls) (.sort u) ∧
      HTS env U Δ [] (df.type.instL ls) (.sort u) →
    env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls) →
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)


section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Key typing transfers from `A` under `σ` to `A` under `σ'` along `A ≡ A'`. -/
theorem keys_transfer {K : List Ob} (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S)
    (hK : ∀ k ∈ K, TypedAt env U Δ cv σ S A k) :
    (∀ k ∈ K, TypedAt env U Δ cv σ' S A' k) ∧ (∀ k ∈ K, TypedAt env U Δ cv σ' S A k) := by
  have W' := SubstEq.right henv hΔ W
  have h1 := (ih σ σ' S W tv tv').1
  have h2 := (ih σ' σ' S W' tv' tv').2.1
  exact ⟨fun k hk => (hK k hk).mono_le h1, fun k hk => ((hK k hk).mono_le h1).mono_le h2⟩

/-- Key typing transfers back from `A'` under `σ'` to `A` under `σ` and `σ'`. -/
theorem keys_transfer_symm {K : List Ob} (ih : SoundAt env U Δ Γ A A' T) (W : Ctx.SubstEq env U Δ σ σ' Γ)
    (tv : TV env U Δ Γ σ S) (tv' : TV env U Δ Γ σ' S)
    (hK : ∀ k ∈ K, TypedAt env U Δ cv σ' S A' k) :
    (∀ k ∈ K, TypedAt env U Δ cv σ S A k) ∧ (∀ k ∈ K, TypedAt env U Δ cv σ' S A k) := by
  have W' := SubstEq.right henv hΔ W
  have h1 := (ih σ σ' S W tv tv').2.1
  have h2 := (ih σ' σ' S W' tv' tv').2.1
  exact ⟨fun k hk => (hK k hk).mono_le h1, fun k hk => (hK k hk).mono_le h2⟩

omit henv hΔ in
theorem sound_bvar (hL : Lookup Γ i A) : SoundAt env U Δ Γ (.bvar i) (.bvar i) A := by
  intro σ σ' S W tv tv'
  exact ⟨.of_imp fun o h => .bvar (Obs.bvar_iff.1 h), .of_imp fun o h => .bvar (Obs.bvar_iff.1 h),
    fun o h => tv.2 _ _ hL o (Obs.bvar_iff.1 h), fun o h => tv'.2 _ _ hL o (Obs.bvar_iff.1 h)⟩

theorem sound_appDF (hA : env.IsDefEqStrong U Γ A A (.sort u))
    (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v)) (hf : env.IsDefEqStrong U Γ f f' (.forallE A B))
    (hBB : env.IsDefEqStrong U Γ (B.inst a) (B.inst a') (.sort v))
    (ha : env.IsDefEqStrong U Γ a a' A) (ihB : SoundAt env U Δ (A::Γ) B B (.sort v))
    (ihf : SoundAt env U Δ Γ f f' (.forallE A B)) (iha : SoundAt env U Δ Γ a a' A)
    (ihBB : SoundAt env U Δ Γ (B.inst a) (B.inst a') (.sort v)) :
    SoundAt env U Δ Γ (.app f a) (.app f' a') (B.inst a) := by
  intro σ σ' S W tv tv'
  have W'' := SubstEq.right henv hΔ W
  have hΓ := W.wf
  have haa : env.IsDefEq U Δ (a.subst σ) (a'.subst σ') (A.subst σ) :=
    ha.defeq.substDF henv hΓ hΔ W
  have hAA : env.IsDefEq U Δ (A.subst σ) (A.subst σ') (.sort u) :=
    hA.defeq.substDF henv hΓ hΔ W
  have IHf := ihf σ σ' S W tv tv'
  have IHa := iha σ σ' S W tv tv'
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 h
    obtain ⟨τs, hτs, hty⟩ := IHf.2.2.1 _ hfo
    cases hty with
    | app hD =>
      have eD := Obs.piDom_mem (hτs _ hD); subst eD
      obtain ⟨o₁, ho₁, l₁⟩ := IHf.1 _ hfo
      obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.app_inv
      obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHa.1 k (hK' k hk)
      refine ⟨y, .app ho₁ (hc.trans (ElCls.eq_of_defeq .self haa)) hK1
        (Covers.trans hK2 (hcov.trans hKK₀)), ly⟩
  · obtain ⟨D, c, K, K', hfo, hc, hK', hcov⟩ := Obs.app_iff.1 h
    obtain ⟨τs, hτs, hty⟩ := IHf.2.2.2 _ hfo
    cases hty with
    | app hD =>
      have eD := Obs.piDom_mem (hτs _ hD); subst eD
      obtain ⟨o₁, ho₁, l₁⟩ := IHf.2.1 _ hfo
      obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.app_inv
      obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHa.2.1 k (hK' k hk)
      refine ⟨y, .app ho₁ (hc.trans (ElCls.eq_of_defeq (.inr (.single (.inl ⟨_, hAA.symm⟩))) haa).symm)
        hK1 (Covers.trans hK2 (hcov.trans hKK₀)), ly⟩
  · exact app_typed henv hΔ hA.defeq hB.defeq ihB W.left tv hf.defeq.hasType.1
      ha.defeq.hasType.1 IHf.2.2.1 h
  · have := app_typed henv hΔ hA.defeq hB.defeq ihB W'' tv' hf.defeq.hasType.2
      ha.defeq.hasType.2 IHf.2.2.2 h
    rw [← vcls_conv henv hΔ W'' hBB.defeq] at this
    exact this.mono_le (ihBB σ' σ' S W'' tv' tv').2.1

theorem sound_forallEDF (hAA : env.IsDefEqStrong U Γ A A' (.sort u))
    (hBB : env.IsDefEqStrong U (A::Γ) B B' (.sort v)) (ihA : SoundAt env U Δ Γ A A' (.sort u))
    (ihB : SoundAt env U Δ (A::Γ) B B' (.sort v)) :
    SoundAt env U Δ Γ (.forallE A B) (.forallE A' B') (.sort (.imax u v)) := by
  intro σ σ' S W tv tv'
  have hΓ := W.wf
  have hA := hAA.defeq.hasType.1
  have eD : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A'.subst σ') :=
    TyCls.eq_of_defeq (hAA.defeq.substDF henv hΓ hΔ W)
  have eDA : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
    TyCls.eq_of_defeq (hA.substDF henv hΓ hΔ W)
  have IHA := ihA σ σ' S W tv tv'
  have imax0 : ∀ ns, (VLevel.imax u v).eval ns = 0 → v.eval ns = 0 := by
    intro ns h; exact imax_eval_zero h
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact ⟨_, by rw [eD]; exact .piDom, .refl⟩
    · obtain ⟨p', hp', l⟩ := IHA.1 p hp; exact ⟨_, .piDomOb hp', .piDomOb l⟩
    · have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      have eC := TyCls.eq_of_defeq (hBB.defeq.substDF henv W'.wf hΔ W')
      exact ⟨_, by rw [eC]; exact .piCod (hc.congr_D eD) hy, .refl⟩
    · have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eDA) hy hbK hK2)).1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      exact ⟨_, .piCodOb (hc.congr_D eD) h1 h2 hbK hy hp', .piCodOb_of_covers Covers.refl l⟩
  · rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact ⟨_, by rw [← eD]; exact .piDom, .refl⟩
    · obtain ⟨p', hp', l⟩ := IHA.2.1 p hp; exact ⟨_, .piDomOb hp', .piDomOb l⟩
    · have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      have eC := TyCls.eq_of_defeq (hBB.defeq.substDF henv W'.wf hΔ W')
      exact ⟨_, by rw [← eC]; exact .piCod hc' hy, .refl⟩
    · have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eDA) hy hbK hK2)).2.1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      exact ⟨_, .piCodOb hc' h1 h2 hbK hy hp', .piCodOb_of_covers Covers.refl l⟩
  · refine typedAt_sort_iff.2 ?_
    rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact .piDom (List.mem_singleton_self _)
    · exact .piDomOb (List.mem_singleton_self _)
    · exact .piCod (List.mem_singleton_self _)
    · have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨_, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      have := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eDA) hy hbK hK2)).2.2.1 p hp
      exact .piCodOb (List.mem_singleton_self _) (typedAt_sort_iff.1 this) imax0
  · refine typedAt_sort_iff.2 ?_
    rcases Obs.forallE_iff.1 h with rfl | ⟨p, rfl, hp⟩ | ⟨c, y, rfl, hc, hy⟩ |
      ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩
    · exact .piDom (List.mem_singleton_self _)
    · exact .piDomOb (List.mem_singleton_self _)
    · exact .piCod (List.mem_singleton_self _)
    · have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      have := (ihB _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eDA) hy hbK hK2)).2.2.2 p hp
      exact .piCodOb (List.mem_singleton_self _) (typedAt_sort_iff.1 this) imax0

end

/-- Delta rules are valid. -/
theorem RuleValid.delta (henv : env.Ordered) (hdr : env.DeltaRules)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hdf : env.defeqs df)
    (hlhs : df.lhs = .const n ls₀) : RuleValid env df := by
  intro U Δ Γ ls u hΔ hlw hlen _ _ _ ihL _ ihR
  replace ihR := ihR.1
  intro σ σ' S W tv tv'
  obtain ⟨rfl, hci⟩ := hdr.const df hdf n ls₀ hlhs
  have elhs : df.lhs.instL ls = .const n ls := by
    rw [hlhs]; simp only [VExpr.instL, VLevel.inst_map_id hlen]
  rw [elhs]
  have hrcl : (df.rhs.instL ls).ClosedN := ((henv.closed.2 hdf).2.1).instL
  have htcl : (df.type.instL ls).ClosedN := ((henv.closed.2 hdf).1.2).instL
  have IHR := ihR σ' σ' S (SubstEq.right henv hΔ W) tv' tv'
  have notRigid : ¬ env.Rigid n := fun hrig => hrig df hdf _ (by rw [hlhs]; rfl)
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, IHR.2.2.1⟩
  · rcases Obs.const_iff.1 h with ⟨_, _, _, _, _, hrig, _⟩ |
      ⟨df', ci', τs, hdf', hlhs', hci', hτ, hty, hv⟩ | ⟨_, _, _, _, _, hc, _⟩ |
      ⟨df', doms, lsP, lead, ctor, lsC, ms, fs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf',
        hl', _⟩ | ⟨fam, info, _, _, _, _, _, hpi, hcn, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrig, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, hrig, _⟩
    · exact absurd hrig notRigid
    · cases hdr.excl df df' hdf hdf' n _ _ hlhs (by rw [hlhs']; rfl)
      exact ⟨o, (Obs.closed_iff_id hrcl).2 hv, .refl⟩
    · exact absurd (hctor n hc) notRigid
    · cases hdr.excl df df' hdf hdf' n _ lsP hlhs (by
        rw [hl']; exact VExpr.stripLams_wrapLams_mkApps_head)
      rw [hlhs] at hl'
      exact absurd hl'.symm VExpr.wrapLams_mkApps_snoc_ne_const
    · exact absurd (hpctor n ⟨fam, info, hpi, hcn⟩) notRigid
    · exact absurd hrig notRigid
    · exact absurd hrig notRigid
  · obtain ⟨τs, hτ, hty⟩ := IHR.2.2.1 o h
    have heq : env.IsDefEq U Γ (.const n ls) (df.rhs.instL ls) (df.type.instL ls) := by
      have := IsDefEq.extra (Γ := Γ) hdf hlw hlen; rwa [elhs] at this
    rw [← vcls_defeq henv hΔ (SubstEq.right henv hΔ W) heq,
      vcls_closed (e := .const _ _) trivial htcl] at hty
    exact ⟨o, .delta hdf (by rw [hlhs]) hci (ci := ⟨df.uvars, df.type⟩)
      (fun τ hτ' => (Obs.closed_iff_id htcl).1 (hτ τ hτ')) hty
      ((Obs.closed_iff_id hrcl).1 h), .refl⟩
  · obtain ⟨τs, hτ, hty⟩ := h.const_typed hci
    rw [vcls_closed (e := .const _ _) trivial htcl]
    exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id htcl).2 (hτ τ hτ'), hty⟩

/-- The quotient rule is valid, in an environment whose rules are delta rules or the quotient
rule. -/
theorem RuleValid.quot (henv : env.Ordered) (hq : QuotConsts env)
    (hqu : ∀ df' ls', env.defeqs df' →
      df'.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift ls' → df' = quotDefEq)
    (hdr : env.DeltaRules)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hcres : ∀ c, IsInstalledCtor env c → env.CtorResultRigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnpQ : ∀ info, ¬ env.projections ``Quot info) (hnpM : ¬ IsProjCtor env ``Quot.mk)
    (hdf : env.defeqs quotDefEq) : RuleValid env quotDefEq := by
  intro U Δ Γ ls u hΔ hlw hlen _ _ _ ihL _ ihR
  have hcisN : IsInstalledCtor env ``Quot.mk := ⟨quotDefEq, hdf, quotDefEq_ctorMajor⟩
  have hcis : IsCtor env ``Quot.mk := .inl hcisN
  have hrigQ : env.Rigid ``Quot := by
    obtain ⟨ci, hci, F, ls', hF, -, hrig⟩ := hcres _ hcisN
    cases hq.2.1.symm.trans hci
    cases hF; exact hrig
  have hcl := henv.closed.2 hdf
  exact sound_pat henv hΔ hdf quotDefEq_lhs quotDefEq_rhs quot_cov
    (VLevel.inst_map_id hlen) hcl.1.1 hcl.2.1 hq.2.2 quotLiftConst_type rfl rfl hrigQ
    ⟨_, _, hq.2.1, rfl⟩ hcis (.inl ⟨hnpQ, hnpM⟩)
    (hctor _ hcis) hctor hpctor hdr (quot_uniq hqu)
    (fun keys hkl hobs => ⟨hqu,
      quot_pf hlw (quot_C_level hq hrigQ hkl hobs)⟩)
    ihL ihR (.extra hdf hlw hlen)


/-- **Validity of a generic case equation** of the schema registered at `b`, for the owner
`owner`: the `elimIota` case of soundness in the model of `env`. -/
def ElimValid (env : VEnv) {schema : InductiveSignature.CaseSchema}
    (owner : Fin schema.signature.families.size) (df : VDefEq) : Prop :=
  ∀ (U : Nat) (Δ Γ : List VExpr) (levels : List VLevel) (target tl : VLevel),
    OnCtx Δ (env.IsType U) → InductiveSignature.CaseSchema.RuleClosed df →
    schema.Permission U owner levels target →
    env.IsDefEqStrong U Γ (df.type.instL (target :: levels)) (df.type.instL (target :: levels))
      (.sort tl) →
    SoundAt env U Δ Γ (df.type.instL (target :: levels)) (df.type.instL (target :: levels))
      (.sort tl) ∧ HTS env U Δ Γ (df.type.instL (target :: levels)) (.sort tl) →
    env.IsDefEqStrong U Γ (df.lhs.instL (target :: levels)) (df.lhs.instL (target :: levels))
      (df.type.instL (target :: levels)) →
    SoundAt env U Δ Γ (df.lhs.instL (target :: levels)) (df.lhs.instL (target :: levels))
      (df.type.instL (target :: levels)) ∧
      HTS env U Δ Γ (df.lhs.instL (target :: levels)) (df.type.instL (target :: levels)) →
    env.IsDefEqStrong U Γ (df.rhs.instL (target :: levels)) (df.rhs.instL (target :: levels))
      (df.type.instL (target :: levels)) →
    SoundAt env U Δ Γ (df.rhs.instL (target :: levels)) (df.rhs.instL (target :: levels))
      (df.type.instL (target :: levels)) ∧
      HTS env U Δ Γ (df.rhs.instL (target :: levels)) (df.type.instL (target :: levels)) →
    SoundAt env U Δ Γ (df.lhs.instL (target :: levels)) (df.rhs.instL (target :: levels))
      (df.type.instL (target :: levels))

/-- Validity of the eliminator rules of an environment `E` in the model of `env`, with
uniqueness of the registered schemas of `env`. -/
structure ElimsValid (env E : VEnv) : Prop where
  uniq : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s'
  valid : ∀ b (schema : InductiveSignature.CaseSchema) owner rules df,
    E.eliminators b schema → schema.genericEquations b owner = some rules → df ∈ rules →
    ElimValid env owner df

theorem ElimsValid.mono {env E E' : VEnv} (H : ElimsValid env E) (h : E' ≤ E) :
    ElimsValid env E' :=
  ⟨H.uniq, fun b schema owner rules df hb => H.valid b schema owner rules df (h.eliminators hb)⟩

theorem ElimsValid.of_elims {env E E' : VEnv} (H : ElimsValid env E)
    (h : ∀ b s, E'.eliminators b s → E.eliminators b s) : ElimsValid env E' :=
  ⟨H.uniq, fun b schema owner rules df hb => H.valid b schema owner rules df (h _ _ hb)⟩

/-- Every observation of an eliminator passes its typing filter. -/
theorem Obs.elim_typed {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (h : Obs' σ S (.elim b owner.val ls) o) (hb : env.eliminators b schema)
    (ht : schema.genericType owner = some type) :
    TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (type.instL ls)) (.elim b owner.val ls))
      .id .empty (type.instL ls) o := by
  obtain ⟨schema', owner', _, _, _, _, _, _, _, _, _, _, type', τs, _, _, _, _, _, _, _, _, ei, rfl,
    hb', -, -, -, -, ht', hτ, hty, -⟩ := Obs.elim_iff.1 h
  cases hEu _ _ _ hb hb'
  cases Fin.ext ei
  cases ht.symm.trans ht'
  exact ⟨τs, hτ, hty⟩

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Soundness** of the observation model for the derivations of an environment `E ≤ env`
whose rules are valid in the model of `env`, carrying semantic typing derivations. -/
theorem sound {E : VEnv} (hle : E ≤ env) (hvalid : ∀ df, E.defeqs df → RuleValid env df)
    (hPV : ∀ n p, E.projections n p → ProjValid env n p) (hEV : ElimsValid env E)
    (H : E.IsDefEqStrong U Γ t t' T) :
    SoundAt env U Δ Γ t t' T ∧ HTS env U Δ Γ t T ∧ HTS env U Δ Γ t' T := by
  induction H with
  | bvar hL _ hA ihA =>
    replace hA := hA.mono hle
    exact ⟨sound_bvar hL, .bvar hL ⟨hA, ihA.1⟩, .bvar hL ⟨hA, ihA.1⟩⟩
  | symm _ ih => exact ⟨ih.1.symm henv hΔ, ih.2.2, ih.2.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans henv hΔ ih2.1, ih1.2.1, ih2.2.2⟩
  | @sortDF l l' _ _ _ h3 =>
    refine ⟨?_, .sort', .sort'⟩
    intro σ σ' S W tv tv'
    have e : l.eval = l'.eval := h3
    refine ⟨.of_imp fun o h => ?_, .of_imp fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · rw [Obs.sort_mem h, e]; exact .sort
    · rw [Obs.sort_mem h, ← e]; exact .sort
    · rw [Obs.sort_mem h]; exact typedAt_sort_iff.2 (.sort (List.mem_singleton_self _))
    · rw [Obs.sort_mem h, ← e]; exact typedAt_sort_iff.2 (.sort (List.mem_singleton_self _))
  | @constDF c ci ls ls' u Γ hci hlw hlw' hlen hls _ h7 h8 ih0 ih8 =>
    replace hci := hle.constants hci
    replace h7 := h7.mono hle
    replace h8 := h8.mono hle
    refine ⟨?_, .const hci hlw hlen ih0.2.1 ⟨h7.hasType.1, ih0.1.refl_l henv hΔ⟩,
      .conv (.const hci hlw' ((Lean4Lean.List.Forall₂.length_eq hls).symm.trans hlen) ih0.2.2
        ⟨h7.hasType.2, ih0.1.refl_r henv hΔ⟩) ⟨h8.symm, ih8.1.symm henv hΔ⟩⟩
    replace ih0 := ih0.1
    intro σ σ' S W tv tv'
    have IH0 := ih0 .id .id .empty .nil TV.empty TV.empty
    have hcl : ∀ ls, (ci.type.instL ls).ClosedN := fun _ => (henv.closedC hci).instL
    have hT : ∀ ci', env.constants c = some ci' →
        Ob.Sub (Obs' .id .empty (ci'.type.instL ls)) (Obs' .id .empty (ci'.type.instL ls')) :=
      fun ci' h => by cases hci.symm.trans h; exact IH0.1
    have hT' : ∀ ci', env.constants c = some ci' →
        Ob.Sub (Obs' .id .empty (ci'.type.instL ls')) (Obs' .id .empty (ci'.type.instL ls)) :=
      fun ci' h => by cases hci.symm.trans h; exact IH0.2.1
    refine ⟨fun o h => ⟨o, h.const_levels hT hlw hlw' hls, .refl⟩,
      fun o h => ⟨o, h.const_levels hT' hlw' hlw (forall₂_equiv_symm hls), .refl⟩,
      fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨τs, h1, h2⟩ := h.const_typed hci
      rw [vcls_closed (e := .const _ _) trivial (hcl ls)]
      exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id (hcl ls)).2 (h1 τ hτ'), h2⟩
    · obtain ⟨τs, h1, h2⟩ := (h.const_typed hci).mono_le IH0.2.1
      rw [vcls_closed (e := .const _ _) trivial (hcl ls),
        TyCls.eq_of_lvEq (LvEq.instL ci.type hlw hlw' hls)]
      exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id (hcl ls)).2 (h1 τ hτ'), h2⟩
  | elimDF hb htype hcl hperm hlw' hls _ h8 ih8 =>
    replace hb := hle.eliminators hb
    replace h8 := h8.mono hle
    have hlw := hperm.packedWF
    refine ⟨?_, .elim hb htype hcl hlw ih8.2.1 ⟨h8.hasType.1, ih8.1.refl_l henv hΔ⟩,
      .conv (.elim hb htype hcl hlw' ih8.2.2 ⟨h8.hasType.2, ih8.1.refl_r henv hΔ⟩)
        ⟨h8.symm, ih8.1.symm henv hΔ⟩⟩
    intro σ σ' S W tv tv'
    have IH := ih8.1 σ σ' S W tv tv'
    refine ⟨fun o h => ⟨o, Obs.elim_indep.1 (h.lvEq (.elim hlw hlw' hls)), .refl⟩,
      fun o h => ⟨o, Obs.elim_indep.1 (h.lvEq (.elim hlw' hlw (forall₂_equiv_symm hls))), .refl⟩,
      fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨τs, h1, h2⟩ := h.elim_typed hEV.uniq hb htype
      rw [vcls_closed (e := .elim _ _ _) trivial hcl.instL]
      exact ⟨τs, fun τ hτ' => (Obs.closed_iff_id hcl.instL).2 (h1 τ hτ'), h2⟩
    · obtain ⟨τs, h1, h2⟩ := h.elim_typed hEV.uniq hb htype
      rw [vcls_closed (e := .elim _ _ _) trivial hcl.instL,
        TyCls.eq_of_lvEq (LvEq.instL _ hlw hlw' hls)]
      obtain ⟨τs', h3, h4⟩ := TypedAt.mono_le (σ' := σ') (S' := S)
        ⟨τs, fun τ hτ' => (Obs.closed_iff_id hcl.instL).2 (h1 τ hτ'), h2⟩ (fun x hx => by
          obtain ⟨y, hy, l⟩ := IH.2.1 x hx
          exact ⟨y, (Obs.closed_iff_id hcl.instL).2 ((Obs.closed_iff_id hcl.instL).1 hy), l⟩)
      exact ⟨τs', h3, h4⟩
  | @appDF Γ A u B v f f' a a' _ _ hA hB hf ha hBB ihA ihB ihf iha ihBB =>
    replace hA := hA.mono hle
    replace hB := hB.mono hle
    replace hf := hf.mono hle
    replace ha := ha.mono hle
    replace hBB := hBB.mono hle
    exact ⟨sound_appDF henv hΔ hA hB hf hBB ha ihB.1 ihf.1 iha.1 ihBB.1,
      .app ⟨hA, ihA.1⟩ ⟨hB, ihB.1⟩ ihf.2.1 hf.defeq.hasType.1 iha.2.1
        ⟨ha.hasType.1, iha.1.refl_l henv hΔ⟩,
      .conv (.app ⟨hA, ihA.1⟩ ⟨hB, ihB.1⟩ ihf.2.2 hf.defeq.hasType.2 iha.2.2
        ⟨ha.hasType.2, iha.1.refl_r henv hΔ⟩)
        ⟨hBB.symm, ihBB.1.symm henv hΔ⟩⟩
  | projDF hp hls hlen hps hidx hF _ hFty h1 h2 hcl hg ihF ih1 ih2 =>
    exact sound_projDF henv hΔ (hle.projections hp) (hPV _ _ hp) hls hlen hps hidx hF
      (hFty.mono hle) (h1.mono hle) (h2.mono hle) hcl hg ⟨ihF.1, ihF.2.1⟩ ⟨ih1.1, ih1.2.2⟩
      ⟨ih2.1, ih2.2.2⟩
  | @lamDF Γ A A' u B v body body' h1 h2 hAA hB hB' hb hb' ihA ihB ihB' ihb ihb' =>
    replace hAA := hAA.mono hle
    replace hB := hB.mono hle
    replace hB' := hB'.mono hle
    replace hb := hb.mono hle
    replace hb' := hb'.mono hle
    refine ⟨?_, .lam ihA.2.1 ⟨hAA.hasType.1, ihA.1.refl_l henv hΔ⟩ ihb.2.1
        ⟨hb.hasType.1, ihb.1.refl_l henv hΔ⟩ ⟨hB, ihB.1⟩,
      .conv (.lam ihA.2.2 ⟨hAA.hasType.2, ihA.1.refl_r henv hΔ⟩ ihb'.2.2
        ⟨hb'.hasType.2, ihb'.1.refl_r henv hΔ⟩ ⟨hB', ihB'.1⟩)
        ⟨.forallEDF h1 h2 hAA.symm hB' hB,
          sound_forallEDF henv hΔ hAA.symm hB' (ihA.1.symm henv hΔ) ihB'.1⟩⟩
    replace ihA := ihA.1
    replace ihb := ihb.1
    intro σ σ' S W tv tv'
    have W'' := SubstEq.right henv hΔ W
    have hΓ := W.wf
    have hA := hAA.defeq.hasType.1
    have eD : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A'.subst σ') :=
      TyCls.eq_of_defeq (hAA.defeq.substDF henv hΓ hΔ W)
    have eD' : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
      TyCls.eq_of_defeq (hA.substDF henv hΓ hΔ W)
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihb _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eD') hy hbK hK2)).1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      refine ⟨_, ?_, Ob.Le.app' Covers.refl l⟩
      rw [eD]; exact .lam (hc.congr_D eD) h1 h2 hbK hy hp'
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      obtain ⟨p', hp', l⟩ := (ihb _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eD') hy hbK hK2)).2.1 p hp
      obtain ⟨τs', h1, h2⟩ := TypedAt.merge hK1
      refine ⟨_, ?_, Ob.Le.app' Covers.refl l⟩
      rw [← eD]; exact .lam hc' h1 h2 hbK hy hp'
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨_, hK2⟩ := keys_transfer henv hΔ ihA W tv tv' hKσ
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc.hasType henv hΔ hy)
      exact lam_typed henv hΔ W.left hA hb.defeq.hasType.1 hc hKσ hbK hy ((ihb _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv'.cons_cls henv hΔ (hc.congr_D eD') hy hbK hK2)).2.2.1 p hp)
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ c σ' S A' k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have ⟨hK1, hK2⟩ := keys_transfer_symm henv hΔ ihA W tv tv' hKσ'
      have hc' := hc.congr_D eD.symm
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons y) (A::Γ) :=
        .cons W hA (hc'.hasType henv hΔ hy)
      have hp' := (ihb _ _ _ W' (tv.cons_cls henv hΔ hc' hy hbK hK1) (tv'.cons_cls henv hΔ (hc'.congr_D eD') hy hbK hK2)).2.2.2 p hp
      have heqlam : env.IsDefEq U Γ (.lam A body') (.lam A' body') (.forallE A B) :=
        IsDefEq.lamDF hAA.defeq hb.defeq.hasType.2
      rw [← vcls_defeq henv hΔ W'' heqlam, ← eD, eD']
      exact lam_typed henv hΔ W'' hA hb.defeq.hasType.2 (hc'.congr_D eD') hK2 hbK hy hp'
  | @forallEDF Γ A A' u B B' v hu hv hAA hBB hBB' ihA ihB ihB' =>
    replace hAA := hAA.mono hle
    replace hBB := hBB.mono hle
    replace hBB' := hBB'.mono hle
    exact ⟨sound_forallEDF henv hΔ hAA hBB ihA.1 ihB.1,
      .forallE ihA.2.1 ⟨hAA.hasType.1, ihA.1.refl_l henv hΔ⟩ ihB.2.1
        ⟨hBB.hasType.1, ihB.1.refl_l henv hΔ⟩,
      .forallE ihA.2.2 ⟨hAA.hasType.2, ihA.1.refl_r henv hΔ⟩ ihB'.2.2
        ⟨hBB'.hasType.2, ihB'.1.refl_r henv hΔ⟩⟩
  | defeqDF _ hAB _ ihAB ihe =>
    replace hAB := hAB.mono hle
    refine ⟨?_, .conv ihe.2.1 ⟨hAB, ihAB.1⟩, .conv ihe.2.2 ⟨hAB, ihAB.1⟩⟩
    replace ihAB := ihAB.1
    replace ihe := ihe.1
    intro σ σ' S W tv tv'
    have IH := ihe σ σ' S W tv tv'
    refine ⟨IH.1, IH.2.1, fun o h => ?_, fun o h => ?_⟩
    · rw [← vcls_conv henv hΔ W.left hAB.defeq]
      exact (IH.2.2.1 o h).mono_le (ihAB σ σ S W.left tv tv).1
    · rw [← vcls_conv henv hΔ (SubstEq.right henv hΔ W) hAB.defeq]
      exact (IH.2.2.2 o h).mono_le (ihAB σ' σ' S (SubstEq.right henv hΔ W) tv' tv').1
  | @beta Γ A u B v e e' _ _ hA hB he he' _ _ ihA ihB ihe ihe' _ ihee' =>
    replace hA := hA.mono hle
    replace hB := hB.mono hle
    replace he := he.mono hle
    replace he' := he'.mono hle
    refine ⟨?_, .beta_lhs, ihee'.2.1⟩
    replace ihA := ihA.1
    replace ihB := ihB.1
    replace ihe := ihe.1
    replace ihe' := ihe'.1
    replace ihee' := ihee'.1
    intro σ σ' S W tv tv'
    have W'' := SubstEq.right henv hΔ W
    have hΓ := W.wf
    have hee : env.IsDefEq U Δ (e'.subst σ) (e'.subst σ') (A.subst σ) :=
      he'.defeq.substDF henv hΓ hΔ W
    have IHA := ihA σ σ' S W tv tv'
    have IHe' := ihe' σ σ' S W tv tv'
    have eA : TyCls env U Δ (A.subst σ) = TyCls env U Δ (A.subst σ') :=
      TyCls.eq_of_defeq (hA.defeq.substDF henv hΓ hΔ W)
    have hce := TypedElCls.of_hasType hee.hasType.1
    have ec : ElCls env U Δ (TyCls env U Δ (A.subst σ')) (e'.subst σ') =
        ElCls env U Δ (TyCls env U Δ (A.subst σ)) (e'.subst σ) := by
      rw [← eA]; exact (ElCls.eq_of_defeq .self hee).symm
    have hmem' : ElCls env U Δ (TyCls env U Δ (A.subst σ)) (e'.subst σ) (e'.subst σ') :=
      ElCls.mem_of_defeq hee
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨D, c, K, K', hlo, hc, hK', hcov⟩ := Obs.app_iff.1 h
      obtain ⟨c₁, K₁, y, τs, p, e₁, hc₁, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 hlo
      injection e₁ with eD ec eK eo
      subst eD ec eK eo hc
      have hKσ : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (e'.subst σ))
          σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (e'.subst σ))
          σ' S A k := fun k hk => (hKσ k hk).mono_le IHA.1
      have hy' : env.IsDefEq U Δ y (e'.subst σ') (A.subst σ) :=
        (ElCls.collapse henv hΔ hee.hasType.1 .self hy).symm.trans hee
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ'.cons (e'.subst σ')) (A::Γ) :=
        .cons W hA.defeq hy'
      obtain ⟨o₁, ho₁, l₁⟩ := (ihe _ _ _ W' (tv.cons_cls henv hΔ hce hy hbK hKσ)
        (tv'.cons_cls henv hΔ (hce.congr_D eA) hmem' hbK hKσ')).1 _ hp
      obtain ⟨o₂, ho₂, l₂⟩ := ho₁.mono_le (S' := S.cons (Obs' σ' S e')) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k, hk, l⟩ := hcov o h
          obtain ⟨k', hk', l'⟩ := IHe'.1 k (hK' k hk)
          exact ⟨k', hk', l'.trans l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨o₂, Obs.inst_iff.2 ho₂, l₂.trans l₁⟩
    · obtain ⟨K, hK, hbK, ho⟩ :=
        (Obs.inst_iff.1 h).compact0B fun o h => Obs.backed h tv'.1
      have hKσ' : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (e'.subst σ))
          σ' S A k := fun k hk => ec ▸ IHe'.2.2.2 k (hK k hk)
      have hKσ : ∀ k ∈ K, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (e'.subst σ))
          σ S A k := fun k hk => (hKσ' k hk).mono_le IHA.2.1
      have W' : Ctx.SubstEq env U Δ (σ.cons (e'.subst σ)) (σ'.cons (e'.subst σ')) (A::Γ) :=
        .cons W hA.defeq hee
      obtain ⟨o₁, ho₁, l₁⟩ := (ihe _ _ _ W' (tv.cons_cls henv hΔ hce ElCls.self hbK hKσ)
        (tv'.cons_cls henv hΔ (hce.congr_D eA) hmem' hbK hKσ')).2.1 o ho
      obtain ⟨τs, h1, h2⟩ := TypedAt.merge hKσ
      have hlam := Obs.lam (TypedElCls.of_hasType hee.hasType.1) h1 h2 hbK ElCls.self ho₁
      obtain ⟨K'', hK1, hK2⟩ := exists_list_cover fun k hk => IHe'.2.1 k (hK k hk)
      exact ⟨o₁, .app hlam rfl hK1 hK2, l₁⟩
    · refine app_typed henv hΔ hA.defeq hB.defeq ihB W.left tv
        (IsDefEq.lamDF hA.defeq he.defeq) he'.defeq (fun o h => ?_) h
      obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      have hKσ : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τs, hτ, hK k hk⟩
      have W' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons y) (A::Γ) :=
        .cons W.left hA.defeq (hc.hasType henv hΔ hy)
      exact lam_typed henv hΔ W.left hA.defeq he.defeq hc hKσ hbK hy
        ((ihe _ _ _ W' (tv.cons_cls henv hΔ hc hy hbK hKσ) (tv.cons_cls henv hΔ hc hy hbK hKσ)).2.2.1 p hp)
    · exact (ihee' σ' σ' S W'' tv' tv').2.2.1 o h
  | @eta Γ A u B v e h1 h2 hA hB hB' he he' hA' ihA ihB ihB' ihe ihe' ihA' =>
    replace hA := hA.mono hle
    replace hB := hB.mono hle
    replace hB' := hB'.mono hle
    replace he := he.mono hle
    replace he' := he'.mono hle
    replace hA' := hA'.mono hle
    have e0 : (B.liftN 1 1).inst (.bvar 0) = B := VExpr.inst_liftN_bvar B 0
    have hb0 : env.IsDefEqStrong U (A :: Γ) (.bvar 0) (.bvar 0) A.lift := .bvar .zero h1 hA'
    have hbody : HTS env U Δ (A :: Γ) (.app e.lift (.bvar 0)) B := by
      have := HTS.app ⟨hA', ihA'.1⟩ ⟨hB', ihB'.1⟩ ihe'.2.1 he'.defeq.hasType.1
        (.bvar .zero ⟨hA', ihA'.1⟩) ⟨hb0, sound_bvar .zero⟩
      rwa [e0] at this
    have hBB : env.IsDefEqStrong U (A :: Γ) ((B.liftN 1 1).inst (.bvar 0))
        ((B.liftN 1 1).inst (.bvar 0)) (.sort v) := by rw [e0]; exact hB
    have sbody : SD env U Δ (A :: Γ) (.app e.lift (.bvar 0)) (.app e.lift (.bvar 0)) B := by
      have d := IsDefEqStrong.appDF h1 h2 hA' hB' he' hb0 hBB
      have sd := sound_appDF henv hΔ hA' hB' he' hBB hb0 ihB'.1 ihe'.1
        (sound_bvar .zero) (by rw [e0]; exact ihB.1)
      rw [e0] at d sd
      exact ⟨d, sd⟩
    refine ⟨?_, .lam ihA.2.1 ⟨hA, ihA.1⟩ hbody sbody ⟨hB, ihB.1⟩, ihe.2.1⟩
    replace ihA := ihA.1
    replace ihe := ihe.1
    intro σ σ' S W tv tv'
    have hΓ := W.wf
    have IHe := ihe σ σ' S W tv tv'
    refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      obtain ⟨D₁, c₁, K₁, K₁', he₁, hc₁, hK₁', hcov₁⟩ := Obs.app_iff.1 hp
      have he₁' := Obs.lift_cons_iff.1 he₁
      obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ he₁'
      cases hty₁ with
      | app hD =>
        have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
        have ec : c₁ = c := hc₁.trans (TypedElCls.eq_of_mem henv hΔ hc hy).symm
        subst ec
        obtain ⟨o₂, ho₂, l₂⟩ := IHe.1 _ he₁'
        refine ⟨o₂, ho₂, l₂.trans (Ob.Le.app' ?_ .refl)⟩
        exact Covers.trans (Covers.of_subset fun k hk => Obs.bvar_iff.1 (hK₁' k hk)) hcov₁
    · obtain ⟨o₁, ho₁, l₁⟩ := IHe.2.1 o h
      obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ ho₁
      obtain ⟨D, c, K, p, rfl⟩ := typed_pi_app hty₁ hτs₁
      cases hty₁ with
      | app hD hd hk hbK hc =>
        have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
        have hτd : ∀ x ∈ _, Obs' σ S A x := fun x hx => Obs.piDomOb_mem (hτs₁ _ (hd x hx))
        obtain ⟨y, hy⟩ := hc.nonempty
        refine ⟨_, .lam hc hτd hk hbK hy ?_, l₁⟩
        refine .app (Obs.lift_cons_iff.2 ho₁) (TypedElCls.eq_of_mem henv hΔ hc hy) (K' := K)
          (fun k hk => Obs.bvar_iff.2 hk) Covers.refl
    · obtain ⟨c, K, y, τs, p, rfl, hc, hτ, hK, hbK, hy, hp⟩ := Obs.lam_iff.1 h
      obtain ⟨D₁, c₁, K₁, K₁', he₁, hc₁, hK₁', hcov₁⟩ := Obs.app_iff.1 hp
      have he₁' := Obs.lift_cons_iff.1 he₁
      obtain ⟨τs₁, hτs₁, hty₁⟩ := IHe.2.2.1 _ he₁'
      have hty₁' := hty₁
      cases hty₁ with
      | app hD =>
        have eD := Obs.piDom_mem (hτs₁ _ hD); subst eD
        have ec : c₁ = c := hc₁.trans (TypedElCls.eq_of_mem henv hΔ hc hy).symm
        subst ec
        have hKK : Covers K K₁ :=
          Covers.trans (Covers.of_subset fun k hk => Obs.bvar_iff.1 (hK₁' k hk)) hcov₁
        rw [vcls_defeq henv hΔ W.left (IsDefEq.eta he.defeq)]
        refine ⟨τs₁ ++ τs.map .piDomOb, fun τ hτ' => ?_,
          (hty₁'.mono fun τ hτ' => List.mem_append_left _ hτ').app_enlarge hKK
            (fun x hx => List.mem_append_right _ (List.mem_map_of_mem hx)) hK hbK⟩
        rcases List.mem_append.1 hτ' with hτ' | hτ'
        · exact hτs₁ τ hτ'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hτ'; exact .piDomOb (hτ x hx)
    · exact IHe.2.2.2 o h
  | proofIrrel _ _ _ ihp ihh ihh' =>
    refine ⟨?_, ihh.2.1, ihh'.2.1⟩
    replace ihp := ihp.1
    replace ihh := ihh.1
    replace ihh' := ihh'.1
    intro σ σ' S W tv tv'
    have IHp := ihp σ σ' S W tv tv'
    have IHh := ihh σ σ' S W tv tv'
    have IHh' := ihh' σ σ' S W tv tv'
    have e1 : ∀ o, ¬ Obs' σ S _ o := fun o h => by
      obtain ⟨τs, h1, h2⟩ := IHh.2.2.1 o h
      exact h2.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (IHp.2.2.1 τ (h1 τ hτ))⟩
    have e2 : ∀ o, ¬ Obs' σ' S _ o := fun o h => by
      obtain ⟨τs, h1, h2⟩ := IHh'.2.2.2 o h
      exact h2.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (IHp.2.2.2 τ (h1 τ hτ))⟩
    exact ⟨fun o h => (e1 o h).elim, fun o h => (e2 o h).elim,
      fun o h => (e1 o h).elim, fun o h => (e2 o h).elim⟩
  | @extra df ls u Γ hdf hlw hlen hu ht0 _ _ hl hr iht0 _ _ ihl ihr =>
    exact ⟨hvalid df hdf _ _ _ _ _ hΔ hlw hlen (ht0.mono hle) ⟨iht0.1, iht0.2.1⟩ (hl.mono hle)
      ⟨ihl.1, ihl.2.1⟩ (hr.mono hle) ⟨ihr.1, ihr.2.1⟩, ihl.2.1, ihr.2.1⟩
  | elimIota hb hrules hmem hrc hperm _ ht0 hl hr iht0 ihl ihr =>
    exact ⟨hEV.valid _ _ _ _ _ hb hrules hmem _ _ _ _ _ _ hΔ hrc hperm (ht0.mono hle)
      ⟨iht0.1, iht0.2.1⟩ (hl.mono hle) ⟨ihl.1, ihl.2.1⟩ (hr.mono hle) ⟨ihr.1, ihr.2.1⟩,
      ihl.2.1, ihr.2.1⟩
  | projIota hp _ hfield _ ihp ihf =>
    exact sound_projIota henv hΔ (hle.projections hp) (hPV _ _ hp) hfield ⟨ihp.1, ihp.2.1⟩
      ⟨ihf.1, ihf.2.1⟩
  | structEta hp hpl _ _ _ ihe ihm =>
    exact sound_structEta henv hΔ (hle.projections hp) (hPV _ _ hp) hpl ⟨ihe.1, ihe.2.1⟩
      ⟨ihm.1, ihm.2.1⟩
  | unitLike hp _ _ hnf _ _ ihe ihe' =>
    exact sound_unitLike henv (hle.projections hp) (hPV _ _ hp) hnf ⟨ihe.1, ihe.2.1⟩
      ⟨ihe'.1, ihe'.2.1⟩

end

/-- **Validity of an environment** `E` in the model of `env`: its rules, projection entries and
eliminator rules are valid. These are the hypotheses of `Model.sound` for `E`. -/
structure EnvValid (env E : VEnv) : Prop where
  rule : ∀ df, E.defeqs df → RuleValid env df
  proj : ∀ n p, E.projections n p → ProjValid env n p
  elim : ElimsValid env E

/-- Validity of an environment with fewer rules, projections and eliminators. -/
theorem EnvValid.of_sub {env E E' : VEnv} (V : EnvValid env E)
    (hdf : ∀ df, E'.defeqs df → E.defeqs df) (hp : ∀ n p, E'.projections n p → E.projections n p)
    (he : ∀ b s, E'.eliminators b s → E.eliminators b s) : EnvValid env E' :=
  ⟨fun df h => V.rule df (hdf df h), fun n p h => V.proj n p (hp n p h), V.elim.of_elims he⟩

/-- Soundness for an environment that is valid in the model of `env`. -/
theorem EnvValid.soundAtH {env E : VEnv} (henv : env.Ordered) (hle : E ≤ env) (V : EnvValid env E)
    (U : Nat) (Δ : List VExpr) (hΔ : OnCtx Δ (env.IsType U)) : SoundTypedIn env E U Δ :=
  fun H => sound henv hΔ hle V.rule V.proj V.elim H

end Model
end VEnv
end Lean4Lean
