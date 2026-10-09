import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Interp
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Definitions

/-! # Telescopes of keys

`TeleKeys σ S ds keys σ' S'`: the keys `keys` are typed keys along the binder domains `ds`
(outermost first), each key's class typed at the type class of its domain under the valuation
extended by the earlier keys, and `(σ', S')` is the extended valuation (a representative of
each key class, and the key observations). The same data describe

* the observations of a lambda telescope (`Obs.wrapLams_iff`: an observation of
  `wrapLams ds b` is `wrap keys o` with `o` an observation of `b` at the extension), and
* the codomain observations of a Pi telescope (`tele_obs`), and typed chains of
  `app` observations at the observations of a Pi telescope unwind to them (`tele_unwind`,
  which needs the soundness of the telescope's codomains, `PiSD`, to change representatives).

`SoundAt` (the soundness statement of one derivation) and `SD` (a strong derivation with
its soundness) are defined here, for use by the semantic typing derivations of
`Model/HTS.lean`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- The soundness statement for one derivation `Γ ⊢ t ≡ t' : T`. -/
def SoundAt (Γ : List VExpr) (t t' T : VExpr) : Prop :=
  ∀ σ σ' S, Ctx.SubstEq env U Δ σ σ' Γ → TV env U Δ Γ σ S → TV env U Δ Γ σ' S →
    Ob.Sub (Obs env U Δ σ S t) (Obs env U Δ σ' S t') ∧
    Ob.Sub (Obs env U Δ σ' S t') (Obs env U Δ σ S t) ∧
    (∀ o, Obs env U Δ σ S t o → TypedAt env U Δ (vcls env U Δ σ t T) σ S T o) ∧
    (∀ o, Obs env U Δ σ' S t' o → TypedAt env U Δ (vcls env U Δ σ' t' T) σ' S T o)

/-- A strong derivation together with its soundness. -/
def SD (Γ : List VExpr) (t t' T : VExpr) : Prop :=
  env.IsDefEqStrong U Γ t t' T ∧ SoundAt env U Δ Γ t t' T

/-- Typed keys along a telescope of binder domains (outermost first), with the extended
valuation. -/
inductive TeleKeys : VExpr.Subst → ObSets → List VExpr → List Key → VExpr.Subst → ObSets →
    Prop
  | nil : TeleKeys σ S [] [] σ S
  | cons : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c → c y →
    (∀ k ∈ K, TypedAt env U Δ c σ S A k) → Backed (listSet K) →
    TeleKeys (σ.cons y) (S.cons (listSet K)) ds keys σ' S' →
    TeleKeys σ S (A :: ds) ((TyCls env U Δ (A.subst σ), c, K) :: keys) σ' S'

/-- Soundness of the domains and of the remaining codomains of a Pi telescope. -/
inductive PiSD : List VExpr → List VExpr → VExpr → Prop
  | nil : PiSD Γ [] R
  | cons : SD env U Δ Γ A A (.sort u) →
    SD env U Δ (A :: Γ) (.wrapForalls ds R) (.wrapForalls ds R) (.sort v) →
    PiSD (A :: Γ) ds R → PiSD Γ (A :: ds) R

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem TeleKeys.length (h : TeleKeys env U Δ σ S ds keys σ' S') : keys.length = ds.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ ih => simp [ih]

theorem mkApps_inv {hd : VExpr} (h : e = VExpr.mkApps hd args) :
    (args = [] ∧ e = hd) ∨
      ∃ as a, args = as ++ [a] ∧ e = .app (VExpr.mkApps hd as) a := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · exact .inl ⟨rfl, h⟩
  · refine .inr ⟨as, a, by simp, ?_⟩
    rw [h, List.concat_eq_append, VExpr.mkApps_snoc]

theorem mkApps_const_inv (h : e = VExpr.mkApps (.const c ls) args) :
    (args = [] ∧ e = .const c ls) ∨
      ∃ as a, args = as ++ [a] ∧ e = .app (VExpr.mkApps (.const c ls) as) a := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · exact .inl ⟨rfl, h⟩
  · refine .inr ⟨as, a, by simp, ?_⟩
    rw [h, List.concat_eq_append, VExpr.mkApps_snoc]

/-- Unwinding a spine observation of the head along the arguments. -/
theorem obs_mkApps_of_wrap {σ : VExpr.Subst} {S : ObSets} :
    ∀ {keys : List Key} {args : List VExpr} {f : VExpr} {o : Ob},
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, Obs env U Δ σ S a x) keys args →
    Obs env U Δ σ S f (wrap keys o) → Obs env U Δ σ S (VExpr.mkApps f args) o
  | _, _, _, _, .nil, h => h
  | _ :: _, a :: as, f, o, .cons ⟨h1, h2⟩ H, h => by
    rw [wrap_cons] at h
    show Obs env U Δ σ S (VExpr.mkApps (.app f a) as) o
    exact obs_mkApps_of_wrap H (.app h h1 h2 Covers.refl)

/-- An observation of an application spine comes from a spine observation of its head. -/
theorem wrap_of_obs_mkApps {σ : VExpr.Subst} {S : ObSets} :
    ∀ {args : List VExpr} {f : VExpr} {o : Ob}, Obs env U Δ σ S (VExpr.mkApps f args) o →
    ∃ keys : List Key, List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ))
      keys args ∧ Obs env U Δ σ S f (wrap keys o)
  | [], _, _, h => ⟨[], .nil, h⟩
  | a :: as, f, o, h => by
    obtain ⟨keys, hk, h'⟩ := wrap_of_obs_mkApps (args := as) (f := .app f a) h
    obtain ⟨D, c, K, K', h1, h2, _, _⟩ := Obs.app_iff.1 h'
    exact ⟨(D, c, K) :: keys, .cons h2 hk, h1⟩

theorem typedAt_sort_iff : TypedAt env U Δ cv σ S (.sort l) o ↔
    TypedOb env U Δ cv o [.sort l.eval] := by
  constructor
  · rintro ⟨τs, h1, h2⟩
    exact h2.mono fun τ hτ => by rw [Obs.sort_mem (h1 τ hτ)]; exact List.mem_singleton_self _
  · intro h
    refine ⟨_, fun τ hτ => ?_, h⟩
    rw [List.mem_singleton] at hτ; subst hτ; exact .sort

/-- Observations of a Pi type at one typed key. -/
theorem pi_list {σ : VExpr.Subst} {S : ObSets} {K τk τc : List Ob}
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c) (hy : c y)
    (hτk : ∀ τ ∈ τk, Obs' σ S A τ) (hkk : ∀ k ∈ K, TypedOb env U Δ c k τk)
    (hbK : Backed (listSet K))
    (hτc : ∀ τ ∈ τc, Obs' (σ.cons y) (S.cons (listSet K)) B τ) :
    ∃ τs, (∀ τ ∈ τs, Obs' σ S (.forallE A B) τ) ∧
      ∀ cv o, TypedOb env U Δ (appCls env U Δ cv c (TyCls env U Δ (B.subst (σ.cons y)))) o τc →
        TypedOb env U Δ cv (.app (TyCls env U Δ (A.subst σ)) c K o) τs := by
  refine ⟨.piDom (TyCls env U Δ (A.subst σ)) ::
    .piCod c (TyCls env U Δ (B.subst (σ.cons y))) :: (τk.map .piDomOb ++ τc.map (.piCodOb c K)),
    ?_, fun cv o ho => ?_⟩
  · intro τ hτ
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hτ
    rcases hτ with rfl | rfl | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact .piDom
    · exact .piCod hc hy
    · exact .piDomOb (hτk x hx)
    · exact .piCodOb hc hτk hkk hbK hy (hτc x hx)
  · refine .app (τd := τk) (τc := τc) (List.mem_cons_self ..) (fun x hx => ?_) hkk hbK hc
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (fun x hx => ⟨K, ?_, Covers.refl⟩) ho
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map_of_mem hx)))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map_of_mem hx)))

/-- Codomain observations at typed keys are observations of the Pi telescope. -/
theorem tele_obs (h : TeleKeys env U Δ σ S ds keys σ' S') (hx : Obs' σ' S' R x) :
    Obs' σ S (.wrapForalls ds R) (piCodChain keys x) := by
  induction h with
  | nil => exact hx
  | cons hc hy hK hb _ ih =>
    obtain ⟨τs, h1, h2⟩ := TypedAt.merge hK
    exact .piCodOb hc h1 h2 hb hy (ih hx)

/-- Observations of a lambda telescope. -/
theorem Obs.wrapLams_iff : Obs' σ S (.wrapLams ds b) o ↔
    ∃ keys σ' S' p, TeleKeys env U Δ σ S ds keys σ' S' ∧ o = wrap keys p ∧ Obs' σ' S' b p := by
  induction ds generalizing σ S o with
  | nil =>
    constructor
    · intro h; exact ⟨[], σ, S, o, .nil, rfl, h⟩
    · rintro ⟨_, _, _, _, h1, rfl, h3⟩; cases h1; exact h3
  | cons A ds ih =>
    constructor
    · intro h
      obtain ⟨c, K, x, τs, p, rfl, hc, hτ, hK, hb, hx, hp⟩ := Obs.lam_iff.1 h
      obtain ⟨keys, σ', S', q, h1, rfl, h3⟩ := ih.1 hp
      exact ⟨_ :: keys, σ', S', q, .cons hc hx (fun k hk => ⟨τs, hτ, hK k hk⟩) hb h1, rfl, h3⟩
    · rintro ⟨_, σ', S', q, h1, rfl, h3⟩
      cases h1 with
      | cons hc hy hK hb h1 =>
        obtain ⟨τs, h4, h5⟩ := TypedAt.merge hK
        exact .lam hc h4 h5 hb hy (ih.2 ⟨_, _, _, _, h1, rfl, h3⟩)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Keys typed at their class extend a typed valuation by any member of the class. -/
theorem TV.cons_cls (tv : TV env U Δ Γ σ S)
    (hc : TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) c) (hy : c y) (hb : Backed (listSet K))
    (hK : ∀ k ∈ K, TypedAt env U Δ c σ S A k) :
    TV env U Δ (A :: Γ) (σ.cons y) (S.cons (listSet K)) :=
  tv.cons hb fun k hk => (hK k hk).congr_cls (let ⟨_, _, _, e⟩ := hc.mem henv hΔ hy; e)

/-- One step of unwinding: an `app` observation typed at observations of a Pi type has its
key typed at the domain, and its result typed, at the class of the applications, at codomain
observations at the extension by any member `y` of the key class. -/
theorem pi_step (hA : env.HasType U Γ A (.sort u)) (hB' : env.HasType U (A :: Γ) B (.sort v))
    (hB : SoundAt env U Δ (A :: Γ) B B (.sort v)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (ho : TypedOb env U Δ cv (.app D c K o) τs)
    (hτ : ∀ τ ∈ τs, Obs' σ S (.forallE A B) τ) (hy : c y) :
    D = TyCls env U Δ (A.subst σ) ∧ TypedElCls env U Δ D c ∧
      (∀ k ∈ K, TypedAt env U Δ c σ S A k) ∧ Backed (listSet K) ∧
      ∃ τc, (∀ τ ∈ τc, Obs' (σ.cons y) (S.cons (listSet K)) B τ) ∧
        TypedOb env U Δ (appCls env U Δ cv c (TyCls env U Δ (B.subst (σ.cons y)))) o τc := by
  cases ho with
  | @app _ τd _ _ _ τc _ C _ hD hd hkt hBK hc hC hcod hty' =>
    have eD := Obs.piDom_mem (hτ _ hD); subst eD
    have hτd : ∀ x ∈ τd, Obs' σ S A x := fun x hx => Obs.piDomOb_mem (hτ _ (hd x hx))
    have hKA : ∀ k ∈ K, TypedAt env U Δ c σ S A k := fun k hk => ⟨τd, hτd, hkt k hk⟩
    refine ⟨rfl, hc, hKA, hBK, ?_⟩
    have eC : C = TyCls env U Δ (B.subst (σ.cons y)) := by
      obtain ⟨-, z, hz, rfl⟩ := Obs.piCod_mem (hτ _ hC)
      have W' : Ctx.SubstEq env U Δ (σ.cons z) (σ.cons y) (A :: Γ) :=
        .cons W hA (hc.defeq henv hΔ hz hy)
      exact TyCls.eq_of_defeq (hB'.substDF henv W'.wf hΔ W')
    subst eC
    have : ∀ x ∈ τc, ∃ x', Obs' (σ.cons y) (S.cons (listSet K)) B x' ∧ x' ≼ x := by
      intro x hx
      obtain ⟨K₀, hm, hKK⟩ := hcod x hx
      obtain ⟨_, ⟨τk, hτk, hkk⟩, z, hz, hxR⟩ := Obs.piCodOb_mem (hτ _ hm)
      have W' : Ctx.SubstEq env U Δ (σ.cons z) (σ.cons y) (A :: Γ) :=
        .cons W hA (hc.defeq henv hΔ hz hy)
      have hK₀ : ∀ k ∈ K₀, TypedAt env U Δ c σ S A k := fun k hk => ⟨τk, hτk, hkk k hk⟩
      have hb₀ := Obs.piCodOb_backed (hτ _ hm)
      obtain ⟨x₁, hx₁, l₁⟩ := (hB _ _ _ W' (tv.cons_cls henv hΔ hc hz hb₀ hK₀)
        (tv.cons_cls henv hΔ hc hy hb₀ hK₀)).1 x hxR
      obtain ⟨x₂, hx₂, l₂⟩ := hx₁.mono_le (S' := S.cons (listSet K)) fun i o h => by
        cases i with
        | zero => obtain ⟨k', hk', l⟩ := hKK o h; exact ⟨k', hk', l⟩
        | succ i => exact ⟨o, h, .refl⟩
      exact ⟨x₂, hx₂, l₂.trans l₁⟩
    obtain ⟨τc', h1, h2⟩ := exists_list_cover this
    exact ⟨τc', h1, hty'.strengthen h2⟩

/-- **Unwinding**: a chain of `app` observations typed at observations of a Pi telescope
(with sound codomains) has typed keys, and its innermost observation is typed (at some class)
at codomain observations at the extended valuation. -/
theorem tele_unwind (hds : PiSD env U Δ Γ ds R) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hlen : keys.length = ds.length)
    (ho : TypedOb env U Δ cv (wrap keys o) τs)
    (hτ : ∀ τ ∈ τs, Obs' σ S (.wrapForalls ds R) τ) :
    ∃ σ' S', TeleKeys env U Δ σ S ds keys σ' S' ∧
      ∃ τc cv', (∀ τ ∈ τc, Obs' σ' S' R τ) ∧ TypedOb env U Δ cv' o τc := by
  induction hds generalizing σ S keys τs cv with
  | nil =>
    cases keys with
    | nil => exact ⟨σ, S, .nil, τs, cv, hτ, ho⟩
    | cons => cases hlen
  | @cons Γ A u ds R v hA hR hds ih =>
    cases keys with
    | nil => cases hlen
    | cons k keys =>
      obtain ⟨D, c, K⟩ := k
      simp only [wrap_cons] at ho
      have hc : TypedElCls env U Δ D c := by cases ho with | app _ _ _ _ hc => exact hc
      obtain ⟨y, hy⟩ := hc.nonempty
      obtain ⟨rfl, hc, hKA, hBK, τc, h1, h2⟩ :=
        pi_step henv hΔ hA.1.defeq.hasType.1 hR.1.defeq.hasType.1 hR.2 W tv ho hτ hy
      have W'' : Ctx.SubstEq env U Δ (σ.cons y) (σ.cons y) (A :: Γ) :=
        .cons W hA.1.defeq.hasType.1 (hc.hasType henv hΔ hy)
      obtain ⟨σ', S', hT, τc'', cv'', h3, h4⟩ :=
        ih W'' (tv.cons_cls henv hΔ hc hy hBK hKA) (Nat.succ.inj hlen) h2 h1
      exact ⟨σ', S', .cons hc hy hKA hBK hT, τc'', cv'', h3, h4⟩

end

end Model
end VEnv
end Lean4Lean
