import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound
import Lean4Lean.Theory.Typing.HeadInjectivity.ChainInjectivity

/-! # Extraction of chain-level head injectivity from soundness

`VEnv.WF.chainHeadInjectivity_of_sound`: in a well-formed environment for which the
observation model is sound (`Model.SoundEnv`, proved for every well-formed environment by
`VEnv.WF.soundEnv` in `Model/EnvValid.lean`), the hypothesis `ChainHeadInjectivity` of the
syntactic layer holds (section 4.1 of the design notes).

All observations are taken at the identity valuation `(id, ∅)` of the chain's own context
(`Δ = Γ`); a chain is turned into `Ob.Sub` inclusions link by link (`chain_sub`, from
`sound`).

* `sort_sort`: the `sort` observation.
* `forallE_chain`, with two observations: the domain class at the identity
  valuation gives `TypeChain Γ A A'`; then, in `A :: Γ` and for the weakened chain, the
  codomain class at the fresh-variable key `bvar 0` gives `TypeChain (A :: Γ) B B'`.
* `rigid_rigid`/`former_args`: a sort-typed spine `mkApps (const c ls) args` has the
  observations `rigid c (ls.map eval) n s` and `rigidArg i cᵢ` (`spine_data`: the spine
  observations of the head are typed, by the strong typing derivation of the spine and the
  typing invariant of soundness); on the other side of the chain they force the same head,
  levels and arity, and each argument into the class of the corresponding left argument,
  which the collapse lemma turns into a definitional equality. For `former_args`, the
  domain classes of the left spine observation are those of the syntactic telescope
  (`tele_spine`), because the observation is typed at the observations of the constant's
  type. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat}

/-! ## List helpers -/

theorem forall₂_equiv_of_map_eval :
    ∀ {ls ls' : List VLevel}, ls.map (·.eval) = ls'.map (·.eval) → List.Forall₂ (· ≈ ·) ls ls'
  | [], [], _ => .nil
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_equiv_of_map_eval h.2)

/-! ## Observations at the identity valuation -/

/-- Observations at the identity valuation of `Γ`. -/
abbrev OI (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → Ob → Prop :=
  Obs env U Γ VExpr.Subst.id ObSets.empty

/-- Soundness of the observation model for every derivation of `env` (at every target
context): the hypothesis of the extraction, supplied for every well-formed environment by
`VEnv.WF.soundEnv`. -/
def SoundEnv (env : VEnv) : Prop :=
  ∀ {U Δ Γ t t' T}, OnCtx Δ (env.IsType U) → env.IsDefEqStrong U Γ t t' T →
    SoundAt env U Δ Γ t t' T ∧ HTS env U Δ Γ t T ∧ HTS env U Δ Γ t' T

/-- Soundness at the identity valuation. -/
theorem sound_id (henv : env.OrderedStrong) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqStrong U Γ t t' T) :
    Ob.Sub (OI env U Γ t) (OI env U Γ t') ∧ Ob.Sub (OI env U Γ t') (OI env U Γ t) ∧
    (∀ o, OI env U Γ t o →
      TypedAt env U Γ (vcls env U Γ .id t T) VExpr.Subst.id ObSets.empty T o) ∧
    (∀ o, OI env U Γ t' o →
      TypedAt env U Γ (vcls env U Γ .id t' T) VExpr.Subst.id ObSets.empty T o) :=
  (hnr hΓ H).1 .id .id .empty (Ctx.SubstEq.id henv hΓ) TV.empty TV.empty

/-- A chain of sort-typed equalities includes the observations of its left end in those of
its right end (up to subsumption). -/
theorem chain_sub (henv : env.OrderedStrong) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ X Y) : Ob.Sub (OI env U Γ X) (OI env U Γ Y) := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact (sound_id henv hnr hΓ (h.strong henv hΓ)).1
  | tail _ h ih =>
    let ⟨_, h⟩ := h; exact ih.trans (sound_id henv hnr hΓ (h.strong henv hΓ)).1

/-! ## Sorts and Pi types -/

theorem sort_sort (henv : env.OrderedStrong) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  have := Obs.sort_mem ho
  injection this

theorem forallE_chain (henv : env.OrderedStrong) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.forallE A B) (.forallE A' B')) :
    env.TypeChain U Γ A A' ∧ env.TypeChain U (A :: Γ) B B' := by
  have ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := h.isType_l.forallE_inv henv
  have ⟨_, ⟨_, hB'⟩⟩ := h.isType_r.forallE_inv henv
  -- the domain, at the identity valuation
  have hdom : env.TypeChain U Γ A A' := by
    obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (.piDom (A := A) (B := B))
    rw [l.piDom_inv] at ho
    have e := Obs.piDom_mem ho
    simp only [VExpr.subst_id] at e
    have : TyCls env U Γ A A' := e ▸ TyCls.self
    exact (TyCls.mem_iff_chain henv hΓ hA).1 this
  refine ⟨hdom, ?_⟩
  -- the codomain, at the fresh variable of `A :: Γ`
  have hΔ : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
  have hw := h.weakN henv (.one (A := A))
  have hdomw : env.TypeChain U (A :: Γ) A.lift A'.lift := hdom.weakN henv .one
  have h0 : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hc : TypedElCls env U (A :: Γ) (TyCls env U (A :: Γ) ((A.liftN 1).subst .id))
      (ElCls env U (A :: Γ) (TyCls env U (A :: Γ) A.lift) (.bvar 0)) := by
    rw [VExpr.subst_id]; exact .of_hasType h0
  have hobs := Obs.piCod (env := env) (U := U) (Δ := A :: Γ) (σ := .id) (S := .empty)
    (B := B.liftN 1 1) hc ElCls.self
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΔ hw _ hobs
  rw [l.piCod_inv] at ho
  obtain ⟨_, y, hy, eC⟩ := Obs.piCod_mem ho
  have e0 : (B.liftN 1 1).subst (VExpr.Subst.id.cons (.bvar 0)) = B :=
    (VExpr.inst_eq _ _).symm.trans (VExpr.inst_liftN_bvar B 0)
  rw [e0] at eC
  have hy0 : env.IsDefEq U (A :: Γ) (.bvar 0) y A.lift := ElCls.collapse henv hΔ h0 .self hy
  have hy0' : env.IsDefEq U (A :: Γ) y (.bvar 0) A'.lift := hdomw.defeqDF hy0.symm
  have hBw : env.HasType U (A'.lift :: A :: Γ) (B'.liftN 1 1) (.sort _) :=
    hB'.weakN henv (.succ (.zero [A]))
  have hBB := IsDefEq.instDF henv hΔ hBw hy0'
  rw [VExpr.inst_liftN_bvar] at hBB
  have e2 : (B'.liftN 1 1).subst (VExpr.Subst.id.cons y) = (B'.liftN 1 1).inst y :=
    (VExpr.inst_eq _ _).symm
  rw [e2] at eC
  have e1 : TyCls env U (A :: Γ) B = TyCls env U (A :: Γ) B' :=
    eC.trans (TyCls.eq_of_defeq hBB)
  have : TyCls env U (A :: Γ) B B' := e1 ▸ TyCls.self
  exact (TyCls.mem_iff_chain henv hΔ hB).1 this

/-! ## Rigid spines -/

/-- The spine observations of a rigid constant ending in a rigid observation are its own rigid
observations. -/
theorem const_wrap_inv {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {keys : List Key}
    (hrig : env.Rigid n) (h : Obs env U Δ σ S (.const n ls) (wrap keys o))
    (ho : (∃ n' ℓs m s, o = .rigid n' ℓs m s) ∨ ∃ i c, o = .rigidArg i c) :
    RigidEnd n (ls.map (·.eval)) keys o := by
  have hna : o.NotApp := by rcases ho with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial
  rcases Obs.const_iff.1 h with ⟨_, _, keys', r, e, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, e, _, _, _, _, _, hr, _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨_, _, _, _, keys', r, e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna hr.notApp
    exact hr
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf _)
  · have hrn : r.NotApp := by
      rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨rfl, rfl⟩ := wrap_inj e hna hrn
    rcases ho with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf lsP)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  all_goals
    obtain ⟨-, rfl⟩ := wrap_inj e hna trivial
    rcases ho with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- The keys of a left spine: each argument class is the class of the argument at the
domain class, which is the type class of a type of the argument, and the key observations
are observations of the argument. -/
def KeyedArgs (env : VEnv) (U : Nat) (Γ : List VExpr) (keys : List Key) (args : List VExpr) :
    Prop :=
  List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 a ∧
    (∀ x ∈ k.2.2, OI env U Γ a x) ∧ ∃ X, env.HasType U Γ a X ∧ k.1 = TyCls env U Γ X) keys args

/-- **Typed spine observations** (from the spine lemma): for a sort-typed spine
`mkApps (const c ls) args : sort u`, there are keys for the arguments such that every
observation typed at `[sort u]`, wrapped in the keys, is typed at observations of the
constant's type. -/
theorem spine_data (henv : env.OrderedStrong) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hu : env.IsDefEq U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls) args) (.sort u)) :
    ∃ ci keys, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ KeyedArgs env U Γ keys args ∧
      (∀ o, TypedOb env U Γ (vcls env U Γ .id (.mkApps (.const c ls) args) (.sort u)) o
          [.sort u.eval] →
        ∃ τs₀, (∀ τ ∈ τs₀, OI env U Γ (ci.type.instL ls) τ) ∧
          TypedOb env U Γ (ElCls env U Γ (TyCls env U Γ (ci.type.instL ls)) (.const c ls))
            (wrap keys o) τs₀) := by
  have H := (hnr hΓ (hu.strong henv hΓ)).2.1
  obtain ⟨ci, info, hci, hls, ⟨u₀, hT, -⟩, hinfo, -, P1, P2, -⟩ :=
    H.spine henv hΓ rfl (Ctx.SubstEq.id henv hΓ) TV.empty (args.map fun _ => [])
      (by
        clear H hu
        induction args with
        | nil => exact .nil
        | cons a as ih => exact .cons nofun ih)
      [.sort u.eval] fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort
  have hlen : info.length = args.length := List.Forall₂.length_eq hinfo
  refine ⟨ci, info.map (·.1), hci, hls, ?_, P1⟩
  · clear P1 P2 hlen H hu hT
    induction hinfo with
    | nil => exact .nil
    | @cons ka a _ _ h _ ih =>
      obtain ⟨h1, h2, h3, _, h5, _⟩ := h
      refine .cons ⟨by rw [h1, VExpr.subst_id], h2, ka.2, h5.1.defeq.hasType.1, ?_⟩ ih
      rw [h3, VExpr.subst_id]

/-- The analysis of a chain between two rigid spines: same head, same levels, and each
right argument in the class of the corresponding left argument (at the left spine's keys,
whose spine observation is typed at the observations of the head's type). -/
theorem rigid_analysis (henv : env.OrderedStrong) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (hrig' : env.Rigid c')
    (h : env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args')) :
    ∃ ci keys u, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ KeyedArgs env U Γ keys args ∧
      (∃ τs₀, (∀ τ ∈ τs₀, OI env U Γ (ci.type.instL ls) τ) ∧
        TypedOb env U Γ (ElCls env U Γ (TyCls env U Γ (ci.type.instL ls)) (.const c ls))
          (wrap keys (.rigid c (ls.map (·.eval)) keys.length u)) τs₀) ∧
      c = c' ∧ ls.map (·.eval) = ls'.map (·.eval) ∧
      List.Forall₂ (fun (k : Key) a' => k.2.1 a') keys args' := by
  obtain ⟨u, hu⟩ := h.isType_l
  obtain ⟨ci, keys, hci, hls, hkeys, hQ⟩ := spine_data henv hnr hΓ hu
  have hk' : List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 (a.subst .id) ∧
      ∀ x ∈ k.2.2, OI env U Γ a x) keys args :=
    List.Forall₂.imp (fun k a ⟨h1, h2, _⟩ => ⟨by rw [VExpr.subst_id]; exact h1, h2⟩) hkeys
  let LeftEnd : Ob → Prop := fun r => r = .rigid c (ls.map (·.eval)) keys.length u.eval ∨
    ∃ i, ∃ h : i < keys.length, r = .rigidArg i (keys[i]).2.1
  have hle : ∀ r, LeftEnd r → RigidEnd c (ls.map (·.eval)) keys r := by
    intro r hr; rcases hr with rfl | h
    · exact .inl ⟨_, rfl⟩
    · exact .inr h
  have hsort : ∀ r, LeftEnd r →
      TypedOb env U Γ (vcls env U Γ .id (.mkApps (.const c ls) args) (.sort u)) r
        [.sort u.eval] := by
    intro r hr
    rcases hr with rfl | ⟨_, _, rfl⟩
    · exact .rigid (List.mem_singleton_self _)
    · exact .rigidArg (List.mem_singleton_self _)
  have hL : ∀ r, LeftEnd r → OI env U Γ (.mkApps (.const c ls) args) r := by
    intro r hr
    obtain ⟨τs₀, h1, h2⟩ := hQ r (hsort r hr)
    exact obs_mkApps_of_wrap hk' (.const hrig hci h1 h2 (hle r hr))
  have hR : ∀ r, LeftEnd r → ∃ keys' : List Key,
      List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 (a.subst .id)) keys' args' ∧
      RigidEnd c' (ls'.map (·.eval)) keys' r := by
    intro r hr
    obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (hL r hr)
    have : o = r := by
      rcases hr with rfl | ⟨_, _, rfl⟩
      · exact l.rigid_inv
      · exact l.rigidArg_inv
    subst this
    obtain ⟨keys', hk, hw⟩ := wrap_of_obs_mkApps ho
    exact ⟨keys', hk, const_wrap_inv hrig' hw (by
      rcases hr with rfl | ⟨_, _, rfl⟩
      · exact .inl ⟨_, _, _, _, rfl⟩
      · exact .inr ⟨_, _, rfl⟩)⟩
  have hlen := List.Forall₂.length_eq hkeys
  obtain ⟨keys', hk1, hr1⟩ := hR _ (.inl rfl)
  rcases hr1 with ⟨_, e⟩ | ⟨_, _, e⟩
  · injection e with ec eℓ en
    refine ⟨ci, keys, u.eval, hci, hls, hkeys, hQ _ (hsort _ (.inl rfl)), ec, eℓ, ?_⟩
    refine List.forall₂_of_getElem (by rw [en, List.Forall₂.length_eq hk1]) fun i h₁ h₂ => ?_
    obtain ⟨keys'', hk2, hr2⟩ := hR _ (.inr ⟨i, h₁, rfl⟩)
    rcases hr2 with ⟨_, e⟩ | ⟨j, hj, e⟩
    · cases e
    · injection e with eij ecl
      subst eij
      obtain ⟨_, hcl⟩ := List.forall₂_getElem_exists hk2 i hj
      rw [ecl, hcl, VExpr.subst_id]; exact ElCls.self
  · cases e

/-- Along a syntactic telescope, the domain classes of a typed spine observation are the
type classes of the instantiated domains, so arguments in the left argument classes are
related at those domains. -/
theorem tele_spine (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (keys : List Key) (ds : List VExpr) (w : VLevel) (Γ' : List VExpr) (σ : VExpr.Subst)
      (args args' : List VExpr) (τs : List Ob) (o : Ob),
    Ctx.SubstEq env U Γ σ σ Γ' → env.IsType U Γ' (VExpr.wrapForalls ds (.sort w)) →
    (∀ τ ∈ τs, ∃ σ'' S'', Ctx.SubstEq env U Γ σ'' σ Γ' ∧
      Obs env U Γ σ'' S'' (VExpr.wrapForalls ds (.sort w)) τ) →
    TypedOb env U Γ cv (wrap keys o) τs →
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Γ k.1 a ∧
      ∃ X, k.1 X ∧ env.HasType U Γ a X) keys args →
    List.Forall₂ (fun (k : Key) a' => k.2.1 a') keys args' →
    SpineArgsEq env U Γ ((VExpr.wrapForalls ds (.sort w)).subst σ) args args'
  | [], _, _, _, _, _, _, _, _, _, _, _, _, .nil, .nil => .nil
  | ⟨D, c, K⟩ :: keys, ds, w, Γ', σ, _, _, τs, o, W, hT, hτs, hty,
      .cons ⟨hc, X, hX, ha⟩ H1, .cons ha' H2 => by
    cases hty with
    | app hD _ _ _ _ _ hcod hty' =>
      obtain ⟨σ'', S'', W'', hobs⟩ := hτs _ hD
      cases ds with
      | nil => cases Obs.sort_mem hobs
      | cons d ds =>
        have hD' := Obs.piDom_mem hobs
        obtain ⟨⟨_, hd⟩, hR⟩ := IsType.forallE_inv henv hT
        have hdd := hd.substDF henv W''.wf hΓ W''
        have eD : D = TyCls env U Γ (d.subst σ) := hD'.trans (TyCls.eq_of_defeq hdd)
        subst eD; dsimp only at hc; subst hc
        have haa := ElCls.collapse henv hΓ ha hX ha'
        refine .cons haa ?_
        rw [VExpr.inst_lift_cons]
        refine tele_spine henv hΓ keys ds w (d :: Γ') (σ.cons _) _ _ _ o
          (.cons W hd haa.hasType.1) hR ?_ hty' H1 H2
        intro x hx
        obtain ⟨K₀, hm, _⟩ := hcod x hx
        obtain ⟨σ₃, S₃, W₃, hobs₃⟩ := hτs _ hm
        obtain ⟨_, _, y, hy, hxR⟩ := Obs.piCodOb_mem hobs₃
        have hdd₃ := hd.substDF henv W₃.wf hΓ W₃
        have hay := ElCls.collapse henv hΓ ha hX hy
        exact ⟨σ₃.cons y, S₃.cons (listSet K₀), .cons W₃ hd (.defeqDF hdd₃.symm hay.symm), hxR⟩

end Model

/-- **Chain-level head injectivity from soundness**: in a well-formed environment for which
the observation model is sound, the hypothesis of the syntactic layer holds. -/
theorem WF.chainHeadInjectivity_of_sound {env : VEnv} (henv : env.WF) (hnr : Model.SoundEnv env) :
    env.ChainHeadInjectivity where
  sort_sort hΓ h := Model.sort_sort henv.orderedStrong hnr hΓ h
  forallE_chain hΓ h := Model.forallE_chain henv.orderedStrong hnr hΓ h
  rigid_rigid hΓ hrig hrig' h := by
    obtain ⟨_, keys, _, _, _, hkeys, _, ec, eℓ, hk'⟩ :=
      Model.rigid_analysis henv.orderedStrong hnr hΓ hrig hrig' h
    refine ⟨ec, Model.forall₂_equiv_of_map_eval eℓ,
      Model.forall₂_zip (fun k a a' ⟨h1, _, X, hX, h2⟩ h3 => ?_) hkeys hk'⟩
    rw [h1, h2] at h3
    exact ⟨X, Model.ElCls.collapse henv.orderedStrong hΓ hX .self h3⟩
  former_args {U Γ c ci doms w ls ls' args args'} hΓ hrig hci hty h := by
    obtain ⟨ci', keys, _, hci', hls, hkeys, ⟨τs₀, hτs₀, hty₀⟩, _, _, hk'⟩ :=
      Model.rigid_analysis henv.orderedStrong hnr hΓ hrig hrig h
    cases hci.symm.trans hci'
    have eT : ci.type.instL ls =
        VExpr.wrapForalls (doms.map (·.instL ls)) (.sort (w.inst ls)) := by
      rw [hty, VExpr.instL_wrapForalls]; rfl
    have hT : env.IsType U [] (VExpr.wrapForalls (doms.map (·.instL ls)) (.sort (w.inst ls))) :=
      eT ▸ IsType.instL hls (henv.ordered.constWF hci)
    have := Model.tele_spine henv.orderedStrong hΓ keys (doms.map (·.instL ls)) (w.inst ls) []
      .id args args' τs₀ _ .nil hT (fun τ hτ => ⟨_, _, .nil, eT ▸ hτs₀ τ hτ⟩) hty₀
      (List.Forall₂.imp (fun k a ⟨h1, _, X, hX, h2⟩ => ⟨h1, X, h2 ▸ .self, hX⟩) hkeys) hk'
    rwa [VExpr.subst_id, ← eT] at this

end VEnv
end Lean4Lean
