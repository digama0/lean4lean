import Lean4Lean.Theory.Typing.HeadInjectivity.Model.HTS

/-! # Lemmas for the rule cases of soundness

Syntactic injectivity of rule patterns, binder types of a rule context, splitting typed key
telescopes, domains of semantically typed Pi telescopes, spine observations with their key
coverage, constructor-spine observations, and related substitutions built pointwise. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Lists -/

theorem forall₂_zip {R : γ → α → Prop} {R' : γ → β → Prop} {P : α → β → Prop}
    (H : ∀ k a b, R k a → R' k b → P a b) :
    ∀ {ks : List γ} {l₁ : List α} {l₂ : List β},
      List.Forall₂ R ks l₁ → List.Forall₂ R' ks l₂ → List.Forall₂ P l₁ l₂
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 H1, .cons h2 H2 => .cons (H _ _ _ h1 h2) (forall₂_zip H H1 H2)

/-! ## Syntax -/

theorem wrapLams_pat_inj :
    ∀ {ds ds' : List VExpr} {as as' : List VExpr} {a a' : VExpr},
    VExpr.wrapLams ds (.mkApps (.const n ls) (as ++ [a])) =
      VExpr.wrapLams ds' (.mkApps (.const n' ls') (as' ++ [a'])) →
    ds = ds' ∧ n = n' ∧ ls = ls' ∧ as = as' ∧ a = a'
  | [], [], as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_nil, VExpr.mkApps_snoc] at h
    injection h with h1 h2
    obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj h1
    exact ⟨rfl, rfl, rfl, rfl, h2⟩
  | [], _ :: _, as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_nil, List.foldr_cons, VExpr.mkApps_snoc] at h; cases h
  | _ :: _, [], as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_nil, List.foldr_cons, VExpr.mkApps_snoc] at h; cases h
  | d :: ds, d' :: ds', as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    injection h with h1 h2
    obtain ⟨rfl, h3⟩ := wrapLams_pat_inj h2
    exact ⟨by rw [h1], h3⟩

theorem wrapLams_inj_len : ∀ {ds ds' : List VExpr} {b b' : VExpr}, ds.length = ds'.length →
    VExpr.wrapLams ds b = VExpr.wrapLams ds' b' → ds = ds' ∧ b = b'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | d :: ds, d' :: ds', _, _, hl, h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    injection h with h1 h2
    obtain ⟨rfl, rfl⟩ := wrapLams_inj_len (Nat.succ.inj hl) h2
    exact ⟨by rw [h1], rfl⟩

/-- The binder types of a context prefix. -/
theorem lookup_append : ∀ (L : List VExpr) (x : Nat) (h : x < L.length),
    Lookup (L ++ Γ) x ((L[x]).liftN (x+1))
  | A :: L, 0, _ => .zero
  | A :: L, x+1, h => by
    have := (lookup_append (Γ := Γ) L x (Nat.lt_of_succ_lt_succ h)).succ (A := A)
    rwa [VExpr.lift, VExpr.liftN_liftN] at this

theorem lookup_binderTy {doms : List VExpr} (hx : x < doms.length) :
    Lookup ((doms.map (·.instL ls)).reverse ++ Γ) x (binderTy doms ls x) := by
  have hx' : x < (doms.map (·.instL ls)).reverse.length := by simpa using hx
  have := lookup_append (Γ := Γ) _ x hx'
  suffices e : binderTy doms ls x =
      ((doms.map (fun d : VExpr => d.instL ls)).reverse[x]'hx').liftN (x+1) by
    rw [e]; exact this
  have hx'' : x < doms.reverse.length := by simpa using hx
  simp only [binderTy, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx'',
    Option.getD_some, VExpr.instL_liftN]
  congr 1
  simp [List.getElem_reverse]

/-! ## Telescopes -/

theorem TeleKeys.split : ∀ {pre : List VExpr} {kpre : List Key} {ds keys},
    pre.length = kpre.length →
    TeleKeys env U Δ σ S (pre ++ ds) (kpre ++ keys) σ' S' →
    ∃ σ₁ S₁, TeleKeys env U Δ σ S pre kpre σ₁ S₁ ∧ TeleKeys env U Δ σ₁ S₁ ds keys σ' S'
  | [], [], _, _, _, h => ⟨_, _, .nil, h⟩
  | _ :: _, _ :: _, _, _, hl, .cons hc hy hK hb h => by
    obtain ⟨σ₁, S₁, h1, h2⟩ := TeleKeys.split (Nat.succ.inj hl) h
    exact ⟨σ₁, S₁, .cons hc hy hK hb h1, h2⟩

/-- A domain of a semantically typed Pi telescope is semantically typed. -/
theorem HTS.tele_dom : ∀ {pre : List VExpr} {Γ T},
    HTS env U Δ Γ (.wrapForalls (pre ++ A :: post) R) T →
    ∃ u, HTS env U Δ (pre.reverse ++ Γ) A (.sort u) ∧
      SD env U Δ (pre.reverse ++ Γ) A A (.sort u)
  | [], _, _, H => by
    obtain ⟨u, v, h1, h2, _, _⟩ := H.forallE_inv rfl
    exact ⟨u, h1, h2⟩
  | B :: pre, _, _, H => by
    obtain ⟨_, _, _, _, h3, _⟩ := H.forallE_inv rfl
    obtain ⟨u, h⟩ := HTS.tele_dom (pre := pre) h3
    exact ⟨u, by simpa [List.reverse_cons, List.append_assoc] using h⟩

/-! ## Valuations -/

theorem subst_eta (σ : VExpr.Subst) : σ = σ.tail.cons σ.head := by
  funext i; cases i <;> rfl

/-- The tail of observation sets. -/
def ObSets.tail (S : ObSets) : ObSets := fun i => S (i+1)

theorem obSets_eta (S : ObSets) : S = S.tail.cons (S 0) := by
  funext i; cases i <;> rfl

theorem Obs.lift_iff_tail {t : VExpr} :
    Obs' σ S t.lift o ↔ Obs' σ.tail S.tail t o := by
  conv => lhs; rw [subst_eta σ, obSets_eta S]
  exact Obs.lift_cons_iff

theorem TypedAt.lift_iff_tail {T : VExpr} :
    TypedAt env U Δ cv σ S T.lift o ↔ TypedAt env U Δ cv σ.tail S.tail T o := by
  unfold TypedAt; simp only [Obs.lift_iff_tail]

theorem TV.tail (h : TV env U Δ (A :: Γ) σ S) : TV env U Δ Γ σ.tail S.tail := by
  refine ⟨fun i => h.1 (i+1), fun i B hL o ho => ?_⟩
  have := h.2 (i+1) _ hL.succ o ho
  rw [vcls_tail] at this
  exact TypedAt.lift_iff_tail.1 this

/-- Contexts `L ++ Γ` whose entries in `L` (innermost first) are sound. -/
inductive CtxSD (env : VEnv) (U : Nat) (Δ Γ : List VExpr) : List VExpr → Prop
  | nil : CtxSD env U Δ Γ []
  | cons : SD env U Δ (L ++ Γ) A A (.sort u) → CtxSD env U Δ Γ L → CtxSD env U Δ Γ (A :: L)

theorem DomsSD.ctxSD : ∀ {ds L Γ}, DomsSD env U Δ (L ++ Γ) ds → CtxSD env U Δ Γ L →
    CtxSD env U Δ Γ (ds.reverse ++ L)
  | [], _, _, _, h => h
  | _ :: ds, L, Γ, .cons hA hds, h => by
    have := DomsSD.ctxSD (L := _ :: L) hds (.cons hA h)
    simpa [List.reverse_cons, List.append_assoc] using this

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Observation typing of variables transfers between related anchors that agree outside a
sound context prefix. -/
theorem TV.transfer : ∀ {L : List VExpr} {τ v : VExpr.Subst} {S : ObSets},
    CtxSD env U Δ Γ L → Ctx.SubstEq env U Δ τ v (L ++ Γ) → (∀ x, L.length ≤ x → τ x = v x) →
    TV env U Δ (L ++ Γ) v S → TV env U Δ (L ++ Γ) τ S
  | [], τ, v, S, _, _, he, tv => by
    have : τ = v := funext fun x => he x (Nat.zero_le _)
    subst this; exact tv
  | A :: L, τ, v, S, .cons hA hL, W, he, tv => by
    cases W with
    | cons W hA0 hhd =>
      have ih := TV.transfer hL W (fun x hx => he (x+1) (by simp; omega)) tv.tail
      refine ⟨tv.1, fun i B hLk o ho => ?_⟩
      cases hLk with
      | zero =>
        have W' : Ctx.SubstEq env U Δ τ v (A :: (L ++ Γ)) := .cons W hA0 hhd
        have ecls := vcls_substEq henv hΔ W' (IsDefEq.bvar (Lookup.zero (ty := A)))
        have h1 := TypedAt.lift_iff_tail.1 (tv.2 0 _ .zero o ho)
        rw [ecls]
        refine TypedAt.lift_iff_tail.2 (h1.mono_le ?_)
        exact (hA.2 _ _ _ (SubstEq.symm henv hΔ W) tv.tail ih).1
      | succ hLk =>
        rw [vcls_tail]
        have := ih.2 _ _ hLk o ho
        exact TypedAt.lift_iff_tail.2 this

end


/-- Related substitutions from pointwise equalities on a context prefix, each established
knowing that the substitutions are related on the entries outside it. -/
theorem SubstEq.of_heads_ind : ∀ {L : List VExpr} {τ v : VExpr.Subst},
    Ctx.SubstEq env U Δ v v (L ++ Γ) → (∀ x, L.length ≤ x → τ x = v x) →
    (∀ x A, x < L.length → Lookup (L ++ Γ) x A →
      Ctx.SubstEq env U Δ (fun i => τ (i + (x+1))) (fun i => v (i + (x+1)))
        (L.drop (x+1) ++ Γ) →
      env.IsDefEq U Δ (τ x) (v x) (A.subst τ)) →
    Ctx.SubstEq env U Δ τ v (L ++ Γ)
  | [], τ, v, W, he, _ => by
    have : τ = v := funext fun x => he x (Nat.zero_le _)
    subst this; exact W
  | A :: L, τ, v, W, he, h => by
    cases W with
    | cons W hA _ =>
      have ih : Ctx.SubstEq env U Δ τ.tail v.tail (L ++ Γ) :=
        SubstEq.of_heads_ind W (fun x hx => he (x+1) (by simp; omega)) fun x B hx hL hW => by
          have := h (x+1) B.lift (by simp; omega) hL.succ hW
          rwa [VExpr.lift_subst] at this
      refine .cons ih hA ?_
      have := h 0 A.lift (by simp) .zero ih
      rwa [VExpr.lift_subst] at this

/-! ## Spines -/

/-- An observation of an application spine comes from a spine observation of its head, at
keys whose observations are covered by observations of the arguments. -/
theorem wrap_of_obs_mkApps_le {σ : VExpr.Subst} {S : ObSets} :
    ∀ {args : List VExpr} {f : VExpr} {o : Ob}, Obs' σ S (VExpr.mkApps f args) o →
    ∃ keys : List Key, List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, ∃ x', Obs' σ S a x' ∧ x' ≼ x) keys args ∧ Obs' σ S f (wrap keys o)
  | [], _, _, h => ⟨[], .nil, h⟩
  | a :: as, f, o, h => by
    obtain ⟨keys, hk, h'⟩ := wrap_of_obs_mkApps_le (args := as) (f := .app f a) h
    obtain ⟨D, c, K, K', h1, h2, h3, h4⟩ := Obs.app_iff.1 h'
    exact ⟨(D, c, K) :: keys, .cons ⟨h2, fun x hx =>
      let ⟨x', hx', l⟩ := h4 x hx; ⟨x', h3 x' hx', l⟩⟩ hk, h1⟩

theorem wrap_inj_len : ∀ {ks ks' : List Key} {o o' : Ob}, ks.length = ks'.length →
    wrap ks o = wrap ks' o' → ks = ks' ∧ o = o'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | k :: ks, k' :: ks', _, _, hl, h => by
    simp only [wrap_cons, Ob.app.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨rfl, rfl⟩ := wrap_inj_len (Nat.succ.inj hl) h4
    obtain ⟨_, _, _⟩ := k; obtain ⟨_, _, _⟩ := k'; simp_all

/-- Constructor observations of a spine of a rigid constructor come from the constructor
clause. -/
theorem ctor_spine_inv {σ : VExpr.Subst} {S : ObSets} (hrig : env.Rigid c)
    (h : Obs' σ S (.mkApps (.const c lsc) margs) r)
    (hr : (∃ n ℓs m, r = .ctorHead n ℓs m) ∨ (∃ i cl, r = .ctorArg i cl) ∨
      ∃ i pre k, r = .ctorArgOb i pre k) :
    ∃ keys, List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, ∃ x', Obs' σ S a x' ∧ x' ≼ x) keys margs ∧
      CtorEnd c (lsc.map (·.eval)) keys r := by
  obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps_le h
  have hna : r.NotApp := by
    rcases hr with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> trivial
  refine ⟨keys, hk, ?_⟩
  rcases Obs.const_iff.1 hw with ⟨_, _, keys', r', e, _, _, _, _, hr'⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r', e, _, _, _, _, _, hr', _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨_, _, _, _, keys', r', e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna hr'.notApp
    rcases hr with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      rcases hr' with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf _)
  · have hrn : r'.NotApp := by
      rcases hr' with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨rfl, rfl⟩ := wrap_inj e hna hrn
    exact hr'
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf lsP)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna trivial
    rcases hr with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna trivial
    rcases hr with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna trivial
    rcases hr with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h

theorem instL_wrapLams (ds : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapLams ds body).instL ls =
      VExpr.wrapLams (ds.map (·.instL ls)) (body.instL ls) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [VExpr.wrapLams, List.foldr_cons, VExpr.instL, List.map_cons] at ih ⊢; rw [ih]

theorem KeyData.forall₂_keys {info : List (Key × VExpr)} {args : List VExpr}
    (h : List.Forall₂ (KeyData env U Δ Γ σ S) info args) :
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, Obs' σ S a x) (info.map (·.1)) args := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons ⟨h.1, h.2.1⟩ ih

theorem KeyData.forall₂_backed {info : List (Key × VExpr)} {args : List VExpr}
    (h : List.Forall₂ (KeyData env U Δ Γ σ S) info args) : KeysBacked (info.map (·.1)) := by
  intro k hk
  obtain ⟨ka, hka, rfl⟩ := List.mem_map.1 hk
  obtain ⟨a, -, hd⟩ := List.Forall₂.forall_exists_l h ka hka
  exact hd.2.2.2.2.2

theorem forall₂_nil_lists (args : List VExpr) {P : VExpr → Ob → Prop} :
    List.Forall₂ (fun K a => ∀ x ∈ K, P a x) (args.map fun _ => ([] : List Ob)) args := by
  induction args with
  | nil => exact .nil
  | cons a as ih => exact .cons nofun ih

theorem TeleKeys.outer (h : TeleKeys env U Δ σ S ds keys v vS) :
    ∀ x, v (x + ds.length) = σ x ∧ vS (x + ds.length) = S x := by
  induction h with
  | nil => intro x; exact ⟨rfl, rfl⟩
  | @cons c y K σ S A ds keys v vS _ _ _ _ _ ih =>
    intro x
    have := ih (x+1)
    simp only [List.length_cons]
    rw [show x + (ds.length + 1) = x + 1 + ds.length by omega]
    exact this

theorem TeleKeys.inner (h : TeleKeys env U Δ σ S ds keys v vS) :
    ∀ x < ds.length, ∃ K, vS x = listSet K := by
  induction h with
  | nil => intro x hx; cases hx
  | @cons c y K σ S A ds keys v vS _ _ _ _ hk ih =>
    intro x hx
    simp only [List.length_cons] at hx
    rcases Nat.lt_or_ge x ds.length with h | h
    · exact ih x h
    · have : x = 0 + ds.length := by omega
      subst this
      exact ⟨K, (hk.outer 0).2⟩

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A semantically typed rigid spine has its rigid head observation, at its sort. -/
theorem spine_rigid_obs (H : HTS env U Δ Γ (.mkApps (.const c ls) args) (.sort u))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) (hrig : env.Rigid c) :
    Obs' σ S (.mkApps (.const c ls) args) (.rigid c (ls.map (·.eval)) args.length u.eval) := by
  obtain ⟨ci, info, hci, hls, -, hinfo, -, P1, -, -⟩ :=
    H.spine henv hΔ rfl W tv (args.map fun _ => []) (forall₂_nil_lists args)
      [.sort u.eval] fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort
  have hlen : info.length = args.length := List.Forall₂.length_eq hinfo
  have hr : RigidEnd c (ls.map (·.eval)) (info.map (·.1))
      (.rigid c (ls.map (·.eval)) args.length u.eval) := .inl ⟨u.eval, by simp [hlen]⟩
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 _ (.rigid (List.mem_singleton_self _))
  exact obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo) (.const hrig hci hτ₀ hty₀ hr)

end

end Model
end VEnv
end Lean4Lean
