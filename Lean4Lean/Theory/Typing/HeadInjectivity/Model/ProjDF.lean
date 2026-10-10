import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineTele
import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.Subst

/-! # The typing invariant of projections (`projDF`)

`Model.proj_obs_typed`: a field observation `fieldOb S j L o` of a major `e`, typed at the
observations of its type `S ls (ps ++ idx)`, has its inner observation `o` typed at the
observations of the field type `F` computed at a definitionally equal major `e'`, at the
value class of the projection. The type observations of a field observation are the
`fieldDom`/`fieldTy` observations of the family spine (`famDom`/`famTy`, inverted by
`famTy_inv`/`famDom_inv`); their key chains are related to the parameters and the earlier
projections of `e'`, so soundness of the constructor telescope moves each field-type
observation to an observation of `F`. -/

namespace Lean4Lean
namespace VEnv
namespace Model
open VExpr

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem keySets_snoc (K : List Key) (k : Key) :
    keySets (K ++ [k]) = (keySets K).cons (listSet k.2.2) := by
  funext m
  cases m with
  | zero => simp [keySets, ObSets.cons]
  | succ m =>
    simp only [keySets, ObSets.cons, List.length_append, List.length_singleton]
    by_cases hm : m < K.length
    · rw [dif_pos (by omega), dif_pos hm]
      simp only [show K.length + 1 - 1 - (m + 1) = K.length - 1 - m by omega]
      rw [List.getElem_append_left (by omega)]
    · rw [dif_neg (by omega), dif_neg hm]

/-- A Pi telescope ending in a non-Pi body has every other telescope presentation as a
prefix. -/
theorem wrapForalls_prefix {R0 : VExpr} (hR0 : ∀ A B, R0 ≠ .forallE A B) :
    ∀ {D Dc : List VExpr} {R0' : VExpr}, VExpr.wrapForalls D R0 = VExpr.wrapForalls Dc R0' →
      Dc.length ≤ D.length ∧ ∀ i (h : i < Dc.length) (h' : i < D.length), Dc[i] = D[i]
  | D, [], _, _ => ⟨Nat.zero_le _, fun i h => absurd h (by simp)⟩
  | [], d :: Dc, R0', h => by
    simp only [VExpr.wrapForalls, List.foldr_nil, List.foldr_cons] at h
    exact absurd h (hR0 _ _)
  | a :: D, d :: Dc, R0', h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.forallE.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨hl, hi⟩ := wrapForalls_prefix hR0 (D := D) (Dc := Dc) h
    refine ⟨by simp; omega, fun i hi' hi'' => ?_⟩
    cases i with
    | zero => rfl
    | succ i => exact hi i (by simp at hi'; omega) (by simp at hi''; omega)

/-- The end observation of a `famTy`/`famDom` spine is not an `app`. -/
private theorem notApp_fieldTy : (Ob.fieldTy n j FL x).NotApp := trivial
private theorem notApp_fieldDom : (Ob.fieldDom n j FL D).NotApp := trivial

/-- Inversion of the field-type observations of a rigid projection-registered family spine. -/
theorem famTy_inv {σ : VExpr.Subst} {S0 : ObSets} {S : Name} {ls : List VLevel}
    {args : List VExpr} {j : Nat} {FL : List Key} {x : Ob} (hrig : env.Rigid S)
    (h : Obs' σ S0 (.mkApps (.const S ls) args) (.fieldTy S j FL x)) :
    ∃ keys : List Key, List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
        ∀ y ∈ k.2.2, ∃ y', Obs' σ S0 a y' ∧ y' ≼ y) keys args ∧
      ∃ info Dc R0 as, ∃ τk : Nat → List Ob, env.projections S info ∧
        (info.resultLevel.inst ls).IsNeverZero ∧
        keys.length = info.nparams + info.nindices ∧ j < info.numFields ∧ FL.length = j ∧
        info.ctorType.instL ls = .wrapForalls Dc R0 ∧ info.nparams + j < Dc.length ∧
        ChainOK env U Δ Dc as (keys.take info.nparams ++ FL) ∧
        KeysBacked (keys.take info.nparams ++ FL) ∧
        (∀ i k τ, (keys.take info.nparams ++ FL)[i]? = some k → τ ∈ τk i →
          Obs' (VExpr.argSubst (as.take i)) (keySets ((keys.take info.nparams ++ FL).take i))
            (Dc.getD i (.sort .zero)) τ) ∧
        (∀ i k y, (keys.take info.nparams ++ FL)[i]? = some k → y ∈ k.2.2 →
          TypedOb env U Δ k.2.1 y (τk i)) ∧
        Obs' (VExpr.argSubst as) (keySets (keys.take info.nparams ++ FL))
          (Dc.getD (info.nparams + j) (.sort .zero)) x := by
  obtain ⟨keys, hk, h'⟩ := wrap_of_obs_mkApps_le h
  refine ⟨keys, hk, ?_⟩
  rcases Obs.const_iff.1 h' with ⟨_, _, keys', r, he, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, he, _, _, _, _, _, hr, _⟩ |
    ⟨df, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨_, _, _, _, keys', r, he, _, _, _, _, _, _, hr, _⟩ |
    ⟨ci, info, τs, keys', j', FL', x', Dc, R0, as, τk, he, _, _, hp, hnz, _, _, hl, hj, hFL,
      hshape, hlt, hchain, hkb, hτk, hty, hx⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, he, _⟩
  · obtain ⟨-, rfl⟩ := wrap_inj he notApp_fieldTy hr.notApp
    rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf (VLevel.params df.uvars))
  · obtain ⟨-, rfl⟩ := wrap_inj he notApp_fieldTy (by
      rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> (subst h; trivial))
    rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf _)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  · obtain ⟨_, _, _, rfl, _⟩ := hr
    obtain ⟨-, h⟩ := wrap_inj he notApp_fieldTy trivial
    cases h
  · obtain ⟨rfl, h⟩ := wrap_inj he notApp_fieldTy notApp_fieldTy
    cases h
    exact ⟨info, Dc, R0, as, τk, hp, hnz, hl, hj, hFL, hshape, hlt, hchain, hkb, hτk, hty, hx⟩
  · obtain ⟨-, h⟩ := wrap_inj he notApp_fieldTy notApp_fieldDom
    cases h

/-- Inversion of the field-domain observations of a rigid projection-registered family
spine. -/
theorem famDom_inv {σ : VExpr.Subst} {S0 : ObSets} {S : Name} {ls : List VLevel}
    {args : List VExpr} {j : Nat} {FL : List Key} {D : VExpr → Prop} (hrig : env.Rigid S)
    (h : Obs' σ S0 (.mkApps (.const S ls) args) (.fieldDom S j FL D)) :
    ∃ keys : List Key, List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
        ∀ y ∈ k.2.2, ∃ y', Obs' σ S0 a y' ∧ y' ≼ y) keys args ∧
      ∃ info Dc R0 as, env.projections S info ∧
        (info.resultLevel.inst ls).IsNeverZero ∧
        keys.length = info.nparams + info.nindices ∧ j < info.numFields ∧ FL.length = j ∧
        info.ctorType.instL ls = .wrapForalls Dc R0 ∧ info.nparams + j < Dc.length ∧
        ChainOK env U Δ Dc as (keys.take info.nparams ++ FL) ∧
        D = TyCls env U Δ ((Dc.getD (info.nparams + j) (.sort .zero)).subst
          (VExpr.argSubst as)) := by
  obtain ⟨keys, hk, h'⟩ := wrap_of_obs_mkApps_le h
  refine ⟨keys, hk, ?_⟩
  rcases Obs.const_iff.1 h' with ⟨_, _, keys', r, he, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, he, _, _, _, _, _, hr, _⟩ |
    ⟨df, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨_, _, _, _, keys', r, he, _, _, _, _, _, _, hr, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, he, _⟩ |
    ⟨ci, info, τs, keys', j', FL', D', Dc, R0, as, he, _, _, hp, hnz, _, _, hl, hj, hFL,
      hshape, hlt, hchain, hD⟩
  · obtain ⟨-, rfl⟩ := wrap_inj he notApp_fieldDom hr.notApp
    rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf (VLevel.params df.uvars))
  · obtain ⟨-, rfl⟩ := wrap_inj he notApp_fieldDom (by
      rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> (subst h; trivial))
    rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf _)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  · obtain ⟨_, _, _, rfl, _⟩ := hr
    obtain ⟨-, h⟩ := wrap_inj he notApp_fieldDom trivial
    cases h
  · obtain ⟨-, h⟩ := wrap_inj he notApp_fieldDom notApp_fieldTy
    cases h
  · obtain ⟨rfl, h⟩ := wrap_inj he notApp_fieldDom notApp_fieldDom
    cases h
    exact ⟨info, Dc, R0, as, hp, hnz, hl, hj, hFL, hshape, hlt, hchain, hD⟩

theorem keySets_nil : keySets [] = ObSets.empty := by
  funext m o; simp [keySets, ObSets.empty]

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A typed key chain gives a typed valuation of the telescope prefix at its anchors. -/
theorem chain_tv {Dc as : List VExpr} {K : List Key} (hch : ChainOK env U Δ Dc as K)
    (hKD : K.length ≤ Dc.length) (hkb : KeysBacked K) {τk : Nat → List Ob}
    (hτk : ∀ i k τ, K[i]? = some k → τ ∈ τk i →
      Obs' (VExpr.argSubst (as.take i)) (keySets (K.take i)) (Dc.getD i (.sort .zero)) τ)
    (hty : ∀ i k y, K[i]? = some k → y ∈ k.2.2 → TypedOb env U Δ k.2.1 y (τk i)) :
    ∀ i, i ≤ K.length →
      TV env U Δ (Dc.take i).reverse (VExpr.argSubst (as.take i)) (keySets (K.take i)) := by
  intro i
  induction i with
  | zero => intro _; simp only [List.take_zero, List.reverse_nil, keySets_nil]; exact TV.empty
  | succ i ih =>
    intro hi
    have tvi := ih (by omega)
    have hal : as.length = K.length := hch.1
    have hKi : K[i]? = some K[i] := List.getElem?_eq_getElem (by omega)
    have hai : as[i]? = some (as[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
    obtain ⟨hc, hy⟩ := hch.2 i _ _ hai hKi
    have hDi : Dc.getD i (.sort .zero) = Dc[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < Dc.length by omega)]
    rw [hDi] at hc
    rw [List.take_succ_eq_append_getElem (show i < Dc.length by omega),
      List.take_succ_eq_append_getElem (show i < as.length by omega),
      List.take_succ_eq_append_getElem (show i < K.length by omega), keySets_snoc,
      VExpr.argSubst_append_one]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    exact tvi.cons_cls henv hΔ hc hy (hkb _ (List.getElem_mem _))
      fun k hk => ⟨τk i, fun τ hτ => by rw [← hDi]; exact hτk i _ τ hKi hτ, hty i _ k hKi hk⟩

/-- Members of the classes of a typed key chain form a substitution related to its anchors. -/
theorem chain_substEq {Dc as bs : List VExpr} {K : List Key} (hch : ChainOK env U Δ Dc as K)
    (hKD : K.length ≤ Dc.length) (hbl : bs.length = K.length)
    (hbs : ∀ (i : Nat) (k : Key) (b : VExpr), K[i]? = some k → bs[i]? = some b → k.2.1 b)
    (hdom : ∀ i (hi : i < K.length), ∃ u,
      env.HasType U (Dc.take i).reverse (Dc[i]'(by omega)) (.sort u)) :
    ∀ i, i ≤ K.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst (as.take i)) (VExpr.argSubst (bs.take i))
        (Dc.take i).reverse := by
  intro i
  induction i with
  | zero => intro _; simp only [List.take_zero, List.reverse_nil]; exact .nil
  | succ i ih =>
    intro hi
    have Wi := ih (by omega)
    have hal : as.length = K.length := hch.1
    have hKi : K[i]? = some K[i] := List.getElem?_eq_getElem (by omega)
    have hai : as[i]? = some (as[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hbi : bs[i]? = some (bs[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
    obtain ⟨hc, hy⟩ := hch.2 i _ _ hai hKi
    have hDi : Dc.getD i (.sort .zero) = Dc[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < Dc.length by omega)]
    rw [hDi] at hc
    obtain ⟨u, hu⟩ := hdom i (by omega)
    rw [List.take_succ_eq_append_getElem (show i < Dc.length by omega),
      List.take_succ_eq_append_getElem (show i < as.length by omega),
      List.take_succ_eq_append_getElem (show i < bs.length by omega),
      VExpr.argSubst_append_one, VExpr.argSubst_append_one]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    exact .cons (by simpa using Wi) hu
      (by simpa using hc.defeq henv hΔ hy (hbs i _ _ hKi hbi))

end

theorem forall₂_get? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ {i : Nat} {a : α} {b : β}, l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h t, 0, _, _, h1, h2 => by simp at h1 h2; subst h1 h2; exact h
  | _, _, .cons _ t, i + 1, _, _, h1, h2 => by simp at h1 h2; exact forall₂_get? t h1 h2

theorem projsOf_getElem? (S : Name) (w : VExpr) (j i : Nat) (h : i < j) :
    (projsOf S w j)[i]? = some (.proj S i w) := by
  simp [projsOf, h]

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The typing invariant of projections.** -/
theorem proj_obs_typed {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hcl : info.ctorType.Closed) (hrigS : env.Rigid S) {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = info.uvars) {D : List VExpr} {R0 : VExpr}
    (T : ProjTele env U S info ls D R0) (hpi : PiSD env U Δ [] D R0)
    {Γ : List VExpr} {σ : VExpr.Subst} {S0 : ObSets}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S0)
    {ps idx : List VExpr} (hps : ps.length = info.nparams) (hidx : idx.length = info.nindices)
    {e e' : VExpr} (hee' : env.IsDefEq U Γ e e' (.mkApps (.const S ls) (ps ++ idx)))
    (hsub : Ob.Sub (Obs' σ S0 e) (Obs' σ S0 e'))
    {j : Nat} {F : VExpr} (hF : info.fieldType S ls ps j e' = some F)
    {L : List (List Ob)} {o : Ob} (hobs : Obs' σ S0 e (.fieldOb S j L o))
    (hty : TypedAt env U Δ (vcls env U Δ σ e (.mkApps (.const S ls) (ps ++ idx))) σ S0
      (.mkApps (.const S ls) (ps ++ idx)) (.fieldOb S j L o)) :
    TypedAt env U Δ (vcls env U Δ σ (.proj S j e) F) σ S0 F o := by
  obtain ⟨τs, hτs, hto⟩ := hty
  cases hto with
  | fieldOb hp' hj hL hDom hFL hτd hoTy _ =>
  cases henv.ordered.projections_unique hp hp'
  -- notation
  have hjD : info.nparams + j < D.length := by have := T.numFields; omega
  have hshapeD := T.shape
  obtain ⟨c0, lsR0, args0, hR0⟩ := T.head
  have hR0' : ∀ A B, R0 ≠ .forallE A B := by
    rw [hR0]; exact fun A B => VExpr.mkApps_ne_forallE (fun _ _ h => by cases h) _
  have hFeq := T.fieldType hlen hps e' hjD
  rw [hF, Option.some.injEq] at hFeq
  have hee'σ : env.IsDefEq U Δ (e.subst σ) (e'.subst σ)
      ((VExpr.mkApps (.const S ls) (ps ++ idx)).subst σ) := hee'.substDF henv W.wf hΔ W
  have heσ := hee'σ.hasType.1
  -- the substitution of the parameters and earlier projections of `e'`
  have hbl : ((ps ++ projsOf S e' j).map (·.subst σ)).length = info.nparams + j := by
    simp [projsOf, hps]
  -- members of chain classes
  have hmem : ∀ (keys FLk : List Key),
      List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
        ∀ y ∈ k.2.2, ∃ y', Obs' σ S0 a y' ∧ y' ≼ y) keys (ps ++ idx) →
      FLCompat env U Δ S (vcls env U Δ σ e (.mkApps (.const S ls) (ps ++ idx))) L FLk →
      ∀ (i : Nat) (k : Key) (b : VExpr), (keys.take info.nparams ++ FLk)[i]? = some k →
        ((ps ++ projsOf S e' j).map (·.subst σ))[i]? = some b → k.2.1 b := by
    intro keys FLk hk hFLk i k b hki hbi
    have hkl := List.Forall₂.length_eq hk
    by_cases hi : i < info.nparams
    · rw [List.getElem?_append_left (by simp [hkl, hps]; omega),
        List.getElem?_take_of_lt hi] at hki
      have hpi' : (ps ++ idx)[i]? = some ps[i] := by
        rw [List.getElem?_append_left (by omega)]; exact List.getElem?_eq_getElem _
      obtain ⟨h1, -⟩ := forall₂_get? hk hki hpi'
      rw [List.getElem?_map, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (show i < ps.length by omega)] at hbi
      cases hbi
      rw [h1]; exact ElCls.self
    · have hkt : (keys.take info.nparams).length = info.nparams := by simp [hkl, hps]
      rw [List.getElem?_append_right (by omega), hkt] at hki
      rw [List.getElem?_map, List.getElem?_append_right (by omega), hps] at hbi
      have hij : i - info.nparams < j := by
        have := (List.getElem?_eq_some_iff.mp hki).1; rw [hFLk.1, hL] at this; exact this
      rw [projsOf_getElem? S e' j _ hij] at hbi
      cases hbi
      have hLi : L[i - info.nparams]? = some (L[i - info.nparams]'(by omega)) :=
        List.getElem?_eq_getElem _
      obtain ⟨⟨Di, hDi⟩, -⟩ := hFLk.2 _ _ _ hki hLi
      rw [hDi]
      exact ⟨e'.subst σ, ElCls.mem_of_defeq hee'σ, ElCls.self⟩
  -- a chain's telescope is the constructor telescope, and its anchors are related to `bs`
  have hchainW : ∀ (keys FLk : List Key) (Dc : List VExpr) (R0' : VExpr) (as : List VExpr),
      List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
        ∀ y ∈ k.2.2, ∃ y', Obs' σ S0 a y' ∧ y' ≼ y) keys (ps ++ idx) →
      FLCompat env U Δ S (vcls env U Δ σ e (.mkApps (.const S ls) (ps ++ idx))) L FLk →
      FLk.length = j → info.ctorType.instL ls = .wrapForalls Dc R0' →
      info.nparams + j < Dc.length → ChainOK env U Δ Dc as (keys.take info.nparams ++ FLk) →
      Dc.take (info.nparams + j) = D.take (info.nparams + j) ∧
      Dc.getD (info.nparams + j) (.sort .zero) = D[info.nparams + j] ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst as)
        (VExpr.argSubst ((ps ++ projsOf S e' j).map (·.subst σ)))
        (D.take (info.nparams + j)).reverse := by
    intro keys FLk Dc R0' as hk hFLk hFLl hshape hlt hch
    have hkl := List.Forall₂.length_eq hk
    obtain ⟨hpl, hpe⟩ := wrapForalls_prefix hR0' (hshapeD.symm.trans hshape)
    have htake : ∀ i, i ≤ Dc.length → Dc.take i = D.take i := by
      intro i hi
      apply List.ext_getElem (by simp; omega)
      intro m h1 h2
      simp only [List.getElem_take]
      exact hpe m (by simp at h1; omega) (by simp at h2; omega)
    have hgd : Dc.getD (info.nparams + j) (.sort .zero) = D[info.nparams + j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, hpe _ hlt hjD]
    have hKl : (keys.take info.nparams ++ FLk).length = info.nparams + j := by
      simp [hkl, hps, hFLl]
    have W := chain_substEq henv hΔ hch (by omega) (by rw [hbl, hKl]) (hmem keys FLk hk hFLk)
      (fun i hi => by
        obtain ⟨u, hu⟩ := T.doms i (by omega)
        refine ⟨u, ?_⟩
        rw [htake i (by omega), hpe i (by omega) (by omega)]
        exact hu) (info.nparams + j) (by omega)
    have hal : as.length = info.nparams + j := hch.1.trans hKl
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
      htake _ (by omega)] at W
    exact ⟨htake _ (by omega), hgd, W⟩
  -- the field domain in its prefix context
  have hdomsD := hpi.doms
  obtain ⟨-, u, hSDn⟩ := DomsSD.take_getElem hdomsD (info.nparams + j) hjD
  have hDnTy : env.HasType U (D.take (info.nparams + j)).reverse D[info.nparams + j] (.sort u) := by
    simpa using hSDn.1.defeq.hasType.1
  have hbs : (ps ++ projsOf S e' j).map (·.subst σ) =
      ps.map (·.subst σ) ++ projsOf S (e'.subst σ) j := by
    rw [List.map_append, projsOf_subst]
  have hFσ : F.subst σ = D[info.nparams + j].subst
      (VExpr.argSubst ((ps ++ projsOf S e' j).map (·.subst σ))) := by
    rw [hFeq, T.dom_subst henv hps e' hjD σ, hbs]
  -- the class of the field domain
  obtain ⟨keys3, hk3, info3, Dc3, R03, as3, hp3, hnz, -, -, hFL3, hshape3, hlt3, hch3, hD3⟩ :=
    famDom_inv hrigS (hτs _ hDom)
  cases henv.ordered.projections_unique hp hp3
  obtain ⟨-, hgd3, W3⟩ := hchainW keys3 _ Dc3 R03 as3 hk3 hFL hFL3 hshape3 hlt3 hch3
  subst hD3
  have hDcls : TyCls env U Δ ((Dc3.getD (info.nparams + j) (.sort .zero)).subst
      (VExpr.argSubst as3)) = TyCls env U Δ (F.subst σ) := by
    rw [hgd3, hFσ]
    have := hDnTy.substDF henv W3.wf hΔ W3
    exact TyCls.eq_of_defeq this
  have hFty : env.HasType U Δ (F.subst σ) (.sort u) := by
    rw [hFσ]; exact hDnTy.subst henv (SubstEq.right henv hΔ W3) hΔ
  have hft := T.fieldType_subst henv hlen hps hjD σ hF
  have hTσ : (VExpr.mkApps (.const S ls) (ps ++ idx)).subst σ =
      VExpr.mkApps (.const S ls) (ps.map (·.subst σ) ++ idx.map (·.subst σ)) := by
    simp [VExpr.subst_mkApps, VExpr.subst]
  have hcls : projCls env U Δ S j (vcls env U Δ σ e (.mkApps (.const S ls) (ps ++ idx)))
      (TyCls env U Δ ((Dc3.getD (info.nparams + j) (.sort .zero)).subst (VExpr.argSubst as3))) =
      vcls env U Δ σ (.proj S j e) F := by
    funext z
    apply propext
    simp only [projCls, vcls, VExpr.subst]
    constructor
    · rintro ⟨w, hw, hz⟩
      have h1 := ElCls.collapse henv hΔ heσ TyCls.self hw
      rw [hTσ] at h1 hee'σ
      have hpd : env.IsDefEq U Δ (.proj S j (e.subst σ)) (.proj S j w) (F.subst σ) :=
        .projDF hp hls hlen (by simp [hps]) (by simp [hidx]) hft hFty hee'σ.symm
          (hee'σ.symm.trans h1) hcl (.inl hnz)
      rw [hDcls] at hz
      rw [ElCls.eq_of_defeq TyCls.self hpd]; exact hz
    · intro hz; exact ⟨e.subst σ, ElCls.self, by rw [hDcls]; exact hz⟩
  -- each type observation of the field maps to an observation of `F`
  have hctx : CtxSD env U Δ [] (D.take (info.nparams + j)).reverse := by
    simpa using DomsSD.ctxSD (L := []) (DomsSD.take hdomsD (info.nparams + j)) .nil
  have hrawl : (ps ++ projsOf S e' j).length = info.nparams + j := by simp [projsOf, hps]
  have hstep : ∀ x, (∃ FLx, Ob.fieldTy S j FLx x ∈ τs ∧
      FLCompat env U Δ S (vcls env U Δ σ e (.mkApps (.const S ls) (ps ++ idx))) L FLx) →
      ∃ y, Obs' σ S0 F y ∧ y ≼ x := by
    intro x hx
    obtain ⟨FLx, hfx, hFLx⟩ := hx
    obtain ⟨keys, hk, info2, Dc, R0', as, τk, hp2, -, hkl, -, hFLl, hshape, hlt, hch, hkb,
      hτk, htyk, hxo⟩ := famTy_inv hrigS (hτs _ hfx)
    cases henv.ordered.projections_unique hp hp2
    obtain ⟨htk, hgd, WK⟩ := hchainW keys FLx Dc R0' as hk hFLx hFLl hshape hlt hch
    have hkl' := List.Forall₂.length_eq hk
    have hKl : (keys.take info.nparams ++ FLx).length = info.nparams + j := by
      simp [hkl', hps, hFLl]
    have hal : as.length = info.nparams + j := hch.1.trans hKl
    have tvK := chain_tv henv hΔ hch (by omega) hkb hτk htyk (info.nparams + j) (by omega)
    rw [List.take_of_length_le (l := as) (by omega),
      List.take_of_length_le (l := keys.take info.nparams ++ FLx) (by omega), htk] at tvK
    have tvbs : TV env U Δ ((D.take (info.nparams + j)).reverse ++ [])
        (VExpr.argSubst ((ps ++ projsOf S e' j).map (·.subst σ)))
        (keySets (keys.take info.nparams ++ FLx)) :=
      TV.transfer henv hΔ hctx (by simpa using SubstEq.symm henv hΔ WK)
        (fun y hy => by
          have hy' : info.nparams + j ≤ y := by simp at hy; omega
          rw [VExpr.argSubst_ge _ (by simp only [List.length_map]; omega),
            VExpr.argSubst_ge _ (by omega), List.length_map, hrawl, hal])
        (by simpa using tvK)
    rw [hgd] at hxo
    obtain ⟨x1, hx1, l1⟩ := (hSDn.2 _ _ _ (by simpa using WK) (by simpa using tvK) tvbs).1 x hxo
    -- move the observation sets to the observations of the instantiating terms
    have H : ∀ (i : Nat) (k : Key) (r : VExpr) (y : Ob),
        (keys.take info.nparams ++ FLx)[i]? = some k → (ps ++ projsOf S e' j)[i]? = some r →
        y ∈ k.2.2 → ∃ y', Obs' σ S0 r y' ∧ y' ≼ y := by
      intro i k r y hki hri hy
      have hil : i < info.nparams + j := by
        have := (List.getElem?_eq_some_iff.mp hki).1; omega
      have hkt : (keys.take info.nparams).length = info.nparams := by simp [hkl', hps]
      by_cases hip : i < info.nparams
      · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hip] at hki
        rw [List.getElem?_append_left (by omega)] at hri
        have hpi' : (ps ++ idx)[i]? = some r := by
          rw [List.getElem?_append_left (by omega)]; exact hri
        exact (forall₂_get? hk hki hpi').2 y hy
      · rw [List.getElem?_append_right (by omega), hkt] at hki
        rw [List.getElem?_append_right (by omega), hps,
          projsOf_getElem? S e' j _ (by omega)] at hri
        cases hri
        have hLi : L[i - info.nparams]? = some (L[i - info.nparams]'(by omega)) :=
          List.getElem?_eq_getElem _
        obtain ⟨-, h2⟩ := hFLx.2 _ _ _ hki hLi
        obtain ⟨y', hy'L, l'⟩ := h2 y hy
        have hw : Obs' σ S0 e (.fieldOb S (i - info.nparams) (L.take (i - info.nparams)) y') :=
          Obs.backed hobs tv.1 _ (Ob.mem_wit_fieldOb.2 (.inl ⟨_, _, y', hLi, hy'L, rfl⟩))
        obtain ⟨o2, ho2, l2⟩ := hsub _ hw
        obtain ⟨L', y2, rfl, l3⟩ := l2.fieldOb_inv
        exact ⟨y2, Obs.proj_iff.2 ⟨L', ho2⟩, l3.trans l'⟩
    have hcov : ∀ m y, keySets (keys.take info.nparams ++ FLx) m y →
        ∃ y', Obs' σ S0 (VExpr.argSubst (ps ++ projsOf S e' j) m) y' ∧ y' ≼ y := by
      intro m y hy
      simp only [keySets] at hy
      split at hy
      · rename_i hm
        rw [VExpr.argSubst_lt _ (by omega)]
        have e1 := List.getElem?_eq_getElem (l := keys.take info.nparams ++ FLx)
          (i := (keys.take info.nparams ++ FLx).length - 1 - m) (by omega)
        have e2 : (ps ++ projsOf S e' j)[(keys.take info.nparams ++ FLx).length - 1 - m]? =
            some (ps ++ projsOf S e' j)[(ps ++ projsOf S e' j).length - 1 - m] := by
          rw [show (keys.take info.nparams ++ FLx).length - 1 - m =
            (ps ++ projsOf S e' j).length - 1 - m by omega]
          exact List.getElem?_eq_getElem _
        exact H _ _ _ y e1 e2 hy
      · exact absurd hy id
    obtain ⟨x2, hx2, l2⟩ := hx1.mono_le hcov
    refine ⟨x2, ?_, l2.trans l1⟩
    rw [hFeq, Obs.subst_iff]
    refine (Obs.closed_iff (T.closedN_dom henv _ hjD) (fun i hi => ?_) (fun _ _ => rfl)).1 hx2
    simp only [VExpr.Subst.comp]
    exact (VExpr.argSubst_comp_lt _ σ (by omega)).symm
  obtain ⟨τs', hτs', hcov⟩ := exists_list_cover (P := Obs' σ S0 F) (R := fun y x => y ≼ x)
    fun x hx => hstep x (hτd x hx)
  exact ⟨τs', hτs', hcls ▸ hoTy.strengthen hcov⟩

end

end Model
end VEnv
end Lean4Lean
