import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EtaBind

/-! # The valuation of a constant spine: observation transfer

`HTS.spineVal`: for a constant spine `mkApps (const c ls) args` semantically typed at `T`, with
the constant's type a Pi telescope `wrapForalls Dw Rw`, the observations of `T` under a typed
valuation `(σ, S)` of the context are, up to subsumption in both directions, the observations
of the residual telescope `wrapForalls (Dw.drop args.length) Rw` under the *argument
valuation*: the anchors `argSubst (args.map (·.subst σ))` and the observation sets
`argSets σ S args` (the observations of the arguments). `HTS.spineVal_dom` is the same for
the domain of the Pi type of a prefix of the spine. These are the observation-level forms of
`spine_res_cls` and `spine_dom_cls` (`Model/EtaBind.lean`), and let the typing of a spine be
read at its telescope with the actual arguments in place of anchors.

`Ob.Sub.mkApps`: subsumption between the observations of two heads is inherited by their
applications to the same arguments. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Spine lemmas without typing -/

/-- Subsumption below a chain of `app` observations. -/
theorem Ob.Le.wrap_inv : ∀ {keys : List Key} {x o : Ob}, o ≼ wrap keys x →
    ∃ keys' x', o = wrap keys' x' ∧
      List.Forall₂ (fun (k' k : Key) => k'.1 = k.1 ∧ k'.2.1 = k.2.1 ∧ Covers k.2.2 k'.2.2)
        keys' keys ∧ x' ≼ x
  | [], x, o, h => ⟨[], o, rfl, .nil, h⟩
  | k :: keys, x, o, h => by
    rw [wrap_cons] at h
    obtain ⟨K₀, y, rfl, hK, hy⟩ := h.app_inv
    obtain ⟨keys', x', rfl, hk, hx⟩ := Ob.Le.wrap_inv hy
    exact ⟨(k.1, k.2.1, K₀) :: keys', x', rfl, .cons ⟨rfl, rfl, hK⟩ hk, hx⟩

/-- Unwinding a spine observation of the head along the arguments, with key observations
covered by observations of the arguments. -/
theorem obs_mkApps_of_wrap_le {σ : VExpr.Subst} {S : ObSets} :
    ∀ {keys : List Key} {args : List VExpr} {f : VExpr} {o : Ob},
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∃ K', (∀ x ∈ K', Obs' σ S a x) ∧ Covers K' k.2.2) keys args →
    Obs' σ S f (wrap keys o) → Obs' σ S (VExpr.mkApps f args) o
  | _, _, _, _, .nil, h => h
  | _ :: _, a :: as, f, o, .cons ⟨h1, K', h2, h3⟩ H, h => by
    rw [wrap_cons] at h
    show Obs' σ S (VExpr.mkApps (.app f a) as) o
    exact obs_mkApps_of_wrap_le H (.app h h1 h2 h3)

/-- **Subsumption is inherited by applications**: if every observation of `f` is subsumed by
one of `f'`, every observation of `mkApps f args` is subsumed by one of `mkApps f' args`. -/
theorem Ob.Sub.mkApps {σ : VExpr.Subst} {S : ObSets} {f f' : VExpr}
    (h : Ob.Sub (Obs' σ S f) (Obs' σ S f')) (args : List VExpr) :
    Ob.Sub (Obs' σ S (.mkApps f args)) (Obs' σ S (.mkApps f' args)) := by
  intro o ho
  obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps_le ho
  obtain ⟨o', ho', l⟩ := h _ hw
  obtain ⟨keys', o'', rfl, hkk, l'⟩ := l.wrap_inv
  refine ⟨o'', obs_mkApps_of_wrap_le ?_ ho', l'⟩
  clear ho hw ho' l l'
  induction hkk generalizing args with
  | nil => cases hk; exact .nil
  | @cons k' k keys' keys hkk' _ ih =>
    cases hk with
    | cons ha hk =>
      refine .cons ⟨by rw [hkk'.2.1, hkk'.1]; exact ha.1, ?_⟩ (ih _ hk)
      obtain ⟨K', h1, h2⟩ := exists_list_cover (P := Obs' σ S _) (R := fun y x => y ≼ x)
        (L := k'.2.2) fun x hx => by
          obtain ⟨y, hy, l⟩ := hkk'.2.2 x hx
          obtain ⟨y', hy', l'⟩ := ha.2 y hy
          exact ⟨y', hy', l'.trans l⟩
      exact ⟨K', h1, h2⟩

/-! ## Sound inversions of a semantically typed spine -/

/-- Inversion of a constant: its derivation's type is soundly equal to the constant's type. -/
theorem HTS.const_inv' (H : HTS env U Δ Γ e T) (he : e = .const c ls) :
    ∃ ci, env.constants c = some ci ∧ ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
      Ob.Sub (Obs' σ S (ci.type.instL ls)) (Obs' σ S T) ∧
      Ob.Sub (Obs' σ S T) (Obs' σ S (ci.type.instL ls)) := by
  induction H with
  | const hci => cases he; exact ⟨_, hci, fun _ _ _ _ => ⟨Ob.Sub.refl, Ob.Sub.refl⟩⟩
  | conv _ hAB ih =>
    obtain ⟨ci, hci, h⟩ := ih he
    refine ⟨ci, hci, fun σ S W tv => ?_⟩
    have hs := SD.sub hAB W tv
    have := h σ S W tv
    exact ⟨this.1.trans hs.1, hs.2.trans this.2⟩
  | other h => exact absurd he (h c ls [])
  | bvar | app | lam | forallE | proj => cases he

/-- Inversion of the last application of a constant spine, with the sound equality between the
derivation's type and the instantiated codomain. -/
theorem HTS.app_const_inv' {c : Name} {ls : List VLevel} {pre : List VExpr} {a : VExpr}
    (H : HTS env U Δ Γ e T) (he : e = .mkApps (.const c ls) (pre ++ [a])) :
    ∃ A B u v, HTS env U Δ Γ (.mkApps (.const c ls) pre) (.forallE A B) ∧
      env.HasType U Γ (.mkApps (.const c ls) pre) (.forallE A B) ∧
      SD env U Δ Γ A A (.sort u) ∧ SD env U Δ (A :: Γ) B B (.sort v) ∧
      HTS env U Δ Γ a A ∧ SD env U Δ Γ a a A ∧
      ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
        Ob.Sub (Obs' σ S (B.inst a)) (Obs' σ S T) ∧ Ob.Sub (Obs' σ S T) (Obs' σ S (B.inst a)) := by
  rw [VExpr.mkApps_snoc] at he
  induction H with
  | app hA hB hf hfty ha hsa =>
    cases he
    exact ⟨_, _, _, _, hf, hfty, hA, hB, ha, hsa, fun _ _ _ _ => ⟨Ob.Sub.refl, Ob.Sub.refl⟩⟩
  | conv _ hAB ih =>
    obtain ⟨A, B, u, v, h1, h2, h3, h4, h5, h6, h⟩ := ih he
    refine ⟨A, B, u, v, h1, h2, h3, h4, h5, h6, fun σ S W tv => ?_⟩
    have hs := SD.sub hAB W tv
    have := h σ S W tv
    exact ⟨this.1.trans hs.1, hs.2.trans this.2⟩
  | other h =>
    exact absurd (he.trans (VExpr.mkApps_snoc _ _ _).symm) (h _ _ _)
  | bvar | const | lam | forallE | proj => cases he

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The valuation of a constant spine** (observation level): the observations of the type of
a semantically typed constant spine are, up to subsumption in both directions, those of the
residual telescope of the constant's type at the argument valuation. -/
theorem HTS.spineVal {Γ : List VExpr} {c : Name} {ls : List VLevel} {ci : VConstant}
    {Dw : List VExpr} {Rw : VExpr} (hci : env.constants c = some ci)
    (hTW : ci.type.instL ls = .wrapForalls Dw Rw) (hpi : PiSD env U Δ [] Dw Rw) :
    ∀ {args : List VExpr} {T : VExpr} {σ : VExpr.Subst} {S : ObSets},
    HTS env U Δ Γ (.mkApps (.const c ls) args) T → Ctx.SubstEq env U Δ σ σ Γ →
    TV env U Δ Γ σ S → args.length ≤ Dw.length →
    Ob.Sub (Obs' σ S T) (Obs' (VExpr.argSubst (args.map (·.subst σ)))
      (argSets env U Δ σ S args) (.wrapForalls (Dw.drop args.length) Rw)) ∧
    Ob.Sub (Obs' (VExpr.argSubst (args.map (·.subst σ))) (argSets env U Δ σ S args)
      (.wrapForalls (Dw.drop args.length) Rw)) (Obs' σ S T) := by
  have hTW' : Ob.Sub (Obs' .id .empty (ci.type.instL ls))
      (Obs' .id .empty (.wrapForalls Dw Rw)) := by rw [hTW]; exact Ob.Sub.refl
  have hcl : (VExpr.wrapForalls Dw Rw).ClosedN := hTW ▸ (henv.ordered.closedC hci).instL
  intro args
  induction args using List.reverseRecOn with
  | nil =>
    intro T σ S H W tv _
    obtain ⟨ci', hci', h⟩ := H.const_inv' rfl
    cases hci.symm.trans hci'
    have := h σ S W tv
    rw [hTW] at this
    simp only [List.map_nil, List.length_nil, List.drop_zero]
    refine ⟨fun o ho => ?_, fun o ho => ?_⟩
    · obtain ⟨o', ho', l⟩ := this.2 o ho
      exact ⟨o', (Obs.closed_iff_id hcl).2 ((Obs.closed_iff_id hcl).1 ho'), l⟩
    · exact this.1 o ((Obs.closed_iff_id hcl).2 ((Obs.closed_iff_id hcl).1 ho))
  | snoc pre a ih =>
    intro T σ S H W tv hn
    have hn' : pre.length + 1 ≤ Dw.length := by simpa using hn
    have hiD : pre.length < Dw.length := by omega
    obtain ⟨A, B, u, v, hf, -, hA, hB, -, hsa, hch⟩ := H.app_const_inv' rfl
    have IH := ih hf W tv (by omega)
    rw [List.drop_eq_getElem_cons hiD] at IH
    -- the argument valuation of the prefix
    obtain ⟨Wp, tvp⟩ := spine_tele_prefix henv hΔ H W tv hci hTW' hpi hn pre.length
      (by simp)
    rw [List.take_left' rfl] at Wp tvp
    have haσ : env.HasType U Δ (a.subst σ) (A.subst σ) :=
      hsa.1.defeq.hasType.1.substDF henv W.wf hΔ W
    have IHa := hsa.2 σ σ S W tv tv
    -- the domain at the prefix
    obtain ⟨hdTake, w, hDi⟩ := DomsSD.take_getElem hpi.doms _ hiD
    have hDiTy : env.HasType U (Dw.take pre.length).reverse Dw[pre.length] (.sort w) := by
      simpa using hDi.1.defeq.hasType.1
    obtain ⟨w', hR⟩ := PiSD.body_at hpi _ hiD
    have hctx : (Dw.take (pre.length + 1)).reverse ++ [] =
        Dw[pre.length] :: (Dw.take pre.length).reverse := by
      rw [List.take_succ_eq_append_getElem hiD]; simp
    rw [hctx] at hR
    have eD : TyCls env U Δ (A.subst σ) =
        TyCls env U Δ (Dw[pre.length].subst (VExpr.argSubst (pre.map (·.subst σ)))) :=
      spine_dom_cls henv hΔ hci hTW' hpi hiD W tv hf
    have IHdom : Ob.Sub (Obs' σ S A) (Obs' (VExpr.argSubst (pre.map (·.subst σ)))
        (argSets env U Δ σ S pre) Dw[pre.length]) := by
      intro x hx
      obtain ⟨o', ho', l⟩ := IH.1 _ (Obs.piDomOb (B := B) hx)
      obtain ⟨y, rfl, l'⟩ := l.piDomOb_inv
      exact ⟨y, Obs.piDomOb_mem (B := .wrapForalls (Dw.drop (pre.length + 1)) Rw) ho', l'⟩
    rw [List.map_append, List.map_singleton, VExpr.argSubst_append_one, argSets_snoc,
      List.length_append, List.length_singleton]
    refine ⟨fun y hy => ?_, fun z hz => ?_⟩
    · -- from the type of the spine to the residual telescope
      obtain ⟨y', hy', ly'⟩ := (hch σ S W tv).2 y hy
      have hy'' := Obs.inst_iff.1 hy'
      obtain ⟨K, hK, hbK, hyK⟩ := hy''.compact0B fun o h => Obs.backed h tv.1
      have hc := TypedElCls.of_hasType haσ
      obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge fun k hk => IHa.2.2.1 k (hK k hk)
      have hpiK : Obs' σ S (.forallE A B) (.piCodOb _ K y') :=
        .piCodOb hc hτk hkk hbK ElCls.self hyK
      obtain ⟨o', ho', lo'⟩ := IH.1 _ hpiK
      obtain ⟨K₀, y₀, rfl, hKK₀, ly₀⟩ := lo'.piCodOb_inv
      obtain ⟨hc', ⟨τk', hτk', hkk'⟩, z, hz, hyR⟩ := Obs.piCodOb_mem ho'
      have hza : env.IsDefEq U Δ z (a.subst σ)
          (Dw[pre.length].subst (VExpr.argSubst (pre.map (·.subst σ)))) :=
        hc'.defeq henv hΔ hz ElCls.self
      have hb₀ := Obs.piCodOb_backed ho'
      have hK₀' : ∀ k ∈ K₀, TypedAt env U Δ _ (VExpr.argSubst (pre.map (·.subst σ)))
          (argSets env U Δ σ S pre) Dw[pre.length] k := fun k hk => ⟨τk', hτk', hkk' k hk⟩
      have W' : Ctx.SubstEq env U Δ ((VExpr.argSubst (pre.map (·.subst σ))).cons z)
          ((VExpr.argSubst (pre.map (·.subst σ))).cons (a.subst σ))
          (Dw[pre.length] :: (Dw.take pre.length).reverse) :=
        .cons (by simpa using Wp) hDiTy (by simpa using hza)
      obtain ⟨y₁, hy₁, l₁⟩ := (hR.2 _ _ _ W' (tvp.cons_cls henv hΔ hc' hz hb₀ hK₀')
        (tvp.cons_cls henv hΔ hc' ElCls.self hb₀ hK₀')).1 _ hyR
      obtain ⟨y₂, hy₂, l₂⟩ := hy₁.mono_le (S' := (argSets env U Δ σ S pre).cons (Obs' σ S a))
        fun i o h => by
          cases i with
          | zero =>
            obtain ⟨k, hk, l⟩ := hKK₀ o h
            exact ⟨k, hK k hk, l⟩
          | succ i => exact ⟨o, h, .refl⟩
      exact ⟨y₂, hy₂, l₂.trans (l₁.trans (ly₀.trans ly'))⟩
    · -- from the residual telescope to the type of the spine
      obtain ⟨K₀, hK₀, hbK₀, hzK⟩ := hz.compact0B fun o h => Obs.backed h tv.1
      have hD' : TyCls env U Δ (Dw[pre.length].subst (VExpr.argSubst (pre.map (·.subst σ))))
          (A.subst σ) := by rw [← eD]; exact TyCls.self
      have haD : env.HasType U Δ (a.subst σ)
          (Dw[pre.length].subst (VExpr.argSubst (pre.map (·.subst σ)))) :=
        TyCls.defeq henv hΔ hD' haσ
      have hc := TypedElCls.of_hasType haD
      have ecls : vcls env U Δ σ a A = ElCls env U Δ
          (TyCls env U Δ (Dw[pre.length].subst (VExpr.argSubst (pre.map (·.subst σ)))))
          (a.subst σ) := by unfold vcls; rw [eD]
      have hK₀' : ∀ k ∈ K₀, TypedAt env U Δ _ (VExpr.argSubst (pre.map (·.subst σ)))
          (argSets env U Δ σ S pre) Dw[pre.length] k := fun k hk =>
        ((IHa.2.2.1 k (hK₀ k hk)).mono_le IHdom).congr_cls ecls
      obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK₀'
      have hpi0 : Obs' (VExpr.argSubst (pre.map (·.subst σ))) (argSets env U Δ σ S pre)
          (.forallE Dw[pre.length] (.wrapForalls (Dw.drop (pre.length + 1)) Rw))
          (.piCodOb _ K₀ z) :=
        .piCodOb hc hτk hkk hbK₀ ElCls.self hzK
      obtain ⟨o', ho', lo'⟩ := IH.2 _ hpi0
      obtain ⟨K₁, z₁, rfl, hKK₁, lz₁⟩ := lo'.piCodOb_inv
      obtain ⟨hcA, ⟨τ₁, hτ₁, hk₁⟩, x, hx, hxB⟩ := Obs.piCodOb_mem ho'
      have hxa : env.IsDefEq U Δ x (a.subst σ) (A.subst σ) := hcA.defeq henv hΔ hx ElCls.self
      have hb₁ := Obs.piCodOb_backed ho'
      have hK₁' : ∀ k ∈ K₁, TypedAt env U Δ _ σ S A k := fun k hk => ⟨τ₁, hτ₁, hk₁ k hk⟩
      have W' : Ctx.SubstEq env U Δ (σ.cons x) (σ.cons (a.subst σ)) (A :: Γ) :=
        .cons W hA.1.defeq.hasType.1 hxa
      obtain ⟨z₂, hz₂, l₂⟩ := (hB.2 _ _ _ W' (tv.cons_cls henv hΔ hcA hx hb₁ hK₁')
        (tv.cons_cls henv hΔ hcA ElCls.self hb₁ hK₁')).1 _ hxB
      obtain ⟨z₃, hz₃, l₃⟩ := hz₂.mono_le (S' := S.cons (Obs' σ S a)) fun i o h => by
        cases i with
        | zero =>
          obtain ⟨k, hk, l⟩ := hKK₁ o h
          exact ⟨k, hK₀ k hk, l⟩
        | succ i => exact ⟨o, h, .refl⟩
      obtain ⟨z₄, hz₄, l₄⟩ := (hch σ S W tv).1 _ (Obs.inst_iff.2 hz₃)
      exact ⟨z₄, hz₄, l₄.trans (l₃.trans (l₂.trans lz₁))⟩

/-- **The domain at an argument of a constant spine** (observation level): the observations of
the derivation's domain for the next argument are those of the telescope's domain at the
argument valuation of the prefix. -/
theorem HTS.spineVal_dom {Γ : List VExpr} {c : Name} {ls : List VLevel} {ci : VConstant}
    {Dw : List VExpr} {Rw : VExpr} (hci : env.constants c = some ci)
    (hTW : ci.type.instL ls = .wrapForalls Dw Rw) (hpi : PiSD env U Δ [] Dw Rw)
    {pre : List VExpr} {A B : VExpr} {σ : VExpr.Subst} {S : ObSets}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) pre) (.forallE A B))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) (hiD : pre.length < Dw.length) :
    Ob.Sub (Obs' σ S A) (Obs' (VExpr.argSubst (pre.map (·.subst σ)))
      (argSets env U Δ σ S pre) Dw[pre.length]) ∧
    Ob.Sub (Obs' (VExpr.argSubst (pre.map (·.subst σ))) (argSets env U Δ σ S pre) Dw[pre.length])
      (Obs' σ S A) := by
  have IH := HTS.spineVal henv hΔ hci hTW hpi H W tv (Nat.le_of_lt hiD)
  rw [List.drop_eq_getElem_cons hiD] at IH
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨o', ho', l⟩ := IH.1 _ (Obs.piDomOb (B := B) hx)
    obtain ⟨y, rfl, l'⟩ := l.piDomOb_inv
    exact ⟨y, Obs.piDomOb_mem (B := .wrapForalls (Dw.drop (pre.length + 1)) Rw) ho', l'⟩
  · obtain ⟨o', ho', l⟩ := IH.2 _
      (Obs.piDomOb (B := .wrapForalls (Dw.drop (pre.length + 1)) Rw) hx)
    obtain ⟨y, rfl, l'⟩ := l.piDomOb_inv
    exact ⟨y, Obs.piDomOb_mem (B := B) ho', l'⟩

end

end Model
end VEnv
end Lean4Lean
