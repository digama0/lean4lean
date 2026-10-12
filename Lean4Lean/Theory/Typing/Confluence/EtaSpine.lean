import Lean4Lean.Theory.Typing.Confluence.JoinLemmas

/-! # Reducts of rigid spines

A reduct of an application of a rigid constant need not be an application of that constant:
function eta expansion (`FullStep.funEta`) of a partial application produces a lambda, which a
later beta step may contract again. `EtaSpine c ls Γ e as n` describes the terms reachable from
the spine `c as`: spines of `c` at reducts of `as`, applications of such terms, and eta
expansions (`n` counts the expansions). The class is closed under full reduction
(`EtaSpine.fullReduction`), and every member reduces to a spine or to an eta expansion
(`EtaSpine.normalize`). With spine exposure through normal equality
(`NormalEqN.spine_expose`) this gives **injectivity of joins of rigid spines**
(`FullCRDefEq.rigid_spine_inv`). -/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

omit [Params] in
theorem List.forall₂_map_both {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ a b, R a b → S (f a) (g b)) : ∀ {l₁ l₂}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S (l₁.map f) (l₂.map g)
  | _, _, .nil => .nil
  | _, _, .cons hab hs => .cons (h _ _ hab) (List.forall₂_map_both h hs)

omit [Params] in
theorem List.forall₂_snoc_right' {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {b : β}, List.Forall₂ R l₁ (l₂ ++ [b]) →
      ∃ l₁' a, l₁ = l₁' ++ [a] ∧ List.Forall₂ R l₁' l₂ ∧ R a b
  | _, [], _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _, _ :: _, _, .cons h hs =>
    let ⟨l, a, e, h1, h2⟩ := List.forall₂_snoc_right' hs
    ⟨_ :: l, a, by simp [e], .cons h h1, h2⟩

omit [Params] in
theorem List.forall₂_snoc_left' {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {a : α}, List.Forall₂ R (l₁ ++ [a]) l₂ →
      ∃ l₂' b, l₂ = l₂' ++ [b] ∧ List.Forall₂ R l₁ l₂' ∧ R a b
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h hs =>
    let ⟨l, b, e, h1, h2⟩ := List.forall₂_snoc_left' hs
    ⟨_ :: l, b, by simp [e], .cons h h1, h2⟩

omit [Params] in
theorem mkApps_ne_proj' {fn : VExpr} (args : List VExpr) (hf : ∀ n i e, fn ≠ .proj n i e := by
    intro _ _ _ h; nomatch h) :
    VExpr.mkApps fn args ≠ .proj family index major := by
  induction args generalizing fn with
  | nil => exact hf _ _ _
  | cons _ _ ih => exact ih (fn := .app _ _) nofun

section
variable (c : Name) (ls : List VLevel)

/-- Terms reachable by full reduction from the spine `c as` (indexed by the original
arguments `as`; `n` counts the eta expansions). -/
inductive EtaSpine : List VExpr → VExpr → List VExpr → Nat → Prop where
  | spine : List.Forall₂ (FullReduction Γ) as bs →
      EtaSpine Γ (VExpr.mkApps (.const c ls) bs) as 0
  | app : EtaSpine Γ f as n → FullReduction Γ a b → EtaSpine Γ (.app f b) (as ++ [a]) n
  | eta : Γ ⊢ A : .sort u → Γ ⊢ VExpr.mkApps (.const c ls) as : .forallE A B →
      EtaSpine (A :: Γ) body (as.map VExpr.lift ++ [.bvar 0]) n →
      EtaSpine Γ (.lam A body) as (n + 1)
end

/-- The arguments are typed. -/
def TypedArgs (Γ : List VExpr) (as : List VExpr) : Prop := ∀ a ∈ as, ∃ T, Γ ⊢ a : T

theorem TypedArgs.append {Γ : List VExpr} {as bs : List VExpr} :
    TypedArgs Γ (as ++ bs) ↔ TypedArgs Γ as ∧ TypedArgs Γ bs := by
  simp only [TypedArgs, List.mem_append]
  exact ⟨fun h => ⟨fun a ha => h a (.inl ha), fun a ha => h a (.inr ha)⟩,
    fun h a ha => ha.elim (h.1 a) (h.2 a)⟩

theorem TypedArgs.lift_bvar {Γ : List VExpr} {as : List VExpr} (h : TypedArgs Γ as) : TypedArgs (A :: Γ) (as.map VExpr.lift ++ [.bvar 0]) := by
  refine TypedArgs.append.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨_, h⟩ := h x hx
    exact ⟨_, h.weak henv.ordered⟩
  · simp at ha; subst ha; exact ⟨_, .bvar .zero⟩

theorem FullReduction.forall₂_defeq (hΓ : OnCtx Γ (env.IsType univs)) :
    List.Forall₂ (FullReduction Γ) as₀ as → TypedArgs Γ as₀ →
      List.Forall₂ (IsDefEqU env univs Γ) as as₀
  | .nil, _ => .nil
  | .cons h hs, ht =>
    let ⟨_, hT⟩ := ht _ (List.mem_cons_self ..)
    .cons ⟨_, (FullReduction.defeq hΓ h hT).symm⟩
      (FullReduction.forall₂_defeq hΓ hs fun a ha => ht a (List.mem_cons_of_mem _ ha))

theorem FullReduction.forall₂_rfl : ∀ (l : List VExpr), List.Forall₂ (FullReduction Γ) l l
  | [] => .nil
  | _ :: l => .cons .rfl (FullReduction.forall₂_rfl l)

theorem EtaSpine.weakN (W : Ctx.LiftN k j Γ Γ') (H : EtaSpine c ls Γ e as n) :
    EtaSpine c ls Γ' (e.liftN k j) (as.map (·.liftN k j)) n := by
  induction H generalizing j Γ' with
  | spine h =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .spine (List.forall₂_map_both (fun _ _ h => h.weakN W) h)
  | app _ hr ih =>
    simp only [VExpr.liftN, List.map_append, List.map_cons, List.map_nil]
    exact .app (ih W) (hr.weakN W)
  | eta hA hp _ ih =>
    have hp' := hp.weakN henv.ordered W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at hp'
    have := ih W.succ
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      ← VExpr.lift_liftN'] at this
    simp only [VExpr.liftN]
    refine .eta (hA.weakN henv.ordered W) hp' ?_
    simpa [VExpr.liftN, liftVar, Function.comp_def] using this

theorem EtaSpine.instN (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ) (ha : Γ₀ ⊢ a : A₀)
    (H : EtaSpine c ls Γ₁ e as n) :
    EtaSpine c ls Γ (e.inst a k) (as.map (·.inst a k)) n := by
  induction H generalizing k Γ with
  | spine h =>
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .spine (List.forall₂_map_both (fun _ _ h => h.instN W ha) h)
  | app _ hr ih =>
    simp only [VExpr.inst, List.map_append, List.map_cons, List.map_nil]
    exact .app (ih W) (hr.instN W ha)
  | eta hA hp _ ih =>
    have hp' := hp.instN henv.ordered W ha
    simp only [VExpr.inst_mkApps, VExpr.inst] at hp'
    have := ih W.succ
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      ← VExpr.lift_instN_lo] at this
    simp only [VExpr.inst]
    refine .eta (hA.instN henv.ordered W ha) hp' ?_
    simpa [VExpr.inst, instVar, Function.comp_def] using this

theorem EtaSpine.pre (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaSpine c ls Γ e as n)
    (hpre : List.Forall₂ (FullReduction Γ) as₀ as) (ht : TypedArgs Γ as₀) :
    EtaSpine c ls Γ e as₀ n := by
  induction H generalizing as₀ with
  | spine h => exact .spine (Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') hpre h)
  | app _ hr ih =>
    obtain ⟨as₁, a₁, rfl, h1, h2⟩ := List.forall₂_snoc_right' hpre
    have := TypedArgs.append.1 ht
    exact .app (ih hΓ h1 this.1) (h2.trans hr)
  | @eta Γ A u as B body n hA hp _ ih =>
    have hdef := FullReduction.forall₂_defeq hΓ hpre ht
    obtain ⟨_, hc⟩ := mkApps_head_type hΓ hp
    have hp' : Γ ⊢ VExpr.mkApps (.const c ls) as₀ : .forallE A B :=
      hp.defeqU_l henv hΓ (IsDefEqU.mkApps_args hΓ ⟨_, hc⟩ hdef hp)
    refine .eta hA hp' (ih ⟨hΓ, _, hA⟩ ?_ ht.lift_bvar)
    exact List.Forall₂.append' (List.forall₂_map_both (fun _ _ h => h.weakN .one) hpre)
      (.cons .rfl .nil)

theorem EtaSpine.defeqDFC (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (H : EtaSpine c ls Γ₁ e as n) (ht : TypedArgs Γ₁ as) :
    EtaSpine c ls Γ₂ e as n := by
  induction H generalizing Γ₂ with
  | spine h =>
    refine .spine ?_
    induction h with
    | nil => exact .nil
    | cons h _ ih =>
      obtain ⟨_, hT⟩ := ht _ (List.mem_cons_self ..)
      exact .cons (h.defeqDFC hΓ₀ W hT) (ih fun a ha => ht a (List.mem_cons_of_mem _ ha))
  | app _ hr ih =>
    have := TypedArgs.append.1 ht
    obtain ⟨_, hT⟩ := this.2 _ (List.mem_singleton_self _)
    exact .app (ih W this.1) (hr.defeqDFC hΓ₀ W hT)
  | eta hA hp _ ih =>
    exact .eta (hA.defeqDFC henv.ordered W) (hp.defeqDFC henv.ordered W)
      (ih (W.succ hA) ht.lift_bvar)

omit [Params] in
theorem mkApps_lift_bvar (h : VExpr) (as : List VExpr) (hc : h.lift = h) :
    VExpr.mkApps h (as.map VExpr.lift ++ [.bvar 0]) = .app (VExpr.mkApps h as).lift (.bvar 0) := by
  rw [VExpr.mkApps_snoc]; congr 1
  have : (VExpr.mkApps h as).lift = VExpr.mkApps h.lift (as.map VExpr.lift) := by
    simp [VExpr.lift, VExpr.liftN_mkApps]
  rw [this, hc]

/-- An eta spine is definitionally equal to the spine at its original arguments. -/
theorem EtaSpine.defeq (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaSpine c ls Γ e as n)
    (ht : TypedArgs Γ as) (he : Γ ⊢ e : T) : Γ ⊢ e ≡ VExpr.mkApps (.const c ls) as := by
  induction H generalizing T with
  | spine h =>
    obtain ⟨_, hc⟩ := mkApps_head_type hΓ he
    exact IsDefEqU.mkApps_args hΓ ⟨_, hc⟩ (FullReduction.forall₂_defeq hΓ h ht) he
  | @app Γ f as n a b _ hr ih =>
    have := TypedArgs.append.1 ht
    obtain ⟨_, ha⟩ := this.2 _ (List.mem_singleton_self _)
    obtain ⟨X, Y, hf, hb⟩ := he.app_inv henv.orderedStrong hΓ
    have h1 := (ih hΓ this.1 hf).of_l henv hΓ hf
    have h2 : Γ ⊢ b ≡ a : X := IsDefEqU.of_l henv hΓ ⟨_, (FullReduction.defeq hΓ hr ha).symm⟩ hb
    rw [VExpr.mkApps_snoc]
    exact ⟨_, .appDF h1 h2⟩
  | @eta Γ A u as B body n hA hp _ ih =>
    obtain ⟨_, _, hbody⟩ := he.lam_inv henv.orderedStrong hΓ
    have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have h1 := (ih hΓ' ht.lift_bvar hbody).of_l henv hΓ' hbody
    rw [mkApps_lift_bvar _ _ rfl] at h1
    exact IsDefEqU.trans henv hΓ ⟨_, IsDefEq.lamDF hA h1⟩ ⟨_, .eta hp⟩

omit [Params] in
theorem getAppFnArgs_app_fst (f a : VExpr) :
    (VExpr.app f a).getAppFnArgs.1 = f.getAppFnArgs.1 :=
  VExpr.getAppFnArgs_mkApps_head f [a]

theorem EtaSpine.head (H : EtaSpine c ls Γ e as n) (hh : e.getAppFnArgs.1 = .const name us) :
    name = c ∧ us = ls := by
  induction H with
  | spine =>
    rw [VExpr.getAppFnArgs_mkApps_head] at hh
    cases hh; exact ⟨rfl, rfl⟩
  | app _ _ ih => exact ih ((getAppFnArgs_app_fst _ _).symm.trans hh)
  | eta => cases hh

theorem EtaSpine.not_proj (H : EtaSpine c ls Γ e as n) : e ≠ .proj family index major := by
  cases H with
  | spine => exact mkApps_ne_proj' _
  | app => nofun
  | eta => nofun

theorem EtaSpine.not_forallE (H : EtaSpine c ls Γ e as n) : e ≠ .forallE A B := by
  cases H with
  | spine => exact VExpr.mkApps_ne_forallE (fn := .const _ _) (fun _ _ h => nomatch h) _
  | app => nofun
  | eta => nofun

/-! ## Inversion -/

theorem EtaSpine.app_inv (H : EtaSpine c ls Γ (.app f b) as n) :
    ∃ as₀ a, as = as₀ ++ [a] ∧ EtaSpine c ls Γ f as₀ n ∧ FullReduction Γ a b := by
  generalize he : VExpr.app f b = e at H
  cases H with
  | spine h =>
    obtain ⟨init, rfl, rfl⟩ := RigidHead.const.mkApps_eq_app he.symm
    obtain ⟨as₀, a, rfl, h1, h2⟩ := List.forall₂_snoc_right' h
    exact ⟨as₀, a, rfl, .spine h1, h2⟩
  | app H hr => cases he; exact ⟨_, _, rfl, H, hr⟩
  | eta => cases he

theorem EtaSpine.lam_inv (H : EtaSpine c ls Γ (.lam A body) as n) :
    ∃ u B m, n = m + 1 ∧ Γ ⊢ A : .sort u ∧
      Γ ⊢ VExpr.mkApps (.const c ls) as : .forallE A B ∧
      EtaSpine c ls (A :: Γ) body (as.map VExpr.lift ++ [.bvar 0]) m := by
  generalize he : VExpr.lam A body = e at H
  cases H with
  | spine => exact absurd he.symm (VExpr.mkApps_ne_lam (fn := .const _ _) (fun _ _ h => nomatch h) _)
  | app => cases he
  | eta hA hp H => cases he; exact ⟨_, _, _, rfl, hA, hp, H⟩

/-- The constant heads a syntactic telescope ending in a sort, in every context. -/
def SortHeaded (c : Name) (ls : List VLevel) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → ∃ doms w, Γ ⊢ .const c ls : VExpr.wrapForalls doms (.sort w)

/-- An application of a function typed by a telescope ending in a sort is not typed by an
application of a rigid constant. -/
theorem HasType.sortTele_not_rigid (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.Rigid S) :
    ∀ {as : List VExpr} {f : VExpr} {doms : List VExpr} {w : VLevel},
      Γ ⊢ f : VExpr.wrapForalls doms (.sort w) →
      Γ ⊢ VExpr.mkApps f as : VExpr.mkApps (.const S lv) ps → False := by
  intro as
  induction as with
  | nil =>
    intro f doms w hf ht
    have hu := hf.uniqU henv hΓ ht
    have ⟨_, hT⟩ := ht.isType henv.ordered hΓ
    cases doms with
    | nil =>
      exact henv.headInversion.sort_rigid hΓ hS (hu.symm.typeChain henv hΓ hT).symm
    | cons d ds =>
      exact IsDefEqU.rigidApp_forallE_inv henv hΓ hS hT hu.symm
  | cons a as ih =>
    intro f doms w hf ht
    have hfa : VExpr.WF env univs Γ (.app f a) :=
      VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app f a) ⟨_, ht⟩
    rcases hfa.app_inv henv.orderedStrong hΓ with ⟨A, B, hfun, harg⟩
    cases doms with
    | nil => exact (IsDefEqU.sort_forallE_inv henv hΓ (hf.uniqU henv hΓ hfun)).elim
    | cons d ds =>
      rcases (hf.uniqU henv hΓ hfun).forallE_inv henv hΓ with ⟨⟨_, hd⟩, _⟩
      have ha := harg.defeqU_r henv hΓ ⟨_, hd.symm⟩
      have hfa' := hf.app ha
      change Γ ⊢ .app f a : (VExpr.wrapForalls ds (.sort w)).inst a at hfa'
      rw [VExpr.wrapForalls_inst] at hfa'
      exact ih hfa' ht

theorem EtaSpine.not_struct (hS : SortHeaded c ls) (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaSpine c ls Γ e as n) (ht : TypedArgs Γ as) (hl : env.projections family info)
    (he : Γ ⊢ e : VExpr.mkApps (.const family levels) params) : False := by
  have hI := he.defeqU_l henv hΓ (H.defeq hΓ ht he)
  obtain ⟨doms, w, hc⟩ := hS hΓ
  exact HasType.sortTele_not_rigid hΓ (henv.projectionRigid hl) hc hI

/-! ## Closure under reduction -/

theorem EtaSpine.parRed (hrig : env.Rigid c) (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaSpine c ls Γ e as n) (ht : TypedArgs Γ as) (he : Γ ⊢ e : T)
    (R : ParRed Γ e e') : ∃ n', EtaSpine c ls Γ e' as n' := by
  induction H generalizing e' T with
  | spine h =>
    obtain ⟨bs', rfl, hbs⟩ := ParRed.rigid_const_spine hrig R
    refine ⟨0, .spine ?_⟩
    exact Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.tail (.core h')) h hbs
  | @app Γ f as n a b Hf hr ih =>
    have hta := TypedArgs.append.1 ht
    obtain ⟨X, Y, hf, hb⟩ := he.app_inv henv.orderedStrong hΓ
    cases R with
    | app Rf Rb =>
      obtain ⟨n', H'⟩ := ih hΓ hta.1 hf Rf
      exact ⟨n', .app H' (hr.tail (.core Rb))⟩
    | beta Rbody Rb =>
      obtain ⟨n', Hl⟩ := ih hΓ hta.1 hf (.lam .rfl Rbody)
      obtain ⟨u, B, m, rfl, hA, hp, Hbody⟩ := Hl.lam_inv
      obtain ⟨Y', hY', hbody⟩ := hf.lam_inv_forallE henv hΓ
      have ⟨⟨_, hXA⟩, _⟩ := hY'.symm.forallE_inv henv hΓ
      have hb' := (Rb.hasType hΓ hb).defeqU_r henv hΓ ⟨_, hXA⟩
      have H' := Hbody.instN .zero hb'
      simp only [List.map_append, List.map_map, Function.comp_def, VExpr.inst_lift,
        List.map_id', List.map_cons, List.map_nil] at H'
      simp only [VExpr.inst, instVar, Nat.lt_irrefl, if_false, VExpr.liftN_zero] at H'
      refine ⟨_, H'.pre hΓ ?_ ht⟩
      exact List.Forall₂.append' (FullReduction.forall₂_rfl _) (.cons (hr.tail (.core Rb)) .nil)
    | extra hp hm =>
      obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
      obtain ⟨rfl, -⟩ := (EtaSpine.app Hf hr).head hh
      exact (Params.not_rigid_match hrig hp hm hh).elim
  | @eta Γ A u as B body n hA hp Hb ih =>
    obtain ⟨_, _, hbody⟩ := he.lam_inv henv.orderedStrong hΓ
    cases R with
    | lam RA Rbody =>
      have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
      obtain ⟨n', H'⟩ := ih hΓ' ht.lift_bvar hbody Rbody
      have hAA := RA.defeq hΓ hA
      obtain ⟨_, hPi⟩ := hp.isType henv.ordered hΓ
      obtain ⟨-, _, hB⟩ := hPi.forallE_inv henv.ordered
      have hpi := IsDefEq.forallEDF hAA hB
      exact ⟨n' + 1, .eta hAA.hasType.2 (.defeqDF hpi hp)
        (H'.defeqDFC hΓ (.succ .zero hAA) ht.lift_bvar)⟩
    | extra hp hm =>
      obtain ⟨_, hh⟩ := (Params.constHeaded hp).matches_head hm
      cases hh
    | _ => skip

theorem EtaSpine.fullStep (hrig : env.Rigid c) (hS : SortHeaded c ls) (R : FullStep Γ e e') :
    ∀ {as n T}, OnCtx Γ (env.IsType univs) → EtaSpine c ls Γ e as n → TypedArgs Γ as →
      Γ ⊢ e : T → ∃ n', EtaSpine c ls Γ e' as n' := by
  induction R with
  | core h => intro _ _ _ hΓ H ht he; exact H.parRed hrig hΓ ht he h
  | delta hpu =>
    intro _ _ _ hΓ H ht he
    obtain ⟨rfl, -⟩ := H.head (by rw [VExpr.getAppFnArgs_mkApps_head]; rfl)
    exact (hpu.not_rigid hrig).elim
  | quotDelta hq =>
    intro _ _ _ hΓ H ht he
    obtain ⟨rfl, -⟩ := H.head (by rw [VExpr.getAppFnArgs_mkApps_head]; rfl)
    exact (hq.not_rigid hrig).elim
  | projIota => intro _ _ _ hΓ H; exact (H.not_proj rfl).elim
  | structEta hl _ _ hs _ => intro _ _ _ hΓ H ht; exact (H.not_struct hS hΓ ht hl hs).elim
  | @funEta Γ e d b hpi =>
    intro as n _ hΓ H ht he
    obtain ⟨_, hT⟩ := hpi.isType henv.ordered hΓ
    obtain ⟨⟨_, hd⟩, -⟩ := hT.forallE_inv henv.ordered
    have hI := hpi.defeqU_l henv hΓ (H.defeq hΓ ht hpi)
    refine ⟨n + 1, .eta hd hI ?_⟩
    exact .app (H.weakN (Ctx.LiftN.one (A := d))) .rfl
  | app Rf Ra ihf _ =>
    intro _ _ _ hΓ H ht he
    obtain ⟨as₀, a, rfl, Hf, hr⟩ := H.app_inv
    obtain ⟨X, Y, hf, hb⟩ := he.app_inv henv.orderedStrong hΓ
    obtain ⟨n', H'⟩ := ihf hΓ Hf (TypedArgs.append.1 ht).1 hf
    exact ⟨n', .app H' (hr.tail Ra)⟩
  | proj => intro _ _ _ hΓ H; exact (H.not_proj rfl).elim
  | lam Rd _ _ ihb =>
    intro _ _ _ hΓ H ht he
    obtain ⟨u, B, m, rfl, hA, hp, Hb⟩ := H.lam_inv
    obtain ⟨_, _, hbody⟩ := he.lam_inv henv.orderedStrong hΓ
    obtain ⟨m', Hb'⟩ := ihb ⟨hΓ, _, hA⟩ Hb ht.lift_bvar hbody
    have hAA := Rd.defeq hΓ hA
    obtain ⟨_, hPi⟩ := hp.isType henv.ordered hΓ
    obtain ⟨-, _, hB⟩ := hPi.forallE_inv henv.ordered
    have hpi := IsDefEq.forallEDF hAA hB
    exact ⟨m' + 1, .eta hAA.hasType.2 (.defeqDF hpi hp)
      (Hb'.defeqDFC hΓ (.succ .zero hAA) ht.lift_bvar)⟩
  | forallE => intro _ _ _ hΓ H; exact (H.not_forallE rfl).elim

theorem EtaSpine.fullReduction (hrig : env.Rigid c) (hS : SortHeaded c ls)
    (hΓ : OnCtx Γ (env.IsType univs)) (R : FullReduction Γ e e')
    (H : EtaSpine c ls Γ e as n) (ht : TypedArgs Γ as) (he : Γ ⊢ e : T) :
    ∃ n', EtaSpine c ls Γ e' as n' := by
  induction R with
  | rfl => exact ⟨_, H⟩
  | tail before step ih =>
    obtain ⟨_, H₀⟩ := ih
    exact EtaSpine.fullStep hrig hS step hΓ H₀ ht (FullReduction.hasType hΓ before he)

/-! ## Normal forms -/

/-- The normal form of a member: a reduct that is a spine at reducts of the original arguments,
or an eta expansion with fewer expansions. -/
def EtaSpine.NF (c : Name) (ls : List VLevel) (Γ : List VExpr) (e : VExpr) (as : List VExpr)
    (n : Nat) : Prop :=
  (∃ bs, FullReduction Γ e (VExpr.mkApps (.const c ls) bs) ∧ List.Forall₂ (FullReduction Γ) as bs) ∨
  (∃ A body m, m < n ∧ FullReduction Γ e (.lam A body) ∧
    EtaSpine c ls (A :: Γ) body (as.map VExpr.lift ++ [.bvar 0]) m)

theorem EtaSpine.normalize_aux (hΓ : OnCtx Γ (env.IsType univs))
    (outer : ∀ m e as T, m < N → EtaSpine c ls Γ e as m → TypedArgs Γ as → Γ ⊢ e : T →
      EtaSpine.NF c ls Γ e as m)
    (H : EtaSpine c ls Γ e as n) (hn : n ≤ N) (ht : TypedArgs Γ as) (he : Γ ⊢ e : T) :
    EtaSpine.NF c ls Γ e as n := by
  induction H generalizing T with
  | spine h => exact .inl ⟨_, .rfl, h⟩
  | eta _ _ Hb => exact .inr ⟨_, _, _, Nat.lt_succ_self _, .rfl, Hb⟩
  | @app Γ f as₀ n a b Hf hr ih =>
    have hta := TypedArgs.append.1 ht
    obtain ⟨X, Y, hf, hb⟩ := he.app_inv henv.orderedStrong hΓ
    rcases ih hΓ outer hn hta.1 hf with ⟨bs, r, hbs⟩ | ⟨A, body, m, hm, r, Hbody⟩
    · refine .inl ⟨bs ++ [b], ?_, List.Forall₂.append' hbs (.cons hr .nil)⟩
      rw [VExpr.mkApps_snoc]; exact r.app .rfl
    · have r1 : FullReduction Γ (.app f b) (.app (.lam A body) b) := r.app .rfl
      have hβ := (FullReduction.hasType hΓ r1 he)
      obtain ⟨X', Y', hl, hb'⟩ := hβ.app_inv henv.orderedStrong hΓ
      obtain ⟨Y'', hY, _⟩ := hl.lam_inv_forallE henv hΓ
      have ⟨⟨_, hAX⟩, _⟩ := hY.forallE_inv henv hΓ
      have hbA : Γ ⊢ b : A := hb'.defeqU_r henv hΓ ⟨_, hAX.symm⟩
      have H' := Hbody.instN .zero hbA
      simp only [List.map_append, List.map_map, Function.comp_def, VExpr.inst_lift,
        List.map_id', List.map_cons, List.map_nil, VExpr.inst, instVar, Nat.lt_irrefl, if_false,
        VExpr.liftN_zero] at H'
      have H'' := H'.pre hΓ (List.Forall₂.append' (FullReduction.forall₂_rfl _)
        (.cons hr .nil)) ht
      have r2 : FullReduction Γ (.app f b) (body.inst b) :=
        r1.tail (.core (.beta .rfl .rfl))
      rcases outer m _ _ _ (by omega) H'' ht (FullReduction.hasType hΓ r2 he) with
        ⟨bs, r', hbs⟩ | ⟨A', body', m', hm', r', Hb'⟩
      · exact .inl ⟨bs, r2.trans r', hbs⟩
      · exact .inr ⟨A', body', m', by omega, r2.trans r', Hb'⟩

theorem EtaSpine.normalize (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n {e as T}, EtaSpine c ls Γ e as n → TypedArgs Γ as → Γ ⊢ e : T →
      EtaSpine.NF c ls Γ e as n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro e as T H ht he
    exact H.normalize_aux hΓ (fun m _ _ _ hm H ht he => ih m hm H ht he) (Nat.le_refl _) ht he

theorem EtaSpine.spine_inv :
    ∀ {bs as n}, EtaSpine c ls Γ (VExpr.mkApps (.const c' ls') bs) as n →
      c' = c ∧ ls' = ls ∧ List.Forall₂ (FullReduction Γ) as bs := by
  intro bs
  induction bs using List.snoc_induction with
  | nil =>
    intro as n H
    generalize he : VExpr.mkApps (.const c' ls') [] = e at H
    cases H with
    | @spine _ _ bs₀ h =>
      rcases List.eq_nil_or_snoc bs₀ with rfl | ⟨bs₁, b, rfl⟩
      · cases he; exact ⟨rfl, rfl, h⟩
      · rw [VExpr.mkApps_snoc] at he; cases he
    | app => cases he
    | eta => cases he
  | snoc bs b ih =>
    intro as n H
    rw [VExpr.mkApps_snoc] at H
    obtain ⟨as₀, a, rfl, Hf, hr⟩ := H.app_inv
    obtain ⟨rfl, rfl, h⟩ := ih Hf
    exact ⟨rfl, rfl, List.Forall₂.append' h (.cons hr .nil)⟩

/-! ## Injectivity of joins of rigid spines -/

omit [Params] in
theorem List.forall₂_join3 {R1 R2 R3 : α → α → Prop} :
    ∀ {as as' ts bs : List α}, List.Forall₂ R1 as as' → List.Forall₂ R3 ts as' →
      List.Forall₂ R2 bs ts → List.Forall₂ (fun a b => ∃ a' t, R1 a a' ∧ R2 b t ∧ R3 t a') as bs
  | _, _, _, _, .nil, .nil, .nil => .nil
  | _, _, _, _, .cons h1 h1s, .cons h3 h3s, .cons h2 h2s =>
    .cons ⟨_, _, h1, h2, h3⟩ (List.forall₂_join3 h1s h3s h2s)

omit [Params] in
theorem List.forall₂_imp_mem {R S : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
      (∀ a ∈ as, ∀ b ∈ bs, R a b → S a b) → List.Forall₂ S as bs
  | _, _, .nil, _ => .nil
  | _, _, .cons h hs, H =>
    .cons (H _ (List.mem_cons_self ..) _ (List.mem_cons_self ..) h)
      (List.forall₂_imp_mem hs fun a ha b hb => H a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb))

theorem HasType.sort_not_proof (hΓ : OnCtx Γ (env.IsType univs))
    (hT : Γ ⊢ e : .sort u) (hp : Γ ⊢ .sort u : .sort .zero) : False := by
  have ⟨_, hS⟩ := hT.isType henv.ordered hΓ
  have := IsDefEqU.sort_inv henv hΓ (IsDefEq.uniqU henv hΓ (HasType.sort (hS.sort_inv henv.ordered)) hp)
  exact absurd (congrFun this []) (by simp [VLevel.eval])

theorem HasType.sort_not_lam (hΓ : OnCtx Γ (env.IsType univs))
    (hT : Γ ⊢ .lam A body : .sort u) : False := by
  obtain ⟨_, hY, _⟩ := hT.lam_inv_forallE henv hΓ
  exact IsDefEqU.sort_forallE_inv henv hΓ hY.symm

/-- **Injectivity of joins of rigid spines.** Two joinable applications of a rigid constant
typed by a sort have pairwise joinable arguments. -/
theorem FullCRDefEq.rigid_spine_inv (hΓ : OnCtx Γ (env.IsType univs)) (hrig : env.Rigid c)
    (hS : SortHeaded c ls) (hS' : SortHeaded c ls')
    (hT : Γ ⊢ VExpr.mkApps (.const c ls) as : .sort u)
    (H : Γ ⊢ VExpr.mkApps (.const c ls) as ≫≪ VExpr.mkApps (.const c ls') bs) :
    List.Forall₂ (FullCRDefEq Γ) as bs := by
  have hRs : Γ ⊢ VExpr.mkApps (.const c ls') bs : .sort u := hT.defeqU_l henv hΓ (H.defeq hΓ)
  obtain ⟨-, -, L, R, r1, r2, n⟩ := H
  have htas : TypedArgs Γ as := fun a ha => mkApps_arg_type hΓ hT ha
  have htbs : TypedArgs Γ bs := fun a ha => mkApps_arg_type hΓ hRs ha
  obtain ⟨n₁, HL⟩ := EtaSpine.fullReduction hrig hS hΓ r1
    (EtaSpine.spine (FullReduction.forall₂_rfl as)) htas hT
  have hL := FullReduction.hasType hΓ r1 hT
  rcases EtaSpine.normalize hΓ n₁ HL htas hL with ⟨as', rL, has'⟩ | ⟨A, body, _, _, rL, _⟩
  case inr => exact (HasType.sort_not_lam hΓ (FullReduction.hasType hΓ rL hL)).elim
  obtain ⟨R', rR', nR'⟩ := (n.symm hΓ).fullReduction hΓ rL
  have hR' := FullReduction.hasType hΓ (r2.trans rR') hRs
  obtain ⟨k, hk⟩ := nR'
  rcases NormalEqN.spine_expose hΓ .const k hk (bs := []) (bs' := []) .nil hR' with
    hp | ⟨h', targs', he, rr, hn⟩ | ⟨A, g, m, targs₁, B, -, rr, -⟩
  · exact (HasType.sort_not_proof hΓ hR' hp).elim
  · cases he with
    | @const ls'' _ _ =>
    obtain ⟨n₂, HR⟩ := EtaSpine.fullReduction hrig hS' hΓ ((r2.trans rR').trans rr)
      (EtaSpine.spine (FullReduction.forall₂_rfl bs)) htbs hRs
    obtain ⟨-, rfl, hbs⟩ := HR.spine_inv
    rw [List.append_nil] at hn
    refine List.forall₂_imp_mem (List.forall₂_join3 has' hn hbs)
      fun a ha b hb ⟨a', t, h1, h2, h3⟩ => ⟨htas a ha, htbs b hb, a', t, h1, h2, h3.symm hΓ⟩
  · exact (HasType.sort_not_lam hΓ (FullReduction.hasType hΓ rr hR')).elim

end Lean4Lean.VEnv
