import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaInstance

/-! # The arguments of an ι instance against the reduct template

Lemmas for establishing `IotaArgRel` (`Model/IotaInstance.lean`) for the rules of ordinary
blocks: argument substitutions through lifts (`argSubst_liftN_mid`), related argument
valuations built position by position (`substEq_argSubst_snoc`), and soundness between
valuations with different observation sets (`SoundAt.sub_sets`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem argSubst_eq_getD (as : List VExpr) (m : Nat) : VExpr.argSubst as m =
    if m < as.length then (as[as.length - 1 - m]?).getD default else .bvar (m - as.length) := by
  split
  · rw [VExpr.argSubst_lt _ (by omega), List.getElem?_eq_getElem (by omega)]; rfl
  · rw [VExpr.argSubst_ge _ (by omega)]

/-- An argument substitution through a lift of the middle block: the lifted variables skip the
middle arguments. -/
theorem argSubst_liftN_mid (e : VExpr) (pre mid post : List VExpr) :
    (e.liftN mid.length post.length).subst (VExpr.argSubst (pre ++ mid ++ post)) =
      e.subst (VExpr.argSubst (pre ++ post)) := by
  rw [VExpr.liftN_subst]
  congr 1
  funext x
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  rw [argSubst_eq_getD, argSubst_eq_getD]
  simp only [List.length_append]
  by_cases hx : x < post.length
  · rw [liftVar_lt hx, if_pos (by omega), if_pos (by omega),
      List.getElem?_append_right (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by omega)]
    congr 2; simp; omega
  · rw [liftVar_le (by omega)]
    by_cases hx' : x < pre.length + post.length
    · rw [if_pos (by omega), if_pos (by omega), List.append_assoc,
        List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      congr 2; omega
    · rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega

/-- Extending related argument valuations by one argument. -/
theorem substEq_argSubst_snoc {D : List VExpr} {as bs : List VExpr} {a b : VExpr} {n : Nat}
    (hn : as.length = n) (hl : n < D.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst bs) (D.take n).reverse)
    (hA : env.HasType U (D.take n).reverse D[n] (.sort u))
    (h : env.IsDefEq U Δ a b (D[n].subst (VExpr.argSubst as))) :
    Ctx.SubstEq env U Δ (VExpr.argSubst (as ++ [a])) (VExpr.argSubst (bs ++ [b]))
      (D.take (n + 1)).reverse := by
  subst hn
  rw [List.take_succ_eq_append_getElem hl,
    List.reverse_append, VExpr.argSubst_append_one, VExpr.argSubst_append_one]
  exact .cons W hA h

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

omit henv hΔ in
/-- The union of two typed valuations' observation sets is typed. -/
theorem TV.union {Γ : List VExpr} {σ : VExpr.Subst} {S₁ S₂ : ObSets}
    (tv₁ : TV env U Δ Γ σ S₁) (tv₂ : TV env U Δ Γ σ S₂) :
    TV env U Δ Γ σ (fun i x => S₁ i x ∨ S₂ i x) := by
  refine ⟨fun i x hx w hw => ?_, fun i A hL x hx => ?_⟩
  · rcases hx with hx | hx
    · exact .inl (tv₁.1 i x hx w hw)
    · exact .inr (tv₂.1 i x hx w hw)
  · rcases hx with hx | hx
    · obtain ⟨τs, h1, h2⟩ := tv₁.2 i A hL x hx
      exact ⟨τs, fun τ hτ => (h1 τ hτ).mono fun _ _ h => .inl h, h2⟩
    · obtain ⟨τs, h1, h2⟩ := tv₂.2 i A hL x hx
      exact ⟨τs, fun τ hτ => (h1 τ hτ).mono fun _ _ h => .inr h, h2⟩

/-- **Soundness between valuations with different observation sets**: the observations of a
soundly typed term at `(σ₁, S₁)` are subsumed by those at a related `(σ₂, S₂)` when every
observation of `S₁` is subsumed by one of `S₂` and both are typed valuations of a sound
context. -/
theorem SoundAt.sub_sets {Γ : List VExpr} {t T : VExpr} (h : SoundAt env U Δ Γ t t T)
    (hctx : CtxSD env U Δ [] Γ)
    {σ₁ σ₂ : VExpr.Subst} {S₁ S₂ : ObSets} (W : Ctx.SubstEq env U Δ σ₁ σ₂ Γ)
    (hout : ∀ x, Γ.length ≤ x → σ₁ x = σ₂ x)
    (tv₁ : TV env U Δ Γ σ₁ S₁) (tv₂ : TV env U Δ Γ σ₂ S₂)
    (hS : ∀ i o, S₁ i o → ∃ o', S₂ i o' ∧ o' ≼ o) :
    Ob.Sub (Obs' σ₁ S₁ t) (Obs' σ₂ S₂ t) := by
  intro o ho
  have W' : Ctx.SubstEq env U Δ σ₁ σ₂ (Γ ++ []) := by simpa using W
  have Ws : Ctx.SubstEq env U Δ σ₂ σ₁ (Γ ++ []) := by simpa using SubstEq.symm henv hΔ W
  have t21 : TV env U Δ Γ σ₁ S₂ := by
    have := TV.transfer henv hΔ (Γ := []) hctx W' (by simpa using hout) (by simpa using tv₂)
    simpa using this
  have t12 : TV env U Δ Γ σ₂ S₁ := by
    have := TV.transfer henv hΔ (Γ := []) hctx Ws (by simpa using fun x hx => (hout x hx).symm)
      (by simpa using tv₁)
    simpa using this
  have tvA := TV.union tv₁ t21
  have tvB := TV.union t12 tv₂
  obtain ⟨o₁, ho₁, l₁⟩ := (h σ₁ σ₂ _ W tvA tvB).1 o (ho.mono fun _ _ h => .inl h)
  obtain ⟨o₂, ho₂, l₂⟩ := ho₁.mono_le (S' := S₂) fun i x hx => by
    rcases hx with hx | hx
    · exact hS i x hx
    · exact ⟨x, hx, .refl⟩
  exact ⟨o₂, ho₂, l₂.trans l₁⟩


/-- `rigid_arg_cls_obs` with the domain class of the argument read off the head's telescope. -/
theorem rigid_arg_cls_obs' {Γ : List VExpr} {c : Name} {ls : List VLevel} {args : List VExpr}
    {u : VLevel} {σ : VExpr.Subst} {S : ObSets} {ci : VConstant} {Dw : List VExpr} {Rw : VExpr}
    (hci : env.constants c = some ci)
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw)
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) (.sort u)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hrig : env.Rigid c) {i : Nat} (hi : i < args.length)
    (hiD : i < Dw.length) :
    ∃ A, HTS env U Δ Γ args[i] A ∧ SD env U Δ Γ args[i] args[i] A ∧
      TyCls env U Δ (A.subst σ) =
        TyCls env U Δ (Dw[i].subst (VExpr.argSubst ((args.take i).map (·.subst σ)))) ∧
      Obs' σ S (.mkApps (.const c ls) args)
        (.rigidArg i (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (args[i].subst σ))) := by
  obtain ⟨Th, info, hTh, -, -, hinfo, -, P1, -, -, PT⟩ :=
    H.spineH' henv hΔ rfl ⟨c, ls, rfl⟩ W tv (args.map fun _ => []) (forall₂_nil_lists args)
      [.sort u.eval] (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort)
  obtain ⟨_, _, ci', e0, hci', -, rfl⟩ := hTh
  cases e0
  cases hci.symm.trans hci'
  have hlen : info.length = args.length := List.Forall₂.length_eq hinfo
  have hi' : i < info.length := by omega
  obtain ⟨_, hd⟩ := List.forall₂_getElem_exists hinfo i hi'
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hd
  have hr : RigidEnd c (ls.map (·.eval)) (info.map (·.1)) (.rigidArg i (info[i]).1.2.1) :=
    .inr (.inl ⟨i, by simpa using hi', by simp⟩)
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 _ (.rigidArg (List.mem_singleton_self _))
  obtain ⟨B, hB⟩ := PT i hi'
  have e := spine_dom_cls henv hΔ hci hTW hpi (pre := args.take i) (by simp; omega) W tv hB
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at e
  refine ⟨(info[i]).2, h4, h5, e, ?_⟩
  have := obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo) (.const hrig hci hτ₀ hty₀ hr)
  rwa [h1, h3] at this

/-- **Related rigid spines along the head's telescope**: two sort-typed spines of the rigid
constant `c` whose observations subsume each other have related argument valuations along the
telescope of `c`'s type, at the levels of the left spine, and mutually subsuming argument
observations. -/
theorem rigid_spines_substEq {Γ₁ Γ₂ : List VExpr} {c : Name} {ls₁ ls₂ : List VLevel}
    {args₁ args₂ : List VExpr} {u₁ u₂ : VLevel} {σ₁ σ₂ : VExpr.Subst} {S₁ S₂ : ObSets}
    {ci : VConstant} {Dw : List VExpr} {Rw : VExpr}
    (hci : env.constants c = some ci)
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls₁)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw)
    (H₁ : HTS env U Δ Γ₁ (.mkApps (.const c ls₁) args₁) (.sort u₁))
    (W₁ : Ctx.SubstEq env U Δ σ₁ σ₁ Γ₁) (tv₁ : TV env U Δ Γ₁ σ₁ S₁)
    (H₂ : HTS env U Δ Γ₂ (.mkApps (.const c ls₂) args₂) (.sort u₂))
    (W₂ : Ctx.SubstEq env U Δ σ₂ σ₂ Γ₂) (tv₂ : TV env U Δ Γ₂ σ₂ S₂) (hrig : env.Rigid c)
    (hsub : Ob.Sub (Obs' σ₁ S₁ (.mkApps (.const c ls₁) args₁))
      (Obs' σ₂ S₂ (.mkApps (.const c ls₂) args₂)))
    (hsub' : Ob.Sub (Obs' σ₂ S₂ (.mkApps (.const c ls₂) args₂))
      (Obs' σ₁ S₁ (.mkApps (.const c ls₁) args₁)))
    (hlenD : args₁.length ≤ Dw.length) :
    args₁.length = args₂.length ∧ List.Forall₂ (· ≈ ·) ls₁ ls₂ ∧
    Ctx.SubstEq env U Δ (VExpr.argSubst (args₁.map (·.subst σ₁)))
      (VExpr.argSubst (args₂.map (·.subst σ₂))) (Dw.take args₁.length).reverse ∧
    ∀ i (hi : i < args₁.length) (hi' : i < args₂.length),
      Ob.Sub (Obs' σ₁ S₁ args₁[i]) (Obs' σ₂ S₂ args₂[i]) ∧
      Ob.Sub (Obs' σ₂ S₂ args₂[i]) (Obs' σ₁ S₁ args₁[i]) := by
  obtain ⟨hlen, hls, hrel⟩ := rigid_spines_rel henv hΔ H₁ W₁ tv₁ H₂ W₂ tv₂ hrig hsub hsub'
  refine ⟨hlen, hls, ?_, fun i hi hi' => ⟨(hrel i hi hi').1, (hrel i hi hi').2.1⟩⟩
  -- the defeqs at the telescope's domains
  have hdef : ∀ i (hi : i < args₁.length) (hi' : i < args₂.length) (hiD : i < Dw.length),
      env.IsDefEq U Δ (args₁[i].subst σ₁) (args₂[i].subst σ₂)
        (Dw[i].subst (VExpr.argSubst ((args₁.take i).map (·.subst σ₁)))) := by
    intro i hi hi' hiD
    obtain ⟨A, -, hsA, eA, hcls⟩ := rigid_arg_cls_obs' henv hΔ hci hTW hpi H₁ W₁ tv₁ hrig hi hiD
    obtain ⟨o', ho', l⟩ := hsub _ hcls
    rw [l.rigidArg_inv] at ho'
    obtain ⟨keys', hk', hw'⟩ := wrap_of_obs_mkApps ho'
    have hend' := const_wrap_inv hrig hw' (.inr ⟨_, _, rfl⟩)
    obtain ⟨j, hj, e⟩ : ∃ j, ∃ h : j < keys'.length,
        Ob.rigidArg i (ElCls env U Δ (TyCls env U Δ (A.subst σ₁)) (args₁[i].subst σ₁)) =
          .rigidArg j (keys'[j]).2.1 := by
      rcases hend' with ⟨_, e⟩ | ⟨j, hj, e⟩ | ⟨_, _, _, _, e⟩
      · cases e
      · exact ⟨j, hj, e⟩
      · cases e
    injection e with e1 e2
    subst e1
    obtain ⟨_, hcl⟩ := List.forall₂_getElem_exists hk' i hj
    have hmem : ElCls env U Δ (TyCls env U Δ (A.subst σ₁)) (args₁[i].subst σ₁)
        (args₂[i].subst σ₂) := by
      rw [e2, hcl]; exact ElCls.self
    have ha : env.HasType U Δ (args₁[i].subst σ₁) (A.subst σ₁) :=
      hsA.1.defeq.hasType.1.substDF henv W₁.wf hΔ W₁
    have h := ElCls.collapse henv hΔ ha TyCls.self hmem
    have hm : TyCls env U Δ (A.subst σ₁)
        (Dw[i].subst (VExpr.argSubst ((args₁.take i).map (·.subst σ₁)))) := by
      rw [eA]; exact TyCls.self
    exact TyCls.defeq_rev henv hΔ hm h
  -- assemble along the prefixes
  have key : ∀ n, n ≤ args₁.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((args₁.take n).map (·.subst σ₁)))
        (VExpr.argSubst ((args₂.take n).map (·.subst σ₂))) (Dw.take n).reverse := by
    intro n
    induction n with
    | zero => intro _; simpa using (Ctx.SubstEq.nil : Ctx.SubstEq env U Δ _ _ [])
    | succ n ih =>
      intro hn
      have hn₁ : n < args₁.length := by omega
      have hn₂ : n < args₂.length := by omega
      have hnD : n < Dw.length := by omega
      obtain ⟨-, w, hDn⟩ := DomsSD.take_getElem hpi.doms n hnD
      rw [List.append_nil] at hDn
      have := substEq_argSubst_snoc (D := Dw) (as := (args₁.take n).map (·.subst σ₁))
        (bs := (args₂.take n).map (·.subst σ₂)) (a := args₁[n].subst σ₁)
        (b := args₂[n].subst σ₂) (n := n) (by simp; omega) hnD (ih (by omega))
        hDn.1.defeq.hasType.1 (hdef n hn₁ hn₂ hnD)
      rw [List.take_succ_eq_append_getElem hn₁, List.take_succ_eq_append_getElem hn₂,
        List.map_append, List.map_append]
      simpa using this
  have := key args₁.length (Nat.le_refl _)
  rwa [List.take_length, List.take_of_length_le (by omega)] at this


/-- The two family spines of an ι redex (`redex_major_rel`, before relating their
arguments): the recursor's major domain at the recursor arguments and the constructor's result
at the constructor arguments are semantically typed sort spines whose observations subsume each
other, at typed valuations of the two telescopes. -/
theorem redex_major_sub {Γ : List VExpr} {n ctor I : Name} {m1 lsC lsI lsC' : List VLevel}
    {ci cc : VConstant} {dsH Dc iargs cargs recArgs ctorArgs : List VExpr} {RH A : VExpr}
    {kM : Nat} {uT uC : VLevel} {σ : VExpr.Subst} {S : ObSets}
    (hci : env.constants n = some ci) (eH : ci.type.instL m1 = .wrapForalls dsH RH)
    (hT : HTS env U Δ [] (ci.type.instL m1) (.sort uT))
    (hlenH : dsH.length = kM + 1) (hkH : dsH[kM]? = some (.mkApps (.const I lsI) iargs))
    (hcc : env.constants ctor = some cc)
    (eC : cc.type.instL lsC = .wrapForalls Dc (.mkApps (.const I lsC') cargs))
    (hTc : HTS env U Δ [] (cc.type.instL lsC) (.sort uC))
    (hrA : recArgs.length = kM) (hcA : ctorArgs.length = Dc.length)
    (H : HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    ∃ uR uI,
      HTS env U Δ (dsH.take kM).reverse (.mkApps (.const I lsI) iargs) (.sort uR) ∧
      HTS env U Δ Dc.reverse (.mkApps (.const I lsC') cargs) (.sort uI) ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst (recArgs.map (·.subst σ)))
        (VExpr.argSubst (recArgs.map (·.subst σ))) (dsH.take kM).reverse ∧
      TV env U Δ (dsH.take kM).reverse (VExpr.argSubst (recArgs.map (·.subst σ)))
        (argSets env U Δ σ S recArgs) ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst (ctorArgs.map (·.subst σ)))
        (VExpr.argSubst (ctorArgs.map (·.subst σ))) Dc.reverse ∧
      TV env U Δ Dc.reverse (VExpr.argSubst (ctorArgs.map (·.subst σ)))
        (argSets env U Δ σ S ctorArgs) ∧
      Ob.Sub (Obs' (VExpr.argSubst (ctorArgs.map (·.subst σ))) (argSets env U Δ σ S ctorArgs)
          (.mkApps (.const I lsC') cargs))
        (Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
          (.mkApps (.const I lsI) iargs)) ∧
      Ob.Sub (Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
          (.mkApps (.const I lsI) iargs))
        (Obs' (VExpr.argSubst (ctorArgs.map (·.subst σ))) (argSets env U Δ σ S ctorArgs)
          (.mkApps (.const I lsC') cargs)) := by
  subst hrA
  have hkM : recArgs.length < dsH.length := by omega
  obtain ⟨Amaj, B, u, v, hf, -, -, -, hmaj, hsmaj, hch⟩ := H.app_const_inv' rfl
  have hT' : HTS env U Δ [] (.wrapForalls dsH RH) (.sort uT) := by rw [← eH]; exact hT
  have hTc' : HTS env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs)) (.sort uC) := by
    rw [← eC]; exact hTc
  have hpiH' : PiSD env U Δ [] dsH RH := hT'.piSD
  have hpiC : PiSD env U Δ [] Dc (.mkApps (.const I lsC') cargs) := hTc'.piSD
  have hTW : Ob.Sub (Obs' .id .empty (ci.type.instL m1))
      (Obs' .id .empty (.wrapForalls dsH RH)) := by rw [eH]; exact Ob.Sub.refl
  have hTWc : Ob.Sub (Obs' .id .empty (cc.type.instL lsC))
      (Obs' .id .empty (.wrapForalls Dc (.mkApps (.const I lsC') cargs))) := by
    rw [eC]; exact Ob.Sub.refl
  obtain ⟨WR, tvR⟩ := spine_tele henv hΔ hf W tv hci hTW hpiH' (by omega)
  obtain ⟨WC, tvC⟩ := spine_tele henv hΔ hmaj W tv hcc hTWc hpiC (Nat.le_of_eq hcA)
  rw [hcA, List.take_length] at WC tvC
  have hdom := HTS.spineVal_dom henv hΔ hci eH hpiH' hf W tv (by omega)
  have hdsHk : dsH[recArgs.length] = .mkApps (.const I lsI) iargs := by
    rw [List.getElem?_eq_getElem hkM] at hkH; exact Option.some.inj hkH
  rw [hdsHk] at hdom
  have hres := HTS.spineVal henv hΔ hcc eC hpiC hmaj W tv (Nat.le_of_eq hcA)
  rw [hcA, List.drop_length] at hres
  simp only [VExpr.wrapForalls, List.foldr_nil] at hres
  obtain ⟨uR, hIR, -⟩ := HTS.tele_dom (pre := dsH.take recArgs.length) (post := [])
    (A := dsH[recArgs.length])
    (by rw [← wrapForalls_last hlenH]; exact hT')
  rw [List.append_nil, hdsHk] at hIR
  obtain ⟨uI, hIC⟩ := HTS.wrapForalls_body hTc'
  rw [List.append_nil] at hIC
  exact ⟨uR, uI, hIR, hIC, WR, tvR, WC, tvC, hres.2.trans hdom.1, hdom.2.trans hres.1⟩


/-- The bodies of two telescopes whose observations are subsumed one way, at typed keys along
both telescopes. -/
theorem tele_sound_body {D₁ D₂ : List VExpr} {R₁ R₂ : VExpr} (hpi₂ : PiSD env U Δ [] D₂ R₂)
    {w : VLevel} (hR₂ : SD env U Δ D₂.reverse R₂ R₂ (.sort w))
    (hsub : Ob.Sub (Obs' .id .empty (.wrapForalls D₁ R₁)) (Obs' .id .empty (.wrapForalls D₂ R₂)))
    {keys : List Key} {σ' : VExpr.Subst} {S' : ObSets}
    (hTK₁ : TeleKeys env U Δ .id .empty D₁ keys σ' S')
    (hTK₂ : TeleKeys env U Δ .id .empty D₂ keys σ' S') :
    Ob.Sub (Obs' σ' S' R₁) (Obs' σ' S' R₂) := by
  have hkl : keys.length = D₂.length := hTK₂.length
  have hds₂ : DomsSD env U Δ [] D₂ := hpi₂.doms
  have hctx : CtxSD env U Δ [] D₂.reverse := by
    have := DomsSD.ctxSD (L := []) (Γ := []) hds₂ .nil
    simpa using this
  obtain ⟨ys₀, hσ', hS', hyl₀, -, -⟩ := hTK₂.data
  intro z hz
  have h1 := tele_obs hTK₁ hz
  obtain ⟨o', ho', l⟩ := hsub _ h1
  obtain ⟨keys', z', rfl, hkk, lz⟩ := Le.piCodChain_inv l
  have hkl' : keys'.length = D₂.length := by rw [List.Forall₂.length_eq hkk, hkl]
  obtain ⟨keys'', ys, hT, -, hky, hz'⟩ := tele_split (Nat.le_of_eq hkl') ho'
  rw [hkl', List.take_length] at hT
  rw [hkl', List.drop_length] at hz'
  simp only [VExpr.wrapForalls, List.foldr_nil] at hz'
  have hcls : List.Forall₂ (fun (k : Key) y => k.2.1 y) keys ys :=
    forall₂_zip (fun _ _ _ h1 h2 => h1.2.1 ▸ h2) hkk hky
  have W' := hTK₂.substEq henv hΔ (v := .id) hds₂ .nil hcls
  rw [List.append_nil] at W'
  have W'' : Ctx.SubstEq env U Δ (VExpr.argSubst ys) σ' D₂.reverse := SubstEq.symm henv hΔ W'
  obtain ⟨Wy, tvy⟩ := hT.typed henv hΔ hds₂ .nil TV.empty
  rw [List.append_nil] at Wy tvy
  have hyl : ys.length = D₂.length := by rw [← List.Forall₂.length_eq hky, hkl']
  have hout : ∀ x, D₂.reverse.length ≤ x →
      σ' x = (ys.foldl VExpr.Subst.cons VExpr.Subst.id) x := by
    intro x hx
    rw [List.length_reverse] at hx
    show σ' x = VExpr.argSubst ys x
    rw [hσ', VExpr.argSubst_ge _ (by omega)]
    show VExpr.argSubst ys₀ x = _
    rw [VExpr.argSubst_ge _ (by omega), hyl, hyl₀]
  have tvσ : TV env U Δ D₂.reverse σ' (extS .empty keys') := by
    have := TV.transfer henv hΔ (Γ := []) hctx (by simpa using W') (by simpa using hout)
      (by simpa using tvy)
    simpa using this
  obtain ⟨z'', hz'', l''⟩ := (hR₂.2 _ _ _ W'' tvy tvσ).1 _ hz'
  obtain ⟨z₃, hz₃, l₃⟩ := hz''.mono_le (S' := S') fun i o h => by
    rw [hS']
    exact extS_covers hkk i o h
  exact ⟨z₃, hz₃, l₃.trans (l''.trans lz)⟩

/-- **Bodies of soundly equal telescopes** at a full typed valuation by arguments: their
observations subsume each other. -/
theorem tele_sound_res {D₁ D₂ : List VExpr} {R₁ R₂ : VExpr} {T : VExpr}
    (hcl₁ : ∀ i (hi : i < D₁.length), (D₁[i]).ClosedN i)
    (hR₁cl : R₁.ClosedN D₁.length) (hR₂cl : R₂.ClosedN D₂.length)
    (hS : SoundAt env U Δ [] (.wrapForalls D₁ R₁) (.wrapForalls D₂ R₂) T)
    (hpi₁ : PiSD env U Δ [] D₁ R₁) (hpi₂ : PiSD env U Δ [] D₂ R₂)
    {w₁ w₂ : VLevel} (hR₁ : SD env U Δ D₁.reverse R₁ R₁ (.sort w₁))
    (hR₂ : SD env U Δ D₂.reverse R₂ R₂ (.sort w₂)) (hlen : D₁.length = D₂.length)
    {as : List VExpr} {Sx : ObSets} (has : as.length = D₁.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst as) D₁.reverse)
    (tv : TV env U Δ D₁.reverse (VExpr.argSubst as) Sx) :
    Ob.Sub (Obs' (VExpr.argSubst as) Sx R₁) (Obs' (VExpr.argSubst as) Sx R₂) ∧
    Ob.Sub (Obs' (VExpr.argSubst as) Sx R₂) (Obs' (VExpr.argSubst as) Sx R₁) := by
  have hS0 := hS .id .id .empty .nil TV.empty TV.empty
  have hsub₁ := hS0.1
  have hsub₂ := hS0.2.1
  -- typed keys along both telescopes at the arguments, with the given demands
  have keysOf : ∀ G : List (List Ob), G.length = as.length →
      (∀ m (hm : m < G.length), ∀ y ∈ G[m], Sx m y) →
      ∃ keys S', TeleKeys env U Δ .id .empty D₁ keys (VExpr.argSubst as) S' ∧
        TeleKeys env U Δ .id .empty D₂ keys (VExpr.argSubst as) S' ∧
        (∀ m (hm : m < G.length), ∀ y ∈ G[m], S' m y) ∧ (∀ m y, S' m y → Sx m y) := by
    intro G hGl hGS
    obtain ⟨keys, S', hTK, hkl, hS', hkeys⟩ := tele_compact hcl₁ has W tv G.reverse
      (by rw [List.length_reverse, hGl, has]) (fun i Fi hFi y hy => by
        have hil : i < G.length := by
          have := (List.getElem?_eq_some_iff.1 hFi).1; simpa using this
        rw [List.getElem?_reverse hil, List.getElem?_eq_getElem (by omega)] at hFi
        cases hFi
        have := hGS (G.length - 1 - i) (by omega) y hy
        rwa [hGl, has] at this)
    have hTK₂ := tele_sound_keys henv hΔ hpi₂ hsub₁ hlen D₁.length (Nat.le_refl _)
      (by rwa [List.take_length])
    rw [List.take_of_length_le (by omega)] at hTK₂
    refine ⟨keys, S', hTK, hTK₂, fun m hm y hy => ?_, fun m y hy => ?_⟩
    · have hmD : m < D₁.length := by rw [← has, ← hGl]; exact hm
      have hkD : D₁.length - 1 - m < keys.length := by omega
      refine (hS' m keys[_] (List.getElem?_eq_getElem hkD) hmD y).2 ?_
      refine (hkeys _ _ (List.getElem?_eq_getElem hkD)).1 G[m] ?_ y hy
      rw [List.getElem?_reverse (by omega), List.getElem?_eq_getElem (by omega)]
      congr 2; omega
    · by_cases hm : m < D₁.length
      · have hkD : D₁.length - 1 - m < keys.length := by omega
        have := (hS' m keys[_] (List.getElem?_eq_getElem hkD) hm y).1 hy
        have h2 := (hkeys _ _ (List.getElem?_eq_getElem hkD)).2.1 y this
        rwa [show D₁.length - 1 - (D₁.length - 1 - m) = m by omega] at h2
      · exfalso
        have hout := hTK.outer (m - D₁.length)
        rw [show m - D₁.length + D₁.length = m by omega] at hout
        rw [hout.2] at hy
        exact hy
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hR₁cl' : R₁.ClosedN as.length := by rw [has]; exact hR₁cl
    obtain ⟨G, hGl, hGS, hG⟩ := Obs.compact_all hR₁cl' (τs := [x])
      (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hx)
    obtain ⟨keys, S', hTK₁, hTK₂, hGS', hSx⟩ := keysOf G hGl hGS
    have hx' : Obs' (VExpr.argSubst as) S' R₁ x := hG S' hGS' x (List.mem_singleton_self _)
    obtain ⟨x', hx', l⟩ := tele_sound_body henv hΔ hpi₂ hR₂ hsub₁ hTK₁ hTK₂ _ hx'
    exact ⟨x', hx'.mono fun m y hy => hSx m y hy, l⟩
  · have hR₂cl' : R₂.ClosedN as.length := by rw [has, hlen]; exact hR₂cl
    obtain ⟨G, hGl, hGS, hG⟩ := Obs.compact_all hR₂cl' (τs := [x])
      (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hx)
    obtain ⟨keys, S', hTK₁, hTK₂, hGS', hSx⟩ := keysOf G hGl hGS
    have hx' : Obs' (VExpr.argSubst as) S' R₂ x := hG S' hGS' x (List.mem_singleton_self _)
    obtain ⟨x', hx', l⟩ := tele_sound_body henv hΔ hpi₁ hR₁ hsub₂ hTK₂ hTK₁ _ hx'
    exact ⟨x', hx'.mono fun m y hy => hSx m y hy, l⟩


omit henv hΔ in
/-- Extending a typed argument valuation by one argument. -/
theorem tv_argSubst_snoc {D as : List VExpr} {Sx : ObSets} {a : VExpr} {X : Ob → Prop} {n : Nat}
    (hn : as.length = n) (hl : n < D.length)
    (tv : TV env U Δ (D.take n).reverse (VExpr.argSubst as) Sx) (hb : Backed X)
    (hX : ∀ o, X o → TypedAt env U Δ
      (ElCls env U Δ (TyCls env U Δ (D[n].subst (VExpr.argSubst as))) a)
      (VExpr.argSubst as) Sx D[n] o) :
    TV env U Δ (D.take (n + 1)).reverse (VExpr.argSubst (as ++ [a])) (Sx.cons X) := by
  subst hn
  rw [List.take_succ_eq_append_getElem hl, List.reverse_append, VExpr.argSubst_append_one]
  exact TV.cons_set tv hb hX

omit henv hΔ in
/-- The entries of related argument valuations along a telescope. -/
theorem substEq_argSubst_get {D as bs : List VExpr}
    (hl : as.length = bs.length) (hD : as.length ≤ D.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst bs) (D.take as.length).reverse)
    {i : Nat} (hi : i < as.length) :
    (∃ u, env.HasType U (D.take i).reverse D[i] (.sort u)) ∧
    env.IsDefEq U Δ as[i] (bs[i]'(by omega)) (D[i].subst (VExpr.argSubst (as.take i))) := by
  have W' := substEq_take as bs hl hD W (i + 1) (by omega)
  rw [List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem (by omega),
    List.take_succ_eq_append_getElem (by omega), List.reverse_append,
    VExpr.argSubst_append_one, VExpr.argSubst_append_one] at W'
  cases W' with
  | cons _ hA h => exact ⟨⟨_, by simpa using hA⟩, by simpa using h⟩

/-- **The domain class at a bare-variable argument of a constant spine** is the class of the
variable's type. -/
theorem bvar_arg_dom_cls {Γ' : List VExpr} {c : Name} {ls : List VLevel} {ci : VConstant}
    {Dw : List VExpr} {Rw T₀ : VExpr} {args : List VExpr} {ρ : VExpr.Subst} {R : ObSets}
    (hci : env.constants c = some ci)
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw)
    (H : HTS env U Δ Γ' (.mkApps (.const c ls) args) T₀)
    (W : Ctx.SubstEq env U Δ ρ ρ Γ') (tv : TV env U Δ Γ' ρ R)
    {i y : Nat} {T : VExpr} (hi : i < args.length) (hiD : i < Dw.length)
    (hy : args[i] = .bvar y) (hL : Lookup Γ' y T) :
    TyCls env U Δ (Dw[i].subst (VExpr.argSubst ((args.take i).map (·.subst ρ)))) =
      TyCls env U Δ (T.subst ρ) := by
  obtain ⟨A, B, hf, ha, -⟩ := HTS.spine_at _ rfl H i hi
  have e1 := spine_dom_cls henv hΔ hci hTW hpi (pre := args.take i) (by simp; omega) W tv hf
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at e1
  rw [hy] at ha
  rw [← e1]
  exact bvar_dom_cls henv hΔ W ha hL


omit henv hΔ in
/-- The argument substitution shifted past the last `x + 1` arguments. -/
theorem argSubst_shift (L : List VExpr) {x : Nat} (hx : x < L.length) :
    (fun j => VExpr.argSubst L (j + (x + 1))) = VExpr.argSubst (L.take (L.length - (x + 1))) := by
  funext j
  rw [argSubst_eq_getD, argSubst_eq_getD]
  simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
  by_cases hj : j + (x + 1) < L.length
  · rw [if_pos hj, if_pos (by omega), List.getElem?_take_of_lt (by omega)]
    congr 2; omega
  · rw [if_neg hj, if_neg (by omega)]
    congr 1; omega

omit henv hΔ in
/-- A type of the reversed telescope at the argument valuation is the domain at the prefix. -/
theorem lift_subst_argSubst (D L : List VExpr) {x : Nat} (hx : x < D.length)
    (hL : L.length = D.length) :
    ((D.reverse[x]'(by simpa using hx)).liftN (x + 1)).subst (VExpr.argSubst L) =
      (D[D.length - 1 - x]'(by omega)).subst (VExpr.argSubst (L.take (D.length - 1 - x))) := by
  rw [liftN_subst_shift, argSubst_shift L (by omega), List.getElem_reverse]
  congr 3; omega

omit henv hΔ in
/-- `binderTy` at the argument valuation. -/
theorem binderTy_subst_argSubst {doms : List VExpr} {ls : List VLevel} {L : List VExpr}
    {x : Nat} (hx : x < doms.length) (hL : L.length = doms.length) :
    (binderTy doms ls x).subst (VExpr.argSubst L) =
      ((doms.map (·.instL ls))[doms.length - 1 - x]'(by simp; omega)).subst
        (VExpr.argSubst (L.take (doms.length - 1 - x))) := by
  have hx' : x < (doms.map (·.instL ls)).reverse.length := by simpa using hx
  have e : binderTy doms ls x =
      ((doms.map (fun d : VExpr => d.instL ls)).reverse[x]'hx').liftN (x+1) :=
    (lookup_binderTy (Γ := []) (ls := ls) hx).uniq (lookup_append _ x hx')
  rw [e, lift_subst_argSubst (doms.map (·.instL ls)) L (by simpa using hx) (by simpa using hL)]
  simp

omit henv hΔ in
/-- The body of a sound Pi telescope is sound in the telescope's context. -/
theorem PiSD.body_sd : ∀ {Γ D : List VExpr} {R : VExpr} {u : VLevel}, PiSD env U Δ Γ D R →
    SD env U Δ Γ (.wrapForalls D R) (.wrapForalls D R) (.sort u) →
    ∃ v, SD env U Δ (D.reverse ++ Γ) R R (.sort v)
  | _, [], _, _, _, h => ⟨_, by simpa [VExpr.wrapForalls] using h⟩
  | Γ, A :: ds, R, _, .cons _ hB hP, _ => by
    obtain ⟨v, h⟩ := PiSD.body_sd hP hB
    exact ⟨v, by simpa [List.reverse_cons, List.append_assoc] using h⟩


omit henv hΔ in
/-- The typing of the last argument of a typed argument valuation. -/
theorem TV.snoc_inv {D as : List VExpr} {Sx : ObSets} {a : VExpr} {X : Ob → Prop} {n : Nat}
    (hn : as.length = n) (hl : n < D.length)
    (tv : TV env U Δ (D.take (n + 1)).reverse (VExpr.argSubst (as ++ [a])) (Sx.cons X)) :
    ∀ o, X o → TypedAt env U Δ
      (ElCls env U Δ (TyCls env U Δ (D[n].subst (VExpr.argSubst as))) a)
      (VExpr.argSubst as) Sx D[n] o := by
  subst hn
  intro o ho
  rw [List.take_succ_eq_append_getElem hl, List.reverse_append, VExpr.argSubst_append_one] at tv
  have h := tv.2 0 _ .zero o ho
  rw [vcls_bvar_zero] at h
  obtain ⟨τs, h1, h2⟩ := h
  exact ⟨τs, fun τ hτ => Obs.lift_cons_iff.1 (h1 τ hτ), h2⟩

omit henv hΔ in
theorem argSets_lt {σ : VExpr.Subst} {S : ObSets} {L : List VExpr} {i : Nat} (hi : i < L.length) :
    argSets env U Δ σ S L i = Obs' σ S (L[L.length - 1 - i]'(by omega)) := by
  simp only [argSets, hi, dite_true]

omit henv hΔ in
theorem argSubst_map_lt {σ : VExpr.Subst} {L : List VExpr} {i : Nat} (hi : i < L.length) :
    VExpr.argSubst (L.map (·.subst σ)) i = (L[L.length - 1 - i]'(by omega)).subst σ := by
  rw [VExpr.argSubst_lt _ (by simpa using hi)]
  simp


omit henv hΔ in
/-- The last entry of related argument valuations. -/
theorem substEq_snoc_inv {D as bs : List VExpr} {a b : VExpr} {n : Nat} (hn : as.length = n)
    (hl : n < D.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst (as ++ [a])) (VExpr.argSubst (bs ++ [b]))
      (D.take (n + 1)).reverse) :
    env.IsDefEq U Δ a b (D[n].subst (VExpr.argSubst as)) ∧
    Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst bs) (D.take n).reverse := by
  subst hn
  rw [List.take_succ_eq_append_getElem hl,
    List.reverse_append, VExpr.argSubst_append_one, VExpr.argSubst_append_one] at W
  cases W with
  | cons W _ h => exact ⟨by simpa using h, by simpa using W⟩

end

end Model
end VEnv
end Lean4Lean
