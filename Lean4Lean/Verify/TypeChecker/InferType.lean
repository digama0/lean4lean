import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem ensureSortCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      (∃ u, e1 = .sort u) ∧ c.TrExpr e1 e' ∧ c.FVarsBelow e e1 := by
  simp [ensureSortCore]; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he.trExpr c.Ewf c.Δwf, .rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he, hb⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf, _, _, _, _, rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .forallE .. := e
    exact .pure ⟨hb, he, _, _, _, _, rfl⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF' {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  let ⟨_, he, eq⟩ := he
  (ensureForallCore.WF he).mono fun _ _ _ ⟨h1, h2, h3⟩ =>
    ⟨h1, h2.defeq c.Ewf c.Δwf eq, h3⟩

theorem checkLevel.WF {c : VContext} (H : l.hasMVar' = false) :
    (checkLevel c.toContext l).WF fun _ => ∃ u', VLevel.ofLevel c.lparams l = some u' := by
  simp [checkLevel]; split <;> [exact .throw; refine .pure ?_]
  exact Level.getUndefParam_none H (by rename_i h; simpa using h)

theorem inferFVar.WF {c : VContext} :
    (inferFVar c.toContext name).WF fun ty => ∃ e' ty', c.TrTyping (.fvar name) ty e' ty' := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, _, h2, _, h3⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  exact ⟨_, _, h2, .fvar h1, h3, c.Δwf.find?_wf c.Ewf h1⟩

theorem envGet.WF {c : VContext} :
    (c.env.get name).WF fun ci => c.env.find? name = some ci := by
  simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]

theorem inferConstant.WF {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      ∃ e' ty', c.TrTyping (.const name ls) ty e' ty' := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq1 => ?_
  have : (ls.foldlM (fun b a => checkLevel c.toContext a) PUnit.unit).WF fun _ =>
      ∃ ls', ls.Forall₂ (VLevel.ofLevel c.lparams · = some ·) ls' := by
    clear hinf
    induction ls with
    | nil => exact .pure ⟨_, .nil⟩
    | cons l ls ih =>
      simp at H
      refine (checkLevel.WF H.1).bind fun ⟨⟩ ⟨_, h1⟩ => ?_
      exact (ih H.2).le fun _ ⟨_, h2⟩ => ⟨_, .cons h1 h2⟩
  split <;> [rename_i h1; exact .throw]
  have main {e'} (he : c.TrExprS (.const name ls) e') : ∃ e' ty',
      c.TrTyping (.const name ls) (ci.instantiateTypeLevelParams ls) e' ty' := by
    let .const h4 H' eq := id he
    have ⟨_, _, h5, h6⟩ := c.trenv.find?_uniq eq1 h4
    have H := List.mapM_eq_some.1 H'
    have s0 := h6.instL c.Ewf (Δ := []) trivial H' (h5.trans eq.symm)
    have s1 := s0.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [(c.Ewf.ordered.closedC h4).instL.liftN_eq (Nat.le_refl _)] at s1
    have ⟨_, s1, s2⟩ := s1
    refine ⟨_, _, ?_, he, s1, .defeqU_r c.Ewf c.Δwf s2.symm ?_⟩
    · intro _ _ _; exact s0.fvarsIn.mono nofun
    · exact .const h4 (.of_mapM_ofLevel H') (H.length_eq.symm.trans eq)
  split
  · split <;> [exact .throw; rename_i h2]
    generalize eq1 : _ <$> (_ : Except Exception _) = F
    generalize eq2 : (fun ty : Expr => _) = P
    suffices ci.isPartial = false ∨ (c.safety == .safe) = false → F.WF P by
      split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
      split <;> [exact .throw; skip]
      rename_i h; simp [Decidable.imp_iff_not_or] at h
      exact this h
    subst eq1 eq2; intro h3
    refine this.map fun _ ⟨_, H⟩ => ?_
    have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq1 <| by
      revert h2 h3
      cases c.safety <;> simp [isAsSafeAs] <;> cases ci.isUnsafe <;> simp +decide
    have eq := h1.symm.trans h5
    exact main (.const h4 (List.mapM_eq_some.2 H) eq)
  · simp_all; let ⟨_, h⟩ := hinf; refine .pure (main h)

theorem inferLambda.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLambda.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  unfold inferLambda.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    generalize eqF : withLocalDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_lam] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom'}
        (domty : (c.withMLC m).venv.IsType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx dom')
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlam dom') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLocalDecl hdom domty le₁ fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLambda.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
        (by simp [← eqfvs, harr]) ?_ (by simp; rfl) ?_ (hr.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩, ?_, fun ty hty => h3 _ ⟨h2.1, hty.abstract1⟩⟩
        rw [eqfvs, ← eq]
        refine h2.2.instantiate1 fun h => ?_
        exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5
      have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
      have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
      exact main le domty' h1 nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .lam (ty' := dom') (body' := body') domty hdom hbody := h1
      exact main .rfl domty hdom _ hbody
  · subst ei
    refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, h2', e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2''⟩ := mwf.1.mkLambda_trS c.Ewf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.Ewf h2' (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2'' h3'
    refine mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) ▸
      ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2''⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    exact this.mp (fun _ => id) h3'.fvarsIn

theorem inferLambda.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLambda e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLambda.loop.WF (Nat.zero_le _) rfl rfl rfl rfl ?_ h1) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem inferForall.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkForall n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hus : us.toList.reverse.Forall₂ (VLevel.ofLevel c.lparams · = some ·) us')
    (hΔ : m.vlctx.SortList c.venv c.lparams.length us')
    (hlen : us'.length = n)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferForall.loop inferOnly arr us e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' u, c.TrTyping e₀ ty e' (.sort u) := by
  unfold inferForall.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    rw [Expr.instantiateList_forallE] at hei; subst ei
    refine (inferType.WF' ?_ ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
    · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    · intro h; let ⟨_, .forallE _ _ h _⟩ := hinf h; exact ⟨_, h⟩
    refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort h4, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' le fun a mwf' s' le₂ res => ?_
    have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
    refine inferForall.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
      (by simp [eqfvs, harr]) ?_ (by simp [eqfvs]; rfl) (hr.2.mono fun _ => .tail _)
      (by simpa using ⟨h4, hus⟩) (.cons hΔ domty) (by simp [hlen]) ?_
    · simp [he₀, ← eq]; congr 2
      refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
      · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
      · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
    · intro h; let ⟨_, .forallE (body' := body') _ _ hdom₁ hbody₁⟩ := hinf h
      refine have hΔ := .refl c.Ewf mwf.1.tr.wf; have H := hdom₁.uniq c.Ewf hΔ h1; ?_
      have H := H.of_r c.Ewf mwf.1.tr.wf.toCtx domty
      have ⟨_, hbody₂⟩ := hbody₁.defeqDFC c.Ewf <| .cons hΔ (ofv := none) nofun (.vlam H)
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', _, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine (ensureSortCore.WF h2).bind fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort (u' := u') h4, h5⟩ := h5
    obtain ⟨us, rfl⟩ : ∃ l, ⟨List.reverse l⟩ = us := ⟨us.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at hus ⊢
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    let ⟨h1', h2'⟩ := mwf.1.mkForall_trS c.Ewf h1 ⟨_, h3⟩ n hn
    have ⟨_, h3', h4'⟩ := mkForall_hasType hus hΔ h4 h3 n hn (hus.length_eq.trans hlen)
    simp [hdrop] at h1' h2' h4'
    refine have h := .sort h3'; .pure ⟨_, _, fun _ _ _ => h.fvarsIn, he₀ ▸ h1', h, h4'⟩

theorem inferForall.WF
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferForall e inferOnly).WF c s fun ty _ => ∃ e' u, c.TrTyping e ty e' (.sort u) :=
  (c.withMLC_self ▸ inferForall.loop.WF (Nat.zero_le _) rfl rfl rfl rfl hr .nil .nil rfl) hinf

theorem inferApp.loop.WF {c : VContext} {s : VState}
    {ll lm lr : List _}
    (stk : AppStack c.venv c.lparams c.vlctx (.mkAppRevList e lm) e' lr)
    (hbelow : FVarsBelow c.vlctx e fType)
    (hfty : c.TrExpr (fType.instantiateList lm) fty') (hety : c.HasType e' fty')
    (hargs : args = ll ++ lm.reverse ++ lr)
    (hj : j = ll.length) (hi : i = ll.length + lm.length) :
    RecM.WF c s (inferApp.loop e₀ ⟨args⟩ fType j i) fun ty _ =>
      ∃ e₁' ty', c.TrTyping (e.mkAppRevList lm |>.mkAppList lr) ty e₁' ty' := by
  subst i j; rw [inferApp.loop.eq_def]
  simp [hargs, Expr.instantiateList_reverse]
  have henv := c.Ewf; have hΔ := c.Δwf
  cases lr with simp
  | cons a lr =>
    let .app hf' ha' hf ha stk := stk
    have uf := hf'.uniqU henv hΔ hety
    split
    · rw [Expr.instantiateList_forallE] at hfty
      let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (lm := a::lm) stk ?_ ?_ (.app hf' ha') (by simp) rfl rfl
      · exact fun _ hP he => (hbelow _ hP he).2
      have ha0 := c.mlctx.noBV ▸ ha.closed
      simp [← Expr.instantiateList_instantiate1_comm ha0.looseBVarRange_zero]
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
    · simp [Nat.add_sub_cancel_left, Expr.instantiateRevList_reverse]
      refine (ensureForallCore.WF' hfty).bind fun _ _ _ ⟨hb, ⟨_, h2, h3⟩, eq⟩ => ?_
      obtain ⟨name, ty, body, bi, rfl⟩ := eq; simp [Expr.bindingBody!]
      let .forallE _ _ hty hbody := h2
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (ll := ll ++ lm.reverse) (lm := [a]) stk ?_ ?_
        (.app hf' ha') (by simp) (by simp) (by simp)
      · intro _ hP he
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
        exact (hb _ hP <| (hbelow _ hP he).instantiateList hlm).2
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
  | nil =>
    rw [← List.length_reverse, List.take_length, Expr.instantiateRevList_reverse]
    have ⟨_, hfty, h2⟩ := hfty
    refine .pure ⟨_, _, fun _ hP he => ?_, stk.tr, hfty, hety.defeqU_r henv hΔ h2.symm⟩
    have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
    exact (hbelow _ hP he).instantiateList hlm

theorem inferApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferApp e) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, he'⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
  refine (inferType.WF he'.tr).bind fun ty _ _ ⟨ty', hb, _, hty', ety⟩ => ?_
  have henv := c.Ewf; have hΔ := c.Δwf
  refine (inferApp.loop.WF (ll := []) (lm := []) he' hb
      (hty'.trExpr henv hΔ) ety rfl rfl rfl).le
    fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
  have := (e.mkAppList_getAppArgsList ▸ h1).uniq henv (.refl henv hΔ) he
  exact ⟨_, e.mkAppList_getAppArgsList ▸ hb, he, h2, h3.defeqU_l henv hΔ this⟩

theorem inferLet.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length) (nds hnds)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLet n hn nds hnds ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLet.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  unfold inferLet.loop
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom val body nd
    generalize eqF : withLetDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_letE] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom' val'}
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hval : (c.withMLC m).TrExprS (val.instantiateList fvs) val')
        (valty : (c.withMLC m).venv.HasType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx val' dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlet dom' val') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLetDecl hdom hval valty le₁ fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLet.loop.WF (Nat.succ_le_succ hn) (some nd :: nds)
        (by simp [hnds]) (by simp [hdrop]) (by simp [← eqfvs, harr])
        ?_ (by simp; rfl) ?_ (hr.2.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => ?_⟩, ?_, fun ty hty => h3 _ ?_⟩
        · simp [or_imp, forall_and]
          exact ⟨(fvarsIn_iff.1 h2.1).1, (fvarsIn_iff.1 h2.2.1).1⟩
        · rw [eqfvs, ← eq]
          refine h2.2.2.instantiate1 fun h => ?_
          exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
        · simp; split <;> rename_i h
          · exact ⟨h2.1, h2.2.1, hty.abstract1⟩
          · rw [Expr.lowerLooseBVars_eq_instantiate (v := .sort .zero) (by simpa using h)]
            exact hty.abstract1.instantiate1 rfl
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind
        fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5; have le := le.trans le₂
      refine (checkType.WF ?_).bind_le le fun ty _ le ⟨val', ty', _, h4, h5, h6⟩ => ?_
      · apply hr.2.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (isDefEq.WF h5 h1).bind_le le fun b _ le h7 => ?_
      cases b <;> simp
      · exact .getEnv <| .getLCtx .throw
      have valty := h6.defeqU_r c.Ewf mwf.1.tr.wf.toCtx (h7 rfl)
      exact main le h1 h4 valty nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .letE (ty' := dom') (body' := body') valty hdom hval hbody := h1
      exact main .rfl hdom hval valty _ hbody
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, hty, e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLet_trS c.Ewf h1 h3 n hn nds hnds
    have h3' := (mwf.1.mkForall_trS c.Ewf hty (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    erw [mwf.1.mkForall_eq _ _ (eqfvs ▸ harr)]
    refine ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2'⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    refine this.mp (fun _ => id) h3'.fvarsIn
termination_by e

theorem inferLet.WF
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLet e inferOnly).WF c s fun ty _ =>
      ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLet.loop.WF (Nat.zero_le _) [] rfl rfl rfl rfl rfl ?_ hr) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

axiom inferProj.WF
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ ty', c.TrTyping (.proj st i e) ty e' ty' -- := sorry

theorem literal_typeName_is_primitive {l : Literal} :
    Environment.primitives.contains l.typeName := by
  simp [Environment.primitives, NameSet.ofList]
  cases l <;> simp +decide [Literal.typeName, NameSet.contains]

theorem infer_literal {c : VContext} (H : c.venv.contains l.typeName) :
    c.TrTyping (.lit l) l.type (.trLiteral l) (.const l.typeName []) := by
  refine
    have := TrExprS.trLiteral c.Ewf c.hasPrimitives l H
    ⟨fun _ _ _ => .litType, this.1, ?_, this.2⟩
  rw [← Literal.mkConst_typeName]
  have ⟨_, h⟩ := this.2.isType c.Ewf c.Δwf
  have ⟨_, h1, _, h3⟩  := h.const_inv c.Ewf c.Δwf
  exact .const h1 rfl h3

theorem infer_sort {c : VContext} (H : VLevel.ofLevel c.lparams u = some u') :
    c.TrTyping (.sort u) (.sort u.succ) (.sort u') (.sort u'.succ) := by
  refine ⟨fun _ _ _ => (?a).fvarsIn, .sort H, ?a, .sort (.of_ofLevel H)⟩
  exact .sort <| by simpa [VLevel.ofLevel]

theorem inferType'.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  unfold inferType'; lift_lets; intro F F1 F2 --; simp
  split <;> [exact .throw; refine .get <| .get ?_]
  split
  · rename_i h; refine .stateWF fun wf => .pure ?_
    generalize hic : cond .. = ic at h
    have : ic.WF c s := by
      subst ic; cases inferOnly <;> [exact wf.inferTypeC_wf; exact wf.inferTypeI_wf]
    exact (this h).2.2.2.2 h1
  generalize hP : (fun ty:Expr => _) = P
  have hF {ty e' ty' s} (H : c.TrTyping e ty e' ty') : (F ty).WF c s P := by
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : InferCache.WF c s ic) : InferCache.WF c s (ic.insert e ty) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv H eq BEq.rfl) (.eqv eq ?_) ?_
      · exact H.2.1.fvarsIn.mono wf.ngen_wf
      · exact H.2.2.1.fvarsIn.mono wf.ngen_wf
    subst P; revert s'; cases inferOnly <;> (dsimp -zeta; intro s'; refine ⟨.rfl, ?_, _, _, H⟩)
    · exact { wf with inferTypeC_wf := hic wf.inferTypeC_wf }
    · exact { wf with inferTypeI_wf := hic wf.inferTypeI_wf }
  unfold F1; refine .get ?_; split
  · extract_lets n G1; split
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h => ?_
      have ⟨_, h, _⟩ := c.trenv.find? h <|
        isAsSafeAs_of_safe (c.safePrimitives h literal_typeName_is_primitive).1
      simp [n, G1]; exact hF (infer_literal ⟨_, h⟩)
    · rename_i h; have ⟨_, h⟩ := hinf (by simpa using h)
      have := h.lit_has_type c.Ewf c.hasPrimitives
      simp [n, G1]; exact hF (infer_literal this)
  · refine (inferType'.WF (by exact h1) ?_).bind fun _ _ _ ⟨_, _, hb, h1, h⟩ => ?_
    · exact fun h => let ⟨_, .mdata h⟩ := hinf h; ⟨_, h⟩
    exact hF ⟨hb, .mdata h1, h⟩
  · refine (inferType'.WF (by exact h1) ?_).bind fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
    · exact fun h => let ⟨_, .proj h ..⟩ := hinf h; ⟨_, h⟩
    exact (inferProj.WF h1 h2 h3).bind fun ty _ _ ⟨ty', h⟩ => hF h
  · exact .readThe <| (M.WF.liftExcept inferFVar.WF).lift.bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact .throw
  · rename_i h _; simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at h
  · split <;> rename_i h
    · refine .readThe <| (M.WF.liftExcept (checkLevel.WF h1)).lift.bind fun _ _ _ ⟨_, h⟩ => ?_
      exact hF (infer_sort h)
    · let ⟨_, .sort h⟩ := hinf (by simpa using h)
      exact hF (infer_sort h)
  · refine .readThe <|
      (M.WF.liftExcept (inferConstant.WF h1 hinf)).lift.bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact (inferLambda.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact (inferForall.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · split <;> rename_i h
    · let ⟨_, h⟩ := hinf h; exact (inferApp.WF h).bind fun _ _ _ ⟨_, h⟩ => hF h
    refine (inferType'.WF h1.1 ?_).bind fun _ _ _ ⟨_, _, hfb, hf1, hf2, hf3⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ h _⟩ := hinf h; ⟨_, h⟩
    refine .stateWF fun wf => ?_
    refine (ensureForallCore.WF hf2).bind fun _ _ _ H => ?_
    obtain ⟨hb, h2, name, dType, body, bi, rfl⟩ := H
    let ⟨_, .forallE (ty' := dType') hl1 hl2 hl3 hl4, hl5⟩ := h2
    extract_lets _ G1
    refine (inferType'.WF h1.2 ?_).bind fun aType _ _ ⟨_, aType', hab, ha1, ha2, ha3⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ _ h⟩ := hinf h; ⟨_, h⟩
    extract_lets G2
    suffices ∀ {s b} (H : b = true → c.IsDefEqU dType' aType'), RecM.WF c s (G2 b) P by
      split
      · refine .bind ?_ (Q := fun b _ => b = true → c.IsDefEqU dType' aType') fun b _ _ => this
        intro _ mwf wf _ _ eq
        let c' := { c with eagerReduce := true }
        have ⟨_, h1, h2, h3, h4⟩ := isDefEq.WF (c := c') hl3 ha2 _ mwf { wf with } _ _ eq
        exact ⟨_, h1, h2, { h3 with }, h4⟩
      · exact (isDefEq.WF hl3 ha2).bind fun b _ _ => this
    subst G2; dsimp; rintro s ⟨⟩ H
    · exact .getEnv <| .getLCtx .throw
    simp [G1, Expr.bindingBody!]
    have hf3 := hf3.defeqU_r c.Ewf c.Δwf hl5.symm
    have ha3 := ha3.defeqU_r c.Ewf c.Δwf (H rfl).symm
    subst hP; refine hF ⟨?_, .app hf3 ha3 hf1 ha1, hl4.inst c.Ewf ha3 ha1, .app hf3 ha3⟩
    exact fun _ hP he => (hfb.trans hb _ hP he.1).2.instantiate1 he.2
  · exact (inferLet.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
