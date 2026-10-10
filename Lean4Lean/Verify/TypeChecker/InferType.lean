import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.TypeChecker.Projection
import Lean4Lean.Verify.EquivManager

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem ensureForallCore.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf, _, _, _, _, rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .forallE .. := e
    exact .pure ⟨hb, he, _, _, _, _, rfl⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF' {c : VContext} {s : State} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  let ⟨_, he, eq⟩ := he
  (ensureForallCore.WF he).mono fun _ _ _ ⟨h1, h2, h3⟩ =>
    ⟨h1, h2.defeq c.Ewf c.Δwf eq, h3⟩

theorem ensureForallCore.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.LevelsBelow e e1 := by
  simp [ensureForallCore]; split
  · exact .pure .rfl
  refine (whnf.WF_levels he).bind fun e _ _ hl => ?_; split
  · exact .pure hl
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.ParamUniformBelow pfx e e1 := by
  simp [ensureForallCore]; split
  · exact .pure .rfl
  refine (whnf.WF_paramUniform he hp).bind fun e _ _ hl => ?_; split
  · exact .pure hl
  exact .getEnv <| .getLCtx .throw

theorem ensureSortCore.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ => c.LevelsBelow e e1 := by
  simp [ensureSortCore]; split
  · exact .pure .rfl
  refine (whnf.WF_levels he).bind fun e _ _ hl => ?_; split
  · exact .pure hl
  exact .getEnv <| .getLCtx .throw

theorem ensureSortCore.WF_below {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      ((∃ u, e1 = .sort u) ∧ c.TrExpr e1 e' ∧ c.FVarsBelow e e1) ∧ c.LevelsBelow e e1 :=
  (ensureSortCore.WF he).and (ensureSortCore.WF_levels he)

theorem ensureForallCore.WF_below {c : VContext} {s : State} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => (c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi) ∧ c.LevelsBelow e e1 :=
  let ⟨_, he', _⟩ := he
  (ensureForallCore.WF' he).and (ensureForallCore.WF_levels he')

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

/-- The type of a free variable is its declared type, so it lies in every universe scope of the
variable. -/
theorem inferFVar.WF_levels {c : VContext} :
    (inferFVar c.toContext name).WF fun ty => c.LevelsBelow (.fvar name) ty := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  exact fun Us P hs _ hP => (hs.2 _ _ hP h).1

theorem inferConstant.WF_all {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      (∃ e' ty', c.TrTyping (.const name ls) ty e' ty') ∧
      ∀ Us, (∀ l ∈ ls, l.paramsIn Us = true) → ty.levelParamsIn Us = true := by
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
  have main {e'} (he : c.TrExprS (.const name ls) e') : (∃ e' ty',
      c.TrTyping (.const name ls) (ci.instantiateTypeLevelParams ls) e' ty') ∧
      ∀ Us, (∀ l ∈ ls, l.paramsIn Us = true) →
        (ci.instantiateTypeLevelParams ls).levelParamsIn Us = true := by
    let .const h4 H' eq := id he
    have ⟨_, _, h5, h6⟩ := c.trenv.find?_uniq eq1 h4
    refine ⟨?_, fun Us hUs => ?_⟩
    · have H := List.mapM_eq_some.1 H'
      have s0 := h6.instL c.Ewf (Δ := []) trivial H' (h5.trans eq.symm)
      have s1 := s0.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
      rw [(c.Ewf.ordered.closedC h4).instL.liftN_eq (Nat.le_refl _)] at s1
      have ⟨_, s1, s2⟩ := s1
      refine ⟨_, _, ?_, he, s1, .defeqU_r c.Ewf c.Δwf s2.symm ?_⟩
      · intro _ _ _; exact s0.fvarsIn.mono nofun
      · exact .const h4 (.of_mapM_ofLevel H') (H.length_eq.symm.trans eq)
    · exact Expr.levelParamsIn_instantiateLevelParams h6.levelParamsIn hUs
        (h5.trans eq.symm)
  split
  · split <;> [exact .throw; rename_i h2]
    generalize eq1 : _ <$> (_ : Except Exception _) = F
    generalize eq2 : (fun ty : Expr => _) = P
    suffices ci.isPartial = false ∨ c.safety ≠ .safe → F.WF P by
      split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
      split <;> [exact .throw; apply this]
      rename_i h; simpa [Decidable.or_iff_not_imp_left, ConstantInfo.isPartial] using h
    subst eq1 eq2; intro h3
    refine this.map fun _ ⟨_, H⟩ => ?_
    have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq1 <| by
      revert h2 h3
      simp [ConstantInfo.safety]
      split <;> simp +contextual [*]
      split <;> simp [DefinitionSafety.le_safe, *]
      cases c.safety <;> decide
    have eq := h1.symm.trans h5
    exact main (.const h4 (List.mapM_eq_some.2 H) eq)
  · simp_all; let ⟨_, h⟩ := hinf; refine .pure (main h)

theorem inferConstant.WF {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      ∃ e' ty', c.TrTyping (.const name ls) ty e' ty' :=
  (inferConstant.WF_all H hinf).mono fun _ h => h.1

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
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.orderedStrong mwf'.1.tr.wf⟩
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
    have ⟨_, h2', e2⟩ := h2.trExpr c.Ewf.orderedStrong wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2''⟩ := mwf.1.mkLambda_trS c.Ewf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.Ewf h2' (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2'' h3'
    refine mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) (m.noBV ▸ h2'.closed) ▸
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
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.Ewf.orderedStrong mwf'.1.tr.wf⟩
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

theorem inferApp.loop.WF {c : VContext} {s : State}
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

theorem inferApp.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
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
      · rw [he₀, eqfvs, ← eq]; simp [MLCtx.mkLetArg]; congr 2
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
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.orderedStrong mwf'.1.tr.wf⟩
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
    have ⟨_, hty, e2⟩ := h2.trExpr c.Ewf.orderedStrong wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLet_trS c.Ewf h1 h3 n hn nds hnds
    have h3' := (mwf.1.mkForall_trS c.Ewf hty (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    erw [mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) (m.noBV ▸ hty.closed)]
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

theorem inferProj.WF_all (hb : c.FVarsBelow e ety) (he : c.TrExprS e e')
    (hty : c.TrExprS ety ety') (hasty : c.HasType e' ety') (hpfx : s.ngen.namePrefix = pfx) :
    (inferProj st i e ety).WF c s fun ty _ =>
      ((∃ projected ty', c.TrTyping (.proj st i e) ty projected ty') ∧
      ∀ Us P, c.UniverseScope Us P → e.levelParamsIn Us = true →
        ety.levelParamsIn Us = true → FVarsIn P e → ty.levelParamsIn Us = true) ∧
      ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → (Expr.proj st i e).ParamUniformIn c.env heads As ls →
        ety.ParamUniformIn c.env heads As ls → FVarsIn P e → ty.ParamUniformIn c.env heads As ls := by
  unfold inferProj; lift_lets; intro pe
  refine ((whnf.WF_below hty).and (whnf.WF_paramUniform hty hpfx)).bind
    fun type _ le₀ ⟨⟨hbt, hltT, tT', htT, hdefeq⟩, hhT⟩ => ?_
  have hpfx₀ := State.LE.namePrefix_eq hpfx le₀
  rw [Expr.withApp_eq]; dsimp only
  refine .getEnv ?_
  -- the two shapes of failure: a bare throw, and a throw followed by the rest of the block
  have hfail' {α : Type} {s : State} {Q : α → State → Prop} :
      ((do let l ← getLCtx; throw (Exception.invalidProj c.env l pe)) : RecM α).WF c s Q :=
    .getLCtx .throw
  have hfail {α β : Type} {s : State} {Q : β → State → Prop} {k : α → RecM β} :
      (((do let l ← getLCtx; throw (Exception.invalidProj c.env l pe)) : RecM α) >>= k).WF c s Q :=
    (RecM.WF.getLCtx (Q := fun _ _ => False) .throw).bind fun _ _ _ h => h.elim
  split <;> [rename_i I_name I_levels hI; exact hfail']
  split <;> [exact hfail; rename_i hname]
  obtain rfl : st = I_name := by simpa using hname
  refine (M.WF.liftExcept envGet.WF).lift.bind fun ci _ le₁ hci => ?_
  have hpfx₁ := State.LE.namePrefix_eq hpfx₀ le₁
  split <;> [rename_i I_val; exact hfail']
  split <;> [rename_i mkC hsingle; exact hfail']
  split <;> [exact hfail; rename_i harity]
  have harity : type.getAppArgs.size = I_val.numParams + I_val.numIndices := by simpa using harity
  refine (M.WF.liftExcept envGet.WF).lift.bind fun cci _ le₂ hcci => ?_
  have hpfx₂ := State.LE.namePrefix_eq hpfx₁ le₂
  -- the constant the structure lists is a constructor of the structure
  obtain ⟨c_val, rfl, hinduct', -⟩ :=
    c.listedConstructors st I_val hci mkC (by simp [hsingle]) cci hcci
  -- the spine of the whnf'd structure type
  have htT' : c.TrExprS ((Expr.const st I_levels).mkAppList type.getAppArgsList) tT' := by
    rw [← hI, type.mkAppList_getAppArgsList]; exact htT
  have ⟨fn', stk⟩ := AppStack.build htT'
  have ⟨args', hargs, htT''⟩ := stk.translatedArguments
  have .const (us' := ls') hfc hls hlen := stk.tr
  -- registry facts
  have ⟨info, hinfo, hname, decl, doms, result, hwf, hctor, hshape, hvalid, hhead, hdn, hdu, hle,
    hnp, hnf, hnf', hsp, hsi, hidxs, hind, hsort, hparam⟩ :=
    VContext.registryShape hci hfc hsingle hcci hinduct'
  subst hname
  obtain ⟨indType, hind⟩ := hind
  rw [hfc] at hind; cases hind
  have heq := htT'.uniq c.Ewf (.refl c.Ewf c.Δwf) htT''
  have hlsWF := VLevel.WF.of_mapM_ofLevel hls
  have hlen' : ls'.length = info.uvars := (List.mapM_eq_some.1 hls).length_eq.symm.trans hlen
  have hargsLen : args'.length = type.getAppArgs.size := by
    rw [← Lean4Lean.List.Forall₂.length_eq hargs, ← Expr.getAppArgs_toList, Array.length_toList]
  have hargsLen' : args'.length = info.nparams + info.nindices := by
    rw [hargsLen, harity, hsp, hsi]
  have hargsGet : ∀ k (hk : k < type.getAppArgs.size),
      c.TrExprS type.getAppArgs[k] (args'[k]'(by omega)) := by
    intro k hk
    have := Lean4Lean.List.forall₂_getElem hargs k
      (by rw [← Expr.getAppArgs_toList, Array.length_toList]; omega) (by omega)
    simpa [← Expr.getAppArgs_toList] using this
  -- typing of the major and the sort of its type
  have hety : c.HasType e' (VExpr.mkApps (.const st ls') args') :=
    (hasty.defeqU_r c.Ewf c.Δwf hdefeq.symm).defeqU_r c.Ewf c.Δwf heq
  have ⟨uS, hetyS⟩ := hety.isType c.Ewf c.Δwf
  -- the constructor type, translated syntactically up to universe levels
  have ⟨_, h5, h6⟩ := (c.trenv.find?_uniq hcci hctor).2
  have hcT : ∃ T₀,
      TrExprS c.venv c.lparams []
        ((ConstantInfo.ctorInfo c_val).instantiateTypeLevelParams I_levels) T₀ ∧
      c.TrExprS ((ConstantInfo.ctorInfo c_val).instantiateTypeLevelParams I_levels) T₀ ∧
      VExpr.LEquiv c.lparams.length T₀ (info.ctorType.instL ls') := by
    have ⟨T₀, hT₀, L⟩ := h6.instL_lequiv hls (h5.trans hlen.symm) c.Ewf (Δ := []) trivial
    refine ⟨T₀, hT₀, ?_, L⟩
    have := hT₀.weakFV c.Ewf.orderedStrong (.from_nil c.mlctx.noBV) c.Δwf
    rwa [(VExpr.WF.closedN c.Ewf.orderedStrong (hT₀.wf c.Ewf.orderedStrong (by trivial)) trivial).liftN_eq
      (j := 0) (Nat.le_refl 0)] at this
  obtain ⟨T₀, hT₀nil, hT₀, L⟩ := hcT
  rw [hshape, VExpr.instL_wrapForalls] at L
  obtain ⟨doms₀, result₀, rfl, hdoms, hres₀⟩ := L.wrapForalls_inv
  have hdomsLen : doms₀.length = doms.length := by
    simpa using Lean4Lean.List.Forall₂.length_eq hdoms
  have hdomsK : ∀ k (hk : k < doms.length),
      VExpr.LEquiv c.lparams.length (doms₀[k]'(by omega)) (doms[k].instL ls') := by
    intro k hk
    have := Lean4Lean.List.forall₂_getElem hdoms k (by omega) (by simpa using hk)
    simpa using this
  have hclosed : info.ctorType.Closed := by
    have ⟨_, h⟩ := hwf
    exact VExpr.WF.closedN c.Ewf.orderedStrong ⟨_, h⟩ trivial
  -- the parameters
  have hP'len : (args'.take info.nparams).length = info.nparams := by simp; omega
  have hnpLen : info.nparams ≤ doms₀.length := by omega
  refine (instantiateProjectionParameters.WF_all hT₀ (ds := doms₀) (position := 0)
      (xs' := args'.take info.nparams) (by rw [hsp]; exact hnpLen) (by rw [hP'len, hsp]) ?_ ?_
      hpfx₂).bind fun r _ le₃ H => ?_
  · intro k hk
    rw [hsp] at hk
    refine ⟨type.getAppArgs[k]'(by omega), ?_, ?_⟩
    · simp only [Nat.zero_add]; exact Array.getElem?_eq_getElem _
    · have := hargsGet k (by omega)
      rwa [List.getElem_take]
  · intro k hk
    rw [hsp] at hk
    refine ⟨(doms[k]'(by omega) |>.instL ls').instOuter (args'.take k), ?_, ?_⟩
    · have := (hdomsK k (by omega)).instOuter (args'.take k)
      rwa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    · have := hparam ls' args' hlen' hargsLen' ⟨_, hetyS⟩ k hk (by omega)
      rwa [List.getElem_take]
  split <;> [rename_i afterParameters hafter; exact hfail']
  obtain ⟨⟨⟨⟨R₁, hR₁, hafter'⟩, hfvAfter⟩, hlvAfter⟩, hhAfter⟩ := H _ rfl
  have hpfx₃ := State.LE.namePrefix_eq hpfx₂ le₃
  rw [VProjectionInfo.instantiateProjectionParameters_wrapForalls _ _ _
    (by rw [hP'len]; exact hnpLen)] at hR₁
  cases hR₁
  rw [hP'len] at hafter'
  generalize hds_def : VExpr.instDomsAt (doms₀.drop info.nparams) (args'.take info.nparams) 0 = ds
    at hafter'
  -- the sort level of the structure type
  refine (getSortLevel.WF htT).bind fun l _ le₄ ⟨u', hu', hsortT⟩ => ?_
  have hpfx₄ := State.LE.namePrefix_eq hpfx₃ le₄
  have hsortT' : c.HasType (VExpr.mkApps (.const st ls') args') (.sort u') :=
    hsortT.defeqU_l c.Ewf c.Δwf heq
  have hcanon := hsort ls' args' hlen' hargsLen' ⟨_, hsortT'⟩
  have hu'canon : u' ≈ info.resultLevel.inst ls' :=
    (hsortT'.uniqU c.Ewf c.Δwf hcanon).sort_inv c.Ewf c.Δwf
  -- the domains of the field binders, as instantiations of the constructor's domains
  have hdsLen : ds.length = doms₀.length - info.nparams := by rw [← hds_def]; simp
  have hds : ∀ m (hm : m < ds.length),
      (ds[m]'hm).instOuter (projs st e' 0 m) =
        (doms₀[info.nparams + m]'(by omega)).instOuter
          (args'.take info.nparams ++ (List.range m).map fun j => .proj st j e') := by
    intro m hm
    have hm' : m < (doms₀.drop info.nparams).length := by rw [hdsLen] at hm; simpa using hm
    subst hds_def
    rw [VExpr.instDomsAt_getElem _ _ _ _ hm', List.getElem_drop]
    simp only [projs, Nat.zero_add, VExpr.instOuter_eq_instOuterAt, VExpr.instOuterAt_append,
      List.length_map, List.length_range]
  -- the guard of `projDF` for the sort of a field
  let G : VLevel → Prop := fun u => (info.resultLevel.inst ls').IsNeverZero ∨ u ≈ .zero
  have hG : (!l.isNeverZero) = false → ∀ u, G u := by
    intro h u
    exact .inl ((ofLevel_isNeverZero hu' (by simpa using h)).of_equiv hu'canon)
  have hclosed : info.ctorType.Closed := by
    have ⟨_, h⟩ := hwf
    exact VExpr.WF.closedN c.Ewf.orderedStrong ⟨_, h⟩ trivial
  -- the typing of an earlier field's projection at its binder
  have hproj : ∀ m (hm : m < ds.length) u,
      c.HasType ((ds[m]'hm).instOuter (projs st e' 0 m)) (.sort u) → G u →
      c.HasType (.proj st m e') ((ds[m]'hm).instOuter (projs st e' 0 m)) := by
    intro m hm u hu hGu
    rw [hds m hm] at hu ⊢
    have hlt : info.nparams + m < doms.length := by omega
    have hfield := VProjectionInfo.fieldType_eq_instOuter info hshape hlen' hP'len hlt
      (typeName := st) (major := e')
    have hL := ((hdomsK _ hlt).instOuter
      (args'.take info.nparams ++ (List.range m).map fun j => VExpr.proj st j e')).defeq
      c.Ewf c.Δwf.toCtx ⟨_, hu⟩
    have hFty := hu.defeqU_l c.Ewf c.Δwf hL
    have hp := VEnv.IsDefEq.projDF hinfo hlsWF hlen' hP'len (indexArgs := args'.drop info.nparams)
      (by simp; omega) hfield hFty (by rw [List.take_append_drop]; exact hety)
      (by rw [List.take_append_drop]; exact hety) hclosed hGu
    exact hp.hasType.2.defeqU_r c.Ewf c.Δwf hL.symm
  -- the fields
  by_cases hidx : c_val.numFields ≤ i
  · -- past the fields, the walk reaches the constructor's result type, an application of the
    -- rigid structure type, which `whnf` does not turn into a binder: the walk fails
    obtain ⟨r, rfl⟩ : ∃ r, i = ds.length + r := ⟨i - ds.length, by omega⟩
    have hrigid := c.Ewf.projectionRigid hinfo
    rw [instantiateProjectionFields_add, bind_assoc]
    refine (instantiateProjectionFields.WF_all (st := st) (G := G)
      (b := result₀.instOuterAt (List.take info.nparams args') (doms₀.length - info.nparams))
      he (.inr rfl) hG hafter' (Nat.le_refl _)
      (fun m hm u hu hGu => by simpa using hproj m (by omega) u (by simpa using hu) hGu)
      hpfx₄).bind fun o _ _ H => ?_
    rcases o with _ | t
    · exact hfail'
    obtain ⟨⟨⟨⟨R, hR, htR⟩, -⟩, -⟩, -⟩ := H t rfl
    rw [VProjectionInfo.instantiateProjectionParameters_wrapForalls _ _ _ (by simp),
      projs_length, List.drop_length, Nat.sub_self] at hR
    simp only [VExpr.instDomsAt, VExpr.wrapForalls, List.foldr_nil, Option.some.injEq] at hR
    subst hR
    have hRn : (VExpr.instOuterAt (result₀.instOuterAt (List.take info.nparams args')
        (doms₀.length - info.nparams)) (projs st e' 0 ds.length) 0).HeadName st :=
      (((VExpr.HeadName.of_getAppFnArgs hhead).instL).of_lequiv hres₀).instOuterAt _ _
        |>.instOuterAt _ _
    refine (instantiateProjectionFields.WF_stuck htR hRn hrigid r _ _).bind fun o' _ _ H' => ?_
    rcases o' with _ | t'
    · exact hfail'
    obtain rfl := H' t' rfl
    refine (whnf.WF_not_forallE htR hRn hrigid).bind fun w _ _ hw => ?_
    split
    · exact absurd rfl (hw _ _ _ _)
    · exact hfail'
  replace hidx : i < c_val.numFields := by omega
  have hile : i ≤ ds.length := by omega
  refine (instantiateProjectionFields.WF_all (st := st) (G := G) he (.inr rfl) hG
    hafter' hile (fun m hm u hu hGu => by simpa using hproj m (by omega) u (by simpa using hu) hGu)
    hpfx₄).bind fun r _ le₅ H => ?_
  have hpfx₅ := State.LE.namePrefix_eq hpfx₄ le₅
  split <;> [skip; exact hfail']
  obtain ⟨⟨⟨⟨R₂, hR₂, hsel'⟩, hfvSel⟩, hlvSel⟩, hhSel⟩ := H _ rfl
  rw [VProjectionInfo.instantiateProjectionParameters_wrapForalls _ _ _ (by simpa using hile)]
    at hR₂
  cases hR₂
  rw [projs_length] at hsel'
  -- the selected field's binder
  obtain ⟨F₀, rest₀, hdrop⟩ : ∃ F₀ rest₀, ds.drop i = F₀ :: rest₀ := by
    cases h : ds.drop i with
    | nil => simp at h; omega
    | cons F₀ rest₀ => exact ⟨_, _, rfl⟩
  rw [hdrop] at hsel'
  have hsel'' : c.TrExprS _ (.forallE (F₀.instOuterAt (projs st e' 0 i) 0)
      (VExpr.wrapForalls (VExpr.instDomsAt rest₀ (projs st e' 0 i) 1) _)) := hsel'
  have hF₀ : F₀ = ds[i]'(by omega) := by
    have h1 : (ds.drop i).head? = some F₀ := by rw [hdrop]; rfl
    rw [List.head?_drop, List.getElem?_eq_getElem (by omega)] at h1
    exact (Option.some.inj h1).symm
  have hFeq : F₀.instOuterAt (projs st e' 0 i) 0 =
      (doms₀[info.nparams + i]'(by omega)).instOuter
        (args'.take info.nparams ++ (List.range i).map fun j => .proj st j e') := by
    rw [← VExpr.instOuter_eq_instOuterAt, hF₀]; exact hds i (by omega)
  generalize F₀.instOuterAt (projs st e' 0 i) 0 = F at hsel'' hFeq
  subst hFeq
  refine ((whnf.WF_below_of_fvarsIn hsel'').and (whnf.WF_paramUniform hsel'' hpfx₅)).bind fun w _ _ Hw => ?_
  obtain ⟨⟨⟨hbw, -, hs⟩, hlw⟩, hhw⟩ := Hw
  have hw := hs _ _ rfl
  split <;> [rename_i n domain body bi; exact hfail']
  let .forallE hF _ hdom _ := hw
  -- the field type of the projection is the selected binder up to universe levels
  have hlt : info.nparams + i < doms.length := by omega
  have hfield := VProjectionInfo.fieldType_eq_instOuter info hshape hlen' hP'len hlt
    (typeName := st) (major := e')
  have ⟨_, hF'⟩ := hF
  have hL := ((hdomsK _ hlt).instOuter
    (args'.take info.nparams ++ (List.range i).map fun j => VExpr.proj st j e')).defeq
    c.Ewf c.Δwf.toCtx ⟨_, hF'⟩
  -- the conclusion, given the sort of the field type and the guard
  have final {s : State} (fl : VLevel)
      (hFl : c.HasType ((doms₀[info.nparams + i]'(by omega)).instOuter
        (args'.take info.nparams ++ (List.range i).map fun j => .proj st j e')) (.sort fl))
      (hGl : G fl) :
      RecM.WF c s (pure domain) fun ty _ =>
        ((∃ projected ty', c.TrTyping (.proj st i e) ty projected ty') ∧
        ∀ Us P, c.UniverseScope Us P → e.levelParamsIn Us = true →
          ety.levelParamsIn Us = true → FVarsIn P e → ty.levelParamsIn Us = true) ∧
        ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P →
          (Expr.proj st i e).ParamUniformIn c.env heads As ls →
          ety.ParamUniformIn c.env heads As ls → FVarsIn P e → ty.ParamUniformIn c.env heads As ls := by
    have hFty := hFl.defeqU_l c.Ewf c.Δwf hL
    have hp := VEnv.IsDefEq.projDF hinfo hlsWF hlen' hP'len (indexArgs := args'.drop info.nparams)
      (by simp; omega) hfield hFty (by rw [List.take_append_drop]; exact hety)
      (by rw [List.take_append_drop]; exact hety) hclosed hGl
    have hpF := hp.hasType.2.defeqU_r c.Ewf c.Δwf hL.symm
    have hmem : ∀ k a, type.getAppArgs[0 + k]? = some a → a ∈ type.getAppArgsList :=
      fun k a ha => List.mem_of_getElem? (by
        rw [← Expr.getAppArgs_toList]; simpa [Array.getElem?_toList] using ha)
    have hfvT₀ {P} : FVarsIn P
        ((ConstantInfo.ctorInfo c_val).instantiateTypeLevelParams I_levels) :=
      hT₀nil.fvarsIn.mono fun _ h => absurd h (by simp)
    refine .pure ⟨⟨⟨.proj st i e', _, ?_, .proj he ⟨_, hpF⟩, hdom, hpF⟩, ?_⟩,
      ?_⟩
    · intro P hP hfv
      have hfve : FVarsIn P e := hfv
      have hfvtype := hbt P hP (hb P hP hfve)
      have hfvargs : ∀ a ∈ type.getAppArgsList, FVarsIn P a :=
        (FVarsIn.mkAppList.1 (type.mkAppList_getAppArgsList ▸ hfvtype)).2
      have h1 := hfvAfter P hP hfvT₀ fun k _ a ha => hfvargs a (hmem k a ha)
      exact (hbw P hP (hfvSel P hP h1 hfve)).1
    · intro Us P hs hle hlety hP
      have hfvtype := hbt P hs.1 (hb P hs.1 hP)
      have hltype := hltT Us P hs hlety (hb P hs.1 hP)
      have hfvargs : ∀ a ∈ type.getAppArgsList, FVarsIn P a :=
        (FVarsIn.mkAppList.1 (type.mkAppList_getAppArgsList ▸ hfvtype)).2
      have hlargs : ∀ a ∈ type.getAppArgsList, a.levelParamsIn Us = true :=
        fun a h => Expr.levelParamsIn_of_mem_getAppArgsList hltype h
      have hlsU : ∀ l ∈ I_levels, l.paramsIn Us = true := by
        have := Expr.levelParamsIn_getAppFn hltype
        rw [hI] at this; simpa [Expr.levelParamsIn] using this
      have hlT₀ : ((ConstantInfo.ctorInfo c_val).instantiateTypeLevelParams I_levels).levelParamsIn
          Us = true :=
        Expr.levelParamsIn_instantiateLevelParams h6.levelParamsIn hlsU (h5.trans hlen.symm)
      have h1 := hfvAfter P hs.1 hfvT₀ fun k _ a ha => hfvargs a (hmem k a ha)
      have l1 := hlvAfter Us P hs hlT₀ hfvT₀ fun k _ a ha =>
        ⟨hlargs a (hmem k a ha), hfvargs a (hmem k a ha)⟩
      have l2 := hlvSel Us P hs l1 h1 hle hP
      have l3 := hlw Us P hs l2 (hfvSel P hs.1 h1 hP)
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at l3
      exact l3.1
    · intro heads As ls P hs hl hlety hP
      have hp := hs.params.fvars
      have ⟨hok, hle⟩ := hl.proj_inv
      have hfvtype := hbt P hs.up (hb P hs.up hP)
      have htype := hhT heads As ls P hs hlety (hb P hs.up hP)
      have hfvargs : ∀ a ∈ type.getAppArgsList, FVarsIn P a :=
        (FVarsIn.mkAppList.1 (type.mkAppList_getAppArgsList ▸ hfvtype)).2
      have hcnot := hok.2 I_val hci _ (by rw [hsingle]; exact .head _)
      have hT₀ : ((ConstantInfo.ctorInfo c_val).instantiateTypeLevelParams I_levels).ParamUniformIn
          c.env heads As ls :=
        .instantiateLevelParams_of_avoids (hs.env.type_avoids hcci hcnot) (hs.env.type_projs hcci)
      have h1 := hfvAfter P hs.up hfvT₀ fun k _ a ha => hfvargs a (hmem k a ha)
      have k1 := hhAfter heads As ls P hs hT₀ hfvT₀ fun k _ a ha =>
        ⟨htype.of_mem_getAppArgsList hp (hmem k a ha), hfvargs a (hmem k a ha)⟩
      have k2 := hhSel heads As ls P hs k1 h1 hle hP hok
      exact (hhw heads As ls P hs k2 (hfvSel P hs.up h1 hP)).forallE_inv.1
  split
  · rename_i hmp
    refine (isProp.WF hdom).bind fun bp _ _ hbp => ?_
    split <;> [exact hfail; rename_i hbp']
    exact final .zero (hbp (by simpa using hbp')) (.inr rfl)
  · rename_i hmp
    exact final _ hF' (hG (by simpa using hmp) _)


theorem inferProj.WF (hb : c.FVarsBelow e ety) (he : c.TrExprS e e') (hty : c.TrExprS ety ety')
    (hasty : c.HasType e' ety') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ projected ty', c.TrTyping (.proj st i e) ty projected ty' :=
  (inferProj.WF_all hb he hty hasty rfl).mono fun _ _ _ h => h.1.1

theorem literal_is_primitive (H : n = ``Nat ∨ n = ``Char.ofNat ∨ n = ``String.ofList)  :
    Environment.primitives.contains n := by
  simp [Environment.primitives, NameSet.ofList]
  obtain rfl|rfl|rfl := H <;> simp +decide [NameSet.contains]

theorem infer_literal {c : VContext} (H : c.venv.ContainsLits l) :
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

theorem inferLambda.loop.WF_all {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hlev : ∀ Us P, c.UniverseScope Us P → e₀.levelParamsIn Us = true → FVarsIn P e₀ →
      (c.withMLC m).UniverseScope Us (AllAbove c.vlctx P) ∧ ei.levelParamsIn Us = true ∧
      ∀ ty, ty.levelParamsIn Us = true → (m.mkForall n hn ty).levelParamsIn Us = true)
    (hhit : inferOnly = true → ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P →
      e₀.ParamUniformIn c.env heads As ls → FVarsIn P e₀ →
      (c.withMLC m).ParamUniformScope pfx heads As ls (AllAbove c.vlctx P) ∧
      ei.ParamUniformIn c.env heads As ls ∧
      ∀ ty, ty.ParamUniformIn c.env heads As ls → (m.mkForall n hn ty).ParamUniformIn c.env heads As ls)
    (hpfx : s.ngen.namePrefix = pfx)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLambda.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ((∃ e' ty', c.TrTyping e₀ ty e' ty') ∧ c.LevelsBelow e₀ ty) ∧
      (inferOnly = true → c.ParamUniformBelow pfx e₀ ty) := by
  unfold inferLambda.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    generalize eqF : withLocalDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ((∃ _, _) ∧ _) ∧ _) = P
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
      refine inferLambda.loop.WF_all (Nat.succ_le_succ hn) (by simp [hdrop])
        (by simp [← eqfvs, harr]) ?_ (by simp; rfl) ?_ ?_ ?_ (State.LE.namePrefix_eq hpfx le₂)
        (hr.2.mono fun _ => .tail _) ?_
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
      · intro Us P hs hl hP
        have ⟨k1, k2, k3⟩ := hlev Us P hs hl hP
        have ⟨h1, h2, _⟩ := hbelow _ hs.1 hP
        simp only [Expr.levelParamsIn, Bool.and_eq_true] at k2
        refine ⟨?_, ?_, fun ty hty => k3 _ ?_⟩
        · refine VContext.UniverseScope.cons_same (c := c.withMLC m)
            (fun fv h => mwf'.1.find?_vlam h) k1
            ⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩ fun decl hd => ?_
          erw [mwf'.1.find?_vlam_self] at hd; cases hd
          exact ⟨k2.1, by simp [LocalDecl.value?]⟩
        · rw [eqfvs, ← eq]
          exact Expr.levelParamsIn_instantiate1 k2.2 rfl
        · simp [Expr.levelParamsIn, k2.1, hty]
      · intro hio heads As ls P hs hl hP
        have ⟨k1, k2, k3⟩ := hhit hio heads As ls P hs hl hP
        have ⟨h1, h2, _⟩ := hbelow _ hs.up hP
        have hne := hs.params.ne_of_not_reserves (State.LE.namePrefix_eq hpfx le₁) res
        have ⟨kd, kb⟩ := k2.lam_inv
        refine ⟨?_, ?_, fun ty hty => k3 _ (.forallE kd (hty.abstract1 hne 0))⟩
        · refine VContext.ParamUniformScope.cons_same (c := c.withMLC m) rfl
            (fun fv h => mwf'.1.find?_vlam h) k1
            ⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩ fun decl hd => ?_
          erw [mwf'.1.find?_vlam_self] at hd; cases hd
          exact ⟨kd, by simp [LocalDecl.value?]⟩
        · rw [eqfvs, ← eq]
          exact kb.instantiate1' hs.params.fvars .fvar 0
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.orderedStrong mwf'.1.tr.wf⟩
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
    have hd : FVarsIn (· ∈ (c.withMLC m).vlctx.fvars) (e.instantiateList fvs) := by
      apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine ((inferType.WF_below_of_fvarsIn hd hinf).and_forall (ι := Unit) (H := fun _ => inferOnly = true)
      (R := fun _ ty => (c.withMLC m).ParamUniformTyBelow pfx (e.instantiateList fvs) ty) fun _ hio => ?_).bind
      fun ty _ _ ⟨⟨⟨e', ty', hb, h1, h2, h3⟩, hl⟩, hh⟩ => ?_
    · subst hio; let ⟨_, h⟩ := hinf rfl; exact inferType.WF_paramUniform h hpfx
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, h2', e2⟩ := h2.trExpr c.Ewf.orderedStrong wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2''⟩ := mwf.1.mkLambda_trS c.Ewf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.Ewf h2' (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2'' h3'
    refine mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) (m.noBV ▸ h2'.closed) ▸
      ⟨⟨⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2''⟩, fun Us P hs hl' hP => ?_⟩,
        fun hio heads As ls P hs hl' hP => ?_⟩
    · have ⟨c1, c2, c3⟩ := hbelow _ hP he
      have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
      exact this.mp (fun _ => id) h3'.fvarsIn
    · have ⟨k1, k2, k3⟩ := hlev Us P hs hl' hP
      have ⟨_, c2, _⟩ := hbelow _ hs.1 hP
      exact k3 _ ((BetaReduce.cheapBetaReduce (m.noBV ▸ h2.closed)).levelParamsIn
        (hl Us _ k1 k2 c2))
    · have ⟨k1, k2, k3⟩ := hhit hio heads As ls P hs hl' hP
      have ⟨_, c2, _⟩ := hbelow _ hs.up hP
      exact k3 _ (((hh () hio).1 heads As ls _ k1 k2 c2).betaReduce hs.params.fvars
        (BetaReduce.cheapBetaReduce (m.noBV ▸ h2.closed)))

theorem inferLambda.WF_all
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLambda e inferOnly).WF c s fun ty _ =>
      ((∃ e' ty', c.TrTyping e ty e' ty') ∧ c.LevelsBelow e ty) ∧
      (inferOnly = true → c.ParamUniformBelow s.ngen.namePrefix e ty) := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLambda.loop.WF_all (Nat.zero_le _) rfl rfl rfl rfl ?_ ?_ ?_ rfl h1)
    hinf
  · exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩
  · exact fun Us P hs hl _ => ⟨hs.allAbove, hl, fun _ => id⟩
  · exact fun _ heads As ls P hs hl _ => ⟨hs.allAbove, hl, fun _ => id⟩

theorem inferApp.loop.WF_all {c : VContext} {s : State}
    {ll lm lr : List _}
    (stk : AppStack c.venv c.lparams c.vlctx (.mkAppRevList e lm) e' lr)
    (hbelow : FVarsBelow c.vlctx e fType) (hlev : c.LevelsBelow e fType)
    (hhit : ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P →
      ((e.mkAppRevList lm).mkAppList lr).ParamUniformIn c.env heads As ls →
      FVarsIn P ((e.mkAppRevList lm).mkAppList lr) →
      (fType.ParamUniformIn c.env heads As ls ∧ ∀ a ∈ lm, a.ParamUniformIn c.env heads As ls) ∨
      ((∃ n ∈ heads, e = .const n ls) ∧ Expr.HeadRest heads As.length ls lm.length fType ∧
        fType.ProjsOK (projAvoidsHeads c.env heads)))
    (hpfx : s.ngen.namePrefix = pfx)
    (hfty : c.TrExpr (fType.instantiateList lm) fty') (hety : c.HasType e' fty')
    (hargs : args = ll ++ lm.reverse ++ lr)
    (hj : j = ll.length) (hi : i = ll.length + lm.length) :
    RecM.WF c s (inferApp.loop e₀ ⟨args⟩ fType j i) fun ty _ =>
      ((∃ e₁' ty', c.TrTyping (e.mkAppRevList lm |>.mkAppList lr) ty e₁' ty') ∧
      c.LevelsBelow (e.mkAppRevList lm |>.mkAppList lr) ty) ∧
      c.ParamUniformBelow pfx (e.mkAppRevList lm |>.mkAppList lr) ty := by
  have key : ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P →
      ((e.mkAppRevList lm).mkAppList lr).ParamUniformIn c.env heads As ls →
      FVarsIn P ((e.mkAppRevList lm).mkAppList lr) →
      ((∀ nm d b bi, fType ≠ .forallE nm d b bi) ∨ lr = []) →
      (fType.instantiateList lm).ParamUniformIn c.env heads As ls := by
    intro heads As ls P hs hl hP hnf
    have hp := hs.params.fvars
    have hargsOK : ∀ x ∈ lm, x.ParamUniformIn c.env heads As ls := fun x hx =>
      hl.of_mem_getAppArgsList hp (by
        simp [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_mkAppRevList, hx])
    rcases hhit heads As ls P hs hl hP with ⟨hfT, _⟩ | ⟨⟨n, hn, rfl⟩, hrest, hproj⟩
    · exact hfT.instantiateList hp hargsOK 0
    · have hfn : ((Expr.const n ls).mkAppRevList lm |>.mkAppList lr).getAppFn = .const n ls := by
        rw [Expr.getAppFn_mkAppList, Expr.getAppFn_mkAppRevList]; rfl
      obtain ⟨-, rest, hall, -⟩ := hl.1.getAppFn_const_head_inv hfn hn
      rw [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_mkAppRevList] at hall
      have hconst : (Expr.const n ls).getAppArgsList = [] := rfl
      rw [hconst, List.nil_append] at hall
      have hk : As.length ≤ lm.length := by
        refine Nat.le_of_not_lt fun hlt => ?_
        rcases hnf with hnf | rfl
        · obtain ⟨nm, d, b, bi, h⟩ := hrest.isForall hlt; exact hnf _ _ _ _ h
        · have := congrArg List.length hall; simp at this; omega
      have hB := hrest.body hk
      have hcl : ∀ x ∈ lm, x.looseBVarRange' = 0 := by
        intro x hx
        have hc := (c.mlctx.noBV ▸ stk.tr.closed).getAppArgsList
          (a := x) (by rw [Expr.getAppArgsList_mkAppRevList, hconst]; simpa using hx)
        exact Nat.le_zero.1 hc.looseBVarRange_le
      refine ⟨Expr.ParamUniformBV.instantiateList_params (d := lm.length - As.length) hp rfl
        (by omega) ?_
        (fun x hx => ⟨(hargsOK x hx).1, hcl x hx⟩) hB (by omega : _ = _ + 0),
        hproj.instantiateList (fun x hx => (hargsOK x hx).2) 0⟩
      intro i hi
      have h1 : lm.reverse[i]? = As[i]? := by
        have := congrArg (·[i]?) hall
        rwa [List.getElem?_append_left (by simp; omega),
          List.getElem?_append_left (by omega)] at this
      rw [List.getElem?_reverse (by omega)] at h1
      rw [show lm.length - As.length + (As.length - 1 - i) = lm.length - 1 - i by omega]
      exact h1
  subst i j; rw [inferApp.loop.eq_def]
  simp [hargs, Expr.instantiateList_reverse]
  have henv := c.Ewf; have hΔ := c.Δwf
  cases lr with simp
  | cons a lr =>
    let .app hf' ha' hf ha stk' := stk
    have uf := hf'.uniqU henv hΔ hety
    split
    · rw [Expr.instantiateList_forallE] at hfty
      let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF_all (lm := a::lm) stk' ?_ ?_ ?_ hpfx ?_ (.app hf' ha') (by simp)
        rfl rfl
      · exact fun _ hP he => (hbelow _ hP he).2
      · intro Us P hs hl hP
        have := hlev Us P hs hl hP
        simp only [Expr.levelParamsIn, Bool.and_eq_true] at this
        exact this.2
      · intro heads As ls P hs hl hP
        have haOK : a.ParamUniformIn c.env heads As ls := hl.of_mem_getAppArgsList hs.params.fvars (by
          simp [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_mkAppRevList])
        rcases hhit heads As ls P hs hl hP with ⟨hfT, hlm⟩ | ⟨hhead, hrest, hproj⟩
        · refine .inl ⟨hfT.forallE_inv.2, fun x hx => ?_⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact haOK
          · exact hlm x hx
        · exact .inr ⟨hhead, hrest.forallE, hproj.2⟩
      have ha0 := c.mlctx.noBV ▸ ha.closed
      simp [← Expr.instantiateList_instantiate1_comm ha0.looseBVarRange_zero]
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
    · rename_i hnf
      simp [Nat.add_sub_cancel_left, Expr.instantiateRevList_reverse]
      have ⟨_, hftyS, _⟩ := hfty
      refine ((ensureForallCore.WF_below hfty).and (ensureForallCore.WF_paramUniform hftyS hpfx)).bind
        fun _ _ le ⟨⟨⟨hb, ⟨_, h2, h3⟩, eq⟩, hfl⟩, hfh⟩ => ?_
      obtain ⟨name, ty, body, bi, rfl⟩ := eq; simp [Expr.bindingBody!]
      let .forallE _ _ hty hbody := h2
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF_all (ll := ll ++ lm.reverse) (lm := [a]) stk' ?_ ?_ ?_
        (State.LE.namePrefix_eq hpfx le) ?_ (.app hf' ha') (by simp) (by simp) (by simp)
      · intro _ hP he
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
        exact (hb _ hP <| (hbelow _ hP he).instantiateList hlm).2
      · intro Us P hs hl hP
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 hP
        have ⟨hle, hlml⟩ := Expr.levelParamsIn_mkAppRevList_iff.1 hl
        have := hfl Us P hs (Expr.levelParamsIn_instantiateList (hlev Us P hs hle he) hlml)
          ((hbelow _ hs.1 he).instantiateList hlm)
        simp only [Expr.levelParamsIn, Bool.and_eq_true] at this
        exact this.2
      · intro heads As ls P hs hl hP
        have haOK : a.ParamUniformIn c.env heads As ls := hl.of_mem_getAppArgsList hs.params.fvars (by
          simp [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_mkAppRevList])
        have hP' : FVarsIn P (e.mkAppRevList lm) := by
          have := FVarsIn.mkAppList.1 hP; exact this.1.1
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 hP'
        have hinst := key heads As ls P hs hl hP (.inl fun nm d b bi h => hnf nm d b bi h)
        have := hfh heads As ls P hs hinst ((hbelow _ hs.up he).instantiateList hlm)
        refine .inl ⟨this.forallE_inv.2, fun x hx => ?_⟩
        rw [List.mem_singleton.1 hx]; exact haOK
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
  | nil =>
    rw [← List.length_reverse, List.take_length, Expr.instantiateRevList_reverse]
    have ⟨_, hfty, h2⟩ := hfty
    refine .pure ⟨⟨⟨_, _, fun _ hP he => ?_, stk.tr, hfty, hety.defeqU_r henv hΔ h2.symm⟩,
      fun Us P hs hl hP => ?_⟩, fun heads As ls P hs hl hP => key heads As ls P hs hl hP (.inr rfl)⟩
    · have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
      exact (hbelow _ hP he).instantiateList hlm
    · have ⟨he, hlm⟩ := FVarsIn.appRevList.1 hP
      have ⟨hle, hlml⟩ := Expr.levelParamsIn_mkAppRevList_iff.1 hl
      exact Expr.levelParamsIn_instantiateList (hlev Us P hs hle he) hlml

theorem inferApp.WF_all {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (inferApp e) fun ty _ => ((∃ ty', c.TrTyping e ty e' ty') ∧ c.LevelsBelow e ty) ∧
      c.ParamUniformBelow s.ngen.namePrefix e ty := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, he'⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
  refine ((inferType.WF_below he'.tr).and (inferType.WF_paramUniform he'.tr rfl)).bind
    fun ty _ le ⟨⟨⟨ty', hb, _, hty', ety⟩, hl⟩, hh⟩ => ?_
  have henv := c.Ewf; have hΔ := c.Δwf
  refine (inferApp.loop.WF_all (ll := []) (lm := []) he' hb hl ?_ (State.LE.namePrefix_eq rfl le)
      (hty'.trExpr henv hΔ) ety rfl rfl rfl).le
    fun _ _ _ ⟨⟨⟨_, _, hb, h1, h2, h3⟩, hl⟩, hh⟩ => ?_
  · intro heads As ls P hs hl hP
    simp only [Expr.mkAppRevList] at hl hP
    rw [e.mkAppList_getAppArgsList] at hl hP
    by_cases hhd : ∃ n us, e.getAppFn = .const n us ∧ n ∈ heads
    · obtain ⟨n, us, hfn, hn⟩ := hhd
      obtain ⟨rfl, -⟩ := hl.1.getAppFn_const_head_inv hfn hn
      have := hh.2 heads As _ P hs n hn hfn
      obtain ⟨⟨body, H1, H2⟩, H3⟩ := this
      exact .inr ⟨⟨n, hn, hfn⟩, .start H1 H2, H3⟩
    · exact .inl ⟨hh.1 heads As ls P hs
        (hl.getAppFn_of_not_head fun c us h hc => hhd ⟨c, us, h, hc⟩) hP.appFn, by simp⟩
  · have := (e.mkAppList_getAppArgsList ▸ h1).uniq henv (.refl henv hΔ) he
    exact ⟨⟨⟨_, e.mkAppList_getAppArgsList ▸ hb, he, h2, h3.defeqU_l henv hΔ this⟩,
      e.mkAppList_getAppArgsList ▸ hl⟩, e.mkAppList_getAppArgsList ▸ hh⟩

theorem inferForall.loop.WF_all {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkForall n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hus : us.toList.reverse.Forall₂ (VLevel.ofLevel c.lparams · = some ·) us')
    (hΔ : m.vlctx.SortList c.venv c.lparams.length us')
    (hlen : us'.length = n)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei)
    (hlev : ∀ Us P, c.UniverseScope Us P → e₀.levelParamsIn Us = true → FVarsIn P e₀ →
      (c.withMLC m).UniverseScope Us (AllAbove c.vlctx P) ∧ ei.levelParamsIn Us = true ∧
      ∀ u ∈ us.toList, u.paramsIn Us = true)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferForall.loop inferOnly arr us e).WF (c.withMLC m) s fun ty _ =>
      (∃ e' u, c.TrTyping e₀ ty e' (.sort u)) ∧ c.LevelsBelow e₀ ty := by
  unfold inferForall.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    rw [Expr.instantiateList_forallE] at hei; subst ei
    have hd : FVarsIn (· ∈ m.vlctx.fvars) (dom.instantiateList fvs) := by
      apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine (inferType.WF_below_of_fvarsIn hd ?_).bind
      fun uv _ le ⟨⟨dom', uv', hbu, h1, h2, h3⟩, hlu⟩ => ?_
    · intro h; let ⟨_, .forallE _ _ h _⟩ := hinf h; exact ⟨_, h⟩
    refine (ensureSortCore.WF_below h2).bind_le le fun _ _ le ⟨⟨h4, h5, hbs⟩, hls⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort h4, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' le fun a mwf' s' le₂ res => ?_
    have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
    refine inferForall.loop.WF_all (Nat.succ_le_succ hn) (by simp [hdrop])
      (by simp [eqfvs, harr]) ?_ (by simp [eqfvs]; rfl) (hr.2.mono fun _ => .tail _)
      (by simpa using ⟨h4, hus⟩) (.cons hΔ domty) (by simp [hlen]) ?_ ?_ ?_
    · simp [he₀, ← eq]; congr 2
      refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
      · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
      · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
    · intro P hP he
      have ⟨h1, h2⟩ := hbelow _ hP he
      refine ⟨⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩, ?_⟩
      simp only [← eq]
      refine h2.2.instantiate1 fun h => ?_
      exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
    · intro Us P hs hl hP
      have ⟨k1, k2, k3⟩ := hlev Us P hs hl hP
      have ⟨h1', h2'⟩ := hbelow _ hs.1 hP
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at k2
      refine ⟨?_, ?_, ?_⟩
      · refine VContext.UniverseScope.cons_same (c := c.withMLC m)
          (fun fv h => mwf'.1.find?_vlam h) k1
          ⟨h1', fun _ => (fvarsIn_iff.1 h2'.1).1⟩ fun decl hd => ?_
        erw [mwf'.1.find?_vlam_self] at hd; cases hd
        exact ⟨k2.1, by simp [LocalDecl.value?]⟩
      · simp only [← eq]
        exact Expr.levelParamsIn_instantiate1 k2.2 rfl
      · have hu := hls Us _ k1 (hlu Us _ k1 k2.1 h2'.1) (hbu _ k1.1 h2'.1)
        simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        rintro u (hu' | rfl)
        · exact k3 u hu'
        · simpa [Expr.sortLevel!, Expr.levelParamsIn] using hu
    · intro h; let ⟨_, .forallE (body' := body') _ _ hdom₁ hbody₁⟩ := hinf h
      refine have hΔ := .refl c.Ewf mwf.1.tr.wf; have H := hdom₁.uniq c.Ewf hΔ h1; ?_
      have H := H.of_r c.Ewf mwf.1.tr.wf.toCtx domty
      have ⟨_, hbody₂⟩ := hbody₁.defeqDFC c.Ewf <| .cons hΔ (ofv := none) nofun (.vlam H)
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.Ewf.orderedStrong mwf'.1.tr.wf⟩
  · subst ei
    have hd : FVarsIn (· ∈ m.vlctx.fvars) (e.instantiateList fvs) := by
      apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine (inferType.WF_below_of_fvarsIn hd hinf).bind
      fun ty _ _ ⟨⟨e', ty', hbu, h1, h2, h3⟩, hlu⟩ => ?_
    refine (ensureSortCore.WF_below h2).bind fun _ _ le₂ ⟨⟨h4, h5, _⟩, hls⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort (u' := u') h4, h5⟩ := h5
    obtain ⟨us, rfl⟩ : ∃ l, ⟨List.reverse l⟩ = us := ⟨us.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at hus hlev ⊢
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    let ⟨h1', h2'⟩ := mwf.1.mkForall_trS c.Ewf h1 ⟨_, h3⟩ n hn
    have ⟨_, h3', h4'⟩ := mkForall_hasType hus hΔ h4 h3 n hn (hus.length_eq.trans hlen)
    simp [hdrop] at h1' h2' h4'
    refine have h := .sort h3'; .pure ⟨⟨_, _, fun _ _ _ => h.fvarsIn, he₀ ▸ h1', h, h4'⟩, ?_⟩
    intro Us P hs hl hP
    have ⟨k1, k2, k3⟩ := hlev Us P hs hl hP
    have ⟨_, h2'⟩ := hbelow _ hs.1 hP
    have hu := hls Us _ k1 (hlu Us _ k1 k2 h2') (hbu _ k1.1 h2')
    simp only [Expr.levelParamsIn] at hu ⊢
    exact Level.paramsIn_foldl_mkIMax k3 hu

theorem inferForall.WF_all
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferForall e inferOnly).WF c s fun ty _ =>
      (∃ e' u, c.TrTyping e ty e' (.sort u)) ∧ c.LevelsBelow e ty := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferForall.loop.WF_all (Nat.zero_le _) rfl rfl rfl rfl hr .nil .nil rfl
    ?_ ?_) hinf
  · exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h⟩
  · exact fun Us P hs hl _ => ⟨hs.allAbove, hl, by simp⟩
theorem inferLet.loop.WF_all {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length) (nds hnds)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLet n hn nds hnds ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hlev : ∀ Us P, c.UniverseScope Us P → e₀.levelParamsIn Us = true → FVarsIn P e₀ →
      (c.withMLC m).UniverseScope Us (AllAbove c.vlctx P) ∧ ei.levelParamsIn Us = true ∧
      ∀ ty, ty.levelParamsIn Us = true → (m.mkForall n hn ty).levelParamsIn Us = true)
    (hhit : inferOnly = true → ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P →
      e₀.ParamUniformIn c.env heads As ls → FVarsIn P e₀ →
      (c.withMLC m).ParamUniformScope pfx heads As ls (AllAbove c.vlctx P) ∧
      ei.ParamUniformIn c.env heads As ls ∧
      ∀ ty, ty.ParamUniformIn c.env heads As ls → (m.mkForall n hn ty).ParamUniformIn c.env heads As ls)
    (hpfx : s.ngen.namePrefix = pfx)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLet.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ((∃ e' ty', c.TrTyping e₀ ty e' ty') ∧ c.LevelsBelow e₀ ty) ∧
      (inferOnly = true → c.ParamUniformBelow pfx e₀ ty) := by
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  unfold inferLet.loop
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom val body nd
    generalize eqF : withLetDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ((∃ _, _) ∧ _) ∧ _) = P
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
      refine inferLet.loop.WF_all (Nat.succ_le_succ hn) (some nd :: nds)
        (by simp [hnds]) (by simp [hdrop]) (by simp [← eqfvs, harr])
        ?_ (by simp; rfl) ?_ ?_ ?_ (State.LE.namePrefix_eq hpfx le₂)
        (hr.2.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp [MLCtx.mkLetArg]; congr 2
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
      · intro Us P hs hl hP
        have ⟨k1, k2, k3⟩ := hlev Us P hs hl hP
        have ⟨h1, h2, _⟩ := hbelow _ hs.1 hP
        simp only [Expr.levelParamsIn, Bool.and_eq_true] at k2
        refine ⟨?_, ?_, fun ty hty => k3 _ ?_⟩
        · refine VContext.UniverseScope.cons_same (c := c.withMLC m)
            (fun fv h => mwf'.1.find?_vlet h) k1
            ⟨h1, fun _ => ?_⟩ fun decl hd => ?_
          · simp [or_imp, forall_and]
            exact ⟨(fvarsIn_iff.1 h2.1).1, (fvarsIn_iff.1 h2.2.1).1⟩
          erw [mwf'.1.find?_vlet_self] at hd; cases hd
          exact ⟨k2.1.1, by simp [LocalDecl.value?, k2.1.2]⟩
        · rw [eqfvs, ← eq]
          exact Expr.levelParamsIn_instantiate1 k2.2 rfl
        · simp; split
          · simp [Expr.levelParamsIn, k2.1.1, k2.1.2, hty]
          · simp [hty]
      · intro hio heads As ls P hs hl hP
        have ⟨k1, k2, k3⟩ := hhit hio heads As ls P hs hl hP
        have ⟨h1, h2, _⟩ := hbelow _ hs.up hP
        have hne := hs.params.ne_of_not_reserves (State.LE.namePrefix_eq hpfx le₁) res
        have ⟨kd, kv, kb⟩ := k2.letE_inv
        refine ⟨?_, ?_, fun ty hty => k3 _ ?_⟩
        · refine VContext.ParamUniformScope.cons_same (c := c.withMLC m) rfl
            (fun fv h => mwf'.1.find?_vlet h) k1
            ⟨h1, fun _ => ?_⟩ fun decl hd => ?_
          · simp [or_imp, forall_and]
            exact ⟨(fvarsIn_iff.1 h2.1).1, (fvarsIn_iff.1 h2.2.1).1⟩
          erw [mwf'.1.find?_vlet_self] at hd; cases hd
          exact ⟨kd, fun v hv => by rw [LocalDecl.value?_ldecl_true] at hv; cases hv; exact kv⟩
        · rw [eqfvs, ← eq]
          exact kb.instantiate1' hs.params.fvars .fvar 0
        · simp; split
          · exact .letE kd kv (hty.abstract1 hne 0)
          · exact (hty.abstract1 hne 0).lowerLooseBVars' hs.params.fvars 1 1
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.orderedStrong mwf'.1.tr.wf⟩
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
  · subst ei
    have hd : FVarsIn (· ∈ (c.withMLC m).vlctx.fvars) (e.instantiateList fvs) := by
      apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine ((inferType.WF_below_of_fvarsIn hd hinf).and_forall (ι := Unit) (H := fun _ => inferOnly = true)
      (R := fun _ ty => (c.withMLC m).ParamUniformTyBelow pfx (e.instantiateList fvs) ty)
      fun _ hio => ?_).bind fun ty _ _ ⟨⟨⟨e', ty', hb, h1, h2, h3⟩, hl⟩, hh⟩ => ?_
    · subst hio; let ⟨_, h⟩ := hinf rfl; exact inferType.WF_paramUniform h hpfx
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, hty, e2⟩ := h2.trExpr c.Ewf.orderedStrong wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLet_trS c.Ewf h1 h3 n hn nds hnds
    have h3' := (mwf.1.mkForall_trS c.Ewf hty (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    erw [mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) (m.noBV ▸ hty.closed)]
    refine ⟨⟨⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2'⟩, fun Us P hs hl' hP => ?_⟩,
      fun hio heads As ls P hs hl' hP => ?_⟩
    · have ⟨c1, c2, c3⟩ := hbelow _ hP he
      have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
      exact this.mp (fun _ => id) h3'.fvarsIn
    · have ⟨k1, k2, k3⟩ := hlev Us P hs hl' hP
      have ⟨_, c2, _⟩ := hbelow _ hs.1 hP
      exact k3 _ ((BetaReduce.cheapBetaReduce (m.noBV ▸ h2.closed)).levelParamsIn
        (hl Us _ k1 k2 c2))
    · have ⟨k1, k2, k3⟩ := hhit hio heads As ls P hs hl' hP
      have ⟨_, c2, _⟩ := hbelow _ hs.up hP
      exact k3 _ (((hh () hio).1 heads As ls _ k1 k2 c2).betaReduce hs.params.fvars
        (BetaReduce.cheapBetaReduce (m.noBV ▸ h2.closed)))
termination_by e

theorem inferLet.WF_all
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLet e inferOnly).WF c s fun ty _ =>
      ((∃ e' ty', c.TrTyping e ty e' ty') ∧ c.LevelsBelow e ty) ∧
      (inferOnly = true → c.ParamUniformBelow s.ngen.namePrefix e ty) := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLet.loop.WF_all (Nat.zero_le _) [] rfl rfl rfl rfl rfl ?_ ?_ ?_
    rfl hr) hinf
  · exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩
  · exact fun Us P hs hl _ => ⟨hs.allAbove, hl, fun _ => id⟩
  · exact fun _ heads As ls P hs hl _ => ⟨hs.allAbove, hl, fun _ => id⟩
theorem RecM.Res.withLocalDecl {f : Expr → RecM α} {Q : α → Prop}
    (H : ∀ x, (f x).Res Q) : (withLocalDecl name bi ty f).Res Q := by
  intro m ctx st a st' e
  change (withFreshId _ : M α) ctx st = _ at e
  rw [withFreshId_eq] at e
  exact H _ m _ _ _ _ e

theorem inferForall.loop.Res_sort :
    (inferForall.loop inferOnly fvars us e).Res fun ty => ∃ u, ty = .sort u := by
  induction e generalizing fvars us with
  | forallE name dom body bi _ ih =>
    unfold inferForall.loop
    exact RecM.Res.bind fun _ => RecM.Res.bind fun _ => RecM.Res.withLocalDecl fun _ => ih
  | _ =>
    unfold inferForall.loop
    exact RecM.Res.bind fun _ => RecM.Res.bind fun _ => .pure ⟨_, rfl⟩

theorem inferForall.Res_sort :
    (inferForall e inferOnly).Res fun ty => ∃ u, ty = .sort u := inferForall.loop.Res_sort

theorem inferConstant.WF_eq {c : VContext} :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      ∃ ci, c.env.find? name = some ci ∧ ty = ci.instantiateTypeLevelParams ls := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq1 => ?_
  have hret {β} {x : Except Exception β} :
      ((fun _ => ci.instantiateTypeLevelParams ls) <$> x).WF fun ty =>
        ∃ ci', c.env.find? name = some ci' ∧ ty = ci'.instantiateTypeLevelParams ls :=
    Except.WF.map (h1 := fun _ _ => trivial) fun _ _ => ⟨ci, eq1, rfl⟩
  split <;> [skip; exact .throw]
  split
  · split <;> [exact .throw; skip]
    split <;> [skip; exact hret]
    split <;> [exact .throw; exact hret]
  · exact .pure ⟨ci, eq1, rfl⟩

theorem inferFVar.WF_paramUniform {c : VContext} :
    (inferFVar c.toContext name).WF fun ty => c.ParamUniformTyBelow pfx (.fvar name) ty := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  exact ⟨fun heads As ls P hs _ hP => (hs.decls _ _ hP h).1, nofun⟩

theorem _root_.Lean.Literal.levelParamsIn_type {l : Literal} :
    l.type.levelParamsIn Us = true := by
  cases l <;> rfl

theorem inferType'.WF_all
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ =>
      ((∃ e' ty', c.TrTyping e ty e' ty') ∧ c.LevelsBelow e ty) ∧
      (inferOnly = true → c.ParamUniformTyBelow s.ngen.namePrefix e ty) := by
  generalize hpfx : s.ngen.namePrefix = pfx
  unfold inferType'; lift_lets; intro F F1
  split <;> [exact .throw; refine .get <| .get ?_]
  split
  · rename_i h; refine .stateWF fun wf => .pure ?_
    generalize hic : cond .. = ic at h
    have : ic.WF c s ∧ LevelsCache.WF c ic ∧ (inferOnly = true → ParamUniformTyCache.WF c pfx ic) := by
      subst ic; cases inferOnly <;>
        [exact ⟨wf.inferTypeC_wf, wf.inferTypeC_levels, nofun⟩;
         exact ⟨wf.inferTypeI_wf, wf.inferTypeI_levels, fun _ => hpfx ▸ wf.inferTypeI_paramUniform⟩]
    exact ⟨⟨(this.1 h).2.2.2.2 h1, this.2.1 h h1⟩, fun hio => this.2.2 hio h h1⟩
  generalize hP : (fun _ (_ : State) => _) = P
  have hF {ty e' ty' s} (hs : s.ngen.namePrefix = pfx) (H : c.TrTyping e ty e' ty')
      (HL : c.LevelsBelow e ty) (HH : inferOnly = true → c.ParamUniformTyBelow pfx e ty) :
      (F ty).WF c s P := by
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : InferCache.WF c s ic) : InferCache.WF c s (ic.insert e ty) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv H eq BEq.rfl) (.eqv eq ?_) ?_
      · exact H.2.1.fvarsIn.mono wf.ngen_wf
      · exact H.2.2.1.fvarsIn.mono wf.ngen_wf
    subst P; revert s'; cases inferOnly <;>
      (dsimp -zeta; intro s'; refine ⟨.rfl, ?_, ⟨⟨_, _, H⟩, HL⟩, hs ▸ HH⟩)
    · exact { wf with
        inferTypeC_wf := hic wf.inferTypeC_wf
        inferTypeC_levels := wf.inferTypeC_levels.insert HL }
    · have HH' := HH rfl; rw [← hs] at HH'
      exact { wf with
        inferTypeI_wf := hic wf.inferTypeI_wf
        inferTypeI_levels := wf.inferTypeI_levels.insert HL
        inferTypeI_paramUniform := wf.inferTypeI_paramUniform.insert HH' }
  have hlit {l} : c.LevelsBelow (.lit l) l.type := fun _ _ _ _ _ => Literal.levelParamsIn_type
  have hlitH {l : Literal} (hl : c.venv.ContainsLits l) :
      c.ParamUniformTyBelow pfx (.lit l) (mkConst l.typeName) := by
    refine ⟨fun heads As ls P hs _ _ => ?_, nofun⟩
    cases l with
    | natVal => exact .const (hs.env.prim (by simp [Literal.typeName, checkerPrimNames]))
    | strVal =>
      exact .const (hs.env.str (c.strLitsDeclared hl) (by simp [Literal.typeName, strLitNames]))
  have hle {s'} (le : s ≤ s') : s'.ngen.namePrefix = pfx := State.LE.namePrefix_eq hpfx le
  split
  · extract_lets G1; split <;> [split; skip]
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ le h => ?_
      have ⟨_, h, _⟩ := c.trenv.find? h <|
        (c.safePrimitives h (literal_is_primitive (.inl rfl))).1 ▸ DefinitionSafety.le_safe
      exact hF (hle le) (infer_literal ⟨_, h⟩) hlit fun _ => hlitH ⟨_, h⟩
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ le h1 => ?_
      refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ le' h2 => ?_
      have ⟨_, h1, _⟩ := c.trenv.find? h1 <|
        (c.safePrimitives h1 (literal_is_primitive (.inr (.inl rfl)))).1 ▸ DefinitionSafety.le_safe
      have ⟨_, h2, _⟩ := c.trenv.find? h2 <|
        (c.safePrimitives h2 (literal_is_primitive (.inr (.inr rfl)))).1 ▸ DefinitionSafety.le_safe
      exact hF (hle (le.trans le')) (infer_literal ⟨⟨_, h1⟩, ⟨_, h2⟩⟩) hlit
        fun _ => hlitH ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    · rename_i h; have ⟨_, h⟩ := hinf (by simpa using h)
      have := h.lit_has_type
      simp [G1]; exact hF hpfx (infer_literal this) hlit fun _ => by
        rw [← Literal.mkConst_typeName]; exact hlitH this
  · refine (inferType'.WF_all (by exact h1) ?_).bind
      fun _ _ le ⟨⟨⟨_, _, hb, h1, h⟩, hl⟩, hh⟩ => ?_
    · exact fun h => let ⟨_, .mdata h⟩ := hinf h; ⟨_, h⟩
    refine hF (hle le) ⟨hb, .mdata h1, h⟩ hl fun hio => ⟨?_, nofun⟩
    have := (hh hio).1; rw [hpfx] at this
    exact fun heads As ls P hs hl hP => this heads As ls P hs hl.mdata_inv hP
  · refine (inferType'.WF_all (by exact h1) ?_).bind
      fun _ _ le ⟨⟨⟨_, _, hb, h1, h2, h3⟩, hl⟩, hh⟩ => ?_
    · exact fun h => let ⟨_, .proj h ..⟩ := hinf h; ⟨_, h⟩
    exact (inferProj.WF_all hb h1 h2 h3 (hle le)).bind fun ty _ le' ⟨⟨⟨_, _, h⟩, hl'⟩, hh'⟩ =>
      hF (hle (le.trans le')) h (fun Us P hs he hP => hl' Us P hs he (hl Us P hs he hP) hP)
        fun hio => ⟨fun heads As ls P hs he hP => by
          have := (hh hio).1; rw [hpfx] at this
          exact hh' heads As ls P hs he (this heads As ls P hs he.proj_inv.2 hP) hP, nofun⟩
  · exact .readThe <| (M.WF.liftExcept (x := inferFVar _ _)
      (Q := fun ty => ((∃ e' ty', c.TrTyping _ ty e' ty') ∧ c.LevelsBelow _ ty) ∧
        c.ParamUniformTyBelow pfx _ ty)
      fun a h => ⟨⟨inferFVar.WF a h, inferFVar.WF_levels a h⟩, inferFVar.WF_paramUniform a h⟩).lift.bind
      fun _ _ le ⟨⟨⟨_, _, h⟩, hl⟩, hh⟩ => hF (hle le) h hl fun _ => hh
  · exact .throw
  · rename_i h _; simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at h
  · have hl {u : Level} : c.LevelsBelow (.sort u) (.sort u.succ) := fun _ _ _ h _ => by
      simpa [Expr.levelParamsIn, Level.paramsIn] using h
    have hh {u : Level} : c.ParamUniformTyBelow pfx (.sort u) (.sort u.succ) :=
      ⟨fun _ _ _ _ _ _ _ => .sort, nofun⟩
    split <;> rename_i h
    · refine .readThe <| (M.WF.liftExcept (checkLevel.WF h1)).lift.bind fun _ _ le ⟨_, h⟩ => ?_
      exact hF (hle le) (infer_sort h) hl fun _ => hh
    · let ⟨_, .sort h⟩ := hinf (by simpa using h)
      exact hF hpfx (infer_sort h) hl fun _ => hh
  · rename_i n ls' _ _
    refine .readThe <| (M.WF.liftExcept (x := inferConstant _ _ _ _)
      (Q := fun ty => ((∃ e' ty', c.TrTyping _ ty e' ty') ∧ ∀ Us, (∀ l ∈ ls', l.paramsIn Us = true) →
          ty.levelParamsIn Us = true) ∧
        ∃ ci, c.env.find? n = some ci ∧ ty = ci.instantiateTypeLevelParams ls')
      fun a h => ⟨inferConstant.WF_all h1 hinf a h, inferConstant.WF_eq a h⟩).lift.bind
      fun _ _ le ⟨⟨⟨_, _, h⟩, hl⟩, ci, hci, hty⟩ => ?_
    subst hty
    refine hF (hle le) h (fun Us _ _ h _ => hl Us (by simpa [Expr.levelParamsIn] using h))
      fun _ => ⟨fun heads As ls P hs hl _ => ?_, fun heads As ls P hs n' hn he => ?_⟩
    · rcases hl.1.const_inv with hn | ⟨hn, rfl, hAs⟩
      · exact .instantiateLevelParams_of_avoids (hs.env.type_avoids hci hn)
          (hs.env.type_projs hci)
      · obtain ⟨body, H1, H2⟩ := hs.env.head_type hci hn
        rw [hAs] at H1 H2; cases H1
        exact ⟨hAs ▸ H2.zero_params, (hs.env.type_projs hci).instantiateLevelParams⟩
    · cases he
      exact ⟨hs.env.head_type hci hn, (hs.env.type_projs hci).instantiateLevelParams⟩
  · exact (inferLambda.WF_all h1 hinf).bind fun _ _ le ⟨⟨⟨_, _, h⟩, hl⟩, hh⟩ =>
      hF (hle le) h hl fun hio => ⟨hpfx ▸ hh hio, nofun⟩
  · refine ((inferForall.WF_all h1 hinf).and_post (inferForall.Res_sort).post).bind
      fun _ _ le ⟨⟨⟨_, _, h⟩, hl⟩, u, hu⟩ => ?_
    subst hu
    exact hF (hle le) h hl fun _ => ⟨fun _ _ _ _ _ _ _ => .sort, nofun⟩
  · split <;> rename_i h
    · let ⟨_, h⟩ := hinf h
      exact (inferApp.WF_all h).bind fun _ _ le ⟨⟨⟨_, h⟩, hl⟩, hh⟩ =>
        hF (hle le) h hl fun _ => ⟨hpfx ▸ hh, nofun⟩
    refine (inferType'.WF_all h1.1 ?_).bind
      fun _ _ le₁ ⟨⟨⟨_, _, hfb, hf1, hf2, hf3⟩, hfl⟩, _⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ h _⟩ := hinf h; ⟨_, h⟩
    refine .stateWF fun wf => ?_
    refine (ensureForallCore.WF_below (hf2.trExpr c.Ewf c.Δwf)).bind fun _ _ le₂ ⟨H, Hl⟩ => ?_
    obtain ⟨hb, h2, name, dType, body, bi, rfl⟩ := H
    let ⟨_, .forallE (ty' := dType') hl1 hl2 hl3 hl4, hl5⟩ := h2
    extract_lets _ G1
    refine (inferType'.WF_all h1.2 ?_).bind
      fun aType _ le₃ ⟨⟨⟨_, aType', hab, ha1, ha2, ha3⟩, _⟩, _⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ _ h⟩ := hinf h; ⟨_, h⟩
    have hs₃ := hle (le₁.trans le₂ |>.trans le₃)
    extract_lets G2
    suffices ∀ {s b} (H : b = true → c.IsDefEqU dType' aType'), s.ngen.namePrefix = pfx →
        RecM.WF c s (G2 b) P by
      split
      · refine .bind ?_ (Q := fun b s => (b = true → c.IsDefEqU dType' aType') ∧
          s.ngen.namePrefix = pfx) fun b _ _ h => this h.1 h.2
        intro _ mwf wf _ _ eq
        let c' := { c with eagerReduce := true }
        have ⟨_, h1, h2, h3, h4⟩ := isDefEq.WF (c := c') hl3 ha2 _ mwf { wf with } _ _ eq
        exact ⟨_, h1, h2, { h3 with }, h4, State.LE.namePrefix_eq hs₃ h2⟩
      · exact (isDefEq.WF hl3 ha2).bind fun b _ le h => this h (State.LE.namePrefix_eq hs₃ le)
    subst G2; dsimp; rintro s ⟨⟩ H hs
    · exact .getEnv <| .getLCtx .throw
    simp [G1, Expr.bindingBody!]
    have hf3 := hf3.defeqU_r c.Ewf c.Δwf hl5.symm
    have ha3 := ha3.defeqU_r c.Ewf c.Δwf (H rfl).symm
    subst hP; refine hF hs ⟨?_, .app hf3 ha3 hf1 ha1, hl4.inst c.Ewf ha3 ha1, .app hf3 ha3⟩ ?_
      fun hio => absurd hio h
    · exact fun _ hP he => (hfb.trans hb _ hP he.1).2.instantiate1 he.2
    · intro Us P hs hl hP
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at hl
      have := Hl Us P hs (hfl Us P hs hl.1 hP.1) (hfb P hs.1 hP.1)
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at this
      exact Expr.levelParamsIn_instantiate1 this.2 hl.2
  · exact (inferLet.WF_all h1 hinf).bind fun _ _ le ⟨⟨⟨_, _, h⟩, hl⟩, hh⟩ =>
      hF (hle le) h hl fun hio => ⟨hpfx ▸ hh hio, nofun⟩

theorem inferType'.WF_paramUniform
    (he : c.TrExprS e e') :
    (inferType' e true).WF c s fun ty _ => c.ParamUniformTyBelow s.ngen.namePrefix e ty :=
  (inferType'.WF_all he.fvarsIn fun _ => ⟨_, he⟩).mono fun _ _ _ h => h.2 rfl

theorem inferType'.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  (inferType'.WF_all h1 hinf).mono fun _ _ _ h => h.1.1

theorem inferType'.WF_levels
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ => c.LevelsBelow e ty :=
  (inferType'.WF_all h1 hinf).mono fun _ _ _ h => h.1.2
