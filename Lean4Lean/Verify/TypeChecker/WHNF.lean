import Lean4Lean.Verify.TypeChecker.Reduce

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

/-- The ι step of recursor reduction, refined against the ι rules registered for the recursor:
on a redex whose major premise is the saturated constructor application `ctorName cls cargs`,
the reduct `inductiveReduceRecCore` builds translates to the redex's own translation.

The translated redex matches the rule's ι pattern, whose reduct `SimplePattern.iotaRHS` is the
rule's template applied to the same two slices the kernel takes — the recursor's parameters,
motives and minor premises, and the constructor's fields — with the arguments after the major
re-applied on both sides. Saturation of the major (`hsat`) is what makes the two slicings
agree, the kernel taking the *last* `rule.nfields` arguments of the major and the pattern the
ones past the constructor's parameters; it is a consequence of the redex being well-typed, and
is left to the caller. -/
theorem inductiveReduceRecCore.WF {c : VContext} {recName ctorName : Name}
    {rval : RecursorVal} {rule : RecursorRule} {cval : ConstructorVal}
    {ls cls : List Level} {as cargs : List Expr} {e' : VExpr} {e₁ : Expr}
    (hrec : c.env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == ctorName) = some rule)
    (hctor : c.env.find? ctorName = some (.ctorInfo cval))
    (hsat : cargs.length = cval.numParams + rule.nfields)
    (hmaj : as[rval.getMajorIdx]? = some (Expr.mkAppList (.const ctorName cls) cargs))
    (he : c.TrExprS (Expr.mkAppList (.const recName ls) as) e')
    (heq : inductiveReduceRecCore rval ls as.toArray
      (Expr.mkAppList (.const ctorName cls) cargs) = some e₁) :
    c.FVarsBelow (Expr.mkAppList (.const recName ls) as) e₁ ∧ c.TrExpr e₁ e' := by
  have hKM : rval.getFirstIndexIdx + rval.numIndices = rval.getMajorIdx := rfl
  obtain ⟨hM, hasM⟩ := List.getElem?_eq_some_iff.1 hmaj
  -- the recursor's arguments split into the rule's prefix, the indices, the major and the rest
  obtain ⟨p1, idx, post, hp1len, hidxlen, rfl⟩ :
      ∃ p1 idx post, p1.length = rval.getFirstIndexIdx ∧ idx.length = rval.numIndices ∧
        as = p1 ++ idx ++ (Expr.mkAppList (.const ctorName cls) cargs) :: post := by
    refine ⟨as.take rval.getFirstIndexIdx, (as.take rval.getMajorIdx).drop rval.getFirstIndexIdx,
      as.drop (rval.getMajorIdx + 1), by simp; omega, by simp; omega, ?_⟩
    have h3 : as.take rval.getFirstIndexIdx ++
        (as.take rval.getMajorIdx).drop rval.getFirstIndexIdx = as.take rval.getMajorIdx := by
      conv => rhs; rw [← List.take_append_drop rval.getFirstIndexIdx (as.take rval.getMajorIdx)]
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [h3, ← hasM, ← List.drop_eq_getElem_cons hM, List.take_append_drop]
  obtain ⟨cpar, cfld, hcparlen, hcfldlen, rfl⟩ :
      ∃ cpar cfld, cpar.length = cval.numParams ∧ cfld.length = rule.nfields ∧
        cargs = cpar ++ cfld := by
    refine ⟨cargs.take cval.numParams, cargs.drop cval.numParams, by simp; omega, by simp; omega,
      (List.take_append_drop ..).symm⟩
  -- the kernel's reduct: the rule's template applied to the prefix, the fields and the rest
  have hargs : (Expr.mkAppList (.const ctorName cls) (cpar ++ cfld)).getAppArgs
      = (cpar ++ cfld).toArray := by
    simp [Expr.getAppArgs_eq, Expr.getAppArgsList_mkAppList]; rfl
  have hgrr : getRecRuleFor rval (Expr.mkAppList (.const ctorName cls) (cpar ++ cfld))
      = some rule := by simp [getRecRuleFor, Expr.getAppFn, hrule]
  rw [inductiveReduceRecCore, hgrr] at heq
  simp only [hargs, List.size_toArray] at heq
  split at heq
  · rename_i h; simp at h; omega
  split at heq
  · exact absurd heq nofun
  rename_i hlp
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlp
  have hr1 : mkAppRange (rule.rhs.instantiateLevelParams rval.levelParams ls) 0
      rval.getFirstIndexIdx
      (p1 ++ idx ++ (Expr.mkAppList (.const ctorName cls) (cpar ++ cfld)) :: post).toArray
      = (rule.rhs.instantiateLevelParams rval.levelParams ls).mkAppList p1 :=
    Expr.mkAppRange_eq (l₁ := []) (l₂ := p1)
      (l₃ := idx ++ (Expr.mkAppList (.const ctorName cls) (cpar ++ cfld)) :: post)
      (by simp) rfl (by simp [hp1len])
  have hr2 : ∀ f, mkAppRange f ((cpar ++ cfld).length - rule.nfields) (cpar ++ cfld).length
      (cpar ++ cfld).toArray = f.mkAppList cfld := fun _ =>
    Expr.mkAppRange_eq (l₁ := cpar) (l₂ := cfld) (l₃ := []) (by simp) (by simp; omega) (by simp)
  have hr3 : ∀ f, mkAppRange f (rval.getMajorIdx + 1)
      (p1 ++ idx ++ (Expr.mkAppList (.const ctorName cls) (cpar ++ cfld)) :: post).length
      (p1 ++ idx ++ (Expr.mkAppList (.const ctorName cls) (cpar ++ cfld)) :: post).toArray
      = f.mkAppList post := fun _ =>
    Expr.mkAppRange_eq (l₁ := p1 ++ idx ++ [Expr.mkAppList (.const ctorName cls) (cpar ++ cfld)])
      (l₂ := post) (l₃ := []) (by simp) (by simp; omega) (by simp)
  rw [hr1, hr2] at heq
  have heq1 : e₁ = (((rule.rhs.instantiateLevelParams rval.levelParams ls).mkAppList p1).mkAppList
      cfld).mkAppList post := by
    split at heq
    · rw [hr3] at heq; exact (Option.some.inj heq).symm
    · rename_i h; simp at h
      rw [show post = [] from List.eq_nil_of_length_eq_zero (by omega)]
      exact (Option.some.inj heq).symm
  -- take the redex's translation apart along the same split
  simp only [Expr.mkAppList_append, Expr.mkAppList] at he
  obtain ⟨e₀', post', hE₀, -, rfl⟩ := TrExprS.mkAppList_inv he
  have hE₀c := hE₀
  cases hE₀ with | app _ _ hfun hmajT => ?_
  obtain ⟨_, idx', hfun2, hidxT, rfl⟩ := TrExprS.mkAppList_inv hfun
  obtain ⟨g', p1', hconst, hp1T, rfl⟩ := TrExprS.mkAppList_inv hfun2
  obtain ⟨_, cfld', hmaj2, hcfldT, rfl⟩ := TrExprS.mkAppList_inv hmajT
  obtain ⟨h₂', cpar', hcconst, hcparT, rfl⟩ := TrExprS.mkAppList_inv hmaj2
  obtain ⟨us', hc1, hc2, rfl⟩ : ∃ us', (∃ ci, c.venv.constants recName = some ci) ∧
      ls.mapM (VLevel.ofLevel c.lparams) = some us' ∧ g' = .const recName us' := by
    cases hconst with | const h1 h2 _ => exact ⟨_, ⟨_, h1⟩, h2, rfl⟩
  obtain ⟨cus', rfl⟩ : ∃ cus', h₂' = .const ctorName cus' := by
    cases hcconst with | const _ _ _ => exact ⟨_, rfl⟩
  have hp1'len : p1'.length = rval.numParams + rval.numMotives + rval.numMinors := by
    rw [← List.Forall₂.length_eq hp1T, hp1len]; rfl
  have hidx'len : idx'.length = rval.numIndices := by
    rw [← List.Forall₂.length_eq hidxT, hidxlen]
  have hcpar'len : cpar'.length = cval.numParams := by
    rw [← List.Forall₂.length_eq hcparT, hcparlen]
  have hcfld'len : cfld'.length = rule.nfields := by
    rw [← List.Forall₂.length_eq hcfldT, hcfldlen]
  -- the redex matches the recursor's ι pattern for this constructor, so the ι rule fires
  obtain ⟨g1, hm1, hg1⟩ := Pattern.matches_varN_const (c := recName) (ls := us')
    (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) (p1' ++ idx')
    (by simp [hp1'len, hidx'len])
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := ctorName) (ls := cus')
    (cval.numParams + rule.nfields) (cpar' ++ cfld') (by simp [hcpar'len, hcfld'len])
  rw [VExpr.mkApps_append] at hm1 hm2
  have hsafe : c.safety ≤ (ConstantInfo.recInfo rval).safety := by
    obtain ⟨_, h1, h2⟩ := c.trenv.find?_iff.2 hc1
    rw [hrec] at h1; cases h1; exact h2
  obtain ⟨A₀, hty⟩ := hE₀c.wf c.Ewf c.Δwf
  obtain ⟨rhs, hclosed, htr, hdefeq⟩ :=
    c.trenv.iota_rec hrec hrule hsafe hctor (hm1.app hm2) hty
  simp only [SimplePattern.iotaRHS] at hdefeq
  rw [SimplePattern.iotaRHS'_apply _ _ _ _ _ _ _ _ _ (Sum.elim g1 g2)
      (by simp [hp1'len, hidx'len]) (by simp [hcpar'len, hcfld'len]) hg1 hg2,
    List.take_left' hp1'len, List.drop_left' hcpar'len] at hdefeq
  -- the kernel's reduct translates to that ι reduct, hence to the redex's translation
  have c1 := htr.instL (Δ := []) c.Ewf trivial hc2 hlp.symm
  have htmpl : c.TrExpr (rule.rhs.instantiateLevelParams rval.levelParams ls) (rhs.instL us') := by
    have c2 := c1.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rwa [(c1.wf.closedN c.Ewf trivial).liftN_eq (Nat.zero_le _)] at c2
  have hredty : c.HasType ((rhs.instL us').mkApps (p1' ++ cfld')) A₀ :=
    (hdefeq.of_l c.Ewf c.Δwf hty).hasType.2
  have hred := TrExpr.mkAppList c.Ewf c.Δwf
    (List.Forall₂.append (List.Forall₂.imp (fun _ _ h => h.trExpr c.Ewf c.Δwf) hp1T)
      (List.Forall₂.imp (fun _ _ h => h.trExpr c.Ewf c.Δwf) hcfldT)) htmpl hredty
  have hfinal := (hred.defeq c.Ewf c.Δwf hdefeq.symm).rebuild_mkAppList c.Ewf c.Δwf hE₀c he
  rw [Expr.mkAppList_append] at hfinal
  subst heq1
  refine ⟨fun P _ hfv => ?_, hfinal⟩
  obtain ⟨-, hfv⟩ := FVarsIn.mkAppList.1 hfv
  have hmajfv :=
    (FVarsIn.mkAppList.1 (hfv _ (List.mem_append_right _ (List.mem_cons_self ..)))).2
  simp only [FVarsIn.mkAppList]
  exact ⟨⟨⟨c1.fvarsIn.mono nofun,
      fun a ha => hfv a (List.mem_append_left _ (List.mem_append_left _ ha))⟩,
    fun a ha => hmajfv a (List.mem_append_right _ ha)⟩,
    fun a ha => hfv a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))⟩

theorem reduceRecursor.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := sorry

theorem whnfFVar.WF {c : VContext} {s : VState} (he : c.TrExprS (.fvar fv) e') :
    RecM.WF c s (whnfFVar (.fvar fv) cheapProj) fun e₁ _ =>
      c.FVarsBelow (.fvar fv) e₁ ∧ c.TrExpr e₁ e' := by
  refine .getLCtx ?_
  simp [Expr.fvarId!]; split <;> [skip; exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, h2, _, h3, _⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  refine (whnfCore.WF h3).mono fun _ _ _ ⟨h4, h5⟩ => ?_
  refine ⟨h2.trans h4, h5.defeq c.Ewf c.Δwf ?_⟩
  refine (TrExprS.fvar h1).uniq c.Ewf ?_ he
  exact .refl c.Ewf c.Δwf

theorem whnfCore'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : full e → RecM.WF c s (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · let .mdata he := he
      exact hP ▸ whnfCore'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnfCore_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have hsave {e₁ s} (h1 : c.FVarsBelow e e₁) (h2 : c.TrExpr e₁ e') :
      (save e cheapProj e₁).WF c s P := by
    simp [save]
    split <;> [skip; exact hP ▸ .pure ⟨h1, h2⟩]
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (.eqv eq ?_) ?_ --_ (.eqv h2 eq BEq.rfl) (.eqv eq ?_) ?_
      · exact he.fvarsIn.mono wf.ngen_wf
      · exact h2.fvarsIn.mono wf.ngen_wf
    exact hP ▸ ⟨.rfl, { wf with whnfCore_wf := hic wf.whnfCore_wf }, h1, h2⟩
  split <;> cases hfull
  · exact hP ▸ whnfFVar.WF he
  · rename_i fn arg _; generalize eq : fn.app arg = e at *
    have ⟨_, stk⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
    refine (whnfCore.WF stk.tr).bind fun _ s _ ⟨h1, h2⟩ => ?_
    split <;> [rename_i name dom body bi _; split]
    · let rec loop.WF {e e' i rargs f} (H : LambdaBodyN i e' f) (hi : i ≤ rargs.size) :
        ∃ n f', LambdaBodyN n e' f' ∧ n ≤ rargs.size ∧
          loop e cheapProj rargs i f = loop.cont e cheapProj rargs n f' := by
        unfold loop; split
        · split
          · refine loop.WF (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
          · exact ⟨_, _, H, hi, rfl⟩
        · exact ⟨_, _, H, hi, rfl⟩
      refine
        let ⟨i, f, h3, h4, eq⟩ := loop.WF (e' := .lam name dom body bi) (.succ .zero) <| by
          simp [← eq, Expr.getAppRevArgs_eq, Expr.getAppArgsRevList]
        eq ▸ ?_; clear eq
      simp [Expr.getAppRevArgs_eq] at h4 ⊢
      obtain ⟨l₁, l₂, h5, rfl⟩ : ∃ l₁ l₂, e.getAppArgsRevList = l₁ ++ l₂ ∧ l₂.length = i :=
        ⟨_, _, (List.take_append_drop (e.getAppArgsRevList.length - i) ..).symm, by simp; omega⟩
      simp [loop.cont, h5, List.take_of_length_le]
      rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₂ := l₁) (l₃ := l₂) (by simp) (by rfl) (by rfl)]
      have br := BetaReduce.inst_reduce (l₁ := l₂.reverse)
        [] (by simpa using h3) (Expr.instantiateList_append ..) (h := by
          have := h5 ▸ (c.mlctx.noBV ▸ he.closed).getAppArgsRevList
          simp [or_imp, forall_and] at this ⊢
          exact this.2) |>.mkAppRevList (es := l₁)
      simp [← Expr.mkAppRevList_reverse, ← Expr.mkAppRevList_append, ← h5] at br
      have := h2.rebuild_mkAppRevList c.Ewf c.Δwf stk.tr <|
        e.mkAppRevList_getAppArgsRevList ▸ he
      have ⟨_, a1, a2⟩ := this.beta c.Ewf c.Δwf br
      refine (whnfCore.WF a1).bind fun _ _ _ ⟨b1, b2⟩ => ?_
      have hb := e.mkAppRevList_getAppArgsRevList ▸ h1.mkAppRevList
      exact hsave (hb.trans (.betaReduce br) |>.trans b1) <|
        b2.defeq c.Ewf c.Δwf a2
    · refine (reduceRecursor.WF he).bind fun _ _ _ h => ?_
      split <;> [skip; exact hid]
      let ⟨h1, _, h2, eq⟩ := h _ rfl
      refine hP ▸ (whnfCore.WF h2).mono fun _ _ _ ⟨h3, h4⟩ => ?_
      exact ⟨h1.trans h3, h4.defeq c.Ewf c.Δwf eq⟩
    · rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₃ := [])
        (by simp [Expr.getAppRevArgs_toList]; rfl) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
      have {e e₁ : Expr} (hb : c.FVarsBelow e e₁) {es e₀' e'}
          (hes : c.TrExprS (e.mkAppRevList es) e₀') (he : c.TrExprS e e') (he₁ : c.TrExpr e₁ e') :
          c.FVarsBelow (e.mkAppRevList es) (e₁.mkAppRevList es) ∧
          c.TrExpr (e₁.mkAppRevList es) e₀' := by
        induction es generalizing e₁ e₀' e' with
        | nil =>
          refine ⟨hb, he₁.defeq c.Ewf c.Δwf ?_⟩
          exact he.uniq c.Ewf (.refl c.Ewf c.Δwf) hes
        | cons _ _ ih =>
          have .app h1 h2 h3 h4 := hes
          have ⟨h5, h6⟩ := ih hb h3 he he₁
          exact ⟨fun _ hP he => ⟨h5 _ hP he.1, he.2⟩,
            .app c.Ewf c.Δwf h1 h2 h6 (h4.trExpr c.Ewf c.Δwf)⟩
      have eq := e.mkAppRevList_getAppArgsRevList
      let ⟨h3, _, h4, eq⟩ := eq ▸ this h1 (eq ▸ he) stk.tr h2
      refine (whnfCore.WF h4).bind fun _ _ _ ⟨h5, h6⟩ => ?_
      refine hsave (h3.trans h5) (h6.defeq c.Ewf c.Δwf eq)
  · let .letE h1 h2 h3 h4 := he
    refine (whnfCore.WF (h4.inst_let c.Ewf.ordered h3)).bind fun _ _ _ ⟨h1, h2⟩ => ?_
    exact hsave (.trans (fun _ _ he => he.2.2.instantiate1 he.2.1) h1) h2
  · refine (reduceProj.WF he).bind fun _ _ _ H => ?_
    split
    · let ⟨h1, _, h2, eq⟩ := H _ rfl
      refine (whnfCore.WF h2).bind fun _ _ _ ⟨h3, h4⟩ => ?_
      exact hsave (h1.trans h3) (h4.defeq c.Ewf c.Δwf eq)
    · exact hsave .rfl (he.trExpr c.Ewf c.Δwf)

theorem whnf'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnf'; extract_lets F
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : RecM.WF c s (F ()) P by
    split
    any_goals exact hid
    any_goals exact hF
    · let .mdata he := he
      exact hP ▸ whnf'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF]
  simp [F]; refine .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnf_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have {e e' s n} (he : c.TrExprS e e') : (loop e n).WF c s fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    induction n generalizing s e e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.WF he).bind fun e₁ s _ ⟨h1, _, he₁, eq⟩ => ?_
    refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h3 => ?_
    split <;> [cases h3 _ rfl; skip]
    refine (reduceNat.WF he₁).bind fun _ _ _ h3 => ?_; split
    · exact .pure ⟨.trans h1 (h3 _ rfl).1, (h3 _ rfl).2.defeq c.Ewf c.Δwf eq⟩
    refine (unfoldDefinition.WF he₁).bind fun _ _ _ H => ?_
    split <;> [skip; exact .pure ⟨h1, _, he₁, eq⟩]
    have ⟨a1, _, a2, eq'⟩ := H
    refine (ih a2).mono fun _ _ _ ⟨b1, b2⟩ => ?_
    exact ⟨h1.trans <| a1.trans b1, b2.defeq c.Ewf c.Δwf <| eq'.trans c.Ewf c.Δwf eq⟩
  refine .readThe <| (this he).bind fun e₁ s _ ⟨h1, h2⟩ => ?_
  rintro _ mwf wf a s' ⟨⟩
  refine let s' := _; ⟨s', rfl, ?_⟩
  have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
    intro _ _ h
    rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
    rename_i eq
    refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (.eqv eq ?_) ?_
    · exact he.fvarsIn.mono wf.ngen_wf
    · exact h2.fvarsIn.mono wf.ngen_wf
  exact hP ▸ ⟨.rfl, { wf with whnf_wf := hic wf.whnf_wf }, h1, h2⟩
