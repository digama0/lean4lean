import Lean4Lean.Verify.Inductive.Recursor.Signature.Families
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem insertBinders_eq_prefix (domains : List VExpr) (n : Nat) :
    InductiveSignature.insertBinders domains n =
      (liftContextPrefixAt n 0 domains.reverse).reverse := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i hleft hright
    have hi : i < domains.length := by simpa [InductiveSignature.insertBinders] using hleft
    have hget := liftContextPrefixAt_reverse_getElem n 0 domains i hi
    simpa [InductiveSignature.insertBinders, getElem!_pos, hi] using hget.symm

theorem vars_eq_bvarSpine (n : Nat) : InductiveSignature.vars n 0 = bvarSpine n := by
  simp [InductiveSignature.vars, bvarSpine]

theorem vars_lift (count below n : Nat) :
    (InductiveSignature.vars count below).map (fun e => e.liftN n 0) =
      InductiveSignature.vars count (n + below) := by
  simp [InductiveSignature.vars, List.map_map, Function.comp_def, VExpr.liftN,
    Nat.add_comm, Nat.add_left_comm]

theorem vars_lift_below (count below n : Nat) :
    (InductiveSignature.vars count below).map (fun e => e.liftN n below) =
      InductiveSignature.vars count (n + below) := by
  apply List.ext_getElem
  · simp [InductiveSignature.vars]
  · intro i hleft hright
    have hi : i < count := by simpa [InductiveSignature.vars] using hright
    simp only [InductiveSignature.vars, List.getElem_map, List.getElem_reverse,
      List.length_range, List.getElem_range] at *
    simp only [VExpr.liftN, liftVar]
    split <;> simp_all <;> omega

theorem vars_lift_above (count n : Nat) :
    (InductiveSignature.vars count 0).map (fun e => e.liftN n count) =
      InductiveSignature.vars count 0 := by
  apply List.ext_getElem
  · simp [InductiveSignature.vars]
  · intro i hleft hright
    have hi : i < count := by simpa [InductiveSignature.vars] using hright
    simp only [InductiveSignature.vars, List.getElem_map, List.getElem_reverse,
      List.length_range, List.getElem_range] at *
    simp only [VExpr.liftN, liftVar]
    split
    · simp_all
    · omega

theorem motive_eq_scalar_lift (g : InductiveSignature.Instance s)
    (family : InductiveSignature.Family) (prior : Nat) :
    g.motive family prior =
      (VExpr.wrapForalls (family.indices.map (VExpr.instL g.levels))
        (.forallE
          (VExpr.mkApps (.const family.name g.levels)
            (bvarSpine (s.params.length + family.indices.length)))
          (.sort g.targetLevel))).liftN prior 0 := by
  rw [VExpr.liftN_wrapForalls]
  simp only [Nat.zero_add, VExpr.liftN, VExpr.liftN_mkApps, List.length_map]
  rw [bvarSpine_add, List.map_append, ← vars_eq_bvarSpine,
    ← vars_eq_bvarSpine, vars_lift, Nat.add_zero, vars_lift_below, vars_lift_above]
  simp [InductiveSignature.Instance.motive, insertBinders_eq_prefix,
    VExpr.wrapForalls]

theorem TrExprS.of_forallBinderTranslations
    (Htel : Expr.ForallTelescope source n residual)
    (hlen : domains.length = n)
    (Hdomains : ∀ i (hi : i < domains.length) sourceDomain,
      Expr.ForallBinderAt source i sourceDomain →
      TrExprS env Us (abstractForallContext (domains.take i) Δ) sourceDomain domains[i] ∧
      env.IsType Us.length (abstractForallContext (domains.take i) Δ).toCtx domains[i])
    (Hres : TrExprS env Us (abstractForallContext domains Δ) residual result)
    (HresType : env.IsType Us.length (abstractForallContext domains Δ).toCtx result) :
    TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using And.intro Hres HresType
  | @cons body arity residual name sourceDom bi Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      have Hdom := Hdomains 0 (by simp) sourceDom .here
      simp only [List.take_zero, abstractForallContext, List.reverse_nil, List.map_nil,
        List.nil_append, List.getElem_cons_zero] at Hdom
      have Htail : ∀ i (hi : i < domains.length) sourceDomain,
          Expr.ForallBinderAt body i sourceDomain →
          TrExprS env Us (abstractForallContext (domains.take i) ((none, .vlam dom) :: Δ))
            sourceDomain domains[i] ∧
          env.IsType Us.length
            (abstractForallContext (domains.take i) ((none, .vlam dom) :: Δ)).toCtx domains[i] := by
        intro i hi sourceDomain Hb
        have Hd := Hdomains (i+1) (by simpa using hi) sourceDomain (.there Hb)
        simp only [List.getElem_cons_succ] at Hd
        simpa [abstractForallContext, List.take_succ_cons, List.map_append, List.append_assoc] using Hd
      obtain ⟨Hbody, HbodyType⟩ := ih (by simpa using hlen) Htail
        (by simpa [abstractForallContext, List.map_append, List.append_assoc] using Hres)
        (by simpa [abstractForallContext, List.map_append, List.append_assoc] using HresType)
      exact ⟨.forallE Hdom.2 HbodyType Hdom.1 Hbody, .forallE Hdom.2 HbodyType⟩

theorem RecursorConstruction.motiveSource_support
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    let source := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
    source.FVarsIn (fun fv => fv ∈ H.params.fvars) ∧ Closed source 0 := by
  obtain ⟨S, _⟩ := H.motiveTelescopes.motiveDecls owner howner
  rcases cachedParameterDecls_fvars S.motiveParameterDecls with
    ⟨parameterFVars, hparameterExprs, hparameterScopeFVars⟩
  have hstatsParams : stats.params.toList.reverse = H.params.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList H.params.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have hparameterFVars : parameterFVars = H.params.fvars.reverse := by
    apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
    exact hparameterExprs.symm.trans hstatsParams
  have Hfv := S.motiveSourceFVars
  rw [S.motiveSourceParameterScope, hparameterScopeFVars, hparameterFVars] at Hfv
  refine ⟨by simpa using Hfv, ?_⟩
  simpa [H.recursorWF.mlctx.noBV] using S.motiveTypeTr.closed

theorem RecursorConstruction.motiveBinderSource
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    let source := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
    Expr.ForallBinderAt
      ((H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) (.sort .zero)).abstractList
        H.params.fvars) owner
      ((source.abstractList H.params.fvars).liftLooseBVars' 0 owner) := by
  obtain ⟨D⟩ := H.bindings.motives.declarationAt H.localWF owner (by simpa using howner)
  have hparts := (H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner).parts
  have hmotives : H.bindings.motives.fvars.Nodup := hparts.motives
  have hparams : H.params.fvars.Nodup := hparts.params
  have Hb := ((H.bindings.motives.toCDeclArray H.localWF).forallBinderAt
    hmotives D (body := .sort .zero)).abstractList H.params.fvars
  have Htype := (H.origins.motives.type_eq D).trans (H.motiveShapes.shape owner howner)
  have Hsupport := H.motiveSource_support owner howner
  have Hnone : D.type.FVarsIn (fun fv => fv ∉ H.bindings.motives.fvars.take owner) := by
    rw [Htype]
    apply Hsupport.1.mono
    intro fv hfv hmem
    have hm := List.mem_of_mem_take hmem
    exact hparts.params_later fv hfv fv (by
      simp [RecInfoBindings.toRecursorBinderGroups, FVarArrayIn.toCDeclArray, hm]) rfl
  have Hclosed : Closed D.type 0 := Htype ▸ Hsupport.2
  simp only [FVarArrayIn.toCDeclArray, Nat.zero_add] at Hb
  change Expr.ForallBinderAt _ owner
    ((D.type.abstractN (H.bindings.motives.fvars.take owner)).abstractList H.params.fvars owner) at Hb
  rw [Expr.abstractN_eq_abstractList_of_closed
    (List.Nodup.sublist (List.take_sublist _ _) hmotives) Hclosed] at Hb
  have Habstract := Expr.abstractList_add_eq_liftLooseBVars (extra := owner) Hclosed hparams
  simp only [Nat.zero_add] at Habstract
  rw [Hnone.abstractList_eq_self Hclosed, Habstract, Htype] at Hb
  exact Hb

theorem RecursorConstruction.sourceParameterCount
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) : R.parameterScope.toCtx.length = stats.params.size := by
  have hlength := Lean4Lean.List.Forall₂.length_eq H.parameterSuffix.cached
  have hctxLength := checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
    H.parameterSuffix.cached
  have hdomains := congrArg List.length H.parameterDomains
  simp only [List.length_reverse, List.length_map] at hdomains
  rw [← hdomains, hctxLength, ← hlength]
  simp

theorem RecursorConstruction.generatedMotiveBinder
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (g : InductiveSignature.Instance s)
    (hp : s.params = R.parameterScope.toCtx.reverse)
    (_hf : s.families = H.families)
    (hl : g.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some g.targetLevel)
    (owner : Fin H.recInfos.size) (prior : List VExpr) (hprior : prior.length = owner.val) :
    let source := H.localContext.lctx.mkForall H.recInfos[owner.val]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner.val]!.major] (.sort H.elimLevel))
    TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext prior (abstractForallContext g.params []))
      ((source.abstractList H.params.fvars).liftLooseBVars' 0 owner.val)
      (g.motive (H.families[owner.val]'(by simp [owner.isLt])) owner.val) := by
  have Hscalar := (H.sourceIndices_motive owner hu).1
  have hp' : g.params = H.parameterSuffix.parameterDecls.toCtx.reverse := by
    rw [InductiveSignature.Instance.params, hp, hl, H.parameterDomains]
  have Hweak := Hscalar.weakBV H.recursorWF.checking.tr.wf.orderedStrong
    (abstractForallContext.bvLift prior
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []))
  rw [hprior] at Hweak
  rw [hp', motive_eq_scalar_lift]
  simpa only [H.families_indices owner, H.families_name owner, hl,
    H.sourceIndices_length owner, hp, List.length_reverse, H.sourceParameterCount] using Hweak

theorem RecursorConstruction.generatedMotivesTranslation
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (g : InductiveSignature.Instance s)
    (hp : s.params = R.parameterScope.toCtx.reverse)
    (hf : s.families = H.families)
    (hl : g.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some g.targetLevel) :
    TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext g.params [])
      ((H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) (.sort .zero)).abstractList
        H.params.fvars)
      (VExpr.wrapForalls g.motives (.sort .zero)) ∧
    H.recursorWF.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext g.params []).toCtx
      (VExpr.wrapForalls g.motives (.sort .zero)) := by
  have hcount : g.motives.length = H.recInfos.size := by
    simp [InductiveSignature.Instance.motives, hf]
  have Htel := (H.bindings.motives.mkForall_forallTelescope H.localWF (.sort .zero)).abstractList
    H.params.fvars
  have hsort (fvars : List FVarId) (k : Nat) :
      (Expr.sort .zero).abstractList fvars k = .sort .zero :=
    Expr.abstractList_eq_self_of_abstract1 _ (by intro fv depth; simp [Expr.abstract1]) fvars k
  have hsortN (fvars : List FVarId) (k : Nat) :
      (Expr.sort .zero).abstractN fvars k = .sort .zero := rfl
  simp only [Array.size_map, hsort, hsortN] at Htel
  apply TrExprS.of_forallBinderTranslations Htel hcount
  · intro i hi sourceDomain Hbinder
    have hi' : i < H.recInfos.size := by omega
    have hsource := Hbinder.unique (H.motiveBinderSource i hi')
    rw [hsource]
    have htake : (g.motives.take i).length = i := by simp; omega
    have Htr := H.generatedMotiveBinder g hp hf hl hu ⟨i, hi'⟩ (g.motives.take i) htake
    have htarget : g.motives[i] = g.motive (H.families[i]'(by simp [hi'])) i := by
      simp [InductiveSignature.Instance.motives, hf]
    rw [htarget]
    refine ⟨Htr, ?_⟩
    obtain ⟨S, _⟩ := H.motiveTelescopes.motiveDecls i hi'
    have Hindices := S.indicesBound.mkForall_forallTelescope H.localWF
      (H.localContext.lctx.mkForall #[H.recInfos[i]!.major] (.sort H.elimLevel))
    have Hmajor := (S.majorBound.mkForall_forallTelescope H.localWF (.sort H.elimLevel)).abstractN
      S.indicesBound.fvars
    have Hwhole := ((Hindices.trans Hmajor).abstractList H.params.fvars).liftLooseBVars' 0 i
    exact TrExprS.isType_of_forallTelescope Hwhole (by simp) Htr
  · exact .sort rfl
  · exact ⟨_, .sort trivial⟩

/-- For an instance `g` whose parameters, families, universe levels and target level are those
of the recursor construction, the executable's closed parameter-and-motive telescope (ending in
`Prop`) translates to `g.params ++ g.motives` in the recursor-checking environment at the
recursor's universe parameters. -/
theorem RecursorConstruction.generatedParametersMotivesTranslation
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (g : InductiveSignature.Instance s)
    (hp : s.params = R.parameterScope.toCtx.reverse)
    (hf : s.families = H.families)
    (hl : g.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some g.targetLevel) :
    TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params
        (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) (.sort .zero)))
      (VExpr.wrapForalls (g.params ++ g.motives) (.sort .zero)) := by
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have Htel := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) (.sort .zero))
  have hcount : g.params.length = stats.params.size := by
    simp [InductiveSignature.Instance.params, hp, H.sourceParameterCount]
  have Htemplate : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (Expr.forallDomainsOnly stats.params.size
        (H.localContext.lctx.mkForall stats.params
          (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) (.sort .zero))))
      (VExpr.wrapForalls g.params (.sort .zero)) := by
    rw [H.params.forallDomainsOnly H.localWF hparams, H.recursorEnv]
    simpa only [InductiveSignature.Instance.params, hp, hl] using H.sourceParameterTranslation
  obtain ⟨Hmotives, HmotivesType⟩ := H.generatedMotivesTranslation g hp hf hl hu
  have hmotivesNodup : H.bindings.motives.fvars.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp houter).1).2.1
  have hmotivesClosed : Closed (H.localContext.lctx.mkForall (H.recInfos.map (·.motive))
      (.sort .zero)) :=
    H.bindings.motives.mkForall_closed H.localWF hmotivesNodup H.recursorWF.lctxClosed trivial
  rw [← Expr.abstractN_eq_abstractList_of_closed hparams hmotivesClosed] at Hmotives
  have Hfull := (TrExprS.rebuildForallPrefix Htel hcount Htemplate Hmotives HmotivesType).1
  rw [H.recursorEnv, ← VExpr.wrapForalls_append] at Hfull
  exact Hfull

end Lean4Lean.VerifyInductive
