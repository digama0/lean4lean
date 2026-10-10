import Lean4Lean.Verify.Inductive.Recursor.Signature.FieldDomains

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Given a translation of a telescope to a type `target` and a translation of its first `n`
domains to `domains`, the telescope also translates to `wrapForalls domains result` for some
`result` that translates the residual in the context extended by `domains`; both are types,
and `target` is definitionally equal to `wrapForalls domains result`. -/
theorem TrExprS.retargetForallPrefix
    (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (Htel : Expr.ForallTelescope source n residual)
    (hdomains : domains.length = n)
    (Hfull : TrExprS env Us Δ source target)
    (Htype : env.IsType Us.length Δ.toCtx target)
    (Htemplate : TrExprS env Us Δ (Expr.forallDomainsOnly n source)
      (VExpr.wrapForalls domains (.sort .zero))) :
    ∃ result,
      TrExprS env Us Δ source (VExpr.wrapForalls domains result) ∧
      env.IsType Us.length Δ.toCtx (VExpr.wrapForalls domains result) ∧
      TrExprS env Us (abstractForallContext domains Δ) residual result ∧
      env.IsType Us.length (abstractForallContext domains Δ).toCtx result ∧
      env.IsDefEqU Us.length Δ.toCtx target (VExpr.wrapForalls domains result) := by
  obtain ⟨oldDomains, oldResult, hlen, heq, _⟩ :=
    TrExprS.forallTelescope_shape_with_context Htel Hfull
  subst target
  have Hprefix := (TrExprS.forallDomainsOnly Htel hlen Hfull).1
  have Hcontexts := TrExprS.forallPrefixContextEq henv Htel.domainsOnly hlen hdomains
    Hprefix Htemplate (.refl henv hΔ)
  obtain ⟨Hres, HresType⟩ := TrExprS.forallTelescope_residual_typed Htel hlen Hfull Htype
  obtain ⟨result, HnewRes⟩ := Hres.defeqDFC henv Hcontexts
  have HresEq := Hres.uniq henv Hcontexts HnewRes
  have HnewType := (HresType.defeqU_l henv Hcontexts.wf.toCtx HresEq).defeqDFC
    henv.ordered Hcontexts.defeqCtx
  obtain ⟨Hnew, HnewFullType⟩ := TrExprS.rebuildForallPrefix Htel hdomains Htemplate HnewRes HnewType
  exact ⟨result, Hnew, HnewFullType, HnewRes, HnewType,
    Hfull.uniq henv (.refl henv hΔ) Hnew⟩

/-- The field telescope of a minor's constructor traversal, ending in its terminal family
application and abstracted over the parameters, translates in the header environment to
`wrapForalls domains result` with `domains` the unannotated field domains
(`declFieldDomains`), and the terminal application translates to `result` over those domains;
both are types. -/
theorem RecursorConstruction.sourceConstructorTail
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let domains := H.declFieldDomains owner howner localIndex hlocal
    ∃ result,
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars)
        (VExpr.wrapForalls domains result) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx (VExpr.wrapForalls domains result) ∧
      TrExprS R.headerVEnv c.lparams
        (abstractForallContext domains (abstractForallContext R.parameterScope.toCtx.reverse []))
        ((HS.semantic.traversal.terminal.abstractList HS.semantic.fieldsRecent.fvars).abstractList
          H.params.fvars S.fields.size) result ∧
      R.headerVEnv.IsType c.lparams.length (domains.reverse ++ R.parameterScope.toCtx) result := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  obtain ⟨sourceTarget, Hsource, HsourceType, _⟩ :=
    H.constructorUnannotatedHeaderReplay owner howner localIndex hlocal HS
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  let Hbound := HS.semantic.fieldsRecent.toFVarArrayIn.mono Hext
  have Htel := (Hbound.mkForall_forallTelescope H.localWF HS.semantic.traversal.terminal).abstractList H.params.fvars
  simp only [Nat.zero_add] at Htel
  have Htemplate : TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
      (Expr.forallDomainsOnly S.fields.size
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars))
      (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal) (.sort .zero)) := by
    rw [Expr.forallDomainsOnly_abstractList,
      Hbound.forallDomainsOnly H.localWF HS.semantic.fieldsRecent.nodup]
    exact (H.sourceFields_headerReplay owner howner localIndex hlocal).1
  have HsourceType' : R.headerVEnv.IsType c.lparams.length
      (abstractForallContext R.parameterScope.toCtx.reverse []).toCtx sourceTarget := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HsourceType
  obtain ⟨result, Hnew, HnewType, Hres, HresType, _⟩ :=
    TrExprS.retargetForallPrefix R.headerCheckingAnnotations.1.wf R.headerAnonymousParameterWF Htel
      (H.sourceFields_length owner howner localIndex hlocal) Hsource HsourceType' Htemplate
  have hterminalClosed : Closed HS.semantic.traversal.terminal := by
    have h := HS.semantic.terminalTranslation.closed
    simpa [TypeChecker.MLCtx.noBV] using h
  have hboundNodup : Hbound.fvars.Nodup := HS.semantic.fieldsRecent.nodup
  rw [Expr.abstractN_eq_abstractList_of_closed (xs := Hbound.fvars) hboundNodup
    hterminalClosed] at Hres
  refine ⟨result, Hnew, ?_, Hres, ?_⟩
  · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HnewType
  · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HresType

end Lean4Lean.VerifyInductive

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem TrExprS.forallTelescope_residual
    (Htel : Expr.ForallTelescope source n residual) (hlen : domains.length = n)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result)) :
    TrExprS env Us (abstractForallContext domains Δ) residual result := by
  induction Htel generalizing Δ domains result with
  | nil =>
    have hnil := List.eq_nil_of_length_eq_zero hlen
    subst domains
    simpa [abstractForallContext, VExpr.wrapForalls] using Htr
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons dom domains =>
      cases Htr with
      | forallE _ _ _ Hbody =>
        simpa [abstractForallContext, List.map_append, List.append_assoc] using
          ih (by simpa using hlen) Hbody

theorem RecursorConstruction.constructorTerminalSpine
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    HS.semantic.traversal.terminal.getAppFn =
      .const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name stats.levels ∧
    HS.semantic.traversal.terminal.getAppArgsList.take stats.params.size = stats.params.toList := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, hstats, hvalid, _⟩ :=
    H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at hvalid hstats
  obtain ⟨htarget, hvalidIdx⟩ := checkPositivityStep.isValidIndApp?_some hvalid
  have htarget' : (AddInductive.getIIndices stats HS.semantic.traversal.terminal).1 < decl.types.length := by
    rwa [H.cardinality.families] at htarget
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalidIdx (H.validStats.indConstAt htarget')
  refine ⟨?_, H.validStats.sourceParameterPrefix hvalidIdx⟩
  obtain ⟨rawTraversal, hrawTraversal, hownerEq, _, hcount, Hraw⟩ :=
    H.minorSourceReplay owner howner hsourceOwner localIndex hlocal
      (H.sourceMinorOffsetBound owner howner localIndex hlocal)
  have heqRaw : rawTraversal = HS.semantic.traversal :=
    Option.some.inj (hrawTraversal.symm.trans HS.semantic.traversal_eq)
  rw [heqRaw] at Hraw hcount
  let ctor := R.sourceSignatureConstructor
    ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
  change HS.semantic.traversal.fields.size = ctor.fields.length at hcount
  change ctor.owner.val = owner at hownerEq
  have hfieldlen : (R.sourceSignature.fieldTypes ctor).length = HS.semantic.traversal.fields.size := by
    simp only [InductiveSignature.fieldTypes, List.length_map, List.length_zipIdx]
    exact hcount.symm
  have Hres := TrExprS.forallTelescope_residual (domains := R.sourceSignature.fieldTypes ctor)
    HS.semantic.traversal.fieldTelescope hfieldlen Hraw
  rw [← HS.semantic.traversal.fieldClosed] at Hres
  have hclosedHead : (HS.semantic.traversal.terminal.abstractList HS.semantic.traversal.fieldFVars).getAppFn =
      .const (decl.types[(AddInductive.getIIndices stats HS.semantic.traversal.terminal).1]'htarget').name stats.levels := by
    rw [Expr.getAppFn_abstractList, hhead, Expr.abstractList_const]
  obtain ⟨levels, args, hspine, _, _⟩ := checkPositivityStep.TrExprS.constAppSpine Hres hclosedHead
  have hname := congrArg (fun pair => pair.1) hspine
  simp only [InductiveSignature.familyApp] at hname
  rw [VExpr.getAppFnArgs_mkApps] at hname
  have hfamilyOwner : R.sourceSignatureHeader.families[ctor.owner].name =
      (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name := by
    have hheader : owner < R.sourceSignatureHeader.families.size := by
      have := ctor.owner.isLt
      omega
    have hfamily := List.forall₂_getElem R.sourceSignatureHeader_families owner
      (by simpa using hheader) (by rw [← H.cardinality.records]; exact howner)
    have hfin : ctor.owner = ⟨owner, hheader⟩ := Fin.ext hownerEq
    exact (congrArg (fun i : Fin R.sourceSignatureHeader.families.size =>
      R.sourceSignatureHeader.families[i].name) hfin).trans
      (by simpa only [Array.getElem_toList, Fin.getElem_fin] using hfamily.1)
  rw [hhead]
  congr 1
  exact (VExpr.const.inj hname).1.symm.trans hfamilyOwner

theorem RecursorConstruction.constructorClosedParameters
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    stats.params.toList.map (fun arg =>
      (arg.abstractList HS.semantic.fieldsRecent.fvars).abstractList
        H.params.fvars (H.origins.minorShapes owner howner localIndex hlocal).fields.size) =
      List.ofFn (fun i : Fin stats.params.size => Expr.bvar
        ((H.origins.minorShapes owner howner localIndex hlocal).fields.size +
          (stats.params.size - 1 - i))) := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  have hfields : HS.semantic.fieldsRecent.fvars = S.fields_bound.fvars :=
    HS.semantic.fieldsRecent.toFVarArrayIn.fvars_eq_of_array_eq S.fields_bound rfl
  have hdisjoint : ∀ fv ∈ H.params.fvars, fv ∉ HS.semantic.fieldsRecent.fvars := by
    intro fv hp hf
    have h := H.templates.fields_outer_fresh owner howner localIndex hlocal fv
      (hfields ▸ hf)
    apply h
    simp only [List.mem_append]
    exact Or.inl (Or.inl (H.params.exprArrayFVarIds ▸ hp))
  have hnd : H.params.fvars.Nodup :=
    (List.pairwise_append.mp (List.pairwise_append.mp
      (H.bindings.outerNodup H.params H.noAlias)).1).1
  have hfirst := congrArg Array.toList
    (Expr.abstractList_fvarArray_of_disjoint H.params.fvars HS.semantic.fieldsRecent.fvars 0 hdisjoint)
  have hsecond := congrArg Array.toList
    (Expr.abstractList_fvarArray H.params.fvars S.fields.size hnd)
  simp only [Array.toList_map] at hfirst hsecond
  have hcombined := (congrArg (List.map fun e => e.abstractList H.params.fvars S.fields.size) hfirst).trans hsecond
  have hlength : H.params.fvars.length = stats.params.size := H.params.length_fvars
  have hsource : stats.params.toList = H.params.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList H.params.expressions
  simp only [List.map_map, Function.comp_def] at hcombined
  rw [hlength] at hcombined
  simpa only [hsource, List.map_map, Function.comp_def] using hcombined

theorem TrExprS.shiftedBvarSpine_eq
    (Hargs : List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
      (List.ofFn (fun i : Fin n => Expr.bvar (below + (n - 1 - i)))) targets)
    (hbound : n + below ≤ domains.length) :
    targets = InductiveSignature.vars n below := by
  apply List.ext_getElem
  · have h := Lean4Lean.List.Forall₂.length_eq Hargs
    simpa [InductiveSignature.vars] using h.symm
  · intro i hi hj
    have hin : i < n := by simpa [InductiveSignature.vars] using hj
    have h := List.forall₂_getElem Hargs i (by simpa using hin) hi
    simp only [List.getElem_ofFn] at h
    have heq := TrExprS.bvar_eq_of_abstractForallContext h (by omega)
    simpa [InductiveSignature.vars, List.getElem_reverse] using heq

theorem RecursorConstruction.constructorResultIndices
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let domains := H.declFieldDomains owner howner localIndex hlocal
    ∃ indices,
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars)
        (VExpr.wrapForalls domains (VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (VLevel.params decl.uvars))
          (InductiveSignature.vars stats.params.size S.fields.size ++ indices))) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls domains (VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (VLevel.params decl.uvars))
          (InductiveSignature.vars stats.params.size S.fields.size ++ indices))) ∧
      List.Forall₂ (TrExprS R.headerVEnv c.lparams
        (abstractForallContext domains (abstractForallContext R.parameterScope.toCtx.reverse [])))
        ((HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size).map fun arg =>
          (arg.abstractList HS.semantic.fieldsRecent.fvars).abstractList H.params.fvars S.fields.size)
        indices := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  let domains := H.declFieldDomains owner howner localIndex hlocal
  obtain ⟨result, Hfull, Htype, Hres, _⟩ := H.sourceConstructorTail owner howner localIndex hlocal HS
  obtain ⟨hhead, hparams⟩ := H.constructorTerminalSpine owner howner localIndex hlocal HS
  have hclosedHead : ((HS.semantic.traversal.terminal.abstractList HS.semantic.fieldsRecent.fvars).abstractList
      H.params.fvars S.fields.size).getAppFn =
      .const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name stats.levels := by
    rw [Expr.getAppFn_abstractList (k := S.fields.size), Expr.getAppFn_abstractList, hhead,
      Expr.abstractList_const, Expr.abstractList_const]
  obtain ⟨levels, args, hspine, hlevels, Hargs⟩ :=
    checkPositivityStep.TrExprS.constAppSpine Hres hclosedHead
  have hlevelsEq : levels = VLevel.params decl.uvars :=
    Option.some.inj (hlevels.symm.trans (R.recursorHeaders.levelParamsTranslation H.lparamsNodup))
  subst levels
  have hsplit : HS.semantic.traversal.terminal.getAppArgsList = stats.params.toList ++
      HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size := by
    conv => lhs; rw [← List.take_append_drop stats.params.size HS.semantic.traversal.terminal.getAppArgsList]
    rw [hparams]
  rw [Expr.getAppArgsList_abstractList (k := S.fields.size), Expr.getAppArgsList_abstractList, hsplit,
    List.map_append, List.map_append] at Hargs
  simp only [List.map_map, Function.comp_def] at Hargs
  rw [H.constructorClosedParameters owner howner localIndex hlocal HS] at Hargs
  obtain ⟨params, indices, hargsEq, Hparams, Hindices⟩ :=
    checkPositivityStep.List.Forall₂.split_left Hargs
  rw [abstractForallContext_append] at Hparams
  have hparamsEq := TrExprS.shiftedBvarSpine_eq Hparams (by
    simp only [List.length_append, List.length_reverse]
    rw [H.sourceParameterCount, H.sourceFields_length]
    omega)
  subst params
  have hresult : result = VExpr.mkApps
      (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
        (VLevel.params decl.uvars))
      (InductiveSignature.vars stats.params.size S.fields.size ++ indices) := by
    have h := congrArg (fun pair => VExpr.mkApps pair.1 pair.2) hspine
    simp only [VExpr.getAppFnArgs] at h
    rw [VExpr.mkApps_getAppFnArgs] at h
    simpa only [hargsEq] using h
  rw [hresult] at Hfull Htype
  exact ⟨indices, Hfull, Htype, Hindices⟩

theorem RecursorConstruction.constructorTerminalOwner
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    AddInductive.isValidIndApp? stats HS.semantic.traversal.terminal = some owner := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, _, hvalid, _⟩ :=
    H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at hvalid
  obtain ⟨htarget, hvalidIdx⟩ := checkPositivityStep.isValidIndApp?_some hvalid
  have htarget' : (AddInductive.getIIndices stats HS.semantic.traversal.terminal).1 < decl.types.length := by
    rwa [H.cardinality.families] at htarget
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalidIdx (H.validStats.indConstAt htarget')
  have hactual := (H.constructorTerminalSpine owner howner localIndex hlocal HS).1
  have hname := (Expr.const.inj (hhead.symm.trans hactual)).1
  have hnames : (decl.types.map (fun family => family.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  have htargetEq : (AddInductive.getIIndices stats HS.semantic.traversal.terminal).1 = owner := by
    apply (List.getElem_inj (h₀ := by simpa using htarget')
      (h₁ := by simpa [H.cardinality.records] using howner) hnames).mp
    simpa only [List.getElem_map] using hname
  simpa only [htargetEq] using hvalid

theorem RecursorConstruction.constructorIndices_length
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls)
    (Hindices : List.Forall₂ Rel
      ((HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size).map F) indices) :
    indices.length = (H.declIndexDomains ⟨owner, howner⟩).length := by
  have hvalid := H.constructorTerminalOwner owner howner localIndex hlocal HS
  have harity := checkPositivityStep.isValidIndAppIdx.arity (checkPositivityStep.isValidIndApp?_some hvalid).2
  have hlength := Lean4Lean.List.Forall₂.length_eq Hindices
  simp only [List.length_map, List.length_drop] at hlength
  have hsourceLength : HS.semantic.traversal.terminal.getAppArgsList.length =
      stats.params.size + stats.nindices[owner]! := by
    rw [← Expr.getAppArgs_toList, Array.length_toList]
    exact harity
  rw [hsourceLength] at hlength
  rw [H.sourceIndices_length, H.arities owner howner]
  omega

/-- A typing of the constructor traversal of a minor (`TypedMinorTraversalAt`), chosen once so
that the result indices below are read off a single typing. -/
noncomputable def RecursorConstruction.sourceMinorTyping
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls :=
  Classical.choice (H.minorTyping owner howner localIndex hlocal)

/-- The result indices of a minor's constructor, translated in the source universes over the
unannotated field domains (`declFieldDomains`). -/
noncomputable def RecursorConstruction.declConstructorIndices
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) : List VExpr :=
  Classical.choose (H.constructorResultIndices owner howner localIndex hlocal
    (H.sourceMinorTyping owner howner localIndex hlocal))

theorem RecursorConstruction.sourceConstructorIndices_replay
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let HS := H.sourceMinorTyping owner howner localIndex hlocal
    let domains := H.declFieldDomains owner howner localIndex hlocal
    let indices := H.declConstructorIndices owner howner localIndex hlocal
    let result := VExpr.mkApps
      (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
        (VLevel.params decl.uvars))
      (InductiveSignature.vars stats.params.size S.fields.size ++ indices)
    TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
      ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars)
      (VExpr.wrapForalls domains result) ∧
    R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx (VExpr.wrapForalls domains result) ∧
    List.Forall₂ (TrExprS R.headerVEnv c.lparams
      (abstractForallContext domains (abstractForallContext R.parameterScope.toCtx.reverse [])))
      ((HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size).map fun arg =>
        (arg.abstractList HS.semantic.fieldsRecent.fvars).abstractList H.params.fvars S.fields.size)
      indices :=
  Classical.choose_spec (H.constructorResultIndices owner howner localIndex hlocal
    (H.sourceMinorTyping owner howner localIndex hlocal))

theorem RecursorConstruction.sourceConstructorIndices_length
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (H.declConstructorIndices owner howner localIndex hlocal).length =
      (H.declIndexDomains ⟨owner, howner⟩).length :=
  H.constructorIndices_length owner howner localIndex hlocal
    (H.sourceMinorTyping owner howner localIndex hlocal)
    (H.sourceConstructorIndices_replay owner howner localIndex hlocal).2.2

end Lean4Lean.VerifyInductive

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The constructor type assembled from a minor's unannotated field domains and result indices
is definitionally equal, in the header environment over the parameter scope, to the matching
constructor of the source signature. -/
theorem RecursorConstruction.sourceConstructorDefEq
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    R.headerVEnv.IsDefEqU c.lparams.length R.parameterScope.toCtx
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices))
      (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal)
        (VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (VLevel.params decl.uvars))
          (InductiveSignature.vars stats.params.size S.fields.size ++
            H.declConstructorIndices owner howner localIndex hlocal))) := by
  let HS := H.sourceMinorTyping owner howner localIndex hlocal
  obtain ⟨consumed, Hconsumed, _, Heq⟩ := H.constructorUnannotatedHeaderReplay owner howner localIndex hlocal HS
  have HfixedConsumed := (H.sourceConstructorIndices_replay owner howner localIndex hlocal).1
  have henv := R.headerCheckingAnnotations.1.wf
  have hΔ := R.headerAnonymousParameterWF
  have Hright := Hconsumed.uniq henv (.refl henv hΔ) HfixedConsumed
  simp only [abstractForallContext_toCtx, List.reverse_reverse, VLCtx.toCtx, List.append_nil] at Hright
  have Hctx : OnCtx R.parameterScope.toCtx (R.headerVEnv.IsType c.lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hΔ.toCtx
  exact Heq.trans henv Hctx Hright

end Lean4Lean.VerifyInductive
