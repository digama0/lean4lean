import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorSpine
import Lean4Lean.Verify.Inductive.Recursor.Context.DeclarationUniverses
import Lean4Lean.Verify.Inductive.Recursor.Binders.InductionHypothesisUniverses
import Lean4Lean.Verify.Inductive.Recursor.Signature.MotiveGroup
import Lean4Lean.Verify.Inductive.Recursor.Construction
import Lean4Lean.Verify.Inductive.Recursor.Context.Unannotated

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Opening constructor fields preserves bound-variable closedness of the
remaining telescope. -/
theorem RecursorFieldDecisions.terminalClosed
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (hclosed : Closed source) : Closed terminal := by
  induction H with
  | nil => exact hclosed
  | nonrecursive _ _ ih | recursive _ _ ih =>
    have h := ih
    simp only [Closed] at h
    rw [Expr.instantiate1_eq]
    exact h.2.instantiate1 trivial

theorem RecursorFieldDecisions.consumeClosed
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars))
    (hclosed : Closed source)
    (C : Expr → Expr)
    (hforall : ∀ name dom body bi, C (.forallE name dom body bi) =
      .forallE name (dom.consumeTypeAnnotationsVerified root.env.isTypeAnnotationWrapper) (C body) bi)
    (habstract : ∀ e fv, (C e).abstractN [fv] = C (e.abstractN [fv])) :
    current.lctx.mkForall fields (C terminal) = C source := by
  induction H with
  | nil => exact LocalContext.mkForall_empty _ _
  | @nonrecursive c name dom body bi fields selected positions H _ ih
  | @recursive c name dom body bi fields selected positions target H _ ih =>
    obtain ⟨Hc, HrootC, ⟨Hfields⟩⟩ := H.freshBindings Hroot
    have hbodyScope := (H.currentFVarsIn Hroot hsource).2
    have hbodyFresh : body.FVarsIn (fun fv => fv ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
      apply hbodyScope.mono
      intro fv hfv heq
      subst fv
      exact Hc.current_not_mem hfv
    have hdecl : ∀ fv ∈ Hfields.fvars, ∃ decl, c.lctx.find? fv = some decl := by
      intro fv hf
      obtain ⟨index, name, type, bi, kind, hfind⟩ := Hc.findCDecl fv (Hfields.members fv hf)
      exact ⟨_, hfind⟩
    have hclose := LocalContext.mkForall_append_fresh Hc.wf Hc.currentFind?_eq_none hdecl Hfields.nodup
      (body := C (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) (name := name)
      (type := (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)) (bi := bi)
    have hforallClosed := H.terminalClosed hclosed
    simp only [Closed] at hforallClosed
    have hbodyClose : (C (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))).abstractN [⟨c.ngen.curr⟩] = C body := by
      rw [habstract, Expr.instantiate1_eq, hbodyFresh.abstractN_instantiate1 hforallClosed.2]
    rw [hbodyClose, HrootC.env_eq, ← hforall] at hclose
    rw [HrootC.env_eq]
    have harr : ((Hfields.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]).map Expr.fvar).toArray =
        fields.push (.fvar ⟨c.ngen.curr⟩) := by simp [Hfields.expressions]
    rw [harr, ← Hfields.expressions] at hclose
    exact hclose.trans ih

theorem RecursorFieldDecisions.consumeForallTypes
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars))
    (hclosed : Closed source) :
    current.lctx.mkForall fields
        (Lean4Lean.Expr.consumeForallTypes root.env.isTypeAnnotationWrapper terminal) =
      Lean4Lean.Expr.consumeForallTypes root.env.isTypeAnnotationWrapper source :=
  H.consumeClosed Hroot hsource hclosed
    (Lean4Lean.Expr.consumeForallTypes root.env.isTypeAnnotationWrapper)
    (fun _ _ _ _ => rfl) (fun e fv => Lean4Lean.Expr.abstractN_consumeForallTypes e [fv])

/-- Every minor's constructor traversal starts in the kernel constructor environment. -/
theorem RecursorConstruction.minorRootEnv
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    HS.semantic.traversal.rootContext.env = ctorEnv := by
  have h1 := HS.semantic.fieldsRecent.contextLE.env_eq
  have h2 := (HS.semantic.hypothesesRecent.contextLE.trans
    HS.semantic.extension.contextLE).env_eq
  have h3 := H.localExtends.env_eq
  exact h1.symm.trans (h2.symm.trans h3)

theorem RecursorConstruction.constructorUnannotatedSource
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    (H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars =
      Lean4Lean.Expr.consumeForallTypes ctorEnv.isTypeAnnotationWrapper
        (HS.semantic.traversal.parameterTail.abstractList H.params.fvars) := by
  have hsource : HS.semantic.traversal.parameterTail.FVarsIn
      (fun fv => fv ∈ HS.semantic.traversal.rootContext.lctx.fvars) := by
    apply HS.semantic.parameterScope.mono
    intro fv hfv
    rw [← HS.semantic.rootWF.lctx_eq, HS.semantic.rootWF.mlctx_wf.tr.fvars_eq,
      HS.semantic.parameterSuffix.context, VLCtx.fvars_append]
    exact List.mem_append_right _ hfv
  have hsourceBVar : Closed HS.semantic.traversal.parameterTail := by
    have h := HS.semantic.parameterTranslation.closed
    simpa [HS.semantic.rootWF.mlctx.noBV] using h
  have hclosed := HS.semantic.traversal.decisions.consumeForallTypes
    HS.semantic.rootWF.toBindingContextWF hsource hsourceBVar
  rw [H.minorRootEnv owner howner localIndex hlocal HS] at hclosed
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, _, hvalid, _⟩ :=
    H.minorSources.rows owner howner (by rwa [← H.sourceFamilyCount]) localIndex hlocal
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at hvalid
  obtain ⟨htarget, hvalidIdx⟩ := checkPositivityStep.isValidIndApp?_some hvalid
  have htarget' : (AddInductive.getIIndices stats HS.semantic.traversal.terminal).1 < decl.types.length := by
    rwa [H.cardinality.families] at htarget
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalidIdx (H.validStats.indConstAt htarget')
  have hterminal : Lean4Lean.Expr.consumeForallTypes ctorEnv.isTypeAnnotationWrapper HS.semantic.traversal.terminal =
      HS.semantic.traversal.terminal := by
    have hterminalConst (e : Expr) (name : Name) (levels : List Level)
        (hhead : e.getAppFn = .const name levels) : Lean4Lean.Expr.consumeForallTypes ctorEnv.isTypeAnnotationWrapper e = e := by
      cases e <;> simp_all [Lean4Lean.Expr.consumeForallTypes, Expr.getAppFn]
    exact hterminalConst _ _ _ hhead
  rw [hterminal, HS.semantic.traversal_fields] at hclosed
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have hcontext := HS.semantic.fieldsRecent.toFVarArrayIn.mkForall_mono Hext
    HS.semantic.traversal.terminal
  dsimp only
  rw [hcontext, hclosed, Lean4Lean.Expr.abstractList_consumeForallTypes]

/-- Abstracting the header's cached parameters (`CachedParameterDecl`) turns a translation
over the parameter scope into a translation of the closed expression over the anonymous
parameter context `abstractForallContext`. -/
theorem TrExprS.abstractCachedParameters {scope : VLCtx}
    (Hcached : List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
      params.toList.reverse scope)
    (Hparams : FVarArrayIn root params) (hnd : Hparams.fvars.Nodup)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us (abstractForallContext scope.toCtx.reverse [])
      (source.abstractList Hparams.fvars) target := by
  have hparamExprs : params.toList.reverse = Hparams.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList Hparams.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  rw [hparamExprs, List.forall₂_map_left_iff] at Hcached
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type))
      Hparams.fvars.reverse scope :=
    Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have Hclosed := TrExprS.abstractFVarLambdaSuffix (domains := []) Hdecls
    (List.nodup_reverse.mpr hnd) (by simpa [abstractForallContext] using Htr)
  simpa using Hclosed

theorem RecursorConstruction.constructorRawSourceReplay
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
      (HS.semantic.traversal.parameterTail.abstractList H.params.fvars)
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) := by
  obtain ⟨traversal, htraversal, _, _, _, Hraw⟩ := H.minorSourceReplay owner howner
    (by rwa [← H.sourceFamilyCount]) localIndex hlocal
    (H.sourceMinorOffsetBound owner howner localIndex hlocal)
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at Hraw
  have Hcached := R.recursorHeaders.parameterSuffix.cached
  have hscope : R.recursorHeaders.parameterSuffix.parameterDecls = R.parameterScope :=
    R.recursorHeaders_parameterScope
  rw [hscope] at Hcached
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  exact TrExprS.abstractCachedParameters Hcached H.params hparams
    Hraw

/-- The header environment is a checking environment, and the type-annotation wrappers
recognized by the constructor environment are definitions of the header environment, since
the constructor stage adds only constructors. -/
theorem RecursorInput.headerCheckingAnnotations
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    CheckingEnv c.safety R.headerEnv R.headerVEnv ∧
      TypeAnnotationWrappers R.headerEnv ctorEnv.isTypeAnnotationWrapper := by
  refine ⟨R.headers.context.checking, .of_reflect _ _ fun {n v} hfind => ?_⟩
  rcases R.find?_headerOrigin hfind with h | h
  · exact h
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨_, _, h⟩ := List.mem_map.mp h
    cases h

theorem RecursorInput.headerAnonymousParameterWF
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VLCtx.WF R.headerVEnv c.lparams.length
      (abstractForallContext R.parameterScope.toCtx.reverse []) := by
  have Hparams := R.statsWF.paramsContext
  rw [R.checkedParameterScope] at Hparams
  have Hctx := abstractForallContext.isDefEq
    (right := R.parameterScope.toCtx.reverse) (by simpa using Hparams)
  exact (Hctx.symm R.headerCheckingAnnotations.1.wf.orderedStrong).wf

/-- Each constructor type of the source signature is a type in the header environment, over
the parameter scope. -/
theorem RecursorInput.sourceConstructorTailType
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (index : Fin decl.ownedConstructors.length) :
    let ctor := R.sourceSignatureConstructor index
    R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
      (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
        (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) := by
  obtain ⟨_, _, _, tailTarget, _, _, _, _, _, ⟨_, htail⟩, _, htype⟩ := R.sourceSignatureConstructor_replay index
  have Htype := htail.isType
  rw [sourceConstructor_tail_eq htype] at Htype
  exact Eq.mp (congrArg (fun u => R.headerVEnv.IsType u R.parameterScope.toCtx
    (VExpr.wrapForalls (R.sourceSignature.fieldTypes (R.sourceSignatureConstructor index))
      (R.sourceSignature.familyApp (R.sourceSignatureConstructor index).owner
        (VLevel.params R.sourceSignature.uvars)
        (InductiveSignature.vars R.sourceSignature.params.length (R.sourceSignatureConstructor index).fields.length)
        (R.sourceSignatureConstructor index).indices))) R.statsWF.uvars.symm) Htype

/-- The executable field telescope of a minor's constructor traversal, ending in its terminal
family application and abstracted over the parameters, translates in the header environment
to a type definitionally equal to the matching source signature constructor type. -/
theorem RecursorConstruction.constructorUnannotatedHeaderReplay
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (HS : TypedMinorTraversalAt H.recursorWF
      (H.origins.minorShapes owner howner localIndex hlocal) H.parameterSuffix.parameterDecls) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
    ∃ consumed,
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        ((H.localContext.lctx.mkForall S.fields HS.semantic.traversal.terminal).abstractList H.params.fvars) consumed ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx consumed ∧
      R.headerVEnv.IsDefEqU c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
          (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
            (InductiveSignature.vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) consumed := by
  have Hraw := H.constructorRawSourceReplay owner howner localIndex hlocal HS
  have Htype := R.sourceConstructorTailType
    ⟨recursorMinorOffset indTypes owner + localIndex, H.sourceMinorOffsetBound owner howner localIndex hlocal⟩
  have hctx : (abstractForallContext R.parameterScope.toCtx.reverse []).toCtx = R.parameterScope.toCtx := by
    simp [abstractForallContext_toCtx, VLCtx.toCtx]
  rw [← hctx] at Htype
  obtain ⟨consumed, Hconsumed, HconsumedType, Heq⟩ := Hraw.consumeForallTypes_of_wrappers
    R.headerCheckingAnnotations.1 R.headerCheckingAnnotations.2 R.headerAnonymousParameterWF Htype
  rw [← H.constructorUnannotatedSource owner howner localIndex hlocal HS] at Hconsumed
  exact ⟨consumed, Hconsumed, by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HconsumedType,
    by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Heq⟩

end Lean4Lean.VerifyInductive

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem MLCtxOnlyLams.mkForall_fvarsIn_upset
    (H : MLCtxOnlyLams m) (Hwf : m.WF env Us)
    (n : Nat) (hn : n ≤ m.length) (body : Expr)
    (Hup : IsFVarUpSet (fun fv => fv ∈ m.fvarRevList n hn ∨ P fv) m.vlctx)
    (Hbody : body.FVarsIn (fun fv => fv ∈ m.fvarRevList n hn ∨ P fv)) :
    (m.mkForall n hn body).FVarsIn P := by
  induction n generalizing m body with
  | zero => simpa using Hbody
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlet fv name type value type' value' tail => exact H.vlet_false.elim
    | vlam fv name type type' bi tail =>
      have htail := Nat.le_of_succ_le_succ hn
      have hnot := Hwf.1.tr.find?_eq_none.mp Hwf.2.1
      let Q := fun other => other ∈ tail.fvarRevList n htail ∨ P other
      have HupTail : IsFVarUpSet Q tail.vlctx := by
        apply (IsFVarUpSet.congr Hwf.1.tr.wf.fvwf (P := fun other => other = fv ∨ Q other) (Q := Q) ?_).mp
          (by simpa [TypeChecker.MLCtx.fvarRevList, Q, List.mem_cons, or_assoc] using Hup.1)
        intro other hother
        have hne : other ≠ fv := by intro heq; subst other; exact hnot hother
        simp [hne]
      have Htype : type.FVarsIn Q := by
        apply fvarsIn_iff.mpr
        refine ⟨?_, Hwf.2.2.1.fvarsIn.mono (fun _ _ => trivial)⟩
        intro other hother
        have hP := Hup.2 (by simp) other hother
        have hmem := (fvarsIn_iff.mp Hwf.2.2.1.fvarsIn).1 other hother
        have hne : other ≠ fv := by intro heq; subst other; exact hnot hmem
        simpa [Q, TypeChecker.MLCtx.fvarRevList, hne] using hP
      apply ih H.tail_vlam Hwf.1 htail _ HupTail
      constructor
      · exact Htype
      · apply FVarsIn.abstract1_of
        simpa [TypeChecker.MLCtx.fvarRevList, Q, List.mem_cons, or_assoc] using Hbody

/-- A translation in the recursor-checking environment at the source universe parameters, over
the source parameter scope, lifts to the recursor's universe parameters and parameter context,
with the target instantiated at the recursor's universe levels. -/
theorem RecursorConstruction.liftDeclUnivType
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (Hsource : TrExprS R.context.venv c.lparams
      (abstractForallContext R.parameterScope.toCtx.reverse []) source target) :
    TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
      (target.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) := by
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have Hidentity := Hsource.substLevelParamsCore
      (Us := c.lparams) (F := Level.param) (ls := VLevel.params c.lparams.length)
      R.sourceAnonymousParameterWF (fun level hlevel => VLevel.params_wf hlevel)
      (fun u u' hu => by
        simpa [Level.substParams_id, VLevel.inst_id (VLevel.WF.of_ofLevel hu)] using hu)
    rw [Expr.instantiateLevelParamsCore_id] at Hidentity
    rw [H.parameterAnonymousContext, H.recursorEnv, recursorDeclarationAbstractLevels_zero H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams] using Hidentity
  · have hfresh : fresh ∉ c.lparams := by
      simpa [helim, AddInductive.AdmissibleElimLevel] using H.elimLevelAdmissible
    have Hrec := Hsource.prependLevelParam R.context.checking.tr.wf R.sourceAnonymousParameterWF hfresh
    rw [H.parameterAnonymousContext, H.recursorEnv, recursorDeclarationAbstractLevels_param H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams] using Hrec

/-- The executable field telescope of a minor (closed with `Prop`, abstracted over the
parameters) translates in the header environment to some `sourceDomains`, which form a type,
and translates at the recursor's universe parameters to `sourceDomains` instantiated at the
recursor's universe levels. The domains are read in the header environment, before the
block's constructors exist. -/
theorem RecursorConstruction.sourceFieldDomains
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (_hsourceOwner : owner < indTypes.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (_hindex : recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let source := (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars
    ∃ sourceDomains, sourceDomains.length = S.fields.size ∧
      TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls sourceDomains (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          (sourceDomains.map (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) := by
  obtain ⟨HS⟩ := H.minorTyping owner howner localIndex hlocal
  obtain ⟨target, Htr, _⟩ := H.constructorUnannotatedHeaderReplay owner howner localIndex hlocal HS
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  let Hbound := HS.semantic.fieldsRecent.toFVarArrayIn.mono Hext
  have Htel := (Hbound.mkForall_forallTelescope H.localWF HS.semantic.traversal.terminal).abstractList H.params.fvars
  obtain ⟨domains, result, hlen, heq, _⟩ := TrExprS.forallTelescope_shape_with_context Htel Htr
  rw [heq] at Htr
  obtain ⟨Hprefix, HprefixType⟩ := TrExprS.forallDomainsOnly Htel hlen Htr
  rw [Expr.forallDomainsOnly_abstractList,
    Hbound.forallDomainsOnly H.localWF HS.semantic.fieldsRecent.nodup] at Hprefix
  refine ⟨domains, hlen, Hprefix, ?_, ?_⟩
  · simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HprefixType
  · simpa [VExpr.instL_wrapForalls, VExpr.instL, VLevel.inst] using
      H.liftDeclUnivType (Hprefix.mono (R.headerLE.trans R.ctorLE))

end Lean4Lean.VerifyInductive

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The field domains of the constructor of a minor, chosen by `sourceFieldDomains` in the
header environment, in the source universes and parameter scope. -/
noncomputable def RecursorConstruction.declFieldDomains
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) : List VExpr :=
  Classical.choose (H.sourceFieldDomains owner howner (by rwa [← H.sourceFamilyCount])
    localIndex hlocal (H.sourceMinorOffsetBound owner howner localIndex hlocal))

theorem RecursorConstruction.sourceFields_length
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (H.declFieldDomains owner howner localIndex hlocal).length =
      (H.origins.minorShapes owner howner localIndex hlocal).fields.size :=
  (Classical.choose_spec (H.sourceFieldDomains owner howner (by rwa [← H.sourceFamilyCount])
    localIndex hlocal (H.sourceMinorOffsetBound owner howner localIndex hlocal))).1

theorem RecursorConstruction.sourceFields_headerReplay
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let source := (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars
    TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal) (.sort .zero)) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal) (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          ((H.declFieldDomains owner howner localIndex hlocal).map
            (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) :=
  (Classical.choose_spec (H.sourceFieldDomains owner howner (by rwa [← H.sourceFamilyCount])
    localIndex hlocal (H.sourceMinorOffsetBound owner howner localIndex hlocal))).2

theorem RecursorConstruction.sourceFields_replay
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let source := (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars
    TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal) (.sort .zero)) ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal) (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          ((H.declFieldDomains owner howner localIndex hlocal).map
            (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) := by
  obtain ⟨Hsource, Htype, Hrec⟩ := H.sourceFields_headerReplay owner howner localIndex hlocal
  have Hle := R.headerLE.trans R.ctorLE
  exact ⟨Hsource.mono Hle, Htype.mono Hle, Hrec⟩

end Lean4Lean.VerifyInductive
