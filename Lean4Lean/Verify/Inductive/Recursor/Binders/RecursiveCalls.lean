import Lean4Lean.Verify.Inductive.Recursor.Binders.MotivesAndIndices
import Lean4Lean.Verify.Inductive.Recursor.Binders.MotiveFrames

/-! Typing of the motive frames and recursive calls of the recursor construction:
the generated motive telescope of each family and its agreement with the
executable motive (`motiveDecl`, `resultTyping` of the motive pass), the
refinement of `loopUArgs` to a recursive-domain judgment, and the recursive-call
syntax (`RecursiveCall`) and typing (`TypedRecursiveCall`) used by the rules. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem mlctx_fvarRevList_eq_take (c : TypeChecker.MLCtx) (n : Nat)
    (hn : n ≤ c.length) : c.fvarRevList n hn = c.vlctx.fvars.take n := by
  have h := c.fvarRevList_prefix (n := n) (hn := hn)
  rw [List.prefix_iff_eq_take] at h
  simpa using h

theorem checkInductiveTypes.loopType.FrontFVLift.fvars_take
    (H : checkInductiveTypes.loopType.FrontFVLift sourceDomains
      expandedDomains scope expanded shift) :
    scope.fvars.take sourceDomains.length =
      expanded.fvars.take sourceDomains.length := by
  induction H with
  | zero => simp
  | cons fv deps indexType _ H ih =>
    simp [VLCtx.fvars_cons_some, ih]

/-- Close a major-premise motive body over the most recent checker
declarations.  Everything happens in the checker `MLCtx`, so no translation
in the executable context is restricted. -/
theorem RecursorContextWF.scopedMotiveClosure
    {c : AddInductive.Context} {U : List Name}
    (R : RecursorContextWF c U) (n : Nat) (hn : n ≤ R.chk.length)
    (indices : Array Expr)
    (hxs : indices.toList.reverse = (R.chk.fvarRevList n hn).map Expr.fvar)
    {majorTy : Expr} {C₀ : VExpr}
    (hC : TrExprS R.venv U R.chk.vlctx majorTy C₀)
    (hCty : R.venv.IsType U.length R.chk.vlctx.toCtx C₀)
    {l : Level} {u : VLevel} (hl : VLevel.ofLevel U l = some u) :
    TrExprS R.venv U (R.chk.dropN n hn).vlctx
        (c.lctx.mkForall indices (.forallE `t majorTy (.sort l) .default))
        (R.chk.mkForall' n hn (.forallE C₀ (.sort u))) ∧
      R.venv.IsType U.length (R.chk.dropN n hn).vlctx.toCtx
        (R.chk.mkForall' n hn (.forallE C₀ (.sort u))) := by
  have henv := R.checking.tr.wf
  have hsortTy : R.venv.IsType U.length (C₀ :: R.chk.vlctx.toCtx) (.sort u) :=
    ⟨.succ u, VEnv.HasType.sort (.of_ofLevel hl)⟩
  have hbody : TrExprS R.venv U R.chk.vlctx
      (.forallE `t majorTy (.sort l) .default) (.forallE C₀ (.sort u)) :=
    .forallE hCty hsortTy hC (.sort hl)
  have hbodyTy : R.venv.IsType U.length R.chk.vlctx.toCtx
      (.forallE C₀ (.sort u)) := VEnv.IsType.forallE hCty hsortTy
  have hclosed : Closed (Expr.forallE `t majorTy (.sort l) .default) := by
    simpa [TypeChecker.MLCtx.noBV] using hbody.closed
  have hsrc := R.check.wf.mkForall_eq n hn hxs hclosed
  have hidx : indices =
      (((R.chk.fvarRevList n hn).reverse).map Expr.fvar).toArray := by
    apply Array.ext'
    have h := congrArg List.reverse hxs
    simpa [List.map_reverse] using h
  have hmem : ∀ fv ∈ (R.chk.fvarRevList n hn).reverse,
      ∃ d, c.checkLCtx.find? fv = some d := by
    intro fv hfv
    rw [← R.check.lctx_eq]
    exact R.check.wf.tr.find?_eq_some.2
      ((TypeChecker.MLCtx.fvarRevList_prefix _).subset (List.mem_reverse.mp hfv))
  have hsub := R.checkSub.mkForall_eq hmem
    (Expr.forallE `t majorTy (.sort l) .default)
  rw [← hidx] at hsub
  rw [hsub]
  have hlctx : c.checkLCtx.mkForall indices
      (Expr.forallE `t majorTy (.sort l) .default) =
      R.chk.lctx.mkForall indices
        (Expr.forallE `t majorTy (.sort l) .default) :=
    congrArg (fun lc : LocalContext => lc.mkForall indices _) R.check.lctx_eq.symm
  rw [hlctx, hsrc]
  exact R.check.wf.mkForall_trS henv hbody hbodyTy n hn

namespace mkRecInfos.loopInd1

/-- The application of family `dIdx` to all of its parameter and
index variables (a bvar spine) splits as the application to the parameter
variables, lifted over the indices, applied to the index variables. -/
theorem canonicalFamilyApp_split
    {base : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {baseDepth : Nat}
    {stats : AddInductive.InductiveStats} {source : InductiveType}
    {dIdx : Nat} {elimLevel : Level}
    {Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel}
    (Hheader : mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl
      baseDepth source dIdx)
    {env : VEnv} {Us : List Name} {scope : VLCtx} {narrowTarget : VExpr}
    {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        env Us (Hheader.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    {indices : Array Expr} (hindicesSize : indices.size = nindices)
    (harity : (indices.size == stats.nindices[dIdx]!) = true) :
    VExpr.mkApps
      (.const Hheader.target.name (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim))
      (mkRecInfos.loopArgs1.indexBVarSpine
        (decl.nparams + Hheader.target.numIndices)) =
      VExpr.mkApps
        ((VExpr.mkApps
          ((VExpr.const Hheader.target.name
            (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
              Hsynthesis.params.length 0)
          (bvarSpine Hsynthesis.params.length)).liftN
            Hsynthesis.indices.length 0)
        (bvarSpine Hsynthesis.indices.length) := by
  have hp : Hsynthesis.params.length = decl.nparams :=
    Hsynthesis.parameterCount.trans Hheader.parameterCount
  have hn : Hsynthesis.indices.length =
      Hheader.target.numIndices := by
    have hguard : indices.size = stats.nindices[dIdx]! := by
      simpa using harity
    have hfam : stats.nindices[dIdx]! =
        Hheader.target.numIndices := by
      simp [Array.getElem!_eq_getD, Hheader.indexCount]
    rw [Hsynthesis.indexCount]
    omega
  have hsplit := VExpr.mkApps_bvarSpine_add
    (.const Hheader.target.name
      (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim))
    Hsynthesis.params.length Hsynthesis.indices.length
  have hcv : mkRecInfos.loopArgs1.indexBVarSpine
      (decl.nparams + Hheader.target.numIndices) =
      bvarSpine
        (Hsynthesis.params.length + Hsynthesis.indices.length) := by
    rw [hp, hn]; rfl
  rw [hcv]
  simpa [VExpr.liftN] using hsplit

/-- Rebuilding the motive of family `dIdx` in the checker context of
the index loop and closing it over the indices translates it in the
parameter scope `motiveSourceScope` below those indices, to a type that is
definitionally equal to the generated motive telescope of the family. -/
theorem motiveSourceReplay
    {base current cIndices : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {baseDepth : Nat}
    {stats : AddInductive.InductiveStats} {source : InductiveType}
    {dIdx : Nat} {elimLevel : Level}
    {Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel}
    (Hheader : mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl
      baseDepth source dIdx)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams)}
    (Rindices : RecursorContextWF cIndices
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henvIndices : Rindices.venv = Hbase.venv)
    {narrowTarget : VExpr} {scope : VLCtx} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Rindices.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (Hheader.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (HnarrowStats : RecursorValidAppStatsWF Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope Rindices.mlctx.vlctx)
    (hfront : Hruntime.frontSourceDomains = Hsynthesis.indices)
    (halign : VLCtx.IsDefEq Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      scope Rindices.chk.vlctx)
    (HnarrowIndices : List.Forall₂ (TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) scope)
      indices.toList indexTargets)
    (hindexCount : indexTargets.length = nindices)
    (hcanonical :
      indexTargets = mkRecInfos.loopArgs1.indexBVarSpine nindices)
    (Hrecent : RecursorFVarSuffix R Rindices indices)
    (harity : (indices.size == stats.nindices[dIdx]!) = true)
    {resultLevel : VLevel}
    (hresultLevel : VLevel.ofLevel
      (AddInductive.getRecLevelParams elimLevel base.lparams) elimLevel =
        some resultLevel)
    {motiveSourceScope : VLCtx}
    (hsourceScope : scope.drop Hsynthesis.indices.length = motiveSourceScope)
    (hsourceCtx : VLCtx.toCtx motiveSourceScope = Hsynthesis.params.reverse) :
    ∃ motiveSourceTarget,
      TrExprS Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        motiveSourceScope
        (cIndices.lctx.mkForall indices
          (.forallE `t
            ((mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
              indices).consumeTypeAnnotationsVerified
                cIndices.env.isTypeAnnotationWrapper)
            (.sort elimLevel) .default))
        motiveSourceTarget ∧
      Rindices.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        (VLCtx.toCtx motiveSourceScope) motiveSourceTarget ∧
      Rindices.venv.IsDefEqU
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        (VLCtx.toCtx motiveSourceScope) motiveSourceTarget
        (VExpr.wrapForalls Hsynthesis.indices
          (.forallE
            (VExpr.mkApps
              ((VExpr.mkApps
                ((VExpr.const Hheader.target.name
                  (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
                    Hsynthesis.params.length 0)
                (bvarSpine Hsynthesis.params.length)).liftN
                  Hsynthesis.indices.length 0)
              (bvarSpine Hsynthesis.indices.length))
            (.sort resultLevel))) ∧
      motiveSourceScope.WF Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length := by
  have hindicesSize : indices.size = nindices := by
    have hlength :=
      List.Forall₂.length_eq HnarrowIndices
    simpa [hindexCount] using hlength
  have hfrontLength : Hruntime.frontSourceDomains.length =
      indices.size := by
    rw [hfront, Hsynthesis.indexCount, ← hindicesSize]
  have henvR := Rindices.checking.tr.wf
  have hmainTake : (Rindices.mlctx.fvarRevList indices.size
      Hrecent.size_le) = Rindices.mlctx.vlctx.fvars.take indices.size :=
    mlctx_fvarRevList_eq_take _ _ _
  have hfrontTake := Hruntime.front.fvars_take
  rw [hfrontLength] at hfrontTake
  have hchkTake : Rindices.chk.vlctx.fvars.take indices.size =
      Rindices.mlctx.vlctx.fvars.take indices.size := by
    rw [← halign.fvars, hfrontTake, Hruntime.context.fvars]
  have hnChk : indices.size ≤ Rindices.chk.length := by
    have hlen := congrArg List.length hchkTake
    simp only [List.length_take] at hlen
    have h1 : Rindices.mlctx.vlctx.fvars.length = Rindices.mlctx.length :=
      Rindices.onlyLams.fvars_length
    have h2 : Rindices.chk.vlctx.fvars.length = Rindices.chk.length :=
      Rindices.check.onlyLams.fvars_length
    have hmainLen := Hrecent.size_le
    omega
  have hxsChk : indices.toList.reverse =
      (Rindices.chk.fvarRevList indices.size hnChk).map Expr.fvar := by
    rw [mlctx_fvarRevList_eq_take, hchkTake, ← hmainTake]
    exact Hrecent.reverse_eq
  have HfamNarrow :=
    Hheader.recursorScopedFamilyApplication Helim
      Rindices Hsynthesis HnarrowStats HnarrowIndices
      hindexCount hcanonical harity henvIndices
  obtain ⟨famChk, HfamChk⟩ := HfamNarrow.1.defeqDFC henvR halign
  have HfamChkEq := HfamNarrow.1.uniq henvR halign HfamChk
  have HfamChkType : Rindices.venv.IsType
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      Rindices.chk.vlctx.toCtx famChk :=
    (HfamNarrow.2.2.defeqU_l henvR halign.wf.toCtx HfamChkEq).defeqDFC
      henvR.ordered halign.defeqCtx
  rcases hconsume _ _ Rindices.atCheckLCtx HfamChk HfamChkType with
    ⟨majorChk, HmajorChk⟩
  have HmotiveChk := Rindices.scopedMotiveClosure indices.size hnChk
    indices hxsChk HmajorChk.unannotated HmajorChk.isType
    hresultLevel
  have hdropAlign : VLCtx.IsDefEq Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      motiveSourceScope (Rindices.chk.dropN indices.size hnChk).vlctx := by
    rw [Rindices.check.onlyLams.vlctx_dropN, ← hsourceScope,
      Hsynthesis.indexCount, ← hindicesSize]
    exact halign.drop indices.size
  obtain ⟨motiveSourceTarget, HmotiveSourceTr⟩ :=
    HmotiveChk.1.defeqDFC henvR (hdropAlign.symm henvR.orderedStrong)
  have HmotiveSourceEq := HmotiveChk.1.uniq henvR
    (hdropAlign.symm henvR.orderedStrong) HmotiveSourceTr
  have HmotiveSourceType : Rindices.venv.IsType
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      (VLCtx.toCtx motiveSourceScope) motiveSourceTarget :=
    (HmotiveChk.2.defeqU_l henvR (hdropAlign.symm henvR.orderedStrong).wf.toCtx
      HmotiveSourceEq).defeqDFC henvR.ordered
        (hdropAlign.symm henvR.orderedStrong).defeqCtx
  have hsplitK := canonicalFamilyApp_split Hheader Hsynthesis hindicesSize
    harity
  have hscopeWF := halign.wf.toCtx
  have hFK := HfamChkEq
  rw [hsplitK] at hFK
  have hfamMajor : Rindices.venv.IsDefEqU
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      scope.toCtx famChk majorChk := by
    rcases HmajorChk.source_defeq with ⟨w, hw⟩
    exact ⟨_, hw.defeqDFC henvR.ordered
      (halign.defeqCtx.symm henvR.ordered)⟩
  have hdomK := hFK.trans henvR hscopeWF hfamMajor
  have HKty := HfamNarrow.2.2
  rw [hsplitK] at HKty
  obtain ⟨vK, hKty⟩ := HKty
  have hdomK' := hdomK.of_l henvR hscopeWF hKty
  have HbodyK := VEnv.IsDefEq.forallEDF hdomK'
    (VEnv.HasType.sort (.of_ofLevel hresultLevel))
  have hnScope : indices.size ≤ scope.toCtx.length := by
    rw [Hsynthesis.scopeCtx]
    simp [Hsynthesis.indexCount, hindicesSize]
  obtain ⟨_, hclose⟩ := VEnv.IsDefEqCtx.closeHeads halign.defeqCtx
    indices.size hnScope HbodyK
  have hscopeTake : (scope.toCtx.take indices.size).reverse =
      Hsynthesis.indices := by
    rw [Hsynthesis.scopeCtx, hindicesSize.trans Hsynthesis.indexCount.symm]
    simp
  have hscopeDrop : scope.toCtx.drop indices.size =
      VLCtx.toCtx motiveSourceScope := by
    rw [hsourceCtx, Hsynthesis.scopeCtx,
      hindicesSize.trans Hsynthesis.indexCount.symm]
    simp
  have hchkTakeCtx : (Rindices.chk.vlctx.toCtx.take indices.size).reverse =
      MLCtxForallDomains Rindices.chk indices.size hnChk :=
    (Rindices.check.onlyLams.forallDomains_eq_take_reverse _ _).symm
  rw [hscopeTake, hscopeDrop, hchkTakeCtx,
    ← TypeChecker.MLCtx.mkForall'_eq_wrapForalls] at hclose
  have HmotiveSourceCanonical : Rindices.venv.IsDefEqU
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      (VLCtx.toCtx motiveSourceScope) motiveSourceTarget
      (VExpr.wrapForalls Hsynthesis.indices
        (.forallE
          (VExpr.mkApps
            ((VExpr.mkApps
              ((VExpr.const Hheader.target.name
                (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
                  Hsynthesis.params.length 0)
              (bvarSpine Hsynthesis.params.length)).liftN
                Hsynthesis.indices.length 0)
            (bvarSpine Hsynthesis.indices.length))
          (.sort resultLevel))) := by
    have hNT := HmotiveSourceEq.defeqDFC henvR.ordered
      (hdropAlign.symm henvR.orderedStrong).defeqCtx
    exact hNT.symm.trans henvR hdropAlign.wf.toCtx ⟨_, hclose.symm⟩
  exact ⟨motiveSourceTarget, HmotiveSourceTr, HmotiveSourceType,
    HmotiveSourceCanonical, hdropAlign.wf⟩

/-- Every free variable of the motive type of family `dIdx`, built
over its indices and major premise, lies in the parameter scope below those
indices. -/
theorem motiveSourceFVars
    {base current cIndices : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {baseDepth : Nat}
    {stats : AddInductive.InductiveStats} {source : InductiveType}
    {dIdx : Nat} {elimLevel : Level}
    {Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel}
    (Hheader : mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl
      baseDepth source dIdx)
    {R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams)}
    (Rindices : RecursorContextWF cIndices
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henvIndices : Rindices.venv = Hbase.venv)
    {narrowTarget : VExpr} {scope : VLCtx} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Rindices.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (Hheader.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (HnarrowStats : RecursorValidAppStatsWF Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope Rindices.mlctx.vlctx)
    (hfront : Hruntime.frontSourceDomains = Hsynthesis.indices)
    (HnarrowIndices : List.Forall₂ (TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) scope)
      indices.toList indexTargets)
    (hindexCount : indexTargets.length = nindices)
    (Hrecent : RecursorFVarSuffix R Rindices indices)
    (Hframe : RecursorMotiveFrameWF Rindices stats dIdx indices elimLevel) :
    let majorTy :=
      ((mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified
          cIndices.env.isTypeAnnotationWrapper)
    let lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t majorTy
      .default
    (lctx.mkForall indices
      (lctx.mkForall #[.fvar ⟨cIndices.ngen.curr⟩] (.sort elimLevel))).FVarsIn
      (· ∈ VLCtx.fvars (scope.drop Hruntime.frontSourceDomains.length)) := by
  intro majorTy _
  have hindicesSize : indices.size = nindices := by
    have hlength :=
      List.Forall₂.length_eq HnarrowIndices
    simpa [hindexCount] using hlength
  let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
    Hframe.majorTr Hframe.majorType
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
      majorTy .default }
  let major := Expr.fvar ⟨cIndices.ngen.curr⟩
  let motiveTy := cMajor.lctx.mkForall indices <|
    cMajor.lctx.mkForall #[major] <| .sort elimLevel
  let majorBody := cMajor.lctx.mkForall #[major] (.sort elimLevel)
  have HnarrowFamily :=
    (Hheader.recursorScopedFamilyPrefixTranslation Helim Rindices
      Hsynthesis HnarrowStats henvIndices).1
  have HnarrowIndexFVars : ∀ arg ∈ indices.toList,
      arg.FVarsIn (· ∈ scope.fvars) := by
    have go : ∀ {sources targets : List _},
        List.Forall₂ (TrExprS Rindices.venv
          (AddInductive.getRecLevelParams elimLevel base.lparams)
          scope) sources targets →
        ∀ arg ∈ sources, arg.FVarsIn (· ∈ scope.fvars) := by
      intro sources targets Htranslated arg harg
      induction Htranslated with
      | nil => simp at harg
      | cons Hhead Htail ih =>
        simp only [List.mem_cons] at harg
        rcases harg with rfl | harg
        · exact Hhead.fvarsIn
        · exact ih harg
    exact go HnarrowIndices
  have HmajorRawFVars :
      (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
        indices).FVarsIn (· ∈ scope.fvars) := by
    rw [Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    refine ⟨HnarrowFamily.fvarsIn, ?_⟩
    exact HnarrowIndexFVars
  have HmajorTyFVars : majorTy.FVarsIn (· ∈ scope.fvars) := by
    exact Expr.consumeTypeAnnotationsVerified_fvarsIn HmajorRawFVars
  rcases Helim.sortType (env := Rindices.venv) (Δ := scope) with
    ⟨narrowSortLevel, HsortNarrow, _HsortNarrowType⟩
  have hone : 1 ≤ Rmajor.mlctx.length := by
    dsimp only [Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
    simp
  have hmajorRecent : #[major].toList.reverse =
      (Rmajor.mlctx.fvarRevList 1 hone).map Expr.fvar := by
    dsimp only [major, Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
    simp
  have hmajorConcrete : majorBody =
      Rmajor.mlctx.mkForall 1 hone (.sort elimLevel) := by
    dsimp only [majorBody]
    rw [← Rmajor.lctx_eq]
    exact Rmajor.mlctx_wf.mkForall_eq 1 hone hmajorRecent trivial
  have HmajorBodyFVars : majorBody.FVarsIn
      (· ∈ scope.fvars) := by
    rw [hmajorConcrete]
    have HsortAbstract :
        (Expr.abstract1 ⟨cIndices.ngen.curr⟩
          (.sort elimLevel)).FVarsIn (· ∈ scope.fvars) := by
      apply FVarsIn.abstract1_of
      exact HsortNarrow.fvarsIn.mono fun _ h => Or.inr h
    simpa only [Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.mkForall] using
      (show (Expr.forallE `t majorTy
          (Expr.abstract1 ⟨cIndices.ngen.curr⟩ (.sort elimLevel))
          .default).FVarsIn
          (· ∈ scope.fvars) from
        ⟨HmajorTyFVars, HsortAbstract⟩)
  let hmajorLE := BindingContextLE.withLocalDecl cIndices
    Rindices.toBindingContextWF `t majorTy .default
  have hmotiveConcrete : motiveTy =
      cIndices.lctx.mkForall indices majorBody := by
    dsimp [motiveTy, majorBody]
    exact Hrecent.toFVarArrayAfter.toFVarArrayIn.mkForall_mono
      hmajorLE _
  have hmotiveMkForall : motiveTy =
      Rindices.mlctx.mkForall indices.size Hrecent.size_le
        majorBody := by
    rw [hmotiveConcrete, ← Rindices.lctx_eq]
    exact Rindices.mlctx_wf.mkForall_eq indices.size Hrecent.size_le
      Hrecent.reverse_eq
      (hmajorConcrete ▸ Rmajor.mlctx_wf.mkForall_closed 1 hone trivial)
  have hfrontLength : Hruntime.frontSourceDomains.length =
      indices.size := by
    rw [hfront, Hsynthesis.indexCount, ← hindicesSize]
  have hfrontLE : Hruntime.frontSourceDomains.length ≤
      Rindices.mlctx.length := by
    rw [hfrontLength]
    exact Hrecent.size_le
  have HmotiveSourceFVarsAtBase : motiveTy.FVarsIn
      (· ∈ VLCtx.fvars
        (scope.drop Hruntime.frontSourceDomains.length)) := by
    rw [hmotiveMkForall]
    simpa only [hfrontLength] using
      Hruntime.front.mkForall_fvarsIn_sourceBase
        Rindices.onlyLams Rindices.mlctx_wf Hruntime.context
        hfrontLE majorBody HmajorBodyFVars
  exact HmotiveSourceFVarsAtBase

/-- The generated, permutation-free motive telescope of family `dIdx`, over
the parameter and index domains of its checked header.  Its
parameter domains are those of `Hsynthesis`, and its motive type is the
index telescope closed over the major premise. -/
theorem canonicalMotiveTelescope
    {base cIndices : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {baseDepth : Nat}
    {stats : AddInductive.InductiveStats} {source : InductiveType}
    {dIdx : Nat} {elimLevel : Level}
    {Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel}
    (Hheader : mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl
      baseDepth source dIdx)
    (Rindices : RecursorContextWF cIndices
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henvIndices : Rindices.venv = Hbase.venv)
    {narrowTarget : VExpr} {scope : VLCtx} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Rindices.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (Hheader.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (HnarrowStats : RecursorValidAppStatsWF Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope stats decl nindices)
    (HnarrowIndices : List.Forall₂ (TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) scope)
      indices.toList indexTargets)
    (hindexCount : indexTargets.length = nindices)
    (hcanonical :
      indexTargets = mkRecInfos.loopArgs1.indexBVarSpine nindices)
    (harity : (indices.size == stats.nindices[dIdx]!) = true)
    (info : AddInductive.RecInfo) (hinfo : info.indices = indices)
    (resultLevel : VLevel) :
    ∃ C : ClosedMotiveTelescope Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        stats decl dIdx info elimLevel,
      C.params = Hsynthesis.params ∧
      C.motiveType = VExpr.wrapForalls Hsynthesis.indices
        (.forallE
          (VExpr.mkApps
            ((VExpr.mkApps
              ((VExpr.const Hheader.target.name
                (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
                  Hsynthesis.params.length 0)
              (bvarSpine Hsynthesis.params.length)).liftN
                Hsynthesis.indices.length 0)
            (bvarSpine Hsynthesis.indices.length))
          (.sort resultLevel)) := by
  subst hinfo
  have hindicesSize : info.indices.size = nindices := by
    have hlength :=
      List.Forall₂.length_eq HnarrowIndices
    simpa [hindexCount] using hlength
  have htargetLt : dIdx < decl.types.length :=
    (List.getElem?_eq_some_iff.mp Hheader.targetAt).1
  have htargetEq : decl.types[dIdx] = Hheader.target := by
    have htargetAt := Hheader.targetAt
    rw [List.getElem?_eq_getElem htargetLt] at htargetAt
    exact Option.some.inj htargetAt
  have hcanonicalLevelTranslation : stats.levels.mapM
      (VLevel.ofLevel
        (AddInductive.getRecLevelParams elimLevel base.lparams)) =
      some (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim) := by
    cases elimLevel with
    | zero =>
      simpa [mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels,
        mkRecInfos.loopArgs1.MotivePassHeaderAt.abstractLevels,
        AddInductive.getRecLevelParams] using
        Hheader.checked.levelTranslation
    | param fresh =>
      have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim
        Hheader.checked.levelTranslation
      simpa [mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels,
        mkRecInfos.loopArgs1.MotivePassHeaderAt.abstractLevels,
        AddInductive.getRecLevelParams] using hshifted
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
      simp [AddInductive.AdmissibleElimLevel] at Helim
  refine ⟨{
    target_lt := htargetLt
    params := Hsynthesis.params
    indices := Hsynthesis.indices
    levels := mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim
    family := VExpr.mkApps
      ((VExpr.const Hheader.target.name
        (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
          Hsynthesis.params.length 0)
      (bvarSpine Hsynthesis.params.length)
    familyResult := narrowTarget
    motiveType := VExpr.wrapForalls Hsynthesis.indices
      (.forallE
        (VExpr.mkApps
          ((VExpr.mkApps
            ((VExpr.const Hheader.target.name
              (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
                Hsynthesis.params.length 0)
            (bvarSpine Hsynthesis.params.length)).liftN
              Hsynthesis.indices.length 0)
          (bvarSpine Hsynthesis.indices.length))
        (.sort resultLevel))
    resultLevel := resultLevel
    params_length := Hsynthesis.parameterCount
    indices_length := Hsynthesis.indexCount.trans hindicesSize.symm
    levels_length := by
      rw [htargetEq]
      exact Hheader.recursorAbstractLevels_length Helim
    levels_wf := Hheader.recursorAbstractLevels_wf Helim
    levels_translation := hcanonicalLevelTranslation
    family_eq := by rw [htargetEq]
    motiveType_eq := rfl
    family_typing :=
      Hheader.recursorCanonicalFamilyPrefix Helim Rindices Hsynthesis
        henvIndices
    familyApplicationType := by
      have Hfamily :=
        (Hheader.recursorScopedFamilyApplication Helim
          Rindices Hsynthesis HnarrowStats HnarrowIndices
          hindexCount hcanonical harity henvIndices).2.2
      rw [canonicalFamilyApp_split Hheader Hsynthesis hindicesSize harity]
        at Hfamily
      simpa [Hsynthesis.scopeCtx, VExpr.liftN] using Hfamily
    telescope :=
      RecursorMotiveTelescope.wrapForalls Hsynthesis.indices
        (VExpr.mkApps
          ((VExpr.const Hheader.target.name
            (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim)).liftN
              Hsynthesis.params.length 0)
          (bvarSpine Hsynthesis.params.length))
        narrowTarget resultLevel }, rfl, rfl⟩

/-- Once the major premise and then the motive of a frame have been
declared, the unannotated motive type is the binder telescope over
the frame's indices and major premise read in the extended local context. -/
theorem motiveTypeShape
    {cIndices : AddInductive.Context} {recLparams : List Name}
    {stats : AddInductive.InductiveStats} {dIdx : Nat}
    {indices : Array Expr} {elimLevel : Level}
    (Rindices : RecursorContextWF cIndices recLparams)
    (Hframe : RecursorMotiveFrameWF Rindices stats dIdx indices elimLevel)
    (Hbound : FVarArrayIn cIndices indices) (motiveName : Name) :
    let majorTy :=
      ((mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified
          cIndices.env.isTypeAnnotationWrapper)
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
        majorTy .default }
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[.fvar ⟨cIndices.ngen.curr⟩] <| .sort elimLevel
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩ motiveName
        (motiveTy.consumeTypeAnnotationsVerified
          cIndices.env.isTypeAnnotationWrapper) .default }
    motiveTy.consumeTypeAnnotationsVerified
        cIndices.env.isTypeAnnotationWrapper =
      cMotive.lctx.mkForall indices
        (cMotive.lctx.mkForall #[.fvar ⟨cIndices.ngen.curr⟩]
          (.sort elimLevel)) := by
  intro majorTy cMajor motiveTy cMotive
  let major := Expr.fvar ⟨cIndices.ngen.curr⟩
  let hMajorFrame := BindingContextLE.withLocalDecl cIndices
    Rindices.toBindingContextWF `t majorTy .default
  let hMotiveFrame := BindingContextLE.withLocalDecl cMajor
    (Rindices.toBindingContextWF.withLocalDecl
      `t majorTy .default)
    motiveName (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default
  let HindicesAtMajor : FVarArrayIn cMajor indices :=
    Hbound.mono hMajorFrame
  let HmajorAtMajor : FVarArrayIn cMajor #[major] := by
    simpa [cMajor, major] using
      (FVarArrayIn.empty cIndices).pushCurrent
        `t majorTy .default
  have hsourceShape : (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) =
      cMajor.lctx.mkForall indices
        (cMajor.lctx.mkForall #[major] (.sort elimLevel)) := by
    change (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) = motiveTy
    exact Hframe.motiveSourceEq
  calc
    (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) =
        cMajor.lctx.mkForall indices
          (cMajor.lctx.mkForall #[major] (.sort elimLevel)) :=
      hsourceShape
    _ = cMotive.lctx.mkForall indices
          (cMajor.lctx.mkForall #[major] (.sort elimLevel)) :=
      (HindicesAtMajor.mkForall_mono hMotiveFrame _).symm
    _ = cMotive.lctx.mkForall indices
          (cMotive.lctx.mkForall #[major] (.sort elimLevel)) :=
      congrArg (fun body => cMotive.lctx.mkForall indices body)
        (HmajorAtMajor.mkForall_mono hMotiveFrame _).symm

/-- The scope below the indices of an executable index front is
the parameter scope `P`: it has no bound variables, its typing context is the
abstract parameter telescope, and its literal weakening is definitionally
equal to the executable context with those indices dropped. -/
theorem motiveSourceScopeFacts
    {cIndices : AddInductive.Context} {recLparams : List Name}
    (Rindices : RecursorContextWF cIndices recLparams)
    {skeleton : VInductiveTypeSkeleton} {narrowTarget : VExpr}
    {scope P : VLCtx} {nparams nindices : Nat} {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Rindices.venv recLparams skeleton scope narrowTarget nparams nindices)
    (hscopeBase : scope.drop nindices = P)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding Rindices.venv
      recLparams scope Rindices.mlctx.vlctx)
    (hfront : Hruntime.frontSourceDomains = Hsynthesis.indices)
    (hindicesSize : indices.size = nindices)
    (hsize : indices.size ≤ Rindices.mlctx.length)
    {motiveSourceScope motiveSourceExpanded : VLCtx}
    (hmotiveSourceScope :
      scope.drop Hruntime.frontSourceDomains.length = motiveSourceScope)
    (hmotiveSourceExpanded :
      Hruntime.expanded.drop Hruntime.frontExpandedDomains.length =
        motiveSourceExpanded) :
    scope.drop Hsynthesis.indices.length = motiveSourceScope ∧
      motiveSourceScope = P ∧
      VLCtx.NoBV motiveSourceScope ∧
      VLCtx.toCtx motiveSourceScope = Hsynthesis.params.reverse ∧
      VLCtx.IsDefEq Rindices.venv recLparams.length motiveSourceExpanded
        (Rindices.mlctx.dropN indices.size hsize).vlctx := by
  have hfrontSourceLength : Hruntime.frontSourceDomains.length =
      indices.size := by
    rw [hfront, Hsynthesis.indexCount, ← hindicesSize]
  have hfrontExpandedLength : Hruntime.frontExpandedDomains.length =
      indices.size := by
    rw [← Hruntime.front.length_eq, hfrontSourceLength]
  have hmotiveSourceScope' :
      scope.drop Hsynthesis.indices.length = motiveSourceScope := by
    simpa [hfront] using hmotiveSourceScope
  refine ⟨hmotiveSourceScope', ?_, ?_, ?_, ?_⟩
  · rw [← hmotiveSourceScope', Hsynthesis.indexCount]
    exact hscopeBase
  · change VLCtx.bvars motiveSourceScope = 0
    rw [← hmotiveSourceScope', ← hfront]
    rw [Hruntime.front.sourceBaseBVars]
    exact Hruntime.noBV
  · have hdecomposition := Hruntime.front.sourceContext
    rw [hfront, Hsynthesis.scopeCtx, hmotiveSourceScope'] at hdecomposition
    exact List.append_inj_right hdecomposition.symm rfl
  · have Hdrop := Hruntime.context.drop indices.size
    rw [← Rindices.onlyLams.vlctx_dropN indices.size hsize] at Hdrop
    have hexpandedDrop : Hruntime.expanded.drop indices.size =
        motiveSourceExpanded := by
      simpa [hfrontExpandedLength] using hmotiveSourceExpanded
    change VLCtx.IsDefEq Rindices.venv recLparams.length
      (Hruntime.expanded.drop indices.size)
      (Rindices.mlctx.dropN indices.size hsize).vlctx at Hdrop
    rw [hexpandedDrop] at Hdrop
    exact Hdrop

/-- Weakening past the freshly declared major premise: the frame's motive
target is definitionally equal to the weakening of every type that is
definitionally equal to the closed motive telescope reopened over the
indices. -/
theorem motiveTargetDefEqAfterMajor
    {cIndices : AddInductive.Context} {recLparams : List Name}
    {stats : AddInductive.InductiveStats} {dIdx : Nat}
    {indices : Array Expr} {elimLevel : Level}
    {Rindices : RecursorContextWF cIndices recLparams}
    (Hframe : RecursorMotiveFrameWF Rindices stats dIdx indices elimLevel)
    {T : VExpr}
    (H : Rindices.venv.IsDefEqU recLparams.length Rindices.mlctx.vlctx.toCtx
      ((VExpr.wrapForalls Hframe.indexDomains
        (.forallE Hframe.majorTarget (.sort Hframe.resultLevel))).liftN
          indices.size 0) T) :
    let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
      Hframe.majorTr Hframe.majorType
    Rmajor.venv.IsDefEqU recLparams.length Rmajor.mlctx.vlctx.toCtx
      Hframe.motiveTarget
      (T.lift' ((RecursorContextExtension.withLocalDecl (name := `t)
        (bi := .default) Rindices Hframe.majorTr Hframe.majorType).shift.consN
          0)) := by
  intro _
  let HmajorExtension :=
    RecursorContextExtension.withLocalDecl (name := `t)
      (bi := .default) Rindices
      Hframe.majorTr Hframe.majorType
  have hmajorLift (expression : VExpr) :
      expression.liftN 1 0 =
        expression.lift' (HmajorExtension.shift.consN 0) := by
    change expression.liftN 1 0 =
      expression.lift' ((Lift.skip .refl).consN 0)
    rw [← Lift.skipN_one, VExpr.lift'_consN_skipN]
  rw [Hframe.motiveTarget_eq, hmajorLift]
  exact HmajorExtension.weakDefEqU H

/-- The motive data `MotiveDecl` for family `dIdx`, established once its major
premise and motive have been opened over the index telescope.  It
lives over the recursor context extended by both new declarations, and
its generated parameter domains are aligned with the shared recursor
parameter context of `Hsuffix`. -/
theorem motiveDecl
    {base current cIndices : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {baseDepth runtimeDepth : Nat}
    {stats : AddInductive.InductiveStats} {source : InductiveType}
    {dIdx : Nat} {elimLevel : Level}
    {Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel}
    (Hheader : mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl
      baseDepth source dIdx)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams)}
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (Hroot : BindingContextLE base current)
    (Rindices : RecursorContextWF cIndices
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henvIndices : Rindices.venv = Hbase.venv)
    {narrowTarget : VExpr} {scope : VLCtx} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Rindices.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (Hheader.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (hcanonicalParams :
      Hsynthesis.params.reverse = Hsuffix.parameterDecls.toCtx)
    (hscopeBase : scope.drop nindices = Hsuffix.parameterDecls)
    (HnarrowStats : RecursorValidAppStatsWF Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope Rindices.mlctx.vlctx)
    (hfront : Hruntime.frontSourceDomains = Hsynthesis.indices)
    (halign : VLCtx.IsDefEq Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      scope Rindices.chk.vlctx)
    (HnarrowIndices : List.Forall₂ (TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) scope)
      indices.toList indexTargets)
    (hindexCount : indexTargets.length = nindices)
    (hcanonical :
      indexTargets = mkRecInfos.loopArgs1.indexBVarSpine nindices)
    (Hbound : FVarArrayIn cIndices indices)
    (Hrecent : RecursorFVarSuffix R Rindices indices)
    (hindexUniverses :
      (cIndices.lctx.mkForall indices (.sort .zero)).levelParamsIn
        base.lparams = true)
    (harity : (indices.size == stats.nindices[dIdx]!) = true)
    (Hframe : RecursorMotiveFrameWF Rindices stats dIdx indices elimLevel)
    (motiveName : Name) :
    ∃ S : MotiveDecl
        ((Rindices.withLocalDecl (name := `t) (bi := .default)
          Hframe.majorTr Hframe.majorType).withLocalDecl
            (name := motiveName) (bi := .default)
            Hframe.motiveTr Hframe.motiveType)
        stats decl dIdx
        { motive := .fvar ⟨cIndices.ngen.next.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ }
        elimLevel,
      VEnv.IsDefEqCtx Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        [] S.canonical.params.reverse Hsuffix.parameterDecls.toCtx := by
  have hindicesSize : indices.size = nindices := by
    have hlength :=
      List.Forall₂.length_eq HnarrowIndices
    simpa [hindexCount] using hlength
  rcases Hheader.recursorMotiveTypeDefEq Helim Rindices
      Hsynthesis HnarrowStats Hruntime HnarrowIndices hcanonical
      Hbound henvIndices hindicesSize hfront Hframe with
    ⟨Hcanonical, HmotiveCanonical, HmotiveCanonicalClosed,
      hcanonicalMotiveReopen, hcanonicalMotiveBody⟩
  let majorTy :=
    ((mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
      indices).consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper)
  let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
    Hframe.majorTr Hframe.majorType
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
      majorTy .default }
  let major := Expr.fvar ⟨cIndices.ngen.curr⟩
  let motiveTy := cMajor.lctx.mkForall indices <|
    cMajor.lctx.mkForall #[major] <| .sort elimLevel
  let Rmotive := Rmajor.withLocalDecl (name := motiveName)
    (bi := .default) Hframe.motiveTr Hframe.motiveType
  let cMotive : AddInductive.Context := { cMajor with
    ngen := cMajor.ngen.next
    lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩ motiveName
      (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default }
  let hIndices := Hrecent.contextLE
  let hMajorFrame := BindingContextLE.withLocalDecl cIndices
    Rindices.toBindingContextWF `t majorTy .default
  let hMotiveFrame := BindingContextLE.withLocalDecl cMajor
    (Rindices.toBindingContextWF.withLocalDecl
      `t majorTy .default)
    motiveName (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default
  let hAllFrames : BindingContextLE current cMotive :=
    hIndices.trans (hMajorFrame.trans hMotiveFrame)
  let HindicesAtMajor : FVarArrayIn cMajor indices :=
    Hbound.mono hMajorFrame
  let HmajorAtMajor : FVarArrayIn cMajor #[major] := by
    simpa [cMajor, major] using
      (FVarArrayIn.empty cIndices).pushCurrent
        `t majorTy .default
  have hnewMotiveShape := motiveTypeShape Rindices Hframe Hbound motiveName
  let nextInfo : AddInductive.RecInfo := {
    motive := .fvar ⟨cMajor.ngen.curr⟩
    minors := #[]
    indices
    major }
  have hnewMotiveShape' : (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) =
      cMotive.lctx.mkForall nextInfo.indices
        (cMotive.lctx.mkForall #[nextInfo.major]
          (.sort elimLevel)) := by
    change (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) =
      cMotive.lctx.mkForall indices
        (cMotive.lctx.mkForall #[major] (.sort elimLevel))
    exact hnewMotiveShape
  let HmajorExtension :=
    RecursorContextExtension.withLocalDecl (name := `t)
      (bi := .default) Rindices
      Hframe.majorTr Hframe.majorType
  let HmotiveExtension :=
    RecursorContextExtension.withLocalDecl (name := motiveName)
      (bi := .default) Rmajor
      Hframe.motiveTr Hframe.motiveType
  have HmotiveTypeDefEqMajor' :=
    motiveTargetDefEqAfterMajor Hframe HmotiveCanonical
  have htargetLt : dIdx < decl.types.length :=
    (List.getElem?_eq_some_iff.mp Hheader.targetAt).1
  have htargetEq : decl.types[dIdx] = Hheader.target := by
    have htargetAt := Hheader.targetAt
    rw [List.getElem?_eq_getElem htargetLt] at htargetAt
    exact Option.some.inj htargetAt
  have hseedIndexCount : indices.size =
      (decl.types[dIdx]'htargetLt).numIndices := by
    rw [htargetEq]
    have hguard : indices.size = stats.nindices[dIdx]! := by
      simpa using harity
    exact hguard.trans (by
      simp [Array.getElem!_eq_getD, Hheader.indexCount])
  let HindicesAtMotive : FVarArrayIn cMotive indices :=
    Hbound.mono (hMajorFrame.trans hMotiveFrame)
  let HmajorAtMotiveBound : FVarArrayIn cMotive #[major] :=
    HmajorAtMajor.mono hMotiveFrame
  rcases Hframe.motiveClosed with
    ⟨hclosedSize, motiveClosedTarget, HmotiveClosedTr,
      HmotiveClosedType, hmotiveClosedTarget⟩
  let majorBody := cMajor.lctx.mkForall #[major] (.sort elimLevel)
  have hone : 1 ≤ Rmajor.mlctx.length := by
    dsimp only [Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
    simp
  have hmajorRecent : #[major].toList.reverse =
      (Rmajor.mlctx.fvarRevList 1 hone).map Expr.fvar := by
    dsimp only [major, Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
    simp
  have hmajorConcrete : majorBody =
      Rmajor.mlctx.mkForall 1 hone (.sort elimLevel) := by
    dsimp only [majorBody]
    rw [← Rmajor.lctx_eq]
    exact Rmajor.mlctx_wf.mkForall_eq 1 hone hmajorRecent trivial
  let hmajorLE := BindingContextLE.withLocalDecl cIndices
    Rindices.toBindingContextWF `t majorTy .default
  have hmotiveConcrete : motiveTy =
      cIndices.lctx.mkForall indices majorBody := by
    dsimp [motiveTy, majorBody]
    exact Hrecent.toFVarArrayAfter.toFVarArrayIn.mkForall_mono
      hmajorLE _
  have HmotiveSourceFVarsAtBase := motiveSourceFVars Hheader Rindices
    henvIndices Hsynthesis HnarrowStats Hruntime hfront HnarrowIndices
    hindexCount Hrecent Hframe
  have HmotiveClosedTrSeed : TrExprS Rmotive.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      (Rindices.mlctx.dropN indices.size hclosedSize).vlctx
      (cMotive.lctx.mkForall nextInfo.indices
        (cMotive.lctx.mkForall #[nextInfo.major]
          (.sort elimLevel))) motiveClosedTarget := by
    rw [← hnewMotiveShape']
    change TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      (Rindices.mlctx.dropN indices.size hclosedSize).vlctx
      (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) motiveClosedTarget
    simpa only [motiveTy, cMajor] using HmotiveClosedTr
  rcases Hruntime.front.base with
    ⟨motiveSourceScope, motiveSourceExpanded, motiveSourceShift,
      hmotiveSourceScope, hmotiveSourceExpanded, hmotiveSourceShift,
      HmotiveSourceLift⟩
  obtain ⟨hmotiveSourceScope', hmotiveSourceParameterScope,
      HmotiveSourceNoBV, hmotiveSourceScopeCtx, HmotiveSourceContext⟩ :=
    motiveSourceScopeFacts Rindices Hsynthesis hscopeBase Hruntime hfront
      hindicesSize hclosedSize hmotiveSourceScope hmotiveSourceExpanded
  have HmotiveSourceFVarsNarrow : motiveTy.FVarsIn
      (· ∈ VLCtx.fvars motiveSourceScope) := by
    rw [← hmotiveSourceScope']
    simpa [hfront] using HmotiveSourceFVarsAtBase
  -- The motive rebuilt in the checker context of the index loop.
  obtain ⟨motiveSourceTarget, HmotiveSourceTr, HmotiveSourceType,
      HmotiveSourceCanonical, HmotiveSourceWF⟩ :=
    motiveSourceReplay Hheader hconsume Rindices henvIndices Hsynthesis
      HnarrowStats Hruntime hfront halign HnarrowIndices hindexCount
      hcanonical Hrecent harity Hframe.resultLevelOf hmotiveSourceScope'
      hmotiveSourceScopeCtx
  have hmajorBodyShape : cMajor.lctx.mkForall #[major] (.sort elimLevel) =
      .forallE `t majorTy (.sort elimLevel) .default := by
    change majorBody = _
    rw [hmajorConcrete]
    simp [Rmajor, RecursorContextWF.withLocalDecl,
      TypeChecker.MLCtx.mkForall, Expr.abstract1]
    try rfl
  have hmotiveSourceShape :
      cMotive.lctx.mkForall nextInfo.indices
        (cMotive.lctx.mkForall #[nextInfo.major] (.sort elimLevel)) =
      cIndices.lctx.mkForall indices
        (.forallE `t majorTy (.sort elimLevel) .default) := by
    have hsourceShape : motiveTy.consumeTypeAnnotationsVerified
        cIndices.env.isTypeAnnotationWrapper = motiveTy :=
      Hframe.motiveSourceEq
    rw [← hnewMotiveShape', hsourceShape, ← hmajorBodyShape]
    exact hmotiveConcrete
  obtain ⟨Ccanonical, hCparams, hCmotive⟩ := canonicalMotiveTelescope Hheader
    Rindices henvIndices Hsynthesis HnarrowStats HnarrowIndices hindexCount
    hcanonical harity nextInfo rfl Hframe.resultLevel
  have HparamsSelf : VEnv.IsDefEqCtx Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      Ccanonical.params.reverse Hsynthesis.params.reverse := by
    rw [hCparams]
    exact VEnv.IsDefEqCtx.refl (OnCtx.of_append (by
      rw [← Hsynthesis.scopeCtx]
      exact Hsynthesis.scopeWF.toCtx))
  let Hseed : MotiveDecl Rmotive stats decl dIdx
      nextInfo elimLevel := {
    canonical := Ccanonical
    target_lt := htargetLt
    indexCount := hseedIndexCount
    family := (Hframe.familyTarget.lift'
      (HmajorExtension.shift.consN 0)).lift'
        (HmotiveExtension.shift.consN 0)
    familyActualType :=
      (Hcanonical.familyType.lift'
        (HmajorExtension.shift.consN 0)).lift'
          (HmotiveExtension.shift.consN 0)
    familyType :=
      (Hcanonical.familyType.lift'
        (HmajorExtension.shift.consN 0)).lift'
          (HmotiveExtension.shift.consN 0)
    motiveActualType :=
      Hframe.motiveTarget.lift' (HmotiveExtension.shift.consN 0)
    motiveType :=
      (Hcanonical.motiveType.lift'
        (HmajorExtension.shift.consN 0)).lift'
          (HmotiveExtension.shift.consN 0)
    resultLevel := Hframe.resultLevel
    indexUniverses := by
      change (cMotive.lctx.mkForall indices (.sort .zero)).levelParamsIn
        cIndices.lparams = true
      rw [Hbound.mkForall_mono
        (HmajorExtension.contextLE.trans HmotiveExtension.contextLE),
        (Hroot.trans hIndices).lparams_eq]
      exact hindexUniverses
    motiveClosedScope :=
      (Rindices.mlctx.dropN indices.size hclosedSize).vlctx
    motiveClosedAmbient := Hsuffix.ambientDecls
    motiveParameterScope := Hsuffix.parameterDecls
    motiveClosedContext := by
      change (Rindices.mlctx.dropN indices.size hclosedSize).vlctx =
        Hsuffix.ambientDecls ++ Hsuffix.parameterDecls
      rw [show hclosedSize = Hrecent.size_le from rfl,
        Hrecent.drop_eq]
      exact Hsuffix.context
    motiveParameterAlignment := hcanonicalParams ▸ HparamsSelf
    motiveParameterDecls := Hsuffix.cached
    motiveSourceScope := motiveSourceScope
    motiveSourceExpanded := motiveSourceExpanded
    motiveSourceShift := motiveSourceShift
    motiveSourceAlignment := hmotiveSourceScopeCtx ▸ HparamsSelf
    motiveSourceParameterScope := hmotiveSourceParameterScope
    motiveSourceLift := HmotiveSourceLift
    motiveSourceContext := HmotiveSourceContext
    motiveSourceNoBV := HmotiveSourceNoBV
    motiveSourceFVars := by
      rw [← hnewMotiveShape', Hframe.motiveSourceEq]
      exact HmotiveSourceFVarsNarrow
    motiveSourceTarget := motiveSourceTarget
    motiveSourceTr := by
      rw [hmotiveSourceShape]
      exact HmotiveSourceTr
    motiveSourceType := HmotiveSourceType
    motiveSourceCanonical := hCmotive ▸ HmotiveSourceCanonical
    motiveSourceWF := HmotiveSourceWF
    motiveClosedTarget := motiveClosedTarget
    motiveClosedTr := HmotiveClosedTrSeed
    motiveClosedType := HmotiveClosedType
    motiveClosedCanonicalTarget :=
      VExpr.wrapForalls Hruntime.frontExpandedDomains
        (.forallE Hframe.majorSourceTarget
          (.sort Hframe.resultLevel))
    motiveClosedCanonicalEq := by
      rw [hCmotive]
      let canonicalBody := VExpr.forallE
        (VExpr.mkApps
          ((VExpr.mkApps
            (.const Hheader.target.name
              (mkRecInfos.loopArgs1.MotivePassHeaderAt.recursorAbstractLevels base.lparams Helim))
            (bvarSpine Hsynthesis.params.length)).liftN
              Hsynthesis.indices.length 0)
          (bvarSpine Hsynthesis.indices.length))
        (.sort Hframe.resultLevel)
      have Hclose := Hruntime.front.closeAtBase motiveSourceShift
        hmotiveSourceShift canonicalBody
      have hbody := hcanonicalMotiveBody
      dsimp only at hbody
      rw [hfront, hbody] at Hclose
      simpa [canonicalBody, VExpr.liftN] using Hclose
    motiveClosedCanonicalDefEq := by
      change Rindices.venv.IsDefEqU
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        (Rindices.mlctx.dropN indices.size hclosedSize).vlctx.toCtx
        motiveClosedTarget
        (VExpr.wrapForalls Hruntime.frontExpandedDomains
          (.forallE Hframe.majorSourceTarget
            (.sort Hframe.resultLevel)))
      rw [Rindices.onlyLams.toCtx_dropN indices.size hclosedSize]
      rw [hmotiveClosedTarget]
      exact HmotiveCanonicalClosed
    motiveReopenedCanonicalTarget :=
      (((VExpr.wrapForalls Hruntime.frontExpandedDomains
        (.forallE Hframe.majorSourceTarget
          (.sort Hframe.resultLevel))).liftN indices.size 0).lift'
            (HmajorExtension.shift.consN 0)).lift'
              (HmotiveExtension.shift.consN 0)
    motiveTypeCanonicalEq := by
      rw [hcanonicalMotiveReopen]
    familyTr := HmotiveExtension.weakTrExprS
      (HmajorExtension.weakTrExprS Hframe.familyTr)
    familyTyping := HmotiveExtension.weakHasType
      (HmajorExtension.weakHasType Hcanonical.familyTyping)
    familyTypeDefEq := ⟨_, Classical.choose_spec
      ((HmotiveExtension.weakHasType
        (HmajorExtension.weakHasType Hcanonical.familyTyping)).isType
          Rmotive.checking.tr.wf Rmotive.mlctx_wf.tr.wf.toCtx)⟩
    indicesBound := HindicesAtMotive
    majorBound := HmajorAtMotiveBound
    motiveTypeTr := by
      rw [← hnewMotiveShape']
      exact HmotiveExtension.weakTrExprS Hframe.motiveTr
    motiveTypeDefEq := HmotiveExtension.weakDefEqU HmotiveTypeDefEqMajor'
    telescope := (Hcanonical.telescope.lift'
      (HmajorExtension.shift.consN 0)).lift'
        (HmotiveExtension.shift.consN 0) }
  have HseedParams0 :
      VEnv.IsDefEqCtx Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        [] Hseed.canonical.params.reverse
          Hsuffix.parameterDecls.toCtx :=
    hcanonicalParams ▸ HparamsSelf
  exact ⟨Hseed, HseedParams0⟩

/-- Typing for the motive pass of `mkRecInfos`.  In addition
to the binder facts of `resultBindings`, every
family is opened against its checked header under the common
recursor universe list, and the index/major/motive binder-type rows
remain translated and typed after all later mutual frames. -/
theorem resultTyping {alpha : Type} {Q : alpha → Prop}
    {base current : AddInductive.Context} (Hbase : ContextWF base)
    {decl : VInductDecl} {baseDepth runtimeDepth : Nat}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (Hheaders : ∀ i (hi : i < indTypes.size),
      mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl
        baseDepth indTypes[i] i)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (HparamsCtx : ∀ i (hi : i < indTypes.size),
      VEnv.IsDefEqCtx R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length []
        ((Hheaders i hi).recursorParams Helim).reverse
        Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      R.mlctx.vlctx stats decl runtimeDepth)
    (Hbindings : RecInfoBindings current recInfos)
    (Horigins : RecInfoBinderTypes current recInfos)
    (HmajorTypes : TrBinderTypes R Horigins.majorTypes)
    (HmajorShapes : MajorPremiseTypes stats recInfos Horigins.majorTypes
      current.env.isTypeAnnotationWrapper)
    (HmotiveTypes : TrBinderTypes R Horigins.motiveTypes)
    (HmotiveShapes : MotiveTypes current recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl
      Hsuffix.parameterDecls.toCtx recInfos elimLevel)
    (HindexTypeRows :
      TrBinderTypesPerFamily R Horigins.indexTypes)
    (Hparams : FVarArrayIn current stats.params)
    (HnoAlias : RecInfoBindings.NoAlias stats.params recInfos)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE base current)
    (hprogress : recInfos.size = dIdx)
    (Harities : RecInfoArities stats recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hblueprints : RecInfoTemplateCounts recInfos)
    (hparamU : ParameterUniverseSupport current stats.params)
    (HindexTraces : IndexTelescopeRuns stats indTypes current recInfos)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (_henvOut : Rout.venv = Hbase.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (_hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (_HstatsOut : RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rout.mlctx.vlctx stats decl outDepth)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoBinderTypes outCtx out),
      TrBinderTypes Rout HoriginsOut.majorTypes →
      MajorPremiseTypes stats out HoriginsOut.majorTypes
        outCtx.env.isTypeAnnotationWrapper →
      TrBinderTypes Rout HoriginsOut.motiveTypes →
      MotiveTypes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl
        HsuffixOut.parameterDecls.toCtx out elimLevel →
      TrBinderTypesPerFamily Rout HoriginsOut.indexTypes →
      (HparamsOut : FVarArrayIn outCtx stats.params) →
      RecInfoBindings.NoAlias stats.params out →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      RecInfoMinorsEmpty out →
      RecInfoTemplateCounts out →
      BindingContextLE base outCtx →
      out.size = recInfos.size + (indTypes.size - dIdx) →
      IndexTelescopeRuns stats indTypes outCtx out →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k current).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) current).WF
        (fun c' => c' = current) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context)
      hread fun ctx hctx => ?_
    subst ctx
    let Hheader := Hheaders dIdx hidx
    let loopK : Array Expr → AddInductive.M alpha := fun indices => do
      unless indices.size == stats.nindices[dIdx]! do
        throw <| .other
          "recursor index arity does not match checked inductive header"
      let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
      AddInductive.withUnannotatedLocalDecl `t .default tTy fun major => do
      let lctx ← getLCtx
      let motiveTy := lctx.mkForall indices <|
        lctx.mkForall #[major] <| .sort elimLevel
      let name := if indTypes.size > 1 then
        (`motive).appendIndexAfter (dIdx + 1) else `motive
      AddInductive.withUnannotatedLocalDecl name .default motiveTy fun motive =>
      AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel (dIdx + 1)
        (recInfos.push { motive, minors := #[], indices, major }) k
    change ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
        AddInductive.M Expr) { current with checkLCtx := {} } >>= fun normalized =>
      (AddInductive.paramCheckLCtx stats stats.params.size >>= fun L =>
        AddInductive.withCheckLCtx L
          (AddInductive.mkRecInfos.loopArgs1 stats normalized 0 #[]
            current.fuel.inductiveFuel loopK)) current).WF Q
    refine Hheader.startRecursorTyping Helim R hconsume henv
      Hsuffix (HparamsCtx dIdx hidx) Hstats hparamU Hroot.lparams_eq
      loopK ?_ current.fuel.inductiveFuel
    · intro cIndices nextDepth Rindices henvIndices HsuffixIndices
        hparameterDecls type
        fullTarget narrowTarget scope nindices indices indexOrigins
        indexTargets Hsynthesis hcanonicalParams hscopeBase HnarrowStats HstatsIndices Hruntime
        hfront halign htypeNarrow htypeFVars htypeFull htypeFullType Hindices
        HnarrowIndices hindexCount hcanonical HindexOrigins HindexTypes
        Hrecent hindexUniverses HindexTrace
      by_cases harity : (indices.size == stats.nindices[dIdx]!) = true
      · simp only [loopK]
        rw [if_pos harity]
        rcases Hheader.recursorFrame Helim R Rindices Hsynthesis
            HnarrowStats Hruntime HnarrowIndices hindexCount hcanonical
            harity henvIndices hconsume Hrecent with ⟨Hframe⟩
        let majorTy :=
          ((mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
            indices).consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper)
        refine withLocalDecl.recursorWF (name := `t) (bi := .default)
          Rindices Hframe.majorTr Hframe.majorType ?_
        let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
          Hframe.majorTr Hframe.majorType
        let HsuffixMajor := HsuffixIndices.withAmbient
          (name := `t) (bi := .default) Hframe.majorTr Hframe.majorType
        let HstatsMajor := HstatsIndices.withFVar Rmajor.checking.tr.wf
          Rmajor.mlctx_wf.tr.wf
        let cMajor : AddInductive.Context := { cIndices with
          ngen := cIndices.ngen.next
          lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
            majorTy .default }
        have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
            (fun lctx => lctx = cMajor.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        let major := Expr.fvar ⟨cIndices.ngen.curr⟩
        let motiveTy := cMajor.lctx.mkForall indices <|
          cMajor.lctx.mkForall #[major] <| .sort elimLevel
        let motiveName := if indTypes.size > 1 then
          (`motive).appendIndexAfter (dIdx + 1) else `motive
        refine withLocalDecl.recursorWF (name := motiveName) (bi := .default)
          Rmajor Hframe.motiveTr Hframe.motiveType ?_
        let Rmotive := Rmajor.withLocalDecl (name := motiveName)
          (bi := .default) Hframe.motiveTr Hframe.motiveType
        let HsuffixMotive := HsuffixMajor.withAmbient
          (name := motiveName) (bi := .default)
          Hframe.motiveTr Hframe.motiveType
        let HstatsMotive := HstatsMajor.withFVar Rmotive.checking.tr.wf
          Rmotive.mlctx_wf.tr.wf
        have HmajorAtIndices := HmajorTypes.weakenRecent Hrecent
        have HmotiveAtIndices := HmotiveTypes.weakenRecent Hrecent
        have HindexRowsAtIndices := HindexTypeRows.weakenRecent Hrecent
        let HmajorAtMotive :=
          (HmajorAtIndices.push (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).withLocalDecl
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HmotiveAtMotive :=
          (HmotiveAtIndices.withLocalDecl (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).push
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HindexRowsAtMotive :=
          (HindexRowsAtIndices.withLocalDecl (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).withLocalDecl
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HindexTypesAtMotive :=
          (HindexTypes.withLocalDecl (name := `t) (bi := .default)
            Hframe.majorTr Hframe.majorType).withLocalDecl
              (name := motiveName) (bi := .default)
              Hframe.motiveTr Hframe.motiveType
        let HindexRows' := HindexRowsAtMotive.push HindexTypesAtMotive
        let cMotive : AddInductive.Context := { cMajor with
          ngen := cMajor.ngen.next
          lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩ motiveName
            (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default }
        let hIndices := Hrecent.contextLE
        let hMajorFrame := BindingContextLE.withLocalDecl cIndices
          Rindices.toBindingContextWF `t majorTy .default
        let hMotiveFrame := BindingContextLE.withLocalDecl cMajor
          (Rindices.toBindingContextWF.withLocalDecl
            `t majorTy .default)
          motiveName (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default
        let hAllFrames : BindingContextLE current cMotive :=
          hIndices.trans (hMajorFrame.trans hMotiveFrame)
        let Hbindings' := Hbindings.pushFrame hIndices
          Rindices.toBindingContextWF
          Hrecent.toFVarArrayAfter.toFVarArrayIn
          `t majorTy .default motiveName
          (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default
        let Horigins' := Horigins.pushFrame hIndices
          Rindices.toBindingContextWF HindexOrigins
          `t majorTy .default motiveName
          (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) .default
        let Hparams' := Hparams.mono hAllFrames
        have HnoAlias' : RecInfoBindings.NoAlias stats.params (recInfos.push {
            motive := .fvar ⟨cIndices.ngen.next.curr⟩, minors := #[], indices,
            major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
          exact Hbindings.pushFrame_noAlias Hparams HnoAlias hIndices
            Rindices.toBindingContextWF
            Hrecent.toFVarArrayAfter
            `t majorTy .default
        have holdMinors : Hbindings.flatMinors.fvars = [] :=
          Hempty.flatMinors_fvars Hbindings
        have hnewMinors : Hbindings'.flatMinors.fvars = [] :=
          Hempty.push.flatMinors_fvars Hbindings'
        have hparamsFVars : Hparams'.fvars = Hparams.fvars := rfl
        have hmotiveFVars : Hbindings'.motives.fvars =
            Hbindings.motives.fvars ++
              [(⟨cMajor.ngen.curr⟩ : FVarId)] := by
          rw [← Hbindings'.motives.exprArrayFVarIds,
            ← Hbindings.motives.exprArrayFVarIds]
          simp [ExprArrayFVarIds, cMajor, recursorFVarId]
        have hcontextFVars : Rmotive.mlctx.vlctx.fvars =
            (⟨cMajor.ngen.curr⟩ : FVarId) ::
              ((⟨cIndices.ngen.curr⟩ : FVarId) ::
                Hrecent.fvars.reverse) ++ R.mlctx.vlctx.fvars := by
          dsimp only [Rmotive, Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
            TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some]
          rw [Hrecent.contextFVars]
          rfl
        have Horder' : RecInfoOuterOrder Rmotive Hparams' Hbindings' :=
          RecInfoOuterOrder.pushMotive Horder holdMinors hparamsFVars
            hmotiveFVars hnewMinors hcontextFVars
        have hparameterDeclsMotive :
            HsuffixMotive.parameterDecls = Hsuffix.parameterDecls :=
          hparameterDecls
        have HparamsCtx' : ∀ i (hi : i < indTypes.size),
            VEnv.IsDefEqCtx Rmotive.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length []
              ((Hheaders i hi).recursorParams Helim).reverse
              HsuffixMotive.parameterDecls.toCtx := by
          intro i hi
          have hvenvMotive : Rmotive.venv = R.venv := by
            change Rindices.venv = R.venv
            exact henvIndices.trans henv.symm
          rw [hvenvMotive, hparameterDeclsMotive]
          exact HparamsCtx i hi
        have hnewMotiveShape := motiveTypeShape Rindices Hframe HindexOrigins.bound motiveName
        let nextInfo : AddInductive.RecInfo := {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major }
        have hnewMotiveShape' : (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) =
            cMotive.lctx.mkForall nextInfo.indices
              (cMotive.lctx.mkForall #[nextInfo.major]
                (.sort elimLevel)) := by
          change (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) =
            cMotive.lctx.mkForall indices
              (cMotive.lctx.mkForall #[major] (.sort elimLevel))
          exact hnewMotiveShape
        let HmotiveShapes' := HmotiveShapes.push Hbindings hAllFrames
          nextInfo (motiveTy.consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) hnewMotiveShape'
        have hnewMajorShape : majorTy =
            ((mkAppN (mkAppN stats.indConsts[recInfos.size]! stats.params)
              nextInfo.indices).consumeTypeAnnotationsVerified cIndices.env.isTypeAnnotationWrapper) := by
          simp only [majorTy, nextInfo]
          rw [hprogress]
        have HmajorShapesI : MajorPremiseTypes stats recInfos Horigins.majorTypes
            cIndices.env.isTypeAnnotationWrapper := by
          rw [hIndices.env_eq]; exact HmajorShapes
        let HmajorShapes' := HmajorShapesI.push nextInfo majorTy hnewMajorShape
        let HmajorExtension :=
          RecursorContextExtension.withLocalDecl (name := `t)
            (bi := .default) Rindices
            Hframe.majorTr Hframe.majorType
        let HmotiveExtension :=
          RecursorContextExtension.withLocalDecl (name := motiveName)
            (bi := .default) Rmajor
            Hframe.motiveTr Hframe.motiveType
        let HframeExtension : RecursorContextExtension Rindices Rmotive :=
          HmajorExtension.trans HmotiveExtension
        let HrootExtension : RecursorContextExtension R Rmotive :=
          Hrecent.contextExtension.trans HframeExtension
        have HseedPair :
            ∃ S : MotiveDecl Rmotive stats decl
                recInfos.size nextInfo elimLevel,
              VEnv.IsDefEqCtx Rmotive.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                [] S.canonical.params.reverse
                  Hsuffix.parameterDecls.toCtx := by
          rw [hprogress]
          exact motiveDecl Hheader hconsume Hsuffix Hroot Rindices
            henvIndices Hsynthesis hcanonicalParams hscopeBase HnarrowStats
            Hruntime hfront halign HnarrowIndices hindexCount hcanonical
            HindexOrigins.bound Hrecent hindexUniverses harity Hframe
            motiveName
        rcases HseedPair with ⟨Hseed', HseedParams⟩
        have HseedAt : MotiveAppliesAbove Rmotive stats decl
            recInfos.size nextInfo elimLevel := Hseed'.toTelescopeAt
        let Htelescopes' :=
          (Htelescopes.mono HrootExtension).push nextInfo
            HseedAt Hseed' HseedParams
        have HindexTraces' : IndexTelescopeRuns stats indTypes cMotive
            (recInfos.push nextInfo) := by
          refine (HindexTraces.mono hAllFrames).push nextInfo (type := type) ?_
          have hsrc : indTypes[recInfos.size]!.type = indTypes[dIdx].type := by
            rw [hprogress, getElem!_pos indTypes dIdx hidx]
          rw [hsrc]
          exact HindexTrace.mono (hMajorFrame.trans hMotiveFrame)
        refine resultTyping Hbase stats indTypes elimLevel Helim Hheaders
          hconsume (dIdx + 1)
          (recInfos.push {
            motive := .fvar ⟨cMajor.ngen.curr⟩
            minors := #[]
            indices
            major }) k Rmotive (by simpa [Rmotive, Rmajor] using henvIndices)
          HsuffixMotive HparamsCtx' HstatsMotive Hbindings' Horigins'
          HmajorAtMotive HmajorShapes' HmotiveAtMotive HmotiveShapes' (by
            simpa [hparameterDeclsMotive] using Htelescopes') HindexRows' Hparams'
          HnoAlias' Horder'
          (Hroot.trans hAllFrames)
          (by simp [hprogress])
          (by
            apply Harities.push
            have hnew : indices.size = stats.nindices[dIdx]! := by
              simpa using harity
            simpa [hprogress] using hnew)
          Hempty.push Hblueprints.pushEmpty
          (hparamU.mono Hparams hAllFrames)
          HindexTraces' ?_
        · intro cOut outDepth out Rout henvOut HsuffixOut
            hparameterDeclsOut HstatsOut HbindingsOut
            HoriginsOut HmajorOut HmajorShapesOut HmotiveOut HmotiveShapesOut
            HtelescopesOut HindexRowsOut
            HparamsOut HnoAliasOut HorderOut HaritiesOut HemptyOut
            HblueprintsOut HrootOut houtSize HindexTracesOut
          apply Hk out Rout henvOut HsuffixOut
            (hparameterDeclsOut.trans hparameterDeclsMotive)
            HstatsOut HbindingsOut
            HoriginsOut HmajorOut HmajorShapesOut HmotiveOut HmotiveShapesOut
            HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
            HaritiesOut HemptyOut HblueprintsOut HrootOut ?_ HindexTracesOut
          simp only [Array.size_push] at houtSize
          omega
      · simp only [loopK]
        rw [if_neg harity]
        exact Except.WF.throw
  · rw [dif_neg hidx]
    exact Hk recInfos R henv Hsuffix rfl Hstats Hbindings Horigins HmajorTypes
      HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexTypeRows Hparams HnoAlias
      Horder Harities Hempty Hblueprints Hroot (by omega) HindexTraces
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd1

namespace mkRecInfos.loopUArgs.loop

/-- Refinement of `loopUArgs.loop` which reconstructs the complete
higher-order recursive-domain judgment on the way back out of the forall
telescope.  The terminal executable check supplies the direct family
application; each traversed binder contributes one `RecursiveArgAtTarget`
`forallE` constructor. -/
theorem resultRecursiveDomain {alpha : Type}
    (head : Expr)
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Nat → AddInductive.M alpha)
    {decl : VInductDecl} {recLparams : List Name}
    {root : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Rroot.venv stats.indConsts)
    {initialType uiTy : Expr} {xs : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : Nat → alpha → Prop}
    (R : RecursorContextWF c recLparams)
    {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {typeTarget : VExpr}
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx uiTy typeTarget)
    (htypeType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx typeTarget)
    {typeTarget₀ : VExpr}
    (htype₀ : TrExpr R.venv recLparams R.chk.vlctx uiTy typeTarget₀)
    (htypeType₀ : R.venv.IsType recLparams.length R.chk.vlctx.toCtx typeTarget₀)
    (Hxs : RecursorFVarSuffix Rroot R xs)
    {M₀ : TypeChecker.MLCtx} {T₀ : VExpr}
    (hagreeR : ∃ hn : xs.size ≤ R.chk.length,
      MLCtxTopAgree R.mlctx R.chk xs.size ∧ R.chk.dropN xs.size hn = M₀ ∧
        R.venv.IsDefEqU recLparams.length M₀.vlctx.toCtx T₀
          (R.chk.mkForall' xs.size hn typeTarget₀))
    {l : LocalContext}
    (Htrace : LoopUArgsRun root l initialType c uiTy xs)
    {P : FVarId → Prop}
    (htypeScope : uiTy.FVarsIn
      (fun fv => fv ∈ Hxs.fvars ∨ P fv))
    (hcurrentUp : IsFVarUpSet
      (fun fv => fv ∈ Hxs.fvars ∨ P fv) R.mlctx.vlctx)
    {appliedTarget : VExpr}
    (happlied : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN head xs) appliedTarget)
    (happliedType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx appliedTarget typeTarget)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      LoopUArgsRun root l initialType current exposedType args →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hrecent : RecursorFVarSuffix Rroot Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN head args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      AddInductive.isValidIndApp? stats exposedType = some target →
      exposedType.FVarsIn
        (fun fv => fv ∈ Hrecent.fvars ∨ P fv) →
      IsFVarUpSet (fun fv => fv ∈ Hrecent.fvars ∨ P fv)
        Rcurrent.mlctx.vlctx →
      (∃ hn : args.size ≤ Rcurrent.chk.length,
        MLCtxTopAgree Rcurrent.mlctx Rcurrent.chk args.size ∧
          Rcurrent.chk.dropN args.size hn = M₀ ∧
          ∃ t₀, TrExpr Rcurrent.venv recLparams Rcurrent.chk.vlctx
            exposedType t₀ ∧
          Rcurrent.venv.IsType recLparams.length Rcurrent.chk.vlctx.toCtx t₀ ∧
          Rcurrent.venv.IsDefEqU recLparams.length M₀.vlctx.toCtx T₀
            (Rcurrent.chk.mkForall' args.size hn t₀)) →
      (k exposedType args target current).WF (Q target)) :
    (AddInductive.mkRecInfos.loopUArgs.loop
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        k exposedType args target)
      uiTy xs fuel c).WF fun out =>
        ∃ target, ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[target]'htarget).name
              R.mlctx.vlctx.toCtx depth typeTarget ∧ Q target out := by
  induction fuel generalizing c uiTy xs typeTarget typeTarget₀ appliedTarget depth R with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopUArgs.loop] at h
  | succ fuel ih =>
    cases uiTy with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopUArgs.loop]
      rcases TrExpr.forallE_source htype with
        ⟨sourceDom, sourceBody, hdom, hbody, hdomType,
          hbodyType, hforallEq⟩
      rcases hconsume c recLparams R hdom hdomType with
        ⟨consumedDom, Hdom⟩
      rcases Hdom.body R hbody with
        ⟨consumedBody, hbodyConsumed, hbodyEq⟩
      rcases TrExpr.forallE_source htype₀ with
        ⟨dom₀, bodyN₀, hdom₀, hbodyN₀, hdom₀Type, hbodyN₀Type, hforallEq₀⟩
      rcases hconsume _ recLparams R.atCheckLCtx hdom₀ hdom₀Type with
        ⟨consumedDom₀, Hdom₀⟩
      rcases Hdom₀.body R.atCheckLCtx hbodyN₀ with
        ⟨consumedBody₀, hbodyConsumed₀, hbodyEq₀⟩
      -- the closed checker type stays fixed across the checking-context binder
      have hchkWF := R.check.wf.tr.wf
      have HforallConsumed₀ : R.venv.IsDefEqU recLparams.length
          R.chk.vlctx.toCtx (.forallE dom₀ bodyN₀)
          (.forallE consumedDom₀ consumedBody₀) := by
        rcases hbodyN₀Type with ⟨bodyLevel₀, HbodyType₀⟩
        have hctx₀ : OnCtx (dom₀ :: R.chk.vlctx.toCtx)
            (R.venv.IsType recLparams.length) := ⟨hchkWF.toCtx, hdom₀Type⟩
        have HbodyAtSource₀ := hbodyEq₀.of_l R.checking.tr.wf hctx₀ HbodyType₀
        exact ⟨_, VEnv.IsDefEq.forallEDF
          Hdom₀.source_defeq.choose_spec HbodyAtSource₀⟩
      have HtypeConsumed₀ : R.venv.IsDefEqU recLparams.length
          R.chk.vlctx.toCtx typeTarget₀
          (.forallE consumedDom₀ consumedBody₀) :=
        hforallEq₀.symm.trans R.checking.tr.wf hchkWF.toCtx HforallConsumed₀
      have HtypeType₀ : R.venv.IsType recLparams.length R.chk.vlctx.toCtx
          typeTarget₀ := by
        have h := VEnv.IsType.forallE hdom₀Type hbodyN₀Type
        exact h.defeqU_l R.checking.tr.wf hchkWF.toCtx hforallEq₀
      rcases HtypeType₀ with ⟨typeLevel₀, HtypeType₀⟩
      have HtypeConsumedAtSort₀ := HtypeConsumed₀.of_l R.checking.tr.wf
        hchkWF.toCtx HtypeType₀
      refine withCheckedLocalDecl.recursorWF (name := name) (bi := bi)
        (Q := fun out =>
          ∃ target, ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[target]'htarget).name
              R.mlctx.vlctx.toCtx depth typeTarget ∧ Q target out)
        R Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType ?_
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
        checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }
      let R' : RecursorContextWF c' recLparams :=
        R.withCheckedLocalDecl (name := name) (bi := bi)
        Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
      let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have happliedFn := happlied.weakFV R.checking.tr.wf.orderedStrong W
        R'.mlctx_wf.tr.wf
      have happliedFnType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (appliedTarget.liftN 1 0)
          ((VExpr.forallE sourceDom sourceBody).liftN 1 0) := by
        exact (happliedType.defeqU_r R.checking.tr.wf
          R.mlctx_wf.tr.wf.toCtx hforallEq.symm).weakN
            R.checking.tr.wf.ordered W.toCtx
      have harg : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        apply TrExprS.fvar
        change VLCtx.find?
          ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
            R.mlctx.vlctx)
          (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0)
        simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
          VLocalDecl.value, VLocalDecl.type, VExpr.lift]
      have hargType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (.bvar 0) (sourceDom.liftN 1 0) := by
        have hlookup : R'.mlctx.vlctx.find? (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0) := by
          change VLCtx.find?
            ((some (⟨c.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
              R.mlctx.vlctx)
            (.inr ⟨c.ngen.curr⟩) =
              some ((.bvar 0), consumedDom.liftN 1 0)
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type, VExpr.lift]
        have hconsumed := R'.mlctx_wf.tr.wf.find?_wf
          R'.checking.tr.wf.orderedStrong hlookup
        have hdomainEq := Hdom.source_defeq.choose_spec.weakN
          R.checking.tr.wf.ordered W.toCtx
        exact hconsumed.defeqU_r R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx hdomainEq.symm.toU
      have happlied' : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (mkAppN head (xs.push (.fvar ⟨c.ngen.curr⟩)))
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) := by
        simpa [mkAppN] using
          TrExprS.app happliedFnType hargType happliedFn harg
      have happliedType' : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) consumedBody := by
        have happ := VEnv.HasType.app happliedFnType hargType
        have hbodyEq' := Hdom.bodyDefEqUnannotated R hbodyEq
        apply happ.defeqU_r R'.checking.tr.wf R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
          RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VExpr.inst_liftN_bvar] using
            hbodyEq'
      have hopened := R.instantiateFresh (name := name) (bi := bi)
        Hdom.unannotated Hdom.isType hbodyConsumed
      let Hxs' := Hxs.pushCurrentChecked name (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
        consumedDom bi Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
      have hopened₀ := R.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
        Hdom₀.unannotated Hdom₀.isType hbodyConsumed₀
      have hbodyScope : (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)).FVarsIn
          (fun fv => fv ∈ Hxs'.fvars ∨ P fv) := by
        have hbodyScopeBase : body.FVarsIn
            (fun fv => fv ∈ Hxs'.fvars ∨ P fv) := by
          apply htypeScope.2.mono
          intro fv h
          rcases h with hlocal | hroot
          · exact Or.inl (by
              change fv ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩]
              exact List.mem_append_left _ hlocal)
          · exact Or.inr hroot
        simpa only [Expr.instantiate1_eq] using
          hbodyScopeBase.instantiate1 (by
            simp only [FVarsIn]
            exact Or.inl (by
              change (⟨c.ngen.curr⟩ : FVarId) ∈
                Hxs.fvars ++ [⟨c.ngen.curr⟩]
              simp))
      have hnewNotCurrent : (⟨c.ngen.curr⟩ : FVarId) ∉
          R.mlctx.vlctx.fvars := by
        intro hmem
        rw [← R.mlctx_wf.tr.fvars_eq, R.lctx_eq] at hmem
        exact R.toBindingContextWF.current_not_mem hmem
      have hcurrentUp' : IsFVarUpSet
          (fun fv => fv ∈ Hxs'.fvars ∨ P fv) R.mlctx.vlctx := by
        apply (IsFVarUpSet.congr (R.mlctx_wf.tr.wf).fvwf ?_).mp hcurrentUp
        intro fv hfv
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inl (by
              change fv ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩]
              exact List.mem_append_left _ h)
          · exact Or.inr h
        · intro h
          rcases h with h | h
          · change fv ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩] at h
            rcases List.mem_append.mp h with h | h
            · exact Or.inl h
            · simp only [List.mem_singleton] at h
              subst fv
              exact False.elim (hnewNotCurrent hfv)
          · exact Or.inr h
      have hnextUp : IsFVarUpSet
          (fun fv => fv ∈ Hxs'.fvars ∨ P fv) R'.mlctx.vlctx := by
        change IsFVarUpSet _
          ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
            R.mlctx.vlctx)
        refine ⟨hcurrentUp', fun _ dep hdep => ?_⟩
        have hselected := (fvarsIn_iff.mp
          (Expr.consumeTypeAnnotationsVerified_fvarsIn htypeScope.1)).1 dep hdep
        rcases hselected with hlocal | hroot
        · exact Or.inl (by
            change dep ∈ Hxs.fvars ++ [⟨c.ngen.curr⟩]
            exact List.mem_append_left _ hlocal)
        · exact Or.inr hroot
      have hsourceBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx sourceBody := by
        let hctxEq : VLCtx.IsDefEq R.venv recLparams.length
            ((none, .vlam sourceDom) :: R.mlctx.vlctx)
            ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
          VLCtx.IsDefEq.cons
            (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
            (.vlam Hdom.source_defeq.choose_spec)
        simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
          RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VLCtx.toCtx] using
          hbodyType.defeqDFC R.checking.tr.wf.ordered hctxEq.defeqCtx
      have hbodyEq' := Hdom.bodyDefEqUnannotated R hbodyEq
      have hconsumedBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx consumedBody := by
        apply hsourceBodyType.defeqU_l R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
          RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VLCtx.toCtx] using hbodyEq'
      let normalizeRun :=
        (monadLift (TypeChecker.whnf
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
            AddInductive.M Expr) c'
      have hnormalizeSemantic :=
        whnfInRecursorContext.dualWF R' hopened hopened₀
      have hnormalize : normalizeRun.WF fun normalized =>
          normalizeRun = .ok normalized ∧
          (FVarsBelow R'.mlctx.vlctx
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized ∧
          TrExpr R'.venv recLparams R'.mlctx.vlctx normalized consumedBody) ∧
          TrExpr R'.venv recLparams R'.chk.vlctx normalized consumedBody₀ := by
        intro normalized hrun
        have h := hnormalizeSemantic normalized hrun
        exact ⟨hrun, h.1, h.2.2⟩
      refine hnormalize.bind fun normalized hnormalized => ?_
      rcases hnormalized with ⟨hnormalizeRun, hnormalized, hnormalized₀⟩
      have Hstats' := Hstats.withFVar R'.checking.tr.wf R'.mlctx_wf.tr.wf
      have hctx' : VLCtx.NoIndConsts
          (decl.types.map (·.name)) R'.mlctx.vlctx := by
        apply VLCtx.NoIndConsts.cons hctx
        rfl
      have hnormalizedScope := hnormalized.1 _ hnextUp hbodyScope
      let Htrace' : LoopUArgsRun root l initialType c' normalized
          (xs.push (.fvar ⟨c.ngen.curr⟩)) :=
        .push Htrace rfl hnormalizeRun
      have hagreeR' : ∃ hn : (xs.push (.fvar ⟨c.ngen.curr⟩)).size ≤ R'.chk.length,
          MLCtxTopAgree R'.mlctx R'.chk (xs.push (.fvar ⟨c.ngen.curr⟩)).size ∧
            R'.chk.dropN (xs.push (.fvar ⟨c.ngen.curr⟩)).size hn = M₀ ∧
            R'.venv.IsDefEqU recLparams.length M₀.vlctx.toCtx T₀
              (R'.chk.mkForall' (xs.push (.fvar ⟨c.ngen.curr⟩)).size hn
                consumedBody₀) := by
        obtain ⟨hn, hag, hdrop, hclosed⟩ := hagreeR
        have h := MLCtxTopAgree.stepDropEq (M := M₀) ⟨c.ngen.curr⟩ name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom consumedDom₀ bi
          ⟨hn, hag, hdrop⟩
        obtain ⟨hn', hag', hdrop'⟩ := h
        rcases R.check.wf.mkForall'_congr HtypeConsumedAtSort₀ xs.size hn with
          ⟨closedLevel, HclosedCongr⟩
        have HclosedCongr' : R.venv.IsDefEqU recLparams.length M₀.vlctx.toCtx
            (R.chk.mkForall' xs.size hn typeTarget₀)
            (R.chk.mkForall' xs.size hn
              (.forallE consumedDom₀ consumedBody₀)) := by
          rw [← hdrop]
          exact ⟨_, HclosedCongr⟩
        have hM₀WF : M₀.WF R.venv recLparams := by
          rw [← hdrop]
          exact R.check.wf.dropN _ _
        simp only [Array.size_push]
        refine ⟨hn', hag', hdrop', ?_⟩
        exact hclosed.trans R.checking.tr.wf hM₀WF.tr.wf.toCtx HclosedCongr'
      have hconsumedBodyType₀ : R'.venv.IsType recLparams.length
          R'.chk.vlctx.toCtx consumedBody₀ := by
        have hctx₀ : VEnv.IsDefEqCtx R.venv recLparams.length []
            (dom₀ :: R.chk.vlctx.toCtx) (consumedDom₀ :: R.chk.vlctx.toCtx) :=
          .succ (.refl hchkWF.toCtx) Hdom₀.source_defeq.choose_spec
        have hctx₀' : OnCtx (dom₀ :: R.chk.vlctx.toCtx)
            (R.venv.IsType recLparams.length) := ⟨hchkWF.toCtx, hdom₀Type⟩
        have h1 := hbodyN₀Type.defeqU_l R.checking.tr.wf hctx₀' hbodyEq₀
        exact h1.defeqDFC R.checking.tr.wf.ordered hctx₀
      have Hrec := ih R' Hstats' hctx' hnormalized.2
        hconsumedBodyType hnormalized₀ hconsumedBodyType₀
        Hxs' hagreeR' Htrace' hnormalizedScope hnextUp
        happlied' happliedType'
      exact Hrec.mono fun out Hout => by
        rcases Hout with ⟨target, htarget, hrecursive, hout⟩
        rcases hforallEq.symm with ⟨forallType, hforall⟩
        rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
        rcases hbodyEq with ⟨bodyType, hbodyEq⟩
        exact ⟨target, htarget, .forallE hforall hdomEq hbodyEq
          hrecursive, hout⟩
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      change ((do
        let some target := AddInductive.isValidIndApp? stats _
          | throw (Lean.Kernel.Exception.other
            "recursive constructor field lost its inductive result type")
        k _ xs target) c).WF _
      rcases htype with ⟨syntaxTarget, hsyntax, hdefeq⟩
      cases hvalid : AddInductive.isValidIndApp? stats _ with
      | none =>
        exact Except.WF.throw
      | some target =>
        have htargetStats : target < stats.indConsts.size :=
          (checkPositivityStep.isValidIndApp?_some hvalid).1
        have htarget : target < decl.types.length := by
          rw [← Hstats.types_size]
          exact htargetStats
        let Hvalid := Hstats.validatedIndAppAt hsyntax hvalid htarget
          (by simpa only [Hxs.venv_eq] using hlit) hctx
        have Hterminal := Hk (target := target) R Htrace hsyntax hdefeq
          htypeType Hxs happlied happliedType hvalid htypeScope hcurrentUp
          (by
            obtain ⟨hn, hag, hdrop, hclosed⟩ := hagreeR
            exact ⟨hn, hag, hdrop, _, htype₀, htypeType₀, hclosed⟩)
        exact Hterminal.mono fun out hout => by
          rcases hdefeq.symm with ⟨exprType, hterminal⟩
          exact ⟨target, htarget,
            VInductDecl.RecursiveArgAtTarget.direct hterminal
              Hvalid.application,
            hout⟩

end mkRecInfos.loopUArgs.loop

/-- The recursive-field interface keeps the complete source domain,
not merely the validated family application exposed after traversing its
higher-order binders.  This is the fact needed to align the
executable's selected recursive calls with `VInductDecl.RecursiveField`.
-/
theorem mkRecInfos.loopUArgs.resultRecursiveDomainOfInferredScope {alpha : Type}
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Nat → AddInductive.M alpha)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    (prior : Array Expr)
    (hpriorFVars : ∃ k, prior.toList.map (·.fvarId!) =
        ((c.checkLCtx.toList.map (·.fvarId)).reverse).take k ∧
      ((c.checkLCtx.toList.map (·.fvarId)).reverse)[k]? =
        some (Expr.fvar fv).fvarId!)
    {P : FVarId → Prop}
    (hinferredScopeRun : (AddInductive.getType (.fvar fv) c).WF fun ty => ty.FVarsIn P)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {Q : Nat → alpha → Prop}
    (Hk : ∀ (Hinput : LoopUArgsInput c (.fvar fv))
      {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      LoopUArgsRun c (loopUArgsCheckLCtx c Hinput.prior)
        Hinput.normalizedType current exposedType args →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hrecent : RecursorFVarSuffix R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      AddInductive.isValidIndApp? stats exposedType = some target →
      exposedType.FVarsIn
        (fun fv => fv ∈ Hrecent.fvars ∨ P fv) →
      IsFVarUpSet (fun fv => fv ∈ Hrecent.fvars ∨ P fv)
        Rcurrent.mlctx.vlctx →
      (∃ hn : args.size ≤ Rcurrent.chk.length,
        MLCtxTopAgree Rcurrent.mlctx Rcurrent.chk args.size ∧
          ∃ j hj ty₀, Rcurrent.chk.dropN args.size hn = R.chk.dropN j hj ∧
            (∃ k, (R.chk.dropN j hj).fvarList = R.chk.fvarList.take k ∧
              R.chk.fvarList[k]? = some fv) ∧
            TrExprS R.venv recLparams (R.chk.dropN j hj).vlctx
              (c.lctx.get! fv).type ty₀ ∧
            R.venv.IsType recLparams.length (R.chk.dropN j hj).vlctx.toCtx ty₀ ∧
            ∃ t₀, TrExpr Rcurrent.venv recLparams Rcurrent.chk.vlctx
              exposedType t₀ ∧
            Rcurrent.venv.IsType recLparams.length Rcurrent.chk.vlctx.toCtx t₀ ∧
            Rcurrent.venv.IsDefEqU recLparams.length
              (R.chk.dropN j hj).vlctx.toCtx ty₀
              (Rcurrent.chk.mkForall' args.size hn t₀)) →
      (k exposedType args target current).WF (Q target)) :
    (AddInductive.mkRecInfos.loopUArgs prior (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        k exposedType args target) c).WF fun out =>
          ∃ domain,
            R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
              fieldTarget domain ∧
            ∃ target, ∃ htarget : target < decl.types.length,
              decl.RecursiveArgAtTarget R.venv recLparams.length
                (decl.types[target]'htarget).name
                R.mlctx.vlctx.toCtx depth domain ∧ Q target out := by
  unfold AddInductive.mkRecInfos.loopUArgs
  let inferRun := AddInductive.getType (.fvar fv) c
  have hinferSemantic := getTypeFVarInRecursorContext.WF R hfield
  have hinfer : inferRun.WF fun inferred =>
      inferRun = .ok inferred ∧
      ∃ inferredTarget, TrTyping R.venv recLparams R.mlctx.vlctx
        (.fvar fv) inferred fieldTarget inferredTarget := by
    intro inferred hr
    exact ⟨hr, hinferSemantic inferred hr⟩
  refine AddInductive.M.WF_bind hinfer fun inferred hinferred => ?_
  rcases hinferred with
    ⟨hinferRun, inferredTarget, _hbelow, hfieldAgain, hinferredTr,
      hfieldTyping⟩
  have hinferredEq : inferred = (c.lctx.get! fv).type := by
    have h := hinferRun.symm.trans (AddInductive.getType.run (.fvar fv) c)
    exact Except.ok.inj h
  have hinferredScope : inferred.FVarsIn P :=
    hinferredScopeRun inferred hinferRun
  have hinferredType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
  refine AddInductive.M.WF_bind AddInductive.getLCtx.WF fun _ hlctx => ?_
  subst hlctx
  -- Normalization and the argument telescope run in the checker context of
  -- the parameters and the fields before `fv`.
  let F := loopUArgsCheckLCtx c prior
  obtain ⟨jF, hjF, fieldType₀, hlctxF, hfieldType₀, hfieldType₀Ty, hkF⟩ :=
    R.priorBase hpriorFVars
  let BF : R.Base F := (R.check.below jF hjF).cast hlctxF
  let RF := R.withCheckLCtx F BF
  rw [AddInductive.withCheckLCtx_apply]
  have hinferred₀ : TrExprS RF.venv recLparams RF.chk.vlctx inferred fieldType₀ := by
    rw [hinferredEq]; exact hfieldType₀
  let normalizeRun :=
    (monadLift (TypeChecker.whnf inferred) : AddInductive.M Expr)
      { c with checkLCtx := F }
  have hnormalizeSemantic :=
    whnfInRecursorContext.dualWF RF hinferredTr hinferred₀
  have hnormalize : normalizeRun.WF fun normalized =>
      normalizeRun = .ok normalized ∧
      (FVarsBelow R.mlctx.vlctx inferred normalized ∧
      TrExpr R.venv recLparams R.mlctx.vlctx normalized inferredTarget) ∧
      TrExpr R.venv recLparams RF.chk.vlctx normalized fieldType₀ := by
    intro normalized hr
    have h := hnormalizeSemantic normalized hr
    exact ⟨hr, h.1, h.2.2⟩
  refine AddInductive.M.WF_bind hnormalize fun normalized hnormalized => ?_
  rcases hnormalized with ⟨hnormalizeRun, ⟨hnormalizedScope,
    hnormalizedTr⟩, hnormalized₀⟩
  let Hinput : LoopUArgsInput c (.fvar fv) := {
    prior := prior
    priorFVars := hpriorFVars
    inferredType := inferred
    normalizedType := normalized
    inference := hinferRun
    normalization := hnormalizeRun }
  have hnormalizedScope : normalized.FVarsIn P :=
    hnormalizedScope P hrootUp hinferredScope
  refine AddInductive.M.WF_bind AddInductive.readContext.WF fun _ hctx => ?_
  subst hctx
  change (AddInductive.mkRecInfos.loopUArgs.loop
    (fun exposedType args => do
      let some target := AddInductive.isValidIndApp? stats exposedType
        | throw (.other
          "recursive constructor field lost its inductive result type")
      k exposedType args target)
    normalized #[] c.fuel.inductiveFuel { c with checkLCtx := F }).WF _
  have Hloop := mkRecInfos.loopUArgs.loop.resultRecursiveDomain
    (fuel := c.fuel.inductiveFuel) (.fvar fv) stats k RF
    hconsume hlit RF Hstats hctx hnormalizedTr hinferredType hnormalized₀
    hfieldType₀Ty
    (RecursorFVarSuffix.empty RF)
    (M₀ := RF.chk) (T₀ := fieldType₀)
    ⟨Nat.zero_le _, .zero _ _, rfl, by
      obtain ⟨u, h⟩ := hfieldType₀Ty
      exact ⟨_, h⟩⟩
    (LoopUArgsRun.root (root := { c with checkLCtx := F }) (l := F)
      (source := normalized))
    (hnormalizedScope.mono fun _ h => Or.inr h)
    (by
      apply (IsFVarUpSet.congr (R.mlctx_wf.tr.wf).fvwf ?_).mp hrootUp
      intro fv _
      change P fv ↔ fv ∈ ([] : List FVarId) ∨ P fv
      simp)
    (by
      change TrExprS R.venv recLparams R.mlctx.vlctx
        (.fvar fv) fieldTarget
      exact hfieldAgain)
    hfieldTyping (fun {_} Rcurrent {_} {_ _ _} {_} {_} htrace h1 h2 h3 Hrecent
        h4 h5 h6 h7 h8 h9 =>
      Hk Hinput Rcurrent htrace.ofCheckRoot h1 h2 h3 Hrecent.ofCheckRoot
        h4 h5 h6 h7 h8
        (by
          obtain ⟨hn, hag, hd, t₀, htr, htrTy, hcl⟩ := h9
          exact ⟨hn, hag, jF, hjF, fieldType₀, hd, hkF, hfieldType₀, hfieldType₀Ty,
            t₀, htr, htrTy, hcl⟩))
  exact Hloop.mono fun out hout => ⟨inferredTarget, hfieldTyping, hout⟩

/-- Source-level construction of one induction-hypothesis type.
It records the terminal family application and the higher-order telescope
selected by `loopUArgs`, before the resulting type is installed as a local
declaration by `loopU`. -/
structure InductionHypothesisTypeAt
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (root : AddInductive.Context) (field type : Expr) where
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  exposedType : Expr
  args : Array Expr
  arguments_bound : FVarArrayAfter root current args
  loopInput : LoopUArgsInput root field
  loopTrace : LoopUArgsRun root
    (loopUArgsCheckLCtx root loopInput.prior) loopInput.normalizedType current
    exposedType args
  field_fvar : ∃ fv, field = .fvar fv ∧ fv ∈ root.lctx.fvars
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats exposedType = some ownerIdx
  motive_is_fvar : ∃ fv,
    recInfos[ownerIdx]!.motive = .fvar fv ∧ fv ∈ root.lctx.fvars
  type_eq :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive itIndices)
      (mkAppN field args)
    type = current.lctx.mkForall args motiveApp

/-- Forget that the construction was recorded by the in-progress hypothesis loop;
`InductionHypothesisType` for the finished minor has the same data. -/
def InductionHypothesisTypeAt.toMinor
    (O : InductionHypothesisTypeAt stats recInfos root field type) :
    InductionHypothesisType stats recInfos root field type := {
  current := O.current
  current_wf := O.current_wf
  current_extends := O.current_extends
  exposedType := O.exposedType
  args := O.args
  arguments_bound := O.arguments_bound
  loopInput := O.loopInput
  loopTrace := O.loopTrace
  field_fvar := O.field_fvar
  ownerIdx := O.ownerIdx
  owner_valid := O.owner_valid
  motive_is_fvar := O.motive_is_fvar
  type_eq := O.type_eq }

/-- Pointwise source constructions for the prefix of recursive fields already
processed by `loopU`.  Each declared hypothesis is tied to the type (before
annotation stripping) returned by the corresponding `loopUArgs` run. -/
structure InductionHypothesisTypesPrefix
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (fieldRoot c : AddInductive.Context)
    (fields hypotheses : Array Expr) where
  size_le : hypotheses.size ≤ fields.size
  entry : ∀ j (_hj : j < hypotheses.size),
    ∃ root sourceType,
      BindingContextLE fieldRoot root ∧
      Nonempty (InductionHypothesisTypeAt
        stats recInfos root fields[j]! sourceType) ∧
      ∃ D : FVarDeclAt c hypotheses j,
        D.type = (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)

theorem InductionHypothesisTypesPrefix.empty
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (c : AddInductive.Context) (fields : Array Expr) :
    InductionHypothesisTypesPrefix stats recInfos c c fields #[] where
  size_le := by simp
  entry := by intro j hj; simp at hj

theorem InductionHypothesisTypesPrefix.pushCurrent
    (H : InductionHypothesisTypesPrefix stats recInfos fieldRoot c
      fields hypotheses)
    (Hc : BindingContextWF c)
    (name : Name) (sourceType : Expr) (bi : BinderInfo)
    (hnext : hypotheses.size < fields.size)
    (Hroot : BindingContextLE fieldRoot root)
    (Horigin : Nonempty (InductionHypothesisTypeAt stats recInfos root
      fields[hypotheses.size]! sourceType)) :
    InductionHypothesisTypesPrefix stats recInfos fieldRoot
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }
      fields (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) := by
  let ty := (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withLocalDecl c Hc name ty bi
  refine {
    size_le := by simpa using Nat.succ_le_of_lt hnext
    entry := ?_ }
  intro j hj
  by_cases hilast : j = hypotheses.size
  · subst j
    let D : FVarDeclAt c'
        (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) hypotheses.size := {
      inBounds := by simp
      fvar := ⟨c.ngen.curr⟩
      expression := by simp
      member := by
        simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
          List.map_cons, LocalDecl.fvarId, List.mem_cons]
        exact Or.inl trivial
      index := c.lctx.decls.size
      userName := name
      type := ty
      binderInfo := bi
      kind := .default
      declaration := by
        simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
          Hc.wf.map_wf.find?_insert] }
    exact ⟨root, sourceType, Hroot, Horigin, D, rfl⟩
  · have hjOld : j < hypotheses.size := by
      have : j < hypotheses.size + 1 := by simpa using hj
      omega
    rcases H.entry j hjOld with
      ⟨oldRoot, oldType, HoldRoot, Hold, D, htype⟩
    exact ⟨oldRoot, oldType, HoldRoot, Hold,
      (D.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep, htype⟩

/-- The call-template row produced beside a hypothesis prefix, indexed by
the same constructions as `InductionHypothesisTypesPrefix`.  `rooted`
additionally records the recursor-context well-formedness of each call's
`loopUArgs` root and the up-set `rootScope` in it. -/
structure CallTemplatesMatchPrefix
    (H : InductionHypothesisTypesPrefix stats recInfos fieldRoot c
      fields hypotheses)
    (rootScope : FVarId → Prop)
    (calls : Array AddInductive.RecCallTemplate) : Prop where
  size_eq : calls.size = hypotheses.size
  entry : ∀ j (_hj : j < hypotheses.size),
    ∃ root sourceType,
      ∃ (O : InductionHypothesisType stats recInfos root
        fields[j]! sourceType),
        ∃ (D : FVarDeclAt c hypotheses j),
          BindingContextLE fieldRoot root ∧
          D.type = (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) ∧
          calls[j]! = {
            major := fields[j]!
            args := O.args
            lctx := O.current.lctx
            targetTypeIdx := O.ownerIdx
            targetIndices := O.exposedType.getAppArgs[stats.params.size:]
            template := O.current.lctx.mkLambda O.args <|
              (mkAppN (.bvar O.args.size)
                O.exposedType.getAppArgs[stats.params.size:]).app
                  (mkAppN fields[j]! O.args) }
  rooted : ∀ j (_hj : j < hypotheses.size),
    ∃ root sourceType,
      ∃ (recLparams : List Name) (Rroot : RecursorContextWF root recLparams)
        (O : InductionHypothesisType stats recInfos root
          fields[j]! sourceType)
        (D : FVarDeclAt c hypotheses j),
        BindingContextLE fieldRoot root ∧
        IsFVarUpSet rootScope Rroot.mlctx.vlctx ∧
        D.type = (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) ∧
        calls[j]! = {
          major := fields[j]!
          args := O.args
          lctx := O.current.lctx
          targetTypeIdx := O.ownerIdx
          targetIndices := O.exposedType.getAppArgs[stats.params.size:]
          template := O.current.lctx.mkLambda O.args <|
            (mkAppN (.bvar O.args.size)
              O.exposedType.getAppArgs[stats.params.size:]).app
                (mkAppN fields[j]! O.args) }

theorem CallTemplatesMatchPrefix.empty
    (H : InductionHypothesisTypesPrefix stats recInfos c c fields #[])
    (rootScope : FVarId → Prop) :
    CallTemplatesMatchPrefix H rootScope #[] where
  size_eq := rfl
  entry j hj := by simp at hj
  rooted j hj := by simp at hj

theorem CallTemplatesMatchPrefix.pushCurrent
    {H : InductionHypothesisTypesPrefix stats recInfos fieldRoot c
      fields hypotheses}
    {rootScope : FVarId → Prop}
    {calls : Array AddInductive.RecCallTemplate}
    (Hcalls : CallTemplatesMatchPrefix H rootScope calls)
    (Hc : BindingContextWF c)
    (name : Name) (sourceType : Expr) (bi : BinderInfo)
    (hnext : hypotheses.size < fields.size)
    (Hroot : BindingContextLE fieldRoot root)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    (hup : IsFVarUpSet rootScope Rroot.mlctx.vlctx)
    (O : InductionHypothesisTypeAt stats recInfos root
      fields[hypotheses.size]! sourceType)
    (call : AddInductive.RecCallTemplate)
    (hcall : call = {
      major := fields[hypotheses.size]!
      args := O.args
      lctx := O.current.lctx
      targetTypeIdx := O.ownerIdx
      targetIndices := O.exposedType.getAppArgs[stats.params.size:]
      template := O.current.lctx.mkLambda O.args <|
        (mkAppN (.bvar O.args.size)
          O.exposedType.getAppArgs[stats.params.size:]).app
            (mkAppN fields[hypotheses.size]! O.args) }) :
    CallTemplatesMatchPrefix
      (H.pushCurrent Hc name sourceType bi hnext Hroot ⟨O⟩) rootScope
      (calls.push call) := by
  let ty := (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withLocalDecl c Hc name ty bi
  let D : FVarDeclAt c'
      (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) hypotheses.size := {
    inBounds := by simp
    fvar := ⟨c.ngen.curr⟩
    expression := by simp
    member := by
      simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
        List.map_cons, LocalDecl.fvarId, List.mem_cons]
      exact Or.inl trivial
    index := c.lctx.decls.size
    userName := name
    type := ty
    binderInfo := bi
    kind := .default
    declaration := by
      simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
        Hc.wf.map_wf.find?_insert] }
  have hlast : (calls.push call)[hypotheses.size]! = call := by
    rw [show hypotheses.size = calls.size from Hcalls.size_eq.symm]
    simp
  have hpush : ∀ j, j < hypotheses.size → (calls.push call)[j]! = calls[j]! := by
    intro j hjOld
    have hjCalls : j < calls.size := by rw [Hcalls.size_eq]; exact hjOld
    simp only [Array.getElem!_eq_getD]
    unfold Array.getD
    rw [dif_pos (by simp; omega), dif_pos hjCalls]
    exact Array.getElem_push_lt hjCalls
  refine {
    size_eq := by simpa using congrArg Nat.succ Hcalls.size_eq
    entry := ?_
    rooted := ?_ }
  · intro j hj
    by_cases hilast : j = hypotheses.size
    · subst j
      refine ⟨root, sourceType, O.toMinor, D, Hroot, rfl, ?_⟩
      rw [hlast, hcall]
      rfl
    · have hjOld : j < hypotheses.size := by
        have : j < hypotheses.size + 1 := by simpa using hj
        omega
      rcases Hcalls.entry j hjOld with
        ⟨oldRoot, oldType, Oold, Dold, HoldRoot, htype, hcallOld⟩
      refine ⟨oldRoot, oldType, Oold,
        (Dold.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep,
        HoldRoot, htype, ?_⟩
      rw [hpush j hjOld]
      exact hcallOld
  · intro j hj
    by_cases hilast : j = hypotheses.size
    · subst j
      refine ⟨root, sourceType, recLparams, Rroot, O.toMinor, D, Hroot, hup,
        rfl, ?_⟩
      rw [hlast, hcall]
      rfl
    · have hjOld : j < hypotheses.size := by
        have : j < hypotheses.size + 1 := by simpa using hj
        omega
      rcases Hcalls.rooted j hjOld with
        ⟨oldRoot, oldType, oldLparams, Rold, Oold, Dold, HoldRoot, hupOld,
          htype, hcallOld⟩
      refine ⟨oldRoot, oldType, oldLparams, Rold, Oold,
        (Dold.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep,
        HoldRoot, hupOld, htype, ?_⟩
      rw [hpush j hjOld]
      exact hcallOld

/-- Recursive-call syntax together with the inner binding context used
to close its higher-order arguments. -/
structure RecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context) (field value : Expr) where
  exposedType : Expr
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats exposedType = some ownerIdx
  localArgs : Array Expr
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  arguments_bound : FVarArrayAfter root current localArgs
  value_eq :
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
    let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
      minors
    value = (current.lctx.mkLambda localArgs <|
      (mkAppN (.bvar localArgs.size) indices).app
        (mkAppN field localArgs)).instantiate1 recursor

/-- Typing of one generated recursive call before installation.  The
template-producing minor pass declares hypotheses for earlier recursive fields,
so the higher-order argument telescope is recent relative to the root of its
own `loopUArgs` run.  The common constructor-field root remains separate. -/
structure TypedRecursiveCall
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (decl : VInductDecl) (depth : Nat) (field value : Expr) where
  generated : RecursiveCall indTypes stats motives minors lvls
    root field value
  current_context : RecursorContextWF generated.current recLparams
  recent : RecursorFVarSuffix R current_context
    generated.localArgs
  rootScope : FVarId → Prop
  /-- Source scope established by the successful recursive-field
  traversal.  It is a fact about that run, not a premise supplied by the caller. -/
  exposed_scope : generated.exposedType.FVarsIn
    (fun fv => fv ∈ recent.fvars ∨ rootScope fv)
  current_scope_up : IsFVarUpSet
    (fun fv => fv ∈ recent.fvars ∨ rootScope fv)
    current_context.mlctx.vlctx
  /-- The call-local arguments were opened in the checker context too, above
  a prefix of the root checker context. -/
  chkAgree : ∃ hn : generated.localArgs.size ≤ current_context.chk.length,
    MLCtxTopAgree current_context.mlctx current_context.chk
      generated.localArgs.size ∧
      ∃ j hj ty₀, current_context.chk.dropN generated.localArgs.size hn =
          R.chk.dropN j hj ∧
        (∃ k, (R.chk.dropN j hj).fvarList = R.chk.fvarList.take k ∧
          R.chk.fvarList[k]? = some field.fvarId!) ∧
        TrExprS R.venv recLparams (R.chk.dropN j hj).vlctx
          (root.lctx.get! field.fvarId!).type ty₀ ∧
        R.venv.IsType recLparams.length (R.chk.dropN j hj).vlctx.toCtx ty₀ ∧
        ∃ t₀, TrExpr current_context.venv recLparams
          current_context.chk.vlctx generated.exposedType t₀ ∧
        current_context.venv.IsType recLparams.length
          current_context.chk.vlctx.toCtx t₀ ∧
        current_context.venv.IsDefEqU recLparams.length
          (R.chk.dropN j hj).vlctx.toCtx ty₀
          (current_context.chk.mkForall' generated.localArgs.size hn t₀)
  exposedTarget : VExpr
  exposed_translation : TrExprS current_context.venv recLparams
    current_context.mlctx.vlctx generated.exposedType exposedTarget
  terminalTarget : VExpr
  exposed_defeq : current_context.venv.IsDefEqU recLparams.length
    current_context.mlctx.vlctx.toCtx exposedTarget terminalTarget
  terminal_type : current_context.venv.IsType recLparams.length
    current_context.mlctx.vlctx.toCtx terminalTarget
  appliedFieldTarget : VExpr
  applied_field_translation : TrExprS current_context.venv recLparams
    current_context.mlctx.vlctx
    (mkAppN field generated.localArgs) appliedFieldTarget
  applied_field_typing : current_context.venv.HasType recLparams.length
    current_context.mlctx.vlctx.toCtx appliedFieldTarget terminalTarget
  /-- The validated inductive application produced at this call site. -/
  validated : RecursorValidatedIndAppAt current_context.venv recLparams
    current_context.mlctx.vlctx stats decl
    (depth + generated.localArgs.size) generated.exposedType exposedTarget
    generated.ownerIdx
  /-- The call-local telescope closed and restricted to the common
  constructor-field context.  In the template-producing minor pass this removes
  the irrelevant hypotheses installed for earlier recursive fields. -/
  commonDomains : List VExpr
  commonDomains_length : commonDomains.length = generated.localArgs.size
  common_exposed_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (generated.current.lctx.mkForall generated.localArgs
      generated.exposedType)
    (VExpr.wrapForalls commonDomains exposedTarget)
  common_exposed_type : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapForalls commonDomains exposedTarget)
  common_applied_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (generated.current.lctx.mkLambda generated.localArgs
      (mkAppN field generated.localArgs))
    (VExpr.wrapLams commonDomains appliedFieldTarget)
  common_applied_typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapLams commonDomains appliedFieldTarget)
    (VExpr.wrapForalls commonDomains exposedTarget)
  /-- Recursive-domain judgment from positivity.  These facts
  are produced by the successful field check and discharge source closedness
  obligations without rerunning the checker. -/
  fieldTarget : VExpr
  domain : VExpr
  field_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    field fieldTarget
  field_typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    fieldTarget domain
  owner_lt : generated.ownerIdx < decl.types.length
  recursive : decl.RecursiveArgAtTarget R.venv recLparams.length
    (decl.types[generated.ownerIdx]'owner_lt).name
    R.mlctx.vlctx.toCtx depth domain

/-- The higher-order argument suffix of a recursive constructor field,
closed back to the rule's field context.  The exposed result type and the
eta-expanded field use one shared domain list; this is the typed major premise
later supplied to the recursively selected generated recursor. -/
structure TypedRecursiveCall.AppliedFieldTelescope
    {R : RecursorContextWF root recLparams}
    (S : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) where
  domains : List VExpr
  domains_length : domains.length = S.generated.localArgs.size
  exposed_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (S.generated.current.lctx.mkForall S.generated.localArgs
      S.generated.exposedType)
    (VExpr.wrapForalls domains S.exposedTarget)
  exposed_type : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapForalls domains S.exposedTarget)
  applied_translation : TrExprS R.venv recLparams R.mlctx.vlctx
    (S.generated.current.lctx.mkLambda S.generated.localArgs
      (mkAppN field S.generated.localArgs))
    (VExpr.wrapLams domains S.appliedFieldTarget)
  applied_typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    (VExpr.wrapLams domains S.appliedFieldTarget)
    (VExpr.wrapForalls domains S.exposedTarget)

/-- The recursive field syntax recorded by the successful traversal has no
ambient loose variables. -/
theorem TypedRecursiveCall.fieldClosed
    {R : RecursorContextWF root recLparams}
    (S : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    field.looseBVarRange' = 0 := by
  have hclosed := S.field_translation.closed
  rw [R.mlctx.noBV] at hclosed
  exact hclosed.looseBVarRange_zero

/-- Recover the shared higher-order field telescope from the facts
already established by `loopUArgs`.  The executable normalizer may expose a
definitionally equal terminal type, so it is transported back to the
syntax translation before the suffix is closed. -/
def TypedRecursiveCall.appliedFieldTelescope
    {R : RecursorContextWF root recLparams}
    (S : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    S.AppliedFieldTelescope where
  domains := S.commonDomains
  domains_length := S.commonDomains_length
  exposed_translation := S.common_exposed_translation
  exposed_type := S.common_exposed_type
  applied_translation := S.common_applied_translation
  applied_typing := S.common_applied_typing

def RecursiveCall.body
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let (typeIdx, indices) := AddInductive.getIIndices stats H.exposedType
  let recursor := .const (Lean.mkRecName indTypes[typeIdx]!.name) lvls
  let recursor := mkAppN (mkAppN (mkAppN recursor stats.params) motives)
    minors
  let templateBody := (mkAppN (.bvar H.localArgs.size) indices).app
    (mkAppN field H.localArgs)
  (templateBody.abstractN H.arguments_bound.fvars).instantiate1'
    recursor H.localArgs.size

theorem RecursiveCall.value_eq_body
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) :
    value = (H.current.lctx.mkLambda H.localArgs <|
      let indices := (AddInductive.getIIndices stats H.exposedType).2
      (mkAppN (.bvar H.localArgs.size) indices).app
        (mkAppN field H.localArgs)).instantiate1
          (mkAppN (mkAppN (mkAppN
            (.const (Lean.mkRecName
              indTypes[(AddInductive.getIIndices stats H.exposedType).1]!.name)
              lvls) stats.params) motives) minors) := by
  simpa using H.value_eq

/-- The lambda telescope closed by one generated recursive call. -/
theorem RecursiveCall.lambdaTelescope
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) :
    Expr.LambdaTelescope value H.localArgs.size
      H.body := by
  rcases H with
    ⟨exposedType, ownerIdx, howner, localArgs, current, Hwf, Hle, Hargs,
      Hvalue⟩
  let templateBody : Expr :=
    let (typeIdx, indices) := AddInductive.getIIndices stats exposedType
    (mkAppN (.bvar localArgs.size) indices).app (mkAppN field localArgs)
  let recursor : Expr :=
    let (typeIdx, _) := AddInductive.getIIndices stats exposedType
    mkAppN (mkAppN (mkAppN
      (.const (Lean.mkRecName indTypes[typeIdx]!.name) lvls) stats.params)
      motives) minors
  have Hvalue' : value =
      (current.lctx.mkLambda localArgs templateBody).instantiate1 recursor := by
    simpa [templateBody, recursor] using Hvalue
  change Expr.LambdaTelescope value localArgs.size
    ((templateBody.abstractN Hargs.fvars).instantiate1'
      recursor localArgs.size)
  rw [Hvalue']
  let Hselection :=
    Hargs.toFVarArrayIn.toCDeclArray Hwf
  have Hfvars : Hselection.fvars = Hargs.fvars := rfl
  rcases Hselection with ⟨fvars, rfl, Hdecl⟩
  rw [← Hfvars]
  have Htemplate := LocalContext.mkLambda_fvars_lambdaTelescopeN
    (body := templateBody) Hdecl
  simpa using Htemplate.instantiate1 recursor

/-- The eta-expanded field is closed with respect to loose variables
(`TypedRecursiveCall.fieldClosed`).  Instantiating the outer
recursor placeholder therefore changes only the call template, while
preserving its executable higher-order lambda prefix. -/
theorem TypedRecursiveCall.sameAppliedFieldLambdaPrefix
    (H : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    Expr.SameLambdaPrefix H.generated.localArgs.size value
      (H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)) := by
  let Hselection :=
    H.generated.arguments_bound.toFVarArrayIn.toCDeclArray
      H.generated.current_wf
  let templateBody : Expr :=
    let indices :=
      (AddInductive.getIIndices stats H.generated.exposedType).2
    (mkAppN (.bvar H.generated.localArgs.size) indices).app
      (mkAppN field H.generated.localArgs)
  let applied := H.generated.current.lctx.mkLambda H.generated.localArgs
    (mkAppN field H.generated.localArgs)
  have Hsame : Expr.SameLambdaPrefix H.generated.localArgs.size
      (H.generated.current.lctx.mkLambda H.generated.localArgs templateBody)
      applied :=
    Hselection.sameLambdaPrefix H.generated.arguments_bound.nodup
      templateBody (mkAppN field H.generated.localArgs)
  let recursor := mkAppN (mkAppN (mkAppN
    (.const (Lean.mkRecName
      indTypes[(AddInductive.getIIndices stats H.generated.exposedType).1]!.name)
      lvls) stats.params) motives) minors
  have Hsame' := Hsame.instantiate1 recursor
  have happliedClosed : Closed applied := by
    have hclosed := H.appliedFieldTelescope.applied_translation.closed
    simpa [applied, R.mlctx.noBV] using hclosed
  have happliedInst : applied.instantiate1 recursor = applied :=
    by simpa [Expr.instantiate1_eq] using
      (Expr.instantiate1_eq_self
        (a := recursor) happliedClosed.looseBVarRange_zero)
  rw [happliedInst] at Hsame'
  have Hsame'' : Expr.SameLambdaPrefix H.generated.localArgs.size
      ((H.generated.current.lctx.mkLambda H.generated.localArgs <|
        let indices :=
          (AddInductive.getIIndices stats H.generated.exposedType).2
        (mkAppN (.bvar H.generated.localArgs.size) indices).app
          (mkAppN field H.generated.localArgs)).instantiate1 recursor)
      (H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)) := by
    simpa [templateBody, recursor, applied] using Hsame'
  exact Eq.mp (congrArg
    (fun source => Expr.SameLambdaPrefix H.generated.localArgs.size source
      (H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)))
    H.generated.value_eq_body).symm Hsame''

/-- Closing a generated call over an additional rule-level binder list
preserves its higher-order lambda arity. The residual records the necessary
binder-depth shift explicitly, avoiding any assumption that translation and
simultaneous abstraction commute definitionally. -/
theorem RecursiveCall.outerAbstractedLambdaTelescope
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) :
    Expr.LambdaTelescope (value.abstractList binders)
      H.localArgs.size
      (H.body.abstractList binders H.localArgs.size) := by
  simpa using H.lambdaTelescope.abstractList binders

/-- Simultaneous abstraction preserves the generated recursor spine and
turns the freshly opened local arguments into the bvar spine
on the recursive field. -/
theorem RecursiveCall.abstractedBody_eq
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) :
    let (typeIdx, indices) :=
      AddInductive.getIIndices stats H.exposedType
    let recursor := mkAppN (mkAppN (mkAppN
      (.const (Lean.mkRecName indTypes[typeIdx]!.name) lvls)
      stats.params) motives) minors
    let abstractedFn :=
      mkAppN ((Expr.bvar H.localArgs.size).abstractN H.arguments_bound.fvars)
        (indices.map fun e => e.abstractN H.arguments_bound.fvars)
    let abstractedMajor :=
      mkAppN (field.abstractN H.arguments_bound.fvars)
        (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
          Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray
    H.body =
      (abstractedFn.instantiate1' recursor H.localArgs.size).app
        (abstractedMajor.instantiate1' recursor H.localArgs.size) := by
  rcases hindices : AddInductive.getIIndices stats H.exposedType with
    ⟨typeIdx, indices⟩
  have hlocal :
      H.localArgs.map (fun e =>
        e.abstractN H.arguments_bound.fvars) =
      (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      H.localArgs.map (fun e =>
          e.abstractN H.arguments_bound.fvars) =
          ((H.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractN H.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractN H.arguments_bound.fvars)
            H.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractN_fvarArray
          H.arguments_bound.fvars 0 H.arguments_bound.nodup
  simp only [RecursiveCall.body, hindices,
    Expr.abstractN_app, Expr.abstractN_mkAppN]
  rw [hlocal]
  rfl

def RecursiveCall.recursorName
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) : Name :=
  Lean.mkRecName indTypes[(AddInductive.getIIndices stats H.exposedType).1]!.name

/-- The owner returned by the successful validation branch is exactly the
family index used by the partial executable helper. -/
theorem RecursiveCall.recursorName_eq_owner
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.recursorName = Lean.mkRecName indTypes[H.ownerIdx]!.name := by
  simp only [RecursiveCall.recursorName,
    checkPositivityStep.getIIndices.fst_eq_of_valid H.owner_valid]

def RecursiveCall.abstractedRecursor
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let indices := (AddInductive.getIIndices stats H.exposedType).2
  let recursor := mkAppN (mkAppN (mkAppN
    (.const H.recursorName lvls) stats.params) motives) minors
  (mkAppN ((Expr.bvar H.localArgs.size).abstractN H.arguments_bound.fvars)
    (indices.map fun e => e.abstractN H.arguments_bound.fvars)).instantiate1'
      recursor H.localArgs.size

def RecursiveCall.abstractedMajor
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) : Expr :=
  let recursor := mkAppN (mkAppN (mkAppN
    (.const H.recursorName lvls) stats.params) motives) minors
  (mkAppN (field.abstractN H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray).instantiate1'
        recursor H.localArgs.size

def RecursiveCall.outerAbstractedRecursor
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) : Expr :=
  H.abstractedRecursor.abstractList binders H.localArgs.size

def RecursiveCall.outerAbstractedMajor
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) (binders : List FVarId) : Expr :=
  H.abstractedMajor.abstractList binders H.localArgs.size

/-- The eta-expanded recursive field used as the generated recursor's major
premise closes over the same fresh higher-order arguments as the call
itself.  Its residual is `abstractedMajor`, rather than the complete call
body of `lambdaTelescope`. -/
theorem RecursiveCall.appliedFieldLambdaTelescope
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldClosed : field.looseBVarRange' = 0) :
    Expr.LambdaTelescope
      (H.current.lctx.mkLambda H.localArgs (mkAppN field H.localArgs))
      H.localArgs.size H.abstractedMajor := by
  let Hselection :=
    H.arguments_bound.toFVarArrayIn.toCDeclArray H.current_wf
  have Hdecl := Hselection.declarations
  have HselectionFvars : Hselection.fvars =
      H.arguments_bound.fvars := rfl
  rw [HselectionFvars] at Hdecl
  have Hexpressions := H.arguments_bound.expressions
  rw [Hexpressions]
  have Htel := LocalContext.mkLambda_fvars_lambdaTelescopeN
    (body := mkAppN field
      (H.arguments_bound.fvars.map Expr.fvar).toArray) Hdecl
  have hlocal :
      (H.arguments_bound.fvars.map Expr.fvar).toArray.map (fun e =>
        e.abstractN H.arguments_bound.fvars) =
      (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar
          (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    simpa using Expr.abstractN_fvarArray
      H.arguments_bound.fvars 0 H.arguments_bound.nodup
  have hsize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  let major := mkAppN (field.abstractN H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray
  have hfieldRange :
      (field.abstractN H.arguments_bound.fvars).looseBVarRange' ≤
        H.arguments_bound.fvars.length := by
    have Hrange := Expr.abstractN_looseBVarRange_le
      (e := field) (fvs := H.arguments_bound.fvars) (k := 0)
    simpa [hfieldClosed] using Hrange
  have hmajorRange : major.looseBVarRange' ≤
      H.arguments_bound.fvars.length := by
    apply Expr.mkAppN_looseBVarRange_le hfieldRange
    intro arg harg
    rcases Array.mem_iff_getElem.mp harg with ⟨i, hi, rfl⟩
    have hi' : i < H.arguments_bound.fvars.length := by simpa using hi
    simp only [List.getElem_toArray, List.getElem_ofFn,
      Lean.Expr.looseBVarRange']
    omega
  have hmajorInst : major.instantiate1'
      (mkAppN (mkAppN (mkAppN (.const H.recursorName lvls)
        stats.params) motives) minors) H.localArgs.size = major := by
    apply Expr.instantiate1'_eq_self
    rw [hsize]
    exact hmajorRange
  have habstractedMajor : H.abstractedMajor = major := by
    change major.instantiate1'
      (mkAppN (mkAppN (mkAppN (.const H.recursorName lvls)
        stats.params) motives) minors) H.localArgs.size = major
    exact hmajorInst
  rw [habstractedMajor]
  simpa [Expr.abstractN_mkAppN, hlocal, major] using Htel

/-- When the field expression is closed, the instantiated
template major reduces to the ordinary eta-expanded field residual. -/
theorem RecursiveCall.abstractedMajor_eq_of_closed
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldClosed : field.looseBVarRange' = 0) :
    H.abstractedMajor =
      mkAppN (field.abstractN H.arguments_bound.fvars)
        (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
          Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray := by
  let major := mkAppN (field.abstractN H.arguments_bound.fvars)
    (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
      Expr.bvar (H.arguments_bound.fvars.length - 1 - i))).toArray
  change major.instantiate1'
    (mkAppN (mkAppN (mkAppN (.const H.recursorName lvls)
      stats.params) motives) minors) H.localArgs.size = major
  apply Expr.instantiate1'_eq_self
  have hsize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  rw [hsize]
  apply Expr.mkAppN_looseBVarRange_le
  · have Hrange := Expr.abstractN_looseBVarRange_le
      (e := field) (fvs := H.arguments_bound.fvars) (k := 0)
    simpa [hfieldClosed] using Hrange
  · intro arg harg
    rcases Array.mem_iff_getElem.mp harg with ⟨i, hi, rfl⟩
    have hi' : i < H.arguments_bound.fvars.length := by simpa using hi
    simp only [List.getElem_toArray, List.getElem_ofFn,
      Lean.Expr.looseBVarRange']
    omega

/-- Closing the shared higher-order prefix over the surrounding rule binders
preserves its literal equality. -/
theorem TypedRecursiveCall.sameOuterAppliedFieldLambdaPrefix
    (H : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) (binders : List FVarId) :
    Expr.SameLambdaPrefix H.generated.localArgs.size
      (value.abstractList binders)
      ((H.generated.current.lctx.mkLambda H.generated.localArgs
        (mkAppN field H.generated.localArgs)).abstractList binders) := by
  exact H.sameAppliedFieldLambdaPrefix.abstractList binders

/-- A root free variable is untouched by the fresh call-local binders.
Abstracting it over the surrounding rule telescope below those locals is
therefore exactly weakening its ordinary rule abstraction. -/
theorem RecursiveCall.outerAbstractedFVar_eq_lift_of_fresh
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfresh : fv ∉ H.arguments_bound.fvars)
    (hbinders : binders.Nodup) :
    ((Expr.fvar fv).abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size =
      ((Expr.fvar fv).abstractList binders).liftLooseBVars'
        0 H.localArgs.size := by
  rw [Expr.abstractList_fvar_of_not_mem hfresh]
  simpa using Expr.abstractList_add_eq_liftLooseBVars
    (e := .fvar fv) (fvars := binders) (depth := 0)
    (extra := H.localArgs.size) (by trivial) hbinders

theorem RecursiveCall.outerAbstractedRootFVar_eq_lift
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (hroot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) :
    ((Expr.fvar fv).abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size =
      ((Expr.fvar fv).abstractList binders).liftLooseBVars'
        0 H.localArgs.size := by
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hroot
  exact H.outerAbstractedFVar_eq_lift_of_fresh hfresh hbinders

/-- Array form for binders declared in a context other than the call root.
The traversal supplies disjointness from the temporary call-local arguments. -/
theorem RecursiveCall.outerAbstractedBoundArray_eq_lift_of_fresh
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (B : FVarArrayIn c xs)
    (hfresh : ∀ fv ∈ B.fvars, fv ∉ H.arguments_bound.fvars)
    (hbinders : binders.Nodup) :
    xs.map (fun arg =>
        (arg.abstractList H.arguments_bound.fvars).abstractList
          binders H.localArgs.size) =
      xs.map (fun arg =>
        (arg.abstractList binders).liftLooseBVars' 0 H.localArgs.size) := by
  apply Array.ext
  · simp
  · intro j hleft hright
    have hj : j < xs.size := by simpa using hleft
    rcases B.getElem_eq_fvar j hj with ⟨hjFvars, harg⟩
    simp only [Array.getElem_map]
    rw [harg]
    exact H.outerAbstractedFVar_eq_lift_of_fresh
      (hfresh B.fvars[j] (List.getElem_mem hjFvars)) hbinders

def RecursiveCall.localIndices
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) : List Nat :=
  List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
    H.arguments_bound.fvars.length - 1 - i

/-- Alpha-normalized shape of the recursive-result `loopUArgs` run.  It is
the rule-construction counterpart of
`InductionHypothesisType.replayTrace`. -/
def RecursiveCall.replayTrace
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (fieldBinders : List FVarId) : InductionHypothesisShape where
  ownerIdx := H.ownerIdx
  localArity := H.localArgs.size
  localTelescope :=
    (H.current.lctx.mkForall H.localArgs (.sort .zero)).abstractList
      fieldBinders
  motive :=
    (motives[H.ownerIdx]!.abstractList
      H.arguments_bound.fvars).abstractList fieldBinders H.localArgs.size
  indices :=
    ((H.exposedType.getAppArgs[stats.params.size:] : Array Expr).map
      fun index =>
        (index.abstractList H.arguments_bound.fvars).abstractList
          fieldBinders H.localArgs.size)

/-- The rule-construction counterpart of
`InductionHypothesisType.outerAbstractedMotiveApp`. -/
def RecursiveCall.outerAbstractedMotiveApp
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (fieldBinders : List FVarId) : Expr :=
  Expr.app
    (mkAppN (H.replayTrace fieldBinders).motive
      (H.replayTrace fieldBinders).indices)
    (H.outerAbstractedMajor fieldBinders)

theorem RecursiveCall.outerAbstractedMotiveApp_eq
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (fieldBinders : List FVarId)
    (hfieldClosed : field.looseBVarRange' = 0) :
    let indices : Array Expr :=
      H.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN motives[H.ownerIdx]! indices)
      (mkAppN field H.localArgs)
    (motiveApp.abstractList H.arguments_bound.fvars).abstractList
        fieldBinders H.localArgs.size =
      H.outerAbstractedMotiveApp fieldBinders := by
  dsimp only
  have hlocal :
      H.localArgs.map (fun e =>
        e.abstractList H.arguments_bound.fvars) =
        (List.ofFn (fun i : Fin H.arguments_bound.fvars.length =>
          Expr.bvar
            (H.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      H.localArgs.map (fun e =>
          e.abstractList H.arguments_bound.fvars) =
          ((H.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractList H.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractList H.arguments_bound.fvars)
            H.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          H.arguments_bound.fvars 0 H.arguments_bound.nodup
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hlocal]
  unfold RecursiveCall.outerAbstractedMotiveApp
  unfold RecursiveCall.outerAbstractedMajor
  rw [H.abstractedMajor_eq_of_closed hfieldClosed,
    Expr.abstractN_eq_abstractList H.arguments_bound.nodup field 0 (Nat.le_of_eq hfieldClosed)]
  simp [
    RecursiveCall.replayTrace,
    Expr.abstractList_mkAppN, Array.map_map, Array.map_ofFn, Function.comp_def]

end VerifyInductive
end Lean4Lean
