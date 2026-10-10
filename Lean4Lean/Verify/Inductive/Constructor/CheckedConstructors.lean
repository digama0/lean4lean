import Lean4Lean.Verify.Inductive.Constructor.ParameterPrefixes

/-! The constructor loops of `checkConstructors` refine the abstract constructor
shapes and types and retain the checked common-parameter prefix and tail of
every constructor (`CheckedConstructors`), which the checked formation and the
recursor construction reuse. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkConstructors.loopCtors

/-- The executable constructor loop refines the abstract constructor shapes
and types while accumulating the exact checked common-parameter prefix and
tail of each constructor beside the abstract shape/type prefix. -/
theorem refinesTypeWithReplay
    {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {target : VInductiveType}
    {sourceEnv envTypes : VEnv} {params : List VExpr}
    {source : InductiveType}
    (Q : List (List Bool) → Prop)
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams source target)
    (Hprefix : IndexedPrefix target.ctors.length
      (fun i _ => CtorTypeChecked envTypes decl params target target.ctors[i]) ctorIdx)
    (Hreplay : IndexedPrefix source.ctors.length
      (fun i _ => ConstructorParamPrefixAt stats source.ctors[i]) ctorIdx)
    {tailScope : VLCtx} {classes : List (List Bool)}
    (hclasses : classes.length = ctorIdx)
    (Htails : IndexedPrefix source.ctors.length
      (fun i _ => CheckedConstructorTailAt Hc.venv c.lparams tailScope stats decl target
        source.ctors[i] classes[i]!) ctorIdx)
    (Hshape : ∀ i (hsource : i < source.ctors.length)
      (htarget : i < target.ctors.length),
      TrSourceConstRaw envTypes c.lparams source.ctors[i].name
        source.ctors[i].type target.ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        source.ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        source.ctors[i].name targetIdx source.ctors[i].type 0
        c.fuel.inductiveFuel c).WF fun fields => ∃ tail tailTarget,
          ParameterPrefix stats 0 source.ctors[i].type tail ∧
          ∃ sourceDomains,
          CheckedConstructorParameterPrefix Hc.venv c.lparams stats
            source.ctors[i].type stats.params.size tail tailScope
            sourceDomains ∧
          TrExprS Hc.venv c.lparams tailScope tail tailTarget ∧
          ConstructorTailCertificate Hc.venv decl target
            tailScope.toCtx 0 tailTarget fields ∧
          TrSourceConstRaw Hc.venv c.lparams source.ctors[i].name
            source.ctors[i].type target.ctors[i] ∧
          Nonempty
            (checkInductiveTypes.loopType.ScopedHeaderTelescope
              Hc.venv c.lparams
              (constructorTelescopeTarget target.ctors[i]) tailScope
              tailTarget stats.params.size 0) ∧
          decl.CtorShape envTypes params target target.ctors[i] ∧
          envTypes.IsType decl.uvars [] target.ctors[i].type ∧
          ∃ k, Expr.ForallSpine source.ctors[i].type k)
    (Hfinish : ∀ classes',
      (∀ i (hi : i < target.ctors.length),
        CtorTypeChecked envTypes decl params target target.ctors[i]) →
      (∀ i (hi : i < source.ctors.length), ConstructorParamPrefixAt stats source.ctors[i]) →
      FamilyConstructorTails Hc.venv c.lparams tailScope stats decl target
        source.ctors classes' →
      Q classes') :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF fun rest => Q (classes ++ rest) := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepPrefix.checkedWF (stats := stats) (isUnsafe := isUnsafe)
      (targetIdx := targetIdx) (Q := fun rest => Q (classes ++ rest)) Hc hidx
    intro checkedType type' checkedType' hchecked
    have Hchecked := Hshape ctorIdx hidx htarget Hctor checkedType type'
      checkedType' hchecked
    exact Hchecked.mono fun fields HcheckedCtor => by
      rcases HcheckedCtor with
        ⟨tail, tailTarget, Hparam, sourceDomains, Hcomparisons,
          Htranslated, Htail, HctorNarrow,
          Hsynthesis, HctorShape, HctorType, Hspine⟩
      have HtailReplay : CheckedConstructorTailAt Hc.venv c.lparams
          tailScope stats decl target source.ctors[ctorIdx] fields :=
        ⟨target.ctors[ctorIdx], tail, tailTarget, sourceDomains,
          List.getElem_mem htarget, HctorNarrow, Hparam, Hcomparisons,
          Htranslated, Htail, Hsynthesis⟩
      exact (refinesTypeWithReplay Q Hc Htarget
        (Hprefix.push htarget ⟨HctorShape, HctorType⟩)
        (Hreplay.push hidx ⟨⟨tail, Hparam⟩, Hspine⟩) (classes := classes ++ [fields])
        (by simp [hclasses])
        (Htails.snoc (P := fun i _ fields => CheckedConstructorTailAt Hc.venv c.lparams
          tailScope stats decl target source.ctors[i] fields) hclasses hidx HtailReplay)
        Hshape Hfinish).mono fun rest h => by simpa using h
  · have heq : ctorIdx = source.ctors.length := by
      have := Hprefix.covered
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget]
        at this
      omega
    apply result.WF (Q := fun rest => Q (classes ++ rest)) hidx
    rw [List.append_nil]
    have hlength := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Htarget
    exact Hfinish classes (fun i hi => Hprefix.holds i (by omega) hi)
      (fun i hi => Hreplay.holds i (by omega) hi)
      ⟨by omega, fun i hi => Htails.holds i (by omega) hi⟩
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

/-- Mutual-family fold retaining every concrete constructor parameter replay. -/
theorem refinesBlockWithReplay
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType}
    {decl : VInductDecl} {sourceEnv envTypes : VEnv}
    {params : List VExpr}
    (Q : List (List (List Bool)) → Prop)
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv envTypes c.lparams)
      indTypes.toList decl.types)
    (Hprefix : IndexedPrefix decl.types.length
      (fun i hi => ∀ j (hj : j < (decl.types[i]'hi).ctors.length),
        CtorTypeChecked envTypes decl params (decl.types[i]'hi)
          ((decl.types[i]'hi).ctors[j]'hj)) targetIdx)
    (Hreplays : IndexedPrefix indTypes.size
      (fun i hi => ∀ j (hj : j < (indTypes[i]'hi).ctors.length),
        ConstructorParamPrefixAt stats ((indTypes[i]'hi).ctors[j]'hj)) targetIdx)
    {tailScope : VLCtx} {classes : List (List (List Bool))}
    (hsize : indTypes.size = decl.types.length)
    (hclasses : classes.length = targetIdx)
    (Htails : IndexedPrefix indTypes.size
      (fun i hi => FamilyConstructorTails Hc.venv c.lparams tailScope stats decl
        (decl.types[i]'(hsize ▸ hi)) (indTypes[i]'hi).ctors classes[i]!) targetIdx)
    (Hshape : ∀ targetIdx (hsource : targetIdx < indTypes.size)
      (htarget : targetIdx < decl.types.length)
      i (hctorSource : i < indTypes[targetIdx].ctors.length)
      (hctorTarget : i < decl.types[targetIdx].ctors.length),
      TrSourceConstRaw envTypes c.lparams indTypes[targetIdx].ctors[i].name
        indTypes[targetIdx].ctors[i].type decl.types[targetIdx].ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[targetIdx].ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[targetIdx].ctors[i].name targetIdx
        indTypes[targetIdx].ctors[i].type 0 c.fuel.inductiveFuel c).WF
        fun fields => ∃ tail tailTarget,
          ParameterPrefix stats 0 indTypes[targetIdx].ctors[i].type tail ∧
          ∃ sourceDomains,
          CheckedConstructorParameterPrefix Hc.venv c.lparams stats
            indTypes[targetIdx].ctors[i].type stats.params.size tail
            tailScope sourceDomains ∧
          TrExprS Hc.venv c.lparams tailScope tail tailTarget ∧
          ConstructorTailCertificate Hc.venv decl decl.types[targetIdx]
            tailScope.toCtx 0 tailTarget fields ∧
          TrSourceConstRaw Hc.venv c.lparams
            indTypes[targetIdx].ctors[i].name
            indTypes[targetIdx].ctors[i].type
            decl.types[targetIdx].ctors[i] ∧
          Nonempty
            (checkInductiveTypes.loopType.ScopedHeaderTelescope
              Hc.venv c.lparams
              (constructorTelescopeTarget
                decl.types[targetIdx].ctors[i]) tailScope tailTarget
              stats.params.size 0) ∧
          decl.CtorShape envTypes params decl.types[targetIdx]
            decl.types[targetIdx].ctors[i] ∧
          envTypes.IsType decl.uvars [] decl.types[targetIdx].ctors[i].type ∧
          ∃ k, Expr.ForallSpine indTypes[targetIdx].ctors[i].type k)
    (Hfinish : ∀ classes',
      (∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
        CtorTypeChecked envTypes decl params decl.types[i] decl.types[i].ctors[j]) →
      (∀ i (hi : i < indTypes.size) j (hj : j < indTypes[i].ctors.length),
        ConstructorParamPrefixAt stats indTypes[i].ctors[j]) →
      ConstructorTails Hc.venv c.lparams tailScope stats decl indTypes classes' →
      Q classes') :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF fun rest => Q (classes ++ rest) := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      omega
    have Htarget : TrInductiveTypeHeaders sourceEnv envTypes c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := List.forall₂_getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := fun rest => Q (classes ++ rest)) hidx
    refine (checkConstructors.loopCtors.refinesTypeWithReplay
      (Q := fun fields =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF fun rest => Q (classes ++ fields :: rest))
      Hc Htarget (decl := decl) (params := params) (tailScope := tailScope)
      .empty .empty (classes := []) rfl .empty ?_ ?_).mono
      fun fields h => by simpa using h
    · intro i hsource htarget' Hctor checkedType type' checkedType' hchecked
      exact Hshape targetIdx hidx htarget i hsource htarget' Hctor
        checkedType type' checkedType' hchecked
    · intro fields Htype Hrow HtailRow
      exact (refinesBlockWithReplay Q Hc Htypes
        (Hprefix.push htarget Htype) (Hreplays.push hidx Hrow) hsize
        (classes := classes ++ [fields]) (by simp [hclasses])
        (Htails.snoc (P := fun i hi fields => FamilyConstructorTails Hc.venv c.lparams
          tailScope stats decl (decl.types[i]'(hsize ▸ hi)) indTypes[i].ctors fields)
          hclasses hidx HtailRow)
        Hshape Hfinish).mono fun rest h => by simpa using h
  · have heq : targetIdx = indTypes.size := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      have := Hprefix.covered
      omega
    apply result.WF (Q := fun rest => Q (classes ++ rest)) hidx
    rw [List.append_nil]
    exact Hfinish classes (fun i hi j hj => Hprefix.holds i (by omega) hi j hj)
      (fun i hi j hj => Hreplays.holds i (by omega) hi j hj)
      (.ofAll hsize (by omega) fun i hi => Htails.holds i (by omega) hi)
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

/-- Constructor-checking output needed by both declaration installation and
the recursor construction.  The first component is the abstract formation
certificate; the others retain the exact concrete parameter prefixes and
tails of the kernel constructors, with the field classifications `classes`
returned by the executable check. -/
structure CheckedConstructors
    (sourceEnv : VEnv) (decl : VInductDecl) (envTypes : VEnv)
    (params : List VExpr) (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (Us : List Name)
    (scope : VLCtx) (classes : List (List (List Bool))) : Prop where
  checked : CheckedConstructorCertificate sourceEnv decl envTypes params
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  constructorTails : ConstructorTails envTypes Us scope stats
    decl indTypes classes

/-- Fold the end-to-end constructor theorem over the executable's nested
family/constructor loops.  This is the constructor-formation result used
by `FormationCertificate`; environment installation is intentionally a
separate obligation. -/
theorem checkConstructors.loopTypes.refinesChecked
    {decl : VInductDecl} {sourceEnv : VEnv}
    {params : List VExpr}
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams)
      indTypes.toList decl.types)
    (htypesAdded : sourceEnv.addConstVals decl.typeConstants = some Hc.venv)
    (Hmaterialized :
      checkInductiveTypes.loopInd.HeaderStatsWF
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hparams : Hmaterialized.headers.params = params)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hmaterialized.parameterScope Hc.chk.vlctx)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      Hc.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel ≈ .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel)
    (hlparams : c.lparams.Nodup) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0 c).WF
      (fun classes => CheckedConstructors sourceEnv decl Hc.venv
        params stats indTypes c.lparams Hmaterialized.parameterScope classes) := by
  have hlevels := Hmaterialized.levelParamsTranslation hlparams
  let Hsuffix := Hmaterialized.parameterSuffix
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped
      Hmaterialized
  have hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx := by
    change VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hmaterialized.parameterScope.toCtx
    subst params
    simpa [Hmaterialized.uvars] using Hmaterialized.paramsContext
  have hindTypesSize : indTypes.size = decl.types.length := by
    simpa using List.Forall₂.length_eq Htypes
  refine (checkConstructors.loopTypes.refinesBlockWithReplay
    (Q := fun classes => CheckedConstructors sourceEnv decl Hc.venv
      params stats indTypes c.lparams Hmaterialized.parameterScope classes)
    Hc Htypes (params := params) (tailScope := Hmaterialized.parameterScope)
    .empty .empty hindTypesSize (classes := []) rfl .empty ?_ ?_).mono
    fun _ h => by simpa using h
  · intro targetIdx hsource htarget ctorIdx hctorSource hctorTarget
      Hctor checkedType fullType checkedType' hchecked
    have Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := List.forall₂_getElem Htypes
        targetIdx (by simpa using hsource) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    have htargetUvars : decl.types[targetIdx].uvars = decl.uvars := by
      exact Htarget.header.uvars.trans Hstats.uvars
    have htargetLookup : Hc.venv.constants decl.types[targetIdx].name =
        some decl.types[targetIdx].toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      exact List.mem_map.mpr
        ⟨decl.types[targetIdx], List.getElem_mem htarget, rfl⟩
    have htargetWF : decl.types[targetIdx].toVConstant.WF Hc.venv :=
      Htarget.header.wf.mono (VEnv.addConstVals_le htypesAdded)
    have htargetShape : decl.TypeShape Hc.venv params
        decl.types[targetIdx] := by
      rw [← hparams]
      exact Hmaterialized.headers.typeShapes _ (List.getElem_mem htarget)
    have Hchecked := checkConstructors.loopCtor.refinesCtorShape
      (fuel := c.fuel.inductiveFuel) Hc Hsuffix Hstats halign hparamsCtx
      Hctor hchecked htarget rfl htargetUvars htargetLookup htargetWF
      htargetShape hconsume hlit hunsafe (hbound targetIdx htarget) hlevels
    exact Hchecked.mono fun fields Hresult => by
      rcases Hresult with
        ⟨tail, tailTarget, Hprefix, sourceDomains, Hcomparisons,
          Htranslated, HtailCertificate,
          Hsynthesis, Hshape, Htype, Hspine⟩
      have Hcomparisons' : CheckedConstructorParameterPrefix Hc.venv
          c.lparams stats indTypes[targetIdx].ctors[ctorIdx].type
          stats.params.size tail Hmaterialized.parameterScope
          sourceDomains := by
        change CheckedConstructorParameterPrefix Hc.venv c.lparams stats
          indTypes[targetIdx].ctors[ctorIdx].type stats.params.size tail
          Hsuffix.parameterDecls sourceDomains
        simpa [Hstats.params_size] using Hcomparisons
      exact ⟨tail, tailTarget, Hprefix, sourceDomains, Hcomparisons',
        Htranslated, HtailCertificate, Hctor, Hsynthesis, Hshape, Htype,
        Hspine⟩
  · intro classes Hcomplete Hreplays Htails
    exact {
      checked := .ofCtorTypesChecked Hcomplete
      parameterPrefixes := .ofAll Hreplays
      constructorTails := Htails }

end VerifyInductive
end Lean4Lean
