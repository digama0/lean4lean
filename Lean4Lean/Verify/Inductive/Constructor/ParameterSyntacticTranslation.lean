import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveFields
import Lean4Lean.Verify.Typing.RawShape

/-! The checked common-parameter prefix of each constructor determines its raw
syntactic shape (`CheckedConstructors.rawShapes`,
`CheckedConstructors.parameterShapes`) without inverting definitional
equality between forall types. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Exact raw translation state corresponding to a successful constructor
parameter prefix.  `rawScope` uses the domains selected by the structural
translation of the source constructor, while the executable's scope
uses the cached mutual parameters.  Keeping their pointwise local-context
conversion is what avoids forall injectivity. -/
def CheckedConstructorParameterPrefix.RawTranslation
    (_H : CheckedConstructorParameterPrefix env Us stats original
      i current checkedScope checkedDomains)
    (target : VExpr) : Prop :=
  ∃ rawScope domains residual,
    target = VExpr.wrapForalls domains residual ∧
    domains.length = i ∧
    rawScope.toCtx = domains.reverse ∧
    VLCtx.IsDefEq env Us.length rawScope checkedScope ∧
    TrExprS.IsUniqueCtx rawScope checkedScope ∧
    TrExprS env Us rawScope current residual

/-- Build the raw translation state directly from the exact structural
translation and the successful executable comparisons.  At each step
the two translations of the same concrete domain are compared directly;
the proof never inverts definitional equality between forall expressions. -/
theorem CheckedConstructorParameterPrefix.rawTranslation
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current checkedScope checkedDomains)
    (hscope : checkedScope.WF env Us.length)
    (Horiginal : TrExprS env Us [] original target) :
    H.RawTranslation target := by
  induction H generalizing target with
  | zero =>
    exact ⟨[], [], target, by simp [VExpr.wrapForalls], rfl, rfl, .nil, .base,
      by simpa using Horiginal⟩
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    rename_i i name dom body bi oldScope sourceDomains param fv sourceDomain
      paramType deps
    rcases ih hscope.1 Horiginal with
      ⟨rawScope, domains, residual, htarget, hlength, hrawContext,
        Hcontexts, Hunique, Hcurrent⟩
    cases Hcurrent with
    | @forallE rawDomain rawBody _ _ _ _ _ rawDomainType rawBodyType
        rawDomainTranslation rawBodyTranslation =>
      have hrawSource := rawDomainTranslation.uniq henv Hcontexts hdomain
      have hsourceDomainTypeRaw := hdomainType.defeqDFC henv.ordered
        (Hcontexts.symm henv.ordered).defeqCtx
      have hcompareRaw := hcompare.defeqDFC henv.ordered
        (Hcontexts.symm henv.ordered).defeqCtx
      have hrawSourceAtSort := hrawSource.of_r henv Hcontexts.wf.toCtx
        (Classical.choose_spec hsourceDomainTypeRaw)
      have hcompareAtSort := hcompareRaw.of_l henv Hcontexts.wf.toCtx
        (Classical.choose_spec hsourceDomainTypeRaw)
      have hrawParam := hrawSourceAtSort.trans hcompareAtSort
      have hrawFresh : ∀ currentFv currentDeps,
          some (fv, deps) = some (currentFv, currentDeps) →
          currentFv ∉ rawScope.fvars ∧ currentDeps ⊆ rawScope.fvars := by
        intro currentFv currentDeps heq
        cases heq
        have hcheckedFresh := hscope.2.1 fv deps rfl
        simpa [Hcontexts.fvars] using hcheckedFresh
      let Hcontexts : VLCtx.IsDefEq env Us.length
          ((some (fv, deps), .vlam rawDomain) :: rawScope)
          ((some (fv, deps), .vlam paramType) :: oldScope) :=
        .cons Hcontexts hrawFresh (.vlam hrawParam)
      have Hopened := rawBodyTranslation.inst_fvar henv.ordered Hcontexts.wf
      refine ⟨(some (fv, deps), .vlam rawDomain) :: rawScope,
        domains ++ [rawDomain], rawBody, ?_, ?_, ?_, Hcontexts,
        Hunique.cons .vlam, ?_⟩
      · rw [htarget]
        simp [VExpr.wrapForalls]
      · simp [hlength]
      · simp [VLCtx.toCtx, hrawContext, List.reverse_append]
      · simpa [Expr.instantiate1_eq, hparamFVar] using Hopened

/-- Package the exact raw-prefix translation state in the independent formation
judgment. -/
theorem CheckedConstructorParameterPrefix.ctorParameterShape
    {decl : VInductDecl} {ctor : VConstVal} {params : List VExpr}
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      decl.nparams current scope checkedDomains)
    (hscope : scope.WF env Us.length)
    (Horiginal : TrExprS env Us [] original ctor.type)
    (huvars : decl.uvars = Us.length)
    (hparams : env.IsDefEqCtx Us.length [] params.reverse scope.toCtx) :
    decl.CtorParameterShape env params ctor := by
  rcases H.rawTranslation henv hscope Horiginal with
    ⟨rawScope, domains, residual, htarget, hlength, hrawContext,
      Hcontexts, _, _⟩
  refine ⟨domains, residual, ?_, ?_⟩
  · rw [htarget, ← hlength]
    exact VExpr.takeForalls_wrapForalls domains residual
  · have hrawChecked : env.IsDefEqCtx Us.length [] domains.reverse
        scope.toCtx := by
      rw [← hrawContext]
      exact Hcontexts.defeqCtx
    have hparams' := VEnv.IsDefEqCtx.trans_empty henv hparams
      (hrawChecked.symm henv.ordered)
    simpa [VInductDecl.ParamsDefEq, huvars] using hparams'

/-- The closed raw constructor retains the checked tail's telescope, owning
family, and common-parameter variables. Projection implementation choices
inside fields and indices do not affect this skeleton. -/
theorem CheckedConstructorParameterPrefix.rawCtorShape
    {decl : VInductDecl} {target : VInductiveType} {ctor : VConstVal}
    {tail : Expr} {tailTarget : VExpr}
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      decl.nparams tail scope sourceDomains)
    (hscope : scope.WF env Us.length)
    (Horiginal : TrExprS env Us [] original ctor.type)
    (Htail : TrExprS env Us scope tail tailTarget)
    (Hcert : ConstructorTailCertificate env decl target scope.toCtx 0
      tailTarget classes) :
    decl.RawCtorShape target ctor := by
  rcases H.rawTranslation henv hscope Horiginal with
    ⟨rawScope, domains, residual, htarget, hlength, _, _, Hunique, Hresidual⟩
  have hres := TrExprS.rawShape Hunique.rawShape Hresidual Htail
  rcases Hcert.raw with ⟨doms, result, hwrap, hvalid, hhead⟩
  have hshape : decl.RawCtorShape target
      {ctor with type := VExpr.wrapForalls domains tailTarget} := by
    refine ⟨domains ++ doms, result, ?_, ?_, ?_, hhead⟩
    · simp only [hwrap, VExpr.wrapForalls_append]
    · simp [hlength]
    · simpa [hlength] using hvalid.raw
  apply hshape.of_rawShapeRel
  change VExpr.RawShapeRel ctor.type (VExpr.wrapForalls domains tailTarget)
  rw [htarget]
  exact hres.wrapForalls domains

/-- The checked constructors yield the raw syntactic shape of every
source constructor, positionally aligned with the declaration. -/
theorem CheckedConstructors.rawShapes
    (H : CheckedConstructors sourceEnv decl env params stats indTypes
      Us scope classes)
    (henv : env.WF)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv env Us)
      indTypes.toList decl.types)
    (hscope : scope.WF env Us.length)
    (hparamsSize : stats.params.size = decl.nparams) :
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor := by
  intro target htarget ctor hctor
  rcases List.mem_iff_getElem.1 htarget with ⟨familyIdx, hfamilyTarget, rfl⟩
  rcases List.mem_iff_getElem.1 hctor with ⟨ctorIdx, hctorTarget, rfl⟩
  have hfamilySource : familyIdx < indTypes.size := by
    have hlength := Lean4Lean.List.Forall₂.length_eq Htypes
    simpa using (show familyIdx < indTypes.toList.length by
      rw [hlength]
      exact hfamilyTarget)
  have Hfamily := Lean4Lean.List.forall₂_getElem Htypes
    familyIdx (by simpa using hfamilySource) hfamilyTarget
  have Hfamily' : TrInductiveTypeHeaders sourceEnv env Us
      indTypes[familyIdx] decl.types[familyIdx] := by
    simpa using Hfamily
  have hctorSource : ctorIdx < indTypes[familyIdx].ctors.length := by
    rw [Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Hfamily']
    exact hctorTarget
  have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
    Hfamily' ctorIdx hctorSource hctorTarget
  rcases H.constructorTails.replay familyIdx hfamilySource ctorIdx hctorSource with
    ⟨ctorVal, _tail, _tailTarget, _sourceDomains, _hmem, Hraw, _Hprefix,
      Hcomparisons, Htranslated, Htail, _Hsynthesis⟩
  have Hcomparisons' : CheckedConstructorParameterPrefix env Us stats
      indTypes[familyIdx].ctors[ctorIdx].type decl.nparams _tail scope
      _sourceDomains := by
    simpa [hparamsSize] using Hcomparisons
  have Hshape := Hcomparisons'.rawCtorShape henv hscope Hraw.type Htranslated
    Htail
  exact Hshape.of_rawShapeRel (TrExprS.rawShape .base Hctor.type Hraw.type)

/-- The checked constructors already contain every successful raw
parameter comparison.  Pair it with the declaration translation at the same
family/constructor indices to obtain the independent raw shape judgment,
without changing the executable loop or adding a semantic callback. -/
theorem CheckedConstructors.parameterShapes
    (H : CheckedConstructors sourceEnv decl env params stats indTypes
      Us scope classes)
    (henv : env.WF)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv env Us)
      indTypes.toList decl.types)
    (hscope : scope.WF env Us.length)
    (hparamsSize : stats.params.size = decl.nparams)
    (huvars : decl.uvars = Us.length)
    (hparams : env.IsDefEqCtx Us.length [] params.reverse scope.toCtx) :
    ConstructorParameterCertificate env decl params where
  shapes target htarget ctor hctor := by
    rcases List.mem_iff_getElem.1 htarget with ⟨familyIdx, hfamilyTarget, rfl⟩
    rcases List.mem_iff_getElem.1 hctor with ⟨ctorIdx, hctorTarget, rfl⟩
    have hfamilySource : familyIdx < indTypes.size := by
      have hlength := Lean4Lean.List.Forall₂.length_eq Htypes
      simpa using (show familyIdx < indTypes.toList.length by
        rw [hlength]
        exact hfamilyTarget)
    have Hfamily := Lean4Lean.List.forall₂_getElem Htypes
      familyIdx (by simpa using hfamilySource) hfamilyTarget
    have Hfamily' : TrInductiveTypeHeaders sourceEnv env Us
        indTypes[familyIdx] decl.types[familyIdx] := by
      simpa using Hfamily
    have hctorSource : ctorIdx < indTypes[familyIdx].ctors.length := by
      rw [Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length Hfamily']
      exact hctorTarget
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
      Hfamily' ctorIdx hctorSource hctorTarget
    rcases H.constructorTails.replay familyIdx hfamilySource ctorIdx hctorSource with
      ⟨_ctorVal, _tail, _tailTarget, _sourceDomains, _hmem, _Hraw, _Hprefix,
        Hcomparisons, _Htranslated, _Htail, _Hsynthesis⟩
    have Hcomparisons' : CheckedConstructorParameterPrefix env Us stats
        indTypes[familyIdx].ctors[ctorIdx].type decl.nparams _tail scope
        _sourceDomains := by
      simpa [hparamsSize] using Hcomparisons
    exact Hcomparisons'.ctorParameterShape henv hscope Hctor.type huvars hparams

end VerifyInductive
end Lean4Lean
