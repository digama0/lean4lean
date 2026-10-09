import Lean4Lean.Theory.Inductive.RestorationProjNames

namespace Lean4Lean
namespace InductiveSignature

/-! ### Monotonicity of case certificates

`CaseCompilationData.mono`: the case part of a compilation (the certificate of
`CaseSchema.Certified`) survives every extension of the base environment in which the source
and expanded declarations still install. The nested path uses it to keep the certificate of
a source block's case eliminator valid over larger environments (`VInductDecl.CaseEliminators`,
section 3.2 of the design notes). -/

theorem ContainerSpecialization.WellFormed.mono {a : ContainerSpecialization}
    {envTypes envTypes' : VEnv} {source : VInductDecl} {params : List VExpr}
    (H : a.WellFormed envTypes source params) (hle : envTypes ≤ envTypes') :
    a.WellFormed envTypes' source params := by
  obtain ⟨h1, h2, h3, h4, h5, type, htype⟩ := H
  exact ⟨h1, h2, h3, h4, h5, type, htype.mono hle⟩

theorem RestoresType.mono {r : Restoration} {env env' : VEnv} {U : Nat} {n s : VExpr}
    (H : RestoresType r env U n s) (hle : env ≤ env') : RestoresType r env' U n s := by
  obtain ⟨restored, hr, hd⟩ := H
  exact ⟨restored, hr, hd.mono hle⟩

theorem RestoresFamily.mono {r : Restoration} {env env' : VEnv} {U : Nat}
    {n s : VInductiveType} (H : RestoresFamily r env U n s) (hle : env ≤ env') :
    RestoresFamily r env' U n s := by
  obtain ⟨domains, body, level, exprType, hlevel, htype, hbody⟩ := H.type
  exact { H with
    type := ⟨domains, body, level, exprType, hlevel, htype.mono hle, hbody.mono hle⟩
    constructors := Lean4Lean.List.Forall₂.imp
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.mono hle⟩) H.constructors }

/-- The case part of a compilation is monotone along larger environments in which the source
and expanded declarations still install. -/
theorem CaseCompilationData.mono {env env' : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {auxiliaries : List ContainerSpecialization}
    {block : VInductBlock} {sourceTypes' sourceCtors' expandedTypes' expandedCtors' : VEnv}
    (H : CaseCompilationData env source expanded s auxiliaries block) (hle : env ≤ env')
    (hsourceTypes : env'.addConstVals source.typeConstants = some sourceTypes')
    (hsourceCtors : sourceTypes'.addConstVals source.constructorConstants = some sourceCtors')
    (hexpandedTypes : env'.addConstVals expanded.typeConstants = some expandedTypes')
    (hexpandedCtors : expandedTypes'.addConstVals expanded.constructorConstants =
      some expandedCtors') :
    CaseCompilationData env' source expanded s auxiliaries block where
  sourceWF := H.sourceWF.mono_of_addConstVals hle hsourceTypes hsourceCtors
  sourceParameters := H.sourceParameters.mono_of_addConstVals hle hsourceTypes
  expandedWF := H.expandedWF.mono_of_addConstVals hle hexpandedTypes hexpandedCtors
  headerPrefix := H.headerPrefix
  expandedFormation := H.expandedFormation.mono_of_addConstVals hle hexpandedTypes
  model := H.model.mono hle hexpandedTypes
  uvars := H.uvars
  nparams := H.nparams
  safety := H.safety
  restorationScoped := H.restorationScoped
  correspondence := by
    obtain ⟨envTypes, direct, ht, hmapM, hwf, hF⟩ := H.correspondence
    have hTle : envTypes ≤ sourceTypes' := VEnv.addConstVals_mono hle ht hsourceTypes
    exact ⟨sourceTypes', direct, hsourceTypes, hmapM, fun a ha => (hwf a ha).mono hTle,
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.mono hTle) hF⟩
  familyTypesWF := by
    obtain ⟨T, C, es, ht, hc, hes, hfam⟩ := H.familyTypesWF
    have hTle : T ≤ expandedTypes' := VEnv.addConstVals_mono hle ht hexpandedTypes
    have hCle : C ≤ expandedCtors' := VEnv.addConstVals_mono hTle hc hexpandedCtors
    exact ⟨expandedTypes', expandedCtors', es, hexpandedTypes, hexpandedCtors,
      hes.mono hle hexpandedTypes,
      hfam.mono (VEnv.addProjections_mono (VEnv.addEliminators_mono hCle))⟩
  types := H.types
  ctors := H.ctors
  projections := H.projections

theorem RecursorNamesFresh.mono {env env' : VEnv} {source expanded : VInductDecl}
    {auxiliaries : List ContainerSpecialization}
    (H : RecursorNamesFresh env source expanded auxiliaries)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).recursors.map Prod.fst,
      env'.constants n = none) :
    RecursorNamesFresh env' source expanded auxiliaries :=
  fun n hn => ⟨hfresh n hn, (H n hn).2⟩

theorem _root_.Lean4Lean.ContainersInstalled.mono {env env' : VEnv}
    {auxiliaries : List ContainerSpecialization}
    (H : ContainersInstalled env auxiliaries) (hle : env ≤ env') :
    ContainersInstalled env' auxiliaries := by
  induction auxiliaries with
  | nil => exact .nil
  | cons a rest ih =>
    cases H with
    | cons hcompiled hblock hinstall hinst hrest =>
      exact .cons hcompiled hblock hinstall (hinst.trans hle) (ih hrest)

theorem CaseSchema.HeaderAgreement.mono {schema : CaseSchema} {env env' envTypes' : VEnv}
    {source : VInductDecl} (H : schema.HeaderAgreement env source) (hle : env ≤ env')
    (htypes' : env'.addConstVals source.typeConstants = some envTypes') :
    schema.HeaderAgreement env' source := by
  obtain ⟨RP, hRP, hhdr⟩ := H
  refine ⟨RP, hRP, fun owner => ?_⟩
  obtain ⟨RI, hRI, hagree⟩ := hhdr owner
  refine ⟨RI, hRI, fun type htype hname => ?_⟩
  obtain ⟨envTypes₀, ht₀, hdefeq⟩ := hagree type htype hname
  exact ⟨envTypes', htypes', hdefeq.mono (VEnv.addConstVals_mono hle ht₀ htypes')⟩

end InductiveSignature
end Lean4Lean
