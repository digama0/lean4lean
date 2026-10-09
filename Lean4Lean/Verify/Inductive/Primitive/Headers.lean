import Lean4Lean.Verify.Inductive.Primitive.Context
import Lean4Lean.Verify.Inductive.Header.Declaration
import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Install.Headers

/-!
# Headers of a primitive declaration

The header phase on the primitive path: the executable header installation is an atomic
batch (`declareInductiveTypes.installsHeadersAtomicWF`), the canonical `Bool`/`Nat` syntax
fixes the constructor targets, and the checked headers are packaged as a
`PrimitiveHeaderEnvironment` (`declareInductiveTypes.primitiveHeadersWF`), whose checking
context is only a `LocalContextWF`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A finite abstract constant batch can be installed whenever all names are
fresh in the source environment and pairwise distinct. -/
theorem VEnv.exists_addConstVals
    {env : VEnv} {values : List VConstVal}
    (hfresh : ∀ value ∈ values, env.constants value.name = none)
    (hnodup : (values.map (·.name)).Nodup) :
    ∃ out, env.addConstVals values = some out := by
  induction values generalizing env with
  | nil => exact ⟨env, rfl⟩
  | cons value values ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases VEnv.addConst_eq_none
      (ci := value.toVConstant) (hfresh value (by simp)) with
      ⟨next, hnext⟩
    have htailFresh : ∀ later ∈ values,
        next.constants later.name = none := by
      intro later hlater
      rw [VEnv.addConst_constants_eq hnext]
      have hne : value.name ≠ later.name := by
        intro heq
        exact hnodup.1 (List.mem_map.mpr ⟨later, hlater, heq.symm⟩)
      simp [hne, hfresh later (by simp [hlater])]
    rcases ih htailFresh hnodup.2 with ⟨out, hout⟩
    exact ⟨out, by simp [VEnv.addConstVals, hnext, hout]⟩

/-- Successful executable header installation always determines a matching
abstract atomic batch, even when primitive reserved names are allowed.  The
result deliberately stops at `AtomicAddConstants`: no validity claim is made
for the header-only abstract environment. -/
theorem AddInductive.declareInductiveTypes.installsHeadersAtomicWF
    (Hc : ContextWF c)
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams numParams commonParams commonLevel indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ outVEnv,
          Hc.venv.addConstVals Hsemantic.headers.targets = some outVEnv ∧
          AtomicAddConstants c.safety c.env Hc.venv
            (List.zip
              ((AddInductive.inductiveTypeInfos stats numParams indTypes
                numNested isUnsafe c.lparams).toList.map
                  (fun info => .inductInfo info))
              Hsemantic.headers.targets)
            outEnv outVEnv := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Hentries :=
    AddInductive.inductiveTypeInfos.translatedCheckedHeaders
      (stats := stats) (numParams := numParams) (numNested := numNested)
      Hsemantic.headers hindices hvisible
  have Hproduction := declareInductiveTypeInfos_refines c.allowPrimitive
    infos.toList c.env Hc.checking.tr.map_wf
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  intro outEnv hout
  have Hdeclared := Hproduction outEnv hout
  have hnames : infos.toList.map (fun info => info.name) =
      Hsemantic.headers.targets.map (·.name) := by
    rw [← List.forall₂_eq, List.forall₂_map_left_iff,
      List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ _ Hentry => Hentry.1.2)
      Hentries
  have hfresh : ∀ value ∈ Hsemantic.headers.targets,
      Hc.venv.constants value.name = none := by
    intro value hvalue
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hentries value hvalue with
      ⟨info, hinfo, Hentry⟩
    have hprod : c.env.find? value.name = none := by
      rw [← Hentry.1.2]
      exact Hdeclared.sourceFresh info hinfo
    cases habstract : Hc.venv.constants value.name with
    | none => rfl
    | some ci =>
      rcases Hc.checking.tr.find?_iff.mpr ⟨ci, habstract⟩ with
        ⟨source, hsource, _⟩
      rw [hprod] at hsource
      contradiction
  have hnodup : (Hsemantic.headers.targets.map (·.name)).Nodup := by
    rw [← hnames]
    exact Hdeclared.namesNodup
  rcases VEnv.exists_addConstVals hfresh hnodup with ⟨outVEnv, habstract⟩
  have Hatomic := AtomicAddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive) Hc.checking.tr Hentries VEnv.LE.rfl
      habstract
  exact ⟨outVEnv, habstract, Hatomic outEnv hout⟩

/-- The semantic header traversal and a successful atomic header installation
determine raw constructor targets for either canonical primitive source.
These targets are finite and source-derived; no declaration skeleton is an
input. -/
theorem PrimitiveInductiveShape.checkedConstructorRows
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        env lparams nparams params commonLevel types)
    (htypesAdded : env.addConstVals Hsemantic.headers.targets =
      some envTypes) :
    Nonempty (RawBlockCtorTranslations envTypes lparams types) := by
  rcases Hshape with ⟨rfl, rfl, rfl, hbool | ⟨binderName, binderInfo, hnat⟩⟩
  · subst types
    rcases List.Forall₂.leftSingleton Hsemantic.headers.translations with
      ⟨target, htargets, Htarget⟩
    have hlookup : envTypes.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      simp [htargets]
    let falseVal : VConstVal :=
      { name := ``Bool.false, uvars := 0, type := .const target.name [] }
    let trueVal : VConstVal :=
      { name := ``Bool.true, uvars := 0, type := .const target.name [] }
    have hconst : TrExprS envTypes [] [] (.const ``Bool [])
        (.const target.name []) := by
      simpa [Htarget.name] using
        (TrExprS.const (env := envTypes) (Us := []) (Δ := []) hlookup
          (by rfl) (by simp [Htarget.uvars]))
    have Hfalse : TrSourceConstRaw envTypes [] ``Bool.false
        (.const ``Bool []) falseVal := by
      exact ⟨rfl, rfl, by simpa [falseVal] using hconst⟩
    have Htrue : TrSourceConstRaw envTypes [] ``Bool.true
        (.const ``Bool []) trueVal := by
      exact ⟨rfl, rfl, by simpa [trueVal] using hconst⟩
    exact ⟨{
      targets := [[falseVal, trueVal]]
      translations := .cons (.cons Hfalse (.cons Htrue .nil)) .nil }⟩
  · subst types
    rcases List.Forall₂.leftSingleton Hsemantic.headers.translations with
      ⟨target, htargets, Htarget⟩
    have hlookup : envTypes.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get htypesAdded
      simp [htargets]
    have htargetType : target.type = .sort (.succ .zero) := by
      have hcanonical : TrExprS env [] [] (.sort (.succ .zero))
          (.sort (.succ .zero)) := TrExprS.sort rfl
      exact TrExprS.unique Htarget.type hcanonical
    have hconst (Delta : VLCtx) : TrExprS envTypes [] Delta
        (.const ``Nat []) (.const target.name []) := by
      simpa [Htarget.name] using
        (TrExprS.const (env := envTypes) (Us := []) (Δ := Delta) hlookup
          (by rfl) (by simp [Htarget.uvars]))
    have hconstIsType (Gamma : List VExpr) :
        envTypes.IsType 0 Gamma (.const target.name []) := by
      refine ⟨.succ .zero, ?_⟩
      simpa [htargetType, VExpr.instL, VLevel.inst] using
        (VEnv.HasType.const (U := 0) (ls := []) (Γ := Gamma) hlookup
          (by simp) (by simp [Htarget.uvars]))
    let zeroVal : VConstVal :=
      { name := ``Nat.zero, uvars := 0, type := .const target.name [] }
    let succVal : VConstVal := {
      name := ``Nat.succ
      uvars := 0
      type := .forallE (.const target.name []) (.const target.name []) }
    have Hzero : TrSourceConstRaw envTypes [] ``Nat.zero
        (.const ``Nat []) zeroVal := by
      exact ⟨rfl, rfl, by simpa [zeroVal] using hconst []⟩
    have Hsucc : TrSourceConstRaw envTypes [] ``Nat.succ
        (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
        succVal := by
      refine ⟨rfl, rfl, ?_⟩
      simpa [succVal] using
        (TrExprS.forallE (env := envTypes) (Us := []) (Δ := [])
          (hconstIsType []) (hconstIsType [.const target.name []])
          (hconst []) (hconst [(none, .vlam (.const target.name []))]))
    exact ⟨{
      targets := [[zeroVal, succVal]]
      translations := .cons (.cons Hzero (.cons Hsucc .nil)) .nil }⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Package skeleton-free semantic assembly against an atomic primitive
header installation.  The resulting context is only a `LocalContextWF` until
constructor installation completes the batch of Bool or Nat constants. -/
def HeaderDeclaration.toPrimitiveHeaderEnvironment
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {envTypes : VEnv} {outEnv : Environment}
    (Hinstalled : AtomicAddConstants c.safety c.env Hc.venv
      (List.zip
        ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
          isUnsafe c.lparams).toList.map (fun info => .inductInfo info))
        Hsemantic.headers.targets)
      outEnv envTypes)
    (H : HeaderDeclaration Hc.venv envTypes c.lparams nparams
      indTypes.toList isUnsafe commonParams commonLevel Hsemantic)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (hpresent : ListedConstructorsPresent c.env) :
    PrimitiveHeaderEnvironment c stats H.decl nparams isUnsafe depth
      Hc.venv indTypes outEnv := by
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  let entries : List (ConstantInfo × VConstVal) :=
    List.zip (infos.toList.map fun info => .inductInfo info)
      Hsemantic.headers.targets
  have hmetadataLength : H.metadata.length = indTypes.toList.length := by
    calc
      H.metadata.length = H.skeleton.types.length :=
        VInductDeclSkeleton.withMetadata_length H.checked
      _ = H.decl.types.length :=
        (VInductDeclSkeleton.withMetadata_fields H.checked).2.2.2.symm
      _ = indTypes.toList.length :=
        (List.Forall₂.length_eq H.translation.types).symm
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = stats.nindices.toList.length := by simp
      _ = (H.metadata.map Prod.fst).length := congrArg List.length hindices
      _ = H.metadata.length := by simp
      _ = indTypes.toList.length := hmetadataLength
      _ = indTypes.size := by simp
  have hsourceLength : indTypes.toList.length =
      Hsemantic.headers.targets.length :=
    List.Forall₂.length_eq
      Hsemantic.headers.translations
  have hinfosLength : infos.toList.length =
      Hsemantic.headers.targets.length := by
    calc
      infos.toList.length = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      _ = indTypes.toList.length := by simp
      _ = Hsemantic.headers.targets.length := hsourceLength
  have hentriesFst : entries.map Prod.fst =
      infos.toList.map (fun info => ConstantInfo.inductInfo info) := by
    apply List.map_fst_zip
    simpa using Nat.le_of_eq hinfosLength
  have hentriesSnd : entries.map Prod.snd =
      Hsemantic.headers.targets := by
    apply List.map_snd_zip
    simpa using Nat.le_of_eq hinfosLength.symm
  let sourceMaterialized :=
    H.checkedResult hlevels hlevelParams
      hindices hconsts hparams Hcache Hsuffix Hambient hcommon hnotzero
  have hsourceHeaders : sourceMaterialized.headers = H.headers := by
    change H.formations.complete H.checked = H.headers
    exact H.headers_eq.symm
  let context : LocalContextWF { c with env := outEnv } :=
    Hc.toLocal.withEnv (venv' := envTypes)
      (Hinstalled.checking Hc.checking.tr) Hinstalled.le
      ((Hc.checking.ctorTelescopes.ofCtors
        (Hinstalled.ctors_of_noCtor Hc.checking.tr.map_wf inductInfo_zip_noCtor)).mono
        Hinstalled.le)
  have hcontextVEnv : context.venv = envTypes := rfl
  have hle : Hc.venv ≤ context.venv := Hinstalled.le
  let materializedMono := sourceMaterialized.mono hle
  have hscope : Hc.mlctx.vlctx = context.mlctx.vlctx := rfl
  let materialized := materializedMono.retargetScope hscope
  exact {
    entries := entries
    infos := ⟨numNested, by simpa [infos] using hentriesFst⟩
    sourceAligned := ⟨numNested, by
      change InductiveHeaderEntries infos.toList entries
      exact InductiveHeaderEntries.ofZip hinfosLength⟩
    values := hentriesSnd.trans H.typeConstants.symm
    context := context
    headers := H.headers
    translation := by rw [hcontextVEnv]; exact H.translation
    installed := by rw [hcontextVEnv]; simpa [entries, infos] using Hinstalled
    sourceContext := Hc
    sourcePresent := hpresent
    sourceContextVEnv := rfl
    sourceStatsWF := sourceMaterialized
    sourceHeaderParams := congrArg (fun headers => headers.params) hsourceHeaders
    statsWF := materialized
    headerParams := by
      calc
        materialized.headers.params = materializedMono.headers.params := by
          simp [materialized]
        _ = sourceMaterialized.headers.params :=
          checkInductiveTypes.loopInd.HeaderStatsWF.mono_headers_params
            sourceMaterialized hle
        _ = H.headers.params := congrArg (fun headers => headers.params)
          hsourceHeaders
    parameterScopeEq := by
      simp [materialized, materializedMono] }

/-- Primitive header installation with the declaration synthesized from the
successful semantic header fold and the finite canonical constructor rows.
No caller-provided skeleton or header translation remains. -/
theorem AddInductive.declareInductiveTypes.primitiveHeadersWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hpresent : ListedConstructorsPresent c.env) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ decl, ∃ _envTypes : VEnv,
          ∃ _Hheaders : PrimitiveHeaderEnvironment c stats decl nparams
            isUnsafe depth Hc.venv indTypes outEnv, True := by
  have Hinstall :=
    AddInductive.declareInductiveTypes.installsHeadersAtomicWF
      (numNested := numNested) Hc Hsemantic hindicesSize hvisible
  exact Hinstall.mono fun outEnv Hresult => by
    rcases Hresult with ⟨envTypes, htypesAdded, Hatomic⟩
    rcases Hshape.checkedConstructorRows Hsemantic htypesAdded with
      ⟨Hconstructors⟩
    rcases HeaderDeclaration.ofTargetsExact (isUnsafe := isUnsafe)
      Hsemantic Hconstructors hcommonParams htypesAdded with ⟨A⟩
    have hindices' : stats.nindices.toList = A.metadata.map Prod.fst := by
      rw [A.metadata_eq]
      exact hindices
    let Hheaders := A.toPrimitiveHeaderEnvironment Hatomic hlevels hlevelParams
      hindices' hconsts hparams Hcache Hsuffix Hambient hcommon hnotzero hpresent
    exact ⟨A.decl, envTypes, Hheaders, trivial⟩

end VerifyInductive
end Lean4Lean
