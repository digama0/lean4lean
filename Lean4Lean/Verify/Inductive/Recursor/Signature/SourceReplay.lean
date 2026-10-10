import Lean4Lean.Verify.Inductive.Recursor.Inputs
import Lean4Lean.Verify.Inductive.Constructor.SourceSignature
import Lean4Lean.Verify.Inductive.Recursor.Context.ParameterContext
import Lean4Lean.Theory.Inductive.ConstructorArity

/-! # The source signature replayed from the retained constructor telescopes

The recursor construction reads the declaration's source signature off the exact kernel
constructor telescopes the constructor check retained (`ConstructorTails`): each constructor of
the signature keeps its literal checked tail (`SourceConstructorTelescope`), which the recursor
generator re-walks. This is the source branch's `CheckedFormation.sourceSignature` (by replay),
stated for `RecursorInput`; the constructor phase's own `CheckedFormation.sourceSignature` is
built from the abstract tails instead. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace checkInductiveTypes.loopInd

/-- Select one normalized source header per family, before adding the fresh
recursor universe. The family table and later generation share this choice. -/
noncomputable def HeaderStatsWF.signatureFamily
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (i : Nat) (hi : i < decl.types.length) : InductiveSignature.Family :=
  let source := Classical.choose (H.normalizedShapes i hi)
  { name := decl.types[i].name
    indices := source.indices
    resultLevel := decl.types[i].resultLevel }

noncomputable def HeaderStatsWF.signatureFamilies
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    Array InductiveSignature.Family :=
  Array.ofFn fun i : Fin decl.types.length => H.signatureFamily i.val i.isLt

@[simp] theorem HeaderStatsWF.signatureFamilies_size
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    H.signatureFamilies.size = decl.types.length := by
  simp [signatureFamilies]

/-- The chosen index domains are those of the same retained normalized source
header that proves this family's model; their universe context is unchanged. -/
theorem HeaderStatsWF.signatureFamily_model
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (henv : env.WF)
    (i : Nat) (hi : i < decl.types.length)
    (htype : env.IsType decl.uvars [] decl.types[i].type) :
    (H.signatureFamily i hi).name = decl.types[i].name ∧
    (H.signatureFamily i hi).indices.length = decl.types[i].numIndices ∧
    (H.signatureFamily i hi).resultLevel = decl.types[i].resultLevel ∧
    env.IsDefEqU decl.uvars [] decl.types[i].type
      (VExpr.wrapForalls (H.headers.params ++ (H.signatureFamily i hi).indices)
        (.sort (H.signatureFamily i hi).resultLevel)) := by
  let source := Classical.choose (H.normalizedShapes i hi)
  obtain ⟨result, exprType, hnormalized, hresult⟩ :=
    Classical.choose_spec (H.normalizedShapes i hi)
  refine ⟨rfl, source.indexCount, rfl, ?_⟩
  have hcanonical := canonicalFamilyOfTelescope henv
    (by simpa [H.uvars] using htype) hnormalized source.parameters hresult
  simpa [signatureFamily, source, H.uvars] using hcanonical

theorem HeaderStatsWF.signatureFamilies_names
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    H.signatureFamilies.toList.map (·.name) = decl.types.map (·.name) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < decl.types.length := by simpa using hright
    simp [signatureFamilies, signatureFamily]

/-- The common source parameter list has exactly the arity checked by the
executable parameter cache. -/
theorem HeaderStatsWF.signatureParams_length
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    H.headers.params.length = decl.nparams := by
  have hcontext := H.paramsContext.length_eq
  have hcached := checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length H.cachedScope
  have hscope := List.Forall₂.length_eq H.cachedScope
  have htranslated := List.Forall₂.length_eq H.params
  simp only [List.length_reverse, Array.length_toList,
    VInductDecl.paramVars, List.length_map, List.length_reverse, List.length_range] at *
  omega

/-- Shared source-universe family and parameter choices. Constructor fields
are filled from the checked source-tail certificates over this same table. -/
noncomputable def HeaderStatsWF.signatureHeader
    (H : HeaderStatsWF env Us Δ stats decl depth) : InductiveSignature where
  uvars := decl.uvars
  params := H.headers.params
  families := H.signatureFamilies
  constructors := #[]
  isUnsafe := decl.isUnsafe

end checkInductiveTypes.loopInd

open InductiveSignature

open Kernel InductiveSignature

/-- The exact kernel telescope retained with a selected constructor.
Typed source correspondence alone cannot recover literal index occurrences
or the translations needed when generating a recursor. -/
def SourceConstructorTelescope (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (source : Constructor) (sourceCtor : VConstVal)
    (s : InductiveSignature) (ctor : InductiveSignature.Constructor s.families.size) : Prop :=
  ∃ tail tailTarget sourceDomains,
    TrSourceConstRaw env Us source.name source.type sourceCtor ∧
    ParameterPrefix stats 0 source.type tail ∧
    CheckedConstructorParameterPrefix env Us stats source.type stats.params.size tail scope sourceDomains ∧
    TrExprS env Us scope tail tailTarget ∧
    (∃ classes, ConstructorTailCertificate env decl target scope.toCtx 0 tailTarget classes) ∧
    Nonempty (checkInductiveTypes.loopType.ScopedHeaderTelescope
      env Us (constructorTelescopeTarget sourceCtor) scope tailTarget stats.params.size 0) ∧
    VExpr.wrapForalls s.params tailTarget = s.constructorType ctor

/-- A fixed parameter prefix is injective in its residual expression. -/
private theorem wrapForalls_body_eq {params : List VExpr}
    (H : VExpr.wrapForalls params left = VExpr.wrapForalls params right) : left = right := by
  induction params with
  | nil => exact H
  | cons param params ih => exact ih (VExpr.forallE.inj H).2

/-- The retained tail is the literal generator telescope, so its result
indices and stored field domains are available syntactically as well as by typing. -/
theorem sourceConstructor_tail_eq {s : InductiveSignature}
    {ctor : InductiveSignature.Constructor s.families.size}
    (H : VExpr.wrapForalls s.params tail = s.constructorType ctor) :
    tail = VExpr.wrapForalls (s.fieldTypes ctor)
      (s.familyApp ctor.owner (VLevel.params s.uvars)
        (vars s.params.length ctor.fields.length) ctor.indices) := by
  apply wrapForalls_body_eq (params := s.params)
  simpa only [constructorType, VExpr.wrapForalls_append] using H

/-- The selected constructor keeps the literal result arity already checked
by its checked tail certificate. No semantic inversion is required. -/
theorem SourceConstructorTelescope.constructorArity
    (H : SourceConstructorTelescope env Us scope stats decl target source sourceCtor s ctor)
    (names : (decl.types.map (·.name)).Nodup) (targetMember : target ∈ decl.types)
    (params : s.params.length = decl.nparams)
    (family : s.families[ctor.owner].indices.length = target.numIndices) :
    ctor.indices.length = s.families[ctor.owner].indices.length := by
  obtain ⟨_, _, _, _, _, _, _, ⟨_, certificate⟩, _, literal⟩ := H
  obtain ⟨domains, result, same, application, head⟩ := certificate.raw
  exact constructor_indices_length_of_rawTail names targetMember params family
    ⟨domains, result, same, application.raw, head⟩ (sourceConstructor_tail_eq literal)

/-- A later constructor pass consumes the same cached parameter prefix.
Its residual therefore translates to the literal telescope selected for
generation, without making another normalization choice. -/
theorem SourceConstructorTelescope.tailTranslation
    {s : InductiveSignature}
    {ctor : InductiveSignature.Constructor s.families.size}
    (H : SourceConstructorTelescope env Us scope stats decl target source sourceCtor s ctor)
    (hprefix : ParameterPrefix stats 0 source.type residual) :
    TrExprS env Us scope residual
      (VExpr.wrapForalls (s.fieldTypes ctor)
        (s.familyApp ctor.owner (VLevel.params s.uvars)
          (vars s.params.length ctor.fields.length) ctor.indices)) := by
  obtain ⟨tail, tailTarget, _, _, hchecked, _, htranslation, _, _, htype⟩ := H
  have htail := hchecked.tail_eq hprefix
  have htarget := sourceConstructor_tail_eq htype
  simpa only [← htail, ← htarget] using htranslation

/-- The retained constructor replay produces a generator constructor over
the shared parameter and family table. Its stored type is related to the
actual source constructor chosen by that replay. -/
theorem CheckedConstructorTailAt.signatureConstructor
    {env : VEnv} {decl : VInductDecl} {s : InductiveSignature}
    {Us : List Name} {scope : VLCtx} {source : Constructor}
    {target : VInductiveType}
    (H : CheckedConstructorTailAt env Us scope stats decl target source classes)
    (henv : env.WF) (hu : Us.length = decl.uvars)
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (hctx : env.IsDefEqCtx decl.uvars [] s.params.reverse scope.toCtx)
    (owner : Fin s.families.size) (howner : s.families[owner].name = target.name) :
    ∃ sourceCtor ∈ target.ctors, ∃ ctor : InductiveSignature.Constructor s.families.size,
      sourceCtor.name = source.name ∧ ctor.name = source.name ∧ ctor.owner = owner ∧
      env.IsDefEqU decl.uvars [] (s.constructorType ctor) sourceCtor.type ∧
      (s.isUnsafe = true ∨ ctor.fields.map Field.isRecursive = classes) ∧
      (∀ i (hi : i < ctor.fields.length),
        SignatureFieldModel env decl s
          (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse) i ctor.fields[i]) ∧
      SourceConstructorTelescope env Us scope stats decl target source sourceCtor s ctor := by
  obtain ⟨sourceCtor, tail, tailTarget, sourceDomains, hmem, hraw, hprefix, hcomparisons, htranslation, htail,
    ⟨hsynthesis⟩⟩ := H
  have hindices : hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero hsynthesis.indexCount
  have hscope : scope.toCtx = hsynthesis.params.reverse := by
    simpa only [hindices, List.reverse_nil, List.nil_append] using hsynthesis.scopeCtx
  have huniform := htail.uniform.defeqCtx henv.ordered (hctx.symm henv.ordered)
  obtain ⟨ctor, hname, hctorOwner, htype, hclasses, hfields⟩ := signatureConstructorOfUniform
    huvars hparams hnames hsafety owner howner source.name huniform
  obtain ⟨level, htailType⟩ := htail.isType
  obtain ⟨closedLevel, hclosed⟩ := (hctx.symm henv.ordered).closeForalls htailType
  have hclosed' : env.IsDefEqU decl.uvars []
      (VExpr.wrapForalls hsynthesis.params tailTarget)
      (VExpr.wrapForalls s.params tailTarget) := by
    simpa only [hscope, List.reverse_reverse] using
      (show env.IsDefEqU decl.uvars []
        (VExpr.wrapForalls scope.toCtx.reverse tailTarget)
        (VExpr.wrapForalls s.params.reverse.reverse tailTarget) from ⟨_, hclosed⟩)
  have hsource : env.IsDefEqU decl.uvars [] sourceCtor.type
      (VExpr.wrapForalls hsynthesis.params tailTarget) := by
    simpa only [constructorTelescopeTarget, hindices, List.append_nil, hu] using
      (show env.IsDefEqU Us.length [] sourceCtor.type
        (VExpr.wrapForalls (hsynthesis.params ++ hsynthesis.indices) tailTarget) from
        ⟨_, hsynthesis.header⟩)
  refine ⟨sourceCtor, hmem, ctor, hraw.name, hname, hctorOwner, ?_, hclasses, hfields,
    tail, tailTarget, sourceDomains, hraw, hprefix, hcomparisons, htranslation, ⟨_, htail⟩,
    ⟨hsynthesis⟩, htype⟩
  rw [← htype]
  exact (hsource.trans henv trivial hclosed').symm

namespace RecursorInput
variable {isUnsafe : Bool}

/-- Constructor identities are unique in the actual kernel constructor array as
well as in its translated table. This identifies retained replays
with the constructors visited by subsequent passes. -/
theorem kernelConstructorNames
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    (indTypes.toList.flatMap (·.ctors)).map Lean.Constructor.name =
      decl.constructorConstants.map VConstVal.name := by
  have names : ∀ {sources targets},
      List.Forall₂ (TrInductiveType sourceEnv R.headerVEnv c.lparams) sources targets →
      (sources.flatMap (·.ctors)).map Lean.Constructor.name =
        (targets.flatMap (·.ctors)).map VConstVal.name := by
    intro sources targets H
    induction H with
    | nil => rfl
    | @cons source target sources targets h _ ih =>
      have ctorNames : ∀ {sources targets},
          List.Forall₂ (fun source target => TrSourceConst R.headerVEnv c.lparams
            source.name source.type target) sources targets →
          sources.map Lean.Constructor.name = targets.map VConstVal.name := by
        intro sources targets hc
        induction hc with
        | nil => rfl
        | cons h _ ih => simp only [List.map_cons, h.name, ih]
      have hctors := ctorNames h.ctors
      simpa only [List.flatMap_cons, List.map_append, hctors] using
        congrArg (target.ctors.map VConstVal.name ++ ·) ih
  exact names R.core.types

theorem kernelConstructorNames_nodup
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    ((indTypes.toList.flatMap (·.ctors)).map Lean.Constructor.name).Nodup := by
  rw [R.kernelConstructorNames]
  exact VEnv.addConstVals_names_nodup R.core.ctorsAdded

/-- Shared source-universe parameters and family choices, before the
eliminator's additional universe is introduced. -/
noncomputable def sourceSignatureHeader
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) : InductiveSignature :=
  R.sourceStatsWF.signatureHeader

theorem sourceSignatureHeader_params
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) : R.sourceSignatureHeader.params = R.params :=
  R.sourceHeaderParams

theorem sourceSignatureHeader_params_length
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) : R.sourceSignatureHeader.params.length = decl.nparams :=
  R.sourceStatsWF.signatureParams_length

theorem sourceSignatureHeader_families
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    List.Forall₂ (fun f src =>
      f.name = src.name ∧ f.indices.length = src.numIndices ∧
      f.resultLevel = src.resultLevel ∧
      sourceEnv.IsDefEqU decl.uvars []
        (VExpr.wrapForalls (R.sourceSignatureHeader.params ++ f.indices) (.sort f.resultLevel))
        src.type)
      R.sourceSignatureHeader.families.toList decl.types := by
  apply Lean4Lean.List.forall₂_of_getElem (by
    simp [sourceSignatureHeader, checkInductiveTypes.loopInd.HeaderStatsWF.signatureHeader])
  intro i hi hi'
  obtain ⟨source, _, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_r R.core.types
    _ (List.getElem_mem hi')
  have hu : decl.types[i].uvars = decl.uvars := htr.header.uvars.trans R.core.uvars.symm
  have htype : R.sourceContext.venv.IsType decl.uvars [] decl.types[i].type := by
    simpa only [R.sourceContextVEnv, VConstant.WF, hu] using htr.header.wf
  obtain ⟨hn, hiCount, hl, ht⟩ := R.sourceStatsWF.signatureFamily_model
    R.sourceContext.checking.tr.wf i hi' htype
  simpa [sourceSignatureHeader,
    checkInductiveTypes.loopInd.HeaderStatsWF.signatureHeader,
    checkInductiveTypes.loopInd.HeaderStatsWF.signatureFamilies,
    R.sourceContextVEnv] using And.intro hn (And.intro hiCount (And.intro hl ht.symm))

/-- Each checked source constructor supplies one constructor over the same
source family table. Ordered source names identify the replay's exact target. -/
theorem sourceSignatureHeader_constructor
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (i : Nat) (hi : i < decl.types.length)
    (j : Nat) (hj : j < decl.types[i].ctors.length) :
    ∃ ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size,
      R.sourceSignatureHeader.families[ctor.owner].name = decl.types[i].name ∧
      ctor.name = decl.types[i].ctors[j].name ∧
      R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType ctor) decl.types[i].ctors[j].type ∧
      (R.sourceSignatureHeader.isUnsafe = true ∨
        ctor.fields.map Field.isRecursive = R.classes[i]![j]!) ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
          (((R.sourceSignatureHeader.fieldTypes ctor).take k).reverse ++
            R.sourceSignatureHeader.params.reverse) k ctor.fields[k]) ∧
      ∃ production ∈ indTypes.toList.flatMap (·.ctors),
        SourceConstructorTelescope R.headerVEnv c.lparams R.parameterScope stats decl
          decl.types[i] production decl.types[i].ctors[j] R.sourceSignatureHeader ctor := by
  have hip : i < indTypes.size := by
    simpa only [R.constructorTails.size_eq] using hi
  have htr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core i (by simpa using hip) hi
  simp only [Array.getElem_toList] at htr
  have hjp : j < indTypes[i].ctors.length := by
    have hlength := Lean4Lean.List.Forall₂.length_eq htr.ctors
    omega
  have hctor := Lean4Lean.List.forall₂_getElem htr.ctors j (by simpa using hjp) hj
  have henv : sourceEnv.WF := by
    simpa only [R.sourceContextVEnv] using R.sourceContext.checking.tr.wf
  have hctx : R.headerVEnv.IsDefEqCtx decl.uvars []
      R.sourceSignatureHeader.params.reverse R.parameterScope.toCtx := by
    simpa only [R.statsWF.uvars, R.checkedParams,
      R.checkedParameterScope, R.sourceSignatureHeader_params] using R.statsWF.paramsContext
  let owner : Fin R.sourceSignatureHeader.families.size :=
    ⟨i, by simpa [sourceSignatureHeader,
      checkInductiveTypes.loopInd.HeaderStatsWF.signatureHeader] using hi⟩
  have howner : R.sourceSignatureHeader.families[owner].name = decl.types[i].name := by
    simp [owner, sourceSignatureHeader,
      checkInductiveTypes.loopInd.HeaderStatsWF.signatureHeader,
      checkInductiveTypes.loopInd.HeaderStatsWF.signatureFamilies,
      checkInductiveTypes.loopInd.HeaderStatsWF.signatureFamily]
  obtain ⟨sourceCtor, hmem, ctor, hsourceName, hname, hctorOwner, htype, hclasses, hfields,
      hreplay⟩ :=
    (R.constructorTails.replay i hip j hjp).signatureConstructor
      (Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core henv) R.core.uvars.symm rfl
      R.sourceSignatureHeader_params_length R.sourceStatsWF.signatureFamilies_names
      rfl hctx owner howner
  have hmem' : sourceCtor ∈ decl.constructorConstants :=
    List.mem_flatMap.mpr ⟨decl.types[i], List.getElem_mem hi, hmem⟩
  have hmemTarget : decl.types[i].ctors[j] ∈ decl.constructorConstants :=
    List.mem_flatMap.mpr ⟨decl.types[i], List.getElem_mem hi, List.getElem_mem hj⟩
  have hsame : sourceCtor = decl.types[i].ctors[j] :=
    List.eq_of_mem_of_nodup_map (VEnv.addConstVals_names_nodup R.core.ctorsAdded)
      hmem' hmemTarget (hsourceName.trans hctor.name.symm)
  cases hsame
  have hijBang : R.classes[i]![j]! = R.classes[i]![j]! := rfl
  have hjBang : indTypes[i]! = indTypes[i] := by simp [hip]
  exact ⟨ctor, by simpa only [hctorOwner] using howner,
    hname.trans hsourceName.symm, htype, hclasses, hfields,
    indTypes[i].ctors[j], List.mem_flatMap.mpr
      ⟨indTypes[i], by simp, List.getElem_mem hjp⟩, hreplay⟩

/-- An owned constructor determines its family and local positions: family and
constructor names are distinct. -/
theorem ownedConstructor_index_unique
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    {i i' j j' : Nat} (hi : i < decl.types.length) (hi' : i' < decl.types.length)
    (hj : j < decl.types[i].ctors.length) (hj' : j' < decl.types[i'].ctors.length)
    (hfamily : decl.types[i] = decl.types[i'])
    (hctor : decl.types[i].ctors[j] = decl.types[i'].ctors[j']) :
    i = i' ∧ j = j' := by
  have hnames : (decl.types.map (fun family => family.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  have hii : i = i' := (List.getElem_inj (h₀ := by simpa using hi)
    (h₁ := by simpa using hi') hnames).mp (by simp [hfamily])
  subst hii
  refine ⟨rfl, ?_⟩
  have hctorNames : (decl.constructorConstants.map VConstVal.name).Nodup :=
    VEnv.addConstVals_names_nodup R.core.ctorsAdded
  have hsub : (decl.types[i].ctors.map VConstVal.name).Sublist
      (decl.constructorConstants.map VConstVal.name) := by
    apply List.Sublist.map
    rw [VInductDecl.constructorConstants, List.flatMap_def]
    exact List.sublist_flatten_of_mem (List.mem_map_of_mem (List.getElem_mem hi))
  exact (List.getElem_inj (h₀ := by simpa using hj) (h₁ := by simpa using hj')
    (hsub.nodup hctorNames)).mp (by simp [hctor])

theorem sourceSignatureHeader_ownedConstructor
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (pair : VInductiveType × VConstVal) (hpair : pair ∈ decl.ownedConstructors) :
    ∃ ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size,
      R.sourceSignatureHeader.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name ∧
      R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType ctor) pair.2.type ∧
      (∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
        pair = (decl.types[i], decl.types[i].ctors[j]) →
        R.sourceSignatureHeader.isUnsafe = true ∨
          ctor.fields.map Field.isRecursive = R.classes[i]![j]!) ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
          (((R.sourceSignatureHeader.fieldTypes ctor).take k).reverse ++
            R.sourceSignatureHeader.params.reverse) k ctor.fields[k]) ∧
      ∃ production ∈ indTypes.toList.flatMap (·.ctors),
        SourceConstructorTelescope R.headerVEnv c.lparams R.parameterScope stats decl
          pair.1 production pair.2 R.sourceSignatureHeader ctor := by
  obtain ⟨family, hfamily, hmapped⟩ := List.mem_flatMap.mp hpair
  obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hmapped
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hfamily
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
  obtain ⟨sig, hfamilyName, hname, htype, hclasses, hfields, hreplay⟩ :=
    R.sourceSignatureHeader_constructor i hi j hj
  refine ⟨sig, hfamilyName, hname, htype, ?_, hfields, hreplay⟩
  intro i' hi' j' hj' hpair'
  obtain ⟨hfam, hctor'⟩ := Prod.mk.inj hpair'
  obtain ⟨rfl, rfl⟩ := R.ownedConstructor_index_unique hi hi' hj hj' hfam hctor'
  exact hclasses

/-- Choose each constructor once, in the declaration's exact flattened
order. All later generation uses these same source-universe choices. -/
noncomputable def sourceSignatureConstructor
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
    InductiveSignature.Constructor R.sourceSignatureHeader.families.size :=
  Classical.choose (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))

noncomputable def sourceSignature
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) : InductiveSignature :=
  { R.sourceSignatureHeader with
    constructors := Array.ofFn R.sourceSignatureConstructor }

theorem sourceSignatureConstructor_name
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
    (R.sourceSignatureConstructor i).name = decl.ownedConstructors[i].2.name :=
  (Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))).2.1

/-- The selected constructor keeps its source family's position, not just
its name. Distinct installed header names determine the owner index. -/
theorem sourceSignatureConstructor_owner
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length)
    (owner : Nat) (howner : owner < decl.types.length)
    (hfamily : decl.ownedConstructors[i].1 = decl.types[owner]) :
    (R.sourceSignatureConstructor i).owner.val = owner := by
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
  let ctor := R.sourceSignatureConstructor i
  have hsize : R.sourceSignatureHeader.families.size = decl.types.length :=
    R.sourceStatsWF.signatureFamilies_size
  have hc : ctor.owner.val < decl.types.length := by
    have := ctor.owner.isLt
    omega
  have hf := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families
    ctor.owner.val (by simp) hc
  have hname : decl.types[ctor.owner.val].name = decl.types[owner].name := by
    have hm : R.sourceSignatureHeader.families[ctor.owner].name =
        decl.ownedConstructors[i].1.name := hmodel.1
    exact hf.1.symm.trans (hm.trans (congrArg (fun family : VInductiveType => family.name) hfamily))
  have hnames : (decl.types.map (fun family => family.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  apply (List.getElem_inj (h₀ := by simpa using hc)
    (h₁ := by simpa using howner) hnames).mp
  simpa only [List.getElem_map] using hname

theorem sourceSignature_fieldType
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (field : Field R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldType k field = R.sourceSignatureHeader.fieldType k field := by
  cases field <;> rfl

theorem sourceSignature_fieldTypes
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldTypes ctor = R.sourceSignatureHeader.fieldTypes ctor := by
  unfold fieldTypes
  apply List.map_congr_left
  intro field _
  exact R.sourceSignature_fieldType field.1

theorem sourceSignature_constructorType
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.constructorType ctor = R.sourceSignatureHeader.constructorType ctor := by
  simp only [constructorType, sourceSignature_fieldTypes]
  rfl

theorem sourceSignature_fieldModel
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (field : Field R.sourceSignatureHeader.families.size) :
    SignatureFieldModel env decl' R.sourceSignature ctx k field ↔
      SignatureFieldModel env decl' R.sourceSignatureHeader ctx k field := by
  cases field <;> rfl

/-- Every selected source constructor keeps its exact checked replay,
including the literal tail used to determine fields and result indices. -/
theorem sourceSignatureConstructor_replay
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length) :
    ∃ production ∈ indTypes.toList.flatMap (·.ctors),
      SourceConstructorTelescope R.headerVEnv c.lparams R.parameterScope stats decl
        decl.ownedConstructors[i].1 production decl.ownedConstructors[i].2
        R.sourceSignature (R.sourceSignatureConstructor i) := by
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
  obtain ⟨production, hproduction, tail, tailTarget, sourceDomains,
    hraw, hprefix, hcomparisons, htranslation, htail, hsynthesis, htype⟩ := hmodel.2.2.2.2.2
  refine ⟨production, hproduction, tail, tailTarget, sourceDomains,
    hraw, hprefix, hcomparisons, htranslation, htail, hsynthesis, ?_⟩
  rw [sourceSignature_constructorType]
  exact htype

/-- The selected replay belongs to the actual kernel constructor with
this name. Global constructor freshness rules out a different source
telescope hidden by the existential replay witness. -/
theorem sourceSignature_replay_of_source
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (i : Fin decl.ownedConstructors.length)
    (source : Constructor) (hsource : source ∈ indTypes.toList.flatMap (·.ctors))
    (hname : source.name = decl.ownedConstructors[i].2.name) :
    SourceConstructorTelescope R.headerVEnv c.lparams R.parameterScope stats decl
      decl.ownedConstructors[i].1 source decl.ownedConstructors[i].2
      R.sourceSignature (R.sourceSignatureConstructor i) := by
  obtain ⟨production, hproduction, hreplay⟩ := R.sourceSignatureConstructor_replay i
  have hraw := hreplay
  obtain ⟨_, _, _, hraw, _⟩ := hraw
  have heq : production = source := List.eq_of_mem_of_nodup_map
    R.kernelConstructorNames_nodup hproduction hsource
    (hraw.name.symm.trans hname.symm)
  simpa only [heq] using hreplay

/-- Arity comes from the exact retained replay of each selected constructor,
not from comparing the types of a fully applied family. -/
theorem sourceSignature_constructorArity
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    ∀ ctor ∈ R.sourceSignature.constructors.toList,
      ctor.indices.length = R.sourceSignature.families[ctor.owner].indices.length := by
  intro ctor member
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  have hi' : i < decl.ownedConstructors.length := by simpa [sourceSignature] using hi
  let position : Fin decl.ownedConstructors.length := ⟨i, hi'⟩
  have hget : R.sourceSignature.constructors.toList[i] = R.sourceSignatureConstructor position := by
    simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn, position]
  rw [hget]
  obtain ⟨production, _, replay⟩ := R.sourceSignatureConstructor_replay position
  have chosen := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem hi'))
  have targetMember : decl.ownedConstructors[i].1 ∈ decl.types := by
    have member := List.getElem_mem hi'
    obtain ⟨family, hfamily, constructor⟩ := List.mem_flatMap.mp member
    obtain ⟨_, _, same⟩ := List.mem_map.mp constructor
    exact (congrArg Prod.fst same) ▸ hfamily
  have names : (decl.types.map (·.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  have ownerBound : (R.sourceSignatureConstructor position).owner.val < decl.types.length := by
    have bound := (R.sourceSignatureConstructor position).owner.isLt
    simpa only [sourceSignatureHeader,
      checkInductiveTypes.loopInd.HeaderStatsWF.signatureHeader,
      checkInductiveTypes.loopInd.HeaderStatsWF.signatureFamilies_size] using bound
  have family := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families
    (R.sourceSignatureConstructor position).owner.val
    (by simp) ownerBound
  have same : decl.types[(R.sourceSignatureConstructor position).owner.val] =
      decl.ownedConstructors[i].1 :=
    List.eq_of_mem_of_nodup_map names (List.getElem_mem ownerBound) targetMember
      (family.1.symm.trans chosen.1)
  apply replay.constructorArity names targetMember R.sourceSignatureHeader_params_length
  simpa only [sourceSignature, Array.getElem_toList, Fin.getElem_fin, same, position] using family.2.1

/-- The complete checked source signature models the source declaration.
Its normalization choices are fixed before the recursor construction begins. -/
private theorem sourceSignature_models_of_nonempty
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) (hnonempty : decl.types ≠ []) :
    R.sourceSignature.Models sourceEnv decl := by
  apply sourceModelsOfTables (s := R.sourceSignature)
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hnonempty
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)) R.core.typesAdded rfl
    R.sourceSignatureHeader_params_length rfl
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      R.sourceSignatureHeader_families
  · apply Lean4Lean.List.forall₂_of_getElem (by simp [sourceSignature])
    intro i hi hi'
    have hmodel := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem hi'))
    have hget : R.sourceSignature.constructors.toList[i] =
        R.sourceSignatureConstructor ⟨i, hi'⟩ := by
      simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn]
    rw [hget]
    refine ⟨hmodel.1, hmodel.2.1, ?_⟩
    have ht : R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType (R.sourceSignatureConstructor ⟨i, hi'⟩))
        decl.ownedConstructors[i].2.type := hmodel.2.2.1
    simpa only [sourceSignature_constructorType] using ht
  · intro ctor hctor k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hi' : i < decl.ownedConstructors.length := by
      simpa [sourceSignature] using hi
    have hmodel := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem hi'))
    have hget : R.sourceSignature.constructors.toList[i] =
        R.sourceSignatureConstructor ⟨i, hi'⟩ := by
      simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn]
    simp only [hget] at hk ⊢
    have hf : SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
        (((R.sourceSignatureHeader.fieldTypes (R.sourceSignatureConstructor ⟨i, hi'⟩)).take k).reverse ++
          R.sourceSignatureHeader.params.reverse) k
        (R.sourceSignatureConstructor ⟨i, hi'⟩).fields[k] := hmodel.2.2.2.2.1 k hk
    apply (R.sourceSignature_fieldModel _).2
    rw [sourceSignature_fieldTypes]
    change SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
      (((R.sourceSignatureHeader.fieldTypes (R.sourceSignatureConstructor ⟨i, hi'⟩)).take k).reverse ++
        R.sourceSignatureHeader.params.reverse) k
      (R.sourceSignatureConstructor ⟨i, hi'⟩).fields[k]
    exact hf
  · exact R.sourceSignature_constructorArity

/-- Source extraction is total even for an empty intermediate table; the
public installation boundary separately enforces declaration nonemptiness. -/
theorem sourceSignature_models
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) : R.sourceSignature.Models sourceEnv decl := by
  by_cases hempty : decl.types = []
  · have hfamilies : R.sourceSignature.families = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp [sourceSignature, sourceSignatureHeader,
        checkInductiveTypes.loopInd.HeaderStatsWF.signatureHeader, hempty]
    have hctors : R.sourceSignature.constructors = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp only [sourceSignature, Array.size_ofFn]
      simp [VInductDecl.ownedConstructors, hempty]
    refine ⟨rfl, R.sourceSignatureHeader_params_length, rfl, ?_,
      ⟨R.headerVEnv, R.core.typesAdded, ?_⟩,
      .inr ⟨R.headerVEnv, R.core.typesAdded, ?_⟩, ?_⟩
    all_goals simp [declaration, hfamilies, hctors, VInductDecl.constructorConstants, hempty]
  · exact R.sourceSignature_models_of_nonempty hempty

theorem headerWF
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.headerVEnv.WF :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core
    (by rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf)

/-- The family applications of the source signature are typed in the header environment. -/
theorem sourceSignature_familyTypesWF_header
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.sourceSignature.FamilyTypesWF R.headerVEnv decl.uvars := by
  intro owner
  have henv := R.headerWF
  have hle : sourceEnv ≤ R.headerVEnv := VEnv.addConstVals_le R.core.typesAdded
  have hheader : owner.val < R.sourceSignatureHeader.families.size := owner.isLt
  have hdecl : owner.val < decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    omega
  have hfam := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families owner.val
    (by simpa using hheader) hdecl
  simp only [Array.getElem_toList] at hfam
  obtain ⟨hname, _, _, hdefeq⟩ := hfam
  have hmem : decl.types[owner.val] ∈ decl.types := List.getElem_mem hdecl
  have hsourceWF := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core
    (List.ne_nil_of_mem hmem) (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
  have huvars : decl.types[owner.val].uvars = decl.uvars := hsourceWF.2.2.1 _ hmem
  have hlookup : R.headerVEnv.constants decl.types[owner.val].name =
      some decl.types[owner.val].toVConstant :=
    VEnv.addConstVals_get R.core.typesAdded (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have hconst := VEnv.HasType.const0 hlookup (henv.ordered.constWF hlookup)
  change R.headerVEnv.HasType decl.types[owner.val].uvars [] (.const decl.types[owner.val].name
      (VLevel.params decl.types[owner.val].uvars)) decl.types[owner.val].type at hconst
  rw [huvars, ← hname] at hconst
  have hW := hconst.defeqU_r henv trivial (hdefeq.symm.mono hle)
  have hWT := hW.isType henv.ordered trivial
  have hctx := (VEnv.IsType.wrapForalls_inv henv.ordered (ctx := []) trivial hWT).1
  simp only [List.append_nil] at hctx
  have happ := VEnv.HasType.mkApps_bvarRange henv hW hctx trivial
  have hctx' : OnCtx (R.sourceSignatureHeader.families[owner.val].indices.reverse ++
      R.sourceSignatureHeader.params.reverse) (R.headerVEnv.IsType decl.uvars) := by
    simpa [List.reverse_append] using hctx
  refine ⟨hctx', ?_⟩
  change R.headerVEnv.HasType decl.uvars
    (R.sourceSignatureHeader.families[owner.val].indices.reverse ++
      R.sourceSignatureHeader.params.reverse)
    (VExpr.mkApps (.const R.sourceSignatureHeader.families[owner.val].name
      (VLevel.params decl.uvars))
      (InductiveSignature.vars R.sourceSignatureHeader.params.length
          R.sourceSignatureHeader.families[owner.val].indices.length ++
        InductiveSignature.vars R.sourceSignatureHeader.families[owner.val].indices.length 0))
    (.sort R.sourceSignatureHeader.families[owner.val].resultLevel)
  rw [InductiveSignature.vars_append_eq_bvarRange, ← List.length_append]
  simpa [List.reverse_append] using happ

end RecursorInput

end VerifyInductive
end Lean4Lean
