import Lean4Lean.Theory.Inductive.CaseEliminators
import Lean4Lean.Verify.Inductive.Constructor.SourceSignature
import Lean4Lean.Theory.Inductive.ConstructorArity
import Lean4Lean.Verify.Inductive.Recursor.Binders.ParameterPrefixes
import Lean4Lean.Verify.Inductive.Formation
import Lean4Lean.Theory.Inductive.CaseProjNames
import Lean4Lean.Theory.Typing.ProjNamesTyping
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! # The checked formation and its source signature

`CheckedFormation` is the data available once every constructor of a declaration is checked
and declared, before any checker run in the recursor-checking environment: the checked headers,
the checked constructor tails and the abstract translation. The source signature of the
declaration (`sourceSignature`, whose model is `sourceSignature_models`) is computed from it, so
the declaration's case eliminator can be certified at this point, before the projections and
the recursors (section 3.2 of the design notes). Abstract case-eliminator certificates live in
`Theory/Inductive/CaseEliminators.lean`. -/

open private Lean4Lean.ordinaryCaseIngredients
  Lean4Lean.ordinaryCaseIngredients.caseEliminators
  Lean4Lean.ordinaryCaseIngredients.own
  from Lean4Lean.Theory.Inductive.CaseEliminators

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel InductiveSignature

structure CheckedFormation (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool) (depth : Nat)
    (sourceEnv : VEnv) (indTypes : Array InductiveType) where
  headerVEnv : VEnv
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  sourceStatsWF : checkInductiveTypes.loopInd.HeaderStatsWF
    sourceContext.venv c.lparams sourceContext.mlctx.vlctx stats decl depth
  headerMLCtx : TypeChecker.MLCtx
  headers : HeaderCertificate sourceEnv decl
  params : List VExpr
  headerParams : headers.params = params
  sourceHeaderParams : sourceStatsWF.headers.params = params
  parameterScope : VLCtx
  sourceParameterScope : sourceStatsWF.parameterScope = parameterScope
  statsWF : checkInductiveTypes.loopInd.HeaderStatsWF
    headerVEnv c.lparams headerMLCtx.vlctx stats decl depth
  checkedParams : statsWF.headers.params = params
  checkedParameterScope : statsWF.parameterScope = parameterScope
  /-- The field classifications returned by the executable constructor check, family by
  family and constructor by constructor. -/
  classes : List (List (List Bool))
  constructorTails : ConstructorTails headerVEnv c.lparams
    parameterScope stats decl indTypes classes
  ctorVEnv : VEnv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl headerVEnv ctorVEnv

end Lean4Lean.VerifyInductive

namespace Lean4Lean.VerifyInductive

/-- The recursor-checking environment of a declaration with certified case eliminators: its constructor
stage with the eliminators, and then with its projection entries, is well formed. -/
theorem _root_.Lean4Lean.VInductBlock.EliminatorsWF.recursorCheckingEnvWF {base envTypes envCtors : VEnv}
    {decl : VInductDecl} {es : List (Name × InductiveSignature.CaseSchema)}
    {lparams : List Name} {nparams : Nat} {types : List Lean.InductiveType} {isUnsafe : Bool}
    (Hcases : VInductBlock.EliminatorsWF base decl (decl.caseBlock es)) (hbase : base.WF)
    (Hcore : TrInductDeclCore base lparams nparams types isUnsafe decl envTypes envCtors)
    (hparams : decl.SourceParameterWF base) :
    (envCtors.addEliminators es).WF ∧
      ((envCtors.addEliminators es).addProjections decl.projectionEntries).WF := by
  have hcases : (envCtors.addEliminators es).WF :=
    Hcases.casesWF hbase (TrInductDeclCore.envCtorsWF Hcore hbase) Hcore.typesAdded
      Hcore.ctorsAdded
  refine ⟨hcases, ?_⟩
  obtain ⟨_, _, _, _, helim⟩ := Hcases
  rcases helim with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, -⟩
  · rw [VInductDecl.projectionEntries_eq_nil hT]
    exact hcases
  exact VEnv.WF.inductProjections (base := base) (envTypes := envTypes)
    (decl := decl) (block := decl.caseBlock es)
    hbase hcases ⟨key, schema, hE, hreg⟩
    (TrInductDeclCore.sourceNames_nodup Hcore) (TrInductDeclCore.typeHeadersWF Hcore)
    (TrInductDeclCore.constructorUvars Hcore) (TrInductDeclCore.constructorsWF Hcore)
    hparams hparams.rawCtorShape rfl rfl rfl Hcore.typesAdded Hcore.ctorsAdded

end Lean4Lean.VerifyInductive

/-! Source signature selections at the checked formation. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
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

namespace CheckedFormation
variable {isUnsafe : Bool}

/-- Constructor identities are unique in the actual kernel constructor array as
well as in its translated table. This identifies retained replays
with the constructors visited by subsequent passes. -/
theorem kernelConstructorNames
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ((indTypes.toList.flatMap (·.ctors)).map Lean.Constructor.name).Nodup := by
  rw [R.kernelConstructorNames]
  exact VEnv.addConstVals_names_nodup R.core.ctorsAdded

/-- Shared source-universe parameters and family choices, before the
eliminator's additional universe is introduced. -/
noncomputable def sourceSignatureHeader
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) : InductiveSignature :=
  R.sourceStatsWF.signatureHeader

theorem sourceSignatureHeader_params
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) : R.sourceSignatureHeader.params = R.params :=
  R.sourceHeaderParams

theorem sourceSignatureHeader_params_length
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) : R.sourceSignatureHeader.params.length = decl.nparams :=
  R.sourceStatsWF.signatureParams_length

theorem sourceSignatureHeader_families
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length) :
    InductiveSignature.Constructor R.sourceSignatureHeader.families.size :=
  Classical.choose (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))

noncomputable def sourceSignature
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) : InductiveSignature :=
  { R.sourceSignatureHeader with
    constructors := Array.ofFn R.sourceSignatureConstructor }

theorem sourceSignatureConstructor_name
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length) :
    (R.sourceSignatureConstructor i).name = decl.ownedConstructors[i].2.name :=
  (Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))).2.1

/-- The selected constructor keeps its source family's position, not just
its name. Distinct installed header names determine the owner index. -/
theorem sourceSignatureConstructor_owner
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length)
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (field : Field R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldType k field = R.sourceSignatureHeader.fieldType k field := by
  cases field <;> rfl

theorem sourceSignature_fieldTypes
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.fieldTypes ctor = R.sourceSignatureHeader.fieldTypes ctor := by
  unfold fieldTypes
  apply List.map_congr_left
  intro field _
  exact R.sourceSignature_fieldType field.1

theorem sourceSignature_constructorType
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (ctor : InductiveSignature.Constructor R.sourceSignatureHeader.families.size) :
    R.sourceSignature.constructorType ctor = R.sourceSignatureHeader.constructorType ctor := by
  simp only [constructorType, sourceSignature_fieldTypes]
  rfl

theorem sourceSignature_fieldModel
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (field : Field R.sourceSignatureHeader.families.size) :
    SignatureFieldModel env decl' R.sourceSignature ctx k field ↔
      SignatureFieldModel env decl' R.sourceSignatureHeader ctx k field := by
  cases field <;> rfl

/-- Every selected source constructor keeps its exact checked replay,
including the literal tail used to determine fields and result indices. -/
theorem sourceSignatureConstructor_replay
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length) :
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (i : Fin decl.ownedConstructors.length)
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) (hnonempty : decl.types ≠ []) :
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
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) : R.sourceSignature.Models sourceEnv decl := by
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

/-! ### The case eliminator certified at the checked formation -/

theorem headerWF
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    R.headerVEnv.WF :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core
    (by rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf)

/-- The family applications of the source signature are typed in the header environment. -/
theorem sourceSignature_familyTypesWF_header
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
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

/-- The key of the declaration's case eliminator: its first family. -/
noncomputable def caseKey
    (_R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) : Name :=
  (decl.types.head?.map (·.name)).getD default

/-- The declaration's case schema: the source signature, without restoration. -/
noncomputable def caseSchema
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    InductiveSignature.CaseSchema :=
  InductiveSignature.CaseSchema.ofCompilation decl R.sourceSignature []

open Classical in
/-- The declaration's case eliminators: none for an empty declaration (which has no
projections), its case schema under its key otherwise. -/
noncomputable def caseEliminators
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    List (Name × InductiveSignature.CaseSchema) :=
  if decl.types = [] then [] else [(R.caseKey, R.caseSchema)]

private theorem mapM_expr_empty (l : List VExpr) :
    l.mapM ({} : InductiveSignature.Restoration).expr = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih]

/-- Every piece of the source signature projects only out of structures registered in the
constructor environment. -/
theorem caseSchema_projNamesRegistered
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hdeclNe : decl.types ≠ []) :
    R.caseSchema.ProjNamesRegistered R.ctorVEnv R.caseKey := by
  have hsrcWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  have hleH : sourceEnv ≤ R.headerVEnv := VEnv.addConstVals_le R.core.typesAdded
  have hleC : R.headerVEnv ≤ R.ctorVEnv := VEnv.addConstVals_le R.core.ctorsAdded
  have hokS : ∀ {e : VExpr}, e.ProjNamesOK (fun S => ∃ info, sourceEnv.projections S info) →
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) :=
    VExpr.ProjNamesOK.mono fun _ ⟨info, h⟩ => ⟨info, (hleH.trans hleC).projections h⟩
  have hokH : ∀ {e : VExpr}, e.ProjNamesOK (fun S => ∃ info, R.headerVEnv.projections S info) →
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) :=
    VExpr.ProjNamesOK.mono fun _ ⟨info, h⟩ => ⟨info, hleC.projections h⟩
  -- the header pieces
  have hheaders : ∀ f ∈ R.sourceSignatureHeader.families.toList,
      (VExpr.wrapForalls (R.sourceSignatureHeader.params ++ f.indices) (.sort f.resultLevel)).ProjNamesOK
        (fun S => ∃ info, sourceEnv.projections S info) := by
    intro f hf
    obtain ⟨src, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_l R.sourceSignatureHeader_families f hf
    obtain ⟨_, hd⟩ := h.2.2.2
    exact (hd.projNamesOK hsrcWF.ordered trivial).1
  have hfamNe : 0 < R.sourceSignatureHeader.families.size := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    have : 0 < decl.types.length := List.length_pos_iff.mpr hdeclNe
    omega
  have hparams : ∀ e ∈ R.caseSchema.signature.params,
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro e he
    have h := (VExpr.ProjNamesOK.wrapForalls_inv
      (hheaders _ (Array.getElem_mem_toList (i := 0) hfamNe))).1 e (List.mem_append_left _ he)
    exact hokS h
  have hindices : ∀ f ∈ R.caseSchema.signature.families.toList, ∀ e ∈ f.indices,
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro f hf e he
    exact hokS ((VExpr.ProjNamesOK.wrapForalls_inv (hheaders f hf)).1 e (List.mem_append_right _ he))
  have hctor' : ∀ i : Fin decl.ownedConstructors.length,
      (R.sourceSignatureHeader.constructorType (R.sourceSignatureConstructor i)).ProjNamesOK
        (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro i
    obtain ⟨_, _, hdef, _⟩ := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
    obtain ⟨_, hd⟩ := hdef
    exact hokH (hd.projNamesOK R.headerWF.ordered trivial).1
  have hmem : ∀ c ∈ R.caseSchema.signature.constructors.toList,
      ∃ i, R.sourceSignatureConstructor i = c := by
    intro c hc
    have hc' : c ∈ (Array.ofFn R.sourceSignatureConstructor).toList := hc
    rw [Array.toList_ofFn] at hc'
    exact List.mem_ofFn.mp hc'
  have hfields : ∀ c ∈ R.caseSchema.signature.constructors.toList,
      ∀ e ∈ R.caseSchema.signature.fieldTypes c,
        e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro c hc e he
    obtain ⟨i, rfl⟩ := hmem c hc
    have h := VExpr.ProjNamesOK.wrapForalls_inv (hctor' i)
    have he' : e ∈ R.sourceSignature.fieldTypes (R.sourceSignatureConstructor i) := he
    rw [R.sourceSignature_fieldTypes] at he'
    exact h.1 e (List.mem_append_right _ he')
  have hcindices : ∀ c ∈ R.caseSchema.signature.constructors.toList, ∀ e ∈ c.indices,
      e.ProjNamesOK (fun S => ∃ info, R.ctorVEnv.projections S info) := by
    intro c hc e he
    obtain ⟨i, rfl⟩ := hmem c hc
    have h := (VExpr.ProjNamesOK.wrapForalls_inv (hctor' i)).2
    exact (VExpr.ProjNamesOK.mkApps_inv h).2 e (List.mem_append_right _ he)
  have H := InductiveSignature.CaseSchema.projNamesOK_of_pieces (schema := R.caseSchema) rfl
    hparams hindices hfields hcindices R.caseKey
  exact ⟨H.1, H.2⟩

/-- The source families' declared headers are their normalized headers. -/
theorem caseSchema_headerAgreement
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    R.caseSchema.HeaderAgreement sourceEnv decl := by
  refine ⟨R.sourceSignatureHeader.params, mapM_expr_empty _, fun owner => ?_⟩
  refine ⟨(R.sourceSignatureHeader.families[owner.val]'owner.isLt).indices, mapM_expr_empty _,
    fun type htype hname => ⟨R.headerVEnv, R.core.typesAdded, ?_⟩⟩
  have hdecl : owner.val < decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    have := owner.isLt
    change owner.val < R.sourceSignatureHeader.families.size at this
    omega
  have hown : owner.val < R.sourceSignatureHeader.families.size := owner.isLt
  have hfam := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families owner.val
    (by simpa using hown) hdecl
  simp only [Array.getElem_toList] at hfam
  obtain ⟨hname', _, _, hdefeq⟩ := hfam
  have hsame : type = decl.types[owner.val] := by
    have hnodup : (decl.types.map (·.name)).Nodup := by
      have := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
      simp only [VInductDecl.sourceNames, VInductDecl.typeConstants, List.map_map] at this
      exact (List.nodup_append.mp this).1
    exact List.eq_of_mem_of_nodup_map hnodup htype (List.getElem_mem hdecl)
      (hname.trans hname')
  subst hsame
  exact (hdefeq.mono (VEnv.addConstVals_le R.core.typesAdded)).symm

/-- **The declaration's case eliminator is certified at the checked formation.** -/
theorem caseEliminatorsWF
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock R.caseEliminators) := by
  refine ⟨R.headerVEnv, R.ctorVEnv, R.core.typesAdded, R.core.ctorsAdded, ?_⟩
  by_cases hne : decl.types = []
  · exact .inl ⟨hne, by simp [VInductDecl.caseBlock, caseEliminators, hne]⟩
  refine .inr ⟨R.caseKey, R.caseSchema, by simp [VInductDecl.caseBlock, caseEliminators, hne],
    ⟨?_, ?_, R.caseSchema_headerAgreement⟩, R.caseSchema_projNamesRegistered hne⟩
  · have hsource := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hne
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
    exact InductiveSignature.CaseSchema.ofCaseCompilation_certified
      (InductiveSignature.CaseCompilationData.ofOrdinary hsource R.formation.formationWF
        R.sourceSignature_models R.core.typesAdded R.core.ctorsAdded
        (es := []) (fun _ h => by cases h)
        (R.sourceSignature_familyTypesWF_header.mono
          ((VEnv.addConstVals_le R.core.ctorsAdded).trans VEnv.addProjections_le))
        rfl rfl rfl) .nil InductiveSignature.recursorNamesFresh_nil
  · cases htypes : decl.types with
    | nil => exact absurd htypes hne
    | cons family families => simp [caseKey, htypes]

private theorem caseIngredients
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    Lean4Lean.ordinaryCaseIngredients sourceEnv decl R.caseEliminators := by
  by_cases hne : decl.types = []
  · exact .inl ⟨hne, by simp [caseEliminators, hne]⟩
  refine .inr ⟨R.sourceSignature, R.caseKey, by simp [caseEliminators, hne, caseSchema], ?_,
    Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hne
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core),
    R.formation.formationWF, R.sourceSignature_models, R.headerVEnv, R.ctorVEnv,
    R.core.typesAdded, R.core.ctorsAdded,
    R.sourceSignature_familyTypesWF_header.mono
      ((VEnv.addConstVals_le R.core.ctorsAdded).trans VEnv.addProjections_le),
    R.caseSchema_projNamesRegistered hne, R.caseSchema_headerAgreement⟩
  cases htypes : decl.types with
  | nil => exact absurd htypes hne
  | cons family families => simp [caseKey, htypes]

/-- **The declaration's case eliminators are certified along every extension.** -/
theorem caseEliminatorsCertified
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    decl.CaseEliminators sourceEnv (fun _ => False) R.caseEliminators :=
  R.caseIngredients.caseEliminators

/-- The declaration's case eliminators are its own restoration-free case schemas. -/
theorem caseEliminatorsOwn
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    decl.OwnCaseEliminators sourceEnv R.caseEliminators :=
  R.caseIngredients.own

/-- The recursor-checking environment of the declaration: its constructor stage with its case eliminators, and then
with its projection entries, is well formed. -/
theorem recursorCheckingEnvWF
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    (R.ctorVEnv.addEliminators R.caseEliminators).WF ∧
      ((R.ctorVEnv.addEliminators R.caseEliminators).addProjections
        decl.projectionEntries).WF :=
  R.caseEliminatorsWF.recursorCheckingEnvWF (by rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf)
    R.core R.formation.formationWF.sourceParameterWF

/-- The constructor stage with the declaration's case eliminators is well formed. -/
theorem casesWF
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    (R.ctorVEnv.addEliminators R.caseEliminators).WF :=
  R.recursorCheckingEnvWF.1

/-- The constructor stage with the declaration's case eliminators and projections is well
formed. -/
theorem projectedWF
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ((R.ctorVEnv.addEliminators R.caseEliminators).addProjections decl.projectionEntries).WF :=
  R.recursorCheckingEnvWF.2

end CheckedFormation
end Lean4Lean.VerifyInductive
