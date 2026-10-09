import Lean4Lean.Verify.Inductive.Recursor.Entries.AddConstants
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation
import Lean4Lean.Verify.Inductive.Constructor.ParameterSyntacticTranslation
import Lean4Lean.Verify.Inductive.Constructor.Telescopes

/-! The environments of the ordinary pipeline: the header environment
(`HeaderEnvironment`), the constructor environment (`ConstructorEnvironment`),
the recursor-checking environment (`RecursorCheckingEnvironment`) and the
ordinary constructor check (`OrdinaryConstructorCheck`), with the facts linking
the executable header and constructor folds to the abstract declaration:
installed-family lookups, agreement of constructor parameters, and the checked
formation (`HeaderEnvironment.toCheckedFormation`).  See section 3.2 of
the design notes. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Every abstract value in an ordinary lockstep installation has the same
non-primitive name as its kernel constant. -/
theorem AddConstants.valueNamesNonprimitive
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ name ∈ (entries.map Prod.snd).map VConstVal.name,
      ¬ Kernel.Environment.primitives.contains name := by
  induction H with
  | nil => simp
  | cons _hn hnprim htr _hwf _hadd _hdelta _Htail ih =>
    intro name hname
    simp only [List.map_cons, List.mem_cons] at hname
    rcases hname with hhead | htail
    · subst name
      simpa [htr.2] using hnprim
    · exact ih name htail

/-- A primitive lookup visible after an `AddConstants` fold was already
visible before the fold, since every installed name is non-primitive. -/
theorem AddConstants.sourceContainsOfTargetContainsPrimitive
    (H : AddConstants safety env source entries outEnv target)
    (hprimitive : Kernel.Environment.primitives.contains name)
    (htarget : target.contains name) : source.contains name := by
  rcases htarget with ⟨ci, hlookup⟩
  refine ⟨ci, ?_⟩
  rw [VEnv.addConstVals_constants_of_forall_ne H.abstract ?_] at hlookup
  · exact hlookup
  · intro value hvalue hname
    apply H.valueNamesNonprimitive value.name
      (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
    simpa [hname] using hprimitive

/-- Literal availability cannot be introduced by an ordinary non-primitive
constant fold: each name controlling literal support is reserved. -/
theorem AddConstants.sourceContainsLits
    (H : AddConstants safety env source entries outEnv target)
    (hlit : target.ContainsLits literal) : source.ContainsLits literal := by
  cases literal with
  | natVal n =>
      exact H.sourceContainsOfTargetContainsPrimitive (by
        simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]) hlit
  | strVal s =>
      exact ⟨H.sourceContainsOfTargetContainsPrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]) hlit.1,
        H.sourceContainsOfTargetContainsPrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]) hlit.2⟩

/-- The environment-indexed literal condition is preserved by an ordinary
non-primitive constant installation. -/
theorem AddConstants.availableLiteralDisjoint
    (H : AddConstants safety prodEnv source entries outProd target)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint source indConsts) :
    checkPositivityStep.AvailableLiteralDisjoint target indConsts :=
  fun literal havailable => hlit literal (H.sourceContainsLits havailable)

theorem InductInfosFromDecl.addConstants
    {source middle target : Environment}
    (O : InductInfosFromDecl source.constants middle.constants decl)
    (H : AddConstants safety middle venv entries target outVEnv)
    (hwf : middle.constants.WF)
    (hnind : ∀ (info : ConstantInfo) (value : VConstVal),
      (info, value) ∈ entries → ∀ inductiveValue,
        info ≠ ConstantInfo.inductInfo inductiveValue) :
    InductInfosFromDecl source.constants target.constants decl := by
  intro familyName familyInfo hfamily
  have htargetWF := H.targetMapWF hwf
  have hfamilyEnv : target.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?]
    exact hfamily
  rcases H.entryOrigin hwf hfamilyEnv with hold | hnew
  · have holdMap : middle.constants.find? familyName =
        some (.inductInfo familyInfo) := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hold
    rcases O familyName familyInfo holdMap with hsource | hcurrent
    · exact Or.inl hsource
    · rcases hcurrent with ⟨familyIdx, hname, ⟨A⟩⟩
      exact Or.inr ⟨familyIdx, hname, ⟨A.rebase
        (by simpa [← hname] using hfamily)
        (H.preservesMapFind hwf)⟩⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    exact False.elim (hnind entry.1 entry.2 hentry familyInfo hinfo.symm)

/-- Non-circular result of mutual header declaration. It retains typed
headers, raw constructor correspondence, and the exact installed header
environment, but makes no constructor-WF claim. -/
structure HeaderEnvironment (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool)
    (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  entries : List (ConstantInfo × VConstVal)
  infos : ∃ numNested,
    entries.map Prod.fst =
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList.map (fun info => .inductInfo info)
  sourceAligned : ∃ numNested,
    InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList entries
  values : entries.map Prod.snd = decl.typeConstants
  context : ContextWF { c with env := outEnv }
  headers : HeaderCertificate sourceEnv decl
  translation : TrInductDeclHeaders sourceEnv c.lparams nparams
    indTypes.toList isUnsafe decl context.venv
  installed : AddConstants c.safety c.env sourceEnv entries outEnv context.venv
  sourceContext : ContextWF c
  /-- Every constructor a header of the source environment lists is present there. -/
  sourcePresent : ListedConstructorsPresent c.env
  sourceContextVEnv : sourceContext.venv = sourceEnv
  sourceStatsWF : checkInductiveTypes.loopInd.HeaderStatsWF
    sourceContext.venv c.lparams sourceContext.mlctx.vlctx stats decl depth
  sourceHeaderParams : sourceStatsWF.headers.params = headers.params
  statsWF : checkInductiveTypes.loopInd.HeaderStatsWF
    context.venv c.lparams context.mlctx.vlctx stats decl depth
  headerParams : statsWF.headers.params = headers.params
  parameterScopeEq : statsWF.parameterScope =
    sourceStatsWF.parameterScope

theorem HeaderEnvironment.entriesNoRecursor
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv) :
    ∀ entry ∈ H.entries, ∀ r, entry.1 ≠ .recInfo r := by
  intro entry hentry r heq
  obtain ⟨numNested, hprod⟩ := H.infos
  have : entry.1 ∈ H.entries.map Prod.fst := List.mem_map_of_mem hentry
  rw [hprod] at this
  obtain ⟨_, _, h⟩ := List.mem_map.mp this
  rw [heq] at h
  cases h

def HeaderEnvironment.formation
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (Hchecked : CheckedConstructors sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams
      H.statsWF.parameterScope classes) :
    FormationCertificate sourceEnv decl where
  headers := H.headers
  envTypes := H.context.venv
  typesInstalled := H.translation.typesAdded
  constructorParameters := Hchecked.parameterShapes
    H.context.checking.tr.wf H.translation.types
    (H.statsWF.parameterEmbedding.scopeWF H.context.checking.tr.wf)
    (checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped
      H.statsWF).params_size
    H.statsWF.uvars.symm (by
      rw [← H.headerParams]
      exact H.statsWF.paramsContext)
  constructors := Hchecked.checked.formation
  rawShapes := Hchecked.rawShapes H.context.checking.tr.wf H.translation.types
    (H.statsWF.parameterEmbedding.scopeWF H.context.checking.tr.wf)
    (checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped
      H.statsWF).params_size

theorem AddConstants.entryTr
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ entry ∈ entries, (∃ venv', TrConstVal safety venv' entry.1 entry.2) ∧
      entry.1.deltaValue? = none := by
  induction H with
  | nil => simp
  | cons _ _ htr _ _ hdelta _ ih =>
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | h
    · exact ⟨⟨_, htr⟩, hdelta⟩
    · exact ih entry h

/-- An installation of translated, non-recursor constants keeps the environment ghost-free. -/
theorem AddConstants.envGhostFree
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) (henv : TypeChecker.EnvGhostFree (fun _ => True) env)
    (hnorec : ∀ entry ∈ entries, ∀ r, entry.1 ≠ .recInfo r) :
    TypeChecker.EnvGhostFree (fun _ => True) outEnv := by
  intro n found hfind
  rcases H.entryOrigin hwf hfind with h | ⟨entry, hentry, -, rfl⟩
  · exact henv h
  · obtain ⟨⟨_, htr, -⟩, hdelta⟩ := H.entryTr entry hentry
    exact ⟨htr.2.2.envGhostFree, fun v hv => (by rw [hdelta] at hv; cases hv),
      fun r hr => absurd hr (hnorec entry hentry r)⟩

/-- The constructor check certifies the telescope of every source constructor type. -/
theorem AddInductive.checkConstructors.telescopesWF
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) outEnv) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        SourceCtorsCertified H.context.venv c.lparams indTypes.toList := by
  have Hloops := checkConstructors.loopTypes.telTrWF
    (indTypes := indTypes) (stats := stats) (isUnsafe := isUnsafe)
    H.statsWF.parameterSuffix.headerCheck henv 0
  rw [AddInductive.checkConstructors]
  refine AddInductive.M.WF_bind (P := fun _ => True) (fun _ _ => trivial)
    fun _ _ => ?_
  refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
  subst hL
  rw [AddInductive.withCheckLCtx_apply]
  refine Hloops.mono fun _ h owner howner ctor hctor => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem howner
  obtain ⟨T, hT⟩ := h i (Nat.zero_le _) (by simpa using hi) ctor (by simpa using hctor)
  exact ⟨T, hT⟩

/-- Constructor checking consumes only the raw constructor translations
retained by header installation and returns both formation and pointwise
constructor typing.  In particular this boundary does not assume the source
constructor constants are already well-formed. -/
theorem AddInductive.checkConstructors.checkedWF
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hlparams : c.lparams.Nodup) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun classes =>
        CheckedConstructors sourceEnv decl H.context.venv
          H.headers.params stats indTypes c.lparams
          H.statsWF.parameterScope classes := by
  have Hloops := checkConstructors.loopTypes.refinesChecked
    H.statsWF.parameterSuffix.headerCheck H.translation.types
    H.translation.typesAdded H.statsWF
    H.headerParams H.statsWF.parameterSuffix.headerCheck_paramAligned
    hconsume hlit hunsafe H.statsWF.universeBound hlparams
  rw [AddInductive.checkConstructors]
  refine AddInductive.M.WF_bind (P := fun _ => True) (fun _ _ => trivial)
    fun _ _ => ?_
  -- Constructors are checked on top of the parameters.
  refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
  subst hL
  rw [AddInductive.withCheckLCtx_apply]
  exact Hloops

/-- The same executable constructor check also retains the owner
normal form for every constructor.  This proof is kept as an independent
projection so the abstract formation certificate does not depend on the
later recursor implementation. -/
theorem AddInductive.checkConstructors.ownerNormalFormsWF
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        ConstructorOwnerNormalForms stats indTypes := by
  let Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      H.statsWF.parameterSuffix.headerCheck stats depth :=
    H.statsWF.parameterSuffix.toHeaderCheck
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped
      H.statsWF
  have Hloops := checkConstructors.loopTypes.ownerNormalFormsWF
    (Q := fun _ => ConstructorOwnerNormalForms stats indTypes)
    (isUnsafe := isUnsafe)
    H.statsWF.parameterSuffix.headerCheck H.translation.types
    (ConstructorOwnerNormalFormRows.empty stats indTypes)
    Hsuffix Hstats H.statsWF.parameterSuffix.headerCheck_paramAligned
    hconsume hlit
    (fun Hrows _ => Hrows.complete)
  rw [AddInductive.checkConstructors]
  refine AddInductive.M.WF_bind (P := fun _ => True) (fun _ _ => trivial)
    fun _ _ => ?_
  -- Constructors are checked on top of the parameters.
  refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
  subst hL
  rw [AddInductive.withCheckLCtx_apply]
  exact Hloops

/-- The constructor environment, the result of the constructor-info fold.  It
retains the exact abstract constructor environment and the typed pointwise
source translation needed to join the header and constructor phases. -/
structure ConstructorEnvironment
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (outEnv : Environment) where
  venvCtors : VEnv
  entries : List (ConstantInfo × VConstVal)
  values : entries.map Prod.snd = decl.constructorConstants
  installed : AddConstants c.safety headerEnv H.context.venv entries
    outEnv venvCtors
  sourceAligned : ConstructorTypeEntries
    (AddInductive.constructorInfo stats c.lparams isUnsafe)
    indTypes.toList entries
  infos : ∀ entry ∈ entries,
    ∃ info : ConstructorVal, entry.1 = ConstantInfo.ctorInfo info
  nonInductive : ∀ (entry : ConstantInfo × VConstVal), entry ∈ entries →
    ∀ (value : InductiveVal),
    entry.1 ≠ ConstantInfo.inductInfo value
  translation : TrInductDeclConstructors H.context.venv c.lparams
    indTypes.toList decl venvCtors

/-- The recursor-checking environment.  Its abstract environment is the
constructor environment together with the declaration's case eliminators and
projection table: the projection registry must already be present when the
recursor construction runs the type checker in this context, and
`inductProjections` admits the table exactly at this point of the installation. -/
structure RecursorCheckingEnvironment
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (outEnv : Environment) extends ConstructorEnvironment H outEnv where
  /-- The declaration's case eliminator, certified by the checked formation
  (`CheckedFormation.caseEliminatorsWF`). -/
  eliminators : List (Name × InductiveSignature.CaseSchema)
  eliminatorsWF : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock eliminators)
  eliminatorsCertified : decl.CaseEliminators sourceEnv (fun _ => False) eliminators
  eliminatorsOwn : decl.OwnCaseEliminators sourceEnv eliminators
  /-- The eliminators are those of a checked formation of the declaration, so their
  signature is its source signature. -/
  eliminatorsBoundary : ∃ B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv
    indTypes, eliminators = B.caseEliminators ∧ B.params = H.headers.params ∧
      B.parameterScope = H.statsWF.parameterScope
  context : ContextWF { c with env := outEnv }
  contextVEnv : context.venv =
    (venvCtors.addEliminators eliminators).addProjections decl.projectionEntries
  contextMLCtx : context.mlctx = H.context.mlctx

/-- Select one newly installed kernel constructor by its source family and
owner-local index, and prove the coherence of its common parameters with the
abstract declaration.  This links the executable header and constructor folds
positionally to the independent formation specification. -/
theorem ConstructorEnvironment.installedConstructorCoherenceAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (D : ConstructorEnvironment H outEnv)
    (core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
      isUnsafe decl H.context.venv D.venvCtors)
    (Hchecked : CheckedConstructors sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams H.statsWF.parameterScope classes)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ familyInfo : InductiveVal,
      ∃ hi : ctorIdx < familyInfo.ctors.length,
        familyInfo.name = indTypes[familyIdx].name ∧
        familyInfo.ctors = indTypes[familyIdx].ctors.map (fun ctor => ctor.name) ∧
        outEnv.find? familyInfo.name = some (.inductInfo familyInfo) ∧
        Nonempty (ConstructorParameterAlignmentAt
          outEnv D.venvCtors familyInfo.name familyInfo ctorIdx hi) := by
  rcases H.sourceAligned with ⟨numNested, Haligned⟩
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, H.statsWF.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length core).symm
      _ = indTypes.size := by simp
  have hinfosSize : infos.size = indTypes.size := by
    simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hinfoIdx : familyIdx < infos.size := by simpa [hinfosSize] using hfamily
  let familyInfo := infos[familyIdx]
  have hfamilyInfoMem : familyInfo ∈ infos.toList := by
    apply Array.mem_toList_iff.mpr
    simp [familyInfo]
  have hfamilyName : familyInfo.name = indTypes[familyIdx].name := by
    simp [familyInfo, infos, AddInductive.inductiveTypeInfos]
  have hfamilyCtors : familyInfo.ctors =
      indTypes[familyIdx].ctors.map (fun ctor => ctor.name) := by
    simp [familyInfo, infos, AddInductive.inductiveTypeInfos]
  have hi : ctorIdx < familyInfo.ctors.length := by
    simpa [hfamilyCtors] using hctor
  rcases Haligned.findInfo hfamilyInfoMem with ⟨familyValue, hfamilyEntry⟩
  have hfamilyHeader :
      headerEnv.find? familyInfo.name = some (.inductInfo familyInfo) :=
    H.installed.findEntry H.sourceContext.checking.tr.map_wf hfamilyEntry
  have hfamilyLookup :
      outEnv.find? familyInfo.name = some (.inductInfo familyInfo) :=
    D.installed.preservesSourceFind H.context.checking.tr.map_wf
      hfamilyHeader
  let sourceFamily := indTypes[familyIdx]
  let sourceCtor := sourceFamily.ctors[ctorIdx]
  let ctorInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
    sourceFamily ctorIdx sourceCtor
  rcases D.sourceAligned.findAt
      (owner := sourceFamily) (List.getElem_mem hfamily)
      ctorIdx hctor with ⟨ctorValue, hctorEntry⟩
  have hctorLookupExact :
      outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
    D.installed.findEntry H.context.checking.tr.map_wf hctorEntry
  have hctorLookup :
      outEnv.find? familyInfo.ctors[ctorIdx] = some (.ctorInfo ctorInfo) := by
    simpa [ctorInfo, sourceCtor, sourceFamily, hfamilyCtors,
      AddInductive.constructorInfo] using hctorLookupExact
  have htargetFamily : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length core]
    simpa using hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt core
    familyIdx (by simpa using hfamily) htargetFamily
  have htargetCtor : ctorIdx < decl.types[familyIdx].ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
    simpa [sourceFamily] using hctor
  have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
    ctorIdx (by simpa [sourceFamily] using hctor) htargetCtor
  have hfamilyTargetLookup : D.venvCtors.constants familyInfo.name =
      some decl.types[familyIdx].toVConstant := by
    have hlookup : H.context.venv.constants decl.types[familyIdx].name =
        some decl.types[familyIdx].toVConstant := by
      apply VEnv.addConstVals_get core.typesAdded
      exact List.mem_map.mpr
        ⟨decl.types[familyIdx], List.getElem_mem htargetFamily, rfl⟩
    simpa [hfamilyName, Htype.header.name] using
      (VEnv.addConstVals_le core.ctorsAdded).constants hlookup
  have hctorTargetLookup : D.venvCtors.constants
      familyInfo.ctors[ctorIdx] =
      some decl.types[familyIdx].ctors[ctorIdx].toVConstant := by
    have hlookup := VEnv.addConstVals_get core.ctorsAdded
      (ci := decl.types[familyIdx].ctors[ctorIdx]) (by
        simp only [VInductDecl.constructorConstants]
        apply List.mem_flatMap.mpr
        exact ⟨decl.types[familyIdx], List.getElem_mem htargetFamily,
          List.getElem_mem htargetCtor⟩)
    simpa [hfamilyCtors, sourceFamily, Hctor.name] using hlookup
  have hfinalWF : D.venvCtors.WF :=
    (D.installed.checking H.context.checking.tr).wf
  have hparamsSize : stats.params.size = decl.nparams := by
    have hlength := List.Forall₂.length_eq
      H.statsWF.params
    simpa [VInductDecl.paramVars] using hlength
  let C : CtorInfoCoherentAt outEnv familyInfo.name familyInfo
      ctorIdx hi := {
    info := ctorInfo
    lookup := hctorLookup
    induct := by
      simp [ctorInfo, sourceFamily, AddInductive.constructorInfo, hfamilyName]
    cidx := by simp [ctorInfo, AddInductive.constructorInfo]
    numParams := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo, hparamsSize, core.nparams]
    levelParams := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo]
    isUnsafe := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo] }
  refine ⟨familyInfo, hi, hfamilyName, hfamilyCtors, hfamilyLookup, ?_⟩
  apply ConstructorParameterAlignmentAt.ofShapes C hfinalWF
    decl.types[familyIdx] decl.types[familyIdx].ctors[ctorIdx]
    hfamilyTargetLookup hctorTargetLookup
  · exact Htype.header.uvars.trans core.uvars.symm
  · exact Hctor.uvars.trans core.uvars.symm
  · simp [familyInfo, infos, AddInductive.inductiveTypeInfos,
      core.uvars]
  · simp [familyInfo, infos, AddInductive.inductiveTypeInfos,
      core.nparams]
  · exact H.headers.typeShapes _ (List.getElem_mem htargetFamily)
  · exact Hchecked.checked.formation.ctorShape
      (List.getElem_mem htargetFamily) (List.getElem_mem htargetCtor)
  · exact H.installed.le.trans D.installed.le
  · exact D.installed.le

/-- The executable header and constructor folds identify every newly visible
inductive family of the kernel environment with one exact source declaration
position. -/
theorem ConstructorEnvironment.inductInfosFromDecl
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (D : ConstructorEnvironment H outEnv)
    (core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
      isUnsafe decl H.context.venv D.venvCtors)
    (Hchecked : CheckedConstructors sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams H.statsWF.parameterScope classes) :
    InductInfosFromDecl c.env.constants outEnv.constants decl := by
  intro familyName familyInfo hfamily
  have hsourceWF := H.sourceContext.checking.tr.map_wf
  have hheaderWF := H.context.checking.tr.map_wf
  have houtWF := D.installed.targetMapWF hheaderWF
  have hfamilyEnv : outEnv.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
    exact hfamily
  rcases D.installed.entryOrigin hheaderWF hfamilyEnv with
      hheader | hctorOrigin
  · rcases H.installed.entryOrigin hsourceWF hheader with hold | hnew
    · left
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?] at hold
    · right
      rcases hnew with ⟨entry, hentry, hentryName, hentryValue⟩
      rcases H.sourceAligned with ⟨numNested, Haligned⟩
      rcases Haligned.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
      have hinfoEq : familyInfo = info := by
        have heq : ConstantInfo.inductInfo familyInfo = .inductInfo info :=
          hentryValue.trans hentryInfo
        cases heq
        rfl
      subst info
      rcases List.mem_iff_getElem.mp hinfo with
        ⟨familyIdx, hfamilyInfo, hfamilyInfoEq⟩
      let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
        numNested isUnsafe c.lparams
      have hindicesSize : stats.nindices.size = indTypes.size := by
        calc
          stats.nindices.size = decl.types.length := by
            rw [Array.size_eq_length_toList, H.statsWF.indices,
              List.length_map]
          _ = indTypes.toList.length :=
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              core).symm
          _ = indTypes.size := by simp
      have hparamsSize : stats.params.size = decl.nparams := by
        have hlength := List.Forall₂.length_eq
          H.statsWF.params
        simpa [VInductDecl.paramVars] using hlength
      have hinfosSize : infos.size = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      have hfamilyIdx : familyIdx < indTypes.size := by
        have : familyIdx < infos.toList.length := by
          simpa [infos] using hfamilyInfo
        simpa [hinfosSize] using this
      have htargetIdx : familyIdx < decl.types.length := by
        rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length core]
        simpa using hfamilyIdx
      have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt core
        familyIdx (by simpa using hfamilyIdx) htargetIdx
      have hfamilyInfoExact : familyInfo = infos[familyIdx] := by
        rw [← hfamilyInfoEq]
        exact Array.getElem_toList (by simpa [infos] using hfamilyInfo)
      have hfamilyNameEq : familyName = familyInfo.name := by
        have hentryFamilyName : entry.1.name = familyInfo.name := by
          have heq := congrArg ConstantInfo.name hentryValue
          dsimp only [ConstantInfo.name] at heq
          exact heq.symm
        exact hentryName.trans hentryFamilyName
      refine ⟨familyIdx, hfamilyNameEq, ⟨{
        familyIdx_lt := htargetIdx
        name := ?_
        lookup := by simpa [← hfamilyNameEq] using hfamily
        all := ?_
        levelParams := ?_
        numParams := ?_
        numIndices := ?_
        constructors := ?_
        isUnsafe := ?_
        constructor := ?_ }⟩⟩
      · calc
          familyInfo.name = indTypes[familyIdx].name := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types[familyIdx].name := Htype.header.name.symm
      · calc
          familyInfo.all = indTypes.toList.map (fun type => type.name) := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types.map (fun type => type.name) := by
            apply List.ext_getElem
            · simpa using
                Lean4Lean.VerifyInductive.TrInductDeclCore.types_length core
            · intro i hsource htarget
              simp only [List.getElem_map]
              exact (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt core
                i (by simpa using hsource) (by simpa using htarget)).header.name.symm
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, core.uvars]
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, core.nparams]
      · have hindex : stats.nindices[familyIdx]? =
            some decl.types[familyIdx].numIndices := by
          rw [← Array.getElem?_toList, H.statsWF.indices]
          simp [htargetIdx]
        have hstats : familyIdx < stats.nindices.size := by
          simpa [hindicesSize] using hfamilyIdx
        have hindexExact : stats.nindices[familyIdx] =
            decl.types[familyIdx].numIndices := by
          rw [Array.getElem?_eq_getElem hstats] at hindex
          exact Option.some.inj hindex
        calc
          familyInfo.numIndices = stats.nindices[familyIdx] := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types[familyIdx].numIndices := hindexExact
      · simpa [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos] using
          Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, core.isUnsafe]
      · intro ctorIdx htargetCtor
        have hsourceCtor : ctorIdx < indTypes[familyIdx].ctors.length := by
          have hbound := htargetCtor
          rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype] at hbound
          simpa using hbound
        have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
          ctorIdx hsourceCtor htargetCtor
        rcases D.installedConstructorCoherenceAt core Hchecked familyIdx hfamilyIdx
            ctorIdx hsourceCtor with
          ⟨installedInfo, hi, hinstalledName, hinstalledCtors,
            hinstalledLookup, ⟨C⟩⟩
        have hsourceName : familyName = indTypes[familyIdx].name := by
          calc
            familyName = familyInfo.name := hfamilyNameEq
            _ = indTypes[familyIdx].name := by
              simp [hfamilyInfoExact, infos,
                AddInductive.inductiveTypeInfos]
        have hsameLookup : outEnv.find? familyName =
            some (.inductInfo installedInfo) := by
          simpa [hinstalledName, hsourceName] using hinstalledLookup
        have hinstalledEq : installedInfo = familyInfo := by
          rw [hfamilyEnv] at hsameLookup
          cases Option.some.inj hsameLookup
          rfl
        subst installedInfo
        have hctorLookup : outEnv.constants.find? familyInfo.ctors[ctorIdx] =
            some (.ctorInfo C.info) := by
          have hlookup := C.lookup
          rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hlookup
          exact hlookup
        let sourceFamily := indTypes[familyIdx]
        let sourceCtor := sourceFamily.ctors[ctorIdx]
        let ctorInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
          sourceFamily ctorIdx sourceCtor
        rcases D.sourceAligned.findAt
            (owner := sourceFamily) (List.getElem_mem hfamilyIdx)
            ctorIdx (by simpa [sourceFamily] using hsourceCtor) with
          ⟨ctorValue, hctorEntry⟩
        have hctorLookupExact :
            outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
          D.installed.findEntry H.context.checking.tr.map_wf hctorEntry
        have hctorNameExact :
            familyInfo.ctors[ctorIdx] = ctorInfo.name := by
          simp [ctorInfo, sourceCtor, sourceFamily, hinstalledCtors,
            AddInductive.constructorInfo]
        have hctorLookupExact' :
            outEnv.constants.find? familyInfo.ctors[ctorIdx] =
              some (.ctorInfo ctorInfo) := by
          have hlookup := hctorLookupExact
          rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hlookup
          simpa [hctorNameExact] using hlookup
        have hctorInfoExact : C.info = ctorInfo := by
          have heq : (ConstantInfo.ctorInfo C.info) = .ctorInfo ctorInfo := by
            exact Option.some.inj (hctorLookup.symm.trans hctorLookupExact')
          exact ConstantInfo.ctorInfo.inj heq
        exact ⟨{
          familyIdx_lt := htargetIdx
          ctorIdx_lt := htargetCtor
          familyInfo_ctorIdx_lt := hi
          info := C.info
          name := by
            calc
              familyInfo.ctors[ctorIdx] =
                  indTypes[familyIdx].ctors[ctorIdx].name := by
                simp [hinstalledCtors]
              _ = decl.types[familyIdx].ctors[ctorIdx].name :=
                Hctor.name.symm
          lookup := hctorLookup
          induct := by simpa [hfamilyNameEq] using C.induct
          cidx := C.cidx
          numParams := by
            calc
              C.info.numParams = familyInfo.numParams := C.numParams
              _ = decl.nparams := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, core.nparams]
          numFields := by
            rw [hctorInfoExact]
            calc
              ctorInfo.numFields =
                  AddInductive.constructorArity sourceCtor.type -
                    stats.params.size :=
                AddInductive.constructorInfo_numFields stats c.lparams
                  isUnsafe sourceFamily ctorIdx sourceCtor
              _ = AddInductive.constructorArity ctorInfo.type -
                    decl.nparams := by
                rw [hparamsSize]
                rfl
          numFields_forallArity := by
            rw [hctorInfoExact]
            rcases Hchecked.parameterPrefixes.spines familyIdx hfamilyIdx ctorIdx
              hsourceCtor with ⟨k, hspine⟩
            calc
              ctorInfo.numFields =
                  AddInductive.constructorArity sourceCtor.type -
                    stats.params.size :=
                AddInductive.constructorInfo_numFields stats c.lparams
                  isUnsafe sourceFamily ctorIdx sourceCtor
              _ = k - decl.nparams := by
                rw [hspine.constructorArity, hparamsSize]
              _ = (decl.types[familyIdx].ctors[ctorIdx]).type.forallArity -
                    decl.nparams := by
                rw [checkPositivityStep.TrExprS.forallArity_of_spine hspine
                  Hctor.type]
          levelParamsExact := C.levelParams
          levelParams := by
            calc
              C.info.levelParams.length = familyInfo.levelParams.length :=
                congrArg List.length C.levelParams
              _ = decl.uvars := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, core.uvars]
          isUnsafe := by
            calc
              C.info.isUnsafe = familyInfo.isUnsafe := C.isUnsafe
              _ = decl.isUnsafe := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, core.isUnsafe] }⟩
  · rcases hctorOrigin with ⟨entry, hentry, _hname, hvalue⟩
    exact False.elim (D.nonInductive entry hentry familyInfo
      hvalue.symm)

/-- Header and constructor installation preserves the persistent invariant
for base families and supplies it positionally for every newly declared
family.  The fact for a new family is built positionally, not by matching
names; names only identify the unique kernel lookup after installation. -/
theorem ConstructorEnvironment.constructorParameterAlignment
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (D : ConstructorEnvironment H outEnv)
    (core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
      isUnsafe decl H.context.venv D.venvCtors)
    (Hchecked : CheckedConstructors sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams H.statsWF.parameterScope classes)
    (Hsource : ConstructorParameterAlignment
      safety c.env sourceEnv) :
    ConstructorParameterAlignment
      safety outEnv D.venvCtors := by
  intro familyName familyInfo hfamily hvisible ctorIdx hctor
  rcases D.installed.entryOrigin H.context.checking.tr.map_wf
      hfamily with hheader | hctorOrigin
  · rcases H.installed.entryOrigin H.sourceContext.checking.tr.map_wf
        hheader with hold | hnew
    · rcases Hsource familyName familyInfo hold hvisible ctorIdx hctor with ⟨C⟩
      have hctorHeader := H.installed.preservesSourceFind
        H.sourceContext.checking.tr.map_wf C.lookup
      have hctorFinal := D.installed.preservesSourceFind
        H.context.checking.tr.map_wf hctorHeader
      exact ⟨C.rebaseKernel hctorFinal
        (H.installed.le.trans D.installed.le)⟩
    · rcases hnew with ⟨entry, hentry, hentryName, hentryValue⟩
      rcases H.sourceAligned with ⟨numNested, Haligned⟩
      rcases Haligned.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
      have hinfoEq : familyInfo = info := by
        have heq : ConstantInfo.inductInfo familyInfo = .inductInfo info :=
          hentryValue.trans hentryInfo
        cases heq
        rfl
      subst info
      rcases List.mem_iff_getElem.mp hinfo with
        ⟨familyIdx, hfamilyInfo, hfamilyInfoEq⟩
      let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
        numNested isUnsafe c.lparams
      have hindicesSize : stats.nindices.size = indTypes.size := by
        calc
          stats.nindices.size = decl.types.length := by
            rw [Array.size_eq_length_toList, H.statsWF.indices,
              List.length_map]
          _ = indTypes.toList.length :=
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              core).symm
          _ = indTypes.size := by simp
      have hinfosSize : infos.size = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      have hfamilyIdx : familyIdx < indTypes.size := by
        have : familyIdx < infos.toList.length := by
          simpa [infos] using hfamilyInfo
        simpa [hinfosSize] using this
      have hfamilyInfoExact : familyInfo = infos[familyIdx] := by
        rw [← hfamilyInfoEq]
        exact Array.getElem_toList (by simpa [infos] using hfamilyInfo)
      have hsourceCtor : ctorIdx < indTypes[familyIdx].ctors.length := by
        simpa [hfamilyInfoExact, infos, AddInductive.inductiveTypeInfos]
          using hctor
      rcases D.installedConstructorCoherenceAt core Hchecked familyIdx hfamilyIdx
          ctorIdx hsourceCtor with
        ⟨installedInfo, hi, hinstalledName, hinstalledCtors,
          hinstalledLookup, ⟨C⟩⟩
      have hentryFamilyName : entry.1.name = familyInfo.name := by
        have heq := congrArg ConstantInfo.name hentryValue
        dsimp only [ConstantInfo.name] at heq
        exact heq.symm
      have hsourceName : familyName = indTypes[familyIdx].name := by
        calc
          familyName = entry.1.name := hentryName
          _ = familyInfo.name := hentryFamilyName
          _ = indTypes[familyIdx].name := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
      have hfamilyNameEq : familyName = familyInfo.name := by
        exact hentryName.trans hentryFamilyName
      have hsameLookup : outEnv.find? familyName =
          some (.inductInfo installedInfo) := by
        simpa [hinstalledName, hsourceName] using hinstalledLookup
      have hinstalledEq : installedInfo = familyInfo := by
        rw [hfamily] at hsameLookup
        cases Option.some.inj hsameLookup
        rfl
      subst installedInfo
      rw [hfamilyNameEq]
      exact ⟨by simpa only [Subsingleton.elim hi hctor] using C⟩
  · rcases hctorOrigin with ⟨entry, hentry, _hname, hvalue⟩
    exact False.elim (D.nonInductive entry hentry familyInfo
      hvalue.symm)

/-- The checked formation of a declaration whose headers and constructors are checked and
whose constructors are declared. -/
noncomputable def HeaderEnvironment.toCheckedFormation
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv)
    (Hchecked : CheckedConstructors sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams H.statsWF.parameterScope classes)
    (venvCtors : VEnv)
    (core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
      H.context.venv venvCtors) :
    CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes where
  headerVEnv := H.context.venv
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceStatsWF := H.sourceStatsWF
  headerMLCtx := H.context.mlctx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.statsWF.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  statsWF := H.statsWF
  checkedParams := H.headerParams
  checkedParameterScope := rfl
  classes := classes
  constructorTails := Hchecked.constructorTails
  ctorVEnv := venvCtors
  formation := H.formation Hchecked
  core := core

theorem AddInductive.declareConstructors.WF
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (Hchecked : CheckedConstructors sourceEnv decl H.context.venv
      H.headers.params stats indTypes c.lparams H.statsWF.parameterScope classes)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (htele : SourceCtorsCertified H.context.venv c.lparams indTypes.toList) :
    (AddInductive.declareConstructors stats indTypes isUnsafe
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : RecursorCheckingEnvironment H outEnv, True := by
  let mkInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
  have Htranslated := Hchecked.checked.translated H.translation
  have Hfold := AddConstants.ofConstructorTypes
    (allowPrimitive := c.allowPrimitive) mkInfo H.context.checking.tr
    Htranslated VEnv.LE.rfl
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by
      intro owner i ctor
      simpa [mkInfo, AddInductive.constructorInfo] using hvisible)
    hnprim
  rw [AddInductive.declareConstructors, ← Array.foldlM_toList]
  change (indTypes.toList.foldlM (init := headerEnv) fun
      (env : Environment) (owner : InductiveType) => do
    let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
        (state : Nat × Environment) (ctor : Constructor) => do
      let (cidx, env) := state
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add (.ctorInfo (mkInfo owner cidx ctor)))
    pure env).WF _
  exact Hfold.mono fun outEnv Hout => by
    rcases Hout with
      ⟨venvCtors, entries, hvalues, Hinstalled, Haligned, hproduction,
        hnind⟩
    have hctorsAdded : H.context.venv.addConstVals decl.constructorConstants =
        some venvCtors := by
      simp only [VInductDecl.constructorConstants]
      rw [← hvalues]
      exact Hinstalled.abstract
    let Htranslation : TrInductDeclConstructors H.context.venv c.lparams
        indTypes.toList decl venvCtors := {
      ctorsAdded := hctorsAdded
      types := Htranslated }
    let D : ConstructorEnvironment H outEnv := {
      venvCtors := venvCtors
      entries := entries
      values := by simpa [VInductDecl.constructorConstants] using hvalues
      installed := Hinstalled
      sourceAligned := by simpa [mkInfo] using Haligned
      infos := hproduction
      nonInductive := hnind
      translation := Htranslation }
    have core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
        isUnsafe decl H.context.venv venvCtors :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.ofPhases H.translation
        Htranslation
    have hsourceWF : sourceEnv.WF := by
      rw [← H.sourceContextVEnv]
      exact H.sourceContext.checking.tr.wf
    have hvalidCore : CheckingEnv.ValidCore c.safety outEnv venvCtors :=
      Hinstalled.validCore H.context.checking.toValidCore
    have hparams : decl.SourceParameterWF sourceEnv :=
      (H.formation Hchecked).formationWF.sourceParameterWF
    have hindicesSize : stats.nindices.size = indTypes.size := by
      calc
        stats.nindices.size = decl.types.length := by
          rw [Array.size_eq_length_toList, H.statsWF.indices,
            List.length_map]
        _ = indTypes.toList.length :=
          (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length core).symm
        _ = indTypes.size := by simp
    have hheaderWF := H.context.checking.tr.map_wf
    have hsourceMapWF := H.sourceContext.checking.tr.map_wf
    have howners : ConstructorOwnersPresent outEnv := by
      apply Hinstalled.constructorOwnersPresent hheaderWF
        H.context.checking.constructorOwners
      intro entry hentry info hinfo
      rcases Haligned.ownerOfEntry hentry with
        ⟨owner, howner, installedInfo, hentryInfo, hownerName, hmem, hunsafe⟩
      have hinfoEq : info = installedInfo := by
        rw [hentryInfo] at hinfo
        exact (ConstantInfo.ctorInfo.inj hinfo).symm
      subst info
      rcases H.sourceAligned with ⟨numNested, Hheaders⟩
      rcases inductiveTypeInfos_owner stats nparams indTypes numNested isUnsafe
          c.lparams hindicesSize howner with
        ⟨ownerInfo, hownerInfo, hname, hctors, hownerUnsafe⟩
      rcases Hheaders.findInfo hownerInfo with ⟨value, hheaderEntry⟩
      refine ⟨ownerInfo, ?_, by rw [hctors]; exact hmem, hunsafe.trans hownerUnsafe.symm⟩
      rw [hownerName, ← hname]
      exact Hinstalled.preservesSourceFind hheaderWF
        (H.installed.findEntry hsourceMapWF hheaderEntry)
    have hpreserves : ∀ {name ci}, c.env.constants.find? name = some ci →
        outEnv.constants.find? name = some ci := by
      intro name ci hfind
      have hfind' : c.env.find? name = some ci := by
        rw [Lean.Kernel.Environment.find?, hsourceMapWF.find?'_eq_find?]
        exact hfind
      have hout := Hinstalled.preservesSourceFind hheaderWF
        (H.installed.preservesSourceFind hsourceMapWF hfind')
      rwa [Lean.Kernel.Environment.find?,
        (Hinstalled.targetMapWF hheaderWF).find?'_eq_find?] at hout
    have hreflect : ∀ {name info},
        outEnv.constants.find? name = some (.ctorInfo info) →
        c.env.constants.find? name = some (.ctorInfo info) ∨
          c.env.constants.find? info.induct = none := by
      intro name info hfind
      have hfind' : outEnv.find? name = some (.ctorInfo info) := by
        rw [Lean.Kernel.Environment.find?,
          (Hinstalled.targetMapWF hheaderWF).find?'_eq_find?]
        exact hfind
      rcases Hinstalled.entryOrigin hheaderWF hfind' with hheader | hnew
      · rcases H.installed.entryOrigin hsourceMapWF hheader with hold | hheaderEntry
        · left
          rwa [Lean.Kernel.Environment.find?, hsourceMapWF.find?'_eq_find?] at hold
        · rcases hheaderEntry with ⟨entry, hentry, _, hvalue⟩
          rcases H.sourceAligned with ⟨numNested, Hheaders⟩
          rcases Hheaders.originInfo hentry with ⟨familyInfo, _, hentryInfo⟩
          rw [hentryInfo] at hvalue
          cases hvalue
      · rcases hnew with ⟨entry, hentry, _, hvalue⟩
        rcases Haligned.ownerOfEntry hentry with
          ⟨owner, howner, installedInfo, hentryInfo, hownerName, -⟩
        have hinfoEq : info = installedInfo := by
          rw [hentryInfo] at hvalue
          exact ConstantInfo.ctorInfo.inj hvalue
        subst info
        right
        rcases H.sourceAligned with ⟨numNested, Hheaders⟩
        rcases inductiveTypeInfos_owner stats nparams indTypes numNested
            isUnsafe c.lparams hindicesSize howner with
          ⟨ownerInfo, hownerInfo, hname, -⟩
        rcases Hheaders.findInfo hownerInfo with ⟨value, hheaderEntry⟩
        have hfresh := H.installed.entryFresh hsourceMapWF hheaderEntry
        rw [hownerName, ← hname]
        rwa [Lean.Kernel.Environment.find?, hsourceMapWF.find?'_eq_find?]
          at hfresh
    have htypeUvars : ∀ type ∈ decl.types, type.uvars = decl.uvars := by
      intro type htype
      rcases List.mem_iff_getElem.mp htype with ⟨i, hi, rfl⟩
      have hsource : i < indTypes.toList.length := by
        rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length core]
        exact hi
      exact (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt core i hsource
        hi).header.uvars.trans core.uvars.symm
    have hsourceRecursors : RecursorEnvCoherent c.safety c.env.constants sourceEnv := by
      rw [← H.sourceContextVEnv]
      exact H.sourceContext.checking.recursors
    have hheaderRecursors := H.installed.recursorEnvCoherent hsourceMapWF (by
      intro entry hentry rec heq
      rcases H.sourceAligned with ⟨numNested, Hheaders⟩
      rcases Hheaders.originInfo hentry with ⟨_, _, hinfo⟩
      rw [hinfo] at heq
      cases heq) hsourceRecursors
    have hctorRecursors := Hinstalled.recursorEnvCoherent hheaderWF (by
      intro entry hentry rec heq
      rcases Haligned.ownerOfEntry hentry with ⟨_, _, _, hinfo, _⟩
      rw [hinfo] at heq
      cases heq) hheaderRecursors
    have hrecursors : RecursorEnvCoherent c.safety outEnv.constants
        (venvCtors.addProjections decl.projectionEntries) :=
      hctorRecursors.addProjections _
    have hquot : outEnv.quotInit = true → QuotEnvCoherent outEnv.constants
        (venvCtors.addProjections decl.projectionEntries) := by
      have hsourceQuot : c.env.quotInit = true →
          QuotEnvCoherent c.env.constants sourceEnv := by
        rw [← H.sourceContextVEnv]
        exact H.sourceContext.checking.quot
      intro hq
      exact (Hinstalled.quotEnvCoherent hheaderWF hctorRecursors.heads
        (H.installed.quotEnvCoherent hsourceMapWF hheaderRecursors.heads hsourceQuot) hq).extend
        (fun h => h) VEnv.addProjections_le hrecursors.heads
    let B := H.toCheckedFormation Hchecked venvCtors core
    have helimsWF := B.caseEliminatorsWF
    obtain ⟨helimWF, hprojectedWF⟩ := helimsWF.recursorCheckingEnvWF hsourceWF core hparams
    have hle : venvCtors.addProjections decl.projectionEntries ≤
        (venvCtors.addEliminators B.caseEliminators).addProjections decl.projectionEntries :=
      VEnv.addProjections_mono VEnv.addEliminators_le
    have hrecursors' := hrecursors.extendSimple (fun h => h) (fun h _ => h) hle
      (fun _ h => by simpa using h)
    let venv' := (venvCtors.addEliminators B.caseEliminators).addProjections decl.projectionEntries
    have hcore' := (hvalidCore.addEliminators helimWF).addProjections hprojectedWF
    have houtWF : outEnv.constants.WF := hcore'.tr.map_wf
    have htelsAll : CtorTelescopes c.safety outEnv venv' :=
      (Hinstalled.ctorTelescopes H.context.checking.tr H.context.checking.ctorTelescopes
        (Haligned.ctorTelescopeSteps htele)).mono
        (VEnv.addEliminators_le.trans VEnv.addProjections_le)
    have hsourceLE : sourceEnv ≤ venv' :=
      (VEnv.addConstVals_le core.typesAdded).trans
        ((VEnv.addConstVals_le core.ctorsAdded).trans VEnv.addEliminators_addProjections_le)
    have hctorsLE : venvCtors ≤ venv' := VEnv.addEliminators_addProjections_le
    have hsourceBlocks : InstalledBlocks c.safety c.env sourceEnv .headers := by
      rw [← H.sourceContextVEnv]; exact H.sourceContext.checking.blocks
    have hblocks : InstalledBlocks c.safety outEnv venv' .headers := by
      refine hsourceBlocks.addCtorStage H.sourcePresent hsourceMapWF hcore'.tr
        (fun {n ci} h => by
          have h' := hpreserves (by rwa [Lean.Kernel.Environment.find?,
            hsourceMapWF.find?'_eq_find?] at h)
          rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?])
        hsourceLE (D.inductInfosFromDecl core Hchecked) ?_ ?_ howners [] ?_ (by simp) (by simp)
        (by simp) B.caseEliminators ?_ ?_ htelsAll
      · intro T hT
        have hmem : T.toVConstVal ∈ H.entries.map Prod.snd := by
          rw [H.values]; exact List.mem_map_of_mem hT
        obtain ⟨⟨ci, val⟩, he, hval⟩ := List.mem_map.mp hmem
        obtain ⟨numNested, Hheaders⟩ := H.sourceAligned
        obtain ⟨info, -, hci⟩ := Hheaders.originInfo he
        simp only at hci hval
        subst hci
        have hname : info.name = T.name := by
          obtain ⟨⟨_, htr⟩, -⟩ := H.installed.entryTr _ he
          have := htr.2
          simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at this
          rw [this, hval]
        refine ⟨info, ?_, ?_⟩
        · rw [← hname]
          exact Hinstalled.preservesSourceFind hheaderWF (H.installed.findEntry hsourceMapWF he)
        · rw [← hname]; exact H.installed.entryFresh hsourceMapWF he
      · have := VEnv.addConstVals_names_nodup core.typesAdded
        simpa [VInductDecl.typeConstants, Function.comp_def] using this
      · intro n r hf hnone
        exfalso
        rcases Hinstalled.entryOrigin hheaderWF hf with hheader | ⟨entry, hentry, -, hvalue⟩
        · rcases H.installed.entryOrigin hsourceMapWF hheader with hold | ⟨entry, hentry, -, hvalue⟩
          · rw [hold] at hnone; cases hnone
          · obtain ⟨numNested, Hheaders⟩ := H.sourceAligned
            obtain ⟨info, -, hinfo⟩ := Hheaders.originInfo hentry
            rw [hinfo] at hvalue; cases hvalue
        · obtain ⟨info, hinfo⟩ := D.infos entry hentry
          rw [hinfo] at hvalue; cases hvalue
      · exact {
          typeUvars := htypeUvars
          constructorUvars :=
            Lean4Lean.VerifyInductive.TrInductDeclCore.constructorUvars core
          family := fun i hi => (VEnv.addConstVals_le core.ctorsAdded).trans hctorsLE |>.constants
            (VEnv.addConstVals_get core.typesAdded
              (List.mem_map.mpr ⟨decl.types[i], List.getElem_mem hi, rfl⟩))
          ctor := fun i k hi hk => hctorsLE.constants
            (VEnv.addConstVals_get core.ctorsAdded (by
              simp only [VInductDecl.constructorConstants, List.mem_flatMap]
              exact ⟨_, List.getElem_mem hi, List.getElem_mem hk⟩))
          projections := fun e he =>
            VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩)
          eliminators := fun e he => VEnv.addProjections_le.eliminators
            (VEnv.addEliminators_iff.mpr (.inl he)) }
      · intro S info hp
        rcases VEnv.addProjections_iff.mp hp with ⟨e, he, rfl, rfl⟩ | hold
        · exact .inr he
        · left
          rw [VEnv.addEliminators_projections, VEnv.addConstVals_projections core.ctorsAdded,
            VEnv.addConstVals_projections core.typesAdded] at hold
          exact hold
    have hvalid : CheckingEnv.Valid c.safety outEnv venv' :=
      hcore'.toValid hblocks hrecursors'.heads
        (fun hq => (hquot hq).extend (fun h => h) hle hrecursors'.heads)
    exact ⟨{
      toConstructorEnvironment := D
      eliminators := B.caseEliminators
      eliminatorsWF := helimsWF
      eliminatorsCertified := B.caseEliminatorsCertified
      eliminatorsOwn := B.caseEliminatorsOwn
      eliminatorsBoundary := ⟨B, rfl, rfl, rfl⟩
      context := H.context.withEnv hvalid
        (Hinstalled.le.trans VEnv.addEliminators_addProjections_le)
      contextVEnv := rfl
      contextMLCtx := rfl }, trivial⟩

structure OrdinaryConstructorCheck
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv)
    (outEnv : Environment) where
  checked : CheckedConstructorCertificate sourceEnv decl H.context.venv
    H.headers.params
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  /-- The field classifications returned by the executable constructor check. -/
  classes : List (List (List Bool))
  constructorTails : ConstructorTails H.context.venv c.lparams
    H.statsWF.parameterScope stats decl indTypes classes
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes
  /-- The telescope certificates of the source constructor types, read off their checks. -/
  telescopes : SourceCtorsCertified H.context.venv c.lparams indTypes.toList
  declared : RecursorCheckingEnvironment H outEnv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl H.context.venv declared.venvCtors

theorem OrdinaryConstructorCheck.installedConstructorCoherenceAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : OrdinaryConstructorCheck H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ familyInfo : InductiveVal,
      ∃ hi : ctorIdx < familyInfo.ctors.length,
        familyInfo.name = indTypes[familyIdx].name ∧
        familyInfo.ctors = indTypes[familyIdx].ctors.map (fun ctor => ctor.name) ∧
        outEnv.find? familyInfo.name = some (.inductInfo familyInfo) ∧
        Nonempty (ConstructorParameterAlignmentAt
          outEnv R.declared.venvCtors familyInfo.name familyInfo ctorIdx hi) :=
  R.declared.toConstructorEnvironment.installedConstructorCoherenceAt
    R.core ⟨R.checked, R.parameterPrefixes, R.constructorTails⟩ familyIdx hfamily
    ctorIdx hctor

/-- The executable header and constructor folds identify every newly visible
inductive family of the kernel environment with one exact source declaration
position. -/
theorem OrdinaryConstructorCheck.inductInfosFromDecl
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : OrdinaryConstructorCheck H outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants decl :=
  R.declared.toConstructorEnvironment.inductInfosFromDecl R.core
    ⟨R.checked, R.parameterPrefixes, R.constructorTails⟩

theorem OrdinaryConstructorCheck.constructorParameterAlignment
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : OrdinaryConstructorCheck H outEnv)
    (Hsource : ConstructorParameterAlignment
      safety c.env sourceEnv) :
    ConstructorParameterAlignment
      safety outEnv R.declared.venvCtors :=
  R.declared.toConstructorEnvironment.constructorParameterAlignment R.core
    ⟨R.checked, R.parameterPrefixes, R.constructorTails⟩ Hsource

/-- The independent source environment used for header translation contains
none of the declaration's subsequently installed type or constructor names.
Successful installation supplies this fact; it is not a caller premise. -/
theorem TrInductDeclCore.headerBaseAvoidsSourceNames
    (H : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    {name : Name} {ci : VConstant}
    (hlookup : base.constants name = some ci) :
    name ∉ decl.sourceNames := by
  intro hname
  have Hadd : base.addConstVals
      (decl.typeConstants ++ decl.constructorConstants) = some envCtors :=
    VEnv.addConstVals_append H.typesAdded H.ctorsAdded
  have Hfresh := (VEnv.addConstVals_names_fresh Hadd).2
  unfold VInductDecl.sourceNames at hname
  simp only [List.mem_append] at hname
  rcases hname with htype | hctor
  · rcases List.mem_map.mp htype with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_left _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction
  · rcases List.mem_map.mp hctor with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_right _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction

/-- Re-establish source and formation well-formedness in a larger safety
model using the freshly replayed block installation.  Freshness-sensitive
`addConstVals` facts come from `Hblock`; all semantic typing and positivity facts
are transported monotonically from the source declaration judgment. -/
theorem VInductDecl.WF.rebaseOfBlock
    {decl : VInductDecl} {block : VInductBlock}
    {base largerBase : VEnv}
    (H : decl.WF base)
    (hbase : base ≤ largerBase)
    (Hblock : block.WF largerBase)
    (htypes : block.types = decl.typeConstants)
    (hctors : block.ctors = decl.constructorConstants) :
    decl.WF largerBase := by
  rcases Hblock with
    ⟨largerTypes, largerCtors, largerRecursors, hlargerTypes,
      hlargerCtors, hlargerRecursors, _htypesWF, _hctorsWF, _hrecsWF,
      _hrulesWF⟩
  have hlargerTypes' :
      largerBase.addConstVals decl.typeConstants = some largerTypes := by
    simpa [htypes] using hlargerTypes
  have hlargerCtors' :
      largerTypes.addConstVals decl.constructorConstants = some largerCtors := by
    simpa [hctors] using hlargerCtors
  rcases H.1 with
    ⟨hnonempty, hnames, htypeUvars, hctorUvars, sourceTypes,
      sourceCtors, hsourceTypes, hsourceCtors, hsourceTypesWF,
      hsourceCtorsWF⟩
  have hsourceTypesLE : sourceTypes ≤ largerTypes :=
    VEnv.addConstVals_mono hbase hsourceTypes hlargerTypes'
  have Hsource : decl.SourceWF largerBase :=
    ⟨hnonempty, hnames, htypeUvars, hctorUvars, largerTypes, largerCtors,
      hlargerTypes', hlargerCtors',
      fun type htype => (hsourceTypesWF type htype).mono hbase,
      fun ctor hctor => (hsourceCtorsWF ctor hctor).mono hsourceTypesLE⟩
  cases H.2 with
  | ordinary Hordinary =>
    rcases Hordinary with
      ⟨params, resultLevel, formationTypes, hformationTypes, htypeShapes,
        hctorShapes, hraw⟩
    have hformationTypesLE : formationTypes ≤ largerTypes :=
      VEnv.addConstVals_mono hbase hformationTypes hlargerTypes'
    have Hformation : decl.OrdinaryFormationWF largerBase :=
      ⟨params, resultLevel, largerTypes, hlargerTypes',
        fun type htype =>
          ⟨(htypeShapes type htype).1,
            (htypeShapes type htype).2.mono hbase⟩,
        fun type htype ctor hctor =>
          let Hctor := hctorShapes type htype ctor hctor
          ⟨Hctor.1.mono hformationTypesLE,
            Hctor.2.mono hformationTypesLE⟩, hraw⟩
    exact ⟨Hsource, .ordinary Hformation⟩
  | nested Hnested hformationBase =>
    exact ⟨Hsource, .nested Hnested (hformationBase.trans hbase)⟩

end VerifyInductive
end Lean4Lean
