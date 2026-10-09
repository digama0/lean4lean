import Lean4Lean.Verify.Inductive.Primitive.BatchInstallation
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation

/-! The formation installation (`FormationInstallation`: headers and constructors
added one constant at a time, or as an atomic primitive batch) and the
constructor check (`ConstructorCheck`), the input of the recursor phase, with
its ordinary construction (section 3.2 of the design notes).  The
primitive construction, `PrimitiveConstructorCheck.toConstructorCheck`, is in
`Primitive/ConstructorParams.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two sound installation histories that can reach the constructor
environment.  Ordinary declarations preserve validity after every
constant; primitive Bool/Nat declarations instead regain it only after the
whole header/constructor batch, which is why the primitive case records that
the batch is exactly the Bool or Nat batch and that its primitive
kernel names are safe and universe-monomorphic. -/
inductive FormationInstallation (safety : DefinitionSafety)
    (sourceEnv : Environment) (sourceVEnv : VEnv)
    (headerEntries : List (ConstantInfo × VConstVal))
    (headerEnv : Environment) (headerVEnv : VEnv)
    (ctorEntries : List (ConstantInfo × VConstVal))
    (ctorEnv : Environment) (ctorVEnv : VEnv) : Prop
  | ordinary :
    AddConstants safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ->
    AddConstants safety headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv ->
    FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv
  | primitive :
    AtomicAddConstants safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ->
    AtomicAddConstants safety headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv ->
    (headerEntries.map Prod.snd ++ ctorEntries.map Prod.snd = primitiveBoolConstants ∨
      headerEntries.map Prod.snd ++ ctorEntries.map Prod.snd = primitiveNatConstants) ->
    (∀ entry ∈ headerEntries ++ ctorEntries,
      Kernel.Environment.primitives.contains entry.1.name →
      entry.1.safety = .safe ∧ entry.1.levelParams = []) ->
    FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv

theorem FormationInstallation.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : FormationInstallation checkSafety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    FormationInstallation safety sourceEnv sourceVEnv headerEntries
      headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv := by
  cases H with
  | ordinary Hheaders Hctors =>
      exact .ordinary (Hheaders.sf_mono hsafety) (Hctors.sf_mono hsafety)
  | primitive Hheaders Hctors hconstants hsafe =>
      exact .primitive (Hheaders.sf_mono hsafety) (Hctors.sf_mono hsafety)
        hconstants hsafe

theorem FormationInstallation.headerLE
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    sourceVEnv <= headerVEnv := by
  cases H with
  | ordinary Htypes _ => exact Htypes.le
  | primitive Htypes _ _ _ => exact Htypes.le

theorem FormationInstallation.constructorLE
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    headerVEnv <= ctorVEnv := by
  cases H with
  | ordinary _ Hctors => exact Hctors.le
  | primitive _ Hctors _ _ => exact Hctors.le

theorem FormationInstallation.headerAbstract
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    sourceVEnv.addConstVals (headerEntries.map Prod.snd) = some headerVEnv := by
  cases H with
  | ordinary Htypes _ => exact Htypes.abstract
  | primitive Htypes _ _ _ => exact Htypes.abstract

theorem FormationInstallation.constructorAbstract
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    headerVEnv.addConstVals (ctorEntries.map Prod.snd) = some ctorVEnv := by
  cases H with
  | ordinary _ Hctors => exact Hctors.abstract
  | primitive _ Hctors _ _ => exact Hctors.abstract

/-- The complete formation endpoint always carries the local checker
invariant. In the primitive case the header-only prefix is used only as a
`CheckingEnv`, never as `CheckingEnv.Valid`. -/
theorem FormationInstallation.checking
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : CheckingEnv safety sourceEnv sourceVEnv) :
    CheckingEnv safety ctorEnv ctorVEnv := by
  cases H with
  | ordinary Htypes Hctors =>
      exact (AtomicAddConstants.ofAddConstants Hctors).checking
        ((AtomicAddConstants.ofAddConstants Htypes).checking Hsource)
  | primitive Htypes Hctors _ _ =>
      exact Hctors.checking (Htypes.checking Hsource)

theorem FormationInstallation.quotInit_eq
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    ctorEnv.quotInit = sourceEnv.quotInit := by
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.quotInit_eq.trans Htypes.quotInit_eq
  | primitive Htypes Hctors _ _ =>
      exact Hctors.quotInit_eq.trans Htypes.quotInit_eq

/-- Replay a complete formation prefix in a larger abstract environment.
Primitive headers and constructors are replayed with only `CheckingEnv`; the
primitive invariant is not asserted at the invalid header-only intermediate
state. -/
theorem FormationInstallation.rebase
    (H : FormationInstallation checkSafety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hvalid : CheckingEnv safety sourceEnv largerSource)
    (hsafety : safety <= checkSafety)
    (hsource : sourceVEnv <= largerSource) :
    exists largerHeader largerCtors,
      Nonempty (FormationInstallation safety sourceEnv largerSource
        headerEntries headerEnv largerHeader ctorEntries ctorEnv largerCtors) /\
      headerVEnv <= largerHeader /\ ctorVEnv <= largerCtors := by
  cases H with
  | ordinary Htypes Hctors =>
      rcases Htypes.rebase Hvalid hsafety hsource with
        ⟨largerHeader, Htypes', hheader⟩
      rcases Hctors.rebase (Htypes'.checking Hvalid) hsafety hheader with
        ⟨largerCtors, Hctors', hctors⟩
      exact ⟨largerHeader, largerCtors,
        ⟨.ordinary Htypes' Hctors'⟩, hheader, hctors⟩
  | primitive Htypes Hctors hconstants hsafe =>
      rcases Htypes.rebase Hvalid hsafety hsource with
        ⟨largerHeader, Htypes', hheader⟩
      rcases Hctors.rebase (Htypes'.checking Hvalid) hsafety hheader with
        ⟨largerCtors, Hctors', hctors⟩
      exact ⟨largerHeader, largerCtors,
        ⟨.primitive Htypes' Hctors' hconstants hsafe⟩, hheader, hctors⟩

theorem FormationInstallation.headerMapWF
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF) : headerEnv.constants.WF := by
  cases H with
  | ordinary Htypes _ => exact Htypes.targetMapWF hwf
  | primitive Htypes _ _ _ => exact Htypes.targetMapWF hwf

/-- A retained header entry is visible in the constructor environment
for both ordinary and atomic primitive histories. -/
theorem FormationInstallation.findHeaderEntry
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hentry : (info, value) ∈ headerEntries) :
    ctorEnv.find? info.name = some info := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary Htypes Hctors =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.findEntry hwf hentry)
  | primitive Htypes Hctors _ _ =>
      exact Hctors.preservesSourceFind hheaderWF
        (Htypes.findEntry hwf hentry)

/-- Every constant of the constructor environment is a base constant or an installed entry. -/
theorem FormationInstallation.entryOrigin
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : ctorEnv.find? name = some found) :
    sourceEnv.find? name = some found ∨ (∃ e ∈ headerEntries, found = e.1) ∨
      ∃ e ∈ ctorEntries, found = e.1 := by
  have hheaderWF := H.headerMapWF hwf
  cases H with
  | ordinary Htypes Hctors =>
    rcases (AtomicAddConstants.ofAddConstants Hctors).entryOrigin hheaderWF hfind with
      h | ⟨e, he, -, rfl⟩
    · rcases (AtomicAddConstants.ofAddConstants Htypes).entryOrigin hwf h with
        h | ⟨e, he, -, rfl⟩
      · exact .inl h
      · exact .inr (.inl ⟨e, he, rfl⟩)
    · exact .inr (.inr ⟨e, he, rfl⟩)
  | primitive Htypes Hctors _ _ =>
    rcases Hctors.entryOrigin hheaderWF hfind with h | ⟨e, he, -, rfl⟩
    · rcases Htypes.entryOrigin hwf h with h | ⟨e, he, -, rfl⟩
      · exact .inl h
      · exact .inr (.inl ⟨e, he, rfl⟩)
    · exact .inr (.inr ⟨e, he, rfl⟩)

/-- The header and constructor prefix as one atomic lockstep batch, for either
installation history. -/
theorem FormationInstallation.atomic
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv) :
    AtomicAddConstants safety sourceEnv sourceVEnv (headerEntries ++ ctorEntries)
      ctorEnv ctorVEnv := by
  cases H with
  | ordinary Htypes Hctors =>
      exact (AtomicAddConstants.ofAddConstants Htypes).append
        (AtomicAddConstants.ofAddConstants Hctors)
  | primitive Htypes Hctors _ _ => exact Htypes.append Hctors

/-- The formation prefix restores `HasPrimitives`: ordinary
installation never touches a primitive name, and a primitive batch is the
complete Bool or Nat constant batch. -/
theorem FormationInstallation.hasPrimitives
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : sourceVEnv.HasPrimitives) : ctorVEnv.HasPrimitives := by
  cases H with
  | ordinary Htypes Hctors => exact Hctors.hasPrimitives (Htypes.hasPrimitives Hsource)
  | primitive Htypes Hctors hconstants _ =>
      have hadd := VEnv.addConstVals_append Htypes.abstract Hctors.abstract
      rcases hconstants with hbool | hnat
      · rw [hbool] at hadd
        exact VEnv.HasPrimitives.addBoolConstants Hsource hadd
      · rw [hnat] at hadd
        exact VEnv.HasPrimitives.addNatConstants Hsource hadd

/-- The formation installation carries the local checking invariants,
for both installation histories. -/
theorem FormationInstallation.validCore
    (H : FormationInstallation safety sourceEnv sourceVEnv
      headerEntries headerEnv headerVEnv ctorEntries ctorEnv ctorVEnv)
    (Hsource : CheckingEnv.ValidCore safety sourceEnv sourceVEnv) :
    CheckingEnv.ValidCore safety ctorEnv ctorVEnv := by
  have hprimitives := H.hasPrimitives Hsource.hasPrimitives
  have hchecking := H.checking Hsource.tr
  cases H with
  | ordinary Htypes Hctors => exact Hctors.validCore (Htypes.validCore Hsource)
  | primitive Htypes Hctors _ hsafe =>
      exact ⟨hchecking, hprimitives,
        (Htypes.append Hctors).safePrimitives Hsource.tr.map_wf
          Hsource.safePrimitives hsafe⟩

theorem InductiveHeaderEntries.not_ctor (H : InductiveHeaderEntries infos entries) :
    ∀ e ∈ entries, ∀ info : ConstructorVal, e.1 ≠ .ctorInfo info := by
  induction H with
  | nil => simp
  | cons _ ih =>
    intro e he info heq
    rcases List.mem_cons.mp he with rfl | he
    · cases heq
    · exact ih e he info heq

theorem ConstructorListEntries.mem_info
    {mkInfo : Nat → Constructor → ConstructorVal}
    (H : ConstructorListEntries mkInfo start ctors entries) :
    ∀ e ∈ entries, ∃ ctor ∈ ctors, ∃ i, e.1 = .ctorInfo (mkInfo i ctor) := by
  induction H with
  | nil => simp
  | @cons start ctors tail ctor value _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨ctor, List.mem_cons_self, _, rfl⟩
    · obtain ⟨c, hc, i, h⟩ := ih e he
      exact ⟨c, List.mem_cons_of_mem _ hc, i, h⟩

theorem ConstructorTypeEntries.mem_info
    {mkInfo : InductiveType → Nat → Constructor → ConstructorVal}
    (H : ConstructorTypeEntries mkInfo owners entries) :
    ∀ e ∈ entries, ∃ owner ∈ owners, ∃ ctor ∈ owner.ctors, ∃ i,
      e.1 = .ctorInfo (mkInfo owner i ctor) := by
  induction H with
  | nil => simp
  | cons Hhead _ ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨c, hc, i, h⟩ := Hhead.mem_info e he
      exact ⟨_, List.mem_cons_self, c, hc, i, h⟩
    · obtain ⟨o, ho, c, hc, i, h⟩ := ih e he
      exact ⟨o, List.mem_cons_of_mem _ ho, c, hc, i, h⟩

/-- The constructor check, the input of the recursor phase.  It contains only
facts available after every constructor is installed and the checking context
over the recursor-checking environment is valid.  No field requires a valid
header-only context. -/
structure ConstructorCheck (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (nparams : Nat) (isUnsafe : Bool) (depth : Nat)
    (sourceEnv : VEnv) (indTypes : Array InductiveType)
    (ctorEnv : Environment) extends
    CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes where
  headerEnv : Environment
  headerEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  headerValues : headerEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  context : ContextWF { c with env := ctorEnv }
  contextMLCtx : context.mlctx = headerMLCtx
  checked : CheckedConstructorCertificate sourceEnv decl headerVEnv
    params
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes
  /-- The telescope certificates of the source constructor types. -/
  telescopes : SourceCtorsCertified headerVEnv c.lparams indTypes.toList
  headerSourceAligned : exists numNested,
    InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList headerEntries
  constructorSourceAligned : ConstructorTypeEntries
    (AddInductive.constructorInfo stats c.lparams isUnsafe)
    indTypes.toList constructorEntries
  constructorKernel : forall
      (entry : ConstantInfo × VConstVal), entry ∈ constructorEntries ->
    exists info : ConstructorVal, entry.1 = ConstantInfo.ctorInfo info
  constructorNonInductive : forall
      (entry : ConstantInfo × VConstVal), entry ∈ constructorEntries ->
    forall value : InductiveVal,
      entry.1 ≠ ConstantInfo.inductInfo value
  /-- The declaration's certified case eliminator, registered over the constructors. -/
  eliminators : List (Name × InductiveSignature.CaseSchema)
  eliminatorsWF : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock eliminators)
  eliminatorsCertified : decl.CaseEliminators sourceEnv (fun _ => False) eliminators
  eliminatorsOwn : decl.OwnCaseEliminators sourceEnv eliminators
  /-- The eliminators are those of a checked formation of the declaration. -/
  eliminatorsBoundary : ∃ B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv
    indTypes, eliminators = B.caseEliminators ∧ B.params = params ∧
      B.parameterScope = parameterScope
  /-- The retained checking context carries the declaration's case eliminator and projection
  entries: every checker run after the constructor stage happens in this environment. -/
  contextVEnv : context.venv =
    (ctorVEnv.addEliminators eliminators).addProjections decl.projectionEntries
  installation : FormationInstallation c.safety c.env sourceEnv
    headerEntries headerEnv headerVEnv constructorEntries ctorEnv ctorVEnv
  inductInfosFromDecl :
    InductInfosFromDecl c.env.constants ctorEnv.constants decl
  constructorParameterAlignment : forall {safety},
    ConstructorParameterAlignment safety c.env sourceEnv ->
    ConstructorParameterAlignment safety ctorEnv ctorVEnv

/-- Every constructor of the constructor environment is a base constant, or a new constructor of
the declaration, with the declaration's safety flag and a certified type. -/
theorem ConstructorCheck.ctorOrigin
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hfind : ctorEnv.find? name = some (.ctorInfo ci)) :
    c.env.find? name = some (.ctorInfo ci) ∨
      (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt R.headerVEnv ci) := by
  rcases R.installation.entryOrigin R.sourceContext.checking.tr.map_wf hfind with
    h | ⟨e, he, heq⟩ | ⟨e, he, heq⟩
  · exact .inl h
  · obtain ⟨_, hH⟩ := R.headerSourceAligned
    exact absurd heq.symm (hH.not_ctor e he ci)
  · obtain ⟨owner, howner, ctor, hctor, i, he1⟩ :=
      R.constructorSourceAligned.mem_info e he
    rw [he1] at heq
    cases heq
    refine .inr ⟨by simp [AddInductive.constructorInfo], ?_⟩
    obtain ⟨T, hT⟩ := R.telescopes owner howner ctor hctor
    exact .of_telTrN (T := T) (by simpa [AddInductive.constructorInfo] using hT)

/-- The abstract constructor environment with the declaration's case
eliminators and projection entries is well formed. -/
theorem ConstructorCheck.projectedWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ((R.ctorVEnv.addEliminators R.eliminators).addProjections decl.projectionEntries).WF := by
  rw [← R.contextVEnv]
  exact R.context.checking.tr.wf

/-- The abstract constructor environment with the declaration's case eliminators is
well formed. -/
theorem ConstructorCheck.casesWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    (R.ctorVEnv.addEliminators R.eliminators).WF := by
  have hsourceWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  exact R.eliminatorsWF.casesWF hsourceWF
    (Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF R.core hsourceWF)
    R.core.typesAdded R.core.ctorsAdded

theorem ConstructorCheck.ctorLE
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.ctorVEnv ≤ R.context.venv := by
  rw [R.contextVEnv]
  exact VEnv.addEliminators_addProjections_le

/-- The header and constructor installation preserves the constructor-owner
invariant.  New constructor metadata obtains its owner from the family-major
constructor installation, and that owner's header is found among the
installed headers. -/
theorem ConstructorCheck.constructorOwnersPresent
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hsource : ConstructorOwnersPresent c.env) :
    ConstructorOwnersPresent ctorEnv := by
  rcases R.headerSourceAligned with ⟨numNested, Hheaders⟩
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, R.statsWF.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  apply R.installation.atomic.constructorOwnersPresent
    R.sourceContext.checking.tr.map_wf hsource
  intro entry hentry info hinfo
  rcases List.mem_append.mp hentry with hheader | hctor
  · rcases Hheaders.originInfo hheader with ⟨familyInfo, _, heq⟩
    rw [heq] at hinfo
    cases hinfo
  · rcases R.constructorSourceAligned.ownerOfEntry hctor with
      ⟨owner, howner, installedInfo, hentryInfo, hownerName, hmem, hunsafe⟩
    have hinfoEq : info = installedInfo := by
      rw [hentryInfo] at hinfo
      exact ConstantInfo.ctorInfo.inj hinfo.symm
    subst info
    rcases inductiveTypeInfos_owner stats nparams indTypes numNested isUnsafe
        c.lparams hindicesSize howner with
      ⟨ownerInfo, hownerInfo, hname, hctors, hownerUnsafe⟩
    rcases Hheaders.findInfo hownerInfo with ⟨value, hentry⟩
    refine ⟨ownerInfo, ?_, by rw [hctors]; exact hmem, hunsafe.trans hownerUnsafe.symm⟩
    rw [hownerName, ← hname]
    exact R.installation.findHeaderEntry
      R.sourceContext.checking.tr.map_wf hentry

/-- Transport the retained checked headers to the valid constructor
environment, at the start of the recursor phase. -/
def ConstructorCheck.recursorHeaders
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    checkInductiveTypes.loopInd.HeaderStatsWF
      R.context.venv c.lparams R.context.mlctx.vlctx stats decl depth := by
  let M := R.statsWF.mono (R.installation.constructorLE.trans R.ctorLE)
  exact {
    headers := M.headers
    isNotZero := M.isNotZero
    commonLevel := M.commonLevel
    levels := M.levels
    levelParams := M.levelParams
    uvars := M.uvars
    consts := M.consts
    indices := M.indices
    params := by simpa only [R.contextMLCtx] using M.params
    paramFVars := M.paramFVars
    parameterScope := M.parameterScope
    normalizedSources := M.normalizedSources
    normalizedShapes := M.normalizedShapes
    ambientScope := M.ambientScope
    scopeDecomposition := by
      simpa only [R.contextMLCtx] using M.scopeDecomposition
    ambientLength := M.ambientLength
    cachedScope := M.cachedScope
    parameterEmbedding := by simpa only [R.contextMLCtx] using M.parameterEmbedding
    paramsContext := M.paramsContext
    suffixParams := M.suffixParams }

theorem ConstructorCheck.recursorHeaders_parameterScope
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.recursorHeaders.parameterScope = R.parameterScope := by
  simp [ConstructorCheck.recursorHeaders,
    checkInductiveTypes.loopInd.HeaderStatsWF.mono,
    R.checkedParameterScope]

/-- Embed the ordinary constructor check into `ConstructorCheck`, retaining
its header and constructor installations. -/
def OrdinaryConstructorCheck.toConstructorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : OrdinaryConstructorCheck H ctorEnv) :
    ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv
      indTypes ctorEnv where
  headerEnv := headerEnv
  headerVEnv := H.context.venv
  headerEntries := H.entries
  constructorEntries := R.declared.entries
  headerValues := H.values
  constructorValues := R.declared.values
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceStatsWF := H.sourceStatsWF
  context := R.declared.context
  headerMLCtx := H.context.mlctx
  contextMLCtx := R.declared.contextMLCtx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.statsWF.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  statsWF := H.statsWF
  checkedParams := H.headerParams
  checkedParameterScope := rfl
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  classes := R.classes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  telescopes := R.telescopes
  headerSourceAligned := H.sourceAligned
  constructorSourceAligned := R.declared.sourceAligned
  constructorKernel := R.declared.infos
  constructorNonInductive := R.declared.nonInductive
  ctorVEnv := R.declared.venvCtors
  eliminators := R.declared.eliminators
  eliminatorsWF := R.declared.eliminatorsWF
  eliminatorsCertified := R.declared.eliminatorsCertified
  eliminatorsOwn := R.declared.eliminatorsOwn
  eliminatorsBoundary := R.declared.eliminatorsBoundary
  contextVEnv := R.declared.contextVEnv
  installation := .ordinary H.installed R.declared.installed
  formation := R.formation
  core := R.core
  inductInfosFromDecl := R.inductInfosFromDecl
  constructorParameterAlignment := fun Hsource => R.constructorParameterAlignment Hsource

end VerifyInductive
end Lean4Lean
