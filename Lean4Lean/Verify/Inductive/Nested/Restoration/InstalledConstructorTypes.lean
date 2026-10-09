import Lean4Lean.Verify.Inductive.Nested.Install.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledFamilyLookups
import Lean4Lean.Verify.EquivManager

/-!
# Installed nested constructor types versus source constructor types

Nested installation stores `restoreNested loweredEnv loweredCtor.type`
(`Lean4Lean.restoreConstructorDecl`), while
`validateSourceConstructorTypes.run` checks the source type
`ctor.type`. This file relates the two for every successful nested run.

**Literal equality is false.** `ElimNestedInductive.findCachedAux?` reuses an
auxiliary family when the parameters of a nested occurrence are `==` to a
previously recorded one, and `==` on `Expr` is `Expr.eqv`, which ignores binder
names and binder annotations (`Expr.eqv_eq`, `Expr.eqv'` with
`strict := false`). Restoration rebuilds a cache hit from the parameters
recorded for the first occurrence. The source constructor

  `CE.T.mk : List ((a : Nat) → CE.T) → List ({b : Nat} → CE.T) → CE.T`

is accepted and installed with type

  `List ((a : Nat) → CE.T) → List ((a : Nat) → CE.T) → CE.T`

(`Lean4Lean.Tests.NestedConstructorRoundTrip` checks this; Lean's C++ kernel
installs the same type). The parameter telescope, the constructor's own field
binders, and the index arguments of nested occurrences are restored verbatim;
only binders inside the parameters of a cache-hit occurrence can change.

**What holds** is the strongest relation used by the cache: the installed type
is `Expr.eqv`-equal to the source type.

* `NestedRun.constructorTypeRoundTrip`: for a successful
  validated nested run,
  - `ConstructorsFromSources`: every constructor visible in the output
    environment is inherited unchanged from the input environment, or is the
    installation of a source constructor `source` (a member of some
    `type.ctors`, `type ∈ sourceTypes`) with the same name, universe
    parameters `lparams`, and `(info.type == source.type) = true`;
  - `ConstructorTypesInstalled`: every source constructor is visible in the
    output environment with the same relation.
* `NestedRun.installedConstructorSource`: the lookup-indexed
  form, additionally giving `EquivManager.RelevantEq info.type source.type`.

Consumers transport a source-type certificate along `==`: `TrExprS.eqv` does
this for translations, and any relation on `Expr` that ignores binder names and
binder annotations transports the same way. All other `ConstructorVal` fields
of the installed constant are those of the lowered constructor
(`ConstructorRestorationStep.newInfo_eq`, `ConstructorRestoration`); their
alignment with the source declaration (`numParams`, `numFields`, `induct`,
`cidx`) is `InductInfosFromDecl`
(`NestedRestorationFolds.inductInfosFromDecl`).

**Obtaining the hypotheses.** `E : NestedRun ...` is the
`validated` field produced by
`Environment.addInductiveAfterLowering.nestedValidatedRawSourceWF`;
`SourceSyntaxChecks sourceTypes` is supplied to the continuation of
`addInductiveDeclaration.checkedLoweringClosedWF` (from
`checkInductiveSources`); `ConstructorOwnersPresent sourceProdEnv` is
`VEnvs.WF.constructorOwners`.

The core per-constructor inverse is
`ConstructorRestorationInverse.restoredType_eqv_source`; the lemmas here
thread it through the executable restoration fold
(`LoweredRestoredConstructors`, `NestedRestorationFolds`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The relation between one installed restored constructor and the source
constructor it came from. -/
structure RestoredConstructorType (lparams : List Name)
    (source : Constructor) (info : ConstructorVal) : Prop where
  name : info.name = source.name
  levelParams : info.levelParams = lparams
  type_eqv : (info.type == source.type) = true

/-- The safety flag of a newly installed constructor: it is the declaration's flag, unless its
name is already taken in the base environment `baseEnv` (which freshness later excludes). -/
def RestoredConstructorSafety (baseEnv : Environment) (isUnsafe : Bool) (name : Name)
    (info : ConstructorVal) : Prop :=
  info.isUnsafe = isUnsafe ∨ ∃ ci, baseEnv.find? name = some ci

/-- Every constructor visible in `targetEnv` is inherited from `sourceEnv`, or
is the installed form of one of `sources`, carrying the declaration's safety flag relative to
`baseEnv`. -/
def ConstructorsFromSources (lparams : List Name) (baseEnv : Environment) (isUnsafe : Bool)
    (sources : List Constructor) (sourceEnv targetEnv : Environment) : Prop :=
  ∀ name info, targetEnv.find? name = some (.ctorInfo info) →
    sourceEnv.find? name = some (.ctorInfo info) ∨
      ∃ source ∈ sources, RestoredConstructorType lparams source info ∧
        RestoredConstructorSafety baseEnv isUnsafe name info

theorem ConstructorsFromSources.refl :
    ConstructorsFromSources lparams baseEnv isUnsafe sources env env :=
  fun _ _ hfind => .inl hfind

theorem ConstructorsFromSources.mono
    (H : ConstructorsFromSources lparams baseEnv isUnsafe sources sourceEnv targetEnv)
    (hsub : ∀ source ∈ sources, source ∈ sources') :
    ConstructorsFromSources lparams baseEnv isUnsafe sources' sourceEnv targetEnv := by
  intro name info hfind
  rcases H name info hfind with hold | ⟨source, hsource, horigin⟩
  · exact .inl hold
  · exact .inr ⟨source, hsub source hsource, horigin⟩

theorem ConstructorsFromSources.trans
    (H₁ : ConstructorsFromSources lparams baseEnv isUnsafe sources₁ env₁ env₂)
    (H₂ : ConstructorsFromSources lparams baseEnv isUnsafe sources₂ env₂ env₃) :
    ConstructorsFromSources lparams baseEnv isUnsafe (sources₁ ++ sources₂) env₁ env₃ := by
  intro name info hfind
  rcases H₂ name info hfind with hmid | ⟨source, hsource, horigin⟩
  · rcases H₁ name info hmid with hold | ⟨source, hsource, horigin⟩
    · exact .inl hold
    · exact .inr ⟨source, List.mem_append_left _ hsource, horigin⟩
  · exact .inr ⟨source, List.mem_append_right _ hsource, horigin⟩

/-- A checked addition of a non-constructor constant adds no constructor. -/
theorem ConstructorsFromSources.addNonConstructor
    {env : Environment} (hwf : env.constants.WF) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hci : ∀ info, ci ≠ .ctorInfo info) :
    ConstructorsFromSources lparams baseEnv isUnsafe [] env (env.add ci) := by
  intro name info hfind
  rcases Environment.find?_freshAdd_cases hwf ci hfresh hfind with
    ⟨_hname, hfound⟩ | hold
  · exact absurd hfound.symm (hci info)
  · exact .inl hold

/-- A checked addition of one constructor. -/
theorem ConstructorsFromSources.addConstructor
    {env : Environment} (hwf : env.constants.WF) (info : ConstructorVal)
    (hfresh : env.find? (ConstantInfo.ctorInfo info).name = none)
    (horigin : RestoredConstructorType lparams source info)
    (hsafety : RestoredConstructorSafety baseEnv isUnsafe info.name info) :
    ConstructorsFromSources lparams baseEnv isUnsafe [source] env
      (env.add (.ctorInfo info)) := by
  intro name found hfind
  rcases Environment.find?_freshAdd_cases hwf _ hfresh hfind with
    ⟨_hname, hfound⟩ | hold
  · cases hfound
    subst _hname
    exact .inr ⟨source, by simp, horigin, hsafety⟩
  · exact .inl hold

/-- Every constructor of `sources` is visible in `targetEnv` with the
restored-constructor relation to its source. -/
def ConstructorTypesInstalled (lparams : List Name)
    (sources : List Constructor) (targetEnv : Environment) : Prop :=
  ∀ source ∈ sources, ∃ info,
    targetEnv.find? source.name = some (.ctorInfo info) ∧
      RestoredConstructorType lparams source info

theorem ConstructorTypesInstalled.nil :
    ConstructorTypesInstalled lparams [] env := by
  intro source hsource
  simp at hsource

theorem ConstructorTypesInstalled.append
    (H₁ : ConstructorTypesInstalled lparams sources₁ env)
    (H₂ : ConstructorTypesInstalled lparams sources₂ env) :
    ConstructorTypesInstalled lparams (sources₁ ++ sources₂) env := by
  intro source hsource
  rcases List.mem_append.mp hsource with hsource | hsource
  · exact H₁ source hsource
  · exact H₂ source hsource

theorem ConstructorTypesInstalled.fresh
    (H : ConstructorTypesInstalled lparams sources env)
    (Hfresh : FreshExtension env entries env')
    (hwf : env.constants.WF) :
    ConstructorTypesInstalled lparams sources env' := by
  intro source hsource
  rcases H source hsource with ⟨info, hfind, horigin⟩
  exact ⟨info, Hfresh.preservesSourceFind hwf hfind, horigin⟩

/-- **Constructor-list round trip.** Along the lockstep alignment of
constructor lowering with the executable restoration fold, every installed
constructor is the restoration of its positionally corresponding source
constructor, with an `Expr.eqv`-equal type. -/
theorem LoweredRestoredConstructors.constructorsFromSources
    (H : LoweredRestoredConstructors result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (HsyntaxBVar : ∀ source ∈ sources, Closed source.type)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams)
    (hparamsSize : params.size = nparams)
    (hsourceWF : sourceProdEnv.constants.WF)
    (hlowered : ∀ name old, loweredEnv.find? name = some (.ctorInfo old) →
      old.isUnsafe = isUnsafe ∨ ∃ ci, baseEnv.find? name = some ci) :
    ConstructorsFromSources lparams baseEnv isUnsafe sources sourceProdEnv targetProdEnv := by
  induction H with
  | nil => exact .refl
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsyntax with
    | cons HsourceSyntax HtailSyntax =>
      rcases Hmapping.constructorRestoration_inverse hresultParams paramFvars
          hparams hnodup HsourceSyntax.closed (HsyntaxBVar source (by simp))
          hparamsSize loweredEnv (Hdisjoint source (by simp)) hresultNParams
          Hstep.restored.restoration htype with ⟨Hinverse⟩
      have horigin : RestoredConstructorType lparams source
          Hstep.restored.newInfo := {
        name := Hstep.restored.restoration.name.trans
          (hname.trans Hmapping.name)
        levelParams := Hstep.restored.restoration.levelParams.trans hlevels
        type_eqv := Hinverse.restoredType_eqv_source }
      let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
      have hfresh : sourceProdEnv.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middleProdEnv.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      have hsafe : RestoredConstructorSafety baseEnv isUnsafe Hstep.restored.newInfo.name
          Hstep.restored.newInfo := by
        have hn : Hstep.restored.newInfo.name = target.name := by
          rw [Hstep.restored.newInfo_eq]; exact hname
        have hu : Hstep.restored.newInfo.isUnsafe = Hstep.oldInfo.isUnsafe := by
          rw [Hstep.restored.newInfo_eq]
        rcases hlowered _ _ Hstep.lookup with h | h
        · exact .inl (hu.trans h)
        · rw [hn]; exact .inr h
      have Hhead : ConstructorsFromSources lparams baseEnv isUnsafe [source] sourceProdEnv
          middleProdEnv := by
        rw [hmiddle]
        exact .addConstructor hsourceWF _ hfresh horigin hsafe
      have Htail := ih HtailSyntax
        (fun tail htail => HsyntaxBVar tail (by simp [htail]))
        (fun tail htail => Hdisjoint tail (by simp [htail])) hmiddleWF
      exact Hhead.trans Htail

theorem LoweredRestoredConstructors.freshExtension
    (H : LoweredRestoredConstructors result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries, FreshExtension sourceProdEnv entries targetProdEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh : sourceProdEnv.find? ci.name = none :=
      find?_none_of_contains_false hsourceWF Hstep.restored.fresh
    have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middleProdEnv.constants.WF :=
      hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
    rcases ih hmiddleWF with ⟨entries, Htail⟩
    rw [hmiddle] at Htail
    exact ⟨ci :: entries, .cons hfresh Htail⟩

/-- Forward form of `LoweredRestoredConstructors.constructorsFromSources`:
every source constructor is installed. -/
theorem LoweredRestoredConstructors.constructorTypesInstalled
    (H : LoweredRestoredConstructors result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (HsyntaxBVar : ∀ source ∈ sources, Closed source.type)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams)
    (hparamsSize : params.size = nparams)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ConstructorTypesInstalled lparams sources targetProdEnv := by
  induction H with
  | nil => exact .nil
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsyntax with
    | cons HsourceSyntax HtailSyntax =>
      rcases Hmapping.constructorRestoration_inverse hresultParams paramFvars
          hparams hnodup HsourceSyntax.closed (HsyntaxBVar source (by simp))
          hparamsSize loweredEnv (Hdisjoint source (by simp)) hresultNParams
          Hstep.restored.restoration htype with ⟨Hinverse⟩
      have horigin : RestoredConstructorType lparams source
          Hstep.restored.newInfo := {
        name := Hstep.restored.restoration.name.trans
          (hname.trans Hmapping.name)
        levelParams := Hstep.restored.restoration.levelParams.trans hlevels
        type_eqv := Hinverse.restoredType_eqv_source }
      let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
      have hfresh : sourceProdEnv.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middleProdEnv = sourceProdEnv.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middleProdEnv.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      have hheadFind : middleProdEnv.find? source.name = some ci := by
        rw [hmiddle, ← horigin.name]
        exact Environment.find?_freshAdd_self hsourceWF ci hfresh
      rcases Hrest.freshExtension hmiddleWF with ⟨_entries, HtailFresh⟩
      have Hhead : ConstructorTypesInstalled lparams [source]
          middleProdEnv := by
        intro source' hsource'
        simp only [List.mem_singleton] at hsource'
        subst source'
        exact ⟨Hstep.restored.newInfo, hheadFind, horigin⟩
      have Htail := ih HtailSyntax
        (fun tail htail => HsyntaxBVar tail (by simp [htail]))
        (fun tail htail => Hdisjoint tail (by simp [htail])) hmiddleWF
      exact (Hhead.fresh HtailFresh hmiddleWF).append Htail

/-- Every constructor of the kernel environment after a recursor check is already
present in the base environment, or a new constructor of the declaration with its
safety flag. -/
theorem RecursorCheck.ctorIsUnsafe
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType} {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv) :
    ∀ name old, outEnv.find? name = some (.ctorInfo old) →
      old.isUnsafe = isUnsafe ∨ ∃ ci, c.env.find? name = some ci := by
  intro name old hfind
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.toConstructorCheck.context.checking.tr.map_wf
  have h := (AtomicAddConstants.ofAddConstants H.installed).ctors_of_noCtor hwf
    (fun e he info => H.generated.nonConstructor e.1 e.2 (by simpa using he) info) hfind
  rw [H.localExtends.env_eq] at h
  rcases R.toConstructorCheck.ctorOrigin h with h | ⟨h, -⟩
  · exact .inr ⟨_, h⟩
  · exact .inl h

/-- One restored source family: its header and source recursor add no
constructor, and its constructor fold follows the lockstep alignment with lowering. -/
theorem NestedLoweringOutputClosed.familyConstructorsFromSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (HsourceBVar : ∀ source ∈ sourceTypes[familyIdx].ctors,
      Closed source.type)
    (Hdisjoint : ∀ source ∈ sourceTypes[familyIdx].ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget)
    (hwf : stepSource.constants.WF) :
    ConstructorsFromSources c.lparams c.env isUnsafe sourceTypes[familyIdx].ctors stepSource
      stepTarget := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, _stepState, _target, _loweredState, hparams, hnodup, _hsize,
      _htarget, _hctorNames, _Hmappings, _Htrace, Haligned⟩
  let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
  have hheaderEnv : Hstep.restored.headerEnv = stepSource.add header :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderFresh : stepSource.find? header.name = none :=
    find?_none_of_contains_false hwf Hstep.restored.header.fresh
  have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hwf hheaderFresh
  have Hheader : ConstructorsFromSources c.lparams c.env isUnsafe [] stepSource
      Hstep.restored.headerEnv := by
    rw [hheaderEnv]
    exact .addNonConstructor hwf header hheaderFresh (by
      intro info h
      simp [header] at h)
  have Hctors : ConstructorsFromSources c.lparams c.env isUnsafe sourceTypes[familyIdx].ctors
      Hstep.restored.headerEnv Hstep.restored.constructorEnv :=
    Haligned.constructorsFromSources
      (Hsources.getElem familyIdx hfamily).constructors HsourceBVar Hdisjoint
      rfl fvars hparams hnodup H.toResult.resultNParams
      (H.resultParamsSize.trans H.toResult.resultNParams) hheaderWF
      Hprod.ctorIsUnsafe
  obtain ⟨_entries, HctorFresh⟩ :=
    Hstep.restored.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
    HctorFresh.targetWF hheaderWF
  let recursor : ConstantInfo := .recInfo Hstep.restored.recursor.restored.newInfo
  have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hconstructorWF
      Hstep.restored.recursor.restored.fresh
  have htarget : stepTarget = Hstep.restored.constructorEnv.add recursor :=
    congrArg Prod.snd Hstep.restored.recursor.restored.output
  have Hrec : ConstructorsFromSources c.lparams c.env isUnsafe []
      Hstep.restored.constructorEnv stepTarget := by
    have Hadd : ConstructorsFromSources c.lparams c.env isUnsafe []
        Hstep.restored.constructorEnv
        (Hstep.restored.constructorEnv.add recursor) :=
      .addNonConstructor hconstructorWF recursor hrecFresh (by
        intro info h
        simp [recursor] at h)
    rwa [← htarget] at Hadd
  exact ((Hheader.trans Hctors).trans Hrec).mono (by simp)

/-- The auxiliary-recursor suffix of nested restoration adds no constructor. -/
theorem FoldSteps.recursorConstructorsFromSources
    (H : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ConstructorsFromSources lparams baseEnv isUnsafe [] sourceEnv targetEnv := by
  induction H with
  | nil => exact .refl
  | cons Hstep Htail ih =>
    rename_i _head source middle _tail _target
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh : source.find? ci.name = none :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have hmiddle : middle = source.add ci :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middle.constants.WF :=
      hmiddle.symm ▸ constantsWF_add_checked hwf hfresh
    have Hhead : ConstructorsFromSources lparams baseEnv isUnsafe [] source middle := by
      rw [hmiddle]
      exact .addNonConstructor hwf ci hfresh (by
        intro info h
        simp [ci] at h)
    exact (Hhead.trans (ih hmiddleWF)).mono (by simp)

/-- The fold over the source families. -/
theorem NestedLoweringOutputClosed.familiesConstructorsFromSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourceBVar : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      Closed source.type)
    (Hdisjoint : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      remaining sourceEnv targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hwf : sourceEnv.constants.WF) :
    ConstructorsFromSources c.lparams c.env isUnsafe (sourceTypes.flatMap (·.ctors))
      sourceEnv targetEnv := by
  induction Htrace generalizing processed with
  | nil => exact .refl
  | @cons head stepSource middle tail target Hstep Htail ih =>
    let familyIdx := processed.length
    have hfamily : familyIdx < sourceTypes.length := by
      simp [familyIdx, hsplit]
    have hfamilyEq : sourceTypes[familyIdx] = head := by
      simp [familyIdx, hsplit]
    have Hstep' : RestoredInductiveStep result loweredEnv auxRec allIndNames
        sourceTypes[familyIdx] stepSource middle := by
      simpa [hfamilyEq] using Hstep
    have hmem : sourceTypes[familyIdx] ∈ sourceTypes :=
      List.getElem_mem hfamily
    have Hhead := H.familyConstructorsFromSources Hc Hprod hempty Hsources
      familyIdx hfamily (HsourceBVar _ hmem) (Hdisjoint _ hmem) Hstep' hwf
    obtain ⟨_entries, Hfresh⟩ := Hstep'.restored.freshExtension hwf
    have hmiddleWF : middle.constants.WF := Hfresh.targetWF hwf
    have Hrest := ih (processed ++ [head])
      (by simpa [List.append_assoc] using hsplit) hmiddleWF
    refine (Hhead.trans Hrest).mono ?_
    intro source hsource
    rcases List.mem_append.mp hsource with hsource | hsource
    · exact List.mem_flatMap.mpr ⟨_, hmem, hsource⟩
    · exact hsource

/-- The complete executable restoration fold of a nested block. -/
theorem NestedLoweringOutputClosed.restorationConstructorsFromSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourceBVar : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      Closed source.type)
    (Hdisjoint : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (Hrestored : NestedRestorationFolds result loweredEnv sourceEnv
      auxRec allIndNames sourceTypes auxRecNames out)
    (hwf : sourceEnv.constants.WF) :
    ConstructorsFromSources c.lparams c.env isUnsafe (sourceTypes.flatMap (·.ctors))
      sourceEnv out.2 := by
  have Hprimary := H.familiesConstructorsFromSources Hc Hprod hempty Hsources
    HsourceBVar Hdisjoint Hrestored.inductives [] (by simp) hwf
  obtain ⟨_entries, Hfresh⟩ := Hrestored.inductives.inductiveFreshExtension hwf
  have Haux := Hrestored.auxiliaries.recursorConstructorsFromSources
    (lparams := c.lparams) (baseEnv := c.env) (isUnsafe := isUnsafe) (Hfresh.targetWF hwf)
  exact (Hprimary.trans Haux).mono (by simp)

private theorem SourceSyntaxChecks.inductiveSyntaxOfMem
    (H : SourceSyntaxChecks types) (hmem : type ∈ types) :
    SourceInductiveSyntax type := by
  induction H with
  | nil => simp at hmem
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact Hhead
    · exact ih htail

/-- Forward form of `familyConstructorsFromSources`. -/
theorem NestedLoweringOutputClosed.familyConstructorTypesInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (HsourceBVar : ∀ source ∈ sourceTypes[familyIdx].ctors,
      Closed source.type)
    (Hdisjoint : ∀ source ∈ sourceTypes[familyIdx].ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] stepSource stepTarget)
    (hwf : stepSource.constants.WF) :
    ConstructorTypesInstalled c.lparams sourceTypes[familyIdx].ctors
      stepTarget := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, _stepState, _target, _loweredState, hparams, hnodup, _hsize,
      _htarget, _hctorNames, _Hmappings, _Htrace, Haligned⟩
  let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
  have hheaderEnv : Hstep.restored.headerEnv = stepSource.add header :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderFresh : stepSource.find? header.name = none :=
    find?_none_of_contains_false hwf Hstep.restored.header.fresh
  have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hwf hheaderFresh
  have Hctors : ConstructorTypesInstalled c.lparams
      sourceTypes[familyIdx].ctors Hstep.restored.constructorEnv :=
    Haligned.constructorTypesInstalled
      (Hsources.getElem familyIdx hfamily).constructors HsourceBVar Hdisjoint
      rfl fvars hparams hnodup H.toResult.resultNParams
      (H.resultParamsSize.trans H.toResult.resultNParams) hheaderWF
  obtain ⟨_entries, HctorFresh⟩ :=
    Hstep.restored.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
    HctorFresh.targetWF hheaderWF
  let recursor : ConstantInfo :=
    .recInfo Hstep.restored.recursor.restored.newInfo
  have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name =
      none :=
    find?_none_of_contains_false hconstructorWF
      Hstep.restored.recursor.restored.fresh
  have htarget : stepTarget = Hstep.restored.constructorEnv.add recursor :=
    congrArg Prod.snd Hstep.restored.recursor.restored.output
  have HrecFresh : FreshExtension Hstep.restored.constructorEnv
      [recursor] stepTarget := by
    have Hadd : FreshExtension Hstep.restored.constructorEnv [recursor]
        (Hstep.restored.constructorEnv.add recursor) := .cons hrecFresh .nil
    rwa [← htarget] at Hadd
  exact Hctors.fresh HrecFresh hconstructorWF

/-- Forward form of `familiesConstructorsFromSources`. -/
theorem NestedLoweringOutputClosed.familiesConstructorTypesInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourceBVar : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      Closed source.type)
    (Hdisjoint : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      remaining sourceEnv targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hwf : sourceEnv.constants.WF) :
    ConstructorTypesInstalled c.lparams (remaining.flatMap (·.ctors))
      targetEnv := by
  induction Htrace generalizing processed with
  | nil => exact .nil
  | @cons head stepSource middle tail target Hstep Htail ih =>
    let familyIdx := processed.length
    have hfamily : familyIdx < sourceTypes.length := by
      simp [familyIdx, hsplit]
    have hfamilyEq : sourceTypes[familyIdx] = head := by
      simp [familyIdx, hsplit]
    have Hstep' : RestoredInductiveStep result loweredEnv auxRec allIndNames
        sourceTypes[familyIdx] stepSource middle := by
      simpa [hfamilyEq] using Hstep
    have hmem : sourceTypes[familyIdx] ∈ sourceTypes :=
      List.getElem_mem hfamily
    have Hhead := H.familyConstructorTypesInstalled Hc Hprod hempty Hsources
      familyIdx hfamily (HsourceBVar _ hmem) (Hdisjoint _ hmem) Hstep' hwf
    rw [hfamilyEq] at Hhead
    obtain ⟨_entries, Hfresh⟩ := Hstep'.restored.freshExtension hwf
    have hmiddleWF : middle.constants.WF := Hfresh.targetWF hwf
    obtain ⟨_tailEntries, HtailFresh⟩ := Htail.inductiveFreshExtension hmiddleWF
    have Hrest := ih (processed ++ [head])
      (by simpa [List.append_assoc] using hsplit) hmiddleWF
    simpa using (Hhead.fresh HtailFresh hmiddleWF).append Hrest

/-- Forward form of `restorationConstructorsFromSources`. -/
theorem NestedLoweringOutputClosed.restorationConstructorTypesInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourceBVar : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      Closed source.type)
    (Hdisjoint : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (Hrestored : NestedRestorationFolds result loweredEnv sourceEnv
      auxRec allIndNames sourceTypes auxRecNames out)
    (hwf : sourceEnv.constants.WF) :
    ConstructorTypesInstalled c.lparams (sourceTypes.flatMap (·.ctors))
      out.2 := by
  have Hprimary := H.familiesConstructorTypesInstalled Hc Hprod hempty
    Hsources HsourceBVar Hdisjoint Hrestored.inductives [] (by simp) hwf
  obtain ⟨_entries, Hfresh⟩ := Hrestored.inductives.inductiveFreshExtension hwf
  have hprimaryWF := Hfresh.targetWF hwf
  obtain ⟨_auxEntries, HauxFresh⟩ :=
    Hrestored.auxiliaries.recursorFreshExtension hprimaryWF
  exact Hprimary.fresh HauxFresh hprimaryWF

/-- Both directions of the constructor round trip for the complete
restoration fold.  The side conditions of the lowering/restoration inverse
(bound-variable closedness and disjointness from the auxiliary names) are
discharged from the source translation and the freshness of the auxiliary
declarations. -/
theorem NestedLoweringOutputClosed.constructorTypeRoundTripOfSource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Howners : ConstructorOwnersPresent c.env)
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec allIndNames sourceTypes auxRecNames out) :
    ConstructorsFromSources c.lparams c.env isUnsafe (sourceTypes.flatMap (·.ctors))
        c.env out.2 ∧
      ConstructorTypesInstalled c.lparams (sourceTypes.flatMap (·.ctors))
        out.2 := by
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors : RestoreAuxConstructorsFresh result loweredEnv
      envTypes :=
    H.restoreAuxConstructorsFreshAtTypes Hc Hprod Hsource Howners hempty
  have Htranslation : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      ∃ constructor,
        TrSourceConst envTypes c.lparams source.name source.type
          constructor := by
    intro type htype source hsource
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hsource.types type htype
      with ⟨target, _htarget, Htype⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_l Htype.ctors source hsource
      with ⟨constructor, _hconstructor, Hctor⟩
    exact ⟨constructor, Hctor⟩
  have HsourceBVar : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      Closed source.type := by
    intro type htype source hsource
    rcases Htranslation type htype source hsource with ⟨_constructor, Hctor⟩
    simpa [VLCtx.bvars] using Hctor.type.closed
  have Hdisjoint : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      RestoreSourceDisjoint result loweredEnv source.type := by
    intro type htype source hsource
    rcases Htranslation type htype source hsource with ⟨_constructor, Hctor⟩
    exact ((Hsources.inductiveSyntaxOfMem htype).constructors.of_mem
      hsource).noNestedAux.restoreSourceDisjointOfFresh
        Hctor.type.constantsDefined Hfamilies Hconstructors
  exact ⟨H.restorationConstructorsFromSources Hc Hprod hempty Hsources
      HsourceBVar Hdisjoint Hrestored Hc.checking.tr.map_wf,
    H.restorationConstructorTypesInstalled Hc Hprod hempty Hsources
      HsourceBVar Hdisjoint Hrestored Hc.checking.tr.map_wf⟩

/-- **Installed nested constructors are their source constructors up to
`Expr.eqv`.**  For a successful validated nested run:

* every constructor visible in the output environment is either inherited
  unchanged from the input environment, or is the restored installation of a
  constructor of one of the source families (`ConstructorsFromSources`);
* every source constructor is visible in the output environment
  (`ConstructorTypesInstalled`);

and in both cases the installed constructor carries the source constructor's
name and the declaration's universe parameters, and its type is
`Expr.eqv`-equal to the source type.  Literal equality is false in general;
see the module docstring. -/
theorem NestedRun.constructorTypeRoundTrip
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv) :
    ConstructorsFromSources lparams sourceProdEnv isUnsafe (sourceTypes.flatMap (·.ctors))
        sourceProdEnv outEnv ∧
      ConstructorTypesInstalled lparams (sourceTypes.flatMap (·.ctors))
        outEnv := by
  have key : ∀ P : LoweredRun E.loweredEnv,
      P.c.env = sourceProdEnv → P.c.lparams = lparams →
      P.nparams = nparams → P.indTypes = result.types.toArray →
      P.isUnsafe = isUnsafe → P.initialEnv = sourceVEnv → ContextWF P.c →
      ConstructorsFromSources lparams sourceProdEnv isUnsafe (sourceTypes.flatMap (·.ctors))
          sourceProdEnv outEnv ∧
        ConstructorTypesInstalled lparams (sourceTypes.flatMap (·.ctors))
          outEnv := by
    intro P henv hlparams hnparams hindTypes hunsafe hinitial Hc
    rcases P with ⟨c, stats, loweredDecl, nparams', depth, isUnsafe',
      initialEnv, indTypes, headerEnv, ctorEnv, Hheaders, R, Hprod⟩
    dsimp only at henv hlparams hnparams hindTypes hunsafe hinitial Hc
    subst hnparams hindTypes hunsafe hinitial
    let initialState : Lean4Lean.ElimNestedInductive.State :=
      { lvls := lparams.map .param, newTypes := #[] }
    have hempty : initialState.nestedAux = #[] := by
      apply Array.ext
      · rfl
      · intro i _hi₁ hi₂
        simp at hi₂
    have Hlower : NestedLoweringOutputClosed c.env
        E.validationFuel.inductiveFuel nparams' sourceTypes
        { initialState with newTypes := sourceTypes.toArray } result := by
      rw [henv]
      simpa [initialState] using E.lowering
    have Hsource : TrInductDeclCore initialEnv c.lparams nparams' sourceTypes
        isUnsafe' E.sourceCore.sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
      rw [hlparams]
      exact E.sourceCore.core
    have Howners' : ConstructorOwnersPresent c.env := by
      rw [henv]
      exact Howners
    have Hrestored : NestedRestorationFolds result E.loweredEnv
        c.env (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1
        ((), outEnv) := by
      rw [henv]
      exact E.restoration
    have H := Hlower.constructorTypeRoundTripOfSource Hc Hprod hempty
      Hsources Hsource Howners' Hrestored
    rw [henv, hlparams] at H
    exact H
  exact key E.lowered
    ((congrArg AddInductive.Context.env E.lowered_c).trans
      E.context_env)
    ((congrArg AddInductive.Context.lparams E.lowered_c).trans
      E.context_lparams)
    E.lowered_nparams E.lowered_indTypes E.lowered_isUnsafe_source
    E.lowered_initialEnv (E.lowered_c ▸ E.contextWF)

/-- Consumer form: a constructor visible after a successful validated nested
run is inherited, or its type is `RelevantEq` to (in particular, translates
exactly like) the type of a source constructor with the same name. -/
theorem NestedRun.installedConstructorSource
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hfind : outEnv.find? name = some (.ctorInfo info)) :
    sourceProdEnv.find? name = some (.ctorInfo info) ∨
      ∃ type ∈ sourceTypes, ∃ source ∈ type.ctors,
        info.name = source.name ∧ info.levelParams = lparams ∧
        (info.type == source.type) = true ∧
        EquivManager.RelevantEq info.type source.type ∧ info.isUnsafe = isUnsafe := by
  rcases (E.constructorTypeRoundTrip Hsources Howners).1 name info hfind with
    hold | ⟨source, hsource, horigin, hsafe⟩
  · exact .inl hold
  · rcases hsafe with hsafe | ⟨ci, hci⟩
    · rcases List.mem_flatMap.mp hsource with ⟨type, htype, hctor⟩
      exact .inr ⟨type, htype, source, hctor, horigin.name,
        horigin.levelParams, horigin.type_eqv,
        EquivManager.RelevantEq.of_eqv horigin.type_eqv, hsafe⟩
    · left
      have hwf : sourceProdEnv.constants.WF := by
        have h := E.contextWF.checking.tr.map_wf
        rwa [E.context_env] at h
      rcases E.restoration.inductives.inductiveFreshExtension hwf with ⟨_, Hprimary⟩
      have hprimaryWF := Hprimary.targetWF hwf
      rcases E.restoration.auxiliaries.recursorFreshExtension hprimaryWF with ⟨_, Hauxiliary⟩
      have h := Hauxiliary.preservesSourceFind hprimaryWF (Hprimary.preservesSourceFind hwf hci)
      rw [hfind] at h
      rw [← h] at hci
      exact hci

end VerifyInductive
end Lean4Lean
