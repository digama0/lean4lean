import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Environment
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledFamilyLookups
import Lean4Lean.Verify.Inductive.Nested.Install.DependencyOrder

/-!
# Projection registry of the constructor validation environment

The restored recursor type validator (`validateRestoredRecursorTypes`) runs
the ordinary checker in a side environment holding the restored source
headers and constructors (`ValidationEnvironment`).  This file shows that this
side environment satisfies the complete checking invariant against the source
recursor-checking environment (the source constructor environment with the
case eliminators and projection entries): its lookups are included in those of
the environment after the source-family restoration fold, every constructor
owner is present, and the projection registry is coherent. It also gives the local checking facts of
the restored environment (`NestedRestorationFolds.localValidOfInstallation`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! ### Restored constructors belong to freshly restored families -/

theorem RestoredInductiveStep.constructorInductFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      stepSource stepTarget)
    (hsourceWF : stepSource.constants.WF) :
    ∀ name info, stepTarget.find? name = some (.ctorInfo info) →
      stepSource.find? name = some (.ctorInfo info) ∨
        stepSource.find? info.induct = none := by
  intro name info hfind
  let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
  have hheaderFresh : stepSource.find? header.name = none :=
    find?_none_of_contains_false hsourceWF Hstep.restored.header.fresh
  have hheaderEnv : Hstep.restored.headerEnv = stepSource.add header :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hsourceWF hheaderFresh
  obtain ⟨ctorEntries, HctorFresh⟩ :=
    Hstep.restored.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
    HctorFresh.targetWF hheaderWF
  let recursor : ConstantInfo :=
    .recInfo Hstep.restored.recursor.restored.newInfo
  have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hconstructorWF
      Hstep.restored.recursor.restored.fresh
  have htarget : stepTarget = Hstep.restored.constructorEnv.add recursor :=
    congrArg Prod.snd Hstep.restored.recursor.restored.output
  rw [htarget] at hfind
  rcases Environment.find?_freshAdd_cases hconstructorWF recursor hrecFresh
      hfind with hrec | hconstructor
  · rcases hrec with ⟨_name, hinfo⟩
    simp [recursor] at hinfo
  · rcases Hstep.restored.constructors.constructorFindCases hheaderWF
        hconstructor with hbefore | hrestored
    · rw [hheaderEnv] at hbefore
      rcases Environment.find?_freshAdd_cases hsourceWF header hheaderFresh
          hbefore with hnewHeader | hsource
      · rcases hnewHeader with ⟨_name, hinfo⟩
        simp [header] at hinfo
      · exact Or.inl hsource
    · rcases hrestored with
        ⟨ctorIdx, hidx, ctorSource, ctorTarget, Hctor, _hname, hinfo⟩
      right
      rw [hinfo, Hstep.restoredConstructorOwnerAt Hlower Hprod hempty
        familyIdx hfamily ctorIdx hidx Hctor]
      simpa [header, ConstantInfo.name, ConstantInfo.toConstantVal] using
        hheaderFresh

theorem FoldSteps.sourceFamiliesConstructorInductFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      remaining sourceEnv targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hsourceWF : sourceEnv.constants.WF) :
    ∀ name info, targetEnv.find? name = some (.ctorInfo info) →
      sourceEnv.find? name = some (.ctorInfo info) ∨
        sourceEnv.find? info.induct = none := by
  induction Htrace generalizing processed with
  | nil => exact fun _ _ h => Or.inl h
  | @cons head stepSource middle tail target Hstep Htail ih =>
      intro name info hfind
      let familyIdx := processed.length
      have hfamily : familyIdx < sourceTypes.length := by
        simp [familyIdx, hsplit]
      have hfamilyEq : sourceTypes[familyIdx] = head := by
        simp [familyIdx, hsplit]
      have Hstep' : RestoredInductiveStep result loweredEnv auxRec
          (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
          stepSource middle := by
        simpa [hfamilyEq] using Hstep
      obtain ⟨entries, Hfresh⟩ := Hstep'.restored.freshExtension hsourceWF
      have hmiddleWF : middle.constants.WF := Hfresh.targetWF hsourceWF
      rcases ih (processed := processed ++ [head])
          (hsplit := by simpa [List.append_assoc] using hsplit)
          hmiddleWF name info hfind with hmid | hnone
      · exact Hstep'.constructorInductFresh Hlower Hprod hempty familyIdx
          hfamily hsourceWF name info hmid
      · right
        cases hsrc : stepSource.find? info.induct with
        | none => rfl
        | some found =>
          have := Hfresh.preservesSourceFind hsourceWF hsrc
          rw [this] at hnone
          cases hnone

/-- Auxiliary recursor restoration adds no constructors: constructor lookups
after the suffix already hold before it. -/
theorem FoldSteps.recursorConstructorFind
    (Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF)
    (hfind : targetEnv.find? name = some (.ctorInfo info)) :
    sourceEnv.find? name = some (.ctorInfo info) := by
  induction Htrace with
  | nil => exact hfind
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
      have hfresh : stepSource.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middle = stepSource.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middle.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      have hmid := ih hmiddleWF hfind
      rw [hmiddle] at hmid
      rcases Environment.find?_freshAdd_cases hsourceWF ci hfresh hmid with
          ⟨_, hci⟩ | hsrc
      · simp [ci] at hci
      · exact hsrc

theorem NestedRestorationFolds.constructorInductFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      out) :
    ∀ name info, out.2.find? name = some (.ctorInfo info) →
      c.env.find? name = some (.ctorInfo info) ∨
        c.env.find? info.induct = none := by
  intro name info hfind
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  obtain ⟨primaryEntries, HprimaryFresh⟩ :=
    Hrestored.inductives.inductiveFreshExtension hsourceWF
  have hprimaryWF : Hrestored.sourceFamiliesEnv.constants.WF :=
    HprimaryFresh.targetWF hsourceWF
  exact Hrestored.inductives.sourceFamiliesConstructorInductFresh Hlower Hprod
    hempty [] (by simp) hsourceWF name info
    (Hrestored.auxiliaries.recursorConstructorFind hprimaryWF hfind)

/-! ### Membership in the environment after the source-family restoration fold -/

theorem FoldSteps.constructorFindOfMem
    (H : FoldSteps (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) (hmem : cn ∈ names) :
    ∃ ctorOld : ConstructorVal,
      loweredEnv.find? cn = some (.ctorInfo ctorOld) ∧
      targetEnv.find? ctorOld.name = some (.ctorInfo
        { ctorOld with type := result.restoreNested loweredEnv ctorOld.type }) := by
  induction H with
  | nil => simp at hmem
  | @cons head source middle tail target Hstep Htail ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh : source.find? ci.name = none :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have hmiddle : middle = source.add ci :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨Hstep.oldInfo, Hstep.lookup, ?_⟩
      have hself : middle.find? ci.name = some ci := by
        rw [hmiddle]
        exact Environment.find?_freshAdd_self hwf ci hfresh
      rcases Htail.constructorFreshExtension hmiddleWF with ⟨entries, Hfresh⟩
      have hkept := Hfresh.preservesSourceFind hmiddleWF hself
      simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal,
        Hstep.restored.newInfo_eq] using hkept
    · exact ih hmiddleWF hmem

theorem FoldSteps.inductiveHeaderFindOfMem
    (H : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) (hmem : indType ∈ types) :
    ∃ oldInfo : InductiveVal,
      loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
      targetEnv.find? oldInfo.name =
        some (.inductInfo { oldInfo with all := allIndNames }) ∧
      ∀ cn ∈ oldInfo.ctors, ∃ ctorOld : ConstructorVal,
        loweredEnv.find? cn = some (.ctorInfo ctorOld) ∧
        targetEnv.find? ctorOld.name = some (.ctorInfo
          { ctorOld with type := result.restoreNested loweredEnv ctorOld.type }) := by
  induction H with
  | nil => simp at hmem
  | @cons head source middle tail target Hstep Htail ih =>
    obtain ⟨entries, Hfresh⟩ := Hstep.restored.freshExtension hwf
    have hmiddleWF : middle.constants.WF := Hfresh.targetWF hwf
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨Hstep.oldInfo, Hstep.lookup, ?_, ?_⟩
      · have hheader := Hstep.restored.headerFind hwf
        rcases Htail.inductiveFreshExtension hmiddleWF with ⟨entries', Hfresh'⟩
        have := Hfresh'.preservesSourceFind hmiddleWF hheader
        simpa [Hstep.restored.header.restored] using this
      · intro cn hcn
        let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
        have hheaderFresh : source.find? header.name = none :=
          find?_none_of_contains_false hwf Hstep.restored.header.fresh
        have hheaderEnv : Hstep.restored.headerEnv = source.add header :=
          congrArg Prod.snd Hstep.restored.header.output
        have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
          hheaderEnv.symm ▸ constantsWF_add_checked hwf hheaderFresh
        rcases Hstep.restored.constructors.constructorFindOfMem hheaderWF hcn
          with ⟨ctorOld, hlookup, hfindCtor⟩
        refine ⟨ctorOld, hlookup, ?_⟩
        obtain ⟨ctorEntries, HctorFresh⟩ :=
          Hstep.restored.constructors.constructorFreshExtension hheaderWF
        have hconstructorWF := HctorFresh.targetWF hheaderWF
        let recursor : ConstantInfo :=
          .recInfo Hstep.restored.recursor.restored.newInfo
        have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name =
            none :=
          find?_none_of_contains_false hconstructorWF
            Hstep.restored.recursor.restored.fresh
        have hmiddleEq : middle = Hstep.restored.constructorEnv.add recursor :=
          congrArg Prod.snd Hstep.restored.recursor.restored.output
        have hmid : middle.find? ctorOld.name = some (.ctorInfo
            { ctorOld with type := result.restoreNested loweredEnv ctorOld.type }) := by
          rw [hmiddleEq]
          exact Environment.find?_freshAdd_preserves hconstructorWF recursor
            hrecFresh hfindCtor
        rcases Htail.inductiveFreshExtension hmiddleWF with ⟨entries', Hfresh'⟩
        exact Hfresh'.preservesSourceFind hmiddleWF hmid
    · exact ih hmiddleWF hmem

theorem FoldSteps.inductiveFindCases
    (H : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : targetEnv.find? familyName = some (.inductInfo info)) :
    sourceEnv.find? familyName = some (.inductInfo info) ∨
      ∃ indType ∈ types, ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        familyName = oldInfo.name ∧ info = { oldInfo with all := allIndNames } := by
  induction H with
  | nil => exact Or.inl hfind
  | @cons head source middle tail target Hstep Htail ih =>
    obtain ⟨entries, Hfresh⟩ := Hstep.restored.freshExtension hwf
    have hmiddleWF : middle.constants.WF := Hfresh.targetWF hwf
    rcases ih hmiddleWF hfind with hmid | ⟨indType, hmem, oldInfo, hlookup, hF, hinfo⟩
    · rcases Hstep.restored.inductiveFindCases hwf hmid with ⟨hF, hinfo⟩ | hsrc
      · right
        refine ⟨head, by simp, Hstep.oldInfo, Hstep.lookup, ?_, ?_⟩
        · rw [hF]
          simp [Hstep.restored.header.restored]
        · rw [hinfo]
          exact Hstep.restored.header.restored
      · exact Or.inl hsrc
    · right
      exact ⟨indType, by simp [hmem], oldInfo, hlookup, hF, hinfo⟩

/-! ### Lookups in the constructor validation environment -/

theorem FoldSteps.headersFreshExtension
    {loweredEnv : Environment} {allIndNames : List Name}
    {types : List InductiveType} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (fun indType source target => ValidationHeaderStep loweredEnv
        allIndNames indType.name source target) types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | @cons head source middle tail target Hstep Htail ih =>
    let ci : ConstantInfo := .inductInfo { Hstep.oldInfo with all := allIndNames }
    have hfresh : source.find? ci.name = none :=
      find?_none_of_contains_false hwf
        (by simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hstep.fresh)
    have hmiddle : middle = source.add ci := Hstep.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    rcases ih hmiddleWF with ⟨entries, Htail'⟩
    refine ⟨ci :: entries, .cons hfresh ?_⟩
    rw [← hmiddle]
    exact Htail'

theorem FoldSteps.headerFind
    {loweredEnv : Environment} {allIndNames : List Name}
    {types : List InductiveType} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (fun indType source target => ValidationHeaderStep loweredEnv
        allIndNames indType.name source target) types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) (hmem : indType ∈ types) :
    ∃ oldInfo : InductiveVal,
      loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
      targetEnv.find? oldInfo.name =
        some (.inductInfo { oldInfo with all := allIndNames }) := by
  induction H with
  | nil => simp at hmem
  | @cons head source middle tail target Hstep Htail ih =>
    let ci : ConstantInfo := .inductInfo { Hstep.oldInfo with all := allIndNames }
    have hfresh : source.find? ci.name = none :=
      find?_none_of_contains_false hwf
        (by simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hstep.fresh)
    have hmiddle : middle = source.add ci := Hstep.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨Hstep.oldInfo, Hstep.lookup, ?_⟩
      have hself : middle.find? ci.name = some ci := by
        rw [hmiddle]
        exact Environment.find?_freshAdd_self hwf ci hfresh
      rcases Htail.headersFreshExtension hmiddleWF with ⟨entries, Hfresh⟩
      have := Hfresh.preservesSourceFind hmiddleWF hself
      simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal] using this
    · exact ih hmiddleWF hmem

theorem FoldSteps.headerFindCases
    {loweredEnv : Environment} {allIndNames : List Name}
    {types : List InductiveType} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (fun indType source target => ValidationHeaderStep loweredEnv
        allIndNames indType.name source target) types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : targetEnv.find? name = some ci) :
    sourceEnv.find? name = some ci ∨
      ∃ indType ∈ types, ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        name = oldInfo.name ∧
        ci = .inductInfo { oldInfo with all := allIndNames } := by
  induction H with
  | nil => exact Or.inl hfind
  | @cons head source middle tail target Hstep Htail ih =>
    let ci' : ConstantInfo := .inductInfo { Hstep.oldInfo with all := allIndNames }
    have hfresh : source.find? ci'.name = none :=
      find?_none_of_contains_false hwf
        (by simpa [ci', ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hstep.fresh)
    have hmiddle : middle = source.add ci' := Hstep.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    rcases ih hmiddleWF hfind with hmid |
        ⟨indType, hmem, oldInfo, hlookup, hn, hci⟩
    · rw [hmiddle] at hmid
      rcases Environment.find?_freshAdd_cases hwf ci' hfresh hmid with
          ⟨hn, hci⟩ | hsrc
      · right
        refine ⟨head, by simp, Hstep.oldInfo, Hstep.lookup, ?_, hci⟩
        simpa [ci', ConstantInfo.name, ConstantInfo.toConstantVal] using hn
      · exact Or.inl hsrc
    · right
      exact ⟨indType, by simp [hmem], oldInfo, hlookup, hn, hci⟩

theorem FoldSteps.constructorsFreshExtension
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {allowPrimitive : Bool}
    {names : List Name} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (ValidationConstructorStep result loweredEnv allowPrimitive)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | @cons head source middle tail target Hstep Htail ih =>
    let ci : ConstantInfo := .ctorInfo
      { Hstep.oldInfo with type := result.restoreNested loweredEnv Hstep.oldInfo.type }
    have hfresh : source.find? ci.name = none :=
      find?_none_of_contains_false hwf
        (by simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hstep.fresh)
    have hmiddle : middle = source.add ci := Hstep.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    rcases ih hmiddleWF with ⟨entries, Htail'⟩
    refine ⟨ci :: entries, .cons hfresh ?_⟩
    rw [← hmiddle]
    exact Htail'

theorem FoldSteps.validationConstructorFindCases
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {allowPrimitive : Bool}
    {names : List Name} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (ValidationConstructorStep result loweredEnv allowPrimitive)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : targetEnv.find? name = some ci) :
    sourceEnv.find? name = some ci ∨
      ∃ cn ∈ names, ∃ ctorOld : ConstructorVal,
        loweredEnv.find? cn = some (.ctorInfo ctorOld) ∧
        name = ctorOld.name ∧
        ci = .ctorInfo
          { ctorOld with type := result.restoreNested loweredEnv ctorOld.type } := by
  induction H with
  | nil => exact Or.inl hfind
  | @cons head source middle tail target Hstep Htail ih =>
    let ci' : ConstantInfo := .ctorInfo
      { Hstep.oldInfo with type := result.restoreNested loweredEnv Hstep.oldInfo.type }
    have hfresh : source.find? ci'.name = none :=
      find?_none_of_contains_false hwf
        (by simpa [ci', ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hstep.fresh)
    have hmiddle : middle = source.add ci' := Hstep.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    rcases ih hmiddleWF hfind with hmid |
        ⟨cn, hmem, ctorOld, hlookup, hn, hci⟩
    · rw [hmiddle] at hmid
      rcases Environment.find?_freshAdd_cases hwf ci' hfresh hmid with
          ⟨hn, hci⟩ | hsrc
      · right
        refine ⟨head, by simp, Hstep.oldInfo, Hstep.lookup, ?_, hci⟩
        simpa [ci', ConstantInfo.name, ConstantInfo.toConstantVal] using hn
      · exact Or.inl hsrc
    · right
      exact ⟨cn, by simp [hmem], ctorOld, hlookup, hn, hci⟩

theorem FoldSteps.familiesFreshExtension
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {allowPrimitive : Bool}
    {types : List InductiveType} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (ValidationFamilyStep result loweredEnv
        allowPrimitive) types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | @cons head source middle tail target Hstep Htail ih =>
    rcases Hstep.constructors.constructorsFreshExtension hwf with ⟨entries, Hhead⟩
    have hmiddleWF : middle.constants.WF := Hhead.targetWF hwf
    rcases ih hmiddleWF with ⟨entries', Htail'⟩
    exact ⟨entries ++ entries', Hhead.append Htail'⟩

theorem FoldSteps.familiesFindCases
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {allowPrimitive : Bool}
    {types : List InductiveType} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (ValidationFamilyStep result loweredEnv
        allowPrimitive) types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : targetEnv.find? name = some ci) :
    sourceEnv.find? name = some ci ∨
      ∃ indType ∈ types, ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        ∃ cn ∈ oldInfo.ctors, ∃ ctorOld : ConstructorVal,
          loweredEnv.find? cn = some (.ctorInfo ctorOld) ∧
          name = ctorOld.name ∧
          ci = .ctorInfo
            { ctorOld with type := result.restoreNested loweredEnv ctorOld.type } := by
  induction H with
  | nil => exact Or.inl hfind
  | @cons head source middle tail target Hstep Htail ih =>
    rcases Hstep.constructors.constructorsFreshExtension hwf with ⟨entries, Hhead⟩
    have hmiddleWF : middle.constants.WF := Hhead.targetWF hwf
    rcases ih hmiddleWF hfind with hmid |
        ⟨indType, hmem, oldInfo, hlookup, cn, hcn, ctorOld, hctor, hn, hci⟩
    · rcases Hstep.constructors.validationConstructorFindCases hwf hmid with hsrc |
          ⟨cn, hcn, ctorOld, hctor, hn, hci⟩
      · exact Or.inl hsrc
      · right
        exact ⟨head, by simp, Hstep.oldInfo, Hstep.lookup, cn, hcn, ctorOld,
          hctor, hn, hci⟩
    · right
      exact ⟨indType, by simp [hmem], oldInfo, hlookup, cn, hcn, ctorOld, hctor,
        hn, hci⟩

theorem ValidationEnvironment.headerEnvWF
    (H : ValidationEnvironment result loweredEnv sourceEnv
      allIndNames allowPrimitive types targetEnv)
    (hwf : sourceEnv.constants.WF) : H.headerEnv.constants.WF := by
  rcases H.headers.headersFreshExtension hwf with ⟨entries, Hfresh⟩
  exact Hfresh.targetWF hwf

theorem ValidationEnvironment.preservesSourceFind
    (H : ValidationEnvironment result loweredEnv sourceEnv
      allIndNames allowPrimitive types targetEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : sourceEnv.find? name = some ci) :
    targetEnv.find? name = some ci := by
  rcases H.headers.headersFreshExtension hwf with ⟨entries, Hheaders⟩
  rcases H.constructors.familiesFreshExtension (H.headerEnvWF hwf) with
    ⟨entries', Hconstructors⟩
  exact Hconstructors.preservesSourceFind (H.headerEnvWF hwf)
    (Hheaders.preservesSourceFind hwf hfind)

/-- The `quotInit` flag of the kernel environment is unchanged by the
constructor validation restoration. -/
theorem ValidationEnvironment.quotInit_eq
    (H : ValidationEnvironment result loweredEnv sourceEnv
      allIndNames allowPrimitive types targetEnv)
    (hwf : sourceEnv.constants.WF) : targetEnv.quotInit = sourceEnv.quotInit := by
  rcases H.headers.headersFreshExtension hwf with ⟨entries, Hheaders⟩
  rcases H.constructors.familiesFreshExtension (H.headerEnvWF hwf) with
    ⟨entries', Hconstructors⟩
  exact Hconstructors.quotInit_eq.trans Hheaders.quotInit_eq

theorem ValidationEnvironment.findCases
    (H : ValidationEnvironment result loweredEnv sourceEnv
      allIndNames allowPrimitive types targetEnv)
    (hwf : sourceEnv.constants.WF)
    (hfind : targetEnv.find? name = some ci) :
    sourceEnv.find? name = some ci ∨
      (∃ indType ∈ types, ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        name = oldInfo.name ∧
        ci = .inductInfo { oldInfo with all := allIndNames }) ∨
      (∃ indType ∈ types, ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        ∃ cn ∈ oldInfo.ctors, ∃ ctorOld : ConstructorVal,
          loweredEnv.find? cn = some (.ctorInfo ctorOld) ∧
          name = ctorOld.name ∧
          ci = .ctorInfo
            { ctorOld with type := result.restoreNested loweredEnv ctorOld.type }) := by
  rcases H.constructors.familiesFindCases (H.headerEnvWF hwf) hfind with
      hheaders | hctor
  · rcases H.headers.headerFindCases hwf hheaders with hsrc | hheader
    · exact Or.inl hsrc
    · exact Or.inr (Or.inl hheader)
  · exact Or.inr (Or.inr hctor)

theorem ValidationEnvironment.headerFind
    (H : ValidationEnvironment result loweredEnv sourceEnv
      allIndNames allowPrimitive types targetEnv)
    (hwf : sourceEnv.constants.WF) (hmem : indType ∈ types) :
    ∃ oldInfo : InductiveVal,
      loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
      targetEnv.find? oldInfo.name =
        some (.inductInfo { oldInfo with all := allIndNames }) := by
  rcases H.headers.headerFind hwf hmem with ⟨oldInfo, hlookup, hheader⟩
  rcases H.constructors.familiesFreshExtension (H.headerEnvWF hwf) with
    ⟨entries', Hconstructors⟩
  exact ⟨oldInfo, hlookup,
    Hconstructors.preservesSourceFind (H.headerEnvWF hwf) hheader⟩

/-! ### Restricting constructor alignments to a sub-environment -/

def CtorInfoAlignment.restrict
    (H : CtorInfoAlignment target decl familyIdx ctorIdx familyInfo)
    (hlookup : sub.find? (familyInfo.ctors[ctorIdx]'H.familyInfo_ctorIdx_lt) =
      some (.ctorInfo H.info)) :
    CtorInfoAlignment sub decl familyIdx ctorIdx familyInfo :=
  { H with lookup := hlookup }

theorem InductInfoAlignment.restrict
    (H : InductInfoAlignment target decl familyIdx familyInfo)
    (hfamily : sub.find? familyInfo.name = some (.inductInfo familyInfo))
    (hsub : ∀ {name ci}, sub.find? name = some ci → target.find? name = some ci)
    (hctors : ∀ ctorIdx (hctor : ctorIdx < familyInfo.ctors.length),
      ∃ ci, sub.find? familyInfo.ctors[ctorIdx] = some ci) :
    InductInfoAlignment sub decl familyIdx familyInfo where
  familyIdx_lt := H.familyIdx_lt
  name := H.name
  lookup := hfamily
  all := H.all
  levelParams := H.levelParams
  numParams := H.numParams
  numIndices := H.numIndices
  constructors := H.constructors
  isUnsafe := H.isUnsafe
  constructor ctorIdx hctor := by
    rcases H.constructor ctorIdx hctor with ⟨C⟩
    obtain ⟨ci, hci⟩ := hctors ctorIdx C.familyInfo_ctorIdx_lt
    have hci' := hsub hci
    rw [C.lookup] at hci'
    cases hci'
    exact ⟨CtorInfoAlignment.restrict C hci⟩

theorem InductInfosFromDecl.restrict
    (H : InductInfosFromDecl source target decl)
    (hsourceSub : ∀ {name ci}, source.find? name = some ci →
      sub.find? name = some ci)
    (hsub : ∀ {name ci}, sub.find? name = some ci → target.find? name = some ci)
    (hctors : ∀ familyName familyInfo familyIdx,
      sub.find? familyName = some (.inductInfo familyInfo) →
      source.find? familyName = none →
      InductInfoAlignment target decl familyIdx familyInfo →
      ∀ ctorIdx (hctor : ctorIdx < familyInfo.ctors.length),
        ∃ ci, sub.find? familyInfo.ctors[ctorIdx] = some ci) :
    InductInfosFromDecl source sub decl := by
  intro familyName familyInfo hfind
  cases hsrc : source.find? familyName with
  | some ci =>
    have hci := hsourceSub hsrc
    rw [hfind] at hci
    cases Option.some.inj hci
    exact Or.inl rfl
  | none =>
    rcases H familyName familyInfo (hsub hfind) with hold | ⟨familyIdx, hname, ⟨A⟩⟩
    · rw [hold] at hsrc
      cases hsrc
    · right
      refine ⟨familyIdx, hname, ⟨InductInfoAlignment.restrict A ?_ hsub
        (hctors familyName familyInfo familyIdx hfind hsrc A)⟩⟩
      rw [← hname]
      exact hfind

/-! ### The validation environment against the source recursor-checking environment -/

/-- The constructor validation environment satisfies the complete checking
invariant against the source recursor-checking environment (the source
constructor environment with the case eliminators `es` and the projection
entries). Owners and registry alignment
are transported from the environment after the source-family restoration
fold, whose lookups include those of the validation environment. -/
theorem ValidationEnvironment.validProjected
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      out)
    (H : ValidationEnvironment result loweredEnv c.env
      (sourceTypes.map (fun type => type.name)) allowPrimitive sourceTypes
      validationEnv)
    (hvalid : CheckingEnv.ValidCore c.safety validationEnv envCtors)
    (hsourceValid : CheckingEnv.Valid c.safety c.env sourceVEnv)
    (hcasesWF : (envCtors.addEliminators es).WF)
    (hprojectedWF : ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries).WF)
    (htels : CtorTelescopes c.safety validationEnv envCtors) :
    CheckingEnv.Valid c.safety validationEnv
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) := by
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have Howners : ConstructorOwnersPresent c.env := Hc.checking.constructorOwners
  have hvalidWF : validationEnv.constants.WF := hvalid.tr.map_wf
  have Hinitial : InductInfosFromDecl c.env.constants c.env.constants
      sourceDecl := fun _ _ h => .inl h
  have Hprimary : InductInfosFromDecl c.env.constants
      Hrestored.sourceFamiliesEnv.constants sourceDecl :=
    Hrestored.inductives.sourceFamiliesInductInfosFromDecl Hlower Hc
      Hprod Hsource Hmetadata Hsources Harity Howners hempty [] (by simp)
      hsourceWF Hinitial
  have HprimaryOwners : ConstructorOwnersPresent Hrestored.sourceFamiliesEnv :=
    Hrestored.inductives.sourceFamiliesConstructorOwnersPresent Hlower Hprod
      hempty [] (by simp) hsourceWF Howners
  have HprimaryInduct :=
    Hrestored.inductives.sourceFamiliesConstructorInductFresh Hlower Hprod
      hempty [] (by simp) hsourceWF
  obtain ⟨primaryEntries, HprimaryFresh⟩ :=
    Hrestored.inductives.inductiveFreshExtension hsourceWF
  have hprimaryWF : Hrestored.sourceFamiliesEnv.constants.WF :=
    HprimaryFresh.targetWF hsourceWF
  have hsubset : ∀ {name ci}, validationEnv.find? name = some ci →
      Hrestored.sourceFamiliesEnv.find? name = some ci := by
    intro name ci hfind
    rcases H.findCases hsourceWF hfind with hold |
        ⟨indType, hmem, oldInfo, hlookup, rfl, rfl⟩ |
        ⟨indType, hmem, oldInfo, hlookup, cn, hcn, ctorOld, hctorLookup, rfl, rfl⟩
    · exact HprimaryFresh.preservesSourceFind hsourceWF hold
    · rcases Hrestored.inductives.inductiveHeaderFindOfMem hsourceWF hmem with
        ⟨oldInfo', hlookup', hheader, _⟩
      cases ConstantInfo.inductInfo.inj (Option.some.inj (hlookup.symm.trans hlookup'))
      exact hheader
    · rcases Hrestored.inductives.inductiveHeaderFindOfMem hsourceWF hmem with
        ⟨oldInfo', hlookup', _, hctors⟩
      cases ConstantInfo.inductInfo.inj (Option.some.inj (hlookup.symm.trans hlookup'))
      rcases hctors cn hcn with ⟨ctorOld', hctorLookup', hctorFind⟩
      cases ConstantInfo.ctorInfo.inj
        (Option.some.inj (hctorLookup.symm.trans hctorLookup'))
      exact hctorFind
  have hsourceSub : ∀ {name ci}, c.env.find? name = some ci →
      validationEnv.find? name = some ci :=
    fun h => H.preservesSourceFind hsourceWF h
  have hfindV : ∀ {name ci}, validationEnv.constants.find? name = some ci →
      validationEnv.find? name = some ci := by
    intro name ci h
    rw [Lean.Kernel.Environment.find?, hvalidWF.find?'_eq_find?]
    exact h
  have hfindS : ∀ {name ci}, c.env.constants.find? name = some ci →
      c.env.find? name = some ci := by
    intro name ci h
    rw [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
    exact h
  have howners : ConstructorOwnersPresent validationEnv := by
    intro name info hfind
    rcases H.findCases hsourceWF hfind with hold |
        ⟨_, _, _, _, _, hci⟩ | ⟨_, _, _, _, _, _, _, _, _, _⟩
    · rcases Howners name info hold with ⟨owner, howner, hrest⟩
      exact ⟨owner, hsourceSub howner, hrest⟩
    · cases hci
    · rcases HprimaryOwners name info (hsubset hfind) with ⟨owner, howner, hrest⟩
      rcases Hrestored.inductives.inductiveFindCases hsourceWF howner with hold |
          ⟨indType', hmem', oldInfo', hlookup', hF, hownerEq⟩
      · exact ⟨owner, hsourceSub hold, hrest⟩
      · rcases H.headerFind hsourceWF hmem' with ⟨oldInfo'', hlookup'', hheader⟩
        cases ConstantInfo.inductInfo.inj
          (Option.some.inj (hlookup'.symm.trans hlookup''))
        subst hownerEq
        exact ⟨_, by rw [hF]; exact hheader, hrest⟩
  have horiginsV : InductInfosFromDecl c.env.constants validationEnv.constants sourceDecl := by
    apply InductInfosFromDecl.restrict Hprimary
    · intro name ci h
      exact Environment.mapFind_of_find hvalidWF (hsourceSub (hfindS h))
    · intro name ci h
      exact Environment.mapFind_of_find hprimaryWF (hsubset (hfindV h))
    · intro familyName familyInfo familyIdx hfind _hnone A ctorIdx hctor
      have hctorDecl :
          ctorIdx < (sourceDecl.types[familyIdx]'A.familyIdx_lt).ctors.length := by
        rw [← A.constructors]
        exact hctor
      rcases A.constructor ctorIdx hctorDecl with ⟨C⟩
      have hname : familyInfo.ctors[ctorIdx]'hctor =
          ((sourceDecl.types[familyIdx]'A.familyIdx_lt).ctors[ctorIdx]'hctorDecl).name :=
        C.name
      have hmem : ((sourceDecl.types[familyIdx]'A.familyIdx_lt).ctors[ctorIdx]'hctorDecl) ∈
          sourceDecl.constructorConstants := by
        simp only [VInductDecl.constructorConstants, List.mem_flatMap]
        exact ⟨_, List.getElem_mem _, List.getElem_mem _⟩
      have habstract := VEnv.addConstVals_get Hsource.ctorsAdded hmem
      rw [← hname] at habstract
      rcases hvalid.tr.aligned.find?_iff.mpr ⟨_, habstract⟩ with ⟨ci, hci, _⟩
      exact ⟨ci, hci⟩
  have hle : sourceVEnv ≤ (envCtors.addEliminators es).addProjections sourceDecl.projectionEntries :=
    (VEnv.addConstVals_le Hsource.typesAdded).trans
      ((VEnv.addConstVals_le Hsource.ctorsAdded).trans VEnv.addEliminators_addProjections_le)
  have hpres : ∀ {n ci}, c.env.constants.find? n = some ci →
      validationEnv.constants.find? n = some ci := by
    intro n ci hfind
    have hfind' : c.env.find? n = some ci := by
      rw [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
      exact hfind
    have hout := H.preservesSourceFind hsourceWF hfind'
    rwa [Lean.Kernel.Environment.find?, hvalidWF.find?'_eq_find?] at hout
  have hrecursors : RecursorEnvCoherent c.safety validationEnv.constants
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) := by
    refine hsourceValid.recursors.extendSimple hpres ?_ hle ?_
    · intro n rec hfind _
      have hfind' : validationEnv.find? n = some (.recInfo rec) := by
        rw [Lean.Kernel.Environment.find?, hvalidWF.find?'_eq_find?]
        exact hfind
      rcases H.findCases hsourceWF hfind' with hold |
          ⟨_, _, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, _, _, heq⟩
      · rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?] at hold
      · cases heq
      · cases heq
    · intro df hdf
      rw [VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
        VEnv.addConstVals_defeqs Hsource.ctorsAdded,
        VEnv.addConstVals_defeqs Hsource.typesAdded] at hdf
      exact hdf
  have hquot : validationEnv.quotInit = true →
      QuotEnvCoherent validationEnv.constants
        ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) := by
    intro hq
    rw [H.quotInit_eq hsourceWF] at hq
    exact (hsourceValid.quot hq).extend hpres hle hrecursors.heads
  have hcore' := (hvalid.addEliminators hcasesWF).addProjections hprojectedWF
  have hpresV : ∀ {n ci}, c.env.find? n = some ci → validationEnv.find? n = some ci :=
    fun h => hsourceSub h
  have hkindsV : ∀ {n ci}, validationEnv.find? n = some ci → c.env.find? n = none →
      (∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) := by
    intro n ci hfind hnone
    rcases H.findCases hsourceWF hfind with hold | ⟨_, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    · rw [hold] at hnone; cases hnone
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  have hsourceNames : sourceDecl.sourceNames.Nodup := by
    have := VEnv.addConstVals_names_nodup
      (VEnv.addConstVals_append Hsource.typesAdded Hsource.ctorsAdded)
    simpa [VInductDecl.sourceNames, List.map_append] using this
  have hreg : InstalledBlocks.DeclRegistered ((envCtors.addEliminators es).addProjections
      sourceDecl.projectionEntries) sourceDecl es := {
    typeUvars := by
      intro type htype
      rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types type htype with
        ⟨_, _, Htype⟩
      rw [Htype.header.uvars, Hsource.uvars]
    constructorUvars := Lean4Lean.VerifyInductive.TrInductDeclCore.constructorUvars Hsource
    family := fun i hi => ((VEnv.addConstVals_le Hsource.ctorsAdded).trans
        VEnv.addEliminators_addProjections_le).constants
      (VEnv.addConstVals_get Hsource.typesAdded
        (List.mem_map.mpr ⟨sourceDecl.types[i], List.getElem_mem hi, rfl⟩))
    ctor := fun i k hi hk => VEnv.addEliminators_addProjections_le.constants
      (VEnv.addConstVals_get Hsource.ctorsAdded (by
        simp only [VInductDecl.constructorConstants, List.mem_flatMap]
        exact ⟨_, List.getElem_mem hi, List.getElem_mem hk⟩))
    projections := fun e he => VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩)
    eliminators := fun e he => VEnv.addProjections_le.eliminators
      (VEnv.addEliminators_iff.mpr (.inl he)) }
  have hcover := InductInfosFromDecl.cover hsourceValid.tr hcore'.tr Hheaders.sourcePresent
    hpresV horiginsV howners
    (fun T hT => (VEnv.addConstVals_names_fresh Hsource.typesAdded).2 _
      (List.mem_map.mpr ⟨T, hT, rfl⟩))
    (fun T hT => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      exact ⟨_, hreg.family i hi⟩)
    hsourceNames hkindsV
  have hblocks := hsourceValid.blocks.addCtorStage Hheaders.sourcePresent hsourceWF hcore'.tr
    hpresV hle horiginsV hcover
    (by
      have := VEnv.addConstVals_names_nodup Hsource.typesAdded
      simpa [VInductDecl.typeConstants, Function.comp_def] using this)
    howners []
    (fun hf hnone => by
      rcases hkindsV hf hnone with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h)
    (by simp) (by simp) (by simp)
    es hreg
    (fun hp => by
      rcases VEnv.addProjections_iff.mp hp with ⟨e, he, rfl, rfl⟩ | hold
      · exact .inr he
      · left
        rw [VEnv.addEliminators_projections, VEnv.addConstVals_projections Hsource.ctorsAdded,
          VEnv.addConstVals_projections Hsource.typesAdded] at hold
        exact hold)
    (htels.mono (VEnv.addEliminators_le.trans VEnv.addProjections_le))
  exact hcore'.toValid hblocks hrecursors.heads hquot


/-! ### The restored environment -/

/-- Local checking facts for the restored environment: core invariants
come from the block installation `canonical` of a permutation of the installed
entries, owners from the restoration fold steps, and the alignment of the restored source
families with the source declaration. These facts do not supply recursor semantics. -/
theorem NestedRestorationFolds.localValidOfInstallation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv))
    (Hactual : FreshExtension c.env actualEntries outEnv)
    (canonical : BlockInstallation c.safety c.env sourceVEnv types ctors recursors
      sourceDecl.projectionEntries canonicalProdEnv installedVEnv)
    (hperm : actualEntries ~ (types ++ ctors ++ recursors).map Prod.fst)
    (hvalidSource : CheckingEnv.Valid c.safety c.env sourceVEnv) :
    CheckingEnv.ValidCore c.safety outEnv installedVEnv ∧
      ConstructorOwnersPresent outEnv ∧
      InductInfosFromDecl c.env.constants outEnv.constants sourceDecl := by
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have Howners : ConstructorOwnersPresent c.env := Hc.checking.constructorOwners
  have houtWF : outEnv.constants.WF := Hactual.targetWF hsourceWF
  have howners : ConstructorOwnersPresent outEnv :=
    Hrestored.constructorOwnersPresent Hlower Hc Hprod hempty Howners
  have horigins : InductInfosFromDecl c.env.constants outEnv.constants
      sourceDecl :=
    Hrestored.inductInfosFromDecl Hlower Hc Hprod Hsource Hmetadata
      Hsources Harity Howners hempty
  exact ⟨canonical.validCoreOfFreshPermutation Hactual hperm hvalidSource.toValidCore,
    howners, horigins⟩

end VerifyInductive
end Lean4Lean
