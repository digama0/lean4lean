import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps

/-! The recursors installed by a nested restoration are the restored recursors of its steps. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! ### The fresh recursors of a nested restoration -/

/-- A restored constructor fold installs no recursor. -/
theorem FoldSteps.constructorFreshExtensionNoRec
    (H : FoldSteps (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      ∀ e ∈ entries, ∀ r, e ≠ .recInfo r := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh := find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hrec⟩
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    intro e he r
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · nofun
    · exact hrec e he r

/-- The recursors installed by a restoration step are those of the step. -/
def RecursorsFromSteps (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name) (allIndNames : List Name)
    (oldRecNames : List Name) (entries : List ConstantInfo) : Prop :=
  ∀ e ∈ entries, ∀ r, e = .recInfo r →
    ∃ oldRecName ∈ oldRecNames, ∃ (s t : Environment)
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s t),
      r = Hstep.restored.newInfo

theorem RecursorsFromSteps.append
    (H₁ : RecursorsFromSteps result loweredEnv auxRec allIndNames names₁ entries₁)
    (H₂ : RecursorsFromSteps result loweredEnv auxRec allIndNames names₂ entries₂) :
    RecursorsFromSteps result loweredEnv auxRec allIndNames (names₁ ++ names₂)
      (entries₁ ++ entries₂) := by
  intro e he r hr
  rcases List.mem_append.mp he with he | he
  · obtain ⟨n, hn, h⟩ := H₁ e he r hr
    exact ⟨n, List.mem_append_left _ hn, h⟩
  · obtain ⟨n, hn, h⟩ := H₂ e he r hr
    exact ⟨n, List.mem_append_right _ hn, h⟩

theorem SourceFamilyRestoration.freshExtensionRecursorSteps
    (H : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      RecursorsFromSteps result loweredEnv auxRec allIndNames
        [Lean.mkRecName indType.name] entries ∧
      .inductInfo H.header.newInfo ∈ entries := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : FoldSteps
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshExtensionNoRec hwfHeader with
    ⟨constructors, Hconstructors, hnorec⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  refine ⟨header :: constructors ++ [recursor], ?_, ?_, by simp [header]⟩
  · rw [htarget]
    exact FreshExtension.cons hheaderFresh
      (Hconstructors.append (.cons hrecFresh .nil))
  · intro e he r hr
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | he | rfl
    · simp [header] at hr
    · exact absurd hr (hnorec e he r)
    · simp only [recursor, ConstantInfo.recInfo.injEq] at hr
      subst hr
      exact ⟨_, List.mem_singleton_self _, _, _, H.recursor, rfl⟩

theorem FoldSteps.inductiveFreshExtensionRecursorSteps
    (H : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      RecursorsFromSteps result loweredEnv auxRec allIndNames
        (types.map fun t => Lean.mkRecName t.name) entries ∧
      ∀ t ∈ types, ∃ (s t' : Environment)
        (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames t s t'),
        .inductInfo Hstep.restored.header.newInfo ∈ entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp [RecursorsFromSteps], by simp⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshExtensionRecursorSteps hwf with
      ⟨headEntries, Hhead, hhead, hheader⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail, htail, htailHeaders⟩
    refine ⟨headEntries ++ tailEntries, Hhead.append Htail, hhead.append htail, ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨_, _, Hstep, List.mem_append_left _ hheader⟩
    · obtain ⟨s, t', H', hmem⟩ := htailHeaders t ht
      exact ⟨s, t', H', List.mem_append_right _ hmem⟩

theorem FoldSteps.recursorFreshExtensionRecursorSteps
    (H : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv ∧
      RecursorsFromSteps result loweredEnv auxRec allIndNames names entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp [RecursorsFromSteps]⟩
  | @cons head src mid tl tgt Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh := find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hsteps⟩
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    have hhead : RecursorsFromSteps result loweredEnv auxRec allIndNames [head] [ci] := by
      intro e he r hr
      simp only [List.mem_singleton] at he
      subst he
      simp only [ci, ConstantInfo.recInfo.injEq] at hr
      subst hr
      exact ⟨_, List.mem_singleton_self _, _, _, Hstep, rfl⟩
    simpa using hhead.append hsteps

/-- Every recursor installed by a nested restoration is the restored
recursor of one of its steps. -/
theorem NestedRestorationFolds.freshExtensionRecursorSteps
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames ((), outEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries outEnv ∧
      RecursorsFromSteps result loweredEnv auxRec allIndNames
        (types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames) entries ∧
      ∀ t ∈ types, ∃ (s t' : Environment)
        (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames t s t'),
        .inductInfo Hstep.restored.header.newInfo ∈ entries := by
  rcases H.inductives.inductiveFreshExtensionRecursorSteps hwf with
    ⟨primaryEntries, Hprimary, hprimary, hheaders⟩
  rcases H.auxiliaries.recursorFreshExtensionRecursorSteps (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary, hauxiliary⟩
  refine ⟨_, Hprimary.append Hauxiliary, hprimary.append hauxiliary, ?_⟩
  intro t ht
  obtain ⟨s, t', Hstep, hmem⟩ := hheaders t ht
  exact ⟨s, t', Hstep, List.mem_append_left _ hmem⟩


end VerifyInductive
end Lean4Lean
