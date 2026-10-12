import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Environment.Checker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

/-! # Primitive-safe restoration folds

`FreshExtension` records the successful freshness checks performed by
nested restoration. The nested installation proof also needs the other
fact returned by the same `checkName`: when primitive declarations are not
allowed, every installed name is outside the kernel primitive table.
`FreshNonprimitiveExtension` records that fact alongside, without changing the
restoration fold structures.
-/

inductive FreshNonprimitiveExtension (allowPrimitive : Bool) :
    Environment → List ConstantInfo → Environment → Prop
  | nil : FreshNonprimitiveExtension allowPrimitive env [] env
  | cons :
      env.find? ci.name = none →
      (allowPrimitive = false →
        Kernel.Environment.primitives.contains ci.name = false) →
      FreshNonprimitiveExtension allowPrimitive (env.add ci) cis outEnv →
      FreshNonprimitiveExtension allowPrimitive env (ci :: cis) outEnv

theorem FreshNonprimitiveExtension.fresh
    (H : FreshNonprimitiveExtension allowPrimitive source entries target) :
    FreshExtension source entries target := by
  induction H with
  | nil => exact .nil
  | cons hfresh _ _ ih => exact .cons hfresh ih

theorem FreshNonprimitiveExtension.append
    (H₁ : FreshNonprimitiveExtension allowPrimitive source entries middle)
    (H₂ : FreshNonprimitiveExtension allowPrimitive middle rest target) :
    FreshNonprimitiveExtension allowPrimitive source (entries ++ rest)
      target := by
  induction H₁ with
  | nil => exact H₂
  | cons hfresh hnprim _ ih => exact .cons hfresh hnprim (ih H₂)

theorem FreshNonprimitiveExtension.nonprimitive
    (H : FreshNonprimitiveExtension false source entries target) :
    ∀ ci ∈ entries,
      ¬ Kernel.Environment.primitives.contains ci.name := by
  induction H with
  | nil => simp
  | cons _ hnprim _ ih =>
    intro ci hci
    rcases List.mem_cons.mp hci with rfl | htail
    · simp [hnprim rfl]
    · exact ih ci htail

/-- The header restoration step retains both results of its successful
`checkName`, not only map freshness. -/
theorem restoreInductiveHeaderDecl_primitiveSafe
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (indName : Name) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indName = some (.inductInfo oldInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
      allowPrimitive indName sourceEnv).WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  unfold Lean4Lean.restoreInductiveHeaderDecl
  simp only [hlookup]
  exact (checkName.WF hsourceWF oldInfo.name allowPrimitive).bind
    fun _ hname => by
      let ci : ConstantInfo :=
        .inductInfo { oldInfo with all := allIndNames }
      exact Except.WF.pure ⟨[ci], .cons hname.1 (by
        intro hallow
        change Kernel.Environment.primitives.contains oldInfo.name = false
        cases hprim : Kernel.Environment.primitives.contains oldInfo.name
        · rfl
        · have := hname.2 (by simp [hprim])
          simp [hallow] at this) .nil⟩

/-- Constructor restoration retains the primitive-safety result of its exact
successful `checkName`. -/
theorem restoreConstructorDecl_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (ctorName : Name) (oldInfo : ConstructorVal)
    (hlookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive ctorName
      sourceEnv).WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  unfold Lean4Lean.restoreConstructorDecl
  simp only [hlookup]
  exact (checkName.WF hsourceWF oldInfo.name allowPrimitive).bind
    fun _ hname => by
      let ci : ConstantInfo := .ctorInfo {
        oldInfo with type := result.restoreNested loweredEnv oldInfo.type }
      exact Except.WF.pure ⟨[ci], .cons hname.1 (by
        intro hallow
        change Kernel.Environment.primitives.contains oldInfo.name = false
        cases hprim : Kernel.Environment.primitives.contains oldInfo.name
        · rfl
        · have := hname.2 (by simp [hprim])
          simp [hallow] at this) .nil⟩

/-- Recursor restoration retains the primitive-safety result of its exact
successful `checkName`. -/
theorem restoreRecursorDecl_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool) (oldRecName : Name)
    (oldInfo : RecursorVal)
    (hlookup : loweredEnv.find? oldRecName = some (.recInfo oldInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
      allowPrimitive oldRecName sourceEnv).WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  unfold Lean4Lean.restoreRecursorDecl
  simp only [hlookup]
  let newRecName := auxRec.getD oldRecName oldRecName
  exact (checkName.WF hsourceWF newRecName allowPrimitive).bind
    fun _ hname => by
      let ci : ConstantInfo := .recInfo
        (result.restoreRecursor loweredEnv auxRec allIndNames oldRecName
          newRecName oldInfo)
      exact Except.WF.pure ⟨[ci], .cons hname.1 (by
        intro hallow
        change Kernel.Environment.primitives.contains newRecName = false
        cases hprim : Kernel.Environment.primitives.contains newRecName
        · rfl
        · have := hname.2 (by simp [hprim])
          simp [hallow] at this) .nil⟩

/-- Fold primitive-safe steps over the executable `forM`. -/
theorem stateForM_primitiveSafe
    {items : List α} {source : Environment} {allowPrimitive : Bool}
    (step : α → StateT Environment (Except Exception) Unit)
    (Hstep : ∀ item, item ∈ items → ∀ source,
      source.constants.WF →
      (step item source).WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive source
          entries out.2)
    (hsourceWF : source.constants.WF) :
    (items.forM step source).WF fun out =>
      ∃ entries, FreshNonprimitiveExtension allowPrimitive source
        entries out.2 := by
  induction items generalizing source with
  | nil => exact Except.WF.pure ⟨[], .nil⟩
  | cons head tail ih =>
    rw [List.forM]
    exact (Hstep head (by simp) source hsourceWF).bind fun headOut Hhead => by
      rcases headOut with ⟨done, middle⟩
      rcases done with ⟨⟩
      rcases Hhead with ⟨headEntries, Hhead⟩
      have hmiddleWF : middle.constants.WF :=
        Hhead.fresh.targetWF hsourceWF
      have Htail : ∀ item, item ∈ tail → ∀ source,
          source.constants.WF →
          (step item source).WF fun out =>
            ∃ entries, FreshNonprimitiveExtension allowPrimitive source
              entries out.2 := by
        intro item hitem
        exact Hstep item (by simp [hitem])
      exact (ih Htail hmiddleWF).mono fun tailOut HtailOut => by
        rcases HtailOut with ⟨tailEntries, HtailTrace⟩
        exact ⟨headEntries ++ tailEntries, Hhead.append HtailTrace⟩

theorem restoreConstructorDecls_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (ctorNames : List Name)
    (Hctors : ∀ ctorName, ctorName ∈ ctorNames →
      ∃ oldInfo : ConstructorVal,
        loweredEnv.find? ctorName = some (.ctorInfo oldInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (ctorNames.forM fun ctorName => Lean4Lean.restoreConstructorDecl result
      loweredEnv allowPrimitive ctorName) sourceEnv |>.WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  apply stateForM_primitiveSafe _ (items := ctorNames) (source := sourceEnv)
    (allowPrimitive := allowPrimitive) _ hsourceWF
  intro ctorName hctor stepSource hstepWF
  rcases Hctors ctorName hctor with ⟨oldInfo, hlookup⟩
  exact restoreConstructorDecl_primitiveSafe result loweredEnv stepSource
    allowPrimitive ctorName oldInfo hlookup hstepWF

theorem restoreRecursorDecls_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (recNames : List Name)
    (Hrecursors : ∀ recName, recName ∈ recNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (recNames.forM fun recName => Lean4Lean.restoreRecursorDecl result
      loweredEnv auxRec allIndNames allowPrimitive recName) sourceEnv |>.WF
        fun out =>
          ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
            entries out.2 := by
  apply stateForM_primitiveSafe _ (items := recNames) (source := sourceEnv)
    (allowPrimitive := allowPrimitive) _ hsourceWF
  intro recName hrec stepSource hstepWF
  rcases Hrecursors recName hrec with ⟨oldInfo, hlookup⟩
  exact restoreRecursorDecl_primitiveSafe result loweredEnv stepSource auxRec
    allIndNames allowPrimitive recName oldInfo hlookup hstepWF

/-- One complete source-family restoration retains primitive safety for its
header, constructor batch, and source recursor. -/
theorem restoreInductiveDecl_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (indType : InductiveType) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo))
    (Hctors : ∀ ctorName, ctorName ∈ oldInfo.ctors →
      ∃ ctorInfo : ConstructorVal,
        loweredEnv.find? ctorName = some (.ctorInfo ctorInfo))
    (recInfo : RecursorVal)
    (hrecLookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo recInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (Lean4Lean.restoreInductiveDecl result loweredEnv auxRec allIndNames
      allowPrimitive indType sourceEnv).WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  have Hheader := restoreInductiveHeaderDecl_primitiveSafe loweredEnv sourceEnv
    allIndNames allowPrimitive indType.name oldInfo hlookup hsourceWF
  have Hcombined :
      ((Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
          allowPrimitive indType.name sourceEnv).bind fun headerOut =>
        ((oldInfo.ctors.forM fun ctorName =>
          Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
            ctorName) headerOut.2).bind fun constructorOut =>
          Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
            allowPrimitive (Lean.mkRecName indType.name) constructorOut.2).WF
        fun out =>
          ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
            entries out.2 :=
    Hheader.bind fun headerOut HheaderOut => by
    rcases headerOut with ⟨done, headerEnv⟩
    rcases done with ⟨⟩
    rcases HheaderOut with ⟨headerEntries, HheaderTrace⟩
    have hheaderWF := HheaderTrace.fresh.targetWF hsourceWF
    have HconstructorFold := restoreConstructorDecls_primitiveSafe result
      loweredEnv headerEnv allowPrimitive oldInfo.ctors Hctors hheaderWF
    exact HconstructorFold.bind fun constructorOut HconstructorOut => by
      rcases constructorOut with ⟨done, constructorEnv⟩
      rcases done with ⟨⟩
      rcases HconstructorOut with
        ⟨constructorEntries, HconstructorTrace⟩
      have hconstructorWF := HconstructorTrace.fresh.targetWF hheaderWF
      have Hrecursor := restoreRecursorDecl_primitiveSafe result loweredEnv
        constructorEnv auxRec allIndNames allowPrimitive
        (Lean.mkRecName indType.name) recInfo hrecLookup hconstructorWF
      exact Hrecursor.mono fun recursorOut HrecursorOut => by
        rcases HrecursorOut with ⟨recursorEntries, HrecursorTrace⟩
        exact ⟨headerEntries ++ constructorEntries ++ recursorEntries,
          (HheaderTrace.append HconstructorTrace).append HrecursorTrace⟩
  simpa [Lean4Lean.restoreInductiveDecl, hlookup, bind, StateT.bind] using
    Hcombined

theorem restoreInductiveDecls_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo)) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (types.forM fun indType => Lean4Lean.restoreInductiveDecl result
      loweredEnv auxRec allIndNames allowPrimitive indType) sourceEnv |>.WF
        fun out =>
          ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
            entries out.2 := by
  apply stateForM_primitiveSafe _ (items := types) (source := sourceEnv)
    (allowPrimitive := allowPrimitive) _ hsourceWF
  intro indType hind stepSource hstepWF
  rcases Htypes indType hind with
    ⟨oldInfo, hlookup, Hctors, recInfo, hrecLookup⟩
  exact restoreInductiveDecl_primitiveSafe result loweredEnv stepSource auxRec
    allIndNames allowPrimitive indType oldInfo hlookup Hctors recInfo
      hrecLookup hstepWF

/-- The executable nested-restoration run yields a `FreshNonprimitiveExtension`:
its entries are fresh, and primitive-safe when `allowPrimitive = false`. -/
theorem restoreNestedDeclarations_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) (auxRecNames : List Name)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo)) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo))
    (Haux : ∀ recName, recName ∈ auxRecNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo))
    (hsourceWF : sourceEnv.constants.WF) :
    (Lean4Lean.restoreNestedDeclarations result loweredEnv auxRec allIndNames
      allowPrimitive types auxRecNames sourceEnv).WF fun out =>
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  have Hprimary := restoreInductiveDecls_primitiveSafe result loweredEnv
    sourceEnv auxRec allIndNames allowPrimitive types Htypes hsourceWF
  have Hcombined :
      (((types.forM fun indType => Lean4Lean.restoreInductiveDecl result
          loweredEnv auxRec allIndNames allowPrimitive indType) sourceEnv).bind
        fun primaryOut =>
          (auxRecNames.forM fun recName => Lean4Lean.restoreRecursorDecl result
            loweredEnv auxRec allIndNames allowPrimitive recName)
            primaryOut.2).WF fun out =>
              ∃ entries, FreshNonprimitiveExtension allowPrimitive
                sourceEnv entries out.2 :=
    Hprimary.bind fun primaryOut HprimaryOut => by
    rcases primaryOut with ⟨done, primaryEnv⟩
    rcases done with ⟨⟩
    rcases HprimaryOut with ⟨primaryEntries, HprimaryTrace⟩
    have hprimaryWF := HprimaryTrace.fresh.targetWF hsourceWF
    have Hauxiliary := restoreRecursorDecls_primitiveSafe result loweredEnv
      primaryEnv auxRec allIndNames allowPrimitive auxRecNames Haux hprimaryWF
    exact Hauxiliary.mono fun out HauxiliaryOut => by
      rcases HauxiliaryOut with ⟨auxiliaryEntries, HauxiliaryTrace⟩
      exact ⟨primaryEntries ++ auxiliaryEntries,
        HprimaryTrace.append HauxiliaryTrace⟩
  simpa [Lean4Lean.restoreNestedDeclarations, bind, StateT.bind] using Hcombined

/-- Both facts about one executable restoration run: its restoration folds
(`NestedRestorationFolds`) and its `FreshNonprimitiveExtension` share the same
`Except.ok` output, so the nested installation proof needs no caller-supplied
correspondence between their endpoints. -/
theorem restoreNestedDeclarations_refines_primitiveSafe
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) (auxRecNames : List Name)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type result.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type result.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs result.nparams)
    (Haux : ∀ recName, recName ∈ auxRecNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs result.nparams)
    (hsourceWF : sourceEnv.constants.WF) :
    (Lean4Lean.restoreNestedDeclarations result loweredEnv auxRec allIndNames
      allowPrimitive types auxRecNames sourceEnv).WF fun out =>
        Nonempty (NestedRestorationFolds result loweredEnv sourceEnv
          auxRec allIndNames types auxRecNames out) ∧
        ∃ entries, FreshNonprimitiveExtension allowPrimitive sourceEnv
          entries out.2 := by
  have Hrestored := restoreNestedDeclarations_refines result loweredEnv
    sourceEnv auxRec allIndNames allowPrimitive types auxRecNames Htypes Haux
  have Hprimitive := restoreNestedDeclarations_primitiveSafe result loweredEnv
    sourceEnv auxRec allIndNames allowPrimitive types auxRecNames
    (fun indType hind => by
      rcases Htypes indType hind with
        ⟨oldInfo, hlookup, Hctors, recInfo, hrecLookup, _Htype, _Hrules⟩
      exact ⟨oldInfo, hlookup,
        (fun ctorName hctor => by
          rcases Hctors ctorName hctor with ⟨ctorInfo, hctorLookup, _⟩
          exact ⟨ctorInfo, hctorLookup⟩), recInfo, hrecLookup⟩)
    (fun recName hrec => by
      rcases Haux recName hrec with ⟨oldInfo, hlookup, _Htype, _Hrules⟩
      exact ⟨oldInfo, hlookup⟩)
    hsourceWF
  intro out hout
  exact ⟨Hrestored out hout, Hprimitive out hout⟩

end VerifyInductive
end Lean4Lean
