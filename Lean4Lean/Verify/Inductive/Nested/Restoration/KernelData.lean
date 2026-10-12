import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Environment.Basic

/-! # The kernel constants of a restoration run

The restoration folds (`NestedRestorationFolds`, `Steps.lean`) read off as lists: the restored
headers with their constructors (`FoldSteps.inductiveInfos`, PR #43's `ivals`), the restored
recursors (`FoldSteps.inductiveRecs` for the source families, `FoldSteps.recursorInfos` for
the auxiliary recursors), the constants in the executable's insertion order
(`NestedRestorationFolds.entries`), the exact fresh extension
(`NestedRestorationFolds.freshExtensionExact`), the output map as an `insertConsts`
(`FreshExtension.map_eq`) and the permutation between the insertion order and PR #43's
stage order (`NestedRestorationFolds.entries_perm`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

variable {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
  {auxRec : NameMap Name} {allIndNames : List Name}

/-- The restored constructors of a constructor fold. -/
def FoldSteps.ctorInfos : ∀ {names : List Name} {sourceEnv targetEnv : Environment},
    FoldSteps (RestoredConstructorStep result loweredEnv) names sourceEnv targetEnv →
    List ConstructorVal
  | _, _, _, .nil => []
  | _, _, _, .cons h t => h.restored.newInfo :: FoldSteps.ctorInfos t

/-- The restored recursors of a recursor fold. -/
def FoldSteps.recursorInfos : ∀ {names : List Name} {sourceEnv targetEnv : Environment},
    FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names sourceEnv
      targetEnv → List RecursorVal
  | _, _, _, .nil => []
  | _, _, _, .cons h t => h.restored.newInfo :: FoldSteps.recursorInfos t

/-- The restored headers with their constructors of the family fold. -/
def FoldSteps.inductiveInfos : ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment},
    FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types sourceEnv
      targetEnv → List (InductiveVal × List ConstructorVal)
  | _, _, _, .nil => []
  | _, _, _, .cons h t =>
    (h.restored.header.newInfo, FoldSteps.ctorInfos h.restored.constructors) ::
      FoldSteps.inductiveInfos t

/-- The restored source recursors of the family fold. -/
def FoldSteps.inductiveRecs : ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment},
    FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types sourceEnv
      targetEnv → List RecursorVal
  | _, _, _, .nil => []
  | _, _, _, .cons h t => h.restored.recursor.restored.newInfo :: FoldSteps.inductiveRecs t

/-- The constants of the family fold in insertion order: per family, the header, its
constructors and its recursor. -/
def FoldSteps.inductiveEntries : ∀ {types : List InductiveType}
    {sourceEnv targetEnv : Environment},
    FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types sourceEnv
      targetEnv → List ConstantInfo
  | _, _, _, .nil => []
  | _, _, _, .cons h t =>
    (.inductInfo h.restored.header.newInfo ::
      (FoldSteps.ctorInfos h.restored.constructors).map .ctorInfo ++
      [.recInfo h.restored.recursor.restored.newInfo]) ++ FoldSteps.inductiveEntries t

theorem FreshExtension.castSource {e e' t : Environment} {l : List ConstantInfo} (h : e = e')
    (H : FreshExtension e l t) : FreshExtension e' l t := h ▸ H

theorem FreshExtension.castTarget {e t t' : Environment} {l : List ConstantInfo} (h : t = t')
    (H : FreshExtension e l t) : FreshExtension e l t' := h ▸ H

theorem FoldSteps.ctorFreshExact {names : List Name} {sourceEnv targetEnv : Environment}
    (H : FoldSteps (RestoredConstructorStep result loweredEnv) names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    FreshExtension sourceEnv (H.ctorInfos.map .ctorInfo) targetEnv := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail ih =>
    have hfresh := find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    exact .cons hfresh (FreshExtension.castSource htarget
      (ih (htarget ▸ constantsWF_add_checked hwf hfresh)))

theorem FoldSteps.recursorFreshExact {names : List Name} {sourceEnv targetEnv : Environment}
    (H : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names
      sourceEnv targetEnv) (hwf : sourceEnv.constants.WF) :
    FreshExtension sourceEnv (H.recursorInfos.map .recInfo) targetEnv := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail ih =>
    have hfresh := find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    exact .cons hfresh (FreshExtension.castSource htarget
      (ih (htarget ▸ constantsWF_add_checked hwf hfresh)))

theorem FoldSteps.inductiveFreshExact {types : List InductiveType}
    {sourceEnv targetEnv : Environment}
    (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
      sourceEnv targetEnv) (hwf : sourceEnv.constants.WF) :
    FreshExtension sourceEnv H.inductiveEntries targetEnv := by
  induction H with
  | nil => exact .nil
  | @cons indType sourceEnv middleEnv types targetEnv Hstep Htail ih =>
    let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
    have hheaderEnv : Hstep.restored.headerEnv = sourceEnv.add header :=
      congrArg Prod.snd Hstep.restored.header.output
    have hheaderFresh : sourceEnv.find? header.name = none :=
      find?_none_of_contains_false hwf Hstep.restored.header.fresh
    have hwfHeader := constantsWF_add_checked hwf hheaderFresh
    have hwfHeader' : Hstep.restored.headerEnv.constants.WF := by
      rw [hheaderEnv]; exact hwfHeader
    have Hctors := FoldSteps.ctorFreshExact Hstep.restored.constructors hwfHeader'
    have hwfCtors := Hctors.targetWF hwfHeader'
    let recursor : ConstantInfo := .recInfo Hstep.restored.recursor.restored.newInfo
    have hmid : middleEnv = Hstep.restored.constructorEnv.add recursor :=
      congrArg Prod.snd Hstep.restored.recursor.restored.output
    have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name = none :=
      find?_none_of_contains_false hwfCtors Hstep.restored.recursor.restored.fresh
    have Hhead : FreshExtension sourceEnv
        (header :: (FoldSteps.ctorInfos Hstep.restored.constructors).map .ctorInfo ++
          [recursor]) middleEnv := by
      refine .cons hheaderFresh (FreshExtension.castTarget hmid.symm ?_)
      exact FreshExtension.castSource hheaderEnv (Hctors.append (.cons hrecFresh .nil))
    exact Hhead.append (ih (Hhead.targetWF hwf))

/-- The constants of a restoration run in insertion order. -/
def NestedRestorationFolds.entries {types : List InductiveType} {auxRecNames : List Name}
    {sourceEnv : Environment} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) : List ConstantInfo :=
  H.inductives.inductiveEntries ++ H.auxiliaries.recursorInfos.map .recInfo

theorem NestedRestorationFolds.freshExtensionExact {types : List InductiveType}
    {auxRecNames : List Name} {sourceEnv : Environment} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) (hwf : sourceEnv.constants.WF) : FreshExtension sourceEnv H.entries out.2 := by
  have H1 := H.inductives.inductiveFreshExact hwf
  exact H1.append (H.auxiliaries.recursorFreshExact (H1.targetWF hwf))

/-- A fresh extension inserts its entries into the constant map. -/
theorem FreshExtension.map_eq {env outEnv : Environment} {entries : List ConstantInfo}
    (H : FreshExtension env entries outEnv) :
    outEnv.constants = insertConsts env.constants entries := by
  induction H with
  | nil => rfl
  | cons _ _ ih => rw [ih, insertConsts_cons]; rfl

/-- The restored headers with constructors of the run. -/
abbrev NestedRestorationFolds.ivals {types : List InductiveType} {auxRecNames : List Name}
    {sourceEnv : Environment} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) : List (InductiveVal × List ConstructorVal) :=
  H.inductives.inductiveInfos

/-- The restored recursors of the run: the source recursors, then the auxiliary ones. -/
abbrev NestedRestorationFolds.rvals {types : List InductiveType} {auxRecNames : List Name}
    {sourceEnv : Environment} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) : List RecursorVal :=
  H.inductives.inductiveRecs ++ H.auxiliaries.recursorInfos

private theorem perm_interleave {α : Type _} :
    ∀ (l : List (α × List α × α)),
      (l.flatMap fun x => x.1 :: x.2.1 ++ [x.2.2]) ~
        l.map (·.1) ++ l.flatMap (·.2.1) ++ l.map (·.2.2)
  | [] => by simp
  | x :: l => by
    have ih := perm_interleave l
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.append_assoc]
    refine List.Perm.cons _ ?_
    have h1 : x.2.1 ++ [x.2.2] ++ List.flatMap (fun x => x.1 :: x.2.1 ++ [x.2.2]) l ~
        x.2.1 ++ [x.2.2] ++ (l.map (·.1) ++ l.flatMap (·.2.1) ++ l.map (·.2.2)) :=
      List.Perm.append_left _ ih
    simp only [List.append_assoc, List.singleton_append] at h1
    refine h1.trans ?_
    have h2 : x.2.2 :: (l.map (·.1) ++ (l.flatMap (·.2.1) ++ l.map (·.2.2))) ~
        l.map (·.1) ++ (l.flatMap (·.2.1) ++ x.2.2 :: l.map (·.2.2)) := by
      have := (List.perm_middle (a := x.2.2) (l₁ := l.map (·.1) ++ l.flatMap (·.2.1))
        (l₂ := l.map (·.2.2)))
      simpa only [List.append_assoc] using this.symm
    refine (List.Perm.append_left _ h2).trans ?_
    rw [← List.append_assoc, ← List.append_assoc x.2.1]
    have h3 : x.2.1 ++ l.map (·.1) ~ l.map (·.1) ++ x.2.1 := List.perm_append_comm
    have := List.Perm.append_right (l.flatMap (·.2.1) ++ x.2.2 :: l.map (·.2.2)) h3
    simpa only [List.append_assoc] using this

theorem FoldSteps.inductiveEntries_perm :
    ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv),
      H.inductiveEntries ~ H.inductiveInfos.map (.inductInfo ·.1) ++
        H.inductiveInfos.flatMap (·.2.map .ctorInfo) ++ H.inductiveRecs.map .recInfo := by
  intro types sourceEnv targetEnv H
  let toTriple : ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment},
      FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv → List (ConstantInfo × List ConstantInfo × ConstantInfo) :=
    fun H => (H.inductiveInfos.zip H.inductiveRecs).map fun p =>
      (.inductInfo p.1.1, p.1.2.map .ctorInfo, .recInfo p.2)
  have key : ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv),
      H.inductiveEntries = (toTriple H).flatMap (fun x => x.1 :: x.2.1 ++ [x.2.2]) ∧
      (toTriple H).map (·.1) = H.inductiveInfos.map (.inductInfo ·.1) ∧
      (toTriple H).flatMap (·.2.1) = H.inductiveInfos.flatMap (·.2.map .ctorInfo) ∧
      (toTriple H).map (·.2.2) = H.inductiveRecs.map .recInfo := by
    intro types sourceEnv targetEnv H
    induction H with
    | nil => simp [toTriple, FoldSteps.inductiveEntries, FoldSteps.inductiveInfos,
        FoldSteps.inductiveRecs]
    | cons h t ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      simp only [toTriple] at h1 h2 h3 h4 ⊢
      simp [FoldSteps.inductiveEntries, FoldSteps.inductiveInfos, FoldSteps.inductiveRecs,
        h1, h2, h3, h4]
  obtain ⟨h1, h2, h3, h4⟩ := key H
  rw [h1, ← h2, ← h3, ← h4]
  exact perm_interleave _

/-- The insertion order is a permutation of PR #43's stage order (`AddInduct.consts`). -/
theorem NestedRestorationFolds.entries_perm {types : List InductiveType}
    {auxRecNames : List Name} {sourceEnv : Environment} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) : H.entries ~ AddInduct.consts H.ivals H.rvals := by
  unfold NestedRestorationFolds.entries AddInduct.consts
  refine (List.Perm.append_right _ (H.inductives.inductiveEntries_perm)).trans ?_
  simp only [List.map_append, List.append_assoc, NestedRestorationFolds.ivals,
    NestedRestorationFolds.rvals]
  exact List.Perm.refl _

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- The kernel side of a restoration run in the form of PR #43's `AddInduct`: the run's
constants in insertion order, a permutation of the stage order, fresh in the source map, and
inserted into it to give the output map. -/
theorem NestedRestorationFolds.kernelOrder {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceEnv outEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {types : List InductiveType} {auxRecNames : List Name}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      ((), outEnv)) (hwf : sourceEnv.constants.WF) :
    H.entries.Perm (AddInduct.consts H.ivals H.rvals) ∧
      (∀ ci ∈ AddInduct.consts H.ivals H.rvals, sourceEnv.constants.find? ci.name = none) ∧
      outEnv.constants = insertConsts sourceEnv.constants H.entries ∧
      outEnv.quotInit = sourceEnv.quotInit := by
  have Hfresh := H.freshExtensionExact hwf
  refine ⟨H.entries_perm, fun ci hci => ?_, Hfresh.map_eq, Hfresh.quotInit_eq⟩
  have h := Hfresh.sourceFresh hwf ((H.entries_perm).mem_iff.mpr hci)
  rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at h

end VerifyInductive
end Lean4Lean
