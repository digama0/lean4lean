import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshExtensions
import Lean4Lean.Verify.Inductive.Recursor.Entries.AddConstants

/-! Fresh extensions of a kernel environment: their lookups, and independence of
the kernel lookups and the local checking invariants from the insertion order. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Every lookup introduced by a fresh extension is one of its exact
entries; all other lookups come from the source environment. -/
theorem FreshExtension.entryOrigin
    (H : FreshExtension source entries target)
    (hsourceWF : source.constants.WF)
    (hfind : target.find? name = some found) :
    source.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.name ∧ found = entry := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hfresh Htail ih =>
    rename_i rest out env ci
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
        at hfresh
    have hnextWF : (env.add ci).constants.WF :=
      constantsWF_add_checked hsourceWF hfresh
    rcases ih hnextWF hfind with hnext | ⟨entry, hentry, hname, hfound⟩
    · change (env.add ci).constants.find?' name = some found at hnext
      rw [hnextWF.find?'_eq_find?] at hnext
      change (env.constants.insert ci.name ci).find? name = some found at hnext
      rw [hsourceWF.find?_insert] at hnext
      split at hnext
      · rename_i heq
        right
        simp only [Option.some.injEq] at hnext
        exact ⟨ci, by simp, (LawfulBEq.eq_of_beq heq).symm, hnext.symm⟩
      · left
        rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
    · exact Or.inr ⟨entry, by simp [hentry], hname, hfound⟩

/-- Every exact entry of a fresh extension is present in the target
environment with unchanged metadata. -/
theorem FreshExtension.findEntry
    (H : FreshExtension source entries target)
    (hsourceWF : source.constants.WF)
    (hentry : info ∈ entries) :
    target.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hfresh Htail ih =>
    rename_i rest out env ci
    simp only [List.mem_cons] at hentry
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
        at hfresh
    have hnextWF : (env.add ci).constants.WF :=
      constantsWF_add_checked hsourceWF hfresh
    rcases hentry with hhead | htail
    · have hinfo : info = ci := hhead
      subst info
      apply Htail.preservesSourceFind hnextWF
      change (env.constants.insert ci.name ci).find?' ci.name = some ci
      rw [(hsourceWF.insert ci.name ci hfreshMap).find?'_eq_find?,
        hsourceWF.find?_insert]
      simp
    · exact ih hnextWF htail

/-- Fresh insertion order is irrelevant to kernel lookups.
This is deliberately an extensional statement: the two `SMap`
representations need not be propositionally equal. -/
theorem FreshExtension.lookupEqOfPerm
    (Hleft : FreshExtension source leftEntries leftTarget)
    (Hright : FreshExtension source rightEntries rightTarget)
    (hsourceWF : source.constants.WF)
    (hperm : leftEntries ~ rightEntries) :
    ∀ name, leftTarget.constants.find? name =
      rightTarget.constants.find? name := by
  intro name
  have hleftWF := Hleft.targetWF hsourceWF
  have hrightWF := Hright.targetWF hsourceWF
  have forward : ∀ {found},
      leftTarget.constants.find? name = some found →
      rightTarget.constants.find? name = some found := by
    intro found hfind
    have hfindEnv : leftTarget.find? name = some found := by
      rw [Lean.Kernel.Environment.find?, hleftWF.find?'_eq_find?]
      exact hfind
    rcases Hleft.entryOrigin hsourceWF hfindEnv with hold | hnew
    · have htarget := Hright.preservesSourceFind hsourceWF hold
      rwa [Lean.Kernel.Environment.find?, hrightWF.find?'_eq_find?]
        at htarget
    · rcases hnew with ⟨entry, hentry, hname, hfound⟩
      subst found
      subst name
      have hentry' : entry ∈ rightEntries := hperm.mem_iff.mp hentry
      have htarget := Hright.findEntry hsourceWF hentry'
      rwa [Lean.Kernel.Environment.find?, hrightWF.find?'_eq_find?]
        at htarget
  have backward : ∀ {found},
      rightTarget.constants.find? name = some found →
      leftTarget.constants.find? name = some found := by
    intro found hfind
    have hfindEnv : rightTarget.find? name = some found := by
      rw [Lean.Kernel.Environment.find?, hrightWF.find?'_eq_find?]
      exact hfind
    rcases Hright.entryOrigin hsourceWF hfindEnv with hold | hnew
    · have htarget := Hleft.preservesSourceFind hsourceWF hold
      rwa [Lean.Kernel.Environment.find?, hleftWF.find?'_eq_find?]
        at htarget
    · rcases hnew with ⟨entry, hentry, hname, hfound⟩
      subst found
      subst name
      have hentry' : entry ∈ leftEntries := hperm.mem_iff.mpr hentry
      have htarget := Hleft.findEntry hsourceWF hentry'
      rwa [Lean.Kernel.Environment.find?, hleftWF.find?'_eq_find?]
        at htarget
  cases hleft : leftTarget.constants.find? name with
  | none =>
    cases hright : rightTarget.constants.find? name with
    | none => rfl
    | some found =>
      have := backward hright
      rw [hleft] at this
      contradiction
  | some found =>
    exact (forward hleft).symm

/-- Rebase a checking environment across an exact extensional change of its
kernel constant-map representation. -/
theorem CheckingEnv.mapExt
    (H : CheckingEnv safety source venv)
    (htargetWF : target.constants.WF)
    (heq : ∀ name, source.constants.find? name =
      target.constants.find? name) :
    CheckingEnv safety target venv where
  aligned := H.aligned.mapExt htargetWF heq
  wf := H.wf
  of_value := by
    intro name ci value hfind hs hvalue
    have hfindTarget : target.constants.find? name = some ci := by
      rw [← htargetWF.find?'_eq_find?, ← Lean.Kernel.Environment.find?]
      exact hfind
    have hfindSource : source.constants.find? name = some ci := by
      rw [heq]
      exact hfindTarget
    have hfindSource' : source.find? name = some ci := by
      rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?]
      exact hfindSource
    exact H.of_value hfindSource' hs hvalue

/-- The local checking invariants depend only on the lookups of the kernel
environment's constant map. -/
theorem CheckingEnv.ValidCore.mapExt
    (H : CheckingEnv.ValidCore safety source venv)
    (htargetWF : target.constants.WF)
    (heq : ∀ name, source.constants.find? name =
      target.constants.find? name) :
    CheckingEnv.ValidCore safety target venv where
  tr := CheckingEnv.mapExt H.tr htargetWF heq
  hasPrimitives := H.hasPrimitives
  safePrimitives := by
    intro name ci hfind hprimitive
    have hfindTarget : target.constants.find? name = some ci := by
      rw [← htargetWF.find?'_eq_find?,
        ← Lean.Kernel.Environment.find?]
      exact hfind
    have hfindSource : source.constants.find? name = some ci := by
      rw [heq]
      exact hfindTarget
    apply H.safePrimitives _ hprimitive
    rw [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?]
    exact hfindSource

/-- Forget the typing part of a lockstep installation (`AddConstants`) while
retaining its fresh extension. -/
theorem AddConstants.freshExtension
    (H : AddConstants safety source sourceVEnv entries target targetVEnv) :
    FreshExtension source (entries.map Prod.fst) target := by
  induction H with
  | nil => exact .nil
  | cons hfresh _ _ _ _ _ _ ih => exact .cons hfresh ih

end VerifyInductive
end Lean4Lean
