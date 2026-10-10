import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Header.RawTranslation
import Lean4Lean.Verify.Inductive.Header.Translation

/-! Raw constructor targets: the abstract constructor constants produced by the
executable's `checkClosedType` calls, accumulated in source order over the
mutual constructor matrix (`RawCtorTranslations`, `RawBlockCtorTranslations`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Ordered raw abstract constructor targets for one source family.  This is
the constructor-side counterpart of `RawHeaderTranslations`: target
constants are outputs of the executable closed-type checks, not inputs
chosen by a declaration skeleton. -/
structure RawCtorTranslations (env : VEnv) (Us : List Name)
    (sources : List Constructor) where
  targets : List VConstVal
  translations : List.Forall₂
    (fun source target =>
      TrSourceConstRaw env Us source.name source.type target)
    sources targets

namespace RawCtorTranslations

def empty (env : VEnv) (Us : List Name) :
    RawCtorTranslations env Us [] where
  targets := []
  translations := .nil

def snoc (H : RawCtorTranslations env Us sources)
    (source : Constructor) (target : VConstVal)
    (Htarget : TrSourceConstRaw env Us source.name source.type target) :
    RawCtorTranslations env Us (sources ++ [source]) where
  targets := H.targets ++ [target]
  translations := List.Forall₂.append'
    H.translations (.cons Htarget .nil)

end RawCtorTranslations

/-- Two-dimensional, source-aligned raw constructor targets for a prefix of
the mutual family list. -/
structure RawBlockCtorTranslations (env : VEnv) (Us : List Name)
    (sources : List InductiveType) where
  targets : List (List VConstVal)
  translations : List.Forall₂
    (fun source targets => List.Forall₂
      (fun ctor target =>
        TrSourceConstRaw env Us ctor.name ctor.type target)
      source.ctors targets)
    sources targets

namespace RawBlockCtorTranslations

def empty (env : VEnv) (Us : List Name) :
    RawBlockCtorTranslations env Us [] where
  targets := []
  translations := .nil

def snoc (H : RawBlockCtorTranslations env Us sources)
    (source : InductiveType)
    (row : RawCtorTranslations env Us source.ctors) :
    RawBlockCtorTranslations env Us (sources ++ [source]) where
  targets := H.targets ++ [row.targets]
  translations := List.Forall₂.append'
    H.translations (.cons row.translations .nil)

end RawBlockCtorTranslations

/-- Assemble metadata-free family targets from independently accumulated
header constants and constructor rows. -/
def assembleInductiveSkeletonTypes (headers : List VConstVal)
    (constructors : List (List VConstVal)) : List VInductiveTypeSkeleton :=
  List.zipWith (fun header ctors => {
    toVConstVal := header
    ctors := ctors }) headers constructors

theorem assembleInductiveSkeletonTypes_translated
    {sources : List InductiveType} {headers : List VConstVal}
    {constructors : List (List VConstVal)}
    (Hheaders : List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      sources headers)
    (Hconstructors : List.Forall₂
      (fun source targets => List.Forall₂
        (fun ctor target =>
          TrSourceConstRaw envTypes Us ctor.name ctor.type target)
        source.ctors targets)
      sources constructors) :
    List.Forall₂ (fun source target => ∀ numIndices resultLevel,
        TrInductiveTypeHeaders env envTypes Us source
          (target.toVInductiveType numIndices resultLevel))
      sources (assembleInductiveSkeletonTypes headers constructors) := by
  induction Hheaders generalizing constructors with
  | nil =>
      cases Hconstructors
      exact .nil
  | cons Hheader Hheaders ih =>
      cases Hconstructors with
      | cons Hctors Hconstructors =>
        exact .cons (fun _ _ => ⟨Hheader, Hctors⟩) (ih Hconstructors)

theorem assembleInductiveSkeletonTypes_headers
    {sources : List InductiveType} {headers : List VConstVal}
    {constructors : List (List VConstVal)}
    (Hheaders : List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      sources headers)
    (Hconstructors : List.Forall₂
      (fun source targets => List.Forall₂
        (fun ctor target =>
          TrSourceConstRaw envTypes Us ctor.name ctor.type target)
        source.ctors targets)
      sources constructors) :
    (assembleInductiveSkeletonTypes headers constructors).map
      VInductiveTypeSkeleton.toVConstVal = headers := by
  have hlength : constructors.length = headers.length := by
    rw [← List.Forall₂.length_eq Hconstructors,
      List.Forall₂.length_eq Hheaders]
  have go : ∀ (hs : List VConstVal) (cs : List (List VConstVal)),
      cs.length = hs.length →
      (assembleInductiveSkeletonTypes hs cs).map
        VInductiveTypeSkeleton.toVConstVal = hs := by
    intro hs
    induction hs with
    | nil =>
        intro cs hlen
        have : cs = [] := List.eq_nil_of_length_eq_zero hlen
        subst cs
        rfl
    | cons header headers ih =>
        intro cs hlen
        cases cs with
        | nil => simp at hlen
        | cons ctors constructors =>
          have hlen' : constructors.length = headers.length := by
            simpa using Nat.succ.inj hlen
          change header ::
            (assembleInductiveSkeletonTypes headers constructors).map
              VInductiveTypeSkeleton.toVConstVal = header :: headers
          rw [ih constructors hlen']
  exact go headers constructors hlength

namespace checkConstructors.loopCtors

/-- One constructor iteration extends an existentially built raw-target row.
The semantic `loopCtor` proof remains with the caller, but its target
translation is the one produced by this very `checkClosedType` call. -/
theorem stepPrefix.accumulatesRawTargets
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {targetIdx ctorIdx : Nat}
    {ctors : List Constructor} {foundCtors : NameSet}
    {sources : List Constructor} {Q : List (List Bool) → Prop}
    (Hc : ContextWF c)
    (Hprefix : RawCtorTranslations
      Hc.venv c.lparams sources)
    (hidx : ctorIdx < ctors.length)
    (Hloop : ∀ checkedType,
      (Hchecked : ClosedHeaderCheck Hc
        ctors[ctorIdx].name ctors[ctorIdx].type checkedType) →
      RawCtorTranslations Hc.venv c.lparams
        (sources ++ [ctors[ctorIdx]]) →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun fields =>
          (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
            ctors (ctorIdx + 1)
            (foundCtors.insert ctors[ctorIdx].name) c).WF fun rest =>
              Q (fields :: rest)) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
  cases hfresh : foundCtors.contains ctors[ctorIdx].name with
  | true =>
      simp only [↓reduceIte]
      exact Except.WF.throw
  | false =>
      rw [if_neg (by simp)]
      change (AddInductive.checkClosedType ctors[ctorIdx].name
        ctors[ctorIdx].type c >>= fun _ => ((do
          let _ ← readThe AddInductive.Context
          let fields ← AddInductive.checkConstructors.loopCtor stats isUnsafe
            ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
            c.fuel.inductiveFuel
          return fields :: (← AddInductive.checkConstructors.loopCtors stats isUnsafe
            targetIdx ctors (ctorIdx + 1)
            (foundCtors.insert ctors[ctorIdx].name))) :
          AddInductive.M (List (List Bool))) c).WF Q
      exact (checkClosedType.rawSourceTranslationWF Hc).bind
        fun checkedType hchecked => by
          rcases hchecked with ⟨Hchecked⟩
          change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
            ((AddInductive.checkConstructors.loopCtor stats isUnsafe
                ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
                c'.fuel.inductiveFuel >>= fun fields => do
              return fields :: (← AddInductive.checkConstructors.loopCtors stats isUnsafe
                targetIdx ctors (ctorIdx + 1)
                (foundCtors.insert ctors[ctorIdx].name))) :
              AddInductive.M (List (List Bool))) c).WF Q
          have hread : ((read : AddInductive.M AddInductive.Context) c).WF
              (fun c' => c' = c) := by
            intro c' h
            cases h
            rfl
          refine hread.bind fun c' hc' => ?_
          subst c'
          exact (Hloop checkedType Hchecked
            (Hprefix.snoc ctors[ctorIdx] Hchecked.target
              Hchecked.source)).bind fun _ hnext =>
                hnext.bind fun _ hrest => Except.WF.pure hrest

/-- Traverse one complete constructor list while existentially retaining its
raw abstract targets in exact source order. -/
theorem accumulatesRawTargets
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {targetIdx ctorIdx : Nat}
    {ctors : List Constructor} {foundCtors : NameSet}
    {Q : List (List Bool) → Prop}
    (Hc : ContextWF c)
    (Hprefix : RawCtorTranslations Hc.venv c.lparams
      (ctors.take ctorIdx))
    (Hcheck : ∀ i (hi : i < ctors.length) checkedType,
      (Hchecked : ClosedHeaderCheck Hc
        ctors[i].name ctors[i].type checkedType) →
      ∀ (R : List Bool → Prop), (∀ fields, R fields) →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[i].name targetIdx ctors[i].type 0
        c.fuel.inductiveFuel c).WF R)
    (Hfinish : RawCtorTranslations Hc.venv c.lparams
      ctors → ∀ out, Q out) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < ctors.length
  · apply stepPrefix.accumulatesRawTargets
      (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
      (foundCtors := foundCtors) (Q := Q) Hc Hprefix hidx
    intro checkedType Hchecked Hprefix'
    have Hnext : RawCtorTranslations Hc.venv c.lparams
        (ctors.take (ctorIdx + 1)) := by
      rw [List.take_succ_eq_append_getElem hidx]
      exact Hprefix'
    apply Hcheck ctorIdx hidx checkedType Hchecked
    intro fields
    exact accumulatesRawTargets (Q := fun rest => Q (fields :: rest)) Hc Hnext Hcheck
      (fun h rest => Hfinish h _)
  · apply result.WF (Q := Q) hidx
    have htake : ctors.take ctorIdx = ctors :=
      List.take_of_length_le (Nat.le_of_not_gt hidx)
    exact Hfinish (by simpa [htake] using Hprefix) _
termination_by ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

/-- Traverse the complete mutual constructor matrix without a caller-chosen
constructor skeleton.  Each row is generated by the corresponding
`checkClosedType` calls and the result preserves the executable's family and
constructor order exactly. -/
theorem accumulatesRawTargets
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {indTypes : Array InductiveType}
    {targetIdx : Nat} {Q : List (List (List Bool)) → Prop}
    (Hc : ContextWF c)
    (Hrows : RawBlockCtorTranslations Hc.venv c.lparams
      (indTypes.toList.take targetIdx))
    (Hcheck : ∀ familyIdx (hfamily : familyIdx < indTypes.size)
      ctorIdx (hctor : ctorIdx < indTypes[familyIdx].ctors.length)
      checkedType,
      (Hchecked : ClosedHeaderCheck Hc
        indTypes[familyIdx].ctors[ctorIdx].name
        indTypes[familyIdx].ctors[ctorIdx].type checkedType) →
      ∀ (R : List Bool → Prop), (∀ fields, R fields) →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[familyIdx].ctors[ctorIdx].name familyIdx
        indTypes[familyIdx].ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF R)
    (Hfinish : RawBlockCtorTranslations Hc.venv c.lparams
      indTypes.toList → ∀ out, Q out) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.accumulatesRawTargets
      (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
      (ctors := indTypes[targetIdx].ctors) (ctorIdx := 0)
      (foundCtors := {})
      (Q := fun fields =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF fun rest => Q (fields :: rest))
      Hc (by
        change RawCtorTranslations Hc.venv c.lparams []
        exact RawCtorTranslations.empty Hc.venv c.lparams)
    · intro ctorIdx hctor checkedType Hchecked R hR
      exact Hcheck targetIdx hidx ctorIdx hctor checkedType Hchecked R hR
    · intro Hrow fields
      have Hrows' : RawBlockCtorTranslations Hc.venv c.lparams
          (indTypes.toList.take (targetIdx + 1)) := by
        rw [List.take_succ_eq_append_getElem (by simpa using hidx)]
        exact Hrows.snoc indTypes[targetIdx] Hrow
      exact accumulatesRawTargets (Q := fun rest => Q (fields :: rest)) Hc Hrows' Hcheck
        (fun h rest => Hfinish h _)
  · apply result.WF (Q := Q) hidx
    have htake : indTypes.toList.take targetIdx = indTypes.toList :=
      List.take_of_length_le (by simpa using Nat.le_of_not_gt hidx)
    exact Hfinish (by simpa [htake] using Hrows) _
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

end VerifyInductive
end Lean4Lean
