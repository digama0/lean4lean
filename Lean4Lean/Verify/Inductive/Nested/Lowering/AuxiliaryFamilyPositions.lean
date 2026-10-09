import Lean4Lean.Verify.Inductive.Nested.Lowering.Queue

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Positions of the auxiliary families in the lowering queue

Formation needs to know that every slot of the final lowering queue
strictly after the initial source block holds an auxiliary family produced by an actual
auxiliary generation step (`AuxiliaryFamilySpecialization`) and then lowered
(`LoweredAuxiliaryFamily`, `NestedLowering.resolvedAuxiliaryFamilyAt`), and that every entry
of the final auxiliary cache points to such a slot (`NestedLowering.cachedAuxiliaryFamily`).
These facts are carried as queue invariants rather than inferred from equality of family
values.
-/

/-- Positions of the entries of the append-only auxiliary cache.  Every
cache entry is paired with the generated-family queue slot that introduced its
fresh name.  The slot's family may later be lowered in place, but family-level
lowering preserves its name, so the position remains stable throughout the
queue run. -/
structure AuxiliaryCachePositions
    (initialSize : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  size : initialSize ≤ state.newTypes.size
  position : ∀ nested auxName, (nested, auxName) ∈ state.nestedAux →
    ∃ j, ∃ hj : j < state.newTypes.size,
      initialSize ≤ j ∧ state.newTypes[j].name = auxName

theorem AuxiliaryGenerationStep.familyPositions
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  constructor
  · simp only [Array.size_push]
    exact Nat.le_trans Hpositions.size (Nat.le_succ _)
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · rcases Hpositions.position nested name hold with
        ⟨j, hj, hinitial, hname⟩
      refine ⟨j, ?_, hinitial, ?_⟩
      · simp only [Array.size_push]
        omega
      simpa [Array.getElem_push, hj] using hname
    · cases hnew
      refine ⟨state.newTypes.size, by simp, Hpositions.size, ?_⟩
      simpa [Array.getElem_push] using Hbuilt.name

theorem AuxiliaryGenerationBatch.familyPositions
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  induction H with
  | nil => exact Hpositions
  | cons Hstep Htail ih => exact ih (Hstep.familyPositions Hpositions)

theorem OccurrenceReplacement.familyPositions
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  cases H with
  | cached => exact Hpositions
  | generated _ Hbatch => exact Hbatch.familyPositions Hpositions

theorem NodeReplacement.familyPositions
    (H : NodeReplacement env lctx params As input state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  cases H with
  | unrecognized => exact Hpositions
  | recognized _ _ Hrecognized =>
    exact Hrecognized.familyPositions Hpositions

theorem ExprLowering.familyPositions
    (H : ExprLowering env lctx params As input state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  induction H with
  | occurrence Hnode => exact Hnode.familyPositions Hpositions
  | bvar | fvar | mvar | sort | const | lit => exact Hpositions
  | app Hnode _ _ ihFn ihArg =>
    exact ihArg (ihFn (Hnode.familyPositions Hpositions))
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact ihBody (ihDom (Hnode.familyPositions Hpositions))
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.familyPositions Hpositions)))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact ihBody (Hnode.familyPositions Hpositions)

theorem ConstructorLowering.familyPositions
    (H : ConstructorLowering env params nparams source state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _Hopening, _Hbinding,
      _Hselection, _hnodup, hopenedTypes, hopenedAux, _hopenedNext, _hsize,
      Hreplace, _htype⟩
  have Hopened : AuxiliaryCachePositions initialSize openedState := by
    constructor
    · simpa [hopenedTypes] using Hpositions.size
    · intro nested name hentry
      have hentryState : (nested, name) ∈ state.nestedAux := by
        simpa [hopenedAux] using hentry
      rcases Hpositions.position nested name hentryState with
        ⟨j, hj, hinitial, hname⟩
      refine ⟨j, ?_, hinitial, ?_⟩
      · simpa [hopenedTypes] using hj
      · simpa [hopenedTypes] using hname
  exact Hreplace.familyPositions Hopened

theorem ConstructorLowerings.familyPositions
    (H : ConstructorLowerings env params nparams sources state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  induction H with
  | nil => exact Hpositions
  | cons Hhead Htail ih => exact ih (Hhead.familyPositions Hpositions)

theorem FamilyLowering.familyPositions
    (H : FamilyLowering env params nparams source state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 :=
  H.constructors.familyPositions Hpositions

/-- Every pending queue slot in the generated suffix carries the exact
`AuxiliaryFamilySpecialization` that appended it. -/
def PendingGeneratedFamilyOrigins
    (env : Environment) (params : Array Expr) (initialSize cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, initialSize ≤ j → cursor ≤ j →
    (hj : j < state.newTypes.size) →
    Nonempty (AuxiliaryFamilySpecialization env params state.nestedAux
      state.newTypes[j])

theorem AuxiliaryGenerationStep.pendingGeneratedFamilyOrigins
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hselection : CDeclArray lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hnparams : nparams ≤ args.size)
    (hsourceParams : nparams = sourceInfo.numParams)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args, arg.FVarsIn (· ∈ Hselection.fvars))
    (HargsClosed : ∀ i, i < nparams → args[i]!.hasLooseBVars = false)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  intro j hinitial hcursor hj
  simp only [Array.size_push] at hj
  by_cases hold : j < state.newTypes.size
  · rcases Horigins j hinitial hcursor hold with ⟨Horigin⟩
    refine ⟨{ Horigin with
      family_eq := by
        simpa [Array.getElem_push, hold] using Horigin.family_eq
      cached := by
        simp only [Array.mem_push]
        exact Or.inl Horigin.cached }⟩
  · have heq : j = state.newTypes.size := by omega
    subst j
    exact ⟨{
      lctx := lctx
      As := As
      levels := levels
      nestedNParams := nparams
      sourceNumParams := hsourceParams
      args := args
      argsArity := hnparams
      sourceName := sourceName
      auxName := auxName
      sourceInfo := sourceInfo
      data := data
      selection := Hselection
      selectionNodup := hselectionNodup
      ngen := ngen
      closing := Hclosing
      levelsNoMVars := Hlevels
      argsFVars := Hargs
      argsClosed := HargsClosed
      built := Hbuilt
      family_eq := by simp [Array.getElem_push]
      cached := by simp }⟩

theorem AuxiliaryGenerationBatch.pendingGeneratedFamilyOrigins
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hselection : CDeclArray lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hnparams : nparams ≤ args.size)
    (hclosures : MutualInductivesClosed env)
    (triggerInfo : InductiveVal)
    (htrigger : env.find? targetName = some (.inductInfo triggerInfo))
    (hsourceNames : ∀ sourceName ∈ sourceNames,
      sourceName ∈ triggerInfo.all)
    (hnparamsTrigger : nparams = triggerInfo.numParams)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args, arg.FVarsIn (· ∈ Hselection.fvars))
    (HargsClosed : ∀ i, i < nparams → args[i]!.hasLooseBVars = false)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  induction H with
  | nil => exact Horigins
  | cons Hstep Htail ih =>
    have Hclosure := hclosures targetName triggerInfo htrigger
    rcases Hstep.generated with
      ⟨_auxName, _nextIdx, _data, _Hfresh, Hbuilt, _hresult, _hstate⟩
    have hmemberParams := Hclosure.parameters _ _
      (hsourceNames _ (by simp)) Hbuilt.lookup
    have hstepParams : nparams = _ :=
      hnparamsTrigger.trans hmemberParams.symm
    exact ih
      (fun sourceName hsource => hsourceNames sourceName (by simp [hsource]))
      (Hstep.pendingGeneratedFamilyOrigins Hselection
        hselectionNodup Hclosing hnparams hstepParams Hlevels Hargs HargsClosed Horigins)

theorem OccurrenceReplacement.pendingGeneratedFamilyOrigins
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Hselection : CDeclArray lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hnparams : value.numParams ≤ args.size)
    (hclosures : MutualInductivesClosed env)
    (htrigger : env.find? targetName = some (.inductInfo value))
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args, arg.FVarsIn (· ∈ Hselection.fvars))
    (HargsClosed : ∀ i, i < value.numParams → args[i]!.hasLooseBVars = false)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  cases H with
  | cached => exact Horigins
  | generated _ Hbatch =>
    exact Hbatch.pendingGeneratedFamilyOrigins Hselection hselectionNodup
      Hclosing hnparams hclosures value htrigger (by simp) rfl Hlevels Hargs
      HargsClosed Horigins

theorem NodeReplacement.pendingGeneratedFamilyOrigins
    (H : NodeReplacement env lctx params As e state out)
    (Hselection : CDeclArray lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hclosures : MutualInductivesClosed env)
    (Hinput : e.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  cases H with
  | unrecognized => exact Horigins
  | recognized Hcandidate hhead Hresult =>
    exact Hresult.pendingGeneratedFamilyOrigins Hselection hselectionNodup
      Hclosing Hcandidate.parameters.arity hclosures (by
        rcases Hcandidate.headFound with ⟨fn, levels, hfn, hfind⟩
        rw [hhead] at hfn
        injection hfn with hname _
        simpa [hname] using hfind) (by
        have Hfn := Hinput.getAppFn
        rw [hhead] at Hfn
        simpa [Lean4Lean.FVarsIn] using Hfn) (by
        intro arg harg
        apply Hinput.getAppArgsList
        rw [← Expr.getAppArgs_toList]
        exact Array.mem_toList_iff.mpr harg) Hcandidate.parameters.closed
      Horigins

theorem ExprLowering.pendingGeneratedFamilyOrigins
    (H : ExprLowering env lctx params As e state out)
    (Hselection : CDeclArray lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hclosures : MutualInductivesClosed env)
    (Hinput : e.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  induction H with
  | occurrence Hnode =>
    exact Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup
      Hclosing hclosures Hinput Horigins
  | bvar | fvar | mvar | sort | const | lit => exact Horigins
  | app Hnode _ _ ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2 (ihFn Hinput.1
      (Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup Hclosing
        hclosures Hinput Horigins))
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2 (ihDom Hinput.1
      (Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup Hclosing
        hclosures Hinput Horigins))
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2 (ihValue Hinput.2.1 (ihType Hinput.1
      (Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup Hclosing
        hclosures Hinput Horigins)))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact ihBody Hinput (Hnode.pendingGeneratedFamilyOrigins Hselection
      hselectionNodup Hclosing hclosures Hinput Horigins)

theorem ConstructorLowering.pendingGeneratedFamilyOrigins
    (H : ConstructorLowering env params nparams source state out)
    (hclosures : MutualInductivesClosed env)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hbinding,
      Hselection, hnodup, hopenedTypes, hopenedAux, _hopenedNext, _hsize,
      Hreplace, _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hopened : PendingGeneratedFamilyOrigins env params initialSize cursor
      openedState := by
    intro j hinitial hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    rcases Horigins j hinitial hcursor hjState with ⟨Horigin⟩
    exact ⟨by simpa [hopenedTypes, hopenedAux] using Horigin⟩
  have Hclosing : NestedClosingContext lctx As openedState.ngen :=
    Hopening.closingContext Hbinding Hselection hnodup Hsource
  exact Hreplace.pendingGeneratedFamilyOrigins Hselection hnodup Hclosing
    hclosures Htail Hopened

theorem ConstructorLowerings.pendingGeneratedFamilyOrigins
    (H : ConstructorLowerings env params nparams sources state out)
    (hclosures : MutualInductivesClosed env)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  induction H with
  | nil => exact Horigins
  | cons Hhead Htail ih =>
    exact ih (fun source hsource => Hsources source (by simp [hsource]))
      (Hhead.pendingGeneratedFamilyOrigins hclosures
        (Hsources _ (by simp)) Horigins)

theorem FamilyLowering.pendingGeneratedFamilyOrigins
    (H : FamilyLowering env params nparams source state out)
    (hclosures : MutualInductivesClosed env)
    (Hsource : InductiveConstructorsClosed source)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 :=
  H.constructors.pendingGeneratedFamilyOrigins hclosures Hsource Horigins

/-- An auxiliary family at a slot of the final queue: the generation step that appended its
source family and the family lowering that produced it. -/
structure LoweredAuxiliaryFamily
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalState : Lean4Lean.ElimNestedInductive.State)
    (target : InductiveType) where
  source : InductiveType
  generated : AuxiliaryFamilySpecialization env params finalState.nestedAux source
  stepState : Lean4Lean.ElimNestedInductive.State
  loweredState : Lean4Lean.ElimNestedInductive.State
  lowered : FamilyLowering env params nparams source stepState
    (target, loweredState)
  later : NestedAuxLE loweredState finalState

def LoweredAuxiliaryFamily.mono
    (H : LoweredAuxiliaryFamily env params nparams state target)
    (Haux : NestedAuxLE state nextState) :
    LoweredAuxiliaryFamily env params nparams nextState target :=
  { H with
    generated := { H.generated with cached := Haux.mem H.generated.cached }
    later := H.later.trans Haux }

/-- The auxiliary families of the queue, split at the dynamic queue cursor: lowered behind
it, pending at or after it. -/
structure LoweringQueueAuxiliaryFamilies
    (env : Environment) (params : Array Expr) (nparams initialSize cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  processed : ∀ j, initialSize ≤ j →
    (hj : j < state.newTypes.size) → j < cursor →
    Nonempty (LoweredAuxiliaryFamily env params nparams state
      state.newTypes[j])
  pending : PendingGeneratedFamilyOrigins env params initialSize cursor state

theorem LowerNextStep.familyPositions
    (H : LowerNextStep env params nparams i state
      (some source, nextState))
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize nextState := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have HloweredPositions := Hlowered.familyPositions Hpositions
    have Hle := Hlowered.newTypesLE
    have hiLowered := (Hle.getElem hi).choose
    constructor
    · simpa [Array.size_set!] using HloweredPositions.size
    · intro nested name hentry
      rcases HloweredPositions.position nested name hentry with
        ⟨j, hj, hinitial, hname⟩
      have hjNext : j < (loweredState.newTypes.set! i target).size := by
        simpa [Array.size_set!] using hj
      refine ⟨j, hjNext, hinitial, ?_⟩
      by_cases hji : j = i
      · subst j
        have hsource : loweredState.newTypes[i] = state.newTypes[i] :=
          (Hle.getElem hi).choose_spec
        have htargetName : target.name = loweredState.newTypes[i].name := by
          rw [Hlowered.name, hsource]
        calc
          (loweredState.newTypes.set! i target)[i].name = target.name := by
            simp
          _ = loweredState.newTypes[i].name := htargetName
          _ = name := hname
      · have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hj
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        simpa [Array.set!, hget] using hname

theorem LowerNextStep.generatedFamilyOrigins
    (H : LowerNextStep env params nparams i state
      (some source, nextState))
    (Hpending : PendingNewTypesClosed i state)
    (hclosures : MutualInductivesClosed env)
    (Horigins : LoweringQueueAuxiliaryFamilies env params nparams initialSize i
      state) :
    LoweringQueueAuxiliaryFamilies env params nparams initialSize (i + 1)
      nextState := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have Haux := Hlowered.nestedAuxLE
    have HsetAux : NestedAuxLE loweredState
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } :=
      ⟨[], by simp⟩
    have hiLowered := (Hle.getElem hi).choose
    have HpendingOrigins := Hlowered.pendingGeneratedFamilyOrigins
      hclosures (Hpending i (Nat.le_refl _) hi) Horigins.pending
    constructor
    · intro j hinitial hjNext hjProcessed
      by_cases hji : j = i
      · subst j
        rcases Horigins.pending i hinitial (Nat.le_refl _) hi with
          ⟨Hsource⟩
        let Hfinal : LoweredAuxiliaryFamily env params nparams
            { loweredState with
              newTypes := loweredState.newTypes.set! i target } target := {
          source := state.newTypes[i]
          generated := { Hsource with cached := Haux.mem Hsource.cached }
          stepState := state
          loweredState := loweredState
          lowered := Hlowered
          later := HsetAux }
        exact ⟨by
          simpa [Array.getElem_setIfInBounds, hiLowered] using Hfinal⟩
      · have hjOld : j < i := by omega
        have hjState : j < state.newTypes.size := by omega
        rcases Horigins.processed j hinitial hjState hjOld with ⟨Hprocessed⟩
        rcases Hle.getElem hjState with ⟨hjLowered, hsame⟩
        have Hprocessed' := Hprocessed.mono (Haux.trans HsetAux)
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact ⟨by simpa [Array.set!, hget, hsame] using Hprocessed'⟩
    · intro j hinitial hjCursor hjNext
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hjNext
      rcases HpendingOrigins j hinitial (by omega) hjLowered with ⟨Hsource⟩
      have hji : j ≠ i := by omega
      have hget := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun h : i = j => hji h.symm)] at hget
      exact ⟨by simpa [Array.set!, hget] using Hsource⟩

/-- Every auxiliary slot of the final result is a `LoweredAuxiliaryFamily`. -/
theorem LoweringQueue.resolvedAuxiliaryFamilyAt
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hpending : PendingNewTypesClosed i state)
    (Horigins : LoweringQueueAuxiliaryFamilies env params nparams initialSize i
      state)
    (hinitial : initialSize ≤ j)
    (hj : j < out.1.types.length) :
    Nonempty (LoweredAuxiliaryFamily env params nparams out.2
      out.1.types[j]) := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    have hjState : j < stateDone.newTypes.size := by simpa using hj
    exact Horigins.processed j hinitial hjState (by omega)
  | step Hnext Htail ih =>
    exact ih (Hnext.pendingNewTypesClosed Henv Hpending)
      (Hnext.generatedFamilyOrigins Hpending hclosures Horigins) hj

theorem LoweringQueue.familyPositions
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hpositions : AuxiliaryCachePositions initialSize state) :
    AuxiliaryCachePositions initialSize out.2 := by
  induction H with
  | done => exact Hpositions
  | step Hnext Htail ih => exact ih (Hnext.familyPositions Hpositions)

theorem LoweringQueue.resultTypes
    (H : LoweringQueue env params nparams lctx i fuel state out) :
    out.1.types = out.2.newTypes.toList := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

/-- Every auxiliary slot of the final result is a `LoweredAuxiliaryFamily`, indexed by its
position in the final result. -/
theorem NestedLowering.resolvedAuxiliaryFamilyAt
    (H : NestedLowering env fuel nparams types initialState out)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hsuffix : initialState.newTypes.size ≤ j)
    (hj : j < out.1.types.length) :
    Nonempty (LoweredAuxiliaryFamily env out.1.params nparams
      out.2 out.1.types[j]) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      hnewTypes, _hnestedAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have Horigins : LoweringQueueAuxiliaryFamilies env params nparams
      initialState.newTypes.size 0 paramsState := by
    constructor
    · intro j _hinitial _hj hjProcessed
      omega
    · intro j hinitial _hcursor hj
      have hjInitial : j < initialState.newTypes.size := by
        simpa [hnewTypes] using hj
      omega
  have Hpending : PendingNewTypesClosed 0 paramsState := by
    intro j _hj hjState
    have hjInitial : j < initialState.newTypes.size := by
      simpa [hnewTypes] using hjState
    have hmember : initialState.newTypes[j] ∈ types := by
      have hmemInitial : initialState.newTypes[j] ∈ initialState.newTypes :=
        Array.getElem_mem hjInitial
      simp [hinitialTypes]
    have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
      have heq := congrArg (fun xs : Array InductiveType => xs[j]!) hnewTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hjState, hjInitial] using heq
    rw [hvalue]
    exact Hsources.constructorsClosed hmember
  have Hfinal := Hqueue.resolvedAuxiliaryFamilyAt Henv hclosures Hpending Horigins
    hsuffix hj
  rw [Hqueue.resultContext.2]
  exact Hfinal

/-- Every final auxiliary-cache entry points back to a concrete generated
suffix slot.  This is derived from the paired cache/queue pushes of the
executable lowering run, rather than assumed. -/
theorem NestedLowering.resolvedAuxFamilyPosition
    (H : NestedLowering env fuel nparams types initialState out)
    (hempty : initialState.nestedAux = #[]) :
    AuxiliaryCachePositions initialState.newTypes.size out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      hnewTypes, hinitialAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have Hinitial : AuxiliaryCachePositions initialState.newTypes.size
      paramsState := by
    constructor
    · simp [hnewTypes]
    · intro nested name hentry
      have : (nested, name) ∈ initialState.nestedAux := by
        simpa [hinitialAux] using hentry
      simp [hempty] at this
  exact Hqueue.familyPositions Hinitial

/-- The auxiliary family recovered from an entry of the final cache.
The cache's fresh-name invariant makes the auxiliary family at that position agree
with the queried nested expression, including for a replacement that reused an entry
created earlier in the lowering traversal. -/
structure CachedAuxiliaryFamily
    (env : Environment) (params : Array Expr) (nparams initialSize : Nat)
    (finalState : Lean4Lean.ElimNestedInductive.State)
    (nested : Expr) (auxName : Name) where
  j : Nat
  hj : j < finalState.newTypes.size
  generatedSuffix : initialSize ≤ j
  origin : LoweredAuxiliaryFamily env params nparams finalState
    finalState.newTypes[j]
  nested_eq : origin.generated.data.nested = nested
  auxName_eq : origin.generated.auxName = auxName

/-- The executable result map contains no entries other than those retained
in the final lowering cache.  This reverse direction is what lets a local
replacement rejoin the auxiliary family of the queue that the whole lowering run
records. -/
theorem NestedLowering.resolvedCacheEntryOfResultLookup
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hlookup : result.aux2nested.find? auxName = some nested) :
    (nested, auxName) ∈ finalState.nestedAux := by
  rw [H.resultAuxMap] at hlookup
  change (finalState.nestedAux.foldl
    (fun (map : Std.TreeMap Name Expr Name.quickCmp)
      (entry : Expr × Name) => map.insert entry.2 entry.1)
    {})[auxName]? = some nested at hlookup
  rw [← Array.foldl_toList] at hlookup
  simpa using nestedAuxFold_find_mem finalState.nestedAux.toList hlookup

theorem NestedLowering.cachedAuxiliaryFamily
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hempty : initialState.nestedAux = #[])
    (hentry : (nested, auxName) ∈ finalState.nestedAux) :
    Nonempty (CachedAuxiliaryFamily env result.params nparams
      initialState.newTypes.size finalState nested auxName) := by
  rcases (H.resolvedAuxFamilyPosition hempty).position nested auxName hentry with
    ⟨j, hj, hinitial, hname⟩
  rcases H.source with
    ⟨_first, _rest, _tail, _paramsState, _lctx, _params, _htypes,
      _Hopening, _hnewTypes, _hinitialAux, _hnextIdx, _hprefix, _Hctx, _Hselection,
      Hqueue⟩
  have hjResult : j < result.types.length := by
    rw [Hqueue.resultTypes]
    simpa using hj
  rcases H.resolvedAuxiliaryFamilyAt Henv hclosures Hsources hinitialTypes hinitial
    hjResult with ⟨Horigin⟩
  have hfamily : result.types[j] = finalState.newTypes[j] := by
    have harr : result.types.toArray = finalState.newTypes := by
      simpa using congrArg List.toArray Hqueue.resultTypes
    have hget := congrArg
      (fun xs : Array InductiveType => xs[j]!) harr
    have hleft : result.types.toArray[j]! = result.types[j] := by
      simp [hjResult]
    have hright : finalState.newTypes[j]! = finalState.newTypes[j] := by
      simp [hj]
    exact hleft.symm.trans (hget.trans hright)
  have HoriginFinal : LoweredAuxiliaryFamily env result.params
      nparams finalState finalState.newTypes[j] := by
    simpa [hfamily] using Horigin
  have hauxName : HoriginFinal.generated.auxName = auxName := by
    calc
      HoriginFinal.generated.auxName = HoriginFinal.generated.data.type.name :=
        HoriginFinal.generated.built.name.symm
      _ = HoriginFinal.source.name :=
        congrArg InductiveType.name HoriginFinal.generated.family_eq.symm
      _ = finalState.newTypes[j].name := HoriginFinal.lowered.name.symm
      _ = auxName := hname
  have hgeneratedEntry :
      (HoriginFinal.generated.data.nested, auxName) ∈
        finalState.nestedAux := by
    simpa [hauxName] using HoriginFinal.generated.cached
  have hnodup := H.resultNamesNodupOfEmpty hempty
  have hfind := nestedAuxFold_find finalState.nestedAux.toList
    ({} : Std.TreeMap Name Expr Name.quickCmp) hnodup
    (by simpa using hentry)
  have hfindGenerated := nestedAuxFold_find finalState.nestedAux.toList
    ({} : Std.TreeMap Name Expr Name.quickCmp) hnodup
    (by simpa using hgeneratedEntry)
  have hnested : HoriginFinal.generated.data.nested = nested := by
    rw [hfind] at hfindGenerated
    exact Option.some.inj hfindGenerated.symm
  exact ⟨{
    j := j
    hj := hj
    generatedSuffix := hinitial
    origin := HoriginFinal
    nested_eq := hnested
    auxName_eq := hauxName }⟩

/-- Map-facing form of `cachedAuxiliaryFamily`.  Replacement
relations expose an exact lookup in the executable map; both cache reuse and newly
generated families can therefore recover their auxiliary slot of the queue
without any caller-supplied correspondence. -/
theorem NestedLowering.cachedAuxiliaryFamilyOfLookup
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hempty : initialState.nestedAux = #[])
    (hlookup : result.aux2nested.find? auxName = some nested) :
    Nonempty (CachedAuxiliaryFamily env result.params nparams
      initialState.newTypes.size finalState nested auxName) :=
  H.cachedAuxiliaryFamily Henv hclosures Hsources hinitialTypes hempty
    (H.resolvedCacheEntryOfResultLookup hlookup)

theorem LoweredAuxiliaryFamily.resolvedMapping
    (H : LoweredAuxiliaryFamily env params nparams finalState
      target)
    (Hmap : NestedAuxMapModels result finalState) :
    FamilyLowering.Resolved env params nparams result H.source H.stepState
      (target, H.loweredState) :=
  H.lowered.resolvedMapping H.later Hmap

end VerifyInductive
end Lean4Lean
