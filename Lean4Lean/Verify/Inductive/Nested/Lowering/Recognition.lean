import Lean4Lean.Verify.Inductive.Nested.Lowering.Basic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! # Recognition of nested occurrences

The specification `NestedOccurrence` of the executable test `isNestedInductiveApp?`: an
application of a previously declared inductive family whose parameters mention a family of the
lowering queue and have no loose bound variables. The file proves that the executable test
returns exactly the recognized occurrences (`isNestedInductiveApp_candidate`,
`NestedOccurrence.recognized`), and specifies the generation of auxiliary families for a whole
container block (`AuxiliaryGenerationBatch`, `generateAuxiliaries_refines`). -/

/-- Syntactic facts that must hold before an expression can be treated as a
nested occurrence. The environment lookup and parameter scan are certified
separately, at the point where their reader/state effects are exposed. -/
structure NestedOccurrenceShape (e : Expr) : Prop where
  isApp : e.isApp = true
  constHead : ∃ fn levels, e.getAppFn = .const fn levels

/-- Independent specification of the occurrence test used while scanning
parameters of a previously declared inductive application. -/
def MentionsQueuedFamily
    (newTypes : Array InductiveType) (e : Expr) : Prop :=
  e.findAny (fun
    | .const name _ => newTypes.any fun type => name == type.name
    | _ => false) = true

theorem mentionsQueuedFamily_iff
    (newTypes : Array InductiveType) (e : Expr) :
    Lean4Lean.ElimNestedInductive.mentionsQueuedFamily newTypes e = true ↔
      MentionsQueuedFamily newTypes e := by
  rfl

theorem nestedParamFlags_fst
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) :
    (Lean4Lean.ElimNestedInductive.nestedParamFlags newTypes args n).1 = true ↔
      ∃ i, i < n ∧ MentionsQueuedFamily newTypes args[i]! := by
  induction n with
  | zero => simp [Lean4Lean.ElimNestedInductive.nestedParamFlags]
  | succ n ih =>
    rw [Lean4Lean.ElimNestedInductive.nestedParamFlags]
    simp only [Bool.or_eq_true, ih, mentionsQueuedFamily_iff]
    constructor
    · rintro (⟨i, hi, hmentions⟩ | hmentions)
      · exact ⟨i, by omega, hmentions⟩
      · exact ⟨n, by omega, hmentions⟩
    · rintro ⟨i, hi, hmentions⟩
      by_cases h : i = n
      · subst i; exact Or.inr hmentions
      · exact Or.inl ⟨i, by omega, hmentions⟩

theorem nestedParamFlags_snd_false
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) :
    (Lean4Lean.ElimNestedInductive.nestedParamFlags newTypes args n).2 = false ↔
      ∀ i, i < n → args[i]!.hasLooseBVars = false := by
  induction n with
  | zero => simp [Lean4Lean.ElimNestedInductive.nestedParamFlags]
  | succ n ih =>
    rw [Lean4Lean.ElimNestedInductive.nestedParamFlags]
    simp only [Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨hprev, hn⟩ i hi
      by_cases h : i = n
      · simpa [h] using hn
      · exact hprev i (by omega)
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall n (by omega)⟩

/-- Abstract contract for the parameter scan in
`isNestedInductiveApp?`: the application has enough arguments, at least one
parameter mentions a family currently being lowered, and every scanned
parameter is closed with respect to bound variables. -/
structure NestedOccurrenceArgs
    (newTypes : Array InductiveType) (args : Array Expr) (n : Nat) : Prop where
  arity : n ≤ args.size
  nested : ∃ i, i < n ∧ MentionsQueuedFamily newTypes args[i]!
  closed : ∀ i, i < n → args[i]!.hasLooseBVars = false

/-- Full abstract acceptance contract for nested-application recognition.
It is stated without reference to the executable loop, so the refinement theorems
(`isNestedInductiveApp_candidate`, `NestedOccurrence.recognized`) compare the loop
against an independent specification. -/
structure NestedOccurrence (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (e : Expr) (info : InductiveVal) : Prop where
  shape : NestedOccurrenceShape e
  headFound : ∃ fn levels, e.getAppFn = .const fn levels ∧
    env.find? fn = some (.inductInfo info)
  parameters : NestedOccurrenceArgs state.newTypes e.getAppArgs info.numParams

/-- Recognition is maximal over an application spine: adding trailing
arguments preserves a nested occurrence because only its leading
parameter prefix is inspected. -/
theorem NestedOccurrence.app
    (H : NestedOccurrence env state fn info) (arg : Expr) :
    NestedOccurrence env state (.app fn arg) info := by
  have hargs : (Expr.app fn arg).getAppArgs = fn.getAppArgs.push arg := by
    rw [Expr.getAppArgs_eq, Expr.getAppArgs_eq, Expr.getAppArgsList_app]
    simp
  refine {
    shape := ⟨rfl, ?_⟩
    headFound := ?_
    parameters := ?_ }
  · rcases H.shape.constHead with ⟨name, levels, hhead⟩
    exact ⟨name, levels, by simpa [Expr.getAppFn] using hhead⟩
  · rcases H.headFound with ⟨name, levels, hhead, hfound⟩
    exact ⟨name, levels, by simpa [Expr.getAppFn] using hhead, hfound⟩
  · refine {
      arity := by
        rw [hargs]
        exact Nat.le_trans H.parameters.arity (by simp)
      nested := ?_
      closed := ?_ }
    · rcases H.parameters.nested with ⟨i, hi, hmentions⟩
      refine ⟨i, hi, ?_⟩
      have hiOld : i < fn.getAppArgs.size :=
        Nat.lt_of_lt_of_le hi H.parameters.arity
      have hiPush : i < (fn.getAppArgs.push arg).size := by simp; omega
      have hbang : (fn.getAppArgs.push arg)[i]! = fn.getAppArgs[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hiPush, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hargs, hbang]
      exact hmentions
    · intro i hi
      have hiOld : i < fn.getAppArgs.size :=
        Nat.lt_of_lt_of_le hi H.parameters.arity
      have hiPush : i < (fn.getAppArgs.push arg).size := by simp; omega
      have hbang : (fn.getAppArgs.push arg)[i]! = fn.getAppArgs[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hiPush, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hargs, hbang]
      exact H.parameters.closed i hi

theorem isNestedInductiveApp_candidate
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => ∀ info, out.1 = some info →
        NestedOccurrence env state e info := by
  intro out hout info hinfo
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp [happ] at hout
    cases hout
    simp at hinfo
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      simp [happTrue, hhead,
        Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
      cases hfound : env.find? fn with
      | none =>
        simp [hfound] at hout
        change Except.ok (none, state) = .ok out at hout
        cases hout
        simp at hinfo
      | some found =>
        cases found with
        | inductInfo ci =>
          simp only [hfound] at hout
          by_cases harity : e.getAppArgs.size < ci.numParams
          · simp [harity] at hout
            cases hout
            simp at hinfo
          · simp only [harity, ↓reduceIte] at hout
            let flags := Lean4Lean.ElimNestedInductive.nestedParamFlags
              state.newTypes e.getAppArgs ci.numParams
            by_cases hnested : flags.1 = false
            · simp [flags, hnested] at hout
              cases hout
              simp at hinfo
            · have hnestedTrue : flags.1 = true := by
                cases h : flags.1 <;> simp_all
              by_cases hloose : flags.2 = true
              · simp [flags, hnestedTrue, hloose] at hout
                cases hout
              · have hlooseFalse : flags.2 = false := by
                  cases h : flags.2 <;> simp_all
                simp [flags, hnestedTrue, hlooseFalse] at hout
                cases hout
                simp only [Option.some.injEq] at hinfo
                subst info
                refine {
                  shape := ⟨happTrue, ⟨fn, levels, hhead⟩⟩
                  headFound := ⟨fn, levels, hhead, hfound⟩
                  parameters := ?_ }
                refine {
                  arity := by omega
                  nested := (nestedParamFlags_fst
                    state.newTypes e.getAppArgs ci.numParams).mp hnestedTrue
                  closed := (nestedParamFlags_snd_false
                    state.newTypes e.getAppArgs ci.numParams).mp hlooseFalse }
        | _ =>
          simp [hfound] at hout
          change Except.ok (none, state) = .ok out at hout
          cases hout
          simp at hinfo
    | _ =>
      simp [happTrue, hhead] at hout
      cases hout
      simp at hinfo

/-- Completeness of the independent recognition contract: every abstract
candidate is returned by the executable recognizer. -/
theorem NestedOccurrence.recognized
    (H : NestedOccurrence env state e info) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.1 = some info := by
  intro out hout
  rcases H.headFound with ⟨fn, levels, hhead, hfound⟩
  have hnested :
      (Lean4Lean.ElimNestedInductive.nestedParamFlags state.newTypes
        e.getAppArgs info.numParams).1 = true :=
    (nestedParamFlags_fst state.newTypes e.getAppArgs info.numParams).mpr
      H.parameters.nested
  have hloose :
      (Lean4Lean.ElimNestedInductive.nestedParamFlags state.newTypes
        e.getAppArgs info.numParams).2 = false :=
    (nestedParamFlags_snd_false state.newTypes e.getAppArgs
      info.numParams).mpr H.parameters.closed
  have harity : ¬ e.getAppArgs.size < info.numParams :=
    Nat.not_lt_of_ge H.parameters.arity
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  simp only [H.shape.isApp, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hhead, Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
  simp [hfound, harity, hnested, hloose] at hout
  cases hout
  rfl

def NotNestedOccurrence (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) (e : Expr) : Prop :=
  ∀ info, ¬ NestedOccurrence env state e info

theorem isNestedInductiveApp_preservesState
    (e : Expr) (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e env state).WF
      fun out => out.2 = state := by
  intro out hout
  unfold Lean4Lean.ElimNestedInductive.isNestedInductiveApp? at hout
  by_cases happ : e.isApp = false
  · simp [happ] at hout
    cases hout
    rfl
  · have happTrue : e.isApp = true := by
      cases h : e.isApp <;> simp_all
    cases hhead : e.getAppFn with
    | const fn levels =>
      simp [happTrue, hhead,
        Lean4Lean.ElimNestedInductive.isNestedInductiveAppConst?] at hout
      cases hfound : env.find? fn with
      | none =>
        simp [hfound] at hout
        cases hout
        rfl
      | some found =>
        cases found with
        | inductInfo ci =>
          simp only [hfound] at hout
          by_cases harity : e.getAppArgs.size < ci.numParams
          · simp [harity] at hout
            cases hout
            rfl
          · simp only [harity, ↓reduceIte] at hout
            let flags := Lean4Lean.ElimNestedInductive.nestedParamFlags
              state.newTypes e.getAppArgs ci.numParams
            by_cases hnested : flags.1 = false
            · simp [flags, hnested] at hout
              cases hout
              rfl
            · have hnestedTrue : flags.1 = true := by
                cases h : flags.1 <;> simp_all
              by_cases hloose : flags.2 = true
              · simp [flags, hnestedTrue, hloose] at hout
                cases hout
              · have hlooseFalse : flags.2 = false := by
                  cases h : flags.2 <;> simp_all
                simp [flags, hnestedTrue, hlooseFalse] at hout
                cases hout
                rfl
        | _ =>
          simp [hfound] at hout
          cases hout
          rfl
    | _ =>
      simp [happTrue, hhead] at hout
      cases hout
      rfl

/-- Reader/state bind specialized to nested lowering. -/
theorem nestedBind.WF
    {α β : Type} {P : α × Lean4Lean.ElimNestedInductive.State → Prop}
    {Q : β × Lean4Lean.ElimNestedInductive.State → Prop}
    {x : Lean4Lean.ElimNestedInductive.M α}
    {f : α → Lean4Lean.ElimNestedInductive.M β}
    (Hx : (x env state).WF P)
    (Hf : ∀ a nextState, P (a, nextState) →
      (f a env nextState).WF Q) :
    ((x >>= f) env state).WF Q := by
  exact Hx.bind fun result hresult => Hf result.1 result.2 hresult

/-- Relational specification of the mutual-family generation loop.  Each list member
has one certified fresh-generation step, and the accumulator passed to the
tail is exactly the executable `Option.or` update. -/
inductive AuxiliaryGenerationBatch
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) : Option Expr → List Name →
      Lean4Lean.ElimNestedInductive.State →
      Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | nil (hresult : result.isSome = true) :
      AuxiliaryGenerationBatch env lctx params As targetName levels nparams args
        result [] state (result, state)
  | cons :
      AuxiliaryGenerationStep env lctx params As targetName levels nparams args
        sourceName sourceInfo state step →
      AuxiliaryGenerationBatch env lctx params As targetName levels nparams args
        (step.1.or result) sourceNames step.2 out →
      AuxiliaryGenerationBatch env lctx params As targetName levels nparams args
        result (sourceName :: sourceNames) state out

theorem AuxiliaryGenerationBatch.resultSome
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : out.1.isSome = true := by
  induction H with
  | nil hresult => exact hresult
  | cons _ _ ih => exact ih

theorem AuxiliaryGenerationBatch.auxFVarsIn
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (HAs : CDeclArray lctx As)
    (hnparams : nparams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih =>
    exact ih (Hstep.auxFVarsIn HAs hnparams Hlevels Hargs Hparams Hstate)

theorem AuxiliaryGenerationBatch.pendingNewTypesClosed
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih =>
    exact ih (Hstep.pendingNewTypesClosed Henv Hclosing Hlevels Hargs Hstate)

private theorem generateAuxiliariesLoop_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (hsize : As.size = params.size)
    (sourceNames : List Name) (infos : InductiveMemberInfos env sourceNames)
    (result : Option Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hready : result.isSome = true ∨ targetName ∈ sourceNames) :
    (Lean4Lean.ElimNestedInductive.generateAuxiliaries.loop lctx params As
      targetName levels nparams args result sourceNames env state).WF fun out =>
        AuxiliaryGenerationBatch env lctx params As targetName levels nparams
          args result sourceNames state out := by
  induction infos generalizing result state with
  | nil =>
    rcases hready with hsome | hmem
    · simp only [Lean4Lean.ElimNestedInductive.generateAuxiliaries.loop,
        hsome, ↓reduceIte, pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure (.nil hsome)
    · simp at hmem
  | @cons sourceName sourceInfo sourceNames hlookup infos ih =>
    rw [Lean4Lean.ElimNestedInductive.generateAuxiliaries.loop]
    refine nestedBind.WF
      (generateAuxiliary_refines env lctx params As targetName levels nparams
        args sourceName sourceInfo state hlookup hsize) ?_
    intro found nextState Hstep
    have hnext : (found.or result).isSome = true ∨
        targetName ∈ sourceNames := by
      rcases hready with hsome | hmem
      · left
        cases found <;> cases result <;> simp_all
      · simp only [List.mem_cons] at hmem
        rcases hmem with heq | htail
        · subst sourceName
          left
          rcases Hstep.generated with
            ⟨auxName, nextIdx, data, Hfresh, Hdata, hfound, hstate⟩
          simp only [beq_self_eq_true, if_true] at hfound
          rw [hfound]
          simp
        · exact Or.inr htail
    exact (ih (result := found.or result) (state := nextState) hnext).mono
      fun _ Htail => .cons Hstep Htail

theorem generateAuxiliaries_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (value : InductiveVal)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (infos : InductiveMemberInfos env value.all)
    (htarget : targetName ∈ value.all) :
    (Lean4Lean.ElimNestedInductive.generateAuxiliaries lctx params As targetName
      levels nparams args value env state).WF fun out =>
        AuxiliaryGenerationBatch env lctx params As targetName levels nparams
          args none value.all state out := by
  unfold Lean4Lean.ElimNestedInductive.generateAuxiliaries
  exact generateAuxiliariesLoop_refines env lctx params As targetName levels
    nparams args hsize value.all infos none state (Or.inr htarget)


end VerifyInductive
end Lean4Lean
