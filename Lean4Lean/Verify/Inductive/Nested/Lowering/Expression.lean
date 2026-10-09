import Lean4Lean.Verify.Inductive.Nested.Lowering.Recognition
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Result

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! # Nested lowering of expressions

Relational specification of the expression traversal of `ElimNestedInductive`
(`Expr.replaceM` over a constructor type): a recognized nested occurrence is replaced by an
application of its auxiliary family, either reusing a cache entry or generating auxiliary
families for the whole container block (`OccurrenceReplacement`, `NodeReplacement`,
`ExprLowering`). The resolved and reopened forms (`ExprLowering.Resolved`,
`ExprLowering.Reopened`) connect each replacement to the final `aux2nested` map and prove that
restoration is a left inverse of lowering up to expression equivalence
(`ExprLowering.Reopened.restore_eqv`). -/

/-- Complete outcome specification for an application already recognized as
nested: either an existing cache entry is reused without changing state, or a
certified batch for the entire mutual block is generated. -/
inductive OccurrenceReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (args : Array Expr)
    (value : InductiveVal) (state : Lean4Lean.ElimNestedInductive.State) :
    Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | cached (auxName : Name) :
      AuxiliaryCacheEntry state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) auxName →
      OccurrenceReplacement env lctx params As targetName levels args
        value state
        (some (mkAppRange (mkAppN (.const auxName state.lvls) As)
          value.numParams args.size args), state)
  | generated :
      MutualInductiveClosure env targetName value →
      AuxiliaryGenerationBatch env lctx params As targetName levels
        value.numParams args none value.all state out →
      OccurrenceReplacement env lctx params As targetName levels args
        value state out

theorem replaceRecognizedNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (args : Array Expr)
    (value : InductiveVal) (state : Lean4Lean.ElimNestedInductive.State)
    (hargs : value.numParams ≤ args.size)
    (hsize : As.size = params.size)
    (hclosure : MutualInductiveClosure env targetName value) :
    (Lean4Lean.ElimNestedInductive.replaceRecognizedNested lctx params As
      (.const targetName levels) args value env state).WF fun out =>
        OccurrenceReplacement env lctx params As targetName levels args
          value state out := by
  unfold Lean4Lean.ElimNestedInductive.replaceRecognizedNested
  simp only [hargs, ↓reduceIte]
  refine nestedBind.WF
    (replaceNestedParams_state_refines params
      (mkAppRange (.const targetName levels) 0 value.numParams args) As
      env state hsize) ?_
  intro nested nextState hnested
  cases hnested
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  cases hcache : Lean4Lean.ElimNestedInductive.findCachedAux?
      state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) with
  | some auxName =>
    simp only [pure, ReaderT.pure, StateT.pure]
    exact Except.WF.pure (OccurrenceReplacement.cached auxName
      (findCachedAux?_refines state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) auxName hcache))
  | none =>
    exact (generateAuxiliaries_refines env lctx params As targetName levels
      value.numParams args value state hsize hclosure.members
      hclosure.target).mono fun _ Hbatch =>
        OccurrenceReplacement.generated hclosure Hbatch

/-- Complete node-level result of nested replacement.  An expression that is not a
nested occurrence is left untouched; every recognized occurrence carries both the
independent recognition fact (`NestedOccurrence`) and the cache-or-generation certificate. -/
inductive NodeReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State) :
    Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | unrecognized : NotNestedOccurrence env state e →
      NodeReplacement env lctx params As e state (none, state)
  | recognized :
      NestedOccurrence env state e value →
      e.getAppFn = .const targetName levels →
      OccurrenceReplacement env lctx params As targetName levels
        e.getAppArgs value state out →
      NodeReplacement env lctx params As e state out

theorem replaceIfNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.replaceIfNested lctx params As e env state).WF
      fun out => NodeReplacement env lctx params As e state out := by
  rw [Lean4Lean.ElimNestedInductive.replaceIfNested]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e)
    (P := fun recognized =>
      recognized.2 = state ∧
      (∀ value, recognized.1 = some value →
        NestedOccurrence env state e value) ∧
      (recognized.1 = none → NotNestedOccurrence env state e)) ?_ ?_
  · intro recognized hrecognized
    refine ⟨isNestedInductiveApp_preservesState e env state
        recognized hrecognized,
      isNestedInductiveApp_candidate e env state recognized hrecognized, ?_⟩
    intro hnone info Hcandidate
    have hcomplete := Hcandidate.recognized recognized hrecognized
    change recognized.1 = some info at hcomplete
    rw [hnone] at hcomplete
    cases hcomplete
  · intro recognized nextState hrecognized
    rcases hrecognized with ⟨hstate, hcandidate, hnone⟩
    simp only at hstate hcandidate hnone ⊢
    subst nextState
    cases recognized with
    | none =>
      exact Except.WF.pure (.unrecognized (hnone rfl))
    | some value =>
      have Hcandidate := hcandidate value rfl
      rcases Hcandidate.headFound with
        ⟨targetName, levels, hhead, hlookup⟩
      simp only
      rw [Expr.withApp_eq, hhead]
      exact (replaceRecognizedNested_refines env lctx params As targetName
        levels e.getAppArgs value state Hcandidate.parameters.arity hsize
        (hclosures targetName value hlookup)).mono fun _ Hresult =>
          .recognized Hcandidate hhead Hresult

theorem OccurrenceReplacement.resultSome
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out) : out.1.isSome = true := by
  cases H with
  | cached => simp
  | generated _ Hbatch => exact Hbatch.resultSome

theorem NodeReplacement.outcome
    (H : NodeReplacement env lctx params As e state out) :
    out = (none, state) ∨ ∃ output nextState, out = (some output, nextState) := by
  cases H with
  | unrecognized => exact Or.inl rfl
  | recognized Hcandidate hhead Hresult =>
    right
    have hsome := Hresult.resultSome
    cases h : out.1 with
    | none => simp [h] at hsome
    | some output => exact ⟨output, out.2, by cases out; simp_all⟩

theorem NodeReplacement.noCandidate
    (H : NodeReplacement env lctx params As e state (none, state)) :
    NotNestedOccurrence env state e := by
  cases H with
  | unrecognized Hnone => exact Hnone
  | recognized Hcandidate hhead Hresult =>
    have hsome := Hresult.resultSome
    simp at hsome

/-- Stateful, top-down specification of `Expr.replaceM` for nested lowering.
A successful node replacement stops descent; otherwise children are processed
left-to-right with the exact intermediate states and update combinators used by
Lean's expression traversal. -/
inductive ExprLowering
    (env : Environment) (lctx : LocalContext) (params As : Array Expr) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | occurrence : NodeReplacement env lctx params As input state
      (some output, nextState) →
      ExprLowering env lctx params As input state (output, nextState)
  | bvar : NodeReplacement env lctx params As (.bvar i) state (none, state) →
      ExprLowering env lctx params As (.bvar i) state (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NodeReplacement env lctx params As (.fvar fvarId) state (none, state) →
      ExprLowering env lctx params As (.fvar fvarId) state
        (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NodeReplacement env lctx params As (.mvar mvarId) state (none, state) →
      ExprLowering env lctx params As (.mvar mvarId) state
        (.mvar mvarId, state)
  | sort : NodeReplacement env lctx params As (.sort level) state (none, state) →
      ExprLowering env lctx params As (.sort level) state (.sort level, state)
  | const : NodeReplacement env lctx params As (.const name levels) state
      (none, state) →
      ExprLowering env lctx params As (.const name levels) state
        (.const name levels, state)
  | lit : NodeReplacement env lctx params As (.lit literal) state (none, state) →
      ExprLowering env lctx params As (.lit literal) state
        (.lit literal, state)
  | app : NodeReplacement env lctx params As (.app fn arg) state (none, state) →
      ExprLowering env lctx params As fn state (fn', fnState) →
      ExprLowering env lctx params As arg fnState (arg', outState) →
      ExprLowering env lctx params As (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NodeReplacement env lctx params As (.lam name dom body bi) state
      (none, state) →
      ExprLowering env lctx params As dom state (dom', domState) →
      ExprLowering env lctx params As body domState (body', outState) →
      ExprLowering env lctx params As (.lam name dom body bi) state
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NodeReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      ExprLowering env lctx params As dom state (dom', domState) →
      ExprLowering env lctx params As body domState (body', outState) →
      ExprLowering env lctx params As (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NodeReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      ExprLowering env lctx params As type state (type', typeState) →
      ExprLowering env lctx params As value typeState (value', valueState) →
      ExprLowering env lctx params As body valueState (body', outState) →
      ExprLowering env lctx params As (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NodeReplacement env lctx params As (.mdata data body) state
      (none, state) →
      ExprLowering env lctx params As body state (body', outState) →
      ExprLowering env lctx params As (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NodeReplacement env lctx params As (.proj name idx body) state
      (none, state) →
      ExprLowering env lctx params As body state (body', outState) →
      ExprLowering env lctx params As (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Nested lowering only appends to `newTypes` while traversing expressions. -/
def NestedNewTypesLE (source target : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ suffix, target.newTypes.toList = source.newTypes.toList ++ suffix

/-- Nested-expression traversal also grows the `(nested expression, fresh
family name)` cache append-only. This cache is the source of the final
`aux2nested` map used by restoration. The universe arguments `lvls` at which
every auxiliary occurrence is emitted are never modified. -/
def NestedAuxLE (source target : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ suffix, target.nestedAux.toList = source.nestedAux.toList ++ suffix ∧
    target.lvls = source.lvls

theorem NestedAuxLE.refl (state : Lean4Lean.ElimNestedInductive.State) :
    NestedAuxLE state state := ⟨[], by simp, rfl⟩

theorem NestedAuxLE.trans
    (H₁ : NestedAuxLE first middle) (H₂ : NestedAuxLE middle last) :
    NestedAuxLE first last := by
  rcases H₁ with ⟨xs, hxs, hl₁⟩
  rcases H₂ with ⟨ys, hys, hl₂⟩
  exact ⟨xs ++ ys, by simp [hys, hxs, List.append_assoc], hl₂.trans hl₁⟩

theorem NestedAuxLE.lvls
    (H : NestedAuxLE source target) : target.lvls = source.lvls := by
  obtain ⟨_, _, h⟩ := H
  exact h

theorem NestedAuxLE.mem
    (H : NestedAuxLE source target)
    (hentry : entry ∈ source.nestedAux) : entry ∈ target.nestedAux := by
  rcases H with ⟨suffix, hsuffix, -⟩
  have hsource : entry ∈ source.nestedAux.toList := by simpa using hentry
  have htarget : entry ∈ target.nestedAux.toList := by
    rw [hsuffix]
    exact List.mem_append_left suffix hsource
  simpa using htarget

/-- An application spine has no loose bound variables when neither its head
nor any argument has one. -/
theorem Expr.looseBVarRange'_mkAppList_eq_zero {fn : Expr} {args : List Expr}
    (hfn : fn.looseBVarRange' = 0)
    (hargs : ∀ arg ∈ args, arg.looseBVarRange' = 0) :
    (Expr.mkAppList fn args).looseBVarRange' = 0 := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons arg args ih =>
    simp only [Expr.mkAppList]
    apply ih
    · simp [Expr.looseBVarRange', hfn, hargs arg (by simp)]
    · intro a ha
      exact hargs a (by simp [ha])

/-- The parameter prefix of a recognized nested application has no loose
bound variables: this is the kernel's own "nested inductive datatype
parameters cannot contain local variables" check. -/
theorem Expr.mkAppRange_looseBVarRange_zero {fn : Expr} {args : Array Expr}
    {n : Nat} (hfn : fn.looseBVarRange' = 0) (harity : n ≤ args.size)
    (hargs : ∀ i, i < n → args[i]!.hasLooseBVars = false) :
    (mkAppRange fn 0 n args).looseBVarRange' = 0 := by
  rw [Expr.mkAppRange_from_zero _ _ _ harity]
  apply Expr.looseBVarRange'_mkAppList_eq_zero hfn
  intro arg harg
  rcases List.mem_iff_getElem.mp harg with ⟨i, hi, rfl⟩
  have hin : i < n := by
    have hi' := hi
    simp only [List.length_take, Array.length_toList] at hi'
    omega
  have hiargs : i < args.size := Nat.lt_of_lt_of_le hin harity
  have hz : args[i].looseBVarRange' = 0 := by
    have hclosed := hargs i hin
    rw [getElem!_pos args i hiargs] at hclosed
    simpa [Expr.hasLooseBVars, Expr.looseBVarRange_eq] using hclosed
  simpa [List.getElem_take, Array.getElem_toList] using hz

theorem NestedOccurrence.prefixLooseBVarRange_zero
    (H : NestedOccurrence env state input value) (fn : Expr)
    (hfn : fn.looseBVarRange' = 0) :
    (mkAppRange fn 0 value.numParams input.getAppArgs).looseBVarRange' = 0 :=
  Expr.mkAppRange_looseBVarRange_zero hfn H.parameters.arity
    H.parameters.closed

/-- A family freshly appended by nested lowering, together with the matching
cache entry that lets restoration recover the application from which it was
built.  Keeping the two append-only arrays paired is the correspondence that is
lost by `NestedNewTypesLE` alone. -/
structure AuxiliaryFamilySpecialization
    (env : Environment) (params : Array Expr)
    (nestedAux : Array (Expr × Name))
    (family : InductiveType) where
  lctx : LocalContext
  As : Array Expr
  levels : List Level
  nestedNParams : Nat
  args : Array Expr
  argsArity : nestedNParams ≤ args.size
  sourceName : Name
  auxName : Name
  sourceInfo : InductiveVal
  sourceNumParams : nestedNParams = sourceInfo.numParams
  data : Lean4Lean.ElimNestedInductive.AuxiliaryData
  selection : CDeclArray lctx As
  selectionNodup : selection.fvars.Nodup
  ngen : NameGenerator
  closing : NestedClosingContext lctx As ngen
  levelsNoMVars : ∀ level ∈ levels, level.hasMVar' = false
  argsFVars : ∀ arg ∈ args, arg.FVarsIn (· ∈ selection.fvars)
  argsClosed : ∀ i, i < nestedNParams → args[i]!.hasLooseBVars = false
  built : AuxiliaryFamilySpec env lctx params As levels nestedNParams args
    sourceName auxName sourceInfo data
  family_eq : family = data.type
  cached : (data.nested, auxName) ∈ nestedAux

/-- Closing a generated family's cached application over the final lowering
parameters yields the same de Bruijn application as closing the source
application over the parameters selected when the auxiliary was built.  The
retained argument-scope invariant is the essential alpha-conversion premise. -/
theorem AuxiliaryFamilySpecialization.cachedClosureAlpha
    (H : AuxiliaryFamilySpecialization env params nestedAux family)
    (resultSelection : CDeclArray resultLctx params)
    (hresultNodup : resultSelection.fvars.Nodup) :
    H.data.nested.abstractList resultSelection.fvars =
      (mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars := by
  let sourceApp := mkAppRange (.const H.sourceName H.levels) 0
    H.nestedNParams H.args
  have HsourceScope : sourceApp.FVarsIn (· ∈ H.selection.fvars) := by
    apply FVarsIn.mkAppRange_zero H.argsArity
    · simpa [Lean4Lean.FVarsIn] using H.levelsNoMVars
    · exact H.argsFVars
  have Hclosed : (sourceApp.abstractList H.selection.fvars).FVarsIn
      (fun _ => False) := by
    apply FVarsIn.abstractList_of
    exact HsourceScope.mono fun fv hfv => Or.inl hfv
  have Haway : (sourceApp.abstractList H.selection.fvars).FVarsIn
      (fun fv => fv ∉ resultSelection.fvars) :=
    Hclosed.mono fun _ hfalse => False.elim hfalse
  rw [H.built.nested]
  change (Expr.reopenParams sourceApp H.As params).abstractList
      resultSelection.fvars = sourceApp.abstractList H.selection.fvars
  rw [Expr.reopenParams_eq_reopenFVarsAt H.selectionNodup H.selection.expressions
    resultSelection.expressions
    (Expr.mkAppRange_looseBVarRange_zero rfl H.argsArity H.argsClosed)]
  exact Haway.abstractList_instantiateRevList hresultNodup

/-- Exact-model form of `cachedClosureAlpha`: the operational abstraction of
the cached application over the final parameters is literally the de Bruijn
closure of the source application over the parameters selected when the
auxiliary was built. -/
theorem AuxiliaryFamilySpecialization.cachedClosureAlphaExact
    (H : AuxiliaryFamilySpecialization env params nestedAux family)
    (resultSelection : CDeclArray resultLctx params)
    (hresultNodup : resultSelection.fvars.Nodup) :
    H.data.nested.abstract params =
      (mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars := by
  let sourceApp := mkAppRange (.const H.sourceName H.levels) 0
    H.nestedNParams H.args
  have hsource : sourceApp.looseBVarRange' = 0 :=
    Expr.mkAppRange_looseBVarRange_zero rfl H.argsArity H.argsClosed
  have HsourceScope : sourceApp.FVarsIn (· ∈ H.selection.fvars) := by
    apply FVarsIn.mkAppRange_zero H.argsArity
    · simpa [Lean4Lean.FVarsIn] using H.levelsNoMVars
    · exact H.argsFVars
  have Hclosed : (sourceApp.abstract H.As).FVarsIn (fun _ => False) :=
    FVarsIn.abstract_fvarArray_of H.selection.fvars H.As H.selection.expressions
      (HsourceScope.mono fun fv hfv => Or.inl hfv)
  have Haway : (sourceApp.abstract H.As).FVarsIn
      (fun fv => fv ∉ resultSelection.fvars) :=
    Hclosed.mono fun _ hfalse => False.elim hfalse
  have hlb : (sourceApp.abstract H.As).looseBVarRange' ≤
      resultSelection.fvars.length := by
    have hbound := Expr.abstractN_looseBVarRange_le (e := sourceApp)
      (fvs := H.selection.fvars) (k := 0)
    rw [hsource] at hbound
    have h1 : H.selection.fvars.length = H.As.size := by
      simpa using (congrArg Array.size H.selection.expressions).symm
    have h2 : resultSelection.fvars.length = params.size := by
      simpa using (congrArg Array.size resultSelection.expressions).symm
    have harity := H.built.arity
    have hrw : sourceApp.abstract H.As = sourceApp.abstractN H.selection.fvars :=
      calc
        sourceApp.abstract H.As =
            sourceApp.abstract (H.selection.fvars.map Expr.fvar).toArray :=
          congrArg sourceApp.abstract H.selection.expressions
        _ = sourceApp.abstractN H.selection.fvars := Expr.abstractN_eq _ _
    rw [hrw]
    omega
  rw [H.built.nested]
  change ((sourceApp.abstract H.As).instantiateRev params).abstract params = _
  rw [Haway.abstract_instantiateRev_fvarArray params resultSelection.fvars
    resultSelection.expressions hresultNodup hlb]
  calc
    sourceApp.abstract H.As =
        sourceApp.abstract (H.selection.fvars.map Expr.fvar).toArray :=
      congrArg sourceApp.abstract H.selection.expressions
    _ = _ := Expr.abstract_eq_of_closed _ _ H.selectionNodup hsource

private theorem nestedAuxFold_find_of_not_mem
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnot : name ∉ entries.map Prod.snd) :
    (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = map[name]? := by
  induction entries generalizing map with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.foldl_cons]
    rw [ih _ hnot.2]
    rw [Std.TreeMap.getElem?_insert]
    split
    next heq =>
      have hname : entry.2 = name :=
        Std.LawfulEqCmp.compare_eq_iff_eq.mp heq
      exact False.elim (hnot.1 hname.symm)
    next => rfl

def NestedAuxMapFVarsIn (P : FVarId → Prop)
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr),
    map[name]? = some nested → nested.FVarsIn P

/-- Every key in a restoration map belongs to the private namespace used by
the lowering-generated auxiliary families. -/
def NestedAuxMapNamesReserved
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr), map[name]? = some nested →
    (`_nested).isPrefixOf name = true

def NestedAuxMapNamesFresh (env : Environment)
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr), map[name]? = some nested →
    env.contains name = false

theorem NestedAuxMapNamesReserved.insert
    (Hmap : NestedAuxMapNamesReserved map)
    (Hname : (`_nested).isPrefixOf name = true) :
    NestedAuxMapNamesReserved (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  next hcmp =>
    cases hfind
    rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
    exact Hname
  next => exact Hmap query value hfind

theorem NestedAuxMapNamesFresh.insert
    (Hmap : NestedAuxMapNamesFresh env map)
    (Hname : env.contains name = false) :
    NestedAuxMapNamesFresh env (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  next hcmp =>
    cases hfind
    rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
    exact Hname
  next => exact Hmap query value hfind

theorem NestedAuxMapFVarsIn.insert
    (Hmap : NestedAuxMapFVarsIn P map) (Hnested : nested.FVarsIn P) :
    NestedAuxMapFVarsIn P (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind
    exact Hnested
  · exact Hmap query value hfind

theorem nestedAuxFold_fvarsIn
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries, entry.1.FVarsIn P)
    (Hmap : NestedAuxMapFVarsIn P map) :
    NestedAuxMapFVarsIn P
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

theorem nestedAuxFold_namesReserved
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries,
      (`_nested).isPrefixOf entry.2 = true)
    (Hmap : NestedAuxMapNamesReserved map) :
    NestedAuxMapNamesReserved
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

theorem nestedAuxFold_namesFresh
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries, env.contains entry.2 = false)
    (Hmap : NestedAuxMapNamesFresh env map) :
    NestedAuxMapNamesFresh env
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

/-- Folding a cache with unique generated names retrieves the nested
expression paired with every cache entry. -/
theorem nestedAuxFold_find
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnodup : (entries.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ entries) :
    (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = some nested := by
  induction entries generalizing map with
  | nil => simp at hentry
  | cons entry entries ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.mem_cons] at hentry
    simp only [List.foldl_cons]
    rcases hentry with hhead | htail
    · cases hhead
      rw [nestedAuxFold_find_of_not_mem entries _ hnodup.1]
      simp
    · have htailNodup : (entries.map Prod.snd).Nodup := hnodup.2
      have htailFind := ih (map.insert entry.2 entry.1) htailNodup htail
      simpa using htailFind

/-- A successful lookup in a cache fold comes either from the initial map or
from an exact cache entry.  This is the reverse direction of
`nestedAuxFold_find`; unlike that theorem it does not need name uniqueness,
because the value returned by the final insertion is retained exactly. -/
theorem nestedAuxFold_find_mem_or_initial
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hfind : (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = some nested) :
    map[name]? = some nested ∨ (nested, name) ∈ entries := by
  induction entries generalizing map with
  | nil => exact Or.inl hfind
  | cons entry entries ih =>
    simp only [List.foldl_cons] at hfind
    rcases ih (map := map.insert entry.2 entry.1) hfind with
      hinsert | htail
    · rw [Std.TreeMap.getElem?_insert] at hinsert
      split at hinsert
      next hcmp =>
        have hname : entry.2 = name :=
          Std.LawfulEqCmp.compare_eq_iff_eq.mp hcmp
        have hnested : entry.1 = nested := Option.some.inj hinsert
        exact Or.inr (by
          apply List.mem_cons.mpr
          left
          exact Prod.ext hnested.symm hname.symm)
      next => exact Or.inl hinsert
    · exact Or.inr (by simp [htail])

/-- A lookup in a cache fold starting from the empty map therefore
comes from a cache entry. -/
theorem nestedAuxFold_find_mem
    (entries : List (Expr × Name))
    (hfind : (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      ({} : Std.TreeMap Name Expr Name.quickCmp))[name]? = some nested) :
    (nested, name) ∈ entries := by
  rcases nestedAuxFold_find_mem_or_initial entries {} hfind with
    hinitial | hentry
  · simp at hinitial
  · exact hentry

/-- A final restoration map faithfully represents every entry retained in a
nested-lowering state. This isolates the map property needed by local
lowering/restoration proofs from the particular fold that builds the map. -/
def NestedAuxMapModels (result : Lean4Lean.ElimNestedInductive.Result)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux →
    result.aux2nested.find? name = some nested

theorem NestedNewTypesLE.refl (state : Lean4Lean.ElimNestedInductive.State) :
    NestedNewTypesLE state state := ⟨[], by simp⟩

theorem NestedNewTypesLE.trans
    (H₁ : NestedNewTypesLE first middle)
    (H₂ : NestedNewTypesLE middle last) : NestedNewTypesLE first last := by
  rcases H₁ with ⟨xs, hxs⟩
  rcases H₂ with ⟨ys, hys⟩
  exact ⟨xs ++ ys, by simp [hys, hxs, List.append_assoc]⟩

theorem NestedNewTypesLE.mem
    (H : NestedNewTypesLE source target)
    (hentry : entry ∈ source.newTypes) : entry ∈ target.newTypes := by
  rcases H with ⟨suffix, hsuffix⟩
  have hsource : entry ∈ source.newTypes.toList := by simpa using hentry
  have htarget : entry ∈ target.newTypes.toList := by
    rw [hsuffix]
    exact List.mem_append_left suffix hsource
  simpa using htarget

theorem NestedNewTypesLE.getElem
    (H : NestedNewTypesLE source target) (hi : i < source.newTypes.size) :
    ∃ htarget : i < target.newTypes.size,
      target.newTypes[i] = source.newTypes[i] := by
  rcases H with ⟨suffix, hsuffix⟩
  have htarget : i < target.newTypes.size := by
    have hsizes := congrArg List.length hsuffix
    have hlen : target.newTypes.size =
        source.newTypes.size + suffix.length := by simpa using hsizes
    rw [hlen]
    omega
  refine ⟨htarget, ?_⟩
  have hlist : target.newTypes.toList[i] = source.newTypes.toList[i] := by
    simp [hsuffix, hi]
  simpa using hlist

theorem AuxiliaryGenerationStep.newTypesLE
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out) : NestedNewTypesLE state out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  rw [hstate]
  exact ⟨[data.type], by simp⟩

theorem AuxiliaryGenerationStep.nestedAuxLE
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out) : NestedAuxLE state out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  rw [hstate]
  exact ⟨[(data.nested, auxName)], by simp, rfl⟩

theorem AuxiliaryGenerationStep.namesWF
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
  rcases Hfresh.index with ⟨index, hstart, hname, hnext⟩
  rw [hstate]
  have hnot : auxName ∉ state.nestedAux.toList.map Prod.snd := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨nested, oldName⟩, hold, heq⟩
    change oldName = auxName at heq
    rcases Hstate.indexed nested oldName (by simpa using hold) with
      ⟨oldIndex, holdName, holdIndex⟩
    have hsuffix : oldIndex = index := by
      rw [holdName, hname] at heq
      injection heq
    omega
  constructor
  · simp only [Array.toList_push, List.map_append, List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨Hstate.nodup, by simp, ?_⟩
    intro oldName hold newName hnew
    simp only [List.mem_singleton] at hnew
    subst newName
    intro heq
    subst oldName
    exact hnot hold
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · rcases Hstate.indexed nested name hold with
        ⟨oldIndex, holdName, holdIndex⟩
      refine ⟨oldIndex, holdName, ?_⟩
      change oldIndex < nextIdx
      rw [hnext]
      omega
    · cases hnew
      refine ⟨index, hname, ?_⟩
      change index < nextIdx
      rw [hnext]
      omega
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · exact Hstate.reserved nested name hold
    · cases hnew
      rw [hname]
      exact nested_isPrefix_mkNum index

theorem AuxiliaryGenerationStep.namesFresh
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
  rw [hstate]
  intro nested name hentry
  simp only [Array.mem_push] at hentry
  rcases hentry with hold | hnew
  · exact Hstate nested name hold
  · cases hnew
    exact Hfresh.fresh

theorem AuxiliaryGenerationBatch.newTypesLE
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hstep Htail ih => exact Hstep.newTypesLE.trans ih

theorem AuxiliaryGenerationBatch.nestedAuxLE
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hstep Htail ih => exact Hstep.nestedAuxLE.trans ih

theorem AuxiliaryGenerationBatch.namesWF
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih => exact ih (Hstep.namesWF Hstate)

theorem AuxiliaryGenerationBatch.namesFresh
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih => exact ih (Hstep.namesFresh Hstate)

/-- If the target family does not occur in the remaining mutual-family
suffix, that suffix cannot replace the accumulated result. -/
theorem AuxiliaryGenerationBatch.result_eq_of_target_not_mem
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hnot : targetName ∉ sourceNames) : out.1 = result := by
  induction H with
  | nil => rfl
  | @cons sourceName sourceInfo state step result sourceNames out Hstep Htail ih =>
    simp only [List.mem_cons, not_or] at hnot
    rcases Hstep.generated with
      ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
    have hne : sourceName ≠ targetName := Ne.symm hnot.1
    have hstep : step.1 = none := by
      rw [hresult]
      simp [hne]
    have htail := ih hnot.2
    simpa [hstep] using htail

/-- With unique mutual-family names, the batch result is exactly the
auxiliary application generated at the unique target-family step. The same
fresh name remains paired with its source expression in the final cache. -/
theorem AuxiliaryGenerationBatch.targetResult
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hnodup : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name) (nextIdx : Nat)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      FreshNestedName env `_nested stepState.nextIdx
        auxName nextIdx ∧
      AuxiliaryFamilySpec env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      stepState.lvls = state.lvls ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      (data.nested, auxName) ∈ out.2.nestedAux ∧
      data.type ∈ out.2.newTypes := by
  induction H with
  | nil => simp at htarget
  | @cons sourceName sourceInfo state step result sourceNames out Hstep Htail ih =>
    simp only [List.nodup_cons] at hnodup
    simp only [List.mem_cons] at htarget
    rcases htarget with hhead | htail
    · subst sourceName
      rcases Hstep.generated with
        ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstepState⟩
      have hstepResult : step.1 = some (mkAppRange
          (mkAppN (.const auxName state.lvls) As) nparams args.size args) := by
        simpa using hresult
      have hfinal := Htail.result_eq_of_target_not_mem hnodup.1
      refine ⟨state, _, auxName, nextIdx, data, Hfresh, Hbuilt, rfl, ?_, ?_, ?_⟩
      · simpa [hstepResult] using hfinal
      · apply Htail.nestedAuxLE.mem
        rw [hstepState]
        simp
      · apply Htail.newTypesLE.mem
        rw [hstepState]
        simp
    · rcases ih hnodup.2 htail with
        ⟨stepState, sourceInfo, auxName, nextIdx, data, Hfresh, Hbuilt,
          hlevels, hresult, hentry, htype⟩
      rcases Hstep.generated with
        ⟨headAuxName, headNextIdx, headData, headFresh, headBuilt,
          headResult, hstep⟩
      refine ⟨stepState, sourceInfo, auxName, nextIdx, data, Hfresh, Hbuilt,
        ?_, hresult, hentry, htype⟩
      simpa [hstep] using hlevels

/-- `NestedAuxMapModels` turns the unique target step into the exact
`aux2nested` lookup used by restoration, even after later lowering has
appended more cache entries. -/
theorem AuxiliaryGenerationBatch.targetResultMapped
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsourceNames : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      AuxiliaryFamilySpec env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      stepState.lvls = state.lvls ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      finalResult.aux2nested.find? auxName = some data.nested := by
  rcases H.targetResult hsourceNames htarget with
    ⟨stepState, sourceInfo, auxName, _nextIdx, data, _Hfresh, Hbuilt, hlevels,
      hresult, hentry, _htype⟩
  exact ⟨stepState, sourceInfo, auxName, data, Hbuilt, hlevels, hresult,
    Hmap data.nested auxName (Hlater.mem hentry)⟩

/-- Both cache reuse and fresh mutual-family generation expose the same
restoration-facing fact: the returned auxiliary application is keyed in the
final map by the normalized source-family application it replaced. -/
theorem OccurrenceReplacement.resolvedMapping
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ∃ auxName auxLevels nested lowered,
      auxLevels = state.lvls ∧
      out.1 = some lowered ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams args.size args ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract
          As).instantiateRev params) = true ∧
      finalResult.aux2nested.find? auxName = some nested := by
  cases H with
  | cached auxName Hcached =>
    rcases Hcached.entry with
      ⟨⟨found, foundName⟩, hentry, heq, hname⟩
    change foundName = auxName at hname
    rw [hname] at hentry
    refine ⟨auxName, state.lvls, found, _, rfl, rfl, rfl, heq, ?_⟩
    exact Hmap _ auxName (Hlater.mem hentry)
  | generated Hclosure Hbatch =>
    rcases Hbatch.targetResultMapped Hclosure.names Hclosure.target Hlater Hmap
      with ⟨stepState, sourceInfo, auxName, data, Hbuilt, hlevels, hresult,
        hlookup⟩
    refine ⟨auxName, state.lvls, data.nested, _, rfl, hresult, ?_, ?_, hlookup⟩
    · simp [hlevels]
    rw [Hbuilt.nested]
    simp

def NodeReplacementHasResolvedMapping
    (env : Environment) (params As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (finalResult : Lean4Lean.ElimNestedInductive.Result) : Prop :=
    ∃ value targetName levels auxName auxLevels nested,
      NestedOccurrence env state input value ∧
      auxLevels = state.lvls ∧
      input.getAppFn = .const targetName levels ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams input.getAppArgs.size input.getAppArgs ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As).instantiateRev params) = true ∧
      finalResult.aux2nested.find? auxName = some nested

/-- A successful replacement of a nested occurrence, with its cache-or-generation
branch.  Unlike `NodeReplacementHasResolvedMapping`, this retains the
`OccurrenceReplacement` and the state at which it completed.  In the generation branch this
leads back to `AuxiliaryFamilySpec`; cache reuse remains identifiable
and can be joined to the auxiliary families of the final cache (`CachedAuxiliaryFamily`). -/
def NodeReplacementResolved
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (nextState : Lean4Lean.ElimNestedInductive.State)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (finalState : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ value targetName levels,
    NestedOccurrence env state input value ∧
    input.getAppFn = .const targetName levels ∧
    OccurrenceReplacement env lctx params As targetName levels
      input.getAppArgs value state (some lowered, nextState) ∧
    NestedAuxLE nextState finalState ∧
    NestedAuxMapModels finalResult finalState

/-- Forget the cache-or-generation branch, keeping only the resolved mapping into the
final `aux2nested` map. -/
theorem NodeReplacementResolved.mapping
    (H : NodeReplacementResolved env lctx params As input state lowered
      nextState finalResult finalState) :
    NodeReplacementHasResolvedMapping env params As input state lowered
      finalResult := by
  rcases H with
    ⟨value, targetName, levels, Hcandidate, hhead, Hrecognized, Hlater, Hmap⟩
  rcases Hrecognized.resolvedMapping Hlater Hmap with
    ⟨auxName, auxLevels, nested, replacement, hauxLevels, hresult, hreplacement,
      hnested, hlookup⟩
  cases hresult
  exact ⟨value, targetName, levels, auxName, auxLevels, nested, Hcandidate,
    hauxLevels, hhead, hreplacement, hnested, hlookup⟩

/-- A mapped replacement introduces only its selected parameter variables;
all trailing arguments are inherited from the source application. -/
theorem NodeReplacementHasResolvedMapping.outputFVarsIn
    (H : NodeReplacementHasResolvedMapping env params As input state
      lowered finalResult)
    (Hselection : CDeclArray lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    lowered.FVarIdsIn (· ∈ Hselection.fvars) := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, _hauxLevels, hhead, hlowered, hnested, hlookup⟩
  have HAs : ∀ arg ∈ As.toList,
      arg.FVarIdsIn (· ∈ Hselection.fvars) := by
    intro arg harg
    rw [Hselection.expressions] at harg
    rcases List.mem_map.mp harg with ⟨fv, hfv, rfl⟩
    simpa [Expr.FVarIdsIn] using hfv
  rw [hlowered]
  rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
  apply Expr.FVarIdsIn.mkAppList.mpr
  constructor
  · rw [Expr.mkAppN_eq_mkAppList]
    exact Expr.FVarIdsIn.mkAppList.mpr
      ⟨by simp [Expr.FVarIdsIn], HAs⟩
  · intro arg harg
    apply Hinput.getAppArgsList
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop harg

theorem NodeReplacementResolved.outputFVarsIn
    (H : NodeReplacementResolved env lctx params As input state lowered
      nextState finalResult finalState)
    (Hselection : CDeclArray lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    lowered.FVarIdsIn (· ∈ Hselection.fvars) :=
  H.mapping.outputFVarsIn Hselection Hinput

/-- A mapped lowering leaf after reopening its cached source application with
the parameter array chosen by restoration. -/
def NodeReplacementReopens
    (env : Environment) (As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) : Prop :=
  ∃ value targetName levels auxName auxLevels nested,
    NestedOccurrence env state input value ∧
    input.getAppFn = .const targetName levels ∧
    lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
      value.numParams input.getAppArgs.size input.getAppArgs ∧
    finalResult.aux2nested.find? auxName = some nested ∧
    (((nested.abstract finalResult.params).instantiateRev restoreAs) ==
      ((mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs).abstract As).instantiateRev restoreAs) = true

/-- A reopened replacement is interpreted by the concrete family branch of
`restoreNestedNode`.  The auxiliary parameter prefix is discarded and the
reopened source-family prefix is reattached to the identically renamed
non-parameter arguments, yielding the renamed source application up to
expression equivalence.  The statement is at an arbitrary binder depth `k`
because the occurrence may sit below binders of the constructor body; only the
closed parameter prefix is compared with the depth-zero array operation. -/
theorem NodeReplacementReopens.restoreNode
    (H : NodeReplacementReopens env As input state lowered
      finalResult restoreAs)
    (restoreEnv : Environment)
    (Hselection : CDeclArray lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size) (k : Nat) :
    ∃ restored,
      finalResult.restoreNestedNode restoreEnv restoreAs {}
          (Expr.reopenFVarsAt lowered Hselection.fvars restoreFvars k) =
        some restored ∧
      (restored ==
        Expr.reopenFVarsAt input Hselection.fvars restoreFvars k) = true := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hlookup, hreopens⟩
  let R : Expr → Expr := fun e =>
    Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
  let trailing : List Expr :=
    input.getAppArgsList.drop value.numParams |>.map R
  let paramPrefix : List Expr := As.toList.map R
  have hloweredReopened : R lowered =
      Expr.mkAppList (.const auxName auxLevels) (paramPrefix ++ trailing) := by
    rw [hlowered]
    rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    rw [Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
    change Expr.reopenFVarsAt _ Hselection.fvars restoreFvars k = _
    rw [Expr.reopenFVarsAt_mkAppList, Expr.reopenFVarsAt_const]
    simp [R, paramPrefix, trailing, Expr.getAppArgs_toList]
  have hfn : (R lowered).getAppFn = .const auxName auxLevels := by
    rw [hloweredReopened]
    exact Expr.getAppFn_mkAppList_const auxName auxLevels _
  have hargsList : (R lowered).getAppArgsList = paramPrefix ++ trailing := by
    rw [hloweredReopened]
    exact Expr.getAppArgsList_mkAppList_const auxName auxLevels _
  have hargs : (R lowered).getAppArgs = (paramPrefix ++ trailing).toArray := by
    rw [Expr.getAppArgs_eq, hargsList]
  have hprefixLength : paramPrefix.length = finalResult.nparams := by
    simp [paramPrefix, hresultNParams]
  have harity : finalResult.nparams ≤ (R lowered).getAppArgs.size := by
    rw [hargs]
    simp [hprefixLength]
  have hnode := restoreNestedNode_family_general finalResult restoreEnv
    restoreAs {}
    (R lowered) nested auxName auxLevels hfn (by rfl) hlookup harity
  have hrestored :
      mkAppRange ((nested.abstract finalResult.params).instantiateRev restoreAs)
          finalResult.nparams (R lowered).getAppArgs.size
          (R lowered).getAppArgs =
        Expr.mkAppList
          ((nested.abstract finalResult.params).instantiateRev restoreAs)
          trailing := by
    rw [Expr.mkAppRange_to_end _ _ _ harity, hargs]
    simp [hprefixLength]
  refine ⟨Expr.mkAppList
      ((nested.abstract finalResult.params).instantiateRev restoreAs)
      trailing, ?_, ?_⟩
  · rw [hrestored] at hnode
    simpa only [R] using hnode
  · have hprefixSource :
        R (mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs) =
          Expr.mkAppList (.const targetName levels)
            (input.getAppArgsList.take value.numParams |>.map R) := by
      rw [Expr.mkAppRange_from_zero _ _ _ Hcandidate.parameters.arity]
      change Expr.reopenFVarsAt _ Hselection.fvars restoreFvars k = _
      rw [Expr.reopenFVarsAt_mkAppList, Expr.reopenFVarsAt_const]
      simp [R, Expr.getAppArgs_toList]
    have hprefixExact :
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As).instantiateRev restoreAs =
        R (mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs) := by
      change Expr.reopenParams _ As restoreAs = _
      symm
      exact Expr.reopenFVarsAt_eq_reopenParams hnd hsize Hselection.expressions
        hrestore _ k (Hcandidate.prefixLooseBVarRange_zero _ rfl)
    rw [hprefixExact] at hreopens
    have happended := Expr.mkAppList_eqv hreopens trailing
    rw [hprefixSource] at happended
    have hinput : R input =
        Expr.mkAppList (.const targetName levels)
          (input.getAppArgsList.map R) :=
      Expr.reopenFVarsAt_of_getAppFn_const Hselection.fvars restoreFvars k hhead
    rw [← Expr.mkAppList_append] at happended
    simp only [trailing] at happended
    rw [List.map_take, List.map_drop, List.take_append_drop] at happended
    simpa [hinput, trailing, R] using happended

/-- The final-map lookup retained at a replacement is a left inverse for
the abstraction/reopening part of `restoreNestedNode`.  The only local
scoping premise is that abstracting the constructor-opening parameters has
removed all free variables; constructor lowering establishes that fact from
its closed source type. -/
theorem NodeReplacementHasResolvedMapping.reopens
    (H : NodeReplacementHasResolvedMapping env params As input state
      lowered finalResult)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : CDeclArray lctx As)
    (hAs : Hselection.fvars.length ≤ fvars.length)
    (hclosed : ∀ value targetName levels,
      NestedOccurrence env state input value →
      input.getAppFn = .const targetName levels →
      FVarsIn (fun _ => False)
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As)) :
    NodeReplacementReopens env As input state lowered
      finalResult restoreAs := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, _hauxLevels, hhead, hlowered, hnested, hlookup⟩
  let base := (mkAppRange (.const targetName levels) 0 value.numParams
    input.getAppArgs).abstract As
  have habstract :
      (nested.abstract params) ==
        ((base.instantiateRev params).abstract params) := by
    rw [hparams, Expr.abstractN_eq, Expr.abstractN_eq]
    apply Expr.abstractN_eqv
    simpa [base, hparams] using hnested
  have heqv :
      ((nested.abstract finalResult.params).instantiateRev restoreAs) ==
        (((base.instantiateRev params).abstract params).instantiateRev
          restoreAs) := by
    rw [hresultParams, Expr.instantiateRev_eq, Expr.instantiate_eq,
      Expr.instantiateRev_eq, Expr.instantiate_eq]
    exact Expr.instantiateList_eqv habstract
  refine ⟨value, targetName, levels, auxName, auxLevels, nested, Hcandidate,
    hhead, hlowered, hlookup, ?_⟩
  have hfree : FVarsIn (fun fv => fv ∉ fvars) base :=
    (hclosed value targetName levels Hcandidate hhead).mono
      fun fv hfalse => False.elim hfalse
  have hlb : base.looseBVarRange' ≤ fvars.length := by
    have hprefix := Hcandidate.prefixLooseBVarRange_zero (.const targetName levels) rfl
    have hbound := Expr.abstractN_looseBVarRange_le
      (e := mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs) (fvs := Hselection.fvars) (k := 0)
    rw [hprefix] at hbound
    simp only [base, Hselection.expressions, Expr.abstractN_eq]
    omega
  have hcancel := hfree.reabstract_instantiateRev_fvarArray
    params restoreAs fvars hparams hnodup hlb
  rw [hcancel] at heqv
  exact heqv

/-- A recognized nested application's source-family prefix becomes closed
once all constructor-opening free variables are abstracted. -/
theorem NestedOccurrence.abstractedPrefixClosed
    (H : NestedOccurrence env state input value)
    (Hselection : CDeclArray lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input)
    (hhead : input.getAppFn = .const targetName levels) :
    FVarsIn (fun _ => False)
      ((mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs).abstract As) := by
  apply FVarsIn.abstract_fvarArray_of Hselection.fvars As
    Hselection.expressions
  apply FVarsIn.mkAppRange_zero H.parameters.arity
  · have Hfn := Hinput.getAppFn
    rw [hhead] at Hfn
    exact Hfn
  · intro arg harg
    have harg' : arg ∈ input.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    exact (Hinput.getAppArgsList harg').mono fun fv hfv => Or.inl hfv

/-- Constructor-scoped specialization of `reopens`; the closedness premise
is derived from the source body's free-variable invariant. -/
theorem NodeReplacementHasResolvedMapping.reopensOfFVars
    (H : NodeReplacementHasResolvedMapping env params As input state
      lowered finalResult)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : CDeclArray lctx As)
    (hAs : Hselection.fvars.length ≤ fvars.length)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    NodeReplacementReopens env As input state lowered
      finalResult restoreAs := by
  apply H.reopens hresultParams fvars hparams hnodup Hselection hAs
  intro value targetName levels Hcandidate hhead
  exact Hcandidate.abstractedPrefixClosed Hselection Hinput hhead

theorem NodeReplacementResolved.reopensOfFVars
    (H : NodeReplacementResolved env lctx params As input state lowered
      nextState finalResult finalState)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : CDeclArray lctx As)
    (hAs : Hselection.fvars.length ≤ fvars.length)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    NodeReplacementReopens env As input state lowered
      finalResult restoreAs :=
  H.mapping.reopensOfFVars hresultParams fvars hparams hnodup Hselection hAs
    Hinput

/-- Successful node replacement with its cache-or-generation branch retained
verbatim. -/
theorem NodeReplacement.resolvedTrace
    (H : NodeReplacement env lctx params As input state
      (some lowered, nextState))
    (Hlater : NestedAuxLE nextState finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    NodeReplacementResolved env lctx params As input state lowered
      nextState finalResult finalState := by
  cases H with
  | recognized Hcandidate hhead Hrecognized =>
    exact ⟨_, _, _, Hcandidate, hhead, Hrecognized, Hlater, Hmap⟩

/-- Structural expression-lowering relation whose successful leaves are
already connected to the final restoration map. Unlike `ExprLowering`,
this relation forgets monadic control flow and retains exactly the
information needed to interpret the lowered expression. -/
inductive ExprLowering.Resolved
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | occurrence : NodeReplacementResolved env lctx params As input state output
      nextState finalResult finalState →
      ExprLowering.Resolved env lctx params As finalResult input state
        (output, nextState)
  | bvar : NodeReplacement env lctx params As (.bvar i) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult (.bvar i) state
      (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NodeReplacement env lctx params As (.fvar fvarId) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult
      (.fvar fvarId) state (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NodeReplacement env lctx params As (.mvar mvarId) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult
      (.mvar mvarId) state (.mvar mvarId, state)
  | sort : NodeReplacement env lctx params As (.sort level) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult (.sort level) state
      (.sort level, state)
  | const : NodeReplacement env lctx params As (.const name levels) state
      (none, state) → ExprLowering.Resolved env lctx params As finalResult
      (.const name levels) state (.const name levels, state)
  | lit : NodeReplacement env lctx params As (.lit literal) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult (.lit literal) state
      (.lit literal, state)
  | app : NodeReplacement env lctx params As (.app fn arg) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult fn state
      (fn', fnState) →
      ExprLowering.Resolved env lctx params As finalResult arg fnState
        (arg', outState) →
      ExprLowering.Resolved env lctx params As finalResult (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NodeReplacement env lctx params As (.lam name dom body bi) state
      (none, state) → ExprLowering.Resolved env lctx params As finalResult dom state
      (dom', domState) →
      ExprLowering.Resolved env lctx params As finalResult body domState
        (body', outState) →
      ExprLowering.Resolved env lctx params As finalResult (.lam name dom body bi)
        state (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NodeReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult dom state
      (dom', domState) →
      ExprLowering.Resolved env lctx params As finalResult body domState
        (body', outState) →
      ExprLowering.Resolved env lctx params As finalResult
        (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NodeReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      ExprLowering.Resolved env lctx params As finalResult type state
      (type', typeState) →
      ExprLowering.Resolved env lctx params As finalResult value typeState
        (value', valueState) →
      ExprLowering.Resolved env lctx params As finalResult body valueState
        (body', outState) →
      ExprLowering.Resolved env lctx params As finalResult
        (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NodeReplacement env lctx params As (.mdata data body) state
      (none, state) → ExprLowering.Resolved env lctx params As finalResult body state
      (body', outState) →
      ExprLowering.Resolved env lctx params As finalResult (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NodeReplacement env lctx params As (.proj name idx body) state
      (none, state) → ExprLowering.Resolved env lctx params As finalResult body state
      (body', outState) →
      ExprLowering.Resolved env lctx params As finalResult (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Nested lowering preserves free-variable-ID scoping. Replaced occurrences use
`outputFVarsIn`; other nodes inherit the property componentwise. -/
theorem ExprLowering.Resolved.outputFVarIdsIn
    (H : ExprLowering.Resolved env lctx params As finalResult input state out)
    (Hselection : CDeclArray lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    out.1.FVarIdsIn (· ∈ Hselection.fvars) := by
  induction H with
  | occurrence Hnode => exact Hnode.outputFVarsIn Hselection Hinput
  | bvar | fvar | mvar | sort | const | lit => exact Hinput
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateApp!, Expr.FVarIdsIn] using
      And.intro (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateLambdaE!, Expr.FVarIdsIn] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateForallE!, Expr.FVarIdsIn] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateLet!, Expr.FVarIdsIn] using
      And.intro (ihType Hinput.1)
        (And.intro (ihValue Hinput.2.1) (ihBody Hinput.2.2))
  | mdata Hnode Hbody ihBody =>
    simpa [Expr.updateMData!, Expr.FVarIdsIn] using ihBody Hinput
  | proj Hnode Hbody ihBody =>
    simpa [Expr.updateProj!, Expr.FVarIdsIn] using ihBody Hinput



/-- Nested lowering preserves bound-variable closedness at every depth: a
replacement swaps a closed parameter prefix for an auxiliary head applied to the
copied parameter variables, and other nodes recurse componentwise. -/
theorem ExprLowering.Resolved.closed
    (H : ExprLowering.Resolved env lctx params As finalResult input state out)
    (Hselection : CDeclArray lctx As)
    (Hinput : Closed input k) : Closed out.1 k := by
  induction H generalizing k with
  | occurrence Hnode =>
    rcases Hnode.mapping with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, _hauxLevels, hhead, hlowered, hnested, hlookup⟩
    rw [hlowered, Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    apply Closed.mkAppList_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Expr.mkAppN_eq_mkAppList]
      apply Closed.mkAppList_iff.mpr
      refine ⟨trivial, ?_⟩
      intro arg harg
      rw [Hselection.expressions] at harg
      rcases List.mem_map.mp (by simpa using harg) with ⟨fv, _, rfl⟩
      trivial
    · intro arg harg
      apply Hinput.getAppArgsList_at
      rw [← Expr.getAppArgs_toList]
      exact List.mem_of_mem_drop harg
  | bvar | fvar | mvar | sort | const | lit => exact Hinput
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Closed] at Hinput
    simpa [Expr.updateApp!, Closed] using
      And.intro (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Closed] at Hinput
    simpa [Expr.updateLambdaE!, Closed] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Closed] at Hinput
    simpa [Expr.updateForallE!, Closed] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Closed] at Hinput
    simpa [Expr.updateLet!, Closed] using
      And.intro (ihType Hinput.1)
        (And.intro (ihValue Hinput.2.1) (ihBody Hinput.2.2))
  | mdata Hnode Hbody ihBody =>
    simpa [Expr.updateMData!, Closed] using ihBody Hinput
  | proj Hnode Hbody ihBody =>
    simpa [Expr.updateProj!, Closed] using ihBody Hinput

/-- Structural lowering map with every successful leaf upgraded to its
parameter-reopening certificate. -/
inductive ExprLowering.Reopened
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | occurrence : NodeReplacementReopens env As input state output
      finalResult restoreAs →
      ExprLowering.Reopened env lctx params As finalResult restoreAs input state
        (output, nextState)
  | bvar : NodeReplacement env lctx params As (.bvar i) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
      (.bvar i) state (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NodeReplacement env lctx params As (.fvar fvarId) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.fvar fvarId) state (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NodeReplacement env lctx params As (.mvar mvarId) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.mvar mvarId) state (.mvar mvarId, state)
  | sort : NodeReplacement env lctx params As (.sort level) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
      (.sort level) state (.sort level, state)
  | const : NodeReplacement env lctx params As (.const name levels) state
      (none, state) → ExprLowering.Reopened env lctx params As finalResult restoreAs
      (.const name levels) state (.const name levels, state)
  | lit : NodeReplacement env lctx params As (.lit literal) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
      (.lit literal) state (.lit literal, state)
  | app : NodeReplacement env lctx params As (.app fn arg) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs fn state
      (fn', fnState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs arg fnState
        (arg', outState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NodeReplacement env lctx params As (.lam name dom body bi) state
      (none, state) → ExprLowering.Reopened env lctx params As finalResult restoreAs dom state
      (dom', domState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs body domState
        (body', outState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.lam name dom body bi) state
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NodeReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs dom
      state (dom', domState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs body domState
        (body', outState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NodeReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs type state
      (type', typeState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs value typeState
        (value', valueState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs body valueState
        (body', outState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NodeReplacement env lctx params As (.mdata data body) state
      (none, state) → ExprLowering.Reopened env lctx params As finalResult restoreAs body state
      (body', outState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NodeReplacement env lctx params As (.proj name idx body) state
      (none, state) → ExprLowering.Reopened env lctx params As finalResult restoreAs body state
      (body', outState) →
      ExprLowering.Reopened env lctx params As finalResult restoreAs
        (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Leafwise reopening certificates also preserve bound-variable closedness
at every depth. -/
theorem ExprLowering.Reopened.closed
    (H : ExprLowering.Reopened env lctx params As finalResult restoreAs input
      state out)
    (Hselection : CDeclArray lctx As)
    (Hinput : Closed input k) : Closed out.1 k := by
  induction H generalizing k with
  | occurrence Hnode =>
    rcases Hnode with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, hhead, hlowered, hlookup, hreopens⟩
    rw [hlowered, Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    apply Closed.mkAppList_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Expr.mkAppN_eq_mkAppList]
      apply Closed.mkAppList_iff.mpr
      refine ⟨trivial, ?_⟩
      intro arg harg
      rw [Hselection.expressions] at harg
      rcases List.mem_map.mp (by simpa using harg) with ⟨fv, _, rfl⟩
      trivial
    · intro arg harg
      apply Hinput.getAppArgsList_at
      rw [← Expr.getAppArgs_toList]
      exact List.mem_of_mem_drop harg
  | bvar | fvar | mvar | sort | const | lit => exact Hinput
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Closed] at Hinput
    simpa [Expr.updateApp!, Closed] using
      And.intro (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Closed] at Hinput
    simpa [Expr.updateLambdaE!, Closed] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Closed] at Hinput
    simpa [Expr.updateForallE!, Closed] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Closed] at Hinput
    simpa [Expr.updateLet!, Closed] using
      And.intro (ihType Hinput.1)
        (And.intro (ihValue Hinput.2.1) (ihBody Hinput.2.2))
  | mdata Hnode Hbody ihBody =>
    simpa [Expr.updateMData!, Closed] using ihBody Hinput
  | proj Hnode Hbody ihBody =>
    simpa [Expr.updateProj!, Closed] using ihBody Hinput

/-- Lift a complete expression mapping to leafwise reopening.  Source
free-variable scoping is split structurally in exactly the same way as the
lowering traversal. -/
theorem ExprLowering.Resolved.reopens
    (H : ExprLowering.Resolved env lctx params As finalResult input state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : CDeclArray lctx As)
    (hAs : Hselection.fvars.length ≤ fvars.length)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    ExprLowering.Reopened env lctx params As finalResult restoreAs input state
      out := by
  induction H with
  | occurrence Hnode =>
    exact .occurrence (Hnode.reopensOfFVars hresultParams fvars hparams hnodup
      Hselection hAs Hinput)
  | bvar Hnode => exact .bvar Hnode
  | fvar Hnode => exact .fvar Hnode
  | mvar Hnode => exact .mvar Hnode
  | sort Hnode => exact .sort Hnode
  | const Hnode => exact .const Hnode
  | lit Hnode => exact .lit Hnode
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .app Hnode (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .lam Hnode (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .forallE Hnode (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .letE Hnode (ihType Hinput.1) (ihValue Hinput.2.1)
      (ihBody Hinput.2.2)
  | mdata Hnode Hbody ihBody =>
    exact .mdata Hnode (ihBody Hinput)
  | proj Hnode Hbody ihBody =>
    exact .proj Hnode (ihBody Hinput)

/-- A reopened lowering cannot introduce a constant application head
unless the root itself was recognized. In the application case, maximality
rules out a recognized function prefix whenever the parent is certified not to be
a nested occurrence. -/
theorem ExprLowering.Reopened.constHead_of_noCandidate
    (H : ExprLowering.Reopened env lctx params As finalResult restoreAs input
      state out)
    (Hmiss : NotNestedOccurrence env state input)
    (Hhead : out.1.getAppFn = .const name levels) :
    input.getAppFn = .const name levels := by
  induction H with
  | occurrence Hnode =>
    rcases Hnode with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, hhead, hlowered, hlookup, hreopens⟩
    exact False.elim (Hmiss value Hcandidate)
  | bvar | fvar | mvar | sort | const | lit => exact Hhead
  | @app fn arg state fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have HfnMiss : NotNestedOccurrence env state fn := by
      intro info Hcandidate
      exact Hmiss info (Hcandidate.app arg)
    apply ihFn HfnMiss
    simpa [Expr.getAppFn] using Hhead
  | lam => simp [Expr.getAppFn] at Hhead
  | forallE => simp [Expr.getAppFn] at Hhead
  | letE => simp [Expr.getAppFn] at Hhead
  | mdata => simp [Expr.getAppFn] at Hhead
  | proj => simp [Expr.getAppFn] at Hhead

/-- The constant-head reflection theorem remains true after the constructor
parameters have been renamed at an arbitrary binder depth. -/
theorem ExprLowering.Reopened.reopenedConstHead_of_noCandidate
    (H : ExprLowering.Reopened env lctx params As finalResult restoreAs input
      state out)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (Hmiss : NotNestedOccurrence env state input)
    (Hhead : (Expr.reopenFVarsAt out.1 fvars restoreFvars k).getAppFn =
      .const name levels) :
    input.getAppFn = .const name levels := by
  apply H.constHead_of_noCandidate Hmiss
  exact Expr.getAppFn_reopenFVarsAt_eq_const hnd hsize out.1 k Hhead

/-- At a structural lowering node, restoration must miss the node itself.
The proof uses recognition maximality for the lowered head and source-map
disjointness for the corresponding source constant. -/
theorem ExprLowering.Reopened.restoreNode_none
    (H : ExprLowering.Reopened env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (Hmiss : NotNestedOccurrence env state input)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input) (k : Nat) :
    finalResult.restoreNestedNode restoreEnv targetAs {}
      (Expr.reopenFVarsAt out.1 fvars restoreFvars k) = none := by
  generalize ht : Expr.reopenFVarsAt out.1 fvars restoreFvars k = t
  cases t with
  | const name levels =>
    have hsourceHead : input.getAppFn = .const name levels :=
      H.reopenedConstHead_of_noCandidate hnd hsize Hmiss (by
        rw [ht]
        rfl)
    have hdisjoint := Hsource.getAppFn hsourceHead
    have hrec : ({} : NameMap Name).find? name = none := rfl
    simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn, hrec, hdisjoint.1, hdisjoint.2]
  | app fn arg =>
    cases hhead : (Expr.app fn arg).getAppFn with
    | const name levels =>
      simp only [Expr.getAppFn] at hhead
      have hsourceHead : input.getAppFn = .const name levels :=
        H.reopenedConstHead_of_noCandidate hnd hsize Hmiss (by
          rw [ht]
          exact hhead)
      have hdisjoint := Hsource.getAppFn hsourceHead
      simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        Expr.getAppFn, hhead, hdisjoint.1, hdisjoint.2]
    | bvar | fvar | mvar | sort | app | lam | forallE | letE | lit | mdata
        | proj =>
      simp only [Expr.getAppFn] at hhead
      simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        Expr.getAppFn, hhead]
  | bvar | fvar | mvar | sort | lam | forallE | letE | lit | mdata | proj =>
    simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn]

/-- Restoring a completely lowered expression is a left inverse, up to Lean
expression equivalence, of the nested-expression traversal. The proof follows
the same top-down stopping rule as `Expr.replace`: replaced occurrences restore
immediately, while other nodes recurse through the renamed children. -/
theorem ExprLowering.Reopened.restore_eqv
    (H : ExprLowering.Reopened env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : CDeclArray lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat) :
    ((Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
      Expr.reopenFVarsAt input Hselection.fvars restoreFvars k) = true := by
  induction H generalizing k with
  | @occurrence hitInput hitState hitOutput nextState Hnode =>
    rcases Hnode.restoreNode restoreEnv Hselection hnd restoreFvars hrestore
        hsize hresultNParams k with
      ⟨restored, hrestored, heqv⟩
    rw [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hrestored]
    exact heqv
  | bvar Hnode =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.bvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    rw [Expr.reopenFVarsAt_bvar hsize] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | fvar Hnode =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.fvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    rcases Expr.reopenFVarsAt_fvar_exists hnd hsize _ k with
      ⟨restored, hopen⟩
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @mvar stepState id Hnode =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.mvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.mvar id) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @sort level stepState Hnode =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.sort Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.sort level) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @const name levels stepState Hnode =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.const Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.const name levels) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @lit literal stepState Hnode =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.lit Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.lit literal) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @app fn arg stepState fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.app Hnode Hfn Harg) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateApp! (.app fn arg) fn' arg') =
        .app (R fn') (R arg') := by
      simp [R, Expr.reopenFVarsAt]
    have hinput : R (.app fn arg) = .app (R fn) (R arg) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateApp! (.app fn arg) fn' arg')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.app fn arg)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateApp! (.app fn arg) fn' arg')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def]
    rw [hnone]
    have hfn := ihFn Hsource.1 k
    have harg := ihArg Hsource.2 k
    rw [Expr.replace_eq] at hfn harg
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R fn') == R fn) = true) at hfn
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R arg') == R arg) = true) at harg
    exact Expr.app_eqv hfn harg
  | @lam name dom body bi stepState dom' domState body' outState
      Hnode Hdom Hbody ihDom ihBody =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.lam Hnode Hdom Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body') =
        .lam name (R0 dom') (R1 body') bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.lam name dom body bi) =
        .lam name (R0 dom) (R1 body) bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R0 (.lam name dom body bi)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body')) = none
        at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hdom := ihDom Hsource.1 k
    have hbody := ihBody Hsource.2 (k + 1)
    rw [Expr.replace_eq] at hdom hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 dom') == R0 dom) = true) at hdom
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.lam_eqv hdom hbody
  | @forallE name dom body bi stepState dom' domState body' outState
      Hnode Hdom Hbody ihDom ihBody =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.forallE Hnode Hdom Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body') =
        .forallE name (R0 dom') (R1 body') bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.forallE name dom body bi) =
        .forallE name (R0 dom) (R1 body) bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R0 (.forallE name dom body bi)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body')) = none
        at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hdom := ihDom Hsource.1 k
    have hbody := ihBody Hsource.2 (k + 1)
    rw [Expr.replace_eq] at hdom hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 dom') == R0 dom) = true) at hdom
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.forallE_eqv hdom hbody
  | @letE name type value body nondep stepState type' typeState value'
      valueState body' outState Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.letE Hnode Htype Hvalue Hbody) restoreEnv hnd hsize
        Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateLet! (.letE name type value body nondep)
        type' value' body' nondep) =
        .letE name (R0 type') (R0 value') (R1 body') nondep := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.letE name type value body nondep) =
        .letE name (R0 type) (R0 value) (R1 body) nondep := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateLet! (.letE name type value body nondep)
      type' value' body' nondep)).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
      R0 (.letE name type value body nondep)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateLet! (.letE name type value body nondep)
        type' value' body' nondep)) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have htype := ihType Hsource.1 k
    have hvalue := ihValue Hsource.2.1 k
    have hbody := ihBody Hsource.2.2 (k + 1)
    rw [Expr.replace_eq] at htype hvalue hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 type') == R0 type) = true) at htype
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 value') == R0 value) = true) at hvalue
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.letE_eqv htype hvalue hbody
  | @mdata data body stepState body' outState Hnode Hbody ihBody =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.mdata Hnode Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateMData! (.mdata data body) body') =
        .mdata data (R body') := by simp [R, Expr.reopenFVarsAt]
    have hinput : R (.mdata data body) = .mdata data (R body) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateMData! (.mdata data body) body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.mdata data body)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateMData! (.mdata data body) body')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hbody := ihBody Hsource k
    rw [Expr.replace_eq] at hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R body') == R body) = true) at hbody
    exact Expr.mdata_eqv data hbody
  | @proj name idx body stepState body' outState Hnode Hbody ihBody =>
    have hnone := ExprLowering.Reopened.restoreNode_none (targetAs := targetAs)
      (.proj Hnode Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateProj! (.proj name idx body) body') =
        .proj name idx (R body') := by simp [R, Expr.reopenFVarsAt]
    have hinput : R (.proj name idx body) = .proj name idx (R body) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateProj! (.proj name idx body) body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.proj name idx body)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateProj! (.proj name idx body) body')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hbody := ihBody Hsource k
    rw [Expr.replace_eq] at hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R body') == R body) = true) at hbody
    exact Expr.proj_eqv hbody

theorem OccurrenceReplacement.auxFVarsIn
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (HAs : CDeclArray lctx As)
    (hnparams : value.numParams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch =>
    exact Hbatch.auxFVarsIn HAs hnparams Hlevels Hargs Hparams Hstate

theorem NodeReplacement.auxFVarsIn
    (H : NodeReplacement env lctx params As e state out)
    (HAs : CDeclArray lctx As)
    (Hinput : e.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | @recognized value targetName levels out Hcandidate hhead Hresult =>
    apply Hresult.auxFVarsIn HAs Hcandidate.parameters.arity
    · have Hfn := Hinput.getAppFn
      rw [hhead] at Hfn
      simpa [Lean4Lean.FVarsIn] using Hfn
    · intro arg harg
      apply Hinput.getAppArgsList
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    · exact Hparams
    · exact Hstate

theorem OccurrenceReplacement.pendingNewTypesClosed
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch =>
    exact Hbatch.pendingNewTypesClosed Henv Hclosing Hlevels Hargs Hstate

theorem NodeReplacement.pendingNewTypesClosed
    (H : NodeReplacement env lctx params As e state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hinput : e.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | @recognized value targetName levels out Hcandidate hhead Hresult =>
    apply Hresult.pendingNewTypesClosed Henv Hclosing
    · have Hfn := Hinput.getAppFn
      rw [hhead] at Hfn
      simpa [Lean4Lean.FVarsIn] using Hfn
    · intro arg harg
      apply Hinput.getAppArgsList
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    · exact Hstate

theorem OccurrenceReplacement.newTypesLE
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out) : NestedNewTypesLE state out.2 := by
  cases H with
  | cached => exact .refl _
  | generated _ Hbatch => exact Hbatch.newTypesLE

theorem OccurrenceReplacement.nestedAuxLE
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out) : NestedAuxLE state out.2 := by
  cases H with
  | cached => exact .refl _
  | generated _ Hbatch => exact Hbatch.nestedAuxLE

theorem OccurrenceReplacement.namesWF
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch => exact Hbatch.namesWF Hstate

theorem OccurrenceReplacement.namesFresh
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch => exact Hbatch.namesFresh Hstate

theorem NodeReplacement.newTypesLE
    (H : NodeReplacement env lctx params As e state out) :
    NestedNewTypesLE state out.2 := by
  cases H with
  | unrecognized => exact .refl _
  | recognized _ _ Hresult => exact Hresult.newTypesLE

theorem NodeReplacement.nestedAuxLE
    (H : NodeReplacement env lctx params As e state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | unrecognized => exact .refl _
  | recognized _ _ Hresult => exact Hresult.nestedAuxLE

theorem NodeReplacement.namesWF
    (H : NodeReplacement env lctx params As e state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | recognized _ _ Hresult => exact Hresult.namesWF Hstate

theorem NodeReplacement.namesFresh
    (H : NodeReplacement env lctx params As e state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | recognized _ _ Hresult => exact Hresult.namesFresh Hstate

theorem ExprLowering.newTypesLE
    (H : ExprLowering env lctx params As e state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | occurrence Hnode => exact Hnode.newTypesLE
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app Hnode _ _ ihFn ihArg =>
    exact Hnode.newTypesLE.trans (ihFn.trans ihArg)
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact Hnode.newTypesLE.trans (ihDom.trans ihBody)
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact Hnode.newTypesLE.trans (ihType.trans (ihValue.trans ihBody))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact Hnode.newTypesLE.trans ihBody

theorem ExprLowering.nestedAuxLE
    (H : ExprLowering env lctx params As e state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | occurrence Hnode => exact Hnode.nestedAuxLE
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app Hnode _ _ ihFn ihArg =>
    exact Hnode.nestedAuxLE.trans (ihFn.trans ihArg)
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact Hnode.nestedAuxLE.trans (ihDom.trans ihBody)
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact Hnode.nestedAuxLE.trans (ihType.trans (ihValue.trans ihBody))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact Hnode.nestedAuxLE.trans ihBody

/-- A successful replacement leaves the universe arguments `lvls` of the
lowering state unchanged. -/
theorem NodeReplacementResolved.lvls
    (H : NodeReplacementResolved env lctx params As input state lowered
      nextState finalResult finalState) : nextState.lvls = state.lvls := by
  rcases H with ⟨_, _, _, _, _, Hrecognized, _, _⟩
  exact Hrecognized.nestedAuxLE.lvls

/-- The resolved expression lowering leaves the universe arguments `lvls` of
the lowering state unchanged. -/
theorem ExprLowering.Resolved.lvls
    (H : ExprLowering.Resolved env lctx params As finalResult input state out) :
    out.2.lvls = state.lvls := by
  induction H with
  | occurrence Hnode => exact Hnode.lvls
  | bvar | fvar | mvar | sort | const | lit => rfl
  | app _ _ _ ihFn ihArg => exact ihArg.trans ihFn
  | lam _ _ _ ihDom ihBody | forallE _ _ _ ihDom ihBody => exact ihBody.trans ihDom
  | letE _ _ _ _ ihType ihValue ihBody => exact ihBody.trans (ihValue.trans ihType)
  | mdata _ _ ihBody | proj _ _ ihBody => exact ihBody

theorem ExprLowering.namesWF
    (H : ExprLowering env lctx params As e state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | occurrence Hnode => exact Hnode.namesWF Hstate
  | bvar | fvar | mvar | sort | const | lit => exact Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    exact ihArg (ihFn (Hnode.namesWF Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesWF Hstate))
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesWF Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.namesWF Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody (Hnode.namesWF Hstate)

theorem ExprLowering.namesFresh
    (H : ExprLowering env lctx params As e state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | occurrence Hnode => exact Hnode.namesFresh Hstate
  | bvar | fvar | mvar | sort | const | lit => exact Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    exact ihArg (ihFn (Hnode.namesFresh Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesFresh Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.namesFresh Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody (Hnode.namesFresh Hstate)

theorem ExprLowering.pendingNewTypesClosed
    (H : ExprLowering env lctx params As e state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hinput : e.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | occurrence Hnode =>
    exact Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate
  | bvar Hnode | fvar Hnode | mvar Hnode | sort Hnode | const Hnode
      | lit Hnode =>
    exact Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2
      (ihFn Hinput.1
        (Hnode.pendingNewTypesClosed Henv Hclosing
          ⟨Hinput.1, Hinput.2⟩ Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2
      (ihDom Hinput.1
        (Hnode.pendingNewTypesClosed Henv Hclosing
          ⟨Hinput.1, Hinput.2⟩ Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2
      (ihValue Hinput.2.1
        (ihType Hinput.1
          (Hnode.pendingNewTypesClosed Henv Hclosing
            ⟨Hinput.1, Hinput.2.1, Hinput.2.2⟩ Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody Hinput
      (Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate)

theorem ExprLowering.auxFVarsIn
    (H : ExprLowering env lctx params As e state out)
    (HAs : CDeclArray lctx As)
    (Hinput : e.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H generalizing P with
  | occurrence Hnode => exact Hnode.auxFVarsIn HAs Hinput Hparams Hstate
  | bvar Hnode | fvar Hnode | mvar Hnode | sort Hnode | const Hnode
      | lit Hnode =>
    exact Hnode.auxFVarsIn HAs Hinput Hparams Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2 Hparams
      (ihFn Hinput.1 Hparams
        (Hnode.auxFVarsIn HAs Hinput Hparams Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2 Hparams
      (ihDom Hinput.1 Hparams
        (Hnode.auxFVarsIn HAs Hinput Hparams Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2 Hparams
      (ihValue Hinput.2.1 Hparams
        (ihType Hinput.1 Hparams
          (Hnode.auxFVarsIn HAs Hinput Hparams Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput Hparams
      (Hnode.auxFVarsIn HAs Hinput Hparams Hstate)

theorem ExprLowering.resolvedMapping
    (H : ExprLowering env lctx params As input state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ExprLowering.Resolved env lctx params As finalResult input state out := by
  induction H generalizing finalState with
  | occurrence Hnode => exact .occurrence (Hnode.resolvedTrace Hlater Hmap)
  | bvar Hnode => exact .bvar Hnode
  | fvar Hnode => exact .fvar Hnode
  | mvar Hnode => exact .mvar Hnode
  | sort Hnode => exact .sort Hnode
  | const Hnode => exact .const Hnode
  | lit Hnode => exact .lit Hnode
  | app Hnode Hfn Harg ihFn ihArg =>
    exact .app Hnode (ihFn (Harg.nestedAuxLE.trans Hlater) Hmap)
      (ihArg Hlater Hmap)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    exact .lam Hnode (ihDom (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact .forallE Hnode (ihDom (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact .letE Hnode
      (ihType (Hvalue.nestedAuxLE.trans
        (Hbody.nestedAuxLE.trans Hlater)) Hmap)
      (ihValue (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | mdata Hnode Hbody ihBody => exact .mdata Hnode (ihBody Hlater Hmap)
  | proj Hnode Hbody ihBody => exact .proj Hnode (ihBody Hlater Hmap)

theorem replaceAllNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.replaceAllNested lctx params As e env state).WF
      fun out => ExprLowering env lctx params As e state out := by
  induction e generalizing state with
  | bvar i =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.bvar i)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.bvar Hnode)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | fvar id =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.fvar id)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.fvar Hnode)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | mvar id =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.mvar id)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.mvar Hnode)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | sort level =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.sort level)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.sort Hnode)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | const name levels =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.const name levels) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.const Hnode)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | lit literal =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.lit literal) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.lit Hnode)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | app fn arg ihFn ihArg =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.app fn arg) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihFn state) ?_
      intro fn' fnState Hfn
      refine nestedBind.WF (ihArg fnState) ?_
      intro arg' outState Harg
      exact Except.WF.pure (.app Hnode Hfn Harg)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | lam name dom body bi ihDom ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.lam name dom body bi) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihDom state) ?_
      intro dom' domState Hdom
      refine nestedBind.WF (ihBody domState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.lam Hnode Hdom Hbody)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | forallE name dom body bi ihDom ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.forallE name dom body bi) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihDom state) ?_
      intro dom' domState Hdom
      refine nestedBind.WF (ihBody domState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.forallE Hnode Hdom Hbody)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.letE name type value body nondep) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihType state) ?_
      intro type' typeState Htype
      refine nestedBind.WF (ihValue typeState) ?_
      intro value' valueState Hvalue
      refine nestedBind.WF (ihBody valueState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.letE Hnode Htype Hvalue Hbody)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | mdata data body ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.mdata data body) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihBody state) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.mdata Hnode Hbody)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)
  | proj name idx body ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.proj name idx body) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihBody state) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.proj Hnode Hbody)
    · cases hsome; exact Except.WF.pure (.occurrence Hnode)

end VerifyInductive
end Lean4Lean
