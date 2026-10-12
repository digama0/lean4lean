import Lean4Lean.Verify.Inductive.Recursor.Binders.BinderTypes

/-! Induction-hypothesis and minor-premise types of the minor pass of
`mkRecInfos`: the source construction of each hypothesis
(`InductionHypothesisType`) and minor (`MinorPremiseType`), the per-family binder
types `RecInfoBinderTypes`, the alignment of the recorded rule templates with the
minors (`CallTemplatesMatch`, `RuleTemplatesMatch`), and the executable shapes of
major and motive domains (`MajorPremiseTypes`, `MotiveTypes`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

structure InductionHypothesisType
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (root : AddInductive.Context) (field type : Expr) where
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  exposedType : Expr
  args : Array Expr
  arguments_bound : FVarArrayAfter root current args
  loopInput : LoopUArgsInput root field
  loopTrace : LoopUArgsRun root
    (loopUArgsCheckLCtx root loopInput.prior) loopInput.normalizedType current
    exposedType args
  field_fvar : ∃ fv, field = .fvar fv ∧ fv ∈ root.lctx.fvars
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats exposedType = some ownerIdx
  motive_is_fvar : ∃ fv,
    recInfos[ownerIdx]!.motive = .fvar fv ∧ fv ∈ root.lctx.fvars
  type_eq :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive itIndices)
      (mkAppN field args)
    type = current.lctx.mkForall args motiveApp

/-- The higher-order telescope of an induction hypothesis before the
type annotations of the installed declaration are stripped. -/
theorem InductionHypothesisType.sourceTelescope
    (O : InductionHypothesisType stats recInfos root field type) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    Expr.ForallTelescope type O.args.size
      (motiveApp.abstractN O.arguments_bound.fvars) := by
  cases O with
  | mk current current_wf _current_extends exposedType args
      arguments_bound _loopInput _loopTrace _field_fvar ownerIdx _owner_valid
      _motive_is_fvar type_eq =>
    dsimp only at type_eq ⊢
    rw [type_eq]
    exact arguments_bound.toFVarArrayIn.mkForall_forallTelescope
      current_wf _

/-- Closing the fresh higher-order arguments turns the selected field
application into its bvar spine.  This is the minor-pass
counterpart of `RecursiveCall.abstractedMajor`. -/
theorem InductionHypothesisType.abstractedMotiveApp_eq
    (O : InductionHypothesisType stats recInfos root field type) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    motiveApp.abstractList O.arguments_bound.fvars =
      Expr.app
        (mkAppN
          (recInfos[O.ownerIdx]!.motive.abstractList
            O.arguments_bound.fvars)
          (indices.map fun e =>
            e.abstractList O.arguments_bound.fvars))
        (mkAppN (field.abstractList O.arguments_bound.fvars)
          (List.ofFn (fun i : Fin O.arguments_bound.fvars.length =>
            Expr.bvar (O.arguments_bound.fvars.length - 1 - i))).toArray) := by
  dsimp only
  have hlocal :
      O.args.map (fun e => e.abstractList O.arguments_bound.fvars) =
        (List.ofFn (fun i : Fin O.arguments_bound.fvars.length =>
          Expr.bvar
            (O.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      O.args.map (fun e => e.abstractList O.arguments_bound.fvars) =
          ((O.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractList O.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractList O.arguments_bound.fvars)
            O.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          O.arguments_bound.fvars 0 O.arguments_bound.nodup
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hlocal]

def InductionHypothesisType.localIndices
    (O : InductionHypothesisType stats recInfos root field type) :
    List Nat :=
  List.ofFn fun i : Fin O.arguments_bound.fvars.length =>
    O.arguments_bound.fvars.length - 1 - i

def InductionHypothesisType.abstractedField
    (O : InductionHypothesisType stats recInfos root field type) :
    Expr :=
  mkAppN (field.abstractList O.arguments_bound.fvars)
    (O.localIndices.map Expr.bvar).toArray

def InductionHypothesisType.outerAbstractedField
    (O : InductionHypothesisType stats recInfos root field type)
    (binders : List FVarId) : Expr :=
  O.abstractedField.abstractList binders O.args.size

/-- Alpha-normalized shape of the minor-pass `loopUArgs` run.  Closing the
fresh higher-order suffix and then the constructor fields removes the fresh
identifiers while keeping exactly the owner, local arity, and index spine
which determine the generated induction-hypothesis type. -/
def InductionHypothesisType.replayTrace
    (O : InductionHypothesisType stats recInfos root field type)
    (fieldBinders : List FVarId) : InductionHypothesisShape where
  ownerIdx := O.ownerIdx
  localArity := O.args.size
  localTelescope :=
    (O.current.lctx.mkForall O.args (.sort .zero)).abstractList fieldBinders
  motive :=
    (recInfos[O.ownerIdx]!.motive.abstractList
      O.arguments_bound.fvars).abstractList fieldBinders O.args.size
  indices :=
    ((O.exposedType.getAppArgs[stats.params.size:] : Array Expr).map
      fun index =>
        (index.abstractList O.arguments_bound.fvars).abstractList
          fieldBinders O.args.size)

/-- The minor-pass hypothesis result after closing its higher-order arguments
and all constructor fields.  This is the motive application;
the surrounding forall telescope is handled separately. -/
def InductionHypothesisType.outerAbstractedMotiveApp
    (O : InductionHypothesisType stats recInfos root field type)
    (fieldBinders : List FVarId) : Expr :=
  Expr.app
    (mkAppN (O.replayTrace fieldBinders).motive
      (O.replayTrace fieldBinders).indices)
    (O.outerAbstractedField fieldBinders)

theorem InductionHypothesisType.outerAbstractedMotiveApp_eq
    (O : InductionHypothesisType stats recInfos root field type)
    (fieldBinders : List FVarId) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    (motiveApp.abstractList O.arguments_bound.fvars).abstractList
        fieldBinders O.args.size =
      O.outerAbstractedMotiveApp fieldBinders := by
  dsimp only
  rw [O.abstractedMotiveApp_eq]
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  simp [InductionHypothesisType.outerAbstractedMotiveApp,
    InductionHypothesisType.replayTrace,
    InductionHypothesisType.outerAbstractedField,
    Array.map_map, Function.comp_def]
  unfold InductionHypothesisType.abstractedField
    InductionHypothesisType.localIndices
  rw [Expr.abstractList_mkAppN]
  simp [List.map_ofFn, Function.comp_def]

/-- Closedness of the recorded motive application follows from closedness of
its outer abstraction, by peeling the two sequential closures. -/
theorem InductionHypothesisType.motiveApp_closed_of_outer
    (O : InductionHypothesisType stats recInfos root field type)
    (fieldBinders : List FVarId)
    (hclosed : Closed (O.outerAbstractedMotiveApp fieldBinders)
      (O.args.size + fieldBinders.length)) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    Closed motiveApp := by
  dsimp only
  rw [← O.outerAbstractedMotiveApp_eq fieldBinders] at hclosed
  have h1 := Expr.closed_of_abstractList (depth := O.args.size)
    (fvars := fieldBinders) hclosed
  have hlen : O.arguments_bound.fvars.length = O.args.size :=
    O.arguments_bound.length_fvars
  exact Expr.closed_of_abstractList (depth := 0)
    (fvars := O.arguments_bound.fvars) (by simpa [hlen] using h1)

/-- Sequential-model form of `sourceTelescope` for a closed motive
application. -/
theorem InductionHypothesisType.sourceTelescopeList
    (O : InductionHypothesisType stats recInfos root field type)
    (hclosed : Closed (Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive
        (O.exposedType.getAppArgs[stats.params.size:] : Array Expr))
      (mkAppN field O.args))) :
    Expr.ForallTelescope type O.args.size
      ((Expr.app
        (mkAppN recInfos[O.ownerIdx]!.motive
          (O.exposedType.getAppArgs[stats.params.size:] : Array Expr))
        (mkAppN field O.args)).abstractList O.arguments_bound.fvars) := by
  have h := O.sourceTelescope
  dsimp only at h
  rwa [Expr.abstractN_eq_abstractList_of_closed O.arguments_bound.nodup hclosed] at h

/-- After also closing an outer binder list, the selected field
is the outer de Bruijn variable shifted beneath its higher-order
arguments and applied to their bvar spine. -/
theorem InductionHypothesisType.outerAbstractedField_eq_bvar
    (O : InductionHypothesisType stats recInfos root field type)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      O.outerAbstractedField binders =
        mkAppN (.bvar (O.args.size + fieldVar))
          (O.localIndices.map Expr.bvar).toArray := by
  subst field
  rcases List.mem_iff_getElem.mp hfield with ⟨i, hi, hget⟩
  let fieldVar := binders.length - 1 - i
  have hfresh : fv ∉ O.arguments_bound.fvars := by
    intro hmem
    exact O.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldLocal :
      (Expr.fvar fv).abstractList O.arguments_bound.fvars = .fvar fv :=
    Expr.abstractList_fvar_of_not_mem hfresh
  have hlocalSize : O.args.size = O.arguments_bound.fvars.length := by
    have h := congrArg Array.size O.arguments_bound.expressions
    simpa using h
  have hfieldOuter := Expr.abstractList_fvar_getElem
    hbinders i hi (k := O.args.size)
  rw [hget] at hfieldOuter
  have hfieldOuter' :
      (Expr.fvar fv).abstractList binders O.args.size =
        .bvar (O.args.size + fieldVar) := by
    simpa [fieldVar] using hfieldOuter
  have hfieldBase := Expr.abstractList_fvar_getElem
    hbinders i hi (k := 0)
  rw [hget] at hfieldBase
  have hfieldBase' : (Expr.fvar fv).abstractList binders =
      .bvar fieldVar := by
    simpa [fieldVar] using hfieldBase
  have hsourceArgs :
      (List.ofFn fun i : Fin O.arguments_bound.fvars.length =>
        Expr.bvar (O.arguments_bound.fvars.length - 1 - i)) =
      O.localIndices.map Expr.bvar := by
    simp [InductionHypothesisType.localIndices,
      List.map_ofFn, Function.comp_def]
  refine ⟨fieldVar, by omega, hfieldBase', ?_⟩
  unfold InductionHypothesisType.outerAbstractedField
    InductionHypothesisType.abstractedField
  rw [Expr.abstractList_mkAppN, hfieldLocal, hfieldOuter']
  apply congrArg (mkAppN (.bvar (O.args.size + fieldVar)))
  rw [← hsourceArgs]
  apply Array.ext
  · simp
  · intro j hjLeft hjRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_ofFn]
    apply Expr.abstractList_bvar_lt
    have hj : j < O.arguments_bound.fvars.length := by
      simpa [InductionHypothesisType.localIndices] using hjRight
    omega

/-- Positional form of `outerAbstractedField_eq_bvar`.  When the
field is known to occupy binder position `i`, its de Bruijn index is no
longer existential: it is exactly the reverse ordinal of that position. -/
theorem InductionHypothesisType.outerAbstractedField_eq_bvar_at
    (O : InductionHypothesisType stats recInfos root field type)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hi : i < binders.length)
    (hget : binders[i] = fv) :
    O.outerAbstractedField binders =
      mkAppN (.bvar (O.args.size + (binders.length - 1 - i)))
        (O.localIndices.map Expr.bvar).toArray := by
  have hmem : fv ∈ binders := by
    rw [← hget]
    exact List.getElem_mem hi
  rcases O.outerAbstractedField_eq_bvar hfieldEq hfieldRoot hbinders hmem with
    ⟨fieldVar, _hfieldVar, habstract, houter⟩
  have hexact := Expr.abstractList_fvar_getElem hbinders i hi (k := 0)
  rw [hget] at hexact
  have hfieldVarExact : fieldVar = binders.length - 1 - i := by
    have hexact' : (Expr.fvar fv).abstractList binders =
        .bvar (binders.length - 1 - i) := by
      simpa only [Nat.zero_add] using hexact
    exact Expr.bvar.inj (habstract.symm.trans hexact')
  simpa [hfieldVarExact] using houter

/-- The constructed hypothesis type cannot itself be a top-level parameter
annotation: a nonempty local suffix produces a forall, while the empty case
is the explicit motive application. -/
theorem InductionHypothesisType.consumeTypeAnnotationsVerified_eq_self
    (O : InductionHypothesisType stats recInfos root field type) :
    (type.consumeTypeAnnotationsVerified annOk) = type := by
  let itIndices := O.exposedType.getAppArgs[stats.params.size:]
  let motiveApp := Expr.app
    (mkAppN recInfos[O.ownerIdx]!.motive itIndices)
    (mkAppN field O.args)
  rw [O.type_eq]
  by_cases hpos : 0 < O.args.size
  · have Htelescope :=
      O.arguments_bound.toFVarArrayIn.mkForall_forallTelescope
        O.current_wf motiveApp
    exact Htelescope.consumeTypeAnnotationsVerified_eq_self_of_pos hpos
  · have hsize : O.args.size = 0 := by omega
    have hargs : O.args = #[] := Array.eq_empty_of_size_eq_zero hsize
    rw [hargs]
    rw [LocalContext.mkForall_empty]
    rcases O.motive_is_fvar with ⟨motiveFVar, hmotive, _hmotiveRoot⟩
    have hhead :
        (Expr.app
          (mkAppN recInfos[O.ownerIdx]!.motive itIndices)
          (mkAppN field #[])).getAppFn = .fvar motiveFVar := by
      simp only [Expr.getAppFn, Expr.getAppFn_mkAppN, hmotive]
    apply Expr.consumeTypeAnnotationsVerified_eq_self
    · change (Expr.app _ _).isAppOfArity `optParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change (Expr.app _ _).isAppOfArity `autoParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change (Expr.app _ _).isAppOfArity `outParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change (Expr.app _ _).isAppOfArity `semiOutParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _

/-- The source type of each induction hypothesis of one generated minor,
before annotation stripping, with the run (`InductionHypothesisType`) that built it. -/
structure MinorInductionHypothesisTypes
    (c : AddInductive.Context) (fields hypotheses : Array Expr) where
  stats : AddInductive.InductiveStats
  recInfos : Array AddInductive.RecInfo
  fieldRoot : AddInductive.Context
  fieldRoot_wf : BindingContextWF fieldRoot
  hypotheses_outer_fresh : ∀ fv,
    fv ∈ ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (recInfos.map (·.motive)) →
      fv ∉ ExprArrayFVarIds hypotheses
  entry : ∀ j (_hj : j < hypotheses.size),
    ∃ root sourceType,
      BindingContextLE fieldRoot root ∧
      Nonempty (InductionHypothesisType
        stats recInfos root fields[j]! sourceType) ∧
      ∃ D : FVarDeclAt c hypotheses j,
        D.type = (sourceType.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)

/-- The source construction of one generated minor domain: `origin` is the
declared (unannotated) domain and `sourceType` the expression before annotation
stripping.  The source local context is stored in the structure: after
`mkForall` closes the freshly introduced fields and recursive hypotheses, the
resulting expression is stable under every later ambient-context extension. -/
structure MinorPremiseType where
  localIndex : Nat
  origin : Expr
  constructor : Constructor
  sourceConstructors : List Constructor
  sourceConstructor : sourceConstructors[localIndex]? = some constructor
  sourceFullContext : AddInductive.Context
  sourceFullWF : BindingContextWF sourceFullContext
  sourceContext : LocalContext
  sourceContext_eq : sourceFullContext.lctx = sourceContext
  fields : Array Expr
  fields_bound : FVarArrayIn sourceFullContext fields
  fields_nodup : fields_bound.fvars.Nodup
  recursiveFields : Array Expr
  hypotheses : Array Expr
  hypotheses_bound : FVarArrayIn sourceFullContext hypotheses
  hypotheses_nodup : hypotheses_bound.fvars.Nodup
  hypotheses_fields_fresh : ∀ fv ∈ hypotheses_bound.fvars,
    fv ∉ fields_bound.fvars
  hypothesis_type_origins : Option
    (MinorInductionHypothesisTypes
      sourceFullContext recursiveFields hypotheses)
  hypotheses_size : hypotheses.size = recursiveFields.size
  traversal : Option ConstructorFieldTraversal
  hypothesis_origins_fieldRoot : ∀ origins T,
    hypothesis_type_origins = some origins →
    traversal = some T →
    origins.fieldRoot = T.terminalContext
  motiveApp : Expr
  sourceType : Expr
  sourceType_eq : sourceType =
    sourceContext.mkForall fields
      (sourceContext.mkForall hypotheses motiveApp)
  unannotated_eq :
    (sourceType.consumeTypeAnnotationsVerified sourceFullContext.env.isTypeAnnotationWrapper) = origin

/-- A minor carries its induction-hypothesis types (`hypothesis_type_origins`),
produced with the expected inductive statistics and motives. -/
def MinorPremiseType.HasInductionHypothesisTypes
    (S : MinorPremiseType) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  match S.hypothesis_type_origins with
  | none => False
  | some origins => origins.stats = stats ∧
      origins.recInfos.map (·.motive) = recInfos.map (·.motive)

theorem MinorPremiseType.hypothesisTypeOrigins_exists
    (S : MinorPremiseType) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (H : S.HasInductionHypothesisTypes stats recInfos) :
    ∃ origins, S.hypothesis_type_origins = some origins ∧
      origins.stats = stats ∧
        origins.recInfos.map (·.motive) = recInfos.map (·.motive) := by
  cases h : S.hypothesis_type_origins with
  | none => simp [MinorPremiseType.HasInductionHypothesisTypes, h] at H
  | some origins =>
      exact ⟨origins, rfl, by
        simpa [MinorPremiseType.HasInductionHypothesisTypes, h] using H⟩

/-- The hypothesis array is the inner forall
telescope of the generated minor source type.  Its residual is expressed
after simultaneous abstraction by the corresponding hypothesis
identifiers, matching the representation used for generated rule bodies. -/
theorem MinorPremiseType.hypothesisTelescope
    (S : MinorPremiseType) :
    Expr.ForallTelescope
      (S.sourceContext.mkForall S.hypotheses S.motiveApp)
      S.hypotheses.size
      (S.motiveApp.abstractN S.hypotheses_bound.fvars) := by
  let B := S.hypotheses_bound
  have hsize : B.fvars.length = S.hypotheses.size := by
    have h := congrArg Array.size B.expressions
    simpa using h.symm
  have Htelescope := LocalContext.mkForall_fvars_forallTelescope
    (lctx := S.sourceFullContext.lctx) (body := S.motiveApp)
    (fvs := B.fvars) (by
      intro fv hfv
      exact S.sourceFullWF.findCDecl fv (B.members fv hfv))
  have houter : S.sourceContext.mkForall S.hypotheses S.motiveApp =
      S.sourceFullContext.lctx.mkForall
        (B.fvars.map Expr.fvar).toArray S.motiveApp := by
    calc
      _ = S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp :=
        congrArg (fun lctx => lctx.mkForall S.hypotheses S.motiveApp)
          S.sourceContext_eq.symm
      _ = _ := congrArg
        (fun fields => S.sourceFullContext.lctx.mkForall fields S.motiveApp)
        B.expressions
  rw [houter]
  simpa only [B, ← hsize] using Htelescope

/-- The constructor fields likewise form the outer telescope
of the minor source type around any chosen body. -/
theorem MinorPremiseType.fieldTelescope
    (S : MinorPremiseType) (body : Expr) :
    Expr.ForallTelescope
      (S.sourceContext.mkForall S.fields body)
      S.fields.size (body.abstractN S.fields_bound.fvars) := by
  have Htelescope := S.fields_bound.mkForall_forallTelescope
    S.sourceFullWF body
  have houter : S.sourceContext.mkForall S.fields body =
      S.sourceFullContext.lctx.mkForall S.fields body :=
    congrArg (fun lctx => lctx.mkForall S.fields body)
      S.sourceContext_eq.symm
  rw [houter]
  exact Htelescope

/-- Combining the two arrays exposes the complete field/hypothesis
telescope of the minor source type (before annotation stripping), including the precise
abstraction cutoff beneath the inner hypothesis binders. -/
theorem MinorPremiseType.sourceTelescope
    (S : MinorPremiseType) :
    Expr.ForallTelescope S.sourceType
      (S.fields.size + S.hypotheses.size)
      ((S.motiveApp.abstractN S.hypotheses_bound.fvars).abstractN
        S.fields_bound.fvars S.hypotheses.size) := by
  rw [S.sourceType_eq]
  have Hfields := S.fieldTelescope
    (S.sourceContext.mkForall S.hypotheses S.motiveApp)
  have Hhypotheses :=
    S.hypothesisTelescope.abstractN S.fields_bound.fvars
  simpa only [Nat.zero_add] using Hfields.trans Hhypotheses

/-- Sequential-model form of `sourceTelescope` for a closed motive
application. -/
theorem MinorPremiseType.sourceTelescopeList
    (S : MinorPremiseType) (hclosed : Closed S.motiveApp) :
    Expr.ForallTelescope S.sourceType
      (S.fields.size + S.hypotheses.size)
      ((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size) := by
  have h := S.sourceTelescope
  have hlen : S.hypotheses.size = S.hypotheses_bound.fvars.length := by
    simpa using congrArg Array.size S.hypotheses_bound.expressions
  rw [Expr.abstractN_eq_abstractList_of_closed S.hypotheses_nodup hclosed] at h
  rw [Expr.abstractN_eq_abstractList S.fields_nodup _ _ (by
    have hc := (Closed.abstractList_at (fvars := S.hypotheses_bound.fvars)
      (depth := 0) (outer := 0) hclosed).looseBVarRange_le
    simpa [hlen] using hc)] at h
  exact h

/-- The unannotated domain `origin` declared for the minor keeps
the complete field/hypothesis arity of its source type. -/
theorem MinorPremiseType.originTelescope
    (S : MinorPremiseType) :
    ∃ residual, Expr.ForallTelescope S.origin
      (S.fields.size + S.hypotheses.size) residual := by
  rcases S.sourceTelescope.consumeTypeAnnotationsVerified_arity with
    ⟨residual, Htelescope⟩
  rw [S.unannotated_eq] at Htelescope
  exact ⟨residual, Htelescope⟩

/-- The types passed to `withLocalDecl` for each motive, major, index and minor,
in the same row structure as the executable's `RecInfo`s.  Per-owner rows keep
the insertion position of minor premises during the minor pass. -/
structure RecInfoBinderTypes (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) where
  motiveTypes : Array Expr
  majorTypes : Array Expr
  indexTypes : Array (Array Expr)
  minorTypes : Array (Array Expr)
  indexTypes_size : indexTypes.size = recInfos.size
  minorTypes_size : minorTypes.size = recInfos.size
  motives : FVarArrayBinderTypes c (recInfos.map (·.motive)) motiveTypes
  majors : FVarArrayBinderTypes c (recInfos.map (·.major)) majorTypes
  indices : ∀ i (_hi : i < recInfos.size),
    FVarArrayBinderTypes c recInfos[i]!.indices indexTypes[i]!
  minors : ∀ i (_hi : i < recInfos.size),
    FVarArrayBinderTypes c recInfos[i]!.minors minorTypes[i]!
  minorShapes : ∀ i (_hi : i < recInfos.size) j
    (_hj : j < minorTypes[i]!.size),
    MinorPremiseType

/-- The recursive-call templates recorded in the minor pass, matched with the
induction-hypothesis types of one minor.  Every entry comes from the
`loopUTemplates` run which introduced the corresponding hypothesis, so no
comparison of two separate runs is needed. -/
structure CallTemplatesMatch
    {sourceFullContext : AddInductive.Context}
    (origins : MinorInductionHypothesisTypes
      sourceFullContext fields hypotheses)
    (allFields : Array Expr)
    (calls : Array AddInductive.RecCallTemplate) : Prop where
  size_eq : calls.size = hypotheses.size
  entry : ∀ j (_hj : j < hypotheses.size),
    ∃ originRoot sourceType,
      ∃ (O : InductionHypothesisType origins.stats origins.recInfos
        originRoot fields[j]! sourceType),
        ∃ (D : FVarDeclAt sourceFullContext hypotheses j),
          BindingContextLE origins.fieldRoot originRoot ∧
          D.type = (sourceType.consumeTypeAnnotationsVerified
            sourceFullContext.env.isTypeAnnotationWrapper) ∧
          calls[j]! = {
            major := fields[j]!
            args := O.args
            lctx := O.current.lctx
            targetTypeIdx := O.ownerIdx
            targetIndices :=
              O.exposedType.getAppArgs[origins.stats.params.size:]
            template := O.current.lctx.mkLambda O.args <|
              (mkAppN (.bvar O.args.size)
                O.exposedType.getAppArgs[origins.stats.params.size:]).app
                  (mkAppN fields[j]! O.args) }
  /-- The same data as `entry`, together with the
  recursor-context well-formedness of each call's `loopUArgs` root and the
  up-set of the constructor fields (`allFields`) and common parameters in
  it.  These are what a per-call `whnf` fact needs along the
  `LoopUArgsRun`. -/
  rooted : ∀ j (_hj : j < hypotheses.size),
    ∃ originRoot sourceType,
      ∃ (recLparams : List Name)
        (Rorigin : RecursorContextWF originRoot recLparams)
        (O : InductionHypothesisType origins.stats origins.recInfos
          originRoot fields[j]! sourceType)
        (D : FVarDeclAt sourceFullContext hypotheses j),
        BindingContextLE origins.fieldRoot originRoot ∧
        IsFVarUpSet (fun fv => fv ∈ ExprArrayFVarIds allFields ∨
          fv ∈ ExprArrayFVarIds origins.stats.params) Rorigin.mlctx.vlctx ∧
        D.type = (sourceType.consumeTypeAnnotationsVerified
            sourceFullContext.env.isTypeAnnotationWrapper) ∧
        calls[j]! = {
          major := fields[j]!
          args := O.args
          lctx := O.current.lctx
          targetTypeIdx := O.ownerIdx
          targetIndices :=
            O.exposedType.getAppArgs[origins.stats.params.size:]
          template := O.current.lctx.mkLambda O.args <|
            (mkAppN (.bvar O.args.size)
              O.exposedType.getAppArgs[origins.stats.params.size:]).app
                (mkAppN fields[j]! O.args) }

/-- One executable rule template is determined by the source shape of its
minor (`MinorPremiseType`). -/
def RuleTemplateMatchesMinor
    (stats : AddInductive.InductiveStats)
    (S : MinorPremiseType)
    (minor : Expr) (B : AddInductive.RecRuleTemplate) : Prop :=
  B.ctor = S.constructor.name ∧
    B.fields = S.fields ∧
    B.lctx = S.sourceFullContext.lctx ∧
    B.minor = minor ∧
    ∃ traversal origins,
      S.traversal = some traversal ∧
      S.hypothesis_type_origins = some origins ∧
      B.targetTypeIdx =
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      B.targetIndices =
        (AddInductive.getIIndices stats traversal.terminal).2 ∧
      CallTemplatesMatch origins S.fields B.recursiveCalls

/-- Owner- and minor-indexed alignment between the executable rule template
rows and the minor binder types recorded in the minor pass.  A rule builder
using this alignment never reruns field classification, inference,
or `whnf`, and so needs no comparison of two runs up to alpha. -/
structure RuleTemplatesMatch
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (H : RecInfoBinderTypes c recInfos) : Prop where
  rows_size : ∀ owner (_howner : owner < recInfos.size),
    recInfos[owner]!.ruleTemplates.size = H.minorTypes[owner]!.size
  entry : ∀ owner (howner : owner < recInfos.size)
    localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
    let S := H.minorShapes owner howner localIndex hlocal
    let B := recInfos[owner]!.ruleTemplates[localIndex]!
    RuleTemplateMatchesMinor stats S
      recInfos[owner]!.minors[localIndex]! B
  fields_outer_fresh : ∀ owner (howner : owner < recInfos.size)
      (localIndex : Nat)
      (hlocal : localIndex < H.minorTypes[owner]!.size)
      (fv : FVarId),
    fv ∈ (H.minorShapes owner howner localIndex hlocal).fields_bound.fvars →
    fv ∉ (ExprArrayFVarIds stats.params ++
      ExprArrayFVarIds (recInfos.map (·.motive))) ++
      ExprArrayFVarIds (recInfos.flatMap (·.minors))

/-- Executable shape of every generated major-premise declaration.
This positional fact is independent of translation: it records that
the stored binder type is the selected family applied to the common
parameters and this record's indices. -/
structure MajorPremiseTypes (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (majorTypes : Array Expr)
    (ok : Name → Bool) : Prop where
  size_eq : majorTypes.size = recInfos.size
  shape : ∀ i (_hi : i < recInfos.size),
    majorTypes[i]! =
      ((mkAppN (mkAppN stats.indConsts[i]! stats.params)
        recInfos[i]!.indices).consumeTypeAnnotationsVerified ok)

theorem MajorPremiseTypes.empty (stats : AddInductive.InductiveStats) (ok : Name → Bool) :
    MajorPremiseTypes stats #[] #[] ok where
  size_eq := rfl
  shape i hi := by simp at hi

/-- Append one family frame to the positional major-domain shapes. -/
theorem MajorPremiseTypes.push
    (H : MajorPremiseTypes stats recInfos majorTypes ok)
    (info : AddInductive.RecInfo) (majorType : Expr)
    (hnew : majorType =
      ((mkAppN (mkAppN stats.indConsts[recInfos.size]! stats.params)
        info.indices).consumeTypeAnnotationsVerified ok)) :
    MajorPremiseTypes stats (recInfos.push info)
      (majorTypes.push majorType) ok where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    by_cases hold : i < recInfos.size
    · have hmajor : i < majorTypes.size := by
        rw [H.size_eq]
        exact hold
      have hmajorPush : (majorTypes.push majorType)[i]! = majorTypes[i]! := by
        have hpush : i < (majorTypes.push majorType).size := by
          simp only [Array.size_push]
          omega
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hmajor]
        exact Array.getElem_push_lt hmajor
      have hinfoPush : (recInfos.push info)[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hmajorPush, hinfoPush]
      exact H.shape i hold
    · have hieq : i = recInfos.size := by
        simp only [Array.size_push] at hi
        omega
      subst i
      have hmajorPush :
          (majorTypes.push majorType)[recInfos.size]! = majorType := by
        rw [show recInfos.size = majorTypes.size from H.size_eq.symm]
        simp
      have hinfoPush : (recInfos.push info)[recInfos.size]! = info := by
        simp
      rw [hmajorPush, hinfoPush]
      exact hnew

def RecInfoBinderTypes.empty (c : AddInductive.Context) :
    RecInfoBinderTypes c #[] where
  motiveTypes := #[]
  majorTypes := #[]
  indexTypes := #[]
  minorTypes := #[]
  indexTypes_size := rfl
  minorTypes_size := rfl
  motives := by simpa using FVarArrayBinderTypes.empty c
  majors := by simpa using FVarArrayBinderTypes.empty c
  indices i hi := by simp at hi
  minors i hi := by simp at hi
  minorShapes i hi := by simp at hi

def RecInfoBinderTypes.mono
    (H : RecInfoBinderTypes c recInfos) (hle : BindingContextLE c c') :
    RecInfoBinderTypes c' recInfos where
  motiveTypes := H.motiveTypes
  majorTypes := H.majorTypes
  indexTypes := H.indexTypes
  minorTypes := H.minorTypes
  indexTypes_size := H.indexTypes_size
  minorTypes_size := H.minorTypes_size
  motives := H.motives.mono hle
  majors := H.majors.mono hle
  indices i hi := (H.indices i hi).mono hle
  minors i hi := (H.minors i hi).mono hle
  minorShapes i hi j hj := H.minorShapes i hi j hj

/-- Executable shape of every motive declaration domain.  This is
kept separately from `TrBinderTypes`: the latter states
that the stored domain translates to a type, while this structure states
which dependent forall telescope that domain is supposed to be. -/
structure MotiveTypes (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) (motiveTypes : Array Expr)
    (elimLevel : Level) : Prop where
  size_eq : motiveTypes.size = recInfos.size
  shape : ∀ i (_hi : i < recInfos.size),
    motiveTypes[i]! =
      c.lctx.mkForall recInfos[i]!.indices
        (c.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel))

end VerifyInductive
end Lean4Lean
