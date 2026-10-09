import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveCalls

/-! The syntax of one generated iota rule (`RecursorRuleSyntax`): its constructor, binders
(parameters, motives, minors, fields), recursive calls and right-hand side, with the de Bruijn
form of the simultaneously abstracted binders and the unique translation of each binder group.
`RecursorRuleSyntax.Semantics` adds the typing facts of the field and recursive-call loops,
and the `TypedRecursiveCall*` structures type the recursive calls at their call sites. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Rule-level abstraction turns the selected field free variable into its
outer de Bruijn index beneath the generated call's local lambda binders. -/
theorem RecursiveCall.outerAbstractedMajor_eq_bvar
    (H : RecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      H.outerAbstractedMajor binders =
        mkAppN (.bvar (H.localArgs.size + fieldVar))
          (H.localIndices.map Expr.bvar).toArray := by
  rcases List.mem_iff_getElem.mp hfield with ⟨i, hi, hget⟩
  let fieldVar := binders.length - 1 - i
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldLocal :
      (Expr.fvar fv).abstractN H.arguments_bound.fvars = .fvar fv :=
    Expr.abstractN_fvar_of_not_mem hfresh
  have hlocalSize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  have hfieldOuter := Expr.abstractList_fvar_getElem
    hbinders i hi (k := H.localArgs.size)
  rw [hget] at hfieldOuter
  have hfieldOuter' :
      (Expr.fvar fv).abstractList binders H.localArgs.size =
        .bvar (H.localArgs.size + fieldVar) := by
    simpa [fieldVar] using hfieldOuter
  have hfieldBase := Expr.abstractList_fvar_getElem
    hbinders i hi (k := 0)
  rw [hget] at hfieldBase
  have hfieldBase' : (Expr.fvar fv).abstractList binders =
      .bvar fieldVar := by
    simpa [fieldVar] using hfieldBase
  have hsourceArgs :
      (List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i)) =
      H.localIndices.map Expr.bvar := by
    simp [RecursiveCall.localIndices,
      List.map_ofFn, Function.comp_def]
  refine ⟨fieldVar, by omega, hfieldBase', ?_⟩
  unfold RecursiveCall.outerAbstractedMajor
  rw [H.abstractedMajor_eq_of_closed (by simp [Lean.Expr.looseBVarRange'])]
  rw [Expr.abstractList_mkAppN, hfieldLocal, hfieldOuter']
  apply congrArg (mkAppN (.bvar (H.localArgs.size + fieldVar)))
  rw [hsourceArgs]
  apply Array.ext
  · simp
  · intro j hjLeft hjRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map]
    apply Expr.abstractList_bvar_lt
    have hj : j < H.localIndices.length := by simpa using hjRight
    have hj' : j < H.arguments_bound.fvars.length := by
      simpa [RecursiveCall.localIndices] using hj
    simp only [RecursiveCall.localIndices,
      List.getElem_ofFn]
    omega

/-- Dependent array-selection wrapper for
`outerAbstractedMajor_eq_bvar`. -/
theorem RecursiveCall.outerAbstractedMajor_eq_bvar_of_field_eq
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      H.outerAbstractedMajor binders =
        mkAppN (.bvar (H.localArgs.size + fieldVar))
          (H.localIndices.map Expr.bvar).toArray := by
  subst field
  exact H.outerAbstractedMajor_eq_bvar hfieldRoot hbinders hfield

/-- Positional form of `outerAbstractedMajor_eq_bvar_of_field_eq`. -/
theorem RecursiveCall.outerAbstractedMajor_eq_bvar_at
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hi : i < binders.length)
    (hget : binders[i] = fv) :
    H.outerAbstractedMajor binders =
      mkAppN (.bvar (H.localArgs.size + (binders.length - 1 - i)))
        (H.localIndices.map Expr.bvar).toArray := by
  have hmem : fv ∈ binders := by
    rw [← hget]
    exact List.getElem_mem hi
  rcases H.outerAbstractedMajor_eq_bvar_of_field_eq hfieldEq hfieldRoot
      hbinders hmem with
    ⟨fieldVar, _hfieldVar, habstract, houter⟩
  have hexact := Expr.abstractList_fvar_getElem hbinders i hi (k := 0)
  rw [hget] at hexact
  have hfieldVarExact : fieldVar = binders.length - 1 - i := by
    have hexact' : (Expr.fvar fv).abstractList binders =
        .bvar (binders.length - 1 - i) := by
      simpa only [Nat.zero_add] using hexact
    exact Expr.bvar.inj (habstract.symm.trans hexact')
  simpa [hfieldVarExact] using houter

theorem RecursiveCall.abstractedBody_eq_named
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.body =
      H.abstractedRecursor.app H.abstractedMajor := by
  simpa [RecursiveCall.abstractedRecursor,
    RecursiveCall.abstractedMajor,
    RecursiveCall.recursorName] using H.abstractedBody_eq

theorem RecursiveCall.outerAbstractedBody_eq_named
    (H : RecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.body.abstractList binders H.localArgs.size =
      (H.outerAbstractedRecursor binders).app
        (H.outerAbstractedMajor binders) := by
  rw [H.abstractedBody_eq_named]
  exact Expr.abstractList_app

/-- Shifting loose variables cannot introduce a constant name. -/
private theorem avoidsConsts_liftLooseBVars'
    (H : Lean.Expr.AvoidsConsts names e) (start amount : Nat) :
    Lean.Expr.AvoidsConsts names (e.liftLooseBVars' start amount) := by
  induction H generalizing start with
  | bvar i => exact .bvar _
  | fvar fv => exact .fvar fv
  | mvar mv => exact .mvar mv
  | sort u => exact .sort u
  | const name levels fresh => exact .const name levels fresh
  | app fn arg _ _ ihFn ihArg =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.app _ _ (ihFn start) (ihArg start)
  | lam name dom body bi _ _ ihDom ihBody =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.lam name _ _ bi
          (ihDom start) (ihBody (start + 1))
  | forallE name dom body bi _ _ ihDom ihBody =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.forallE name _ _ bi
          (ihDom start) (ihBody (start + 1))
  | letE name type value body nondep _ _ _ ihType ihValue ihBody =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.letE name _ _ _ nondep
          (ihType start) (ihValue start) (ihBody (start + 1))
  | lit value expanded _ =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.lit value expanded
  | mdata data body _ ih =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.mdata data _ (ih start)
  | proj structName idx body _ ih =>
      simpa [Expr.liftLooseBVars'] using
        Lean.Expr.AvoidsConsts.proj structName idx _ (ih start)

/-- The retained closed call template instantiates its single recursor
placeholder and leaves the locally abstracted index arguments unchanged. -/
theorem TypedRecursiveCall.abstractedRecursor_eq
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (H : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) :
    let indices := (AddInductive.getIIndices stats
      H.generated.exposedType).2
    let recursor := mkAppN (mkAppN (mkAppN
      (.const H.generated.recursorName lvls) stats.params) motives) minors
    H.generated.abstractedRecursor =
      mkAppN (recursor.liftLooseBVars' 0 H.generated.localArgs.size)
        (indices.map fun source =>
          source.abstractN H.generated.arguments_bound.fvars) := by
  dsimp only
  let indices := (AddInductive.getIIndices stats
    H.generated.exposedType).2
  let recursor := mkAppN (mkAppN (mkAppN
    (.const H.generated.recursorName lvls) stats.params) motives) minors
  have hexposedClosed : Closed H.generated.exposedType := by
    have hclosed := H.exposed_translation.closed
    rw [H.current_context.mlctx.noBV] at hclosed
    exact hclosed
  have hsize : H.generated.localArgs.size =
      H.generated.arguments_bound.fvars.length := by
    have := congrArg Array.size H.generated.arguments_bound.expressions
    simpa using this
  have hindexFullMem : ∀ source ∈ indices,
      source ∈ H.generated.exposedType.getAppArgsList := by
    intro source hsource
    rw [← Expr.getAppArgs_toList]
    have hsourceArray : source ∈
        (AddInductive.getIIndices stats H.generated.exposedType).2 := by
      simpa [indices] using hsource
    unfold AddInductive.getIIndices at hsourceArray
    change source ∈
      (H.generated.exposedType.getAppArgs.toSubarray
        stats.params.size).toArray at hsourceArray
    let sub := H.generated.exposedType.getAppArgs.toSubarray
      stats.params.size
    have hsourceSubArray : source ∈ sub.toArray := by
      simpa [sub] using hsourceArray
    have hsourceArrayList : source ∈ sub.toArray.toList :=
      Array.mem_toList_iff.mpr hsourceSubArray
    have hsub : source ∈
        (H.generated.exposedType.getAppArgs.toSubarray
          stats.params.size).toList := by
      rw [← Subarray.toList_toArray]
      simpa [sub] using hsourceArrayList
    rw [Subarray.toList_eq_drop_take,
      Array.array_toSubarray] at hsub
    exact List.mem_of_mem_take (List.mem_of_mem_drop hsub)
  have hindexClosed : ∀ source ∈ indices, Closed source := by
    intro source hsource
    exact hexposedClosed.getAppArgsList (hindexFullMem source hsource)
  have hindicesInst :
      (indices.map fun source =>
        (source.abstractN H.generated.arguments_bound.fvars).instantiate1'
          recursor H.generated.localArgs.size) =
      indices.map fun source =>
        source.abstractN H.generated.arguments_bound.fvars := by
    apply Array.ext
    · simp
    · intro i hiLeft hiRight
      have hi : i < indices.size := by simpa using hiRight
      simp only [Array.getElem_map]
      apply Expr.instantiate1'_eq_self
      have hrange := Expr.abstractN_looseBVarRange_le
        (e := indices[i]'hi)
        (fvs := H.generated.arguments_bound.fvars) (k := 0)
      have hclosed := (hindexClosed (indices[i]'hi)
        (Array.getElem_mem hi)).looseBVarRange_zero
      calc
        ((indices[i]'hi).abstractN
              H.generated.arguments_bound.fvars).looseBVarRange' ≤
            H.generated.arguments_bound.fvars.length := by
          simpa [hclosed] using hrange
        _ = H.generated.localArgs.size := hsize.symm
  unfold RecursiveCall.abstractedRecursor
  rw [show (Expr.bvar H.generated.localArgs.size).abstractN H.generated.arguments_bound.fvars =
    .bvar H.generated.localArgs.size from rfl]
  simp only [Expr.instantiate1'_mkAppN]
  rw [Array.map_map]
  have hindicesInst' :
      ((AddInductive.getIIndices stats H.generated.exposedType).2.map
        ((fun arg => arg.instantiate1'
          (mkAppN (mkAppN (mkAppN
            (.const H.generated.recursorName lvls) stats.params) motives)
            minors) H.generated.localArgs.size) ∘
          fun source =>
            source.abstractN H.generated.arguments_bound.fvars)) =
      (AddInductive.getIIndices stats H.generated.exposedType).2.map
        (fun source =>
          source.abstractN H.generated.arguments_bound.fvars) := by
    simpa [indices, recursor, Function.comp_def] using hindicesInst
  rw [hindicesInst']
  simp [Expr.instantiate1', hsize]

/-- Prefix invariant for rule generation retaining both exact syntax and the
binding facts needed to translate every higher-order recursive result. -/
structure RecursiveCallsPrefix
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    Nonempty (RecursiveCall indTypes stats motives minors lvls
      root u[i] v[i]!)

/-- Prefix invariant for recursive-result generation with each executable
call coupled to the independent recursive-domain judgment for its exact
selected field. -/
structure TypedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (decl : VInductDecl) (depth : Nat) (P : FVarId → Prop)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    ∃ S : TypedRecursiveCall indTypes stats motives
        minors lvls R decl depth u[i] v[i]!,
      S.rootScope = P

/-- Typed recursive calls, each in the context in which the minor pass checked
it.  Hypothesis allocation advances both the local context and validation depth;
the closed generated rule does not justify collapsing these call contexts to the
later installation context. -/
structure TypedRecursiveCallsAbove
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {fieldRoot : AddInductive.Context} {recLparams : List Name}
    (Rfield : RecursorContextWF fieldRoot recLparams)
    (decl : VInductDecl) (P : FVarId → Prop)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    ∃ originRoot,
      ∃ Rorigin : RecursorContextWF originRoot recLparams,
        ∃ _ : RecursorContextExtension Rfield Rorigin,
          ∃ callDepth,
            ∃ S : TypedRecursiveCall indTypes stats
              motives minors lvls Rorigin decl callDepth u[i] v[i]!,
              S.rootScope = P

/-- The exact motive application proved while the template-producing minor
pass checks one recursive field.  It holds in the call's own context: the
later recursor contexts are siblings of that context and cannot soundly
reconstruct it by weakening. -/
structure TypedRecursiveCall.MotiveApplication
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {motives minors : Array Expr} {lvls : List Level}
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    {decl : VInductDecl} {depth : Nat} {field value : Expr}
    (S : TypedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value) : Type where
  target : VExpr
  translation : TrExprS S.current_context.venv recLparams
    S.current_context.mlctx.vlctx
    (Expr.app
      (mkAppN motives[S.generated.ownerIdx]!
        S.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN field S.generated.localArgs)) target
  typing : S.current_context.venv.IsType recLparams.length
    S.current_context.mlctx.vlctx.toCtx target

/-- Typed recursive calls with the exact earlier-hypothesis suffix
retained at every call's context.  Unlike the compatibility staging above, this
is populated only by `loopUTemplates`, whose accumulator supplies the
literal recent suffix and its position in the call row. -/
structure TypedRecursiveCallsAfterHypotheses
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {fieldRoot : AddInductive.Context} {recLparams : List Name}
    (Rfield : RecursorContextWF fieldRoot recLparams)
    (decl : VInductDecl) (P : FVarId → Prop)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    ∃ originRoot,
      ∃ Rorigin : RecursorContextWF originRoot recLparams,
        ∃ priorHypotheses : Array Expr,
          ∃ _ : RecursorFVarSuffix Rfield Rorigin
              priorHypotheses,
            priorHypotheses.size = i ∧ Rorigin.chk = Rfield.chk ∧
              ∃ callDepth,
                ∃ S : TypedRecursiveCall indTypes stats
                  motives minors lvls Rorigin decl callDepth u[i] v[i]!,
                  S.rootScope = P ∧
                    Nonempty S.MotiveApplication

theorem TypedRecursiveCallsAfterHypotheses.toAbove
    (H : TypedRecursiveCallsAfterHypotheses indTypes stats
      motives minors lvls Rfield decl P u v done) :
    TypedRecursiveCallsAbove indTypes stats motives minors
      lvls Rfield decl P u v done where
  covered := H.covered
  size := H.size
  entries i hi hiu := by
    rcases H.entries i hi hiu with
      ⟨originRoot, Rorigin, prior, Hrecent, _hsize, _hchk, callDepth, S,
        hscope, _Hmotive⟩
    exact ⟨originRoot, Rorigin, Hrecent.contextExtension,
      callDepth, S, hscope⟩

theorem TypedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (decl : VInductDecl) (depth : Nat) (P : FVarId → Prop)
    (u : Array Expr) :
    TypedRecursiveCalls indTypes stats motives minors lvls
      R decl depth P u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

theorem RecursiveCallsPrefix.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context) (u : Array Expr) :
    RecursiveCallsPrefix indTypes stats motives minors lvls root
      u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

/-- One generated iota rule retaining the constructor-field context and the
binder-aware certificate for every recursive result. -/
structure RecursorRuleSyntax
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx : Nat) (rule : RecursorRule) where
  root : AddInductive.Context
  /-- Context used to close the shared parameter, motive, and minor prefix.
  Retained first-pass rules may have produced their constructor fields before
  later minors were introduced, so this context need not be `root`. -/
  outerRoot : AddInductive.Context
  root_wf : BindingContextWF root
  outer_wf : BindingContextWF outerRoot
  root_le_outer : BindingContextLE root outerRoot
  target : Expr
  allArgs : Array Expr
  recursiveArgs : Array Expr
  recursiveResults : Array Expr
  minor_valid : minorIdx < minors.size
  params_bound : FVarArrayIn outerRoot stats.params
  motives_bound : FVarArrayIn outerRoot motives
  minors_bound : FVarArrayIn outerRoot minors
  outer_binders_nodup :
    ((params_bound.fvars ++ motives_bound.fvars) ++
      minors_bound.fvars).Nodup
  all_args_bound : FVarArrayIn root allArgs
  recursive_args_bound : FVarArrayIn root recursiveArgs
  recursive_args_sublist : recursiveArgs.toList.Sublist allArgs.toList
  all_args_nodup : all_args_bound.fvars.Nodup
  recursive_args_nodup : recursive_args_bound.fvars.Nodup
  all_args_outer_fresh : ∀ fv ∈ all_args_bound.fvars,
    fv ∉ (params_bound.fvars ++ motives_bound.fvars) ++ minors_bound.fvars
  recursive_calls : RecursiveCallsPrefix indTypes stats motives
    minors lvls root recursiveArgs recursiveResults recursiveArgs.size
  ctor_eq : rule.ctor = ctor.name
  fields_eq : rule.nfields = allArgs.size
  rhs_eq : rule.rhs =
    (outerRoot.lctx.mkLambda stats.params <|
     outerRoot.lctx.mkLambda motives <|
     outerRoot.lctx.mkLambda minors <| root.lctx.mkLambda allArgs <|
     mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults)

/-- All source binders closed by a generated rule are globally distinct:
outer recursor binders are no-alias by construction, while constructor fields
are fresh relative to that outer context. -/
theorem RecursorRuleSyntax.binders_nodup
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    (((H.params_bound.fvars ++ H.motives_bound.fvars) ++
      H.minors_bound.fvars) ++ H.all_args_bound.fvars).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨H.outer_binders_nodup, H.all_args_nodup, ?_⟩
  intro outer houter field hfield heq
  subst outer
  exact H.all_args_outer_fresh field hfield houter

def RecursorRuleSyntax.binders
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) : List FVarId :=
  ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
    H.minors_bound.fvars) ++ H.all_args_bound.fvars

def RecursorRuleSyntax.sourceRhsBody
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  mkAppN (mkAppN minors[minorIdx]! H.allArgs) H.recursiveResults

/-- Constructor application appearing as the major premise of the generated
iota left-hand side. -/
def RecursorRuleSyntax.sourceConstructorMajor
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) H.allArgs

/-- Canonical source left-hand-side body determined by the residual target
returned from `loopCtorArgs`. -/
def RecursorRuleSyntax.sourceLhsBody
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  let (ownerIdx, indices) := AddInductive.getIIndices stats H.target
  let recursor := .const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls
  (mkAppN
    (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices).app H.sourceConstructorMajor

def RecursorRuleSyntax.all_binders_bound
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) : FVarArrayIn H.outerRoot
      (stats.params ++ motives ++ minors ++ H.allArgs) :=
  ((H.params_bound.append H.motives_bound).append H.minors_bound).append
    (H.all_args_bound.mono H.root_le_outer)

/-- Simultaneously closing the complete rule-binder payload produces the
canonical de Bruijn variables in source-binder order. -/
theorem RecursorRuleSyntax.abstractedBinders_eq
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    (((stats.params ++ motives ++ minors ++ H.allArgs).map
      fun arg => arg.abstractList H.binders).toList) =
      List.ofFn (fun i : Fin H.binders.length =>
        Expr.bvar (H.binders.length - 1 - i)) := by
  have hexpressions := H.all_binders_bound.expressions
  have hmapped := congrArg
    (fun args : Array Expr => args.map fun arg =>
      arg.abstractList H.binders) hexpressions
  have hfvars : H.all_binders_bound.fvars = H.binders := by
    rfl
  have hcanonical := Expr.abstractList_fvarArray
    H.binders 0 H.binders_nodup
  rw [hfvars, hcanonical] at hmapped
  simpa using congrArg Array.toList hmapped

/-- The parameter prefix of the simultaneously abstracted rule binders is
the corresponding prefix of canonical de Bruijn variables. -/
theorem RecursorRuleSyntax.abstractedParams_eq
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ((stats.params.map fun arg => arg.abstractList H.binders).toList) =
      List.ofFn (fun i : Fin stats.params.size =>
        Expr.bvar (H.binders.length - 1 - i)) := by
  have h := congrArg (List.take stats.params.size) H.abstractedBinders_eq
  have hparams : H.params_bound.fvars.length = stats.params.size := by
    have := congrArg Array.size H.params_bound.expressions
    simpa using this.symm
  have hle : stats.params.size ≤ H.binders.length := by
    unfold RecursorRuleSyntax.binders
    simp only [List.length_append]
    omega
  have htake :
      List.take stats.params.size
          (List.ofFn fun i : Fin H.binders.length =>
            Expr.bvar (H.binders.length - 1 - i)) =
        List.ofFn (fun i : Fin stats.params.size =>
          Expr.bvar (H.binders.length - 1 - i)) := by
    apply List.ext_getElem
    · simp [hle]
    · intro j hj₁ hj₂
      simp only [List.getElem_take, List.getElem_ofFn]
  have hprefix :
      ((stats.params.map fun arg => arg.abstractList H.binders).toList) =
        List.take stats.params.size
          (List.ofFn fun i : Fin H.binders.length =>
            Expr.bvar (H.binders.length - 1 - i)) := by
    simpa [Array.toList_append, List.take_append,
      List.take_of_length_le] using h
  exact hprefix.trans htake

theorem RecursorRuleSyntax.abstractedParamsTranslation
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((stats.params.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (H.binders.length - 1 - i)) := by
  have Htr := H.params_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders []
      (H.motives_bound.fvars ++ H.minors_bound.fvars ++
        H.all_args_bound.fvars)
      (by simp [RecursorRuleSyntax.binders, List.append_assoc])
      H.binders_nodup domains Δ hdomains
  simpa using Htr

theorem RecursorRuleSyntax.abstractedMotivesTranslation
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((motives.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin motives.size =>
        VExpr.bvar (H.binders.length - 1 -
          (H.params_bound.fvars.length + i))) := by
  exact H.motives_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders H.params_bound.fvars
      (H.minors_bound.fvars ++ H.all_args_bound.fvars)
      (by simp [RecursorRuleSyntax.binders, List.append_assoc])
      H.binders_nodup domains Δ hdomains

theorem RecursorRuleSyntax.abstractedMinorsTranslation
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((minors.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin minors.size =>
        VExpr.bvar (H.binders.length - 1 -
          ((H.params_bound.fvars ++ H.motives_bound.fvars).length + i))) := by
  exact H.minors_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders
      (H.params_bound.fvars ++ H.motives_bound.fvars)
      H.all_args_bound.fvars
      (by simp [RecursorRuleSyntax.binders, List.append_assoc])
      H.binders_nodup domains Δ hdomains

theorem RecursorRuleSyntax.abstractedAllArgsTranslation
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((H.allArgs.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin H.allArgs.size =>
        VExpr.bvar (H.binders.length - 1 -
          (((H.params_bound.fvars ++ H.motives_bound.fvars) ++
            H.minors_bound.fvars).length + i))) := by
  exact H.all_args_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders
      ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
        H.minors_bound.fvars) []
      (by simp [RecursorRuleSyntax.binders])
      H.binders_nodup domains Δ hdomains

/-- The four nested executable `mkLambda` calls are one exact, globally
no-alias lambda telescope over the retained binder sequence. -/
theorem RecursorRuleSyntax.rhs_eq_bindingList
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    rule.rhs = LocalContext.mkBindingListN true H.outerRoot.lctx
      H.binders H.sourceRhsBody := by
  rw [H.rhs_eq]
  symm
  unfold RecursorRuleSyntax.binders
    RecursorRuleSyntax.sourceRhsBody
  have hdecl : ∀ fv ∈
      ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
        H.minors_bound.fvars) ++ H.all_args_bound.fvars,
      ∃ decl, H.outerRoot.lctx.find? fv = some decl := by
    intro fv hfv
    have hmem : fv ∈ H.outerRoot.lctx.fvars := by
      rcases List.mem_append.mp hfv with houter | hall
      · rcases List.mem_append.mp houter with hpm | hminor
        · rcases List.mem_append.mp hpm with hparam | hmotive
          · exact H.params_bound.members fv hparam
          · exact H.motives_bound.members fv hmotive
        · exact H.minors_bound.members fv hminor
      · exact H.root_le_outer (H.all_args_bound.members fv hall)
    rcases H.outer_wf.findCDecl fv hmem with
      ⟨index, name, type, bi, kind, hfind⟩
    exact ⟨.cdecl index fv name type bi kind, hfind⟩
  rw [LocalContext.mkBindingListN_append_four hdecl H.binders_nodup]
  simp only [LocalContext.mkLambda, ← LocalContext.mkBinding_eqN]
  have hp : ({ toList := H.params_bound.fvars.map Expr.fvar } :
      Array Expr) = stats.params := by
    simpa using H.params_bound.expressions.symm
  have hm : ({ toList := H.motives_bound.fvars.map Expr.fvar } :
      Array Expr) = motives := by
    simpa using H.motives_bound.expressions.symm
  have hmi : ({ toList := H.minors_bound.fvars.map Expr.fvar } :
      Array Expr) = minors := by
    simpa using H.minors_bound.expressions.symm
  have ha : ({ toList := H.all_args_bound.fvars.map Expr.fvar } :
      Array Expr) = H.allArgs := by
    simpa using H.all_args_bound.expressions.symm
  rw [hp, hm, hmi, ha]
  have hfields := H.all_args_bound.mkLambda_mono H.root_le_outer
    (mkAppN (mkAppN minors[minorIdx]! H.allArgs) H.recursiveResults)
  simpa only [LocalContext.mkLambda, ← LocalContext.mkBinding_eqN] using
    congrArg (fun body =>
      H.outerRoot.lctx.mkLambda stats.params <|
        H.outerRoot.lctx.mkLambda motives <|
          H.outerRoot.lctx.mkLambda minors body) hfields

theorem RecursorRuleSyntax.rhsLambdaTelescope
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    Expr.LambdaTelescope rule.rhs H.binders.length
      (H.sourceRhsBody.abstractN H.binders) := by
  rw [H.rhs_eq_bindingList]
  exact LocalContext.mkBindingListN_lambdaTelescope
    (H.all_binders_bound.toCDeclArray
      H.outer_wf).declarations

/-- Simultaneous closing preserves the canonical recursor/constructor LHS
spines and abstracts every source argument pointwise. -/
theorem RecursorRuleSyntax.abstractedSourceLhs
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let (ownerIdx, indices) := AddInductive.getIIndices stats H.target
    H.sourceLhsBody.abstractList H.binders =
      (mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls)
              (stats.params.map fun arg => arg.abstractList H.binders))
            (motives.map fun arg => arg.abstractList H.binders))
          (minors.map fun arg => arg.abstractList H.binders))
        (indices.map fun arg => arg.abstractList H.binders)).app
      (mkAppN
        (mkAppN (.const ctor.name stats.levels)
          (stats.params.map fun arg => arg.abstractList H.binders))
        (H.allArgs.map fun arg => arg.abstractList H.binders)) := by
  rcases htarget : AddInductive.getIIndices stats H.target with
    ⟨ownerIdx, indices⟩
  simp only [RecursorRuleSyntax.sourceLhsBody, htarget,
    RecursorRuleSyntax.sourceConstructorMajor,
    Expr.abstractList_app, Expr.abstractList_mkAppN,
    Expr.abstractList_const]

/-- Inverting the translated canonical LHS exposes the exact recursor and
constructor constant spines matched by the `lhs_pattern` field of `VInductDecl.IotaRule`. -/
theorem RecursorRuleSyntax.translatedLhsResidual
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceLhsBody.abstractList H.binders) lhsBody) :
    ∃ recursorLevels leadingArgs ctorLevels ctorArgs,
      lhsBody = VExpr.mkApps
        (.const (Lean.mkRecName indTypes[ownerIdx]!.name) recursorLevels)
        (leadingArgs ++
          [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs]) ∧
      lvls.mapM (VLevel.ofLevel Us) = some recursorLevels ∧
      stats.levels.mapM (VLevel.ofLevel Us) = some ctorLevels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        ((stats.params.map fun arg => arg.abstractList H.binders).toList ++
          (motives.map fun arg => arg.abstractList H.binders).toList ++
          (minors.map fun arg => arg.abstractList H.binders).toList ++
          (indices.map fun arg => arg.abstractList H.binders).toList)
        leadingArgs ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        ((stats.params.map fun arg => arg.abstractList H.binders).toList ++
          (H.allArgs.map fun arg => arg.abstractList H.binders).toList)
        ctorArgs := by
  have hsource := H.abstractedSourceLhs
  rw [htarget] at hsource
  rw [hsource] at Htr
  let leadingSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList ++
    (motives.map fun arg => arg.abstractList H.binders).toList ++
    (minors.map fun arg => arg.abstractList H.binders).toList ++
    (indices.map fun arg => arg.abstractList H.binders).toList
  let ctorArgsSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList ++
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
  let ctorSource :=
    mkAppN
      (mkAppN (.const ctor.name stats.levels)
        (stats.params.map fun arg => arg.abstractList H.binders))
      (H.allArgs.map fun arg => arg.abstractList H.binders)
  have hrecursorHead :
      ((mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls)
              (stats.params.map fun arg => arg.abstractList H.binders))
            (motives.map fun arg => arg.abstractList H.binders))
          (minors.map fun arg => arg.abstractList H.binders))
        (indices.map fun arg => arg.abstractList H.binders)).app
          ctorSource).getAppFn =
        .const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls := by
    simp only [Expr.getAppFn, Expr.getAppFn_mkAppN]
  rcases checkPositivityStep.TrExprS.constAppSpine Htr hrecursorHead with
    ⟨recursorLevels, translatedArgs, hrecursorSpine, hrecursorLevels,
      HtranslatedArgs⟩
  have HtranslatedArgs' : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (leadingSource ++ [ctorSource]) translatedArgs := by
    simpa only [leadingSource, ctorSource, Expr.getAppArgsList_app,
      Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append, List.append_assoc]
      using HtranslatedArgs
  rcases checkPositivityStep.List.Forall₂.split_left HtranslatedArgs' with
    ⟨leadingArgs, translatedMajorTail, rfl, Hleading, HmajorTail⟩
  have hmajor : ∃ translatedMajor,
      translatedMajorTail = [translatedMajor] ∧
      TrExprS env Us (abstractForallContext domains Δ)
        ctorSource translatedMajor := by
    cases HmajorTail with
    | cons Hctor Hnil =>
      cases Hnil
      exact ⟨_, rfl, Hctor⟩
  rcases hmajor with ⟨translatedMajor, rfl, Hctor⟩
  have hctorHead : ctorSource.getAppFn =
      .const ctor.name stats.levels := by
    simp only [ctorSource, Expr.getAppFn_mkAppN, Expr.getAppFn]
  rcases checkPositivityStep.TrExprS.constAppSpine Hctor hctorHead with
    ⟨ctorLevels, ctorArgs, hctorSpine, hctorLevels, HctorArgs⟩
  have HctorArgs' : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ctorArgsSource ctorArgs := by
    simpa only [ctorArgsSource, ctorSource,
      Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append,
      List.append_assoc] using HctorArgs
  have hmajorRebuild := VExpr.mkApps_getAppFnArgs translatedMajor
  rw [hctorSpine] at hmajorRebuild
  have hlhsRebuild := VExpr.mkApps_getAppFnArgs lhsBody
  rw [hrecursorSpine] at hlhsRebuild
  refine ⟨recursorLevels, leadingArgs, ctorLevels, ctorArgs, ?_,
    hrecursorLevels, hctorLevels, ?_, ?_⟩
  · rw [← hmajorRebuild] at hlhsRebuild
    exact hlhsRebuild.symm
  · simpa [leadingSource] using Hleading
  · simpa [ctorArgsSource] using HctorArgs'

/-- Proof-side construction record for the `VDefEq` corresponding to one
executable `RecursorRule`. The executable record stores only its constructor,
field count, and RHS; this certificate makes the reconstructed LHS, common
telescope, and equation type an explicit refinement boundary. -/
structure RecursorRuleSyntax.EquationTranslation
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx) (rule : VDefEq) where
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  domains_length : domains.length = H.binders.length
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  lhs_residual : TrExprS trEnv Us (abstractForallContext domains Δ)
    (H.sourceLhsBody.abstractList H.binders) lhsBody
  rhs_residual : TrExprS trEnv Us (abstractForallContext domains Δ)
    (H.sourceRhsBody.abstractList H.binders) rhsBody

/-- The selected minor has a canonical de Bruijn position in the closed rule
telescope: constructor fields are newer, and the remaining minors occur in
reverse order immediately behind them. -/
theorem RecursorRuleSyntax.abstractedSourceRhsAtMinor
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let minorVar := H.all_args_bound.fvars.length +
      (H.minors_bound.fvars.length - 1 - minorIdx)
    H.sourceRhsBody.abstractList H.binders =
      mkAppN
        (mkAppN (.bvar minorVar)
          (H.allArgs.map fun arg => arg.abstractList H.binders))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders) := by
  rcases H.minors_bound.getElem_eq_fvar minorIdx H.minor_valid with
    ⟨hiFvars, hminor⟩
  let fv := H.minors_bound.fvars[minorIdx]
  let outerPrefix := H.params_bound.fvars ++ H.motives_bound.fvars
  let before := outerPrefix ++ H.minors_bound.fvars.take minorIdx
  let after := H.minors_bound.fvars.drop (minorIdx + 1) ++
    H.all_args_bound.fvars
  have hminorDecomp : H.minors_bound.fvars =
      H.minors_bound.fvars.take minorIdx ++ fv ::
        H.minors_bound.fvars.drop (minorIdx + 1) := by
    calc
      H.minors_bound.fvars =
          H.minors_bound.fvars.take (minorIdx + 1) ++
            H.minors_bound.fvars.drop (minorIdx + 1) :=
        (List.take_append_drop (minorIdx + 1) _).symm
      _ = (H.minors_bound.fvars.take minorIdx ++ [fv]) ++
          H.minors_bound.fvars.drop (minorIdx + 1) := by
        rw [List.take_succ_eq_append_getElem hiFvars]
      _ = H.minors_bound.fvars.take minorIdx ++ fv ::
          H.minors_bound.fvars.drop (minorIdx + 1) := by simp
  have hbindersDecomp : H.binders = before ++ fv :: after := by
    change ((outerPrefix ++ H.minors_bound.fvars) ++
      H.all_args_bound.fvars) = before ++ fv :: after
    rw [hminorDecomp]
    dsimp only [before, after]
    simp only [List.append_assoc]
    rw [List.cons_append]
  have hnodup : (before ++ fv :: after).Nodup := by
    rw [← hbindersDecomp]
    exact H.binders_nodup
  have habstract := Expr.abstractList_fvar_getElem
    hnodup before.length (by simp) (k := 0)
  have habstract' : (Expr.fvar fv).abstractList
      (before ++ fv :: after) =
      .bvar ((before ++ fv :: after).length - 1 - before.length) := by
    simpa using habstract
  let minorVar := H.all_args_bound.fvars.length +
    (H.minors_bound.fvars.length - 1 - minorIdx)
  have hafterLength : after.length = minorVar := by
    unfold after minorVar
    simp only [List.length_append, List.length_drop]
    omega
  have habstractFinal : (Expr.fvar fv).abstractList H.binders =
      .bvar minorVar := by
    rw [hbindersDecomp]
    simpa [hafterLength] using habstract'
  have hminorBang : minors[minorIdx]! = .fvar fv := by
    rw [Array.getElem!_eq_getD, Array.getD, dif_pos H.minor_valid]
    exact hminor
  unfold RecursorRuleSyntax.sourceRhsBody
  rw [Expr.abstractList_mkAppN, Expr.abstractList_mkAppN,
    hminorBang, habstractFinal]

theorem RecursorRuleSyntax.abstractedSourceRhsAtMinorArray
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let minorVar := H.allArgs.size + (minors.size - 1 - minorIdx)
    H.sourceRhsBody.abstractList H.binders =
      mkAppN
        (mkAppN (.bvar minorVar)
          (H.allArgs.map fun arg => arg.abstractList H.binders))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders) := by
  have hall : H.all_args_bound.fvars.length = H.allArgs.size := by
    have h := congrArg Array.size H.all_args_bound.expressions
    simpa using h.symm
  have hminors : H.minors_bound.fvars.length = minors.size := by
    have h := congrArg Array.size H.minors_bound.expressions
    simpa using h.symm
  simpa [hall, hminors] using H.abstractedSourceRhsAtMinor

/-- Pointwise semantic state retained from the actual `mkRecInfos` field and
recursive-call loops.  The concrete arrays and generated results are fixed by
`H`; this record stores only the independently checked classification and
recursive-domain facts that the executable `RecursorRule` omits. -/
structure RecursorRuleSyntax.Semantics
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (expectedOwnerIdx : Nat) where
  depth : Nat
  context : RecursorContextWF H.root recLparams
  fieldRoot : AddInductive.Context
  fieldRootContext : RecursorContextWF fieldRoot recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix fieldRootContext stats
    parameterDepth
  parameterDecls : VLCtx
  parameterDecls_eq : parameterSuffix.parameterDecls = parameterDecls
  /-- The field root of the minor pass precedes the rule's recursor context.
  Rule templates must preserve this direction; reversing it would amount
  to pretending that the fields were freshly replayed after installation. -/
  fieldRootExtension : RecursorContextExtension fieldRootContext Rroot
  fieldsRecent : RecursorFVarSuffix fieldRootContext context
    H.allArgs
  parameterTail : Expr
  parameterPrefix : ParameterPrefix stats 0 sourceCtor.type parameterTail
  parameterTail_fvars :
    parameterTail.FVarsIn (· ∈ ExprArrayFVarIds stats.params)
  parameterTarget : VExpr
  parameterTranslation : TrExprS fieldRootContext.venv recLparams
    fieldRootContext.mlctx.vlctx parameterTail parameterTarget
  parameterType : fieldRootContext.venv.IsType recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
  parameterTranslation₀ : ∃ t, TrExprS fieldRootContext.venv recLparams
      parameterSuffix.parameterDecls parameterTail t ∧
    fieldRootContext.venv.IsType recLparams.length
      parameterSuffix.parameterDecls.toCtx t
  fieldOpening : ConstructorFieldOpening parameterTail H.target H.allArgs
  fieldParameterUp : IsFVarUpSet (fun fv =>
    fv ∈ fieldsRecent.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params) context.mlctx.vlctx
  /-- The fields were also opened in the checker context, directly above the
  parameter declarations. -/
  fieldCheck : ∃ M : TypeChecker.MLCtx, M.WF context.venv recLparams ∧
    (0 < H.allArgs.size → context.chk = M) ∧
    ∃ hn : H.allArgs.size ≤ M.length,
      MLCtxTopAgree context.mlctx M H.allArgs.size ∧
        (M.dropN H.allArgs.size hn).vlctx = parameterSuffix.parameterDecls ∧
        ∃ T₀, TrExprS fieldRootContext.venv recLparams
          parameterSuffix.parameterDecls parameterTail T₀ ∧
        ∃ t₀', TrExprS context.venv recLparams M.vlctx H.target t₀' ∧
          context.venv.IsDefEqU recLparams.length
            parameterSuffix.parameterDecls.toCtx T₀
            (M.mkForall' H.allArgs.size hn t₀')
  context_venv : context.venv = Rroot.venv
  validStats : RecursorValidAppStatsWF context.venv recLparams
    context.mlctx.vlctx stats decl depth
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  expected_owner_lt : expectedOwnerIdx < decl.types.length
  expected_target_valid : AddInductive.isValidIndAppIdx stats H.target
    expectedOwnerIdx = true
  targetTarget : VExpr
  target_not_forall : H.target.isForall = false
  target_translation : TrExprS context.venv recLparams context.mlctx.vlctx
    H.target targetTarget
  target_type : context.venv.IsType recLparams.length
    context.mlctx.vlctx.toCtx targetTarget
  fieldTargetDefEq : fieldRootContext.venv.IsDefEqU recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
      (context.mlctx.mkForall' H.allArgs.size fieldsRecent.size_le
        targetTarget)
  constructorTarget : VExpr
  constructor_translation : TrExprS context.venv recLparams
    context.mlctx.vlctx H.sourceConstructorMajor constructorTarget
  constructor_typing : context.venv.HasType recLparams.length
    context.mlctx.vlctx.toCtx constructorTarget targetTarget
  target_valid : AddInductive.isValidIndApp? stats H.target = some ownerIdx
  validated : RecursorValidatedIndAppAt context.venv recLparams
    context.mlctx.vlctx stats decl depth H.target targetTarget ownerIdx
  fields : List
    (RecursiveFieldDomainAt context.venv decl recLparams.length)
  selection : RecursiveFieldSelectionsAt context.venv decl recLparams.length
    H.allArgs H.recursiveArgs fields
  decisionPositions : List Nat
  decisions : RecursorFieldDecisions stats fieldRoot parameterTail H.root
    H.target H.allArgs H.recursiveArgs decisionPositions
  calls : TypedRecursiveCallsAbove indTypes stats motives
    minors lvls context decl
      (fun fv => fv ∈ fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      H.recursiveArgs H.recursiveResults
      H.recursiveArgs.size

/-- Alpha-independent mask selected by the rule-generation field traversal. -/
def RecursorRuleSyntax.Semantics.recursivePositions
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) : List Nat :=
  S.decisionPositions

@[simp] theorem
    RecursorRuleSyntax.Semantics.recursivePositions_length
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    S.recursivePositions.length = H.recursiveArgs.size := by
  exact S.decisions.positions_length

/-- Once the two alpha-independent masks agree, their executable recursive
arrays have the same cardinality.  This isolates the sole cross-pass fact
needed by recursive minor application from either pass's fresh identifiers. -/
theorem ConstructorFieldTraversal.recursiveFields_size_eq_rule
    {stats : AddInductive.InductiveStats}
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (T : ConstructorFieldTraversal)
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (hpositions : T.recursivePositions = S.recursivePositions) :
    T.recursiveFields.size = H.recursiveArgs.size := by
  rw [← T.recursivePositions_length, hpositions,
    S.recursivePositions_length]

/-- The generated minor introduces exactly one hypothesis per rule recursive
result as soon as its retained traversal mask is aligned with the rule mask. -/
theorem MinorPremiseType.hypotheses_size_eq_rule
    {stats : AddInductive.InductiveStats}
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (M : MinorPremiseType) (T : ConstructorFieldTraversal)
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (hrecursive : T.recursiveFields = M.recursiveFields)
    (hpositions : T.recursivePositions = S.recursivePositions) :
    M.hypotheses.size = H.recursiveArgs.size := by
  rw [M.hypotheses_size, ← hrecursive]
  exact T.recursiveFields_size_eq_rule S hpositions

/-- The exact constructor-field suffix, closed back into the semantic context
that preceded `loopCtorArgs`.  Both sides are deliberately retained: the
forall telescope types the constructor target, while the lambda telescope
types the constructor application used as the iota major premise. -/
structure RecursorRuleSyntax.Semantics.FieldTelescope
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) where
  domains : List VExpr
  domains_length : domains.length = H.allArgs.size
  target_translation : TrExprS S.fieldRootContext.venv recLparams
    S.fieldRootContext.mlctx.vlctx
    (H.root.lctx.mkForall H.allArgs H.target)
    (VExpr.wrapForalls domains S.targetTarget)
  target_type : S.fieldRootContext.venv.IsType recLparams.length
    S.fieldRootContext.mlctx.vlctx.toCtx
    (VExpr.wrapForalls domains S.targetTarget)
  major_translation : TrExprS S.fieldRootContext.venv recLparams
    S.fieldRootContext.mlctx.vlctx
    (H.root.lctx.mkLambda H.allArgs H.sourceConstructorMajor)
    (VExpr.wrapLams domains S.constructorTarget)
  major_typing : S.fieldRootContext.venv.HasType recLparams.length
    S.fieldRootContext.mlctx.vlctx.toCtx
    (VExpr.wrapLams domains S.constructorTarget)
    (VExpr.wrapForalls domains S.targetTarget)

/-- The terminal constructor target mentions only the exact fields opened by
the constructor traversal and the cached inductive parameters. -/
theorem RecursorRuleSyntax.Semantics.targetFVarsIn
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    H.target.FVarsIn (fun fv =>
      fv ∈ S.fieldsRecent.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params) := by
  have hscope := S.fieldOpening.currentFVarsIn S.parameterTail_fvars
  rw [S.fieldOpening.fvars_eq_bound
    S.fieldsRecent.toFVarArrayAfter.toFVarArrayIn] at hscope
  exact hscope

/-- Recover the typed field telescope directly from the consecutive-suffix
certificate retained by the executable constructor traversal. -/
def RecursorRuleSyntax.Semantics.fieldTelescope
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    S.FieldTelescope := by
  let domains := MLCtxForallDomains S.context.mlctx H.allArgs.size
    S.fieldsRecent.size_le
  have Htarget := S.fieldsRecent.mkForallExact S.target_translation
    S.target_type
  have Hmajor := S.fieldsRecent.mkLambda S.constructor_translation
    S.constructor_typing
  exact {
    domains := domains
    domains_length := by
      exact S.context.onlyLams.forallDomains_length H.allArgs.size
        S.fieldsRecent.size_le
    target_translation := by simpa [domains] using Htarget.1
    target_type := by simpa [domains] using Htarget.2
    major_translation := by simpa [domains] using Hmajor.1
    major_typing := by simpa [domains] using Hmajor.2 }

/-- Transport the field-context conversion of the minor pass forward to the
rule's recursor context.  The field telescope is exposed after the
exact free-variable lift retained by `fieldRootExtension`; no equality of
the two local contexts is assumed. -/
theorem RecursorRuleSyntax.Semantics.fieldContextDefEqMono
    {H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    ∃ sourceDomains sourceResidual consumedDomains consumedResidual,
      sourceDomains.length = H.allArgs.size ∧
      consumedDomains.length = H.allArgs.size ∧
      TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx S.parameterTail
        (VExpr.wrapForalls sourceDomains sourceResidual) ∧
      (VExpr.wrapForalls S.fieldTelescope.domains S.targetTarget).lift'
          (S.fieldRootExtension.shift.consN 0) =
        VExpr.wrapForalls consumedDomains consumedResidual ∧
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        (sourceDomains.reverse ++ Rroot.mlctx.vlctx.toCtx)
        (consumedDomains.reverse ++ Rroot.mlctx.vlctx.toCtx) := by
  have Hparameter := S.fieldRootExtension.weakTrExprS S.parameterTranslation
  rcases TrExprS.forallTelescope_shape S.fieldOpening.telescope Hparameter with
    ⟨sourceDomains, sourceResidual, hsourceLength, hsourceTarget⟩
  let F := S.fieldTelescope
  rcases VExpr.lift'_wrapForalls_shape F.domains S.targetTarget
      (S.fieldRootExtension.shift.consN 0) with
    ⟨consumedDomains, consumedResidual, hconsumedLength, hconsumedTarget⟩
  have hconsumedLength' : consumedDomains.length = H.allArgs.size :=
    hconsumedLength.trans F.domains_length
  have HfieldTarget : S.fieldRootContext.venv.IsDefEqU recLparams.length
      S.fieldRootContext.mlctx.vlctx.toCtx S.parameterTarget
      (VExpr.wrapForalls F.domains S.targetTarget) := by
    simpa [F, RecursorRuleSyntax.Semantics.fieldTelescope,
      TypeChecker.MLCtx.mkForall'_eq_wrapForalls] using S.fieldTargetDefEq
  have Htarget := S.fieldRootExtension.weakDefEqU HfieldTarget
  rw [hsourceTarget, hconsumedTarget] at Htarget
  have Hsource : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
      S.parameterTail (VExpr.wrapForalls sourceDomains sourceResidual) := by
    rw [← hsourceTarget]
    exact Hparameter
  have Hbase : VEnv.IsDefEqCtx Rroot.venv recLparams.length []
      Rroot.mlctx.vlctx.toCtx Rroot.mlctx.vlctx.toCtx :=
    .refl Rroot.mlctx_wf.tr.wf.toCtx
  exact ⟨sourceDomains, sourceResidual, consumedDomains, consumedResidual,
    hsourceLength, hconsumedLength', Hsource, hconsumedTarget,
    VEnv.IsDefEqU.wrapForalls_context Rroot.checking.tr.wf Hbase
      (hsourceLength.trans hconsumedLength'.symm) Htarget⟩

/-- Duplicate-free declaration names identify the first family selected by
`isValidIndApp?` with the constructor owner certified by the earlier checker
pass.  This is the explicit link between the scan used by rule generation
and the outer mutual-family traversal. -/
theorem RecursorRuleSyntax.Semantics.owner_eq
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hsemantic : H.Semantics Rroot decl expectedOwnerIdx)
    (hnames : (decl.types.map (·.name)).Nodup) :
    Hsemantic.ownerIdx = expectedOwnerIdx := by
  have hselectedValid : AddInductive.isValidIndAppIdx stats H.target
      Hsemantic.ownerIdx = true :=
    (checkPositivityStep.isValidIndApp?_some Hsemantic.target_valid).2
  have hselectedHead : H.target.getAppFn =
      .const (decl.types[Hsemantic.ownerIdx]'Hsemantic.owner_lt).name
        stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead hselectedValid
      (Hsemantic.validStats.indConstAt Hsemantic.owner_lt)
  have hexpectedHead : H.target.getAppFn =
      .const
        (decl.types[expectedOwnerIdx]'Hsemantic.expected_owner_lt).name
        stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead
      Hsemantic.expected_target_valid
      (Hsemantic.validStats.indConstAt Hsemantic.expected_owner_lt)
  have hname :
      (decl.types[Hsemantic.ownerIdx]'Hsemantic.owner_lt).name =
      (decl.types[expectedOwnerIdx]'Hsemantic.expected_owner_lt).name := by
    have heq := hselectedHead.symm.trans hexpectedHead
    injection heq
  have hleft : Hsemantic.ownerIdx < (decl.types.map (·.name)).length := by
    simpa using Hsemantic.owner_lt
  have hright : expectedOwnerIdx <
      (decl.types.map (·.name)).length := by
    simpa using Hsemantic.expected_owner_lt
  apply (List.getElem_inj (h₀ := hleft) (h₁ := hright) hnames).mp
  simpa only [List.getElem_map] using hname

/-- Ordered binder-aware coverage of a constructor suffix. -/
inductive RecursorRulesSyntax
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : RecursorRulesSyntax indTypes stats motives minors lvls
      [] start []
  | cons :
      Nonempty (RecursorRuleSyntax indTypes stats motives minors
        lvls ctor start rule) →
      RecursorRulesSyntax indTypes stats motives minors lvls
        ctors (start + 1) rules →
      RecursorRulesSyntax indTypes stats motives minors lvls
        (ctor :: ctors) start (rule :: rules)

/-- Semantic strengthening of `RecursorRulesSyntax`.  Each emitted
source rule is paired with the exact classifier and recursive-call facts
from the same executable iteration; the tail advances the flattened minor
ordinal in lockstep. -/
inductive TypedRecursorRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (ownerIdx : Nat) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : TypedRecursorRules indTypes stats motives minors
      lvls Rroot decl ownerIdx [] start []
  | cons
      (Hrule : RecursorRuleSyntax indTypes stats motives minors lvls
        ctor start rule)
      (Hsemantic : Nonempty
        (Hrule.Semantics Rroot decl ownerIdx))
      (Htail : TypedRecursorRules indTypes stats motives
        minors lvls Rroot decl ownerIdx ctors (start + 1)
          rules) :
      TypedRecursorRules indTypes stats motives minors lvls
        Rroot decl ownerIdx (ctor :: ctors) start
          (rule :: rules)

theorem TypedRecursorRules.bound
    (H : TypedRecursorRules indTypes stats motives minors
      lvls Rroot decl ownerIdx ctors start rules) :
    RecursorRulesSyntax indTypes stats motives minors lvls ctors
      start rules := by
  induction H with
  | nil => exact .nil
  | cons Hrule _ _ ih => exact .cons ⟨Hrule⟩ ih

theorem RecursorRulesSyntax.length
    (H : RecursorRulesSyntax indTypes stats motives minors lvls
      ctors start rules) : rules.length = ctors.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RecursorRulesSyntax.entry
    (H : RecursorRulesSyntax indTypes stats motives minors lvls
      ctors start rules) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      Nonempty (RecursorRuleSyntax indTypes stats motives minors
        lvls ctors[i] (start + i) rules[i]) := by
  induction H with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor start rule ctors rules Hrule Htail ih =>
      intro i hctor hrule
      cases i with
      | zero => simpa using Hrule
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        simpa only [List.getElem_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 i] using h

end VerifyInductive
end Lean4Lean
