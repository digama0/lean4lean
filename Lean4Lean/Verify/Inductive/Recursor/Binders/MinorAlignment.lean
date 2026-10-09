import Lean4Lean.Verify.Inductive.Recursor.Binders.BinderFrames

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-! ### `loopArgs1` runs

`mkRecInfos.loopInd1` normalizes each family header with `whnf` and opens its
parameter and index binders with `mkRecInfos.loopArgs1`, normalizing every
instantiated body again.  The index declarations of the recursor context are
domains of these `whnf` outputs.  The relations below record each such call
together with the recursor-context well-formedness of the context it ran in, so
that facts about the lifted `whnf` (for example preservation of a syntactic
shape) apply along the run. -/

/-- One lifted `whnf` call of the motive pass, run in a context
`ctx` below `final`.  `P` is a free-variable up-set of the abstract context
containing the input's free variables; its members satisfy `Q` and are
variables of `ctx`. -/
def WhnfRunAt (final : AddInductive.Context) (Q : FVarId → Prop)
    (input output : Expr) : Prop :=
  ∃ (ctx : AddInductive.Context) (recLparams : List Name)
    (Rc : RecursorContextWF ctx recLparams) (P : FVarId → Prop)
    (target : VExpr),
    BindingContextLE ctx final ∧
    TrExprS Rc.venv recLparams Rc.mlctx.vlctx input target ∧
    IsFVarUpSet P Rc.mlctx.vlctx ∧
    (∀ fv, P fv → Q fv ∧ fv ∈ ctx.lctx.fvars) ∧
    input.FVarsIn P ∧
    (monadLift (TypeChecker.whnf input) : AddInductive.M Expr) ctx = .ok output ∧
    ∃ target₀, TrExprS Rc.venv recLparams Rc.chk.vlctx input target₀

theorem WhnfRunAt.mono {final final' : AddInductive.Context}
    {Q Q' : FVarId → Prop} {input output : Expr}
    (H : WhnfRunAt final Q input output)
    (hle : BindingContextLE final final') (hQ : ∀ fv, Q fv → Q' fv) :
    WhnfRunAt final' Q' input output := by
  obtain ⟨ctx, recLparams, Rc, P, target, hctx, htr, hup, hP, hin, hrun, htr₀⟩ := H
  exact ⟨ctx, recLparams, Rc, P, target, hctx.trans hle, htr, hup,
    fun fv h => ⟨hQ fv (hP fv h).1, (hP fv h).2⟩, hin, hrun, htr₀⟩

/-- Successful prefix of `whnf header >>= loopArgs1 stats · 0 #[]`:
the header normalization, the parameter steps (instantiating the cached
parameters `stats.params`) and the index steps (opening a fresh index
variable `x`, declared in `final` with the unannotated domain). The
`Nat` index is the number of parameters instantiated, the `Expr` the current
normalized type and the array the opened indices. -/
inductive IndexTelescopeRun (stats : AddInductive.InductiveStats)
    (final : AddInductive.Context) (header : Expr) :
    Nat → Expr → Array Expr → Prop
  | start {normalized : Expr}
      (call : WhnfRunAt final (fun _ => False) header normalized) :
      IndexTelescopeRun stats final header 0 normalized #[]
  | param {i : Nat} {name : Name} {dom body normalized : Expr}
      {bi : BinderInfo}
      (previous : IndexTelescopeRun stats final header i
        (.forallE name dom body bi) #[])
      (hi : i < stats.params.size)
      (call : WhnfRunAt final
        (fun fv => fv ∈ ExprArrayFVarIds stats.params)
        (body.instantiate1 stats.params[i]!) normalized) :
      IndexTelescopeRun stats final header (i + 1) normalized #[]
  | index {indices : Array Expr} {name : Name} {dom body normalized : Expr}
      {bi : BinderInfo} {x : FVarId}
      (previous : IndexTelescopeRun stats final header stats.params.size
        (.forallE name dom body bi) indices)
      (member : x ∈ final.lctx.fvars)
      (declaration : ∃ index userName binderInfo kind,
        final.lctx.find? x = some (.cdecl index x userName
          (dom.consumeTypeAnnotationsVerified final.env.isTypeAnnotationWrapper)
          binderInfo kind))
      (call : WhnfRunAt final
        (fun fv => fv ∈ ExprArrayFVarIds stats.params ∨
          fv ∈ ExprArrayFVarIds (indices.push (.fvar x)))
        (body.instantiate1 (.fvar x)) normalized) :
      IndexTelescopeRun stats final header stats.params.size normalized
        (indices.push (.fvar x))

theorem IndexTelescopeRun.mono {stats : AddInductive.InductiveStats}
    {final final' : AddInductive.Context} {header : Expr}
    (hle : BindingContextLE final final') {i : Nat} {type : Expr}
    {indices : Array Expr}
    (H : IndexTelescopeRun stats final header i type indices) :
    IndexTelescopeRun stats final' header i type indices := by
  induction H with
  | start call => exact .start (call.mono hle fun _ h => h)
  | param _ hi call ih => exact .param ih hi (call.mono hle fun _ h => h)
  | index _ member declaration call ih =>
    obtain ⟨index, userName, binderInfo, kind, hfind⟩ := declaration
    refine .index ih (hle.fvars member)
      ⟨index, userName, binderInfo, kind, ?_⟩ (call.mono hle fun _ h => h)
    rw [hle.declarations _ member, hle.env_eq]
    exact hfind

/-- Every family's index telescope was opened by a `loopArgs1`
run (`IndexTelescopeRun`) starting at the family header `indTypes[i].type`. -/
def IndexTelescopeRuns (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size → ∃ type,
    IndexTelescopeRun stats c indTypes[i]!.type stats.params.size type
      recInfos[i]!.indices

theorem IndexTelescopeRuns.empty {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {c : AddInductive.Context} :
    IndexTelescopeRuns stats indTypes c #[] := by
  intro i hi
  simp at hi

theorem IndexTelescopeRuns.mono {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {c c' : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    (H : IndexTelescopeRuns stats indTypes c recInfos)
    (hle : BindingContextLE c c') :
    IndexTelescopeRuns stats indTypes c' recInfos := by
  intro i hi
  obtain ⟨type, T⟩ := H i hi
  exact ⟨type, T.mono hle⟩

theorem IndexTelescopeRuns.push {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {c : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    (H : IndexTelescopeRuns stats indTypes c recInfos)
    (info : AddInductive.RecInfo) {type : Expr}
    (T : IndexTelescopeRun stats c indTypes[recInfos.size]!.type
      stats.params.size type info.indices) :
    IndexTelescopeRuns stats indTypes c (recInfos.push info) := by
  intro i hi
  by_cases hlast : i = recInfos.size
  · subst i
    refine ⟨type, ?_⟩
    simpa using T
  · have hold : i < recInfos.size := by
      simp only [Array.size_push] at hi
      omega
    have hget : (recInfos.push info)[i]! = recInfos[i]! := by
      rw [getElem!_pos _ i hi, getElem!_pos _ i hold]
      exact Array.getElem_push_lt hold
    rw [hget]
    exact H i hold

/-- The runs only see the index arrays of the records. -/
theorem IndexTelescopeRuns.congr {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {c : AddInductive.Context}
    {left right : Array AddInductive.RecInfo}
    (H : IndexTelescopeRuns stats indTypes c left)
    (hsize : left.size = right.size)
    (hindices : ∀ i, i < left.size → left[i]!.indices = right[i]!.indices) :
    IndexTelescopeRuns stats indTypes c right := by
  intro i hi
  have hi' : i < left.size := by omega
  rw [← hindices i hi']
  exact H i hi'

theorem IndexTelescopeRuns.modifyMinors {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {c : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    (H : IndexTelescopeRuns stats indTypes c recInfos)
    (dIdx : Nat) (f : Array Expr → Array Expr) :
    IndexTelescopeRuns stats indTypes c (recInfos.modify dIdx fun info =>
      { info with minors := f info.minors }) := by
  refine H.congr (by simp) fun i hi => ?_
  by_cases hdi : dIdx = i
  · subst i
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hi]
  · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hdi]

/-- Every minor shape names the executable constructor list of its
owning source family, together with the constructor traversal that produced it.
The minor pass of `mkRecInfos` and rule generation may allocate different
locals, but they traverse the same owner-indexed constructor arrays. -/
def MinorsMatchConstructors
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (H : RecInfoBinderTypes c recInfos) : Prop :=
  ∀ owner (howner : owner < recInfos.size)
    (_hsourceOwner : owner < indTypes.size)
    localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
    let S := H.minorShapes owner howner localIndex hlocal;
      S.origin = H.minorTypes[owner]![localIndex]! ∧
      S.localIndex = localIndex ∧
      S.sourceConstructors = indTypes[owner]!.ctors ∧
      S.HasInductionHypothesisTypes stats recInfos ∧
        ∃ traversal, S.traversal = some traversal ∧
          traversal.constructor = S.constructor ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          AddInductive.isValidIndApp? stats traversal.terminal = some
            (AddInductive.getIIndices stats traversal.terminal).1 ∧
          S.motiveApp = (
            let (motiveOwner, indices) :=
              AddInductive.getIIndices stats traversal.terminal
            Expr.app
              (mkAppN recInfos[motiveOwner]!.motive indices)
              (mkAppN
                (mkAppN (.const S.constructor.name stats.levels)
                  stats.params)
                S.fields)) ∧
          BindingContextLE traversal.rootContext c ∧
          BindingContextLE traversal.terminalContext c ∧
          BindingContextLE S.sourceFullContext c

/-- The source alignment of a recursor construction: the
minor rows (`MinorsMatchConstructors`) together with the `loopArgs1`
runs of every family's index telescope (`IndexTelescopeRuns`). -/
def MinorsAndIndicesMatchSource
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (H : RecInfoBinderTypes c recInfos) : Prop :=
  MinorsMatchConstructors stats indTypes H ∧
    IndexTelescopeRuns stats indTypes c recInfos

theorem MinorsAndIndicesMatchSource.rows
    {H : RecInfoBinderTypes c recInfos}
    (A : MinorsAndIndicesMatchSource stats indTypes H) :
    MinorsMatchConstructors stats indTypes H := A.1

theorem MinorsAndIndicesMatchSource.traces
    {H : RecInfoBinderTypes c recInfos}
    (A : MinorsAndIndicesMatchSource stats indTypes H) :
    IndexTelescopeRuns stats indTypes c recInfos := A.2

/-- Typed counterpart of `MinorsAndIndicesMatchSource` for one
minor.  The structural alignment records that the source context embeds in
the current local context; this structure also records the
translation-side lift produced by that executable extension.  Keeping the
source `RecursorContextWF` existential avoids fixing a particular sequence of
intermediate field and hypothesis binders in the minor shape. -/
structure TypedMinorTraversal
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (S : MinorPremiseType) where
  sourceWF : RecursorContextWF S.sourceFullContext recLparams
  extension : RecursorContextExtension sourceWF R
  traversal : ConstructorFieldTraversal
  traversal_eq : S.traversal = some traversal
  traversal_fields : traversal.fields = S.fields
  rootWF : RecursorContextWF traversal.rootContext recLparams
  terminalWF : RecursorContextWF traversal.terminalContext recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix rootWF traversal.stats
    parameterDepth
  parameterScope : traversal.parameterTail.FVarsIn
    (fun fv => fv ∈ parameterSuffix.parameterDecls.fvars)
  parameterTarget : VExpr
  parameterTranslation : TrExprS rootWF.venv recLparams
    rootWF.mlctx.vlctx traversal.parameterTail parameterTarget
  parameterType : rootWF.venv.IsType recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
  /-- The same tail translated directly in the cached parameter suffix. -/
  parameterTranslation₀ : ∃ t, TrExprS rootWF.venv recLparams
    parameterSuffix.parameterDecls traversal.parameterTail t
  fieldsRecent : RecursorFVarSuffix rootWF terminalWF S.fields
  /-- The fields were also opened in the checker context directly above the
  parameter declarations, and the checker closure of the terminal agrees
  with the parameter-scope translation of the tail. -/
  fieldCheck : ∃ M : TypeChecker.MLCtx, M.WF terminalWF.venv recLparams ∧
    (0 < S.fields.size → terminalWF.chk = M) ∧
    ∃ hn : S.fields.size ≤ M.length,
      MLCtxTopAgree terminalWF.mlctx M S.fields.size ∧
        (M.dropN S.fields.size hn).vlctx = parameterSuffix.parameterDecls ∧
        ∃ T₀, TrExprS rootWF.venv recLparams parameterSuffix.parameterDecls
          traversal.parameterTail T₀ ∧
        ∃ t₀', TrExprS terminalWF.venv recLparams M.vlctx
          traversal.terminal t₀' ∧
          terminalWF.venv.IsDefEqU recLparams.length
            parameterSuffix.parameterDecls.toCtx T₀
            (M.mkForall' S.fields.size hn t₀')
  /-- The opening chosen by the minor-pass constructor
  traversal.  Rule construction reads this opening instead of
  opening the constructor telescope a second time. -/
  fieldOpening : ConstructorFieldOpening traversal.parameterTail
    traversal.terminal S.fields
  fieldParameterUp : IsFVarUpSet (fun fv =>
    fv ∈ fieldsRecent.fvars ∨
      fv ∈ ExprArrayFVarIds traversal.stats.params) terminalWF.mlctx.vlctx
  hypothesesRecent : RecursorFVarSuffix terminalWF sourceWF
    S.hypotheses
  terminalTarget : VExpr
  terminalTranslation : TrExprS terminalWF.venv recLparams
    terminalWF.mlctx.vlctx traversal.terminal terminalTarget
  terminalType : terminalWF.venv.IsType recLparams.length
    terminalWF.mlctx.vlctx.toCtx terminalTarget
  /-- The checked constructor application at the end of the
  field traversal.  This lets the template-based rule builder recover its
  constructor typing without repeating field classification or type
  checking. -/
  constructorApplication : ConstructorApplicationAt terminalWF
    traversal.stats traversal.constructor traversal.terminal S.fields
    terminalTarget
  fieldTargetDefEq : rootWF.venv.IsDefEqU recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
      (terminalWF.mlctx.mkForall' S.fields.size fieldsRecent.size_le
        terminalTarget)
  /-- The source motive application is assembled before recursive-hypothesis
  locals are opened.  Recording this derivation before weakening makes the later
  hypothesis closure visibly alpha-invariant. -/
  motivePreTarget : VExpr
  motivePreTranslation : TrExprS terminalWF.venv recLparams
    terminalWF.mlctx.vlctx S.motiveApp motivePreTarget
  motivePreType : terminalWF.venv.IsType recLparams.length
    terminalWF.mlctx.vlctx.toCtx motivePreTarget
  /-- The application head is an outer motive binder, introduced before the
  fresh constructor fields. -/
  motiveHeadRoot : ∃ fv,
    S.motiveApp.getAppFn = .fvar fv ∧
      fv ∈ rootWF.mlctx.vlctx.fvars
  motiveTarget : VExpr
  motiveTranslation : TrExprS sourceWF.venv recLparams
    sourceWF.mlctx.vlctx S.motiveApp motiveTarget
  motiveType : sourceWF.venv.IsType recLparams.length
    sourceWF.mlctx.vlctx.toCtx motiveTarget
  sourceTarget : VExpr
  unannotatedTarget : VExpr
  consumption : sourceWF.UnannotatedDomain S.sourceType sourceTarget
    unannotatedTarget

def TypedMinorTraversal.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {S : MinorPremiseType}
    (HS : TypedMinorTraversal Rroot S)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    TypedMinorTraversal Rcurrent S where
  sourceWF := HS.sourceWF
  extension := HS.extension.trans Hext
  traversal := HS.traversal
  traversal_eq := HS.traversal_eq
  traversal_fields := HS.traversal_fields
  rootWF := HS.rootWF
  terminalWF := HS.terminalWF
  parameterDepth := HS.parameterDepth
  parameterSuffix := HS.parameterSuffix
  parameterScope := HS.parameterScope
  parameterTarget := HS.parameterTarget
  parameterTranslation := HS.parameterTranslation
  parameterType := HS.parameterType
  parameterTranslation₀ := HS.parameterTranslation₀
  fieldsRecent := HS.fieldsRecent
  fieldCheck := HS.fieldCheck
  fieldOpening := HS.fieldOpening
  fieldParameterUp := HS.fieldParameterUp
  hypothesesRecent := HS.hypothesesRecent
  terminalTarget := HS.terminalTarget
  terminalTranslation := HS.terminalTranslation
  terminalType := HS.terminalType
  constructorApplication := HS.constructorApplication
  fieldTargetDefEq := HS.fieldTargetDefEq
  motivePreTarget := HS.motivePreTarget
  motivePreTranslation := HS.motivePreTranslation
  motivePreType := HS.motivePreType
  motiveHeadRoot := HS.motiveHeadRoot
  motiveTarget := HS.motiveTarget
  motiveTranslation := HS.motiveTranslation
  motiveType := HS.motiveType
  sourceTarget := HS.sourceTarget
  unannotatedTarget := HS.unannotatedTarget
  consumption := HS.consumption

/-- Recursive hypotheses are introduced only after the selected-motive
application has been assembled.  Closing their fresh identifiers therefore
leaves that source application unchanged. -/
theorem TypedMinorTraversal.abstractHypotheses_motiveApp
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : MinorPremiseType}
    (HS : TypedMinorTraversal R S) :
    S.motiveApp.abstractList S.hypotheses_bound.fvars = S.motiveApp := by
  have hclosed : Closed S.motiveApp 0 := by
    have h := HS.motivePreTranslation.closed
    rw [HS.terminalWF.mlctx.noBV] at h
    simpa using h
  have hscope := HS.motivePreTranslation.fvarsIn
  have havoids : S.motiveApp.FVarsIn
      (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply hscope.mono
    intro fv hterminal hhypothesis
    have hhypothesisFVars : HS.hypothesesRecent.fvars =
        S.hypotheses_bound.fvars :=
      FVarArrayIn.fvars_eq_of_array_eq
        HS.hypothesesRecent.toFVarArrayAfter.toFVarArrayIn
        S.hypotheses_bound rfl
    rw [← hhypothesisFVars] at hhypothesis
    apply HS.hypothesesRecent.fresh fv hhypothesis
    rw [← HS.terminalWF.lctx_eq,
      HS.terminalWF.mlctx_wf.tr.fvars_eq]
    exact hterminal
  exact havoids.abstractList_eq_self hclosed

/-- Stripping binder annotations cannot change a generated minor type.  A
nonempty field/hypothesis telescope starts with a genuine forall binder.  In
the degenerate empty-telescope case the residual is an application headed by
the freshly bound motive variable, so it cannot be any of Lean's four
top-level parameter-annotation encodings either. -/
theorem TypedMinorTraversal.sourceType_consumeTypeAnnotations_eq_self
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : MinorPremiseType}
    (HS : TypedMinorTraversal R S) {ok : Name → Bool} :
    (S.sourceType.consumeTypeAnnotationsVerified ok) = S.sourceType := by
  by_cases hpositive : 0 < S.fields.size + S.hypotheses.size
  · exact S.sourceTelescope.consumeTypeAnnotationsVerified_eq_self_of_pos hpositive
  · have hfields : S.fields.size = 0 := by omega
    have hhypotheses : S.hypotheses.size = 0 := by omega
    have hfieldsEmpty : S.fields = #[] :=
      Array.eq_empty_of_size_eq_zero hfields
    have hhypothesesEmpty : S.hypotheses = #[] :=
      Array.eq_empty_of_size_eq_zero hhypotheses
    have hsource : S.sourceType = S.motiveApp := by
      rw [S.sourceType_eq, hfieldsEmpty, hhypothesesEmpty,
        LocalContext.mkForall_empty, LocalContext.mkForall_empty]
    rw [hsource]
    rcases HS.motiveHeadRoot with ⟨motiveFVar, hhead, _hmotiveRoot⟩
    apply Expr.consumeTypeAnnotationsVerified_eq_self
    · change S.motiveApp.isAppOfArity `optParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change S.motiveApp.isAppOfArity `autoParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change S.motiveApp.isAppOfArity `outParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change S.motiveApp.isAppOfArity `semiOutParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _

/-- Restrict the shared constructor-tail translation to the cached parameter
suffix.  The ambient motives and previously generated minors cannot occur in
that source by the field-traversal scope invariant. -/
theorem TypedMinorTraversal.parameterTranslationAtSuffix
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : MinorPremiseType}
    (HS : TypedMinorTraversal R S) :
    ∃ target, TrExprS HS.rootWF.venv recLparams
      HS.parameterSuffix.parameterDecls HS.traversal.parameterTail target :=
  HS.parameterTranslation₀

structure TypedMinorTraversalAt
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (S : MinorPremiseType)
    (parameterDecls : VLCtx) where
  semantic : TypedMinorTraversal R S
  parameterDecls_eq : semantic.parameterSuffix.parameterDecls =
    parameterDecls

def TypedMinorTraversalAt.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {S : MinorPremiseType} {parameterDecls : VLCtx}
    (HS : TypedMinorTraversalAt Rroot S parameterDecls)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    TypedMinorTraversalAt Rcurrent S parameterDecls where
  semantic := HS.semantic.mono Hext
  parameterDecls_eq := HS.parameterDecls_eq

/-- Every minor source carries its typed extension (`TypedMinorTraversal`) into the
current recursor context.  Unlike `BindingContextLE`, this invariant is strong
enough to transport or restrict translated declaration types without guessing
how later named locals shift their de Bruijn targets. -/
def TypedMinors
    {c : AddInductive.Context} {recInfos : Array AddInductive.RecInfo}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (H : RecInfoBinderTypes c recInfos) (parameterDecls : VLCtx) : Prop :=
  ∀ owner (howner : owner < recInfos.size)
    localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
    Nonempty (TypedMinorTraversalAt R
      (H.minorShapes owner howner localIndex hlocal) parameterDecls)

theorem TypedMinors.ofEmpty
    (R : RecursorContextWF c recLparams)
    (H : RecInfoBinderTypes c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos) :
    TypedMinors R H parameterDecls := by
  intro owner howner localIndex hlocal
  have hsize := (H.minors owner howner).size_eq
  rw [Hempty owner howner] at hsize
  omega

theorem TypedMinors.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {recInfos : Array AddInductive.RecInfo}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {H : RecInfoBinderTypes root recInfos}
    (A : TypedMinors Rroot H parameterDecls)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    TypedMinors Rcurrent (H.mono Hext.contextLE)
      parameterDecls := by
  intro owner howner localIndex hlocal
  rcases A owner howner localIndex hlocal with ⟨HS⟩
  exact ⟨HS.mono Hext⟩

theorem TypedMinors.addMinor
    {root current : AddInductive.Context} {recLparams : List Name}
    {recInfos : Array AddInductive.RecInfo}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {H : RecInfoBinderTypes root recInfos}
    (A : TypedMinors Rroot H parameterDecls)
    (Hext : RecursorContextExtension Rroot Rcurrent)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    {minorTarget : VExpr}
    (Hminor : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      minorTy minorTarget)
    (HminorType : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx minorTarget)
    (Hshape : MinorPremiseType)
    (HshapeSemantic : Nonempty
      (TypedMinorTraversalAt Rcurrent Hshape parameterDecls)) :
    TypedMinors
      (Rcurrent.withLocalDecl (name := minorName) (bi := minorBi)
        Hminor HminorType)
      (H.addMinor dIdx hidx Hext.contextLE Rcurrent.toBindingContextWF
        minorName minorTy minorBi Hshape) parameterDecls := by
  let Rnext := Rcurrent.withLocalDecl (name := minorName) (bi := minorBi)
    Hminor HminorType
  let Hstep := RecursorContextExtension.withLocalDecl
    (name := minorName) (bi := minorBi) Rcurrent Hminor HminorType
  let nextMinorTypes := H.minorTypes.modify dIdx fun types =>
    types.push minorTy
  intro owner howner localIndex hlocal
  have hownerOld : owner < recInfos.size := by simpa using howner
  have hownerTypes : owner < H.minorTypes.size := by
    rw [H.minorTypes_size]
    exact hownerOld
  by_cases hdi : dIdx = owner
  · subst owner
    have horigin : nextMinorTypes[dIdx]! =
        H.minorTypes[dIdx]!.push minorTy := by
      dsimp [nextMinorTypes]
      rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
        hownerTypes]
    change localIndex < nextMinorTypes[dIdx]!.size at hlocal
    rw [horigin] at hlocal
    by_cases hlast : localIndex = H.minorTypes[dIdx]!.size
    · subst localIndex
      rcases HshapeSemantic with ⟨HS⟩
      simpa [RecInfoBinderTypes.addMinor, nextMinorTypes,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hownerTypes] using
        (show Nonempty
            (TypedMinorTraversalAt Rnext Hshape parameterDecls) from
          ⟨HS.mono Hstep⟩)
    · have hold : localIndex < H.minorTypes[dIdx]!.size := by
        simp only [Array.size_push] at hlocal
        omega
      rcases A dIdx hidx localIndex hold with ⟨HS⟩
      have hget : (H.minorTypes[dIdx]!.push minorTy)[localIndex]! =
          H.minorTypes[dIdx]![localIndex]! := by
        have hpush : localIndex <
            (H.minorTypes[dIdx]!.push minorTy).size := by simp; omega
        rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy) localIndex hpush,
          getElem!_pos H.minorTypes[dIdx]! localIndex hold]
        exact Array.getElem_push_lt hold
      simpa [RecInfoBinderTypes.addMinor, hlast,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hownerTypes, hget] using
        (show Nonempty (TypedMinorTraversalAt Rnext
            (H.minorShapes dIdx hidx localIndex hold) parameterDecls) from
          ⟨HS.mono (Hext.trans Hstep)⟩)
  · have horigin : nextMinorTypes[owner]! = H.minorTypes[owner]! := by
      dsimp [nextMinorTypes]
      rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner _
        hownerTypes hdi]
    change localIndex < nextMinorTypes[owner]!.size at hlocal
    rw [horigin] at hlocal
    rcases A owner hownerOld localIndex hlocal with ⟨HS⟩
    simpa [RecInfoBinderTypes.addMinor, hdi,
      mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner
        (fun types => types.push minorTy) hownerTypes hdi] using
      (show Nonempty (TypedMinorTraversalAt Rnext
          (H.minorShapes owner hownerOld localIndex hlocal)
            parameterDecls) from
        ⟨HS.mono (Hext.trans Hstep)⟩)

theorem MinorsMatchConstructors.ofEmpty
    (H : RecInfoBinderTypes c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos) :
    MinorsMatchConstructors stats indTypes H := by
  intro owner howner _ localIndex hlocal
  have hsize := (H.minors owner howner).size_eq
  rw [Hempty owner howner] at hsize
  omega

theorem MinorsMatchConstructors.mono
    {c c' : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoBinderTypes c recInfos}
    (A : MinorsMatchConstructors stats indTypes H)
    (hle : BindingContextLE c c') :
    MinorsMatchConstructors stats indTypes (H.mono hle) := by
  intro owner howner hsourceOwner localIndex hlocal
  rcases A owner howner hsourceOwner localIndex hlocal with
    ⟨horigin, hindex, hsource, hhypothesisOrigins,
      traversal, htraversal, hconstructor,
      hfields, hrecursive, hstats, hvalid, hmotiveApp,
      hroot, hterminal,
      hsourceContext⟩
  exact ⟨horigin, hindex, hsource, hhypothesisOrigins,
    traversal, htraversal, hconstructor,
    hfields, hrecursive, hstats, hvalid, hmotiveApp,
    hroot.trans hle,
    hterminal.trans hle, hsourceContext.trans hle⟩

theorem MinorsMatchConstructors.addMinor
    {c cMinorTy : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoBinderTypes c recInfos}
    (A : MinorsMatchConstructors stats indTypes H)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (Hshape : MinorPremiseType)
    (HshapePosition :
      Hshape.localIndex = H.minorTypes[dIdx]!.size ∧
      Hshape.origin = minorTy)
    (hsource : Hshape.sourceConstructors = indTypes[dIdx]!.ctors)
    (hhypothesisOrigins : Hshape.HasInductionHypothesisTypes stats recInfos)
    (htraversal : ∃ traversal,
      Hshape.traversal = some traversal ∧
      traversal.constructor = Hshape.constructor ∧
      traversal.fields = Hshape.fields ∧
      traversal.recursiveFields = Hshape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      Hshape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const Hshape.constructor.name stats.levels)
              stats.params)
            Hshape.fields)) ∧
      BindingContextLE traversal.rootContext cMinorTy ∧
      BindingContextLE traversal.terminalContext cMinorTy ∧
      BindingContextLE Hshape.sourceFullContext cMinorTy) :
    MinorsMatchConstructors stats indTypes
      (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
        Hshape) := by
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy HcMinorTy
    minorName minorTy minorBi
  let hfinal := hle.trans hstep
  let nextRecInfos := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }
  have hmotives : nextRecInfos.map (·.motive) =
      recInfos.map (·.motive) := by
    apply Array.ext
    · simp [nextRecInfos]
    · intro owner hleft hright
      by_cases howner : dIdx = owner <;>
        simp [nextRecInfos, Array.getElem_modify, howner]
  have motiveAppNext (S : MinorPremiseType)
      (traversal : ConstructorFieldTraversal)
      (Happ : S.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const S.constructor.name stats.levels) stats.params)
            S.fields))) :
      S.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN nextRecInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const S.constructor.name stats.levels) stats.params)
            S.fields)) := by
    rw [Happ]
    have hmotiveGet : ∀ motiveOwner : Nat,
        AddInductive.RecInfo.motive nextRecInfos[motiveOwner]! =
          AddInductive.RecInfo.motive recInfos[motiveOwner]! := by
      intro motiveOwner
      by_cases hi : motiveOwner < recInfos.size
      · by_cases hdi : dIdx = motiveOwner <;>
          simp [nextRecInfos, hi,
            Array.getElem_modify, hdi]
      · simp [nextRecInfos, hi]
    rcases AddInductive.getIIndices stats traversal.terminal with
      ⟨motiveOwner, indices⟩
    simp only
    rw [hmotiveGet]
  have hypothesisOriginsNext (S : MinorPremiseType)
      (HS : S.HasInductionHypothesisTypes stats recInfos) :
      S.HasInductionHypothesisTypes stats nextRecInfos := by
    unfold MinorPremiseType.HasInductionHypothesisTypes at HS ⊢
    cases horigins : S.hypothesis_type_origins with
    | none => simp [horigins] at HS
    | some origins =>
      simp only [horigins] at HS ⊢
      exact ⟨HS.1, HS.2.trans hmotives.symm⟩
  have htraversalFinal : ∃ traversal,
      Hshape.traversal = some traversal ∧
      traversal.constructor = Hshape.constructor ∧
      traversal.fields = Hshape.fields ∧
      traversal.recursiveFields = Hshape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      Hshape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN nextRecInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const Hshape.constructor.name stats.levels)
              stats.params)
            Hshape.fields)) ∧
      BindingContextLE traversal.rootContext cMinor ∧
      BindingContextLE traversal.terminalContext cMinor ∧
      BindingContextLE Hshape.sourceFullContext cMinor := by
    rcases htraversal with
      ⟨traversal, hsome, hconstructor, hfields, hrecursive, hstats,
        hvalid, hmotiveApp, hroot, hterminal, hsourceContext⟩
    exact ⟨traversal, hsome, hconstructor, hfields, hrecursive, hstats,
      hvalid, motiveAppNext Hshape traversal hmotiveApp,
      hroot.trans hstep,
      hterminal.trans hstep,
      hsourceContext.trans hstep⟩
  have Aextended : ∀ owner (howner : owner < recInfos.size)
      (hsourceOwner : owner < indTypes.size)
      localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
      let S := H.minorShapes owner howner localIndex hlocal;
        S.origin = H.minorTypes[owner]![localIndex]! ∧
        S.localIndex = localIndex ∧
        S.sourceConstructors = indTypes[owner]!.ctors ∧
        S.HasInductionHypothesisTypes stats nextRecInfos ∧
          ∃ traversal, S.traversal = some traversal ∧
            traversal.constructor = S.constructor ∧
            traversal.fields = S.fields ∧
            traversal.recursiveFields = S.recursiveFields ∧
            traversal.stats = stats ∧
            AddInductive.isValidIndApp? stats traversal.terminal = some
              (AddInductive.getIIndices stats traversal.terminal).1 ∧
            S.motiveApp = (
              let (motiveOwner, indices) :=
                AddInductive.getIIndices stats traversal.terminal
              Expr.app
                (mkAppN nextRecInfos[motiveOwner]!.motive indices)
                (mkAppN
                  (mkAppN (.const S.constructor.name stats.levels)
                    stats.params)
                  S.fields)) ∧
            BindingContextLE traversal.rootContext cMinor ∧
            BindingContextLE traversal.terminalContext cMinor ∧
            BindingContextLE S.sourceFullContext cMinor := by
    intro owner howner hsourceOwner localIndex hlocal
    rcases A owner howner hsourceOwner localIndex hlocal with
      ⟨horigin, hindex, hsource, hhypothesisOrigins,
        traversal, hsome, hconstructor,
        hfields, hrecursive, hstats, hvalid, hmotiveApp,
        hroot, hterminal,
        hsourceContext⟩
    exact ⟨horigin, hindex, hsource,
      hypothesisOriginsNext _ hhypothesisOrigins,
      traversal, hsome, hconstructor,
      hfields, hrecursive, hstats, hvalid,
      motiveAppNext _ traversal hmotiveApp,
      hroot.trans hfinal,
      hterminal.trans hfinal, hsourceContext.trans hfinal⟩
  intro owner howner hsourceOwner localIndex hlocal
  by_cases hdi : dIdx = owner
  · subst owner
    have hiTypes : dIdx < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hidx
    have horigin : (H.minorTypes.modify dIdx fun types =>
        types.push minorTy)[dIdx]! = H.minorTypes[dIdx]!.push minorTy := by
      rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
        hiTypes]
    change localIndex < (H.minorTypes.modify dIdx fun types =>
      types.push minorTy)[dIdx]!.size at hlocal
    rw [horigin] at hlocal
    by_cases hlast : localIndex = H.minorTypes[dIdx]!.size
    · subst localIndex
      simpa [RecInfoBinderTypes.addMinor,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hiTypes,
        getElem!_pos (H.minorTypes[dIdx]!.push minorTy)
          H.minorTypes[dIdx]!.size (by simp)] using
        ⟨HshapePosition.2, HshapePosition.1, hsource,
          hypothesisOriginsNext _ hhypothesisOrigins, htraversalFinal⟩
    · have hold : localIndex < H.minorTypes[dIdx]!.size := by
        simp only [Array.size_push] at hlocal
        omega
      have hget : (H.minorTypes[dIdx]!.push minorTy)[localIndex]! =
          H.minorTypes[dIdx]![localIndex]! := by
        have hpush : localIndex <
            (H.minorTypes[dIdx]!.push minorTy).size := by simp; omega
        rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy) localIndex hpush,
          getElem!_pos H.minorTypes[dIdx]! localIndex hold]
        exact Array.getElem_push_lt hold
      simpa [RecInfoBinderTypes.addMinor, hlast,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hiTypes, hget] using
        Aextended dIdx hidx hsourceIdx localIndex hold
  · have hownerOld : owner < recInfos.size := by simpa using howner
    have hownerTypes : owner < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hownerOld
    have horigin : (H.minorTypes.modify dIdx fun types =>
        types.push minorTy)[owner]! = H.minorTypes[owner]! := by
      rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner _
        hownerTypes hdi]
    change localIndex < (H.minorTypes.modify dIdx fun types =>
      types.push minorTy)[owner]!.size at hlocal
    rw [horigin] at hlocal
    have hlocalOld : localIndex < H.minorTypes[owner]!.size := by
      exact hlocal
    simpa [RecInfoBinderTypes.addMinor, hdi,
      mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner
        (fun types => types.push minorTy) hownerTypes hdi] using
      Aextended owner hownerOld hsourceOwner localIndex hlocalOld

theorem MinorsAndIndicesMatchSource.ofEmpty
    (H : RecInfoBinderTypes c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Htraces : IndexTelescopeRuns stats indTypes c recInfos) :
    MinorsAndIndicesMatchSource stats indTypes H :=
  ⟨MinorsMatchConstructors.ofEmpty H Hempty, Htraces⟩

theorem MinorsAndIndicesMatchSource.mono
    {c c' : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoBinderTypes c recInfos}
    (A : MinorsAndIndicesMatchSource stats indTypes H)
    (hle : BindingContextLE c c') :
    MinorsAndIndicesMatchSource stats indTypes (H.mono hle) :=
  ⟨A.rows.mono hle, A.traces.mono hle⟩

theorem MinorsAndIndicesMatchSource.addMinor
    {c cMinorTy : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoBinderTypes c recInfos}
    (A : MinorsAndIndicesMatchSource stats indTypes H)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (Hshape : MinorPremiseType)
    (HshapePosition :
      Hshape.localIndex = H.minorTypes[dIdx]!.size ∧
      Hshape.origin = minorTy)
    (hsource : Hshape.sourceConstructors = indTypes[dIdx]!.ctors)
    (hhypothesisOrigins : Hshape.HasInductionHypothesisTypes stats recInfos)
    (htraversal : ∃ traversal,
      Hshape.traversal = some traversal ∧
      traversal.constructor = Hshape.constructor ∧
      traversal.fields = Hshape.fields ∧
      traversal.recursiveFields = Hshape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      Hshape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const Hshape.constructor.name stats.levels)
              stats.params)
            Hshape.fields)) ∧
      BindingContextLE traversal.rootContext cMinorTy ∧
      BindingContextLE traversal.terminalContext cMinorTy ∧
      BindingContextLE Hshape.sourceFullContext cMinorTy) :
    MinorsAndIndicesMatchSource stats indTypes
      (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
        Hshape) :=
  ⟨A.rows.addMinor dIdx hidx hsourceIdx hle HcMinorTy minorName minorTy
      minorBi Hshape HshapePosition hsource hhypothesisOrigins htraversal,
    (A.traces.mono (hle.trans (BindingContextLE.withLocalDecl cMinorTy
      HcMinorTy minorName minorTy minorBi))).modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨cMinorTy.ngen.curr⟩))⟩

private def recInfoMinorIds (info : AddInductive.RecInfo) : List FVarId :=
  ExprArrayFVarIds info.minors

private theorem recInfoMinorIds_flatMap_eq_nil
    (infos : List AddInductive.RecInfo)
    (hempty : ∀ info ∈ infos, info.minors.size = 0) :
    infos.flatMap recInfoMinorIds = [] := by
  induction infos with
  | nil => rfl
  | cons info infos ih =>
    have hhead : info.minors = #[] :=
      Array.eq_empty_of_size_eq_zero (hempty info (by simp))
    have htail : ∀ tailInfo ∈ infos, tailInfo.minors.size = 0 := by
      intro tailInfo htailInfo
      exact hempty tailInfo (by simp [htailInfo])
    rw [List.flatMap_cons, ih htail]
    simp [recInfoMinorIds, hhead, ExprArrayFVarIds]

/-- Appending a minor in row `i` appends it to the flattened minor order when
all later rows are still empty. -/
private theorem recInfoMinorIds_modify_eq
    (infos : List AddInductive.RecInfo) (i : Nat) (hi : i < infos.length)
    (minor : Expr)
    (hlater : ∀ j, i < j → j < infos.length →
      infos[j]!.minors.size = 0) :
    (infos.modify i fun info =>
      { info with minors := info.minors.push minor }).flatMap
        recInfoMinorIds =
      infos.flatMap recInfoMinorIds ++ [recursorFVarId minor] := by
  induction infos generalizing i with
  | nil => simp at hi
  | cons info infos ih =>
    cases i with
    | zero =>
      have htailRows : ∀ tailInfo ∈ infos,
          tailInfo.minors.size = 0 := by
        intro tailInfo htailInfo
        rcases List.mem_iff_getElem.mp htailInfo with ⟨j, hj, rfl⟩
        have h := hlater (j + 1) (by omega) (by simpa using hj)
        rw [getElem!_pos (info :: infos) (j + 1) (by simpa using hj)] at h
        simpa using h
      have htail := recInfoMinorIds_flatMap_eq_nil infos htailRows
      simp [List.modify, recInfoMinorIds, ExprArrayFVarIds, htail]
    | succ i =>
      have hi' : i < infos.length := by simpa using hi
      have hlater' : ∀ j, i < j → j < infos.length →
          infos[j]!.minors.size = 0 := by
        intro j hij hj
        have h := hlater (j + 1) (by omega) (by simpa using hj)
        simpa using h
      rw [List.modify, List.modifyTailIdx_succ_cons]
      change (recInfoMinorIds info ++
        (infos.modify i fun info =>
          { info with minors := info.minors.push minor }).flatMap
            recInfoMinorIds) = _
      rw [ih i hi' hlater']
      simp [List.append_assoc]

theorem RecInfoBindings.addMinor_flatMinors_fvars
    (H : RecInfoBindings c recInfos)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0) :
    (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
      ).flatMinors.fvars = H.flatMinors.fvars ++
        [(⟨cMinorTy.ngen.curr⟩ : FVarId)] := by
  let minor := Expr.fvar ⟨cMinorTy.ngen.curr⟩
  let next := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push minor }
  have hlaterList : ∀ j, dIdx < j → j < recInfos.toList.length →
      recInfos.toList[j]!.minors.size = 0 := by
    intro j hdj hj
    have hj' : j < recInfos.size := by simpa using hj
    rw [getElem!_pos recInfos.toList j (by simpa using hj)]
    have h := hlater j hdj hj'
    rw [getElem!_pos recInfos j hj'] at h
    simpa using h
  have hflat := recInfoMinorIds_modify_eq recInfos.toList dIdx
    (by simpa using hidx) minor hlaterList
  rw [← (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy
      minorBi).flatMinors.exprArrayFVarIds,
    ← H.flatMinors.exprArrayFVarIds]
  change ((recInfos.toList.modify dIdx fun info =>
      { info with minors := info.minors.push minor }).flatMap
        (fun info => info.minors.toList.map recursorFVarId)) =
    recInfos.toList.flatMap
      (fun info => info.minors.toList.map recursorFVarId) ++
        [recursorFVarId minor] at hflat
  simpa [next, minor, recInfoMinorIds, ExprArrayFVarIds,
    Array.toList_flatMap, List.map_flatMap, recursorFVarId] using hflat

theorem RecInfoBindings.addMinor_motives_fvars
    (H : RecInfoBindings c recInfos)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
      ).motives.fvars = H.motives.fvars := by
  rw [← (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy
      minorBi).motives.exprArrayFVarIds,
    ← H.motives.exprArrayFVarIds]
  apply congrArg ExprArrayFVarIds
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]

private theorem recInfoMinorIds_modify_perm
    (infos : List AddInductive.RecInfo) (i : Nat) (hi : i < infos.length)
    (minor : Expr) :
    ((infos.modify i fun info =>
      { info with minors := info.minors.push minor }).flatMap
        recInfoMinorIds).Perm
      (infos.flatMap recInfoMinorIds ++ [recursorFVarId minor]) := by
  induction infos generalizing i with
  | nil => simp at hi
  | cons info infos ih =>
    cases i with
    | zero =>
      rw [List.modify, List.modifyTailIdx_zero, List.modifyHead_cons]
      simp only [List.flatMap_cons, recInfoMinorIds,
        ExprArrayFVarIds, Array.toList_push, List.map_append,
        List.map_cons, List.map_nil]
      simpa [List.append_assoc] using
        (List.Perm.refl
          (info.minors.toList.map recursorFVarId)).append
            (List.perm_append_comm :
              [recursorFVarId minor] ++ infos.flatMap recInfoMinorIds ~
                infos.flatMap recInfoMinorIds ++ [recursorFVarId minor])
    | succ i =>
      have hi' : i < infos.length := by simpa using hi
      rw [List.modify, List.modifyTailIdx_succ_cons]
      change (recInfoMinorIds info ++
        (infos.modify i fun info =>
          { info with minors := info.minors.push minor }).flatMap
            recInfoMinorIds).Perm _
      simpa only [List.flatMap_cons, List.append_assoc] using
        (List.Perm.refl (recInfoMinorIds info)).append
          (ih i hi')

theorem RecInfoBindings.addMinor_allFvars_perm
    (params : Array Expr) (recInfos : Array AddInductive.RecInfo)
    (dIdx : Nat) (hidx : dIdx < recInfos.size) (minorFVar : FVarId) :
    (RecInfoBindings.allFvars params (recInfos.modify dIdx fun info =>
        { info with minors := info.minors.push (.fvar minorFVar) })).Perm
      (RecInfoBindings.allFvars params recInfos ++ [minorFVar]) := by
  let minor := Expr.fvar minorFVar
  let next := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push minor }
  have hMotives : next.map (·.motive) = recInfos.map (·.motive) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hMajors : next.map (·.major) = recInfos.map (·.major) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hIndexRows : next.map (·.indices) = recInfos.map (·.indices) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hIndices : next.flatMap (·.indices) =
      recInfos.flatMap (·.indices) := by
    rw [Array.flatMap_def, Array.flatMap_def, hIndexRows]
  have hMinors :
      (ExprArrayFVarIds (next.flatMap (·.minors))).Perm
        (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
          [(minorFVar : FVarId)]) := by
    have h := recInfoMinorIds_modify_perm recInfos.toList dIdx
      (by simpa using hidx) minor
    change ((recInfos.toList.modify dIdx fun info =>
        { info with minors := info.minors.push minor }).flatMap
          (fun info => info.minors.toList.map recursorFVarId)).Perm
      (recInfos.toList.flatMap
        (fun info => info.minors.toList.map recursorFVarId) ++
          [recursorFVarId minor]) at h
    dsimp [minor, recursorFVarId] at h
    simpa [next, minor, ExprArrayFVarIds, Array.toList_flatMap,
      List.map_flatMap] using h
  unfold RecInfoBindings.allFvars
  change (ExprArrayFVarIds params ++
    (ExprArrayFVarIds (next.map (·.motive)) ++
      (ExprArrayFVarIds (next.flatMap (·.minors)) ++
        (ExprArrayFVarIds (next.flatMap (·.indices)) ++
          ExprArrayFVarIds (next.map (·.major)))))).Perm _
  rw [hMotives, hIndices, hMajors]
  let pre := ExprArrayFVarIds params ++
    ExprArrayFVarIds (recInfos.map (·.motive))
  let suffix := ExprArrayFVarIds (recInfos.flatMap (·.indices)) ++
    ExprArrayFVarIds (recInfos.map (·.major))
  have hMove :
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
        [(minorFVar : FVarId)]) ++ suffix ~
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++ suffix) ++
        [(minorFVar : FVarId)] := by
    simpa [List.append_assoc] using
      (List.Perm.refl
        (ExprArrayFVarIds (recInfos.flatMap (·.minors)))).append
          (List.perm_append_comm :
            [(minorFVar : FVarId)] ++ suffix ~
              suffix ++ [(minorFVar : FVarId)])
  have hTail := (hMinors.append (List.Perm.refl suffix)).trans hMove
  simpa [pre, suffix, List.append_assoc] using
    (List.Perm.refl pre).append hTail

theorem RecInfoBindings.addMinor_noAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy) :
    RecInfoBindings.NoAlias stats.params (recInfos.modify dIdx fun info =>
      { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }) := by
  let minor : FVarId := ⟨cMinorTy.ngen.curr⟩
  have hfresh : minor ∉ RecInfoBindings.allFvars stats.params recInfos := by
    intro hmem
    exact HcMinorTy.current_not_mem <| hle <|
      H.allFvars_members Hparams minor hmem
  have hcombined : (RecInfoBindings.allFvars stats.params recInfos ++ [minor]).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hnoalias, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hfresh (heq ▸ hfv)⟩
  apply (RecInfoBindings.addMinor_allFvars_perm stats.params recInfos dIdx hidx
    ⟨cMinorTy.ngen.curr⟩).symm.nodup
  simpa [minor] using hcombined

end VerifyInductive
end Lean4Lean
