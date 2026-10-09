import Lean4Lean.Verify.Inductive.Rules.Motive

/-! The frame of one recursive call in a rule's right-hand side
(`RecursorCheck.RuleAlignment.RecursiveCallFrame`): the recursor selected by the call together
with the earlier-hypothesis suffix recorded by the minor pass. Also the dependency-selected
scope core `FVarCheckingScopeCore` used to close call-local arguments, and the rule-wide scope
of constructor fields above the cached parameters. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Recursor-environment package selected by one generated recursive
call.  Besides the checked call semantics, it retains the literal earlier-
hypothesis suffix recorded by the minor pass.  Thus the call's context is related to the
rule root by executable allocation history, not by an assumed context
equality. -/
structure
    RecursorCheck.RuleAlignment.RecursiveCallFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) where
  sourceShape : MinorPremiseType
  hypothesisOrigins : MinorInductionHypothesisTypes
    sourceShape.sourceFullContext sourceShape.recursiveFields
      sourceShape.hypotheses
  hypothesisOrigins_eq :
    sourceShape.hypothesis_type_origins = some hypothesisOrigins
  sourceOriginRoot : AddInductive.Context
  sourceType : Expr
  sourceOrigin : InductionHypothesisType hypothesisOrigins.stats
    hypothesisOrigins.recInfos sourceOriginRoot
      sourceShape.recursiveFields[j]! sourceType
  sourceDeclaration : FVarDeclAt sourceShape.sourceFullContext
    sourceShape.hypotheses j
  sourceDeclaration_type : sourceDeclaration.type =
    (sourceType.consumeTypeAnnotationsVerified
      sourceShape.sourceFullContext.env.isTypeAnnotationWrapper)
  originRoot : AddInductive.Context
  originContext : RecursorContextWF originRoot
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
  priorHypotheses : Array Expr
  originRecent : RecursorFVarSuffix A.typing.context
    originContext priorHypotheses
  originCheck : originContext.chk = A.typing.context.chk
  priorHypotheses_size : priorHypotheses.size = j
  callDepth : Nat
  semantic : TypedRecursiveCall indTypes stats
    (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels H.elimLevel stats.levels)
    originContext decl callDepth
    A.rule.recursiveArgs[j] A.rule.recursiveResults[j]!
  motiveApplication : Nonempty semantic.MotiveApplication
  motiveLookup : MotiveTelescopesAt A.typing.context stats decl
    H.recInfos H.elimLevel
  root_scope : semantic.rootScope = fun fv =>
    fv ∈ A.typing.fieldOpening.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params
  replay : sourceOrigin.replayTrace sourceShape.fields_bound.fvars =
    semantic.generated.replayTrace A.rule.all_args_bound.fvars
  typing_eq : HEq semantic (A.minorReplayAt j hj).semantic
  producerReplay_eq :
    (A.minorReplayAt j hj).semantic.generated.replayTrace
        A.rule.all_args_bound.fvars =
      semantic.generated.replayTrace A.rule.all_args_bound.fvars
  entry_lt : semantic.generated.ownerIdx < H.entries.length
  telescope : RecursorTypeTelescope H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (H.generated.entry semantic.generated.ownerIdx entry_lt).info.type
    H.entries[semantic.generated.ownerIdx].2.type
    stats.params.size (H.recInfos.map (·.motive)).size
    (H.recInfos.flatMap (·.minors)).size
    H.recInfos[semantic.generated.ownerIdx]!.indices.size
    semantic.generated.ownerIdx
  typing :
    let recursor := H.entries[semantic.generated.ownerIdx].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type

/-- The extension from the rule's recursor context to the call's context, derived
from the retained earlier-hypothesis suffix.  It is not a field or premise of the call frame. -/
def RecursorCheck.RuleAlignment.RecursiveCallFrame.originExtension
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    RecursorContextExtension A.typing.context F.originContext :=
  F.originRecent.contextExtension

theorem
    RecursorCheck.RuleAlignment.recursiveCallFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    Nonempty (A.RecursiveCallFrame j hj) := by
  let Horigin := A.minorOrigin
  let Hproducer := Horigin.producer
  let P := A.minorReplayAt j hj
  let originRoot := P.originRoot
  let Rorigin := P.originContext
  let S := P.semantic
  have hrecInfo : S.generated.ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records]
    exact S.validated.target_lt
  have hentry : S.generated.ownerIdx < H.entries.length := by
    simpa [H.generated.length] using hrecInfo
  rcases H.installedRecursorTelescopeTranslationAt
      S.generated.ownerIdx hentry with ⟨T⟩
  exact ⟨{
    sourceShape := A.minorShape
    hypothesisOrigins := P.hypothesisOrigins
    hypothesisOrigins_eq := P.hypothesisOrigins_eq
    sourceOriginRoot := P.sourceOriginRoot
    sourceType := P.sourceType
    sourceOrigin := P.sourceOrigin
    sourceDeclaration := P.sourceDeclaration
    sourceDeclaration_type := P.sourceDeclaration_type
    originRoot := originRoot
    originContext := Rorigin
    priorHypotheses := P.priorHypotheses
    originRecent := P.originRecent
    originCheck := P.originCheck
    priorHypotheses_size := P.priorHypotheses_size
    callDepth := P.callDepth
    semantic := S
    motiveApplication := P.motiveApplication
    motiveLookup := Hproducer.motiveLookup
    root_scope := P.root_scope
    replay := P.replay
    typing_eq := HEq.rfl
    producerReplay_eq := rfl
    entry_lt := hentry
    telescope := T
    typing := H.recursorTypingAt S.generated.ownerIdx hentry }⟩

end VerifyInductive

end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkInductiveTypes.loopType

/-- The proof-relevant core of a dependency-selected scope.  Unlike
`ScopeEmbedding`, this certificate does not retain source declaration names
and domains; equation assembly needs the checked embedding, declaration
shape, and target context, but closes its already-abstracted source terms
directly.  Omitting the source declarations lets the certificate reuse the exact
cached parameter/field targets rather than choosing a second translation. -/
structure FVarCheckingScopeCore (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  declarations : List.Forall₂
    (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), .vlam type))
    scope.fvars scope
  wf : scope.WF env Us.length

def FVarCheckingScopeCore.retargetRuntime
    (H : FVarCheckingScopeCore env Us scope runtime) (h : runtime = runtime') :
    FVarCheckingScopeCore env Us scope runtime' where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := by cases h; exact H.context
  upset := by cases h; exact H.upset
  noBV := H.noBV
  declarations := H.declarations
  wf := H.wf

theorem FVarCheckingScopeCore.scopeWF
    (H : FVarCheckingScopeCore env Us scope runtime) (_henv : env.WF) :
    scope.WF env Us.length := H.wf

theorem FVarCheckingScopeCore.toCtx_length
    (H : FVarCheckingScopeCore env Us scope runtime) :
    scope.toCtx.length = scope.length :=
  VLCtx.toCtx_length_of_forall₂_vlam H.declarations

theorem FVarCheckingScopeCore.fullTargetEq
    (H : FVarCheckingScopeCore env Us scope runtime) (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

private theorem coreNamedDeclarations_fvars
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) xs ys) :
    VLCtx.fvars ys = xs := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    simpa [VLCtx.fvars] using ih

theorem FVarCheckingScopeCore.fvars_take
    (H : FVarCheckingScopeCore env Us scope runtime) (n : Nat) :
    VLCtx.fvars (scope.take n) = scope.fvars.take n :=
  coreNamedDeclarations_fvars (List.forall₂_take H.declarations n)

theorem FVarCheckingScopeCore.abstractPrefix
    (H : FVarCheckingScopeCore env Us scope runtime) (henv : env.WF) (n : Nat)
    (hbase : scope.drop n = baseScope)
    (Htr : TrExprS env Us scope source target) :
    TrExprS env Us
      (abstractForallContext (VLCtx.toCtx (scope.take n)).reverse baseScope)
      (source.abstractList (scope.fvars.take n).reverse) target := by
  let scopePrefix := scope.take n
  let tail := scope.drop n
  have hscope : scopePrefix ++ tail = scope := by
    simp [scopePrefix, tail]
  have Hprefix := List.forall₂_take H.declarations n
  have hprefixFVars : VLCtx.fvars scopePrefix = scope.fvars.take n :=
    coreNamedDeclarations_fvars Hprefix
  have Htr' : TrExprS env Us
      (abstractForallContext [] (scopePrefix ++ tail)) source target := by
    simpa [abstractForallContext, hscope] using Htr
  have hnodup : (scope.fvars.take n).Nodup :=
    (H.scopeWF henv).fvars_nodup.sublist
      (List.take_sublist n scope.fvars)
  have Habstract := TrExprS.abstractFVarLambdaPrefix
    (domains := []) Hprefix hnodup Htr'
  simpa [scopePrefix, tail, hprefixFVars, hbase] using Habstract

def FVarCheckingScopeCore.withIndex
    (H : FVarCheckingScopeCore env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u))
    (htype : env.IsType Us.length scope.toCtx indexType) :
    FVarCheckingScopeCore env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := H.noBV
  declarations := .cons ⟨deps, indexType, rfl⟩ H.declarations
  wf := by
    refine ⟨H.wf, ?_, htype⟩
    rintro _ _ ⟨⟩
    refine ⟨fun hmem => ?_, hdeps⟩
    have hsub : scope.fvars ⊆ runtime.fvars := by
      rw [← H.context.fvars]
      exact H.lift.fvars_sublist.subset
    exact (hnewRuntime.2.1 _ _ rfl).1 (hsub hmem)

def FVarCheckingScopeCore.skipIndex
    (H : FVarCheckingScopeCore env Us scope runtime) (henv : env.WF)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hskip : fv ∉ scope.fvars) :
    FVarCheckingScopeCore env Us scope
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded := (some (fv, deps), .vlam runtimeType) :: H.expanded
  shift := H.shift.skipN 1
  lift := H.lift.skip_fvar (fv, deps) (.vlam runtimeType)
  context := by
    have Htype : env.IsType Us.length H.expanded.toCtx runtimeType :=
      hnewRuntime.2.2.defeqDFC henv.ordered
        (H.context.defeqCtx.symm henv.ordered)
    rcases Htype with ⟨level, Htype⟩
    exact .cons H.context (by
      have hfresh := hnewRuntime.2.1
      simpa [H.context.fvars] using hfresh)
      (VLocalDecl.IsDefEq.refl henv H.context.wf.toCtx
        ⟨level, Htype⟩)
  upset := by
    refine ⟨H.upset, ?_⟩
    intro hmem
    exact False.elim (hskip hmem)
  noBV := H.noBV
  declarations := H.declarations
  wf := H.wf

end checkInductiveTypes.loopType

theorem MLCtxLamPrefix.skipFVarCheckingScopeCore
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF) (Hwf : runtime.WF env Us)
    (Hbase : Nonempty
      (checkInductiveTypes.loopType.FVarCheckingScopeCore env Us
        baseScope (runtime.dropN n H.le).vlctx))
    (hskip : ∀ fv ∈ runtime.fvarRevList n H.le,
      fv ∉ baseScope.fvars) :
    Nonempty (checkInductiveTypes.loopType.FVarCheckingScopeCore env Us
      baseScope runtime.vlctx) := by
  induction H with
  | nil runtime => exact Hbase
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, _hfresh, _Htype, _HtypeType⟩
    have htailSkip : ∀ other ∈ tail.fvarRevList n Hprefix.le,
        other ∉ baseScope.fvars := by
      intro other hother
      exact hskip other (by simp [TypeChecker.MLCtx.fvarRevList, hother])
    rcases ih HtailWF Hbase htailSkip with ⟨Htail⟩
    have hhead : fv ∉ baseScope.fvars :=
      hskip fv (by simp [TypeChecker.MLCtx.fvarRevList])
    exact ⟨Htail.skipIndex henv HruntimeWF hhead⟩

/-- Extend a dependency-selected scope core by the recent prefix of the runtime
context, when that prefix was also opened in a checker context embedded in the
base scope.  Each retained domain is the checker
translation weakened along the embedding, so no runtime translation is
restricted. -/
theorem MLCtxLamPrefix.extendFVarCheckingScopeCoreEmbedded
    (H : MLCtxLamPrefix runtime n domains)
    (henv : env.WF) (Hwf : runtime.WF env Us)
    (Hbase : checkInductiveTypes.loopType.FVarCheckingScopeCore env Us
      baseScope (runtime.dropN n H.le).vlctx)
    (hup : IsFVarUpSet
      (fun fv => fv ∈ runtime.fvarRevList n H.le ++ baseScope.fvars)
      runtime.vlctx)
    {chk : TypeChecker.MLCtx} (hchkWF : chk.WF env Us)
    (hn : n ≤ chk.length) (hagree : MLCtxTopAgree runtime chk n)
    (hbaseEmb : ChkEmbeds env Us.length (chk.dropN n hn).vlctx baseScope) :
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarCheckingScopeCore env Us
          scope runtime.vlctx,
        scope.fvars = runtime.fvarRevList n H.le ++ baseScope.fvars ∧
        scope.drop n = baseScope ∧
        ∃ newDomains : List VExpr,
          newDomains.length = n ∧
          scope.toCtx = newDomains.reverse ++ baseScope.toCtx ∧
          Hscope.shift = Hbase.shift.consN n ∧
          (∀ {body target},
            TrExprS env Us scope body target →
            env.IsType Us.length scope.toCtx target →
            TrExprS env Us baseScope
                (runtime.mkForall n H.le body)
                (VExpr.wrapForalls newDomains target) ∧
              env.IsType Us.length baseScope.toCtx
                (VExpr.wrapForalls newDomains target)) ∧
          ChkEmbeds env Us.length chk.vlctx scope := by
  induction H generalizing chk with
  | nil runtime =>
    exact ⟨baseScope, Hbase,
      by simp [TypeChecker.MLCtx.fvarRevList], rfl, [], rfl, by simp,
      by simp [Lift.consN], by
        intro body target Hbody HbodyType
        simpa [TypeChecker.MLCtx.mkForall, VExpr.wrapForalls] using
          And.intro Hbody HbodyType,
      by simpa using hbaseEmb⟩
  | @cons tail n domains fv name type type' bi Hprefix ih =>
    cases hagree with
    | @vlam _ chkTail _ hagreeTail _ _ _ _ t₂ _ =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
    rcases hchkWF with ⟨hchkTailWF, _hfreshC, Htype₀, Htype₀Type⟩
    have hcurrentFresh : fv ∉ tail.vlctx.fvars :=
      HtailWF.tr.find?_eq_none.1 hfresh
    have htailUp : IsFVarUpSet
        (fun fv' =>
          fv' ∈ tail.fvarRevList n Hprefix.le ++ baseScope.fvars)
        tail.vlctx := by
      apply (IsFVarUpSet.congr HtailWF.tr.wf.fvwf ?_).mp hup.1
      intro fv' hfv'
      constructor
      · intro h
        rcases List.mem_cons.mp h with hcurrent | h
        · exact False.elim (hcurrentFresh (hcurrent ▸ hfv'))
        · exact h
      · exact List.mem_cons_of_mem _
    have hnTail : n ≤ chkTail.length := by simpa using hn
    rcases ih HtailWF Hbase htailUp hchkTailWF hnTail hagreeTail
        (by simpa using hbaseEmb) with
      ⟨tailScope, HtailScope, htailScopeFVars, htailBase,
        tailDomains, htailDomains, htailContext, htailShift,
        HtailReplay, hembTail⟩
    have hdepsFull : ∀ dep ∈ type.fvarsList,
        dep ∈ fv :: tail.fvarRevList n Hprefix.le ++ baseScope.fvars :=
      hup.2 (by simp)
    have hdeps : type.fvarsList ⊆ tailScope.fvars := by
      intro dep hdep
      rw [htailScopeFVars]
      have hselected := hdepsFull dep hdep
      rcases List.mem_cons.mp hselected with hcurrent | hselected
      · exact False.elim
          (hcurrentFresh (hcurrent ▸ Htype.fvarsList hdep))
      · exact hselected
    obtain ⟨narrowType, HnarrowType⟩ := hembTail.trExprS henv Htype₀
    have HnarrowIsType : env.IsType Us.length tailScope.toCtx narrowType :=
      hembTail.isType henv Htype₀ HnarrowType Htype₀Type
    have Hweak : TrExprS env Us HtailScope.expanded type
        (narrowType.lift' HtailScope.shift) := by
      simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
        HtailScope.context.wf
    have HtargetEq := Hweak.uniq henv HtailScope.context Htype
    have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
        type' := HtypeType.defeqDFC henv.ordered
          (HtailScope.context.symm henv.ordered).defeqCtx
    rcases HtargetType with ⟨u, HtargetType⟩
    have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
        (narrowType.lift' HtailScope.shift) type' (.sort u) :=
      HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
    let Hnext := HtailScope.withIndex HruntimeWF hdeps Hdomain HnarrowIsType
    have hfreshScope : fv ∉ tailScope.fvars := by
      intro hmem
      have hsub : tailScope.fvars ⊆ tail.vlctx.fvars := by
        rw [← HtailScope.context.fvars]
        exact HtailScope.lift.fvars_sublist.subset
      exact hcurrentFresh (hsub hmem)
    refine ⟨_, Hnext, ?_, ?_, tailDomains ++ [narrowType], ?_, ?_,
      ?_, ?_, ?_⟩
    · simp [htailScopeFVars, TypeChecker.MLCtx.fvarRevList]
    · simpa using htailBase
    · simp [htailDomains]
    · change narrowType :: tailScope.toCtx = _
      rw [htailContext]
      simp [List.reverse_append]
    · change HtailScope.shift.consN 1 = Hbase.shift.consN (n + 1)
      rw [htailShift]
      simp [Lift.consN]
    · intro body target Hbody HbodyType
      have HdomainType : env.IsType Us.length tailScope.toCtx narrowType :=
        HnarrowIsType
      have W : VLCtx.Abstract tailScope fv (.vlam narrowType) 0 0
          ((some (fv, type.fvarsList), .vlam narrowType) :: tailScope)
          ((none, .vlam narrowType) :: tailScope) := .zero
      have Hbody' : TrExprS env Us
          ((none, .vlam narrowType) :: tailScope)
          (body.abstract1 fv) target := by
        apply TrExprS.abstract W
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarCheckingScopeCore.withIndex] using Hbody
      have HbodyType' : env.IsType Us.length
          (narrowType :: tailScope.toCtx) target := by
        simpa [Hnext,
          checkInductiveTypes.loopType.FVarCheckingScopeCore.withIndex,
          VLCtx.toCtx] using HbodyType
      have Hone : TrExprS env Us tailScope
          (.forallE name type (body.abstract1 fv) bi)
          (.forallE narrowType target) :=
        .forallE HdomainType HbodyType' HnarrowType Hbody'
      have HoneType : env.IsType Us.length tailScope.toCtx
          (.forallE narrowType target) :=
        VEnv.IsType.forallE HdomainType HbodyType'
      have Hclosed := HtailReplay Hone HoneType
      simpa [TypeChecker.MLCtx.mkForall, VExpr.wrapForalls_append,
        VExpr.wrapForalls] using Hclosed
    · exact hembTail.cons henv hfreshScope Htype₀ HnarrowType HnarrowIsType

/-- Recover the selected mutual family's canonical motive telescope in the
exact recursive-call context.  Both the motive binding and telescope lookup
come from the certificate recorded by the minor pass and retained by the rule; the only
context transport follows the literal prior-hypothesis and call-local suffixes
recorded by the executable traversal. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.typedMotiveAppliesTo
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ binding : MotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      Nonempty (MotiveAppliesTo
        F.semantic.current_context stats H.recInfos[selectedOwner]!
        binding F.semantic.generated.exposedType F.semantic.exposedTarget) := by
  let selectedOwner := F.semantic.generated.ownerIdx
  have hrecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  let Hext : RecursorContextExtension A.typing.context
      F.semantic.current_context :=
    F.originExtension.trans F.semantic.recent.contextExtension
  have HexposedType : F.semantic.current_context.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      F.semantic.current_context.mlctx.vlctx.toCtx
      F.semantic.exposedTarget :=
    VEnv.IsType.defeqU_l F.semantic.current_context.checking.tr.wf
      F.semantic.current_context.mlctx_wf.tr.wf.toCtx
      F.semantic.exposed_defeq.symm F.semantic.terminal_type
  exact F.motiveLookup.appliesTo selectedOwner hrecInfo
    F.semantic.current_context Hext F.semantic.exposed_translation
    HexposedType F.semantic.validated

/-- Replay the constructor fields once above the cached parameter scope.
This rule-wide frame is independent of any particular recursive call; later
call-local dependency selection reuses its exact field/parameter identifier order. -/
theorem
    RecursorCheck.RuleAlignment.scopedFieldRuntimeScope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls := A.typing.parameterSuffix.parameterDecls
    ∃ fieldScope,
      ∃ HfieldScope : checkInductiveTypes.loopType.FrontScopeEmbedding
          A.typing.fieldRootContext.venv Us fieldScope
            A.typing.context.mlctx.vlctx,
        fieldScope.fvars =
            A.typing.fieldsRecent.fvars.reverse ++ parameterDecls.fvars ∧
        fieldScope.drop HfieldScope.frontSourceDomains.length =
            parameterDecls ∧
        (∃ fieldDomains,
          fieldDomains.length = A.rule.allArgs.size ∧
          HfieldScope.frontSourceDomains = fieldDomains) ∧
        (0 < A.rule.allArgs.size →
          VLCtx.IsDefEq A.typing.fieldRootContext.venv Us.length
            fieldScope A.typing.context.chk.vlctx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls := A.typing.parameterSuffix.parameterDecls
  let Hparameter := A.typing.parameterSuffix.parameterEmbedding
  rcases A.typing.context.onlyLams.lamPrefix
      A.rule.allArgs.size A.typing.fieldsRecent.size_le with
    ⟨_runtimeFieldDomains, HfieldPrefix⟩
  have hfieldRuntime :
      (A.typing.context.mlctx.dropN A.rule.allArgs.size
        HfieldPrefix.le).vlctx =
        A.typing.fieldRootContext.mlctx.vlctx := by
    have hle : HfieldPrefix.le = A.typing.fieldsRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle, A.typing.fieldsRecent.drop_eq]
  let HfieldBase := Hparameter.retargetRuntime hfieldRuntime.symm
  have HfieldWF : A.typing.context.mlctx.WF
      A.typing.fieldRootContext.venv Us := by
    simpa only [Us, A.typing.fieldsRecent.venv_eq] using
      A.typing.context.mlctx_wf
  have hfieldRev : A.typing.context.mlctx.fvarRevList
      A.rule.allArgs.size HfieldPrefix.le =
        A.typing.fieldsRecent.fvars.reverse := by
    have hle : HfieldPrefix.le = A.typing.fieldsRecent.size_le :=
      Subsingleton.elim _ _
    rw [hle]
    exact A.typing.fieldsRecent.fvarRevList_eq
  have HfieldUp : IsFVarUpSet
      (fun fv => fv ∈ A.typing.context.mlctx.fvarRevList
          A.rule.allArgs.size HfieldPrefix.le ++ parameterDecls.fvars)
      A.typing.context.mlctx.vlctx := by
    apply (IsFVarUpSet.congr HfieldWF.tr.wf.fvwf ?_).mp
      A.typing.fieldParameterUp
    intro fv _
    rw [hfieldRev, A.typing.parameterSuffix.parameterDecls_fvars]
    simp
  obtain ⟨M, hMwf, hchkM, hnM, hagree, hdrop, -⟩ := A.typing.fieldCheck
  have hMwf' : M.WF A.typing.fieldRootContext.venv Us := by
    simpa only [Us, A.typing.fieldsRecent.venv_eq] using hMwf
  have hbaseAlign : VLCtx.IsDefEq A.typing.fieldRootContext.venv Us.length
      parameterDecls (M.dropN A.rule.allArgs.size hnM).vlctx := by
    rw [hdrop]
    exact .refl A.typing.fieldRootContext.checking.tr.wf HfieldBase.wf
  rcases HfieldPrefix.extendFrontScopeEmbeddingAligned
      A.typing.fieldRootContext.checking.tr.wf HfieldWF HfieldBase
        HfieldUp hMwf' hnM hagree hbaseAlign with
    ⟨fieldScope, HfieldScope, hfieldScopeFVars, hfieldBase,
      ⟨fieldDomains, hfieldDomains, hfieldFront⟩, halign⟩
  have hbase : fieldScope.drop HfieldScope.frontSourceDomains.length =
      parameterDecls := by
    simpa [HfieldBase, Hparameter,
      checkInductiveTypes.loopType.FrontScopeEmbedding.retargetRuntime,
      RecursorParameterContextSuffix.parameterEmbedding,
      checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix]
      using hfieldBase
  have hfront : HfieldScope.frontSourceDomains = fieldDomains := by
    simpa [HfieldBase, Hparameter,
      checkInductiveTypes.loopType.FrontScopeEmbedding.retargetRuntime,
      RecursorParameterContextSuffix.parameterEmbedding,
      checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix]
      using hfieldFront
  exact ⟨fieldScope, HfieldScope, by simpa [hfieldRev] using
    hfieldScopeFVars, hbase, ⟨fieldDomains, hfieldDomains, hfront⟩,
    fun hpos => by rw [hchkM hpos]; exact halign⟩

end VerifyInductive

end Lean4Lean
