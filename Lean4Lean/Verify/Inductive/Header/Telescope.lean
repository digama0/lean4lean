import Lean4Lean.Verify.Inductive.Header.CheckingScope

/-!
# The header telescope loop

Verifies `checkInductiveTypes.loopType`, the traversal of one family type's parameter and
index binders in the header phase (section 3.2 of the design notes). The first
header introduces the common parameters and is described by `HeaderTelescope`; a later header
reuses the cached parameters and is described in its own scope, which excludes the indices
left by earlier families (`ScopedHeaderTelescope`, `ReusedParameterScope`). Each header
yields a `HeaderFormation`: its arity, result universe and the definitional agreement of the
source type with the synthesized telescope, together with the concrete source telescope
(`HeaderSourceTelescope`). `HeaderFormations` accumulates them in source order.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive
namespace checkInductiveTypes.loopType

/-- Shape of the CPS-retained runtime context after the first header has fixed
the block-wide parameter telescope.  Header indices form an ambient prefix;
the common parameters remain an exact suffix. -/
structure AmbientParamContext (Hc : ContextWF c) (params : List VExpr)
    (depth : Nat) where
  ambient : List VExpr
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (ambient ++ params.reverse) Hc.mlctx.vlctx.toCtx
  length : ambient.length = depth

/-- The exact cached-parameter suffix represents the common abstract
parameter telescope fixed by the first header.  The ambient prefixes may
differ definitionally, but have the same recorded depth and can be inverted
away from the context conversion. -/
theorem ParameterContextSuffix.paramsDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hambient : AmbientParamContext Hc params depth)
    (hparams : params.length = stats.params.size) :
    VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx := by
  have hcontext : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (Hambient.ambient ++ params.reverse)
      (Hsuffix.ambientDecls.toCtx ++ Hsuffix.parameterDecls.toCtx) := by
    simpa [Hsuffix.context] using Hambient.context
  have hparameterCtx : Hsuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    have hcachedLength : ∀ {ps : List Expr} {decls : VLCtx},
        List.Forall₂ CachedParameterDecl ps decls →
        decls.toCtx.length = ps.length := by
      intro ps decls hcached
      induction hcached with
      | nil => rfl
      | cons h _ ih =>
        rcases h with ⟨fv, deps, type, rfl, rfl⟩
        simp [VLCtx.toCtx, ih]
    simpa using hcachedLength Hsuffix.cached
  have hprefix : Hambient.ambient.length =
      Hsuffix.ambientDecls.toCtx.length := by
    have hlength := hcontext.length_eq
    simp only [List.length_append, List.length_reverse] at hlength
    omega
  exact VEnv.IsDefEqCtx.dropPrefixes hcontext hprefix

/-- Source-side account of the header telescope traversed by `loopType`.
`root` is the source normalized header and `current` is its untraversed
suffix.  The context relation records that stripping type annotations may change a
binder domain without changing the abstract telescope up to definitional
equality. -/
structure HeaderTelescopeCertificate (Hc : ContextWF c)
    (root current : VExpr) (params indices : List VExpr) where
  rebuild : root = VExpr.wrapForalls (params ++ indices) current
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx

theorem HeaderTelescopeCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeCertificate Hc root root [] [] where
  rebuild := by simp [VExpr.wrapForalls]
  context := by simpa using hctx

/-- Type-valued state carried by the executable telescope loop.  It owns the
source parameter and index lists, and synchronizes their lengths with the two
counters maintained by `loopType`. -/
structure HeaderTelescopeLoopCertificate (Hc : ContextWF c)
    (root current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  telescope : HeaderTelescopeCertificate Hc root current params indices
  parameterCount : params.length = i
  indexCount : indices.length = nindices

/-- Definitional, rather than syntactic, header-telescope accumulator.  Its
`header` field relates the independent source header to the telescope
synthesized from every binder exposed by the executable per-binder `whnf`.
This is the state used by the complete loop refinement. -/
structure HeaderTelescope (Hc : ContextWF c)
    (target : VInductiveTypeSkeleton) (current : VExpr)
    (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx
  currentType : Hc.venv.IsType c.lparams.length
    (indices.reverse ++ params.reverse) current
  exprType : VExpr
  header : Hc.venv.IsDefEq c.lparams.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def HeaderTelescope.empty
    {c : AddInductive.Context} {Hc : ContextWF c}
    {target : VInductiveTypeSkeleton} {current exprType : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx)
    (hcurrent : Hc.venv.IsType c.lparams.length [] current)
    (hheader : Hc.venv.IsDefEq c.lparams.length []
      target.type current exprType) :
    HeaderTelescope Hc target current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  context := by simpa using hctx
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

def HeaderTelescope.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescope Hc target
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.UnannotatedDomain dom sourceDom consumedDom)
    (hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀) :
    HeaderTelescope
      (Hc.withCheckedLocalDecl (name := name) (bi := bi)
        hdom.unannotated hdom.isType hdom₀.unannotated hdom₀.isType)
      target body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: H.params.reverse)
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      have hOld : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
          H.params.reverse Hc.mlctx.vlctx.toCtx := by
        simpa [hindices] using H.context
      exact .succ hOld
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (hOld.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv, ContextWF.withCheckedLocalDeclOn_venv,
      ContextWF.withLocalDecl_toCtx, ContextWF.withCheckedLocalDecl_toCtx, ContextWF.withCheckedLocalDeclOn_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [hindices, ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv, ContextWF.withCheckedLocalDeclOn_venv] using htype
  exprType := H.exprType
  header := by
    simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv, ContextWF.withCheckedLocalDeclOn_venv]
      using H.header

def HeaderTelescope.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescope Hc target
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.UnannotatedDomain dom sourceDom consumedDom)
    (hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀) :
    HeaderTelescope
      (Hc.withCheckedLocalDecl (name := name) (bi := bi)
        hdom.unannotated hdom.isType hdom₀.unannotated hdom₀.isType)
      target body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: (H.indices.reverse ++ H.params.reverse))
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv, ContextWF.withCheckedLocalDeclOn_venv,
      ContextWF.withLocalDecl_toCtx, ContextWF.withCheckedLocalDecl_toCtx, ContextWF.withCheckedLocalDeclOn_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [List.reverse_append, ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv, ContextWF.withCheckedLocalDeclOn_venv] using htype
  exprType := H.exprType
  header := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv, ContextWF.withCheckedLocalDeclOn_venv] using H.header

/-- Replace the residual telescope by a definitionally equal normal form and
close that equality over every already discovered binder. -/
noncomputable def HeaderTelescope.normalize
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescope Hc target current i nindices)
    (heq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx current next) :
    HeaderTelescope Hc target next i nindices := by
  have heq' := heq.defeqDFC Hc.checking.tr.wf.ordered
    (H.context.symm Hc.checking.tr.wf.ordered)
  let currentLevel := Classical.choose H.currentType
  have hcurrent := Classical.choose_spec H.currentType
  have heqTyped := heq'.of_l Hc.checking.tr.wf H.context.isType hcurrent
  have heqTyped' : Hc.venv.IsDefEq c.lparams.length
      ((H.params ++ H.indices).reverse ++ []) current next
      (.sort currentLevel) := by
    simpa [List.reverse_append] using heqTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
      (domains := H.params ++ H.indices) (Γ := [])
      (by simpa [List.reverse_append] using H.context.isType)
      heqTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices
    parameterCount := H.parameterCount
    indexCount := H.indexCount
    context := H.context
    currentType := H.currentType.defeqU_l Hc.checking.tr.wf
      H.context.isType heq'
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r Hc.checking.tr.wf (by trivial)
      (by simpa using hwrapped) }

/-- Definitional header synthesis in a scope smaller than the executable
reader context.  Later mutual headers retain indices introduced while
checking earlier family members; those declarations must not become part of
the later header's semantic telescope. -/
structure ScopedHeaderTelescope
    (env : VEnv) (Us : List Name) (target : VInductiveTypeSkeleton)
    (scope : VLCtx) (current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  scopeLength : scope.length = i + nindices
  scopeCtx : scope.toCtx = indices.reverse ++ params.reverse
  scopeWF : scope.WF env Us.length
  currentType : env.IsType Us.length scope.toCtx current
  exprType : VExpr
  header : env.IsDefEq Us.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def ScopedHeaderTelescope.empty
    {exprType : VExpr}
    (_htarget : env.IsType Us.length [] target.type)
    (hcurrent : env.IsType Us.length [] current)
    (hheader : env.IsDefEq Us.length [] target.type current exprType) :
    ScopedHeaderTelescope env Us target [] current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  scopeLength := rfl
  scopeCtx := rfl
  scopeWF := by trivial
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

/-- Replace the current residual by a definitionally equal forall over the
next cached common-parameter type, then move that binder into the header's
own scope. -/
noncomputable def ScopedHeaderTelescope.withParameter
    (henv : env.WF)
    (H : ScopedHeaderTelescope env Us target scope
      (.forallE sourceDom sourceBody) i 0)
    (hindices : H.indices = [])
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE paramType next)) :
    ScopedHeaderTelescope env Us target
      ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0 := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE paramType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hparamsCtx : OnCtx H.params.reverse (env.IsType Us.length) := by
    simpa [hindices, H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length (H.params.reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE paramType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [hindices, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params) (Γ := []) (by simpa using hparamsCtx)
      hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params ++ [paramType]
    indices := []
    parameterCount := by simp [H.parameterCount]
    indexCount := rfl
    scopeLength := by simp [H.scopeLength]
    scopeCtx := by simp [VLCtx.toCtx, H.scopeCtx, hindices]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append]
        using hwrapped }

/-- Move a definitionally equal residual forall into the header's own index
telescope. -/
noncomputable def ScopedHeaderTelescope.withIndex
    (henv : env.WF)
    (H : ScopedHeaderTelescope env Us target scope
      (.forallE sourceDom sourceBody) i nindices)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE indexType next)) :
    ScopedHeaderTelescope env Us target
      ((some (fv, deps), .vlam indexType) :: scope)
      next i (nindices + 1) := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE indexType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hdomainsCtx : OnCtx (H.params ++ H.indices).reverse
      (env.IsType Us.length) := by
    simpa [List.reverse_append, ← H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length
      ((H.params ++ H.indices).reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE indexType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [List.reverse_append, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params ++ H.indices) (Γ := [])
      (by simpa using hdomainsCtx) hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices ++ [indexType]
    parameterCount := H.parameterCount
    indexCount := by simp [H.indexCount]
    scopeLength := by simp [H.scopeLength, Nat.add_assoc]
    scopeCtx := by
      simp [VLCtx.toCtx, H.scopeCtx, List.reverse_append]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
        List.append_assoc] using hwrapped }

/-- Compare the next domain of a scoped header telescope with the next domain of
another certified presentation of the same source header. -/
theorem ScopedHeaderTelescope.nextDomainDefEq
    (henv : env.WF)
    (H : ScopedHeaderTelescope env Us target scope
      (.forallE currentDomain currentBody) i nindices)
    (hindices : H.indices = [])
    (hlen : H.params.length = expectedPrefix.length)
    (htarget : env.IsDefEq Us.length [] target.type
      (VExpr.wrapForalls expectedPrefix
        (.forallE expectedDomain expectedBody)) targetType) :
    ∃ u, env.IsDefEq Us.length H.params.reverse
      currentDomain expectedDomain (.sort u) := by
  have hleftTarget : env.IsDefEqU Us.length []
      (VExpr.wrapForalls H.params (.forallE currentDomain currentBody))
      target.type := ⟨_, by simpa [hindices] using H.header.symm⟩
  have htargetRight : env.IsDefEqU Us.length [] target.type
      (VExpr.wrapForalls expectedPrefix
        (.forallE expectedDomain expectedBody)) := ⟨_, htarget⟩
  have hboth := hleftTarget.trans henv (by trivial) htargetRight
  simpa using VEnv.IsDefEqU.wrapForalls_next henv (by trivial)
    hlen hboth

/-- Build the semantic parameter transition from the syntax translation in
the header's own scope and the executable comparison and normalization
results. -/
theorem ScopedHeaderTelescope.consumeParameter
    (henv : env.WF)
    (H : ScopedHeaderTelescope env Us target scope current i 0)
    (hindices : H.indices = [])
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' paramType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam paramType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (paramType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      Nonempty (ScopedHeaderTelescope env Us target
        ((some (fv, deps), .vlam paramType) :: scope)
        normalized' (i + 1) 0) := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE paramType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      ⟨H.withParameter henv hindices hscopeWF hstep⟩⟩

/-- Build the semantic index transition from the syntax translation in
the header's own scope and the executable comparison and normalization
results. -/
theorem ScopedHeaderTelescope.consumeIndex
    (henv : env.WF)
    (H : ScopedHeaderTelescope env Us target scope current i
      nindices)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' indexType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam indexType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (indexType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      ∃ H' : ScopedHeaderTelescope env Us target
        ((some (fv, deps), .vlam indexType) :: scope)
        normalized' i (nindices + 1),
        H'.params = H.params ∧ H'.indices = H.indices ++ [indexType] := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ indexType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam indexType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE indexType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      H.withIndex henv hscopeWF hstep, rfl, rfl⟩

theorem ScopedHeaderTelescope.typeShapeWithParams
    {decl : VInductDecl} {target : VInductiveType}
    {commonParams : List VExpr}
    (H : ScopedHeaderTelescope env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hparams : decl.ParamsDefEq env commonParams H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env commonParams target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := commonParams) (ownParams := H.params)
    (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake hparams hlevel hsort

theorem HeaderTelescope.typeShapeWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params : List VExpr}
    (H : HeaderTelescope Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hparams : decl.ParamsDefEq Hc.venv params H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    huvars H.context
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    hparams hlevel hsort

theorem HeaderTelescope.typeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    (H : HeaderTelescope Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params target := by
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using H.context.isType
  exact H.typeShapeWithParams huvars
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

/-- Construct the two semantic header fields from the successful executable
tail.  Unlike `typeShape`, this theorem does not require either field to have
been chosen before the traversal: the index counter and translated sort are
used to construct the target itself. -/
theorem HeaderTelescope.formationTypeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveTypeSkeleton}
    (H : HeaderTelescope Hc target current
      decl.nparams nindices)
    (huvars : c.lparams.length = decl.uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params
      (target.toVInductiveType nindices resultLevel) := by
  apply H.typeShape (target := target.toVInductiveType nindices resultLevel)
    huvars
  · intro resultLevel' hofLevel'
    rw [hofLevel] at hofLevel'
    cases hofLevel'
    rfl
  · exact hsort

/-- How the normalized semantic parameter/index telescope sits in the
executable header context, as selected by a source-aware scope.  The first header occupies the full context; later mutual headers
can skip indices left by earlier families. -/
inductive HeaderSourceScopeAlignment (env : VEnv) (Us : List Name)
    (sourceScope runtime : VLCtx) (ownParams indices : List VExpr) : Type
  | full
      (sourceFVars : sourceScope.fvars = runtime.fvars)
      (semanticContext : VEnv.IsDefEqCtx env Us.length []
        (indices.reverse ++ ownParams.reverse) runtime.toCtx) :
      HeaderSourceScopeAlignment env Us sourceScope runtime ownParams indices
  | embedded
      (semanticScope : VLCtx)
      (sourceFVars : sourceScope.fvars = semanticScope.fvars)
      (semantic : FrontScopeEmbedding env Us semanticScope runtime)
      (semanticContext : semanticScope.toCtx =
        indices.reverse ++ ownParams.reverse) :
      HeaderSourceScopeAlignment env Us sourceScope runtime ownParams indices

/-- Concrete source telescope retained only once the header has been
checked.  Keeping this separate from `ScopedHeaderTelescope` is
essential: constructor replay universe-instantiates that generic certificate
with abstract levels for which there need not be corresponding Lean source
syntax. -/
structure HeaderSourceTelescope (env : VEnv) (Us : List Name)
    (commonParams : List VExpr) (nparams nindices : Nat) : Type where
  runtime : VLCtx
  sourceScope : VLCtx
  source : ScopeEmbedding env Us sourceScope runtime
  sourceLctx : LocalContext
  sourceClosure : ∀ body,
    source.sourceTelescope.closeSource body =
      sourceLctx.mkForall
        (sourceScope.fvars.reverse.map Expr.fvar).toArray body
  abstractScope : VLCtx
  abstractSources : SourceTelescope env Us abstractScope
  abstractScopeWF : abstractScope.WF env Us.length
  ownParams : List VExpr
  indices : List VExpr
  parameterCount : ownParams.length = nparams
  indexCount : indices.length = nindices
  sourceLength : sourceScope.length = nparams + nindices
  parameters : VEnv.IsDefEqCtx env Us.length []
    commonParams.reverse ownParams.reverse
  abstractContext : VEnv.IsDefEqCtx env Us.length []
    (indices.reverse ++ ownParams.reverse) abstractScope.toCtx
  alignment : HeaderSourceScopeAlignment env Us sourceScope runtime
    ownParams indices

def HeaderSourceScopeAlignment.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : HeaderSourceScopeAlignment env Us sourceScope runtime
      ownParams indices) :
    HeaderSourceScopeAlignment env' Us sourceScope runtime
      ownParams indices := by
  cases H with
  | full sourceFVars semanticContext =>
    exact .full sourceFVars (semanticContext.mono henv)
  | embedded semanticScope sourceFVars semantic semanticContext =>
    exact .embedded semanticScope sourceFVars (semantic.mono henv)
      semanticContext

def HeaderSourceTelescope.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : HeaderSourceTelescope env Us commonParams
      nparams nindices) :
    HeaderSourceTelescope env' Us commonParams
      nparams nindices where
  runtime := H.runtime
  sourceScope := H.sourceScope
  source := H.source.mono henv
  sourceLctx := H.sourceLctx
  sourceClosure := by
    intro body
    simpa [ScopeEmbedding.mono] using H.sourceClosure body
  abstractScope := H.abstractScope
  abstractSources := H.abstractSources.mono henv
  abstractScopeWF := H.abstractScopeWF.mono henv
  ownParams := H.ownParams
  indices := H.indices
  parameterCount := H.parameterCount
  indexCount := H.indexCount
  sourceLength := H.sourceLength
  parameters := H.parameters.mono henv
  abstractContext := H.abstractContext.mono henv
  alignment := H.alignment.mono henv

/-- Persistent result of checking one metadata-free source header.  The final
mutual declaration need not exist yet; only its two block-wide counters are
relevant to `TypeShape`.  This lets the outer traversal accumulate checked
headers and build the declaration with `withMetadata` after every family
member has supplied its metadata. -/
structure HeaderFormation (env : VEnv) (Us : List Name)
    (uvars nparams : Nat)
    (params : List VExpr) (source : VInductiveTypeSkeleton)
    (numIndices : Nat) (resultLevel : VLevel) : Prop where
  parameterCount : params.length = nparams
  levelCount : Us.length = uvars
  normalizedSource : Nonempty
    (HeaderSourceTelescope env Us params nparams numIndices)
  /-- The retained concrete source telescope and the semantic header shape
  are the same replay, not two unrelated existential witnesses.  This is
  needed after nested lowering: the literal source index telescope must be
  paired with the exact abstract index domains used to type the installed
  family. -/
  normalizedShape : ∃ sourceTelescope :
      HeaderSourceTelescope env Us params nparams numIndices,
    ∃ residual exprType,
      env.IsDefEq Us.length []
        (source.toVInductiveType numIndices resultLevel).type
        (VExpr.wrapForalls
          (sourceTelescope.ownParams ++ sourceTelescope.indices) residual)
        exprType ∧
      env.IsDefEq Us.length
        (sourceTelescope.indices.reverse ++
          sourceTelescope.ownParams.reverse)
        residual (.sort resultLevel) (.sort (.succ resultLevel))
  typeShape : ∀ decl : VInductDecl,
    decl.uvars = uvars → decl.nparams = nparams →
    decl.TypeShape env params
      (source.toVInductiveType numIndices resultLevel)

theorem ScopedHeaderTelescope.headerFormationWithParams
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : ScopedHeaderTelescope env Us source scope current
      nparams nindices)
    (henv : env.WF)
    (Hruntime : FrontScopeEmbedding env Us scope runtime)
    (Hsource : ScopeEmbedding env Us sourceScope runtime)
    (hsourceFVars : sourceScope.fvars = scope.fvars)
    (sourceLctx : LocalContext)
    (hsourceClosure : ∀ body,
      Hsource.sourceTelescope.closeSource body =
        sourceLctx.mkForall
          (sourceScope.fvars.reverse.map Expr.fvar).toArray body)
    (huvars : Us.length = uvars)
    (hparams : VEnv.IsDefEqCtx env uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel Us level = some resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    HeaderFormation env Us uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  levelCount := huvars
  normalizedSource := by
    exact ⟨{
      runtime := runtime
      sourceScope := sourceScope
      source := Hsource
      sourceLctx := sourceLctx
      sourceClosure := hsourceClosure
      abstractScope := scope
      abstractSources := Hruntime.sourceTelescope
      abstractScopeWF := Hruntime.scopeWF henv
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = scope.fvars.length := congrArg List.length hsourceFVars
          _ = scope.length := VLCtx.fvars_length_of_noBV Hruntime.noBV
          _ = nparams + nindices := H.scopeLength
      parameters := by simpa [huvars] using hparams
      abstractContext := by
        simpa [H.scopeCtx] using
          (VEnv.IsDefEqCtx.refl H.scopeWF.toCtx)
      alignment := .embedded scope hsourceFVars Hruntime H.scopeCtx }⟩
  normalizedShape := by
    let sourceTelescope : HeaderSourceTelescope env Us
        commonParams nparams nindices := {
      runtime := runtime
      sourceScope := sourceScope
      source := Hsource
      sourceLctx := sourceLctx
      sourceClosure := hsourceClosure
      abstractScope := scope
      abstractSources := Hruntime.sourceTelescope
      abstractScopeWF := Hruntime.scopeWF henv
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = scope.fvars.length := congrArg List.length hsourceFVars
          _ = scope.length := VLCtx.fvars_length_of_noBV Hruntime.noBV
          _ = nparams + nindices := H.scopeLength
      parameters := by simpa [huvars] using hparams
      abstractContext := by
        simpa [H.scopeCtx] using
          (VEnv.IsDefEqCtx.refl H.scopeWF.toCtx)
      alignment := .embedded scope hsourceFVars Hruntime H.scopeCtx }
    rcases TrExpr.sort_result henv H.scopeWF.toCtx hsort with
      ⟨resultLevel', hlevel', Hresult⟩
    have hresultLevel : resultLevel' = resultLevel := by
      rw [hofLevel] at hlevel'
      exact (Option.some.inj hlevel').symm
    subst resultLevel'
    exact ⟨sourceTelescope, current, H.exprType, by
      simpa [sourceTelescope, VInductiveTypeSkeleton.toVInductiveType] using
        H.header, by
      simpa [sourceTelescope, H.scopeCtx] using Hresult⟩
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : Us.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq env commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      henv huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

theorem HeaderTelescope.headerFormation
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton}
    (H : HeaderTelescope Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    HeaderFormation Hc.venv c.lparams uvars nparams H.params source
      nindices resultLevel where
  parameterCount := H.parameterCount
  levelCount := huvars
  normalizedSource := by
    have hup := IsFVarUpSet.suffixFVars Hc.mlctx.vlctx ([] : VLCtx)
      (by simpa using Hc.mlctx_wf.tr.wf)
    rcases MLCtxOnlyLams.fullSourceScope Hc.onlyLams
        Hc.checking.tr.wf Hc.mlctx_wf with
      ⟨sourceScope, Hsource, hsourceFVars, hsourceClosure⟩
    have hfilter : Hc.mlctx.vlctx.fvars.filter
        (· ∈ Hc.mlctx.vlctx.fvars) = Hc.mlctx.vlctx.fvars :=
      List.filter_mem_eq_of_sublist_nodup (.refl _)
        Hc.mlctx_wf.tr.wf.fvars_nodup
    exact ⟨{
      runtime := Hc.mlctx.vlctx
      sourceScope := sourceScope
      source := Hsource
      sourceLctx := Hc.mlctx.lctx
      sourceClosure := hsourceClosure
      abstractScope := Hc.mlctx.vlctx
      abstractSources := MLCtxOnlyLams.sources Hc.onlyLams Hc.mlctx_wf
      abstractScopeWF := Hc.mlctx_wf.tr.wf
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = Hc.mlctx.vlctx.fvars.length :=
            congrArg List.length (hsourceFVars.trans hfilter)
          _ = Hc.mlctx.length := Hc.onlyLams.fvars_length
          _ = Hc.mlctx.vlctx.toCtx.length :=
            Hc.onlyLams.toCtx_length.symm
          _ = (H.indices.reverse ++ H.params.reverse).length :=
            H.context.length_eq.symm
          _ = nparams + nindices := by
            simp [H.parameterCount, H.indexCount, Nat.add_comm]
      parameters := .refl (OnCtx.of_append H.context.isType)
      abstractContext := H.context
      alignment := .full (hsourceFVars.trans hfilter) H.context }⟩
  normalizedShape := by
    have hup := IsFVarUpSet.suffixFVars Hc.mlctx.vlctx ([] : VLCtx)
      (by simpa using Hc.mlctx_wf.tr.wf)
    rcases MLCtxOnlyLams.fullSourceScope Hc.onlyLams
        Hc.checking.tr.wf Hc.mlctx_wf with
      ⟨sourceScope, Hsource, hsourceFVars, hsourceClosure⟩
    have hfilter : Hc.mlctx.vlctx.fvars.filter
        (· ∈ Hc.mlctx.vlctx.fvars) = Hc.mlctx.vlctx.fvars :=
      List.filter_mem_eq_of_sublist_nodup (.refl _)
        Hc.mlctx_wf.tr.wf.fvars_nodup
    let sourceTelescope : HeaderSourceTelescope Hc.venv c.lparams
        H.params nparams nindices := {
      runtime := Hc.mlctx.vlctx
      sourceScope := sourceScope
      source := Hsource
      sourceLctx := Hc.mlctx.lctx
      sourceClosure := hsourceClosure
      abstractScope := Hc.mlctx.vlctx
      abstractSources := MLCtxOnlyLams.sources Hc.onlyLams Hc.mlctx_wf
      abstractScopeWF := Hc.mlctx_wf.tr.wf
      ownParams := H.params
      indices := H.indices
      parameterCount := H.parameterCount
      indexCount := H.indexCount
      sourceLength := by
        calc
          sourceScope.length = sourceScope.fvars.length :=
            Hsource.fvars_length.symm
          _ = Hc.mlctx.vlctx.fvars.length :=
            congrArg List.length (hsourceFVars.trans hfilter)
          _ = Hc.mlctx.length := Hc.onlyLams.fvars_length
          _ = Hc.mlctx.vlctx.toCtx.length :=
            Hc.onlyLams.toCtx_length.symm
          _ = (H.indices.reverse ++ H.params.reverse).length :=
            H.context.length_eq.symm
          _ = nparams + nindices := by
            simp [H.parameterCount, H.indexCount, Nat.add_comm]
      parameters := .refl (OnCtx.of_append H.context.isType)
      abstractContext := H.context
      alignment := .full (hsourceFVars.trans hfilter) H.context }
    rcases TrExpr.sort_result Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsort with ⟨resultLevel', hlevel', Hresult⟩
    have hresultLevel : resultLevel' = resultLevel := by
      rw [hofLevel] at hlevel'
      exact (Option.some.inj hlevel').symm
    subst resultLevel'
    exact ⟨sourceTelescope, current, H.exprType, by
      simpa [sourceTelescope, VInductiveTypeSkeleton.toVInductiveType] using
        H.header, by
      simpa [sourceTelescope] using Hresult.defeqDFC Hc.checking.tr.wf.ordered
        (H.context.symm Hc.checking.tr.wf.ordered)⟩
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    subst nparams
    apply H.formationTypeShape (decl := decl)
    · exact huvars'
    · exact hofLevel
    · exact hsort

structure HeaderFormationAt (env : VEnv) (Us : List Name)
    (uvars nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : VInductiveTypeSkeleton) (data : Nat × VLevel) : Prop where
  header : HeaderFormation env Us uvars nparams params source data.1 data.2
  commonLevel : data.2 ≈ commonLevel

/-- Prefix of the metadata list built by the outer mutual-header traversal.
`Forall₂` fixes both ordering and cardinality, so `withMetadata` cannot
associate a checked arity or universe with the wrong family member. -/
structure HeaderFormations (env : VEnv) (Us : List Name)
    (skeleton : VInductDeclSkeleton) (params : List VExpr)
    (commonLevel : VLevel) (metadata : List (Nat × VLevel))
    (done : Nat) : Prop where
  parameterCount : params.length = skeleton.nparams
  covered : done ≤ skeleton.types.length
  checked : List.Forall₂
    (HeaderFormationAt env Us skeleton.uvars skeleton.nparams
      params commonLevel)
    (skeleton.types.take done) metadata

/-- Every position of a checked header prefix retains the concrete source
telescope selected while checking that family. -/
theorem HeaderFormations.normalizedSourceAt
    (H : HeaderFormations env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (i : Nat) (hi : i < skeleton.types.length)
    (hmetadata : i < metadata.length) :
    Nonempty (HeaderSourceTelescope env Us params
      skeleton.nparams metadata[i].1) := by
  have Hchecked := List.forall₂_getElem H.checked i
    (by simpa using hi) hmetadata
  exact Hchecked.header.normalizedSource

/-- After `withMetadata`, the retained source telescope is indexed by
the corresponding family in the resulting declaration. -/
theorem HeaderFormations.normalizedSourceAtChecked
    (H : HeaderFormations env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.withMetadata metadata = some decl)
    (i : Nat) (hi : i < decl.types.length) :
    Nonempty (HeaderSourceTelescope env Us params decl.nparams
      decl.types[i].numIndices) := by
  have hfields := VInductDeclSkeleton.withMetadata_fields Hmaterialize
  have hskeleton : i < skeleton.types.length := by omega
  have hmetadata : i < metadata.length := by
    rw [VInductDeclSkeleton.withMetadata_length Hmaterialize]
    exact hskeleton
  have Hsource := H.normalizedSourceAt i hskeleton hmetadata
  rcases VInductDeclSkeleton.withMetadata_typeAt Hmaterialize hskeleton with
    ⟨data, hdata, htarget⟩
  have hdataEq : data = metadata[i] := by
    rw [List.getElem?_eq_getElem hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have htargetEq : decl.types[i] = skeleton.types[i].toVInductiveType
      metadata[i].1 metadata[i].2 := by
    rw [List.getElem?_eq_getElem hi] at htarget
    exact Option.some.inj htarget
  have hindices : decl.types[i].numIndices = metadata[i].1 := by
    rw [htargetEq]
    simp [VInductiveTypeSkeleton.toVInductiveType]
  simpa [hfields.2.1, hindices] using Hsource

/-- The family built by `withMetadata` retains the joint source and semantic
header telescope used by the checker.  In particular, the concrete source index telescope and
the abstract index domains in the family typing are selected by one header
replay, rather than by unrelated existential `TypeShape` proofs. -/
theorem HeaderFormations.normalizedShapeAtChecked
    (H : HeaderFormations env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.withMetadata metadata = some decl)
    (i : Nat) (hi : i < decl.types.length) :
    ∃ sourceTelescope : HeaderSourceTelescope env Us params
        decl.nparams decl.types[i].numIndices,
      ∃ residual exprType,
        env.IsDefEq Us.length [] decl.types[i].type
          (VExpr.wrapForalls
            (sourceTelescope.ownParams ++ sourceTelescope.indices) residual)
          exprType ∧
        env.IsDefEq Us.length
          (sourceTelescope.indices.reverse ++
            sourceTelescope.ownParams.reverse)
          residual (.sort decl.types[i].resultLevel)
            (.sort (.succ decl.types[i].resultLevel)) := by
  have hfields := VInductDeclSkeleton.withMetadata_fields Hmaterialize
  have hskeleton : i < skeleton.types.length := by omega
  have hmetadata : i < metadata.length := by
    rw [VInductDeclSkeleton.withMetadata_length Hmaterialize]
    exact hskeleton
  have Hchecked := List.forall₂_getElem H.checked i
    (by simpa using hskeleton) hmetadata
  rcases VInductDeclSkeleton.withMetadata_typeAt Hmaterialize hskeleton with
    ⟨data, hdata, htarget⟩
  have hdataEq : data = metadata[i] := by
    rw [List.getElem?_eq_getElem hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have htargetEq : decl.types[i] = skeleton.types[i].toVInductiveType
      metadata[i].1 metadata[i].2 := by
    rw [List.getElem?_eq_getElem hi] at htarget
    exact Option.some.inj htarget
  have Hshape := Hchecked.header.normalizedShape
  rw [hfields.2.1]
  rw [htargetEq]
  simpa [VInductiveTypeSkeleton.toVInductiveType] using Hshape

/-- Once every header has been visited, `withMetadata` turns the
metadata-prefix invariant into the public formation header certificate. -/
def HeaderFormations.complete
    (H : HeaderFormations env Us skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.withMetadata metadata = some decl) :
    HeaderCertificate env decl := by
  have hfields := VInductDeclSkeleton.withMetadata_fields Hmaterialize
  have hcheckedLength :
      (skeleton.types.take skeleton.types.length).length = metadata.length :=
    List.Forall₂.length_eq H.checked
  have hmetadata : metadata.length = skeleton.types.length := by
    simpa using hcheckedLength.symm
  have checkedAt : ∀ i (hi : i < skeleton.types.length),
      HeaderFormationAt env Us skeleton.uvars skeleton.nparams
        params commonLevel skeleton.types[i] metadata[i] := by
    intro i hi
    simpa using List.forall₂_getElem H.checked i
      (by simpa using hi) (by simpa [hmetadata] using hi)
  have materializedAt : ∀ i (hi : i < skeleton.types.length),
      decl.types[i]'(by omega) =
        skeleton.types[i].toVInductiveType metadata[i].1 metadata[i].2 := by
    intro i hi
    rcases VInductDeclSkeleton.withMetadata_typeAt Hmaterialize hi with
      ⟨data, hdata, htarget⟩
    have hmetadataGet : metadata[i]? = some metadata[i] := by
      simp [hmetadata, hi]
    have hdataEq : data = metadata[i] := by
      rw [hmetadataGet] at hdata
      cases hdata
      rfl
    subst data
    rw [List.getElem?_eq_getElem (by omega)] at htarget
    exact Option.some.inj htarget
  refine {
    params := params
    resultLevel := commonLevel
    commonLevels := ?_
    typeShapes := ?_ }
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).commonLevel
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).header.typeShape decl
      hfields.1 hfields.2.1

def HeaderTelescopeLoopCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeLoopCertificate Hc root root 0 0 where
  params := []
  indices := []
  telescope := .empty hctx
  parameterCount := rfl
  indexCount := rfl

def AmbientParamContext.ofFirstDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := hctx
  length := by simp

def AmbientParamContext.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : AmbientParamContext Hc params depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx ty ty₀)
    (hty₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx ty₀)
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    AmbientParamContext
      (Hc.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀)
      params (depth + 1) where
  ambient := sourceTy :: H.ambient
  context := by
    rcases hsource with ⟨u, hsource⟩
    change VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceTy :: (H.ambient ++ params.reverse))
      (ty' :: Hc.mlctx.vlctx.toCtx)
    exact .succ H.context
      (hsource.defeqDFC Hc.checking.tr.wf.ordered
        (H.context.symm Hc.checking.tr.wf.ordered))
  length := by simp [H.length]

theorem ParameterCachePrefix.empty
    (hparams : stats.params = #[]) :
    ParameterCachePrefix env Us Δ stats 0 depth := by
  refine ⟨?_, ?_⟩
  · simp [hparams]
  · simp [hparams]

def ParameterContextSuffix.empty
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (hparams : stats.params = #[]) :
    ParameterContextSuffix Hc stats 0 where
  ambientDecls := []
  parameterDecls := []
  context := by simpa using hctx
  prefixLength := rfl
  cached := by simp [hparams]
  suffixParams := by simp [hparams]
  sources := .nil

/-- The first-header parameter branch extends the cached suffix itself.  The
empty-prefix premise records that parameters are all introduced before any
index binder. -/
def ParameterContextSuffix.push
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats 0)
    (hprefix : H.ambientDecls = [])
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx ty ty₀)
    (hty₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx ty₀) :
    ParameterContextSuffix
      (Hc.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀)
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      0 := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := []
    parameterDecls := entry :: H.parameterDecls
    context := ?_
    prefixLength := rfl
    cached := ?_
    suffixParams := ?_
    sources := ?_ }
  · have hcontext := H.context
    rw [hprefix] at hcontext
    change entry :: Hc.mlctx.vlctx = [] ++ entry :: H.parameterDecls
    simp only [List.nil_append]
    simpa using congrArg (entry :: ·) hcontext
  · simp only [Array.toList_push, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    exact .cons ⟨⟨c.ngen.curr⟩, ty.fvarsList, ty', rfl, rfl⟩
      H.cached
  · let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀
    let W : VLCtx.FVLift H.parameterDecls
        (entry :: H.parameterDecls) 0 1 0 :=
      .skip_fvar _ _ .refl
    have hscope : Hc.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    have hnarrowWF : VLCtx.WF Hc'.venv c.lparams.length
        (entry :: H.parameterDecls) := by
      change VLCtx.WF Hc.venv c.lparams.length
        (entry :: H.parameterDecls)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hscope] using Hc.mlctx_wf.tr.wf
      · intro fv deps heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨by simpa [hscope] using Hc.current_not_mem,
          by simpa [hscope] using htr.fvarsList⟩
      · change Hc.venv.IsType c.lparams.length
          H.parameterDecls.toCtx ty'
        simpa [hscope] using hty
    have hold : List.Forall₂
        (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
        stats.params.toList
        ((cachedParamVars stats.params.size 0).map
          fun e => e.liftN 1 0) := by
      have weakAll : ∀ {as bs},
          List.Forall₂
              (TrExprS Hc.venv c.lparams H.parameterDecls) as bs →
            List.Forall₂
              (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
              as (bs.map fun e => e.liftN 1 0) := by
        intro as bs hp
        induction hp with
        | nil => exact .nil
        | cons h _ ih =>
          exact .cons
            (h.weakFV Hc.checking.tr.wf.ordered W hnarrowWF) ih
      exact weakAll H.suffixParams
    have hnew : TrExprS Hc'.venv c.lparams
        (entry :: H.parameterDecls)
        (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
      apply TrExprS.fvar (A := ty'.lift)
      simp [entry, VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type]
    simpa [Array.toList_push, cachedParamVars_succ] using
      List.Forall₂.append' hold
        (.cons hnew .nil)
  · have hscope : Hc.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    change SourceTelescope Hc.venv c.lparams
      (entry :: H.parameterDecls)
    exact .cons H.sources name bi ty (by simpa [hscope] using htr)

/-- Index binders extend only the ambient prefix and preserve the exact
cached-parameter suffix. -/
def ParameterContextSuffix.withIndex
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx ty ty₀)
    (hty₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx ty₀) :
    ParameterContextSuffix
      (Hc.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀)
      stats (depth + 1) := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := ?_
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    suffixParams := H.suffixParams
    sources := H.sources }
  change entry :: Hc.mlctx.vlctx =
    (entry :: H.ambientDecls) ++ H.parameterDecls
  simp only [List.cons_append]
  rw [H.context]

theorem ParameterContextSuffix.parameterDecls_length
    (H : ParameterContextSuffix Hc stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := List.Forall₂.length_eq
    H.cached
  simpa using hlength.symm

/-- Locate executable parameter `i` in the reverse-ordered local-context
suffix. -/
theorem ParameterContextSuffix.parameterAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := by
    exact hj
  have hcached := List.forall₂_getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change CachedParameterDecl stats.params[stats.params.size - 1 - j]
    H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

/-- Split the cached-parameter suffix at executable array index `i`.  Entries
in `newer` are precisely the cached declarations introduced after parameter
`i`; `older` contains those introduced before it. -/
theorem ParameterContextSuffix.splitAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      CachedParameterDecl stats.params[i] entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

/-- Expose the exact `FVLift` that removes the ambient declarations and the
cached parameters newer than executable parameter `i`, leaving that
parameter as the head of the retained suffix. -/
theorem ParameterContextSuffix.fvLiftAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      Hc.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        Hc.mlctx.vlctx
        0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : Hc.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older)
      hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, rfl,
    hcontext, hparam, hlift⟩

theorem _root_.Lean4Lean.TypeChecker.MLCtx.fvarList_eq (m : TypeChecker.MLCtx) :
    m.fvarList = m.vlctx.fvars.reverse := by
  induction m with
  | nil => rfl
  | vlam id _ _ _ _ c ih =>
    simp [TypeChecker.MLCtx.fvarList, ih, TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some]
  | vlet id _ _ _ _ _ c ih =>
    simp [TypeChecker.MLCtx.fvarList, ih, TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some]

theorem CachedParameterDecl.forall₂_fvars
    (H : List.Forall₂ CachedParameterDecl ps decls) :
    VLCtx.fvars decls = ps.map (·.fvarId!) := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    obtain ⟨fv, deps, ty, rfl, rfl⟩ := h
    simp [VLCtx.fvars_cons_some, ih, Expr.fvarId!]

theorem CachedParameterDecl.forall₂_drop :
    ∀ (n : Nat) {ps : List Expr} {decls : VLCtx},
      List.Forall₂ CachedParameterDecl ps decls →
      List.Forall₂ CachedParameterDecl (ps.drop n) (decls.drop n)
  | 0, _, _, H => by simpa using H
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ H => by simpa using CachedParameterDecl.forall₂_drop n H

theorem ParameterContextSuffix.mlctx_length
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    Hc.mlctx.length = depth + stats.params.size := by
  rw [← TypeChecker.MLCtx.vlctx_length, H.context, List.length_append,
    H.prefixLength, H.parameterDecls_length]

/-- The first `k` parameters are the `k` oldest declarations of the main
context: the bottom of the context that drops all but them. -/
theorem ParameterContextSuffix.bottom
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) (k : Nat)
    (hk : k ≤ stats.params.size) :
    (Hc.mlctx.dropN (depth + (stats.params.size - k))
        (by rw [H.mlctx_length]; omega)).vlctx =
      H.parameterDecls.drop (stats.params.size - k) ∧
    paramCheckFVars stats k =
      (Hc.mlctx.dropN (depth + (stats.params.size - k))
        (by rw [H.mlctx_length]; omega)).fvarList := by
  have hvl : (Hc.mlctx.dropN (depth + (stats.params.size - k))
      (by rw [H.mlctx_length]; omega)).vlctx =
      H.parameterDecls.drop (stats.params.size - k) := by
    rw [Hc.onlyLams.vlctx_dropN, H.context, List.drop_append, H.prefixLength]
    rw [List.drop_eq_nil_of_le (by rw [H.prefixLength]; omega)]
    simp
  refine ⟨hvl, ?_⟩
  rw [TypeChecker.MLCtx.fvarList_eq, hvl]
  have hcached := H.cached
  have hdrop : List.Forall₂ CachedParameterDecl
      (stats.params.toList.reverse.drop (stats.params.size - k))
      (H.parameterDecls.drop (stats.params.size - k)) :=
    CachedParameterDecl.forall₂_drop _ hcached
  rw [CachedParameterDecl.forall₂_fvars hdrop, ← List.map_reverse]
  unfold paramCheckFVars
  congr 1
  have hlen : stats.params.toList.length = stats.params.size := by simp
  rw [List.drop_reverse]
  simp only [List.reverse_reverse]
  congr 1
  omega

theorem ParameterContextSuffix.depth_le
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    depth ≤ Hc.mlctx.length := by
  rw [H.mlctx_length]; omega

theorem ParameterContextSuffix.headerFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    paramCheckFVars stats stats.params.size =
      (Hc.mlctx.dropN depth H.depth_le).fvarList := by
  have h := (H.bottom stats.params.size (Nat.le_refl _)).2
  simp only [Nat.sub_self, Nat.add_zero] at h
  exact h

theorem ParameterContextSuffix.headerVLCtx
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    (Hc.mlctx.dropN depth H.depth_le).vlctx = H.parameterDecls := by
  have h := (H.bottom stats.params.size (Nat.le_refl _)).1
  simp only [Nat.sub_self, Nat.add_zero, List.drop_zero] at h
  exact h

/-- The header checker context of a parameter suffix: the checker context
holds exactly the cached parameters, which are the bottom of the main
context. -/
def ParameterContextSuffix.headerCheck
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    ContextWF (headerCheckContext c stats) :=
  Hc.headerCheck stats depth H.depth_le H.headerFVars

@[simp] theorem ParameterContextSuffix.headerCheck_venv
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    H.headerCheck.venv = Hc.venv := rfl

@[simp] theorem ParameterContextSuffix.headerCheck_mlctx
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    H.headerCheck.mlctx = Hc.mlctx := rfl

theorem ParameterContextSuffix.headerCheck_chk_vlctx
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    H.headerCheck.chk.vlctx = H.parameterDecls := H.headerVLCtx

/-- The same suffix, over the header checker context. -/
def ParameterContextSuffix.toHeaderCheck
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    ParameterContextSuffix H.headerCheck stats depth := { H with }

/-- In the header checker context the parameter declarations are aligned
with the checker context. -/
theorem ParameterContextSuffix.headerCheck_paramAligned
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : ParameterContextSuffix Hc stats depth) :
    VLCtx.IsDefEq Hc.venv c.lparams.length H.parameterDecls
      H.headerCheck.chk.vlctx := by
  rw [H.headerCheck_chk_vlctx]
  have hwf := H.headerCheck.check.wf.tr.wf
  change VLCtx.WF Hc.venv c.lparams.length H.headerCheck.chk.vlctx at hwf
  rw [H.headerCheck_chk_vlctx] at hwf
  exact .refl Hc.checking.tr.wf hwf

/-- Concrete scope of a later header immediately before processing cached
parameter `i`.
Only parameters already processed by this later header may occur; ambient
indices and the current-or-future cached parameters are excluded. -/
structure ReusedParameterScope
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : Hc.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    Hc.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem ReusedParameterScope.olderLength
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size) :
    H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

theorem ReusedParameterScope.older_eq_nil
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

/-- After the final cached parameter is processed, the accumulated
scope is exactly the complete cached-parameter suffix. -/
theorem ReusedParameterScope.scope
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

/-- Consecutive cached-parameter scopes agree on the processed suffix. -/
theorem ReusedParameterScope.nextOlder
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {e next : Expr}
    (H : ReusedParameterScope Hsuffix i e)
    (Hnext : ReusedParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

theorem ReusedParameterScope.openedFVars
    (H : ReusedParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem ReusedParameterScope.openedUpSet
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : ReusedParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      Hc.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older) H.added
    (by simpa [H.context] using Hc.mlctx_wf.tr.wf)

/-- Substitution of the current cached parameter, followed by an executable
normalization step, cannot introduce dependencies outside the newly processed
parameter scope. -/
theorem ReusedParameterScope.unannotatedFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : ReusedParameterScope Hsuffix i body)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

theorem ReusedParameterScope.olderDrop
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e) (hi : i < stats.params.size) :
    Hsuffix.parameterDecls.drop (stats.params.size - i) = H.older ∧
    Hsuffix.parameterDecls.drop (stats.params.size - (i + 1)) =
      (some (H.fv, H.deps), .vlam H.paramType) :: H.older := by
  rw [H.parameterDecls]
  have hn := H.newerLength
  constructor
  · rw [show stats.params.size - i = H.newer.length + 1 by omega, List.drop_append]
    simp
  · rw [show stats.params.size - (i + 1) = H.newer.length by omega, List.drop_append]
    simp

/-- The checker contexts of the cached-parameter step: the parameters before
`i`, and those up to and including `i`, together with the declared type of
parameter `i` translated among the earlier parameters. -/
theorem ReusedParameterScope.scopedTyping
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : ReusedParameterScope Hsuffix i e) (hi : i < stats.params.size) :
    (Hc.mlctx.dropN (depth + (stats.params.size - i))
        (by rw [Hsuffix.mlctx_length]; omega)).vlctx = H.older ∧
    (Hc.mlctx.dropN (depth + (stats.params.size - (i + 1)))
        (by rw [Hsuffix.mlctx_length]; omega)).vlctx =
      (some (H.fv, H.deps), .vlam H.paramType) :: H.older ∧
    ∃ paramTy, (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy) ∧
      TrExprS Hc.venv c.lparams H.older paramTy H.paramType ∧
      Hc.venv.IsType c.lparams.length H.older.toCtx H.paramType := by
  obtain ⟨hd₀, hd₁⟩ := H.olderDrop hi
  have hb₀ := (Hsuffix.bottom i (by omega)).1
  have hb₁ := (Hsuffix.bottom (i + 1) (by omega)).1
  rw [hd₀] at hb₀
  rw [hd₁] at hb₁
  refine ⟨hb₀, hb₁, ?_⟩
  have hj : depth + (stats.params.size - (i + 1)) ≤ Hc.mlctx.length := by
    rw [Hsuffix.mlctx_length]; omega
  have hmwf := Hc.mlctx_wf.dropN _ hj
  have hmem : H.fv ∈ (Hc.mlctx.dropN _ hj).vlctx.fvars := by
    rw [hb₁]; simp [VLCtx.fvars_cons_some]
  have hfind := Hc.onlyLams.dropN_find?_eq Hc.mlctx_wf _ hj hmem
  have honly := Hc.onlyLams.dropN _ hj
  generalize Hc.mlctx.dropN _ hj = m at hb₁ hmwf hfind honly
  cases m with
  | nil => simp at hb₁
  | vlet => exact honly.vlet_false.elim
  | vlam id name ty ty' bi tail =>
    simp only [TypeChecker.MLCtx.vlctx, List.cons.injEq, Prod.mk.injEq,
      Option.some.injEq] at hb₁
    obtain ⟨⟨⟨rfl, -⟩, hty'⟩, htail⟩ := hb₁
    cases hty'
    obtain ⟨htailWF, hfresh, htr, hty⟩ := hmwf
    rw [htail] at htr hty
    refine ⟨ty, ?_, htr, hty⟩
    intro ty' hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty' at hrun
    have hfind' : c.lctx.find? H.fv =
        some (.cdecl tail.lctx.decls.size H.fv name ty bi .default) := by
      rw [← Hc.lctx_eq, hfind]
      change (tail.lctx.mkLocalDecl H.fv name ty bi).find? H.fv = _
      rw [LocalContext.find?_mkLocalDecl htailWF.tr.1.map_wf]
      simp
    simp only [LocalContext.get!, hfind', Except.ok.injEq] at hrun
    exact hrun.symm

/-- Recover every premise needed by the executable cached-parameter branch
from the retained local-context translation. -/
theorem ReusedParameterScope.typing
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : ReusedParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' ∧
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? Hc.mlctx_wf.tr.wf.fvars_nodup hhead
  rcases hfull with hfull
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : Hc.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ Hc.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  have hlocal :=
    (Hc.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv
  rcases hlocal with ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← Hc.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ Hc.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact Hc.mlctx_wf.tr.wf.find?_wf Hc.checking.tr.wf hfind

theorem ParameterCachePrefix.push
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats done 0)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      (done + 1) 0 := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hold : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList
      ((cachedParamVars done 0).map fun e => e.liftN 1 0) := by
    have mapRight : ∀ {as bs},
        List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
        List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
          (bs.map fun e => e.liftN 1 0) := by
      intro as bs hp
      induction hp with
      | nil => exact .nil
      | cons h _ ih =>
        exact .cons
          (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
    exact mapRight H.params
  have hfresh : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
    exact TrExprS.fvar (A := ty'.lift) (by
      change VLCtx.find? ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
      simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
        VLocalDecl.value, VLocalDecl.type])
  refine ⟨?_, ?_⟩
  · simpa using List.Forall₂.append'
      hold (.cons hfresh .nil)
  · intro param hparam
    simp only [Array.mem_push] at hparam
    rcases hparam with hparam | rfl
    · exact H.paramFVars param hparam
    · exact ⟨⟨c.ngen.curr⟩, rfl⟩

/-- Index binders do not change the concrete parameter cache; they uniformly
shift its abstract de Bruijn interpretation. -/
theorem ParameterCachePrefix.withIndex
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats
      done depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats done (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  refine ⟨?_, H.paramFVars⟩
  rw [cachedParamVars_depth_succ]
  have mapRight : ∀ {as bs},
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
      List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
        (bs.map fun e => e.liftN 1 0) := by
    intro as bs hp
    induction hp with
    | nil => exact .nil
    | cons h _ ih =>
      exact .cons
        (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
  exact mapRight H.params

theorem ParameterCachePrefix.complete
    {decl : VInductDecl}
    (H : ParameterCachePrefix env Us Δ stats decl.nparams depth) :
    List.Forall₂ (TrExprS env Us Δ) stats.params.toList
      (decl.paramVars depth) := by
  rw [← cachedParamVars_eq_paramVars decl]
  exact H.params

/-- Fuel exhaustion cannot produce a successful result. -/
theorem zero.WF :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      0 k c).WF Q := by
  intro _ h
  simp [AddInductive.checkInductiveTypes.loopType] at h

/-- Base case of the header telescope traversal.  This theorem deliberately
states only the executable control-flow fact; the caller's continuation owns
the declarative result-sort and accumulated-telescope obligations. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i = nparams)
    (Hk : (k type stats nindices c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  subst i
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]

/-- A non-forall tail with the wrong number of common parameters is rejected,
so this branch is semantically vacuous. -/
theorem parameterMismatch.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i ≠ nparams) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Verification step for an index binder.  `hdom`/`hdomType` are stated for
the unannotated domain (`consumeTypeAnnotationsVerified`) actually installed
in the executable local context, and `hdom₀`/`hdomType₀` for the same domain
in the checker context; deriving them from the source domain is the separate
`ConsumeTypeAnnotationsCompat` obligation.  The continuation receives the facts about the
normal form in both contexts. -/
theorem index.WF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hdom₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx
      (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) dom₀)
    (hdomType₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx dom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam dom₀) :: Hc.chk.vlctx) body body₀)
    (Hrec : ∀ normalized,
      FVarsBelow
        (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
      TrExpr (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).venv
        c.lparams
        (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).mlctx.vlctx
        normalized body' →
      FVarsBelow
        (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).chk.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
      TrExpr Hc.venv c.lparams
        (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).chk.vlctx
        normalized body₀ →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_neg hi]
  refine withCheckedLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => do
      let type := body.instantiate1 arg
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) i (nindices + 1) fuel k)
    Hc hdom hdomType hdom₀ hdomType₀ ?_
  let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  have hopened₀ := Hc.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
    hdom₀ hdomType₀ hbody₀
  exact (whnfInContext.dualWF Hc' hopened hopened₀).bind
    fun normalized ⟨⟨h1, h2⟩, h3, h4⟩ => Hrec normalized h1 h2 h3 h4

/-- Source-facing index step: consume the domain certificates and transport
the source bodies automatically before invoking `index.WF`. -/
theorem index.sourceWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ body₀',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom₀ :: Hc.chk.vlctx.toCtx) sourceBody₀ body₀' →
      ∀ normalized,
        FVarsBelow
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx normalized body'' →
        FVarsBelow
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx normalized body₀' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
            checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  rcases Hdom₀.body Hc.atCheckLCtx hbody₀ with ⟨body₀', hbody₀', hbodyEq₀⟩
  exact index.WF Hc hi Hdom.unannotated Hdom.isType hbody''
    Hdom₀.unannotated Hdom₀.isType hbody₀'
    (fun normalized h1 h2 h3 h4 =>
      Hrec body'' hbodyEq body₀' hbodyEq₀ normalized h1 h2 h3 h4)

/-- Index-step wrapper whose continuation also receives the cached-parameter
invariant at the extended context. -/
theorem index.cacheWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ body₀',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom₀ :: Hc.chk.vlctx.toCtx) sourceBody₀ body₀' →
      ∀ normalized,
        FVarsBelow
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx normalized body'' →
        FVarsBelow
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).chk.vlctx normalized body₀' →
        ParameterCachePrefix Hc.venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx stats done (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
            checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hdom hbody Hdom₀ hbody₀
  intro body'' hbodyEq body₀' hbodyEq₀ normalized h1 h2 h3 h4
  exact Hrec body'' hbodyEq body₀' hbodyEq₀ normalized h1 h2 h3 h4
    (Hcache.withIndex Hc Hdom.unannotated Hdom.isType)

/-- Complete index branch for the synthesized header telescope of the first
header, whose checker context is aligned with the main context.  The source
body conversion and the following executable `whnf` are composed before the
recursive state is exposed. -/
theorem index.cacheTelescopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (halign : Hc.Aligned)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hsynthesis : HeaderTelescope Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_henv : c'.env = c.env)
      (_hsafety : c'.safety = c.safety)
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (_hallowPrimitive : c'.allowPrimitive = c.allowPrimitive)
      (_hfuel : c'.fuel = c.fuel)
      (normalized : Expr) (next : VExpr),
      Hc'.Aligned →
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats done (depth + 1) →
      ParameterContextSuffix Hc' stats (depth + 1) →
      HeaderTelescope Hc' target next i (nindices + 1) →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        i (nindices + 1) fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  obtain ⟨source₀, consumed₀, Hdom₀, hsu, -⟩ := halign.unannotatedDomain Hdom
  obtain ⟨body₀, hbody₀, -⟩ := halign.body Hdom.sourceIsType hsu hbody
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody Hdom₀ hbody₀
  intro body'' hbodyEq _ _ normalized _ hnormalized _ _ Hcache'
  let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
    Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
  have hbodyEq' := Hdom.bodyDefEqUnannotated Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv,
      ContextWF.withCheckedLocalDeclOn_venv, ContextWF.withLocalDecl_toCtx,
      ContextWF.withCheckedLocalDecl_toCtx, ContextWF.withCheckedLocalDeclOn_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  exact Hrec Hc' rfl rfl rfl rfl rfl rfl normalized next
    (halign.withCheckedLocalDecl _ _ _ _) hnext Hcache'
    (Hsuffix.withIndex Hc Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType)
    ((Hsynthesis.withIndex Hdom Hdom₀).normalize hsourceNext)

/-- Verification step for a common parameter of the first mutual header.  In
addition to the opened-body relation, the continuation sees the exact fresh
free variable appended to the executable parameter cache. -/
theorem firstParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hdom₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx
      (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) dom₀)
    (hdomType₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx dom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam dom₀) :: Hc.chk.vlctx) body body₀)
    (Hrec : ∀ normalized,
      TrExpr (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).venv
        c.lparams
        (Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_pos hempty]
  refine withCheckedLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun param => do
      let stats := { stats with params := stats.params.push param }
      let type := body.instantiate1 param
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k)
    Hc hdom hdomType hdom₀ hdomType₀ ?_
  let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi) hdom hdomType hdom₀ hdomType₀
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  have hopened₀ := Hc.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
    hdom₀ hdomType₀ hbody₀
  exact (whnfInContext.WF Hc' hopened hopened₀).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Source-facing first-parameter step, including annotation-domain and body
transport. -/
theorem firstParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
            checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  rcases Hdom₀.body Hc.atCheckLCtx hbody₀ with ⟨body₀', hbody₀', -⟩
  exact firstParameter.WF Hc hi hempty Hdom.unannotated Hdom.isType hbody''
    Hdom₀.unannotated Hdom₀.isType hbody₀'
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- First-parameter wrapper synchronized with the executable cache push. -/
theorem firstParameter.cacheWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom sourceDom₀ consumedDom₀)
    (hbody₀ : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom₀) :: Hc.chk.vlctx) body sourceBody₀)
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).venv c.lparams
          (Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
            checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hdom hbody Hdom₀ hbody₀
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.push Hc Hdom.unannotated Hdom.isType)

/-- Complete first-parameter branch for the synthesized header telescope. -/
theorem firstParameter.cacheTelescopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (halign : Hc.Aligned)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hsuffix : ParameterContextSuffix Hc stats 0)
    (hprefix : Hsuffix.ambientDecls = [])
    (Hsynthesis : HeaderTelescope Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Hsynthesis.indices = [])
    (Hdom : Hc.UnannotatedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_henv : c'.env = c.env)
      (_hsafety : c'.safety = c.safety)
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (_hallowPrimitive : c'.allowPrimitive = c.allowPrimitive)
      (_hfuel : c'.fuel = c.fuel)
      (normalized : Expr) (next : VExpr),
      Hc'.Aligned →
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        (done + 1) 0 →
      ParameterContextSuffix Hc'
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        0 →
      (Hsynthesis' : HeaderTelescope
        Hc' target next (i + 1) nindices) →
      Hsynthesis'.indices = [] →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  obtain ⟨source₀, consumed₀, Hdom₀, hsu, -⟩ := halign.unannotatedDomain Hdom
  obtain ⟨body₀, hbody₀, -⟩ := halign.body Hdom.sourceIsType hsu hbody
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody Hdom₀ hbody₀
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
    Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
  have hbodyEq' := Hdom.bodyDefEqUnannotated Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv, ContextWF.withCheckedLocalDecl_venv,
      ContextWF.withCheckedLocalDeclOn_venv, ContextWF.withLocalDecl_toCtx,
      ContextWF.withCheckedLocalDecl_toCtx, ContextWF.withCheckedLocalDeclOn_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  let Hsynthesis' :=
    (Hsynthesis.withParameter hindices Hdom Hdom₀).normalize hsourceNext
  exact Hrec Hc' rfl rfl rfl rfl rfl rfl normalized next
    (halign.withCheckedLocalDecl _ _ _ _) hnext Hcache'
    (Hsuffix.push Hc hprefix Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType)
    Hsynthesis' (by rfl)

/-- A closed source header starts the later-parameter traversal with an empty
free-variable scope. -/
noncomputable def ReusedParameterScope.ofNoFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    ReusedParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

/-- Advance the reused-parameter scope after substituting cached parameter `i` and
normalizing the resulting body.  The next parameter's older suffix is
exactly the current cached declaration followed by the current older suffix.
-/
noncomputable def ReusedParameterScope.next
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : ReusedParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    ReusedParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp :
        H.newer ++ currentEntry :: H.older =
          (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hopened : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older))
        (body.instantiate1 stats.params[i]!) := by
      rw [Expr.instantiate1_eq, H.parameter]
      exact H.openedFVars
    have hnormalized : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older)) normalized :=
      hbelow _ H.openedUpSet hopened
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

/-- Complete cached-parameter step of a later mutual header.  The executable
compares the domain with the cached parameter type in the checker context of
the earlier parameters, and normalizes the instantiated body in the checker
context of the parameters up to the current one; both runs are verified in
those contexts, which are exactly the scopes recorded by `Hscope`. -/
theorem laterParameter.checkedScopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : ReusedParameterScope Hsuffix i
      (.forallE name dom body bi))
    (histats : i < stats.params.size)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hnarrow : TrExprS Hc.venv c.lparams Hscope.older
      (.forallE name dom body bi) narrowCurrent)
    (Hrec : ∀ {paramTy' param'},
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' →
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      (∃ sourceDom',
        TrExprS Hc.venv c.lparams Hscope.older dom sourceDom' ∧
        Hc.venv.IsDefEqU c.lparams.length Hscope.older.toCtx
          sourceDom' Hscope.paramType) →
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          ReusedParameterScope Hsuffix (i + 1) normalized) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hscope.typing with
    ⟨paramTy, paramTy', param', hget, hparamTy, _hparamTyEq,
      hparam, hparamType⟩
  obtain ⟨hb₀, hb₁, paramTy₀, hget₀, hparamTy₀, hparamType₀⟩ :=
    Hscope.scopedTyping histats
  cases hnarrow with
  | forallE _hdomType₀ _hbodyType₀ hdom₀ hbody₀ =>
  rename_i dom₀ body₀
  have hj₀ : depth + (stats.params.size - i) ≤ Hc.mlctx.length := by
    rw [Hsuffix.mlctx_length]; omega
  have hj₁ : depth + (stats.params.size - (i + 1)) ≤ Hc.mlctx.length := by
    rw [Hsuffix.mlctx_length]; omega
  let Hci := Hc.paramCheck stats i _ hj₀ (Hsuffix.bottom i (by omega)).2
  let Hci₁ := Hc.paramCheck stats (i + 1) _ hj₁ (Hsuffix.bottom (i + 1) (by omega)).2
  have hchk₀ : Hci.chk.vlctx = Hscope.older := hb₀
  have hchk₁ : Hci₁.chk.vlctx =
      (some (Hscope.fv, Hscope.deps), .vlam Hscope.paramType) :: Hscope.older := hb₁
  have holderWF : VLCtx.WF Hc.venv c.lparams.length Hscope.older :=
    hchk₀ ▸ Hci.check.wf.tr.wf
  have hentryWF : VLCtx.WF Hc.venv c.lparams.length
      ((some (Hscope.fv, Hscope.deps), .vlam Hscope.paramType) :: Hscope.older) :=
    hchk₁ ▸ Hci₁.check.wf.tr.wf
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← AddInductive.withCheckLCtx (← AddInductive.paramCheckLCtx stats i)
          (TypeChecker.isDefEq dom paramTy) do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      let type ← AddInductive.withCheckLCtx
        (← AddInductive.paramCheckLCtx stats (i + 1)) (TypeChecker.whnf type)
      AddInductive.checkInductiveTypes.loopType nparams stats type
        (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  have hgetBoth : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy ∧ ty = paramTy₀) := fun a ha => ⟨hget a ha, hget₀ a ha⟩
  refine hgetBoth.bind fun paramTy'' ⟨hparamTyEq, hparamTyEq₀⟩ => ?_
  subst paramTy''
  subst paramTy₀
  refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
  subst hL
  have hdomN : TrExprS Hc.venv c.lparams Hci.chk.vlctx dom dom₀ := by
    rw [hchk₀]; exact hdom₀
  have hparamTyN : TrExprS Hc.venv c.lparams Hci.chk.vlctx paramTy Hscope.paramType := by
    rw [hchk₀]; exact hparamTy₀
  refine (isDefEqInContext.checkingWF Hci hdomN hparamTyN).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq₀ : Hc.venv.IsDefEqU c.lparams.length Hscope.older.toCtx dom₀ Hscope.paramType := by
      have := hequal rfl; rw [hchk₀] at this; exact this
    have heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx dom' paramTy' :=
      Hci.check.embed.isDefEqU Hc.checking.tr.wf hdomN hparamTyN hdom hparamTy (hequal rfl)
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    -- the body in the header's own scope, under the cached parameter type
    obtain ⟨v, hv⟩ := _hdomType₀
    have hctx : VLCtx.IsDefEq Hc.venv c.lparams.length
        ((none, .vlam dom₀) :: Hscope.older)
        ((none, .vlam Hscope.paramType) :: Hscope.older) :=
      .cons (.refl Hc.checking.tr.wf.ordered holderWF) nofun
        (.vlam (heq₀.of_l Hc.checking.tr.wf holderWF.toCtx hv))
    obtain ⟨bodyC, hbodyC⟩ := hbody₀.defeqDFC Hc.checking.tr.wf hctx
    have hopened₀ : TrExprS Hc.venv c.lparams Hci₁.chk.vlctx
        (body.instantiate1 stats.params[i]!) bodyC := by
      rw [hchk₁, Expr.instantiate1_eq, Hscope.parameter]
      exact hbodyC.inst_fvar Hc.checking.tr.wf.ordered hentryWF
    refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
    subst hL
    let Hbody : ReusedParameterScope Hsuffix i body := {
      Hscope with fvars := Hscope.fvars.2 }
    exact (whnfInContext.dualWF Hci₁ hopened hopened₀).bind
      fun normalized ⟨⟨hbelow, hnormalized⟩, _, hnormalized₀⟩ => by
      refine Hrec hparam hparamType heq ⟨dom₀, hdom₀, heq₀⟩ ⟨bodyC, hbodyC⟩
        normalized hbelow hnormalized ?_ (fun hnext => Hbody.next hnext hbelow)
      rw [hchk₁] at hnormalized₀
      obtain ⟨normalized', hnormalized', hnormEq⟩ := hnormalized₀
      exact ⟨bodyC, normalized', hbodyC, hnormalized', hnormEq.symm⟩

/-- Recursive verifier for the first mutual header.  It follows the concrete
fuel recursion and carries both the parameter cache and the synthesized
abstract telescope to the terminal continuation. -/
theorem firstHeaderTelescopeWF
    {target : VInductiveTypeSkeleton}
    {sourceEnv : Environment}
    {sourceSafety : DefinitionSafety}
    {sourceAllowPrimitive : Bool}
    {sourceFuel : FuelConfig}
    {baseLevels : List Level} {baseNindices : Array Nat}
    {baseConsts : Array Expr}
    {R : VEnv → Prop}
    {α : Type} (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M α) (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {type' : Expr}
      {current' : VExpr} {i' nindices' : Nat}
      (Hc' : ContextWF c'),
      c'.env = sourceEnv →
      c'.safety = sourceSafety →
      c'.lparams = Us →
      c'.allowPrimitive = sourceAllowPrimitive →
      c'.fuel = sourceFuel →
      stats'.indConsts.isEmpty = true →
      stats'.levels = baseLevels →
      stats'.nindices = baseNindices →
      stats'.indConsts = baseConsts →
      R Hc'.venv →
      Hc'.Aligned →
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      i' = nparams →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' i' nindices' →
      ParameterContextSuffix Hc' stats' nindices' →
      HeaderTelescope Hc' target current' i' nindices' →
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      (k type' stats' nindices' c').WF Q)
    (Hc : ContextWF c)
    (halign : Hc.Aligned)
    (henv : c.env = sourceEnv)
    (hsafety : c.safety = sourceSafety)
    (hlparams : c.lparams = Us)
    (hallowPrimitive : c.allowPrimitive = sourceAllowPrimitive)
    (hfuel : c.fuel = sourceFuel)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevelsStable : stats.levels = baseLevels)
    (hnindicesStable : stats.nindices = baseNindices)
    (hconstsStable : stats.indConsts = baseConsts)
    (HR : R Hc.venv)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats i nindices)
    (Hsuffix : ParameterContextSuffix Hc stats nindices)
    (Hsynthesis : HeaderTelescope Hc target current i nindices)
    (hphase : i < nparams → Hsynthesis.indices = [] ∧ nindices = 0)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      fuel k c).WF Q := by
  induction fuel generalizing c stats type current i nindices halign with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htype with
      | forallE hdomType hbodyType hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom, Hdom⟩
        by_cases hi : i < nparams
        · rcases hphase hi with ⟨hindices, hnindices⟩
          subst nindices
          have hambient : Hsuffix.ambientDecls = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using Hsuffix.prefixLength
          apply firstParameter.cacheTelescopeWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi hempty halign (by simpa using Hcache) Hsuffix hambient
            Hsynthesis hindices Hdom hbody
          intro c' Hc' henv' hsafety' hvenv' hlparams' hallowPrimitive'
            hfuel' normalized next halign' hnext Hcache' Hsuffix'
            Hsynthesis' hindices'
          apply ih Hc' halign' (henv'.trans henv) (hsafety'.trans hsafety)
            (hlparams'.trans hlparams)
            (hallowPrimitive'.trans hallowPrimitive)
            (hfuel'.trans hfuel)
            (by simpa using hempty)
            (by simpa using hlevelsStable)
            (by simpa using hnindicesStable)
            (by simpa using hconstsStable)
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro _
            exact ⟨hindices', rfl⟩
          · exact hnext
        · apply index.cacheTelescopeWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi halign Hcache Hsuffix Hsynthesis Hdom hbody
          intro c' Hc' henv' hsafety' hvenv' hlparams' hallowPrimitive'
            hfuel' normalized next halign' hnext Hcache' Hsuffix'
            Hsynthesis'
          apply ih Hc' halign' (henv'.trans henv) (hsafety'.trans hsafety)
            (hlparams'.trans hlparams)
            (hallowPrimitive'.trans hallowPrimitive)
            (hfuel'.trans hfuel)
            hempty hlevelsStable
            hnindicesStable hconstsStable
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro hlt
            exact False.elim (hi hlt)
          · exact hnext
    · by_cases hi : i = nparams
      · exact result.WF hforall hi
          (Hresult Hc henv hsafety hlparams hallowPrimitive hfuel hempty
            hlevelsStable hnindicesStable
            hconstsStable HR halign hforall hi Hcache Hsuffix Hsynthesis htype)
      · exact parameterMismatch.WF hforall hi

/-- Cached-parameter recursion with the independent scoped header telescope
accumulated in lockstep.  The executable reader context remains unchanged;
the synthesis scope grows only by the parameters processed by this header. -/
theorem laterParameterTelescopeWF
    {alpha : Type} (Hc : ContextWF c)
    {target : VInductiveTypeSkeleton}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hresult : ∀ {type' narrowCurrent fullCurrent scope' i' fuel'},
      i' = nparams →
      ScopedHeaderTelescope Hc.venv c.lparams target
        scope' narrowCurrent i' 0 →
      scope' = Hsuffix.parameterDecls →
      TrExprS Hc.venv c.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' fullCurrent →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        0 fuel' k c).WF Q)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : ∀ _h : i < stats.params.size,
      ReusedParameterScope Hsuffix i type)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis : ScopedHeaderTelescope Hc.venv c.lparams
      target scope narrowCurrent i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      0 fuel k c).WF Q := by
  induction fuel generalizing type scope narrowCurrent fullCurrent i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htypeFull with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := 0) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix Hcurrent histats hdom hbody htypeNarrow
        intro paramTy' param' _hparam _hparamType _heq hdomain
          _habstract normalized hbelow hnormalized htransition hnext
        have hindices : Hsynthesis.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
        have hcurrentWF : VLCtx.WF Hc.venv c.lparams.length
            ((some (Hcurrent.fv, Hcurrent.deps), .vlam Hcurrent.paramType) ::
              Hcurrent.older) := by
          have := (Hc.mlctx_wf.dropN _
            (by rw [Hsuffix.mlctx_length]; omega :
              depth + (stats.params.size - (i + 1)) ≤ Hc.mlctx.length)).tr.wf
          rwa [(Hcurrent.scopedTyping histats).2.1] at this
        rcases Hsynthesis.consumeParameter Hc.checking.tr.wf hindices
            htypeNarrow hcurrentWF hdomain htransition with
          ⟨normalized', hnormalized', ⟨Hsynthesis'⟩⟩
        let Hbody : ReusedParameterScope Hsuffix i body := {
          Hcurrent with fvars := Hcurrent.fvars.2 }
        exact ih (i := i + 1)
          (scope := (some (Hcurrent.fv, Hcurrent.deps),
            .vlam Hcurrent.paramType) :: Hcurrent.older)
          (narrowCurrent := normalized')
          (fullCurrent := body'.inst param')
          (hbound := by omega)
          (Hscope := fun hlt => hnext hlt)
          (hscopeEq := fun hlt =>
            Hcurrent.nextOlder (hnext hlt) hlt)
          (hcompleteScope := fun heq => by
            have hdone : i + 1 = stats.params.size := by
              rw [hparams]
              exact heq
            exact Hcurrent.scope hdone)
          Hsynthesis' hnormalized'
          (Hbody.unannotatedFVars hbelow) hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq Hsynthesis (hcompleteScope hieq)
        htypeNarrow htypeFVars htypeFull

/-- Traverse the index suffix of a later mutual header while keeping its
semantic telescope independent of ambient declarations retained by the
executable checker. -/
theorem laterIndexTelescopeWF
    {alpha : Type} {target : VInductiveTypeSkeleton}
    {commonParams : List VExpr}
    {paramU : Nat}
    {sourceEnv : Environment}
    {sourceSafety : DefinitionSafety}
    {sourceAllowPrimitive : Bool}
    {sourceFuel : FuelConfig}
    {R : VEnv → Prop}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_henv : c'.env = sourceEnv)
      (_hsafety : c'.safety = sourceSafety)
      (_hlparams : c'.lparams = c.lparams)
      (_hallowPrimitive : c'.allowPrimitive = sourceAllowPrimitive)
      (_hfuel : c'.fuel = sourceFuel)
      {type' narrowCurrent fullCurrent scope' nindices' fuel'},
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      (Hsynthesis' : ScopedHeaderTelescope Hc'.venv c'.lparams
        target scope' narrowCurrent nparams nindices') →
      FrontScopeEmbedding Hc'.venv c'.lparams scope' Hc'.mlctx.vlctx →
      VLCtx.IsDefEq Hc'.venv c'.lparams.length scope' Hc'.chk.vlctx →
      TrExprS Hc'.venv c'.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' fullCurrent →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats nparams (depth + nindices') →
      ParameterContextSuffix Hc' stats (depth + nindices') →
      AmbientParamContext Hc' commonParams (depth + nindices') →
      R Hc'.venv →
      VEnv.IsDefEqCtx Hc'.venv paramU []
        commonParams.reverse Hsynthesis'.params.reverse →
      (AddInductive.checkInductiveTypes.loopType nparams stats type'
        nparams nindices' (fuel' + 1) k c').WF Q)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hc : ContextWF c)
    (henv : c.env = sourceEnv)
    (hsafety : c.safety = sourceSafety)
    (hallowPrimitive : c.allowPrimitive = sourceAllowPrimitive)
    (hfuel : c.fuel = sourceFuel)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats nparams (depth + nindices))
    (Hsuffix : ParameterContextSuffix Hc stats (depth + nindices))
    (Hambient : AmbientParamContext Hc commonParams
      (depth + nindices))
    (HR : R Hc.venv)
    (Hsynthesis : ScopedHeaderTelescope Hc.venv c.lparams
      target scope narrowCurrent nparams nindices)
    (Hparams : VEnv.IsDefEqCtx Hc.venv paramU []
      commonParams.reverse Hsynthesis.params.reverse)
    (Hruntime : FrontScopeEmbedding Hc.venv c.lparams
      scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type
      nparams nindices fuel k c).WF Q := by
  induction fuel generalizing c type scope narrowCurrent fullCurrent
      nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htypeNarrow with
      | @forallE indexType narrowBody _ _ _ _ _
          hdomType _hbodyType hdomNarrow hbodyNarrow =>
        have henvWF := Hc.checking.tr.wf
        have hscopeWF₀ : VLCtx.WF Hc.venv c.lparams.length scope := halign.wf
        rcases TrExpr.forallE_source htypeFull with
          ⟨sourceDom, fullBody, hdomFull, hbodyFull,
            hdomFullType, _hbodyFullType, _hfullCurrent⟩
        rcases hconsume c Hc hdomFull hdomFullType with
          ⟨consumedDom, Hdom⟩
        rcases Hdom.body Hc hbodyFull with
          ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
        -- the same binder in the checker context
        obtain ⟨domC, hdomC⟩ := hdomNarrow.defeqDFC henvWF halign
        have hdomCU := hdomNarrow.uniq henvWF halign hdomC
        have hdomCType : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx domC :=
          (hdomType.defeqU_l henvWF hscopeWF₀.toCtx hdomCU).defeqDFC
            henvWF.ordered halign.defeqCtx
        rcases hconsume _ Hc.atCheckLCtx hdomC hdomCType with ⟨consumed₀, Hdom₀⟩
        obtain ⟨v, hv⟩ := hdomType
        have hctxC : VLCtx.IsDefEq Hc.venv c.lparams.length
            ((none, .vlam indexType) :: scope) ((none, .vlam domC) :: Hc.chk.vlctx) :=
          .cons halign nofun (.vlam (hdomCU.of_l henvWF hscopeWF₀.toCtx hv))
        obtain ⟨bodyC, hbodyC⟩ := hbodyNarrow.defeqDFC henvWF hctxC
        rcases Hdom₀.body Hc.atCheckLCtx hbodyC with
          ⟨consumedBody₀, hbodyConsumed₀, _hbodyEq₀⟩
        apply index.WF (stats := stats) (nparams := nparams)
          (i := nparams) (nindices := nindices) (fuel := fuel)
          (k := k) (Q := Q) Hc (by omega) Hdom.unannotated Hdom.isType
          hbodyConsumed Hdom₀.unannotated Hdom₀.isType hbodyConsumed₀
        intro normalized hbelow hnormalized _hbelow₀ hnormalized₀
        let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
        have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotationsVerified_fvarsIn htypeFVars.1)).1
        rcases Hruntime.unannotatedDomain Hc Hdom hdomNarrow with
          ⟨domainLevel, hdomain⟩
        let Hruntime' : FrontScopeEmbedding Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
              .vlam indexType) :: scope)
            Hc'.mlctx.vlctx :=
          Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
            hdomNarrow hdomain ⟨v, hv⟩
        -- the checker context stays aligned with the header's own scope
        have hindexCons : Hc.venv.IsDefEqU c.lparams.length scope.toCtx indexType consumed₀ := by
          obtain ⟨_, hsc⟩ := Hdom₀.source_defeq
          have hsc' := hsc.defeqDFC henvWF.ordered (halign.defeqCtx.symm henvWF.ordered)
          exact hdomCU.trans henvWF hscopeWF₀.toCtx ⟨_, hsc'⟩
        have hfreshScope : (⟨c.ngen.curr⟩ : FVarId) ∉ scope.fvars := by
          rw [halign.fvars]
          intro h
          exact Hc.current_not_mem (Hc.check.embed.fvars_subset h)
        have halign' : VLCtx.IsDefEq Hc'.venv c.lparams.length
            ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
              .vlam indexType) :: scope) Hc'.chk.vlctx :=
          .cons halign (by rintro _ _ ⟨⟩; exact ⟨hfreshScope, hdeps⟩)
            (.vlam (hindexCons.of_l henvWF hscopeWF₀.toCtx hv))
        have hscopeWF : VLCtx.WF Hc'.venv c.lparams.length
            ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
              .vlam indexType) :: scope) := halign'.wf
        have hopenedNarrow : TrExprS Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
              .vlam indexType) :: scope)
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
          rw [Expr.instantiate1_eq]
          exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
        have hopenedFVars : FVarsIn
            (· ∈ VLCtx.fvars ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
              .vlam indexType) :: scope))
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) := by
          rw [Expr.instantiate1_eq]
          apply (htypeFVars.2.mono fun fv hfv => by
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_of_mem _ hfv).instantiate1
          rw [VLCtx.fvars_cons_some]
          exact List.mem_cons_self
        have hnormalizedFVars := hbelow _ Hruntime'.upset hopenedFVars
        -- the checker-context normal form, read in the header's own scope
        rcases hnormalized₀ with ⟨normalizedC, hnormalizedC, hnormalizedCEq⟩
        obtain ⟨normalizedNarrow, hnormalizedNarrow⟩ :=
          hnormalizedC.defeqDFC henvWF (halign'.symm henvWF.ordered)
        have hnn := hnormalizedNarrow.uniq henvWF halign' hnormalizedC
        have hctxB : VLCtx.IsDefEq Hc.venv c.lparams.length
            ((none, .vlam indexType) :: scope)
            ((none, .vlam consumed₀) :: Hc.chk.vlctx) :=
          .cons halign nofun (.vlam (hindexCons.of_l henvWF hscopeWF₀.toCtx hv))
        have hbodyU := hbodyNarrow.uniq henvWF hctxB hbodyConsumed₀
        have hnormC : Hc.venv.IsDefEqU c.lparams.length
            (indexType :: scope.toCtx) normalizedC consumedBody₀ :=
          hnormalizedCEq.defeqDFC henvWF.ordered (hctxB.symm henvWF.ordered).defeqCtx
        have hscope'Ctx : VLCtx.toCtx ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
              .vlam indexType) :: scope) = indexType :: scope.toCtx := rfl
        have hΓ' : OnCtx (indexType :: scope.toCtx) (Hc.venv.IsType c.lparams.length) := by
          rw [← hscope'Ctx]; exact hscopeWF.toCtx
        have hnarrow : Hc'.venv.IsDefEqU c.lparams.length
            (indexType :: scope.toCtx)
            narrowBody normalizedNarrow := by
          have h1 : Hc.venv.IsDefEqU c.lparams.length (indexType :: scope.toCtx)
              normalizedNarrow normalizedC := by
            rw [← hscope'Ctx]; exact hnn
          exact hbodyU.trans henvWF hΓ' (hnormC.symm.trans henvWF hΓ' h1.symm)
        have hdomainNarrow : ∃ sourceDom',
            TrExprS Hc'.venv c.lparams scope dom sourceDom' ∧
            Hc'.venv.IsDefEqU c.lparams.length scope.toCtx
              sourceDom' indexType :=
          ⟨_, hdomNarrow, ⟨.sort v, hv⟩⟩
        have htransition : ∃ sourceBody' normalized',
            TrExprS Hc'.venv c.lparams
              ((none, .vlam indexType) :: scope)
              body sourceBody' ∧
            TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope)
              normalized normalized' ∧
            Hc'.venv.IsDefEqU c.lparams.length
              (indexType :: scope.toCtx)
              sourceBody' normalized' :=
          ⟨narrowBody, normalizedNarrow, hbodyNarrow,
            hnormalizedNarrow, hnarrow⟩
        rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
            Hc'.checking.tr.wf
            (.forallE ⟨v, hv⟩ _hbodyType hdomNarrow hbodyNarrow)
            hscopeWF hdomainNarrow htransition with
          ⟨nextNarrow, hnextNarrow, Hsynthesis',
            ⟨hparamsPreserved, _hindicesPreserved⟩⟩
        exact ih (fun Hc'' henv'' hsafety'' hlparams'' hallowPrimitive''
            hfuel'' => Hresult Hc'' henv'' hsafety''
              (by simpa using hlparams'') hallowPrimitive'' hfuel'') Hc'
          (by simpa using henv) (by simpa using hsafety)
          (by simpa using hallowPrimitive) (by simpa using hfuel)
          (by
            have h := Hcache.withIndex (name := name) (bi := bi) Hc Hdom.unannotated Hdom.isType
            rw [← Nat.add_assoc]; exact h)
          (by simpa [Nat.add_assoc] using
            Hsuffix.withIndex Hc Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType)
          (by simpa [Nat.add_assoc] using
            (Hambient.withIndex Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
              Hdom.source_defeq))
          (by change R Hc.venv; exact HR)
          Hsynthesis' (by
            rw [hparamsPreserved]
            change VEnv.IsDefEqCtx Hc.venv paramU []
              commonParams.reverse Hsynthesis.params.reverse
            exact Hparams) Hruntime' halign' hnextNarrow
          hnormalizedFVars
          ⟨_, hnormalized.choose_spec.1, hnormalized.choose_spec.2⟩
    · exact Hresult Hc henv hsafety rfl hallowPrimitive hfuel hforall
        Hsynthesis Hruntime halign
        htypeNarrow
        htypeFVars htypeFull Hcache Hsuffix Hambient HR Hparams

end checkInductiveTypes.loopType

end VerifyInductive
end Lean4Lean
