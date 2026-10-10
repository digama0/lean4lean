import Lean4Lean.Verify.Inductive.Header.Telescope
import Lean4Lean.Verify.Inductive.Header.RawTranslation

/-!
# Per-family steps of the mutual-header loop

Verifies the continuation of `checkInductiveTypes.loopInd` after one header telescope has
been traversed: the first family fixes the common parameters and result universe, later
families must agree with them (`firstResult.WF`, `laterResult.WF`), and the loop ends with
the executable statistics described by `HeaderStatsWF`, the header-phase invariant used
by the constructor phase.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkInductiveTypes.loopInd

/-- At the first mutual header, the executable `whnf` result determines a
syntax-directed abstract normal form.  Independent translation of the source
header shows that this normal form is definitionally equal to the header in
`TrInductDecl`; the checked source type supplies the common typing witness. -/
theorem initialHeaderNormalization
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrSourceConstRaw Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType := by
  rcases hnormalized with ⟨normalized', hnormalized', hnormalizedEq⟩
  have hsource : TrExprS Hc.venv c.lparams [] source.type sourceType := by
    simpa [hctx] using hchecked.2.1
  have htargetEq : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType :=
    Htarget.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsource
  have hsourceType : Hc.venv.HasType c.lparams.length []
      sourceType checkedType' := by
    simpa [hctx, VLCtx.toCtx] using hchecked.2.2.2
  have htargetType := hsourceType.defeqU_l Hc.checking.tr.wf
    (by trivial) htargetEq.symm
  have hnormalizedEq' : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType := by
    simpa [hctx, VLCtx.toCtx] using hnormalizedEq
  have htargetNormalized := htargetEq.trans Hc.checking.tr.wf
    (by trivial) hnormalizedEq'.symm
  exact ⟨normalized', checkedType', hnormalized',
    htargetNormalized.of_l Hc.checking.tr.wf (by trivial) htargetType⟩


/-- Definitional synthesis state used by the complete first-header recursion. -/
theorem initialHeaderTelescopeState
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.HeaderTelescope
        Hc target normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget.raw hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.uvars] at hwf
    exact hwf
  have hcurrent : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader.toU
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.HeaderTelescope.empty
      hctxEq hcurrent hheader⟩⟩

/-- A later source header is closed before cached parameters are substituted.
The free-variable bound of the outer `whnf` result therefore initializes the
reused-parameter scope (`ReusedParameterScope`) at executable parameter zero. -/
noncomputable def initialReusedParameterScope
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (hi : 0 < stats.params.size)
    (Htarget : TrSourceConstRaw Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hnormalized : FVarsBelow Hc.mlctx.vlctx source.type normalized) :
    checkInductiveTypes.loopType.ReusedParameterScope
      Hsuffix 0 normalized := by
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.type.fvarsIn.mono fun fv hfv => by
      simp [VLCtx.fvars] at hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) Hc.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  exact checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars hi
    (hnormalized _ hfalseUpSet hsourceNoFVars)


/-- Initialize the later-header telescope state (`ScopedHeaderTelescope`) in the
empty scope, from the closed translation of the normalized header that the closed
`whnf` run produces in the empty checker context. -/
theorem initialLaterHeaderTelescopeState
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    (Hc : ContextWF c)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hclosed : TrExpr Hc.venv c.lparams [] normalized target.type) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.ScopedHeaderTelescope
        Hc.venv c.lparams target [] normalized' 0 0) := by
  rcases hclosed with ⟨normalized', hnormalized', hheader⟩
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.uvars] at hwf
    exact hwf
  have hnormalizedType : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader.symm
  rcases htargetType with ⟨targetLevel, htargetType⟩
  have hheaderTyped := hheader.symm.of_l Hc.checking.tr.wf (by trivial)
    htargetType
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.ScopedHeaderTelescope.empty
      ⟨targetLevel, htargetType⟩ hnormalizedType hheaderTyped⟩⟩

/-- A sort translation obtained in the checker context transfers to any scope
definitionally equal to the checker context. -/
theorem TrExpr.sort_of_aligned {env : VEnv} {Us : List Name}
    {scope chk : VLCtx} {e : Expr} {cur cur₀ : VExpr} {s : Level}
    (henv : env.WF)
    (halign : VLCtx.IsDefEq env Us.length scope chk)
    (htype : TrExprS env Us scope e cur)
    (htype₀ : TrExprS env Us chk e cur₀)
    (hsorted₀ : TrExpr env Us chk (.sort s) cur₀) :
    TrExpr env Us scope (.sort s) cur := by
  rcases hsorted₀ with ⟨e₂, hs, heq⟩
  have hu := htype.uniq henv halign htype₀
  have heq' := heq.defeqDFC henv.ordered (halign.defeqCtx.symm henv.ordered)
  cases hs with
  | sort h =>
    exact ⟨_, .sort h, heq'.trans henv halign.wf.toCtx hu.symm⟩

def updatedStats (stats : AddInductive.InductiveStats)
    (lctx : LocalContext) (resultLevel : Level) (setResult : Bool)
    (nindices : Nat) (indName : Name) : AddInductive.InductiveStats :=
  let stats := if setResult then
    { stats with
      lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
  else stats
  { stats with
    nindices := stats.nindices.push nindices
    indConsts := stats.indConsts.push (.const indName stats.levels) }

/-- Post-telescope continuation for the first mutual header. -/
theorem firstResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (htype₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx type type₀)
    (Hrec : ∀ resultSort,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      TrExpr Hc.venv c.lparams Hc.chk.vlctx (.sort resultSort) type₀ →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.dualWF Hc htype htype₀).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨⟨hsorted, resultSort, rfl⟩, hsorted₀⟩
  rw [if_pos hempty]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun c' h => ?_
  subst c'
  simpa [updatedStats, Expr.sortLevel!] using Hrec resultSort hsorted hsorted₀


/-- Metadata-synthesizing first-header continuation.  The executable index
counter and translated result sort are exported as data, together with a
declaration-independent shape proof; no pre-existing `VInductiveType`
metadata is assumed. -/
theorem firstResult.formsHeader
    {source : VInductiveTypeSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderTelescope
      Hc source current nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (halign : Hc.Aligned)
    (huvars : c.lparams.length = uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.HeaderFormation Hc.venv c.lparams
        uvars nparams
        Hsynthesis.params source nindices resultLevel →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  obtain ⟨type₀, htype₀, -⟩ := halign.tr htype
  apply firstResult.WF k Q Hc hempty htype htype₀
  intro resultSort hsorted _
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  exact Hrec resultSort resultLevel hofLevel
    (Hsynthesis.headerFormation huvars hofLevel hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)


/-- Post-telescope continuation for later mutual headers.  A mismatched result
universe throws; a successful path records the checked equivalence before
updating the per-type arrays. -/
theorem laterResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (htype₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx type type₀)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      TrExpr Hc.venv c.lparams Hc.chk.vlctx (.sort resultSort) type₀ →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.dualWF Hc htype htype₀).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨⟨hsorted, resultSort, rfl⟩, hsorted₀⟩
  rw [if_neg (by simp [hnonempty])]
  by_cases hequiv : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = true
  · have hequiv' : resultSort.isEquiv stats.resultLevel = true := by
      simpa [Expr.sortLevel!] using hequiv
    simpa [updatedStats, Expr.sortLevel!, hequiv, hequiv'] using
      Hrec resultSort hequiv' hsorted hsorted₀
  · have hfalse : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = false := by
      cases h : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel <;>
        simp_all
    have hnot : (!(Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel) = true := by
      simp [hfalse]
    rw [if_pos hnot]
    change (Except.error _).WF Q
    exact Except.WF.throw


/-- Base case of the mutual-header loop.  The executable assertions become
explicit invariants at the proof boundary instead of being silently erased. -/
theorem result.WF
    (hidx : ¬ dIdx < indTypes.size)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = indTypes.size)
    (hconsts : stats.indConsts.size = indTypes.size)
    (hparams : stats.params.size = nparams)
    (Hk : (k stats c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_neg hidx]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  simpa [hlevels, hindices, hconsts, hparams] using Hk


/-- Concrete statistics recovered together with the checked mutual headers.
This is the early traversal-facing form of `ValidAppStatsWF`; it is kept here
because the latter also packages the derived name-search invariant used by
positivity, which is defined after the executable constructor interfaces. -/
structure HeaderStatsWF (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (depth : Nat) where
  headers : HeaderCertificate env decl
  normalizedSources : ∀ i (hi : i < decl.types.length), Nonempty
    (checkInductiveTypes.loopType.HeaderSourceTelescope env Us
      headers.params decl.nparams decl.types[i].numIndices)
  normalizedShapes : ∀ i (hi : i < decl.types.length),
    ∃ sourceTelescope :
        checkInductiveTypes.loopType.HeaderSourceTelescope env Us
          headers.params decl.nparams decl.types[i].numIndices,
      ∃ residual exprType,
        env.IsDefEq Us.length [] decl.types[i].type
          (VExpr.wrapForalls
            (sourceTelescope.ownParams ++ sourceTelescope.indices) residual)
          exprType ∧
        env.IsDefEq Us.length
          (sourceTelescope.indices.reverse ++
            sourceTelescope.ownParams.reverse)
          residual (.sort decl.types[i].resultLevel)
            (.sort (.succ decl.types[i].resultLevel))
  isNotZero : stats.isNotZero = stats.resultLevel.isNeverZero
  commonLevel : VLevel.ofLevel Us stats.resultLevel =
    some headers.resultLevel
  levels : stats.levels.length = decl.uvars
  levelParams : stats.levels = Us.map .param
  uvars : Us.length = decl.uvars
  consts : stats.indConsts =
    (decl.types.map fun type => .const type.name stats.levels).toArray
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv
  parameterScope : VLCtx
  ambientScope : VLCtx
  scopeDecomposition : Δ = ambientScope ++ parameterScope
  ambientLength : ambientScope.length = depth
  cachedScope : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse parameterScope
  parameterEmbedding : checkInductiveTypes.loopType.FrontScopeEmbedding
    env Us parameterScope Δ
  paramsContext : VEnv.IsDefEqCtx env Us.length []
    headers.params.reverse parameterScope.toCtx
  suffixParams : List.Forall₂ (TrExprS env Us parameterScope)
    stats.params.toList (decl.paramVars 0)

/-- The executable universe arguments initialized from the declaration's
level-parameter names translate pointwise to their abstract parameter
indices. -/
theorem VLevel.mapM_ofLevel_paramNames (names : List Name) :
    (names.map Level.param).mapM (VLevel.ofLevel names) =
      some (names.map fun name => .param (names.idxOf name)) := by
  have go : ∀ xs : List Name, xs ⊆ names →
      (xs.map Level.param).mapM (VLevel.ofLevel names) =
        some (xs.map fun name => .param (names.idxOf name)) := by
    intro xs hsubset
    induction xs with
    | nil => rfl
    | cons name xs ih =>
      have hname : names.idxOf name < names.length :=
        List.idxOf_lt_length_iff.2 (hsubset (by simp))
      simp [VLevel.ofLevel, hname,
        ih (fun value hvalue => hsubset (by simp [hvalue]))]
  exact go names fun _ => id

theorem HeaderStatsWF.levelTranslation
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    stats.levels.mapM (VLevel.ofLevel Us) =
      some (Us.map fun name => .param (Us.idxOf name)) := by
  rw [H.levelParams]
  exact VLevel.mapM_ofLevel_paramNames Us

theorem _root_.Lean4Lean.VerifyInductive.List.map_param_idxOf_eq_params
    {names : List Name} (H : names.Nodup) :
    names.map (fun name => VLevel.param (names.idxOf name)) =
      VLevel.params names.length := by
  apply List.ext_getElem
  · simp [VLevel.params]
  · intro i hleft hright
    have hi : i < names.length := by
      simpa [VLevel.params] using hright
    simp [VLevel.params, H.idxOf_getElem i hi]

/-- With distinct universe parameters, the block's concrete level list
translates to the identity instantiation of the declaration's universe
context. -/
theorem HeaderStatsWF.levelParamsTranslation
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (hlparams : Us.Nodup) :
    stats.levels.mapM (VLevel.ofLevel Us) = some (VLevel.params decl.uvars) := by
  rw [H.levelTranslation,
    Lean4Lean.VerifyInductive.List.map_param_idxOf_eq_params hlparams, H.uvars]

/-- The executable field-universe guard implies the independent constructor
bound.  The zero branch is semantic level equivalence, matching Lean's
`isAlwaysZero`; the comparison branch is soundness of `geq'`, transported
from the common mutual level to the selected family member. -/
theorem HeaderStatsWF.universeBound
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel Us fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq' (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel ≈ .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel := by
  intro targetIdx hi fieldLevel fieldLevel' hfield hguard
  have htarget := H.headers.commonLevels decl.types[targetIdx]
    (List.getElem_mem hi)
  simp only [Bool.or_eq_true] at hguard
  rcases hguard with hzero | hgeq
  · exact .inl (htarget.trans (ofLevel_isAlwaysZero H.commonLevel hzero))
  · have hle : fieldLevel' ≤ H.headers.resultLevel :=
      Level.geq'_wf H.commonLevel
        (by simpa [Expr.sortLevel!] using hfield) hgeq
    exact .inr (VLevel.le_trans hle (VLevel.le_antisymm_iff.mp htarget).2)

theorem _root_.Lean4Lean.TrSourceConst.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrSourceConst env Us name type value) :
    TrSourceConst env' Us name type value where
  uvars := H.uvars
  name := H.name
  type := H.type.mono henv
  wf := H.wf.mono henv

private theorem forall₂_trExprS_mono {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {es : List Expr} {es' : List VExpr},
      List.Forall₂ (TrExprS env Us Δ) es es' →
      List.Forall₂ (TrExprS env' Us Δ) es es'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (h.mono henv)
      (forall₂_trExprS_mono henv hs)

def HeaderStatsWF.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    HeaderStatsWF env' Us Δ stats decl depth where
  headers := H.headers.mono henv
  normalizedSources := fun i hi =>
    ⟨(Classical.choice (H.normalizedSources i hi)).mono henv⟩
  normalizedShapes := fun i hi => by
    rcases H.normalizedShapes i hi with
      ⟨sourceTelescope, residual, exprType, hheader, hresult⟩
    exact ⟨sourceTelescope.mono henv, residual, exprType,
      hheader.mono henv, hresult.mono henv⟩
  isNotZero := H.isNotZero
  commonLevel := H.commonLevel
  levels := H.levels
  levelParams := H.levelParams
  uvars := H.uvars
  consts := H.consts
  indices := H.indices
  params := forall₂_trExprS_mono henv H.params
  paramFVars := H.paramFVars
  parameterScope := H.parameterScope
  ambientScope := H.ambientScope
  scopeDecomposition := H.scopeDecomposition
  ambientLength := H.ambientLength
  cachedScope := H.cachedScope
  parameterEmbedding := H.parameterEmbedding.mono henv
  paramsContext := H.paramsContext.mono henv
  suffixParams := forall₂_trExprS_mono henv H.suffixParams

def HeaderStatsWF.parameterSuffix
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth) :
    checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth where
  ambientDecls := H.ambientScope
  parameterDecls := H.parameterScope
  context := H.scopeDecomposition
  prefixLength := H.ambientLength
  cached := H.cachedScope
  suffixParams := by
    have hsize : stats.params.size = decl.nparams := by
      have hlength :=
        List.Forall₂.length_eq H.suffixParams
      simpa [VInductDecl.paramVars] using hlength
    rw [hsize,
      checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
    exact H.suffixParams
  sources := H.parameterEmbedding.sourceTelescope


end checkInductiveTypes.loopInd


end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive
namespace checkInductiveTypes.loopType

/-- The executable per-header statistics update leaves the cached common
parameters untouched, so the semantic cache transports unchanged. -/
theorem ParameterCachePrefix.reindexUpdatedStats
    (H : ParameterCachePrefix
      env Us scope stats done depth)
    (lctx : LocalContext) (resultLevel : Level) (first : Bool)
    (nindices : Nat) (indName : Name) :
    ParameterCachePrefix env Us scope
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel first
        nindices indName)
      done depth :=
  H.reindex (by
    cases first <;> simp [checkInductiveTypes.loopInd.updatedStats])

/-- Exact cached-context suffixes survive the same per-header statistics
update. -/
def ParameterContextSuffix.reindexUpdatedStats
    (H : ParameterContextSuffix Hc stats depth)
    (lctx : LocalContext) (resultLevel : Level) (first : Bool)
    (nindices : Nat) (indName : Name) :
    ParameterContextSuffix Hc
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel first
        nindices indName) depth :=
  H.reindex (by
    cases first <;> simp [checkInductiveTypes.loopInd.updatedStats])

end checkInductiveTypes.loopType

end VerifyInductive
end Lean4Lean
