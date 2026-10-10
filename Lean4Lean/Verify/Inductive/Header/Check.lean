import Lean4Lean.Verify.Inductive.Header.Loop
import Lean4Lean.Verify.Inductive.Context.TypeAnnotations

/-! # The header phase: `checkInductiveTypes`

The interface of the mutual-header traversal `AddInductive.checkInductiveTypes nparams indTypes k`
(`Inductive/Add.lean`): it checks every family's type against the common parameter telescope and
result level, records the `InductiveStats` and runs the continuation `k stats` in a context whose
local context holds the parameters as free variables. `HeaderPhase` is what that continuation
may assume (frozen interface); `AddInductive.checkInductiveTypes.WF` is the boundary theorem.

The structures are the interface. The traversal itself is verified in `Header/Loop.lean`
(`checkInductiveTypes.accumulatesHeadersSourceAligned`) against the loop's own accumulator
`checkInductiveTypes.loopType.CheckedHeaders`; `HeaderPhase` retains that accumulator and the
parameter-scope invariants of the loop (`loopHeaders`, `cache`, `suffix`, `ambientParams`) for
the constructor phase, and `CheckedHeaders.ofLoop` reads the interface's `CheckedHeaders` off
it. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The abstract header of a family: the translated constant with the recovered index count and
result level, and no constructors. -/
def headerType (target : VConstVal) (numIndices : Nat) (resultLevel : VLevel) :
    VInductiveType where
  toVConstVal := target
  numIndices := numIndices
  resultLevel := resultLevel
  ctors := []

/-- One checked header: the translation of the source family type and its shape as a family of
any declaration with these universe and parameter counts (`VInductDecl.TypeShape`), at the
common parameter telescope `params` and with a result level equivalent to `commonLevel`. -/
structure CheckedHeader (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel) (source : InductiveType) where
  target : VConstVal
  numIndices : Nat
  resultLevel : VLevel
  translation : TrSourceConst env Us source.name source.type target
  typeShape : ∀ decl : VInductDecl, decl.uvars = Us.length → decl.nparams = nparams →
    decl.TypeShape env params (headerType target numIndices resultLevel)
  commonLevel : resultLevel ≈ commonLevel
  /-- The loop's per-family certificate (`Header/Telescope.lean`): the normalized source
  telescope of the family together with its semantic shape. -/
  formation : checkInductiveTypes.loopType.HeaderFormation env Us Us.length nparams params
    (checkInductiveTypes.loopType.headerSkeleton target) numIndices resultLevel

/-- Ordered semantic outputs of the mutual-header traversal, one per source family. -/
structure CheckedHeaders (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel) (sources : List InductiveType) where
  payloads : List (Sigma fun source => CheckedHeader env Us nparams params commonLevel source)
  sourceOrder : payloads.map Sigma.fst = sources

namespace CheckedHeaders

/-- The recovered `(numIndices, resultLevel)` of every family, in order. -/
def metadata (H : CheckedHeaders env Us nparams params commonLevel sources) :
    List (Nat × VLevel) :=
  H.payloads.map fun p => (p.2.numIndices, p.2.resultLevel)

/-- The abstract type formers, in order. -/
def targets (H : CheckedHeaders env Us nparams params commonLevel sources) : List VConstVal :=
  H.payloads.map fun p => p.2.target

theorem payloads_length (H : CheckedHeaders env Us nparams params commonLevel sources) :
    H.payloads.length = sources.length := by
  have := congrArg List.length H.sourceOrder
  simpa using this

/-- The interface payload of one of the loop's checked headers. -/
def _root_.Lean4Lean.VerifyInductive.CheckedHeader.ofLoop
    (H : checkInductiveTypes.loopType.CheckedHeader env Us nparams params commonLevel source) :
    CheckedHeader env Us nparams params commonLevel source where
  target := H.target
  numIndices := H.numIndices
  resultLevel := H.resultLevel
  translation := H.translation
  typeShape decl huvars hnparams := H.formation.typeShape decl huvars hnparams
  commonLevel := H.commonLevel
  formation := H.formation

/-- The interface headers of the loop's accumulator. -/
def ofLoop
    (H : checkInductiveTypes.loopType.CheckedHeaders env Us nparams params commonLevel sources) :
    CheckedHeaders env Us nparams params commonLevel sources where
  payloads := H.payloads.map fun p => ⟨p.1, CheckedHeader.ofLoop p.2⟩
  sourceOrder := by simpa [List.map_map, Function.comp_def] using H.sourceOrder

@[simp] theorem ofLoop_metadata
    (H : checkInductiveTypes.loopType.CheckedHeaders env Us nparams params commonLevel sources) :
    (ofLoop H).metadata = H.metadata := by
  simp [ofLoop, metadata, checkInductiveTypes.loopType.CheckedHeaders.metadata,
    CheckedHeader.ofLoop]

@[simp] theorem ofLoop_targets
    (H : checkInductiveTypes.loopType.CheckedHeaders env Us nparams params commonLevel sources) :
    (ofLoop H).targets = H.headers.targets := by
  simp [ofLoop, targets, checkInductiveTypes.loopType.CheckedHeaders.headers,
    CheckedHeader.ofLoop]

/-- A declaration whose headers are these: same universe and parameter counts, families with
the checked constants, index counts and result levels, and the source constructor names. The
constructor types are fixed later, by the constructor phase. -/
def Describes (H : CheckedHeaders env Us nparams params commonLevel sources)
    (decl : VInductDecl) : Prop :=
  decl.uvars = Us.length ∧ decl.nparams = nparams ∧
  List.Forall₂ (fun (p : Sigma fun source => CheckedHeader env Us nparams params commonLevel source)
      (t : VInductiveType) =>
    t.toVConstVal = p.2.target ∧ t.numIndices = p.2.numIndices ∧
    t.resultLevel = p.2.resultLevel ∧ t.ctors.map (·.name) = p.1.ctors.map (·.name))
    H.payloads decl.types

/-- The header certificate of a described declaration. -/
def Describes.headerCertificate {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) : HeaderCertificate env decl where
  params := params
  resultLevel := commonLevel
  commonLevels type htype := by
    obtain ⟨p, _, -, -, hlevel, -⟩ := List.Forall₂.forall_exists_r D.2.2 type htype
    rw [hlevel]; exact p.2.commonLevel
  typeShapes type htype := by
    obtain ⟨p, _, htarget, hindices, hlevel, -⟩ := List.Forall₂.forall_exists_r D.2.2 type htype
    have Hshape := p.2.typeShape decl D.1 D.2.1
    have htype : type.type = p.2.target.type := congrArg (fun v : VConstVal => v.type) htarget
    unfold VInductDecl.TypeShape at Hshape ⊢
    rw [htype, hindices, hlevel]
    exact Hshape

end CheckedHeaders

/-- The common-parameter context of the header phase: the cached parameters `stats.params` are
the free variables of the suffix `parameterDecls` of the main context, translating to the
de Bruijn parameter variables, and the context converts to the ambient prefix (of length
`depth`) followed by the common parameter telescope `params`. -/
structure HeaderParameterContext {c : AddInductive.Context} (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats) (params : List VExpr) (depth : Nat) where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : Hc.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv
  /-- Each cached parameter is the free variable of the matching λ-declaration of the suffix,
  innermost first. -/
  cached : List.Forall₂ (fun (param : Expr) (entry : Option (FVarId × List FVarId) × VLocalDecl) =>
      ∃ fv deps type, param = .fvar fv ∧ entry = (some (fv, deps), .vlam type))
    stats.params.toList.reverse parameterDecls
  /-- The cached parameters translate, in the whole context, to the parameter variables
  (outermost parameter first) beneath the `depth` ambient declarations. -/
  paramsTr : List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) stats.params.toList
    ((List.range stats.params.size).reverse.map fun i => .bvar (depth + i))
  ambient : List VExpr
  ambient_length : ambient.length = depth
  /-- The context converts to the ambient prefix followed by the common parameter telescope. -/
  paramsDefEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (ambient ++ params.reverse) Hc.mlctx.vlctx.toCtx

/-- The loop's cached parameter variables are the parameter variables beneath `depth`
ambient declarations. -/
theorem cachedParamVars_eq_range (n depth : Nat) :
    checkInductiveTypes.loopType.cachedParamVars n depth =
      (List.range n).reverse.map fun i => .bvar (depth + i) := by
  have := checkInductiveTypes.loopType.cachedParamVars_eq_paramVars (depth := depth)
    { uvars := 0, nparams := n, types := [], isUnsafe := false }
  simpa [VInductDecl.paramVars] using this

/-- The interface's parameter context, from the loop's parameter invariants. -/
def HeaderParameterContext.ofLoop {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {params : List VExpr} {depth nparams : Nat}
    (cache : checkInductiveTypes.loopType.ParameterCachePrefix Hc.venv c.lparams
      Hc.mlctx.vlctx stats nparams depth)
    (suffix : checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth)
    (ambient : checkInductiveTypes.loopType.AmbientParamContext Hc params depth)
    (hsize : stats.params.size = nparams) :
    HeaderParameterContext Hc stats params depth where
  ambientDecls := suffix.ambientDecls
  parameterDecls := suffix.parameterDecls
  context := suffix.context
  prefixLength := suffix.prefixLength
  paramFVars := cache.paramFVars
  cached := suffix.cached
  paramsTr := by
    rw [hsize, ← cachedParamVars_eq_range]
    exact cache.params
  ambient := ambient.ambient
  ambient_length := ambient.length
  paramsDefEq := ambient.context

/-- The output of the header traversal, as seen by the continuation `k stats` run in the context
`c'`: `c'` is `c` with the parameters declared, the statistics are the literal ones, and the
headers are checked (`CheckedHeaders`) at a common parameter telescope the context converts to. -/
structure HeaderPhase {c : AddInductive.Context} (Hc : ContextWF c) (nparams : Nat)
    (indTypes : Array InductiveType) (c' : AddInductive.Context) (Hc' : ContextWF c')
    (stats : AddInductive.InductiveStats) where
  env_eq : c'.env = c.env
  safety_eq : c'.safety = c.safety
  lparams_eq : c'.lparams = c.lparams
  allowPrimitive_eq : c'.allowPrimitive = c.allowPrimitive
  fuel_eq : c'.fuel = c.fuel
  venv_eq : Hc'.venv = Hc.venv
  depth : Nat
  commonParams : List VExpr
  commonLevel : VLevel
  headers : CheckedHeaders Hc'.venv c'.lparams nparams commonParams commonLevel indTypes.toList
  levels : stats.levels = c'.lparams.map .param
  nindices_size : stats.nindices.size = indTypes.size
  nindices : stats.nindices.toList = headers.metadata.map Prod.fst
  indConsts : stats.indConsts =
    (indTypes.toList.map fun source => .const source.name stats.levels).toArray
  params_size : stats.params.size = nparams
  commonParams_length : commonParams.length = nparams
  parameters : HeaderParameterContext Hc' stats commonParams depth
  commonLevel_eq : VLevel.ofLevel c'.lparams stats.resultLevel = some commonLevel
  isNotZero : stats.isNotZero = stats.resultLevel.isNeverZero
  /-- The loop's own accumulator, from which `headers` is read (`headers_eq`). -/
  loopHeaders : checkInductiveTypes.loopType.CheckedHeaders Hc'.venv c'.lparams nparams
    commonParams commonLevel indTypes.toList
  headers_eq : headers = CheckedHeaders.ofLoop loopHeaders
  /-- The loop's parameter cache: the cached parameters translate to the parameter variables
  beneath the `depth` ambient declarations. -/
  cache : checkInductiveTypes.loopType.ParameterCachePrefix Hc'.venv c'.lparams
    Hc'.mlctx.vlctx stats nparams depth
  /-- The loop's parameter suffix of the main context. -/
  suffix : checkInductiveTypes.loopType.ParameterContextSuffix Hc' stats depth
  /-- The loop's conversion of the context to the ambient prefix and the common parameters. -/
  ambientParams : checkInductiveTypes.loopType.AmbientParamContext Hc' commonParams depth

/-- The boundary theorem of the header phase: `checkInductiveTypes` satisfies `Q` if its
continuation does in every context and statistics the traversal can produce (`HeaderPhase`). -/
theorem AddInductive.checkInductiveTypes.WF
    {c : AddInductive.Context} {indTypes : Array InductiveType} {nparams : Nat} {α : Type}
    (k : AddInductive.InductiveStats → AddInductive.M α) (Q : α → Prop)
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = []) (hnonempty : 0 < indTypes.size)
    (Hfinish : ∀ {c' : AddInductive.Context} {stats : AddInductive.InductiveStats}
      (Hc' : ContextWF c'), HeaderPhase Hc nparams indTypes c' Hc' stats → (k stats c').WF Q) :
    (AddInductive.checkInductiveTypes nparams indTypes k c).WF Q := by
  apply checkInductiveTypes.loopInd.checkInductiveTypes.accumulatesHeadersSourceAligned
    k Q Hc hctx hnonempty consumeTypeAnnotationsCompat
  intro c' stats depth commonParams commonLevel Hc' henv hsafety hlparams hallow hfuel hvenv
    Hloop _hlevelsLength hlevels hnindicesSize hnindices _hconstsSize hconsts _hconstsNonempty
    hparams hcommonParams Hcache Hsuffix Hambient hcommon hnotzero
  exact Hfinish Hc' {
    env_eq := henv
    safety_eq := hsafety
    lparams_eq := hlparams
    allowPrimitive_eq := hallow
    fuel_eq := hfuel
    venv_eq := hvenv
    depth := depth
    commonParams := commonParams
    commonLevel := commonLevel
    headers := CheckedHeaders.ofLoop Hloop
    levels := hlevels
    nindices_size := hnindicesSize
    nindices := by rw [CheckedHeaders.ofLoop_metadata]; exact hnindices
    indConsts := hconsts
    params_size := hparams
    commonParams_length := hcommonParams
    parameters := .ofLoop Hcache Hsuffix Hambient hparams
    commonLevel_eq := hcommon
    isNotZero := hnotzero
    loopHeaders := Hloop
    headers_eq := rfl
    cache := Hcache
    suffix := Hsuffix
    ambientParams := Hambient }

end VerifyInductive
end Lean4Lean
