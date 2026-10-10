import Lean4Lean.Verify.Inductive.Header.Declare

/-! # Header installation: `declareInductiveTypes`

After the header traversal, `AddInductive.declareInductiveTypes` adds the kernel headers
(`inductiveTypeInfos`) to the environment, one checked name at a time. `HeaderEnvironment` is
the frozen interface of the resulting environment, indexed by the abstract declaration `decl`
the constructor phase will select (only its header data is constrained here);
`AddInductive.declareInductiveTypes.WF` is the boundary theorem.

Wave 2 scaffold: owned by the `Header/`+`Context/`+`Formation` agent (source branch:
`Header/{Declaration,Installation}.lean`, `Install/Headers.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The environment after `declareInductiveTypes`: the kernel headers are installed over the
source environment (`map_eq`, `fresh`), each translating to the abstract type former of `decl`
(`trHeaders`, the header half of `TrIndType`); the abstract header environment is the source
model with `decl`'s type constants (`typesAdded`); the parameters are still declared in the
context (`parameters`). -/
structure HeaderEnvironment (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  numNested : Nat
  /-- The kernel headers, exactly the executable's `inductiveTypeInfos`. -/
  infos : List InductiveVal
  infos_eq : infos = (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
    isUnsafe c.lparams).toList
  map_eq : outEnv.constants = insertConsts c.env.constants (infos.map .inductInfo)
  quotInit_eq : outEnv.quotInit = c.env.quotInit
  fresh : ∀ info ∈ infos, c.env.find? info.name = none
  uvars : decl.uvars = c.lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  /-- The source context and the context over the header environment share the main local
  context (the parameters). -/
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  context : ContextWF { c with env := outEnv }
  contextMLCtx : context.mlctx = sourceContext.mlctx
  typesAdded : sourceEnv.addConstVals decl.typeConstants = some context.venv
  headers : HeaderCertificate sourceEnv decl
  /-- Each kernel header translates to the abstract type former and lists the declaration's
  constructor names (the header half of `TrIndType`). -/
  trHeaders : List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
      TrConstVal c.safety sourceEnv (.inductInfo info) t.toVConstVal ∧
      info.ctors = t.ctors.map (·.name))
    infos decl.types
  /-- The source family types translate to the abstract type formers. -/
  trSources : List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
      TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
      source.ctors.map (·.name) = t.ctors.map (·.name))
    indTypes.toList decl.types
  parameters : HeaderParameterContext context stats headers.params depth
  sourceParameters : HeaderParameterContext sourceContext stats headers.params depth
  /-- Every constructor a header of the source environment lists is present there. -/
  sourcePresent : ListedConstructorsPresent c.env
  /-- The header statistics of the header phase (`HeaderStatsWF`: the normalized source
  telescope and semantic shape of every family, and the parameter scope) over the source
  environment ... -/
  sourceStatsWF : checkInductiveTypes.loopInd.HeaderStatsWF sourceContext.venv c.lparams
    sourceContext.mlctx.vlctx stats decl depth
  sourceHeaderParams : sourceStatsWF.headers.params = headers.params
  /-- ... and over the header environment. -/
  statsWF : checkInductiveTypes.loopInd.HeaderStatsWF context.venv c.lparams
    context.mlctx.vlctx stats decl depth
  headerParams : statsWF.headers.params = headers.params
  parameterScopeEq : statsWF.parameterScope = sourceStatsWF.parameterScope

/-- The constructor names of a declaration are absent from an environment. The header
environment is a checking environment (`CheckingEnv.Valid`: a header lists only absent names or
its own constructors) only once the constructor names are known to be absent from it; the
executable checks this only when it declares the constructors, after checking their types, so
the constructor phase reads it off a successful `declareConstructors`
(`AddInductive.declareConstructors.namesAbsent`). -/
def ConstructorNamesAbsent (indTypes : Array InductiveType) (env : Environment) : Prop :=
  ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors, env.find? ctor.name = none

/-- The constructor fold of `declareConstructors` succeeds only on names absent from every
environment it extends. -/
theorem AddInductive.declareConstructors.ctorFoldAbsent
    (allowPrimitive : Bool) (mk : Nat → Constructor → ConstantInfo)
    (hmk : ∀ i ctor, (mk i ctor).name = ctor.name) (base : Environment) :
    ∀ (ctors : List Constructor) (cidx : Nat) (env : Environment), env.constants.WF →
      (∀ {n x}, base.find? n = some x → env.find? n = some x) →
      (ctors.foldlM (init := (cidx, env)) fun (state : Nat × Environment)
          (ctor : Constructor) => do
        let (cidx, env) := state
        env.checkName ctor.name allowPrimitive
        pure (cidx + 1, env.add (mk cidx ctor))).WF fun r =>
        r.2.constants.WF ∧ (∀ {n x}, base.find? n = some x → r.2.find? n = some x) ∧
        ∀ ctor ∈ ctors, base.find? ctor.name = none
  | [], _, _, hwf, hsub => Except.WF.pure ⟨hwf, hsub, by simp⟩
  | ctor :: ctors, cidx, env, hwf, hsub => by
    rw [List.foldlM_cons]
    refine Except.WF.bind (Q := fun r => r.2.constants.WF ∧
        (∀ {n x}, base.find? n = some x → r.2.find? n = some x) ∧
        base.find? ctor.name = none) ?_ fun r ⟨hwf', hsub', habs⟩ => ?_
    · refine (checkName.WF hwf ctor.name allowPrimitive).bind fun _ ⟨hn, _⟩ => ?_
      have hn' : env.find? (mk cidx ctor).name = none := by rw [hmk]; exact hn
      have hnMap : env.constants.find? (mk cidx ctor).name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn'
      refine Except.WF.pure ⟨?_, ?_, ?_⟩
      · change (env.constants.insert (mk cidx ctor).name (mk cidx ctor)).WF
        exact hwf.insert _ _ hnMap
      · intro n x h
        exact findAddFresh_of_find hwf _ hn' (hsub h)
      · cases hb : base.find? ctor.name with
        | none => rfl
        | some x => rw [hsub hb] at hn; cases hn
    · exact (ctorFoldAbsent allowPrimitive mk hmk base ctors r.1 r.2 hwf' hsub').mono
        fun r' ⟨h1, h2, h3⟩ => ⟨h1, h2, by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact habs
          · exact h3 c hc⟩

/-- `declareConstructors` succeeds only when every constructor name is absent from the
environment it starts from. -/
theorem AddInductive.declareConstructors.namesAbsent
    {c : AddInductive.Context} (hwf : c.env.constants.WF) :
    (AddInductive.declareConstructors stats indTypes isUnsafe c).WF fun _ =>
      ConstructorNamesAbsent indTypes c.env := by
  let mk := fun (owner : InductiveType) (cidx : Nat) (ctor : Constructor) =>
    ConstantInfo.ctorInfo (AddInductive.constructorInfo stats c.lparams isUnsafe owner cidx ctor)
  have outer : ∀ (owners : List InductiveType) (env : Environment), env.constants.WF →
      (∀ {n x}, c.env.find? n = some x → env.find? n = some x) →
      (owners.foldlM (init := env) fun (env : Environment) (owner : InductiveType) => do
        let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
            (state : Nat × Environment) (ctor : Constructor) => do
          let (cidx, env) := state
          env.checkName ctor.name c.allowPrimitive
          pure (cidx + 1, env.add (mk owner cidx ctor))
        pure env).WF fun _ =>
        ∀ owner ∈ owners, ∀ ctor ∈ owner.ctors, c.env.find? ctor.name = none := by
    intro owners
    induction owners with
    | nil => intro _ _ _; exact Except.WF.pure (by simp)
    | cons owner owners ih =>
      intro env hwf hsub
      rw [List.foldlM_cons]
      refine Except.WF.bind (Q := fun env' : Environment => env'.constants.WF ∧
            (∀ {n x}, c.env.find? n = some x → env'.find? n = some x) ∧
            ∀ ctor ∈ owner.ctors, c.env.find? ctor.name = none) ?_ fun env' h => ?_
      · exact Except.WF.bind (AddInductive.declareConstructors.ctorFoldAbsent
          c.allowPrimitive (mk owner) (by intros; rfl) c.env owner.ctors 0 env hwf hsub)
          fun ⟨_, _⟩ h => Except.WF.pure h
      · rcases h with ⟨hwf', hsub', habs⟩
        exact (ih env' hwf' hsub').mono fun _ h o ho ctor hctor => by
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact habs ctor hctor
          · exact h o ho ctor hctor
  rw [AddInductive.declareConstructors, ← Array.foldlM_toList]
  exact outer indTypes.toList c.env hwf id

/-! ## Reading the kernel headers and the described declaration -/

/-- The kernel headers, family by family. -/
theorem inductiveTypeInfos_getElem (stats : AddInductive.InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) (lparams : List Name)
    (hsize : stats.nindices.size = indTypes.size) :
    (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
      lparams).toList.length = indTypes.toList.length ∧
    ∀ i (hi : i < indTypes.toList.length) (hi' : i < (AddInductive.inductiveTypeInfos stats
        nparams indTypes numNested isUnsafe lparams).toList.length),
      let info := (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
        lparams).toList[i]
      info.name = indTypes.toList[i].name ∧ info.type = indTypes.toList[i].type ∧
      info.levelParams = lparams ∧ info.ctors = indTypes.toList[i].ctors.map (·.name) ∧
      info.isUnsafe = isUnsafe := by
  refine ⟨by simp [AddInductive.inductiveTypeInfos, hsize], ?_⟩
  intro i hi hi'
  simp [AddInductive.inductiveTypeInfos]

/-- Every kernel header is the header of a source family. -/
theorem inductiveTypeInfos_mem {stats : AddInductive.InductiveStats} {nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool} {lparams : List Name}
    {info : InductiveVal}
    (h : info ∈ (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
      lparams).toList) :
    ∃ owner ∈ indTypes.toList, info.name = owner.name ∧
      info.ctors = owner.ctors.map (·.name) := by
  simp only [AddInductive.inductiveTypeInfos, Array.toList_zipWith] at h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hi, rfl⟩ := h
  have hi' : i < indTypes.toList.length := by
    simp only [List.length_zipWith] at hi; omega
  simp only [List.getElem_zipWith]
  exact ⟨indTypes.toList[i], List.getElem_mem hi', rfl, rfl⟩

namespace CheckedHeaders

variable {env : VEnv} {Us : List Name} {nparams : Nat} {params : List VExpr}
  {commonLevel : VLevel} {sources : List InductiveType}

theorem Describes.length {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) : decl.types.length = sources.length := by
  rw [← List.Forall₂.length_eq D.2.2, H.payloads_length]

/-- The `i`th family of a described declaration has the header fields of the `i`th payload. -/
theorem Describes.getElem {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) (i : Nat) (hi : i < decl.types.length) :
    ∃ hp : i < H.payloads.length,
      decl.types[i].toVConstVal = H.payloads[i].2.target ∧
      decl.types[i].numIndices = H.payloads[i].2.numIndices ∧
      decl.types[i].resultLevel = H.payloads[i].2.resultLevel ∧
      decl.types[i].ctors.map (·.name) = H.payloads[i].1.ctors.map (·.name) := by
  have hp : i < H.payloads.length := by rw [List.Forall₂.length_eq D.2.2]; exact hi
  have := List.forall₂_getElem D.2.2 i hp hi
  exact ⟨hp, this.1, this.2.1, this.2.2.1, this.2.2.2⟩

theorem payloads_getElem_fst (H : CheckedHeaders env Us nparams params commonLevel sources)
    (i : Nat) (hp : i < H.payloads.length) (hs : i < sources.length) :
    H.payloads[i].1 = sources[i] := by
  have := congrArg (fun l => l[i]?) H.sourceOrder
  simp [hp, hs] at this
  exact this

theorem Describes.typeConstants {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) : decl.typeConstants = H.targets := by
  apply List.ext_getElem
  · simp [VInductDecl.typeConstants, targets, List.Forall₂.length_eq D.2.2]
  · intro i h1 h2
    have hi : i < decl.types.length := by simpa [VInductDecl.typeConstants] using h1
    obtain ⟨hp, ht, -⟩ := D.getElem i hi
    simp [VInductDecl.typeConstants, targets, ht]

/-- The source family types translate to the described type formers. -/
theorem Describes.trSources {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) :
    List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
      TrSourceConst env Us source.name source.type t.toVConstVal ∧
      source.ctors.map (·.name) = t.ctors.map (·.name)) sources decl.types := by
  have go : ∀ {ps : List (Sigma fun source =>
      CheckedHeader env Us nparams params commonLevel source)} {ts : List VInductiveType},
      List.Forall₂ (fun (p : Sigma fun source =>
          CheckedHeader env Us nparams params commonLevel source) (t : VInductiveType) =>
        t.toVConstVal = p.2.target ∧ t.numIndices = p.2.numIndices ∧
        t.resultLevel = p.2.resultLevel ∧ t.ctors.map (·.name) = p.1.ctors.map (·.name)) ps ts →
      List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
        TrSourceConst env Us source.name source.type t.toVConstVal ∧
        source.ctors.map (·.name) = t.ctors.map (·.name)) (ps.map Sigma.fst) ts := by
    intro ps ts h
    induction h with
    | nil => exact .nil
    | @cons p t _ _ h _ ih =>
      refine .cons ⟨?_, h.2.2.2.symm⟩ ih
      rw [h.1]; exact p.2.translation
  have := go D.2.2
  rwa [H.sourceOrder] at this

end CheckedHeaders

/-- The names of the families of a described declaration are the source names. -/
theorem CheckedHeaders.Describes.names {env : VEnv} {Us : List Name} {nparams : Nat}
    {params : List VExpr} {commonLevel : VLevel} {sources : List InductiveType}
    {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) :
    decl.types.map (·.name) = sources.map (·.name) := by
  have go : ∀ {ss : List InductiveType} {ts : List VInductiveType},
      List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
        TrSourceConst env Us source.name source.type t.toVConstVal ∧
        source.ctors.map (·.name) = t.ctors.map (·.name)) ss ts →
      ts.map (·.name) = ss.map (·.name) := by
    intro ss ts h
    induction h with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.name
  exact go D.trSources

/-- The index counts of a described declaration are the checked ones. -/
theorem CheckedHeaders.Describes.numIndices {env : VEnv} {Us : List Name} {nparams : Nat}
    {params : List VExpr} {commonLevel : VLevel} {sources : List InductiveType}
    {H : CheckedHeaders env Us nparams params commonLevel sources}
    {decl : VInductDecl} (D : H.Describes decl) :
    decl.types.map (·.numIndices) = H.metadata.map Prod.fst := by
  have go : ∀ {ps : List (Sigma fun source =>
      CheckedHeader env Us nparams params commonLevel source)} {ts : List VInductiveType},
      List.Forall₂ (fun (p : Sigma fun source =>
          CheckedHeader env Us nparams params commonLevel source) (t : VInductiveType) =>
        t.toVConstVal = p.2.target ∧ t.numIndices = p.2.numIndices ∧
        t.resultLevel = p.2.resultLevel ∧ t.ctors.map (·.name) = p.1.ctors.map (·.name)) ps ts →
      ts.map (·.numIndices) = ps.map fun p => p.2.numIndices := by
    intro ps ts h
    induction h with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, ih, h.2.1]
  simpa [CheckedHeaders.metadata, List.map_map, Function.comp_def] using go D.2.2

/-- The header statistics of the source branch (`HeaderStatsWF`) for every declaration the
checked headers describe: its header certificate, the normalized source telescope and
semantic shape of every family, and the parameter scope of the header phase. -/
def HeaderPhase.statsWF {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) {decl : VInductDecl}
    (D : P.headers.Describes decl) :
    checkInductiveTypes.loopInd.HeaderStatsWF Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl
      P.depth where
  headers := D.headerCertificate
  normalizedSources i hi := by
    obtain ⟨hp, -, hidx, -, -⟩ := D.getElem i hi
    have := (P.headers.payloads[i]).2.formation.normalizedSource
    rw [D.2.1, hidx]
    exact this
  normalizedShapes i hi := by
    obtain ⟨hp, ht, hidx, hlevel, -⟩ := D.getElem i hi
    have := (P.headers.payloads[i]).2.formation.normalizedShape
    have htype : decl.types[i].type = (P.headers.payloads[i]).2.target.type :=
      congrArg (fun v : VConstVal => v.type) ht
    rw [D.2.1, hidx, hlevel, htype]
    exact this
  isNotZero := P.isNotZero
  commonLevel := P.commonLevel_eq
  levels := by rw [P.levels, List.length_map, D.1]
  levelParams := P.levels
  uvars := D.1.symm
  consts := by
    rw [P.indConsts]
    have := congrArg (fun names =>
      (names.map fun name => Expr.const name stats.levels).toArray) D.names
    simpa [List.map_map, Function.comp_def] using this.symm
  indices := by rw [P.nindices, D.numIndices]
  params := by
    have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix Hc'.venv c'.lparams
        Hc'.mlctx.vlctx stats decl.nparams P.depth := by
      rw [D.2.1]; exact P.cache
    exact Hcache.complete
  paramFVars := P.cache.paramFVars
  parameterScope := P.suffix.parameterDecls
  ambientScope := P.suffix.ambientDecls
  scopeDecomposition := P.suffix.context
  ambientLength := P.suffix.prefixLength
  cachedScope := P.suffix.cached
  parameterEmbedding :=
    checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix Hc' P.suffix
  paramsContext := P.suffix.paramsDefEq P.ambientParams
    (P.commonParams_length.trans P.params_size.symm)
  suffixParams := by
    rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
    have hsize : stats.params.size = decl.nparams := P.params_size.trans D.2.1.symm
    simpa [hsize] using P.suffix.suffixParams

@[simp] theorem HeaderPhase.statsWF_headers_params {c c' : AddInductive.Context}
    {Hc : ContextWF c} {nparams : Nat} {indTypes : Array InductiveType} {Hc' : ContextWF c'}
    {stats : AddInductive.InductiveStats} (P : HeaderPhase Hc nparams indTypes c' Hc' stats)
    {decl : VInductDecl} (D : P.headers.Describes decl) :
    (P.statsWF D).headers.params = P.commonParams := rfl

/-- Move a header parameter context to a larger environment over the same local context. -/
def HeaderParameterContext.withEnv {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {params : List VExpr} {depth : Nat}
    (H : HeaderParameterContext Hc stats params depth) {env' : Environment} {venv' : VEnv}
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hshapes : RecursorShapesCoherent c.safety env'.constants venv')
    (hiota : IotaRulesRegistered c.safety env' venv') (hle : Hc.venv ≤ venv') :
    HeaderParameterContext (Hc.withEnv hchecking hshapes hiota hle) stats params depth where
  ambientDecls := H.ambientDecls
  parameterDecls := H.parameterDecls
  context := H.context
  prefixLength := H.prefixLength
  paramFVars := H.paramFVars
  cached := H.cached
  paramsTr := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.mono hle) H.paramsTr
  ambient := H.ambient
  ambient_length := H.ambient_length
  paramsDefEq := H.paramsDefEq.mono hle

/-- The header environment before the declaration is known: the kernel headers
(`inductiveTypeInfos`) are installed over the source environment, the abstract header
environment is the source model with the checked header targets (`typesAdded`), and the
parameters are still declared (`parameters`). The constructor phase checks the constructor
types here, then picks the declaration they translate to
(`InstalledHeaders.toHeaderEnvironment`). -/
structure InstalledHeaders {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (outEnv : Environment) where
  infos : List InductiveVal
  infos_eq : infos = (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
    isUnsafe c'.lparams).toList
  map_eq : outEnv.constants = insertConsts c'.env.constants (infos.map .inductInfo)
  quotInit_eq : outEnv.quotInit = c'.env.quotInit
  fresh : ∀ info ∈ infos, c'.env.find? info.name = none
  context : ContextWF { c' with env := outEnv }
  contextMLCtx : context.mlctx = Hc'.mlctx
  le : Hc'.venv ≤ context.venv
  typesAdded : Hc'.venv.addConstVals P.headers.targets = some context.venv
  /-- Each kernel header translates to its checked target. -/
  trInfos : List.Forall₂ (fun info v =>
      TrConstVal c'.safety Hc'.venv (.inductInfo info) v ∧ v.toVConstant.WF Hc'.venv)
    infos P.headers.targets
  parameters : HeaderParameterContext context stats P.commonParams P.depth
  /-- Every constructor a header of the source environment lists is present there. -/
  sourcePresent : ListedConstructorsPresent c'.env

/-- Header installation, before the declaration is known: `declareInductiveTypes` yields a
well-formed constant map and, once the constructor names are absent from it, the installed
headers. -/
theorem AddInductive.declareInductiveTypes.installedWF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c'.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe c'.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested isUnsafe c').WF
      fun headerEnv => headerEnv.constants.WF ∧
        (ConstructorNamesAbsent indTypes headerEnv →
          Nonempty (InstalledHeaders P numNested isUnsafe headerEnv)) := by
  have hwf := Hc'.checking.tr.map_wf
  have hsize : stats.nindices.size = indTypes.size := P.nindices_size
  obtain ⟨hlen, hget⟩ := inductiveTypeInfos_getElem stats nparams indTypes numNested isUnsafe
    c'.lparams hsize
  let infos := (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
    c'.lparams).toList
  let L := HeaderInstallation.listedNames indTypes
  have hpayloads : P.headers.payloads.length = indTypes.toList.length := P.headers.payloads_length
  have hinfosPayloads : infos.length = P.headers.payloads.length := by
    rw [hpayloads]; exact hlen
  -- the kernel headers translate to the checked targets
  have Hentries : List.Forall₂ (fun info v =>
      TrConstVal c'.safety Hc'.venv (.inductInfo info) v ∧ v.toVConstant.WF Hc'.venv)
      infos P.headers.targets := by
    apply List.forall₂_of_getElem (by simpa [CheckedHeaders.targets] using hinfosPayloads)
    intro i hi hi'
    have hp : i < P.headers.payloads.length := by simpa [CheckedHeaders.targets] using hi'
    have hs : i < indTypes.toList.length := by rw [← hpayloads]; exact hp
    obtain ⟨hname, htype, hlp, -, hunsafe⟩ := hget i hs hi
    have hsrc := P.headers.payloads_getElem_fst i hp hs
    have htr : TrSourceConst Hc'.venv c'.lparams indTypes.toList[i].name indTypes.toList[i].type
        P.headers.payloads[i].2.target := by
      rw [← hsrc]; exact P.headers.payloads[i].2.translation
    simp only [CheckedHeaders.targets, List.getElem_map]
    exact ⟨TrSourceConst.inductInfo htr hlp hname htype (by rw [hunsafe]; exact hvisible),
      htr.wf⟩
  change (AddInductive.declareInductiveTypeInfos c'.allowPrimitive infos c'.env).WF _
  have HS := HeaderInstallation.declareInfos_structural c'.allowPrimitive infos c'.env hwf
  intro out hout
  obtain ⟨hwfOut, hmap, hquot, hfresh, hmono, hself, -⟩ := HS out hout
  refine ⟨hwfOut, fun habsent => ?_⟩
  -- the listed names are absent from the source environment and distinct from the headers
  have hLabs : ∀ n ∈ L, out.find? n = none := by
    intro n hn
    obtain ⟨owner, howner, ctor, hctor, rfl⟩ := HeaderInstallation.mem_listedNames.1 hn
    exact habsent owner howner ctor hctor
  have hL : ∀ n ∈ L, c'.env.find? n = none := by
    intro n hn
    cases h : c'.env.find? n with
    | none => rfl
    | some ci => have := hLabs n hn; rw [hmono h] at this; cases this
  have hnotL : ∀ info ∈ infos, info.name ∉ L := by
    intro info hinfo hmem
    have := hLabs _ hmem
    rw [hself info hinfo] at this
    cases this
  have hsub : ∀ info ∈ infos, ∀ n ∈ info.ctors, n ∈ L := by
    intro info hinfo n hn
    obtain ⟨owner, howner, -, hctors⟩ := inductiveTypeInfos_mem hinfo
    rw [hctors] at hn
    obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.1 hn
    exact HeaderInstallation.mem_listedNames.2 ⟨owner, howner, ctor, hctor, rfl⟩
  have hinv : ∀ fn fi, c'.env.find? fn = some (.inductInfo fi) → ∀ n ∈ fi.ctors,
      (∃ c, c'.env.find? n = some c) ∨ n ∈ L :=
    fun fn fi hfi n hn => .inl (hpresent fn fi hfi n hn)
  obtain ⟨outVEnv, htypes, hle, hV, hS, hI⟩ :=
    HeaderInstallation.declareInfos_valid c'.allowPrimitive L Hc'.venv infos P.headers.targets
      c'.env Hc'.venv Hentries VEnv.LE.rfl Hc'.checking (@Hc'.shapes) (@Hc'.iota) hL hnotL hsub
      hinv hnprim out hout
  exact ⟨{
    infos := infos
    infos_eq := rfl
    map_eq := hmap
    quotInit_eq := hquot
    fresh := hfresh
    context := Hc'.withEnv hV @hS @hI hle
    contextMLCtx := rfl
    le := hle
    typesAdded := htypes
    trInfos := Hentries
    parameters := P.parameters.withEnv hV @hS @hI hle
    sourcePresent := hpresent }⟩

/-- The header environment of a declaration the checked headers describe. -/
def InstalledHeaders.toHeaderEnvironment {c c' : AddInductive.Context} {Hc : ContextWF c}
    {nparams : Nat} {indTypes : Array InductiveType} {Hc' : ContextWF c'}
    {stats : AddInductive.InductiveStats} {P : HeaderPhase Hc nparams indTypes c' Hc' stats}
    {numNested : Nat} {isUnsafe : Bool} {outEnv : Environment}
    (I : InstalledHeaders P numNested isUnsafe outEnv)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    {decl : VInductDecl} (D : P.headers.Describes decl) (hdeclUnsafe : decl.isUnsafe = isUnsafe) :
    HeaderEnvironment c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes outEnv := by
  have hsize : stats.nindices.size = indTypes.size := P.nindices_size
  obtain ⟨hlen, hget⟩ := inductiveTypeInfos_getElem stats nparams indTypes numNested isUnsafe
    c'.lparams hsize
  have htrHeaders : List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
      TrConstVal c'.safety Hc'.venv (.inductInfo info) t.toVConstVal ∧
      info.ctors = t.ctors.map (·.name)) I.infos decl.types := by
    rw [I.infos_eq]
    have hdlen : decl.types.length = indTypes.toList.length := D.length
    apply List.forall₂_of_getElem (by rw [hdlen]; exact hlen)
    intro i hi hi'
    obtain ⟨hp, ht, -, -, hctors⟩ := D.getElem i hi'
    have hs : i < indTypes.toList.length := by rw [← hdlen]; exact hi'
    obtain ⟨hname, htype, hlp, hictors, hunsafe⟩ := hget i hs hi
    have hsrc := P.headers.payloads_getElem_fst i hp hs
    have htr : TrSourceConst Hc'.venv c'.lparams indTypes.toList[i].name indTypes.toList[i].type
        P.headers.payloads[i].2.target := by
      rw [← hsrc]; exact P.headers.payloads[i].2.translation
    rw [ht]
    refine ⟨TrSourceConst.inductInfo htr hlp hname htype (by rw [hunsafe]; exact hvisible), ?_⟩
    rw [hictors, hctors, hsrc]
  let S := P.statsWF D
  exact {
    numNested := numNested
    infos := I.infos
    infos_eq := I.infos_eq
    map_eq := I.map_eq
    quotInit_eq := I.quotInit_eq
    fresh := I.fresh
    uvars := D.1
    nparams := D.2.1
    isUnsafe := hdeclUnsafe
    sourceContext := Hc'
    sourceContextVEnv := rfl
    context := I.context
    contextMLCtx := I.contextMLCtx
    typesAdded := by rw [D.typeConstants]; exact I.typesAdded
    headers := D.headerCertificate
    trHeaders := htrHeaders
    trSources := D.trSources
    parameters := I.parameters
    sourceParameters := P.parameters
    sourcePresent := I.sourcePresent
    sourceStatsWF := S
    sourceHeaderParams := rfl
    statsWF := (S.mono I.le).retargetScope (by rw [I.contextMLCtx])
    headerParams := by simp; rfl
    parameterScopeEq := by simp }

/-- The boundary theorem of header installation: in the context of a completed header phase,
`declareInductiveTypes` yields a well-formed constant map and, once the constructor names are
absent from it, a header environment for every declaration the checked headers describe. -/
theorem AddInductive.declareInductiveTypes.WF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c'.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe c'.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested isUnsafe c').WF
      fun headerEnv => headerEnv.constants.WF ∧
        (ConstructorNamesAbsent indTypes headerEnv → ∀ decl : VInductDecl,
          P.headers.Describes decl → decl.isUnsafe = isUnsafe →
          Nonempty (HeaderEnvironment c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes
            headerEnv)) :=
  (AddInductive.declareInductiveTypes.installedWF P numNested isUnsafe hvisible hnprim
    hpresent).mono fun _ ⟨hwf, H⟩ => ⟨hwf, fun habsent _ D hu =>
      let ⟨I⟩ := H habsent; ⟨I.toHeaderEnvironment hvisible D hu⟩⟩

end VerifyInductive
end Lean4Lean
