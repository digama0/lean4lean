import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Declarations

/-! # The environment condition at the recursor pass of a nested run

The parameter-uniformity facts that read `NestedRun.auxHeadsFacts`: the lowered constructor types
are head types for the run's head set, the heads are fresh in the source model, the family types are
head types, and `NestedRun.envParamUniform`: `EnvParamUniform` of the recursor pass's environment.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- **Every lowered constructor type is a head type for the run's head set**
(before level instantiation). -/
theorem NestedRun.ctorTypes_headType
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ owner ∈ result.types.toArray.toList, ∀ ctor ∈ owner.ctors,
      HeadType E.uniformHeads nparams (lparams.map Level.param) ctor.type := by
  obtain ⟨-, -, -, -, -, -, hkeys, hnodupAll⟩ := E.auxHeadsFacts wf Hsources
  have hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup :=
    (List.nodup_append.1 hnodupAll).1
  have hmaps := E.loweredFamilyMappings wf Hsources
  intro owner howner ctor hctor
  -- head type for the auxiliary heads
  have hAux : HeadType E.auxHeads nparams (lparams.map Level.param) ctor.type := by
    have howner' : owner ∈ result.types := by
      simpa using howner
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 howner'
    obtain ⟨source, st, ls, havoid, -, hlv, M⟩ := hmaps i hi
    obtain ⟨src, hsrc, before, after, hbefore, Mc⟩ := M.constructors.forall_mem ctor hctor
    exact Mc.headType hkeys (havoid src hsrc) (hbefore.trans hlv)
  -- the constructor type avoids the source constructor names
  have hcore := E.lowered.constructors.core
  obtain ⟨t, ht, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_l hcore.types owner howner
  obtain ⟨c', hc', HC⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT.ctors ctor hctor
  have hfresh : ∀ n ∈ E.mainCtorNames, E.lowered.headers.context.venv.constants n = none := by
    intro n hn
    obtain ⟨t'', ht'', hn⟩ := List.mem_flatMap.1 hn
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.1 hn
    exact E.ctorNames_fresh_headerVEnv wf hnodup (List.mem_of_mem_take ht'') hc''
  have havoid : ctor.type.AvoidsConsts E.mainCtorNames :=
    checkPositivityStep.TrExprS.sourceAvoidsFresh hfresh HC.type
  exact hAux.grow (E.auxHeads_subset_uniformHeads) (fun c hc hnot => by
    rcases List.mem_append.1 hc with h | h
    · exact absurd h hnot
    · exact h) havoid


/-- **Auxiliary family types are parameter telescopes**: the
lowering builds them as `LocalContext.mkForall As _` over the `nparams`
lowering parameters. -/
theorem NestedRun.generatedFamilyType_forall
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ i (hi : i < result.types.length), sourceTypes.length ≤ i →
      ∃ body, Expr.LeadingForalls nparams result.types[i].type body := by
  obtain ⟨-, -, -, -, -, -, -, hparamsSize, -, -⟩ := E.restorationTablesRestoring wf Hsources
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : nparams = nparams := rfl
  have hinitial : P.Hc'.venv = ves.venv safety := by
    simpa only [safety] using E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  let initialState := E.initialState
  have Hlower : NestedLoweringOutputClosed P.c.env
      E.validationFuel.inductiveFuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hpack := E.lowered
  let R := Hpack.constructors
  have Hsource : TrInductDeclCore P.Hc'.venv P.c.lparams nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [hinitial, hlparams, hisUnsafe, safety,
      E.sourceCoreDecl_eq] using E.sourceCore.core
  have Htarget : TrInductDeclCore P.Hc'.venv P.c.lparams nparams
      result.types P.isUnsafe P.loweredDecl R.headers.context.venv
        R.ctorVEnv := by
    simpa using R.core
  have wfP : ves.WF P.c.env := by
    simpa only [henv] using wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.Hc'.venv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.sourceCore.sourceHeaders
  have HsourceAdded : P.Hc'.venv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    simpa only [hinitial, safety] using E.sourceCore.sourceAdded
  have HbaseWF : P.Hc'.venv.WF := by
    simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource HbaseWF
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := rfl
  rcases Hrun.auxiliaryFamilySources (R := R) Hcache Hparams wfP
      hinitial HcP Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, -⟩
  intro i hi hge
  obtain ⟨k, rfl⟩ : ∃ k, i = sourceTypes.length + k := ⟨i - sourceTypes.length, by omega⟩
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  have hgeneratedLength := N.length
  have hgen : k < N.generated.length := by omega
  have htarget : sourceTypes.length + k < P.loweredDecl.types.length := by omega
  rcases N.sourceAt k hgen hi htarget with ⟨Horigin, -, -⟩
  obtain ⟨tail, -, htype⟩ := Horigin.generated.built.opening
  have hT : result.types[sourceTypes.length + k].type =
      Horigin.generated.data.type.type := by
    rw [Horigin.lowered.type]; exact congrArg InductiveType.type Horigin.generated.family_eq
  rw [hT, htype]
  have hsize : Horigin.generated.As.size = nparams := by
    rw [Horigin.generated.built.arity, hparamsSize, Hrun.resultNParams, hnparams]
  have hl := LeadingForalls.mkForall_selection Horigin.generated.selection
    (tail.instantiateRevRange 0 Horigin.generated.nestedNParams Horigin.generated.args)
  rw [hsize] at hl
  exact ⟨_, hl⟩


/-- The heads are absent from the source kernel environment. -/
theorem NestedRun.uniformHeads_fresh
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) :
    ∀ n ∈ E.uniformHeads, sourceProdEnv.find? n = none := by
  intro n hn
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c_env]; exact (wf.tr (safety := .unsafe)).map_wf
  have := E.lowered.fresh_familyNames hwfP (E.uniformHeads_subset hn)
  rwa [E.lowered_c_env] at this


/-- A family of the run whose name is a head is an auxiliary family, so its
type is a head type. -/
theorem NestedRun.familyType_headType
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {owner : InductiveType} (howner : owner ∈ result.types.toArray.toList)
    (hname : owner.name ∈ E.uniformHeads) :
    HeadType E.uniformHeads nparams (lparams.map Level.param) owner.type := by
  obtain ⟨-, -, -, -, -, -, -, hnodupAll⟩ := E.auxHeadsFacts wf Hsources
  have hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup :=
    (List.nodup_append.1 hnodupAll).1
  have hcore := E.lowered.constructors.core
  have hlen := Lean4Lean.List.Forall₂.length_eq hcore.types
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 howner
  have hiD : i < E.lowered.loweredDecl.types.length := by omega
  have HT := Lean4Lean.List.forall₂_getElem hcore.types i hi hiD
  have hsrcLen : sourceTypes.length = sourceDecl.types.length := by
    have := TrInductDeclCore.types_length E.sourceCore.core
    rwa [E.sourceCoreDecl_eq] at this
  have hge : sourceTypes.length ≤ i := by
    refine Nat.le_of_not_gt fun hlt => E.mainFamily_not_mem_uniformHeads hnodup
      (t := E.lowered.loweredDecl.types[i]) ?_ ?_
    · rw [List.mem_iff_getElem]
      refine ⟨i, ?_, ?_⟩
      · rw [List.length_take]; omega
      · rw [List.getElem_take]
    · have hn : E.lowered.loweredDecl.types[i].name = result.types.toArray.toList[i].name :=
        HT.header.name
      rw [hn]; exact hname
  have hres : result.types.toArray.toList = result.types := by
    simp
  have hiR : i < result.types.length := by rw [← hres]; exact hi
  obtain ⟨body, hl⟩ := E.generatedFamilyType_forall wf Hsources i hiR hge
  have heq : result.types.toArray.toList[i] = result.types[i] := List.getElem_of_eq hres hi
  obtain ⟨e', htr⟩ := E.familyType_tr (List.getElem_mem hi)
  rw [heq] at htr ⊢
  have havoid : result.types[i].type.AvoidsConsts E.uniformHeads :=
    avoids_of_tr wf (E.uniformHeads_fresh wf) _ htr
  exact ⟨body, hl, Expr.ParamUniformBV.of_avoidsConsts (hl.avoidsConsts havoid) 0⟩


/-- **The environment condition of the type checker's parameter-uniformity invariant
holds in the environment of the recursor pass** of a validated nested
run, for the head set `E.uniformHeads` (auxiliary families and constructors, and
the source constructors), `nparams` parameters and the declaration's level
parameters.

The constants the checker builds on its own are not heads: the reserved ones
(`checkerPrimNames`) because every head was installed by a `checkName` without
primitive permission (`LoweredRun.nonprimitive_familyNames`);
the other string-literal constants (`strLitNames`) because, once the
environment declares `Char.ofNat` and `String.ofList`, these two are base
constants (they are reserved, so the run did not install them), and then
`HasPrimitives` of the source model forces `String`, `Char`, `List.nil` and
`List.cons` to be base constants as well, while every head is fresh
(`uniformHeads_fresh`). -/
theorem NestedRun.envParamUniform
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    EnvParamUniform E.lowered.ctorEnv E.uniformHeads nparams (lparams.map Level.param) := by
  have hfresh := E.uniformHeads_fresh wf
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.lowered.ctorEnv.find? n = some ci := E.ctorEnv_preserves wf
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c_env]; exact (wf.tr (safety := .unsafe)).map_wf
  have horigin : ∀ {n ci}, E.lowered.ctorEnv.find? n = some ci →
      sourceProdEnv.find? n = some ci ∨
      (∃ indType ∈ result.types.toArray.toList, ∃ info : InductiveVal,
        ci = .inductInfo info ∧ n = indType.name ∧ info.type = indType.type ∧
        info.levelParams = lparams) ∨
      (∃ owner ∈ result.types.toArray.toList, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
        ci = .ctorInfo info ∧ n = ctor.name ∧ info.type = ctor.type ∧
        info.levelParams = lparams) := by
    intro n ci h
    have := E.lowered.ctorEnv_find_cases hwfP h
    rwa [E.lowered_c_env, E.lowered_c_lparams] at this
  have hfreshN : ∀ {n ci}, sourceProdEnv.find? n = some ci → n ∉ E.uniformHeads :=
    fun h hn => by rw [hfresh _ hn] at h; cases h
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hheaderV : E.lowered.headers.context.venv.OrderedStrong :=
    E.lowered.headers.context.checking.wf.orderedStrong
  have hheaderSub : ∀ s info, E.lowered.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.lowered.constructors.core.typesAdded,
      E.lowered_initialEnv] at h
    exact ⟨info, h⟩
  refine {
    prims := ?prims
    strs := ?strs
    type_avoids := ?type_avoids
    value_avoids := ?value_avoids
    rules_avoid := ?rules_avoid
    head_kind := ?head_kind
    head_type := ?head_type
    rec_major := ?rec_major
    type_projs := ?type_projs
    value_projs := ?value_projs
    rules_projs := ?rules_projs }
  case prims =>
    intro n hn hmem
    exact E.loweredNonprimitive _ (E.uniformHeads_subset hmem)
      (checkerPrimNames_primitive n hn)
  case strs =>
    rintro ⟨⟨ci₁, h₁⟩, ⟨ci₂, h₂⟩⟩ n hn hmem
    have hold : ∀ {p ci}, Kernel.Environment.primitives.contains p →
        E.lowered.ctorEnv.find? p = some ci → ∃ ci', sourceProdEnv.find? p = some ci' := by
      intro p ci hp h
      cases h0 : sourceProdEnv.find? p with
      | some ci' => exact ⟨ci', rfl⟩
      | none =>
        refine absurd hp (E.lowered.ctorEnv_new_nonprimitive E.loweredNonprimitive hwfP h ?_)
        rw [E.lowered_c_env]; exact h0
    obtain ⟨_, hc₁⟩ := hold (checkerPrimNames_primitive _ (by simp [checkerPrimNames])) h₁
    obtain ⟨_, hc₂⟩ := hold (checkerPrimNames_primitive _ (by simp [checkerPrimNames])) h₂
    have htr := wf.tr (safety := .unsafe)
    obtain ⟨_, hv₁, -⟩ := htr.find? hc₁ DefinitionSafety.unsafe_le
    obtain ⟨_, hv₂, -⟩ := htr.find? hc₂ DefinitionSafety.unsafe_le
    have hord : (ves.venv .unsafe).OrderedStrong := htr.wf.orderedStrong
    have hprimU : (ves.venv .unsafe).HasPrimitives := wf.hasPrimitives (safety := .unsafe)
    have hlits : (ves.venv .unsafe).ContainsLits (.strVal "") := ⟨⟨_, hv₁⟩, ⟨_, hv₂⟩⟩
    have hcontains : (ves.venv .unsafe).contains n := by
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | hn
      · obtain ⟨_, H⟩ := (TrExprS.trLiteral hord hprimU (.strVal "") hlits
          (Us := []) (Δ := [])).2.isType hord trivial
        obtain ⟨_, h1, -⟩ := H.const_inv hord trivial
        exact ⟨_, h1⟩
      · exact unreservedLiteralConstructorsOfStringOfList hprimU hord hlits.2 n
          (by simpa [checkPositivityStep.unreservedLiteralConstructorNames] using hn)
    obtain ⟨_, hfind, -⟩ := htr.find?_iff.2 hcontains
    rw [hfresh n hmem] at hfind; cases hfind
  case type_avoids =>
    intro n ci h hn
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, -⟩
    · exact (old_type_avoids wf hfresh hold).1
    · show info.type.AvoidsConsts _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact avoids_of_tr wf hfresh _ htr
    · exfalso
      obtain ⟨-, t, ht, c, hc, hcn⟩ := E.ctorType_tr howner hctor
      exact hn (hcn ▸ E.ctorName_mem_uniformHeads ht hc)
  case value_avoids =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact (old_value_avoids wf hfresh hold hv).1
    · cases hv
    · cases hv
  case rules_avoid =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact (old_rules_avoid wf hfresh hold hrule).1
    · cases heq
    · cases heq
  case head_kind =>
    intro n ci h hn
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact absurd hn (hfreshN hold)
    · exact .inl ⟨info, rfl⟩
    · exact .inr ⟨info, rfl⟩
  case head_type =>
    intro n ci h hn
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, hlp⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, hlp⟩
    · exact absurd hn (hfreshN hold)
    · show HeadType _ _ _ (info.type.instantiateLevelParams info.levelParams _)
      rw [htype, hlp]
      exact (E.familyType_headType wf Hsources hmem hn).instantiateLevelParams_self
    · show HeadType _ _ _ (info.type.instantiateLevelParams info.levelParams _)
      rw [htype, hlp]
      exact (E.ctorTypes_headType wf Hsources owner howner ctor hctor).instantiateLevelParams_self
  case rec_major =>
    intro n r h
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact old_rec_major wf hpres hfresh hold
    · cases heq
    · cases heq
  case type_projs =>
    intro n ci h
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -, htype, -⟩
    · obtain ⟨e', htr⟩ := (old_type_avoids wf hfresh hold).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.orderedStrong
        (fun s i h => ⟨i, h⟩) htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
      exact projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr
  case value_projs =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · obtain ⟨e', htr⟩ := (old_value_avoids wf hfresh hold hv).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases hv
    · cases hv
  case rules_projs =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · obtain ⟨e', htr⟩ := (old_rules_avoid wf hfresh hold hrule).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases heq
    · cases heq


/-- **`whnf` preserves parameter uniformity in a validated nested run**, at the head
set `E.uniformHeads` (auxiliary families and constructors, and the source
constructors), the run's parameters and the declaration's levels, in the
environment of the recursor pass. -/
theorem NestedRun.whnfPreservesParamUniform
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    WhnfPreservesParamUniform E.uniformHeads E.lowered.stats.params.toList (lparams.map Level.param)
      E.lowered.recursors.localContext.env := by
  refine .of_env ?_ E.paramsUngeneratedParams
  have hlen : E.lowered.stats.params.toList.length = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    rw [Array.length_toList, E.statsParamsSize, Hrun.resultNParams]
  rw [E.recursorPassEnv, hlen]
  exact E.envParamUniform wf Hsources

/-- **The non-`whnf` parameter-uniformity inputs of a validated nested run**, at the
head set `E.uniformHeads`, with the projection condition at the environment of the
recursor pass, derived from the run alone:

* parameter declarations: translated in the source environment, where the
  heads are fresh and every registered projection names a base structure
  (`RecursorConstruction.paramDecls_paramUniformIn`, `projParamUniformIn_of_old`);
* family headers: translated in the source environment
  (`NestedRun.familyType_tr`);
* constructor types: head types for `E.uniformHeads`
  (`NestedRun.ctorTypes_headType`), translated in the header
  environment, whose projections are the source environment's;
* recursor names: distinct from the family and constructor names. -/
theorem NestedRun.paramUniformDeclarations_of
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    E.lowered.recursors.toRecursorConstruction.ParamUniformDeclarations
      E.uniformHeads := by
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hfresh := E.uniformHeads_fresh wf
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.lowered.recursors.toRecursorConstruction.localContext.env.find?
        n = some ci := by
    intro n ci h
    have := E.ctorEnv_preserves wf h
    rw [← E.recursorPassEnv] at this
    exact this
  obtain ⟨-, -, -, -, -, -, -, hnodup⟩ := E.auxHeadsFacts wf Hsources
  have hnp : result.nparams = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    exact Hrun.resultNParams
  have hheaderV : E.lowered.headers.context.venv.OrderedStrong :=
    E.lowered.headers.context.checking.wf.orderedStrong
  have hheaderSub : ∀ s info, E.lowered.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.lowered.constructors.core.typesAdded,
      E.lowered_initialEnv] at h
    exact ⟨info, h⟩
  have hmem : ∀ i, i < result.types.toArray.size →
      result.types.toArray[i]! ∈ result.types.toArray.toList := by
    intro i hi
    rw [getElem!_pos result.types.toArray i hi]
    exact Array.getElem_mem_toList hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine E.lowered.recursors.toRecursorConstruction.paramDecls_paramUniformIn
      (fun n hn => ?_) (fun s info h => ?_)
    · rw [E.lowered_initialEnv]
      cases hc : (ves.venv sf).constants n with
      | none => rfl
      | some ci =>
        obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨ci, hc⟩
        rw [hfresh n hn] at hfind; cases hfind
    · rw [E.lowered_initialEnv] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
        (wf.tr (safety := sf)).wf.ordered.projectionShape h
      obtain ⟨ci, hci, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨_, hlookup⟩
      exact projParamUniformIn_of_old wf hpres hfresh hci
  · intro i hi
    obtain ⟨e', htr⟩ := E.familyType_tr (hmem i hi)
    exact ⟨avoids_of_tr wf hfresh _ htr,
      projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.orderedStrong
        (fun s i h => ⟨i, h⟩) htr⟩
  · intro i hi ctor hctor
    obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr (hmem i hi) hctor
    refine ⟨?_, projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr⟩
    obtain ⟨body, hl, hb⟩ := E.ctorTypes_headType wf Hsources _ (hmem i hi) ctor hctor
    rw [E.statsLevels, E.statsParamsSize, hnp]
    exact ⟨body, hl.leadingBinders, hb⟩
  · exact E.lowered.recursors.toRecursorConstruction.recursorNames_not_mem
      (fun _ hh => E.uniformHeads_subset hh) hnodup

/-- **Parameter uniformity of the lowered recursor type and rule right-hand sides of a
validated nested run, at the checker's head set `E.uniformHeads`**:
`recursorParamUniform` with its two hypotheses discharged by
`paramUniformDeclarations_of` and `whnfPreservesParamUniform`. -/
theorem NestedRun.recursorParamUniform_uniformHeads
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.ParamUniformTele E.uniformHeads result.nparams (lparams.map Level.param)
        Hstep.oldInfo.type ∧
      ∀ rule ∈ Hstep.oldInfo.rules,
        Expr.ParamUniformTele E.uniformHeads result.nparams (lparams.map Level.param) rule.rhs :=
  E.recursorParamUniform (E.paramUniformDeclarations_of wf Hsources) (E.whnfPreservesParamUniform wf Hsources)
    owner Hstep

/-- **Parameter uniformity of the lowered recursor type and rule right-hand sides of a
validated nested run**, at the auxiliary heads `E.auxHeads`: for every
generated owner and every executable restoration step at the owner's lowered
recursor name, the stored recursor type and every stored rule right-hand side
are closed parameter telescopes of `result.nparams` binders whose body is
parameter-uniform in bound-variable form for the auxiliary heads at the levels
`lparams.map Level.param`.

The proof runs the parameter-uniformity chain at the checker's head set `E.uniformHeads`
(`recursorParamUniform_uniformHeads`) and drops the source constructors with
`ParamUniformTele.shrink`. -/
theorem NestedRun.recursorParamUniform_of_wfCore
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.ParamUniformTele E.auxHeads result.nparams (lparams.map Level.param)
        Hstep.oldInfo.type ∧
      ∀ rule ∈ Hstep.oldInfo.rules,
        Expr.ParamUniformTele E.auxHeads result.nparams (lparams.map Level.param) rule.rhs := by
  obtain ⟨htype, hrules⟩ := E.recursorParamUniform_uniformHeads wf Hsources owner Hstep
  exact ⟨htype.shrink E.auxHeads_subset_uniformHeads,
    fun rule hrule => (hrules rule hrule).shrink E.auxHeads_subset_uniformHeads⟩


end VerifyInductive
end Lean4Lean
