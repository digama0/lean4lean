import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Whnf
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructorTypes

/-! # Discharging the non-`whnf` parameter-uniformity inputs of a nested run

The `NestedRun` part of the declaration facts (the generic part is `Uniform/Heads.lean`): name
prefixes; `NestedRun.auxHeadsFacts` (the
auxiliary heads are fresh in the source environment, lie in the reserved `_nested` namespace,
and contain every key of `aux2nested`); the lowering mappings of the lowered families
(`NestedRun.loweredFamilyMappings`), the parameter uniformity of the lowered constructor types
(`NestedRun.constructorTypesParamUniform`) and the totality of `Restoration.expr` on the
normalized constructor types (`NestedRun.normalizedTotal_of`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open InductiveSignature

namespace VerifyInductive

open Kernel

private def nameDepth' : Name → Nat
  | .anonymous => 0
  | .str p _ => nameDepth' p + 1
  | .num p _ => nameDepth' p + 1

private theorem NamePrefix.depth_le' {P x : Name} (H : NamePrefix P x) :
    nameDepth' P ≤ nameDepth' x := by
  induction H with
  | refl => exact Nat.le_refl _
  | str _ _ ih => simp only [nameDepth']; omega
  | num _ _ ih => simp only [nameDepth']; omega

theorem NamePrefix.trans {Q A B : Name} (h₁ : NamePrefix Q A) (h₂ : NamePrefix A B) :
    NamePrefix Q B := by
  induction h₂ with
  | refl => exact h₁
  | str s _ ih => exact .str s ih
  | num k _ ih => exact .num k ih

/-- Replacing a prefix `P` of `x` by `A` yields a name with prefix `A`. -/
theorem NamePrefix.replacePrefix_prefix {P x : Name} (H : NamePrefix P x) (A : Name) :
    NamePrefix A (x.replacePrefix P A) := by
  induction H with
  | refl => rw [Name.replacePrefix_self]; exact .refl
  | @str p s H ih =>
    have hne : Name.str p s ≠ P := by
      intro h; have := H.depth_le'; rw [← h] at this; simp [nameDepth'] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkStr]
    exact .str s ih
  | @num p k H ih =>
    have hne : Name.num p k ≠ P := by
      intro h; have := H.depth_le'; rw [← h] at this; simp [nameDepth'] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkNum]
    exact .num k ih

theorem NamePrefix.isPrefixOf {P x : Name} (H : NamePrefix P x) : P.isPrefixOf x = true := by
  induction H with
  | refl => cases P <;> simp [Name.isPrefixOf]
  | str s _ ih => simp [Name.isPrefixOf, ih]
  | num k _ ih => simp [Name.isPrefixOf, ih]

theorem namePrefix_of_isPrefixOf {P : Name} :
    ∀ {x : Name}, P.isPrefixOf x = true → NamePrefix P x
  | .anonymous, h => by
    simp only [Name.isPrefixOf, beq_iff_eq] at h
    subst h; exact .refl
  | .str p s, h => by
    simp only [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .str s (namePrefix_of_isPrefixOf h)
  | .num p k, h => by
    simp only [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .num k (namePrefix_of_isPrefixOf h)

/-! ### Run-level facts about the auxiliary heads -/

/-- **The auxiliary heads of a validated nested run** are fresh in the
source environment (and in the environment extended by the source family
headers), lie in the reserved `_nested` namespace, and contain every key of
the `aux2nested` map of the lowering result. The lowered family and recursor names are
moreover pairwise distinct. -/
theorem NestedRun.auxHeadsFacts
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∃ envTypes : VEnv,
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      (∀ name ∈ E.auxHeads, envTypes.constants name = none) ∧
      (∀ name ∈ E.auxHeads,
        (ves.venv (if isUnsafe then .unsafe else .safe)).constants name = none) ∧
      (∀ name ∈ E.auxHeads, (`_nested).isPrefixOf name = true) ∧
      (∀ c nested, result.aux2nested.find? c = some nested → c ∈ E.auxHeads) ∧
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoring wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      _hparamsSize, D, _Hrestoring⟩
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hheadNames : auxiliaries.flatMap (·.headNames) = E.auxHeads :=
    auxiliarySpecializations_headNames Haux Hexpansion
  have hfresh : ∀ name ∈ E.auxHeads, envTypes.constants name = none := by
    intro name hname
    apply hfreshAll
    rw [← hheadNames, ← compilationRestoration_heads_auxiliary sourceDecl] at hname
    exact List.mem_append_left _ hname
  rcases E.lowering with ⟨finalState, Hrun, -, -⟩
  have hres := Hrun.resultFamilyNamesReservedOfEmpty rfl
  have hauxRes : ∀ a ∈ auxiliaries, (`_nested).isPrefixOf a.auxiliary = true := by
    intro a ha
    obtain ⟨nested, hfind⟩ := D.familyLookup a ha
    exact hres _ _ hfind
  refine ⟨envTypes, hadded, henvTypes, hfresh,
    fun name hname => (VEnv.addConstVals_le hadded).constants_eq_none_left
      (hfresh name hname), ?_, ?_, hnodup⟩
  · intro name hname
    rw [← hheadNames] at hname
    obtain ⟨a, ha, hn⟩ := List.mem_flatMap.1 hname
    simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨ctor, hctor, rfl⟩
    · exact hauxRes a ha
    · have hP := namePrefix_of_replacePrefix_ne (D.ctorRenamed a ha ctor hctor)
      exact ((namePrefix_of_isPrefixOf (hauxRes a ha)).trans
        (hP.replacePrefix_prefix a.auxiliary)).isPrefixOf
  · intro c nested hfind
    obtain ⟨a, ha, rfl, -⟩ := D.familyKey c nested hfind
    rw [← hheadNames]
    exact List.mem_flatMap.2 ⟨a, ha, by simp [ContainerSpecialization.headNames]⟩

/-! ### Lowered constructor types of a run -/

theorem ConstructorLowerings.Resolved.forall_mem
    {env : Environment} {params : Array Expr} {nparams : Nat}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {sources : List Constructor} {state : Lean4Lean.ElimNestedInductive.State}
    {out : List Constructor × Lean4Lean.ElimNestedInductive.State}
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources state out) :
    ∀ t ∈ out.1, ∃ source ∈ sources, ∃ before after,
      before.lvls = state.lvls ∧
      ConstructorLowering.Resolved env params nparams finalResult source before (t, after) := by
  induction H with
  | nil => intro t ht; simp at ht
  | @cons source state step sources out Hhead Htail ih =>
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨source, List.mem_cons_self, state, step.2, rfl, Hhead⟩
    · obtain ⟨src, hsrc, before, after, hlv, M⟩ := ih t ht
      exact ⟨src, List.mem_cons_of_mem _ hsrc, before, after, hlv.trans Hhead.lvls, M⟩

/-- **Every lowered family of a validated nested run has a lowering
mapping from a pre-lowering family whose constructor types avoid the
auxiliary heads**, at a state carrying the declaration's universe levels.
Source families use the checked source translations; auxiliary families use
the pre-lowering data of the run (`AuxiliaryFamilySources`),
whose constructor types are translated in the environment of the source
headers, where the auxiliary names are fresh. -/
theorem NestedRun.loweredFamilyMappings
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ i (hi : i < result.types.length), ∃ source stepState loweredState,
      (∀ ctor ∈ source.ctors, ctor.type.AvoidsConsts E.auxHeads) ∧
      source.type.AvoidsConsts E.auxHeads ∧
      stepState.lvls = lparams.map Level.param ∧
      FamilyLowering.Resolved sourceProdEnv result.params nparams result source stepState
        (result.types[i], loweredState) := by
  obtain ⟨envTypes, hadded, _henvTypes, hfreshTypes, hfreshSrc, _hreserved, _hkeys,
    _hnodup⟩ := E.auxHeadsFacts wf Hsources
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
  have HsourceCore := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at HsourceCore
  have htypesEq : E.sourceCore.envTypes = envTypes :=
    Option.some.inj (HsourceCore.typesAdded.symm.trans hadded)
  have hfreshN : ∀ name ∈ E.auxHeads, E.sourceCore.envTypes.constants name = none := by
    rw [htypesEq]; exact hfreshTypes
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  have hinitLvls : initialState.lvls = lparams.map Level.param := by
    simp only [initialState, NestedRun.initialState, E.lowered_lparams]
  have hfreshInit : ∀ name ∈ E.auxHeads, P.Hc'.venv.constants name = none := by
    rw [hinitial]; exact hfreshSrc
  suffices key : ∀ i (hi : i < result.types.length), ∃ source stepState loweredState,
      (∀ ctor ∈ source.ctors, ctor.type.AvoidsConsts E.auxHeads) ∧
      source.type.AvoidsConsts E.auxHeads ∧
      stepState.lvls = lparams.map Level.param ∧
      FamilyLowering.Resolved P.c.env result.params nparams result source stepState
        (result.types[i], loweredState) by
    intro i hi
    obtain ⟨source, st, ls, h1, h0, h2, M⟩ := key i hi
    rw [henv, hnparams] at M
    exact ⟨source, st, ls, h1, h0, h2, M⟩
  intro i hi
  by_cases hsrc : i < sourceTypes.length
  · have hj : i < ({ initialState with newTypes := sourceTypes.toArray }).newTypes.size := by
      simpa using hsrc
    rcases Hrun.resolvedMappingAtInitialAlignedLvls
        (Hrun.resultNamesNodupOfEmpty (by simpa using hempty)) hj with
      ⟨params, stepState, target, loweredState, hresultParams,
        _hsize, Hmapping, htarget, hstepLvls⟩
    subst hresultParams
    have htargetEq : target = result.types[i] := by
      rw [List.getElem?_eq_getElem hi] at htarget
      exact (Option.some.inj htarget).symm
    subst htargetEq
    have hsrcDecl : i < sourceDecl.types.length := by
      rw [← TrInductDeclCore.types_length Hsource]; exact hsrc
    have HT := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource i hsrc hsrcDecl
    refine ⟨_, stepState, loweredState, ?_,
      checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshInit HT.header.type,
      hstepLvls.trans hinitLvls, Hmapping⟩
    intro ctor hctor
    have hctor' : ctor ∈ sourceTypes[i].ctors := by simpa using hctor
    obtain ⟨ctor', -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT.ctors ctor hctor'
    exact checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshN hC.type
  · have hge : sourceTypes.length ≤ i := Nat.le_of_not_gt hsrc
    obtain ⟨k, rfl⟩ : ∃ k, i = sourceTypes.length + k := ⟨i - sourceTypes.length, by omega⟩
    have hgeneratedLength := N.length
    have hgen : k < N.generated.length := by omega
    have htarget : sourceTypes.length + k < P.loweredDecl.types.length := by omega
    rcases N.sourceAt k hgen hi htarget with ⟨Horigin, Nsource, -⟩
    have Hmap := Hrun.resultAuxMapModelsOfEmpty (by simpa using hempty)
    have M := Horigin.lowered.resolvedMapping Horigin.later Hmap
    have hlv : Horigin.stepState.lvls = lparams.map Level.param :=
      ((Horigin.lowered.nestedAuxLE.lvls.symm.trans Horigin.later.lvls.symm).trans
        Hrun.lvls).trans hinitLvls
    refine ⟨Horigin.source, Horigin.stepState, Horigin.loweredState, ?_,
      checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshInit
        Nsource.translation.header.type, hlv, M⟩
    intro ctor hctor
    obtain ⟨ctor', -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      Nsource.translation.ctors ctor hctor
    exact checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshN hC.type

/-- **Lowered constructor types of a validated nested run are parameter-uniform
parameter telescopes** for the auxiliary heads, at the lowered run's
parameter count and levels. -/
theorem NestedRun.constructorTypesParamUniform
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ i, i < result.types.toArray.size → ∀ ctor ∈ result.types.toArray[i]!.ctors,
      Expr.ParamUniformTele E.auxHeads E.lowered.stats.params.size
        E.lowered.stats.levels ctor.type := by
  obtain ⟨-, -, -, -, -, -, hkeys, -⟩ := E.auxHeadsFacts wf Hsources
  have hmaps := E.loweredFamilyMappings wf Hsources
  have hnp : result.nparams = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    exact Hrun.resultNParams
  rw [E.statsLevels, E.statsParamsSize, hnp]
  intro i hi ctor hctor
  have hi' : i < result.types.length := by simpa using hi
  have hget : result.types.toArray[i]! = result.types[i] := by
    simp [getElem!_pos result.types.toArray i hi]
  rw [hget] at hctor
  obtain ⟨source, st, ls, havoid, -, hlv, M⟩ := hmaps i hi'
  obtain ⟨src, hsrc, before, after, hbefore, Mc⟩ := M.constructors.forall_mem ctor hctor
  exact Mc.paramUniformTele hkeys (havoid src hsrc) (hbefore.trans hlv)

/-! ### Totality of restoration on the normalized constructor types -/

/-- **Restoration is total on the normalized constructor types of a
validated nested run** (source and auxiliary families alike), for every
specialisation list whose head names are the run's auxiliary family and
constructor names. This gives the `normalizedTotal` field of
`LoweredConstructorsRestore` (used by `NestedRun.compilationData_of_tables`). -/
theorem NestedRun.normalizedTotal_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheadNames : auxiliaries.flatMap (·.headNames) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)) :
    ∀ normalized ∈ E.lowered.signature.declaration.types,
      ∀ ctor ∈ normalized.ctors, ∃ restored,
        (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored := by
  obtain ⟨-, -, -, -, hfreshSrc, hreserved, -, -⟩ := E.auxHeadsFacts wf Hsources
  have hfresh : ∀ name ∈ E.auxHeads, E.lowered.Hc'.venv.constants name = none := by
    rw [E.lowered_initialEnv]; exact hfreshSrc
  have hN := E.lowered.recursorConstruction.normalizedHeadsApplied
    (E.constructorTypesParamUniform wf Hsources)
    (fun l => avoidsConsts_lit_of_reserved hreserved l)
    (E.lowered.recursorConstruction.paramsFree_of_fresh hfresh)
  have Hsource := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at Hsource
  have hnp : E.lowered.stats.params.size = sourceDecl.nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    rw [E.statsParamsSize, Hrun.resultNParams, Hsource.nparams]
  have hlv : E.lowered.stats.levels.length = sourceDecl.uvars := by
    rw [E.statsLevels, List.length_map, Hsource.uvars]
  have hheads : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.auxiliary ∈ E.auxHeads ∧ h.uvars = sourceDecl.uvars ∧
        h.nparams = sourceDecl.nparams := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.1 hh
    obtain ⟨hu, hn, -, -⟩ := ContainerSpecialization.mem_heads hh
    refine ⟨?_, hu, hn⟩
    show h.auxiliary ∈ familyNames _
    rw [← hheadNames]
    refine List.mem_flatMap.2 ⟨a, ha, ?_⟩
    rw [← ContainerSpecialization.heads_map_auxiliary a sourceDecl.uvars sourceDecl.nparams]
    exact List.mem_map_of_mem hh
  intro normalized hn ctor hc
  have hA := hN normalized hn ctor hc
  rw [hnp, hlv] at hA
  exact hA.restorationExpr _ hheads


end VerifyInductive
end Lean4Lean
