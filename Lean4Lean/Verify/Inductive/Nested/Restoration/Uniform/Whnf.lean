import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Run
/-! # `whnf` preserves parameter uniformity in a nested run (owner: Restoration-A)

The `NestedRun` sections of the source branch's `Nested/Restoration/Uniform/Whnf.lean`: the
production facts of the lowered run, the checker's head set `E.uniformHeads`, the lowered
constructor types, `NestedRun.envParamUniform` (`EnvParamUniform` of the recursor pass's
environment) and the resulting `WhnfPreservesParamUniform`. The generic lemmas are in
`Uniform/Generic.lean` and `Uniform/Base.lean`.

Present so far: the lookups of the recursor pass's environment (`LoweredView.ctorEnv_find_cases`,
`fresh_familyNames`), the head set `NestedRun.uniformHeads`, and the run-environment lemmas that
read only `NestedRun`. Pending on Restoration-B's `NestedRun.auxHeadsFacts` inputs
(`ContainerSpecializations`) and `restorationTablesRestoring`: `NestedRun.ctorTypes_headType`,
`generatedFamilyType_forall`, `uniformHeads_fresh`, `familyType_headType`, `envParamUniform`.
The source's `LoweredRun.nonprimitive_familyNames` is the premise `LoweredView.Nonprimitive`
(the target's lowered run does not record its `checkName`s). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive


/-! ### The environment of the recursor pass -/

section Production

private theorem mem_zipWith_left {f : α → β → γ} :
    ∀ {as : List α} {bs : List β} {x : γ}, x ∈ List.zipWith f as bs → ∃ a ∈ as, ∃ b, x = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, x, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, rfl⟩
    · obtain ⟨a', ha', b', rfl⟩ := mem_zipWith_left h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', rfl⟩

theorem mem_inductiveTypeInfos {stats : AddInductive.InductiveStats} {numParams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {lparams : List Name} {info : InductiveVal}
    (h : info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
      isUnsafe lparams).toList) :
    ∃ indType ∈ indTypes.toList, info.name = indType.name ∧ info.type = indType.type ∧
      info.levelParams = lparams := by
  simp only [AddInductive.inductiveTypeInfos, Array.toList_zipWith] at h
  obtain ⟨indType, hmem, _, rfl⟩ := mem_zipWith_left h
  exact ⟨indType, hmem, rfl, rfl, rfl⟩

theorem ConstructorListEntries.entryInfo {mkInfo : Nat → Constructor → ConstructorVal}
    {start : Nat} {ctors : List Constructor} {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorListEntries mkInfo start ctors entries) {entry : ConstantInfo × VConstVal}
    (hentry : entry ∈ entries) :
    ∃ ctor ∈ ctors, ∃ k, entry.1 = .ctorInfo (mkInfo k ctor) := by
  induction H with
  | nil => simp at hentry
  | cons _ ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact ⟨_, List.mem_cons_self, _, rfl⟩
    · obtain ⟨c, hc, k, he⟩ := ih htail
      exact ⟨c, List.mem_cons_of_mem _ hc, k, he⟩

theorem ConstructorTypeEntries.entryInfo
    {mkInfo : InductiveType → Nat → Constructor → ConstructorVal}
    {owners : List InductiveType} {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorTypeEntries mkInfo owners entries) {entry : ConstantInfo × VConstVal}
    (hentry : entry ∈ entries) :
    ∃ owner ∈ owners, ∃ ctor ∈ owner.ctors, ∃ k, entry.1 = .ctorInfo (mkInfo owner k ctor) := by
  induction H with
  | nil => simp at hentry
  | cons Hhead _ ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · obtain ⟨ctor, hctor, k, he⟩ := Hhead.entryInfo hhead
      exact ⟨_, List.mem_cons_self, ctor, hctor, k, he⟩
    · obtain ⟨owner, howner, ctor, hctor, k, he⟩ := ih htail
      exact ⟨owner, List.mem_cons_of_mem _ howner, ctor, hctor, k, he⟩

theorem AddConstants.entryNonprimitive
    (H : AddConstants safety env venv entries outEnv outVEnv)
    {entry : ConstantInfo × VConstVal} (hentry : entry ∈ entries) :
    ¬ Kernel.Environment.primitives.contains entry.1.name := by
  induction H with
  | nil => simp at hentry
  | cons _ hnprim _ _ _ _ _ ih =>
    rcases List.mem_cons.1 hentry with rfl | htail
    · exact hnprim
    · exact ih htail

variable {outEnv : Environment} (P : LoweredView outEnv)

theorem LoweredView.headerMapWF : P.headerEnv.constants.WF :=
  P.constructors.headers.context.checking.map_wf

theorem LoweredView.ctorMapWF : P.ctorEnv.constants.WF :=
  P.constructors.context.checking.tr.map_wf

/-- The kernel headers carry the declaration's family names. -/
theorem LoweredView.infoNames :
    P.constructors.headers.infos.map (·.name) = P.loweredDecl.types.map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.1.2) P.constructors.headers.trHeaders

/-- The kernel constructors carry the declaration's constructor names. -/
theorem LoweredView.ctorNames :
    (P.constructors.ivals.flatMap (·.2)).map (·.name) =
      (P.loweredDecl.types.flatMap (·.ctors)).map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.1.2)
    (List.Forall₂.flatMap (fun _ _ h => h.ctors) P.constructors.trTypes)

theorem LoweredView.namesNodup :
    (P.loweredDecl.types.map (·.name) ++
      (P.loweredDecl.types.flatMap (·.ctors)).map (·.name)).Nodup := by
  have h := TrInductDeclCore.sourceNames_nodup P.constructors.core
  simpa [VInductDecl.sourceNames, VInductDecl.typeConstants, VInductDecl.constructorConstants,
    List.map_map, Function.comp_def, List.map_flatMap] using h

theorem LoweredView.infoCis_nodup :
    ((P.constructors.headers.infos.map ConstantInfo.inductInfo).map (·.name)).Nodup := by
  have : (P.constructors.headers.infos.map ConstantInfo.inductInfo).map (·.name) =
      P.constructors.headers.infos.map (·.name) := by simp only [List.map_map]; rfl
  rw [this, P.infoNames]
  exact (List.nodup_append.mp P.namesNodup).1

theorem LoweredView.ctorCis_nodup :
    ((P.constructors.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo).map
      (·.name)).Nodup := by
  have : (P.constructors.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo).map (·.name) =
      (P.constructors.ivals.flatMap (·.2)).map (·.name) := by
    simp only [List.map_flatMap, List.map_map]; rfl
  rw [this, P.ctorNames]
  exact (List.nodup_append.mp P.namesNodup).2.1

theorem LoweredView.infoCis_fresh (hwf : P.c.env.constants.WF) :
    ∀ ci ∈ P.constructors.headers.infos.map ConstantInfo.inductInfo,
      P.c.env.constants.find? ci.name = none := by
  intro ci hci
  obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hci
  have := P.constructors.headers.fresh info hinfo
  rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at this

theorem LoweredView.ctorCis_fresh :
    ∀ ci ∈ P.constructors.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo),
      P.headerEnv.constants.find? ci.name = none := by
  intro ci hci
  obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
  have := P.constructors.fresh iv hiv cval hcval
  rwa [Lean.Kernel.Environment.find?, P.headerMapWF.find?'_eq_find?] at this

/-- **Lookups in the constructor-phase environment** (where the recursor pass
runs): either a base constant, an installed family header, or an installed
constructor. -/
theorem LoweredView.ctorEnv_find_cases (hwf : P.c.env.constants.WF)
    {n : Name} {ci : ConstantInfo} (h : P.ctorEnv.find? n = some ci) :
    P.c.env.find? n = some ci ∨
      (∃ indType ∈ P.indTypes.toList, ∃ info : InductiveVal, ci = .inductInfo info ∧
        n = indType.name ∧ info.type = indType.type ∧ info.levelParams = P.c.lparams) ∨
      (∃ owner ∈ P.indTypes.toList, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
        ci = .ctorInfo info ∧ n = ctor.name ∧ info.type = ctor.type ∧
        info.levelParams = P.c.lparams) := by
  rw [Lean.Kernel.Environment.find?, P.ctorMapWF.find?'_eq_find?,
    P.constructors.map_eq] at h
  rcases insertConsts_find? P.headerMapWF P.ctorCis_fresh P.ctorCis_nodup h with
    hH | ⟨hci, hname⟩
  · rw [P.constructors.headers.map_eq] at hH
    rcases insertConsts_find? hwf (P.infoCis_fresh hwf) P.infoCis_nodup hH with
      h0 | ⟨hci, hname⟩
    · left; rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    · obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hci
      rw [P.constructors.headers.infos_eq] at hinfo
      obtain ⟨indType, hmem, hn, ht, hl⟩ := mem_inductiveTypeInfos hinfo
      exact .inr (.inl ⟨indType, hmem, info, rfl, hname.symm.trans hn, ht, hl⟩)
  · obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hci
    obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
    rw [P.constructors.ivals_eq] at hiv
    obtain ⟨⟨info, owner⟩, hp, rfl⟩ := List.mem_map.mp hiv
    have howner : owner ∈ P.indTypes.toList := (List.of_mem_zip hp).2
    obtain ⟨k, ctor, hctor, rfl⟩ := mem_ctorInfosFrom hcval
    exact .inr (.inr ⟨owner, howner, ctor, hctor, _, rfl, hname.symm, rfl, rfl⟩)

/-- A constant of the constructor-phase environment absent from the base environment is a
family or constructor name of the installed declaration. -/
theorem LoweredView.ctorEnv_new_name (hwf : P.c.env.constants.WF)
    {n : Name} {ci : ConstantInfo} (h : P.ctorEnv.find? n = some ci)
    (hold : P.c.env.find? n = none) :
    n ∈ InductiveSignature.familyNames P.loweredDecl.types := by
  rw [Lean.Kernel.Environment.find?, P.ctorMapWF.find?'_eq_find?,
    P.constructors.map_eq] at h
  have hmemNames : n ∈ P.loweredDecl.types.map (·.name) ++
      (P.loweredDecl.types.flatMap (·.ctors)).map (·.name) := by
    rcases insertConsts_find? P.headerMapWF P.ctorCis_fresh P.ctorCis_nodup h with
      hH | ⟨hci, hname⟩
    · rw [P.constructors.headers.map_eq] at hH
      rcases insertConsts_find? hwf (P.infoCis_fresh hwf) P.infoCis_nodup hH with
        h0 | ⟨hci, hname⟩
      · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, h0] at hold; cases hold
      · obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hci
        refine List.mem_append_left _ ?_
        rw [← P.infoNames, ← hname]
        exact List.mem_map_of_mem hinfo
    · obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hci
      obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
      refine List.mem_append_right _ ?_
      rw [← P.ctorNames, ← hname]
      exact List.mem_map_of_mem (List.mem_flatMap.mpr ⟨iv, hiv, hcval⟩)
  rcases List.mem_append.mp hmemNames with hn | hn
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
    exact List.mem_flatMap.mpr ⟨t, ht, List.mem_cons_self⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨t, ht, List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩

/-- Every family and constructor name of the installed declaration is fresh
in the environment before installation. -/
theorem LoweredView.fresh_familyNames (hwf : P.c.env.constants.WF)
    {n : Name} (hn : n ∈ InductiveSignature.familyNames P.loweredDecl.types) :
    P.c.env.find? n = none := by
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  rcases List.mem_cons.1 hn with rfl | hctor
  · have hv : t.name ∈ P.constructors.headers.infos.map (·.name) := by
      rw [P.infoNames]; exact List.mem_map_of_mem ht
    obtain ⟨info, hinfo, hname⟩ := List.mem_map.1 hv
    rw [← hname]; exact P.constructors.headers.fresh info hinfo
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hctor
    have hv : c.name ∈ (P.constructors.ivals.flatMap (·.2)).map (·.name) := by
      rw [P.ctorNames]; exact List.mem_map_of_mem (List.mem_flatMap.2 ⟨t, ht, hc⟩)
    obtain ⟨cval, hcval, hname⟩ := List.mem_map.1 hv
    obtain ⟨iv, hiv, hcval⟩ := List.mem_flatMap.1 hcval
    have hfreshH := P.constructors.fresh iv hiv cval hcval
    rw [← hname]
    cases h0 : P.c.env.find? cval.name with
    | none => rfl
    | some found =>
      have h0' : P.c.env.constants.find? cval.name = some found := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h0
      have := insertConsts_find?_mono_of_fresh hwf.map₂ (P.infoCis_fresh hwf) h0'
      rw [← P.constructors.headers.map_eq] at this
      rw [Lean.Kernel.Environment.find?, P.headerMapWF.find?'_eq_find?, this] at hfreshH
      cases hfreshH

/-- The family and constructor names of the lowered declaration are not checker primitives:
they passed `checkName` without primitive permission (`NestedRun.context_allowPrimitive`).
-- WAVE 3 restA: a premise of the instances below (`NestedRun.envParamUniform`), produced
by the nested run. -/
def LoweredView.Nonprimitive : Prop :=
  ∀ n ∈ InductiveSignature.familyNames P.loweredDecl.types,
    ¬ Kernel.Environment.primitives.contains n

/-- A constant of the constructor-phase environment that is not a base
constant was installed by the run, hence is not a reserved primitive name. -/
theorem LoweredView.ctorEnv_new_nonprimitive (hnprim : P.Nonprimitive)
    (hwf : P.c.env.constants.WF)
    {n : Name} {ci : ConstantInfo} (h : P.ctorEnv.find? n = some ci)
    (hold : P.c.env.find? n = none) :
    ¬ Kernel.Environment.primitives.contains n :=
  hnprim n (P.ctorEnv_new_name hwf h hold)

end Production

/-- The checker's own primitive constants are reserved names. -/
theorem checkerPrimNames_primitive : ∀ n ∈ checkerPrimNames, Kernel.Environment.primitives.contains n := by
  intro n hn
  simp only [checkerPrimNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  simp only [Kernel.Environment.primitives, NameSet.ofList]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [NameSet.contains]

/-! ### The head set of a nested run -/

section Heads

/-- In a duplicate-free list of family names, no family name is a constructor
name. -/
theorem familyName_not_mem_ctorNames :
    ∀ {L : List VInductiveType}, (InductiveSignature.familyNames L).Nodup →
      ∀ t ∈ L, t.name ∉ L.flatMap (fun t => t.ctors.map (·.name))
  | [], _, _, h => by simp at h
  | t0 :: L, hnd, t, ht => by
    simp only [InductiveSignature.familyNames, List.flatMap_cons] at hnd
    have hnd' := List.nodup_append.1 hnd
    have hL : (InductiveSignature.familyNames L).Nodup := hnd'.2.1
    have hsub : ∀ x ∈ L.flatMap (fun t => t.ctors.map (·.name)),
        x ∈ InductiveSignature.familyNames L := by
      intro x hx
      obtain ⟨t', ht', hx⟩ := List.mem_flatMap.1 hx
      exact List.mem_flatMap.2 ⟨t', ht', List.mem_cons_of_mem _ hx⟩
    simp only [List.flatMap_cons, List.mem_append, not_or]
    rcases List.mem_cons.1 ht with rfl | ht
    · refine ⟨fun h => (List.nodup_cons.1 hnd'.1).1 h, fun h => ?_⟩
      exact hnd'.2.2 _ List.mem_cons_self _ (hsub _ h) rfl
    · refine ⟨fun h => ?_, familyName_not_mem_ctorNames hL t ht⟩
      exact hnd'.2.2 _ (List.mem_cons_of_mem _ h) _
        (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩) rfl

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}

/-- The constructor names of the source families of a nested run. Their
lowered types mention auxiliary families, so they are heads of the type
checker's parameter-uniformity invariant. -/
def NestedRun.mainCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  (E.lowered.loweredDecl.types.take sourceDecl.types.length).flatMap
    fun t => t.ctors.map (·.name)

/-- The head set of the type checker's parameter-uniformity invariant at the recursor
pass: the auxiliary families and constructors together with the source
constructors. -/
def NestedRun.uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  E.auxHeads ++ E.mainCtorNames

theorem NestedRun.uniformHeads_subset
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) {n : Name}
    (hn : n ∈ E.uniformHeads) :
    n ∈ InductiveSignature.familyNames E.lowered.loweredDecl.types := by
  rcases List.mem_append.1 hn with hn | hn
  · exact familyNames_drop_subset hn
  · obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
    exact List.mem_flatMap.2 ⟨t, List.mem_of_mem_take ht, List.mem_cons_of_mem _ hn⟩

theorem NestedRun.auxHeads_subset_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ c ∈ E.auxHeads, c ∈ E.uniformHeads := fun _ h => List.mem_append_left _ h

/-- Every lowered constructor name is a head. -/
theorem NestedRun.ctorName_mem_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {t : VInductiveType} (ht : t ∈ E.lowered.loweredDecl.types)
    {c : VConstVal} (hc : c ∈ t.ctors) : c.name ∈ E.uniformHeads := by
  have hsplit := List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types
  rw [← hsplit] at ht
  rcases List.mem_append.1 ht with ht | ht
  · exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨t, ht, List.mem_map_of_mem hc⟩)
  · exact List.mem_append_left _
      (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩)

/-- A source family name is not a head. -/
theorem NestedRun.mainFamily_not_mem_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup)
    {t : VInductiveType} (ht : t ∈ E.lowered.loweredDecl.types.take sourceDecl.types.length) :
    t.name ∉ E.uniformHeads := by
  have hsplit := List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types
  have hnd := hnodup
  rw [← hsplit, InductiveSignature.familyNames, List.flatMap_append] at hnd
  have hnd' := List.nodup_append.1 hnd
  intro hmem
  rcases List.mem_append.1 hmem with hmem | hmem
  · exact hnd'.2.2 _ (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩) _ hmem rfl
  · exact familyName_not_mem_ctorNames hnd'.1 t ht hmem

end Heads

/-! ### Lowered constructor types are head types -/

section CtorTypes

/-- The lowering of a constructor closes its opened parameters with
`LocalContext.mkForall`, so its type is a head type. -/
theorem ConstructorLowering.Resolved.headType {heads : List Name} {ls : List Level}
    {env : Environment} {params : Array Expr} {nparams : Nat}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {source : Constructor} {state : Lean4Lean.ElimNestedInductive.State}
    {out : Constructor × Lean4Lean.ElimNestedInductive.State}
    (H : ConstructorLowering.Resolved env params nparams finalResult source state out)
    (hkeys : ∀ auxName nested, finalResult.aux2nested.find? auxName = some nested →
      auxName ∈ heads)
    (hsource : source.type.AvoidsConsts heads) (hlvls : state.lvls = ls) :
    HeadType heads nparams ls out.1.type := by
  obtain ⟨lctx, tail, As, lowered, openedState, Hopen, -, Hselection, hnodup, -, -, -,
    hsize, Hmap, htype⟩ := H.mapped
  have hopenedLvls : openedState.lvls = ls := by
    rw [← Hmap.lvls, H.lvls, hlvls]
  have Hlowered := Hmap.paramUniform hkeys (Hopen.tailAvoidsConsts hsource) hopenedLvls
  rw [htype, ← hsize]
  refine Expr.ParamUniform.mkForall_headType Hlowered
    (by have h := congrArg Array.toList Hselection.expressions; simpa using h)
    hnodup fun x hx => ?_
  obtain ⟨index, name, type, bi, kind, hfind⟩ := Hselection.declarations x hx
  exact ⟨index, x, name, type, bi, kind, hfind⟩

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The constructor names of the lowered declaration are absent from the
environment in which its constructor types are translated (the source
environment extended by the lowered family headers). -/
theorem NestedRun.ctorNames_fresh_headerVEnv
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    (hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup)
    {t : VInductiveType} (ht : t ∈ E.lowered.loweredDecl.types)
    {c : VConstVal} (hc : c ∈ t.ctors) :
    E.lowered.headers.context.venv.constants c.name = none := by
  have hcore := E.lowered.constructors.core
  have hadded := hcore.typesAdded
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c, E.context_env]; exact (wf.tr (safety := .unsafe)).map_wf
  have hfreshK : E.lowered.c.env.find? c.name = none :=
    E.lowered.fresh_familyNames hwfP
      (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩)
  have hne : ∀ ci ∈ E.lowered.loweredDecl.typeConstants, ci.name ≠ c.name := by
    intro ci hci heq
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hci
    exact familyName_not_mem_ctorNames hnodup t' ht'
      (by rw [show t'.toVConstVal.name = t'.name from rfl] at heq; rw [heq]
          exact List.mem_flatMap.2 ⟨t, ht, List.mem_map_of_mem hc⟩)
  rw [VEnv.addConstVals_constants_of_forall_ne hadded hne]
  cases hv : E.lowered.initialEnv.constants c.name with
  | none => rfl
  | some ci =>
    exfalso
    rw [E.lowered_initialEnv] at hv
    obtain ⟨ci', hfind, -⟩ :=
      (wf.tr (safety := if isUnsafe then .unsafe else .safe)).find?_iff.2 ⟨ci, hv⟩
    rw [E.lowered_c, E.context_env] at hfreshK
    rw [hfreshK] at hfind; cases hfind

theorem LeadingForalls.mkForall_selection {lctx : LocalContext} {As : Array Expr}
    (S : CDeclArray lctx As) (b : Expr) :
    Expr.LeadingForalls As.size (lctx.mkForall As b) (b.abstractN S.fvars) := by
  obtain ⟨fvars, hAs, hdecl⟩ := S
  subst hAs
  simp only [LocalContext.mkForall, List.size_toArray, List.length_map]
  rw [LocalContext.mkBinding_eqN]
  exact Expr.LeadingForalls.mkBindingListN (fun x hx => by
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl x hx
    exact ⟨index, x, name, type, bi, kind, hfind⟩) b

end CtorTypes

/-! ### The environment condition at the recursor pass -/

section RunEnv

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The recursor pass runs in the constructor-phase environment. -/
theorem NestedRun.recursorPassEnv
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    E.lowered.recursors.localContext.env = E.lowered.ctorEnv :=
  E.lowered.recursors.localExtends.env_eq

theorem NestedRun.lowered_c_env
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    E.lowered.c.env = sourceProdEnv := by
  rw [E.lowered_c, E.context_env]

theorem NestedRun.lowered_c_lparams
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    E.lowered.c.lparams = lparams := by
  rw [E.lowered_c, E.context_lparams]

/-- Lookups of base constants persist into the constructor-phase environment. -/
theorem NestedRun.ctorEnv_preserves
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) {n : Name} {ci : ConstantInfo}
    (h : sourceProdEnv.find? n = some ci) : E.lowered.ctorEnv.find? n = some ci := by
  have := wf
  rw [← E.lowered_c_env] at h
  exact E.lowered.constructors.sourcePres h

/-- Family header types are translated in the source environment. -/
theorem NestedRun.familyType_tr
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {owner : InductiveType} (howner : owner ∈ E.lowered.indTypes.toList) :
    ∃ e', TrExprS (ves.venv (if isUnsafe then .unsafe else .safe)) lparams [] owner.type e' := by
  obtain ⟨t, -, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    E.lowered.constructors.core.types owner howner
  have h := HT.header.type
  rw [E.lowered_initialEnv, E.lowered_c_lparams] at h
  exact ⟨_, h⟩

/-- Constructor types are translated in the header environment, and their
names are lowered constructor names. -/
theorem NestedRun.ctorType_tr
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {owner : InductiveType} (howner : owner ∈ E.lowered.indTypes.toList)
    {ctor : Constructor} (hctor : ctor ∈ owner.ctors) :
    (∃ e', TrExprS E.lowered.headers.context.venv E.lowered.c.lparams [] ctor.type e') ∧
      ∃ t ∈ E.lowered.loweredDecl.types, ∃ c ∈ t.ctors, c.name = ctor.name := by
  obtain ⟨t, ht, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    E.lowered.constructors.core.types owner howner
  obtain ⟨c', hc', HC⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT.ctors ctor hctor
  exact ⟨⟨_, HC.type⟩, t, ht, c', hc', HC.name⟩

end RunEnv

end VerifyInductive
end Lean4Lean
