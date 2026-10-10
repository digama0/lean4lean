import Lean4Lean.Verify.Inductive.Constructor.Install
import Lean4Lean.Verify.Inductive.Constructor.CheckRun

/-! # The constructor phase: `constructorPhase`

`AddInductive.constructorPhase` installs the headers (`declareInductiveTypes`), checks the
constructors against them (`checkConstructors`) and installs them (`declareConstructors`). Its
output is the constructor environment, the input of the recursor phase. `ConstructorCheck` is the
frozen interface of that environment; `AddInductive.constructorPhase.WF` is the boundary
theorem.

Wave 2 scaffold: owned by the `Constructor/`+`CheckedFormation` agent, who composes the header
agent's `declareInductiveTypes.WF` with their own `checkConstructors` and `declareConstructors`
refinements (source branch: `Constructor/Check.lean`, `Install/{Environments,Formation}.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The constructor check, the input of the recursor phase: the checked formation, the kernel
constructors installed over the header environment (`ivals`, `map_eq`, `fresh`) and translating
to the abstract ones (`trTypes`, PR #43's `TrIndType`, the `types` field of `AddInduct`), and a
valid checking context over the constructor environment with the declaration's projection
entries registered (`context`, `contextVEnv`): the recursors are checked in it. -/
structure ConstructorCheck (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (ctorEnv : Environment) extends
    CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes where
  /-- The kernel headers with their constructors, in block order. -/
  ivals : List (InductiveVal × List ConstructorVal)
  ivals_infos : ivals.map (·.1) = headers.infos
  trTypes : List.Forall₂ (fun (iv : InductiveVal × List ConstructorVal) (t : VInductiveType) =>
    TrIndType c.safety sourceEnv headers.context.venv iv.1 iv.2 t) ivals decl.types
  map_eq : ctorEnv.constants =
    insertConsts headerEnv.constants (ivals.flatMap fun iv => iv.2.map .ctorInfo)
  quotInit_eq : ctorEnv.quotInit = headerEnv.quotInit
  fresh : ∀ iv ∈ ivals, ∀ cval ∈ iv.2, headerEnv.find? cval.name = none
  /-- The checking context of the recursor phase: the constructor environment with the
  declaration's projection entries registered (the recursors are checked there). -/
  context : ContextWF { c with env := ctorEnv }
  contextVEnv : context.venv = ctorVEnv.addProjections decl.projectionEntries
  contextMLCtx : context.mlctx = headers.context.mlctx
  parameters : HeaderParameterContext context stats formation.headers.params depth
  closed : MutualInductivesClosed ctorEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants ctorEnv.constants decl
  constructorParameterAlignment : ∀ {safety},
    ConstructorParameterAlignment safety c.env sourceEnv →
    ConstructorParameterAlignment safety ctorEnv ctorVEnv
  /-- (Added by the constructor agent.) The kernel headers with their constructors are the
  executable's `inductiveTypeInfos` and `constructorInfo`s. -/
  ivals_eq : ivals = (headers.infos.zip indTypes.toList).map fun p =>
    (p.1, familyCtorInfos stats c.lparams isUnsafe p.2)
  /-- (Added for the rules agent.) Every kernel constructor has the declaration's parameter
  count. -/
  ctor_numParams : ∀ iv ∈ ivals, ∀ cval ∈ iv.2, cval.numParams = decl.nparams
  /-- (Added for the recursor agent.) The concrete parameter prefixes and spines of the source
  constructor types. -/
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  /-- (Added for the recursor agent.) The concrete checked tails, in the header environment's
  parameter scope. -/
  constructorTails : ConstructorTails headers.context.venv c.lparams
    headers.statsWF.parameterScope stats decl indTypes classes
  /-- (Added for the recursor agent.) The owner normal forms of the kernel constructor types. -/
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes
  /-- (Added by install, WAVE 2 install COMPAT.) Positivity's literal side condition, in the
  recursor phase's context. -/
  literalDisjoint : checkPositivityStep.AvailableLiteralDisjoint context.venv stats.indConsts

namespace ConstructorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}

/-- The projection-stage environment, in which the recursors are checked. -/
abbrev envP (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VEnv := R.ctorVEnv.addProjections decl.projectionEntries

theorem envP_eq (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.context.venv = R.envP := R.contextVEnv

theorem envP_wf (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.envP.WF := by have := R.context.wf; rwa [R.contextVEnv] at this

theorem addTypesCtors (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : decl.addTypesCtors sourceEnv = some R.ctorVEnv := by
  rw [VInductDecl.addTypesCtors, VInductDecl.addTypes_eq_addConstVals, R.core.typesAdded]
  simp [VInductDecl.addCtors_eq_addConstVals, R.core.ctorsAdded]

theorem addTypesCtorsProjs (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : decl.addTypesCtorsProjs sourceEnv = some R.envP := by
  rw [VInductDecl.addTypesCtorsProjs, R.addTypesCtors]; rfl

theorem typesWF (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF sourceEnv := by
  intro ci hci
  simp only [VInductDecl.typeConstants, List.mem_map] at hci
  obtain ⟨t, ht, rfl⟩ := hci
  exact TrInductDeclCore.typeHeadersWF R.core t ht

theorem ctorsWF (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF R.headerVEnv := by
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  obtain ⟨t, ht, hci⟩ := hci
  obtain ⟨_, _, Ht⟩ := List.Forall₂.forall_exists_r R.core.types t ht
  obtain ⟨_, _, Hc⟩ := List.Forall₂.forall_exists_r Ht.ctors ci hci
  exact Hc.wf

end ConstructorCheck

/-- The boundary theorem of the constructor phase: in the context of a completed header phase,
`constructorPhase` yields a constructor check for a declaration the checked headers describe,
whose classification is the one returned. -/
theorem AddInductive.constructorPhase.WF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c'.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe c'.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hnprimCtors : c'.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hlparams : c'.lparams.Nodup)
    (hclosed : MutualInductivesClosed c'.env)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.constructorPhase stats nparams indTypes numNested isUnsafe c').WF
      fun out => ∃ decl, P.headers.Describes decl ∧
        ∃ R : ConstructorCheck c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes out.1,
          R.classes = out.2 := by
  have HD := AddInductive.declareInductiveTypes.installedWF P numNested isUnsafe hvisible
    hnprimTypes hpresent
  have HP := AddInductive.declareInductiveTypes.allowsPrimitives (c := c') stats nparams indTypes
    numNested isUnsafe Hc'.checking.tr.map_wf
  unfold AddInductive.constructorPhase
  refine Except.WF.bind (fun r h => And.intro (HD r h) (HP r h))
    fun headerEnv ⟨⟨hwfH, Hhdr⟩, hprimH⟩ => ?_
  intro out hout
  change (AddInductive.checkConstructors indTypes stats isUnsafe { c' with env := headerEnv } >>=
    fun positivity => (AddInductive.declareConstructors stats indTypes isUnsafe >>= fun ctorEnv =>
      pure (ctorEnv, positivity)) { c' with env := headerEnv }) = .ok out at hout
  cases hcheck : AddInductive.checkConstructors indTypes stats isUnsafe
      { c' with env := headerEnv } with
  | error e => rw [hcheck] at hout; cases hout
  | ok positivity =>
  rw [hcheck] at hout
  change (AddInductive.declareConstructors stats indTypes isUnsafe { c' with env := headerEnv } >>=
    fun ctorEnv => (pure (ctorEnv, positivity) : Except Exception _)) = .ok out at hout
  cases hdeclare : AddInductive.declareConstructors stats indTypes isUnsafe
      { c' with env := headerEnv } with
  | error e => rw [hdeclare] at hout; cases hout
  | ok ctorEnv =>
  rw [hdeclare] at hout
  cases hout
  have habsent := AddInductive.declareConstructors.namesAbsent (c := { c' with env := headerEnv })
    (stats := stats) (indTypes := indTypes) (isUnsafe := isUnsafe) hwfH ctorEnv hdeclare
  obtain ⟨hmap, hquot, hfr, hnd⟩ := AddInductive.declareConstructors.WF
    (c := { c' with env := headerEnv }) stats indTypes isUnsafe hwfH ctorEnv hdeclare
  obtain ⟨HI⟩ := Hhdr habsent
  have hnprimOwner : ∀ owner ∈ indTypes.toList,
      ¬ Kernel.Environment.primitives.contains owner.name := by
    intro owner howner hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp howner
    obtain ⟨hlen, hget⟩ := inductiveTypeInfos_getElem stats nparams indTypes numNested isUnsafe
      c'.lparams P.nindices_size
    have hi' : i < (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
        c'.lparams).toList.length := by rw [hlen]; exact hi
    obtain ⟨hname, -⟩ := hget i hi hi'
    have hmem := List.getElem_mem hi'
    rw [← hname] at hp
    exact hnprimTypes (hprimH _ hmem hp) _ hmem hp
  obtain ⟨decl, hD, hU, hK⟩ := AddInductive.checkConstructors.WF P numNested isUnsafe HI
    hvisible hnprimOwner hlparams positivity hcheck
  let H := HI.toHeaderEnvironment hvisible hD hU
  have hnindices : ∀ i (hi : i < decl.types.length) (hn : i < stats.nindices.size),
      stats.nindices[i] = decl.types[i].numIndices := by
    intro i hi hn
    have h1 := congrArg (·[i]?) P.nindices
    have h2 := congrArg (·[i]?) hD.numIndices
    simp only [Array.getElem?_toList] at h1
    rw [← h2] at h1
    simpa [hi, hn] using h1
  have hnprim : ∀ cval ∈ ctorInfos stats c'.lparams isUnsafe indTypes.toList,
      ¬ Kernel.Environment.primitives.contains cval.name := fun cval hcval hp => by
    have hallow := (hfr cval hcval).2 hp
    obtain ⟨t, ht, j, ctor, hctor, rfl⟩ := mem_ctorInfos hcval
    exact hnprimCtors hallow t ht ctor hctor hp
  -- WAVE 2 install COMPAT: `CtorInstall` over the header data, with its primitive fields
  have hnprimFam : ∀ T ∈ decl.types, ¬ Kernel.Environment.primitives.contains T.name := by
    intro T hT hp
    obtain ⟨src, hsrc, htr⟩ := List.Forall₂.forall_exists_r H.trSources T hT
    exact hnprimOwner src hsrc (htr.1.name ▸ hp)
  have hprims := CtorInstall.ordinaryPrimitives H (hK H) hmap (fun cval hcval => (hfr cval hcval).1)
    hnd hnprim hnprimFam
  let I : CtorInstall c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes headerEnv ctorEnv
      positivity := {
    H := H.toData
    K := hK H
    map_eq := hmap
    quotInit_eq := hquot
    fresh := fun cval hcval => (hfr cval hcval).1
    nodup := hnd
    hasPrimitives := hprims.1
    safePrimitives := hprims.2.1
    literalDisjoint := hprims.2.2
    nindices_size := P.nindices_size
    nindices := hnindices
    params_size := P.params_size
    visible := hvisible }
  refine ⟨decl, hD, {
    headerEnv := headerEnv
    headers := H
    ctorVEnv := I.ctorVEnv
    core := I.core
    formation := I.formation
    params_eq := rfl
    checked := ⟨I.K.shapes, I.K.types⟩
    classes := positivity
    classes_length := I.K.classes_length
    tails := I.K.tails
    ivals := I.ivals
    ivals_infos := I.ivals_infos
    trTypes := I.trTypes
    map_eq := by rw [I.ivals_flat]; exact hmap
    quotInit_eq := hquot
    fresh := fun iv hiv cval hcval => by
      have hmem : ConstantInfo.ctorInfo cval ∈
          I.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo) :=
        List.mem_flatMap.mpr ⟨iv, hiv, List.mem_map_of_mem hcval⟩
      rw [I.ivals_flat] at hmem
      obtain ⟨cv, hcv, he⟩ := List.mem_map.mp hmem
      cases he
      exact (hfr _ hcv).1
    context := I.context
    contextVEnv := rfl
    contextMLCtx := H.contextMLCtx.symm  -- WAVE 2 install COMPAT
    parameters := I.parameters
    closed := I.closed hclosed
    inductInfosFromDecl := I.inductInfosFromDecl
    constructorParameterAlignment := fun h => I.constructorParameterAlignment h
    ivals_eq := rfl
    ctor_numParams := I.ctor_numParams
    parameterPrefixes := I.K.parameterPrefixes
    constructorTails := I.K.constructorTails
    ownerNormalForms := I.K.ownerNormalForms
    literalDisjoint := I.contextLiteralDisjoint }, rfl⟩

end VerifyInductive
end Lean4Lean
