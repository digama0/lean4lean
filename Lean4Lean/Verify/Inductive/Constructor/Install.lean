import Lean4Lean.Verify.Inductive.Constructor.Environment
import Lean4Lean.Verify.Inductive.Constructor.LiteralNames  -- WAVE 2 install COMPAT

/-! # The constructor environment

`CtorInstall` collects what the constructor phase knows once the constructors are checked and
declared: the header environment `H`, the constructor check `K`, and the effect of
`declareConstructors` on the constant map. From it this file builds the abstract constructor
environment (`ctorVEnv`), the translation of the kernel constructors, and the checking
invariant of the constructor environment with the declaration's projection entries. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem VEnv.exists_addConstVals {env : VEnv} : ∀ {cis : List VConstVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConstVals cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConstVals (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConstVals, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VExpr.piArity_eq_forallArity : ∀ e : VExpr, e.piArity = e.forallArity
  | .forallE _ b => by simp [VExpr.piArity, VExpr.forallArity, VExpr.piArity_eq_forallArity b]
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .proj _ _ _ => rfl

theorem inductiveTypeInfos_size {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} (h : stats.nindices.size = indTypes.size)
    (nparams numNested : Nat) (isUnsafe : Bool) (lparams : List Name) :
    (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe lparams).size =
      indTypes.size := by
  simp [AddInductive.inductiveTypeInfos, h]

theorem inductiveTypeInfos_fields {stats : AddInductive.InductiveStats}
    {indTypes : Array InductiveType} {nparams numNested : Nat} {isUnsafe : Bool}
    {lparams : List Name} (i : Nat)
    (hi : i < (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
      lparams).size) :
    let info := (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe
      lparams)[i]
    ∃ (hi' : i < indTypes.size) (hn : i < stats.nindices.size),
      info.name = indTypes[i].name ∧ info.type = indTypes[i].type ∧
      info.numParams = nparams ∧ info.numIndices = stats.nindices[i] ∧
      info.all = (indTypes.map (·.name)).toList ∧ info.isUnsafe = isUnsafe ∧
      info.levelParams = lparams ∧ info.ctors = indTypes[i].ctors.map (·.name) := by
  have h1 : i < indTypes.size := by
    have := hi; simp [AddInductive.inductiveTypeInfos] at this; omega
  have h2 : i < stats.nindices.size := by
    have := hi; simp [AddInductive.inductiveTypeInfos] at this; omega
  exact ⟨h1, h2, by simp [AddInductive.inductiveTypeInfos]⟩

/-- What the constructor phase knows once the constructors are checked and declared. -/
structure CtorInstall (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (headerEnv ctorEnv : Environment)
    (classes : List (List (List Bool))) where
  -- WAVE 2 install COMPAT: the header data (no header `ContextWF`), so that the primitive
  -- `Bool`/`Nat` path installs its constructors here too
  H : HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv
  K : ConstructorsChecked H classes
  map_eq : ctorEnv.constants = insertConsts headerEnv.constants
    ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map .ctorInfo)
  quotInit_eq : ctorEnv.quotInit = headerEnv.quotInit
  fresh : ∀ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
    headerEnv.find? cval.name = none
  nodup : ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name)).Nodup
  -- WAVE 2 install COMPAT: the primitive invariant of the constructor model and the primitive
  -- constants of the constructor environment, in place of `nprim` (the ordinary path proves
  -- them from the constructor names being nonprimitive, `CtorInstall.ofNprim`)
  hasPrimitives : ∀ venv', H.context.venv.addConstVals decl.constructorConstants = some venv' →
    venv'.HasPrimitives
  safePrimitives : ∀ {n ci}, ctorEnv.find? n = some ci →
    Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  -- WAVE 2 install COMPAT: positivity's literal side condition in the constructor model
  literalDisjoint : ∀ venv', H.context.venv.addConstVals decl.constructorConstants = some venv' →
    checkPositivityStep.AvailableLiteralDisjoint venv' stats.indConsts
  nindices_size : stats.nindices.size = indTypes.size
  nindices : ∀ i (hi : i < decl.types.length) (hn : i < stats.nindices.size),
    stats.nindices[i] = decl.types[i].numIndices
  params_size : stats.params.size = nparams
  visible : c.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe)

theorem trSourceConst_names {env : VEnv} {lparams : List Name} :
    ∀ {ctors : List Constructor} {ctors' : List VConstVal},
    List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
      TrSourceConst env lparams ctor.name ctor.type ctor') ctors ctors' →
    ctors.map (·.name) = ctors'.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [h.name, trSourceConst_names hs]

theorem constructorArity_instantiate1'_fvar (fv : FVarId) : ∀ (e : Expr) (d : Nat),
    AddInductive.constructorArity (e.instantiate1' (.fvar fv) d) = AddInductive.constructorArity e
  | .forallE _ _ b _, d => by
    simp [Expr.instantiate1', AddInductive.constructorArity, constructorArity_instantiate1'_fvar fv b]
  | .bvar i, d => by
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · simp [Expr.liftLooseBVars', AddInductive.constructorArity]
      · rfl
  | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl
  | .mdata .., _ | .proj .., _ | .app .., _ | .lam .., _ | .letE .., _ => rfl

theorem ParameterPrefix.constructorArity {stats : AddInductive.InductiveStats}
    (H : ParameterPrefix stats i source tail)
    (hfv : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv) :
    i ≤ stats.params.size ∧ AddInductive.constructorArity source =
      stats.params.size - i + AddInductive.constructorArity tail := by
  induction H with
  | done hi => subst hi; simp
  | @step i param body tail name dom bi hparam _ ih =>
    have hi : i < stats.params.size := (Array.getElem?_eq_some_iff.mp hparam).1
    obtain ⟨fv, rfl⟩ := hfv param (Array.mem_of_getElem? hparam)
    obtain ⟨-, ih⟩ := ih
    rw [Expr.instantiate1_eq, constructorArity_instantiate1'_fvar] at ih
    refine ⟨Nat.le_of_lt hi, ?_⟩
    simp only [AddInductive.constructorArity, ih]
    omega

theorem ConstantInfo.ctorInfo_safety (v : ConstructorVal) :
    (ConstantInfo.ctorInfo v).safety =
      if v.isUnsafe then DefinitionSafety.unsafe else .safe := by
  simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  by_cases h : v.isUnsafe = true <;> simp [h]

theorem mapCtorInfo {safety : DefinitionSafety} {env : VEnv} :
    ∀ {cvals : List ConstructorVal} {cs : List VConstVal},
    List.Forall₂ (fun cval c => TrConstVal safety env (.ctorInfo cval) c ∧
      cval.numParams + cval.numFields = c.type.piArity) cvals cs →
    List.Forall₂ (fun ci v => TrConstVal safety env ci v) (cvals.map ConstantInfo.ctorInfo) cs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h.1 (mapCtorInfo hs)

def _root_.Lean4Lean.VRecursorShape.mono' {env env' : VEnv} (hle : env ≤ env')
    {recName : Name} {recUvars nparams cnparams nmotives nminors nindices : Nat} {indName : Name}
    {indLevels : List VLevel} {ctorParams : List VExpr}
    (S : VRecursorShape env recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams) :
    VRecursorShape env' recName recUvars nparams cnparams nmotives nminors nindices indName
      indLevels ctorParams :=
  { S with const := hle.constants S.const }

def _root_.Lean4Lean.VConstructorShape.mono' {env env' : VEnv} (hle : env ≤ env')
    {ctorName : Name} {ctorUvars nparams nfields nindices : Nat} {indName : Name}
    (S : VConstructorShape env ctorName ctorUvars nparams nfields nindices indName) :
    VConstructorShape env' ctorName ctorUvars nparams nfields nindices indName :=
  { S with const := hle.constants S.const }

theorem InductiveMemberInfos.mono {env env' : Environment}
    (hpres : ∀ {n ci}, env.find? n = some ci → env'.find? n = some ci) :
    ∀ {names}, InductiveMemberInfos env names → InductiveMemberInfos env' names
  | _, .nil => .nil
  | _, .cons h hs => .cons (hpres h) (InductiveMemberInfos.mono hpres hs)

namespace CtorInstall

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {headerEnv ctorEnv : Environment} {classes : List (List (List Bool))}
  (I : CtorInstall c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv ctorEnv
    classes)
include I

/-- The abstract header environment. -/
abbrev headerVEnv : VEnv := I.H.context.venv

theorem headerVEnv_wf : I.headerVEnv.WF := I.H.context.wf

theorem sourceEnv_wf : sourceEnv.WF := by
  rw [← I.H.sourceContextVEnv]; exact I.H.sourceContext.wf

theorem sourceLE : sourceEnv ≤ I.headerVEnv := VEnv.addConstVals_le I.H.typesAdded

theorem types_length : indTypes.size = decl.types.length := by
  simpa using List.Forall₂.length_eq I.H.trSources

theorem infos_length : I.H.infos.length = indTypes.size := by
  rw [I.H.infos_eq]; simp [inductiveTypeInfos_size I.nindices_size]

/-- The kernel constructors of each family, with their abstract constructors. -/
theorem ctorTrAt (i : Nat) (hi : i < indTypes.size) :
    ∃ hi' : i < decl.types.length,
      List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
        TrSourceConst I.headerVEnv c.lparams ctor.name ctor.type ctor')
        indTypes[i].ctors decl.types[i].ctors := by
  have hi' : i < decl.types.length := I.types_length ▸ hi
  refine ⟨hi', ?_⟩
  have := List.forall₂_getElem I.K.ctorTr i (by simpa using hi) hi'
  simpa using this

theorem ctorNames : decl.constructorConstants.map (·.name) =
    (ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name) := by
  rw [ctorInfos_names]
  simp only [VInductDecl.constructorConstants, List.map_flatMap]
  have go : ∀ {sources : List InductiveType} {targets : List VInductiveType},
      List.Forall₂ (fun (source : InductiveType) (target : VInductiveType) =>
        List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
          TrSourceConst I.headerVEnv c.lparams ctor.name ctor.type ctor')
          source.ctors target.ctors) sources targets →
      targets.flatMap (fun t => t.ctors.map (·.name)) =
        sources.flatMap (fun t => t.ctors.map (·.name)) := by
    intro sources targets h
    induction h with
    | nil => rfl
    | @cons s t ss ts hst _ ih =>
      simp only [List.flatMap_cons, ih]
      congr 1
      exact (trSourceConst_names hst).symm
  exact go I.K.ctorTr

theorem ctorNames_nodup : (decl.constructorConstants.map (·.name)).Nodup := by
  rw [I.ctorNames]; exact I.nodup

/-- A name of the abstract header environment is a name of the kernel header environment. -/
theorem headerFind_of_constants {n : Name} {ci : VConstant}
    (h : I.headerVEnv.constants n = some ci) : ∃ found, headerEnv.find? n = some found := by
  obtain ⟨found, hfound, -⟩ := I.H.context.checking.find?_iff.mpr ⟨ci, h⟩
  exact ⟨found, hfound⟩

theorem ctorFresh : ∀ ci ∈ decl.constructorConstants, I.headerVEnv.constants ci.name = none := by
  intro ci hci
  cases h : I.headerVEnv.constants ci.name with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨found, hfound⟩ := I.headerFind_of_constants h
    have hmem : ci.name ∈ (ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name) := by
      rw [← I.ctorNames]; exact List.mem_map_of_mem hci
    obtain ⟨cval, hcval, he⟩ := List.mem_map.mp hmem
    have := I.fresh cval hcval
    rw [he, hfound] at this; cases this

theorem exists_ctorVEnv : ∃ ctorVEnv, I.headerVEnv.addConstVals decl.constructorConstants =
    some ctorVEnv :=
  VEnv.exists_addConstVals I.ctorFresh I.ctorNames_nodup

/-- The abstract constructor environment. -/
noncomputable def ctorVEnv : VEnv := Classical.choose I.exists_ctorVEnv

theorem ctorsAdded : I.headerVEnv.addConstVals decl.constructorConstants = some I.ctorVEnv :=
  Classical.choose_spec I.exists_ctorVEnv

theorem headerLE : I.headerVEnv ≤ I.ctorVEnv := VEnv.addConstVals_le I.ctorsAdded

theorem constructorUvars : ∀ ci ∈ decl.constructorConstants, ci.uvars = decl.uvars := by
  intro ci hci
  obtain ⟨t, ht, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨s, hs, hst⟩ := List.Forall₂.forall_exists_r I.K.ctorTr t ht
  obtain ⟨sc, _, htr⟩ := List.Forall₂.forall_exists_r hst ci hci
  exact htr.uvars.trans I.H.uvars.symm

theorem ctorsWF' : ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF I.headerVEnv := by
  intro ci hci
  have := I.K.types ci hci
  simpa [VConstant.WF, VConstVal.toVConstant, I.constructorUvars ci hci] using this

/-- The core translation of the declaration. -/
theorem core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
    I.headerVEnv I.ctorVEnv := by
  refine TrInductDeclCore.ofPhases ⟨I.H.uvars, I.H.nparams, I.H.isUnsafe, I.H.typesAdded, ?_⟩
    ⟨I.ctorsAdded, I.K.ctorTr⟩
  have go : ∀ {sources : List InductiveType} {targets : List VInductiveType},
      List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
        TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
        source.ctors.map (·.name) = t.ctors.map (·.name)) sources targets →
      List.Forall₂ (fun (source : InductiveType) (target : VInductiveType) =>
        List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
          TrSourceConst I.headerVEnv c.lparams ctor.name ctor.type ctor')
          source.ctors target.ctors) sources targets →
      List.Forall₂ (TrInductiveTypeHeaders sourceEnv I.headerVEnv c.lparams) sources targets := by
    intro sources targets h1 h2
    induction h1 with
    | nil => exact .nil
    | cons h _ ih =>
      cases h2 with
      | cons h2 h2s => exact .cons ⟨h.1, List.Forall₂.imp (fun _ _ h => h.raw) h2⟩ (ih h2s)
  exact go I.H.trSources I.K.ctorTr

/-- The formation certificate of the declaration. -/
def formation : FormationCertificate sourceEnv decl where
  headers := I.H.headers
  envTypes := I.headerVEnv
  typesInstalled := I.H.typesAdded
  constructorParameters := I.K.parameterShapes
  constructors := I.K.shapes
  rawShapes := I.K.rawShapes

/-- The kernel headers with their constructors, in block order. -/
def ivals : List (InductiveVal × List ConstructorVal) :=
  (I.H.infos.zip indTypes.toList).map fun p => (p.1, familyCtorInfos stats c.lparams isUnsafe p.2)

theorem ivals_infos : I.ivals.map (·.1) = I.H.infos := by
  simp only [ivals, List.map_map]
  have : I.H.infos.length ≤ indTypes.toList.length := by simp [I.infos_length]
  simpa [Function.comp_def] using List.map_fst_zip this

theorem ivals_flat : I.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo) =
    (ctorInfos stats c.lparams isUnsafe indTypes.toList).map ConstantInfo.ctorInfo := by
  simp only [ivals, ctorInfos, List.map_flatMap, List.flatMap_map]
  have : indTypes.toList.length ≤ I.H.infos.length := by simp [I.infos_length]
  conv => rhs; rw [← List.map_snd_zip this]
  simp [List.flatMap_map]

theorem ivals_length : I.ivals.length = decl.types.length := by
  simp [ivals, I.infos_length, I.types_length]

theorem ivals_getElem (i : Nat) (hi : i < I.ivals.length) :
    ∃ (h1 : i < I.H.infos.length) (h2 : i < indTypes.size),
      I.ivals[i] = (I.H.infos[i], familyCtorInfos stats c.lparams isUnsafe indTypes[i]) := by
  have h1 : i < I.H.infos.length := by simp [ivals] at hi; omega
  have h2 : i < indTypes.size := by simpa [I.infos_length] using h1
  exact ⟨h1, h2, by simp [ivals]⟩

/-- The kernel constructor values all carry the declaration's parameter count. -/
theorem ctor_numParams : ∀ iv ∈ I.ivals, ∀ cval ∈ iv.2, cval.numParams = decl.nparams := by
  intro iv hiv cval hcval
  obtain ⟨⟨info, t⟩, _, rfl⟩ := List.mem_map.mp hiv
  obtain ⟨k, ctor, _, rfl⟩ := mem_ctorInfosFrom hcval
  simp [AddInductive.constructorInfo, I.params_size, I.H.nparams]

/-- One kernel constructor translates to its abstract constructor, with the arity
`numParams + numFields` of the abstract type. -/
theorem ctorAt (i : Nat) (hi : i < indTypes.size) (j : Nat)
    (hj : j < indTypes[i].ctors.length) (ctor' : VConstVal)
    (htr : TrSourceConst I.headerVEnv c.lparams indTypes[i].ctors[j].name
      indTypes[i].ctors[j].type ctor') :
    let cval := AddInductive.constructorInfo stats c.lparams isUnsafe indTypes[i] j
      indTypes[i].ctors[j]
    TrConstVal c.safety I.headerVEnv (.ctorInfo cval) ctor' ∧
      cval.numParams + cval.numFields = ctor'.type.piArity := by
  intro cval
  refine ⟨⟨⟨?_, ?_, ?_⟩, htr.name.symm⟩, ?_⟩
  · rw [ConstantInfo.ctorInfo_safety]
    simpa [cval, AddInductive.constructorInfo] using I.visible
  · exact htr.uvars.symm
  · exact htr.type
  · obtain ⟨tail, hprefix⟩ := I.K.parameterPrefixes.replay i hi j hj
    obtain ⟨k, hspine⟩ := I.K.parameterPrefixes.spines i hi j hj
    obtain ⟨-, harity⟩ := hprefix.constructorArity I.H.sourceParameters.paramFVars
    have hk := hspine.constructorArity
    have hfa := TrExprS.forallArity_of_spine hspine htr.type
    rw [VExpr.piArity_eq_forallArity, hfa]
    simp only [cval, AddInductive.constructorInfo_numFields]
    simp only [AddInductive.constructorInfo]
    omega

/-- The kernel families with their constructors translate to the declaration's families. -/
theorem trTypes : List.Forall₂ (fun (iv : InductiveVal × List ConstructorVal) (t : VInductiveType) =>
    TrIndType c.safety sourceEnv I.headerVEnv iv.1 iv.2 t) I.ivals decl.types := by
  apply List.forall₂_of_getElem I.ivals_length
  intro i hi hi'
  obtain ⟨h1, h2, heq⟩ := I.ivals_getElem i hi
  rw [heq]
  have hhdr := List.forall₂_getElem I.H.trHeaders i h1 hi'
  obtain ⟨_, hctors⟩ := I.ctorTrAt i h2
  refine ⟨hhdr.1, ?_, ?_⟩
  · rw [hhdr.2]
    rw [← trSourceConst_names hctors]
    simp [familyCtorInfos, ctorInfosFrom_names]
  · apply List.forall₂_of_getElem (by rw [familyCtorInfos_length]; exact List.Forall₂.length_eq hctors)
    intro j hj hj'
    have hjs : j < indTypes[i].ctors.length := by simpa [familyCtorInfos_length] using hj
    rw [familyCtorInfos_getElem]
    exact I.ctorAt i h2 j hjs _ (List.forall₂_getElem hctors j hjs hj')

theorem headerMapWF : headerEnv.constants.WF := I.H.context.checking.map_wf

/-- The kernel constructors in lockstep with the abstract ones. -/
theorem ctorEntries : List.Forall₂ (fun ci v => TrConstVal c.safety I.headerVEnv ci v ∧
      v.toVConstant.WF I.headerVEnv ∧ ci.deltaValue? = none)
    ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map ConstantInfo.ctorInfo)
    decl.constructorConstants := by
  have htr : List.Forall₂ (fun ci v => TrConstVal c.safety I.headerVEnv ci v)
      (I.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo)
      (decl.types.flatMap (·.ctors)) := by
    apply Lean4Lean.List.Forall₂.flatMap (R := fun (iv : InductiveVal × List ConstructorVal)
      (t : VInductiveType) => TrIndType c.safety sourceEnv I.headerVEnv iv.1 iv.2 t) _ I.trTypes
    intro iv t h
    exact mapCtorInfo h.ctors
  rw [← I.ivals_flat]
  refine Lean4Lean.List.Forall₂.imp (fun ci v ⟨h, hci, hv⟩ => ⟨h, I.ctorsWF' v hv, ?_⟩)
    (Lean4Lean.List.Forall₂.and_mem htr)
  obtain ⟨iv, _, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨cval, _, rfl⟩ := List.mem_map.mp hci
  rfl

theorem ctorCis_fresh : ∀ ci ∈ (ctorInfos stats c.lparams isUnsafe indTypes.toList).map
    ConstantInfo.ctorInfo, headerEnv.find? ci.name = none := by
  intro ci hci
  obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
  exact I.fresh cval hcval

theorem ctorCis_nodup : (((ctorInfos stats c.lparams isUnsafe indTypes.toList).map
    ConstantInfo.ctorInfo).map (·.name)).Nodup := by
  rw [List.map_map]; exact I.nodup

theorem ctorMapWF : ctorEnv.constants.WF :=
  insertConsts_map_wf I.map_eq I.headerMapWF I.ctorCis_fresh I.ctorCis_nodup

/-- Every constant of the header environment is a constant of the constructor environment. -/
theorem headerPres {n : Name} {ci : ConstantInfo} (h : headerEnv.find? n = some ci) :
    ctorEnv.find? n = some ci :=
  insertConsts_env_mono I.map_eq I.headerMapWF I.ctorCis_fresh I.ctorCis_nodup h

theorem ctorEnv_cases {n : Name} {ci : ConstantInfo} (h : ctorEnv.find? n = some ci) :
    headerEnv.find? n = some ci ∨ ∃ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
      ci = .ctorInfo cval ∧ cval.name = n := by
  rcases insertConsts_env_cases I.map_eq I.headerMapWF I.ctorCis_fresh I.ctorCis_nodup h with
    h | ⟨hmem, hname⟩
  · exact .inl h
  · obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hmem
    exact .inr ⟨cval, hcval, rfl, hname⟩

theorem ctorEnv_self {cval : ConstructorVal}
    (h : cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList) :
    ctorEnv.find? cval.name = some (.ctorInfo cval) :=
  insertConsts_env_self I.map_eq I.headerMapWF I.ctorCis_fresh I.ctorCis_nodup
    (List.mem_map_of_mem h)

theorem sourceMapWF : c.env.constants.WF := I.H.sourceContext.checking.tr.map_wf

theorem infoCis_fresh : ∀ ci ∈ I.H.infos.map ConstantInfo.inductInfo, c.env.find? ci.name = none := by
  intro ci hci
  obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hci
  exact I.H.fresh info hinfo

theorem infoNames : I.H.infos.map (·.name) = decl.types.map (·.name) := by
  have go : ∀ {infos : List InductiveVal} {types : List VInductiveType},
      List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
        TrConstVal c.safety sourceEnv (.inductInfo info) t.toVConstVal ∧
        info.ctors = t.ctors.map (·.name)) infos types →
      infos.map (·.name) = types.map (·.name) := by
    intro infos types h
    induction h with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.2
  exact go I.H.trHeaders

theorem typeNames_nodup : (decl.types.map (·.name)).Nodup := by
  simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
    VEnv.addConstVals_names_nodup I.H.typesAdded

theorem infoCis_nodup : ((I.H.infos.map ConstantInfo.inductInfo).map (·.name)).Nodup := by
  rw [List.map_map]
  have : (I.H.infos.map ConstantInfo.inductInfo).map (·.name) = I.H.infos.map (·.name) := by
    simp only [List.map_map]; rfl
  rw [← List.map_map, this, I.infoNames]; exact I.typeNames_nodup

/-- Every constant of the source environment is a constant of the constructor environment. -/
theorem sourcePres {n : Name} {ci : ConstantInfo} (h : c.env.find? n = some ci) :
    ctorEnv.find? n = some ci :=
  I.headerPres (insertConsts_env_mono I.H.map_eq I.sourceMapWF I.infoCis_fresh I.infoCis_nodup h)

theorem headerEnv_cases {n : Name} {ci : ConstantInfo} (h : headerEnv.find? n = some ci) :
    c.env.find? n = some ci ∨ ∃ info ∈ I.H.infos, ci = .inductInfo info ∧ info.name = n := by
  rcases insertConsts_env_cases I.H.map_eq I.sourceMapWF I.infoCis_fresh I.infoCis_nodup h with
    h | ⟨hmem, hname⟩
  · exact .inl h
  · obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hmem
    exact .inr ⟨info, hinfo, rfl, hname⟩

theorem headerEnv_self {info : InductiveVal} (h : info ∈ I.H.infos) :
    headerEnv.find? info.name = some (.inductInfo info) :=
  insertConsts_env_self I.H.map_eq I.sourceMapWF I.infoCis_fresh I.infoCis_nodup
    (List.mem_map_of_mem h)

/-- The checking invariant of the constructor environment over the abstract one. -/
theorem checkingCtor : CheckingEnv c.safety ctorEnv I.ctorVEnv :=
  CheckingEnv.of_constants_eq (CheckingEnv.insertConsts I.H.context.checking I.ctorEntries
    I.ctorCis_fresh I.ctorCis_nodup I.ctorsAdded) (by rw [I.map_eq, constants_foldl_add])

/-- The projection-stage environment, in which the recursors are checked. -/
noncomputable abbrev envP : VEnv := I.ctorVEnv.addProjections decl.projectionEntries

theorem envP_wf : I.envP.WF :=
  VEnv.WF.inductProjections (block := ⟨decl.typeConstants, decl.constructorConstants, [], [],
      decl.projectionEntries⟩)
    I.sourceEnv_wf I.checkingCtor.wf (TrInductDeclCore.sourceNames_nodup I.core)
    (TrInductDeclCore.typeHeadersWF I.core) I.constructorUvars I.ctorsWF'
    I.formation.formationWF.sourceParameterWF I.K.rawShapes rfl rfl rfl I.H.typesAdded
    I.ctorsAdded

theorem headerLE_P : I.headerVEnv ≤ I.envP := I.headerLE.trans VEnv.addProjections_le

theorem sourceLE_P : sourceEnv ≤ I.envP := I.sourceLE.trans I.headerLE_P

omit I in
theorem HasPrimitives_addConstVals : ∀ {env env' : VEnv} {vs : List VConstVal},
    env.HasPrimitives → (∀ v ∈ vs, ¬ Kernel.Environment.primitives.contains v.name) →
    env.addConstVals vs = some env' → env'.HasPrimitives
  | _, _, [], h, _, hadd => by cases hadd; exact h
  | env, env', v :: vs, h, hn, hadd => by
    simp only [VEnv.addConstVals] at hadd
    cases hmid : env.addConst v.name v.toVConstant with
    | none => simp [hmid] at hadd
    | some mid =>
      simp only [hmid, Option.bind_eq_bind, Option.bind_some] at hadd
      exact HasPrimitives_addConstVals (h.addConst_of_not_primitive hmid (hn v (.head _)))
        (fun w hw => hn w (.tail _ hw)) hadd

/-- The local checking invariants of the constructor environment with its projections. -/
theorem validCore : CheckingEnv.ValidCore c.safety ctorEnv I.envP where
  tr := I.checkingCtor.addProjections I.envP_wf
  hasPrimitives := (I.hasPrimitives _ I.ctorsAdded).addProjections
  safePrimitives := I.safePrimitives

theorem contextLiteralDisjoint :
    checkPositivityStep.AvailableLiteralDisjoint I.envP stats.indConsts :=
  (I.literalDisjoint _ I.ctorsAdded).addProjections _

omit I in
theorem toEnvFind {E : Environment} (hwf : E.constants.WF) {n : Name} {ci : ConstantInfo} :
    E.constants.find? n = some ci ↔ E.find? n = some ci := by
  rw [Kernel.Environment.find?, hwf.find?'_eq_find?]

theorem sourceNames : indTypes.toList.map (·.name) = decl.types.map (·.name) := by
  have go : ∀ {sources : List InductiveType} {types : List VInductiveType},
      List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
        TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
        source.ctors.map (·.name) = t.ctors.map (·.name)) sources types →
      sources.map (·.name) = types.map (·.name) := by
    intro s t h
    induction h with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.name.symm
  exact go I.H.trSources

/-- The kernel header of family `i`. -/
theorem infoAt (i : Nat) (hi : i < decl.types.length) :
    ∃ (h : i < I.H.infos.length) (hs : i < indTypes.size),
      I.H.infos[i].name = decl.types[i].name ∧
      I.H.infos[i].all = decl.types.map (·.name) ∧
      I.H.infos[i].numParams = decl.nparams ∧
      I.H.infos[i].numIndices = decl.types[i].numIndices ∧
      I.H.infos[i].levelParams = c.lparams ∧
      I.H.infos[i].isUnsafe = isUnsafe ∧
      I.H.infos[i].ctors = indTypes[i].ctors.map (·.name) ∧
      I.H.infos[i].ctors = decl.types[i].ctors.map (·.name) := by
  have h : i < I.H.infos.length := by rw [I.infos_length, I.types_length]; exact hi
  have hs : i < indTypes.size := by rw [I.types_length]; exact hi
  have hhdr := List.forall₂_getElem I.H.trHeaders i h hi
  have harr : i < (AddInductive.inductiveTypeInfos stats nparams indTypes I.H.numNested isUnsafe
      c.lparams).size := by rw [inductiveTypeInfos_size I.nindices_size]; exact hs
  obtain ⟨_, hn, hname, -, hnp, hni, hall, hunsafe, hlp, hctors⟩ :=
    inductiveTypeInfos_fields (stats := stats) (nparams := nparams) (indTypes := indTypes)
      (numNested := I.H.numNested) (isUnsafe := isUnsafe) (lparams := c.lparams) i harr
  have heq : I.H.infos[i] = (AddInductive.inductiveTypeInfos stats nparams indTypes
      I.H.numNested isUnsafe c.lparams)[i] := by
    simp only [I.H.infos_eq, Array.getElem_toList]
  refine ⟨h, hs, hhdr.1.2, ?_, ?_, ?_, ?_, ?_, ?_, hhdr.2⟩
  · rw [heq, hall]; simpa using I.sourceNames
  · rw [heq, hnp, I.H.nparams]
  · rw [heq, hni]; exact I.nindices i hi hn
  · rw [heq, hlp]
  · rw [heq, hunsafe]
  · rw [heq, hctors]

omit I in
/-- The kernel constructors of family `i`. -/
theorem ctorInfoAt (i : Nat) (hi : i < indTypes.size) (j : Nat)
    (hj : j < indTypes[i].ctors.length) :
    AddInductive.constructorInfo stats c.lparams isUnsafe indTypes[i] j indTypes[i].ctors[j] ∈
      ctorInfos stats c.lparams isUnsafe indTypes.toList := by
  apply List.mem_flatMap.mpr
  refine ⟨indTypes[i], by simp, ?_⟩
  have hj' : j < (familyCtorInfos stats c.lparams isUnsafe indTypes[i]).length := by
    rw [familyCtorInfos_length]; exact hj
  rw [← familyCtorInfos_getElem j hj']
  exact List.getElem_mem hj'

/-- Every newly visible family is an exact family of the declaration. -/
theorem inductInfosFromDecl : InductInfosFromDecl c.env.constants ctorEnv.constants decl := by
  intro familyName familyInfo hfamily
  have hfind := (toEnvFind I.ctorMapWF).mp hfamily
  rcases I.ctorEnv_cases hfind with h | ⟨cval, _, he, _⟩
  · rcases I.headerEnv_cases h with h | ⟨info, hinfo, he, hname⟩
    · exact .inl ((toEnvFind I.sourceMapWF).mpr h)
    · cases he
      right
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hinfo
      have hid : i < decl.types.length := by rw [I.infos_length, I.types_length] at hi; exact hi
      obtain ⟨_, hs, hname', hall, hnp, hni, hlp, hunsafe, hctorsI, hctorsD⟩ := I.infoAt i hid
      refine ⟨i, hname.symm, ⟨{
        familyIdx_lt := hid
        name := hname'
        lookup := by rw [hname]; exact hfamily
        all := hall
        levelParams := by rw [hlp, I.H.uvars]
        numParams := hnp
        numIndices := hni
        constructors := by rw [hctorsD]; simp
        isUnsafe := by rw [hunsafe, I.H.isUnsafe]
        constructor := fun j hj => ?_ }⟩⟩
      obtain ⟨_, hctors⟩ := I.ctorTrAt i hs
      have hjs : j < indTypes[i].ctors.length := by
        rw [List.Forall₂.length_eq hctors]; exact hj
      have htr := List.forall₂_getElem hctors j hjs hj
      have hji : j < I.H.infos[i].ctors.length := by rw [hctorsI]; simpa using hjs
      have hmem := ctorInfoAt (stats := stats) (c := c) (isUnsafe := isUnsafe) i hs j hjs
      have harity := (I.ctorAt i hs j hjs _ htr).2
      refine ⟨{
        familyIdx_lt := hid
        ctorIdx_lt := hj
        familyInfo_ctorIdx_lt := hji
        info := AddInductive.constructorInfo stats c.lparams isUnsafe indTypes[i] j
          indTypes[i].ctors[j]
        name := by simp [hctorsD]
        lookup := by
          have hn : I.H.infos[i].ctors[j] = indTypes[i].ctors[j].name := by simp [hctorsI]
          rw [hn]
          exact (toEnvFind I.ctorMapWF).mpr (I.ctorEnv_self hmem)
        induct := by
          simp only [AddInductive.constructorInfo]
          rw [hname']
          have := congrArg (·[i]?) I.sourceNames
          simpa [hid, hs] using this
        cidx := rfl
        numParams := by simp [AddInductive.constructorInfo, I.params_size, I.H.nparams]
        numFields := by
          rw [AddInductive.constructorInfo_numFields]
          simp [AddInductive.constructorInfo, I.params_size, I.H.nparams]
        numFields_forallArity := by
          rw [← VExpr.piArity_eq_forallArity, ← harity]
          simp [AddInductive.constructorInfo, I.params_size, I.H.nparams]
        levelParamsExact := by simp [AddInductive.constructorInfo, hlp]
        levelParams := by simp [AddInductive.constructorInfo, I.H.uvars]
        isUnsafe := by simp [AddInductive.constructorInfo, I.H.isUnsafe] }⟩
  · cases he

theorem indNameAt (i : Nat) (hi : i < indTypes.size) :
    ∃ h : i < decl.types.length, decl.types[i].name = indTypes[i].name := by
  have h : i < decl.types.length := I.types_length ▸ hi
  refine ⟨h, ?_⟩
  have := congrArg (·[i]?) I.sourceNames
  simp [h, hi] at this
  exact this.symm

/-- Every constructor of the constructor environment is listed by its present owner. -/
theorem constructorOwnersPresent : ConstructorOwnersPresent ctorEnv := by
  intro name info hfind
  rcases I.ctorEnv_cases hfind with h | ⟨cval, hcval, he, hname⟩
  · rcases I.headerEnv_cases h with h | ⟨_, _, he, _⟩
    · obtain ⟨owner, hown, hmem, hu⟩ :=
        I.H.sourceContext.checking.constructorOwners name info h
      exact ⟨owner, I.sourcePres hown, hmem, hu⟩
    · cases he
  · cases he
    obtain ⟨t, ht, j, ctor, hctor, rfl⟩ := mem_ctorInfos hcval
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have his : i < indTypes.size := by simpa using hi
    obtain ⟨hid, hdn⟩ := I.indNameAt i his
    obtain ⟨hl, _, hn, -, -, -, -, hunsafe, hctors, -⟩ := I.infoAt i hid
    refine ⟨I.H.infos[i], ?_, ?_, ?_⟩
    · have := I.headerPres (I.headerEnv_self (List.getElem_mem hl))
      simp only [AddInductive.constructorInfo]
      rw [hn, hdn] at this
      simpa using this
    · rw [← hname, hctors]
      simp only [AddInductive.constructorInfo]
      exact List.mem_map_of_mem (by simpa using hctor)
    · simp [AddInductive.constructorInfo, hunsafe]

theorem cover : ∀ T ∈ decl.types, ∃ v, ctorEnv.find? T.name = some (.inductInfo v) ∧
    c.env.find? T.name = none := by
  intro T hT
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
  obtain ⟨hl, _, hn, -⟩ := I.infoAt i hi
  refine ⟨I.H.infos[i], ?_, ?_⟩
  · rw [← hn]; exact I.headerPres (I.headerEnv_self (List.getElem_mem hl))
  · rw [← hn]; exact I.H.fresh _ (List.getElem_mem hl)

theorem typeUvars : ∀ T ∈ decl.types, T.uvars = decl.uvars := by
  intro T hT
  obtain ⟨_, _, htr⟩ := List.Forall₂.forall_exists_r I.H.trSources T hT
  exact htr.1.uvars.trans I.H.uvars.symm

theorem declRegistered : InstalledBlocks.DeclRegistered I.envP decl where
  typeUvars := I.typeUvars
  constructorUvars := I.constructorUvars
  family i hi := by
    simp only [VEnv.addProjections_constants]
    exact I.headerLE.constants (VEnv.addConstVals_get I.H.typesAdded
      (List.mem_map_of_mem (List.getElem_mem hi)))
  ctor i k hi hk := by
    simp only [VEnv.addProjections_constants]
    exact VEnv.addConstVals_get I.ctorsAdded
      (List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, List.getElem_mem hk⟩)
  projections e he := VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩)

theorem projOrigin {S : Name} {info : VProjectionInfo} (h : I.envP.projections S info) :
    I.H.sourceContext.venv.projections S info ∨ ⟨S, info⟩ ∈ decl.projectionEntries := by
  rcases VEnv.addProjections_iff.mp h with ⟨e, he, rfl, rfl⟩ | h
  · exact .inr he
  · left
    rw [I.H.sourceContextVEnv]
    rw [VEnv.addConstVals_projections I.ctorsAdded, VEnv.addConstVals_projections I.H.typesAdded]
      at h
    exact h

theorem blocks : InstalledBlocks c.safety ctorEnv I.envP .headers := by
  have HB := I.H.sourceContext.checking.blocks
  refine HB.addCtorStage I.H.sourcePresent I.sourceMapWF I.validCore.tr (fun h => I.sourcePres h)
    (by rw [I.H.sourceContextVEnv]; exact I.sourceLE_P) I.inductInfosFromDecl I.cover
    I.typeNames_nodup I.constructorOwnersPresent [] ?_ (by simp) (by simp) (by simp)
    I.declRegistered (fun h => I.projOrigin h)
  intro n r hfind hnone
  exfalso
  rcases I.ctorEnv_cases hfind with h | ⟨_, _, he, _⟩
  · rcases I.headerEnv_cases h with h | ⟨_, _, he, _⟩
    · rw [h] at hnone; cases hnone
    · cases he
  · cases he

theorem headerPresMap {n : Name} {ci : ConstantInfo} (h : headerEnv.constants.find? n = some ci) :
    ctorEnv.constants.find? n = some ci :=
  (toEnvFind I.ctorMapWF).mpr (I.headerPres ((toEnvFind I.headerMapWF).mp h))

theorem sourcePresMap {n : Name} {ci : ConstantInfo} (h : c.env.constants.find? n = some ci) :
    ctorEnv.constants.find? n = some ci :=
  (toEnvFind I.ctorMapWF).mpr (I.sourcePres ((toEnvFind I.sourceMapWF).mp h))

theorem sourceVEnvLE_P : I.H.sourceContext.venv ≤ I.envP := by
  rw [I.H.sourceContextVEnv]; exact I.sourceLE_P

-- WAVE 2 install COMPAT: from the source context, extended over the headers and constructors
theorem equationHeads : EquationHeadsCoherent ctorEnv.constants I.envP :=
  (I.H.sourceContext.checking.equationHeads.extendSimple (C' := ctorEnv.constants)
    (venv' := I.ctorVEnv) (fun h => I.sourcePresMap h)
    (fun df h => by
      rw [VEnv.addConstVals_defeqs I.ctorsAdded, VEnv.addConstVals_defeqs I.H.typesAdded] at h
      rwa [I.H.sourceContextVEnv])
    (fun p r h => by
      rw [VEnv.addConstVals_pats I.ctorsAdded, VEnv.addConstVals_pats I.H.typesAdded] at h
      rwa [I.H.sourceContextVEnv])).addProjections _

/-- The checking invariant of the constructor environment with the projection entries. -/
theorem valid : CheckingEnv.Valid c.safety ctorEnv I.envP :=
  I.validCore.toValid I.blocks I.equationHeads fun hq =>
    (I.H.sourceContext.checking.quot (by rw [← I.H.quotInit_eq, ← I.quotInit_eq]; exact hq)).extend
      (fun h => I.sourcePresMap h) I.sourceVEnvLE_P I.equationHeads

/-- A recursor of the constructor environment is a recursor of the header environment. -/
theorem recHeader {n : Name} {r : RecursorVal}
    (h : ctorEnv.constants.find? n = some (.recInfo r)) :
    headerEnv.constants.find? n = some (.recInfo r) := by
  rcases I.ctorEnv_cases ((toEnvFind I.ctorMapWF).mp h) with h | ⟨_, _, he, _⟩
  · exact (toEnvFind I.headerMapWF).mpr h
  · cases he

/-- A recursor of the constructor environment is a recursor of the source environment. -/
theorem recSource {n : Name} {r : RecursorVal}
    (h : ctorEnv.constants.find? n = some (.recInfo r)) :
    c.env.constants.find? n = some (.recInfo r) := by
  rcases I.headerEnv_cases ((toEnvFind I.headerMapWF).mp (I.recHeader h)) with h | ⟨_, _, he, _⟩
  · exact (toEnvFind I.sourceMapWF).mpr h
  · cases he

-- WAVE 2 install COMPAT: from the source context
theorem shapes : RecursorShapesCoherent c.safety ctorEnv.constants I.envP := by
  intro name rec hrec hsafe
  obtain ⟨cnparams, indLevels, ctorParams, ⟨S⟩, hrules⟩ :=
    I.H.sourceContext.shapes (I.recSource hrec) hsafe
  refine ⟨cnparams, indLevels, ctorParams, ⟨S.mono' I.sourceVEnvLE_P⟩, fun rule hrule => ?_⟩
  obtain ⟨ctorUvars, hlen, ⟨C⟩, hparams⟩ := hrules rule hrule
  refine ⟨ctorUvars, hlen, ⟨C.mono' I.sourceVEnvLE_P⟩, fun cval hcval => ?_⟩
  rcases I.ctorEnv_cases ((toEnvFind I.ctorMapWF).mp hcval) with h | ⟨cv, hcv, he, hn⟩
  · rcases I.headerEnv_cases h with h | ⟨_, _, he, _⟩
    · exact hparams cval ((toEnvFind I.sourceMapWF).mpr h)
    · cases he
  · exfalso
    obtain ⟨found, hfound, -⟩ := I.H.sourceContext.checking.tr.find?_iff.mpr ⟨_, C.const⟩
    have := I.fresh cv hcv
    rw [hn] at this
    rw [insertConsts_env_mono I.H.map_eq I.sourceMapWF I.infoCis_fresh I.infoCis_nodup hfound]
      at this
    cases this

theorem iota : IotaRulesRegistered c.safety ctorEnv I.envP := by
  intro recName cName rval rule hrec hrule hsafe
  have hrec' := (toEnvFind I.sourceMapWF).mp (I.recSource ((toEnvFind I.ctorMapWF).mpr hrec))
  obtain ⟨cval, rhs, hc, hfind, htr, hpat⟩ := I.H.sourceContext.iota hrec' hrule hsafe
  refine ⟨cval, rhs, hc, I.sourcePres hfind, htr.mono I.sourceVEnvLE_P, ?_⟩
  exact I.sourceVEnvLE_P.pats hpat

/-- The checking context over the constructor environment. -/
noncomputable def context : ContextWF { c with env := ctorEnv } :=
  -- WAVE 2 install COMPAT: from the source context
  I.H.sourceContext.withEnv I.valid I.shapes I.iota I.sourceVEnvLE_P

theorem context_venv : I.context.venv = I.envP := rfl
theorem context_mlctx : I.context.mlctx = I.H.context.mlctx := I.H.contextMLCtx.symm

noncomputable def parameters :
    HeaderParameterContext I.context stats I.H.headers.params depth :=
  I.H.sourceParameters.withEnv I.valid I.shapes I.iota I.sourceVEnvLE_P

/-- The mutual families of the constructor environment are closed. -/
theorem closed (hclosed : MutualInductivesClosed c.env) : MutualInductivesClosed ctorEnv := by
  intro targetName value hfind
  rcases I.ctorEnv_cases hfind with h | ⟨_, _, he, _⟩
  · rcases I.headerEnv_cases h with h | ⟨info, hinfo, he, hname⟩
    · have Hs := hclosed targetName value h
      refine ⟨Hs.members.mono fun h => I.sourcePres h, Hs.target, Hs.names, ?_⟩
      intro member info hmember hfindm
      obtain ⟨sinfo, hs⟩ := Hs.members.find hmember
      have := I.sourcePres hs
      rw [hfindm] at this
      cases this
      exact Hs.parameters member _ hmember hs
    · cases he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hinfo
      have hid : i < decl.types.length := by rw [I.infos_length, I.types_length] at hi; exact hi
      obtain ⟨_, _, hn, hall, hnp, -⟩ := I.infoAt i hid
      have hmembers : ∀ k (hk : k < decl.types.length),
          ctorEnv.find? decl.types[k].name = some (.inductInfo (I.H.infos[k]'(by
            rw [I.infos_length, I.types_length]; exact hk))) := by
        intro k hk
        obtain ⟨hl, _, hn', -⟩ := I.infoAt k hk
        rw [← hn']; exact I.headerPres (I.headerEnv_self (List.getElem_mem hl))
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hall]
        have : ∀ (l : List VInductiveType), (∀ T ∈ l, ∃ v, ctorEnv.find? T.name =
            some (.inductInfo v)) → InductiveMemberInfos ctorEnv (l.map (·.name)) := by
          intro l hl
          induction l with
          | nil => exact .nil
          | cons T l ih =>
            obtain ⟨v, hv⟩ := hl T (.head _)
            exact .cons hv (ih fun T' h' => hl T' (.tail _ h'))
        apply this
        intro T hT
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hT
        exact ⟨_, hmembers k hk⟩
      · rw [hall, ← hname, hn]; exact List.mem_map_of_mem (List.getElem_mem hid)
      · rw [hall]; exact I.typeNames_nodup
      · intro member minfo hmember hfindm
        rw [hall] at hmember
        obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hmember
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hT
        rw [hmembers k hk] at hfindm
        cases hfindm
        obtain ⟨_, _, _, _, hnp', -⟩ := I.infoAt k hk
        rw [hnp', hnp]
  · cases he

/-- Common-parameter alignment of the constructor environment, from that of the source
environment and the constructor shapes of the declaration. -/
theorem constructorParameterAlignment {safety : DefinitionSafety}
    (Hsource : ConstructorParameterAlignment safety c.env sourceEnv) :
    ConstructorParameterAlignment safety ctorEnv I.ctorVEnv := by
  intro familyName familyInfo hfamily hvisible j hj
  rcases I.ctorEnv_cases hfamily with h | ⟨_, _, he, _⟩
  · rcases I.headerEnv_cases h with h | ⟨info, hinfo, he, hname⟩
    · obtain ⟨C⟩ := Hsource familyName familyInfo h hvisible j hj
      exact ⟨C.rebaseKernel (I.sourcePres C.lookup) (I.sourceLE.trans I.headerLE)⟩
    · cases he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hinfo
      have hkd : k < decl.types.length := by rw [I.infos_length, I.types_length] at hk; exact hk
      obtain ⟨_, hks, hn, -, hnp, -, hlp, hunsafe, hctorsI, hctorsD⟩ := I.infoAt k hkd
      obtain ⟨_, hctors⟩ := I.ctorTrAt k hks
      have hjs : j < indTypes[k].ctors.length := by rw [hctorsI] at hj; simpa using hj
      have hjd : j < decl.types[k].ctors.length := by rw [hctorsD] at hj; simpa using hj
      have hmem := ctorInfoAt (stats := stats) (c := c) (isUnsafe := isUnsafe) k hks j hjs
      have hname' : I.H.infos[k].ctors[j] = indTypes[k].ctors[j].name := by simp [hctorsI]
      have hnameD : I.H.infos[k].ctors[j] = decl.types[k].ctors[j].name := by simp [hctorsD]
      obtain ⟨_, hdn⟩ := I.indNameAt k hks
      let C : CtorInfoCoherentAt ctorEnv familyName I.H.infos[k] j hj := {
        info := AddInductive.constructorInfo stats c.lparams isUnsafe indTypes[k] j
          indTypes[k].ctors[j]
        lookup := by rw [hname']; exact I.ctorEnv_self hmem
        induct := by simp [AddInductive.constructorInfo, ← hname, hn, hdn]
        cidx := rfl
        numParams := by simp [AddInductive.constructorInfo, I.params_size, I.H.nparams, hnp]
        levelParams := by simp [AddInductive.constructorInfo, hlp]
        isUnsafe := by simp [AddInductive.constructorInfo, hunsafe] }
      refine ConstructorParameterAlignmentAt.ofShapes (decl := decl) C I.checkingCtor.wf
        decl.types[k] decl.types[k].ctors[j] ?_ ?_ (I.typeUvars _ (List.getElem_mem hkd))
        (I.constructorUvars _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hkd,
          List.getElem_mem hjd⟩))
        (by rw [hlp, I.H.uvars]) hnp
        (I.H.headers.typeShapes _ (List.getElem_mem hkd))
        (I.K.shapes.ctorShape (List.getElem_mem hkd) (List.getElem_mem hjd))
        (I.sourceLE.trans I.headerLE) I.headerLE
      · rw [← hname, hn]
        exact I.headerLE.constants (VEnv.addConstVals_get I.H.typesAdded
          (List.mem_map_of_mem (List.getElem_mem hkd)))
      · rw [hnameD]
        exact VEnv.addConstVals_get I.ctorsAdded
          (List.mem_flatMap.mpr ⟨_, List.getElem_mem hkd, List.getElem_mem hjd⟩)
  · cases he

end CtorInstall

-- WAVE 2 install COMPAT: the primitive fields of `CtorInstall` on the ordinary path, where no
-- constructor name is a primitive.
theorem CtorInstall.ordinaryPrimitives {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool}
    {depth : Nat} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment} {classes : List (List (List Bool))}
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv)
    (K : ConstructorsChecked H.toData classes)
    (map_eq : ctorEnv.constants = insertConsts headerEnv.constants
      ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map .ctorInfo))
    (fresh : ∀ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
      headerEnv.find? cval.name = none)
    (nodup : ((ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name)).Nodup)
    (nprim : ∀ cval ∈ ctorInfos stats c.lparams isUnsafe indTypes.toList,
      ¬ Kernel.Environment.primitives.contains cval.name)
    (nprimFam : ∀ T ∈ decl.types, ¬ Kernel.Environment.primitives.contains T.name) :
    (∀ venv', H.context.venv.addConstVals decl.constructorConstants = some venv' →
      venv'.HasPrimitives) ∧
    (∀ {n ci}, ctorEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []) ∧
    (∀ venv', H.context.venv.addConstVals decl.constructorConstants = some venv' →
      checkPositivityStep.AvailableLiteralDisjoint venv' stats.indConsts) := by
  have hnames : decl.constructorConstants.map (·.name) =
      (ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name) := by
    rw [ctorInfos_names]
    simp only [VInductDecl.constructorConstants, List.map_flatMap]
    have go : ∀ {sources : List InductiveType} {targets : List VInductiveType},
        List.Forall₂ (fun (source : InductiveType) (target : VInductiveType) =>
          List.Forall₂ (fun (ctor : Constructor) (ctor' : VConstVal) =>
            TrSourceConst H.context.venv c.lparams ctor.name ctor.type ctor')
            source.ctors target.ctors) sources targets →
        targets.flatMap (fun t => t.ctors.map (·.name)) =
          sources.flatMap (fun t => t.ctors.map (·.name)) := by
      intro sources targets h
      induction h with
      | nil => rfl
      | @cons s t ss ts hst _ ih =>
        simp only [List.flatMap_cons, ih]
        congr 1
        exact (trSourceConst_names hst).symm
    exact go K.ctorTr
  have hnp : ∀ v ∈ decl.constructorConstants,
      ¬ Kernel.Environment.primitives.contains v.name := by
    intro v hv hp
    have hmem : v.name ∈ (ctorInfos stats c.lparams isUnsafe indTypes.toList).map (·.name) := by
      rw [← hnames]; exact List.mem_map_of_mem hv
    obtain ⟨cval, hcval, he⟩ := List.mem_map.mp hmem
    exact nprim cval hcval (he ▸ hp)
  have hwfH : headerEnv.constants.WF := H.context.checking.tr.map_wf
  have hfr : ∀ ci ∈ (ctorInfos stats c.lparams isUnsafe indTypes.toList).map
      ConstantInfo.ctorInfo, headerEnv.find? ci.name = none := by
    intro ci hci
    obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
    exact fresh cval hcval
  have hnd : (((ctorInfos stats c.lparams isUnsafe indTypes.toList).map
      ConstantInfo.ctorInfo).map (·.name)).Nodup := by
    rw [List.map_map]; exact nodup
  refine ⟨fun venv' h => CtorInstall.HasPrimitives_addConstVals
    H.context.checking.hasPrimitives hnp h, fun {n ci} h hp => ?_, fun venv' h => ?_⟩
  rotate_left
  · have Hlit := H.checkedAvailableLiteralDisjoint nprimFam
    have hsame : ∀ name, Kernel.Environment.primitives.contains name →
        venv'.constants name = H.context.venv.constants name := fun name hp =>
      VEnv.addConstVals_constants_of_forall_ne h fun ci hci e => hnp ci hci (e ▸ hp)
    intro lit hlit
    apply Hlit lit
    cases lit with
    | natVal _ =>
      obtain ⟨ci, hci⟩ := hlit
      exact ⟨ci, by rwa [hsame _ (by simp [Kernel.Environment.primitives, NameSet.contains,
        NameSet.ofList])] at hci⟩
    | strVal _ =>
      obtain ⟨⟨ci, hci⟩, ⟨cj, hcj⟩⟩ := hlit
      exact ⟨⟨ci, by rwa [hsame _ (by simp [Kernel.Environment.primitives, NameSet.contains,
        NameSet.ofList])] at hci⟩, ⟨cj, by rwa [hsame _ (by simp [Kernel.Environment.primitives,
        NameSet.contains, NameSet.ofList])] at hcj⟩⟩
  rcases insertConsts_env_cases map_eq hwfH hfr hnd h with h | ⟨hmem, hname⟩
  · exact H.context.checking.safePrimitives h hp
  · obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hmem
    have hn : cval.name = n := hname
    subst hn
    exact absurd hp (nprim cval hcval)

end VerifyInductive
end Lean4Lean
