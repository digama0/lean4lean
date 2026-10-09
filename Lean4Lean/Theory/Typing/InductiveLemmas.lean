import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
namespace VEnv

theorem addDefEqRules_le {env : VEnv} {dfs : List VDefEq} : env ≤ env.addDefEqRules dfs := by
  induction dfs generalizing env with
  | nil => exact .rfl
  | cons df dfs ih =>
      exact VEnv.addDefEq_le.trans ih

theorem addDefEqRules_defeqs_iff_mem_or {env : VEnv} {rules : List VDefEq} :
    (env.addDefEqRules rules).defeqs df ↔ df ∈ rules ∨ env.defeqs df := by
  induction rules generalizing env with
  | nil => simp [VEnv.addDefEqRules]
  | cons rule rules ih =>
    simp only [VEnv.addDefEqRules, ih, VEnv.addDefEq, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

theorem addConsts_eq_addConstVals {env : VEnv} {cis : List VDefVal} :
    env.addConsts cis = env.addConstVals (cis.map (·.toVConstVal)) := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, List.map_cons, VEnv.addConstVals]
    cases env.addConst ci.name ci.toVConstant with
    | none => rfl
    | some middle => exact ih (env := middle)

theorem addDefEqs_eq_addDefEqRules {env : VEnv} {cis : List VDefVal} :
    env.addDefEqs cis = env.addDefEqRules (cis.map (·.toDefEq)) := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem addDefEqs_le : ∀ {cis' : List VDefVal} {venv : VEnv}, venv ≤ venv.addDefEqs cis'
  | [], _ => .rfl
  | ci :: cis, venv => by
    show venv ≤ VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis
    exact VEnv.addDefEq_le.trans addDefEqs_le

theorem _root_.Lean4Lean.VInductBlock.install_type_lookup (H : VInductBlock.install base block = some installed)
    (hvalue : value ∈ block.types) : installed.constants value.name = some value.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact ((VEnv.addConstVals_le hc).trans <| VEnv.addEliminators_addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans addDefEqRules_le).constants (VEnv.addConstVals_get ht hvalue)

theorem Ordered.addConstVals {env env' : VEnv} {cis : List VConstVal} (H : Ordered env)
    (hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (hadd : env.addConstVals cis = some env') : Ordered env' := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConstVals] at hadd; subst env'; exact H
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hci] at hadd
    | some env₁ =>
      simp [VEnv.addConstVals, hci] at hadd
      have hle := VEnv.addConst_le hci
      exact ih (.const H (hwf ci (by simp)) hci)
        (fun ci' hmem => (hwf ci' (by simp [hmem])).mono hle) hadd

theorem Ordered.addDefEqRules {env : VEnv} {dfs : List VDefEq} (H : Ordered env)
    (hwf : ∀ df ∈ dfs, df.WF env) : Ordered (env.addDefEqRules dfs) := by
  induction dfs generalizing env with
  | nil => exact H
  | cons df dfs ih =>
    exact ih (.defeq H (hwf df (by simp)))
      (fun df' hmem => (hwf df' (by simp [hmem])).mono VEnv.addDefEq_le)

theorem VInductBlock.WF.ordered (H : VInductBlock.WF env block)
    (hdecl : VInductDecl.WF env decl)
    (hcompile : VInductDecl.CompilesTo env decl block)
    (henv : Ordered env) (hinstall : VInductBlock.install env block = some env') :
    Ordered env' := by
  rcases H with
    ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs,
      htypesWF, hctorsWF, hrecsWF, hrulesWF⟩
  have h1 := henv.addConstVals htypesWF htypes
  have h2 := h1.addConstVals hctorsWF hctors
  have htypes' : env.addConstVals decl.typeConstants = some envTypes := by
    rwa [hcompile.types] at htypes
  have hparams := hdecl.sourceParameterWF htypes'
  have h3 := Ordered.inductProjections (es := block.eliminators) henv h2 hcompile.sourceNames hdecl.1.sourceTypes
    hdecl.1.2.2.2.1 (hdecl.1.constructorsWF_at htypes') hparams
    hparams.rawCtorShape
    hcompile.types hcompile.ctors
    hcompile.projections htypes hctors
  have h4 := h3.addConstVals hrecsWF hrecs
  have h5 := h4.addDefEqRules hrulesWF
  simp [VInductBlock.install, htypes, hctors, hrecs] at hinstall
  cases hinstall
  exact h5

/-- Declaration-level facts recoverable from a registered projection entry
alone.  Every entry originates from an exact source declaration whose family
and constructor constants are installed, whose constructor type is well
formed, whose header and raw constructor prefix agree with a common parameter
telescope, and whose constructor type is a raw syntactic telescope ending in a
valid application of the family. -/
theorem Ordered.projectionShape {env : VEnv} (H : Ordered env)
    {typeName : Name} {info : VProjectionInfo}
    (hproj : env.projections typeName info) :
    ∃ (decl : VInductDecl) (type : VInductiveType) (ctor : VConstVal),
      type ∈ decl.types ∧ ctor ∈ type.ctors ∧
      type.name = typeName ∧ ctor.uvars = decl.uvars ∧
      decl.uvars = info.uvars ∧ decl.nparams = info.nparams ∧
      type.numIndices = info.nindices ∧ type.resultLevel = info.resultLevel ∧
      ctor.name = info.ctorName ∧ ctor.type = info.ctorType ∧
      env.constants typeName = some type.toVConstant ∧
      env.IsType decl.uvars [] ctor.type ∧
      (∃ params, decl.TypeShape env params type ∧
        decl.CtorParameterShape env params ctor) ∧
      decl.RawCtorShape type ctor ∧ decl.sourceNames.Nodup := by
  induction H with
  | empty => cases hproj
  | const _ _ hadd ih =>
    rw [VEnv.addConst_projections hadd] at hproj
    rcases ih hproj with ⟨decl, type, ctor, htype, hctor, hname, hctorUvars,
      huvars, hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
      ⟨params, Hshape, Hparams⟩, Hraw, hnodup⟩
    have hle := VEnv.addConst_le hadd
    exact ⟨decl, type, ctor, htype, hctor, hname, hctorUvars, huvars, hnparams,
      hindices, hlevel, hctorName, hctorType, hle.constants hlookup, hwf.mono hle,
      ⟨params, Hshape.mono hle, Hparams.mono hle⟩, Hraw, hnodup⟩
  | @defeq env' df' _ _ ih =>
    rcases ih hproj with ⟨decl, type, ctor, htype, hctor, hname, hctorUvars,
      huvars, hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
      ⟨params, Hshape, Hparams⟩, Hraw, hnodup⟩
    have hle : env' ≤ env'.addDefEq df' := VEnv.addDefEq_le
    exact ⟨decl, type, ctor, htype, hctor, hname, hctorUvars, huvars, hnparams,
      hindices, hlevel, hctorName, hctorType, hle.constants hlookup, hwf.mono hle,
      ⟨params, Hshape.mono hle, Hparams.mono hle⟩, Hraw, hnodup⟩
  | @eliminator env' key schema _ ih =>
    rcases ih hproj with ⟨decl, type, ctor, htype, hctor, hname, hctorUvars,
      huvars, hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
      ⟨params, Hshape, Hparams⟩, Hraw, hnodup⟩
    have hle : env' ≤ env'.addEliminator key schema := VEnv.addEliminator_le
    exact ⟨decl, type, ctor, htype, hctor, hname, hctorUvars, huvars, hnparams,
      hindices, hlevel, hctorName, hctorType, hle.constants hlookup, hwf.mono hle,
      ⟨params, Hshape.mono hle, Hparams.mono hle⟩, Hraw, hnodup⟩
  | @inductProjections base envTypes envCtors decl block _es
      hbase hctorsOrdered hsource htypesWF hconstructorUvars hctorsWF hparams hshape
      htypesSource hctorsSource hprojections htypes hctors ihBase ihCtors =>
    rw [VEnv.addProjections_iff] at hproj
    simp only [VEnv.addEliminators_projections] at hproj
    rcases hproj with hnew | hold
    · rcases hnew with ⟨entry, hentry, rfl, rfl⟩
      rw [hprojections] at hentry
      rcases VInductDecl.projectionEntries_origin hentry with
        ⟨type, htype, ctor, hctorsType, rfl⟩
      have hctorMem : ctor ∈ type.ctors := by
        rw [hctorsType]
        simp
      have hctorConst : ctor ∈ decl.constructorConstants := by
        simp only [VInductDecl.constructorConstants, List.mem_flatMap]
        exact ⟨type, htype, hctorMem⟩
      have hle : envTypes ≤ (envCtors.addEliminators _es).addProjections block.projections :=
        (VEnv.addConstVals_le hctors).trans VEnv.addEliminators_addProjections_le
      have hbaseLe : base ≤ (envCtors.addEliminators _es).addProjections block.projections :=
        (VEnv.addConstVals_le htypes).trans hle
      have htypeValue : type.toVConstVal ∈ block.types := by
        rw [htypesSource]
        exact List.mem_map.mpr ⟨type, htype, rfl⟩
      have hlookup := hle.constants (VEnv.addConstVals_get htypes htypeValue)
      have huvars := hconstructorUvars ctor hctorConst
      have hwf : ((envCtors.addEliminators _es).addProjections block.projections).IsType
          decl.uvars [] ctor.type := by
        have := (hctorsWF ctor hctorConst).mono hle
        change ((envCtors.addEliminators _es).addProjections block.projections).IsType
          ctor.uvars [] ctor.type at this
        rwa [huvars] at this
      have htypes' : base.addConstVals decl.typeConstants = some envTypes := by
        rwa [htypesSource] at htypes
      rcases hparams with ⟨params, envTypes', htypes'', Htypes, Hctors, _⟩
      cases Option.some.inj (htypes''.symm.trans htypes')
      exact ⟨decl, type, ctor, htype, hctorMem, rfl, huvars, rfl, rfl, rfl, rfl,
        rfl, rfl, hlookup, hwf,
        ⟨params, (Htypes type htype).mono hbaseLe,
          (Hctors type htype ctor hctorMem).mono hle⟩,
        hshape type htype ctor hctorMem, hsource⟩
    · rcases ihCtors hold with ⟨decl', type, ctor, htype, hctor, hname, hctorUvars,
        huvars, hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
        ⟨params, Hshape, Hparams⟩, Hraw, hnodup⟩
      have hle : envCtors ≤ (envCtors.addEliminators _es).addProjections block.projections :=
        VEnv.addEliminators_addProjections_le
      exact ⟨decl', type, ctor, htype, hctor, hname, hctorUvars, huvars, hnparams,
        hindices, hlevel, hctorName, hctorType, hle.constants hlookup,
        hwf.mono hle, ⟨params, Hshape.mono hle, Hparams.mono hle⟩, Hraw, hnodup⟩

theorem addInduct_WF (henv : Ordered env) (hdecl : VInductDecl.WF env decl)
    (henv' : VEnv.AddInduct env decl env') : Ordered env' := by
  cases henv' with
  | intro _ hcompile hblock _ hinstall =>
    exact VInductBlock.WF.ordered hblock hdecl hcompile henv hinstall
