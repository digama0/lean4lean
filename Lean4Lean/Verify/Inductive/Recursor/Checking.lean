import Lean4Lean.Verify.Inductive.Recursor.Recs
import Lean4Lean.Verify.Inductive.Install.RecursorShapesOf

/-! # The checking invariant at the recursor stage

The output of the recursor phase (the constructor environment with the recursors inserted, and
the projection stage with the recursor constants) is a valid checking environment: its block
descriptor is built from the source environment's (`InstalledBlocks.addCtorStage`) with the
new recursors, their K clause (`kLike`) and shapes (`recursorShapesOf`); the equation heads and
the quotient facts extend from the constructor stage. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem AddConstants.pats_eq
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment} {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv) : outVEnv.pats = venv.pats := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ hadd _ _ ih => rw [ih, VEnv.addConst_pats hadd]

theorem AddConstants.projections_eq
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment} {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    outVEnv.projections = venv.projections := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ hadd _ _ ih => rw [ih, VEnv.addConst_projections hadd]

namespace RecursorInput

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}

/-- Constants of the source environment stay in the constructor environment. -/
theorem sourcePres (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) {n : Name} {ci : ConstantInfo} (h : c.env.find? n = some ci) :
    ctorEnv.find? n = some ci := by
  have hWFc : c.env.constants.WF := R.headers.sourceContext.checking.tr.map_wf
  have hWFh : R.headerEnv.constants.WF := R.headers.context.checking.map_wf
  have hWFo : ctorEnv.constants.WF := R.context.checking.tr.map_wf
  have hfreshH : ∀ d ∈ R.headers.infos.map ConstantInfo.inductInfo,
      c.env.constants.find? d.name = none := by
    intro d hd
    obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hd
    have := R.headers.fresh info hinfo
    rwa [Kernel.Environment.find?, hWFc.find?'_eq_find?] at this
  have hfreshC : ∀ d ∈ R.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo),
      R.headerEnv.constants.find? d.name = none := by
    intro d hd
    obtain ⟨iv, hiv, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hd
    have := R.fresh iv hiv cv hcv
    rwa [Kernel.Environment.find?, hWFh.find?'_eq_find?] at this
  rw [Kernel.Environment.find?, hWFc.find?'_eq_find?] at h
  have hH : R.headerEnv.constants.find? n = some ci := by
    rw [R.headers.map_eq]; exact insertConsts_find?_mono_of_fresh hWFc.map₂ hfreshH h
  rw [Kernel.Environment.find?, hWFo.find?'_eq_find?, R.map_eq]
  exact insertConsts_find?_mono_of_fresh hWFh.map₂ hfreshC hH

end RecursorInput

namespace RecursorInstallation

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

theorem ctorMapWF (H : RecursorInstallation R outEnv) : H.localContext.env.constants.WF := by
  rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf

theorem outWF (H : RecursorInstallation R outEnv) : outEnv.constants.WF :=
  H.installed.targetMapWF H.ctorMapWF

theorem outPres (H : RecursorInstallation R outEnv) {n : Name} {ci : ConstantInfo}
    (h : ctorEnv.find? n = some ci) : outEnv.find? n = some ci :=
  H.installed.preservesFind H.ctorMapWF (by rw [H.localExtends.env_eq]; exact h)

theorem outOrigin (H : RecursorInstallation R outEnv) {n : Name} {ci : ConstantInfo}
    (h : outEnv.find? n = some ci) :
    ctorEnv.find? n = some ci ∨ ∃ r ∈ H.rvals, ci = .recInfo r := by
  rcases H.installed.origin H.ctorMapWF h with hold | ⟨entry, hentry, -, rfl⟩
  · left; rw [H.localExtends.env_eq] at hold; exact hold
  · right
    have hmem : entry.1 ∈ H.entries.map Prod.fst := List.mem_map_of_mem hentry
    rw [H.entries_fst] at hmem
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hmem
    exact ⟨r, hr, he.symm⟩

theorem ownersPresent (H : RecursorInstallation R outEnv) :
    ConstructorOwnersPresent outEnv := by
  intro name info hfind
  rcases H.outOrigin hfind with h | ⟨r, -, he⟩
  · obtain ⟨owner, hown, hmem, hu⟩ := R.context.checking.constructorOwners name info h
    exact ⟨owner, H.outPres hown, hmem, hu⟩
  · cases he

theorem cover (H : RecursorInstallation R outEnv) :
    ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      c.env.find? T.name = none := by
  intro T hT
  obtain ⟨info, hinfo, htr⟩ := List.Forall₂.forall_exists_r R.headers.trHeaders T hT
  have hname : info.name = T.name := htr.1.2
  refine ⟨info, ?_, ?_⟩
  · rw [← hname]; exact H.outPres (R.headerInfo_find hinfo)
  · rw [← hname]; exact R.headers.fresh info hinfo

theorem recsOfNew (H : RecursorInstallation R outEnv) {n : Name} {r : RecursorVal}
    (h : outEnv.find? n = some (.recInfo r)) (hnone : c.env.find? n = none) : r ∈ H.rvals := by
  rcases H.outOrigin h with h | ⟨r', hr', he⟩
  · rcases R.find?_origin h with h | h | h
    · rw [h] at hnone; cases hnone
    · obtain ⟨_, _, he⟩ := List.mem_map.mp h; cases he
    · obtain ⟨_, _, h⟩ := List.mem_flatMap.mp h
      obtain ⟨_, _, he⟩ := List.mem_map.mp h; cases he
  · cases he; exact hr'

theorem recFind (H : RecursorInstallation R outEnv) :
    ∀ r ∈ H.rvals, outEnv.find? r.name = some (.recInfo r) ∧ c.env.find? r.name = none := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.rvals_mem hr
  have hmem : (H.entries[owner.val]'(H.entries_lt owner)) ∈ H.entries := List.getElem_mem _
  have h := H.installed.findOfMem H.ctorMapWF
    (info := (H.entries[owner.val]'(H.entries_lt owner)).1)
    (value := (H.entries[owner.val]'(H.entries_lt owner)).2) hmem
  rw [H.entry_fst owner] at h
  refine ⟨h, ?_⟩
  cases hc : c.env.find? (H.rvalAt owner).name with
  | none => rfl
  | some ci =>
    have := R.sourcePres hc
    rw [H.freshRvals _ (by simp [rvals, List.mem_ofFn])] at this
    cases this

theorem recMajor (H : RecursorInstallation R outEnv) :
    ∀ r ∈ H.rvals, ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info) := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.rvals_mem hr
  have M := H.rvalAt_metadata owner
  obtain ⟨family, hfamily, hname, -⟩ := H.generator.models.family owner
  obtain ⟨info, hinfo, -⟩ := H.familyInfo family hfamily
  refine ⟨info, ?_⟩
  rw [M.major]
  have hname' : H.generationSignature.families[owner].name = family.name := hname
  rw [hname', Lean.Kernel.Environment.find?, H.outWF.find?'_eq_find?]
  exact hinfo

theorem outVEnvLE (H : RecursorInstallation R outEnv) : R.envP ≤ H.outVEnv := by
  rw [← R.envP_eq]; exact H.installed.le

theorem declRegistered (H : RecursorInstallation R outEnv) :
    InstalledBlocks.DeclRegistered H.outVEnv decl where
  typeUvars T hT := by
    obtain ⟨_, _, htr⟩ := List.Forall₂.forall_exists_r R.headers.trSources T hT
    exact htr.1.uvars.trans R.headers.uvars.symm
  constructorUvars := TrInductDeclCore.constructorUvars R.core
  family i hi := by
    apply (R.headerLE.trans (VEnv.addProjections_le.trans H.outVEnvLE)).constants
    exact VEnv.addConstVals_get R.headers.typesAdded
      (List.mem_map_of_mem (List.getElem_mem hi))
  ctor i k hi hk := by
    apply (VEnv.addProjections_le.trans H.outVEnvLE).constants
    exact VEnv.addConstVals_get R.core.ctorsAdded
      (List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, List.getElem_mem hk⟩)
  projections e he :=
    H.outVEnvLE.projections (VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩))

theorem projOrigin (H : RecursorInstallation R outEnv) {S : Name} {info : VProjectionInfo}
    (h : H.outVEnv.projections S info) :
    R.headers.sourceContext.venv.projections S info ∨ ⟨S, info⟩ ∈ decl.projectionEntries := by
  rw [H.installed.projections_eq, R.contextVEnv] at h
  rcases VEnv.addProjections_iff.mp h with ⟨e, he, rfl, rfl⟩ | h
  · exact .inr he
  · left
    rw [R.headers.sourceContextVEnv]
    rw [VEnv.addConstVals_projections_eq R.core.ctorsAdded,
      VEnv.addConstVals_projections_eq R.headers.typesAdded] at h
    exact h

theorem trRecs (H : RecursorInstallation R outEnv) :
    List.Forall₂ (TrRecursor c.safety R.envP H.outVEnv outEnv.constants) H.rvals H.recs := by
  apply List.forall₂_of_getElem (by simp)
  intro i h₁ h₂
  have hi : i < H.generationSignature.families.size := by simpa using h₁
  simp only [rvals, recs, List.getElem_ofFn]
  exact H.trRecursor ⟨i, hi⟩

theorem metadataAll (H : RecursorInstallation R outEnv) :
    List.Forall₂ (fun (owner : Fin H.generationSignature.families.size) rval =>
      InductiveSignature.RecursorMetadata H.generationInstance H.outVEnv owner rval)
      (List.finRange H.generationSignature.families.size) H.rvals := by
  apply List.forall₂_of_getElem (by simp)
  intro i h₁ h₂
  have hi : i < H.generationSignature.families.size := by simpa using h₁
  simp only [rvals, List.getElem_ofFn, List.getElem_finRange]
  exact H.rvalAt_metadata ⟨i, hi⟩

theorem coverageAll (H : RecursorInstallation R outEnv) :
    List.Forall₂ (fun (owner : Fin H.generationSignature.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule H.generationInstance H.outVEnv
        rval.levelParams) (H.generationSignature.ownedConstructors owner) rval.rules)
      (List.finRange H.generationSignature.families.size) H.rvals := by
  apply List.forall₂_of_getElem (by simp)
  intro i h₁ h₂
  have hi : i < H.generationSignature.families.size := by simpa using h₁
  simp only [rvals, List.getElem_ofFn, List.getElem_finRange]
  exact H.rulesCoverage ⟨i, hi⟩

theorem recs_mem (H : RecursorInstallation R outEnv) {r : VRecursor}
    (h : r ∈ H.recs) : ∃ owner, H.modelRecursor owner = r := by
  simpa [recs, List.mem_ofFn] using h

theorem rulesCtorAll (H : RecursorInstallation R outEnv) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules,
      ∃ ci, R.ctorVEnv.constants ru.ctor = some ci ∧
        ci.type.CtorShape (ru.ctorParams + ru.nfields) := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.recs_mem hr
  exact H.rulesCtor owner

theorem recsFind (H : RecursorInstallation R outEnv) :
    ∀ r ∈ H.recs, H.outVEnv.constants r.name = some r.toVConstVal.toVConstant := by
  intro r hr
  have h := H.installed.abstract
  rw [H.entries_snd] at h
  exact VEnv.addConstVals_get h (List.mem_map_of_mem hr)

theorem ctorNumParams (H : RecursorInstallation R outEnv) {n : Name} {cval : ConstructorVal}
    (h : outEnv.constants.find? n = some (.ctorInfo cval))
    (hsrc : ∃ src ∈ decl.constructorConstants, src.name = n) :
    cval.numParams = decl.nparams := by
  have h' : outEnv.find? n = some (.ctorInfo cval) := by
    rwa [Lean.Kernel.Environment.find?, H.outWF.find?'_eq_find?]
  have hctor : ctorEnv.find? n = some (.ctorInfo cval) := by
    rcases H.outOrigin h' with h | ⟨_, _, he⟩
    · exact h
    · cases he
  obtain ⟨src, hsrcMem, rfl⟩ := hsrc
  have hname : src.name ∈ (R.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo).map
      (·.name) := by rw [R.ctorInfoNames]; exact List.mem_map_of_mem hsrcMem
  obtain ⟨ci, hci, hcin⟩ := List.mem_map.mp hname
  obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hci
  have h2 := R.ctorInfo_find hiv hcv
  have hcin' : cv.name = src.name := hcin
  rw [hcin', hctor] at h2
  cases h2
  exact R.ctor_numParams iv hiv _ hcv

theorem shapes (H : RecursorInstallation R outEnv) :
    ∀ rval ∈ H.rvals, RecursorShapesAt outEnv.constants H.outVEnv rval := by
  have hlevels : H.generationInstance.levels.length = H.generationSignature.uvars := by
    have h1 : H.generationInstance.levels.length = c.lparams.length := by
      change H.generator.generation.levels.length = _
      rw [H.generator.levels, recursorDeclarationAbstractLevels_length]
    have h2 : H.generationSignature.uvars = decl.uvars := H.generator.models.uvars
    rw [h1, h2, R.headers.uvars]
  exact recursorShapesOf H.generationInstance (safety := c.safety) (envA := R.envP)
    H.generator.models hlevels R.headers.typesAdded R.core.ctorsAdded
    (TrInductDeclCore.sourceNames_nodup R.core) R.formation.rawShapes
    (R.ctorLE.trans H.installed.le) H.recsFind H.recs_recursors H.trRecs H.metadataAll
    H.coverageAll H.rulesCtorAll (fun h hsrc => H.ctorNumParams h hsrc)

/-- The equation heads of the output, extended from the constructor stage. -/
theorem equationHeads (H : RecursorInstallation R outEnv) :
    EquationHeadsCoherent outEnv.constants H.outVEnv :=
  R.context.checking.equationHeads.extendSimple
    (fun h => H.outFind ((by
      rwa [Lean.Kernel.Environment.find?, R.context.checking.tr.map_wf.find?'_eq_find?])))
    (fun df h => H.installed.defeqs df h)
    (fun p r h => by rwa [H.installed.pats_eq] at h)

/-- The recursor-stage environment is a valid checking environment of the output. -/
theorem checkingValid (H : RecursorInstallation R outEnv) :
    CheckingEnv.Valid c.safety outEnv H.outVEnv := by
  have hwfc : c.env.constants.WF := R.headers.sourceContext.checking.tr.map_wf
  have hnodup : (decl.types.map (·.name)).Nodup := by
    have h := TrInductDeclCore.sourceNames_nodup R.core
    rw [VInductDecl.sourceNames] at h
    have := (List.nodup_append.mp h).1
    simpa [VInductDecl.typeConstants, List.map_map, Function.comp_def] using this
  have hle : R.headers.sourceContext.venv ≤ H.outVEnv := by
    rw [R.headers.sourceContextVEnv]
    exact R.sourceLE.trans (R.headerLE.trans (R.ctorLE.trans H.installed.le))
  have hblocks := R.headers.sourceContext.checking.blocks.addCtorStage
    R.headers.sourcePresent hwfc H.validCore.tr (fun h => H.outPres (R.sourcePres h)) hle
    H.inductInfos H.cover hnodup H.ownersPresent H.rvals (fun h hnone => H.recsOfNew h hnone)
    H.recFind H.recMajor (fun r hr _ => H.kLike r hr) H.declRegistered
    (fun h => H.projOrigin h) (fun r hr _ => H.shapes r hr)
  have hpres : ∀ {n ci}, ctorEnv.constants.find? n = some ci →
      outEnv.constants.find? n = some ci := fun h => H.outFind (by
        rwa [Lean.Kernel.Environment.find?, R.context.checking.tr.map_wf.find?'_eq_find?])
  exact H.validCore.toValid hblocks H.equationHeads fun hq =>
    (R.context.checking.quot (by rw [← H.quotInitEq]; exact hq)).extend hpres
      H.installed.le H.equationHeads

end RecursorInstallation

end VerifyInductive
end Lean4Lean
