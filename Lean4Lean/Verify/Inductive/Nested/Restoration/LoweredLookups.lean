import Lean4Lean.Verify.Inductive.Nested.Restoration.Run
import Lean4Lean.Verify.Inductive.Constructor.Environment
import Lean4Lean.Verify.Inductive.Recursor.Checking

/-! # Lookups in the lowered environment

The constants the restoration fold reads from the lowered environment: the kernel headers of
the header phase, the constructors of the constructor phase (`ConstructorCheck.ivals`) and the
recursors of the recursor phase, read off the `insertConsts` maps of the phase interfaces
(`HeaderData.map_eq`, `ConstructorCheck.map_eq`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace ConstructorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams : Nat} {isUnsafe : Bool} {depth : Nat} {sourceEnv : VEnv}
  {indTypes : Array InductiveType} {ctorEnv : Environment}
  (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
include R

theorem sourceMapWF : c.env.constants.WF := R.headers.sourceContext.checking.tr.map_wf

theorem infoNames : R.headers.infos.map (·.name) = decl.types.map (·.name) := by
  have go : ∀ {infos : List InductiveVal} {types : List VInductiveType},
      List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
        TrConstVal c.safety sourceEnv (.inductInfo info) t.toVConstVal ∧
        info.ctors = t.ctors.map (·.name)) infos types →
      infos.map (·.name) = types.map (·.name) := by
    intro infos types h
    induction h with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.2
  exact go R.headers.trHeaders

theorem sourceNames_nodup : decl.sourceNames.Nodup := TrInductDeclCore.sourceNames_nodup R.core

theorem typeNames_nodup : (decl.types.map (·.name)).Nodup := by
  have h := (List.nodup_append.mp R.sourceNames_nodup).1
  simpa [VInductDecl.typeConstants, List.map_map, Function.comp_def] using h

theorem infoCis_fresh :
    ∀ ci ∈ R.headers.infos.map ConstantInfo.inductInfo, c.env.find? ci.name = none := by
  intro ci hci
  obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hci
  exact R.headers.fresh info hinfo

theorem infoCis_nodup : ((R.headers.infos.map ConstantInfo.inductInfo).map (·.name)).Nodup := by
  have : (R.headers.infos.map ConstantInfo.inductInfo).map (·.name) =
      R.headers.infos.map (·.name) := by simp only [List.map_map]; rfl
  rw [this, R.infoNames]; exact R.typeNames_nodup

theorem headerMapWF : R.headerEnv.constants.WF :=
  insertConsts_map_wf R.headers.map_eq R.sourceMapWF R.infoCis_fresh R.infoCis_nodup

/-- The kernel constructors of the block, flattened. -/
abbrev ctorCis : List ConstantInfo := R.ivals.flatMap fun iv => iv.2.map .ctorInfo

theorem ctorCis_fresh : ∀ ci ∈ R.ctorCis, R.headerEnv.find? ci.name = none := by
  intro ci hci
  obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
  exact R.fresh iv hiv cval hcval

theorem ctorCis_names : R.ctorCis.map (·.name) = decl.constructorConstants.map (·.name) := by
  have go : ∀ {ivs : List (InductiveVal × List ConstructorVal)} {types : List VInductiveType},
      List.Forall₂ (fun (iv : InductiveVal × List ConstructorVal) (t : VInductiveType) =>
        TrIndType c.safety sourceEnv R.headers.context.venv iv.1 iv.2 t) ivs types →
      (ivs.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo).map (·.name) =
        (types.flatMap (·.ctors)).map (·.name) := by
    intro ivs types h
    induction h with
    | nil => rfl
    | @cons iv t ivs types h _ ih =>
      simp only [List.flatMap_cons, List.map_append, ih]
      congr 1
      have hc := h.ctors
      clear ih h
      generalize iv.2 = cvals at hc ⊢
      generalize t.ctors = ts at hc ⊢
      induction hc with
      | nil => rfl
      | cons h _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) h.1.2
  exact go R.trTypes

theorem ctorCis_nodup : (R.ctorCis.map (·.name)).Nodup := by
  rw [R.ctorCis_names]; exact (List.nodup_append.mp R.sourceNames_nodup).2.1

theorem ctorMapWF : ctorEnv.constants.WF :=
  insertConsts_map_wf R.map_eq R.headerMapWF R.ctorCis_fresh R.ctorCis_nodup

theorem headerPres {n : Name} {ci : ConstantInfo} (h : R.headerEnv.find? n = some ci) :
    ctorEnv.find? n = some ci :=
  insertConsts_env_mono R.map_eq R.headerMapWF R.ctorCis_fresh R.ctorCis_nodup h

theorem headerEnv_self {info : InductiveVal} (h : info ∈ R.headers.infos) :
    R.headerEnv.find? info.name = some (.inductInfo info) :=
  insertConsts_env_self R.headers.map_eq R.sourceMapWF R.infoCis_fresh R.infoCis_nodup
    (List.mem_map_of_mem h)

theorem ctorEnv_header {info : InductiveVal} (h : info ∈ R.headers.infos) :
    ctorEnv.find? info.name = some (.inductInfo info) :=
  R.headerPres (R.headerEnv_self h)

theorem ctorEnv_ctor {iv : InductiveVal × List ConstructorVal} (hiv : iv ∈ R.ivals)
    {cval : ConstructorVal} (hc : cval ∈ iv.2) :
    ctorEnv.find? cval.name = some (.ctorInfo cval) :=
  insertConsts_env_self R.map_eq R.headerMapWF R.ctorCis_fresh R.ctorCis_nodup
    (List.mem_flatMap.mpr ⟨iv, hiv, List.mem_map_of_mem hc⟩)

theorem headerEnv_cases {n : Name} {ci : ConstantInfo} (h : R.headerEnv.find? n = some ci) :
    c.env.find? n = some ci ∨ ∃ info ∈ R.headers.infos, ci = .inductInfo info ∧ info.name = n := by
  rcases insertConsts_env_cases R.headers.map_eq R.sourceMapWF R.infoCis_fresh R.infoCis_nodup h
    with h | ⟨hmem, hname⟩
  · exact .inl h
  · obtain ⟨info, hinfo, rfl⟩ := List.mem_map.mp hmem
    exact .inr ⟨info, hinfo, rfl, hname⟩

theorem ctorEnv_cases {n : Name} {ci : ConstantInfo} (h : ctorEnv.find? n = some ci) :
    R.headerEnv.find? n = some ci ∨
      ∃ iv ∈ R.ivals, ∃ cval ∈ iv.2, ci = .ctorInfo cval ∧ cval.name = n := by
  rcases insertConsts_env_cases R.map_eq R.headerMapWF R.ctorCis_fresh R.ctorCis_nodup h with
    h | ⟨hmem, hname⟩
  · exact .inl h
  · obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hmem
    obtain ⟨cval, hcval, rfl⟩ := List.mem_map.mp hci
    exact .inr ⟨iv, hiv, cval, hcval, rfl, hname⟩

theorem infos_length : R.headers.infos.length = indTypes.size := by
  have h1 := congrArg List.length R.infoNames
  have h2 := List.Forall₂.length_eq R.core.types
  simp only [List.length_map] at h1
  rw [h1, ← h2, Array.length_toList]

/-- The kernel header and constructors of each lowered family (`inductiveTypeInfos`,
`familyCtorInfos`). -/
theorem family_of_mem {owner : InductiveType} (howner : owner ∈ indTypes.toList) :
    ∃ iv ∈ R.ivals, iv.1 ∈ R.headers.infos ∧ iv.1.name = owner.name ∧
      iv.1.ctors = owner.ctors.map (·.name) ∧
      iv.1.all = indTypes.toList.map (·.name) ∧ iv.1.levelParams = c.lparams ∧
      iv.1.isUnsafe = isUnsafe ∧ iv.2 = familyCtorInfos stats c.lparams isUnsafe owner := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp howner
  have hi' : i < R.headers.infos.length := by rw [R.infos_length]; simpa using hi
  have hinfo : R.headers.infos[i] = (AddInductive.inductiveTypeInfos stats nparams indTypes
      R.headers.numNested isUnsafe c.lparams).toList[i]'(by rw [← R.headers.infos_eq]; exact hi') := by
    simp only [R.headers.infos_eq]
  have hzip : i < (R.headers.infos.zip indTypes.toList).length := by
    simp only [List.length_zip, Array.length_toList]; exact Nat.lt_min.mpr ⟨hi', by simpa using hi⟩
  refine ⟨(R.headers.infos[i], familyCtorInfos stats c.lparams isUnsafe indTypes.toList[i]),
    ?_, List.getElem_mem hi', ?_⟩
  · rw [R.ivals_eq]
    exact List.mem_map.mpr ⟨_, List.getElem_mem hzip, by simp⟩
  · rw [hinfo]
    simp [AddInductive.inductiveTypeInfos]

/-- The kernel constructor of a lowered constructor. -/
theorem ctor_of_mem {owner : InductiveType} (howner : owner ∈ indTypes.toList)
    {ctor : Constructor} (hctor : ctor ∈ owner.ctors) :
    ∃ iv ∈ R.ivals, ∃ cval ∈ iv.2, cval.name = ctor.name ∧ cval.type = ctor.type ∧
      cval.levelParams = c.lparams ∧ cval.isUnsafe = isUnsafe ∧ cval.induct = owner.name := by
  obtain ⟨iv, hiv, -, -, -, -, -, -, hctors⟩ := R.family_of_mem howner
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
  have hj' : j < (familyCtorInfos stats c.lparams isUnsafe owner).length := by
    simpa [familyCtorInfos_length] using hj
  refine ⟨iv, hiv, _, by rw [hctors]; exact List.getElem_mem hj', ?_⟩
  rw [familyCtorInfos_getElem j hj']
  simp [AddInductive.constructorInfo]

theorem ctor_safety {iv : InductiveVal × List ConstructorVal} (hiv : iv ∈ R.ivals)
    {cval : ConstructorVal} (hc : cval ∈ iv.2) :
    c.safety ≤ (ConstantInfo.ctorInfo cval).safety := by
  obtain ⟨t, -, ht⟩ := List.Forall₂.forall_exists_l R.trTypes iv hiv
  obtain ⟨v, -, hv⟩ := List.Forall₂.forall_exists_l ht.ctors cval hc
  exact hv.1.1.1

/-- The constructors installed by the constructor phase carry the block's safety flag. -/
theorem ctor_isUnsafe {iv : InductiveVal × List ConstructorVal} (hiv : iv ∈ R.ivals)
    {cval : ConstructorVal} (hc : cval ∈ iv.2) : cval.isUnsafe = isUnsafe := by
  rw [R.ivals_eq] at hiv
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hiv
  obtain ⟨i, ctor, -, rfl⟩ := mem_ctorInfosFrom hc
  rfl

/-- A constructor of the recursor stage is a constructor of the source environment or a new
constructor of the block, with its safety flag. -/
theorem ctorEnv_ctor_cases {n : Name} {cval : ConstructorVal}
    (h : ctorEnv.find? n = some (.ctorInfo cval)) :
    c.env.find? n = some (.ctorInfo cval) ∨ cval.isUnsafe = isUnsafe := by
  rcases R.ctorEnv_cases h with h | ⟨iv, hiv, cv, hc, heq, -⟩
  · rcases R.headerEnv_cases h with h | ⟨_, _, heq, -⟩
    · exact .inl h
    · cases heq
  · cases heq; exact .inr (R.ctor_isUnsafe hiv hc)

end ConstructorCheck

end VerifyInductive
end Lean4Lean
