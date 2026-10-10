import Lean4Lean.Verify.Inductive.Recursor.Metadata
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.Signature.GeneratorShapes

/-! Alignment of the installed block with a signature that models the source declaration,
for a recursor check: field counts, index arities, constructor types, family metadata, the
major premise and K-like recursors (`RecursorInstallation.alignmentOfTr`, `RecursorInstallation.kOfTr`).

Source formation supplies raw constructor shapes. The normalized signature supplies exact
family and constructor correspondences, while typing of the generated equations fixes
constructor field counts. All typing arguments take place in the recursor environment
`H.outVEnv`, before the iota rules are added; the resulting shapes and K equalities then
extend to the installed environment `H.outVEnv.addDefEqRules g.equations`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace InductiveSignature

/-- The typed generated major pattern supplies exactly the fields of the raw
source constructor, by constructor saturation. -/
theorem Instance.fieldCount_of_equation {s : InductiveSignature} (g : Instance s)
    {env : VEnv} (henv : env.WF) (index : Fin s.constructors.size)
    {fields : Nat}
    (hlookup : env.constants (g.recursorName s.constructors[index].owner) =
      some (g.recursor s.constructors[index].owner).toVConstant)
    (hctor : VConstructorShape env s.constructors[index].name s.uvars s.params.length fields
      s.families[s.constructors[index].owner].indices.length
      s.families[s.constructors[index].owner].name)
    (hrigid : env.Rigid s.families[s.constructors[index].owner].name)
    (hindices : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length)
    (hwf : (g.equation index).WF env) : fields = s.constructors[index].fields.length := by
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  let pre := vars (s.params.length + extra) nf ++ indices
  let target := VExpr.mkApps (.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
    (indices ++ [major])
  have hleft : env.HasType g.uvars []
      (VExpr.wrapLams domains (VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
        (pre ++ [major]))) (VExpr.wrapForalls domains target) := hwf.1
  rcases VEnv.HasType.wrapLams_inv henv (by trivial) hleft with ⟨hctx, hbody⟩
  rcases g.recursor_shape ctor.owner hlookup with ⟨hrec⟩
  have hpre : pre.length = s.params.length + s.families.size + s.constructors.size +
      s.families[ctor.owner].indices.length := by
    simp only [pre, indices, vars, List.length_append, List.length_map,
      List.length_reverse, List.length_range]
    change s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].indices.length = s.params.length + s.families.size + s.constructors.size +
        s.families[s.constructors[index].owner].indices.length
    omega
  have ⟨_, hmajor, _⟩ := hrec.spine_typing henv hctx VLevel.params_wf VLevel.params_length
    hpre ⟨_, hbody⟩
  have hsaturated := hctor.saturated_of_hasType henv hctx hrigid hmajor
  simp only [List.length_append, vars, List.length_map,
    List.length_reverse, List.length_range] at hsaturated
  change s.params.length + s.constructors[index].fields.length = s.params.length + fields at hsaturated
  omega

end InductiveSignature

namespace VerifyInductive

/-- The recursor-stage environment is a checking environment of the output. -/
theorem RecursorInstallation.validCore
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) :
    CheckingEnv.ValidCore c.safety outEnv H.outVEnv := by
  have hv : CheckingEnv.ValidCore H.localContext.safety H.localContext.env R.context.venv := by
    rw [H.localExtends.safety_eq, H.localExtends.env_eq]
    exact R.context.checking.toValidCore
  have := H.installed.validCore hv
  rwa [H.localExtends.safety_eq] at this

theorem RecursorInstallation.outVEnvWF
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : H.outVEnv.WF :=
  H.validCore.tr.wf

theorem RecursorInstallation.headerLE
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : R.headerVEnv ≤ H.outVEnv :=
  R.headerLE.trans (R.ctorLE.trans H.installed.le)

theorem RecursorInstallation.sourceLE
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : sourceEnv ≤ H.outVEnv :=
  R.sourceLE.trans H.headerLE

theorem RecursorInstallation.familyConstant
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.constants family.name = some family.toVConstant :=
  H.headerLE.constants (VEnv.addConstVals_get R.core.typesAdded
    (List.mem_map.mpr ⟨family, hf, rfl⟩))

theorem RecursorInstallation.constructorConstant
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (ctor : VConstVal) (hc : ctor ∈ decl.constructorConstants) :
    H.outVEnv.constants ctor.name = some ctor.toVConstant :=
  (R.ctorLE.trans H.installed.le).constants
    (VEnv.addConstVals_get R.core.ctorsAdded hc)

theorem _root_.Lean4Lean.VEnv.Rigid.addConstVals {env env' : VEnv} {c : Name}
    {cis : List VConstVal} (H : env.Rigid c) (h : env.addConstVals cis = some env') :
    env'.Rigid c := by
  induction cis generalizing env with
  | nil => cases h; exact H
  | cons ci cis ih =>
    simp only [VEnv.addConstVals] at h
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => rw [hadd] at h; cases h
    | some env₁ => rw [hadd] at h; exact ih (H.addConst hadd) h

theorem AddConstants.rigid {c : Name}
    (H : AddConstants safety env venv entries outEnv outVEnv) (hr : venv.Rigid c) :
    outVEnv.Rigid c := by
  induction H with
  | nil => exact hr
  | cons _ _ _ _ hadd _ _ ih => exact ih (hr.addConst hadd)

theorem RecursorInstallation.familyRigid
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.Rigid family.name := by
  have hsourceWF : sourceEnv.WF := R.sourceContextVEnv ▸ R.sourceContext.checking.tr.wf
  have hfresh := (VEnv.addConstVals_names_fresh R.core.typesAdded).2
    family.toVConstVal (List.mem_map.mpr ⟨family, hf, rfl⟩)
  have hrigid := hsourceWF.rigid_of_absent hfresh
  have hP : R.context.venv.Rigid family.name := by
    rw [R.contextVEnv]
    exact ((hrigid.addConstVals R.core.typesAdded).addConstVals R.core.ctorsAdded).addProjections
  exact H.installed.rigid hP

/-- In a signature that models the declaration, each constructor result has as many
indices as its family (`Models.constructorArity`). -/
theorem RecursorInstallation.normalizedIndexArity
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (_H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (index : Fin s.constructors.size) :
    s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length :=
  hm.constructorArity _ (by simp)

theorem _root_.Lean4Lean.VInductDecl.RawCtorShape.constructorShape
    {decl : VInductDecl} {family : VInductiveType} {ctor : VConstVal} {env : VEnv}
    (H : decl.RawCtorShape family ctor) (hnames : decl.sourceNames.Nodup)
    (hfamily : family ∈ decl.types)
    (hlookup : env.constants ctor.name = some ⟨decl.uvars, ctor.type⟩) :
    ∃ fields, Nonempty (VConstructorShape env ctor.name decl.uvars decl.nparams
      fields family.numIndices family.name) := by
  rcases H with ⟨doms, result, htype, hparamsLe, hvalid, hhead⟩
  rcases hvalid with ⟨target, htarget, htargetName, levels, hfn, hlevels, hargs, hparams⟩
  rcases htargetName with hnone | htargetName
  · cases hnone
  have heq : target = family := VInductDecl.type_eq_of_mem_name hnames htarget hfamily
    (Option.some.inj htargetName).symm
  subst target
  change result.getAppFnArgs.2.length = decl.nparams + family.numIndices at hargs
  change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (doms.length - decl.nparams) at hparams
  refine ⟨doms.length - decl.nparams, ⟨{
    type := ctor.type
    const := hlookup
    doms := doms
    indices := result.getAppFnArgs.2.drop decl.nparams
    type_eq := ?_
    doms_length := by omega
    indices_length := by simp only [List.length_drop, hargs]; omega }⟩⟩
  rw [htype]
  congr 1
  calc
    result = VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 :=
      (VExpr.mkApps_getAppFnArgs_eq result).symm
    _ = VExpr.mkApps (.const family.name (VLevel.params decl.uvars))
        ((result.getAppFnArgs.2.take decl.nparams) ++ result.getAppFnArgs.2.drop decl.nparams) := by
      rw [List.take_append_drop, hhead]
    _ = _ := by
      rw [hparams]
      congr 2
      rw [show decl.paramVars (doms.length - decl.nparams) =
          InductiveSignature.vars decl.nparams (doms.length - decl.nparams) from rfl,
        InductiveSignature.vars_eq_bvarRange, Nat.add_comm]

theorem RecursorInstallation.rawConstructorShape
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (index : Fin s.constructors.size) :
    ∃ fields, Nonempty (VConstructorShape H.outVEnv s.constructors[index].name
      s.uvars s.params.length fields s.families[s.constructors[index].owner].indices.length
      s.families[s.constructors[index].owner].name) := by
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.family s.constructors[index].owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hfctors⟩
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily hfctors with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  have hcMem : ctor ∈ decl.constructorConstants := List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩
  have hlookup : H.outVEnv.constants ctor.name = some ⟨decl.uvars, ctor.type⟩ := by
    have := H.constructorConstant ctor hcMem
    change H.outVEnv.constants ctor.name = some ⟨ctor.uvars, ctor.type⟩ at this
    simpa only [← hcuvars, hm.uvars] using this
  have hraw := R.formation.formationWF.sourceParameterWF.rawCtorShape family hfamily ctor hctor
  rcases hraw.constructorShape hnames hfamily hlookup with ⟨fields, hshape⟩
  exact ⟨fields, by simpa only [← hm.uvars, ← hm.nparams, ← hcname, ← hfindex, ← hfname] using hshape⟩

/-- The installed constructor's type is definitionally equal to the signature's constructor
type. -/
theorem RecursorInstallation.constructorTypeDefEq
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (index : Fin s.constructors.size) :
    ∀ ctorUvars ctorDoms ctorBody,
      H.outVEnv.constants s.constructors[index].name =
        some ⟨ctorUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ →
      H.outVEnv.IsDefEqU s.uvars [] (s.constructorType s.constructors[index])
        (VExpr.wrapForalls ctorDoms ctorBody) := by
  intro ctorUvars ctorDoms ctorBody hc
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.family s.constructors[index].owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hfctors⟩
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily hfctors with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  have hcMem : ctor ∈ decl.constructorConstants := List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩
  have hlookup := H.constructorConstant ctor hcMem
  rw [← hcname, hc] at hlookup
  have htype : VExpr.wrapForalls ctorDoms ctorBody = ctor.type :=
    congrArg VConstant.type (Option.some.inj hlookup)
  rw [htype, hm.uvars]
  exact hctype.mono H.headerLE

theorem RecursorInstallation.normalizedFamilyRigid
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (owner : Fin s.families.size) : H.outVEnv.Rigid s.families[owner].name := by
  rcases hm.family owner with ⟨family, hfamily, hname, _⟩
  rw [hname]
  exact H.familyRigid family hfamily

/-- The installed header is an `inductInfo` whose constructor-name list is exactly that of
the source family. -/
theorem RecursorInstallation.familyInfo
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    ∃ info : InductiveVal,
      outEnv.constants.find? family.name = some (.inductInfo info) ∧
      info.ctors = family.ctors.map VConstVal.name := by
  obtain ⟨info, hinfo, htr⟩ := List.Forall₂.forall_exists_r R.headers.trHeaders family hf
  have hname : info.name = family.name := htr.1.2
  have hctorWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf
  have hfind : H.localContext.env.find? info.name = some (.inductInfo info) := by
    rw [H.localExtends.env_eq]; exact R.headerInfo_find hinfo
  have hout := H.installed.preservesFind hctorWF hfind
  have houtWF := H.installed.targetMapWF hctorWF
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, hname] at hout
  exact ⟨info, hout, htr.2⟩

theorem RecursorInstallation.majorOfTr
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) {g : s.Instance}
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.TrRecursorVal g H.outVEnv owner rec) :
    ∃ info, outEnv.constants.find? rec.getMajorInduct = some (.inductInfo info) := by
  rcases hm.family owner with ⟨family, hfamily, hname, _⟩
  rcases H.familyInfo family hfamily with ⟨info, hinfo, _⟩
  exact ⟨info, by simpa only [hr.major, hname] using hinfo⟩

/-- A recursor whose translation carries the K flag is K-like in the installed environment.
The alignment is read off source formation: the family header's
`TypeShape` exposes its parameter and index telescope ending in the recorded
sort (which is `Prop` by the K condition and the model's result level), the
constructor's raw parameter prefix comes from `CtorParameterShape`, and both
parameter telescopes agree with the common one (`ParamsDefEq`). -/
theorem RecursorInstallation.kOfTr
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) (g : s.Instance)
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.TrRecursorVal g H.outVEnv owner rec) :
    KLikeRecursor outEnv.constants (H.outVEnv.addDefEqRules g.equations) rec := by
  intro hk
  rcases hr.k hk with ⟨hfamilies, hctors, hzero, _⟩
  let index : Fin s.constructors.size := ⟨0, by omega⟩
  have howner : s.constructors[index].owner = owner := by
    apply Fin.eq_of_val_eq
    have h1 := s.constructors[index].owner.isLt
    have h2 := owner.isLt
    omega
  have hctorList : s.constructors.toList = [s.constructors[index]] := by
    apply List.ext_getElem
    · simpa only [Array.length_toList, List.length_singleton] using hctors
    · intro i hi hi'
      have heq : i = 0 := by simpa using hi'
      subst i
      rfl
  rcases hm.family owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hfctors⟩
  have hsingle : (s.declarationFamily owner).ctors.map VConstVal.name =
      [s.constructors[index].name] := by
    have hownerVal : s.constructors[index].owner.val = owner.val := congrArg Fin.val howner
    simp only [InductiveSignature.declarationFamily, hctorList, List.filterMap_cons,
      List.filterMap_nil, if_pos hownerVal, List.map_cons, List.map_nil]
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily
      (by simpa only [howner] using hfctors) with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  rcases H.familyInfo family hfamily with ⟨info, hlookupInfo, hinfoCtors⟩
  refine ⟨info, s.constructors[index].name, ?_, ?_, ?_⟩
  · simpa only [hr.major, hfname] using hlookupInfo
  · exact hinfoCtors.trans (hfctors.symm.trans hsingle)
  · apply KLikeAlignment.mono VEnv.addDefEqRules_le
    have henv := H.outVEnvWF
    have hlookupF := H.familyConstant family hfamily
    have hlookupC := H.constructorConstant ctor (List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩)
    have hfamilyWF : H.outVEnv.IsType decl.uvars [] family.type := by
      simpa only [VConstant.WF, ← hfuvars, hm.uvars] using henv.ordered.constWF hlookupF
    have hctorWF : H.outVEnv.IsType decl.uvars [] ctor.type := by
      simpa only [VConstant.WF, ← hcuvars, hm.uvars] using henv.ordered.constWF hlookupC
    -- The header and constructor shapes come from source formation.
    obtain ⟨params, envTypes', htypes', Htypes, Hctors, _⟩ :=
      R.formation.formationWF.sourceParameterWF
    have hEnvTypes : envTypes' = R.headerVEnv :=
      Option.some.inj (htypes'.symm.trans R.core.typesAdded)
    subst hEnvTypes
    obtain ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnorm, htakeP, htakeI, hPD, hres⟩ := Htypes family hfamily
    obtain ⟨ownParamsC, tail, htakeC, hPDC⟩ := Hctors family hfamily ctor hctor
    obtain ⟨hnormEq, hPlen⟩ := VExpr.takeForalls_rebuild htakeP
    obtain ⟨hafterEq, hIlen⟩ := VExpr.takeForalls_rebuild htakeI
    obtain ⟨hctorShape, hClen⟩ := VExpr.takeForalls_rebuild htakeC
    have hnorm' : H.outVEnv.IsDefEq decl.uvars [] family.type
        (VExpr.wrapForalls (ownParams ++ indices) result) exprType := by
      rw [VExpr.wrapForalls_append, ← hafterEq, ← hnormEq]
      exact hnorm.mono H.sourceLE
    have hnormalizedWF : H.outVEnv.IsType decl.uvars []
        (VExpr.wrapForalls (ownParams ++ indices) result) :=
      hfamilyWF.defeqU_l henv (by trivial) ⟨_, hnorm'⟩
    rcases VEnv.IsType.wrapForalls_inv henv (by trivial) hnormalizedWF with ⟨hctx, _⟩
    have hres' : H.outVEnv.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ [])
        result (.sort family.resultLevel) (.sort (.succ family.resultLevel)) := by
      simpa [List.reverse_append] using hres.mono H.sourceLE
    have hsortWF : H.outVEnv.IsType decl.uvars ((ownParams ++ indices).reverse ++ [])
        (.sort family.resultLevel) := ⟨_, hres'.hasType.2⟩
    have hsort : H.outVEnv.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ [])
        (.sort family.resultLevel) (.sort .zero) (.sort (.succ family.resultLevel)) :=
      .sortDF (hsortWF.sort_inv henv.ordered) trivial (hflevel.symm.trans hzero)
    rcases VExpr.wrapForalls_defeq hctx (hres'.trans hsort) with ⟨sortLevel, hwrapped⟩
    have hprop : H.outVEnv.IsDefEqU decl.uvars [] family.type
        (VExpr.wrapForalls (ownParams ++ indices) (.sort .zero)) :=
      VEnv.IsDefEqU.trans henv (by trivial) ⟨_, hnorm'⟩ ⟨_, hwrapped⟩
    have hctorEq : H.outVEnv.IsDefEqU decl.uvars [] ctor.type
        (VExpr.wrapForalls ownParamsC tail) := by
      rw [← hctorShape]
      obtain ⟨_, h⟩ := hctorWF
      exact ⟨_, h⟩
    have hPDo : VEnv.IsDefEqCtx H.outVEnv decl.uvars [] params.reverse ownParams.reverse :=
      VEnv.IsDefEqCtx.mono H.sourceLE hPD
    have hPDCo : VEnv.IsDefEqCtx H.outVEnv decl.uvars [] params.reverse ownParamsC.reverse :=
      VEnv.IsDefEqCtx.mono H.headerLE hPDC
    have hOC : decl.ParamsDefEq H.outVEnv ownParams ownParamsC :=
      VEnv.IsDefEqCtx.trans_empty henv (hPDo.symm henv.ordered) hPDCo
    refine ⟨decl.uvars, family.type, ctor.type, ownParams ++ indices,
      ownParamsC, tail, ?_, hprop, ?_, ?_, hctorEq, ?_, ?_⟩
    · have hu : family.uvars = decl.uvars := hfuvars.symm.trans hm.uvars
      rw [hr.major, hfname, hlookupF]
      rw [← hu]
    · rw [hr.numParams, hr.numIndices, List.length_append, hPlen, hIlen, hm.nparams, hfindex]
    · have hu : ctor.uvars = decl.uvars := hcuvars.symm.trans hm.uvars
      rw [hcname, hlookupC]
      rw [← hu]
    · rw [hr.numParams, hClen, hm.nparams]
    · intro k hk hk'
      have hkP : k < ownParams.length := by omega
      obtain ⟨u, h⟩ := VInductDecl.ParamsDefEq.getElem (i := k) hOC hkP
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left hkP]
      exact ⟨_, h⟩

/-- `kOfTr` read off the recursor metadata alone, in the recursor stage. -/
theorem RecursorInstallation.kOfMetadata
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) (g : s.Instance)
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.RecursorMetadata g H.outVEnv owner rec) :
    KLikeRecursor outEnv.constants H.outVEnv rec := by
  intro hk
  rcases hr.k hk with ⟨hfamilies, hctors, hzero, _⟩
  let index : Fin s.constructors.size := ⟨0, by omega⟩
  have howner : s.constructors[index].owner = owner := by
    apply Fin.eq_of_val_eq
    have h1 := s.constructors[index].owner.isLt
    have h2 := owner.isLt
    omega
  have hctorList : s.constructors.toList = [s.constructors[index]] := by
    apply List.ext_getElem
    · simpa only [Array.length_toList, List.length_singleton] using hctors
    · intro i hi hi'
      have heq : i = 0 := by simpa using hi'
      subst i
      rfl
  rcases hm.family owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hfctors⟩
  have hsingle : (s.declarationFamily owner).ctors.map VConstVal.name =
      [s.constructors[index].name] := by
    have hownerVal : s.constructors[index].owner.val = owner.val := congrArg Fin.val howner
    simp only [InductiveSignature.declarationFamily, hctorList, List.filterMap_cons,
      List.filterMap_nil, if_pos hownerVal, List.map_cons, List.map_nil]
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily
      (by simpa only [howner] using hfctors) with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  rcases H.familyInfo family hfamily with ⟨info, hlookupInfo, hinfoCtors⟩
  refine ⟨info, s.constructors[index].name, ?_, ?_, ?_⟩
  · simpa only [hr.major, hfname] using hlookupInfo
  · exact hinfoCtors.trans (hfctors.symm.trans hsingle)
  · have henv := H.outVEnvWF
    have hlookupF := H.familyConstant family hfamily
    have hlookupC := H.constructorConstant ctor (List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩)
    have hfamilyWF : H.outVEnv.IsType decl.uvars [] family.type := by
      simpa only [VConstant.WF, ← hfuvars, hm.uvars] using henv.ordered.constWF hlookupF
    have hctorWF : H.outVEnv.IsType decl.uvars [] ctor.type := by
      simpa only [VConstant.WF, ← hcuvars, hm.uvars] using henv.ordered.constWF hlookupC
    -- The header and constructor shapes come from source formation.
    obtain ⟨params, envTypes', htypes', Htypes, Hctors, _⟩ :=
      R.formation.formationWF.sourceParameterWF
    have hEnvTypes : envTypes' = R.headerVEnv :=
      Option.some.inj (htypes'.symm.trans R.core.typesAdded)
    subst hEnvTypes
    obtain ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnorm, htakeP, htakeI, hPD, hres⟩ := Htypes family hfamily
    obtain ⟨ownParamsC, tail, htakeC, hPDC⟩ := Hctors family hfamily ctor hctor
    obtain ⟨hnormEq, hPlen⟩ := VExpr.takeForalls_rebuild htakeP
    obtain ⟨hafterEq, hIlen⟩ := VExpr.takeForalls_rebuild htakeI
    obtain ⟨hctorShape, hClen⟩ := VExpr.takeForalls_rebuild htakeC
    have hnorm' : H.outVEnv.IsDefEq decl.uvars [] family.type
        (VExpr.wrapForalls (ownParams ++ indices) result) exprType := by
      rw [VExpr.wrapForalls_append, ← hafterEq, ← hnormEq]
      exact hnorm.mono H.sourceLE
    have hnormalizedWF : H.outVEnv.IsType decl.uvars []
        (VExpr.wrapForalls (ownParams ++ indices) result) :=
      hfamilyWF.defeqU_l henv (by trivial) ⟨_, hnorm'⟩
    rcases VEnv.IsType.wrapForalls_inv henv (by trivial) hnormalizedWF with ⟨hctx, _⟩
    have hres' : H.outVEnv.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ [])
        result (.sort family.resultLevel) (.sort (.succ family.resultLevel)) := by
      simpa [List.reverse_append] using hres.mono H.sourceLE
    have hsortWF : H.outVEnv.IsType decl.uvars ((ownParams ++ indices).reverse ++ [])
        (.sort family.resultLevel) := ⟨_, hres'.hasType.2⟩
    have hsort : H.outVEnv.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ [])
        (.sort family.resultLevel) (.sort .zero) (.sort (.succ family.resultLevel)) :=
      .sortDF (hsortWF.sort_inv henv.ordered) trivial (hflevel.symm.trans hzero)
    rcases VExpr.wrapForalls_defeq hctx (hres'.trans hsort) with ⟨sortLevel, hwrapped⟩
    have hprop : H.outVEnv.IsDefEqU decl.uvars [] family.type
        (VExpr.wrapForalls (ownParams ++ indices) (.sort .zero)) :=
      VEnv.IsDefEqU.trans henv (by trivial) ⟨_, hnorm'⟩ ⟨_, hwrapped⟩
    have hctorEq : H.outVEnv.IsDefEqU decl.uvars [] ctor.type
        (VExpr.wrapForalls ownParamsC tail) := by
      rw [← hctorShape]
      obtain ⟨_, h⟩ := hctorWF
      exact ⟨_, h⟩
    have hPDo : VEnv.IsDefEqCtx H.outVEnv decl.uvars [] params.reverse ownParams.reverse :=
      VEnv.IsDefEqCtx.mono H.sourceLE hPD
    have hPDCo : VEnv.IsDefEqCtx H.outVEnv decl.uvars [] params.reverse ownParamsC.reverse :=
      VEnv.IsDefEqCtx.mono H.headerLE hPDC
    have hOC : decl.ParamsDefEq H.outVEnv ownParams ownParamsC :=
      VEnv.IsDefEqCtx.trans_empty henv (hPDo.symm henv.ordered) hPDCo
    refine ⟨decl.uvars, family.type, ctor.type, ownParams ++ indices,
      ownParamsC, tail, ?_, hprop, ?_, ?_, hctorEq, ?_, ?_⟩
    · have hu : family.uvars = decl.uvars := hfuvars.symm.trans hm.uvars
      rw [hr.major, hfname, hlookupF]
      rw [← hu]
    · rw [hr.numParams, hr.numIndices, List.length_append, hPlen, hIlen, hm.nparams, hfindex]
    · have hu : ctor.uvars = decl.uvars := hcuvars.symm.trans hm.uvars
      rw [hcname, hlookupC]
      rw [← hu]
    · rw [hr.numParams, hClen, hm.nparams]
    · intro k hk hk'
      have hkP : k < ownParams.length := by omega
      obtain ⟨u, h⟩ := VInductDecl.ParamsDefEq.getElem (i := k) hOC hkP
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left hkP]
      exact ⟨_, h⟩

end VerifyInductive
end Lean4Lean
