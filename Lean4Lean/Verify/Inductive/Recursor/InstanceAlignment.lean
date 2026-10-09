import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.Signature.GeneratorShapes
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

/-! Alignment of the installed block with a signature that models the source declaration,
for a recursor check: field counts, index arities, constructor types, family metadata, the
major premise and K-like recursors (`RecursorCheck.alignmentOfTr`, `RecursorCheck.kOfTr`).

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

theorem RecursorCheck.headerLE
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : R.headerVEnv ≤ H.outVEnv :=
  R.installation.constructorLE.trans (R.ctorLE.trans H.installed.le)

theorem RecursorCheck.sourceLE
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : sourceEnv ≤ H.outVEnv :=
  R.installation.headerLE.trans H.headerLE

theorem RecursorCheck.familyConstant
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.constants family.name = some family.toVConstant :=
  H.headerLE.constants (VEnv.addConstVals_get R.core.typesAdded
    (List.mem_map.mpr ⟨family, hf, rfl⟩))

theorem RecursorCheck.constructorConstant
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (ctor : VConstVal) (hc : ctor ∈ decl.constructorConstants) :
    H.outVEnv.constants ctor.name = some ctor.toVConstant :=
  (R.ctorLE.trans H.installed.le).constants
    (VEnv.addConstVals_get R.core.ctorsAdded hc)

theorem RecursorCheck.familyRigid
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.Rigid family.name := by
  have hsourceWF : sourceEnv.WF := R.sourceContextVEnv ▸ R.sourceContext.checking.tr.wf
  have hfresh := (VEnv.addConstVals_names_fresh R.core.typesAdded).2
    family.toVConstVal (List.mem_map.mpr ⟨family, hf, rfl⟩)
  have hrigid := hsourceWF.ordered.rigid_of_absent hfresh
  intro df hdf ls hhead
  have hdf' := H.installation.atomic.defeqs df hdf
  rw [VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs] at hdf'
  exact hrigid df hdf' ls hhead

/-- In a signature that models the declaration, each constructor result has as many
indices as its family (`Models.constructorArity`). -/
theorem RecursorCheck.normalizedIndexArity
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (_H : RecursorCheck R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (index : Fin s.constructors.size) :
    s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length :=
  hm.constructorArity _ (by simp)

theorem RecursorCheck.rawConstructorShape
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
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
theorem RecursorCheck.constructorTypeDefEq
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
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

theorem RecursorCheck.normalizedFamilyRigid
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl)
    (owner : Fin s.families.size) : H.outVEnv.Rigid s.families[owner].name := by
  rcases hm.family owner with ⟨family, hfamily, hname, _⟩
  rw [hname]
  exact H.familyRigid family hfamily

theorem RecursorCheck.alignmentOfTr
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) (g : s.Instance)
    (hlevels : g.levels.length = s.uvars) (hlevelsWF : ∀ l ∈ g.levels, l.WF g.uvars)
    (hrecursors : ∀ owner, H.outVEnv.constants (g.recursorName owner) = some (g.recursor owner).toVConstant)
    (hwf : ∀ index, (g.equation index).WF H.outVEnv)
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.TrRecursorVal g H.outVEnv owner rec) :
    RecursorAlignmentCore (H.outVEnv.addDefEqRules g.equations) rec := by
  rcases g.recursor_shape owner (hrecursors owner) with ⟨hshape⟩
  refine ⟨s.params.length, g.levels, VExpr.bvarRange s.params.length s.params.length, ?_, ?_⟩
  · have hshape' := VRecursorShape.mono (venv' := H.outVEnv.addDefEqRules g.equations)
      VEnv.addDefEqRules_le hshape
    rw [hr.numParams]
    simpa only [hr.name, hr.uvars, hr.numMotives, hr.numMinors,
      hr.numIndices, hr.major] using Nonempty.intro hshape'
  · intro rule hmem
    rcases Lean4Lean.List.Forall₂.forall_exists_r hr.rules rule hmem with ⟨index, hindex, hi⟩
    have howner : s.constructors[index].owner = owner := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp hindex).2
    have hind := H.normalizedIndexArity hm index
    rcases H.rawConstructorShape hm index with ⟨fields, ⟨hc⟩⟩
    have hfields := g.fieldCount_of_equation H.outVEnvWF index
      (hrecursors _) hc (H.normalizedFamilyRigid hm _) hind (hwf index)
    subst fields
    have hdf : (H.outVEnv.addDefEqRules g.equations).defeqs (g.equation index) :=
      VEnv.addDefEqRules_defeqs_iff.mpr (.inr (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩))
    refine ⟨g.equation index, ?_⟩
    refine { shape := ?_
             rhs := hi.rhs.mono VEnv.addDefEqRules_le
             ctor := ?_ }
    · rw [hr.numParams]
      simpa only [hr.name, hr.uvars, hr.numMotives, hr.numMinors,
        hr.numIndices, hi.ctor, hi.nfields, howner] using
        g.iota_shape index H.outVEnvWF VEnv.addDefEqRules_le (fun _ => by simp) hdf hind hlevelsWF
          (hrecursors _) (H.constructorTypeDefEq hm index)
    · refine ⟨s.uvars, hlevels, ?_⟩
      have hc' := VConstructorShape.mono (venv' := H.outVEnv.addDefEqRules g.equations)
        VEnv.addDefEqRules_le hc
      simpa only [hi.ctor, hi.nfields, hr.numIndices, hr.major, howner] using
        Nonempty.intro hc'

/-- The installed header is an `inductInfo` whose constructor-name list is exactly that of
the source family. -/
theorem RecursorCheck.familyInfo
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    ∃ info : InductiveVal,
      outEnv.constants.find? family.name = some (.inductInfo info) ∧
      info.ctors = family.ctors.map VConstVal.name := by
  have hvalue : family.toVConstVal ∈ R.headerEntries.map Prod.snd := by
    rw [R.headerValues]
    exact List.mem_map.mpr ⟨family, hf, rfl⟩
  rcases List.mem_map.mp hvalue with ⟨entry, he, hvalue⟩
  have hall : entry ∈ R.headerEntries ++ R.constructorEntries ++ H.entries := by
    simp [he]
  have ha := H.installation.atomic
  have hwf := R.sourceContext.checking.tr.map_wf
  have houtWF := ha.targetMapWF hwf
  have hname : entry.1.name = family.name := by
    rw [ha.entryNames hall, hvalue]
  rcases R.headerSourceAligned with ⟨_, hheaders⟩
  rcases hheaders.originInfo he with ⟨info, _, hinfo⟩
  have hlookup := ha.findEntry hwf (info := entry.1) (value := entry.2) hall
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, hname, hinfo] at hlookup
  have hfresh := ha.entryFresh hwf (info := entry.1) (value := entry.2) hall
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hname] at hfresh
  rcases H.inductInfosFromDecl family.name info hlookup with hold |
      ⟨familyIdx, hinfoName, ⟨A⟩⟩
  · rw [hfresh] at hold
    cases hold
  · have hfamilyIdx := A.familyIdx_lt
    have hfamilyEq : decl.types[familyIdx] = family :=
      VInductDecl.type_eq_of_mem_name
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
        (List.getElem_mem A.familyIdx_lt) hf (A.name.symm.trans hinfoName.symm)
    refine ⟨info, hlookup, ?_⟩
    apply List.ext_getElem
    · simpa only [List.length_map, hfamilyEq] using A.constructors
    · intro i hi hi'
      have hiSrc : i < decl.types[familyIdx].ctors.length := by rw [← A.constructors]; exact hi
      rcases A.constructor i hiSrc with ⟨C⟩
      simpa only [List.getElem_map, hfamilyEq] using C.name

theorem RecursorCheck.majorOfTr
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
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
theorem RecursorCheck.kOfTr
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
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

end VerifyInductive
end Lean4Lean
