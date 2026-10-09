import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Declarations
import Lean4Lean.Theory.Inductive.CaseCertificateMono

/-! # Pieces of the case certificate of a nested declaration

The source declaration of a nested run registers the case schema of the signature of the
lowered declaration's checked formation (`CheckedFormation.sourceSignature`), restored by the
nested compilation restoration (section 3.3 of the design notes). This file proves
the facts about a checked formation that this needs beyond the restoration-free certificate of
`CheckedFormation.caseEliminatorsCertified`:

* the constructor types of the signature are head-applied whenever the executable
  constructor types are parameter-uniform in the heads, so restoration is total on them
  (`CheckedFormation.sourceSignature_headsApplied`);
* the pieces of the signature project only out of structures registered in the source
  environment (`CheckedFormation.sourceSignature_pieces_projNamesOK`);
* restoration fixes the signature's header (`CheckedFormation.restored_headerAgreement`). -/

open Lean4Lean.InductiveSignature

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

namespace CheckedFormation
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams : Nat} {isUnsafe : Bool} {depth : Nat} {sourceEnv : VEnv}
  {indTypes : Array InductiveType}

theorem stats_params_fvars
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ∃ pfvs : List FVarId, stats.params = (pfvs.map Expr.fvar).toArray := by
  have h := R.statsWF.paramFVars
  refine ⟨stats.params.toList.map fun e => match e with | .fvar fv => fv | _ => default, ?_⟩
  apply Array.ext'
  simp only [List.map_map]
  conv => lhs; rw [← List.map_id stats.params.toList]
  apply List.map_congr_left
  intro e he
  obtain ⟨fv, rfl⟩ := h e (Array.mem_toList_iff.1 he)
  rfl

/-- **The constructor types of the checked-formation signature are head-applied**, given that
the executable constructor types are parameter-uniform in the heads and the parameters avoid
the heads. -/
theorem sourceSignature_headsApplied
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    {heads : List Name}
    (hctorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
      Expr.ParamUniformTele heads stats.params.size stats.levels ctor.type)
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads)
    (hparamsFree : ∀ A ∈ R.params, A.containsAnyConst heads = false) :
    ∀ normalized ∈ R.sourceSignature.declaration.types, ∀ ctor ∈ normalized.ctors,
      VExpr.HeadsApplied heads stats.params.size stats.levels.length ctor.type := by
  intro normalized hnorm ctor hctor
  simp only [InductiveSignature.declaration, List.mem_map] at hnorm
  obtain ⟨⟨fam, i⟩, -, rfl⟩ := hnorm
  simp only [List.mem_filterMap] at hctor
  obtain ⟨cc, hcc, hsome⟩ := hctor
  split at hsome
  case isFalse => cases hsome
  cases hsome
  change VExpr.HeadsApplied heads stats.params.size stats.levels.length
    (R.sourceSignature.constructorType cc)
  have hcc' : cc ∈ (Array.ofFn R.sourceSignatureConstructor).toList := hcc
  rw [Array.toList_ofFn] at hcc'
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hcc'
  obtain ⟨production, hproduction, tail, tailTarget, -, -, hprefix, -, htr, -, -, htype⟩ :=
    R.sourceSignatureConstructor_replay k
  rw [← htype]
  -- the executable constructor is parameter-uniform
  obtain ⟨owner, howner, hctorMem⟩ := List.mem_flatMap.1 hproduction
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 howner
  have hj' : j < indTypes.size := by simpa using hj
  have hget : indTypes[j]! = indTypes.toList[j] := by
    simp [getElem!_pos indTypes j hj']
  have Hsrc := hctorTypes j hj' production (by rw [hget]; exact hctorMem)
  obtain ⟨pfvs, hpfvs⟩ := R.stats_params_fvars
  have Htail := hprefix.paramUniform hpfvs Hsrc
  have hA := Htail.headsApplied fun p hp => by
    rw [hpfvs] at hp
    simp only [List.mem_map] at hp
    obtain ⟨fv, -, rfl⟩ := hp
    exact .fvar fv
  simp only [Array.length_toList] at hA
  have hscope : ∀ x ∈ R.parameterScope, VExpr.HeadsApplied heads stats.params.size
      stats.levels.length x.2.value := by
    intro x hx
    have hcached := R.sourceStatsWF.cachedScope
    rw [R.sourceParameterScope] at hcached
    obtain ⟨p, -, hp⟩ := Lean4Lean.List.Forall₂.forall_exists_r hcached x hx
    obtain ⟨fv, deps, type, -, rfl⟩ := hp
    exact .bvar 0
  have hT := hA.trExprS hlit hscope htr
  refine VExpr.HeadsApplied.wrapForalls (fun d hd => ?_) hT
  have hd' : d ∈ R.params := by
    rw [← R.sourceSignatureHeader_params]; exact hd
  exact .of_containsAnyConst (hparamsFree d hd')

/-- **The pieces of the checked-formation signature project only out of structures registered in the
source environment.** -/
theorem sourceSignature_pieces_projNamesOK
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hdeclNe : decl.types ≠ []) :
    let ok := fun S => ∃ info, sourceEnv.projections S info
    (∀ e ∈ R.sourceSignature.params, e.ProjNamesOK ok) ∧
    (∀ f ∈ R.sourceSignature.families.toList, ∀ e ∈ f.indices, e.ProjNamesOK ok) ∧
    (∀ c ∈ R.sourceSignature.constructors.toList,
      ∀ e ∈ R.sourceSignature.fieldTypes c, e.ProjNamesOK ok) ∧
    (∀ c ∈ R.sourceSignature.constructors.toList, ∀ e ∈ c.indices, e.ProjNamesOK ok) := by
  intro ok
  have hsrcWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  have hokH : ∀ {e : VExpr}, e.ProjNamesOK (fun S => ∃ info, R.headerVEnv.projections S info) →
      e.ProjNamesOK ok := by
    intro e h
    have hp := VEnv.addConstVals_projections R.core.typesAdded
    exact h.mono fun S ⟨info, hi⟩ => ⟨info, by rw [hp] at hi; exact hi⟩
  have hheaders : ∀ f ∈ R.sourceSignatureHeader.families.toList,
      (VExpr.wrapForalls (R.sourceSignatureHeader.params ++ f.indices) (.sort f.resultLevel)).ProjNamesOK
        ok := by
    intro f hf
    obtain ⟨src, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_l R.sourceSignatureHeader_families f hf
    obtain ⟨_, hd⟩ := h.2.2.2
    exact (hd.projNamesOK hsrcWF.ordered trivial).1
  have hfamNe : 0 < R.sourceSignatureHeader.families.size := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    have : 0 < decl.types.length := List.length_pos_iff.mpr hdeclNe
    omega
  have hctor' : ∀ i : Fin decl.ownedConstructors.length,
      (R.sourceSignatureHeader.constructorType (R.sourceSignatureConstructor i)).ProjNamesOK ok := by
    intro i
    obtain ⟨_, _, hdef, _⟩ := Classical.choose_spec
      (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))
    obtain ⟨_, hd⟩ := hdef
    exact hokH (hd.projNamesOK R.headerWF.ordered trivial).1
  have hmem : ∀ c ∈ R.sourceSignature.constructors.toList,
      ∃ i, R.sourceSignatureConstructor i = c := by
    intro c hc
    have hc' : c ∈ (Array.ofFn R.sourceSignatureConstructor).toList := hc
    rw [Array.toList_ofFn] at hc'
    exact List.mem_ofFn.mp hc'
  refine ⟨fun e he => ?_, fun f hf e he => ?_, fun c hc e he => ?_, fun c hc e he => ?_⟩
  · exact (VExpr.ProjNamesOK.wrapForalls_inv
      (hheaders _ (Array.getElem_mem_toList (i := 0) hfamNe))).1 e (List.mem_append_left _ he)
  · exact (VExpr.ProjNamesOK.wrapForalls_inv (hheaders f hf)).1 e (List.mem_append_right _ he)
  · obtain ⟨i, rfl⟩ := hmem c hc
    have h := VExpr.ProjNamesOK.wrapForalls_inv (hctor' i)
    have he' : e ∈ R.sourceSignature.fieldTypes (R.sourceSignatureConstructor i) := he
    rw [R.sourceSignature_fieldTypes] at he'
    exact h.1 e (List.mem_append_right _ he')
  · obtain ⟨i, rfl⟩ := hmem c hc
    have h := (VExpr.ProjNamesOK.wrapForalls_inv (hctor' i)).2
    exact (VExpr.ProjNamesOK.mkApps_inv h).2 e (List.mem_append_right _ he)

/-- **Header agreement of a restored checked-formation schema.** The signature's header lives in
the source environment, where the restorable names are fresh, so restoration fixes it; the
families of a declaration whose headers form a prefix of the checked declaration agree with
it. -/
theorem restored_headerAgreement
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hdeclNe : decl.types ≠ []) {schema : CaseSchema} {source : VInductDecl}
    (hsig : schema.signature = R.sourceSignature)
    (hfresh : ∀ name ∈ schema.restoration.restorableNames, sourceEnv.constants name = none)
    (hprefix : source.typeConstants = decl.typeConstants.take source.types.length)
    (huvars : decl.uvars = source.uvars)
    {sourceTypes : VEnv} (hsourceTypes : sourceEnv.addConstVals source.typeConstants = some sourceTypes) :
    schema.HeaderAgreement sourceEnv source := by
  obtain ⟨orig, sig, rst⟩ := schema
  simp only at hsig hfresh
  subst hsig
  have hsrcWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  have hfams := R.sourceSignatureHeader_families
  have hsize : R.sourceSignatureHeader.families.size = decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq hfams
    simpa using this
  have hheader : ∀ i (hi : i < R.sourceSignatureHeader.families.size),
      (VExpr.wrapForalls (R.sourceSignatureHeader.params ++
          R.sourceSignatureHeader.families[i].indices)
        (.sort R.sourceSignatureHeader.families[i].resultLevel)).containsAnyConst
          rst.restorableNames = false ∧
      sourceEnv.IsDefEqU decl.uvars []
        (VExpr.wrapForalls (R.sourceSignatureHeader.params ++
            R.sourceSignatureHeader.families[i].indices)
          (.sort R.sourceSignatureHeader.families[i].resultLevel))
        (decl.types[i]'(hsize ▸ hi)).type ∧
      R.sourceSignatureHeader.families[i].name = (decl.types[i]'(hsize ▸ hi)).name := by
    intro i hi
    have hf := Lean4Lean.List.forall₂_getElem hfams i (by simpa using hi) (hsize ▸ hi)
    simp only [Array.getElem_toList] at hf
    obtain ⟨hname, -, -, hd⟩ := hf
    obtain ⟨_, hd'⟩ := id hd
    exact ⟨(hd'.noFreshConsts hsrcWF.ordered hfresh (by intro _ h; simp at h)).1, hd, hname⟩
  have hfamNe : 0 < R.sourceSignatureHeader.families.size := by
    have : 0 < decl.types.length := List.length_pos_iff.mpr hdeclNe
    omega
  refine ⟨R.sourceSignatureHeader.params, ?_, fun owner => ?_⟩
  · apply Restoration.mapM_expr_of_avoid
    intro e he
    exact (VExpr.containsAnyConst_wrapForalls_inv (hheader 0 hfamNe).1).1 e
      (List.mem_append_left _ he)
  have hown : owner.val < R.sourceSignatureHeader.families.size := owner.isLt
  obtain ⟨hfree, hd, hname⟩ := hheader owner.val hown
  refine ⟨(R.sourceSignatureHeader.families[owner.val]'hown).indices, ?_,
    fun type htype htname => ⟨sourceTypes, hsourceTypes, ?_⟩⟩
  · apply Restoration.mapM_expr_of_avoid
    intro e he
    exact (VExpr.containsAnyConst_wrapForalls_inv hfree).1 e (List.mem_append_right _ he)
  -- identify the source family with the checked declaration's family
  have hmemC : type.toVConstVal ∈ decl.typeConstants := by
    have : type.toVConstVal ∈ source.typeConstants := List.mem_map_of_mem htype
    rw [hprefix] at this
    exact List.mem_of_mem_take this
  obtain ⟨t, ht, hteq⟩ := List.mem_map.1 hmemC
  have hnodup : (decl.types.map (·.name)).Nodup := by
    simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
      VEnv.addConstVals_names_nodup R.core.typesAdded
  have htname' : t.name = (decl.types[owner.val]'(hsize ▸ hown)).name := by
    have h1 : t.name = type.name := congrArg VConstVal.name hteq
    rw [h1, htname]
    exact hname
  have hsame : t = decl.types[owner.val]'(hsize ▸ hown) :=
    List.eq_of_mem_of_nodup_map hnodup ht (List.getElem_mem _) htname'
  have htype' : type.type = (decl.types[owner.val]'(hsize ▸ hown)).type := by
    rw [← hsame]; exact (congrArg (·.type) hteq).symm
  rw [htype']
  have := (hd.mono (VEnv.addConstVals_le hsourceTypes)).symm
  rw [← huvars]
  exact this

/-- The checked-formation parameters mention no name that is fresh in the source environment. -/
theorem params_avoid
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hdeclNe : decl.types ≠ []) {names : List Name}
    (hfresh : ∀ name ∈ names, sourceEnv.constants name = none) :
    ∀ A ∈ R.params, A.containsAnyConst names = false := by
  have hsrcWF : sourceEnv.WF := by
    rw [← R.sourceContextVEnv]; exact R.sourceContext.checking.tr.wf
  have hfams := R.sourceSignatureHeader_families
  have hsize : R.sourceSignatureHeader.families.size = decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq hfams
    simpa using this
  have hfamNe : 0 < R.sourceSignatureHeader.families.size := by
    have : 0 < decl.types.length := List.length_pos_iff.mpr hdeclNe
    omega
  have hf := Lean4Lean.List.forall₂_getElem hfams 0 (by simpa using hfamNe) (hsize ▸ hfamNe)
  simp only [Array.getElem_toList] at hf
  obtain ⟨-, -, -, _, hd⟩ := hf
  have hfree := (hd.noFreshConsts hsrcWF.ordered hfresh (by intro _ h; simp at h)).1
  intro A hA
  rw [← R.sourceSignatureHeader_params] at hA
  exact (VExpr.containsAnyConst_wrapForalls_inv hfree).1 A (List.mem_append_left _ hA)

/-- The checked-formation parameters, in the source environment, are its parameter scope. -/
theorem params_scope
    (R : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    sourceEnv.IsDefEqCtx decl.uvars [] R.params.reverse R.parameterScope.toCtx := by
  have Hctx := R.sourceStatsWF.paramsContext
  rw [R.sourceHeaderParams, R.sourceParameterScope,
    R.sourceContextVEnv, R.sourceStatsWF.uvars] at Hctx
  exact Hctx

end CheckedFormation

end Lean4Lean.VerifyInductive
