import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Verify.Inductive.Recursor.Signature.MotiveGroup
import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation

/-! Well-formed family applications (`InductiveSignature.FamilyTypesWF`) for the signatures
over the families of the recursor construction (`RecursorConstruction.families`). The
corresponding fact for the checked-formation source signature is in
`Constructor/CheckedFormation.lean`.

The proof does not compare the index telescope definitionally with the declared family type:
the telescope and the family application are read off the index domains of the motive pass
(`sourceIndexDomains`) and the generated motive, and the result sort off the declared family
constant. -/

namespace Lean4Lean

namespace VerifyInductive
open Lean hiding Environment Exception
open Kernel

namespace ConstructorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}

end ConstructorCheck

theorem vars_append_bvarSpine (a b : Nat) :
    InductiveSignature.vars a b ++ InductiveSignature.vars b 0 = bvarSpine (a + b) := by
  rw [bvarSpine_add, ← vars_eq_bvarSpine, ← vars_eq_bvarSpine, vars_lift, Nat.add_zero]

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The index domains of each family (`declIndexDomains`), over the source parameter scope, form
a well-formed context in the recursor-checking environment (from `sourceIndexDomains`). -/
theorem RecursorConstruction.unannotatedIndices_onCtx
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) :
    OnCtx ((H.declIndexDomains owner).reverse ++ R.parameterScope.toCtx)
      (R.context.venv.IsType c.lparams.length) := by
  have henv : R.context.venv.WF := R.context.checking.tr.wf
  have hP : OnCtx R.parameterScope.toCtx (R.context.venv.IsType c.lparams.length) := by
    simpa [VLCtx.toCtx] using R.sourceAnonymousParameterWF.toCtx
  have hdomains := Classical.choose_spec (H.sourceIndexDomains owner owner.isLt)
  exact (VEnv.IsType.wrapForalls_inv henv.ordered hP hdomains.2.2.1).1

/-- The family applied to the bvar spine of parameters and indices is a type over the family's
index domains and the source parameter scope, at the source universes. It is read off the
family's generated motive, brought back to the source universes. -/
theorem RecursorConstruction.unannotatedFamilyApp_isType
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) :
    R.context.venv.IsType c.lparams.length
      ((H.declIndexDomains owner).reverse ++ R.parameterScope.toCtx)
      (VExpr.mkApps
        (.const (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).name
          (VLevel.params c.lparams.length))
        (bvarSpine (stats.params.size + H.recInfos[owner.val]!.indices.size))) := by
  have henv : R.context.venv.WF := R.context.checking.tr.wf
  have hP : OnCtx R.parameterScope.toCtx (R.context.venv.IsType c.lparams.length) := by
    simpa [VLCtx.toCtx] using R.sourceAnonymousParameterWF.toCtx
  have hIdx := H.unannotatedIndices_onCtx owner
  have hidxId : (H.declIndexDomains owner).map (VExpr.instL (VLevel.params c.lparams.length)) =
      H.declIndexDomains owner := by
    have h := onCtx_isType_instL_id hIdx
    rw [List.map_append, hP |> onCtx_isType_instL_id] at h
    have h2 := List.append_cancel_right h
    rw [List.map_reverse] at h2
    exact List.reverse_inj.mp h2
  have hPId := onCtx_isType_instL_id hP
  have hparamCtx : H.parameterSuffix.parameterDecls.toCtx =
      R.parameterScope.toCtx.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) := by
    have h := congrArg List.reverse H.parameterDomains
    rwa [List.reverse_reverse, ← List.map_reverse, List.reverse_reverse] at h
  -- The generated motive, at the recursor universes.
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  have hpeel : ∀ {level : VLevel} {indices : List VExpr} {Γ : List VExpr} {A : VExpr},
      Γ = R.parameterScope.toCtx → indices = H.declIndexDomains owner →
      R.context.venv.IsType c.lparams.length Γ
        (VExpr.wrapForalls indices (.forallE A (.sort level))) →
      R.context.venv.IsType c.lparams.length
        ((H.declIndexDomains owner).reverse ++ R.parameterScope.toCtx) A := by
    intro level indices Γ A hΓ hindices hM
    subst hΓ hindices
    have hbody := (VEnv.IsType.wrapForalls_inv henv.ordered hP hM).2
    exact (VEnv.IsType.forallE_inv henv.ordered hbody).1
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have hL := recursorDeclarationAbstractLevels_zero H.elimLevelAdmissible helim
    have hmot := (H.sourceIndices_motive owner (level := .zero) (by
      rw [helim]; rfl)).2
    rw [H.recursorEnv, hparamCtx, hL, hPId] at hmot
    have hlen : (AddInductive.getRecLevelParams H.elimLevel c.lparams).length =
        c.lparams.length := by
      rw [helim]; rfl
    rw [hlen, hidxId] at hmot
    exact hpeel rfl rfl hmot
  · have hL := recursorDeclarationAbstractLevels_param H.elimLevelAdmissible helim
    have hmot := (H.sourceIndices_motive owner (level := .param 0) (by
      rw [helim]; simp [AddInductive.getRecLevelParams, VLevel.ofLevel])).2
    rw [H.recursorEnv, hparamCtx, hL] at hmot
    have hdrop := hmot.instL (recursorDropLevels_wf (n := c.lparams.length))
    simp only [List.map_map, Function.comp_def, VExpr.instL_instL,
      VExpr.instL_wrapForalls, VExpr.instL, VExpr.instL_mkApps,
      recursorDropLevels_prependShift] at hdrop
    have hcv : (bvarSpine (stats.params.size + H.recInfos[owner.val]!.indices.size)).map
        (fun e => e.instL (recursorDropLevels c.lparams.length)) =
        bvarSpine (stats.params.size + H.recInfos[owner.val]!.indices.size) := by
      simp [bvarSpine, List.map_map, Function.comp_def, VExpr.instL]
    have heta : (fun x => VExpr.instL (VLevel.params c.lparams.length) x) =
        VExpr.instL (VLevel.params c.lparams.length) := rfl
    rw [hcv, heta, hPId, hidxId] at hdrop
    exact hpeel rfl rfl hdrop

/-- A signature with the source parameter scope and the families of the recursor construction
has well-formed family applications in the recursor-checking environment. The telescope's
well-formedness comes from `unannotatedIndices_onCtx`, the application's from the generated
motive (at the source universes), and its sort from the declared family constant, whose
header is definitionally a telescope ending in the recorded sort (source formation). No
definitional agreement of these index domains with the declared ones is used, and the checked
recursor type is not consulted. -/
theorem RecursorConstruction.unannotatedFamilyTypesWF
    (H : RecursorConstruction R) {s : InductiveSignature}
    (hp : s.params = R.parameterScope.toCtx.reverse) (hf : s.families = H.families) :
    s.FamilyTypesWF R.context.venv decl.uvars := by
  intro owner
  have hown : owner.val < H.recInfos.size := by
    have hsize : s.families.size = H.recInfos.size := by rw [hf, H.families_size]
    have := owner.isLt
    omega
  let o : Fin H.recInfos.size := ⟨owner.val, hown⟩
  have hdecl : owner.val < decl.types.length := by rw [← H.cardinality.records]; exact hown
  have hfam : s.families[owner] = H.families[owner.val]'(by simp [hown]) := by
    simp only [Fin.getElem_fin, hf]
  have hidx : s.families[owner].indices = H.declIndexDomains o := by
    rw [hfam]; exact H.families_indices o
  have hname : s.families[owner].name = (decl.types[owner.val]'hdecl).name := by
    rw [hfam]; exact H.families_name o
  have hlev : s.families[owner].resultLevel = (decl.types[owner.val]'hdecl).resultLevel := by
    rw [hfam]; exact H.families_level o
  have hU : decl.uvars = c.lparams.length := R.core.uvars
  have hPrev : s.params.reverse = R.parameterScope.toCtx := by rw [hp, List.reverse_reverse]
  have hplen : s.params.length = stats.params.size := by
    rw [hp, List.length_reverse, H.sourceParameterCount]
  have hilen : (H.declIndexDomains o).length = H.recInfos[owner.val]!.indices.size :=
    H.sourceIndices_length o
  have henv : R.context.venv.WF := R.context.checking.tr.wf
  have hIdx := H.unannotatedIndices_onCtx o
  rw [← hU] at hIdx
  refine ⟨by rw [hidx, hPrev]; exact hIdx, ?_⟩
  -- The application is well formed (generated motive).
  have hA := H.unannotatedFamilyApp_isType o
  rw [← hU] at hA
  obtain ⟨_, hAty⟩ := hA
  -- The declared header is a telescope ending in the recorded sort.
  have hmem : decl.types[owner.val] ∈ decl.types := List.getElem_mem hdecl
  have hsourceWF := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core
    (List.ne_nil_of_mem hmem) (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
  have huvars : decl.types[owner.val].uvars = decl.uvars := hsourceWF.2.2.1 _ hmem
  have hctorsLE : R.headerVEnv ≤ R.context.venv :=
    (VEnv.addConstVals_le R.core.ctorsAdded).trans R.ctorLE
  have hle : sourceEnv ≤ R.context.venv := (VEnv.addConstVals_le R.core.typesAdded).trans hctorsLE
  have hlookup : R.context.venv.constants decl.types[owner.val].name =
      some decl.types[owner.val].toVConstant :=
    hctorsLE.constants (VEnv.addConstVals_get R.core.typesAdded
      (List.mem_map.mpr ⟨_, hmem, rfl⟩))
  have hT : R.context.venv.IsType decl.uvars [] decl.types[owner.val].type := by
    have := henv.ordered.constWF hlookup
    change R.context.venv.IsType decl.types[owner.val].uvars [] decl.types[owner.val].type at this
    rwa [huvars] at this
  have hconst := VEnv.HasType.const0 hlookup (henv.ordered.constWF hlookup)
  change R.context.venv.HasType decl.types[owner.val].uvars [] (.const decl.types[owner.val].name
      (VLevel.params decl.types[owner.val].uvars)) decl.types[owner.val].type at hconst
  rw [huvars] at hconst
  obtain ⟨_, _, _, Htypes, _, _⟩ := R.formation.formationWF.sourceParameterWF
  obtain ⟨doms, body, exprType, hdlen, h1, h2⟩ := (Htypes _ hmem).header
  have hclose := VEnv.IsDefEq.close_sort_header henv hT (h1.mono hle) (h2.mono hle)
  have hW := (hconst.defeqU_r henv trivial hclose).weak0 henv.ordered
    (Γ := (H.declIndexDomains o).reverse ++ R.parameterScope.toCtx)
  have hlen : (bvarSpine (stats.params.size + H.recInfos[owner.val]!.indices.size)).length =
      doms.length := by
    rw [hdlen, ← H.cardinality.params, ← H.cardinality.indices owner.val hown]
    simp [bvarSpine]
  have happ := (VEnv.HasType.mkApps_wrapForalls henv hIdx hW ⟨_, hAty⟩ hlen).2
  simp only [VExpr.instOuter_sort] at happ
  change R.context.venv.HasType decl.uvars
    (s.families[owner].indices.reverse ++ s.params.reverse)
    (VExpr.mkApps (.const s.families[owner].name (VLevel.params decl.uvars))
      (InductiveSignature.vars s.params.length s.families[owner].indices.length ++
        InductiveSignature.vars s.families[owner].indices.length 0))
    (.sort s.families[owner].resultLevel)
  rw [hidx, hPrev, hname, hlev, hplen, vars_append_bvarSpine, hilen]
  exact happ

end VerifyInductive
end Lean4Lean
