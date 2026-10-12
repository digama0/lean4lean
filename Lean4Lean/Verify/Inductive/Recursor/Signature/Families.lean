import Lean4Lean.Verify.Inductive.Recursor.Signature.Motives
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Each family has index domains in the source universes that translate its executable index
telescope (`indexDomainSource`) over the source parameter scope and form a type there, and
whose instantiation at the recursor's universe levels translates the same telescope over the
recursor parameter context. -/
theorem RecursorConstruction.sourceIndexDomains
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ domains,
      domains.length = H.recInfos[owner]!.indices.size ∧
      TrExprS R.context.venv c.lparams
        (abstractForallContext R.parameterScope.toCtx.reverse [])
        (H.indexDomainSource owner) (VExpr.wrapForalls domains (.sort .zero)) ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls domains (.sort .zero)) ∧
      TrExprS H.recursorWF.venv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
        (H.indexDomainSource owner)
        (VExpr.wrapForalls
          (domains.map (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) := by
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  rcases hsplit with helim | ⟨fresh, helim⟩
  ·
    obtain ⟨domains, hdomains, Hsource, Htype⟩ := H.chooseDeclUnivIndexDomains_small owner howner helim
    refine ⟨domains, hdomains, Hsource, Htype, ?_⟩
    have Hidentity := Hsource.substLevelParamsCore
      (Us := c.lparams) (F := Level.param) (ls := VLevel.params c.lparams.length)
      R.sourceAnonymousParameterWF
      (fun level hlevel => VLevel.params_wf hlevel)
      (fun u u' hu => by
        simpa [Level.substParams_id, VLevel.inst_id (VLevel.WF.of_ofLevel hu)] using hu)
    rw [Expr.instantiateLevelParamsCore_id, R.sourceAnonymousParameterWF.instL_id] at Hidentity
    have Hctx := H.parameterAnonymousContext
    rw [recursorDeclarationAbstractLevels_zero H.elimLevelAdmissible helim, R.sourceAnonymousParameterWF.instL_id] at Hctx
    rw [Hctx, H.recursorEnv, recursorDeclarationAbstractLevels_zero H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams, VExpr.instL_wrapForalls, VExpr.instL, VLevel.inst]
      using Hidentity
  ·
    obtain ⟨domains, hdomains, Hsource, Htype, Hrec⟩ :=
      H.chooseDeclUnivIndexDomains_large owner howner helim
    refine ⟨domains, hdomains, Hsource, Htype, ?_⟩
    rw [H.parameterAnonymousContext, H.recursorEnv,
      recursorDeclarationAbstractLevels_param H.elimLevelAdmissible helim]
    simpa [helim, AddInductive.getRecLevelParams] using Hrec

noncomputable def RecursorConstruction.declIndexDomains
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) : List VExpr :=
  Classical.choose (H.sourceIndexDomains owner owner.isLt)

theorem RecursorConstruction.sourceIndices_length
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) :
    (H.declIndexDomains owner).length = H.recInfos[owner.val]!.indices.size :=
  (Classical.choose_spec (H.sourceIndexDomains owner owner.isLt)).1

/-- The families of the construction's signature: names and result levels are those of the
source declaration, index domains are `declIndexDomains` (chosen by `sourceIndexDomains`). -/
noncomputable def RecursorConstruction.families
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) : Array InductiveSignature.Family :=
  Array.ofFn fun owner : Fin H.recInfos.size =>
    { name := (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).name
      indices := H.declIndexDomains owner
      resultLevel := (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).resultLevel }

@[simp] theorem RecursorConstruction.families_size
    (H : RecursorConstruction R) : H.families.size = H.recInfos.size := by
  simp [families]

theorem RecursorConstruction.sourceIndices_motive
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size)
    (hlevel : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some level) :
    let motive := VExpr.wrapForalls
      ((H.declIndexDomains owner).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      (.forallE
        (VExpr.mkApps (.const (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).name
          (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
          (bvarSpine (stats.params.size + H.recInfos[owner.val]!.indices.size)))
        (.sort level))
    TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner.val]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner.val]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars) motive ∧
      H.recursorWF.venv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        H.parameterSuffix.parameterDecls.toCtx motive := by
  have Hchoice := Classical.choose_spec (H.sourceIndexDomains owner owner.isLt)
  exact H.replayMotiveWithIndexDomains owner owner.isLt
    (by simp [H.sourceIndices_length owner])
    (R.recursorHeaders.recursorLevelTranslation H.lparamsNodup H.elimLevelAdmissible)
    hlevel Hchoice.2.2.2

@[simp] theorem RecursorConstruction.families_indices
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) :
    (H.families[owner.val]'(by simp [owner.isLt])).indices = H.declIndexDomains owner := by
  simp [families]

@[simp] theorem RecursorConstruction.families_name
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) :
    (H.families[owner.val]'(by simp [owner.isLt])).name =
      (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).name := by
  simp [families]

@[simp] theorem RecursorConstruction.families_level
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Fin H.recInfos.size) :
    (H.families[owner.val]'(by simp [owner.isLt])).resultLevel =
      (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).resultLevel := by
  simp [families]

end Lean4Lean.VerifyInductive
