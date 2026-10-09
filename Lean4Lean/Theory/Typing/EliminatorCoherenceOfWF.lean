import Lean4Lean.Theory.Typing.EliminatorCoherence
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Batteries.Tactic.OpenPrivate

/-! Eliminator coherence is a consequence of well-formedness.

`VEnv.WF'.inductEliminators` requires the projections registered for the
certified declaration's families to be that declaration's own entries
(`VInductDecl.ProjectionsCoherent`). Every later projection registration is
for fresh family names, so the coherence persists. -/

namespace Lean4Lean.VEnv
open InductiveSignature CaseSchema VExpr
set_option linter.unusedSectionVars false

variable {env env' : VEnv}

private theorem EliminatorsCoherent.extendAt (H : env.EliminatorsCoherent) (hle : env ≤ env')
    (hproj : ∀ F info, env'.projections F info → env.projections F info ∨ env.constants F = none)
    (hs : env.eliminators key schema) :
    ∃ base source block,
      base ≤ env' ∧ schema.Certified base source block ∧
      (∀ value ∈ block.types ++ block.ctors, env'.constants value.name = some value.toVConstant) ∧
      ∀ type ∈ source.types, ∀ info, env'.projections type.name info →
        (⟨type.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries := by
  obtain ⟨base, source, block, hbl, hcert, hconst, hcoh⟩ := H key schema hs
  refine ⟨base, source, block, hbl.trans hle, hcert, fun v hv => hle.constants (hconst v hv), ?_⟩
  intro type htype info hp
  rcases hproj _ info hp with hp | hfresh
  · exact hcoh type htype info hp
  · exfalso
    obtain ⟨expanded, auxiliaries, hdata, _⟩ := hcert
    have hmem : type.toVConstVal ∈ block.types ++ block.ctors := by
      apply List.mem_append_left
      rw [hdata.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩
    have := hconst _ hmem
    change env.constants type.name = _ at this
    rw [hfresh] at this
    cases this

private theorem EliminatorsCoherent.extend (H : env.EliminatorsCoherent) (hle : env ≤ env')
    (helim : env'.eliminators = env.eliminators)
    (hproj : ∀ F info, env'.projections F info → env.projections F info ∨ env.constants F = none) :
    env'.EliminatorsCoherent := by
  intro key schema hs
  rw [helim] at hs
  exact H.extendAt hle hproj hs

/-- The eliminator registered with a block is coherent with the block's projections. -/
private theorem coherent_new {base envTypes : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (hbase : base.Ordered)
    (htypesSource : block.types = decl.typeConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hproj : ∀ F info, env'.projections F info →
      (∃ entry ∈ block.projections, F = entry.typeName ∧ info = entry.info) ∨
        base.projections F info) :
    ∀ type ∈ decl.types, ∀ info, env'.projections type.name info →
      (⟨type.name, info⟩ : VProjectionEntry) ∈ decl.projectionEntries := by
  intro type htype info hp
  rcases hproj _ info hp with ⟨entry, hentry, hname, rfl⟩ | hp
  · rw [hprojections] at hentry
    rw [hname]
    exact hentry
  · exfalso
    obtain ⟨c, hc⟩ := hbase.projectionConstant hp
    have hfresh := VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
      rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
    change base.constants type.name = none at hfresh
    rw [hfresh] at hc
    cases hc

private theorem old_projections (h : env'.projections = env.projections) :
    ∀ F info, env'.projections F info → env.projections F info ∨ env.constants F = none := by
  intro F info hp
  rw [h] at hp
  exact .inl hp

private theorem EliminatorsCoherent.addInduct (H : env.EliminatorsCoherent) (henv : env.Ordered)
    (hadd : env.AddInduct decl env') : env'.EliminatorsCoherent := by
  cases hadd with
  | @intro block installed hdecl hcompile hblock helim hinstall =>
    obtain ⟨eT, eC, hT', hC', helim⟩ := helim
    simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hinstall
    obtain ⟨envTypes, htypes, envCtors, hctors, envRecs, hrecs, rfl⟩ := hinstall
    obtain rfl : envTypes = eT := Option.some.inj (htypes.symm.trans hT')
    obtain rfl : envCtors = eC := Option.some.inj (hctors.symm.trans hC')
    have hle : env ≤ (envRecs.addDefEqRules block.rules) :=
      (((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)).trans
        (VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le hrecs))).trans
          VEnv.addDefEqRules_le
    have hproj : ∀ F info, (envRecs.addDefEqRules block.rules).projections F info →
        (∃ entry ∈ block.projections, F = entry.typeName ∧ info = entry.info) ∨
          env.projections F info := by
      intro F info hp
      rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hrecs,
        VEnv.addProjections_iff, VEnv.addEliminators_projections,
        VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hp
      exact hp
    intro k s hs
    rw [addDefEqRules_eliminators, VEnv.addConstVals_eliminators hrecs,
      VEnv.addProjections_eliminators, VEnv.addEliminators_iff,
      VEnv.addConstVals_eliminators hctors, VEnv.addConstVals_eliminators htypes] at hs
    rcases hs with hnew | hold
    · rcases helim with ⟨-, hE⟩ | ⟨key, schema, hE, ⟨hcert, hkey, -⟩, hprojs⟩
      · rw [hE] at hnew; cases hnew
      rw [hE] at hnew
      simp only [List.mem_singleton, Prod.mk.injEq] at hnew
      obtain ⟨rfl, rfl⟩ := hnew
      refine ⟨env, decl, block, hle, hcert, fun value hv => ?_,
        coherent_new henv hcompile.types hcompile.projections htypes hproj⟩
      have hle' : envCtors ≤ envRecs.addDefEqRules block.rules :=
        (VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le hrecs)).trans
          VEnv.addDefEqRules_le
      rcases List.mem_append.mp hv with hv | hv
      · exact hle'.constants ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hv))
      · exact hle'.constants (VEnv.addConstVals_get hctors hv)
    · refine H.extendAt hle (fun F info hp => ?_) hold
      rcases hproj F info hp with ⟨entry, hentry, rfl, rfl⟩ | hp
      · right
        rw [hcompile.projections] at hentry
        obtain ⟨type, htype, ctor, _, rfl⟩ := decl.projectionEntries_origin hentry
        exact VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
          rw [hcompile.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      · exact .inl hp

private theorem EliminatorsCoherent.addQuot (H : env.EliminatorsCoherent)
    (hadd : env.addQuot = some env') : env'.EliminatorsCoherent := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hadd
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hadd
  have hle : env ≤ d.addDefEq quotDefEq :=
    ((((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)).trans
      (VEnv.addConst_le hc)).trans (VEnv.addConst_le hd)).trans VEnv.addDefEq_le
  apply H.extend hle
  · rw [VEnv.addDefEq_eliminators, VEnv.addConst_eliminators hd, VEnv.addConst_eliminators hc,
      VEnv.addConst_eliminators hb, VEnv.addConst_eliminators ha]
  · exact old_projections ((VEnv.addConst_projections hd).trans <|
      (VEnv.addConst_projections hc).trans <|
        (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha))

theorem WF'.eliminatorsCoherent {ds : List VDecl} (H : VEnv.WF' ds env) :
    env.EliminatorsCoherent := by
  induction H with
  | empty => intro _ _ h; cases h
  | @decl d env' ds env hdecl hbase ih =>
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      exact ih.extend (VEnv.addConst_le hadd) (VEnv.addConst_eliminators hadd)
        (old_projections (VEnv.addConst_projections hadd))
    | «example» => exact ih
    | @«def» _ _ ci _ hadd =>
      exact ih.extend ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le)
        (by rw [VEnv.addDefEq_eliminators, VEnv.addConst_eliminators hadd])
        (fun F info hp => .inl ((VEnv.addConst_projections hadd) ▸ hp))
    | mutualDef _ hadd _ =>
      have hadd' := VEnv.addConsts_eq_addConstVals ▸ hadd
      apply ih.extend
      · rw [VEnv.addDefEqs_eq_addDefEqRules]
        exact (VEnv.addConsts_le hadd).trans VEnv.addDefEqRules_le
      · rw [VEnv.addDefEqs_eq_addDefEqRules, addDefEqRules_eliminators, VEnv.addConstVals_eliminators hadd']
      · apply old_projections
        rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hadd']
    | quot _ hadd => exact ih.addQuot hadd
    | induct hadd => exact ih.addInduct (show env.WF from ⟨ds, hbase⟩).ordered hadd
  | inductEliminators hbase henv hle hreg hconstants _ _ hcoherent hfresh _ ihBase ih =>
    intro k s hs
    rcases hs with ⟨rfl, rfl⟩ | hs
    · refine ⟨_, _, _, hle.trans VEnv.addEliminator_le, hreg.certified,
        fun v hv => VEnv.addEliminator_le.constants (hconstants v hv), ?_⟩
      intro type htype info hp
      exact hcoherent type htype info hp
    · obtain ⟨b, src, blk, hbl, hc, hconst, hcoh⟩ := ih k s hs
      exact ⟨b, src, blk, hbl.trans VEnv.addEliminator_le, hc,
        fun v hv => VEnv.addEliminator_le.constants (hconst v hv), hcoh⟩
  | @inductProjections baseDecls ds base envTypes envCtors decl block
      hbase _ hcert hsource _ _ _ _ _ htypesSource _ hprojections htypes hctors ihBase ihCtors =>
    obtain ⟨key, schema, hE, ⟨hcertS, hkey, -⟩⟩ := hcert
    have hbaseOrdered := (show base.WF from ⟨baseDecls, hbase⟩).ordered
    have hle : base ≤ (envCtors.addEliminators block.eliminators).addProjections block.projections :=
      (VEnv.addConstVals_le htypes).trans ((VEnv.addConstVals_le hctors).trans
        VEnv.addEliminators_addProjections_le)
    have hproj : ∀ F info, ((envCtors.addEliminators block.eliminators).addProjections
        block.projections).projections F info →
        (∃ entry ∈ block.projections, F = entry.typeName ∧ info = entry.info) ∨
          base.projections F info := by
      intro F info hp
      rw [VEnv.addProjections_iff, VEnv.addEliminators_projections,
        VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hp
      exact hp
    intro k s hs
    rw [VEnv.addProjections_eliminators, VEnv.addEliminators_iff,
      VEnv.addConstVals_eliminators hctors, VEnv.addConstVals_eliminators htypes] at hs
    rcases hs with hnew | hold
    · rw [hE] at hnew
      simp only [List.mem_singleton, Prod.mk.injEq] at hnew
      obtain ⟨rfl, rfl⟩ := hnew
      refine ⟨base, decl, block, hle, hcertS, fun value hv => ?_,
        coherent_new hbaseOrdered htypesSource hprojections htypes hproj⟩
      have hle' : envCtors ≤ (envCtors.addEliminators block.eliminators).addProjections
          block.projections := VEnv.addEliminators_addProjections_le
      rcases List.mem_append.mp hv with hv | hv
      · exact hle'.constants ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hv))
      · exact hle'.constants (VEnv.addConstVals_get hctors hv)
    · refine ihBase.extendAt hle (fun F info hp => ?_) hold
      rcases hproj F info hp with ⟨entry, hentry, rfl, rfl⟩ | hp
      · right
        rw [hprojections] at hentry
        obtain ⟨type, htype, ctor, _, rfl⟩ := decl.projectionEntries_origin hentry
        exact VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
          rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      · exact .inl hp

/-- Registered case eliminators are coherent with registered projections in
every well-formed environment. -/
theorem WF.eliminatorsCoherent (H : env.WF) : env.EliminatorsCoherent :=
  H.choose_spec.eliminatorsCoherent

end Lean4Lean.VEnv
