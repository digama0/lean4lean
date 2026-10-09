import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.CaseProjNames
import Lean4Lean.Theory.Typing.ProjNamesTyping
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! Case-eliminator certificates over installing extensions.

The replay and monotone certificates below refer only to abstract declarations
and environments. The checked formation supplies their concrete refinement in
`Verify/Inductive/Constructor/CheckedFormation.lean`.
-/

namespace Lean4Lean

theorem InductiveSignature.vars_append_eq_bvarRange (a b : Nat) :
    vars a b ++ vars b 0 = VExpr.bvarRange (a + b) (a + b) := by
  apply List.ext_getElem
  · simp [vars]
  · intro j h1 h2
    simp only [List.length_append, vars, List.length_map, List.length_reverse,
      List.length_range] at h1
    rw [VExpr.bvarRange_getElem _ _ _ (by omega)]
    by_cases hj : j < a
    · rw [List.getElem_append_left (by simp [vars]; omega)]
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, VExpr.bvar.injEq]
      omega
    · rw [List.getElem_append_right (by simp [vars]; omega)]
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, List.length_map, List.length_reverse, VExpr.bvar.injEq]
      omega


/-- The block's eliminators are certified over every environment in which its families and
constructors install. Larger safety models of the same kernel environment are such
environments. -/
def VInductBlock.EliminatorsReplay (env : VEnv) (decl : VInductDecl) (block : VInductBlock) :
    Prop :=
  ∀ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes →
    envTypes.addConstVals decl.constructorConstants = some envCtors →
    VInductBlock.EliminatorsWF env decl block

theorem VInductBlock.EliminatorsReplay.eliminatorsWF {env : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsReplay env decl block)
    (hdecl : decl.SourceWF env) : VInductBlock.EliminatorsWF env decl block := by
  obtain ⟨-, -, -, -, envTypes, envCtors, ht, hc, -⟩ := hdecl
  exact H envTypes envCtors ht hc

theorem VInductBlock.EliminatorsReplay.congr_block {env : VEnv} {decl : VInductDecl}
    {block block' : VInductBlock} (H : VInductBlock.EliminatorsReplay env decl block)
    (h : block' = block) : VInductBlock.EliminatorsReplay env decl block' := h ▸ H

theorem VInductBlock.EliminatorsReplay.congr_fields {env : VEnv} {decl : VInductDecl}
    {block block' : VInductBlock} (H : VInductBlock.EliminatorsReplay env decl block)
    (htypes : block'.types = block.types) (hctors : block'.ctors = block.ctors)
    (hprojections : block'.projections = block.projections)
    (heliminators : block'.eliminators = block.eliminators) :
    VInductBlock.EliminatorsReplay env decl block' := fun T C ht hc =>
  (H T C ht hc).congr_block htypes hctors hprojections heliminators

/-- **Case eliminators certified along extensions**, the monotone form of
`VInductBlock.EliminatorsWF`. The case eliminators `es` of `decl` are certified
(`EliminatorsWF`) over every extension of `env` in which the names satisfying `reserved` are
fresh and the declaration's families and constructors install. `EliminatorsWF` itself is not
monotone: its certificate fixes freshness of the declaration's names in the base. An ordinary
declaration reserves no names (its certificate only needs its own names fresh, which
installation provides); a nested one reserves the names fresh in its kernel environment,
which include its auxiliary families and recursors. Views: `EliminatorsReplay` at one
environment (`CaseEliminators.replay`) and `EliminatorsWF` at the base
(`CaseEliminators.eliminatorsWF`). -/
def VInductDecl.CaseEliminators (env : VEnv) (decl : VInductDecl) (reserved : Name → Prop)
    (es : List (Name × InductiveSignature.CaseSchema)) : Prop :=
  ∀ env', env ≤ env' → (∀ n, reserved n → env'.constants n = none) →
    VInductBlock.EliminatorsReplay env' decl (decl.caseBlock es)

theorem VInductDecl.CaseEliminators.mono {env env' : VEnv} {decl : VInductDecl}
    {reserved : Name → Prop} {es : List (Name × InductiveSignature.CaseSchema)}
    (H : decl.CaseEliminators env reserved es) (hle : env ≤ env') :
    decl.CaseEliminators env' reserved es := fun env'' hle' =>
  H env'' (hle.trans hle')

theorem VInductDecl.CaseEliminators.replay {env env' : VEnv} {decl : VInductDecl}
    {reserved : Name → Prop} {es : List (Name × InductiveSignature.CaseSchema)}
    {block : VInductBlock} (H : decl.CaseEliminators env reserved es) (hle : env ≤ env')
    (hfresh : ∀ n, reserved n → env'.constants n = none)
    (htypes : block.types = decl.typeConstants) (hctors : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (heliminators : block.eliminators = es) :
    VInductBlock.EliminatorsReplay env' decl block :=
  (H env' hle hfresh).congr_fields htypes hctors hprojections heliminators

theorem VInductDecl.CaseEliminators.eliminatorsWF {env : VEnv} {decl : VInductDecl}
    {reserved : Name → Prop} {es : List (Name × InductiveSignature.CaseSchema)}
    (H : decl.CaseEliminators env reserved es)
    (hfresh : ∀ n, reserved n → env.constants n = none) (hdecl : decl.SourceWF env) :
    VInductBlock.EliminatorsWF env decl (decl.caseBlock es) :=
  (H env .rfl hfresh).eliminatorsWF hdecl

/-- The monotone ingredients of the certificate of the case eliminators of an ordinary
declaration: none for a declaration without families, otherwise the case schema of a source
signature of the declaration (`CaseSchema.ofCompilation decl s []`) under the key of its first
family. -/
private def ordinaryCaseIngredients (env : VEnv) (decl : VInductDecl)
    (es : List (Name × InductiveSignature.CaseSchema)) : Prop :=
  (decl.types = [] ∧ es = []) ∨
  ∃ (s : InductiveSignature) (key : Name),
    es = [(key, InductiveSignature.CaseSchema.ofCompilation decl s [])] ∧
    decl.types.head?.map (·.name) = some key ∧
    decl.SourceWF env ∧ decl.OrdinaryFormationWF env ∧ s.Models env decl ∧
    ∃ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes ∧
      envTypes.addConstVals decl.constructorConstants = some envCtors ∧
      s.FamilyTypesWF (envCtors.addProjections decl.projectionEntries) decl.uvars ∧
      (InductiveSignature.CaseSchema.ofCompilation decl s []).ProjNamesRegistered envCtors key ∧
      (InductiveSignature.CaseSchema.ofCompilation decl s []).HeaderAgreement env decl

private theorem ordinaryCaseIngredients.eliminatorsWF {env : VEnv} {decl : VInductDecl}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (H : ordinaryCaseIngredients env decl es)
    (hadded : ∃ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes ∧
      envTypes.addConstVals decl.constructorConstants = some envCtors) :
    VInductBlock.EliminatorsWF env decl (decl.caseBlock es) := by
  rcases H with ⟨hT, hE⟩ | ⟨s, key, hE, hkey, hsource, hformation, hmodel, envTypes, envCtors,
    ht, hc, hfam, hprojs, hhdr⟩
  · obtain ⟨envTypes, envCtors, ht, hc⟩ := hadded
    exact ⟨envTypes, envCtors, ht, hc, .inl ⟨hT, hE⟩⟩
  · refine ⟨envTypes, envCtors, ht, hc, .inr ⟨key, _, hE, ⟨?_, hkey, hhdr⟩, hprojs⟩⟩
    exact InductiveSignature.CaseSchema.ofCaseCompilation_certified
      (InductiveSignature.CaseCompilationData.ofOrdinary hsource hformation hmodel ht hc
        (es := []) (fun _ h => by cases h) hfam rfl rfl rfl) .nil
      InductiveSignature.recursorNamesFresh_nil

private theorem ordinaryCaseIngredients.mono {env env' envTypes' envCtors' : VEnv}
    {decl : VInductDecl} {es : List (Name × InductiveSignature.CaseSchema)}
    (H : ordinaryCaseIngredients env decl es) (hle : env ≤ env')
    (htypes' : env'.addConstVals decl.typeConstants = some envTypes')
    (hctors' : envTypes'.addConstVals decl.constructorConstants = some envCtors') :
    ordinaryCaseIngredients env' decl es := by
  rcases H with H | ⟨s, key, hE, hkey, hsource, hformation, hmodel, envTypes, envCtors,
    ht, hc, hfam, hprojs, ⟨RP, hRP, hhdr⟩⟩
  · exact .inl H
  have htLE : envTypes ≤ envTypes' := VEnv.addConstVals_mono hle ht htypes'
  have hcLE : envCtors ≤ envCtors' := VEnv.addConstVals_mono htLE hc hctors'
  refine .inr ⟨s, key, hE, hkey, hsource.mono_of_addConstVals hle htypes' hctors',
    hformation.mono_of_addConstVals hle htypes', hmodel.mono hle htypes', envTypes', envCtors',
    htypes', hctors', hfam.mono (VEnv.addProjections_mono hcLE), hprojs.mono hcLE,
    RP, hRP, fun owner => ?_⟩
  obtain ⟨RI, hRI, hagree⟩ := hhdr owner
  refine ⟨RI, hRI, fun type htype hname => ?_⟩
  obtain ⟨envTypes₀, ht₀, hdefeq⟩ := hagree type htype hname
  exact ⟨envTypes', htypes', hdefeq.mono (VEnv.addConstVals_mono hle ht₀ htypes')⟩

/-- Ordinary case eliminators are certified along every extension: their ingredients are
monotone once the families and constructors install. -/
private theorem ordinaryCaseIngredients.caseEliminators {env : VEnv} {decl : VInductDecl}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (H : ordinaryCaseIngredients env decl es) : decl.CaseEliminators env (fun _ => False) es :=
  fun _ hle _ _ _ ht hc => (H.mono hle ht hc).eliminatorsWF ⟨_, _, ht, hc⟩

/-- The case eliminators of an ordinary declaration are its own restoration-free case
schemas. -/
private theorem ordinaryCaseIngredients.own {env : VEnv} {decl : VInductDecl}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (H : ordinaryCaseIngredients env decl es) : decl.OwnCaseEliminators env es := by
  rcases H with ⟨-, hE⟩ | ⟨s, key, hE, -, -, -, hmodel, -⟩
  · intro p hp; rw [hE] at hp; cases hp
  · intro p hp
    rw [hE] at hp
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨rfl, rfl, hmodel⟩

/-- The constructor stage of a block with its certified eliminators is well formed, given that
the constructor stage itself is. -/
theorem VInductBlock.EliminatorsWF.casesWF {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsWF base decl block) (hbase : base.WF)
    (hctorsWF : envCtors.WF)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addEliminators block.eliminators).WF := by
  obtain ⟨eT, eC, ht, hc, helim⟩ := H
  cases htypes.symm.trans ht
  cases hctors.symm.trans hc
  rcases helim with ⟨-, hE⟩ | ⟨key, schema, hE, hreg, hprojs⟩
  · rw [hE]; exact hctorsWF
  · rw [hE]
    exact hreg.register_after_constructors hbase htypes hctors hprojs

end Lean4Lean
