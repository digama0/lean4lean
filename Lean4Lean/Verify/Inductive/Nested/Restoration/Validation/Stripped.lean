import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Checks
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Install.Rebase

/-! # The rule-free recursor stage is a checking environment (owner: Restoration-A)

`validateRestoredRecursorRules` runs in `stripRecursorRules outEnv names`: the restored
environment with the rule lists of the new recursors emptied. Its model is the recursor stage
`H.envR` of the block, where the restored rules are not yet registered, so that the validation
does not use the rules it validates. The stripped environment is the installation of the
*rule-free* declaration (every recursor with `rules := []`) over the source environment, so the
statement here is about an arbitrary rule-free `AddInduct`: given the checking invariant of the
source environment and the facts `RuleFreeStage` about the new block (all of them rule-free:
the projection stage, the recursor types, the restored headers, the K clause and shapes of the
new recursors), the output is a checking environment over `H.envR`
(`RuleFreeStage.checkingValid`), and a checker environment (`RuleFreeStage.checkerEnv`). The
descriptor of the new block is built by `InstalledBlocks.addCtorStage`, as in the ordinary
recursor phase (`RecursorInstallation.checkingValid`).

This replaces the source branch's `Validation/StrippedEnvironment.lean`
(`NestedRestorationFolds.validOfInstallation_of_shapes`), which took the same rule-free data. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The rule-free facts about a block installation `H` into `S` (see the module
documentation). For the stripped restored environment `S = stripRecursorRules outEnv names`
and the restored declaration with every recursor's rules removed. -/
structure RuleFreeStage (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (decl : VInductDecl) (S : Environment) (venv₂ : VEnv)
    (H : AddInduct safety env.constants venv decl S.constants venv₂) : Prop where
  /-- The declaration carries no rule. -/
  rules_empty : ∀ r ∈ decl.recs, r.rules = []
  quotInit : S.quotInit = env.quotInit
  /-- The projection stage is a well-formed environment (`VEnv.WF.inductProjections`). -/
  envP_wf : H.envP.WF
  /-- The recursor types are types of the projection stage. -/
  recs_wf : ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF H.envP
  /-- No constant of the block is a checker primitive. -/
  nonprimitive : ∀ ci ∈ AddInduct.consts H.ivals H.rvals,
    ¬ Kernel.Environment.primitives.contains ci.name
  /-- The headers of the source environment list present constructors. -/
  listedPresent : ListedConstructorsPresent env
  typeUvars : ∀ T ∈ decl.types, T.uvars = decl.uvars
  constructorUvars : ∀ c ∈ decl.constructorConstants, c.uvars = decl.uvars
  /-- The kernel headers of the block are aligned with the declaration. -/
  origins : InductInfosFromDecl env.constants S.constants decl
  cover : ∀ T ∈ decl.types,
    ∃ v, S.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none
  owners : ConstructorOwnersPresent S
  recMajor : ∀ r ∈ H.rvals, ∃ info, S.find? r.getMajorInduct = some (.inductInfo info)
  /-- The K clause of every new recursor, at the recursor stage. -/
  recK : ∀ r ∈ H.rvals, safety ≤ (ConstantInfo.recInfo r).safety →
    KLikeRecursor S.constants H.envR r
  /-- The shapes of every new recursor, at the recursor stage. -/
  recShapes : ∀ r ∈ H.rvals, safety ≤ (ConstantInfo.recInfo r).safety →
    RecursorShapesAt S.constants H.envR r

/-- Adding well-typed constants as axioms keeps the environment well formed. -/
theorem VEnv.WF.addConstVals_axioms : ∀ {env env' : VEnv} {vs : List VConstVal},
    env.WF → (∀ v ∈ vs, v.toVConstant.WF env) → env.addConstVals vs = some env' → env'.WF
  | _, _, [], h, _, hadd => by cases hadd; exact h
  | env, env', v :: vs, h, hv, hadd => by
    simp only [VEnv.addConstVals] at hadd
    cases hmid : env.addConst v.name v.toVConstant with
    | none => simp [hmid] at hadd
    | some mid =>
      simp only [hmid, Option.bind_eq_bind, Option.bind_some] at hadd
      obtain ⟨ds, hds⟩ := h
      have hmidWF : mid.WF := ⟨_, hds.decl (.axiom (ci := v) (hv v (.head _)) hmid)⟩
      exact VEnv.WF.addConstVals_axioms hmidWF
        (fun w hw => (hv w (.tail _ hw)).mono (VEnv.addConst_le hmid)) hadd


/-! ### Recursor facts of the stripped recursors

The stripped environment's new recursors are the restored ones with their rules removed. Their
shapes read only the model's constants, which the rule stage does not change, so the shapes in
the output model (`RestoredBlock.recShapes`) give them at the recursor stage; and a recursor of
a nested block is not K-like (its expanded block has an auxiliary family), so the K clause is
vacuous. -/

/-- Recursor shapes read only the constants of the model; with the rules removed, the rule
clauses are vacuous. -/
theorem RecursorShapesAt.stripRules {C C' : ConstMap} {venv venv' : VEnv} {r : RecursorVal}
    (hconst : ∀ n, venv.constants n = venv'.constants n) (H : RecursorShapesAt C venv r) :
    RecursorShapesAt C' venv' { r with rules := [] } := by
  obtain ⟨⟨cnparams, indLevels, ctorParams, ⟨S⟩, -⟩, -⟩ := H
  refine ⟨⟨cnparams, indLevels, ctorParams, ⟨{ S with const := ?_ }⟩, nofun⟩, nofun⟩
  rw [← hconst]; exact S.const

/-- A recursor that is not K-like satisfies the K clause. -/
theorem KLikeRecursor.of_k_false {C : ConstMap} {venv : VEnv} {r : RecursorVal}
    (hk : r.k = false) : KLikeRecursor C venv r := fun h => by rw [hk] at h; cases h

/-- The rule stage keeps the constants. -/
theorem addRules_constants_eq' {decl : VInductDecl} {envR env' : VEnv}
    (h : decl.addRules envR = some env') : ∀ n, envR.constants n = env'.constants n := by
  intro n; rw [VEnv.addRules_constants h]

namespace RuleFreeStage

variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv} {decl : VInductDecl}
  {S : Environment} {venv₂ : VEnv} {H : AddInduct safety env.constants venv decl S.constants venv₂}

/-- With no rules, the rule stage is the recursor stage. -/
theorem venv₂_eq (F : RuleFreeStage safety env venv decl S venv₂ H) : venv₂ = H.envR := by
  have h := H.stP
  unfold VInductDecl.addRules at h
  have : ∀ (rs : List VRecursor) (e : VEnv), (∀ r ∈ rs, r.rules = []) →
      rs.foldlM (init := e) (fun e r => r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru)
        = some e := by
    intro rs
    induction rs with
    | nil => intro e _; rfl
    | cons r rs ih =>
      intro e hr
      simp only [List.foldlM_cons, hr r (.head _), List.foldlM_nil]
      exact ih e fun r' h' => hr r' (.tail _ h')
  rw [this _ _ F.rules_empty] at h
  exact (Option.some.inj h).symm

theorem le_envP : venv ≤ H.envP :=
  (VEnv.addTypes_le H.stT).trans ((VEnv.addCtors_le H.stC).trans VEnv.addProjs_le)

theorem envP_le_envR : H.envP ≤ H.envR := VEnv.addRecs_le H.stR

theorem le_envR : venv ≤ H.envR := le_envP.trans envP_le_envR

theorem envR_defeqs : H.envR.defeqs = venv.defeqs := by
  rw [VEnv.addRecs_defeqs H.stR, VEnv.addProjs_defeqs, VEnv.addCtors_defeqs H.stC,
    VEnv.addTypes_defeqs H.stT]

theorem envR_pats : H.envR.pats = venv.pats := by
  have hR := H.stR
  have hT := H.stT
  have hC := H.stC
  rw [VInductDecl.addRecs_eq_addConstVals] at hR
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  rw [VInductDecl.addCtors_eq_addConstVals] at hC
  rw [VEnv.addConstVals_pats hR]
  change (H.envC.addProjections decl.projectionEntries).pats = _
  rw [VEnv.addProjections_pats, VEnv.addConstVals_pats hC, VEnv.addConstVals_pats hT]

theorem envR_projections {S' : Name} {info : VProjectionInfo} (h : H.envR.projections S' info) :
    venv.projections S' info ∨ ⟨S', info⟩ ∈ decl.projectionEntries := by
  have hR := H.stR
  have hT := H.stT
  have hC := H.stC
  rw [VInductDecl.addRecs_eq_addConstVals] at hR
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  rw [VInductDecl.addCtors_eq_addConstVals] at hC
  rw [VEnv.addConstVals_projections hR] at h
  rcases VEnv.addProjections_iff.mp h with ⟨e, he, rfl, rfl⟩ | h
  · exact .inr he
  · left
    rwa [VEnv.addConstVals_projections hC, VEnv.addConstVals_projections hT] at h

/-- The recursor stage is well formed: the recursors are axioms over the projection stage. -/
theorem envR_wf (F : RuleFreeStage safety env venv decl S venv₂ H) : H.envR.WF := by
  have hR := H.stR
  rw [VInductDecl.addRecs_eq_addConstVals] at hR
  refine VEnv.WF.addConstVals_axioms F.envP_wf ?_ hR
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  exact F.recs_wf r hr

theorem nonprimitive_names (F : RuleFreeStage safety env venv decl S venv₂ H) :
    ∀ n ∈ decl.types.map (·.name) ++ (decl.types.flatMap (·.ctors)).map (·.name) ++
      decl.recs.map (·.name), ¬ Kernel.Environment.primitives.contains n := by
  intro n hn
  rw [← H.consts_names] at hn
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
  exact F.nonprimitive ci hci

theorem hasPrimitives (F : RuleFreeStage safety env venv decl S venv₂ H)
    (hprim : venv.HasPrimitives) : H.envR.HasPrimitives := by
  have hR := H.stR
  have hT := H.stT
  have hC := H.stC
  rw [VInductDecl.addRecs_eq_addConstVals] at hR
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  rw [VInductDecl.addCtors_eq_addConstVals] at hC
  have hn := F.nonprimitive_names
  have hTp := CtorInstall.HasPrimitives_addConstVals hprim (fun v hv => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact hn _ (by simp only [List.mem_append, List.mem_map]; exact .inl (.inl ⟨t, ht, rfl⟩)))
    hT
  have hCp := CtorInstall.HasPrimitives_addConstVals hTp (fun v hv => by
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hv
    exact hn _ (by
      simp only [List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl (.inr ⟨v, ⟨t, ht, hc⟩, rfl⟩))) hC
  exact CtorInstall.HasPrimitives_addConstVals hCp.addProjections (fun v hv => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    exact hn _ (by simp only [List.mem_append, List.mem_map]; exact .inr ⟨r, hr, rfl⟩)) hR

theorem declRegistered (F : RuleFreeStage safety env venv decl S venv₂ H) :
    InstalledBlocks.DeclRegistered H.envR decl where
  typeUvars := F.typeUvars
  constructorUvars := F.constructorUvars
  family i hi := by
    apply ((VEnv.addCtors_le H.stC).trans (VEnv.addProjs_le.trans envP_le_envR)).constants
    exact VEnv.addTypes_find H.stT _ (List.getElem_mem hi)
  ctor i k hi hk := by
    apply (VEnv.addProjs_le.trans envP_le_envR).constants
    exact VEnv.addCtors_find H.stC _ (List.getElem_mem hi) _ (List.getElem_mem hk)
  projections e he :=
    envP_le_envR.projections (VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩))

/-- **The rule-free recursor stage is a checking environment.** -/
theorem checkingValid (F : RuleFreeStage safety env venv decl S venv₂ H)
    (hin : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety S H.envR := by
  have wf₁ : env.constants.WF := hin.tr.map_wf
  have wfS : S.constants.WF := H.wf wf₁
  have hfindE : ∀ x, env.find? x = env.constants.find? x := fun x => by
    rw [Lean.Kernel.Environment.find?, wf₁.find?'_eq_find?]
  have hfindS : ∀ x, S.find? x = S.constants.find? x := fun x => by
    rw [Lean.Kernel.Environment.find?, wfS.find?'_eq_find?]
  have hpresMap : ∀ {n ci}, env.constants.find? n = some ci → S.constants.find? n = some ci :=
    fun h => H.find?_mono wf₁ h
  have hpres : ∀ {n ci}, env.find? n = some ci → S.find? n = some ci := fun h => by
    rw [hfindS]; rw [hfindE] at h; exact hpresMap h
  have hal : Aligned safety S.constants H.envR := by
    have := Aligned.addInduct H hin.tr.aligned
    rwa [F.venv₂_eq] at this
  have hcore : CheckingEnv.ValidCore safety S H.envR := {
    tr := {
      aligned := hal
      wf := F.envR_wf
      of_value := by
        intro name ci v hfind hs hv
        rw [hfindS] at hfind
        have hold := H.value_find wf₁ hfind hv
        rw [← hfindE] at hold
        exact (hin.tr.of_value hold hs hv).mono le_envR }
    hasPrimitives := F.hasPrimitives hin.hasPrimitives
    safePrimitives := by
      intro n ci hfind hprim
      rw [hfindS] at hfind
      rcases H.find? wf₁ hfind with hold | ⟨hci, hname⟩
      · exact hin.safePrimitives (by rw [hfindE]; exact hold) hprim
      · exact absurd (hname ▸ hprim) (F.nonprimitive ci hci) }
  have hheads : EquationHeadsCoherent S.constants H.envR :=
    hin.equationHeads.extendSimple hpresMap (fun df h => by rwa [envR_defeqs] at h)
      (fun p r h => by rwa [envR_pats] at h)
  have hnodup : (decl.types.map (·.name)).Nodup := by
    have h := H.names_nodup
    rw [H.consts_names] at h
    exact (List.nodup_append.mp (List.nodup_append.mp h).1).1
  have hblocks : InstalledBlocks safety S H.envR .headers := by
    refine hin.blocks.addCtorStage F.listedPresent wf₁ hcore.tr hpres le_envR F.origins F.cover
      hnodup F.owners H.rvals ?_ ?_ F.recMajor F.recK F.declRegistered
      (fun h => envR_projections h) F.recShapes
    · intro n r hf hnone
      rw [hfindS] at hf
      rcases H.find? wf₁ hf with hold | ⟨hci, -⟩
      · rw [hfindE, hold] at hnone; cases hnone
      · rcases AddInduct.mem_consts.mp hci with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨r', hr', h⟩
        · cases h
        · cases h
        · cases h; exact hr'
    · intro r hr
      have hci : ConstantInfo.recInfo r ∈ AddInduct.consts H.ivals H.rvals :=
        AddInduct.mem_consts.mpr (.inr (.inr ⟨r, hr, rfl⟩))
      refine ⟨by rw [hfindS]; exact H.find?_self wf₁ hci, ?_⟩
      rw [hfindE]; exact H.fresh _ hci
  exact hcore.toValid hblocks hheads fun hq =>
    (hin.quot (by rw [← F.quotInit]; exact hq)).extend hpresMap le_envR hheads

/-- **The rule-free recursor stage is a checker environment**: the new recursors carry no
rule, and the ι rules of the old ones are registered in the source model. -/
theorem checkerEnv (F : RuleFreeStage safety env venv decl S venv₂ H)
    (C : CheckerEnv safety env venv) : CheckerEnv safety S H.envR := by
  have V := F.checkingValid C.toValid
  have wf₁ : env.constants.WF := C.tr.map_wf
  have wfS : S.constants.WF := H.wf wf₁
  have hfindE : ∀ x, env.find? x = env.constants.find? x := fun x => by
    rw [Lean.Kernel.Environment.find?, wf₁.find?'_eq_find?]
  have hfindS : ∀ x, S.find? x = S.constants.find? x := fun x => by
    rw [Lean.Kernel.Environment.find?, wfS.find?'_eq_find?]
  refine { V with shapes := V.blocks.recursorShapesCoherent V.tr.map_wf, iota := ?_ }
  intro recName cName rval rule hrec hrule hsafe
  rw [hfindS] at hrec
  rcases H.find? wf₁ hrec with hold | ⟨hci, -⟩
  · rw [← hfindE] at hold
    obtain ⟨cval, rhs, hc, hcval, hrhs, hpat⟩ := C.iota hold hrule hsafe
    refine ⟨cval, rhs, hc, ?_, hrhs.mono le_envR, ?_⟩
    · rw [hfindS]; rw [hfindE] at hcval; exact H.find?_mono wf₁ hcval
    · rw [envR_pats]; exact hpat
  · rcases AddInduct.mem_consts.mp hci with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨r', hr', h⟩
    · cases h
    · cases h
    · cases h
      obtain ⟨r, hr, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_l H.recs _ hr'
      have hnil : rval.rules = [] := by
        have h := htr.rules
        rw [F.rules_empty r hr] at h
        exact List.forall₂_nil_right_iff.mp h
      rw [hnil] at hrule
      cases hrule

end RuleFreeStage

end VerifyInductive
end Lean4Lean
