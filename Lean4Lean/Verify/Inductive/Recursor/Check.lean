import Lean4Lean.Verify.Inductive.RecursorInput  -- WAVE 2 install COMPAT
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.Checking

/-! # The recursor phase

After the constructors, the executable computes the elimination level, the K flag and the
recursor infos (`mkRecInfos`: motives, minors, rule templates), checks the recursive fields and
declares the recursors (`declareRecursors`, which type-checks every generated recursor type and
instantiates the rule templates). `RecursorCheck` is the frozen interface of the resulting
environment: the kernel recursors `rvals`, the model recursors `recs` they translate to
(PR #43's `TrRecursor`, with the rules' reducts translated in the recursor-stage environment),
the recursor-stage environment `outVEnv`, the shape clauses of `VInductDecl.WF`, and the
signature generator (`signature`, `generation`) whose recursors the `recs` are. The rules'
typing and their identification with the generated equations are the rule phase's
(`Rules/RuleTranslations.lean`). `RecursorInput.recursorPhasesWF` is the boundary theorem.

Wave 2 scaffold: owned by the `Recursor/**` agent (source branch: `Recursor/{Check,
Construction,Metadata,RecInfoCheck,InstanceAlignment}.lean`, `Recursor/{Binders,Context,
Elimination,Entries,Signature}/**`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor check: the recursors are installed over the constructor environment, typed in
the projection stage, and translate to the generated recursors of a signature instance that
models the declaration. -/
structure RecursorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)  -- WAVE 2 install COMPAT
    (outEnv : Environment) where
  elimLevel : Level
  elimLevelChecked : AddInductive.getElimLevel stats indTypes { c with env := ctorEnv } =
    .ok elimLevel
  kTarget : Bool
  /-- The kernel recursors, one per family, in family order. -/
  rvals : List RecursorVal
  rvals_names : rvals.map (·.name) = indTypes.toList.map (Lean.mkRecName ·.name)
  /-- The model recursors with their ι rules. -/
  recs : List VRecursor
  /-- The recursor-stage environment: the projection stage with the recursors added. -/
  outVEnv : VEnv
  recsAdded : (decl.withRecs recs).addRecs R.envP = some outVEnv
  /-- Each kernel recursor translates to its model recursor (PR #43's `TrRecursor`): type in
  the constructor stage, telescope split and K flag copied, rules matched one to one with
  reducts translated in the recursor stage and constructor parameter counts read off the
  output map. -/
  trRecs : List.Forall₂ (TrRecursor c.safety R.envP outVEnv outEnv.constants) rvals recs
  map_eq : outEnv.constants = insertConsts ctorEnv.constants (rvals.map .recInfo)
  quotInit_eq : outEnv.quotInit = ctorEnv.quotInit
  fresh : ∀ rval ∈ rvals, ctorEnv.find? rval.name = none
  /-- The recursor-stage environment is a valid checking environment of the output. -/
  checking : CheckingEnv.Valid c.safety outEnv outVEnv
  /-- `VInductDecl.WF.recs_wf`: the recursors are typed in the projection stage. -/
  recsWF : ∀ r ∈ recs, r.toVConstVal.toVConstant.WF R.envP
  /-- `VInductDecl.WF.rec_shape`. -/
  rec_shape : ∀ r ∈ recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  /-- `VInductDecl.WF.rules_nodup`. -/
  rules_nodup : ∀ r ∈ recs, (r.rules.map (·.ctor)).Nodup
  /-- `VInductDecl.WF.rules_ctor`, in the constructor stage. -/
  rules_ctor : ∀ r ∈ recs, ∀ ru ∈ r.rules,
    ∃ ci, R.ctorVEnv.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  /-- `VInductDecl.WF.rule_shape`. -/
  rule_shape : ∀ r ∈ recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  /-- Every reduct is closed, so `addRules` (hence `addInduct`) succeeds. -/
  rules_closed : ∀ r ∈ recs, ∀ ru ∈ r.rules, ru.rhs.Closed
  /-- The K clause of every new recursor (`InstalledBlocks.addInduct`'s `hrecK`). -/
  kLike : ∀ rval ∈ rvals, KLikeRecursor outEnv.constants outVEnv rval
  /-- The signature generator: a signature modelling the declaration and an admissible
  instance of it whose induction hypotheses and family applications are typed in the
  projection stage (the clauses of `InductiveSignature.Compiles`). -/
  signature : InductiveSignature
  generation : InductiveSignature.Instance signature
  models : signature.Models sourceEnv decl
  admissible : generation.Admissible R.headerVEnv
  ihsWellTyped : generation.GeneratedIHsWellTyped R.envP
  familyTypesWF : signature.FamilyTypesWF R.envP decl.uvars
  recursorNames : ∀ owner, generation.recursorName owner = signature.families[owner].name.str "rec"
  /-- The model recursors are the generated ones. -/
  recursors_eq : recs.map (·.toVConstVal) = generation.recursors
  /-- Each kernel recursor has the generated metadata of its owner. -/
  metadata : List.Forall₂ (fun (owner : Fin signature.families.size) rval =>
      InductiveSignature.RecursorMetadata generation outVEnv owner rval)
    (List.finRange signature.families.size) rvals
  closed : MutualInductivesClosed outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants decl
  constructorParameterAlignment : ∀ {safety},
    ConstructorParameterAlignment safety c.env sourceEnv →
    ConstructorParameterAlignment safety outEnv outVEnv
  /-- (Added by the recursor agent.) The source branch's recursor check: the recursor
  construction (elimination level, recursor infos, their binder and template typing, the
  generator) and the installation of the generated recursors. The rule phase reads the
  recursor internals here (`H.installation.recInfos`, `.entries`, `.generated`, `.ruleTyping`,
  `.generator`, ...); the interface fields above are read off it (`installation_*`). -/
  installation : RecursorInstallation R outEnv
  installation_elimLevel : installation.elimLevel = elimLevel
  installation_kTarget : installation.kTarget = kTarget
  installation_outVEnv : installation.outVEnv = outVEnv
  installation_rvals : installation.entries.map Prod.fst = rvals.map .recInfo
  installation_signature : installation.generationSignature = signature
  installation_generation : HEq installation.generationInstance generation
  installation_recs : recs = installation.recs
  installation_rvals' : rvals = installation.rvals
  /-- Every model rule fires on a constructor with the declaration's parameter count. -/
  rules_ctorParams : ∀ r ∈ recs, ∀ ru ∈ r.rules, ru.ctorParams = decl.nparams

namespace RecursorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT

/-- The declaration with the generated recursors: the declaration `addInduct` installs. -/
abbrev decl' (H : RecursorCheck R outEnv) : VInductDecl := decl.withRecs H.recs

theorem rvals_length (H : RecursorCheck R outEnv) : H.rvals.length = indTypes.size := by
  have := congrArg List.length H.rvals_names; simpa using this

theorem recs_length (H : RecursorCheck R outEnv) : H.recs.length = H.rvals.length :=
  (List.Forall₂.length_eq H.trRecs).symm

theorem addTypesCtorsProjsRecs (H : RecursorCheck R outEnv) :
    H.decl'.addTypesCtorsProjsRecs sourceEnv = some H.outVEnv := by
  rw [VInductDecl.addTypesCtorsProjsRecs]
  have h : H.decl'.addTypesCtorsProjs sourceEnv = some R.envP := R.addTypesCtorsProjs
  rw [h]; exact H.recsAdded

theorem outVEnv_wf (H : RecursorCheck R outEnv) : H.outVEnv.WF := H.checking.tr.wf

end RecursorCheck

/-- The recursor check of a recursor installation: the kernel recursors and the model recursors
of the installation (`Recursor/Recs.lean`), the checking invariant at the recursor stage
(`Recursor/Checking.lean`), the generator's signature and instance, and the installation
itself. -/
noncomputable def RecursorInstallation.toRecursorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : RecursorCheck R outEnv where
  elimLevel := H.elimLevel
  elimLevelChecked := H.elimLevelChecked
  kTarget := H.kTarget
  rvals := H.rvals
  rvals_names := by
    have hsize : H.generationSignature.families.size = indTypes.size := H.generator.familyCount
    apply List.ext_getElem
    · simp [hsize]
    · intro i h₁ h₂
      have hi : i < H.generationSignature.families.size := by simpa using h₁
      have hi' : i < indTypes.size := hsize ▸ hi
      simp only [List.getElem_map, RecursorInstallation.rvals, List.getElem_ofFn,
        Array.getElem_toList]
      have hn : (H.rvalAt ⟨i, hi⟩).name = Lean.mkRecName indTypes[i]!.name :=
        (H.generated.entry i (H.entries_lt ⟨i, hi⟩)).name
      rw [hn]
      simp [hi']
  recs := H.recs
  outVEnv := H.outVEnv
  recsAdded := by
    rw [VInductDecl.addRecs_eq_addConstVals, VInductDecl.withRecs_recs, ← H.entries_snd,
      ← R.envP_eq]
    exact H.installed.abstract
  trRecs := H.trRecs
  map_eq := H.mapEq
  quotInit_eq := H.quotInitEq
  fresh := H.freshRvals
  checking := H.checkingValid
  recsWF := H.recsWF
  rec_shape := by
    intro r hr
    obtain ⟨owner, rfl⟩ := H.recs_mem hr
    exact H.recShape owner
  rules_nodup := by
    intro r hr
    obtain ⟨owner, rfl⟩ := H.recs_mem hr
    exact H.rulesNodup owner
  rules_ctor := H.rulesCtorAll
  rule_shape := by
    intro r hr
    obtain ⟨owner, rfl⟩ := H.recs_mem hr
    exact H.ruleShape owner
  rules_closed := by
    intro r hr
    obtain ⟨owner, rfl⟩ := H.recs_mem hr
    exact H.rulesClosed owner
  kLike := H.kLike
  signature := H.generationSignature
  generation := H.generationInstance
  models := H.generator.models
  admissible := H.generator.admissible
  ihsWellTyped := by rw [← R.envP_eq]; exact H.generator.generatedIHsWellTyped
  familyTypesWF := by rw [← R.envP_eq]; exact H.generator.familyTypesWF
  recursorNames := H.generator.names
  recursors_eq := H.recs_recursors
  metadata := H.metadataAll
  closed := H.closed
  inductInfosFromDecl := H.inductInfos
  constructorParameterAlignment := fun Hsource => H.ctorParamAlignment Hsource
  installation := H
  installation_elimLevel := rfl
  installation_kTarget := rfl
  installation_outVEnv := rfl
  installation_rvals := H.entries_fst
  installation_signature := rfl
  installation_generation := HEq.rfl
  installation_recs := rfl
  installation_rvals' := rfl
  rules_ctorParams := by
    intro r hr ru hru
    obtain ⟨owner, rfl⟩ := H.recs_mem hr
    obtain ⟨index, -, rule, -, -, rfl⟩ := H.modelRule_at owner hru
    rfl

/-- The boundary theorem of the recursor phase: the recursor suffix of `runWithStats`
(elimination level, K flag, recursor infos, recursive-field check, `declareRecursors`), run in
the constructor environment, yields a recursor check. -/
theorem RecursorInput.recursorPhasesWF  -- WAVE 2 install COMPAT
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)  -- WAVE 2 install COMPAT
    (hlparams : c.lparams.Nodup)
    (hsourceSafety : isUnsafe = (c.safety != .safe))
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains (Lean.mkRecName indTypes[owner]!.name))
    (hpositivity : positivity = R.classes) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.withTypeCheckerLParams
        (AddInductive.getRecLevelParams elimLevel c.lparams) do
        let kTarget ← AddInductive.isKTarget stats indTypes
        AddInductive.mkRecInfos stats indTypes elimLevel fun recInfos => do
          AddInductive.checkRecursiveFields isUnsafe positivity recInfos
          AddInductive.declareRecursors stats indTypes elimLevel recInfos
            kTarget c.lparams)
      { c with env := ctorEnv }).WF fun outEnv =>
        Nonempty (RecursorCheck R outEnv) := by
  exact (R.recursorInstallationWF R.closed hlparams R.literalDisjoint
    (hsourceSafety := hsourceSafety) hnotPartial hnprim hpositivity).mono
      fun _ ⟨H⟩ => ⟨H.toRecursorCheck⟩

end VerifyInductive
end Lean4Lean
