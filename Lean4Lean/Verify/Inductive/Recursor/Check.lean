import Lean4Lean.Verify.Inductive.ConstructorCheck
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.Checking

/-! # The recursor phase

After the constructors, the executable computes the elimination level, the K flag and the
recursor infos (`mkRecInfos`: motives, minors, rule templates), checks the recursive fields and
declares the recursors (`declareRecursors`, which type-checks every generated recursor type and
instantiates the rule templates). `RecursorCheck` is the interface of the resulting
environment: the kernel recursors `rvals`, the model recursors `recs` they translate to
(PR #43's `TrRecursor`, with the rules' reducts translated in the recursor-stage environment),
the recursor-stage environment `outVEnv`, the shape clauses of `VInductDecl.WF`, and the
signature generator (`signature`, `generation`) whose recursors the `recs` are. The rules'
typing and their identification with the generated equations are the rule phase's
(`Rules/RuleTranslations.lean`). `ConstructorCheck.recursorPhasesWF` is the boundary theorem. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor check: the recursors are installed over the constructor environment, typed in
the projection stage, and translate to the generated recursors of a signature instance that
models the declaration. It is the recursor installation (`RecursorInstallation`: the recursor
construction and the installation of the generated recursors); the interface the rule phase and
the block certificate read is the theorems below together with `RecursorInstallation`'s own
(`rvals`, `recs`, `outVEnv`, `trRecs`, `recsWF`, `kLike`, `mapEq`, `quotInitEq`, `freshRvals`,
`checkingValid`, `metadataAll`, `inductInfos`, `ctorParamAlignment`, `recs_recursors`). -/
abbrev RecursorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (outEnv : Environment) : Type :=
  RecursorInstallation R outEnv

namespace RecursorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The signature of the generator: it models the declaration. -/
noncomputable abbrev signature (H : RecursorCheck R outEnv) : InductiveSignature := H.generationSignature

/-- The admissible instance of the generator whose recursors the model recursors are. -/
noncomputable abbrev generation (H : RecursorCheck R outEnv) : InductiveSignature.Instance H.signature :=
  H.generationInstance

/-- The declaration with the generated recursors: the declaration `addInduct` installs. -/
noncomputable abbrev decl' (H : RecursorCheck R outEnv) : VInductDecl := decl.withRecs H.recs

/-- The kernel recursors are named after their families, in family order. -/
theorem rvals_names (H : RecursorCheck R outEnv) :
    H.rvals.map (·.name) = indTypes.toList.map (Lean.mkRecName ·.name) := by
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

theorem rvals_length (H : RecursorCheck R outEnv) : H.rvals.length = indTypes.size := by
  have := congrArg List.length H.rvals_names; simpa using this

theorem recs_length (H : RecursorCheck R outEnv) : H.recs.length = H.rvals.length :=
  (List.Forall₂.length_eq H.trRecs).symm

/-- The recursor-stage environment is the projection stage with the recursors added. -/
theorem recsAdded (H : RecursorCheck R outEnv) :
    (decl.withRecs H.recs).addRecs R.envP = some H.outVEnv := by
  rw [VInductDecl.addRecs_eq_addConstVals, VInductDecl.withRecs_recs, ← H.entries_snd,
    ← R.envP_eq]
  exact H.installed.abstract

/-- `VInductDecl.WF.rec_shape`. -/
theorem rec_shape (H : RecursorCheck R outEnv) :
    ∀ r ∈ H.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.recs_mem hr
  exact H.recShape owner

/-- `VInductDecl.WF.rules_nodup`. -/
theorem rules_nodup (H : RecursorCheck R outEnv) :
    ∀ r ∈ H.recs, (r.rules.map (·.ctor)).Nodup := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.recs_mem hr
  exact H.rulesNodup owner

/-- `VInductDecl.WF.rule_shape`. -/
theorem rule_shape (H : RecursorCheck R outEnv) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
      r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
      ru.nfields ≤ A.piArity ∧
      ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields
        (A.piArity - ru.nfields) j := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.recs_mem hr
  exact H.ruleShape owner

/-- Every reduct is closed, so `addRules` (hence `addInduct`) succeeds. -/
theorem rules_closed (H : RecursorCheck R outEnv) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ru.rhs.Closed := by
  intro r hr
  obtain ⟨owner, rfl⟩ := H.recs_mem hr
  exact H.rulesClosed owner

/-- Every model rule fires on a constructor with the declaration's parameter count. -/
theorem rules_ctorParams (H : RecursorCheck R outEnv) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ru.ctorParams = decl.nparams := by
  intro r hr ru hru
  obtain ⟨owner, rfl⟩ := H.recs_mem hr
  obtain ⟨index, -, rule, -, -, rfl⟩ := H.modelRule_at owner hru
  rfl

/-! The generator's clauses (`InductiveSignature.Compiles`): the signature models the
declaration, and the instance is admissible with its induction hypotheses and family types typed
in the projection stage. -/

theorem models (H : RecursorCheck R outEnv) : H.signature.Models sourceEnv decl :=
  H.generator.models

theorem admissible (H : RecursorCheck R outEnv) : H.generation.Admissible R.headerVEnv :=
  H.generator.admissible

theorem ihsWellTyped (H : RecursorCheck R outEnv) :
    H.generation.GeneratedIHsWellTyped R.envP := by
  rw [← R.envP_eq]; exact H.generator.generatedIHsWellTyped

theorem familyTypesWF (H : RecursorCheck R outEnv) :
    H.signature.FamilyTypesWF R.envP decl.uvars := by
  rw [← R.envP_eq]; exact H.generator.familyTypesWF

theorem recursorNames (H : RecursorCheck R outEnv) :
    ∀ owner, H.generation.recursorName owner = H.signature.families[owner].name.str "rec" :=
  H.generator.names

theorem addTypesCtorsProjsRecs (H : RecursorCheck R outEnv) :
    H.decl'.addTypesCtorsProjsRecs sourceEnv = some H.outVEnv := by
  rw [VInductDecl.addTypesCtorsProjsRecs]
  have h : H.decl'.addTypesCtorsProjs sourceEnv = some R.envP := R.addTypesCtorsProjs
  rw [h]; exact H.recsAdded

theorem outVEnv_wf (H : RecursorCheck R outEnv) : H.outVEnv.WF := H.checkingValid.tr.wf

end RecursorCheck

/-- The boundary theorem of the recursor phase: the recursor suffix of `runWithStats`
(elimination level, K flag, recursor infos, recursive-field check, `declareRecursors`), run in
the constructor environment, yields a recursor check. -/
theorem ConstructorCheck.recursorPhasesWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
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
      fun _ ⟨H⟩ => ⟨H⟩

end VerifyInductive
end Lean4Lean
