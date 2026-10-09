import Lean4Lean.Verify.Inductive.Recursor.Construction
import Lean4Lean.Verify.Inductive.Recursor.Signature.Generator
import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening
import Lean4Lean.Verify.Inductive.TypeAnnotations
import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation
import Lean4Lean.Verify.Inductive.Recursor.Elimination.Singleton
import Lean4Lean.Verify.Inductive.Constructor.ParameterSyntacticTranslation
import Lean4Lean.Theory.Inductive.SignatureLemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor check: the recursor construction together with the installation of the
generated recursors (`declareRecursors`), indexed only by the constructor check. In particular
it does not require a well-formed header-only environment or an ordinary `AddConstants`
derivation for primitive family and constructor names. -/
structure RecursorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (outEnv : Environment) extends RecursorConstruction R where
  outVEnv : VEnv
  entries : List (ConstantInfo × VConstVal)
  generated : GeneratedRecursors localContext.safety
    R.context.venv
    localContext.lparams elimLevel localContext stats indTypes recInfos entries
  ruleTyping : TypedRecursorRulesRange
    recursorWF decl stats indTypes recInfos origins elimLevel
      parameterSuffix.parameterDecls 0 entries
  installed : AddConstants localContext.safety localContext.env
    R.context.venv
    entries outEnv outVEnv
  closed : MutualInductivesClosed outEnv
  targets : ∀ i (hi : i < entries.length),
    entries[i].2 = toRecursorConstruction.recursorTarget i

/-- The installed recursor values are exactly the generator's recursors, in order. Equality
holds because the targets are chosen before the loop, not by uniqueness of translations. -/
theorem RecursorCheck.recursors
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    H.entries.map Prod.snd = H.toRecursorConstruction.generationInstance.recursors := by
  have hsize : H.entries.length = H.toRecursorConstruction.generationSignature.families.size := by
    rw [H.generated.length, H.cardinality.records]
    change decl.types.length = H.toRecursorConstruction.generator.signature.families.size
    rw [H.toRecursorConstruction.generator.familyCount]
    exact (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
  apply List.ext_getElem
  · simp [InductiveSignature.Instance.recursors, hsize]
  · intro i hi hi'
    have hiEntry : i < H.entries.length := by simpa using hi
    have hiFamily : i < H.toRecursorConstruction.generationSignature.families.size := by
      simpa [InductiveSignature.Instance.recursors] using hi'
    simp only [List.getElem_map]
    rw [H.targets i hiEntry]
    simp [RecursorConstruction.recursorTarget, hiFamily,
      InductiveSignature.Instance.recursors]

/-- Every emitted recursor carries the single bit selected by the executable
K check before the recursor loop. -/
theorem RecursorCheck.generated_k
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.k = H.kTarget :=
  (H.generated.entry owner howner).kChecked.unique H.kTargetChecked
    H.localContext

/-- The installed recursor rules are literally the instantiations of the rule templates
recorded by `mkRecInfos`, as `declareRecursors.loop` builds them through
`mkRecRulesFromTemplates` in the local context of the recursor construction. -/
theorem RecursorCheck.generated_rules_eq
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.rules =
      H.recInfos[owner]!.ruleTemplates.toList.map fun blueprint =>
        blueprint.instantiate indTypes stats (H.recInfos.map (·.motive))
          (H.recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels H.elimLevel stats.levels)
          H.localContext.lctx :=
  (H.generated.entry owner howner).rules_eq

/-- Each installed recursor has exactly one rule per rule template. -/
theorem RecursorCheck.generated_rules_length
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.rules.length =
      H.recInfos[owner]!.ruleTemplates.size := by
  rw [H.generated_rules_eq owner howner]
  simp

/-- Rule-wise form of `generated_rules_eq`. -/
theorem RecursorCheck.rulesLiteral
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hi : i < (H.generated.entry owner howner).info.rules.length) :
    (H.generated.entry owner howner).info.rules[i] =
      (H.recInfos[owner]!.ruleTemplates[i]!).instantiate indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        H.localContext.lctx := by
  have hsize := H.generated_rules_length owner howner
  have hi' : i < H.recInfos[owner]!.ruleTemplates.size := hsize ▸ hi
  simp only [H.generated_rules_eq owner howner, List.getElem_map,
    Array.getElem_toList, getElem!_pos H.recInfos[owner]!.ruleTemplates i hi']

/-- The recursor safety metadata agrees with the source declaration because
both flags come from the same declaration checking context. -/
theorem RecursorCheck.generated_isUnsafe
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.isUnsafe = decl.isUnsafe := by
  rw [(H.generated.entry owner howner).isUnsafe, H.localExtends.safety_eq,
    ← H.sourceSafety, R.core.isUnsafe]

/-- Installing the constructors and recursors preserves the constructor-owner invariant
through the whole inductive block. Constructor entries get their owners from the checked
formation, while generated recursor entries are definitionally `recInfo` and therefore add
no constructor metadata. -/
theorem RecursorCheck.constructorOwnersPresent
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (hsource : ConstructorOwnersPresent c.env) :
    ConstructorOwnersPresent outEnv := by
  have hctor : ConstructorOwnersPresent H.localContext.env := by
    rw [H.localExtends.env_eq]
    exact R.constructorOwnersPresent hsource
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  apply (AtomicAddConstants.ofAddConstants H.installed).constructorOwnersPresent
    hwf hctor
  intro entry hentry info hinfo
  have hne := H.generated.nonConstructor entry.1 entry.2 (by simpa using hentry) info
  exact False.elim (hne hinfo)

/-- The recursor phase adds no constructor: every constructor of the output is a base
constant, or a new constructor of the declaration with its safety flag and a constructor
telescope certificate (`CtorTelescopeAt`) in the header environment. -/
theorem RecursorCheck.ctorOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (hfind : outEnv.find? name = some (.ctorInfo ci)) :
    c.env.find? name = some (.ctorInfo ci) ∨
      (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt R.headerVEnv ci) := by
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  have h := (AtomicAddConstants.ofAddConstants H.installed).ctors_of_noCtor hwf
    (fun e he info => H.generated.nonConstructor e.1 e.2 (by simpa using he) info) hfind
  rw [H.localExtends.env_eq] at h
  exact R.ctorOrigin h

/-- The recursor phase (`getElimLevel`, `mkRecInfos`, `declareRecursors`) run after a
constructor check succeeds and yields a `RecursorCheck`. This is shared by ordinary and
atomic primitive formation. -/
theorem ConstructorCheck.recursorPhasesWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hclosed : MutualInductivesClosed ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.context.venv stats.indConsts)
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true ->
      forall owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name))
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
  apply R.getElimLevelMkRecInfosWF hlparams
    Lean4Lean.recursorConsumeTypeAnnotationsCompat hlit
    (Q := fun outEnv => Nonempty (RecursorCheck R outEnv))
    (k := fun elimLevel kTarget recInfos => do
      AddInductive.checkRecursiveFields isUnsafe positivity recInfos
      AddInductive.declareRecursors stats indTypes elimLevel recInfos kTarget
        c.lparams)
  intro elimLevel hElim hElimRun kTarget hkTarget localContext localDepth recInfos Rlocal henvLocal
    HsuffixLocal hparameterDeclsLocal HstatsLocal hctxLocal Hbindings
    Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics HmajorTypes HmajorShapes
    HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams hnoalias
    houterOrder Harities HminorCounts Hcard Hle
  refine (AddInductive.checkRecursiveFields.WF (c := localContext)).bind
    fun _ hchecked => ?_
  rw [hpositivity] at hchecked
  have Hvalid : CheckingEnv.Valid localContext.safety localContext.env
      R.context.venv := by
    rw [Hle.safety_eq, Hle.env_eq]
    exact R.context.checking
  have Hcore : TrInductDeclCore sourceEnv localContext.lparams nparams
      indTypes.toList isUnsafe decl R.headerVEnv R.ctorVEnv := by
    rw [Hle.lparams_eq]
    exact R.core
  have Hseed : forall owner (howner : owner < indTypes.size),
      forall ctor, ctor ∈ indTypes[owner]!.ctors ->
        exists tail tailTarget introTarget,
          ParameterPrefix stats 0 ctor.type tail ∧
          Nonempty
            (ConstructorOwnerNormalForm stats owner tail) ∧
          tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
          TrExprS Rlocal.venv
            (AddInductive.getRecLevelParams elimLevel c.lparams)
            Rlocal.mlctx.vlctx tail tailTarget ∧
          Rlocal.venv.IsType
            (AddInductive.getRecLevelParams elimLevel c.lparams).length
            Rlocal.mlctx.vlctx.toCtx tailTarget ∧
          TrExprS Rlocal.venv
            (AddInductive.getRecLevelParams elimLevel c.lparams)
            Rlocal.mlctx.vlctx
            (mkAppN (.const ctor.name stats.levels) stats.params)
            introTarget ∧
          Rlocal.venv.HasType
            (AddInductive.getRecLevelParams elimLevel c.lparams).length
            Rlocal.mlctx.vlctx.toCtx introTarget tailTarget := by
    intro owner howner ctor hctor
    have hownerBang : indTypes[owner]! = indTypes[owner] := by
      simp [howner]
    rw [hownerBang] at hctor
    rcases List.mem_iff_getElem.mp hctor with ⟨ctorIdx, hctorIdx, rfl⟩
    rcases R.checkedConstructorPrefixInRecursorContextAt elimLevel hElim hlparams Rlocal
        henvLocal HsuffixLocal hparameterDeclsLocal owner howner ctorIdx
        hctorIdx with
      ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars, Htail,
        HtailType, Hintro, HintroType, _⟩
    exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
      Htail, HtailType, Hintro, HintroType⟩
  let construction (T : TrRecursorTypes R.context.venv localContext.lparams
      elimLevel localContext stats indTypes recInfos) :
      RecursorConstruction R := {
    sourceSafety := hsourceSafety
    recursorTypes := T
    elimLevel := elimLevel
    elimLevelAdmissible := hElim
    elimLevelChecked := hElimRun
    lparamsNodup := hlparams
    kTarget := kTarget
    kTargetChecked := hkTarget
    recInfos := recInfos
    localContext := localContext
    localWF := Rlocal.toBindingContextWF
    localExtends := Hle
    recursorDepth := localDepth
    recursorWF := Rlocal
    recursorEnv := henvLocal
    parameterSuffix := HsuffixLocal
    parameterDecls := hparameterDeclsLocal
    validStats := HstatsLocal
    noIndConsts := hctxLocal
    bindings := Hbindings
    origins := Horigins
    templates := Hblueprints
    templateTyping := HblueprintSemantics
    minorSources := HminorSources
    minorTyping := HminorSemantics
    majorTypes := HmajorTypes
    majorShapes := HmajorShapes
    motiveTypes := HmotiveTypes
    motiveShapes := HmotiveShapes
    motiveTelescopes := Htelescopes
    indexRows := HindexRows
    params := Hparams
    noAlias := hnoalias
    outerOrder := houterOrder
    arities := Harities
    minorCounts := HminorCounts
    cardinality := Hcard
    recursiveFieldsChecked := hchecked
  }
  have Hrecursors := AddInductive.declareRecursors.bindingWFOfTargets
    (elimLevel := elimLevel) kTarget hkTarget Hvalid Rlocal
    HstatsLocal Lean4Lean.recursorConsumeTypeAnnotationsCompat
    (by simpa only [henvLocal] using hlit) hctxLocal Hcard Hcore Hbindings
    Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics
    Hparams hnoalias HminorCounts HsuffixLocal.parameterFVarsUp Hseed
    (fun T owner => ((construction T).recursorTarget owner).type) (by
      intro T owner howner
      simpa only [Hle.lparams_eq] using (construction T).typeTranslations owner howner) (by
      rw [Hle.safety_eq]
      exact hnotPartial) (henvLocal ▸ Rlocal.cacheSound) (by
        intro hallow
        exact hnprim (Hle.allowPrimitive_eq ▸ hallow))
  have hclosedLocal : MutualInductivesClosed localContext.env := by
    rw [Hle.env_eq]
    exact hclosed
  have Hrecursors' :
      (AddInductive.declareRecursors stats indTypes elimLevel recInfos
        kTarget c.lparams localContext).WF fun outEnv =>
          ∃ outVEnv : VEnv,
          ∃ entries : List (ConstantInfo × VConstVal),
            Nonempty (GeneratedRecursors localContext.safety
              R.context.venv
              localContext.lparams elimLevel localContext stats indTypes
              recInfos entries) ∧
            Nonempty (TypedRecursorRulesRange Rlocal decl stats
              indTypes recInfos Horigins elimLevel
                HsuffixLocal.parameterDecls 0 entries) ∧
            AddConstants localContext.safety localContext.env
              R.context.venv
              entries outEnv outVEnv ∧
            ∃ T : TrRecursorTypes R.context.venv localContext.lparams
              elimLevel localContext stats indTypes recInfos,
            ∀ i (hi : i < entries.length), entries[i].2 = {
              name := Lean.mkRecName indTypes[i]!.name
              uvars := (AddInductive.getRecLevelParams elimLevel c.lparams).length
              type := ((construction T).recursorTarget i).type } := by
    simpa only [Hle.lparams_eq] using Hrecursors
  exact Hrecursors'.mono fun outEnv Hout => by
    rcases Hout with
      ⟨outVEnv, entries, ⟨Hgenerated⟩, ⟨HruleSemantics⟩, Hinstalled, T, Htargets⟩
    exact ⟨{
      toRecursorConstruction := construction T
      outVEnv := outVEnv
      entries := entries
      generated := Hgenerated
      ruleTyping := HruleSemantics
      installed := Hinstalled
      closed := Hgenerated.closesMutuals Hinstalled Hvalid.tr.map_wf
        hclosedLocal
      targets := by
        intro i hi
        have hbound : i < indTypes.size := by
          have hc := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hcore
          rw [Hgenerated.length, Hcard.records] at hi
          simp only [Array.length_toList] at hc
          omega
        rw [Htargets i hi]
        exact ((construction T).recursorTarget_eq i hbound).symm }⟩

/-- The executable's universe-parameter check succeeds only for a duplicate-free
parameter list. -/
theorem Kernel.Environment.checkDuplicatedUnivParams.WF
    (lparams : List Name) :
    (Kernel.Environment.checkDuplicatedUnivParams lparams).WF
      (fun _ => lparams.Nodup) := by
  induction lparams with
  | nil =>
    intro out hout
    cases hout
    trivial
  | cons param lparams ih =>
    by_cases hmem : param ∈ lparams
    · rw [Kernel.Environment.checkDuplicatedUnivParams]
      simp only [hmem, if_pos]
      exact Except.WF.throw
    · simpa [Kernel.Environment.checkDuplicatedUnivParams, hmem] using
        ih.mono fun _ htail => List.nodup_cons.mpr ⟨hmem, htail⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The construction's signature instance (`generationInstance`) of a recursor check. The
generated recursors and the executable metadata are both compared with this one instance. -/
noncomputable def RecursorCheck.canonicalGeneration
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    InductiveSignature.Instance H.toRecursorConstruction.generationSignature :=
  H.toRecursorConstruction.generationInstance

/-- The construction's instance is admissible in the header environment, with the elimination
level and singleton decision the executable computed. -/
theorem RecursorCheck.canonicalGeneration_admissible
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    H.canonicalGeneration.Admissible R.headerVEnv :=
  H.toRecursorConstruction.generator.admissible

end VerifyInductive
end Lean4Lean
