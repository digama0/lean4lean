import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRuleAvoidance
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestoredShapes
import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.RuleConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestoredRecursorShapes
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.RestoredWF
import Lean4Lean.Verify.Inductive.Nested.Equations.RuleAlignment

/-! # The recursor and compilation half of the restored block

The fields of `RestoredBlock` (`Nested/Restoration/Certificate.lean`) about recursors and
compilation, produced from a nested run `E`, a rule-free restored block base `B` of it, and the
restoration tables of `restorationTablesRestoringAll`.

* **Rule translation** (`NestedRun.trRestoredRecursorRule_of_equation`): in the recursor stage
  of `B`, where the stripped output environment is a checker environment (`CheckerEnv`, the
  input of `validateRestoredRecursorRules.check.WF`), the right-hand side of every executable
  restored rule translates, and its translation is the restoration of the generated right-hand
  side. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The right-hand side of a restored recursor rule translates in any model in which the
stripped output environment is a checker environment (the rule validation pass). -/
theorem NestedRun.restoredRuleRhs_translation'
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    {venv : VEnv}
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) venv)
    {recName : Name}
    (hrecName : recName ∈ sourceTypes.map (fun t => Lean.mkRecName t.name) ++
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) recName s t)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length) :
    ∃ target, TrExprS venv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs target := by
  have hcheck := validateRestoredRecursorRules.run.WF Cstrip _ _ _ _ _ _ _
    E.recursorRuleValidation recName hrecName
  obtain ⟨recInfo, hfind, hrules⟩ := validateRestoredRecursorRules.check.WF Cstrip _ _ _ _ _ _
    hcheck
  have hold : recInfo = Hstep.oldInfo := by
    have h := hfind.symm.trans Hstep.lookup
    injection h with h
    injection h
  subst hold
  have hnew : restoredRecursorOf result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 (sourceTypes.map (·.name))
      recName Hstep.oldInfo = Hstep.restored.newInfo := Hstep.restored.produced.symm
  rw [hnew] at hrules
  obtain ⟨rhs, -, Ht, -⟩ := hrules _ (List.getElem_mem hj)
  exact ⟨rhs, Ht⟩

theorem _root_.Lean4Lean.InductiveSignature.Restoration.equation_eq_some'
    {r : Restoration} {eq rule : VDefEq} (h : r.equation eq = some rule) :
    rule.uvars = eq.uvars ∧ r.expr eq.lhs = some rule.lhs ∧
      r.expr eq.rhs = some rule.rhs ∧ r.expr eq.type = some rule.type := by
  simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at h
  cases hl : r.expr eq.lhs with
  | none => simp [hl] at h
  | some lhs =>
    cases hr : r.expr eq.rhs with
    | none => simp [hl, hr] at h
    | some rhs =>
      cases ht : r.expr eq.type with
      | none => simp [hl, hr, ht] at h
      | some ty =>
        simp only [hl, hr, ht, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Translation of a restored generated equation**, over the stripped checker environment
`Cstrip`. In the recursor environment of a restored
block base, the abstract restoration of the `k`-th generated equation is a translation of the
executable restored rule at `k`. -/
theorem NestedRun.trRestoredRecursorRule_of_equation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.loweredDecl = E.lowered.loweredDecl)
    (hkernel : List.Perm
      ((C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map Prod.fst)
      E.restoration.entries)
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.recursorVEnv)
    {X : List Name}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → C.recursorVEnv.constants n = none)
    (HL : E.LoweredRulesAvoid E.auxHeads X)
    (k : Fin E.lowered.recursors.generationSignature.constructors.size)
    {rule : VDefEq}
    (hrule : (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule) :
    E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
      C.recursorVEnv k rule := by
  let P := E.lowered.recursors
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped hwf hkernel
  let owner := P.generationSignature.constructors[k].owner
  obtain ⟨entry, -, s, t, Hstep, -, -, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hinfos owner (List.mem_finRange owner)
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hmap := P.ownedConstructors_map_val owner hi
  have hmem : k ∈ P.generationSignature.ownedConstructors owner := by
    simp [InductiveSignature.ownedConstructors, owner]
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  rw [hjk] at hval
  have hlenOwned : (P.generationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, hinfo]
  have hjNew : j < Hstep.restored.newInfo.rules.length := by
    rw [Hstep.restored.restoration.rules.length, ← hlenOwned]
    exact hj
  have hnames := E.recursorNames_order C.sourceNonempty
  have hn : P.canonicalGeneration.recursorName owner ∈
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_finRange owner)
  obtain ⟨target, Ht⟩ := E.restoredRuleRhs_translation' Cstrip hn Hstep j hjNew
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hrhs := E.restoredRuleRhs_of_trail wf Hsources hheads hparamsSize D hscoped Hfresh
    owner Hstep (fun rule hrule => by
      rw [hheads]; exact HL owner Hstep.oldInfo Hstep.lookup rule hrule) j hjNew k hval Ht
  obtain ⟨huvars, hlhs, hrhs', htype⟩ := Restoration.equation_eq_some' hrule
  have htarget : target = rule.rhs := Option.some.inj (hrhs.symm.trans hrhs')
  subst htarget
  exact ⟨owner, j, s, t, Hstep, hjNew, hval, huvars, Ht, hlhs, htype⟩

/-! ### The kernel recursors of the run in fold order -/

section Folds

variable {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
  {auxRec : NameMap Name} {allIndNames : List Name}

/-- The source recursors of the family fold are the restoration steps at the source families'
recursor names. -/
theorem FoldSteps.inductiveRecs_steps :
    ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        (types.map (fun t => Lean.mkRecName t.name)) H.inductiveRecs
  | _, _, _, .nil => .nil
  | _, _, _, .cons h t => .cons ⟨_, _, h.restored.recursor, rfl⟩ (FoldSteps.inductiveRecs_steps t)

/-- The auxiliary recursors of the recursor fold are the restoration steps at their names. -/
theorem FoldSteps.recursorInfos_steps :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        names H.recursorInfos
  | _, _, _, .nil => .nil
  | _, _, _, .cons h t => .cons ⟨_, _, h, rfl⟩ (FoldSteps.recursorInfos_steps t)

/-- The restored recursors of a run are the restoration steps at the recursor names, in order. -/
theorem NestedRestorationFolds.rvals_steps {sourceEnv : Environment}
    {types : List InductiveType} {auxRecNames : List Name} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) :
    List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
        (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
        Hs.restored.newInfo = rv)
      (types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames) H.rvals :=
  Lean4Lean.List.Forall₂.append (FoldSteps.inductiveRecs_steps H.inductives)
    (FoldSteps.recursorInfos_steps H.auxiliaries)

/-- The translation of a restored source recursor, in the form of a `recInfo`. -/
theorem SourceRecursorTranslation.trConstVal {decl : VInductDecl} {owner : VInductiveType}
    {safety : DefinitionSafety} {oldRecName : Name} {s t : Environment} {venv : VEnv}
    {Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s t}
    (H : SourceRecursorTranslation decl owner safety Hs venv) :
    TrConstVal safety venv (.recInfo Hs.restored.newInfo) H.recursor := by
  have R := Hs.restored.restoration
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have h := H.safety_le
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, R.isUnsafe]
      using h
  · show Hs.restored.newInfo.levelParams.length = _
    rw [R.levelParams]; exact H.uvars
  · show TrExprS venv Hs.restored.newInfo.levelParams [] Hs.restored.newInfo.type _
    rw [R.levelParams]; exact H.type
  · show Hs.restored.newInfo.name = _
    rw [R.name, H.name]

theorem SourceFamilyTranslations.rvalsTranslated {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv} :
    ∀ {types : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
      {Htrace : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv} {owners : List VInductiveType}
      {recursors : List VConstVal},
      SourceFamilyTranslations decl lparams safety sourceVEnv envTypes envCtors Htrace owners
        recursors →
      List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
          TrConstVal safety envCtors (.recInfo rv) v ∧ v.toVConstant.WF envCtors)
        Htrace.inductiveRecs recursors := by
  intro types sourceProdEnv targetProdEnv Htrace owners recursors H
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons ⟨Hrecursor.trConstVal, Hrecursor.wf⟩ ih

theorem AuxiliaryRecursorTranslations.rvalsTranslated {safety : DefinitionSafety}
    {trEnv recursorEnv : VEnv} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      {Htrace : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv} {prior final : List VConstVal},
      AuxiliaryRecursorTranslations safety trEnv recursorEnv Htrace prior final →
      ∃ added, final = prior ++ added ∧
        List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
          TrConstVal safety trEnv (.recInfo rv) v ∧ v.toVConstant.WF recursorEnv)
        Htrace.recursorInfos added := by
  intro names sourceEnv targetEnv Htrace prior final H
  induction H with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons Hstep Htail Hhead Hrest ih =>
    obtain ⟨added, hfinal, hadded⟩ := ih
    exact ⟨Hhead.recursor :: added, by rw [hfinal]; simp,
      .cons ⟨Hhead.translated, Hhead.wf⟩ hadded⟩

end Folds

/-- The restored kernel recursors of the run against the base's abstract recursors, in fold
order: translated, and well formed, in the projection stage of the base. -/
theorem RestoredBlockBase.rvalsTranslated
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (B : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :
    List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
        TrConstVal safety (B.install.venvCtors.addProjections decl.projectionEntries)
          (.recInfo rv) v ∧
        v.toVConstant.WF (B.install.venvCtors.addProjections decl.projectionEntries))
      H.rvals (B.sourceRecursors ++ B.auxiliaryRecursors) := by
  obtain ⟨added, hfinal, hadded⟩ := B.auxiliaryRecursorTrace.rvalsTranslated
  simp only [List.nil_append] at hfinal
  rw [hfinal]
  exact Lean4Lean.List.Forall₂.append B.sourceTranslations.rvalsTranslated hadded

theorem forall₂_through_map {α β γ δ : Type _} {f : α → β} {R : α → γ → Prop}
    {S : β → δ → Prop} {T : δ → γ → Prop} (h : ∀ a c d, R a c → S (f a) d → T d c) :
    ∀ {l : List α} {lc : List γ} {ld : List δ},
      List.Forall₂ R l lc → List.Forall₂ S (l.map f) ld → List.Forall₂ T ld lc
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (forall₂_through_map h t1 t2)

/-- **The kernel recursors of the run are those of the base's recursor entries, in order**:
both are the restoration steps at the generated recursor names. -/
theorem NestedRun.rvals_recursorEntries
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    (hnonempty : sourceTypes ≠ [])
    {entries : List (ConstantInfo × VConstVal)}
    (hinfos : List.Forall₂ (fun owner (entry : ConstantInfo × VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.lowered.recursors.canonicalGeneration.recursorName owner) s t),
          entry.1 = .recInfo Hstep.restored.newInfo)
      (List.finRange E.lowered.recursors.generationSignature.families.size) entries) :
    List.Forall₂ (fun (rv : RecursorVal) (entry : ConstantInfo × VConstVal) =>
      entry.1 = .recInfo rv) E.restoration.rvals entries := by
  have hsteps := E.restoration.rvals_steps
  rw [← E.recursorNames_order hnonempty] at hsteps
  refine forall₂_through_map ?_ hinfos hsteps
  rintro owner entry rv ⟨s, t, Hs, he⟩ ⟨s', t', Hs', rfl⟩
  rw [he, (Hs.info_eq Hs').2]

/-- **The restored compilation of a nested run**, over a rule-free base `C` and the stripped
checker environment: for the
specializations of `restorationTablesRestoringAll`, the restored generated equations `rules`
exist, the containers are installed, the restored block with these rules is a
`CompilationData` of the lowered run's generator, and every recursor entry of `C` translates the
restoration of the generated recursor of its owner (`TrRestoredRecursorEntry`, in the recursor
stage of `C`). -/
theorem NestedRun.restoredCompilation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.loweredDecl = E.lowered.loweredDecl)
    (hkernel : List.Perm
      ((C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map Prod.fst)
      E.restoration.entries)
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.recursorVEnv) :
    ∃ (auxiliaries : List ContainerSpecialization) (rules : List VDefEq),
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams ∧
      E.lowered.generatedInstance.restoredEquations
        (compilationRestoration sourceDecl auxiliaries) = some rules ∧
      ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries ∧
      CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
        sourceDecl E.lowered.loweredDecl E.lowered.signature
        E.lowered.generatedInstance auxiliaries
        (restoredBlock sourceDecl C.sourceRecursors C.auxiliaryRecursors rules []) ∧
      List.Forall₂
        (TrRestoredRecursorEntry E.lowered.generatedInstance
          (compilationRestoration sourceDecl auxiliaries)
          (sourceDecl.types.map (·.name)) C.recursorVEnv)
        (List.finRange E.lowered.signature.families.size)
        C.recursorEntries ∧
      List.Forall₂ (fun (rv : RecursorVal) (entry : ConstantInfo × VConstVal) =>
        entry.1 = .recInfo rv) E.restoration.rvals C.recursorEntries ∧
      ∃ (envTypes : VEnv) (generated : List VInductiveType),
        List.Forall₂ (SpecializationGenerates
          (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
          E.lowered.headers.commonParameterContext sourceDecl) auxiliaries generated ∧
        List.Forall₂ (VInductDecl.NestedTypeExpansion
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
            (VInductDecl.NestedOccurrenceReplacementAbs
              (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
          generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
        ∀ a ∈ auxiliaries, ∃ info,
          sourceProdEnv.find? a.source.name = some (.inductInfo info) ∧
            info.ctors = a.source.ctors.map (·.name) := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring, Hkernel⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hfreshFinal := E.recursorVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC
    hkernel D
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D
  have hfreshF : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ ((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames) →
      C.recursorVEnv.constants n = none := by
    intro n hn hnot
    exact hfreshFinal n hn (fun hm => hnot (List.mem_filter.mpr ⟨hm, by simpa using hn⟩))
  -- the restored generated equations
  have hrecs := E.restoredRecursorList_of_paramUniform C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.generatedInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.lowered.generatedInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have Hrules : List.Forall₂ (fun k rule => (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule)
      (List.finRange E.lowered.recursors.generationSignature.constructors.size)
      rules := by
    have h := List.mapM_eq_some.mp hrulesEq
    simp only [InductiveSignature.Instance.equations] at h
    exact (Lean4Lean.List.forall₂_map_left_iff).mp h
  have HCrules : List.Forall₂
      (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
        C.recursorVEnv)
      (List.finRange E.lowered.recursors.generationSignature.constructors.size) rules :=
    Lean4Lean.List.Forall₂.imp (fun k _ hk =>
      E.trRestoredRecursorRule_of_equation wf Hsources hadded Haux Hexpansion hnodup
        hparamsSize D hscoped C hC hkernel Cstrip hfreshF HL k hk) Hrules
  have hequations : E.lowered.generatedInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some (rules ++ []) := by
    rw [List.append_nil]; exact hrulesEq
  obtain ⟨Hcertified, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC rules []
    hadded henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have htypesEq : C.install.venvTypes = envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.install.venvCtors := by
    have h := C.install.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.install.recursorsAdded.abstract
  have hle : C.install.venvCtors.addProjections sourceDecl.projectionEntries ≤
      C.recursorVEnv := VEnv.addConstVals_le hrecAdded
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at Hcore
    exact (forall₂_trInductiveType_names Hcore.types).symm
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf hkernel
  have HCrules' : List.Forall₂
      (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
        C.recursorVEnv)
      (List.finRange E.lowered.signature.constructors.size) rules := HCrules
  refine ⟨auxiliaries, rules, D, hrulesEq, Hcertified, Hdata, ?_,
    E.rvals_recursorEntries C.sourceNonempty (Lean4Lean.List.Forall₂.imp
      (fun _ _ ⟨s, t, Hs, h1, _⟩ => ⟨s, t, Hs, h1⟩) hinfos),
    envTypes, generated, Haux, Hexpansion, Hkernel⟩
  refine forall₂_imp_mem_right hinfos ?_
  rintro owner entry hentry ⟨s, t, Hstep, hentry1, hrec, Hw⟩
  refine ⟨Hstep.restored.newInfo, hentry1, hrec, ?_⟩
  obtain ⟨head, hhead, hheadName, hlevels, hargs, happ, Hctor⟩ :=
    Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
  have hinstalled : C.recursorVEnv.constants Hstep.restored.newInfo.name ≠ none := by
    have hget := VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)
    have hname : entry.2.name = Hstep.restored.newInfo.name :=
      Hw.1.trans Hstep.restored.restoration.name.symm
    rw [← hname, hget]
    simp
  have Hrules' := E.trRestoredRules D hctorNames Hdata.recursorNames
    Hdata.heads_not_recursors hfreshF
    (fun a ha hm => E.auxRecName_not_renamed wf Hsources D a ha (List.mem_filter.mp hm).1)
    (by rw [List.append_nil] at hequations; exact hequations) HCrules' owner Hstep hinstalled
    head Hctor
  refine E.trRestoredRecursorVal_of_step D hnames owner Hstep hle hrec Hw
    ⟨head, hhead, ?_, hlevels, hargs, happ, Hrules'⟩
  rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
    owner Hstep, hheadName]


/-! ### Choosing the model recursors -/

theorem forall₂_choose {α β γ : Type _} {S : α → β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a b => ∃ c, S a b c) l₁ l₂ →
      ∃ l₃ : List γ, List.Forall₂ (fun (ab : α × β) c => S ab.1 ab.2 c) (l₁.zip l₂) l₃
  | _, _, .nil => ⟨[], .nil⟩
  | _, _, .cons ⟨c, hc⟩ t =>
    let ⟨l₃, h⟩ := forall₂_choose t
    ⟨c :: l₃, .cons hc h⟩

theorem forall₂_zip_left {α β γ : Type _} {P : α → β → Prop} {Q : γ → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ P l₁ l₂ → List.Forall₂ Q l₃ l₂ →
      List.Forall₂ (fun c (ab : α × β) => P ab.1 ab.2 ∧ Q c ab.2) l₃ (l₁.zip l₂)
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨h1, h2⟩ (forall₂_zip_left t1 t2)

theorem forall₂_and {α β : Type _} {P Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → List.Forall₂ Q l₁ l₂ →
      List.Forall₂ (fun a b => P a b ∧ Q a b) l₁ l₂
  | _, _, .nil, .nil => .nil
  | _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨h1, h2⟩ (forall₂_and t1 t2)

theorem forall₂_zip_fst {α β : Type _} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → (l₁.zip l₂).map Prod.fst = l₁
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [forall₂_zip_fst t]

theorem forall₂_zip_snd {α β : Type _} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → (l₁.zip l₂).map Prod.snd = l₂
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [forall₂_zip_snd t]

/-- The model rule read off one restored kernel rule: the kernel rule's constructor and field
count, the restored family head's parameter count, the restored generated reduct. -/
def RestoredRuleSpec {s : InductiveSignature} (g : Instance s) (r : Restoration)
    (venv : VEnv) (lparams : List Name) (head : RestoredFamilyHead)
    (index : Fin s.constructors.size) (rule : Lean.RecursorRule) (ru : VRecRule) : Prop :=
  ru.ctor = rule.ctor ∧ ru.nfields = rule.nfields ∧ ru.ctorParams = head.arguments.length ∧
    TrRestoredRecursorRule g r venv lparams head index rule ∧
    ∃ df, r.equation (g.equation index) = some df ∧ ru.rhs = df.rhs ∧
      TrExprS venv lparams [] rule.rhs df.rhs

/-- The model recursor read off one restored kernel recursor (`rv`) and its base entry (`e`). -/
def RestoredRecSpec {s : InductiveSignature} (g : Instance s) (r : Restoration)
    (sourceNames : List Name) (venv : VEnv) (owner : Fin s.families.size)
    (rv : Lean.RecursorVal) (e : ConstantInfo × VConstVal) (vr : VRecursor) : Prop :=
  vr.toVConstVal = e.2 ∧ vr.all = rv.all ∧ vr.numParams = rv.numParams ∧
    vr.numMotives = rv.numMotives ∧ vr.numMinors = rv.numMinors ∧
    vr.numIndices = rv.numIndices ∧ vr.k = rv.k ∧
    r.recursor (g.recursor owner) = some e.2 ∧
    TrRestoredRecursorVal g r sourceNames venv owner rv ∧
    ∃ head, g.restoredFamilyHead r owner = some head ∧ rv.getMajorInduct = head.name ∧
      List.Forall₂ (fun (ir : Fin s.constructors.size × Lean.RecursorRule) ru =>
          RestoredRuleSpec g r venv rv.levelParams head ir.1 ir.2 ru)
        ((s.ownedConstructors owner).zip rv.rules) vr.rules ∧
      List.Forall₂ (TrRestoredRecursorRule g r venv rv.levelParams head)
        (s.ownedConstructors owner) rv.rules

theorem RestoredRecSpec.exists {s : InductiveSignature} {g : Instance s} {r : Restoration}
    {sourceNames : List Name} {venv : VEnv} {owner : Fin s.families.size}
    {rv : Lean.RecursorVal} {e : ConstantInfo × VConstVal}
    (H : TrRestoredRecursorEntry g r sourceNames venv owner e) (he : e.1 = .recInfo rv) :
    ∃ vr, RestoredRecSpec g r sourceNames venv owner rv e vr := by
  obtain ⟨rec, he', hrec, HV⟩ := H
  have hrv : rec = rv := by rw [he] at he'; injection he' with h; exact h.symm
  subst hrv
  obtain ⟨head, hhead, hmajor, -, -, -, HR⟩ := HV.specialization
  have Hex : List.Forall₂ (fun (index : Fin s.constructors.size) (rule : Lean.RecursorRule) =>
      ∃ ru, RestoredRuleSpec g r venv rec.levelParams head index rule ru)
      (s.ownedConstructors owner) rec.rules := by
    refine Lean4Lean.List.Forall₂.imp (fun index rule h => ?_) HR
    obtain ⟨df, hdf, -, ht⟩ := h.equation
    exact ⟨VRecRule.mk rule.ctor head.arguments.length rule.nfields df.rhs,
      rfl, rfl, rfl, h, df, hdf, rfl, ht⟩
  obtain ⟨rus, hrus⟩ := forall₂_choose Hex
  exact ⟨VRecursor.mk e.2 rec.all rec.numParams rec.numMotives rec.numMinors rec.numIndices
      rec.k rus,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hrec, HV, head, hhead, hmajor, hrus, HR⟩

/-- A nested run with a recorded nested occurrence generates an auxiliary
family, so its expanded block has more than one family. -/
theorem NestedRun.one_lt_familiesSize
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    (hnested : result.aux2nested.size ≠ 0) :
    1 < E.lowered.recursors.generationSignature.families.size := by
  rcases E.lowering with ⟨finalState, Hrun, _, _⟩
  have hmap := Hrun.resultAuxMap
  have hne : finalState.nestedAux.size ≠ 0 := by
    intro h
    apply hnested
    rw [hmap, Array.size_eq_zero_iff.mp h]
    rfl
  have hentry := Array.getElem_mem (xs := finalState.nestedAux) (i := 0) (by omega)
  obtain ⟨j, hj, hinit, -⟩ := (Hrun.resolvedAuxFamilyPosition rfl).position _ _ hentry
  rcases Hrun.source with
    ⟨first, rest, _tail, _paramsState, _lctx, _params, htypes, _Hopening,
      _hnewTypes, _hinitialAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hresult : result.types.length = finalState.newTypes.size := by
    rw [Hqueue.resultTypes]; simp
  have hN : E.lowered.recursors.generationSignature.families.size =
      result.types.length := by
    rw [← E.lowered.recursors.entries_length_eq]
    change E.lowered.recursors.entries.length = _
    rw [E.lowered.recursors.generated.length,
      E.lowered.recursors.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        E.lowered.constructors.core]
  have hj' : j < finalState.newTypes.size := hj
  have hinit' : sourceTypes.length ≤ j := by simpa using hinit
  have hlen : 1 ≤ sourceTypes.length := by rw [htypes]; simp
  rw [hN, hresult]
  omega


theorem forall₂_mem_zip_l {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁,
      ∃ b, (a, b) ∈ l₁.zip l₂ ∧ R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab t, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_mem_zip_l t a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall₂_zip_map_snd {α β γ : Type _} {R : α → β → Prop} {S : α × β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S (l₁.zip l₂) l₃ → List.Forall₂ (fun b c => ∃ a, R a b ∧ S (a, b) c) l₂ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨_, h1, h2⟩ (forall₂_zip_map_snd t1 t2)

theorem forall₂_zip_map_fst_eq {α β γ δ : Type _} {R : α → β → Prop} {S : α × β → γ → Prop}
    {f : α → δ} {h : γ → δ} (hS : ∀ ab c, S ab c → h c = f ab.1) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S (l₁.zip l₂) l₃ → l₃.map h = l₁.map f
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons _ t1, .cons h2 t2 => by
    simp only [List.map_cons, hS _ _ h2, forall₂_zip_map_fst_eq hS t1 t2]

/-! ### The model recursors' clauses, per recursor -/

theorem mem_ownedConstructors_owner {s : InductiveSignature} {owner : Fin s.families.size}
    {index : Fin s.constructors.size} (h : index ∈ s.ownedConstructors owner) :
    s.constructors[index].owner = owner := by
  unfold InductiveSignature.ownedConstructors at h
  simp only [List.mem_filter, beq_iff_eq] at h
  exact h.2

theorem mem_ownedConstructors_of_owner {s : InductiveSignature}
    {index : Fin s.constructors.size} :
    index ∈ s.ownedConstructors s.constructors[index].owner := by
  unfold InductiveSignature.ownedConstructors
  simp

private theorem lamBody_const_spine (c : Name) (ls : List VLevel) :
    ∀ (args : List VExpr), args ≠ [] →
      ((VExpr.const c ls).mkApps args).lamBody = (VExpr.const c ls).mkApps args := by
  intro args hargs
  obtain ⟨as, a, rfl⟩ := List.eq_nil_or_concat args |>.resolve_left hargs
  rw [List.concat_eq_append, VExpr.mkApps_snoc]; rfl

/-- The restored left-hand side of a generated equation: the renamed recursor applied to the
restored arguments, as many as the generated ones, the last being the restored constructor
application. -/
theorem Restoration.equation_lhs_spine {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {index : Fin s.constructors.size} {df : VDefEq}
    (hdf : r.equation (g.equation index) = some df)
    (hnot : r.heads.find? (fun h => h.auxiliary == g.recursorName s.constructors[index].owner) =
      none)
    {M : VExpr} (hM : r.expr (g.constructorApp s.constructors[index]
      (s.families.size + s.constructors.size) 0) = some M) :
    ∃ args, df.lhs.lamBody = (VExpr.const (r.recursorName
        (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars)).mkApps args ∧
      args.length = s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].indices.length + 1 ∧
      args.getLast? = some M := by
  obtain ⟨-, hl, -, -⟩ := Restoration.equation_eq_some' hdf
  simp only [Instance.equation, Instance.recursorHead] at hl
  obtain ⟨ds', body', -, hb, hlhs⟩ := Restoration.expr_wrapLams_eq_some hl
  rw [Restoration.expr_mkApps, Option.bind_eq_some_iff] at hb
  obtain ⟨args, ha, hb⟩ := hb
  · simp only [Restoration.expr.go, hnot] at hb
    simp only [Option.some.injEq] at hb
    subst hb
    obtain ⟨pre, last, -, hlast, rfl⟩ := List.mapM_append_eq_some ha
    obtain ⟨M', hM', rfl⟩ : ∃ M', r.expr (g.constructorApp s.constructors[index]
        (s.families.size + s.constructors.size) 0) = some M' ∧ last = [M'] := by
      simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hlast
      obtain ⟨M', hM', _, rfl, rfl⟩ := hlast
      exact ⟨M', hM', rfl⟩
    have hMM : M' = M := Option.some.inj (hM'.symm.trans hM)
    subst hMM
    refine ⟨pre ++ [M'], ?_, ?_, by simp⟩
    · rw [hlhs, VExpr.lamBody_wrapLams, lamBody_const_spine _ _ _ (by simp)]
    · have := List.mapM_some_length ha
      simp only [List.length_append, length_vars, List.length_map, List.length_singleton]
        at this ⊢
      omega

/-- **`OfEquation`** of a model rule read off a restored kernel rule. -/
theorem RestoredRuleSpec.ofEquation {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {lparams : List Name} {head : RestoredFamilyHead}
    {index : Fin s.constructors.size} {rule : Lean.RecursorRule} {ru : VRecRule}
    (H : RestoredRuleSpec g r venv lparams head index rule ru) {vr : VRecursor}
    (hname : vr.name = r.recursorName (g.recursorName s.constructors[index].owner))
    (hmajor : vr.getMajorIdx = s.params.length + (s.families.size + s.constructors.size) +
      s.constructors[index].indices.length)
    (hnot : r.heads.find? (fun h => h.auxiliary == g.recursorName s.constructors[index].owner) =
      none) :
    ∃ df, r.equation (g.equation index) = some df ∧ VRecRule.OfEquation vr ru df := by
  obtain ⟨hctor, hnf, hcp, HT, df, hdf, hrhs, -⟩ := H
  obtain ⟨args, hbody, hlen, hlast⟩ := Restoration.equation_lhs_spine hdf hnot
    HT.constructorApplication
  refine ⟨df, hdf, hrhs.symm, ?_, ?_, VExpr.mkApps (.const rule.ctor head.levels)
    (head.arguments.map (fun arg => arg.liftN
      (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
      vars s.constructors[index].fields.length 0), ?_, ?_, ?_⟩
  · rw [hbody, VExpr.headConst?_eq_some, hname]
    exact ⟨VLevel.params g.uvars, by simp [VExpr.getAppFn]⟩
  · rw [hbody, hmajor]; simp [VExpr.getAppArgs, hlen]
  · rw [hbody]; simpa [VExpr.getAppArgs] using hlast
  · rw [VExpr.headConst?_eq_some, hctor]
    exact ⟨head.levels, by simp [VExpr.getAppFn]⟩
  · simp [VExpr.getAppArgs, hcp, hnf, HT.nfields]

theorem Restoration.recursor_type {r : Restoration} {v w : VConstVal}
    (h : r.recursor v = some w) : r.expr v.type = some w.type ∧ w.name = r.recursorName v.name ∧
      w.uvars = v.uvars := by
  simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at h
  cases ht : r.expr v.type with
  | none => simp [ht] at h
  | some t =>
    simp only [ht, Option.bind_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩

section Spec

variable {s : InductiveSignature} {g : Instance s} {r : Restoration} {sourceNames : List Name}
  {venv : VEnv} {owner : Fin s.families.size} {rv : Lean.RecursorVal}
  {e : ConstantInfo × VConstVal} {vr : VRecursor}

theorem RestoredRecSpec.type (H : RestoredRecSpec g r sourceNames venv owner rv e vr) :
    r.expr (g.recursorType owner) = some vr.type := by
  obtain ⟨hv, -, -, -, -, -, -, hrec, -⟩ := H
  have h := (Restoration.recursor_type hrec).1
  rw [show vr.type = e.2.type by rw [← hv]]
  exact h

theorem RestoredRecSpec.name (H : RestoredRecSpec g r sourceNames venv owner rv e vr) :
    vr.name = r.recursorName (g.recursorName owner) := by
  obtain ⟨hv, -, -, -, -, -, -, hrec, -⟩ := H
  rw [show vr.name = e.2.name by rw [← hv]]
  exact (Restoration.recursor_type hrec).2.1

theorem RestoredRecSpec.counts (H : RestoredRecSpec g r sourceNames venv owner rv e vr) :
    vr.numParams = s.params.length ∧ vr.numMotives = s.families.size ∧
      vr.numMinors = s.constructors.size ∧
      vr.numIndices = s.families[owner].indices.length := by
  obtain ⟨-, -, hp, hm, hmi, hi, -, -, HV, -⟩ := H
  exact ⟨hp.trans HV.numParams, hm.trans HV.numMotives, hmi.trans HV.numMinors,
    hi.trans HV.numIndices⟩

/-- `rec_shape` of a model recursor read off a restored kernel recursor. -/
theorem RestoredRecSpec.recShape (H : RestoredRecSpec g r sourceNames venv owner rv e vr)
    (hr : r.Scoped) (hnp : ∀ h ∈ r.heads, h.nparams = s.params.length) :
    vr.type.RecShape vr.numParams vr.numMotives vr.numMinors vr.numIndices := by
  obtain ⟨hp, hm, hmi, hi⟩ := H.counts
  rw [hp, hm, hmi, hi]
  exact Restoration.recursorType_recShape hr hnp g owner H.type

/-- The rule data of a model rule of a model recursor. -/
theorem RestoredRecSpec.rule_mem (H : RestoredRecSpec g r sourceNames venv owner rv e vr)
    {ru : VRecRule} (hru : ru ∈ vr.rules) :
    ∃ head index rule, g.restoredFamilyHead r owner = some head ∧
      index ∈ s.ownedConstructors owner ∧ rule ∈ rv.rules ∧
      RestoredRuleSpec g r venv rv.levelParams head index rule ru := by
  obtain ⟨-, -, -, -, -, -, -, -, -, head, hhead, -, Hrules, -⟩ := H
  obtain ⟨⟨index, rule⟩, hmem, hspec⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hrules ru hru
  exact ⟨head, index, rule, hhead, (List.of_mem_zip hmem).1, (List.of_mem_zip hmem).2, hspec⟩

theorem RestoredRuleSpec.ctor_headName {head : RestoredFamilyHead}
    {index : Fin s.constructors.size} {lparams : List Name} {rule : Lean.RecursorRule}
    {ru : VRecRule} (H : RestoredRuleSpec g r venv lparams head index rule ru) :
    ru.ctor = r.headName s.constructors[index].name := by
  obtain ⟨hctor, -, -, HT, -⟩ := H
  have h := Restoration.expr_mkApps_const_headConst (r := r) HT.constructorApplication
  simp only [VExpr.headConst?, VExpr.getAppFn_mkApps, VExpr.getAppFn, Option.some.injEq] at h
  rw [hctor, h]

/-- `rule_shape` of a model rule read off a restored kernel rule. -/
theorem RestoredRecSpec.ruleShape (H : RestoredRecSpec g r sourceNames venv owner rv e vr)
    {ru : VRecRule} (hru : ru ∈ vr.rules) :
    ∃ j < vr.numMinors, ∃ A,
      vr.type.piBinders[vr.numParams + vr.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
      ru.nfields ≤ A.piArity ∧
      ru.rhs.RuleShape vr.numParams vr.numMotives vr.numMinors ru.nfields
        (A.piArity - ru.nfields) j := by
  obtain ⟨head, index, rule, -, hidx, -, hspec⟩ := H.rule_mem hru
  have hown := mem_ownedConstructors_owner hidx
  have hT := H.type
  rw [← hown] at hT
  have hc := RestoredRuleSpec.ctor_headName hspec
  obtain ⟨-, hnf, -, HT, df, hdf, hrhs, -⟩ := hspec
  obtain ⟨hp, hm, hmi, -⟩ := H.counts
  rw [hp, hm, hmi, hnf, HT.nfields, hrhs, hc]
  exact Restoration.equation_ruleShape g index hT hdf

/-- Every model rule's reduct is closed. -/
theorem RestoredRecSpec.rules_closed (H : RestoredRecSpec g r sourceNames venv owner rv e vr)
    (hvenv : venv.OrderedStrong) {ru : VRecRule} (hru : ru ∈ vr.rules) : ru.rhs.Closed := by
  obtain ⟨head, index, rule, -, -, -, -, -, -, -, df, -, hrhs, ht⟩ := H.rule_mem hru
  rw [hrhs]
  exact TrExprS.closedN_nil hvenv ht

/-- `OfEquation` of every model rule of a model recursor. -/
theorem RestoredRecSpec.ofEquation (H : RestoredRecSpec g r sourceNames venv owner rv e vr)
    (hindices : ∀ index : Fin s.constructors.size,
      s.constructors[index].indices.length = s.families[s.constructors[index].owner].indices.length)
    (hnot : r.heads.find? (fun h => h.auxiliary == g.recursorName owner) = none)
    {ru : VRecRule} (hru : ru ∈ vr.rules) :
    ∃ index, s.constructors[index].owner = owner ∧
      ∃ df, r.equation (g.equation index) = some df ∧ VRecRule.OfEquation vr ru df := by
  obtain ⟨head, index, rule, -, hidx, -, hspec⟩ := H.rule_mem hru
  have hown := mem_ownedConstructors_owner hidx
  obtain ⟨hp, hm, hmi, hi⟩ := H.counts
  refine ⟨index, hown, RestoredRuleSpec.ofEquation hspec (by rw [H.name, hown]) ?_
    (by rw [hown]; exact hnot)⟩
  simp only [VRecursor.getMajorIdx, hp, hm, hmi, hi, hindices index, hown]
  omega

/-- The model rules of a model recursor against the kernel rules. -/
theorem RestoredRecSpec.rules_forall₂ (H : RestoredRecSpec g r sourceNames venv owner rv e vr) :
    ∃ head, g.restoredFamilyHead r owner = some head ∧
      List.Forall₂ (fun rule ru => ∃ index, index ∈ s.ownedConstructors owner ∧
        TrRestoredRecursorRule g r venv rv.levelParams head index rule ∧
        RestoredRuleSpec g r venv rv.levelParams head index rule ru) rv.rules vr.rules := by
  obtain ⟨-, -, -, -, -, -, -, -, -, head, hhead, -, Hrules, HR⟩ := H
  refine ⟨head, hhead, ?_⟩
  have h := forall₂_zip_map_snd (Lean4Lean.List.Forall₂.and_mem HR) Hrules
  refine Lean4Lean.List.Forall₂.imp (fun rule ru ⟨index, ⟨hT, hidx, _⟩, hspec⟩ =>
    ⟨index, hidx, hT, hspec⟩) h

/-- The constructors of the model rules of a model recursor, in order. -/
theorem RestoredRecSpec.rules_ctors (H : RestoredRecSpec g r sourceNames venv owner rv e vr) :
    vr.rules.map (·.ctor) = (s.ownedConstructors owner).map fun index =>
      r.restoredHeadName s.constructors[index].name := by
  obtain ⟨-, -, -, -, -, -, -, -, -, head, hhead, -, Hrules, HR⟩ := H
  exact forall₂_zip_map_fst_eq (fun ir ru h => h.1.trans h.2.2.2.1.ctor) HR Hrules

/-- Every generated equation of the owner is read off by a model rule. -/
theorem RestoredRecSpec.ofEquation_at (H : RestoredRecSpec g r sourceNames venv owner rv e vr)
    (hindices : ∀ index : Fin s.constructors.size,
      s.constructors[index].indices.length = s.families[s.constructors[index].owner].indices.length)
    (hnot : r.heads.find? (fun h => h.auxiliary == g.recursorName owner) = none)
    {index : Fin s.constructors.size} (hidx : index ∈ s.ownedConstructors owner) :
    ∃ ru ∈ vr.rules, ∃ df, r.equation (g.equation index) = some df ∧
      VRecRule.OfEquation vr ru df := by
  have hname := H.name
  obtain ⟨hp, hm, hmi, hi⟩ := H.counts
  obtain ⟨-, -, -, -, -, -, -, -, -, head, hhead, -, Hrules, HR⟩ := H
  have hown := mem_ownedConstructors_owner hidx
  obtain ⟨rule, hmem, -⟩ := forall₂_mem_zip_l HR index hidx
  obtain ⟨ru, hru, hspec⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hrules _ hmem
  refine ⟨ru, hru, RestoredRuleSpec.ofEquation hspec (by rw [hname, hown]) ?_
    (by rw [hown]; exact hnot)⟩
  simp only [VRecursor.getMajorIdx, hp, hm, hmi, hi, hindices index, hown]
  omega

end Spec


/-- A compilation does not read the source declaration's recursors. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.withRecs {env : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {auxiliaries : List ContainerSpecialization}
    {block : VInductBlock} (H : CompilationData env source expanded s g auxiliaries block)
    (recs : List VRecursor) :
    CompilationData env (source.withRecs recs) expanded s g auxiliaries block where
  sourceWF := H.sourceWF
  sourceParameters := H.sourceParameters
  expandedWF := H.expandedWF
  headerPrefix := H.headerPrefix
  expandedFormation := H.expandedFormation
  model := H.model
  uvars := H.uvars
  nparams := H.nparams
  safety := H.safety
  restorationScoped := H.restorationScoped
  correspondence := H.correspondence
  familyTypesWF := H.familyTypesWF
  types := H.types
  ctors := H.ctors
  projections := H.projections
  admissible := H.admissible
  generatedIHsWellTyped := H.generatedIHsWellTyped
  recursorNames := H.recursorNames
  generatedNames := H.generatedNames
  recursorsFresh := H.recursorsFresh
  recursors := H.recursors
  equations := H.equations
  names := H.names
/-! ### The recursor and compilation half of the restored block -/

/-- **The recursor and compilation fields of `RestoredBlock`** for a nested run `E`, its
rule-free base `C` with its kernel order `hkernel`, and the stripped checker environment of the
base's recursor stage (`Cstrip`), with `decl := sourceDecl.withRecs recs`, the stage environments
`E.sourceCore.envTypes`/`envCtors`, `envR := C.recursorVEnv`, and `rvals := E.restoration.rvals`. -/
theorem NestedRun.assemblyRecursors
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (hnested : result.aux2nested.size ≠ 0)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.loweredDecl = E.lowered.loweredDecl)
    (hkernel : List.Perm
      ((C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map Prod.fst)
      E.restoration.entries)
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.recursorVEnv)
    (hV : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.recursorVEnv) :
    ∃ (recs : List VRecursor) (auxiliaries : List ContainerSpecialization)
      (block : VInductBlock) (envR outVEnv : VEnv),
      ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries ∧
      CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
        (sourceDecl.withRecs recs) E.lowered.loweredDecl E.lowered.signature
        E.lowered.generatedInstance auxiliaries block ∧
      (sourceDecl.withRecs recs).RecsOf block ∧
      (sourceDecl.withRecs recs).addRecs
        ((sourceDecl.withRecs recs).addProjs E.sourceCore.envCtors) = some envR ∧
      List.Forall₂ (TrRecursor (if isUnsafe then .unsafe else .safe)
        ((sourceDecl.withRecs recs).addProjs E.sourceCore.envCtors) envR outEnv.constants)
        E.restoration.rvals (sourceDecl.withRecs recs).recs ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs,
        r.toVConstVal.toVConstant.WF ((sourceDecl.withRecs recs).addProjs E.sourceCore.envCtors)) ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs,
        r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices) ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs, (r.rules.map (·.ctor)).Nodup) ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs, ∀ ru ∈ r.rules,
        ∃ ci, E.sourceCore.envCtors.constants ru.ctor = some ci ∧
          ci.type.CtorShape (ru.ctorParams + ru.nfields)) ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs, ∀ ru ∈ r.rules,
        (∃ c ∈ (sourceDecl.withRecs recs).constructorConstants, ru.ctor = c.name ∧
            ru.ctorParams = (sourceDecl.withRecs recs).nparams) ∨
        (∃ D, VEnv.InstalledBelow (ves.venv (if isUnsafe then .unsafe else .safe)) D ∧
          ∃ c ∈ D.constructorConstants, ru.ctor = c.name ∧ ru.ctorParams = D.nparams)) ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
        r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
        ru.nfields ≤ A.piArity ∧
        ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields
          (A.piArity - ru.nfields) j) ∧
      (∀ r ∈ (sourceDecl.withRecs recs).recs, ∀ ru ∈ r.rules, ru.rhs.Closed) ∧
      (sourceDecl.withRecs recs).addRules envR = some outVEnv ∧
      (∀ rval ∈ E.restoration.rvals, RecursorShapesAt outEnv.constants outVEnv rval) ∧
      (∀ rval ∈ E.restoration.rvals, KLikeRecursor outEnv.constants outVEnv rval) ∧
      envR = C.recursorVEnv ∧
      (∀ df ∈ block.rules, df.WF envR) := by
  classical
  obtain ⟨auxiliaries, rules, D, hrulesEq, Hcert, Hdata, Hentries, Hal, _, _, Haux,
      Hexpansion, HkernelCtors⟩ := E.restoredCompilation wf Hsources C hC hkernel Cstrip
  -- the stage environments
  have Hsource : TrInductDeclCore (ves.venv (if isUnsafe then .unsafe else .safe))
      lparams nparams sourceTypes isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.core
  have htypesEq : C.install.venvTypes = E.sourceCore.envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, Hsource.typesAdded] at h
    exact (Option.some.inj h).symm
  have hctorsEq : C.install.venvCtors = E.sourceCore.envCtors := by
    have h := C.install.abstract_ctors
    rw [C.constructorValues, htypesEq, Hsource.ctorsAdded] at h
    exact (Option.some.inj h).symm
  -- the model recursors
  have hTr := C.rvalsTranslated
  rw [← C.recursorValues, Lean4Lean.List.forall₂_map_right_iff] at hTr
  have Hpair := forall₂_and Hal hTr
  have Htrip := forall₂_zip_left Hpair Hentries
  have Hex := Lean4Lean.List.Forall₂.imp (S := fun owner
      (p : RecursorVal × (ConstantInfo × VConstVal)) => ∃ vr : VRecursor,
        (p.2.1 = .recInfo p.1 ∧
          TrConstVal (if isUnsafe then .unsafe else .safe)
            (C.install.venvCtors.addProjections sourceDecl.projectionEntries) (.recInfo p.1) p.2.2 ∧
          p.2.2.toVConstant.WF (C.install.venvCtors.addProjections sourceDecl.projectionEntries)) ∧
        RestoredRecSpec E.lowered.generatedInstance (compilationRestoration sourceDecl auxiliaries)
          (sourceDecl.types.map (·.name)) C.recursorVEnv owner p.1 p.2 vr)
    (fun owner p ⟨⟨he, htr⟩, hent⟩ =>
      let ⟨vr, hvr⟩ := RestoredRecSpec.exists hent he
      ⟨vr, ⟨he, htr⟩, hvr⟩) Htrip
  obtain ⟨recs, Hrecs⟩ := forall₂_choose Hex
  have hZsnd := forall₂_zip_snd Htrip
  have hPfst := forall₂_zip_fst Hpair
  have hPsnd := forall₂_zip_snd Hpair
  have hrecsVals : recs.map (·.toVConstVal) = C.recursorEntries.map Prod.snd := by
    have h := Lean4Lean.List.Forall₂.map_eq (f := fun q : Fin _ × (RecursorVal ×
        (ConstantInfo × VConstVal)) => q.2.2.2) (g := fun vr : VRecursor => vr.toVConstVal)
      (fun q vr h => h.2.1.symm) Hrecs
    have h2 : ((List.finRange E.lowered.signature.families.size).zip
        (E.restoration.rvals.zip C.recursorEntries)).map (fun q => q.2.2.2) =
        ((((List.finRange E.lowered.signature.families.size).zip
          (E.restoration.rvals.zip C.recursorEntries)).map Prod.snd).map Prod.snd).map
            Prod.snd := by
      simp [List.map_map, Function.comp_def]
    rw [hZsnd, hPsnd] at h2
    rw [← h, h2]
  have Hrv : List.Forall₂ (fun rv vr => ∃ owner e,
      (e.1 = .recInfo rv ∧
        TrConstVal (if isUnsafe then .unsafe else .safe)
          (C.install.venvCtors.addProjections sourceDecl.projectionEntries) (.recInfo rv) e.2 ∧
        e.2.toVConstant.WF (C.install.venvCtors.addProjections sourceDecl.projectionEntries)) ∧
      RestoredRecSpec E.lowered.generatedInstance (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.recursorVEnv owner rv e vr)
      E.restoration.rvals recs := by
    have h : E.restoration.rvals = ((List.finRange E.lowered.signature.families.size).zip
        (E.restoration.rvals.zip C.recursorEntries)).map (fun q => q.2.1) := by
      have h3 : ((List.finRange E.lowered.signature.families.size).zip
          (E.restoration.rvals.zip C.recursorEntries)).map (fun q => q.2.1) =
          (((List.finRange E.lowered.signature.families.size).zip
            (E.restoration.rvals.zip C.recursorEntries)).map Prod.snd).map Prod.fst := by
        simp [List.map_map, Function.comp_def]
      rw [h3, hZsnd, hPfst]
    rw [h, Lean4Lean.List.forall₂_map_left_iff]
    exact Lean4Lean.List.Forall₂.imp (fun q vr h => ⟨q.1, q.2.2, h⟩) Hrecs
  have hrecMem : ∀ vr ∈ recs, ∃ rv owner e, rv ∈ E.restoration.rvals ∧
      (e.1 = .recInfo rv ∧
        TrConstVal (if isUnsafe then .unsafe else .safe)
          (C.install.venvCtors.addProjections sourceDecl.projectionEntries) (.recInfo rv) e.2 ∧
        e.2.toVConstant.WF (C.install.venvCtors.addProjections sourceDecl.projectionEntries)) ∧
      RestoredRecSpec E.lowered.generatedInstance (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.recursorVEnv owner rv e vr := by
    intro vr hvr
    obtain ⟨rv, hrv, owner, e, h1, h2⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hrv vr hvr
    exact ⟨rv, owner, e, hrv, h1, h2⟩
  have hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped := Hdata.restorationScoped
  have hnpS : E.lowered.signature.params.length = sourceDecl.nparams :=
    Hdata.model.nparams.trans Hdata.nparams
  have hnp : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.nparams = E.lowered.signature.params.length := fun h hh =>
    (compilationRestoration_heads_nparams h hh).trans hnpS.symm
  have hindices : ∀ index : Fin E.lowered.signature.constructors.size,
      E.lowered.signature.constructors[index].indices.length =
        E.lowered.signature.families[E.lowered.signature.constructors[index].owner].indices.length :=
    fun index => Hdata.model.constructorArity _ (by simp)
  have hvenvStrong : C.recursorVEnv.OrderedStrong := Cstrip.wf.orderedStrong
  have hclosed : ∀ r ∈ recs, ∀ ru ∈ r.rules, ru.rhs.Closed := by
    intro vr hvr ru hru
    obtain ⟨rv, owner, e, hmem, ⟨he, htr, hwfv⟩, H⟩ := hrecMem vr hvr
    exact RestoredRecSpec.rules_closed H hvenvStrong hru
  obtain ⟨outVEnv, hout⟩ := VEnv.addRules_exists (decl := sourceDecl.withRecs recs)
    C.recursorVEnv hclosed
  have hprojs : (sourceDecl.withRecs recs).addProjs E.sourceCore.envCtors =
      C.install.venvCtors.addProjections sourceDecl.projectionEntries := by
    rw [hctorsEq]; rfl
  have hrecsAdded : (sourceDecl.withRecs recs).addRecs
      ((sourceDecl.withRecs recs).addProjs E.sourceCore.envCtors) = some C.recursorVEnv := by
    rw [VInductDecl.addRecs_eq_addConstVals, hprojs]
    show (C.install.venvCtors.addProjections sourceDecl.projectionEntries).addConstVals
      (recs.map (·.toVConstVal)) = _
    rw [hrecsVals]
    exact C.install.recursorsAdded.abstract
  have hrulesMem : ∀ {index df}, (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.generatedInstance.equation index) = some df → df ∈ rules := by
    intro index df hdf
    have h := List.mapM_eq_some.mp hrulesEq
    obtain ⟨df', hdf', hr⟩ := Lean4Lean.List.Forall₂.forall_exists_l h _
      (List.mem_map_of_mem (f := fun i => E.lowered.generatedInstance.equation i)
        (List.mem_finRange index))
    rw [hdf] at hr
    cases hr
    exact hdf'
  have hrecsRV : ∀ {owner} {p : RecursorVal × (ConstantInfo × VConstVal)},
      (owner, p) ∈ (List.finRange E.lowered.signature.families.size).zip
        (E.restoration.rvals.zip C.recursorEntries) →
      ∃ vr ∈ recs, RestoredRecSpec E.lowered.generatedInstance
        (compilationRestoration sourceDecl auxiliaries) (sourceDecl.types.map (·.name))
        C.recursorVEnv owner p.1 p.2 vr := by
    intro owner p hmem
    obtain ⟨vr, hvr, -, H⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hrecs _ hmem
    exact ⟨vr, hvr, H⟩
  have hHrule := fun owner {head} (hhead : E.lowered.generatedInstance.restoredFamilyHead
      (compilationRestoration sourceDecl auxiliaries) owner = some head) index
      (hown : E.lowered.signature.constructors[index].owner = owner) =>
    E.restoredRuleConstructors wf Hsources D Hcert Hdata (E.constructorArityPrefix C hC) Haux
        Hexpansion HkernelCtors owner hhead index hown
  refine ⟨recs, auxiliaries, restoredBlock sourceDecl C.sourceRecursors C.auxiliaryRecursors
    rules [], C.recursorVEnv, outVEnv, Hcert, Hdata.withRecs recs, ⟨?_, ?_, ?_⟩, hrecsAdded, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hclosed, hout, ?_, ?_, rfl, ?_⟩
  · -- RecsOf.recursors
    show recs.map (·.toVConstVal) = C.sourceRecursors ++ C.auxiliaryRecursors
    rw [hrecsVals, C.recursorValues]
  · -- RecsOf.rules
    intro vr hvr ru hru
    obtain ⟨rv, owner, e, -, -, H⟩ := hrecMem vr hvr
    obtain ⟨index, -, df, hdf, hof⟩ := RestoredRecSpec.ofEquation H hindices
      (Hdata.recursorName_not_head owner) hru
    exact ⟨df, by simp only [restoredBlock, List.append_nil]; exact hrulesMem hdf, hof⟩
  · -- RecsOf.rules_total
    intro df hdf
    simp only [restoredBlock, List.append_nil] at hdf
    have h := List.mapM_eq_some.mp hrulesEq
    obtain ⟨eq, heq, hr⟩ := Lean4Lean.List.Forall₂.forall_exists_r h df hdf
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp heq
    let owner := E.lowered.signature.constructors[k].owner
    obtain ⟨p, hp, -⟩ := forall₂_mem_zip_l Htrip owner (List.mem_finRange owner)
    obtain ⟨vr, hvr, H⟩ := hrecsRV hp
    obtain ⟨ru, hru, df', hdf', hof⟩ := RestoredRecSpec.ofEquation_at H hindices
      (Hdata.recursorName_not_head owner) mem_ownedConstructors_of_owner
    rw [hr] at hdf'
    cases hdf'
    exact ⟨vr, hvr, ru, hru, hof⟩
  · -- the recursor translations
    rw [hprojs]
    refine Lean4Lean.List.Forall₂.imp (fun rv vr h => ?_) Hrv
    obtain ⟨owner, e, ⟨he, htr, -⟩, H⟩ := h
    have hv : vr.toVConstVal = e.2 := H.1
    obtain ⟨head, hhead, Hrules⟩ := RestoredRecSpec.rules_forall₂ H
    obtain ⟨-, hall, hp, hm, hmi, hi, hk, -⟩ := H
    refine ⟨hv ▸ htr, hall, hp, hm, hmi, hi, hk, ?_⟩
    refine Lean4Lean.List.Forall₂.imp (fun rule ru h => ?_) Hrules
    obtain ⟨index, hidx, hT, hspec⟩ := h
    obtain ⟨hctor, hnf, hcp, -, df, -, hrhs, ht⟩ := hspec
    obtain ⟨⟨cval, hcval, hnum⟩, -⟩ := hHrule owner hhead index (mem_ownedConstructors_owner hidx)
    refine ⟨hctor, hnf, ⟨cval, by rw [hT.ctor]; exact hcval, by rw [hcp, hnum]⟩, ?_⟩
    rw [hrhs]; exact ht
  · -- recs_wf
    intro vr hvr
    obtain ⟨rv, owner, e, -, ⟨-, -, hwfv⟩, H⟩ := hrecMem vr hvr
    rw [hprojs, show vr.toVConstVal = e.2 from H.1]
    exact hwfv
  · -- rec_shape
    intro vr hvr
    obtain ⟨rv, owner, e, -, -, H⟩ := hrecMem vr hvr
    exact RestoredRecSpec.recShape H hscoped hnp
  · -- rules_nodup
    intro vr hvr
    obtain ⟨rv, owner, e, -, -, H⟩ := hrecMem vr hvr
    rw [RestoredRecSpec.rules_ctors H]
    exact E.restoredRuleConstructors_nodup Hcert Hdata owner
  · -- rules_ctor
    intro vr hvr ru hru
    obtain ⟨rv, owner, e, -, -, H⟩ := hrecMem vr hvr
    obtain ⟨head, index, rule, hhead, hidx, -, hspec⟩ := RestoredRecSpec.rule_mem H hru
    obtain ⟨hctor, hnf, hcp, hT, -⟩ := hspec
    obtain ⟨-, ⟨ci, hci, hshape⟩, -⟩ := hHrule owner hhead index (mem_ownedConstructors_owner hidx)
    refine ⟨ci, by rw [hctor, hT.ctor]; exact hci, ?_⟩
    rw [hcp, hnf, hT.nfields]; exact hshape
  · -- rules_ctorParams
    intro vr hvr ru hru
    obtain ⟨rv, owner, e, -, -, H⟩ := hrecMem vr hvr
    obtain ⟨head, index, rule, hhead, hidx, -, hspec⟩ := RestoredRecSpec.rule_mem H hru
    obtain ⟨hctor, -, hcp, hT, -⟩ := hspec
    obtain ⟨-, -, halt⟩ := hHrule owner hhead index (mem_ownedConstructors_owner hidx)
    rw [hctor, hT.ctor, hcp]
    exact halt
  · -- rule_shape
    intro vr hvr ru hru
    obtain ⟨rv, owner, e, -, -, H⟩ := hrecMem vr hvr
    exact RestoredRecSpec.ruleShape H hru
  · -- recShapes
    intro rv hrv
    exact (E.restoredRecursorShapes wf Hsources C hC hkernel rv hrv).extend (VEnv.addRules_le hout) id
  · -- recK
    intro rv hrv
    obtain ⟨vr, -, owner, e, -, H⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hrv rv hrv
    obtain ⟨-, -, -, -, -, -, -, -, HV, -⟩ := H
    exact KLikeRecursor.of_k_false (HV.k_eq_false (E.one_lt_familiesSize hnested))
  · -- the restored equations are well formed in the recursor stage
    intro df hdf
    simp only [restoredBlock, List.append_nil] at hdf
    have h := List.mapM_eq_some.mp hrulesEq
    obtain ⟨eq, heq, hr⟩ := Lean4Lean.List.Forall₂.forall_exists_r h df hdf
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp heq
    exact E.hrestoredWF_of wf Hsources auxiliaries D C hC hV k df hr

end VerifyInductive
end Lean4Lean
