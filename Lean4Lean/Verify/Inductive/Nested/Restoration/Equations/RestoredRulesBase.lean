import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.RestoredRules

/-! The rule-shape hypothesis over the rule-free assembly base.

`RestoredBlockBase.withRules` extends a rule-free restored block base by
two rule lists, building the source iota rules and the auxiliary rule facts out
of the base's source-family translations `sourceTranslations` and its
rule-free auxiliary recursor translations `auxiliaryRecursorTrace`. The
underlying base is the given one definitionally.

`NestedRun.hruleShape_of_base` then extends the base of
`assemblyBaseValid` by the restored generated equations: their
translation comes from the right-hand-side type check of the restored rules,
their nested-iota shape from the generator, and their well-formedness is the
hypothesis `HrestoredWF`. Family counts, rule counts and block names are read
off the base's translations and `stepRules_length`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Building the source iota rules -/

/-- The source iota rules of one family (`SourceIotaRules`) from a rule
restoration list and a pointwise list of well-formed nested iota rules of the
same length. -/
theorem SourceIotaRules.ofForall₂
    {decl : VInductDecl} {block : VInductBlock} {owner : VInductiveType}
    {result : Lean4Lean.ElimNestedInductive.Result} {prodEnv : Environment}
    {P : LoweredRun prodEnv} {targetVEnv : VEnv} {auxRec : NameMap Name}
    {oldRecName newRecName : Name} {oldRules newRules : List RecursorRule}
    (Hrules : RulesRestoration result prodEnv auxRec oldRecName newRecName oldRules newRules) :
    ∀ {ctors : List VConstVal} {rules : List VDefEq},
      ctors.length = oldRules.length →
      List.Forall₂ (fun ctor rule =>
        Nonempty (decl.NestedIotaRule block owner ctor rule) ∧ rule.WF targetVEnv)
        ctors rules →
      SourceIotaRules decl block owner result prodEnv P targetVEnv auxRec
        oldRecName newRecName Hrules ctors rules := by
  induction Hrules with
  | nil =>
    intro ctors rules hlen H
    have : ctors = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    cases H
    exact .nil
  | cons Hrule Htail ih =>
    intro ctors rules hlen H
    cases H with
    | nil => simp at hlen
    | cons h t =>
      exact .cons Hrule Htail _ (Classical.choice h.1) h.2 (ih (by simpa using hlen) t)

/-- The source iota rules of every family (`SourceIotaRulesAll`) over the
source-family translations, from pointwise well-formed nested iota rules for the
owned constructors, given that each owner has as many constructors as its
lowered recursor has rules. -/
theorem SourceFamilyTranslations.sourceIotaOfRules
    {decl : VInductDecl} {block : VInductBlock} {targetVEnv : VEnv}
    {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : LoweredRun loweredEnv)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {sourceTypes : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    (Hsource : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (hcount : List.Forall₂ (fun (indType : InductiveType) (owner : VInductiveType) =>
      ∀ (s m : Environment) (Hstep : RestoredInductiveStep result loweredEnv auxRec
          allIndNames indType s m),
        owner.ctors.length = Hstep.restored.recursor.oldInfo.rules.length)
      sourceTypes owners)
    {rules : List VDefEq}
    (H : List.Forall₂ (fun (oc : VInductiveType × VConstVal) rule =>
      Nonempty (decl.NestedIotaRule block oc.1 oc.2 rule) ∧ rule.WF targetVEnv)
      (ownedConstructorsFor owners) rules) :
    SourceIotaRulesAll decl block targetVEnv P Hsource owners rules := by
  induction Hsource generalizing rules with
  | nil => cases H; exact .nil _
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    cases hcount with
    | cons hc hcount =>
      obtain ⟨r₁, r₂, rfl, Hh, Ht⟩ := List.Forall₂.append_inv H
      rw [Lean4Lean.List.forall₂_map_left_iff] at Hh
      exact .cons Hstep Htail Hheader Hconstructors Hrecursor Hrest
        (SourceIotaRules.ofForall₂ _ (hc _ _ Hstep) Hh)
        (ih hcount Ht)

/-! ### Building the auxiliary rule facts -/

/-- The guarded-rule and well-formedness facts of the auxiliary recursors
(`AuxiliaryRecursorRuleBatches`, `RestoredAuxiliaryRecursorsWF`) over rule-free
auxiliary recursor translations, for any block: the added rules need only the
right per-step counts and be well formed. -/
theorem AuxiliaryRecursorTranslations.shapeWF
    {safety : DefinitionSafety} {trEnv recursorEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    {priorRecursors finalRecursors : List VConstVal}
    (H : AuxiliaryRecursorTranslations safety trEnv recursorEnv Htrace
      priorRecursors finalRecursors)
    (ruleEnv : VEnv)
    {counts : List Nat}
    (Hc : List.Forall₂ (fun (name : Name) (c : Nat) =>
      ∀ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv auxRec
        allIndNames name s t), Hstep.restored.newInfo.rules.length = c) names counts)
    (priorRules added finalRules : List VDefEq)
    (hfinal : finalRules = priorRules ++ added)
    (hlen : added.length = counts.sum)
    (Hwf : ∀ rule ∈ added, rule.WF ruleEnv) :
    ∃ Hsemantic : AuxiliaryRecursorRuleBatches safety trEnv Htrace
        priorRecursors priorRules finalRecursors finalRules,
      RestoredAuxiliaryRecursorsWF safety trEnv recursorEnv ruleEnv
        Hsemantic priorRecursors priorRules finalRecursors finalRules :=
  match H, Hc with
  | .nil sourceEnv recursors, .nil => by
    have hnil : added = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [List.append_nil] at hfinal
    subst finalRules
    exact ⟨.nil _ recursors priorRules, .nil _ recursors priorRules⟩
  | .cons Hstep Htail Hhead Hrest, .cons hc Hc => by
    have hm := hc _ _ Hstep
    simp only [List.sum_cons] at hlen
    let m := Hstep.restored.newInfo.rules.length
    let Hsemantic : AuxiliaryRecursorRuleBatch safety trEnv Hstep := {
      recursor := Hhead.recursor
      rules := added.take m
      translated := Hhead.translated
      rulesLength := by
        rw [List.length_take]
        omega }
    obtain ⟨Hrest', Hfinal'⟩ := Hrest.shapeWF ruleEnv Hc
      (priorRules ++ added.take m) (added.drop m) finalRules
      (by rw [hfinal, List.append_assoc, List.take_append_drop])
      (by simp only [List.length_drop]; omega)
      (fun rule hrule => Hwf rule (List.mem_of_mem_drop hrule))
    exact ⟨.cons Hstep Htail Hsemantic Hrest', .cons Hstep Htail Hsemantic Hrest' Hhead.wf
      (fun rule hrule => Hwf rule (List.mem_of_mem_take hrule)) Hfinal'⟩

/-! ### Extending a base by rule lists -/

/-- A restored block derivation over a rule-free base `B`, with the given rule
lists. The source iota rules and the auxiliary rule facts are built from
`B.sourceTranslations` and `B.auxiliaryRecursorTrace`; the underlying base is
`B` itself
(`RestoredBlockBase.withRules_toBase`). -/
noncomputable def RestoredBlockBase.withRules
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (B : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety)
    (primaryRules auxiliaryRules : List VDefEq)
    (hcount : List.Forall₂ (fun (indType : InductiveType) (owner : VInductiveType) =>
      ∀ (s m : Environment) (Hstep : RestoredInductiveStep result loweredEnv auxRec
          allIndNames indType s m),
        owner.ctors.length = Hstep.restored.recursor.oldInfo.rules.length)
      sourceTypes (B.main :: B.rest))
    (Hprimary : List.Forall₂ (fun (oc : VInductiveType × VConstVal) rule =>
      Nonempty (decl.NestedIotaRule
        (restoredShapeBlock decl B.sourceRecursors B.auxiliaryRecursors)
        oc.1 oc.2 rule) ∧ rule.WF B.recursorVEnv)
      (ownedConstructorsFor (B.main :: B.rest)) primaryRules)
    {counts : List Nat}
    (hauxCounts : List.Forall₂ (fun (name : Name) (c : Nat) =>
      ∀ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv auxRec
        allIndNames name s t), Hstep.restored.newInfo.rules.length = c) auxRecNames counts)
    (hauxLen : auxiliaryRules.length = counts.sum)
    (Hwf : ∀ rule ∈ auxiliaryRules, rule.WF B.recursorVEnv) :
    RestoredBlockDerivation H sourceEnv decl lparams nparams isUnsafe safety :=
  have Haux := B.auxiliaryRecursorTrace.shapeWF B.recursorVEnv hauxCounts [] auxiliaryRules
    auxiliaryRules (by simp) hauxLen Hwf
  { toRestoredBlockBase := B
    sourceRules := primaryRules
    auxiliaryRules := auxiliaryRules
    sourceIota := B.sourceTranslations.sourceIotaOfRules B.lowered hcount Hprimary
    auxiliaryRuleBatches := Haux.elim fun Hsemantic _ => Hsemantic
    auxiliaryWF := Haux.elim fun _ HWF => HWF }

theorem RestoredBlockBase.withRules_toBase
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (B : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety)
    (primaryRules auxiliaryRules : List VDefEq) (hcount Hprimary)
    {counts : List Nat} (hauxCounts hauxLen Hwf) :
    (B.withRules primaryRules auxiliaryRules hcount Hprimary (counts := counts)
      hauxCounts hauxLen Hwf).toRestoredBlockBase = B := rfl

/-! ### The rule-shape hypothesis over the base -/

/-- **The rule-shape hypothesis `HruleShape` of `hrules_of`, over the
rule-free base.** The base of `assemblyBaseValid` (constructed without
the rule validator) is extended by the restored generated equations
(`RestoredBlockBase.withRules`):

* each restored generated equation is a translation of the executable
  restored rule (`trRestoredRecursorRule_of_equation`, from the
  right-hand-side type check);
* the restored generated equation of a source constructor is a nested iota
  rule of the rule-free restored block `restoredShapeBlock`
  (`sourceNestedIotaRule`, from the generator);
* `HrestoredWF`: each restored generated equation is well formed in the
  recursor environment `B.recursorVEnv` of every base `B` in which the
  stripped output environment is valid.

Family counts, rule counts and block names come from the base's translations,
the run's restoration tables and `stepRules_length`. -/
theorem NestedRun.hruleShape_of_base
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0)
    (HrestoredWF : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        ∀ (k : Fin E.lowered.recursors.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.lowered.recursors.canonicalGeneration.equation k) =
            some rule →
          rule.WF B.recursorVEnv) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered ∧
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules) := by
  intro auxiliaries D
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, hparamsSize, D',
      Hctors, -⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, hauxNames, -, -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  rcases E.assemblyBaseValid wf Hsources hnested with ⟨⟨B, hB, hV⟩⟩
  have hfresh := fresh_filter_restorable
    (E.recursorVEnv_restorableNames_fresh_of_not_renamed wf Hsources B hB D')
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D'
  -- the restored generated equations
  have hrecs := E.restoredRecursorList_of_paramUniform B hB wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D' hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl aux').expr
      (E.lowered.generatedInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl aux').expr
        (E.lowered.generatedInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.lowered.generatedInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have Hrules : List.Forall₂ (fun k rule => (compilationRestoration sourceDecl aux').equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule)
      (List.finRange E.lowered.recursors.generationSignature.constructors.size)
      rules := by
    have h := List.mapM_eq_some.mp hrulesEq
    simp only [InductiveSignature.Instance.equations] at h
    exact (Lean4Lean.List.forall₂_map_left_iff).mp h
  have hlenRules : rules.length =
      E.lowered.recursors.generationSignature.constructors.size := by
    have := Lean4Lean.List.Forall₂.length_eq Hrules
    simpa using this.symm
  -- translation, in the given table
  have Hreal' : List.Forall₂
      (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
        B.recursorVEnv)
      (List.finRange E.lowered.recursors.generationSignature.constructors.size)
      rules :=
    Lean4Lean.List.Forall₂.imp (fun k _ hk => by
      obtain ⟨owner, j, s, t, Hstep, hj, hk', hu, Ht, hl, hty⟩ :=
        E.trRestoredRecursorRule_of_equation wf Hsources hadded Haux Hexpansion hnodup
          hparamsSize D' hscoped B hB hV hfresh HL k hk
      exact ⟨owner, j, s, t, Hstep, hj, hk', hu, Ht, (D.expr_eq D' _).trans hl,
        (D.expr_eq D' _).trans hty⟩) Hrules
  -- families and offsets
  have hnames := E.recursorNames_order B.sourceNonempty
  have hfamSize : E.lowered.recursors.generationSignature.families.size =
      E.lowered.indTypes.size := by
    rw [← E.lowered.recursors.entries_length_eq,
      E.lowered.recursors.generated.length,
      E.lowered.recursors.recInfos_size_eq_source]
  have hnamesLen := congrArg List.length hnames
  simp only [List.length_map, List.length_finRange, List.length_append] at hnamesLen
  have hp : (B.main :: B.rest).length = sourceTypes.length :=
    (Lean4Lean.List.Forall₂.length_eq B.sourceTranslations.types).symm
  rw [← B.typesSource] at hp
  have hprimName : ∀ (f : Nat) (hf : f < sourceTypes.length),
      Lean.mkRecName (sourceTypes[f]'hf).name =
        E.lowered.recursors.canonicalGeneration.recursorName
          ⟨f, by omega⟩ := by
    intro f hf
    have h := List.getElem_of_eq hnames (i := f) (by simp; omega)
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_append_left
      (as := sourceTypes.map _) (by simpa using hf)] at h
    exact h.symm
  have hauxName : ∀ (a : Nat)
      (ha : a < (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length),
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1[a] =
        E.lowered.recursors.canonicalGeneration.recursorName
          ⟨sourceTypes.length + a, by omega⟩ := by
    intro a ha
    have h := List.getElem_of_eq hnames (i := sourceTypes.length + a) (by simp; omega)
    rw [List.getElem_append_right (by simp)] at h
    simp only [List.getElem_map, List.getElem_finRange, List.length_map,
      Nat.add_sub_cancel_left] at h
    exact h.symm
  have hOn : recursorMinorOffset E.lowered.indTypes E.lowered.indTypes.size =
      E.lowered.recursors.generationSignature.constructors.size :=
    E.lowered.recursors.constructors_size_offset.symm
  have hpSize : sourceDecl.types.length ≤ E.lowered.indTypes.size := by omega
  have hOp : recursorMinorOffset E.lowered.indTypes sourceDecl.types.length ≤
      E.lowered.recursors.generationSignature.constructors.size := by
    rw [← hOn]
    exact recursorMinorOffset_mono _ _ _ hpSize (Nat.le_refl _)
  -- the constructor counts of the source families
  have hcountPrim : ∀ (f : Nat) (hf : f < sourceDecl.types.length),
      (sourceDecl.types[f]'hf).ctors.length = E.lowered.indTypes[f]!.ctors.length := by
    intro f hf
    have hfl : f < E.lowered.loweredDecl.types.length := by
      have := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        E.lowered.constructors.core
      simp only [Array.length_toList] at this
      omega
    have hfi : f < E.lowered.indTypes.toList.length := by simp; omega
    have h1 := Lean4Lean.List.Forall₂.length_eq
      (Lean4Lean.List.forall₂_getElem Hctors f hf (by simp; omega))
    have h2 := Lean4Lean.VerifyInductive.TrInductiveType.ctors_length
      (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt E.lowered.constructors.core
        f hfi hfl)
    simp only [List.getElem_take] at h1
    rw [h1, ← h2]
    simp [getElem!_pos, show f < E.lowered.indTypes.size by omega]
  have hcount : List.Forall₂ (fun (indType : InductiveType) (owner : VInductiveType) =>
      ∀ (s m : Environment) (Hstep : RestoredInductiveStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) indType s m),
        owner.ctors.length = Hstep.restored.recursor.oldInfo.rules.length)
      sourceTypes (B.main :: B.rest) := by
    apply Lean4Lean.List.forall₂_of_getElem (by rw [← B.typesSource]; omega)
    intro f hf hf' s m Hstep
    have hf'' : f < sourceDecl.types.length := by omega
    have howner : (B.main :: B.rest)[f]'hf' = sourceDecl.types[f]'hf'' := by
      simp only [B.typesSource]
    rw [howner, hcountPrim f hf'']
    exact (E.stepRules_length ⟨f, by omega⟩ Hstep.restored.recursor (hprimName f hf)).1.symm
  -- the source rules
  have Hprim : List.Forall₂ (fun (oc : VInductiveType × VConstVal) rule =>
      Nonempty (sourceDecl.NestedIotaRule
        (restoredShapeBlock sourceDecl B.sourceRecursors B.auxiliaryRecursors)
        oc.1 oc.2 rule) ∧ rule.WF B.recursorVEnv)
      (ownedConstructorsFor (B.main :: B.rest))
      (rules.take (recursorMinorOffset E.lowered.indTypes sourceDecl.types.length)) := by
    rw [← B.typesSource]
    apply forall₂_ownedConstructorsFor_offsets sourceDecl.types _
      (recursorMinorOffset E.lowered.indTypes)
    · simp [recursorMinorOffset]
    · intro i hi
      rw [recursorMinorOffset_step _ _ (by omega), hcountPrim i hi]
    · simp only [List.length_take, hlenRules]
      omega
    · intro i hi j hj hk
      simp only [List.length_take] at hk
      have hk' : recursorMinorOffset E.lowered.indTypes i + j < rules.length := by omega
      have hkn : recursorMinorOffset E.lowered.indTypes i + j <
          E.lowered.recursors.generationSignature.constructors.size := by
        omega
      simp only [List.getElem_take]
      have Hk := Lean4Lean.List.forall₂_getElem Hrules _ (by simpa using hkn) hk'
      simp only [List.getElem_finRange] at Hk
      exact ⟨E.sourceNestedIotaRule wf Hsources hadded Haux Hexpansion hnodup hparamsSize D'
          hscoped B hB hcountPrim hauxNames _ Hk i hi j hj rfl,
        HrestoredWF aux' D' B hB hV _ _ Hk⟩
  -- the auxiliary rule counts
  have hauxCounts : List.Forall₂ (fun (name : Name) (c : Nat) =>
      ∀ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) name s t), Hstep.restored.newInfo.rules.length = c)
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1
      ((List.range (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length).map
        (fun a => E.lowered.indTypes[sourceTypes.length + a]!.ctors.length)) := by
    apply Lean4Lean.List.forall₂_of_getElem (by simp)
    intro a ha _ s t Hstep
    simp only [List.getElem_map, List.getElem_range]
    exact (E.stepRules_length ⟨sourceTypes.length + a, by omega⟩ Hstep (hauxName a ha)).2
  have hsrcLen : sourceTypes.length = sourceDecl.types.length := by omega
  have hauxLen : (rules.drop
      (recursorMinorOffset E.lowered.indTypes sourceDecl.types.length)).length =
      ((List.range (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length).map
        (fun a => E.lowered.indTypes[sourceTypes.length + a]!.ctors.length)).sum := by
    rw [recursorMinorOffset_sum _ _ _ (by omega), hsrcLen, show sourceDecl.types.length +
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length =
        E.lowered.indTypes.size by omega, hOn, List.length_drop, hlenRules]
  have HwfAux : ∀ rule ∈ rules.drop
      (recursorMinorOffset E.lowered.indTypes sourceDecl.types.length),
      rule.WF B.recursorVEnv := by
    intro rule hrule
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrule
    simp only [List.length_drop] at hi
    simp only [List.getElem_drop]
    have hm : recursorMinorOffset E.lowered.indTypes sourceDecl.types.length + i <
        rules.length := by omega
    have hmn : recursorMinorOffset E.lowered.indTypes sourceDecl.types.length + i <
        E.lowered.recursors.generationSignature.constructors.size := by omega
    have Hk := Lean4Lean.List.forall₂_getElem Hrules _ (by simpa using hmn) hm
    exact HrestoredWF aux' D' B hB hV _ _ Hk
  refine ⟨B.withRules
    (rules.take (recursorMinorOffset E.lowered.indTypes sourceDecl.types.length))
    (rules.drop (recursorMinorOffset E.lowered.indTypes sourceDecl.types.length))
    hcount Hprim hauxCounts hauxLen HwfAux, hB, ?_⟩
  show List.Forall₂ _ _ (rules.take _ ++ rules.drop _)
  rw [List.take_append_drop]
  exact Hreal'

end VerifyInductive
end Lean4Lean
