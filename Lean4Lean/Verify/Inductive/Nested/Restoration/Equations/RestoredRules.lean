import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.GeneratedGuard

/-! Facts about the restored generated equations of a nested run, used by
`NestedRun.hruleShape_of_base` (`Nested/Restoration/Equations/RestoredRulesBase.lean`)
to extend the rule-free assembly base by the restored generated equations:

* translation of the executable restored rules
  (`trRestoredRecursorRule_of_equation`): the right-hand side of each
  restored rule translates (the right-hand-side type check of the restored
  rules) and its translation is the restored generated right-hand side
  (`restoredRuleRhs_of_trail`, with the freshness of the non-renamed
  restorable names and the input-side avoidance `loweredRulesAvoid_renamed`);
* every restored generated equation of a source constructor is a nested iota
  rule of the restored block (`sourceNestedIotaRule`); every clause,
  including the right-hand-side spine and guardedness, is computed from the
  generator through restoration (`restoredEquation_rhs`,
  `restoredGeneratedAvoidance` in `Nested/Restoration/Equations/GeneratedGuard.lean`);
* rule counts along the restoration steps (`stepRules_length`).

The well-formedness of the restored generated equations in the recursor
environment of the restored block base (`HrestoredWF`) is `hrestoredWF_of`
(`Nested/Restoration/AuxiliaryProjections.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### The restoration is determined by the restoration table data

(as in `Nested/Restoration/RecursorAlignment.lean`, kept local) -/

section TableUniqueness

variable {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
  {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}

end TableUniqueness

/-! ### Replacing the rule lists of the restored block -/

/-! ### Translation of the restored generated equations -/

theorem _root_.Lean4Lean.InductiveSignature.Restoration.equation_eq_some
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

/-- A restored recursor rule's right-hand side translates in any environment
in which the stripped output environment is valid (the rule validator). -/
theorem NestedRun.restoredRuleRhs_translation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {venv : VEnv}
    (hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) venv)
    (hmode : E.validationFuel.cacheMode.Sound venv)
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
  have hrun := E.recursorRuleValidation
  obtain ⟨rule, hrule⟩ : ∃ rule, Hstep.restored.newInfo.rules[j]'hj = rule := ⟨_, rfl⟩
  rw [hrule]
  have hmem : rule ∈ Hstep.restored.newInfo.rules := hrule ▸ List.getElem_mem hj
  have hmem' := hmem
  rw [Hstep.restored.produced] at hmem'
  rcases List.mem_append.mp hrecName with hp | ha
  · obtain ⟨indType, hind, hname⟩ := List.mem_map.mp hp
    subst hname
    obtain ⟨_, target, _, Hty⟩ :=
      validateRestoredRecursorRules.sourceTranslation_of_run hvalid hmode hrun hind Hstep.lookup hmem'
    refine ⟨target, ?_⟩
    have h := Hty.2.1
    rw [← Hstep.restored.produced] at h
    exact h
  · obtain ⟨_, target, _, Hty⟩ :=
      validateRestoredRecursorRules.auxiliaryTranslation_of_run hvalid hmode hrun ha Hstep.lookup hmem'
    refine ⟨target, ?_⟩
    have h := Hty.2.1
    rw [← Hstep.restored.produced] at h
    exact h

/-- **Translation of a restored generated equation.** In the recursor
environment of a restored block base in which the stripped output environment
is valid and the restorable names are fresh, the abstract restoration of the
`k`-th generated equation is a translation of the executable restored rule at
`k` (`TrRestoredRecursorRule`). -/
theorem NestedRun.trRestoredRecursorRule_of_equation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
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
    (hC : C.lowered = E.lowered)
    (hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
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
    hnodup hparamsSize D hscoped hwf
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
  obtain ⟨target, Ht⟩ := E.restoredRuleRhs_translation hvalid (E.cacheSound_of_le C.install.le) hn Hstep j hjNew
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hrhs := E.restoredRuleRhs_of_trail wf Hsources hheads hparamsSize D hscoped Hfresh
    owner Hstep (fun rule hrule => by
      rw [hheads]; exact HL owner Hstep.oldInfo Hstep.lookup rule hrule) j hjNew k hval Ht
  obtain ⟨huvars, hlhs, hrhs', htype⟩ := Restoration.equation_eq_some hrule
  have htarget : target = rule.rhs := Option.some.inj (hrhs.symm.trans hrhs')
  subst htarget
  exact ⟨owner, j, s, t, Hstep, hjNew, hval, huvars, Ht, hlhs, htype⟩

/-! ### Rule counts along the restoration steps -/

/-! ### Owned-constructor enumeration by offsets -/

theorem offsets_mono {α : Type _} (cs : List α) (len : α → Nat) (O : Nat → Nat)
    (hO : ∀ i (hi : i < cs.length), O (i + 1) = O i + len cs[i]) :
    ∀ i j, i ≤ j → j ≤ cs.length → O i ≤ O j := by
  intro i j hij hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have h1 := hO (i + d) (by omega)
    have h2 := ih (by omega) (by omega)
    rw [← Nat.add_assoc, h1]
    omega

/-- Enumerate the owned constructors of a list of owners against a list of
rules, given the owners' rule offsets. -/
theorem forall₂_ownedConstructorsFor_offsets {β : Type _}
    {R : VInductiveType × VConstVal → β → Prop} :
    ∀ (owners : List VInductiveType) (rules : List β) (O : Nat → Nat),
      O 0 = 0 →
      (∀ i (hi : i < owners.length), O (i + 1) = O i + owners[i].ctors.length) →
      rules.length = O owners.length →
      (∀ i (hi : i < owners.length) j (hj : j < owners[i].ctors.length)
        (hk : O i + j < rules.length), R (owners[i], owners[i].ctors[j]) rules[O i + j]) →
      List.Forall₂ R (ownedConstructorsFor owners) rules
  | [], rules, O, h0, _, hlen, _ => by
    simp only [List.length_nil, h0] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen]
    exact .nil
  | o :: os, rules, O, h0, hO, hlen, H => by
    have hsplit : ownedConstructorsFor (o :: os) =
        o.ctors.map (o, ·) ++ ownedConstructorsFor os := rfl
    rw [hsplit]
    have hO1 : O 1 = o.ctors.length := by
      have := hO 0 (by simp)
      simpa [h0] using this
    have hmono := offsets_mono (o :: os) (·.ctors.length) O hO
    have hge : ∀ i, i ≤ os.length → o.ctors.length ≤ O (i + 1) := by
      intro i hi
      rw [← hO1]
      exact hmono 1 (i + 1) (by omega) (by simp; omega)
    have hlenc : o.ctors.length ≤ rules.length := by
      have := hge os.length (Nat.le_refl _)
      rw [hlen]; simpa using this
    rw [← List.take_append_drop o.ctors.length rules]
    refine (Lean4Lean.List.Forall₂.append_of_left (by simp; omega)).mpr ⟨?_, ?_⟩
    · apply Lean4Lean.List.forall₂_of_getElem (by simp; omega)
      intro j hj hj'
      simp only [List.getElem_map, List.getElem_take]
      have hj0 : j < o.ctors.length := by simpa using hj
      have := H 0 (by simp) j hj0 (by rw [h0]; omega)
      simpa [h0] using this
    · apply forall₂_ownedConstructorsFor_offsets os _
        (fun i => O (i + 1) - o.ctors.length)
      · simp [hO1]
      · intro i hi
        have h1 := hO (i + 1) (by simp; omega)
        have h2 := hge i (by omega)
        simp only [List.getElem_cons_succ] at h1
        omega
      · simp only [List.length_drop, hlen, List.length_cons]
      · intro i hi j hj hk
        have h2 := hge i (by omega)
        simp only [List.getElem_drop]
        have hidx : o.ctors.length + (O (i + 1) - o.ctors.length + j) = O (i + 1) + j := by
          omega
        have := H (i + 1) (by simp; omega) j (by simpa using hj)
          (by simp only [List.length_drop] at hk; omega)
        simp only [List.getElem_cons_succ] at this
        simp only [hidx]
        exact this

/-! ### Rule counts and guardedness of the restored rules -/

theorem NestedRun.stepRules_length
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name} {nm : Name} {s t : Environment}
    (Hs : RestoredRecursorStep result E.loweredEnv auxRec allIndNames nm s t)
    (hnm : nm = E.lowered.recursors.canonicalGeneration.recursorName owner) :
    Hs.oldInfo.rules.length = E.lowered.indTypes[owner.val]!.ctors.length ∧
      Hs.restored.newInfo.rules.length = E.lowered.indTypes[owner.val]!.ctors.length := by
  subst hnm
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hs
  have h := (E.lowered.recursors.generated.entry owner.val hi).rules.length
  rw [hinfo] at h
  exact ⟨h, Hs.restored.restoration.rules.length.trans h⟩

/-- Offsets telescope: the rule counts of a run of consecutive families sum
to the difference of their offsets. -/
theorem recursorMinorOffset_sum (indTypes : Array InductiveType) (p : Nat) :
    ∀ m, p + m ≤ indTypes.size →
      ((List.range m).map (fun a => indTypes[p + a]!.ctors.length)).sum =
        recursorMinorOffset indTypes (p + m) - recursorMinorOffset indTypes p
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append,
      recursorMinorOffset_sum indTypes p m (by omega)]
    have hstep := recursorMinorOffset_step indTypes (p + m) (by omega)
    have hmono := recursorMinorOffset_mono indTypes p (p + m) (by omega) (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [← Nat.add_assoc, hstep]
    omega

/-! ### The restored generated equation of a source constructor -/

theorem VExpr.wrapLams_inj_of_length :
    ∀ {D₁ D₂ : List VExpr} {b₁ b₂ : VExpr}, D₁.length = D₂.length →
      VExpr.wrapLams D₁ b₁ = VExpr.wrapLams D₂ b₂ → D₁ = D₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => by simpa [VExpr.wrapLams] using h
  | d₁ :: D₁, d₂ :: D₂, _, _, hlen, h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    injection h with hd hb
    obtain ⟨hD, hbody⟩ := VExpr.wrapLams_inj_of_length (by simpa using hlen) hb
    exact ⟨by rw [hd, hD], hbody⟩

/-- The restored generated equation of a constructor whose owner's recursor
name and whose own name are not restoration heads. -/
theorem Restoration.equation_source_structure {s : InductiveSignature}
    (g : Instance s) (r : Restoration) (k : Fin s.constructors.size) {rule : VDefEq}
    (hrule : r.equation (g.equation k) = some rule)
    (hrec : r.heads.find? (fun h => h.auxiliary ==
      g.recursorName s.constructors[k].owner) = none)
    (hctor : r.heads.find? (fun h => h.auxiliary == s.constructors[k].name) = none) :
    ∃ D idx,
      (g.params ++ g.motives ++ g.minors ++
        insertBinders ((s.fieldTypes s.constructors[k]).map (·.instL g.levels))
          (s.families.size + s.constructors.size)).mapM r.expr = some D ∧
      (s.constructors[k].indices.map fun e =>
        (e.instL g.levels).liftN (s.families.size + s.constructors.size)
          s.constructors[k].fields.length).mapM r.expr = some idx ∧
      rule.lhs = VExpr.wrapLams D (VExpr.mkApps
        (.const (r.recursorName (g.recursorName s.constructors[k].owner))
          (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
            s.constructors[k].fields.length ++ idx ++
          [VExpr.mkApps (.const (r.recursorName s.constructors[k].name) g.levels)
            (vars s.params.length
                (s.families.size + s.constructors.size + s.constructors[k].fields.length + 0) ++
              vars s.constructors[k].fields.length 0)])) ∧
      (∃ X, rule.rhs = VExpr.wrapLams D X) ∧
      (∃ T, rule.type = VExpr.wrapForalls D T) := by
  obtain ⟨-, hlhs, hrhs, htype⟩ := Restoration.equation_eq_some hrule
  simp only [Instance.equation, Instance.recursorHead, Instance.constructorApp] at hlhs hrhs htype
  rw [Restoration.expr_wrapLams_eq] at hlhs hrhs
  rw [Restoration.expr_wrapForalls] at htype
  obtain ⟨D, hD, hlhs⟩ := Option.bind_eq_some_iff.mp hlhs
  rw [hD, Option.bind_some] at hrhs htype
  obtain ⟨lb, hlb, hlhs⟩ := Option.map_eq_some_iff.mp hlhs
  obtain ⟨X, -, hX⟩ := Option.map_eq_some_iff.mp hrhs
  obtain ⟨T, -, hT⟩ := Option.map_eq_some_iff.mp htype
  rw [Restoration.expr_mkApps_const_of_find_none _ hrec] at hlb
  obtain ⟨args, hargs, hlb⟩ := Option.map_eq_some_iff.mp hlb
  simp only [List.mapM_append, Restoration.mapM_expr_vars, List.mapM_cons,
    List.mapM_nil, Restoration.expr_mkApps_const_of_find_none _ hctor] at hargs
  simp only [bind, pure, Option.bind_some, Option.map_some] at hargs
  obtain ⟨pre, hpre, hargs⟩ := Option.bind_eq_some_iff.mp hargs
  obtain ⟨idx, hidx, hpre⟩ := Option.bind_eq_some_iff.mp hpre
  refine ⟨D, idx, hD, hidx, ?_, ⟨X, hX.symm⟩, ⟨T, hT.symm⟩⟩
  rw [← hlhs, ← hlb]
  simp only [Option.some.injEq] at hargs hpre
  rw [← hargs, ← hpre]

/-! ### Helpers for the restored source equations -/

/-- The data of the source-family translations at one family position. -/
theorem SourceFamilyTranslations.at
    {decl : VInductDecl} {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    ∀ (f : Nat) (hf : f < types.length), ∃ (ho : f < owners.length)
      (hr : f < recursors.length) (s m : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames types[f] s m)
      (Hrecursor : SourceRecursorTranslation decl owners[f] safety
        Hstep.restored.recursor envCtors),
      Nonempty (RestoredConstructorTranslations result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv Hstep.restored.constructorEnv
        types[f].ctors owners[f].ctors) ∧
      Hrecursor.recursor = recursors[f] := by
  induction H with
  | nil => intro f hf; simp at hf
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    intro f hf
    cases f with
    | zero => exact ⟨by simp, by simp, _, _, Hstep, Hrecursor, ⟨Hconstructors⟩, rfl⟩
    | succ f =>
      obtain ⟨ho, hr, s, m, Hs, Hr, Hc, heq⟩ := ih f (by simpa using hf)
      exact ⟨by simpa using ho, by simpa using hr, s, m, Hs, Hr, Hc, heq⟩

theorem RestoredRecursorStep.info_eq_of_name_eq
    {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
    {auxRec : NameMap Name} {allIndNames : List Name} {n₁ n₂ : Name}
    {s₁ t₁ s₂ t₂ : Environment}
    (H₁ : RestoredRecursorStep result loweredEnv auxRec allIndNames n₁ s₁ t₁)
    (H₂ : RestoredRecursorStep result loweredEnv auxRec allIndNames n₂ s₂ t₂)
    (hn : n₁ = n₂) :
    H₁.oldInfo = H₂.oldInfo ∧ H₁.restored.newInfo = H₂.restored.newInfo := by
  subst hn
  exact H₁.info_eq H₂

theorem InductiveSignature.declaration_ctors_names (s : InductiveSignature)
    (f : Fin s.families.size) (h : f.val < s.declaration.types.length) :
    (s.declaration.types[f.val]'h).ctors.map (·.name) =
      (s.ownedConstructors f).map (fun i => s.constructors[i].name) := by
  simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx,
    InductiveSignature.ownedConstructors]
  rw [List.map_filterMap]
  have : s.constructors.toList =
      (List.finRange s.constructors.size).map (fun i => s.constructors[i]) := by
    apply List.ext_getElem <;> simp
  rw [this, List.filterMap_map]
  induction (List.finRange s.constructors.size) with
  | nil => rfl
  | cons i l ih =>
    rw [List.filterMap_cons, List.filter_cons, ih]
    simp only [Function.comp, Nat.zero_add, Fin.getElem_fin]
    by_cases hi : (s.constructors[i.val]).owner = f
    · simp [hi]
    · have : ¬ (s.constructors[i.val].owner.val = f.val) := fun h' => hi (Fin.ext h')
      simp [this, hi]

theorem Restoration.find_none_of_mem_prefix {r : Restoration} {types : List VInductiveType}
    {p : Nat} (hheads : r.heads.map (·.auxiliary) = familyNames (types.drop p))
    (hnodup : (familyNames types).Nodup) {n : Name} (hn : n ∈ familyNames (types.take p)) :
    r.heads.find? (fun h => h.auxiliary == n) = none := by
  apply List.find?_eq_none.mpr
  intro h hh heq
  have heq' : h.auxiliary = n := by simpa using heq
  have hmem : h.auxiliary ∈ familyNames (types.drop p) := by
    rw [← hheads]; exact List.mem_map_of_mem hh
  have hsplit : familyNames types = familyNames (types.take p) ++ familyNames (types.drop p) := by
    simp only [familyNames, ← List.flatMap_append, List.take_append_drop]
  rw [hsplit] at hnodup
  exact (List.nodup_append.mp hnodup).2.2 _ hn _ hmem heq'.symm

/-! ### The restored source equations are nested iota rules -/

set_option maxHeartbeats 4000000 in
/-- **The restored generated equation of a source constructor is a nested
iota rule** of the restored block of a restored block base, for the
source owner and constructor at its position. Every clause is computed from
the generator: the left-hand side and type by `equation_source_structure`,
the right-hand side (its spine, field arguments, recursive results and
guardedness) by `restoredEquation_rhs`, whose recursor avoidance comes from
`restoredGeneratedAvoidance`. -/
theorem NestedRun.sourceNestedIotaRule
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
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
    (hC : C.lowered = E.lowered)
    (hcount : ∀ (f : Nat) (hf : f < sourceDecl.types.length),
      (sourceDecl.types[f]'hf).ctors.length = E.lowered.indTypes[f]!.ctors.length)
    (hauxNames : auxiliaries.map (·.auxiliary) =
      (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    (k : Fin E.lowered.recursors.generationSignature.constructors.size)
    {rule : VDefEq}
    (hrule : (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule)
    (f : Nat) (hf : f < sourceDecl.types.length) (j : Nat)
    (hj : j < (sourceDecl.types[f]'hf).ctors.length)
    (hk : k.val = recursorMinorOffset E.lowered.indTypes f + j) :
    Nonempty (sourceDecl.NestedIotaRule
      (restoredShapeBlock sourceDecl C.sourceRecursors C.auxiliaryRecursors)
      (sourceDecl.types[f]'hf) ((sourceDecl.types[f]'hf).ctors[j]'hj) rule) := by
  have hfamSize : E.lowered.recursors.generationSignature.families.size =
      E.lowered.indTypes.size := by
    rw [← E.lowered.recursors.entries_length_eq,
      E.lowered.recursors.generated.length,
      E.lowered.recursors.recInfos_size_eq_source]
  have hnames := E.recursorNames_order C.sourceNonempty
  have hnamesLen := congrArg List.length hnames
  simp only [List.length_map, List.length_finRange, List.length_append] at hnamesLen
  have hp : (C.main :: C.rest).length = sourceTypes.length :=
    (Lean4Lean.List.Forall₂.length_eq C.sourceTranslations.types).symm
  rw [← C.typesSource] at hp
  have hf' : f < sourceTypes.length := by omega
  have hfFam : f < E.lowered.recursors.generationSignature.families.size := by
    omega
  have hpSize' : sourceDecl.types.length ≤ E.lowered.indTypes.size := by omega
  -- the generated recursor step of the family
  have huvars : rule.uvars = E.lowered.recursors.canonicalGeneration.uvars :=
    (Restoration.equation_eq_some hrule).1
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped (wf.tr (safety := .safe)).map_wf
  obtain ⟨_, -, s', t', Hs', -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hinfos ⟨f, hfFam⟩ (List.mem_finRange _)
  -- the owner and position of the rule
  have hlocal : j < E.lowered.indTypes[f]!.ctors.length := hcount f hf ▸ hj
  -- the source family
  obtain ⟨ho, hr, s0, m0, Hstep, Hrecursor, ⟨Hcons⟩, hrecEq⟩ := C.sourceTranslations.at f hf'
  have hprimName : Lean.mkRecName (sourceTypes[f]'hf').name =
      E.lowered.recursors.canonicalGeneration.recursorName ⟨f, hfFam⟩ := by
    have h := List.getElem_of_eq hnames (i := f) (by simp; omega)
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_append_left
      (as := sourceTypes.map _) (by simpa using hf')] at h
    exact h.symm
  obtain ⟨holdEq, hnewEq⟩ := RestoredRecursorStep.info_eq_of_name_eq Hstep.restored.recursor Hs'
    hprimName
  -- the rule validator at this rule
  have hjOld : j < Hstep.restored.recursor.oldInfo.rules.length := by
    rw [holdEq, (E.stepRules_length ⟨f, hfFam⟩ Hs' rfl).1]; exact hlocal
  have hjNew : j < Hstep.restored.recursor.restored.newInfo.rules.length := by
    rw [Hstep.restored.recursor.restored.restoration.rules.length]; exact hjOld
  -- the generated constructor
  have hkOwner : E.lowered.recursors.generationSignature.constructors[k].owner =
      ⟨f, hfFam⟩ := by
    apply Fin.ext
    have h := E.lowered.recursors.generatedConstructor_owner f (by omega) j
      hlocal (hk ▸ k.isLt)
    simp only [Fin.getElem_fin, hk]
    exact h
  have hi : f < E.lowered.recursors.entries.length := by
    rw [E.lowered.recursors.entries_length_eq]; exact hfFam
  have hmap := E.lowered.recursors.ownedConstructors_map_val ⟨f, hfFam⟩ hi
  have hjOwned : j < (E.lowered.recursors.generationSignature.ownedConstructors
      ⟨f, hfFam⟩).length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, (E.lowered.recursors.generated.entry f hi).rules.length]
    exact hlocal
  have hownedJ : (E.lowered.recursors.generationSignature.ownedConstructors
      ⟨f, hfFam⟩)[j] = k := by
    apply Fin.ext
    rw [RuleAssembly.getElem_of_map_val_eq hmap j hjOwned, hk]
  -- constructor names
  have hloweredDecl : C.formationAssembly.expanded = E.lowered.loweredDecl := by
    rw [C.formationExpanded, hC]
  have HT := C.formationAssembly.types
  rw [hloweredDecl] at HT
  have hlenHT := Lean4Lean.List.Forall₂.length_eq HT
  simp only [List.length_append] at hlenHT
  have hfLow : f < E.lowered.loweredDecl.types.length := by omega
  have HTf := Lean4Lean.List.forall₂_getElem HT f (by simp; omega) hfLow
  rw [List.getElem_append_left hf] at HTf
  have HM := E.lowered.recursorConstruction.generator.models.families
  have hlenHM := Lean4Lean.List.Forall₂.length_eq HM
  have hfDecl : f < E.lowered.signature.declaration.types.length := by
    have h : f < E.lowered.signature.families.size := hfFam
    simpa [InductiveSignature.declaration] using h
  have HMf := Lean4Lean.List.forall₂_getElem HM f hfDecl hfLow
  have hjLow : j < (E.lowered.loweredDecl.types[f]'hfLow).ctors.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq HTf.constructors]; exact hj
  have hctorNameSrc : ((sourceDecl.types[f]'hf).ctors[j]'hj).name =
      E.lowered.recursors.generationSignature.constructors[k].name := by
    have h1 := (Lean4Lean.List.forall₂_getElem HTf.constructors j hj hjLow).name
    have h2 := HMf.2.2.2.2
    have h3 := InductiveSignature.declaration_ctors_names
      E.lowered.recursors.generationSignature ⟨f, hfFam⟩ hfDecl
    have h4 := List.getElem_of_eq (h3.symm.trans h2) (i := j) (by simpa using hjOwned)
    simp only [List.getElem_map, hownedJ] at h4
    rw [← h1, ← h4]
  have hctorLow : ((E.lowered.loweredDecl.types[f]'hfLow).ctors[j]'hjLow).name =
      E.lowered.recursors.generationSignature.constructors[k].name := by
    rw [← hctorNameSrc]
    exact (Lean4Lean.List.forall₂_getElem HTf.constructors j hj hjLow).name
  -- names of the source family are not restoration heads
  have hheadsAux : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hnodupFam : (familyNames E.lowered.loweredDecl.types).Nodup :=
    (List.nodup_append.mp hnodup).1
  have hlowMem : E.lowered.loweredDecl.types[f]'hfLow ∈
      E.lowered.loweredDecl.types.take sourceDecl.types.length := by
    rw [List.mem_iff_getElem]
    exact ⟨f, by simp; omega, by simp⟩
  have hctorHead : (compilationRestoration sourceDecl auxiliaries).heads.find? (fun h =>
      h.auxiliary ==
        E.lowered.recursors.generationSignature.constructors[k].name) = none :=
    Restoration.find_none_of_mem_prefix hheadsAux hnodupFam
      (mem_familyNames.mpr ⟨_, hlowMem, .inr ⟨_, List.getElem_mem hjLow, hctorLow.symm⟩⟩)
  have hfamName : E.lowered.recursors.generationSignature.families[f].name =
      (E.lowered.loweredDecl.types[f]'hfLow).name := by
    have h := HMf.1
    simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx] at h
    exact h
  have hfamHead : (compilationRestoration sourceDecl auxiliaries).heads.find? (fun h =>
      h.auxiliary ==
        E.lowered.recursors.generationSignature.families[f].name) = none :=
    Restoration.find_none_of_mem_prefix hheadsAux hnodupFam
      (mem_familyNames.mpr ⟨_, hlowMem, .inl hfamName⟩)
  -- the source recursor is not renamed
  have hrecNames := E.lowered.recursorConstruction.generator.names
  have hnotRec : E.lowered.recursors.canonicalGeneration.recursorName ⟨f, hfFam⟩ ∉
      (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
    intro hmem
    obtain ⟨pair, hpair, hpairName⟩ := List.mem_map.mp hmem
    obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hpair
    have ha : a ∈ auxiliaries := List.fst_mem_of_mem_zipIdx hai
    have hfamName' : E.lowered.recursors.generationSignature.families[f].name =
        a.auxiliary := by
      have h := hpairName.trans (hrecNames ⟨f, hfFam⟩)
      exact (Name.str.inj h).1.symm
    have hmemHead : (⟨a.auxiliary, sourceDecl.uvars, sourceDecl.nparams, a.source.name,
        a.levels, a.arguments⟩ : HeadSpecialization) ∈
          (compilationRestoration sourceDecl auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have := List.find?_eq_none.mp hfamHead _ hmemHead
    simp only [beq_iff_eq] at this
    exact this (by simpa using hfamName'.symm)
  have hsame : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName (sourceTypes[f]'hf').name := by
    rw [Hstep.restored.recursor.restored.mappedName, nameMap_getD_eq, ← D.recursorName,
      hprimName]
    exact Restoration.recursorName_of_not_mem hnotRec
  -- the old and new rule at the position
  have Rj := Hstep.restored.recursor.restored.restoration.rules.entry j hjOld hjNew
  obtain ⟨hi', hinfo⟩ := E.generatedEntryOfStep ⟨f, hfFam⟩ Hs'
  have RR := E.lowered.recursors.trRules
    E.lowered.recursors.ruleRhsTranslations ⟨f, hfFam⟩ hi'
  have hjEntry : j < (E.lowered.recursors.generated.entry f hi').info.rules.length := by
    rw [hinfo, ← holdEq]; exact hjOld
  have RRj := Lean4Lean.List.forall₂_getElem RR j hjOwned hjEntry
  have hentryEq : (E.lowered.recursors.generated.entry f hi').info =
      Hstep.restored.recursor.oldInfo := hinfo.trans holdEq.symm
  have holdRule : (E.lowered.recursors.generated.entry f hi').info.rules[j] =
      Hstep.restored.recursor.oldInfo.rules[j] :=
    List.getElem_of_eq (congrArg RecursorVal.rules hentryEq) hjEntry
  have hctorOld : (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor =
      (Hstep.restored.recursor.oldInfo.rules[j]'hjOld).ctor := by
    have h := Rj.ctor
    have hb : (Hstep.restored.recursor.restored.newRecName ==
        Lean.mkRecName (sourceTypes[f]'hf').name) = true := by
      rw [hsame]; exact beq_self_eq_true _
    rw [hb, if_pos rfl] at h
    exact h
  have hctorGen : (Hstep.restored.recursor.oldInfo.rules[j]'hjOld).ctor =
      E.lowered.recursors.generationSignature.constructors[k].name := by
    have h := RRj.ctor
    rw [holdRule] at h
    rw [h, hownedJ]
  have hnewCtor : (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor =
      E.lowered.recursors.generationSignature.constructors[k].name :=
    hctorOld.trans hctorGen
  have hnewFields : (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).nfields =
      E.lowered.recursors.generationSignature.constructors[k].fields.length := by
    have h := RRj.nfields
    rw [holdRule] at h
    rw [Rj.nfields, h, hownedJ]
  -- counts of the restored recursor
  obtain ⟨⟨rtype, hrtype, hrconst⟩, hnumP, hnumI, hnumM, hnumMin⟩ :=
    E.restoredRecursorShapeFields C hC wf Hsources hadded Haux Hexpansion hnodup hparamsSize D
      hscoped ⟨f, hfFam⟩ Hs'
  rw [← hnewEq] at hnumP hnumI hnumM hnumMin hrconst
  have hnp : result.nparams =
      E.lowered.recursors.generationSignature.params.length := by
    rw [← E.statsParamsSize]; exact E.lowered.recursors.params_size_eq
  have hdeclNp : sourceDecl.nparams =
      E.lowered.recursors.generationSignature.params.length :=
    D.nparams.trans hnp
  -- the restored generated equation
  obtain ⟨D0, idx, hD0, hidx, hlhsEq, ⟨X0, hrhsEq0⟩, ⟨T0, htypeEq0⟩⟩ :=
    Restoration.equation_source_structure _ _ k hrule
      (by rw [hkOwner]; exact E.recursorName_not_head Haux Hexpansion hnodup ⟨f, hfFam⟩)
      hctorHead
  have hD0len : D0.length =
      E.lowered.recursors.generationSignature.params.length +
        E.lowered.recursors.generationSignature.families.size +
        E.lowered.recursors.generationSignature.constructors.size +
        E.lowered.recursors.generationSignature.constructors[k].fields.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hD0)]
    simp [InductiveSignature.Instance.params, InductiveSignature.Instance.motives,
      InductiveSignature.Instance.minors, insertBinders, InductiveSignature.fieldTypes]
    omega
  have hidxLen : idx.length =
      E.lowered.recursors.generationSignature.constructors[k].indices.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hidx)]
    simp
  -- the restored right-hand side
  obtain ⟨L, hmention, hrecType⟩ := E.restoredGeneratedAvoidance wf Hsources hadded Haux
    Hexpansion hauxNames C hC
  obtain ⟨hprefixAvoid, hpieces⟩ := recursorType_pieces_avoid _ ⟨f, hfFam⟩ (hrecType _)
  obtain ⟨hfieldsAvoid, -, hrecAvoid⟩ := hpieces k
  obtain ⟨D1, calls, hD1, -, hcallsLen, hrhsGen, hguardGen⟩ := restoredEquation_rhs _ _
    hmention (fun o => E.recursorName_not_head Haux Hexpansion hnodup o)
    (E.restoredRecursorName_mem D C) hprefixAvoid k hfieldsAvoid hrecAvoid hrule
  have hD1eq : D1 = D0 := Option.some.inj (hD1.symm.trans hD0)
  subst D1
  -- the restored recursor of the family
  have howner : (C.main :: C.rest)[f]'ho = sourceDecl.types[f]'hf :=
    List.getElem_of_eq C.typesSource.symm ho
  obtain ⟨S0⟩ := Hrecursor.shape
  have hS0name : Hrecursor.recursor.name = sourceDecl.recursorName (sourceDecl.types[f]'hf) :=
    S0.name.trans (congrArg sourceDecl.recursorName howner)
  have hS0uvars := S0.uvars
  have hrecMemPrim : Hrecursor.recursor ∈ C.sourceRecursors := hrecEq ▸ List.getElem_mem hr
  have hrecMem : Hrecursor.recursor ∈
      (restoredShapeBlock sourceDecl C.sourceRecursors C.auxiliaryRecursors).recursors := by
    simp only [restoredShapeBlock, restoredBlock]
    exact List.mem_append_left _ hrecMemPrim
  have hrecName : Hrecursor.recursor.name = Hstep.restored.recursor.restored.newInfo.name :=
    Hrecursor.name.trans Hstep.restored.recursor.restored.restoration.name.symm
  have hrecUvars : Hrecursor.recursor.uvars =
      Hstep.restored.recursor.restored.newInfo.levelParams.length := by
    rw [Hstep.restored.recursor.restored.restoration.levelParams]; exact Hrecursor.uvars.symm
  have hadd := C.install.recursorsAdded.abstract
  rw [C.recursorValues] at hadd
  have hinst := VEnv.addConstVals_get hadd (List.mem_append_left _ hrecMemPrim)
  rw [hrecName, hrconst] at hinst
  have hrecType : Hrecursor.recursor.type = rtype :=
    (congrArg VConstant.type (Option.some.inj hinst)).symm
  obtain ⟨pre, major, hpre, -, htypeEq⟩ := Restoration.expr_recursorType_eq_some _ hrtype
  have hpreLen : pre.length =
      E.lowered.recursors.generationSignature.params.length +
        E.lowered.recursors.generationSignature.families.size +
        E.lowered.recursors.generationSignature.constructors.size +
        (E.lowered.recursors.generationSignature.families[f]'hfFam).indices.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)]
    exact Instance.recursorPrefix_length _ _
  -- index counts and universe levels
  have hownerIdx : (sourceDecl.types[f]'hf).numIndices =
      (E.lowered.recursors.generationSignature.families[f]'hfFam).indices.length := by
    have h1 := HTf.numIndices
    have h2 := HMf.2.2.1
    simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx] at h2
    rw [← h1, ← h2]
    rfl
  have hctorIdx : E.lowered.recursors.generationSignature.constructors[k].indices.length =
      (E.lowered.recursors.generationSignature.families[f]'hfFam).indices.length := by
    have h := E.lowered.recursorConstruction.generator.models.constructorArity
      _ (Array.getElem_mem_toList k.isLt)
    simp only [Fin.getElem_fin] at hkOwner ⊢
    refine h.trans ?_
    simp only [hkOwner]
    rfl
  have hlevels : E.lowered.recursors.canonicalGeneration.levels.length =
      sourceDecl.uvars := by
    have h1 := E.lowered.recursorConstruction.generator.admissible.levels_length
    have h2 := E.lowered.recursorConstruction.generator.models.uvars
    have h3 := C.formationAssembly.uvars
    rw [hloweredDecl] at h3
    exact h1.trans (h2.trans h3)
  -- the nested recursor shape of the restored recursor
  obtain ⟨Lp, Lm, Lmi, Li, Lma, hsplit, hLp, hLm, hLmi, hLi, hLma⟩ :=
    List.exists_append_five_of_length_eq (pre ++ [major])
      E.lowered.recursors.generationSignature.params.length
      E.lowered.recursors.generationSignature.families.size
      E.lowered.recursors.generationSignature.constructors.size
      (E.lowered.recursors.generationSignature.families[f]'hfFam).indices.length 1
      (by simp only [List.length_append, List.length_singleton, hpreLen])
  have hownedLen : sourceDecl.ownedConstructors.length ≤
      E.lowered.recursors.generationSignature.constructors.size := by
    have hsum : sourceDecl.ownedConstructors.length =
        recursorMinorOffset E.lowered.indTypes sourceDecl.types.length := by
      rw [← ownedConstructorsFor_eq]
      have key : ∀ (types : List VInductiveType) (f0 : Nat),
          (∀ i (hi : i < types.length), (types[i]'hi).ctors.length =
            E.lowered.indTypes[f0 + i]!.ctors.length) →
          f0 + types.length ≤ E.lowered.indTypes.size →
          (ownedConstructorsFor types).length =
            recursorMinorOffset E.lowered.indTypes (f0 + types.length) -
              recursorMinorOffset E.lowered.indTypes f0 := by
        intro types
        induction types with
        | nil => intro f0 _ _; simp [ownedConstructorsFor]
        | cons t ts ih =>
          intro f0 hc hle
          have h0 : t.ctors.length = E.lowered.indTypes[f0]!.ctors.length := by
            have := hc 0 (by simp)
            simp only [List.getElem_cons_zero, Nat.add_zero] at this
            exact this
          have hstep := recursorMinorOffset_step E.lowered.indTypes f0 (by simp at hle; omega)
          have hrest := ih (f0 + 1) (fun i hi => by
            have := hc (i + 1) (by simp; omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this) (by simp at hle; omega)
          have hmono := recursorMinorOffset_mono E.lowered.indTypes (f0 + 1)
            (f0 + 1 + ts.length) (by omega) (by simp at hle; omega)
          have hsplit' : ownedConstructorsFor (t :: ts) =
              t.ctors.map (t, ·) ++ ownedConstructorsFor ts := rfl
          rw [hsplit', List.length_append, List.length_map, hrest]
          simp only [List.length_cons]
          rw [show f0 + (ts.length + 1) = f0 + 1 + ts.length by omega]
          omega
      have := key sourceDecl.types 0 (fun i hi => by simpa using hcount i hi) (by simpa using hpSize')
      simpa [recursorMinorOffset] using this
    rw [hsum, ← E.lowered.recursors.constructors_size_offset.symm]
    exact recursorMinorOffset_mono _ _ _ hpSize' (Nat.le_refl _)
  have htype' : Hrecursor.recursor.type = VExpr.wrapForalls (Lp ++ Lm ++ Lmi ++ Li ++ Lma)
      (E.lowered.recursors.canonicalGeneration.recursorBody ⟨f, hfFam⟩) := by
    rw [hrecType, htypeEq, hsplit]
  have hresult : E.lowered.recursors.canonicalGeneration.recursorBody ⟨f, hfFam⟩ =
      sourceDecl.recursorResultWithCounts f Lm.length Lmi.length (sourceDecl.types[f]'hf) := by
    simp only [Instance.recursorBody, VInductDecl.recursorResultWithCounts, hLm, hLmi,
      hownerIdx, vars]
    congr 1
    · congr 1
      simp only [Fin.getElem_fin]
      omega
    · congr 1
      apply List.map_congr_left
      intro i _
      rw [Nat.add_comm]
  let S1 : sourceDecl.NestedRecursorShape (sourceDecl.types[f]'hf) Hrecursor.recursor :=
    VInductDecl.NestedRecursorShape.ofWrapped hf rfl hS0name hS0uvars
      (by rw [hLp, hdeclNp]) (by rw [hLm]; omega) (by rw [hLmi]; exact hownedLen)
      (by rw [hLi, hownerIdx]) hLma htype' hresult
  -- the restored names in the left-hand side
  have hrecRestored : (compilationRestoration sourceDecl auxiliaries).recursorName
      (E.lowered.recursors.canonicalGeneration.recursorName
        E.lowered.recursors.generationSignature.constructors[k].owner) =
      Hstep.restored.recursor.restored.newInfo.name :=
    (congrArg (fun o => (compilationRestoration sourceDecl auxiliaries).recursorName
      (E.lowered.recursors.canonicalGeneration.recursorName o)) hkOwner).trans
      ((Restoration.recursorName_of_not_mem hnotRec).trans (hprimName.symm.trans
        (hsame.symm.trans Hstep.restored.recursor.restored.restoration.name.symm)))
  have hctorRestored : (compilationRestoration sourceDecl auxiliaries).recursorName
      E.lowered.recursors.generationSignature.constructors[k].name =
      (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor := by
    rw [hnewCtor]
    apply Restoration.recursorName_of_not_mem
    rw [compilationRestoration_recursors_fst]
    intro hmem
    obtain ⟨a, ha, haName⟩ := List.mem_map.mp hmem
    have haLow : a.auxiliary ∈ E.lowered.loweredDecl.types.map (·.name) := by
      have h1 : a.auxiliary ∈ auxiliaries.map (·.auxiliary) := List.mem_map_of_mem ha
      rw [hauxNames] at h1
      obtain ⟨t, ht, htn⟩ := List.mem_map.mp h1
      exact List.mem_map.mpr ⟨t, List.mem_of_mem_drop ht, htn⟩
    have hrecMem' : E.lowered.recursors.generationSignature.constructors[k].name ∈
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec") := by
      obtain ⟨t, ht, htn⟩ := List.mem_map.mp haLow
      rw [← haName, ← htn]
      exact List.mem_map_of_mem ht
    have hfamMem : E.lowered.recursors.generationSignature.constructors[k].name ∈
        familyNames E.lowered.loweredDecl.types :=
      mem_familyNames.mpr ⟨_, List.getElem_mem hfLow, .inr ⟨_, List.getElem_mem hjLow,
        hctorLow.symm⟩⟩
    exact (List.nodup_append.mp hnodup).2.2 _ hfamMem _ hrecMem' rfl
  -- the uvars
  have M := E.recursorMetadataOfStep ⟨f, hfFam⟩ Hs'
  have hguvars : E.lowered.recursors.canonicalGeneration.uvars =
      Hstep.restored.recursor.restored.newInfo.levelParams.length := by
    rw [Hstep.restored.recursor.restored.restoration.levelParams, holdEq, M.uvars]
  -- the nested iota rule
  have hnewCtorSrc : ((sourceDecl.types[f]'hf).ctors[j]'hj).name =
      (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor :=
    hctorNameSrc.trans hnewCtor.symm
  rw [hrecRestored, ← hrecName, hctorRestored, ← hnewCtorSrc] at hlhsEq
  obtain ⟨hord, hlt⟩ := recursiveFields_positions
    E.lowered.recursors.generationSignature.constructors[k]
  have hguard := hguardGen.congrRecursors (recursors' :=
    (restoredShapeBlock sourceDecl C.sourceRecursors C.auxiliaryRecursors).recursors.map
      (·.name)) (by
        intro name
        simp [restoredShapeBlock, restoredBlock])
  have hsub := recursiveFields_args_sublist
    E.lowered.recursors.generationSignature.constructors[k]
  refine ⟨nestedIotaRuleOfGenerated Hrecursor.recursor hrecMem S1
    (huvars.trans (hguvars.trans hrecUvars.symm)) D0
    E.lowered.recursors.generationSignature.params.length
    E.lowered.recursors.generationSignature.constructors[k].fields.length
    (E.lowered.recursors.generationSignature.families.size +
      E.lowered.recursors.generationSignature.constructors.size)
    (VLevel.params E.lowered.recursors.canonicalGeneration.uvars)
    E.lowered.recursors.canonicalGeneration.levels idx calls
    ((Instance.recursiveFields
      E.lowered.recursors.generationSignature.constructors[k]).map Prod.fst)
    (E.lowered.recursors.generationSignature.constructors[k].fields.length +
      E.lowered.recursors.generationSignature.constructors.size - 1 - k.val) T0
    hdeclNp ?_ ?_ ?_ hlhsEq hrhsGen htypeEq0 ?_ hlevels ?_ hord ?_ hsub ?_ hguard⟩
  · show _ = Lm.length + Lmi.length
    rw [hLm, hLmi]
  · rw [hD0len]; omega
  · rw [hidxLen, hctorIdx, hownerIdx]
  · simp only [VLevel.params, List.length_map, List.length_range]
    exact hguvars.trans hrecUvars.symm
  · have := k.isLt
    rw [hD0len]; omega
  · intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    exact hlt p hp
  · rw [hcallsLen, List.length_map]

end VerifyInductive
end Lean4Lean
