import Lean4Lean.Verify.Inductive.Nested.Restoration.HeaderRenaming
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.RestoredRules
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorAlignment
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryConstructors
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Verify.Inductive.Nested.CaseEliminators.Restored

/-! The restored-equation well-formedness hypothesis `HrestoredWF` of
`NestedRun.hruleShape_of_base` (`Nested/Restoration/Equations/RestoredRulesBase.lean`).

Route. Every generated equation of the lowered run is well formed in
the lowered recursor environment (`loweredEquationWF`, from
`RecursorCheck.equationsWF` and `ruleRhsTranslations`). The restoration
interpretation (`Restoration.interpretation`, `Theory/Inductive/RestorationInterpretation.lean`)
is a restoration substitution from that environment into the recursor environment
`B.recursorVEnv` of a restored block base; it transports the typing of both sides to the
restored equation (`Restoration.equation_wf`), using beta subject reduction of that well-formed
environment. Its clauses are proved for the context invariant `VEnv.TypedCtx`: the projection
rules of auxiliary structure-like families and the rules of the restored eliminator
(`VEnv.RestoredEliminator.clause`) are transported up to beta, which needs a well-formed
context; the equations are stated in the empty context, so every transported derivation starts
in a well-formed context. The interpretation replaces each restoration head (auxiliary family or
constructor) by its restoration lambda `λ params, target levels args`
(`Restoration.lambdaReplacement`) and renames every other constant and every projection owner
by `Restoration.renaming` (auxiliary recursors to their restored names, auxiliary families in
projection position to their containers). Its soundness is built in stages:

* `headerInterpretationSound`: the lowered header environment (base
  constants and source headers kept, auxiliary headers replaced), in every context;
* `constructorInterpretationSound`: the lowered constructors (source
  constructors kept under their own name with the source constructor type,
  which is definitionally equal to the interpreted lowered type by restoration
  at the header stage; auxiliary constructors replaced), the lowered eliminator and the
  lowered projections;
* `Restoration.interpretation_ofAddConstants_recursors`: the lowered recursors,
  kept under their restored names with the restored recursor types, which are
  definitionally equal to the interpreted lowered types by restoration at the
  previous stage.

`RestorationSubstitutionPremises` collects the facts the substitution is built
from, proved for the run in later modules (`Nested/Restoration/Equations/ProjNames.lean`,
`Nested/Restoration/Equations/AuxiliaryConstructors.lean`,
`Nested/Restoration/AuxiliaryProjections.lean`, where
`NestedRun.restoredEquationGaps` and the hypothesis-free
`NestedRun.hrestoredWF_of` are assembled): projection-name
avoidance of the base eliminator schemas, of the lowered
constructor types, of the generated recursor types and of the generated
equations (restoration keeps projection type names, so a projection of an
auxiliary family in a generated equation would make the restored equation
ill-typed); the typing of the restoration lambdas of the auxiliary
constructors at the restored lowered constructor types; and the transport of
the projection rules of the lowered declaration's projections in well-formed
contexts (including those of auxiliary structure-like families, renamed to
their containers).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- Every generated equation of the lowered run is well formed in the
lowered recursor environment. -/
theorem NestedRun.loweredEquationWF
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (k : Fin E.lowered.recursors.generationSignature.constructors.size) :
    (E.lowered.recursors.canonicalGeneration.equation k).WF
      E.lowered.recursors.outVEnv := by
  have H := E.lowered.recursors.equationsWF
    (E.lowered.recursors.equationBodyTranslations_of
      E.lowered.recursors.ruleRhsTranslations)
  exact H _ (by
    simp only [InductiveSignature.Instance.equations, List.mem_map, List.mem_finRange,
      true_and]
    exact ⟨k, rfl⟩)

/-- **The constructor stage**: the restoration interpretation is sound, in well-formed
contexts, from the lowered constructor environment with its eliminator and projections into the
recursor environment of the restored block base, modulo the typing of the restoration lambdas of
the auxiliary constructors (`HauxCtor`), the transport of the lowered projections (`Hproj`), the
restored eliminators (`Hes`), and projection-name avoidance (`HprojNamesCtor`, `Helim`). -/
theorem NestedRun.constructorInterpretationSound
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
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
    (hauxNames : auxiliaries.map (·.auxiliary) =
      (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    {envS : VEnv} (hSwf : envS.WF) (hle : envTypes ≤ envS)
    (Helim : EliminatorProjNamesAvoid (ves.venv (if isUnsafe then .unsafe else .safe))
      (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (hctorsS : ∀ sc ∈ sourceDecl.constructorConstants,
      envS.constants sc.name = some sc.toVConstant)
    (hnames : List.Forall₂ (fun st lt : VInductiveType => List.Forall₂
        (fun sc lc : VConstVal => lc.name = sc.name) st.ctors lt.ctors)
      sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length))
    (Hlowered : List.Forall₂ (fun lowered source : VInductiveType =>
        List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
            envTypes.SimAt sourceDecl.uvars [] restored sc.type)
          lowered.ctors source.ctors)
      (E.lowered.loweredDecl.types.take sourceDecl.types.length) sourceDecl.types)
    (HprojNamesCtor : ∀ lc ∈ E.lowered.loweredDecl.constructorConstants,
      lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
        true)
    (HauxCtor : ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.auxiliary = lc.name →
        ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
            some restored ∧
          envTypes.HasType sourceDecl.uvars []
            (VExpr.wrapLams E.lowered.signature.params
              (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored)
    (Hproj : ∀ entry ∈ E.lowered.loweredDecl.projectionEntries,
      ((compilationRestoration sourceDecl auxiliaries).interpretation
        E.lowered.signature.params).ProjectionClause envS envS.TypedCtx
        entry.typeName entry.info)
    (Hes : ∀ e ∈ E.lowered.constructors.declared.eliminators, ∃ families r,
      VEnv.RestoredEliminator envS
        ((compilationRestoration sourceDecl auxiliaries).interpretation
          E.lowered.signature.params) e.1 e.2 families r) :
    ((compilationRestoration sourceDecl auxiliaries).interpretation
      E.lowered.signature.params).Sound envS
      ((E.lowered.constructors.declared.venvCtors.addEliminators
          E.lowered.constructors.declared.eliminators).addProjections
        E.lowered.loweredDecl.projectionEntries) envS.TypedCtx := by
  obtain ⟨hsplit, hheadNames, hnp, hargs, hPclosed, hscoped, hrepl⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have ShS := E.headerInterpretationSound wf hadded henvTypes Haux Hexpansion hnodup
    hSwf.ordered hle Helim
  have ShT := E.headerInterpretationSound wf hadded henvTypes Haux Hexpansion hnodup
    henvTypes.ordered VEnv.LE.rfl Helim
  have A := Restoration.interpretation_agrees (P := E.lowered.signature.params) hnp
  have hβT : envTypes.BetaSubjectReduction sourceDecl.uvars := henvTypes.betaSubjectReduction
  have hcore := E.lowered.constructors.core
  -- the lowered constructor constants are well formed in the lowered header environment
  have hloweredUvars : E.lowered.c.lparams.length = sourceDecl.uvars := by
    have h2 := E.sourceCore.core.uvars
    rw [E.sourceCoreDecl_eq] at h2
    rw [h2, E.lowered_c, E.context_lparams]
  have hlcWF : ∀ lc ∈ E.lowered.loweredDecl.constructorConstants,
      lc.uvars = sourceDecl.uvars ∧
        lc.toVConstant.WF E.lowered.constructors.toConstructorCheck.headerVEnv := by
    intro lc hlc
    obtain ⟨t, ht, hlct⟩ := List.mem_flatMap.mp hlc
    obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r hcore.types t ht
    obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors lc hlct
    exact ⟨hC.uvars.trans hloweredUvars, hC.wf⟩
  -- transported typing and restoration of a lowered constructor type, in `envTypes`
  have hsim : ∀ lc ∈ E.lowered.loweredDecl.constructorConstants, ∀ restored,
      (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored →
      ∃ u, envTypes.IsDefEq sourceDecl.uvars []
        (((compilationRestoration sourceDecl auxiliaries).interpretation
          E.lowered.signature.params).expr lc.type) restored (.sort u) := by
    intro lc hlc restored hr
    obtain ⟨hu, u, hwf⟩ := hlcWF lc hlc
    have H := ShT.isDefEq .any hwf trivial
    simp only [List.map_nil] at H
    rw [hu] at H
    exact ⟨_, A.expr_simAt henvTypes.ordered hβT (Γ := []) trivial
      (Restoration.projNamesFixed_of_avoid (HprojNamesCtor lc hlc)) hr _ H⟩
  have Hes' : ∀ e ∈ E.lowered.constructors.declared.eliminators,
      ((compilationRestoration sourceDecl auxiliaries).interpretation
        E.lowered.signature.params).EliminatorClause envS envS.TypedCtx e.1 e.2 :=
    fun e he => let ⟨_, _, R⟩ := Hes e he; R.clause hSwf.ordered
  refine (((ShS.addConstVals hcore.ctorsAdded ?_).weaken fun _ => trivial).addEliminators
    Hes').addProjections Hproj
  intro lc hlc
  obtain ⟨t, ht, hlct⟩ := List.mem_flatMap.mp hlc
  rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types] at ht
  rcases List.mem_append.mp ht with hprim | hauxT
  · -- a source constructor: kept, with the source constructor type
    have Hboth : List.Forall₂ (fun st lt : VInductiveType => List.Forall₂
        (fun sc lc : VConstVal => lc.name = sc.name ∧ ∃ restored,
          (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
          envTypes.SimAt sourceDecl.uvars [] restored sc.type) st.ctors lt.ctors)
        sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length) :=
      Lean4Lean.List.Forall₂.imp (fun st lt h =>
          Lean4Lean.List.Forall₂.imp (fun _ _ h => h)
            (Lean4Lean.List.Forall₂.and h.1 (Lean4Lean.List.Forall₂.flip
              (R := fun sc lc : VConstVal => ∃ restored,
                (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
                envTypes.SimAt sourceDecl.uvars [] restored sc.type) h.2)))
        (Lean4Lean.List.Forall₂.and hnames (Lean4Lean.List.Forall₂.flip
          (R := fun st lt : VInductiveType => List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
            envTypes.SimAt sourceDecl.uvars [] restored sc.type) lt.ctors st.ctors) Hlowered))
    obtain ⟨st, hst, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hboth t hprim
    obtain ⟨sc, hsc, hscName, restored, hr, hsimS⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r hrel lc hlct
    have hn : lc.name ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames :=
      not_restorable_of_take hnodup hheadNames hauxNames
        (mem_familyNames.mpr ⟨t, hprim, .inr ⟨lc, hlct, rfl⟩⟩)
    have hρ := Restoration.lambdaReplacement_eq_none_of_not_restorable
      (domains := fun _ => E.lowered.signature.params) hn
    refine ⟨fun t' ht' => (by rw [Restoration.interpretation_consts, hρ] at ht'; cases ht'),
      fun _ => ?_⟩
    have hscUvars : sc.uvars = lc.uvars := by
      rw [(hlcWF lc hlc).1]
      have Hsource := E.sourceCore.core
      rw [E.sourceCoreDecl_eq] at Hsource
      obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hsource.types st hst
      obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
      rw [hC.uvars, Hsource.uvars]
    obtain ⟨u, hdef⟩ := hsim lc hlc restored hr
    have hdef' := hsimS _ hdef.hasType.2
    have hchain : envTypes.IsDefEq sourceDecl.uvars [] _ sc.type (.sort u) := hdef.trans hdef'
    refine ⟨sc.toVConstant, ?_, hscUvars, u, ?_⟩
    · rw [Restoration.interpretation_rename, Restoration.renaming_eq_self hn, hscName]
      exact hctorsS sc (List.mem_flatMap.mpr ⟨st, hst, hsc⟩)
    · rw [(hlcWF lc hlc).1]
      exact (hchain.symm).mono hle
  · -- an auxiliary constructor: replaced by its restoration lambda
    have hmem : lc.name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
        (·.auxiliary) := by
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, hauxT, .inr ⟨lc, hlct, rfl⟩⟩
    obtain ⟨hd, hf, hdmem, hdaux⟩ := Restoration.find?_of_mem_heads hmem
    refine ⟨fun t' ht' => ?_, fun hnone => ?_⟩
    · simp only [Restoration.interpretation_consts, Restoration.lambdaReplacement, hf,
        Option.map_some, Option.some.injEq] at ht'
      subst ht'
      obtain ⟨restored, hr, htyped⟩ := HauxCtor t hauxT lc hlct hd hdmem hdaux
      obtain ⟨u, hdef⟩ := hsim lc hlc restored hr
      rw [(hlcWF lc hlc).1]
      exact (VEnv.IsDefEq.defeqDF hdef.symm htyped).mono hle
    · simp [Restoration.lambdaReplacement, hf] at hnone

/-- **The recursor stage**: extending the soundness of the restoration interpretation along an
installation of recursors, each kept under its restored name with its restored type, which is
installed in `envS`. -/
theorem Restoration.interpretation_ofAddConstants_recursors
    {r : Restoration} {P : List VExpr} {envS : VEnv} (hSwf : envS.WF)
    (hnp : ∀ h ∈ r.heads, h.nparams = P.length)
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment} {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (S : (r.interpretation P).Sound envS venv envS.TypedCtx)
    (hrecs : ∀ v ∈ entries.map Prod.snd,
      r.heads.find? (fun h => h.auxiliary == v.name) = none ∧
      v.type.projNamesAvoid r.restorableNames = true ∧
      ∃ w, r.recursor v = some w ∧ envS.constants w.name = some w.toVConstant) :
    (r.interpretation P).Sound envS outVEnv envS.TypedCtx := by
  induction H with
  | nil => exact S
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    rename_i cinfo value venvNext rest outE outV envHead Htail
    apply ih
    · refine S.addConst hadd ⟨?_, ?_⟩
      · obtain ⟨hfind, -, -⟩ := hrecs value (by simp)
        intro t ht
        rw [htr.2] at ht
        simp [Restoration.interpretation_consts, Restoration.lambdaReplacement, hfind] at ht
      · intro _
        obtain ⟨hfind, hproj, w, hw, hwS⟩ := hrecs value (by simp)
        simp only [Restoration.recursor, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hw
        obtain ⟨rt, hrt, rfl⟩ := hw
        obtain ⟨u, hu⟩ := hwf
        have H1 := S.isDefEq (.typed S.ordered) hu trivial
        simp only [List.map_nil, VEnv.Interpretation.expr] at H1
        have H2 := (Restoration.interpretation_agrees hnp).expr_simAt S.ordered
          hSwf.betaSubjectReduction (Γ := []) trivial
          (Restoration.projNamesFixed_of_avoid hproj) hrt _ H1
        refine ⟨{ uvars := value.uvars, type := rt }, ?_, rfl, u, H2.symm⟩
        rw [htr.2, Restoration.interpretation_rename, Restoration.renaming_of_find_none hfind]
        exact hwS
    · exact fun v hv => hrecs v (by simp only [List.map_cons, List.mem_cons]; exact .inr hv)

/-- The facts used by `restoredEquationsWF_of_substitutionPremises`, for a restoration table
`auxiliaries` and a restored block base `B` (see the module documentation;
proved for the run by `NestedRun.restoredEquationGaps`). -/
structure RestorationSubstitutionPremises
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (B : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (auxiliaries : List ContainerSpecialization) : Prop where
  /-- Projection names of the base eliminator schemas avoid the restorable
  names. -/
  eliminatorProjNames : EliminatorProjNamesAvoid
    (ves.venv (if isUnsafe then .unsafe else .safe))
    (compilationRestoration sourceDecl auxiliaries).restorableNames
  /-- Projection names of the lowered constructor types avoid the restorable
  names. -/
  constructorProjNames : ∀ lc ∈ E.lowered.loweredDecl.constructorConstants,
    lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
      true
  /-- Projection names of the generated recursor types avoid the restorable
  names. -/
  recursorProjNames :
    ∀ owner : Fin E.lowered.recursors.generationSignature.families.size,
      (E.lowered.recursors.canonicalGeneration.recursorType owner).projNamesAvoid
        (compilationRestoration sourceDecl auxiliaries).restorableNames = true
  /-- Projection names of the generated equations avoid the restorable names. -/
  equationProjNames :
    ∀ k : Fin E.lowered.recursors.generationSignature.constructors.size,
      (E.lowered.recursors.canonicalGeneration.equation k).lhs.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
      (E.lowered.recursors.canonicalGeneration.equation k).rhs.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
      (E.lowered.recursors.canonicalGeneration.equation k).type.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true
  /-- The restoration lambda `λ params, J.c levels args` of every auxiliary
  constructor head has the restored type of the lowered auxiliary
  constructor. -/
  auxiliaryConstructors : ∀ envTypes : VEnv,
    (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes →
    ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.auxiliary = lc.name →
        ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
            some restored ∧
          envTypes.HasType sourceDecl.uvars []
            (VExpr.wrapLams E.lowered.signature.params
              (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored
  /-- The projection rules of the lowered declaration's projections
  hold after interpretation in `B.recursorVEnv`, in well-formed contexts. -/
  projections : ∀ entry ∈ E.lowered.loweredDecl.projectionEntries,
    ((compilationRestoration sourceDecl auxiliaries).interpretation
      E.lowered.signature.params).ProjectionClause B.recursorVEnv B.recursorVEnv.TypedCtx
      entry.typeName entry.info

/-- **The case eliminator of the lowered recursor-checking environment is matched by the
restored schema of a restored block base** (`VEnv.RestoredEliminator`): the base registers
the schema with the same key and signature, restored by a specialisation list whose restoration tables are those of the run,
so its restoration agrees with the restoration interpretation of every restoration table of
the run (`RestorationTablesAgree.find_eq`). The lowered schema projects only out of base
structures (its certificate `EliminatorsWF`), which are not restorable, and the
restoration succeeds on its generic equations because it succeeds on its generic case type, the
registered source case type. -/
theorem NestedRun.restoredEliminators
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
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
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hnp : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.nparams = E.lowered.signature.params.length)
    (B : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.lowered = E.lowered) (hSwf : B.recursorVEnv.WF) :
    ∀ e ∈ E.lowered.constructors.declared.eliminators, ∃ families r,
      VEnv.RestoredEliminator B.recursorVEnv
        ((compilationRestoration sourceDecl auxiliaries).interpretation
          E.lowered.signature.params) e.1 e.2 families r := by
  obtain ⟨key, sL, auxC, hcompEl, hesEq, DC⟩ := B.eliminatorsRestored
  rw [hB] at hcompEl
  intro e he
  change e ∈ E.lowered.constructors.toConstructorCheck.eliminators at he
  rw [hcompEl, List.mem_singleton] at he
  subst he
  -- the lowered schema projects only out of base structures
  have Havoid :
      (∀ owner type, (CaseSchema.ofCompilation E.lowered.loweredDecl sL []).genericType
          owner = some type →
        type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true) ∧
      (∀ owner rules, (CaseSchema.ofCompilation E.lowered.loweredDecl sL []).genericEquations
          key owner = some rules → ∀ df ∈ rules,
        df.lhs.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true ∧
        df.rhs.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true ∧
        df.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true) := by
    obtain ⟨envTypes', envCtors', ht', hc', Hel⟩ :=
      E.lowered.constructors.toConstructorCheck.eliminatorsWF
    rcases Hel with ⟨-, hE⟩ | ⟨key', schema', hE', -, hprojs⟩
    · simp [VInductDecl.caseBlock, hcompEl] at hE
    · simp only [VInductDecl.caseBlock, hcompEl, List.cons.injEq, Prod.mk.injEq,
        and_true] at hE'
      obtain ⟨rfl, hs⟩ := hE'
      rw [← hs] at hprojs
      have hnot : ∀ S, (∃ info, envCtors'.projections S info) →
          S ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
        rintro S ⟨info, hinfo⟩
        rw [VEnv.addConstVals_projections_eq hc', VEnv.addConstVals_projections_eq ht',
          E.lowered_initialEnv] at hinfo
        exact E.baseProjection_not_restorable wf hadded Haux Hexpansion hnodup hinfo
      refine ⟨fun owner type h => (hprojs.1 owner type h).projNamesAvoid hnot,
        fun owner rules h df hdf => ?_⟩
      obtain ⟨hl, hr, ht⟩ := hprojs.2 owner rules h df hdf
      exact ⟨hl.projNamesAvoid hnot, hr.projNamesAvoid hnot, ht.projNamesAvoid hnot⟩
  -- the restored schema is registered in the final environment
  have hreg : B.recursorVEnv.eliminators key
      (CaseSchema.ofCompilation sourceDecl sL auxC) := by
    have hle := B.install.recursorsAdded.le
    refine hle.eliminators ?_
    rw [VEnv.addProjections_eliminators, hesEq]
    exact VEnv.addEliminators_iff.mpr (.inl (List.mem_singleton_self _))
  have A := (Restoration.interpretation_agrees hnp).congr (D.find_eq DC)
    (fun n => (D.recursorName n).trans (DC.recursorName n).symm)
    (fun n hn => Restoration.renaming_eq_self fun h => hn (DC.restorable_transfer D h))
  refine ⟨sourceDecl.types.map fun t : VInductiveType => t.name,
    compilationRestoration sourceDecl auxC,
    VEnv.RestoredEliminator.of_wf hSwf rfl hreg A
      (fun owner type h => Restoration.projNamesFixed_of_avoid (Havoid.1 owner type h)) ?_⟩
  intro owner rules h df hdf
  obtain ⟨hl, hr, ht⟩ := Havoid.2 owner rules h df hdf
  refine ⟨Restoration.projNamesFixed_of_avoid hl, Restoration.projNamesFixed_of_avoid hr,
    Restoration.projNamesFixed_of_avoid ht, ?_⟩
  refine CaseSchema.genericEquations_restorable rfl key owner (fun type htype => ?_) h df hdf
  obtain ⟨type', h', -⟩ := EnvTables.VEnv.WF.eliminator_genericType_closed hSwf hreg owner
  have := CaseSchema.genericType_withRestoration (schema :=
    CaseSchema.ofCompilation E.lowered.loweredDecl sL []) rfl htype
    (sourceDecl.types.map fun t : VInductiveType => t.name)
    (compilationRestoration sourceDecl auxC)
  change (CaseSchema.ofCompilation sourceDecl sL auxC).genericType owner = _ at this
  rw [h'] at this
  rw [← this]
  rfl

/-- **The restoration substitution of a nested run**, from the
lowered recursor environment into the recursor environment of a restored
block base, for the restoration table of
`restorationTablesRestoringAll`, modulo `RestorationSubstitutionPremises`. -/
theorem NestedRun.restoredEquationSubstitution
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
    (henvTypes : envTypes.WF)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hrestoring : List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length))
    (B : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.lowered = E.lowered)
    (hV : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv)
    (G : RestorationSubstitutionPremises E B auxiliaries) :
    (compilationRestoration sourceDecl auxiliaries).Substitution B.recursorVEnv
      E.lowered.recursors.outVEnv
      ((compilationRestoration sourceDecl auxiliaries).interpretation
        E.lowered.signature.params) := by
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, hauxNames, hheadNames', -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨-, -, hnp, -, -, -, -⟩ := E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hSwf : B.recursorVEnv.WF := hV.tr.wf
  -- the source header environment of the shape
  have hvenvTypes : B.install.venvTypes = envTypes := by
    have h1 := B.install.abstract_types
    rw [B.typeValues, hadded] at h1
    exact (Option.some.inj h1).symm
  have hctorsAdded := B.install.abstract_ctors
  rw [B.constructorValues, hvenvTypes] at hctorsAdded
  have hleCtors : B.install.venvCtors ≤ B.recursorVEnv :=
    VEnv.addEliminators_addProjections_le.trans B.install.recursorsAdded.le
  have hle : envTypes ≤ B.recursorVEnv :=
    (VEnv.addConstVals_le hctorsAdded).trans hleCtors
  have hctorsS : ∀ sc ∈ sourceDecl.constructorConstants,
      B.recursorVEnv.constants sc.name = some sc.toVConstant :=
    fun sc hsc => hleCtors.constants (VEnv.addConstVals_get hctorsAdded hsc)
  -- constructor names of the source prefix
  have hnames : List.Forall₂ (fun st lt : VInductiveType => List.Forall₂
        (fun sc lc : VConstVal => lc.name = sc.name) st.ctors lt.ctors)
      sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length) := by
    have h := B.formationAssembly.types
    rw [B.formationExpanded, hB] at h
    have hlen : sourceDecl.types.length =
        (E.lowered.loweredDecl.types.take sourceDecl.types.length).length := by
      have := Lean4Lean.List.Forall₂.length_eq h
      simp only [List.length_append] at this
      simp only [List.length_take]
      omega
    rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types] at h
    have h1 := ((Lean4Lean.List.Forall₂.append_of_left hlen).mp h).1
    exact Lean4Lean.List.Forall₂.imp (fun _ _ hx =>
      Lean4Lean.List.Forall₂.imp (fun _ _ hc => hc.name) hx.constructors) h1
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames'
  have Hlowered := E.loweredConstructors_of_lowering hadded henvTypes hfreshAll Hrestoring
    hlevels
  have S₁ := E.constructorInterpretationSound wf hadded henvTypes Haux Hexpansion hnodup
    hauxNames hSwf hle G.eliminatorProjNames hctorsS hnames Hlowered G.constructorProjNames
    (G.auxiliaryConstructors envTypes hadded) G.projections
    (E.restoredEliminators wf hadded Haux Hexpansion hnodup D hnp B hB hSwf)
  -- the restored recursors
  have hrestoredRecs := E.restoredRecursorEntries_of_paramUniform B hB wf Hsources hadded Haux
    Hexpansion hnodup hparamsSize D hscoped
  have hrecAdded := B.install.recursorsAdded.abstract
  rw [B.recursorValues] at hrecAdded
  have hrecs : ∀ v ∈ E.lowered.recursors.entries.map Prod.snd,
      (compilationRestoration sourceDecl auxiliaries).heads.find?
          (fun h => h.auxiliary == v.name) = none ∧
      v.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
        true ∧
      ∃ w, (compilationRestoration sourceDecl auxiliaries).recursor v = some w ∧
        B.recursorVEnv.constants w.name = some w.toVConstant := by
    intro v hv
    have hcanon := E.lowered.recursors.recursors
    change E.lowered.recursors.entries.map Prod.snd = _ at hcanon
    rw [hcanon] at hv
    simp only [InductiveSignature.Instance.recursors, List.mem_map, List.mem_finRange,
      true_and] at hv
    obtain ⟨owner, rfl⟩ := hv
    obtain ⟨w, hw, hrw⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrestoredRecs owner
      (List.mem_finRange owner)
    refine ⟨E.recursorName_not_head Haux Hexpansion hnodup owner,
      G.recursorProjNames owner, w, hrw.1, VEnv.addConstVals_get hrecAdded hw⟩
  rw [← E.lowered.constructors.declared.contextVEnv] at S₁
  have S₂ := Restoration.interpretation_ofAddConstants_recursors hSwf hnp
    E.lowered.recursors.installed S₁ hrecs
  exact ⟨S₂, Restoration.interpretation_agrees hnp⟩

/-- **`HrestoredWF` of `NestedRun.hruleShape_of_base`**: every
restored generated equation is well formed in the recursor environment
of a restored block base in which the stripped output environment is valid,
modulo `RestorationSubstitutionPremises` (the hypothesis-free form is
`NestedRun.hrestoredWF_of`,
`Nested/Restoration/AuxiliaryProjections.lean`).

The generated equation is well formed in the lowered recursor environment
(`loweredEquationWF`); the restoration substitution
of the run
(`restoredEquationSubstitution`, for the table of
`restorationTablesRestoringAll`, whose restoration agrees with that of every
table by `RestorationTablesAgree.expr_eq`) transports it to the recursor
environment of the base, where beta subject reduction holds by well-formedness. -/
theorem NestedRun.restoredEquationsWF_of_substitutionPremises
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (G : ∀ auxiliaries : List ContainerSpecialization,
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
        RestorationSubstitutionPremises E B auxiliaries) :
    ∀ auxiliaries : List ContainerSpecialization,
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
          rule.WF B.recursorVEnv := by
  intro auxiliaries D B hB hV k rule hrule
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, hparamsSize, D',
      Hrestoring, -⟩
  have G' := G aux' D' B hB hV
  have S := E.restoredEquationSubstitution wf Hsources hadded henvTypes Haux Hexpansion
    hparamsSize D' Hrestoring B hB hV G'
  have hrule' : (compilationRestoration sourceDecl aux').equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule := by
    simp only [Restoration.equation, D.expr_eq D'] at hrule ⊢
    exact hrule
  obtain ⟨hl, hr, ht⟩ := G'.equationProjNames k
  exact Restoration.equation_wf S hV.tr.wf.betaSubjectReduction (E.loweredEquationWF k)
    (Restoration.projNamesFixed_of_avoid hl) (Restoration.projNamesFixed_of_avoid hr)
    (Restoration.projNamesFixed_of_avoid ht) hrule'

end VerifyInductive
end Lean4Lean
