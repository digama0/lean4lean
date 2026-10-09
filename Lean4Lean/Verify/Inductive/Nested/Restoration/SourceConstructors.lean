import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Verify.Inductive.Nested.CaseEliminators.Avoidance
import Lean4Lean.Std.List

/-! Restoration of the constructor types of the source families of a
validated nested run (the `sourceConstructors` field of
`NestedCompilationRestorationFacts`).

The lowered header environment `envL` is the source header environment
`envTypes` extended by the opaque auxiliary family headers. The restoration
interpretation keeping projection owners (`Restoration.constInterpretation`), which
interprets each restoration head by the lambda abstraction of its container
specialization over the common parameters, is a restoration substitution from
`envL` to `envTypes` (`Restoration.constInterpretation_substitution`; its clauses hold
in every context). With beta subject reduction of the well-formed `envTypes` it
transports the defeq of `Models.constructors` between a normalized and a lowered
constructor type to the source environment (`RestoresType.of_models_constructor`).

The facts not derived from the run are collected in
`LoweredConstructorsRestore`. The specialization list and the freshness
of its restoration names are hypotheses here; `Restoration/CompilationDataConstructors.lean`
supplies them from `NestedRun.restorationTablesRestoring` and
`NestedRun.restorableNames_fresh`.
-/

namespace Lean4Lean

open InductiveSignature

namespace InductiveSignature

/-! ### The lambda replacement is a restoration substitution -/

/-- Lookups of the extended header environment: either a lookup of the
source header environment or one of the appended headers. -/
theorem lookup_of_addConstVals_append {env envTypes envL : VEnv}
    {sourceTC auxTC : List VConstVal}
    (htypes : env.addConstVals sourceTC = some envTypes)
    (hlowered : env.addConstVals (sourceTC ++ auxTC) = some envL)
    (hc : envL.constants c = some ci) :
    envTypes.constants c = some ci ∨
      ∃ entry ∈ auxTC, entry.name = c ∧ entry.toVConstant = ci := by
  rcases VEnv.addConstVals_lookup_cases hlowered hc with hbase | ⟨entry, hmem, hname, hval⟩
  · exact .inl ((VEnv.addConstVals_le htypes).constants hbase)
  · rcases List.mem_append.mp hmem with hsrc | haux
    · left
      rw [← hname, ← hval]
      exact VEnv.addConstVals_get htypes hsrc
    · exact .inr ⟨entry, haux, hname, hval⟩

theorem addConstVals_append_defeqs {env envTypes envL : VEnv}
    {sourceTC auxTC : List VConstVal}
    (htypes : env.addConstVals sourceTC = some envTypes)
    (hlowered : env.addConstVals (sourceTC ++ auxTC) = some envL) :
    envL.defeqs = envTypes.defeqs ∧ envL.eliminators = envTypes.eliminators ∧
      envL.projections = envTypes.projections :=
  ⟨(VEnv.addConstVals_defeqs hlowered).trans (VEnv.addConstVals_defeqs htypes).symm,
    (VEnv.addConstVals_eliminators hlowered).trans
      (VEnv.addConstVals_eliminators htypes).symm,
    (VEnv.addConstVals_projections hlowered).trans
      (VEnv.addConstVals_projections htypes).symm⟩

/-- The restoration interpretation keeping projection owners, over a common closed parameter
telescope `P`, is a restoration substitution from the extended header environment to the source
header environment. Its clauses hold in every context. -/
theorem Restoration.constInterpretation_substitution {env envTypes envL : VEnv}
    {sourceTC auxTC : List VConstVal} {r : Restoration} {P : List VExpr}
    (henvTypes : envTypes.WF)
    (htypes : env.addConstVals sourceTC = some envTypes)
    (hlowered : env.addConstVals (sourceTC ++ auxTC) = some envL)
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length)
    (hargs : ∀ h ∈ r.heads, ∀ arg ∈ h.arguments, arg.ClosedN h.nparams)
    (hPclosed : ∀ i (hi : i < P.length), P[i].ClosedN i)
    (hfresh : ∀ name ∈ r.restorableNames, envTypes.constants name = none)
    (hauxHeads : ∀ entry ∈ auxTC, entry.name ∈ r.heads.map (·.auxiliary))
    (hreplaced : ∀ h ∈ r.heads, ∀ ci, envL.constants h.auxiliary = some ci →
      ci.type.containsAnyConst r.restorableNames = false ∧
      envTypes.HasType ci.uvars []
        (VExpr.wrapLams P (VExpr.mkApps (.const h.target h.levels) h.arguments)) ci.type)
    (helim : EliminatorsAvoidConsts envTypes r.restorableNames) :
    r.Substitution envTypes envL (r.constInterpretation P) := by
  have hordered := henvTypes.ordered
  have hon := hordered.onTypes_noFreshConsts hfresh
  have hfix : ∀ {e : VExpr}, e.containsAnyConst r.restorableNames = false →
      (r.constInterpretation P).expr e = e :=
    Restoration.constInterpretation_expr_eq_self
  have hnotR : ∀ {c ci}, envTypes.constants c = some ci → c ∉ r.restorableNames := by
    intro c ci hci hmem
    rw [hfresh c hmem] at hci
    cases hci
  have hfixConst : ∀ {c ci}, envTypes.constants c = some ci →
      (r.constInterpretation P).consts c = none ∧ (r.constInterpretation P).rename c = c ∧
      (r.constInterpretation P).expr ci.type = ci.type := by
    intro c ci hci
    obtain ⟨_, h, _⟩ := hon.1 hci
    exact ⟨Restoration.lambdaReplacement_eq_none_of_not_restorable (hnotR hci),
      Restoration.renaming_eq_self (hnotR hci), hfix h⟩
  have hfind : ∀ {c h}, r.heads.find? (fun h => h.auxiliary == c) = some h →
      h ∈ r.heads ∧ h.auxiliary = c := by
    intro c h hf
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  have hI := Restoration.interpretation_closed hnparams hargs hPclosed
  have ⟨hdf, hel, hpr⟩ := addConstVals_append_defeqs htypes hlowered
  have S : (r.constInterpretation P).Sound envTypes envL fun _ _ => True := {
    closed := hI
    ordered := hordered
    constants := ?_
    defeqs := ?_
    eliminators := ?_
    projections := ?_ }
  · exact ⟨S.weaken fun _ => trivial, Restoration.constInterpretation_agrees hnparams⟩
  · intro c ci hci
    refine ⟨fun t hρ => ?_, fun hρ => ?_⟩
    · change r.lambdaReplacement (fun _ => P) c = some t at hρ
      unfold Restoration.lambdaReplacement at hρ
      cases hf : r.heads.find? (fun h => h.auxiliary == c) with
      | none => simp [hf] at hρ
      | some h =>
        simp only [hf, Option.map_some, Option.some.injEq] at hρ
        subst hρ
        obtain ⟨hmem, rfl⟩ := hfind hf
        obtain ⟨hfree, htyped⟩ := hreplaced h hmem ci hci
        rw [hfix hfree]
        exact htyped
    · rcases lookup_of_addConstVals_append htypes hlowered hci with h | ⟨entry, hmem, rfl, -⟩
      · obtain ⟨-, hr, hty⟩ := hfixConst h
        obtain ⟨u, hu⟩ := hordered.constWF h
        refine ⟨ci, by rw [hr]; exact h, rfl, u, ?_⟩
        rw [hty]
        exact hu
      · exfalso
        obtain ⟨h, hh, heq⟩ := List.mem_map.mp (hauxHeads entry hmem)
        have hsome : (r.heads.find? (fun h => h.auxiliary == entry.name)).isSome :=
          List.find?_isSome.mpr ⟨h, hh, by simp [heq]⟩
        change r.lambdaReplacement (fun _ => P) entry.name = none at hρ
        unfold Restoration.lambdaReplacement at hρ
        cases hf : r.heads.find? (fun h => h.auxiliary == entry.name) with
        | none => rw [hf] at hsome; cases hsome
        | some _ => rw [hf] at hρ; cases hρ
  · intro df hdf'
    rw [hdf] at hdf'
    obtain ⟨h1, h2⟩ := hon.2 hdf'
    exact VEnv.Interpretation.DefEqClause.of_rule hdf' rfl (hfix h1.1).symm (hfix h2.1).symm
      (hfix h1.2).symm
  · intro block schema hs
    rw [hel] at hs
    obtain ⟨ht, hrules⟩ := helim block schema hs
    have hfix' : ∀ {e : VExpr}, e.mentionsAnyConst r.restorableNames = false →
        (r.constInterpretation P).expr e = e := fun h =>
      VEnv.Interpretation.expr_eq_self_of_mentions
        (fun _ hc => Restoration.lambdaReplacement_eq_none_of_not_restorable hc)
        (fun _ hc => Restoration.renaming_eq_self hc) (fun _ _ => rfl) h
        (VExpr.projNamesFixed_id _)
    refine VEnv.Interpretation.EliminatorClause.of_fixed hs (fun _ => rfl)
      (fun owner type h => hfix' (ht owner type h)) ?_
    intro owner rules h df hdf
    obtain ⟨a, b, c⟩ := hrules owner rules h df hdf
    exact ⟨hfix' a, hfix' b, hfix' c⟩
  · intro typeName info hp
    rw [hpr] at hp
    obtain ⟨_, htn⟩ := hordered.projectionConstant hp
    have hctor := hordered.projectionConstructor hp
    obtain ⟨h1, h2, -⟩ := hfixConst htn
    obtain ⟨h3, h4, h5⟩ := hfixConst hctor
    exact VEnv.Interpretation.ProjectionClause.of_fixed hI
      (Restoration.interpretation_preservesTelescopes r P) hp h1 h2 rfl h3 h4 h5

/-! ### Constructor correspondence from a restoration substitution -/

/-- Split a constructor-list correspondence along families of equal
constructor counts. -/
theorem forall₂_ctors_split {R : VConstVal → VConstVal → Prop} :
    ∀ {A B : List VInductiveType},
      List.Forall₂ (fun a b => a.ctors.length = b.ctors.length) A B →
      List.Forall₂ R (A.flatMap (·.ctors)) (B.flatMap (·.ctors)) →
      List.Forall₂ (fun a b => List.Forall₂ R a.ctors b.ctors) A B
  | _, _, .nil, _ => .nil
  | _, _, .cons hlen hrest, H => by
    simp only [List.flatMap_cons] at H
    obtain ⟨h1, h2⟩ := (Lean4Lean.List.Forall₂.append_of_left hlen).mp H
    exact .cons h1 (forall₂_ctors_split hrest h2)

theorem forall₂_take {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.take k) (r.take k)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons]
    exact .cons h (forall₂_take t k)

/-- The constructor correspondence of the source families, from a restoration
substitution, the defeq of normalized and lowered constructor types in the
lowered header environment, the restoration of the lowered constructor types
to the source ones, and totality of restoration on the normalized types. -/
theorem sourceConstructors_of_substitution {envS envL : VEnv} {r : Restoration}
    {I : VEnv.Interpretation} {U : Nat}
    (S : r.Substitution envS envL I) (hfix : ∀ e : VExpr, e.ProjNamesFixed I.projOwner)
    (hβ : envS.BetaSubjectReduction U)
    {normalized lowered source : List VInductiveType}
    (Hdefeq : List.Forall₂ (fun n l => List.Forall₂
      (fun nc lc : VConstVal => envL.IsDefEqU U [] nc.type lc.type) n.ctors l.ctors)
      normalized lowered)
    (Hlowered : List.Forall₂ (fun l src => List.Forall₂
      (fun lc sc : VConstVal => ∃ restored, r.expr lc.type = some restored ∧
        envS.SimAt U [] restored sc.type) l.ctors src.ctors) lowered source)
    (Htotal : ∀ n ∈ normalized, ∀ c ∈ n.ctors, ∃ restored, r.expr c.type = some restored) :
    List.Forall₂ (fun n src => List.Forall₂
      (fun nc sc : VConstVal => RestoresType r envS U nc.type sc.type) n.ctors src.ctors)
      normalized source := by
  refine Lean4Lean.List.Forall₂.trans (fun n l src hnl hls => ?_)
    (Lean4Lean.List.Forall₂.and_mem Hdefeq) Hlowered
  obtain ⟨hnl, hn, -⟩ := hnl
  refine Lean4Lean.List.Forall₂.trans (fun nc lc sc hd hl => ?_)
    (Lean4Lean.List.Forall₂.and_mem hnl) hls
  obtain ⟨hd, hnc, -⟩ := hd
  obtain ⟨restored, hr, hsim⟩ := hl
  exact RestoresType.of_models_constructor S hβ hd hr hsim (Htotal n hn nc hnc) (hfix _)
    (hfix _)

end InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- The facts used here that are not derived from a validated nested run.

* `loweredConstructors`: each lowered constructor type of a source family
  restores to (a term defeq at every type to) the source constructor type.
  The abstract expansion relation `NestedOccurrenceReplacementAbs` records the
  leaf's container, levels and arguments only up to definitional equality of
  the auxiliary family's type, not syntactically as the specialization of
  the auxiliary, so it does not determine the restoration of a leaf.
* `normalizedTotal`: restoration is defined on every normalized constructor
  type of a source family, i.e. every auxiliary head in the unannotated field
  domains is applied to at least the parameters at the source universe
  arity. -/
structure LoweredConstructorsRestore (envTypes : VEnv)
    (sourceDecl loweredDecl : VInductDecl) (s : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) : Prop where
  loweredConstructors : List.Forall₂ (fun lowered source : VInductiveType =>
      List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
          (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
          envTypes.SimAt sourceDecl.uvars [] restored sc.type)
        lowered.ctors source.ctors)
    (loweredDecl.types.take sourceDecl.types.length) sourceDecl.types
  normalizedTotal : ∀ normalized ∈ s.declaration.types.take sourceDecl.types.length,
    ∀ ctor ∈ normalized.ctors, ∃ restored,
      (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored

theorem mem_familyNames {types : List VInductiveType} {name : Name} :
    name ∈ familyNames types ↔ ∃ t ∈ types, name = t.name ∨ ∃ c ∈ t.ctors, name = c.name := by
  simp only [familyNames, List.mem_flatMap, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact ⟨t, ht, .inl h⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact ⟨t, ht, .inl h⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩

/-- **Restoration of the source constructor types of a validated nested run**
(the `sourceConstructors` field of `NestedCompilationRestorationFacts`), for any
specialization list generated by lowering whose restoration heads and
recursors are fresh in the source header environment, modulo
`LoweredConstructorsRestore`. The specializations are supplied by the
caller (in `Restoration/CompilationDataConstructors.lean`, by
`NestedRun.restorationTablesRestoring`). -/
theorem NestedRun.sourceConstructors_of_lowering
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
    (hfresh : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
      (·.auxiliary), envTypes.constants name = none)
    (hrecFresh : ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
      envTypes.constants p.1 = none)
    (G : LoweredConstructorsRestore envTypes sourceDecl E.lowered.loweredDecl
      E.lowered.signature auxiliaries) :
    ∀ envTypes', (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes' →
      List.Forall₂ (fun normalized family : VInductiveType =>
          List.Forall₂ (fun normalized ctor : VConstVal =>
            RestoresType (compilationRestoration sourceDecl auxiliaries) envTypes'
              sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (E.lowered.signature.declaration.types.take
          sourceDecl.types.length) sourceDecl.types := by
  intro envTypes' hadded'
  rw [hadded] at hadded'
  cases hadded'
  have hsuffixNodup :
      (familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ++
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map
          (fun t => t.name.str "rec")).Nodup := by
    refine hnodup.sublist (List.Sublist.append ?_ ((List.drop_sublist _ _).map _))
    conv => rhs; rw [← List.take_append_drop sourceDecl.types.length
      E.lowered.loweredDecl.types]
    simp only [familyNames, List.flatMap_append]
    exact List.sublist_append_right _ _
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.lowered.constructors.toConstructorCheck.parameterScope.toCtx.reverse).reverse
      E.lowered.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      OrdinaryConstructorCheck.parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hscoped := auxiliarySpecializations_scoped Haux Hexpansion hsuffixNodup
  -- the base and lowered header environments
  have hinit : E.lowered.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.lowered_initialEnv
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.lowered.loweredDecl.typeConstants =
        some E.lowered.constructors.toConstructorCheck.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.lowered.loweredDecl.typeConstants =
          some E.lowered.constructors.toConstructorCheck.headerVEnv) hinit)
      E.lowered.constructors.toConstructorCheck.core.typesAdded
  have Hsource := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at Hsource
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hprefix : sourceDecl.typeConstants =
      E.lowered.loweredDecl.typeConstants.take sourceDecl.types.length := by
    have h := E.sourceCore.sourceTypeValues
    rw [E.sourceCoreDecl_eq] at h
    rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
  have hloweredSplit : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      (sourceDecl.typeConstants ++
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map
          VInductiveType.toVConstVal) =
        some E.lowered.constructors.toConstructorCheck.headerVEnv := by
    rw [hprefix, VInductDecl.typeConstants, List.map_drop, List.take_append_drop]
    exact hloweredTypes
  have Hmodels : E.lowered.signature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.lowered.loweredDecl := by
    have h := E.lowered.recursorConstruction.generator.models
    change E.lowered.signature.Models E.lowered.initialEnv
      E.lowered.loweredDecl at h
    rwa [hinit] at h
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  -- the common parameter telescope
  have hparams : E.lowered.signature.params =
      E.lowered.constructors.toConstructorCheck.parameterScope.toCtx.reverse :=
    E.lowered.recursorConstruction.generator.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.lowered.signature.params.reverse
      E.lowered.headers.commonParameterContext := by
    rw [hparams]; exact hlink
  have hPclosed : ∀ i (hi : i < E.lowered.signature.params.length),
      E.lowered.signature.params[i].ClosedN i := by
    intro i hi
    simpa using OnCtx.reverse_getElem_closedN henvTypes (Γ := [])
      (by simpa using hP.isType) i hi
  have hordered := henvTypes.ordered
  have hscopedNodup := hscoped.1
  -- the family head of each auxiliary, and its specialization
  have hfamilyHead : ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∃ a ∈ auxiliaries, ∃ g,
        SpecializationGenerates (ves.venv (if isUnsafe then .unsafe else .safe))
          envTypes E.lowered.headers.commonParameterContext sourceDecl a g ∧
        VInductDecl.NestedTypeExpansion (ves.venv (if isUnsafe then .unsafe else .safe))
          sourceDecl (VInductDecl.NestedOccurrenceReplacementAbs
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated) g t := by
    intro t ht
    obtain ⟨g, hg, hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hexpansion t ht
    obtain ⟨a, ha, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
    exact ⟨a, ha, g, hev, hexp⟩
  have hheadsParams : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.nparams = E.lowered.signature.params.length := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hh
    have hn : h.nparams = sourceDecl.nparams := by
      simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
      rcases hh with rfl | ⟨_, _, rfl⟩ <;> rfl
    obtain ⟨g, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    obtain ⟨sourceParams, hlen, hctx, -⟩ := hev.application
    rw [hn, ← hlen]
    have h1 := hctx.length_eq
    have h2 := hP.length_eq
    simp only [List.length_reverse] at h1 h2
    omega
  have hfreshAll : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      envTypes.constants name = none := by
    intro name hname
    rcases List.mem_append.mp hname with h | h
    · exact hfresh name h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact hrecFresh p hp
  have hreplaced : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads, ∀ ci,
      E.lowered.constructors.toConstructorCheck.headerVEnv.constants h.auxiliary = some ci →
      ci.type.containsAnyConst
          (compilationRestoration sourceDecl auxiliaries).restorableNames = false ∧
      envTypes.HasType ci.uvars []
        (VExpr.wrapLams E.lowered.signature.params
          (VExpr.mkApps (.const h.target h.levels) h.arguments)) ci.type := by
    intro h hh ci hci
    rcases lookup_of_addConstVals_append hadded hloweredSplit hci with
      henvT | ⟨entry, hentry, hn, hval⟩
    · rw [hfresh _ (List.mem_map_of_mem hh)] at henvT; cases henvT
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
    obtain ⟨a, ha, g, hev, hexp⟩ := hfamilyHead t ht
    have hfh : InductiveSignature.HeadSpecialization.mk a.auxiliary sourceDecl.uvars
        sourceDecl.nparams a.source.name a.levels a.arguments ∈
        (compilationRestoration sourceDecl auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have heqh := Lean4Lean.List.nodup_map_inj hscopedNodup hh hfh
      (hn.symm.trans (hexp.name.trans hev.auxiliary.symm))
    subst heqh
    subst hval
    obtain ⟨sourceParams, hlen, hctx, honctx, htyping, hgtype, -⟩ := hev.application
    have htype : envTypes.IsDefEqU sourceDecl.uvars [] g.type t.type :=
      hexp.type.mono (VEnv.addConstVals_le hadded)
    obtain ⟨_, htypeD⟩ := htype
    have huvars : t.uvars = sourceDecl.uvars := hexp.uvars.trans hev.generatedUvars
    change t.type.containsAnyConst _ = false ∧
      envTypes.HasType t.uvars [] _ t.type
    rw [huvars]
    refine ⟨(htypeD.noFreshConsts hordered hfreshAll (by intro _ h; simp at h)).2.1, ?_⟩
    have hPS : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
        E.lowered.signature.params.reverse sourceParams.reverse :=
      VEnv.IsDefEqCtx.trans_empty henvTypes hP (hctx.symm hordered)
    have htypingP := htyping.defeqDFC hordered (hPS.symm hordered)
    have hlam : envTypes.HasType sourceDecl.uvars []
        (VExpr.wrapLams E.lowered.signature.params
          (VExpr.mkApps (.const a.source.name a.levels) a.arguments))
        (VExpr.wrapForalls E.lowered.signature.params
          (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments)) :=
      VEnv.HasType.wrapLams (ctx := []) (by simpa using hP.isType) (by simpa using htypingP)
    obtain ⟨u, hu⟩ := htyping.isType hordered honctx
    have hforalls := VExpr.wrapForalls_defeqCtx henvTypes hPS ⟨u, hu⟩ ⟨_, hu⟩
    have hchain : envTypes.IsDefEqU sourceDecl.uvars []
        (VExpr.wrapForalls E.lowered.signature.params
          (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments))
        t.type :=
      VEnv.IsDefEqU.trans henvTypes trivial hforalls
        (VEnv.IsDefEqU.trans henvTypes trivial hgtype.symm ⟨_, htypeD⟩)
    exact hlam.defeqU_r henvTypes trivial hchain
  -- the restoration substitution
  have S := Restoration.constInterpretation_substitution
    (r := compilationRestoration sourceDecl auxiliaries)
    (P := E.lowered.signature.params)
    henvTypes hadded hloweredSplit hheadsParams
    (fun h hh arg harg => (hscoped.2.2.1 h hh).2 arg harg) hPclosed hfreshAll
    (by
      intro entry hentry
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, ht, .inl rfl⟩)
    hreplaced (henvTypes.eliminatorsAvoidConsts hfreshAll)
  -- the lowered defeq of normalized and lowered constructor types
  have hloweredUvars : E.lowered.loweredDecl.uvars = sourceDecl.uvars := by
    have h1 := E.lowered.constructors.toConstructorCheck.core.uvars
    have h2 := E.sourceCore.core.uvars
    rw [E.sourceCoreDecl_eq] at h2
    rw [h1, h2, E.lowered_c, E.context_lparams]
  obtain ⟨envT, henvT, Hctors⟩ := Hmodels.constructors
  rw [hloweredTypes] at henvT
  cases henvT
  have Hlengths : List.Forall₂ (fun a b : VInductiveType => a.ctors.length = b.ctors.length)
      E.lowered.signature.declaration.types E.lowered.loweredDecl.types :=
    Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      simpa using congrArg List.length h.2.2.2.2) Hmodels.families
  have Hdefeq := forall₂_take (forall₂_ctors_split (R := fun nc lc : VConstVal =>
      E.lowered.constructors.toConstructorCheck.headerVEnv.IsDefEqU sourceDecl.uvars []
        nc.type lc.type) Hlengths
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      rw [hloweredUvars] at h
      exact h.2.2) Hctors)) sourceDecl.types.length
  exact sourceConstructors_of_substitution S VExpr.projNamesFixed_id
    henvTypes.betaSubjectReduction Hdefeq G.loweredConstructors G.normalizedTotal

end VerifyInductive

end Lean4Lean
