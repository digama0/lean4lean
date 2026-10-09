import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryHeaders
import Lean4Lean.Verify.Inductive.Nested.Lowering.Levels
import Lean4Lean.Std.List

/-! Restoration of the auxiliary constructor types of a validated nested run
(the constructor-type conjunct of the `auxiliaryFamilies` field of
`NestedCompilationRestorationFacts`).

Every lowered auxiliary family expands the generated family of its container
specialization by restoring leaves
(`NestedRun.restorationTablesRestoringAll`), so restoration
maps each lowered auxiliary constructor type syntactically to the generated
constructor type. The generated constructor type is definitionally the
container's constructor type instantiated at the specialization arguments,
under a parameter telescope definitionally equal to the common one; the
constructor of the direct family is the same instantiation under the
signature's parameters. The restoration substitution of
`Restoration/SourceConstructors.lean` transports the defeq of `Models.constructors`
between normalized and lowered constructor types to the source header
environment (`sourceConstructors_of_substitution`).
-/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-! ### Direct constructors -/

/-- Replace a parameter telescope by a definitionally equal one, for a term
definitionally equal to the telescope. -/
theorem VEnv.IsDefEqU.wrapForalls_params {env : VEnv} {U : Nat} (henv : env.WF)
    {sp params : List VExpr} {X R : VExpr}
    (hctx : VEnv.IsDefEqCtx env U [] params.reverse sp.reverse)
    (h : env.IsDefEqU U [] X (VExpr.wrapForalls sp R)) :
    env.IsDefEqU U [] X (VExpr.wrapForalls params R) := by
  cases sp with
  | nil =>
    have hlen := hctx.length_eq
    simp only [List.length_reverse, List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    exact h
  | cons d rest =>
    obtain ⟨T, hT⟩ := h
    have hW : env.HasType U [] (.forallE d (VExpr.wrapForalls rest R)) T := hT.hasType.2
    obtain ⟨hd, hB⟩ := hW.forallE_inv henv.ordered
    have hR := (VEnv.IsType.wrapForalls_inv henv.ordered
      (ctx := [d]) ⟨trivial, hd⟩ hB).2
    have hY : env.IsType U (d :: rest).reverse R := by
      simpa [List.reverse_cons] using hR
    obtain ⟨u, hu⟩ := hY
    have hclose := VExpr.wrapForalls_defeqCtx henv hctx ⟨u, hu⟩ ⟨_, hu⟩
    exact VEnv.IsDefEqU.trans henv trivial ⟨T, hT⟩ hclose.symm

/-! ### Lowered auxiliary constructors restore to the direct constructors -/

/-- For auxiliary families expanding their generated families by restoring
leaves, restoration maps every lowered auxiliary constructor type to a term
equal (at every type) to the corresponding constructor type of the direct
family. -/
theorem auxiliaryLoweredConstructors_restore
    {base envTypes : VEnv} {paramCtx params : List VExpr} {decl : VInductDecl}
    {r : Restoration} {auxiliaries : List ContainerSpecialization}
    {generated targets direct : List VInductiveType}
    (henv : envTypes.WF)
    (Haux : List.Forall₂ (SpecializationGenerates base envTypes paramCtx decl)
      auxiliaries generated)
    (Hexp : List.Forall₂ (VInductDecl.NestedTypeExpansion base decl
        (r.RestoringLeaf (VLevel.params decl.uvars)))
      generated targets)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx)
    (hfresh : ∀ name ∈ r.restorableNames, envTypes.constants name = none)
    (hlevels : ∀ t ∈ targets, ∀ lc ∈ t.ctors,
      lc.type.ConstLevelsAt (r.heads.map (·.auxiliary)) (VLevel.params decl.uvars))
    (hmapM : auxiliaries.mapM (fun a => a.specializedFamily decl.uvars params) = some direct) :
    List.Forall₂ (fun t d : VInductiveType => List.Forall₂
        (fun lc dc : VConstVal => ∃ restored, r.expr lc.type = some restored ∧
          envTypes.SimAt decl.uvars [] restored dc.type)
        t.ctors d.ctors)
      targets direct := by
  have hordered := henv.ordered
  induction Haux generalizing targets direct with
  | nil =>
    cases Hexp
    simp only [List.mapM_nil, pure, Option.some.injEq] at hmapM
    subst hmapM
    exact .nil
  | @cons a g auxs gens hev _ ih =>
    cases Hexp with
    | @cons _ t _ ts hexp hexps =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at hmapM
    obtain ⟨d, hd, ds, hds, rfl⟩ := hmapM
    refine .cons ?_ (ih hexps
      (fun t ht => hlevels t (List.mem_cons_of_mem _ ht)) hds)
    obtain ⟨sp, -, hspCtx, -, -, -, hctors⟩ := hev.application
    have hPS : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse sp.reverse :=
      VEnv.IsDefEqCtx.trans_empty henv hparams (hspCtx.symm hordered)
    -- generated and direct constructors are definitionally equal
    have HGD : List.Forall₂ (fun gc dc : VConstVal =>
        envTypes.IsDefEqU decl.uvars [] gc.type dc.type) g.ctors d.ctors :=
      Lean4Lean.List.Forall₂.trans (fun gc c dc h1 h2 => by
          rw [h2]
          exact VEnv.IsDefEqU.wrapForalls_params henv hPS h1.type)
        (Lean4Lean.List.Forall₂.flip hctors)
        (ContainerSpecialization.directFamily_ctors hd)
    refine Lean4Lean.List.Forall₂.trans (fun lc gc dc h1 h2 => ?_)
      (Lean4Lean.List.Forall₂.flip
        (Lean4Lean.List.Forall₂.and_mem hexp.constructors)) HGD
    obtain ⟨hc, -, hlc⟩ := h1
    obtain ⟨_, hgd⟩ := h2
    have hfree : gc.type.containsAnyConst r.restorableNames = false :=
      (hgd.hasType.1.noFreshConsts hordered hfresh (by intro _ h; simp at h)).1
    exact ⟨gc.type, hc.type.restore hfree (hlevels t List.mem_cons_self lc hlc),
      fun _ hT => VEnv.IsDefEqU.of_l henv trivial ⟨_, hgd⟩ hT⟩

/-! ### The restoration substitution of a validated nested run -/

/-- The restoration substitution of a validated nested run from the lowered
header environment to the source header environment
(`Restoration.constInterpretation_substitution` over the signature's
parameters), together with the definitional equality, in the lowered header
environment, of the normalized and lowered constructor types of every family
(`Models.constructors`). This is the setup of
`NestedRun.sourceConstructors_of_lowering`. -/
theorem NestedRun.constructorRestorationSubstitution
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
      envTypes.constants p.1 = none) :
    (compilationRestoration sourceDecl auxiliaries).Substitution envTypes
        E.lowered.constructors.toConstructorCheck.headerVEnv
        ((compilationRestoration sourceDecl auxiliaries).constInterpretation
          E.lowered.signature.params) ∧
      List.Forall₂ (fun n l : VInductiveType => List.Forall₂
          (fun nc lc : VConstVal =>
            E.lowered.constructors.toConstructorCheck.headerVEnv.IsDefEqU sourceDecl.uvars []
              nc.type lc.type) n.ctors l.ctors)
        E.lowered.signature.declaration.types
        E.lowered.loweredDecl.types := by
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
  exact ⟨S, forall₂_ctors_split (R := fun nc lc : VConstVal =>
      E.lowered.constructors.toConstructorCheck.headerVEnv.IsDefEqU sourceDecl.uvars []
        nc.type lc.type) Hlengths
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      rw [hloweredUvars] at h
      exact h.2.2) Hctors)⟩

/-- **Restoration of the auxiliary constructor types of a validated nested
run** (the constructor-type conjunct of the `auxiliaryFamilies` field of
`NestedCompilationRestorationFacts`), for any specialization list whose auxiliary
families expand their generated families by restoring leaves, given that
restoration is defined on the normalized auxiliary constructor types. -/
theorem NestedRun.auxiliaryConstructors_of_lowering
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
    (HauxRestoring : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
          (VLevel.params sourceDecl.uvars)))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (htotal : ∀ normalized ∈ E.lowered.signature.declaration.types.drop
        sourceDecl.types.length,
      ∀ ctor ∈ normalized.ctors, ∃ restored,
        (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored) :
    ∀ envTypes direct,
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes →
      auxiliaries.mapM (fun a => a.specializedFamily sourceDecl.uvars
        E.lowered.signature.params) = some direct →
      List.Forall₂ (fun normalized family : VInductiveType =>
          List.Forall₂ (fun normalized ctor : VConstVal =>
            RestoresType (compilationRestoration sourceDecl auxiliaries) envTypes
              sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (E.lowered.signature.declaration.types.drop
          sourceDecl.types.length) direct := by
  intro envTypes' direct hadded' hmapM
  rw [hadded] at hadded'
  cases hadded'
  let r := compilationRestoration sourceDecl auxiliaries
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨S, Hdefeq⟩ := E.constructorRestorationSubstitution wf hadded henvTypes
    Haux Hexpansion hnodup hfresh hrecFresh
  -- the common parameter telescope
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.lowered.constructors.toConstructorCheck.parameterScope.toCtx.reverse).reverse
      E.lowered.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      OrdinaryConstructorCheck.parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hparams : E.lowered.signature.params =
      E.lowered.constructors.toConstructorCheck.parameterScope.toCtx.reverse :=
    E.lowered.recursorConstruction.generator.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.lowered.signature.params.reverse
      E.lowered.headers.commonParameterContext := by
    rw [hparams]; exact hlink
  -- the universe arguments of the lowered auxiliary constructor types
  have hlevels : ∀ t ∈ E.lowered.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, lc.type.ConstLevelsAt (r.heads.map (·.auxiliary))
        (VLevel.params sourceDecl.uvars) := by
    have h := E.loweredAuxiliaryConstructorLevels wf Hsources
    rwa [← auxiliarySpecializations_headNames Haux Hexpansion,
      ← compilationRestoration_heads_auxiliary] at h
  have Hlowered := auxiliaryLoweredConstructors_restore henvTypes Haux HauxRestoring hP
    hfreshAll hlevels hmapM
  exact sourceConstructors_of_substitution S VExpr.projNamesFixed_id
    henvTypes.betaSubjectReduction
    (Lean4Lean.List.forall₂_drop Hdefeq sourceDecl.types.length) Hlowered htotal

end VerifyInductive

end Lean4Lean
