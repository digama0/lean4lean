import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseFormation

namespace Lean4Lean

/-- Abstract compilation, separate from the executable compiler: the shared
finite derivation `CompiledInductive` (ordinary compilation being its
zero-specialization case) generates the block. That the block lays out the
declaration's families, constructors and projections, and that its installed
names are distinct, are consequences (`CompilesTo.types`, `.ctors`,
`.projections`, `.names`). -/
abbrev VInductDecl.CompilesTo
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop :=
  CompiledInductive env decl block

theorem VInductDecl.CompilesTo.types {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : block.types = decl.typeConstants :=
  CompiledInductive.types_eq H

theorem VInductDecl.CompilesTo.ctors {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : block.ctors = decl.constructorConstants :=
  CompiledInductive.ctors_eq H

theorem VInductDecl.CompilesTo.projections {env : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : decl.CompilesTo env block) :
    block.projections = decl.projectionEntries :=
  CompiledInductive.projections_eq H

theorem VInductDecl.CompilesTo.names {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup :=
  CompiledInductive.names_nodup H

theorem InductiveSignature.FamilyTypesWF.mono {s : InductiveSignature}
    {env env' : VEnv} {uvars : Nat}
    (H : s.FamilyTypesWF env uvars) (hle : env ≤ env') :
    s.FamilyTypesWF env' uvars :=
  fun owner => ⟨(H owner).1.mono fun h => h.mono hle, (H owner).2.mono hle⟩

theorem InductiveSignature.Models.mono
    {s : InductiveSignature} {env env' envTypes' : VEnv} {decl : VInductDecl}
    (H : s.Models env decl) (henv : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes') :
    s.Models env' decl := by
  rcases H.constructors with ⟨envTypes, htypesOld, hctors⟩
  have hle := VEnv.addConstVals_mono henv htypesOld htypes
  refine { H with
    families := ?_
    constructors := ⟨envTypes', htypes, ?_⟩
    classifiedFields := ?_ }
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ _ h => h) H.families
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.mono hle⟩) hctors
  · rcases H.classifiedFields with hunsafe | ⟨envTypesPos, htypesPos, hpos⟩
    · exact .inl hunsafe
    · refine .inr ⟨envTypes', htypes, ?_⟩
      intro ctor hc i hi
      obtain ⟨normalized, hnormal, hshape⟩ := hpos ctor hc i hi
      exact ⟨normalized,
        hnormal.mono (VEnv.addConstVals_mono henv htypesPos htypes), hshape⟩

theorem VInductDecl.OwnCaseEliminators.mono {env env' envTypes' : VEnv} {decl : VInductDecl}
    {es : List (Name × InductiveSignature.CaseSchema)} (H : decl.OwnCaseEliminators env es)
    (henv : env ≤ env') (htypes : env'.addConstVals decl.typeConstants = some envTypes') :
    decl.OwnCaseEliminators env' es := fun p hp =>
  let ⟨hr, ho, hm⟩ := H p hp
  ⟨hr, ho, hm.mono henv htypes⟩

theorem VInductDecl.CompilesTo.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (Hblock : block.WF env')
    (H : decl.CompilesTo env block) : decl.CompilesTo env' block :=
  CompiledInductive.mono H henv Hblock

theorem VInductDecl.CompilesTo.sourceNames
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : decl.sourceNames.Nodup := by
  have hprefix : ((block.types ++ block.ctors).map (·.name)).Nodup := by
    apply List.Nodup.sublist (l₂ :=
      (block.types ++ block.ctors ++ block.recursors).map (·.name))
    · simp [List.map_append, List.append_assoc]
    · exact H.names
  simpa [VInductDecl.sourceNames, H.types, H.ctors, List.map_append]
    using hprefix

/-! ## Ordinary-or-nested formation derivations

Nested formation refers only to prior, finitely derived installed inductive
blocks. Defining the installation of prior containers (`VEnv.InstalledBelow`) in the same
mutual induction as formation avoids both an uncheckable environment lookup and a definitional
cycle through `AddInduct`. -/

/-- Exact construction of one direct auxiliary constructor before its own
body is recursively lowered. -/
structure VInductDecl.SpecializedAuxConstructor
    (env : VEnv) (U : Nat)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (containerFamily auxiliaryFamily : VInductiveType)
    (source target : VConstVal) : Prop where
  name : target.name = source.name.replacePrefix containerFamily.name
    auxiliaryFamily.name
  uvars : target.uvars = auxiliaryFamily.uvars
  type : env.IsDefEqU U [] target.type
    (VExpr.wrapForalls sourceParams
      (VExpr.instantiateForallPrefix (source.type.instL levels) baseArgs))

/-- A rigid head used to package two corresponding argument lists as one
expression relation.  Unlike a bound variable, it is stable when the
surrounding constructor telescope is lifted. -/
def VInductDecl.nestedTrailingMarker : VExpr :=
  .const `_nested.trailing []

mutual

/-- Formation is either the ordinary judgment or a finite nested
expansion into an independently ordinary well-formed declaration. -/
inductive VInductDecl.FormationWF : VEnv → VInductDecl → Prop
  | ordinary {env decl} : VInductDecl.OrdinaryFormationWF env decl →
      VInductDecl.FormationWF env decl
  | nested {base env decl} : VInductDecl.NestedFormationWF base decl →
      base ≤ env →
      VInductDecl.FormationWF env decl

/-- A prior container declaration. It has its own finite source/formation derivation, compiles
to the exact block, and that well-formed block is installed below the ambient environment. -/
inductive VEnv.InstalledBelow : VEnv → VInductDecl → Prop
  | intro {env container base block installed} :
      VInductDecl.SourceWF base container →
      VInductDecl.FormationWF base container →
      container.CompilesTo base block →
      block.WF base →
      VInductBlock.install base block = some installed →
      installed ≤ env →
      VEnv.InstalledBelow env container

/-- One legal replacement of a maximal nested occurrence. The auxiliary family
is an exact parameter specialization of a family in a previously installed
container block, and its direct constructors are the corresponding exact
specializations with deterministic names.  The verification of the executable
lowering separately records that some concrete parameter syntax
mentions the finite lowering queue.  That occurrence is intentionally not a
premise here: `TrExprS` erases metadata and let types/values and interprets
projections opaquely, so a concrete occurrence need not survive in `VExpr`.
Such an erased-only occurrence may generate a semantically unused auxiliary;
this remains sound because the prior-container specialization is exact and
ordinary formation checks the complete expanded finite block. -/
inductive VInductDecl.NestedOccurrenceReplacement :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | intro {env sourceTypesEnv source generated depth input output container
      containerFamily auxiliaryFamily sourceParams baseArgs levels
      auxiliaryLevels inputBaseArgs sourceTrailing targetTrailing} :
      env.addConstVals source.typeConstants = some sourceTypesEnv →
      VEnv.InstalledBelow sourceTypesEnv container →
      containerFamily ∈ container.types →
      auxiliaryFamily ∈ generated →
      sourceParams.length = source.nparams →
      baseArgs.length = container.nparams →
      (∀ arg ∈ baseArgs, arg.ClosedN source.nparams) →
      levels.length = container.uvars →
      (∀ level ∈ levels, level.WF source.uvars) →
      auxiliaryFamily.uvars = source.uvars →
      sourceTypesEnv.IsDefEqU source.uvars [] auxiliaryFamily.type
        (VExpr.wrapForalls sourceParams
          (VExpr.instantiateForallPrefix
            (containerFamily.type.instL levels) baseArgs)) →
      List.Forall₂
        (VInductDecl.SpecializedAuxConstructor sourceTypesEnv source.uvars sourceParams
          baseArgs levels containerFamily auxiliaryFamily)
        containerFamily.ctors auxiliaryFamily.ctors →
      auxiliaryLevels.length = source.uvars →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker
          (baseArgs.map (fun arg => arg.liftN depth 0)))
        (VExpr.mkApps VInductDecl.nestedTrailingMarker inputBaseArgs) →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceTrailing)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker targetTrailing) →
      input = VExpr.mkApps (.const containerFamily.name levels)
        (inputBaseArgs ++ sourceTrailing) →
      output = VExpr.mkApps (.const auxiliaryFamily.name auxiliaryLevels)
        (source.paramVars depth ++ targetTrailing) →
      VInductDecl.NestedOccurrenceReplacement env source generated depth input output

/-- Specialized structural expansion used inside the mutual formation
derivation. It has a forgetful map to `VExpr.NestedExprExpansion`; spelling it
out here is required by Lean's strict-positivity checker for the mutual leaf. -/
inductive VInductDecl.NestedExprWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | occurrence {env source generated depth relativeDepth input output} :
      depth = source.nparams + relativeDepth →
      VInductDecl.NestedOccurrenceReplacement env source generated relativeDepth
        input output →
      VInductDecl.NestedExprWFExpansion env source generated depth input output
  | bvar {env source generated index depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.bvar index) (.bvar index)
  | sort {env source generated level depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.sort level) (.sort level)
  | const {env source generated name levels depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.const name levels) (.const name levels)
  | elim {env source generated block owner levels depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.elim block owner levels) (.elim block owner levels)
  | proj {env source generated typeName index depth sourceMajor targetMajor} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceMajor targetMajor →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.proj typeName index sourceMajor)
        (.proj typeName index targetMajor)
  | app {env source generated depth sourceFn targetFn sourceArg targetArg} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceFn targetFn →
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceArg targetArg →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.app sourceFn sourceArg) (.app targetFn targetArg)
  | lam {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.lam sourceDomain sourceBody) (.lam targetDomain targetBody)
  | forallE {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)

/-- Strictly-positive counterpart of `NestedForallPrefixExpansion` for the
mutually defined nested-formation leaf. -/
inductive VInductDecl.NestedForallPrefixWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hbody : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth 0
        sourceBody targetBody
  | cons
      (Hdomain : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain)
      (Hbody : VInductDecl.NestedForallPrefixWFExpansion env source generated
        (depth + 1) arity sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth
        (arity + 1) (.forallE sourceDomain sourceBody)
          (.forallE targetDomain targetBody)

/-- Ordered constructor expansion without nesting the mutually defined leaf
inside an external `List.Forall₂`. -/
inductive VInductDecl.NestedConstructorWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VConstVal → List VConstVal → Prop
  | nil {env source generated} :
      VInductDecl.NestedConstructorWFExpansions env source generated [] []
  | cons {env source generated sourceCtor targetCtor sourceCtors targetCtors} :
      targetCtor.name = sourceCtor.name →
      targetCtor.uvars = sourceCtor.uvars →
      VInductDecl.NestedForallPrefixWFExpansion env source generated 0
        source.nparams sourceCtor.type targetCtor.type →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceCtors targetCtors →
      VInductDecl.NestedConstructorWFExpansions env source generated
        (sourceCtor :: sourceCtors) (targetCtor :: targetCtors)

/-- Ordered family expansion for the initial mutual block followed by the
direct, unlowered auxiliary queue. -/
inductive VInductDecl.NestedTypeWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VInductiveType → List VInductiveType → Prop
  | nil {env source generated} :
      VInductDecl.NestedTypeWFExpansions env source generated [] []
  | cons {env source generated sourceType targetType sourceTypes targetTypes} :
      targetType.name = sourceType.name →
      targetType.uvars = sourceType.uvars →
      env.IsDefEqU source.uvars [] sourceType.type targetType.type →
      targetType.numIndices = sourceType.numIndices →
      targetType.resultLevel = sourceType.resultLevel →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceType.ctors targetType.ctors →
      VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
        targetTypes →
      VInductDecl.NestedTypeWFExpansions env source generated
        (sourceType :: sourceTypes) (targetType :: targetTypes)

/-- A nested declaration is formed by expanding the source families and a
finite queue of direct auxiliary sources into a declaration satisfying the
ordinary source and formation judgments. -/
inductive VInductDecl.NestedFormationWF : VEnv → VInductDecl → Prop
  | intro {env source expanded generated} :
      VInductDecl.SourceWF env expanded →
      VInductDecl.OrdinaryFormationWF env expanded →
      VInductDecl.SourceParameterWF env source →
      expanded.uvars = source.uvars →
      expanded.nparams = source.nparams →
      expanded.isUnsafe = source.isUnsafe →
      VInductDecl.NestedTypeWFExpansions env source generated
        (source.types ++ generated) expanded.types →
      VInductDecl.NestedFormationWF env source

end

/-- Constructor expressions count every enclosing forall binder, whereas
`NestedOccurrenceReplacement` counts only constructor-field binders below the common
parameter prefix.  This wrapper is the explicit boundary between those two
depth conventions. -/
def VInductDecl.NestedOccurrenceReplacementAbs
    (env : VEnv) (source : VInductDecl)
    (generated : List VInductiveType) (depth : Nat)
    (input output : VExpr) : Prop :=
  ∃ relativeDepth,
    depth = source.nparams + relativeDepth ∧
    VInductDecl.NestedOccurrenceReplacement env source generated relativeDepth
      input output


theorem VExpr.getAppFnArgs_mkApps_const (name : Name) (levels : List VLevel)
    (args : List VExpr) :
    (VExpr.mkApps (.const name levels) args).getAppFnArgs =
      (.const name levels, args) := by
  suffices h : ∀ (fn : VExpr) (pre : List VExpr),
      fn.getAppFnArgs = (.const name levels, pre) →
      (VExpr.mkApps fn args).getAppFnArgs = (.const name levels, pre ++ args) by
    simpa using h (.const name levels) [] (by simp)
  induction args with
  | nil =>
    intro fn pre h
    simpa [VExpr.mkApps] using h
  | cons arg args ih =>
    intro fn pre h
    have := ih (.app fn arg) (pre ++ [arg]) (by simp [VExpr.getAppFnArgs_app, h])
    simpa [VExpr.mkApps, List.append_assoc] using this

/-- Every auxiliary-family leaf replaces a source expression by an
application headed by one of the auxiliary families. -/
theorem VInductDecl.NestedOccurrenceReplacementAbs.headConst
    {env : VEnv} {source : VInductDecl} {generated : List VInductiveType}
    {depth : Nat} {input output : VExpr}
    (H : VInductDecl.NestedOccurrenceReplacementAbs env source generated depth
      input output) :
    ∃ auxiliary ∈ generated, ∃ levels args,
      output.getAppFnArgs = (.const auxiliary.name levels, args) := by
  rcases H with ⟨relativeDepth, _hdepth, H⟩
  cases H with
  | intro _ _ _ hgen _ _ _ _ _ _ _ _ _ _ _ _ houtput =>
    exact ⟨_, hgen, _, _, by rw [houtput]; exact VExpr.getAppFnArgs_mkApps_const _ _ _⟩

theorem List.Forall₂.map_eq_of {α β γ : Type _} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (H : List.Forall₂ R l₁ l₂)
    (f : α → γ) (g : β → γ) (hf : ∀ a b, R a b → f a = g b) :
    l₁.map f = l₂.map g := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp [hf _ _ h, ih]

/-- Raw constructor shapes of the source families follow from the raw
shapes of the expanded declaration through the ordered nested expansion. -/
theorem VInductDecl.rawShapesOfNestedExpansions
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      (source.types ++ generated) expanded.types)
    (Hraw : ∀ type ∈ expanded.types, ∀ ctor ∈ type.ctors,
      expanded.RawCtorShape type ctor)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnodup : (expanded.types.map (·.name)).Nodup) :
    ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor := by
  have hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name) :=
    (Lean4Lean.List.Forall₂.map_eq_of Htypes (·.name) (·.name)
      (fun _ _ h => h.name.symm)).symm
  intro type htype ctor hctor
  rcases Lean4Lean.List.Forall₂.forall_exists_l Htypes type
      (List.mem_append_left _ htype) with ⟨target, htarget, Hexp⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_l Hexp.constructors ctor hctor with
    ⟨targetCtor, htargetCtor, Hctor⟩
  exact VInductDecl.RawCtorShape.ofNestedExpansion
    (fun h => VInductDecl.NestedOccurrenceReplacementAbs.headConst h)
    huvars hnparams hnames hnodup htype htarget Hexp.name Hexp.numIndices
    Hctor.type (Hraw target htarget targetCtor htargetCtor)

/-- Constructor telescope lengths agree positionally across the ordered
nested expansion of the source families. -/
theorem VInductDecl.constructorArityPrefixOfNestedExpansions
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      (source.types ++ generated) expanded.types)
    (Hraw : ∀ type ∈ expanded.types, ∀ ctor ∈ type.ctors,
      expanded.RawCtorShape type ctor)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnodup : (expanded.types.map (·.name)).Nodup) :
    source.ConstructorArityPrefix expanded := by
  have hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name) :=
    (Lean4Lean.List.Forall₂.map_eq_of Htypes (·.name) (·.name)
      (fun _ _ h => h.name.symm)).symm
  intro familyIdx hsource hexpanded ctorIdx hsourceCtor hexpandedCtor
  have hprefix : familyIdx < (source.types ++ generated).length := by
    simp only [List.length_append]
    omega
  have Hexp := Lean4Lean.List.Forall₂.getElem_of Htypes familyIdx hprefix hexpanded
  have hget : (source.types ++ generated)[familyIdx] = source.types[familyIdx] :=
    List.getElem_append_left hsource
  rw [hget] at Hexp
  have Hctor := Lean4Lean.List.Forall₂.getElem_of Hexp.constructors ctorIdx
    hsourceCtor hexpandedCtor
  exact (VInductDecl.RawCtorShape.ofNestedExpansion_core
    (fun h => VInductDecl.NestedOccurrenceReplacementAbs.headConst h)
    huvars hnparams hnames hnodup (List.getElem_mem hsource)
    (List.getElem_mem hexpanded) Hexp.name Hexp.numIndices Hctor.type
    (Hraw _ (List.getElem_mem hexpanded) _ (List.getElem_mem hexpandedCtor))).2

/-- Abstract well-formedness always retains the source judgment;
formation is a finite ordinary-or-nested derivation. -/
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧ decl.FormationWF env

/-- Source constructor typing at the exact header environment named by an
installation. -/
theorem VInductDecl.SourceWF.constructorsWF_at
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes := by
  rcases H.sourceConstructors with ⟨envTypes', htypes', hwf⟩
  cases Option.some.inj (htypes'.symm.trans htypes)
  exact hwf

/-- Both ordinary and nested formation retain the source
parameter judgment at any environment in which the headers install. -/
theorem VInductDecl.FormationWF.sourceParameterWF
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.FormationWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    decl.SourceParameterWF env := by
  cases H with
  | ordinary H => exact H.sourceParameterWF
  | nested H hle =>
    cases H with
    | intro _ _ Hparams _ _ _ _ =>
      exact Hparams.mono_of_addConstVals hle htypes

theorem VInductDecl.WF.sourceParameterWF
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.WF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    decl.SourceParameterWF env :=
  H.2.sourceParameterWF htypes

theorem VEnv.InstalledBelow.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : VEnv.InstalledBelow env decl) :
    VEnv.InstalledBelow env' decl := by
  cases H with
  | intro hsource hformation hcompile hblock hinstall hle =>
    exact .intro hsource hformation hcompile hblock hinstall (hle.trans henv)

/-- Every projection entry derived from an installed declaration is present
in the ambient projection registry.  This is the registry fact carried by an
installation certificate; clients do not need to reconstruct the installation order
of `VInductBlock.install`. -/
theorem VEnv.InstalledBelow.projection
    {env : VEnv} {decl : VInductDecl} {entry : VProjectionEntry}
    (H : VEnv.InstalledBelow env decl)
    (hentry : entry ∈ decl.projectionEntries) :
    env.projections entry.typeName entry.info := by
  cases H with
  | intro hsource hformation hcompile hblock hinstall hle =>
    unfold VInductBlock.install at hinstall
    simp at hinstall
    rcases hinstall with
      ⟨envTypes, htypes, envCtors, hctors, envRecursors, hrecursors, rfl⟩
    apply hle.projections
    simp only [VEnv.addDefEqRules_projections]
    rw [VEnv.addConstVals_projections hrecursors]
    rw [VEnv.addProjections_iff]
    exact Or.inl ⟨entry, hcompile.projections.symm ▸ hentry, rfl, rfl⟩

/-- An installed declaration exposes each of its family constants at the
exact abstract value recorded by the source declaration. -/
theorem VEnv.InstalledBelow.familyConstant
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl)
    (familyIdx : Nat) (hfamily : familyIdx < decl.types.length) :
    env.constants decl.types[familyIdx].name =
      some decl.types[familyIdx].toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : decl.types[familyIdx].toVConstVal ∈ block.types := by
      rw [Hcompile.types]
      exact List.mem_map.mpr
        ⟨decl.types[familyIdx], List.getElem_mem hfamily, rfl⟩
    have hlookup := VEnv.addConstVals_get htypes hmember
    have hcanonical : VInductBlock.install base block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecursors]
    have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (Hinstall.symm.trans hcanonical)
    subst installed
    apply hle.constants
    simpa only [VEnv.addDefEqRules_constants] using
      (VEnv.addConstVals_le hrecursors).constants
        (VEnv.addEliminators_addProjections_le.constants
          ((VEnv.addConstVals_le hctors).constants hlookup))

/-- Every family of an installed declaration carries the declaration's
universe arity. -/
theorem VEnv.InstalledBelow.typeUvars
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl) :
    ∀ type ∈ decl.types, type.uvars = decl.uvars := by
  cases H with
  | intro Hsource _ _ _ _ _ => exact Hsource.2.2.1

/-- Every constructor of an installed declaration carries the declaration's
universe arity. -/
theorem VEnv.InstalledBelow.constructorUvars
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl) :
    ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars := by
  cases H with
  | intro Hsource _ _ _ _ _ => exact Hsource.2.2.2.1

/-- An installed declaration exposes each of its constructor constants at
the exact abstract value recorded by the source declaration. -/
theorem VEnv.InstalledBelow.constructorConstant
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl)
    (familyIdx ctorIdx : Nat) (hfamily : familyIdx < decl.types.length)
    (hctor : ctorIdx < decl.types[familyIdx].ctors.length) :
    env.constants decl.types[familyIdx].ctors[ctorIdx].name =
      some decl.types[familyIdx].ctors[ctorIdx].toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : decl.types[familyIdx].ctors[ctorIdx] ∈ block.ctors := by
      rw [Hcompile.ctors]
      simp only [VInductDecl.constructorConstants, List.mem_flatMap]
      exact ⟨decl.types[familyIdx], List.getElem_mem hfamily,
        List.getElem_mem hctor⟩
    have hlookup := VEnv.addConstVals_get hctors hmember
    have hcanonical : VInductBlock.install base block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecursors]
    have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (Hinstall.symm.trans hcanonical)
    subst installed
    apply hle.constants
    simpa only [VEnv.addDefEqRules_constants] using
      (VEnv.addConstVals_le hrecursors).constants
        (VEnv.addEliminators_addProjections_le.constants hlookup)


/-- The declaration has no families and the block registers no case eliminator, or the block
registers exactly one case eliminator with a registration certificate
(`CaseSchema.RegistrationCertificate`:
the case-only compilation certificate, the key of the first family and header agreement),
projecting only out of structures registered in the constructor environment. It is installed after the
constructors and before the projections (`VInductBlock.install`). -/
def VInductBlock.EliminatorsWF (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop :=
  ∃ envTypes envCtors, env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    ((decl.types = [] ∧ block.eliminators = []) ∨
    ∃ key schema, block.eliminators = [(key, schema)] ∧
      schema.RegistrationCertificate env decl block key ∧ schema.ProjNamesRegistered envCtors key)

/-- The block skeleton of a declaration after its constructors: families, constructors,
projections and case eliminators, without generated recursors. -/
def VInductDecl.caseBlock (decl : VInductDecl)
    (eliminators : List (Name × InductiveSignature.CaseSchema)) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  recursors := []
  rules := []
  projections := decl.projectionEntries
  eliminators := eliminators

theorem InductiveSignature.CaseSchema.Certified.congr_block {schema : InductiveSignature.CaseSchema}
    {base : VEnv} {source : VInductDecl} {block block' : VInductBlock}
    (H : schema.Certified base source block) (htypes : block'.types = block.types)
    (hctors : block'.ctors = block.ctors) (hprojections : block'.projections = block.projections) :
    schema.Certified base source block' := by
  obtain ⟨expanded, auxiliaries, hdata, hprior, hr, hnames, hfresh⟩ := H
  exact ⟨expanded, auxiliaries,
    { hdata with
      types := htypes.trans hdata.types
      ctors := hctors.trans hdata.ctors
      projections := hprojections.trans hdata.projections },
    hprior, hr, hnames, hfresh⟩

theorem InductiveSignature.CaseSchema.RegistrationCertificate.congr_block
    {schema : InductiveSignature.CaseSchema} {base : VEnv} {source : VInductDecl}
    {block block' : VInductBlock} {key : Name}
    (H : schema.RegistrationCertificate base source block key) (htypes : block'.types = block.types)
    (hctors : block'.ctors = block.ctors) (hprojections : block'.projections = block.projections) :
    schema.RegistrationCertificate base source block' key :=
  { H with certified := H.certified.congr_block htypes hctors hprojections }

/-- Eliminator certification only reads a block's families, constructors and eliminators. -/
theorem VInductBlock.EliminatorsWF.congr_block {env : VEnv} {decl : VInductDecl}
    {block block' : VInductBlock} (H : VInductBlock.EliminatorsWF env decl block)
    (htypes : block'.types = block.types) (hctors : block'.ctors = block.ctors)
    (hprojections : block'.projections = block.projections)
    (heliminators : block'.eliminators = block.eliminators) :
    VInductBlock.EliminatorsWF env decl block' := by
  obtain ⟨envTypes, envCtors, ht, hc, H⟩ := H
  refine ⟨envTypes, envCtors, htypes ▸ ht, hctors ▸ hc, ?_⟩
  rcases H with ⟨hT, hE⟩ | ⟨key, schema, hE, hreg, hprojs⟩
  · exact .inl ⟨hT, heliminators.trans hE⟩
  · exact .inr ⟨key, schema, heliminators.trans hE,
      hreg.congr_block htypes hctors hprojections, hprojs⟩

/-- Relational abstract environment extension for inductive declarations,
including the compiled block, which the refinement proof uses. -/
inductive VEnv.AddInduct (env : VEnv) (decl : VInductDecl) : VEnv → Prop where
  | intro :
    decl.WF env →
    VInductDecl.CompilesTo env decl block →
    VInductBlock.WF env block →
    VInductBlock.EliminatorsWF env decl block →
    VInductBlock.install env block = some env' →
    VEnv.AddInduct env decl env'

/-- An admitted inductive declaration is well formed. -/
theorem VEnv.AddInduct.sourceWF {env env' : VEnv} {decl : VInductDecl}
    (H : VEnv.AddInduct env decl env') : decl.WF env := by
  cases H with
  | intro hdecl => exact hdecl
