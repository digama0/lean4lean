# `Verify/Inductive`: the interface of the inductive refinement proof

This directory verifies the executable inductive checker on PR #43's calculus and `addInduct`,
on top of the checker verification (`Verify/TypeChecker`) and the environment model
(`Verify/Environment`). Each phase of the executable has an interface structure and a boundary
theorem; the tables below list them in pipeline order. Every boundary theorem is proved; the
proofs depend on `sorryAx` only through the accepted open proofs of `OPEN_PROOFS.md`.

## Principle

Interface structures carry the facts their consumers use, stated in the foundation's
vocabulary (`Theory/`, `Verify/Typing`, `Verify/TypeChecker`, `Verify/Environment`). Producers
construct them from directory-internal invariants, most of them ported from PR #53. A structure
may carry fields its consumers ignore; the boundary theorems' statements are the interface.

## What the pipeline consumes and produces

* From the checker verification: `CheckerEnv safety env venv` (what the checker reads:
  `CheckingEnv.Valid` plus `RecursorShapesCoherent` and `IotaRulesRegistered`) and
  `VContext`/`MLCtx`/`CheckBase`. The pipeline's context `ContextWF c` (`Context.lean`) carries
  all three environment facts, so `ContextSemantics.checkerEnv` gives the checker its `CheckerEnv` in
  every intermediate environment (header, constructor, projection stage).
* From the environment model: `VEnvs`/`VEnvs.WF`, `InstalledBlocks` and `InstalledBlocks.addInduct`,
  `CheckingEnv.Valid`, `EquationHeadsCoherent` (through `CheckingEnv.Valid.equationHeads`),
  PR #43's `AddInduct`, `TrIndType`, `TrRecursor`, `insertConsts`, `TrEnv'.induct`,
  `VEnvs.WF.extendInductExact`/`extendUnsafeExact`, `TrInductDeclCore`.
* To install a block the pipeline produces a `BlockCertificate safety env venv decl outEnv
  outVEnv` (`Install/BlockCertificate.lean`): `decl.WF venv` (all of `VInductDecl.WF`'s fields:
  `source`, `formation`, `recsCompiled`, `recs_wf`, `rec_shape`, `rules_nodup`, `rules_ctor`,
  `rule_shape`, `rules_wf : PatTyped`), PR #43's `AddInduct safety env.constants venv decl
  outEnv.constants outVEnv` (stages `stT`/`stC`/`stR`/`stP`, `TrIndType`, `TrRecursor` with
  `VRecRule`s read off the generator's equations, `order`/`fresh`/`map_eq`), and the facts
  `InstalledBlocks.addInduct` reads of the output (`MutualInductivesClosed`,
  `ConstructorOwnersPresent`, `InductInfosFromDecl`, cover, recursor majors,
  `ConstructorParameterAlignment`, `KLikeRecursor`). `BlockCertificate.extendSafeExact` and
  `extendUnsafeExact` install it into `VEnvs` (`VEnvs.WF.extendInductExact`, replaying the
  block at the other safety levels by `BlockCertificate.rebase`; `VEnvs.WF.extendUnsafeExact`
  with `TrEnv'.ignore` for the hidden observers).
* The inductive case of `addDecl.WF` (`Verify/Environment.lean`) is
  `addInductiveDeclaration.preserves` (`Dispatch.lean`): the primitive branch
  (`Primitive.checkInductive = .ok true`, `checkPrimitiveInductive_eq_true_iff`), the ordinary
  branch (lowering with no auxiliary family) and the nested branch
  (`Environment.addInductiveAfterLowering.nestedInductiveExtensionWF`,
  `Nested/Install/Extension.lean`). `addInductiveDeclaration.spec` is the source-facing form
  (`InductiveExtension`), under `SourceBVarClosed`.

## The phases and their interfaces (in pipeline order)

| phase (executable) | interface structure | boundary theorem | file |
|---|---|---|---|
| context | `ContextWF c` (`initial`, `withEnv` proved) | | `Context.lean` |
| certificates | `HeaderCertificate`, `ConstructorCertificate`, `FormationCertificate`, `RecursorsWF`, `FormationCertificate.wf : decl.WF`, `TrInductDeclCore.*` | `TrInductDeclCore.sourceNames_nodup`, `ConstructorCertificate.withRecs` | `Formation.lean` |
| `checkInductiveTypes nparams indTypes k` | `CheckedHeader(s)`, `CheckedHeaders.Describes`, `HeaderParameterContext`, `HeaderPhase Hc nparams indTypes c' Hc' stats` | `AddInductive.checkInductiveTypes.WF`, `Describes.headerCertificate` | `Header/Check.lean` |
| `declareInductiveTypes` | `HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv` extends `HeaderData` (decl-indexed; only header data constrained) with the validity of the header context | `AddInductive.declareInductiveTypes.WF` | `Header/Installation.lean`, `HeaderData.lean` |
| `constructorPhase` (= headers + checkConstructors + declareConstructors) | `ConstructorCheck`: header data, `TrInductDeclCore`, `FormationCertificate`, `classes`, `ivals`, `trTypes : TrIndType`, `map_eq`/`fresh`, `context : ContextWF {c with env := ctorEnv}` over `envP = ctorVEnv.addProjections decl.projectionEntries`, `closed`, `inductInfosFromDecl`, `constructorParameterAlignment` (one structure for the ordinary and the primitive path) | `AddInductive.constructorPhase.WF` | `ConstructorCheck.lean`, `Constructor/Check.lean` |
| recursor suffix of `runWithStats` | `RecursorCheck R outEnv` (= `RecursorInstallation R outEnv`): `rvals`, `recs`, `outVEnv`, `recsAdded`, `trRecs : TrRecursor`, `mapEq`/`freshRvals`, `checkingValid`, the shape clauses `recsWF`/`rec_shape`/`rules_nodup`/`rulesCtorAll`/`rule_shape`/`rules_closed`, `kLike`, the generator (`signature`, `generation`, `models`, `admissible`, `ihsWellTyped`, `familyTypesWF`, `recs_recursors`, `metadataAll`) | `ConstructorCheck.recursorPhasesWF`, `VRecRule.OfEquation.ofTr` | `Recursor/Check.lean`, `Recursor/Entries/TrRecursorVal.lean` |
| rules | `RuleTranslations H` (Prop): `trRules : TrRecursorRule` coverage, `equationsWF : VDefEq.WF`, `rules_wf : PatTyped`; derived `block`, `compiles`, `blockWF`, `compilesTo`, `recsOf`, `recsCompiled`, `recursorsWF` | `RecursorCheck.generatedRuleTranslation`; `blockWF`/`compilesTo`/`recsOf` | `Rules/RuleTranslations.lean` |
| assembly | `BlockCertificate`, `RecursorCheck.outVEnv'` | `RecursorCheck.blockCertificate`, `BlockCertificate.installedBlocks`/`rebase`/`extendSafeExact`/`extendUnsafeExact` | `Install/BlockCertificate.lean` |
| `AddInductive.run` | `OrdinaryInstallation`, `OrdinaryRunResult`, `PrimitiveNamesFresh` | `Kernel.Environment.checkDuplicatedUnivParams.WF` | `Install/Ordinary.lean` |
| `addInductiveAfterLowering` (ordinary) | `OrdinaryInstallation.extend*Exact`, `extensionModelWF`, `ordinaryInstalledModelWF`, `ordinaryExtensionModelWF` | | `Install/OrdinaryExtension.lean` |
| `checkInductiveSources`, `ElimNestedInductive.run` | `SourceSyntaxChecks`, `SourceBVarClosed`, `loweringRun`, `NestedLoweringOutput`, `Environment.addInductive.WF`; `types_nonempty`/`ordinary_types_eq_source` derived | `loweringRun.WF` | `Lowering.lean` |
| primitive branch | `PrimitiveInductiveShape`, `primitiveAddInductiveContext`, `PrimitiveInstallation`, `PrimitiveRunResult`; extension chain | `checkPrimitiveInductive_eq_true_iff`, `loweringRun.primitiveNoop`, `AddInductive.constructorPhase.primitiveWF`, recursor names not primitive (in `primitiveSourceAlignedWF`) | `Primitive/{Shape,Run,Extension}.lean` |
| result, dispatch | `SourceAddInduct` (`decl.WF ∧ addInduct = some`), `InductiveExtension`, `NestedInductivePreserves`, `addInductiveDeclaration.WF`/`WF_spec`/`WF_preserves`; `nestedInductivePreserves`, `addInductiveDeclaration.spec`/`preserves` (`Nested/Install/Dispatch.lean`) | | `Install/Result.lean`, `Dispatch.lean` |

The installed declaration is `decl.withRecs recs` (`Basic.lean`): the constructor phase fixes
the source part, the recursor phase adds the generated recursors with their `VRecRule`s. The
source fields reduce (`simp` lemmas `withRecs_*`); judgments indexed by the declaration transport
by `TrInductDeclCore.withRecs`, `FormationCertificate.withRecs` (`Formation.lean`).

Directories: `Context.lean`, `Context/**`, `Formation.lean`, `Header/**` (header phase);
`Constructor/**`; `Recursor/**`; `Rules/**`; `Install/**`, `Primitive/**`, `Prelude/**`
(installation, the primitive `Bool`/`Nat` path and the prelude's `Eq`); `Basic.lean`,
`Lowering.lean`, `Dispatch.lean` (shared statements).

## Dependencies between the phases

The header phase depends on nothing above it. The constructor phase consumes
`HeaderPhase`/`HeaderEnvironment` (including the header parameter scope's
`HeaderStatsWF.normalizedShapes` and concrete index telescopes). The recursor phase consumes the
constructor phase's telescope data (`ConstructorTails`, `ConstructorParameterPrefixes`,
`ConstructorOwnerNormalForms`) as fields of `ConstructorCheck`; the primitive path, which also
produces a `ConstructorCheck`, supplies them too. The rule phase consumes the recursor phase's
internals (rule templates, minor contexts, `canonicalGeneration`, `recInfos`, `elimLevel` data,
the `RuleAlignment` inputs). The installation needs the final shapes of all four interfaces;
the model installation (`rebase`, `extendSafeExact`, `extendUnsafeExact`, `installedBlocks`) and
`Primitive/Shape.lean` depend on nothing upstream. The nested branch discharges
`NestedInductivePreserves`; see the nested section below.

## Interface decisions

* `TrRecursor` (PR #43) is used as is for the recursor translation; `TrRecursorRule`/
  `RecursorMetadata`/`TrRecursorVal` are kept for the generator side, and
  `VRecRule.OfEquation.ofTr` connects them (via `TrExprS.unique`). `VInductDecl.RecsOf` is read
  off the block `RuleTranslations.block` with `recursors := generation.recursors`,
  `rules := generation.equations`.
* `rules_wf : PatTyped` is a field of `RuleTranslations` (restating `generatorEquationWF` as
  the generic instance); `equationsWF : VDefEq.WF` is kept beside it because the compiled
  block's `VInductBlock.WF` (needed by `CompiledInductive`, `ContainersInstalled`,
  `InstalledBelow`) still types the equations.
* Theory changes: `VEnv.addInduct`'s stages and
  `VInductDecl.RecsOf`/`VRecRule.OfEquation` moved to `Theory/Inductive/AddInduct.lean`;
  `ContainersInstalled.cons` and `VEnv.InstalledBelow.intro` now read
  `CompiledInductive base container block → block.WF base → container.RecsOf block →
  base.addInduct container = some installed → installed ≤ env` (the `VInductBlock.install`
  premise replaced by `RecsOf` and `addInduct`); the `InstalledBelow` lookup lemmas
  (`projection`, `familyConstant`, `constructorConstant`) moved to
  `Theory/Typing/InductiveLemmas.lean`. The checker produces these from `VEnv.InductInstalled`
  (`decl.WF base ∧ base.addInduct decl = some installed ∧ installed ≤ venv`): `WF.recsCompiled`
  gives the block with `CompilesTo` and `RecsOf`; `block.WF base` needs the equations' `VDefEq.WF`,
  which is why `RuleTranslations.equationsWF` is kept.
* For the ι clause of the observation model (`Model.PatValid.ordinary` and
  `Model.PatValid.nested`, both proved): every complete installed block exposes its whole
  `VInductDecl.WF` through `InstalledBlocks` (`InstalledBlock.Abstract.installed :
  VEnv.InductInstalled venv B.decl`), hence `rec_shape`, `rules_ctor`, `rules_nodup`,
  `rule_shape`, `recs_wf`, `rules_wf` and the formation data (`FormationWF` →
  `OrdinaryFormationWF`: `TypeShape` for the family sort, `CtorShape`/`CtorTailWF` for the
  singleton proof binders) and `recsCompiled` (the signature: fields, induction hypotheses).
  `PatsIota` is PR #43's theorem on `pats`. Structure eta is a `VEnv.projections` fact through
  `projectionEntries` (`addInduct_projections_iff`). The `BlockCertificate` adds nothing beyond
  `decl.WF` and `AddInduct` at the instance level; the kernel metadata is in
  `AddInduct.ivals`/`rvals` with `TrIndType`/`TrRecursor`.
* `VEnvAt.recursorShapes` (`Verify/TypeChecker.lean`) is consumed by `ContextWF.initial`; it is
  proved from `InstalledBlocks`, whose descriptors turn `decl.WF`'s `rec_shape`/`rules_ctor`
  into `VRecursorShape`/`VConstructorShape`. `VEnv.WF.patsAvoidFreshConsts`
  (`Verify/Typing/ConstSupport.lean`) is untouched by the pipeline's statements.
* `ContextWF` has no cache-mode field (there is one cache mode) and carries `shapes`/`iota`.
  `ConstructorTailCertificate.uniform` keeps `VInductDecl.UniformCtorTail`
  (`Theory/Inductive/Normalization.lean`).

## The nested branch

`Nested/**` verifies the nested branch on the same principle. `nestedInductivePreserves`
(`Nested/Install/Dispatch.lean`) proves `NestedInductivePreserves`, so `addDecl.WF`
(`Verify/Environment.lean`) has no hypothesis left. The executable's nested branch is
`AddInductive.run` on the lowered block followed by `Environment.restoreNestedAfterInstall`
(restore the source declaration from the lowered environment, then four validation passes in
side environments).

### Pipeline and interfaces (in order)

| phase (executable) | interface | boundary theorem | file |
|---|---|---|---|
| `ElimNestedInductive.run` (`loweringRun`) | `NestedLoweringOutput env fuel nparams sourceTypes lparams res` (Prop): `res.types` = source families (headers unchanged, constructors lowered, `source_headers`) ++ auxiliary families (`types_length`, `aux_cached`/`cached_aux`: one per cache entry); each cached occurrence is a container application `I Ds` at `I.numParams` arguments over `res.params` (`nested_app`); auxiliary names fresh (`aux_fresh`); `res.lctx` declares the parameters (`lctx_params`); the zero-auxiliary identity (`ordinary`); restoration inverts lowering on the source constructors up to `Expr.eqv` (`restore_source`, under `RestoreSourceDisjoint`) | `loweringRun.WF` | `Lowering.lean`; consequences in `Nested/Lowering/Basic.lean` |
| `AddInductive.run` on `res.types` | `LoweredRun Hc nparams indTypes loweredEnv`: the header phase from the source context, the constructor check (`loweredDecl`, header/constructor stages) and the recursor installation of the lowered block; `NestedRun` is indexed by it; `L.rules : RuleTranslations` | `AddInductive.run.loweredRun`, `OrdinaryRunResult.toLoweredRun` | `Nested/Restoration/LoweredRun.lean` |
| `restoreNestedAfterInstall` | `RestorationRun res loweredEnv env lparams types safety allowPrimitive fuel outEnv` (Prop): the restoration fold's output, the two side environments and the four passes' `= .ok ()` | `Environment.restoreNestedAfterInstall.WF` | `Nested/Restoration/RestorationRun.lean` |
| the validation passes | checker-facing: under `CheckerEnv safety E V` for the side environment, each pass yields `TrExprS`/typing in `V` (`validateSourceConstructorTypes.run.WF`, `validateRestoredRecursorTypes.{check,run}.WF`, `validateRestoredRecursorRules.{check,run}.WF`, `validateNestedAuxiliaries.WF`); the stripped output is a valid checking environment of the recursor stage (`stripRecursorRules.checkingValid`) | the seven statements | `Nested/Restoration/Validation/Passes.lean` |
| restoration | `RestoredBlock L sourceTypes isUnsafe outEnv` (data): the source declaration `decl` with restored recursors, `TrInductDeclCore` of the submitted syntax, `NestedFormationWF`, the specialization list with `ContainersInstalled` (on `addInduct`), `CompilationData` of the lowered run's generator with `compilationRestoration decl auxiliaries`, `RecsOf`, the kernel constants with `TrIndType`/`TrRecursor` in the stages, `order`/`map_eq`/`fresh`/`newUnsafe`, the shape clauses (`recs_wf`, `rec_shape`, `rules_nodup`, `rules_ctor`, `rule_shape`, `rules_closed`), `recShapes`/`recK` for every new recursor (auxiliary included); derived: `addInduct : AddInduct` (PR #43's step witness), `compilesTo`, `recsCompiled`, `rules_ofRestoredEquation`, `rule_ctor_cases`, `wf` (given the rule typing) | `nestedRestoredBlock` | `Nested/Restoration/Certificate.lean` (interface), `Restore.lean` |
| rule typing | `RestoredBlock.rulesWF : VInductDecl.WF.rules_wf` of the restored rules in `B.envR`, `RestoredBlock.blockWF : B.block.WF`; derived `wf'`, `compiledWF` | the two | `Nested/Equations/Rules.lean` |
| installation | `RestoredBlock.Installed B` (Prop): `CheckingEnv.Valid c.safety outEnv B.outVEnv`, `MutualInductivesClosed`, `ConstructorOwnersPresent`, `InductInfosFromDecl`, cover, recursor majors, `ConstructorParameterAlignment`; derived `blockCertificate : BlockCertificate` | `RestoredBlock.installedFacts` | `Nested/Install/Installed.lean` |
| result, dispatch | `NestedCertificate` (the block certificate plus the source translation), `extendExact`/`inductiveExtension` via `BlockCertificate.extend{Safe,Unsafe}Exact`; `nestedInductivePreserves` | | `Nested/Install/{Result,Dispatch}.lean` |

Theory files of the nested branch: `Theory/Typing/Interpretation.lean` (environment
interpretations; the eliminator clause replaced by `PatClause`, the obligation for a registered
ι rule, with `PatClause.of_fixed` for rules the interpretation fixes and `Sound.addPat`),
`Theory/Inductive/RestorationInterpretation.lean` (the restoration interpretation and
substitution; `VEnv.RestoredPattern` with its `clause`, the `pat` analogue of PR #53's
`RestoredEliminator`), `Theory/Typing/RestorationShapes.lean`,
`Theory/Inductive/RestorationHead.lean`, the second half of `Theory/Inductive/Restoration.lean` (the
helpers formerly in the dropped case-eliminator files), `Theory/Inductive/CompilationMajors.lean`
(what `WF.patCtor_rigid` needs, below).

### What the nested `VInductDecl.WF`/`RecsCompiled` instance provides for the model

The head-inversion model (`Theory/Typing/HeadInjectivity/Model/`) reads two kinds of facts
off an installed block; the nested instance provides them through `RestoredBlock`:

* **`WF.patCtor_rigid`** (`Model/WFFacts.lean`, proved): the constructor of every rule of every
  recursor of an installed block is a constructor of the block or of an installed container.
  Stated in Theory as `CompiledInductive.rule_ctor_cases`
  (`Theory/Inductive/CompilationMajors.lean`): for `CompiledInductive env source block` and
  `source.RecsOf block`, every `ru ∈ r.rules` with `r ∈ source.recs` has `ru.ctor` a
  constructor constant of `source` or `VEnv.IsPatCtor env ru.ctor` (the container's own ι rule
  on that constructor is registered in `env`, by `ContainersInstalled` on `addInduct`:
  `ContainersInstalled.constructor_isPatCtor`). Its ingredients are
  `Instance.restored_equation_major` and `CompilationData.constructor_name_cases`. On a
  `RestoredBlock` it is `RestoredBlock.rule_ctor_cases`. PR #53's stored-equation alternative
  (`env.defeqs prior ∧ prior.HasConstructorMajor name`) became a registered pattern, so the
  history induction of `patCtor_rigid` recurses on the container's pattern, added strictly
  earlier.
* **`Model.PatValid.nested`** (`Model/PatSound.lean`, proved): what the ordinary path gets from
  `RecsCompiled` and `VInductBlock.WF` holds for restored blocks too. `RestoredBlock.recsCompiled`
  is `⟨block, CompiledInductive.intro compiled containers, recsOf⟩` with `compiled :
  CompilationData venv decl L.loweredDecl s g auxiliaries block`, so (i) every installed
  `VRecRule` is `OfEquation` of a block equation that is the restoration of a generated
  equation of the lowered run's generator (`RestoredBlock.rules_ofRestoredEquation`:
  `CompilationData.equations : g.restoredEquations (compilationRestoration decl auxiliaries) =
  some block.rules`); (ii) the restored equation's λ-binders agree with the restored recursor's
  Π-telescope because both are `Restoration.expr` of the generator's (`CompilationData.recursors`,
  `Restoration.expr_wrapForalls`/`expr_recursorType` of `Theory/Typing/RestorationShapes.lean`;
  the generator's own agreement is the ordinary path's `recursorShapesOf`); (iii) the equations
  are typed in the empty context of the restored recursor stage (`RestoredBlock.blockWF`,
  through `Restoration.equation_wf`); (iv) the auxiliary recursors' rules fire on
  container constructors at the container's parameter count (`TrRecursor.rules` reads
  `ctorParams` off the output map; `rules_ctor` finds the constructor in the constructor stage,
  where the container is installed below). Structure eta and the projection entries are
  generic: `addInduct_projections_iff` on `decl.projectionEntries`, as for ordinary blocks.

### Directories

* `Nested/Lowering/**`: the lowering refinement, ending in `loweringRun.WF` (`Lowering.lean`).
* `Nested/Restoration/Validation/**`, `Nested/Restoration/Uniform/**`: the seven statements of
  `Validation/Passes.lean` and the parameter uniformity of the lowered recursors.
* The rest of `Nested/Restoration/**`: `nestedRestoredBlock` (`Restore.lean`), with the Theory
  facts of `CompilationMajors.lean`.
* `Nested/Equations/**`, `Nested/Install/**`: `rulesWF`, `blockWF` (`Equations/Rules.lean`),
  `installedFacts` (`Install/Installed.lean`), with `RestoredPattern.clause`
  (`Theory/Inductive/RestorationInterpretation.lean`) and `instantiateParams_liftN`
  (`Theory/Typing/RestorationShapes.lean`).
* Shared statements: `Lowering.lean`, `Nested/Restoration/{LoweredRun,RestorationRun,
  Certificate}.lean`, `Nested/Install/{Result,Dispatch}.lean`, `Dispatch.lean`,
  `Verify/Environment.lean`.

### Dependencies between the nested phases

1. The lowering and the validation passes depend on nothing above them; neither reads the
   other's output (the validation statements are checker-facing, over a `CheckerEnv` the caller
   supplies).
2. The restoration consumes `NestedLoweringOutput` (the cache facts `nested_app`,
   `aux_cached`, the inverse `restore_source`) and the validation passes (the side environments'
   models are built from the restoration folds and instantiate `Passes.lean`'s statements). The
   Theory facts of `CompilationMajors.lean` depend on nothing upstream.
3. The rule typing and installation consume `RestoredBlock` (rule typing over `B.envR` and the
   lowered run's `L.rules`; the environment-side facts over `B.addInduct`).
   `RestoredPattern.clause`, `instantiateParams_liftN` and the restoration substitution depend
   on nothing upstream.

### Interface decisions (nested)

* The restoration inverse is stated up to `Expr.eqv` (`==`), as in PR #53
  (`restoredType_eqv_source`); consumers translate through `TrExprS.eqv`. The zero-auxiliary
  identity stays literal.
* `NestedLoweringOutput` is syntactic (kernel `Expr`s, `env.find?`); the typing of the cached
  occurrences comes from the validation pass `validateNestedAuxiliaries`, not from lowering.
* `RestoredBlock` carries `CompilationData` against the lowered run's generator
  (`L.recursors.signature`/`generation`), so the rule typing transports `L.rules` along
  `compilationRestoration decl auxiliaries` without re-deriving the generator.
* `Interpretation.Sound.ordered` is `OrderedStrong` (`IsDefEq.instL_r` and `BetaRed.simAt`
  need it); `Sound` has a `pats` clause and no eliminator clause.
* `RestoredBlock.Installed` is a separate Prop structure so that the environment-side
  reasoning on the output (`InstalledBlocks`-style) is separate from the restoration data.
