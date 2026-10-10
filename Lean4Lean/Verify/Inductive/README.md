# `Verify/Inductive`: the interface of the inductive refinement proof

Wave 2 scaffold (branch `agent/iota-w2-scaffold`). This directory makes the verification of the
executable inductive checker exist on the merged foundation (PR #43's calculus and `addInduct`,
wave 1A's checker verification, wave 1B's environment model) as a buildable skeleton: every
cross-directory statement is in place, every proof that is not yet ported is a named stub listed
in the "Wave 2 scaffold" section of `STUBS.md`. Five agents fill the directories in parallel
without touching each other's files or this interface.

## Principle

Interface structures carry the facts their consumers use, stated in the foundation's
vocabulary (`Theory/`, `Verify/Typing`, `Verify/TypeChecker`, `Verify/Environment`). Producers
construct them from directory-internal invariants, which they port freely from the source branch
(`/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives`, commit `0dc2c7b3`). The
interface files below are frozen: an agent may *add* fields to a structure it produces (the
consumers ignore them) and add theorems, but may not rename, remove or retype a field or change
a boundary theorem's statement without the lead. Removals and retypings go through the lead.

## What the pipeline consumes and produces

* From wave 1A: `CheckerEnv safety env venv` (what the checker reads: `CheckingEnv.Valid` plus
  `RecursorShapesCoherent` and `IotaRulesRegistered`) and `VContext`/`MLCtx`/`CheckBase`. The
  pipeline's context `ContextWF c` (`Context.lean`) carries all three environment facts, so
  `ContextWF.checkerEnv` gives the checker its `CheckerEnv` in every intermediate environment
  (header, constructor, projection stage).
* From wave 1B: `VEnvs`/`VEnvs.WF`, `InstalledBlocks` and `InstalledBlocks.addInduct`,
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
* `InductiveDeclPreserves` (wave 1B's exact statement, `Verify/Environment.lean`) is now the
  theorem `inductiveDeclPreserves (hnested : NestedInductivePreserves)`, from
  `addInductiveDeclaration.WF_preserves` (`Dispatch.lean`): the primitive branch
  (`Primitive.checkInductive = .ok true`, `checkPrimitiveInductive_eq_true_iff`), the ordinary
  branch (lowering with no auxiliary family) and the nested branch, the latter being the
  hypothesis `NestedInductivePreserves` (layer-5 style; wave 3 proves it). `addDecl.WF` takes
  `hnested`; `addDecl.WF_of` keeps the `InductiveDeclPreserves` form. `addInductiveDeclaration.WF_spec`
  is the source-facing form (`InductiveExtension`), under `SourceBVarClosed`.

## The phases and their interfaces (in pipeline order)

| phase (executable) | interface structure | boundary theorem (stub) | file | owner |
|---|---|---|---|---|
| context | `ContextWF c` (frozen fields; `initial`, `withEnv` proved) | | `Context.lean` | Header |
| certificates | `HeaderCertificate`, `ConstructorCertificate`, `FormationCertificate`, `RecursorsWF`, `FormationCertificate.wf : decl.WF` (proved), `TrInductDeclCore.*` | `TrInductDeclCore.sourceNames_nodup`, `ConstructorCertificate.withRecs` | `Formation.lean` | Header (`withRecs`: Install) |
| `checkInductiveTypes nparams indTypes k` | `CheckedHeader(s)`, `CheckedHeaders.Describes`, `HeaderParameterContext`, `HeaderPhase Hc nparams indTypes c' Hc' stats` | `AddInductive.checkInductiveTypes.WF`, `Describes.headerCertificate` | `Header/Check.lean` | Header |
| `declareInductiveTypes` | `HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv` (decl-indexed; only header data constrained) | `AddInductive.declareInductiveTypes.WF` (`∀ decl, Describes → HeaderEnvironment`) | `Header/Installation.lean` | Header |
| `checkConstructors` | `CheckedFormation` (header env, `TrInductDeclCore`, `FormationCertificate`, `classes`) | `CheckedFormation.signature` (∃ `s`, `s.Models sourceEnv decl ∧ FamilyTypesWF headerVEnv`) | `Constructor/CheckedFormation.lean` | Constructor |
| `constructorPhase` (= headers + checkConstructors + declareConstructors) | `ConstructorCheck` extends `CheckedFormation`: `ivals`, `trTypes : TrIndType`, `map_eq`/`fresh`, `context : ContextWF {c with env := ctorEnv}` over `envP = ctorVEnv.addProjections decl.projectionEntries`, `closed`, `inductInfosFromDecl`, `constructorParameterAlignment` | `AddInductive.constructorPhase.WF` | `Constructor/Check.lean` | Constructor |
| recursor suffix of `runWithStats` | `RecursorCheck R outEnv`: `rvals`, `recs`, `outVEnv`, `recsAdded`, `trRecs : TrRecursor`, `map_eq`/`fresh`, `checking`, the shape clauses `recsWF`/`rec_shape`/`rules_nodup`/`rules_ctor`/`rule_shape`/`rules_closed`, `kLike`, the generator (`signature`, `generation`, `models`, `admissible`, `ihsWellTyped`, `familyTypesWF`, `recursors_eq`, `metadata`) | `ConstructorCheck.recursorPhasesWF`, `VRecRule.OfEquation.ofTr` | `Recursor/Check.lean`, `Recursor/Entries/TrRecursorVal.lean` | Recursor |
| rules | `RuleTranslations H` (Prop): `trRules : TrRecursorRule` coverage, `equationsWF : VDefEq.WF`, `rules_wf : PatTyped`; derived `block`, `compiles` (proved), `blockWF`, `compilesTo`, `recsOf`, `recsCompiled`, `recursorsWF` (proved from the stubs) | `RecursorCheck.generatedRuleTranslation`; `blockWF`/`compilesTo`/`recsOf` (Install) | `Rules/RuleTranslations.lean` | Rules (derived facts: Install) |
| assembly | `BlockCertificate`, `RecursorCheck.outVEnv'` | `RecursorCheck.blockCertificate`, `BlockCertificate.installedBlocks`/`rebase`/`extendSafeExact`/`extendUnsafeExact` | `Install/BlockCertificate.lean` | Install |
| `AddInductive.run` | `OrdinaryInstallation`, `OrdinaryRunResult`, `PrimitiveNamesFresh` (glue proved) | `Kernel.Environment.checkDuplicatedUnivParams.WF` | `Install/Ordinary.lean` | Install |
| `addInductiveAfterLowering` (ordinary) | `OrdinaryInstallation.extend*Exact`, `extensionModelWF`, `ordinaryInstalledModelWF`, `ordinaryExtensionModelWF` (all proved) | | `Install/OrdinaryExtension.lean` | Install |
| `checkInductiveSources`, `ElimNestedInductive.run` | `SourceSyntaxChecks`, `SourceBVarClosed`, `loweringRun`, `NestedLoweringOutput`, `Environment.addInductive.WF` (proved); `types_nonempty`/`ordinary_types_eq_source` derived | `loweringRun.WF` | `Lowering.lean` | Lowering (wave 3) |
| primitive branch | `PrimitiveInductiveShape`, `primitiveAddInductiveContext`, `PrimitiveInstallation`, `PrimitiveRunResult`; extension chain proved | `checkPrimitiveInductive_eq_true_iff`, `loweringRun.primitiveNoop`, `AddInductive.constructorPhase.primitiveWF`, recursor names not primitive (in `primitiveSourceAlignedWF`) | `Primitive/{Shape,Run,Extension}.lean` | Primitive |
| result, dispatch | `SourceAddInduct` (`decl.WF ∧ addInduct = some`), `InductiveExtension`, `NestedInductivePreserves`, `addInductiveDeclaration.WF`/`WF_spec`/`WF_preserves` (proved); `nestedInductivePreserves`, `addInductiveDeclaration.spec`/`preserves` (proved through the nested stubs, `Nested/Install/Dispatch.lean`) | | `Install/Result.lean`, `Dispatch.lean` | shared (lead) |

The installed declaration is `decl.withRecs recs` (`Basic.lean`): the constructor phase fixes
the source part, the recursor phase adds the generated recursors with their `VRecRule`s. The
source fields reduce (`simp` lemmas `withRecs_*`); judgments indexed by the declaration transport
by `TrInductDeclCore.withRecs`, `FormationCertificate.withRecs` (`Formation.lean`).

## Ownership map

* **Header**: `Context.lean`, `Context/**` (new), `Formation.lean`, `Header/**`.
* **Constructor**: `Constructor/**`.
* **Recursor**: `Recursor/**`.
* **Rules**: `Rules/**`.
* **Install**: `Install/**`, `Primitive/**`, `Prelude/**` (absent in the scaffold; `Tests/PreludeEq`
  stays deferred to wave 4), plus the derived facts in `Rules/RuleTranslations.lean`
  (`blockWF`, `compilesTo`, `recsOf`) and `ConstructorCertificate.withRecs` in `Formation.lean`.
* **Shared (lead)**: `Basic.lean`, `Install/Result.lean`, `Lowering.lean` (statements; proofs are
  wave 3's), `Dispatch.lean`, `Inductive.lean`, this file, `Verify/Environment.lean`.

## Dependency order

All five agents can start at once on the bulk of their directories (telescope, binder and
translation lemmas against the frozen foundation). The boundary theorems land in this order:

1. **Header** (`checkInductiveTypes.WF`, `declareInductiveTypes.WF`): nothing above it. The
   Constructor agent needs `HeaderPhase`/`HeaderEnvironment` only as hypotheses, so it can
   proceed in parallel; but the constructor check runs in the header context's parameter
   scope, so internal facts about that scope beyond `HeaderParameterContext` (the source
   branch's `HeaderStatsWF.normalizedShapes`, the concrete index telescopes) are requested
   from the Header agent as *additional fields* of `HeaderPhase`/`HeaderEnvironment`.
2. **Constructor** (`constructorPhase.WF`, `CheckedFormation.signature`): after Header's
   additions. The Recursor agent needs the constructor phase's internal telescope data (the
   source branch's `ConstructorTails`, `ConstructorParameterPrefixes`,
   `ConstructorOwnerNormalForms`, `SourceCtorsCertified`) as additional fields of
   `ConstructorCheck`; the Constructor agent adds them (the Primitive agent, who also produces
   `ConstructorCheck`, must then supply them: Primitive after Constructor).
3. **Recursor** (`recursorPhasesWF`, `VRecRule.OfEquation.ofTr`): after Constructor's additions.
   The Rules agent consumes the recursor phase's internals (rule templates, minor contexts,
   `canonicalGeneration`); the source branch's `RuleRhsTranslations` is stated against them, so
   Rules' boundary theorem lands after Recursor's `RecursorCheck` is final (additional fields:
   `recInfos`, `elimLevel` data, the `RuleAlignment` inputs).
4. **Rules** (`generatedRuleTranslation`): after Recursor.
5. **Install** (`blockCertificate`, `extend*Exact`, the derived `RuleTranslations` facts,
   `Primitive/**`): the assembly needs the final shapes of all four interfaces; the model
   installation (`rebase`, `extendSafeExact`, `extendUnsafeExact`, `installedBlocks`) and
   `Primitive/Shape.lean` depend on nothing upstream and can start immediately.

Wave 3 (nested) discharges `NestedInductivePreserves`; see the nested section below.

## Interface decisions for the lead and owners

* `TrRecursor` (PR #43) is used as is for the recursor translation; `TrRecursorRule`/
  `RecursorMetadata`/`TrRecursorVal` of the source branch are kept for the generator side, and
  `VRecRule.OfEquation.ofTr` bridges them (via `TrExprS.unique`). `VInductDecl.RecsOf` is read
  off the block `RuleTranslations.block` with `recursors := generation.recursors`,
  `rules := generation.equations`.
* `rules_wf : PatTyped` is a field of `RuleTranslations` (the Rules agent restates
  `generatorEquationWF` as the generic instance, PORT_PLAN section 2.3); `equationsWF :
  VDefEq.WF` is kept beside it because the compiled block's `VInductBlock.WF` (needed by
  `CompiledInductive`, `ContainersInstalled`, `InstalledBelow`) still types the equations.
* Theory COMPAT (`-- WAVE 2 COMPAT`, commit `17e28233`): `VEnv.addInduct`'s stages and
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
* For wave 1C's `Model.PatValid.iota` stub: every complete installed block exposes its whole
  `VInductDecl.WF` through `InstalledBlocks` (`InstalledBlock.Abstract.installed :
  VEnv.InductInstalled venv B.decl`), hence `rec_shape`, `rules_ctor`, `rules_nodup`,
  `rule_shape`, `recs_wf`, `rules_wf` and the formation data (`FormationWF` →
  `OrdinaryFormationWF`: `TypeShape` for the family sort, `CtorShape`/`CtorTailWF` for the
  singleton proof binders) and `recsCompiled` (the signature: fields, induction hypotheses).
  `PatsIota` is PR #43's theorem on `pats`. Structure eta is a `VEnv.projections` fact through
  `projectionEntries` (`addInduct_projections_iff`). The `BlockCertificate` adds nothing beyond
  `decl.WF` and `AddInduct` at the instance level; if the stub needs the kernel metadata it is in
  `AddInduct.ivals`/`rvals` with `TrIndType`/`TrRecursor`.
* Wave 1A's two stubs stay: `VEnvAt.recursorShapes` (`Verify/TypeChecker.lean`) is consumed by
  `ContextWF.initial`; it is provable from `InstalledBlocks` once `decl.WF`'s `rec_shape`/
  `rules_ctor` are turned into `VRecursorShape`/`VConstructorShape` (Install agent, with the
  Theory shape lemmas). `VEnv.Ordered.patsAvoidFreshConsts` (`Verify/Typing/ConstSupport.lean`)
  is untouched by the pipeline's statements.
* `ContextWF` lost the cache-mode field (cache modes are gone) and gained `shapes`/`iota`.
  `ConstructorTailCertificate.uniform` keeps `VInductDecl.UniformCtorTail`
  (`Theory/Inductive/Normalization.lean`).

## The nested branch (wave 3 scaffold, branch `agent/iota-w3s`)

`Nested/**` makes the nested branch exist as a buildable skeleton on the same principle: every
statement in place, every unported proof a named stub (`-- WAVE 3 STUB (owner)`) listed in the
"Wave 3 scaffold" section of `STUBS.md`. `nestedInductivePreserves` (`Nested/Install/Dispatch.lean`)
proves wave 2's hypothesis through the stubs, so `addDecl.WF` (`Verify/Environment.lean`) has
no hypothesis left. The executable's nested branch is `AddInductive.run` on the lowered block
followed by `Environment.restoreNestedAfterInstall` (restore the source declaration from the
lowered environment, then four validation passes in side environments).

### Pipeline and interfaces (in order)

| phase (executable) | interface | boundary theorem (stub) | file | owner |
|---|---|---|---|---|
| `ElimNestedInductive.run` (`loweringRun`) | `NestedLoweringOutput env fuel nparams sourceTypes lparams res` (Prop): `res.types` = source families (headers unchanged, constructors lowered, `source_headers`) ++ auxiliary families (`types_length`, `aux_cached`/`cached_aux`: one per cache entry); each cached occurrence is a container application `I Ds` at `I.numParams` arguments over `res.params` (`nested_app`); auxiliary names fresh (`aux_fresh`); `res.lctx` declares the parameters (`lctx_params`); the zero-auxiliary identity (`ordinary`); restoration inverts lowering on the source constructors up to `Expr.eqv` once the lowered auxiliary constructors are installed (`restore_source`, `LoweredAuxiliariesInstalled`) | `loweringRun.WF` | `Lowering.lean`; consequences in `Nested/Lowering/Basic.lean` | Lowering |
| `AddInductive.run` on `res.types` | `LoweredRun Hc nparams indTypes loweredEnv`: the header phase from the source context, the recursor input (`loweredDecl`, header/constructor stages) and the recursor check of the lowered block; `L.rules : RuleTranslations` | `AddInductive.run.loweredRun`, `OrdinaryRunResult.toLoweredRun` (proved) | `Nested/Restoration/LoweredRun.lean` | shared |
| `restoreNestedAfterInstall` | `RestorationRun res loweredEnv env lparams types safety allowPrimitive fuel outEnv` (Prop): the restoration fold's output, the two side environments and the four passes' `= .ok ()` | `Environment.restoreNestedAfterInstall.WF` (proved) | `Nested/Restoration/RestorationRun.lean` | shared |
| the validation passes | checker-facing: under `CheckerEnv safety E V` for the side environment, each pass yields `TrExprS`/typing in `V` (`validateSourceConstructorTypes.run.WF`, `validateRestoredRecursorTypes.{check,run}.WF`, `validateRestoredRecursorRules.{check,run}.WF`, `validateNestedAuxiliaries.WF`); the stripped output is a valid checking environment of the recursor stage (`stripRecursorRules.checkingValid`) | the seven statements | `Nested/Restoration/Validation/Passes.lean` | Restoration-A |
| restoration | `RestoredBlock L sourceTypes isUnsafe outEnv` (data): the source declaration `decl` with restored recursors, `TrInductDeclCore` of the submitted syntax, `NestedFormationWF`, the specialization list with `ContainersInstalled` (on `addInduct`), `CompilationData` of the lowered run's generator with `compilationRestoration decl auxiliaries`, `RecsOf`, the kernel constants with `TrIndType`/`TrRecursor` in the stages, `order`/`map_eq`/`fresh`/`newUnsafe`, the shape clauses (`recs_wf`, `rec_shape`, `rules_nodup`, `rules_ctor`, `rule_shape`, `rules_closed`), `recShapes`/`recK` for every new recursor (auxiliary included); derived: `addInduct : AddInduct` (PR #43's step witness), `compilesTo`, `recsCompiled`, `rules_ofRestoredEquation`, `rule_ctor_cases`, `wf` (given the rule typing) | `nestedRestoredBlock` | `Nested/Restoration/Certificate.lean` (interface), `Restore.lean` (stub) | Restoration-B |
| rule typing | `RestoredBlock.rulesWF : VInductDecl.WF.rules_wf` of the restored rules in `B.envR`, `RestoredBlock.blockWF : B.block.WF`; derived `wf'`, `compiledWF` | the two | `Nested/Equations/Rules.lean` | Equations+Install |
| installation | `RestoredBlock.Installed B` (Prop): `CheckingEnv.Valid c.safety outEnv B.outVEnv`, `MutualInductivesClosed`, `ConstructorOwnersPresent`, `InductInfosFromDecl`, cover, recursor majors, `ConstructorParameterAlignment`; derived `blockCertificate : BlockCertificate` (proved) | `RestoredBlock.installedFacts` | `Nested/Install/Installed.lean` | Install |
| result, dispatch | `NestedCertificate` (the block certificate plus the source translation), `extendExact`/`inductiveExtension` via `BlockCertificate.extend{Safe,Unsafe}Exact` (proved); `nestedInductivePreserves` (proved) | | `Nested/Install/{Result,Dispatch}.lean` | shared |

Theory (`-- WAVE 3 COMPAT`, new files): `Theory/Typing/Interpretation.lean` (environment
interpretations; the eliminator clause replaced by `PatClause`, the obligation for a registered
ι rule, with `PatClause.of_fixed` for rules the interpretation fixes and `Sound.addPat`),
`Theory/Inductive/RestorationInterpretation.lean` (the restoration interpretation and
substitution; `VEnv.RestoredPattern` with its stubbed `clause`, the `pat` analogue of the
source's `RestoredEliminator`), `Theory/Typing/RestorationShapes.lean`,
`Theory/Inductive/RestorationHead.lean`, `Theory/Inductive/RestorationNames.lean` (the
helpers formerly in the dropped case-eliminator files), `Theory/Inductive/CompilationMajors.lean`
(what `WF.patCtor_rigid` needs, below).

### What the nested `VInductDecl.WF`/`RecsCompiled` instance provides for the model stubs

The head-inversion model (`Theory/Typing/HeadInjectivity/Model/`) reads two kinds of facts
off an installed block; the nested instance provides them through `RestoredBlock`:

* **`WF.patCtor_rigid`** (`Model/WFFacts.lean`): the constructor of every rule of every recursor
  of an installed block is a constructor of the block or of an installed container. Stated in
  Theory as `CompiledInductive.rule_ctor_cases` (`Theory/Inductive/CompilationMajors.lean`,
  stub, Restoration-B): for `CompiledInductive env source block` and `source.RecsOf block`,
  every `ru ∈ r.rules` with `r ∈ source.recs` has `ru.ctor` a constructor constant of `source`
  or `VEnv.IsPatCtor env ru.ctor` (the container's own ι rule on that constructor is registered
  in `env`, by `ContainersInstalled` on `addInduct`: `ContainersInstalled.constructor_isPatCtor`).
  Its ingredients are the source branch's `Instance.restored_equation_major` and
  `CompilationData.constructor_name_cases`, stated there as stubs. On a `RestoredBlock` it is
  `RestoredBlock.rule_ctor_cases`. The stored-equation alternative of the source branch
  (`env.defeqs prior ∧ prior.HasConstructorMajor name`) became a registered pattern, so the
  history induction of `patCtor_rigid` recurses on the container's pattern, added strictly
  earlier.
* **`Model.PatValid.iota`** (`Model/PatSound.lean`): what the ordinary path gets from
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
  Equations, through `Restoration.equation_wf`); (iv) the auxiliary recursors' rules fire on
  container constructors at the container's parameter count (`TrRecursor.rules` reads
  `ctorParams` off the output map; `rules_ctor` finds the constructor in the constructor stage,
  where the container is installed below). Structure eta and the projection entries are
  generic: `addInduct_projections_iff` on `decl.projectionEntries`, as for ordinary blocks.

### Ownership map (wave 3)

* **Lowering**: `Nested/Lowering/**`; proves `loweringRun.WF` (`Lowering.lean`, lead-owned
  statement). Source: `Nested/Lowering/**` (15k).
* **Restoration-A**: `Nested/Restoration/Validation/**` and `Nested/Restoration/Uniform/**` (to
  create); proves the seven statements of `Validation/Passes.lean`. Source:
  `Nested/Restoration/{Validation,Uniform}/**` (8k).
* **Restoration-B**: the rest of `Nested/Restoration/**` (to create, under
  `Nested/Restoration/`), proves `nestedRestoredBlock` (`Restore.lean`) and the Theory stubs of
  `CompilationMajors.lean`. Source: `Nested/Restoration/**` minus `Equations/`, `Validation/`,
  `Uniform/` (22k), plus `Nested/Install/{Permutation,RecursorTranslations,DependencyOrder,
  ConstructorCoherence}.lean` (3.5k).
* **Equations+Install**: `Nested/Equations/**`, `Nested/Install/**`; proves `rulesWF`,
  `blockWF` (`Equations/Rules.lean`), `installedFacts` (`Install/Installed.lean`),
  `RestoredPattern.clause` (`Theory/Inductive/RestorationInterpretation.lean`),
  `instantiateParams_liftN` (`Theory/Typing/RestorationShapes.lean`). Source:
  `Nested/Restoration/Equations/**` (5.5k), `Nested/Install/{BlockCertificate,FromRun,
  Certificate,CertificateOfRun,Result}.lean` (3.5k).
* **Shared (lead)**: `Lowering.lean`, `Nested/Restoration/{LoweredRun,RestorationRun,
  Certificate}.lean`, `Nested/Install/{Result,Dispatch}.lean`, `Dispatch.lean`,
  `Verify/Environment.lean`, this file. Frozen as in wave 2: producers may add fields and
  theorems, not rename, remove or retype.

### Dependency order (wave 3)

1. **Lowering** and **Restoration-A** have nothing above them and start at once; neither reads
   the other's output (Restoration-A's statements are checker-facing, over a `CheckerEnv` the
   caller supplies).
2. **Restoration-B** consumes `NestedLoweringOutput` (the cache facts `nested_app`,
   `aux_cached`, the inverse `restore_source`) and the validation passes (the side environments'
   models are its own, built from the restoration folds; it instantiates `Passes.lean`'s
   statements with them). It can start on the folds, the kernel order and the compilation data
   immediately, requesting fields of `NestedLoweringOutput` from Lowering as needed; its
   boundary theorem lands after both. The Theory stubs of `CompilationMajors.lean` depend on
   nothing upstream.
3. **Equations+Install** consumes `RestoredBlock` (rule typing over `B.envR` and the lowered
   run's `L.rules`; the environment-side facts over `B.addInduct`). `RestoredPattern.clause`,
   `instantiateParams_liftN` and the restoration substitution depend on nothing upstream and
   can start immediately; `rulesWF`/`blockWF`/`installedFacts` land after Restoration-B's
   interface is final.

### Interface decisions (wave 3)

* The restoration inverse is stated up to `Expr.eqv` (`==`), as the source branch proved it
  (`restoredType_eqv_source`); consumers translate through `TrExprS.eqv`. The zero-auxiliary
  identity stays literal.
* `NestedLoweringOutput` is syntactic (kernel `Expr`s, `env.find?`); the typing of the cached
  occurrences comes from the validation pass `validateNestedAuxiliaries`, not from lowering.
* `RestoredBlock` carries `CompilationData` against the lowered run's generator
  (`L.recursors.signature`/`generation`), so the Equations owner transports `L.rules` along
  `compilationRestoration decl auxiliaries` without re-deriving the generator.
* `Interpretation.Sound.ordered` is `OrderedStrong` (wave 2 moved `IsDefEq.instL_r` and
  `BetaRed.simAt` there); `Sound` has a `pats` clause and no eliminator clause.
* `RestoredBlock.Installed` is a separate Prop structure so that the Install owner's work
  (`InstalledBlocks`-style reasoning on the output) does not touch the Restoration owners' data.
