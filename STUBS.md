# Stub ledger: verified inductives on the ι pattern calculus

Every `sorry` in `Lean4Lean/Theory/` (the `Lean4Lean.Theory` library builds every file under
that directory), with its owner wave. `lake build Lean4Lean.Theory`, `Lean4Lean.Experimental`,
`Lean4Lean.Tests.IotaShape` and `Lean4Lean.Tests.ShapeDecide` are green at wave 0;
`Lean4Lean.Verify` is not yet imported (waves 1 to 3) and the `lake build` default target
therefore fails on `Verify/` until wave 1. Waves follow `iota-port/PLAN-RECONCILED.md`.

| statement | file | origin | owner |
|---|---|---|---|
| `VEnv.WF.patsStrong` | `Theory/Typing/EnvLemmas.lean` | PR #43 | wave 1D (`patsStrong`), after the 0b spike |
| `VEnv.Model.PatValid.iota` (`-- WAVE 1C STUB`) | `Theory/Typing/HeadInjectivity/Model/PatSound.lean` | new: the `pat` case of `Model.sound` for the registered ι rules (see the wave 1C section) | wave 1C |
| `VEnv.WF.patCtor_rigid` (`-- WAVE 1C STUB`) | `Theory/Typing/HeadInjectivity/Model/WFFacts.lean` | `ConstructorRigidity.lean` on the source branch (`WF.installed_constructor_rigid`) | wave 1C |
| `IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean` | master | open on master; the one strengthening principle the checker uses (PORT_PLAN section 5) |
| `NormalEq.parRed` (two `sorry`s, the `extra` cases) | `Theory/Typing/ChurchRosser.lean` | master | wave 4 (confluence retargeted onto `env.pats` supersedes this file) |
| ~~`VEnv.RestoredPattern.clause`~~ (closed, wave 3 eqinst) | `Theory/Inductive/RestorationInterpretation.lean` | new: the `pat` analogue of the source branch's `RestoredEliminator.clause` | wave 3 (Equations+Install) |
| ~~`InductiveSignature.instantiateParams_liftN`~~ (closed, wave 3 eqinst) | `Theory/Typing/RestorationShapes.lean` | source `CaseReduction.lean` | wave 3 (Equations+Install) |

Not stubs but conditional results: everything through `VEnv.WF.orderedStrong` (the strong
system, substitution theorems, inversion lemmas) depends on `patsStrong`; everything through
`VEnv.WF.headInversion` and `IsDefEq.uniq` depends on `patsStrong` (through
`VEnv.WF.orderedStrong`, see the wave 1C section) and on the two wave 1C stubs.
`Injectivity.lean` has no `sorry` of its own: PR #43's `IsDefEqU.const_arity_inv` is derived
from `VEnv.WF'.inductTypeRigid` and `headInversion`.

## Wave 1C: the observation model on the ι pattern calculus

`VEnv.WF.chainHeadInjectivity` and `VEnv.WF.headSeparationModel` (`HeadInversion.lean`) are
theorems: `WF.chainHeadInjectivity_of_sound henv henv.soundEnv` and
`WF.headSeparation_of_sound henv henv.soundEnv`, with `VEnv.WF.soundEnv` from the history
induction `VEnv.WF'.envValid` (`Model/EnvValid.lean`). The model is
`Theory/Typing/HeadInjectivity/{Model,Projections,Rules}/` (22 model files, 4 projection
files, 3 rule files).

**Dependence on `patsStrong`.** The model interprets strong derivations and the extraction
strengthens the weak links of a `TypeChain` by `IsDefEq.strong` (`Model.chain_sub`,
`Model.spine_data`, `Model/Extract.lean`), which takes `VEnv.OrderedStrong` on this calculus;
the substitution theorems (`IsDefEq.substDF`, `IsDefEqStrong.substEq'`) and inversion lemmas
(`HasType.app_inv`, `HasType.const_inv`, `HasType.head_const_lookup`) the model uses take
`OrderedStrong` too. Every model lemma therefore takes `henv : env.OrderedStrong`, supplied by
`VEnv.WF.orderedStrong`, i.e. by `patsStrong`. The history induction uses nothing else from
`patsStrong`: it only ever strengthens derivations of the final environment and of the header
environments of projection entries (`ProjDeclAt`, which now records `envTypes.WF`), both through
`WF.orderedStrong`. A reorganisation that uses `patsStrong` on strict prefixes only would not
remove the use, because the extraction's input is a weak chain of the final environment; the
spike's conclusion stands (`SPIKE_PATSSTRONG.md`, section 3).

**What changed in the port.** `Obs` loses `elimRule` and gains `pat` (`Model/Interp.lean`), of
the same `RuleBind` shape as the stored-rule clause `rule`, which stays for the quotient rule
(the one `defeqs` entry with a constructor major); the reduct template `rhs = wrapLams doms
body` is read off `SimplePattern.iotaRHS'`, the generic leading arguments are
`Model.iotaLead` (bound variables for parameters, motives and minors, a non-variable dummy at
the ignored index positions) and the fields `Model.iotaFs`; the recursor's major domain
(`VExpr.RecShape`) supplies the family `I` and its levels `lsI` to the eta binding; in mode C
the clause records that the rule is the only pattern headed by its recursor. `IsCtor` reads
the constructor of a pattern (`VEnv.IsPatCtor`, `Rules/ConstructorMajor.lean`). `HTS`,
`HeadTy` and the spine lemmas are for constant heads only. `DeltaRules` gains a `pats` field
(no pattern is headed by a defined constant) and loses its inductive case (`addInduct` adds no
`defeqs`). `Model.sound` takes `PatValid` for the patterns of `E` (`Model/Sound.lean`);
`EnvValid` has fields `rule`, `proj`, `pat`. `Model/WFFacts.lean` proves the static facts
along the history: `WF'.defeqs_cases`, the quotient facts (`WF.quotConsts`, `WF.quot_rigid`,
`WF.quotMk_rigid`, `WF.quot_not_projection`), `WF.projStatic`, `WF.isCtor_rigid`,
`WF.installedCtor_resultRigid`. `EnvValid` carries `HeadsClosed` and `PatsClosed` (no later
declaration adds a rule or a pattern headed by an existing constant). Dropped: `EnvTables/`,
`Rules/{Coverage,RecursorEquations,RestoredRecursorEquations}`, `Model/{CaseRule,
CaseRuleSound,RecursorRule,RestoredRecursorRule,Singleton,FamSort,EmptyRule,TeleArity,
CtorArity,ProjMajorWF,ProjMajorRules,ProjStaticWF}` (eliminator registry and stored-equation
provenance); `IotaSoundnessLemmas.lean` is not needed (the stored-equation detour collapses to
`IsDefEq.pat`).

| statement | file | what remains |
|---|---|---|
| `VEnv.Model.PatValid.iota` | `Model/PatSound.lean` | The `pat` case of soundness for an instance `rec us args ≡ rhs us pmm fields` of a registered rule, from the semantic typing of redex and reduct (`HTS.spine`, `HTS.lamSpine`) and the static facts of the block: `VInductDecl.WF.rec_shape` (the `dsH`/`I`/`lsI` data of `Obs.pat`), `rules_ctor`, `PatsIota` and `rules_nodup` (uniqueness), the family's recorded sort (`FamSort`, `Model/FamSort.lean` on the source branch, from soundness of the environment before the block), proof binders of a singleton elimination (mode C, `Model/Singleton.lean` on the source branch), the projection entry of a structure family (eta mode). The two directions are `pat_lhs_sub`/`pat_rhs_sub_head` of `Model/RuleSound.lean` with the instance's spine in place of the λ-wrapped generic sides; `pat_rhs_sub_head` is already stated for an abstract head clause `hrule`. Estimated 1.5k to 2.5k lines. |
| `VEnv.WF.patCtor_rigid` | `Model/WFFacts.lean` | The constructor of a registered pattern is a constructor of its block or of a container block (`VInductDecl.RecsCompiled`, `VRecRule.OfEquation`, the compilation's `equation_major_cases`), hence rigid (`WF'.inductCtorRigid`). The source branch's `ConstructorRigidity.lean`. |


## Parked, not deleted

| item | where | why | owner |
|---|---|---|---|
| `Theory/Typing/Confluence/**`, `ChurchRosser`/`FullReduction`/`LevelledReduction`/`FullChurchRosser`/`HeadReduction` of the source branch, `LevelledConfluence.lean`, `NormalSubstitution.lean`, `Inductive/{RecursorData,RecursorPrefixUnfolding,QuotPrefixUnfolding,RecursorEquationHeads,RecursorEquationCoverage,SingletonReconstruction}.lean`, `Typing/{RecursorRegistration,RecursorRuleRegistration,RecursorRegistryInstallation,StoredRuleHeads,PatternCaptures,DefinitionPatterns,DefinitionRegistryInstallation,QuotLiftTelescope,QuotPropInhabitant,ConstructorRigidity,RecursorMajorFamily}.lean`, `PrefixUnfolding/`, `SingletonExtraction/` | source branch only | confluence development, to be retargeted from stored equations to `env.pats` | wave 4 |
| `Theory/Typing/HeadInjectivity/{Model,Rules,Projections}/**`, `EnvTables/`, `Typing/IotaSoundnessLemmas.lean` | source branch only | the observation model behind the two wave-0 stubs | wave 1C |
| `Theory/Typing/Interpretation.lean`, `Inductive/RestorationInterpretation.lean`, `Typing/RestorationShapes.lean`, `Inductive/RestorationHead.lean` | ported by the wave 3 scaffold (`-- WAVE 3 COMPAT`), with `PatClause` in place of the eliminator clause; see the wave 3 section | | done |
| `Theory/Typing/Strengthening/**` | source branch only | dropped (PORT_PLAN section 5) | never |
| `Inductive/Case*.lean`, `CaseSchema*`, `ProjNamesAvoid`, `RestorationProjNames`, `Typing/{CaseReduction,CaseMotive,CaseSourceSort,CaseMajorDomain,EliminatorCoherence*,SchemaStructCompat,EliminatorRestorationScope,ProjNamesTyping,ProjectionFamilyArity,ProjectionConstructorFamily,SignatureVars}.lean` | source branch only | the case-eliminator registry, dropped with `VExpr.elim` | never |
| PR #43's `ChurchRosser.lean`, `HeadReduction.lean`, `InductiveParams.lean` | kept and building | `Params.no_projections` makes them the structure-free instance; `toParams`/`inductParams` take the projection-free hypothesis | wave 4 decides whether they stay as the small-environment instance |

## Not a stub: hypotheses of the declaration judgment

`VInductDecl.WF` (`Theory/Inductive.lean`) keeps the recursor typing (`recs_wf`), the rule
typing (`rules_wf : VEnv.PatTyped`), the recursor shapes (`rec_shape`, `rule_shape`,
`rules_nodup`) and the constructor-constant clause (`rules_ctor`) as *fields* discharged by
the checker verification (waves 2 and 3), not as theorems of `RecsCompiled` as PORT_PLAN 1.4
proposed. Deriving `rules_wf` from the typing of the generated λ-wrapped equations needs
uniqueness and Π-injectivity, both stub-backed in wave 0; wave 2 may either prove it or keep
discharging the field directly from `generatorEquationWF`.

## Wave 1E (executable, tests, divergences)

No stubs: the executable and test ports add no `sorry`. Tests that do not build yet are listed
in `Lean4Lean/Tests.lean` (the manifest of the `Lean4Lean.Tests` library, which no longer globs
`Lean4Lean/Tests/`) with the wave that adds them back:

| test | needs | wave |
|---|---|---|
| `AmbientContext` (PR #43) | `Verify.TypeChecker` | 1A |
| closed-form and translation checks of `QuotInit` (removed from the ported test) | `Verify.Environment` (`Environment.addQuot_eq`, `VEnv.addQuot`) | 1B |
| `InductiveTheory`, `TypedInductiveCompilation` | re-expression for the structure `VInductDecl.WF` and `VEnv.pats` | 2 |
| `CorruptRecursorMetadata` | `Verify.Inductive.Recursor` | 2 |
| `CorruptRestoredRecursorMetadata` | `Verify.Inductive.Nested` | 3 |
| `RecursiveFieldClassification` | `Theory.Typing.Interpretation` | 3 |
| `PreludeEq` | `Verify.Inductive.Prelude.EqSyntax`; `VEnv.HasCanonicalEq` only for confluence | 4 |
| `CacheMode`, `SyntacticTranslation` | dropped with the scoped cache mode and the strengthening study | never |

## Wave 1B (environment model)

No `sorry` in `Lean4Lean/Verify/Environment/**`, `Verify/Environment.lean` or `Verify.lean`.
`lake build Lean4Lean.Verify.Environment Lean4Lean.Verify Lean4Lean.Tests.QuotInit` is green
(the `sorry`s it reports are wave 0's and wave 1A's, in `Theory/` and `Verify/TypeChecker`,
`Verify/Typing`).

| statement | file | kind | owner |
|---|---|---|---|
| `InductiveDeclPreserves` | `Verify/Environment.lean` | named hypothesis of `addDecl.WF` (not a `sorry`): a checked inductive declaration, at any fuel, preserves `VEnvs.WF` and extends every safety level | waves 2 and 3 (`addInductiveDeclaration.WF_preserves`) |

Interface notes for the waves that build on this one:

- `VEnvs`, `VEnvs.WF` (now with `blocks : InstalledBlocks safety env (ves.venv safety) .complete`),
  `VEnvs.axiom_of_choice` and `VEnvAt` live in `Verify/Environment/Model.lean`;
  `Verify/TypeChecker.lean` imports it (`-- WAVE 1B COMPAT`).
- `RecursorAlignment.lean` is gone. `Verify/Environment/RecursorCoherence.lean` keeps
  `KLikeAlignment`, `KLikeRecursor`, `QuotCoherent`, `QuotEnvCoherent`; `RecursorRulesCoherent`
  is the K clause only; `EquationHeadsCoherent` is a structure with `defeqs` (as before) and
  `pats` (every registered pattern is headed by a recursor of the map), so `rigid`,
  `rigid_quot` and `rigid_of_fresh` give the two-field `VEnv.Rigid`. The ι rule the checker
  fires is `TrEnv.pats_iota'` (PR #43), which already reads `ctorParams` off the constructor's
  own `ctorInfo` and so covers nested auxiliary recursors.
- `CheckingEnv.Valid` has no `ctorTelescopes`; `InstalledBlock` has no `eliminators` and no
  constructor telescope; `InstalledBlocks.addInduct` takes `decl.WF venv ∧ venv.addInduct decl =
  some venv'` and the K clause of the new recursors (`hrecK`) instead of the old `AddInduct`.
- `AddInduct` (PR #43's structure) has the projection stage: `stR : decl.addRecs (decl.addProjs
  envC) = some envR`, `AddInduct.envP`, `addTypesCtorsProjs`, `addTypesCtorsProjsRecs`.
  `AddInduct.ctor_find` no longer concludes `ctorParams = numParams` (false for nested blocks).
- `TrEnv'` gains `inductProjections` (the projection stage, premise `(env.addProjections
  entries).WF`), and `empty` is either map stage.

Found while porting (not fixed here, `Theory/` is frozen):

- `VEnv.InstalledBelow` (`Theory/Inductive.lean`) still installs a block through
  `VInductBlock.install`, which adds the generated rules as stored equations (`defeqs`). No
  environment built by `VEnv.addInduct` contains them, so `InstalledBelow` fails for every
  container with at least one generated rule in the environments the checker builds, and with
  it `VInductDecl.NestedFormationWF` (which requires the container to be `InstalledBelow`). The installed-blocks invariant uses
  `VEnv.InductInstalled venv decl := ∃ base installed, decl.WF base ∧ base.addInduct decl =
  some installed ∧ installed ≤ venv` (`Verify/Environment/Blocks.lean`) instead; wave 2/3 must
  restate `InstalledBelow` (or nested formation) on `addInduct`.

Parked:

| item | why | owner |
|---|---|---|
| `Verify/CanonicalEq.lean` | needs `Verify/Inductive/Prelude/EqSyntax.lean` and a `VEnv.HasCanonicalEq` whose `Eq.rec` rule is a pattern; `addDecl.WF` no longer needs it | wave 4 |
| `Verify/QuotInit.lean` | replaced by PR #43's `Verify/Environment/Quot.lean` | never |

## Wave 2 header (`Context.lean`, `Context/**`, `Formation.lean`, `Header/**`)

Closed: all four header stubs (`AddInductive.checkInductiveTypes.WF`,
`CheckedHeaders.Describes.headerCertificate`, `AddInductive.declareInductiveTypes.WF`,
`TrInductDeclCore.sourceNames_nodup`). No `sorry` in `Context.lean`, `Context/**`, `Header/**`;
the one in `Formation.lean` is Install's `ConstructorCertificate.withRecs`.

Two more corrections of the scaffold's header interface (both were false as stated):

* `HeaderParameterContext.paramsTr` placed the parameter variables at `.bvar i`; the
  continuation of `checkInductiveTypes` runs beneath the index binders of every family (the loop
  nests them), so they are `.bvar (depth + i)`.
* `declareInductiveTypes.WF` takes `decl.isUnsafe = isUnsafe` beside `Describes` (which does not
  constrain `isUnsafe`), since `HeaderEnvironment.isUnsafe` asserts it.

Interface change (statement of a boundary theorem): `AddInductive.declareInductiveTypes.WF` as
scaffolded was false. Its postcondition built a `ContextWF` over the header environment, whose
`CheckingEnv.Valid` needs every name a header lists to be absent or a constructor of that
header, but `declareInductiveTypes` only checks the header names (a source constructor named
like an existing definition, or like a family of the same block, passes it). The executable
checks constructor names only in `declareConstructors`, after `checkConstructors`. The
postcondition is now `headerEnv.constants.WF ∧ (ConstructorNamesAbsent indTypes headerEnv → ∀
decl, Describes → Nonempty HeaderEnvironment)`, as on the source branch
(`declareInductiveTypes.headersWF`); the consumer (`constructorPhase.WF`) obtains
`ConstructorNamesAbsent` from a successful `declareConstructors`
(`AddInductive.declareConstructors.namesAbsent`, `Header/Installation.lean`), as the source
branch's `formationCoreWF` does (case on `checkConstructors`, then on `declareConstructors`).

Fields added to the header interface (consumers may read them): `CheckedHeader.formation`
(the loop's `HeaderFormation`); `HeaderPhase.{loopHeaders, headers_eq, cache, suffix,
ambientParams}` (the loop's accumulator and parameter invariants); `HeaderEnvironment.
{sourceStatsWF, sourceHeaderParams, statsWF, headerParams, parameterScopeEq}` (the source
branch's `HeaderStatsWF`, built by `HeaderPhase.statsWF` for every described declaration);
`ContextSemantics`/`RecursorContextWF` carry `shapes`/`iota` in place of the cache mode, with
`RecursorContextWF.checkerEnv`. New: `InstalledHeaders` and
`AddInductive.declareInductiveTypes.installedWF` (the header environment before the declaration
is known, as the source's `declareInductiveTypes.headersWF`), `InstalledHeaders.toHeaderEnvironment`.
`declareRecursors.checkRecursorType.WF` (`Context.lean`) now takes a `CheckerEnv` and no cache
mode. The source's top-level `TypeAnnotations.lean` is `Context/TypeAnnotations.lean`; the
helpers the source kept in `Theory/Typing/IotaSoundnessLemmas.lean` and used here
(`VerifyInductive.VExpr.takeForalls_rebuild`) are in `Formation.lean`, with the rest of the
source's `Formation.lean` (`IndexedPrefix`, `List.Forall₂.targets_eq_of_unique`,
`VEnv.addConstVals_append`, ...).

## Wave 2 ctor (`Verify/Inductive/Constructor/**`)

Closed: both constructor stubs (`CheckedFormation.signature`, `AddInductive.constructorPhase.WF`).
No `sorry` in `Constructor/**`; no named stub left. `lake build`, `Lean4Lean.Tests`,
`Lean4Lean.Experimental` green; `--fresh Init.Prelude` (1975) and `--fresh Init.Core` (3953) pass.

* `CheckedFormation.signature`: the family table is read off the header certificate's type
  shapes (`HeaderCertificate.familyTelescope`), the constructors off the checked tails
  (`CheckedFormation.tails`, new field). The empty declaration gets the empty signature.
* `constructorPhase.WF`: `declareInductiveTypes.installedWF` (header), then the constructor check
  `AddInductive.checkConstructors.WF` (`Constructor/CheckRun.lean`: the declaration is the one
  whose constructor types are the raw translations of the run, `accumulatesRawTargets`; the
  certificates come from `checkConstructors.loopTypes.refinesChecked` and
  `loopTypes.ownerNormalFormsWF`), then `declareConstructors` (`Constructor/Declare.lean`:
  `insertConsts` of the `constructorInfo`s, fresh, distinct, nonprimitive) and the constructor
  environment (`Constructor/Install.lean`: `CheckingEnv.Valid` via
  `InstalledBlocks.addCtorStage`, recursor shapes and ι rules, projection-stage `WF` via
  `VEnv.WF.inductProjections`, closure, `InductInfosFromDecl`, parameter alignment).

Interface changes: `constructorPhase.WF`'s postcondition is `∃ R : ConstructorCheck …, R.classes
= out.2` (the scaffold's `Nonempty … ∧ ∀ R, R.classes = out.2` was unprovable: nothing pins an
arbitrary `R`'s classes); `Install/Ordinary.lean` adapted (`-- WAVE 2 COMPAT (ctor)`).
`RecursorInput.constructorTails` is stated over `headers.statsWF.parameterScope`
(`-- WAVE 2 ctor COMPAT`). Fields added: `CheckedFormation.tails`; `ConstructorCheck.{ivals_eq,
ctor_numParams, parameterPrefixes, constructorTails, ownerNormalForms}`. Definitions the
recursor phase imports from `Constructor/Tails.lean`: `ParameterPrefix`, `ParameterSegment`,
`Expr.ForallSpine`, `CheckedConstructorParameterPrefix`, `ConstructorParameterPrefixes`,
`CheckedConstructorTailAt`, `ConstructorTails`, `ConstructorOwnerNormalForm(At/s)`,
`ConstructorScopedTelescope` (= the header's `ScopedHeaderTelescope`).
`Constructor/OwnerNormalForms.lean` imports the recursor agent's
`Recursor/Context/FVarArrays.lean` (whose import closure stays inside
`Constructor/{Tails,Positivity,PrefixUtilities,CheckedFormation,SourceSignature}`).
The source's `Header/Declaration.lean` is not ported: `CheckedHeaders.declOf` selects the
declaration from the checked headers and the raw constructor rows.

## Wave 2 rec (`Verify/Inductive/Recursor/**`, `Rules/RuleSyntax.lean`, `Rules/FromTemplates.lean`)

Closed: `RecursorInput.recursorPhasesWF` (the boundary theorem) and
`InductiveSignature.VRecRule.OfEquation.ofTr`. `Recursor/**` contains no `sorry`; the boundary
theorem's only `sorryAx` sources are the foundation stubs `VEnv.WF.patsStrong`,
`VEnv.Model.PatValid.iota`, `VEnv.WF.patCtor_rigid`, `VEnv.IsDefEqU.weakN_iff`. Ported: the source
branch's `Recursor/**` (65 files, about 41.8k lines) and `Rules/{RuleSyntax,FromTemplates}` (2.5k,
lead's ruling: they sit inside the recursor chain).

Structure: `RecursorInstallation` (`Recursor/Installation.lean`) is the source branch's
`RecursorCheck` (extends `RecursorConstruction`), produced by `RecursorInput.recursorInstallationWF`
(the source's run theorem); `Recursor/Recs.lean` reads the kernel recursors `rvals` and the model
recursors `recs` (rules: `ctorParams := decl.nparams`, `rhs :=` the generated equation's) off it,
with every shape clause of `VInductDecl.WF`; `Recursor/Checking.lean` proves the checking
invariant at the recursor stage (`InstalledBlocks.addCtorStage` from the source blocks, install's
`recursorShapesOf`); `RecursorInstallation.toRecursorCheck` (`Recursor/Check.lean`) assembles the
frozen interface. The rule coverage is the rule phase's `RecursorInstallation.rulesCovered`
(`Rules/Coverage.lean`).

Interface changes (all agreed with the lead or the owner):
* `RecursorCheck` gained `installation : RecursorInstallation R outEnv` with
  `installation_{elimLevel,kTarget,outVEnv,rvals,signature,generation,recs,rvals'}` and
  `rules_ctorParams`.
* `RecursorCheck.trRecs` and PR #43's `AddInduct.recs` translate recursor types in the projection
  stage (`R.envP`, `decl.addProjs envC`), where the executable checks them (`-- WAVE 2 rec COMPAT`
  in `Verify/Environment/Basic.lean`, `Verify/Environment/Lemmas.lean`, `Install/Rebase.lean`).
* `VRecRule.OfEquation.ofTr` takes the index-count side condition `harity`
  (`Models.constructorArity`); `ofTrModels` discharges it from a modelling signature.
* `RecursorInput.literalDisjoint` (install's field) supplies positivity's literal side condition.

Recursor-side homes of source content that lived elsewhere on the source branch:
`Recursor/Inputs.lean` (the source `ConstructorCheck`'s header-side members on `RecursorInput`:
`sourceContext`, `statsWF`, `parameterScope`, `recursorHeaders`, `headerLE`/`ctorLE`/`sourceLE`,
`find?_origin`, `headerInfo_find`, `ctorInfo_find`, `modelCtorAt`), `Recursor/SourceAlignment.lean`,
`Recursor/Signature/RecursorTypeTelescope.lean` (from `Nested/Restoration/ExprReplace`),
`Recursor/Signature/SourceReplay.lean` (the replay-based source signature of the source
`Constructor/{SourceSignature,CheckedFormation}`), `Recursor/Entries/Metadata.lean` (from
`Install/Metadata`). Dropped: the case-eliminator and telescope-certificate lemmas
(`addEliminators`, `SourceCtorsCertified`, `CtorTelescopeAt`), `RecursorCheck.alignmentOfTr`
(replaced by install's `recursorShapesOf`), the old `AtomicAddConstants` helpers; the constructor
loop's production (owner normal forms, parameter prefixes) moved to `Constructor/**`.

## Wave 2 rules (`Verify/Inductive/Rules/**`)

`RecursorCheck.generatedRuleTranslation` is proved. The source branch's `Rules/**` is ported onto
the recursor installation (`RecursorInstallation`, the source `RecursorCheck`): `Rules/{Alignment,
MinorContext,MinorPremise,Motive,RecursiveCallScope,RecursiveCall,RecursiveApplication,
EquationTranslation,RecursiveBody,RecursiveResults,Rhs,Lhs,EquationWF,LhsTranslation,Translation}`,
with the assembly in `Rules/Coverage.lean` (`RecursorInstallation.rulesCovered`, which the recursor
phase uses to build `TrRecursor`, and `equationsWF'`). Support ported from other source
directories into `Rules/`: `ContextLemmas.lean` (`rebaseCommonSuffix`, from `Install/Lookups`),
`SameForallPrefix.lean` (from `Nested/Restoration/ParameterOpening` and
`Nested/Lowering/ParameterOpening`), `InstallationLemmas.lean` (from `Install/BlockCertificate`).
`rules_wf : PatTyped` is the restatement of the generated equations' `VDefEq.WF`
(`Instance.equation_patTyped`, `Rules/IotaPatTyped.lean`; `RecursorCheck.rules_wf_of`,
`Rules/RulesWF.lean`). `RecursorCheck.rules_ofEquation` gives `VInductDecl.RecsOf`'s rule clauses.
Foundation changes met in the port: `.ordered` → `.orderedStrong` where `TrExprS.weakBV`/
`VLCtx.IsDefEq.refl` now take `OrderedStrong`; constructor lookup through `R.core.ctorsAdded`.
The rule chain's only `sorryAx` dependencies are the foundation's `VEnv.WF.patsStrong`,
`Model.PatValid.iota`, `WF.patCtor_rigid`, `IsDefEqU.weakN_iff`.

No named stub remains in `Rules/**`. `RecursorCheck.rulesCovered`/`equationsWF` are read off the
installation (`installation_*`); `ruleCtorParams` is the Recursor agent's `rules_ctorParams` with
`models.nparams`.

`Rules/RuleSyntax.lean` and `Rules/FromTemplates.lean` are the Recursor agent's (lead's decision:
the source's `Recursor/**` imports them).

## Wave 2 install (`Install/**`, `Primitive/**`, `Prelude/**`, derived `RuleTranslations` facts)

No `sorry` left in the install/primitive/prelude directories. Closed: `BlockCertificate.installedBlocks`
(`hpres`), `rebase`, `extendSafeExact`, `extendUnsafeExact`, `RecursorCheck.blockCertificate`,
`Kernel.Environment.checkDuplicatedUnivParams.WF`, `RuleTranslations.blockWF`/`compilesTo`/`recsOf`
(`recsOf` through the rule phase's `rules_ofEquation`), `ConstructorCertificate.withRecs`,
`checkPrimitiveInductive_eq_true_iff`, `loweringRun.primitiveNoop`, the recursor-names-not-primitive
`sorry`, `AddInductive.constructorPhase.primitiveWF`, and wave 1A's `VEnvAt.recursorShapes`
(`Verify/TypeChecker.lean`, now read off the installed-block descriptors). `Prelude/{EqSyntax,EqReady,Eq}`
are ported (the `QuotReady` half: `Environment.addInductive.preludeEqExtensionWF`; the `HasCanonicalEq`
half stays with `Tests/PreludeEq`, wave 4).

Interface changes (all marked `-- WAVE 2 install COMPAT`):
* `Verify/Inductive/HeaderData.lean` (new, shared): `LocalContextWF` (`ContextWF` with `checking :
  CheckingEnv`, no `HasPrimitives`/`shapes`/`iota`) and `HeaderData` (`HeaderEnvironment` with
  `context : LocalContextWF`, without the header context's `parameters`), `HeaderEnvironment.toData`.
  The header-only environment of `Bool`/`Nat` violates `HasPrimitives`, so no `ContextWF` exists there.
* `Verify/Inductive/RecursorInput.lean` (new, shared): `RecursorInput` = `ConstructorCheck` with its
  `CheckedFormation` fields flattened under the same names and `headers : HeaderData`;
  `ConstructorCheck.toRecursorInput`, `CtorInstall.toRecursorInput`. `RecursorCheck`,
  `RuleTranslations`, `RecursorInput.recursorPhasesWF` (renamed from `ConstructorCheck.recursorPhasesWF`),
  `blockCertificate` and `OrdinaryInstallation` are indexed by `RecursorInput`.
* `Constructor/{Checked,Install}.lean`: `ConstructorsChecked` and `CtorInstall` are over `HeaderData`;
  `CtorInstall.nprim` is replaced by `hasPrimitives` (of the constructor model) and `safePrimitives`
  (of the constructor environment); the ordinary path proves both from nonprimitive names
  (`CtorInstall.ordinaryPrimitives`); shapes/iota/equation heads/quotients and the parameter context come
  from the source context. `Constructor/CheckRun.lean`: `checkConstructors.WF` concludes
  `ConstructorsChecked H.toData`.
* `Verify/Environment/Blocks.lean`: `RecursorShapes` moved here (from `TypeChecker/CheckerEnv.lean`);
  `InstalledBlock.WF` gains `shapes : ∀ r ∈ B.recursors, visible → RecursorShapesAt env.constants venv r`;
  `addBlock`/`addInduct` take `hrecShapes`, `addCtorStage` takes it as an auto-discharged argument.
  `InstalledBlocks.recursorShapesCoherent` (`TypeChecker/CheckerEnv.lean`).
* `RecursorInput`, `ConstructorCheck` and `CtorInstall` gain `literalDisjoint` (positivity's literal
  side condition, `AvailableLiteralDisjoint`, in the recursor phase's context; requested by rec).
* `BlockCertificate` gains `compiled` (a well-formed compiled block, for `rebase`), `newUnsafe` (inserted
  constants carry the declaration's `isUnsafe`) and `recShapes`; `rebase` takes `ves.WF env` and
  `decl.isUnsafe = false`. `RuleTranslations.compilesTo`/`recsCompiled`/`recursorsWF` take
  `indTypes.toList ≠ []`.

Owed by wave 3: every caller of `InstalledBlocks.addInduct` (the nested installation) supplies
`hrecShapes`, i.e. `RecursorShapesAt` of each new recursor, auxiliary recursors included (their majors are
containers at specialized arguments, so `recursorShapesOf`, which reads the major off `MajorApp` and the
rules' constructors off the source declaration, does not cover them).

## Wave 3 eqinst (`Nested/Equations/**`, `Nested/Install/**`, two Theory stubs)

Closed: `InductiveSignature.instantiateParams_liftN`, `VEnv.RestoredPattern.clause`,
`RestoredBlock.rulesWF`, `RestoredBlock.blockWF`. `RestoredBlock.installedFacts` is now proved
from the stub `kernelFacts` (below). The nested `InstalledBlocks.addInduct` call is inside
`installedFacts`. Its `hrecShapes` is `RestoredBlock.recShapes` and its `hrecK` is `recK` (both
cover every new recursor, auxiliary ones included). `BlockCertificate.compiled` is
`RestoredBlock.compiledWF` and `newUnsafe` is `RestoredBlock.newUnsafe`.

* `RestoredPattern.clause` gains three fields of `VEnv.RestoredPattern`: `wf : envS.WF`,
  `recursorNotHead`, and `templateTyped` (the interpreted reduct template is typed). The
  `PatClause` gives the typing of the interpreted redex only. The interpreted reduct is a
  β-*expansion* of the restored reduct, so its typing has to come from the template, and
  uniqueness of typing (`IsDefEq.uniq`, hence `wf`) turns the forward `SimAt` around. Nothing
  constructs a `RestoredPattern` yet. `rulesWF` does not need it: the substitution goes from the
  lowered *recursor* stage, which has no patterns of the block.
  (Fields accepted by the lead.) Who constructs a `RestoredPattern`: nobody on the current
  route. It is needed only if a restoration substitution is built from a lowered environment
  that already registers the block's ι rules (the lowered rule stage or a later one). Its
  `PatClause` then has to be discharged per lowered rule, and whoever builds that
  substitution constructs it: `wf` from the target's `VEnv.WF`, `recursorNotHead` from
  `CompilationData.recursorName_not_head` (`RuleAlignment.lean`), and `templateTyped` from
  the typing of the interpreted template (`Restoration.equation_wf` on the lowered equation).
* `rulesWF` is `VEnv.patTyped_iota_of_wrapped` on the restored equation of each rule.
  `RestoredBlock.ruleEquation` (`Nested/Equations/RuleAlignment.lean`, new) recovers the exact
  ι counts from the restored generated equation (`rules_ofRestoredEquation`), the restored
  recursor type (`rec_shape`'s arity and motive-application conjuncts, *not* `MajorApp`) and
  the reduct's λ-arity (`rule_shape`). `envP_wf`/`envR_wf` (`Rules.lean`) are proved from the
  restored block's fields.
* `installedFacts` (WAVE 3 eqinst COMPAT) takes `TrEnv c.safety c.env Hc.venv`, the base's
  complete `InstalledBlocks`, and its `ConstructorParameterAlignment`.
  `Nested/Install/Dispatch.lean` passes `wf.tr wf.blocks wf.constructorParameterAlignment`.
  `ContextWF` has the blocks at `.headers` only, which `InstalledBlocks.addInduct` cannot
  extend.

| statement | file | what remains |
|---|---|---|
| `RestoredBlock.restoredEquationsWF` | `Nested/Equations/Rules.lean` | `∀ df ∈ B.block.rules, df.WF B.envR`: the restoration substitution from `L.recursors.outVEnv` into `B.envR` (source `Equations/WF.lean`: `restoredEquationSubstitution`, `restoredEquationsWF_of_substitutionPremises`, with `ProjNames`, `Equations/AuxiliaryConstructors`, `ProjectionRenaming`). Needs `B.run`, restB's port of `NestedRun`/`RestoredBlockBase`, not yet a field of `RestoredBlock`. `blockWF` and `rulesWF` reduce to it. |
| `RestoredBlock.kernelFacts` | `Nested/Install/Installed.lean` | `KernelFacts B`: `MutualInductivesClosed`, `ConstructorOwnersPresent`, `InductInfosFromDecl`, the recursor majors, the constructor parameter alignment, and `HasPrimitives`/`safePrimitives` of the output, all from the restoration folds of `B.run` (source `RestoredBlockCertificate.inductInfosFromDecl`, `NestedRestorationFolds.constructorOwnersPresentOfContext`, `Install/ConstructorCoherence.lean`). |

Flagged: `VExpr.RecShape`'s `MajorApp` conjunct (`VInductDecl.WF.rec_shape`,
`RestoredBlock.rec_shape`) is false for the auxiliary recursors of a nested block. Their major
is the container applied to the specialization arguments, not to parameter variables.
Reported to restB and the lead. Decided by the lead: `MajorApp` is weakened to a head family
constant applied to parameter-closed arguments followed by index variables (restB implements it). `ruleEquation` uses
only the arity and motive-application conjuncts, so it is unaffected.

Pending: `InductInstalled` is gaining the compiled block
(`∃ block, decl.CompilesTo base block ∧ decl.RecsOf block ∧ block.WF base`, lowering, in
`Verify/Environment/Blocks.lean`). The `InstalledBlocks.addInduct` call in `installedFacts`
will supply it from `RestoredBlock.compiledWF`.

## Wave 3 restB (`Nested/Restoration/**` outside `Validation/`, `Uniform/`; `CompilationMajors.lean`)

Closed: `Instance.restored_equation_major`, `CompilationData.constructor_name_cases`,
`ContainersInstalled.constructor_isPatCtor`, `CompiledInductive.rule_ctor_cases`
(`Theory/Inductive/CompilationMajors.lean`, no `sorry`; with the ported helpers
`Restoration.expr_wrapLams_parts`, `headName_of_mem`, `CompilationData.headName_source`,
`CaseCompilationData.headName_auxiliary_constructor`/`directFamily_restored_constructor_names`,
`CompilationData.constructor_equation`, `CompiledInductive.constructor_equation`/
`equation_major_cases`, `VDefEq.HasConstructorMajor.ofEquation`).

Ownership change (lead-approved): the restoration is one dependency chain across the scaffold's
map, so Restoration-B ports the source files on the path to `RestoredBlock` in source topological
order whoever the map assigned them to: besides `Nested/Restoration/**` (minus Restoration-A's
`Validation/{Checks,Stripped*,ParameterPrefix,ParameterScopes,Result}` and `Uniform/**`) also
`Install/{AddInduct,FromRun,Certificate,RunView,Permutation,DependencyOrder,RecursorTranslations,
ConstructorCoherence}`, `Equations/{SourceIotaFamilies,SourceIota,RuleRhs}` and the translation
half of `Equations/{RestoredRules,GeneratedGuard}` (source paths and names kept); the side
environments' models (source `Validation/{Environment,ConstructorEnvironment}`) live in
`Nested/Restoration/SideEnvironment/`. Equations+Install keeps the typing side.

`VExpr.RecShape` was false for nested blocks as inherited from #43 (same family as
`rules_own_params`/`rec_counts`/`recs_over_block`): its `MajorApp` required the major's leading
arguments to be the recursor's parameter variables, which a restored auxiliary recursor
(`Tree.rec_1`, major `List (Tree α)`) violates. Lead decision: weaken `MajorApp` (Restoration-B,
`-- WAVE 3 COMPAT (restB)`), in progress.

## Wave 3 Restoration-A (`Nested/Restoration/Validation/**`)

The seven statements of `Validation/Passes.lean` are proved; Restoration-A adds no stub.
Three statements gained premises, because the passes run the checker without checking them
or because the scaffold form was circular:

* `validateSourceConstructorTypes.run.WF` takes the closedness of the constructor types
  (`SourceSyntaxChecks.ctorTypesClosed`, `Validation/Checks.lean`, provides it).
* `validateNestedAuxiliaries.WF` takes the checker context `mlctx` of the lowering's
  parameters (`mlctx.WF`, `mlctx.lctx = res.lctx`, freshness for the checker's name generator,
  the cached occurrences scoped in it) and concludes the typing of every cached occurrence in
  it. The context is a lowering fact: `NestedLoweringOutput.params_opening` with
  `LoweringParamOpening.toMLCtx` (`Validation/ParameterPrefix.lean`).
* `stripRecursorRules.checkingValid` (and the new `stripRecursorRules.checkerEnv`, the
  `CheckerEnv` that `validateRestoredRecursorRules.check.WF` consumes) is stated over a
  rule-free `AddInduct` into the stripped map and the rule-free facts `RuleFreeStage`
  (`Validation/Stripped.lean`): the projection stage's `VEnv.WF`, the recursor types, the
  block's names not primitive, the restored header facts, the K clause and shapes of the new
  recursors at the recursor stage. The scaffold form took the output's `AddInduct` and
  `CheckingEnv.Valid`, which contain the rule translations the pass establishes. Restoration-B
  produces the `RuleFreeStage` (agreed).

`Nested/Restoration/Uniform/**` (parameter uniformity of the lowered recursors, consumed by
Restoration-B) is ported as far as Restoration-B's run is available: `Uniform/{Recursors,
Generic,Heads,Base,Lowered,Run,Whnf}.lean`. Pending on Restoration-B's `ContainerSpecializations`
(`NamePrefix`), `restorationTablesRestoring`, `CompilationDataConstructors`/`Commutation` and
`NestedInstalledRun`: `NestedRun.auxHeadsFacts`, `envParamUniform`, `whnfPreservesParamUniform`,
`recursorParamUniform_of_wfCore`, the `NestedRun` part of `Uniform/Declarations` and
`Validation/ParameterScopes`. `NestedRun.envParamUniform` will take `LoweredView.Nonprimitive`
(the lowered names passed `checkName` without primitive permission; the target's lowered run
does not record it). Source `Validation/Result.lean` is superseded by `RestorationRun`.

## Wave 3 lowering

Statement changes to `NestedLoweringOutput`/`loweringRun.WF` (`Verify/Inductive/Lowering.lean`,
`-- WAVE 3 COMPAT (lowering)`, approved by the lead):

1. `loweringRun.WF` takes `wf : ves.WF env`: `nested_app`'s `FVarsIn` and the container
   parameter count of a sibling `J ∈ I.all` need `EnvironmentTypesClosed`/`MutualInductivesClosed`
   (auxiliary constructor types instantiate kernel constructor types). The ordinary branch's
   consequences (`loweringRun.types_nonempty`, `loweringRun.ordinary_types_eq_source`) stay
   hypothesis-free through `loweringRun.sourceShape`.
2. `lctx_params` reads `res.params.toList.reverse.map (·.fvarId!) = res.lctx.fvars`
   (`LocalContext.fvars` is most recent first).
3. `aux_fresh` is `env.find? t.name = none ∧ ∃ i, t.name = .num `_nested i`; new field
   `aux_ctor_names` (an auxiliary constructor is a container constructor renamed under the
   auxiliary family). Disjointness from the source family names (a source family may be named
   `_nested.1`) and constructor freshness (kernel constructor names need not extend their
   family's name) are not lowering facts; they come from the lowered installation.
4. `restore_source`'s premise `LoweredAuxiliariesInstalled` is replaced by
   `RestoreSourceDisjoint res loweredEnv sc.type` per source constructor (the source branch's
   premise; `LoweredAuxiliariesInstalled` does not exclude a source constant registered in
   `loweredEnv` as a constructor of an auxiliary family). Restoration-B establishes it from the
   lowered installation (`RestoreAuxConstructorsFresh`, `AddConstants`), as the source did.
5. `loweringRun.WF` also takes `hsources : SourceSyntaxChecks env types`, and
   `loweringRun.types_nonempty`/`loweringRun.ordinary_types_eq_source` take `wf` and `hsources`
   (`Dispatch.lean`'s two calls and the nested dispatch updated): the ported refinement
   (`ElimNestedInductive.run'.translationClosed`) carries a closing context that exists only for
   closed source types.
6. New fields: `params_opening` (the parameter opening of the first source header, for the
   parameter metacontext of `validateNestedAuxiliaries.WF`, source `resultParameterMLCtx`) and
   `closed : NestedLoweringOutputClosed …` (the source branch's run relation, so restoration
   lemmas port verbatim). `SourceBVarClosed` and `RestoreSourceDisjoint` are defined in
   `Nested/Lowering/Refinement.lean` (imported by `Lowering.lean`); the source branch's
   `NestedLoweringOutput` def is `NestedLoweringRun` (`Nested/Lowering/Output.lean`), its inductive
   `SourceSyntaxChecks` is `SourceSyntaxChecked`.

7. (Lead's option (B).) `VEnv.InductInstalled` (`Verify/Environment/Blocks.lean`) also records
   a well-formed compiled block of the declaration (`∃ block, decl.CompilesTo base block ∧
   decl.RecsOf block ∧ block.WF base`), so that an installed declaration is a container of
   nested formation (`VEnv.InductInstalled.installedBelow : … → VEnv.InstalledBelow venv decl`).
   `InstalledBlocks.addInduct`'s `hadd` and `VEnv.InductInstalled.of_addInduct` take it; the
   ordinary installer supplies `BlockCertificate.compiled` (`Install/BlockCertificate.lean`,
   also replayed in `rebase`), `SourceAddInduct.inductInstalled` takes it as a hypothesis
   (`Install/Result.lean`). The nested installer goes through `BlockCertificate` and supplies it
   from `RestoredBlock.compiledWF` (Equations+Install).

`loweringRun.WF` is proved (no stub left in `Lowering.lean` or `Nested/Lowering/**`): each field
in `Nested/Lowering/Assembly.lean` from `NestedLoweringOutputClosed`
(`ElimNestedInductive.run'.translationClosed`), over the source branch's lowering refinement
ported under `Nested/Lowering/` (`Refinement`, `ParameterOpening`, `Recognition`, `Expression`,
`Queue`, `AuxiliaryFamilyPositions`, `Output`, `Ordinary`, `Restore/{ExprReplace,ParameterOpening}`;
new: `Counts` for `types_length`). `Nested/Lowering/Expansion/**` and `AuxiliaryFamilies`,
`AuxiliaryConstructors`, `OccurrenceTyping` are ported too, without stub: the nested expansion for
`RestoredBlock.formation` is `RecursorInput.nestedExpansionData` / `RecursorInput.nestedFormationWF`
(`Nested/Lowering/Expansion/Data.lean`), over the lowered run's `RecursorInput`
(`LoweredRun.input`), the lowering run and the restoration side's source facts. Adaptations:
the source branch's `OrdinaryConstructorCheck`/`HeaderEnvironment` arguments became
`RecursorInput`/`HeaderData`, the eliminator cases of the expansion relations are gone, and
`InstalledBelow` facts are read through `addInduct`'s stages (`VEnv.addInduct_stages`).

## Wave 3 scaffold (`Verify/Inductive/Nested/**`, the nested branch's interface)

`lake build` (default targets), `Lean4Lean.Tests` and `Lean4Lean.Experimental` are green with
`Verify/Inductive/Nested/**` imported by `Verify/Inductive.lean` and by `Verify/Environment.lean`
(through `Nested/Install/Dispatch.lean`). `NestedInductivePreserves` is the theorem
`nestedInductivePreserves`; `addDecl.WF` has no hypothesis. The interface, the ownership map
(Lowering / Restoration-A / Restoration-B / Equations+Install) and the dependency order are the
nested section of `Lean4Lean/Verify/Inductive/README.md`. Every `sorry` of the scaffold is one of
the named stubs below (`-- WAVE 3 STUB (owner)` in the source); the two `Lowering.lean` stubs
of wave 2 are now consequences of `loweringRun.WF`.

| statement | file | what it is on the source branch | owner |
|---|---|---|---|
| `loweringRun.WF` | `Verify/Inductive/Lowering.lean` | `NestedLowering`/`NestedLoweringOutputClosed` (`Nested/Restoration/SourceTranslations.lean`, over `Nested/Lowering/**`): `ElimNestedInductive.run.refines`, `LowerNextStep`, `NestedAuxMapModels`, `ConstructorRestorationInverse.restoredType_eqv_source`, `types_eq_source_of_aux2nested_size_eq_zero` | Lowering |
| `validateSourceConstructorTypes.run.WF` | `Verify/Inductive/Nested/Restoration/Validation/Passes.lean` | `Validation/Checks.lean` (`validateSourceConstructorTypes.WF`) with `checkType.WF`/`ensureSort.WF` | Restoration-A |
| `validateRestoredRecursorTypes.check.WF`, `.run.WF` | same | `Validation/Checks.lean`, `Validation/Environment.lean` (`ValidationEnvironment`) | Restoration-A |
| `validateRestoredRecursorRules.check.WF`, `.run.WF` | same | `Validation/Checks.lean`, `Validation/StrippedEnvironment.lean` | Restoration-A |
| `validateNestedAuxiliaries.WF` | same | `Nested/Lowering/Basic.lean`'s `validateNestedAuxiliaries.WF` (`NestedBindingContextWF`, `NestedOccurrencesTyped`) | Restoration-A |
| `stripRecursorRules.checkingValid` | same | `Validation/StrippedEnvironment.lean`, `Validation/StrippedRecursorShapes.lean` (overwriting a well-formed `SMap`, `Aligned` under same-type replacement) | Restoration-A |
| `nestedRestoredBlock` | `Verify/Inductive/Nested/Restoration/Restore.lean` | `nestedValidatedRawSourceWF` + `NestedRun.assemblyOfRun` (`Install/Certificate.lean`, `Install/CertificateOfRun.lean`) + `RestoredBlockCertificate.blockCertificate` (`Install/BlockCertificate.lean`): the restoration folds (`Steps.lean`), the restored source declaration (`SourceDeclaration`, `SourceTranslations`, ...), the specialization tables (`Tables`, `TableAgreement`, `ContainerSpecializations`), the restored recursors (`Recursors`, `RecursorRenaming`, `RecursorShape`, `RecursorAlignment`), the compilation data (`CompilationData*`), the kernel order (`Install/Permutation`, `DependencyOrder`, `RecursorTranslations`) | Restoration-B |
| `RestoredBlock.rulesWF` | `Verify/Inductive/Nested/Equations/Rules.lean` | `Equations/WF.lean` (`restoredEquationSubstitution`, `restoredEquationsWF_of_substitutionPremises`), `Equations/{RestoredRules,RestoredRulesBase,GeneratedGuard,RuleRhs,SourceIota*}.lean`, restated as `PatTyped` (`Rules/IotaPatTyped.lean`) | Equations+Install |
| `RestoredBlock.blockWF` | same | `Restoration.equation_wf` along the substitution, `RestoredBlockCertificate.blockCertificate`'s `rulesWF` | Equations+Install |
| `VEnv.RestoredPattern.clause` | `Theory/Inductive/RestorationInterpretation.lean` | new: the `pat` analogue of `RestoredEliminator.clause` (the interpreted redex is β-convertible to a redex of the restored rule, `Agrees.expr_simAt`, `BetaRed.mkApps_wrapLams`) | Equations+Install |
| `InductiveSignature.instantiateParams_liftN` | `Theory/Typing/RestorationShapes.lean` | `CaseReduction.instantiateParams_liftN` | Equations+Install |
| `RestoredBlock.installedFacts` | `Verify/Inductive/Nested/Install/Installed.lean` | `Install/BlockCertificate.lean` (`inductInfosFromDecl`, `cover`, `constructorOwnersPresentOfContext`), `Install/FromRun.lean` (`assemblyBaseValid`), `Install/ConstructorCoherence.lean` (`constructorParameterDomainsDefEqOfSource`) | Install |

Owed to wave 3 by wave 2, now carried by the interface: `InstalledBlocks.addInduct`'s
`hrecShapes` is `RestoredBlock.recShapes` (every new recursor, auxiliary recursors included,
whose majors are containers at specialized arguments; `recursorShapesOf` does not cover them,
so Restoration-B ports `Restoration/RecursorShape.lean` and `Validation/StrippedRecursorShapes.lean`);
`BlockCertificate.compiled` is `RestoredBlock.compiledWF`, `newUnsafe` is `RestoredBlock.newUnsafe`.

For the model stubs (lead's request): `CompiledInductive.rule_ctor_cases` is what
`WF.patCtor_rigid` reads (the second alternative is `VEnv.IsPatCtor env ru.ctor`, the
container's own registered rule, so the history induction recurses on an earlier pattern);
`Model.PatValid.iota` reads `RecsCompiled` as `⟨block, .intro compiled containers, recsOf⟩` with
`CompilationData.equations`/`recursors` (restorations of the generator's equations and
recursors, `RestoredBlock.rules_ofRestoredEquation`) and `blockWF` (equation typing in the empty
context); README nested section, "What the nested instance provides".

Theory COMPAT of this wave (`-- WAVE 3 COMPAT`, all new files): `Theory/Typing/Interpretation.lean`
(`VEnv.Interpretation` without `elim`; `Sound` with `ordered : OrderedStrong`, a `pats` clause
`PatClause` and no eliminator clause; `PatClause.of_fixed`, `Sound.addPat`, `Sound.of_le` with
`hpats`), `Theory/Inductive/RestorationInterpretation.lean` (no eliminators; `RestoredPattern`),
`Theory/Typing/RestorationShapes.lean`, `Theory/Inductive/RestorationHead.lean`,
`Theory/Inductive/RestorationNames.lean` (`restorableNames`, `headName`, `expr_mkApps`,
`equation_parts`, `expr_of_avoid`, `VExpr.projNamesAvoid`, two closedness lemmas),
`Theory/Inductive/CompilationMajors.lean`. No existing Theory file was edited.

Still deferred in `Lean4Lean/Tests.lean`: `CorruptRestoredRecursorMetadata` (needs the restored
recursor metadata of `nestedRestoredBlock`'s internals) and `RecursiveFieldClassification` (the
source test imports the restoration interpretation; the test file itself is not on this tree and
is added back by the Equations+Install owner).

## Wave 2 scaffold (`Verify/Inductive/**`, the inductive refinement's interface)

`lake build` (default targets), `Lean4Lean.Tests` and `Lean4Lean.Experimental` are green with
`Verify/Inductive/**` imported by `Verify/Environment.lean` through `Verify/Inductive/Dispatch.lean`.
`InductiveDeclPreserves` is now the theorem `inductiveDeclPreserves (hnested :
VerifyInductive.NestedInductivePreserves)`; `addDecl.WF` takes `hnested` (wave 3's branch) and
`addDecl.WF_of` keeps the `InductiveDeclPreserves` form. The interface, the ownership map and the
dependency order of the five follow-on agents are in `Lean4Lean/Verify/Inductive/README.md`.
Every `sorry` of the scaffold is one of the named stubs below (`-- WAVE 2 STUB (owner)` in the
source); the owner is the directory agent of README.md's ownership map.

| statement | file | what it is on the source branch | owner |
|---|---|---|---|
| `AddInductive.checkInductiveTypes.WF` | `Verify/Inductive/Header/Check.lean` | `checkInductiveTypes.accumulatesHeadersSourceAligned` (`Header/Check.lean`), restated with `HeaderPhase` | Header |
| `CheckedHeaders.Describes.headerCertificate` | `Verify/Inductive/Header/Check.lean` | `HeaderFormations.complete` (`Header/Telescope.lean`): `TypeShape` reads only the header fields | Header |
| `AddInductive.declareInductiveTypes.WF` | `Verify/Inductive/Header/Installation.lean` | `HeaderDeclaration.toHeaderEnvironment` (`Install/Headers.lean`), `declareInductiveTypes.installsHeadersAtomicWF` | Header |
| `TrInductDeclCore.sourceNames_nodup` | `Verify/Inductive/Formation.lean` | same name, via `VEnv.addConstVals_append` | Header |
| `CheckedFormation.signature` | `Verify/Inductive/Constructor/CheckedFormation.lean` | `sourceSignature`, `sourceSignature_models`, `sourceSignature_familyTypesWF_header` (`Constructor/CheckedFormation.lean`), without the case schema | Constructor |
| `AddInductive.constructorPhase.WF` | `Verify/Inductive/Constructor/Check.lean` | `AddInductive.formationCoreClosedWF` (`Install/Formation.lean`) from `declareInductiveTypes.WF`, `checkConstructors.checkedWF`, `declareConstructors.WF` | Constructor |
| `ConstructorCheck.recursorPhasesWF` | `Verify/Inductive/Recursor/Check.lean` | same name (`Recursor/Check.lean`), output `TrRecursor` and the shape clauses of `VInductDecl.WF` | Recursor |
| `InductiveSignature.VRecRule.OfEquation.ofTr` | `Verify/Inductive/Recursor/Entries/TrRecursorVal.lean` | new: a rule that is a generated equation (`TrRecursorRule`) and translates to a `VRecRule` (`TrRecursor`) is `VRecRule.OfEquation` (`TrExprS.unique`, shape of `Instance.equation`) | Recursor |
| `RecursorCheck.generatedRuleTranslation` | `Verify/Inductive/Rules/RuleTranslations.lean` | same name: `ruleRhsTranslations`, `equationsWF`, `trRules`, plus `rules_wf : PatTyped` (PORT_PLAN 2.3) | Rules |
| `RuleTranslations.blockWF` (one `sorry`: `addRecs` is `addConstVals` over the recursors) | `Verify/Inductive/Rules/RuleTranslations.lean` | `VInductDecl.addRecs_eq_addConstVals` | Install |
| `RuleTranslations.compilesTo` | `Verify/Inductive/Rules/RuleTranslations.lean` | `OrdinaryCompilationCertificate.compilesTo` (`Compilation.lean`): `CompiledInductive.intro` with no auxiliaries | Install |
| `RuleTranslations.recsOf` | `Verify/Inductive/Rules/RuleTranslations.lean` | new: `VInductDecl.RecsOf` from `trRules`, `trRecs`, `recursors_eq` and `VRecRule.OfEquation.ofTr` | Install |
| `ConstructorCertificate.withRecs` | `Verify/Inductive/Formation.lean` | new: transport of `CtorShape`/`CtorTailWF` along `VInductDecl.withRecs` | Install |
| `RecursorCheck.blockCertificate` | `Verify/Inductive/Install/BlockCertificate.lean` | `RecursorCheck.blockCertificate` + `OrdinaryInstallation.extend*Exact`'s assembly of `AddInduct` (`Install/BlockCertificate.lean`, `Install/OrdinaryExtension.lean`) | Install |
| `BlockCertificate.installedBlocks` (one `sorry`: `hpres`) | `Verify/Inductive/Install/BlockCertificate.lean` | every constant of the source is a constant of the output (`insertConsts_find?_mono_of_fresh`) | Install |
| `BlockCertificate.rebase` | `Verify/Inductive/Install/BlockCertificate.lean` | `BlockCertificate.rebaseAddInductSafe` | Install |
| `BlockCertificate.extendSafeExact` | `Verify/Inductive/Install/BlockCertificate.lean` | same name, via `rebase` and `VEnvs.WF.extendInductExact` | Install |
| `BlockCertificate.extendUnsafeExact` | `Verify/Inductive/Install/BlockCertificate.lean` | `BlockCertificate.extendUnsafeOfHiddenExact`, via `VEnvs.WF.extendUnsafeExact` and `TrEnv'.ignore` | Install |
| `Kernel.Environment.checkDuplicatedUnivParams.WF` | `Verify/Inductive/Install/Ordinary.lean` | same name (`Recursor/Check.lean`) | Install |
| `checkPrimitiveInductive_eq_true_iff` | `Verify/Inductive/Primitive/Shape.lean` | same name (`Primitive/Shape.lean`) | Primitive |
| `loweringRun.primitiveNoop` | `Verify/Inductive/Primitive/Shape.lean` | `ElimNestedInductive.run'.primitiveNoopWF` (`Primitive/Lowering.lean`) | Primitive |
| `AddInductive.constructorPhase.primitiveWF` | `Verify/Inductive/Primitive/Run.lean` | `AddInductive.formationCore.primitiveClosedWF` (`Primitive/Run.lean`) with `Primitive/{Headers,Constructors,ConstructorCheck,ConstructorParams,BatchInstallation,Constants}.lean` | Primitive |
| `AddInductive.run.primitiveSourceAlignedWF` (one `sorry`: `Bool.rec`/`Nat.rec` are not primitives) | `Verify/Inductive/Primitive/Run.lean` | `PrimitiveInductiveShape.recursorsNonprimitive` | Primitive |
| `loweringRun.types_nonempty`, `loweringRun.ordinary_types_eq_source` | `Verify/Inductive/Lowering.lean` | now derived from the wave 3 scaffold's `loweringRun.WF` (`NestedLoweringOutput.source_nonempty`, `.types_length`, `.ordinary`) | wave 3 (Lowering), through `loweringRun.WF` |

`VerifyInductive.NestedInductivePreserves` (`Verify/Inductive/Dispatch.lean`), the named
hypothesis of the nested branch, is the theorem `nestedInductivePreserves` since the wave 3
scaffold (`Nested/Install/Dispatch.lean`), proved through the wave 3 stubs below.

Wave 1A's two stubs stay (`VEnvAt.recursorShapes`, now consumed by `ContextWF.initial`;
`VEnv.Ordered.patsAvoidFreshConsts`), owner Install for the first (from `InstalledBlocks` and
`VInductDecl.WF`'s `rec_shape`/`rules_ctor`), wave 2 for the second.

Theory COMPAT of this wave (`-- WAVE 2 COMPAT`): `VEnv.addInduct`'s stages and
`VInductDecl.RecsOf`/`VRecRule.OfEquation` moved to `Theory/Inductive/AddInduct.lean`;
`ContainersInstalled.cons` (`Theory/Inductive/Compilation.lean`) and `VEnv.InstalledBelow.intro`
(`Theory/Inductive.lean`) now install the container by `base.addInduct container = some installed`
with `container.RecsOf block` (and still `block.WF base`), replacing `VInductBlock.install`; the
`InstalledBelow` lookup lemmas moved to `Theory/Typing/InductiveLemmas.lean`. This resolves wave
1B's `InstalledBelow` finding below and wave 1C's `ContainersInstalled` finding. No new `sorry` in
`Theory/`.

Still deferred in `Lean4Lean/Tests.lean`: `InductiveTheory`, `TypedInductiveCompilation`,
`CorruptRecursorMetadata` (they need the recursor phase's internals, not just the interface).

## Wave 1A (checker verification)

`lake build` (default targets), `Lean4Lean.Tests` (with `AmbientContext` restored) and
`Lean4Lean.Experimental` are green. Outside `Theory/` the only `sorry`s are these two:

| statement | file | why | owner |
|---|---|---|---|
| `VEnvAt.recursorShapes` | `Verify/TypeChecker.lean` | the recursor and constructor telescopes (`VRecursorShape`, `VConstructorShape` at the constructor's own parameter count) of every visible recursor of a complete model. Recursor reduction needs them to show the constructor application of a well-typed ι redex saturated. On the source branch they were part of the installed-block invariant (`RecursorAlignmentCore`); `VInductDecl.WF` only records the syntactic `rec_shape`/`rules_ctor` (`CtorShape` does not say the constructor ends in its family at the parameter variables), so they must come from the formation data of the installed declaration. Every other fact the checker reads (`CheckerEnv`) is wave 1B's `CheckingEnv.Valid` or PR #43's `TrEnv.pats_iota'` | wave 2 (installed blocks) |
| `VEnv.Ordered.patsAvoidFreshConsts` | `Verify/Typing/ConstSupport.lean` | the `pat` case of `IsDefEq.noConsts`: the fixed parts of a registered rule's right-hand side avoid names absent from the environment. `VEnv.PatTyped` types a generic instance in an arbitrary context, so the template's constants are not bounded by the environment without a further argument. Used only by `VExpr.WF.noFreshConsts` (constructor positivity) | wave 2 (or a `PatWF` that types the template in the empty context) |

Interface for the waves that build on this one: the checker reads its environment through
`CheckerEnv safety env venv` (`Verify/TypeChecker/CheckerEnv.lean`), which extends
`CheckingEnv.Valid` by `shapes : RecursorShapesCoherent` and `iota : IotaRulesRegistered`
(`TrEnv.iotaRulesRegistered` proves the latter from `TrEnv`). An inductive declaration that runs
the checker in an intermediate environment must supply both there.
