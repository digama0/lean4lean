# Lean-for-Lean

This is an implementation of the Lean 4 kernel written in (mostly) pure Lean 4.
It is derived directly from the C++ kernel implementation, and as such likely
shares some implementation bugs with it (it's not really an independent
implementation), although it also benefits from the same algorithmic performance
improvements existing in the C++ Lean kernel.

The project also houses some metatheory regarding the Lean
system, in the same general direction as the
[MetaCoq project](https://github.com/MetaCoq/metacoq/).

## Building

To compile the code, you will need [Lean](https://lean-lang.org/lean4/doc/quickstart.html), or more specifically `elan`, the Lean version manager, which will make sure you have the right version of lean as specified in the [lean-toolchain](lean-toolchain) file. Assuming you have elan, the project can be compiled with:

```
lake build
```

This builds all components but you can also build them separately:

* `lake build Lean4Lean` builds the `Lean4Lean` library interface, and does not include any of the proofs.
* `lake build lean4lean` (note the capitalization!) builds the `lean4lean` command line tool, again without building proofs.
* `lake build Lean4Lean.Theory` contains the Lean metatheory and properties.
* `lake build Lean4Lean.Verify` is the proof that the `Lean4Lean` implementation satisfies the `Lean4Lean.Theory` abstract specification.

## Running

After `lake build lean4lean`, the executable will be in `.lake/build/bin/lean4lean`. Because it requires some environment variables to be set for search paths which are provided by lake, you should evaluate it like `lake env .lake/build/bin/lean4lean`.

If you run this as is (with no additional arguments), it will check every olean in the `lean4lean` package itself, which is probably not what you want. To check a different Lean package you should navigate the directory of the target project, then use `lake env path/to/lean4lean/.lake/build/bin/lean4lean <args>` to run `lean4lean` in the context of the target project. The command line arguments are:

> `lean4lean [--fresh] [--exact] [-v|--verbose] [--compare] [--differential] [MOD]`

* `MOD`: an optional lean module name, like `Lean4Lean.Verify`. If provided, the specified module will be checked (single-threaded); otherwise, all modules on the Lean search path will be checked (multithreaded).
* `--fresh`: Only valid when a `MOD` is provided. In this mode, the module and all its imports will be rebuilt from scratch, checking all dependencies of the module. The behavior without the flag is to only check the module itself, assuming all imports are correct.
* `--verbose`: shows the name of each declaration before adding it to the environment. Useful to know if the kernel got stuck on something.
* `--compare`: If lean4lean takes more than a second on a given definition, we also check the C++ kernel performance to see if it is also slow on the same definition and report if lean4lean is abnormally slow in comparison.
* `--exact`: match `MOD` exactly instead of as a prefix, so that `--fresh --exact Init` replays the module `Init` and all its imports.
* `--differential`: also send every declaration to the C++ kernel on the same environment, compare the two decisions and, when both accept, the constants the declaration adds; print the counts per module and fail on any disagreement.

## Verified inductive declarations

`Lean4Lean.addDecl.WF` (`Lean4Lean/Verify/Environment.lean`) states that the checked `addDecl`
is sound for every declaration form, including ordinary, mutual and nested inductive
declarations and quotient initialization: whenever it returns an environment, that environment
is modelled at every safety level by a well-formed abstract environment (`VEnv.WF`, with the
generative specification of inductive types in `Lean4Lean/Theory/Inductive`) extending the
previous model. Its only hypothesis is that the invariant held before the call.
`replayFresh.WF` (`Lean4Lean/Verify/Replay.lean`) lifts this to a whole `--fresh` replay from
the empty environment, without hypotheses: the replayed environment is modelled by well-formed
abstract environments, and every safe, non-partial source constant is in it and agrees with
the source. Outside the soundness argument, `VEnv.WF.church_rosser`
(`Lean4Lean/Theory/Typing/Confluence/WFParams.lean`) states confluence: in a well-formed
environment with the prelude's `Eq`, two definitionally equal terms reduce to terms that are
equal up to universe levels, proof irrelevance and eta.

These theorems are conditional on one open proof, listed with its status in
[OPEN_PROOFS.md](OPEN_PROOFS.md). The trusted base is the three standard axioms, the
implementation axioms of `Lean4Lean/Verify/Axioms.lean` and that open proof; the exact
list is `scripts/inductive-audit-inventory.json`. The changes to the executable are audited in
[divergences.md](divergences.md).

The checks, as CI runs them:

```
lake build                                              # Theory and Verify
lake build Lean4Lean.Experimental                       # prototypes
lake build Lean4Lean.Tests                              # executable and specification tests
python3 scripts/check-inductive-audit.py --self-test    # tests the dependency auditor
python3 scripts/check-inductive-audit.py --no-build --require-complete
lake exe lean4lean Init.Core
lake exe lean4lean --fresh Init.System.IO
scripts/differential-replay.sh                          # lean4lean against the C++ kernel
```

The audit walks the dependency closure of the top-level theorems, including opaque bodies and
types. It fails on an axiom not listed in `scripts/inductive-audit-inventory.json`, on a `sorry`
that is not one of the listed open proofs, on any `sorry` under a strict root (the generator
definitions and the confluence theorem with its coverage lemmas) that the inventory does not
accept for that root, and, with `--require-complete`, on a listed open proof that is no longer
reached. The differential replay sends every declaration of `Init` and of the test modules to
both lean4lean and the C++ kernel and compares the decisions and the generated constructors and
recursors. The tests in `Lean4Lean/Tests` compare generated recursors, constructors and rules
with Lean's kernel, check the specification on small examples, and pin the divergences listed in
`divergences.md`.

Wall time of `lake exe lean4lean --fresh MOD` (seconds, median of three runs, bash `time`, on a
shared and loaded machine) against PR #43's head, whose executable has the same caches:

| `MOD` | declarations | PR #43 | this branch |
|---|---|---|---|
| `Init.Prelude` | 1975 | 0.49 | 0.47 |
| `Init.Core` | 3953 | 0.66 | 0.64 |
| `Init.System.IO` | 43609 | 29.2 | 30.4 |

The `Init.System.IO` runs were interleaved between the two builds; on this machine single runs
varied by up to 7 seconds. The `Init.System.IO` time of this branch was re-measured after the
`whnf` caches were given the C++ kernel's keys (`let` expressions and let-bound variables),
interleaved with the executable without them: 30.4 against 30.0 seconds, within that variation.

A `lake build` of the default targets from a clean checkout took 17 minutes of wall time (28
CPU-minutes) on the same machine; `Lean4Lean.Tests` and `Lean4Lean.Experimental` add about 30
seconds on top of it.

Larger corpora. The same differential replay (`lean4lean --fresh --exact --differential MOD`,
run directly with `LEAN_PATH` set to the corpus's build) was run over two packages pinned to
this branch's toolchain `v4.33.0-rc2`: Batteries at `45f65c8b` (its last commit on that
toolchain) and Mathlib at `3ef2c2e2` (likewise), built from the Mathlib cache. Each run replays
the root module and everything it imports from the empty environment, so it covers `Init`,
`Std` and the imported part of `Lean` as well (1372 modules for Batteries, 10498 for Mathlib,
including Aesop, Qq, Plausible and ProofWidgets); unsafe and partial constants are skipped as
for `Init`. Both kernels accepted every declaration, and every constant the declarations add
agreed:

| corpus | declarations checked | agreements | lean4lean-only rejections | kernel-only rejections | constructed-term mismatches | wall time | peak RSS |
|---|---|---|---|---|---|---|---|
| `Batteries` | 129623 | 129623 | 0 | 0 | 0 | 2 min 7 s | 1.0 GB |
| `Mathlib` | 750221 | 750221 | 0 | 0 | 0 | 37 min 38 s | 7.8 GB |

Wall time is from process start to exit, on a shared and loaded 96-core machine (the replay is single
threaded); peak RSS is `VmHWM` sampled every two seconds. In the Mathlib run 21 declarations
took lean4lean over a second, the slowest `PresheafOfModules.freeObj._proof_2` (34 s).

## More documentation

* [bugs-found.md](bugs-found.md): A list of kernel bugs that the lean4lean project has uncovered.
* [divergences.md](divergences.md): A list of deliberate divergences between lean's kernel and the lean4lean kernel.
* [OPEN_PROOFS.md](OPEN_PROOFS.md): The open proofs the verification of inductive declarations is conditional on.

## (Selected) file breakdown

* `Main.lean`: command line app
* `Lean4Lean`: source files
  * `Environment.lean`: library entry point
  * `TypeChecker.lean`: main recursive function
  * `Inductive`
    * `Add.lean`: constructing inductive recursors
    * `Reduce.lean`: inductive iota rules
  * `Quot.lean`: quotient types handling
  * `Primitive.lean`: checking correctness of built-ins
  * `Std`: stuff that should exist upstream
  * `Theory`: lean metatheory
    * `VLevel.lean`: level expressions
    * `VExpr.lean`: expressions (boring de Bruijn variable theorems are here)
    * `VDecl.lean`: declarations
    * `VEnv.lean`: environment
    * `Meta.lean`: elaborator producing `VExpr`s
    * `Inductive.lean`: inductive types
    * `Quot.lean`: quotient types
    * `Typing`
      * `Basic.lean`: The typing relation itself
      * `Lemmas.lean`: theorems about the typing relation
      * `Meta.lean`: tactic for proving typing judgments
      * `Strong.lean`: proof that you can have all the inductive hypotheses
      * `UniqueTyping.lean`: uniqueness of types, and context strengthening
      * `Env.lean`: typing for environments
  * `Verify`: relation between the metatheory and the kernel
    * `Axioms.lean`: theorems about upstream opaques that shouldn't be opaque
    * `Expr.lean`: correctness of basics on `Expr`
    * `Level.lean`: correctness of basics on `Level`
    * `Level/Std.lean`: soundness of the standard-library level operations
    * `VLCtx.lean`: a "translation context" suitable for translating expressions
    * `LocalContext.lean`: properties of lean's `LocalContext` type
    * `NameGenerator.lean`: properties of the fresh name generator
    * `Typing`
      * `Expr.lean`: translating expressions (`TrExpr` is here)
      * `Lemmas.lean`: properties of `TrExpr`
      * `ConditionallyTyped.lean`: properties of expressions in caches that may be out of scope
    * `Environment`
      * `Basic.lean`: translating environments
      * `Lemmas.lean`: properties of `TrEnv`
    * `TypeChecker`
      * `Basic.lean`: typechecker invariants
      * `EquivManager.lean`: invariants for the union-find defeq cache
      * `InferType.lean`: correctness of `inferType`
      * `WHNF.lean`: correctness of `whnf`
      * `IsDefEq.lean`: correctness of `isDefEq`
    * `TypeChecker.lean`: top-level typechecker correctness
  * `Experimental`: work in progress formalizations and ideas
      * `Stratified.lean`: stratified typing judgment
      * `StratifiedUntyped.lean` another stratified typing judgment
      * `ParallelReduction.lean`: stuff related to church-rosser
      * `Stronger.lean`: a more heavily annotated typing judgment
