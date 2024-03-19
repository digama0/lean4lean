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

> `lean4lean [--fresh] [--verbose] [--compare] [MOD]`

* `MOD`: an optional lean module name, like `Lean4Lean.Verify`. If provided, the specified module will be checked (single-threaded); otherwise, all modules on the Lean search path will be checked (multithreaded).
* `--fresh`: Only valid when a `MOD` is provided. In this mode, the module and all its imports will be rebuilt from scratch, checking all dependencies of the module. The behavior without the flag is to only check the module itself, assuming all imports are correct.
* `--verbose`: shows the name of each declaration before adding it to the environment. Useful to know if the kernel got stuck on something.
* `--compare`: If lean4lean takes more than a second on a given definition, we also check the C++ kernel performance to see if it is also slow on the same definition and report if lean4lean is abnormally slow in comparison.

## (Selected) file breakdown

* `Main.lean`: command line app
* `Lean4Lean`: source files
  * `Environment.lean`: library entry point
  * `TypeChecker.lean`: main recursive function
  * `Inductive`
    * `Add.lean`: constructing inductive recursors
    * `Reduce.lean`: inductive iota rules
  * `Quot.lean`: quotient types handling
  * `UnionFind.lean`: a union-find data structure
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
      * `Stratified.lean`: (experimental) stratified typing judgment
      * `StratifiedUntyped.lean` (experimental) another stratified typing judgment
      * `UniqueTyping.lean`: conjectures about the typing relation
      * `ParallelReduction.lean`: (experimental) stuff related to church-rosser
      * `Env.lean`: typing for environments
  * `Verify`: relation between the metatheory and the kernel
    * `Axioms.lean`: theorems about upstream opaques that shouldn't be opaque
    * `UnionFind.lean`: proof of correctness of union-find
    * `VLCtx.lean`: a "translation context" suitable for translating expressions
    * `LocalContext.lean`: properties of lean's `LocalContext` type
    * `NameGenerator.lean`: properties of the fresh name generator
    * `Typing`
      * `Expr.lean`: translating expressions (`TrExpr` is here)
      * `Lemmas.lean`: properties of `TrExpr`
      * `ConditionallyTyped.lean`: properties of expressions in caches that may be out of scope
    * `Environment.lean`: translating environments
