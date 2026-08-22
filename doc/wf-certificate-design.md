# Well-founded primitive-checking certificates

This note describes the executable certificate checker in `Lean4Lean/Primitive.lean` and the evidence consumed by its verification in `Lean4Lean/Verify/Primitive.lean`.

## What a certificate means

A certificate here is a finite record of expressions recovered while reducing a candidate primitive definition, together with expected structural shapes and closed definitional equalities. It is not an unchecked assertion and it is not itself a kernel proof term.

The executable checker obtains the expressions from the candidate, checks their types, compares the required shapes, and independently checks each recorded equality with `isDefEq`. The verification layer then translates those same expressions into the model and proves that a successful check supplies the semantic equations needed to preserve `VEnv.HasPrimitives`.

This separates two jobs:

- Reduction discovers the implementation-specific pieces hidden behind compiled recursion.
- Certificate checking turns those pieces into stable, closed evidence that the verification proof can consume.

`M.sandbox` runs discovery transactionally. Its result survives, but any type-checker cache or fresh-name state created during discovery is discarded.

## Why four Nat primitives need special treatment

Most recognized primitives expose their defining equations after ordinary reduction. For example, `Nat.add`, `Nat.pred`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.beq`, and `Nat.ble` can be checked by applying the candidate under closed lambdas and comparing the result with the expected zero and successor equations.

Four primitives hide their equations behind non-structural recursion:

- `Nat.mod` and `Nat.div` call fuel-carrying `go` functions. Their checks must validate both the public entry equation and the recursive fuel-step equation, including the dependent proof arguments.
- `Nat.gcd` and `Nat.bitwise` compile through `WellFounded.Nat.fix`. Checking only their surface equations does not expose enough of the compiled fixpoint to prove their semantic behavior in the model.

The implementation therefore uses two related forms of evidence. `Nat.mod` and `Nat.div` use closed equation pairs produced by `natModTopEquation`, `natModGoEquation`, `natDivTopEquation`, and `natDivGoEquation`. `Nat.gcd` and `Nat.bitwise` use structured certificates built on `NatWellFoundedCoreResult`.

## The generic well-founded certificate

`unfoldNatWellFoundedCore` applies the candidate to fresh arguments, reduces the resulting unary implementation, and requires its head to be `WellFounded.Nat.fix`. It extracts the state type, motive, measure, functional, initial state, fixpoint application, and internal fuel-based `fix.go`.

`NatWellFoundedCoreResult` retains:

- `equation`, the candidate's defining equation obtained from the supplied `eq_def`;
- `fixFn`, `fixGo`, and `goFn`, the relevant fixpoint and fuel-recursion functions;
- `measure`, `functional`, and `state`, the implementation pieces passed to `WellFounded.Nat.fix`;
- `callLhs` and `callRhs`, connecting the candidate application to the exposed recursive call;
- `entryLhs` and `entryRhs`, connecting the entry point to the full fixpoint application;
- `topLhs` and `topRhs`, exposing the initial eager fuel;
- `eagerLhs` and `eagerRhs`, showing how `WellFounded.Nat.eager` computes;
- the true and false Boolean-selector equations used by eager fuel;
- `stepLhs` and `stepRhs`, exposing one successor-fuel reduction;
- `specStepLhs` and `specStepRhs`, the same reduction specialized to the candidate's measure and functional.

`checkNatWellFoundedCertificate` first checks the expected auxiliary shape, including the canonical eager function and closure of `goFn`. It then type-checks and checks definitional equality for every recorded pair. The resulting record is generic in the `WellFounded.fix` state at this stage.

## GCD specialization

`specializeNatGcdFixCertificate` turns the generic result into a `NatGcdFixCertificate`. It exposes three equations:

- The public call enters the internal `go` function with eager fuel and the two input naturals as state.
- A state `(0, b)` reduces to `b`.
- A state `(a + 1, b)` reduces at one less unit of fuel to `(b % (a + 1), a + 1)`.

The specialization retains the dependent proof arguments found in the actual reduction instead of fabricating them. Its expected expressions then place those arguments into canonical call shapes.

`checkNatGcdFixCertificate` performs the specialization in a sandbox, compares the recovered expressions with those canonical shapes using `exprShapeEq`, rechecks the generic certificate, and checks each specialized equation independently. The verification theorem normalizes this evidence and proves that the candidate reflects mathematical `Nat.gcd`.

The current specialization defines its state as:

```lean
mkApp2 q(@PSigma.mk Nat (fun _ => Nat)) a b
```

That representation restriction is important for the acceptance comparison below.

## Bitwise specialization

`specializeNatBitwiseFixCertificate` follows the same pattern but retains a closed `callFn` parameterized by the Boolean operation, fuel, and two natural arguments. It extracts and checks:

- the public entry equation;
- the left-zero equation;
- the right-zero equation for a positive left argument;
- the positive-positive equation, including division by two, extraction of the low bits, the recursive call, and reconstruction with `Nat.add`.

The specialization locates the recursive call in the reduced body and requires a `PSigma.mk` state. `NatBitwiseFixCertificate.shape` also requires the retained call function to contain no free or metavariables.

`checkNatBitwiseFixCertificate` checks the generic certificate, all four specialized equations, the call function's type, and the expected closed shape. Its verification then interprets those equations for an arbitrary reflected Boolean operation.

## Mod and div equations

`checkNatModPrimitive` and `checkNatDivPrimitive` do not construct `NatWellFoundedCoreResult`, because their compiled implementations expose explicit fuel-carrying `go` functions rather than `WellFounded.Nat.fix`.

Each checker validates the candidate type, required environment entries, the type of its `go` function`, and the relevant conditional operator. It then type-checks both sides of its closed top-level and fuel-step equations and requires definitional equality. These equation pairs serve the same proof role as the structured fixpoint certificates: they retain exactly the reductions later interpreted by the conservation proof.

## What `checkPrimitiveDefCore` verifies

For every recognized primitive, `checkPrimitiveDefCore` checks the required declarations in the environment, universe parameters, expected type, and defining equations. A malformed known primitive raises an error; an unrecognized name returns `false`. The public `checkPrimitiveDef` additionally returns `false` for definitions that are not safe.

For `Nat.gcd` and `Nat.bitwise`, the core checker additionally:

1. Derives a closed equation from the corresponding `eq_def`.
2. Extracts and checks the generic well-founded certificate.
3. Specializes it to the primitive-specific call and recursive-state equations.
4. Checks the specialized structural shape and definitional equalities.
5. Checks the public zero, successor, or bitwise equations needed by the semantic proof.

For `Nat.mod` and `Nat.div`, it checks their public and fuel-step equations directly.

Successful executable checking does not by itself establish conservation. The theorems in `Lean4Lean/Verify/Primitive.lean` show that these checked expressions translate into the model, have the required types, and implement the corresponding semantic operation. The environment proof then uses those results to preserve `VEnv.HasPrimitives`.

## Acceptance behavior

Master's `unfoldNatWellFounded` binds `#[α, motive, f, F, a₀]` and remains generic in `α`. It contains no `PSigma` or `Prod` requirement. The new GCD and bitwise specializations instead synthesize `PSigma.mk Nat (fun _ => Nat)` states and compare the recovered expressions with that concrete representation.

Lean 4.33.0-rc2 uses `PSigma` when it directly compiles a recursive function with two varying arguments. [`Lean.Elab.PreDefinition.WF.Main`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Elab/PreDefinition/WF/Main.lean) builds an `ArgsPacker` from the varying arguments, [`Lean.Elab.PreDefinition.WF.PackMutual`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Elab/PreDefinition/WF/PackMutual.lean) turns an n-ary definition into a unary definition, and [`Lean.Meta.ArgsPacker`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Meta/ArgsPacker.lean) uses iterated `PSigma` and `PSigma.mk` for that unary packing. The shipped `Nat.gcd` consequently has the form:

```lean
fun m n => Nat.gcd._unary (PSigma.mk m n)
```

The representation difference is not reachable through an arbitrary user declaration. `checkPrimitiveDefCore` dispatches on `v.name`, and only declarations literally named `Nat.gcd` or `Nat.bitwise` enter the affected cases. A definition named `prodGcd` or `prodGcdAux` reaches the default case instead, so it cannot demonstrate acceptance or rejection by the GCD certificate checker. With Lean's shipped prelude, the affected reserved names are already declared and ordinary user code cannot replace them.

The relevant input space is an alternative prelude. Such a prelude can define the reserved `Nat.gcd` name through a one-argument well-founded helper whose state is `Nat × Nat`:

```lean
namespace Nat

def gcdAux (p : Nat × Nat) : Nat :=
  if h : p.1 = 0 then
    p.2
  else
    gcdAux (p.2 % p.1, p.1)
  termination_by p.1
  decreasing_by
    simp_wf
    exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero h)

def gcd (m n : Nat) : Nat :=
  gcdAux (m, n)

end Nat
```

The declaration passed to `checkPrimitiveDefCore` is then literally named `Nat.gcd`, so it enters the GCD case. Reducing its wrapper exposes the helper's `WellFounded.Nat.fix` implementation. The helper has one varying argument, and the executed `gcdW` check quoted below confirms that the compiler preserves its `Nat × Nat` state rather than packing the wrapper's two arguments with `PSigma`. Master's checker is generic in that state type. The new specialization instead constructs and shape-checks `PSigma.mk` states, so it rejects this alternative representation even when the generic equations hold.

Classification: **(b) reachable**, but only in the alternative-prelude input space that primitive checking exists to validate. It is a genuine narrowing of which preludes lean4lean accepts, not a difference observable in ordinary user code and not a difference affecting Lean's shipped prelude. Restoring master's acceptance requires deriving the state constructor and its component behavior from the generic certificate instead of synthesizing `PSigma.mk`.

Execution with the pinned Lean 4.33.0-rc2 toolchain demonstrates both representation claims. `set_option pp.explicit true in #print Nat.gcd` produces:

```lean
@[irreducible] def Nat.gcd : Nat → Nat → Nat :=
fun m n => Nat.gcd._unary (@PSigma.mk Nat (fun m => Nat) m n)
```

and `#check @Nat.gcd._unary` produces `Nat.gcd._unary : (_ : Nat) ×' Nat → Nat`, confirming that the shipped prelude uses exactly the state representation required by the certificate checker. Compiling the one-argument `Nat × Nat` helper and running `set_option pp.explicit true in #print gcdW` produces:

```lean
def gcdW : Nat → Nat → Nat :=
fun m n => gcdAux (@Prod.mk Nat Nat m n)
```

and `#check @gcdAux` produces `gcdAux : Nat × Nat → Nat`, confirming that Lean preserves the helper's `Prod` state instead of repacking it into `PSigma`. Nobody has yet built an alternative prelude that defines the reserved name `Nat.gcd` this way and run both checkers against it, so the end-to-end differential remains undemonstrated. The structural acceptance argument does not depend on that missing run.

The corresponding `divergences.md` entry reads:

```markdown
* [`Lean4Lean.Environment.checkPrimitiveDef`](Lean4Lean/Primitive.lean), `Nat.gcd` and `Nat.bitwise` cases: lean4lean requires the `WellFounded.Nat.fix` state used by these reserved primitive declarations to be `PSigma Nat (fun _ => Nat)` and requires recursive states to be constructed with `PSigma.mk`, while the previous checker was generic in the fixpoint state type. The shipped `Nat.gcd` prints with exactly this representation under Lean 4.33.0-rc2, so Lean's shipped prelude is unaffected. Ordinary user declarations cannot reach these cases because dispatch is by the reserved names `Nat.gcd` and `Nat.bitwise`. The restriction applies only to an alternative prelude that defines one of those names using another state representation, such as a `Nat.gcd` wrapper around a one-argument well-founded helper over `Nat × Nat`. Compiling an analogous wrapper confirms that Lean retains the helper's `Prod.mk` state rather than repacking it with `PSigma.mk`; the previous checker can accept that representation, while the certificate checker rejects it. An end-to-end run with a complete alternative prelude has not been performed.
```

## Verification boundary

The certificate proofs establish conservation for accepted definitions. They do not establish behavioral parity with master for alternative preludes, as this reserved-name narrowing demonstrates. Lean's shipped prelude and ordinary user declarations are unaffected by this specific difference.

The final `addDecl.WF` theorem is conditional on `Declaration.SupportedByModel`. Inductive declarations cannot satisfy that condition, so inductives are excluded entirely. Mutual blocks must supply a `Nodup` hypothesis that master's `addMutual.WF` derived from the executable checker.

The branch removes one admitted proof and adds none. Nevertheless, `addDecl.WF` still depends on `sorryAx` through admitted lemmas elsewhere under `Lean4Lean/Verify/` that already exist on master. Its axiom report also contains two `bv_decide` axioms originating in `Lean4Lean/Verify/Expr.lean` and no `native_decide` axiom. These facts prevent interpreting the theorem as complete kernel verification.

## Relationship to the interpreter proposal

This note describes the executable checker changed by this PR. It is distinct from `doc/wf-certificate-interpreter.md` on `agent/wf-certificate-interpreter`, which proposes a future verification-side refactor under the explicit assumption that the executable checker remains unchanged.
