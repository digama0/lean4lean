# A certificate interpreter for well-founded `Nat` primitives

Status: design + spine prototype. Constraint: the executable checker
(`Lean4Lean/Primitive.lean`, `Environment.lean`) must faithfully match the
lean4 kernel and is never modified; all layers are verification-side. Branch `agent/wf-certificate-interpreter`,
stacked on PR #32.

## Problem

Four primitives are defined by non-structural recursion and verified against
checked defeq equations: `Nat.mod`, `Nat.div` (fuel-carrying `go` functions),
`Nat.gcd` and `Nat.bitwise` (compiled `WellFounded.fix`). Their verification
is ~12k lines across `ModDivCondition`, `ModDivReflect`, the six `Bitwise*`
files, and the gcd sections of `Verify/Primitive.lean`. Measured composition
(mod/div, and the pattern holds for the others):

- ~75-80% syntactic plumbing: `TrExprS` constructions, telescope
  instantiation, binder alignment, canonicalization of translated calls;
- ~15-20% condition reflection: turning `decide (a ≤ b)` / `decide (a = b)` /
  `Bool`-valued `ite` applications into literal `Bool`s and selected branches;
- ~4-9% actual fixpoint reasoning, in four copies of the same ~40-line fuel
  induction (`of_modCore_equations`, `of_divCore_equations`,
  `of_gcd_fix_relation`, `evalNatBitwise_of_fix_relation`).

Today there are also three disjoint partial interpreters: the
`Reflection`/`Condition` selector machinery (mod/div), `ReflectsBoolNatITE`
(bitwise, genuinely evaluating), and the `NatWellFoundedCoreResult`
eager/fuel certificate (gcd/bitwise entry) that mod/div bypass entirely.

## Architecture

Four layers, each usable independently:

1. **Spine** (prototyped here): `FuelStep α` and
   `VEnv.natLit_defeq_of_fuel_relation`. A call relation
   `G : Nat → α → VExpr → Prop` steps by a semantic
   `step : α → FuelStep α`; a step either terminates with a literal or
   recurses at a smaller measure with a defeq-compatible post-processing
   `post : Nat → Nat` of the recursive result (identity for mod/gcd,
   successor for div, the bit-reassembly for bitwise). One strong induction
   on fuel replaces the four hand-rolled ones, and any future wf primitive
   gets its induction for free by exhibiting a `step`.

2. **Condition atoms**: one generic evaluator
   `decide (R a b) ≡ boolLit (impl a b)` parameterized by the relation, its
   `Bool` implementation (`Nat.ble`/`Nat.beq`, both already reflected
   primitives), and the `Reflection` scheme, unifying
   `BitwiseCondition.lean`'s `natEq` machinery (~2.4k lines) with
   `ModDivCondition.lean`'s `natLE` selector machinery (~2.1k lines).
   `ReflectsBoolNatITE` stays as the branch evaluator.

3. **Telescope/call plumbing**: adopt the bitwise `callFn` design for all
   four families (a closed, type-checked lambda hiding the dependent state,
   taking the recursion arguments as plain `Nat`s, related by `IsDefEqU`
   rather than syntactic equality), and generalize
   `BitwiseSupport.instantiate_bitwise_lam{3,4}_equation` and
   `finish_bitwise_proof_equation` over the binder telescope. This is what
   removes the bulk of gcd's ~500-line `succ_semantics` and the
   `zero`/`zero_right` near-duplication; the mod/div dependent-proof binder
   plumbing (the largest single cost there) flows through the same lemmas.

4. **Entry certificates**: out of scope. Unifying the certificate entry
   would mean re-emitting mod/div's checked equations through the shared
   format, i.e. changing which defeqs the executable checker validates. The
   checker must faithfully match the lean4 kernel's acceptance behavior, so
   it is frozen; the verification layers below interpret exactly the
   equations it already checks.

What stays per-primitive: the transition inventory (gcd: zero/succ; bitwise:
zero/zero-right/succ), gcd's argument swap (renormalizing the swapped state
through `Nat.mod` reflection), bitwise's bit decomposition and its Kripke
quantifier, and each family's measure lemma.

## Prototype result (this branch)

Layer 1 is implemented and all four existing inductions are re-derived as
instances of the one spine theorem, with their statements unchanged:

- `Nat.gcd`: `step (a, b) = if a = 0 then done b else recur (b % a, a) id`,
  measure `a`, decrease `Nat.mod_lt`;
- `Nat.bitwise`: three-way step with
  `post q = if f (bits) then q+q+1 else q+q`, measure `a`, decrease
  `Nat.bitwise_rec_lemma`;
- `Nat.mod`/`Nat.div`: `step x = if y ≤ x then recur (x - y) post else done`,
  `post = id` / `(· + 1)`, measure `x`, decrease `Nat.sub_lt_self`, with the
  dependent proof arguments carried existentially inside `G` exactly as
  before.

This validates the abstraction the other three layers hang off: the
"terminal or recurse-with-postprocessing" step shape is sufficient for all
four families.

## Estimated cost/benefit for the full build-out

- Layer 2: replaces ~4.5k lines of twin condition machinery with an
  estimated ~1.2k; medium risk, no executable-checker changes.
- Layer 3: the biggest verification win (est. 1.5-2k lines off gcd + bitwise
  transitions and the mod/div instantiation toolbox); medium-high effort,
  no executable-checker changes.
- Layer 4: dropped (checker is frozen; see above).

Total realistic effect on the ~12k wf mass from layers 2 and 3 alone: down
to roughly 6.5-7.5k, at a cost comparable to the whole deduplication round
already landed on PR #32, with the executable checker byte-identical
throughout. The spine (this branch) is cheap and stands alone; each further
layer can be evaluated after the previous one lands.
