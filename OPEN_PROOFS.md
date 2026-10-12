# Open proofs

The verification of `addDecl` (`Lean4Lean.addDecl.WF`) and everything stated on top of it is
conditional on one theorem whose proof is `sorry`. It is the `openProofs` entry of
`scripts/inductive-audit-inventory.json`; `scripts/check-inductive-audit.py --require-complete`
checks that every `sorry` reached from an audit root is it and that it is still reached. Paths
are relative to `Lean4Lean/`.

| theorem | origin | reached by |
|---|---|---|
| `IsDefEqU.weakN_iff` | master | the checker verification |

## `IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean`)

**Statement.** Context strengthening: in a well-formed environment, if two terms that do not
mention `n` binders of a context are definitionally equal in that context, they are
definitionally equal in the context without those binders.

**Use.** The executable keeps the C++ kernel's caches and equivalence manager across binders.
The checker verification moves the facts they record out of a binder's scope with this theorem,
through `VEnv.WF.strengthening` (`Verify/Typing/ConditionallyTyped.lean`) and
`VContext.strengthening` (`Verify/TypeChecker/Basic.lean`). It is master's statement, used as
master uses it, at Mario's direction. Every root of the checker verification reaches it
(`addDecl.WF`, `whnf.WF`, the inductive pipeline, the replay theorems); `reduceRecursor.WF` and
the confluence theorem do not.

**Why it is open.** It is not known to be true. The predecessor branch (PR #53) argued that it is
false for well-formed environments without `Eq`. In the environment that
`Tests/CacheScope.lean` builds (two singleton `Prop` families `I`, `J` with large elimination
over `P : F c → Prop`), the types `SI := I.rec K p` and `SJ := J.rec K r` are definitionally
equal under a binder `q : P v` (proof irrelevance and ι reduction through `K v q`), while a
groupoid interpretation of the context without `q` (one object with automorphism group `Z/3`
acting on a three-element fiber) separates them. The larger-context derivation was checked in
Lean; the separation is argued on paper, not formalised. With canonical `Eq` this countermodel
disappears (`P v` can be extracted from `p`), but no proof is known: PR #53 reduced the statement
to strengthening for endpoints typed at a common type without closing it.

**What would close it.** Either a proof under canonical `Eq` (add `VEnv.HasCanonicalEq` to the
hypotheses, which `addDecl.preludeEq_hasCanonicalEq` supplies for the real prelude; this at least
removes the countermodel), or a verification that never moves a typing fact to a smaller context
(PR #53's scoped caches and constructor-telescope certificates; an executable change, slower
than the C++ kernel's caching).

**Attempts on this branch.** Two attempts to prove the special case with canonical `Eq`, on the
branches `agent/iota-strengthA` (confluence-based) and `agent/iota-strengthB` (model-based), are
checked and `sorry`-free but do not close it. They reduce the statement, on this calculus and for
every well-formed environment with canonical `Eq`, to one obligation: `PropFront`, strengthening
for two propositions typed below the new binders (equivalently `TypedFront`, `LamDomainFront`,
`KeyFaithful`, `StrictJoinRepair` on those branches). The confluence route proves that a strict
normal equality between lifted terms descends with no hypothesis at all (`NormalEqS.descend`),
that core reduction steps above a lift descend (`ParRed.descend`), and that eta and proof
irrelevance, which PR #53 diagnosed as the circularity, are not obstacles here; what remains is a
matched beta-redex pair in the confluence join whose arguments are lambdas, that is, aligning the
domains of two lifted abstractions with no type information, and beta-normalising such a join is
not available because the calculus does not normalise. The model route shows that the observation
model cannot help: a lifted equation says only that the terms have the same observations in every
target where the new binder's type is inhabited, and the reflection step back to the smaller
context is false (`extension_not_freshReflection`). Canonical `Eq` enters only through the
confluence theorem. The obligation holds in every normalising fragment; no counterexample with
canonical `Eq` is known, and a counterexample would itself be a pair of propositions typed and
inhabited below whose lifts are convertible above but not below.

**Fresh replay.** The executable keeps its caches across binders unconditionally, as the C++
kernel does, so every binder exit of the checker moves cache facts with this theorem, whichever
declaration is being checked. The prelude's declarations before `Eq` (`id`, `PUnit`, `True`,
`Not`, ...) have binders, so `replayFresh.WF` and `replayFresh.WF_target` use the theorem in
environments without `Eq`, which is the case the countermodel concerns. Restricting the theorem
to environments with canonical `Eq` therefore cannot cover fresh replay: a sharpened variant
(branch `agent/iota-canoneq`) makes `addDecl.WF` depend only on the restricted statement but has
to give the fresh-replay theorems the explicit hypothesis that strengthening holds in well-formed
environments without `Eq`. The uses are `State.WF.restrict` through `VContext.strengthening`
(`Verify/TypeChecker/Basic.lean`), `lowerClosedBody` (`Verify/TypeChecker/IsDefEq.lean`),
`TrExprS.lowerClosedBV` (`Verify/TypeChecker/Projection.lean`), `State.WF.eqv_uniq`
(`Verify/EquivManager.lean`) and two places in `Verify/Environment/Primitive/Recursion.lean`.

