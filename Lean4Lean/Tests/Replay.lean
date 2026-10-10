import Lean4Lean.Replay

/-! The pure replay core.

* `replayFresh` replays a hand-built constant table (an axiom, an inductive type, a definition,
  an inductive predicate and a theorem using them) from the empty environment: it adds the five
  declarations, and every source constant, including the constructors and recursors the kernel
  generated, is present in the result and agrees with the source. With a target `decl := some d`
  only the dependency cone of `d` is replayed, `d` is checked, and an absent or unsafe target is
  an error (also with an empty constant table).
* A source constructor that differs from the generated one is rejected by the postponed
  constructor check, and a source recursor that differs is rejected by the postponed recursor
  check.
* A source inductive type whose metadata differs from the generated one is rejected by the final
  agreement check. -/

namespace Lean4Lean.Tests.Replay

axiom A : Type

inductive T : Type
  | a
  | b (x : A)

def d : T := .a

inductive P : T → Prop
  | mk : P d

theorem thm : P d := .mk

open Lean Lean4Lean.Replay

def sourceNames : List Name :=
  [``A, ``T, ``T.a, ``T.b, ``T.rec, ``d, ``P, ``P.mk, ``P.rec, ``thm]

def sourceTable : CoreM (Std.HashMap Name ConstantInfo) := do
  let env ← getEnv
  sourceNames.foldlM (init := {}) fun m n => do
    let some ci := env.find? n | throwError "missing test constant {n}"
    return m.insert n ci

def check (cond : Bool) (msg : String) : CoreM Unit :=
  unless cond do throwError msg

def errorText : ReplayError → String
  | .kernel n _ => s!"kernel error at {n}"
  | .msg s => s

run_meta do
  let src ← sourceTable
  match replayFresh src with
  | .error e => throwError "replayFresh failed: {errorText e}"
  | .ok r =>
    check (r.numAdded == 5) s!"expected 5 declarations, got {r.numAdded}"
    check (r.checked.length == sourceNames.length) "not every source constant was checked"
    for n in sourceNames do
      check (r.checked.contains n) s!"{n} was not checked"
      let some ci' := r.env.find? n | throwError "{n} is missing from the replayed environment"
      check (ci' == src[n]!) s!"{n} differs from the source"
  -- Only the dependency cone of `d` is replayed with `decl := some d`.
  match replayFresh src (decl := some ``d) with
  | .error e => throwError "replayFresh (decl := d) failed: {errorText e}"
  | .ok r =>
    check (r.numAdded == 3) s!"expected 3 declarations for the cone of d, got {r.numAdded}"
    check ((r.env.find? ``thm).isNone) "thm is outside the cone of d"
    check (!r.checked.contains ``thm) "thm is outside the cone of d"
    check (r.checked.contains ``d) "the target d was not checked"
  -- A target that is not a source constant is an error, also with an empty table.
  for table in [src, {}] do
    match replayFresh table (decl := some `missing) with
    | .ok _ => throwError "a replay of the absent target `missing` succeeded"
    | .error e =>
      check (errorText e == s!"target {`missing} is not a source constant")
        s!"unexpected error: {errorText e}"
  -- So is an unsafe target, which the replay skips.
  let unsafeSrc := src.insert ``d (match src[``d]! with
    | .defnInfo v => .defnInfo { v with safety := .unsafe }
    | ci => ci)
  match replayFresh unsafeSrc (decl := some ``d) with
  | .ok _ => throwError "a replay of the unsafe target d succeeded"
  | .error e =>
    check (errorText e == s!"target {``d} is unsafe or partial and is not replayed")
      s!"unexpected error: {errorText e}"

/-- Replay `src` with the constant `n` replaced by `f` of it, and return the error text. -/
def replayError (src : Std.HashMap Name ConstantInfo) (n : Name)
    (f : ConstantInfo → ConstantInfo) : CoreM String := do
  match replayFresh (src.insert n (f src[n]!)) with
  | .ok _ => throwError "a corrupted {n} was accepted"
  | .error e => return errorText e

run_meta do
  let src ← sourceTable
  -- A source constructor with the wrong constructor index.
  let e ← replayError src ``T.b fun
    | .ctorInfo v => .ctorInfo { v with cidx := 0 }
    | ci => ci
  check (e == s!"Invalid constructor {``T.b}") s!"unexpected error: {e}"
  -- A source recursor with the wrong number of minor premises.
  let e ← replayError src ``T.rec fun
    | .recInfo v => .recInfo { v with numMinors := v.numMinors + 1 }
    | ci => ci
  check (e == s!"Invalid recursor {``T.rec}") s!"unexpected error: {e}"
  -- A source inductive type whose recursive flag is wrong: no constructor or recursor check
  -- covers it, the final agreement check does.
  let e ← replayError src ``T fun
    | .inductInfo v => .inductInfo { v with isRec := true }
    | ci => ci
  check (e == s!"Replayed constant {``T} differs from the source") s!"unexpected error: {e}"

end Lean4Lean.Tests.Replay

/-! Quotient initialization needs a safe `Eq` with the prelude's type, up to `==`.

The kernel's `checkEqType` (run by `Lean4Lean.addDecl · .quotDecl`) compares the type of `Eq`
and of `Eq.refl` with the prelude's and rejects an `unsafe` `Eq` (see `divergences.md`); the
replay core adds no check of its own.

* An `Eq` and `Eq.refl` that differ from the prelude's only in the binder annotation of `α` are
  accepted: `==` ignores binder annotations.
* An unsafe `Eq` with the prelude's type is rejected by `checkEqType`, so the replay fails at
  `Quot` with a kernel error.
* An `Eq` whose type differs from the prelude's is rejected. -/

namespace Lean4Lean.Tests.Replay
open Lean Lean4Lean.Replay

def explicitOuter : Expr → Expr
  | .forallE n t b _ => .forallE n t b .default
  | e => e

/-- The `Eq` declaration with the types of `Eq` and `Eq.refl` changed by `f` and `g`. -/
def eqDecl (eqI : InductiveVal) (reflI : ConstructorVal) (f g : Expr → Expr)
    (isUnsafe := false) : Declaration :=
  .inductDecl eqI.levelParams eqI.numParams
    [{ name := ``Eq, type := f eqI.type,
       ctors := [{ name := ``Eq.refl, type := g reflI.type }] }] isUnsafe

run_meta do
  let env ← getEnv
  let some (.inductInfo eqI) := env.find? ``Eq | throwError "no Eq"
  let some (.ctorInfo reflI) := env.find? ``Eq.refl | throwError "no Eq.refl"
  let some quotI := env.find? ``Quot | throwError "no Quot"
  -- Nonstandard binder annotations on `Eq` and `Eq.refl`: the replay succeeds.
  let src : Std.HashMap Name ConstantInfo := ({} : Std.HashMap Name ConstantInfo)
    |>.insert ``Eq (.inductInfo { eqI with type := explicitOuter eqI.type })
    |>.insert ``Eq.refl (.ctorInfo { reflI with type := explicitOuter reflI.type })
    |>.insert ``Quot quotI
  match replayFresh src with
  | .error e => throwError "quotient initialization on an Eq with the prelude's type up to `==` \
      was rejected: {errorText e}"
  | .ok r => check r.env.quotInit "the quotient module was not initialized"
  let some kenv := (Lean4Lean.addDecl (freshStart .anonymous)
      (eqDecl eqI reflI explicitOuter explicitOuter)).toOption
    | throwError "the kernel rejected the modified Eq"
  check (Lean4Lean.addDecl kenv .quotDecl).toBool "checkEqType rejected the modified Eq"
  -- The prelude's `Eq` passes.
  let some kenv := (Lean4Lean.addDecl (freshStart .anonymous) (eqDecl eqI reflI id id)).toOption
    | throwError "the kernel rejected the prelude's Eq"
  check (Lean4Lean.addDecl kenv .quotDecl).toBool "checkEqType rejected the prelude's Eq"
  -- An unsafe `Eq`: `checkEqType` rejects quotient initialization, so the replay fails at `Quot`.
  let some kenv := (Lean4Lean.addDecl (freshStart .anonymous)
      (eqDecl eqI reflI id id (isUnsafe := true))).toOption
    | throwError "the kernel rejected the unsafe Eq"
  check (!(Lean4Lean.addDecl kenv .quotDecl).toBool) "checkEqType accepted an unsafe Eq"
  let src : Std.HashMap Name ConstantInfo := ({} : Std.HashMap Name ConstantInfo)
    |>.insert ``Eq (.inductInfo { eqI with isUnsafe := true })
    |>.insert ``Eq.refl (.ctorInfo { reflI with isUnsafe := true })
    |>.insert ``Quot quotI
  match replayFresh src with
  | .ok _ => throwError "quotient initialization on an unsafe Eq was accepted"
  | .error e =>
    let msg := errorText e
    check (msg == s!"kernel error at {``Quot}") s!"unexpected error: {msg}"
  -- An `Eq` valued in `Type` instead of `Prop` is rejected.
  let toType : Expr → Expr := fun e => e.replace fun
    | .sort .zero => some (.sort (.succ .zero))
    | _ => none
  let some kenv := (Lean4Lean.addDecl (freshStart .anonymous)
      (eqDecl eqI reflI toType id)).toOption
    | throwError "the kernel rejected the Type-valued Eq"
  check (!(Lean4Lean.addDecl kenv .quotDecl).toBool) "checkEqType accepted a Type-valued Eq"

end Lean4Lean.Tests.Replay
