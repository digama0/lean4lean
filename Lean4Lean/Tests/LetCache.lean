import Lean4Lean.Environment

/-! # `let` expressions and let-bound variables in the `whnf` caches

The `whnf` and `whnfCore` caches of lean4lean have the keys of `type_checker.cpp`: `whnf` caches
lambdas, applications, constants, projections, `let` expressions and let-bound free variables,
and `whnfCore` caches applications, `let` expressions and projections. The first check reads the
caches after reducing a `let` expression and a let-bound variable whose value is a dependent
function type; such a key translates to a function type, and its cache entry is read back when
the variable is applied.

The second check gives a list of let-heavy declarations to lean4lean and to the C++ kernel,
each under a fresh name in the environment of this module, and prints both decisions. The
accepted ones bind type aliases (directly, as the domain of a binder, and through a chain of
let-bound aliases) that are applied repeatedly, so the cache entries of the `let` expressions
and of the let-bound variables are read. The rejected ones are ill-typed through a `let`: a
value of the wrong type, and an application of a let-bound function to itself.

The `def`s below are also replayed by both kernels in the differential replay
(`scripts/differential-replay.sh`).
-/

namespace Lean4Lean.Tests.LetCache

open Lean

def aliasApplied : (Nat → Nat) → Nat :=
  let T : Type := Nat → Nat
  fun (f : T) => f (f (f 0))

def letDomain : (Nat → Nat) → Nat :=
  fun (f : let T : Type := Nat → Nat; T) => f (f (f 0))

def aliasChain : (Nat → Nat) → Nat :=
  let T0 : Type := Nat → Nat
  let T1 : Type := T0
  let T2 : Type := T1
  let T3 : Type := T2
  let T4 : Type := T3
  let T5 : Type := T4
  fun (f : T5) => (fun (g : T3) (h : T0) => f (g (h (f (g (h 0)))))) f f

def valueChain : Nat :=
  let a := 1
  let b := a + a
  let c := b + b
  let d := c + c
  let e := d + d
  e + e + e

theorem valueChain_eq : valueChain = 48 := rfl

/--
info: whnf of the let-bound alias: Nat → Nat
---
info: whnf cache has the let expression: true
---
info: whnfCore cache has the let expression: true
---
info: whnf cache has the let-bound variable: true
---
info: application through the cached alias: Nat
-/
#guard_msgs in
run_elab do
  let env := (← getEnv).toKernelEnv
  let nat := mkConst ``Nat
  let fnTy := Expr.forallE `x nat nat .default
  let letE := Expr.letE `T (mkSort (.succ .zero)) fnTy (.bvar 0) false
  let r := Lean4Lean.TypeChecker.M.run env .safe {} [] {} do
    Lean4Lean.withLetDecl `T (mkSort (.succ .zero)) fnTy fun T => do
      let w ← Lean4Lean.TypeChecker.whnf T
      let _ ← Lean4Lean.TypeChecker.whnf letE
      let s ← get
      -- `f : T` applied twice: each application reduces `T` and reads the cache entry.
      let ty ← Lean4Lean.withLocalDecl `f .default T fun f =>
        Lean4Lean.TypeChecker.checkType (mkApp f (mkApp f (mkNatLit 0)))
      pure (w, s.whnfCache.contains letE, s.whnfCoreCache.contains letE,
        s.whnfCache.contains T, ty)
  match r with
  | .ok (w, a, b, c, ty) =>
    logInfo m!"whnf of the let-bound alias: {w}"
    logInfo m!"whnf cache has the let expression: {a}"
    logInfo m!"whnfCore cache has the let expression: {b}"
    logInfo m!"whnf cache has the let-bound variable: {c}"
    logInfo m!"application through the cached alias: {ty}"
  | .error e => throwError "checker exception: {e.toMessageData {}}"

/--
info: aliasApplied: lean4lean accepted, C++ accepted
---
info: letDomain: lean4lean accepted, C++ accepted
---
info: aliasChain: lean4lean accepted, C++ accepted
---
info: valueChain: lean4lean accepted, C++ accepted
---
info: valueChain_eq: lean4lean accepted, C++ accepted
---
info: badValue: lean4lean rejected, C++ rejected
---
info: selfApplied: lean4lean rejected, C++ rejected
-/
#guard_msgs in
run_elab do
  let env := (← getEnv).toKernelEnv
  let nat := mkConst ``Nat
  let fnTy := Expr.forallE `x nat nat .default
  let fresh (n : Name) := Name.str `Lean4Lean.Tests.LetCache.fresh n.getString!
  let copy (n : Name) : Except String Declaration :=
    match env.find? n with
    | some (.defnInfo v) => .ok (.defnDecl { v with name := fresh n })
    | some (.thmInfo v) => .ok (.thmDecl { v with name := fresh n })
    | _ => .error s!"{n} is not a definition"
  -- `let x : Nat := "s"; x`
  let badValue : Declaration := .defnDecl {
    name := `Lean4Lean.Tests.LetCache.fresh.badValue, levelParams := [], type := nat,
    value := .letE `x nat (mkStrLit "s") (.bvar 0) false, hints := .opaque, safety := .safe }
  -- `let f : Nat → Nat := fun n => n; f f`
  let selfApplied : Declaration := .defnDecl {
    name := `Lean4Lean.Tests.LetCache.fresh.selfApplied, levelParams := [], type := nat,
    value := .letE `f fnTy (.lam `n nat (.bvar 0) .default) (mkApp (.bvar 0) (.bvar 0)) false,
    hints := .opaque, safety := .safe }
  let mut decls := #[]
  for n in [``aliasApplied, ``letDomain, ``aliasChain, ``valueChain, ``valueChain_eq] do
    match copy n with
    | .ok d => decls := decls.push (n.getString!, d)
    | .error e => throwError e
  decls := decls.push ("badValue", badValue) |>.push ("selfApplied", selfApplied)
  for (n, d) in decls do
    let l4l := match Lean4Lean.addDecl env d with | .ok _ => "accepted" | .error _ => "rejected"
    let cpp := match Kernel.Environment.addDeclCore env 0 200000 d none with
      | .ok _ => "accepted" | .error _ => "rejected"
    logInfo m!"{n}: lean4lean {l4l}, C++ {cpp}"

end Lean4Lean.Tests.LetCache
