import Lean4Lean.TypeChecker
/-! # Conversion facts outlive a binder scope, as in the C++ kernel

Two singleton `Prop` families `I` and `J` with large elimination give types `SI := left K vv pp`
and `SJ := right K vv rr` that are definitionally equal under a binder `q : P vv` (through
`K vv q`, by proof irrelevance and iota), but for which no derivation is available in the empty
context without the binder. The closed definition

    result : SJ := let seed : (q : P v) → Type 1 := fun q => …; let ret : SJ := zz; ret

(with `zz : SI` an axiom) has a `seed` body that forces the comparisons `SI ≡ … ≡ SJ` inside
the scope of `q`. The C++ kernel, whose caches and equivalence manager persist across scopes,
then answers `SI ≡ SJ` outside that scope and accepts `result`, while it rejects the same
definition without `seed`. Lean4Lean's caches and equivalence manager persist across scopes in
the same way, so it accepts `result` and rejects the unseeded definition, exactly as the C++
kernel does. (A branch of lean4lean once restored its caches when a binder was closed and
rejected `result`; that mode is gone. The acceptance is sound: `IsDefEqU.weakN_iff`, context
strengthening, says the conversion under the unused binder `q` holds without it.)

The last check runs the comparisons directly: before the binder `SI ≡ SJ` fails, and under it
each link succeeds. After it, `SI ≡ SJ` itself still fails, because the failure found before the
binder is in the failure cache, but the fresh comparison `(let unused := SI; SI) ≡ SJ` (the type
of `zz`, as in `result`) succeeds from the cache entries that survived the binder. The axioms
below are object-language declarations of the test environment.
-/

namespace Lean4Lean.Tests.CacheScope

axiom C : Type
axiom F : C → Type
axiom c : C
axiom P : F c → Prop
axiom leftMap : F c → F c
axiom rightMap : F c → F c

inductive I : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : I c v (leftMap v)

inductive J : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : J c v (rightMap v)


def left (K : (v : F c) → P v → Type) (v : F c)
    (p : I c v (leftMap v)) : Type :=
  I.rec (motive := fun _ _ _ _ => Type) K p

def right (K : (v : F c) → P v → Type) (v : F c)
    (p : J c v (rightMap v)) : Type :=
  J.rec (motive := fun _ _ _ _ => Type) K p

-- Each constructor computation is literal iota.
example (K : (v : F c) → P v → Type) (v : F c) (q : P v) :
    left K v (I.mk v q) = K v q := rfl

example (K : (v : F c) → P v → Type) (v : F c) (q : P v) :
    right K v (J.mk v q) = K v q := rfl

-- Each major replacement is definitionally proof irrelevant.
example (v : F c) (q : P v) (p : I c v (leftMap v)) : p = I.mk v q := rfl
example (v : F c) (q : P v) (p : J c v (rightMap v)) : p = J.mk v q := rfl

-- This Lean equality proof records the congruence/transitivity chain;
-- it is not a claim that kernel reduction directly compares the endpoints.
theorem withProof (K : (v : F c) → P v → Type) (v : F c)
    (p : I c v (leftMap v)) (r : J c v (rightMap v)) (q : P v) :
    left K v p = right K v r := by
  calc
    left K v p = left K v (I.mk v q) := congrArg (left K v) (show p = I.mk v q from rfl)
    _ = K v q := rfl
    _ = right K v (J.mk v q) := rfl
    _ = right K v r := congrArg (right K v) (show J.mk v q = r from rfl)

/--
info: Lean4Lean.Tests.CacheScope.I.rec: large singleton elimination accepted, three indices, zero parameters; isK=false
---
info: Lean4Lean.Tests.CacheScope.J.rec: large singleton elimination accepted, three indices, zero parameters; isK=false
-/
#guard_msgs in
open Lean Lean.Elab.Command in
run_elab do
  for name in [``I.rec, ``J.rec] do
    let some (.recInfo info) := (← getEnv).find? name | throwError "not a recursor"
    unless info.levelParams.length == 1 && info.numParams == 0 &&
        info.numIndices == 3 && info.numMinors == 1 do
      throwError "unexpected source recursor metadata"
    logInfo m!"{name}: large singleton elimination accepted, three indices, zero parameters; isK={info.k}"

end Lean4Lean.Tests.CacheScope

namespace Lean4Lean.Tests.CacheScope
axiom KK : (v : F c) → P v → Type
axiom vv : F c
axiom pp : I c vv (leftMap vv)
axiom rr : J c vv (rightMap vv)
/--
info: small environment checked by C++: Eq present = false
---
info: L4L whole term accepted
---
info: L4L unseeded term rejected
---
info: C++ unseeded declaration rejected
---
info: C++ whole declaration accepted
---
info: cache experiment: (false, (true, true, true, true), false, true)
-/
#guard_msgs in
open Lean in
run_elab do
  let si := mkAppN (mkConst ``left) #[mkConst ``KK, mkConst ``vv, mkConst ``pp]
  let sj := mkAppN (mkConst ``right) #[mkConst ``KK, mkConst ``vv, mkConst ``rr]
  let host := (← getEnv).toKernelEnv
  let empty := (← Lean.mkEmptyEnvironment).toKernelEnv
  let build : Except Kernel.Exception Kernel.Environment := do
    let mut env := empty
    for n in [``C, ``F, ``c, ``P, ``leftMap, ``rightMap] do
      let some (.axiomInfo v) := host.find? n | throw (.other "missing axiom")
      env ← Kernel.Environment.addDeclCore env 0 50000 (.axiomDecl v) none
    for (n, cn) in [(``I, ``I.mk), (``J, ``J.mk)] do
      let some iv := host.find? n | throw (.other "missing family")
      let some cv := host.find? cn | throw (.other "missing constructor")
      env ← Kernel.Environment.addDeclCore env 0 50000
        (.inductDecl [] 0 [{ name := n, type := iv.type, ctors := [{ name := cn, type := cv.type }] }] false) none
    for n in [``left, ``right] do
      let some (.defnInfo v) := host.find? n | throw (.other "missing definition")
      env ← Kernel.Environment.addDeclCore env 0 50000 (.defnDecl v) none
    for n in [``KK, ``vv, ``pp, ``rr] do
      let some (.axiomInfo v) := host.find? n | throw (.other "missing axiom")
      env ← Kernel.Environment.addDeclCore env 0 50000 (.axiomDecl v) none
    return env
  let .ok smallEnv := build | throwError "small environment rejected"
  logInfo m!"small environment checked by C++: Eq present = {smallEnv.contains ``Eq}"
  let zzName := Name.str `Lean4Lean.Tests.CacheScope "zz"
  let wrapped := Expr.letE `unused (mkSort (.succ .zero)) si si false
  let .ok smallEnv := Kernel.Environment.addDeclCore smallEnv 0 50000
    (.axiomDecl { name := zzName, levelParams := [], type := wrapped, isUnsafe := false }) none
    | throwError "z rejected"
  let q := mkFVar ⟨`test_q⟩
  let ci := mkAppN (mkConst ``I.mk) #[mkConst ``vv, q]
  let cj := mkAppN (mkConst ``J.mk) #[mkConst ``vv, q]
  let ii := mkAppN (mkConst ``left) #[mkConst ``KK, mkConst ``vv, ci]
  let jj := mkAppN (mkConst ``right) #[mkConst ``KK, mkConst ``vv, cj]
  let mid := mkAppN (mkConst ``KK) #[mkConst ``vv, q]
  let mut seedBody := si
  for (a,b) in [(jj,sj), (mid,jj), (ii,mid), (si,ii)] do
    let aty := Expr.forallE `x a a .default
    let bv := Expr.lam `x b (.bvar 0) .default
    seedBody := Expr.letE `f aty bv (seedBody.liftLooseBVars 0 1) false
  let qTy := mkApp (mkConst ``P) (mkConst ``vv)
  let seed := Expr.lam `q qTy (seedBody.abstract #[q]) .default
  let seedTy := Expr.forallE `q qTy (mkSort (.succ .zero)) .default
  let finalBody := Expr.letE `ret sj (mkConst zzName) (.bvar 0) false
  let term := Expr.letE `seed seedTy seed finalBody false
  let l4l := Lean4Lean.TypeChecker.M.run smallEnv .safe {} [] {} (Lean4Lean.TypeChecker.checkType term)
  match l4l with
  | .ok _ => logInfo "L4L whole term accepted"
  | .error _ => logInfo "L4L whole term rejected"
  let l4lUnseeded := Lean4Lean.TypeChecker.M.run smallEnv .safe {} [] {}
    (Lean4Lean.TypeChecker.checkType finalBody)
  match l4lUnseeded with
  | .ok _ => logInfo "L4L unseeded term accepted"
  | .error _ => logInfo "L4L unseeded term rejected"
  let unseeded := Kernel.Environment.addDeclCore smallEnv 0 50000
    (.defnDecl { name := Name.str `Lean4Lean.Tests.CacheScope "unseeded", levelParams := [], type := sj, value := finalBody, hints := .opaque, safety := .safe }) none
  match unseeded with
  | .ok _ => logInfo "C++ unseeded declaration accepted"
  | .error _ => logInfo "C++ unseeded declaration rejected"
  let native := Kernel.Environment.addDeclCore smallEnv 0 50000
    (.defnDecl { name := Name.str `Lean4Lean.Tests.CacheScope "result", levelParams := [], type := sj, value := term, hints := .opaque, safety := .safe }) none
  match native with
  | .ok _ => logInfo "C++ whole declaration accepted"
  | .error _ => logInfo "C++ whole declaration rejected"
  let result := Lean4Lean.TypeChecker.M.run smallEnv .safe {} [] {} do
    let before ← Lean4Lean.TypeChecker.isDefEq si sj
    let links ← Lean4Lean.withLocalDecl `q .default (mkApp (mkConst ``P) (mkConst ``vv)) fun q => do
      let ci := mkAppN (mkConst ``I.mk) #[mkConst ``vv, q]
      let cj := mkAppN (mkConst ``J.mk) #[mkConst ``vv, q]
      let ii := mkAppN (mkConst ``left) #[mkConst ``KK, mkConst ``vv, ci]
      let jj := mkAppN (mkConst ``right) #[mkConst ``KK, mkConst ``vv, cj]
      let mid := mkAppN (mkConst ``KK) #[mkConst ``vv, q]
      let a ← Lean4Lean.TypeChecker.isDefEq si ii
      let b ← Lean4Lean.TypeChecker.isDefEq ii mid
      let c ← Lean4Lean.TypeChecker.isDefEq mid jj
      let d ← Lean4Lean.TypeChecker.isDefEq jj sj
      pure (a,b,c,d)
    let after ← Lean4Lean.TypeChecker.isDefEq si sj
    let afterWrap ← Lean4Lean.TypeChecker.isDefEq wrapped sj
    pure (before, links, after, afterWrap)
  match result with
  | .ok r => logInfo m!"cache experiment: {repr r}"
  | .error _ => throwError "checker exception"
end Lean4Lean.Tests.CacheScope
