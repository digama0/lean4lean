import Lean4Lean.Environment

/-!
Executable regressions for the kernel hardening merged between Lean v4.32.2 and
v4.33.0-rc2.  The declarations are assembled manually so they exercise
`Lean4Lean.addDecl` and `Lean4Lean.TypeChecker` directly.
-/

namespace Lean4Lean.Tests.KernelHardening

open Lean Lean4Lean TypeChecker

private def errorOf (r : Except Kernel.Exception α) : MetaM (Option String) := do
  match r with
  | .ok _ => return none
  | .error e => return some (← (e.toMessageData {}).toString)

private def mentions (pat s : String) : Bool := (s.splitOn pat).length > 1

private def expectError (label pat : String) (r : Except Kernel.Exception α) : MetaM Unit := do
  match ← errorOf r with
  | none => throwError "{label} was accepted"
  | some msg => unless mentions pat msg do throwError "{label} failed for the wrong reason: {msg}"

private def runM (r : Except Kernel.Exception α) : MetaM α := do
  match r with
  | .ok a => pure a
  | .error e => throwError "kernel operation failed: {← (e.toMessageData {}).toString}"

private def mkPartial (n : Name) (lparams : List Name) (type value : Expr) : DefinitionVal :=
  { name := n, levelParams := lparams, type, value, hints := .opaque, safety := .partial }

private def universeTy : Expr :=
  .forallE `x (.sort (.param `u)) (.sort (.param `u)) .default

private def universeVal : Expr :=
  .lam `x (.sort (.param `u)) (.bvar 0) .default

private def imaxProp : Expr := .sort (.imax (.succ .zero) .zero)

private def imaxDataDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKIPData
    type := imaxProp
    ctors := [{
      name := `L4LKIPData.mk
      type := .forallE `b (.const ``Bool []) (.const `L4LKIPData []) .default }]
  }] false

/-- The auxiliary name the kernel generates for a nested `List` occurrence. -/
private def auxListName : Name := (`_nested ++ `List).appendIndexAfter 1

/-- lean4#14616.  `mk` nests `List L4LKNReal`, so eliminating it makes the kernel generate
`_nested.List_1`; `bad` then names that auxiliary.  This is the form that *discriminates*:
without the check the declaration is accepted, and `restoreNested` rewrites the stored type of
`bad` to `List L4LKNReal → L4LKNReal`, which the kernel never checked.  A declaration naming an
auxiliary that never exists is instead rejected as an unknown constant either way. -/
private def nestedAuxRealDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKNReal
    type := .sort 1
    ctors := [
      { name := `L4LKNReal.mk
        type := .forallE `xs (.app (.const ``List [.zero]) (.const `L4LKNReal []))
          (.const `L4LKNReal []) .default },
      { name := `L4LKNReal.bad
        type := .forallE `y (.const auxListName []) (.const `L4LKNReal []) .default }]
  }] false

private def nestedAuxProjDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKNProj
    type := .sort .zero
    ctors := [{
      name := `L4LKNProj.mk
      type := .forallE `x (.const ``Nat [])
        (.forallE `y (.proj `_nested.L4LHost_1 0 (.bvar 0))
          (.const `L4LKNProj []) .default) .default }]
  }] false

private def nestedBadDecl (bad : Expr) (name : Name) : Declaration :=
  let ind := fun a => .app (.const name []) a
  .inductDecl [] 1 [{
    name
    type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [{
      name := name ++ `mk
      type := .forallE `α (.sort 1)
        (.forallE `xs (.app (.const ``Array [.zero]) (ind bad))
          (ind (.bvar 1)) .default) .default }]
  }] false

/-- lean4#14613: projecting the field back out of a `Sort (imax 1 0)` proof would break proof
irrelevance, so `inferProj` must reject it. -/
private def imaxLeakDecl : Declaration :=
  .defnDecl {
    name := `L4LKIPLeak
    levelParams := []
    type := .forallE `proof (.const `L4LKIPData []) (.const ``Bool []) .default
    value := .lam `proof (.const `L4LKIPData []) (.proj `L4LKIPData 0 (.bvar 0)) .default
    hints := .abbrev, safety := .safe }

structure L4LKC where b : Bool
inductive L4LKW : Type where | mk (p : Bool)
inductive L4LKL (α : Type) (b : Bool) : Type where | mk

/-- lean4#14576/#14577: the parametric arguments of a nested occurrence are dropped from the
auxiliary declaration, so they escape checking unless they are checked against the environment
that results from the declaration. Here `w.1.1` is ill typed. -/
private def nestedIllTypedParams : Declaration :=
  let w : Expr := .bvar 0
  let Ew : Expr := .app (.const `L4LKE []) w
  let b : Expr := .proj ``L4LKC 0 (.proj ``L4LKC 0 w)
  let l : Expr := mkApp2 (.const ``L4LKL []) Ew b
  .inductDecl [] 1 [{
    name := `L4LKE
    type := .forallE `w (.const ``L4LKW []) (.sort 1) .default
    ctors := [{
      name := `L4LKE.mk
      type := .forallE `w (.const ``L4LKW [])
        (.forallE `l l (.app (.const `L4LKE []) (.bvar 1)) .default) .default }]
  }] false

private partial def deepNat : Nat → Expr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (deepNat n)

structure ProjB where b : Nat

run_meta do
  let env := (← getEnv).toKernelEnv

  -- lean4#14608 and lean4#14632: mutual blocks share level parameters and names.
  expectError "mutual block with mismatched universe parameters"
    "same universe level parameters" <|
    Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutA [`u] universeTy universeVal,
      mkPartial `L4LMutB [] universeTy universeVal]
  expectError "mutual block with a duplicate name" "duplicate declaration name" <|
    Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutDup [] (.const ``Nat []) (mkRawNatLit 0),
      mkPartial `L4LMutDup [] (.const ``Bool []) (.const ``Bool.true [])]
  match Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutGoodA [] (.const ``Nat []) (mkRawNatLit 0),
      mkPartial `L4LMutGoodB [] (.const ``Bool []) (.const ``Bool.true [])] with
  | .error e => throwError "valid mutual block was rejected: {← (e.toMessageData {}).toString}"
  | .ok _ => pure ()

  -- lean4#14613/#14615: normalized `Prop` controls inductive classification and recursor levels.
  let env' ← match Lean4Lean.addDecl env imaxDataDecl with
    | .ok env' => pure env'
    | .error e => throwError "imax-Prop inductive was rejected: {← (e.toMessageData {}).toString}"
  let some (.recInfo recInfo) := env'.find? `L4LKIPData.rec
    | throwError "imax-Prop recursor was not generated"
  unless recInfo.levelParams.isEmpty do
    throwError "imax-Prop inductive received a large-elimination universe"
  -- ... but its field must not be projectable back out, or proof irrelevance equates
  -- `mk false` and `mk true`.
  expectError "projection out of an `imax`-`Prop` proof" "invalid projection" <|
    Lean4Lean.addDecl env' imaxLeakDecl

  -- lean4#14616: a constructor naming a `_nested` auxiliary the kernel really generated.
  expectError "constructor naming a generated nested auxiliary" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxRealDecl
  -- The `Expr.proj` form of the same scan.  Note this one names an auxiliary that never exists,
  -- so it pins the branch rather than the hole: without the check it is still rejected, as an
  -- unknown constant.
  expectError "constructor naming a nested auxiliary in a projection" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxProjDecl

  -- lean4#14576/#14577: parametric arguments dropped from the auxiliary declaration.
  expectError "nested inductive with ill-typed dropped parameters" "invalid projection" <|
    Lean4Lean.addDecl env nestedIllTypedParams

  -- lean4#14607: validate original nested constructor types before elimination can hide them.
  expectError "nested inductive containing a free variable" "free variables" <|
    Lean4Lean.addDecl env <| nestedBadDecl (.fvar { name := `l4lBadFVar }) `L4LNestedFVar
  expectError "nested inductive containing a metavariable" "metavariables" <|
    Lean4Lean.addDecl env <| nestedBadDecl (.mvar { name := `l4lBadMVar }) `L4LNestedMVar

  -- lean4#14632: projection indices are `Nat` throughout lean4lean, so an index past `2^32`
  -- is stuck rather than truncated.  The structure *name* is deliberately not compared here;
  -- see the projection entry in `divergences.md`.
  let b : Expr := .app (.const ``ProjB.mk []) (mkRawNatLit 7)
  let good : Expr := .proj ``ProjB 0 b
  let huge : Expr := .proj ``ProjB 4294967296 b
  let goodWhnf ← runM <| TypeChecker.M.run env (x := TypeChecker.whnf good)
  unless goodWhnf == mkRawNatLit 7 do throwError "valid projection did not reduce"
  let hugeWhnf ← runM <| TypeChecker.M.run env (x := TypeChecker.whnf huge)
  unless hugeWhnf == huge do throwError "large projection index was truncated during reduction"
  let same ← runM <| TypeChecker.M.run env (x := TypeChecker.isDefEq good good)
  unless same do throwError "identical projections were not definitionally equal"
  expectError "out-of-range large projection" "invalid projection" <|
    TypeChecker.M.run env (x := TypeChecker.checkType huge)

  -- lean4#13956: lean4lean's explicit fuel remains deterministic and configurable.
  expectError "deep term with low recursion fuel" "deep recursion" <|
    TypeChecker.M.run env (fuel := { recDepth := 1 }) (x := TypeChecker.checkType (deepNat 100))
  match TypeChecker.M.run env (fuel := { recDepth := 1000 })
      (x := TypeChecker.checkType (deepNat 100)) with
  | .error e => throwError "deep term with sufficient recursion fuel failed: {← (e.toMessageData {}).toString}"
  | .ok ty => unless ty.isConstOf ``Nat do throwError "deep term inferred an unexpected type"

end Lean4Lean.Tests.KernelHardening
