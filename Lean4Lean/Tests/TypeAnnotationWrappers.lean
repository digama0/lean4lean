import Lean4Lean.Environment
import Lean4Lean.Verify.CanonicalEq

/-! Type-annotation wrappers.

The inductive checker strips `optParam`, `autoParam`, `outParam` and `semiOutParam` from binder
domains only when the environment declares the name as the prelude's definition
(`Kernel.Environment.isTypeAnnotationWrapper`).

* The prelude's four wrappers are recognised, and an `optParam` field is stripped in the
  generated recursor, as Lean's kernel does.
* A hostile `optParam` (declared with a different body, in an environment without the prelude)
  is not stripped: the constructor field and the recursor's minor premise keep the literal
  domain. Lean's kernel strips it by name, giving a minor premise whose field has the wrong type.
* The base case of the replay invariant is stated for the environment the replay starts from. -/

namespace Lean4Lean.Tests.TypeAnnotationWrappers

open Lean Meta

example (m : Name) : ∃ ves : VEnvs, ves.WF (Kernel.Environment.empty m) :=
  ⟨_, VEnvs.WF.empty m false⟩

def check (cond : Bool) (msg : String) : MetaM Unit :=
  unless cond do throwError msg

/-- The domain of the minor premise of a single-constructor, single-field recursor
`(motive : T → Sort u) → ((x : D) → motive (T.mk x)) → (t : T) → motive t`. -/
def minorFieldDomain? : Expr → Option Expr
  | .forallE _ _ (Expr.forallE _ (Expr.forallE _ d _ _) _ _) _ => some d
  | _ => none

def oneFieldDecl (n : Name) (dom : Expr) : Declaration :=
  let ctor : Constructor :=
    { name := n.str "mk"
      type := Expr.forallE (Name.mkSimple "x") dom (.const n []) BinderInfo.default }
  .inductDecl [] 0 [{ name := n, type := Expr.sort 1, ctors := [ctor] }] false

def lean4leanAdd (env : Kernel.Environment) (d : Declaration) : MetaM Kernel.Environment :=
  match Lean4Lean.addDecl env d (check := true) with
  | .error e => throwError "Lean4Lean.addDecl rejected: {e.toMessageData {}}"
  | .ok env => pure env

-- The prelude's wrappers.
run_meta do
  let env := (← getEnv).toKernelEnv
  for n in [``optParam, ``autoParam, ``outParam, ``semiOutParam] do
    check (env.isTypeAnnotationWrapper n) s!"prelude {n} not recognised"
  for n in [``id, ``Nat, ``Eq] do
    check (!env.isTypeAnnotationWrapper n) s!"{n} recognised as a wrapper"
  let nat : Expr := .const ``Nat []
  let opt := mkApp2 (.const ``optParam [1]) nat (mkRawNatLit 0)
  check (opt.consumeTypeAnnotationsVerified env.isTypeAnnotationWrapper == nat)
    "prelude optParam not stripped"
  let out := mkApp (.const ``outParam [1]) nat
  check (out.consumeTypeAnnotationsVerified env.isTypeAnnotationWrapper == nat)
    "prelude outParam not stripped"
  let kenv ← lean4leanAdd env (oneFieldDecl `TAWPrelude opt)
  let some (.recInfo r) := kenv.find? `TAWPrelude.rec | throwError "no TAWPrelude.rec"
  check (minorFieldDomain? r.type == some nat)
    s!"the recursor of a prelude optParam field is not stripped: {r.type}"

-- A hostile `optParam`: `def optParam (α β : Type) : Type := β`.
run_meta do
  let ty : Expr := .sort 1
  let a : Expr := .const `A []
  let b : Expr := .const `B []
  let mut env := Kernel.Environment.empty `TAWHostile
  for n in [`A, `B] do
    let ax : AxiomVal := { name := n, levelParams := [], type := ty, isUnsafe := false }
    env ← lean4leanAdd env (.axiomDecl ax)
  let hostile : DefinitionVal :=
   { name := ``optParam, levelParams := []
     type := Expr.forallE (Name.mkSimple "α") ty (Expr.forallE (Name.mkSimple "β") ty ty BinderInfo.default) BinderInfo.default
     value := Expr.lam (Name.mkSimple "α") ty (Expr.lam (Name.mkSimple "β") ty (.bvar 0) BinderInfo.default) BinderInfo.default
     hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe, all := [``optParam] }
  env ← lean4leanAdd env (.defnDecl hostile)
  check (!env.isTypeAnnotationWrapper ``optParam) "hostile optParam recognised"
  let dom := mkApp2 (.const ``optParam []) a b
  check (dom.consumeTypeAnnotationsVerified env.isTypeAnnotationWrapper == dom)
    "hostile optParam stripped"
  let decl := oneFieldDecl `T dom
  let kenv ← lean4leanAdd env decl
  let some (.ctorInfo c) := kenv.find? `T.mk | throwError "no T.mk"
  check (c.type == Expr.forallE (Name.mkSimple "x") dom (.const `T []) BinderInfo.default) "constructor type changed"
  let some (.recInfo r) := kenv.find? `T.rec | throwError "no T.rec"
  check (minorFieldDomain? r.type == some dom)
    s!"Lean4Lean's recursor does not keep the literal domain: {r.type}"
  -- Lean's kernel strips `optParam A B` to `A` by name.
  match env.addDecl {} decl with
  | .error e => throwError "Lean's kernel rejected T: {e.toMessageData {}}"
  | .ok kenv' =>
    let some (.recInfo r') := kenv'.find? `T.rec | throwError "no T.rec from Lean's kernel"
    check (minorFieldDomain? r'.type == some a)
      s!"Lean's kernel no longer strips the hostile optParam: {r'.type}"

end Lean4Lean.Tests.TypeAnnotationWrappers
