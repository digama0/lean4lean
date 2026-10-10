import Lean4Lean.Theory.Inductive.SignatureData

/-! Total restoration of generated inductive syntax.

An auxiliary family or constructor is a parameter specialization of a source
constant. Restoration substitutes the actual common parameters into that
specialization and preserves the remaining indices/fields. Recursor names
are renamed separately. This module accepts no replacement equation bodies:
both sides and the type of every restored equation come from generation.
The finite formation derivation must justify the specialization table.
-/

namespace Lean4Lean.InductiveSignature

/-- One specialized family or constructor head. `arguments` is scoped under
`nparams` common parameters, in telescope order; `levels` uses `uvars` source
universe variables. The target may have a different number of parameters. -/
structure HeadSpecialization where
  auxiliary : Name
  uvars : Nat
  nparams : Nat
  target : Name
  levels : List VLevel
  arguments : List VExpr

/-- Scope of the parameter substitution. Typing and ownership are additional
formation obligations, not consequences of this syntactic condition. -/
def HeadSpecialization.Scoped (h : HeadSpecialization) : Prop :=
  (∀ level ∈ h.levels, level.WF h.uvars) ∧
  (∀ argument ∈ h.arguments, argument.ClosedN h.nparams)

/-- Simultaneous substitution, with actual arguments in telescope order.
Inserted arguments are not subsequently substituted into each other. -/
def instantiateParams (body : VExpr) (args : List VExpr) : VExpr :=
  body.subst fun i =>
    if hi : i < args.length then args[args.length - 1 - i]
    else .bvar (i - args.length)

/-- Remove the parameter telescope before simultaneously substituting its
arguments. A short telescope is rejected. -/
def specializeType (type : VExpr) (args : List VExpr) : Option VExpr := do
  let (_, body) ← type.takeForalls args.length
  return instantiateParams body args

/-- Restore a fully applied specialized head. Partial applications and wrong
universe arities have no restoration, rather than silently dropping syntax. -/
def HeadSpecialization.apply (h : HeadSpecialization)
    (levels : List VLevel) (args : List VExpr) : Option VExpr := do
  if levels.length != h.uvars || args.length < h.nparams then none else
  let params := args.take h.nparams
  let specialized := h.arguments.map fun arg => instantiateParams (arg.instL levels) params
  return VExpr.mkApps (.const h.target (h.levels.map (·.inst levels)))
    (specialized ++ args.drop h.nparams)

structure Restoration where
  heads : List HeadSpecialization := []
  recursors : List (Name × Name) := []

/-- A restoration table must give each head a unique interpretation. -/
def Restoration.Scoped (r : Restoration) : Prop :=
  (r.heads.map (·.auxiliary)).Nodup ∧
  (r.recursors.map Prod.fst).Nodup ∧
  (∀ h ∈ r.heads, h.Scoped) ∧
  ∀ h ∈ r.heads, h.auxiliary ∉ r.recursors.map Prod.fst

def Restoration.recursorName (r : Restoration) (name : Name) : Name :=
  match r.recursors.find? (fun pair => pair.1 == name) with
  | some pair => pair.2
  | none => name

/-- Traverse complete application spines, restoring their arguments before
substituting a specialized head. This also restores nested occurrences in
indices and higher-order fields. Recursion is structural on the input term. -/
def Restoration.expr (r : Restoration) (e : VExpr) : Option VExpr :=
  go e []
where
  go : VExpr → List VExpr → Option VExpr
    | .app fn arg, args => do
      let arg' ← go arg []
      go fn (arg' :: args)
    | .const name levels, args =>
      match r.heads.find? (fun h => h.auxiliary == name) with
      | some h => h.apply levels args
      | none => some (VExpr.mkApps (.const (r.recursorName name) levels) args)
    | .bvar i, args => some (VExpr.mkApps (.bvar i) args)
    | .sort u, args => some (VExpr.mkApps (.sort u) args)
    | .lam domain body, args => do
      let domain' ← go domain []
      let body' ← go body []
      return VExpr.mkApps (.lam domain' body') args
    | .forallE domain body, args => do
      let domain' ← go domain []
      let body' ← go body []
      return VExpr.mkApps (.forallE domain' body') args
    | .proj name i major, args => do
      let major' ← go major []
      return VExpr.mkApps (.proj name i major') args

/-- The recursor's type is restored along with its generated name. -/
def Restoration.recursor (r : Restoration) (value : VConstVal) : Option VConstVal := do
  return { value with name := r.recursorName value.name, type := ← r.expr value.type }

/-- Exact restoration of all three generated equation expressions. -/
def Restoration.equation (r : Restoration) (equation : VDefEq) : Option VDefEq := do
  return { equation with
    lhs := ← r.expr equation.lhs
    rhs := ← r.expr equation.rhs
    type := ← r.expr equation.type }

def Instance.restoredRecursors {s : InductiveSignature}
    (g : Instance s) (r : Restoration) : Option (List VConstVal) :=
  g.recursors.mapM r.recursor

def Instance.restoredEquations {s : InductiveSignature}
    (g : Instance s) (r : Restoration) : Option (List VDefEq) :=
  g.equations.mapM r.equation

@[simp] theorem Restoration.expr_empty (e : VExpr) :
    ({} : Restoration).expr e = some e := by
  suffices h : ∀ args, Restoration.expr.go {} e args = some (VExpr.mkApps e args) from h []
  induction e with
  | bvar | sort | const => intros; rfl
  | app fn arg ihfn iharg =>
    intro args
    simp [Restoration.expr.go, iharg, ihfn, VExpr.mkApps]
  | lam domain body ihdomain ihbody =>
    intro args
    simp [Restoration.expr.go, ihdomain, ihbody, VExpr.mkApps]
  | forallE domain body ihdomain ihbody =>
    intro args
    simp [Restoration.expr.go, ihdomain, ihbody, VExpr.mkApps]
  | proj name i major ih =>
    intro args
    simp [Restoration.expr.go, ih, VExpr.mkApps]

@[simp] theorem Restoration.recursor_empty (value : VConstVal) :
    ({} : Restoration).recursor value = some value := by
  simp [Restoration.recursor, Restoration.recursorName]

@[simp] theorem Restoration.equation_empty (equation : VDefEq) :
    ({} : Restoration).equation equation = some equation := by
  simp [Restoration.equation]

@[simp] theorem Instance.restoredRecursors_empty {s : InductiveSignature}
    (g : Instance s) : g.restoredRecursors {} = some g.recursors := by
  unfold Instance.restoredRecursors
  have h : ({} : Restoration).recursor = (pure : VConstVal → Option VConstVal) :=
    funext Restoration.recursor_empty
  rw [h, List.mapM_pure]
  simp

@[simp] theorem Instance.restoredEquations_empty {s : InductiveSignature}
    (g : Instance s) : g.restoredEquations {} = some g.equations := by
  unfold Instance.restoredEquations
  have h : ({} : Restoration).equation = (pure : VDefEq → Option VDefEq) :=
    funext Restoration.equation_empty
  rw [h, List.mapM_pure]
  simp

@[simp] theorem Restoration.expr_bvar (r : Restoration) (i : Nat) :
    r.expr (.bvar i) = some (.bvar i) := rfl

@[simp] theorem Restoration.expr_sort (r : Restoration) (u : VLevel) :
    r.expr (.sort u) = some (.sort u) := rfl

end Lean4Lean.InductiveSignature
