import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.Formation

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

/-! ### Names of a restoration table and basic facts about `Restoration.expr`

The helpers the restoration metatheory (`Theory/Typing/RestorationShapes.lean`,
`Theory/Inductive/RestorationInterpretation.lean`, `RestorationHead.lean`) reads off a
`Restoration`:

* `Restoration.restorableNames`: the auxiliary heads and the renamed recursors;
* `Restoration.headName`: the constant a restored head is renamed to;
* `Restoration.expr` on application spines (`expr_mkApps`), equations (`equation_parts`) and
  on terms avoiding the restorable names (`expr_of_avoid`);
* `VExpr.projNamesAvoid` and two closedness lemmas for λ-telescopes and spines. -/

namespace Lean4Lean

namespace VExpr

/-- No projection type name of the term is in `names`. -/
def projNamesAvoid (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ | .const .. => true
  | .app f a | .lam f a | .forallE f a => f.projNamesAvoid names && a.projNamesAvoid names
  | .proj n _ e => !names.contains n && e.projNamesAvoid names

theorem ClosedN.mkApps_closed {fn : VExpr} {args : List VExpr} {n : Nat} (hf : fn.ClosedN n)
    (ha : ∀ arg ∈ args, arg.ClosedN n) : (VExpr.mkApps fn args).ClosedN n := by
  induction args generalizing fn with
  | nil => exact hf
  | cons a args ih => exact ih ⟨hf, ha _ (.head _)⟩ (fun _ h => ha _ (.tail _ h))

/-- Close a lambda telescope whose domains are scoped in binder order. -/
theorem ClosedN.wrapLams_closed {domains : List VExpr} {body : VExpr} {n : Nat}
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapLams domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      rwa [Nat.add_comm i 1, ← Nat.add_assoc] at hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

end VExpr

namespace InductiveSignature

/-- The names a restoration replaces: its auxiliary heads and its renamed recursors. -/
def Restoration.restorableNames (r : Restoration) : List Name :=
  r.heads.map (·.auxiliary) ++ r.recursors.map Prod.fst

theorem Restoration.heads_find?_eq_none {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) :
    r.heads.find? (fun h => h.auxiliary == name) = none := by
  apply List.find?_eq_none.mpr
  intro head hmem heq
  exact h (List.mem_map.mpr ⟨head, hmem, by simpa using heq⟩)

theorem Restoration.recursorName_of_not_mem {r : Restoration} {name : Name}
    (h : name ∉ r.recursors.map Prod.fst) : r.recursorName name = name := by
  unfold Restoration.recursorName
  rw [List.find?_eq_none.mpr]
  intro pair hpair heq
  exact h (List.mem_map.mpr ⟨pair, hpair, by simpa using heq⟩)

/-- The constant a restored head becomes: the target of a specialized head, the renamed
recursor otherwise. -/
def Restoration.headName (r : Restoration) (name : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == name) with
  | some h => h.target
  | none => r.recursorName name

theorem Restoration.expr_eq_go (r : Restoration) (e : VExpr) :
    r.expr e = Restoration.expr.go r e [] := rfl

theorem Restoration.go_mkApps (r : Restoration) (f : VExpr) (args acc : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps f args) acc =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f (args' ++ acc) := by
  induction args generalizing f acc with
  | nil => simp [VExpr.mkApps]
  | cons a as ih =>
    have hm : VExpr.mkApps f (a :: as) = VExpr.mkApps (.app f a) as := rfl
    rw [hm, ih]
    simp only [Restoration.expr.go, List.mapM_cons]
    cases ha : Restoration.expr.go r a [] <;>
      cases has : as.mapM r.expr <;> simp [ha, Restoration.expr_eq_go]

theorem Restoration.expr_mkApps (r : Restoration) (f : VExpr) (args : List VExpr) :
    r.expr (VExpr.mkApps f args) =
      (args.mapM r.expr).bind fun args' => Restoration.expr.go r f args' := by
  simp [Restoration.expr_eq_go, Restoration.go_mkApps]

/-- `go_mkApps` in `do` form. -/
theorem restoration_mkApps (r : Restoration) (fn : VExpr) (inputArgs args : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps fn inputArgs) args = (do
      let restoredArgs ← inputArgs.mapM r.expr
      Restoration.expr.go r fn (restoredArgs ++ args)) :=
  Restoration.go_mkApps r fn inputArgs args

theorem Restoration.equation_parts {r : Restoration} {source restored : VDefEq}
    (h : r.equation source = some restored) :
    r.expr source.lhs = some restored.lhs ∧ r.expr source.rhs = some restored.rhs ∧
      r.expr source.type = some restored.type := by
  simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at h
  obtain ⟨lhs, hl, rhs, hr, type, ht, h⟩ := h
  cases h
  exact ⟨hl, hr, ht⟩

theorem Restoration.go_of_avoid {r : Restoration} :
    ∀ {e : VExpr} {args : List VExpr}, e.containsAnyConst r.restorableNames = false →
      Restoration.expr.go r e args = some (VExpr.mkApps e args)
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .const name levels, args, h => by
    have hn : name ∉ r.restorableNames := by simpa [VExpr.containsAnyConst] using h
    have hh : name ∉ r.heads.map (·.auxiliary) := fun hm =>
      hn (List.mem_append_left _ hm)
    have hrec : name ∉ r.recursors.map Prod.fst := fun hm =>
      hn (List.mem_append_right _ hm)
    simp only [Restoration.expr.go, Restoration.heads_find?_eq_none hh,
      Restoration.recursorName_of_not_mem hrec]
  | .app f a, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [Restoration.expr.go, go_of_avoid h.2, Option.bind_eq_bind, Option.bind_some]
    exact go_of_avoid (args := _ :: args) h.1
  | .lam d b, args, h | .forallE d b, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, Restoration.expr_eq_go, go_of_avoid h.1, go_of_avoid h.2,
      VExpr.mkApps]
  | .proj n i e, args, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp [Restoration.expr.go, Restoration.expr_eq_go, go_of_avoid h.2, VExpr.mkApps]

/-- Restoration fixes every term that avoids its restorable names. -/
theorem Restoration.expr_of_avoid {r : Restoration} {e : VExpr}
    (h : e.containsAnyConst r.restorableNames = false) : r.expr e = some e :=
  Restoration.go_of_avoid (args := []) h

theorem Restoration.mapM_expr_of_avoid {r : Restoration} :
    ∀ {l : List VExpr}, (∀ e ∈ l, e.containsAnyConst r.restorableNames = false) →
      l.mapM r.expr = some l
  | [], _ => rfl
  | e :: l, h => by
    rw [List.mapM_cons, Restoration.expr_of_avoid (h e List.mem_cons_self),
      mapM_expr_of_avoid (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

end InductiveSignature
end Lean4Lean
