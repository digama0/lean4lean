import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ConstructorMajor

/-! # The schema of a registered recursor

The data of a compiled declaration that the confluence development reads off a recursor:
the source families it owns, the generated signature and the restoration table. The ι pattern
calculus has no abstract eliminators, so these three data fields are the whole schema.

`EquationBody` (the open body of a generated equation with its shared λ/∀ telescope) and the
closedness helpers of the telescope are here too. -/

namespace Lean4Lean.InductiveSignature

structure RecursorSchema where
  /-- Source families owned by this block, excluding auxiliary families. -/
  sourceFamilies : List Name
  signature : InductiveSignature
  restoration : Restoration

namespace RecursorSchema

/-- The schema of a compilation: the source families, the generated signature and the
restoration table of the specializations. -/
def ofCompilation (source : VInductDecl) (s : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) : RecursorSchema :=
  ⟨source.types.map (·.name), s, compilationRestoration source auxiliaries⟩

/-- The source sort is specialized at the occurrence, independently of the
recursor's permitted elimination universe. -/
def sourceLevel (schema : RecursorSchema) (owner : Fin schema.signature.families.size)
    (levels : List VLevel) : VLevel :=
  schema.signature.families[owner].resultLevel.inst levels

/-- The open body of a generated equation, with its exact shared telescope. -/
structure EquationBody where
  domains : List VExpr
  lhs : VExpr
  rhs : VExpr
  type : VExpr

/-- Peel matching lambda binders and their forall type together. Mismatched
binder domains or telescope lengths are rejected. -/
def EquationBody.extract : VExpr → VExpr → VExpr → Option EquationBody
  | .lam domain lhs, .lam domain' rhs, .forallE domain'' type => do
    if domain ≠ domain' ∨ domain ≠ domain'' then none else
    let body ← extract lhs rhs type
    return { body with domains := domain :: body.domains }
  | .lam .., _, _ => none
  | lhs, rhs, type => some { domains := [], lhs, rhs, type }

/-- Extraction preserves both generated equation sides and their type. -/
theorem EquationBody.extract_sound {lhs rhs type : VExpr} {body : EquationBody}
    (h : EquationBody.extract lhs rhs type = some body) :
    VExpr.wrapLams body.domains body.lhs = lhs ∧
    VExpr.wrapLams body.domains body.rhs = rhs ∧
    VExpr.wrapForalls body.domains body.type = type := by
  induction lhs generalizing rhs type body with
  | lam domain lhs ihDomain ih =>
    cases rhs <;> cases type <;> simp [EquationBody.extract] at h
    obtain ⟨⟨rfl, rfl⟩, inner, hextract, rfl⟩ := h
    obtain ⟨hl, hr, ht⟩ := ih hextract
    simp [VExpr.wrapLams, VExpr.wrapForalls, ← hl, ← hr, ← ht]
  | _ => simp only [EquationBody.extract, Option.some.injEq] at h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- The extracted left body is not a λ. -/
theorem EquationBody.extracted_lhs_stripLams {lhs rhs type : VExpr} {body : EquationBody}
    (H : EquationBody.extract lhs rhs type = some body) :
    body.lhs.stripLams = body.lhs := by
  induction lhs generalizing rhs type body with
  | lam domain lhs ihDomain ih =>
    cases rhs <;> cases type <;> simp [EquationBody.extract] at H
    obtain ⟨⟨rfl, rfl⟩, inner, hi, rfl⟩ := H
    exact ih (body := inner) hi
  | _ => simp only [EquationBody.extract, Option.some.injEq] at H; cases H; rfl

end RecursorSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.VExpr

/-- Argument accumulation of `getAppFnArgs`. -/
theorem getAppFnArgs_go_eq (e : VExpr) (args : List VExpr) :
    VExpr.getAppFnArgs.go e args = (e.getAppFnArgs.1, e.getAppFnArgs.2 ++ args) := by
  induction e generalizing args with
  | app f a ih _ =>
    change VExpr.getAppFnArgs.go f (a :: args) = _
    rw [ih]
    change _ = ((VExpr.getAppFnArgs.go f [a]).1, (VExpr.getAppFnArgs.go f [a]).2 ++ args)
    rw [ih]
    simp
  | _ => rfl

/-- The spine of an application: the function's spine extended by the argument. -/
theorem case_spine_app (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs = (fn.getAppFnArgs.1, fn.getAppFnArgs.2 ++ [arg]) := by
  show VExpr.getAppFnArgs.go fn [arg] = _
  rw [getAppFnArgs_go_eq]

theorem spine_app_head (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  show (VExpr.getAppFnArgs.go fn [arg]).1 = _
  rw [getAppFnArgs_go_eq]

theorem spine_mkApps_head (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih => exact (ih (.app fn arg)).trans (spine_app_head fn arg)

/-- The spine of an application of a head without arguments. -/
theorem spine_mkApps_exact (fn : VExpr) (args : List VExpr)
    (h : fn.getAppFnArgs = (fn, [])) :
    (VExpr.mkApps fn args).getAppFnArgs = (fn, args) := by
  have apps : ∀ fn args acc, VExpr.getAppFnArgs.go (VExpr.mkApps fn args) acc =
      VExpr.getAppFnArgs.go fn (args ++ acc) := by
    intro fn args
    induction args generalizing fn with
    | nil => intros; rfl
    | cons a as ih => intro acc; exact ih (.app fn a) acc
  change VExpr.getAppFnArgs.go (VExpr.mkApps fn args) [] = _
  rw [apps, List.append_nil, getAppFnArgs_go_eq, h]
  rfl

/-- The spine head is the application head. -/
theorem getAppFn_eq_fst : ∀ e : VExpr, e.getAppFn = e.getAppFnArgs.1
  | .app f a => by rw [VExpr.getAppFn, spine_app_head]; exact getAppFn_eq_fst f
  | .bvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .proj .. => rfl

/-- An expression is the application of its head to its arguments. -/
theorem rebuild_spine (e : VExpr) :
    VExpr.mkApps e.getAppFnArgs.1 e.getAppFnArgs.2 = e := by
  suffices ∀ args, VExpr.mkApps (VExpr.getAppFnArgs.go e args).1
      (VExpr.getAppFnArgs.go e args).2 = VExpr.mkApps e args from this []
  induction e with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

theorem closed_wrapLams_body {domains : List VExpr} {body : VExpr} {k : Nat}
    (h : (VExpr.wrapLams domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapLams domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem closed_wrapForalls_body {domains : List VExpr} {body : VExpr} {k : Nat}
    (h : (VExpr.wrapForalls domains body).ClosedN k) : body.ClosedN (k + domains.length) := by
  induction domains generalizing k with
  | nil => exact h
  | cons domain domains ih =>
    have := ih (show (VExpr.wrapForalls domains body).ClosedN (k + 1) from h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem closed_wrapForalls_domain {domains : List VExpr} {body : VExpr} {k i : Nat}
    (hc : (VExpr.wrapForalls domains body).ClosedN k)
    (hi : i < domains.length) : domains[i].ClosedN (k + i) := by
  induction domains generalizing k i with
  | nil => cases hi
  | cons domain domains ih =>
    cases i with
    | zero => exact hc.1
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih hc.2 (Nat.lt_of_succ_lt_succ hi)

/-- A scoped simultaneous substitution preserves the indicated scope. -/
theorem ClosedN.subst_closed {e : VExpr} {k n : Nat} {σ : Subst} (he : e.ClosedN k)
    (hσ : ∀ i < k, (σ i).ClosedN n) : (e.subst σ).ClosedN n := by
  induction e generalizing k n σ with (simp only [ClosedN, subst] at he ⊢)
  | bvar i => exact hσ i he
  | app _ _ ih1 ih2 => exact ⟨ih1 he.1 hσ, ih2 he.2 hσ⟩
  | proj _ _ _ ih => exact ih he hσ
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    refine ⟨ih1 he.1 hσ, ih2 he.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact (hσ i (by omega)).liftN

theorem ClosedN.wrapForalls_closed {domains : List VExpr} {body : VExpr} {n : Nat}
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapForalls domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

/-- Applications of variables to variables, in order: the shape of the index arguments of a
generated equation, left untouched by universe instantiation. -/
inductive VariableApplications : VExpr → Prop where
  | bvar : VariableApplications (.bvar i)
  | app : VariableApplications fn → VariableApplications arg → VariableApplications (.app fn arg)

theorem VariableApplications.instL_eq {e : VExpr} {levels : List VLevel}
    (H : VariableApplications e) : e.instL levels = e := by
  induction H with
  | bvar => rfl
  | app _ _ ihf iha => simp only [VExpr.instL, ihf, iha]

end Lean4Lean.VExpr

namespace Lean4Lean

theorem case_forall₂_get {α β : Type _} {R : α → β → Prop} {xs : List α} {ys : List β} {i : Nat}
    (h : List.Forall₂ R xs ys) (hi : i < xs.length) (hi' : i < ys.length) :
    R xs[i] ys[i] := by
  induction h generalizing i with
  | nil => cases hi
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih (by simpa using hi) (by simpa using hi')

end Lean4Lean

namespace Lean4Lean.SimplePattern

theorem recursor_varN_head {name : Name} {n : Nat} {e : VExpr} {ls : List VLevel}
    {values : (Pattern.varN (.const name) n).Path → VExpr}
    (h : (Pattern.varN (.const name) n).Matches e ls values) :
    e.getAppFnArgs.1 = .const name ls := by
  induction n generalizing e ls with
  | zero => cases h; rfl
  | succ n ih =>
    cases h with | var h => exact (VExpr.spine_app_head _ _).trans (ih h)

/-- A simple pattern (delta or iota) matches only applications headed by a constant. -/
theorem recursor_pattern_head {pattern : SimplePattern} {e : VExpr} {ls : List VLevel}
    {values : pattern.toPattern.Path → VExpr}
    (h : pattern.toPattern.Matches e ls values) :
    ∃ name, e.getAppFnArgs.1 = .const name ls := by
  cases pattern with
  | defn name => cases h; exact ⟨name, rfl⟩
  | iota name major ctor args =>
    cases h with
    | app hf _ => exact ⟨name, (VExpr.spine_app_head _ _).trans (recursor_varN_head hf)⟩

end Lean4Lean.SimplePattern

namespace Lean4Lean.InductiveSignature

/-- `instantiateParams` is the outer instantiation. -/
theorem instantiateParams_eq_instOuter (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

/-- Simultaneous parameter substitution of a scoped template commutes with substitution. -/
theorem instantiateParams_subst {body : VExpr} {arguments : List VExpr}
    (hc : body.ClosedN arguments.length) (σ : VExpr.Subst) :
    (instantiateParams body arguments).subst σ =
      instantiateParams body (arguments.map (·.subst σ)) := by
  let σ₀ : VExpr.Subst := fun i =>
    if hi : i < arguments.length then arguments[arguments.length - 1 - i]
    else .bvar (i - arguments.length)
  change (body.subst σ₀).subst σ = _
  rw [VExpr.subst_subst]
  unfold instantiateParams
  apply VExpr.subst_congr_closedN hc
  intro i hi
  simp [σ₀, VExpr.Subst.comp, hi]

/-- Simultaneous parameter substitution of a scoped template commutes with renaming. -/
theorem instantiateParams_lift' {body : VExpr} {arguments : List VExpr}
    (hc : body.ClosedN arguments.length) (ρ : Lift) :
    (instantiateParams body arguments).lift' ρ =
      instantiateParams body (arguments.map (·.lift' ρ)) := by
  let σ₀ : VExpr.Subst := fun i =>
    if hi : i < arguments.length then arguments[arguments.length - 1 - i]
    else .bvar (i - arguments.length)
  change (body.subst σ₀).lift' ρ = _
  rw [VExpr.lift'_subst]
  unfold instantiateParams
  apply VExpr.subst_congr_closedN hc
  intro i hi
  simp only [σ₀, VExpr.Subst.lift_r, List.length_map, dif_pos hi, List.getElem_map]

/-- Simultaneous parameter substitution of a scoped template commutes with instantiation. -/
theorem instantiateParams_instN {body : VExpr} {arguments : List VExpr}
    (hc : body.ClosedN arguments.length) {value : VExpr} {k : Nat} :
    (instantiateParams body arguments).inst value k =
      instantiateParams body (arguments.map fun arg => arg.inst value k) := by
  simpa only [← VExpr.instN_eq] using
    instantiateParams_subst hc (VExpr.Subst.liftN (VExpr.Subst.one value) k)

end Lean4Lean.InductiveSignature
