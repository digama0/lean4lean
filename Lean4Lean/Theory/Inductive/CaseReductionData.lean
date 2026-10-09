import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.Pattern

/-! Applied case rules are extracted from generated, restored equations. The
shared lambda/forall telescope is retained and checked syntactically. Matching
an application uses the entire specialized left side, including constructor
parameters, indices and universe arguments. -/

deriving instance DecidableEq for Lean4Lean.VLevel
deriving instance DecidableEq for Lean4Lean.VExpr

namespace Lean4Lean.InductiveSignature.CaseSchema

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

/-- An abstract case head and the exact restored constructor major. -/
structure Application where
  block : Name
  owner : Nat
  levels : List VLevel
  arguments : List VExpr
  ctorName : Name
  ctorLevels : List VLevel
  ctorArguments : List VExpr

/-- The final argument is the fully specialized constructor application. -/
def Application.expr (a : Application) : VExpr :=
  .app (VExpr.mkApps (.elim a.block a.owner a.levels) a.arguments)
    (VExpr.mkApps (.const a.ctorName a.ctorLevels) a.ctorArguments)

/-- Recognize a saturated abstract case application. Recursor constants are never
interpreted as abstract heads. -/
def Application.extract : VExpr → Option Application
  | .app fn major =>
    match fn.getAppFnArgs, major.getAppFnArgs with
    | (.elim block owner levels, arguments), (.const ctorName ctorLevels,
        ctorArguments) =>
      some {
        block := block
        owner := owner
        levels := levels
        arguments := arguments
        ctorName := ctorName
        ctorLevels := ctorLevels
        ctorArguments := ctorArguments }
    | _, _ => none
  | _ => none

private theorem rebuild_spine (e : VExpr) :
    VExpr.mkApps e.getAppFnArgs.1 e.getAppFnArgs.2 = e := by
  suffices ∀ args, VExpr.mkApps (VExpr.getAppFnArgs.go e args).1
      (VExpr.getAppFnArgs.go e args).2 = VExpr.mkApps e args from this []
  induction e with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

theorem Application.extract_sound (h : Application.extract e = some a) : a.expr = e := by
  cases e <;> simp only [Application.extract, reduceCtorEq] at h <;> try contradiction
  rename_i fn major
  split at h <;> simp_all
  rename_i hfn hmajor
  have hf := rebuild_spine fn
  have hm := rebuild_spine major
  simp only [hfn, hmajor] at hf hm
  cases h
  simp only [Application.expr, hf, hm]

/-- A generated equation together with its parsed applied body. The parser
checks ownership against the registry key and the selected family slot. -/
structure AppliedRule where
  equation : VDefEq
  body : EquationBody
  application : Application

/-- Case minors receive precisely the constructor fields, without
recursive induction hypotheses. Their number is read from the generated body. -/
def AppliedRule.numFields (rule : AppliedRule) : Nat :=
  rule.body.rhs.getAppFnArgs.2.length

def AppliedRule.numPrefix (rule : AppliedRule) : Nat :=
  rule.body.domains.length - rule.numFields

/-- Recover every equation argument from its designated occurrence: the
recursor prefix supplies parameters, motive and minors; the final constructor
arguments supply fields. Indices and specialized constructor parameters are
checked against these arguments, rather than treated as additional inputs. -/
def AppliedRule.capture (rule : AppliedRule) (actual : Application) : List VExpr :=
  actual.arguments.take rule.numPrefix ++
    actual.ctorArguments.drop (actual.ctorArguments.length - rule.numFields)

def AppliedRule.extract (block : Name) (owner : Nat) (equation : VDefEq) :
    Option AppliedRule := do
  let body ← EquationBody.extract equation.lhs equation.rhs equation.type
  let application ← Application.extract body.lhs
  if application.block ≠ block ∨ application.owner ≠ owner then none else
  return { equation, body, application }

theorem AppliedRule.extract_spec {block : Name} {owner : Nat}
    {equation : VDefEq} {rule : AppliedRule}
    (h : AppliedRule.extract block owner equation = some rule) :
    rule.equation = equation ∧
    EquationBody.extract equation.lhs equation.rhs equation.type = some rule.body ∧
    Application.extract rule.body.lhs = some rule.application ∧
    rule.application.block = block ∧ rule.application.owner = owner := by
  simp [AppliedRule.extract] at h
  obtain ⟨body, hb, application, ha, ⟨hblock, howner⟩, rfl⟩ := h
  exact ⟨rfl, hb, ha, hblock, howner⟩

/-- Generation of one applied rule: both the equation and its parsing
come from the selected schema, rather than being supplied by a caller. -/
def Generates (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (rule : AppliedRule) : Prop :=
  ∃ equations, schema.genericEquations block owner = some equations ∧
    rule.equation ∈ equations ∧
    AppliedRule.extract block owner.val rule.equation = some rule

/-- Instantiate the complete generated body simultaneously in telescope order.
Universe instantiation happens before term substitution, so open actual
arguments retain their own universe variables and cannot capture each other. -/
def AppliedRule.lhs (rule : AppliedRule) (levels : List VLevel)
    (arguments : List VExpr) : VExpr :=
  instantiateParams (rule.body.lhs.instL levels) arguments

def AppliedRule.rhs (rule : AppliedRule) (levels : List VLevel)
    (arguments : List VExpr) : VExpr :=
  instantiateParams (rule.body.rhs.instL levels) arguments

def AppliedRule.type (rule : AppliedRule) (levels : List VLevel)
    (arguments : List VExpr) : VExpr :=
  instantiateParams (rule.body.type.instL levels) arguments

variable {schema : CaseSchema} {block : Name}
  {owner : Fin schema.signature.families.size} {rule : AppliedRule}
  {levels : List VLevel} {arguments : List VExpr}

/-- Generation fixes both the registry key and the family slot. -/
theorem Generates.owned (h : schema.Generates block owner rule) :
    rule.application.block = block ∧ rule.application.owner = owner.val := by
  obtain ⟨_, _, _, hextract⟩ := h
  exact (AppliedRule.extract_spec hextract).2.2.2

theorem Generates.body_exact (h : schema.Generates block owner rule) :
    VExpr.wrapLams rule.body.domains rule.body.lhs = rule.equation.lhs ∧
    VExpr.wrapLams rule.body.domains rule.body.rhs = rule.equation.rhs ∧
    VExpr.wrapForalls rule.body.domains rule.body.type = rule.equation.type := by
  obtain ⟨_, _, _, hextract⟩ := h
  exact EquationBody.extract_sound (AppliedRule.extract_spec hextract).2.1

/-- Specialize every application component, including the restored constructor
parameters. A parameter specialization is never replaced by the recursor's
parameter count or by a bare list of variables. -/
def Application.specialize (a : Application) (levels : List VLevel)
    (arguments : List VExpr) : Application where
  block := a.block
  owner := a.owner
  levels := a.levels.map (·.inst levels)
  arguments := a.arguments.map fun e => instantiateParams (e.instL levels) arguments
  ctorName := a.ctorName
  ctorLevels := a.ctorLevels.map (·.inst levels)
  ctorArguments := a.ctorArguments.map fun e =>
    instantiateParams (e.instL levels) arguments

theorem Application.specialize_expr (a : Application)
    {levels : List VLevel} {arguments : List VExpr} :
    (a.specialize levels arguments).expr =
      instantiateParams (a.expr.instL levels) arguments := by
  have subst_application (σ : VExpr.Subst) :
      (a.expr.instL levels).subst σ =
      .app
        (VExpr.mkApps (.elim a.block a.owner (a.levels.map (·.inst levels)))
          (a.arguments.map fun e => (e.instL levels).subst σ))
        (VExpr.mkApps (.const a.ctorName (a.ctorLevels.map (·.inst levels)))
          (a.ctorArguments.map fun e => (e.instL levels).subst σ)) := by
    simp [Application.expr, VExpr.instL, VExpr.subst_mkApps, List.map_map,
      Function.comp_def, VExpr.subst]
  exact (subst_application _).symm

/-- Exact matching retains the complete specialized application, rather than
checking only its head and constructor arity. -/
theorem Generates.lhs_exact (h : schema.Generates block owner rule) :
    rule.lhs levels arguments = (rule.application.specialize levels arguments).expr := by
  obtain ⟨_, _, _, hextract⟩ := h
  have happ := Application.extract_sound (AppliedRule.extract_spec hextract).2.2.1
  rw [Application.specialize_expr, happ]
  rfl

private theorem spine_go_head (e : VExpr) (args : List VExpr) :
    (VExpr.getAppFnArgs.go e args).1 = e.getAppFnArgs.1 := by
  induction e generalizing args with
  | app fn arg ih _ => exact (ih (arg :: args)).trans (ih [arg]).symm
  | _ => rfl

private theorem spine_app_head (fn arg : VExpr) :
    (VExpr.app fn arg).getAppFnArgs.1 = fn.getAppFnArgs.1 :=
  spine_go_head fn [arg]

private theorem spine_mkApps_head (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih => exact (ih (.app fn arg)).trans (spine_app_head fn arg)

theorem Application.head (a : Application) :
    a.expr.getAppFnArgs.1 = .elim a.block a.owner a.levels := by
  simp only [Application.expr, spine_app_head, spine_mkApps_head]
  rfl

private theorem recursor_varN_head {name : Name} {n : Nat}
    {values : (Pattern.varN (.const name) n).Path → VExpr}
    (h : (Pattern.varN (.const name) n).Matches e ls values) :
    e.getAppFnArgs.1 = .const name ls := by
  induction n generalizing e ls with
  | zero => cases h; rfl
  | succ n ih =>
    cases h with | var h => exact (spine_app_head _ _).trans (ih h)

/-- A stored-rule pattern (delta or iota) matches only applications headed by a constant. -/
theorem recursor_pattern_head {pattern : SimplePattern}
    {values : pattern.toPattern.Path → VExpr}
    (h : pattern.toPattern.Matches e ls values) :
    ∃ name, e.getAppFnArgs.1 = .const name ls := by
  cases pattern with
  | defn name => cases h; exact ⟨name, rfl⟩
  | iota name major ctor args =>
    cases h with
    | app hf _ => exact ⟨name, (spine_app_head _ _).trans (recursor_varN_head hf)⟩

end Lean4Lean.InductiveSignature.CaseSchema
