import Lean4Lean.Theory.ProjectionFieldType
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.InductBlock

namespace Lean4Lean



@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
  projections : Name → VProjectionInfo → Prop := fun _ _ => False
  eliminators : Name → InductiveSignature.CaseSchema → Prop := fun _ _ => False

/-- A constant is *rigid* when no definitional rule of the environment is headed by it
after stripping the lambda binders that wrap stored rules: it has no delta rule, and it is
not a recursor. Inductive type constants are rigid. -/
def VEnv.Rigid (env : VEnv) (c : Name) : Prop :=
  ∀ df, env.defeqs df → ∀ ls, df.lhs.stripLams.getAppFnArgs.1 ≠ .const c ls

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False
  projections _ _ := False
  eliminators _ _ := False

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.contains (env : VEnv) (name : Name) := ∃ ci, env.constants name = some ci

def VEnv.addConst (env : VEnv) (name : Name) (ci : VConstant) : Option VEnv :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

def VEnv.addDefEq (env : VEnv) (df : VDefEq) : VEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

/-- Register a pure case-eliminator schema under a declaration block key.
Typing and well-formed installation are separate judgments. -/
def VEnv.addEliminator (env : VEnv) (block : Name)
    (schema : InductiveSignature.CaseSchema) : VEnv :=
  { env with eliminators := fun name value =>
      (name = block ∧ value = schema) ∨ env.eliminators name value }

@[simp] theorem VEnv.addEliminator_iff {env : VEnv} :
    (env.addEliminator block schema).eliminators name value ↔
      (name = block ∧ value = schema) ∨ env.eliminators name value := Iff.rfl

@[simp] theorem VEnv.addEliminator_constants {env : VEnv} :
    (env.addEliminator block schema).constants = env.constants := rfl

@[simp] theorem VEnv.addEliminator_defeqs {env : VEnv} :
    (env.addEliminator block schema).defeqs = env.defeqs := rfl

@[simp] theorem VEnv.addEliminator_projections {env : VEnv} :
    (env.addEliminator block schema).projections = env.projections := rfl

/-- Register a list of case-eliminator schemas, in order. -/
def VEnv.addEliminators : VEnv → List (Name × InductiveSignature.CaseSchema) → VEnv
  | env, [] => env
  | env, (block, schema) :: rest => (env.addEliminator block schema).addEliminators rest

theorem VEnv.addEliminators_iff {env : VEnv} {es : List (Name × InductiveSignature.CaseSchema)} :
    (env.addEliminators es).eliminators name value ↔
      (name, value) ∈ es ∨ env.eliminators name value := by
  induction es generalizing env with
  | nil => simp [VEnv.addEliminators]
  | cons e es ih =>
    obtain ⟨block, schema⟩ := e
    rw [VEnv.addEliminators, ih]
    simp only [List.mem_cons, Prod.mk.injEq, VEnv.addEliminator_iff, or_assoc, or_left_comm]

@[simp] theorem VEnv.addEliminators_constants {env : VEnv} {es} :
    (env.addEliminators es).constants = env.constants := by
  induction es generalizing env with
  | nil => rfl
  | cons e es ih => exact ih

@[simp] theorem VEnv.addEliminators_defeqs {env : VEnv} {es} :
    (env.addEliminators es).defeqs = env.defeqs := by
  induction es generalizing env with
  | nil => rfl
  | cons e es ih => exact ih

@[simp] theorem VEnv.addEliminators_projections {env : VEnv} {es} :
    (env.addEliminators es).projections = env.projections := by
  induction es generalizing env with
  | nil => rfl
  | cons e es ih => exact ih

@[simp] theorem VEnv.addEliminators_nil {env : VEnv} : env.addEliminators [] = env := rfl

theorem VEnv.addEliminator_self {env : VEnv} :
    (env.addEliminator block schema).eliminators block schema := .inl ⟨rfl, rfl⟩

@[simp] theorem VEnv.addDefEq_eliminators (env : VEnv) (df : VDefEq) :
    (env.addDefEq df).eliminators = env.eliminators := rfl

def VEnv.addProjection (env : VEnv) (entry : VProjectionEntry) : VEnv :=
  { env with projections := fun name info =>
      (name = entry.typeName ∧ info = entry.info) ∨ env.projections name info }

def VEnv.addProjections : VEnv → List VProjectionEntry → VEnv
  | env, [] => env
  | env, entry :: entries => (env.addProjection entry).addProjections entries

theorem VEnv.addProjections_iff {env : VEnv} {entries : List VProjectionEntry} :
    (env.addProjections entries).projections name info ↔
      (∃ entry ∈ entries, name = entry.typeName ∧ info = entry.info) ∨
        env.projections name info := by
  induction entries generalizing env with
  | nil => simp [VEnv.addProjections]
  | cons entry entries ih =>
    rw [VEnv.addProjections, ih]
    simp [VEnv.addProjection, or_assoc, or_left_comm]

@[simp] theorem VEnv.addProjection_constants (env : VEnv) (entry : VProjectionEntry) :
    (env.addProjection entry).constants = env.constants := rfl

@[simp] theorem VEnv.addProjection_defeqs (env : VEnv) (entry : VProjectionEntry) :
    (env.addProjection entry).defeqs = env.defeqs := rfl

@[simp] theorem VEnv.addProjection_eliminators (env : VEnv) (entry : VProjectionEntry) :
    (env.addProjection entry).eliminators = env.eliminators := rfl

@[simp] theorem VEnv.addProjections_constants (env : VEnv)
    (entries : List VProjectionEntry) :
    (env.addProjections entries).constants = env.constants := by
  induction entries generalizing env with
  | nil => rfl
  | cons entry entries ih => exact ih (env := env.addProjection entry)

@[simp] theorem VEnv.addProjections_defeqs (env : VEnv)
    (entries : List VProjectionEntry) :
    (env.addProjections entries).defeqs = env.defeqs := by
  induction entries generalizing env with
  | nil => rfl
  | cons entry entries ih => exact ih (env := env.addProjection entry)

@[simp] theorem VEnv.addProjections_eliminators (env : VEnv)
    (entries : List VProjectionEntry) :
    (env.addProjections entries).eliminators = env.eliminators := by
  induction entries generalizing env with
  | nil => rfl
  | cons entry entries ih => exact ih (env := env.addProjection entry)

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df
  projections : env1.projections n p → env2.projections n p
  eliminators : env1.eliminators n s → env2.eliminators n s

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id, id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2, h2.3 ∘ h1.3, h2.4 ∘ h1.4⟩

theorem VEnv.addEliminator_le {env : VEnv} : env ≤ env.addEliminator block schema :=
  ⟨id, id, id, Or.inr⟩

theorem VEnv.addEliminators_le {env : VEnv} {es} : env ≤ env.addEliminators es :=
  ⟨by simp, by simp, by simp, fun h => VEnv.addEliminators_iff.mpr (Or.inr h)⟩

theorem VEnv.addEliminators_mono {env₁ env₂ : VEnv} {es} (H : env₁ ≤ env₂) :
    env₁.addEliminators es ≤ env₂.addEliminators es where
  constants h := by simpa using H.constants (by simpa using h)
  defeqs h := by simpa using H.defeqs (by simpa using h)
  projections h := by simpa using H.projections (by simpa using h)
  eliminators := fun h => VEnv.addEliminators_iff.mpr
    ((VEnv.addEliminators_iff.mp h).imp_right H.eliminators)

theorem VEnv.addConst_le {env env' : VEnv}
    (h : env.addConst n ci = some env') : env ≤ env' := by
  unfold addConst at h; split at h <;> cases h
  exact ⟨fun _ => by simp; split <;> simp_all, by simp [*], id, id⟩

theorem VEnv.addConst_self {env env' : VEnv}
    (h : env.addConst n ci = some env') :
    env'.constants n = some ci := by
  unfold addConst at h; split at h <;> cases h; simp

theorem VEnv.addConst_constants_of_ne {env env' : VEnv}
    (h : env.addConst n ci = some env') (hne : n ≠ p) :
    env'.constants p = env.constants p := by
  unfold addConst at h
  split at h <;> cases h
  simp [hne]

theorem VEnv.addConst_projections {env env' : VEnv}
    (h : env.addConst n ci = some env') :
    env'.projections = env.projections := by
  unfold addConst at h
  split at h <;> cases h
  rfl

theorem VEnv.addConst_eliminators {env env' : VEnv}
    (h : env.addConst n ci = some env') :
    env'.eliminators = env.eliminators := by
  unfold addConst at h
  split at h <;> cases h
  rfl

theorem VEnv.addConst_defeqs {env env' : VEnv}
    (h : env.addConst n ci = some env') : env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h
  split at h <;> cases h
  rfl

theorem VEnv.addConst_fresh {env env' : VEnv} (h : env.addConst n ci = some env') :
    env.constants n = none := by
  unfold VEnv.addConst at h
  split at h <;> cases h
  assumption

theorem VEnv.LE.constants_eq_none_left {source target : VEnv} (H : source ≤ target)
    (hnone : target.constants name = none) : source.constants name = none := by
  cases hb : source.constants name with
  | none => rfl
  | some ci => rw [H.constants hb] at hnone; cases hnone

theorem VEnv.addDefEq_le {env : VEnv} : env ≤ env.addDefEq df :=
  ⟨id, .inr, id, id⟩

theorem VEnv.addDefEq_self {env : VEnv} :
    (env.addDefEq df).defeqs df := .inl rfl

theorem VEnv.addProjection_le {env : VEnv} {entry : VProjectionEntry} :
    env ≤ env.addProjection entry where
  constants := id
  defeqs := id
  projections hinfo := Or.inr hinfo
  eliminators := id

theorem VEnv.addProjections_le {env : VEnv} {entries : List VProjectionEntry} :
    env ≤ env.addProjections entries := by
  induction entries generalizing env with
  | nil => exact .rfl
  | cons entry entries ih => exact addProjection_le.trans ih

/-- The constructor environment is below its extension by the block's eliminators and
projections (the recursor-checking environment). -/
theorem VEnv.addEliminators_addProjections_le {env : VEnv} {es}
    {entries : List VProjectionEntry} : env ≤ (env.addEliminators es).addProjections entries :=
  addEliminators_le.trans addProjections_le

theorem VEnv.addProjection_mono {env₁ env₂ : VEnv} {entry : VProjectionEntry}
    (H : env₁ ≤ env₂) :
    env₁.addProjection entry ≤ env₂.addProjection entry where
  constants := H.constants
  defeqs := H.defeqs
  projections := fun hinfo => hinfo.elim Or.inl (Or.inr ∘ H.projections)
  eliminators := H.eliminators

theorem VEnv.addProjections_mono {env₁ env₂ : VEnv}
    {entries : List VProjectionEntry} (H : env₁ ≤ env₂) :
    env₁.addProjections entries ≤ env₂.addProjections entries := by
  induction entries generalizing env₁ env₂ with
  | nil => exact H
  | cons entry entries ih => exact ih (addProjection_mono H)
