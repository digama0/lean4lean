import Lean4Lean.Theory.ProjectionFieldType
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.InductBlock

namespace Lean4Lean

@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
  /-- Schematic reduction rules, keyed by a `Pattern` (the redex shape) and its
  reduct/side-condition pair; the registry for ι-reduction rules. -/
  pats : (p : Pattern) → p.RHS × p.Check → Prop
  /-- Projection metadata of the registered structures, read by the projection rules
  `projDF`/`projIota`/`structEta`/`unitLike`. -/
  projections : Name → VProjectionInfo → Prop := fun _ _ => False

/-- The head constant of a pattern: the constant at the root of its application spine. -/
def Pattern.headConst : Pattern → Name
  | .const c => c
  | .app f _ => f.headConst
  | .var f => f.headConst

/-- A constant is *rigid* when no reduction rule of the environment is headed by it: no
definitional axiom (after stripping the lambda binders that wrap stored rules) and no
registered pattern rule has it as head. Inductive type constants are rigid. -/
structure VEnv.Rigid (env : VEnv) (c : Name) : Prop where
  defeqs : ∀ df, env.defeqs df → ∀ ls, df.lhs.stripLams.getAppFnArgs.1 ≠ .const c ls
  pats : ∀ p r, env.pats p r → p.headConst ≠ c

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False
  pats _ _ := False
  projections _ _ := False

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.addConst (env : VEnv) (name : Name) (ci : VConstant) : Option VEnv :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

def VEnv.addDefEq (env : VEnv) (df : VDefEq) : VEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

/-- Register a schematic pattern-reduction rule `r` for pattern `p`; used to
install ι-reduction rules in `VEnv.addInduct`. The dependent equality
`∃ h : p' = p, h ▸ r' = r` accounts for `r'` and `r` living in different
`RHS × Check` types. -/
def VEnv.addPat (env : VEnv) (p : Pattern) (r : p.RHS × p.Check) : VEnv :=
  { env with pats := fun p' r' => (∃ h : p' = p, h ▸ r' = r) ∨ env.pats p' r' }

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

@[simp] theorem VEnv.addProjection_pats (env : VEnv) (entry : VProjectionEntry) :
    (env.addProjection entry).pats = env.pats := rfl

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

@[simp] theorem VEnv.addProjections_pats (env : VEnv)
    (entries : List VProjectionEntry) :
    (env.addProjections entries).pats = env.pats := by
  induction entries generalizing env with
  | nil => rfl
  | cons entry entries ih => exact ih (env := env.addProjection entry)

@[simp] theorem VEnv.addProjections_nil {env : VEnv} : env.addProjections [] = env := rfl

@[simp] theorem VEnv.addDefEq_projections (env : VEnv) (df : VDefEq) :
    (env.addDefEq df).projections = env.projections := rfl

@[simp] theorem VEnv.addDefEq_pats (env : VEnv) (df : VDefEq) :
    (env.addDefEq df).pats = env.pats := rfl

@[simp] theorem VEnv.addPat_projections (env : VEnv) (p : Pattern) (r : p.RHS × p.Check) :
    (env.addPat p r).projections = env.projections := rfl

@[simp] theorem VEnv.addPat_defeqs (env : VEnv) (p : Pattern) (r : p.RHS × p.Check) :
    (env.addPat p r).defeqs = env.defeqs := rfl

@[simp] theorem VEnv.addPat_constants (env : VEnv) (p : Pattern) (r : p.RHS × p.Check) :
    (env.addPat p r).constants = env.constants := rfl

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df
  pats : env1.pats p r → env2.pats p r
  projections : env1.projections n p → env2.projections n p

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id, id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2, h2.3 ∘ h1.3, h2.4 ∘ h1.4⟩

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

theorem VEnv.addConst_pats {env env' : VEnv}
    (h : env.addConst n ci = some env') :
    env'.pats = env.pats := by
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

theorem VEnv.addPat_le {env : VEnv} {p r} : env ≤ env.addPat p r := ⟨id, id, .inr, id⟩

theorem VEnv.addPat_self {env : VEnv} {p r} : (env.addPat p r).pats p r := .inl ⟨rfl, rfl⟩

theorem VEnv.addProjection_le {env : VEnv} {entry : VProjectionEntry} :
    env ≤ env.addProjection entry where
  constants := id
  defeqs := id
  pats := id
  projections hinfo := Or.inr hinfo

theorem VEnv.addProjections_le {env : VEnv} {entries : List VProjectionEntry} :
    env ≤ env.addProjections entries := by
  induction entries generalizing env with
  | nil => exact .rfl
  | cons entry entries ih => exact addProjection_le.trans ih

theorem VEnv.addProjection_mono {env₁ env₂ : VEnv} {entry : VProjectionEntry}
    (H : env₁ ≤ env₂) :
    env₁.addProjection entry ≤ env₂.addProjection entry where
  constants := H.constants
  defeqs := H.defeqs
  pats := H.pats
  projections := fun hinfo => hinfo.elim Or.inl (Or.inr ∘ H.projections)

theorem VEnv.addProjections_mono {env₁ env₂ : VEnv}
    {entries : List VProjectionEntry} (H : env₁ ≤ env₂) :
    env₁.addProjections entries ≤ env₂.addProjections entries := by
  induction entries generalizing env₁ env₂ with
  | nil => exact H
  | cons entry entries ih => exact ih (addProjection_mono H)

end Lean4Lean
