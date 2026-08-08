import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.Pattern

namespace Lean4Lean

structure VConstant where
  uvars : Nat
  type : VExpr

structure VDefEq where
  uvars : Nat
  lhs : VExpr
  rhs : VExpr
  type : VExpr

@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
  /-- Schematic reduction rules, keyed by a `Pattern` (the redex shape) and its
  reduct/side-condition pair; the registry for ι-reduction rules. -/
  pats : (p : Pattern) → p.RHS × p.Check → Prop

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False
  pats _ _ := False

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.contains (env : VEnv) (name : Name) := ∃ ci, env.constants name = some ci

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

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df
  pats : env1.pats p r → env2.pats p r

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2, h2.3 ∘ h1.3⟩
