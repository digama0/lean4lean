import Lean4Lean.Theory.VExpr

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
  constants : Name → Option (Option VConstant)
  defeqs : VDefEq → Prop

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.addConst (env : VEnv) (name : Name) (ci : Option VConstant) : Option VEnv :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

def VEnv.addDefEq (env : VEnv) (df : VDefEq) : VEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2⟩
