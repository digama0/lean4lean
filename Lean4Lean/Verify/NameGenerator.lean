import Lean4Lean.Expr
import Lean4Lean.Theory.VExpr

namespace Lean.NameGenerator

def Reserves (ngen : NameGenerator) (fvars : List FVarId) : Prop :=
  ∀ fv ∈ fvars, ∀ i, fv = ⟨.num ngen.namePrefix i⟩ → i < ngen.idx

protected inductive LE : NameGenerator → NameGenerator → Prop where
  | le : i ≤ j → NameGenerator.LE ⟨pfx, i⟩ ⟨pfx, j⟩

instance : LE NameGenerator := ⟨NameGenerator.LE⟩

theorem LE.rfl {ngen : NameGenerator} : ngen ≤ ngen := ⟨Nat.le_refl _⟩

theorem LE.trans {ngen₁ ngen₃ ngen₃ : NameGenerator} : ngen₁ ≤ ngen₂ → ngen₂ ≤ ngen₃ → ngen₁ ≤ ngen₃
  | ⟨h₁⟩, ⟨h₂⟩ => ⟨Nat.le_trans h₁ h₂⟩

theorem Reserves.mono : ngen ≤ ngen' → fvars' ⊆ fvars → Reserves ngen fvars → Reserves ngen' fvars'
  | ⟨h₁⟩, h₂ => fun H _ hfv _ hi => Nat.lt_of_lt_of_le (H _ (h₂ hfv) _ hi) h₁
