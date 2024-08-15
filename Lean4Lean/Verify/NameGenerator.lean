import Lean4Lean.Expr
import Lean4Lean.Theory.VExpr

namespace Lean.NameGenerator

def Reserves (ngen : NameGenerator) (fv : FVarId) : Prop :=
  ∀ i, fv = ⟨.num ngen.namePrefix i⟩ → i < ngen.idx

protected inductive LE : NameGenerator → NameGenerator → Prop where
  | le : i ≤ j → NameGenerator.LE ⟨pfx, i⟩ ⟨pfx, j⟩

instance : LE NameGenerator := ⟨NameGenerator.LE⟩

theorem LE.rfl {ngen : NameGenerator} : ngen ≤ ngen := ⟨Nat.le_refl _⟩

theorem LE.trans {ngen₁ ngen₂ ngen₃ : NameGenerator} : ngen₁ ≤ ngen₂ → ngen₂ ≤ ngen₃ → ngen₁ ≤ ngen₃
  | ⟨h₁⟩, ⟨h₂⟩ => ⟨Nat.le_trans h₁ h₂⟩

theorem Reserves.mono : ngen ≤ ngen' → Reserves ngen fv → Reserves ngen' fv
  | ⟨h₁⟩ => fun H _ hi => Nat.lt_of_lt_of_le (H _ hi) h₁

theorem LE.next {ngen : NameGenerator} : ngen ≤ ngen.next := ⟨Nat.le_succ _⟩
