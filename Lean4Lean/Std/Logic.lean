import Std.Data.Nat.Lemmas

theorem funext_iff {β : α → Sort u} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

protected theorem Nat.lt_add_left (a b c : Nat) (h : a < c) : a < b + c :=
  Nat.add_comm .. ▸ Nat.lt_add_right _ _ _ h
