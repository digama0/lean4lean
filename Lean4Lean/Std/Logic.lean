import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas

theorem funext_iff {β : α → Sort u} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

protected theorem Nat.lt_add_left (a b c : Nat) (h : a < c) : a < b + c :=
  Nat.add_comm .. ▸ Nat.lt_add_right _ _ _ h

protected theorem List.Forall₂.rfl
    {R : α → α → Prop} {l : List α} (h : ∀ a ∈ l, R a a) : l.Forall₂ R l := by
  induction l with
  | nil => constructor
  | cons _ _ ih => simp at h; exact .cons h.1 (ih h.2)
