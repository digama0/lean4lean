import Std.Data.List.Perm
import Std.Tactic.SeqFocus

namespace List
def NodupKeys (l : List (α × β)) : Prop := Nodup (l.map (·.1))

theorem nodupKeys_iff_pairwise {l : List (α × β)} :
    NodupKeys l ↔ Pairwise (fun a b => a.1 ≠ b.1) l := pairwise_map

@[simp] theorem nodupKeys_cons : NodupKeys (a::l) ↔ (∀ a' ∈ l, a.1 ≠ a'.1) ∧ NodupKeys l := by
  simp [nodupKeys_iff_pairwise]

theorem Perm.nodupKeys_iff {l₁ l₂ : List (α × β)} (h : l₁ ~ l₂) :
    NodupKeys l₁ ↔ NodupKeys l₂ := (h.map _).nodup_iff

theorem Perm.lookup_eq [BEq α] [LawfulBEq α]
    {l₁ l₂ : List (α × β)} (h : l₁ ~ l₂) (nd : l₁.NodupKeys) : l₁.lookup a = l₂.lookup a := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [lookup]; split <;> [rfl; exact ih (pairwise_cons.1 nd).2]
  | swap _ h ih =>
    simp at nd
    simp [lookup]; split <;> split <;> rename_i h1 _ h2 <;> try rfl
    simp at h1 h2; cases nd.1.1 (by rw [← h1, h2])
  | trans h1 _ ih1 ih2 => exact (ih1 nd).trans (ih2 (h1.nodupKeys_iff.1 nd))

theorem NodupKeys.lookup_eq_some [BEq α] [LawfulBEq α]
    {l : List (α × β)} (nd : l.NodupKeys) : l.lookup a = some b ↔ (a, b) ∈ l := by
  induction l with
  | nil => simp
  | cons p l ih =>
    let (a', b') := p
    simp [lookup] at nd ⊢; split <;> rename_i h
    · simp at h; subst a'; simp [eq_comm]
      refine (or_iff_left_of_imp fun h => ?_).symm
      cases nd.1 _ h rfl
    · simp at h; simp [h, ih nd.2]
