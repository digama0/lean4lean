import Lean.Data.SMap
import Std.Data.HashMap.Lemmas
import Lean4Lean.Std.HashMap
import Lean4Lean.Std.PersistentHashMap

namespace Lean.SMap

variable [BEq α] [Hashable α]
structure WF (s : SMap α β) where
  map₂ : s.map₂.WF
  stage : s.stage₁ → s.map₂ = .empty
  disjoint : s.map₂.contains a → ¬a ∈ s.map₁

theorem WF.empty : WF ({} : SMap α β) := ⟨.empty, fun _ => rfl, by simp⟩

protected nonrec theorem WF.insert [LawfulBEq α] [LawfulHashable α] {s : SMap α β}
    (h : s.WF) (k : α) (v : β) (hn : s.find? k = none) : (s.insert k v).WF := by
  unfold insert; split
  · refine ⟨h.map₂, h.stage, fun _ h' => ?_⟩
    have := h.stage
    simp_all [find?, PersistentHashMap.find?_isSome, PersistentHashMap.WF.empty.find?_eq]
  · refine ⟨h.map₂.insert .., nofun, fun h1 => ?_⟩
    simp_all [PersistentHashMap.find?_isSome, h.map₂.find?_insert]
    revert ‹_›; split
    · simp_all [find?]
    · exact h.disjoint ∘ by simp [PersistentHashMap.find?_isSome]

variable [LawfulBEq α] [LawfulHashable α] in
theorem WF.find?_insert {s : SMap α β} (h : s.WF) :
    (s.insert k v).find? x = if k == x then some v else s.find? x := by
  unfold insert; split <;> simp [find?]
  · exact Std.HashMap.getElem?_insert (α := α)
  · rw [h.map₂.find?_insert]; split <;> rfl

noncomputable def toList' [BEq α] [Hashable α] (m : SMap α β) :
    List (α × β) := m.map₂.toList' ++ m.map₁.toList

open scoped _root_.List in
theorem WF.toList'_insert {α β} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) (b : β)
    (h : m.find? a = none) :
    (m.insert a b).toList' ~ (a, b) :: m.toList' := by
  unfold insert; split <;> simp [toList']
  · have : EquivBEq α := inferInstance; clear ‹LawfulBEq _›
    have := wf.stage rfl; simp [find?] at this h; subst this; simp
    refine (List.filter_eq_self.2 ?_ ▸ Std.HashMap.insert_toList (α := α) .. :)
    rintro ⟨a', b⟩ h
    refine Decidable.by_contra fun h2 => ?_
    simp at h2
    have := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.2 ⟨_, h2, h⟩
    exact ‹¬_› (Std.HashMap.mem_of_getElem? this)
  · refine .append_right (l₂ := _::_) _ ?_
    refine (List.filter_eq_self.2 ?_ ▸ wf.map₂.toList'_insert .. :)
    rintro ⟨a', b⟩ h'
    have := wf.map₂.find?_eq a
    simp_all [find?]; rintro rfl
    exact h.1 _ _ h' rfl

theorem WF.find?_eq {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.find? a = m.toList'.lookup a := by
  simp [find?]; split
  · cases wf.stage rfl
    simp [toList']
    exact Std.HashMap.getElem?_eq_lookup_toList ..
  · simp [toList', List.lookup_append, wf.map₂.find?_eq]
    cases List.lookup a .. <;> simp [Std.HashMap.getElem?_eq_lookup_toList]

theorem WF.find?'_eq_find? {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.find?' a = m.find? a := by
  simp [find?, find?']; split; · rfl
  rename_i m₁ m₂
  cases e1 : m₁[a]? <;> cases e2 : m₂.find? a <;> simp
  cases wf.disjoint (by simp [PersistentHashMap.find?_isSome, e2]) (Std.HashMap.mem_of_getElem? e1)

theorem find?_isSome {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : SMap α β) (a : α) : m.contains a = (m.find? a).isSome := by
  simp [find?, contains]; split <;> simp [← PersistentHashMap.find?_isSome, Bool.or_comm]
