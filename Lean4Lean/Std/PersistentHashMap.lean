import Lean.Data.SMap
import Std.Data.HashMap.Lemmas
import Lean4Lean.Verify.Axioms

namespace Lean.PersistentHashMap

@[simp] theorem toList'_empty [BEq α] [Hashable α] :
    (.empty : PersistentHashMap α β).toList' = [] := by
  have this n : @Node.toList' α β (.entries ⟨.replicate n .null⟩) = [] := by
    simp [Node.toList']
    induction n <;> simp [*, List.replicate_succ]
  apply this

@[simp] theorem toList'_empty' [BEq α] [Hashable α] :
    ({} : PersistentHashMap α β).toList' = [] := toList'_empty

theorem find?_isSome {α β} [BEq α] [Hashable α]
    (m : PersistentHashMap α β) (a : α) : m.contains a = (m.find? a).isSome := findAux_isSome ..

theorem WF.nodupKeys [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α]
    {m : PersistentHashMap α β} (h : WF m) : m.toList'.NodupKeys := by
  induction h with
  | empty => simp; exact .nil
  | insert h1 ih =>
    refine (h1.toList'_insert ..).nodupKeys_iff.2 (List.nodupKeys_cons.2 ⟨?_, ih.filter _⟩)
    rintro _ h3 rfl
    simpa using (List.mem_filter.1 h3).2

variable [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] in
theorem WF.find?_insert {s : PersistentHashMap α β} (h : s.WF) :
    (s.insert k v).find? x = if k == x then some v else s.find? x := by
  rw [h.insert.find?_eq, h.find?_eq, BEq.comm,
    (h.toList'_insert ..).lookup_eq h.insert.nodupKeys, List.lookup]
  cases eq : x == k <;> simp
  induction s.toList' with
  | nil => rfl
  | cons kv l ih =>
    simp [List.filter]; split <;> simp [List.lookup, *]
    split <;> [skip; rfl]
    rename_i h1 _ h2
    simp at h1 h2; simp [h1, h2] at eq
