import Std.Data.HashMap.Lemmas
import Lean

namespace Std.Internal.List

namespace Const

def containsKey [BEq α] (a : α) : List (α × β) → Bool
  | [] => false
  | ⟨k, _⟩ :: l => k == a || containsKey a l

def replaceEntry [BEq α] (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => []
  | ⟨k', v'⟩ :: l => bif k' == k then ⟨k, v⟩ :: l else ⟨k', v'⟩ :: replaceEntry k v l

def insertEntry [BEq α] (k : α) (v : β) (l : List (α × β)) : List (α × β) :=
  bif containsKey k l then replaceEntry k v l else (k, v) :: l

theorem insertEntry_perm_filter [BEq α] [PartialEquivBEq α]
    (k : α) (v : β) {l : List (α × β)} (hl : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (insertEntry k v l).Perm <| (k, v) :: l.filter (¬k == ·.1) := by
  unfold insertEntry
  cases eq : containsKey k l <;> simp
  · rw [List.filter_eq_self.2]
    induction l <;> simp_all [containsKey, BEq.comm]; assumption
  · induction l <;> simp_all [-List.pairwise_cons, containsKey, replaceEntry, List.filter, BEq.comm]
    revert eq; cases h : k == _ <;> intro eq <;> simp_all
    rename_i ih
    · exact .trans (.cons _ ih) (.swap ..)
    · rw [List.filter_eq_self.2]
      intro ⟨a, b⟩ h'
      have := hl.1 a b h'
      refine Decidable.by_contra fun h2 => ?_
      simp at h2
      cases h2.symm.trans (BEq.congr_left h ▸ this)

end Const

theorem containsKey_map [BEq α] (l : List ((_ : α) × β)) :
    Const.containsKey k (l.map (fun x => (x.1, x.2))) = containsKey k l := by
  induction l <;> simp [containsKey, Const.containsKey, *]

theorem replaceEntry_map [BEq α] (l : List ((_ : α) × β)) :
    Const.replaceEntry k v (l.map (fun x => (x.1, x.2))) =
    (replaceEntry k v l).map (fun x => (x.1, x.2)) := by
  induction l <;> simp [replaceEntry, Const.replaceEntry, *]
  cases _ == k <;> simp

theorem insertEntry_map [BEq α] (l : List ((_ : α) × β)) :
    Const.insertEntry k v (l.map (fun x => (x.1, x.2))) =
    (insertEntry k v l).map (fun x => (x.1, x.2)) := by
  simp [insertEntry, Const.insertEntry, containsKey_map, replaceEntry_map]
  cases containsKey k l <;> simp

end Std.Internal.List

namespace Std.DHashMap
open Std.Internal.List Internal.Raw Internal.Raw₀

variable [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

theorem insert_perm_insertEntry (m : DHashMap α β) (a b) :
    (insert m a b).toList.Perm (insertEntry a b m.toList) := by
  simp [toList, toList_eq_toListModel]
  exact toListModel_insert (WF.out m.2)

theorem Const.insert_perm_insertEntry (m : DHashMap α fun _ => β) (a b) :
    (Const.toList (insert m a b)).Perm (Const.insertEntry a b (Const.toList m)) := by
  simp [Const.toList, Const.toList_eq_toListModel_map, insertEntry_map]
  exact (toListModel_insert (WF.out m.2)).map _

end Std.DHashMap

namespace Std.HashMap
open Internal.List

variable [BEq α] [Hashable α] [LawfulHashable α]

theorem insert_toList [EquivBEq α] (m : HashMap α β) :
    (insert m a b).toList.Perm ((a, b) :: m.toList.filter (¬a == ·.1)) := by
  refine (DHashMap.Const.insert_perm_insertEntry m.1 a b).trans ?_
  exact Const.insertEntry_perm_filter _ _ distinct_keys_toList

theorem getElem?_eq_lookup_toList [LawfulBEq α] (m : HashMap α β) (a : α) :
    m[a]? = m.toList.lookup a := by
  apply Option.ext fun b => ?_
  simp; rw [← mem_toList_iff_getElem?_eq_some]
  have := distinct_keys_toList (m := m); revert this
  induction m.toList <;> intro H <;> simp_all [List.lookup]
  split <;> simp_all [Prod.ext_iff]
  simp [eq_comm]
  rw [List.lookup_eq_none_iff.2]; · simp
  simp; exact H.1

theorem mem_of_getElem? [EquivBEq α] {m : HashMap α β} (h : m[a]? = some b) : a ∈ m := by
  refine Decidable.by_contra fun h' => ?_
  cases (getElem?_eq_none h').symm.trans h

end Std.HashMap
