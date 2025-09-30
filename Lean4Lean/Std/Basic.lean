import Batteries.CodeAction
import Batteries.Data.Array.Lemmas
import Batteries.Data.HashMap.Basic
import Batteries.Data.UnionFind.Basic
import Batteries.Tactic.SeqFocus

open Std

attribute [simp] Option.bind_eq_some List.filterMap_cons

protected theorem Nat.le_iff_exists_add {a b : Nat} : a ≤ b ↔ ∃ c, b = a + c :=
  ⟨fun h => ⟨_, (Nat.add_sub_cancel' h).symm⟩, fun ⟨_, h⟩ => h ▸ Nat.le_add_right ..⟩

protected theorem Nat.le_iff_exists_add' {a b : Nat} : a ≤ b ↔ ∃ c, b = c + a := by
  simp [Nat.add_comm, Nat.le_iff_exists_add]

protected theorem List.Forall₂.rfl
    {R : α → α → Prop} {l : List α} (h : ∀ a ∈ l, R a a) : l.Forall₂ R l := by
  induction l with
  | nil => constructor
  | cons _ _ ih => simp at h; exact .cons h.1 (ih h.2)

@[simp] theorem List.forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp] theorem List.forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

theorem List.forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h => match u, h with | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    (fun h => match u, h with | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂)

theorem List.forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h => match u, h with | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    (fun h => match u, h with | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂)

theorem List.Forall₂.imp (H : ∀ a b, R a b → S a b)
    {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> [(apply H; assumption); assumption]

theorem List.Forall₂.trans (H : ∀ a b c, R a b → S b c → T a c)
    {l₁ l₂ l₃} (h₁ : Forall₂ R l₁ l₂) (h₂ : Forall₂ S l₂ l₃) : Forall₂ T l₁ l₃ := by
  induction h₁ generalizing l₃ <;> cases h₂ <;> constructor <;> solve_by_elim

theorem List.Forall₂.and {l₁ l₂} (h₁ : Forall₂ R l₁ l₂) (h₂ : Forall₂ S l₁ l₂) :
    Forall₂ (fun x y => R x y ∧ S x y) l₁ l₂ := by induction h₁ <;> simp_all

@[simp] theorem List.forall₂_map_left_iff {f : γ → α} :
    ∀ {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp] theorem List.forall₂_map_right_iff {f : γ → β} :
    ∀ {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]

theorem List.Forall₂.flip : ∀ {a b}, Forall₂ (flip R) b a → Forall₂ R a b
  | _, _, Forall₂.nil => Forall₂.nil
  | _ :: _, _ :: _, Forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip

theorem List.Forall₂.forall_exists_l {l₁ l₂} (h : Forall₂ R l₁ l₂) : ∀ a ∈ l₁, ∃ b ∈ l₂, R a b := by
  induction h with simp [*] | cons _ _ ih => exact fun a h => .inr (ih _ h)

theorem List.Forall₂.forall_exists_r {l₁ l₂} (h : Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, R a b :=
  h.flip.forall_exists_l

theorem List.Forall₂.length_eq : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂
  | _, _, Forall₂.nil => rfl
  | _, _, Forall₂.cons _ h₂ => congrArg Nat.succ (Forall₂.length_eq h₂)

theorem List.Forall₂.append_of_left : ∀ {l₁ l₂ r₁ r₂}, length l₁ = length l₂ →
    (Forall₂ R (l₁ ++ r₁) (l₂ ++ r₂) ↔ Forall₂ R l₁ l₂ ∧ Forall₂ R r₁ r₂)
  | [], [], _, _, _ => by simp
  | a::l₁, b::l₂, _, _, eq => by simp [append_of_left (Nat.succ_inj.1 eq), and_assoc]

theorem List.Forall₂.append_of_right {l₁ l₂ r₁ r₂} (H : length r₁ = length r₂) :
    Forall₂ R (l₁ ++ r₁) (l₂ ++ r₂) ↔ Forall₂ R l₁ l₂ ∧ Forall₂ R r₁ r₂ := by
  refine ⟨fun h => (append_of_left ?_).1 h, fun h => (append_of_left h.1.length_eq).2 h⟩
  simpa [H] using h.length_eq

theorem List.map_id''' {f : α → α} (l : List α) (h : ∀ x ∈ l, f x = x) : map f l = l := by
  induction l <;> simp_all

theorem List.map_fst_lookup {f : α → β} [BEq β] (l : List α) (b : β) :
    (l.map (fun a => (f a, a))).lookup b = l.find? fun a => b == f a := by
  induction l <;> simp_all [lookup, find?]

def List.All (P : α → Prop) : List α → Prop
  | [] => True
  | a::as => P a ∧ as.All P

theorem List.All.imp {P Q : α → Prop} (h : ∀ a, P a → Q a) : ∀ {l : List α}, l.All P → l.All Q
  | [] => id
  | _::_ => And.imp (h _) (List.All.imp h)

theorem List.append_eq_append_of_length_le {a b c d : List α} (h : length a ≤ length c) :
  a ++ b = c ++ d ↔ ∃ a', c = a ++ a' ∧ b = a' ++ d := by
  rw [append_eq_append_iff, or_iff_left_iff_imp]
  rintro ⟨c', rfl, rfl⟩
  rw [← Nat.add_zero c.length, length_append,
    Nat.add_le_add_iff_left, Nat.le_zero, length_eq_zero_iff] at h
  subst h; exact ⟨[], by simp⟩

@[simp] theorem List.nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
  pairwise_reverse.trans <| by simp only [Nodup, Ne, eq_comm]

theorem List.foldl_congr
    (H : ∀ a, ∀ x ∈ l, f a x = g a x) : foldl f a l = foldl g a l := by
  induction l generalizing a <;> simp_all

theorem List.idxOf_eq_length_iff [BEq α] [LawfulBEq α]
    {a : α} {l : List α} : idxOf a l = length l ↔ a ∉ l := by
  induction l with
  | nil => exact iff_of_true rfl not_mem_nil
  | cons b l ih =>
    simp only [length, mem_cons, idxOf_cons]
    rw [cond_eq_if]
    split <;> rename_i h <;> simp at h
    · exact iff_of_false (by rintro ⟨⟩) fun H => H <| Or.inl h.symm
    · simp only [Ne.symm h, false_or]
      rw [← ih]
      exact Nat.succ_inj

instance [BEq α] [LawfulBEq α] : PartialEquivBEq α where
  symm h := by simp at *; exact h.symm
  trans h1 h2 := by simp at *; exact h1.trans h2

theorem beq_comm [BEq α] [PartialEquivBEq α] (a b : α) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 ⟨PartialEquivBEq.symm, PartialEquivBEq.symm⟩

theorem List.mapM_eq_some {f : α → Option β} {l : List α} {l' : List β} :
    l.mapM f = some l' ↔ List.Forall₂ (f · = some ·) l l' := by
  induction l generalizing l' with
  | nil => simp only [mapM_nil, pure, Option.some.injEq, forall₂_nil_left_iff, @eq_comm _ l']
  | cons x l ih =>
    simp [mapM_cons, Bind.bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      forall₂_cons_left_iff, @eq_comm _ l', exists_and_left, ih]

@[simp] theorem Option.bind_eq_none'' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by cases o <;> simp

@[simp] theorem Option.forall_ne_some {o : Option α} : (∀ a, o ≠ some a) ↔ o = none := by
  cases o <;> simp

@[simp] theorem Option.orElse_eq_none {a : Option α} {b : Unit → Option α} :
    a.orElse b = none ↔ a = none ∧ b () = none := by
  cases a <;> simp [Option.orElse]

instance [BEq α] [PartialEquivBEq α] [BEq β] [PartialEquivBEq β] : PartialEquivBEq (α × β) where
  symm := by simp [(· == ·)]; grind [BEq.symm]
  trans := by simp [(· == ·)]; grind [BEq.trans]

instance [BEq α] [EquivBEq α] [BEq β] [EquivBEq β] : EquivBEq (α × β) where
  rfl := by simp [(· == ·)]

instance [BEq α] [PartialEquivBEq α] : PartialEquivBEq (List α) where
  symm := by
    simp [(· == ·)]; intro a b
    induction a generalizing b <;> cases b <;> simp [List.beq]; grind [BEq.symm]
  trans := by
    simp [(· == ·)]; intro a b c
    induction a generalizing b c <;> cases b <;> simp [List.beq]
    cases c <;> simp [List.beq]; grind [BEq.trans]

instance [BEq α] [EquivBEq α] : EquivBEq (List α) where
  rfl {a} := by simp [(· == ·)]; induction a <;> simp [List.beq, *]

namespace BitVec

variable (n : Nat)

instance : TransOrd (BitVec n) :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    BitVec.le_antisymm BitVec.le_trans BitVec.le_total BitVec.not_le

instance : LawfulEqOrd (BitVec n) where
  eq_of_compare := compareOfLessAndEq_eq_eq BitVec.le_refl BitVec.not_le |>.mp

end BitVec

namespace UInt64

variable (n : Nat)

instance : TransOrd UInt64 :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    UInt64.le_antisymm UInt64.le_trans UInt64.le_total UInt64.not_le

instance : LawfulEqOrd UInt64 where
  eq_of_compare := compareOfLessAndEq_eq_eq UInt64.le_refl UInt64.not_le |>.mp

end UInt64

namespace Batteries.UnionFind

@[simp] theorem size_push (uf : UnionFind) : uf.push.size = uf.size + 1 := by
  simp [push, size]

@[simp] theorem size_link (uf : UnionFind) (i j hi) : (uf.link i j hi).size = uf.size := by
  simp [link, size]

@[simp] theorem size_union (uf : UnionFind) (i j) : (uf.union i j).size = uf.size := by
  simp [union, size]

theorem Equiv.eq_of_ge_size (h : Equiv uf a b) (h2 : uf.size ≤ a) : a = b := by
  simp [Equiv, rootD, Nat.not_lt.2 h2] at h; split at h
  · have := (uf.root ⟨b, ‹_›⟩).2; omega
  · exact h

theorem Equiv.lt_size (h : Equiv uf a b) : a < uf.size ↔ b < uf.size :=
  suffices ∀ {a b}, Equiv uf a b → b < uf.size → a < uf.size from ⟨this h.symm, this h⟩
  fun h h1 => Nat.not_le.1 fun h2 => Nat.not_le.2 h1 <| h.eq_of_ge_size h2 ▸ h2


end Batteries.UnionFind
