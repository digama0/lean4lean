import Batteries.CodeAction
import Batteries.Data.Array.Lemmas
import Batteries.Data.HashMap.Basic

attribute [simp] Option.bind_eq_some List.filterMap_cons

theorem funext_iff {β : α → Sort u} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

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
    Nat.add_le_add_iff_left, Nat.le_zero, length_eq_zero] at h
  subst h; exact ⟨[], by simp⟩

instance [BEq α] [LawfulBEq α] : PartialEquivBEq α where
  symm h := by simp at *; exact h.symm
  trans h1 h2 := by simp at *; exact h1.trans h2

instance [BEq α] [LawfulBEq α] [Hashable α] : Batteries.HashMap.LawfulHashable α where
  hash_eq h := by simp at *; subst h; rfl

instance : LawfulBEq Lean.FVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Lean.Name) h; rfl
  rfl := LawfulBEq.rfl (α := Lean.Name)

theorem beq_comm [BEq α] [PartialEquivBEq α] (a b : α) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 ⟨PartialEquivBEq.symm, PartialEquivBEq.symm⟩

theorem List.mapM_eq_some {f : α → Option β} {l : List α} {l' : List β} :
    l.mapM f = some l' ↔ List.Forall₂ (f · = some ·) l l' := by
  induction l generalizing l' <;>
    simp [List.mapM_nil, List.mapM_cons, bind, List.forall₂_cons_left_iff, *, pure, @eq_comm _ l']

@[simp] theorem Option.bind_eq_none'' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by cases o <;> simp

@[simp] theorem Option.forall_ne_some {o : Option α} : (∀ a, o ≠ some a) ↔ o = none := by
  cases o <;> simp
