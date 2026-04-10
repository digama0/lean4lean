import Lean4Lean.Experimental.SExpr
import Batteries.WF

namespace Lean4Lean

namespace SExpr
variable [Params]

private instance : DecidableEq SLevel := sorry

@[simp] theorem SLevel.succ_ne_zero {l : SLevel} : l.succ ≠ .zero := sorry
@[simp] theorem SLevel.imax_eq_zero {l l' : SLevel} : l.imax l' = .zero ↔ l' = .zero := sorry

inductive Shape0 : Type where
  | bot : Shape0
  | sort (rel : Bool) : Shape0

inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (rel : Bool) : ShapeS Shape
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape

def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort (rel : Bool) : ∀ {n}, Shape n
  | 0 => Shape0.sort rel
  | _+1 => ShapeS.sort rel

abbrev Shape.prop : ∀ {n}, Shape n := .sort false
abbrev Shape.type : ∀ {n}, Shape n := .sort true

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | 0, _, .bot | _+1, .bot, _ | _+1, _, .bot => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _, _, _ => false

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.ble s' && ShapeFun.ble ble f f'
  | _+1, .lam f, .lam f' => ShapeFun.ble ble f f'
  | _, _, _ => false

def ShapeFun.LE (s s' : ShapeFun n) : Prop := ShapeFun.ble Shape.ble s s'
def Shape.LE (s s' : Shape n) : Prop := s.ble s'
instance : LE (Shape n) := ⟨Shape.LE⟩
instance : DecidableRel (α := Shape n) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x.ble y))

omit [Params] in
@[simp] theorem Shape.bot_le : Shape.bot ≤ (s : Shape n) := by cases n <;> rfl

def ShapeFun.bot : ShapeFun n := [(.bot, .bot)]

omit [Params] in
theorem ShapeFun.LE.def {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x y:Shape n, (x, y) ∈ f → ∃ x' y':Shape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [LE, ble]; rfl

omit [Params] in
theorem Shape.LE.def {s s' : Shape (n + 1)} : s ≤ s' ↔
    match s, s' with
    | .bot, _ => True
    | .sort r, .sort r' => r = r' --j ≤ i
    | .forallE s f, .forallE s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
    | _, _ => False := by
  dsimp only [(· ≤ ·), Shape.LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp

omit [Params] in
theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> simp [ble]
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]

omit [Params] in
theorem Shape.LE.of_eq {s : Shape n} : s = t → s ≤ t := by rintro ⟨⟩; exact .rfl

omit [Params] in
theorem ShapeFun.LE.rfl {s : ShapeFun n} : s.LE s := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact fun _ h => ⟨_, h, Shape.LE.rfl, Shape.LE.rfl⟩

omit [Params] in
theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

omit [Params] in
theorem Shape.le_sort {s : Shape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r := by
  cases n <;> simp [sort, bot, (· ≤ ·), Shape.LE] <;> cases s <;>
    simp [ble] <;> exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

theorem ShapeFun.bot_le {f : ShapeFun n} : ShapeFun.bot.LE f := by
  simp [ShapeFun.LE.def, bot]
  exact ⟨.bot, sorry, Shape.bot_le⟩

omit [Params] in
theorem Shape.sort_le {s : Shape n} : .sort r ≤ s ↔ .sort r = s := by
  cases n <;> simp [sort, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble, Shape]

omit [Params] in
theorem Shape.LE.trans {s t u : Shape n} : s ≤ t → t ≤ u → s ≤ u := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;>
      (intro h1 h2; exact h1.trans h2)
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;> grind

omit [Params] in
theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s.LE t → t.LE u → s.LE u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n m}, Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift s) <| ShapeFun.lift lift f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift lift f

omit [Params] in
@[simp] theorem Shape.lift_bot : ((.bot : Shape n).lift : Shape m) = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in
@[simp] theorem Shape.lift_sort : ((.sort r : Shape n).lift : Shape m) = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in theorem Shape.lift_prop : ((.prop : Shape n).lift : Shape m) = .prop := lift_sort
omit [Params] in theorem Shape.lift_type : ((.type : Shape n).lift : Shape m) = .type := lift_sort

omit [Params] in
theorem Shape.lift_self {s : Shape n} : s.lift = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s <;> [rfl; grind]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]

omit [Params] in
theorem ShapeFun.lift_self {s : ShapeFun n} : lift Shape.lift s = s := by
  simp [ShapeFun.lift]; apply List.map_id''; simp [Shape.lift_self]

omit [Params] in
theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    ((s.lift : Shape n₂).lift : Shape n₃) = s.lift := by
  induction n₁ generalizing n₂ n₃ with
  | zero => cases s <;> simp [lift]
  | succ n₁ ih =>
    cases n₃ with
    | zero =>
      cases n₂ with | zero => rw [lift_self] | succ n₃
      cases s <;> simp [lift]
    | succ n₃ =>
      let n₂ + 1 := n₂; simp at le; replace ih {s} := ih (s := s) le
      have ihf {s : ShapeFun n₁} :
          (ShapeFun.lift lift (ShapeFun.lift lift s : ShapeFun n₂) : ShapeFun n₃) =
          ShapeFun.lift lift s := by simp [ShapeFun.lift, ih]
      cases s <;> simp [lift, ih, ihf]

omit [Params] in
theorem ShapeFun.lift_lift {s : ShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (lift Shape.lift (lift Shape.lift s : ShapeFun n₂) : ShapeFun n₃) =
    lift Shape.lift s := by simp [ShapeFun.lift, Shape.lift_lift le]

omit [Params] in
theorem Shape.lift_le_lift {s t : Shape n} (le : n ≤ m) : (s.lift : Shape m) ≤ t.lift ↔ s ≤ t := by
  dsimp [(· ≤ ·), Shape.LE]; rw [← Bool.eq_iff_iff]
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases s <;> cases t <;> simp [lift, ble]
  | succ n ih =>
    let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {t' s} := @ih m t' s le
    have ihf {s t} :
        ShapeFun.ble ble (ShapeFun.lift (lift : Shape n → Shape m) s) (ShapeFun.lift lift t) =
        ShapeFun.ble ble s t := by
      simp only [ShapeFun.ble, ShapeFun.lift, List.all_map, List.any_map, Function.comp_def, ih]
    cases s <;> cases t <;> simp [ble, lift, *]

omit [Params] in
theorem Shape.lift_le_bot {s : Shape n} (h : n ≤ m) : s.lift (m := m) ≤ .bot ↔ s = .bot := by
  rw [← le_bot, ← lift_bot, Shape.lift_le_lift h]

omit [Params] in
theorem Shape.lift_eq_bot {s : Shape n} (h : n ≤ m) : s.lift (m := m) = .bot ↔ s = .bot := by
  rw [← le_bot, Shape.lift_le_bot h]

omit [Params] in
theorem Shape.lift_mono {s t : Shape n} : s ≤ t → (s.lift : Shape m) ≤ t.lift := by
  dsimp [(· ≤ ·), Shape.LE]
  cases n with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
  | succ n =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      let rec go {n m} (ih : ∀ {s t : Shape n}, s ≤ t → (s.lift : Shape m) ≤ t.lift)
          {s t} : ShapeFun.ble ble s t → ShapeFun.ble ble
            (ShapeFun.lift (lift : Shape n → Shape m) s) (ShapeFun.lift lift t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      have := @Shape.lift_mono n m; dsimp [(· ≤ ·), Shape.LE] at this
      have := @go n m Shape.lift_mono
      cases s <;> cases t <;> simp [ble, lift, *] <;> grind

omit [Params] in
theorem ShapeFun.lift_mono {s t : ShapeFun n} : s.LE t →
    LE (lift Shape.lift s : ShapeFun m) (lift Shape.lift t) := Shape.lift_mono.go Shape.lift_mono

def ShapeFun.plift (lift : α → β × Option β) (x : List (α × α)) :
    List (β × β) × Option (List (β × β)) :=
  (x.filterMap fun (a, b) => return (← (lift a).2, (lift b).1),
   x.mapM fun (a, b) => return ((lift a).1, ← (lift b).2))

def Shape.plift : ∀ {n m}, Shape n → Shape m × Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => (.sort r, some (.sort r))
  | 0, _, .bot | _+1, _, .bot => (.bot, some .bot)
  | _+1, 0, _ => (.bot, none)
  | _+1, _+1, .forallE s f =>
    let (s₀, s₁) := s.plift
    let (f₀, f₁) := ShapeFun.plift plift f
    (.forallE s₀ f₀, return .forallE (← s₁) (← f₁))
  | _+1, _+1, .lam f =>
    let (f₀, f₁) := ShapeFun.plift plift f
    (.lam f₀, return .lam (← f₁))

omit [Params] in
theorem Shape.plift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.plift (m := m) = (s.lift, some s.lift) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.plift (m := m) = (s.lift, some s.lift))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift s = (ShapeFun.lift (lift (m := m)) s, some (ShapeFun.lift lift s)) := by
    simp only [ShapeFun.plift, ShapeFun.lift, IH le, bind, pure]; congr 1
    · rw [← List.filterMap_eq_map]; rfl
    · rw [List.mapM_eq_some, List.forall₂_map_right_iff]
      exact .rfl fun _ _ => rfl
  unfold plift; split <;> simp [lift] at le ⊢ <;> simp [plift_eq_lift le, go plift_eq_lift le]

omit [Params] in
theorem Shape.plift_lift (le : n ≤ m) {s : Shape n} :
    (s.lift (m := m)).plift = (s, some s) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, (s.lift (m := m)).plift = (s, some s))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift (ShapeFun.lift (lift (m := m)) s) = (s, some s) := by
    simp only [ShapeFun.plift, ShapeFun.lift, List.filterMap_map, List.mapM_map]; congr 1
    · refine .trans ?_ List.filterMap_some; congr 1; funext (a, b); simp [IH le]
    · rw [List.mapM_eq_some]; refine .rfl fun (a, b) _ => by simp [IH le]
  unfold lift; split <;> (try cases m) <;> try simp [plift, sort, bot] at le ⊢
  · cases le; cases s <;> grind
  all_goals · simp [plift_lift le, go plift_lift le]

omit [Params] in
theorem Shape.plift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (t.lift ≤ s ↔ t ≤ (s.plift (m := n)).1) ∧
    (s ≤ t.lift ↔ ∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t) := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n},
        (t.lift ≤ s ↔ t ≤ (s.plift (m := n)).1) ∧
        (s ≤ t.lift ↔ ∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t))
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      (ShapeFun.LE (ShapeFun.lift lift t) s ↔ ShapeFun.LE t (ShapeFun.plift plift s).1) ∧
      (ShapeFun.LE s (ShapeFun.lift lift t) ↔
        ∃ z, (ShapeFun.plift plift s).2 = some z ∧ ShapeFun.LE z t) := by
    simp [ShapeFun.LE, ShapeFun.ble, ShapeFun.lift, ShapeFun.plift, List.mapM_eq_some,
      -List.any_filterMap, -Prod.forall]
    refine ⟨⟨fun H (a, b) h => ?_, fun H (a, b) h => ?_⟩,
      ⟨fun H => ?_, fun ⟨l, hl, hl2⟩ (a, b) h => ?_⟩⟩
    · obtain ⟨a₁, b₁, h1, h2, h3⟩ := H _ h
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h2
      exact ⟨_, _, ⟨_, _, h1, _, hz, rfl, rfl⟩, hz2, (IH le).1.1 h3⟩
    · obtain ⟨_, _, ⟨_, _, h1, _, h2, rfl, rfl⟩, h3, h4⟩ := H _ h
      exact ⟨_, _, h1, (IH le).2.2 ⟨_, h2, h3⟩, (IH le).1.2 h4⟩
    · induction s with | nil => exact ⟨[], .nil, nofun⟩ | cons p s ih
      simp only [List.mem_cons, or_imp, forall_and, forall_eq] at H
      have ⟨⟨a', b', h1, h2, h3⟩, H⟩ := H
      have ⟨l, hl, hl2⟩ := ih H
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h3
      refine ⟨_::l, .cons ⟨_, hz, rfl⟩ hl, ?_⟩
      exact List.forall_mem_cons.2 ⟨⟨_, _, h1, (IH le).1.1 h2, hz2⟩, hl2⟩
    · obtain ⟨_, h1, _, h2, rfl⟩ := hl.forall_exists_l _ h
      have ⟨_, _, h3, h4, h5⟩ := hl2 _ h1
      exact ⟨_, _, h3, (IH le).1.2 h4, (IH le).2.2 ⟨_, h2, h5⟩⟩
  unfold plift; split
    <;> (try (first | cases Nat.le_zero.1 le | cases n); cases t)
    <;> (try · simp [lift, sort, bot, (· ≤ ·), LE, ble])
    <;> (try · cases t <;> simp [lift, sort, bot, Shape.LE.def])
  · rename_i s _ _; cases s with
    | bot | sort => grind
    | _ => cases t <;> simp [lift, sort, bot, (· ≤ ·), LE, ble]
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | forallE => ?_ | _ => intros; subst_vars; simp
    simp [Shape.plift_thm (Nat.le_of_succ_le_succ le),
      go Shape.plift_thm (Nat.le_of_succ_le_succ le)]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | lam => ?_ | _ => intros; subst_vars; simp
    simp [go Shape.plift_thm (Nat.le_of_succ_le_succ le)]; grind

omit [Params] in
theorem Shape.le_plift (le : n ≤ m) {s : Shape m} {t : Shape n} :
    t ≤ (s.plift (m := n)).1 ↔ t.lift ≤ s := (Shape.plift_thm le).1.symm

omit [Params] in
theorem Shape.plift_le (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t) ↔ s ≤ t.lift := (Shape.plift_thm le).2.symm

omit [Params] in
theorem ShapeFun.le_plift (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    LE t (plift Shape.plift s).1  ↔ LE (lift Shape.lift t) s :=
  (Shape.plift_thm.go Shape.plift_thm le).1.symm

omit [Params] in
theorem ShapeFun.plift_le (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    (∃ z, (plift Shape.plift s).2 = some z ∧ LE z t) ↔ LE s (lift Shape.lift t) :=
  (Shape.plift_thm.go Shape.plift_thm le).2.symm

omit [Params] in
theorem Shape.plift_mono {s t : Shape m} (H : s ≤ t) :
    (s.plift (m := n)).1 ≤ (t.plift (m := n)).1 := by
  obtain le | le := Nat.le_total m n
  · rw [Shape.plift_eq_lift le, Shape.plift_eq_lift le]; exact Shape.lift_mono H
  · exact (Shape.le_plift le).2 (.trans ((Shape.le_plift le).1 .rfl) H)

def Shape.Join (x y z : Shape n) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w
def ShapeFun.Join (x y z : ShapeFun n) := ∀ w, z.LE w ↔ x.LE w ∧ y.LE w

theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift : Shape m).Compat y.lift ↔ x.Compat y := sorry

theorem ShapeFun.Compat.lift {x y : ShapeFun n} (le : n ≤ m) :
    Compat Shape.Compat (lift Shape.lift x : ShapeFun m) (lift Shape.lift y) ↔
    Compat Shape.Compat x y := sorry

omit [Params] in
theorem Shape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

omit [Params] in
theorem ShapeFun.Join.le (H : Join x y z) : x.LE z ∧ y.LE z := (H _).1 .rfl

omit [Params] in
theorem Shape.join_self : Join x x y ↔ x ≤ y ∧ y ≤ x :=
  ⟨fun H => ⟨((H _).1 .rfl).1, (H _).2 ⟨.rfl, .rfl⟩⟩,
   fun ⟨H1, H2⟩ _ => ⟨fun h => ⟨H1.trans h, H1.trans h⟩, fun h => H2.trans h.1⟩⟩

omit [Params] in
theorem Shape.Compat.def {x y : Shape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := sorry

omit [Params] in
theorem Shape.Compat.mono {x y x' y' : Shape n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := Shape.Compat.def.1 H
  Shape.Compat.def.2 ⟨_, h1.trans a1, h2.trans a2⟩

omit [Params] in
theorem Shape.Join.compat (H : Join x y z) : x.Compat y := Compat.def.2 ⟨_, (H _).1 .rfl⟩

omit [Params] in
theorem Shape.Join.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift : Shape m).Join y.lift z.lift ↔ x.Join y z := sorry

def ShapeFun.join (join : Shape n → Shape n → Shape n)
    (f f' : List (Shape n × Shape n)) : List (Shape n × Shape n) := by
  refine f.foldl (init := []) fun l (x, y) => ?_
  refine f'.foldl (init := l) fun l (x', y') => ?_
  refine if x.Compat x' then ?_ else l
  let jx := join x x'
  let jy := join y y'
  exact l.map fun (z, w) => (z, if z ≤ jx then join w jy else w)

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, .bot | 0, .bot, s | _+1, .bot, s | _+1, s, .bot => s
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => if r = r' then .sort r else .bot
  | _+1, .forallE s f, .forallE s' f' => .forallE (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, _, _ => .bot

omit [Params] in
theorem Shape.Join.mk (H : x.Compat y) : Join x y (x.join y) := sorry

omit [Params] in
theorem ShapeFun.Join.mk (H : Compat Shape.Compat x y) : Join x y (join Shape.join x y) := sorry

omit [Params] in
theorem Shape.Join.iff : Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y :=
  ⟨fun h => ⟨h.compat, (mk h.compat _).2 h.le, (h _).2 (mk h.compat).le⟩,
   fun ⟨h1, h2, h3⟩ _ => .trans ⟨(.trans h2 ·), (.trans h3 ·)⟩ (mk h1 _)⟩

omit [Params] in
theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    ((x.join y).lift : Shape m) = x.lift.join y.lift := sorry

omit [Params] in
theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    (lift Shape.lift (ShapeFun.join Shape.join x y) : ShapeFun m) =
    join Shape.join (lift Shape.lift x) (lift Shape.lift y) := sorry

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n :=
  maxBelow (s.filter (·.1 ≤ a)) |>.2

def ShapeFun.WF (WF : Shape n → Bool) (f : ShapeFun n) : Bool :=
  (f.all fun (x, y) => WF x && WF y) && f.any (·.1 ≤ .bot) &&
  (f.all fun (x, y) => f.all fun (x', y') =>
    (x.Compat x' → (y.Compat y' && let j := x.join x'; f.any fun (z, _) => z ≤ j && j ≤ z)) &&
    (x ≤ x' → y ≤ y')) &&
  f.Pairwise fun (x, y) (x', y') => x ≤ x' → ¬y' ≤ y

def Shape.WF : ∀ {n}, Shape n → Bool
  | 0, _ | _+1, .bot | _+1, .sort .. => true
  | _+1, .forallE s f => s.WF && ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f

omit [Params] in
theorem ShapeFun.bot_mem (f : ShapeFun n) : ∃ y, (.bot, y) ∈ f := by
  have wf : ShapeFun.WF Shape.WF f := sorry
  simp only [WF, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at wf
  have ⟨⟨x, y⟩, hmem, hle⟩ := wf.1.1.2
  exact ⟨y, Shape.le_bot.1 hle ▸ hmem⟩

omit [Params] in
theorem ShapeFun.non_bot (f : ShapeFun n) : ∃ x y, (x, y) ∈ f ∧ y ≠ .bot := sorry

omit [Params] in
theorem ShapeFun.app_of_mem {f : ShapeFun n} (h : (x, y) ∈ f) : f.app x = y :=
  sorry

omit [Params] in
theorem ShapeFun.uniq {f : ShapeFun n} (h1 : (x, y) ∈ f) (h2 : (x', y') ∈ f)
    (h3 : x ≤ x') (h4 : y' ≤ y) : x = x' ∧ y = y' :=
  sorry

omit [Params] in
theorem ShapeFun.app_eq (f : ShapeFun n) (x) : ∃ x' y', x' ≤ x ∧ (x', y') ∈ f ∧ f.app x = y' :=
  sorry

omit [Params] in
theorem ShapeFun.app_mono_l {f f' : ShapeFun n} : f.LE f' → ∀ a, f.app a ≤ f'.app a :=
  sorry

omit [Params] in
theorem ShapeFun.app_mono_r {f : ShapeFun n} : a ≤ a' → f.app a ≤ f.app a' :=
  sorry

omit [Params] in
theorem ShapeFun.Join.app {f g h : ShapeFun n} (hJ : Join f g h) (p : Shape n) :
    Shape.Join (f.app p) (g.app p) (h.app p) := sorry

omit [Params] in
theorem ShapeFun.uniq_l {f : ShapeFun n} (h1 : (x, y) ∈ f) (h2 : (x', y') ∈ f)
    (h3 : x ≤ x') (h4 : x' ≤ x) : x = x' ∧ y = y' :=
  ShapeFun.uniq h1 h2 h3 (app_of_mem h1 ▸ app_of_mem h2 ▸ app_mono_r h4)

omit [Params] in
@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := by
  simp [ShapeFun.bot, ShapeFun.app, ShapeFun.maxBelow]

omit [Params] in
@[simp] theorem ShapeFun.lift_app (le : n ≤ m) :
    ((app f a : Shape n).lift : Shape m) = app (lift Shape.lift f) a.lift  := by
  sorry

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

omit [Params] in
@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

omit [Params] in
@[simp] theorem Shape.lift_app :
    ((app f a : Shape n).lift : Shape m) = app f.lift a.lift  := by
  sorry

def ShapeFun.single (x y : Shape n) : ShapeFun n :=
  (x, y) :: if x ≤ .bot then [] else [(.bot, .bot)]

theorem ShapeFun.single_app : (ShapeFun.single x y).app x' = if x ≤ x' then y else .bot := by
  sorry

theorem ShapeFun.single_le :
    (ShapeFun.single x y).LE f ↔ ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' := by
  sorry

omit [Params] in
theorem ShapeFun.lift_single (le : n ≤ m) {x y : Shape n} :
    lift Shape.lift (ShapeFun.single x y) = (ShapeFun.single (x.lift (m := m)) y.lift) := by
  simp [lift, single] <;> split <;> rename_i h <;>
    simpa [Shape.lift_le_bot le, Shape.le_bot] using h

omit [Params] in
theorem Shape.app_mono_l {f f' : Shape (n + 1)} (le : f ≤ f') (a) : f.app a ≤ f'.app a := by
  unfold app; split <;> [split; simp]
  · exact ShapeFun.app_mono_l le _
  · cases f' <;> simp [LE.def] at le; grind

omit [Params] in
theorem Shape.app_mono_r {f : Shape (n + 1)} {a a' : Shape n}
    (le : a ≤ a') : f.app a ≤ f.app a' := by
  unfold app; split <;> [exact ShapeFun.app_mono_r le; exact .rfl]

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b => b.all fun (x, y) => x.hasType a && y.hasType .type
  | _+1, .forallE a b, .sort r => b.all fun (x, y) => x.hasType a && y.hasType (.sort r)
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort _ => true
  | 0, .sort _, .sort j | _+1, .sort _, .sort j => j
  | _+1, .lam f, .forallE a b =>
    b.all (fun (x, y) => x.hasType a && y.hasType .type) &&
    f.all (fun (x, y) => x.hasType a && y.hasType (ShapeFun.app b x))
  | _, _, _ => false

def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

def Shape.HasDom (f : ShapeFun n) (a : Shape n) :=
  ∀ x, ∃ x', x' ≤ x ∧ HasType x' a ∧ f.app x ≤ f.app x'

omit [Params] in
theorem Shape.HasDom.def : HasDom f a ↔ ∀ x y, (x, y) ∈ f → x.HasType a := by
  refine ⟨fun H x y h => ?_, fun H x => ?_⟩
  · sorry
  · have ⟨x', y', hle, hmem, heq⟩ := ShapeFun.app_eq f x
    exact ⟨x', hle, H _ _ hmem, heq ▸ ShapeFun.app_of_mem hmem ▸ .rfl⟩

omit [Params] in
theorem Shape.HasDom.lift (le : n ≤ m) :
    HasDom (n := m) (.lift Shape.lift f) a.lift ↔ HasDom (n := n) f a := by
  sorry

def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) (rel : Bool) :=
  Shape.HasDom b a ∧ ∀ x, HasType x a → HasType (b.app x) (.sort rel)

omit [Params] in
theorem Shape.HasTypePi.def {b : ShapeFun n} :
    HasTypePi b a r ↔ Shape.HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort r) := by
  refine and_congr_right fun H1 => ⟨fun H x y h => ?_, fun H x h => ?_⟩
  · exact b.app_of_mem h ▸ H _ (Shape.HasDom.def.1 H1 _ _ h)
  · have ⟨_, _, h1, h2, h3⟩ := b.app_eq x
    exact h3 ▸ H _ _ h2

def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  Shape.HasTypePi b a true ∧ Shape.HasDom f a ∧ ∀ x, HasType x a → HasType (f.app x) (b.app x)

omit [Params] in
theorem Shape.HasType.mono_r {m a a' : Shape n} (ha : a ≤ a') :
    HasType a' (.sort r) → HasType m a → HasType m a' := sorry

omit [Params] in
theorem Shape.HasTypeLam.def {b : ShapeFun n} : HasTypeLam f a b ↔
    Shape.HasTypePi b a true ∧ Shape.HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x) := by
  refine and_congr_right fun H1 => and_congr_right fun H2 => ⟨fun H x y h => ?_, fun H x h => ?_⟩
  · exact f.app_of_mem h ▸ H _ (Shape.HasDom.def.1 H2 _ _ h)
  · have ⟨_, _, h1, h2, h3⟩ := f.app_eq x
    exact .mono_r (ShapeFun.app_mono_r h1) (H1.2 _ h) (h3 ▸ H _ _ h2)

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.forallE a b)

omit [Params] in
theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := by
  unfold HasType hasType; split <;> (try simp) <;> intros <;> subst_vars <;>
    constructor -- <;> try grind [HasType, type]
  · simp [HasType, hasType]; grind
  · rename_i b _ H
    refine ⟨HasDom.def.2 fun _ _ h => (H _ _ h).1, fun x h => ?_⟩
    have ⟨_, _, h1, h2, h3⟩ := ShapeFun.app_eq b x
    exact h3 ▸ (H _ _ h2).2
  · rename_i x; cases x <;> rfl
  · rfl
  · rfl
  · rename_i h1 h2
    exact Shape.HasTypeLam.def.2 ⟨Shape.HasTypePi.def.2 ⟨
      Shape.HasDom.def.2 fun _ _ h => (h1 _ _ h).1, fun _ _ h => (h1 _ _ h).2⟩,
      Shape.HasDom.def.2 fun _ _ h => (h2 _ _ h).1, fun _ _ h => (h2 _ _ h).2⟩

omit [Params] in
theorem Shape.HasType.unfold_iff {m a : Shape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  unfold HasType hasType
  cases h with
  | bot h =>
    cases h.unfold with
    | bot | sort => cases n <;> rfl
    | forallE => simpa [HasType, hasType] using h
  | sort => cases n <;> rfl
  | forallE h =>
    have := HasTypePi.def.1 h
    have := HasDom.def.1 this.1
    simp; grind [HasType]
  | lam h =>
    have ⟨h1, h2, _⟩ := HasTypeLam.def.1 h
    have := HasDom.def.1 h2
    have := HasTypePi.def.1 h1
    have := HasDom.def.1 this.1
    simp; grind [HasType]

omit [Params] in
theorem Shape.HasType.bot' : HasType (n := n) x .type → HasType .bot x :=
  (unfold_iff.2 <| .bot ·)
omit [Params] in
theorem Shape.HasType.sort : HasType (n := n) (.sort r) .type := unfold_iff.2 .sort
omit [Params] in
theorem Shape.HasType.forallE : HasTypePi (n := n) b a r →
    HasType (n := n+1) (.forallE a b) (.sort r) := (unfold_iff.2 <| .forallE ·)
omit [Params] in
theorem Shape.HasType.lam : HasTypeLam (n := n) f a b →
    HasType (n := n+1) (.lam f) (.forallE a b) := (unfold_iff.2 <| .lam ·)

omit [Params] in
theorem Shape.HasType.toType : HasType (n := n) x (.sort r) → HasType x .type := by
  induction n with intro H
  | zero =>
    cases H.unfold with
    | bot h => exact .bot' h
    | sort => exact .sort
  | succ _ ih =>
    cases H.unfold with
    | bot h => exact .bot' h
    | sort => exact .sort
    | forallE h => exact .forallE ⟨h.1, fun _ h' => ih (h.2 _ h')⟩

omit [Params] in
theorem Shape.HasTypePi.toType (H : HasTypePi (n := n) b a r) : HasTypePi (n := n) b a true :=
  ⟨H.1, fun _ h' => (H.2 _ h').toType⟩

omit [Params] in
theorem Shape.HasType.bot : HasType (n := n) x (.sort r) → HasType .bot x := (.bot' ·.toType)

omit [Params] in
theorem Shape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases H.unfold <;> rfl

omit [Params] in
theorem Shape.HasType.isType {m a : Shape n} (h : HasType m a) : HasType a .type := by
  cases h.unfold with
  | bot h1 => exact h1
  | sort | forallE => exact .sort
  | lam h1 => exact .forallE h1.1

omit [Params] in
theorem Shape.HasDom.isType (H : Shape.HasDom f a) : a.HasType .type :=
  let ⟨_, _, h, _⟩ := H .bot; h.isType

omit [Params] in
theorem Shape.HasDom.bot (ha : a.HasType .type) : HasDom .bot a :=
  fun _ => ⟨_, bot_le, .bot ha, ShapeFun.bot_app.symm ▸ bot_le⟩

theorem Shape.HasType.lift (h : n ≤ n') :
    HasType (n := n') m.lift a.lift ↔ HasType (n := n) m a := sorry

omit [Params] in
theorem Shape.HasType.join (hJ : Join m₁ m₂ m) :
    HasType m₁ a → HasType m₂ a → HasType m a := sorry

omit [Params] in
theorem Shape.HasType.mono_l {m a : Shape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a :=
  .join (Shape.join_self.2 ⟨hm1, hm2⟩) H H

omit [Params] in
theorem Shape.HasType.proofIrrel
    (ha : HasType (n := n) a .prop) (hx : HasType x a) : x = .bot := by
  cases n with | zero => cases ha.unfold; exact hx.bot_r | succ n
  cases ha.unfold with | bot => exact hx.bot_r | forallE ha
  cases hx.unfold with | bot => rfl | @lam _ f _ _ hx
  obtain ⟨x, y, h1, h2⟩ := f.non_bot
  obtain ⟨x', a1, a2, a3⟩ := hx.2.1 x
  have := f.app_of_mem h1 ▸ (hx.2.2 _ a2).mono_l (ShapeFun.app_mono_r a1) a3
  cases h2 (proofIrrel (ha.2 _ a2) this)

omit [Params] in
theorem Shape.HasDom.single : HasDom (ShapeFun.single x y) a ↔ x.HasType a := by
  simp [Shape.HasDom.def, ShapeFun.single, or_imp, forall_and]
  intro h _ _ _ rfl _; exact .bot h.isType

omit [Params] in
theorem Shape.HasDom.mono (le : a ≤ a') (h : a'.HasType .type) (H : HasDom f a) : HasDom f a' :=
  fun x => let ⟨_, h1, h2, h3⟩ := H x; ⟨_, h1, .mono_r le h h2, h3⟩

omit [Params] in
theorem Shape.HasDom.join (h1 : HasDom f₁ a₁) (h2 : HasDom f₂ a₂)
    (cf : ShapeFun.Compat Compat f₁ f₂) (ca : a₁.Compat a₂) :
    HasDom (ShapeFun.join join f₁ f₂) (a₁.join a₂) := by
  intro a
  have ⟨x₁, a1, a2, a3⟩ := h1 a
  have ⟨x₂, b1, b2, b3⟩ := h2 a
  have ja := Shape.Join.mk ca
  have aa := a2.isType.join ja b2.isType
  have jx := Shape.Join.mk (Shape.Compat.def.2 ⟨_, a1, b1⟩)
  refine ⟨_, (jx _).2 ⟨a1, b1⟩, (aa.mono_r ja.le.1 a2).join jx (aa.mono_r ja.le.2 b2), ?_⟩
  have jf := ShapeFun.Join.mk cf
  refine (ShapeFun.Join.app jf a _).2 ⟨?_, ?_⟩
  · exact a3.trans <| (ShapeFun.app_mono_r jx.le.1).trans (ShapeFun.app_mono_l jf.le.1 _)
  · exact b3.trans <| (ShapeFun.app_mono_r jx.le.2).trans (ShapeFun.app_mono_l jf.le.2 _)

def Valuation := Nat → Σ n, Shape n

def Valuation.nil : Valuation := fun _ => ⟨0, .bot⟩
def Valuation.push (ρ : Valuation) (u : Shape n) : Valuation
  | 0 => ⟨_, u⟩
  | n+1 => ρ n

def Valuation.LE (ρ ρ' : Valuation) : Prop :=
  ∀ n m, (ρ n).1 ≤ m → (ρ' n).1 ≤ m → (ρ n).2.lift (m := m) ≤ (ρ' n).2.lift (m := m)

omit [Params] in
theorem Valuation.LE.rfl {ρ : Valuation} : ρ.LE ρ :=
  fun _ _ _ _ => .rfl

omit [Params] in
theorem Valuation.LE.push' {ρ ρ' : Valuation} (le1 : n ≤ m) (le2 : n' ≤ m) :
    (ρ.push (n := n) a).LE (ρ'.push (n := n') a') ↔ ρ.LE ρ' ∧ a.lift (m := m) ≤ a'.lift := by
  refine ⟨fun H => ⟨fun _ _ h1 h2 => H (_+1) _ h1 h2, ?_⟩, ?_⟩
  · exact H 0 _ le1 le2
  · rintro ⟨H1, H2⟩ (_|n) m' h1 h2
    · have := Shape.lift_mono (m := max m m') H2
      apply (Shape.lift_le_lift (Nat.le_max_right m m')).1
      rw [Shape.lift_lift (.inl le1), Shape.lift_lift (.inl le2)] at this
      rwa [Shape.lift_lift (.inl h1), Shape.lift_lift (.inl h2)]
    · exact H1 _ _ h1 h2

omit [Params] in
theorem Valuation.LE.push {ρ ρ' : Valuation} : (ρ.push a).LE (ρ'.push a') ↔ ρ.LE ρ' ∧ a ≤ a' := by
  rw [Valuation.LE.push' (Nat.le_refl _) (Nat.le_refl _), Shape.lift_le_lift (Nat.le_refl _)]

/-- Two valuations are compatible if their entries are compatible at each index
(after lifting to a common level). -/
def Valuation.Compat (ρ₁ ρ₂ : Valuation) : Prop :=
  ∀ i, ((ρ₁ i).2.lift (m := max (ρ₁ i).1 (ρ₂ i).1)).Compat (ρ₂ i).2.lift

/-- Pointwise join of two valuations. Each entry is lifted to a common level and joined. -/
def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i =>
  ⟨max (ρ₁ i).1 (ρ₂ i).1, (ρ₁ i).2.lift.join (ρ₂ i).2.lift⟩

omit [Params] in
theorem Valuation.Compat.le_join {ρ₁ ρ₂ : Valuation}
    (hc : ρ₁.Compat ρ₂) : ρ₁.LE (ρ₁.join ρ₂) ∧ ρ₂.LE (ρ₁.join ρ₂) := by
  simp only [Valuation.LE, Valuation.join]
  constructor <;> intro i m h1 h2
  · have := Shape.lift_mono (m := m) (Shape.Join.mk (hc i)).le.1
    rwa [Shape.lift_lift (.inl (Nat.le_max_left ..))] at this
  · have := Shape.lift_mono (m := m) (Shape.Join.mk (hc i)).le.2
    rwa [Shape.lift_lift (.inl (Nat.le_max_right ..))] at this

inductive LE_Interp : Valuation → ∀ {n}, Shape n → SExpr → Prop
  | bot : LE_Interp ρ .bot M
  -- | le : m ≤ m' → LE_Interp ρ m' M → LE_Interp ρ m M
  -- | unlift : n ≤ n' → LE_Interp (n := n') ρ m.lift M → LE_Interp (n := n) ρ m M
  | bvar : (ρ i).1 ≤ n' → n ≤ n' →
    m.lift (m := n') ≤ (ρ i).2.lift → LE_Interp (n := n) ρ m (.bvar i)
  | sort : m ≤ .sort (l ≠ .zero) → LE_Interp ρ m (.sort l)
  | app : LE_Interp (n := n+1) ρ f F → LE_Interp ρ a A →
    n' ≤ n → m.lift ≤ f.app a → LE_Interp (n := n') ρ m (.app F A)
  | lam : LE_Interp (n := n) ρ a A →
    Shape.HasDom f a → (∀ x, x.HasType a → LE_Interp (ρ.push x) ((f : ShapeFun n).app x) F) →
    n' ≤ n+1 → m.lift (m := n+1) ≤ .lam f → LE_Interp (n := n') ρ m (.lam A F)
  | forallE : LE_Interp (n := n) ρ b B → LE_Interp (n := n) ρ b' B →
    Shape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x) ((f : ShapeFun n).app x) F) →
    n' ≤ n+1 → m.lift (m := n+1) ≤ .forallE b f → LE_Interp (n := n') ρ m (.forallE B F)

theorem LE_Interp.bvar' : LE_Interp ρ (ρ i).2 (.bvar i) :=
  .bvar (Nat.le_refl _) (Nat.le_refl _) .rfl
theorem LE_Interp.bvar0 : LE_Interp (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem LE_Interp.sort' : LE_Interp (n := n) ρ (.sort (l ≠ .zero)) (.sort l) := .sort .rfl
theorem LE_Interp.app' (h1 : LE_Interp (n := n+1) ρ f F) (h2 : LE_Interp ρ a A) :
    LE_Interp ρ (f.app a) (.app F A) := .app h1 h2 (Nat.le_refl _) (Shape.lift_self ▸ .rfl)
theorem LE_Interp.lam' {f : ShapeFun n} (h1 : LE_Interp ρ a A) (h2 : Shape.HasDom f a)
    (h3 : ∀ x, x.HasType a → LE_Interp (ρ.push x) (f.app x) F) :
    LE_Interp (n := n+1) ρ (.lam f) (.lam A F) :=
  .lam h1 h2 h3 (Nat.le_refl _) (Shape.lift_self ▸ .rfl)
theorem LE_Interp.forallE' {f : ShapeFun n}
    (h1 : LE_Interp (n := n) ρ b B) (h2 : LE_Interp (n := n) ρ b' B)
    (h3 : Shape.HasDom f b') (h4 : ∀ x, x.HasType b' → LE_Interp (ρ.push x) (f.app x) F) :
    LE_Interp (n := n+1) ρ (.forallE b f) (.forallE B F) :=
  .forallE h1 h2 h3 h4 (Nat.le_refl _) (Shape.lift_self ▸ .rfl)

theorem LE_Interp.bvar_iff :
    LE_Interp (n := n) ρ m (.bvar i) ↔
    ∃ k, n ≤ k ∧ (ρ i).1 ≤ k ∧ m.lift (m := k) ≤ (ρ i).2.lift := by
  refine ⟨?_, fun ⟨k, h1, h2, h3⟩ => .bvar h2 h1 h3⟩
  intro
  | .bot => exact ⟨_, Nat.le_max_left .., Nat.le_max_right .., Shape.lift_bot.symm ▸ Shape.bot_le⟩
  | .bvar h1 h2 h3 => exact ⟨_, h2, h1, h3⟩

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort (u ≠ .zero) := by
  generalize eq : SExpr.sort u = M at H
  induction H with cases eq
  | bot => exact Shape.bot_le
  | sort h => exact h

theorem LE_Interp.mono (h : m ≤ m') (H : LE_Interp ρ m' M) : LE_Interp ρ m M := by
  induction H with
  | bot => exact Shape.le_bot.1 h ▸ .bot
  | bvar h1 h2 h3 => exact .bvar h1 h2 ((Shape.lift_mono h).trans h3)
  | sort h1 => exact .sort (h.trans h1)
  | app hf ha hle h1 => exact .app hf ha hle ((Shape.lift_mono h).trans h1)
  | lam ha hdom hbody hle h1 => exact .lam ha hdom hbody hle ((Shape.lift_mono h).trans h1)
  | forallE hb hb' hdom hbody hle h1 => exact .forallE hb hb' hdom hbody hle ((Shape.lift_mono h).trans h1)

theorem LE_Interp.mono_l (hρ : ρ.LE ρ') (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 h2 h3 =>
    refine have le₁ := Nat.le_max_left ..; have le₂ := Nat.le_max_right ..
      .bvar le₂ (Nat.le_trans h2 le₁) (.trans ?_ (hρ _ _ (Nat.le_trans h1 le₁) le₂))
    rw [← Shape.lift_lift (.inl h2), ← Shape.lift_lift (.inl h1)]; exact Shape.lift_mono h3
  | sort h1 => exact .sort h1
  | app _ _ hle h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) hle h1
  | lam _ hdom _ hle h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) hle h1
  | forallE _ _ hdom _ hle h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ hle h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)

theorem LE_Interp.unlift (le : n ≤ n')
    (H : LE_Interp (n := n') ρ m.lift M) : LE_Interp (n := n) ρ m M := by
  generalize eq : m.lift = m' at H
  cases H with try subst eq
  | bot => exact (Shape.lift_eq_bot le).1 eq ▸ .bot
  | sort h1 => exact .sort ((Shape.lift_le_lift le).1 (Shape.lift_sort.symm ▸ h1))
  | bvar h1 h2 h3 => exact .bvar h1 (Nat.le_trans le h2) (Shape.lift_lift (.inl le) ▸ h3)
  | app hf ha h1 h2 => exact .app hf ha (Nat.le_trans le h1) (Shape.lift_lift (.inl le) ▸ h2)
  | lam ha hdom hbody h1 h2 =>
    exact .lam ha hdom hbody (Nat.le_trans le h1) (Shape.lift_lift (.inl le) ▸ h2)
  | forallE hb hb' hdom hbody h1 h2 =>
    exact .forallE hb hb' hdom hbody (Nat.le_trans le h1) (Shape.lift_lift (.inl le) ▸ h2)

theorem LE_Interp.lift (le : n ≤ n')
    (H : LE_Interp (n := n) ρ m M) : LE_Interp (n := n') ρ m.lift M := by
  induction H generalizing n' with
  | bot => exact Shape.lift_bot.symm ▸ .bot
  | sort h1 => exact .sort (Shape.lift_sort ▸ (Shape.lift_le_lift le).2 h1)
  | @bvar _ k _ _ _ h1 h2 h3 =>
    refine .bvar (Nat.le_trans h1 (Nat.le_max_left ..)) (Nat.le_max_right ..) ?_
    rw [Shape.lift_lift (.inl le), ← Shape.lift_lift (.inl h2), ← Shape.lift_lift (.inl h1)]
    exact Shape.lift_mono h3
  | @app _ k _ _ _ _ _ _ hf ha h1 h2 ih_f ih_a =>
    have le₁ := Nat.le_max_left k n'
    refine .app (ih_f (Nat.succ_le_succ le₁)) (ih_a le₁) (Nat.le_max_right ..) ?_
    rw [← Shape.lift_app, Shape.lift_lift (.inl le), ← Shape.lift_lift (.inl h1)]
    exact Shape.lift_mono h2
  | @lam _ k _ _ f _ _ _ ha hdom hbody h1 h2 ih_a ih_f =>
    have le₁ := Nat.le_max_left k n'; have le₂ := Nat.le_max_right k n'
    have hdom' := (Shape.HasDom.lift le₁).2 hdom
    refine .lam (ih_a le₁) hdom' ?_ (Nat.le_succ_of_le le₂) ?_
    · intro x h
      obtain ⟨_, _, a1, a2, a3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f) x
      obtain ⟨⟨x', y'⟩, a2', ⟨⟩⟩ := List.mem_map.1 a2
      have hx' := Shape.HasDom.def.1 hdom _ _ a2'
      exact a3 ▸ (ShapeFun.app_of_mem a2' ▸ ih_f x' hx' le₁).mono_l
        ((Valuation.LE.push' le₁ (Nat.le_refl _)).2 ⟨.rfl, by rwa [Shape.lift_self]⟩)
    · rw [Shape.lift_lift (.inl le), ← Shape.lift_lift (.inl h1)]
      exact Shape.lift_mono h2
  | @forallE _ k _ _ _ f _ _ _ hb hb' hdom hbody h1 h2 ih_b ih_b' ih_f =>
    have le₁ := Nat.le_max_left k n'; have le₂ := Nat.le_max_right k n'
    have hdom' := (Shape.HasDom.lift le₁).2 hdom
    refine .forallE (ih_b le₁) (ih_b' le₁) hdom' ?_ (Nat.le_succ_of_le le₂) ?_
    · intro x h
      obtain ⟨_, _, a1, a2, a3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f) x
      obtain ⟨⟨x', y'⟩, a2', ⟨⟩⟩ := List.mem_map.1 a2
      have hx' := Shape.HasDom.def.1 hdom _ _ a2'
      exact a3 ▸ (ShapeFun.app_of_mem a2' ▸ ih_f x' hx' le₁).mono_l
        ((Valuation.LE.push' le₁ (Nat.le_refl _)).2 ⟨.rfl, by rwa [Shape.lift_self]⟩)
    · rw [Shape.lift_lift (.inl le), ← Shape.lift_lift (.inl h1)]
      exact Shape.lift_mono h2

theorem LE_Interp.lift_iff (le : n ≤ n') :
    LE_Interp (n := n') ρ m.lift M ↔ LE_Interp (n := n) ρ m M := ⟨.unlift le, .lift le⟩

theorem LE_Interp.weak'_iff (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    LE_Interp ρ' m (M.lift' l) ↔ LE_Interp ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 h2 h3 => rw [← h] at h1 h3; exact .bvar h1 h2 h3
    | app _ _ hle h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) hle h1
    | lam _ hdom _ hle h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) hle h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ hle h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) hle h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 h2 h3 => rw [h] at h1 h3; exact .bvar h1 h2 h3
    | app _ _ hle h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) hle h1
    | lam _ hdom _ hle h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) hle h1
      exact ih_body y hy l.cons (fun i => by cases i <;> simp [Valuation.push, h])
    | forallE _ _ hdom _ hle h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) hle h1
      exact ih_body y hy l.cons (fun i => by cases i <;> simp [Valuation.push, h])

theorem LE_Interp.weak_iff : LE_Interp (ρ.push x) m M.lift ↔ LE_Interp ρ m M :=
  LE_Interp.weak'_iff (.skip .refl) (fun _ => rfl)

theorem LE_Interp.weak (H : LE_Interp ρ m M) : LE_Interp (ρ.push x) m M.lift :=
  weak_iff.2 H

private theorem LE_Interp.compat_join {m₁ m₂ : Shape n}
    (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M := by
  have mk {n ρ m₁ m₂ m M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : LE_Interp ρ m M) :
      m₁.Compat (n := n) m₂ ∧ LE_Interp ρ (m₁.join m₂) M :=
    have := Shape.Compat.def.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((Shape.Join.mk this _).2 ⟨H1, H2⟩)⟩
  have lift {ρ n n' M} {m₁ m₂ : Shape n} (le : n ≤ n')
      : m₁.lift.Compat (n := n') m₂.lift ∧ LE_Interp ρ (m₁.lift.join m₂.lift) M →
      m₁.Compat (n := n) m₂ ∧ LE_Interp ρ (m₁.join m₂) M
    | ⟨H1, H2⟩ => ⟨(Shape.Compat.lift le).1 H1, ((Shape.lift_join le).symm ▸ H2).unlift le⟩
  induction M generalizing ρ n m₁ m₂ with
  | const => cases H1 with | bot => exact mk Shape.bot_le .rfl H2
  | sort =>
    cases id H1 with | bot => exact mk Shape.bot_le .rfl H2 | sort h1
    cases H2 with | bot => exact mk .rfl Shape.bot_le H1 | sort h2
    exact mk h1 h2 (.sort .rfl)
  | bvar =>
    cases id H1 with | bot => exact mk Shape.bot_le .rfl H2 | bvar h1n h1k h1le
    cases H2 with | bot => exact mk .rfl Shape.bot_le H1 | bvar h2n h2k h2le
    rename_i k₁ k₂
    have h1le' := Shape.lift_lift (.inl h1k) ▸ Shape.lift_lift (.inl h1n) ▸
      Shape.lift_mono (m := max k₁ k₂) h1le
    have h2le' := Shape.lift_lift (.inl h2k) ▸ Shape.lift_lift (.inl h2n) ▸
      Shape.lift_mono (m := max k₁ k₂) h2le
    have le := Nat.le_trans h1k (Nat.le_max_left k₁ k₂)
    exact lift le <| mk h1le' h2le' <| .lift (Nat.le_trans h1n (Nat.le_max_left ..)) .bvar'
  | app _ _ _ ih_f ih_a =>
    cases id H1 with | bot => exact mk Shape.bot_le .rfl H2 | app hf ha hle h1
    cases H2 with | bot => exact mk .rfl Shape.bot_le H1 | app hf' ha' hle' h1'
    rename_i n₁ _ _ n₂ _ _
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have ⟨cf, jf⟩ := ih_f (hf.lift (Nat.succ_le_succ le₁)) (hf'.lift (Nat.succ_le_succ le₂))
    have ⟨ca, ja⟩ := ih_a (ha.lift le₁) (ha'.lift le₂)
    have hf := (Shape.Join.mk cf).le
    have ha := (Shape.Join.mk ca).le
    refine lift (Nat.le_trans hle le₁) <| mk ?_ ?_ (jf.app' ja)
    · have := (Shape.app_mono_l hf.1 _).trans (Shape.app_mono_r ha.1)
      exact Shape.lift_lift (.inl hle) ▸ (Shape.lift_mono h1).trans <| Shape.lift_app ▸ this
    · have := (Shape.app_mono_l hf.2 _).trans (Shape.app_mono_r ha.2)
      exact Shape.lift_lift (.inl hle') ▸ (Shape.lift_mono h1').trans <| Shape.lift_app ▸ this
  | lam A F ih_a ih_f =>
    cases id H1 with | bot => exact mk Shape.bot_le .rfl H2 | lam ha hdom he hle h1
    cases H2 with | bot => exact mk .rfl Shape.bot_le H1 | lam ha' hdom' he' hle' h1'
    rename_i n₁ a₁ f₁ n₂ a₂ f₂; let k := max n₁ n₂
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have ⟨ca, ia⟩ := ih_a (ha.lift le₁) (ha'.lift le₂)
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂)
        (hc : x₁.lift.Compat (n := k) x₂.lift) :
        y₁.lift.Compat (n := k) y₂.lift ∧
        LE_Interp (ρ.push (x₁.lift.join (n := k) x₂.lift)) (y₁.lift.join (n := k) y₂.lift) F := by
      have ⟨j1, j2⟩ := (Shape.Join.mk hc).le
      have hx1 := Shape.HasDom.def.1 hdom _ _ h1
      have hx2 := Shape.HasDom.def.1 hdom' _ _ h2
      apply ih_f
      · exact ShapeFun.app_of_mem h1 ▸ he _ hx1 |>.lift le₁ |>.mono_l <|
          (Valuation.LE.push' le₁ (Nat.le_refl _)).2 ⟨.rfl, by exact Shape.lift_self ▸ j1⟩
      · exact ShapeFun.app_of_mem h2 ▸ he' _ hx2 |>.lift le₂ |>.mono_l <|
          (Valuation.LE.push' le₂ (Nat.le_refl _)).2 ⟨.rfl, by exact Shape.lift_self ▸ j2⟩
    replace h1 := Shape.lift_lift (.inl hle) ▸ Shape.lift_mono (m := k+1) h1
    replace h1' := Shape.lift_lift (.inl hle') ▸ Shape.lift_mono (m := k+1) h1'
    refine have cf : ShapeFun.Compat .. := ?_; have cm := Shape.Compat.mono h1 h1' cf
      lift (Nat.le_trans hle (Nat.succ_le_succ le₁)) ⟨cm, ?_⟩
    · simp only [ShapeFun.Compat, List.all_eq_true, decide_eq_true_eq, ShapeFun.lift,
        List.all_map, Function.comp_apply]
      exact fun (x₁, y₁) h1 (x₂, y₂) h2 hc => (hC h1 h2 hc).1
    have jf := ShapeFun.Join.mk cf
    have hdom := (Shape.HasDom.lift le₁).2 hdom
    have hdom' := (Shape.HasDom.lift le₂).2 hdom'
    refine .mono ((Shape.Join.mk cm _).2 ⟨h1.trans jf.le.1, h1'.trans jf.le.2⟩) <|
      .lam' ia (hdom.join hdom' cf ca) fun x hx => ?_
    have ⟨_, _, a1, a2', a3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f₁) x
    obtain ⟨⟨x₁, y₁⟩, a2, ⟨⟩⟩ := List.mem_map.1 a2'
    have a4 := (Shape.HasType.lift le₁).1 <| Shape.HasDom.def.1 hdom _ _ a2'
    rw [← ShapeFun.app_of_mem a2] at a3
    have ⟨_, _, b1, b2', b3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f₂) x
    obtain ⟨⟨x₂, y₂⟩, b2, ⟨⟩⟩ := List.mem_map.1 b2'
    have b4 := (Shape.HasType.lift le₂).1 <| Shape.HasDom.def.1 hdom' _ _ b2'
    rw [← ShapeFun.app_of_mem b2] at b3
    refine ih_f ?_ ?_ |>.2.mono (Shape.Join.iff.1 (jf.app x)).2.2
    · refine a3 ▸ .lift le₁ ?_
      exact (he _ a4).mono_l <| (Valuation.LE.push' le₁ (Nat.le_refl _)).2
        ⟨.rfl, Shape.lift_lift (.inl le₁) ▸ Shape.lift_mono a1⟩
    · refine b3 ▸ .lift le₂ ?_
      exact (he' _ b4).mono_l <| (Valuation.LE.push' le₂ (Nat.le_refl _)).2
        ⟨.rfl, Shape.lift_lift (.inl le₂) ▸ Shape.lift_mono b1⟩
  | forallE A F ih_a ih_f =>
    cases id H1 with | bot => exact mk Shape.bot_le .rfl H2 | forallE hb ha hdom he hle h1
    cases H2 with | bot => exact mk .rfl Shape.bot_le H1 | forallE hb2 ha2 hdom2 he2 hle2 h12
    rename_i n₁ _ a₁ f₁ n₂ _ a₂ f₂; let k := max n₁ n₂
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have ⟨cb, ib⟩ := ih_a (hb.lift le₁) (hb2.lift le₂)
    have ⟨ca, ia⟩ := ih_a (ha.lift le₁) (ha2.lift le₂)
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂)
        (hc : x₁.lift.Compat (n := k) x₂.lift) :
        y₁.lift.Compat (n := k) y₂.lift ∧
        LE_Interp (ρ.push (x₁.lift.join (n := k) x₂.lift)) (y₁.lift.join (n := k) y₂.lift) F := by
      have ⟨j1, j2⟩ := (Shape.Join.mk hc).le
      have hx1 := Shape.HasDom.def.1 hdom _ _ h1
      have hx2 := Shape.HasDom.def.1 hdom2 _ _ h2
      apply ih_f
      · exact ShapeFun.app_of_mem h1 ▸ he _ hx1 |>.lift le₁ |>.mono_l <|
          (Valuation.LE.push' le₁ (Nat.le_refl _)).2 ⟨.rfl, by exact Shape.lift_self ▸ j1⟩
      · exact ShapeFun.app_of_mem h2 ▸ he2 _ hx2 |>.lift le₂ |>.mono_l <|
          (Valuation.LE.push' le₂ (Nat.le_refl _)).2 ⟨.rfl, by exact Shape.lift_self ▸ j2⟩
    replace h1 := Shape.lift_lift (.inl hle) ▸ Shape.lift_mono (m := k+1) h1
    replace h12 := Shape.lift_lift (.inl hle2) ▸ Shape.lift_mono (m := k+1) h12
    have cf : ShapeFun.Compat (Shape.Compat (n := k))
        (ShapeFun.lift Shape.lift f₁) (ShapeFun.lift Shape.lift f₂) := by
      simp only [ShapeFun.Compat, List.all_eq_true, decide_eq_true_eq, ShapeFun.lift,
        List.all_map, Function.comp_apply]
      exact fun (x₁, y₁) h1 (x₂, y₂) h2 hc => (hC h1 h2 hc).1
    refine have cm := Shape.Compat.mono h1 h12 ?_
      lift (Nat.le_trans hle (Nat.succ_le_succ le₁)) ⟨cm, ?_⟩
    · simp [Shape.Compat, Shape.lift]; exact ⟨cb, cf⟩
    have jb := Shape.Join.mk cb; have jf := ShapeFun.Join.mk cf
    have hdom := (Shape.HasDom.lift le₁).2 hdom
    have hdom2 := (Shape.HasDom.lift le₂).2 hdom2
    refine .mono ((Shape.Join.mk cm _).2 ⟨?_, ?_⟩) <|
       .forallE' ib ia (hdom.join hdom2 cf ca) (fun x hx => ?_)
    · exact h1.trans (Shape.LE.def.2 ⟨jb.le.1, jf.le.1⟩)
    · exact h12.trans (Shape.LE.def.2 ⟨jb.le.2, jf.le.2⟩)
    have ⟨_, _, a1, a2', a3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f₁) x
    obtain ⟨⟨x₁, y₁⟩, a2, ⟨⟩⟩ := List.mem_map.1 a2'
    have a4 := (Shape.HasType.lift le₁).1 <| Shape.HasDom.def.1 hdom _ _ a2'
    rw [← ShapeFun.app_of_mem a2] at a3
    have ⟨_, _, b1, b2', b3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f₂) x
    obtain ⟨⟨x₂, y₂⟩, b2, ⟨⟩⟩ := List.mem_map.1 b2'
    have b4 := (Shape.HasType.lift le₂).1 <| Shape.HasDom.def.1 hdom2 _ _ b2'
    rw [← ShapeFun.app_of_mem b2] at b3
    refine ih_f ?_ ?_ |>.2.mono (Shape.Join.iff.1 (jf.app x)).2.2
    · refine a3 ▸ .lift le₁ ?_
      exact (he _ a4).mono_l <| (Valuation.LE.push' le₁ (Nat.le_refl _)).2
        ⟨.rfl, Shape.lift_lift (.inl le₁) ▸ Shape.lift_mono a1⟩
    · refine b3 ▸ .lift le₂ ?_
      exact (he2 _ b4).mono_l <| (Valuation.LE.push' le₂ (Nat.le_refl _)).2
        ⟨.rfl, Shape.lift_lift (.inl le₂) ▸ Shape.lift_mono b1⟩

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ :=
  (H1.compat_join H2).1

theorem LE_Interp.join' (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ (m₁.join m₂) M :=
  (H1.compat_join H2).2

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M := (H1.join' H2).mono (Shape.Join.iff.1 J).2.2

theorem LE_Interp.subst : LE_Interp (n := n) ρ m (M.subst σ) ↔
    ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i).2 (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · induction M generalizing n σ ρ with
    | bvar j =>
      refine ⟨fun k => if k = j then ⟨_, m⟩ else ⟨0, .bot⟩, ?_, fun k => ?_⟩
      · refine .unlift (by simp) <| .mono ?_ .bvar'
        rw [if_pos rfl, Shape.lift_self]; exact .rfl
      · dsimp; by_cases eq : k = j
        · exact if_pos eq ▸ eq ▸ H
        · exact if_neg eq ▸ .bot
    | sort => exact ⟨.nil, .mono H.le_sort .sort', fun _ => .bot⟩
    | const => cases H with | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
    | app F A _ ih_F ih_A =>
      cases H with | bot => exact ⟨.nil, .bot, fun _ => .bot⟩ | app hf ha hle h1
      have ⟨ρ₁, hF, h₁⟩ := ih_F hf
      have ⟨ρ₂, hA, h₂⟩ := ih_A ha
      have hc : ρ₁.Compat ρ₂ := fun i =>
        ((h₁ i).lift (Nat.le_max_left ..)).compat ((h₂ i).lift (Nat.le_max_right ..))
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) hle h1, fun i => ?_⟩
      exact (h₁ i).lift (Nat.le_max_left ..) |>.join' ((h₂ i).lift (Nat.le_max_right ..))
    | lam A F ih_A ih_F =>
      cases H with
      | bot => exact ⟨.nil, .bot, fun _ => .bot⟩ | @lam ρ n₁ a A f F n' m' ha hdom hbody hle h1
      suffices ∃ ρ', LE_Interp ρ' a A ∧ (∀ i, LE_Interp ρ (ρ' i).2 (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1) x.2 F by
        have ⟨ρ', ha, hρ, H⟩ := this
        refine ⟨ρ', .lam ha hdom (fun x h => ?_) hle h1, hρ⟩
        obtain ⟨x', y', a1, a2, rfl⟩ := ShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2 F ∧ ∀ i, LE_Interp (ρ.push x.1) (ρ' i).snd (σ.lift i) :=
        ih_F (σ := σ.lift) (ShapeFun.app_of_mem h ▸ hbody _ (Shape.HasDom.def.1 hdom _ _ h))
      clear h1 hdom hbody
      have ⟨ρA, ha, hρA⟩ := ih_A ha
      induction f with | nil => exact ⟨ρA, ha, hρA, nofun⟩ | cons x f ih
      have ⟨⟨ρ₁, hy, hρ₁⟩, H⟩ := List.forall_mem_cons.1 H
      have ⟨ρ₂, ha, hρ₂, H⟩ := ih H
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i).2 (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i =>
        ((hρ₁' i).lift (Nat.le_max_left ..)).compat ((hρ₂ i).lift (Nat.le_max_right ..))
      have ⟨k, h1, (h2 : n₁ ≤ _), (h3 : _ ≤ x.1.lift)⟩ := bvar_iff.1 (hρ₁ 0)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha.mono_l hj2, fun i => ?_, List.forall_mem_cons.2 ?_⟩
      · exact ((hρ₁' i).lift (Nat.le_max_left ..)).join' ((hρ₂ i).lift (Nat.le_max_right ..))
      refine ⟨hy.mono_l ?_, fun _ h => (H _ h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)⟩
      rw [← (by funext i; cases i <;> rfl : ρ₁'.push (ρ₁ 0).2 = ρ₁)]
      exact (Valuation.LE.push' h1 h2).2 ⟨hj1, h3⟩
    | forallE B F ih_B ih_F =>
      cases H with
      | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
      | @forallE ρ n₁ b B b' f F n' m' hb hb' hdom hbody hle h1
      suffices ∃ ρ', LE_Interp ρ' b B ∧ LE_Interp ρ' b' B ∧ (∀ i, LE_Interp ρ (ρ' i).2 (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1) x.2 F by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) hle h1, hρ⟩
        obtain ⟨x', y', a1, a2, rfl⟩ := ShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2 F ∧ ∀ i, LE_Interp (ρ.push x.1) (ρ' i).snd (σ.lift i) :=
        ih_F (σ := σ.lift) (ShapeFun.app_of_mem h ▸ hbody _ (Shape.HasDom.def.1 hdom _ _ h))
      clear h1 hdom hbody
      induction f with
      | nil =>
        have ⟨ρ₁, hb, hρ₁⟩ := ih_B hb
        have ⟨ρ₂, hb', hρ₂⟩ := ih_B hb'
        have hc : ρ₁.Compat ρ₂ := fun i =>
          ((hρ₁ i).lift (Nat.le_max_left ..)).compat ((hρ₂ i).lift (Nat.le_max_right ..))
        have ⟨hj1, hj2⟩ := hc.le_join
        refine ⟨ρ₁.join ρ₂, hb.mono_l hj1, hb'.mono_l hj2, fun i => ?_, nofun⟩
        exact ((hρ₁ i).lift (Nat.le_max_left ..)).join' ((hρ₂ i).lift (Nat.le_max_right ..))
      | cons x f ih =>
        have ⟨⟨ρ₁, hy, hρ₁⟩, H⟩ := List.forall_mem_cons.1 H
        have ⟨ρ₂, hb₂, hb'₂, hρ₂, H⟩ := ih H
        let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
        have hρ₁' i : LE_Interp ρ (ρ₁' i).2 (σ i) := weak_iff.1 (hρ₁ (i + 1))
        have : ρ₁'.Compat ρ₂ := fun i =>
          ((hρ₁' i).lift (Nat.le_max_left ..)).compat ((hρ₂ i).lift (Nat.le_max_right ..))
        have ⟨k, h1, (h2 : n₁ ≤ _), (h3 : _ ≤ x.1.lift)⟩ := bvar_iff.1 (hρ₁ 0)
        have ⟨hj1, hj2⟩ := this.le_join
        refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2, fun i => ?_, List.forall_mem_cons.2 ?_⟩
        · exact ((hρ₁' i).lift (Nat.le_max_left ..)).join' ((hρ₂ i).lift (Nat.le_max_right ..))
        refine ⟨hy.mono_l ?_, fun _ h => (H _ h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)⟩
        rw [← (by funext i; cases i <;> rfl : ρ₁'.push (ρ₁ 0).2 = ρ₁)]
        exact (Valuation.LE.push' h1 h2).2 ⟨hj1, h3⟩
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 h2 h3 =>
      rename_i i
      exact ((h i).lift h1 |>.mono h3).unlift h2
    | app hf ha hle h1 ih_f ih_a =>
      exact .app (ih_f h) (ih_a h) hle h1
    | lam ha hdom hbody hle h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) hle h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | forallE hb hb' hdom hbody hle h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) hle h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak

theorem LE_Interp.inst : LE_Interp (n := n) ρ f (F.inst A) ↔
    ∃ m a, LE_Interp (n := n) (ρ.push a) f F ∧ LE_Interp (n := m) ρ a A := by
  refine ⟨fun H => ?_, fun ⟨_, a, hF, hA⟩ => ?_⟩
  · have ⟨ρ', hF, hσ⟩ := LE_Interp.subst.1 H
    refine ⟨_, _, hF.mono_l fun n m h1 h2 => ?_, hσ 0⟩
    cases n with | zero => exact .rfl | succ i
    have ⟨k, hk1, hk2, hk3⟩ := bvar_iff.1 (hσ (i+1))
    have := Shape.lift_mono (m := max k m) hk3
    rwa [Shape.lift_lift (.inl hk1), Shape.lift_lift (.inl hk2), ← Shape.lift_lift (.inl h1),
      ← Shape.lift_lift (.inl h2), Shape.lift_le_lift (Nat.le_max_right ..)] at this
  · exact (LE_Interp.subst (σ := .one A)).2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem LE_Interp.forallE_inv {b} {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.forallE b f) (.forallE B F)) :
    LE_Interp ρ b B ∧ ∀ {{X x}}, LE_Interp ρ x X → LE_Interp ρ (f.app x) (F.inst X) := by
  let .forallE hb₁ hb₂ hd hiB hle le := H
  simp [Shape.lift, Shape.LE.def] at le hle
  refine ⟨(hb₁.mono le.1).unlift hle, fun X x hx => ?_⟩
  obtain ⟨x', _, le1, hf, rfl⟩ := ShapeFun.app_eq f x
  obtain ⟨_, _, hf, le2, lf⟩ := ShapeFun.LE.def.1 le.2 _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  refine .inst.2 ⟨_, _, ?_, ((hx.mono le1).lift hle).mono le2⟩
  exact hiB _ (Shape.HasDom.def.1 hd _ _ hf)
    |>.mono (lf.trans (ShapeFun.app_of_mem hf ▸ .rfl)) |>.unlift hle

theorem LE_Interp.forallE_inv' {b} {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.forallE b f) (.forallE B F)) :
    LE_Interp ρ b B ∧ ∀ x, LE_Interp (ρ.push x) (f.app x) F := by
  have ⟨h1, h2⟩ := H.forallE_inv; refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x) H).forallE_inv.2
    (.bvar (i := 0) (Nat.le_refl _) (Nat.le_refl _) .rfl)
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.lam_inv {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.lam f) (.lam B F))
    {{X x}} (hx : LE_Interp ρ x X) : LE_Interp ρ (f.app x) (F.inst X) := by
  let .lam _ hd hiF hle le := H; simp at hle
  obtain ⟨x', _, le1, hf, rfl⟩ := ShapeFun.app_eq f x
  obtain ⟨_, _, hf, le2, lf⟩ := ShapeFun.LE.def.1 le _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  refine .inst.2 ⟨_, _, ?_, ((hx.mono le1).lift hle).mono le2⟩
  exact hiF _ (Shape.HasDom.def.1 hd _ _ hf)
    |>.mono (lf.trans (ShapeFun.app_of_mem hf ▸ .rfl)) |>.unlift hle

theorem LE_Interp.lam_inv' {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.lam f) (.lam B F)) (x) :
    LE_Interp (ρ.push x) (f.app x) F := by
  have := (LE_Interp.weak (x := x) H).lam_inv (.bvar (i := 0) (Nat.le_refl _) (Nat.le_refl _) .rfl)
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

inductive Valuation.Fits : (Γ Δ : List SExpr) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {n a}, LE_Interp (n := n) ρ a A →
      ∃ n' a', n ≤ n' ∧ a.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp (n := n) ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

def InterpTyped (ρ : Valuation) (m : Shape n) (M A : SExpr) :=
  ∃ n' m' a, n ≤ n' ∧ m.lift (m := n') ≤ m' ∧
    LE_Interp ρ m' M ∧ LE_Interp ρ a A ∧ m'.HasType a

theorem InterpTyped.mk (h1 : (m : Shape n) ≤ m') (h2 : LE_Interp ρ m' M)
    (h3 : LE_Interp ρ a A) (h4 : m'.HasType a) : InterpTyped ρ m M A :=
  ⟨_, _, _, Nat.le_refl _, Shape.lift_self.symm ▸ h1, h2, h3, h4⟩

theorem InterpTyped.bot : InterpTyped (n := n) ρ .bot M A :=
  .mk .rfl .bot .bot (.bot' <| .bot .sort)

theorem LE_Interp.sound_bot :
    (LE_Interp (n := n) ρ .bot M ↔ LE_Interp (n := n) ρ .bot N) ∧
    (LE_Interp (n := n) ρ .bot M → InterpTyped (n := n) ρ .bot M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem LE_Interp.sound_app
    (H1 : ∀ {n} {m : Shape n}, LE_Interp ρ m f → InterpTyped ρ m f (.forallE A B))
    (H2 : ∀ {n} {m : Shape n}, LE_Interp ρ m (B.inst a) →
      ∃ n' a', n ≤ n' ∧ m.lift (m := n') ≤ a' ∧ LE_Interp ρ a' (B.inst a) ∧ a'.HasType .type)
    {m : Shape n} (h1 : LE_Interp ρ m (f.app a pat)) :
    InterpTyped ρ m (f.app a pat) (B.inst a) := by
  by_cases hm : m = .bot; · exact hm ▸ .bot
  cases h1 with | bot => exact .bot | @app _ _ _ _ a _ _ _ h1 h2 h3' h3
  have ⟨n', f, s, le, a1, a2, a3, a4⟩ := H1 h1
  have hf : f ≠ .bot := fun h => by
    subst h; cases (Shape.lift_le_bot le).1 a1; cases hm ((Shape.lift_le_bot h3').1 h3)
  have hs : s ≠ .bot := fun h => by subst h; cases a4.bot_r; cases hf rfl
  cases a3 with | bot => cases hs rfl | @forallE _ _ _ _ _ _ _ _ s b1 b2 b3 b4 b5' b5
  let n'+1 := n'; simp at le b5'; have le₁ := Nat.le_trans h3' le
  cases s with simp [Shape.lift, Shape.LE.def] at b5 | bot => cases hs rfl | forallE
  cases a4.unfold with | bot => cases hf rfl | lam c1
  have ⟨_, d1, d2, d3⟩ := b3 a.lift
  have ⟨m', _, le', g1, g2, g3⟩ :=
    H2 (LE_Interp.inst.2 ⟨_, _, b4 _ d2, .mono d1 (h2.lift (Nat.le_trans le b5'))⟩)
  have le₂ := Nat.le_trans b5' le'
  have ⟨_, e1, e2, e3⟩ := c1.2.1 a.lift
  have := (c1.2.2 _ e2).mono_l (ShapeFun.app_mono_r e1) e3
  refine ⟨_, _, _, Nat.le_trans le₁ le₂, ?_, .lift le₂ (.app' a2 (h2.lift le)),
    g2, g3.mono_r ?_ ((Shape.HasType.lift le₂).2 this)⟩
  · refine Shape.lift_lift (.inl h3') ▸ .trans (Shape.lift_mono h3) ?_
    refine Shape.lift_lift (.inl le) ▸ Shape.lift_mono ?_
    exact Shape.lift_app ▸ Shape.app_mono_l a1 _
  · refine Shape.lift_lift (.inl b5') ▸ .trans (Shape.lift_mono (.trans ?_ d3)) g1
    refine .trans ?_ (ShapeFun.app_mono_r (Shape.lift_lift (.inl le) ▸ Shape.lift_mono e1))
    exact ShapeFun.lift_app b5' ▸ ShapeFun.app_mono_l b5.2 _

theorem LE_Interp.sound_lam
    (H1 : ∀ {n} {m : Shape n}, LE_Interp ρ m A →
      ∃ n' a', n ≤ n' ∧ m.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type)
    (H2 : ∀ {n} {a x : Shape n}, LE_Interp ρ a A → x.HasType a →
      ∀ {m} {e : Shape m}, LE_Interp (ρ.push x) e F → InterpTyped (ρ.push x) e F B)
    {m : Shape n} (h1 : LE_Interp ρ m (A.lam F)) : InterpTyped ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m = .bot; · exact hm ▸ .bot
  cases h1 with | bot => cases hm rfl | @lam _ n a _ f _ n' m h1 h2 h3 hle h4
  generalize eq : m.lift = m' at h4
  cases m' with simp [Shape.LE.def] at h4
  | bot => cases hm ((Shape.lift_eq_bot hle).1 eq) | lam f'
  have ⟨m', a', le, a1, a2, a3⟩ := H1 h1
  suffices ∃ n', n ≤ n' ∧ ∃ f' b : ShapeFun n', ShapeFun.LE (ShapeFun.lift Shape.lift f) f' ∧
      Shape.HasDom f' a.lift ∧ Shape.HasDom b a.lift ∧ ∀ x, x.HasType a.lift →
      LE_Interp (ρ.push x) (f'.app x) F ∧ LE_Interp (ρ.push x) (b.app x) B ∧
      (f'.app x).HasType (b.app x) by
    have ⟨n', le', f₁, b, a1, a2, a3, a4⟩ := this; simp [forall_and] at a4
    have h1' := h1.lift le'
    exact ⟨_+1, .lam f₁, _, Nat.le_trans hle (Nat.succ_le_succ le'),
      .trans (t := Shape.lift (n := _+1) (.lam f))
        (Shape.lift_lift (.inl hle) ▸ Shape.lift_mono (eq ▸ Shape.LE.def.2 h4)) a1,
      .lam' h1' a2 a4.1, .forallE' h1' h1' a3 a4.2.1,
      .lam ⟨⟨a3, fun _ h => (a4.2.2 _ h).isType⟩, a2, a4.2.2⟩⟩
  replace h3 (p) (h : p ∈ f) : p.1.HasType a ∧ LE_Interp (ρ.push p.1) p.2 F :=
    have := Shape.HasDom.def.1 h2 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h3 _ this⟩
  have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : ShapeFun k,
      f'.map Prod.fst = f.map (·.1.lift) ∧ b.map Prod.fst = f.map (·.1.lift) ∧
      ∀ x fx, (x, fx) ∈ f → ∃ f'x bx, (x.lift, f'x) ∈ f' ∧ (x.lift, bx) ∈ b ∧
      fx.lift ≤ f'x ∧ LE_Interp (ρ.push x) f'x F ∧ LE_Interp (ρ.push x) bx B ∧
      f'x.HasType bx := by
    clear h2 h4
    induction f with
    | nil => exact ⟨_, Nat.le_refl _, fun _ _ => ⟨[], [], by simp⟩⟩
    | cons p _ ih; let (x, fx) := p
    simp only [List.mem_cons, forall_eq_or_imp] at h3
    have ⟨k₁, le1, H1⟩ := ih h3.2
    have ⟨m', f'x, bx, le, b1, b2, b3, b4⟩ := H2 h1 h3.1.1 h3.1.2
    refine ⟨k₁.max m', Nat.le_trans le (Nat.le_max_right ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have ⟨f', b, a1, a2, a3⟩ := H1 _ le₁
    refine ⟨(x.lift, f'x.lift) :: f', (x.lift, bx.lift) :: b, ?_⟩
    simp [or_imp, forall_and, *]
    exact ⟨.inl (.inl ⟨Shape.lift_lift (.inl le) ▸ Shape.lift_mono b1,
      b2.lift le₂, b3.lift le₂, (Shape.HasType.lift le₂).2 b4⟩), by grind⟩
  have ⟨f', b, a1, a2, a3⟩ := H _ (Nat.le_refl _)
  refine ⟨_, le, f', b, ShapeFun.LE.def.2 fun _ _ h => ?_, ?_, ?_, fun x h => ?_⟩
  simp [ShapeFun.lift] at h; obtain ⟨_, _, h, rfl, rfl⟩ := h
  · have ⟨_, _, b1, _, b3, _⟩ := a3 _ _ h; exact ⟨_, _, b1, .rfl, b3⟩
  · refine Shape.HasDom.def.2 fun _ _ h => ?_
    obtain ⟨⟨_, _⟩, h1, ⟨⟩⟩ := List.mem_map.1 <| a1 ▸ List.mem_map.2 ⟨_, h, rfl⟩
    exact (Shape.HasType.lift le).2 <| Shape.HasDom.def.1 h2 _ _ h1
  · refine Shape.HasDom.def.2 fun _ _ h => ?_
    obtain ⟨⟨_, _⟩, h1, ⟨⟩⟩ := List.mem_map.1 <| a2 ▸ List.mem_map.2 ⟨_, h, rfl⟩
    exact (Shape.HasType.lift le).2 <| Shape.HasDom.def.1 h2 _ _ h1
  · have ⟨x₁, _, b1, b2, rfl⟩ := ShapeFun.app_eq f' x
    obtain ⟨⟨_, _⟩, b3, ⟨⟩⟩ := List.mem_map.1 <| a1 ▸ List.mem_map.2 ⟨_, b2, rfl⟩
    have ⟨x₂, _, b1', b2', rfl⟩ := ShapeFun.app_eq b x
    obtain ⟨⟨_, _⟩, b3', ⟨⟩⟩ := List.mem_map.1 <| a2 ▸ List.mem_map.2 ⟨_, b2', rfl⟩
    have ⟨_, _, c1, c2, c3, c4, c5, c6⟩ := a3 _ _ b3
    cases (ShapeFun.uniq_l b2 c1 .rfl .rfl).2
    refine ⟨?_, ?_, ?_⟩
    · exact c4.mono_l <| (Valuation.LE.push' le (Nat.le_refl _)).2
        ⟨.rfl, (Shape.lift_self (s := x)).symm ▸ b1⟩
    · have ⟨_, _, _, c2, _, _, c5, _⟩ := a3 _ _ b3'
      cases (ShapeFun.uniq_l b2' c2 .rfl .rfl).2
      exact c5.mono_l <| (Valuation.LE.push' le (Nat.le_refl _)).2
        ⟨.rfl, (Shape.lift_self (s := x)).symm ▸ b1'⟩
    · refine .mono_r (r := true) (ShapeFun.app_of_mem c2 ▸ ShapeFun.app_mono_r b1) ?_ c6
      have ⟨_, _, _, c2, _, _, c5, c6⟩ := a3 _ _ b3'
      cases (ShapeFun.uniq_l b2' c2 .rfl .rfl).2
      exact c6.isType

theorem LE_Interp.sound_forallE
    (H1 : ∀ {n} {m : Shape n}, LE_Interp ρ m A →
      ∃ n' a', n ≤ n' ∧ m.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (u ≠ .zero)))
    (H2 : ∀ {n} {a x : Shape n}, LE_Interp ρ a A → x.HasType a →
      ∀ {m} {e : Shape m}, LE_Interp (ρ.push x) e B → InterpTyped (ρ.push x) e B (.sort v))
    {m : Shape n} (h1 : LE_Interp ρ m (A.forallE B)) :
    InterpTyped ρ m (A.forallE B) (.sort (.imax u v)) := by
  by_cases hm : m = .bot; · exact hm ▸ .bot
  cases h1 with | bot => cases hm rfl | @forallE _ n b₀ _ b f _ _ m h1 h2 h3 h4 hle h5
  generalize eq : m.lift = m' at h5
  cases m' with simp [Shape.LE.def] at h5
  | bot => cases hm ((Shape.lift_eq_bot hle).1 eq) | forallE b' f'
  have ⟨b₁, a1, a2, a3⟩ := H1 h2
  suffices ∃ n', n ≤ n' ∧ ∃ f' : ShapeFun n', ShapeFun.LE (ShapeFun.lift Shape.lift f) f' ∧
      Shape.HasDom f' b.lift ∧ ∀ x, x.HasType b.lift →
      LE_Interp (ρ.push x) (f'.app x) B ∧ (f'.app x).HasType (.sort (v ≠ .zero)) by
    have ⟨n', le', f₁, b1, b2, b3⟩ := this; simp [forall_and] at b3
    have hJ := Shape.Join.mk (h1.compat h2)
    have ⟨m', b₂, le, c1, c2, c3⟩ := H1 (h1.join hJ h2)
    have le₁ := Nat.le_max_right n' m'
    have le₂ := Nat.le_max_left n' m'
    have hJ' := (Shape.Join.lift le).2 hJ
    have hJ₂ := (Shape.Join.lift (Nat.le_trans le le₁)).2 hJ
    have b2' := Shape.lift_lift (.inl le') ▸ (Shape.HasDom.lift le₂).2 b2
    refine ⟨n'.max m'+1, .forallE .., _,
      Nat.le_trans hle (Nat.succ_le_succ (Nat.le_trans le le₁)),
      Shape.lift_lift (.inl hle) ▸ eq ▸ Shape.LE.def.2 ⟨
        (Shape.lift_mono h5.1).trans (hJ₂.le.1.trans
          (Shape.lift_lift (.inl le) ▸ Shape.lift_mono c1)),
        .trans (ShapeFun.lift_mono h5.2)
          (ShapeFun.lift_lift (.inl le') ▸ ShapeFun.lift_mono b1)⟩,
      .forallE' (c2.lift le₁)
        ((h2.lift le').lift le₂)
        ((Shape.HasDom.lift le₂).2 b2) (fun x h => ?_),
      .sort .rfl,
      .forallE ⟨.mono (Shape.lift_mono <| hJ'.le.2.trans c1)
        (Shape.lift_type ▸ (Shape.HasType.lift le₁).2 c3.toType)
        ((Shape.lift_lift (.inl le)).symm ▸ b2'), fun x h => ?_⟩⟩
    · refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq ..; d3 ▸ ?_
      simp [ShapeFun.lift] at d2; obtain ⟨_, _, d2, rfl, rfl⟩ := d2
      have := ShapeFun.app_of_mem d2 ▸ b3.1 _ (Shape.HasDom.def.1 b2 _ _ d2)
      refine (this.mono_l ?_).lift le₂
      exact (Valuation.LE.push' le₂ (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ d1⟩
    · have ⟨y, d1, d2, d3⟩ := b2' x
      refine have ⟨_, _, e1, e2, e3⟩ := ShapeFun.app_eq _ y; have d3' := e3 ▸ d3; ?_
      simp [ShapeFun.lift] at e2; obtain ⟨_, _, e2, rfl, rfl⟩ := e2
      refine .mono_l (ShapeFun.app_mono_r d1) d3 <|
        e3 ▸ Shape.lift_sort.symm ▸ (Shape.HasType.lift le₂).2 ?_
      simpa [← ShapeFun.app_of_mem e2] using b3.2 _ (Shape.HasDom.def.1 b2 _ _ e2)
  replace h4 (p) (h : p ∈ f) : p.1.HasType b ∧ LE_Interp (ρ.push p.1) p.2 B :=
    have := Shape.HasDom.def.1 h3 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h4 _ this⟩
  have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : ShapeFun k,
      f'.map Prod.fst = f.map (·.1.lift) ∧
      ∀ x fx, (x, fx) ∈ f → ∃ f'x, (x.lift, f'x) ∈ f' ∧
      fx.lift ≤ f'x ∧ LE_Interp (ρ.push x) f'x B ∧ f'x.HasType (.sort (v ≠ .zero)) := by
    clear h3 h5
    induction f with
    | nil => exact ⟨_, Nat.le_refl _, fun _ _ => ⟨[], by simp⟩⟩
    | cons p _ ih; let (x, fx) := p
    simp only [List.mem_cons, forall_eq_or_imp] at h4
    have ⟨k₁, le1, H1⟩ := ih h4.2
    have ⟨m', f'x, bx, le, b1, b2, b3, b4⟩ := H2 h2 h4.1.1 h4.1.2
    refine ⟨k₁.max m', Nat.le_trans le (Nat.le_max_right ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have ⟨f', a1, a2⟩ := H1 _ le₁
    refine ⟨(x.lift, f'x.lift) :: f', ?_⟩
    replace b4 : f'x.HasType (.sort (v ≠ .zero)) := by
      cases b3 with
      | sort h => exact .mono_r h .sort b4
      | bot => cases b4.bot_r; exact .bot .sort
    simp [or_imp, forall_and, *] at b4 ⊢
    exact ⟨.inl ⟨Shape.lift_lift (.inl le) ▸ Shape.lift_mono b1, b2.lift le₂,
      Shape.lift_sort ▸ (Shape.HasType.lift le₂).2 b4⟩, by grind⟩
  have ⟨f', a1, a2⟩ := H _ (Nat.le_refl _)
  refine ⟨_, le, f', ShapeFun.LE.def.2 fun _ _ h => ?_, ?_, fun x h => ?_⟩
  · simp [ShapeFun.lift] at h; obtain ⟨_, _, h, rfl, rfl⟩ := h
    have ⟨_, b1, b2, _⟩ := a2 _ _ h; exact ⟨_, _, b1, .rfl, b2⟩
  · refine Shape.HasDom.def.2 fun _ _ h => ?_
    obtain ⟨⟨_, _⟩, h1, ⟨⟩⟩ := List.mem_map.1 <| a1 ▸ List.mem_map.2 ⟨_, h, rfl⟩
    exact (Shape.HasType.lift le).2 <| Shape.HasDom.def.1 h3 _ _ h1
  · have ⟨x₁, _, b1, b2, rfl⟩ := ShapeFun.app_eq f' x
    obtain ⟨⟨_, _⟩, b3, ⟨⟩⟩ := List.mem_map.1 <| a1 ▸ List.mem_map.2 ⟨_, b2, rfl⟩
    have ⟨_, c1, c2, c3, c4⟩ := a2 _ _ b3
    cases (ShapeFun.uniq_l b2 c1 .rfl .rfl).2
    refine ⟨c3.mono_l ?_, c4⟩
    exact (Valuation.LE.push' le (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ b1⟩

theorem LE_Interp.sound (H : Γ ⊢ M ≡ N : A)
    (W : Valuation.Fits Γ₀ Γ ρ) {m : Shape n} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧
    (LE_Interp ρ m M → InterpTyped ρ m M A) := by
  have hsort' {ρ A U}
      (H : ∀ {n a}, LE_Interp (n := n) ρ a A → InterpTyped (n := n) ρ a A (.sort U))
      {n a} (h : LE_Interp (n := n) ρ a A) :
      ∃ n' a', n ≤ n' ∧ a.lift (m := n') ≤ a' ∧
        LE_Interp ρ a' A ∧ a'.HasType (.sort (U ≠ .zero)) := by
    have ⟨n', a', u', le, h1, h2, h3, h4⟩ := H h; refine ⟨_, _, le, h1, h2, ?_⟩
    cases h3 with | bot => cases h4.bot_r; exact .bot .sort | sort h3
    obtain rfl | rfl := Shape.le_sort.1 h3; · cases h4.bot_r; exact .bot .sort
    exact h4
  have hsort {ρ A U}
      (H : ∀ {n a}, LE_Interp (n := n) ρ a A → InterpTyped (n := n) ρ a A (.sort U))
      {n a} (h : LE_Interp (n := n) ρ a A) :
      ∃ n' a', n ≤ n' ∧ a.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type :=
    have ⟨n', a', le, h1, h2, h3⟩ := hsort' H h; ⟨_, _, le, h1, h2, h3.toType⟩
  replace H := H.strong
  induction H generalizing n m ρ with
  | @bvar _ i A h =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.bvar i = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot' <| .bot .sort)
    | bvar a1 a2 a3
    induction W generalizing i A with
    | nil => cases (Shape.lift_le_bot a2).1 a3; exact .mk .rfl .bot .bot (.bot' <| .bot .sort)
    | cons h1 h2 h3 h4 ih =>
      cases h with simp [Valuation.push] at a1 a2
      | zero =>
        exact ⟨_, _, _, a2, a3, .bvar a1 (Nat.le_refl _) (by rw [Shape.lift_self]; exact .rfl),
          h3.weak.lift a1, (Shape.HasType.lift a1).2 h4⟩
      | succ h =>
        have ⟨_, _, _, le, h1, h2, h3, h4⟩ := ih h a1 a3
        exact ⟨_, _, _, le, h1, h2.weak, h3.weak, h4⟩
  | symm _ ih =>
    refine ⟨(ih W).1.symm, fun h => ?_⟩
    have ⟨_, _, _, le, a1, a2, a3⟩ := (ih W).2 ((ih W).1.2 h)
    exact ⟨_, _, _, le, a1, (ih W).1.1 a2, a3⟩
  | trans _ _ _ _ ih1 ih2 =>
    refine ⟨(ih1 W).1.trans (ih2 W).1, fun h => ?_⟩
    have ⟨_, _, _, le, a1, a2, a3⟩ := (ih2 W).2 ((ih1 W).1.1 h)
    exact ⟨_, _, _, le, a1, (ih1 W).1.2 a2, a3⟩
  | @sort _ l =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.sort l = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot' <| .bot .sort)
    | sort h1 => exact .mk h1 (.sort .rfl) (.sort .rfl) (by simpa using .sort)
  | @const c _ _ ls =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.const c ls = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot' <| .bot .sort)
  | appDF _ _ _ _ _ ihA ihB ih1 ih2 ih3 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, sound_app (ih1 W).2 (hsort (ih3 W).2)⟩ <;>
      cases h with | bot => cases hm rfl | app h1 h2 hle h3
    · exact .app ((ih1 W).1.1 h1) ((ih2 W).1.1 h2) hle h3
    · exact .app ((ih1 W).1.2 h1) ((ih2 W).1.2 h2) hle h3
  | @lamDF _ _ _ _ B _ body body' _ _ _ ih1 _ ih2 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_lam (hsort (ih1 W).2) fun h1 h2 => (ih2 (W.cons (hsort (ih1 W).2) h1 h2)).2⟩ <;>
      cases h with | bot => cases hm rfl | @lam _ n a _ f _ n' m h1 h2 h3 hle h4
    · refine .lam ((ih1 W).1.1 h1) h2 (fun _ h => ?_) hle h4
      exact (ih2 (W.cons (hsort (ih1 W).2) h1 h)).1.1 (h3 _ h)
    · refine .lam ((ih1 W).1.2 h1) h2 (fun _ h => ?_) hle h4
      exact (ih2 (W.cons (hsort (ih1 W).2) ((ih1 W).1.2 h1) h)).1.2 (h3 _ h)
  | @forallEDF _ A _ _ body body' v _ _ ih1 ih2 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_forallE (hsort' (ih1 W).2) fun h1 h2 => (ih2 (W.cons (hsort (ih1 W).2) h1 h2)).2⟩ <;>
      try cases h with | bot => cases hm rfl | @forallE _ n b₀ _ b f _ _ m h1 h2 h3 h4 hle h5
    · refine .forallE ((ih1 W).1.1 h1) ((ih1 W).1.1 h2) h3 (fun _ h => ?_) hle h5
      exact (ih2 (W.cons (hsort (ih1 W).2) h2 h)).1.1 (h4 _ h)
    · refine .forallE ((ih1 W).1.2 h1) ((ih1 W).1.2 h2) h3 (fun _ h => ?_) hle h5
      exact (ih2 (W.cons (hsort (ih1 W).2) ((ih1 W).1.2 h2) h)).1.2 (h4 _ h)
  | defeqDF _ _ ih1 ih2 =>
    refine ⟨(ih2 W).1, fun h => ?_⟩
    have ⟨_, _, _, le, h1, h2, h3, h4⟩ := (ih2 W).2 h
    exact ⟨_, _, _, le, h1, h2, (ih1 W).1.1 h3, h4⟩
  | beta _ _ _ _ ih1 ih2 ih3 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih3 W).2⟩
    · cases h with | bot => cases hm rfl | app h1 h2 hle h3
      cases h1 with | bot => cases hm ((Shape.lift_le_bot hle).1 h3) | lam h4 h5 h6 hle' h7
      simp at hle'
      have ⟨_, _, a1, a2, a3, a4⟩ := (ih2 W).2 h2
      refine have ⟨_, b1, b2, b3⟩ := h5 _; LE_Interp.inst.2 ⟨_, _, ?_, (h2.lift hle').mono b1⟩
      exact .unlift hle <| .mono h3 <| .unlift hle' <| Shape.lift_app ▸
         ((h6 _ b2).mono b3).mono (Shape.app_mono_l h7 _)
    · have ⟨n', _, h1, h2⟩ := LE_Interp.inst.1 h
      have ⟨_, _, _, le, a1, a2, a3, a4⟩ := (ih2 W).2 <| h2.lift (Nat.le_max_right n n')
      have le' := Nat.max_le.1 le
      refine .unlift le'.1 <| .mono ?_ <|
        .app' (.lam' a3 ((Shape.HasDom.single (y := m.lift)).2 a4) (fun _ h => ?_)) a2
      · rw [Shape.app, ShapeFun.single_app, if_pos .rfl]; exact .rfl
      simp [ShapeFun.single_app]; split <;> [skip; exact .bot]
      refine .lift le'.1 <| h1.mono_l ?_
      refine (Valuation.LE.push' le'.2 (Nat.le_refl _)).2
        ⟨.rfl, .trans (Shape.lift_lift (.inl (Nat.le_max_right ..)) ▸ a1) ?_⟩
      rwa [Shape.lift_self]
  | @eta _ F _ _ _ _ ih1 ih2 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih2 W).2⟩
    · have ⟨_, e, t, le, h1, h2, h3, h4⟩ := (ih2 W).2 h
      have ht : t ≠ .bot := fun h => by
        subst h; cases h4.bot_r; cases hm ((Shape.lift_le_bot le).1 h1)
      cases h2 with
      | bot => cases hm ((Shape.lift_le_bot le).1 h1)
      | @lam _ n _ _ f' _ _ _ a1 a2 a3 a4' a4
      cases h3 with | bot => cases ht rfl | @forallE _ _ _ _ _ _ _ _ _ b1 b2 b3 b4 b5' b5
      generalize eq : t.lift = t' at b5
      cases t' with simp [Shape.LE.def] at b5
      | bot => cases ht ((Shape.lift_eq_bot b5').1 eq) | forallE a' b'
      have h4' := eq ▸ (Shape.HasType.lift b5').2 h4
      generalize eq' : e.lift = e' at h4'
      cases h4'.unfold with
      | bot => cases (Shape.lift_eq_bot b5').1 eq'; cases hm ((Shape.lift_le_bot le).1 h1)
      | @lam _ f _ _ d1
      have key : ∀ x y, (x, y) ∈ f' → y ≠ .bot →
          LE_Interp (n := n+1) ρ (ShapeS.lam (ShapeFun.single x y)) F := by
        intro x y hmem hy
        have := ShapeFun.app_of_mem hmem ▸ a3 x (Shape.HasDom.def.1 a2 _ _ hmem)
        cases this with | bot => cases hy rfl | @app _ _ f_s _ a_s _ _ _ c1 c2 c2le c3
        cases f_s with | lam g => ?_ | _ => cases hy ((Shape.lift_le_bot c2le).1 c3)
        refine .unlift (Nat.succ_le_succ c2le) <| .mono ?_ (LE_Interp.weak_iff.1 c1)
        simp [Shape.lift, Shape.LE.def, ShapeFun.lift_single c2le, ShapeFun.single_le]
        have ⟨k', le₁, _, hle⟩ := LE_Interp.bvar_iff.1 c2
        have ha_s := (Shape.lift_le_lift le₁).1 ((Shape.lift_lift (.inl c2le)).symm ▸ hle)
        have ⟨x'', y'', hle₁, hmemg, happ⟩ := ShapeFun.app_eq g a_s
        simp [Shape.app, happ] at c3
        exact ⟨_, _, hmemg, .trans hle₁ ha_s, c3⟩
      have main (l : List (Shape n × Shape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g : Shape (n+1),
            (g = .bot ∨ ∃ l, g = .lam l) ∧
            (∀ z, g ≤ z ↔ ∀ x y, (x, y) ∈ l → y ≠ .bot → .lam (ShapeFun.single x y) ≤ z) ∧
            LE_Interp (n := _+1) ρ g F := by
        induction l with | nil => exact ⟨.bot, .inl rfl, by simp, .bot⟩ | cons p l ih
        let (x, y) := p; simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, eq, a1, a2⟩ := ih H.2
        by_cases hy : y = .bot
        · exact ⟨g, eq, fun z => (a1 z).trans (by simp [or_imp, forall_and, hy]), a2⟩
        · have := Shape.Join.mk (x := g) (y := .lam (ShapeFun.single x y)) <| by
            obtain rfl | ⟨g, rfl⟩ := eq; · simp [Shape.Compat]
            refine Shape.Compat.def.2 ⟨.lam f', ?_, ?_⟩
            · exact (a1 _).2 fun _ _ h _ => ShapeFun.single_le.2 ⟨_, _, H.2 _ h, .rfl, .rfl⟩
            · exact ShapeFun.single_le.2 ⟨_, _, H.1, .rfl, .rfl⟩
          refine ⟨_, .inr ?_, fun z => (this z).trans ?_, .join this a2 (key _ _ H.1 hy)⟩
          · obtain rfl | ⟨g, rfl⟩ := eq <;> exact ⟨_, rfl⟩
          · simp [a1, or_imp, forall_and, and_comm, hy]
      have ⟨g, _, a1, a2⟩ := main f' (fun _ => id)
      refine .unlift le <| .mono h1 <| .unlift a4' <| .mono a4 <| .mono ?_ a2
      have ⟨x, y, hmem, hy⟩ := f'.non_bot
      obtain ⟨g, rfl⟩ : ∃ g', g = .lam g' := by
        have := (a1 _).1 .rfl _ _ hmem hy
        cases g <;> simp [Shape.LE.def] at this; exact ⟨_, rfl⟩
      simp [Shape.LE.def, ShapeFun.LE.def]
      intro x' y' hmem
      by_cases hy : y' = .bot
      · have ⟨_, hmem⟩ := ShapeFun.bot_mem g
        exact ⟨_, _, hmem, Shape.bot_le, hy ▸ Shape.bot_le⟩
      · simpa [Shape.LE.def, ShapeFun.single_le] using (a1 _).1 .rfl _ _ hmem hy
    · have ⟨n', m', f, le, a1, a2, a3, a4⟩ := (ih1 W).2 h
      have hf : f ≠ .bot := fun h => by
        subst h; cases a4.bot_r; cases hm ((Shape.lift_le_bot le).1 a1)
      cases a3 with | bot => cases hf rfl | @forallE _ _ _ _ _ _ _ _ _ b1 b2 b3 b4 b4le b5
      cases n' <;> cases f <;> simp [Shape.lift, Shape.LE.def] at b5 <;> try cases hf rfl
      simp at b4le
      cases a4.unfold with | bot => cases hm ((Shape.lift_le_bot le).1 a1) | lam d1
      refine .unlift le <| .mono a1 <|
        .lam' ((b1.mono b5.1).unlift b4le) d1.2.1 fun _ h => .app' a2.weak .bvar0
  | @proofIrrel _ p h h' _ _ _ ih1 ih2 ih3 =>
    suffices ∀ {h h'}, InterpTyped ρ m h p → LE_Interp ρ m h → LE_Interp ρ m h' from
      ⟨⟨fun h => this ((ih2 W).2 h) h, fun h => this ((ih3 W).2 h) h⟩, (ih2 W).2⟩
    refine fun ⟨_, _, _, le, a1, a2, a3, a4⟩ h1 => (?_ : m = .bot) ▸ .bot
    have ⟨_, _, _, le', b1, b2, b3, b4⟩ := (ih1 W).2 a3
    have b4' := Shape.HasType.mono_r (by simpa using b3.le_sort) .sort b4
    cases (Shape.lift_eq_bot le').1 (b4'.proofIrrel (b4'.mono_r b1 ((Shape.HasType.lift le').2 a4)))
    exact (Shape.lift_le_bot le).1 a1
  | extra => sorry

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  /-- Term validity: `M ≡ N : A` at element-shape `m` and type-shape `a`. -/
  DefEq (M N A : SExpr) (m a : Shape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at type-shape `a`. -/
  TyDefEq (A B : SExpr) (a : Shape n) : Prop

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  sort_iff : DefEq M N A (.sort r) (.sort r') ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  sort_iff_ty : TyDefEq M N (.sort r) ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  bot : a.HasType .type → DefEq M N A .bot a
  toType : DefEq M N A m (.sort r) → TyDefEq M N m
  left : DefEq M N A m a → DefEq M M A m a
  left_ty : TyDefEq M N m → TyDefEq M M m
  symm : DefEq M N A m a → DefEq N M A m a
  symm_ty : TyDefEq M N m → TyDefEq N M m
  trans : DefEq M₁ M₂ A m a → DefEq M₂ M₃ A m a → DefEq M₁ M₃ A m a
  trans_ty : TyDefEq M₁ M₂ m → TyDefEq M₂ M₃ m → TyDefEq M₁ M₃ m
  conv : TyDefEq A B a → DefEq M N A m a → DefEq M N B m a
  mono_r_2 : a ≤ a' → m.HasType a → a'.HasType .type → DefEq M N A m a' → DefEq M N A m a
  mono_r_2_ty : a ≤ a' → a.HasType .type → a'.HasType .type → TyDefEq A B a' → TyDefEq A B a
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → TyDefEq A A a' → DefEq M N A m a → DefEq M N A m a'
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → DefEq M N A m' a → DefEq M N A m a
  join_ty : m₁.Compat m₂ → m₁.HasType .type → m₂.HasType .type →
    TyDefEq A B m₁ → TyDefEq A B m₂ → TyDefEq A B (m₁.join m₂)
  whr : Γ ⊢ M ⤳* M' → Γ ⊢ N ⤳* N' → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty : Γ ⊢ A ⤳* A' → Γ ⊢ B ⤳* B' → (TyDefEq A B m ↔ TyDefEq A' B' m)

theorem LogRelBase.TyDefEq.sort {R : LogRel Γ n} : R.TyDefEq (.sort u) (.sort u) (.sort r) :=
  R.toType (A := default) (r := default) (R.sort_iff.2 ⟨_, .rfl, .rfl⟩)

/-! #### Concrete definitions at level 0 -/

def LR0.TyDefEq (Γ : List SExpr) (M N : SExpr) : Shape 0 → Prop
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u

def LR0.DefEq (Γ : List SExpr) (M N : SExpr) (m a : Shape 0) : Prop :=
  match a with
  | .bot => True
  | .sort _ => LR0.TyDefEq Γ M N m

def LR0 : LogRel Γ 0 where
  DefEq M N _ := LR0.DefEq Γ M N
  TyDefEq := LR0.TyDefEq Γ
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot {_ _ _ a} _ := by cases a <;> trivial
  toType := id
  left {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  left_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  symm {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  symm_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  trans_ty {M₁ M₂ m M₃} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  conv _ := id
  mono_r_2 {a a' _ _ _ _} le _ _ := by cases a <;> cases a' <;> simp [LR0.DefEq]; cases le
  mono_r_2_ty {a a' _ _} le _ _ := by cases a <;> cases a' <;> simp [LR0.TyDefEq]; cases le
  mono_r_1 {a a' _ _ _ b} le h1 _ h2 := by
    cases a <;> cases a' <;> (try exact id) <;> [cases h1.bot_r; cases le]; exact id
  mono_l {m m' M N A a} le _ _ := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    cases m <;> cases m' <;> (try exact id) <;> [exact fun _ => trivial; cases le]
  join_ty {A B m₁ m₂} hC hm₁ hm₂ := by
    cases m₁ <;> cases m₂ <;> simp [LR0.TyDefEq, Shape.join]
    simp [Shape.Compat] at hC; subst hC; simp; grind
  whr {M M' N N' A m a} hM hN := by
    dsimp [LR0.DefEq]; split <;> [exact .rfl; skip]
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
    · exact ⟨u, .trans hM r1, .trans hN r2⟩
  whr_ty {A A' B B' m} hA hB := by
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
    · exact ⟨u, .trans hA r1, .trans hB r2⟩

/-! #### Concrete definitions at level n+1 -/

/-- Pi edge validity (merged `PiEdgeDefEq` / `PiEdgeEq2`).
For each argument `a ≡ b : A₁`, the substituted codomains are valid types.
For each argument `a : A₁`, the codomains `A₂[a]` and `B₂[a]` are equal types. -/
def LRS.PiDefEq (IH : LogRel Γ n)
    (B F₁ F₂ : SExpr) (b : Shape n) (f : ShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → Γ ⊢ a ≡ b' : B → IH.DefEq a b' B p b →
    IH.TyDefEq (F₁.inst a) (F₁.inst b') (ShapeFun.app f p) ∧
    IH.TyDefEq (F₂.inst a) (F₂.inst b') (ShapeFun.app f p)) ∧
  ∀ {{a p}}, p.HasType b → Γ ⊢ a : B → IH.DefEq a a B p b →
    IH.TyDefEq (F₁.inst a) (F₂.inst a) (ShapeFun.app f p)

theorem LRS.PiDefEq.left {IH : LogRel Γ n} :
    LRS.PiDefEq IH B F₁ F₂ b f → LRS.PiDefEq IH B F₁ F₁ b f
  | ⟨h1, _⟩ => ⟨fun _ _ _ hp ha a1 => ⟨(h1 hp ha a1).1, (h1 hp ha a1).1⟩,
                 fun _ _ hp ha a1 => (h1 hp ha a1).1⟩

def LRS.ValTyPi2 (IH : LogRel Γ n) (M₁ M₂ : SExpr) (b : Shape n) (f : ShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂ u v,
    Γ ⊢ M₁ ⤳* .forallE B₁ F₁ ∧ Γ ⊢ M₂ ⤳* .forallE B₂ F₂ ∧
    Γ ⊢ B₁ ≡ B₂ : .sort u ∧ B₁::Γ ⊢ F₁ ≡ F₂ : .sort v ∧ IH.TyDefEq B₁ B₂ b ∧
    LRS.PiDefEq IH B₁ F₁ F₂ b f

def LRS.LamDefEq (IH : LogRel Γ n)
    (M N A₁ A₂ : SExpr) (m : ShapeFun n) (a₁ : Shape n) (a₂ : ShapeFun n) : Prop :=
  (∀ {{a b p}}, p.HasType a₁ → Γ ⊢ a ≡ b : A₁ → IH.DefEq a b A₁ p a₁ →
    IH.DefEq (M.app a) (M.app b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) ∧
    IH.DefEq (N.app a) (N.app b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p)) ∧
  (∀ {{a p}}, p.HasType a₁ → Γ ⊢ a : A₁ → IH.DefEq a a A₁ p a₁ →
    IH.DefEq (M.app a) (N.app a) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p))

/-- Monotonicity of `LamDefEq` in the type-shape: increase. -/
theorem LRS.LamDefEq.mono_r_1 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂.LE a₂') (hm : Shape.HasTypeLam m a₁ a₂)
    (hm' : Shape.HasTypeLam m a₁' a₂') (piEV : LRS.PiDefEq IH A₁ A₂ A₂ a₁' a₂') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' := by
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ x hx ha a1 => ?_, fun _ x hx ha a1 => ?_⟩
  all_goals
    have ⟨x', le', hax, h1⟩ := hm.2.1 x
    have hax' := Shape.HasType.mono_r le₁ hx.isType hax
    have a1_x := IH.mono_l le' hax' hx a1
    have a1_down := IH.mono_r_2 le₁ hax hx.isType a1_x
    have hg_x := hm.2.2 x' hax
    have hg_p := hg_x.mono_l (ShapeFun.app_mono_r le') h1
    have le_cod := (ShapeFun.app_mono_r le').trans (ShapeFun.app_mono_l le₂ _)
    have ht_cod := hm'.1.2 x hx
    have hm_target := Shape.HasType.mono_r le_cod ht_cod hg_p
  · have ⟨p1, p2⟩ := pav hax ha a1_down
    have tyA₂ := (piEV.1 hx ha.hasType.1 (IH.left a1)).1
    exact ⟨IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p1),
           IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p2)⟩
  · have q := pae hax ha a1_down
    have tyA₂ := piEV.2 hx ha a1
    exact IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x q)

/-- Type validity at element-shape `m` (merged `TyDefEq` / `EqTyDefEq`).
Non-trivial at `.forallE` (Pi injectivity) and `.sort` (sort injectivity). -/
def LRS.TyDefEq (IH : LogRel Γ n) (M N : SExpr) : Shape (n+1) → Prop
  | .bot | .lam _ => True
  | .sort _ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  | .forallE b f => LRS.ValTyPi2 IH M N b f

theorem LRS.TyDefEq.left {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH M M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  · intro ⟨B₁, F₁, _, _, u, v, rM, _, hB, hF, hValB, hE⟩
    exact ⟨B₁, F₁, B₁, F₁, u, v, rM, rM, hB.hasType.1, hF.hasType.1, IH.left_ty hValB, hE.left⟩

theorem LRS.TyDefEq.symm {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH N M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  · intro ⟨_, _, _, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩
    have hValB' := IH.symm_ty hValB
    refine ⟨_, _, _, _, _, _, rN, rM, hB.symm, hB.defeqDF_l hF.symm,
      hValB', fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact (hE1 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1)).symm
    · exact IH.symm_ty (hE2 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1))

theorem LRS.TyDefEq.trans {IH : LogRel Γ n} :
    LRS.TyDefEq IH M₁ M₂ m → LRS.TyDefEq IH M₂ M₃ m → LRS.TyDefEq IH M₁ M₃ m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM₁, hM₂⟩ ⟨u', hM₂', hM₃⟩
    cases hM₂.determ .sort hM₂' .sort; exact ⟨u, hM₁, hM₃⟩
  · intro ⟨B₁, F₁, B₂, F₂, u, v, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩
          ⟨_, _, B₃, F₃, u', v', rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩
    cases rM₂.determ .forallE rM₂' .forallE
    have hF₂₃' := hB₁₂.symm.defeqDF_l hF₂₃
    cases hB₁₂.uniq_sort hB₂₃
    cases hF₁₂.uniq_sort hF₂₃'
    refine ⟨_, _, _, _, _, _, rM₁, rM₃, hB₁₂.trans hB₂₃, hF₁₂.trans hF₂₃',
      IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact ⟨(hE1.1 hp ha a1).1, (hE2.1 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1)).2⟩
    · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1))

theorem LRS.LamDefEq.left {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LRS.LamDefEq.symm {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH N M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩
  · exact IH.symm (hP.2 hp ha a1)

theorem LRS.LamDefEq.trans {IH : LogRel Γ n} :
    LRS.LamDefEq IH M₁ M₂ B F m m₁ m₂ →
    LRS.LamDefEq IH M₂ M₃ B F m m₁ m₂ → LRS.LamDefEq IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · exact IH.trans (hP2 hp ha a1) (hP2' hp ha a1)

theorem LRS.PiDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : b.LE b') (le₂ : ShapeFun.LE f f')
    (htpi : Shape.HasTypePi f b r) (htpi' : Shape.HasTypePi f' b' r')
    (hValA₁ : IH.TyDefEq A₁ A₁ b') :
    LRS.PiDefEq IH A₁ A₂ B₂ b' f' → LRS.PiDefEq IH A₁ A₂ B₂ b f
  | ⟨h1, h2⟩ => by
    refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
    all_goals
      have hp' := Shape.HasType.mono_r le₁ htpi'.1.isType hp
      have a2 := IH.mono_r_1 le₁ hp hp' hValA₁ a1
      have hm_tgt := (htpi.2 _ hp).toType; have hm_src := (htpi'.2 _ hp').toType
    · let ⟨t1, t2⟩ := h1 hp' ha a2
      exact ⟨IH.mono_r_2_ty (ShapeFun.app_mono_l le₂ x) hm_tgt hm_src t1,
             IH.mono_r_2_ty (ShapeFun.app_mono_l le₂ x) hm_tgt hm_src t2⟩
    · exact IH.mono_r_2_ty (ShapeFun.app_mono_l le₂ x) hm_tgt hm_src (h2 hp' ha a2)

theorem LRS.LamDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : a₁.LE a₁') (le₂ : a₂.LE a₂') (hm : Shape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.TyDefEq A₁ A₁ a₁') (htpi' : Shape.HasTypePi a₂' a₁' r') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  intro ⟨h1, h2⟩
  refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
  all_goals
    have hp' := Shape.HasType.mono_r le₁ htpi'.1.isType hp
    have a1' := IH.mono_r_1 le₁ hp hp' hValA₁ a1
    have hm_tgt := hm.2.2 _ hp
    have ht_src := (htpi'.2 _ hp').toType
  · have ⟨d1, d2⟩ := h1 hp' ha a1'
    exact ⟨IH.mono_r_2 (ShapeFun.app_mono_l le₂ x) hm_tgt ht_src d1,
           IH.mono_r_2 (ShapeFun.app_mono_l le₂ x) hm_tgt ht_src d2⟩
  · have q := h2 hp' ha a1'
    exact IH.mono_r_2 (ShapeFun.app_mono_l le₂ _) hm_tgt ht_src q

/-- Monotonicity of `LamDefEq` in the element-shape: decrease. -/
theorem LRS.LamDefEq.mono_l {IH : LogRel Γ n}
    (le : m.LE m') (hm : Shape.HasTypeLam m a₁ a₂)
    (hm' : Shape.HasTypeLam m' a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ m' a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  all_goals
    have hm_tgt := hm.2.2 _ hp
    have hm_src := hm'.2.2 _ hp
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨IH.mono_l (ShapeFun.app_mono_l le _) hm_tgt hm_src d1,
           IH.mono_l (ShapeFun.app_mono_l le _) hm_tgt hm_src d2⟩
  · have q := pae hp ha a1
    exact IH.mono_l (ShapeFun.app_mono_l le _) hm_tgt hm_src q

/-- Join of `PiDefEq`: given edge validity at `(b₁, f₁)` and `(b₂, f₂)`,
produce edge validity at `(b₁.join b₂, f₁.join f₂)`.
Follows the same representative-based strategy as old `LRS.join`. -/
theorem LRS.PiDefEq.join {IH : LogRel Γ n}
    (htB₁ : b₁.HasType .type) (htB₂ : b₂.HasType .type) (hC_b : b₁.Compat b₂)
    (ht₁ : Shape.HasTypePi f₁ b₁ r₁) (ht₂ : Shape.HasTypePi f₂ b₂ r₂)
    (hC_f : ShapeFun.Compat Shape.Compat f₁ f₂)
    (hE₁ : LRS.PiDefEq IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LRS.PiDefEq IH B₁ F₁ F₂ b₂ f₂) :
    LRS.PiDefEq IH B₁ F₁ F₂ (b₁.join b₂) (ShapeFun.join Shape.join f₁ f₂) := by
  have hJ_b := Shape.Join.mk hC_b
  have htB_join := Shape.HasType.join hJ_b htB₁ htB₂
  have hJ_f := ShapeFun.Join.mk hC_f
  refine ⟨fun _ _ p hp ha a1 => ?_, fun _ p hp ha a1 => ?_⟩
  all_goals
    obtain ⟨_, _, d1, d2, rfl⟩ := ShapeFun.app_eq f₁ p
    have d3 := Shape.HasDom.def.1 ht₁.1 _ _ d2
    have c2 := IH.mono_r_2 hJ_b.le.1 d3 htB_join
      (IH.mono_l d1 (Shape.HasType.mono_r hJ_b.le.1 htB_join d3) hp a1)
    obtain ⟨_, _, e1, e2, rfl⟩ := ShapeFun.app_eq f₂ p
    have e3 := Shape.HasDom.def.1 ht₂.1 _ _ e2
    have c3 := IH.mono_r_2 hJ_b.le.2 e3 htB_join
      (IH.mono_l e1 (Shape.HasType.mono_r hJ_b.le.2 htB_join e3) hp a1)
    have ht_f1 := (ShapeFun.app_of_mem d2 ▸ ht₁.2 _ d3).toType
    have ht_f2 := (ShapeFun.app_of_mem e2 ▸ ht₂.2 _ e3).toType
    have hJ_fp := ShapeFun.Join.app hJ_f p
    have ⟨hC_fp, _, hC_fJ⟩ := Shape.Join.iff.1 hJ_fp
    have ht_fJ := ht_f1.join hJ_fp ht_f2
    have ht_fJ' := ht_f1.join (.mk hC_fp) ht_f2
  · constructor
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (ShapeFun.app_of_mem d2 ▸ (hE₁.1 d3 ha c2).1)
        (ShapeFun.app_of_mem e2 ▸ (hE₂.1 e3 ha c3).1)
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (ShapeFun.app_of_mem d2 ▸ (hE₁.1 d3 ha c2).2)
        (ShapeFun.app_of_mem e2 ▸ (hE₂.1 e3 ha c3).2)
  · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
      (ShapeFun.app_of_mem d2 ▸ hE₁.2 d3 ha c2)
      (ShapeFun.app_of_mem e2 ▸ hE₂.2 e3 ha c3)

/-- Head reduction on M, N preserves `LamDefEq`. Uses `IH.whr` (with `WHRed.app`)
to transport the inner `IH.DefEq` terms. HasType is preserved trivially (doesn't mention M, N). -/
theorem LRS.LamDefEq.whr {IH : LogRel Γ n}
    (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).1 d1, (IH.whr (.app hN) (.app hN)).1 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).1 (pae hp ha a1)
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).2 d1, (IH.whr (.app hN) (.app hN)).2 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).2 (pae hp ha a1)

/-- Term validity at `(m, a)`. -/
def LRS.DefEq (IH : LogRel Γ n) (M N A : SExpr) (m a : Shape (n+1)) : Prop :=
  match a with
  | .bot => True
  | .sort _ => LRS.TyDefEq IH M N m
  | .forallE a₁ a₂ =>
    match m with
    | .bot => True
    | .lam m =>
      ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ a₁ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂ ∧ LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂
    | _ => False
  | _ => False

def LRS (IH : LogRel Γ n) : LogRel Γ (n+1) where
  DefEq := LRS.DefEq IH
  TyDefEq := LRS.TyDefEq IH
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot ha := by cases ha.unfold <;> trivial
  left_ty := .left
  symm_ty := .symm
  trans_ty := .trans
  toType := id
  left {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .left
    · cases m with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.left⟩
  symm {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .symm
    · cases m with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.symm⟩
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .trans
    · cases m with | lam => ?_ | _ => simp
      intro ⟨B, F, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ ⟨_, _, _, _, rA', _, _, _, _, hP'⟩
      cases rA.determ .forallE rA' .forallE
      exact ⟨_, _, _, _, rA, hA1, hA2, hA₂, hE, hP.trans hP'⟩
  conv {A A' a M N m} := by
    dsimp [LRS.TyDefEq]; dsimp [LRS.DefEq]; split <;> (try · simp); dsimp
    intro ⟨B, F, B', F', u, v, rA, rA', hBB', hFF', hValB, hEdge⟩
    cases m with | lam => ?_ | _ => exact id
    intro ⟨_, _, _, v', rA₁, hA1, hValA, hA₂, hEdge₁, hP⟩
    cases rA.determ .forallE rA₁ .forallE
    cases hA1.uniq_sort hBB'.hasType.1
    cases hA₂.uniq_sort hFF'.hasType.1
    refine ⟨_, _, _, _, rA', hBB'.hasType.2, IH.left_ty (IH.symm_ty hValB),
      hBB'.defeqDF_l hFF'.hasType.2, ?_, ?_⟩
    · refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;>
        have ha' := hBB'.symm.defeqDF ha
      · exact and_self_iff.2 (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
      · exact (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
    refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;> (
      have a2 := IH.conv (IH.symm_ty hValB) a1
      have ha' := hBB'.symm.defeqDF ha
      have c := hEdge.2 hp ha'.hasType.1 (IH.left a2))
    · have ⟨v1, v2⟩ := hP.1 hp ha' a2; exact ⟨IH.conv c v1, IH.conv c v2⟩
    · exact IH.conv c (hP.2 hp ha' a2)
  mono_r_2 {a a' M N A m} le hm ht h := by
    cases a with dsimp [LRS.DefEq]
    | sort => cases a' <;> simp [Shape.LE.def] at le; subst le; exact h
    | forallE a₁ a₂ =>
      cases a' <;> simp [Shape.LE.def] at le
      let .forallE hp := hm.isType.unfold
      let .forallE hp' := ht.unfold
      cases hm.unfold with | bot => trivial | lam hm
      let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hEdge, hP⟩ := h
      exact ⟨A₁, A₂, u, v, rA, hA1,
        IH.mono_r_2_ty le.1 hp.1.isType hp'.1.isType hA2, hA₂,
        hEdge.mono_r_2 le.1 le.2 hp hp' hA2, hP.mono_r_2 le.1 le.2 hm hA2 hp'⟩
    | lam => cases a' <;> simp [Shape.LE.def] at le; exact h
  mono_r_2_ty {a a' A B} le ha ha' h := by
    dsimp [LRS.TyDefEq] at h ⊢; split <;> try trivial
    · cases a' <;> simp [Shape.LE.def] at le; subst le; exact h
    · cases a' <;> simp [Shape.LE.def] at le
      have .forallE hp := ha.unfold; have .forallE hp' := ha'.unfold
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', hValB, hEdge⟩ := h
      exact ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF',
        IH.mono_r_2_ty le.1 hp.1.isType hp'.1.isType hValB,
        hEdge.mono_r_2 le.1 le.2 hp hp' (IH.left_ty hValB)⟩
  mono_r_1 {a a' A M N m} le ha ha' hA h := by
    cases ha'.unfold with
    | bot ha' => cases ha'.unfold <;> trivial
    | sort => cases ha.unfold; exact h
    | forallE => obtain rfl | rfl := Shape.le_sort.1 le <;> [cases ha.unfold; exact h]
    | lam ha'' =>
      let .lam ha := ha.unfold; simp [Shape.LE.def] at le
      let ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge_src, hP⟩ := h
      let ⟨B₁, F₁, B₂, F₂, u', v', rA', rA'', hBB_tgt, hFF_tgt, hValB_tgt, hEdge_tgt⟩ := hA
      cases rA.determ .forallE rA' .forallE
      cases rA.determ .forallE rA'' .forallE
      cases hA₂.uniq_sort hFF_tgt
      exact ⟨_, _, _, _, rA, hBB_tgt.hasType.1, hValB_tgt, hA₂, hEdge_tgt,
        hP.mono_r_1 le.1 le.2 ha ha'' hEdge_tgt⟩
  mono_l {m m' M N A a} le hm hm' h := by
    cases a with dsimp [LRS.DefEq]
    | sort s =>
      dsimp [LRS.TyDefEq] at h ⊢; split <;> (try trivial) <;>
        cases m' <;> simp [Shape.LE.def] at le
      · subst le; exact h
      · have .forallE hm := hm.unfold; have .forallE hm' := hm'.unfold
        let ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', hValB, hEdge⟩ := h
        exact ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF',
          IH.mono_r_2_ty le.1 hm.1.isType hm'.1.isType hValB,
          hEdge.mono_r_2 le.1 le.2 hm hm' (IH.left_ty hValB)⟩
    | forallE a₁ a₂ =>
      cases hm.unfold with | bot => trivial | lam hm
      cases hm'.unfold with | bot => simp [Shape.LE.def] at le | lam hm'
      let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ := h
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.mono_l le hm hm'⟩
    | lam => exact h
  join_ty {A B m₁ m₂} hC hm₁ hm₂ h1 h2 := by
    cases hm₁.unfold with
    | bot => simp [Shape.join]; exact h2
    | sort =>
      cases m₂ with simp [Shape.join]
      | sort => split <;> [exact h1; trivial]
      | _ => trivial
    | forallE =>
      cases m₂ with simp [Shape.join] | forallE b₂ f₂ => ?_ | _ => trivial
      simp only [Shape.Compat, Bool.and_eq_true] at hC
      have .forallE ht₁ := hm₁.unfold
      have .forallE ht₂ := hm₂.unfold
      dsimp [LRS.TyDefEq]
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, hValB₁, hEdge₁⟩ := h1
      let ⟨_, _, _, _, u', v', rA', rB', hBB', hFF', hValB₂, hEdge₂⟩ := h2
      cases rA.determ .forallE rA' .forallE
      cases rB.determ .forallE rB' .forallE
      cases hBB.uniq_sort hBB'.symm
      cases hFF.uniq_sort hFF'.symm
      exact ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF,
        IH.join_ty hC.1 ht₁.1.isType ht₂.1.isType hValB₁ hValB₂,
        .join ht₁.1.isType ht₂.1.isType hC.1 ht₁ ht₂ hC.2 hEdge₁ hEdge₂⟩
  whr {M M' N N' A m a} hM hN := by
    cases a with dsimp [LRS.DefEq]
    | sort s =>
      dsimp [LRS.TyDefEq]; split <;> try rfl
      · constructor <;> intro ⟨u, r1, r2⟩
        · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
        · exact ⟨u, .trans hM r1, .trans hN r2⟩
      · constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
        · exact ⟨B₁, F₁, B₂, F₂, u, v, hM.determ_l rM .forallE, hN.determ_l rN .forallE, rest⟩
        · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hM rM, .trans hN rN, rest⟩
    | forallE a₁ a₂ =>
      cases m with | lam g => ?_ | _ => rfl
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr hM hN).1 hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr hM hN).2 hP⟩
    | _ => rfl
  whr_ty {A A' B B' m} hA hB := by
    dsimp [LRS.TyDefEq]; split <;> try rfl
    · constructor <;> intro ⟨u, r1, r2⟩
      · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
      · exact ⟨u, .trans hA r1, .trans hB r2⟩
    · constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, hA.determ_l rA .forallE, hB.determ_l rB .forallE, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hA rA, .trans hB rB, rest⟩

def LR (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => LR0
  | _+1 => LRS (LR Γ)

private theorem LRS.PiDefEq.lift_aux
    {b} {f : ShapeFun n} (le : n ≤ n') (htpi_a : Shape.HasTypePi f b true)
    (IH1 : ∀ {M N : SExpr} {m : Shape n}, m.HasType .type →
      ((LR Γ).TyDefEq (n := n') M N m.lift ↔ (LR Γ).TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      ((LR Γ).DefEq (n := n') M N A m.lift a.lift ↔ (LR Γ).DefEq M N A m a)) :
    LRS.PiDefEq (LR Γ) (n := n') B F₁ F₂ b.lift (ShapeFun.lift Shape.lift f) ↔
    LRS.PiDefEq (LR Γ) B F₁ F₂ b f := by
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (Shape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have ⟨r1, r2⟩ := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_a.2 _ hp)).1 (ShapeFun.lift_app le ▸ r1),
              (IH1 (htpi_a.2 _ hp)).1 (ShapeFun.lift_app le ▸ r2)⟩
    · exact (IH1 (htpi_a.2 _ hp)).1 (ShapeFun.lift_app le ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift _) _; d3 ▸ ?_
      simp [ShapeFun.lift] at d2; obtain ⟨q, _, d2, rfl, rfl⟩ := d2
      have hq := Shape.HasDom.def.1 htpi_a.1 _ _ d2
      have v' := (IH2 hq).1 ((LR Γ).mono_l d1
        ((Shape.HasType.lift le).2 hq) hp v))
    · have ⟨r1, r2⟩ := hEdge.1 hq ha v'
      exact ⟨ShapeFun.app_of_mem d2 ▸ (IH1 (htpi_a.2 _ hq)).2 r1,
             ShapeFun.app_of_mem d2 ▸ (IH1 (htpi_a.2 _ hq)).2 r2⟩
    · exact ShapeFun.app_of_mem d2 ▸ (IH1 (htpi_a.2 _ hq)).2 (hEdge.2 hq ha v')

private theorem LRS.LamDefEq.lift_aux
    {g : ShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : Shape.HasTypeLam g a₁ a₂)
    (IH : ∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      ((LR Γ).DefEq (n := n') M N A m.lift a.lift ↔ (LR Γ).DefEq M N A m a))
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) (n := n') M N A₁ A₂
      (ShapeFun.lift Shape.lift g) a₁.lift (ShapeFun.lift Shape.lift a₂) ↔
    LRS.LamDefEq (LR Γ) M N A₁ A₂ g a₁ a₂ := by
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (Shape.HasType.lift le).2 hp
      have v' := (IH hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IH (htm.2.2 _ hp)).1 ?_, (IH (htm.2.2 _ hp)).1 ?_⟩
        <;> rw [ShapeFun.lift_app le, ShapeFun.lift_app le] <;> [exact r1; exact r2]
    · apply (IH (htm.2.2 _ hp)).1
      rw [ShapeFun.lift_app le, ShapeFun.lift_app le]
      exact hP.2 hp' ha v'
  · refine ⟨fun _ _ p hp ha v => ?_, fun _ p hp ha v => ?_⟩
    all_goals
      have ⟨_, _, dg1, dg2, dg3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift g) p
      simp [ShapeFun.lift] at dg2; obtain ⟨qg, fg, dg2, rfl, rfl⟩ := dg2
      have ⟨_, _, da1, da2, da3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift a₂) p
      simp [ShapeFun.lift] at da2; obtain ⟨qa, fa, da2, rfl, rfl⟩ := da2
      obtain rfl : fg = g.app qg := (ShapeFun.app_of_mem dg2).symm
      obtain rfl : fa = a₂.app qa := (ShapeFun.app_of_mem da2).symm
      have hqg := Shape.HasDom.def.1 htm.2.1 _ _ dg2
      have hqa := Shape.HasDom.def.1 htm.1.1 _ _ da2
      have v_lo := (IH hqg).1 ((LR Γ).mono_l dg1
        ((Shape.HasType.lift le).2 hqg) hp v)
      have le_a2 : a₂.app qg ≤ a₂.app qa := by
        rw [← Shape.lift_le_lift le, ShapeFun.lift_app le, ShapeFun.app_of_mem da2, ← da3]
        exact ShapeFun.app_mono_r dg1
      have ht_lo := htm.2.2 _ hqg
      have ht_hi := (htm.1.2 _ hqa).mono_r le_a2 ht_lo
      have v_lo_qa := (IH hqa).1 ((LR Γ).mono_l da1
        ((Shape.HasType.lift le).2 hqa) hp v)
      have vt_qa := hEdge.2 hqa ha.hasType.1 ((LR Γ).left v_lo_qa)
      rw [dg3, da3]
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo
      exact ⟨(IH ht_hi).2 ((LR Γ).mono_r_1 le_a2 ht_lo ht_hi vt_qa r1),
              (IH ht_hi).2 ((LR Γ).mono_r_1 le_a2 ht_lo ht_hi vt_qa r2)⟩
    · exact (IH ht_hi).2 ((LR Γ).mono_r_1 le_a2 ht_lo ht_hi vt_qa (hP.2 hqg ha v_lo))

private theorem LR.lift_succ_aux :
    (∀ {M N : SExpr} {m : Shape n}, m.HasType .type →
      (LRS.TyDefEq (n := n) (LR Γ) M N m.lift ↔ (LR Γ).TyDefEq M N m)) ∧
    (∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      (LRS.DefEq (n := n) (LR Γ) M N A m.lift a.lift ↔ (LR Γ).DefEq M N A m a)) := by
  induction n with
  | zero => exact ⟨by rintro _ _ ⟨⟩ _ <;> rfl, by rintro _ _ _ ⟨⟩ ⟨⟩ _ <;> rfl⟩
  | succ k ih
  refine have h1 := ?_; ⟨h1, ?_⟩
  · intro M N m hmt; cases m with | forallE b f => ?_ | _ => rfl
    have .forallE htpi := hmt.unfold
    constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, hValB, hE⟩
    · refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, (ih.1 htpi.1.isType).1 hValB,
        ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩⟩ <;> (
        have hp' := (Shape.HasType.lift (Nat.le_succ k)).2 hp
        have v' := (ih.2 hp).2 v)
      · have ⟨r1, r2⟩ := hE.1 hp' ha v'
        exact ⟨(ih.1 (htpi.2 _ hp)).1 (ShapeFun.lift_app (Nat.le_succ k) ▸ r1),
               (ih.1 (htpi.2 _ hp)).1 (ShapeFun.lift_app (Nat.le_succ k) ▸ r2)⟩
      · exact (ih.1 (htpi.2 _ hp)).1 (ShapeFun.lift_app (Nat.le_succ k) ▸ hE.2 hp' ha v')
    · refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, (ih.1 htpi.1.isType).2 hValB,
        fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩
      all_goals
        refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f) _; d3 ▸ ?_
        simp [ShapeFun.lift] at d2; obtain ⟨q, _, d2, rfl, rfl⟩ := d2
        have hq := Shape.HasDom.def.1 htpi.1 _ _ d2
        have v' := (ih.2 hq).1 ((LRS (LR Γ)).mono_l d1
          ((Shape.HasType.lift (Nat.le_succ k)).2 hq) hp v)
      · have ⟨r1, r2⟩ := hE.1 hq ha v'
        exact ⟨ShapeFun.app_of_mem d2 ▸ (ih.1 (htpi.2 _ hq)).2 r1,
               ShapeFun.app_of_mem d2 ▸ (ih.1 (htpi.2 _ hq)).2 r2⟩
      · exact ShapeFun.app_of_mem d2 ▸ (ih.1 (htpi.2 _ hq)).2 (hE.2 hq ha v')
  · intro M N A m a hma
    cases a with | bot | lam => rfl | sort r => exact h1 hma.toType | forallE a₁ a₂
    change ShapeFun .. at a₂; have .forallE htpi_a := hma.isType.unfold
    cases hma.unfold with | bot => constructor <;> intro <;> trivial | @lam _ g _ _ htm
    constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge, hP⟩
    · have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).1 hEdge
      refine ⟨A₁, A₂, u, v, rA, hA1, (ih.1 htpi_a.1.isType).1 hValA, hA₂, hEdge', ?_⟩
      exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge').1 hP
    · have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).2 hEdge
      refine ⟨A₁, A₂, u, v, rA, hA1, (ih.1 htpi_a.1.isType).2 hValA, hA₂, hEdge', ?_⟩
      exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge).2 hP

theorem LR.DefEq.lift {m a : Shape n} (le : n ≤ n') (hma : m.HasType a) :
    (LR Γ).DefEq (n := n') M N A m.lift a.lift ↔ (LR Γ).DefEq M N A m a := by
  induction le with | refl => simp [Shape.lift_self] | step le ih
  rw [(Shape.lift_lift (.inl le)).symm, (Shape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((Shape.HasType.lift le).2 hma)).trans ih

theorem LR.TyDefEq.lift {m : Shape n} (le : n ≤ n') (hmt : m.HasType .type) :
    (LR Γ).TyDefEq (n := n') M N m.lift ↔ (LR Γ).TyDefEq M N m := by
  induction le with | refl => simp [Shape.lift_self] | step le ih
  rw [(Shape.lift_lift (.inl le)).symm]
  exact (LR.lift_succ_aux.1 (Shape.lift_type ▸ (Shape.HasType.lift le).2 hmt)).trans ih

theorem LRS.PiDefEq.lift
    {b} {f : ShapeFun n} (le : n ≤ n') (htpi_a : Shape.HasTypePi f b true) :
    LRS.PiDefEq (LR Γ) (n := n') B F₁ F₂ b.lift (ShapeFun.lift Shape.lift f) ↔
    LRS.PiDefEq (LR Γ) B F₁ F₂ b f := lift_aux le htpi_a (LR.TyDefEq.lift le) (LR.DefEq.lift le)

theorem LRS.LamDefEq.lift {g : ShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : Shape.HasTypeLam g a₁ a₂)
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) (n := n') M N A₁ A₂
      (ShapeFun.lift Shape.lift g) a₁.lift (ShapeFun.lift Shape.lift a₂) ↔
    LRS.LamDefEq (LR Γ) M N A₁ A₂ g a₁ a₂ := lift_aux le htm (LR.DefEq.lift le) hEdge

def LR.Subst1 (Γ₀ : List SExpr) (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∀ {{n}} (a : Shape n), LE_Interp ρ a A₀ →
    (a.HasType .type → (∃ u, Γ₀ ⊢ A ≡ A' : .sort u) ∧ (LR Γ₀).TyDefEq A A' a) ∧
    (∀ {{m}}, LE_Interp ρ m (.bvar i) → m.HasType a → (LR Γ₀).DefEq x x' A m a)

inductive LR.SubstWF (Γ₀ : List SExpr) : Subst → Subst → List SExpr → Valuation → Prop where
  | id : LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {n a}, LE_Interp (n := n) ρ a A →
      ∃ n' a', n ≤ n' ∧ a.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp (n := n) ρ a A → x.HasType a →
    LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

theorem LR.SubstWF.fits : LR.SubstWF Γ₀ σ σ' Γ ρ → ρ.Fits Γ₀ Γ
  | .id => .nil
  | .cons W h1 h2 h3 _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.toSubstEq : LR.SubstWF Γ₀ σ σ' Γ ρ → Ctx.SubstEq Γ₀ σ σ' Γ
  | .id => .nil
  | .cons W _ _ _ h0 => .cons W.toSubstEq h0.1

theorem LR.SubstWF.left (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 h0 ih =>
    refine .cons ih h1 h2 h3 ⟨h0.1.hasType.1, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _).left_ty h2⟩
    · exact (LR _).left <| (h0.2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 h0 ih =>
    refine .cons ih h1 h2 h3 ⟨?_, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (h0.2 (n := 0) _ .bot).1 (.bot .sort)
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (h0.2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _).symm_ty h2⟩
    · let ⟨_, h2⟩ := (h0.2 a ha).1 hmem.isType
      exact (LR _).conv h2 ((LR _).symm ((h0.2 a ha).2 hM hmem))
