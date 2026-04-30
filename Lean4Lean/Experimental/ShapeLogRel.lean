import Lean4Lean.Experimental.SExpr

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
  | ctor : Name → List Shape → ShapeS Shape

def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

def TShape := Σ n, Shape n
abbrev Shape.T : Shape n → TShape := Sigma.mk _

abbrev ShapeFun (n) := List (Shape n × Shape n)

def TShapeFun := List (TShape × TShape)
abbrev ShapeFun.T : ShapeFun n → TShapeFun := .map fun (a, b) => (a.T, b.T)

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
  | _+1, .ctor c l, .ctor c' l' => c == c' && l.Forall₂ (Shape.ble · ·) l'
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
    | .ctor c f, .ctor c' f' => c = c' ∧ f.Forall₂ Shape.LE f'
    | _, _ => False := by
  dsimp only [(· ≤ ·), LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp
  · intro; rfl

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
    · exact .rfl fun _ _ => ih

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
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;> grind [List.Forall₂.trans]

omit [Params] in
theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s.LE t → t.LE u → s.LE u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n} m, Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift _ s) <| ShapeFun.lift (lift _) f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift (lift _) f
  | _+1, _+1, .ctor c l => .ctor c <| l.map (lift _)

omit [Params] in
@[simp] theorem Shape.lift_bot : (.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in
@[simp] theorem Shape.lift_sort : (.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in theorem Shape.lift_prop : (.prop : Shape n).lift m = .prop := lift_sort
omit [Params] in theorem Shape.lift_type : (.type : Shape n).lift m = .type := lift_sort

omit [Params] in
theorem Shape.lift_self {s : Shape n} : s.lift n = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s <;> [rfl; grind]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]
  · rw [List.map_id'' fun _ => Shape.lift_self]

omit [Params] in
theorem ShapeFun.lift_self {s : ShapeFun n} : lift (Shape.lift n) s = s := by
  simp [ShapeFun.lift]; apply List.map_id''; simp [Shape.lift_self]

omit [Params] in
theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift _ := by
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
          ShapeFun.lift (lift n₃) (ShapeFun.lift (lift n₂) s) = ShapeFun.lift (lift _) s := by
        simp [ShapeFun.lift, ih]
      cases s <;> simp [lift, ih, ihf]
      · congr 2; ext; exact ih

omit [Params] in
theorem ShapeFun.lift_lift {s : ShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    lift (Shape.lift n₃) (lift (Shape.lift n₂) s) = lift (Shape.lift _) s := by
  simp [ShapeFun.lift, Shape.lift_lift le]

omit [Params] in
theorem Shape.lift_le_lift {s t : Shape n} (le : n ≤ m) : s.lift m ≤ t.lift m ↔ s ≤ t := by
  dsimp [(· ≤ ·), Shape.LE]; rw [← Bool.eq_iff_iff]
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases s <;> cases t <;> simp [lift, ble]
  | succ n ih =>
    let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {t' s} := @ih m t' s le
    let rec go {s t : ShapeFun n} :
        ShapeFun.ble ble (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) =
        ShapeFun.ble ble s t := by
      simp only [ShapeFun.ble, ShapeFun.lift, List.all_map, List.any_map, Function.comp_def, ih]
    cases s <;> cases t <;> simp [ble, lift, go, *]

omit [Params] in
theorem ShapeFun.lift_le_lift {s t : ShapeFun n} (le : n ≤ m) :
    ShapeFun.LE (lift (Shape.lift m) s) (lift (Shape.lift m) t) ↔ ShapeFun.LE s t := by
  dsimp [ShapeFun.LE]; rw [← Bool.eq_iff_iff,
    Shape.lift_le_lift.go _ _ (Bool.eq_iff_iff.2 (Shape.lift_le_lift le))]

omit [Params] in
theorem Shape.lift_le_bot {s : Shape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← le_bot, ← lift_bot, Shape.lift_le_lift h]

omit [Params] in
theorem Shape.lift_eq_bot {s : Shape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  rw [← le_bot, Shape.lift_le_bot h]

omit [Params] in
theorem Shape.lift_mono {s t : Shape n} : s ≤ t → s.lift m ≤ t.lift m := by
  dsimp [(· ≤ ·), Shape.LE]
  cases n with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
  | succ n =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      let rec go {n m} (ih : ∀ {s t : Shape n}, s ≤ t → s.lift m ≤ t.lift m)
          {s t} : ShapeFun.ble ble s t → ShapeFun.ble ble
            (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      have := @Shape.lift_mono n m; dsimp [(· ≤ ·), Shape.LE] at this
      have := @go n m Shape.lift_mono
      cases s <;> cases t <;> simp [ble, lift, *] <;> grind [List.Forall₂.imp]

omit [Params] in
theorem ShapeFun.lift_mono {s t : ShapeFun n} : s.LE t →
    LE (lift (Shape.lift m) s) (lift (Shape.lift _) t) := Shape.lift_mono.go Shape.lift_mono

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
  | _+1, _+1, .ctor c l => (.ctor c (l.map (·.plift.1)), return .ctor c (← l.mapM (·.plift.2)))

omit [Params] in
theorem Shape.plift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.plift = (s.lift m, some (s.lift m)) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.plift = (s.lift m, some (s.lift m)))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift s = (ShapeFun.lift (lift m) s, some (ShapeFun.lift (lift m) s)) := by
    simp only [ShapeFun.plift, ShapeFun.lift, IH le, bind, pure]; congr 1
    · rw [← List.filterMap_eq_map]; rfl
    · rw [List.mapM_eq_some, List.forall₂_map_right_iff]
      exact .rfl fun _ _ => rfl
  unfold plift; split <;> simp [lift] at le ⊢ <;> simp [plift_eq_lift le, go plift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩

omit [Params] in
theorem Shape.plift_lift (le : n ≤ m) {s : Shape n} :
    (s.lift m).plift = (s, some s) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, (s.lift m).plift = (s, some s))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift (ShapeFun.lift (lift m) s) = (s, some s) := by
    simp only [ShapeFun.plift, ShapeFun.lift, List.filterMap_map, List.mapM_map]; congr 1
    · refine .trans ?_ List.filterMap_some; congr 1; funext (a, b); simp [IH le]
    · rw [List.mapM_eq_some]; refine .rfl fun (a, b) _ => by simp [IH le]
  unfold lift; split <;> (try cases m) <;> try simp [plift, sort, bot] at le ⊢
  · cases le; cases s <;> grind
  · simp [plift_lift le, go plift_lift le]
  · simp [go plift_lift le]
  · simp [Function.comp_def, plift_lift le]
    exact ⟨_, List.mapM_pure, List.map_id _ ▸ rfl⟩

omit [Params] in
theorem Shape.plift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (t.lift m ≤ s ↔ t ≤ (s.plift (m := n)).1) ∧
    (s ≤ t.lift m ↔ ∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t) := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n},
        (t.lift m ≤ s ↔ t ≤ s.plift.1) ∧ (s ≤ t.lift m ↔ ∃ z, s.plift.2 = some z ∧ z ≤ t))
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      (ShapeFun.LE (ShapeFun.lift (lift _) t) s ↔ ShapeFun.LE t (ShapeFun.plift plift s).1) ∧
      (ShapeFun.LE s (ShapeFun.lift (lift _) t) ↔
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
  all_goals have le := Nat.le_of_succ_le_succ le
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | forallE => ?_ | _ => intros; subst_vars; simp
    simp [Shape.plift_thm le,
      go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | lam => ?_ | _ => intros; subst_vars; simp
    simp [go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def, List.mapM_eq_some]
    | ctor => ?_ | _ => intros; subst_vars; simp
    refine ⟨fun _ => ?_, ?_, ?_⟩
    · apply Iff.of_eq; congr; funext a b
      exact propext (Shape.plift_thm le).1
    · rintro ⟨rfl, h⟩; rename_i c l _ l'
      suffices ∃ z, l.Forall₂ (·.plift.2 = some ·) z ∧ z.Forall₂ LE l' from
        have ⟨z, h1, h2⟩ := this; ⟨_, ⟨_, h1, rfl⟩, rfl, h2⟩
      induction h with | nil => exact ⟨_, .nil, .nil⟩ | cons h _ ih
      have ⟨a, a1, a2⟩ := (Shape.plift_thm le).2.1 h; have ⟨z, b1, b2⟩ := ih
      exact ⟨_, .cons a1 b1, .cons a2 b2⟩
    · rintro ⟨z, ⟨a, h1, rfl⟩, h2, h3⟩; refine ⟨h2, h1.trans (fun _ _ _ h1 h3 => ?_) h3⟩
      exact (Shape.plift_thm le).2.2 ⟨_, h1, h3⟩

omit [Params] in
theorem Shape.le_plift (le : n ≤ m) {s : Shape m} {t : Shape n} :
    t ≤ s.plift.1 ↔ t.lift m ≤ s := (Shape.plift_thm le).1.symm

omit [Params] in
theorem Shape.plift_le (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (∃ z, s.plift.2 = some z ∧ z ≤ t) ↔ s ≤ t.lift m := (Shape.plift_thm le).2.symm

omit [Params] in
theorem ShapeFun.le_plift (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    LE t (plift Shape.plift s).1  ↔ LE (lift (Shape.lift m) t) s :=
  (Shape.plift_thm.go Shape.plift_thm le).1.symm

omit [Params] in
theorem ShapeFun.plift_le (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    (∃ z, (plift Shape.plift s).2 = some z ∧ LE z t) ↔ LE s (lift (Shape.lift m) t) :=
  (Shape.plift_thm.go Shape.plift_thm le).2.symm

omit [Params] in
theorem Shape.plift_mono {s t : Shape m} (H : s ≤ t) : (s.plift (m := n)).1 ≤ t.plift.1 := by
  obtain le | le := Nat.le_total m n
  · rw [Shape.plift_eq_lift le, Shape.plift_eq_lift le]; exact Shape.lift_mono H
  · exact (Shape.le_plift le).2 (.trans ((Shape.le_plift le).1 .rfl) H)

def TShape.LE (a b : TShape) : Prop := a.2.lift (max a.1 b.1) ≤ b.2.lift _
instance : _root_.LE TShape := ⟨TShape.LE⟩
omit [Params] in
theorem TShape.LE.def' {a b : TShape} : a ≤ b ↔ a.2.lift (max a.1 b.1) ≤ b.2.lift _ := .rfl

def TShapeFun.LE (a : ShapeFun n) (b : ShapeFun m) : Prop :=
  ShapeFun.LE (.lift (Shape.lift (max n m)) a) (.lift (Shape.lift _) b)

omit [Params] in
theorem TShape.LE.def {a b : TShape} (h1 : a.1 ≤ m) (h2 : b.1 ≤ m) :
    a ≤ b ↔ a.2.lift m ≤ b.2.lift m := by
  refine (Shape.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [Shape.lift_lift (.inl (Nat.le_max_left ..)), Shape.lift_lift (.inl (Nat.le_max_right ..))]

omit [Params] in
theorem TShapeFun.LE.def {a : ShapeFun n} {b : ShapeFun m} (h1 : n ≤ k) (h2 : m ≤ k) :
    TShapeFun.LE a b ↔ ShapeFun.LE (.lift (Shape.lift k) a) (.lift (Shape.lift _) b) := by
  refine (ShapeFun.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [ShapeFun.lift_lift (.inl (Nat.le_max_left ..)),
    ShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

def TShape.bot : TShape := Shape.T (n := 0) .bot
def TShape.sort (r : Bool) : TShape := Shape.T (n := 0) (.sort r)
def TShape.type : TShape := Shape.T (n := 0) .type

omit [Params] in
nonrec theorem TShape.LE.rfl {a : TShape} : a ≤ a := .rfl

omit [Params] in
theorem TShape.LE.trans {a b c : TShape} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  let k := max (max a.1 b.1) c.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  exact (LE.def hk.1.1 hk.2).2 (.trans ((LE.def hk.1.1 hk.1.2).1 h1) ((LE.def hk.1.2 hk.2).1 h2))

omit [Params] in
theorem TShape.LE.lift_l {a b : TShape} (h1 : a.1 ≤ b.1) : a ≤ b ↔ a.2.lift (b.1) ≤ b.2 := by
  refine (LE.def h1 (Nat.le_refl _)).trans (Shape.lift_self ▸ .rfl)
omit [Params] in
theorem TShape.LE.lift_r {a b : TShape} (h1 : b.1 ≤ a.1) : a ≤ b ↔ a.2 ≤ b.2.lift (a.1) := by
  refine (LE.def (Nat.le_refl _) h1).trans (Shape.lift_self ▸ .rfl)
omit [Params] in
theorem Shape.LE.T_iff {a b : Shape n} : a.T ≤ b.T ↔ a ≤ b := by
  refine (TShape.LE.lift_l (Nat.le_refl _) (a := a.T) (b := b.T)).trans (Shape.lift_self ▸ .rfl)
omit [Params] in
theorem Shape.LE.T {a b : Shape n} : a ≤ b → a.T ≤ b.T := T_iff.2
omit [Params] in
theorem Shape.LE.of_T {a b : Shape n} : a.T ≤ b.T → a ≤ b := T_iff.1

omit [Params] in
theorem TShape.bot_eqv : (Shape.bot (n := n)).T ≤ bot ∧ bot ≤ (Shape.bot (n := n)).T := by
  simp [TShape.LE.def', bot]

omit [Params] in
theorem TShape.bot_le' : Shape.T (n := n) .bot ≤ a := by simp [TShape.LE.def']

omit [Params] in
theorem TShape.bot_le {a : TShape} : bot ≤ a := bot_le'

omit [Params] in
theorem TShape.le_bot {a : TShape} : a ≤ bot ↔ a.2 = .bot := by
  simp [TShape.LE.def', bot, Shape.lift_le_bot (Nat.le_max_left ..)]

omit [Params] in
theorem TShape.le_bot' {a : TShape} : a ≤ bot ↔ a = Shape.T (n := a.1) .bot := by
  simp [TShape.LE.def', bot, Shape.lift_le_bot (Nat.le_max_left ..)]; cases a <;> grind

omit [Params] in
theorem TShape.lift_eqv {a : TShape} (h : a.1 ≤ m) :
    (a.2.lift m).T ≤ a ∧ a ≤ (a.2.lift m).T := by
  simp [TShape.LE.def', Shape.lift_lift (.inl h), Shape.LE.rfl]

omit [Params] in
theorem TShape.sort_eqv :
    (Shape.sort (n := n) r).T ≤ .sort r ∧ .sort r ≤ (Shape.sort (n := n) r).T := by
  simp [sort, TShape.LE.def', Shape.LE.rfl]

def Shape.Join (x y z : Shape n) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w
def ShapeFun.Join (x y z : ShapeFun n) := ∀ w, z.LE w ↔ x.LE w ∧ y.LE w

theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) ↔ x.Compat y := sorry

theorem ShapeFun.Compat.lift {x y : ShapeFun n} (le : n ≤ m) :
    Compat Shape.Compat (lift (Shape.lift m) x) (lift (Shape.lift m) y) ↔
    Compat Shape.Compat x y := sorry

def TShape.Compat (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).Compat (y.2.lift _)

theorem TShape.Compat.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.Compat y ↔ (x.2.lift m).Compat (y.2.lift _) := by
  refine (Shape.Compat.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [Shape.lift_lift (.inl (Nat.le_max_left ..)), Shape.lift_lift (.inl (Nat.le_max_right ..))]

theorem Shape.Compat.T_iff {x y : Shape n} : x.Compat y ↔ x.T.Compat y.T := by
  refine .trans ?_ (TShape.Compat.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).symm
  rw [Shape.lift_self, Shape.lift_self]

theorem Shape.Compat.T {x y : Shape n} : x.Compat y → x.T.Compat y.T := T_iff.1

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

theorem TShape.Compat.def' {x y : TShape} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨z, h1, h2⟩ => ?_⟩
  · have ⟨z, h1, h2⟩ := Shape.Compat.def.1 h
    exact ⟨z.T, (LE.lift_l (Nat.le_max_left ..)).2 h1, (LE.lift_l (Nat.le_max_right ..)).2 h2⟩
  · let k := max (max x.1 y.1) z.1
    have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    exact (TShape.Compat.def hk.1.1 hk.1.2).2 <|
      Shape.Compat.def.2 ⟨_, (LE.def hk.1.1 hk.2).1 h1, (LE.def hk.1.2 hk.2).1 h2⟩

omit [Params] in
theorem Shape.Compat.mono {x y x' y' : Shape n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := Shape.Compat.def.1 H
  Shape.Compat.def.2 ⟨_, h1.trans a1, h2.trans a2⟩

omit [Params] in
theorem Shape.Join.compat (H : Join x y z) : x.Compat y := Compat.def.2 ⟨_, (H _).1 .rfl⟩

omit [Params] in
theorem Shape.Join.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift m).Join (y.lift m) (z.lift m) ↔ x.Join y z := sorry

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
    (x.join y).lift m = (x.lift m).join (y.lift m) := sorry

omit [Params] in
theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    lift (Shape.lift m) (ShapeFun.join Shape.join x y) =
    join Shape.join (lift (Shape.lift m) x) (lift (Shape.lift m) y) := sorry

def TShape.join (x y : TShape) : TShape := ⟨max x.1 y.1, (x.2.lift _).join (y.2.lift _)⟩

omit [Params] in
theorem TShape.lift_join {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    (x.join y).2.lift m = (x.2.lift m).join (y.2.lift m) := by
  simp [join, Shape.lift_join (Nat.max_le.2 ⟨h1, h2⟩), Shape.lift_lift (.inl (Nat.le_max_left ..)),
    Shape.lift_lift (.inl (Nat.le_max_right ..))]

def TShape.Join (x y z : TShape) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w

omit [Params] in
theorem TShape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

omit [Params] in
theorem TShape.Join.def (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) (h3 : z.1 ≤ m) :
    Join x y z ↔ Shape.Join (x.2.lift m) (y.2.lift m) (z.2.lift m) := by
  refine ⟨fun H w => ?_, fun H w => ?_⟩
  · have := H w.T; rwa [LE.lift_l h3, LE.lift_l h1, LE.lift_l h2] at this
  · let k := max m w.1; have hk := Nat.max_le.1 (Nat.le_refl k)
    rw [LE.def (Nat.le_trans h3 hk.1) hk.2,
      LE.def (Nat.le_trans h1 hk.1) hk.2,
      LE.def (Nat.le_trans h2 hk.1) hk.2]
    have := (Shape.Join.lift hk.1).2 H
    rw [Shape.lift_lift (.inl h1), Shape.lift_lift (.inl h2), Shape.lift_lift (.inl h3)] at this
    exact this _

omit [Params] in
theorem Shape.Join.T_iff {x y z : Shape n} : Join x y z ↔ TShape.Join x.T y.T z.T := by
  refine .symm <| (TShape.Join.def (x := x.T) (y := y.T) (z := z.T)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  rw [Shape.lift_self, Shape.lift_self, Shape.lift_self]

omit [Params] in
theorem Shape.Join.T {x y z : Shape n} : Join x y z → TShape.Join x.T y.T z.T := T_iff.1

omit [Params] in
theorem TShape.Join.mk (H : x.Compat y) : Join x y (x.join y) := by
  refine (Join.def (Nat.le_max_left ..) (Nat.le_max_right ..) (Nat.le_refl _)).2 ?_
  rw [TShape.lift_join (Nat.le_max_left ..) (Nat.le_max_right ..)]; exact Shape.Join.mk H

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
  | _+1, .ctor _ l => l.all WF

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
    (app f a : Shape n).lift m = app (lift (Shape.lift m) f) (a.lift m) := by
  sorry

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

omit [Params] in
@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

omit [Params] in
@[simp] theorem Shape.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (f.lift _) (a.lift _) := by
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
    lift (Shape.lift _) (ShapeFun.single x y) = (ShapeFun.single (x.lift m) (y.lift m)) := by
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

omit [Params] in
theorem TShape.app_mono {f : Shape (n + 1)} {f' : Shape (m + 1)} {a a'}
    (le₁ : f.T ≤ f'.T) (le₂ : a.T ≤ a'.T) : (f.app a).T ≤ (f'.app a').T := by
  have lm₁ := Nat.le_max_left n m; have lm₂ := Nat.le_max_right n m
  rw [TShape.LE.def', Shape.lift_app lm₁, Shape.lift_app lm₂]
  refine (Shape.app_mono_l ?_ _).trans  (Shape.app_mono_r le₂)
  exact (LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂)).1 le₁

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
    HasDom (.lift (Shape.lift m) f) (a.lift m) ↔ HasDom (n := n) f a := by
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

omit [Params] in
theorem Shape.HasTypeLam.lift (le : n ≤ m) :
    HasTypeLam (.lift (Shape.lift m) f) (a.lift m) (.lift (Shape.lift m) b) ↔
    HasTypeLam (n := n) f a b := by
  sorry

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
    HasType (m.lift n') (a.lift n') ↔ HasType (n := n) m a := sorry

omit [Params] in
theorem Shape.HasType.join (hJ : Join m₁ m₂ m) :
    HasType m₁ a → HasType m₂ a → HasType m a := sorry

def TShape.HasType (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).HasType (y.2.lift _)

theorem TShape.HasType.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.HasType y ↔ (x.2.lift m).HasType (y.2.lift m) := by
  refine (Shape.HasType.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [Shape.lift_lift (.inl (Nat.le_max_left ..)), Shape.lift_lift (.inl (Nat.le_max_right ..))]

theorem Shape.HasType.T_iff {x y : Shape n} : x.T.HasType y.T ↔ x.HasType y := by
  refine (TShape.HasType.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  simp [Shape.lift_self]

theorem Shape.HasType.T {x y : Shape n} : x.HasType y → x.T.HasType y.T := T_iff.2

omit [Params] in
theorem TShape.HasType.bot_r (H : HasType x .bot) : x ≤ .bot := by
  simp [TShape.HasType, bot] at H
  exact TShape.le_bot.2 <| (Shape.lift_eq_bot (Nat.le_max_left ..)).1 H.bot_r

theorem TShape.HasType.mono_r {m a a' : TShape} (ha : a ≤ a')
    (h1 : HasType a' (.sort r)) (h2 : HasType m a) : HasType m a' := by
  let k := max (max m.1 a.1) a'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 h1
  have h2 := (TShape.HasType.def hk.1.1 hk.1.2).1 h2
  have ha := (TShape.LE.def hk.1.2 hk.2).1 ha
  exact (TShape.HasType.def hk.1.1 hk.2).2 (h1.mono_r ha h2)

theorem TShape.HasType.bot : HasType x (.sort r) → HasType .bot x := by
  rw [TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _),
    TShape.HasType.def (Nat.zero_le _) (Nat.le_refl _)]
  simp [sort]; exact .bot

theorem TShape.HasType.bot' : HasType x .type → HasType .bot x := .bot

omit [Params] in
theorem TShape.HasType.sort : HasType (.sort r) .type := by simp [HasType]; exact .sort

theorem TShape.HasType.join (hJ : Join m₁ m₂ m)
    (h1 : HasType m₁ a) (h2 : HasType m₂ a) : HasType m a := by
  let k := max (max m₁.1 m₂.1) (max m.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2.2).1 h2
  have hJ := (TShape.Join.def hk.1.1 hk.1.2 hk.2.1).1 hJ
  exact (TShape.HasType.def hk.2.1 hk.2.2).2 (h1.join hJ h2)

theorem TShape.HasType.bot_r' (ha : a ≤ .bot) (H : HasType x a) : x ≤ .bot :=
  (mono_r (r := true) ha (.bot' .sort) H).bot_r

-- inductive TShape.HasTypeU : TShape → TShape → Prop
--   | bot : HasType x .type → HasTypeU .bot x
--   | sort : HasTypeU (.sort r) .type
--   | forallE : Shape.HasTypePi b a r → HasTypeU (Shape.T (n := n+1) (.forallE a b)) (.sort r)
--   | lam : Shape.HasTypeLam f a b → HasTypeU (Shape.T (n := n+1) (.lam f)) (Shape.T (m+1) (.forallE a b))

inductive LE_Forall {n} : TShape → Shape n → ShapeFun n → Prop where
  | bot : a ≤ .bot → LE_Forall a b f
  | forallE : b'.T ≤ b.T → TShapeFun.LE (n := m) f' f →
    LE_Forall (Shape.T (n := m+1) (.forallE b' f')) b f

omit [Params] in
theorem TShape.LE.le_forall (ha : a ≤ Shape.T (n := _+1) (.forallE b f)) :
    LE_Forall a b f := by
  obtain ⟨⟨⟩, a⟩ := a <;> (cases a with | bot => exact .bot TShape.bot_eqv.1 | _ => ?_) <;>
    (first
    | rw [TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)] at ha
    | rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
        (Nat.succ_le_succ (Nat.le_max_right ..))] at ha) <;>
    simp [Shape.lift, Shape.T, Shape.sort, Shape.LE.def] at ha
  exact .forallE ha.1 ha.2

def TShape.HasTypeLam (f : ShapeFun n) (a : Shape m) (b : ShapeFun m) :=
  Shape.HasTypeLam (ShapeFun.lift (Shape.lift _) f) (a.lift (max n m)) (ShapeFun.lift (Shape.lift _) b)

omit [Params] in
theorem TShape.HasTypeLam.def (le₁ : n ≤ k) (le₂ : m ≤ k) :
    HasTypeLam (n := n) (m := m) f a b ↔
    Shape.HasTypeLam (.lift (Shape.lift _) f) (a.lift k) (.lift (Shape.lift _) b) := by
  rw [TShape.HasTypeLam, ← Shape.HasTypeLam.lift (Nat.max_le.2 ⟨le₁, le₂⟩),
    ShapeFun.lift_lift (.inl (Nat.le_max_left ..)), Shape.lift_lift (.inl (Nat.le_max_right ..)),
    ShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.HasType.ty_forallE_inv
    {x : TShape} (H : x.HasType (Shape.T (n := _+1) (.forallE b f))) :
    x ≤ .bot ∨ ∃ n g, x = Shape.T (n := n+1) (.lam g) ∧ TShape.HasTypeLam g b f := by
  refine have le₁ := Nat.le_succ_of_le (Nat.le_max_left ..)
    have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
    have H := (TShape.HasType.def le₁ le₂).1 H; ?_
  generalize eq : x.2.lift _ = y at H
  cases H.unfold with
  | bot => left; exact TShape.le_bot.2 <| (Shape.lift_eq_bot le₁).1 eq
  | lam H =>
    obtain ⟨_|_, ⟨⟩⟩ := x <;> cases eq
    refine .inr ⟨_, _, rfl, (TShape.HasTypeLam.def ?_ ?_).2 H⟩
    · exact Nat.le_of_succ_le (Nat.le_max_left ..)
    · exact Nat.le_max_right ..

omit [Params] in
theorem Shape.HasType.mono_l {m a : Shape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a :=
  .join (Shape.join_self.2 ⟨hm1, hm2⟩) H H

theorem TShape.HasType.mono_l {m a : TShape}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  let k := max (max m.1 a.1) m'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have H := (TShape.HasType.def hk.1.1 hk.1.2).1 H
  have hm1 := (TShape.LE.def hk.1.1 hk.2).1 hm1
  have hm2 := (TShape.LE.def hk.2 hk.1.1).1 hm2
  exact (TShape.HasType.def hk.2 hk.1.2).2 (H.mono_l hm1 hm2)

theorem TShape.HasType.sort_T : HasType (Shape.T (n := n) (.sort r)) .type :=
  mono_l TShape.sort_eqv.2 TShape.sort_eqv.1 .sort

theorem TShape.HasType.sort_r {x : Shape n} : x.T.HasType (.sort r) ↔ x.HasType (.sort r) :=
  .trans ⟨mono_r TShape.sort_eqv.2 .sort_T, mono_r TShape.sort_eqv.1 .sort⟩ Shape.HasType.T_iff

theorem TShape.HasType.bot_T (H : HasType x (.sort r)) : HasType (Shape.T (n := n) .bot) x :=
  H.bot.mono_l bot_eqv.2 bot_eqv.1
theorem TShape.HasType.bot_T' (H : HasType x .type) : HasType (Shape.T (n := n) .bot) x := H.bot_T

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

theorem TShape.HasType.proofIrrel
    (ha : HasType a (.sort false)) (hx : HasType x a) : x ≤ .bot := by
  have ha := (TShape.HasType.def (Nat.le_max_right x.1 a.1) (Nat.zero_le _)).1 ha
  exact TShape.le_bot.2 <| (Shape.lift_eq_bot (Nat.le_max_left ..)).1 <| ha.proofIrrel hx

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

def Valuation := Nat → TShape

def Valuation.nil : Valuation := fun _ => ⟨0, .bot⟩
def Valuation.push (ρ : Valuation) (u : TShape) : Valuation
  | 0 => u
  | n+1 => ρ n

def Valuation.LE (ρ ρ' : Valuation) : Prop := ∀ n, ρ n ≤ ρ' n

omit [Params] in
theorem Valuation.LE.rfl {ρ : Valuation} : ρ.LE ρ := fun _ => .rfl

omit [Params] in
theorem Valuation.LE.push {ρ ρ' : Valuation} :
    (ρ.push a).LE (ρ'.push a') ↔ ρ.LE ρ' ∧ a ≤ a' :=
  ⟨fun H => ⟨fun _ => H (_+1), H 0⟩, fun ⟨H1, H2⟩ => fun | 0 => H2 | _+1 => H1 _⟩

/-- Two valuations are compatible if their entries are compatible at each index
(after lifting to a common level). -/
def Valuation.Compat (ρ₁ ρ₂ : Valuation) : Prop := ∀ i, (ρ₁ i).Compat (ρ₂ i)

/-- Pointwise join of two valuations. Each entry is lifted to a common level and joined. -/
def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

omit [Params] in
theorem Valuation.Compat.le_join {ρ₁ ρ₂ : Valuation}
    (hc : ρ₁.Compat ρ₂) : ρ₁.LE (ρ₁.join ρ₂) ∧ ρ₂.LE (ρ₁.join ρ₂) :=
  ⟨fun i => (TShape.Join.mk (hc i)).le.1, fun i => (TShape.Join.mk (hc i)).le.2⟩

inductive LE_Interp.Matches : (p : Pattern) → ∀ {n}, Name → List SLevel → List (Shape n) →
    (p.Path.1 → List SLevel) → (p.Path.2 → TShape) → Prop
  | const : Matches (.const c) c ls rargs (fun _ => ls) nofun
  | var : Matches f c ls rargs f1 g1 → Matches (.var f) c ls (a :: rargs) f1 (·.elim ⟨_, a⟩ g1)
  | app : Matches (n := n+1) f c ls rargs f1 g1 → Matches a c' ls' rargs' f2 g2 →
    Matches (n := n+1) (.app f a) c ls (.ctor c' rargs'.reverse :: rargs)
      (Sum.elim f1 f2) (Sum.elim g1 g2)

variable {p : Pattern} (m1 : p.Path.1 → List SLevel) (m2 : p.Path.2 → TShape)
  (R : TShape → SExpr → Prop) in
inductive LE_Interp.RHS : TShape → p.RHS → Prop
  | bot : RHS (Shape.T .bot) r
  | const : R m ((SExpr.mk e).instL (m1 path)) → RHS m (.fixed path e cl)
  | var : m ≤ m2 path → RHS m (.var path)
  | app : RHS (Shape.T (n := n + 1) f) F → RHS a.T A → m ≤ (f.app a).T → RHS m (.app F A)

variable (c : Name) (ls : List SLevel) (R : TShape → SExpr → Prop) {n : Nat} in
inductive LE_Interp.Const : List (Shape n) → TShape → Prop
  | lam : k ≤ n → (∀ x y : Shape k, (x, y) ∈ f → Const (x.lift n :: rargs) y.T) →
    m ≤ Shape.T (n := k+1) (.lam f) → Const rargs m
  | ctor : m ≤ Shape.T (n := n + 1) (.ctor c rargs.reverse) → Const rargs m
  | pat : Params.Pat p r → Matches p c ls rargs m1 m2 → RHS m1 m2 R m r.1 → Const rargs m
-- Const (n' := n + 1) args (.ctor c args)

inductive LE_Interp : Valuation → TShape → SExpr → Prop
  | bot : LE_Interp ρ (Shape.T .bot) M
  -- | le : m ≤ m' → LE_Interp ρ m' M → LE_Interp ρ m M
  -- | unlift : n ≤ n' → LE_Interp (n := n') ρ m.lift M → LE_Interp (n := n) ρ m M
  | bvar : m ≤ ρ i → LE_Interp ρ m (.bvar i)
  | sort : m ≤ .sort (l ≠ .zero) → LE_Interp ρ m (.sort l)
  | app : LE_Interp ρ (Shape.T f) F → LE_Interp ρ a.T A →
    m ≤ (f.app a).T → LE_Interp ρ m (.app F A)
  | lam : LE_Interp ρ (Shape.T (n := n) a) A →
    Shape.HasDom f a → (∀ x, x.HasType a → LE_Interp (ρ.push x.T) ((f : ShapeFun n).app x).T F) →
    m ≤ Shape.T (n := _+1) (.lam f) → LE_Interp ρ m (.lam A F)
  | forallE : LE_Interp ρ (Shape.T (n := n) b) B → LE_Interp ρ (Shape.T (n := n) b') B →
    Shape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) ((f : ShapeFun n).app x).T F) →
    m ≤ Shape.T (n := n+1) (.forallE b f) → LE_Interp ρ m (.forallE B F)
  | const :
    Params.env.constants c = some ci → ls.length = ci.uvars →
    m ≤ Shape.T m' → m'.HasType a →
    LE_Interp ρ (Shape.T a) ((SExpr.mk ci.type).instL ls) →
    LE_Interp.Const c ls R [] m → (∀ m e, R m e → LE_Interp ρ m e) →
    LE_Interp ρ m (.const c ls)

theorem LE_Interp.bvar' : LE_Interp ρ (ρ i) (.bvar i) := .bvar .rfl
theorem LE_Interp.bvar0 : LE_Interp (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem LE_Interp.sort' : LE_Interp ρ (.sort (l ≠ .zero)) (.sort l) := .sort .rfl
theorem LE_Interp.app' (h1 : LE_Interp ρ (Shape.T f) F) (h2 : LE_Interp ρ a.T A) :
    LE_Interp ρ (f.app a).T (.app F A) := .app h1 h2 .rfl
theorem LE_Interp.lam' {f : ShapeFun n} (h1 : LE_Interp ρ (Shape.T a) A) (h2 : Shape.HasDom f a)
    (h3 : ∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (Shape.T (n := n+1) (.lam f)) (.lam A F) := .lam h1 h2 h3 .rfl
theorem LE_Interp.forallE' {f : ShapeFun n}
    (h1 : LE_Interp ρ b.T B) (h2 : LE_Interp ρ b'.T B)
    (h3 : Shape.HasDom f b') (h4 : ∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (Shape.T (n := n+1) (.forallE b f)) (.forallE B F) := .forallE h1 h2 h3 h4 .rfl

theorem LE_Interp.bvar_iff : LE_Interp ρ m (.bvar i) ↔ m ≤ ρ i :=
  ⟨fun | .bot => TShape.bot_le' | .bvar h => h, .bvar⟩

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort (u ≠ .zero) := by
  generalize eq : SExpr.sort u = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | sort h => exact h.trans TShape.sort_eqv.1

theorem LE_Interp.le_sort' (H : LE_Interp ρ m (.sort u)) : m.2 ≤ .sort (u ≠ .zero) :=
  (TShape.LE.lift_r (Nat.zero_le _)).1 H.le_sort

theorem LE_Interp.RHS.mono (h : m ≤ m')
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R' a A)
    (H : RHS m1 m2 R m' r) : RHS m1 m2 R' m r := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | const h1 => exact .const (hR h h1)
  | var h1 => exact .var (h.trans h1)
  | app hf ha h1 ihf iha => exact .app (ihf .rfl) (iha .rfl) (h.trans h1)

theorem LE_Interp.Const.mono (h : m ≤ m')
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R' a A)
    (H : Const c ls R rargs m') : Const c ls R' rargs m := by
  induction H generalizing m with
  | lam h1 h2 h3 ih => exact .lam h1 (ih · · · .rfl) (h.trans h3)
  | ctor h1 => exact .ctor (h.trans h1)
  | pat h1 h2 h3 => exact .pat h1 h2 (h3.mono h hR)

theorem LE_Interp.mono (h : m ≤ m') (H : LE_Interp ρ m' M) : LE_Interp ρ m M := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | bvar h1 => exact .bvar (h.trans h1)
  | sort h1 => exact .sort (h.trans h1)
  | app hf ha h1 => exact .app hf ha (h.trans h1)
  | lam ha hdom hbody h1 => exact .lam ha hdom hbody (h.trans h1)
  | forallE hb hb' hdom hbody h1 => exact .forallE hb hb' hdom hbody (h.trans h1)
  | @const _ _ _ _ _ _ _ _ _ R h1 h2 h3 h4 h5 h6 _ _ ih2 =>
    refine .const (R := fun a A => ∃ a', a ≤ a' ∧ R a' A) h1 h2
      (h.trans h3) h4 h5 (h6.mono h fun h hr => ⟨_, h, hr⟩) ?_
    rintro m A ⟨_, a1, a2⟩; exact ih2 _ _ a2 a1

theorem LE_Interp.mono_l (hρ : ρ.LE ρ') (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (h1.trans (hρ _))
  | sort h1 => exact .sort h1
  | app _ _ h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | const h1 h2 h3 h4 _ h6 _ ihA ihR => exact .const h1 h2 h3 h4 (ihA hρ) h6 (ihR · · · hρ)

theorem LE_Interp.unlift (le : m.1 ≤ n)
    (H : LE_Interp ρ (m.2.lift n).T M) : LE_Interp ρ m M := H.mono (TShape.lift_eqv le).2

theorem LE_Interp.RHS.mono_l (hm : ∀ p, m2' p ≤ m2 p) (H : RHS m1 m2' R m r) : RHS m1 m2 R m r := by
  induction H  with try subst eq
  | bot => exact .bot
  | const h1 => exact .const h1
  | app hf ha h1 ihf iha => exact .app ihf iha h1
  | @var _ path h1 => exact .var (h1.trans (hm path))

theorem LE_Interp.Matches.lift (le : n ≤ n') (H : Matches (n := n) p c ls rargs m1 m2) :
    ∃ m2', Matches p c ls (rargs.map (.lift n')) m1 m2' ∧ ∀ p, m2 p ≤ m2' p ∧ m2' p ≤ m2 p := by
  induction H generalizing n' with
  | const => exact ⟨_, .const, nofun⟩
  | var _ ih =>
    have ⟨m2', h1, h2⟩ := ih le; exact ⟨_, .var h1, (·.casesOn (TShape.lift_eqv le).symm h2)⟩
  | app _ _ ih1 ih2 =>
    have ⟨m2f, f1, f2⟩ := ih1 le; let n' + 1 := n'
    have ⟨m2a, a1, a2⟩ := ih2 (Nat.le_of_succ_le_succ le)
    exact ⟨_, List.map_reverse ▸ f1.app a1, by exact (·.casesOn f2 a2)⟩

theorem LE_Interp.Const.lift (hn : n₁ ≤ n₂)
    (H : Const (n := n₁) c ls R rargs m) : Const c ls R (rargs.map (.lift n₂)) m := by
  induction H generalizing n₂ with
  | lam h1 h2 h3 ih =>
    -- rename_i k f _ n _
    refine .lam (Nat.le_trans h1 hn) (fun _ _ h => ?_) h3
    have := ih _ _ h hn; rwa [List.map, Shape.lift_lift (.inl h1)] at this
  | ctor h1 => exact .ctor <| List.map_reverse ▸ h1.trans (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | pat h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := h2.lift hn
    exact .pat h1 a1 <| h3.mono_l (a2 · |>.1)

theorem LE_Interp.lift (le : m.1 ≤ n)
    (H : LE_Interp ρ m M) : LE_Interp ρ (m.2.lift n).T M := H.mono (TShape.lift_eqv le).1

theorem LE_Interp.RHS.closed
    (H : RHS m1 m2 R m r) : RHS m1 m2 (fun e A => A.ClosedN ∧ R e A) m r := by
  induction H with
  | bot => exact .bot
  | @const _ _ _ cl h1 => exact .const ⟨cl.mkS.instL, h1⟩
  | var h1 => exact .var h1
  | app hf ha h1 ih_f ih_a => exact .app ih_f ih_a h1

theorem LE_Interp.Const.closed
    (H : Const c ls R rargs m) : Const c ls (fun e A => A.ClosedN ∧ R e A) rargs m := by
  induction H with
  | lam h1 _ h3 ih => exact .lam h1 ih h3
  | ctor h1 => exact .ctor h1
  | pat h1 h2 h3 => exact .pat h1 h2 h3.closed

theorem LE_Interp.weak'_iff (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    LE_Interp ρ' m (M.lift' l) ↔ LE_Interp ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed ?_
      · exact ih1 _ h <| (Params.henv.closedC h1).mkS.instL.lift'_eq .zero
      · rintro m A ⟨a1, a2⟩; exact ih2 _ _ a2 _ h <| a1.lift'_eq .zero
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons (fun i => by cases i <;> simp [Valuation.push, h])
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons (fun i => by cases i <;> simp [Valuation.push, h])
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed ?_
      · exact (Params.henv.closedC h1).mkS.instL.lift'_eq .zero ▸ ih1 _ h
      · rintro m A ⟨a1, a2⟩; exact a1.lift'_eq .zero ▸ ih2 _ _ a2 _ h

theorem LE_Interp.weak_iff : LE_Interp (ρ.push x) m M.lift ↔ LE_Interp ρ m M :=
  LE_Interp.weak'_iff (.skip .refl) (fun _ => rfl)

theorem LE_Interp.weak (H : LE_Interp ρ m M) : LE_Interp (ρ.push x) m M.lift :=
  weak_iff.2 H

private theorem LE_Interp.compat_join {m₁ m₂ : TShape}
    (hρ : ρ'.LE ρ) (H1 : LE_Interp ρ' m₁ M) (H2 : LE_Interp ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M := by
  -- have lift {ρ M n₁ n₂ m₁ m₂ n n'} (le : n ≤ n')
  --     (H : @Joinable ρ M n₁ n₂ m₁ m₂ n) : Joinable ρ M m₁ m₂ n' := by
  --   have := And.intro ((Shape.Compat.lift le).2 H.2.1) (Shape.lift_join le ▸ H.2.2.lift le)
  --   rw [Shape.lift_lift (.inl H.1.1), Shape.lift_lift (.inl H.1.2)] at this
  --   exact ⟨⟨Nat.le_trans H.1.1 le, Nat.le_trans H.1.2 le⟩, this⟩
  -- have unlift {ρ M n₁ n₂ m₁ m₂ n n'} (le₁ : n₁ ≤ n) (le₂ : n₂ ≤ n) (le : n ≤ n')
  --     (H : @Joinable ρ M n₁ n₂ m₁ m₂ n') : Joinable ρ M m₁ m₂ n := by
  --   refine ⟨⟨le₁, le₂⟩, (Shape.Compat.lift le).1 ?_, .unlift le <| Shape.lift_join le ▸ ?_⟩
  --   · rw [Shape.lift_lift (.inl le₁), Shape.lift_lift (.inl le₂)]; exact H.2.1
  --   · rw [Shape.lift_lift (.inl le₁), Shape.lift_lift (.inl le₂)]; exact H.2.2
  have mk {m₁ m₂ m ρ M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : LE_Interp ρ m M) :
      m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M :=
    have := TShape.Compat.def'.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((TShape.Join.mk this _).2 ⟨H1, H2⟩)⟩

    -- have le := Nat.max_le.2 ⟨le₁, le₂⟩
    -- have l₁ := Nat.le_max_left n₁ n₂; have l₂ := Nat.le_max_right n₁ n₂
    -- have := Shape.Compat.def.2 ⟨_, H1, H2⟩
    -- refine ⟨(Shape.Compat.lift le).1 ?_, ?_⟩
    -- · rwa [Shape.lift_lift (.inl l₁), Shape.lift_lift (.inl l₂)]
    -- · have := (Shape.Join.mk this _).2 ⟨H1, H2⟩
    --   refine .unlift le <| Shape.lift_join le ▸ ?_
    --   rw [Shape.lift_lift (.inl l₁), Shape.lift_lift (.inl l₂)]; exact H.mono this
  -- have mk' {n₁ n₂} {m₁ : Shape n₁} {m₂ : Shape n₂} {m : Shape (max n₁ n₂)} {ρ M} :
  --     m₁.lift ≤ m → m₂.lift ≤ m → LE_Interp ρ m M → Joinable ρ M m₁ m₂ (max n₁ n₂) :=
  --   mk (Nat.le_max_left ..) (Nat.le_max_right ..)
  have bot_r {m₁ n₂ ρ' ρ M} (hρ : ρ'.LE ρ) (H : LE_Interp ρ' m₁ M) :
      m₁.Compat (Shape.bot (n := n₂)).T ∧ LE_Interp ρ (m₁.join (Shape.bot (n := n₂)).T) M :=
    mk .rfl TShape.bot_le' (H.mono_l hρ)
  induction H1 generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl H2
  | sort h1 =>
    cases H2 with | bot => exact bot_r hρ (.sort h1) | sort h2
    exact mk h1 (h2.trans TShape.sort_eqv.2) (.sort .rfl)
  | bvar h1 =>
    cases H2 with | bot => exact bot_r hρ (.bvar h1) | bvar h2
    exact mk (h1.trans (hρ _)) h2 .bvar'
  | app hf ha h1 ih_f ih_a =>
    cases H2 with | bot => exact bot_r hρ (.app hf ha h1) | app hf' ha' h1'
    have ⟨cf, jf⟩ := ih_f hρ hf'
    have ⟨ca, ja⟩ := ih_a hρ ha'
    have hf := (TShape.Join.mk cf).le
    have ha := (TShape.Join.mk ca).le
    refine have le' := Nat.add_max_add_right .. ▸ Nat.le_refl _; mk ?_ ?_ ((jf.lift le').app' ja)
    · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
    · exact h1'.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2
  | lam ha hdom he h1 ih_a ih_f =>
    cases H2 with | bot => exact bot_r hρ (.lam ha hdom he h1) | lam ha' hdom' he' h1'
    rename_i ρ' n₁ a₁ A f₁ F m₁ n₂ a₂ f₂
    have ⟨ca, ia⟩ := ih_a hρ ha'
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have hx1 := Shape.HasDom.def.1 hdom _ _ h1
      have hx2 := Shape.HasDom.def.1 hdom' _ _ h2
      exact ShapeFun.app_of_mem h1 ▸ ih_f _ hx1 (Valuation.LE.push.2 ⟨hρ, j1⟩) <|
        ShapeFun.app_of_mem h2 ▸ he' _ hx2 |>.mono_l (Valuation.LE.push.2 ⟨.rfl, j2⟩)
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : ShapeFun.Compat Shape.Compat (ShapeFun.lift (Shape.lift _) f₁)
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) f₂) := by
      simp only [ShapeFun.Compat, List.all_eq_true, decide_eq_true_eq, ShapeFun.lift,
        List.all_map, Function.comp_apply]
      exact fun (x₁, y₁) h1 (x₂, y₂) h2 hc => (hC h1 h2 hc).1
    have jf := ShapeFun.Join.mk cf
    have hdom := (Shape.HasDom.lift le₁).2 hdom
    have hdom' := (Shape.HasDom.lift le₂).2 hdom'
    refine mk (h1.trans ?_) (h1'.trans ?_) <|
      .lam' ia (hdom.join hdom' cf ca) fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 jf.le.1
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 jf.le.2
    have ⟨_, _, a1, a2', a3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) f₁) x
    obtain ⟨⟨x₁, y₁⟩, a2, ⟨⟩⟩ := List.mem_map.1 a2'
    have ⟨_, _, b1, b2', b3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) f₂) x
    obtain ⟨⟨x₂, y₂⟩, b2, ⟨⟩⟩ := List.mem_map.1 b2'
    have a1' : x₁.T ≤ x.T := (TShape.LE.lift_l le₁).2 a1
    have a2' : x₂.T ≤ x.T := (TShape.LE.lift_l le₂).2 b1
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', a2'⟩
    have ⟨_, hj⟩ := hC a2 b2 hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', a2'⟩⟩) |>.mono ?_
    refine Shape.LE.T_iff (a := ShapeFun.app _ x) (b := Shape.join _ _) |>.2 ?_
    exact a3 ▸ b3 ▸ (Shape.Join.iff.1 (jf.app x)).2.2
  | forallE hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.forallE hb ha hdom he h1) | forallE hb2 ha2 hdom2 he2 h12
    rename_i ρ' n₁ b₁ b₁' B f₁ F m₁ n₂ b₂ b₂' f₂
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have hx1 := Shape.HasDom.def.1 hdom _ _ h1
      have hx2 := Shape.HasDom.def.1 hdom2 _ _ h2
      exact ShapeFun.app_of_mem h1 ▸ ih_f _ hx1 (Valuation.LE.push.2 ⟨hρ, j1⟩) <|
        ShapeFun.app_of_mem h2 ▸ he2 _ hx2 |>.mono_l (Valuation.LE.push.2 ⟨.rfl, j2⟩)
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : ShapeFun.Compat Shape.Compat (ShapeFun.lift (Shape.lift _) f₁)
        (ShapeFun.lift (Shape.lift (max n₁ n₂)) f₂) := by
      simp only [ShapeFun.Compat, List.all_eq_true, decide_eq_true_eq, ShapeFun.lift,
        List.all_map, Function.comp_apply]
      exact fun (x₁, y₁) h1 (x₂, y₂) h2 hc => (hC h1 h2 hc).1
    have jb := Shape.Join.mk cb; have jf := ShapeFun.Join.mk cf
    have hdom := (Shape.HasDom.lift le₁).2 hdom
    have hdom2 := (Shape.HasDom.lift le₂).2 hdom2
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .forallE' ib ia (hdom.join hdom2 cf ca) fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 (Shape.LE.def.2 ⟨jb.le.1, jf.le.1⟩)
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 (Shape.LE.def.2 ⟨jb.le.2, jf.le.2⟩)
    have ⟨_, _, a1, a2', a3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) f₁) x
    obtain ⟨⟨x₁, y₁⟩, a2, ⟨⟩⟩ := List.mem_map.1 a2'
    have ⟨_, _, b1, b2', b3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) f₂) x
    obtain ⟨⟨x₂, y₂⟩, b2, ⟨⟩⟩ := List.mem_map.1 b2'
    have a1' : x₁.T ≤ x.T := (TShape.LE.lift_l le₁).2 a1
    have a2' : x₂.T ≤ x.T := (TShape.LE.lift_l le₂).2 b1
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', a2'⟩
    have ⟨_, hj⟩ := hC a2 b2 hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', a2'⟩⟩) |>.mono ?_
    refine Shape.LE.T_iff (a := ShapeFun.app _ x) (b := Shape.join _ _) |>.2 ?_
    exact a3 ▸ b3 ▸ (Shape.Join.iff.1 (jf.app x)).2.2
  | const h1 h2 h3 h4 h5 h6 h7 =>
    cases H2 with
    | bot => exact bot_r hρ (.const h1 h2 h3 h4 h5 h6 h7) | const a1 a2 a3 a4 a5 a6 a7
    cases h1.symm.trans a1
    sorry

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ :=
  (compat_join .rfl H1 H2).1

theorem LE_Interp.join' (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ (m₁.join m₂) M :=
  (compat_join .rfl H1 H2).2

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M :=
  (H1.join' H2).mono ((J _).2 (TShape.Join.mk (H1.compat H2)).le)

theorem LE_Interp.subst : LE_Interp ρ m (M.subst σ) ↔
    ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · induction M generalizing m σ ρ with
    | bvar j =>
      refine ⟨fun k => if k = j then m else ⟨0, .bot⟩, ?_, fun k => ?_⟩
      · exact .bvar (by simp [TShape.LE.rfl])
      · dsimp; by_cases eq : k = j
        · exact if_pos eq ▸ eq ▸ H
        · exact if_neg eq ▸ .bot
    | sort => exact ⟨.nil, .sort H.le_sort, fun _ => .bot⟩
    | const =>
      cases H with | bot => exact ⟨.nil, .bot, fun _ => .bot⟩ | const
      sorry
    | app F A _ ih_F ih_A =>
      cases H with | bot => exact ⟨.nil, .bot, fun _ => .bot⟩ | app hf ha h1
      have ⟨ρ₁, hF, h₁⟩ := ih_F hf
      have ⟨ρ₂, hA, h₂⟩ := ih_A ha
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | lam A F ih_A ih_F =>
      cases H with
      | bot => exact ⟨.nil, .bot, fun _ => .bot⟩ | @lam _ n₁ a _ f _ m' ha hdom hbody h1
      suffices ∃ ρ', LE_Interp ρ' a.T A ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F by
        have ⟨ρ', ha, hρ, H⟩ := this
        refine ⟨ρ', .lam ha hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', y', a1, a2, rfl⟩ := ShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, Shape.LE.T a1⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) :=
        ih_F (ShapeFun.app_of_mem h ▸ hbody _ (Shape.HasDom.def.1 hdom _ _ h))
      clear h1 hdom hbody
      have ⟨ρA, ha, hρA⟩ := ih_A ha
      induction f with | nil => exact ⟨ρA, ha, hρA, nofun⟩ | cons x f ih
      have ⟨⟨ρ₁, hy, hρ₁⟩, H⟩ := List.forall_mem_cons.1 H
      have ⟨ρ₂, ha, hρ₂, H⟩ := ih H
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha.mono_l hj2, fun i => ?_, List.forall_mem_cons.2 ?_⟩
      · exact (hρ₁' i).join' (hρ₂ i)
      refine ⟨hy.mono_l ?_, fun _ h => (H _ h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)⟩
      rw [← (by funext i; cases i <;> rfl : ρ₁'.push (ρ₁ 0) = ρ₁)]
      exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
    | forallE B F ih_B ih_F =>
      cases H with
      | bot => exact ⟨.nil, .bot, fun _ => .bot⟩ | @forallE _ n₁ b _ b' f _ m' hb hb' hdom hbody h1
      suffices ∃ ρ', LE_Interp ρ' b.T B ∧ LE_Interp ρ' b'.T B ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', y', a1, a2, rfl⟩ := ShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, Shape.LE.T a1⟩
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) :=
        ih_F (ShapeFun.app_of_mem h ▸ hbody _ (Shape.HasDom.def.1 hdom _ _ h))
      clear h1 hdom hbody
      induction f with
      | nil =>
        have ⟨ρ₁, hb, hρ₁⟩ := ih_B hb
        have ⟨ρ₂, hb', hρ₂⟩ := ih_B hb'
        have hc : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat (hρ₂ i)
        have ⟨hj1, hj2⟩ := hc.le_join
        refine ⟨ρ₁.join ρ₂, hb.mono_l hj1, hb'.mono_l hj2, fun i => ?_, nofun⟩
        exact (hρ₁ i).join' (hρ₂ i)
      | cons x f ih =>
        have ⟨⟨ρ₁, hy, hρ₁⟩, H⟩ := List.forall_mem_cons.1 H
        have ⟨ρ₂, hb₂, hb'₂, hρ₂, H⟩ := ih H
        let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
        have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
        have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
        have ⟨hj1, hj2⟩ := this.le_join
        refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2, fun i => ?_, List.forall_mem_cons.2 ?_⟩
        · exact (hρ₁' i).join' (hρ₂ i)
        refine ⟨hy.mono_l ?_, fun _ h => (H _ h).mono_l <| Valuation.LE.push.2 ⟨hj2, .rfl⟩⟩
        rw [← (by funext i; cases i <;> rfl : ρ₁'.push (ρ₁ 0) = ρ₁)]
        exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact (h _).mono h1
    | app hf ha h1 ih_f ih_a => exact .app (ih_f h) (ih_a h) h1
    | lam ha hdom hbody h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed fun _ _ ⟨a1, a2⟩ => ?_
      · exact (Params.henv.closedC h1).mkS.instL.subst_eq .zero ▸ ih1 h
      · exact a1.subst_eq .zero ▸ ih2 _ _ a2 h

theorem LE_Interp.inst : LE_Interp ρ f (F.inst A) ↔
    ∃ a, LE_Interp (ρ.push a) f F ∧ LE_Interp ρ a A := by
  refine ⟨fun H => ?_, fun ⟨a, hF, hA⟩ => ?_⟩
  · have ⟨ρ', hF, hσ⟩ := LE_Interp.subst.1 H
    refine ⟨_, hF.mono_l ?_, hσ 0⟩
    intro | 0 => exact .rfl | i+1 => exact (bvar_iff.1 (hσ (i+1)) :)
  · exact (LE_Interp.subst (σ := .one A)).2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem LE_Interp.forallE_inv {b} {f : ShapeFun n} {B F}
    (H : LE_Interp ρ (Shape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ {{X x}}, LE_Interp ρ x.T X → LE_Interp ρ (f.app x).T (F.inst X) := by
  let .forallE (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)] at le
  simp [Shape.lift, Shape.LE.def] at le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 le.1), fun X x hx => ?_⟩
  obtain ⟨x', _, le1, hf, rfl⟩ := ShapeFun.app_eq f x
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 le.2 _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hf, ⟨⟩⟩ := List.mem_map.1 hf'
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  exact hiB _ (Shape.HasDom.def.1 hd _ _ hf)
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.def le₂ le₁).2 le2⟩)
    |>.mono (ShapeFun.app_of_mem hf ▸ (TShape.LE.def' (a := (f.app x).T) (b := y₁.T)).2 lf)

theorem LE_Interp.forallE_inv' {b} {f : ShapeFun n} {B F}
    (H : LE_Interp ρ (Shape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ x, LE_Interp (ρ.push x.T) (f.app x).T F := by
  have ⟨h1, h2⟩ := H.forallE_inv; refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x.T) H).forallE_inv.2 .bvar0
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.lam_inv {f : ShapeFun n} {B F}
    (H : LE_Interp ρ (Shape.T (n := n+1) (.lam f)) (.lam B F))
    {{X x}} (hx : LE_Interp ρ x.T X) : LE_Interp ρ (f.app x).T (F.inst X) := by
  let .lam (n := n') (f := f₁) _ hd hiF le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)] at le
  simp [Shape.lift, Shape.LE.def] at le
  obtain ⟨x', _, le1, hf, rfl⟩ := ShapeFun.app_eq f x
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 le _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hf, ⟨⟩⟩ := List.mem_map.1 hf'
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  exact hiF _ (Shape.HasDom.def.1 hd _ _ hf)
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.def le₂ le₁).2 le2⟩)
    |>.mono (ShapeFun.app_of_mem hf ▸ (TShape.LE.def' (a := (f.app x).T) (b := y₁.T)).2 lf)

theorem LE_Interp.lam_inv' {f : ShapeFun n} {B F}
    (H : LE_Interp ρ (Shape.T (n := n+1) (.lam f)) (.lam B F)) (x) :
    LE_Interp (ρ.push x.T) (f.app x).T F := by
  have := (LE_Interp.weak (x := x.T) H).lam_inv .bvar0
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

inductive Valuation.Fits : (Γ Δ : List SExpr) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {a}, LE_Interp ρ a A → ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

def InterpTyped (ρ : Valuation) (m : TShape) (M A : SExpr) :=
  ∃ m' a, m ≤ m' ∧ LE_Interp ρ m' M ∧ LE_Interp ρ a A ∧ m'.HasType a

theorem InterpTyped.bot : InterpTyped ρ (Shape.T (n := n) .bot) M A :=
  ⟨_, _, .rfl, .bot, .bot, Shape.HasType.T <| .bot' <| .bot .sort⟩

theorem InterpTyped.mk (le : m ≤ m') (h_m : LE_Interp ρ m' M) (h_a : LE_Interp ρ a A)
    (h_type : m'.HasType a) : InterpTyped ρ m M A := ⟨_, _, le, h_m, h_a, h_type⟩

theorem InterpTyped.out (H : InterpTyped ρ m M A) :
    ∃ n' m' a, m.1 ≤ n' ∧ m ≤ m'.T ∧
      LE_Interp ρ (m' : Shape n').T M ∧ LE_Interp ρ a.T A ∧ m'.HasType a := by
  let ⟨m', a, a1, a2, a3, a4⟩ := H
  let k := max m.1 (max m'.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  exact ⟨_, _, _, hk.1, a1.trans (TShape.lift_eqv hk.2.1).2,
    a2.lift hk.2.1, a3.lift hk.2.2, (TShape.HasType.def hk.2.1 hk.2.2).1 a4⟩

theorem LE_Interp.sound_bot :
    (LE_Interp ρ (Shape.T (n := n) .bot) M ↔ LE_Interp ρ (Shape.T (n := n) .bot) N) ∧
    (LE_Interp ρ (Shape.T (n := n) .bot) M → InterpTyped ρ (Shape.T (n := n) .bot) M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem LE_Interp.sound_app
    (H1 : ∀ {m}, LE_Interp ρ m F → InterpTyped ρ m F (.forallE A B))
    (H2 : ∀ {b}, LE_Interp ρ b (B.inst X) →
      ∃ b', b ≤ b' ∧ LE_Interp ρ b' (B.inst X) ∧ b'.HasType .type)
    (h1 : LE_Interp ρ m (F.app X pat)) : InterpTyped ρ m (F.app X pat) (B.inst X) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  rename_i nf f_shape a_sh
  have ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := H1 h1
  have hf : ¬f_ts ≤ .bot := fun h => by
    cases TShape.le_bot.1 (le_f.trans h); erw [Shape.bot_app] at h3
    exact hm (h3.trans TShape.bot_le')
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf c1
  let k := max (max n₂ m) (max npi nf)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have a3' := LE_Interp.forallE b1 b2 b3 b4 (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)).1
  have h_Binst := a3'.forallE_inv.2 (h2.lift hk.2.2)
  have ⟨a', le', g1, g2⟩ := H2 h_Binst
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have ⟨_, e1, e2, e3⟩ := c1.2.1 (Shape.lift _ a_sh)
  refine ⟨_, a', ?_, .app' (a2.lift (Nat.succ_le_succ hk.1.1)) (h2.lift hk.2.2), g1, ?_⟩
  · refine h3.trans (TShape.app_mono ?_ (TShape.lift_eqv hk.2.2).2)
    exact le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2
  · have b6 := (TShapeFun.LE.def hk.1.2 hk.2.1).1 b6
    have le := (ShapeFun.app_mono_l b6 _).trans (ShapeFun.app_mono_r e1)
    refine g2.mono_r (le.T.trans le') <| Shape.HasType.T ?_
    exact (c1.2.2 _ e2).mono_l (ShapeFun.app_mono_r e1) e3

theorem LE_Interp.sound_lam
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type)
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e F → InterpTyped (ρ.push x) e F B)
    (h1 : LE_Interp ρ m (A.lam F)) : InterpTyped ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @lam _ n a _ f _ _ h1 h2 h3 h4
  have ⟨a', a1, a2, a3⟩ := H1 h1
  suffices ∃ n', n ≤ n' ∧ ∃ f' b : ShapeFun n', ShapeFun.LE (ShapeFun.lift (Shape.lift _) f) f' ∧
      Shape.HasDom f' (a.lift _) ∧ Shape.HasDom b (a.lift _) ∧ ∀ x, x.HasType (a.lift _) →
      LE_Interp (ρ.push x.T) (f'.app x).T F ∧ LE_Interp (ρ.push x.T) (b.app x).T B ∧
      (f'.app x).HasType (b.app x) by
    have ⟨n', le', f₁, b, a1, a2, a3, a4⟩ := this; simp [forall_and] at a4
    have h1' := h1.lift le'
    refine ⟨_, _, ?_, .lam' h1' a2 a4.1, .forallE' h1' h1' a3 a4.2.1, ?_⟩
    · exact h4.trans ((TShape.LE.lift_l (Nat.succ_le_succ le')).2 (Shape.LE.def.2 a1))
    · exact Shape.HasType.T <| .lam ⟨⟨a3, fun _ h => (a4.2.2 _ h).isType⟩, a2, a4.2.2⟩
  replace h3 (p) (h : p ∈ f) : p.1.HasType a ∧ LE_Interp (ρ.push p.1.T) p.2.T F :=
    have := Shape.HasDom.def.1 h2 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h3 _ this⟩
  have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : ShapeFun k,
      f'.map Prod.fst = f.map (·.1.lift _) ∧ b.map Prod.fst = f.map (·.1.lift _) ∧
      ∀ x fx, (x, fx) ∈ f → ∃ f'x bx, (x.lift _, f'x) ∈ f' ∧ (x.lift _, bx) ∈ b ∧
      fx.lift _ ≤ f'x ∧ LE_Interp (ρ.push x.T) f'x.T F ∧ LE_Interp (ρ.push x.T) bx.T B ∧
      f'x.HasType bx := by
    clear h2 h4
    induction f with
    | nil => exact ⟨_, Nat.le_refl _, fun _ _ => ⟨[], [], by simp⟩⟩
    | cons p _ ih; let (x, fx) := p
    simp only [List.mem_cons, forall_eq_or_imp] at h3
    have ⟨k₁, le1, H1⟩ := ih h3.2
    have ⟨f'x, bx, le, b1, b2, b3⟩ := H2 h1 h3.1.1.T h3.1.2
    let m' := max f'x.1 bx.1
    have lf := Nat.le_max_left f'x.1 bx.1; have lb := Nat.le_max_right f'x.1 bx.1
    refine ⟨k₁.max m', Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nfk := Nat.le_trans lf le₂; have le_nbk := Nat.le_trans lb le₂
    have ⟨f', b, a1, a2, a3⟩ := H1 _ le₁
    refine ⟨(x.lift _, f'x.2.lift _) :: f', (x.lift _, bx.2.lift _) :: b, ?_⟩
    simp [or_imp, forall_and, *]
    exact ⟨.inl <| .inl ⟨(TShape.LE.def (Nat.le_trans le1 le₁) le_nfk).1 le,
      b1.lift le_nfk, b2.lift le_nbk, (TShape.HasType.def le_nfk le_nbk).1 b3⟩, by grind⟩
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
    · exact c4.mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le).2 b1⟩
    · have ⟨_, _, _, c2, _, _, c5, _⟩ := a3 _ _ b3'
      cases (ShapeFun.uniq_l b2' c2 .rfl .rfl).2
      exact c5.mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le).2 b1'⟩
    · refine .mono_r (r := true) (ShapeFun.app_of_mem c2 ▸ ShapeFun.app_mono_r b1) ?_ c6
      have ⟨_, _, _, c2, _, _, c5, c6⟩ := a3 _ _ b3'
      cases (ShapeFun.uniq_l b2' c2 .rfl .rfl).2
      exact c6.isType

theorem LE_Interp.sound_forallE
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (u ≠ .zero)))
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e B → InterpTyped (ρ.push x) e B (.sort v))
    (h1 : LE_Interp ρ m (A.forallE B)) :
    InterpTyped ρ m (A.forallE B) (.sort (.imax u v)) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @forallE _ n b₀ _ b f _ _ h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∃ n', n ≤ n' ∧ ∃ f', ShapeFun.LE (ShapeFun.lift (Shape.lift n') f) f' ∧
      Shape.HasDom f' (b.lift _) ∧ ∀ x, x.HasType (b.lift _) →
      LE_Interp (ρ.push x.T) (f'.app x).T B ∧ (f'.app x).HasType (.sort (v ≠ .zero)) by
    have ⟨n', le', f₁, b1, b2, b3⟩ := this; simp [forall_and] at b3
    have hC : Shape.Compat b₀ b := by
      have := h1.compat h2
      rw [TShape.Compat.def (Nat.le_refl n) (Nat.le_refl n)] at this
      simpa [Shape.lift_self] using this
    have hJ := TShape.Join.mk (h1.compat h2)
    have hJ_n := Shape.Join.mk hC
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hJ h2)
    let k := max n' b₂.1
    have le₁ := Nat.le_max_right n' b₂.1
    have le₂ := Nat.le_max_left n' b₂.1
    have b₀_le_ca := (TShape.LE.def (Nat.le_trans le' le₂) le₁).1 (hJ.le.1.trans c1)
    have b_le_ca := (TShape.LE.def (Nat.le_trans le' le₂) le₁).1 (hJ.le.2.trans c1)
    have hJ' := (Shape.Join.lift (Nat.le_trans le' le₂)).2 hJ_n
    have b2' := Shape.lift_lift (.inl le') ▸ (Shape.HasDom.lift le₂).2 b2
    have le_forallE : Shape.T (n:=_+1) (.forallE b₀ f) ≤
        Shape.T (n:=_+1) (.forallE (b₂.2.lift k) (ShapeFun.lift (Shape.lift _) f₁)) := by
      rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le' le₂))]
      exact Shape.LE.def.2 ⟨b₀_le_ca, ShapeFun.lift_lift (.inl le') ▸ ShapeFun.lift_mono b1⟩
    have c_ht_k : (b₂.2.lift k).HasType .type :=
      (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3 |>.toType
    refine ⟨_, _, h5.trans le_forallE,
      .forallE' (c2.lift le₁)
        ((h2.lift le').lift le₂)
        ((Shape.HasDom.lift le₂).2 b2) (fun x h => ?_),
      .sort .rfl, ?_⟩
    · refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq ..; d3 ▸ ?_
      simp [ShapeFun.lift] at d2; obtain ⟨_, _, d2, rfl, rfl⟩ := d2
      have := ShapeFun.app_of_mem d2 ▸ b3.1 _ (Shape.HasDom.def.1 b2 _ _ d2)
      refine (this.mono_l ?_).lift le₂
      exact Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le₂).2 d1⟩
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [Shape.lift_self]
      refine .forallE ⟨.mono b_le_ca (Shape.lift_type (n := k) ▸ c_ht_k) b2', fun x h => ?_⟩
      have ⟨y, d1, d2, d3⟩ := b2' x
      refine have ⟨_, _, e1, e2, e3⟩ := ShapeFun.app_eq _ y; have d3' := e3 ▸ d3; ?_
      simp [ShapeFun.lift] at e2; obtain ⟨_, _, e2, rfl, rfl⟩ := e2
      refine .mono_l (ShapeFun.app_mono_r d1) d3 <|
        e3 ▸ Shape.lift_sort.symm ▸ (Shape.HasType.lift le₂).2 ?_
      simpa [← ShapeFun.app_of_mem e2] using b3.2 _ (Shape.HasDom.def.1 b2 _ _ e2)
  replace h4 (p) (h : p ∈ f) : p.1.HasType b ∧ LE_Interp (ρ.push p.1.T) p.2.T B :=
    have := Shape.HasDom.def.1 h3 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h4 _ this⟩
  have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : ShapeFun k,
      f'.map Prod.fst = f.map (·.1.lift _) ∧
      ∀ x fx, (x, fx) ∈ f → ∃ f'x, (x.lift _, f'x) ∈ f' ∧
      fx.lift _ ≤ f'x ∧ LE_Interp (ρ.push x.T) f'x.T B ∧ f'x.HasType (.sort (v ≠ .zero)) := by
    clear h3 h5
    induction f with
    | nil => exact ⟨_, Nat.le_refl _, fun _ _ => ⟨[], by simp⟩⟩
    | cons p _ ih; let (x, fx) := p
    simp only [List.mem_cons, forall_eq_or_imp] at h4
    have ⟨k₁, le1, H1⟩ := ih h4.2
    have ⟨f'x, _, le, b1, b2, b3⟩ := H2 h2 h4.1.1.T h4.1.2
    replace b3 : f'x.HasType (.sort (v ≠ .zero)) := .mono_r b2.le_sort .sort b3
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have ⟨f', a1, a2⟩ := H1 _ le₁
    refine ⟨(x.lift _, f'x.2.lift k) :: f', ?_⟩
    have b4 : (f'x.2.lift k).HasType (.sort (v ≠ .zero)) :=
      (TShape.HasType.def le₂ (Nat.zero_le k)).1 b3
    simp [or_imp, forall_and, *] at b4 ⊢
    exact ⟨.inl ⟨(TShape.LE.def (Nat.le_trans le1 le₁) le₂).1 le, b1.lift le₂, b4⟩, by grind⟩
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
    exact Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le).2 b1⟩

theorem LE_Interp.sound (H : Γ ⊢ M ≡ N : A)
    (W : Valuation.Fits Γ₀ Γ ρ) {m : TShape} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧
    (LE_Interp ρ m M → InterpTyped ρ m M A) := by
  have hsort' {ρ A U}
      (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
      {a} (h : LE_Interp ρ a A) :
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (U ≠ .zero)) :=
    have ⟨_, _, h1, h2, h3, h4⟩ := H h
    ⟨_, h1, h2, .mono_r h3.le_sort .sort h4⟩
  have hsort {ρ A U}
      (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
      {a} (h : LE_Interp ρ a A) :
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type :=
    have ⟨a', h1, h2, h3⟩ := hsort' H h; ⟨a', h1, h2, h3.toType⟩
  replace H := H.strong
  induction H generalizing m ρ with
  | @bvar _ i A h =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.bvar i = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    | bvar a1
    induction W generalizing i A with
    | nil => exact TShape.le_bot'.1 a1 ▸ .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    | cons _ h1 h2 h3 ih =>
      cases h with simp [Valuation.push] at a1
      | zero => exact ⟨_, _, a1, .bvar .rfl, h2.weak, h3⟩
      | succ h =>
        have ⟨_, _, le, h1, h2, h3⟩ := ih h a1
        exact ⟨_, _, le, h1.weak, h2.weak, h3⟩
  | symm _ ih =>
    refine ⟨(ih W).1.symm, fun h => ?_⟩
    have ⟨_, _, le, a1, a2, a3⟩ := (ih W).2 ((ih W).1.2 h)
    exact ⟨_, _, le, (ih W).1.1 a1, a2, a3⟩
  | trans _ _ _ _ ih1 ih2 =>
    refine ⟨(ih1 W).1.trans (ih2 W).1, fun h => ?_⟩
    have ⟨_, _, le, a1, a2, a3⟩ := (ih2 W).2 ((ih1 W).1.1 h)
    exact ⟨_, _, le, (ih1 W).1.2 a1, a2, a3⟩
  | @sort _ l =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.sort l = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    | sort h1 => exact .mk h1 (.sort .rfl) (.sort .rfl) (by simpa using .sort)
  | @const c _ _ ls =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.const c ls = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    | const => sorry -- TODO: const case needs adaptation
  | appDF _ _ _ _ _ ihA ihB ih1 ih2 ih3 =>
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, sound_app (ih1 W).2 (hsort (ih3 W).2)⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | app h1 h2 h3
    · exact .app ((ih1 W).1.1 h1) ((ih2 W).1.1 h2) h3
    · exact .app ((ih1 W).1.2 h1) ((ih2 W).1.2 h2) h3
  | @lamDF _ _ _ _ B _ body body' _ _ _ ih1 _ ih2 =>
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_lam (hsort (ih1 W).2) fun h1 h2 => (ih2 (W.cons (hsort (ih1 W).2) h1 h2)).2⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | lam h1 h2 h3 h4
    · refine .lam ((ih1 W).1.1 h1) h2 (fun _ h => ?_) h4
      exact (ih2 (W.cons (hsort (ih1 W).2) h1 h.T)).1.1 (h3 _ h)
    · refine .lam ((ih1 W).1.2 h1) h2 (fun _ h => ?_) h4
      exact (ih2 (W.cons (hsort (ih1 W).2) ((ih1 W).1.2 h1) h.T)).1.2 (h3 _ h)
  | @forallEDF _ A _ _ body body' v _ _ ih1 ih2 =>
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_forallE (hsort' (ih1 W).2) fun h1 h2 => (ih2 (W.cons (hsort (ih1 W).2) h1 h2)).2⟩ <;>
      try cases h with | bot => cases hm TShape.bot_le' | forallE h1 h2 h3 h4 h5
    · refine .forallE ((ih1 W).1.1 h1) ((ih1 W).1.1 h2) h3 (fun _ h => ?_) h5
      exact (ih2 (W.cons (hsort (ih1 W).2) h2 h.T)).1.1 (h4 _ h)
    · refine .forallE ((ih1 W).1.2 h1) ((ih1 W).1.2 h2) h3 (fun _ h => ?_) h5
      exact (ih2 (W.cons (hsort (ih1 W).2) ((ih1 W).1.2 h2) h.T)).1.2 (h4 _ h)
  | defeqDF _ _ ih1 ih2 =>
    refine ⟨(ih2 W).1, fun h => ?_⟩
    have ⟨_, _, h1, h2, h3, h4⟩ := (ih2 W).2 h
    exact ⟨_, _, h1, h2, (ih1 W).1.1 h3, h4⟩
  | beta _ _ _ _ ih1 ih2 ih3 =>
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih3 W).2⟩
    · cases h with | bot => cases hm TShape.bot_le' | @app _ n₁ _ _ _ _ a h1 h2 h3
      cases h1 with | bot => cases hm (h3.trans TShape.bot_eqv.1) | @lam _ n₂ _ _ f' _ _ h4 h5 h6 h7
      let k := max n₂ n₁; have hk := Nat.max_le.1 (Nat.le_refl k)
      have ⟨_, _, a1, a2, a3, a4⟩ := (ih2 W).2 h2
      obtain ⟨_, _, b1, b2, b3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift k) f') (a.lift k)
      obtain ⟨⟨x', y'⟩, b2', ⟨⟩⟩ := List.mem_map.1 b2
      refine LE_Interp.inst.2 ⟨_, ?_, h2.mono (m := x'.T) b1⟩
      refine (h6 _ (Shape.HasDom.def.1 h5 _ _ b2')).mono (h3.trans ((TShape.LE.def hk.2 hk.1).2 ?_))
      rw [Shape.lift_app hk.2, ShapeFun.lift_app hk.1]
      have h7' := (TShape.LE.def (Nat.succ_le_succ hk.2) (Nat.succ_le_succ hk.1)).1 h7
      refine (Shape.app_mono_l h7' _).trans ?_
      rw [Shape.lift, Shape.app, b3, ← ShapeFun.app_of_mem b2', ShapeFun.lift_app hk.1]; exact .rfl
    · have ⟨_, h1, h2⟩ := LE_Interp.inst.1 h
      have ⟨e, a, a1, a2, a3, a4⟩ := (ih2 W).2 h2
      let k := max m.1 (max e.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
      refine
        have := (Shape.HasDom.single (y := m.2.lift k)).2 ((TShape.HasType.def hk.2.1 hk.2.2).1 a4)
        .mono ?_ <| .app' (.lam' (a3.lift hk.2.2) this fun _ hx => ?_) (a2.lift hk.2.1)
      · rw [Shape.app, ShapeFun.single_app, if_pos .rfl]; exact (TShape.lift_eqv hk.1).2
      · simp [ShapeFun.single_app]; split <;> [skip; exact .bot]
        refine (h1.lift hk.1).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.trans ?_⟩
        sorry
  | @eta _ F _ _ _ _ ih1 ih2 =>
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih2 W).2⟩
    · have ⟨e, t, h1, h2, h3, h4⟩ := (ih2 W).2 h
      have ht : ¬t ≤ .bot := fun h => hm (h1.trans (h4.bot_r' h))
      cases h2 with
      | bot => cases hm (h1.trans TShape.bot_le')
      | @lam _ n _ _ f' _ _ h2a h2d h2f h2le
      cases h3 with | bot => cases ht TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases ht b5 | forallE b5 b6
      obtain c1 | ⟨n₂, g, rfl, c1⟩ := h4.ty_forallE_inv; · cases hm (h1.trans c1)
      have key : ∀ x y, (x, y) ∈ f' → y ≠ .bot →
          LE_Interp ρ (Shape.T (n := n+1) (.lam (ShapeFun.single x y))) F := by
        intro x y hmem hy
        have := ShapeFun.app_of_mem hmem ▸ h2f x (Shape.HasDom.def.1 h2d _ _ hmem)
        cases this with | bot => cases hy rfl | @app _ n' f _ _ _ a' c1 c2 c3
        cases f with | lam g => ?_ | _ => cases hy (TShape.le_bot.1 (c3.trans TShape.bot_le'))
        have ⟨x', y', hle, mem, appeq⟩ := ShapeFun.app_eq g a'
        have le₁ := Nat.le_max_left n' n; have le₂ := Nat.le_max_right n' n
        refine (LE_Interp.weak_iff.1 c1).mono ?_
        refine (TShape.LE.def (Nat.succ_le_succ le₂) (Nat.succ_le_succ le₁)).2 ?_
        rw [Shape.lift, ShapeFun.lift_single le₂]
        refine Shape.LE.def.2 <| ShapeFun.single_le.2 ?_
        refine ⟨x'.lift _, y'.lift _, List.mem_map.2 ⟨_, mem, rfl⟩, ?_, ?_⟩
        · exact (TShape.LE.def le₁ le₂).1 (hle.T.trans (LE_Interp.bvar_iff.1 c2))
        · exact (TShape.LE.def le₂ le₁).1 (c3.trans (c := y'.T) (appeq ▸ TShape.LE.rfl))
      have main (l : List (Shape n × Shape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g : Shape (n+1),
            (g = .bot ∨ ∃ l, g = .lam l) ∧
            (∀ z, g ≤ z ↔ ∀ x y, (x, y) ∈ l → y ≠ .bot → .lam (ShapeFun.single x y) ≤ z) ∧
            LE_Interp ρ g.T F := by
        induction l with | nil => exact ⟨.bot, .inl rfl, by simp, .bot⟩ | cons p l ih
        let (x, y) := p; simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, eq, a1, a2⟩ := ih H.2
        by_cases hy : y = .bot
        · exact ⟨g, eq, fun z => (a1 z).trans (by simp [or_imp, forall_and, hy]), a2⟩
        · have hJ := Shape.Join.mk <| Shape.Compat.T_iff.2 <| a2.compat (key _ _ H.1 hy)
          refine ⟨_, .inr ?_, fun z => (hJ z).trans ?_, a2.join hJ.T (key _ _ H.1 hy)⟩
          · obtain rfl | ⟨g, rfl⟩ := eq <;> exact ⟨_, rfl⟩
          · simp [a1, or_imp, forall_and, and_comm, hy]
      have ⟨g, _, a1, a2⟩ := main f' fun _ => id
      refine a2.mono (h2le.trans (Shape.LE.T ?_)) |>.mono h1
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
    · have ⟨m', f, a1, a2, a3, a4⟩ := (ih1 W).2 h
      have hm' : ¬m' ≤ .bot := fun h => hm (a1.trans h)
      have hf : ¬f ≤ .bot := fun h => hm' (a4.bot_r' h)
      cases a3 with | bot => cases hf TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases hf b5 | @forallE m _ _ _ _ b5 b6
      obtain c1 | ⟨n₂, g, rfl, c1⟩ := a4.ty_forallE_inv; · cases hm' c1
      exact .mono (a1.trans (TShape.lift_eqv (Nat.succ_le_succ (Nat.le_max_left ..))).2) <|
        .lam' ((b1.mono b5).lift (Nat.le_max_right ..)) c1.2.1 fun _ _ =>
        .app' (a2.lift (Nat.succ_le_succ (Nat.le_max_left ..))).weak .bvar0
  | @proofIrrel _ p h h' _ _ _ ih1 ih2 ih3 =>
    suffices ∀ {h h'}, InterpTyped ρ m h p → LE_Interp ρ m h → LE_Interp ρ m h' from
      ⟨⟨fun h => this ((ih2 W).2 h) h, fun h => this ((ih3 W).2 h) h⟩, (ih2 W).2⟩
    refine fun ⟨_, _, a1, a2, a3, a4⟩ h1 => .mono (?_ : m ≤ .bot) .bot
    have ⟨_, _, b1, b2, b3, b4⟩ := (ih1 W).2 a3
    have b4' := TShape.HasType.mono_r (by simpa using b3.le_sort) .sort b4
    exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))
  | extra h1 h2 _ _ ih1 ih2 =>
    refine ⟨?_, (ih1 W).2⟩
    let ⟨p, r, m1, m2, dfs, a1, a2, a3, a4, a5⟩ := Params.extra_pat Γ₀ h1 h2
    sorry

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
  | .bot | .lam _ | .ctor _ _ => True
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
    | ctor => cases hm.isType.unfold
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
    | ctor => cases hm.isType.unfold
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
      ((LR Γ).TyDefEq M N (m.lift n') ↔ (LR Γ).TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a)) :
    LRS.PiDefEq (LR Γ) B F₁ F₂ (b.lift n') (ShapeFun.lift (Shape.lift _) f) ↔
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
      refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) _) _; d3 ▸ ?_
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
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a))
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) (n := n') M N A₁ A₂
      (ShapeFun.lift (Shape.lift _) g) (a₁.lift _) (ShapeFun.lift (Shape.lift _) a₂) ↔
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
      have ⟨_, _, dg1, dg2, dg3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) g) p
      simp [ShapeFun.lift] at dg2; obtain ⟨qg, fg, dg2, rfl, rfl⟩ := dg2
      have ⟨_, _, da1, da2, da3⟩ := ShapeFun.app_eq (ShapeFun.lift (Shape.lift _) a₂) p
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
      (LRS.TyDefEq (n := n) (LR Γ) M N (m.lift _) ↔ (LR Γ).TyDefEq M N m)) ∧
    (∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      (LRS.DefEq (n := n) (LR Γ) M N A (m.lift _) (a.lift _) ↔ (LR Γ).DefEq M N A m a)) := by
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
        refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq (.lift (Shape.lift _) f) _; d3 ▸ ?_
        simp [ShapeFun.lift] at d2; obtain ⟨q, _, d2, rfl, rfl⟩ := d2
        have hq := Shape.HasDom.def.1 htpi.1 _ _ d2
        have v' := (ih.2 hq).1 ((LRS (LR Γ)).mono_l d1
          ((Shape.HasType.lift (Nat.le_succ k)).2 hq) hp v)
      · have ⟨r1, r2⟩ := hE.1 hq ha v'
        exact ⟨ShapeFun.app_of_mem d2 ▸ (ih.1 (htpi.2 _ hq)).2 r1,
               ShapeFun.app_of_mem d2 ▸ (ih.1 (htpi.2 _ hq)).2 r2⟩
      · exact ShapeFun.app_of_mem d2 ▸ (ih.1 (htpi.2 _ hq)).2 (hE.2 hq ha v')
  · intro M N A m a hma
    cases a with | bot | lam | ctor => rfl | sort r => exact h1 hma.toType | forallE a₁ a₂
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
    (LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a := by
  induction le with | refl => simp [Shape.lift_self] | step le ih
  rw [(Shape.lift_lift (.inl le)).symm, (Shape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((Shape.HasType.lift le).2 hma)).trans ih

theorem LR.TyDefEq.lift {m : Shape n} (le : n ≤ n') (hmt : m.HasType .type) :
    (LR Γ).TyDefEq (n := n') M N (m.lift _) ↔ (LR Γ).TyDefEq M N m := by
  induction le with | refl => simp [Shape.lift_self] | step le ih
  rw [(Shape.lift_lift (.inl le)).symm]
  exact (LR.lift_succ_aux.1 (Shape.lift_type ▸ (Shape.HasType.lift le).2 hmt)).trans ih

theorem LRS.PiDefEq.lift
    {b} {f : ShapeFun n} (le : n ≤ n') (htpi_a : Shape.HasTypePi f b true) :
    LRS.PiDefEq (LR Γ) (n := n') B F₁ F₂ (b.lift _) (ShapeFun.lift (Shape.lift _) f) ↔
    LRS.PiDefEq (LR Γ) B F₁ F₂ b f := lift_aux le htpi_a (LR.TyDefEq.lift le) (LR.DefEq.lift le)

theorem LRS.LamDefEq.lift {g : ShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : Shape.HasTypeLam g a₁ a₂)
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) M N A₁ A₂
      (ShapeFun.lift (Shape.lift _) g) (a₁.lift n') (ShapeFun.lift (Shape.lift _) a₂) ↔
    LRS.LamDefEq (LR Γ) M N A₁ A₂ g a₁ a₂ := lift_aux le htm (LR.DefEq.lift le) hEdge

def LR.Subst1 (Γ₀ : List SExpr) (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∀ {{n}} (a : Shape n), LE_Interp ρ a.T A₀ →
    (a.HasType .type → (∃ u, Γ₀ ⊢ A ≡ A' : .sort u) ∧ (LR Γ₀).TyDefEq A A' a) ∧
    (∀ {{m : Shape n}}, LE_Interp ρ m.T (.bvar i) → m.HasType a → (LR Γ₀).DefEq x x' A m a)

inductive LR.SubstWF (Γ₀ : List SExpr) : Subst → Subst → List SExpr → Valuation → Prop where
  | id : LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a → Γ ⊢ A : .sort u →
    LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

theorem LR.SubstWF.fits : LR.SubstWF Γ₀ σ σ' Γ ρ → ρ.Fits Γ₀ Γ
  | .id => .nil
  | .cons W h1 h2 h3 _ _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.toSubstEq : LR.SubstWF Γ₀ σ σ' Γ ρ → Ctx.SubstEq Γ₀ σ σ' Γ
  | .id => .nil
  | .cons W _ _ _ hA h0 => .cons W.toSubstEq hA h0.1

theorem LR.SubstWF.left (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨h0.1.hasType.1, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _).left_ty h2⟩
    · exact (LR _).left <| (h0.2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨?_, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (h0.2 (n := 0) _ .bot).1 (.bot .sort)
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (h0.2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _).symm_ty h2⟩
    · let ⟨_, h2⟩ := (h0.2 a ha).1 hmem.isType
      exact (LR _).conv h2 ((LR _).symm ((h0.2 a ha).2 hM hmem))
