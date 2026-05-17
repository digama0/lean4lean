module

/-!
# Partial formalization of Coquand & Huber, "An Adequacy Theorem for Dependent Type Theory"
https://doi.org/10.1007/s00224-018-9879-9

This might be useful for others, I just wanted to make sure I understood
the monotonicity theorem right.
-/

axiom mySorry : α

inductive Shape0 : Type where
  | bot : Shape0
  | U : Shape0

inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | U : ShapeS Shape
  | pi : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape

def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.U : ∀ {n}, Shape n
  | 0 => Shape0.U
  | _+1 => ShapeS.U

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, _, _ | _+1, .bot, _ | _+1, _, .bot | _+1, .U, .U => true
  | _+1, .pi s f, .pi s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _, _, _ => false

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .U, .U | _+1, .U, .U => True --j ≤ i
  | _+1, .pi s f, .pi s' f' => s.ble s' && ShapeFun.ble ble f f'
  | _+1, .lam f, .lam f' => ShapeFun.ble ble f f'
  | _, _, _ => false

def ShapeFun.LE (s s' : ShapeFun n) : Prop := ShapeFun.ble Shape.ble s s'
def Shape.LE (s s' : Shape n) : Prop := s.ble s'
instance : LE (Shape n) := ⟨Shape.LE⟩
instance : DecidableRel (α := Shape n) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x.ble y))

local notation s " ≤≤ " s':36 => ShapeFun.LE s s'

@[simp] theorem Shape.bot_le : Shape.bot ≤ (s : Shape n) := by cases n <;> rfl

theorem ShapeFun.LE.def {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x y:Shape n, (x, y) ∈ f → ∃ x' y':Shape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [LE, ble]; rfl

def ShapeFun.bot : ShapeFun n := [(.bot, .bot)]

theorem Shape.LE.def {s s' : Shape (n + 1)} : s ≤ s' ↔
    match s, s' with
    | .bot, _ => True
    | .U, .U => True --j ≤ i
    | .pi s f, .pi s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
    | _, _ => False := by
  dsimp only [(· ≤ ·), Shape.LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp

theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> rfl
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]

theorem ShapeFun.LE.rfl {f : ShapeFun n} : f ≤≤ f := by
  show ShapeFun.ble Shape.ble f f
  simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact fun _ h => ⟨_, h, Shape.LE.rfl, Shape.LE.rfl⟩

theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

theorem ShapeFun.LE.bot : .bot ≤≤ f := sorry

theorem Shape.le_U {s : Shape n} : s ≤ .U ↔ s = .bot ∨ s = .U := by
  cases n <;> simp [U, bot, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble]

theorem Shape.LE.trans {s t u : Shape n} : s ≤ t → t ≤ u → s ≤ u := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> cases t <;> simp [ble]
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble]
    · exact fun h1 h2 h3 h4 => ⟨ih h1 h3, ihf h2 h4⟩
    · exact ihf

theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s ≤≤ t → t ≤≤ u → s ≤≤ u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

theorem Shape.Compat.bot_l {x : Shape n} : Shape.bot.Compat x = true := by
  cases n <;> rfl
theorem Shape.Compat.bot_r {x : Shape n} : x.Compat Shape.bot = true := by
  cases n <;> cases x <;> rfl

def Shape.Join (x y z : Shape n) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w
def ShapeFun.Join (x y z : ShapeFun n) := ∀ w, z.LE w ↔ x.LE w ∧ y.LE w

theorem Shape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl
theorem ShapeFun.Join.le (H : Join x y z) : x ≤≤ z ∧ y ≤≤ z := (H _).1 .rfl

theorem Shape.Compat.def {x y : Shape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := sorry

theorem Shape.Join.compat (H : Join x y z) : x.Compat y := Compat.def.2 ⟨_, (H _).1 .rfl⟩

def ShapeFun.join (join : Shape n → Shape n → Shape n) (f f' : ShapeFun n) : ShapeFun n := by
  refine f.foldl (init := []) fun l (x, y) => ?_
  refine f'.foldl (init := l) fun l (x', y') => ?_
  refine if x.Compat x' then ?_ else l
  let jx := join x x'
  let jy := join y y'
  exact l.map fun (z, w) => (z, if z ≤ jx then join w jy else w)

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, .bot | 0, .bot, s | _+1, .bot, s | _+1, s, .bot => s
  | 0, .U, .U | _+1, .U, .U => .U
  | _+1, .pi s f, .pi s' f' => .pi (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, _, _ => .bot

theorem Shape.join.bot_l {x : Shape n} : Shape.bot.join x = x := by
  cases n <;> cases x <;> rfl
theorem Shape.join.bot_r {x : Shape n} : x.join Shape.bot = x := by
  cases n <;> cases x <;> rfl

theorem Shape.Join.mk (H : x.Compat y) : Join x y (x.join y) := sorry

theorem ShapeFun.Join.mk (H : Compat Shape.Compat x y) : Join x y (join Shape.join x y) := sorry

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n :=
  maxBelow (s.filter (·.1 ≤ a)) |>.2

theorem ShapeFun.app_mono_l {f f' : ShapeFun n} : f.LE f' → ∀ a, f.app a ≤ f'.app a :=
  sorry

theorem ShapeFun.app_mono_r {f : ShapeFun n} : a ≤ a' → f.app a ≤ f.app a' :=
  sorry

theorem ShapeFun.Join.app (H : Join x y z) : Shape.Join (x.app a) (y.app a) (z.app a) := sorry

theorem ShapeFun.Compat.def {f f' : ShapeFun n} :
    ShapeFun.Compat Shape.Compat f f' ↔ ∀ x, (f.app x).Compat (f'.app x) :=
  sorry

@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := sorry

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

theorem Shape.Join.app (H : Join x y z) : Shape.Join (x.app a) (y.app a) (z.app a) := sorry

theorem Shape.app_mono_l {f f' : Shape (n + 1)} (h1 : f ≤ f') (a) : f.app a ≤ f'.app a := by
  unfold app; split
  · cases f' <;> simp [Shape.LE.def] at h1
    exact ShapeFun.app_mono_l h1 _
  · exact bot_le

theorem Shape.app_mono_r {f : Shape (n + 1)} (h1 : x ≤ y) : f.app x ≤ f.app y := sorry

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .pi a b, .U =>
    a.hasType .U && b.all fun (x, y) => x.hasType a && y.hasType .U
  | 0, .bot, _ | _+1, .bot, _
  | 0, .U, .U | _+1, .U, .U => true
  | _+1, .lam f, .pi a b =>
    f.all fun (x, y) => x.hasType a && y.hasType (ShapeFun.app b x)
  | _, _, _ => false

def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

local notation u " :ᶠ " a:36 => Shape.HasType u a

def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) :=
  HasType a .U ∧ ∀ x y, (x, y) ∈ b → HasType x a ∧ HasType y .U

def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  ∀ x y, (x, y) ∈ (f : ShapeFun n) → HasType x a ∧ HasType y (ShapeFun.app b x)

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasTypeU .bot x
  | U : HasTypeU .U .U
  | pi : HasTypePi (n := n) b a → HasTypeU (n := n+1) (.pi a b) .U
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.pi a b)

theorem Shape.HasType.unfold {m a : Shape n} : m :ᶠ a → HasTypeU m a := by
  unfold HasType hasType; split <;> simp <;> intros <;> constructor <;>
    grind [HasType, HasTypeLam, HasTypePi]

theorem Shape.HasType.unfold_iff {m a : Shape n} : m :ᶠ a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  unfold HasType hasType
  cases h with
  | bot | U => cases n <;> rfl
  | _ => simp <;> grind [HasType, HasTypeLam, HasTypePi]

theorem Shape.HasType.bot : HasType (n := n) .bot x := unfold_iff.2 .bot
theorem Shape.HasType.U : HasType (n := n) .U .U := unfold_iff.2 .U
theorem Shape.HasType.pi : HasTypePi (n := n) b a → HasType (n := n+1) (.pi a b) .U :=
  (unfold_iff.2 <| .pi ·)
theorem Shape.HasType.lam : HasTypeLam (n := n) f a b → HasType (n := n+1) (.lam f) (.pi a b) :=
  (unfold_iff.2 <| .lam ·)

theorem Shape.HasTypeLam.bot : HasTypeLam .bot a b := by
  simp [HasTypeLam, ShapeFun.bot]; exact ⟨.bot, .bot⟩

theorem Shape.HasType.mono {m a a' : Shape n} (ha : a ≤ a') : m :ᶠ a → m :ᶠ a' := sorry

theorem Shape.HasTypeLam.app (H : HasTypeLam f a b) (ht : HasType x a) :
    HasType (ShapeFun.app f x) (ShapeFun.app b x) := sorry

theorem Shape.HasTypePi.app (H : HasTypePi f a)
    (ht : HasType x a) : HasType (ShapeFun.app f x) .U := sorry

theorem Shape.HasType.maximal
    (H : HasTypeLam f a b) (ha : a ≤ a') (ht : HasType x' a') :
    ∃ x, HasType x a ∧ x ≤ x' ∧ ShapeFun.app f x = ShapeFun.app f x' := sorry

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n m}, Shape n → Shape m
  | 0, _, .U | _+1, _, .U => .U
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .pi s f => .pi (lift s) <| ShapeFun.lift lift f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift lift f

@[simp] theorem Shape.lift_bot : ((Shape.bot : Shape n).lift : Shape m) = Shape.bot := by
  cases n; rfl; cases m <;> rfl

@[simp] theorem Shape.lift_U : ((Shape.U : Shape n).lift : Shape m) = Shape.U := by
  cases n; rfl; cases m <;> rfl

theorem Shape.lift_self {s : Shape n} : s.lift = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s; rfl; grind
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]

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
      -- case sort i h1 => split <;> split <;> simp [lift, *]; grind

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
    -- have sif {i} (h : i ≤ n) : (if h : i ≤ m then .sort i h else .bot : Shape (m+1)) =
    --     .sort i (Nat.le_trans h le) := dif_pos _
    cases s <;> cases t <;> simp [ble, lift, *]

theorem Shape.lift_mono {s t : Shape n} : s ≤ t → (s.lift : Shape m) ≤ t.lift := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n generalizing m with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.LE.rfl | exact Shape.bot_le
  | succ n ih =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      specialize @ih m
      have ihf {s t} : ShapeFun.ble ble s t →
          ShapeFun.ble ble (ShapeFun.lift (lift : Shape n → Shape m) s) (ShapeFun.lift lift t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      cases s <;> cases t <;> simp [ble, lift, *]
      -- · split <;> split <;> simp [ble]; omega
      · grind
      · grind

theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift : Shape m).Compat y.lift ↔ x.Compat y := sorry

theorem ShapeFun.Compat.lift {x y : ShapeFun n} (le : n ≤ m) :
    Compat Shape.Compat (lift Shape.lift x : ShapeFun m) (lift Shape.lift y) ↔
    Compat Shape.Compat x y := sorry

theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    ((x.join y).lift : Shape m) = x.lift.join y.lift := sorry

theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    (lift Shape.lift (x.join Shape.join y) : ShapeFun m) =
    join Shape.join (lift Shape.lift x) (lift Shape.lift y) := sorry

theorem ShapeFun.lift_app {f : ShapeFun n} {a} (le : n ≤ m) :
    (f.app a).lift (m := m) = ShapeFun.app (ShapeFun.lift Shape.lift f) a.lift :=
  sorry

theorem Shape.lift_app {f : Shape (n+1)} {a} (le : n ≤ m) :
    (f.app a).lift (m := m) = f.lift.app a.lift :=
  sorry

structure D : Type where
  above : Shape n → Prop
  lift : n ≤ n' → above (n := n) a → above (n := n') a.lift
  bot' : above (n := n) .bot
  le : b ≤ a → above a → above b
  join : above a → above b → a.Compat b ∧ above (a.join b)

theorem D.above.join' (J : a.Join b c) {x : D}
    (h1 : x.above a) (h2 : x.above b) : x.above c :=
  have ⟨a1, a2⟩ := x.join h1 h2
  x.le ((J _).2 (Shape.Join.mk a1).le) a2

@[ext] theorem D.ext {x y : D} (H : ∀ {n} (s : Shape n), x.above s ↔ y.above s) : x = y := by
  cases x; cases y; congr; ext; apply H

def D.LE (x y : D) : Prop := ∀ {{n}} {{s : Shape n}}, x.above s → y.above s

instance : LE D := ⟨D.LE⟩

theorem D.LE.rfl {x : D} : x ≤ x := fun _ _ => id

theorem D.LE.antisymm {x y : D} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := ext fun _ => ⟨@h1 _ _, @h2 _ _⟩
theorem D.LE.trans {x y z : D} : x ≤ y → y ≤ z → x ≤ z := fun h1 h2 _ _ h => h2 (h1 h)

def Shape.embed (s : Shape n) : D where
  above {m} x := x.lift (m := max n m) ≤ s.lift
  lift {m m' x} le h1 := by
    rw [lift_lift (.inl le)]
    refine cast ?_ (lift_mono (m := max n m') h1)
    congr 1 <;> rw [lift_lift] <;> omega
  bot' := by simp
  le h1 h2 := .trans (lift_mono h1) h2
  join h1 h2 :=
    have := Compat.def.2 ⟨_, h1, h2⟩; have r := Nat.le_max_right ..
    ⟨(Compat.lift r).1 this, lift_join r ▸ (Shape.Join.mk this _).2 ⟨h1, h2⟩⟩

def D.bot : D := Shape.bot.embed (n := 0)
@[simp] theorem D.bot_above : D.bot.above (n := n) s ↔ s ≤ .bot := by
  simp [D.bot, Shape.embed]
  simpa using Shape.lift_le_lift (Nat.le_max_right 0 n) (s := s) (t := .bot)

theorem D.LE.bot {x : D} : .bot ≤ x := fun _ _ h => x.le (by simpa using h) x.bot'

def D.U : D := Shape.U.embed (n := 0)

structure DF : Type where
  f : Shape n → D
  lift : n ≤ n' → f (n := n') a.lift = f (n := n) a
  mono : a ≤ b → f a ≤ f b

axiom ShapeFun.embed : ShapeFun n → DF
noncomputable instance : CoeOut (Shape n) D := ⟨Shape.embed⟩
noncomputable instance : CoeOut (ShapeFun n) DF := ⟨ShapeFun.embed⟩

def DF.app (f : DF) (x : D) : D where
  above y₀ := ∃ n, ∃ x₀ : Shape n, x.above x₀ ∧ (f.f x₀).above y₀
  lift h1 | ⟨_, _, h2, h3⟩ => ⟨_, _, h2, (f.f _).lift h1 h3⟩
  bot' := ⟨0, _, x.bot', (f.f _).bot'⟩
  le h1 | ⟨_, _, h2, h3⟩ => ⟨_, _, h2, (f.f _).le h1 h3⟩
  join := by
    intro _ _ _ ⟨n, _, h1, h2⟩ ⟨m, _, h3, h4⟩
    have ⟨a1, a2⟩ := x.join (x.lift (Nat.le_max_left ..) h1) (x.lift (Nat.le_max_right ..) h3)
    have ⟨l1, l2⟩ := (Shape.Join.mk a1).le
    rw [← f.lift (Nat.le_max_left n m)] at h2
    rw [← f.lift (Nat.le_max_right n m)] at h4
    have ⟨b1, b2⟩ := (f.f _).join (f.mono l1 h2) (f.mono l2 h4)
    exact ⟨b1, _, _, a2, b2⟩

noncomputable instance : CoeFun DF fun _ => D → D := ⟨(·.app)⟩

def DF.mk' (f : D → D) : DF := sorry
@[simp] axiom DF.mk'_app : DF.mk' g x = g x

theorem D.LE.app {f : DF} (h : x ≤ y) : f x ≤ f y :=
  fun _ _ ⟨_, _, h1, h2⟩ => ⟨_, _, h h1, h2⟩

def DF.comp (f g : DF) : DF where
  f y := f.app (g.f y)
  lift le := g.lift le ▸ rfl
  mono le := .app (g.mono le)

def D.lam (f : DF) : D where
  above {n} y := ∀ {{m}}, n ≤ m + 1 → ∃ g, y.lift (m := m + 1) ≤ .lam g ∧
    ∀ x : Shape m, (f.f x).above (ShapeFun.app g x)
  lift h1 h2 _ le :=
    have ⟨_, a1, a2⟩ := h2 (Nat.le_trans h1 le)
    ⟨_, (Shape.lift_lift (.inl h1)).symm ▸ a1, a2⟩
  bot' le := ⟨ShapeFun.bot, by simp; exact fun _ => (f.f _).bot'⟩
  le {n _ _} h1 h2 m le :=
    have ⟨_, a1, a2⟩ := h2 le
    ⟨_, .trans (Shape.lift_mono h1) a1, a2⟩
  join {n} a b h1 h2 := by
    have H {a : Shape n} (ha : a ≠ .bot)
        (h1 : ∀ ⦃m⦄, n ≤ m + 1 → ∃ g, a.lift (m := m+1) ≤ .lam g ∧
          ∀ x : Shape m, (f.f x).above (ShapeFun.app g x)) :
        ∃ n', n = n' + 1 ∧ ∃ g : ShapeFun n', a ≍ ShapeS.lam g := by
      have ⟨_, a1, _⟩ := h1 (Nat.le_succ _)
      cases n <;> cases a <;> simp [Shape.lift, Shape.LE.def, Shape.bot, Shape.lift] at a1 ha
      exact ⟨_, rfl, _, .rfl⟩
    by_cases ha : a = .bot; · simp [ha, Shape.Compat.bot_l, Shape.join.bot_l]; exact h2
    by_cases hb : b = .bot; · simp [hb, Shape.Compat.bot_r, Shape.join.bot_r]; exact h1
    obtain ⟨n, ⟨⟩, a, ⟨⟩⟩ := H ha h1; obtain ⟨_, ⟨⟩, b, ⟨⟩⟩ := H hb h2
    simp [Shape.lift, Shape.LE.def, Shape.join, Shape.Compat] at h1 h2 ⊢
    refine have hJ := ?_; ⟨hJ, fun m h3 => ?_⟩
    · simp [ShapeFun.Compat.def]; intro x
      obtain ⟨_, h1, a1⟩ := h1 (Nat.le_succ _)
      obtain ⟨_, h2, a2⟩ := h2 (Nat.le_succ _)
      have ⟨_, b1, b2⟩ := Shape.Compat.def.1 ((f.f _).join (a1 x.lift) (a2 x.lift)).1
      have b1 := ShapeFun.lift_app (Nat.le_succ _) ▸ (ShapeFun.app_mono_l h1 _).trans b1
      have b2 := ShapeFun.lift_app (Nat.le_succ _) ▸ (ShapeFun.app_mono_l h2 _).trans b2
      exact (Shape.Compat.lift (Nat.le_succ _)).1 <| Shape.Compat.def.2 ⟨_, b1, b2⟩
    · have ⟨g, h1, a1⟩ := h1 h3; have ⟨g', h2, a2⟩ := h2 h3
      have := (@ShapeFun.Compat.def _ g g').2 fun x => ((f.f _).join (a1 x) (a2 x)).1
      have H := ShapeFun.Join.mk this
      refine ⟨ShapeFun.join Shape.join g g', ?_, fun x => ?_⟩
      · rw [ShapeFun.lift_join h3]
        exact (ShapeFun.Join.mk ((ShapeFun.Compat.lift h3).2 hJ) _).2
          ⟨h1.trans H.le.1, h2.trans H.le.2⟩
      have ⟨_, b1, b2⟩ := Shape.Compat.def.1 ((f.f _).join (a1 x) (a2 x)).1
      exact (a1 _).join' H.app (a2 _)

def D.pi : D → DF → D := sorry

instance : LE DF := ⟨fun f g => ∀ x, f x ≤ g x⟩

theorem DF.LE.trans {x y z : DF} : x ≤ y → y ≤ z → x ≤ z := fun h1 h2 _ => (h1 _).trans (h2 _)

noncomputable def DF.bot : DF where
  f _ := .bot
  lift := by simp
  mono _ _ _ := id

@[simp] theorem DF.bot_app : DF.bot.app x = .bot := by
  ext; simp [app, bot]; exact fun _ => ⟨0, _, x.bot'⟩

theorem D.lam_bot : D.lam .bot = .bot := by
  refine LE.antisymm (fun _ _ h => D.bot_above.2 ?_) .bot
  have ⟨_, a1, a2⟩ := h (Nat.le_succ _)
  refine (Shape.lift_le_lift (Nat.le_succ _)).1 (a1.trans ?_)
  simp [Shape.LE.def]; exact mySorry

def D.unlam (f : D) : DF where
  f {n} x₀ := {
    above {m} y₀ := ∃ k, n ≤ k ∧ m ≤ k ∧
      ∃ f₀ : Shape (k + 1), f.above f₀ ∧ y₀.lift ≤ f₀.app x₀.lift
    lift {m m' x} h1 := fun ⟨k, h2, h3, f₀, h4, h5⟩ => by
      refine ⟨_, Nat.le_trans h2 (Nat.le_max_right ..), Nat.le_max_left .., f₀.lift,
        f.lift (Nat.succ_le_succ (Nat.le_max_right ..)) h4, ?_⟩
      have := Shape.lift_mono (m := max m' k) h5
      rw [Shape.lift_lift (.inl h3), Shape.lift_app (Nat.le_max_right ..),
        Shape.lift_lift (.inl h2)] at this
      rwa [Shape.lift_lift (.inl h1)]
    bot' {m} := ⟨_, Nat.le_max_left .., Nat.le_max_right .., _, f.bot', by simp⟩
    le h1 := fun ⟨k, h2, h3, f₀, h4, h5⟩ =>
       ⟨k, h2, h3, f₀, h4, .trans (Shape.lift_mono h1) h5⟩
    join {m a b} := fun ⟨k, a1, a2, f₀, a3, a4⟩ ⟨k', b1, b2, f₁, b3, b4⟩ => by
      replace a4 := Shape.lift_mono (m := max k k') a4
      replace b4 := Shape.lift_mono (m := max k k') b4
      rw [Shape.lift_lift (.inl ‹_›), Shape.lift_app (by omega),
        Shape.lift_lift (.inl ‹_›)] at a4 b4
      have ⟨c1, c2⟩ := f.join
        (f.lift (Nat.add_le_add_right (Nat.le_max_left ..) _) a3)
        (f.lift (Nat.add_le_add_right (Nat.le_max_right ..) _) b3)
      have hJ := (Shape.Join.mk c1).app (a := x₀.lift)
      have ⟨_, c3, c4⟩ := Shape.Compat.def.1 hJ.compat
      refine have := Shape.Compat.def.2 ⟨_, .trans a4 c3, .trans b4 c4⟩
        ⟨(Shape.Compat.lift (Nat.le_trans a2 (Nat.le_max_left ..))).1 this, ?_⟩
      refine
        have hn := Nat.le_trans a1 (Nat.le_max_left ..)
        have hm := Nat.le_trans a2 (Nat.le_max_left ..)
        ⟨max k k', hn, hm, _, c2, ?_⟩
      rw [Shape.lift_join hm]
      exact (Shape.Join.mk this _).2 ⟨.trans a4 hJ.le.1, .trans b4 hJ.le.2⟩ }
  lift {n n' x} le := ext fun x => by
    dsimp; constructor <;> intro ⟨k, h1, h2, _, h3, h4⟩
    · exact ⟨_, Nat.le_trans le h1, h2, _, h3, (Shape.lift_lift (.inl le) ▸ h4 :)⟩
    · refine ⟨_, Nat.le_max_right .., Nat.le_trans h2 (Nat.le_max_left ..),
        _, f.lift (Nat.succ_le_succ (Nat.le_max_left ..)) h3, ?_⟩
      replace h4 := Shape.lift_mono (m := max k n') h4
      rw [Shape.lift_lift (.inl h2), Shape.lift_app (Nat.le_max_left ..),
        Shape.lift_lift (.inl h1)] at h4
      rwa [Shape.lift_lift (.inl le)]
  mono le _ _ := fun ⟨k, h1, h2, _, h3, h4⟩ =>
    ⟨_, h1, h2, _, h3, .trans h4 (Shape.app_mono_r (Shape.lift_mono le))⟩

def D.app (f : D) : D → D := DF.app (D.unlam f)

noncomputable instance : CoeFun D fun _ => D → D := ⟨.app⟩
axiom D.app_lam : D.lam f x = f x

axiom D.LE.lam {x y : DF} : D.lam x ≤ .lam y ↔ x ≤ y
axiom D.LE.pi {x y : D} : D.pi x f ≤ D.pi y g ↔ x ≤ y ∧ f ≤ g

axiom D.LE.embed {x y : Shape n} : Shape.embed x ≤ Shape.embed y ↔ x ≤ y
axiom DF.LE.embed {x y : ShapeFun n} : ShapeFun.embed x ≤ ShapeFun.embed y ↔ x ≤≤ y

@[simp] axiom Shape.embed_U : (Shape.U (n := n) : D) = .U

axiom proj : D → DF
axiom proj_U_U : proj .U .U = .U
axiom proj_U_pi : proj .U (.pi a f) = .pi (proj .U a) ((proj .U).comp <| f.comp <| proj a)
axiom proj_pi : proj (.pi a f) (.lam w) =
  .lam (.mk' fun x => proj (f (proj a x)) (w (proj a x)))

axiom proj_le : proj a u ≤ u
axiom proj_proj (a u : D) : proj a (proj a u) = proj a u

def El (a u : D) : Prop := proj a u = u

theorem El_iff {u a : Shape n} : El a u ↔ u :ᶠ a := sorry
theorem El_U_iff {u : Shape n} : El .U u ↔ u :ᶠ .U := by rw [← El_iff, Shape.embed_U]
theorem El.mono : v ≤ u → El a u → El a v := sorry

inductive Expr where
  | bvar : Nat → Expr
  | lam : Expr → Expr → Expr
  | app : Expr → Expr → Expr
  | pi : Expr → Expr → Expr
  | U : Expr

def subst : Expr → Expr → Expr := sorry

def tail (ρ : Nat → D) (n : Nat) : D := ρ (n + 1)
noncomputable def push (ρ : Nat → D) (u a : D) : Nat → D
  | 0 => proj u a
  | n+1 => ρ n

noncomputable def Expr.eval (ρ : Nat → D) : Expr → D
  | .bvar i => ρ i
  | .U => .U
  | .pi A B => .pi (A.eval ρ) (.mk' fun u => B.eval (push ρ u (A.eval ρ)))
  | .app M N => (M.eval ρ) (N.eval ρ)
  | .lam A M => .lam (.mk' fun u => M.eval (push ρ u (A.eval ρ)))

def fits (ρ : Nat → D) : List Expr → Prop
  | [] => True
  | A::Γ => El .U (A.eval (tail ρ)) ∧ El (A.eval (tail ρ)) (ρ 0) ∧ fits (tail ρ) Γ

def Valuation := Nat → D

def Valuation.nil : Valuation := fun _ => .bot
def Valuation.push (ρ : Valuation) (u : D) : Valuation
  | 0 => u
  | n+1 => ρ n

noncomputable def interp (ρ : Valuation) : Expr → D
  | .bvar i => ρ i
  | .U => .U
  | .app f a => .app (interp ρ f) (interp ρ a)
  | .lam a f => .lam (.mk' fun u => interp (ρ.push (proj (interp ρ a) u)) f)
  | .pi a f => .pi (interp ρ a) (.mk' fun u => interp (ρ.push (proj (interp ρ a) u)) f)

inductive WHRed : Expr → Expr → Prop
  | app : WHRed N N' → WHRed (.app N M) (.app N' M)
  | beta : WHRed (.app (.lam A N) M) (subst N M)

axiom DefEq (Γ : List Expr) (M N A : Expr) : Prop
axiom DefEq.U : DefEq Γ .U .U .U
axiom DefEq.left : DefEq Γ M N A → DefEq Γ M M A
def Conv (M N _ : Expr) := M = N

def WHRedT (M N A : Expr) := WHRed M N ∧ Conv M N A
inductive WHRedTS : (M N A : Expr) → Prop where
  | rfl : DefEq [] M M A → WHRedTS M M A
  | tail : WHRedTS M N A → WHRedT N P A → WHRedTS M P A

local notation M " ⤳* " N " : " A:36 => WHRedTS M N A

axiom WHRedTS.uniq_pi : M ⤳* .pi B F : A → M ⤳* .pi B' F' : A → B.pi F = B'.pi F'

section
variable (DefEqF : Expr → Expr → Expr → Shape n → Shape n → Prop)

def DefEqPiF (B F F' : Expr) (b : Shape n) (f : ShapeFun n) : Prop :=
  ∀ v, v :ᶠ b → ∀ N, v.embed ≤ N.eval (fun _ => .bot) →
  (∀ N', v.embed ≤ N'.eval (fun _ => .bot) → DefEqF N N' B v b →
    DefEqF (subst F N) (subst F N') .U (f.app v) .U ∧
    DefEqF (subst F' N) (subst F' N') .U (f.app v) .U) ∧
  (DefEqF N N B v b → DefEqF (subst F N) (subst F' N) .U (f.app v) .U)

def DefEqLamF (M M' B F : Expr) (m : ShapeFun n) (b : Shape n) (f : ShapeFun n) : Prop :=
  ∀ v, v :ᶠ b → ∀ N, v.embed ≤ N.eval (fun _ => .bot) →
  (∀ N', v.embed ≤ N'.eval (fun _ => .bot) → DefEqF N N' B v b →
    -- DefEqF (subst F N) (subst F N') .U (f.app v) .U ∧
    DefEqF (.app M N) (.app M N') (subst F N) (m.app v) (f.app v) ∧
    DefEqF (.app M' N) (.app M' N') (subst F N) (m.app v) (f.app v)) ∧
  (DefEqF N N B v b → DefEqF (.app M N) (.app M' N) (subst F N) (m.app v) (f.app v))
end

def DefEqF : ∀ {n}, Expr → Expr → Expr → Shape n → Shape n → Prop
  | 0, _, _, _, _, .bot | _+1, _, _, _, _, .bot => True
  | _+1, _, _, _, _, .lam f => f ≤≤ .bot
  | 0, A, A', V, .U, .U | _+1, A, A', V, .U, .U => V ⤳* .U : .U ∧ A ⤳* .U : .U ∧ A' ⤳* .U : .U
  | _+1, A, A', V, .pi b f, .U => V ⤳* .U : .U ∧
    ∃ B F B' F', A ⤳* .pi B F : .U ∧ A' ⤳* .pi B' F' : .U ∧
    DefEqF B B' .U b .U ∧ DefEq [B] F F' .U ∧ DefEqPiF DefEqF B F F' b f
  | 0, _, _, V, .bot, .U | _+1, _, _, V, .bot, .U => V ⤳* .U : .U
  | _+1, _, _, V, .lam f, .U => V ⤳* .U : .U ∧ f ≤≤ .bot
  | _+1, M, M', A, .lam m, .pi b f => ∃ B F, A ⤳* .pi B F : .U ∧ DefEqLamF DefEqF M M' B F m b f
  | _+1, M, M', A, .bot, .pi b f => ∃ B F, A ⤳* .pi B F : .U ∧ DefEqLamF DefEqF M M' B F .bot b f
  | _, _, _, _, _, _ => False

theorem DefEqF.U_U : @DefEqF n A A' V .U .U ↔ V ⤳* .U : .U ∧ A ⤳* .U : .U ∧ A' ⤳* .U : .U := by
  cases n <;> simp [DefEqF]

theorem DefEqPiF.left : DefEqPiF DefEqF B F F' b f → DefEqPiF DefEqF B F F b f := by
  intro h1 v h2 N hN
  have a1 := (h1 _ h2 _ hN).1
  exact ⟨fun N' hN' h3 => ⟨(a1 _ hN' h3).1, (a1 _ hN' h3).1⟩, fun h3 => (a1 _ hN h3).1⟩

theorem DefEqLamF.left : DefEqLamF DefEqF M M' B F m b f → DefEqLamF DefEqF M M B F m b f := by
  intro h1 v h2 N hN
  have a1 := (h1 _ h2 _ hN).1
  exact ⟨fun N' hN' h3 => ⟨(a1 _ hN' h3).1, (a1 _ hN' h3).1⟩, fun h3 => (a1 _ hN h3).1⟩

theorem DefEqF.left {a : Shape n} : DefEqF M M' A u a → DefEqF M M A u a := by
  unfold DefEqF; split
  · exact id
  · exact id
  · exact id
  · exact fun ⟨h1, h2, _⟩ => ⟨h1, h2, h2⟩
  · exact fun ⟨h1, h2, _⟩ => ⟨h1, h2, h2⟩
  · intro ⟨h1, _, _, _, _, h2, h3, h4, h5, h6⟩
    exact ⟨h1, _, _, _, _, h2, h2, h4.left, h5.left, h6.left⟩
  · exact id
  · exact id
  · exact id
  · exact fun ⟨_, _, h1, h2⟩ => ⟨_, _, h1, h2.left⟩
  · exact fun ⟨_, _, h1, h2⟩ => ⟨_, _, h1, h2.left⟩
  · exact id

mutual

theorem DefEqF.bot : DefEqF (n := n) A A .U a .U → DefEqF M N A .bot a := by
  cases n <;> cases a <;> simp [DefEqF]
  intro h1 _ _ h2 _ _ h3 h4 h5 h6
  exact ⟨_, _, h2, .bot h6⟩
termination_by 2 * n

theorem DefEqLamF.bot :
    DefEqPiF (n := n) DefEqF B F F' a f → DefEqLamF DefEqF M M' B F .bot a f := by
  intro h3 v h5 N hN; simp
  have ⟨a1, a2⟩ := h3 _ h5 _ hN
  refine ⟨fun N' hN' h6 => ?_, fun h6 => .bot (a1 _ hN h6).1⟩
  · have := (a1 _ hN' h6).1.left; exact ⟨.bot this, .bot this⟩
termination_by 2 * n + 1

end

mutual

theorem DefEqF.mono {a a' : Shape n} : DefEqF A A .U a .U → a :ᶠ .U → a' ≤ a →
    u :ᶠ a → DefEqF M M' A u a → u' ≤ u → u' :ᶠ a' → DefEqF M M' A u' a' := by
  intro h1 h2 h3 h7 h4 h6 h5
  unfold DefEqF at h4; split at h4
  · cases a' <;> cases h3; simp [DefEqF]
  · cases a' <;> cases h3; simp [DefEqF]
  · cases a' with | bot => simp [DefEqF] | lam => ?_ | _ => cases h3
    exact .trans h3 h4
  · cases a' with | bot => simp [DefEqF] | U
    cases u' with | bot => exact h4.1 | U => exact h4
  · cases a' with | bot => simp [DefEqF] | U => ?_ | _ => cases h3
    cases u' with | bot => exact h4.1 | U => exact h4 | _ => cases h6
  · cases a' with | bot => simp [DefEqF] | U => ?_ | _ => cases h3
    cases u' with | bot => exact h4.1 | pi => ?_ | _ => cases h6
    let ⟨a1, _, _, _, _, a2, a2', a3, a4, a5⟩ := h4; simp [Shape.LE.def] at h6
    let .pi hf := h5.unfold; let .pi b1 := h7.unfold
    refine ⟨a1, _, _, _, _, a2, a2',
      .mono (DefEqF.U_U.2 ⟨.rfl .U, .rfl .U, .rfl .U⟩) .U .rfl b1.1 a3 h6.1 hf.1,
      a4, .mono a3.left hf b1 h6.1 h6.2 a5⟩
  · cases a' with | bot => simp [DefEqF] | U
    cases u' with | bot => exact h4 | _ => cases h6
  · cases a' with | bot => simp [DefEqF] | U => ?_ | _ => cases h3
    cases u' with | bot => exact h4 | _ => cases h6
  · cases a' with | bot => simp [DefEqF] | U => ?_ | _ => cases h3
    cases h5.unfold with simp [DefEqF] | bot => exact h4.1 | _ => cases h6
  · cases a' with | bot => simp [DefEqF] | pi a f => ?_ | _ => cases h3
    let .pi c1 := h2.unfold; let .lam b1 := h7.unfold
    let ⟨B, F, a1, a2⟩ := h4; let ⟨_, _, _, _, a1', a1'', a3, a4, a5⟩ := h1.2
    cases a1.uniq_pi a1'; cases a1.uniq_pi a1''
    cases h5.unfold with simp [DefEqF, Shape.LE.def] at h3 ⊢
    | bot => exact ⟨B, F, a1, .mono a3 a5 c1 .bot .bot h3.1 h3.2 b1 a2⟩
    | lam h5 => exact ⟨B, F, a1, .mono a3 a5 c1 h5 h6 h3.1 h3.2 b1 a2⟩
  · cases a' with | bot => simp [DefEqF] | pi a f => ?_ | _ => cases h3
    let .pi c1 := h2.unfold; cases Shape.le_bot.1 h6; simp [Shape.LE.def] at h3
    let ⟨B, F, a1, a2⟩ := h4; let ⟨_, _, _, _, a1', a1'', a3, a4, a5⟩ := h1.2
    cases a1.uniq_pi a1'; cases a1.uniq_pi a1''
    exact ⟨B, F, a1, .mono a3 a5 c1 .bot .rfl h3.1 h3.2 .bot a2⟩
  · cases h4
termination_by 2 * n

theorem DefEqLamF.mono :
    DefEqF (n := n) B B .U b .U → DefEqPiF DefEqF B F F b f →
    Shape.HasTypePi f b → Shape.HasTypeLam m' b' f' →
    m' ≤≤ m → b' ≤ b → f' ≤≤ f →
    Shape.HasTypeLam m b f → DefEqLamF DefEqF M M' B F m b f →
    DefEqLamF DefEqF M M' B F m' b' f' := by
  intro h0 bf h1 hm' h3 h4 h5 hm h6 v h8 N hN
  have ⟨a1, a2⟩ := h6 _ (h8.mono h4) _ hN
  have ⟨a3, a4⟩ := bf _ (h8.mono h4) _ hN
  refine ⟨fun N' hN' h9 => ?_, fun h9 => ?_⟩
  · have h9' := h0.mono_r h1.1 h4 h9 h8
    have ⟨a1, a2⟩ := a1 _ hN' h9'
    have b1 := (a3 _ hN' h9').1.left
    refine ⟨?_, ?_⟩
    · exact .mono b1 (h1.app (h8.mono h4)) (ShapeFun.app_mono_l h5 _)
        (hm.app (h8.mono h4)) a1 (ShapeFun.app_mono_l h3 _) (hm'.app h8)
    · exact .mono b1 (h1.app (h8.mono h4)) (ShapeFun.app_mono_l h5 _)
        (hm.app (h8.mono h4)) a2 (ShapeFun.app_mono_l h3 _) (hm'.app h8)
  · have h9' := h0.mono_r h1.1 h4 h9 h8
    exact .mono (a4 h9') (h1.app (h8.mono h4)) (ShapeFun.app_mono_l h5 _)
      (hm.app (h8.mono h4)) (a2 h9') (ShapeFun.app_mono_l h3 _) (hm'.app h8)
termination_by 2 * n + 1

theorem DefEqPiF.mono : DefEqF (n := n) B B .U b .U →
    Shape.HasTypePi f' b' → Shape.HasTypePi f b → b' ≤ b → f' ≤≤ f →
    DefEqPiF DefEqF B F F' b f → DefEqPiF DefEqF B F F' b' f' := by
  intro h1 h3 hf h4 h5 h6 v h8 N hN
  have ⟨a1, a2⟩ := h6 _ (h8.mono h4) _ hN
  refine ⟨fun N' hN' h9 => ?_, fun h9 => ?_⟩
  · have ⟨a1, a2⟩ := a1 _ hN' (h1.mono_r hf.1 h4 h9 h8)
    refine ⟨?_, ?_⟩
    · exact .mono (DefEqF.U_U.2 ⟨.rfl .U, .rfl .U, .rfl .U⟩) .U .rfl
        (hf.app (h8.mono h4)) a1 (ShapeFun.app_mono_l h5 _) (h3.app h8)
    · exact .mono (DefEqF.U_U.2 ⟨.rfl .U, .rfl .U, .rfl .U⟩) .U .rfl
        (hf.app (h8.mono h4)) a2 (ShapeFun.app_mono_l h5 _) (h3.app h8)
  · specialize a2 (h1.mono_r hf.1 h4 h9 h8)
    exact .mono (DefEqF.U_U.2 ⟨.rfl .U, .rfl .U, .rfl .U⟩) .U .rfl
      (hf.app (h8.mono h4)) a2 (ShapeFun.app_mono_l h5 _) (h3.app h8)
termination_by 2 * n + 1

theorem DefEqF.mono_r : DefEqF (n := n) A A .U a .U → a :ᶠ .U → a' ≤ a →
    DefEqF M M' A u' a' → u' :ᶠ a' → DefEqF M M' A u' a := by
  intro h1 h2 h3 h4 h5
  unfold DefEqF at h4; split at h4
  · cases h5.unfold
    cases h2.unfold with
    | bot => trivial
    | U => exact h1.2.1
  · cases h5.unfold
    cases h2.unfold with
    | bot => trivial
    | U => exact h1.2.1
    | pi b1 => let ⟨B, F, _, _, a1, a1', a2, a3, a4⟩ := h1.2; exact ⟨_, _, a1, .bot a4⟩
  · cases h2.unfold with | bot => trivial | _ => cases h3
  · cases h2.unfold with | U => exact h4 | _ => cases h3
  · cases h2.unfold with | U => exact h4 | _ => cases h3
  · cases h2.unfold with | U => exact h4 | _ => cases h3
  · cases h2.unfold <;> cases h3; trivial
  · cases h2.unfold <;> cases h3; trivial
  · cases h5.unfold
  · cases h2.unfold <;> simp [Shape.LE.def] at h3
    let .lam h5 := h5.unfold; let .pi h6 := h2.unfold
    let ⟨B, F, a1, a2⟩ := h4; let ⟨_, _, _, _, a1', a1'', a3, a4, a5⟩ := h1.2
    cases a1.uniq_pi a1'; cases a1.uniq_pi a1''
    exact ⟨B, F, a1, .mono_r a3 a5 h6 h5 h3.1 h3.2 a2⟩
  · cases h2.unfold <;> simp [Shape.LE.def] at h3; let .pi h6 := h2.unfold
    let ⟨B, F, a1, a2⟩ := h4; let ⟨_, _, _, _, a1', a1'', a3, a4, a5⟩ := h1.2
    cases a1.uniq_pi a1'; cases a1.uniq_pi a1''
    exact ⟨B, F, a1, .mono_r a3 a5 h6 .bot h3.1 h3.2 a2⟩
  · cases h4
termination_by 2 * n

theorem DefEqLamF.mono_r : DefEqF (n := n) B B .U a .U → DefEqPiF DefEqF B F F a f →
    Shape.HasTypePi f a → Shape.HasTypeLam m a' f' →
    a' ≤ a → f' ≤≤ f → DefEqLamF DefEqF M M' B F m a' f' → DefEqLamF DefEqF M M' B F m a f := by
  intro hb bf h2 h3 h4 h5 h6 v hv N hN
  have ⟨v', hv', lv, eq⟩ := hv.maximal h3 h4
  have fv : f'.app v' ≤ f.app v := .trans (ShapeFun.app_mono_l h5 v') (ShapeFun.app_mono_r lv)
  have ⟨a1, a2⟩ := h6 _ hv' _ (.trans (D.LE.embed.2 lv) hN)
  have ⟨b1, b2⟩ := bf _ hv _ hN
  refine ⟨fun N' hN' h9 => ?_, fun h9 => ?_⟩
  · have ⟨a1, a2⟩ := a1 _ (.trans (D.LE.embed.2 lv) hN') (.mono hb h2.1 h4 hv h9 lv hv')
    refine ⟨?_, ?_⟩
    · exact .mono_r (b1 _ hN' h9).1.left (h2.app hv) fv (eq ▸ a1) (eq ▸ h3.app hv')
    · exact .mono_r (b1 _ hN' h9).1.left (h2.app hv) fv (eq ▸ a2) (eq ▸ h3.app hv')
  · specialize a2 (.mono hb h2.1 h4 hv h9 lv hv')
    exact .mono_r (b1 _ hN h9).1.left (h2.app hv) fv (eq ▸ a2) (eq ▸ h3.app hv')
termination_by 2 * n + 1

end

@[expose] public section
