import Lean4Lean.Experimental.SExpr
import Batteries.WF

example : Unit := sorry set_option warn.sorry false -- so I don't forget

namespace Lean4Lean

namespace SExpr
variable [Params]

private instance : DecidableEq SLevel := sorry

@[simp] theorem SLevel.succ_ne_zero {l : SLevel} : l.succ ≠ .zero := sorry
@[simp] theorem SLevel.imax_eq_zero {l l' : SLevel} : l.imax l' = .zero ↔ l' = .zero := sorry

-- structure Classifier' where
--   level : SLevel
--   HasTy' (e : SExpr) : Prop
-- def Classifier (_Γ : List SExpr) (_A : SExpr) := Classifier'

-- def Classifier.HasTy (C : Classifier Γ A) (e : SExpr) : Prop := Γ ⊢ e : A ∧ C.HasTy' e

@[ext] structure IProp where
  val : Nat → Prop
  mono : i ≤ j → val i → val j

@[ext] structure BIProp (n : Nat) where
  val : Nat → Prop
  bound : val i → i < n
  mono : i ≤ j → j < n → val i → val j

def BIProp.restrict (C : BIProp n) (m : Nat) (h : m ≤ n) : BIProp m where
  val i := i < m ∧ C.1 i
  bound H := H.1
  mono H1 H2 H3 := ⟨H2, C.mono H1 (Nat.lt_of_lt_of_le H2 h) H3.2⟩

def IProp.restrict (P : IProp) (n : Nat) : BIProp n where
  val i := i < n ∧ P.1 i
  bound H := H.1
  mono H1 H2 H3 := ⟨H2, P.mono H1 H3.2⟩

omit [Params] in
theorem IProp.restrict_restrict {P : IProp} : (P.restrict n).restrict m h = P.restrict m := by
  ext <;> simp [restrict, BIProp.restrict]; omega

axiom WHRedUpToN (Γ : List SExpr) (e e' : SExpr) (n : Nat) : Prop
axiom WHRedUpToN.mono : n ≤ n' → WHRedUpToN Γ e e' n → WHRedUpToN Γ e e' n'
axiom ParRedN (Γ : List SExpr) (e e' : SExpr) (n : Nat) : Prop
axiom ParRedN.mono : n ≤ n' → ParRedN Γ e e' n → ParRedN Γ e e' n'
axiom InferTypeN (Γ : List SExpr) (e A : SExpr) (n : Nat) : Prop
axiom InferTypeN.mono : n ≤ n' → InferTypeN Γ e e' n → InferTypeN Γ e e' n'
axiom NormalEqN (Γ : List SExpr) (e e' : SExpr) (n : Nat) : Prop
axiom NormalEqN.mono : n ≤ n' → NormalEqN Γ e e' n → NormalEqN Γ e e' n'
def CRDefEqN (Γ : List SExpr) (A B : SExpr) (n : Nat) : Prop :=
  ∃ A' B', ParRedN Γ A A' n ∧ ParRedN Γ B B' n ∧ NormalEqN Γ A' B' n

theorem CRDefEqN.mono : n ≤ n' → CRDefEqN Γ e e' n → CRDefEqN Γ e e' n'
  | h1, ⟨_, _, h2, h3, h4⟩ => ⟨_, _, h2.mono h1, h3.mono h1, h4.mono h1⟩

def CheckType (Γ : List SExpr) (e A : SExpr) (u : SLevel) : Prop :=
  ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ≫≪ A : .sort u
def CheckTypeN (Γ : List SExpr) (e A : SExpr) (n : Nat) : Prop :=
  ∃ A', InferTypeN Γ e A' n ∧ CRDefEqN Γ A A' n

theorem CheckTypeN.mono : n ≤ n' → CheckTypeN Γ e e' n → CheckTypeN Γ e e' n'
  | h1, ⟨_, h2, h3⟩ => ⟨_, h2.mono h1, h3.mono h1⟩

theorem CRDefEq.reduce_sort (H : Γ ⊢ e ≫≪ .sort u : A) : Γ ⊢ e ⤳* .sort u := sorry
theorem CRDefEq.reduce_forallE (H : Γ ⊢ e ≫≪ .forallE A B : V) :
  ∃ A' B', Γ ⊢ e ⤳* .forallE A' B' := sorry
theorem CRDefEq.forallE_inv (H : Γ ⊢ forallE A B ≫≪ .forallE A' B' : V)
  (H1 : Γ ⊢ A : .sort u) (H2 : A::Γ ⊢ B : .sort v) :
  Γ ⊢ A ≫≪ A' : .sort u ∧ A::Γ ⊢ B ≫≪ B' : .sort v := sorry

theorem CheckType.sort : CheckType Γ e (.sort u) v → Γ ⊢ e ▷* .sort u
  | ⟨_, h1, h2⟩ => ⟨_, h1, h2.reduce_sort⟩

theorem CheckType.forallE : CheckType Γ e (.forallE A B) u → ∃ A' B', Γ ⊢ e ▷* .forallE A' B'
  | ⟨_, h1, h2⟩ => let ⟨_, _, h3⟩ := h2.reduce_forallE; ⟨_, _, _, h1, h3⟩

theorem CheckType.defeqDF : CheckType Γ e A u → Γ ⊢ A ≫≪ B : .sort u → CheckType Γ e B u
  | ⟨_, h1, h2⟩, H => ⟨_, h1, h2.trans H⟩

-- structure Classifier.OK (C : Classifier Γ A) (n : Nat) : Prop where
--   HasTy_below : C.HasTy x i → i < n

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
    -- have sif {i} (h : i ≤ n) : (if h : i ≤ m then .sort i h else .bot : Shape (m+1)) =
    --     .sort i (Nat.le_trans h le) := dif_pos _
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
  induction n generalizing m with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
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

omit [Params] in
theorem ShapeFun.lift_mono {s t : ShapeFun n} : s.LE t →
    LE (lift Shape.lift s : ShapeFun m) (lift Shape.lift t) := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
    ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
  exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, Shape.lift_mono h3, Shape.lift_mono h4⟩

-- def ShapeFun.plift (lift : α → β × Option β) (x : List (α × α)) :
--     List (β × β) × Option (List (β × β)) :=
--   (x.filterMap fun (a, b) => return (← (lift a).2, (lift b).1),
--    x.mapM fun (a, b) => return ((lift a).1, ← (lift b).2))

-- def Shape.plift : ∀ {n m}, Shape n → Shape m × Option (Shape m)
--   | 0, _, _ | _+1, _, .bot => (.bot, some .bot)
--   | _+1, 0, _ => (.bot, none)
--   | n+1, m+1, .sort i _ =>
--     (if h : i ≤ m then .sort i h else .bot, _)
  -- | _+1, _+1, .forallE s f => .forallE (lift s) <| ShapeFun.lift lift f
  -- | _+1, _+1, .lam f => .lam <| ShapeFun.lift lift f

-- omit [Params] in
-- theorem Shape.lift_lift_le {s : Shape n} : (s.lift : Shape m).lift ≤ s := by
--   show ble ..
--   induction n generalizing m with | zero => rfl | succ n ih
--   cases m with | zero => rw [show s.lift = .bot from rfl]; simp; exact Shape.bot_le | succ m
--   specialize @ih m
--   have ihf {s : ShapeFun m} :
--       ShapeFun.ble ble (ShapeFun.lift lift (ShapeFun.lift lift s : ShapeFun n)) s := by
--     simp only [ShapeFun.ble, ShapeFun.lift, List.map_map, List.all_map, List.all_eq_true,
--       Function.comp_apply, List.any_eq_true, Bool.and_eq_true]
--     exact fun _ h => ⟨_, h, _, _⟩
--   cases s <;> simp [lift, ih, ihf]
--   case sort i h1 => split <;> split <;> simp [lift, *]; grind

-- omit [Params] in
-- theorem Shape.lift_lift_le' {s : Shape n₁} :
--     ((s.lift : Shape n₂).lift : Shape n₃) ≤ s.lift := by
--   suffices ∀ n', n₂ ≤ n' → ∀ s : Shape n', (s.lift : Shape n₂).lift.ble s by
--     if h : n₁ ≤ n₂ ∨ n₃ ≤ n₂ then rw [lift_lift h]; exact .rfl else
--     simp at h
--     rw [← lift_lift (n₁ := n₂) (n₂ := n₁.min n₃) (n₃ := n₃) (by simp [Nat.le_min]; omega),
--       ← lift_lift (n₁ := n₁) (n₂ := n₁.min n₃) (n₃ := n₃) (by simp [Nat.le_min]; omega),
--       ← lift_lift (n₁ := n₁) (n₂ := n₁.min n₃) (n₃ := n₂) (by simp [Nat.le_min]; omega)]
--     apply lift_mono; apply this; simp [Nat.le_min]; omega
--   clear n₁ n₃ s; intro m le s
--   induction n₂ generalizing m with
--   | zero => rw [show s.lift = .bot from rfl]; simp; exact Shape.bot_le
--   | succ n ih =>
--     let m + 1 := m; simp at le; replace ih {s} := ih _ le s
--     have ihf {s : ShapeFun m} :
--         ShapeFun.ble ble (ShapeFun.lift lift (ShapeFun.lift lift s : ShapeFun n)) s := by
--       simp only [ShapeFun.ble, ShapeFun.lift, List.map_map, List.all_map, List.all_eq_true,
--         Function.comp_apply, List.any_eq_true, Bool.and_eq_true]
--       exact fun _ h => ⟨_, h, _, ih⟩
--     cases s <;> simp [lift, ih, ihf]
--     case sort i h1 => split <;> split <;> simp [lift, *]; grind

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
theorem Shape.join_self : Join x x y ↔ x ≤ y ∧ y ≤ x :=
  ⟨fun H => ⟨((H _).1 .rfl).1, (H _).2 ⟨.rfl, .rfl⟩⟩,
   fun ⟨H1, H2⟩ _ => ⟨fun h => ⟨H1.trans h, H1.trans h⟩, fun h => H2.trans h.1⟩⟩

theorem Shape.Compat.def {x y : Shape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := sorry

theorem Shape.Join.compat (H : Join x y z) : x.Compat y := Compat.def.2 ⟨_, (H _).1 .rfl⟩

theorem Shape.Join.forallE (H : Join x y z) : x.Compat y := sorry

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

theorem Shape.Join.mk (H : x.Compat y) : Join x y (x.join y) := sorry

theorem ShapeFun.Join.mk (H : Compat Shape.Compat x y) : Join x y (join Shape.join x y) := sorry

theorem Shape.Join.iff : Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y :=
  ⟨fun h => ⟨h.compat, (mk h.compat _).2 h.le, (h _).2 (mk h.compat).le⟩,
   fun ⟨h1, h2, h3⟩ _ => .trans ⟨(.trans h2 ·), (.trans h3 ·)⟩ (mk h1 _)⟩

theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    ((x.join y).lift : Shape m) = x.lift.join y.lift := sorry

theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    (lift Shape.lift (ShapeFun.join Shape.join x y) : ShapeFun m) =
    join Shape.join (lift Shape.lift x) (lift Shape.lift y) := sorry

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n :=
  maxBelow (s.filter (·.1 ≤ a)) |>.2

omit [Params] in
theorem ShapeFun.bot_mem (f : ShapeFun n) : ∃ y, (.bot, y) ∈ f := sorry

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

@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := sorry

omit [Params] in
@[simp] theorem ShapeFun.lift_app :
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
theorem Shape.app_mono_l {f f' : Shape (n + 1)} (le : f ≤ f') (a) : f.app a ≤ f'.app a := by
  unfold app; split <;> [split; simp]
  · exact ShapeFun.app_mono_l le _
  · cases f' <;> simp [LE.def] at le; grind

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
  · sorry

omit [Params] in
theorem Shape.HasDom.lift (le : n ≤ m) :
    HasDom (n := m) (.lift Shape.lift f) a.lift ↔ HasDom f a := by
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

theorem Shape.HasType.lift (h : n ≤ n') :
    HasType (n := n') m.lift a.lift ↔ HasType (n := n) m a := sorry

omit [Params] in
theorem Shape.HasType.join (hJ : Join m₁ m₂ m) :
    HasType m₁ a → HasType m₂ a → HasType m a := sorry

omit [Params] in
theorem Shape.HasType.mono_l {m a : Shape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a :=
  .join (Shape.join_self.2 ⟨hm1, hm2⟩) H H

theorem Shape.HasType.lam_app
    (H : ∀ x y, (x, y) ∈ (f : ShapeFun n) → HasType x a ∧ HasType y (ShapeFun.app b x))
    (ht : HasType x a) : HasType (ShapeFun.app f x) (ShapeFun.app b x) := sorry

theorem Shape.HasType.pi_app
    (H : ∀ x y, (x, y) ∈ (b : ShapeFun n) → HasType x a ∧ HasType y (.sort r))
    (ht : HasType x a) : HasType (ShapeFun.app f x) (.sort r) := sorry

theorem Shape.HasType.maximal
    (H : ∀ x y, (x, y) ∈ (f : ShapeFun n) → HasType x a ∧ HasType y (ShapeFun.app b x))
    (ha : a ≤ a') (ht : HasType x' a') :
    ∃ x, HasType x a ∧ x ≤ x' ∧ ShapeFun.app f x = ShapeFun.app f x' := sorry

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

inductive LE_Interp : Valuation → ∀ {n}, Shape n → SExpr → Prop
  | bot : LE_Interp ρ .bot M
  -- | le : m ≤ m' → LE_Interp ρ m' M → LE_Interp ρ m M
  -- | lift : n ≤ n' → LE_Interp (n := n) ρ m M → LE_Interp (n := n') ρ m.lift M
  | bvar : (ρ i).1 ≤ n' → n ≤ n' → m.lift (m := n') ≤ (ρ i).2.lift → LE_Interp (n := n) ρ m (.bvar i)
  | sort : m ≤ .sort (decide (l ≠ .zero)) → LE_Interp ρ m (.sort l)
  | app : LE_Interp ρ f F → LE_Interp ρ a A → m ≤ f.app a → LE_Interp ρ m (.app F A)
  | lam : LE_Interp (n := n) ρ a A →
    Shape.HasDom f a → (∀ x, x.HasType a → LE_Interp (ρ.push x) ((f : ShapeFun n).app x) F) →
    m ≤ .lam f → LE_Interp (n := n+1) ρ m (.lam A F)
  | forallE : LE_Interp (n := n) ρ b B → LE_Interp (n := n) ρ b' B →
    Shape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x) ((f : ShapeFun n).app x) F) →
    m ≤ .forallE b f → LE_Interp (n := n+1) ρ m (.forallE B F)

theorem LE_Interp.mono : m ≤ m' → LE_Interp ρ m' M → LE_Interp ρ m M := sorry
theorem LE_Interp.mono_l : ρ.LE ρ' → LE_Interp ρ m M → LE_Interp ρ' m M := sorry
theorem LE_Interp.lift : n ≤ n' → (LE_Interp (n := n') ρ m.lift M ↔ LE_Interp (n := n) ρ m M) := sorry
theorem LE_Interp.weak (H : LE_Interp ρ m M) : LE_Interp (ρ.push x) m M.lift := sorry
theorem LE_Interp.weak_iff : LE_Interp (ρ.push x) m M.lift ↔ LE_Interp ρ m M := sorry
theorem LE_Interp.inst : LE_Interp (n := n) ρ f (F.inst A) ↔
    ∃ m a, LE_Interp (n := n) (ρ.push a) f F ∧ LE_Interp (n := m) ρ a A := sorry
theorem LE_Interp.bvar_iff :
    LE_Interp (n := n) ρ m (.bvar i) ↔
    ∃ k, n ≤ k ∧ (ρ i).1 ≤ k ∧ m.lift (m := k) ≤ (ρ i).2.lift := sorry

theorem LE_Interp.forallE_inv {b} {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.forallE b f) (.forallE B F)) :
    LE_Interp ρ b B ∧ ∀ {{X x}}, LE_Interp ρ x X → LE_Interp ρ (f.app x) (F.inst X) := by
  let .forallE (b := b₁) (b' := b₂) (f := f') hb₁ hb₂ hd hiB le := H
  simp [Shape.LE.def] at le
  refine ⟨hb₁.mono le.1, fun X x hx => ?_⟩
  obtain ⟨x', _, le1, hf, rfl⟩ := ShapeFun.app_eq f x
  obtain ⟨_, _, hf, le2, lf⟩ := ShapeFun.LE.def.1 le.2 _ _ hf
  refine .inst.2 ⟨_, _, ?_, hx.mono (le2.trans le1)⟩
  exact (hiB _ (Shape.HasDom.def.1 hd _ _ hf)).mono (lf.trans (ShapeFun.app_of_mem hf ▸ .rfl))

theorem LE_Interp.forallE_inv' {b} {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.forallE b f) (.forallE B F)) :
    LE_Interp ρ b B ∧ ∀ x, LE_Interp (ρ.push x) (f.app x) F := by
  have ⟨h1, h2⟩ := H.forallE_inv; refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x) H).forallE_inv.2
    (.bvar (i := 0) (Nat.le_refl _) (Nat.le_refl _) .rfl)
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.lam_inv {b} {f : ShapeFun n} {B F}
    (H : LE_Interp (n := n+1) ρ (.lam f) (.lam B F)) (hf : Shape.HasDom f b) :
    LE_Interp ρ b B ∧ ∀ {{x}}, x.HasType b → LE_Interp (ρ.push x) (f.app x) F := sorry

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M := sorry

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ := sorry

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort (u ≠ .zero) := by
  generalize eq : SExpr.sort u = M at H
  induction H with cases eq
  | bot => exact Shape.bot_le
  | sort h => exact h

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
  cases h1 with | bot => exact .bot | app h1 h2 h3
  have ⟨n', f, s, le, a1, a2, a3, a4⟩ := H1 h1
  have hf : f ≠ .bot := fun h => by
    subst h; cases (Shape.lift_le_bot le).1 a1; cases hm (Shape.le_bot.1 h3)
  have hs : s ≠ .bot := fun h => by subst h; cases a4.bot_r; cases hf rfl
  cases a3 with | bot => cases hs rfl | @forallE _ n' _ _ _ _ _ s b1 b2 b3 b4 b5
  replace le := Nat.le_of_succ_le_succ le
  cases s with simp [Shape.LE.def] at b5 | bot => cases hs rfl | forallE
  cases a4.unfold with | bot => cases hf rfl | lam c1
  refine
    have h2 := (LE_Interp.lift le).2 h2
    have ⟨_, d1, d2, d3⟩ := b3 _
    have ⟨m', _, le', g1, g2, g3⟩ := H2 (LE_Interp.inst.2 ⟨_, _, b4 _ d2, .mono d1 h2⟩)
    have ⟨_, e1, e2, e3⟩ := c1.2.1 _
    have := (c1.2.2 _ e2).mono_l (ShapeFun.app_mono_r e1) e3
    ⟨_, _, _, Nat.le_trans le le', ?_, (LE_Interp.lift le').2 (.app a2 h2 .rfl),
      g2, g3.mono_r ?_ ((Shape.HasType.lift le').2 this)⟩
  · rw [← Shape.lift_lift (.inl le)]
    exact Shape.lift_mono <| (Shape.lift_app ▸ Shape.lift_mono h3).trans (Shape.app_mono_l a1 _)
  · refine (Shape.lift_mono ?_).trans g1
    exact (ShapeFun.app_mono_l b5.2 _).trans <| (ShapeFun.app_mono_r e1).trans d3

theorem LE_Interp.sound_lam
    (H1 : ∀ {n} {m : Shape n}, LE_Interp ρ m f → InterpTyped ρ m f (.forallE A B))
    (H2 : ∀ {n} {m : Shape n}, LE_Interp ρ m (B.inst a) →
      ∃ n' a', n ≤ n' ∧ m.lift (m := n') ≤ a' ∧ LE_Interp ρ a' (B.inst a) ∧ a'.HasType .type)
    {m : Shape n} (h1 : LE_Interp ρ m (f.app a pat)) :
    InterpTyped ρ m (f.app a pat) (B.inst a) := by
  by_cases hm : m = .bot; · exact hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  have ⟨n', f, s, le, a1, a2, a3, a4⟩ := H1 h1
  have hf : f ≠ .bot := fun h => by
    subst h; cases (Shape.lift_le_bot le).1 a1; cases hm (Shape.le_bot.1 h3)
  have hs : s ≠ .bot := fun h => by subst h; cases a4.bot_r; cases hf rfl
  cases a3 with | bot => cases hs rfl | @forallE _ _ _ _ _ _ _ s b1 b2 b3 b4 b5
  replace le := Nat.le_of_succ_le_succ le
  cases s with simp [Shape.LE.def] at b5 | bot => cases hs rfl | forallE
  cases a4.unfold with | bot => cases hf rfl | lam c1
  refine
    have h2 := (LE_Interp.lift le).2 h2
    have ⟨_, d1, d2, d3⟩ := b3 _
    have ⟨m', _, le', g1, g2, g3⟩ := H2 (LE_Interp.inst.2 ⟨_, _, b4 _ d2, .mono d1 h2⟩)
    have ⟨_, e1, e2, e3⟩ := c1.2.1 _
    have := (c1.2.2 _ e2).mono_l (ShapeFun.app_mono_r e1) e3
    ⟨_, _, _, Nat.le_trans le le', ?_, (LE_Interp.lift le').2 (.app a2 h2 .rfl),
      g2, g3.mono_r ?_ ((Shape.HasType.lift le').2 this)⟩
  · rw [← Shape.lift_lift (.inl le)]
    exact Shape.lift_mono <| (Shape.lift_app ▸ Shape.lift_mono h3).trans (Shape.app_mono_l a1 _)
  · refine (Shape.lift_mono ?_).trans g1
    exact (ShapeFun.app_mono_l b5.2 _).trans <| (ShapeFun.app_mono_r e1).trans d3

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
          (LE_Interp.lift a1).2 h3.weak, (Shape.HasType.lift a1).2 h4⟩
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
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      cases h with | bot => cases hm rfl | app h1 h2 h3
    · exact .app ((ih1 W).1.1 h1) ((ih2 W).1.1 h2) h3
    · exact .app ((ih1 W).1.2 h1) ((ih2 W).1.2 h2) h3
    · exact sound_app (ih1 W).2 (hsort (ih3 W).2) (.app h1 h2 h3)
  | @lamDF _ _ _ _ B _ body body' _ _ _ ih1 _ ih2 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      cases h with | bot => cases hm rfl | @lam _ n a _ f _ m h1 h2 h3 h4
    · refine .lam ((ih1 W).1.1 h1) h2 (fun _ h => ?_) h4
      exact (ih2 (W.cons (hsort (ih1 W).2) h1 h)).1.1 (h3 _ h)
    · refine .lam ((ih1 W).1.2 h1) h2 (fun _ h => ?_) h4
      exact (ih2 (W.cons (hsort (ih1 W).2) ((ih1 W).1.2 h1) h)).1.2 (h3 _ h)
    · cases m with simp [Shape.LE.def] at h4 | bot => cases hm rfl | lam f'
      have ⟨m', a', le, a1, a2, a3⟩ := hsort (ih1 W).2 h1
      suffices ∃ n', n ≤ n' ∧ ∃ f' b : ShapeFun n', ShapeFun.LE (ShapeFun.lift Shape.lift f) f' ∧
          Shape.HasDom f' a.lift ∧ Shape.HasDom b a.lift ∧ ∀ x, x.HasType a.lift →
          LE_Interp (ρ.push x) (f'.app x) body ∧ LE_Interp (ρ.push x) (b.app x) B ∧
          (f'.app x).HasType (b.app x) by
        have ⟨n', le', f₁, b, a1, a2, a3, a4⟩ := this; simp [forall_and] at a4
        have h1' := (LE_Interp.lift le').2 h1
        exact ⟨_+1, .lam f₁, _, Nat.succ_le_succ le',
          .trans (t := Shape.lift (n := _+1) (.lam f)) (Shape.lift_mono (Shape.LE.def.2 h4)) a1,
          .lam h1' a2 a4.1 .rfl, .forallE h1' h1' a3 a4.2.1 .rfl,
          .lam ⟨⟨a3, fun _ h => (a4.2.2 _ h).isType⟩, a2, a4.2.2⟩⟩
      replace h3 (p) (h : p ∈ f) : p.1.HasType a ∧ LE_Interp (ρ.push p.1) p.2 body :=
        have := Shape.HasDom.def.1 h2 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h3 _ this⟩
      have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : ShapeFun k,
          f'.map Prod.fst = f.map (·.1.lift) ∧ b.map Prod.fst = f.map (·.1.lift) ∧
          ∀ x fx, (x, fx) ∈ f → ∃ f'x bx, (x.lift, f'x) ∈ f' ∧ (x.lift, bx) ∈ b ∧
          fx.lift ≤ f'x ∧ LE_Interp (ρ.push x) f'x body ∧ LE_Interp (ρ.push x) bx B ∧
          f'x.HasType bx := by
        clear h2 h4
        induction f with
        | nil => exact ⟨_, Nat.le_refl _, fun _ _ => ⟨[], [], by simp⟩⟩
        | cons p _ ih; let (x, fx) := p
        simp only [List.mem_cons, forall_eq_or_imp] at h3
        have ⟨k₁, le1, H1⟩ := ih h3.2
        have ⟨m', f'x, bx, le, b1, b2, b3, b4⟩ :=
          (ih2 (W.cons (hsort (ih1 W).2) h1 h3.1.1)).2 h3.1.2
        refine ⟨k₁.max m', Nat.le_trans le (Nat.le_max_right ..), fun k le' => ?_⟩
        have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
        have ⟨f', b, a1, a2, a3⟩ := H1 _ le₁
        refine ⟨(x.lift, f'x.lift) :: f', (x.lift, bx.lift) :: b, ?_⟩
        simp [or_imp, forall_and, *]
        exact ⟨.inl (.inl ⟨Shape.lift_lift (.inl le) ▸ Shape.lift_mono b1,
          (LE_Interp.lift le₂).2 b2, (LE_Interp.lift le₂).2 b3,
          (Shape.HasType.lift le₂).2 b4⟩), by grind⟩
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
  | @forallEDF _ A _ _ body body' v _ _ ih1 ih2 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      cases h with | bot => cases hm rfl | @forallE _ n b₀ _ b f _ m h1 h2 h3 h4 h5
    · refine .forallE ((ih1 W).1.1 h1) ((ih1 W).1.1 h2) h3 (fun _ h => ?_) h5
      exact (ih2 (W.cons (hsort (ih1 W).2) h2 h)).1.1 (h4 _ h)
    · refine .forallE ((ih1 W).1.2 h1) ((ih1 W).1.2 h2) h3 (fun _ h => ?_) h5
      exact (ih2 (W.cons (hsort (ih1 W).2) ((ih1 W).1.2 h2) h)).1.2 (h4 _ h)
    · cases m with simp [Shape.LE.def] at h5 | bot => cases hm rfl | forallE b' f'
      have ⟨b₁, a1, a2, a3⟩ := hsort (ih1 W).2 h2
      suffices ∃ n', n ≤ n' ∧ ∃ f' : ShapeFun n', ShapeFun.LE (ShapeFun.lift Shape.lift f) f' ∧
          Shape.HasDom f' b.lift ∧ ∀ x, x.HasType b.lift →
          LE_Interp (ρ.push x) (f'.app x) body ∧ (f'.app x).HasType (.sort (v ≠ .zero)) by
        have ⟨n', le', f₁, b1, b2, b3⟩ := this; simp [forall_and] at b3
        have hJ := Shape.Join.mk (h1.compat h2)
        have ⟨m', b₂, le, c1, c2, c3⟩ := hsort' (ih1 W).2 (h1.join hJ h2)
        have le₁ := Nat.le_max_right n' m'
        have le₂ := Nat.le_max_left n' m'
        have hJ' := (Shape.Join.lift le).2 hJ
        have hJ₂ := (Shape.Join.lift (Nat.le_trans le le₁)).2 hJ
        have b2' := Shape.lift_lift (.inl le') ▸ (Shape.HasDom.lift le₂).2 b2
        refine ⟨n'.max m'+1, .forallE .., _, Nat.succ_le_succ (Nat.le_trans le le₁),
          Shape.LE.def.2 ⟨
            (Shape.lift_mono h5.1).trans (hJ₂.le.1.trans
              (Shape.lift_lift (.inl le) ▸ Shape.lift_mono c1)),
            .trans (ShapeFun.lift_mono h5.2)
              (ShapeFun.lift_lift (.inl le') ▸ ShapeFun.lift_mono b1)⟩,
          .forallE ((LE_Interp.lift le₁).2 c2)
            ((LE_Interp.lift le₂).2 <| (LE_Interp.lift le').2 h2)
            ((Shape.HasDom.lift le₂).2 b2) (fun x h => ?_) .rfl,
          .sort .rfl,
          .forallE ⟨.mono (Shape.lift_mono <| hJ'.le.2.trans c1)
            (Shape.lift_type ▸ (Shape.HasType.lift le₁).2 c3.toType)
            ((Shape.lift_lift (.inl le)).symm ▸ b2'), fun x h => ?_⟩⟩
        · refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq ..; d3 ▸ ?_
          simp [ShapeFun.lift] at d2; obtain ⟨_, _, d2, rfl, rfl⟩ := d2
          have := ShapeFun.app_of_mem d2 ▸ b3.1 _ (Shape.HasDom.def.1 b2 _ _ d2)
          refine (LE_Interp.lift le₂).2 <| this.mono_l ?_
          exact (Valuation.LE.push' le₂ (Nat.le_refl _)).2 ⟨.rfl, Shape.lift_self ▸ d1⟩
        · have ⟨y, d1, d2, d3⟩ := b2' x
          refine have ⟨_, _, e1, e2, e3⟩ := ShapeFun.app_eq _ y; have d3' := e3 ▸ d3; ?_
          simp [ShapeFun.lift] at e2; obtain ⟨_, _, e2, rfl, rfl⟩ := e2
          refine .mono_l (ShapeFun.app_mono_r d1) d3 <|
            e3 ▸ Shape.lift_sort.symm ▸ (Shape.HasType.lift le₂).2 ?_
          simpa [← ShapeFun.app_of_mem e2] using b3.2 _ (Shape.HasDom.def.1 b2 _ _ e2)
      replace h4 (p) (h : p ∈ f) : p.1.HasType b ∧ LE_Interp (ρ.push p.1) p.2 body :=
        have := Shape.HasDom.def.1 h3 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h4 _ this⟩
      have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : ShapeFun k,
          f'.map Prod.fst = f.map (·.1.lift) ∧
          ∀ x fx, (x, fx) ∈ f → ∃ f'x, (x.lift, f'x) ∈ f' ∧
          fx.lift ≤ f'x ∧ LE_Interp (ρ.push x) f'x body ∧ f'x.HasType (.sort (v ≠ .zero)) := by
        clear h3 h5
        induction f with
        | nil => exact ⟨_, Nat.le_refl _, fun _ _ => ⟨[], by simp⟩⟩
        | cons p _ ih; let (x, fx) := p
        simp only [List.mem_cons, forall_eq_or_imp] at h4
        have ⟨k₁, le1, H1⟩ := ih h4.2
        have ⟨m', f'x, bx, le, b1, b2, b3, b4⟩ :=
          (ih2 (W.cons (hsort (ih1 W).2) h2 h4.1.1)).2 h4.1.2
        refine ⟨k₁.max m', Nat.le_trans le (Nat.le_max_right ..), fun k le' => ?_⟩
        have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
        have ⟨f', a1, a2⟩ := H1 _ le₁
        refine ⟨(x.lift, f'x.lift) :: f', ?_⟩
        replace b4 : f'x.HasType (.sort (v ≠ .zero)) := by
          cases b3 with
          | sort h => exact .mono_r h .sort b4
          | bot => cases b4.bot_r; exact .bot .sort
        simp [or_imp, forall_and, *] at b4 ⊢
        exact ⟨.inl ⟨Shape.lift_lift (.inl le) ▸ Shape.lift_mono b1, (LE_Interp.lift le₂).2 b2,
          Shape.lift_sort ▸ (Shape.HasType.lift le₂).2 b4
          ⟩, by grind⟩
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
  | defeqDF _ _ ih1 ih2 =>
    refine ⟨(ih2 W).1, fun h => ?_⟩
    have ⟨_, _, _, le, h1, h2, h3, h4⟩ := (ih2 W).2 h
    exact ⟨_, _, _, le, h1, h2, (ih1 W).1.1 h3, h4⟩
  | beta _ _ _ _ ih1 ih2 ih3 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih3 W).2⟩
    · cases h with | bot => cases hm rfl | app h1 h2 h3
      cases h1 with | bot => cases hm (Shape.le_bot.1 h3) | lam h4 h5 h6 h7
      have ⟨_, _, a1, a2, a3, a4⟩ := (ih2 W).2 h2
      refine have ⟨_, b1, b2, b3⟩ := h5 _; LE_Interp.inst.2 ⟨_, _, ?_, h2.mono b1⟩
      exact (h6 _ b2).mono <| .trans h3 <| .trans (Shape.app_mono_l h7 _) b3
    · have ⟨n', _, h1, h2⟩ := LE_Interp.inst.1 h
      have ⟨_, _, _, le, a1, a2, a3, a4⟩ :=
        (ih2 W).2 <| (LE_Interp.lift (Nat.le_max_right n n')).2 h2
      have le' := Nat.max_le.1 le
      refine (LE_Interp.lift le'.1).1 <|
        .app (.lam a3 ((Shape.HasDom.single (y := m.lift)).2 a4) (fun _ h => ?_) .rfl) a2 ?_
      · simp [ShapeFun.single_app]; split <;> [skip; exact .bot]
        refine (LE_Interp.lift le'.1).2 <| h1.mono_l ?_
        refine (Valuation.LE.push' le'.2 (Nat.le_refl _)).2
          ⟨.rfl, .trans (Shape.lift_lift (.inl (Nat.le_max_right ..)) ▸ a1) ?_⟩
        rwa [Shape.lift_self]
      · rw [Shape.app, ShapeFun.single_app, if_pos .rfl]; exact .rfl
  | @eta _ e _ _ _ _ ih1 ih2 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih2 W).2⟩
    · have ⟨_, _, t, le, h1, h2, h3, h4⟩ := (ih2 W).2 h
      have ht : t ≠ .bot := fun h => by
        subst h; cases h4.bot_r; cases hm ((Shape.lift_le_bot le).1 h1)
      cases h2 with
      | bot => cases hm ((Shape.lift_le_bot le).1 h1)
      | @lam _ n _ _ f' _ _ a1 a2 a3 a4
      cases h3 with | bot => cases ht rfl | @forallE _ _ _ _ _ _ _ m₁ b1 b2 b3 b4 b5
      cases t with simp [Shape.LE.def] at b5 | bot => cases ht rfl | forallE a' b'
      cases h4.unfold with | bot => cases hm ((Shape.lift_le_bot le).1 h1) | @lam _ f _ _ d1
      have key : ∀ x y, (x, y) ∈ f' → y ≠ .bot →
          LE_Interp (n := n+1) ρ (ShapeS.lam (ShapeFun.single x y)) e := by
        intro x y hmem hy
        have := ShapeFun.app_of_mem hmem ▸ a3 x (Shape.HasDom.def.1 a2 _ _ hmem)
        cases this with | bot => cases hy rfl | @app _ _ f_s _ a_s _ _ c1 c2 c3
        cases f_s with | lam g => ?_ | _ => cases hy (Shape.le_bot.1 c3)
        refine .mono ?_ (LE_Interp.weak_iff.1 c1)
        simp [Shape.LE.def, ShapeFun.single_le]
        have ⟨k', le₁, _, hle⟩ := LE_Interp.bvar_iff.1 c2
        have ha_s : a_s ≤ x := (Shape.lift_le_lift le₁).1 hle
        have ⟨x'', y'', hle₁, hmemg, happ⟩ := ShapeFun.app_eq g a_s
        simp [Shape.app, happ] at c3
        exact ⟨_, _, hmemg, .trans hle₁ ha_s, c3⟩
      have main (l : List (Shape n × Shape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g : Shape (n+1),
            (∀ z, g ≤ z ↔ ∀ x y, (x, y) ∈ l → y ≠ .bot → .lam (ShapeFun.single x y) ≤ z) ∧
            LE_Interp (n := _+1) ρ g e := by
        induction l with | nil => exact ⟨.bot, by simp, .bot⟩ | cons p l ih; let (x, y) := p
        simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, a1, a2⟩ := ih H.2
        by_cases hy : y = .bot
        · exact ⟨g, fun z => (a1 z).trans (by simp [or_imp, forall_and, hy]), a2⟩
        · have := Shape.Join.mk (x := g) (y := .lam (ShapeFun.single x y)) sorry
          refine ⟨_, fun z => (this z).trans ?_, .join this a2 (key _ _ H.1 hy)⟩
          simp [a1, or_imp, forall_and, and_comm, hy]
      have ⟨g, a1, a2⟩ := main f' (fun _ => id)
      refine (lift le).1 <| a2.mono <| h1.trans <| a4.trans ?_
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
    · have ⟨_, m', f, le, a1, a2, a3, a4⟩ := (ih1 W).2 h
      have hf : f ≠ .bot := fun h => by
        subst h; cases a4.bot_r; cases hm ((Shape.lift_le_bot le).1 a1)
      cases a3 with | bot => cases hf rfl | @forallE _ _ _ _ _ _ _ m₁ b1 b2 b3 b4 b5
      cases m₁ with simp [Shape.LE.def] at b5 | bot => cases hf rfl | forallE
      cases a4.unfold with | bot => cases hm ((Shape.lift_le_bot le).1 a1) | lam d1
      refine (LE_Interp.lift le).1 <| .lam (b1.mono b5.1) d1.2.1 (fun _ h => ?_) a1
      exact .app a2.weak (.bvar (Nat.le_refl _) (Nat.le_refl _) .rfl) .rfl
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
  DefEq' (M N A : SExpr) (m a : Shape n) : Prop

def LogRelBase.DefEq (R : LogRelBase Γ n) (M N A : SExpr) (m a : Shape n) : Prop :=
  Shape.HasType m a ∧ Γ ⊢ M ≡ N : A
    ∧ LE_Interp .nil m M ∧ LE_Interp .nil m N ∧ LE_Interp .nil a A
    -- ∧ CheckType Γ M A u ∧ CheckType Γ N A u ∧ InferTypeS Γ A (.sort u)
    ∧ R.DefEq' M N A m a

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  -- isType : toLogRelBase.DefEq M N A m a → Γ ⊢ A ≡ A : .sort u → DefEq' A A (.sort u) a (.sort (u ≠ .zero))
  sort : DefEq' (.sort u) (.sort u) (.sort u.succ) (.sort (u ≠ .zero)) .type
  left : DefEq' M N A m a → DefEq' M M A m a
  symm : DefEq' M N A m a → DefEq' N M A m a
  trans : DefEq' M₁ M₂ A m a → DefEq' M₂ M₃ A m a → DefEq' M₁ M₃ A m a
  defeqDF : toLogRelBase.DefEq A B (.sort u) a (.sort (u ≠ .zero)) →
    DefEq' M N A m a → DefEq' M N B m a
  mono_2 : m.HasType a → m ≤ m' → a ≤ a' →
    a'.HasType .type → LE_Interp .nil a' A → DefEq' M N A m' a' → DefEq' M N A m a
  mono_r_1 : m.HasType a → a ≤ a' →
    a'.HasType .type → LE_Interp .nil a' A → DefEq' M N A m a → DefEq' M N A m a'
  join : m₁ ≠ .bot → m₂ ≠ .bot → m₁.Compat m₂ →
    toLogRelBase.DefEq M N A m₁ a → toLogRelBase.DefEq M N A m₂ a → DefEq' M N A (m₁.join m₂) a

-- theorem LogRelBase.DefEq.isType {R : LogRel Γ n}
--     (H : R.DefEq M N A m a) : ∃ u, R.DefEq A A (.sort u) a (.sort (u ≠ .zero)) :=
--   have ⟨h1, h2, _, _, h5, _⟩ := H
--   have ⟨_, h2'⟩ := h2.isType
--   -- h1.isType : HasType a .type; goal needs HasType a (.sort (u ≠ .zero))
--   -- This holds since u ≠ .zero whenever a ≠ .bot (LE_Interp + sort-typing invariant).
--   -- TODO: replace sorry with proper proof once LE_Interp inversion lemmas are available.
--   ⟨_, by sorry, h2', h5, h5, .sort .rfl, R.isType H h2'⟩

theorem LogRelBase.DefEq.mono_2 {R : LogRel Γ n}
    (hm : m.HasType a) (le1 : m ≤ m') (le2 : a ≤ a') (ha' : a'.HasType .type) :
    R.DefEq M N A m' a' → R.DefEq M N A m a
  | ⟨_, h2, h3, h4, h5, h6⟩ =>
    ⟨hm, h2, h3.mono le1, h4.mono le1, h5.mono le2, R.mono_2 hm le1 le2 ha' h5 h6⟩

theorem LogRelBase.DefEq.mono_l {R : LogRel Γ n}
    (hm : m.HasType a) (le : m ≤ m') (H : R.DefEq M N A m' a) : R.DefEq M N A m a :=
  H.mono_2 hm le .rfl hm.isType

theorem LogRelBase.DefEq.mono_r_1 {R : LogRel Γ n}
    (ha : a ≤ a') (ha' : a'.HasType .type) (hLE : LE_Interp .nil a' A) :
    R.DefEq M N A m a → R.DefEq M N A m a'
  | ⟨ht, h2, h3, h4, _, h6⟩ =>
    ⟨.mono_r ha ha' ht, h2, h3, h4, hLE, R.mono_r_1 ht ha ha' hLE h6⟩

theorem LogRelBase.DefEq.mono_r_2 {R : LogRel Γ n}
    (ht : m.HasType a) (ha : a ≤ a') (H : R.DefEq M N A m a') : R.DefEq M N A m a :=
  H.mono_2 ht .rfl ha H.1.isType

theorem LogRelBase.DefEq.left {R : LogRel Γ n} : R.DefEq M N A m a → R.DefEq M M A m a
  | ⟨h1, h2, h3, _, h5, h6⟩ => ⟨h1, h2.hasType.1, h3, h3, h5, R.left h6⟩

theorem LogRelBase.DefEq.symm {R : LogRel Γ n} : R.DefEq M N A m a → R.DefEq N M A m a
  | ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2.symm, h4, h3, h5, R.symm h6⟩

theorem LogRelBase.DefEq.trans {R : LogRel Γ n} :
    R.DefEq M₁ M₂ A m a → R.DefEq M₂ M₃ A m a → R.DefEq M₁ M₃ A m a
  | ⟨a1, a2, a3, _, a5, a6⟩, ⟨_, b2, _, b4, _, b6⟩ => ⟨a1, a2.trans b2, a3, b4, a5, R.trans a6 b6⟩

theorem LogRelBase.DefEq.join {R : LogRel Γ n} (hJ : m₁.Join m₂ m)
    (h1 : R.DefEq M N A m₁ a) (h2 : R.DefEq M N A m₂ a) : R.DefEq M N A m a := by
  by_cases c1 : m₁ = .bot
  · exact .mono_2 (.join hJ h1.1 h2.1) ((hJ _).2 ⟨c1 ▸ Shape.bot_le, .rfl⟩) .rfl h1.1.isType h2
  by_cases c2 : m₂ = .bot
  · exact .mono_2 (.join hJ h1.1 h2.1) ((hJ _).2 ⟨.rfl, c2 ▸ Shape.bot_le⟩) .rfl h2.1.isType h1
  let ⟨a1, a2, a3, a4, a5, _⟩ := h1; let ⟨b1, _, b3, b4, _⟩ := h2
  refine ⟨a1.join hJ b1, a2, a3.join hJ b3, a4.join hJ b4, a5, ?_⟩
  exact R.mono_2 (a1.join hJ b1) (Shape.Join.iff.1 hJ).2.2 .rfl b1.isType a5
    (R.join c1 c2 hJ.compat h1 h2)

theorem LogRelBase.DefEq.defeqDF {R : LogRel Γ n}
    (hA : R.DefEq A B (.sort u) a (.sort (u ≠ .zero))) : R.DefEq M N A m a → R.DefEq M N B m a
  | ⟨ht, h2, h3, h4, _, h6⟩ =>
    let ⟨_, a2, _, a4, _⟩ := hA
    have ⟨_, b1⟩ := a2.isType
    ⟨ht, .defeqDF (b1.defeqDF a2) h2, h3, h4, a4, R.defeqDF hA h6⟩

theorem LogRelBase.DefEq.sort {R : LogRel Γ n} :
    R.DefEq (.sort u) (.sort u) (.sort u.succ) (.sort (u ≠ .zero)) .type :=
  ⟨.sort, .sort, .sort .rfl, .sort .rfl, .sort (by simpa [SLevel.succ_ne_zero] using .rfl), R.sort⟩

theorem LogRel.mono_r {R : LogRel Γ n}
    (ht : m.HasType a) (ha' : a'.HasType .type) (hLE : LE_Interp .nil a' A) (ha : a ≤ a') :
    R.DefEq M N A m a ↔ R.DefEq M N A m a' := ⟨.mono_r_1 ha ha' hLE, .mono_r_2 ht ha⟩

def LR0.DefEqTy (Γ : List SExpr) (M N : SExpr) (m : Shape 0) : Prop :=
  match m with
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u

def LRS.DefEqTy (IH : LogRel Γ n)
    (Γ : List SExpr) (M N : SExpr) (m : Shape (n+1)) : Prop :=
  match m with
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  | .forallE m₁ m₂ =>
    ∃ M₁ M₂ N₁ N₂, Γ ⊢ M ⤳* .forallE M₁ M₂ ∧ Γ ⊢ N ⤳* .forallE N₁ N₂ ∧
    ∃ u v, IH.DefEq M₁ N₁ (.sort u) m₁ (.sort (u ≠ .zero)) ∧ M₁::Γ ⊢ M₂ ≡ N₂ : sort v ∧
    (∀ {{a b p}}, IH.DefEq a b M₁ p m₁ →
      IH.DefEq (M₂.inst a) (M₂.inst b) (.sort v) (ShapeFun.app m₂ p) (.sort (v ≠ .zero)) ∧
      IH.DefEq (N₂.inst a) (N₂.inst b) (.sort v) (ShapeFun.app m₂ p) (.sort (v ≠ .zero))) ∧
    (∀ {{a p}}, IH.DefEq a a M₁ p m₁ →
      IH.DefEq (M₂.inst a) (N₂.inst a) (.sort v) (ShapeFun.app m₂ p) (.sort (v ≠ .zero)))
  | _ => False

def LRS.DefEqForall (IH : LogRel Γ n) (M N A₁ A₂ : SExpr) (m : Shape (n+1))
    (a₁ : Shape n) (a₂ : ShapeFun n) : Prop :=
  match m with
  | .bot => True
  | .lam m =>
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ →
      IH.DefEq (M.app a) (M.app b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) ∧
      IH.DefEq (N.app a) (N.app b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p)) ∧
    (∀ {{a p}}, IH.DefEq a a A₁ p a₁ →
      IH.DefEq (M.app a) (N.app a) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p))
  | _ => False

def LRS.DefEq' (IH : LogRel Γ n) (M N A : SExpr) (m a : Shape (n+1)) : Prop :=
  match a with
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ A ⤳* .sort u ∧ DefEqTy IH Γ M N m
  | .forallE a₁ a₂ => ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
    IH.DefEq A₁ A₁ (.sort u) a₁ (.sort (u ≠ .zero)) ∧ A₁::Γ ⊢ A₂ : sort v ∧
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ →
      IH.DefEq (A₂.inst a) (A₂.inst b) (.sort v) (ShapeFun.app a₂ p) (.sort (v ≠ .zero))) ∧
    DefEqForall IH M N A₁ A₂ m a₁ a₂
  | _ => False

def LR0.DefEq' (Γ : List SExpr) (M N A : SExpr) (m a : Shape 0) : Prop :=
  match a with
  | .bot => True
  | .sort _ => ∃ u, Γ ⊢ A ⤳* .sort u ∧ DefEqTy Γ M N m

def LR0 : LogRel Γ 0 where
  DefEq' := LR0.DefEq' Γ
  -- isType {M N A m a u} h1 hA := by
  --   let ⟨h1, h2, _, _, _, h6⟩ := h1
  --   simp [LR0.DefEq'] at h6; split at h6
  --   · exact ⟨_, .rfl, trivial⟩
  --   · obtain ⟨⟨v, h1⟩, h2⟩ := h6; exact ⟨_, .rfl, _, h1, h1⟩
  sort := ⟨_, .rfl, _, .rfl, .rfl⟩
  left {M N A m a} h1 := by
    dsimp [LR0.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [LR0.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, _⟩ := h3; exact ⟨h1, h3, h3⟩
  symm {M N A m a} h1 := by
    dsimp [LR0.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [LR0.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, h4⟩ := h3; exact ⟨h1, h4, h3⟩
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LR0.DefEq']; split
    · simp
    · rintro ⟨_, a1, a2⟩ ⟨_, -, b2⟩; refine ⟨_, a1, ?_⟩
      revert a2 b2; dsimp [LR0.DefEqTy]; split
      · simp
      · rintro ⟨_, a1, a2⟩ ⟨_, b1, b2⟩; cases a2.determ .sort b1 .sort; exact ⟨_, a1, b2⟩
  defeqDF {A B u a M N m} hA := by
    obtain ⟨A1, A2, _, _, _, A6⟩ := hA
    dsimp [LR0.DefEq']; split
    · trivial
    · rintro ⟨u, a1, a2⟩
      let ⟨_, _, _, _, b3⟩ := A6
      exact ⟨_, b3, a2⟩
  mono_2 {m m' a a' A M N} h1 hm ha ha' hA := by
    cases h1.unfold with
    | bot h1 =>
      cases ha'.unfold with
      | bot => cases Shape.le_bot.1 ha; exact fun _ => trivial
      | sort =>
        obtain rfl|rfl := Shape.le_sort.1 ha <;> [exact fun _ => trivial; skip]
        exact fun ⟨_, h, _⟩ => ⟨_, h, trivial⟩
    | sort =>
      cases m' <;> simp [(· ≤ ·), Shape.LE, Shape.ble] at hm
      cases a' <;> simp [(· ≤ ·), Shape.LE, Shape.ble] at ha
      subst_vars; exact id
  mono_r_1 {a a' A M N m} h1 le ha' hA := by
    cases ha'.unfold with
    | bot => cases Shape.le_bot.1 le; exact id
    | sort =>
      obtain rfl|rfl := Shape.le_sort.1 le <;> [rintro -; exact id]
      cases h1.unfold; exact ⟨sorry, sorry, ⟨⟩⟩
  join {m₁ m₂ M N A a} ne1 ne2 hc h1 _ := by
    cases m₁ with | bot => cases ne1 rfl | sort
    cases m₂ with | bot => cases ne2 rfl | sort
    simp [Shape.Compat] at hc; subst hc; simp [Shape.join]; exact h1.2.2.2.2.2

def LRS (IH : LogRel Γ n) : LogRel Γ (n + 1) where
  DefEq' := LRS.DefEq' IH
  -- isType {M N A m a u} h1 hA := by
  --   let ⟨h1, h2, _, _, _, h6⟩ := h1
  --   simp [LRS.DefEq'] at h6; split at h6
  --   · exact ⟨_, .rfl, trivial⟩
  --   · obtain ⟨⟨v, h1⟩, h2⟩ := h6; exact ⟨_, .rfl, _, h1, h1⟩
  --   · obtain ⟨_, _, h1, ⟨_, h2⟩, _, h3, h4, _⟩ := h6
  --     exact ⟨_, .rfl, _, _, _, _, h1, h1, _, _, h2, h3,
  --       fun _ _ _ a1 => ⟨h4 a1, h4 a1⟩, fun _ _ a1 => h4 a1⟩
  --   · cases h6
  sort := ⟨_, .rfl, _, .rfl, .rfl⟩
  left {M N A m a} h1 := by
    dsimp [LRS.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [LRS.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, _⟩ := h3; exact ⟨h1, h3, h3⟩
      · let ⟨_, _, _, _, h1, _, _, h3, h4, h4', h5, h6⟩ := h3
        exact ⟨_, _, _, _, h1, h1, _, h3, h4.left, h4'.hasType.1,
          fun a b p a1 => ⟨(h5 a1).1, (h5 a1).1⟩, fun a p a1 => (h5 a1).1⟩
      · cases h3
    · let ⟨_, _, _, _, h1, h3, h4, h5, h6⟩ := h1; refine ⟨_, _, _, _, h1, h3, h4, h5, ?_⟩
      dsimp [LRS.DefEqForall] at h6 ⊢; split at h6
      · trivial
      · exact ⟨fun a b p a1 => ⟨(h6.1 a1).1, (h6.1 a1).1⟩, fun a p a1 => (h6.1 a1).1⟩
      · cases h6
    · cases h1
  symm {M N A m a} h1 := by
    dsimp [LRS.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [LRS.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, h4⟩ := h3; exact ⟨h1, h4, h3⟩
      · let ⟨B, F, B', F', h1, h2, _, _, h3, h4, h5, h6⟩ := h3
        refine ⟨_, _, _, _, h2, h1, _, _, h3.symm, h3.2.1.defeqDF_l h4.symm, ?_, ?_⟩
        · exact fun a b p a1 => (h5 (.defeqDF h3.symm a1)).symm
        · exact fun a p a1 => (h6 (.defeqDF h3.symm a1)).symm
      · cases h3
    · let ⟨_, _, _, _, h1, h2, h3, h4, h6⟩ := h1; refine ⟨_, _, _, _, h1, h2, h3, h4, ?_⟩
      dsimp [LRS.DefEqForall] at h6 ⊢; split at h6
      · trivial
      · exact ⟨fun a b p a1 => (h6.1 a1).symm, fun a p a1 => (h6.2 a1).symm⟩
      · cases h6
    · cases h1
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LRS.DefEq']; split
    · simp
    · rintro ⟨_, a1, a2⟩ ⟨_, -, b2⟩; refine ⟨_, a1, ?_⟩
      revert a2 b2; dsimp [LRS.DefEqTy]; split
      · simp
      · rintro ⟨_, a1, a2⟩ ⟨_, b1, b2⟩; cases a2.determ .sort b1 .sort; exact ⟨_, a1, b2⟩
      · rintro ⟨B, F, B', F', a1', a2, u, v, a4, a4', a5, a6⟩
               ⟨B₁, F₁, B₂, F₂, b1, b2, u', v', b4, b4', b5, b6⟩
        cases a2.determ .forallE b1 .forallE
        replace b4' := a4.2.1.symm.defeqDF_l b4'
        cases a4.2.1.uniq_sort b4.2.1; cases a4'.uniq_sort b4'
        obtain c4 := a4.trans b4
        refine ⟨_, _, _, _, a1', b2, _, v, a4.trans b4, a4'.trans b4',
          fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩
        · exact ⟨(a5 c1).1, (b5 (.defeqDF a4 c1)).2⟩
        · exact (a6 c1).trans (b6 (.defeqDF a4 c1))
      · nofun
    · rintro ⟨_, _, u, v, a1, a2, a3, a4, a5⟩ ⟨_, _, u', v', b1, b2, b3, b4, b5⟩
      cases a1.determ .forallE b1 .forallE
      cases a2.2.1.uniq_sort b2.2.1; cases a3.uniq_sort b3
      refine ⟨_, _, _, _, a1, a2, a3, a4, ?_⟩
      revert a5 b5; dsimp [LRS.DefEqForall]; split
      · simp
      · intro ⟨a5, a6⟩ ⟨b5, b6⟩
        exact ⟨fun _ _ _ c1 => ⟨(a5 c1).1, (b5 c1).2⟩, fun _ _ c1 => (a6 c1).trans (b6 c1)⟩
      · nofun
    · nofun
  defeqDF {A B u a M N m} hA := by
    obtain ⟨A1, A2, _, _, _, A6⟩ := hA
    dsimp [LRS.DefEq']; split
    · trivial
    · rintro ⟨u, a1, a2⟩
      let ⟨_, _, _, _, b3⟩ := A6
      exact ⟨_, b3, a2⟩
    · rename_i b f; rintro ⟨B₁, F₁, _, _, a1, a2, a3, a4, a5⟩
      let ⟨_, b1, B₁', F₁', B₂, F₂, b2, b3, _, _, b4, b4', b5, b6⟩ := A6
      cases a1.determ .forallE b2 .forallE
      refine ⟨_, _, _, _, b3, b4.symm.left, b4.2.1.defeqDF_l b4'.hasType.2,
        fun _ _ _ c1 => (b5 (.defeqDF b4.symm c1)).2, ?_⟩
      revert a5; dsimp [LRS.DefEqForall]; split
      · simp
      · refine fun ⟨d1, d2⟩ => ⟨fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩ <;>
          have c2 := b4.symm.defeqDF c1
        · exact ⟨.defeqDF (b6 c2.left) (d1 c2).1, .defeqDF (b6 c2.left) (d1 c2).2⟩
        · exact .defeqDF (b6 c2) (d2 c2)
      · nofun
    · nofun
  mono_2 {m m' a a' A M N} h1 hm ha ha' hA := by
    cases h1.unfold with
    | bot h1 =>
      cases ha'.unfold with
      | bot => cases Shape.le_bot.1 ha; exact fun _ => trivial
      | sort =>
        obtain rfl|rfl := Shape.le_sort.1 ha <;> [exact fun _ => trivial; skip]
        exact fun ⟨_, h, _⟩ => ⟨_, h, trivial⟩
      | forallE =>
        sorry
        -- cases a with simp [Shape.LE.def] at ha | bot => exact fun _ => trivial | forallE
        -- have .forallE ht := h1.unfold; intro ⟨_, _, _, _, b1, b2, b3, b4, b5⟩
        -- refine ⟨_, _, _, _, b1, .mono_l ht.1.isType ha.1 b2, b3, fun _ _ _ c1 => ?_, ⟨⟩⟩
        -- exact (b4 (b2.mono_r_1 ha.1 c1)).mono_l (ht.2 _ c1.1) (ShapeFun.app_mono_l ha.2 _)
    | sort =>
      cases m' <;> simp [Shape.LE.def] at hm
      cases a' <;> simp [Shape.LE.def] at ha
      exact id
    | forallE ht =>
      cases m' <;> simp [Shape.LE.def] at hm
      cases a' <;> simp [Shape.LE.def] at ha
      sorry
      -- intro ⟨_, a3, _, _, _, _, a4, a5, _, _, a6, a7, a8, a9⟩
      -- refine ⟨_, a3, _, _, _, _, a4, a5, _, _, a6.mono_l ht.1.isType hm.1, a7,
      --   fun _ _ _ d => ?_, fun _ _ d => ?_⟩ <;>
      --   have ⟨d1, d2⟩ := a8 (.mono_r_1 hm.1 a6.left d)
      -- · exact have d3 := ht.2 _ d.1; have d4 := ShapeFun.app_mono_l hm.2 _
      --     ⟨d1.mono_l d3 d4, d2.mono_l d3 d4⟩
      -- · exact (a9 (a6.left.mono_r_1 hm.1 d)).mono_l (ht.2 _ d.1) (ShapeFun.app_mono_l hm.2 _)
    | lam ht =>
      cases m' <;> simp [Shape.LE.def] at hm
      cases a' <;> simp [Shape.LE.def] at ha
      sorry
      -- rintro ⟨_, _, _, _, a1, a2, a3, a4, a5, a6⟩
      -- refine ⟨_, _, _, _, a1, .mono_l ht.1.1.isType ha.1 a2, a3,
      --   fun _ _ _ d => ?_, fun _ _ _ d => ?_, fun _ _ d => ?_⟩
      -- · exact .mono_l (ht.1.2 _ d.1) (ShapeFun.app_mono_l ha.2 _) (a4 (.mono_r_1 ha.1 a2 d))
      -- · have ⟨a7, a8⟩ := a5 (.mono_r_1 ha.1 a2 d)
      --   exact
      --     have h1 := ht.2.2 _ d.1; have h2 := ShapeFun.app_mono_l hm _
      --     have h3 := ShapeFun.app_mono_l ha.2 _; have h4 := a4 (.mono_r_1 ha.1 a2 d.left)
      --     ⟨.mono_2 h1 h2 h3 h4 a7, .mono_2 h1 h2 h3 h4 a8⟩
      -- · exact .mono_2 (ht.2.2 _ d.1) (ShapeFun.app_mono_l hm _)
      --     (ShapeFun.app_mono_l ha.2 _) (a4 (.mono_r_1 ha.1 a2 d.left)) (a6 (.mono_r_1 ha.1 a2 d))
  mono_r_1 {a a' A M N m} h1 le ha' hA := by
    cases ha'.unfold with
    | bot => cases Shape.le_bot.1 le; exact id
    | sort =>
      obtain rfl|rfl := Shape.le_sort.1 le <;> [rintro -; exact id]
      cases h1.unfold; exact ⟨sorry, sorry, ⟨⟩⟩
    | forallE =>
      sorry
      -- have ⟨_, _, _, _, A4, A5, _, _, A6, A7, A8, A9⟩ := A4
      -- refine fun h2 => ⟨_, _, _, _, A4, A6.left, A7.hasType.1, fun _ _ _ c1 => (A8 c1).1, ?_⟩
      -- cases a with simp [Shape.LE.def] at le | bot => cases h1.unfold; trivial | forallE
      -- cases h1.unfold with | bot => trivial | lam h
      -- have ⟨_, _, _, _, B4, B5, _, B6, B7, B8⟩ := h2
      -- cases A4.determ .forallE B4 .forallE
      -- refine ⟨fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩
      -- · have ⟨_, c2, c3, eq⟩ := Shape.HasType.maximal
      --     (fun x y hy => ⟨Shape.HasDom.def.1 h.2.1 x y hy, (Shape.HasTypeLam.def.1 h).2.2 x y hy⟩)
      --     le.1 c1.1
      --   have ⟨b1, b2⟩ := B7 (.mono_2 c2 c3 le.1 A6.left c1)
      --   exact have h3 := .trans (ShapeFun.app_mono_l le.2 _) (ShapeFun.app_mono_r c3)
      --     ⟨.mono_r_1 h3 (A8 c1).1.left (eq ▸ b1), .mono_r_1 h3 (A8 c1).1.left (eq ▸ b2)⟩
      -- · have ⟨_, c2, c3, eq⟩ := Shape.HasType.maximal
      --     (fun x y hy => ⟨Shape.HasDom.def.1 h.2.1 x y hy, (Shape.HasTypeLam.def.1 h).2.2 x y hy⟩)
      --     le.1 c1.1
      --   exact have h3 := .trans (ShapeFun.app_mono_l le.2 _) (ShapeFun.app_mono_r c3)
      --     .mono_r_1 h3 (A8 c1).1.left (eq ▸ B8 (.mono_2 c2 c3 le.1 A6.left c1))
  join {m₁ m₂ M N A a} ne1 ne2 hC h1 h2 := by
    cases h1.1.unfold with
    | bot => cases ne1 rfl
    | sort =>
      cases m₂ with simp [Shape.Compat] at hC | bot => cases ne2 rfl | sort
      subst hC; simp [Shape.join]; exact h1.2.2.2.2.2
    | forallE ht₁ =>
      cases m₂ with simp [Shape.Compat] at hC | bot => cases ne2 rfl | forallE
      simp [Shape.join]
      have hJ₁ := Shape.Join.mk hC.1; have hJ₂ := ShapeFun.Join.mk hC.2
      have ⟨_, _, _, _, _, _, a1, _, _, _, _, a2, a3, _, _, a4, a5, a6, a7⟩ := h1
      have ⟨b0, _, _, _, _, _, b1, _, _, _, _, b2, b3, _, _, b4, b5, b6, b7⟩ := h2
      cases a2.determ .forallE b2 .forallE; cases a3.determ .forallE b3 .forallE
      cases a4.2.1.uniq_sort b4.2.1.symm
      cases a5.uniq_sort b5.symm
      have .forallE ht₂ := b0.unfold
      have hJ' := a4.join hJ₁ b4
      refine ⟨_, a1, _, _, _, _, a2, a3, _, _, hJ', a5, fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩
      all_goals
        obtain ⟨_, _, d1, d2, rfl⟩ := ShapeFun.app_eq _ _
        have d3 := Shape.HasDom.def.1 ht₁.1 _ _ d2
        have c2 := c1.mono_l (hJ'.1.mono_r hJ₁.le.1 d3) d1 |>.mono_r_2 d3 hJ₁.le.1
        obtain ⟨_, _, e1, e2, rfl⟩ := ShapeFun.app_eq _ _
        have e3 := Shape.HasDom.def.1 ht₂.1 _ _ e2
        have c3 := c1.mono_l (hJ'.1.mono_r hJ₁.le.2 e3) e1 |>.mono_r_2 e3 hJ₁.le.2
      · constructor
        · have ha := ShapeFun.app_of_mem d2 ▸ (a6 c2).1
          have hb := ShapeFun.app_of_mem e2 ▸ (b6 c3).1
          exact ha.join (ShapeFun.Join.app hJ₂ _) hb
        · have ha := ShapeFun.app_of_mem d2 ▸ (a6 c2).2
          have hb := ShapeFun.app_of_mem e2 ▸ (b6 c3).2
          exact ha.join (ShapeFun.Join.app hJ₂ _) hb
      · have ha := ShapeFun.app_of_mem d2 ▸ a7 c2
        have hb := ShapeFun.app_of_mem e2 ▸ b7 c3
        exact ha.join (ShapeFun.Join.app hJ₂ _) hb
    | lam ht₁ =>
      cases m₂ with simp [Shape.Compat] at hC | bot => cases ne2 rfl | lam
      simp [Shape.join]
      have hJ := ShapeFun.Join.mk hC
      have ⟨_, _, _, _, _, _, _, _, _, a1, a2, a3, a4, a5, a6⟩ := h1
      have ⟨_, _, _, _, _, _, _, _, _, b1, b2, b3, b4, b5, b6⟩ := h2
      cases a1.determ .forallE b1 .forallE
      refine ⟨_, _, _, _, a1, a2, a3, a4, fun _ _ _ c1 => ⟨?_, ?_⟩, fun _ _ c1 => ?_⟩
      · exact (a5 c1).1.join (ShapeFun.Join.app hJ _) (b5 c1).1
      · exact (a5 c1).2.join (ShapeFun.Join.app hJ _) (b5 c1).2
      · exact (a6 c1).join (ShapeFun.Join.app hJ _) (b6 c1)

def LR (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => LR0
  | _+1 => LRS (LR Γ)

inductive LR.Subst : (Γ : List SExpr) → (σ : Subst) → (Δ : List SExpr) → Valuation → Prop
  | nil : LR.Subst Γ .id Γ .nil
  | cons : LR.Subst Γ σ.tail Δ ρ →
    (∀ a, LE_Interp ρ a A →
      (LR Γ).DefEq (A.subst σ.tail) (A.subst σ.tail) (.sort u) a (.sort (u ≠ .zero))) →
    LE_Interp ρ a A → (LR Γ).DefEq σ.head σ.head (A.subst σ.tail) x a →
    LR.Subst Γ σ (A::Δ) (ρ.push x)

theorem LR.Subst.fits (W : LR.Subst Γ σ Δ ρ) : ρ.Fits Γ Δ := sorry

theorem LR.fundamental (H : Γ ⊢ M ≡ N : A) (W : LR.Subst Γ₀ σ Γ ρ)
    (hM : LE_Interp ρ m M) :
    ∃ a, LE_Interp ρ a A ∧ (LR Γ₀).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a := by
  replace H := H.strong; induction H generalizing m with
  | bvar h =>
    sorry
  | symm H ih =>
    have hN := (LE_Interp.sound H.defeq W.fits).1.2 hM
    have ⟨_, h1, h2⟩ := ih W hN; exact ⟨_, h1, h2.symm⟩
  | trans _ H1 H2 ihA ih1 ih2 =>
    have ⟨_, h1, h2⟩ := ih1 W hM
    have hN := (LE_Interp.sound H1.defeq W.fits).1.1 hM
    have ⟨_, h3, h4⟩ := ih2 W hN
    have hJ := Shape.Join.mk (h1.compat h3)
    have ⟨a1, a2⟩ := hJ.le; have a3 := h1.join hJ h3
    have ⟨_, c1, c2⟩ := ihA W a3
    -- TODO: adapt to new mono_r_1 signature (needs ha' : a'.HasType .type, hLE : LE_Interp .nil a' A)
    -- Old code:
    -- exact have c2 := .mono_r_1 c1.le_sort LogRelBase.DefEq.sort c2
    --   ⟨_, a3, .trans (.mono_r_1 a1 c2 h2) (.mono_r_1 a2 c2 h4)⟩
    sorry
  | _ => sorry


/-! ### Agda-aligned definitions (Val2/ValTy2 hierarchy)

These definitions mirror the Agda `Validity2.agda` structure more closely.
Key differences from `DefEq'`/`LogRelBase` above:

1. **Separate type validity (`ValTy2`)**: Type validity is a separate predicate from
   term validity, trivial at sort shapes (matching Agda's `ValTy2 G M UCode = Top`).
   Current `DefEq'` bundles type validity inside `IH.DefEq ... (.sort (u ≠ .zero))`.

2. **`.type` instead of `.sort (u ≠ .zero)`**: Inner type judgments use `.type`
   as the type-shape, matching Agda's use of `UCode` everywhere for the universe.
   This avoids the `HasType a (.sort false) = false` issue that made `isType` unprovable.

3. **Lighter inner type judgments**: `TyDefEq` (5-tuple) drops `LE_Interp .nil a A`
   from the full `DefEq` 6-tuple, and uses `ValTy2` instead of `DefEq'` for semantic content.

Correspondence with Agda `Validity2.agda`:
- `LogRel2Base.ValTy2` ↔ merged `ValTy2` / `EqValTy2`
- `LogRel2Base.Val2`   ↔ merged `Val2` / `EqVal2`
- `LR2S.PiEdge2`        ↔ merged `PiEdgeVal2` / `PiEdgeEq2`
- `LR2S.PiEdgeEqTy2`    ↔ `PiEdgeEqTy2`
- `LR2S.ValPi2`         ↔ merged `ValPi2` / `EqValPi2` (term application)
- `LogRel2Base.TyDefEq` ↔ inner type judgment using `UCode` / `.type`
-/

/-- Base structure for the Agda-aligned logical relation.
Two abstract predicates: term validity `Val2` and type validity `ValTy2`. -/
structure LogRel2Base (Γ : List SExpr) (n : Nat) where
  /-- Term validity: `M ≡ N : A` at element-shape `m` and type-shape `a`. -/
  Val2 (M N A : SExpr) (m a : Shape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at type-shape `a`.
  Trivial at sort shapes; only non-trivial at forallE. -/
  ValTy2 (A B : SExpr) (a : Shape n) : Prop

/-- Full term-level judgment: syntactic + interpretations + semantic `Val2`.
Same shape as `LogRelBase.DefEq` but uses `Val2` for the semantic field. -/
def LogRel2Base.DefEq (R : LogRel2Base Γ n) (M N A : SExpr) (m a : Shape n) : Prop :=
  Shape.HasType m a ∧ Γ ⊢ M ≡ N : A
    ∧ LE_Interp .nil m M ∧ LE_Interp .nil m N ∧ LE_Interp .nil a A
    ∧ R.Val2 M N A m a

/-- Type-level judgment: like `DefEq` but with `.type` as the type-shape.
Drops the `LE_Interp .nil .type (.sort u)` field (unprovable when `u = .zero`)
and uses `ValTy2` instead of `Val2` for the semantic field. -/
def LogRel2Base.TyDefEq (R : LogRel2Base Γ n) (M N : SExpr) (u : SLevel) (m : Shape n) : Prop :=
  Shape.HasType m .type ∧ Γ ⊢ M ≡ N : .sort u
    ∧ LE_Interp .nil m M ∧ LE_Interp .nil m N
    ∧ R.ValTy2 M N m

/-- `LogRel2` extends `LogRel2Base` with structural operations.
Fields mirror Agda's `Validity2.agda` mutual block. Coherence hypotheses are
systematically omitted (every shape is treated as coherent via sorried lemmas). -/
structure LogRel2 (Γ : List SExpr) (n : Nat) extends LogRel2Base Γ n where
  -- basic structural
  sort : Val2 M N A (.sort r) (.sort r')
  bot : a.HasType .type → Val2 M N A .bot a
  -- isType : Val2 M N A m a → ValTy2 A A a
  toType : Val2 M N A m (.sort r) → ValTy2 M N m
  left : Val2 M N A m a → Val2 M M A m a
  left_ty : ValTy2 M N m → ValTy2 M M m
  symm : Val2 M N A m a → Val2 N M A m a
  symm_ty : ValTy2 M N m → ValTy2 N M m
  trans : Val2 M₁ M₂ A m a → Val2 M₂ M₃ A m a → Val2 M₁ M₃ A m a
  trans_ty : ValTy2 M₁ M₂ m → ValTy2 M₂ M₃ m → ValTy2 M₁ M₃ m
  -- type conversion transport (Agda: Val2-EqValTy2-fwd + EqVal2-EqValTy2-fwd)
  conv : ValTy2 A B a → Val2 M N A m a → Val2 M N B m a
  -- monotonicity in type-shape: decrease (Agda: downVal2 + downEqVal2)
  mono_r_2 : a ≤ a' → m.HasType a → a'.HasType .type → Val2 M N A m a' → Val2 M N A m a
  -- monotonicity in type-shape for types: decrease (Agda: downValTy2 + downEqValTy2)
  mono_r_2_ty : a ≤ a' → a.HasType .type → a'.HasType .type → ValTy2 A B a' → ValTy2 A B a
  -- monotonicity in type-shape: increase (Agda: upVal2 + upEqVal2)
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → ValTy2 A A a' → Val2 M N A m a → Val2 M N A m a'
  -- monotonicity in element-shape: decrease (Agda: restrictVal2 + restrictEqVal2)
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → Val2 M N A m' a → Val2 M N A m a
  -- supremum for types (Agda: ValTy2-Sup + EqValTy2-Sup)
  join_ty : m₁.Compat m₂ → m₁.HasType .type → m₂.HasType .type →
    ValTy2 A B m₁ → ValTy2 A B m₂ → ValTy2 A B (m₁.join m₂)
  -- head reduction (Agda: Val2-beta-expand/contract + EqVal2 variants, merged)
  whr : Γ ⊢ M ⤳* M' → Γ ⊢ N ⤳* N' → (Val2 M N A m a ↔ Val2 M' N' A m a)
  -- head reduction for types (Agda: ValTy2-headred-expand/contract + EqValTy2 variants, merged)
  whr_ty : Γ ⊢ A ⤳* A' → Γ ⊢ B ⤳* B' → (ValTy2 A B m ↔ ValTy2 A' B' m)

/-! #### Structural lemmas for DefEq / TyDefEq -/

-- theorem LogRel2Base.DefEq.isType {R : LogRel2 Γ n} :
--     R.DefEq M N A m a → ∃ u, R.TyDefEq A A u a
--   | ⟨h1, h2, _, _, h5, h6⟩ => h2.isType.imp fun _ hA => ⟨h1.isType, hA, h5, h5, R.isType h6⟩

theorem LogRel2Base.DefEq.left {R : LogRel2 Γ n} :
    R.DefEq M N A m a → R.DefEq M M A m a
  | ⟨h1, h2, h3, _, h5, h6⟩ => ⟨h1, h2.hasType.1, h3, h3, h5, R.left h6⟩

theorem LogRel2Base.DefEq.symm {R : LogRel2 Γ n} :
    R.DefEq M N A m a → R.DefEq N M A m a
  | ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2.symm, h4, h3, h5, R.symm h6⟩

theorem LogRel2Base.DefEq.trans {R : LogRel2 Γ n} :
    R.DefEq M₁ M₂ A m a → R.DefEq M₂ M₃ A m a → R.DefEq M₁ M₃ A m a
  | ⟨a1, a2, a3, _, a5, a6⟩, ⟨_, b2, _, b4, _, b6⟩ =>
    ⟨a1, a2.trans b2, a3, b4, a5, R.trans a6 b6⟩

theorem LogRel2Base.DefEq.conv {R : LogRel2 Γ n} :
    R.TyDefEq A B u a → R.DefEq M N A m a → R.DefEq M N B m a
  | ⟨_, a2, _, a4, a5⟩, ⟨b1, b2, b3, b4, _, b6⟩ =>
    ⟨b1, .defeqDF a2 b2, b3, b4, a4, R.conv a5 b6⟩

theorem LogRel2Base.TyDefEq.left {R : LogRel2 Γ n} :
    R.TyDefEq M N u m → R.TyDefEq M M u m
  | ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2.hasType.1, h3, h3, R.left_ty h5⟩

theorem LogRel2Base.TyDefEq.symm {R : LogRel2 Γ n} :
    R.TyDefEq M N u m → R.TyDefEq N M u m
  | ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2.symm, h4, h3, R.symm_ty h5⟩

theorem LogRel2Base.TyDefEq.trans {R : LogRel2 Γ n} :
    R.TyDefEq M₁ M₂ u m → R.TyDefEq M₂ M₃ u m → R.TyDefEq M₁ M₃ u m
  | ⟨a1, a2, a3, _, a5⟩, ⟨_, b2, _, b4, b5⟩ =>
    ⟨a1, a2.trans b2, a3, b4, R.trans_ty a5 b5⟩

-- Projections
theorem LogRel2Base.DefEq.hasType {R : LogRel2Base Γ n}
    (h : R.DefEq M N A m a) : Shape.HasType m a := h.1

theorem LogRel2Base.DefEq.isDefEq {R : LogRel2Base Γ n}
    (h : R.DefEq M N A m a) : Γ ⊢ M ≡ N : A := h.2.1

theorem LogRel2Base.DefEq.val2 {R : LogRel2Base Γ n}
    (h : R.DefEq M N A m a) : R.Val2 M N A m a := h.2.2.2.2.2

theorem LogRel2Base.TyDefEq.hasType {R : LogRel2Base Γ n}
    (h : R.TyDefEq M N u m) : Shape.HasType m .type := h.1

theorem LogRel2Base.TyDefEq.isDefEq {R : LogRel2Base Γ n}
    (h : R.TyDefEq M N u m) : Γ ⊢ M ≡ N : .sort u := h.2.1

theorem LogRel2Base.TyDefEq.valTy2 {R : LogRel2Base Γ n}
    (h : R.TyDefEq M N u m) : R.ValTy2 M N m := h.2.2.2.2

-- Monotonicity structural lemmas on DefEq / TyDefEq

theorem LogRel2Base.TyDefEq.mono_r_2 {R : LogRel2 Γ n} (le : m ≤ m') (hm : m.HasType .type) :
    R.TyDefEq A B u m' → R.TyDefEq A B u m
  | ⟨hm', h2, h3, h4, h5⟩ => ⟨hm, h2, h3.mono le, h4.mono le, R.mono_r_2_ty le hm hm' h5⟩

theorem LogRel2Base.DefEq.mono_r_1 {R : LogRel2 Γ n} (le : a ≤ a')
    (tyA : R.TyDefEq A A u a') : R.DefEq M N A m a → R.DefEq M N A m a'
  | ⟨h1, h2, h3, h4, _, h6⟩ =>
    ⟨.mono_r le tyA.hasType h1, h2, h3, h4, tyA.2.2.1,
     R.mono_r_1 le h1 (.mono_r le tyA.hasType h1) tyA.valTy2 h6⟩

theorem LogRel2Base.DefEq.mono_r_2 {R : LogRel2 Γ n}
    (le : a ≤ a') (hm : m.HasType a) (ht : a'.HasType .type) :
    R.DefEq M N A m a' → R.DefEq M N A m a
  | ⟨_, h2, h3, h4, h5, h6⟩ => ⟨hm, h2, h3, h4, h5.mono le, R.mono_r_2 le hm ht h6⟩

theorem LogRel2Base.DefEq.mono_l {R : LogRel2 Γ n}
    (le : m ≤ m') (hm : m.HasType a) : R.DefEq M N A m' a → R.DefEq M N A m a
  | ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨hm, h2, h3.mono le, h4.mono le, h5, R.mono_l le hm h1 h6⟩

theorem LogRel2Base.TyDefEq.join_ty {R : LogRel2 Γ n}
    (h1 : R.TyDefEq A B u m₁) (h2 : R.TyDefEq A B u m₂) :
    R.TyDefEq A B u (m₁.join m₂) :=
  have hC := LE_Interp.compat h1.2.2.1 h2.2.2.1
  have hJ := Shape.Join.mk hC
  ⟨.join hJ h1.hasType h2.hasType, h1.isDefEq, .join hJ h1.2.2.1 h2.2.2.1,
   .join hJ h1.2.2.2.1 h2.2.2.2.1, R.join_ty hC h1.hasType h2.hasType h1.valTy2 h2.valTy2⟩

theorem LogRel2Base.TyDefEq.join {R : LogRel2 Γ n} (hJ : Shape.Join m₁ m₂ m)
    (h1 : R.TyDefEq A B u m₁) (h2 : R.TyDefEq A B u m₂) :
    R.TyDefEq A B u m :=
  (h1.join_ty h2).mono_r_2 (Shape.Join.iff.1 hJ).2.2 (.join hJ h1.hasType h2.hasType)

theorem LogRel2Base.ValTy2.sort {R : LogRel2 Γ n} : R.ValTy2 M N (.sort r) :=
  R.toType (A := default) (r := default) R.sort

theorem LogRel2Base.DefEq.toType {R : LogRel2 Γ n} :
    R.DefEq M N (.sort u) m a → R.TyDefEq M N u m
  | ⟨h1, h2, h3, h4, h5, h6⟩ =>
    have h1' := Shape.HasType.mono_r h5.le_sort .sort h1
    have h6' := R.mono_r_1 h5.le_sort h1 h1' .sort h6
    ⟨(Shape.HasType.mono_r h5.le_sort .sort h1).toType, h2, h3, h4, R.toType h6'⟩

-- /-- Head reduction preserves `DefEq`. Uses `R.whr` for the `Val2` component;
-- the `IsDefEq` and `LE_Interp` components are sorry'd (semantic soundness of reduction). -/
-- theorem LogRel2Base.DefEq.whr {R : LogRel2 Γ n}
--     (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
--     R.DefEq M N A m a ↔ R.DefEq M' N' A m a := by
--   constructor
--   · rintro ⟨h1, h2, h3, h4, h5, h6⟩
--     exact ⟨h1, sorry, sorry, sorry, h5, (R.whr hM hN).1 h6⟩
--   · rintro ⟨h1, h2, h3, h4, h5, h6⟩
--     exact ⟨h1, sorry, sorry, sorry, h5, (R.whr hM hN).2 h6⟩

/-! #### Concrete definitions at level 0 -/

-- At level 0 (no PiCode/FunEl shapes), all Val2/ValTy2 are trivially True,
-- matching Agda where Val2 at base-level shapes is always Top.
def LR20 : LogRel2 Γ 0 where
  Val2 _ _ _ _ _ := True
  ValTy2 _ _ _ := True
  sort := trivial
  bot _ := trivial
  -- isType := id
  toType := id
  left := id
  left_ty := id
  symm := id
  symm_ty := id
  trans _ := id
  trans_ty _ := id
  conv _ := id
  mono_r_2 _ _ _ := id
  mono_r_2_ty _ _ _ := id
  mono_r_1 _ _ _ _ := id
  mono_l _ _ _ := id
  join_ty _ _ _ _ := id
  whr _ _ := .rfl
  whr_ty _ _ := .rfl

/-! #### Concrete definitions at level n+1 -/

/-- Pi edge validity (merged `PiEdgeVal2` / `PiEdgeEq2`).
For each argument `a ≡ b : A₁`, the substituted codomains are valid types.
For each argument `a : A₁`, the codomains `A₂[a]` and `B₂[a]` are equal types. -/
def LR2S.PiEdge2 (IH : LogRel2 Γ n)
    (B F₁ F₂ : SExpr) (b : Shape n) (f : ShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → Γ ⊢ a ≡ b' : B → IH.Val2 a b' B p b →
    IH.ValTy2 (F₁.inst a) (F₁.inst b') (ShapeFun.app f p) ∧
    IH.ValTy2 (F₂.inst a) (F₂.inst b') (ShapeFun.app f p)) ∧
  ∀ {{a p}}, p.HasType b → Γ ⊢ a : B → IH.Val2 a a B p b →
    IH.ValTy2 (F₁.inst a) (F₂.inst a) (ShapeFun.app f p)

theorem LR2S.PiEdge2.left {IH : LogRel2 Γ n} :
    LR2S.PiEdge2 IH B F₁ F₂ b f → LR2S.PiEdge2 IH B F₁ F₁ b f
  | ⟨h1, _⟩ => ⟨fun _ _ _ hp ha a1 => ⟨(h1 hp ha a1).1, (h1 hp ha a1).1⟩,
                 fun _ _ hp ha a1 => (h1 hp ha a1).1⟩

/-- Pi-type validity (merged `ValTyPi2` / `EqValTyPi2`).
`M` and `N` reduce to Pi types; domain and codomain are recursively valid.
Uses raw `ValTy2` for inner type judgments, with syntactic `IsDefEqStrong` separate. -/
def LR2S.ValTyPi2 (IH : LogRel2 Γ n) (M₁ M₂ : SExpr) (b : Shape n) (f : ShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂ u v,
    Γ ⊢ M₁ ⤳* .forallE B₁ F₁ ∧ Γ ⊢ M₂ ⤳* .forallE B₂ F₂ ∧
    Γ ⊢ B₁ ≡ B₂ : .sort u ∧ B₁::Γ ⊢ F₁ ≡ F₂ : .sort v ∧ IH.ValTy2 B₁ B₂ b ∧
    LR2S.PiEdge2 IH B₁ F₁ F₂ b f

/-- Term application behavior (merged `ValPi2` / `EqValPi2`).
For `m = .lam g`: M and N applied to equal arguments give equal results.
Uses raw `Val2` for input, with `p.HasType a₁` as a separate assumption. -/
def LR2S.ValPi2 (IH : LogRel2 Γ n)
    (M N A₁ A₂ : SExpr) (m : ShapeFun n) (a₁ : Shape n) (a₂ : ShapeFun n) : Prop :=
  (∀ {{a b p}}, p.HasType a₁ → Γ ⊢ a ≡ b : A₁ → IH.Val2 a b A₁ p a₁ →
    IH.Val2 (M.app a) (M.app b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) ∧
    IH.Val2 (N.app a) (N.app b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p)) ∧
  (∀ {{a p}}, p.HasType a₁ → Γ ⊢ a : A₁ → IH.Val2 a a A₁ p a₁ →
    IH.Val2 (M.app a) (N.app a) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p))

/-- Monotonicity of `ValPi2` in the type-shape: increase (Agda: `upPiAppVal2` / `upPiAppEq2`).
Given `PiEdge2` at the TARGET, lifts `ValPi2` from `(a₁, a₂)` to `(a₁', a₂')`. -/
theorem LR2S.ValPi2.mono_r_1 {IH : LogRel2 Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂.LE a₂') (hm : Shape.HasTypeLam m a₁ a₂)
    (hm' : Shape.HasTypeLam m a₁' a₂') (piEV : LR2S.PiEdge2 IH A₁ A₂ A₂ a₁' a₂') :
    LR2S.ValPi2 IH M N A₁ A₂ m a₁ a₂ → LR2S.ValPi2 IH M N A₁ A₂ m a₁' a₂' := by
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

/-- Type validity at element-shape `m` (merged `ValTy2` / `EqValTy2`).
**Trivial at sort shapes** (key Agda principle). Non-trivial only at `.forallE`. -/
def LR2S.ValTy2 (IH : LogRel2 Γ n) (M N : SExpr) : Shape (n+1) → Prop
  | .bot | .sort _ | .lam _ => True
  | .forallE b f => LR2S.ValTyPi2 IH M N b f

theorem LR2S.ValTy2.left {IH : LogRel2 Γ n} :
    LR2S.ValTy2 IH M N m → LR2S.ValTy2 IH M M m := by
  dsimp [LR2S.ValTy2]; split <;> try trivial
  intro ⟨B₁, F₁, _, _, u, v, rM, _, hB, hF, hValB, hE⟩
  exact ⟨B₁, F₁, B₁, F₁, u, v, rM, rM, hB.hasType.1, hF.hasType.1, IH.left_ty hValB, hE.left⟩

theorem LR2S.ValTy2.symm {IH : LogRel2 Γ n} :
    LR2S.ValTy2 IH M N m → LR2S.ValTy2 IH N M m := by
  dsimp [LR2S.ValTy2]; split <;> try trivial
  intro ⟨_, _, _, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩
  have hValB' := IH.symm_ty hValB
  refine ⟨_, _, _, _, _, _, rN, rM, hB.symm, hB.defeqDF_l hF.symm,
    hValB', fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact (hE1 hp sorry (IH.conv hValB' a1)).symm
  · exact IH.symm_ty (hE2 hp sorry (IH.conv hValB' a1))

theorem LR2S.ValTy2.trans {IH : LogRel2 Γ n} :
    LR2S.ValTy2 IH M₁ M₂ m → LR2S.ValTy2 IH M₂ M₃ m → LR2S.ValTy2 IH M₁ M₃ m := by
  dsimp [LR2S.ValTy2]; split <;> try trivial
  intro ⟨B₁, F₁, B₂, F₂, u, v, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩
        ⟨_, _, B₃, F₃, u', v', rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩
  cases rM₂.determ .forallE rM₂' .forallE
  have hF₂₃' := hB₁₂.symm.defeqDF_l hF₂₃
  cases hB₁₂.uniq_sort hB₂₃
  cases hF₁₂.uniq_sort hF₂₃'
  refine ⟨_, _, _, _, _, _, rM₁, rM₃, hB₁₂.trans hB₂₃, hF₁₂.trans hF₂₃',
    IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hE1.1 hp ha a1).1, (hE2.1 hp sorry (IH.conv hValB₁₂ a1)).2⟩
  · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp sorry (IH.conv hValB₁₂ a1))

theorem LR2S.ValPi2.left {IH : LogRel2 Γ n} :
    LR2S.ValPi2 IH M N B F m m₁ m₂ → LR2S.ValPi2 IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LR2S.ValPi2.symm {IH : LogRel2 Γ n} :
    LR2S.ValPi2 IH M N B F m m₁ m₂ → LR2S.ValPi2 IH N M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩
  · exact IH.symm (hP.2 hp ha a1)

theorem LR2S.ValPi2.trans {IH : LogRel2 Γ n} :
    LR2S.ValPi2 IH M₁ M₂ B F m m₁ m₂ →
    LR2S.ValPi2 IH M₂ M₃ B F m m₁ m₂ → LR2S.ValPi2 IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · exact IH.trans (hP2 hp ha a1) (hP2' hp ha a1)

theorem LR2S.PiEdge2.mono_r_2 {IH : LogRel2 Γ n}
    (le₁ : b.LE b') (le₂ : ShapeFun.LE f f')
    (htpi : Shape.HasTypePi f b r) (htpi' : Shape.HasTypePi f' b' r')
    (hValA₁ : IH.ValTy2 A₁ A₁ b') :
    LR2S.PiEdge2 IH A₁ A₂ B₂ b' f' → LR2S.PiEdge2 IH A₁ A₂ B₂ b f
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

theorem LR2S.ValPi2.mono_r_2 {IH : LogRel2 Γ n}
    (le₁ : a₁.LE a₁') (le₂ : a₂.LE a₂') (hm : Shape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.ValTy2 A₁ A₁ a₁') (htpi' : Shape.HasTypePi a₂' a₁' r') :
    LR2S.ValPi2 IH M N A₁ A₂ m a₁' a₂' → LR2S.ValPi2 IH M N A₁ A₂ m a₁ a₂ := by
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

/-- Monotonicity of `ValPi2` in the element-shape: decrease (Agda: `restrictPiAppVal2-sel` etc.).
In Lean this is simpler than Agda because we quantify over all `p` with `DefEq`, not selections. -/
theorem LR2S.ValPi2.mono_l {IH : LogRel2 Γ n}
    (le : m.LE m') (hm : Shape.HasTypeLam m a₁ a₂)
    (hm' : Shape.HasTypeLam m' a₁ a₂) :
    LR2S.ValPi2 IH M N A₁ A₂ m' a₁ a₂ → LR2S.ValPi2 IH M N A₁ A₂ m a₁ a₂ := by
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

/-- Join of `PiEdge2`: given edge validity at `(b₁, f₁)` and `(b₂, f₂)`,
produce edge validity at `(b₁.join b₂, f₁.join f₂)`.
Follows the same representative-based strategy as old `LRS.join`. -/
theorem LR2S.PiEdge2.join {IH : LogRel2 Γ n}
    (htB₁ : b₁.HasType .type) (htB₂ : b₂.HasType .type) (hC_b : b₁.Compat b₂)
    (ht₁ : Shape.HasTypePi f₁ b₁ r₁) (ht₂ : Shape.HasTypePi f₂ b₂ r₂)
    (hC_f : ShapeFun.Compat Shape.Compat f₁ f₂)
    (hE₁ : LR2S.PiEdge2 IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LR2S.PiEdge2 IH B₁ F₁ F₂ b₂ f₂) :
    LR2S.PiEdge2 IH B₁ F₁ F₂ (b₁.join b₂) (ShapeFun.join Shape.join f₁ f₂) := by
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

/-- Head reduction on M, N preserves `ValPi2`. Uses `IH.whr` (with `WHRed.app`)
to transport the inner `IH.Val2` terms. HasType is preserved trivially (doesn't mention M, N). -/
theorem LR2S.ValPi2.whr {IH : LogRel2 Γ n}
    (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    LR2S.ValPi2 IH M N A₁ A₂ m a₁ a₂ ↔ LR2S.ValPi2 IH M' N' A₁ A₂ m a₁ a₂ := by
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).1 d1, (IH.whr (.app hN) (.app hN)).1 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).1 (pae hp ha a1)
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).2 d1, (IH.whr (.app hN) (.app hN)).2 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).2 (pae hp ha a1)

/-- Term validity at `(m, a)` (merged `Val2` / `EqVal2`).
At `.sort`: just `ValTy2 M N m` — no `A` dependency (matches Agda: `Val2 G M A u UCode = ValTy2 G M u`).
At `.forallE`: type validity + term behavior, with `A ⤳*` stored here. -/
def LR2S.Val2 (IH : LogRel2 Γ n) (M N A : SExpr) (m a : Shape (n+1)) : Prop :=
  match a with
  | .bot => True
  | .sort _ => LR2S.ValTy2 IH M N m
  | .forallE a₁ a₂ =>
    match m with
    | .bot => True
    | .lam m =>
      ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
      Γ ⊢ A₁ : .sort u ∧ IH.ValTy2 A₁ A₁ a₁ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LR2S.PiEdge2 IH A₁ A₂ A₂ a₁ a₂ ∧ LR2S.ValPi2 IH M N A₁ A₂ m a₁ a₂
    | _ => False
  | _ => False

def LR2S (IH : LogRel2 Γ n) : LogRel2 Γ (n+1) where
  Val2 := LR2S.Val2 IH
  ValTy2 := LR2S.ValTy2 IH
  sort := trivial
  bot ha := by cases ha.unfold <;> trivial
  left_ty := .left
  symm_ty := .symm
  trans_ty := .trans
  -- isType {M N A m a} := by
  --   dsimp [LR2S.ValTy2]; dsimp [LR2S.Val2]; split <;> [exact id; simp; skip; nofun]
  --   cases m with
  --   | bot => intro; sorry
  --   | lam g =>
  --     intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, _⟩
  --     exact ⟨_, _, _, _, _, _, rA, rA, hA1, hA₂, hA2, hE⟩
  --   | _ => simp
  toType := id
  left {M N A m a} := by
    dsimp [LR2S.Val2]; split <;> try trivial
    · exact .left
    · cases m with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.left⟩
  symm {M N A m a} := by
    dsimp [LR2S.Val2]; split <;> try trivial
    · exact .symm
    · cases m with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.symm⟩
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LR2S.Val2]; split <;> try trivial
    · exact .trans
    · cases m with | lam => ?_ | _ => simp
      intro ⟨B, F, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ ⟨_, _, _, _, rA', _, _, _, _, hP'⟩
      cases rA.determ .forallE rA' .forallE
      exact ⟨_, _, _, _, rA, hA1, hA2, hA₂, hE, hP.trans hP'⟩
  conv {A A' a M N m} := by
    dsimp [LR2S.ValTy2]; dsimp [LR2S.Val2]; split <;> (try · simp); dsimp
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
    cases a with dsimp [LR2S.Val2]
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
    dsimp [LR2S.ValTy2] at h ⊢; split <;> try trivial
    cases a' <;> simp [Shape.LE.def] at le
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
    cases a with dsimp [LR2S.Val2]
    | sort s =>
      dsimp [LR2S.ValTy2] at h ⊢; split <;> try trivial
      cases m' <;> simp [Shape.LE.def] at le
      have .forallE hm := hm.unfold; have .forallE hm' := hm'.unfold
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
      | sort => split <;> trivial
      | _ => trivial
    | forallE =>
      cases m₂ with simp [Shape.join] | forallE b₂ f₂ => ?_ | _ => trivial
      simp only [Shape.Compat, Bool.and_eq_true] at hC
      have .forallE ht₁ := hm₁.unfold
      have .forallE ht₂ := hm₂.unfold
      dsimp [LR2S.ValTy2]
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
    cases a with dsimp [LR2S.Val2]
    | sort s =>
      dsimp [LR2S.ValTy2]; split <;> try rfl
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, hM.determ_l rM .forallE, hN.determ_l rN .forallE, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hM rM, .trans hN rN, rest⟩
    | forallE a₁ a₂ =>
      cases m with | lam g => ?_ | _ => rfl
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LR2S.ValPi2.whr hM hN).1 hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LR2S.ValPi2.whr hM hN).2 hP⟩
    | _ => rfl
  whr_ty {A A' B B' m} hA hB := by
    dsimp [LR2S.ValTy2]; split <;> try rfl
    constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, rest⟩
    · exact ⟨B₁, F₁, B₂, F₂, u, v, hA.determ_l rA .forallE, hB.determ_l rB .forallE, rest⟩
    · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hA rA, .trans hB rB, rest⟩

def LR2 (Γ : List SExpr) : LogRel2 Γ n :=
  match n with
  | 0 => LR20
  | _+1 => LR2S (LR2 Γ)

private theorem LR2S.PiEdge2.lift_aux
    {b} {f : ShapeFun n} (le : n ≤ n') (htpi_a : Shape.HasTypePi f b true)
    (IH1 : ∀ {M N : SExpr} {m : Shape n}, m.HasType .type →
      ((LR2 Γ).ValTy2 (n := n') M N m.lift ↔ (LR2 Γ).ValTy2 M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      ((LR2 Γ).Val2 (n := n') M N A m.lift a.lift ↔ (LR2 Γ).Val2 M N A m a)) :
    LR2S.PiEdge2 (LR2 Γ) (n := n') B F₁ F₂ b.lift (ShapeFun.lift Shape.lift f) ↔
    LR2S.PiEdge2 (LR2 Γ) B F₁ F₂ b f := by
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (Shape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have ⟨r1, r2⟩ := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_a.2 _ hp)).1 (ShapeFun.lift_app ▸ r1),
              (IH1 (htpi_a.2 _ hp)).1 (ShapeFun.lift_app ▸ r2)⟩
    · exact (IH1 (htpi_a.2 _ hp)).1 (ShapeFun.lift_app ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift _) _; d3 ▸ ?_
      simp [ShapeFun.lift] at d2; obtain ⟨q, _, d2, rfl, rfl⟩ := d2
      have hq := Shape.HasDom.def.1 htpi_a.1 _ _ d2
      have v' := (IH2 hq).1 ((LR2 Γ).mono_l d1
        ((Shape.HasType.lift le).2 hq) hp v))
    · have ⟨r1, r2⟩ := hEdge.1 hq ha v'
      exact ⟨ShapeFun.app_of_mem d2 ▸ (IH1 (htpi_a.2 _ hq)).2 r1,
             ShapeFun.app_of_mem d2 ▸ (IH1 (htpi_a.2 _ hq)).2 r2⟩
    · exact ShapeFun.app_of_mem d2 ▸ (IH1 (htpi_a.2 _ hq)).2 (hEdge.2 hq ha v')

private theorem LR2S.ValPi2.lift_aux
    {g : ShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : Shape.HasTypeLam g a₁ a₂)
    (IH : ∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      ((LR2 Γ).Val2 (n := n') M N A m.lift a.lift ↔ (LR2 Γ).Val2 M N A m a))
    (hEdge : LR2S.PiEdge2 (LR2 Γ) A₁ A₂ A₂ a₁ a₂) :
    LR2S.ValPi2 (LR2 Γ) (n := n') M N A₁ A₂
      (ShapeFun.lift Shape.lift g) a₁.lift (ShapeFun.lift Shape.lift a₂) ↔
    LR2S.ValPi2 (LR2 Γ) M N A₁ A₂ g a₁ a₂ := by
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (Shape.HasType.lift le).2 hp
      have v' := (IH hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IH (htm.2.2 _ hp)).1 ?_, (IH (htm.2.2 _ hp)).1 ?_⟩
        <;> rw [ShapeFun.lift_app, ShapeFun.lift_app] <;> [exact r1; exact r2]
    · apply (IH (htm.2.2 _ hp)).1
      rw [ShapeFun.lift_app, ShapeFun.lift_app]
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
      have v_lo := (IH hqg).1 ((LR2 Γ).mono_l dg1
        ((Shape.HasType.lift le).2 hqg) hp v)
      have le_a2 : a₂.app qg ≤ a₂.app qa := by
        rw [← Shape.lift_le_lift le, ShapeFun.lift_app, ShapeFun.app_of_mem da2, ← da3]
        exact ShapeFun.app_mono_r dg1
      have ht_lo := htm.2.2 _ hqg
      have ht_hi := (htm.1.2 _ hqa).mono_r le_a2 ht_lo
      have v_lo_qa := (IH hqa).1 ((LR2 Γ).mono_l da1
        ((Shape.HasType.lift le).2 hqa) hp v)
      have vt_qa := hEdge.2 hqa ha.hasType.1 ((LR2 Γ).left v_lo_qa)
      rw [dg3, da3]
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo
      exact ⟨(IH ht_hi).2 ((LR2 Γ).mono_r_1 le_a2 ht_lo ht_hi vt_qa r1),
              (IH ht_hi).2 ((LR2 Γ).mono_r_1 le_a2 ht_lo ht_hi vt_qa r2)⟩
    · exact (IH ht_hi).2 ((LR2 Γ).mono_r_1 le_a2 ht_lo ht_hi vt_qa (hP.2 hqg ha v_lo))

private theorem LR2.lift_succ_aux :
    (∀ {M N : SExpr} {m : Shape n}, m.HasType .type →
      (LR2S.ValTy2 (n := n) (LR2 Γ) M N m.lift ↔ (LR2 Γ).ValTy2 M N m)) ∧
    (∀ {M N A : SExpr} {m a : Shape n}, m.HasType a →
      (LR2S.Val2 (n := n) (LR2 Γ) M N A m.lift a.lift ↔ (LR2 Γ).Val2 M N A m a)) := by
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
        exact ⟨(ih.1 (htpi.2 _ hp)).1 (ShapeFun.lift_app ▸ r1),
               (ih.1 (htpi.2 _ hp)).1 (ShapeFun.lift_app ▸ r2)⟩
      · exact (ih.1 (htpi.2 _ hp)).1 (ShapeFun.lift_app ▸ hE.2 hp' ha v')
    · refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, (ih.1 htpi.1.isType).2 hValB,
        fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩
      all_goals
        refine have ⟨_, _, d1, d2, d3⟩ := ShapeFun.app_eq (ShapeFun.lift Shape.lift f) _; d3 ▸ ?_
        simp [ShapeFun.lift] at d2; obtain ⟨q, _, d2, rfl, rfl⟩ := d2
        have hq := Shape.HasDom.def.1 htpi.1 _ _ d2
        have v' := (ih.2 hq).1 ((LR2S (LR2 Γ)).mono_l d1
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
    · have hEdge' := (LR2S.PiEdge2.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).1 hEdge
      refine ⟨A₁, A₂, u, v, rA, hA1, (ih.1 htpi_a.1.isType).1 hValA, hA₂, hEdge', ?_⟩
      exact (LR2S.ValPi2.lift_aux (Nat.le_succ k) htm ih.2 hEdge').1 hP
    · have hEdge' := (LR2S.PiEdge2.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).2 hEdge
      refine ⟨A₁, A₂, u, v, rA, hA1, (ih.1 htpi_a.1.isType).2 hValA, hA₂, hEdge', ?_⟩
      exact (LR2S.ValPi2.lift_aux (Nat.le_succ k) htm ih.2 hEdge).2 hP

theorem LR2.Val2.lift {m a : Shape n} (le : n ≤ n') (hma : m.HasType a) :
    (LR2 Γ).Val2 (n := n') M N A m.lift a.lift ↔ (LR2 Γ).Val2 M N A m a := by
  induction le with | refl => simp [Shape.lift_self] | step le ih
  rw [(Shape.lift_lift (.inl le)).symm, (Shape.lift_lift (s := a) (.inl le)).symm]
  exact (LR2.lift_succ_aux.2 ((Shape.HasType.lift le).2 hma)).trans ih

theorem LR2.ValTy2.lift {m : Shape n} (le : n ≤ n') (hmt : m.HasType .type) :
    (LR2 Γ).ValTy2 (n := n') M N m.lift ↔ (LR2 Γ).ValTy2 M N m := by
  induction le with | refl => simp [Shape.lift_self] | step le ih
  rw [(Shape.lift_lift (.inl le)).symm]
  exact (LR2.lift_succ_aux.1 (Shape.lift_type ▸ (Shape.HasType.lift le).2 hmt)).trans ih

theorem LR2S.PiEdge2.lift
    {b} {f : ShapeFun n} (le : n ≤ n') (htpi_a : Shape.HasTypePi f b true) :
    LR2S.PiEdge2 (LR2 Γ) (n := n') B F₁ F₂ b.lift (ShapeFun.lift Shape.lift f) ↔
    LR2S.PiEdge2 (LR2 Γ) B F₁ F₂ b f := lift_aux le htpi_a (LR2.ValTy2.lift le) (LR2.Val2.lift le)

theorem LR2S.ValPi2.lift {g : ShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : Shape.HasTypeLam g a₁ a₂)
    (hEdge : LR2S.PiEdge2 (LR2 Γ) A₁ A₂ A₂ a₁ a₂) :
    LR2S.ValPi2 (LR2 Γ) (n := n') M N A₁ A₂
      (ShapeFun.lift Shape.lift g) a₁.lift (ShapeFun.lift Shape.lift a₂) ↔
    LR2S.ValPi2 (LR2 Γ) M N A₁ A₂ g a₁ a₂ := lift_aux le htm (LR2.Val2.lift le) hEdge

theorem LR2.DefEq.lift {m a : Shape n} (le : n ≤ n') :
    (LR2 Γ).DefEq (n := n') M N A m.lift a.lift ↔ (LR2 Γ).DefEq M N A m a := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6⟩
  · exact ⟨(Shape.HasType.lift le).1 h1, h2, (LE_Interp.lift le).1 h3,
      (LE_Interp.lift le).1 h4, (LE_Interp.lift le).1 h5,
      (LR2.Val2.lift le ((Shape.HasType.lift le).1 h1)).1 h6⟩
  · exact ⟨(Shape.HasType.lift le).2 h1, h2, (LE_Interp.lift le).2 h3,
      (LE_Interp.lift le).2 h4, (LE_Interp.lift le).2 h5, (LR2.Val2.lift le h1).2 h6⟩

theorem LR2.TyDefEq.lift {m : Shape n} (le : n ≤ n') :
    (LR2 Γ).TyDefEq (n := n') M N u m.lift ↔ (LR2 Γ).TyDefEq M N u m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5⟩
  · have hmt : m.HasType .type :=
      (Shape.HasType.lift le).1 (Shape.lift_type.symm ▸ h1)
    exact ⟨hmt, h2, (LE_Interp.lift le).1 h3, (LE_Interp.lift le).1 h4,
      (LR2.ValTy2.lift le hmt).1 h5⟩
  · exact ⟨Shape.lift_type ▸ (Shape.HasType.lift le).2 h1, h2,
      (LE_Interp.lift le).2 h3, (LE_Interp.lift le).2 h4,
      (LR2.ValTy2.lift le h1).2 h5⟩

def LR2.Subst1 (Γ₀ : List SExpr) (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∀ {{n}} (a : Shape n), LE_Interp ρ a A₀ →
    (a.HasType .type → ∃ u', (LR2 Γ₀).TyDefEq A A' u' a) ∧
    (∀ {{m}}, LE_Interp ρ m (.bvar i) → m.HasType a → (LR2 Γ₀).Val2 x x' A m a)

/-- Two-substitution validity: σ and σ' agree up to IsDefEq+Val2 at each variable.
Matches Agda's ValidConvSub2. Uses `IsDefEq ∧ Val2` instead of full `DefEq`
to avoid requiring `LE_Interp .nil` fields that are not available in bvar0_defEq. -/
def LR2.SubstWF (Γ₀ : List SExpr) (σ σ' : Subst) (Γ : List SExpr) (ρ : Valuation) : Prop :=
  ∀ {{i A}}, Lookup Γ i A → LR2.Subst1 Γ₀ (σ i) (σ' i) A (A.subst σ) (A.subst σ') ρ i
  -- ∀ {{i A}}, Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ ∧
  --   ∀ {{n}} (a : Shape n), LE_Interp ρ a A →
  --     (a.HasType .type → ∃ u, (LR2 Γ₀).TyDefEq (A.subst σ) (A.subst σ') u a) ∧
  --     (∀ {{m}}, LE_Interp ρ m (.bvar i) → m.HasType a → (LR2 Γ₀).Val2 (σ i) (σ' i) (A.subst σ) m a)

/-- Well-typed conversion substitution: σ(i) ≡ σ'(i) at each variable. -/
def Ctx.SubstEq (Γ₀ : List SExpr) (σ σ' : SExpr.Subst) (Γ : List SExpr) : Prop :=
  ∀ {{i A}}, Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ

theorem IsDefEq.subst (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Γ ⊢ e1 ≡ e2 : A → Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ := sorry

theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ) (hA : Γ₀ ⊢ A.subst σ : .sort u) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := sorry

theorem LR2.SubstWF.toSubstEq (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) : Ctx.SubstEq Γ₀ σ σ' Γ :=
  fun _ _ h => (W h).1

theorem LR2.SubstWF.fits (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) : ρ.Fits Γ₀ Γ := sorry

/-- Substitution lemma for LE_Interp: if `m` approximates `M` under valuation `ρ`,
and `σ`/`σ'` are substitutions compatible with `ρ` (via SubstWF),
then `m` approximates `M.subst σ` (resp. `M.subst σ'`) under the nil valuation. -/
theorem LE_Interp.subst_nil (h : LE_Interp ρ m M) (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) :
    LE_Interp .nil m (M.subst σ) ∧ LE_Interp .nil m (M.subst σ') := sorry

theorem LR2.SubstWF.left (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) : LR2.SubstWF Γ₀ σ σ Γ ρ := by
  refine fun _ _ h => ⟨(W h).1.hasType.1, fun _ a hA => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
  · exact (((W h).2 a hA).1 ht).imp fun _ => (·.left)
  · exact (LR2 Γ₀).left <| ((W h).2 a hA).2 hM hmem

theorem LR2.SubstWF.symm (W : LR2.SubstWF Γ₀ σ σ' Γ ρ) : LR2.SubstWF Γ₀ σ' σ Γ ρ := by
  refine fun i A h => ⟨?_, fun _ a hA => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
  · have ⟨_, hte⟩ := ((W h).2 (n := 0) _ .bot).1 (.bot .sort)
    exact hte.isDefEq.defeqDF (W h).1.symm
  · exact let ⟨u, hte⟩ := ((W h).2 a hA).1 ht; ⟨u, hte.symm⟩
  · let ⟨_, hte⟩ := ((W h).2 a hA).1 hmem.isType
    exact (LR2 Γ₀).conv hte.valTy2 ((LR2 Γ₀).symm (((W h).2 a hA).2 hM hmem))

theorem LR2.SubstWF.trans (W₁ : LR2.SubstWF Γ₀ σ σ' Γ ρ) (W₂ : LR2.SubstWF Γ₀ σ' σ'' Γ ρ) :
    LR2.SubstWF Γ₀ σ σ'' Γ ρ := by
  refine fun i A h => ⟨?_, fun _ a hA => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
  · have ⟨_, h'⟩ := ((W₁ h).2 (n := 0) _ .bot).1 (.bot .sort)
    exact (W₁ h).1.trans (h'.isDefEq.symm.defeqDF (W₂ h).1)
  · let ⟨u, hte₁⟩ := ((W₁ h).2 a hA).1 ht
    let ⟨_, hte₂⟩ := ((W₂ h).2 a hA).1 ht
    cases hte₁.isDefEq.uniq_sort hte₂.isDefEq
    exact ⟨u, hte₁.trans hte₂⟩
  · let ⟨_, hte⟩ := ((W₁ h).2 a hA).1 hmem.isType
    exact (LR2 Γ₀).trans (((W₁ h).2 a hA).2 hM hmem) <|
      (LR2 Γ₀).conv ((LR2 Γ₀).symm_ty hte.valTy2) (((W₂ h).2 a hA).2 hM hmem)

/-- Extend substitution validity to a new binding.
Matches Agda's ValidSub2-extend / ValidConvSub2-extend.
Zero case: use the hypothesis `h0` for the new variable.
Succ case: delegate to the original `W`, using `lift_subst_cons` and `weak_iff`. -/
theorem LR2.SubstWF.cons (W : LR2.SubstWF Γ₀ σ σ' Γ ρ)
    (h0 : LR2.Subst1 Γ₀ t t' A.lift (A.subst σ) (A.subst σ') (ρ.push x)) :
    LR2.SubstWF Γ₀ (σ.cons t) (σ'.cons t') (A :: Γ) (ρ.push x) := by
  intro i B hlookup
  cases hlookup with
  | zero => simp only [lift_subst_cons, Subst.cons]; exact ⟨h0.1, h0.2⟩
  | succ hlookup =>
    simp only [lift_subst_cons, Subst.cons]
    exact ⟨(W hlookup).1, fun _ a hA =>
      let W' := (W hlookup).2 a (LE_Interp.weak_iff.mp hA)
      ⟨W'.1, fun _ hM hmem => W'.2 (LE_Interp.weak_iff.mp hM) hmem⟩⟩
