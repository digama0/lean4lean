import Lean4Lean.Experimental.SExpr
import Batteries.WF

namespace Lean4Lean

namespace SExpr
variable [Params]

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
  | sort : Shape0

inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort : ShapeS Shape
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape

def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort : ∀ {n}, Shape n
  | 0 => Shape0.sort
  | _+1 => ShapeS.sort

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, _, _ | _+1, .bot, _ | _+1, _, .bot | _+1, .sort, .sort => true
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _, _, _ => false

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .sort, .sort | _+1, .sort, .sort => True --j ≤ i
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
    | .sort, .sort => True --j ≤ i
    | .forallE s f, .forallE s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
    | _, _ => False := by
  dsimp only [(· ≤ ·), Shape.LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp

omit [Params] in
theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> rfl
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]

omit [Params] in
theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

omit [Params] in
theorem Shape.le_sort {s : Shape n} : s ≤ .sort ↔ s = .bot ∨ s = .sort := by
  cases n <;> simp [sort, bot, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble]

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n m}, Shape n → Shape m
  | 0, _, .sort | _+1, _, .sort => .sort
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift s) <| ShapeFun.lift lift f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift lift f

omit [Params] in
@[simp] theorem Shape.lift_bot : ((Shape.bot : Shape n).lift : Shape m) = Shape.bot := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in
@[simp] theorem Shape.lift_sort : ((Shape.sort : Shape n).lift : Shape m) = Shape.sort := by
  cases n <;> [rfl; cases m <;> rfl]

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
  | zero => cases s <;> cases t <;> simp [ble]
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble] <;>
      [exact fun h1 h2 h3 h4 => ⟨ih h1 h3, ihf h2 h4⟩; exact ihf]

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
  | 0, .sort, .sort | _+1, .sort, .sort => .sort
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

@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

omit [Params] in
@[simp] theorem Shape.lift_app :
    ((app f a : Shape n).lift : Shape m) = app f.lift a.lift  := by
  sorry

def ShapeFun.single (x y : Shape n) : ShapeFun n :=
  (x, y) :: if x ≤ .bot then [] else [(.bot, .bot)]

theorem ShapeFun.single_app : (ShapeFun.single x y).app x' = if x ≤ x' then y else .bot := by
  sorry

omit [Params] in
theorem Shape.app_mono_l {f f' : Shape (n + 1)} (le : f ≤ f') (a) : f.app a ≤ f'.app a := by
  unfold app; split <;> [split; simp]
  · exact ShapeFun.app_mono_l le _
  · cases f' <;> simp [LE.def] at le; grind

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b | _+1, .forallE a b, .sort =>
    b.all fun (x, y) => x.hasType a && y.hasType .sort
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort
  | 0, .sort, .sort | _+1, .sort, .sort => true
  | _+1, .lam f, .forallE a b =>
    b.all (fun (x, y) => x.hasType a && y.hasType .sort) &&
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

def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) :=
  Shape.HasDom b a ∧ ∀ x, HasType x a → HasType (b.app x) .sort

omit [Params] in
theorem Shape.HasTypePi.def {b : ShapeFun n} :
    HasTypePi b a ↔ Shape.HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType .sort := by
  refine and_congr_right fun H1 => ⟨fun H x y h => ?_, fun H x h => ?_⟩
  · exact b.app_of_mem h ▸ H _ (Shape.HasDom.def.1 H1 _ _ h)
  · have ⟨_, _, h1, h2, h3⟩ := b.app_eq x
    exact h3 ▸ H _ _ h2

def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  Shape.HasTypePi b a ∧ Shape.HasDom f a ∧
  ∀ x, HasType x a → HasType (f.app x) (b.app x)

omit [Params] in
theorem Shape.HasType.mono_r {m a a' : Shape n} (ha : a ≤ a') :
    HasType a' .sort → HasType m a → HasType m a' := sorry

omit [Params] in
theorem Shape.HasTypeLam.def {b : ShapeFun n} : HasTypeLam f a b ↔
    Shape.HasTypePi b a ∧ Shape.HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x) := by
  refine and_congr_right fun H1 => and_congr_right fun H2 => ⟨fun H x y h => ?_, fun H x h => ?_⟩
  · exact f.app_of_mem h ▸ H _ (Shape.HasDom.def.1 H2 _ _ h)
  · have ⟨_, _, h1, h2, h3⟩ := f.app_eq x
    exact .mono_r (ShapeFun.app_mono_r h1) (H1.2 _ h) (h3 ▸ H _ _ h2)

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x .sort → HasTypeU .bot x
  | sort : HasTypeU .sort .sort
  | forallE : HasTypePi (n := n) b a → HasTypeU (n := n+1) (.forallE a b) .sort
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.forallE a b)

omit [Params] in
theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := by
  unfold HasType hasType; split <;> simp <;> intros <;> constructor <;> try grind [HasType]
  · simp [HasType, hasType]; grind
  · rename_i a b H
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
theorem Shape.HasType.bot : HasType (n := n) x .sort → HasType .bot x := (unfold_iff.2 <| .bot ·)
omit [Params] in
theorem Shape.HasType.sort : HasType (n := n) .sort .sort := unfold_iff.2 .sort
omit [Params] in
theorem Shape.HasType.forallE : HasTypePi (n := n) b a →
    HasType (n := n+1) (.forallE a b) .sort := (unfold_iff.2 <| .forallE ·)
omit [Params] in
theorem Shape.HasType.lam : HasTypeLam (n := n) f a b →
    HasType (n := n+1) (.lam f) (.forallE a b) := (unfold_iff.2 <| .lam ·)

omit [Params] in
theorem Shape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases H.unfold <;> rfl

omit [Params] in
theorem Shape.HasType.isType {m a : Shape n} (h : HasType m a) : HasType a .sort := by
  cases h.unfold with
  | bot h1 => exact h1
  | sort | forallE => exact .sort
  | lam h1 => exact .forallE h1.1

theorem Shape.HasDom.isType (H : Shape.HasDom f a) : a.HasType .sort :=
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
    (H : ∀ x y, (x, y) ∈ (b : ShapeFun n) → HasType x a ∧ HasType y .sort)
    (ht : HasType x a) : HasType (ShapeFun.app f x) .sort := sorry

theorem Shape.HasType.maximal
    (H : ∀ x y, (x, y) ∈ (f : ShapeFun n) → HasType x a ∧ HasType y (ShapeFun.app b x))
    (ha : a ≤ a') (ht : HasType x' a') :
    ∃ x, HasType x a ∧ x ≤ x' ∧ ShapeFun.app f x = ShapeFun.app f x' := sorry

omit [Params] in
theorem Shape.HasDom.single : HasDom (ShapeFun.single x y) a ↔ x.HasType a := by
  simp [Shape.HasDom.def, ShapeFun.single, or_imp, forall_and]
  intro h _ _ _ rfl _; exact .bot h.isType

omit [Params] in
theorem Shape.HasDom.mono (le : a ≤ a') (h : a'.HasType .sort) (H : HasDom f a) : HasDom f a' :=
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
  | sort : m ≤ .sort → LE_Interp ρ m (.sort i)
  | app : LE_Interp ρ f F → LE_Interp ρ a A → m ≤ f.app a → LE_Interp ρ m (.app F A pat)
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

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M := sorry

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ := sorry

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort := by
  generalize eq : SExpr.sort u = M at H
  induction H with cases eq
  | bot => exact Shape.bot_le
  | sort h => exact h

inductive Valuation.Fits : (Γ Δ : List SExpr) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {n a}, LE_Interp (n := n) ρ a A →
      ∃ n' a', n ≤ n' ∧ a.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .sort) →
    LE_Interp (n := n) ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

def InterpTyped (ρ : Valuation) (m : Shape n) (M A : SExpr) :=
  ∃ n' m' a, n ≤ n' ∧ m.lift (m := n') ≤ m' ∧
    LE_Interp ρ m' M ∧ LE_Interp ρ a A ∧ m'.HasType a

theorem InterpTyped.mk (h1 : (m : Shape n) ≤ m') (h2 : LE_Interp ρ m' M)
    (h3 : LE_Interp ρ a A) (h4 : m'.HasType a) : InterpTyped ρ m M A :=
  ⟨_, _, _, Nat.le_refl _, Shape.lift_self.symm ▸ h1, h2, h3, h4⟩

theorem InterpTyped.bot : InterpTyped (n := n) ρ .bot M A :=
  .mk .rfl .bot .bot (.bot <| .bot .sort)

theorem LE_Interp.sound_bot :
    (LE_Interp (n := n) ρ .bot M ↔ LE_Interp (n := n) ρ .bot N) ∧
    (LE_Interp (n := n) ρ .bot M → InterpTyped (n := n) ρ .bot M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem LE_Interp.sound_app
    (H1 : ∀ {n} {m : Shape n}, LE_Interp ρ m f → InterpTyped ρ m f (.forallE A B))
    (H2 : ∀ {n} {m : Shape n}, LE_Interp ρ m (B.inst a) →
      ∃ n' a', n ≤ n' ∧ m.lift (m := n') ≤ a' ∧ LE_Interp ρ a' (B.inst a) ∧ a'.HasType .sort)
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
      ∃ n' a', n ≤ n' ∧ m.lift (m := n') ≤ a' ∧ LE_Interp ρ a' (B.inst a) ∧ a'.HasType .sort)
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
  have hsort {ρ A U}
      (H : ∀ {n a}, LE_Interp (n := n) ρ a A → InterpTyped (n := n) ρ a A (.sort U))
      {n a} (h : LE_Interp (n := n) ρ a A) :
      ∃ n' a', n ≤ n' ∧ a.lift (m := n') ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .sort := by
    have ⟨n', a', u', le, h1, h2, h3, h4⟩ := H h; refine ⟨_, _, le, h1, h2, ?_⟩
    cases h3 with | bot => cases h4.bot_r; exact .bot .sort | sort h3
    obtain rfl | rfl := Shape.le_sort.1 h3; · cases h4.bot_r; exact .bot .sort
    exact h4
  replace H := H.strong
  induction H generalizing n m ρ with
  | @bvar _ i A h =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.bvar i = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot <| .bot .sort)
    | bvar a1 a2 a3
    induction W generalizing i A with
    | nil => cases (Shape.lift_le_bot a2).1 a3; exact .mk .rfl .bot .bot (.bot <| .bot .sort)
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
    | bot => exact .mk .rfl .bot .bot (.bot <| .bot .sort)
    | sort h1 => exact .mk h1 (.sort .rfl) (.sort .rfl) .sort
  | @const c _ _ ls =>
    refine ⟨.rfl, fun h => ?_⟩
    generalize eq : SExpr.const c ls = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot <| .bot .sort)
  | appDF _ _ _ _ _ ihA ihB ih1 ih2 ih3 =>
    by_cases hm : m = .bot; · exact hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      cases h with | bot => cases hm rfl | app h1 h2 h3
    · exact .app ((ih1 W).1.1 h1) ((ih2 W).1.1 h2) h3
    · exact .app ((ih1 W).1.2 h1) ((ih2 W).1.2 h2) h3
    · exact sound_app (ih1 W).2 (hsort (ih3 W).2) (.app h1 h2 h3)
  | @lamDF _ _ _ _ body body' B _ _ ih1 ih2 =>
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
        · refine .mono_r (ShapeFun.app_of_mem c2 ▸ ShapeFun.app_mono_r b1) ?_ c6
          have ⟨_, _, _, c2, _, _, c5, c6⟩ := a3 _ _ b3'
          cases (ShapeFun.uniq_l b2' c2 .rfl .rfl).2
          exact c6.isType
  | @forallEDF _ A _ _ body body' _ _ _ ih1 ih2 =>
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
          LE_Interp (ρ.push x) (f'.app x) body ∧ (f'.app x).HasType .sort by
        have ⟨n', le', f₁, b1, b2, b3⟩ := this; simp [forall_and] at b3
        have hJ := Shape.Join.mk (h1.compat h2)
        have ⟨m', b₂, le, c1, c2, c3⟩ := hsort (ih1 W).2 (h1.join hJ h2)
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
            (Shape.lift_sort ▸ (Shape.HasType.lift le₁).2 c3)
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
          exact ShapeFun.app_of_mem e2 ▸ b3.2 _ (Shape.HasDom.def.1 b2 _ _ e2)
      replace h4 (p) (h : p ∈ f) : p.1.HasType b ∧ LE_Interp (ρ.push p.1) p.2 body :=
        have := Shape.HasDom.def.1 h3 _ _ h; ⟨this, (ShapeFun.app_of_mem h) ▸ h4 _ this⟩
      have ⟨n', le, H⟩ : ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : ShapeFun k,
          f'.map Prod.fst = f.map (·.1.lift) ∧
          ∀ x fx, (x, fx) ∈ f → ∃ f'x, (x.lift, f'x) ∈ f' ∧
          fx.lift ≤ f'x ∧ LE_Interp (ρ.push x) f'x body ∧ f'x.HasType .sort := by
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
        replace b4 : f'x.HasType .sort := by
          cases b3 with
          | sort h => exact .mono_r h .sort b4
          | bot => cases b4.bot_r; exact .bot .sort
        simp [or_imp, forall_and, *]
        exact ⟨.inl ⟨Shape.lift_lift (.inl le) ▸ Shape.lift_mono b1, (LE_Interp.lift le₂).2 b2,
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
  | defeqDF _ _ ih1 ih2 =>
    refine ⟨(ih2 W).1, fun h => ?_⟩
    have ⟨_, _, _, le, h1, h2, h3, h4⟩ := (ih2 W).2 h
    exact ⟨_, _, _, le, h1, h2, (ih1 W).1.1 h3, h4⟩
  | beta _ _ _ ih1 ih2 ih3 =>
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
      | @lam _ _ _ _ f' _ _ a1 a2 a3 a4
      cases h3 with | bot => cases ht rfl | @forallE _ _ _ _ _ _ _ m₁ b1 b2 b3 b4 b5
      cases t with simp [Shape.LE.def] at b5 | bot => cases ht rfl | forallE a' b'
      cases h4.unfold with | bot => cases hm ((Shape.lift_le_bot le).1 h1) | @lam _ f _ _ d1
      have : ∀ x y, (x, y) ∈ f' → LE_Interp (ρ.push x) y (e.lift.app (SExpr.bvar 0)) := by
        intro x y h
        have hy : y ≠ .bot := sorry
        have := ShapeFun.app_of_mem h ▸ a3 x (Shape.HasDom.def.1 a2 _ _ h)
        cases this with | bot => cases hy rfl | app c1 c2 c3
        have := LE_Interp.weak_iff.1 c1
        have ⟨k, le₁, le₂, c2⟩ := LE_Interp.bvar_iff.1 c2
        sorry
      sorry
    · have ⟨_, m', f, le, a1, a2, a3, a4⟩ := (ih1 W).2 h
      have hf : f ≠ .bot := fun h => by
        subst h; cases a4.bot_r; cases hm ((Shape.lift_le_bot le).1 a1)
      cases a3 with | bot => cases hf rfl | @forallE _ _ _ _ _ _ _ m₁ b1 b2 b3 b4 b5
      cases m₁ with simp [Shape.LE.def] at b5 | bot => cases hf rfl | forallE
      cases a4.unfold with | bot => cases hm ((Shape.lift_le_bot le).1 a1) | lam d1
      refine (LE_Interp.lift le).1 <| .lam (b1.mono b5.1) d1.2.1 (fun _ h => ?_) a1
      exact .app a2.weak (.bvar (Nat.le_refl _) (Nat.le_refl _) .rfl) .rfl
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, (ih2 W).2⟩
    · sorry
    · sorry
  | extra => sorry

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  DefEq' (M N A : SExpr) (m a : Shape n) : Prop

def LogRelBase.DefEq (R : LogRelBase Γ n) (M N A : SExpr) (m a : Shape n) : Prop :=
  Shape.HasType m a ∧ Γ ⊢ M ≡ N : A
    ∧ LE_Interp .nil m M ∧ LE_Interp .nil m N ∧ LE_Interp .nil a A
    -- ∧ CheckType Γ M A u ∧ CheckType Γ N A u ∧ InferTypeS Γ A (.sort u)
    ∧ R.DefEq' M N A m a

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  isType : toLogRelBase.DefEq M N A m a → Γ ⊢ A ≡ A : .sort u → DefEq' A A (.sort u) a .sort
  sort : DefEq' (.sort u) (.sort u) (.sort u.succ) .sort .sort
  left : DefEq' M N A m a → DefEq' M M A m a
  symm : DefEq' M N A m a → DefEq' N M A m a
  trans : DefEq' M₁ M₂ A m a → DefEq' M₂ M₃ A m a → DefEq' M₁ M₃ A m a
  defeqDF : toLogRelBase.DefEq A B (.sort u) a .sort →
    DefEq' M N A m a → DefEq' M N B m a
  mono_2 : m.HasType a → m ≤ m' → a ≤ a' →
    toLogRelBase.DefEq A A (.sort u) a' .sort → DefEq' M N A m' a' → DefEq' M N A m a
  mono_r_1 : m.HasType a → a ≤ a' →
    toLogRelBase.DefEq A A (.sort u) a' .sort → DefEq' M N A m a → DefEq' M N A m a'
  join : m₁ ≠ .bot → m₂ ≠ .bot → m₁.Compat m₂ →
    toLogRelBase.DefEq M N A m₁ a → toLogRelBase.DefEq M N A m₂ a → DefEq' M N A (m₁.join m₂) a

theorem LogRelBase.DefEq.isType {R : LogRel Γ n}
    (H : R.DefEq M N A m a) : ∃ u, R.DefEq A A (.sort u) a .sort :=
  have ⟨h1, h2, _, _, h5, _⟩ := H
  have ⟨_, h2'⟩ := h2.isType
  ⟨_, h1.isType, h2', h5, h5, .sort .rfl, R.isType H h2'⟩

theorem LogRelBase.DefEq.mono_2 {R : LogRel Γ n}
    (hm : m.HasType a) (le1 : m ≤ m') (le2 : a ≤ a') (hA : R.DefEq A A (.sort u) a' .sort) :
    R.DefEq M N A m' a' → R.DefEq M N A m a
  | ⟨_, h2, h3, h4, h5, h6⟩ =>
    ⟨hm, h2, h3.mono le1, h4.mono le1, h5.mono le2, R.mono_2 hm le1 le2 hA h6⟩

theorem LogRelBase.DefEq.mono_l {R : LogRel Γ n}
    (hm : m.HasType a) (le : m ≤ m') (H : R.DefEq M N A m' a) : R.DefEq M N A m a :=
  let ⟨_, h⟩ := H.isType; h.mono_2 hm le .rfl H

theorem LogRelBase.DefEq.mono_r_1 {R : LogRel Γ n}
    (ha : a ≤ a') (hA : R.DefEq A A (.sort u) a' .sort) : R.DefEq M N A m a → R.DefEq M N A m a'
  | ⟨ht, h2, h3, h4, _, h6⟩ => ⟨.mono_r ha hA.1 ht, h2, h3, h4, hA.2.2.1, R.mono_r_1 ht ha hA h6⟩

theorem LogRelBase.DefEq.mono_r_2 {R : LogRel Γ n}
    (ht : m.HasType a) (ha : a ≤ a') (H : R.DefEq M N A m a') : R.DefEq M N A m a :=
  let ⟨_, h⟩ := H.isType; h.mono_2 ht .rfl ha H

theorem LogRelBase.DefEq.left {R : LogRel Γ n} : R.DefEq M N A m a → R.DefEq M M A m a
  | ⟨h1, h2, h3, _, h5, h6⟩ => ⟨h1, h2.hasType.1, h3, h3, h5, R.left h6⟩

theorem LogRelBase.DefEq.symm {R : LogRel Γ n} : R.DefEq M N A m a → R.DefEq N M A m a
  | ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2.symm, h4, h3, h5, R.symm h6⟩

theorem LogRelBase.DefEq.trans {R : LogRel Γ n} :
    R.DefEq M₁ M₂ A m a → R.DefEq M₂ M₃ A m a → R.DefEq M₁ M₃ A m a
  | ⟨a1, a2, a3, _, a5, a6⟩, ⟨_, b2, _, b4, _, b6⟩ => ⟨a1, a2.trans b2, a3, b4, a5, R.trans a6 b6⟩

theorem LogRelBase.DefEq.join {R : LogRel Γ n} (hJ : m₁.Join m₂ m)
    (h1 : R.DefEq M N A m₁ a) (h2 : R.DefEq M N A m₂ a) : R.DefEq M N A m a := by
  have ⟨_, h2'⟩ := h2.isType
  by_cases c1 : m₁ = .bot
  · exact .mono_2 (.join hJ h1.1 h2.1) ((hJ _).2 ⟨c1 ▸ Shape.bot_le, .rfl⟩) .rfl h2' h2
  by_cases c2 : m₂ = .bot
  · exact .mono_2 (.join hJ h1.1 h2.1) ((hJ _).2 ⟨.rfl, c2 ▸ Shape.bot_le⟩) .rfl h2' h1
  let ⟨a1, a2, a3, a4, a5, _⟩ := h1; let ⟨b1, _, b3, b4, _⟩ := h2
  refine ⟨a1.join hJ b1, a2, a3.join hJ b3, a4.join hJ b4, a5, ?_⟩
  have ⟨_, h⟩ := h1.isType
  refine R.mono_2 (a1.join hJ b1) (Shape.Join.iff.1 hJ).2.2 .rfl h (R.join c1 c2 hJ.compat h1 h2)

theorem LogRelBase.DefEq.defeqDF {R : LogRel Γ n}
    (hA : R.DefEq A B (.sort u) a .sort) : R.DefEq M N A m a → R.DefEq M N B m a
  | ⟨ht, h2, h3, h4, _, h6⟩ =>
    let ⟨_, a2, _, a4, _⟩ := hA
    have ⟨_, b1⟩ := a2.isType
    ⟨ht, .defeqDF (b1.defeqDF a2) h2, h3, h4, a4, R.defeqDF hA h6⟩

theorem LogRelBase.DefEq.sort {R : LogRel Γ n} :
    R.DefEq (.sort u) (.sort u) (.sort u.succ) .sort .sort :=
  ⟨.sort, .sort, .sort .rfl, .sort .rfl, .sort .rfl, R.sort⟩

theorem LogRel.mono_r {R : LogRel Γ n}
    (ht : m.HasType a) (hA : R.DefEq A A (.sort u) a' .sort) (ha : a ≤ a') :
    R.DefEq M N A m a ↔ R.DefEq M N A m a' := ⟨.mono_r_1 ha hA, .mono_r_2 ht ha⟩

def LR0.DefEqTy (Γ : List SExpr) (M N : SExpr) (m : Shape 0) : Prop :=
  match m with
  | .bot => True
  | .sort => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u

def LRS.DefEqTy (IH : LogRel Γ n)
    (Γ : List SExpr) (M N : SExpr) (m : Shape (n+1)) : Prop :=
  match m with
  | .bot => True
  | .sort => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  | .forallE m₁ m₂ =>
    ∃ M₁ M₂ N₁ N₂, Γ ⊢ M ⤳* .forallE M₁ M₂ ∧ Γ ⊢ N ⤳* .forallE N₁ N₂ ∧
    ∃ u v, IH.DefEq M₁ N₁ (.sort u) m₁ .sort ∧ M₁::Γ ⊢ M₂ ≡ N₂ : sort v ∧
    (∀ {{a b p}}, IH.DefEq a b M₁ p m₁ →
      IH.DefEq (M₂.inst a) (M₂.inst b) (.sort v) (ShapeFun.app m₂ p) .sort ∧
      IH.DefEq (N₂.inst a) (N₂.inst b) (.sort v) (ShapeFun.app m₂ p) .sort) ∧
    (∀ {{a p}}, IH.DefEq a a M₁ p m₁ →
      IH.DefEq (M₂.inst a) (N₂.inst a) (.sort v) (ShapeFun.app m₂ p) .sort)
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
  | .sort => ∃ u, Γ ⊢ A ⤳* .sort u ∧ DefEqTy IH Γ M N m
  | .forallE a₁ a₂ => ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
    IH.DefEq A₁ A₁ (.sort u) a₁ .sort ∧ A₁::Γ ⊢ A₂ : sort v ∧
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ →
      IH.DefEq (A₂.inst a) (A₂.inst b) (.sort v) (ShapeFun.app a₂ p) .sort) ∧
    DefEqForall IH M N A₁ A₂ m a₁ a₂
  | _ => False

def LR0.DefEq' (Γ : List SExpr) (M N A : SExpr) (m a : Shape 0) : Prop :=
  match a with
  | .bot => True
  | .sort => ∃ u, Γ ⊢ A ⤳* .sort u ∧ DefEqTy Γ M N m

def LR0 : LogRel Γ 0 where
  DefEq' := LR0.DefEq' Γ
  isType {M N A m a u} h1 hA := by
    let ⟨h1, h2, _, _, _, h6⟩ := h1
    simp [LR0.DefEq'] at h6; split at h6
    · exact ⟨_, .rfl, trivial⟩
    · obtain ⟨⟨v, h1⟩, h2⟩ := h6; exact ⟨_, .rfl, _, h1, h1⟩
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
  mono_2 {m m' a a' A U M N} h1 hm ha hA := by
    obtain ⟨A1, A2, _, A3, A4⟩ := hA
    cases h1.unfold with
    | bot h1 =>
      cases A1.unfold with
      | bot => cases Shape.le_bot.1 ha; exact fun _ => trivial
      | sort =>
        obtain rfl|rfl := Shape.le_sort.1 ha <;> [exact fun _ => trivial; skip]
        exact fun ⟨_, h, _⟩ => ⟨_, h, trivial⟩
    | sort =>
      cases m' <;> cases hm
      cases a' <;> cases ha
      exact id
  mono_r_1 {a a' A U M N m} h1 le hA := by
    obtain ⟨A1, A2, _, _, _, _, A3, A4⟩ := hA
    cases A1.unfold with
    | bot => cases Shape.le_bot.1 le; exact id
    | sort =>
      obtain rfl|rfl := Shape.le_sort.1 le <;> [rintro -; exact id]
      cases h1.unfold; have ⟨_, h, _⟩ := A4; exact ⟨_, h, ⟨⟩⟩
  join {m₁ m₂ M N A a} ne1 _ _ h1 _ :=
    match m₁ with | .bot => nomatch ne1 rfl | .sort => by cases m₂ <;> exact h1.2.2.2.2.2

def LRS (IH : LogRel Γ n) : LogRel Γ (n + 1) where
  DefEq' := LRS.DefEq' IH
  isType {M N A m a u} h1 hA := by
    let ⟨h1, h2, _, _, _, h6⟩ := h1
    simp [LRS.DefEq'] at h6; split at h6
    · exact ⟨_, .rfl, trivial⟩
    · obtain ⟨⟨v, h1⟩, h2⟩ := h6; exact ⟨_, .rfl, _, h1, h1⟩
    · obtain ⟨_, _, h1, ⟨_, h2⟩, _, h3, h4, _⟩ := h6
      exact ⟨_, .rfl, _, _, _, _, h1, h1, _, _, h2, h3,
        fun _ _ _ a1 => ⟨h4 a1, h4 a1⟩, fun _ _ a1 => h4 a1⟩
    · cases h6
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
  mono_2 {m m' a a' A U M N} h1 hm ha hA := by
    stop
    obtain ⟨A1, A2, _, _, _, _, A3, A4⟩ := hA
    cases h1.unfold with
    | bot h1 =>
      cases A1.unfold with
      | bot => cases Shape.le_bot.1 ha; exact fun _ => trivial
      | sort =>
        obtain rfl|rfl := Shape.le_sort.1 ha <;> [exact fun _ => trivial; skip]
        exact fun ⟨_, h, _⟩ => ⟨_, h, trivial⟩
      | forallE a1 a2 =>
        cases a with simp [Shape.LE.def] at ha | bot => exact fun _ => trivial | forallE
        have .forallE a3 a4 := h1.unfold; intro ⟨_, _, _, _, b1, b2, b3, b4, b5⟩
        refine ⟨_, _, _, _, b1, .mono_l a3 ha.1 b2, b3, fun _ _ _ c1 => ?_, ⟨⟩⟩
        exact (b4 (b2.mono_r_1 ha.1 c1)).mono_l (.pi_app a4 c1.1) (ShapeFun.app_mono_l ha.2 _)
    | sort =>
      cases m' <;> simp [Shape.LE.def] at hm
      cases a' <;> simp [Shape.LE.def] at ha
      exact id
    | forallE c1 c2 =>
      cases m' <;> simp [Shape.LE.def] at hm
      cases a' <;> simp [Shape.LE.def] at ha
      intro ⟨_, a3, _, _, _, _, a4, a5, _, _, a6, a7, a8, a9⟩
      refine ⟨_, a3, _, _, _, _, a4, a5, _, _, a6.mono_l c1 hm.1, a7,
        fun _ _ _ d => ?_, fun _ _ d => ?_⟩ <;>
        have ⟨d1, d2⟩ := a8 (.mono_r_1 hm.1 a6.left d)
      · exact have d3 := .pi_app c2 d.1; have d4 := ShapeFun.app_mono_l hm.2 _
          ⟨d1.mono_l d3 d4, d2.mono_l d3 d4⟩
      · exact (a9 (a6.left.mono_r_1 hm.1 d)).mono_l (.pi_app c2 d.1) (ShapeFun.app_mono_l hm.2 _)
    | lam c1 c2 c3 =>
      cases m' <;> simp [Shape.LE.def] at hm
      cases a' <;> simp [Shape.LE.def] at ha
      rintro ⟨_, _, _, _, a1, a2, a3, a4, a5, a6⟩
      refine ⟨_, _, _, _, a1, .mono_l c1 ha.1 a2, a3,
        fun _ _ _ d => ?_, fun _ _ _ d => ?_, fun _ _ d => ?_⟩
      · exact .mono_l (.pi_app c2 d.1) (ShapeFun.app_mono_l ha.2 _) (a4 (.mono_r_1 ha.1 a2 d))
      · have ⟨a7, a8⟩ := a5 (.mono_r_1 ha.1 a2 d)
        exact
          have h1 := .lam_app c3 d.1; have h2 := ShapeFun.app_mono_l hm _
          have h3 := ShapeFun.app_mono_l ha.2 _; have h4 := a4 (.mono_r_1 ha.1 a2 d.left)
          ⟨.mono_2 h1 h2 h3 h4 a7, .mono_2 h1 h2 h3 h4 a8⟩
      · exact .mono_2 (.lam_app c3 d.1) (ShapeFun.app_mono_l hm _)
          (ShapeFun.app_mono_l ha.2 _) (a4 (.mono_r_1 ha.1 a2 d.left)) (a6 (.mono_r_1 ha.1 a2 d))
  mono_r_1 {a a' A U M N m} h1 le hA := by
    stop
    obtain ⟨A1, A2, _, _, _, _, A3, A4⟩ := hA
    cases A1.unfold with
    | bot => cases Shape.le_bot.1 le; exact id
    | sort =>
      obtain rfl|rfl := Shape.le_sort.1 le <;> [rintro -; exact id]
      cases h1.unfold; have ⟨_, h, _⟩ := A4; exact ⟨_, h, ⟨⟩⟩
    | forallE a1 a2 =>
      have ⟨_, _, _, _, A4, A5, _, _, A6, A7, A8, A9⟩ := A4
      refine fun h2 => ⟨_, _, _, _, A4, A6.left, A7.hasType.1, fun _ _ _ c1 => (A8 c1).1, ?_⟩
      cases a with simp [Shape.LE.def] at le | bot => cases h1.unfold; trivial | forallE
      cases h1.unfold with | bot => trivial | lam a3 a4 a5
      have ⟨_, _, _, _, B4, B5, _, B6, B7, B8⟩ := h2
      cases A4.determ .forallE B4 .forallE
      refine ⟨fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩
      · have ⟨_, c2, c3, eq⟩ := Shape.HasType.maximal a5 le.1 c1.1
        have ⟨b1, b2⟩ := B7 (.mono_2 c2 c3 le.1 A6.left c1)
        exact have h3 := .trans (ShapeFun.app_mono_l le.2 _) (ShapeFun.app_mono_r c3)
          ⟨.mono_r_1 h3 (A8 c1).1.left (eq ▸ b1), .mono_r_1 h3 (A8 c1).1.left (eq ▸ b2)⟩
      · have ⟨_, c2, c3, eq⟩ := Shape.HasType.maximal a5 le.1 c1.1
        exact have h3 := .trans (ShapeFun.app_mono_l le.2 _) (ShapeFun.app_mono_r c3)
          .mono_r_1 h3 (A8 c1).1.left (eq ▸ B8 (.mono_2 c2 c3 le.1 A6.left c1))
  join {m₁ m₂ M N A a} ne1 ne2 hC h1 h2 := by
    cases h1.1.unfold with
    | bot => cases ne1 rfl
    | sort =>
      cases m₂ with simp [Shape.Compat] at hC | bot => cases ne2 rfl | sort
      exact h1.2.2.2.2.2
    | forallE =>
      cases m₂ with simp [Shape.Compat] at hC | bot => cases ne2 rfl | forallE
      simp [Shape.join]
      have hJ₁ := Shape.Join.mk hC.1; have hJ₂ := ShapeFun.Join.mk hC.2
      have ⟨_, _, _, _, _, _, a1, _, _, _, _, a2, a3, _, _, a4, a5, a6, a7⟩ := h1
      have ⟨_, _, _, _, _, _, b1, _, _, _, _, b2, b3, _, _, b4, b5, b6, b7⟩ := h2
      cases a2.determ .forallE b2 .forallE; cases a3.determ .forallE b3 .forallE
      cases a4.2.1.uniq_sort b4.2.1.symm
      refine ⟨_, a1, _, _, _, _, a2, a3, _, _, a4.join hJ₁ b4, a5,
        fun _ _ _ c1 => ⟨?_, ?_⟩, fun _ _ c1 => ?_⟩
      · stop
        have := a6 (c1.mono_r_2 _ hJ₁.le.1)
        sorry
      · sorry
      · sorry
    | lam _ => sorry

def LR (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => LR0
  | _+1 => LRS (LR Γ)

inductive LR.Subst : (Γ : List SExpr) → (σ : Subst) → (Δ : List SExpr) → Valuation → Prop
  | nil : LR.Subst Γ .id Γ .nil
  | cons : LR.Subst Γ σ.tail Δ ρ →
    (∀ a, LE_Interp ρ a A →
      (LR Γ).DefEq (A.subst σ.tail) (A.subst σ.tail) (.sort u) a .sort) →
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
    exact have c2 := .mono_r_1 c1.le_sort .sort c2
      ⟨_, a3, .trans (.mono_r_1 a1 c2 h2) (.mono_r_1 a2 c2 h4)⟩
  | _ => sorry
