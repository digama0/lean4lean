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

-- def Shape.rank : Shape → Nat
--   | .bot => 0
--   | .sort k => k + 1
--   | .forallE s₁ s₂ =>
--     s₂.attach.foldl (fun n ⟨(a, b), _⟩ => max n (max a.rank b.rank)) s₁.rank + 1
-- decreasing_by all_goals
--   simp; first | omega | have := List.sizeOf_lt_of_mem ‹_›; simp at this; omega

-- omit [Params] in
-- theorem Shape.rank_forall_le : (forallE s f).rank ≤ n ↔
--   s.rank < n ∧ ∀ x y, (x, y) ∈ f → x.rank < n ∧ y.rank < n := by
--   simp [rank, Nat.succ_le_iff]; generalize s.rank = i
--   rw [(by simp : (∀ _, _) ↔ (∀ x ∈ f.attach, x.1.1.rank < n ∧ x.1.2.rank < n))]
--   induction f.attach generalizing i <;> simp [*, and_assoc, Nat.max_lt]

-- omit [Params] in
-- @[simp] theorem Shape.lt_rank_forall_fst : s.rank < (forallE s f).rank := by
--   simp [← Nat.not_le, rank_forall_le]

-- omit [Params] in
-- theorem Shape.lt_rank_forall_snd :
--     (x, y) ∈ f → x.rank < (forallE s f).rank ∧ y.rank < (forallE s f).rank :=
--   rank_forall_le.1 (Nat.le_refl _) |>.2 _ _

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, _, _ => true
  | _+1, .sort, .sort => true
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

def Shape.Join (x y z : Shape n) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w

def ShapeFun.join (join : Shape n → Shape n → Shape n)
    (f f' : List (Shape n × Shape n)) : List (Shape n × Shape n) := by
  refine f.attach.foldl (init := []) fun l ⟨(x, y), hxy⟩ => ?_
  refine f'.attach.foldl (init := l) fun l ⟨(x', y'), hxy'⟩ => ?_
  refine if x.Compat x' then ?_ else l
  let jx := join x x'
  let jy := join y y'
  exact l.map fun (z, w) => (z, if z ≤ jx then join w jy else w)

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, _ | _+1, .bot, s | _+1, s, .bot => s
  | _+1, .sort, .sort => .sort
  | _+1, .forallE s f, .forallE s' f' => .forallE (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, _, _ => .bot

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n :=
  maxBelow (s.filter (·.1 ≤ a)) |>.2

theorem ShapeFun.app_mono_l {f f' : ShapeFun n} : f.LE f' → ∀ a, f.app a ≤ f'.app a :=
  sorry

theorem ShapeFun.app_mono_r {f : ShapeFun n} : a ≤ a' → f.app a ≤ f.app a' :=
  sorry

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

theorem Shape.app_mono_l {f f' : Shape (n + 1)} (le : f ≤ f') (a) : f.app a ≤ f'.app a := by
  unfold app; split <;> [split; simp]
  · exact ShapeFun.app_mono_l le _
  · cases f' <;> simp [LE.def] at le; grind

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b | _+1, .forallE a b, .sort =>
    a.hasType .sort && b.all fun (x, y) => x.hasType a && y.hasType .sort
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort
  | 0, .sort, .sort | _+1, .sort, .sort => true
  | _+1, .lam f, .forallE a b =>
    a.hasType .sort && b.all (fun (x, y) => x.hasType a && y.hasType .sort) &&
    f.all (fun (x, y) => x.hasType a && y.hasType (ShapeFun.app b x))
  | _, _, _ => false

def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x .sort → HasTypeU .bot x
  | sort : HasTypeU .sort .sort
  | forallE : HasType (n := n) a .sort →
    (∀ x y, (x, y) ∈ b → HasType x a ∧ HasType y .sort) →
    HasTypeU (n := n+1) (.forallE a b) .sort
  | lam : HasType (n := n) a .sort →
    (∀ x y, (x, y) ∈ b → HasType x a ∧ HasType y .sort) →
    (∀ x y, (x, y) ∈ (f : ShapeFun n) → HasType x a ∧ HasType y (ShapeFun.app b x)) →
    HasTypeU (n := n+1) (.lam f) (.forallE a b)

omit [Params] in
theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := by
  unfold HasType hasType; split <;> simp <;> intros <;> constructor <;> try grind [HasType]
  · simp [HasType, hasType]; grind
  · rename_i x; cases x <;> rfl
  · rfl
  · rfl

omit [Params] in
theorem Shape.HasType.unfold_iff {m a : Shape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  unfold HasType hasType
  cases h with
  | bot h =>
    cases h.unfold with
    | bot | sort => cases n <;> rfl
    | forallE => simp; grind [HasType]
  | sort => cases n <;> rfl
  | _ => simp <;> grind [HasType]

omit [Params] in
theorem Shape.HasType.isType {m a : Shape n} (h : HasType m a) : HasType a .sort := by
  cases h.unfold with
  | bot h1 => exact h1
  | sort | forallE => exact unfold_iff.2 .sort
  | lam h1 h2 => exact unfold_iff.2 <| .forallE h1 h2

theorem Shape.HasType.mono_r {m a a' : Shape n} (ha : a ≤ a') :
    HasType a' .sort → HasType m a → HasType m a' := sorry

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

def ShapeFun.WF (WF : Shape n → Bool) (f : ShapeFun n) : Bool :=
  (f.attach.all fun ⟨(x, y), _⟩ => WF x && WF y) && f.any (·.1 ≤ .bot) &&
  f.all fun (x, y) => f.all fun (x', y') =>
    (x.Compat x' → (y.Compat y' && let j := x.join x'; f.any fun (z, _) => z ≤ j && j ≤ z)) &&
    (x ≤ x' → y ≤ y')

def Shape.WF : ∀ {n}, Shape n → Bool
  | 0, _ | _+1, .bot | _+1, .sort .. => true
  | _+1, .forallE s f => s.WF && ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  DefEq' (M N A : SExpr) (m a : Shape n) : Prop

def LogRelBase.DefEq (R : LogRelBase Γ n) (M N A : SExpr) (m a : Shape n) : Prop :=
  Shape.HasType m a ∧ Γ ⊢ M ≡ N : A
    -- ∧ CheckType Γ M A u ∧ CheckType Γ N A u ∧ InferTypeS Γ A (.sort u)
    ∧ R.DefEq' M N A m a

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  isType : toLogRelBase.DefEq M N A m a → Γ ⊢ A ≡ A : .sort u → DefEq' A A (.sort u) a .sort
  left : DefEq' M N A m a → DefEq' M M A m a
  symm : DefEq' M N A m a → DefEq' N M A m a
  trans : DefEq' M₁ M₂ A m a → DefEq' M₂ M₃ A m a → DefEq' M₁ M₃ A m a
  defeqDF : toLogRelBase.DefEq A B (.sort u) a .sort →
    DefEq' M N A m a → DefEq' M N B m a
  mono'_2 : m.HasType a → m ≤ m' → a ≤ a' →
    toLogRelBase.DefEq A A (.sort u) a' .sort → DefEq' M N A m' a' → DefEq' M N A m a
  mono'_r_1 : m.HasType a → a ≤ a' →
    toLogRelBase.DefEq A A (.sort u) a' .sort → DefEq' M N A m a → DefEq' M N A m a'

theorem LogRelBase.DefEq.isType {R : LogRel Γ n}
    (H : R.DefEq M N A m a) : ∃ u, R.DefEq A A (.sort u) a .sort :=
  have ⟨h1, h2, _⟩ := H
  have ⟨_, h2'⟩ := h2.isType
  ⟨_, h1.isType, h2', R.isType H h2'⟩

theorem LogRelBase.DefEq.mono_2 {R : LogRel Γ n}
    (hm : m.HasType a) (le1 : m ≤ m') (le2 : a ≤ a') (hA : R.DefEq A A (.sort u) a' .sort) :
    R.DefEq M N A m' a' → R.DefEq M N A m a
  | ⟨_, h2, h3⟩ => ⟨hm, h2, R.mono'_2 hm le1 le2 hA h3⟩

theorem LogRelBase.DefEq.mono_l {R : LogRel Γ n}
    (hm : m.HasType .sort) (le : m ≤ m') (H : R.DefEq M N A m' .sort) : R.DefEq M N A m .sort :=
  let ⟨_, h⟩ := H.isType; h.mono_2 hm le .rfl H

theorem LogRelBase.DefEq.mono_r_1 {R : LogRel Γ n}
    (ha : a ≤ a') (hA : R.DefEq A A (.sort u) a' .sort) : R.DefEq M N A m a → R.DefEq M N A m a'
  | ⟨ht, h2, h3⟩ => ⟨.mono_r ha hA.1 ht, h2, R.mono'_r_1 ht ha hA h3⟩

theorem LogRelBase.DefEq.mono_r_2 {R : LogRel Γ n}
    (ht : m.HasType a) (ha : a ≤ a') (H : R.DefEq M N A m a') : R.DefEq M N A m a :=
  let ⟨_, h⟩ := H.isType; h.mono_2 ht .rfl ha H

theorem LogRelBase.DefEq.left {R : LogRel Γ n} : R.DefEq M N A m a → R.DefEq M M A m a
  | ⟨h1, h2, h6⟩ => ⟨h1, h2.hasType.1, R.left h6⟩

theorem LogRelBase.DefEq.symm {R : LogRel Γ n} : R.DefEq M N A m a → R.DefEq N M A m a
  | ⟨h1, h2, h6⟩ => ⟨h1, h2.symm, R.symm h6⟩

theorem LogRelBase.DefEq.trans {R : LogRel Γ n} :
    R.DefEq M₁ M₂ A m a → R.DefEq M₂ M₃ A m a → R.DefEq M₁ M₃ A m a
  | ⟨a1, a2, a3⟩, ⟨_, b2, b3⟩ => ⟨a1, a2.trans b2, R.trans a3 b3⟩

theorem LogRelBase.DefEq.defeqDF {R : LogRel Γ n}
    (hA : R.DefEq A B (.sort u) a .sort) : R.DefEq M N A m a → R.DefEq M N B m a
  | ⟨ht, h2, h6⟩ =>
    let ⟨_, a2, _⟩ := hA
    -- have ⟨_, a4⟩ := R.sort_r a3
    have ⟨_, b1⟩ := a2.isType
    ⟨ht, .defeqDF (b1.defeqDF a2) h2, R.defeqDF hA h6⟩

theorem LogRel.mono_r {R : LogRel Γ n}
    (ht : m.HasType a) (hA : R.DefEq A A (.sort u) a' .sort) (ha : a ≤ a') :
    R.DefEq M N A m a ↔ R.DefEq M N A m a' := ⟨.mono_r_1 ha hA, .mono_r_2 ht ha⟩

def TypeEq0.DefEqTy (Γ : List SExpr) (M N : SExpr) (m : Shape 0) : Prop :=
  match m with
  | .bot => True
  | .sort => ∃ u, WHRedS Γ M (.sort u) ∧ WHRedS Γ N (.sort u)

def TypeEqS.DefEqTy (IH : LogRel Γ n)
    (Γ : List SExpr) (M N : SExpr) (m : Shape (n+1)) : Prop :=
  match m with
  | .bot => True
  | .sort => ∃ u, WHRedS Γ M (.sort u) ∧ WHRedS Γ N (.sort u)
  | .forallE m₁ m₂ =>
    ∃ M₁ M₂ N₁ N₂, WHRedS Γ M (.forallE M₁ M₂) ∧ WHRedS Γ N (.forallE N₁ N₂) ∧
    ∃ u v, IH.DefEq M₁ N₁ (.sort u) m₁ .sort ∧ M₁::Γ ⊢ M₂ ≡ N₂ : sort v ∧
    (∀ {{a b p}}, IH.DefEq a b M₁ p m₁ →
      IH.DefEq (M₂.inst a) (M₂.inst b) (.sort v) (ShapeFun.app m₂ p) .sort ∧
      IH.DefEq (N₂.inst a) (N₂.inst b) (.sort v) (ShapeFun.app m₂ p) .sort) ∧
    (∀ {{a p}}, IH.DefEq a a M₁ p m₁ →
      IH.DefEq (M₂.inst a) (N₂.inst a) (.sort v) (ShapeFun.app m₂ p) .sort)
  | _ => False

def TypeEqS.DefEqForall (IH : LogRel Γ n) (M N A₁ A₂ : SExpr) (m : Shape (n+1))
    (a₁ : Shape n) (a₂ : ShapeFun n) : Prop :=
  match m with
  | .bot => True
  | .lam m =>
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ →
      IH.DefEq (M.inst a) (M.inst b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) ∧
      IH.DefEq (N.inst a) (N.inst b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p)) ∧
    (∀ {{a p}}, IH.DefEq a a A₁ p a₁ →
      IH.DefEq (M.inst a) (N.inst a) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p))
  | _ => False

def TypeEqS.DefEq' (IH : LogRel Γ n) (M N A : SExpr) (m a : Shape (n+1)) : Prop :=
  match a with
  | .bot => True
  | .sort => ∃ u, WHRedS Γ A (.sort u) ∧ DefEqTy IH Γ M N m
  | .forallE a₁ a₂ => ∃ A₁ A₂ u v, WHRedS Γ A (.forallE A₁ A₂) ∧
    IH.DefEq A₁ A₁ (.sort u) a₁ .sort ∧ A₁::Γ ⊢ A₂ : sort v ∧
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ →
      IH.DefEq (A₂.inst a) (A₂.inst b) (.sort v) (ShapeFun.app a₂ p) .sort) ∧
    DefEqForall IH M N A₁ A₂ m a₁ a₂
  | _ => False

def TypeEq0.DefEq' (Γ : List SExpr) (M N A : SExpr) (m a : Shape 0) : Prop :=
  match a with
  | .bot => True
  | .sort => ∃ u, WHRedS Γ A (.sort u) ∧ DefEqTy Γ M N m

def TypeEq0 : LogRel Γ 0 := by
  refine {
    DefEq' := TypeEq0.DefEq' Γ
    isType {M N A m a u} h1 hA := ?_
    left {M N A m a} h1 := ?_
    symm {M N A m a} h1 := ?_
    trans {M₁ M₂ A m a M₃} := ?_
    defeqDF {A B u a M N m} hA := ?_
    mono'_2 {m m' a a' A U M N} h1 hm ha hA := ?_
    mono'_r_1 {a a' A U M N m} h1 le hA := ?_ }
  · let ⟨h1, h2, h6⟩ := h1
    simp [TypeEq0.DefEq'] at h6; split at h6
    · exact ⟨_, .rfl, trivial⟩
    · obtain ⟨⟨v, h1⟩, h2⟩ := h6; exact ⟨_, .rfl, _, h1, h1⟩
  · dsimp [TypeEq0.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [TypeEq0.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, _⟩ := h3; exact ⟨h1, h3, h3⟩
  · dsimp [TypeEq0.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [TypeEq0.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, h4⟩ := h3; exact ⟨h1, h4, h3⟩
  · dsimp [TypeEq0.DefEq']; split
    · simp
    · rintro ⟨_, a1, a2⟩ ⟨_, -, b2⟩; refine ⟨_, a1, ?_⟩
      revert a2 b2; dsimp [TypeEq0.DefEqTy]; split
      · simp
      · rintro ⟨_, a1, a2⟩ ⟨_, b1, b2⟩; cases a2.determ .sort b1 .sort; exact ⟨_, a1, b2⟩
  · obtain ⟨A1, A2, A6⟩ := hA
    dsimp [TypeEq0.DefEq']; split
    · trivial
    · rintro ⟨u, a1, a2⟩
      let ⟨_, _, _, _, b3⟩ := A6
      exact ⟨_, b3, a2⟩
  · obtain ⟨A1, A2, _, A3, A4⟩ := hA
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
  · obtain ⟨A1, A2, _, A3, A4⟩ := hA
    cases A1.unfold with
    | bot => cases Shape.le_bot.1 le; exact id
    | sort =>
      obtain rfl|rfl := Shape.le_sort.1 le <;> [rintro -; exact id]
      cases h1.unfold; have ⟨_, h, _⟩ := A4; exact ⟨_, h, ⟨⟩⟩

def TypeEqS (IH : LogRel Γ n) : LogRel Γ (n + 1) := by
  refine {
    DefEq' := TypeEqS.DefEq' IH
    isType {M N A m a u} h1 hA := ?_
    left {M N A m a} h1 := ?_
    symm {M N A m a} h1 := ?_
    trans {M₁ M₂ A m a M₃} := ?_
    defeqDF {A B u a M N m} hA := ?_
    mono'_2 {m m' a a' A U M N} h1 hm ha hA := ?_
    mono'_r_1 {a a' A U M N m} h1 le hA := ?_ }
  · let ⟨h1, h2, h6⟩ := h1
    simp [TypeEqS.DefEq'] at h6; split at h6
    · exact ⟨_, .rfl, trivial⟩
    · obtain ⟨⟨v, h1⟩, h2⟩ := h6; exact ⟨_, .rfl, _, h1, h1⟩
    · obtain ⟨_, _, h1, ⟨_, h2⟩, _, h3, h4, _⟩ := h6
      exact ⟨_, .rfl, _, _, _, _, h1, h1, _, _, h2, h3,
        fun _ _ _ a1 => ⟨h4 a1, h4 a1⟩, fun _ _ a1 => h4 a1⟩
    · cases h6
  · dsimp [TypeEqS.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [TypeEqS.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, _⟩ := h3; exact ⟨h1, h3, h3⟩
      · let ⟨_, _, _, _, h1, _, _, h3, h4, h4', h5, h6⟩ := h3
        exact ⟨_, _, _, _, h1, h1, _, h3, h4.left, h4'.hasType.1,
          fun a b p a1 => ⟨(h5 a1).1, (h5 a1).1⟩, fun a p a1 => (h5 a1).1⟩
      · cases h3
    · let ⟨_, _, _, _, h1, h3, h4, h5, h6⟩ := h1; refine ⟨_, _, _, _, h1, h3, h4, h5, ?_⟩
      dsimp [TypeEqS.DefEqForall] at h6 ⊢; split at h6
      · trivial
      · exact ⟨fun a b p a1 => ⟨(h6.1 a1).1, (h6.1 a1).1⟩, fun a p a1 => (h6.1 a1).1⟩
      · cases h6
    · cases h1
  · dsimp [TypeEqS.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h3⟩ := h1; refine ⟨_, h1, ?_⟩
      dsimp [TypeEqS.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h3, h4⟩ := h3; exact ⟨h1, h4, h3⟩
      · let ⟨B, F, B', F', h1, h2, _, _, h3, h4, h5, h6⟩ := h3
        refine ⟨_, _, _, _, h2, h1, _, _, h3.symm, h3.2.1.defeqDF_l h4.symm, ?_, ?_⟩
        · exact fun a b p a1 => (h5 (.defeqDF h3.symm a1)).symm
        · exact fun a p a1 => (h6 (.defeqDF h3.symm a1)).symm
      · cases h3
    · let ⟨_, _, _, _, h1, h2, h3, h4, h6⟩ := h1; refine ⟨_, _, _, _, h1, h2, h3, h4, ?_⟩
      dsimp [TypeEqS.DefEqForall] at h6 ⊢; split at h6
      · trivial
      · exact ⟨fun a b p a1 => (h6.1 a1).symm, fun a p a1 => (h6.2 a1).symm⟩
      · cases h6
    · cases h1
  · dsimp [TypeEqS.DefEq']; split
    · simp
    · rintro ⟨_, a1, a2⟩ ⟨_, -, b2⟩; refine ⟨_, a1, ?_⟩
      revert a2 b2; dsimp [TypeEqS.DefEqTy]; split
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
      revert a5 b5; dsimp [TypeEqS.DefEqForall]; split
      · simp
      · intro ⟨a5, a6⟩ ⟨b5, b6⟩
        exact ⟨fun _ _ _ c1 => ⟨(a5 c1).1, (b5 c1).2⟩, fun _ _ c1 => (a6 c1).trans (b6 c1)⟩
      · nofun
    · nofun
  · obtain ⟨A1, A2, A6⟩ := hA
    dsimp [TypeEqS.DefEq']; split
    · trivial
    · rintro ⟨u, a1, a2⟩
      let ⟨_, _, _, _, b3⟩ := A6
      exact ⟨_, b3, a2⟩
    · rename_i b f; rintro ⟨B₁, F₁, _, _, a1, a2, a3, a4, a5⟩
      let ⟨_, b1, B₁', F₁', B₂, F₂, b2, b3, _, _, b4, b4', b5, b6⟩ := A6
      cases a1.determ .forallE b2 .forallE
      refine ⟨_, _, _, _, b3, b4.symm.left, b4.2.1.defeqDF_l b4'.hasType.2,
        fun _ _ _ c1 => (b5 (.defeqDF b4.symm c1)).2, ?_⟩
      revert a5; dsimp [TypeEqS.DefEqForall]; split
      · simp
      · refine fun ⟨d1, d2⟩ => ⟨fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩ <;>
          have c2 := b4.symm.defeqDF c1
        · exact ⟨.defeqDF (b6 c2.left) (d1 c2).1, .defeqDF (b6 c2.left) (d1 c2).2⟩
        · exact .defeqDF (b6 c2) (d2 c2)
      · nofun
    · nofun
  · obtain ⟨A1, A2, _, A3, A4⟩ := hA
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
  · obtain ⟨A1, A2, _, A3, A4⟩ := hA
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

def TypeEq (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => TypeEq0
  | _+1 => TypeEqS (TypeEq Γ)
