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

def Shape.HasType.mono_r {m a a' : Shape n} (ha : a ≤ a') : HasType a' .sort → HasType m a → HasType m a' := sorry
def Shape.HasType.mono_l {m m' a : Shape n} (le : m ≤ m') : HasType m' a → HasType m a := sorry

def Shape.HasType.lam_app
    (H : ∀ x y, (x, y) ∈ (f : ShapeFun n) → HasType x a ∧ HasType y (ShapeFun.app b x))
    (ht : HasType x a) : HasType (ShapeFun.app f x) (ShapeFun.app b x) := sorry

def ShapeFun.WF (WF : Shape n → Bool) (f : ShapeFun n) : Bool :=
  (f.attach.all fun ⟨(x, y), _⟩ => WF x && WF y) && f.any (·.1 ≤ .bot) &&
  f.all fun (x, y) => f.all fun (x', y') =>
    (x.Compat x' → (y.Compat y' && let j := x.join x'; f.any fun (z, _) => z ≤ j && j ≤ z)) &&
    (x ≤ x' → y ≤ y')

def Shape.WF : ∀ {n}, Shape n → Bool
  | 0, _ | _+1, .bot | _+1, .sort .. => true
  | _+1, .forallE s f => s.WF && ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f

@[ext] structure Classifier' (n : Nat) where
  DefEq' : SExpr → SExpr → Shape n → Prop
  mono' : p ≤ p' → DefEq' e e' p' → DefEq' e e' p

abbrev Classifier (_Γ : List SExpr) (_A _B : SExpr) (_k : Shape n) := Classifier' n

def Classifier.true : Classifier Γ A B k := ⟨fun _ _ _ => True, fun _ _ => trivial⟩

-- def Classifier.DefEq (C : Classifier Γ A B (n := n) k) (a b : SExpr) (p : Shape n) : Prop :=
--   CheckType Γ a A ∧ CheckType Γ b B ∧ CRDefEq Γ a b A ∧ C.DefEq' a b p

-- theorem Classifier.DefEq.mono {C : Classifier Γ A B k}
--     (le : p ≤ p') : C.DefEq a b p' → C.DefEq a b p
--   | ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, C.mono' le h4⟩

structure Classifier.LE (C C' : Classifier Γ A B k) : Prop where
  mono' : C.DefEq' a b p → C'.DefEq' a b p
  mono'_r : C.DefEq' a b p → C'.DefEq' a b p
instance : LE (Classifier Γ A B n) := ⟨Classifier.LE⟩

-- theorem Classifier.LE.rfl {C : Classifier Γ A B n} : C ≤ C where mono' := id

-- theorem Classifier.LE.mono {C C' : Classifier Γ A B n} (H : C ≤ C') :
--     C.DefEq a b p → C'.DefEq a b p
--   | ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, H.mono' h4⟩

-- structure LogRelK (Γ : List SExpr) (A B : SExpr) (n : Nat) where
--   TypeEq' (u : SLevel) : Classifier Γ A B n → Prop
abbrev LogRelK (Γ : List SExpr) (A B : SExpr) (k : Shape n) :=
  SLevel → Classifier Γ A B k → Prop

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  DefEq' (M N A : SExpr) (m a : Shape n) : SLevel → Prop

def LogRelBase.DefEq (R : LogRelBase Γ n) (M N A : SExpr) (m a : Shape n) (u : SLevel) : Prop :=
  Shape.HasType m a ∧ CRDefEq Γ M N A ∧ CheckType Γ M A u ∧ CheckType Γ N A u ∧
    InferTypeS Γ A (.sort u) ∧ R.DefEq' M N A m a u

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  isType : toLogRelBase.DefEq M N A m a u → DefEq' A A (.sort u) a .sort u.succ
  left : DefEq' M N A m a u → DefEq' M M A m a u
  symm : DefEq' M N A m a u → DefEq' N M A m a u
  trans : DefEq' M₁ M₂ A m a u → DefEq' M₂ M₃ A m a u → DefEq' M₁ M₃ A m a u
  defeqDF : toLogRelBase.DefEq A B (.sort u) a .sort u.succ →
    DefEq' M N A m a u → DefEq' M N B m a u
  defeqL : Γ ⊢ M ≫≪ M' : A → DefEq' M N A m a u → DefEq' M' N A m a u
  mono'_r : m'.HasType a → m ≤ m' → DefEq' M N A m' a u → DefEq' M N A m a u
  mono'_l_1 : m.HasType a → a ≤ a' →
    toLogRelBase.DefEq A A (.sort u) a' .sort u.succ → DefEq' M N A m a u → DefEq' M N A m a' u
  mono'_l_2 : m.HasType a → a ≤ a' → DefEq' M N A m a' u → DefEq' M N A m a u

-- def LogRel.DefEq (R : LogRel Γ n) (M N A : SExpr) (m a : Shape n) : Prop :=
--   R.toLogRelBase.

theorem LogRelBase.DefEq.isType {R : LogRel Γ n}
    (H : R.DefEq M N A m a u) : R.DefEq A A (.sort u) a .sort u.succ :=
  have ⟨h1, h2, h3, h4, ⟨_, h5, a1⟩, h6⟩ := H
  have a2 := ⟨_, h5, a1.defeq sorry, _, _, a1.parRedS, .rfl, .refl .sort⟩
  have ⟨_, _, h3', _⟩ := h3
  ⟨h1.isType, .refl h3'.hasType.2, a2, a2, ⟨_, .sort, .rfl⟩, R.isType H⟩

theorem LogRelBase.DefEq.mono_r {R : LogRel Γ n}
    (le : m ≤ m') : R.DefEq M N A m' a u → R.DefEq M N A m a u
  | ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1.mono_l le, h2, h3, h4, h5, R.mono'_r h1 le h6⟩

theorem LogRelBase.DefEq.mono_l {R : LogRel Γ n}
    (ha : a ≤ a') (ht' : m.HasType a')
    (hA : R.DefEq A A (.sort u) a' .sort u.succ) : R.DefEq M N A m a u → R.DefEq M N A m a' u
  | ⟨ht, h2, h3, h4, h5, h6⟩ => ⟨ht', h2, h3, h4, h5, R.mono'_l_1 ht ha hA h6⟩

theorem LogRelBase.DefEq.left {R : LogRel Γ n} : R.DefEq M N A m a u → R.DefEq M M A m a u
  | ⟨h1, ⟨a1, _, _, a2, _, a3⟩, h3, _, h5, h6⟩ =>
    ⟨h1, ⟨a1.hasType.1, _, _, a2, a2, .refl a3.defeq.hasType.1⟩, h3, h3, h5, R.left h6⟩

theorem LogRelBase.DefEq.symm {R : LogRel Γ n} : R.DefEq M N A m a u → R.DefEq N M A m a u
  | ⟨h1, ⟨a1, _, _, a2, a3, a4⟩, h3, h4, h5, h6⟩ =>
    ⟨h1, ⟨a1.symm, _, _, a3, a2, a4.symm⟩, h4, h3, h5, R.symm h6⟩

theorem LogRelBase.DefEq.trans {R : LogRel Γ n} :
    R.DefEq M₁ M₂ A m a u → R.DefEq M₂ M₃ A m a v → u = v ∧ R.DefEq M₁ M₃ A m a u
  | ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩ => by
    cases a5.determ .sort b5 .sort
    exact ⟨rfl, a1, a2.trans b2, a3, b4, a5, R.trans a6 b6⟩

theorem LogRelBase.DefEq.trans_sort {R : LogRel Γ n} :
    R.DefEq M₁ M₂ (.sort u) m a u.succ → R.DefEq M₂ M₃ (.sort v) m a v.succ →
    u = v ∧ R.DefEq M₁ M₃ (.sort u) m a u.succ
  | ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩ => by
    cases a4.sort.determ .sort b3.sort .sort
    exact ⟨rfl, a1, a2.trans b2, a3, b4, a5, R.trans a6 b6⟩

theorem LogRelBase.DefEq.defeqDF {R : LogRel Γ n}
    (hA : R.DefEq A B (.sort u) a .sort u.succ) : R.DefEq M N A m a u → R.DefEq M N B m a u
  | ⟨ht, h2, h3, h4, _, h6⟩ =>
    let ⟨_, a2, _, a4, _⟩ := hA
    ⟨ht, h2.defeqDF a2.defeq, h3.defeqDF a2, h4.defeqDF a2, a4.sort, R.defeqDF hA h6⟩

theorem LogRelBase.DefEq.defeqL {R : LogRel Γ n}
    (H : Γ ⊢ M ≫≪ M' : A) : R.DefEq M N A m a u → R.DefEq M' N A m a u
  | ⟨ht, h2, h3, h4, h5, h6⟩ =>
    ⟨ht, H.symm.trans h2, sorry, h4, h5, R.defeqL H h6⟩

theorem LogRelBase.DefEq.defeqLL {R : LogRel Γ n}
    (H1 : Γ ⊢ M ≫≪ M' : A) (H2 : Γ ⊢ N ≫≪ N' : A)
    (H3 : R.DefEq M N A m a u) : R.DefEq M' N' A m a u :=
   H3.defeqL H1 |>.symm.defeqL H2 |>.symm

theorem LogRel.mono_l {R : LogRel Γ n}
    (ht : m.HasType a) (hA : R.DefEq A A (.sort u) a' .sort u.succ) (ha : a ≤ a') :
    R.DefEq M N A m a u ↔ R.DefEq M N A m a' u :=
  ⟨.mono_l ha (.mono_r ha hA.1 ht) hA, fun ⟨_, h2, h3, h4, h5, h6⟩ =>
    ⟨ht, h2, h3, h4, h5, R.mono'_l_2 ht ha h6⟩⟩

-- inductive TypeEq1 (TypeEq : ∀ Γ A B, LogRel Γ A B n) {Γ A B j} :
--     SExpr → SExpr → Classifier Γ A B n → Prop
--   | sort : TypeEq1 TypeEq (.sort u) (.sort u) {
--       DefEq' a b p := ∃ C, ((TypeEq Γ a b).R p).TypeEq' u j C
--       mono' := sorry }
--   -- | forallE : TypeEq1 TypeEq (.forallE u) (.forallE u) {
--   --     DefEq' p a b := ∃ C, (TypeEq Γ p a b).TypeEq' u j C }

-- def LogRelK.bot : LogRelK Γ A B k :=
--   fun _ C => C = ⟨fun _ _ _ => True, fun _ _ => trivial⟩

-- -- def LogRelK.false : LogRelK Γ A B n := { TypeEq' _ _ _ := False, mono' := nofun }

-- def LogRelK.sort (IH : ∀ Γ A B, LogRel Γ A B n) : LogRelK Γ A B (n := n+1) .sort :=
--   fun _ C => ∃ v, WHRedS Γ A (.sort v) ∧ WHRedS Γ B (.sort v) ∧ C = {
--     DefEq' a b p := ∃ C, ∃ q : Shape n, p ≤ q.lift ∧ (IH Γ a b).TypeEq' q v C
--     mono' le := fun ⟨_, _, h1, h2⟩ => ⟨_, _, Shape.LE.trans le h1, h2⟩ }
--   -- mono' le := by
--   --   rintro ⟨_, h1, h2, rfl⟩; refine ⟨_, ⟨_, h1.mono le, h2.mono le, rfl⟩, ?_⟩
--   --   intro _ _ _ ⟨_, _, h3, h4⟩
--   --   let ⟨_, a1, _⟩ := ((TypeEq ..).R _).mono' le h4; exact ⟨_, _, h3, a1⟩

-- def LogRelK.forallE (IH : ∀ Γ A B, LogRel Γ A B n)
--     (kA : Shape n) (kB : ShapeFun n) : LogRelK Γ A B (n := n + 1) (.forallE kA kB) :=
--   fun _ C => ∃ A₁ A₂ B₁ B₂ CA, ∃ CB : ∀ _ _ _, _,
--     WHRedS Γ A (.forallE A₁ A₂) ∧ WHRedS Γ B (.forallE B₁ B₂) ∧
--     (IH Γ A₁ B₁).TypeEq kA CA ∧
--     (∀ a b p, CA.DefEq a b p → (IH (A₁::Γ) A₂ B₂).TypeEq (kB.app p) (CB a b p)) ∧
--     C = {
--       DefEq' f g p := ∀ a b p', CA.DefEq a b p' → (CB a b p').DefEq (f.app a) (g.app b) (p.app p')
--       mono' le H a b p' h1 := (H a b p' h1).mono (Shape.app_mono_l le _) }

omit [Params] in
theorem pull_exists {a : Prop} {p : α → Prop} (z : α) : (a → ∃ b, p b) ↔ ∃ b, a → p b := by
  refine ⟨fun H => ?_, fun ⟨_, h⟩ a => ⟨_, h a⟩⟩
  by_cases h : a <;> simp [h] <;> [exact H h; exact ⟨z, trivial⟩]

def TypeEq0.DefEqTy (Γ : List SExpr) (M N : SExpr) (l : SLevel) (m : Shape 0) : Prop :=
  match m with
  | .bot => True
  | .sort => ∃ u, l = u.succ ∧ WHRedS Γ M (.sort u) ∧ WHRedS Γ N (.sort u)

def TypeEqS.DefEqTy (IH : LogRel Γ n)
    (Γ : List SExpr) (M N : SExpr) (l : SLevel) (m : Shape (n+1)) : Prop :=
  match m with
  | .bot => True
  | .sort => ∃ u, l = u.succ ∧ WHRedS Γ M (.sort u) ∧ WHRedS Γ N (.sort u)
  | .forallE m₁ m₂ =>
    ∃ M₁ M₂ N₁ N₂, WHRedS Γ M (.forallE M₁ M₂) ∧ WHRedS Γ N (.forallE N₁ N₂) ∧
    ∃ u v, l = u.imax v ∧ IH.DefEq M₁ N₁ (.sort u) m₁ .sort u.succ ∧
    (∀ {{a b p}}, IH.DefEq a b M₁ p m₁ u →
      IH.DefEq (M₂.inst a) (M₂.inst b) (.sort v) (ShapeFun.app m₂ p) .sort v.succ ∧
      IH.DefEq (N₂.inst a) (N₂.inst b) (.sort v) (ShapeFun.app m₂ p) .sort v.succ) ∧
    (∀ {{a p}}, IH.DefEq a a M₁ p m₁ u →
      IH.DefEq (M₂.inst a) (N₂.inst a) (.sort v) (ShapeFun.app m₂ p) .sort v.succ)
  | _ => False

def TypeEqS.DefEqForall (IH : LogRel Γ n) (M N A₁ A₂ : SExpr) (m : Shape (n+1))
    (a₁ : Shape n) (a₂ : ShapeFun n) (u v : SLevel) : Prop :=
  match m with
  | .bot => True
  | .lam m =>
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ u →
      IH.DefEq (M.inst a) (M.inst b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) v ∧
      IH.DefEq (N.inst a) (N.inst b) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) v) ∧
    (∀ {{a p}}, IH.DefEq a a A₁ p a₁ u →
      IH.DefEq (M.inst a) (N.inst a) (A₂.inst a) (ShapeFun.app m p) (ShapeFun.app a₂ p) v)
  | _ => False

def TypeEqS.DefEq' (IH : LogRel Γ n) (M N A : SExpr) (m a : Shape (n+1))
    (l : SLevel) : Prop :=
  match a with
  | .bot => True
  | .sort => ∃ u, l = u.succ ∧ WHRedS Γ A (.sort u) ∧ DefEqTy IH Γ M N u m
  | .forallE a₁ a₂ => ∃ A₁ A₂ u v, l = u.imax v ∧ WHRedS Γ A (.forallE A₁ A₂) ∧
    IH.DefEq A₁ A₁ (.sort u) a₁ .sort u.succ ∧ A₁::Γ ⊢ A₂ ▷* sort v ∧
    (∀ {{a b p}}, IH.DefEq a b A₁ p a₁ u →
      IH.DefEq (A₂.inst a) (A₂.inst b) (.sort v) (ShapeFun.app a₂ p) .sort v.succ) ∧
    DefEqForall IH M N A₁ A₂ m a₁ a₂ u v
  | _ => False

def TypeEq0.DefEq' (Γ : List SExpr) (M N A : SExpr) (m a : Shape 0) (l : SLevel) : Prop :=
  match a with
  | .bot => True
  | .sort => ∃ u, l = u.succ ∧ WHRedS Γ A (.sort u) ∧ DefEqTy Γ M N u m

def TypeEq0 : LogRel Γ 0 := by
  refine {
    DefEq' := TypeEq0.DefEq' Γ
    isType {M N A m a u} h1 := ?_
    left {M N A m a u} h1 := ?_
    symm {M N A m a u} h1 := ?_
    trans {M₁ M₂ A m a u M₃} := ?_
    defeqDF {A B u a M N m} hA := ?_
    defeqL {M M' A N m a u} := ?_
    mono'_r {m m' M N A a u} h1 := ?_
    mono'_l_1 {a a' A u M N m} h1 := ?_
    mono'_l_2 {a a' M N A m u} h1 := ?_ }
  · let ⟨h1, h2, h3, h4, h5, h6⟩ := h1
    simp [TypeEq0.DefEq'] at h6; split at h6
    · exact ⟨_, rfl, .rfl, trivial⟩
    · obtain ⟨v, rfl, h1, h2⟩ := h6; exact ⟨_, rfl, .rfl, _, rfl, h1, h1⟩
  · dsimp [TypeEq0.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h2, h3⟩ := h1; refine ⟨_, h1, h2, ?_⟩
      dsimp [TypeEq0.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h2, h3, _⟩ := h3; exact ⟨h1, h2, h3, h3⟩
  · dsimp [TypeEq0.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h2, h3⟩ := h1; refine ⟨_, h1, h2, ?_⟩
      dsimp [TypeEq0.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h2, h3, h4⟩ := h3; exact ⟨h1, h2, h4, h3⟩
  · dsimp [TypeEq0.DefEq']; split
    · simp
    · rintro ⟨_, rfl, a1, a2⟩ ⟨_, eq, -, b2⟩; cases SLevel.succ_inj eq; refine ⟨_, rfl, a1, ?_⟩
      revert a2 b2; dsimp [TypeEq0.DefEqTy]; split
      · simp
      · rintro ⟨_, rfl, a1, -⟩ ⟨_, eq, -, b2⟩; cases SLevel.succ_inj eq; refine ⟨_, rfl, a1, b2⟩
  · obtain ⟨A1, A2, A3, A4, A5, A6⟩ := hA
    dsimp [TypeEq0.DefEq']; split
    · simp
    · rintro ⟨u, rfl, a1, a2⟩
      exact ⟨_, rfl, A2.symm.trans (a1.crDefEq A2.1.hasType.1) |>.reduce_sort, a2⟩
  · sorry
  · sorry
  · sorry
  · sorry

def TypeEqS (IH : LogRel Γ n) : LogRel Γ (n + 1) := by
  refine {
    DefEq' := TypeEqS.DefEq' IH
    isType {M N A m a u} h1 := ?_
    left {M N A m a u} h1 := ?_
    symm {M N A m a u} h1 := ?_
    trans {M₁ M₂ A m a u M₃} := ?_
    defeqDF {A B u a M N m} hA := ?_
    defeqL {M M' A N m a u} := ?_
    mono'_r {m m' M N A a u} h1 := ?_
    mono'_l_1 {a a' A u M N m} h1 := ?_
    mono'_l_2 {a a' M N A m u} h1 := ?_ }
  · let ⟨h1, h2, h3, h4, h5, h6⟩ := h1
    simp [TypeEqS.DefEq'] at h6; split at h6
    · exact ⟨_, rfl, .rfl, trivial⟩
    · obtain ⟨v, rfl, h1, h2⟩ := h6; exact ⟨_, rfl, .rfl, _, rfl, h1, h1⟩
    · obtain ⟨_, _, _, _, rfl, h1, h2, _, h4, _⟩ := h6
      exact ⟨_, rfl, .rfl, _, _, _, _, h1, h1, _, _, rfl, h2,
        fun _ _ _ a1 => ⟨h4 a1, h4 a1⟩, fun _ _ a1 => h4 a1⟩
    · cases h6
  · dsimp [TypeEqS.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h2, h3⟩ := h1; refine ⟨_, h1, h2, ?_⟩
      dsimp [TypeEqS.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h2, h3, _⟩ := h3; exact ⟨h1, h2, h3, h3⟩
      · let ⟨_, _, _, _, h1, h2, _, _, h3, h4, h5, h6⟩ := h3
        exact ⟨_, _, _, _, h1, h1, _, _, h3, h4.left,
          fun a b p a1 => ⟨(h5 a1).1, (h5 a1).1⟩, fun a p a1 => (h5 a1).1⟩
      · cases h3
    · let ⟨_, _, _, _, h1, h2, h3, h4, h5, h6⟩ := h1; refine ⟨_, _, _, _, h1, h2, h3, h4, h5, ?_⟩
      dsimp [TypeEqS.DefEqForall] at h6 ⊢; split at h6
      · trivial
      · exact ⟨fun a b p a1 => ⟨(h6.1 a1).1, (h6.1 a1).1⟩, fun a p a1 => (h6.1 a1).1⟩
      · cases h6
    · cases h1
  · dsimp [TypeEqS.DefEq'] at h1 ⊢; split at h1
    · trivial
    · let ⟨_, h1, h2, h3⟩ := h1; refine ⟨_, h1, h2, ?_⟩
      dsimp [TypeEqS.DefEqTy] at h3 ⊢; split at h3
      · trivial
      · let ⟨h1, h2, h3, h4⟩ := h3; exact ⟨h1, h2, h4, h3⟩
      · let ⟨B, F, B', F', h1, h2, _, _, h3, h4, h5, h6⟩ := h3
        refine ⟨_, _, _, _, h2, h1, _, _, h3, h4.symm, ?_, ?_⟩
        · exact fun a b p a1 => (h5 (.defeqDF h4.symm a1)).symm
        · exact fun a p a1 => (h6 (.defeqDF h4.symm a1)).symm
      · cases h3
    · let ⟨_, _, _, _, h1, h2, h3, h4, h5, h6⟩ := h1; refine ⟨_, _, _, _, h1, h2, h3, h4, h5, ?_⟩
      dsimp [TypeEqS.DefEqForall] at h6 ⊢; split at h6
      · trivial
      · exact ⟨fun a b p a1 => (h6.1 a1).symm, fun a p a1 => (h6.2 a1).symm⟩
      · cases h6
    · cases h1
  · dsimp [TypeEqS.DefEq']; split
    · simp
    · rintro ⟨_, rfl, a1, a2⟩ ⟨_, eq, -, b2⟩; cases SLevel.succ_inj eq; refine ⟨_, rfl, a1, ?_⟩
      revert a2 b2; dsimp [TypeEqS.DefEqTy]; split
      · simp
      · rintro ⟨_, rfl, a1, -⟩ ⟨_, eq, -, b2⟩; cases SLevel.succ_inj eq; refine ⟨_, rfl, a1, b2⟩
      · rintro ⟨_, _, _, _, a1', a2, _, _, rfl, a4, a5, a6⟩
               ⟨_, _, _, _, b1, b2, _, _, _, b4, b5, b6⟩
        cases a2.determ .forallE b1 .forallE
        obtain ⟨rfl, c4⟩ := a4.trans_sort b4
        refine ⟨_, _, _, _, a1', b2, _, _, rfl, c4, fun _ _ _ c1 => ?_, fun _ _ c1 => ?_⟩ <;>
          obtain ⟨rfl, -⟩ := (a5 c1).2.symm.trans_sort (b5 (.defeqDF a4 c1)).1
        · exact ⟨(a5 c1).1, (b5 (.defeqDF a4 c1)).2⟩
        · exact ((a6 c1).trans (b6 (.defeqDF a4 c1))).2
      · nofun
    · rintro ⟨_, _, _, _, rfl, a1, a2, a3, a4, a5⟩ ⟨_, _, _, _, -, b1, b2, b3, b4, b5⟩
      cases a1.determ .forallE b1 .forallE
      obtain ⟨rfl, -⟩ := a2.trans_sort b2
      cases a3.determ .sort b3 .sort
      refine ⟨_, _, _, _, rfl, a1, a2, a3, a4, ?_⟩
      revert a5 b5; dsimp [TypeEqS.DefEqForall]; split
      · simp
      · intro ⟨a5, a6⟩ ⟨b5, b6⟩
        exact ⟨fun _ _ _ c1 => ⟨(a5 c1).1, (b5 c1).2⟩, fun _ _ c1 => (a6 c1).trans (b6 c1) |>.2⟩
      · nofun
    · nofun
  · obtain ⟨A1, A2, A3, A4, A5, A6⟩ := hA
    dsimp [TypeEqS.DefEq']; split
    · simp
    · rintro ⟨u, rfl, a1, a2⟩
      exact ⟨_, rfl, A2.symm.trans (a1.crDefEq A2.1.hasType.1) |>.reduce_sort, a2⟩
    · rintro ⟨_, _, _, _, rfl, a1, a2, a3, a4, a5⟩
      have H := A2.symm.trans (a1.crDefEq A2.1.hasType.1)
      have ⟨_, _, b1⟩ := H.reduce_forallE
      have ⟨b2, b3⟩ := H.symm.trans (b1.crDefEq H.1.hasType.1)
        |>.forallE_inv a2.2.1.defeq a3.hasType
      exact ⟨_, _, _, _, rfl, b1, a2.defeqLL b2 b2, sorry, sorry, sorry⟩
      -- cases a1.determ .forallE b1 .forallE
      -- obtain ⟨rfl, -⟩ := a2.trans_sort b2
      -- cases a3.determ .sort b3 .sort
      stop
      refine ⟨_, _, _, _, rfl, a1, a2, a3, a4, ?_⟩
      revert a5 b5; dsimp [TypeEqS.DefEqForall]; split
      · simp
      · intro ⟨a5, a6⟩ ⟨b5, b6⟩
        exact ⟨fun _ _ _ c1 => ⟨(a5 c1).1, (b5 c1).2⟩, fun _ _ c1 => (a6 c1).trans (b6 c1) |>.2⟩
      · nofun
    · nofun
  stop
  · cases h1.unfold with
    | bot => simp [Shape.le_bot]; rintro rfl; exact id
    | sort =>
      cases m <;> simp [Shape.LE.def]
      · exact fun ⟨_, h1, h2, _⟩ => ⟨_, h1, h2, trivial⟩
      · exact id
    | @forallE n m₁' m₂' =>
      cases m with (rw [Shape.LE.def]; simp)
      | bot => exact fun ⟨_, h1, h2, _⟩ => ⟨_, h1, h2, trivial⟩
      | forallE m₁ m₂ =>
        rintro h1 h2 ⟨_, rfl, h3, M₁, M₂, N₁, N₂, h4, h5, _, _, rfl, h6, h7⟩
        refine ⟨_, rfl, h3, _, _, _, _, h4, h5, _, _, rfl, h6.mono_r h1, fun _ _ _ a1 => ?_⟩
        exact (h7 (.mono_r h1 (.mono_r h1 h6.1 a1.1) _ a1)).mono_r (ShapeFun.app_mono_l h2 _)
    | @lam _ f' a₁ a₂ h2 =>
      cases m with (rw [Shape.LE.def]; simp)
      | bot =>
        rintro ⟨_, _, _, _, rfl, h1, h3, h4, h5, _⟩
        exact ⟨_, _, _, _, rfl, h1, h3, h4, h5, trivial⟩
      | lam f =>
        rintro h1 ⟨_, _, _, _, rfl, h3, h4, h5, h6, h7⟩
        refine ⟨_, _, _, _, rfl, h3, h4, h5, h6, fun _ _ _ a1 => ?_⟩
        exact (h7 a1).mono_r (ShapeFun.app_mono_l h1 _)
  · cases h1.unfold with
    | bot h2 =>
      simp [Shape.LE.def]; split
      · rintro - ⟨h1, -, h3⟩ -
        cases a' with
        | bot => trivial
        | sort =>
          simp [TypeEqS.DefEq', TypeEqS.DefEqTy]
          done

      · exact fun _ => id
      · rintro ⟨h1, h2⟩ ⟨_, _, h3, ⟨_, h4⟩, ⟨_, h5, h6⟩, h7⟩
        refine ⟨_, _, h3, ⟨_, h4.mono_r h1⟩, ⟨_, h5, fun a b p a1 => ?_⟩, trivial⟩
        exact (h6 (a1.mono_l h1)).mono_r (ShapeFun.app_mono_l h2 _)
      · nofun
      · nofun
    | sort | forallE => cases a' <;> simp [Shape.LE.def]; exact id
    | @lam _ a₁ a₂ f' b1 b2 b3 =>
      cases a' <;> simp [Shape.LE.def]
      intro h1 h2 ⟨_, _, h3, ⟨_, h4⟩, ⟨_, h5, h6⟩, h7⟩
      refine ⟨_, _, h3, ⟨_, h4.mono_r h1⟩, ⟨_, h5, fun a b p a1 => ?_⟩, fun a b p a1 => ?_⟩
      · exact (h6 (a1.mono_l h1)).mono_r (ShapeFun.app_mono_l h2 _)
      · exact (IH _).mono_l (Shape.HasType.lam_app b3 a1.1) (ShapeFun.app_mono_l h2 _)
          |>.2 (h7 (a1.mono_l h1))
  · --rintro h0
    cases h1.unfold with
    | bot =>
      simp [Shape.LE.def]; split
      · exact fun _ _ => trivial
      · exact fun _ => id
      · rintro ⟨h1, h2⟩ ⟨_, _, _, _, rfl, a1, a2, a3, a4, a5⟩
        refine ⟨_, _, _, _, rfl, a1, a2.mono_r h1, a3, fun a b p b1 => ?_, trivial⟩
        exact (a4 (b1.mono_l h1 (.mono_r h1 a2.1 b1.1))).mono_r (ShapeFun.app_mono_l h2 _)
      · nofun
      · nofun
    | sort | forallE => cases a' <;> simp [Shape.LE.def]; exact id
    | lam _ _ c3 =>
      cases a' <;> simp [Shape.LE.def]
      rintro h1 h2 ⟨_, _, _, _, rfl, a1, a2, a3, a4, a5⟩
      refine ⟨_, _, _, _, rfl, a1, a2.mono_r h1, a3, fun a b p b1 => ?_, fun a b p b1 => ?_⟩
        <;> have b1' := b1.mono_l h1 (.mono_r h1 a2.1 b1.1)
      · exact (a4 b1').mono_r (ShapeFun.app_mono_l h2 _)
      · exact (IH _).mono_l (Shape.HasType.lam_app c3 b1.1)
          (a4 b1').1 (ShapeFun.app_mono_l h2 _) |>.2 (a5 b1')
  · exact (⟨_, .rfl, ·⟩)
  · rintro u C h1 h2 ⟨A₁, A₂, B₁, B₂, CA, CB, h3, h4, h5, h6, rfl⟩
    let ⟨CA', a1, a2⟩ := h5.mono h1
    have this a b p h := (h6 a b p h).mono (ShapeFun.app_mono_l h2 _)
    conv at this => enter [a, b, p]; rw [pull_exists Classifier.true]
    simp only [Classical.skolem] at this; let ⟨CB', (hf : ∀ a b p, _)⟩ := this; clear this h6
    refine ⟨_, _, _, _, _, _, _, CB', h3, h4, a2, fun a b p h => by
      refine (hf _ _ _ _).2
      done
      , rfl⟩
    simp

def TypeEq (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => TypeEq0
  | _+1 => TypeEqS (TypeEq Γ)
