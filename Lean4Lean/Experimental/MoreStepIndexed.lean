import Lean4Lean.Experimental.SExpr

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

def CheckType (Γ : List SExpr) (e A : SExpr) : Prop :=
  ∃ A', InferType Γ e A' ∧ ∃ u, CRDefEq Γ A A' (.sort u)
def CheckTypeN (Γ : List SExpr) (e A : SExpr) (n : Nat) : Prop :=
  ∃ A', InferTypeN Γ e A' n ∧ CRDefEqN Γ A A' n

theorem CheckTypeN.mono : n ≤ n' → CheckTypeN Γ e e' n → CheckTypeN Γ e e' n'
  | h1, ⟨_, h2, h3⟩ => ⟨_, h2.mono h1, h3.mono h1⟩

-- structure Classifier.OK (C : Classifier Γ A) (n : Nat) : Prop where
--   HasTy_below : C.HasTy x i → i < n

inductive ShapeS (Shape : Type) (n : Nat) : Type where
  | bot : ShapeS Shape n
  | sort : ShapeS Shape n
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape n
  | lam : List (Shape × Shape) → ShapeS Shape n

def Shape : Nat → Type
  | 0 => Unit -- bottom
  | n + 1 => ShapeS (Shape n) n

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => ()
  | _+1 => ShapeS.bot

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
  | _+1, .sort .., .sort .. => true
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _, _, _ => false

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, _, _ | _+1, .bot, _ => true
  | _+1, .sort, .sort => True --j ≤ i
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
  | zero => rfl
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n m}, Shape n → Shape m
  | 0, _, _ | _, 0, _ | _+1, _, .bot => .bot
  | _+1, _m+1, .sort => .sort -- h : i ≤ m then .sort i h else .bot
  | _+1, _+1, .forallE s f => .forallE (lift s) <| ShapeFun.lift lift f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift lift f

omit [Params] in
@[simp] theorem Shape.lift_bot : ((Shape.bot : Shape n).lift : Shape m) = Shape.bot := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in
theorem Shape.lift_self {s : Shape n} : s.lift = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl) <;> dsimp
  -- · rw [dif_pos ‹_›]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]

omit [Params] in
theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    ((s.lift : Shape n₂).lift : Shape n₃) = s.lift := by
  induction n₁ generalizing n₂ n₃ with
  | zero => rw [show s = .bot from rfl]; simp
  | succ n₁ ih =>
    cases n₃ with | zero => rfl | succ n₃
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
  | zero => cases m <;> rfl
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
  | zero => simp [show s = .bot by rfl, show t = .bot by rfl]; exact fun _ => Shape.LE.rfl
  | succ n ih =>
    cases m with | zero => intro; rfl | succ m; specialize @ih m
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
  | zero => exact fun _ _ => rfl
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
  | _+1, .sort, .sort => .sort -- (max i j) (by omega)
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

def Shape.HasType : ∀ {n}, Shape n → Shape n → Prop
  | 0, _, _ | _+1, .bot, _ => True
  | _+1, .sort .., .sort .. => True -- ? ∃ q : Shape i, p ≤ q.lift
  | _+1, .forallE _a _b, .sort .. => True -- ? ∃ q : Shape i, p ≤ q.lift
  | _, _, _ => False

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

def Classifier.DefEq (C : Classifier Γ A B (n := n) k) (a b : SExpr) (p : Shape n) : Prop :=
  CheckType Γ a A ∧ CheckType Γ b B ∧ CRDefEq Γ a b A ∧ C.DefEq' a b p

theorem Classifier.DefEq.mono {C : Classifier Γ A B k}
    (le : p ≤ p') : C.DefEq a b p' → C.DefEq a b p
  | ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, C.mono' le h4⟩

structure Classifier.LE (C C' : Classifier Γ A B k) : Prop where
  mono' : C.DefEq' a b p → C'.DefEq' a b p
  mono'_r : C.DefEq' a b p → C'.DefEq' a b p
instance : LE (Classifier Γ A B n) := ⟨Classifier.LE⟩

theorem Classifier.LE.rfl {C : Classifier Γ A B n} : C ≤ C where
  mono' := id
  mono'_r := id

theorem Classifier.LE.mono {C C' : Classifier Γ A B n} (H : C ≤ C') :
    C.DefEq a b p → C'.DefEq a b p
  | ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, H.mono' h4⟩

-- structure LogRelK (Γ : List SExpr) (A B : SExpr) (n : Nat) where
--   TypeEq' (u : SLevel) : Classifier Γ A B n → Prop
abbrev LogRelK (Γ : List SExpr) (A B : SExpr) (k : Shape n) :=
  SLevel → Classifier Γ A B k → Prop

structure LogRel (Γ : List SExpr) (A B : SExpr) (n : Nat) where
  TypeEq' (k : Shape n) : LogRelK Γ A B k
  mono' : k ≤ k' → TypeEq' k' u C' → ∃ C ≥ C', TypeEq' k u C

def LogRel.TypeEq (R : LogRel Γ A B n) (k : Shape n) (C : Classifier Γ A B k) : Prop :=
  ∃ u, InferType Γ A (.sort u) ∧ InferType Γ B (.sort u) ∧
    CRDefEq Γ A B (.sort u) ∧ R.TypeEq' k u C

theorem LogRel.TypeEq.mono {R : LogRel Γ A B n} (le : k ≤ k') :
    R.TypeEq k' C' → ∃ C ≥ C', R.TypeEq k C
  | ⟨_, h1, h2, h3, h4⟩ => let ⟨_, a1, a2⟩ := R.mono' le h4; ⟨_, a1, _, h1, h2, h3, a2⟩

-- inductive TypeEq1 (TypeEq : ∀ Γ A B, LogRel Γ A B n) {Γ A B j} :
--     SExpr → SExpr → Classifier Γ A B n → Prop
--   | sort : TypeEq1 TypeEq (.sort u) (.sort u) {
--       DefEq' a b p := ∃ C, ((TypeEq Γ a b).R p).TypeEq' u j C
--       mono' := sorry }
--   -- | forallE : TypeEq1 TypeEq (.forallE u) (.forallE u) {
--   --     DefEq' p a b := ∃ C, (TypeEq Γ p a b).TypeEq' u j C }

def LogRelK.bot : LogRelK Γ A B k :=
  fun _ C => C = ⟨fun _ _ _ => True, fun _ _ => trivial⟩

-- def LogRelK.false : LogRelK Γ A B n := { TypeEq' _ _ _ := False, mono' := nofun }

def LogRelK.sort (IH : ∀ Γ A B, LogRel Γ A B n) : LogRelK Γ A B (n := n+1) .sort :=
  fun _ C => ∃ v, WHRedS Γ A (.sort v) ∧ WHRedS Γ B (.sort v) ∧ C = {
    DefEq' a b p := ∃ C, ∃ q : Shape n, p ≤ q.lift ∧ (IH Γ a b).TypeEq' q v C
    mono' le := fun ⟨_, _, h1, h2⟩ => ⟨_, _, Shape.LE.trans le h1, h2⟩ }
  -- mono' le := by
  --   rintro ⟨_, h1, h2, rfl⟩; refine ⟨_, ⟨_, h1.mono le, h2.mono le, rfl⟩, ?_⟩
  --   intro _ _ _ ⟨_, _, h3, h4⟩
  --   let ⟨_, a1, _⟩ := ((TypeEq ..).R _).mono' le h4; exact ⟨_, _, h3, a1⟩

def LogRelK.forallE (IH : ∀ Γ A B, LogRel Γ A B n)
    (kA : Shape n) (kB : ShapeFun n) : LogRelK Γ A B (n := n + 1) (.forallE kA kB) :=
  fun _ C => ∃ A₁ A₂ B₁ B₂ CA, ∃ CB : ∀ _ _ _, _,
    WHRedS Γ A (.forallE A₁ A₂) ∧ WHRedS Γ B (.forallE B₁ B₂) ∧
    (IH Γ A₁ B₁).TypeEq kA CA ∧
    (∀ a b p, CA.DefEq a b p → (IH (A₁::Γ) A₂ B₂).TypeEq (kB.app p) (CB a b p)) ∧
    C = {
      DefEq' f g p := ∀ a b p', CA.DefEq a b p' → (CB a b p').DefEq (f.app a) (g.app b) (p.app p')
      mono' le H a b p' h1 := (H a b p' h1).mono (Shape.app_mono_l le _) }

omit [Params] in
theorem pull_exists {a : Prop} {p : α → Prop} (z : α) : (a → ∃ b, p b) ↔ ∃ b, a → p b := by
  refine ⟨fun H => ?_, fun ⟨_, h⟩ a => ⟨_, h a⟩⟩
  by_cases h : a <;> simp [h] <;> [exact H h; exact ⟨z, trivial⟩]

#exit
def TypeEqS (IH : ∀ Γ A B, LogRel Γ A B n) : LogRel Γ A B (n + 1) := by
  refine {
    TypeEq'
    | .bot => LogRelK.bot
    | .sort => .sort IH
    | .forallE kA kB => .forallE IH kA kB
    | _ => fun _ _ => False
    mono' {k k'} := ?_ }
  rw [Shape.LE.def]; split <;> simp
  · rintro u C -; exact ⟨_, ⟨fun _ => trivial⟩, rfl⟩
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

def TypeEq (Γ : List SExpr) (A B : SExpr) : LogRel Γ A B n :=
  match n with
  | 0 => { R _ := .bot, mono' _ h := h }
  | _+1 => TypeEqS fun _ _ => TypeEq
termination_by n
  -- {
  --   R
  --   | .bot => .bot
  --   | .sort n hn => {
  --     TypeEq' u j C := ∃ v, WHRedUpToN Γ A (.sort v) j ∧ WHRedUpToN Γ B (.sort v) j ∧ C = {
  --       DefEq' a b p := ∃ C, ((TypeEq Γ a b).R p).TypeEq' v j C,
  --       mono' le := fun ⟨C, h1⟩ => ⟨_, (TypeEq ..).mono' le h1⟩ }
  --     mono' le := by
  --       rintro ⟨_, h1, h2, rfl⟩; refine ⟨_, ⟨_, h1.mono le, h2.mono le, rfl⟩, ?_⟩
  --       intro _ h3 h4 ⟨_, h5⟩; let ⟨_, a1, _⟩ := ((TypeEq ..).R _).mono' le h5; exact ⟨_, a1⟩ }
  --   | .forallE kA kB => by
  --     refine { TypeEq' u j C := ?_, mono' := ?_ }
  --     · refine _
  --     done
  --         -- ?_
  --         -- match A', B' with
  --         -- | .sort v₁, .sort v₂ => v₁ = v₂ ∧ C = { DefEq' a b := ∃ C, (TypeEq Γ a b).TypeEq' v₁ j C }
  --         -- | .forallE A₁ F₁, .forallE A₂ F₂ =>
  --         --   ∃ CA CF, (TypeEq Γ A₁ A₂).TypeEq j CA ∧ (TypeEq (A₁::Γ) F₁ F₂).TypeEq j CF ∧
  --         --   ∀ u v, CA.DefEq u v → CF.DefEq (.app _ u)

  --     -- TypeEqS (TypeEq k) Γ A B


  --   | _ => .false
  --   mono' := sorry }
  -- | _+1, .sort n _ => by
  --   refine ⟨fun k u j C => ?_, ?_⟩
  --   · refine ∃ v, WHRedUpToN Γ A (.sort v) j ∧ WHRedUpToN Γ B (.sort v) j ∧
  --       C = { DefEq' p a b := ∃ C, (TypeEq Γ a b).TypeEq' v₁ j C }
  --       -- ?_
  --       -- match A', B' with
  --       -- | .sort v₁, .sort v₂ => v₁ = v₂ ∧ C = { DefEq' a b := ∃ C, (TypeEq Γ a b).TypeEq' v₁ j C }
  --       -- | .forallE A₁ F₁, .forallE A₂ F₂ =>
  --       --   ∃ CA CF, (TypeEq Γ A₁ A₂).TypeEq j CA ∧ (TypeEq (A₁::Γ) F₁ F₂).TypeEq j CF ∧
  --       --   ∀ u v, CA.DefEq u v → CF.DefEq (.app _ u)

  --   -- TypeEqS (TypeEq k) Γ A B
-- termination_by n
-- decreasing_by all_goals sorry

-- theorem TypeEq.mono : k ≤ k' → TypeEq k' Γ A B ≤ TypeEq k Γ A B := sorry
