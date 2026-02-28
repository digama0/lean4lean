/-!
# Partial formalization of Coquand & Huber, "An Adequacy Theorem for Dependent Type Theory"
https://doi.org/10.1007/s00224-018-9879-9

This might be useful for others, I just wanted to make sure I understood
the monotonicity theorem right.
-/

axiom mySorry : α

axiom D : Type
axiom DF.OK (f : D → D) : Prop
def DF : Type := { f : D → D // DF.OK f }

noncomputable instance : CoeFun DF fun _ => D → D := ⟨(·.1)⟩

def DF.comp (f g : DF) : DF := ⟨fun x => f (g x), mySorry⟩

axiom D.bot : D
axiom D.U : D
axiom D.lam : DF → D
axiom D.pi : D → DF → D
axiom D.LE : D → D → Prop

instance : LE D := ⟨D.LE⟩
instance : LE DF := ⟨fun f g => ∀ x, f x ≤ g x⟩

axiom D.LE.antisymm {x y : D} : x ≤ y → y ≤ x → x = y
axiom D.LE.trans {x y z : D} : x ≤ y → y ≤ z → x ≤ z

theorem DF.LE.trans {x y z : DF} : x ≤ y → y ≤ z → x ≤ z := fun h1 h2 _ => (h1 _).trans (h2 _)
axiom DF.mono {f : DF} : x ≤ y → f x ≤ f y

noncomputable def DF.bot : DF := .mk (fun _ => .bot) mySorry
@[simp] theorem DF.bot_val : DF.bot.1 x = .bot := rfl

axiom D.lam_bot : D.lam .bot = .bot

axiom D.app : D → D → D
noncomputable instance : CoeFun D fun _ => D → D := ⟨.app⟩
axiom D.app_lam : D.lam f x = f x

axiom D.LE.bot {x : D} : .bot ≤ x
theorem DF.LE.bot {x : DF} : .bot ≤ x := fun _ => .bot
axiom D.LE.rfl {x : D} : x ≤ x
axiom D.LE.lam {x y : DF} : D.lam x ≤ .lam y ↔ x ≤ y
axiom D.LE.pi {x y : D} : D.pi x f ≤ D.pi y g ↔ x ≤ y ∧ f ≤ g

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

axiom Shape.embed : Shape n → D
axiom ShapeFun.embed : ShapeFun n → DF
noncomputable instance : CoeOut (Shape n) D := ⟨Shape.embed⟩
noncomputable instance : CoeOut (ShapeFun n) DF := ⟨ShapeFun.embed⟩

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

axiom D.LE.embed {x y : Shape n} : Shape.embed x ≤ Shape.embed y ↔ x ≤ y
axiom DF.LE.embed {x y : ShapeFun n} : ShapeFun.embed x ≤ ShapeFun.embed y ↔ x ≤≤ y

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

-- @[simp] axiom FinElem.embed_bot : ((.bot : FinElem) : D) = .bot
-- @[simp] axiom FinFun.embed_bot : ((.bot : FinFun) : DF) = .bot
@[simp] axiom Shape.embed_U : (Shape.U (n := n) : D) = .U
-- def FinElem.LE_unfold : FinElem → FinElem → Prop
--   | .bot, _ => True
--   | .U, .U => True
--   | .pi x f, .pi y g => x ≤ y ∧ f ≤ g
--   | .lam f, .lam g => f ≤ g
--   | .lam f, .bot => f ≤ .bot
--   | _, _ => False

-- @[simp] theorem FinMut.LE.lam {x y : FinFun} : x.lam ≤ y.lam ↔ x ≤ y := sorry
-- @[simp] theorem FinMut.LE.pi {x y : FinElem} : x.pi f ≤ y.pi g ↔ x ≤ y ∧ f ≤ g := sorry
-- axiom FinMut.LE.cons : FinMut.cons u v f ≤ g ↔ v ≤ g u ∧ f ≤ g
-- axiom eval_cons : FinMut.cons u v f x ≤ y ↔ (u ≤ x → v ≤ y) ∧ f x ≤ y
-- @[simp] axiom eval_embed : ((f : FinFun) x : D) = (f : DF) x
-- @[simp] axiom bot_apply : (.bot : FinFun) x = .bot

-- inductive FinHasTypeK : Bool → Type
--   | ty : FinElem → FinHasTypeK false
--   | pi (a : FinElem) : FinHasTypeK true
--   | lam (a : FinElem) (f : FinFun) : FinHasTypeK true

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n :=
  maxBelow (s.filter (·.1 ≤ a)) |>.2

theorem ShapeFun.app_mono_l {f f' : ShapeFun n} : f.LE f' → ∀ a, f.app a ≤ f'.app a :=
  sorry

theorem ShapeFun.app_mono_r {f : ShapeFun n} : a ≤ a' → f.app a ≤ f.app a' :=
  sorry

@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := sorry

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

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

theorem Shape.HasType.mono {m a a' : Shape n} (ha : a ≤ a') :
    m :ᶠ a → m :ᶠ a' := sorry

theorem Shape.HasTypeLam.app (H : HasTypeLam f a b) (ht : HasType x a) :
    HasType (ShapeFun.app f x) (ShapeFun.app b x) := sorry

theorem Shape.HasTypePi.app (H : HasTypePi f a)
    (ht : HasType x a) : HasType (ShapeFun.app f x) .U := sorry

theorem Shape.HasType.maximal
    (H : HasTypeLam f a b) (ha : a ≤ a') (ht : HasType x' a') :
    ∃ x, HasType x a ∧ x ≤ x' ∧ ShapeFun.app f x = ShapeFun.app f x' := sorry

axiom proj : D → DF
axiom proj_U_U : proj .U .U = .U
axiom proj_U_pi : proj .U (.pi a f) = .pi (proj .U a) ((proj .U).comp <| f.comp <| proj a)
axiom proj_pi : proj (.pi a f) (.lam w) =
  .lam (.mk (fun x => proj (f (proj a x)) (w (proj a x))) mySorry)

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
  | .pi A B => .pi (A.eval ρ) (.mk (fun u => B.eval (push ρ u (A.eval ρ))) mySorry)
  | .app M N => (M.eval ρ) (N.eval ρ)
  | .lam A M => .lam (.mk (fun u => M.eval (push ρ u (A.eval ρ))) mySorry)

def fits (ρ : Nat → D) : List Expr → Prop
  | [] => True
  | A::Γ => El .U (A.eval (tail ρ)) ∧ El (A.eval (tail ρ)) (ρ 0) ∧ fits (tail ρ) Γ

inductive WHRed : Expr → Expr → Prop
  | app : WHRed N N' → WHRed (.app N M) (.app N' M)
  | beta : WHRed (.app (.lam A N) M) (subst N M)

axiom HasType (Γ : List Expr) (M N : Expr) : Prop
axiom HasType.U : HasType Γ .U .U
def Conv (M N _ : Expr) := M = N

def WHRedT (M N A : Expr) := WHRed M N ∧ Conv M N A
inductive WHRedTS : (M N A : Expr) → Prop where
  | rfl : HasType [] M A → WHRedTS M M A
  | tail : WHRedTS M N A → WHRedT N P A → WHRedTS M P A

local notation M " ⤳* " N " : " A:36 => WHRedTS M N A

axiom WHRedTS.uniq_pi : M ⤳* .pi B F : A → M ⤳* .pi B' F' : A → B.pi F = B'.pi F'

section
variable (HasTypeF : Expr → Expr → Shape n → Shape n → Prop)

def HasTypeFamF (B F : Expr) (b : Shape n) (f : ShapeFun n) : Prop :=
  ∀ N v, Shape.embed v ≤ N.eval (fun _ => .bot) → v :ᶠ b →
    HasTypeF N B v b → HasTypeF (subst F N) .U (f.app v) .U

def HasPiFamF (M B F : Expr) (m : ShapeFun n) (b : Shape n) (f : ShapeFun n) : Prop :=
  ∀ N v, Shape.embed v ≤ N.eval (fun _ => .bot) → v :ᶠ b →
    HasTypeF N B v b → HasTypeF (.app M N) (subst F N) (m.app v) (f.app v)
end

def HasTypeF : ∀ {n}, Expr → Expr → Shape n → Shape n → Prop
  | 0, _, _, _, .bot | _+1, _, _, _, .bot => True
  | _+1, _, _, _, .lam f => f ≤≤ .bot
  | 0, A, V, .U, .U | _+1, A, V, .U, .U => V ⤳* .U : .U ∧ A ⤳* .U : .U
  | _+1, A, V, .pi b f, .U => V ⤳* .U : .U ∧ ∃ B F, A ⤳* .pi B F : .U ∧
    HasTypeF B .U b .U ∧ HasType [B] F .U ∧ HasTypeFamF HasTypeF B F b f
  | 0, _, V, .bot, .U | _+1, _, V, .bot, .U => V ⤳* .U : .U
  | _+1, _, V, .lam f, .U => V ⤳* .U : .U ∧ f ≤≤ .bot
  | _+1, M, A, .lam m, .pi b f => ∃ B F, A ⤳* .pi B F : .U ∧ HasPiFamF HasTypeF M B F m b f
  | _+1, M, A, .bot, .pi b f => ∃ B F, A ⤳* .pi B F : .U ∧ HasPiFamF HasTypeF M B F .bot b f
  | _, _, _, _, _ => False

theorem HasTypeF.U_U : @HasTypeF n A V .U .U ↔ V ⤳* .U : .U ∧ A ⤳* .U : .U := by
  cases n <;> simp [HasTypeF]

theorem HasPiFamF.bot : @Shape.HasTypePi n f a →
    HasTypeFamF HasTypeF B F a f → HasPiFamF HasTypeF M B F .bot a f := by
  intro h1 h3 N v f' h5 h6
  have h2 := h3 _ _ f' h5 h6
  have := h1.app h5
  generalize eq : f.app v = t at *
  cases this.unfold with simp [HasTypeF] at this ⊢
  | bot | U => cases n <;> simp [HasTypeF] <;> exact h2.2
  | pi a1 =>
    let ⟨B, F, c1, c2, c3, c4⟩ := h2.2
    exact ⟨B, F, c1, HasPiFamF.bot a1 c4⟩

mutual

theorem HasTypeF.mono {a a' : Shape n} : HasTypeF A .U a .U → a :ᶠ .U → a' ≤ a →
    u :ᶠ a → HasTypeF M A u a → u' ≤ u → u' :ᶠ a' → HasTypeF M A u' a' := by
  intro h1 h2 h3 h7 h4 h6 h5
  unfold HasTypeF at h4; split at h4
  · cases a' <;> cases h3; simp [HasTypeF]
  · cases a' <;> cases h3; simp [HasTypeF]
  · cases a' with | bot => simp [HasTypeF] | lam => ?_ | _ => cases h3
    exact .trans h3 h4
  · cases a' with | bot => simp [HasTypeF] | U
    cases u' with | bot => exact h4.1 | U => exact h4
  · cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases h3
    cases u' with | bot => exact h4.1 | U => exact h4 | _ => cases h6
  · cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases h3
    cases u' with | bot => exact h4.1 | pi => ?_ | _ => cases h6
    let ⟨a1, B, F, a2, a3, a4, a5⟩ := h4; simp [Shape.LE.def] at h6
    let .pi hf := h5.unfold; let .pi b1 := h7.unfold
    refine ⟨a1, B, F, a2, .mono (HasTypeF.U_U.2 ⟨.rfl .U, .rfl .U⟩) .U .rfl b1.1 a3 h6.1 hf.1,
      a4, .mono a3 hf b1 h6.1 h6.2 a5⟩
  · cases a' with | bot => simp [HasTypeF] | U
    cases u' with | bot => exact h4 | _ => cases h6
  · cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases h3
    cases u' with | bot => exact h4 | _ => cases h6
  · cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases h3
    cases h5.unfold with simp [HasTypeF] | bot => exact h4.1 | _ => cases h6
  · cases a' with | bot => simp [HasTypeF] | pi a f => ?_ | _ => cases h3
    let .pi c1 := h2.unfold; let .lam b1 := h7.unfold
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    cases h5.unfold with simp [HasTypeF, Shape.LE.def] at h3 ⊢
    | bot => exact ⟨B, F, a1, .mono a3 a5 c1 .bot .bot h3.1 h3.2 b1 a2⟩
    | lam h5 => exact ⟨B, F, a1, .mono a3 a5 c1 h5 h6 h3.1 h3.2 b1 a2⟩
  · cases a' with | bot => simp [HasTypeF] | pi a f => ?_ | _ => cases h3
    let .pi c1 := h2.unfold; cases Shape.le_bot.1 h6; simp [Shape.LE.def] at h3
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    exact ⟨B, F, a1, .mono a3 a5 c1 .bot .rfl h3.1 h3.2 .bot a2⟩
  · cases h4
termination_by 2 * n

theorem HasPiFamF.mono :
    HasTypeF (n := n) B .U b .U → HasTypeFamF HasTypeF B F b f →
    Shape.HasTypePi f b → Shape.HasTypeLam m' b' f' →
    m' ≤≤ m → b' ≤ b → f' ≤≤ f →
    Shape.HasTypeLam m b f → HasPiFamF HasTypeF M B F m b f →
    HasPiFamF HasTypeF M B F m' b' f' := by
  intro h0 bf h1 hm' h3 h4 h5 hm h6 N v h7 h8 h9
  have h9' := h0.mono_r h1.1 h4 h9 h8
  have := h6 _ _ h7 (h8.mono h4) h9'
  refine .mono (bf _ _ h7 (h8.mono h4) h9') (h1.app (h8.mono h4))
    (ShapeFun.app_mono_l h5 _) (hm.app (h8.mono h4))
    this (ShapeFun.app_mono_l h3 _) (hm'.app h8)
termination_by 2 * n + 1

theorem HasTypeFamF.mono : HasTypeF (n := n) B .U b .U →
    Shape.HasTypePi f' b' → Shape.HasTypePi f b → b' ≤ b → f' ≤≤ f →
    HasTypeFamF HasTypeF B F b f → HasTypeFamF HasTypeF B F b' f' := by
  rw [HasTypeFamF, HasTypeFamF]
  intro h1 h3 hf h4 h5 h6 N v h7 h8 h9
  have := h6 _ _ h7 (h8.mono h4) (.mono_r h1 hf.1 h4 h9 h8)
  refine .mono (HasTypeF.U_U.2 ⟨.rfl .U, .rfl .U⟩) .U .rfl
    (hf.app (h8.mono h4)) this (ShapeFun.app_mono_l h5 _) (h3.app h8)
termination_by 2 * n + 1

theorem HasTypeF.mono_r : HasTypeF (n := n) A .U a .U → a :ᶠ .U → a' ≤ a →
    HasTypeF M A u' a' → u' :ᶠ a' → HasTypeF M A u' a := by
  intro h1 h2 h3 h4 h5
  unfold HasTypeF at h4; split at h4
  · cases h5.unfold
    cases h2.unfold with
    | bot => trivial
    | U => exact h1.2
  · cases h5.unfold
    cases h2.unfold with
    | bot => trivial
    | U => exact h1.2
    | pi b1 => let ⟨B, F, a1, a2, a3, a4⟩ := h1.2; exact ⟨_, _, a1, .bot b1 a4⟩
  · cases h2.unfold with | bot => trivial | _ => cases h3
  · cases h2.unfold with | U => exact h4 | _ => cases h3
  · cases h2.unfold with | U => exact h4 | _ => cases h3
  · cases h2.unfold with | U => exact h4 | _ => cases h3
  · cases h2.unfold <;> cases h3; trivial
  · cases h2.unfold <;> cases h3; trivial
  · cases h5.unfold
  · cases h2.unfold <;> simp [Shape.LE.def] at h3
    let .lam h5 := h5.unfold; let .pi h6 := h2.unfold
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    exact ⟨B, F, a1, .mono_r a3 a5 h6 h5 h3.1 h3.2 a2⟩
  · cases h2.unfold <;> simp [Shape.LE.def] at h3; let .pi h6 := h2.unfold
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    exact ⟨B, F, a1, .mono_r a3 a5 h6 .bot h3.1 h3.2 a2⟩
  · cases h4
termination_by 2 * n

theorem HasPiFamF.mono_r : HasTypeF (n := n) B .U a .U → HasTypeFamF HasTypeF B F a f →
    Shape.HasTypePi f a → Shape.HasTypeLam m a' f' →
    a' ≤ a → f' ≤≤ f → HasPiFamF HasTypeF M B F m a' f' → HasPiFamF HasTypeF M B F m a f := by
  intro hb bf h2 h3 h4 h5 h6 N v h7 hv h9
  have ⟨v', hv', lv, eq⟩ := hv.maximal h3 h4
  have := h6 N v' (.trans (D.LE.embed.2 lv) h7) hv' (.mono hb h2.1 h4 hv h9 lv hv')
  have fv : f'.app v' ≤ f.app v := .trans (ShapeFun.app_mono_l h5 v') (ShapeFun.app_mono_r lv)
  exact .mono_r (bf N v h7 hv h9) (h2.app hv) fv (eq ▸ this) (eq ▸ h3.app hv')
termination_by 2 * n + 1

end
