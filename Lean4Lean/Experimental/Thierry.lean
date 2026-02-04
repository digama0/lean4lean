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
inductive FinMut : Bool → Type where
  | bot : FinMut b
  | U : FinMut false
  | lam (f : FinMut true) : FinMut false
  | pi (a : FinMut false) (f : FinMut true) : FinMut false
  | cons (u v : FinMut false) (f : FinMut true) : FinMut true

abbrev FinElem := FinMut false
abbrev FinFun := FinMut true

axiom FinElem.embed : FinElem → D
axiom FinFun.embed : FinFun → DF
noncomputable instance : Coe FinElem D := ⟨FinElem.embed⟩
noncomputable instance : Coe FinFun DF := ⟨FinFun.embed⟩

def FinMut.LE : FinMut b → FinMut b → Prop :=
  match b with
  | false => fun x y => FinElem.embed x ≤ FinElem.embed y
  | true => fun x y => FinFun.embed x ≤ FinFun.embed y

axiom FinFun.eval : FinFun → FinElem → FinElem

instance : LE (FinMut b) := ⟨FinMut.LE⟩
noncomputable instance : CoeFun FinFun fun _ => FinElem → FinElem := ⟨FinFun.eval⟩

def Join (a b c : FinMut x) := ∀ y, a ≤ y ∧ b ≤ y ↔ c ≤ y

@[simp] axiom FinElem.embed_bot : ((.bot : FinElem) : D) = .bot
@[simp] axiom FinFun.embed_bot : ((.bot : FinFun) : DF) = .bot
@[simp] axiom FinElem.embed_U : ((.U : FinElem) : D) = .U
def FinElem.LE_unfold : FinElem → FinElem → Prop
  | .bot, _ => True
  | .U, .U => True
  | .pi x f, .pi y g => x ≤ y ∧ f ≤ g
  | .lam f, .lam g => f ≤ g
  | .lam f, .bot => f ≤ .bot
  | _, _ => False

axiom FinElem.LE.unfold : a ≤ b → FinElem.LE_unfold a b

@[simp] theorem FinMut.LE.bot {x : FinMut b} : .bot ≤ x := by
  cases b
  · show (_:D) ≤ _; simp [FinElem.embed_bot, D.LE.bot]
  · show (_:DF) ≤ _; simp [FinFun.embed_bot, DF.LE.bot]

@[simp] theorem FinMut.LE.rfl {x : FinMut b} : x ≤ x := sorry
@[simp] theorem FinMut.LE.lam {x y : FinFun} : x.lam ≤ y.lam ↔ x ≤ y := sorry
@[simp] theorem FinMut.LE.pi {x y : FinElem} : x.pi f ≤ y.pi g ↔ x ≤ y ∧ f ≤ g := sorry
axiom FinMut.LE.cons : FinMut.cons u v f ≤ g ↔ v ≤ g u ∧ f ≤ g
axiom eval_cons : FinMut.cons u v f x ≤ y ↔ (u ≤ x → v ≤ y) ∧ f x ≤ y
@[simp] axiom eval_embed : ((f : FinFun) x : D) = (f : DF) x
@[simp] axiom bot_apply : (.bot : FinFun) x = .bot

inductive FinHasTypeK : Bool → Type
  | ty : FinElem → FinHasTypeK false
  | pi (a : FinElem) : FinHasTypeK true
  | lam (a : FinElem) (f : FinFun) : FinHasTypeK true

set_option hygiene false
local notation u " :ᶠ " a:36 => FinHasType u (.ty a)

inductive FinHasType : FinMut b → FinHasTypeK b → Prop
  | bot : FinHasType .bot a
  | U : .U :ᶠ .U
  | pi : a :ᶠ .U → FinHasType f (.pi a) → .pi a f :ᶠ .U
  | pi_cons : u :ᶠ a → v :ᶠ .U → FinHasType f (.pi a) → FinHasType (.cons u v f) (.pi a)
  | lam : FinHasType f (.lam a g) → .lam f :ᶠ .pi a g
  | lam_cons : u :ᶠ a → v :ᶠ g u →
    FinHasType f (.lam a g) → FinHasType (.cons u v f) (.lam a g)

theorem FinHasType.mono : u :ᶠ a → a ≤ b → u :ᶠ b := sorry
theorem FinHasType.mono_l : u :ᶠ a → v ≤ u → v :ᶠ a := sorry

theorem FinHasType.join (H : Join u v w) : u :ᶠ a → v :ᶠ b → w :ᶠ b := sorry

theorem FinHasType.pi_eval : FinHasType f (.pi a) → u :ᶠ a → f u :ᶠ .U := sorry
theorem FinHasType.lam_eval : FinHasType f (.lam a g) → u :ᶠ a → f u :ᶠ g u := sorry
theorem FinHasType.lem5 : .lam w :ᶠ .pi b f → b ≤ a → u :ᶠ a → ∃ v, v :ᶠ b ∧ v ≤ u ∧ w u = w v := sorry

axiom proj : D → DF
axiom proj_U_U : proj .U .U = .U
axiom proj_U_pi : proj .U (.pi a f) = .pi (proj .U a) ((proj .U).comp <| f.comp <| proj a)
axiom proj_pi : proj (.pi a f) (.lam w) =
  .lam (.mk (fun x => proj (f (proj a x)) (w (proj a x))) mySorry)

axiom proj_le : proj a u ≤ u
axiom proj_proj (a u : D) : proj a (proj a u) = proj a u

def El (a u : D) : Prop := proj a u = u

theorem El_iff {u a : FinElem} : El a u ↔ u :ᶠ a := sorry
theorem El_U_iff {u : FinElem} : El .U u ↔ u :ᶠ .U := by rw [← El_iff, FinElem.embed_U]
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

@[simp] def meas : FinMut b → Nat
  | .bot (b := true) | .U => 0
  | .bot (b := false) => 1
  | .lam f => meas f + 1
  | .pi a f => meas a + meas f + 1
  | .cons u v f => meas u + meas v + meas f + 1

theorem meas_apply_lt (f : FinFun) (x) : meas (f x) < meas f := sorry

mutual

def HasTypeF : Expr → Expr → FinElem → FinElem → Prop
  | _, _, _, .bot => True
  | _, _, _, .lam f => f ≤ .bot
  | A, V, .U, .U => V ⤳* .U : .U ∧ A ⤳* .U : .U
  | A, V, .pi b f, .U => V ⤳* .U : .U ∧ ∃ B F, A ⤳* .pi B F : .U ∧
    HasTypeF B .U b .U ∧ HasType [B] F .U ∧ HasTypeFamF B F b f
  | _, V, .bot, .U => V ⤳* .U : .U
  | _, V, .lam f, .U => V ⤳* .U : .U ∧ f ≤ .bot
  | M, A, .lam m, .pi b f => ∃ B F, A ⤳* .pi B F : .U ∧ HasPiFamF M B F m b f
  | M, A, .bot, .pi b f => ∃ B F, A ⤳* .pi B F : .U ∧ HasPiFamF M B F .bot b f
  | _, _, _, _ => False
termination_by _ _ u a => 2 * (meas u + meas a) + 1

def HasTypeFamF (B F : Expr) (b : FinElem) (f : FinFun) : Prop :=
  ∀ N v, meas v < meas f → FinElem.embed v ≤ N.eval (fun _ => .bot) → v :ᶠ b →
    HasTypeF N B v b → HasTypeF (subst F N) .U (f v) .U
termination_by 2 * (meas b + meas f)
decreasing_by all_goals first | grind | simp; have := meas_apply_lt f v; grind

def HasPiFamF (M B F : Expr) (m : FinFun) (b : FinElem) (f : FinFun) : Prop :=
  ∀ N v, meas v < meas f → FinElem.embed v ≤ N.eval (fun _ => .bot) → v :ᶠ b →
    HasTypeF N B v b → HasTypeF (.app M N) (subst F N) (m v) (f v)
termination_by 2 * (meas m + meas b + meas f)
decreasing_by all_goals first
  | grind | have := meas_apply_lt m v; have := meas_apply_lt f v; grind

end

theorem HasTypeFamF.def : HasTypeFamF B F b f ↔
  ∀ N v, FinElem.embed v ≤ N.eval (fun _ => .bot) → v :ᶠ b →
    HasTypeF N B v b → HasTypeF (subst F N) .U (f v) .U := sorry

theorem HasPiFamF.def : HasPiFamF M B F m b f ↔
  ∀ N v, FinElem.embed v ≤ N.eval (fun _ => .bot) → v :ᶠ b →
    HasTypeF N B v b → HasTypeF (.app M N) (subst F N) (m v) (f v) := sorry

theorem HasPiFamF.bot : a :ᶠ .U → FinHasType f (.pi a) →
    HasTypeFamF B F a f → HasPiFamF M B F .bot a f := by
  rw [HasPiFamF, HasTypeFamF.def]
  intro h1 h2 h3 n v _ f' h5 h6
  have := h3 _ _ f' h5 h6
  have := FinHasType.pi_eval h2 h5
  have := meas_apply_lt
  generalize eq : FinFun.eval f v = t at *
  cases this with simp [HasTypeF] at this ⊢
  | U => exact this.2
  | pi a1 a2 =>
    let ⟨B, F, c1, c2, c3, c4⟩ := this.2
    exact ⟨B, F, c1, HasPiFamF.bot a1 a2 c4⟩
termination_by 2 * meas f
decreasing_by have := meas_apply_lt f v; grind [meas]

mutual

theorem HasTypeF.mono {a a' : FinElem} : HasTypeF A .U a .U → a :ᶠ .U → a' ≤ a →
    u :ᶠ a → HasTypeF M A u a → u' ≤ u → u' :ᶠ a' → HasTypeF M A u' a' := by
  intro h1 h2 h3 h7 h4 h6 h5
  unfold HasTypeF at h4; split at h4
  · replace h3 := FinElem.LE.unfold h3
    cases a' with | bot => simp [HasTypeF] | lam => ?_ | _ => cases h3
    simpa [HasTypeF, FinElem.LE_unfold] using h3
  · replace h3 := FinElem.LE.unfold h3
    cases a' with | bot => simp [HasTypeF] | lam => ?_ | _ => cases h3
    simp [HasTypeF, FinElem.LE_unfold] at h3 ⊢; exact DF.LE.trans h3 h4
  · cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases FinElem.LE.unfold h3
    cases h5 with simp [HasTypeF] | bot => exact h4.1 | U => exact h4 | pi
    cases FinElem.LE.unfold h6
  · cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases FinElem.LE.unfold h3
    cases h5 with simp [HasTypeF] | bot => exact h4.1 | U => cases FinElem.LE.unfold h6 | pi ha hf
    let ⟨a1, B, F, a2, a3, a4, a5⟩ := h4; let .pi b1 b2 := h7; simp at h6
    refine ⟨a1, B, F, a2, .mono (by simp [HasTypeF]; exact .rfl .U) .U .rfl b1 a3 h6.1 ha,
      a4, .mono a3 b1 ha hf b2 h6.1 h6.2 a5⟩
  · replace h3 := FinElem.LE.unfold h3
    cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases h3
    cases h5 with simp [HasTypeF] | bot => exact h4 | _ => cases FinElem.LE.unfold h6
  · replace h3 := FinElem.LE.unfold h3
    cases a' with | bot => simp [HasTypeF] | U => ?_ | _ => cases h3
    cases h5 with simp [HasTypeF] | bot => exact h4.1 | _ => cases FinElem.LE.unfold h6
  · replace h3 := FinElem.LE.unfold h3
    cases a' with | bot => simp [HasTypeF] | pi a f => ?_ | _ => cases h3
    replace h6 := FinElem.LE.unfold h6; let .pi c1 c2 := h2; let .lam b1 := h7
    simp [HasTypeF] at h1
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    cases h5 with simp [HasTypeF, FinElem.LE_unfold] at h3 ⊢
    | bot => exact ⟨B, F, a1, .mono a3 a5 c1 c2 .bot .bot h3.1 h3.2 b1 a2⟩
    | lam h5 => exact ⟨B, F, a1, .mono a3 a5 c1 c2 h5 h6 h3.1 h3.2 b1 a2⟩
  · replace h3 := FinElem.LE.unfold h3
    cases a' with | bot => simp [HasTypeF] | pi a f => ?_ | _ => cases h3
    replace h6 := FinElem.LE.unfold h6; let .pi c1 c2 := h2
    simp [HasTypeF] at h1
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    cases h5 with simp [HasTypeF, FinElem.LE_unfold] at h3 ⊢
    | bot => exact ⟨B, F, a1, .mono a3 a5 c1 c2 .bot .rfl h3.1 h3.2 .bot a2⟩
    | lam b1 => exact ⟨B, F, a1, .mono a3 a5 c1 c2 b1 h6 h3.1 h3.2 .bot a2⟩
  · cases h4
termination_by 2 * (meas u + meas a)

theorem HasPiFamF.mono :
    HasTypeF B Expr.U b FinMut.U → HasTypeFamF B F b f →
    b :ᶠ .U → FinHasType f (.pi b) → FinHasType m' (.lam b' f') →
    m' ≤ m → b' ≤ b → f' ≤ f →
    FinHasType m (.lam b f) → HasPiFamF M B F m b f → HasPiFamF M B F m' b' f' := by
  rw [HasPiFamF.def, HasPiFamF.def, HasTypeFamF.def]
  intro h0 bf h1 h2 hm' h3 h4 h5 hm h6 N v h7 h8 h9
  have h9' := h0.mono_r h1 h4 h9 h8
  have := h6 _ _ h7 (h8.mono h4) h9'
  refine .mono (bf _ _ h7 (h8.mono h4) h9') (.pi_eval h2 (h8.mono h4))
    (show (_:D)≤ _ by simp; exact h5 _) (.lam_eval hm (h8.mono h4))
    this (show (_:D)≤ _ by simp; exact h3 _) (.lam_eval hm' h8)
termination_by 2 * (meas m + meas b + meas f) + 1
decreasing_by
  · decreasing_tactic
  · have := meas_apply_lt m v; have := meas_apply_lt f v; decreasing_tactic

theorem HasTypeFamF.mono : HasTypeF B Expr.U b FinMut.U →
    b :ᶠ .U → b' :ᶠ .U → FinHasType f' (.pi b') → FinHasType f (.pi b) → b' ≤ b → f' ≤ f →
    HasTypeFamF B F b f → HasTypeFamF B F b' f' := by
  rw [HasTypeFamF.def, HasTypeFamF.def]
  intro h1 hb h2 h3 hf h4 h5 h6 N v h7 h8 h9
  have := h6 _ _ h7 (h8.mono h4) (.mono_r h1 hb h4 h9 h8)
  refine .mono (by simp [HasTypeF]; exact .rfl .U) .U .rfl
    (.pi_eval hf (h8.mono h4)) this (show (_:D)≤ _ by simp; exact h5 _) (.pi_eval h3 h8)
termination_by 2 * (meas b + meas f) + 1
decreasing_by
  · decreasing_tactic
  · have := meas_apply_lt f v; decreasing_tactic

theorem HasTypeF.mono_r : HasTypeF A .U a .U → a :ᶠ .U → a' ≤ a →
    HasTypeF M A u' a' → u' :ᶠ a' → HasTypeF M A u' a := by
  intro h1 h2 h3 h4 h5
  unfold HasTypeF at h4; split at h4
  · cases h5
    cases h2 with
    | bot => simp [HasTypeF]
    | U => simp [HasTypeF] at h1 ⊢; exact h1.2
    | @pi a f b1 b2 =>
      simp [HasTypeF] at h1 ⊢
      let ⟨B, F, a1, a2, a3, a4⟩ := h1.2
      exact ⟨_, _, a1, .bot b1 b2 a4⟩
  · cases h2 with | bot => simp [HasTypeF] | _ => cases FinElem.LE.unfold h3
  · cases h2 with | U => simp [HasTypeF]; exact h4 | _ => cases FinElem.LE.unfold h3
  · cases h2 with | U => simp [HasTypeF]; exact h4 | _ => cases FinElem.LE.unfold h3
  · cases h2 with | U => simp [HasTypeF]; exact h4 | _ => cases FinElem.LE.unfold h3
  · cases h2 <;> cases FinElem.LE.unfold h3; simpa [HasTypeF]
  · cases h2 <;> cases FinElem.LE.unfold h3; simp [HasTypeF] at h1 h3 ⊢; let .lam h5 := h5
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    exact ⟨B, F, a1, .mono_r a3 a5 ‹_› ‹_› h5 h3.1 h3.2 a2⟩
  · cases h2 <;> cases FinElem.LE.unfold h3; simp [HasTypeF] at h1 ⊢
    let ⟨B, F, a1, a2⟩ := h4; let ⟨B', F', a1', a3, a4, a5⟩ := h1.2; cases a1.uniq_pi a1'
    exact ⟨B, F, a1, .mono_r a3 a5 ‹_› ‹_› .bot ‹_› ‹_› a2⟩
  · cases h4
termination_by 2 * (meas a)

theorem HasPiFamF.mono_r : HasTypeF B .U a .U → HasTypeFamF B F a f →
    a :ᶠ .U → FinHasType f (.pi a) →
    FinHasType m (FinHasTypeK.lam a' f') →
    a' ≤ a → f' ≤ f → HasPiFamF M B F m a' f' → HasPiFamF M B F m a f := by
  rw [HasPiFamF.def, HasPiFamF, HasTypeFamF.def]
  intro hb bf h1 h2 h3 h4 h5 h6 N v _ h7 hv h9
  have ⟨v', hv', lv, eq⟩ := FinHasType.lem5 (.lam h3) h4 hv
  have := h6 N v' (D.LE.trans lv h7) hv' (.mono hb h1 h4 hv h9 lv hv')
  have fv : f' v' ≤ f v := D.LE.trans (y := f v')
    (by simpa using h5 v') (by simpa using DF.mono (f := f) lv)
  exact .mono_r (bf N v h7 hv h9) (.pi_eval h2 hv) fv (eq ▸ this) (eq ▸ .lam_eval h3 hv')
termination_by 2 * (meas a + meas f)
decreasing_by
  · decreasing_tactic
  · have := meas_apply_lt f v; decreasing_tactic

end
