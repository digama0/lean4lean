module

public import Lean4Lean.Experimental.SExpr

@[expose] public section

namespace Lean4Lean

namespace SExpr
variable [Params]

structure Classifier' where
  EqTy' : SExpr → Prop := fun _ => True
  HasTy' : SExpr → Prop := fun _ => True
  DefEq' : SExpr → SExpr → Prop := fun _ _ => True
  defEq'_symm : DefEq' a b → DefEq' b a := by exact id
  defEq'_left : DefEq' a b → DefEq' a a := by exact id
  defEq'_self : HasTy' a → DefEq' a a := by exact id
def Classifier (_Γ : List SExpr) (_A : SExpr) (_u : SLevel) := Classifier'

def Classifier.EqTy (cl : Classifier Γ A u) (B : SExpr) : Prop :=
  Γ ⊢ A ≡ B :↑ .sort u ∧ cl.EqTy' B

def Classifier.HasTy (cl : Classifier Γ A u) (a : SExpr) : Prop :=
  (Γ ⊢ a :↑ A) ∧ cl.HasTy' a

def Classifier.DefEq (cl : Classifier Γ A u) (a b : SExpr) : Prop :=
  Γ ⊢ a ≫≪ b :↑ A ∧ cl.HasTy' a ∧ cl.HasTy' b ∧ cl.DefEq' a b

theorem Classifier.DefEq.symm {cl : Classifier Γ A u} : cl.DefEq a b → cl.DefEq b a
  | ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3, h2, cl.defEq'_symm h4⟩
theorem Classifier.DefEq.left {cl : Classifier Γ A u} : cl.DefEq a b → cl.HasTy a
  | ⟨h1, h2, _⟩ => ⟨h1.left, h2⟩

theorem Classifier.defEq_self {cl : Classifier Γ A u} : cl.DefEq a a ↔ cl.HasTy a :=
  ⟨fun h => h.left, fun ⟨h1, h2⟩ => ⟨.refl h1, h2, h2, cl.defEq'_self h2⟩⟩

theorem Classifier.DefEq.imp {Γ A u Γ' A' u'} {cl : Classifier Γ A u} {cl' : Classifier Γ' A' u'}
    {f : SExpr → SExpr}
    (H0 : ∀ {a b}, Γ ⊢ a ≫≪ b :↑ A → Γ' ⊢ f a ≫≪ f b :↑ A')
    (H1 : ∀ {a}, cl.HasTy' a → cl'.HasTy' (f a))
    (H2 : ∀ {a b}, cl.DefEq' a b → cl'.DefEq' (f a) (f b))
    {a b} : cl.DefEq a b → cl'.DefEq (f a) (f b)
  | ⟨h1, h2, h3, h4⟩ => ⟨H0 h1, H1 h2, H1 h3, H2 h4⟩

def Classifier.forallE
    (RA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Classifier Δ (A.lift' ρ) u)
    (RB : ∀ {ρ Δ} (W : Ctx.Lift' ρ Γ Δ) {a},
      (@RA ρ Δ W).HasTy a → Classifier Δ ((B.lift' ρ.cons).inst a) v) :
    Classifier Γ (.forallE A B) (.imax u v) where
  EqTy' C := ∃ A' B', Γ ⊢ C ⤳* .forallE A' B' ∧ Γ ⊢ C ≡ .forallE A' B' :↑ .sort (.imax u v) ∧
    (∀ {ρ Δ} W, (@RA ρ Δ W).EqTy (A'.lift' ρ)) ∧
    (∀ {ρ Δ} W {a} (ha : (@RA ρ Δ W).HasTy a), (RB W ha).EqTy ((B'.lift' ρ.cons).inst a))
  HasTy' f := ∀ {ρ Δ W a b} (ab : (@RA ρ Δ W).DefEq a b),
    (RB W ab.left).DefEq ((f.lift' ρ).app a) ((f.lift' ρ).app b)
  DefEq' f g := ∀ {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a),
    (RB W ha).DefEq ((f.lift' ρ).app a) ((g.lift' ρ).app a)
  defEq'_symm _ _ H {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a) := (H ha).symm
  defEq'_left _ _ H {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a) := Classifier.defEq_self.2 (H ha).left
  defEq'_self _ H {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a) := H (Classifier.defEq_self.2 ha)

def NormalType : SExpr → Prop | .sort _ | .forallE .. => True | _ => False

def NormalType.whnf : ∀ {A}, NormalType A → WHNF Γ A
  | .sort _, _ => .sort
  | .forallE .., _ => .forallE

theorem NormalType.weak' (H : NormalType A) : NormalType (A.lift' ρ) := by
  cases A <;> cases H <;> trivial

theorem NormalType.weak'_inv (H : NormalType (A.lift' ρ)) : NormalType A := by
  cases A <;> cases H <;> trivial

inductive LogRel : ∀ Γ A u, Classifier Γ A u → Type where
  | stuck :
    (∀ A', Γ ⊢ A ⤳* A' → ¬NormalType A') →
    Γ ⊢ A ▷* .sort u → Γ ⊢ A :↑ .sort u → LogRel Γ A u {}
  | sort : Γ ⊢ A ⤳* .sort l → Γ ⊢ A ▷* .sort l.succ → Γ ⊢ A ≡ .sort l :↑ .sort l.succ →
    LogRel Γ A (.succ l) { EqTy' A := Γ ⊢ A ⤳* .sort l }
  | forallE
    {RA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Classifier Δ (A.lift' ρ) u}
    {RB : ∀ {ρ Δ} (W : Ctx.Lift' ρ Γ Δ) {a},
      (@RA ρ Δ W).HasTy a → Classifier Δ ((B.lift' ρ.cons).inst a) v} :
    Γ ⊢ X ⤳* .forallE A B → Γ ⊢ X ▷* .sort (.imax u v) →
    A::Γ ⊢ B ▷* .sort v → A::Γ ⊢ B :↑ .sort v → Γ ⊢ X ≡ .forallE A B :↑ .sort (.imax u v) →
    (∀ {ρ Δ} W, LogRel Δ (A.lift' ρ) u (@RA ρ Δ W)) →
    (∀ {ρ Δ} W {a} (ha : (@RA ρ Δ W).HasTy a), LogRel Δ ((B.lift' ρ.cons).inst a) v (RB W ha)) →
    (∀ {ρ Δ} W {a b} (ab : (@RA ρ Δ W).DefEq a b), (RB W ab.left).EqTy ((B.lift' ρ.cons).inst b)) →
    LogRel Γ X (.imax u v) (.forallE @RA @RB)

theorem LogRel.hasType : LogRel Γ A u cl → Γ ⊢ A :↑ .sort u
  | .stuck _ _ h => h
  | .sort _ _ h | .forallE _ _ _ _ h .. => h.left

theorem LogRel.eqTy_refl (H : LogRel Γ A u cl) : cl.EqTy A := by
  induction H with
  | stuck _ _ h => exact ⟨h, ⟨⟩⟩
  | sort h1 _ h3 => exact ⟨h3.left, h1⟩
  | forallE h1 _ _ _ h5 _ _ h8 ih1 =>
    exact ⟨h5.left, _, _, h1, h5, fun _ => ih1 _, fun _ _ h => h8 _ (Classifier.defEq_self.2 h)⟩

def LRIsType (Γ : List SExpr) (A : SExpr) (u : SLevel) : Type := Σ cl, LogRel Γ A u cl
local notation:65 Γ " ⊩["u"] " A:36 => LRIsType Γ A u

def LREqTy {Γ A u} (B : SExpr) (H : Γ ⊩[u] A) : Prop := H.1.EqTy B
local notation:65 H " ⊩≡ " B:36 => LREqTy B H

def LRDefEq {Γ A u} (a b : SExpr) (H : Γ ⊩[u] A) : Prop := H.1.DefEq a b
local notation:65 H " ⊩ " a:36 " ≡ " b:36 => LRDefEq a b H
local notation:65 H " ⊩ " a:36 => LRDefEq a a H

theorem LRIsType.hasType (J : Γ ⊩[u] A) : Γ ⊢ A :↑ .sort u := J.2.hasType
theorem LREqTy.defeq {J : Γ ⊩[u] A} (H : J ⊩≡ B) : Γ ⊢ A ≡ B :↑ .sort u := H.1
theorem LRDefEq.defeq {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : Γ ⊢ a ≡ b :↑ A := H.1.defeq
nonrec theorem LRDefEq.left {Γ A u a b} {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : J ⊩ a :=
  Classifier.defEq_self.2 H.left

def LRIsType.cast (J : Γ ⊩[u] A) (eq : A = A') : Γ ⊩[u] A' := eq ▸ J
theorem LREqTy.cast {J : Γ ⊩[u] A} (eq : A = A') : J.cast eq ⊩≡ B ↔ J ⊩≡ B := by
  cases eq; rfl
theorem LRDefEq.cast {J : Γ ⊩[u] A} (eq : A = A') : J.cast eq ⊩ a ≡ b ↔ J ⊩ a ≡ b := by
  cases eq; rfl
theorem LRHasTy.cast {J : Γ ⊩[u] A} (eq : A = A') : (J.cast eq).1.HasTy a ↔ J.1.HasTy a := by
  cases eq; rfl

def LRIsType.stuck (H : ∀ A', Γ ⊢ A ⤳* A' → ¬NormalType A')
    (h1 : Γ ⊢ A ▷* .sort u) (h2 : Γ ⊢ A :↑ .sort u) : Γ ⊩[u] A := ⟨_, .stuck H h1 h2⟩
def LRIsType.sort
    (h1 : Γ ⊢ A ⤳* .sort l) (h2 : Γ ⊢ A ▷* .sort l.succ) (h3 : Γ ⊢ A ≡ .sort l :↑ .sort l.succ) :
    Γ ⊩[l.succ] A := ⟨_, .sort h1 h2 h3⟩
def LRIsType.forallE
    (ht1 : Γ ⊢ X ⤳* .forallE A B) (ht2 : Γ ⊢ X ▷* .sort (.imax u v))
    (ht3 : A::Γ ⊢ B ▷* .sort v) (ht4 : A::Γ ⊢ B :↑ .sort v)
    (ht5 : Γ ⊢ X ≡ .forallE A B :↑ .sort (.imax u v))
    (hA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Δ ⊩[u] A.lift' ρ)
    (hB : ∀ {ρ Δ} W {a}, @hA ρ Δ W ⊩ a → Δ ⊩[v] (B.lift' ρ.cons).inst a)
    (ha : ∀ {ρ Δ} W {a b} (ab : @hA ρ Δ W ⊩ a ≡ b), hB W ab.left ⊩≡ (B.lift' ρ.cons).inst b)
    : Γ ⊩[u.imax v] X :=
  ⟨_, .forallE ht1 ht2 ht3 ht4 ht5
    (fun W => (hA W).2) (fun W _ h => (hB W (Classifier.defEq_self.2 h)).2)
    (fun W _ _ => ha W)⟩

@[elab_as_elim] def LRIsType.rec
    {motive : ∀ {Γ u A}, Γ ⊩[u] A → Sort _}
    (stuck : ∀ {Γ u A} h1 h2 h3, motive (@LRIsType.stuck _ Γ u A h1 h2 h3))
    (sort : ∀ {Γ u A} h1 h2 h3, motive (@LRIsType.sort _ Γ u A h1 h2 h3))
    (forallE : ∀ {Γ X A B u v} ht1 ht2 ht3 ht4 ht5 hA hB ha,
      (∀ {ρ Δ} W, motive (@hA ρ Δ W)) →
      (∀ {ρ Δ} W {a} ha, motive (@hB ρ Δ W a ha)) →
      motive (@LRIsType.forallE _ Γ X A B u v ht1 ht2 ht3 ht4 ht5 hA hB ha))
    {Γ u A} (J : Γ ⊩[u] A) : motive J := inner J.2 where
  inner {Γ u A cl} : ∀ (J : LogRel Γ A u cl), motive ⟨cl, J⟩
    | .stuck h1 h2 h3 => stuck h1 h2 h3
    | .sort h1 h2 h3 => sort h1 h2 h3
    | .forallE ht1 ht2 ht3 ht4 ht5 hA hB ha =>
      forallE ht1 ht2 ht3 ht4 ht5 (fun W => ⟨_, hA W⟩)
        (fun W _ ha => ⟨_, hB W (Classifier.defEq_self.1 ha)⟩) ha
        (fun W => inner (hA W))
        (fun W _ ha => inner (hB W (Classifier.defEq_self.1 ha)))

theorem LRIsType.irrel' (J1 : Γ ⊩[u] A) (J2 : Γ ⊩[u'] A) : u = u' ∧ J1 ≍ J2 := by
  induction J1 using LRIsType.rec generalizing u' with
  | stuck l1 l2 =>
    cases J2 using LRIsType.rec with
    | stuck _ r2 => cases l2.determ .sort r2 .sort; exact ⟨rfl, .rfl⟩
    | sort h | forallE h => cases l1 _ h ⟨⟩
  | sort l1 =>
    cases J2 using LRIsType.rec with
    | stuck r1 => cases r1 _ l1 ⟨⟩
    | sort r1 | forallE r1 => cases l1.determ .sort r1 (NormalType.whnf ⟨⟩) <;> exact ⟨rfl, .rfl⟩
  | @forallE Γ u v X A B l1 _ l3 l4 l5 L1 L2 L3 ih1 ih2 =>
    cases J2 using LRIsType.rec with
    | stuck r1 => cases r1 _ l1 ⟨⟩
    | sort r1 => cases l1.determ .forallE r1 .sort
    | @forallE Γ' u' v' X' A' B' r1 _ r3 r4 r5 R1 R2 R3 =>
      cases l1.determ .forallE r1 .forallE
      cases l3.determ .sort r3 .sort
      have {ρ Δ} W := @ih1 ρ Δ W _ (R1 W)
      cases (this .refl).1
      obtain rfl : @L1 = @R1 := by grind
      have {ρ Δ} W {a} ha := @ih2 ρ Δ W a ha _ (R2 W ha)
      obtain rfl : @L2 = @R2 := by grind
      exact ⟨rfl, .rfl⟩

theorem LRIsType.irrel (J1 J2 : Γ ⊩[u] A) : J1 = J2 := eq_of_heq (J1.irrel' J2).2

theorem LREqTy.irrel {J J' : Γ ⊩[u] A} (H : J ⊩≡ B) : J' ⊩≡ B := by
  cases J.irrel J'; exact H

theorem LRDefEq.irrel {J J' : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : J' ⊩ a ≡ b := by
  cases J.irrel J'; exact H

instance {Γ A u} : Subsingleton (Γ ⊩[u] A) := ⟨LRIsType.irrel⟩

protected def LogRel.cast (J : LogRel Γ A u cl) (eq : A = A') : Σ cl, LogRel Γ A' u cl :=
  ⟨cl, eq ▸ J⟩

theorem LogRel.cast_eqTy (J : LogRel Γ A u cl) (eq : A = A') :
    (J.cast eq).1.EqTy a ↔ cl.EqTy a :=
  ⟨fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩⟩

theorem LogRel.cast_hasTy (J : LogRel Γ A u cl) (eq : A = A') :
    (J.cast eq).1.HasTy a ↔ cl.HasTy a :=
  ⟨fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩⟩

theorem LogRel.cast_defEq (J : LogRel Γ A u cl) (eq : A = A') :
    (J.cast eq).1.DefEq a b ↔ cl.DefEq a b := and_congr_left' (eq ▸ .rfl)

variable! {ρ Γ Δ} (W : Ctx.Lift' ρ Γ Δ) in open SExpr LogRel in
def LRIsType.weak' (J : Γ ⊩[u] A) : Δ ⊩[u] A.lift' ρ := by
  induction J using LRIsType.rec with
  | stuck h1 h2 h3 =>
    refine ⟨_, .stuck (fun _ a1 a2 => ?_) (h2.weak' W) (h3.weak' W)⟩
    obtain ⟨_, rfl, b1⟩ := a1.weakU_inv W; exact h1 _ b1 a2.weak'_inv
  | sort h1 h2 h3 => exact ⟨_, .sort (h1.weak' W) (h2.weak' W) (h3.weak' W)⟩
  | @forallE _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    refine .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons) (h5.weak' W)
      (fun W' => (h6 (W.comp W')).cast SExpr.lift'_comp) (fun W' _ ha => ?_) (fun W' _ _ ab => ?_)
    · exact (h7 (W.comp W') ((LRDefEq.cast _).1 ha)).cast (SExpr.lift'_comp ▸ rfl)
    · exact (LREqTy.cast _).2 <| lift'_comp ▸ h8 (W.comp W') ((LRDefEq.cast _).1 ab)

open SExpr LogRel in
theorem LREqTy.weak' (W : Ctx.Lift' ρ Γ Δ) {J : Γ ⊩[u] A} (H : J ⊩≡ B) :
    J.weak' W ⊩≡ B.lift' ρ := by
  induction J using LRIsType.rec with
  | stuck => exact ⟨H.1.weak' W, ⟨⟩⟩
  | sort => exact ⟨H.1.weak' W, H.2.weak' W⟩
  | @forallE _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    let ⟨_, _, a1, a2, a3, a4⟩ := H.2
    refine ⟨H.1.weak' W, _, _, a1.weak' W, a2.weak' W, fun W' => ?_, fun W' _ ha => ?_⟩
    · refine (LREqTy.cast _).2 ?_; rw [← lift'_comp]; exact a3 (W.comp W')
    · refine (LREqTy.cast _).2 ?_; dsimp; rw [← lift'_comp]
      refine a4 (W.comp W') <| (LRHasTy.cast _).1 ha

open SExpr LogRel in
theorem LRDefEq.weak' (W : Ctx.Lift' ρ Γ Δ) {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) :
    J.weak' W ⊩ a.lift' ρ ≡ b.lift' ρ := by
  induction J using LRIsType.rec with
  | stuck | sort => exact ⟨H.1.weak' .weak' W, ⟨⟩, ⟨⟩, ⟨⟩⟩
  | @forallE _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    let ⟨a1, a2, a3⟩ := H.2
    refine ⟨H.1.weak' .weak' W, fun ab => ?_, fun ab => ?_, fun ha => ?_⟩
    · exact (LRDefEq.cast _).2 <| lift'_comp ▸ a1 ((LRDefEq.cast _).1 ab)
    · exact (LRDefEq.cast _).2 <| lift'_comp ▸ a2 ((LRDefEq.cast _).1 ab)
    · exact (LRDefEq.cast _).2 <| lift'_comp ▸ lift'_comp ▸ a3 ((LRHasTy.cast _).1 ha)

theorem LREqTy.defeq_r {J : Γ ⊩[u] A} (J' : Γ ⊩[u] B)
    (H : J ⊩≡ B) (H2 : J ⊩ a ≡ b) : J' ⊩ a ≡ b := sorry

def LREqTy.symm {J : Γ ⊩[u] A} (H : J ⊩≡ B) (J' : Γ ⊩[u] B) :
    {J' : Γ ⊩[u] B // J' ⊩≡ A} :=
  let ⟨_, J⟩ := J
  match J with
  | .stuck .. => sorry -- ⟨⟨_, .stuck _ H.1.hasType.2⟩, H.1.symm, ⟨⟩⟩
  | .sort .. => sorry -- ⟨⟨_, _⟩, _, _⟩
  | .forallE .. => sorry -- ⟨⟨_, _⟩, _, _⟩

nonrec theorem LRDefEq.symm {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : J ⊩ b ≡ a := H.symm

open SExpr (Subst)

structure ClassifierV' where
  EqSubst : List SExpr → Subst → Subst → Prop := fun _ _ _ => True
  eqSubst_left : EqSubst Δ σ σ' → EqSubst Δ σ σ
def ClassifierV (_Γ : List SExpr) := ClassifierV'

def ClassifierV.IsTy (cl : ClassifierV Γ) (A : SExpr) (u : SLevel) : Type :=
  Γ ⊢ A : .sort u ×' ∀ {Δ σ}, cl.EqSubst Δ σ σ →
    { J : Δ ⊩[u] A.subst σ // ∀ σ', cl.EqSubst Δ σ σ' → J ⊩≡ A.subst σ' }

inductive LogRelV : ∀ Γ, ClassifierV Γ → Type where
  | nil : LogRelV [] { eqSubst_left := id }
  | cons : LogRelV Γ R → (JA : R.IsTy A u) → LogRelV (A::Γ) {
      EqSubst Δ σ σ' := ∃ hσ : R.EqSubst Δ σ.tail σ'.tail,
        (JA.2 (R.eqSubst_left hσ)).1 ⊩ σ.head ≡ σ'.head
      eqSubst_left := fun ⟨h1, h2⟩ => ⟨R.eqSubst_left h1, h2.left⟩ }

def LVIsCtx (Γ : List SExpr) := Σ R, LogRelV Γ R
local notation:65 "⊩ᵛ " Γ:36 => LVIsCtx Γ

def LVIsType {Γ : List SExpr} (J : ⊩ᵛ Γ) := J.1.IsTy
local notation:65 J " ⊩ᵛ["u"] " A:36 => LVIsType J A u

def LVEqSubst (Γ : List SExpr) (σ σ' : Subst) {Δ : List SExpr} (J : ⊩ᵛ Δ) := J.1.EqSubst Γ σ σ'
local notation:65 Γ " ⊩ˢ " σ " ≡ " σ' " : " J:36 => LVEqSubst Γ σ σ' J
local notation:65 Γ " ⊩ˢ " σ " : " J:36 => LVEqSubst Γ σ σ J

def LVIsCtx.nil : ⊩ᵛ [] := ⟨_, .nil⟩
def LVIsCtx.cons {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) : ⊩ᵛ A::Γ := ⟨_, .cons J.2 JA⟩

def LVIsType.sort : Γ ⊩ᵛ[u.succ] .sort u :=
  sorry -- ⟨.sort, fun _ => ⟨.sort _, fun _ _ => ⟨.sort, .rfl⟩⟩⟩

inductive LVIsCtxInv : ∀ {Γ}, ⊩ᵛ Γ → Prop
  | nil : LVIsCtxInv .nil
  | cons (J JA) : LVIsCtxInv (.cons (J := J) (u := u) (A := A) JA)

theorem LVIsCtx.inv (J : ⊩ᵛ Γ) : LVIsCtxInv J :=
  match Γ, J with
  | _, ⟨_, .nil⟩ => .nil
  | _, ⟨_, .cons ..⟩ => .cons ⟨_, _⟩ _

theorem LVEqSubst.left {J : ⊩ᵛ Δ} (H : Γ ⊩ˢ σ ≡ σ' : J) : Γ ⊩ˢ σ : J := J.1.eqSubst_left H

def LVIsType.subst {J : ⊩ᵛ Δ} (H : Γ ⊩ˢ σ : J) (JA : J ⊩ᵛ[u] A) :
    Γ ⊩[u] A.subst σ := (JA.2 H).1

theorem LVEqSubst.eqTy {J : ⊩ᵛ Δ} (H : Γ ⊩ˢ σ ≡ σ' : J) (JA : J ⊩ᵛ[u] A) :
    JA.subst H.left ⊩≡ A.subst σ' := (JA.2 H.left).2 _ H

def LVIsCtx.cons_inv (J : ⊩ᵛ A::Γ) : Σ' (J' : ⊩ᵛ Γ) (u:_) (JA : J' ⊩ᵛ[u] A), J = .cons JA :=
  let ⟨_, .cons J JA⟩ := J; ⟨⟨_, J⟩, _, JA, rfl⟩

theorem LVEqSubst.tail {J : ⊩ᵛ Δ} {JA : J ⊩ᵛ[u] A}
    (H : Γ ⊩ˢ σ ≡ σ' : .cons JA) : Γ ⊩ˢ σ.tail ≡ σ'.tail : J := let ⟨h, _⟩ := H; h

theorem LVEqSubst.head {J : ⊩ᵛ Δ} {JA : J ⊩ᵛ[u] A}
    (H : Γ ⊩ˢ σ ≡ σ' : .cons JA) : JA.subst H.tail.left ⊩ σ.head ≡ σ'.head := let ⟨_, h⟩ := H; h

def LVIsType.lift {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (JB : J ⊩ᵛ[v] B) :
    J.cons JA ⊩ᵛ[v] B.lift := by
  refine ⟨JB.1.weak' .one, fun {Δ σ} (Hσ : LVEqSubst ..) => ⟨?_, fun σ' (Hσ : LVEqSubst ..) => ?_⟩⟩
  · exact (JB.subst (by exact Hσ.tail)).cast SExpr.subst_lift'.symm
  · stop
    refine .cast ?_ _; rw [SExpr.subst_lift']; exact Hσ.tail.eqTy JB

-- def LVEqSubst.lift {J : ⊩ᵛ Δ} {JA : J ⊩ᵛ[u] A} (JB : J ⊩ᵛ[v] B) :
--     Γ ⊩ˢ σ ≡ σ' : J.cons JA := by
--   refine ⟨JB.1.weak' .one, fun {Δ σ} (Hσ : LVEqSubst ..) => ⟨?_, fun σ' (Hσ : LVEqSubst ..) => ?_⟩⟩
--   · exact (JB.subst (by exact Hσ.tail)).cast SExpr.subst_lift'.symm
--   · refine .cast ?_ _; rw [SExpr.subst_lift']; exact Hσ.tail.eqTy JB

def LVEqTy {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (B : SExpr) : Prop :=
  ∀ {Δ σ} (Jσ : Δ ⊩ˢ σ : J), JA.subst Jσ ⊩ A.subst σ ≡ B.subst σ
local notation:65 J " ⊩ᵛ≡ " B:36 => LVEqTy J B

def LVHasType {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (a : SExpr) : Prop :=
  ∀ {Δ σ σ'} (H : Δ ⊩ˢ σ ≡ σ' : J), JA.subst H.left ⊩ a.subst σ ≡ a.subst σ'
local notation:65 J " ⊩ᵛ " a:36 => LVHasType J a

-- theorem LVEqSubst.hasType {J : ⊩ᵛ Δ} (Hσ : Γ ⊩ˢ σ ≡ σ' : J)
--     {JA : J ⊩ᵛ[u] A} (Ha : JA ⊩ᵛ a) : JA.subst Hσ.left ⊩ᵛ a.subst σ :=
--   _

-- def LVHasType.lift {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) {JB : J ⊩ᵛ[v] B} {Ha : JB ⊩ᵛ a} :
--     JA.lift JB ⊩ᵛ a.lift := by
--   refine fun Hσ => Hσ.eqTy _

def LVDefEq {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (a b : SExpr) : Prop :=
  JA ⊩ᵛ a ∧ JA ⊩ᵛ b ∧ ∀ {Δ σ} (Jσ : Δ ⊩ˢ σ : J), JA.subst Jσ ⊩ a.subst σ ≡ b.subst σ
local notation:65 J " ⊩ᵛ " a " ≡ " b:36 => LVDefEq J a b

theorem LVDefEq.refl {J : ⊩ᵛ Γ} {JA : J ⊩ᵛ[u] A} (H : JA ⊩ᵛ a) : JA ⊩ᵛ a ≡ a := ⟨H, H, H⟩
theorem LVDefEq.symm {J : ⊩ᵛ Γ} {JA : J ⊩ᵛ[u] A} : JA ⊩ᵛ a ≡ b → JA ⊩ᵛ b ≡ a
  | ⟨h1, h2, h3⟩ => ⟨h2, h1, fun Hσ => (h3 Hσ).symm⟩

theorem fundamental (H : Γ ⊢ a ≡ b : A) (J : ⊩ᵛ Γ) :
    ∃ u, ∃ JA : J ⊩ᵛ[u] A, JA ⊩ᵛ a ≡ b := by
  induction H with
  | bvar h =>
    induction h with
    | zero =>
      let .cons _ JA := J.inv
      refine ⟨_, ⟨JA.1.weak' .one, fun (Hσ : LVEqSubst ..) => ?_⟩, .refl ?_⟩
      · stop
        exact ⟨(JA.subst Hσ.tail).cast (SExpr.subst_lift' ▸ rfl),
          fun σ' (Hσ : LVEqSubst ..) => .cast (SExpr.subst_lift' ▸ Hσ.tail.eqTy JA) _⟩
      · stop exact (·.2.cast _)
    | @succ _ n B _ h ih =>
      let .cons J JA := J.inv
      have ⟨u, JB, H⟩ := ih J
      refine ⟨_, JA.lift JB, .refl ?_⟩
      stop
      exact fun Hσ => ((H.1 Hσ.tail).cast (SExpr.subst_lift' ▸ rfl)).irrel
  | symm h ih => have ⟨u, JA, H⟩ := ih J; exact ⟨u, JA, H.symm⟩
  | trans _ _ ih1 ih2 =>
    have ⟨u, JA, H⟩ := ih1 J
    have ⟨u', JA', H⟩ := ih2 J
    sorry
  | @sort _ u =>
    stop
    exact ⟨.mk _, .sort, .refl fun _ => Classifier.defEq_self.2 ⟨.sort, ⟨⟩, ⟨⟩⟩⟩
  | _ => sorry
