import Lean4Lean.Theory.Typing.ChurchRosser

/-!

# Theorems about (weak) head reduction

This includes the proof of the Standardization theorem, based on a proof by Kashima (2000):
Ryo Kashima, "A Proof of the Standardization Theorem in λ-Calculus"
<https://www.is.c.titech.ac.jp/~kashima/pub/C-145.pdf>.

-/

namespace Lean4Lean
namespace VEnv

open VExpr
variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

omit [Params] in
theorem Subpattern.varN_const (H : Subpattern p (.varN (.const c) n)) :
    ∃ n, p = .varN (.const c) n := by
  generalize eq : Pattern.varN (.const c) n = p' at H
  induction H generalizing n with
  | refl => exact ⟨_, eq.symm⟩
  | appL | appR => cases n <;> cases eq
  | varL _ ih => cases n <;> cases eq; exact ih rfl

theorem Params.simple_app (H : Pat p r) (h : Subpattern (.app p₁ p₂) p) : .app p₁ p₂ = p := by
  obtain ⟨_|_, rfl⟩ := pat_simple H <;> cases h
  · rfl
  · obtain ⟨_|_, ⟨⟩⟩ := Subpattern.varN_const ‹_›
  · obtain ⟨_|_, ⟨⟩⟩ := Subpattern.varN_const ‹_›

def IsMajorPremise (e : VExpr) :=
  ∃ p, (∃ r, Pat p r) ∧ ∃ p₁ p₂, Subpattern (.app p₁ p₂) p ∧ ∃ m1 m2, p₁.Matches e m1 m2

theorem IsMajorPremise.lift' {e ρ} : IsMajorPremise (e.lift' ρ) ↔ IsMajorPremise e := by
  constructor <;> intro ⟨_, h1, _, _, h2, _, _, h3⟩
  · let ⟨_, h4, _⟩ := Pattern.matches_lift'.1 h3
    exact ⟨_, h1, _, _, h2, _, _, h4⟩
  · exact ⟨_, h1, _, _, h2, _, _, Pattern.matches_lift'.2 ⟨_, h3, fun _ => rfl⟩⟩

theorem IsMajorPremise.instN : IsMajorPremise e1 → IsMajorPremise (e1.inst a k)
  | ⟨_, h1, _, _, h2, _, _, h3⟩ => ⟨_, h1, _, _, h2, _, _, Pattern.matches_instN h3⟩

theorem IsMajorPremise.lam : ¬IsMajorPremise (.lam A e) := nofun

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List VExpr) : VExpr → VExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    Γ ⊢ e ⤳ r.1.apply m1 m2

theorem WHRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ⤳ e2) : Γ₂ ⊢ e1 ⤳ e2 := by
  induction H generalizing Γ₂ with
  | app _ ih1 => exact .app (ih1 W)
  | major h1 _ ih1 => exact .major h1 (ih1 W)
  | beta => exact .beta
  | extra h1 h2 h3 => exact .extra h1 h2 <| h3.map fun a b h => h.defeqDFC henv W

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .major h1 h2 => .major (IsMajorPremise.lift'.2 h1) (h2.weak' W)
  | .beta => by rw [VExpr.lift'_inst_hi]; exact .beta
  | .extra h1 h2 h3 => by
    rw [Pattern.RHS.apply_lift']
    refine .extra h1 (Pattern.matches_lift'.2 ⟨_, h2, fun _ => rfl⟩) <| h3.map fun _ _ h => ?_
    simp only [← Pattern.RHS.apply_lift']; exact h.weak' henv W

theorem WHRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ⤳ e2) :
    Γ' ⊢ e1.liftN n k ⤳ e2.liftN n k := by
  simp only [← lift'_consN_skipN]; exact H.weak' (Ctx.liftN_iff_lift'.1 W)

variable! (hΓ : OnCtx Γ' (IsType env univs)) in
theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | major h1 h2 ih =>
    let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl
    exact ⟨_, rfl, .major (IsMajorPremise.lift'.1 h1) a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← VExpr.lift'_inst_hi, VExpr.lift'_inj]; exact .beta
  | extra h1 h2 h3 =>
    subst he
    obtain ⟨_, h4, h5⟩ := Pattern.matches_lift'.1 h2; cases funext h5
    refine ⟨_, (Pattern.RHS.apply_lift' _).symm, .extra h1 h4 <| h3.map fun _ _ h => ?_⟩
    simp only [← Pattern.RHS.apply_lift'] at h
    exact (IsDefEqU.weak'_iff henv hΓ W).1 h

theorem WHRed.parRed (H : Γ ⊢ e1 ⤳ e2) : Γ ⊢ e1 ≫ e2 := by
  induction H with
  | app _ ih => exact .app ih .rfl
  | major _ _ ih => exact .app .rfl ih
  | beta => exact .beta .rfl .rfl
  | extra h1 h2 h3 => exact .extra h1 h2 h3 fun _ => .rfl

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem WHRed.defeq (H : Γ ⊢ e1 ⤳ e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A :=
  H.parRed.defeq hΓ he

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem WHRed.hasType (H : Γ ⊢ e1 ⤳ e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e2 : A := (H.defeq hΓ he).hasType.2

variable! (H₀ : Γ₀ ⊢ a : A₀) in
theorem WHRed.instN (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ⤳ e2) : Γ ⊢ e1.inst a k ⤳ e2.inst a k := by
  induction H with
  | app _ ih => exact .app ih
  | major h1 _ ih => exact .major h1.instN ih
  | beta => rw [(by apply inst_inst_hi : (inst ..).inst _ _ = _)]; exact .beta
  | extra h1 h2 h3 =>
    rw [Pattern.RHS.instN_apply]
    exact .extra h1 (Pattern.matches_instN h2) (h3.instN W H₀)

def WHNF (Γ : List VExpr) (e : VExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.bvar : WHNF Γ (.bvar i) := nofun
theorem WHNF.lam : WHNF Γ (.lam A e) := nofun
theorem WHNF.sort : WHNF Γ (.sort A) := nofun
theorem WHNF.forallE : WHNF Γ (.forallE A B) := nofun

theorem WHNF.subpattern
    (h1 : Pat p r) (h2 : Subpattern p₁ p) (h3 : p₁ ≠ p) (h4 : p₁.Matches e m1 m2) : WHNF Γ e := by
  intro _ H2
  obtain ⟨c, n, rfl⟩ : ∃ c n, p₁ = .varN (.const c) n := by
    obtain ⟨_|_, rfl⟩ := pat_simple h1 <;> cases h2 <;>
      first | cases h3 rfl | exact ⟨_, Subpattern.varN_const ‹_›⟩
  have : ∀ r, ¬Pat (.const c) r := fun _ h => by
    cases (pat_uniq h1 h (.trans (.varN .refl) h2) (Pattern.inter_self _)).1
    exact h3.symm (h2.antisymm (.varN .refl))
  clear h3
  induction H2 generalizing n with
  | app r1 ih => let n+1 := n; let .var h4 := h4; exact ih _ (.trans (.varL .refl) h2) h4
  | major r1 r2 ih =>
    let n+1 := n; let .var h4 := h4
    let ⟨p', ⟨_, h1'⟩, p₁', p₂', h2', _, _, h3'⟩ := r1
    cases simple_app h1' h2'
    obtain ⟨⟨_, n, _⟩ | _, rfl⟩ := pat_simple h1 <;> [skip; cases n <;> cases h2]
    have ⟨_, _, _, a1, a2⟩ := Pattern.matches_inter.1 ⟨⟨_, _, h3'⟩, ⟨_, _, h4⟩⟩
    cases h2 with
    | appL h2 => cases (pat_app_l_uniq h1 h1' .refl .refl h2).symm.trans a1
    | appR h2 =>
      cases (pat_app_uniq h1' h1 .refl .refl .refl (.trans (.varL .refl) h2)).symm.trans a1
  | beta => generalize Pattern.varN .. = p' at m1 m2 h4; nomatch h4
  | extra r1 r2 r3 =>
    have ⟨_, _, _, a1, a2⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, h4⟩⟩
    obtain ⟨⟨_, m, _⟩ | _, rfl⟩ := pat_simple h1 <;> [skip; cases n <;> cases h2]
    obtain ⟨rfl, eq, _⟩ := pat_uniq h1 r1 h2 a1
    cases n <;> cases eq
    exact this _ h1

theorem IsMajorPremise.whnf : IsMajorPremise e → WHNF Γ e := by
  rintro ⟨p, ⟨_, h1⟩, p₁, p₂, h2, _, _, h3⟩
  refine .subpattern h1 (.trans (.appL .refl) h2) ?_ h3
  rintro rfl; cases h2.antisymm (.appL .refl)

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | major r1 r2 => cases r1.whnf _ l1
    | beta => cases WHNF.lam _ l1
    | extra r1 r2 =>
      cases r2 with
      | app r3 => cases IsMajorPremise.whnf ⟨_, ⟨_, r1⟩, _, _, .refl, _, _, r3⟩ _ l1
      | var => cases pat_not_var r1
  | major l1 l2 ih =>
    cases H2 with
    | app r1 => cases l1.whnf _ r1
    | major _ r2 => cases ih r2; rfl
    | beta => cases l1.lam
    | extra r1 r2 =>
      cases r2 with
      | var => cases pat_not_var r1
      | app _ r4 => cases WHNF.subpattern r1 (.appR .refl) nofun r4 _ l2
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | major r1 => cases r1.lam
    | beta => rfl
    | extra _ r2 => nomatch r2
  | extra l1 l2 =>
    cases H2 with
    | beta => nomatch l2
    | major r1 r2 =>
      cases l2 with
      | var => cases pat_not_var l1
      | app _ l4 => cases WHNF.subpattern l1 (.appR .refl) nofun l4 _ r2
    | app r1 =>
      cases l2 with
      | app l3 => cases IsMajorPremise.whnf ⟨_, ⟨_, l1⟩, _, _, .refl, _, _, l3⟩ _ r1
      | var => cases pat_not_var l1
    | extra r1 r2 =>
      have ⟨_, _, _, a1, a2⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, l2⟩⟩
      obtain ⟨rfl, -, ⟨⟩⟩ := pat_uniq l1 r1 .refl a1
      obtain ⟨rfl, rfl⟩ := Pattern.matches_determ l2 r2; rfl

def WHRedS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (WHRed Γ)
local notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ⤳* e2) : Γ₂ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.defeqDFC W)

theorem WHRedS.parRedS (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1 ≫* e2 := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.parRed

theorem WHRedS.app (H : Γ ⊢ f ⤳* f') : Γ ⊢ f.app a ⤳* f'.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.major (H1 : IsMajorPremise f) (H : Γ ⊢ a ⤳* a') : Γ ⊢ f.app a ⤳* f.app a' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.major H1)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A :=
  H.parRedS.defeq hΓ he

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem WHRedS.hasType (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e2 : A :=
  (H.defeq hΓ he).hasType.2

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Γ')
    (H : Γ ⊢ e1 ⤳* e2) : Γ' ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ⤳* e2) :
    Γ' ⊢ e1.liftN n k ⤳* e2.liftN n k := by
  simp only [← lift'_consN_skipN]; exact H.weak' (Ctx.liftN_iff_lift'.1 W)

theorem WHRedS.instN (H₀ : Γ₀ ⊢ a : A₀) (W : Ctx.InstN Γ₀ a A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ⤳* e2) : Γ ⊢ e1.inst a k ⤳* e2.inst a k := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.instN H₀ W)

theorem WHNF.whRedS (H : WHNF Γ e) (H2 : Γ ⊢ e ⤳* e') : e = e' := by
  cases H2 using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases H _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

variable! (hΔ : OnCtx Δ (IsType env univs)) in
theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv hΔ W
    exact ⟨_, rfl, .tail a1 a2⟩

local notation:65 Γ " ⊢ " e1 " ⤳< " e2:36 => StRed Γ e1 e2
inductive StRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ e ⤳* .bvar i → Γ ⊢ e ⤳< .bvar i
  | sort : Γ ⊢ e ⤳* .sort u → Γ ⊢ e ⤳< .sort u
  | const : Γ ⊢ e ⤳* .const c ls → Γ ⊢ e ⤳< .const c ls
  | app : Γ ⊢ e ⤳* .app f a → Γ ⊢ f ⤳< f' → Γ ⊢ a ⤳< a' → Γ ⊢ e ⤳< .app f' a'
  | lam : Γ ⊢ e ⤳* .lam A body → Γ ⊢ A ⤳< A' → A::Γ ⊢ body ⤳< body' → Γ ⊢ e ⤳< .lam A' body'
  | forallE : Γ ⊢ e ⤳* .forallE A B → Γ ⊢ A ⤳< A' → A::Γ ⊢ B ⤳< B' → Γ ⊢ e ⤳< .forallE A' B'

protected theorem StRed.rfl : ∀ {e}, Γ ⊢ e ⤳< e
  | .bvar _ => .bvar .rfl
  | .sort .. => .sort .rfl
  | .const .. => .const .rfl
  | .app .. => .app .rfl .rfl .rfl
  | .lam .. => .lam .rfl .rfl .rfl
  | .forallE .. => .forallE .rfl .rfl .rfl

theorem StRed.bvar_l (H : Γ ⊢ .bvar i ⤳< e) : e = .bvar i := by
  cases H with
  | bvar h1 | sort h1 | const h1 | app h1 | lam h1 | forallE h1 => cases WHNF.bvar.whRedS h1 <;> rfl

theorem StRed.sort_l (H : Γ ⊢ .sort u ⤳< e) : e = .sort u := by
  cases H with
  | bvar h1 | sort h1 | const h1 | app h1 | lam h1 | forallE h1 => cases WHNF.sort.whRedS h1 <;> rfl

theorem StRed.lam_l (H : Γ ⊢ .lam A B ⤳< e) :
    ∃ A' B', e = .lam A' B' ∧ Γ ⊢ A ⤳< A' ∧ A::Γ ⊢ B ⤳< B' := by
  cases H with
  | bvar h1 | sort h1 | const h1 | app h1 | forallE h1 => cases WHNF.lam.whRedS h1
  | lam h1 h2 h3 => cases WHNF.lam.whRedS h1; exact ⟨_, _, rfl, h2, h3⟩

theorem StRed.forallE_l (H : Γ ⊢ .forallE A B ⤳< e) :
    ∃ A' B', e = .forallE A' B' ∧ Γ ⊢ A ⤳< A' ∧ A::Γ ⊢ B ⤳< B' := by
  cases H with
  | bvar h1 | sort h1 | const h1 | app h1 | lam h1 => cases WHNF.forallE.whRedS h1
  | forallE h1 h2 h3 => cases WHNF.forallE.whRedS h1; exact ⟨_, _, rfl, h2, h3⟩

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem StRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ⤳< e2) : Γ₂ ⊢ e1 ⤳< e2 := by
  induction H generalizing Γ₂ A with
  | bvar h1 => exact .bvar (h1.defeqDFC W)
  | sort h1 => exact .sort (h1.defeqDFC W)
  | const h1 => exact .const (h1.defeqDFC W)
  | app h1 _ _ ih1 ih2 =>
    let hΓ := W.isType' hΓ₀; have ⟨_, _, hf, ha⟩ := (h1.hasType hΓ h).app_inv henv hΓ
    exact .app (h1.defeqDFC W) (ih1 W hf) (ih2 W ha)
  | lam h1 _ _ ih1 ih2 =>
    let hΓ := W.isType' hΓ₀; have ⟨⟨_, hA⟩, _, he⟩ := (h1.hasType hΓ h).lam_inv henv hΓ
    exact .lam (h1.defeqDFC W) (ih1 W hA) (ih2 (W.succ hA) he)
  | forallE h1 _ _ ih1 ih2 =>
    let hΓ := W.isType' hΓ₀; have ⟨⟨_, hA⟩, _, hB⟩ := (h1.hasType hΓ h).forallE_inv henv
    exact .forallE (h1.defeqDFC W) (ih1 W hA) (ih2 (W.succ hA) hB)

theorem StRed.parRedS (H : Γ ⊢ e ⤳< e') : Γ ⊢ e ≫* e' := by
  induction H with
  | bvar h1 | sort h1 | const h1 => exact h1.parRedS
  | app h1 _ _ ih1 ih2 => exact h1.parRedS.trans (ih1.app ih2)
  | lam h1 _ _ ih1 ih2 => exact h1.parRedS.trans (ih1.lam ih2)
  | forallE h1 _ _ ih1 ih2 => exact h1.parRedS.trans (ih1.forallE ih2)

theorem StRed.whRed (H1 : Γ ⊢ e₁ ⤳* e₂) (H2 : Γ ⊢ e₂ ⤳< e') : Γ ⊢ e₁ ⤳< e' := by
  cases H2 with
  | bvar h1 => exact .bvar (H1.trans h1)
  | sort h1 => exact .sort (H1.trans h1)
  | const h1 => exact .const (H1.trans h1)
  | app h1 h2 h3 => exact .app (H1.trans h1) h2 h3
  | lam h1 h2 h3 => exact .lam (H1.trans h1) h2 h3
  | forallE h1 h2 h3 => exact .forallE (H1.trans h1) h2 h3

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem StRed.defeq (H : Γ ⊢ e1 ⤳< e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A :=
  H.parRedS.defeq hΓ he

theorem StRed.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ⤳< e2) :
    Γ' ⊢ e1.lift' ρ ⤳< e2.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h1 => exact .bvar (h1.weak' W)
  | sort h1 => exact .sort (h1.weak' W)
  | const h1 => exact .const (h1.weak' W)
  | app h1 _ _ ih1 ih2 => exact .app (h1.weak' W) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.weak' W) (ih1 W) (ih2 W.cons)
  | forallE h1 _ _ ih1 ih2 => exact .forallE (h1.weak' W) (ih1 W) (ih2 W.cons)

theorem StRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ⤳< e2) :
    Γ' ⊢ e1.liftN n k ⤳< e2.liftN n k := by
  simp only [← lift'_consN_skipN]; exact H.weak' (Ctx.liftN_iff_lift'.1 W)

variable! (H₀ : Γ₀ ⊢ a1 ⤳< a2) (H₀' : Γ₀ ⊢ a1 : A₀) in
theorem StRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ⤳< e2) : Γ ⊢ e1.inst a1 k ⤳< e2.inst a2 k := by
  induction H generalizing Γ k with
  | @bvar _ e i h1 =>
    refine .whRed (h1.instN H₀' W) ?_; clear h1
    induction W generalizing i with
    | zero =>
      cases i with simp [inst]
      | zero => exact .whRed .rfl H₀
      | succ i => exact .bvar .rfl
    | succ _ ih =>
      cases i with simp [inst]
      | zero => exact .bvar .rfl
      | succ h => exact ih.weakN .one
  | sort h1 => exact .sort (h1.instN H₀' W)
  | const h1 => exact .const (h1.instN H₀' W)
  | app h1 _ _ ih1 ih2 => exact .app (h1.instN H₀' W) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.instN H₀' W) (ih1 W) (ih2 W.succ)
  | forallE h1 _ _ ih1 ih2 => exact .forallE (h1.instN H₀' W) (ih1 W) (ih2 W.succ)

theorem StRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, Γ ⊢ m2 a ⤳< m3 a) : Γ ⊢ r.apply m1 m2 ⤳< r.apply m1 m3 := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app .rfl (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem StRed.triangle (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e : A) (H1 : Γ₁ ⊢ e ⤳< e₁) (H2 : Γ₂ ⊢ e₁ ≫ e₂) : Γ₁ ⊢ e ⤳< e₂ := by
  induction H2 generalizing Γ₁ e A with
  | bvar | sort | const => exact H1
  | app b1 b2 ih1 ih2 =>
    let .app a1 a2 a3 := H1
    have hΓ := W.isType' hΓ₀; have ⟨_, _, hf, ha⟩ := (a1.hasType hΓ h).app_inv henv hΓ
    exact .app a1 (ih1 W hf a2) (ih2 W ha a3)
  | lam b1 b2 ih1 ih2 =>
    let .lam a1 a2 a3 := H1
    have hΓ := W.isType' hΓ₀; have ⟨⟨_, hA⟩, _, he⟩ := (a1.hasType hΓ h).lam_inv henv hΓ
    exact .lam a1 (ih1 W hA a2) (ih2 (W.succ (a2.defeq hΓ hA)) he.hasType.1 a3)
  | forallE b1 b2 ih1 ih2 =>
    let .forallE a1 a2 a3 := H1
    have hΓ := W.isType' hΓ₀; have ⟨⟨_, hA⟩, _, he⟩ := (a1.hasType hΓ h).forallE_inv henv
    exact .forallE a1 (ih1 W hA a2) (ih2 (W.succ (a2.defeq hΓ hA)) he.hasType.1 a3)
  | beta _ _ ih1 ih2 =>
    let .app a1 a2 a3 := H1; let .lam a4 a5 a6 := a2
    have hΓ := W.isType' hΓ₀; have ⟨_, _, hf, ha⟩ := (a1.hasType hΓ h).app_inv henv hΓ
    have c1 := a4.hasType hΓ hf; have ⟨⟨_, hA⟩, _, he⟩ := c1.lam_inv henv hΓ
    have ⟨⟨_, u1⟩, _, u2⟩ := (c1.uniqU henv hΓ (hA.lam he)).forallE_inv henv hΓ
    exact .whRed (a1.trans a4.app |>.tail .beta) <|
      (ih2 W ha a3).instN (u1.defeq ha) .zero (ih1 (W.succ (a5.defeq hΓ hA)) he a6)
  | @extra p r e₁ m1 m2 Γ₂ m2' h1 h2 h3 _ ih =>
    have hΓ := W.isType' hΓ₀
    suffices ∀ p' m1 m2, Subpattern p' p → p'.Matches e₁ m1 m2 →
         ∃ e₁ m3, Γ₁ ⊢ e ⤳* e₁ ∧ p'.Matches e₁ m1 m3 ∧ (∀ x, Γ₁ ⊢ m3 x ⤳< m2 x) by
      let ⟨e₁, m3, a1, a2, a3⟩ := this _ _ _ .refl h2
      have := (a1.hasType hΓ h).matches_inv hΓ a2
      refine .whRed (.tail a1 (.extra h1 a2 <| h3.map fun a b ⟨_, h⟩ => ?_))
        (.apply_pat _ fun x => let ⟨_, h⟩ := this x; ih x W h (a3 x))
      replace h := h.defeqDFC henv (W.symm henv)
      refine have {r} := IsDefEq.apply_pat hΓ (r := r) fun a A h => ?_
        ⟨_, (this h.hasType.1).symm.trans <| h.trans (this h.hasType.2)⟩
      let ⟨_, h'⟩ := this a; exact ⟨_, ((a3 a).defeq hΓ h').symm⟩
    clear h2 ih h; intro p' m1 m2 hp h2
    induction h2 generalizing e with
    | const => let .const H1 := H1; exact ⟨_, _, H1, .const, nofun⟩
    | app l1 l2 ih1 ih2 =>
      let .app r1 r2 r3 := H1
      have ⟨_, _, a1, a2, a3⟩ := ih1 r2 (.trans (.appL .refl) hp)
      have ⟨_, _, b1, b2, b3⟩ := ih2 r3 (.trans (.appR .refl) hp)
      refine ⟨_, _, r1.trans a1.app |>.trans (b1.major ?_), .app a2 b2, (·.casesOn a3 b3)⟩
      exact ⟨_, ⟨_, h1⟩, _, _, hp, _, _, a2⟩
    | var l1 ih1 =>
      let .app r1 r2 r3 := H1
      have ⟨_, _, a1, a2, a3⟩ := ih1 r2 (.trans (.varL .refl) hp)
      refine ⟨_, _, r1.trans a1.app, .var a2, (·.casesOn r3 a3)⟩

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem StRed.triangleS (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e : A) (H1 : Γ₁ ⊢ e ⤳< e₁) (H2 : Γ₂ ⊢ e₁ ≫* e₂) : Γ₁ ⊢ e ⤳< e₂ := by
  induction H2 with
  | rfl => exact H1
  | tail _ h2 ih => exact ih.triangle hΓ₀ W h h2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.standard (h : Γ ⊢ e : A) (H : Γ ⊢ e ≫* e') : Γ ⊢ e ⤳< e' :=
  .triangleS hΓ .zero h .rfl H

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem IsDefEq.reduce_sort (H : Γ ⊢ e ≡ .sort u : A) :
    ∃ u', Γ ⊢ e ⤳* .sort u' ∧ u' ≈ u := by
  have ⟨_, _, e', _, h1, h2, h3⟩ := H.church_rosser hΓ
  cases (h2.standard hΓ H.hasType.2).sort_l
  have hu := H.hasType.2.sort_inv henv
  obtain ⟨v, rfl, a1⟩ : ∃ v, e' = sort v ∧ v ≈ u := by
    cases h3 with
    | refl => exact ⟨_, rfl, rfl⟩
    | sortDF _ _ h => exact ⟨_, rfl, h⟩
    | etaL h => cases ((HasType.sort hu).uniqU henv hΓ h).sort_forallE_inv henv hΓ
    | proofIrrel h1 _ h3 =>
      have := h1.defeqU_l henv hΓ ((HasType.sort hu).uniqU henv hΓ h3).symm
      have := ((HasType.sort (by exact hu)).uniqU henv hΓ this).sort_inv henv hΓ
      cases congrFun this []
  let .sort h1 := h1.standard hΓ H.hasType.1
  exact ⟨_, h1, a1⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem IsDefEq.reduce_forallE (H : Γ ⊢ e ≡ .forallE A B : V) :
    ∃ A' B', Γ ⊢ e ⤳* .forallE A' B' := by
  have ⟨_, _, e', _, h1, h2, h3⟩ := H.church_rosser hΓ
  obtain ⟨A₁, B₁, rfl, eA, eB⟩ := (h2.standard hΓ H.hasType.2).forallE_l
  have ⟨⟨_, hA⟩, _, hB⟩ := H.hasType.2.forallE_inv henv
  have hA₁ := eA.parRedS.defeq hΓ hA
  have hB₁ := eB.parRedS.hasType (by exact ⟨hΓ, _, hA⟩) hB |>.defeq_l henv hA₁
  obtain ⟨_, _, rfl⟩ : ∃ A' B', e' = .forallE A' B' := by
    cases h3 with
    | refl
    | forallEDF _ _ h => exact ⟨_, _, rfl⟩
    | etaL h => cases ((hA₁.hasType.2.forallE hB₁).uniqU henv hΓ h).sort_forallE_inv henv hΓ
    | proofIrrel h1 _ h3 =>
      have := h1.defeqU_l henv hΓ ((hA₁.hasType.2.forallE hB₁).uniqU henv hΓ h3).symm
      have := ((HasType.sort (by exact this.sort_inv henv)).uniqU henv hΓ this).sort_inv henv hΓ
      cases congrFun this []
  let .forallE h1 .. := h1.standard hΓ H.hasType.1
  exact ⟨_, _, h1⟩

scoped notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : u.WF univs → Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ ci.type.instL ls
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A : .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem InferType.hasType (H : Γ ⊢ e ▷ A) : Γ ⊢ e : A := by
  induction H with
  | bvar h1 => exact .bvar h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 h3 ih =>
    have ⟨_, h⟩ := (ih hΓ).isType henv hΓ
    exact .app (.defeq (h2.defeq hΓ h) (ih hΓ)) h3
  | lam h1 h2 ih => exact .lam h1 (ih ⟨hΓ, _, h1⟩)
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    have ⟨_, hU⟩ := (ih1 hΓ).isType henv hΓ
    have hA := (h2.defeq hΓ hU).defeq (ih1 hΓ)
    refine have hΓ' := ⟨hΓ, _, hA⟩; have ⟨_, hV⟩ := (ih2 hΓ').isType henv hΓ'; ?_
    exact .forallE hA ((h4.defeq hΓ' hV).defeq (ih2 hΓ'))

theorem InferType.determ (H1 : Γ ⊢ e ▷ A) (H2 : Γ ⊢ e ▷ A') : A = A' := by
  induction H1 generalizing A' with
  | bvar h1 => cases H2 with | bvar h2 => exact h1.uniq h2
  | sort => cases H2; rfl
  | const l1 l2 => cases H2 with | const r1 r2 => cases l1.symm.trans r1; rfl
  | app l1 l2 _ ih =>
    cases H2 with | app r1 r2 => cases ih r1; cases l2.determ .forallE r2 .forallE; rfl
  | lam _ l2 ih => cases H2 with | lam _ r2 => cases ih r2; rfl
  | forallE l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with | forallE r1 r2 r3 r4
    cases ih1 r1; cases l2.determ .sort r2 .sort
    cases ih2 r3; cases l4.determ .sort r4 .sort; rfl

theorem InferType.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷ A → Δ ⊢ e.lift' ρ ▷ A.lift' ρ
  | .bvar h => .bvar (h.weak' W)
  | .sort h1 => .sort h1
  | .const h1 h2 h3 => by rw [(henv.ordered.closedC h1).instL.lift'_eq .zero]; exact .const h1 h2 h3
  | .app h1 h2 h3 => VExpr.lift'_inst_hi .. ▸ .app (h1.weak' W) (h2.weak' W) (h3.weak' henv W)
  | .lam h1 h2 => .lam (h1.weak' henv W) (h2.weak' W.cons)
  | .forallE h1 h2 h3 h4 => .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons)

theorem InferType.weakN (W : Ctx.LiftN n k Γ Δ)
    (H : Γ ⊢ e ▷ A) : Δ ⊢ e.liftN n k ▷ A.liftN n k := by
  simp [← VExpr.lift'_consN_skipN]
  exact H.weak' (Ctx.liftN_iff_lift'.1 W)

variable! (hΔ : OnCtx Δ (IsType env univs)) in
theorem InferType.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷ A := by
  generalize he : e.lift' ρ = e' at H
  induction H generalizing Γ ρ e with
  | bvar h => let .bvar _ := e; cases he; let ⟨_, h1, h2⟩ := h.weakU_inv W; exact ⟨_, h1, .bvar h2⟩
  | sort h1 => let .sort _ := e; cases he; exact ⟨_, rfl, .sort h1⟩
  | const h1 h2 h3 =>
    let .const .. := e; cases he
    exact ⟨_, ((henv.ordered.closedC h1).instL.lift'_eq .zero).symm, .const h1 h2 h3⟩
  | app h1 h2 h3 ih =>
    let .app .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih hΔ W rfl
    obtain ⟨F, a2, a3⟩ := h2.weakU_inv hΔ W; cases F <;> cases a2
    refine ⟨_, by rw [VExpr.lift'_inst_hi], .app a1 a3 ((IsDefEq.weak'_iff henv hΔ W).1 h3)⟩
  | lam h1 h2 ih =>
    let .lam .. := e; cases he
    obtain ⟨_, rfl, a2⟩ := ih ⟨hΔ, _, h1⟩ W.cons rfl
    exact ⟨_, rfl, .lam ((IsDefEq.weak'_iff henv hΔ W).1 h1) a2⟩
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    let .forallE .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih1 hΔ W rfl
    obtain ⟨U, a2, a3⟩ := h2.weakU_inv hΔ W; cases U <;> cases a2
    have hΓ := hΔ.weak'_inv henv W
    have := a1.hasType hΓ
    have ⟨_, hU⟩ := this.isType henv hΓ
    have hA := (a3.defeq hΓ hU).defeq this
    refine have hΔ' := ⟨hΔ, _, hA.weak' henv W⟩; have := ih2 hΔ' W.cons rfl; ?_
    obtain ⟨_, rfl, b1⟩ := this
    obtain ⟨V, b2, b3⟩ := h4.weakU_inv hΔ' W.cons; cases V <;> cases b2
    exact ⟨_, rfl, .forallE a1 a3 b1 b3⟩

variable! (hΔ : OnCtx Δ (IsType env univs)) in
theorem InferType.weak'_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A.lift' ρ) : Γ ⊢ e ▷ A := by
  obtain ⟨_, h1, h2⟩ := H.weakU_inv hΔ W
  exact VExpr.lift'_inj.1 h1 ▸ h2

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs))
  (hΓ : OnCtx Γ₁ (IsType env univs)) (h₀ : Γ₀ ⊢ e₀ ▷ A₀) in
theorem InferType.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e ▷ A) :
    Γ ⊢ e.inst e₀ k ▷ A.inst e₀ k := by
  induction H generalizing Γ k with
  | @bvar _ i ty h =>
    dsimp [inst]
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h => exact .bvar h
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
      | zero => exact .bvar .zero
      | succ h => exact (ih h hΓ.1).weakN .one
  | sort h1 => exact .sort h1
  | const h1 h2 h3 =>
    rw [(henv.ordered.closedC h1).instL.instN_eq (Nat.zero_le _)]; exact .const h1 h2 h3
  | app h1 h2 h3 ih =>
    exact VExpr.inst_inst_hi .. ▸
      .app (ih hΓ W) (h2.instN (h₀.hasType hΓ₀) W) (h3.instN henv W (h₀.hasType hΓ₀))
  | lam h1 h2 ih => exact .lam (h1.instN henv W (h₀.hasType hΓ₀)) (ih ⟨hΓ, _, h1⟩ W.succ)
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    have ⟨_, hU⟩ := (h1.hasType hΓ).isType henv hΓ
    have hA := (h2.defeq hΓ hU).defeq (h1.hasType hΓ)
    exact .forallE (ih1 hΓ W) (h2.instN (h₀.hasType hΓ₀) W)
      (ih2 ⟨hΓ, _, hA⟩ W.succ) (h4.instN (h₀.hasType hΓ₀) W.succ)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem InferType.inst (H₀ : Γ ⊢ a ▷ A₀) (H : A₀::Γ ⊢ e ▷ A) :
    Γ ⊢ e.inst a ▷ A.inst a :=
  have ⟨_, hA⟩ := (H₀.hasType hΓ).isType henv hΓ
  .instN hΓ (by exact ⟨hΓ, _, hA⟩) H₀ .zero H

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem InferType.exists (H : Γ ⊢ a : A) : ∃ A', Γ ⊢ a ▷ A' := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize true = b at H
  induction H with
  | base _ ih | defeq _ _ _ _ _ _ _ ih => exact ih hΓ
  | bvar h1 => exact ⟨_, .bvar h1⟩
  | sort' h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app _ _ _ _ _ h1 h2 _ _ _ _ ih1 =>
    let ⟨F, hF⟩ := ih1 hΓ
    have ⟨_, h⟩ := (hF.hasType hΓ).uniq henv hΓ h1.hasType
    have ⟨_, _, rF⟩ := h.reduce_forallE hΓ
    have ⟨⟨_, hA⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ ⟨_, (rF.defeq hΓ h.hasType.1).symm.trans h⟩
    exact ⟨_, .app hF rF (hA.symm.defeq h2.hasType)⟩
  | lam _ _ h1 _ h2 _ ih1 _ ih2 =>
    let ⟨B, hB⟩ := ih2 ⟨hΓ, _, h1.hasType⟩
    exact ⟨_, .lam h1.hasType hB⟩
  | forallE _ _ h1 h2 ih1 ih2 =>
    let ⟨U, hU⟩ := ih1 hΓ
    have ⟨_, h⟩ := (hU.hasType hΓ).uniq henv hΓ h1.hasType
    have ⟨_, rU, _⟩ := h.reduce_sort hΓ
    refine have hΓ' := ⟨hΓ, _, h1.hasType⟩; let ⟨V, hV⟩ := ih2 hΓ'; ?_
    have ⟨_, h⟩ := (hV.hasType hΓ').uniq henv hΓ' h2.hasType
    have ⟨_, rV, _⟩ := h.reduce_sort hΓ'
    exact ⟨_, .forallE hU rU hV rV⟩

def InferTypeS (Γ : List VExpr) (e A : VExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
scoped notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem InferTypeS.hasType : Γ ⊢ e ▷* A → Γ ⊢ e : A
  | ⟨_, h1, h2⟩ =>
    let ⟨_, h3⟩ := (h1.hasType hΓ).isType henv hΓ
    (h2.defeq hΓ h3).defeq (h1.hasType hΓ)

theorem WHRedS.inferType
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem InferTypeS.determ
    (H1 : Γ ⊢ e ▷* A) (W1 : WHNF Γ A)
    (H2 : Γ ⊢ e ▷* A') (W2 : WHNF Γ A') : A = A' := by
  let ⟨_, h1, h2⟩ := H1; let ⟨_, h3, h4⟩ := H2
  cases h1.determ h3; exact h2.determ W1 h4 W2

theorem InferTypeS.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷* A → Δ ⊢ e.lift' ρ ▷* A.lift' ρ
  | ⟨_, h1, h2⟩ => ⟨_, h1.weak' W, h2.weak' W⟩

variable! (hΔ : OnCtx Δ (IsType env univs)) in
theorem InferTypeS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷* A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷* A := by
  let ⟨_, h1, h2⟩ := H
  obtain ⟨_, rfl, a1⟩ := h1.weakU_inv hΔ W
  obtain ⟨_, rfl, a2⟩ := h2.weakU_inv hΔ W
  exact ⟨_, rfl, _, a1, a2⟩
