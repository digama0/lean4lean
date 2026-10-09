import Lean4Lean.Theory.Typing.ChurchRosser

/-!

# Theorems about (weak) head reduction

This includes the proof of the Standardization theorem, based on a proof by Kashima (2000):
Ryo Kashima, "A Proof of the Standardization Theorem in λ-Calculus"
<https://www.is.c.titech.ac.jp/~kashima/pub/C-145.pdf>.

-/

namespace Lean4Lean
open Lean4Lean

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

theorem IsMajorPremise.head (H : IsMajorPremise e) :
    ∃ name levels, e.getAppFnArgs.1 = .const name levels := by
  obtain ⟨p, ⟨r, hp⟩, p₁, p₂, hs, levels, values, hm⟩ := H
  have hn := (Params.constHeaded hp).subpattern (Subpattern.trans (.appL .refl) hs)
  obtain ⟨name, he⟩ := hn.matches_head hm
  exact ⟨name, levels, he⟩

theorem IsMajorPremise.not_rigid (H : IsMajorPremise e) (hrigid : env.Rigid name)
    (hhead : e.getAppFnArgs.1 = .const name levels) : False := by
  obtain ⟨p, ⟨r, hp⟩, p₁, p₂, hs, levels', values, hm⟩ := H
  cases Params.simple_app hp hs
  have hn := matches_constHead hm hhead
  obtain ⟨equation, originalName, originalLevels, hd, hh, he⟩ := pat_storedRule hp
  change p₁.constHead = some originalName at hh
  have heq : originalName = name := Option.some.inj (hh.symm.trans hn)
  subst originalName
  exact hrigid equation hd originalLevels ((VExpr.equationHead_eq _).symm.trans he)

theorem IsMajorPremise.not_caseMajor (H : IsMajorPremise e) (H' : IsCaseMajorPremise env e) : False := by
  obtain ⟨name, levels, hn⟩ := H.head
  obtain ⟨block, owner, packed, hb⟩ := H'.head
  rw [hb] at hn
  cases hn

theorem IsCaseMajorPremise.not_stored_match (H : IsCaseMajorPremise env fn)
    (hp : Pat p r) (hm : p.Matches (.app fn arg) levels values) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  obtain ⟨name, hn⟩ := InductiveSignature.CaseSchema.recursor_pattern_head hm
  obtain ⟨block, owner, packed, hb⟩ := H.head
  rw [case_spine_app] at hn
  change fn.getAppFnArgs.1 = .const name levels at hn
  rw [hb] at hn
  cases hn

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List VExpr) : VExpr → VExpr → Prop where
  | schema : CaseIota env univs Γ e e' → Γ ⊢ e ⤳ e'
  | caseMajor : IsCaseMajorPremise env f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    Γ ⊢ e ⤳ r.1.apply m1 m2

theorem WHRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ⤳ e2) : Γ₂ ⊢ e1 ⤳ e2 := by
  induction H generalizing Γ₂ with
  | schema h => exact .schema (h.defeqDFC henv W)
  | caseMajor hm _ ih => exact .caseMajor hm (ih W)
  | app _ ih1 => exact .app (ih1 W)
  | major h1 _ ih1 => exact .major h1 (ih1 W)
  | beta => exact .beta
  | extra h1 h2 h3 => exact .extra h1 h2 <| h3.map fun a b h => h.defeqDFC henv W

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .schema h => .schema (h.weak' henv W)
  | .caseMajor hm hr => .caseMajor (IsCaseMajorPremise.lift'.2 hm) (hr.weak' W)
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

theorem WHRed.parRed (H : Γ ⊢ e1 ⤳ e2) : Γ ⊢ e1 ≫ e2 := by
  induction H with
  | schema h => exact .of_schema h
  | caseMajor _ _ ih => exact .app .rfl ih
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
  | schema h => exact .schema (h.instN henv H₀ W)
  | caseMajor hm _ ih => exact .caseMajor hm.instN ih
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

theorem WHNF.case_prefix (Hprefix : IsCasePrefix env e) : WHNF Γ e := by
  intro out H
  revert Hprefix
  induction H with
  | schema h => exact fun hp => hp.not_reduction henv h
  | app _ ih => exact fun hp => ih hp.app_left
  | caseMajor hm _ _ => exact fun hp => hm.not_strict_prefix henv hp
  | major hm _ _ =>
    intro hp
    obtain ⟨name, levels, hn⟩ := hm.head
    obtain ⟨block, owner, packed, hb⟩ := hp.app_left.head
    rw [hb] at hn
    cases hn
  | beta => exact fun hp => hp.app_left.not_lam
  | extra hp hm =>
    intro hprefix
    obtain ⟨sp, rfl⟩ := pat_simple hp
    obtain ⟨name, hn⟩ := InductiveSignature.CaseSchema.recursor_pattern_head hm
    obtain ⟨block, owner, levels, hb⟩ := hprefix.head
    rw [hb] at hn
    cases hn

theorem IsCaseMajorPremise.whnf (H : IsCaseMajorPremise env e) : WHNF Γ e :=
  WHNF.case_prefix H.toPrefix

theorem WHNF.rigid_head (hrigid : env.Rigid name)
    (hhead : e.getAppFnArgs.1 = .const name levels) : WHNF Γ e := by
  intro out H
  revert hhead
  induction H with
  | schema h =>
    intro hh
    obtain ⟨_, _, _, hb⟩ := h.head
    rw [hb] at hh
    cases hh
  | app _ ih => exact fun hh => ih ((congrArg Prod.fst (case_spine_app _ _)).symm.trans hh)
  | caseMajor hm _ _ =>
    intro hh
    obtain ⟨_, _, _, hb⟩ := hm.head
    have hh' := (congrArg Prod.fst (case_spine_app _ _)).symm.trans hh
    rw [hb] at hh'
    cases hh'
  | major hm _ _ =>
    intro hh
    exact hm.not_rigid hrigid ((congrArg Prod.fst (case_spine_app _ _)).symm.trans hh)
  | beta => intro hh; cases hh
  | extra hp hm => exact fun hh => Params.not_rigid_match hrigid hp hm hh

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
  | schema h =>
    obtain ⟨name, hn⟩ := (ConstHeaded.varN (p := .const c) trivial).matches_head h4
    obtain ⟨_, _, _, hb⟩ := h.head
    rw [hb] at hn
    cases hn
  | caseMajor hm _ _ =>
    let n+1 := n
    let .var h4 := h4
    obtain ⟨name, hn⟩ := (ConstHeaded.varN (p := .const c) trivial).matches_head h4
    obtain ⟨_, _, _, hb⟩ := hm.head
    rw [hb] at hn
    cases hn
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

theorem WHRed.schema_determ (H : CaseIota env univs Γ e out)
    (H' : Γ ⊢ e ⤳ out') : out = out' := by
  cases H with
  | @iota rule actual hm =>
    generalize he : actual.expr = source at H'
    cases H' with
    | schema hs =>
      subst source
      exact (CaseIota.iota hm).determ henv hs
    | app hf =>
      cases he
      exact False.elim (hm.majorPremise henv |>.whnf _ hf)
    | caseMajor _ hmajor =>
      cases he
      exact False.elim (WHNF.rigid_head hm.ctor_rigid
        (congrArg Prod.fst (InductiveSignature.spine_mkApps_exact _ _ rfl)) _ hmajor)
    | major hnative _ =>
      cases he
      obtain ⟨name, levels, hn⟩ := hnative.head
      rw [InductiveSignature.spine_mkApps_exact _ _ rfl] at hn
      cases hn
    | beta =>
      have hfn := VExpr.app.inj he |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn)
    | extra hp hmatch _ =>
      subst source
      obtain ⟨sp, rfl⟩ := pat_simple hp
      exact False.elim ((CaseIota.iota hm).not_stored_match hmatch)

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | schema h => exact WHRed.schema_determ h H2
  | caseMajor hm ha ih =>
    cases H2 with
    | schema hs => exact (WHRed.schema_determ hs (.caseMajor hm ha)).symm
    | app hf => exact False.elim (hm.whnf _ hf)
    | caseMajor _ ha' => cases ih ha'; rfl
    | major hn _ => exact False.elim (hn.not_caseMajor hm)
    | beta => exact False.elim hm.not_lam
    | extra hp hmatch => exact False.elim (hm.not_stored_match hp hmatch)
  | app l1 ih =>
    cases H2 with
    | schema hs => exact (WHRed.schema_determ hs (.app l1)).symm
    | caseMajor hm _ => exact False.elim (hm.whnf _ l1)
    | app r1 => cases ih r1; rfl
    | major r1 r2 => cases r1.whnf _ l1
    | beta => cases WHNF.lam _ l1
    | extra r1 r2 =>
      cases r2 with
      | app r3 => cases IsMajorPremise.whnf ⟨_, ⟨_, r1⟩, _, _, .refl, _, _, r3⟩ _ l1
      | var => cases pat_not_var r1
  | major l1 l2 ih =>
    cases H2 with
    | schema hs => exact (WHRed.schema_determ hs (.major l1 l2)).symm
    | app r1 => cases l1.whnf _ r1
    | caseMajor hm _ => exact False.elim (l1.not_caseMajor hm)
    | major _ r2 => cases ih r2; rfl
    | beta => cases l1.lam
    | extra r1 r2 =>
      cases r2 with
      | var => cases pat_not_var r1
      | app _ r4 => cases WHNF.subpattern r1 (.appR .refl) nofun r4 _ l2
  | beta =>
    cases H2 with
    | schema hs => exact (WHRed.schema_determ hs .beta).symm
    | app r1 => cases WHNF.lam _ r1
    | major r1 => cases r1.lam
    | caseMajor hm _ => exact False.elim hm.not_lam
    | beta => rfl
    | extra _ r2 => nomatch r2
  | extra l1 l2 lcheck =>
    cases H2 with
    | schema hs => exact (WHRed.schema_determ hs (.extra l1 l2 lcheck)).symm
    | caseMajor hm _ => exact False.elim (hm.not_stored_match l1 l2)
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
      obtain ⟨rfl, rfl⟩ := Pattern.Matches.uniq l2 r2; rfl

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

theorem WHRedS.caseMajor (Hmajor : IsCaseMajorPremise env f) (H : Γ ⊢ a ⤳* a') :
    Γ ⊢ f.app a ⤳* f.app a' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (.caseMajor Hmajor h2)

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

local notation:65 Γ " ⊢ " e1 " ⤳< " e2:36 => StRed Γ e1 e2
inductive StRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ e ⤳* .bvar i → Γ ⊢ e ⤳< .bvar i
  | sort : Γ ⊢ e ⤳* .sort u → Γ ⊢ e ⤳< .sort u
  | const : Γ ⊢ e ⤳* .const c ls → Γ ⊢ e ⤳< .const c ls
  | elim : Γ ⊢ e ⤳* .elim block owner ls → Γ ⊢ e ⤳< .elim block owner ls
  | app : Γ ⊢ e ⤳* .app f a → Γ ⊢ f ⤳< f' → Γ ⊢ a ⤳< a' → Γ ⊢ e ⤳< .app f' a'
  | proj : Γ ⊢ e ⤳* .proj typeName index major →
    Γ ⊢ major ⤳< major' →
    Γ ⊢ e ⤳< .proj typeName index major'
  | lam : Γ ⊢ e ⤳* .lam A body → Γ ⊢ A ⤳< A' → A::Γ ⊢ body ⤳< body' → Γ ⊢ e ⤳< .lam A' body'
  | forallE : Γ ⊢ e ⤳* .forallE A B → Γ ⊢ A ⤳< A' → A::Γ ⊢ B ⤳< B' → Γ ⊢ e ⤳< .forallE A' B'

protected theorem StRed.rfl : ∀ {e}, Γ ⊢ e ⤳< e
  | .bvar _ => .bvar .rfl
  | .sort .. => .sort .rfl
  | .const .. => .const .rfl
  | .elim .. => .elim .rfl
  | .app .. => .app .rfl .rfl .rfl
  | .proj .. => .proj .rfl .rfl
  | .lam .. => .lam .rfl .rfl .rfl
  | .forallE .. => .forallE .rfl .rfl .rfl

theorem StRed.bvar_l (H : Γ ⊢ .bvar i ⤳< e) : e = .bvar i := by
  cases H with
  | bvar h1 | sort h1 | const h1 | elim h1 | app h1 | proj h1 | lam h1 | forallE h1 =>
    cases WHNF.bvar.whRedS h1 <;> rfl

theorem StRed.sort_l (H : Γ ⊢ .sort u ⤳< e) : e = .sort u := by
  cases H with
  | bvar h1 | sort h1 | const h1 | elim h1 | app h1 | proj h1 | lam h1 | forallE h1 =>
    cases WHNF.sort.whRedS h1 <;> rfl

theorem StRed.lam_l (H : Γ ⊢ .lam A B ⤳< e) :
    ∃ A' B', e = .lam A' B' ∧ Γ ⊢ A ⤳< A' ∧ A::Γ ⊢ B ⤳< B' := by
  cases H with
  | bvar h1 | sort h1 | const h1 | elim h1 | app h1 | proj h1 | forallE h1 => cases WHNF.lam.whRedS h1
  | lam h1 h2 h3 => cases WHNF.lam.whRedS h1; exact ⟨_, _, rfl, h2, h3⟩

theorem StRed.forallE_l (H : Γ ⊢ .forallE A B ⤳< e) :
    ∃ A' B', e = .forallE A' B' ∧ Γ ⊢ A ⤳< A' ∧ A::Γ ⊢ B ⤳< B' := by
  cases H with
  | bvar h1 | sort h1 | const h1 | elim h1 | app h1 | proj h1 | lam h1 => cases WHNF.forallE.whRedS h1
  | forallE h1 h2 h3 => cases WHNF.forallE.whRedS h1; exact ⟨_, _, rfl, h2, h3⟩

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem StRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ⤳< e2) : Γ₂ ⊢ e1 ⤳< e2 := by
  induction H generalizing Γ₂ A with
  | bvar h1 => exact .bvar (h1.defeqDFC W)
  | sort h1 => exact .sort (h1.defeqDFC W)
  | const h1 => exact .const (h1.defeqDFC W)
  | elim h1 => exact .elim (h1.defeqDFC W)
  | app h1 _ _ ih1 ih2 =>
    let hΓ := W.isType' hΓ₀; have ⟨_, _, hf, ha⟩ := (h1.hasType hΓ h).app_inv henv hΓ
    exact .app (h1.defeqDFC W) (ih1 W hf) (ih2 W ha)
  | proj h1 _ ihMajor =>
    let hΓ := W.isType' hΓ₀
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      (h1.hasType hΓ h).proj_inv henv hΓ
    exact .proj (h1.defeqDFC W) (ihMajor W hmajor.hasType.2)
  | lam h1 _ _ ih1 ih2 =>
    let hΓ := W.isType' hΓ₀; have ⟨⟨_, hA⟩, _, he⟩ := (h1.hasType hΓ h).lam_inv henv hΓ
    exact .lam (h1.defeqDFC W) (ih1 W hA) (ih2 (W.succ hA) he)
  | forallE h1 _ _ ih1 ih2 =>
    let hΓ := W.isType' hΓ₀; have ⟨⟨_, hA⟩, _, hB⟩ := (h1.hasType hΓ h).forallE_inv henv
    exact .forallE (h1.defeqDFC W) (ih1 W hA) (ih2 (W.succ hA) hB)

theorem StRed.parRedS (H : Γ ⊢ e ⤳< e') : Γ ⊢ e ≫* e' := by
  induction H with
  | bvar h1 | sort h1 | const h1 | elim h1 => exact h1.parRedS
  | app h1 _ _ ih1 ih2 => exact h1.parRedS.trans (ih1.app ih2)
  | proj h1 _ ihMajor => exact h1.parRedS.trans ihMajor.proj
  | lam h1 _ _ ih1 ih2 => exact h1.parRedS.trans (ih1.lam ih2)
  | forallE h1 _ _ ih1 ih2 => exact h1.parRedS.trans (ih1.forallE ih2)

theorem StRed.whRed (H1 : Γ ⊢ e₁ ⤳* e₂) (H2 : Γ ⊢ e₂ ⤳< e') : Γ ⊢ e₁ ⤳< e' := by
  cases H2 with
  | bvar h1 => exact .bvar (H1.trans h1)
  | sort h1 => exact .sort (H1.trans h1)
  | const h1 => exact .const (H1.trans h1)
  | elim h1 => exact .elim (H1.trans h1)
  | app h1 h2 h3 => exact .app (H1.trans h1) h2 h3
  | proj h1 h2 => exact .proj (H1.trans h1) h2
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
  | elim h1 => exact .elim (h1.weak' W)
  | app h1 _ _ ih1 ih2 => exact .app (h1.weak' W) (ih1 W) (ih2 W)
  | proj h1 _ ihMajor => exact .proj (h1.weak' W) (ihMajor W)
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
  | elim h1 => exact .elim (h1.instN H₀' W)
  | app h1 _ _ ih1 ih2 => exact .app (h1.instN H₀' W) (ih1 W) (ih2 W)
  | proj h1 _ ihMajor => exact .proj (h1.instN H₀' W) (ihMajor W)
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.instN H₀' W) (ih1 W) (ih2 W.succ)
  | forallE h1 _ _ ih1 ih2 => exact .forallE (h1.instN H₀' W) (ih1 W) (ih2 W.succ)

theorem StRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, Γ ⊢ m2 a ⤳< m3 a) : Γ ⊢ r.apply m1 m2 ⤳< r.apply m1 m3 := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app .rfl (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

/-- Expose the unchanged head and the source argument spine of a standard
reduction whose target has a constant or abstract eliminator head. -/
theorem StRed.expose_spine
    (hhead : (∃ name levels, head = .const name levels) ∨
      ∃ block owner levels, head = .elim block owner levels)
    (H : Γ ⊢ e ⤳< VExpr.mkApps head arguments) :
    ∃ sourceArgs, Γ ⊢ e ⤳* VExpr.mkApps head sourceArgs ∧
      List.Forall₂ (StRed Γ) sourceArgs arguments := by
  generalize heq : arguments.reverse = revArgs
  have : arguments = revArgs.reverse := by rw [← heq, List.reverse_reverse]
  subst arguments
  clear heq
  induction revArgs generalizing e with
  | nil =>
    rcases hhead with ⟨name, levels, rfl⟩ | ⟨block, owner, levels, rfl⟩
    · let .const h := H
      exact ⟨[], h, .nil⟩
    · let .elim h := H
      exact ⟨[], h, .nil⟩
  | cons arg arguments ih =>
    rw [List.reverse_cons, VExpr.mkApps_append] at H
    change Γ ⊢ e ⤳< .app (VExpr.mkApps head arguments.reverse) arg at H
    let .app hroot hfn harg := H
    rename_i sourceFn sourceArg
    obtain ⟨sourceArgs, hsource, hargs⟩ := ih hfn
    refine ⟨sourceArgs ++ [sourceArg], ?_, ?_⟩
    · rw [VExpr.mkApps_append]
      exact hroot.trans hsource.app
    · simpa only [List.reverse_cons] using List.Forall₂.append' hargs (.cons harg .nil)

open InductiveSignature.CaseSchema in
theorem StRed.expose_case (hm : CaseRedex env univs Γ₂ rule actual)
    (H : Γ ⊢ e ⤳< actual.expr) :
    ∃ source, Γ ⊢ e ⤳* source.expr ∧ CaseApplicationRelated (StRed Γ) source actual := by
  let .app hroot hfn hmajor := H
  obtain ⟨sourceArgs, hfnRed, hargs⟩ := hfn.expose_spine
    (.inr ⟨actual.block, actual.owner, actual.levels, rfl⟩)
  obtain ⟨sourceCtorArgs, hmajorRed, hctorArgs⟩ := hmajor.expose_spine
    (.inl ⟨actual.ctorName, actual.ctorLevels, rfl⟩)
  let source : Application := { actual with arguments := sourceArgs, ctorArguments := sourceCtorArgs }
  refine ⟨source, ?_, ⟨rfl, rfl, rfl, rfl, rfl, hargs, hctorArgs⟩⟩
  have hmajorPremise := hm.majorPremise henv
  obtain ⟨schema, block, owner, levels, args, hlookup, heq, hlen⟩ := hmajorPremise
  have hsourceMajor : IsCaseMajorPremise env
      (VExpr.mkApps (.elim actual.block actual.owner actual.levels) sourceArgs) := by
    have hinj := InductiveSignature.spine_mkApps_exact
      (.elim actual.block actual.owner actual.levels) actual.arguments rfl
    have hinj' := InductiveSignature.spine_mkApps_exact (.elim block owner.val levels) args rfl
    have heq' := congrArg VExpr.getAppFnArgs heq
    rw [hinj, hinj'] at heq'
    have hhead := congrArg Prod.fst heq'
    have hlist := congrArg Prod.snd heq'
    change VExpr.elim actual.block actual.owner actual.levels = .elim block owner.val levels at hhead
    change actual.arguments = args at hlist
    refine ⟨schema, block, owner, levels, sourceArgs, hlookup, ?_, ?_⟩
    · rw [hhead]
    · exact hargs.length_eq.trans ((congrArg List.length hlist).trans hlen)
  exact hroot.trans hfnRed.app |>.trans (hmajorRed.caseMajor hsourceMajor)

open InductiveSignature in
theorem StRed.instantiate_variables {arguments arguments' : List VExpr} (hv : VariableApplications body)
    (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length),
      Γ ⊢ arguments[i] ⤳< arguments'[i]'(by omega))
    (hclosed : body.ClosedN arguments.length) :
    Γ ⊢ instantiateParams body arguments ⤳< instantiateParams body arguments' := by
  induction hv with
  | @bvar i =>
    change i < arguments.length at hclosed
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hclosed, VExpr.instOuter_bvar arguments' (by omega)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by omega)
  | app hf ha ihf iha =>
    exact .app .rfl (ihf hclosed.1) (iha hclosed.2)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CaseApplicationRelated.stRed_defeq
    (H : CaseApplicationRelated (StRed Γ) actual actual')
    (ht : Γ ⊢ actual.expr : type) : CaseApplicationRelated (IsDefEqU env univs Γ) actual actual' := by
  obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
  refine { H with arguments := ?_, ctorArguments := ?_ }
  · exact H.arguments.and_mem.imp fun _ _ h => by
      obtain ⟨type, ht⟩ := schema_mkApps_arg_type hΓ hf h.2.1
      exact ⟨type, h.1.defeq hΓ ht⟩
  · exact H.ctorArguments.and_mem.imp fun _ _ h => by
      obtain ⟨type, ht⟩ := schema_mkApps_arg_type hΓ ha h.2.1
      exact ⟨type, h.1.defeq hΓ ht⟩

theorem CaseApplicationRelated.stRed (H : CaseApplicationRelated (StRed Γ) actual actual') :
    Γ ⊢ actual.expr ⤳< actual'.expr := by
  have mkApps {fn fn' : VExpr} {args args' : List VExpr}
      (hf : Γ ⊢ fn ⤳< fn') (ha : List.Forall₂ (StRed Γ) args args') :
      Γ ⊢ VExpr.mkApps fn args ⤳< VExpr.mkApps fn' args' := by
    induction ha generalizing fn fn' with
    | nil => exact hf
    | cons h ht ih => exact ih (.app .rfl hf h)
  exact .app .rfl (mkApps (by rw [H.block_eq, H.owner_eq, H.levels_eq]; exact .rfl) H.arguments)
    (mkApps (by rw [H.ctor_eq, H.ctorLevels_eq]; exact .rfl) H.ctorArguments)

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem StRed.triangle (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e : A) (H1 : Γ₁ ⊢ e ⤳< e₁) (H2 : Γ₂ ⊢ e₁ ≫ e₂) : Γ₁ ⊢ e ⤳< e₂ := by
  induction H2 generalizing Γ₁ e A with
  | @schema Γ₂ arguments rule actual hm hl hr ih =>
    have hΓ := W.isType' hΓ₀
    obtain ⟨source, hred, hspine⟩ := H1.expose_case hm
    have htyped := hred.hasType hΓ h
    have heq := hspine.stRed.defeq hΓ htyped
    have hdef := hspine.stRed_defeq hΓ htyped
    have hsym : CaseApplicationRelated (IsDefEqU env univs Γ₁) actual source := {
      block_eq := hdef.block_eq.symm
      owner_eq := hdef.owner_eq.symm
      levels_eq := hdef.levels_eq.symm
      ctor_eq := hdef.ctor_eq.symm
      ctorLevels_eq := hdef.ctorLevels_eq.symm
      arguments := hdef.arguments.flip.imp fun _ _ h => IsDefEqU.symm h
      ctorArguments := hdef.ctorArguments.flip.imp fun _ _ h => IsDefEqU.symm h }
    have hm' := (hm.defeqDFC henv (W.symm henv)).congr henv hΓ hsym ⟨_, heq.symm⟩
    have hcapture := hspine.capture (rule := rule)
    have hcaplen := hcapture.length_eq
    refine .whRed (.tail hred (.schema (.iota hm'))) ?_
    have hvars := hm'.source.rhs_variables
    simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq]
    refine StRed.instantiate_variables hvars (hl.trans hcaplen.symm) ?_ hm'.source.closed.2.1
    intro i hi
    have hi' : i < (rule.capture actual).length := by omega
    obtain ⟨type, ht⟩ := hm'.capture_typed (List.getElem_mem hi)
    exact ih i hi' W ht (case_forall₂_get hcapture hi hi')
  | bvar | sort | const | elim => exact H1
  | app b1 b2 ih1 ih2 =>
    let .app a1 a2 a3 := H1
    have hΓ := W.isType' hΓ₀; have ⟨_, _, hf, ha⟩ := (a1.hasType hΓ h).app_inv henv hΓ
    exact .app a1 (ih1 W hf a2) (ih2 W ha a3)
  | proj bMajor ihMajor =>
    let .proj a1 aMajor := H1
    have hΓ := W.isType' hΓ₀
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      (a1.hasType hΓ h).proj_inv henv hΓ
    exact .proj a1 (ihMajor W hmajor.hasType.2 aMajor)
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
    | elim => let .elim H1 := H1; exact ⟨_, _, H1, .elim, nofun⟩
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
