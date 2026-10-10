import Lean4Lean.Verify.Typing.Lemmas

/-! Semantic embeddings of checking contexts and transport of typing judgements. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The semantic checker context `Δc` embeds into the main semantic context
`Δ`: it weakens into a context definitionally equal to `Δ`. -/
def ChkEmbeds (env : VEnv) (U : Nat) (Δc Δ : VLCtx) : Prop :=
  ∃ Δ' n, VLCtx.FVLift' Δc Δ' 0 n 0 ∧ VLCtx.IsDefEq env U Δ' Δ

theorem _root_.Lean4Lean.VLCtx.IsDefEq.isFVarUpSet {env : VEnv} {U : Nat} {P : FVarId → Prop} :
    ∀ {Δ₁ Δ₂ : VLCtx}, VLCtx.IsDefEq env U Δ₁ Δ₂ →
      (IsFVarUpSet P Δ₁ ↔ IsFVarUpSet P Δ₂)
  | _, _, .nil => .rfl
  | (none, _) :: _, (none, _) :: _, .cons H _ _ => H.isFVarUpSet
  | (some (_, _), _) :: _, (some (_, _), _) :: _, .cons H _ _ =>
    and_congr H.isFVarUpSet .rfl

theorem _root_.Lean4Lean.VLCtx.FVLift'.isFVarUpSet {P : FVarId → Prop} {Δ Δ' : VLCtx}
    {dk k : Nat} {n : Lift} (W : VLCtx.FVLift' Δ Δ' dk n k) (H : IsFVarUpSet P Δ') :
    IsFVarUpSet P Δ := by
  induction W with
  | refl => exact H
  | skip_fvar fv d _ ih => obtain ⟨fv, deps⟩ := fv; exact ih H.1
  | cons_fvar fv d _ _ ih => obtain ⟨fv, deps⟩ := fv; exact ⟨ih H.1, H.2⟩
  | cons_bvar d _ ih => exact ih H

namespace ChkEmbeds

variable {env : VEnv} {U : Nat} {Δc Δ : VLCtx}

theorem fvars_subset (H : ChkEmbeds env U Δc Δ) : Δc.fvars ⊆ Δ.fvars := by
  obtain ⟨Δ', n, W, hD⟩ := H
  rw [← hD.fvars]
  exact W.fvars_sublist.subset

theorem isFVarUpSet (H : ChkEmbeds env U Δc Δ) {P : FVarId → Prop}
    (hP : IsFVarUpSet P Δ) : IsFVarUpSet P Δc := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact W.isFVarUpSet (hD.isFVarUpSet.2 hP)

theorem refl (henv : VEnv.OrderedStrong env) (hΔ : VLCtx.WF env U Δ) : ChkEmbeds env U Δ Δ :=
  ⟨Δ, .refl, .refl, .refl henv hΔ⟩

theorem from_nil (henv : VEnv.OrderedStrong env) (hΔ : VLCtx.WF env U Δ) (hb : Δ.NoBV) :
    ChkEmbeds env U [] Δ :=
  ⟨Δ, _, .from_nil hb, .refl henv hΔ⟩

theorem mono {env' : VEnv} (hle : env ≤ env') (H : ChkEmbeds env U Δc Δ) :
    ChkEmbeds env' U Δc Δ := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact ⟨Δ', n, W, hD.mono hle⟩

/-- Opening a binder only in the main context keeps the embedding. -/
theorem skip (henv : VEnv.OrderedStrong env) (H : ChkEmbeds env U Δc Δ)
    (hfresh : fv ∉ Δ.fvars) (hdeps : deps ⊆ Δ.fvars)
    (hA : env.IsType U Δ.toCtx A) :
    ChkEmbeds env U Δc ((some (fv, deps), .vlam A) :: Δ) := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hA' : env.IsType U Δ'.toCtx A := hA.defeqDFC henv (hD.defeqCtx.symm henv)
  obtain ⟨u, hu⟩ := hA'
  refine ⟨(some (fv, deps), .vlam A) :: Δ', _, .skip_fvar _ _ W, .cons hD ?_ (.vlam hu)⟩
  rintro _ _ ⟨⟩
  rw [hD.fvars]
  exact ⟨hfresh, hdeps⟩

/-- Opening the same binder in both contexts keeps the embedding. -/
theorem cons (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hfresh : fv ∉ Δ.fvars)
    (h₀ : TrExprS env Us Δc ty A₀) (h : TrExprS env Us Δ ty A)
    (hA : env.IsType Us.length Δ.toCtx A) :
    ChkEmbeds env Us.length ((some (fv, ty.fvarsList), .vlam A₀) :: Δc)
      ((some (fv, ty.fvarsList), .vlam A) :: Δ) := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hw : TrExprS env Us Δ' ty (A₀.lift' (n.consN 0)) := h₀.weakFV' henv.orderedStrong W hΔ'
  have hDsymm := hD.symm henv.orderedStrong
  have hu : env.IsDefEqU Us.length Δ.toCtx A (A₀.lift' (n.consN 0)) :=
    h.uniq henv hDsymm hw
  have hA' : env.IsType Us.length Δ'.toCtx A := hA.defeqDFC henv.orderedStrong (hD.defeqCtx.symm henv.orderedStrong)
  have hu' : env.IsDefEqU Us.length Δ'.toCtx A (A₀.lift' (n.consN 0)) :=
    hu.defeqDFC henv.orderedStrong (hD.defeqCtx.symm henv.orderedStrong)
  obtain ⟨v, hAv⟩ := hA'
  have hv := hu'.symm.of_r henv hΔ'.toCtx hAv
  refine ⟨(some (fv, ty.fvarsList), .vlam (A₀.lift' n)) :: Δ', _,
    .cons_fvar _ _ h₀.fvarsList W, .cons hD ?_ (.vlam (by simpa using hv))⟩
  rintro _ _ ⟨⟩
  rw [hD.fvars]
  exact ⟨hfresh, h.fvarsList⟩

/-- A translation in the checking context weakens to a main translation of the same expression. -/
theorem trExprS (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (h : TrExprS env Us Δc e e₀) : ∃ e₁, TrExprS env Us Δ e e₁ := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact (h.weakFV' henv.orderedStrong W hD.wf).defeqDFC henv hD

/-- Transfer an output relation from the checking context to the main context, along given
translations of the input in both contexts. -/
theorem trExpr (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn : TrExprS env Us Δc e e₀) (he : TrExprS env Us Δ e e')
    (h : TrExpr env Us Δc e₁ e₀) : TrExpr env Us Δ e₁ e' := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have h' := h.weakFV' henv W hΔ'
  have hn' := hn.weakFV' henv.orderedStrong W hΔ'
  obtain ⟨x, hx, hxe⟩ := h'
  have hx₂ := hx.defeqDFC' henv hD
  obtain ⟨y, hy, hyx⟩ := hx₂
  have hu := hn'.uniq henv hD he
  have hxe' := hxe.defeqDFC henv.orderedStrong hD.defeqCtx
  have hu' := hu.defeqDFC henv.orderedStrong hD.defeqCtx
  have hΔ := (hD.symm henv.orderedStrong).wf
  exact ⟨y, hy, hyx.trans henv hΔ.toCtx (hxe'.trans henv hΔ.toCtx hu')⟩

/-- Transfer a definitional equality from the checking context to the main context, along
translations of both sides in both contexts. -/
theorem isDefEqU (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn₁ : TrExprS env Us Δc e₁ a₁) (hn₂ : TrExprS env Us Δc e₂ a₂)
    (he₁ : TrExprS env Us Δ e₁ b₁) (he₂ : TrExprS env Us Δ e₂ b₂)
    (h : env.IsDefEqU Us.length Δc.toCtx a₁ a₂) :
    env.IsDefEqU Us.length Δ.toCtx b₁ b₂ := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hΔ := (hD.symm henv.orderedStrong).wf
  have h' := (h.weak' henv.orderedStrong W.toCtx).defeqDFC henv.orderedStrong hD.defeqCtx
  have hu₁ := ((hn₁.weakFV' henv.orderedStrong W hΔ').uniq henv hD he₁).defeqDFC henv.orderedStrong hD.defeqCtx
  have hu₂ := ((hn₂.weakFV' henv.orderedStrong W hΔ').uniq henv hD he₂).defeqDFC henv.orderedStrong hD.defeqCtx
  exact hu₁.symm.trans henv hΔ.toCtx (h'.trans henv hΔ.toCtx hu₂)

/-- Transfer a typing judgement from the checking context to the main context, along
translations of the term and of its type in both contexts. -/
theorem hasType (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn : TrExprS env Us Δc e e₀) (he : TrExprS env Us Δ e e')
    (hTn : TrExprS env Us Δc T T₀) (hT : TrExprS env Us Δ T T')
    (h : env.HasType Us.length Δc.toCtx e₀ T₀) : env.HasType Us.length Δ.toCtx e' T' := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hΔ := (hD.symm henv.orderedStrong).wf
  have hh := (h.weak' henv.orderedStrong W.toCtx).defeqDFC henv.orderedStrong hD.defeqCtx
  have hu := ((hn.weakFV' henv.orderedStrong W hΔ').uniq henv hD he).defeqDFC henv.orderedStrong hD.defeqCtx
  have huT := ((hTn.weakFV' henv.orderedStrong W hΔ').uniq henv hD hT).defeqDFC henv.orderedStrong hD.defeqCtx
  exact (hh.defeqU_l henv hΔ.toCtx hu).defeqU_r henv hΔ.toCtx huT

/-- Transfer a typing from the checking context to the main context along a main translation
of the term. -/
theorem trTyping (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (he : TrExprS env Us Δ e e') (h : TrTyping env Us Δc e ty e₀ ty₀) :
    ∃ ty', TrTyping env Us Δ e ty e' ty' := by
  obtain ⟨hb, hn, hty, hhas⟩ := h
  obtain ⟨ty₁, hty₁⟩ := H.trExprS henv hty
  have hΔ : VLCtx.WF env Us.length Δ := by
    obtain ⟨Δ', n, W, hD⟩ := H; exact (hD.symm henv.orderedStrong).wf
  refine ⟨ty₁, fun P hP hin => hb P (H.isFVarUpSet hP) hin, he, hty₁, ?_⟩
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ' : VLCtx.WF env Us.length Δ' := hD.wf
  have hh := (hhas.weak' henv.orderedStrong W.toCtx).defeqDFC henv.orderedStrong hD.defeqCtx
  have hu := ((hn.weakFV' henv.orderedStrong W hΔ').uniq henv hD he).defeqDFC henv.orderedStrong hD.defeqCtx
  have huty := ((hty.weakFV' henv.orderedStrong W hΔ').uniq henv hD hty₁).defeqDFC henv.orderedStrong hD.defeqCtx
  exact (hh.defeqU_l henv hΔ.toCtx hu).defeqU_r henv hΔ.toCtx huty

/-- Transfer typehood from the checking context to the main context along a main translation. -/
theorem isType (henv : VEnv.WF env) {Us : List Name} (H : ChkEmbeds env Us.length Δc Δ)
    (hn : TrExprS env Us Δc e e₀) (he : TrExprS env Us Δ e e')
    (h : env.IsType Us.length Δc.toCtx e₀) : env.IsType Us.length Δ.toCtx e' := by
  obtain ⟨Δ', n, W, hD⟩ := H
  have hΔ := (hD.symm henv.orderedStrong).wf
  have hh := (h.weak' henv.orderedStrong W.toCtx).defeqDFC henv.orderedStrong hD.defeqCtx
  have hu := ((hn.weakFV' henv.orderedStrong W hD.wf).uniq henv hD he).defeqDFC
    henv.orderedStrong hD.defeqCtx
  exact hh.defeqU_l henv hΔ.toCtx hu

theorem fvarsBelow (H : ChkEmbeds env U Δc Δ) (h : FVarsBelow Δc e e₁) :
    FVarsBelow Δ e e₁ :=
  fun P hP hin => h P (H.isFVarUpSet hP) hin

end ChkEmbeds

theorem _root_.Lean4Lean.VLCtx.FVLift'.instL {ls : List VLevel} {Δ Δ' : VLCtx} {dk k : Nat}
    {n : Lift} (W : VLCtx.FVLift' Δ Δ' dk n k) :
    VLCtx.FVLift' (Δ.instL ls) (Δ'.instL ls) dk n k := by
  have hdepth : ∀ d : VLocalDecl, (d.instL ls).depth = d.depth := by
    intro d; cases d <;> rfl
  have hlift : ∀ (d : VLocalDecl) (l : Lift), (d.lift' l).instL ls = (d.instL ls).lift' l := by
    intro d l; cases d <;> simp [VLocalDecl.lift', VLocalDecl.instL, VExpr.instL_lift']
  induction W with
  | refl => exact .refl
  | skip_fvar fv d _ ih =>
    simpa [VLCtx.instL, hdepth] using VLCtx.FVLift'.skip_fvar fv (d.instL ls) ih
  | cons_fvar fv d hsub _ ih =>
    have := VLCtx.FVLift'.cons_fvar fv (d.instL ls) (by simpa using hsub) ih
    simpa [VLCtx.instL, hdepth, hlift] using this
  | cons_bvar d _ ih =>
    have := VLCtx.FVLift'.cons_bvar (d.instL ls) ih
    simpa [VLCtx.instL, hdepth, hlift] using this

theorem _root_.Lean4Lean.VLCtx.IsDefEq.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Δ₁ Δ₂ : VLCtx} (H : VLCtx.IsDefEq env U Δ₁ Δ₂) :
    VLCtx.IsDefEq env U' (Δ₁.instL ls) (Δ₂.instL ls) := by
  induction H with
  | nil => exact .nil
  | cons _ hfresh hdecl ih =>
    refine .cons ih (by simpa using hfresh) ?_
    cases hdecl with
    | vlam h => exact .vlam (VLCtx.instL_toCtx _ ▸ h.instL hls)
    | vlet h1 h2 =>
      exact .vlet (VLCtx.instL_toCtx _ ▸ h1.instL hls) (VLCtx.instL_toCtx _ ▸ h2.instL hls)

theorem ChkEmbeds.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Δc Δ : VLCtx} (H : ChkEmbeds env U Δc Δ) :
    ChkEmbeds env U' (Δc.instL ls) (Δ.instL ls) := by
  obtain ⟨Δ', n, W, hD⟩ := H
  exact ⟨Δ'.instL ls, n, W.instL, hD.instL hls⟩

/-- A pure weakening followed by an embedding is an embedding. -/
theorem ChkEmbeds.of_fvLift {env : VEnv} {U : Nat} {Δ₁ Δ₂ Δ : VLCtx} {n : Lift}
    (W : VLCtx.FVLift' Δ₁ Δ₂ 0 n 0) (H : ChkEmbeds env U Δ₂ Δ) : ChkEmbeds env U Δ₁ Δ := by
  obtain ⟨Δ', n', W', hD⟩ := H
  exact ⟨Δ', _, W.comp W', hD⟩

end VerifyInductive

end Lean4Lean
