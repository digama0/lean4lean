import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Typing.PrefixUnfolding.Rule

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.RecursorData

theorem EqUpToLevels.wrapForalls (hd : List.Forall₂ (EqUpToLevels U) ds ds')
    (hb : EqUpToLevels U body body') :
    EqUpToLevels U (VExpr.wrapForalls ds body) (VExpr.wrapForalls ds' body') := by
  induction hd with
  | nil => exact hb
  | cons h hs ih => exact .forallE h ih

theorem EqUpToLevels.wrapLams (hd : List.Forall₂ (EqUpToLevels U) ds ds')
    (hb : EqUpToLevels U body body') :
    EqUpToLevels U (VExpr.wrapLams ds body) (VExpr.wrapLams ds' body') := by
  induction hd with
  | nil => exact hb
  | cons h hs ih => exact .lam h ih

theorem EqUpToLevels.etaOpen (H : EqUpToLevels U e e') (n : Nat) :
    EqUpToLevels U (VEnv.etaOpen n e) (VEnv.etaOpen n e') := by
  induction n generalizing e e' with
  | zero => exact H
  | succ n ih => exact ih (.app H.weakN .bvar)

theorem HasType.eqUpToLevels_both (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : HasType env U Γ e A) (he : EqUpToLevels U e e') (hA : EqUpToLevels U A A') :
    HasType env U Γ e' A' := by
  obtain ⟨u, htype⟩ := H.isType henv.ordered hΓ
  have he' := (H.eqUpToLevels henv.ordered hΓ he).hasType.2
  exact he'.defeqU_r henv hΓ ⟨_, htype.eqUpToLevels henv.ordered hΓ hA⟩

private theorem levelsContext (henv : env.WF) (_hΓ : OnCtx Γ (env.IsType U))
    (he : List.Forall₂ (EqUpToLevels U) domains domains')
    (hc : OnCtx (domains ++ Γ) (env.IsType U)) :
    IsDefEqCtx env U Γ (domains ++ Γ) (domains' ++ Γ) := by
  induction he with
  | nil => exact .zero
  | cons hd hs ih =>
    obtain ⟨u, ht⟩ := hc.2
    exact .succ (ih hc.1) (ht.eqUpToLevels henv.ordered hc.1 hd)

private theorem levels_spine_inv (H : EqUpToLevels U (VExpr.mkApps fn args) output) :
    ∃ fn' args', output = VExpr.mkApps fn' args' ∧ EqUpToLevels U fn fn' ∧
      List.Forall₂ (EqUpToLevels U) args args' := by
  induction args generalizing fn output with
  | nil => exact ⟨output, [], rfl, H, .nil⟩
  | cons arg args ih =>
    obtain ⟨fn', args', rfl, hf, ha⟩ := ih H
    cases hf with
    | app hfn harg => exact ⟨_, _ :: args', rfl, hfn, .cons harg ha⟩

theorem ConstSpineDefEq.congr_levels (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : ConstSpineDefEq env U Γ actual expected)
    (ha : EqUpToLevels U actual actual') (he : EqUpToLevels U expected expected') :
    ConstSpineDefEq env U Γ actual' expected' := by
  obtain ⟨name, levels, levels', args, args', rfl, rfl, hw, hw', hl, hargs⟩ := H
  obtain ⟨fn, args₁, rfl, hfn, has⟩ := levels_spine_inv ha
  obtain ⟨fn', args₂, rfl, hfn', hes⟩ := levels_spine_inv he
  cases hfn with | const hwl hwr hlr =>
    cases hfn' with | const hw'l hw'r hl'r =>
      refine ⟨_, _, _, _, _, rfl, rfl, hwr, hw'r, ?_, ?_⟩
      · exact Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ h1 h2 => h1.symm.trans h2)
          (Lean4Lean.List.Forall₂.flip hlr)
          (Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ h1 h2 => h1.trans h2) hl hl'r)
      · clear ha he
        induction hargs generalizing args₁ args₂ with
        | nil => cases has; cases hes; exact .nil
        | cons h hs ih =>
          cases has with | cons ha has =>
            cases hes with | cons he hes =>
              obtain ⟨A, ht⟩ := h
              exact .cons ⟨A, ((ht.symm.eqUpToLevels henv.ordered hΓ ha).symm.eqUpToLevels henv.ordered hΓ he)⟩
                (ih _ has _ hes)

end Lean4Lean.VEnv

namespace Lean4Lean.InductiveSignature.RecursorData
open VEnv

/-- The finite unfolding varies only at scoped equivalent universes.
Its installed equation and the parsed generic body remain exactly the same. -/
structure PrefixUnfolding.LevelEquiv (U : Nat) (p p' : PrefixUnfolding) : Prop where
  domains : List.Forall₂ (EqUpToLevels U) p.domains p'.domains
  result : EqUpToLevels U p.result p'.result
  constructor : EqUpToLevels U p.constructor p'.constructor
  equation : p.equation = p'.equation
  equationBody : p.equationBody = p'.equationBody
  captures : List.Forall₂ (EqUpToLevels U) p.captures p'.captures
  levels : List.Forall₂ (· ≈ ·) p.levels p'.levels
  levels_wf : ∀ level ∈ p'.levels, level.WF U

theorem PrefixUnfolding.LevelEquiv.type (H : PrefixUnfolding.LevelEquiv U p p') :
    EqUpToLevels U p.type p'.type := EqUpToLevels.wrapForalls H.domains H.result

theorem PrefixUnfolding.LevelEquiv.rhs (H : PrefixUnfolding.LevelEquiv U p p')
    (hw : ∀ level ∈ p.levels, level.WF U) : EqUpToLevels U p.rhs p'.rhs := by
  apply EqUpToLevels.wrapLams H.domains
  rw [← H.equationBody]
  exact (EqUpToLevels.instL_expr _ hw H.levels_wf H.levels).instantiateParams_args H.captures

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.RecursorData

theorem UnfoldingCheck.congr_levels (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : UnfoldingCheck env U Γ source p)
    (hp : PrefixUnfolding.LevelEquiv U p p') (hs : EqUpToLevels U source source') :
    UnfoldingCheck env U Γ source' p' := by
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv.ordered hΓ)).1
  have W := levelsContext henv hΓ (List.Forall₂.reverse.mpr hp.domains) hctx
  have hlength := Lean4Lean.List.Forall₂.length_eq hp.domains
  have hcaptureLength := Lean4Lean.List.Forall₂.length_eq hp.captures
  refine {
    source_typed := H.source_typed.eqUpToLevels_both henv hΓ hs hp.type
    remaining_nonempty := ?_
    equation_present := hp.equation ▸ H.equation_present
    equation_body := ?_
    levels_wf := hp.levels_wf
    levels_length := ?_
    captures_length := ?_
    captures_typed := ?_
    major_prop := ?_
    recursor_lhs := ?_ }
  · intro he
    apply H.remaining_nonempty
    apply List.eq_nil_of_length_eq_zero
    rw [hlength, he]
    rfl
  · rw [← hp.equation, ← hp.equationBody]
    exact H.equation_body
  · rw [← hp.equation, ← Lean4Lean.List.Forall₂.length_eq hp.levels]
    exact H.levels_length
  · rw [← hp.equationBody, ← hcaptureLength]
    exact H.captures_length
  · intro j hj hd
    have hj₀ : j < p.captures.length := by omega
    have hd₀ : j < p.equationBody.domains.length := by simpa only [← hp.equationBody] using hd
    have he := List.forall₂_getElem hp.captures j hj₀ hj
    have ht : EqUpToLevels U
        ((p.equationBody.domains[j].instL p.levels).instOuter (p.captures.take j))
        ((p'.equationBody.domains[j].instL p'.levels).instOuter (p'.captures.take j)) := by
      simp only [← hp.equationBody, ← instantiateParams_eq_instOuter]
      exact (EqUpToLevels.instL_expr _ H.levels_wf hp.levels_wf hp.levels).instantiateParams_args
        (List.forall₂_take hp.captures _)
    exact ((H.captures_typed j hj₀ hd₀).eqUpToLevels_both henv hctx he ht).defeqDFC henv W
  · obtain ⟨proposition, hprop, hmajor, hctor⟩ := H.major_prop
    exact ⟨proposition, hprop.defeqDFC henv W, hmajor.defeqDFC henv W,
      ((hctor.eqUpToLevels henv.ordered hctx hp.constructor).hasType.2).defeqDFC henv W⟩
  · apply ConstSpineDefEq.defeqDFC henv W
    apply H.recursor_lhs.congr_levels henv hctx
    · rw [← hlength]
      exact .app (hs.etaOpen _).weakN hp.constructor
    · rw [← hp.equationBody, ← instantiateParams_eq_instOuter, ← instantiateParams_eq_instOuter]
      exact (EqUpToLevels.instL_expr _ H.levels_wf hp.levels_wf hp.levels).instantiateParams_args hp.captures

end Lean4Lean.VEnv
