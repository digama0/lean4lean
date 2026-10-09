import Lean4Lean.Theory.Typing.PrefixUnfolding.Renaming
import Lean4Lean.Theory.Typing.PrefixUnfolding.Rule

/-! Renaming preserves the concrete generated prefix and all of its checked
unfolding-check premises. The fresh remaining telescope is renamed under its binders. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.RecursorData

private theorem etaOpen_lift_lift' (e : VExpr) (ρ : Lift) :
    (e.lift' ρ).lift = e.lift.lift' ρ.cons := by
  simp only [← lift'_consN_skipN (k := 0), Lift.consN]
  rw [← lift'_comp, ← lift'_comp]
  congr 1
  simp [Lift.comp, Lift.skipN, Lift.refl_comp]

theorem ConstSpineDefEq.weak' (henv : env.WF)
    (W : Ctx.Lift' ρ Γ Γ') (H : ConstSpineDefEq env U Γ actual expected) :
    ConstSpineDefEq env U Γ' (actual.lift' ρ) (expected.lift' ρ) := by
  obtain ⟨name, levels, levels', args, args', rfl, rfl, hw, hw', heq, hargs⟩ := H
  refine ⟨name, levels, levels', args.map (·.lift' ρ), args'.map (·.lift' ρ),
    VExpr.lift'_mkApps _ _ _, VExpr.lift'_mkApps _ _ _, hw, hw', heq, ?_⟩
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  induction hargs with
  | nil => exact .nil
  | cons h hs ih => exact .cons (h.weak' henv.ordered W) ih

theorem UnfoldingCheck.weak' (henv : env.WF)
    (W : Ctx.Lift' ρ Γ Γ') (H : UnfoldingCheck env U Γ source program) :
    UnfoldingCheck env U Γ' (source.lift' ρ) (program.rename ρ) := by
  have Wext := renameDomains_context program.domains W
  have hscope := H.templateScope henv
  have hnonzero : program.domains.length ≠ 0 := by
    intro hn
    exact H.remaining_nonempty (List.eq_nil_of_length_eq_zero hn)
  refine {
    source_typed := ?_
    remaining_nonempty := ?_
    equation_present := H.equation_present
    equation_body := H.equation_body
    levels_wf := H.levels_wf
    levels_length := H.levels_length
    captures_length := ?_
    captures_typed := ?_
    major_prop := ?_
    recursor_lhs := ?_ }
  · rw [PrefixUnfolding.rename_type]
    exact H.source_typed.weak' henv.ordered W
  · intro hn
    have heq := congrArg List.length hn
    simp only [PrefixUnfolding.rename, renameDomains_length, List.length_nil] at heq
    exact hnonzero heq
  · simpa only [PrefixUnfolding.rename, List.length_map] using H.captures_length
  · intro j hj hd
    have hj' : j < program.captures.length := by simpa only [PrefixUnfolding.rename, List.length_map] using hj
    have ht := (H.captures_typed j hj' hd).weak' henv.ordered Wext
    simp only [PrefixUnfolding.rename, List.getElem_map]
    change HasType _ _ _ _ _ at ht
    have hdscope : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')] using
        (hscope.2.2 j hd).instL (ls := program.levels)
    rw [← instantiateParams_eq_instOuter, instantiateParams_lift' hdscope] at ht
    simp only [instantiateParams_eq_instOuter, List.map_take] at ht
    exact ht
  · obtain ⟨majorType, hp, hm, hc⟩ := H.major_prop
    refine ⟨majorType.lift' (ρ.consN program.domains.length),
      hp.weak' henv.ordered Wext, ?_, hc.weak' henv.ordered Wext⟩
    have hm' := hm.weak' henv.ordered Wext
    cases hn : program.domains.length with
    | zero => contradiction
    | succ n => simpa only [hn, Lift.consN, VExpr.lift', Lift.liftVar, PrefixUnfolding.rename] using hm'
  · have hmatch := H.recursor_lhs.weak' henv Wext
    have hn : program.domains.length = program.domains.length - 1 + 1 := by omega
    have hleft : (VExpr.app (etaOpen (program.domains.length - 1) source).lift program.constructor).lift'
        (ρ.consN program.domains.length) =
        VExpr.app (etaOpen (program.domains.length - 1) (source.lift' ρ)).lift
          (program.constructor.lift' (ρ.consN program.domains.length)) := by
      conv => lhs; rw [hn]
      simp only [VExpr.lift', Lift.consN, Nat.add_sub_cancel]
      rw [← etaOpen_lift_lift', ← etaOpen_lift']
      conv => rhs; rw [hn]
      rfl
    rw [hleft] at hmatch
    rw [← instantiateParams_eq_instOuter,
      instantiateParams_lift' (hscope.1.instL (ls := program.levels))] at hmatch
    simpa only [PrefixUnfolding.rename, renameDomains_length, instantiateParams_eq_instOuter] using hmatch

theorem PrefixUnfold.weak' {name : Name} {levels : List VLevel} (henv : env.WF)
    (W : Ctx.Lift' ρ Γ Γ')
    (H : PrefixUnfold env U registry Γ name levels arguments rhs) :
    PrefixUnfold env U registry Γ' name levels (arguments.map (·.lift' ρ)) (rhs.lift' ρ) := by
  cases H with
  | @intro data program hl hr hn ht hw hz hg replay =>
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold singletonUnfolding at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    have hg' := singletonUnfolding_lift' henv hr ht hz htype (hr.recursorType_closed henv htype) hg (ρ := ρ)
    have replay' := replay.weak' henv W
    rw [VExpr.lift'_mkApps] at replay'
    rw [← PrefixUnfolding.rename_rhs (replay.templateScope henv).2.1]
    exact .intro hl hr hn ht hw hz hg' replay'

theorem PrefixUnfold.weakN {name : Name} {levels : List VLevel} (henv : env.WF)
    (W : Ctx.LiftN n k Γ Γ')
    (H : PrefixUnfold env U registry Γ name levels arguments rhs) :
    PrefixUnfold env U registry Γ' name levels
      (arguments.map (·.liftN n k)) (rhs.liftN n k) := by
  simpa only [lift'_consN_skipN] using H.weak' henv (Ctx.liftN_iff_lift'.mp W)

end Lean4Lean.VEnv
