import Lean4Lean.Theory.Typing.PrefixUnfolding.Supply
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation
import Lean4Lean.Theory.Typing.PrefixUnfolding.Renaming
import Lean4Lean.Theory.Typing.PrefixUnfolding.Rule
import Batteries.Tactic.OpenPrivate

/-! Typed abstraction of an opened recursor prefix. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.RecursorData

theorem HasType.supply (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ fn type) (H : VExpr.WF env U Γ (mkApps fn args))
    (hg : supplyType args type = some residual) :
    env.HasType U Γ (mkApps fn args) residual := by
  induction args generalizing fn type with
  | nil => cases hg; exact hf
  | cons arg args ih =>
    cases type <;> try contradiction
    rename_i domain body
    have hfa : VExpr.WF env U Γ (.app fn arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app fn arg) H
    obtain ⟨domain', body', hf', ha⟩ := hfa.app_inv henv.ordered hΓ
    obtain ⟨⟨_, hdom⟩, _, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
    have harg := ha.defeqU_r henv hΓ ⟨_, hdom.symm⟩
    exact ih (hf.app harg) H hg

theorem takeForalls_sound
    (H : VExpr.takeForalls count type = some (domains, result)) :
    type = wrapForalls domains result := by
  induction count generalizing type domains result with
  | zero => cases H; rfl
  | succ count ih =>
    cases type <;> try contradiction
    simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, ht, he⟩ := H
    cases he
    exact congrArg (VExpr.forallE _) (ih ht)

/-- Successful singleton unfolding determines the actual type of any
well-formed occurrence of that registered recursor prefix. -/
theorem RecursorRegistered.prefixType {data : RecursorData}
    {levels : List VLevel} {program : PrefixUnfolding}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : RecursorRegistered env data)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hg : data.singletonUnfolding env U levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const data.name levels) args)) :
    env.HasType U Γ (mkApps (.const data.name levels) args) program.type := by
  unfold singletonUnfolding at hg
  dsimp only at hg
  split at hg <;> try contradiction
  rename_i hguard
  simp at hguard
  have hlen : levels.length = data.uvars := hguard.1
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨recType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, _, equation, _, body, _, hg⟩ := hg
  split at hg <;> try contradiction
  cases hg
  have hf : env.HasType U Γ (.const data.name levels) (recType.instL levels) :=
    .const (H.recursorType htype) hlevels hlen
  have hh := hf.supply henv hΓ ht hsupply
  rw [takeForalls_sound htake] at hh
  exact hh

end Lean4Lean.VEnv
