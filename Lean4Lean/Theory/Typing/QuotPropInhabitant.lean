import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Typing.Meta

/-! A quotient over a proposition carries an inhabitant of that proposition.
The selector uses the installed primitive Quot.ind declaration and the
occurrence's actual universe equality to zero. -/

namespace Lean4Lean.VEnv
open VExpr
set_option maxHeartbeats 1000000
/-- The closed source selector has its exact three-binder type. -/
theorem QuotRegistered.propInhabitant_type {env : VEnv} (hr : QuotRegistered env) {U : Nat} {u : VLevel}
    (hu : u.WF U) (hz : u ≈ .zero) :
    env.HasType U Γ (QuotPrefixUnfolding.propInhabitant u)
      (wrapForalls [.sort u,
        .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
        mkApps (.const ``Quot [u]) [.bvar 1, .bvar 0]] (.bvar 2)) := by
  have hquot := hr.quotient
  have hind := hr.induction
  have hmk := hr.constructor
  unfold QuotPrefixUnfolding.propInhabitant
  simp only [wrapLams, wrapForalls]
  refine HasType.lam (HasType.sort hu) ?_
  refine HasType.lam (HasType.forallE (HasType.bvar .zero)
    (HasType.forallE (HasType.bvar (.succ .zero)) (HasType.sort (l := .zero) trivial))) ?_
  refine HasType.lam (u := u) ?_ ?_
  · apply HasType.app'
    · apply HasType.app'
      · exact HasType.const hquot (by simpa using hu) rfl
      · type_tac
      · rfl
    · type_tac
    · rfl
  simp only [mkApps]
  apply IsDefEq.defeq (A := .app
    (.lam (mkApps (.const ``Quot [u]) [.bvar 2, .bvar 1]) (.bvar 3)) (.bvar 0))
  · apply IsDefEq.beta (B := .sort .zero)
    · apply IsDefEq.defeq (IsDefEq.sortDF (l' := .zero) hu trivial hz)
      type_tac
    · type_tac
  apply HasType.app'
  · apply HasType.app'
    · apply HasType.app'
      · apply HasType.app'
        · apply HasType.app'
          · exact HasType.const hind (by simpa using hu) rfl
          · type_tac
          · rfl
        · type_tac
        · rfl
      · apply HasType.lam (u := u)
        · apply HasType.app'
          · apply HasType.app'
            · exact HasType.const hquot (by simpa using hu) rfl
            · type_tac
            · rfl
          · type_tac
          · rfl
        · apply IsDefEq.defeq (IsDefEq.sortDF (l' := .zero) hu trivial hz)
          type_tac
      · exact rfl
    · apply HasType.lam (u := u)
      · type_tac
      · apply IsDefEq.defeq'
        · apply IsDefEq.beta (B := .sort .zero)
          · apply IsDefEq.defeq (IsDefEq.sortDF (l' := .zero) hu trivial hz)
            type_tac
          · apply HasType.app'
            · apply HasType.app'
              · apply HasType.app'
                · exact HasType.const (ls := [u]) hmk (by simpa using hu) rfl
                · type_tac
                · rfl
              · type_tac
              · rfl
            · type_tac
            · rfl
        · type_tac
    · exact rfl
  · type_tac
  · rfl

/-- Applying the generated selector to well-typed source data recovers a source proof. -/
theorem QuotRegistered.propInhabitant_app {env : VEnv} (H : QuotRegistered env)
    (hu : u.WF U) (hz : u ≈ .zero)
    (ha : env.HasType U Γ alpha (.sort u))
    (hr : env.HasType U Γ relation (.forallE alpha (.forallE alpha.lift (.sort .zero))))
    (hq : env.HasType U Γ major (mkApps (.const ``Quot [u]) [alpha, relation])) :
    env.HasType U Γ (mkApps (QuotPrefixUnfolding.propInhabitant u) [alpha, relation, major]) alpha := by
  have hw := H.propInhabitant_type (Γ := Γ) hu hz
  have h1 := HasType.app hw ha
  simp [mkApps, inst] at h1
  have h2 := HasType.app h1 hr
  simp [inst, inst_lift, ← lift_instN_lo] at h2
  have h3 := HasType.app h2 hq
  simpa [mkApps, inst_lift] using h3

end Lean4Lean.VEnv
