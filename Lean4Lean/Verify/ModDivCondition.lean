import Lean4Lean.Verify.BitwiseCondition

namespace Lean4Lean.Environment
open Lean VEnv

/-- A checked dependent true-selector equation specializes to its true
branch, retaining the generated proof argument existentially. -/
theorem VEnv.reflectionNatDITE_true_select
    {env : VEnv} (wf : env.WF)
    {rtypeL rtypeR rdite ofTrue p t e H : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hrditeClosed : rdite.ClosedN) (hofTrueClosed : ofTrue.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeL (.bvar 2)) .boolTrue) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolTrue)
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeR (.bvar 2)) .boolTrue) <|
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))))
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolTrue))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolTrue)) :
    ∃ proof,
      env.IsDefEqU 0 []
        (.app (.app (.app (.app (.app rdite p) .boolTrue) H) t) e)
        (.app t proof) := by
  have hpClosed : p.ClosedN := (hp.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  have heClosed : e.ClosedN := (he.closedN' wf.ordered.closed trivial).1
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨⟨_, hHSort⟩, _, hleftHBody⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightHBody⟩ := hd₃.hasType.2.lam_inv wf trivial
  have h₄ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₃ hHSort
    hleftHBody hrightHBody hHL hHR
  simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq,
    hpClosed.instN_eq, htClosed.liftN_eq,
    htClosed.instN_eq, heClosed.lift_eq,
    heClosed.instN_eq] at h₄
  exact ⟨.app (.app ofTrue p) H, h₄⟩

/-- False counterpart of `reflectionNatDITE_true_select`. -/
theorem VEnv.reflectionNatDITE_false_select
    {env : VEnv} (wf : env.WF)
    {rtypeL rtypeR rdite ofFalse p t e H : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hrditeClosed : rdite.ClosedN) (hofFalseClosed : ofFalse.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeL (.bvar 2)) .boolFalse) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolFalse)
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeR (.bvar 2)) .boolFalse) <|
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))))
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolFalse))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolFalse)) :
    ∃ proof,
      env.IsDefEqU 0 []
        (.app (.app (.app (.app (.app rdite p) .boolFalse) H) t) e)
        (.app e proof) := by
  have hpClosed : p.ClosedN := (hp.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  have heClosed : e.ClosedN := (he.closedN' wf.ordered.closed trivial).1
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨⟨_, hHSort⟩, _, hleftHBody⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightHBody⟩ := hd₃.hasType.2.lam_inv wf trivial
  have h₄ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₃ hHSort
    hleftHBody hrightHBody hHL hHR
  simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq,
    hpClosed.instN_eq, htClosed.liftN_eq,
    htClosed.instN_eq, heClosed.lift_eq, heClosed.instN_eq] at h₄
  exact ⟨.app (.app ofFalse p) H, h₄⟩

end Lean4Lean.Environment
