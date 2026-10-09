import Lean4Lean.Theory.Typing.Strengthening.Cancel

/-! # Strengthening along general lifts

Consequences of `VEnv.Strengthening` for the general lifts `Ctx.Lift'` (several binders removed
at several depths), obtained by removing one binder at a time with `IsDefEqU.weakN_iff`. They are
used only by the verification of the checker's global cache mode (`CacheMode.global`), where the
strengthening hypothesis comes from a `GlobalCacheLicense`. -/

namespace Lean4Lean
namespace VEnv
open VExpr

variable {env : VEnv} {U : Nat}

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem _root_.Lean4Lean.OnCtx.weak'_inv
    (W : Ctx.Lift' ρ Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  generalize e : ρ.depth = n
  induction n generalizing ρ Γ' with
  | zero => simpa [W.depth_zero e] using H
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    exact ih W1 (.weakN_inv henv hs W2 H) (by simp)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEqU.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsDefEqU U Γ' (e1.lift' l) (e2.lift' l) ↔ env.IsDefEqU U Γ e1 e2 := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      weakN_iff henv hs hΓ' W2, ih (hΓ'.weakN_inv henv hs W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsDefEq U Γ' (e1.lift' l) (e2.lift' l) (A.lift' l) ↔ env.IsDefEq U Γ e1 e2 A := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      weakN_iff henv hs hΓ' W2, ih (hΓ'.weakN_inv henv hs W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.HasType U Γ' (e.lift' l) (A.lift' l) ↔ env.HasType U Γ e A :=
  IsDefEq.weak'_iff henv hs hΓ' W

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e :=
  exists_congr fun _ => HasType.weak'_iff henv hs hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    VExpr.WF env U Γ' (e.lift' l) ↔ VExpr.WF env U Γ e := IsDefEqU.weak'_iff henv hs hΓ W

end VEnv
end Lean4Lean
