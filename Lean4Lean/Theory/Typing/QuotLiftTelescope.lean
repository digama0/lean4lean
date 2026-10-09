import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift

/-! Typing soundness of the actual primitive quotient iota pattern. -/

namespace Lean4Lean.VEnv
open VExpr
set_option maxHeartbeats 1000000
theorem quotient_walk (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U)
    (H : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, major])) :
    ∃ result, InstForallsC env U Γ (quotLiftConst.type.instL [u,v])
      [alpha, relation, beta, fn, compat, major] result := by
  obtain ⟨result, hw, _⟩ := HasType.mkApps_telescope henv hΓ
    (HasType.const hr.lift (ls := [u,v]) (by simpa using And.intro hu hv) rfl) H
    (by rfl)
  exact ⟨result, hw⟩

end Lean4Lean.VEnv
