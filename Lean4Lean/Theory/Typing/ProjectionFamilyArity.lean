import Lean4Lean.Theory.Typing.ProjectionProofResult
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.CaseSourceSort

/-!
# Arity of a registered structure family at a type

An application of a registered structure family that is itself a type supplies exactly the
parameters and indices of the family: the family's header is a telescope ending in a sort, and
by unique typing a sort is neither a `forallE` nor the result of applying something to an extra
argument.
-/

namespace Lean4Lean.VEnv
open VExpr
variable {env : VEnv} {info : VProjectionInfo}

/-- An application of a registered structure family that has sort type supplies exactly the
family's parameters and indices. -/
theorem HasType.projectionFamily_arity (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hinfo : env.projections family info)
    (hfamily : env.constants family = some ⟨info.uvars, familyT⟩)
    (H : env.HasType U Γ (mkApps (.const family levels) args) (.sort v)) :
    args.length = info.nparams + info.nindices := by
  obtain ⟨decl, familyType, ctor, _, _, _, _, huvars, hnparams, hindexCount,
    _, _, _, hlookup, _, ⟨common, Hshape, _⟩, _, _⟩ :=
    henv.ordered.projectionShape hinfo
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnorm, hown, hidx, _, hresult⟩ := Hshape
  obtain ⟨ci, hci, hlevels, hlevelCount⟩ :=
    (VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, H⟩).elim fun _ h =>
      HasType.const_inv henv.ordered hΓ h
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hfamilyUvars : familyType.uvars = decl.uvars := by
    rw [hlookup] at hfamily
    have := congrArg VConstant.uvars (Option.some.inj hfamily)
    simp only at this
    omega
  have hnormEq : normalized = wrapForalls (ownParams ++ indices) result := by
    rw [VExpr.eq_wrapForalls_of_takeForalls hown, VExpr.eq_wrapForalls_of_takeForalls hidx,
      wrapForalls_append]
  have hT : env.IsType decl.uvars [] familyType.type := by
    have h := henv.ordered.constWF hlookup
    change env.IsType familyType.uvars [] familyType.type at h
    rwa [hfamilyUvars] at h
  rw [hnormEq] at hnorm
  have hsort : env.IsDefEqU decl.uvars [] familyType.type
      (wrapForalls (ownParams ++ indices) (.sort familyType.resultLevel)) :=
    IsDefEq.close_sort_header henv hT hnorm (by simpa only [List.reverse_append] using hresult)
  have hfn := HasType.const (Γ := Γ) hlookup hlevels hlevelCount
  have hsortL : env.IsDefEqU U Γ (familyType.type.instL levels)
      ((wrapForalls (ownParams ++ indices) (.sort familyType.resultLevel)).instL levels) :=
    let ⟨_, h⟩ := hsort; ⟨_, (h.instL hlevels).weak0 henv.ordered⟩
  have hfn' := hfn.defeqU_r henv hΓ hsortL
  rw [instL_wrapForalls] at hfn'
  have hlen := HasType.mkApps_sort_arity henv hΓ hfn' H
  have hp := VExpr.takeForalls_domains_length hown
  have hi := VExpr.takeForalls_domains_length hidx
  simp only [List.length_map, List.length_append] at hlen
  omega

end Lean4Lean.VEnv
