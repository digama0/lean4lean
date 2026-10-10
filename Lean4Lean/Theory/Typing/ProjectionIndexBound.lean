import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.Theory.Typing.RecursorLemmas

namespace Lean4Lean
open VExpr VEnv
variable {env : VEnv} {info : VProjectionInfo}

private theorem projectionParams_shape {domains params : List VExpr}
    (H : VProjectionInfo.instantiateProjectionParameters
      (wrapForalls domains (mkApps (.const name levels) indices)) params = some output) :
    ∃ domains' indices', output = wrapForalls domains' (mkApps (.const name levels) indices') ∧
      domains'.length + params.length = domains.length := by
  induction params generalizing domains indices with
  | nil => cases H; exact ⟨domains, indices, rfl, by simp⟩
  | cons param params ih =>
    cases domains with
    | nil =>
      have hh : (mkApps (.const name levels) indices).getAppFnArgs.1 = .const name levels :=
        congrArg Prod.fst (VExpr.getAppFnArgs_mkApps_const name levels indices)
      generalize he : mkApps (.const name levels) indices = result at *
      cases result <;> try contradiction
    | cons domain domains =>
      change VProjectionInfo.instantiateProjectionParameters
        ((wrapForalls domains (mkApps (.const name levels) indices)).inst param) params = some output at H
      rw [wrapForalls_inst, inst_mkApps] at H
      obtain ⟨ds, args, heq, hlen⟩ := ih H
      refine ⟨ds, args, heq, ?_⟩
      simp only [VExpr.instDomains_length] at hlen
      simp only [List.length_cons]
      omega

private theorem projectionFields_bound {domains : List VExpr}
    (H : VProjectionInfo.instantiateProjectionFields family major wanted current fuel
      (wrapForalls domains (mkApps (.const name levels) indices)) = some output) :
    wanted < current + domains.length := by
  induction fuel generalizing domains indices current with
  | zero => cases H
  | succ fuel ih =>
    cases domains with
    | nil =>
      have hh : (mkApps (.const name levels) indices).getAppFnArgs.1 = .const name levels :=
        congrArg Prod.fst (VExpr.getAppFnArgs_mkApps_const name levels indices)
      generalize he : mkApps (.const name levels) indices = result at *
      cases result <;> try contradiction
    | cons domain domains =>
      simp only [wrapForalls, List.foldr_cons, VProjectionInfo.instantiateProjectionFields] at H
      split at H
      · rename_i heq; simp only [List.length_cons]; omega
      · change VProjectionInfo.instantiateProjectionFields family major wanted (current + 1) fuel
          ((wrapForalls domains (mkApps (.const name levels) indices)).inst (.proj family current major)) =
            some output at H
        rw [wrapForalls_inst, inst_mkApps] at H
        have hb := ih H
        simp only [List.length_cons, VExpr.instDomains_length] at hb ⊢
        omega

theorem VEnv.HasType.proj_index_lt (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.proj family index major) fieldType)
    (hinfo : env.projections family info) : index < info.numFields := by
  obtain ⟨info', levels, params, indexArgs, sourceMajor, resultType, resultLevel,
    hinfo', _, _, hparams, _, hfield, _⟩ := H.proj_inv henv hΓ
  cases henv.ordered.projections_unique hinfo' hinfo
  obtain ⟨decl, type, ctor, _, _, _, _, _, hnparams, _, _, _, hctorType, _, _, _, Hraw, _⟩ :=
    henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, _, hhead, harity⟩ := Hraw.forallArity
  have hresult : result = mkApps (.const type.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← hhead]; exact (mkApps_getAppFnArgs_eq result).symm
  unfold VProjectionInfo.fieldType at hfield
  split at hfield <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hfield
  obtain ⟨tail, hparams', hfields⟩ := hfield
  rw [← hctorType, hshape, hresult, instL_wrapForalls, instL_mkApps] at hparams'
  obtain ⟨ds, args, rfl, hlen⟩ := projectionParams_shape hparams'
  have hb := projectionFields_bound hfields
  simp only [Nat.zero_add] at hb
  simp only [List.length_map] at hlen
  have hcount : info.numFields = doms.length - info.nparams := by
    rw [VProjectionInfo.numFields, ← hctorType, harity]
  rw [hcount]
  omega

end Lean4Lean
