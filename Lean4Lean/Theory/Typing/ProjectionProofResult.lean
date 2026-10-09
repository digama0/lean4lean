import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.Theory.Typing.RecursorLemmas

namespace Lean4Lean.VEnv
open VExpr
variable {env : VEnv} {info : VProjectionInfo}

theorem HasType.projectionFamily_sort (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hinfo : env.projections family info)
    (hlevelsLength : levels.length = info.uvars)
    (hparams : params.length = info.nparams)
    (hindices : indexArgs.length = info.nindices)
    (H : VExpr.WF env U Γ (mkApps (.const family levels) (params ++ indexArgs))) :
    env.HasType U Γ (mkApps (.const family levels) (params ++ indexArgs))
      (.sort (info.resultLevel.inst levels)) := by
  obtain ⟨decl, familyType, ctor, _, _, hname, _, huvars, hnparams, hindexCount,
    hlevel, _, _, hlookup, _, ⟨common, Hshape, _⟩, _, _⟩ :=
    henv.ordered.projectionShape hinfo
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnorm, hown, hidx, _, hresult⟩ := Hshape
  obtain ⟨ci, hci, hlevels, hlevelCount⟩ :=
    (VExpr.WF.of_mkApps henv.ordered hΓ H).elim fun _ h => HasType.const_inv henv.ordered hΓ h
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hfamilyUvars : familyType.uvars = decl.uvars := by
    change levels.length = familyType.uvars at hlevelCount
    omega
  have hnormEq : normalized = wrapForalls (ownParams ++ indices) result := by
    rw [VExpr.eq_wrapForalls_of_takeForalls hown, VExpr.eq_wrapForalls_of_takeForalls hidx,
      wrapForalls_append]
  have hnormalizedType : env.IsType decl.uvars [] normalized := by
    have htype := henv.ordered.constWF hlookup
    change env.IsType familyType.uvars [] familyType.type at htype
    rw [hfamilyUvars] at htype
    exact htype.defeqU_l henv (by trivial) ⟨_, hnorm⟩
  rw [hnormEq] at hnormalizedType
  have hctx := (IsType.wrapForalls_inv henv (by trivial) hnormalizedType).1
  simp only [List.append_nil] at hctx
  have hfn := HasType.const (Γ := Γ) hlookup hlevels hlevelCount
  have hnormL : env.IsDefEqU U Γ (familyType.type.instL levels) (normalized.instL levels) :=
    ⟨_, (hnorm.instL hlevels).weak0 henv.ordered⟩
  have hfn' := hfn.defeqU_r henv hΓ hnormL
  rw [hnormEq, instL_wrapForalls] at hfn'
  have hlen : (params ++ indexArgs).length = ((ownParams ++ indices).map (VExpr.instL levels)).length := by
    have hp := VExpr.takeForalls_domains_length hown
    have hi := VExpr.takeForalls_domains_length hidx
    simp only [List.length_map, List.length_append]
    omega
  obtain ⟨hargs, hfamily⟩ := HasType.mkApps_wrapForalls henv hΓ hfn' H hlen
  have hres : env.IsDefEqU decl.uvars (ownParams ++ indices).reverse result
      (.sort familyType.resultLevel) := by
    simpa only [List.reverse_append] using (show env.IsDefEqU decl.uvars
      (indices.reverse ++ ownParams.reverse) result (.sort familyType.resultLevel) from ⟨_, hresult⟩)
  have hres' := IsDefEqU.closed_telescope_instOuter henv hctx hres hlevels
    (args := params ++ indexArgs) (by simpa only [List.length_reverse, List.length_map] using hlen)
    (by simpa only [List.reverse_reverse] using hargs)
  simp only [VExpr.instL, instOuter_sort, hlevel] at hres'
  exact hfamily.defeqU_r henv hΓ hres'

theorem HasType.proj_result_prop_of_major_proof (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.proj family index major) fieldType)
    (hp : env.HasType U Γ proposition (.sort .zero))
    (hm : env.HasType U Γ major proposition) :
    env.HasType U Γ fieldType (.sort .zero) := by
  obtain ⟨info, levels, params, indexArgs, sourceMajor, resultType, resultLevel,
    hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldType, hmajor, hclosed, hguard⟩ :=
    HasType.proj_inv henv.ordered hΓ H
  have hfamilySort := HasType.projectionFamily_sort henv hΓ hinfo huvars hparams hindices
    (let ⟨_, ht⟩ := hmajor.isType henv.ordered hΓ; ⟨_, ht⟩)
  have hpropSort := hfamilySort.defeqU_l henv hΓ (hmajor.hasType.2.uniqU henv hΓ hm)
  have hzero := (hpropSort.uniqU henv hΓ hp).sort_inv henv hΓ
  have hresultZero : resultLevel ≈ .zero := by
    rcases hguard with hnever | hzero'
    · exact (hnever [] (VLevel.equiv_def.mp hzero [])).elim
    · exact hzero'
  have hproj : env.HasType U Γ (.proj family index major) resultType :=
    .projDF hinfo hlevels huvars hparams hindices hfield hfieldType hmajor hmajor hclosed hguard
  have hsame := hproj.uniqU henv hΓ H
  have hgiven := hfieldType.defeqU_l henv hΓ hsame
  obtain ⟨_, hsort⟩ := hgiven.isType henv.ordered hΓ
  exact .defeqDF (.sortDF (hsort.sort_inv henv.ordered) trivial hresultZero) hgiven

end Lean4Lean.VEnv
