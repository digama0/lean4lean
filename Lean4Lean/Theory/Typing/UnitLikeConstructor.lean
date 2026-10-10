import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.ProjectionShape

/-! A registered unit-like family has a constructor at each well-typed
parameter instance. This is recovered from its declaration and the common
parameter context, without an additional inhabitation assumption. -/

set_option maxHeartbeats 2000000

namespace Lean4Lean.VEnv
open VExpr
variable {env : VEnv} {U : Nat}

theorem HasType.unitLike_constructor (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections name info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hf : info.numFields = 0)
    (H : env.HasType U Γ major (mkApps (.const name levels) params)) :
    env.HasType U Γ (mkApps (.const info.ctorName levels) params)
      (mkApps (.const name levels) params) := by
  obtain ⟨decl, family, ctor, hfamily, hctorMem, hname, hctorUvars, huvars,
    hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
    ⟨common, Hshape, Hparams⟩, Hraw, hnodup⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  have hdomlen : doms.length = info.nparams := by
    have hfields : doms.length - info.nparams = 0 := by
      simpa only [VProjectionInfo.numFields, ← hctorType, harity] using hf
    omega
  have hresultWF := hwf
  rw [hshape] at hresultWF
  obtain ⟨hdomctx, _, hresult⟩ := IsType.wrapForalls_inv henv (by trivial) hresultWF
  have hresultShape : result = mkApps (.const family.name (VLevel.params decl.uvars))
      result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (VExpr.mkApps_getAppFnArgs_eq result).symm
  have hresult' := hresult
  rw [hresultShape] at hresult'
  obtain ⟨_, hfamilyHead⟩ := VExpr.WF.of_mkApps henv hdomctx ⟨_, hresult'⟩
  obtain ⟨ci, hci, _, hcount⟩ := HasType.const_inv henv hdomctx hfamilyHead
  rw [hname, hlookup] at hci
  cases Option.some.inj hci
  have hfamilyUvars : family.uvars = decl.uvars := by simpa using hcount.symm
  obtain ⟨normalized, ownParams, afterParams, indices, result', exprType,
    hnorm, hown, hidx, HownP, hres⟩ := Hshape
  obtain ⟨ctorParams, tail, hctorParams, HctorP⟩ := Hparams
  have hownLen : ownParams.length = info.nparams :=
    (VExpr.takeForalls_domains_length hown).trans hnparams
  have hidxLen : indices.length = 0 :=
    (VExpr.takeForalls_domains_length hidx).trans (hindices.trans hi)
  have hidxNil : indices = [] := List.eq_nil_of_length_eq_zero hidxLen
  subst indices
  have hnormEq : normalized = wrapForalls ownParams result' := by
    rw [VExpr.eq_wrapForalls_of_takeForalls hown,
      VExpr.eq_wrapForalls_of_takeForalls hidx]
    rfl
  have hctorParamsEq : ctorParams = doms := by
    have h1 := VExpr.takeForalls_wrapForalls doms result
    have h2 := hctorParams
    rw [hshape, hnparams, ← hdomlen] at h2
    exact (Prod.mk.inj (Option.some.inj (h2.symm.trans h1))).1
  have hctx : env.IsDefEqCtx decl.uvars [] ownParams.reverse doms.reverse := by
    rw [← hctorParamsEq]
    exact IsDefEqCtx.trans_empty henv (HownP.symm henv.ordered) HctorP
  have htypeWF : env.IsType decl.uvars [] family.type := by
    have ht := henv.ordered.constWF hlookup
    change env.IsType family.uvars [] family.type at ht
    rwa [hfamilyUvars] at ht
  have hnormWF : env.IsType decl.uvars [] normalized :=
    let ⟨u, h⟩ := htypeWF
    ⟨u, h.defeqU_l henv (by trivial) ⟨_, hnorm⟩⟩
  rw [hnormEq] at hnormWF
  have hΓtel := (IsType.wrapForalls_inv henv (by trivial) hnormWF).1
  simp only [List.append_nil] at hΓtel
  obtain ⟨u, hsort⟩ := H.isType henv.ordered hΓ
  obtain ⟨_, hcw⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsort⟩
  obtain ⟨ci', hci', hlsw, hlen'⟩ := HasType.const_inv henv hΓ hcw
  rw [hlookup] at hci'
  cases Option.some.inj hci'
  have hlevels : levels.length = info.uvars := by
    exact hlen'.trans (hfamilyUvars.trans huvars)
  have hc := HasType.const (Γ := Γ) hlookup hlsw hlen'
  have hdef : env.IsDefEqU U Γ (family.type.instL levels) (normalized.instL levels) :=
    ⟨_, (hnorm.instL hlsw).weak0 henv.ordered⟩
  have hc' := hc.defeqU_r henv hΓ hdef
  rw [hnormEq, instL_wrapForalls] at hc'
  obtain ⟨hargsT, _⟩ := HasType.mkApps_wrapForalls henv hΓ hc' ⟨_, hsort⟩
    (by simp only [List.length_map]; omega)
  have hparams : ∀ k (hk : k < params.length) (hk' : k < doms.length),
      env.HasType U Γ params[k] ((doms[k].instL levels).instOuter (params.take k)) := by
    intro k hk hk'
    have hkown : k < ownParams.length := by omega
    obtain ⟨u, hdk⟩ := hctx.reverse_getElem k hkown hk'
    have hΔ₀ : OnCtx (ownParams.take k).reverse (env.IsType decl.uvars) := by
      have he : ownParams.reverse = (ownParams.drop k).reverse ++ (ownParams.take k).reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      rw [he] at hΓtel
      exact hΓtel.of_append
    have hconv := IsDefEqU.closed_telescope_instOuter henv hΔ₀ ⟨_, hdk⟩ hlsw
      (args := params.take k) (by simp; omega) (by
        intro j hj hj'
        simp only [List.length_take] at hj
        have ht := hargsT j (by omega) (by simp; omega)
        simp only [List.reverse_reverse, List.getElem_map, List.getElem_take,
          List.take_take, Nat.min_eq_left (Nat.le_of_lt (show j < k by omega))] at ht ⊢
        exact ht)
    have harg := hargsT k hk (by simpa using hkown)
    simp only [List.getElem_map] at harg
    exact harg.defeqU_r henv hΓ hconv
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hinfo) hlsw hlevels
  rw [← hctorType, hshape, instL_wrapForalls] at hctor
  have hvalue := HasType.mkApps_of_telescope (args := params) hctor
    (by simp only [List.length_map]; omega) (by simpa only [List.getElem_map, List.length_map] using hparams)
  have hhead' : (result.instL levels).getAppFnArgs.1 = .const name levels := by
    rw [VExpr.getAppFnArgs_instL]
    change result.getAppFnArgs.1.instL levels = _
    rw [hhead, hname]
    simp [VExpr.instL, VLevel.params_map_inst levels (hlevels.trans huvars.symm)]
  obtain ⟨idx, hresEq, family', hfamily', hname', hidxCount⟩ :=
    (hvalid.instL levels).instOuter (by simpa only [hname] using hhead') params (by omega)
  have hsame : family' = family := List.eq_of_mem_of_nodup_map
    (VInductDecl.typeNames_nodup hnodup) hfamily' hfamily (by simpa only [hname] using hname')
  have hidxEmpty : idx = [] := List.eq_nil_of_length_eq_zero (by rw [hidxCount, hsame, hindices, hi])
  rw [hresEq, hidxEmpty, List.append_nil, List.take_of_length_le (by omega), hname] at hvalue
  exact hvalue

end Lean4Lean.VEnv
