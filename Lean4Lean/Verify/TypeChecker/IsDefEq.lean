import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.Typing.ProjectionFamilyArity

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

/-- A body that mentions no bound variable, translated under a binder, is translated outside it,
to a term whose lift is its translation under the binder. This is strengthening of the binder:
`isDefEqLambda` and `isDefEqForall` compare such bodies outside the binder, as the C++ kernel's
`is_def_eq_binding` does. -/
theorem lowerClosedBody {c : VContext} {s : State} {m} [mwf : c.MLCWF m]
    (wf : s.WF (c.withMLC m)) (hs : c.venv.Strengthening)
    (b1 : c.venv.IsType c.lparams.length (c.withMLC m).vlctx.toCtx t₂') {fvs : List Expr}
    {bᵢ : Expr} {bᵢ'} (h : bᵢ.looseBVarRange' = 0)
    (a3 : TrExprS c.venv c.lparams ((none, .vlam t₂') :: (c.withMLC m).vlctx)
      (bᵢ.instantiateList fvs 1) bᵢ') :
    ∃ e', (c.withMLC m).TrExprS (bᵢ.instantiateList (default :: fvs)) e' ∧
      c.venv.IsDefEqU c.lparams.length (t₂' :: (c.withMLC m).vlctx.toCtx) bᵢ' e'.lift := by
  have e1 : bᵢ.instantiateList fvs 1 = bᵢ :=
    Expr.instantiateList'_eq_self (by rw [h]; exact Nat.zero_le _)
  have e2 : bᵢ.instantiateList (default :: fvs) = bᵢ :=
    Expr.instantiateList'_eq_self (by rw [h]; exact Nat.zero_le _)
  rw [e1] at a3; rw [e2]
  let v : FVarId := ⟨s.ngen.curr⟩
  have hΔ : VLCtx.WF c.venv c.lparams.length ((some (v, []), .vlam t₂') :: m.vlctx) := by
    refine ⟨mwf.1.tr.wf, ?_, b1⟩
    rintro _ _ ⟨⟩; simp; exact fun h => s.ngen.not_reserves_self (wf.ngen_wf _ h)
  have hw := a3.wf c.Ewf.orderedStrong
    (show VLCtx.WF c.venv c.lparams.length ((none, .vlam t₂') :: m.vlctx) from
      ⟨mwf.1.tr.wf, nofun, b1⟩)
  have := a3.inst_fvar c.Ewf.orderedStrong hΔ
  rw [Expr.instantiate1'_eq_self (by rw [h]; exact Nat.zero_le _)] at this
  obtain ⟨e₀, he, rfl⟩ := this.restrictFV_inv c.Ewf (.skip_fvar _ _ .refl) hΔ
    (by simpa using a3.fvarsIn)
  exact ⟨e₀, he, hw⟩

theorem isDefEqLambda.WF {c : VContext} {s : State}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqLambda e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqLambda; let c' := c.withMLC m
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂; (simp [hsubst]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .lam (ty' := t₁') (body' := b₁') ⟨_, a1⟩ a2 a3 := he₁
  let .lam (ty' := t₂') (body' := b₂') b1 b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.lam b₁') (t₂'.lam b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hsubst]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F
  split <;> rename_i hg
  · extract_lets d₂'
    have : d₂' = d₂.instantiateList fvs := by split at hx <;> [simp [d₂', hsubst]; exact hx]
    clear_value d₂'; subst this
    refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
    have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
    have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
    refine isDefEqLambda.WF (mwf := mwf') (fvs := .fvar v :: fvs) (by simp [hsubst]) a3'' b3'
      |>.mono fun _ _ _ h hb => ?_
    have ⟨_, bb⟩ := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb)
    exact ⟨_, .symm <| .lamDF tt'.symm <| bb.symm⟩
  · simp only [Bool.or_eq_true, not_or, Expr.hasLooseBVars] at hg
    obtain ⟨h1, h2⟩ := hg
    simp at h1 h2
    refine .stateWF fun wf => ?_
    have hs := c.strengthening
    let ⟨_, a4, a5⟩ := lowerClosedBody wf hs b1 h1 a3'
    let ⟨_, b4, b5⟩ := lowerClosedBody wf hs b1 h2 b3
    exact isDefEqLambda.WF (fvs := default :: fvs) (by simp [hsubst]) a4 b4
      |>.mono fun _ _ _ h hb =>
      have hΓ := ⟨c'.Δwf, b1⟩
      have ⟨_, bb⟩ := eq.symm.trans c'.Ewf hΓ a5
        |>.trans c'.Ewf hΓ ((h hb).weak c'.Ewf (B := t₂')) |>.trans c'.Ewf hΓ b5.symm
      ⟨_, .symm <| .lamDF tt'.symm bb.symm⟩

theorem isDefEqForall.WF {c : VContext} {s : State}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqForall e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqForall; let c' := c.withMLC m
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂; (simp [hsubst]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .forallE (ty' := t₁') (body' := b₁') ⟨_, a1⟩ _ a2 a3 := he₁
  let .forallE (ty' := t₂') (body' := b₂') b1 ⟨_, bT⟩ b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.forallE b₁') (t₂'.forallE b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hsubst]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F
  split <;> rename_i hg
  · extract_lets d₂'
    have : d₂' = d₂.instantiateList fvs := by split at hx <;> [simp [d₂', hsubst]; exact hx]
    clear_value d₂'; subst this
    refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
    have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
    have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
    refine isDefEqForall.WF (mwf := mwf') (fvs := .fvar v :: fvs) (by simp [hsubst]) a3'' b3'
      |>.mono fun _ _ _ h hb => ?_
    have bb := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb) |>.of_r c'.Ewf mwf'.1.tr.wf.toCtx bT
    exact ⟨_, .symm <| .forallEDF tt'.symm <| bb.symm⟩
  · simp only [Bool.or_eq_true, not_or, Expr.hasLooseBVars] at hg
    obtain ⟨h1, h2⟩ := hg
    simp at h1 h2
    refine .stateWF fun wf => ?_
    have hs := c.strengthening
    let ⟨_, a4, a5⟩ := lowerClosedBody wf hs b1 h1 a3'
    let ⟨_, b4, b5⟩ := lowerClosedBody wf hs b1 h2 b3
    exact isDefEqForall.WF (fvs := default :: fvs) (by simp [hsubst]) a4 b4
      |>.mono fun _ _ _ h hb =>
      have hΓ := ⟨c'.Δwf, b1⟩
      have bb := eq.symm.trans c'.Ewf hΓ a5 |>.trans c'.Ewf hΓ ((h hb).weak c'.Ewf (B := t₂'))
        |>.trans c'.Ewf hΓ b5.symm |>.of_r c'.Ewf hΓ bT
      ⟨_, .symm <| .forallEDF tt'.symm bb.symm⟩

theorem quickIsDefEq.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (quickIsDefEq e₁ e₂ useHash) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold quickIsDefEq
  refine .bind (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h => ?_
  · intro _ mwf wf _ s₁ eq
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at eq
    split at eq; rename_i b _ b' m hm
    change let s' := _; (_, s') = _ at eq; extract_lets s' at eq
    injection eq; subst b' s₁
    obtain ⟨Δ', hΔ', hm'⟩ := wf.ectx
    have ⟨ewf, _, h1⟩ := EquivManager.isEquiv.WF hm' hm
    refine let vs' := s'; ⟨vs', rfl, .rfl, { wf with ectx := ⟨Δ', hΔ', ewf⟩ }, ?_⟩
    exact fun h => wf.eqv_uniq hΔ' (h1 h) he₁ he₂
  split <;> [exact .pure fun _ => h ‹_›; split]
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqLambda.WF (subst := #[]) (fvs := []) rfl (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqForall.WF (subst := #[]) (fvs := []) rfl (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · have .sort hu := he₁; have .sort hv := he₂
    refine .pure fun h => ⟨_, .sortDF (.of_ofLevel hu) (.of_ofLevel hv) ?_⟩
    exact Level.isEquiv_wf (toLBool_true.1 h) hu hv
  · let .mdata he₁ := he₁; let .mdata he₂ := he₂
    exact .toLBoolM <| isDefEq.WF he₁ he₂
  · cases he₁
  · rename_i a1 a2 _; refine .pure fun h => ?_
    simp at h; subst h; exact he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂
  · exact .pure nofun

theorem isDefEqArgs.WF {c : VContext} {s : State}
    (H : ∃ e₁', c.TrExprS e₁.getAppFn e₁' ∧ ∃ e₂', c.TrExprS e₂.getAppFn e₂' ∧ c.IsDefEqU e₁' e₂')
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqArgs e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqArgs; split <;> (unfold Expr.getAppFn at H)
  · let .app a1 a2 a3 a4 := he₁
    let .app b1 b2 b3 b4 := he₂
    refine (isDefEq.WF a4 b4).bind fun _ _ _ h2 => ?_
    split <;> [exact .pure nofun; rename_i hb2]
    refine (isDefEqArgs.WF H a3 b3).mono fun _ _ _ h1 hb1 => ?_
    simp at hb2
    exact ⟨_, .appDF ((h1 hb1).of_l c.Ewf c.Δwf a1) ((h2 hb2).of_l c.Ewf c.Δwf a2)⟩
  · exact .pure nofun
  · exact .pure nofun
  · refine .pure fun _ => ?_
    simp [*] at H; let ⟨_, h1, _, h2, h3⟩ := H
    have a1 := he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) h1
    have a2 := he₂.uniq c.Ewf (.refl c.Ewf c.Δwf) h2
    exact a1.trans c.Ewf c.Δwf h3 |>.trans c.Ewf c.Δwf a2.symm

theorem tryEtaExpansionCore.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansionCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaExpansionCore; split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨ty₁, a1, a2, a3, a4⟩ => ?_
  refine (whnf.WF a3).bind fun _ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [skip; exact .pure nofun]
  let .forallE (ty' := ty') c1 c2 c3 c4 := b2
  replace a4 := a4.defeqU_r c.Ewf c.Δwf b3.symm
  refine (isDefEq.WF he₁ (.lam c1 c3 (.app (a4.weak c.Ewf) (.bvar .zero) (
    Expr.liftLooseBVars_eq_self (c.mlctx.noBV ▸ a2.closed).looseBVarRange_le ▸
      a2.weakBV c.Ewf (.skip (.vlam ty') .refl)) (.bvar rfl)))).mono fun _ _ _ h hb => ?_
  exact (h hb).trans c.Ewf c.Δwf ⟨_, .eta a4⟩

theorem tryEtaExpansion.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansion e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaExpansion, orM, toBool]
  refine (tryEtaExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem tryEtaStructCore.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaStructCore
  split <;> [rename_i f ls hf; exact .pure nofun]
  refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hci => ?_
  split <;> [rename_i fInfo; exact .pure nofun]
  split <;> [rename_i harity; exact .pure nofun]
  split <;> [rename_i hnonrec; exact .pure nofun]
  -- the constructor is listed by its owner, which is a non-recursive structure
  obtain ⟨sInfo, hfind, hmem, hunsafe⟩ := c.constructorOwners f fInfo hci
  have hsingle : sInfo.ctors = [f] := by
    revert hnonrec; unfold Lean.Kernel.Environment.isNonRecStructure; rw [hfind]
    intro h; split at h
    · rename_i heq; cases heq; simp only [List.mem_singleton] at hmem; subst hmem; rfl
    · cases h
  refine (inferType.WF he₁).bind fun tType _ _ ⟨tT', _, _, htT, htT'⟩ => ?_
  refine (inferType.WF he₂).bind fun sType _ _ ⟨sT', _, _, hsT, hsT'⟩ => ?_
  refine (isDefEq.WF htT hsT).bind fun b _ _ hb => ?_
  split <;> [skip; exact .pure nofun]
  have hb := hb ‹_›
  refine (inferType.WF htT).bind fun tTT _ _ ⟨tTT', _, _, htTT, htTT'⟩ => ?_
  refine (whnf.WF htTT).bind fun w _ _ ⟨_, w', hw, hwdefeq⟩ => ?_
  split <;> [rename_i u; exact .pure nofun]
  split <;> [rename_i hnz; exact .pure nofun]
  have harity := beq_iff_eq.1 harity
  -- the constructor application
  have he₂'' : c.TrExprS ((Expr.const f ls).mkAppList e₂.getAppArgsList) e₂' := by
    rw [← hf, e₂.mkAppList_getAppArgsList]; exact he₂
  have ⟨fn', stk⟩ := AppStack.build he₂''
  have ⟨args', hargs, hs'⟩ := stk.translatedArguments
  have .const (us' := ls') hfc hls hlen := stk.tr
  have hceq := he₂''.uniq c.Ewf (.refl c.Ewf c.Δwf) hs'
  have hargsLen : args'.length = e₂.getAppArgsList.length :=
    (Lean4Lean.List.Forall₂.length_eq hargs).symm
  -- registry facts
  obtain ⟨_, habstract⟩ := c.familyConstant hfind hci hunsafe hfc
  obtain ⟨info, hinfo, hname, decl, doms, result, hwf, hctor, hshape, hvalid, hhead, hdn, hdu, hle,
    hnp, hnf, hnf', hsp, hsi, hidxs, -, hsort, -⟩ :=
    VContext.registryShape hfind habstract hsingle hci rfl
  subst hname
  have hnindices : info.nindices = 0 := by
    rw [← hsi]
    revert hnonrec; unfold Lean.Kernel.Environment.isNonRecStructure; rw [hfind]
    intro h; split at h
    · rename_i heq; cases heq; rfl
    · cases h
  have hlenArgs : args'.length = doms.length := by
    rw [hargsLen, ← List.length_reverse, Expr.getAppArgsList_reverse, ← Expr.getAppNumArgs_eq,
      harity, hnp, hnf]; omega
  -- typing of the constructor application against its telescope
  have ⟨_, hcw⟩ := (TrExprS.const hfc hls hlen).wf c.Ewf c.Δwf
  have ⟨ci', hci', hlsWF, hlen'⟩ := VEnv.HasType.const_inv c.Ewf.orderedStrong c.Δwf.toCtx hcw
  rw [hctor] at hci'; cases Option.some.inj hci'
  have hconst : c.HasType (.const info.ctorName ls') (info.ctorType.instL ls') :=
    VEnv.HasType.const hctor hlsWF hlen'
  have hf' : c.HasType (.const info.ctorName ls')
      (VExpr.wrapForalls (doms.map (·.instL ls')) (result.instL ls')) := by
    rwa [hshape, VExpr.instL_wrapForalls] at hconst
  have hs'wf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (VExpr.mkApps (.const info.ctorName ls') args') :=
    hs'.wf c.Ewf c.Δwf
  have ⟨hargsTy, hsTy⟩ := VEnv.HasType.mkApps_wrapForalls c.Ewf c.Δwf.toCtx hf' hs'wf (by simp [hlenArgs])
  obtain ⟨res, Hw, -⟩ := VEnv.HasType.mkApps_telescope c.Ewf c.Δwf.toCtx hconst hs'wf (by
    rw [hshape, VExpr.instL_wrapForalls, show args'.length = (doms.map (·.instL ls')).length by simp [hlenArgs]]
    exact VExpr.takeForalls_wrapForalls _ _)
  rw [hshape, VExpr.instL_wrapForalls] at Hw
  -- the canonical type of the constructor application: no indices
  have hhead' : (result.instL ls').getAppFnArgs.1 = .const fInfo.induct ls' := by
    rw [VExpr.getAppFnArgs_instL]
    show (result.getAppFnArgs.1.instL ls') = _
    rw [hhead]
    simp [VExpr.instL, VLevel.params_map_inst ls' (hlen'.trans hdu.symm)]
  obtain ⟨idx', hresEq, type, htype, hname, hidxLen⟩ :=
    (hvalid.instL ls').instOuter hhead' args' (by omega)
  have hidx' : idx' = [] := by
    rw [hidxs type htype hname, hnindices] at hidxLen; exact List.eq_nil_of_length_eq_zero hidxLen
  subst hidx'
  rw [hresEq, List.append_nil] at hsTy
  -- `t` has the structure type
  have htS : c.HasType e₁' (VExpr.mkApps (.const fInfo.induct ls') (args'.take info.nparams)) := by
    have h1 : c.HasType e₂' sT' := hsT'
    have h2 := (hceq.of_l c.Ewf c.Δwf h1).hasType.2
    have h3 := h2.uniqU c.Ewf c.Δwf hsTy
    rw [hdn] at h3
    exact (htT'.defeqU_r c.Ewf c.Δwf hb).defeqU_r c.Ewf c.Δwf h3
  rw [hdn] at hsTy hresEq
  have hP'len : (args'.take info.nparams).length = info.nparams := by simp; omega
  -- the sort of the structure type is never zero
  have .sort (u' := u') hu' := hw
  have hguard : (info.resultLevel.inst ls').IsNeverZero := by
    have h1 : c.HasType tT' (.sort u') := htTT'.defeqU_r c.Ewf c.Δwf hwdefeq.symm
    have h2 : c.HasType (VExpr.mkApps (.const fInfo.induct ls') (args'.take info.nparams)) (.sort u') := by
      have h3 : c.HasType e₂' sT' := hsT'
      have h4 := (hceq.of_l c.Ewf c.Δwf h3).hasType.2
      have h5 := h4.uniqU c.Ewf c.Δwf hsTy
      exact h1.defeqU_l c.Ewf c.Δwf (hb.trans c.Ewf c.Δwf h5)
    have h6 := hsort ls' _ hlen' (by omega) ⟨_, h2⟩
    have h7 := h2.uniqU c.Ewf c.Δwf h6
    exact (ofLevel_isNeverZero hu' hnz).of_equiv (h7.sort_inv c.Ewf c.Δwf)
  have hclosed : info.ctorType.Closed := by
    have ⟨_, h⟩ := hwf
    exact VExpr.WF.closedN c.Ewf.orderedStrong ⟨_, h⟩ trivial
  have hTwf : c.IsDefEqU (VExpr.wrapForalls (doms.map (·.instL ls')) (result.instL ls'))
      (VExpr.wrapForalls (doms.map (·.instL ls')) (result.instL ls')) :=
    let ⟨_, h⟩ := VEnv.IsDefEq.isType c.Ewf.orderedStrong c.Δwf.toCtx hf'; ⟨_, h⟩
  have hdl : (doms.map (·.instL ls')).length = doms.length := by simp
  -- the loop invariant: the projections of `t` processed so far are the constructor's arguments
  let inv (k : Nat) : Prop := ∀ j (hj : j < k) (hj' : info.nparams + j < doms.length),
    c.venv.IsDefEq c.lparams.length c.vlctx.toCtx (.proj fInfo.induct j e₁')
      (args'[info.nparams + j]'(by omega))
      ((doms[info.nparams + j].instL ls').instOuter (args'.take (info.nparams + j)))
  have hsize : e₂.getAppArgs.size = args'.length := by
    rw [hargsLen, ← Expr.getAppArgs_toList, Array.length_toList]
  have hargsGet : ∀ i (hi : i < e₂.getAppArgs.size),
      c.TrExprS e₂.getAppArgs[i] (args'[i]'(by omega)) := by
    intro i hi
    have := Lean4Lean.List.forall₂_getElem hargs i (by rw [← hargsLen]; omega) (by omega)
    simpa [← Expr.getAppArgs_toList] using this
  have loopWF : ∀ (m : Nat) {s : State} (i : Nat), m = args'.length - i → info.nparams ≤ i →
      inv (i - info.nparams) →
      RecM.WF c s (tryEtaStructCore.loop e₁ fInfo e₂.getAppArgs i) fun b _ =>
        b = true → inv (args'.length - info.nparams) := by
    intro m
    induction m with
    | zero =>
      intro s i hm hni hinv
      unfold tryEtaStructCore.loop
      rw [dif_neg (by omega)]
      refine .pure fun _ j hj hj' => hinv j (by omega) hj'
    | succ m ih =>
      intro s i hm hni hinv
      unfold tryEtaStructCore.loop
      have hi : i < e₂.getAppArgs.size := by omega
      rw [dif_pos hi]
      have hk : info.nparams + (i - fInfo.numParams) = i := by omega
      have hkd : info.nparams + (i - fInfo.numParams) < doms.length := by omega
      -- the field type of the current projection is definitionally the constructor's domain
      have hbs : List.Forall₂ (c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx)
          (args'.take info.nparams ++
            (List.range (i - fInfo.numParams)).map fun j => VExpr.proj fInfo.induct j e₁')
          (args'.take (info.nparams + (i - fInfo.numParams))) := by
        rw [List.take_add]
        refine List.Forall₂.append' (List.forall₂_of_getElem rfl fun j hj hj' => ?_)
          (List.forall₂_of_getElem (by simp; omega) fun j hj hj' => ?_)
        · simp only [List.getElem_take]
          exact ⟨_, hargsTy j (by simp at hj; omega) (by simp at hj; omega)⟩
        · simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
          exact ⟨_, hinv j (by simp at hj; omega) (by simp at hj; omega)⟩
      have hDeq := VEnv.InstForallsC.domain_defeq c.Ewf c.Δwf.toCtx Hw (by simpa using hlenArgs) rfl
        (by simpa using hkd) hTwf (by simp; omega) hbs
      simp only [List.getElem_map] at hDeq
      have hfieldk := VProjectionInfo.fieldType_eq_instOuter info hshape hlen' hP'len hkd
        (typeName := fInfo.induct) (major := e₁')
      have hDty := VEnv.IsDefEq.isType c.Ewf.orderedStrong c.Δwf.toCtx
        (hargsTy (info.nparams + (i - fInfo.numParams)) (by omega) (by simpa using hkd))
      simp only [List.getElem_map] at hDty
      have ⟨fl, hFty⟩ : c.venv.IsType c.lparams.length c.vlctx.toCtx
          ((doms[info.nparams + (i - fInfo.numParams)].instL ls').instOuter
            (args'.take info.nparams ++
              (List.range (i - fInfo.numParams)).map fun j => VExpr.proj fInfo.induct j e₁')) :=
        hDty.imp fun _ h => h.defeqU_l c.Ewf c.Δwf hDeq.symm
      have hprojk : c.HasType (.proj fInfo.induct (i - fInfo.numParams) e₁') _ :=
        VEnv.IsDefEq.projDF hinfo hlsWF hlen' hP'len (indexArgs := []) (by simp [hnindices]) hfieldk hFty
          (by rw [List.append_nil]; exact htS) (by rw [List.append_nil]; exact htS) hclosed
          (Or.inl hguard)
      have hprojTr : c.TrExprS (.proj fInfo.induct (i - fInfo.numParams) e₁)
          (.proj fInfo.induct (i - fInfo.numParams) e₁') :=
        .proj he₁ ⟨_, hprojk⟩
      refine (isDefEq.WF hprojTr (hargsGet i hi)).bind fun b _ _ hb => ?_
      split <;> [skip; exact .pure nofun]
      have hb := hb ‹_›
      refine ih (i + 1) (by omega) (by omega) fun j hj hj' => ?_
      by_cases hji : j = i - fInfo.numParams
      · subst hji
        simp only [hk]
        have h2 := hargsTy i (by omega) (by omega)
        simp only [List.getElem_map] at h2
        exact hb.of_r c.Ewf c.Δwf h2
      · exact hinv j (by omega) hj'
  refine (loopWF (args'.length - fInfo.numParams) fInfo.numParams rfl (by omega)
    (fun j hj _ => by omega)).mono fun b _ _ H hb => ?_
  have hinv := H hb
  -- congruence along the constructor spine: the arguments are the projections of `t`
  have hnumF : info.numFields = args'.length - info.nparams := by rw [hnf', hnf, hlenArgs]
  have hcongr := VEnv.IsDefEq.mkApps_congr (args := args')
    (args' := args'.take info.nparams ++
      (List.range info.numFields).map fun j => VExpr.proj fInfo.induct j e₁') hf'
    (by simp [hlenArgs]) (by simp [hnumF]; omega) fun j hj hj' hj'' => by
      by_cases hjn : j < info.nparams
      · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
        exact hargsTy j hj hj'
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_range, List.length_take]
        have hjn' : info.nparams + (j - min info.nparams args'.length) = j := by omega
        have := (hinv (j - min info.nparams args'.length) (by omega) (by omega)).symm
        simp only [hjn'] at this ⊢
        exact this
  rw [hresEq, List.append_nil] at hcongr
  have heta := VEnv.IsDefEq.structEta hinfo hP'len hnindices htS hcongr.hasType.2
  exact VEnv.IsDefEqU.trans c.Ewf c.Δwf ⟨_, heta.symm.trans hcongr.symm⟩ hceq.symm

theorem tryEtaStruct.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStruct e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaStruct, orM, toBool]
  refine (tryEtaStructCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaStructCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem isDefEqApp.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqApp e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqApp; split <;> [skip; exact .pure nofun]
  rw [Expr.withApp_eq, Expr.withApp_eq]
  split <;> [rename_i eq; exact .pure nofun]
  have ⟨_, he₁'⟩ := AppStack.build <| e₁.mkAppList_getAppArgsList ▸ he₁
  have ⟨_, he₂'⟩ := AppStack.build <| e₂.mkAppList_getAppArgsList ▸ he₂
  refine (isDefEq.WF he₁'.tr he₂'.tr).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure nofun]
  let rec loop.WF {s args₁ args₂ f₁ f₂ f₁' f₂' eq i} (l₁ r₁ l₂ r₂)
      (h₁ : args₁.toList = l₁ ++ r₁) (hi₁ : l₁.length = i)
      (h₂ : args₂.toList = l₂ ++ r₂) (hi₂ : l₂.length = i)
      (he₁ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₁ l₁) f₁' r₁)
      (he₂ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₂ l₂) f₂' r₂)
      (H1 : c.IsDefEqU f₁' f₂') :
      RecM.WF c s (loop args₁ args₂ eq i) fun b _ => b →
        ∀ e₁', c.TrExprS (f₁.mkAppList args₁.toList) e₁' →
        ∀ e₂', c.TrExprS (f₂.mkAppList args₂.toList) e₂' → c.IsDefEqU e₁' e₂' := by
    unfold loop; split <;> rename_i h
    · have hr₁ : r₁.length > 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length > 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      let .app (a := a₁) (as := r₁) a1 a2 a3 a4 a5 := he₁
      let .app (a := a₂) (as := r₂) b1 b2 b3 b4 b5 := he₂
      simp [
        show args₁[i] = a₁ by cases args₁; cases h₁; simp [hi₁],
        show args₂[i] = a₂ by cases args₂; cases h₂; simp [hi₂]]
      refine (isDefEq.WF a4 b4).bind fun _ _ _ h => ?_
      split <;> [skip; exact .pure nofun]
      have H := (H1.of_l c.Ewf c.Δwf a1).appDF <| (h ‹_›).of_l c.Ewf c.Δwf a2
      exact loop.WF (l₁ ++ [a₁]) r₁ (l₂ ++ [a₂]) r₂
        (by simp [h₁]) (by simp [hi₁]) (by simp [h₂]) (by simp [hi₂])
        (by simp [a5]) (by simp [b5]) ⟨_, H⟩
    · have hr₁ : r₁.length = 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length = 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      simp at hr₁ hr₂; subst r₁ r₂; simp at h₁ h₂; subst l₁ l₂
      refine .pure fun _ _ h1 _ h2 => ?_
      have u1 := h1.uniq c.Ewf (.refl c.Ewf c.Δwf) he₁.tr
      have u2 := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂.tr
      exact u1.trans c.Ewf c.Δwf H1 |>.trans c.Ewf c.Δwf u2.symm
  refine loop.WF [] _ [] _ (i := 0) (by simp [Expr.getAppArgs_toList]) rfl
    (by simp [Expr.getAppArgs_toList]) rfl he₁' he₂' (h ‹_›) |>.mono fun _ _ _ h2 hb => ?_
  simp [Expr.getAppArgs_toList, Expr.mkAppList_getAppArgsList] at h2
  exact h2 hb _ he₁ _ he₂

theorem getSortLevel.WF
    (he : c.TrExprS e e') : (getSortLevel e).WF c s fun l _ =>
      ∃ u', VLevel.ofLevel c.lparams l = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF he).bind fun ty _ le ⟨ty', _, _, h1, h2⟩ => ?_
  refine (ensureSortCore.WF h1).bind fun ty _ le h => ?_
  obtain ⟨⟨u, rfl⟩, ⟨ty₂, h3, h4⟩, _⟩ := h
  let .sort hu := h3
  exact .pure ⟨_, hu, h2.defeqU_r c.Ewf c.Δwf h4.symm⟩

theorem isProp.WF
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ => b → c.HasType e' (.sort .zero) := by
  refine (getSortLevel.WF he).bind fun l _ le ⟨u', hu, h⟩ => .pure fun H => ?_
  exact h.defeqU_r c.Ewf c.Δwf
    ⟨_, .sortDF (.of_ofLevel hu) trivial (ofLevel_isAlwaysZero hu H)⟩

theorem isDefEqProofIrrel.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqProofIrrel e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqProofIrrel
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, a1, a2, a3, a4⟩ => ?_
  refine (isProp.WF a3).bind fun _ _ _ h1 => ?_
  split <;> [exact .pure nofun; skip]
  rename_i h; simp at h
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, b1, b2, b3, b4⟩ => .toLBoolM ?_
  refine (isDefEq.WF a3 b3).mono fun _ _ _ h2 hb => ?_
  exact ⟨_, .proofIrrel (h1 h) a4 (b4.defeqU_r c.Ewf c.Δwf (h2 hb).symm)⟩

theorem cacheFailure.WF {c : VContext} {s : State} :
    (cacheFailure e₁ e₂).WF c s fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  exact ⟨_, rfl, .rfl, { wf with }, ⟨⟩⟩

theorem tryUnfoldProjApp.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    (tryUnfoldProjApp e).WF c s fun oe _ =>
    ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold tryUnfoldProjApp; extract_lets f
  split <;> [exact .pure nofun; skip]
  refine (whnfCore.WF he).bind fun _ _ _ h => ?_
  refine .pure fun _ => ?_
  split <;> rintro ⟨⟩; exact h

def _root_.Lean4Lean.TypeChecker.ReductionStatus.WF
    (c : VContext) (e₁' e₂' : VExpr) (allowContinue := false) : ReductionStatus → Prop
  | .continue e₁ e₂ => allowContinue ∧ c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .unknown e₁ e₂ | .false e₁ e₂ => c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .true => c.IsDefEqU e₁' e₂'

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.bool
    (H1 : c.TrExpr e₁ e₁') (H2 : c.TrExpr e₂ e₂') (H : b = true → c.IsDefEqU e₁' e₂') :
    ReductionStatus.WF c e₁' e₂' allowContinue (.bool e₁ e₂ b) :=
  match b with
  | .false => ⟨H1, H2⟩
  | .true => H rfl

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.defeq
    (h1 : c.IsDefEqU e₁' e₁'') (h2 : c.IsDefEqU e₂' e₂'')
    (H : ReductionStatus.WF c e₁' e₂' ac r) : ReductionStatus.WF c e₁'' e₂'' ac r :=
  match r, H with
  | .continue .., ⟨a1, a2, a3⟩ =>
    ⟨a1, a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .unknown .., ⟨a2, a3⟩ | .false .., ⟨a2, a3⟩ =>
    ⟨a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .true, h => h1.symm.trans c.Ewf c.Δwf h |>.trans c.Ewf c.Δwf h2

theorem lazyDeltaReductionStep.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReductionStep e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
  unfold lazyDeltaReductionStep
  refine .getEnv ?_; extract_lets delta cont F1 F2
  have hdelta {s e e' ci} (he : c.TrExprS e e') (H : isDelta c.env e = some ci) :
      (delta e).WF c s fun r _ => c.TrExpr r e' := by
    let ⟨n, h1, ⟨_, h2⟩, ls, h3, _⟩ := isDelta_is_some.1 H
    have ⟨_, stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
    have .const a1 a2 a3 := h3 ▸ stk.tr
    have ⟨b1, b2, b3, b4⟩ := c.trenv.find?_uniq h1 a1
    refine (unfoldDefinition.WF he).bind fun oe _ _ H => ?_
    obtain _ | e' := oe; · cases H h1 h2 h3 (a3.trans b3.symm)
    have ⟨_, _, c1, c2⟩ := H
    exact (whnfCore.WF c1).mono fun x _ _ h => h.2.defeq c.Ewf c.Δwf c2
  have hcont {s e₁ e₂} (he₁ : c.TrExpr e₁ e₁') (he₂ : c.TrExpr e₂ e₂') :
      (cont e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
    let ⟨_, se₁, de₁⟩ := he₁; let ⟨_, se₂, de₂⟩ := he₂
    refine (quickIsDefEq.WF se₁ se₂).bind fun _ _ _ h => .pure ?_; split
    · exact ⟨rfl, he₁, he₂⟩
    · exact de₁.symm.trans c.Ewf c.Δwf (h rfl) |>.trans c.Ewf c.Δwf de₂
    · exact ⟨he₁, he₂⟩
  split
  · exact .pure ⟨he₁.trExpr c.Ewf c.Δwf, he₂.trExpr c.Ewf c.Δwf⟩
  · refine (tryUnfoldProjApp.WF he₂).bind fun _ _ _ h => ?_; split
    · exact hcont (he₁.trExpr c.Ewf c.Δwf) (h _ rfl).2
    · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  · refine (tryUnfoldProjApp.WF he₁).bind fun _ _ _ h => ?_; split
    · exact hcont (h _ rfl).2 (he₂.trExpr c.Ewf c.Δwf)
    · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  rename_i dt dt' hd1 hd2; extract_lets ht hs; split <;> [skip; split]
  · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  have hF1 {s} : (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' true :=
    (hdelta he₁ ‹_›).bind fun _ _ _ h1 => (hdelta he₂ ‹_›).bind fun _ _ _ h2 => hcont h1 h2
  refine .get ?_; split <;> [skip; exact hF1]
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  rename_i h1 h2; simp at h1
  cases ptrEqConstantInfo_eq h1.1.1.2
  have ⟨n₁, b1₁, ⟨_, b2₁⟩, ls₁, b3₁, _⟩ := isDelta_is_some.1 hd1
  have ⟨n₂, b1₂, ⟨_, b2₂⟩, ls₂, b3₂, _⟩ := isDelta_is_some.1 hd2
  simp [b3₁, b3₂, Expr.constLevels!] at h2
  have ⟨_, stk₁⟩ := AppStack.build (e₁.mkAppList_getAppArgsList ▸ he₁)
  have ⟨_, stk₂⟩ := AppStack.build (e₂.mkAppList_getAppArgsList ▸ he₂)
  have .const (us' := ls₁) c1₁ c2₁ c3₁ := b3₁ ▸ stk₁.tr
  have .const (us' := ls₂) c1₂ c2₂ c3₂ := b3₂ ▸ stk₂.tr
  cases (c.trenv.find?_uniq b1₁ c1₁).1
  cases (c.trenv.find?_uniq b1₂ c1₂).1
  cases c1₁.symm.trans c1₂
  have := VEnv.IsDefEq.constDF c1₁
    (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2₁) (.of_mapM_ofLevel c2₂)
    ((List.mapM_eq_some.1 c2₁).length_eq.symm.trans c3₁)
    (Level.isEquivList_wf h2 c2₁ c2₂)
  refine (isDefEqArgs.WF ⟨_, stk₁.tr, _, stk₂.tr, _, this⟩ he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  exact .pure <| h ‹_›

theorem isNatZero_wf {c : VContext} (H : isNatZero e) (h : c.TrExprS e e') : e' = .natZero := by
  have h1 : c.TrExprS (.lit (.natVal 0)) e' := by
    simp [isNatZero] at H; obtain H|H := H
    · have := h.eqv H; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · split at H <;> [exact h; cases H]
  have := TrExprS.lit_has_type (l := .natVal 0) h1
  exact h1.unique (TrExprS.natLit c.hasPrimitives this 0).1

theorem isNatSuccOf?_wf {c : VContext} (H : isNatSuccOf? e = some e₁)
    (h : c.TrExprS e e') : ∃ x, c.TrExprS e₁ x ∧ e' = .app .natSucc x := by
  unfold isNatSuccOf? at H; split at H <;> cases H
  · rename_i n
    have := TrExprS.lit_has_type (l := .natVal (n+1)) h
    refine ⟨_, (TrExprS.natLit c.hasPrimitives this n).1, ?_⟩
    exact h.unique (TrExprS.natLit c.hasPrimitives this (n+1)).1
  · let .app a1 a2 a3 a4 := h
    let .const b1 b2 b3 := a3
    cases c.hasPrimitives.natSucc b1
    simp at b3; subst b3; simp at b2; subst b2
    exact ⟨_, a4, rfl⟩

theorem isDefEqOffset.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (isDefEqOffset e₁ e₂).WF c s fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqOffset; split
  · rename_i h; simp at h
    cases isNatZero_wf h.1 he₁; cases isNatZero_wf h.2 he₂
    exact .pure fun _ => .refl <| he₁.wf c.Ewf c.Δwf
  · split <;> [skip; exact .pure nofun]
    obtain ⟨_, a1, rfl⟩ := isNatSuccOf?_wf ‹_› he₁
    obtain ⟨_, b1, rfl⟩ := isNatSuccOf?_wf ‹_› he₂
    refine .toLBoolM <| (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    let ⟨_, de'⟩ := he₁.wf c.Ewf c.Δwf
    let ⟨_, _, c1, c2⟩ := de'.hasType.1.app_inv c.Ewf c.Δwf
    exact ⟨_, c1.appDF <| (h hb).of_l c.Ewf c.Δwf c2⟩

theorem lazyDeltaReduction.loop.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReduction.loop e₁ e₂ n).WF c s fun r _ => r.WF c e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; extract_lets F1
  refine (isDefEqOffset.WF he₁ he₂).bind fun _ _ _ h => ?_; split
  · exact .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) (he₂.trExpr c.Ewf c.Δwf) fun hb =>
      h (by simpa using hb)
  suffices hF1 : ∀ {s}, (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' by
    refine .readThe ?_; split <;> [skip; exact hF1]
    refine (reduceNat.WF he₁).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF a1 he₂).bind fun _ _ _ h => ?_
      refine .pure <| .bool ⟨_, a1, a2⟩ (he₂.trExpr c.Ewf c.Δwf) fun hb => ?_
      exact a2.symm.trans c.Ewf c.Δwf (h hb)
    refine (reduceNat.WF he₂).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF he₁ a1).bind fun _ _ _ h => ?_
      refine .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) ⟨_, a1, a2⟩ fun hb => ?_
      exact (h hb).trans c.Ewf c.Δwf a2
    exact hF1
  intro s; unfold F1; refine .getEnv ?_
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (lazyDeltaReductionStep.WF he₁ he₂).bind fun r _ _ h => ?_
  cases r with
  | «continue» =>
    let ⟨_, ⟨_, a1, a2⟩, ⟨_, b1, b2⟩⟩ := h
    exact (ih a1 b1).mono fun _ _ _ h => h.defeq a2 b2
  | _ => exact .pure h

theorem tryStringLitExpansionCore.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansionCore e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold tryStringLitExpansionCore; iterate 3 split <;> [skip; exact .pure nofun]
  let .lit _ he₁ := he₁
  exact .toLBoolM <| isDefEqCore.WF he₁ he₂

theorem tryStringLitExpansion.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansion e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  refine (tryStringLitExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure h]
  exact (tryStringLitExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem isDefEqUnitLike.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun ty _ _ ⟨ty', _, _, hty, hty'⟩ => ?_
  refine (whnf.WF hty).bind fun tType _ _ ⟨_, tT', htT, hdefeq⟩ => ?_
  split <;> [rename_i I ls hI; exact .pure nofun]
  refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hci => ?_
  split <;> [rename_i I_val hval; exact .pure nofun]
  refine (M.WF.liftExcept envGet.WF).lift.bind fun cci _ _ hcci => ?_
  split <;> [rename_i cval hcval; exact .pure nofun]
  refine (inferType.WF he₂).bind fun sty _ _ ⟨sty', _, _, hsty, hsty'⟩ => ?_
  refine (isDefEqCore.WF htT hsty).mono fun b _ _ h hb => ?_
  have hb := h (by simpa using hb)
  -- the whnf of the type of `e₁` is an application of `I`
  have htT' : c.TrExprS ((Expr.const I ls).mkAppList tType.getAppArgsList) tT' := by
    rw [← hI, tType.mkAppList_getAppArgsList]; exact htT
  have ⟨fn', stk⟩ := AppStack.build htT'
  have ⟨args', hargs, htT''⟩ := stk.translatedArguments
  have .const hfc hls hlen := stk.tr
  have heq := htT'.uniq c.Ewf (.refl c.Ewf c.Δwf) htT''
  obtain ⟨info, hinfo, -, decl, doms, result, -, -, -, -, -, -, -, -, -, -, hnf, hnp, hni, -, ⟨_, hfam⟩, -, -⟩ :=
    VContext.registryShape hci hfc rfl hcci (by
      -- the listed constant is a constructor of the structure
      obtain ⟨info, hinfoEq, hinfoInduct, -⟩ :=
        c.listedConstructors I _ hci _ (by simp) _ hcci
      rw [ConstantInfo.ctorInfo.inj hinfoEq]
      exact hinfoInduct)
  -- the type is an application of the structure at a sort, so it supplies exactly the
  -- parameters (the structure has no indices)
  have hlenP : args'.length = info.nparams := by
    have ⟨_, hsort⟩ := hty'.isType c.Ewf.orderedStrong c.Δwf.toCtx
    have hsort := (hsort.defeqU_l c.Ewf c.Δwf hdefeq.symm).defeqU_l c.Ewf c.Δwf heq
    rw [VEnv.HasType.projectionFamily_arity c.Ewf c.Δwf.toCtx hinfo hfam hsort, ← hni]; rfl
  have hfields : info.numFields = 0 := hnf
  have ht : c.HasType e₁' (VExpr.mkApps (.const I _) args') :=
    (hty'.defeqU_r c.Ewf c.Δwf hdefeq.symm).defeqU_r c.Ewf c.Δwf heq
  have hs : c.HasType e₂' (VExpr.mkApps (.const I _) args') :=
    (hsty'.defeqU_r c.Ewf c.Δwf hb.symm).defeqU_r c.Ewf c.Δwf heq
  exact ⟨_, .unitLike hinfo hlenP hni.symm hfields ht hs⟩

theorem lazyDeltaProjReduction.finish.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS (.proj structName i e₁) e₁')
    (he₂ : c.TrExprS (.proj structName i e₂) e₂') :
    (finish structName i e₁ e₂).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  unfold finish
  refine (reduceProjCore.WF he₁).bind fun _ _ _ h1 => ?_; extract_lets F
  have hF {s} : (F ⟨⟩).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
    have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
    refine (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    exact a2.proj_uniq c.Ewf (.refl c.Δwf.toCtx) (h hb)
  split <;> [have ⟨a1, _, a2, a3⟩ := h1 _ rfl; exact .pureBind hF]
  refine (reduceProjCore.WF he₂).bind fun _ _ _ h2 => ?_
  split <;> [have ⟨b1, _, b2, b3⟩ := h2 _ rfl; exact .pureBind hF]
  exact (isDefEqCore.WF a2 b2).mono fun _ _ _ h hb =>
    a3.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf b3

theorem lazyDeltaProjReduction.loop.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS (.proj structName i e₁) e₁')
    (he₂ : c.TrExprS (.proj structName i e₂) e₂') :
    (loop structName i e₁ e₂ n).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
  refine (lazyDeltaReductionStep.WF a1 b1).bind fun _ _ _ h => ?_; split
  · have ⟨_, ⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have e1 := a2.proj_defeqDFC c.Ewf (.refl c.Δwf.toCtx) c2.symm
    have e2 := b2.proj_defeqDFC c.Ewf (.refl c.Δwf.toCtx) d2.symm
    refine (ih (.proj c1 e1) (.proj d1 e2)).mono fun _ _ _ h hb => ?_
    have f1 := e1.proj_uniq c.Ewf (.refl c.Δwf.toCtx) c2
    have f2 := e2.proj_uniq c.Ewf (.refl c.Δwf.toCtx) d2
    exact f1.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf f2
  · exact .pure fun _ => a2.proj_uniq c.Ewf (.refl c.Δwf.toCtx) h
  all_goals
    have ⟨⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have e1 := a2.proj_defeqDFC c.Ewf (.refl c.Δwf.toCtx) c2.symm
    have e2 := b2.proj_defeqDFC c.Ewf (.refl c.Δwf.toCtx) d2.symm
    refine (finish.WF (.proj c1 e1) (.proj d1 e2)).mono fun _ _ _ h hb => ?_
    have f1 := e1.proj_uniq c.Ewf (.refl c.Δwf.toCtx) c2
    have f2 := e2.proj_uniq c.Ewf (.refl c.Δwf.toCtx) d2
    exact f1.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf f2

theorem isDefEqCore'.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore' e₁ e₂) fun b _ => b = true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine .readThe ?_
  suffices ∀ {s}, RecM.WF c s (F1 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [rename_i h1; exact this]
    refine (whnf.WF he₁).bind fun _ _ _ ⟨_, _, a1, a2⟩ => ?_
    split <;> [rename_i h2; exact this]
    refine .pure fun _ => ?_
    simp [Expr.isConstOf] at h1 h2
    split at h1 <;> simp at h1; cases h1.2; split at h2 <;> simp at h2; cases h2
    let .const b1 b2 b3 := he₂
    let .const c1 c2 c3 := a1
    cases c.hasPrimitives.boolTrue b1
    cases c.hasPrimitives.boolTrue c1
    simp at b3 c3; subst b3 c3; simp at b2 c2; subst b2 c2
    exact a2.symm
  intro; unfold F1
  refine (whnfCore.WF he₁).bind fun _ _ _ ⟨_, e₁', a1, a2⟩ => ?_
  refine (whnfCore.WF he₂).bind fun _ _ _ ⟨_, e₂', b1, b2⟩ => ?_
  extract_lets F2
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    a2.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf b2
  suffices ∀ {s}, RecM.WF c s (F2 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [skip; exact this]
    refine (quickIsDefEq.WF a1 b1).bind fun _ _ _ h => ?_
    split <;> [skip; exact this]
    exact .pure fun hb => h (by simpa using hb)
  intro; unfold F2
  refine (isDefEqProofIrrel.WF a1 b1).bind fun _ _ _ h => ?_
  split
  · exact .pure fun hb => h (by simpa using hb)
  refine (lazyDeltaReduction.loop.WF a1 b1).readThe.bind fun _ _ _ h => ?_; split
  · cases h.1
  · exact .pure fun _ => h
  · exact .pure nofun
  have ⟨⟨e₁', c1, c4⟩, ⟨e₂', d1, d4⟩⟩ := h
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    c4.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d4
  extract_lets F3
  suffices ∀ {s}, RecM.WF c s (F3 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split
    · split <;> [rename_i h2; exact this]
      refine .pure fun _ => ?_
      simp at h2; cases h2.1
      have .const c1 c2 c3 := c1; have .const d1 d2 d3 := d1
      cases d1.symm.trans c1
      have := VEnv.IsDefEq.constDF c1
        (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2) (.of_mapM_ofLevel d2)
        ((List.mapM_eq_some.1 c2).length_eq.symm.trans c3)
        (Level.isEquivList_wf h2.2 c2 d2)
      exact this.toU
    · split <;> [rename_i h; exact this]
      simp at h; subst h
      exact .pure fun _ => c1.uniq c.Ewf (.refl c.Ewf c.Δwf) d1
    · split <;> [rename_i h2; exact this]
      simp at h2
      rcases h2 with ⟨rfl, rfl⟩
      refine (lazyDeltaProjReduction.loop.WF c1 d1).bind fun _ _ _ h => ?_
      split <;> [refine .pure fun _ => h ‹_›; exact this]
    · exact this
  intro; unfold F3
  refine (whnfCore.WF c1).bind fun _ _ _ ⟨_, e₁'', c5, c6⟩ => ?_
  refine (whnfCore.WF d1).bind fun _ _ _ ⟨_, e₂'', d5, d6⟩ => ?_
  split
  · exact (isDefEqCore.WF c5 d5).mono fun _ _ _ h hb =>
      c6.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d6
  refine (isDefEqApp.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaStruct.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryStringLitExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine (isDefEqUnitLike.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  exact .pure nofun
