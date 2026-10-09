import Lean4Lean.Theory.Typing.Strengthening.MajorEta

/-! # Typing strengthening: descent of the prefix-unfolding guard

Direction F. B2 isolated the guard of a singleton or
quotient prefix unfolding (`UnfoldingCheck`) as the obligation `UnfoldingCheckDescends`,
quantified over an arbitrary program. As stated it is not a `TypedFront` instance (its
`source_typed` field for an arbitrary domain telescope is a typing-front instance, see the log),
but for the *generated* programs, the only ones that occur, every field descends:

* `UnfoldingCheck.descend_of_typed`: once every capture is typed below at some type and the
  instantiated left-hand side is the recursor spine applied to the reconstructed constructor,
  the check descends: the captures are retyped at their specialized domains
  (`TypedFrontN.retype`, the domains being types below by `IsType.closed_telescope_instOuter`
  over the closed telescope of the installed equation), the constructor is typed below as the
  last argument of the instantiated left-hand side (`IsDefEq.extra_instOuter`), the major
  proposition descends (`majorProp_descend`) and the spine alignment descends
  (`ConstSpineDefEq.descend`);
* `singleton_captures_typed`: the captures of the generated singleton program are typed below.
  The lifted arguments and variables directly; the data fields are index slots; a proof field is
  the extractor `PropElim.value` applied to the parameters, indices, major and cast arguments,
  and it is typed above as a capture, so the prefix spine descent `telInst_descend_prefix` at
  the closed telescope `valueType` yields the typed instance of the singleton layout below (the
  layout agreement with the recursor telescope is never computed), then the cast arguments
  `Eq.refl (Sort s) X_k` are typed below (`HasType.closed_instOuter`, `HasType.eqReflApp`) and
  the whole spine descends (`telInst_descend`), by strong induction on the field index;
* `quot_captures_typed`: the quotient captures are the five opened arguments and the
  `propInhabitant` proof, typed below from the concrete `Quot.lift` telescope (`quotient_walk`,
  `propInhabitant_app`);
* `PrefixUnfold.descend'`, `QuotPrefixUnfold.descend'`, `DeltaPar.descend'`: B2's descents with
  the obligation discharged, and the chain descents `LStep.chain_descend'`,
  `EtaNE.forallE_inv_lift'`, `EtaNE.const_spine_inv_lift'` on which `Final.lean` is built. -/

namespace Lean4Lean.VEnv.StrengtheningUnfolding
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaClosure VEnv.StrengtheningSpineExposure
  VEnv.StrengtheningMajorEta InductiveSignature InductiveSignature.RecursorData

open private closed_wrapForalls_domain from Lean4Lean.Theory.Typing.CaseReduction

variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr}

/-- Prefix form of `telInst_descend`: only the first arguments need to be typed below. -/
theorem telInst_descend_prefix (henv : env.WF) (hTF : TypedFrontN env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    {h : VExpr} {ds₁ ds₂ : List VExpr} {r : VExpr}
    (hh : env.HasType U Γ h (wrapForalls (ds₁ ++ ds₂) r))
    (hcl : (wrapForalls (ds₁ ++ ds₂) r).ClosedN 0)
    {as₁ as₂ : List VExpr} (hlen : as₁.length = ds₁.length) (hlen₂ : as₂.length = ds₂.length)
    (hwf : ∀ a ∈ as₁, VExpr.WF env U Γ a)
    (habove : VExpr.WF env U Γ' (mkApps (h.liftN 1 k) ((as₁ ++ as₂).map (·.liftN 1 k)))) :
    TelInst env U Γ ds₁ as₁ := by
  have hctx := (IsType.wrapForalls_inv henv hΓ (hh.isType henv.ordered hΓ)).1
  have hctx₁ : OnCtx (ds₁.reverse ++ Γ) (env.IsType U) := by
    rw [List.reverse_append, List.append_assoc] at hctx
    exact OnCtx.of_append hctx
  have hh' : env.HasType U Γ' (h.liftN 1 k) (wrapForalls (ds₁ ++ ds₂) r) := by
    have := hh.weakN henv.ordered W
    rwa [hcl.liftN_eq (Nat.zero_le _)] at this
  have habove' := (HasType.mkApps_wrapForalls henv hΓ' hh' habove (by simp [hlen, hlen₂])).1
  refine ⟨hlen, fun j hj hj' => ?_⟩
  induction j using Nat.strongRecOn with
  | _ j ih =>
  have hD : env.IsType U Γ (ds₁[j].instOuter (as₁.take j)) := by
    refine IsType.instOuter_telescope henv (doms := ds₁.take j)
      (OnCtx.getElem_reverse_append hctx₁ j hj').2 (by simp [List.length_take]; omega) ?_
    intro i hi hi'
    simp only [List.length_take] at hi hi'
    have hi₁ : i < j := by omega
    rw [List.getElem_take, List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hi₁)]
    exact ih i hi₁ (by omega) (by omega)
  have hj₂ : j < ((as₁ ++ as₂).map (·.liftN 1 k)).length := by simp; omega
  have hj₃ : j < (ds₁ ++ ds₂).length := by simp; omega
  have hab := habove' j hj₂ hj₃
  have hdcl : ds₁[j].ClosedN (as₁.take j).length := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have := closed_wrapForalls_domain hcl hj₃
    rwa [List.getElem_append_left hj', Nat.zero_add] at this
  rw [List.getElem_map, List.getElem_append_left (by omega), List.getElem_append_left hj',
    ← List.map_take, List.take_append_of_le_length (Nat.le_of_lt hj),
    ← instantiateParams_eq_instOuter, ← instantiateParams_liftN hdcl,
    instantiateParams_eq_instOuter] at hab
  obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hj)
  obtain ⟨u, hDu⟩ := hD
  exact hTF.retype henv W hΓ hΓ' hA hDu hab

theorem lift'_consN_skipN_add (e : VExpr) (k n : Nat) :
    e.lift' (((Lift.refl.skipN 1).consN k).consN n) = e.liftN 1 (k + n) := by
  rw [Lift.consN_consN, lift'_consN_skipN]

/-- The lift of the opened source applied to the constructor. -/
theorem etaOpen_app_lift' (n : Nat) (s c : VExpr) (ρ : Lift) :
    (VExpr.app (etaOpen n s).lift c).lift' (ρ.consN (n + 1)) =
      .app (etaOpen n (s.lift' ρ)).lift (c.lift' (ρ.consN (n + 1))) := by
  simp only [VExpr.lift', Lift.consN]
  rw [etaOpen_lift', lift_lift'_cons]

/-- The eta opening of a constant spine applied to a term is a constant spine. -/
theorem etaOpen_app_const_spine (m : Nat) (c : Name) (ls : List VLevel) (as : List VExpr)
    (e : VExpr) :
    ∃ asL, VExpr.app (etaOpen m (mkApps (.const c ls) as)).lift e = mkApps (.const c ls) asL := by
  suffices h : ∀ m, ∃ as', etaOpen m (mkApps (.const c ls) as) = mkApps (.const c ls) as' by
    obtain ⟨as', h'⟩ := h m
    refine ⟨as'.map (·.lift) ++ [e], ?_⟩
    rw [h', mkApps_snoc]
    simp only [VExpr.lift, liftN_mkApps, liftN]
  intro m
  induction m with
  | zero => exact ⟨as, rfl⟩
  | succ m ih =>
    obtain ⟨as', h'⟩ := ih
    refine ⟨as'.map (·.lift) ++ [.bvar 0], ?_⟩
    rw [etaOpen_succ, h', mkApps_snoc]
    simp only [VExpr.lift, liftN_mkApps, liftN]


/-- A typed telescope instance restricts to prefixes. -/
theorem TelInst.take_prefix {Γ doms args : List VExpr} (H : TelInst env U Γ doms args) (n : Nat) :
    TelInst env U Γ (doms.take n) (args.take n) := by
  by_cases hn : n ≤ doms.length
  · have h := TelInst.take (doms := doms.take n) (more := doms.drop n)
      (by rwa [List.take_append_drop])
    rwa [List.length_take, Nat.min_eq_left hn] at h
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by rw [H.1]; omega)]
    exact H

theorem instOuter_app (f a : VExpr) (args : List VExpr) :
    (VExpr.app f a).instOuter args = .app (f.instOuter args) (a.instOuter args) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst]; rfl

/-- The lifted data of a renamed program: the extended lift, the two opened contexts and the
captures. -/
theorem rename_lift_facts (henv : env.WF) (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    (hΓ' : OnCtx Γ' (env.IsType U)) {source : VExpr} {program : PrefixUnfolding}
    (hsrc : env.HasType U Γ source program.type)
    (H : UnfoldingCheck env U Γ' (source.liftN 1 k) (program.rename ((Lift.refl.skipN 1).consN k))) :
    Ctx.LiftN 1 (k + program.domains.length) (program.domains.reverse ++ Γ)
      ((renameDomains ((Lift.refl.skipN 1).consN k) program.domains).reverse ++ Γ') ∧
    OnCtx (program.domains.reverse ++ Γ) (env.IsType U) ∧
    OnCtx ((renameDomains ((Lift.refl.skipN 1).consN k) program.domains).reverse ++ Γ')
      (env.IsType U) ∧
    (program.rename ((Lift.refl.skipN 1).consN k)).captures =
      program.captures.map (·.liftN 1 (k + program.domains.length)) := by
  refine ⟨?_, (IsType.wrapForalls_inv henv hΓ (hsrc.isType henv.ordered hΓ)).1, ?_, ?_⟩
  · have h := renameDomains_context program.domains (Ctx.liftN_iff_lift'.mp W)
    rw [Ctx.liftN_iff_lift', ← Lift.consN_consN]
    exact h
  · have h : env.HasType U Γ' (source.liftN 1 k)
        (wrapForalls (renameDomains ((Lift.refl.skipN 1).consN k) program.domains)
          (program.result.lift' (((Lift.refl.skipN 1).consN k).consN program.domains.length))) :=
      H.source_typed
    exact (IsType.wrapForalls_inv henv hΓ' (h.isType henv.ordered hΓ')).1
  · simp only [PrefixUnfolding.rename, lift'_consN_skipN_add]

/-- The unfolding check descends once every capture and the reconstructed constructor are typed
below at some type: the captures are retyped at their specialized domains by strong induction on
the position (`TypedFrontN.retype`, the domain a type below by `IsType.closed_telescope_instOuter`
over the closed telescope of the installed equation), the major proposition descends by
`majorProp_descend`, and the spine alignment by `ConstSpineDefEq.descend`. -/
theorem UnfoldingCheck.descend_of_typed (henv : env.WF) (hTF : TypedFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    {name : Name} {levels : List VLevel} {args : List VExpr} {program : PrefixUnfolding}
    (hsrc : env.HasType U Γ (mkApps (.const name levels) args) program.type)
    (H : UnfoldingCheck env U Γ' ((mkApps (.const name levels) args).liftN 1 k)
      (program.rename ((Lift.refl.skipN 1).consN k)))
    (hcap : ∀ j (hj : j < program.captures.length),
      ∃ A, env.HasType U (program.domains.reverse ++ Γ) program.captures[j] A)
    (hlhsApp : ∃ X, (program.equationBody.lhs.instL program.levels).instOuter program.captures =
      .app X program.constructor)
    (hlhs : ∃ c ls as, program.equationBody.lhs = mkApps (.const c ls) as) :
    UnfoldingCheck env U Γ (mkApps (.const name levels) args) program := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Lift, (Lift.refl.skipN 1).consN k = ρ := ⟨_, rfl⟩
  rw [hρ] at H
  have hne : program.domains ≠ [] := by
    intro h
    apply H.remaining_nonempty
    simp [PrefixUnfolding.rename, h, renameDomains]
  obtain ⟨m, hn⟩ : ∃ m, program.domains.length = m + 1 :=
    ⟨program.domains.length - 1, by have := List.length_pos_iff.mpr hne; omega⟩
  have hWext' := renameDomains_context program.domains (Ctx.liftN_iff_lift'.mp W)
  rw [hn, hρ] at hWext'
  have hWext : Ctx.LiftN 1 (k + (m + 1)) (program.domains.reverse ++ Γ)
      ((renameDomains ρ program.domains).reverse ++ Γ') := by
    rw [Ctx.liftN_iff_lift', ← Lift.consN_consN, hρ]
    exact hWext'
  have hctx : OnCtx (program.domains.reverse ++ Γ) (env.IsType U) :=
    (IsType.wrapForalls_inv henv hΓ (hsrc.isType henv.ordered hΓ)).1
  have hctx' : OnCtx ((renameDomains ρ program.domains).reverse ++ Γ') (env.IsType U) := by
    have h : env.HasType U Γ' ((mkApps (.const name levels) args).liftN 1 k)
        (wrapForalls (renameDomains ρ program.domains)
          (program.result.lift' (ρ.consN program.domains.length))) := H.source_typed
    exact (IsType.wrapForalls_inv henv hΓ' (h.isType henv.ordered hΓ')).1
  have hscope := H.templateScope henv
  have hcaps' : (program.rename ρ).captures = program.captures.map (·.liftN 1 (k + (m + 1))) := by
    simp only [PrefixUnfolding.rename, hn, ← hρ, lift'_consN_skipN_add]
  have hctor' : (program.rename ρ).constructor = program.constructor.liftN 1 (k + (m + 1)) := by
    simp only [PrefixUnfolding.rename, hn, ← hρ, lift'_consN_skipN_add]
  -- the closed telescope of the installed equation
  have hpres : env.defeqs program.equation := H.equation_present
  have hbody : CaseSchema.EquationBody.extract program.equation.lhs program.equation.rhs
      program.equation.type = some program.equationBody := H.equation_body
  have hdf := henv.ordered.defEqWF hpres
  obtain ⟨hl, hr, ht⟩ := CaseSchema.EquationBody.extract_sound hbody
  have hTeq : env.IsType program.equation.uvars []
      (wrapForalls program.equationBody.domains program.equationBody.type) := by
    rw [ht]; exact hdf.1.isType henv.ordered trivial
  have hctxE := (IsType.wrapForalls_inv henv (Γ := [])
    (show OnCtx [] (env.IsType program.equation.uvars) from trivial) hTeq).1
  -- the captures are typed at their specialized domains
  have hcapTyped : ∀ j (hj : j < program.captures.length)
      (hd : j < program.equationBody.domains.length),
      env.HasType U (program.domains.reverse ++ Γ) program.captures[j]
        ((program.equationBody.domains[j].instL program.levels).instOuter
          (program.captures.take j)) := by
    intro j
    induction j using Nat.strongRecOn with
    | _ j ih =>
    intro hj hd
    have hD : env.IsType U (program.domains.reverse ++ Γ)
        ((program.equationBody.domains[j].instL program.levels).instOuter
          (program.captures.take j)) := by
      have hA := OnCtx.getElem_reverse_append hctxE j hd
      rw [List.append_nil] at hA
      refine IsType.closed_telescope_instOuter henv hA.1 hA.2 (show ∀ l ∈ program.levels, l.WF U from
        H.levels_wf) (by simp [List.length_take]; omega) ?_
      intro i hi hi'
      simp only [List.length_take, List.length_map] at hi hi'
      have hi₁ : i < j := by omega
      rw [List.getElem_take, List.getElem_map, List.getElem_take, List.take_take,
        Nat.min_eq_left (Nat.le_of_lt hi₁)]
      exact ih i hi₁ (by omega) (by omega)
    have hj' : j < (program.rename ρ).captures.length := by
      simpa [PrefixUnfolding.rename] using hj
    have hab := H.captures_typed j hj' hd
    simp only [hcaps', List.getElem_map, ← List.map_take] at hab
    change env.HasType U ((renameDomains ρ program.domains).reverse ++ Γ')
      (program.captures[j].liftN 1 (k + (m + 1)))
      ((program.equationBody.domains[j].instL program.levels).instOuter
        ((program.captures.take j).map (·.liftN 1 (k + (m + 1))))) at hab
    have hdcl : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      exact (hscope.2.2 j hd).instL
    rw [← instantiateParams_eq_instOuter, ← instantiateParams_liftN hdcl,
      instantiateParams_eq_instOuter] at hab
    obtain ⟨A, hA⟩ := hcap j hj
    obtain ⟨u, hDu⟩ := hD
    exact hTF.retype henv hWext hctx hctx' hA hDu hab
  -- the instantiated left-hand side is typed below, hence the constructor
  have hlw : ∀ l ∈ program.levels, l.WF U := H.levels_wf
  have hll : program.levels.length = program.equation.uvars := H.levels_length
  have hcl : program.captures.length = program.equationBody.domains.length := by
    simpa [PrefixUnfolding.rename] using H.captures_length
  have hlhsT := IsDefEq.extra_instOuter henv hctx hpres hlw hll hl.symm hr.symm ht.symm hcl
    hcapTyped
  have hctor : ∃ C, env.HasType U (program.domains.reverse ++ Γ) program.constructor C := by
    obtain ⟨X, hX⟩ := hlhsApp
    have h := hlhsT.hasType.1
    rw [hX] at h
    obtain ⟨_, _, -, hc⟩ := h.app_inv henv.ordered hctx
    exact ⟨_, hc⟩
  -- the major proposition
  obtain ⟨d, rest, hrev⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hne)
  have hvar : env.HasType U (program.domains.reverse ++ Γ) (.bvar 0) d.lift := by
    rw [hrev]; exact .bvar .zero
  have hD : ∃ u, env.HasType U (program.domains.reverse ++ Γ) d.lift (.sort u) := by
    have h := hctx
    rw [hrev] at h
    obtain ⟨u, hd⟩ := h.2
    exact ⟨u, by rw [hrev]; exact hd.weak henv.ordered⟩
  obtain ⟨u, hD⟩ := hD
  have hvar' : env.HasType U ((renameDomains ρ program.domains).reverse ++ Γ') (.bvar 0)
      (d.lift.liftN 1 (k + (m + 1))) := by
    have := hvar.weakN henv.ordered hWext
    rwa [show (VExpr.bvar 0).liftN 1 (k + (m + 1)) = .bvar 0 by
      simp only [liftN, liftVar_lt (show 0 < k + (m + 1) by omega)]] at this
  obtain ⟨C, hC⟩ := hctor
  have hmajor := majorProp_descend henv hTF hWext hctx hctx' hD hC hvar (by
    have h := H.major_prop
    rwa [hctor'] at h) hvar'
  -- the spine alignment
  obtain ⟨c, ls, as, hlhsEq⟩ := hlhs
  have hright : (program.equationBody.lhs.instL program.levels).instOuter program.captures =
      mkApps (.const c (ls.map (·.inst program.levels)))
        (as.map fun a => (a.instL program.levels).instOuter program.captures) := by
    simp only [hlhsEq, instL_mkApps, VExpr.instOuter_mkApps, instL, List.map_map,
      Function.comp_def, instOuter_closed0 (e := VExpr.const c _) trivial]
  have hrightWF : ∀ a ∈ as.map fun a => (a.instL program.levels).instOuter program.captures,
      VExpr.WF env U (program.domains.reverse ++ Γ) a := by
    have := hlhsT.hasType.1
    rw [hright] at this
    exact VExpr.WF.args_of_mkApps henv.ordered hctx ⟨_, this⟩
  -- the left spine is typed below
  obtain ⟨M, hM0, hvM, hcM⟩ := hmajor
  have hopen := (hsrc.etaOpen_wf henv.ordered hΓ).2
  rw [hn, etaOpen_succ] at hopen
  obtain ⟨A₀, B₀, hf, hb⟩ := hopen.app_inv henv.ordered hctx
  have hcA : env.HasType U (program.domains.reverse ++ Γ) program.constructor A₀ :=
    hcM.defeqU_r henv hctx (hvM.uniqU henv hctx hb)
  have hleftT := hf.app hcA
  obtain ⟨asL, hasL⟩ := etaOpen_app_const_spine m name levels args program.constructor
  have hleftWF : ∀ a ∈ asL, VExpr.WF env U (program.domains.reverse ++ Γ) a := by
    have := hleftT
    rw [hasL] at this
    exact VExpr.WF.args_of_mkApps henv.ordered hctx ⟨_, this⟩
  -- the alignment above, as lifts of the two spines below
  have hlift := H.recursor_lhs
  have hleftLift : VExpr.app (etaOpen ((program.rename ρ).domains.length - 1)
      ((mkApps (.const name levels) args).liftN 1 k)).lift (program.rename ρ).constructor =
      (mkApps (.const name levels) asL).liftN 1 (k + (m + 1)) := by
    rw [← hasL, hctor', ← lift'_consN_skipN_add, ← lift'_consN_skipN_add,
      show (program.rename ρ).domains.length - 1 = m by
        simp [PrefixUnfolding.rename, renameDomains_length, hn],
      ← lift'_consN_skipN (k := k), hρ, etaOpen_app_lift']
  have hscopeL : program.equationBody.lhs.ClosedN program.captures.length := by
    simpa [PrefixUnfolding.rename] using hscope.1
  have hrightLift : ((program.rename ρ).equationBody.lhs.instL (program.rename ρ).levels).instOuter
      (program.rename ρ).captures =
      (mkApps (.const c (ls.map (·.inst program.levels)))
        (as.map fun a => (a.instL program.levels).instOuter program.captures)).liftN 1 (k + (m + 1)) := by
    rw [← hright, hcaps']
    show (program.equationBody.lhs.instL program.levels).instOuter _ = _
    rw [← instantiateParams_eq_instOuter, ← instantiateParams_liftN hscopeL.instL,
      instantiateParams_eq_instOuter]
  rw [hleftLift, hrightLift, liftN_mkApps, liftN_mkApps] at hlift
  have hnc : name = c := by
    obtain ⟨nm, _, _, _, _, h1, h2, -⟩ := hlift
    exact ((VExpr.mkApps_const_inj h1).1.trans (VExpr.mkApps_const_inj h2).1.symm)
  subst hnc
  have hlift' : ConstSpineDefEq env U ((renameDomains ρ program.domains).reverse ++ Γ')
      (mkApps (.const name levels) (asL.map (·.liftN 1 (k + (m + 1)))))
      (mkApps (.const name (ls.map (·.inst program.levels)))
        ((as.map fun a => (a.instL program.levels).instOuter program.captures).map
          (·.liftN 1 (k + (m + 1))))) := hlift
  have halign := ConstSpineDefEq.descend henv hTF hWext hctx hctx' hleftWF hrightWF hlift'
  rw [← hasL, ← hright] at halign
  rw [show m = program.domains.length - 1 by omega] at halign
  exact {
    source_typed := hsrc
    remaining_nonempty := hne
    equation_present := hpres
    equation_body := hbody
    levels_wf := hlw
    levels_length := hll
    captures_length := hcl
    captures_typed := hcapTyped
    major_prop := ⟨M, hM0, hvM, hcM⟩
    recursor_lhs := halign }

/-! ## The reconstructed fields of the singleton unfolding -/

section Occ
variable {S : SingletonLayout} {P : List VExpr} {E : PropElim} {ps idx : List VExpr} {m : VExpr}

theorem occ_fst_getD_prefix (l : Nat) : ∀ n, l < n →
    (PropElim.occ S P E ps idx m n).1.getD l default =
      (PropElim.occ S P E ps idx m (l + 1)).1.getD l default := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hl : l = n
    · subst hl; rfl
    · rw [← ih (by omega)]
      have hlen := (PropElim.occ_length S P E ps idx m n).1
      simp only [PropElim.occ]
      split <;> rw [getD_append_left' (by omega)]

theorem occ_fst_getD_data {l k : Nat} (hs : S.slot.getD l none = some k) {n : Nat} (hl : l < n) :
    (PropElim.occ S P E ps idx m n).1.getD l default =
      VExpr.eqReflApp (.succ (S.sorts.getD l .zero)) (.sort (S.sorts.getD l .zero))
        ((S.indices.getD k default).instOuter (ps ++ idx.take k)) := by
  rw [occ_fst_getD_prefix l n hl]
  have hlen := (PropElim.occ_length S P E ps idx m l).1
  simp only [PropElim.occ, hs]
  rw [getD_append_right' (by omega), hlen, Nat.sub_self]
  rfl

theorem occ_getD_proof {l : Nat} (hs : S.slot.getD l none = none) {n : Nat} (hl : l < n) :
    (PropElim.occ S P E ps idx m n).2.getD l default =
      mkApps (PropElim.value S P E l) (ps ++ idx ++ [m] ++ (PropElim.occ S P E ps idx m l).1) := by
  rw [PropElim.occ_getD_prefix ps idx m n hl]
  have hlen := (PropElim.occ_length S P E ps idx m l).2
  simp only [PropElim.occ, hs]
  rw [getD_append_right' (by omega), hlen, Nat.sub_self]
  rfl

theorem occ_fst_getD_proof {l : Nat} (hs : S.slot.getD l none = none) {n : Nat} (hl : l < n) :
    (PropElim.occ S P E ps idx m n).1.getD l default =
      mkApps (PropElim.value S P E l) (ps ++ idx ++ [m] ++ (PropElim.occ S P E ps idx m l).1) := by
  rw [occ_fst_getD_prefix l n hl]
  have hlen := (PropElim.occ_length S P E ps idx m l).1
  simp only [PropElim.occ, hs]
  rw [getD_append_right' (by omega), hlen, Nat.sub_self]
  rfl

end Occ

theorem singletonCtor_owner {data : RecursorData} {i : Fin data.schema.signature.constructors.size}
    (h : data.singletonCtor = some i) :
    data.schema.signature.constructors[i].owner = data.owner := by
  unfold RecursorData.singletonCtor at h
  split at h
  · rename_i hj
    cases h
    have hmem : i ∈ (List.finRange data.schema.signature.constructors.size).filter
        (fun i => data.schema.signature.constructors[i].owner == data.owner) := by
      rw [hj]; simp
    simpa using (List.mem_filter.mp hmem).2
  · cases h

theorem singletonLayout_ctor {env : VEnv} {data : RecursorData} {levels : List VLevel}
    {S : SingletonLayout} (hS : data.singletonLayout env levels = some S) :
    ∃ i : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[i].owner = data.owner := by
  unfold RecursorData.singletonLayout RecursorData.singletonLayoutGeneric at hS
  simp only [Option.map_eq_some_iff, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hS
  obtain ⟨_, ⟨i, hi, -⟩, -⟩ := hS
  exact ⟨i, singletonCtor_owner hi⟩

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A

/-- The captures of the generated singleton unfolding are typed below (at some types), and the
instantiated left-hand side is the recursor spine applied to the reconstructed constructor. -/
theorem singleton_captures_typed (heq : Params.env.HasCanonicalEq) (hTF : TypedFrontN Params.env)
    {k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {data : RecursorData} {levels : List VLevel} {args : List VExpr} {T : VExpr}
    {program : PrefixUnfolding}
    (hreg : RecursorRegistered Params.env data) (hlarge : data.largeTarget = true)
    (hz : data.sourceLevel levels ≈ .zero) (hw : ∀ l ∈ levels, l.WF univs)
    (hg : data.singletonUnfolding Params.env univs levels args = some program)
    (he : Γ ⊢ mkApps (.const data.name levels) args : T)
    (H : UnfoldingCheck Params.env univs Γ' ((mkApps (.const data.name levels) args).liftN 1 k)
      (program.rename ((Lift.refl.skipN 1).consN k))) :
    (∀ j (hj : j < program.captures.length),
      ∃ A, program.domains.reverse ++ Γ ⊢ program.captures[j] : A) ∧
    (∃ X, (program.equationBody.lhs.instL program.levels).instOuter program.captures =
      .app X program.constructor) := by
  -- the source and the opened context below
  have hsrc := hreg.prefixType henv hΓ hw hg ⟨_, he⟩
  have hctx : OnCtx (program.domains.reverse ++ Γ) (Params.env.IsType univs) :=
    (IsType.wrapForalls_inv henv hΓ (hsrc.isType henv hΓ)).1
  obtain ⟨hargsLe, hne, hlv, hlvlen, hgen, hbody, hcl⟩ := singletonUnfolding_spec hg
  have hlen : levels.length = data.uvars := by
    rw [← hlv, hlvlen]; exact singletonEquation_uvars hgen
  -- the layout, its well-formedness and lengths
  obtain ⟨S, E, hS, hE, hlenD, hctor, hcapture⟩ := singletonUnfolding_layout hg
  obtain ⟨i, hown⟩ := singletonLayout_ctor hS
  obtain ⟨S', E', hS', hE', W_E⟩ := propElim_wf henv hreg hlarge hz hw hlen ⟨i, hown⟩
  cases hS.symm.trans hS'
  cases hE.symm.trans hE'
  have T := W_E.typed
  obtain ⟨hidxl, hpl⟩ := singletonLayout_lengths hS
  -- names
  generalize hPdef : data.propParams levels = P at W_E T hpl hctor hcapture
  generalize hall : data.openedArguments args = all at hctor hcapture
  have hallLen : all.length = data.majorOffset + 1 := by
    rw [← hall]; simp [RecursorData.openedArguments]; omega
  have hnpos : 0 < program.domains.length := by rw [hlenD]; omega
  -- the opened arguments are typed below
  have hW0 : Ctx.LiftN program.domains.length 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simp)
  have hallWF : ∀ a ∈ all, VExpr.WF Params.env univs (program.domains.reverse ++ Γ) a := by
    intro a ha
    rw [← hall] at ha
    simp only [RecursorData.openedArguments, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨b, hb, rfl⟩ | ha
    · obtain ⟨_, hb⟩ := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, he⟩ b hb
      rw [← hlenD]
      exact ⟨_, hb.weakN henv hW0⟩
    · simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      have hj' : 0 + j < (program.domains.reverse ++ Γ).length := by
        simp only [List.length_append, List.length_reverse]; omega
      exact ⟨_, .bvar (Lookup.ofLt hj').2⟩
  -- the lifted data
  obtain ⟨hWext, -, hctx', hcaps'⟩ := rename_lift_facts henv W hΓ hΓ' hsrc H
  -- the shapes of the parameters, indices and fields
  have hio : data.indexOffset ≤ data.majorOffset := Nat.le_add_right _ _
  have hnp : data.numParams ≤ data.indexOffset :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  generalize hps : all.take data.numParams = ps at hctor hcapture
  generalize hidx : (all.drop data.indexOffset).take data.numIndices = idx
  have hpsLen : ps.length = P.length := by
    rw [← hps, List.length_take, hpl, Nat.min_eq_left]; omega
  have hidxLen : idx.length = S.indices.length := by
    rw [← hidx, List.length_take, List.length_drop, hidxl, hallLen, Nat.min_eq_left]
    simp only [RecursorData.majorOffset]; omega
  have hpsWF : ∀ a ∈ ps, VExpr.WF Params.env univs (program.domains.reverse ++ Γ) a := by
    intro a ha; rw [← hps] at ha; exact hallWF a (List.mem_of_mem_take ha)
  have hidxWF : ∀ a ∈ idx, VExpr.WF Params.env univs (program.domains.reverse ++ Γ) a := by
    intro a ha; rw [← hidx] at ha; exact hallWF a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  have hm0 : VExpr.WF Params.env univs (program.domains.reverse ++ Γ) (.bvar 0) := by
    have h0 : 0 < (program.domains.reverse ++ Γ).length := by simp; omega
    exact ⟨_, .bvar (Lookup.ofLt h0).2⟩
  have hfieldsEq : data.singletonFields S E levels args =
      (PropElim.occ S P E ps idx (.bvar 0) S.fields.length).2 := by
    simp only [RecursorData.singletonFields, hall, hPdef, hps, hidx]
  rw [hfieldsEq] at hctor hcapture
  have hcapLen : program.captures.length = data.indexOffset + S.fields.length := by
    rw [hcapture, List.length_append, List.length_take, (PropElim.occ_length ..).2,
      Nat.min_eq_left (by omega)]
  have htakeLen : (all.take data.indexOffset).length = data.indexOffset := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  -- the fields above are captures
  have hfieldA : ∀ l, l < S.fields.length → ∃ A, (renameDomains ((Lift.refl.skipN 1).consN k)
      program.domains).reverse ++ Γ' ⊢
        ((PropElim.occ S P E ps idx (.bvar 0) S.fields.length).2.getD l default).liftN 1
          (k + program.domains.length) : A := by
    intro l hl
    have hj : data.indexOffset + l < (program.rename ((Lift.refl.skipN 1).consN k)).captures.length := by
      rw [hcaps', List.length_map, hcapLen]; omega
    have hd : data.indexOffset + l < program.equationBody.domains.length := by rw [← hcl, hcapLen]; omega
    have h := H.captures_typed _ hj hd
    simp only [hcaps', List.getElem_map] at h
    have hj' : data.indexOffset + l < program.captures.length := by rw [hcapLen]; omega
    have heqcap : program.captures[data.indexOffset + l] =
        (PropElim.occ S P E ps idx (.bvar 0) S.fields.length).2.getD l default := by
      rw [← getD_of_lt hj', hcapture, getD_append_right' (by omega), htakeLen,
        Nat.add_sub_cancel_left]
    rw [heqcap] at h
    exact ⟨_, h⟩
  -- the fields are typed below, by strong induction on the field index
  have hfieldB : ∀ l, l < S.fields.length →
      ∃ A, program.domains.reverse ++ Γ ⊢
        (PropElim.occ S P E ps idx (.bvar 0) S.fields.length).2.getD l default : A := by
    intro l
    induction l using Nat.strongRecOn with
    | _ l ih =>
    intro hl
    cases hslot : S.slot.getD l none with
    | some kk =>
      rw [PropElim.occ_getD_data ps idx (.bvar 0) hslot hl]
      by_cases hk : kk < idx.length
      · rw [getD_of_lt hk]; exact hidxWF _ (List.getElem_mem hk)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hk), Option.getD_none]
        exact ⟨_, (HasType.sort trivial : program.domains.reverse ++ Γ ⊢ VExpr.sort .zero : _)⟩
    | none =>
      rw [occ_getD_proof hslot hl]
      have hval := PropElim.value_typed P henv heq W_E hl hslot
      have hvalΔ : program.domains.reverse ++ Γ ⊢ PropElim.value S P E l :
          wrapForalls ((P ++ S.indices ++ [PropElim.majorTy S P E]) ++
            (S.tel (PropElim.genericPa S P) (PropElim.genericIa S) l).1)
            (S.target (PropElim.genericPa S P) (PropElim.genericIa S) l) := by
        have := hval.weak0 (Γ := program.domains.reverse ++ Γ) henv.ordered
        rwa [PropElim.valueType, ← wrapForalls_append] at this
      have hclT : (wrapForalls ((P ++ S.indices ++ [PropElim.majorTy S P E]) ++
            (S.tel (PropElim.genericPa S P) (PropElim.genericIa S) l).1)
            (S.target (PropElim.genericPa S P) (PropElim.genericIa S) l)).ClosedN 0 := by
        obtain ⟨_, h⟩ := hval.isType henv.ordered (show OnCtx [] (Params.env.IsType univs) from trivial)
        have := VExpr.WF.closedN henv.ordered ⟨_, h⟩ trivial
        rwa [PropElim.valueType, ← wrapForalls_append] at this
      obtain ⟨A, hA⟩ := hfieldA l hl
      rw [occ_getD_proof hslot hl, liftN_mkApps] at hA
      have hlen₁ : (ps ++ idx ++ [VExpr.bvar 0]).length =
          (P ++ S.indices ++ [PropElim.majorTy S P E]).length := by simp [hpsLen, hidxLen]
      have hlen₂ : (PropElim.occ S P E ps idx (.bvar 0) l).1.length =
          (S.tel (PropElim.genericPa S P) (PropElim.genericIa S) l).1.length := by
        rw [(PropElim.occ_length ..).1, (SingletonLayout.tel_length ..).1]
      have hwf₁ : ∀ a ∈ ps ++ idx ++ [VExpr.bvar 0],
          VExpr.WF Params.env univs (program.domains.reverse ++ Γ) a := by
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with (ha | ha) | rfl
        · exact hpsWF a ha
        · exact hidxWF a ha
        · exact hm0
      -- (F1) the parameters, indices and major are a typed instance of the layout below
      have hF1 := telInst_descend_prefix henv hTF hWext hctx hctx' hvalΔ hclT hlen₁ hlen₂ hwf₁ ⟨_, hA⟩
      -- the cast arguments are typed below
      have hhats : ∀ l', l' < l → ∃ A, program.domains.reverse ++ Γ ⊢
          (PropElim.occ S P E ps idx (.bvar 0) l).1.getD l' default : A := by
        intro l' hl'
        cases hslot' : S.slot.getD l' none with
        | some kk =>
          rw [occ_fst_getD_data hslot' hl']
          have hkk : kk < S.indices.length := T.scope.slot_lt l' kk hslot'
          have hsw : (S.sorts.getD l' .zero).WF univs := T.sortWF l'
          have htel : TelInst Params.env univs (program.domains.reverse ++ Γ)
              (P ++ S.indices.take kk) (ps ++ idx.take kk) := by
            have h := TelInst.take_prefix hF1 (P.length + kk)
            have hdoms : (P ++ S.indices ++ [PropElim.majorTy S P E]).take (P.length + kk) =
                P ++ S.indices.take kk := by
              rw [List.append_assoc, List.take_add, List.take_left' rfl, List.drop_left' rfl,
                List.take_append_of_le_length (Nat.le_of_lt hkk)]
            have hargs : (ps ++ idx ++ [VExpr.bvar 0]).take (P.length + kk) = ps ++ idx.take kk := by
              rw [List.append_assoc, List.take_add, List.take_left' hpsLen, List.drop_left' hpsLen,
                List.take_append_of_le_length (by omega)]
            rwa [hdoms, hargs] at h
          have hX := HasType.closed_instOuter henv (T.indicesCtx kk (Nat.le_of_lt hkk))
            (T.slotSort l' kk hslot' hkk) htel
          rw [VExpr.instOuter_sort] at hX
          rw [getD_of_lt hkk]
          exact ⟨_, HasType.eqReflApp heq hsw (HasType.sort hsw) hX⟩
        | none =>
          rw [occ_fst_getD_proof hslot' hl', ← occ_getD_proof hslot' (Nat.lt_trans hl' hl)]
          exact ih l' hl' (Nat.lt_trans hl' hl)
      have hwfAll : ∀ a ∈ ps ++ idx ++ [VExpr.bvar 0] ++ (PropElim.occ S P E ps idx (.bvar 0) l).1,
          VExpr.WF Params.env univs (program.domains.reverse ++ Γ) a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hwf₁ a ha
        · obtain ⟨l', hl', rfl⟩ := List.mem_iff_getElem.mp ha
          rw [← getD_of_lt hl']
          exact hhats l' (by rwa [(PropElim.occ_length ..).1] at hl')
      have htelAll := telInst_descend henv hTF hWext hctx hctx' hvalΔ hclT
        (by simp [hpsLen, hidxLen, hlen₂]) hwfAll ⟨_, hA⟩
      exact ⟨_, HasType.mkApps_of_tel hvalΔ htelAll⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [← getD_of_lt (d := default) hj, hcapture]
    by_cases hjt : j < (all.take data.indexOffset).length
    · rw [getD_append_left' hjt, getD_of_lt hjt]
      exact hallWF _ (List.mem_of_mem_take (List.getElem_mem hjt))
    · rw [getD_append_right' (Nat.le_of_not_lt hjt)]
      apply hfieldB
      have hjl := hj
      rw [hcapLen] at hjl
      have hjt' := hjt
      rw [htakeLen] at hjt'
      rw [htakeLen]
      omega
  · -- the instantiated left-hand side
    obtain ⟨D, lb, rb, tb, X, hgen', hseq, hext, -, -, hlb, hioff, -⟩ :=
      singleton_equation_syntax hreg hlarge hz hlen hown hS hE
    rw [hPdef] at hlb hioff
    have heqn : program.equation = ⟨data.uvars, wrapLams D lb, wrapLams D rb, wrapForalls D tb⟩ := by
      have h := hgen; rw [hseq, hgen'] at h; exact (Option.some.inj h).symm
    have hbodyEq : program.equationBody = ⟨D, lb, rb, tb⟩ := by
      have h := hbody; rw [heqn] at h; simp only at h; rw [hext] at h
      exact (Option.some.inj h).symm
    rw [hbodyEq, hlv]
    simp only [hlb]
    have hctorEq : (mkApps E.ctor (vars P.length (2 + S.fields.length) ++
        vars S.fields.length 0)).instOuter program.captures = program.constructor := by
      rw [VExpr.instOuter_mkApps, instOuter_closed0 W_E.ctor_closed, List.map_append,
        map_instOuter_vars _ _ _ (by rw [hcapLen, hioff]; omega),
        map_instOuter_vars _ _ _ (by rw [hcapLen]; omega), hcapLen, hioff, hctor, hcapture]
      congr 2
      · rw [show P.length + 2 + S.fields.length - (P.length + (2 + S.fields.length)) = 0 by omega,
          List.drop_zero, List.take_append_of_le_length (by rw [htakeLen, hioff]; omega),
          List.take_take, ← hps, hpl, Nat.min_eq_left (by rw [hioff]; omega)]
      · rw [show P.length + 2 + S.fields.length - (S.fields.length + 0) = data.indexOffset by omega,
          List.drop_left' htakeLen, List.take_of_length_le (Nat.le_of_eq (PropElim.occ_length ..).2)]
    exact ⟨_, by rw [instOuter_app, hctorEq]⟩

end


/-! ## The quotient unfolding -/

theorem etaOpen_mkApps_const (c : Name) (ls : List VLevel) (as : List VExpr) :
    ∀ n, etaOpen n (mkApps (.const c ls) as) = mkApps (.const c ls) (as.map (·.liftN n) ++ vars n 0)
  | 0 => by simp [etaOpen, vars]
  | n + 1 => by
    rw [etaOpen_succ, etaOpen_mkApps_const c ls as n]
    have h1 : (mkApps (.const c ls) (as.map (·.liftN n) ++ vars n 0)).lift =
        mkApps (.const c ls) ((as.map (·.liftN n) ++ vars n 0).map VExpr.lift) := by
      show liftN 1 _ 0 = _
      rw [liftN_mkApps]; rfl
    rw [h1, ← VExpr.mkApps_snoc, List.map_append, List.map_map, vars_map_lift, List.append_assoc,
      vars_add n 1 0]
    congr 2
    exact List.map_congr_left fun a _ => (liftN_succ a n).symm

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A

/-- The captures of the generated quotient unfolding are typed below, and the instantiated
left-hand side is the quotient-lift spine applied to the reconstructed constructor. -/
theorem quot_captures_typed {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    {levels : List VLevel} {args : List VExpr} {T : VExpr} {program : PrefixUnfolding}
    (hq : QuotRegistered Params.env) (hw : ∀ l ∈ levels, l.WF univs)
    (hz : levels[0]?.getD .zero ≈ .zero)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (he : Γ ⊢ mkApps (.const ``Quot.lift levels) args : T) :
    (∀ j (hj : j < program.captures.length),
      ∃ A, program.domains.reverse ++ Γ ⊢ program.captures[j] : A) ∧
    (∃ X, (program.equationBody.lhs.instL program.levels).instOuter program.captures =
      .app X program.constructor) := by
  have hsrc := hq.prefixType henv hΓ hw hg ⟨_, he⟩
  have hctx : OnCtx (program.domains.reverse ++ Γ) (Params.env.IsType univs) :=
    (IsType.wrapForalls_inv henv hΓ (hsrc.isType henv hΓ)).1
  obtain ⟨hlen2, hargs5, hne, hlv, heqn, hbody, hcl⟩ := QuotPrefixUnfolding.generate_spec hg
  obtain ⟨hlenD, hctor, hcapture⟩ := QuotPrefixUnfolding.generate_layout hg
  obtain ⟨u, v, rfl⟩ : ∃ u v, levels = [u, v] := by
    match levels, hlen2 with
    | [u, v], _ => exact ⟨_, _, rfl⟩
  have hu : u.WF univs := hw u (by simp)
  have hv : v.WF univs := hw v (by simp)
  -- the opened arguments
  generalize hall : QuotPrefixUnfolding.openedArguments args = all at hctor hcapture
  have hallLen : all.length = 6 := by
    rw [← hall]; simp [QuotPrefixUnfolding.openedArguments]; omega
  have hW0 : Ctx.LiftN program.domains.length 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simp)
  have hallWF : ∀ a ∈ all, VExpr.WF Params.env univs (program.domains.reverse ++ Γ) a := by
    intro a ha
    rw [← hall] at ha
    simp only [QuotPrefixUnfolding.openedArguments, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨b, hb, rfl⟩ | ha
    · obtain ⟨_, hb⟩ := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, he⟩ b hb
      rw [← hlenD]
      exact ⟨_, hb.weakN henv hW0⟩
    · simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      have hj' : 0 + j < (program.domains.reverse ++ Γ).length := by
        simp only [List.length_append, List.length_reverse]; omega
      exact ⟨_, .bvar (Lookup.ofLt hj').2⟩
  -- the six-argument spine is typed in the opened context
  have hspine : VExpr.WF Params.env univs (program.domains.reverse ++ Γ)
      (mkApps (.const ``Quot.lift [u, v]) all) := by
    have h := (hsrc.etaOpen_wf henv hΓ).2
    rw [etaOpen_mkApps_const] at h
    have hall' : args.map (·.liftN program.domains.length) ++ vars program.domains.length 0 = all := by
      rw [← hall, hlenD]; rfl
    rw [hall'] at h
    exact ⟨_, h⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5, all = [a0, a1, a2, a3, a4, a5] := by
    match all, hallLen with
    | [a0, a1, a2, a3, a4, a5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  obtain ⟨result, hwalk⟩ := quotient_walk henv hctx hq hu hv hspine
  cases hwalk with | cons ha hwalk =>
  cases hwalk with | cons hrel hwalk =>
  cases hwalk with | cons hbeta hwalk =>
  cases hwalk with | cons hf hwalk =>
  cases hwalk with | cons hcompat hwalk =>
  cases hwalk with | cons hmajor hwalk =>
  simp [VExpr.instL, VExpr.inst, VLevel.inst, VExpr.inst_lift, ← VExpr.lift_instN_lo] at ha hrel hmajor
  have hproof : program.domains.reverse ++ Γ ⊢
      QuotPrefixUnfolding.prefixProof [u, v] args : a0 := by
    have h := hq.propInhabitant_app (Γ := program.domains.reverse ++ Γ) hu hz ha hrel
      (by simpa [VExpr.mkApps] using hmajor)
    simpa [QuotPrefixUnfolding.prefixProof, hall] using h
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [← getD_of_lt (d := default) hj]
    rw [hcapture] at hj ⊢
    simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
      List.length_cons, List.length_nil] at hj ⊢
    match j, hj with
    | 0, _ => exact hallWF a0 (by simp)
    | 1, _ => exact hallWF a1 (by simp)
    | 2, _ => exact hallWF a2 (by simp)
    | 3, _ => exact hallWF a3 (by simp)
    | 4, _ => exact hallWF a4 (by simp)
    | 5, _ => exact ⟨_, hproof⟩
    | n + 6, h => omega
  · have hbody' : CaseSchema.EquationBody.extract quotDefEq.lhs quotDefEq.rhs quotDefEq.type =
        some program.equationBody := by rwa [heqn] at hbody
    have hbEq := Option.some.inj (hbody'.symm.trans
      (rfl : _ = some (⟨_, _, _, _⟩ : CaseSchema.EquationBody)))
    rw [hbEq, hcapture, hctor, hlv]
    simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    have hctorEq : ((mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]).instL [u, v]).instOuter
        [a0, a1, a2, a3, a4, QuotPrefixUnfolding.prefixProof [u, v] args] =
        mkApps (.const ``Quot.mk [u]) [a0, a1, QuotPrefixUnfolding.prefixProof [u, v] args] := by
      simp [VExpr.instL, VLevel.inst, VExpr.instOuter_eq_subst, VExpr.subst, VExpr.Subst.ofList,
        VExpr.mkApps]
    exact ⟨_, by
      show (VExpr.app ((mkApps (.const ``Quot.lift (VLevel.params 2))
          [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]).instL [u, v])
        ((mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]).instL [u, v])).instOuter _ =
          _
      rw [instOuter_app, hctorEq]⟩

end

/-! ## The descent of prefix unfolding and of parallel delta steps -/

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A

/-- Descent of a singleton prefix unfolding above on the lift of a spine typed below. -/
theorem PrefixUnfold.descend' (heq : Params.env.HasCanonicalEq) (hTF : TypedFrontN Params.env)
    {k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {name : Name} {levels : List VLevel} {args : List VExpr} {T rhs : VExpr}
    (he : Γ ⊢ mkApps (.const name levels) args : T)
    (H : PrefixUnfold Params.env univs recursorData Γ' name levels (args.map (·.liftN 1 k)) rhs) :
    ∃ rhs₀, rhs = rhs₀.liftN 1 k ∧
      PrefixUnfold Params.env univs recursorData Γ name levels args rhs₀ := by
  cases H with
  | @intro data program hl hr hn ht hw hz hg replay =>
    obtain ⟨program₀, hg₀⟩ :=
      InductiveSignature.RecursorData.singletonUnfolding_sameArity (args' := args) hg (by simp)
    obtain ⟨type, htype⟩ := hr.recursorType_exists
    have hg₁ := InductiveSignature.RecursorData.singletonUnfolding_lift'
      (ρ := (Lift.refl.skipN 1).consN k) henv hr ht hz htype (hr.recursorType_closed henv htype) hg₀
    rw [← map_liftN_eq_lift'] at hg₁
    cases InductiveSignature.RecursorData.singletonUnfolding_unique hg hg₁
    have hsrc : mkApps (.const name levels) (args.map (·.liftN 1 k)) =
        (mkApps (.const name levels) args).liftN 1 k := by rw [liftN_mkApps]; rfl
    rw [hsrc] at replay
    subst hn
    obtain ⟨hcap, hlhsApp⟩ := singleton_captures_typed heq hTF W hΓ hΓ' hr ht hz hw hg₀ he replay
    obtain ⟨-, -, -, -, hgen, hbody, -⟩ := singletonUnfolding_spec hg₀
    have replay₀ := UnfoldingCheck.descend_of_typed henv hTF W hΓ hΓ'
      (hr.prefixType henv hΓ hw hg₀ ⟨_, he⟩) replay hcap hlhsApp
      (hr.singletonEquation_body_head hgen hbody)
    refine ⟨program₀.rhs, ?_, .intro hl hr rfl ht hw hz hg₀ replay₀⟩
    rw [InductiveSignature.RecursorData.PrefixUnfolding.rename_rhs (replay₀.templateScope henv).2.1,
      lift'_consN_skipN]

/-- Descent of a quotient prefix unfolding above on the lift of a spine typed below. -/
theorem QuotPrefixUnfold.descend' (hTF : TypedFrontN Params.env)
    {k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {levels : List VLevel} {args : List VExpr} {T rhs : VExpr}
    (he : Γ ⊢ mkApps (.const ``Quot.lift levels) args : T)
    (H : QuotPrefixUnfold Params.env univs Γ' levels (args.map (·.liftN 1 k)) rhs) :
    ∃ rhs₀, rhs = rhs₀.liftN 1 k ∧ QuotPrefixUnfold Params.env univs Γ levels args rhs₀ := by
  cases H with
  | @intro program hr hw hz hg replay =>
    have hg₀ := QuotPrefixUnfolding.generate_inst (arg := .sort .zero) (k := k) hg
    have hargs : (args.map (·.liftN 1 k)).map (·.inst (.sort .zero) k) = args := by
      simp [List.map_map, Function.comp_def, inst_liftN]
    rw [hargs] at hg₀
    have hg₁ := QuotPrefixUnfolding.generate_rename (ρ := (Lift.refl.skipN 1).consN k) hg₀
    rw [← map_liftN_eq_lift'] at hg₁
    have hpe := QuotPrefixUnfolding.generate_unique hg hg₁
    have hsrc : mkApps (.const ``Quot.lift levels) (args.map (·.liftN 1 k)) =
        (mkApps (.const ``Quot.lift levels) args).liftN 1 k := by rw [liftN_mkApps]; rfl
    rw [hsrc, hpe] at replay
    obtain ⟨hcap, hlhsApp⟩ := quot_captures_typed hΓ hr hw hz hg₀ he
    obtain ⟨-, -, -, -, heqn, hbody, -⟩ := QuotPrefixUnfolding.generate_spec hg₀
    have replay₀ := UnfoldingCheck.descend_of_typed henv hTF W hΓ hΓ'
      (hr.prefixType henv hΓ hw hg₀ ⟨_, he⟩) replay hcap hlhsApp
      (QuotPrefixUnfolding.equationBody_head (by rwa [heqn] at hbody))
    refine ⟨_, ?_, .intro hr hw hz hg₀ replay₀⟩
    calc program.rhs
        = ((program.instN (.sort .zero) k).rename ((Lift.refl.skipN 1).consN k)).rhs := by rw [← hpe]
      _ = _ := by
        rw [InductiveSignature.RecursorData.PrefixUnfolding.rename_rhs
          (replay₀.templateScope henv).2.1, lift'_consN_skipN]

/-- Descent of a parallel delta step above on the lift of a term typed below, from the typed
front alone (B2's `DeltaPar.descend` with the unfolding-check descent discharged). -/
theorem DeltaPar.descend' (heq : Params.env.HasCanonicalEq) (hTF : TypedFrontN Params.env)
    {k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {e T out : VExpr} (he : Γ ⊢ e : T) (H : DeltaPar Γ' (e.liftN 1 k) out) :
    ∃ e', out = e'.liftN 1 k ∧ DeltaPar Γ e e' := by
  generalize hs : e.liftN 1 k = src at H
  induction H generalizing e T k Γ with
  | bvar | sort | const | elim => exact ⟨e, hs.symm, .rfl⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv.ordered hΓ
    obtain ⟨f', rfl, hf'⟩ := ih1 W hΓ hΓ' hf rfl
    obtain ⟨a', rfl, ha'⟩ := ih2 W hΓ hΓ' ha rfl
    exact ⟨.app f' a', rfl, .app hf' ha'⟩
  | proj _ ih =>
    obtain ⟨m₀, rfl, rfl⟩ := liftN_eq_proj_inv hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv.ordered hΓ
    obtain ⟨m', rfl, hm'⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    exact ⟨.proj _ _ m', rfl, .proj hm'⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hs
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv.ordered hΓ
    obtain ⟨A', rfl, hA'⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ih2 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    exact ⟨.lam A' b', rfl, .lam hA' hb'⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_forallE_inv hs
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.forallE_inv henv.ordered
    obtain ⟨A', rfl, hA'⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ih2 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    exact ⟨.forallE A' b', rfl, .forallE hA' hb'⟩
  | @delta Γ₁ name levels rhs args args' hlen hargs hunf ih =>
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hs
    have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, he⟩
    obtain ⟨args₀', rfl, hlen₀, hred₀⟩ := list_descend (R := DeltaPar Γ) (l := args') (l₀ := args₀)
      (by simpa using hlen.symm) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hi')
        exact ih i (by simpa using hi') hi W hΓ hΓ' hA (by simp))
    have hfr : List.Forall₂ (FullReduction Γ) args₀ args₀' :=
      forall₂_of_pointwise hlen₀ fun i hi hi' => (hred₀ i hi hi').full
    have he' := (FullReduction.mkApps .rfl hfr).hasType hΓ he
    obtain ⟨rhs₀, rfl, hunf₀⟩ := PrefixUnfold.descend' heq hTF W hΓ hΓ' he' hunf
    exact ⟨rhs₀, rfl, .delta hlen₀.symm (fun i hi hi' => hred₀ i hi hi') hunf₀⟩
  | @quotDelta Γ₁ levels rhs args args' hlen hargs hunf ih =>
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hs
    have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, he⟩
    obtain ⟨args₀', rfl, hlen₀, hred₀⟩ := list_descend (R := DeltaPar Γ) (l := args') (l₀ := args₀)
      (by simpa using hlen.symm) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hi')
        exact ih i (by simpa using hi') hi W hΓ hΓ' hA (by simp))
    have hfr : List.Forall₂ (FullReduction Γ) args₀ args₀' :=
      forall₂_of_pointwise hlen₀ fun i hi hi' => (hred₀ i hi hi').full
    have he' := (FullReduction.mkApps .rfl hfr).hasType hΓ he
    obtain ⟨rhs₀, rfl, hunf₀⟩ := QuotPrefixUnfold.descend' hTF W hΓ hΓ' he' hunf
    exact ⟨rhs₀, rfl, .quotDelta hlen₀.symm (fun i hi hi' => hred₀ i hi hi') hunf₀⟩
  | @projIota Γ₁ family info index levels fieldType field args args' hlen hargs hi hs' hget hfield ih =>
    obtain ⟨m₀, rfl, hm⟩ := liftN_eq_proj_inv hs
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hm.symm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := he.proj_inv henv.ordered hΓ
    have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, hmajor.hasType.2⟩
    obtain ⟨args₀', rfl, hlen₀, hred₀⟩ := list_descend (R := DeltaPar Γ) (l := args') (l₀ := args₀)
      (by simpa using hlen.symm) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hi')
        exact ih i (by simpa using hi') hi W hΓ hΓ' hA (by simp))
    have hfr : List.Forall₂ (FullReduction Γ) args₀ args₀' :=
      forall₂_of_pointwise hlen₀ fun i hi hi' => (hred₀ i hi hi').full
    have he' := (FullReduction.proj (FullReduction.mkApps .rfl hfr)).hasType hΓ he
    obtain ⟨field₀, hget₀, rfl⟩ : ∃ field₀, args₀'[info.nparams + index]? = some field₀ ∧
        field = field₀.liftN 1 k := by
      rw [List.getElem?_map] at hget
      cases h : args₀'[info.nparams + index]? with
      | none => rw [h] at hget; cases hget
      | some f => rw [h] at hget; exact ⟨f, rfl, (Option.some.inj hget).symm⟩
    have hmajor' := (FullReduction.mkApps .rfl hfr).hasType hΓ hmajor.hasType.2
    obtain ⟨_, hf₀⟩ := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, hmajor'⟩ _
      (List.mem_of_getElem? hget₀)
    obtain ⟨u, hT⟩ := he.isType henv.ordered hΓ
    have hs'' : Params.env.HasType univs Γ₁
        ((VExpr.proj family index (mkApps (.const info.ctorName levels) args₀')).liftN 1 k)
        (T.liftN 1 k) := he'.weakN henv.ordered W
    simp only [liftN, liftN_mkApps] at hs''
    have hfield' : Params.env.HasType univs Γ₁ (field₀.liftN 1 k) (T.liftN 1 k) :=
      hfield.defeqU_r henv hΓ' (hs'.uniqU henv hΓ' hs'')
    have hfieldT := hTF.retype henv W hΓ hΓ' hf₀ hT hfield'
    exact ⟨field₀, rfl, .projIota hlen₀.symm (fun i hi hi' => hred₀ i hi hi') hi he' hget₀ hfieldT⟩


/-! ## The chain descents without the unfolding-check obligation -/

/-- `LStep.chain_descend` with the unfolding-check descent discharged. -/
theorem LStep.chain_descend' (heq : Params.env.HasCanonicalEq) (hTF : TypedFrontN Params.env)
    (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hmajor : MajorEtaDescends) {k : Nat} {Γ Γ' : List VExpr} {e T s' : VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (he : Γ ⊢ e : T)
    (H : ReflTransGen (LStep Γ') (e.liftN 1 k) s') :
    ∃ e', s' = e'.liftN 1 k ∧ FullReduction Γ e e' := by
  generalize hs : e.liftN 1 k = s at H
  induction H using ReflTransGen.headIndOn generalizing e with
  | rfl => exact ⟨e, hs.symm, .rfl⟩
  | head step tail ih =>
    subst hs
    rcases step with (h | h) | h
    · obtain ⟨e₁, rfl, h'⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' he h
      obtain ⟨e', rfl, hred⟩ := ih ((FullStep.core h').hasType hΓ he) rfl
      exact ⟨e', rfl, (ReflTransGen.tail .rfl (.core h')).trans hred⟩
    · obtain ⟨e₁, rfl, h'⟩ := DeltaPar.descend' heq hTF W hΓ hΓ' he h
      obtain ⟨e', rfl, hred⟩ := ih (h'.full.hasType hΓ he) rfl
      exact ⟨e', rfl, h'.full.trans hred⟩
    · obtain ⟨e₁, rfl, h'⟩ := MajorEtaIotaC.descend hmajor W hΓ hΓ' he h
      obtain ⟨e', rfl, hred⟩ := ih (h'.hasType hΓ he) rfl
      exact ⟨e', rfl, h'.trans hred⟩

/-- `EtaNE.forallE_inv_lift` with the unfolding-check descent discharged. -/
theorem EtaNE.forallE_inv_lift' (heq : Params.env.HasCanonicalEq) (hTF : TypedFrontN Params.env)
    (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hmajor : MajorEtaDescends)
    {k : Nat} {Γ Γ' : List VExpr} {F A B : VExpr} {u : VLevel} (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (hF : Γ ⊢ F : .sort u) (H : EtaNE Γ' (F.liftN 1 k) (.forallE A B)) :
    ∃ A₀ B₀, FullReduction Γ F (.forallE A₀ B₀) := by
  generalize hs : F.liftN 1 k = s at H
  generalize hr : VExpr.forallE A B = r at H
  induction H generalizing F A B with
  | forallEC =>
    cases hr
    obtain ⟨A₀, B₀, rfl, -, -⟩ := liftN_eq_forallE_inv hs
    exact ⟨A₀, B₀, .rfl⟩
  | funEta hPi =>
    subst hs
    exact (type_not_function hΓ' (hF.weakN henv.ordered W) hPi).elim
  | structEta hl _ _ hs' =>
    subst hs
    exact (type_not_structure hΓ' (hF.weakN henv.ordered W) hl hs').elim
  | betaR hT =>
    exact (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hr.symm).elim
  | redL h _ ih =>
    subst hs hr
    rcases h with (h | h) | h
    · obtain ⟨F₁, rfl, h'⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' hF h
      obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' ((FullStep.core h').hasType hΓ hF) rfl rfl
      exact ⟨A₂, B₂, (ReflTransGen.tail .rfl (.core h')).trans hred⟩
    · obtain ⟨F₁, rfl, h'⟩ := DeltaPar.descend' heq hTF W hΓ hΓ' hF h
      obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' (h'.full.hasType hΓ hF) rfl rfl
      exact ⟨A₂, B₂, h'.full.trans hred⟩
    · obtain ⟨F₁, rfl, h'⟩ := MajorEtaIotaC.descend hmajor W hΓ hΓ' hF h
      obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' (h'.hasType hΓ hF) rfl rfl
      exact ⟨A₂, B₂, h'.trans hred⟩
  | bvar | sort | const | elim | app | proj | lamC | lamD => cases hr

/-- `EtaNE.const_spine_inv_lift` with the unfolding-check descent discharged. -/
theorem EtaNE.const_spine_inv_lift' (heq : Params.env.HasCanonicalEq) (hTF : TypedFrontN Params.env)
    (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hmajor : MajorEtaDescends) {k : Nat} {Γ Γ' : List VExpr} {F : VExpr} {u : VLevel}
    {S : Name} {ls : List VLevel} {args : List VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (hF : Γ ⊢ F : .sort u)
    (H : EtaNE Γ' (F.liftN 1 k) (mkApps (.const S ls) args)) :
    ∃ args₀, FullReduction Γ F (mkApps (.const S ls) args₀) := by
  obtain ⟨s', hch, hc⟩ := EtaNE.const_spine_inv hΓ' H (hF.weakN henv.ordered W) rfl
  obtain ⟨F', rfl, hred⟩ := LStep.chain_descend' heq hTF hcase hcv hmajor W hΓ hΓ' hF hch
  have hF' : Γ' ⊢ F'.liftN 1 k : .sort u := (hred.hasType hΓ hF).weakN henv.ordered W
  rcases hc with ⟨args_s, hs, -⟩ | ⟨family, info, params, hl, -, -, -, hs', -, -, -⟩
  · obtain ⟨args₀, rfl, -⟩ := liftN_eq_mkApps_const_inv hs
    exact ⟨args₀, hred⟩
  · exact (type_not_structure hΓ' hF' hl hs').elim

end

end Lean4Lean.VEnv.StrengtheningUnfolding
