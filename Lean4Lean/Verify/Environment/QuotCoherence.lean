import Lean4Lean.Verify.Environment.RecursorCoherence
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Quot

/-!
# The quotient part of the recursor invariant

The quotient reduction rules of the checker as instances of the shapes of
`Lean4Lean/Theory/Typing/RecursorLemmas.lean`: under `QuotCoherent`, `Quot.lift` has the
recursor shape `VRecursorShape`, `Quot.mk` the constructor shape `VConstructorShape`, and the
`Quot.lift` equation the iota rule shape `VIotaRuleShape`; `Quot.ind` reduces by proof
irrelevance (`QuotCoherent.ind_defeq`). `AddQuot.quotCoherent` establishes `QuotCoherent` when the
quotient constants are added.
-/

namespace Lean4Lean
open Lean

variable {venv : VEnv}

/-- `Quot.lift` has the recursor shape with five parameters, of which the first two are the
parameters of `Quot.mk`. -/
def QuotCoherent.liftRecursorShape (H : QuotCoherent venv) :
    VRecursorShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot [.param 0] where
  ctorParams_length := rfl
  ctorParams_closed := by
    intro p hp
    simp only [VExpr.bvarRange, List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    simp only [VExpr.ClosedN]
    omega
  type := quotLiftConst.type
  const := H.lift
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort (.param 1), .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]
  result := .bvar 3
  type_eq := rfl
  doms_length := rfl
  major_eq := rfl

/-- `Quot.mk` has the constructor shape with two parameters and one field. -/
def QuotCoherent.mkConstructorShape (H : QuotCoherent venv) :
    VConstructorShape venv ``Quot.mk 1 2 1 0 ``Quot where
  type := quotMkConst.type
  const := H.quotMk
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
  indices := []
  type_eq := rfl
  doms_length := rfl
  indices_length := rfl

/-- The `Quot.lift` equation has the iota rule shape. -/
def QuotCoherent.liftRuleShape (H : QuotCoherent venv) :
    VIotaRuleShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot.mk [.param 0] 1 quotDefEq where
  defeq := H.defeq
  uvars := rfl
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort (.param 1), .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .bvar 4]
  lhsBody := quotDefEq.lhs.stripLams
  rhsBody := .app (.bvar 2) (.bvar 0)
  typeBody := .bvar 3
  lhs_eq := rfl
  rhs_eq := rfl
  type_eq := rfl
  doms_length := rfl
  indexArgs := []
  indexArgs_length := rfl
  lhs_pattern := rfl
  rec_doms := by
    intro recDoms recBody hc hlen j hj
    rw [H.lift] at hc
    have htype : VExpr.wrapForalls H.liftRecursorShape.doms H.liftRecursorShape.result =
        VExpr.wrapForalls recDoms recBody := congrArg VConstant.type (Option.some.inj hc)
    obtain ⟨rfl, -⟩ := VExpr.wrapForalls_inj_of_length (by rw [hlen]; rfl) htype
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  ctor_doms := by
    intro ctorUvars ctorDoms ctorBody hc hlen i hi hd hcd
    rw [H.quotMk] at hc
    have htype : VExpr.wrapForalls H.mkConstructorShape.doms
          (VExpr.mkApps (.const ``Quot (VLevel.params 1))
            (VExpr.bvarRange 2 (2 + 1) ++ H.mkConstructorShape.indices)) =
        VExpr.wrapForalls ctorDoms ctorBody := congrArg VConstant.type (Option.some.inj hc)
    obtain ⟨rfl, -⟩ := VExpr.wrapForalls_inj_of_length (by rw [hlen]; rfl) htype
    match i, hi with
    | 0, _ => exact VEnv.IsDefEqU.refl ⟨_, .bvar (.succ (.succ (.succ (.succ .zero))))⟩

/-- A lift over more binders than the instantiation depth is cancelled one step. -/
@[simp] theorem _root_.Lean4Lean.VExpr.inst_liftN_lt (e a : VExpr) {k m : Nat} (h : k < m) :
    (VExpr.liftN m e).inst a k = VExpr.liftN (m - 1) e := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 + k := ⟨m - 1 - k, by omega⟩
  rw [← VExpr.liftN'_liftN_lo e (n + 1) k, VExpr.inst_liftN', VExpr.liftN'_liftN_lo]
  congr 1; omega

/-- `Quot.ind` reduces by proof irrelevance: applied to a term convertible to `Quot.mk α r a`, it
is definitionally equal to its minor premise applied to `a`. -/
theorem QuotCoherent.ind_defeq (henv : VEnv.WF venv) (hΓ : OnCtx Γ (venv.IsType U))
    (hq : QuotCoherent venv) {ls' lsm' : List VLevel}
    (hls'w : ∀ l ∈ ls', l.WF U) (hls'len : ls'.length = 1)
    (hlsm'w : ∀ l ∈ lsm', l.WF U) (hlsm'len : lsm'.length = 1)
    {α' r' β' p' q' a1' a2' a3' : VExpr}
    (hwf : VExpr.WF venv U Γ (VExpr.mkApps (.const ``Quot.ind ls') [α', r', β', p', q']))
    (hmkwf : VExpr.WF venv U Γ (VExpr.mkApps (.const ``Quot.mk lsm') [a1', a2', a3']))
    (hmk : venv.IsDefEqU U Γ (VExpr.mkApps (.const ``Quot.mk lsm') [a1', a2', a3']) q') :
    venv.IsDefEqU U Γ (VExpr.mkApps (.const ``Quot.ind ls') [α', r', β', p', q'])
      (.app p' a3') := by
  obtain ⟨u', rfl⟩ : ∃ u', ls' = [u'] := match ls', hls'len with | [u'], _ => ⟨u', rfl⟩
  obtain ⟨um', rfl⟩ : ∃ um', lsm' = [um'] := match lsm', hlsm'len with | [um'], _ => ⟨um', rfl⟩
  have hu' : u'.WF U := hls'w _ (List.mem_singleton.2 rfl)
  have hum' : um'.WF U := hlsm'w _ (List.mem_singleton.2 rfl)
  -- the eliminator spine
  have hc := VEnv.HasType.const (Γ := Γ) hq.ind hls'w rfl
  have ⟨hargsT, hres⟩ := VEnv.HasType.mkApps_wrapForalls henv hΓ (doms :=
      [.sort u', .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
       .forallE (.app (.app (.const ``Quot [u']) (.bvar 1)) (.bvar 0)) (.sort .zero),
       .forallE (.bvar 2) (.app (.bvar 1)
         (.app (.app (.app (.const ``Quot.mk [u']) (.bvar 3)) (.bvar 2)) (.bvar 0))),
       .app (.app (.const ``Quot [u']) (.bvar 3)) (.bvar 2)])
    (body := .app (.bvar 2) (.bvar 0)) hc hwf rfl
  have hβ : venv.HasType U Γ β'
      (.forallE (.app (.app (.const ``Quot [u']) α') r') (.sort .zero)) := by
    have := hargsT 2 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hp : venv.HasType U Γ p'
      (.forallE α' (.app (VExpr.liftN 1 β')
        (.app (.app (.app (.const ``Quot.mk [u']) (VExpr.liftN 1 α')) (VExpr.liftN 1 r'))
          (.bvar 0)))) := by
    have := hargsT 3 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hq' : venv.HasType U Γ q' (.app (.app (.const ``Quot [u']) α') r') := by
    have := hargsT 4 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hX1 : venv.HasType U Γ (VExpr.mkApps (.const ``Quot.ind [u']) [α', r', β', p', q'])
      (.app β' q') := by
    simpa [VExpr.inst, VExpr.instVar] using hres
  -- the constructor spine
  have hcm := VEnv.HasType.const (Γ := Γ) hq.quotMk hlsm'w rfl
  have ⟨hmargsT, hmres⟩ := VEnv.HasType.mkApps_wrapForalls henv hΓ (doms :=
      [.sort um', .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1])
    (body := .app (.app (.const ``Quot [um']) (.bvar 2)) (.bvar 1)) hcm hmkwf rfl
  have ha1 : venv.HasType U Γ a1' (.sort um') := by
    have := hmargsT 0 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have ha2 : venv.HasType U Γ a2' (.forallE a1' (.forallE (VExpr.liftN 1 a1') (.sort .zero))) := by
    have := hmargsT 1 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have ha3 : venv.HasType U Γ a3' a1' := by
    have := hmargsT 2 (by simp) (by simp)
    simpa [VExpr.inst, VExpr.instVar] using this
  have hmkT : venv.HasType U Γ (VExpr.mkApps (.const ``Quot.mk [um']) [a1', a2', a3'])
      (.app (.app (.const ``Quot [um']) a1') a2') := by
    simpa [VExpr.inst, VExpr.instVar] using hmres
  -- injectivity of `Quot`
  have hQQ : venv.IsDefEqU U Γ (VExpr.mkApps (.const ``Quot [u']) [α', r'])
      (VExpr.mkApps (.const ``Quot [um']) [a1', a2']) :=
    ((hmk.symm.of_l henv hΓ hq').hasType.2).uniqU henv hΓ hmkT
  have ⟨_, hsort⟩ := hq'.isType henv.ordered hΓ
  have ⟨hlv, hargsE⟩ := VEnv.IsDefEqU.rigidApp_inv henv hΓ hq.rigid hQQ hsort
  have hαa : venv.IsDefEqU U Γ α' a1' := List.forall₂_getElem hargsE 0 (by simp) (by simp)
  have hra : venv.IsDefEqU U Γ r' a2' := List.forall₂_getElem hargsE 1 (by simp) (by simp)
  have huu : u' ≈ um' := List.forall₂_getElem hlv 0 (by simp) (by simp)
  -- `Quot.mk um' a1' a2' a3' ≡ Quot.mk u' α' r' a3'`
  have hcDF : venv.IsDefEq U Γ (.const ``Quot.mk [um']) (.const ``Quot.mk [u'])
      (VExpr.wrapForalls [.sort um', .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
        (.app (.app (.const ``Quot [um']) (.bvar 2)) (.bvar 1))) :=
    VEnv.IsDefEq.constDF hq.quotMk hlsm'w hls'w rfl
      (.cons (VLevel.equiv_def'.2 (VLevel.equiv_def'.1 huu).symm) .nil)
  have hcongr := VEnv.IsDefEq.mkApps_congr (args := [a1', a2', a3']) (args' := [α', r', a3'])
    hcDF rfl rfl (by
      intro j hj hj' hj''
      match j, hj with
      | 0, _ => exact hαa.symm.of_l henv hΓ ha1
      | 1, _ =>
        refine hra.symm.of_l henv hΓ ?_
        simpa [VExpr.inst, VExpr.instVar] using ha2
      | 2, _ =>
        show venv.HasType U Γ a3' _
        simpa [VExpr.inst, VExpr.instVar] using ha3)
  simp [VExpr.inst, VExpr.instVar] at hcongr
  have hmk1 : venv.IsDefEq U Γ (VExpr.mkApps (.const ``Quot.mk [um']) [a1', a2', a3'])
      (VExpr.mkApps (.const ``Quot.mk [u']) [α', r', a3'])
      (VExpr.mkApps (.const ``Quot [u']) [α', r']) :=
    VEnv.IsDefEqU.defeqDF henv hΓ hQQ.symm hcongr
  have hqmk : venv.IsDefEq U Γ q' (VExpr.mkApps (.const ``Quot.mk [u']) [α', r', a3'])
      (VExpr.mkApps (.const ``Quot [u']) [α', r']) :=
    (hmk.symm.of_l henv hΓ hq').trans hmk1
  have ha3α : venv.HasType U Γ a3' α' := ha3.defeqU_r henv hΓ hαa.symm
  have hX2 := hp.app ha3α
  simp [VExpr.inst, VExpr.instVar] at hX2
  have hβsort : venv.HasType U Γ (.app β' q') (.sort .zero) := by
    simpa [VExpr.inst] using hβ.app hq'
  have htyeq : venv.IsDefEq U Γ (.app β' q')
      (.app β' (VExpr.mkApps (.const ``Quot.mk [u']) [α', r', a3'])) (.sort .zero) := by
    simpa [VExpr.inst] using hβ.appDF hqmk
  have hX2' : venv.HasType U Γ (.app p' a3') (.app β' q') :=
    hX2.defeqU_r henv hΓ ⟨_, htyeq.symm⟩
  exact ⟨_, VEnv.IsDefEq.proofIrrel hβsort hX1 hX2'⟩

/-! ## The quotient step of the environment translation -/

/-- Initializing quotients yields the quotient invariant, given that `Quot` is rigid in the
resulting environment (`EquationHeadsCoherent.rigid_quot`). -/
theorem AddQuot.quotCoherent (H : AddQuot m₁ m₂ venv₁ venv₂)
    (hrigid : venv₂.Rigid ``Quot) : QuotCoherent venv₂ := by
  obtain ⟨_, _, e1, -, -, h1, _, _, e2, -, -, h2, _, _, e3, -, -, h3, _, _, e4, -, -, h4, -, rfl⟩ := H
  have le2 := VEnv.addConst_le h2
  have le3 := VEnv.addConst_le h3
  have le4 := VEnv.addConst_le h4
  have le5 : e4 ≤ e4.addDefEq quotDefEq := VEnv.addDefEq_le
  refine ⟨?_, ?_, ?_, ?_, Or.inl rfl, hrigid⟩
  · exact le5.constants (le4.constants (le3.constants (le2.constants (VEnv.addConst_self h1))))
  · exact le5.constants (le4.constants (le3.constants (VEnv.addConst_self h2)))
  · exact le5.constants (le4.constants (VEnv.addConst_self h3))
  · exact le5.constants (VEnv.addConst_self h4)

end Lean4Lean
