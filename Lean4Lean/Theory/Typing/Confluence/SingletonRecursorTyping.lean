import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping
import Lean4Lean.Theory.Inductive.InstanceSpecialize
import Lean4Lean.Theory.Inductive.HypothesisTyping
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.SingletonExtraction.TelescopeTyping
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Theory.Typing.IotaLemmas

set_option linter.unusedSimpArgs false
namespace Lean4Lean
open VExpr
namespace VExpr
/-- The proposition `∀ p : Prop, p → p`. -/
def trueTy : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
/-- Its proof `fun p x => x`. -/
def truePf : VExpr := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))
theorem trueTy_closed : trueTy.ClosedN 0 := by simp [trueTy, ClosedN]
/-- Instantiating the outer variables of a term lifted past some of them skips those. -/
theorem liftN_instOuter_drop {e : VExpr} {X Y Z : List VExpr}
    (he : e.ClosedN (X.length + Z.length)) :
    (e.liftN Y.length Z.length).instOuter (X ++ Y ++ Z) = e.instOuter (X ++ Z) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_subst]
  apply VExpr.subst_congr_closedN he
  intro i hi
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  have hX : (X ++ Z).length = X.length + Z.length := by simp
  have hXYZ : (X ++ Y ++ Z).length = X.length + Y.length + Z.length := by simp; omega
  by_cases hik : i < Z.length
  · rw [liftVar_lt hik, VExpr.Subst.ofList_lt _ (by omega), VExpr.Subst.ofList_lt _ (by omega)]
    rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hik), VExpr.Subst.ofList_lt _ (by omega),
      VExpr.Subst.ofList_lt _ (by omega)]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by omega)]
    congr 1; omega
end VExpr
namespace VEnv
variable {env : VEnv} {U : Nat}
theorem HasType.trueTy :
    env.HasType U Γ VExpr.trueTy (.sort .zero) := by
  have h0 : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by simp [VLevel.WF])
  have h1 : env.HasType U (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have h2 : env.HasType U (.bvar 0 :: .sort .zero :: Γ) (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have h := HasType.forallE h0 (HasType.forallE h1 h2)
  exact .defeqDF (.sortDF (by simp [VLevel.WF]) (by simp [VLevel.WF])
    (by funext; simp [VLevel.eval, Lean.Nat.imax])) h
theorem HasType.truePf :
    env.HasType U Γ VExpr.truePf VExpr.trueTy := by
  have h0 : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by simp [VLevel.WF])
  have h1 : env.HasType U (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have h2 : env.HasType U (.bvar 0 :: .sort .zero :: Γ) (.bvar 0) (.bvar 1) := .bvar .zero
  exact HasType.lam h0 (HasType.lam h1 h2)
/-- A Pi-type ending in an application of the constant family `fun ds => trueTy` is
inhabited. -/
theorem HasType.inhabit_trueFamily (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {B xs D : List VExpr}
    (hH : env.HasType U (B.reverse ++ Γ) (VExpr.wrapLams D VExpr.trueTy)
      (VExpr.wrapForalls D (.sort .zero)))
    (hT : env.IsType U Γ (VExpr.wrapForalls B (VExpr.mkApps (VExpr.wrapLams D VExpr.trueTy) xs))) :
    env.HasType U Γ (VExpr.wrapLams B VExpr.truePf)
      (VExpr.wrapForalls B (VExpr.mkApps (VExpr.wrapLams D VExpr.trueTy) xs)) := by
  obtain ⟨hctx, u, hb⟩ := IsType.wrapForalls_inv henv hΓ hT
  have hlen := HasType.mkApps_sort_arity henv hctx hH hb
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hctx hH ⟨_, hb⟩ hlen
  have hβ := IsDefEq.mkApps_wrapLams henv hctx hH hlen hargs
  rw [instOuter_closed0 VExpr.trueTy_closed, instOuter_closed0 (by simp [VExpr.ClosedN])] at hβ
  exact HasType.wrapLams_of hctx (.defeqDF hβ.symm HasType.truePf)
end VEnv
namespace VEnv
open InductiveSignature
variable {env : VEnv} {U : Nat}
theorem OnCtx.closed_reverse (henv : env.Ordered) {doms : List VExpr}
    (h : OnCtx doms.reverse (env.IsType U)) :
    ∀ j (hj : j < doms.length), (doms[j]).ClosedN j := by
  intro j hj
  have hc : OnCtx (doms.reverse ++ []) (fun Γ A => A.ClosedN Γ.length) := by
    rw [List.append_nil]; exact CtxWF.closed henv h
  have := OnCtx.getElem_reverse_append hc j hj
  simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using this.2
/-- The minor premise's field context, with the motive instantiated: the field telescope is
well formed in its own context, and the context of the minor premise is instantiated at the
field variables. -/
theorem minorFields_inst (henv : env.WF) {P F : List VExpr} {Mot M0 : VExpr}
    (hP : OnCtx P.reverse (env.IsType U)) (hM0 : env.HasType U P.reverse M0 Mot)
    (hF : OnCtx ((insertBinders F 1).reverse ++ Mot :: P.reverse) (env.IsType U))
    (hFcl : ∀ i (h : i < F.length), (F[i]).ClosedN (P.length + i)) :
    ∀ i, i ≤ F.length → OnCtx (P ++ F.take i).reverse (env.IsType U) ∧
      TelInst env U (P ++ F.take i).reverse (P ++ [Mot] ++ (insertBinders F 1).take i)
        (bvarRange P.length (P.length + i) ++ [M0.liftN i] ++ bvarRange i i) := by
  have hall : OnCtx (P ++ [Mot] ++ insertBinders F 1).reverse (env.IsType U) := by
    simpa using hF
  have hcl := OnCtx.closed_reverse henv.ordered hall
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simpa using hP, ?_⟩
    have hPcl : ∀ j (h : j < P.length), (P[j]).ClosedN j := fun j h => by
      have := hcl j (by simp; omega)
      rwa [List.getElem_append_left (by simp; omega), List.getElem_append_left h] at this
    have hI := TelInst.ident (env := env) (U := U) [] hPcl
    have hMotcl : Mot.ClosedN P.length := by
      have := hcl P.length (by simp)
      rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)] at this
      simpa using this
    have hM : env.HasType U P.reverse (M0.liftN 0) (Mot.instOuter (bvarRange P.length P.length)) := by
      rw [VExpr.instOuter_range_bvar' _ _ _ hMotcl (Nat.le_refl _), Nat.sub_self,
        VExpr.liftN_zero, VExpr.liftN_zero]
      exact hM0
    have := TelInst.append_one (by simpa using hI) hM
    simpa [bvarRange_zero] using this
  | succ i ih =>
    intro hi
    obtain ⟨hctx, ht⟩ := ih (Nat.le_of_succ_le hi)
    have hilt : i < F.length := hi
    have hFi := OnCtx.getElem_reverse_append (L := P ++ [Mot] ++ insertBinders F 1) (Γ := [])
      (by rw [List.append_nil]; exact hall) (P.length + 1 + i) (by simp; omega)
    have hdom : (P ++ [Mot] ++ insertBinders F 1)[P.length + 1 + i]'(by simp; omega) =
        (F[i]).liftN 1 i := by
      rw [List.getElem_append_right (by simp), getElem_insertBinders (by simp; omega)]
      simp
    have htake : (P ++ [Mot] ++ insertBinders F 1).take (P.length + 1 + i) =
        P ++ [Mot] ++ (insertBinders F 1).take i := by
      rw [List.take_append, List.take_of_length_le (by simp)]
      simp
    rw [hdom, htake, List.append_nil] at hFi
    obtain ⟨hΔ, u, hu⟩ := hFi
    have hinst := IsDefEq.closed_instOuter_congr henv hctx hΔ hu ht.1 ht.1
      (fun j hj _ hd => ht.2 j hj hd)
    have hFicl := hFcl i hilt
    have hdrop : ((F[i]).liftN 1 i).instOuter
        (bvarRange P.length (P.length + i) ++ [M0.liftN i] ++ bvarRange i i) = F[i] := by
      have := VExpr.liftN_instOuter_drop (e := F[i]) (X := bvarRange P.length (P.length + i))
        (Y := [M0.liftN i]) (Z := bvarRange i i) (by simpa using hFicl)
      simp only [List.length_singleton, bvarRange_length] at this
      rw [this, ← SingletonLayout.bvarRange_split, VExpr.instOuter_range_bvar' _ _ _ hFicl (Nat.le_refl _),
        Nat.sub_self, VExpr.liftN_zero]
    rw [hdrop] at hinst
    simp only [VExpr.instOuter_sort] at hinst
    have hctx' : OnCtx (P ++ F.take (i + 1)).reverse (env.IsType U) := by
      rw [List.take_succ_eq_append_getElem hilt, ← List.append_assoc, List.reverse_append]
      exact ⟨hctx, _, hinst⟩
    refine ⟨hctx', ?_⟩
    have hDcl : ∀ j (h : j < (P ++ [Mot] ++ (insertBinders F 1).take i).length),
        ((P ++ [Mot] ++ (insertBinders F 1).take i)[j]).ClosedN j := by
      intro j h
      have := hcl j (by simp at h ⊢; omega)
      have key : ∀ (l1 l2 : List VExpr), l1 = l2 → ∀ (h1 : j < l1.length) (h2 : j < l2.length),
          l1[j] = l2[j] := by intro _ _ e; subst e; intros; rfl
      rw [key _ _ htake.symm h (by simp at h ⊢; omega), List.getElem_take]
      exact this
    have hw := TelInst.weak henv.ordered [F[i]] hDcl ht
    have hmap : (bvarRange P.length (P.length + i) ++ [M0.liftN i] ++ bvarRange i i).map
        (fun x : VExpr => x.liftN [F[i]].length) =
        bvarRange P.length (P.length + (i + 1)) ++ [M0.liftN (i + 1)] ++ bvarRange i (i + 1) := by
      simp only [List.length_singleton, List.map_append, List.map_cons, List.map_nil]
      rw [bvarRange_map_liftN _ _ _ (by omega), bvarRange_map_liftN _ _ _ (by omega),
        VExpr.liftN_liftN]
      simp only [Nat.add_assoc]
    rw [hmap] at hw
    have hb : env.HasType U (F[i] :: (P ++ F.take i).reverse) (.bvar 0)
        (((F[i]).liftN 1 i).instOuter
          (bvarRange P.length (P.length + (i + 1)) ++ [M0.liftN (i + 1)] ++
            bvarRange i (i + 1))) := by
      have := VExpr.liftN_instOuter_drop (e := F[i]) (X := bvarRange P.length (P.length + (i + 1)))
        (Y := [M0.liftN (i + 1)]) (Z := bvarRange i (i + 1)) (by simpa using hFicl)
      simp only [List.length_singleton, bvarRange_length] at this
      rw [this]
      have hsplit : bvarRange P.length (P.length + (i + 1)) ++ bvarRange i (i + 1) =
          bvarRange (P.length + i) (P.length + i + 1) := by
        rw [SingletonLayout.bvarRange_append _ _ _ (by omega)]
        congr 2 <;> omega
      rw [hsplit, VExpr.instOuter_range_bvar' _ _ _ hFicl (by omega)]
      simp only [show P.length + i + 1 - (P.length + i) = 1 by omega]
      exact .bvar .zero
    have := TelInst.append_one hw hb
    rw [List.take_succ_eq_append_getElem (l := insertBinders F 1) (by simpa using hilt),
      getElem_insertBinders]
    have hsnoc : bvarRange (i + 1) (i + 1) = bvarRange i (i + 1) ++ [.bvar 0] := by
      rw [SingletonLayout.bvarRange_append i 1 (i + 1) (by omega)]
      simp [bvarRange]
    have hctxeq : (P ++ F.take (i + 1)).reverse = F[i] :: (P ++ F.take i).reverse := by
      rw [List.take_succ_eq_append_getElem (l := F) hilt, ← List.append_assoc,
        List.reverse_append]; rfl
    rw [hctxeq, hsnoc]
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using this
/-- The minor premise's full context, with the motive instantiated at the constant family
of `trueTy`: every induction hypothesis is then inhabited. -/
theorem minorHyps_inst (henv : env.WF) {P F Hs D : List VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hM0 : env.HasType U P.reverse (VExpr.wrapLams D VExpr.trueTy)
      (VExpr.wrapForalls D (.sort .zero)))
    (hall : OnCtx (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).reverse
      (env.IsType U))
    (hFcl : ∀ i (h : i < F.length), (F[i]).ClosedN (P.length + i))
    (hshape : ∀ j (hj : j < Hs.length) (args : List VExpr),
      args.length = P.length + 1 + F.length + j →
      args[P.length]? = some ((VExpr.wrapLams D VExpr.trueTy).liftN F.length) →
      ∃ B xs, (Hs[j]).instOuter args =
        VExpr.wrapForalls B (VExpr.mkApps
          ((VExpr.wrapLams D VExpr.trueTy).liftN (F.length + B.length)) xs)) :
    OnCtx (P ++ F).reverse (env.IsType U) ∧
    ∃ inh : List VExpr, inh.length = Hs.length ∧
      TelInst env U (P ++ F).reverse
        (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs)
        (bvarRange P.length (P.length + F.length) ++
          [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh) := by
  have hF : OnCtx ((insertBinders F 1).reverse ++ VExpr.wrapForalls D (.sort .zero) :: P.reverse)
      (env.IsType U) := by
    have := OnCtx.of_append (Γ' := Hs.reverse) (by simpa [List.append_assoc] using hall)
    simpa using this
  obtain ⟨hctx, htel⟩ := minorFields_inst henv hP hM0 hF hFcl F.length (Nat.le_refl _)
  rw [List.take_of_length_le (Nat.le_refl _)] at hctx htel
  rw [List.take_of_length_le (by simp)] at htel
  refine ⟨hctx, ?_⟩
  suffices ∀ j, j ≤ Hs.length → ∃ inh : List VExpr, inh.length = j ∧
      TelInst env U (P ++ F).reverse
        (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs.take j)
        (bvarRange P.length (P.length + F.length) ++
          [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh) by
    obtain ⟨inh, hl, h⟩ := this Hs.length (Nat.le_refl _)
    exact ⟨inh, hl, by rwa [List.take_of_length_le (Nat.le_refl _)] at h⟩
  intro j
  induction j with
  | zero => intro _; exact ⟨[], rfl, by simpa using htel⟩
  | succ j ih =>
    intro hj
    obtain ⟨inh, hl, ht⟩ := ih (Nat.le_of_succ_le hj)
    have hjlt : j < Hs.length := hj
    have hHj := OnCtx.getElem_reverse_append
      (L := P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs) (Γ := [])
      (by rw [List.append_nil]; exact hall) (P.length + 1 + F.length + j) (by simp; omega)
    have hdom : (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs)[
        P.length + 1 + F.length + j]'(by simp; omega) = Hs[j] := by
      rw [List.getElem_append_right (by simp; omega)]
      simp; congr 1; omega
    have htake : (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).take
        (P.length + 1 + F.length + j) =
        P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs.take j := by
      rw [List.take_append, List.take_of_length_le (by simp; omega)]
      simp; omega
    rw [hdom, htake, List.append_nil] at hHj
    obtain ⟨hΔ, u, hu⟩ := hHj
    have hinst := IsDefEq.closed_instOuter_congr henv hctx hΔ hu ht.1 ht.1
      (fun j hj _ hd => ht.2 j hj hd)
    simp only [VExpr.instOuter_sort] at hinst
    obtain ⟨B, xs, hBx⟩ := hshape j hjlt (bvarRange P.length (P.length + F.length) ++
        [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh)
      (by simp [hl]; omega)
      (by rw [List.getElem?_append_left (by simp)]; simp)
    rw [hBx] at hinst
    have hW : Ctx.LiftN (F.length + B.length) 0 P.reverse (B.reverse ++ (P ++ F).reverse) := by
      have := Ctx.LiftN.zero (B.reverse ++ F.reverse) (Γ := P.reverse)
      simpa [Nat.add_comm] using this
    have hH := hM0.weakN henv.ordered hW
    have e := liftN_wrapLams D VExpr.trueTy (F.length + B.length)
    rw [VExpr.trueTy_closed.liftN_eq (Nat.zero_le _)] at e
    rw [e, liftN_wrapForalls] at hH
    simp only [VExpr.liftN] at hH
    rw [e] at hinst
    have ha := HasType.inhabit_trueFamily henv hctx hH ⟨_, hinst⟩
    rw [← e, ← hBx] at ha
    refine ⟨inh ++ [VExpr.wrapLams B VExpr.truePf], by simp [hl], ?_⟩
    rw [List.take_succ_eq_append_getElem hjlt, ← List.append_assoc, ← List.append_assoc]
    exact TelInst.append_one ht ha
theorem lifted_instOuter {e : VExpr} {X Y inh : List VExpr} {M : VExpr}
    (he : e.ClosedN (X.length + Y.length)) :
    ((e.liftN inh.length).liftN 1 (Y.length + inh.length)).instOuter (X ++ [M] ++ Y ++ inh) =
      e.instOuter (X ++ Y) := by
  have h1 := VExpr.liftN_instOuter_drop (e := e.liftN inh.length) (X := X) (Y := [M])
    (Z := Y ++ inh) (by
      have := he.liftN (n := inh.length) (j := 0)
      simpa [Nat.add_assoc] using this)
  simp only [List.length_singleton, List.length_append, List.append_assoc] at h1 ⊢
  rw [h1]
  have h2 := VExpr.liftN_instOuter_drop (e := e) (X := X ++ Y) (Y := inh) (Z := []) (by simpa using he)
  simpa using h2
/-- The minor premise's conclusion, with the motive instantiated and the induction
hypotheses inhabited: the constructor's result indices and the constructor application
instantiate the motive's telescope over the parameter and field variables. -/
theorem minorBody_inst (henv : env.WF) {P F Hs D CI : List VExpr} {ctorApp : VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hM0 : env.HasType U P.reverse (VExpr.wrapLams D VExpr.trueTy)
      (VExpr.wrapForalls D (.sort .zero)))
    (hall : OnCtx (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).reverse
      (env.IsType U))
    (hFcl : ∀ i (h : i < F.length), (F[i]).ClosedN (P.length + i))
    (hshape : ∀ j (hj : j < Hs.length) (args : List VExpr),
      args.length = P.length + 1 + F.length + j →
      args[P.length]? = some ((VExpr.wrapLams D VExpr.trueTy).liftN F.length) →
      ∃ B xs, (Hs[j]).instOuter args =
        VExpr.wrapForalls B (VExpr.mkApps
          ((VExpr.wrapLams D VExpr.trueTy).liftN (F.length + B.length)) xs))
    (hbody : env.IsType U (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).reverse
      (VExpr.mkApps (.bvar (F.length + Hs.length))
        (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
          [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)])))
    (hCIcl : ∀ e ∈ CI, e.ClosedN (P.length + F.length))
    (hccl : ctorApp.ClosedN (P.length + F.length)) :
    OnCtx (P ++ F).reverse (env.IsType U) ∧
    TelInst env U (P ++ F).reverse (P ++ D)
      (bvarRange P.length (P.length + F.length) ++ CI ++ [ctorApp]) := by
  obtain ⟨hctx, inh, hl, htel⟩ := minorHyps_inst henv hP hM0 hall hFcl hshape
  refine ⟨hctx, ?_⟩
  obtain ⟨u, hb⟩ := hbody
  have hinst := IsDefEq.closed_instOuter_congr henv hctx hall hb htel.1 htel.1
    (fun j hj _ hd => htel.2 j hj hd)
  simp only [VExpr.instOuter_sort, VExpr.instOuter_mkApps, List.map_append, List.map_map,
    List.map_cons, List.map_nil, Function.comp_def] at hinst
  have hlen : (bvarRange P.length (P.length + F.length) ++
      [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh).length =
      P.length + 1 + F.length + Hs.length := by simp [hl]; omega
  rw [VExpr.instOuter_bvar _ (by omega)] at hinst
  have hhead : (bvarRange P.length (P.length + F.length) ++
      [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh)[
        (bvarRange P.length (P.length + F.length) ++
      [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh).length
        - 1 - (F.length + Hs.length)]'(by omega) = (VExpr.wrapLams D VExpr.trueTy).liftN F.length := by
    simp only [hlen]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_right (by simp; omega)]
    simp
  rw [hhead] at hinst
  have hlift : ∀ e : VExpr, e.ClosedN (P.length + F.length) →
      ((e.liftN Hs.length).liftN 1 (F.length + Hs.length)).instOuter
        (bvarRange P.length (P.length + F.length) ++
          [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh) = e := by
    intro e he
    have := lifted_instOuter (e := e) (X := bvarRange P.length (P.length + F.length))
      (Y := bvarRange F.length F.length) (inh := inh)
      (M := (VExpr.wrapLams D VExpr.trueTy).liftN F.length) (by simpa using he)
    simp only [bvarRange_length, hl] at this
    rw [this, ← SingletonLayout.bvarRange_split, VExpr.instOuter_range_bvar' _ _ _ he (Nat.le_refl _),
      Nat.sub_self, VExpr.liftN_zero]
  rw [hlift _ hccl, List.map_congr_left (fun e he => hlift e (hCIcl e he)), List.map_id'] at hinst
  -- the instantiated motive's type
  have hMotcl : ∀ j (h : j < (P ++ D).length), ((P ++ D)[j]).ClosedN j := by
    have h := (IsType.wrapForalls_inv henv hP (hM0.isType henv.ordered hP)).1
    exact OnCtx.closed_reverse henv.ordered (by simpa using h)
  have hW : Ctx.LiftN F.length 0 P.reverse (P ++ F).reverse := by
    simpa using Ctx.LiftN.zero (n := F.length) F.reverse (Γ := P.reverse) (by simp)
  have hM := hM0.weakN henv.ordered hW
  rw [liftN_wrapForalls] at hM
  simp only [VExpr.liftN] at hM
  have harity := HasType.mkApps_sort_arity henv hctx hM hinst
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hctx hM ⟨_, hinst⟩ harity
  rw [List.append_assoc]
  refine TelInst.append ?_ (by simpa using harity) ?_
  · have h' : TelInst env U (P ++ F).reverse
        (P ++ ([VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs))
        (bvarRange P.length (P.length + F.length) ++
          ([(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh)) := by
      simpa only [List.append_assoc] using htel
    have := TelInst.take h'
    rwa [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)] at this
  · intro j hj
    have hlenD : (CI ++ [ctorApp]).length = D.length := by simpa using harity
    have hj' : j < (CI ++ [ctorApp]).length := by omega
    have hjm : j < (D.mapIdx fun l d => d.liftN F.length l).length := by simpa using hj
    have := hargs j hj' hjm
    rw [List.getElem_mapIdx] at this
    have hDcl : (D[j]).ClosedN (P.length + j) := by
      have := hMotcl (P.length + j) (by simp; omega)
      rw [List.getElem_append_right (by simp)] at this
      simpa only [Nat.add_sub_cancel_left] using this
    have htl : ((CI ++ [ctorApp]).take j).length = j := by
      rw [List.length_take]; omega
    have e := liftN_instOuter_params (P := P.length) (X := D[j])
      (args := (CI ++ [ctorApp]).take j) (by rw [htl]; exact hDcl) F.length
    rw [htl] at e
    rw [e] at this
    rw [getD_of_lt hj', getD_of_lt hj]
    exact this
theorem instDomains_append (A B : List VExpr) (a : VExpr) (k : Nat) :
    VExpr.instDomains (A ++ B) a k = VExpr.instDomains A a k ++ VExpr.instDomains B a (k + A.length) := by
  induction A generalizing k with
  | nil => simp [VExpr.instDomains]
  | cons d ds ih => simp [VExpr.instDomains, ih, Nat.add_assoc, Nat.add_comm 1]
theorem instDomains_insertBinders (F : List VExpr) (a : VExpr) :
    VExpr.instDomains (insertBinders F 1) a 0 = F := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [VExpr.instDomains_getElem _ _ _ _ (by simpa using h2), getElem_insertBinders (by simpa using h2)]
    simpa using VExpr.inst_liftN (k := i) F[i] a
/-- The minor premise built from a branch over the fields: the induction hypotheses are
abstracted and unused. -/
theorem HasType.minorOf (henv : env.WF) {P F Hs CI : List VExpr} {Mot ctorApp M b : VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hMin : env.IsType U (Mot :: P.reverse)
      (VExpr.wrapForalls (insertBinders F 1 ++ Hs)
        (VExpr.mkApps (.bvar (F.length + Hs.length))
          (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
            [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)]))))
    (hM : env.HasType U P.reverse M Mot)
    (hb : env.HasType U (P ++ F).reverse b (VExpr.mkApps (M.liftN F.length) (CI ++ [ctorApp]))) :
    env.HasType U P.reverse
      (VExpr.wrapLams (VExpr.instDomains (insertBinders F 1 ++ Hs) M 0) (b.liftN Hs.length))
      ((VExpr.wrapForalls (insertBinders F 1 ++ Hs)
        (VExpr.mkApps (.bvar (F.length + Hs.length))
          (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
            [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)]))).inst M 0) := by
  have h1 := IsType.instN henv.ordered .zero hMin hM
  rw [VExpr.wrapForalls_inst] at h1 ⊢
  obtain ⟨hctx, _⟩ := IsType.wrapForalls_inv henv hP h1
  apply HasType.wrapLams_of hctx
  have hbody : (VExpr.mkApps (.bvar (F.length + Hs.length))
          (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
            [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)])).inst M
        (0 + (insertBinders F 1 ++ Hs).length) =
      (VExpr.mkApps (M.liftN F.length) (CI ++ [ctorApp])).liftN Hs.length := by
    simp only [VExpr.inst_mkApps, VExpr.liftN_mkApps, List.length_append, InductiveSignature.Instance.length_insertBinders,
      Nat.zero_add, List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
      VExpr.inst_liftN]
    congr 1
    simp [VExpr.inst, VExpr.instVar, VExpr.liftN_liftN, Nat.add_comm]
  rw [hbody]
  rw [instDomains_append, instDomains_insertBinders] at hctx ⊢
  have hW : Ctx.LiftN Hs.length 0 (P ++ F).reverse
      ((VExpr.instDomains Hs M (0 + (insertBinders F 1).length)).reverse ++ (F.reverse ++ P.reverse)) := by
    have := Ctx.LiftN.zero (n := Hs.length) (VExpr.instDomains Hs M (0 + (insertBinders F 1).length)).reverse
      (Γ := (P ++ F).reverse) (by simp)
    simpa using this
  have := hb.weakN henv.ordered hW
  simpa [List.reverse_append, List.append_assoc] using this
theorem insertBinders_eq_mapIdx (l : List VExpr) (n : Nat) :
    insertBinders l n = l.mapIdx fun k d => d.liftN n k := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i h1 h2; simp [insertBinders]
/-- Instantiating the parameters and the motive of a term over both at the parameter
variables, beneath `r` binders. -/
theorem instOuter_vars_snoc {X M : VExpr} {n : Nat} (hX : X.ClosedN (n + 1)) (r : Nat) :
    X.instOuter (bvarRange n (n + r) ++ [M.liftN r]) = (X.inst M 0).liftN r := by
  rw [VExpr.instOuter_eq_subst, VExpr.liftN_eq_subst (X.inst M 0), VExpr.inst_eq,
    VExpr.subst_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  cases i with
  | zero =>
    rw [VExpr.Subst.ofList_lt _ (by simp)]
    simp [VExpr.Subst.comp, VExpr.Subst.cons, VExpr.liftN_eq_subst]
  | succ j =>
    rw [VExpr.Subst.ofList_lt _ (by simp; omega)]
    rw [List.getElem_append_left (by simp; omega), bvarRange_getElem _ _ _ (by simp; omega)]
    simp only [VExpr.Subst.comp, VExpr.Subst.cons, VExpr.Subst.id, VExpr.subst_bvar,
      VExpr.Subst.shift]
    congr 1; simp; omega
/-- Inserting two arguments, at two inserted binders, into a telescope instance. -/
theorem TelInst.insert2 {A B a b : List VExpr} {X Y x y : VExpr}
    (H : TelInst env U Γ (A ++ B) (a ++ b)) (ha : a.length = A.length)
    (hBcl : ∀ k (h : k < B.length), (B[k]).ClosedN (A.length + k))
    (hx : env.HasType U Γ x (X.instOuter a)) (hy : env.HasType U Γ y (Y.instOuter (a ++ [x]))) :
    TelInst env U Γ (A ++ [X] ++ [Y] ++ B.mapIdx fun k d => d.liftN 2 k)
      (a ++ [x] ++ [y] ++ b) := by
  have hb : b.length = B.length := by have := H.1; simp at this; omega
  have hA : TelInst env U Γ A a := by
    have := H.take
    rwa [List.take_left' ha] at this
  refine TelInst.append (TelInst.append_one (TelInst.append_one hA hx) hy) (by simp [hb]) ?_
  intro k hk
  have hk' : k < B.length := by simpa using hk
  have hkb : k < b.length := by omega
  have := H.2 (A.length + k) (by simp; omega) (by simp; omega)
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by simp)] at this
  rw [List.take_append, List.take_of_length_le (by omega)] at this
  simp only [ha, Nat.add_sub_cancel_left] at this
  rw [getD_of_lt hkb, getD_of_lt hk, List.getElem_mapIdx]
  have htk : (b.take k).length = k := by simp; omega
  have e := VExpr.liftN_instOuter_drop (e := B[k]) (X := a) (Y := [x, y]) (Z := b.take k)
    (by rw [htk, ha]; exact hBcl k hk')
  simp only [List.length_cons, List.length_nil, htk] at e
  have e' : a ++ [x] ++ [y] ++ b.take k = a ++ [x, y] ++ b.take k := by simp
  rw [e', e]
  have hidx : A.length + k - a.length = k := by omega
  simpa [hidx] using this
/-- The recursor applied at the generic motive's providers, with a motive into `Prop` and a
minor premise. -/
theorem HasType.elimApp (henv : env.WF) {P I : List VExpr} {Maj Min h M m : VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hidx : OnCtx (P ++ I ++ [Maj]).reverse (env.IsType U))
    (hMin : env.IsType U (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero) :: P.reverse) Min)
    (hhead : env.HasType U [] h
      (VExpr.wrapForalls (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ [Min] ++
          insertBinders I 2 ++ [Maj.liftN 2 I.length])
        (VExpr.mkApps (.bvar (I.length + 2)) (vars I.length 1 ++ [.bvar 0]))))
    (hM : env.HasType U P.reverse M (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)))
    (hm : env.HasType U P.reverse m (Min.inst M 0)) :
    env.HasType U (Maj :: (P ++ I).reverse)
      (VExpr.mkApps h (bvarRange P.length (P.length + I.length + 1) ++
        [M.liftN (I.length + 1), m.liftN (I.length + 1)] ++
        bvarRange (I.length + 1) (I.length + 1)))
      (VExpr.mkApps (M.liftN (I.length + 1)) (bvarRange (I.length + 1) (I.length + 1))) := by
  have hΓe : OnCtx (Maj :: (P ++ I).reverse) (env.IsType U) := by simpa using hidx
  have hcl := OnCtx.closed_reverse henv.ordered hidx
  have hId := TelInst.ident (env := env) (U := U) [] hcl
  have hN : (P ++ I ++ [Maj]).length = P.length + (I.length + 1) := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hN, SingletonLayout.bvarRange_append P.length (I.length + 1) _ (by omega),
    show P.length + (I.length + 1) - P.length = I.length + 1 by omega,
    ← Nat.add_assoc] at hId
  simp only [List.append_nil] at hId
  have hId' : TelInst env U (Maj :: (P ++ I).reverse) (P ++ (I ++ [Maj]))
      (bvarRange P.length (P.length + I.length + 1) ++ bvarRange (I.length + 1) (I.length + 1)) := by
    simpa [List.append_assoc] using hId
  have hctxP := CtxWF.closed henv.ordered hP
  have hMotcl : (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)).ClosedN P.length := by
    obtain ⟨_, hu⟩ := hM.isType henv.ordered hP
    simpa using hu.closedN henv.ordered hctxP
  have hW : Ctx.LiftN (I.length + 1) 0 P.reverse (Maj :: (P ++ I).reverse) := by
    have := Ctx.LiftN.zero (n := I.length + 1) (Maj :: I.reverse) (Γ := P.reverse) (by simp)
    simpa using this
  have hx : env.HasType U (Maj :: (P ++ I).reverse) (M.liftN (I.length + 1))
      ((VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)).instOuter
        (bvarRange P.length (P.length + I.length + 1))) := by
    rw [VExpr.instOuter_range_bvar' _ _ _ hMotcl (by omega),
      show P.length + I.length + 1 - P.length = I.length + 1 by omega]
    exact hM.weakN henv.ordered hW
  have hMincl : Min.ClosedN (P.length + 1) := by
    obtain ⟨_, hu⟩ := hMin
    have := hu.closedN henv.ordered (CtxWF.closed henv.ordered
      ⟨hP, hM.isType henv.ordered hP⟩)
    simpa using this
  have hy : env.HasType U (Maj :: (P ++ I).reverse) (m.liftN (I.length + 1))
      (Min.instOuter (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)])) := by
    rw [show P.length + I.length + 1 = P.length + (I.length + 1) by omega,
      instOuter_vars_snoc hMincl]
    exact hm.weakN henv.ordered hW
  have hBcl : ∀ k (hk : k < (I ++ [Maj]).length), ((I ++ [Maj])[k]).ClosedN (P.length + k) := by
    intro k hk
    have := hcl (P.length + k) (by simp at hk ⊢; omega)
    simp only [List.append_assoc] at this
    rw [List.getElem_append_right (by simp)] at this
    simpa using this
  have htel := TelInst.insert2 hId' (by simp) hBcl hx hy
  have hins : insertBinders (I ++ [Maj]) 2 = insertBinders I 2 ++ [Maj.liftN 2 I.length] := by
    simp [insertBinders, List.zipIdx_append]
  rw [← insertBinders_eq_mapIdx, hins] at htel
  rw [← List.append_assoc] at htel
  have happ := HasType.mkApps_of_tel (hhead.weak0 henv.ordered) htel
  have hargs : (bvarRange P.length (P.length + I.length + 1) ++
      [M.liftN (I.length + 1), m.liftN (I.length + 1)] ++
      bvarRange (I.length + 1) (I.length + 1)) =
      bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
        [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1) := by simp
  rw [hargs]
  refine (congrArg _ ?_).mp happ
  simp only [VExpr.instOuter_mkApps]
  have hlen : (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
      [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1)).length =
      P.length + I.length + 3 := by simp; omega
  rw [VExpr.instOuter_bvar _ (by omega)]
  have hhd : (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
      [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1))[
        (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
      [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1)).length - 1 -
        (I.length + 2)]'(by omega) = M.liftN (I.length + 1) := by
    simp only [hlen]
    simp only [show P.length + I.length + 3 - 1 - (I.length + 2) = P.length by omega]
    rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
      List.getElem_append_right (by simp)]
    simp
  have hv : vars I.length 1 ++ [VExpr.bvar 0] = bvarRange (I.length + 1) (I.length + 1) := by
    rw [vars_eq_bvarRange, SingletonLayout.bvarRange_append I.length 1 _ (by omega)]
    simp [bvarRange]
  rw [hhd, hv, instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega), hlen,
    show P.length + I.length + 3 - (I.length + 1) = P.length + 2 by omega,
    List.drop_left' (by simp), List.take_of_length_le (by simp)]
/-- The family applied to its parameters and indices, at arguments. -/
theorem instOuter_bvarRange_apps {f : VExpr} (hf : f.ClosedN 0) (args : List VExpr) :
    (VExpr.mkApps f (bvarRange args.length args.length)).instOuter args = VExpr.mkApps f args := by
  rw [VExpr.instOuter_mkApps, instOuter_closed0 hf,
    instOuter_bvarRange _ _ _ (Nat.le_refl _) (Nat.le_refl _)]
  simp
theorem sort_agree (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) {A B : VExpr} {a b : VLevel}
    (hA : env.HasType U Γ A (.sort a)) (hB : env.HasType U Γ B (.sort b))
    (hAB : env.IsDefEqU U Γ A B) : a ≈ b := by
  obtain ⟨T, hT⟩ := hAB
  have h1 := IsDefEq.uniqU henv hΓ hA hT
  have h2 := IsDefEq.uniqU henv hΓ hT hB
  exact IsDefEqU.sort_inv henv hΓ (h1.trans henv hΓ h2)
end VEnv
end Lean4Lean
namespace Lean4Lean
open VExpr VEnv
namespace InductiveSignature
namespace Instance
variable {s : InductiveSignature} (g : Instance s)
theorem hypothesis_shape (hfam : s.families.size = 1) (c : Constructor s.families.size)
    (j : Nat) (hj : j < (g.hypotheses c).length) (args : List VExpr) (M : VExpr)
    (hlen : args.length = s.params.length + 1 + (g.fieldsAt c).length + j)
    (hM : args[s.params.length]? = some (M.liftN (g.fieldsAt c).length)) :
    ∃ B xs, ((g.hypotheses c)[j]).instOuter args =
      VExpr.wrapForalls B (VExpr.mkApps (M.liftN ((g.fieldsAt c).length + B.length)) xs) := by
  have hnf : (g.fieldsAt c).length = c.fields.length := by simp [fieldsAt, fieldTypes]
  have hj' : j < (recursiveFields c).length := by simpa [hypotheses] using hj
  simp only [hypotheses, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, hypothesis]
  rw [VExpr.instOuter_eq_subst, subst_wrapForalls, VExpr.subst_mkApps]
  refine ⟨_, _, congrArg (VExpr.wrapForalls _) (congrArg (fun f => VExpr.mkApps f _) ?_)⟩
  simp only [VExpr.subst_bvar, VExpr.Subst.liftN_apply, List.length_mapIdx]
  have hpos : s.families.size - 1 - (recursiveFields c)[j].2.target.val = 0 := by
    have := (recursiveFields c)[j].2.target.isLt; omega
  simp only [hpos, Nat.add_zero, List.length_map, List.length_zipIdx]
  rw [if_neg (by omega), show c.fields.length + j + (recursiveFields c)[j].2.binders.length -
    (recursiveFields c)[j].2.binders.length = c.fields.length + j by omega,
    VExpr.Subst.ofList_lt _ (by omega)]
  have hidx : args.length - 1 - (c.fields.length + j) = s.params.length := by omega
  simp only [hidx]
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hM
  rw [hM, hnf, VExpr.liftN_liftN]
theorem singletonCast_slot (owner : Fin s.families.size) (c : Constructor s.families.size)
    (sorts : List VLevel) (i : Nat) :
    (g.singletonCast owner c sorts).slot.getD i none =
      if i < (g.fieldsAt c).length then fieldSlot (g.ctorIndicesAt c) (g.fieldsAt c).length i
      else none := by
  simp only [singletonCast]
  split
  · rw [getD_of_lt (by simpa)]; simp
  · rename_i h
    simp [List.getD_eq_getElem?_getD, List.getElem?_range, h]
theorem singleton_fieldsCtx {env : VEnv} (henv : env.WF) (hfam : s.families.size = 1)
    (hcs : s.constructors.size = 1) (owner : Fin s.families.size)
    (index : Fin s.constructors.size) {c : Constructor s.families.size}
    (hc : s.constructors[index] = c) (hown : c.owner = owner)
    (htarget : g.targetLevel = .zero)
    {h : VExpr} (hhead : env.HasType g.uvars [] h (g.recursorType owner)) :
    ∀ i, i ≤ (g.fieldsAt c).length →
      OnCtx (g.params ++ (g.fieldsAt c).take i).reverse (env.IsType g.uvars) := by
  have hPlen : g.params.length = s.params.length := by simp [params]
  have hown0 : c.owner.val = 0 := by
    have := c.owner.isLt; omega
  have hrec := g.recursorType_shape hfam hcs owner index
  rw [hc] at hrec
  rw [g.motive_shape owner htarget, g.minor_shape hfam _ hown0, g.major_lift owner,
    g.constructorApp_shape] at hrec
  have H : env.IsType g.uvars [] (g.recursorType owner) := hhead.isType henv.ordered trivial
  rw [hrec] at H
  have hpeel := (IsType.wrapForalls_inv henv (Γ := []) trivial H).1
  have hpeel2 : OnCtx ((insertBinders (g.indicesAt owner) 2 ++
      [(g.majorType owner).liftN 2 (g.indicesAt owner).length]).reverse ++
      (VExpr.wrapForalls (insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c)
        (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)])) ::
        VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero) ::
        g.params.reverse)) (env.IsType g.uvars) := by
    simpa [List.reverse_append, List.append_assoc] using hpeel
  obtain ⟨hMotCtx, hMinT⟩ := OnCtx.of_append hpeel2
  have ⟨hP, hMotT⟩ := hMotCtx
  have hMotInv := IsType.wrapForalls_inv henv hP hMotT
  have hidx : OnCtx (g.params ++ g.indicesAt owner ++ [g.majorType owner]).reverse
      (env.IsType g.uvars) := by
    simpa [List.append_assoc] using hMotInv.1
  have hM0 := HasType.wrapLams_of hMotInv.1 (HasType.trueTy (env := env) (U := g.uvars))
  have hMinInv := IsType.wrapForalls_inv henv hMotCtx hMinT
  have hall : OnCtx (g.params ++ [VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero)] ++
      insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c).reverse (env.IsType g.uvars) := by
    simpa [List.append_assoc] using hMinInv.1
  have hbody : env.IsType g.uvars (g.params ++
      [VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero)] ++
      insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c).reverse
      (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)])) := by
    simpa [List.append_assoc] using hMinInv.2
  have hIcl : ∀ k (hk : k < (g.indicesAt owner).length),
      ((g.indicesAt owner)[k]).ClosedN (g.params.length + k) := by
    intro k hk
    have := OnCtx.closed_reverse henv.ordered hidx (g.params.length + k) (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)] at this
    simpa using this
  have hallcl := OnCtx.closed_reverse henv.ordered hall
  have hFcl : ∀ i (hi : i < (g.fieldsAt c).length),
      ((g.fieldsAt c)[i]).ClosedN (g.params.length + i) := by
    intro i hi
    have := hallcl (g.params.length + 1 + i) (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp),
      getElem_insertBinders (by simp; omega)] at this
    simp only [List.length_append, List.length_singleton,
      show g.params.length + 1 + i - (g.params.length + 1) = i by omega] at this
    exact VExpr.ClosedN.of_liftN (k := g.params.length + i) (by simpa [Nat.add_right_comm] using this)
      (by omega)
  have hF : OnCtx ((insertBinders (g.fieldsAt c) 1).reverse ++
      VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero) :: g.params.reverse)
      (env.IsType g.uvars) := by
    have := hMinInv.1
    rw [List.reverse_append, List.append_assoc] at this
    exact OnCtx.of_append this
  exact fun i hi => (minorFields_inst henv hP hM0 hF hFcl i hi).1
theorem singletonElim_wf {env : VEnv} (henv : env.WF) (hfam : s.families.size = 1)
    (hcs : s.constructors.size = 1) (owner : Fin s.families.size)
    (index : Fin s.constructors.size) {c : Constructor s.families.size}
    (hc : s.constructors[index] = c) (hown : c.owner = owner)
    (htarget : g.targetLevel = .zero)
    {h : VExpr} (hhead : env.HasType g.uvars [] h (g.recursorType owner))
    (harity : (g.ctorIndicesAt c).length = (g.indicesAt owner).length)
    (hfamHead : ∀ {Γ}, OnCtx Γ (env.IsType g.uvars) → ∃ domains level,
      env.HasType g.uvars Γ (.const s.families[owner].name g.levels)
        (VExpr.wrapForalls domains (.sort level)) ∧ level ≈ .zero)
    {sorts : List VLevel}
    (hprop : ∀ i (hi : i < (g.fieldsAt c).length),
      fieldSlot (g.ctorIndicesAt c) (g.fieldsAt c).length i =
        none →
      env.HasType g.uvars (g.params ++ (g.fieldsAt c).take i).reverse
        (g.fieldsAt c)[i] (.sort .zero))
    (hsorts : ∀ i (hi : i < (g.fieldsAt c).length) k,
      fieldSlot (g.ctorIndicesAt c) (g.fieldsAt c).length i =
        some k →
      env.HasType g.uvars (g.params ++ (g.fieldsAt c).take i).reverse
        (g.fieldsAt c)[i] (.sort (sorts.getD i .zero)))
    (hsortWF : ∀ i, (sorts.getD i .zero).WF g.uvars) :
    PropElim.WF (g.singletonCast owner c sorts) g.params
      (g.singletonElim owner c h) env g.uvars := by
  have hPlen : g.params.length = s.params.length := by simp [params]
  have hown0 : c.owner.val = 0 := by
    have := c.owner.isLt; omega
  have hrec := g.recursorType_shape hfam hcs owner index
  rw [hc] at hrec
  rw [g.motive_shape owner htarget, g.minor_shape hfam _ hown0, g.major_lift owner,
    g.constructorApp_shape] at hrec
  have H : env.IsType g.uvars [] (g.recursorType owner) := hhead.isType henv.ordered trivial
  rw [hrec] at H
  have hpeel := (IsType.wrapForalls_inv henv (Γ := []) trivial H).1
  have hpeel2 : OnCtx ((insertBinders (g.indicesAt owner) 2 ++
      [(g.majorType owner).liftN 2 (g.indicesAt owner).length]).reverse ++
      (VExpr.wrapForalls (insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c)
        (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)])) ::
        VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero) ::
        g.params.reverse)) (env.IsType g.uvars) := by
    simpa [List.reverse_append, List.append_assoc] using hpeel
  obtain ⟨hMotCtx, hMinT⟩ := OnCtx.of_append hpeel2
  have ⟨hP, hMotT⟩ := hMotCtx
  have hMotInv := IsType.wrapForalls_inv henv hP hMotT
  have hidx : OnCtx (g.params ++ g.indicesAt owner ++ [g.majorType owner]).reverse
      (env.IsType g.uvars) := by
    simpa [List.append_assoc] using hMotInv.1
  have hM0 := HasType.wrapLams_of hMotInv.1 (HasType.trueTy (env := env) (U := g.uvars))
  have hMinInv := IsType.wrapForalls_inv henv hMotCtx hMinT
  have hall : OnCtx (g.params ++ [VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero)] ++
      insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c).reverse (env.IsType g.uvars) := by
    simpa [List.append_assoc] using hMinInv.1
  have hbody : env.IsType g.uvars (g.params ++
      [VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero)] ++
      insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c).reverse
      (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)])) := by
    simpa [List.append_assoc] using hMinInv.2
  have hIcl : ∀ k (hk : k < (g.indicesAt owner).length),
      ((g.indicesAt owner)[k]).ClosedN (g.params.length + k) := by
    intro k hk
    have := OnCtx.closed_reverse henv.ordered hidx (g.params.length + k) (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)] at this
    simpa using this
  have hallcl := OnCtx.closed_reverse henv.ordered hall
  have hFcl : ∀ i (hi : i < (g.fieldsAt c).length),
      ((g.fieldsAt c)[i]).ClosedN (g.params.length + i) := by
    intro i hi
    have := hallcl (g.params.length + 1 + i) (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp),
      getElem_insertBinders (by simp; omega)] at this
    simp only [List.length_append, List.length_singleton,
      show g.params.length + 1 + i - (g.params.length + 1) = i by omega] at this
    exact VExpr.ClosedN.of_liftN (k := g.params.length + i) (by simpa [Nat.add_right_comm] using this)
      (by omega)
  have hCIcl : ∀ e ∈ g.ctorIndicesAt c, e.ClosedN (g.params.length + (g.fieldsAt c).length) := by
    intro e he
    obtain ⟨_, hb⟩ := hbody
    have hcl := hb.closedN henv.ordered (CtxWF.closed henv.ordered hall)
    have := (VExpr.ClosedN.mkApps_inv hcl).2 _ (List.mem_append_left _ (List.mem_map_of_mem he))
    simp only [List.length_reverse, List.length_append, List.length_singleton,
      InductiveSignature.Instance.length_insertBinders] at this
    have h1 := VExpr.ClosedN.of_liftN (k := g.params.length + (g.fieldsAt c).length + (g.hypotheses c).length)
      (j := (g.fieldsAt c).length + (g.hypotheses c).length) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this) (by omega)
    exact VExpr.ClosedN.of_liftN (j := 0) (n := (g.hypotheses c).length)
      (k := g.params.length + (g.fieldsAt c).length) h1 (Nat.zero_le _)
  have hshape : ∀ j (hj : j < (g.hypotheses c).length) (args : List VExpr),
      args.length = g.params.length + 1 + (g.fieldsAt c).length + j →
      args[g.params.length]? = some
        ((VExpr.wrapLams (g.indicesAt owner ++ [g.majorType owner]) VExpr.trueTy).liftN
          (g.fieldsAt c).length) →
      ∃ B xs, ((g.hypotheses c)[j]).instOuter args =
        VExpr.wrapForalls B (VExpr.mkApps
          ((VExpr.wrapLams (g.indicesAt owner ++ [g.majorType owner]) VExpr.trueTy).liftN
            ((g.fieldsAt c).length + B.length)) xs) := by
    intro j hj args hl ha
    rw [hPlen] at hl ha
    exact g.hypothesis_shape hfam c j hj args _ hl ha
  have hccl : (g.ctorApp c).ClosedN (g.params.length + (g.fieldsAt c).length) := by
    apply ClosedN.mkApps_closed (show (VExpr.const c.name g.levels).ClosedN _ from trivial)
    intro a ha
    simp only [bvarRange, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    show _ < _
    omega
  obtain ⟨hctxF, hmb⟩ := minorBody_inst henv hP hM0 hall hFcl hshape hbody hCIcl hccl
  rw [← List.append_assoc] at hmb
  -- the constructor indices along the index telescope
  have hCItel : TelInst env g.uvars (g.params ++ g.fieldsAt c).reverse
      (g.params ++ g.indicesAt owner)
      (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++ g.ctorIndicesAt c) := by
    have := hmb.take
    rwa [List.take_append_of_le_length (by simp [harity]), List.take_of_length_le (by simp [harity])]
      at this
  have hMajEq : g.majorType owner = VExpr.mkApps (.const s.families[owner].name g.levels)
      (bvarRange (g.params.length + (g.indicesAt owner).length)
        (g.params.length + (g.indicesAt owner).length)) := by
    have hv := vars_eq_bvarRange (g.indicesAt owner).length 0
    simp only [Nat.add_zero] at hv
    simp only [majorType, indicesAt, List.length_map] at hv ⊢
    rw [SingletonLayout.bvarRange_split, ← vars_eq_bvarRange, ← hv, hPlen]
  have hctorT : env.HasType g.uvars (g.params ++ g.fieldsAt c).reverse (g.ctorApp c)
      (VExpr.mkApps (.const s.families[owner].name g.levels)
        (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++ g.ctorIndicesAt c)) := by
    have hl : (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++
        g.ctorIndicesAt c).length = g.params.length + (g.indicesAt owner).length := by
      simp [harity]
    have := hmb.2 (g.params.length + (g.indicesAt owner).length) (by simp [harity])
      (by simp)
    rw [List.getElem_append_right (by simp [harity]), List.getElem_append_right (by simp)] at this
    simp only [List.length_append, bvarRange_length, harity, Nat.sub_self,
      List.getElem_singleton] at this
    rw [List.take_append_of_le_length (by simp [harity]), List.take_of_length_le (by simp [harity]),
      hMajEq, ← hl, instOuter_bvarRange_apps (f := .const s.families[owner].name g.levels) trivial] at this
    exact this
  have hPcl := OnCtx.closed_reverse henv.ordered hP
  have hF : OnCtx ((insertBinders (g.fieldsAt c) 1).reverse ++
      VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero) :: g.params.reverse)
      (env.IsType g.uvars) := by
    have := hMinInv.1
    rw [List.reverse_append, List.append_assoc] at this
    exact OnCtx.of_append this
  have hfields := minorFields_inst henv hP hM0 hF hFcl
  have hindices : ∀ k, k ≤ (g.indicesAt owner).length →
      OnCtx (g.params ++ (g.indicesAt owner).take k).reverse (env.IsType g.uvars) := by
    intro k _
    have e : (g.params ++ (g.indicesAt owner).take k) ++
        ((g.indicesAt owner).drop k ++ [g.majorType owner]) =
        g.params ++ g.indicesAt owner ++ [g.majorType owner] := by
      rw [List.append_assoc, ← List.append_assoc ((g.indicesAt owner).take k),
        List.take_append_drop, ← List.append_assoc]
    rw [← e, List.reverse_append] at hidx
    exact OnCtx.of_append hidx
  have hslot : ∀ i k, (g.singletonCast owner c sorts).slot.getD i none = some k →
      ∃ hi : i < (g.fieldsAt c).length,
        fieldSlot (g.ctorIndicesAt c) (g.fieldsAt c).length i = some k := by
    intro i k h
    rw [singletonCast_slot] at h
    split at h
    · exact ⟨‹_›, h⟩
    · cases h
  refine {
    typed := {
      scope := ⟨hFcl, hIcl, fun i k h => ?_⟩
      params_closed := hPcl
      fieldsCtx := fun i hi => (hfields i hi).1
      indicesCtx := hindices
      fieldSort := fun i hi => ?_
      slotSort := fun i k h hk => ?_
      sortWF := hsortWF }
    family_closed := trivial
    ctor_closed := trivial
    elimHead_closed := hhead.closedN henv.ordered trivial
    majorTy_typed := ?_
    ctorIndices_length := harity
    ctorIndices_typed := hCItel
    ctor_typed := ?_
    slot_literal := fun l k h => ?_
    elim := fun M b hM hb => ?_ }
  · obtain ⟨_, hk⟩ := hslot i k h
    obtain ⟨hkCI, _⟩ := fieldSlot_spec hk
    simpa [singletonCast, harity] using hkCI
  · have hi' : i < (g.fieldsAt c).length := hi
    show env.HasType _ _ _ (.sort (SingletonLayout.fieldSort _ i))
    unfold SingletonLayout.fieldSort
    rw [singletonCast_slot, if_pos hi']
    cases hfs : fieldSlot (g.ctorIndicesAt c) (g.fieldsAt c).length i with
    | none => exact hprop i hi' hfs
    | some k => exact hsorts i hi' k hfs
  · -- a data field's sort is the sort of its index slot (uniqueness of types)
    obtain ⟨hi, hfs⟩ := hslot i k h
    obtain ⟨hkCI, hCIk⟩ := fieldSlot_spec hfs
    have hk' : k < (g.indicesAt owner).length := hk
    show env.HasType _ (g.params ++ (g.indicesAt owner).take k).reverse (g.indicesAt owner)[k]
      (.sort (sorts.getD i .zero))
    have hctxk := hindices (k + 1) hk'
    rw [List.take_succ_eq_append_getElem hk', ← List.append_assoc, List.reverse_append] at hctxk
    obtain ⟨hctxk', uk, hIk⟩ := hctxk
    -- the index domain at the constructor's indices
    have hpre : TelInst env g.uvars (g.params ++ g.fieldsAt c).reverse
        (g.params ++ (g.indicesAt owner).take k)
        (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++
          (g.ctorIndicesAt c).take k) := by
      have e : g.params ++ g.indicesAt owner =
          (g.params ++ (g.indicesAt owner).take k) ++ (g.indicesAt owner).drop k := by
        rw [List.append_assoc, List.take_append_drop]
      rw [e] at hCItel
      have := hCItel.take
      rwa [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk'),
        List.take_append, List.take_of_length_le (l := bvarRange _ _) (by simp),
        bvarRange_length, Nat.add_sub_cancel_left] at this
    have hIinst := IsDefEq.closed_instOuter_congr henv hctxF hctxk' hIk hpre.1 hpre.1
      (fun j hj _ hd => hpre.2 j hj hd)
    simp only [VExpr.instOuter_sort] at hIinst
    have hent := hCItel.getD (j := g.params.length + k) (by simp; omega)
    rw [getD_append_right' (by simp), getD_append_right' (by simp)] at hent
    simp only [bvarRange_length, Nat.add_sub_cancel_left] at hent
    rw [getD_of_lt hkCI, hCIk, getD_of_lt hk'] at hent
    rw [List.take_append, List.take_of_length_le (l := bvarRange _ _) (by simp), bvarRange_length,
      Nat.add_sub_cancel_left] at hent
    -- the field variable at its declared type
    have hlk := Lookup.reverse_append (g.params ++ g.fieldsAt c) [] (g.params.length + i)
      (by simp; omega)
    rw [List.append_nil, List.getElem_append_right (by simp)] at hlk
    simp only [List.length_append, Nat.add_sub_cancel_left] at hlk
    have hvar : env.HasType g.uvars (g.params ++ g.fieldsAt c).reverse
        (.bvar ((g.fieldsAt c).length - 1 - i))
        (((g.fieldsAt c)[i]).liftN ((g.fieldsAt c).length - i)) := by
      have e1 : g.params.length + (g.fieldsAt c).length - 1 - (g.params.length + i) =
          (g.fieldsAt c).length - 1 - i := by omega
      have e2 : g.params.length + (g.fieldsAt c).length - (g.params.length + i) =
          (g.fieldsAt c).length - i := by omega
      rw [e1, e2] at hlk
      exact .bvar hlk
    have hU := IsDefEq.uniqU henv hctxF hvar hent
    have hFs := hsorts i hi k hfs
    have hW : Ctx.LiftN ((g.fieldsAt c).length - i) 0 (g.params ++ (g.fieldsAt c).take i).reverse
        (g.params ++ g.fieldsAt c).reverse := by
      have e : (g.params ++ g.fieldsAt c).reverse =
          ((g.fieldsAt c).drop i).reverse ++ (g.params ++ (g.fieldsAt c).take i).reverse := by
        conv => lhs; rw [← List.take_append_drop i (g.fieldsAt c)]
        rw [← List.append_assoc, List.reverse_append]
      rw [e]
      exact Ctx.LiftN.zero _ (by simp)
    have hFs' := hFs.weakN henv.ordered hW
    simp only [VLevel.WF, VExpr.liftN] at hFs'
    have heq := sort_agree henv hctxF hFs' hIinst hU
    have hukwf := (hIk.isType henv.ordered hctxk').sort_inv henv.ordered
    exact .defeqDF (.sortDF hukwf (hsortWF i) (show _ ≈ _ from Eq.symm heq)) hIk
  · have e : PropElim.majorTy (g.singletonCast owner c sorts) g.params
        (g.singletonElim owner c h) = g.majorType owner := by
      simp only [PropElim.majorTy, singletonElim, singletonCast]
      rw [← SingletonLayout.bvarRange_split, hMajEq]
    rw [e]
    have hidx' : OnCtx (g.majorType owner :: (g.params ++ g.indicesAt owner).reverse)
        (env.IsType g.uvars) := by simpa using hidx
    obtain ⟨hctxPI, u, hu⟩ := hidx'
    obtain ⟨domains, level, hH, hlev⟩ := hfamHead hctxPI
    rw [hMajEq] at hu ⊢
    have hlen := HasType.mkApps_sort_arity henv hctxPI hH hu
    have hT := (HasType.mkApps_wrapForalls henv hctxPI hH ⟨_, hu⟩ hlen).2
    simp only [VExpr.instOuter_sort] at hT
    have hlwf := (hT.isType henv.ordered hctxPI).sort_inv henv.ordered
    exact .defeqDF (.sortDF hlwf (by simp [VLevel.WF]) hlev) hT
  · have e : PropElim.ctorApp (g.singletonCast owner c sorts) g.params
        (g.singletonElim owner c h) = g.ctorApp c := by
      simp [PropElim.ctorApp, ctorApp, singletonElim, singletonCast, hPlen]
    rw [e]; exact hctorT
  · obtain ⟨_, hfs⟩ := hslot l k h
    obtain ⟨hk, he⟩ := fieldSlot_spec hfs
    show (g.ctorIndicesAt c).getD k default = .bvar ((g.fieldsAt c).length - 1 - l)
    rw [getD_of_lt hk, he]
  · have e1 : PropElim.majorTy (g.singletonCast owner c sorts) g.params
        (g.singletonElim owner c h) = g.majorType owner := by
      simp only [PropElim.majorTy, singletonElim, singletonCast]
      rw [← SingletonLayout.bvarRange_split, hMajEq]
    have e2 : PropElim.ctorApp (g.singletonCast owner c sorts) g.params
        (g.singletonElim owner c h) = g.ctorApp c := by
      simp [PropElim.ctorApp, ctorApp, singletonElim, singletonCast, hPlen]
    simp only [PropElim.motiveType, e1] at hM
    rw [e2] at hb
    rw [e1]
    have hm := HasType.minorOf henv hP hMinT hM hb
    rw [hrec] at hhead
    exact HasType.elimApp henv hP hidx hMinT hhead hM hm
end Instance
end InductiveSignature
end Lean4Lean
