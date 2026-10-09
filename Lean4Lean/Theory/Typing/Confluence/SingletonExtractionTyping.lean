import Lean4Lean.Theory.Typing.EqTyping
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.CaseResultTyping
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.CanonicalEq
import Lean4Lean.Theory.Typing.SingletonExtraction.Congruence
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Std.List
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.LevelSat
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.Formation

set_option linter.unusedSimpArgs false
namespace Lean4Lean
open VExpr
namespace VExpr
theorem liftN_subst_liftN' (e : VExpr) (σ : Subst) (n : Nat) :
    (e.liftN n).subst (σ.liftN n) = (e.subst σ).liftN n := by
  induction n with
  | zero => simp only [Subst.liftN, liftN_zero]
  | succ n ih =>
    rw [liftN_succ, Subst.liftN, lift_subst_lift, ih, ← liftN_succ]
@[simp] theorem castMotive_subst (u X) (τ : Subst) :
    (castMotive u X).subst τ = castMotive u (X.subst τ) := by
  simp only [castMotive, subst, eqApp, lift_subst_lift]
  rfl
@[simp] theorem typeCast_subst (u X Y e x) (τ : Subst) :
    (typeCast u X Y e x).subst τ =
      typeCast u (X.subst τ) (Y.subst τ) (e.subst τ) (x.subst τ) := by
  simp [typeCast, eqRecApp]
end VExpr
namespace SingletonLayout
variable (S : SingletonLayout)
theorem Scoped.mono_pa {S : SingletonLayout} {pa : List VExpr} (H : S.Scoped P) (h : pa.length = P) :
    S.Scoped pa.length :=
  h ▸ H
/-- The cast telescope commutes with substitution of its providers. -/
theorem step_subst {S : SingletonLayout} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (i : Nat) (σ : List VExpr) (hσ : σ.length = i) (τ : Subst) :
    (S.step pa ia i σ).1.subst (τ.liftN i) =
        (S.step (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i (σ.map (fun x : VExpr => x.subst (τ.liftN i)))).1 ∧
      (S.step pa ia i σ).2.subst (τ.liftN (i + 1)) =
        (S.step (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i (σ.map (fun x : VExpr => x.subst (τ.liftN i)))).2 := by
  have hY := instOuter_subst_closed (S.fields.getD i default) (pa.map (fun x : VExpr => x.liftN i) ++ σ)
    (by simpa [hσ] using H.fields_getD i) (τ.liftN i)
  have hpa : (pa.map (fun x : VExpr => x.liftN i)).map (fun x : VExpr => x.subst (τ.liftN i)) =
      (pa.map (fun x : VExpr => x.subst τ)).map (fun x : VExpr => x.liftN i) := by
    simp [List.map_map, Function.comp_def, liftN_subst_liftN']
  unfold step
  cases hs : S.slot.getD i none with
  | none =>
    refine ⟨?_, rfl⟩
    simp only [hY, List.map_append, hpa]
  | some k =>
    have hk := H.slot_lt i k hs
    have hX := instOuter_subst_closed (S.indices.getD k default)
      (pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i))
      (by simpa [hia, Nat.min_eq_left (Nat.le_of_lt hk)] using H.indices_getD k) (τ.liftN i)
    have hia' : ((ia.take k).map (fun x : VExpr => x.liftN i)).map (fun x : VExpr => x.subst (τ.liftN i)) =
        ((ia.map (fun x : VExpr => x.subst τ)).take k).map (fun x : VExpr => x.liftN i) := by
      simp [List.map_map, Function.comp_def, liftN_subst_liftN', List.map_take]
    have hget : ((ia.getD k default).liftN (i + 1)).subst (τ.liftN (i + 1)) =
        ((ia.map (fun x : VExpr => x.subst τ)).getD k default).liftN (i + 1) := by
      rw [liftN_subst_liftN']
      congr 1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hia ▸ hk)]
    refine ⟨?_, ?_⟩
    · simp only [VExpr.eqApp_subst, hY, hX, List.map_append, hpa, hia']
      rfl
    · simp only [VExpr.typeCast_subst, hget]
      simp only [Subst.liftN, lift_subst_lift, hY, hX, List.map_append, hpa, hia']
      rfl
theorem tel_subst {S : SingletonLayout} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (τ : Subst) (i : Nat) :
    (S.tel pa ia i).1.mapIdx (fun l d => d.subst (τ.liftN l)) =
        (S.tel (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i).1 ∧
      (S.tel pa ia i).2.map (fun x : VExpr => x.subst (τ.liftN i)) =
        (S.tel (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) i).2 := by
  induction i with
  | zero => simp [tel]
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlen := (S.tel_length pa ia i).2
    have hstep := step_subst H hia i (S.tel pa ia i).2 hlen τ
    simp only [tel, List.mapIdx_append, List.map_append, List.map_map, ← ih1, ← ih2]
    rw [← hstep.1, ← hstep.2]
    simp only [(S.tel_length pa ia i).1, List.mapIdx_cons, List.mapIdx_nil, Nat.zero_add,
      List.length_mapIdx]
    constructor
    · first | rfl | trivial
    · congr 1
      apply List.map_congr_left
      intro x _
      exact lift_subst_lift
theorem target_subst {S : SingletonLayout} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (τ : Subst) (j : Nat) :
    (S.target pa ia j).subst (τ.liftN j) =
      S.target (pa.map (fun x : VExpr => x.subst τ)) (ia.map (fun x : VExpr => x.subst τ)) j := by
  unfold target
  rw [instOuter_subst_closed _ _ (by simpa [(S.tel_length pa ia j).2] using H.fields_getD j)]
  rw [← (tel_subst H hia τ j).2]
  simp [List.map_map, Function.comp_def, liftN_subst_liftN']
/-- The value of field `l` once the cast binders are instantiated, given the instantiated
values `σ` of the earlier fields and the argument `tl` supplied for field `l`'s binder. -/
def valHat (pa ia : List VExpr) (l : Nat) (σ : List VExpr) (tl : VExpr) : VExpr :=
  match S.slot.getD l none with
  | some k =>
    VExpr.typeCast (S.sorts.getD l .zero)
      ((S.indices.getD k default).instOuter (pa ++ ia.take k))
      ((S.fields.getD l default).instOuter (pa ++ σ)) tl (ia.getD k default)
  | none => tl
/-- The domain of field `l`'s binder once the earlier binders are instantiated. -/
def domHat (pa ia : List VExpr) (l : Nat) (σ : List VExpr) : VExpr :=
  match S.slot.getD l none with
  | some k =>
    VExpr.eqApp (.succ (S.sorts.getD l .zero)) (.sort (S.sorts.getD l .zero))
      ((S.indices.getD k default).instOuter (pa ++ ia.take k))
      ((S.fields.getD l default).instOuter (pa ++ σ))
  | none => (S.fields.getD l default).instOuter (pa ++ σ)
/-- The instantiated cast substitution. -/
def substHat (pa ia : List VExpr) : Nat → List VExpr → List VExpr
  | 0, _ => []
  | i + 1, t => substHat pa ia i (t.take i) ++ [S.valHat pa ia i (substHat pa ia i (t.take i)) (t.getD i default)]
end SingletonLayout
namespace VEnv
variable {env : VEnv} {U : Nat}
/-- Arguments typed along a telescope. -/
def TelInst (env : VEnv) (U : Nat) (Γ doms args : List VExpr) : Prop :=
  args.length = doms.length ∧ ∀ j (hj : j < args.length) (hj' : j < doms.length),
    env.HasType U Γ args[j] (doms[j].instOuter (args.take j))
/-- Instantiating a term typed in a closed context at arguments typed along that context. -/
theorem HasType.closed_instOuter (henv : env.WF)
    {doms : List VExpr} (hΔ : OnCtx doms.reverse (env.IsType U))
    (H : env.HasType U doms.reverse X T) (hargs : TelInst env U Γ doms args) :
    env.HasType U Γ (X.instOuter args) (T.instOuter args) := by
  have hclosed := CtxWF.closed henv.ordered hΔ
  have hX : X.ClosedN doms.reverse.length := (H.closedN' henv.ordered.closed hclosed).1
  have hT : T.ClosedN doms.reverse.length := (H.closedN' henv.ordered.closed hclosed).2.2
  have W := Ctx.LiftN.right hclosed Γ
  have H' := H.weakN henv.ordered W
  rw [hX.liftN_eq (Nat.le_refl _), hT.liftN_eq (Nat.le_refl _)] at H'
  exact IsDefEq.instOuter_telescope henv (doms := doms) (args := args)
    H' hargs.1 hargs.2
theorem subst_liftN_lift (σ : VExpr.Subst) : ∀ l, σ.lift.liftN l = σ.liftN (l + 1)
  | 0 => rfl
  | l + 1 => by simp only [VExpr.Subst.liftN, subst_liftN_lift σ l]
theorem subst_wrapForalls (τ : VExpr.Subst) :
    ∀ (doms : List VExpr) (B : VExpr), (VExpr.wrapForalls doms B).subst τ =
      VExpr.wrapForalls (doms.mapIdx fun l d => d.subst (τ.liftN l)) (B.subst (τ.liftN doms.length))
  | [], B => rfl
  | d :: ds, B => by
    show VExpr.forallE (d.subst τ) ((VExpr.wrapForalls ds B).subst τ.lift) = _
    rw [subst_wrapForalls τ.lift ds B]
    simp only [List.mapIdx_cons, subst_liftN_lift, List.length_cons]
    rfl
theorem subst_wrapLams (τ : VExpr.Subst) :
    ∀ (doms : List VExpr) (B : VExpr), (VExpr.wrapLams doms B).subst τ =
      VExpr.wrapLams (doms.mapIdx fun l d => d.subst (τ.liftN l)) (B.subst (τ.liftN doms.length))
  | [], B => rfl
  | d :: ds, B => by
    show VExpr.lam (d.subst τ) ((VExpr.wrapLams ds B).subst τ.lift) = _
    rw [subst_wrapLams τ.lift ds B]
    simp only [List.mapIdx_cons, subst_liftN_lift, List.length_cons]
    rfl
theorem liftN_eq_subst_shift (e : VExpr) (r j : Nat) :
    e.liftN r j = e.subst ((VExpr.Subst.shift r).liftN j) := by
  have h := VExpr.liftN_subst (e := e) (n := r) (k := j) (σ := VExpr.Subst.id)
  rw [VExpr.subst_id] at h
  rw [h]
  congr 1
  funext i
  simp only [VExpr.Subst.lift_l, VExpr.Subst.id, Lift.liftVar_consN_skipN,
    VExpr.Subst.liftN_apply, VExpr.Subst.shift]
  by_cases hi : i < j
  · rw [liftVar_lt hi, if_pos hi]
  · rw [liftVar_le (Nat.le_of_not_gt hi), if_neg hi]
    simp only [VExpr.liftN, liftVar_base']
    congr 1; omega
theorem liftN_wrapForalls (doms : List VExpr) (B : VExpr) (r : Nat) :
    (VExpr.wrapForalls doms B).liftN r =
      VExpr.wrapForalls (doms.mapIdx fun l d => d.liftN r l) (B.liftN r doms.length) := by
  rw [liftN_eq_subst_shift _ r 0, subst_wrapForalls]
  simp only [VExpr.Subst.liftN, liftN_eq_subst_shift]
theorem liftN_wrapLams (doms : List VExpr) (B : VExpr) (r : Nat) :
    (VExpr.wrapLams doms B).liftN r =
      VExpr.wrapLams (doms.mapIdx fun l d => d.liftN r l) (B.liftN r doms.length) := by
  rw [liftN_eq_subst_shift _ r 0, subst_wrapLams]
  simp only [VExpr.Subst.liftN, liftN_eq_subst_shift]
/-- Instantiating the top binders of a term lifted past them: the lifted parameters become
the variables of the enclosing context. -/
theorem liftN_instOuter_params {X : VExpr} {args : List VExpr} (hX : X.ClosedN (P + args.length))
    (r : Nat) :
    (X.liftN r args.length).instOuter args = X.instOuter (bvarRange P (P + r) ++ args) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  by_cases hik : i < args.length
  · rw [liftVar_lt hik, VExpr.Subst.ofList_lt _ hik, VExpr.Subst.ofList_lt _ (by simp; omega),
      List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hik), VExpr.Subst.ofList_ge _ (by omega),
      VExpr.Subst.ofList_lt _ (by simp; omega), List.getElem_append_left (by simp; omega),
      bvarRange_getElem _ _ _ (by simp; omega)]
    congr 1; simp; omega
theorem liftN_instOuter_take (v : VExpr) (t : List VExpr) (k : Nat) (hk : k ≤ t.length) :
    (v.liftN k).instOuter t = v.instOuter (t.take (t.length - k)) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_eq_subst, VExpr.subst_subst]
  congr 1
  funext x
  simp only [VExpr.Subst.comp, VExpr.Subst.shift, VExpr.subst_bvar]
  by_cases hx : x + k < t.length
  · rw [VExpr.Subst.ofList_lt _ hx, VExpr.Subst.ofList_lt _ (by simp; omega), List.getElem_take]
    congr 1; simp; omega
  · rw [VExpr.Subst.ofList_ge _ (by omega), VExpr.Subst.ofList_ge _ (by simp; omega)]
    congr 1; simp; omega
/-- Instantiating at a concatenation: first the outer arguments beneath the inner binders,
then the inner arguments. -/
theorem instOuter_append_split (X : VExpr) (base t : List VExpr) :
    X.instOuter (base ++ t) =
      (X.subst ((VExpr.Subst.ofList base).liftN t.length)).instOuter t := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.subst_subst]
  congr 1
  funext x
  simp only [VExpr.Subst.comp, VExpr.Subst.liftN_apply]
  by_cases hx : x < t.length
  · rw [if_pos hx, VExpr.subst_bvar, VExpr.Subst.ofList_lt _ hx,
      VExpr.Subst.ofList_lt _ (by simp; omega), List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · rw [if_neg hx, VExpr.instOuter_eq_subst_aux]
    by_cases hb : x - t.length < base.length
    · rw [VExpr.Subst.ofList_lt _ hb, VExpr.Subst.ofList_lt _ (by simp; omega),
        List.getElem_append_left (by simp; omega)]
      congr 1; simp; omega
    · rw [VExpr.Subst.ofList_ge (base ++ t) (by simp; omega), VExpr.Subst.ofList_ge base (by omega)]
      congr 1; simp; omega
theorem instOuter_closed0 {e : VExpr} (h : e.ClosedN 0) (args : List VExpr) :
    e.instOuter args = e := by
  rw [VExpr.instOuter_eq_subst]; exact h.subst_eq .zero
theorem getD_take_lt {l : List α} {d : α} (h : m < i) : (l.take i).getD m d = l.getD m d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]
theorem getD_append_left' {l₁ l₂ : List α} {d : α} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_right' {l₁ l₂ : List α} {d : α} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]
/-- Pointwise definitionally equal arguments along a closed telescope form a
substitution between its context and the target context. -/
theorem substEq_ofTel :
    ∀ {doms args args' : List VExpr}, OnCtx doms.reverse (env.IsType U) →
      args.length = doms.length → args'.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < args'.length) (hd : j < doms.length),
        env.IsDefEq U Γ args[j] args'[j] (doms[j].instOuter (args.take j))) →
      Ctx.SubstEq env U Γ (VExpr.Subst.ofList args) (VExpr.Subst.ofList args') doms.reverse := by
  intro doms
  induction doms using List.snoc_induction with
  | nil => intro _ _ _ _ _ _; exact .nil
  | snoc ds d ih =>
    intro args args' hctx hl hl' hpt
    obtain ⟨as, a, rfl⟩ : ∃ as a, args = as ++ [a] := by
      rcases List.eq_nil_or_concat args with h | ⟨as, a, h⟩
      · subst h; simp at hl
      · exact ⟨as, a, by simpa using h⟩
    obtain ⟨bs, b, rfl⟩ : ∃ bs b, args' = bs ++ [b] := by
      rcases List.eq_nil_or_concat args' with h | ⟨bs, b, h⟩
      · subst h; simp at hl'
      · exact ⟨bs, b, by simpa using h⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl hl'
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at hctx ⊢
    obtain ⟨hctx', _, hd⟩ := hctx
    refine .cons ?_ hd ?_
    · rw [VExpr.Subst.ofList_snoc_tail, VExpr.Subst.ofList_snoc_tail]
      exact ih hctx' hl hl' fun j hj hj' hd' => by
        have := hpt j (by simp; omega) (by simp; omega) (by simp; omega)
        rwa [List.getElem_append_left hj, List.getElem_append_left hj',
          List.getElem_append_left hd', List.take_append_of_le_length (Nat.le_of_lt hj)] at this
    · rw [VExpr.Subst.ofList_snoc_head, VExpr.Subst.ofList_snoc_head,
        VExpr.Subst.ofList_snoc_tail, ← VExpr.instOuter_eq_subst]
      have := hpt as.length (by simp) (by simp; omega) (by simp; omega)
      rw [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (by omega),
        List.getElem_append_right (by omega), List.take_left'] at this
      · simpa [hl, hl'] using this
      all_goals simp [hl, hl']
/-- Congruence of instantiation at pointwise definitionally equal arguments. -/
theorem IsDefEq.closed_instOuter_congr (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {doms : List VExpr} (hΔ : OnCtx doms.reverse (env.IsType U))
    (H : env.IsDefEq U doms.reverse X X' T)
    (hl : args.length = doms.length) (hl' : args'.length = doms.length)
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length) (hd : j < doms.length),
      env.IsDefEq U Γ args[j] args'[j] (doms[j].instOuter (args.take j))) :
    env.IsDefEq U Γ (X.instOuter args) (X'.instOuter args') (T.instOuter args) := by
  have W := substEq_ofTel hΔ hl hl' hpt
  have := IsDefEq.substDF henv.ordered hΔ hΓ W H
  simpa only [VExpr.instOuter_eq_subst] using this
theorem IsDefEq.closed_instOuter_congr' (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {doms : List VExpr} (hΔ : OnCtx doms.reverse (env.IsType U))
    (H : env.IsDefEq U doms.reverse X X' T)
    (hl : args.length = doms.length) (hl' : args'.length = doms.length)
    (hpt : ∀ j, j < doms.length →
      env.IsDefEq U Γ (args.getD j default) (args'.getD j default)
        ((doms.getD j default).instOuter (args.take j))) :
    env.IsDefEq U Γ (X.instOuter args) (X'.instOuter args') (T.instOuter args) :=
  IsDefEq.closed_instOuter_congr henv hΓ hΔ H hl hl' fun j hj hj' hd => by
    have := hpt j hd
    rwa [getD_of_lt hj, getD_of_lt hj', getD_of_lt hd] at this
theorem TelInst.getD (H : TelInst env U Γ doms args) (hj : j < doms.length) :
    env.HasType U Γ (args.getD j default) ((doms.getD j default).instOuter (args.take j)) := by
  rw [getD_of_lt (H.1 ▸ hj), getD_of_lt hj]
  exact H.2 j (H.1 ▸ hj) hj
theorem HasType.wrapLams_of :
    ∀ {doms : List VExpr} {Γ : List VExpr} {body T : VExpr},
      OnCtx (doms.reverse ++ Γ) (env.IsType U) → env.HasType U (doms.reverse ++ Γ) body T →
      env.HasType U Γ (VExpr.wrapLams doms body) (VExpr.wrapForalls doms T)
  | [], _, _, _, _, h => h
  | d :: ds, Γ, body, T, hctx, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx h
    have ⟨_, _, hd⟩ := OnCtx.of_append (Γ' := ds.reverse) hctx
    exact .lam hd (HasType.wrapLams_of hctx h)
theorem HasType.wrapForalls_prop (henv : env.Ordered) :
    ∀ {doms : List VExpr} {Γ : List VExpr} {B : VExpr},
      OnCtx (doms.reverse ++ Γ) (env.IsType U) → env.HasType U (doms.reverse ++ Γ) B (.sort .zero) →
      env.HasType U Γ (VExpr.wrapForalls doms B) (.sort .zero)
  | [], _, _, _, h => h
  | d :: ds, Γ, B, hctx, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx h
    have ⟨hΓ, _, hd⟩ := OnCtx.of_append (Γ' := ds.reverse) hctx
    have hf := HasType.forallE hd (HasType.wrapForalls_prop henv hctx h)
    have hu := (hd.isType henv hΓ).sort_inv henv
    exact .defeqDF (.sortDF (by simp [VLevel.WF]; exact hu) (by simp [VLevel.WF]) VLevel.imax_zero) hf
theorem TelInst.append (HA : TelInst env U Γ A a) (hB : b.length = B.length)
    (hBt : ∀ j, j < B.length →
      env.HasType U Γ (b.getD j default) ((B.getD j default).instOuter (a ++ b.take j))) :
    TelInst env U Γ (A ++ B) (a ++ b) := by
  refine ⟨by simp [HA.1, hB], fun j hj hj' => ?_⟩
  by_cases hja : j < a.length
  · rw [List.getElem_append_left hja, List.getElem_append_left (HA.1 ▸ hja),
      List.take_append_of_le_length (Nat.le_of_lt hja)]
    exact HA.2 j hja (HA.1 ▸ hja)
  · have hm : j - a.length < B.length := by simp at hj'; have := HA.1; omega
    rw [List.getElem_append_right (Nat.le_of_not_gt hja),
      List.getElem_append_right (HA.1 ▸ Nat.le_of_not_gt hja), List.take_append,
      List.take_of_length_le (by omega)]
    have := hBt (j - a.length) hm
    rw [getD_of_lt (by omega), getD_of_lt hm] at this
    simpa [HA.1] using this
theorem TelInst.nil : TelInst env U Γ [] [] := ⟨rfl, fun _ h => by simp at h⟩
theorem TelInst.append_one (H : TelInst env U Γ doms args)
    (ha : env.HasType U Γ a (d.instOuter args)) :
    TelInst env U Γ (doms ++ [d]) (args ++ [a]) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < args.length
  · rw [List.getElem_append_left hlt, List.getElem_append_left (H.1 ▸ hlt),
      List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact H.2 j hlt (H.1 ▸ hlt)
  · have hj' : j = args.length := by omega
    subst hj'
    rw [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (H.1 ▸ Nat.le_refl _)]
    simpa [H.1] using ha
theorem TelInst.take (H : TelInst env U Γ (doms ++ more) args) :
    TelInst env U Γ doms (args.take doms.length) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_take] at hj
  have hjd : j < doms.length := hj'
  have hja : j < args.length := by have := H.1; simp at this; omega
  have := H.2 j hja (by simp; omega)
  rw [List.getElem_append_left hjd] at this
  simpa [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjd)] using this
/-- Weakening a telescope instance beneath new binders. -/
theorem TelInst.weak (henv : env.Ordered) (D : List VExpr)
    (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j)
    (H : TelInst env U Γ doms args) :
    TelInst env U (D ++ Γ) doms (args.map (fun x : VExpr => x.liftN D.length)) := by
  refine ⟨by simp [H.1], fun j hj hj' => ?_⟩
  simp only [List.length_map] at hj
  have h := (H.2 j hj hj').weakN henv (Ctx.LiftN.zero D)
  rw [VExpr.liftN_instOuter _ _ (by simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using hcl j hj')] at h
  simpa [List.map_take] using h
/-- The variables of a closed telescope's own context instantiate it. -/
theorem TelInst.ident (Γ : List VExpr) (hcl : ∀ j (h : j < doms.length), (doms[j]).ClosedN j) :
    TelInst env U (doms.reverse ++ Γ) doms (bvarRange doms.length doms.length) := by
  refine ⟨by simp, fun j hj hj' => ?_⟩
  simp only [bvarRange_length] at hj
  rw [bvarRange_getElem _ _ _ hj, bvarRange_take _ _ _ (Nat.le_of_lt hj),
    VExpr.instOuter_range_bvar' _ _ _ (hcl j hj') (Nat.le_of_lt hj)]
  exact .bvar (Lookup.reverse_append doms Γ j hj')
theorem HasType.mkApps_of_tel
    (hf : env.HasType U Γ f (VExpr.wrapForalls doms B)) (H : TelInst env U Γ doms args) :
    env.HasType U Γ (VExpr.mkApps f args) (B.instOuter args) :=
  IsDefEq.mkApps_congr hf H.1 rfl fun j hj hj' _ => H.2 j hj hj'
/-- A telescope over the parameters, lifted past `r` binders and instantiated at its own
arguments, is the telescope instantiated at the lifted parameters. -/
theorem TelInst.unlift {D : List VExpr} (hcl : ∀ j (h : j < D.length), (D[j]).ClosedN (P + j))
    (hP : params.length = P)
    (H : TelInst env U Γ (params ++ D) (bvarRange P (P + r) ++ args)) :
    TelInst env U Γ (D.mapIdx fun l d => d.liftN r l) args := by
  have hlen : args.length = D.length := by have := H.1; simp [hP] at this; omega
  refine ⟨by simp [hlen], fun j hj hj' => ?_⟩
  have hjD : j < D.length := by simpa using hj'
  have := H.2 (P + j) (by simp; omega) (by simp [hP]; omega)
  rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp [hP])] at this
  rw [List.take_append, List.take_of_length_le (by simp)] at this
  simp only [bvarRange_length, Nat.add_sub_cancel_left, hP] at this
  have htl : (args.take j).length = j := by simp; omega
  have e : (D[j].liftN r j).instOuter (args.take j) =
      D[j].instOuter (bvarRange P (P + r) ++ args.take j) := by
    have := liftN_instOuter_params (P := P) (X := D[j]) (args := args.take j)
      (by rw [htl]; exact hcl j hjD) r
    rwa [htl] at this
  rw [List.getElem_mapIdx, e]
  exact this
end VEnv
namespace SingletonLayout
open VEnv
variable {env : VEnv} {U : Nat}
/-- The sort of field `i`: its declared sort for data, `Prop` for proofs. -/
def fieldSort (S : SingletonLayout) (i : Nat) : VLevel :=
  match S.slot.getD i none with
  | some _ => S.sorts.getD i .zero
  | none => .zero
/-- Typing of a singleton family's closed telescopes, at fixed universe levels. -/
structure Typed (env : VEnv) (U : Nat) (S : SingletonLayout) (params : List VExpr) : Prop where
  scope : S.Scoped params.length
  params_closed : ∀ j (h : j < params.length), (params[j]).ClosedN j
  fieldsCtx : ∀ i, i ≤ S.fields.length →
    OnCtx (params ++ S.fields.take i).reverse (env.IsType U)
  indicesCtx : ∀ k, k ≤ S.indices.length →
    OnCtx (params ++ S.indices.take k).reverse (env.IsType U)
  fieldSort : ∀ i (h : i < S.fields.length),
    env.HasType U (params ++ S.fields.take i).reverse S.fields[i] (.sort (S.fieldSort i))
  slotSort : ∀ i k, S.slot.getD i none = some k → ∀ h : k < S.indices.length,
    env.HasType U (params ++ S.indices.take k).reverse S.indices[k] (.sort (S.sorts.getD i .zero))
  sortWF : ∀ i, (S.sorts.getD i .zero).WF U
theorem Typed.prefix_closed {S : SingletonLayout} (T : S.Typed env U params)
    (hrest : ∀ i (h : i < rest.length), (rest[i]).ClosedN (params.length + i)) :
    ∀ j (h : j < (params ++ rest).length), ((params ++ rest)[j]).ClosedN j := by
  intro j h
  by_cases hj : j < params.length
  · rw [List.getElem_append_left hj]; exact T.params_closed j hj
  · rw [List.getElem_append_right (Nat.le_of_not_gt hj)]
    have := hrest (j - params.length) (by simp at h; omega)
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_gt hj)] at this
/-- The cast telescope is well formed and its substitution is a typed instance of the
field telescope, at any providers typed as parameter and index instances. -/
theorem tel_typed (henv : env.WF) (heq : env.HasCanonicalEq) {S : SingletonLayout}
    (T : S.Typed env U params) (hΔ : OnCtx Δ (env.IsType U))
    (hpa : TelInst env U Δ params pa)
    (hia : TelInst env U Δ (params ++ S.indices) (pa ++ ia)) (hialen : ia.length = S.indices.length) :
    ∀ i, i ≤ S.fields.length →
      OnCtx ((S.tel pa ia i).1.reverse ++ Δ) (env.IsType U) ∧
      TelInst env U ((S.tel pa ia i).1.reverse ++ Δ) (params ++ S.fields.take i)
        (pa.map (fun x : VExpr => x.liftN i) ++ (S.tel pa ia i).2) := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [tel] using And.intro hΔ hpa
  | succ i ih =>
    intro hi
    obtain ⟨hctx, hinst⟩ := ih (Nat.le_of_succ_le hi)
    have hi' : i < S.fields.length := hi
    obtain ⟨hdl, hσl⟩ := S.tel_length pa ia i
    generalize hdoms : (S.tel pa ia i).1 = doms at hctx hinst hdl
    generalize hσ : (S.tel pa ia i).2 = σ at hinst hσl
    have htel : S.tel pa ia (i + 1) =
        (doms ++ [(S.step pa ia i σ).1], σ.map (·.lift) ++ [(S.step pa ia i σ).2]) := by
      simp [tel, hdoms, hσ]
    rw [htel]
    -- the declared type of field `i` at the current substitution
    have hY : env.HasType U (doms.reverse ++ Δ)
        ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ))
        (.sort (S.fieldSort i)) := by
      rw [getD_of_lt hi']
      simpa using HasType.closed_instOuter henv (T.fieldsCtx i (Nat.le_of_lt hi'))
        (T.fieldSort i hi') hinst
    have hfcl : ∀ j (h : j < (params ++ S.fields.take i).length),
        ((params ++ S.fields.take i)[j]).ClosedN j :=
      T.prefix_closed (fun l h => by
        simp only [List.length_take] at h
        rw [List.getElem_take]; exact T.scope.fields l (by omega))
    have hlifts : (pa.map (fun x : VExpr => x.liftN i) ++ σ).map (fun x : VExpr => x.liftN 1) =
        pa.map (fun x : VExpr => x.liftN (i + 1)) ++ σ.map (·.lift) := by
      simp [List.map_map, Function.comp_def, liftN_liftN]
    have hfields : params ++ S.fields.take (i + 1) = (params ++ S.fields.take i) ++ [S.fields[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']; simp
    have hctxEq : (doms ++ [(S.step pa ia i σ).1]).reverse ++ Δ =
        (S.step pa ia i σ).1 :: (doms.reverse ++ Δ) := by simp
    rw [hctxEq, hfields]
    dsimp only
    rw [← List.append_assoc]
    -- the old substitution, weakened beneath the new binder
    have hold := TelInst.weak henv.ordered [(S.step pa ia i σ).1] hfcl hinst
    simp only [List.length_singleton, hlifts] at hold
    have hYl : ∀ D : VExpr, env.HasType U (D :: (doms.reverse ++ Δ))
        ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ)).lift
        (.sort (S.fieldSort i)) := fun D => hY.weak henv.ordered
    have hYeq : ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ)).lift =
        S.fields[i].instOuter (pa.map (fun x : VExpr => x.liftN (i + 1)) ++ σ.map (·.lift)) := by
      rw [getD_of_lt hi']
      show VExpr.liftN 1 _ 0 = _
      rw [VExpr.liftN_instOuter _ _ (by
        simpa [hσl, hpa.1] using T.scope.fields i hi'), hlifts]
    cases hs : S.slot.getD i none with
    | none =>
      have hsort : S.fieldSort i = .zero := by unfold fieldSort; rw [hs]
      rw [hsort] at hY
      have hstep : S.step pa ia i σ =
          ((S.fields.getD i default).instOuter (pa.map (fun x : VExpr => x.liftN i) ++ σ), .bvar 0) := by
        unfold step; rw [hs]
      rw [hstep] at hold ⊢
      refine ⟨⟨hctx, _, hY⟩, ?_⟩
      apply TelInst.append_one hold
      rw [← hYeq]
      exact .bvar .zero
    | some k =>
      have hk := T.scope.slot_lt i k hs
      have hsort : S.fieldSort i = S.sorts.getD i .zero := by unfold fieldSort; rw [hs]
      rw [hsort] at hY
      have hu := T.sortWF i
      -- the index slot's type at the current depth
      have hicl : ∀ j (h : j < (params ++ S.indices).length), ((params ++ S.indices)[j]).ClosedN j :=
        T.prefix_closed (fun l h => T.scope.indices l h)
      have hiw := TelInst.weak henv.ordered doms.reverse hicl hia
      simp only [List.length_reverse, hdl] at hiw
      have hsplit : params ++ S.indices = (params ++ S.indices.take k) ++ S.indices.drop k := by
        simp [List.append_assoc]
      rw [hsplit] at hiw
      have hix := hiw.take
      have htake : ((pa ++ ia).map (fun x : VExpr => x.liftN i)).take
          (params ++ S.indices.take k).length =
          pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i) := by
        simp only [List.map_append, List.take_append, List.length_append, List.length_take,
          ← hpa.1, List.length_map, Nat.min_eq_left (Nat.le_of_lt (hialen ▸ hk)), Nat.add_sub_cancel_left]
        rw [List.take_of_length_le (by simp)]
        simp [List.map_take, hialen]
      rw [htake] at hix
      have hX := HasType.closed_instOuter henv (T.indicesCtx k (Nat.le_of_lt hk))
        (T.slotSort i k hs hk) hix
      simp only [VExpr.instOuter_sort] at hX
      -- the index argument itself, at the current depth
      have hxi : env.HasType U (doms.reverse ++ Δ) ((ia[k]'(hialen ▸ hk)).liftN i)
          (S.indices[k].instOuter
            (pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i))) := by
        have hlenP : (params ++ S.indices.take k).length = params.length + k := by
          simp [Nat.min_eq_left (Nat.le_of_lt hk)]
        have := hiw.2 (params.length + k) (by simp [hpa.1, hialen]; omega)
          (by simp; omega)
        rw [← htake] at *
        simpa [List.getElem_append_right, hpa.1, List.getElem_map, List.getElem_drop,
          Nat.min_eq_left (Nat.le_of_lt hk), List.take_take] using this
      generalize hXdef : S.indices[k].instOuter
        (pa.map (fun x : VExpr => x.liftN i) ++ (ia.take k).map (fun x : VExpr => x.liftN i)) = X
        at hX hxi
      generalize hYdef : (S.fields.getD i default).instOuter
        (pa.map (fun x : VExpr => x.liftN i) ++ σ) = Y at hY hYeq
      have hstep : S.step pa ia i σ =
          (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y,
            VExpr.typeCast (S.sorts.getD i .zero) X.lift Y.lift (.bvar 0)
              ((ia[k]'(hialen ▸ hk)).liftN (i + 1))) := by
        unfold step; rw [hs]
        simp only [← hXdef, ← hYdef, getD_of_lt hk, getD_of_lt (hialen ▸ hk)]
      rw [hstep] at hold ⊢
      have hsu : (VLevel.succ (S.sorts.getD i .zero)).WF U := hu
      have hdom := HasType.eqApp heq hsu (.sort hu) hX hY
      refine ⟨⟨hctx, _, hdom⟩, ?_⟩
      apply TelInst.append_one hold
      rw [← hYeq]
      have hX' := hX.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
        (.sort (S.sorts.getD i .zero)) X Y)
      have hY' := hY.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
        (.sort (S.sorts.getD i .zero)) X Y)
      have he : env.HasType U (VExpr.eqApp (.succ (S.sorts.getD i .zero))
          (.sort (S.sorts.getD i .zero)) X Y :: (doms.reverse ++ Δ)) (.bvar 0)
          (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X.lift Y.lift) := by
        have := IsDefEq.bvar (env := env) (uvars := U) (Lookup.zero (ty := VExpr.eqApp
          (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y)
          (Γ := doms.reverse ++ Δ))
        simpa [VEnv.HasType, VExpr.eqApp, VExpr.liftN] using this
      have hx := hxi.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
        (.sort (S.sorts.getD i .zero)) X Y)
      rw [show ((ia[k]'(hialen ▸ hk)).liftN i).lift = (ia[k]'(hialen ▸ hk)).liftN (i + 1) from
        liftN_liftN ..] at hx
      exact HasType.typeCast henv.ordered heq hu (by simpa [VEnv.HasType, VExpr.liftN] using hX') hY' he hx
theorem getD_lift_append {σ : List VExpr} {val : VExpr} (h : l < σ.length) :
    (σ.map (fun x : VExpr => x.lift) ++ [val]).getD l default = (σ.getD l default).lift := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
theorem getD_lift_append_last {σ : List VExpr} {val : VExpr} :
    (σ.map (fun x : VExpr => x.lift) ++ [val]).getD σ.length default = val := by
  simp [List.getD_eq_getElem?_getD]
theorem take_lift_append {σ : List VExpr} {val : VExpr} (h : l ≤ σ.length) :
    (σ.map (fun x : VExpr => x.lift) ++ [val]).take l = (σ.take l).map (fun x : VExpr => x.lift) := by
  rw [List.take_append_of_le_length (by simpa using h), List.map_take]
theorem bvarRange_append (a b t : Nat) (h : a + b ≤ t) :
    bvarRange (a + b) t = bvarRange a t ++ bvarRange b (t - a) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [bvarRange_length] at h1
    by_cases hj : j < a
    · rw [List.getElem_append_left (by simpa using hj), bvarRange_getElem _ _ _ h1,
        bvarRange_getElem _ _ _ hj]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hj), bvarRange_getElem _ _ _ h1]
      simp only [bvarRange_length]
      rw [bvarRange_getElem _ _ _ (by omega)]
      congr 1; omega
/-- In the constructor branch, where the providers are the parameter variables and the
constructor's own indices, every cast computes: the cast substitution is the field
variables (`K`). -/
theorem tel_branch (henv : env.WF) (heq : env.HasCanonicalEq) {S : SingletonLayout}
    (T : S.Typed env U params)
    (hci : TelInst env U (params ++ S.fields).reverse (params ++ S.indices)
      (bvarRange params.length (params.length + S.fields.length) ++ ci))
    (hcil : ci.length = S.indices.length)
    (hlit : ∀ l k, S.slot.getD l none = some k →
      ci.getD k default = .bvar (S.fields.length - 1 - l)) :
    ∀ i, i ≤ S.fields.length → ∀ l, l < i →
      env.IsDefEq U
        ((S.tel (bvarRange params.length (params.length + S.fields.length)) ci i).1.reverse ++
          (params ++ S.fields).reverse)
        ((S.tel (bvarRange params.length (params.length + S.fields.length)) ci i).2.getD l default)
        (((bvarRange S.fields.length S.fields.length).getD l default).liftN i)
        ((S.fields.getD l default).instOuter
          ((bvarRange params.length (params.length + S.fields.length)).map
              (fun x : VExpr => x.liftN i) ++
            (S.tel (bvarRange params.length (params.length + S.fields.length)) ci i).2.take l)) := by
  generalize hP : params.length = P at *
  have hΔ : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hfcl : ∀ j (h : j < (params ++ S.fields).length), ((params ++ S.fields)[j]).ClosedN j :=
    T.prefix_closed (fun l h => T.scope.fields l h)
  have hid := TelInst.ident (env := env) (U := U) [] hfcl
  simp only [List.append_nil, List.length_append, hP, bvarRange_split] at hid
  have hpa : TelInst env U (params ++ S.fields).reverse params (bvarRange P (P + S.fields.length)) := by
    have := hid.take (doms := params) (more := S.fields)
    simpa [hP] using this
  have htyped := tel_typed henv heq T hΔ hpa (by simpa using hci) hcil
  intro i
  induction i with
  | zero => intro _ l hl; omega
  | succ i ih =>
    intro hi l hl
    have hi' : i < S.fields.length := by omega
    obtain ⟨hctx, hinst⟩ := htyped i (by omega)
    have IH := ih (by omega)
    obtain ⟨hdl, hσl⟩ := S.tel_length (bvarRange P (P + S.fields.length)) ci i
    generalize hdoms : (S.tel (bvarRange P (P + S.fields.length)) ci i).1 = doms at hctx hinst hdl IH
    generalize hσ : (S.tel (bvarRange P (P + S.fields.length)) ci i).2 = σ at hinst hσl IH
    have htel : S.tel (bvarRange P (P + S.fields.length)) ci (i + 1) =
        (doms ++ [(S.step (bvarRange P (P + S.fields.length)) ci i σ).1],
          σ.map (·.lift) ++ [(S.step (bvarRange P (P + S.fields.length)) ci i σ).2]) := by
      simp [tel, hdoms, hσ]
    simp only [htel]
    have hctxEq : (doms ++ [(S.step (bvarRange P (P + S.fields.length)) ci i σ).1]).reverse ++
        (params ++ S.fields).reverse =
        (S.step (bvarRange P (P + S.fields.length)) ci i σ).1 :: (doms.reverse ++ (params ++ S.fields).reverse) := by
      simp
    rw [hctxEq]
    have hplift : (bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN (i + 1)) =
        ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i)).map (·.lift) := by
      simp [List.map_map, Function.comp_def, liftN_liftN]
    rcases Nat.lt_or_ge l i with hli | hli
    · -- an old entry, weakened beneath the new binder
      have h := (IH l hli).weak henv.ordered
        (B := (S.step (bvarRange P (P + S.fields.length)) ci i σ).1)
      rw [getD_lift_append (by omega), take_lift_append (by omega), hplift, ← List.map_append,
        ← VExpr.liftN_instOuter]
      · simpa [VExpr.lift, liftN_liftN] using h
      · have := T.scope.fields_getD l
        rw [hP] at this
        simpa [hσl, Nat.min_eq_left (Nat.le_of_lt hli)] using this
    · have hil : i = l := by omega
      subst hil
      have hr1 : i < (bvarRange S.fields.length S.fields.length).length := by simp; omega
      rw [← hσl, getD_lift_append_last, take_lift_append (Nat.le_refl _), List.take_length, hσl, hplift,
        ← List.map_append, ← VExpr.liftN_instOuter _ _ (by
          have := T.scope.fields_getD (List.length σ); rw [hP] at this; simpa [hσl] using this)]
      have hfv : (bvarRange S.fields.length S.fields.length).getD i default =
          .bvar (S.fields.length - 1 - i) := by
        rw [getD_of_lt hr1, bvarRange_getElem _ _ _ (by omega)]
      rw [hfv]
      -- the declared type of field `i` at the cast substitution
      have hY : env.HasType U (doms.reverse ++ (params ++ S.fields).reverse)
          ((S.fields.getD i default).instOuter
            ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ))
          (.sort (S.fieldSort i)) := by
        rw [getD_of_lt hi']
        simpa using HasType.closed_instOuter henv (T.fieldsCtx i (Nat.le_of_lt hi'))
          (T.fieldSort i hi') hinst
      -- the field variable, typed at its declared type in the base context
      have hfvar : env.HasType U (params ++ S.fields).reverse (.bvar (S.fields.length - 1 - i))
          (S.fields[i].instOuter (bvarRange P (P + S.fields.length) ++
            (bvarRange S.fields.length S.fields.length).take i)) := by
        have := hid.getD (j := P + i) (by simp [hP]; omega)
        rw [getD_append_right' (by simp only [List.length_append, bvarRange_length, hP]; omega),
          getD_append_right' (by simp only [List.length_append, bvarRange_length, hP]; omega),
          List.take_append,
          List.take_of_length_le (by simp only [List.length_append, bvarRange_length, hP]; omega)] at this
        simp only [hP, bvarRange_length, Nat.add_sub_cancel_left] at this
        rw [getD_of_lt hr1, getD_of_lt hi', bvarRange_getElem _ _ _ (by omega)] at this
        exact this
      -- the cast substitution agrees with the field variables so far
      have hcongr : env.IsDefEq U (doms.reverse ++ (params ++ S.fields).reverse)
          ((S.fields.getD i default).instOuter
            ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ))
          (S.fields[i].instOuter
            ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
              ((bvarRange S.fields.length S.fields.length).take i).map (fun x : VExpr => x.liftN i)))
          (.sort (S.fieldSort i)) := by
        rw [getD_of_lt hi']
        have hl : ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ).length =
            (params ++ S.fields.take i).length := by simp [hσl, hP]; try omega
        have hl' : ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
            ((bvarRange S.fields.length S.fields.length).take i).map (fun x : VExpr => x.liftN i)).length =
            (params ++ S.fields.take i).length := by simp [hP]; try omega
        have := IsDefEq.closed_instOuter_congr' henv hctx (T.fieldsCtx i (Nat.le_of_lt hi'))
          (T.fieldSort i hi') hl hl' (fun j hd => by
            have hlenP : ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i)).length = P := by
              simp
            by_cases hjP : j < P
            · rw [getD_append_left' (by rw [hlenP]; omega), getD_append_left' (by rw [hlenP]; omega)]
              have := hinst.getD hd
              rwa [getD_append_left' (by rw [hlenP]; omega)] at this
            · have hm : j - P < i := by simp [hP] at hd; omega
              rw [getD_append_right' (by rw [hlenP]; omega), getD_append_right' (by rw [hlenP]; omega), hlenP]
              have e1 : (params ++ S.fields.take i).getD j default = S.fields.getD (j - P) default := by
                rw [getD_append_right' (by omega), hP, getD_of_lt (by simp; omega),
                  getD_of_lt (by omega), List.getElem_take]
              have e2 : (((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i)) ++ σ).take j =
                  (bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ.take (j - P) := by
                rw [List.take_append, List.take_of_length_le (by rw [hlenP]; omega), hlenP]
              have e3 : (((bvarRange S.fields.length S.fields.length).take i).map
                  (fun x : VExpr => x.liftN i)).getD (j - P) default =
                  ((bvarRange S.fields.length S.fields.length).getD (j - P) default).liftN i := by
                rw [getD_of_lt (by simp; omega), getD_of_lt (by simp; omega), List.getElem_map,
                  List.getElem_take]
              rw [e1, e2, e3]
              exact IH (j - P) hm)
        simpa using this
      have hFeq : S.fields[i].instOuter
            ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
              ((bvarRange S.fields.length S.fields.length).take i).map (fun x : VExpr => x.liftN i)) =
          (S.fields[i].instOuter (bvarRange P (P + S.fields.length) ++
            (bvarRange S.fields.length S.fields.length).take i)).liftN i := by
        rw [VExpr.liftN_instOuter _ _ (by
          have := T.scope.fields i hi'; rw [hP] at this; simpa [Nat.min_eq_left (by omega : i ≤ S.fields.length)] using this),
          List.map_append]
      have hfvar' := hfvar.weakN henv.ordered (Ctx.LiftN.zero doms.reverse)
      simp only [List.length_reverse, hdl] at hfvar'
      rw [← hFeq] at hfvar'
      have hfvY := hcongr.symm.defeq hfvar'
      have hY1 := hY.weak henv.ordered (B := (S.step (bvarRange P (P + S.fields.length)) ci i σ).1)
      have hfv1 := hfvY.weak henv.ordered (B := (S.step (bvarRange P (P + S.fields.length)) ci i σ).1)
      rw [show ((VExpr.bvar (S.fields.length - 1 - i)).liftN i).lift =
          (VExpr.bvar (S.fields.length - 1 - i)).liftN (i + 1) from liftN_liftN ..] at hfv1
      cases hs : S.slot.getD i none with
      | none =>
        have hsort : S.fieldSort i = .zero := by unfold fieldSort; rw [hs]
        have hstep : S.step (bvarRange P (P + S.fields.length)) ci i σ =
            ((S.fields.getD i default).instOuter
              ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ), .bvar 0) := by
          unfold step; rw [hs]
        rw [hsort] at hY1
        rw [hstep] at hY1 hfv1 ⊢
        exact .proofIrrel (by simpa [VExpr.liftN] using hY1) (.bvar .zero) hfv1
      | some k =>
        have hk := T.scope.slot_lt i k hs
        have hsort : S.fieldSort i = S.sorts.getD i .zero := by unfold fieldSort; rw [hs]
        rw [hsort] at hY hY1 hcongr
        have hu := T.sortWF i
        have hlitk := hlit i k hs
        -- the index slot type, at the base and at depth `i`
        have hcik : env.HasType U (params ++ S.fields).reverse (ci.getD k default)
            (S.indices[k].instOuter (bvarRange P (P + S.fields.length) ++ ci.take k)) := by
          have := hci.getD (j := P + k) (by simp [hP]; omega)
          rw [getD_append_right' (by simp [hP]), getD_append_right' (by simp [hP]),
            List.take_append, List.take_of_length_le (by simp)] at this
          simp only [hP, bvarRange_length, Nat.add_sub_cancel_left, Nat.sub_self, List.take_zero,
            List.append_nil] at this
          rwa [getD_of_lt hk] at this
        have hX0 : env.HasType U (params ++ S.fields).reverse
            (S.indices[k].instOuter (bvarRange P (P + S.fields.length) ++ ci.take k))
            (.sort (S.sorts.getD i .zero)) := by
          have hsplit : params ++ S.indices = (params ++ S.indices.take k) ++ S.indices.drop k := by
            simp [List.append_assoc]
          have hc := hci
          rw [hsplit] at hc
          have := HasType.closed_instOuter henv (T.indicesCtx k (Nat.le_of_lt hk))
            (T.slotSort i k hs hk) hc.take
          simpa [List.take_append, hP, List.take_of_length_le, hcil, Nat.min_eq_left (Nat.le_of_lt hk)]
            using this
        have hXlift : (S.indices[k].instOuter (bvarRange P (P + S.fields.length) ++ ci.take k)).liftN i =
            (S.indices.getD k default).instOuter
              ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
                (ci.take k).map (fun x : VExpr => x.liftN i)) := by
          rw [getD_of_lt hk, VExpr.liftN_instOuter _ _ (by
            have := T.scope.indices k hk; rw [hP] at this
            simpa [hcil, Nat.min_eq_left (Nat.le_of_lt hk)] using this), List.map_append]
        have hX := hX0.weakN henv.ordered (Ctx.LiftN.zero doms.reverse)
        have hxX := hcik.weakN henv.ordered (Ctx.LiftN.zero doms.reverse)
        simp only [List.length_reverse, hdl, hXlift] at hX hxX
        rw [hlitk] at hxX
        generalize hXdef : (S.indices.getD k default).instOuter
            ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
              (ci.take k).map (fun x : VExpr => x.liftN i)) = X at hX hxX
        generalize hYdef : (S.fields.getD i default).instOuter
            ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ) = Y
          at hY hY1 hcongr hfvY hfv1 ⊢
        -- `X ≡ Y`: both type the same field variable
        obtain ⟨_, hXY'⟩ := IsDefEq.uniq henv hctx hxX hfvY
        have hXY : env.IsDefEq U (doms.reverse ++ (params ++ S.fields).reverse) X Y
            (.sort (S.sorts.getD i .zero)) := hX.trans_l henv hctx hXY'
        have hstep : S.step (bvarRange P (P + S.fields.length)) ci i σ =
            (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y,
              VExpr.typeCast (S.sorts.getD i .zero) X.lift Y.lift (.bvar 0)
                ((ci.getD k default).liftN (i + 1))) := by
          unfold step; rw [hs]; simp only [hXdef, hYdef]
        rw [hstep, hlitk] at hY1 hfv1 ⊢
        have hsu : (VLevel.succ (S.sorts.getD i .zero)).WF U := hu
        have hdom := HasType.eqApp heq hsu (.sort hu) hX hY
        have hΓ' : OnCtx (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y ::
            (doms.reverse ++ (params ++ S.fields).reverse)) (env.IsType U) := ⟨hctx, _, hdom⟩
        have he : env.HasType U (VExpr.eqApp (.succ (S.sorts.getD i .zero))
            (.sort (S.sorts.getD i .zero)) X Y :: (doms.reverse ++ (params ++ S.fields).reverse)) (.bvar 0)
            (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X.lift Y.lift) := by
          have := IsDefEq.bvar (env := env) (uvars := U) (Lookup.zero (ty := VExpr.eqApp
            (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y)
            (Γ := doms.reverse ++ (params ++ S.fields).reverse))
          simpa [VEnv.HasType, VExpr.eqApp, VExpr.liftN] using this
        have hXY1 := hXY.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
            (.sort (S.sorts.getD i .zero)) X Y)
        have hx1 := hxX.weak henv.ordered (B := VExpr.eqApp (.succ (S.sorts.getD i .zero))
            (.sort (S.sorts.getD i .zero)) X Y)
        rw [show ((VExpr.bvar (S.fields.length - 1 - i)).liftN i).lift =
          (VExpr.bvar (S.fields.length - 1 - i)).liftN (i + 1) from liftN_liftN ..] at hx1
        exact IsDefEq.typeCast_refl henv heq hu hΓ' (by simpa [VExpr.liftN] using hXY1) he hx1
/-- The constructor branch returns field `i` at the cast target. -/
theorem tel_branch_target (henv : env.WF) (heq : env.HasCanonicalEq) {S : SingletonLayout}
    (T : S.Typed env U params)
    (hci : TelInst env U (params ++ S.fields).reverse (params ++ S.indices)
      (bvarRange params.length (params.length + S.fields.length) ++ ci))
    (hcil : ci.length = S.indices.length)
    (hlit : ∀ l k, S.slot.getD l none = some k →
      ci.getD k default = .bvar (S.fields.length - 1 - l))
    (i : Nat) (hi' : i < S.fields.length) :
    env.HasType U
      ((S.tel (bvarRange params.length (params.length + S.fields.length)) ci i).1.reverse ++
        (params ++ S.fields).reverse)
      ((VExpr.bvar (S.fields.length - 1 - i)).liftN i)
      (S.target (bvarRange params.length (params.length + S.fields.length)) ci i) := by
  have IH := tel_branch henv heq T hci hcil hlit i (Nat.le_of_lt hi')
  generalize hP : params.length = P at *
  have hΔ : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hfcl : ∀ j (h : j < (params ++ S.fields).length), ((params ++ S.fields)[j]).ClosedN j :=
    T.prefix_closed (fun l h => T.scope.fields l h)
  have hid := TelInst.ident (env := env) (U := U) [] hfcl
  simp only [List.append_nil, List.length_append, hP, bvarRange_split] at hid
  have hpa : TelInst env U (params ++ S.fields).reverse params (bvarRange P (P + S.fields.length)) := by
    have := hid.take (doms := params) (more := S.fields)
    simpa [hP] using this
  have htyped := tel_typed henv heq T hΔ hpa (by simpa using hci) hcil
  obtain ⟨hctx, hinst⟩ := htyped i (Nat.le_of_lt hi')
  obtain ⟨hdl, hσl⟩ := S.tel_length (bvarRange P (P + S.fields.length)) ci i
  unfold target
  generalize hdoms : (S.tel (bvarRange P (P + S.fields.length)) ci i).1 = doms at hctx hinst hdl IH ⊢
  generalize hσ : (S.tel (bvarRange P (P + S.fields.length)) ci i).2 = σ at hinst hσl IH ⊢
  have hr1 : i < (bvarRange S.fields.length S.fields.length).length := by simp; omega
  -- the field variable, typed at its declared type in the base context
  have hfvar : env.HasType U (params ++ S.fields).reverse (.bvar (S.fields.length - 1 - i))
      (S.fields[i].instOuter (bvarRange P (P + S.fields.length) ++
        (bvarRange S.fields.length S.fields.length).take i)) := by
    have := hid.getD (j := P + i) (by simp [hP]; omega)
    rw [getD_append_right' (by simp only [List.length_append, bvarRange_length, hP]; omega),
      getD_append_right' (by simp only [List.length_append, bvarRange_length, hP]; omega),
      List.take_append,
      List.take_of_length_le (by simp only [List.length_append, bvarRange_length, hP]; omega)] at this
    simp only [hP, bvarRange_length, Nat.add_sub_cancel_left] at this
    rw [getD_of_lt hr1, getD_of_lt hi', bvarRange_getElem _ _ _ (by omega)] at this
    exact this
  -- the cast substitution agrees with the field variables so far
  have hcongr : env.IsDefEq U (doms.reverse ++ (params ++ S.fields).reverse)
      ((S.fields.getD i default).instOuter
        ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ))
      (S.fields[i].instOuter
        ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
          ((bvarRange S.fields.length S.fields.length).take i).map (fun x : VExpr => x.liftN i)))
      (.sort (S.fieldSort i)) := by
    rw [getD_of_lt hi']
    have hl : ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ).length =
        (params ++ S.fields.take i).length := by simp [hσl, hP]; try omega
    have hl' : ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
        ((bvarRange S.fields.length S.fields.length).take i).map (fun x : VExpr => x.liftN i)).length =
        (params ++ S.fields.take i).length := by simp [hP]; try omega
    have := IsDefEq.closed_instOuter_congr' henv hctx (T.fieldsCtx i (Nat.le_of_lt hi'))
      (T.fieldSort i hi') hl hl' (fun j hd => by
        have hlenP : ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i)).length = P := by
          simp
        by_cases hjP : j < P
        · rw [getD_append_left' (by rw [hlenP]; omega), getD_append_left' (by rw [hlenP]; omega)]
          have := hinst.getD hd
          rwa [getD_append_left' (by rw [hlenP]; omega)] at this
        · have hm : j - P < i := by simp [hP] at hd; omega
          rw [getD_append_right' (by rw [hlenP]; omega), getD_append_right' (by rw [hlenP]; omega), hlenP]
          have e1 : (params ++ S.fields.take i).getD j default = S.fields.getD (j - P) default := by
            rw [getD_append_right' (by omega), hP, getD_of_lt (by simp; omega),
              getD_of_lt (by omega), List.getElem_take]
          have e2 : (((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i)) ++ σ).take j =
              (bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++ σ.take (j - P) := by
            rw [List.take_append, List.take_of_length_le (by rw [hlenP]; omega), hlenP]
          have e3 : (((bvarRange S.fields.length S.fields.length).take i).map
              (fun x : VExpr => x.liftN i)).getD (j - P) default =
              ((bvarRange S.fields.length S.fields.length).getD (j - P) default).liftN i := by
            rw [getD_of_lt (by simp; omega), getD_of_lt (by simp; omega), List.getElem_map,
              List.getElem_take]
          rw [e1, e2, e3]
          exact IH (j - P) hm)
    simpa using this

  have hFeq : S.fields[i].instOuter
        ((bvarRange P (P + S.fields.length)).map (fun x : VExpr => x.liftN i) ++
          ((bvarRange S.fields.length S.fields.length).take i).map (fun x : VExpr => x.liftN i)) =
      (S.fields[i].instOuter (bvarRange P (P + S.fields.length) ++
        (bvarRange S.fields.length S.fields.length).take i)).liftN i := by
    rw [VExpr.liftN_instOuter _ _ (by
      have := T.scope.fields i hi'; rw [hP] at this; simpa [Nat.min_eq_left (by omega : i ≤ S.fields.length)] using this),
      List.map_append]
  have hfvar' := hfvar.weakN henv.ordered (Ctx.LiftN.zero doms.reverse)
  simp only [List.length_reverse, hdl] at hfvar'
  rw [← hFeq] at hfvar'
  exact hcongr.symm.defeq hfvar'
theorem typeCast_instOuter (u X Y e x) (t : List VExpr) :
    (VExpr.typeCast u X Y e x).instOuter t =
      VExpr.typeCast u (X.instOuter t) (Y.instOuter t) (e.instOuter t) (x.instOuter t) := by
  simp only [VExpr.instOuter_eq_subst, VExpr.typeCast_subst]
theorem eqApp_instOuter (w α a b) (t : List VExpr) :
    (VExpr.eqApp w α a b).instOuter t =
      VExpr.eqApp w (α.instOuter t) (a.instOuter t) (b.instOuter t) := by
  simp only [VExpr.instOuter_eq_subst, VExpr.eqApp_subst]
theorem liftN_instOuter_self (x : VExpr) (t : List VExpr) : (x.liftN t.length).instOuter t = x := by
  rw [VExpr.instOuter_eq_subst]; exact VExpr.instOuter_eq_subst_aux x t
theorem liftN_instOuter_len {x : VExpr} {t : List VExpr} (h : t.length = k) :
    (x.liftN k).instOuter t = x := by subst h; exact liftN_instOuter_self x t
/-- Instantiating the cast binders of the substitution. -/
theorem tel_instOuter {S : SingletonLayout} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length) :
    ∀ i (t : List VExpr), t.length = i →
      (S.tel pa ia i).2.map (fun x : VExpr => x.instOuter t) = S.substHat pa ia i t := by
  intro i
  induction i with
  | zero => intro t _; simp [tel, substHat]
  | succ i ih =>
    intro t ht
    have hti : (t.take i).length = i := by simp; omega
    have hσl := (S.tel_length pa ia i).2
    simp only [tel, substHat, List.map_append, List.map_map, List.map_cons, List.map_nil]
    have hlift : (S.tel pa ia i).2.map ((fun x : VExpr => x.instOuter t) ∘ (·.lift)) =
        (S.tel pa ia i).2.map (fun x : VExpr => x.instOuter (t.take i)) := by
      apply List.map_congr_left; intro x _
      simp only [Function.comp]
      rw [show x.lift = x.liftN 1 from rfl, liftN_instOuter_take _ _ _ (by omega), ht,
        Nat.add_sub_cancel]
    rw [hlift, ih _ hti]
    congr 2
    have hpai : (pa.map (fun x : VExpr => x.liftN i)).map (fun x : VExpr => x.instOuter (t.take i)) = pa := by
      simp only [List.map_map]
      conv => rhs; rw [← List.map_id pa]
      apply List.map_congr_left; intro x _
      simp only [Function.comp, id]; exact liftN_instOuter_len hti
    unfold step valHat
    cases hs : S.slot.getD i none with
    | none =>
      simp only
      rw [VExpr.instOuter_bvar _ (by omega), getD_of_lt (by omega)]
      congr 1; omega
    | some k =>
      have hk := H.slot_lt i k hs
      simp only
      rw [typeCast_instOuter]
      have hX := H.indices_getD k
      have hY := H.fields_getD i
      congr 1
      · rw [show ∀ x : VExpr, x.lift = x.liftN 1 from fun _ => rfl, liftN_instOuter_take _ _ _ (by omega),
          ht, Nat.add_sub_cancel, VExpr.instOuter_instOuter _ _ _ (by
            simpa [hia, Nat.min_eq_left (Nat.le_of_lt hk)] using hX),
          List.map_append, hpai, List.map_map]
        congr 2
        conv => rhs; rw [← List.map_id (ia.take k)]
        apply List.map_congr_left; intro x _
        simp only [Function.comp, id]; exact liftN_instOuter_len hti
      · rw [show ∀ x : VExpr, x.lift = x.liftN 1 from fun _ => rfl, liftN_instOuter_take _ _ _ (by omega),
          ht, Nat.add_sub_cancel, VExpr.instOuter_instOuter _ _ _ (by simpa [hσl] using hY),
          List.map_append, hpai, ih _ hti]
      · rw [VExpr.instOuter_bvar _ (by omega), getD_of_lt (by omega)]
        congr 1; omega
      · exact liftN_instOuter_len ht
theorem tel_dom_getD (S : SingletonLayout) (pa ia : List VExpr) :
    ∀ i l, l < i → (S.tel pa ia i).1.getD l default = (S.step pa ia l (S.tel pa ia l).2).1 := by
  intro i
  induction i with
  | zero => intro l h; omega
  | succ i ih =>
    intro l hl
    simp only [tel]
    rcases Nat.lt_or_ge l i with h | h
    · rw [getD_append_left' (by rw [(S.tel_length pa ia i).1]; exact h), ih l h]
    · have : l = i := by omega
      subst this
      rw [getD_append_right' (by rw [(S.tel_length pa ia l).1]; exact Nat.le_refl _), (S.tel_length pa ia l).1,
        Nat.sub_self]
      rfl
theorem tel_dom_instOuter {S : SingletonLayout} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (i l : Nat) (hl : l < i) (t : List VExpr) (ht : t.length = l) :
    ((S.tel pa ia i).1.getD l default).instOuter t = S.domHat pa ia l (S.substHat pa ia l t) := by
  rw [S.tel_dom_getD pa ia i l hl]
  have hσl := (S.tel_length pa ia l).2
  have hpai : (pa.map (fun x : VExpr => x.liftN l)).map (fun x : VExpr => x.instOuter t) = pa := by
    simp only [List.map_map]
    conv => rhs; rw [← List.map_id pa]
    apply List.map_congr_left; intro x _
    simp only [Function.comp, id]; exact liftN_instOuter_len ht
  have hY : ((S.fields.getD l default).instOuter (pa.map (fun x : VExpr => x.liftN l) ++
      (S.tel pa ia l).2)).instOuter t =
      (S.fields.getD l default).instOuter (pa ++ S.substHat pa ia l t) := by
    rw [VExpr.instOuter_instOuter _ _ _ (by simpa [hσl] using H.fields_getD l), List.map_append, hpai,
      tel_instOuter H hia l t ht]
  unfold step domHat
  cases hs : S.slot.getD l none with
  | none => exact hY
  | some k =>
    have hk := H.slot_lt l k hs
    simp only
    rw [eqApp_instOuter, hY, VExpr.instOuter_sort]
    congr 1
    rw [VExpr.instOuter_instOuter _ _ _ (by
      simpa [hia, Nat.min_eq_left (Nat.le_of_lt hk)] using H.indices_getD k), List.map_append, hpai,
      List.map_map]
    congr 2
    conv => rhs; rw [← List.map_id (ia.take k)]
    apply List.map_congr_left; intro x _
    simp only [Function.comp, id]; exact liftN_instOuter_len ht
theorem target_instOuter {S : SingletonLayout} (H : S.Scoped pa.length) (hia : ia.length = S.indices.length)
    (j : Nat) (t : List VExpr) (ht : t.length = j) :
    (S.target pa ia j).instOuter t = (S.fields.getD j default).instOuter (pa ++ S.substHat pa ia j t) := by
  have hσl := (S.tel_length pa ia j).2
  unfold target
  rw [VExpr.instOuter_instOuter _ _ _ (by simpa [hσl] using H.fields_getD j), List.map_append,
    tel_instOuter H hia j t ht]
  congr 2
  simp only [List.map_map]
  conv => rhs; rw [← List.map_id pa]
  apply List.map_congr_left; intro x _
  simp only [Function.comp, id]; exact liftN_instOuter_len ht
end SingletonLayout
namespace PropElim
variable (S : SingletonLayout) (params : List VExpr) (E : PropElim)
/-- The constructor applied to the parameters and fields, scoped over both. -/
def ctorApp : VExpr :=
  VExpr.mkApps E.ctor (bvarRange (params.length + S.fields.length) (params.length + S.fields.length))
/-- Motive types, scoped over the parameters. -/
def motiveType : VExpr :=
  VExpr.wrapForalls (S.indices ++ [majorTy S params E]) (.sort .zero)
def valueType (j : Nat) : VExpr :=
  VExpr.wrapForalls (params ++ S.indices ++ [majorTy S params E])
    (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j))
/-- What the family's declaration provides: typing of the major and constructor, literal data
slots, and elimination into `Prop` for any motive and branch. -/
structure WF (env : VEnv) (U : Nat) : Prop where
  typed : S.Typed env U params
  family_closed : E.family.ClosedN 0
  ctor_closed : E.ctor.ClosedN 0
  elimHead_closed : E.elimHead.ClosedN 0
  majorTy_typed : env.HasType U (params ++ S.indices).reverse (PropElim.majorTy S params E) (.sort .zero)
  ctorIndices_length : E.ctorIndices.length = S.indices.length
  ctorIndices_typed : VEnv.TelInst env U (params ++ S.fields).reverse (params ++ S.indices)
    (branchPa S params ++ E.ctorIndices)
  ctor_typed : env.HasType U (params ++ S.fields).reverse (ctorApp S params E)
    (VExpr.mkApps E.family (branchPa S params ++ E.ctorIndices))
  slot_literal : ∀ l k, S.slot.getD l none = some k →
    E.ctorIndices.getD k default = .bvar (S.fields.length - 1 - l)
  elim : ∀ M b, env.HasType U params.reverse M (motiveType S params E) →
    env.HasType U (params ++ S.fields).reverse b
      (VExpr.mkApps (M.liftN S.fields.length) (E.ctorIndices ++ [ctorApp S params E])) →
    env.HasType U (PropElim.majorTy S params E :: (params ++ S.indices).reverse)
      (VExpr.mkApps E.elimHead
        (genericPa S params ++
          [M.liftN (S.indices.length + 1), (E.minorOf M b).liftN (S.indices.length + 1)] ++
          bvarRange (S.indices.length + 1) (S.indices.length + 1)))
      (VExpr.mkApps (M.liftN (S.indices.length + 1))
        (bvarRange (S.indices.length + 1) (S.indices.length + 1)))
open VEnv SingletonLayout in
theorem value_typed (henv : env.WF) (heq : env.HasCanonicalEq) {S : SingletonLayout} {E : PropElim}
    (W : E.WF S params env U) (hj : j < S.fields.length) (hs : S.slot.getD j none = none) :
    env.HasType U [] (value S params E j) (valueType S params E j) := by
  have T := W.typed
  -- the generic context: parameters, indices, major
  have hmcl : (majorTy S params E).ClosedN (params.length + S.indices.length) := by
    have hc := CtxWF.closed henv.ordered (T.indicesCtx S.indices.length (Nat.le_refl _))
    rw [List.take_length] at hc
    have := (W.majorTy_typed.closedN' henv.ordered.closed hc).1
    simpa [Nat.add_comm] using this
  have hΔg : OnCtx (params ++ S.indices ++ [majorTy S params E]).reverse (env.IsType U) := by
    have h1 := T.indicesCtx S.indices.length (Nat.le_refl _)
    rw [List.take_length] at h1
    rw [List.reverse_append]
    exact ⟨h1, _, W.majorTy_typed⟩
  have hgcl : ∀ i (h : i < (params ++ S.indices ++ [majorTy S params E]).length),
      ((params ++ S.indices ++ [majorTy S params E])[i]).ClosedN i := by
    intro i h
    by_cases hi : i < (params ++ S.indices).length
    · rw [List.getElem_append_left hi]
      exact T.prefix_closed (fun l h => T.scope.indices l h) i hi
    · have : i = (params ++ S.indices).length := by simp at h hi ⊢; omega
      subst this
      simpa using hmcl
  have hid := TelInst.ident (env := env) (U := U) [] hgcl
  simp only [List.append_nil, List.length_append, List.length_singleton] at hid
  have hsplit : bvarRange (params.length + S.indices.length + 1)
      (params.length + S.indices.length + 1) =
      genericPa S params ++ genericIa S ++ [.bvar 0] := by
    rw [bvarRange_append _ _ _ (Nat.le_refl _), bvarRange_append _ _ _ (by omega)]
    simp only [genericPa, genericIa, List.append_assoc]
    congr 2
    · simp [bvarRange]; intro a ha; omega
    · simp [bvarRange]
  rw [hsplit] at hid
  have hia : TelInst env U (params ++ S.indices ++ [majorTy S params E]).reverse
      (params ++ S.indices) (genericPa S params ++ genericIa S) := by
    have := hid.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [genericPa, genericIa, List.take_append, List.append_assoc,
      List.take_of_length_le] using this
  have hpa : TelInst env U (params ++ S.indices ++ [majorTy S params E]).reverse
      params (genericPa S params) := by
    have := hia.take (doms := params) (more := S.indices)
    simpa [genericPa] using this
  -- the generic cast telescope and its target
  obtain ⟨hgctx, hginst⟩ := tel_typed henv heq T hΔg hpa hia (by simp [genericIa]) j (Nat.le_of_lt hj)
  have hsort : S.fieldSort j = .zero := by unfold fieldSort; rw [hs]
  have htarget : env.HasType U
      ((S.tel (genericPa S params) (genericIa S) j).1.reverse ++
        (params ++ S.indices ++ [majorTy S params E]).reverse)
      (S.target (genericPa S params) (genericIa S) j) (.sort .zero) := by
    unfold target
    rw [getD_of_lt hj]
    have := HasType.closed_instOuter henv (T.fieldsCtx j (Nat.le_of_lt hj)) (T.fieldSort j hj) hginst
    simpa [hsort] using this
  have hbody := HasType.wrapForalls_prop henv.ordered hgctx htarget
  have hmot : env.HasType U params.reverse (motive S params E j) (motiveType S params E) := by
    unfold motive motiveType
    apply HasType.wrapLams_of (by simpa [List.reverse_append, List.append_assoc] using hΔg)
    simpa [List.reverse_append, List.append_assoc] using hbody
  -- the branch, at the cast target of the constructor
  have hΔb : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using T.fieldsCtx S.fields.length (Nat.le_refl _)
  have hfcl : ∀ i (h : i < (params ++ S.fields).length), ((params ++ S.fields)[i]).ClosedN i :=
    T.prefix_closed (fun l h => T.scope.fields l h)
  have hidb := TelInst.ident (env := env) (U := U) [] hfcl
  simp only [List.append_nil, List.length_append, bvarRange_split] at hidb
  have hpab : TelInst env U (params ++ S.fields).reverse params (branchPa S params) := by
    have := hidb.take (doms := params) (more := S.fields)
    simpa [branchPa] using this
  obtain ⟨hbctx, _⟩ := tel_typed henv heq T hΔb hpab W.ctorIndices_typed W.ctorIndices_length j
    (Nat.le_of_lt hj)
  have hbt := tel_branch_target henv heq T W.ctorIndices_typed W.ctorIndices_length W.slot_literal
    j hj
  have hlv : (VExpr.bvar (S.fields.length - 1 - j)).liftN j = .bvar (S.fields.length - 1) := by
    simp only [VExpr.liftN, liftVar_base']; congr 1; omega
  rw [hlv] at hbt
  have hbr0 : env.HasType U (params ++ S.fields).reverse (branch S params E j)
      (VExpr.wrapForalls (S.tel (branchPa S params) E.ctorIndices j).1
        (S.target (branchPa S params) E.ctorIndices j)) :=
    HasType.wrapLams_of hbctx hbt
  -- the generic body, instantiated at the constructor, is the branch's type
  have hlenb : (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]).length =
      params.length + S.indices.length + 1 := by
    simp [branchPa, W.ctorIndices_length]; omega
  have hpaτ : (genericPa S params).map
      (fun x : VExpr => x.subst (VExpr.Subst.ofList (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]))) =
      branchPa S params := by
    have := VExpr.instOuter_bvarRange params.length (params.length + S.indices.length + 1)
      (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) (by omega) (by rw [hlenb]; omega)
    simp only [← VExpr.instOuter_eq_subst]
    rw [genericPa, this, hlenb, Nat.sub_self, List.drop_zero, List.append_assoc,
      List.take_left' (by simp [branchPa])]
  have hiaτ : (genericIa S).map
      (fun x : VExpr => x.subst (VExpr.Subst.ofList (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]))) =
      E.ctorIndices := by
    have := VExpr.instOuter_bvarRange S.indices.length (S.indices.length + 1)
      (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) (by omega) (by rw [hlenb]; omega)
    simp only [← VExpr.instOuter_eq_subst]
    rw [genericIa, this, hlenb, show params.length + S.indices.length + 1 - (S.indices.length + 1) =
      (branchPa S params).length by simp [branchPa], List.append_assoc, List.drop_left,
      ← W.ctorIndices_length, List.take_left' rfl]
  have hscope : S.Scoped (genericPa S params).length := by simpa [genericPa] using T.scope
  have hBτ : (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
        (S.target (genericPa S params) (genericIa S) j)).instOuter
        (branchPa S params ++ E.ctorIndices ++ [ctorApp S params E]) =
      VExpr.wrapForalls (S.tel (branchPa S params) E.ctorIndices j).1
        (S.target (branchPa S params) E.ctorIndices j) := by
    rw [VExpr.instOuter_eq_subst, subst_wrapForalls, (S.tel_length _ _ j).1,
      target_subst hscope (by simp [genericIa]), (tel_subst hscope (by simp [genericIa]) _ j).1,
      hpaτ, hiaτ]
  -- the motive applied to the constructor is that type
  have hmajI : (majorTy S params E).instOuter (branchPa S params ++ E.ctorIndices) =
      VExpr.mkApps E.family (branchPa S params ++ E.ctorIndices) := by
    have hl : (branchPa S params ++ E.ctorIndices).length = params.length + S.indices.length := by
      simp [branchPa, W.ctorIndices_length]; try omega
    simp only [majorTy]
    simp only [VExpr.instOuter_mkApps, instOuter_closed0 W.family_closed, ← VExpr.mkApps_append]
    rw [List.map_append, VExpr.instOuter_bvarRange _ _ _ (by omega) (by rw [hl]; exact Nat.le_refl _),
      VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by rw [hl]; omega), hl]
    simp [branchPa, List.drop_left' (by simp [branchPa] : (branchPa S params).length = params.length),
      List.take_left' (by simp [branchPa] : (branchPa S params).length = params.length),
      ← W.ctorIndices_length]
  have htel3 : TelInst env U (params ++ S.fields).reverse
      (params ++ (S.indices ++ [majorTy S params E]))
      (branchPa S params ++ (E.ctorIndices ++ [ctorApp S params E])) := by
    have := W.ctorIndices_typed.append_one (d := majorTy S params E) (a := ctorApp S params E)
      (by rw [hmajI]; exact W.ctor_typed)
    simpa [List.append_assoc] using this
  have hDcl : ∀ i (h : i < (S.indices ++ [majorTy S params E]).length),
      ((S.indices ++ [majorTy S params E])[i]).ClosedN (params.length + i) := by
    intro i h
    by_cases hi : i < S.indices.length
    · rw [List.getElem_append_left hi]; exact T.scope.indices i hi
    · have : i = S.indices.length := by simp at h; omega
      subst this; simpa using hmcl
  have hD := TelInst.unlift (r := S.fields.length) hDcl rfl htel3
  have hmotW := hmot.weakN henv.ordered (Ctx.LiftN.zero S.fields.reverse)
  simp only [List.length_reverse, motiveType, liftN_wrapForalls] at hmotW
  rw [← List.reverse_append] at hmotW
  have hT' := HasType.mkApps_of_tel (by simpa [VExpr.liftN] using hmotW) hD
  simp only [VExpr.instOuter_sort] at hT'
  have hBcl : (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j)).ClosedN
      (params.length + (S.indices ++ [majorTy S params E]).length) := by
    have hc := CtxWF.closed henv.ordered hΔg
    have := (hbody.closedN' henv.ordered.closed hc).1
    simp only [List.length_reverse, List.length_append, List.length_singleton] at this
    simp only [List.length_append, List.length_singleton]
    rwa [show params.length + (S.indices.length + 1) = params.length + S.indices.length + 1 by omega]
  have hbeta := VExpr.WF.beta_wrapLams henv hΔb
    (domains := (S.indices ++ [majorTy S params E]).mapIdx fun l d => d.liftN S.fields.length l)
    (args := E.ctorIndices ++ [ctorApp S params E])
    (body := (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j)).liftN S.fields.length
        (S.indices ++ [majorTy S params E]).length)
    (by simp [W.ctorIndices_length])
    (by
      have := hT'
      rw [show motive S params E j = VExpr.wrapLams (S.indices ++ [majorTy S params E])
        (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
          (S.target (genericPa S params) (genericIa S) j)) from rfl, liftN_wrapLams] at this
      exact ⟨_, this⟩)
  have hR : ((VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j)).liftN S.fields.length
        (S.indices ++ [majorTy S params E]).length).instOuter (E.ctorIndices ++ [ctorApp S params E]) =
      VExpr.wrapForalls (S.tel (branchPa S params) E.ctorIndices j).1
        (S.target (branchPa S params) E.ctorIndices j) := by
    rw [show (S.indices ++ [majorTy S params E]).length = (E.ctorIndices ++ [ctorApp S params E]).length by
        simp [W.ctorIndices_length],
      liftN_instOuter_params (by have := hBcl; simpa [W.ctorIndices_length] using this),
      ← List.append_assoc]
    exact hBτ
  rw [hR] at hbeta
  have hb : env.HasType U (params ++ S.fields).reverse (branch S params E j)
      (VExpr.mkApps ((motive S params E j).liftN S.fields.length)
        (E.ctorIndices ++ [ctorApp S params E])) := by
    have h := IsDefEqU.defeqDF henv hΔb (IsDefEqU.symm hbeta) hbr0
    rw [show motive S params E j = VExpr.wrapLams (S.indices ++ [majorTy S params E])
        (VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
          (S.target (genericPa S params) (genericIa S) j)) from rfl, liftN_wrapLams]
    exact h
  -- the eliminator application has the motive's body as its type
  have helim := W.elim _ _ hmot hb
  have hΔg' : OnCtx (majorTy S params E :: (params ++ S.indices).reverse) (env.IsType U) := by
    simpa [List.reverse_append] using hΔg
  have hres := HasType.projectionMotive_result henv hΔg'
    (domains := S.indices ++ [majorTy S params E])
    (body := VExpr.wrapForalls (S.tel (genericPa S params) (genericIa S) j).1
      (S.target (genericPa S params) (genericIa S) j))
    (by simpa [motive] using helim)
  unfold value valueType
  apply HasType.wrapLams_of (by simpa using hΔg)
  simpa [List.reverse_append, List.append_assoc, motive] using hres
open VEnv SingletonLayout in
/-- At an occurrence aligned with some typed field instance `f`, the reconstructed fields are
a typed field instance, definitionally equal to `f` field by field. -/
theorem occ_typed (henv : env.WF) (heq : env.HasCanonicalEq) {S : SingletonLayout} {E : PropElim}
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U)) (hpsl : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f))
    (halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Γ (f.getD l default) (idx.getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l))) :
    ∀ i, i ≤ S.fields.length →
      TelInst env U Γ (S.tel ps idx i).1 (occ S params E ps idx m i).1 ∧
      TelInst env U Γ (params ++ S.fields.take i) (ps ++ (occ S params E ps idx m i).2) ∧
      (∀ l, l < i → env.IsDefEq U Γ ((occ S params E ps idx m i).2.getD l default) (f.getD l default)
        ((S.fields.getD l default).instOuter (ps ++ (occ S params E ps idx m i).2.take l))) ∧
      (∀ l, l < i → env.IsDefEq U Γ ((occ S params E ps idx m i).2.getD l default)
        ((S.substHat ps idx i (occ S params E ps idx m i).1).getD l default)
        ((S.fields.getD l default).instOuter (ps ++ (occ S params E ps idx m i).2.take l))) := by
  have T := W.typed
  have h1' := hargs.1
  have h2' := hf.1
  simp only [List.length_append, List.length_singleton] at h1' h2'
  have hidxl : idx.length = S.indices.length := by omega
  have hfl : f.length = S.fields.length := by omega
  have hpsT : TelInst env U Γ params ps := by
    have := (show TelInst env U Γ (params ++ (S.indices ++ [majorTy S params E]))
      (ps ++ (idx ++ [m])) by simpa [List.append_assoc] using hargs).take
    simpa [hpsl] using this
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simpa [tel, occ] using TelInst.nil, by simpa [occ] using hpsT, ?_, ?_⟩ <;>
      intro l hl <;> omega
  | succ i ih =>
    intro hi
    have hi' : i < S.fields.length := hi
    obtain ⟨h1, h2, h3, h4⟩ := ih (Nat.le_of_lt hi')
    obtain ⟨htl, hcl⟩ := occ_length S params E ps idx m i
    generalize ht : (occ S params E ps idx m i).1 = t at h1 h2 h3 h4 htl
    generalize hc : (occ S params E ps idx m i).2 = c at h1 h2 h3 h4 hcl
    have hσl : (S.substHat ps idx i t).length = i := by
      rw [← tel_instOuter (T.scope.mono_pa hpsl) hidxl i t htl]; simp [(S.tel_length _ _ i).2]
    -- the field type at the instantiated cast data, at the reconstruction and at `f`
    have hfs := T.fieldSort i hi'
    have hcongr : ∀ (a : List VExpr), a.length = i →
        (∀ l, l < i → env.IsDefEq U Γ (c.getD l default) (a.getD l default)
          ((S.fields.getD l default).instOuter (ps ++ c.take l))) →
        env.IsDefEq U Γ (S.fields[i].instOuter (ps ++ c)) (S.fields[i].instOuter (ps ++ a))
          (.sort (S.fieldSort i)) := by
      intro a hal hpt
      have := IsDefEq.closed_instOuter_congr' henv hΓ (T.fieldsCtx i (Nat.le_of_lt hi')) hfs
        (args := ps ++ c) (args' := ps ++ a)
        (by simp [hpsl, hcl, Nat.min_eq_left (Nat.le_of_lt hi')])
        (by simp [hpsl, hal, Nat.min_eq_left (Nat.le_of_lt hi')]) (fun j hj => by
          by_cases hjP : j < params.length
          · rw [getD_append_left' (by omega), getD_append_left' (by omega)]
            have := h2.getD hj
            rwa [getD_append_left' (by omega)] at this
          · have hm : j - params.length < i := by
              simp [Nat.min_eq_left (Nat.le_of_lt hi')] at hj; omega
            rw [getD_append_right' (by omega), getD_append_right' (by omega), hpsl,
              getD_append_right' (by omega), getD_take_lt hm, List.take_append,
              List.take_of_length_le (by omega), hpsl]
            exact hpt _ hm)
      simpa using this
    have hYc := hcongr (S.substHat ps idx i t) hσl (fun l hl => h4 l hl)
    have hFc := hcongr (f.take i) (by simp; omega) (fun l hl => by
      rw [getD_take_lt hl]
      exact h3 l hl)
    have hfi : env.HasType U Γ (f.getD i default) (S.fields[i].instOuter (ps ++ f.take i)) := by
      have := hf.getD (j := params.length + i) (by simp; omega)
      rw [getD_append_right' (by omega), getD_append_right' (by omega), List.take_append,
        List.take_of_length_le (by omega), hpsl, Nat.add_sub_cancel_left,
        getD_of_lt (l := S.fields) hi'] at this
      exact this
    -- list bookkeeping for the extended reconstruction
    have hgetc : ∀ (x : VExpr) l, l < i → (c ++ [x]).getD l default = c.getD l default :=
      fun x l hl => getD_append_left' (by omega)
    have htakec : ∀ (x : VExpr) l, l ≤ i → (c ++ [x]).take l = c.take l :=
      fun x l hl => List.take_append_of_le_length (by omega)
    have hlastc : ∀ x : VExpr, (c ++ [x]).getD i default = x := fun x => by
      rw [getD_append_right' (by omega), hcl, Nat.sub_self]; rfl
    have hsubst : ∀ x : VExpr, S.substHat ps idx (i + 1) (t ++ [x]) =
        S.substHat ps idx i t ++ [S.valHat ps idx i (S.substHat ps idx i t) x] := fun x => by
      simp only [substHat]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        getD_append_right' (by omega), htl, Nat.sub_self]
      rfl
    have hfields : params ++ S.fields.take (i + 1) = (params ++ S.fields.take i) ++ [S.fields[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']; simp
    have htel : (S.tel ps idx (i + 1)).1 = (S.tel ps idx i).1 ++ [(S.step ps idx i (S.tel ps idx i).2).1] := by
      simp [tel]
    have hdom : ((S.step ps idx i (S.tel ps idx i).2).1).instOuter t =
        S.domHat ps idx i (S.substHat ps idx i t) := by
      have := tel_dom_instOuter (T.scope.mono_pa hpsl) hidxl (i + 1) i (by omega) t htl
      rwa [htel, getD_append_right' (by rw [(S.tel_length _ _ i).1]; exact Nat.le_refl _), (S.tel_length _ _ i).1,
        Nat.sub_self] at this
    cases hs : S.slot.getD i none with
    | some k =>
      have hk := T.scope.slot_lt i k hs
      have hsort : S.fieldSort i = S.sorts.getD i .zero := by unfold fieldSort; rw [hs]
      have hu := T.sortWF i
      rw [hsort] at hYc hFc
      -- the index and its type
      have hidxPre : ∀ k', k' ≤ S.indices.length →
          TelInst env U Γ (params ++ S.indices.take k') (ps ++ idx.take k') := by
        intro k' hk'
        have h0 := (show TelInst env U Γ (params ++ (S.indices ++ [majorTy S params E]))
          (ps ++ (idx ++ [m])) by simpa [List.append_assoc] using hargs)
        have hsplit : params ++ (S.indices ++ [majorTy S params E]) =
            (params ++ S.indices.take k') ++ (S.indices.drop k' ++ [majorTy S params E]) := by
          rw [List.append_assoc, ← List.append_assoc (List.take k' S.indices) (List.drop k' S.indices),
            List.take_append_drop]
        rw [hsplit] at h0
        have := h0.take
        simpa [List.take_append, hpsl, Nat.min_eq_left hk', hidxl,
          Nat.sub_eq_zero_of_le hk', List.take_of_length_le (show ps.length ≤ params.length + k' by omega)]
          using this
      have hidxT := hidxPre k (Nat.le_of_lt hk)
      have hX := HasType.closed_instOuter henv (T.indicesCtx k (Nat.le_of_lt hk))
        (T.slotSort i k hs hk) hidxT
      simp only [VExpr.instOuter_sort] at hX
      have hidxk : env.HasType U Γ (idx.getD k default)
          ((S.indices.getD k default).instOuter (ps ++ idx.take k)) := by
        have := (hidxPre (k + 1) hk).getD (j := params.length + k) (by simp; omega)
        rw [getD_append_right' (by omega), getD_append_right' (by omega), hpsl, Nat.add_sub_cancel_left,
          getD_take_lt (by omega), getD_take_lt (by omega), List.take_append,
          List.take_of_length_le (by omega), hpsl, Nat.add_sub_cancel_left,
          List.take_take, Nat.min_eq_left (by omega)] at this
        exact this
      rw [getD_of_lt hk] at hidxk
      generalize hXd : S.indices[k].instOuter (ps ++ idx.take k) = X at hX hidxk
      generalize hYd : S.fields[i].instOuter (ps ++ S.substHat ps idx i t) = Y at hYc
      -- `X ≡ Y`: the index's type and the cast field type both type the aligned field
      have hal := halign i k hs
      rw [getD_of_lt (l := S.fields) hi'] at hal
      obtain ⟨_, hXF⟩ := IsDefEq.uniq henv hΓ hidxk hal.symm.hasType.1
      have hXY : env.IsDefEq U Γ X Y (.sort (S.sorts.getD i .zero)) :=
        ((hX.trans_l henv hΓ hXF).trans hFc.symm).trans hYc
      have hsu : (VLevel.succ (S.sorts.getD i .zero)).WF U := hu
      have hrefl : env.HasType U Γ (VExpr.eqReflApp (.succ (S.sorts.getD i .zero))
          (.sort (S.sorts.getD i .zero)) X)
          (VExpr.eqApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X Y) :=
        (IsDefEq.eqApp_r heq hsu (.sort hu) hX hXY).defeq (HasType.eqReflApp heq hsu (.sort hu) hX)
      have hocc : occ S params E ps idx m (i + 1) =
          (t ++ [VExpr.eqReflApp (.succ (S.sorts.getD i .zero)) (.sort (S.sorts.getD i .zero)) X],
            c ++ [idx.getD k default]) := by
        simp only [occ, ht, hc, hs, getD_of_lt hk, hXd]
      rw [hocc, hsubst]
      have hxc : env.HasType U Γ (idx.getD k default) (S.fields[i].instOuter (ps ++ c)) :=
        ((hX.trans_l henv hΓ hXF).trans hFc.symm).defeq hidxk
      have hσl' := hσl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [htel]
        apply h1.append_one
        rw [hdom]
        unfold domHat
        rw [hs]
        simp only [getD_of_lt hk, hXd, getD_of_lt (l := S.fields) hi', hYd]
        exact hrefl
      · rw [hfields]
        simpa only [List.append_assoc] using h2.append_one hxc
      · intro l hl
        rcases Nat.lt_or_ge l i with hli | hli
        · rw [hgetc _ l hli, htakec _ l (Nat.le_of_lt hli)]
          exact h3 l hli
        · have : l = i := by omega
          subst this
          rw [hlastc, htakec _ _ (Nat.le_refl _), List.take_of_length_le (by omega),
            getD_of_lt (l := S.fields) hi']
          exact .defeqDF hFc.symm hal.symm
      · intro l hl
        rcases Nat.lt_or_ge l i with hli | hli
        · rw [hgetc _ l hli, htakec _ l (Nat.le_of_lt hli), getD_append_left' (by omega)]
          exact h4 l hli
        · have : l = i := by omega
          subst this
          rw [hlastc, htakec _ _ (Nat.le_refl _), List.take_of_length_le (by omega),
            getD_append_right' (by omega), hσl, Nat.sub_self, getD_of_lt (l := S.fields) hi']
          show env.IsDefEq U Γ _ ([S.valHat ps idx l (S.substHat ps idx l t) _].getD 0 default) _
          simp only [List.getD_cons_zero]
          unfold valHat
          rw [hs]
          simp only [getD_of_lt hk, hXd, getD_of_lt (l := S.fields) hi', hYd]
          have hK := IsDefEq.typeCast_refl henv heq hu hΓ hXY hrefl hidxk
          exact .defeqDF hYc.symm hK.symm
    | none =>
      have hsort : S.fieldSort i = .zero := by unfold fieldSort; rw [hs]
      rw [hsort] at hYc hFc
      -- the extraction function at the occurrence
      have hval := value_typed params henv heq W hi' hs
      have hvcl := hval.closedN' henv.ordered.closed (Γ := []) trivial
      have hvalΓ := hval.weakN henv.ordered (Ctx.LiftN.zero Γ)
      simp only [List.append_nil] at hvalΓ
      rw [hvcl.1.liftN_eq (Nat.zero_le _), hvcl.2.2.liftN_eq (Nat.zero_le _)] at hvalΓ
      unfold valueType at hvalΓ
      rw [← VExpr.wrapForalls_append] at hvalΓ
      have hbl : (ps ++ idx ++ [m]).length = params.length + S.indices.length + 1 := by
        simp [hpsl, hidxl]; try omega
      have hpaτ : (genericPa S params).map
          (fun x : VExpr => x.subst (VExpr.Subst.ofList (ps ++ idx ++ [m]))) = ps := by
        have := VExpr.instOuter_bvarRange params.length (params.length + S.indices.length + 1)
          (ps ++ idx ++ [m]) (by omega) (by rw [hbl]; exact Nat.le_refl _)
        simp only [← VExpr.instOuter_eq_subst]
        rw [genericPa, this, hbl, Nat.sub_self, List.drop_zero, List.append_assoc,
          List.take_left' hpsl]
      have hiaτ : (genericIa S).map
          (fun x : VExpr => x.subst (VExpr.Subst.ofList (ps ++ idx ++ [m]))) = idx := by
        have := VExpr.instOuter_bvarRange S.indices.length (S.indices.length + 1)
          (ps ++ idx ++ [m]) (by omega) (by rw [hbl]; omega)
        simp only [← VExpr.instOuter_eq_subst]
        rw [genericIa, this, hbl, show params.length + S.indices.length + 1 - (S.indices.length + 1) =
          ps.length by omega, List.append_assoc, List.drop_left, List.take_left' hidxl]
      have hscope : S.Scoped (genericPa S params).length := by simpa [genericPa] using T.scope
      have hgia : (genericIa S).length = S.indices.length := by simp [genericIa]
      have htelS := (tel_subst hscope hgia (VExpr.Subst.ofList (ps ++ idx ++ [m])) i).1
      rw [hpaτ, hiaτ] at htelS
      have hglen := (S.tel_length (genericPa S params) (genericIa S) i).1
      have hargsT : TelInst env U Γ
          ((params ++ S.indices ++ [majorTy S params E]) ++ (S.tel (genericPa S params) (genericIa S) i).1)
          ((ps ++ idx ++ [m]) ++ t) := by
        apply TelInst.append hargs (by rw [htl, hglen])
        intro j hj
        rw [hglen] at hj
        have hj' := h1.getD (j := j) (by rw [(S.tel_length ps idx i).1]; exact hj)
        rw [instOuter_append_split, show (t.take j).length = j by simp; omega]
        have hd : ((S.tel (genericPa S params) (genericIa S) i).1.getD j default).subst
            ((VExpr.Subst.ofList (ps ++ idx ++ [m])).liftN j) = (S.tel ps idx i).1.getD j default := by
          rw [← htelS, getD_of_lt (by rw [hglen]; omega), getD_of_lt (by rw [List.length_mapIdx, hglen]; omega),
            List.getElem_mapIdx]
        rw [hd]
        exact hj'
      have hci := HasType.mkApps_of_tel hvalΓ hargsT
      rw [instOuter_append_split, htl, target_subst hscope hgia, hpaτ, hiaτ,
        target_instOuter (T.scope.mono_pa hpsl) hidxl i t htl] at hci
      generalize hcid : VExpr.mkApps (value S params E i) (ps ++ idx ++ [m] ++ t) = ci at hci
      have hocc : occ S params E ps idx m (i + 1) = (t ++ [ci], c ++ [ci]) := by
        simp only [occ, ht, hc, hs, hcid]
      rw [hocc, hsubst]
      rw [getD_of_lt (l := S.fields) hi'] at hci
      have hcic : env.HasType U Γ ci (S.fields[i].instOuter (ps ++ c)) := hYc.symm.defeq hci
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [htel]
        apply h1.append_one
        rw [hdom]
        unfold domHat
        rw [hs, getD_of_lt (l := S.fields) hi']
        exact hci
      · rw [hfields]
        simpa only [List.append_assoc] using h2.append_one hcic
      · intro l hl
        rcases Nat.lt_or_ge l i with hli | hli
        · rw [hgetc _ l hli, htakec _ l (Nat.le_of_lt hli)]
          exact h3 l hli
        · have : l = i := by omega
          subst this
          rw [hlastc, htakec _ _ (Nat.le_refl _), List.take_of_length_le (by omega),
            getD_of_lt (l := S.fields) hi']
          exact .proofIrrel hYc.hasType.1 hcic (hFc.symm.defeq hfi)
      · intro l hl
        rcases Nat.lt_or_ge l i with hli | hli
        · rw [hgetc _ l hli, htakec _ l (Nat.le_of_lt hli), getD_append_left' (by omega)]
          exact h4 l hli
        · have : l = i := by omega
          subst this
          rw [hlastc, htakec _ _ (Nat.le_refl _), List.take_of_length_le (by omega),
            getD_append_right' (by omega), hσl, Nat.sub_self, getD_of_lt (l := S.fields) hi']
          show env.IsDefEq U Γ _ ([S.valHat ps idx l (S.substHat ps idx l t) _].getD 0 default) _
          simp only [List.getD_cons_zero]
          unfold valHat
          rw [hs]
          exact hcic
theorem mkApps_instOuter_heads {head : VExpr} (hc : head.ClosedN 0) (a b : List VExpr)
    (P n : Nat) (ha : a.length = P) (hb : b.length = n) :
    (VExpr.mkApps head (bvarRange P (P + n) ++ bvarRange n n)).instOuter (a ++ b) =
      VExpr.mkApps head (a ++ b) := by
  have hl : (a ++ b).length = P + n := by simp [ha, hb]
  simp only [VExpr.instOuter_mkApps, VEnv.instOuter_closed0 hc]
  rw [List.map_append, VExpr.instOuter_bvarRange _ _ _ (by omega) (by rw [hl]; exact Nat.le_refl _),
    VExpr.instOuter_bvarRange _ _ _ (Nat.le_refl _) (by rw [hl]; omega), hl]
  simp [Nat.add_sub_cancel, List.drop_left' ha, List.take_left' ha, ← hb]
open VEnv SingletonLayout in
/-- **Singleton eta.** A proof of an aligned instance of a large-eliminating singleton
proposition is definitionally its constructor applied to the parameters and the
reconstructed fields: data read from the indices, proofs extracted from the major itself. -/
theorem singleton_eta (henv : env.WF) (heq : env.HasCanonicalEq) {S : SingletonLayout} {E : PropElim}
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U)) (hpsl : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f))
    (halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Γ (f.getD l default) (idx.getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)))
    (hidx : ∀ k, k < S.indices.length →
      env.IsDefEq U Γ (idx.getD k default) ((E.ctorIndices.getD k default).instOuter (ps ++ f))
        ((S.indices.getD k default).instOuter (ps ++ idx.take k))) :
    env.IsDefEq U Γ m
      (VExpr.mkApps E.ctor (ps ++ (occ S params E ps idx m S.fields.length).2))
      ((majorTy S params E).instOuter (ps ++ idx)) := by
  have T := W.typed
  have h1' := hargs.1
  have h2' := hf.1
  simp only [List.length_append, List.length_singleton] at h1' h2'
  have hidxl : idx.length = S.indices.length := by omega
  have hfl : f.length = S.fields.length := by omega
  obtain ⟨_, h2, h3, _⟩ := occ_typed params (Γ := Γ) henv heq W hΓ hpsl hargs hf halign
    S.fields.length (Nat.le_refl _)
  rw [List.take_length] at h2
  have hcl := (occ_length S params E ps idx m S.fields.length).2
  generalize (occ S params E ps idx m S.fields.length).2 = c at h2 h3 hcl ⊢
  have hΔb := T.fieldsCtx S.fields.length (Nat.le_refl _)
  rw [List.take_length] at hΔb
  -- the constructor at the reconstructed fields
  have hcI := HasType.closed_instOuter henv hΔb W.ctor_typed h2
  have hctorEq : (ctorApp S params E).instOuter (ps ++ c) = VExpr.mkApps E.ctor (ps ++ c) := by
    unfold ctorApp
    rw [bvarRange_split]
    exact mkApps_instOuter_heads W.ctor_closed ps c params.length S.fields.length hpsl hcl
  have hfamEq : ∀ a : List VExpr, a.length = S.fields.length →
      (VExpr.mkApps E.family (branchPa S params ++ E.ctorIndices)).instOuter (ps ++ a) =
        VExpr.mkApps E.family (ps ++ E.ctorIndices.map (·.instOuter (ps ++ a))) := by
    intro a hal
    have hl : (ps ++ a).length = params.length + S.fields.length := by simp [hpsl, hal]
    simp only [VExpr.instOuter_mkApps, VEnv.instOuter_closed0 W.family_closed, List.map_append,
      branchPa]
    rw [VExpr.instOuter_bvarRange _ _ _ (by omega) (by rw [hl]; exact Nat.le_refl _), hl,
      Nat.sub_self, List.drop_zero, List.take_left' hpsl]
  rw [hctorEq, hfamEq c hcl] at hcI
  -- the constructor's type at `c` is its type at `f`
  obtain ⟨uT, hTy⟩ := W.ctor_typed.isType henv.ordered hΔb
  have hcf := IsDefEq.closed_instOuter_congr' henv hΓ hΔb hTy
    (args := ps ++ c) (args' := ps ++ f) (by simp [hpsl, hcl]) (by simp [hpsl, hfl])
    (fun j hj => by
      by_cases hjP : j < params.length
      · rw [getD_append_left' (by omega), getD_append_left' (by omega)]
        have := h2.getD hj
        rwa [getD_append_left' (by omega)] at this
      · have hm : j - params.length < S.fields.length := by simp at hj; omega
        rw [getD_append_right' (by omega), getD_append_right' (by omega), hpsl,
          getD_append_right' (by omega), List.take_append, List.take_of_length_le (by omega), hpsl]
        exact h3 _ hm)
  rw [hfamEq c hcl, hfamEq f hfl, VExpr.instOuter_sort] at hcf
  -- the major's type at `idx` is its type at the constructor's indices
  have hidxT : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := (show TelInst env U Γ ((params ++ S.indices) ++ [majorTy S params E]) ((ps ++ idx) ++ [m])
      from hargs).take
    rwa [List.length_append, ← hpsl, ← hidxl, ← List.length_append,
      List.take_left' rfl] at this
  have hΔi := T.indicesCtx S.indices.length (Nat.le_refl _)
  rw [List.take_length] at hΔi
  have hmc := IsDefEq.closed_instOuter_congr' henv hΓ hΔi W.majorTy_typed
    (args := ps ++ idx) (args' := ps ++ E.ctorIndices.map (·.instOuter (ps ++ f)))
    (by simp [hpsl, hidxl]) (by simp [hpsl, W.ctorIndices_length])
    (fun j hj => by
      by_cases hjP : j < params.length
      · rw [getD_append_left' (by omega), getD_append_left' (by omega)]
        have := hidxT.getD hj
        rwa [getD_append_left' (by omega)] at this
      · have hm : j - params.length < S.indices.length := by simp at hj; omega
        rw [getD_append_right' (by omega), getD_append_right' (by omega), hpsl,
          getD_append_right' (by omega), List.take_append, List.take_of_length_le (by omega), hpsl]
        have e : (E.ctorIndices.map (fun x => x.instOuter (ps ++ f))).getD (j - params.length) default =
            (E.ctorIndices.getD (j - params.length) default).instOuter (ps ++ f) := by
          rw [getD_of_lt (by simp [W.ctorIndices_length]; exact hm), List.getElem_map,
            getD_of_lt (by rw [W.ctorIndices_length]; exact hm)]
        rw [e]
        exact hidx _ hm)
  rw [VExpr.instOuter_sort, majorTy, mkApps_instOuter_heads W.family_closed ps
    (E.ctorIndices.map (·.instOuter (ps ++ f))) params.length S.indices.length hpsl
    (by simp [W.ctorIndices_length])] at hmc
  -- proof irrelevance
  have hm : env.HasType U Γ m ((majorTy S params E).instOuter (ps ++ idx)) := by
    have := hargs.getD (j := params.length + S.indices.length) (by simp)
    rw [getD_append_right' (by simp [hpsl, hidxl]), List.take_append_of_le_length (by simp [hpsl, hidxl]),
      List.take_of_length_le (by simp [hpsl, hidxl])] at this
    simpa [hpsl, hidxl] using this
  have hP := HasType.closed_instOuter henv hΔi W.majorTy_typed hidxT
  simp only [VExpr.instOuter_sort] at hP
  have hctorM : env.HasType U Γ (VExpr.mkApps E.ctor (ps ++ c))
      ((majorTy S params E).instOuter (ps ++ idx)) := by
    exact (hcf.trans_l henv hΓ hmc.symm).defeq hcI
  exact .proofIrrel hP hm hctorM
end PropElim
end Lean4Lean
