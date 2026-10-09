import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Theory.Typing.ProjectionFamilyArity
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.Environment.QuotCoherence
import Lean4Lean.Std.List

/-!
# Recursor reduction

`reduceRecursor` reduces quotient eliminators and inductive recursors whose major premise is (or
converts to) a constructor application. Both are refinements of the stored equations of the abstract
environment: `VIotaRuleShape.iota_body` instantiates a stored rule at the actual arguments, and
`Quot.ind` reduces by proof irrelevance.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem Expr.isAppOfArity_three_eq_true {e : Expr} {name : Name}
    (H : e.isAppOfArity name 3 = true) :
    ∃ levels a₁ a₂ a₃, e = .app (.app (.app (.const name levels) a₁) a₂) a₃ := by
  cases e <;> simp [Expr.isAppOfArity] at H
  case app f a₃ =>
    cases f <;> simp [Expr.isAppOfArity] at H
    case app g a₂ =>
      cases g <;> simp [Expr.isAppOfArity] at H
      case app h a₁ =>
        cases h <;> simp [Expr.isAppOfArity] at H
        case const found levels =>
          subst found
          exact ⟨levels, a₁, a₂, a₃, rfl⟩

namespace TypeChecker

/-- Every visible recursor of the checking environment is aligned with the abstract
environment (the `recursors` field of the context). -/
theorem VContext.recursorRules (c : VContext) :
    RecursorRulesCoherent c.safety c.env.constants c.venv :=
  c.recursors.rules

/-- When quotients are initialized, the abstract environment contains the quotient constants and
the `Quot.lift` equation (the `quot` field of the context). -/
theorem VContext.quotCoherent (c : VContext) (h : c.env.quotInit = true) :
    QuotCoherent c.venv :=
  (c.quot h).coherent

namespace Inner

variable {c : VContext} {s : State}

theorem TrExprS.app_of_wf (hf : c.TrExprS f f') (ha : c.TrExprS a a')
    (hwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (.app f' a')) :
    c.TrExprS (.app f a) (.app f' a') :=
  have ⟨_, _, h1, h2⟩ := hwf.app_inv c.Ewf.ordered c.Δwf.toCtx
  .app h1 h2 hf ha

/-- Assemble a translated application spine from translated pieces, given that the abstract spine
is well formed. -/
theorem TrExprS.mkAppList_of_wf : ∀ {args : List Expr} {args' : List VExpr} {f : Expr} {f' : VExpr},
    c.TrExprS f f' → List.Forall₂ c.TrExprS args args' →
    VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (VExpr.mkApps f' args') →
    c.TrExprS (f.mkAppList args) (VExpr.mkApps f' args')
  | [], _, _, _, hf, .nil, _ => hf
  | _ :: _, _, f, f', hf, .cons ha has, hwf =>
    have hwf' := VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx (f := .app f' _) hwf
    TrExprS.mkAppList_of_wf (f := .app f _) (f' := .app f' _) (TrExprS.app_of_wf hf ha hwf') has
      hwf

/-- The translated arguments of a constant application, indexed like the executable argument
array. -/
theorem AppStack.argsGet {e : Expr} {args' : List VExpr}
    (hargs : List.Forall₂ c.TrExprS e.getAppArgsList args') :
    e.getAppArgs.size = args'.length ∧
    ∀ i (hi : i < e.getAppArgs.size), c.TrExprS e.getAppArgs[i] (args'[i]'(by
      rw [← (Lean4Lean.List.Forall₂.length_eq hargs), ← Expr.getAppArgs_toList]; simpa using hi)) := by
  have hlen : e.getAppArgs.size = args'.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hargs, ← Expr.getAppArgs_toList, Array.length_toList]
  refine ⟨hlen, fun i hi => ?_⟩
  have := Lean4Lean.List.forall₂_getElem hargs i (by rw [← Expr.getAppArgs_toList]; simpa using hi)
    (by omega)
  simpa [← Expr.getAppArgs_toList] using this

/-- Free variables of the result of `mkAppRange` over a suffix of the argument array. -/
theorem mkAppRange_suffix_eq {e r : Expr} {i : Nat} (h : i ≤ e.getAppArgs.size) :
    mkAppRange r i e.getAppArgs.size e.getAppArgs = r.mkAppList (e.getAppArgsList.drop i) := by
  refine Expr.mkAppRange_eq (l₁ := e.getAppArgsList.take i) (l₃ := []) ?_ ?_ ?_
  · rw [Expr.getAppArgs_toList, List.append_nil, List.take_append_drop]
  · rw [List.length_take, ← Expr.getAppArgs_toList, Array.length_toList, Nat.min_eq_left h]
  · rw [List.take_append_drop, ← Expr.getAppArgs_toList, Array.length_toList]

theorem _root_.Lean4Lean.VExpr.instOuter_app_bvar (A : List VExpr) (i j : Nat)
    (hi : i < A.length) (hj : j < A.length) :
    (VExpr.app (.bvar i) (.bvar j)).instOuter A = .app A[A.length - 1 - i] A[A.length - 1 - j] := by
  simp only [VExpr.instOuter_eq_subst, VExpr.subst_app, VExpr.subst_bvar,
    VExpr.Subst.ofList_lt _ hi, VExpr.Subst.ofList_lt _ hj]

/-- Free variables of the arguments of an application are free variables of the application. -/
theorem _root_.Lean4Lean.FVarsIn.of_mem_getAppArgsList {P} {e a : Expr} (h : FVarsIn P e)
    (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  rw [← e.mkAppList_getAppArgsList, FVarsIn.mkAppList] at h
  exact h.2 a ha

/-- Inversion of the translation of a constant applied to three arguments. -/
theorem TrExprS.app3_inv {n : Name} {ls : List Level} {a1 a2 a3 : Expr} {e' : VExpr}
    (H : c.TrExprS (.app (.app (.app (.const n ls) a1) a2) a3) e') :
    ∃ ls' a1' a2' a3',
      c.TrExprS (.app (.app (.app (.const n ls) a1) a2) a3)
        (VExpr.mkApps (.const n ls') [a1', a2', a3']) ∧
      ls.mapM (VLevel.ofLevel c.lparams) = some ls' ∧
      (∃ ci, c.venv.constants n = some ci ∧ ls.length = ci.uvars) ∧
      c.TrExprS a1 a1' ∧ c.TrExprS a2 a2' ∧ c.TrExprS a3 a3' := by
  have ⟨fn', stk⟩ := AppStack.build (e := .const n ls) (as := [a1, a2, a3]) H
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  have .const hlc _ hlen := stk.tr
  cases hargs with | cons ha1 h => ?_
  cases h with | cons ha2 h => ?_
  cases h with | cons ha3 h => ?_
  cases h
  exact ⟨ls', _, _, _, hfull, hls, ⟨_, hlc, hlen⟩, ha1, ha2, ha3⟩

/-- Reduction of `Quot.lift` applied to `Quot.mk`. -/
theorem quotReduceRecCont.lift.WF (he : c.TrExprS e e') {ls : List Level}
    (hfn : e.getAppFn = .const ``Quot.lift ls) (hq : QuotCoherent c.venv) :
    RecM.WF c s (quotReduceRecCont e whnf 5 3) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRecCont
  extract_lets args
  have hargs_eq : args = e.getAppArgs := rfl
  simp only [hargs_eq]
  split <;> [rename_i h5; exact .pure nofun]
  -- the recursor spine
  have he'' : c.TrExprS ((Expr.const ``Quot.lift ls).mkAppList e.getAppArgsList) e' := by
    rw [← hfn, e.mkAppList_getAppArgsList]; exact he
  have ⟨fn', stk⟩ := AppStack.build he''
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  have hceq := he''.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  have .const hlc _ hlen := stk.tr
  rw [hq.lift] at hlc; cases hlc
  have hls'len : ls'.length = 2 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)).symm.trans hlen
  have hls'w := VLevel.WF.of_mapM_ofLevel hls
  refine (whnf.WF (hget 5 h5)).bind fun mk _ _ ⟨hb, mk', hmk, hmkdefeq⟩ => ?_
  split <;> [exact .pure nofun; rename_i hnot]
  have hisApp : mk.isAppOfArity ``Quot.mk 3 = true := by simpa using hnot
  obtain ⟨lsm, a1, a2, a3, rfl⟩ := Expr.isAppOfArity_three_eq_true hisApp
  obtain ⟨lsm', a1', a2', a3', hmk3, hlsm, ⟨_, hlm, hlenm⟩, ha1, ha2, ha3⟩ :=
    TrExprS.app3_inv hmk
  replace hmkdefeq := (hmk3.uniq c.Ewf (.refl c.Ewf c.Δwf) hmk).trans c.Ewf c.Δwf hmkdefeq
  rw [hq.quotMk] at hlm; cases hlm
  have hlsm'len : lsm'.length = 1 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsm)).symm.trans hlenm
  have hlsm'w := VLevel.WF.of_mapM_ofLevel hlsm
  simp only [Expr.appArg!]
  rw [getElem!_pos e.getAppArgs 3 (by omega)]
  -- the abstract reduction
  have hsplit : args' = args'.take 5 ++ args'[5] :: args'.drop 6 := by
    rw [← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  have hwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.const ``Quot.lift ls') (args'.take 5 ++ args'[5] :: args'.drop 6)) := by
    rw [← hsplit]; exact hfull.wf c.Ewf c.Δwf
  have hmajor : c.IsDefEqU args'[5] (VExpr.mkApps (.const ``Quot.mk lsm') ([a1', a2'] ++ [a3'])) :=
    hmkdefeq.symm
  have hiota := VIotaRuleShape.iota_body c.Ewf c.Δwf.toCtx hq.liftRecursorShape
    hq.mkConstructorShape hq.liftRuleShape hq.rigid rfl hls'w hls'len (pre := args'.take 5)
    (by simp; omega) hwf hlsm'len hlsm'w rfl rfl hmajor
  have hbody : ((hq.liftRuleShape.rhsBody.instL ls').instOuter
      ((args'.take 5).take 5 ++ [a3'])) = .app args'[3] a3' := by
    show ((VExpr.app (.bvar 2) (.bvar 0)).instL ls').instOuter _ = _
    rw [List.take_take, Nat.min_self]
    simp only [VExpr.instL]
    rw [VExpr.instOuter_app_bvar _ _ _ (by simp; omega) (by simp)]
    simp only [List.length_append, List.length_take, List.length_singleton]
    rw [List.getElem_append_left (by simp; omega), List.getElem_take,
      List.getElem_append_right (by simp)]
    simp only [List.length_take, List.getElem_singleton]
    have h3 : min 5 args'.length + 1 - 1 - 2 = 3 := by omega
    simp only [h3]
  rw [hbody, ← hsplit] at hiota
  have hdefeq : c.IsDefEqU e' (VExpr.mkApps (.app args'[3] a3') (args'.drop 6)) :=
    hceq.trans c.Ewf c.Δwf hiota
  have hrwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 6)) :=
    let ⟨_, h⟩ := hdefeq; ⟨_, h.hasType.2⟩
  have hr : c.TrExprS ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6))
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 6)) :=
    TrExprS.mkAppList_of_wf (TrExprS.app_of_wf (hget 3 (by omega)) ha3
      (VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx hrwf)) (Lean4Lean.List.forall₂_drop hargs 6) hrwf
  have hfv : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6)) := by
    intro P hP hfe
    rw [FVarsIn.mkAppList]
    refine ⟨⟨?_, ?_⟩, fun a ha => hfe.of_mem_getAppArgsList (List.mem_of_mem_drop ha)⟩
    · exact hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _)
    · have := hb P hP (hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
      exact this.2
  have main : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6)) ∧
      c.TrExpr ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 6)) e' :=
    ⟨hfv, (hr.trExpr c.Ewf c.Δwf).defeq c.Ewf c.Δwf hdefeq.symm⟩
  split
  · rw [mkAppRange_suffix_eq (by omega)]
    exact .pure fun _ h => Option.some.inj h ▸ main
  · rename_i h6
    rw [List.drop_eq_nil_of_le (by rw [← Expr.getAppArgs_toList, Array.length_toList]; omega)] at main
    exact .pure fun _ h => Option.some.inj h ▸ main

/-- Reduction of `Quot.ind` applied to `Quot.mk`, by proof irrelevance. -/
theorem quotReduceRecCont.ind.WF (he : c.TrExprS e e') {ls : List Level}
    (hfn : e.getAppFn = .const ``Quot.ind ls) (hq : QuotCoherent c.venv) :
    RecM.WF c s (quotReduceRecCont e whnf 4 3) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRecCont
  extract_lets args
  have hargs_eq : args = e.getAppArgs := rfl
  simp only [hargs_eq]
  split <;> [rename_i h4; exact .pure nofun]
  -- the eliminator spine
  have he'' : c.TrExprS ((Expr.const ``Quot.ind ls).mkAppList e.getAppArgsList) e' := by
    rw [← hfn, e.mkAppList_getAppArgsList]; exact he
  have ⟨fn', stk⟩ := AppStack.build he''
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  have hceq := he''.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  have .const hlc _ hlen := stk.tr
  rw [hq.ind] at hlc; cases hlc
  have hls'len : ls'.length = 1 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)).symm.trans hlen
  have hls'w := VLevel.WF.of_mapM_ofLevel hls
  refine (whnf.WF (hget 4 h4)).bind fun mk _ _ ⟨hb, mk', hmk, hmkdefeq⟩ => ?_
  split <;> [exact .pure nofun; rename_i hnot]
  have hisApp : mk.isAppOfArity ``Quot.mk 3 = true := by simpa using hnot
  obtain ⟨lsm, a1, a2, a3, rfl⟩ := Expr.isAppOfArity_three_eq_true hisApp
  obtain ⟨lsm', a1', a2', a3', hmk3, hlsm, ⟨_, hlm, hlenm⟩, ha1, ha2, ha3⟩ :=
    TrExprS.app3_inv hmk
  replace hmkdefeq := (hmk3.uniq c.Ewf (.refl c.Ewf c.Δwf) hmk).trans c.Ewf c.Δwf hmkdefeq
  rw [hq.quotMk] at hlm; cases hlm
  have hlsm'len : lsm'.length = 1 :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsm)).symm.trans hlenm
  have hlsm'w := VLevel.WF.of_mapM_ofLevel hlsm
  simp only [Expr.appArg!]
  rw [getElem!_pos e.getAppArgs 3 (by omega)]
  -- the abstract reduction: `Quot.ind p q ≡ p a` by proof irrelevance
  have hsplit : args' = args'.take 5 ++ args'.drop 5 := (List.take_append_drop _ _).symm
  have hwf5 : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.const ``Quot.ind ls') (args'.take 5)) := by
    have := hfull.wf c.Ewf c.Δwf
    rw [hsplit, VExpr.mkApps_append] at this
    exact VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx this
  have hdefeq : c.IsDefEqU (VExpr.mkApps (.const ``Quot.ind ls') (args'.take 5))
      (.app args'[3] a3') := by
    have h5 : args'.take 5 = [args'[0], args'[1], args'[2], args'[3], args'[4]] := by
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp only [List.getElem_take]
        match i, h2 with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
    rw [h5] at hwf5 ⊢
    exact hq.ind_defeq c.Ewf c.Δwf.toCtx hls'w hls'len hlsm'w hlsm'len hwf5
      (hmk3.wf c.Ewf c.Δwf) hmkdefeq
  have hdefeq' : c.IsDefEqU e' (VExpr.mkApps (.app args'[3] a3') (args'.drop 5)) := by
    refine hceq.trans c.Ewf c.Δwf ?_
    have hwf' : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
        (VExpr.mkApps (VExpr.mkApps (.const ``Quot.ind ls') (args'.take 5)) (args'.drop 5)) := by
      rw [← VExpr.mkApps_append, ← hsplit]
      exact hfull.wf c.Ewf c.Δwf
    have := VEnv.IsDefEqU.mkApps_congr_left c.Ewf c.Δwf.toCtx hdefeq hwf'
    rw [← VExpr.mkApps_append, ← hsplit] at this
    exact this
  have hrwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 5)) :=
    let ⟨_, h⟩ := hdefeq'; ⟨_, h.hasType.2⟩
  have hr : c.TrExprS ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5))
      (VExpr.mkApps (.app args'[3] a3') (args'.drop 5)) :=
    TrExprS.mkAppList_of_wf (TrExprS.app_of_wf (hget 3 (by omega)) ha3
      (VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx hrwf)) (Lean4Lean.List.forall₂_drop hargs 5) hrwf
  have hfv : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5)) := by
    intro P hP hfe
    rw [FVarsIn.mkAppList]
    refine ⟨⟨?_, ?_⟩, fun a ha => hfe.of_mem_getAppArgsList (List.mem_of_mem_drop ha)⟩
    · exact hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _)
    · have := hb P hP (hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
      exact this.2
  have main : c.FVarsBelow e ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5)) ∧
      c.TrExpr ((Expr.app e.getAppArgs[3] a3).mkAppList (e.getAppArgsList.drop 5)) e' :=
    ⟨hfv, (hr.trExpr c.Ewf c.Δwf).defeq c.Ewf c.Δwf hdefeq'.symm⟩
  split
  · rw [mkAppRange_suffix_eq (by omega)]
    exact .pure fun _ h => Option.some.inj h ▸ main
  · rename_i h5
    rw [List.drop_eq_nil_of_le (by rw [← Expr.getAppArgs_toList, Array.length_toList]; omega)] at main
    exact .pure fun _ h => Option.some.inj h ▸ main

/-- Quotient reduction refines the abstract environment. -/
theorem quotReduceRec.WF (he : c.TrExprS e e') (hq : QuotCoherent c.venv) :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRec
  split <;> [rename_i fn ls hfn; exact .pure nofun]
  split
  · rename_i h; rw [beq_iff_eq] at h; subst h
    exact quotReduceRecCont.lift.WF he hfn hq
  split
  · rename_i h; rw [beq_iff_eq] at h; subst h
    exact quotReduceRecCont.ind.WF he hfn hq
  exact .pure nofun

theorem forall₂_take {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    (n : Nat) : List.Forall₂ R (l₁.take n) (l₂.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h _ ih => cases n with
    | zero => simp
    | succ n => exact .cons h (ih n)

/-- The final phase of inductive recursor reduction refines the stored rule, given a converted
major premise that translates to something definitionally equal to the original one. -/
theorem inductiveReduceRecTail.WF {info : RecursorVal} {recFn : Name} {ls : List Level}
    {ls' : List VLevel} {args' : List VExpr}
    (he : c.TrExprS e e') (hfn : e.getAppFn = .const recFn ls)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hls : ls.mapM (VLevel.ofLevel c.lparams) = some ls')
    (hargs : List.Forall₂ c.TrExprS e.getAppArgsList args')
    (hfull : c.TrExprS e (VExpr.mkApps (.const recFn ls') args'))
    (hmaj : info.getMajorIdx < e.getAppArgs.size)
    {major₂ : Expr} (hfv : c.FVarsBelow e.getAppArgs[info.getMajorIdx] major₂)
    (hm : c.TrExpr major₂ (args'[info.getMajorIdx]'(by
      rw [← Lean4Lean.List.Forall₂.length_eq hargs, ← Expr.getAppArgs_toList]; simpa using hmaj))) :
    ∀ r, inductiveReduceRecTail info ls e.getAppArgs major₂ = some r →
      c.FVarsBelow e r ∧ c.TrExpr r e' := by
  intro r hr
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  -- the rule for the constructor at the head of the major premise
  unfold inductiveReduceRecTail at hr
  simp only [bind, Option.bind] at hr
  split at hr <;> [rename_i rule hrule; cases hr]
  unfold getRecRuleFor at hrule
  split at hrule <;> [rename_i fn lsc hmfn; cases hrule]
  have hmem := List.mem_of_find?_eq_some hrule
  have hctor : rule.ctor = fn := by simpa using List.find?_some hrule
  subst hctor
  split at hr <;> [cases hr; rename_i hsizeM]
  split at hr <;> [cases hr; rename_i hlsLen]
  simp only [bne_iff_ne, ne_eq, Classical.not_not] at hsizeM hlsLen
  simp only [RecursorVal.getFirstIndexIdx] at hr
  -- the environment facts
  have hceq := he.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
  have hfullS : c.TrExprS ((Expr.const recFn ls).mkAppList e.getAppArgsList)
      (VExpr.mkApps (.const recFn ls') args') := by
    rwa [← hfn, e.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hfullS
  have .const hlc _ hlen := stk.tr
  obtain ⟨hname, hsafe, hlpLen, -⟩ := c.trenv.find?_uniq hinfo hlc
  have hname' : info.name = recFn := hname
  subst hname'
  have hfindC : c.env.constants.find? info.name = some (.recInfo info) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  obtain ⟨⟨cnparams, indLevels, ctorParams, ⟨Hrec⟩, hrigid, hrules⟩, -⟩ := c.recursorRules hfindC hsafe
  obtain ⟨df, ⟨Hrule⟩, hrhs, ctorUvars, hIL, ⟨Hctor⟩⟩ := hrules rule hmem
  have hls'len : ls'.length = info.levelParams.length :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)).symm.trans hlsLen
  have hmaj' : info.numParams + info.numMotives + info.numMinors + info.numIndices <
      args'.length := by
    simpa [RecursorVal.getMajorIdx, hsize] using hmaj
  have hls'w := VLevel.WF.of_mapM_ofLevel hls
  -- the converted major premise as a constructor application
  have ⟨m₂', hm₂, hmdefeq⟩ := hm
  have hm₂S : c.TrExprS ((Expr.const rule.ctor lsc).mkAppList major₂.getAppArgsList) m₂' := by
    rwa [← hmfn, major₂.mkAppList_getAppArgsList]
  have ⟨_, mstk⟩ := AppStack.build hm₂S
  obtain ⟨lsc', MA', hlsc, rfl, hMargs, hMfull⟩ := mstk.constantApplication
  have ⟨hMsize, hMget⟩ := AppStack.argsGet hMargs
  have .const hlcc _ hlenc := mstk.tr
  rw [Hctor.const] at hlcc; cases hlcc
  have hlsc'len : lsc'.length = ctorUvars :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsc)).symm.trans hlenc
  have hlsc'w := VLevel.WF.of_mapM_ofLevel hlsc
  have hmajor : c.IsDefEqU (args'[info.getMajorIdx]'(by omega))
      (VExpr.mkApps (.const rule.ctor lsc') (MA'.take cnparams ++ MA'.drop cnparams)) := by
    rw [List.take_append_drop]
    exact hmdefeq.symm.trans c.Ewf c.Δwf (hm₂S.uniq c.Ewf (.refl c.Ewf c.Δwf) hMfull)
  have hMlen : MA'.length = cnparams + rule.nfields := by
    have hprefix := VExpr.WF.of_mkApps c.Ewf.ordered c.Δwf.toCtx
      (f := VExpr.mkApps (.const info.name ls')
        (args'.take info.getMajorIdx ++ [args'[info.getMajorIdx]'(by omega)]))
      (args := args'.drop (info.getMajorIdx + 1))
      (by
        rw [← VExpr.mkApps_append, List.append_assoc, List.singleton_append,
          ← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
        exact hfull.wf c.Ewf c.Δwf)
    have ⟨_, ht, _⟩ := Hrec.spine_typing c.Ewf c.Δwf.toCtx hls'w hls'len
      (by simp [RecursorVal.getMajorIdx]; omega) hprefix
    have hmTyped := (hmajor.of_l c.Ewf c.Δwf.toCtx ht).hasType.2
    rw [List.take_append_drop] at hmTyped
    exact Hctor.saturated_of_hasType c.Ewf c.Δwf.toCtx hrigid hmTyped
  -- the abstract reduction
  have hsplit : args' = args'.take info.getMajorIdx ++
      (args'[info.getMajorIdx]'(by omega)) :: args'.drop (info.getMajorIdx + 1) := by
    rw [← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  have hwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (VExpr.mkApps (.const info.name ls') (args'.take info.getMajorIdx ++
        (args'[info.getMajorIdx]'(by omega)) :: args'.drop (info.getMajorIdx + 1))) := by
    rw [← hsplit]; exact hfull.wf c.Ewf c.Δwf
  have hiota := Hrule.iota c.Ewf c.Δwf.toCtx Hrec Hctor hrigid hIL hls'w hls'len
    (pre := args'.take info.getMajorIdx)
    (by simp [RecursorVal.getMajorIdx]; omega) hwf hlsc'len hlsc'w
    (by simp; omega) (by simp; omega) hmajor
  rw [← hsplit, List.take_take, Nat.min_eq_left (by simp [RecursorVal.getMajorIdx])] at hiota
  -- the instantiated rule right-hand side
  have hrhs₀ := hrhs.instL c.Ewf (by trivial) hls hlsLen.symm
  have hrhs₀' := hrhs₀.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
  have hclosed : (df.rhs.instL ls').ClosedN 0 :=
    VExpr.WF.closedN c.Ewf.ordered (hrhs₀.wf (Δ := [])) trivial
  rw [hclosed.liftN_eq (Nat.zero_le _)] at hrhs₀'
  have ⟨r₀', hr₀, hr₀defeq⟩ := hrhs₀'
  -- the executable result as an application spine
  generalize hfiiE : info.numParams + info.numMotives + info.numMinors = fii at *
  have hfii : fii ≤ e.getAppArgs.size := by
    simp [RecursorVal.getMajorIdx] at hmaj; omega
  have hr1 : mkAppRange (rule.rhs.instantiateLevelParams info.levelParams ls) 0
      fii e.getAppArgs =
      (rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList
        (e.getAppArgsList.take fii) := by
    refine Expr.mkAppRange_eq (l₁ := []) (l₃ := e.getAppArgsList.drop fii)
      ?_ rfl ?_
    · rw [Expr.getAppArgs_toList, List.nil_append, List.take_append_drop]
    · rw [List.nil_append, List.length_take, ← Expr.getAppArgs_toList, Array.length_toList,
        Nat.min_eq_left hfii]
  have hr2 : ∀ f, mkAppRange f (major₂.getAppArgs.size - rule.nfields) major₂.getAppArgs.size
      major₂.getAppArgs = f.mkAppList (major₂.getAppArgsList.drop cnparams) := by
    intro f
    rw [mkAppRange_suffix_eq (by omega)]
    congr 2; omega
  generalize hA : e.getAppArgsList.take fii ++
    major₂.getAppArgsList.drop cnparams ++ e.getAppArgsList.drop (info.getMajorIdx + 1) = A
  generalize hA' : args'.take fii ++ MA'.drop cnparams ++
    args'.drop (info.getMajorIdx + 1) = A'
  have hAtr : List.Forall₂ c.TrExprS A A' := by
    rw [← hA, ← hA']
    exact ((forall₂_take hargs _).append' (Lean4Lean.List.forall₂_drop hMargs _)).append' (Lean4Lean.List.forall₂_drop hargs _)
  rw [hA'] at hiota
  have hdefeq : c.IsDefEqU e' (VExpr.mkApps r₀' A') := by
    refine hceq.trans c.Ewf c.Δwf (hiota.trans c.Ewf c.Δwf ?_)
    exact VEnv.IsDefEqU.mkApps_congr_left c.Ewf c.Δwf.toCtx hr₀defeq.symm
      (let ⟨_, h⟩ := hiota; ⟨_, h.hasType.2⟩)
  have hrwf : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (VExpr.mkApps r₀' A') :=
    let ⟨_, h⟩ := hdefeq; ⟨_, h.hasType.2⟩
  have hrS : c.TrExprS ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A)
      (VExpr.mkApps r₀' A') :=
    TrExprS.mkAppList_of_wf hr₀ hAtr hrwf
  have hfvr : c.FVarsBelow e ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A) := by
    intro P hP hfe
    rw [FVarsIn.mkAppList]
    refine ⟨hrhs₀.fvarsIn.mono nofun, fun a ha => ?_⟩
    rw [← hA] at ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact hfe.of_mem_getAppArgsList (List.mem_of_mem_take ha)
    · have hmaj' := hfv P hP (hfe.of_mem_getAppArgsList (by
        rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
      exact hmaj'.of_mem_getAppArgsList (List.mem_of_mem_drop ha)
    · exact hfe.of_mem_getAppArgsList (List.mem_of_mem_drop ha)
  have main : c.FVarsBelow e ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A) ∧
      c.TrExpr ((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList A) e' :=
    ⟨hfvr, (hrS.trExpr c.Ewf c.Δwf).defeq c.Ewf c.Δwf hdefeq.symm⟩
  rw [hr1, hr2] at hr
  split at hr
  · rw [mkAppRange_suffix_eq (by omega), ← Expr.mkAppList_append, ← Expr.mkAppList_append,
      ← List.append_assoc, hA, Option.pure_def] at hr
    cases hr
    exact main
  · rename_i hlt
    have hle : e.getAppArgsList.length ≤ info.getMajorIdx + 1 := by
      rw [← Expr.getAppArgs_toList, Array.length_toList]; exact Nat.le_of_not_lt hlt
    rw [← Expr.mkAppList_append, Option.pure_def] at hr
    rw [List.drop_eq_nil_of_le (as := e.getAppArgsList) hle, List.append_nil] at hA
    rw [hA] at hr
    cases hr
    exact main

/-- The final phase of inductive recursor reduction stays in every universe scope containing the
recursor application and the converted major premise: the rule's right-hand side mentions only the
recursor's universe parameters, which are instantiated by the levels of the application. -/
theorem inductiveReduceRecTail.levelParamsIn {info : RecursorVal} {recFn : Name}
    {ls : List Level} (he : c.TrExprS e e') (hfn : e.getAppFn = .const recFn ls)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hl : e.levelParamsIn Us = true) (hm : major₂.levelParamsIn Us = true) :
    ∀ r, inductiveReduceRecTail info ls e.getAppArgs major₂ = some r →
      r.levelParamsIn Us = true := by
  intro r hr
  unfold inductiveReduceRecTail at hr
  simp only [bind, Option.bind] at hr
  split at hr <;> [rename_i rule hrule; cases hr]
  unfold getRecRuleFor at hrule
  split at hrule <;> [rename_i fn lsc hmfn; cases hrule]
  have hmem := List.mem_of_find?_eq_some hrule
  split at hr <;> [cases hr; rename_i hsizeM]
  split at hr <;> [cases hr; rename_i hlsLen]
  simp only [bne_iff_ne, ne_eq, Classical.not_not] at hsizeM hlsLen
  -- the rule's right-hand side
  have hfullS : c.TrExprS ((Expr.const recFn ls).mkAppList e.getAppArgsList) e' := by
    rwa [← hfn, e.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hfullS
  have .const hlc _ _ := stk.tr
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hinfo hlc
  have hname' : info.name = recFn := hname
  subst hname'
  have hfindC : c.env.constants.find? info.name = some (.recInfo info) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  obtain ⟨⟨_, _, _, _, _, hrules⟩, -⟩ := c.recursorRules hfindC hsafe
  obtain ⟨_, _, hrhs, -⟩ := hrules rule hmem
  have hls : ∀ l ∈ ls, l.paramsIn Us = true := by
    have := Expr.levelParamsIn_getAppFn hl
    rw [hfn] at this; simpa [Expr.levelParamsIn] using this
  have hrhsl := Expr.levelParamsIn_instantiateLevelParams hrhs.levelParamsIn hls hlsLen.symm
  have hargs := fun a (h : a ∈ e.getAppArgs) => Expr.levelParamsIn_of_mem_getAppArgs hl h
  have hmargs := fun a (h : a ∈ major₂.getAppArgs) => Expr.levelParamsIn_of_mem_getAppArgs hm h
  split at hr <;> cases hr
  · exact Expr.levelParamsIn_mkAppRange (Expr.levelParamsIn_mkAppRange
      (Expr.levelParamsIn_mkAppRange hrhsl hargs) hmargs) hargs
  · exact Expr.levelParamsIn_mkAppRange (Expr.levelParamsIn_mkAppRange hrhsl hargs) hmargs

/-- The whnf of the type of a K-like major premise, an application of the major inductive at a
sort, supplies exactly the parameters and indices of that inductive (unique typing and sort/Pi
separation, `VEnv.HasType.mkApps_sort_arity`). -/
theorem toCtorWhenK.majorType_size {info : RecursorVal} {A : Expr} {A' : VExpr} {u : VLevel}
    (hK : ∃ ind ctorName, c.env.constants.find? info.getMajorInduct = some (.inductInfo ind) ∧
      ind.ctors = [ctorName] ∧ KLikeAlignment c.venv info ctorName)
    (hAS : c.TrExprS A A') (hAfn : A.getAppFn = .const info.getMajorInduct lsI)
    (hsort : c.HasType A' (.sort u)) :
    A.getAppArgs.size = info.numParams + info.numIndices := by
  obtain ⟨ind, ctorName, -, -, indUvars, indType, -, indDoms, -, -, hIc, hInorm, hIlen, -⟩ := hK
  have hAS' : c.TrExprS ((Expr.const info.getMajorInduct lsI).mkAppList A.getAppArgsList) A' := by
    rwa [← hAfn, A.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hAS'
  obtain ⟨lsI', AA', hlsI, rfl, hAargs, hAfull⟩ := stk.constantApplication
  have hAA := hAS'.uniq c.Ewf (.refl c.Ewf c.Δwf) hAfull
  have .const hlcI _ hlenI := stk.tr
  rw [hIc] at hlcI; cases hlcI
  have hlsI'len : lsI'.length = indUvars :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsI)).symm.trans hlenI
  have hlsI'w := VLevel.WF.of_mapM_ofLevel hlsI
  have hcI := VEnv.HasType.const (Γ := c.vlctx.toCtx) hIc hlsI'w (by simpa using hlsI'len)
  have hcI := hcI.defeqU_r c.Ewf c.Δwf.toCtx ((hInorm.instL hlsI'w).weak0 c.Ewf.ordered)
  rw [VExpr.instL_wrapForalls] at hcI
  have hlen := VEnv.HasType.mkApps_sort_arity c.Ewf c.Δwf.toCtx hcI
    (hsort.defeqU_l c.Ewf c.Δwf hAA)
  rw [← Array.length_toList, Expr.getAppArgs_toList, Lean4Lean.List.Forall₂.length_eq hAargs,
    hlen, List.length_map, hIlen]

/-- Converting the major premise of a K-like recursor to the nullary constructor application
yields a definitionally equal term, by proof irrelevance. -/
theorem toCtorWhenK.WF_all {info : RecursorVal} {major : Expr} {m' : VExpr} (hk : info.k = true)
    (hK : ∃ ind ctorName, c.env.constants.find? info.getMajorInduct = some (.inductInfo ind) ∧
      ind.ctors = [ctorName] ∧ KLikeAlignment c.venv info ctorName)
    (he : c.TrExprS major m') :
    RecM.WF c s (toCtorWhenK c.env whnf inferType isDefEq info major) fun r _ =>
      (c.FVarsBelow major r ∧ c.TrExpr r m') ∧ c.LevelsBelow major r := by
  have hid : ∀ {s : State}, RecM.WF c s (pure major) fun r _ =>
      (c.FVarsBelow major r ∧ c.TrExpr r m') ∧ c.LevelsBelow major r :=
    .pure ⟨⟨.rfl, he.trExpr c.Ewf c.Δwf⟩, .rfl⟩
  unfold toCtorWhenK
  split <;> [skip; exact absurd hk ‹_›]
  refine (inferType.WF_below he).bind fun T _ _ ⟨⟨T', hfvT, _, hTS, hT'⟩, hlT⟩ => ?_
  refine (whnf.WF_below hTS).bind fun A _ _ ⟨hfvA, hlA, A', hAS, hAdefeq⟩ => ?_
  split <;> [rename_i I lsI hAfn; exact hid]
  split <;> [exact hid; rename_i hI]
  split <;> [exact hid; skip]
  simp only [bne_iff_ne, ne_eq, Classical.not_not] at hI
  subst hI
  obtain ⟨ind, ctorName, hind, hctors, indUvars, indType, ctorType,
    indDoms, ctorDoms, ctorBody, hIc, hInorm, hIlen, hCc, hCnorm, hClen, hparams⟩ := hK
  -- the nullary constructor application
  have hind' : c.env.find? info.getMajorInduct = some (.inductInfo ind) := by
    rw [Lean.Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?]; exact hind
  -- the type of the major premise as an inductive application
  have hAS' : c.TrExprS ((Expr.const info.getMajorInduct lsI).mkAppList A.getAppArgsList) A' := by
    rwa [← hAfn, A.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hAS'
  obtain ⟨lsI', AA', hlsI, rfl, hAargs, hAfull⟩ := stk.constantApplication
  have hAA := hAS'.uniq c.Ewf (.refl c.Ewf c.Δwf) hAfull
  have .const hlcI _ hlenI := stk.tr
  rw [hIc] at hlcI; cases hlcI
  have hlsI'len : lsI'.length = indUvars :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsI)).symm.trans hlenI
  have hlsI'w := VLevel.WF.of_mapM_ofLevel hlsI
  have hAAwf := hAfull.wf c.Ewf c.Δwf
  -- the inductive application is a proposition, and its arguments are typed along its telescope
  have hcI := VEnv.HasType.const (Γ := c.vlctx.toCtx) hIc hlsI'w (by simpa using hlsI'len)
  have hcI := hcI.defeqU_r c.Ewf c.Δwf.toCtx
    ((hInorm.instL hlsI'w).weak0 c.Ewf.ordered)
  rw [VExpr.instL_wrapForalls] at hcI
  -- the type of the major premise is a type, so it supplies the whole telescope
  have hAAlen : AA'.length = info.numParams + info.numIndices := by
    have ⟨_, hsortT⟩ := hT'.isType c.Ewf.ordered c.Δwf.toCtx
    have hsortA := (hsortT.defeqU_l c.Ewf c.Δwf hAdefeq.symm).defeqU_l c.Ewf c.Δwf hAA
    rw [VEnv.HasType.mkApps_sort_arity c.Ewf c.Δwf.toCtx hcI hsortA, List.length_map, hIlen]
  have hnullary : mkNullaryCtor c.env A info.numParams =
      some ((Expr.const ctorName lsI).mkAppList (A.getAppArgsList.take info.numParams)) := by
    unfold mkNullaryCtor
    rw [Expr.withApp_eq, hAfn]
    simp only [getFirstCtor, hind', hctors, List.head?_cons, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Option.pure_def]
    refine Expr.mkAppRange_eq (l₁ := []) (l₃ := A.getAppArgsList.drop info.numParams) ?_ rfl ?_
    · rw [Expr.getAppArgs_toList, List.nil_append, List.take_append_drop]
    · have hAsize : A.getAppArgs.size = info.numParams + info.numIndices := by
        rw [← Array.length_toList, Expr.getAppArgs_toList, Lean4Lean.List.Forall₂.length_eq hAargs,
          hAAlen]
      have h1 := congrArg List.length (Expr.getAppArgs_toList (e := A))
      simp only [Array.length_toList] at h1
      rw [List.nil_append, List.length_take, ← h1, hAsize,
        Nat.min_eq_left (Nat.le_add_right _ _)]
  rw [hnullary]
  simp only
  have ⟨hIargs, hIsort⟩ := VEnv.HasType.mkApps_wrapForalls c.Ewf c.Δwf.toCtx hcI hAAwf
    (by simp [hAAlen, hIlen])
  simp only [VExpr.instL, VLevel.inst, VExpr.instOuter_sort] at hIsort
  have hΓI : OnCtx (indDoms.reverse ++ []) (c.venv.IsType indUvars) :=
    (VEnv.IsType.wrapForalls_inv c.Ewf trivial
      ((c.Ewf.ordered.constWF hIc).defeqU_l c.Ewf trivial hInorm)).1
  -- the constructor application is typed at the inductive application
  have hcT := VEnv.HasType.const (Γ := c.vlctx.toCtx) hCc hlsI'w (by simpa using hlsI'len)
  have hcT := hcT.defeqU_r c.Ewf c.Δwf.toCtx
    ((hCnorm.instL hlsI'w).weak0 c.Ewf.ordered)
  rw [VExpr.instL_wrapForalls] at hcT
  have hnewT : c.HasType (VExpr.mkApps (.const ctorName lsI') (AA'.take info.numParams))
      ((ctorBody.instL lsI').instOuter (AA'.take info.numParams)) := by
    refine VEnv.HasType.mkApps_of_telescope hcT (by simp [hClen]; omega) ?_
    intro j hj hj'
    simp only [List.length_take, List.length_map] at hj hj'
    have hjp : j < info.numParams := by omega
    have hI_j := hIargs j (by omega) (by simp [hIlen]; omega)
    have hdef := hparams j (by omega) (by omega)
    have hΓ₀ : OnCtx ((indDoms.take j).reverse) (c.venv.IsType indUvars) := by
      have : indDoms.reverse ++ [] = (indDoms.drop j).reverse ++ (indDoms.take j).reverse := by
        rw [List.append_nil, ← List.reverse_append, List.take_append_drop]
      rw [this] at hΓI
      exact hΓI.of_append
    have hconv := VEnv.IsDefEqU.closed_telescope_instOuter c.Ewf hΓ₀ hdef hlsI'w
      (args := AA'.take j) (by simp; omega) (by
        intro k hk hk'
        simp only [List.length_take] at hk
        have := hIargs k (by omega) (by simp [hIlen]; omega)
        simp only [List.reverse_reverse, List.getElem_map, List.getElem_take, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt (show k < j by omega))]
        simpa [List.getElem_map] using this)
    rw [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjp), List.getElem_map]
    rw [List.getElem_map] at hI_j
    exact hI_j.defeqU_r c.Ewf c.Δwf hconv
  have hnewS : c.TrExprS ((Expr.const ctorName lsI).mkAppList (A.getAppArgsList.take info.numParams))
      (VExpr.mkApps (.const ctorName lsI') (AA'.take info.numParams)) :=
    TrExprS.mkAppList_of_wf (.const hCc hlsI (by simpa using hlenI)) (forall₂_take hAargs _)
      ⟨_, hnewT⟩
  -- the index check
  refine (inferType.WF hnewS).bind fun N _ _ ⟨N', _, _, hNS, hN'⟩ => ?_
  refine (isDefEq.WF hAS hNS).bind fun b _ _ hb => ?_
  split <;> [rename_i hbt; exact hid]
  have hb := hb hbt
  refine .pure ⟨⟨?_, ?_⟩, ?_⟩
  · intro P hP hfe
    have hfA : FVarsIn P A := hfvA P hP (hfvT P hP hfe)
    rw [FVarsIn.mkAppList]
    refine ⟨?_, fun a ha => hfA.of_mem_getAppArgsList (List.mem_of_mem_take ha)⟩
    have := hfA
    rw [← A.mkAppList_getAppArgsList, hAfn, FVarsIn.mkAppList] at this
    exact this.1
  · refine ⟨_, hnewS, ?_⟩
    have hnewI : c.HasType (VExpr.mkApps (.const ctorName lsI') (AA'.take info.numParams))
        (VExpr.mkApps (.const info.getMajorInduct lsI') AA') :=
      hN'.defeqU_r c.Ewf c.Δwf (hb.symm.trans c.Ewf c.Δwf hAA)
    have hmI : c.HasType m' (VExpr.mkApps (.const info.getMajorInduct lsI') AA') :=
      hT'.defeqU_r c.Ewf c.Δwf (hAdefeq.symm.trans c.Ewf c.Δwf hAA)
    exact ⟨_, (VEnv.IsDefEq.proofIrrel hIsort hmI hnewI).symm⟩
  · intro Us P hs hl hP
    have hA := hlA Us P hs (hlT Us P hs hl hP) (hfvT P hs.1 hP)
    refine Expr.levelParamsIn_mkAppList ?_ fun a ha =>
      Expr.levelParamsIn_of_mem_getAppArgsList hA (List.mem_of_mem_take ha)
    have := Expr.levelParamsIn_getAppFn hA
    rw [hAfn] at this; simpa [Expr.levelParamsIn] using this

theorem _root_.Lean.Expr.isConstOf_eq_true {e : Expr} {n : Name} (h : e.isConstOf n = true) :
    ∃ ls, e = .const n ls := by
  cases e <;> simp [Expr.isConstOf] at h
  case const n' ls => subst h; exact ⟨ls, rfl⟩

theorem foldl_app_proj (r : Expr) (n : Name) (e : Expr) (l : List Nat) :
    l.foldl (fun r i => Expr.app r (.proj n i e)) r = r.mkAppList (l.map fun i => .proj n i e) := by
  induction l generalizing r with
  | nil => rfl
  | cons i l ih => simp [ih]

theorem _root_.Lean4Lean.Kernel.Environment.isNonRecStructure_inv {env : Environment} {n : Name}
    (h : env.isNonRecStructure n = true) :
    ∃ sInfo : InductiveVal, ∃ ctor, env.find? n = some (.inductInfo sInfo) ∧
      sInfo.ctors = [ctor] ∧ sInfo.numIndices = 0 := by
  unfold Lean.Kernel.Environment.isNonRecStructure at h
  split at h <;> [rename_i hfind; cases h]
  exact ⟨_, _, hfind, rfl, rfl⟩

/-- A type application of a family registered in the projection registry supplies exactly its
parameters and indices: the family's type is a telescope ending in a sort, and an application
of it at sort type has consumed the whole telescope (`HasType.mkApps_sort_arity`). -/
theorem _root_.Lean4Lean.TypeChecker.VContext.projectionTypeArity (c : VContext) {n : Name}
    {info : VProjectionInfo} (hinfo : c.venv.projections n info) {T : VExpr}
    (hfam : c.venv.constants n = some ⟨info.uvars, T⟩) {ls : List VLevel} {args : List VExpr}
    {u : VLevel} (h : c.HasType (VExpr.mkApps (.const n ls) args) (.sort u)) :
    args.length = info.nparams + info.nindices :=
  VEnv.HasType.projectionFamily_arity c.Ewf c.Δwf.toCtx hinfo hfam h

/-- The type of a well-typed term whose head is a structure (a single-constructor family without
indices) applies the structure to exactly the parameters of its constructor. This is what makes
`args.shrink(nparams)` in the C++ `expand_eta_struct` a no-op. -/
theorem _root_.Lean4Lean.TypeChecker.VContext.structTypeArgs {c : VContext} {A : Expr} {A' : VExpr}
    {n ctor : Name} {lsI : List Level} {sInfo : InductiveVal} {mkInfo : ConstructorVal}
    (hAS : c.TrExprS A A') (hAT : ∃ u, c.HasType A' (.sort u))
    (hAfn : A.getAppFn = .const n lsI)
    (hfind : c.env.find? n = some (.inductInfo sInfo)) (hsingle : sInfo.ctors = [ctor])
    (hnind : sInfo.numIndices = 0)
    (hci : c.env.find? ctor = some (.ctorInfo mkInfo)) (hinduct : mkInfo.induct = n) :
    A.getAppArgs.size = mkInfo.numParams := by
  have hAS' : c.TrExprS ((Expr.const n lsI).mkAppList A.getAppArgsList) A' := by
    rwa [← hAfn, A.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hAS'
  obtain ⟨lsI', P', hlsI, rfl, hPargs, hAfull⟩ := stk.constantApplication
  have hAA := hAS'.uniq c.Ewf (.refl c.Ewf c.Δwf) hAfull
  have .const hlcI _ _ := stk.tr
  obtain ⟨info, hinfo, -, -, -, -, -, -, -, -, -, -, -, -, hnp, -, -, -, hsi, -, ⟨indType, hIc⟩,
    -, -⟩ := VContext.registryShape hfind hlcI hsingle hci hinduct
  obtain ⟨u, hAT⟩ := hAT
  have hlen := c.projectionTypeArity hinfo hIc (hAT.defeqU_l c.Ewf c.Δwf hAA)
  rw [← hsi, hnind, Nat.add_zero] at hlen
  rw [← Array.length_toList, Expr.getAppArgs_toList, Lean4Lean.List.Forall₂.length_eq hPargs, hlen,
    hnp]

/-- The absent-constructor fallback of `expandEtaStruct` is unreachable from recursor
reduction: `inductiveReduceRec` calls `toCtorWhenStruct` with the major inductive of a present
recursor, and the major inductive of every present recursor is a header whose listed
constructors are present constructors of it (`InstalledBlocks.recursorMajorCtors`). -/
theorem VContext.recursorMajorCtor (c : VContext)
    (hrec : c.env.find? recFn = some (.recInfo info))
    (hfind : c.env.find? info.getMajorInduct = some (.inductInfo sInfo))
    (hctor : ctor ∈ sInfo.ctors) :
    ∃ mkInfo, c.env.find? ctor = some (.ctorInfo mkInfo) ∧
      mkInfo.induct = info.getMajorInduct := by
  obtain ⟨info', hfind', hpresent⟩ := c.blocks.recursorMajorCtors hrec
  rw [hfind] at hfind'
  cases hfind'
  obtain ⟨ci, hci⟩ := hpresent ctor hctor
  obtain ⟨mkInfo, rfl, hinduct, -⟩ := c.listedConstructors _ sInfo hfind ctor hctor ci hci
  exact ⟨mkInfo, hci, hinduct⟩

/-- `expandEtaStruct` at the type of the major premise of a present recursor finds the
structure's constructor: its absent-constructor fallback is never taken. -/
theorem VContext.expandEtaStruct_ctor (c : VContext)
    (hrec : c.env.find? recFn = some (.recInfo info))
    (hnonrec : c.env.isNonRecStructure info.getMajorInduct = true) :
    ∃ sInfo ctor mkInfo, c.env.find? info.getMajorInduct = some (.inductInfo sInfo) ∧
      sInfo.ctors.head? = some ctor ∧ c.env.find? ctor = some (.ctorInfo mkInfo) := by
  unfold Lean.Kernel.Environment.isNonRecStructure at hnonrec
  split at hnonrec <;> [rename_i hfind; cases hnonrec]
  rename_i ctor numNested isUnsafe isReflexive
  obtain ⟨mkInfo, hmk, -⟩ := VContext.recursorMajorCtor (ctor := ctor) c hrec hfind (by simp)
  exact ⟨_, ctor, mkInfo, hfind, rfl, hmk⟩

/-- Converting a term of structure type to its constructor applied to its projections yields a
definitionally equal term, by structure eta. -/
theorem toCtorWhenStruct.WF_all {w : Expr} {w' : VExpr} (he : c.TrExprS w w') :
    RecM.WF c s (toCtorWhenStruct c.env whnf inferType n w) fun r _ =>
      (c.FVarsBelow w r ∧ c.TrExpr r w') ∧ c.LevelsBelow w r := by
  have hid : ∀ {s : State}, RecM.WF c s (pure w) fun r _ =>
      (c.FVarsBelow w r ∧ c.TrExpr r w') ∧ c.LevelsBelow w r :=
    .pure ⟨⟨.rfl, he.trExpr c.Ewf c.Δwf⟩, .rfl⟩
  unfold toCtorWhenStruct
  split <;> [exact hid; rename_i hguard]
  have hnonrec : c.env.isNonRecStructure n = true := by
    revert hguard; cases c.env.isNonRecStructure n <;> simp
  refine (inferType.WF_below he).bind fun T _ _ ⟨⟨T', hfvT, _, hTS, hT'⟩, hlT⟩ => ?_
  refine (whnf.WF_below hTS).bind fun A _ _ ⟨hfvA, hlA, A', hAS, hAdefeq⟩ => ?_
  split <;> [exact hid; rename_i hisConst]
  have hisConst' : A.getAppFn.isConstOf n = true := by simpa using hisConst
  obtain ⟨lsI, hAfn⟩ := Expr.isConstOf_eq_true hisConst'
  refine (inferType.WF hAS).bind fun TT _ _ ⟨TT', _, _, hTTS, hTT'⟩ => ?_
  refine (whnf.WF hTTS).bind fun u₀ _ _ ⟨_, u₀', hu₀S, hu₀defeq⟩ => ?_
  split <;> [skip; exact hid]
  split <;> [rename_i u hnz; exact hid]
  -- the structure
  unfold Lean.Kernel.Environment.isNonRecStructure at hnonrec
  split at hnonrec <;> [rename_i hfind; cases hnonrec]
  rename_i ctor numNested isUnsafe isReflexive
  obtain ⟨sInfo, hfind, hsingle, hnind⟩ : ∃ sInfo : InductiveVal,
      c.env.find? n = some (.inductInfo sInfo) ∧ sInfo.ctors = [ctor] ∧ sInfo.numIndices = 0 :=
    ⟨_, hfind, rfl, rfl⟩
  unfold expandEtaStruct
  rw [Expr.withApp_eq, hAfn]
  simp only [hfind, hsingle, List.head?_cons]
  split <;> [rename_i mkInfo hci; exact hid]
  -- the constant the structure lists is a constructor of the structure
  have hinduct : mkInfo.induct = n := by
    obtain ⟨_, hEq, h, -⟩ := c.listedConstructors n sInfo hfind ctor (by simp [hsingle]) _ hci
    rw [ConstantInfo.ctorInfo.inj hEq]
    exact h
  -- the structure type supplies exactly the parameters
  have hsize : A.getAppArgs.size = mkInfo.numParams := by
    obtain ⟨_, hTsort⟩ := hT'.isType c.Ewf.ordered c.Δwf.toCtx
    exact VContext.structTypeArgs hAS ⟨_, hTsort.defeqU_l c.Ewf c.Δwf hAdefeq.symm⟩ hAfn hfind
      hsingle hnind hci hinduct
  rw [foldl_app_proj]
  have hnullary : mkAppRange (Expr.const ctor lsI) 0 mkInfo.numParams A.getAppArgs =
      (Expr.const ctor lsI).mkAppList A.getAppArgsList := by
    refine Expr.mkAppRange_eq (l₁ := []) (l₃ := []) ?_ rfl ?_
    · rw [Expr.getAppArgs_toList, List.nil_append, List.append_nil]
    · rw [List.nil_append, ← Expr.getAppArgs_toList, Array.length_toList, hsize]
  rw [hnullary, ← Expr.mkAppList_append]
  show RecM.WF c _ (pure ((Expr.const ctor lsI).mkAppList _)) _
  -- the structure type application
  have hAS' : c.TrExprS ((Expr.const n lsI).mkAppList A.getAppArgsList) A' := by
    rwa [← hAfn, A.mkAppList_getAppArgsList]
  have ⟨_, stk⟩ := AppStack.build hAS'
  obtain ⟨lsI', P', hlsI, rfl, hPargs, hAfull⟩ := stk.constantApplication
  have hAA := hAS'.uniq c.Ewf (.refl c.Ewf c.Δwf) hAfull
  have .const hlcI _ hlenI := stk.tr
  -- registry facts
  obtain ⟨info, hinfo, hname, decl, doms, result, hwf, hctor, hshape, hvalid, hhead, hdn, hdu, hle,
    hnp, hnf, hnf', hsp, hsi, hidxs, ⟨indType, hIc⟩, hsort, hparams⟩ :=
    VContext.registryShape hfind hlcI hsingle hci hinduct
  subst hname
  have hnindices : info.nindices = 0 := hsi ▸ hnind
  rw [hIc] at hlcI; cases hlcI
  have hlsI'len : lsI'.length = info.uvars :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsI)).symm.trans hlenI
  have hlsI'w := VLevel.WF.of_mapM_ofLevel hlsI
  have hP'len : P'.length = info.nparams := by
    rw [← Lean4Lean.List.Forall₂.length_eq hPargs, ← Expr.getAppArgs_toList, Array.length_toList,
      hsize, hnp]
  have htS : c.HasType w' (VExpr.mkApps (.const n lsI') P') :=
    hT'.defeqU_r c.Ewf c.Δwf (hAdefeq.symm.trans c.Ewf c.Δwf hAA)
  -- the sort of the structure type is never zero
  cases hu₀S with | sort hu' => ?_
  have hsortS : c.HasType (VExpr.mkApps (.const n lsI') P') (.sort _) :=
    (hTT'.defeqU_r c.Ewf c.Δwf hu₀defeq.symm).defeqU_l c.Ewf c.Δwf hAA
  have hsortC := hsort lsI' P' hlsI'len (by rw [hP'len, hnindices, Nat.add_zero]) ⟨_, hsortS⟩
  have hguard : (info.resultLevel.inst lsI').IsNeverZero :=
    (ofLevel_isNeverZero hu' hnz).of_equiv ((hsortS.uniqU c.Ewf c.Δwf hsortC).sort_inv c.Ewf c.Δwf)
  have hclosed : info.ctorType.Closed := by
    have ⟨_, h⟩ := hwf
    exact VExpr.WF.closedN c.Ewf.ordered ⟨_, h⟩ trivial
  -- the constructor telescope
  have hparamsT := hparams lsI' P' hlsI'len (by rw [hP'len, hnindices, Nat.add_zero]) ⟨_, hsortS⟩
  have hcT : c.HasType (.const info.ctorName lsI')
      (VExpr.wrapForalls (doms.map (VExpr.instL lsI')) (result.instL lsI')) := by
    have := VEnv.HasType.const (Γ := c.vlctx.toCtx) hctor hlsI'w hlsI'len
    rwa [hshape, VExpr.instL_wrapForalls] at this
  have hΓdoms : OnCtx ((doms.map (VExpr.instL lsI')).reverse ++ c.vlctx.toCtx)
      (c.venv.IsType c.lparams.length) := by
    have ⟨_, h⟩ := hwf.instL hlsI'w
    have := h.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)
    rw [hshape, VExpr.instL_wrapForalls] at this
    exact (VEnv.IsType.wrapForalls_inv c.Ewf c.Δwf.toCtx ⟨_, this⟩).1
  have hdl : (doms.map (VExpr.instL lsI')).length = doms.length := by simp
  have hnfields : info.nparams + info.numFields = doms.length := by
    rw [hnf', hnf]; omega
  -- the projections are typed along the constructor's field binders
  have hprojT : ∀ i (hi : i < info.numFields),
      c.HasType (.proj n i w') ((doms[info.nparams + i]'(by omega) |>.instL lsI').instOuter
        (P' ++ (List.range i).map fun j => VExpr.proj n j w')) := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
    intro hi
    have hkd : info.nparams + i < doms.length := by omega
    have hfieldk := VProjectionInfo.fieldType_eq_instOuter info hshape hlsI'len hP'len hkd
      (typeName := n) (major := w')
    have hFty : c.IsType ((doms[info.nparams + i].instL lsI').instOuter
        (P' ++ (List.range i).map fun j => VExpr.proj n j w')) := by
      have hdom := hΓdoms.reverse_getElem (info.nparams + i) (by simpa using hkd)
      rw [List.getElem_map] at hdom
      refine VEnv.IsType.instOuter_telescope c.Ewf
        (doms := (doms.map (VExpr.instL lsI')).take (info.nparams + i)) hdom
        (by simp [hP'len]; omega) ?_
      intro j hj hj'
      simp only [List.length_append, List.length_map, List.length_range, hP'len] at hj
      simp only [List.length_take, List.length_map] at hj'
      rw [List.getElem_take, List.getElem_map]
      rcases Nat.lt_or_ge j info.nparams with hjp | hjp
      · rw [List.getElem_append_left (by omega), List.take_append_of_le_length (by omega)]
        exact hparamsT j hjp (by omega)
      · obtain ⟨k, rfl⟩ : ∃ k, j = info.nparams + k := ⟨j - info.nparams, by omega⟩
        have hidx : (P' ++ (List.range i).map fun j => VExpr.proj n j w')[info.nparams + k] =
            .proj n k w' := by
          rw [List.getElem_append_right (by omega)]
          simp [hP'len]
        have htake : (P' ++ (List.range i).map fun j => VExpr.proj n j w').take (info.nparams + k) =
            P' ++ (List.range k).map fun j => VExpr.proj n j w' := by
          rw [List.take_append, List.take_of_length_le (l := P') (by omega), hP'len,
            Nat.add_sub_cancel_left, ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
        rw [hidx, htake]
        exact ih k (by omega) (by omega)
    have ⟨fl, hFty⟩ := hFty
    have := VEnv.IsDefEq.projDF hinfo hlsI'w hlsI'len hP'len (indexArgs := []) (by simp [hnindices])
      hfieldk hFty (by rw [List.append_nil]; exact htS) (by rw [List.append_nil]; exact htS) hclosed
      (Or.inl hguard)
    exact this
  -- the expanded constructor application
  have hargsT : ∀ j (hj : j < (P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w').length)
      (hj' : j < (doms.map (VExpr.instL lsI')).length),
      c.HasType (P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w')[j]
        ((doms.map (VExpr.instL lsI'))[j].instOuter
          ((P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w').take j)) := by
    intro j hj hj'
    simp only [List.length_append, hP'len, List.length_map, List.length_range] at hj
    simp only [List.length_map] at hj'
    rw [List.getElem_map]
    rcases Nat.lt_or_ge j info.nparams with hjp | hjp
    · rw [List.getElem_append_left (by omega), List.take_append_of_le_length (by omega)]
      exact hparamsT j hjp hj'
    · obtain ⟨k, rfl⟩ : ∃ k, j = info.nparams + k := ⟨j - info.nparams, by omega⟩
      have hidx : (P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w')[info.nparams + k]
          = .proj n k w' := by
        rw [List.getElem_append_right (by omega)]
        simp [hP'len]
      have htake : (P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w').take
          (info.nparams + k) = P' ++ (List.range k).map fun j => VExpr.proj n j w' := by
        rw [List.take_append, List.take_of_length_le (l := P') (by omega), hP'len,
          Nat.add_sub_cancel_left, ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
      rw [hidx, htake]
      exact hprojT k (by omega)
  have hctorT := VEnv.HasType.mkApps_of_telescope hcT
    (by simp [hP'len]; omega) hargsT
  -- its type is the structure type
  have hhead' : (result.instL lsI').getAppFnArgs.1 = .const n lsI' := by
    rw [VExpr.getAppFnArgs_instL]
    show (result.getAppFnArgs.1.instL lsI') = _
    rw [hhead]
    simp [VExpr.instL, VLevel.params_map_inst lsI' (hlsI'len.trans hdu.symm)]
  obtain ⟨idx', hresEq, type, htype, hname, hidxLen⟩ :=
    (hvalid.instL lsI').instOuter hhead'
      (P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w') (by simp [hP'len]; omega)
  have hidx' : idx' = [] := by
    rw [hidxs type htype hname, hnindices] at hidxLen; exact List.eq_nil_of_length_eq_zero hidxLen
  subst hidx'
  rw [hresEq, List.append_nil, hdn, List.take_left' hP'len] at hctorT
  have heta := VEnv.IsDefEq.structEta hinfo hP'len hnindices htS hctorT
  -- the executable expansion translates to it
  have hexpS : c.TrExprS ((Expr.const info.ctorName lsI).mkAppList
      (A.getAppArgsList ++ (List.range mkInfo.numFields).map fun i => Expr.proj n i w))
      (VExpr.mkApps (.const info.ctorName lsI')
        (P' ++ (List.range info.numFields).map fun j => VExpr.proj n j w')) := by
    refine TrExprS.mkAppList_of_wf (.const hctor hlsI hlenI) (hPargs.append' ?_) ⟨_, hctorT⟩
    rw [← hnf']
    refine List.forall₂_of_getElem (by simp) fun i hi hi' => ?_
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at hi
    exact .proj he ⟨_, hprojT i hi⟩
  refine .pure ⟨⟨?_, ⟨_, hexpS, ⟨_, heta⟩⟩⟩, ?_⟩
  · intro P hP hfe
    have hfA : FVarsIn P A := hfvA P hP (hfvT P hP hfe)
    rw [FVarsIn.mkAppList]
    refine ⟨?_, fun a ha => ?_⟩
    · have := hfA
      rw [← A.mkAppList_getAppArgsList, hAfn, FVarsIn.mkAppList] at this
      exact this.1
    · simp only [List.mem_append, List.mem_map, List.mem_range] at ha
      rcases ha with ha | ⟨i, -, rfl⟩
      · exact hfA.of_mem_getAppArgsList ha
      · exact hfe
  · intro Us P hs hl hP
    have hA := hlA Us P hs (hlT Us P hs hl hP) (hfvT P hs.1 hP)
    refine Expr.levelParamsIn_mkAppList ?_ fun a ha => ?_
    · have := Expr.levelParamsIn_getAppFn hA
      rw [hAfn] at this; simpa [Expr.levelParamsIn] using this
    · simp only [List.mem_append, List.mem_map, List.mem_range] at ha
      rcases ha with ha | ⟨i, -, rfl⟩
      · exact Expr.levelParamsIn_of_mem_getAppArgsList hA ha
      · exact hl

/-- Inductive recursor reduction refines the stored rules. -/
theorem inductiveReduceRec.WF_all (he : c.TrExprS e e') :
    RecM.WF c s (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
      ∀ e₁, oe = some e₁ → (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') ∧ c.LevelsBelow e e₁ := by
  unfold inductiveReduceRec
  split <;> [rename_i recFn ls hfn; exact .pure nofun]
  split <;> [rename_i info hinfo; exact .pure nofun]
  extract_lets recArgs majorIdx jpTail jpMatch
  have hrecArgs : recArgs = e.getAppArgs := rfl
  have hmajorIdx : majorIdx = info.getMajorIdx := rfl
  simp only [hrecArgs, hmajorIdx]
  split <;> [rename_i major hmajor; exact .pure nofun]
  obtain ⟨hmaj, rfl⟩ := Array.getElem?_eq_some_iff.1 hmajor
  -- the recursor spine
  have he'' : c.TrExprS ((Expr.const recFn ls).mkAppList e.getAppArgsList) e' := by
    rw [← hfn, e.mkAppList_getAppArgsList]; exact he
  have ⟨fn', stk⟩ := AppStack.build he''
  obtain ⟨ls', args', hls, rfl, hargs, hfull⟩ := stk.constantApplication
  rw [← hfn, e.mkAppList_getAppArgsList] at hfull
  have ⟨hsize, hget⟩ := AppStack.argsGet hargs
  have hmaj' : info.getMajorIdx < args'.length := by omega
  -- the K-like facts
  have .const hlc _ _ := stk.tr
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hinfo hlc
  have hfindC : c.env.constants.find? recFn = some (.recInfo info) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  obtain ⟨-, hK⟩ := c.recursorRules hfindC hsafe
  -- the tail
  have htail : ∀ {s : State} (major₂ : Expr),
      c.FVarsBelow e.getAppArgs[info.getMajorIdx] major₂ →
      c.TrExpr major₂ (args'[info.getMajorIdx]'hmaj') →
      c.LevelsBelow e.getAppArgs[info.getMajorIdx] major₂ →
      RecM.WF c s (pure (inductiveReduceRecTail info ls e.getAppArgs major₂)) fun oe _ =>
        ∀ e₁, oe = some e₁ → (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') ∧ c.LevelsBelow e e₁ := by
    refine fun major₂ hfv hm hlv => .pure fun e₁ h => ⟨inductiveReduceRecTail.WF he hfn hinfo hls
      hargs hfull hmaj hfv hm e₁ h, fun Us P hs hl hP => ?_⟩
    have hmem : e.getAppArgs[info.getMajorIdx] ∈ e.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _
    exact inductiveReduceRecTail.levelParamsIn he hfn hinfo hl
      (hlv Us P hs (Expr.levelParamsIn_of_mem_getAppArgsList hl hmem)
        (hP.of_mem_getAppArgsList hmem)) e₁ h
  -- after the K conversion
  have hjp : ∀ {s : State} (m₁ : Expr),
      c.FVarsBelow e.getAppArgs[info.getMajorIdx] m₁ →
      c.TrExpr m₁ (args'[info.getMajorIdx]'hmaj') →
      c.LevelsBelow e.getAppArgs[info.getMajorIdx] m₁ →
      RecM.WF c s (jpMatch () m₁) fun oe _ =>
        ∀ e₁, oe = some e₁ → (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') ∧ c.LevelsBelow e e₁ := by
    intro s m₁ hfv₁ hm₁ hlv₁
    simp only [jpMatch, jpTail]
    have ⟨m₁', hm₁S, hm₁defeq⟩ := hm₁
    refine (whnf.WF_below hm₁S).bind fun w _ _ ⟨hfvw, hlvw, w', hwS, hwdefeq⟩ => ?_
    have hchain : ∀ {major₂ : Expr}, c.FVarsBelow w major₂ → c.TrExpr major₂ w' →
        c.FVarsBelow e.getAppArgs[info.getMajorIdx] major₂ ∧
        c.TrExpr major₂ (args'[info.getMajorIdx]'hmaj') :=
      fun h1 h2 => ⟨hfv₁.trans (hfvw.trans h1),
        (h2.defeq c.Ewf c.Δwf hwdefeq).defeq c.Ewf c.Δwf hm₁defeq⟩
    have hlchain : ∀ {major₂ : Expr}, c.FVarsBelow w major₂ → c.LevelsBelow w major₂ →
        c.LevelsBelow e.getAppArgs[info.getMajorIdx] major₂ :=
      fun h1 h2 => (hlv₁.trans hfv₁ hlvw).trans (hfv₁.trans hfvw) h2
    split
    · rename_i n
      cases hwS with | lit _ hlit => ?_
      exact htail _ (hchain (fun _ _ _ => FVarsIn.natLitToConstructor) (hlit.trExpr c.Ewf c.Δwf)).1
        (hchain (fun _ _ _ => FVarsIn.natLitToConstructor) (hlit.trExpr c.Ewf c.Δwf)).2
        (hlchain (fun _ _ _ => FVarsIn.natLitToConstructor)
          fun _ _ _ _ _ => Expr.levelParamsIn_natLitToConstructor)
    · rename_i str _
      cases hwS with | lit _ hlit => ?_
      refine (whnf.WF_below hlit).bind fun major₂ _ _ ⟨hfv₂, hlv₂, hm₂⟩ => ?_
      have hfv₂' : c.FVarsBelow (.lit (.strVal str)) major₂ :=
        FVarsBelow.trans (e₂ := .strLitToConstructor str)
          (fun _ _ _ => FVarsIn.strLitToConstructor) hfv₂
      have hlv₂' : c.LevelsBelow (.lit (.strVal str)) major₂ := fun Us P hs _ _ =>
        hlv₂ Us P hs Expr.levelParamsIn_strLitToConstructor FVarsIn.strLitToConstructor
      exact htail _ (hchain hfv₂' hm₂).1 (hchain hfv₂' hm₂).2 (hlchain hfv₂' hlv₂')
    · refine (toCtorWhenStruct.WF_all hwS).bind fun major₂ _ _ ⟨⟨hfv₂, hm₂⟩, hlv₂⟩ => ?_
      exact htail _ (hchain hfv₂ hm₂).1 (hchain hfv₂ hm₂).2 (hlchain hfv₂ hlv₂)
  split
  · exact (toCtorWhenK.WF_all ‹_› (hK ‹_›) (hget _ hmaj)).bind
      fun m₁ _ _ ⟨⟨h1, h2⟩, h3⟩ => hjp m₁ h1 h2 h3
  · exact hjp _ .rfl ((hget _ hmaj).trExpr c.Ewf c.Δwf) .rfl

theorem inductiveReduceRec.WF (he : c.TrExprS e e') :
    RecM.WF c s (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  (inductiveReduceRec.WF_all he).mono fun _ _ _ H e₁ h => (H e₁ h).1

theorem TrExprS.getAppArgs_get (he : c.TrExprS e e') (i) (hi : i < e.getAppArgs.size) :
    ∃ a', c.TrExprS e.getAppArgs[i] a' := by
  have ⟨_, stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
  have ⟨args', hargs, _⟩ := stk.translatedArguments
  exact ⟨_, (AppStack.argsGet hargs).2 i hi⟩

/-- Quotient reduction stays in every universe scope of the eliminator application: the result
is assembled from its arguments and the reduced `Quot.mk` application. -/
theorem quotReduceRecCont.WF_levels (he : c.TrExprS e e') :
    RecM.WF c s (quotReduceRecCont e whnf mkPos argPos) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.LevelsBelow e e₁ := by
  unfold quotReduceRecCont
  extract_lets args
  have hargs_eq : args = e.getAppArgs := rfl
  simp only [hargs_eq]
  split <;> [rename_i h5; exact .pure nofun]
  have ⟨_, ha⟩ := TrExprS.getAppArgs_get he _ h5
  refine (whnf.WF_below ha).bind fun mk _ _ ⟨_, hml, _⟩ => ?_
  split <;> [exact .pure nofun; rename_i hnot]
  have hisApp : mk.isAppOfArity ``Quot.mk 3 = true := by simpa using hnot
  obtain ⟨lsm, a1, a2, a3, rfl⟩ := Expr.isAppOfArity_three_eq_true hisApp
  simp only [Expr.appArg!]
  have main : ∀ Us P, c.UniverseScope Us P → e.levelParamsIn Us = true → FVarsIn P e →
      (Expr.app e.getAppArgs[argPos]! a3).levelParamsIn Us = true := by
    intro Us P hs hl hP
    have hall := fun a (h : a ∈ e.getAppArgs) => Expr.levelParamsIn_of_mem_getAppArgs hl h
    have hm := hml Us P hs (hall _ (Array.getElem_mem _)) (hP.of_mem_getAppArgsList (by
      rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hm ⊢
    exact ⟨Expr.levelParamsIn_getElem!_of_forall hall _, hm.2⟩
  split
  · exact .pure fun _ h Us P hs hl hP => Option.some.inj h ▸
      Expr.levelParamsIn_mkAppRange (main Us P hs hl hP)
        fun a h => Expr.levelParamsIn_of_mem_getAppArgs hl h
  · exact .pure fun _ h Us P hs hl hP => Option.some.inj h ▸ main Us P hs hl hP

theorem quotReduceRec.WF_levels (he : c.TrExprS e e') :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ => ∀ e₁, oe = some e₁ → c.LevelsBelow e e₁ := by
  unfold quotReduceRec
  split <;> [skip; exact .pure nofun]
  split
  · exact quotReduceRecCont.WF_levels he
  split
  · exact quotReduceRecCont.WF_levels he
  exact .pure nofun

end Inner
end TypeChecker
end Lean4Lean
