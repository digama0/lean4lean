import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Header.Check

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

theorem _root_.Lean4Lean.FVarsIn.getAppArgsList
    (H : FVarsIn P e) (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  have H' : FVarsIn P
      (e.getAppFn.mkAppRevList e.getAppArgsRevList) := by
    rw [Expr.mkAppRevList_getAppArgsRevList]
    exact H
  have ha' : a ∈ e.getAppArgsRevList := by
    simpa [← Expr.getAppArgsList_reverse] using ha
  exact (FVarsIn.mkAppRevList.mp H').2 a ha'

/-- Abstracting a free variable removes precisely that variable from the
free-variable obligation. This is the structural lemma needed for nested
parameter replacement, which goes through the opaque executable `Expr.abstract`. -/
theorem _root_.Lean4Lean.FVarsIn.abstract1_of
    (H : FVarsIn (fun fv => fv = selected ∨ P fv) e) :
    FVarsIn P (Expr.abstract1 selected e k) := by
  induction e generalizing k <;>
    simp_all [Lean4Lean.FVarsIn, Expr.abstract1]
  case fvar fv =>
    split
    · trivial
    · rename_i hne
      rcases H with heq | hP
      · subst fv
        simp at hne
      · exact hP

/-- Abstracting a list of selected variables removes the entire selection
from the free-variable obligation. -/
theorem _root_.Lean4Lean.FVarsIn.abstractList_of
    (H : FVarsIn (fun fv => fv ∈ selected ∨ P fv) e) :
    FVarsIn P (e.abstractList selected k) := by
  induction selected generalizing e with
  | nil => simpa [Expr.abstractList] using H
  | cons selected rest ih =>
    simp only [Expr.abstractList]
    apply ih
    apply FVarsIn.abstract1_of
    exact H.mono fun fv hfv => by
      rcases hfv with hmem | hP
      · rcases List.mem_cons.mp hmem with heq | hrest
        · exact Or.inl heq
        · exact Or.inr (Or.inl hrest)
      · exact Or.inr (Or.inr hP)

/-- An index front built in the checking scope closes back to its
base, even when the executable `MLCtx` contains an interleaved ambient
prefix below that front.  `FrontFVLift` records the fact that each
new executable domain depends only on the preceding checking scope, while the
context equality identifies those dependency lists with the executable
declarations selected by `MLCtx.mkForall`. -/
theorem _root_.Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.FrontFVLift.mkForall_fvarsIn_sourceBase
    {sourceDomains expandedDomains : List VExpr}
    {scope expanded : VLCtx} {shift : Lift}
    {m : TypeChecker.MLCtx} {env : VEnv} {Us : List Name}
    (H : Lean4Lean.VerifyInductive.checkInductiveTypes.loopType.FrontFVLift
      sourceDomains expandedDomains scope expanded shift)
    (Hm : MLCtxOnlyLams m) (Hmwf : m.WF env Us)
    (Hctx : VLCtx.IsDefEq env Us.length expanded m.vlctx)
    (hn : sourceDomains.length ≤ m.length) (body : Expr)
    (Hbody : body.FVarsIn (· ∈ scope.fvars)) :
    (m.mkForall sourceDomains.length hn body).FVarsIn
      (· ∈ VLCtx.fvars (scope.drop sourceDomains.length)) := by
  induction H generalizing m body with
  | zero => simpa using Hbody
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    cases m with
    | nil => cases Hctx
    | vlam current name type type' bi tail =>
      cases Hctx with
      | cons Htail _ _ =>
        have hnTail : sourceDomains.length ≤ tail.length := by
          apply Nat.le_of_succ_le_succ
          simpa using hn
        have Hdomain : type.FVarsIn (· ∈ scope.fvars) := by
          apply fvarsIn_iff.mpr
          refine ⟨hdeps, ?_⟩
          exact Hmwf.2.2.1.fvarsIn.mono fun _ _ => trivial
        have Habstract : (body.abstract1 fv).FVarsIn
            (· ∈ scope.fvars) := by
          apply FVarsIn.abstract1_of
          exact Hbody.mono fun current hcurrent => by
            simpa only [VLCtx.fvars_cons_some, List.mem_cons] using hcurrent
        simpa only [List.length_append, List.length_singleton,
          Nat.add_one, TypeChecker.MLCtx.mkForall,
          TypeChecker.MLCtx.dropN, List.drop_succ_cons] using
          ih Hm.tail_vlam Hmwf.1 Htail hnTail
            (.forallE name type (body.abstract1 fv) bi)
            ⟨Hdomain, Habstract⟩
    | vlet current name type value type' value' tail =>
      exact Hm.vlet_false.elim

theorem _root_.Lean4Lean.FVarsIn.abstractN_of {P : FVarId → Prop} {xs : List FVarId} :
    ∀ {e : Expr} {k}, FVarsIn (fun fv => fv ∈ xs ∨ P fv) e → FVarsIn P (e.abstractN xs k)
  | .bvar _, _, _ => trivial
  | .fvar v, k, h => by
    simp only [Expr.abstractN]
    split
    · trivial
    · rename_i hnone
      exact h.resolve_left (Expr.lastRevIdx?_eq_none_iff.1 hnone)
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .lit _, _, h => h
  | .mvar _, _, h => h
  | .mdata _ e, k, h => FVarsIn.abstractN_of (e := e) h
  | .proj _ _ e, k, h => FVarsIn.abstractN_of (e := e) h
  | .app f a, k, h => ⟨FVarsIn.abstractN_of (e := f) h.1, FVarsIn.abstractN_of (e := a) h.2⟩
  | .lam _ t b _, k, h => ⟨FVarsIn.abstractN_of (e := t) h.1, FVarsIn.abstractN_of (e := b) h.2⟩
  | .forallE _ t b _, k, h =>
    ⟨FVarsIn.abstractN_of (e := t) h.1, FVarsIn.abstractN_of (e := b) h.2⟩
  | .letE _ t v b _, k, h =>
    ⟨FVarsIn.abstractN_of (e := t) h.1, FVarsIn.abstractN_of (e := v) h.2.1,
      FVarsIn.abstractN_of (e := b) h.2.2⟩

theorem _root_.Lean4Lean.FVarsIn.abstract_fvarArray_of
    (fvars : List FVarId) (selected : Array Expr)
    (hselected : selected = (fvars.map Expr.fvar).toArray)
    (H : FVarsIn (fun fv => fv ∈ fvars ∨ P fv) e) :
    FVarsIn P (e.abstract selected) := by
  rw [hselected, Expr.abstractN_eq]
  exact H.abstractN_of

/-- `instantiateRev` introduces no free variables beyond those already in
the body and substitution array. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateRev
    (He : FVarsIn P e) (Hsubst : ∀ a ∈ subst, FVarsIn P a) :
    FVarsIn P (e.instantiateRev subst) := by
  rw [Expr.instantiateRev_eq, Expr.instantiate_eq]
  apply He.instantiateList
  intro a ha
  apply Hsubst a
  simpa using ha

/-- Range-restricted reverse instantiation has the same free-variable
discipline as the underlying simultaneous instantiation. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateRevRange
    (He : FVarsIn P e) (Hsubst : ∀ a ∈ subst, FVarsIn P a) :
    FVarsIn P (e.instantiateRevRange start stop subst) := by
  rw [Expr.instantiateRevRange_eq]
  apply He.instantiateRev
  intro a ha
  rcases Array.mem_iff_getElem.mp ha with ⟨i, hi, heq⟩
  have hi' : start + i < subst.size := by
    rw [Array.size_extract] at hi
    have hmin := Nat.min_le_right stop subst.size
    omega
  apply Hsubst a
  rw [← heq, Array.getElem_extract]
  exact Array.getElem_mem hi'

/-- Replacing universe parameters by universe expressions without metavariables
does not introduce a universe metavariable. -/
theorem _root_.Lean.Level.substParams'_hasMVar_false
    (Hu : u.hasMVar' = false)
    (Hs : ∀ name, (s name).hasMVar' = false) :
    (Lean.Level.substParams' s red u).hasMVar' = false := by
  induction u generalizing red with
  | zero | param | mvar => simp_all [Lean.Level.substParams', Lean.Level.hasMVar']
  | succ u ih =>
      simp only [Lean.Level.substParams', Lean.Level.hasMVar'] at Hu ⊢
      exact ih Hu
  | max u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]
  | imax u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelIMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]

/-- Universe-parameter instantiation preserves the expression free-variable
predicate when every supplied universe is metavariable-free. -/
theorem _root_.Lean4Lean.FVarsIn.instantiateLevelParams
    (He : FVarsIn P e)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false) :
    FVarsIn P (e.instantiateLevelParams levelParams levels) := by
  rw [Expr.instantiateLevelParams_eq]
  have Hsubst : ∀ name,
      (((levelParams.idxOf? name).bind fun i => levels[i]?).getD
        (.param name)).hasMVar' = false := by
    intro name
    cases hidx : levelParams.idxOf? name with
    | none => simp [Lean.Level.hasMVar']
    | some i =>
      cases hget : levels[i]? with
      | none => simp [hget, Lean.Level.hasMVar']
      | some level =>
        simp only [Option.bind_some, hget, Option.getD_some]
        have hi : i < levels.length := by
          by_contra hnot
          have hnone := List.getElem?_eq_none (Nat.le_of_not_gt hnot)
          rw [hget] at hnone
          contradiction
        have heq : levels[i]'hi = level := by
          rw [← Option.some.injEq, ← hget]
          exact (List.getElem?_eq_getElem hi).symm
        exact Hlevels level (heq ▸ List.getElem_mem hi)
  induction e <;>
    simp_all [Expr.instantiateLevelParamsCore', Lean4Lean.FVarsIn,
      Lean.Level.substParams'_hasMVar_false]

theorem _root_.Lean4Lean.FVarsIn.mkAppRange_zero
    (hn : n ≤ args.size) (Hfn : FVarsIn P fn)
    (Hargs : ∀ arg ∈ args, FVarsIn P arg) :
    FVarsIn P (mkAppRange fn 0 n args) := by
  rw [Expr.mkAppRange_eq (l₁ := []) (l₂ := args.toList.take n)
    (l₃ := args.toList.drop n)]
  · rw [FVarsIn.mkAppList]
    refine ⟨Hfn, ?_⟩
    intro arg harg
    apply Hargs arg
    apply Array.mem_toList_iff.mp
    exact List.mem_of_mem_take harg
  · simp
  · rfl
  · simp [List.length_take, Nat.min_eq_left (by simpa using hn)]

theorem _root_.Lean4Lean.Expr.eqv_fvar_eq
    (H : (((.fvar fv : Expr) == e)) = true) : e = .fvar fv := by
  cases e <;> simp [(· == ·), Expr.eqv'] at H
  rename_i fv'
  have : fv = fv' := beq_iff_eq.mp H
  cases this
  rfl
end VerifyInductive
end Lean4Lean
