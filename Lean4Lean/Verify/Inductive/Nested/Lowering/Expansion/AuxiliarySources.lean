import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliaryHeads
import Lean4Lean.Verify.Inductive.Nested.Lowering.AuxiliaryConstructors
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Contexts
import Lean4Lean.Verify.Inductive.Nested.Install.Permutation
import Lean4Lean.Verify.Inductive.RecursorInput

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Sources of the auxiliary families for nested formation

This module joins the concrete auxiliary builder to the independently
validated, closed translation of each cached nested application.  For every auxiliary slot
of the lowering queue it constructs the pre-lowering auxiliary family as a specialization of
its installed container (`AuxiliaryFamilySource`, `AuxiliaryFamilySources`), interprets
every replaced occurrence by that source (`AuxiliaryFamilySources.replacementCompat`), and
assembles the ordered nested expansion of the whole lowered queue
(`NestedLowering.allExpansionsOfSources`) required by `NestedFormationWF`.  The results are
indexed by the auxiliary family of each slot (`LoweredAuxiliaryFamily`); no replacement or
compatibility fact is supplied by the caller.
-/

private theorem Expr.eqvPrime_getAppFn {left right : Expr}
    (H : left.eqv' right = true) :
    left.getAppFn.eqv' right.getAppFn = true := by
  induction left generalizing right with
    | app leftFn leftArg ih =>
      cases right <;> simp [Expr.eqv', Expr.getAppFn] at H ⊢
      exact ih H.1
    | _ =>
      cases right <;> simp_all [Expr.eqv', Expr.getAppFn]

private theorem Expr.eqvPrime_getAppArgsListAux {left right : Expr}
    {leftArgs rightArgs : List Expr}
    (H : left.eqv' right = true) :
    List.Forall₂ (fun left right => left.eqv' right = true)
      leftArgs rightArgs →
    List.Forall₂ (fun left right => left.eqv' right = true)
      (left.getAppArgsList leftArgs) (right.getAppArgsList rightArgs) := by
  intro Hargs
  induction left generalizing right leftArgs rightArgs with
    | app leftFn leftArg ih =>
      cases right <;> simp [Expr.eqv'] at H
      rename_i rightFn rightArg
      exact ih (right := rightFn) H.1 (.cons H.2 Hargs)
    | _ =>
      cases right <;> simp_all [Expr.eqv', Expr.getAppArgsList]

/-- Expression equivalence preserves the ordered maximal application
arguments pointwise. -/
theorem Expr.eqv_getAppArgsList {left right : Expr}
    (H : left == right) :
    List.Forall₂ (· == ·) left.getAppArgsList right.getAppArgsList := by
  have H' : left.eqv' right = true := by
    simpa only [(· == ·), Expr.eqv_eq] using H
  have Hargs := Expr.eqvPrime_getAppArgsListAux H' (.nil)
  simpa only [(· == ·), Expr.eqv_eq] using Hargs

theorem Expr.abstractList_mkAppList (head : Expr) (args : List Expr)
    (fvars : List FVarId) (depth : Nat := 0) :
    (Expr.mkAppList head args).abstractList fvars depth =
      Expr.mkAppList (head.abstractList fvars depth)
        (args.map fun arg => arg.abstractList fvars depth) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    simpa only [Expr.mkAppList, List.map_cons, Expr.abstractList_app] using
      ih (.app head arg)

/-- A reused replacement and the auxiliary family of the queue selected by its
cache key close the same source container application, up to Lean expression
equivalence.  The proof cancels the two concrete parameter openings using the
parameter selections and scope invariants retained by lowering. -/
theorem LoweredOccurrenceSpine.cachedSourceApplicationEqv
    {Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result traceFinalState}
    {Hselection : CDeclArray lctx As}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    (T : LoweredOccurrenceSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (O : CachedAuxiliaryFamily prodEnv result.params nparams
      initialSize runFinalState T.nested T.auxName)
    (resultSelection : CDeclArray result.lctx result.params)
    (hresultNodup : resultSelection.fvars.Nodup)
    (hselectionNodup : Hselection.fvars.Nodup)
    (hAs : As.size = result.params.size)
    (Hscope : input.FVarsIn (· ∈ Hselection.fvars)) :
    let currentSource := mkAppRange (.const T.targetName T.levels) 0
      T.value.numParams input.getAppArgs
    let generatedSource := mkAppRange
      (.const O.origin.generated.sourceName O.origin.generated.levels) 0
      O.origin.generated.nestedNParams O.origin.generated.args
    currentSource.abstractList Hselection.fvars ==
      generatedSource.abstractList O.origin.generated.selection.fvars := by
  dsimp only
  let currentSource := mkAppRange (.const T.targetName T.levels) 0
    T.value.numParams input.getAppArgs
  let currentClosed := currentSource.abstract As
  have HcurrentClosed : currentClosed.FVarsIn (fun _ => False) := by
    exact T.candidate.abstractedPrefixClosed Hselection Hscope T.inputHead
  have Haway : currentClosed.FVarsIn
      (fun fv => fv ∉ resultSelection.fvars) :=
    HcurrentClosed.mono fun _ hfalse => False.elim hfalse
  have hprefix : currentSource.looseBVarRange' = 0 :=
    T.candidate.prefixLooseBVarRange_zero (.const T.targetName T.levels) rfl
  have hlb : currentClosed.looseBVarRange' ≤ resultSelection.fvars.length := by
    have hbound := Expr.abstractN_looseBVarRange_le (e := currentSource)
      (fvs := Hselection.fvars) (k := 0)
    rw [hprefix] at hbound
    have h1 : Hselection.fvars.length = As.size := by
      simpa using (congrArg Array.size Hselection.expressions).symm
    have h2 : resultSelection.fvars.length = result.params.size := by
      simpa using (congrArg Array.size resultSelection.expressions).symm
    have hrw : currentClosed = currentSource.abstractN Hselection.fvars := by
      simp only [currentClosed, Hselection.expressions, Expr.abstractN_eq]
    rw [hrw]
    omega
  have hcancel := Haway.abstract_instantiateRev_fvarArray result.params
    resultSelection.fvars resultSelection.expressions hresultNodup hlb
  have hcurrent : T.nested.abstract result.params == currentClosed := by
    have Habstract := Expr.abstractN_eqv
      (xs := resultSelection.fvars) (k := 0)
      T.nested_eq
    have hcancelN :
        (currentClosed.instantiateRev result.params).abstractN
          resultSelection.fvars = currentClosed := by
      have h := hcancel
      simp only [resultSelection.expressions, Expr.abstractN_eq] at h ⊢
      exact h
    rw [hcancelN] at Habstract
    simpa only [resultSelection.expressions, Expr.abstractN_eq] using Habstract
  have hgenerated : O.origin.generated.data.nested.abstract result.params =
      (mkAppRange
        (.const O.origin.generated.sourceName O.origin.generated.levels) 0
        O.origin.generated.nestedNParams O.origin.generated.args).abstractList
          O.origin.generated.selection.fvars :=
    O.origin.generated.cachedClosureAlphaExact resultSelection hresultNodup
  have hclosedEqv : currentClosed ==
      (mkAppRange
        (.const O.origin.generated.sourceName O.origin.generated.levels) 0
        O.origin.generated.nestedNParams O.origin.generated.args).abstractList
          O.origin.generated.selection.fvars := by
    rw [← hgenerated, O.nested_eq]
    exact BEq.symm hcurrent
  have hcurrentAbstract : currentClosed =
      currentSource.abstractList Hselection.fvars := by
    simp only [currentClosed, Hselection.expressions]
    exact Expr.abstract_eq_of_closed _ _ hselectionNodup hprefix
  rw [← hcurrentAbstract]
  exact hclosedEqv

/-- Head and ordered parameter-spine consequences of the cache alpha law. -/
theorem LoweredOccurrenceSpine.cachedSourceSpines
    {Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result traceFinalState}
    {Hselection : CDeclArray lctx As}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    (T : LoweredOccurrenceSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (O : CachedAuxiliaryFamily prodEnv result.params nparams
      initialSize runFinalState T.nested T.auxName)
    (resultSelection : CDeclArray result.lctx result.params)
    (hresultNodup : resultSelection.fvars.Nodup)
    (hselectionNodup : Hselection.fvars.Nodup)
    (hAs : As.size = result.params.size)
    (Hscope : input.FVarsIn (· ∈ Hselection.fvars)) :
    T.targetName = O.origin.generated.sourceName ∧
    T.levels = O.origin.generated.levels ∧
    List.Forall₂ (· == ·)
      ((input.getAppArgsList.take T.value.numParams).map
        (fun arg => arg.abstractList Hselection.fvars))
      ((O.origin.generated.args.toList.take
        O.origin.generated.nestedNParams).map
          (fun arg => arg.abstractList O.origin.generated.selection.fvars)) := by
  have Halpha := T.cachedSourceApplicationEqv O resultSelection
    hresultNodup hselectionNodup hAs Hscope
  have hcurrent :
      (mkAppRange (.const T.targetName T.levels) 0 T.value.numParams
        input.getAppArgs).abstractList Hselection.fvars =
      Expr.mkAppList (.const T.targetName T.levels)
        ((input.getAppArgsList.take T.value.numParams).map
          (fun arg => arg.abstractList Hselection.fvars)) := by
    rw [Expr.mkAppRange_from_zero _ _ _ T.candidate.parameters.arity]
    simp only [Expr.abstractList_mkAppList, Expr.abstractList_const,
      Expr.getAppArgs_toList]
  have hgenerated :
      (mkAppRange
        (.const O.origin.generated.sourceName O.origin.generated.levels) 0
        O.origin.generated.nestedNParams O.origin.generated.args).abstractList
          O.origin.generated.selection.fvars =
      Expr.mkAppList
        (.const O.origin.generated.sourceName O.origin.generated.levels)
        ((O.origin.generated.args.toList.take
          O.origin.generated.nestedNParams).map
            (fun arg =>
              arg.abstractList O.origin.generated.selection.fvars)) := by
    rw [Expr.mkAppRange_from_zero _ _ _ O.origin.generated.argsArity]
    simp only [Expr.abstractList_mkAppList, Expr.abstractList_const]
  dsimp only at Halpha
  rw [hcurrent, hgenerated] at Halpha
  have Halpha' :
      (Expr.mkAppList (.const T.targetName T.levels)
          ((input.getAppArgsList.take T.value.numParams).map
            (fun arg => arg.abstractList Hselection.fvars))).eqv'
        (Expr.mkAppList
          (.const O.origin.generated.sourceName O.origin.generated.levels)
          ((O.origin.generated.args.toList.take
            O.origin.generated.nestedNParams).map
              (fun arg =>
                arg.abstractList O.origin.generated.selection.fvars))) = true := by
    simpa only [(· == ·), Expr.eqv_eq] using Halpha
  have Hhead := Expr.eqvPrime_getAppFn Halpha'
  have Hargs := Expr.eqv_getAppArgsList Halpha
  have hhead : T.targetName = O.origin.generated.sourceName ∧
      T.levels = O.origin.generated.levels := by
    simpa only [Expr.getAppFn_mkAppList_const, Expr.eqv', beq_iff_eq,
      Bool.and_eq_true] using Hhead
  refine ⟨hhead.1, hhead.2, ?_⟩
  simpa only [Expr.getAppArgsList_mkAppList_const] using Hargs

/-- Context invariant for comparing a parameter-abstracted translation retained by
lowering with the live translation at a replaced occurrence.  `abstractDepth`
counts concrete binders (including erased lets), while `targetDepth` counts
the binders that survive in `VExpr`.  The retained target is weakened by the
already-open constructor fields before it is compared with the live target. -/
structure ParameterExpansionCtx
    (leaf : Nat → VExpr → VExpr → Prop)
    (fvars : List FVarId) (fieldDepth abstractDepth targetDepth : Nat)
    (canonicalCtx currentCtx : VLCtx) : Prop where
  selected : ∀ (i : Nat) (hi : i < fvars.length)
      {canonicalValue canonicalType currentValue currentType : VExpr},
    canonicalCtx.find? (.inl
      (abstractDepth + (fvars.length - 1 - i))) =
        some (canonicalValue, canonicalType) →
    currentCtx.find? (.inr fvars[i]) =
        some (currentValue, currentType) →
    VExpr.NestedExprExpansion leaf
      (fvars.length + fieldDepth + targetDepth)
      (canonicalValue.liftN fieldDepth targetDepth) currentValue
  localLookup : ∀ (i : Nat) (_hi : i < abstractDepth)
      {canonicalValue canonicalType currentValue currentType : VExpr},
    canonicalCtx.find? (.inl i) =
        some (canonicalValue, canonicalType) →
    currentCtx.find? (.inl i) = some (currentValue, currentType) →
    VExpr.NestedExprExpansion leaf
      (fvars.length + fieldDepth + targetDepth)
      (canonicalValue.liftN fieldDepth targetDepth) currentValue

/-- The anonymous de Bruijn parameter context and the live selected-parameter
context satisfy the comparison invariant before entering expression-local
binders. -/
theorem ParameterExpansionCtx.base
    (hdomains : domains.length = fvars.length)
    (Hparams : SelectedParameterTargets fvars fieldDepth currentCtx) :
    ParameterExpansionCtx leaf fvars fieldDepth 0 0
      (abstractForallContext domains []) currentCtx := by
  refine ⟨?_, ?_⟩
  · intro i hi canonicalValue canonicalType currentValue currentType
      Hcanonical Hcurrent
    have hiDomains : fvars.length - 1 - i < domains.length := by omega
    rcases abstractForallContext.find?_bvar domains []
        (fvars.length - 1 - i) hiDomains with
      ⟨canonicalType', Hcanonical'⟩
    have Hcanonical0 :
        (abstractForallContext domains []).find?
            (.inl (fvars.length - 1 - i)) =
          some (canonicalValue, canonicalType) := by
      simpa using Hcanonical
    have hcanonicalValue : canonicalValue =
        .bvar (fvars.length - 1 - i) := by
      rw [Hcanonical'] at Hcanonical0
      exact congrArg Prod.fst (Option.some.inj Hcanonical0).symm
    rcases Hparams i hi with ⟨currentType', Hcurrent'⟩
    have hcurrentValue : currentValue =
        .bvar (fieldDepth + (fvars.length - 1 - i)) := by
      rw [Hcurrent'] at Hcurrent
      exact congrArg Prod.fst (Option.some.inj Hcurrent).symm
    subst canonicalValue
    subst currentValue
    simpa [VExpr.liftN, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      (VExpr.NestedExprExpansion.bvar
        (leaf := leaf)
        (depth := fvars.length + fieldDepth)
        (index := fieldDepth + (fvars.length - 1 - i)))
  · intro i hi
    omega

/-- Entering a surviving lambda/forall binder advances both concrete
abstraction depth and abstract target depth. -/
theorem ParameterExpansionCtx.vlam
    (H : ParameterExpansionCtx leaf fvars fieldDepth abstractDepth
      targetDepth canonicalCtx currentCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf) :
    ParameterExpansionCtx leaf fvars fieldDepth
      (abstractDepth + 1) (targetDepth + 1)
      ((none, .vlam canonicalType) :: canonicalCtx)
      ((none, .vlam currentType) :: currentCtx) := by
  refine ⟨?_, ?_⟩
  · intro i hi canonicalValue canonicalValueType currentValue
      currentValueType Hcanonical Hcurrent
    have hindex : abstractDepth + 1 + (fvars.length - 1 - i) =
        (abstractDepth + (fvars.length - 1 - i)) + 1 := by omega
    rw [hindex] at Hcanonical
    cases hcanonicalOld : canonicalCtx.find? (.inl
        (abstractDepth + (fvars.length - 1 - i))) with
    | none =>
        have : False := by
          simp [VLCtx.find?, VLCtx.next, hcanonicalOld] at Hcanonical
        exact this.elim
    | some canonicalPair =>
      rcases canonicalPair with ⟨canonicalOld, canonicalOldType⟩
      cases hcurrentOld : currentCtx.find? (.inr fvars[i]) with
      | none =>
          simp [VLCtx.find?, VLCtx.next, hcurrentOld] at Hcurrent
      | some currentPair =>
        rcases currentPair with ⟨currentOld, currentOldType⟩
        have hcanonicalValue : canonicalValue = canonicalOld.liftN 1 0 := by
          have Hpair :
              some (canonicalOld.liftN 1 0,
                canonicalOldType.liftN 1 0) =
                some (canonicalValue, canonicalValueType) := by
            simpa [VLCtx.find?, VLCtx.next, hcanonicalOld,
              VLocalDecl.depth] using Hcanonical
          exact congrArg Prod.fst (Option.some.inj Hpair).symm
        have hcurrentValue : currentValue = currentOld.liftN 1 0 := by
          have Hpair :
              some (currentOld.liftN 1 0, currentOldType.liftN 1 0) =
                some (currentValue, currentValueType) := by
            simpa [VLCtx.find?, VLCtx.next, hcurrentOld,
              VLocalDecl.depth] using Hcurrent
          exact congrArg Prod.fst (Option.some.inj Hpair).symm
        subst canonicalValue
        subst currentValue
        have Hold := H.selected i hi hcanonicalOld hcurrentOld
        have Hnext := VExpr.NestedExprExpansion.liftDepth Hlift Hold 0
          (Nat.zero_le _)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          VExpr.lift, VExpr.lift_liftN'] using Hnext
  · intro i hi canonicalValue canonicalValueType currentValue
      currentValueType Hcanonical Hcurrent
    cases i with
    | zero =>
        have hcanonicalValue : canonicalValue = .bvar 0 := by
          simpa [VLCtx.find?, VLCtx.next, VLocalDecl.value] using
            congrArg Prod.fst (Option.some.inj Hcanonical).symm
        have hcurrentValue : currentValue = .bvar 0 := by
          simpa [VLCtx.find?, VLCtx.next, VLocalDecl.value] using
            congrArg Prod.fst (Option.some.inj Hcurrent).symm
        subst canonicalValue
        subst currentValue
        simpa [VExpr.liftN] using
          (VExpr.NestedExprExpansion.bvar
            (leaf := leaf)
            (depth := fvars.length + fieldDepth + (targetDepth + 1))
            (index := 0))
    | succ i =>
      have hiOld : i < abstractDepth := by omega
      cases hcanonicalOld : canonicalCtx.find? (.inl i) with
      | none =>
          simp [VLCtx.find?, VLCtx.next, hcanonicalOld] at Hcanonical
      | some canonicalPair =>
        rcases canonicalPair with ⟨canonicalOld, canonicalOldType⟩
        cases hcurrentOld : currentCtx.find? (.inl i) with
        | none =>
            simp [VLCtx.find?, VLCtx.next, hcurrentOld] at Hcurrent
        | some currentPair =>
          rcases currentPair with ⟨currentOld, currentOldType⟩
          have hcanonicalValue : canonicalValue = canonicalOld.liftN 1 0 := by
            have Hpair :
                some (canonicalOld.liftN 1 0,
                  canonicalOldType.liftN 1 0) =
                  some (canonicalValue, canonicalValueType) := by
              simpa [VLCtx.find?, VLCtx.next, hcanonicalOld,
                VLocalDecl.depth] using Hcanonical
            exact congrArg Prod.fst (Option.some.inj Hpair).symm
          have hcurrentValue : currentValue = currentOld.liftN 1 0 := by
            have Hpair :
                some (currentOld.liftN 1 0, currentOldType.liftN 1 0) =
                  some (currentValue, currentValueType) := by
              simpa [VLCtx.find?, VLCtx.next, hcurrentOld,
                VLocalDecl.depth] using Hcurrent
            exact congrArg Prod.fst (Option.some.inj Hpair).symm
          subst canonicalValue
          subst currentValue
          have Hold := H.localLookup i hiOld hcanonicalOld hcurrentOld
          have Hnext := VExpr.NestedExprExpansion.liftDepth Hlift Hold 0
            (Nat.zero_le _)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            VExpr.lift, VExpr.lift_liftN'] using Hnext

/-- Entering an erased let advances concrete abstraction depth but leaves the
abstract target depth unchanged; the stored let value supplies the new local
variable comparison. -/
theorem ParameterExpansionCtx.vlet
    (H : ParameterExpansionCtx leaf fvars fieldDepth abstractDepth
      targetDepth canonicalCtx currentCtx)
    (Hvalue : VExpr.NestedExprExpansion leaf
      (fvars.length + fieldDepth + targetDepth)
      (canonicalValue.liftN fieldDepth targetDepth) currentValue) :
    ParameterExpansionCtx leaf fvars fieldDepth
      (abstractDepth + 1) targetDepth
      ((none, .vlet canonicalType canonicalValue) :: canonicalCtx)
      ((none, .vlet currentType currentValue) :: currentCtx) := by
  refine ⟨?_, ?_⟩
  · intro i hi foundCanonical foundCanonicalType foundCurrent
      foundCurrentType Hcanonical Hcurrent
    have hindex : abstractDepth + 1 + (fvars.length - 1 - i) =
        (abstractDepth + (fvars.length - 1 - i)) + 1 := by omega
    rw [hindex] at Hcanonical
    cases hcanonicalOld : canonicalCtx.find? (.inl
        (abstractDepth + (fvars.length - 1 - i))) with
    | none =>
        have : False := by
          simp [VLCtx.find?, VLCtx.next, hcanonicalOld] at Hcanonical
        exact this.elim
    | some canonicalPair =>
      rcases canonicalPair with ⟨canonicalOld, canonicalOldType⟩
      cases hcurrentOld : currentCtx.find? (.inr fvars[i]) with
      | none =>
          simp [VLCtx.find?, VLCtx.next, hcurrentOld] at Hcurrent
      | some currentPair =>
        rcases currentPair with ⟨currentOld, currentOldType⟩
        have hfoundCanonical : foundCanonical = canonicalOld := by
          have Hpair : some (canonicalOld, canonicalOldType) =
              some (foundCanonical, foundCanonicalType) := by
            simpa [VLCtx.find?, VLCtx.next, hcanonicalOld,
              VLocalDecl.depth] using Hcanonical
          exact congrArg Prod.fst (Option.some.inj Hpair).symm
        have hfoundCurrent : foundCurrent = currentOld := by
          have Hpair : some (currentOld, currentOldType) =
              some (foundCurrent, foundCurrentType) := by
            simpa [VLCtx.find?, VLCtx.next, hcurrentOld,
              VLocalDecl.depth] using Hcurrent
          exact congrArg Prod.fst (Option.some.inj Hpair).symm
        subst foundCanonical
        subst foundCurrent
        simpa [Nat.add_assoc] using
          H.selected i hi hcanonicalOld hcurrentOld
  · intro i hi foundCanonical foundCanonicalType foundCurrent
      foundCurrentType Hcanonical Hcurrent
    cases i with
    | zero =>
        have hfoundCanonical : foundCanonical = canonicalValue := by
          simpa [VLCtx.find?, VLCtx.next, VLocalDecl.value] using
            congrArg Prod.fst (Option.some.inj Hcanonical).symm
        have hfoundCurrent : foundCurrent = currentValue := by
          simpa [VLCtx.find?, VLCtx.next, VLocalDecl.value] using
            congrArg Prod.fst (Option.some.inj Hcurrent).symm
        subst foundCanonical
        subst foundCurrent
        simpa [Nat.add_assoc] using Hvalue
    | succ i =>
      have hiOld : i < abstractDepth := by omega
      cases hcanonicalOld : canonicalCtx.find? (.inl i) with
      | none =>
          simp [VLCtx.find?, VLCtx.next, hcanonicalOld] at Hcanonical
      | some canonicalPair =>
        rcases canonicalPair with ⟨canonicalOld, canonicalOldType⟩
        cases hcurrentOld : currentCtx.find? (.inl i) with
        | none =>
            simp [VLCtx.find?, VLCtx.next, hcurrentOld] at Hcurrent
        | some currentPair =>
          rcases currentPair with ⟨currentOld, currentOldType⟩
          have hfoundCanonical : foundCanonical = canonicalOld := by
            have Hpair : some (canonicalOld, canonicalOldType) =
                some (foundCanonical, foundCanonicalType) := by
              simpa [VLCtx.find?, VLCtx.next, hcanonicalOld,
                VLocalDecl.depth] using Hcanonical
            exact congrArg Prod.fst (Option.some.inj Hpair).symm
          have hfoundCurrent : foundCurrent = currentOld := by
            have Hpair : some (currentOld, currentOldType) =
                some (foundCurrent, foundCurrentType) := by
              simpa [VLCtx.find?, VLCtx.next, hcurrentOld,
                VLocalDecl.depth] using Hcurrent
            exact congrArg Prod.fst (Option.some.inj Hpair).symm
          subst foundCanonical
          subst foundCurrent
          simpa [Nat.add_assoc] using
            H.localLookup i hiOld hcanonicalOld hcurrentOld

/-- A context-free concrete expression translates to a target with no loose
bound variables. -/
theorem TrExprS.ContextFree.targetClosed
    (Hfree : TrExprS.ContextFree expr)
    (H : TrExprS env lparams ctx expr target) : target.Closed := by
  induction Hfree generalizing ctx target with
  | sort =>
      cases H
      trivial
  | const =>
      cases H
      trivial
  | app _ _ ihFn ihArg =>
      cases H with
      | app _ _ Hfn Harg => exact ⟨ihFn Hfn, ihArg Harg⟩
  | lit _ ih =>
      cases H with
      | lit _ Hconstructor => exact ih Hconstructor
  | mdata _ ih =>
      cases H with
      | mdata Hbody => exact ih Hbody

/-- Closing exactly the selected parameters before translation agrees, after
weakening by the live constructor-field depth, with translating the opened
expression at the replaced occurrence.  Projection outputs are related through the
environment-indexed support certificates carried by their two translations. -/
theorem TrExprS.abstractSelectedExpansion
    (Hnodup : fvars.Nodup)
    (Hbridge : ParameterExpansionCtx leaf fvars fieldDepth
      abstractDepth targetDepth canonicalCtx currentCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hclosed : Closed (expr.abstractList fvars abstractDepth)
      (fvars.length + abstractDepth))
    (Hscope : expr.FVarsIn (· ∈ fvars))
    (Hcanonical : TrExprS canonicalEnv lparams canonicalCtx
      (expr.abstractList fvars abstractDepth) canonicalTarget)
    (Hcurrent : TrExprS currentEnv lparams currentCtx expr currentTarget) :
    VExpr.NestedExprExpansion leaf
      (fvars.length + fieldDepth + targetDepth)
      (canonicalTarget.liftN fieldDepth targetDepth) currentTarget := by
  induction Hcurrent generalizing canonicalCtx canonicalTarget abstractDepth
      targetDepth with
  | @bvar currentValue currentType currentCtx i HcurrentLookup =>
      have hi : i < abstractDepth := by
        have HsourceClosed : Closed (.bvar i) abstractDepth :=
          Expr.closed_of_abstractList (by
            simpa [Nat.add_comm] using Hclosed)
        simpa only [Closed] using HsourceClosed
      rw [Expr.abstractList_bvar_lt fvars hi] at Hcanonical
      cases Hcanonical with
      | bvar HcanonicalLookup =>
          exact Hbridge.localLookup i hi HcanonicalLookup HcurrentLookup
  | @fvar currentValue currentType currentCtx fv HcurrentLookup =>
      rcases List.getElem_of_mem Hscope with ⟨i, hi, hfv⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi] at Hcanonical
      cases Hcanonical with
      | bvar HcanonicalLookup =>
          exact Hbridge.selected i hi HcanonicalLookup HcurrentLookup
  | @sort level currentLevel currentCtx HcurrentLevel =>
      have habstract : (Expr.sort level).abstractList fvars abstractDepth =
          .sort level := Lean.Expr.abstractList_sort'
      rw [habstract] at Hcanonical
      cases Hcanonical with
      | sort HcanonicalLevel =>
          have hlevel := Option.some.inj
            (HcanonicalLevel.symm.trans HcurrentLevel)
          cases hlevel
          simpa [VExpr.liftN] using
            (VExpr.NestedExprExpansion.sort
              (leaf := leaf)
              (depth := fvars.length + fieldDepth + targetDepth)
              (level := _))
  | @const name currentConst currentLevels currentCtx levels HcurrentConst
      HcurrentLevels HcurrentArity =>
      have habstract : (Expr.const name levels).abstractList fvars
          abstractDepth = .const name levels := by
        exact Lean.Expr.abstractList_const
      rw [habstract] at Hcanonical
      cases Hcanonical with
      | const HcanonicalConst HcanonicalLevels HcanonicalArity =>
          have hlevels := Option.some.inj
            (HcanonicalLevels.symm.trans HcurrentLevels)
          cases hlevels
          simpa [VExpr.liftN] using
            (VExpr.NestedExprExpansion.const
              (leaf := leaf)
              (depth := fvars.length + fieldDepth + targetDepth)
              (name := name) (levels := _))
  | @app currentDomain currentBody currentFn currentArg currentCtx fn arg
      HcurrentFnType HcurrentArgType HcurrentFn HcurrentArg ihFn ihArg =>
      rw [Expr.abstractList_app] at Hcanonical
      cases Hcanonical with
      | app _ _ HcanonicalFn HcanonicalArg =>
          simp only [Expr.abstractList_app, Closed] at Hclosed
          simp only [Lean4Lean.FVarsIn] at Hscope
          have Hfn := ihFn Hbridge Hclosed.1 Hscope.1
            HcanonicalFn
          have Harg := ihArg Hbridge Hclosed.2 Hscope.2
            HcanonicalArg
          simpa [VExpr.liftN] using
            VExpr.NestedExprExpansion.app Hfn Harg
  | lam _ HcurrentDomain HcurrentBody ihDomain ihBody =>
      rw [Expr.abstractList_lam] at Hcanonical
      cases Hcanonical with
      | lam _ HcanonicalDomain HcanonicalBody =>
          simp only [Expr.abstractList_lam, Closed] at Hclosed
          simp only [Lean4Lean.FVarsIn] at Hscope
          have Hdomain := ihDomain Hbridge Hclosed.1 Hscope.1
            HcanonicalDomain
          have Hbody := ihBody (Hbridge.vlam Hlift) Hclosed.2 Hscope.2
            HcanonicalBody
          simpa [VExpr.liftN, Nat.add_assoc] using
            VExpr.NestedExprExpansion.lam Hdomain Hbody
  | forallE _ _ HcurrentDomain HcurrentBody ihDomain ihBody =>
      rw [Expr.abstractList_forallE] at Hcanonical
      cases Hcanonical with
      | forallE _ _ HcanonicalDomain HcanonicalBody =>
          simp only [Expr.abstractList_forallE, Closed] at Hclosed
          simp only [Lean4Lean.FVarsIn] at Hscope
          have Hdomain := ihDomain Hbridge Hclosed.1 Hscope.1
            HcanonicalDomain
          have Hbody := ihBody (Hbridge.vlam Hlift) Hclosed.2 Hscope.2
            HcanonicalBody
          simpa [VExpr.liftN, Nat.add_assoc] using
            VExpr.NestedExprExpansion.forallE Hdomain Hbody
  | letE _ HcurrentType HcurrentValue HcurrentBody ihType ihValue ihBody =>
      rw [Expr.abstractList_letE] at Hcanonical
      cases Hcanonical with
      | letE _ HcanonicalType HcanonicalValue HcanonicalBody =>
          simp only [Expr.abstractList_letE, Closed] at Hclosed
          simp only [Lean4Lean.FVarsIn] at Hscope
          have Htype := ihType Hbridge Hclosed.1 Hscope.1 HcanonicalType
          have Hvalue := ihValue Hbridge Hclosed.2.1 Hscope.2.1
            HcanonicalValue
          have Hbody := ihBody (Hbridge.vlet Hvalue) Hclosed.2.2
            Hscope.2.2 HcanonicalBody
          exact Hbody
  | @lit literal currentCtx currentTarget Hcontains HcurrentConstructor ih =>
      have habstract : (Expr.lit literal).abstractList fvars abstractDepth =
          .lit literal :=
        Lean.Expr.abstractList_lit'
      rw [habstract] at Hcanonical
      have heq :=
        (TrExprS.ContextFree.literal literal).translation_unique
          Hcanonical (TrExprS.lit Hcontains HcurrentConstructor)
      have hclosed :=
        (TrExprS.ContextFree.literal literal).targetClosed Hcanonical
      have hlift : canonicalTarget.liftN fieldDepth targetDepth =
          canonicalTarget := hclosed.liftN_eq (Nat.zero_le _)
      rw [hlift, heq]
      exact VExpr.NestedExprExpansion.refl leaf
        (fvars.length + fieldDepth + targetDepth) _
  | @mdata currentCtx body currentBody data HcurrentBody ih =>
      rw [Expr.abstractList_mdata] at Hcanonical
      cases Hcanonical with
      | mdata HcanonicalBody =>
          have HclosedBody : Closed (body.abstractList fvars abstractDepth)
              (fvars.length + abstractDepth) := by
            simpa only [Expr.abstractList_mdata, Closed] using Hclosed
          have HscopeBody : body.FVarsIn (· ∈ fvars) := by
            simpa only [Lean4Lean.FVarsIn] using Hscope
          simpa using ih Hbridge HclosedBody HscopeBody HcanonicalBody
  | @proj currentCtx body currentBody structName index
      HcurrentBody HcurrentProj ih =>
      rw [Expr.abstractList_proj] at Hcanonical
      cases Hcanonical with
      | proj HcanonicalBody HcanonicalProj =>
          have HclosedBody : Closed (body.abstractList fvars abstractDepth)
              (fvars.length + abstractDepth) := by
            simpa only [Expr.abstractList_proj, Closed] using Hclosed
          have HscopeBody : body.FVarsIn (· ∈ fvars) := by
            simpa only [Lean4Lean.FVarsIn] using Hscope
          have Hmajor := ih Hbridge HclosedBody HscopeBody HcanonicalBody
          exact .proj Hmajor

/-- Pre-lowering source of one auxiliary family of the queue.  It is
constructed by `AuxiliaryFamilyContainer.auxiliaryFamilySource` below, not supplied by a
caller.  It contains no final expansion judgment: it records the exact
pre-lowering family `source` with its independent translation and the two
metadata fields not represented by `TrInductiveType`, together with the same
constructor list both as a raw source translation and as the exact
installed-container specialization. -/
structure AuxiliaryFamilySource
    (H : LoweredAuxiliaryFamily prodEnv params nparams finalState
      targetConcrete)
    (baseVEnv sourceTypesVEnv : VEnv) (lparams : List Name)
    (target : VInductiveType) where
  source : VInductiveType
  translation : TrInductiveTypeHeaders baseVEnv sourceTypesVEnv lparams H.source
    source
  numIndices : target.numIndices = source.numIndices
  resultLevel : target.resultLevel = source.resultLevel
  container : VInductDecl
  containerFamily : VInductiveType
  sourceParams : List VExpr
  baseArgs : List VExpr
  levels : List VLevel
  installed : VEnv.InstalledBelow sourceTypesVEnv container
  /-- The same container is already installed below the pre-header
  observer, as required by `ContainersInstalled`. -/
  installedBase : VEnv.InstalledBelow baseVEnv container
  /-- The concrete looked-up family's safety flag is the container's. -/
  containerUnsafe : H.generated.sourceInfo.isUnsafe = container.isUnsafe
  familyMember : containerFamily ∈ container.types
  containerName : containerFamily.name = H.generated.sourceName
  sourceParamsLength : sourceParams.length = nparams
  sourceParamsWF : OnCtx sourceParams.reverse
    (sourceTypesVEnv.IsType lparams.length)
  baseArgsLength : baseArgs.length = container.nparams
  baseTranslations : List.Forall₂
    (TrExprS sourceTypesVEnv lparams
      (abstractForallContext sourceParams []))
    ((H.generated.args.toList.take H.generated.nestedNParams).map
      (fun arg => arg.abstractList H.generated.selection.fvars))
    baseArgs
  baseArgsClosed : ∀ arg ∈ baseArgs, arg.ClosedN sourceParams.length
  levelsTranslation : H.generated.levels.mapM (VLevel.ofLevel lparams) =
    some levels
  levelsLength : levels.length = container.uvars
  levelsWF : ∀ level ∈ levels, level.WF lparams.length
  sourceUvars : source.uvars = lparams.length
  sourceName : source.name = H.generated.auxName
  targetType : sourceTypesVEnv.IsDefEqU lparams.length [] target.type
    source.type
  familyType : sourceTypesVEnv.IsDefEqU lparams.length [] source.type
    (VExpr.wrapForalls sourceParams
      (VExpr.instantiateForallPrefix (containerFamily.type.instL levels)
        baseArgs))
  familyApplicationTyping : sourceTypesVEnv.HasType lparams.length
    (abstractForallContext sourceParams []).toCtx
    (VExpr.mkApps (.const containerFamily.name levels) baseArgs)
    (VExpr.instantiateForallPrefix (containerFamily.type.instL levels)
      baseArgs)
  constructors : List.Forall₂
    (VInductDecl.SpecializedAuxConstructor sourceTypesVEnv lparams.length sourceParams
      baseArgs levels containerFamily source)
    containerFamily.ctors source.ctors
  /-- Each generated constructor type is syntactically the parameter closure
  of the container constructor type instantiated at the specialization
  arguments, up to the level equivalence (`VExpr.LEquiv`) between the
  translation of a level-instantiated expression and the level instantiation
  of its translation. -/
  constructorShapes : List.Forall₂
    (fun ctor target => ∃ instCtorType : VExpr,
      VExpr.LEquiv lparams.length instCtorType (ctor.type.instL levels) ∧
      target.type = VExpr.wrapForalls sourceParams
        (VExpr.instantiateForallPrefix instCtorType baseArgs))
    containerFamily.ctors source.ctors

/-- Once the pre-lowering source data is available, the final
queue mapping yields the complete abstract expansion of the auxiliary family. -/
theorem LoweredAuxiliaryFamily.abstractExpansion
    (H : LoweredAuxiliaryFamily prodEnv params nparams finalState
      targetConcrete)
    (Hsource : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (Htarget : TrInductiveType baseVEnv targetTypesVEnv lparams targetConcrete
      target)
    (Hmap : NestedAuxMapModels result finalState)
    (henv : baseVEnv.WF)
    (huvars : decl.uvars = lparams.length)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (HtargetTypesWF : targetTypesVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (generated : List VInductiveType)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionLookupCtx
        (VInductDecl.NestedOccurrenceReplacementAbs baseVEnv decl generated)
        depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue →
      TrExprS targetTypesVEnv lparams targetCtx output targetValue →
      VInductDecl.NestedOccurrenceReplacementAbs baseVEnv decl generated depth
        sourceValue targetValue)
    :
    VInductDecl.NestedTypeExpansion baseVEnv decl
      (VInductDecl.NestedOccurrenceReplacementAbs baseVEnv decl generated)
      Hsource.source target := by
  have Hmapping := H.resolvedMapping Hmap
  have Hheader : NestedTypeExpansionHeader baseVEnv decl Hsource.source target :=
    Hmapping.abstractHeaderExpansion Hsource.translation Htarget henv huvars
      Hsource.numIndices Hsource.resultLevel
  exact Hmapping.abstractExpansion Hsource.translation Htarget Hheader
    (Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.constructorsClosed
      Hsource.translation)
    HsourceTypesWF HtargetTypesWF hparamsSize hnparams Hhit

/-- The base arguments retained by an auxiliary family source and
the live base arguments at a reused replacement are structurally identical after the
selected parameters are closed and the live constructor fields are opened.
The proof uses a leaf-free expansion; projection nodes are justified only by
their environment-indexed support certificates. -/
theorem AuxiliaryFamilySource.baseExpansionsAtReplacement
    {Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result traceFinalState}
    {Hselection : CDeclArray lctx As}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    (T : LoweredOccurrenceSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (S : SourceOccurrenceSpine
      (sourceVEnv := sourceTypesVEnv) (sourceCtx := sourceCtx)
      (sourceValue := sourceValue) (lparams := lparams) (input := input)
      T.targetName T.levels T.value Hsource)
    (O : CachedAuxiliaryFamily prodEnv result.params nparams
      initialSize runFinalState T.nested T.auxName)
    (N : AuxiliaryFamilySource O.origin baseVEnv
      sourceTypesVEnv lparams target)
    (resultSelection : CDeclArray result.lctx result.params)
    (hresultNodup : resultSelection.fvars.Nodup)
    (hselectionNodup : Hselection.fvars.Nodup)
    (hAs : As.size = result.params.size)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth sourceCtx)
    (hparamLength : N.sourceParams.length = Hselection.fvars.length)
    (Hscope : input.FVarsIn (· ∈ Hselection.fvars)) :
    List.Forall₂
      (VExpr.NestedExprExpansion (fun _ _ _ => False)
        (Hselection.fvars.length + fieldDepth))
      (N.baseArgs.map (fun arg => arg.liftN fieldDepth 0))
      S.baseArgsAtDepth := by
  rcases T.cachedSourceSpines O resultSelection hresultNodup hselectionNodup hAs
      Hscope with
    ⟨_headName, _headLevels, Halpha⟩
  let currentArgs := input.getAppArgsList.take T.value.numParams
  let currentAbstract := currentArgs.map
    (fun arg => arg.abstractList Hselection.fvars)
  let generatedAbstract :=
    (O.origin.generated.args.toList.take
      O.origin.generated.nestedNParams).map
        (fun arg => arg.abstractList O.origin.generated.selection.fvars)
  have Halpha' : List.Forall₂ (· == ·) currentAbstract
      generatedAbstract := by
    simpa only [currentArgs, currentAbstract, generatedAbstract] using Halpha
  have hsourceLength : currentAbstract.length = N.baseArgs.length := by
    calc
      currentAbstract.length = generatedAbstract.length :=
        Lean4Lean.List.Forall₂.length_eq Halpha'
      _ = N.baseArgs.length :=
        Lean4Lean.List.Forall₂.length_eq N.baseTranslations
  have htargetLength : S.baseArgsAtDepth.length = N.baseArgs.length := by
    calc
      S.baseArgsAtDepth.length = currentArgs.length :=
        (Lean4Lean.List.Forall₂.length_eq S.baseArgsTranslation).symm
      _ = currentAbstract.length := by simp [currentAbstract]
      _ = N.baseArgs.length := hsourceLength
  apply List.forall₂_of_getElem (by simp [htargetLength])
  intro i hsource htarget
  have hiBase : i < N.baseArgs.length := by simpa using hsource
  have hiCurrent : i < currentArgs.length := by
    rw [show currentArgs.length = N.baseArgs.length by
      simpa [currentAbstract] using hsourceLength]
    exact hiBase
  have hiCurrentAbstract : i < currentAbstract.length := by
    simpa [currentAbstract] using hiCurrent
  have hiGenerated : i < generatedAbstract.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq Halpha']
    exact hiCurrentAbstract
  have HalphaAt := Lean4Lean.List.forall₂_getElem
    Halpha' i hiCurrentAbstract hiGenerated
  have HnativeAt := Lean4Lean.List.forall₂_getElem
    N.baseTranslations i hiGenerated hiBase
  have HcanonicalCurrent := HnativeAt.eqv (BEq.symm HalphaAt)
  have hcurrentAbstractGet : currentAbstract[i] =
      currentArgs[i].abstractList Hselection.fvars := by
    simp [currentAbstract]
  rw [hcurrentAbstractGet] at HcanonicalCurrent
  have HcurrentAt := Lean4Lean.List.forall₂_getElem
    S.baseArgsTranslation i hiCurrent (by simpa [htargetLength] using htarget)
  have HclosedAt : Closed
      (currentArgs[i].abstractList Hselection.fvars)
      (Hselection.fvars.length + 0) := by
    have Hclosed := HcanonicalCurrent.closed
    simpa only [abstractForallContext_bvars, VLCtx.bvars, Nat.add_zero,
      hparamLength] using Hclosed
  have HscopeAt : currentArgs[i].FVarsIn (· ∈ Hselection.fvars) := by
    apply Hscope.getAppArgsList
    exact List.mem_of_mem_take (List.getElem_mem hiCurrent)
  have Hbridge : ParameterExpansionCtx (fun _ _ _ => False)
      Hselection.fvars fieldDepth 0 0
      (abstractForallContext N.sourceParams []) sourceCtx :=
    ParameterExpansionCtx.base hparamLength Hparams
  have Hexpansion := TrExprS.abstractSelectedExpansion hselectionNodup
    Hbridge (fun _ _ hfalse => False.elim hfalse)
    HclosedAt HscopeAt HcanonicalCurrent HcurrentAt
  simpa [currentArgs, currentAbstract] using Hexpansion

/-- Sources of all auxiliary families of the queue.
Each slot retains the `LoweredAuxiliaryFamily` used to construct its source;
consumers never have to compare an arbitrary second translation with the
chosen source by syntactic equality. -/
structure AuxiliaryFamilySources
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLowering prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (baseVEnv sourceTypesVEnv : VEnv) (lparams : List Name)
    (loweredDecl : VInductDecl) where
  generated : List VInductiveType
  length : generated.length + sourceTypes.length = result.types.length
  sourceAt : ∀ (i : Nat) (hi : i < generated.length)
      (hresult : sourceTypes.length + i < result.types.length)
      (htarget : sourceTypes.length + i < loweredDecl.types.length),
    ∃ Horigin : LoweredAuxiliaryFamily prodEnv result.params
        nparams finalState result.types[sourceTypes.length + i],
      ∃ N : AuxiliaryFamilySource Horigin baseVEnv
        sourceTypesVEnv lparams
          loweredDecl.types[sourceTypes.length + i],
        N.source = generated[i]
  /-- The common parameter context of the header phase. -/
  parameterContext : List VExpr
  /-- Every slot has a source whose parameter telescope is
  definitionally the common header parameter context. -/
  parametersAt : ∀ (i : Nat) (hi : i < generated.length)
      (hresult : sourceTypes.length + i < result.types.length)
      (htarget : sourceTypes.length + i < loweredDecl.types.length),
    ∃ Horigin : LoweredAuxiliaryFamily prodEnv result.params
        nparams finalState result.types[sourceTypes.length + i],
      ∃ N : AuxiliaryFamilySource Horigin baseVEnv
        sourceTypesVEnv lparams
          loweredDecl.types[sourceTypes.length + i],
        N.source = generated[i] ∧
        VEnv.IsDefEqCtx baseVEnv lparams.length [] N.sourceParams.reverse
          parameterContext

theorem LoweredAuxiliaryFamily.auxName_eq_targetName
    (H : LoweredAuxiliaryFamily env params nparams finalState
      target) :
    H.generated.auxName = target.name := by
  calc
    H.generated.auxName = H.generated.data.type.name :=
      H.generated.built.name.symm
    _ = H.source.name := congrArg InductiveType.name H.generated.family_eq.symm
    _ = target.name := H.lowered.name.symm

/-- Use the source of an auxiliary family at one replaced occurrence.
The specialization arguments may have a different certified
projection normal form from the occurrence's source translation, so their exact
structural expansion is retained separately from the trailing lowering
expansion. -/
theorem AuxiliaryFamilySource.nestedOccurrenceReplacement
    (N : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (sourceDecl : VInductDecl) (generated : List VInductiveType)
    (hsourceTypes : baseVEnv.addConstVals sourceDecl.typeConstants =
      some sourceTypesVEnv)
    (huvars : sourceDecl.uvars = lparams.length)
    (hnparams : sourceDecl.nparams = N.sourceParams.length)
    (hfamily : N.source ∈ generated)
    (inputBaseArgs sourceTrailing targetTrailing : List VExpr)
    (auxiliaryLevels : List VLevel)
    (hauxiliaryLevels : auxiliaryLevels.length = sourceDecl.uvars)
    (Hbase : VInductDecl.NestedExprWFExpansion baseVEnv sourceDecl generated
      (sourceDecl.nparams + depth)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker
        (N.baseArgs.map (fun arg => arg.liftN depth 0)))
      (VExpr.mkApps VInductDecl.nestedTrailingMarker inputBaseArgs))
    (Htrailing : VInductDecl.NestedExprWFExpansion baseVEnv sourceDecl
      generated (sourceDecl.nparams + depth)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceTrailing)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker targetTrailing))
    (hinput : input = VExpr.mkApps (.const N.containerFamily.name N.levels)
      (inputBaseArgs ++ sourceTrailing))
    (houtput : output = VExpr.mkApps
      (.const N.source.name auxiliaryLevels)
      (sourceDecl.paramVars depth ++ targetTrailing)) :
    VInductDecl.NestedOccurrenceReplacement baseVEnv sourceDecl generated depth
      input output := by
  refine .intro hsourceTypes N.installed N.familyMember hfamily
    hnparams.symm N.baseArgsLength
    (by simpa only [hnparams] using N.baseArgsClosed) N.levelsLength
    (by simpa only [huvars] using N.levelsWF) ?_ ?_ ?_
    hauxiliaryLevels Hbase Htrailing hinput houtput
  · exact N.sourceUvars.trans huvars.symm
  · simpa only [huvars] using N.familyType
  · simpa only [huvars] using N.constructors

/-- Construct the source of an auxiliary family once the exact installed container,
checker header, and cached application spine have been recovered.  The
constructor list is synthesized positionally by the executable auxiliary
builder theorem; no family or constructor translation is supplied. -/
theorem AuxiliaryFamilyContainer.auxiliaryFamilySource
    {ves : VEnvs}
    (Horigin : LoweredAuxiliaryFamily prodEnv params nparams
      finalState targetConcrete)
    (C : AuxiliaryFamilyContainer prodEnv (ves.venv safety)
      params finalState.nestedAux Horigin.source Horigin.generated)
    (wf : ves.WF prodEnv)
    (henv : (ves.venv safety).WF)
    (sourceTypesVEnv : VEnv)
    (hbaseLE : ves.venv safety ≤ sourceTypesVEnv)
    (henvTypes : sourceTypesVEnv.WF)
    (lparams : List Name) (sourceParams baseArgs : List VExpr)
    (levels : List VLevel)
    (Hlevels : Horigin.generated.levels.mapM (VLevel.ofLevel lparams) =
      some levels)
    (Hbase : List.Forall₂
      (TrExprS sourceTypesVEnv lparams
        (abstractForallContext sourceParams []))
      ((Horigin.generated.args.toList.take
        Horigin.generated.nestedNParams).map
          (fun arg => arg.abstractList Horigin.generated.selection.fvars))
      baseArgs)
    (hdomains : sourceParams.length =
      Horigin.generated.selection.fvars.length)
    (hparams : OnCtx sourceParams.reverse
      (sourceTypesVEnv.IsType lparams.length))
    (familyTarget : VExpr)
    (HfamilyHeader : TrExprS (ves.venv safety) lparams [] Horigin.source.type
      (VExpr.wrapForalls sourceParams familyTarget))
    (Hfamily : TrExprS sourceTypesVEnv lparams [] Horigin.source.type
      (VExpr.wrapForalls sourceParams familyTarget))
    (target : VInductiveType)
    (HcheckedHeader : TrSourceConst (ves.venv safety) lparams
      Horigin.source.name Horigin.source.type target.toVConstVal)
    (HfamilyApps : VExpr.WF sourceTypesVEnv lparams.length
      (abstractForallContext sourceParams []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name levels)
        baseArgs))
    (hsourceParamsLength : sourceParams.length = nparams)
    (hbaseClosed : ∀ arg ∈ baseArgs, arg.ClosedN sourceParams.length)
    (hlevelsLength : levels.length = C.container.uvars) :
    ∃ N : AuxiliaryFamilySource Horigin
      (ves.venv safety) sourceTypesVEnv lparams target,
      N.sourceParams = sourceParams := by
  let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
  let largerVes : VEnvs := ⟨fun _ => sourceTypesVEnv⟩
  let Ctypes := C.mono hbaseLE
  have HfamilyData :=
    AuxiliaryFamilyContainer.directAuxiliaryFamilyType
      (ves := largerVes) (safety := safety) Ctypes henvTypes lparams sourceParams
    baseArgs levels Hlevels Hbase hdomains hparams familyTarget Hfamily
      HfamilyApps (by
        simpa only [Ctypes, AuxiliaryFamilyContainer.mono]
          using hlevelsLength)
  have HfamilyDefEq := HfamilyData.1
  let auxiliaryFamily := VInductiveType.directAuxiliary sourceParams
    baseArgs levels (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt)
      Horigin.generated.auxName lparams.length target.numIndices
        target.resultLevel
  have Hpoint : ∀ i (hi : i < Horigin.generated.sourceInfo.ctors.length),
      ∃ targetCtor : VConstVal,
        TrSourceConstRaw sourceTypesVEnv lparams
          (Horigin.source.ctors[i]'(by
            have htarget : i < Horigin.generated.data.type.ctors.length := by
              simpa [← Horigin.generated.built.constructors_length] using hi
            simpa [Horigin.generated.family_eq] using htarget)).name
          (Horigin.source.ctors[i]'(by
            have htarget : i < Horigin.generated.data.type.ctors.length := by
              simpa [← Horigin.generated.built.constructors_length] using hi
            simpa [Horigin.generated.family_eq] using htarget)).type
          targetCtor ∧
        VInductDecl.SpecializedAuxConstructor sourceTypesVEnv lparams.length
          sourceParams baseArgs levels
          (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt)
          auxiliaryFamily
          ((Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt).ctors[i]'(by
            simpa [Ctypes, AuxiliaryFamilyContainer.mono,
              ← C.constructors] using hi)) targetCtor ∧
        ∃ instCtorType : VExpr,
          VExpr.LEquiv lparams.length instCtorType
            (((Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt).ctors[i]'(by
              simpa [Ctypes, AuxiliaryFamilyContainer.mono,
                ← C.constructors] using hi)).type.instL levels) ∧
          targetCtor.type = VExpr.wrapForalls sourceParams
            (VExpr.instantiateForallPrefix instCtorType baseArgs) := by
    intro i hi
    rcases C.auxiliaryConstructorTranslation wf i hi with ⟨Bbase⟩
    let B : Ctypes.AuxiliaryConstructorTranslation (ves := largerVes) i hi := by
      simpa [Ctypes, largerVes] using
        (Bbase.mono (largerVes := largerVes) (by
          simpa [largerVes] using hbaseLE))
    simpa only [auxiliaryFamily] using
      AuxiliaryFamilyContainer.AuxiliaryConstructorTranslation.directAuxiliary
        (ves := largerVes) (safety := safety) Ctypes B henvTypes lparams
          sourceParams baseArgs
          levels Hlevels Hbase hdomains hparams familyTarget Hfamily
            HfamilyApps (by
              simpa only [Ctypes, AuxiliaryFamilyContainer.mono]
                using hlevelsLength)
              target.numIndices target.resultLevel
  let targetCtor (i : Fin Horigin.generated.sourceInfo.ctors.length) :
      VConstVal := Classical.choose (Hpoint i i.isLt)
  have HtargetCtor (i : Fin Horigin.generated.sourceInfo.ctors.length) :=
    Classical.choose_spec (Hpoint i i.isLt)
  let targets : List VConstVal := List.ofFn targetCtor
  have HconstructorTranslations : List.Forall₂
      (fun ctor target => TrSourceConstRaw sourceTypesVEnv lparams ctor.name
        ctor.type target) Horigin.source.ctors targets := by
    have hlength : Horigin.source.ctors.length =
        Horigin.generated.sourceInfo.ctors.length := by
      calc
        Horigin.source.ctors.length =
            Horigin.generated.data.type.ctors.length := by
          simpa using congrArg (fun type => type.ctors.length)
            Horigin.generated.family_eq
        _ = Horigin.generated.sourceInfo.ctors.length :=
          Horigin.generated.built.constructors_length.symm
    apply List.forall₂_of_getElem
    · simp [targets, hlength]
    · intro i hsource htargets
      have hi : i < Horigin.generated.sourceInfo.ctors.length := by
        simpa [← hlength] using hsource
      simpa [targets, targetCtor] using (HtargetCtor ⟨i, hi⟩).1
  have HdirectConstructors : List.Forall₂
      (VInductDecl.SpecializedAuxConstructor sourceTypesVEnv lparams.length
        sourceParams baseArgs levels
          (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt)
        auxiliaryFamily)
      (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt).ctors
      targets := by
    have hlength :
        (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt).ctors.length =
          Horigin.generated.sourceInfo.ctors.length := by
      simpa [Ctypes, AuxiliaryFamilyContainer.mono] using
        C.constructors.symm
    apply List.forall₂_of_getElem
    · simp [targets, hlength]
    · intro i hcontainer htargets
      have hi : i < Horigin.generated.sourceInfo.ctors.length := by
        simpa [← hlength] using hcontainer
      simpa [targets, targetCtor] using (HtargetCtor ⟨i, hi⟩).2.1
  have HconstructorShapes : List.Forall₂
      (fun ctor target => ∃ instCtorType : VExpr,
        VExpr.LEquiv lparams.length instCtorType (ctor.type.instL levels) ∧
        target.type = VExpr.wrapForalls sourceParams
          (VExpr.instantiateForallPrefix instCtorType baseArgs))
      (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt).ctors
      targets := by
    have hlength :
        (Ctypes.container.types[Ctypes.familyIdx]'Ctypes.familyIdx_lt).ctors.length =
          Horigin.generated.sourceInfo.ctors.length := by
      simpa [Ctypes, AuxiliaryFamilyContainer.mono] using
        C.constructors.symm
    apply List.forall₂_of_getElem
    · simp [targets, hlength]
    · intro i hcontainer htargets
      have hi : i < Horigin.generated.sourceInfo.ctors.length := by
        simpa [← hlength] using hcontainer
      simpa [targets, targetCtor] using (HtargetCtor ⟨i, hi⟩).2.2
  have hsourceName : Horigin.source.name = Horigin.generated.auxName :=
    (congrArg InductiveType.name Horigin.generated.family_eq).trans
      Horigin.generated.built.name
  have HheaderEq : (ves.venv safety).IsDefEqU lparams.length []
      target.type (VExpr.wrapForalls sourceParams familyTarget) :=
    HcheckedHeader.type.uniq henv (.refl henv (by trivial)) HfamilyHeader
  have HtargetType : (ves.venv safety).IsType lparams.length [] target.type := by
    have Hwf := HcheckedHeader.wf
    change (ves.venv safety).IsType target.uvars [] target.type at Hwf
    rw [HcheckedHeader.uvars] at Hwf
    exact Hwf
  have HsourceType : (ves.venv safety).IsType lparams.length []
      (VExpr.wrapForalls sourceParams familyTarget) :=
    VEnv.IsType.defeqU_l henv (by trivial) HheaderEq HtargetType
  let source : VInductiveType := {
    uvars := lparams.length
    name := Horigin.generated.auxName
    type := VExpr.wrapForalls sourceParams familyTarget
    numIndices := target.numIndices
    resultLevel := target.resultLevel
    ctors := targets }
  have HsourceHeader : TrSourceConst (ves.venv safety) lparams
      Horigin.source.name Horigin.source.type source.toVConstVal := {
    uvars := rfl
    name := by simpa [source] using hsourceName.symm
    type := by simpa [source] using HfamilyHeader
    wf := by
      change (ves.venv safety).IsType lparams.length []
        (VExpr.wrapForalls sourceParams familyTarget)
      exact HsourceType }
  have HconstructorTranslations' : List.Forall₂
      (fun ctor target => TrSourceConstRaw sourceTypesVEnv lparams ctor.name
        ctor.type target) Horigin.source.ctors targets :=
    HconstructorTranslations
  have HdirectConstructors' : List.Forall₂
      (VInductDecl.SpecializedAuxConstructor sourceTypesVEnv lparams.length
        sourceParams baseArgs levels containerFamily source)
      containerFamily.ctors targets := by
    have go : ∀ {sources targets : List VConstVal}, List.Forall₂
        (VInductDecl.SpecializedAuxConstructor sourceTypesVEnv lparams.length
          sourceParams baseArgs levels containerFamily
            (VInductiveType.directAuxiliary sourceParams baseArgs levels
              containerFamily Horigin.generated.auxName lparams.length
                target.numIndices target.resultLevel))
        sources targets →
        List.Forall₂
          (VInductDecl.SpecializedAuxConstructor sourceTypesVEnv lparams.length
            sourceParams baseArgs levels containerFamily source)
          sources targets := by
      intro sources targets Hdirect
      induction Hdirect with
      | nil => exact .nil
      | cons Hhead _ ih =>
        exact .cons {
          name := by simpa [source, containerFamily,
            VInductiveType.directAuxiliary] using Hhead.name
          uvars := by simpa [source, containerFamily,
            VInductiveType.directAuxiliary] using Hhead.uvars
          type := Hhead.type } ih
    exact go (by
      simpa only [auxiliaryFamily, containerFamily, Ctypes,
        AuxiliaryFamilyContainer.mono]
        using HdirectConstructors)
  exact ⟨{
    source := source
    translation := {
      header := HsourceHeader
      ctors := by simpa [source] using HconstructorTranslations' }
    numIndices := by simp [source]
    resultLevel := by simp [source]
    container := C.container
    containerFamily := containerFamily
    sourceParams := sourceParams
    baseArgs := baseArgs
    levels := levels
    installed := by
      simpa only [Ctypes, AuxiliaryFamilyContainer.mono]
        using Ctypes.installed
    installedBase := C.installed
    containerUnsafe := C.containerUnsafe
    familyMember := List.getElem_mem C.familyIdx_lt
    containerName := (C.lookupName.trans C.familyName).symm
    sourceParamsLength := hsourceParamsLength
    sourceParamsWF := hparams
    baseArgsLength := by
      have hlength := Lean4Lean.List.Forall₂.length_eq Hbase
      have hsourceLength :
          ((Horigin.generated.args.toList.take
            Horigin.generated.nestedNParams).map
              (fun arg => arg.abstractList
                Horigin.generated.selection.fvars)).length =
              Horigin.generated.nestedNParams := by
        simp [Nat.min_eq_left Horigin.generated.argsArity]
      exact hlength.symm.trans
        (hsourceLength.trans C.nestedNParams)
    baseTranslations := Hbase
    baseArgsClosed := hbaseClosed
    levelsTranslation := Hlevels
    levelsLength := hlevelsLength
    levelsWF := VLevel.WF.of_mapM_ofLevel Hlevels
    sourceUvars := by simp [source]
    sourceName := by simp [source]
    targetType := by
      have Htarget := HcheckedHeader.type.mono hbaseLE
      have Hsource := HsourceHeader.type.mono hbaseLE
      simpa [source, VLCtx.toCtx] using
        Htarget.uniq henvTypes (.refl henvTypes (by trivial)) Hsource
    familyType := by
      simpa only [source, containerFamily, Ctypes,
        AuxiliaryFamilyContainer.mono]
        using HfamilyDefEq
    familyApplicationTyping := by
      simpa only [containerFamily, Ctypes,
        AuxiliaryFamilyContainer.mono] using HfamilyData.2
    constructors := by
      simpa [source, containerFamily] using HdirectConstructors'
    constructorShapes := by
      simpa only [source, containerFamily, Ctypes,
        AuxiliaryFamilyContainer.mono] using HconstructorShapes }, rfl⟩

/-- Every family header installed by the ordinary run was
absent from its source kernel environment.  This is the
freshness companion to `RecursorCheck.findSourceHeader`: it retains the exact header entry
selected by the declaration's family list and reads freshness off the
lockstep installation. -/
theorem HeaderData.sourceHeaderFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv : Environment}
    (Hheaders : HeaderData c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hc : ContextWF c)
    (howner : owner ∈ indTypes.toList) :
    c.env.find? owner.name = none := by
  have := Hc
  obtain ⟨t, ht, Htr, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hheaders.trSources owner howner
  obtain ⟨info, hinfo, Hinfo, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r Hheaders.trHeaders t ht
  have hname : info.name = owner.name := Hinfo.2.trans Htr.name
  rw [← hname]
  exact Hheaders.fresh info hinfo

/-- Recover a generated family's previously installed container in the
pre-header observer.  The restored application initially exposes its lookup
after the current source headers have been installed.  The successful run
proves that every one of those header names was fresh in the source kernel
environment, whereas the container lookup was already present there; hence
the finite header fold cannot have introduced or shadowed that lookup. -/
theorem LoweredAuxiliaryFamily.installedContainerBeforeHeaders
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {headerEnv : Environment}
    {Hheaders : HeaderData c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {ves : VEnvs}
    (wf : ves.WF c.env)
    (hsourceVEnv : sourceVEnv = ves.venv safety)
    (Hrun : NestedLowering c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hc : ContextWF c)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (Horigin : LoweredAuxiliaryFamily c.env result.params nparams
      finalState target)
    (realization : AuxiliaryHeadTyping sourceTypesVEnv c.lparams
      parameterDomains
      ((mkAppRange (.const Horigin.generated.sourceName
        Horigin.generated.levels) 0 Horigin.generated.nestedNParams
        Horigin.generated.args).abstractList
          Horigin.generated.selection.fvars)) :
    Nonempty (AuxiliaryFamilyContainer c.env sourceVEnv
      result.params finalState.nestedAux Horigin.source Horigin.generated) := by
  rcases Horigin.generated.abstractContainerLookup realization with
    ⟨abstractFamily, habstractAfter⟩
  have hnames : ∀ ci ∈
      (loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal,
      ci.name ≠ Horigin.generated.sourceName := by
    intro ci hci
    rcases List.mem_map.mp hci with ⟨targetType, htargetType, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r HsourceHeaders targetType
        htargetType with ⟨sourceType, hsourceType, Hheader⟩
    rcases Hrun.preservesInitialTypeName
        ⟨sourceType, by simpa using hsourceType, rfl⟩ with
      ⟨loweredType, hloweredType, hloweredName⟩
    have hfresh := Hheaders.sourceHeaderFresh Hc (by simpa using hloweredType)
    intro htargetName
    have hsourceName : sourceType.name = Horigin.generated.sourceName :=
      Hheader.name.symm.trans (by simpa using htargetName)
    have hloweredName' : loweredType.name =
        Horigin.generated.sourceName := hloweredName.trans hsourceName
    rw [hloweredName'] at hfresh
    rw [Horigin.generated.built.lookup] at hfresh
    contradiction
  have habstractBefore : sourceVEnv.constants
      Horigin.generated.sourceName = some abstractFamily := by
    rw [VEnv.addConstVals_constants_of_forall_ne HsourceAdded hnames] at habstractAfter
    exact habstractAfter
  rw [hsourceVEnv] at habstractBefore ⊢
  exact Horigin.generated.installedContainerOfAbstractLookup wf safety
    abstractFamily habstractBefore

/-- The ordinary header checker already translated the auxiliary family
header that occurs at this exact final queue position.  Lowering preserves
that header literally, while the builder records its pre-lowering parameter
telescope.  Consequently the checker's parameter suffix supplies
the parameter context for the pre-lowering auxiliary family itself. -/
theorem LoweredAuxiliaryFamily.formationHeaderParameterDomains
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv targetTypesVEnv : VEnv}
    {headerEnv : Environment}
    {Hheaders : HeaderData c stats loweredDecl nparams isUnsafe
      depth sourceVEnv indTypes headerEnv}
    (H : LoweredAuxiliaryFamily c.env params nparams finalState
      targetConcrete)
    (Htarget : TrInductiveType sourceVEnv targetTypesVEnv c.lparams
      targetConcrete targetAbstract)
    (htarget : targetAbstract ∈ loweredDecl.types)
    (hparams : params.size = nparams)
    (HenvB : EnvironmentTypesBVarClosed c.env) :
    let parameterDomains :=
      (Hheaders.sourceStatsWF.parameterSuffix.toRecursorContext
        (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse
    ∃ domains targetResidual,
      domains.length = nparams ∧
      TrExprS sourceVEnv c.lparams [] H.source.type
        (VExpr.wrapForalls domains targetResidual) ∧
      VEnv.IsDefEqCtx sourceVEnv c.lparams.length []
        domains.reverse parameterDomains.reverse := by
  dsimp only [AddInductive.getRecLevelParams]
  rcases H.generated.built.generatedFamilyTelescope H.generated.selection with
    ⟨sourceTail, _HsourceTelescope, HgeneratedTelescope⟩
  have Htelescope : Expr.ForallTelescope H.source.type nparams
      ((sourceTail.instantiateRevRange 0 H.generated.nestedNParams
        H.generated.args).abstractList H.generated.selection.fvars) := by
    simpa only [H.generated.family_eq, hparams,
      Expr.abstractN_eq_abstractList_of_closed H.generated.selectionNodup
        (H.generated.residualClosed HenvB sourceTail _HsourceTelescope)] using
      HgeneratedTelescope
  have Htelescope' : Expr.ForallTelescope H.source.type loweredDecl.nparams
      ((sourceTail.instantiateRevRange 0 H.generated.nestedNParams
        H.generated.args).abstractList H.generated.selection.fvars) := by
    rw [Hheaders.nparams]
    exact Htelescope
  let HsourceHeader : TrSourceConst sourceVEnv c.lparams H.source.name
      H.source.type targetAbstract.toVConstVal := {
    uvars := Htarget.header.uvars
    name := Htarget.header.name.trans H.lowered.name
    type := by
      rw [← H.lowered.type]
      exact Htarget.header.type
    wf := Htarget.header.wf }
  have HsourceHeader' : TrSourceConst Hheaders.sourceContext.venv c.lparams
      H.source.name H.source.type targetAbstract.toVConstVal := by
    rw [Hheaders.sourceContextVEnv]
    exact HsourceHeader
  rcases Hheaders.sourceStatsWF.sourceParameterDomainsAt H.source
      targetAbstract HsourceHeader' htarget (elimLevel := .zero) (by trivial)
      Htelescope' with
    ⟨domains, targetResidual, hdomains, Htranslation, Hcontext⟩
  rw [Hheaders.sourceContextVEnv] at Htranslation Hcontext
  exact ⟨domains, targetResidual,
    hdomains.trans Hheaders.nparams,
    by simpa only [AddInductive.getRecLevelParams] using Htranslation, by
      simpa only [AddInductive.getRecLevelParams, List.reverse_reverse]
        using Hcontext⟩

/-- Formation uses the declaration's own universe parameters.  At that
universe observer, the first source header and the nested-auxiliary
validation derive exactly the same common-parameter context.  The statement is
proved directly, so formation does not depend on a recursor check. -/
theorem NestedLoweringOutputClosed.auxiliaryFormationParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {ctorEnv : Environment}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv
      result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (selection : CDeclArray result.lctx result.params)
    (Haux : ClosedNestedOccurrenceTyping sourceTypesVEnv c.lparams
      result selection e) :
    let Hsuffix := R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
      (elimLevel := .zero) (by trivial)
    let parameterDomains := Hsuffix.parameterDecls.toCtx.reverse
    VEnv.IsDefEqCtx sourceTypesVEnv c.lparams.length []
      parameterDomains.reverse Haux.domains.reverse := by
  dsimp only [AddInductive.getRecLevelParams]
  have HsourceClosed : ∀ source ∈ sourceTypes,
      source.type.FVarsIn fun _ => False := by
    intro source hsource
    exact Hsources.typeClosed hsource
  have HsourceBClosed : ∀ source ∈ sourceTypes, Closed source.type := by
    intro source hsource
    rcases Lean4Lean.List.Forall₂.forall_exists_l HsourceHeaders source hsource with
      ⟨target, _htarget, Htr⟩
    have h := Htr.type.closed
    simpa [VLCtx.bvars] using h
  rcases H.sourceParameterPrefix HsourceClosed HsourceBClosed Haux.type with
    ⟨first, rest, residual, hsourceTypes, Htelescope, Hsame⟩
  subst sourceTypes
  have hfamily : 0 < (first :: rest).length := by simp
  have hprefix :
      0 < (loweredDecl.types.take (first :: rest).length).length := by
    have hlength := Lean4Lean.List.Forall₂.length_eq HsourceHeaders
    exact hlength ▸ hfamily
  have hdecl : 0 < loweredDecl.types.length := by
    rw [List.length_take] at hprefix
    omega
  have Hheader := Lean4Lean.List.forall₂_getElem
    HsourceHeaders 0 hfamily hprefix
  have hprefixEq :
      (loweredDecl.types.take (first :: rest).length)[0] =
        loweredDecl.types[0] := by
    simp only [List.getElem_take]
  rw [hprefixEq] at Hheader
  have Hheader' : TrSourceConst R.headers.sourceContext.venv c.lparams
      first.name first.type (loweredDecl.types[0]'hdecl).toVConstVal := by
    rw [R.headers.sourceContextVEnv]
    simpa using Hheader
  have Htelescope' : Expr.ForallTelescope first.type loweredDecl.nparams
      residual := by
    rw [R.core.nparams]
    exact Htelescope
  rcases R.headers.sourceStatsWF.sourceParameterDomainsAt first
      loweredDecl.types[0] Hheader' (List.getElem_mem hdecl)
      (elimLevel := .zero) (by trivial) Htelescope' with
    ⟨sourceDomains, sourceResidual, hsourceDomains,
      HsourceTranslation, HsourceContext⟩
  simp only [AddInductive.getRecLevelParams] at HsourceTranslation HsourceContext
  rw [R.headers.sourceContextVEnv] at HsourceTranslation HsourceContext
  have hsourceLE : sourceVEnv ≤ sourceTypesVEnv := by
    exact VEnv.addConstVals_le HsourceAdded
  have henv : sourceTypesVEnv.WF := HsourceTypesWF
  have HsourceTranslation' : TrExprS sourceTypesVEnv c.lparams [] first.type
      (VExpr.wrapForalls sourceDomains sourceResidual) :=
    HsourceTranslation.mono hsourceLE
  have HauxClosed : TrExprS sourceTypesVEnv c.lparams []
      (result.lctx.mkForall result.params Haux.type)
      (VExpr.wrapForalls Haux.domains Haux.residualType) :=
    Haux.closed
  have HauxSource : VEnv.IsDefEqCtx sourceTypesVEnv c.lparams.length []
      Haux.domains.reverse sourceDomains.reverse := by
    have hauxDomains : Haux.domains.length = nparams :=
      Haux.arity.trans (H.resultParamsSize.trans H.toResult.resultNParams)
    have Hcontexts := Hsame.translatedContextsExact henv
      (.refl henv (by trivial)) HauxClosed HsourceTranslation'
      hauxDomains (by simpa [R.core.nparams] using hsourceDomains)
    simpa [VLCtx.toCtx] using Hcontexts
  have HsourceContext' := HsourceContext.mono hsourceLE
  have HparameterSource := HsourceContext'.symm henv.ordered
  have HsourceAux := HauxSource.symm henv.ordered
  have HparameterAux := VEnv.IsDefEqCtx.trans_empty henv
    HparameterSource HsourceAux
  simpa only [List.reverse_reverse] using HparameterAux

/-- An auxiliary family of the queue obtains its abstract container spine
from the nested-auxiliary validation result and the exact lowering run.  The
parameter-context conversion is the one derived by
`NestedLoweringOutputClosed.auxiliaryFormationParameterContext`; it is not selected by a
caller. -/
theorem LoweredAuxiliaryFamily.abstractContainerApplication
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {ctorEnv : Environment}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv
      result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLowering c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (hempty : initialState.nestedAux = #[])
    (selection : CDeclArray result.lctx result.params)
    (Htranslations : ClosedNestedOccurrenceTypings sourceTypesVEnv
      c.lparams result selection)
    (Horigin : LoweredAuxiliaryFamily c.env result.params nparams
      finalState target) :
    let parameterDomains :=
      (R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
        (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse
    let sourceApplication :=
      (mkAppRange (.const Horigin.generated.sourceName
        Horigin.generated.levels) 0 Horigin.generated.nestedNParams
        Horigin.generated.args).abstractList Horigin.generated.selection.fvars
    ∃ realization : AuxiliaryHeadTyping sourceTypesVEnv
        c.lparams parameterDomains sourceApplication,
      ∃ abstractLevels, ∃ baseArgs,
      Horigin.generated.levels.mapM
          (VLevel.ofLevel c.lparams) =
        some abstractLevels ∧
      baseArgs.length = Horigin.generated.nestedNParams ∧
      List.Forall₂
        (TrExprS sourceTypesVEnv c.lparams
          (abstractForallContext parameterDomains []))
        ((Horigin.generated.args.toList.take
          Horigin.generated.nestedNParams).map
            (fun arg =>
              arg.abstractList Horigin.generated.selection.fvars))
        baseArgs ∧
      (∀ arg ∈ baseArgs, arg.ClosedN parameterDomains.length) ∧
      realization.family = VExpr.mkApps
        (.const Horigin.generated.sourceName abstractLevels) baseArgs := by
  dsimp only
  let Hclosed : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  have Hmap : NestedAuxMapModels result finalState :=
    Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have hselectionNodup : selection.fvars.Nodup :=
    Hclosed.selectionNodup selection
  have hsourceLE : sourceVEnv ≤ sourceTypesVEnv :=
    VEnv.addConstVals_le HsourceAdded
  have henvTypesWF : sourceTypesVEnv.WF := HsourceTypesWF
  have Hcontexts : ∀ Haux : ClosedNestedOccurrenceTyping sourceTypesVEnv
      c.lparams result selection Horigin.generated.data.nested,
      VEnv.IsDefEqCtx sourceTypesVEnv c.lparams.length []
        ((R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
          (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse).reverse
        Haux.domains.reverse := by
    intro Haux
    exact Hclosed.auxiliaryFormationParameterContext (R := R) Hsources
      HsourceHeaders HsourceAdded HsourceTypesWF selection Haux
  rcases Horigin.generated.cachedAuxiliaryHeadTyping Hmap
      hselectionNodup Htranslations henvTypesWF
      ((R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
        (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse)
      Hcontexts with
    ⟨realization⟩
  rcases Horigin.generated.abstractContainerApplication realization
      henvTypesWF (by
        have Hwf :=
          (R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
            (elimLevel := .zero) (by trivial)).parameterWF
        have hbaseLE :
            (R.headers.sourceContext.toAdmissibleRecursorContextWF
              (elimLevel := .zero) (by trivial)).venv ≤ sourceTypesVEnv := by
          change R.headers.sourceContext.venv ≤ sourceTypesVEnv
          rw [R.headers.sourceContextVEnv]
          exact hsourceLE
        have Hwf' := (Hwf.mono hbaseLE).toCtx
        simpa only [AddInductive.getRecLevelParams, List.reverse_reverse]
          using Hwf') with
    ⟨abstractLevels, baseArgs, Hlevels, hbaseLength, Hbase, HbaseClosed,
      hfamily⟩
  exact ⟨realization, abstractLevels, baseArgs, Hlevels, hbaseLength, Hbase,
    HbaseClosed, hfamily⟩

/-- The complete pre-lowering source of the auxiliary family at a queue
position is reconstructed from the lowering run and the ordinary header
check.  Parameter-context conversion, application transport, the installed
container, header translation, and every constructor target are
all derived here. -/
theorem LoweredAuxiliaryFamily.auxiliaryFamilySource
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv targetTypesVEnv : VEnv}
    {ctorEnv : Environment}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv
      result.types.toArray ctorEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {ves : VEnvs}
    (wf : ves.WF c.env)
    (hsourceVEnv : sourceVEnv = ves.venv safety)
    (Hrun : NestedLowering c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (Hc : ContextWF c)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (hempty : initialState.nestedAux = #[])
    (selection : CDeclArray result.lctx result.params)
    (Htranslations : ClosedNestedOccurrenceTypings sourceTypesVEnv
      c.lparams result selection)
    (H : LoweredAuxiliaryFamily c.env result.params nparams
      finalState targetConcrete)
    (Htarget : TrInductiveType sourceVEnv targetTypesVEnv c.lparams
      targetConcrete targetAbstract)
    (htarget : targetAbstract ∈ loweredDecl.types)
    (hparamsSize : result.params.size = nparams) :
    ∃ N : AuxiliaryFamilySource H sourceVEnv
      sourceTypesVEnv c.lparams targetAbstract,
      VEnv.IsDefEqCtx sourceVEnv c.lparams.length [] N.sourceParams.reverse
        (R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
          (elimLevel := .zero) (by trivial)).parameterDecls.toCtx := by
  subst sourceVEnv
  let parameterDomains :=
    (R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
      (elimLevel := .zero) (by trivial)).parameterDecls.toCtx.reverse
  rcases H.abstractContainerApplication (R := R) Hrun Hcache Hparams Hsources
      HsourceHeaders HsourceAdded HsourceTypesWF hempty selection Htranslations
      with
    ⟨realization, abstractLevels, baseArgs, Hlevels, _hbaseLength, Hbase,
      _HbaseClosed, hfamily⟩
  rcases H.installedContainerBeforeHeaders (Hheaders := R.headers) wf rfl Hrun Hc
      HsourceHeaders HsourceAdded realization with ⟨C⟩
  rcases H.formationHeaderParameterDomains Htarget htarget hparamsSize
      (VEnvs.WF.environmentTypesBVarClosed wf) with
    ⟨sourceDomains, familyTarget, hsourceDomains, Hfamily, Hcontext⟩
  have henv : (ves.venv safety).WF := wf.tr.wf
  have hbaseLE : ves.venv safety ≤ sourceTypesVEnv :=
    VEnv.addConstVals_le HsourceAdded
  have HcontextTypes := Hcontext.mono hbaseLE
  have HcontextV : VLCtx.IsDefEq sourceTypesVEnv c.lparams.length
      (abstractForallContext parameterDomains [])
      (abstractForallContext sourceDomains []) :=
    abstractForallContext.isDefEq
      (HcontextTypes.symm HsourceTypesWF.ordered)
  rcases Lean4Lean.VerifyInductive.TrExprS.forall₂DefEqDFCWithTargets
      HsourceTypesWF HcontextV Hbase with
    ⟨sourceBaseArgs, HsourceBase, HbaseEq⟩
  have hsourceParamWF : OnCtx sourceDomains.reverse
      (sourceTypesVEnv.IsType c.lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
      (abstractForallContext.isDefEq HcontextTypes).wf.toCtx
  have HfamilyAppsCanonical : VExpr.WF sourceTypesVEnv c.lparams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
          abstractLevels) baseArgs) := by
    refine ⟨realization.familyType, ?_⟩
    rw [← C.lookupName.trans C.familyName, ← hfamily]
    simpa only [VEnv.HasType, abstractForallContext_toCtx, VLCtx.toCtx,
      List.append_nil] using realization.familyTyping
  have HfamilyAppsOldAtSource : VExpr.WF sourceTypesVEnv c.lparams.length
      (abstractForallContext sourceDomains []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
          abstractLevels) baseArgs) := by
    rcases HfamilyAppsCanonical with ⟨familyAppType, HfamilyApp⟩
    exact ⟨familyAppType,
      HfamilyApp.defeqDFC HsourceTypesWF.ordered HcontextV.defeqCtx⟩
  have HbaseEq' : List.Forall₂
      (sourceTypesVEnv.IsDefEqU c.lparams.length
        (abstractForallContext sourceDomains []).toCtx)
      baseArgs sourceBaseArgs := by
    have go : ∀ {left right}, List.Forall₂
        (sourceTypesVEnv.IsDefEqU c.lparams.length
          (abstractForallContext sourceDomains []).toCtx) right left →
        List.Forall₂
          (sourceTypesVEnv.IsDefEqU c.lparams.length
            (abstractForallContext sourceDomains []).toCtx) left right := by
      intro left right Heq
      induction Heq with
      | nil => exact .nil
      | cons Hhead _ ih => exact .cons Hhead.symm ih
    exact go HbaseEq
  have hctx : OnCtx (abstractForallContext sourceDomains []).toCtx
      (sourceTypesVEnv.IsType c.lparams.length) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hsourceParamWF
  have HheadWF := VExpr.WF.mkApps_fn HsourceTypesWF.orderedStrong hctx
    HfamilyAppsOldAtSource
  have HheadEq := VEnv.IsDefEqU.refl HheadWF
  have HappEq := VEnv.IsDefEqU.mkApps HsourceTypesWF hctx HheadEq
    HfamilyAppsOldAtSource HbaseEq'
  have HfamilyApps : VExpr.WF sourceTypesVEnv c.lparams.length
      (abstractForallContext sourceDomains []).toCtx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name
          abstractLevels) sourceBaseArgs) := by
    rcases HappEq with ⟨appType, HappEq⟩
    exact ⟨appType, HappEq.hasType.2⟩
  have hdomains : sourceDomains.length = H.generated.selection.fvars.length := by
    calc
      sourceDomains.length = nparams := hsourceDomains
      _ = result.params.size := hparamsSize.symm
      _ = H.generated.As.size := H.generated.built.arity.symm
      _ = H.generated.selection.fvars.length := H.generated.selection.size
  have hbaseClosed : ∀ arg ∈ sourceBaseArgs,
      arg.ClosedN sourceDomains.length := by
    intro arg harg
    rcases Lean4Lean.List.Forall₂.forall_exists_r HsourceBase arg harg with
      ⟨sourceArg, _hsourceArg, Harg⟩
    have hctx : OnCtx (abstractForallContext sourceDomains []).toCtx
        (sourceTypesVEnv.IsType c.lparams.length) := by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hsourceParamWF
    have HargWF := Harg.wf HsourceTypesWF.orderedStrong
      (by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
        (abstractForallContext.isDefEq HcontextTypes).wf)
    have hctxClosed : CtxClosed
        (abstractForallContext sourceDomains []).toCtx :=
      VEnv.CtxWF.closed HsourceTypesWF.ordered hctx
    have Hclosed := HargWF.closedN HsourceTypesWF.ordered hctxClosed
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hclosed
  have hlevelsLength : abstractLevels.length = C.container.uvars := by
    calc
      abstractLevels.length = H.generated.levels.length :=
        (checkPositivityStep.List.mapM_some_length Hlevels).symm
      _ = (C.container.types[C.familyIdx]'C.familyIdx_lt).uvars := by
        simpa using H.generated.levelsLengthOfAbstractLookup realization
          (hbaseLE.constants C.familyLookup)
      _ = C.container.uvars := C.familyUvars
  let HcheckedHeader : TrSourceConst (ves.venv safety) c.lparams H.source.name
      H.source.type targetAbstract.toVConstVal := {
    uvars := Htarget.header.uvars
    name := Htarget.header.name.trans H.lowered.name
    type := by
      rw [← H.lowered.type]
      exact Htarget.header.type
    wf := Htarget.header.wf }
  have Hnative := C.auxiliaryFamilySource H wf wf.tr.wf
    sourceTypesVEnv hbaseLE HsourceTypesWF
      c.lparams sourceDomains
      sourceBaseArgs abstractLevels Hlevels HsourceBase hdomains
      hsourceParamWF familyTarget
      Hfamily
      (Hfamily.mono hbaseLE) targetAbstract
      HcheckedHeader
      HfamilyApps hsourceDomains hbaseClosed
      hlevelsLength
  rcases Hnative with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  rw [hN]
  simpa only [parameterDomains, List.reverse_reverse] using Hcontext

/-- Construct the sources of all auxiliary families by finite choice over
the auxiliary slots of the final queue.  Every choice is immediately certified by the
`LoweredAuxiliaryFamily` at that position and the builder proof, so no translation
or formation fact is supplied by a caller. -/
theorem NestedLowering.auxiliaryFamilySources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv targetTypesVEnv targetCtorsVEnv : VEnv}
    {ctorEnv : Environment}
    {R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv
      result.types.toArray ctorEnv}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {ves : VEnvs}
    (Hrun : NestedLowering c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (wf : ves.WF c.env)
    (hsourceVEnv : sourceVEnv = ves.venv safety)
    (Hc : ContextWF c)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (hempty : initialState.nestedAux = #[])
    (selection : CDeclArray result.lctx result.params)
    (Htranslations : ClosedNestedOccurrenceTypings sourceTypesVEnv
      c.lparams result selection)
    (Htarget : TrInductDeclCore sourceVEnv c.lparams nparams result.types
      isUnsafe loweredDecl targetTypesVEnv targetCtorsVEnv) :
    ∃ N : AuxiliaryFamilySources Hrun sourceVEnv
      sourceTypesVEnv c.lparams loweredDecl,
      N.parameterContext =
        (R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
          (elimLevel := .zero) (by trivial)).parameterDecls.toCtx := by
  subst sourceVEnv
  let parameterContext :=
    (R.headers.sourceStatsWF.parameterSuffix.toRecursorContext
      (elimLevel := .zero) (by trivial)).parameterDecls.toCtx
  let count := result.types.length - sourceTypes.length
  have hle : sourceTypes.length ≤ result.types.length :=
    (show NestedLoweringRun c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result from
        ⟨finalState, Hrun⟩).sourceTypes_length_le
  have hresultAt (i : Fin count) :
      sourceTypes.length + i.1 < result.types.length := by
    dsimp only [count] at i
    omega
  have htargetAt (i : Fin count) :
      sourceTypes.length + i.1 < loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget]
    exact hresultAt i
  let AuxiliarySourceAt (i : Fin count) :=
    Σ Horigin : LoweredAuxiliaryFamily c.env result.params
      nparams finalState
        (getElem result.types (sourceTypes.length + i.1) (hresultAt i)),
      { N : AuxiliaryFamilySource Horigin (ves.venv safety)
          sourceTypesVEnv c.lparams
            (getElem loweredDecl.types (sourceTypes.length + i.1) (htargetAt i)) //
        VEnv.IsDefEqCtx (ves.venv safety) c.lparams.length []
          N.sourceParams.reverse parameterContext }
  have Hpoint : ∀ i : Fin count, Nonempty (AuxiliarySourceAt i) := by
    intro i
    have hresult := hresultAt i
    have htarget := htargetAt i
    rcases Hrun.resolvedAuxiliaryFamilyAt
        (VerifyInductive.VEnvs.WF.environmentTypesClosed wf)
        wf.inductivesClosed Hsources (by simp) (by simp) hresult with
      ⟨Horigin⟩
    rcases Horigin.auxiliaryFamilySource
        wf rfl Hrun
        Hcache Hparams Hc Hsources HsourceHeaders
        HsourceAdded HsourceTypesWF hempty selection Htranslations
        (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Htarget
          (sourceTypes.length + i.1) hresult htarget)
        (List.getElem_mem htarget) Hrun.resultParamsSize with
      ⟨N, hN⟩
    exact ⟨⟨Horigin, N, hN⟩⟩
  let auxiliarySourceAt (i : Fin count) : AuxiliarySourceAt i := Classical.choice (Hpoint i)
  let generated : List VInductiveType :=
    List.ofFn fun i : Fin count => (auxiliarySourceAt i).2.1.source
  refine ⟨{
    generated := generated
    length := ?_
    sourceAt := ?_
    parameterContext := parameterContext
    parametersAt := ?_ }, rfl⟩
  · simp only [generated, List.length_ofFn, count]
    omega
  · intro i hi hresult htarget
    have hicount : i < count := by
      simpa only [generated, List.length_ofFn] using hi
    let fi : Fin count := ⟨i, hicount⟩
    let O := (auxiliarySourceAt fi).1
    let N := (auxiliarySourceAt fi).2.1
    refine ⟨O, ?_, ?_⟩
    · simpa only [fi, O, N] using N
    · simp only [generated, List.getElem_ofFn, N]
      congr 1
  · intro i hi hresult htarget
    have hicount : i < count := by
      simpa only [generated, List.length_ofFn] using hi
    let fi : Fin count := ⟨i, hicount⟩
    let O := (auxiliarySourceAt fi).1
    let N := (auxiliarySourceAt fi).2
    refine ⟨O, N.1, ?_, N.2⟩
    simp only [generated, List.getElem_ofFn, N]
    congr 1

/-- Reindex the registry source at the exact cache slot selected by a reused
replacement.  Cache-name uniqueness identifies the retained
auxiliary family with the queried nested expression, yielding a `CachedAuxiliaryFamily`
for that same source rather than constructing a second source. -/
theorem AuxiliaryFamilySources.sourceForReplacement
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hrun : NestedLowering prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState)}
    (N : AuxiliaryFamilySources Hrun baseVEnv sourceTypesVEnv
      lparams loweredDecl)
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    {Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result traceFinalState}
    {Hselection : CDeclArray lctx As}
    {HtargetExpr : TrExprS targetEnvTypes lparams targetCtx output targetValue}
    (T : LoweredOccurrenceSpine Htrace Hselection HtargetExpr sourceDecl
      fieldDepth)
    (O : CachedAuxiliaryFamily prodEnv result.params nparams
      sourceTypes.toArray.size finalState T.nested T.auxName)
    (hempty : initialState.nestedAux = #[]) :
    ∃ (i : Nat) (hi : i < N.generated.length)
      (hresult : sourceTypes.length + i < result.types.length)
      (htarget : sourceTypes.length + i < loweredDecl.types.length),
      ∃ Ocanonical : CachedAuxiliaryFamily prodEnv result.params
          nparams sourceTypes.toArray.size finalState T.nested T.auxName,
        result.types[sourceTypes.length + i]'hresult =
          finalState.newTypes[Ocanonical.j]'Ocanonical.hj ∧
        ∃ Nsource : AuxiliaryFamilySource
            Ocanonical.origin baseVEnv sourceTypesVEnv lparams
              loweredDecl.types[sourceTypes.length + i],
          Nsource.source = N.generated[i] := by
  have hresultArray : result.types.toArray = finalState.newTypes := by
    rcases Hrun.source with
      ⟨_first, _rest, _tail, _paramsState, _lctx, _params, _htypes,
        _Hopening, _hnewTypes, _hinitialAux, _hnextIdx, _hprefix, _Hctx,
        _Hselection, Hqueue⟩
    simpa using congrArg List.toArray Hqueue.resultTypes
  have hresultSize : result.types.length = finalState.newTypes.size := by
    have hsize := congrArg Array.size hresultArray
    simpa using hsize
  have hjResult : O.j < result.types.length := by
    rw [hresultSize]
    exact O.hj
  have hsourceLE : sourceTypes.length ≤ O.j := by
    simpa using O.generatedSuffix
  let i := O.j - sourceTypes.length
  have hindex : sourceTypes.length + i = O.j := by
    dsimp only [i]
    omega
  have hi : i < N.generated.length := by
    have hlength := N.length
    omega
  have htarget : sourceTypes.length + i < loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget,
      hindex]
    exact hjResult
  have hresult : sourceTypes.length + i < result.types.length := by
    simpa only [hindex] using hjResult
  rcases N.sourceAt i hi hresult htarget with
    ⟨Hcanonical, Ncanonical, hsource⟩
  let finalTarget : InductiveType :=
    getElem finalState.newTypes O.j O.hj
  have hfamily :
      getElem result.types (sourceTypes.length + i) hresult =
        finalTarget := by
    have hget := congrArg
      (fun xs : Array InductiveType => xs[O.j]!) hresultArray
    have hleft : result.types.toArray[O.j]! =
        getElem result.types O.j hjResult := by
      simp [hjResult]
    have hright : finalState.newTypes[O.j]! =
        finalTarget := by
      simp [finalTarget, O.hj]
    have hresultGet : getElem result.types O.j hjResult = finalTarget :=
      hleft.symm.trans (hget.trans hright)
    simpa only [hindex] using hresultGet
  let canonicalFinal :
      Σ Horigin : LoweredAuxiliaryFamily prodEnv result.params
          nparams finalState finalTarget,
        { Nsource : AuxiliaryFamilySource Horigin baseVEnv
            sourceTypesVEnv lparams
              loweredDecl.types[sourceTypes.length + i] //
          Nsource.source = N.generated[i] } := by
    rw [← hfamily]
    exact ⟨Hcanonical, Ncanonical, hsource⟩
  let HcanonicalFinal := canonicalFinal.1
  let NcanonicalFinal := canonicalFinal.2.1
  have hcanonicalAux : HcanonicalFinal.generated.auxName = T.auxName := by
    calc
      HcanonicalFinal.generated.auxName =
          finalTarget.name :=
        HcanonicalFinal.auxName_eq_targetName
      _ = O.origin.generated.auxName :=
        O.origin.auxName_eq_targetName.symm
      _ = T.auxName := O.auxName_eq
  have hcanonicalLookup := Hrun.resultAuxLookup
    (Hrun.resultNamesNodupOfEmpty hempty) HcanonicalFinal.generated.cached
  rw [hcanonicalAux] at hcanonicalLookup
  have hcanonicalNested : HcanonicalFinal.generated.data.nested = T.nested := by
    exact Option.some.inj (hcanonicalLookup.symm.trans T.resultLookup)
  let Ocanonical : CachedAuxiliaryFamily prodEnv result.params
      nparams sourceTypes.toArray.size finalState T.nested T.auxName := {
    j := O.j
    hj := O.hj
    generatedSuffix := O.generatedSuffix
    origin := HcanonicalFinal
    nested_eq := hcanonicalNested
    auxName_eq := hcanonicalAux }
  exact ⟨i, hi, hresult, htarget, Ocanonical, hfamily, NcanonicalFinal,
    canonicalFinal.2.2⟩

/-- Every replacement leaf needed by formation is reconstructed from the
replaced occurrence and the sources of the auxiliary families (`AuxiliaryFamilySources`).
No caller-supplied callback or arbitrary second source translation is
used. -/
theorem AuxiliaryFamilySources.replacementCompat
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hrun : NestedLowering prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState)}
    (N : AuxiliaryFamilySources Hrun baseVEnv sourceTypesVEnv
      lparams loweredDecl)
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetTypesVEnv targetCtorsVEnv)
    (Henv : EnvironmentTypesClosed prodEnv)
    (hclosures : MutualInductivesClosed prodEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (hsourceTypes : baseVEnv.addConstVals sourceDecl.typeConstants =
      some sourceTypesVEnv)
    (resultSelection : CDeclArray result.lctx result.params)
    (hresultNodup : resultSelection.fvars.Nodup)
    (hempty : initialState.nestedAux = #[])
    (huvars : sourceDecl.uvars = lparams.length)
    (hnparams : sourceDecl.nparams = nparams) :
    NestedFormationReplacementCompat prodEnv result baseVEnv sourceTypesVEnv
      targetTypesVEnv lparams sourceDecl N.generated := by
  intro lctx As input state output nextState traceFinalState depth fieldDepth
    sourceValue targetValue sourceCtx targetCtx Htrace Hctx selection
    hselectionNodup Harity Hdepth HsourceParams HtargetParams Hscope HsourceExpr
    HtargetExpr
  have hselectionLength : selection.fvars.length = sourceDecl.nparams := by
    calc
      selection.fvars.length = As.size := selection.size.symm
      _ = result.params.size := Harity
      _ = nparams := Hrun.resultParamsSize
      _ = sourceDecl.nparams := hnparams.symm
  have HbaseDepth : sourceDecl.nparams ≤ depth := by
    rw [Hdepth, ← hselectionLength]
    omega
  rcases Htrace.targetSpine selection Harity HtargetParams
      (Hrun.resultParamsSize.trans hnparams.symm) HtargetExpr with ⟨T⟩
  rcases T.sourceSpine HsourceExpr with ⟨S⟩
  have Htrailing := TrExprS.forall₂_abstractExpansionAbsolute Hctx HbaseDepth
    S.trailingTranslation T.trailingTranslation
  rcases T.resolvedAuxiliaryFamily Hrun Henv hclosures Hsources rfl hempty
      with ⟨O⟩
  rcases N.sourceForReplacement Htarget T O hempty with
    ⟨i, hi, hresult, htarget, Ocanonical, hresultFinal, Nsource, hsourceEq⟩
  have hparamLength : Nsource.sourceParams.length = selection.fvars.length := by
    exact Nsource.sourceParamsLength.trans (hnparams ▸ hselectionLength.symm)
  have Hbase := Nsource.baseExpansionsAtReplacement T S Ocanonical
    resultSelection hresultNodup hselectionNodup Harity HsourceParams
      hparamLength Hscope
  have HbaseAbsolute : List.Forall₂
      (VExpr.NestedExprExpansion
        (VInductDecl.NestedOccurrenceReplacementAbs baseVEnv sourceDecl
          N.generated) depth)
      (Nsource.baseArgs.map (fun arg => arg.liftN fieldDepth 0))
      S.baseArgsAtDepth := by
    have Hmapped := Lean4Lean.List.Forall₂.imp
      (fun _ _ Hentry => Hentry.map
        (leaf' := VInductDecl.NestedOccurrenceReplacementAbs baseVEnv sourceDecl
          N.generated) (fun Hfalse => False.elim Hfalse)) Hbase
    simpa [Hdepth] using Hmapped
  have HbaseWF : VInductDecl.NestedExprWFExpansion baseVEnv sourceDecl
      N.generated (sourceDecl.nparams + fieldDepth)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker
        (Nsource.baseArgs.map (fun arg => arg.liftN fieldDepth 0)))
      (VExpr.mkApps VInductDecl.nestedTrailingMarker S.baseArgsAtDepth) := by
    have := forall₂_nestedTrailingExpansion HbaseAbsolute
    simpa [Hdepth, hselectionLength] using this
  have HtrailingWF : VInductDecl.NestedExprWFExpansion baseVEnv sourceDecl
      N.generated (sourceDecl.nparams + fieldDepth)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker S.trailing)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker T.trailing) := by
    have := forall₂_nestedTrailingExpansion Htrailing
    simpa [Hdepth, hselectionLength] using this
  rcases T.cachedSourceSpines Ocanonical resultSelection hresultNodup
      hselectionNodup Harity Hscope with
    ⟨hheadName, hheadLevels, _Halpha⟩
  have hinputName : T.targetName = Nsource.containerFamily.name :=
    hheadName.trans Nsource.containerName.symm
  have hinputLevels : S.sourceLevels = Nsource.levels := by
    have HmapLevels := congrArg
      (fun levels => levels.mapM (VLevel.ofLevel lparams)) hheadLevels
    exact Option.some.inj (S.sourceLevelsTranslation.symm.trans
      (HmapLevels.trans Nsource.levelsTranslation))
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget (sourceTypes.length + i) hresult htarget
  have htargetName :
      (loweredDecl.types[sourceTypes.length + i]'htarget).name = T.auxName := by
    calc
      (loweredDecl.types[sourceTypes.length + i]'htarget).name =
          (result.types[sourceTypes.length + i]'hresult).name := by
        exact HtargetType.header.name
      _ = (finalState.newTypes[Ocanonical.j]'Ocanonical.hj).name :=
        congrArg InductiveType.name hresultFinal
      _ = Ocanonical.origin.generated.auxName :=
        Ocanonical.origin.auxName_eq_targetName.symm
      _ = T.auxName := Ocanonical.auxName_eq
  have htargetMember :
      (loweredDecl.types[sourceTypes.length + i]'htarget).toVConstVal ∈
        loweredDecl.typeConstants := by
    simp only [VInductDecl.typeConstants]
    exact List.mem_map.mpr
      ⟨loweredDecl.types[sourceTypes.length + i]'htarget,
        List.getElem_mem htarget, rfl⟩
  have htargetLookup := VEnv.addConstVals_get Htarget.typesAdded htargetMember
  rw [htargetName] at htargetLookup
  have hauxInfo : T.auxiliaryInfo =
      (loweredDecl.types[sourceTypes.length + i]'htarget).toVConstVal.toVConstant :=
    Option.some.inj (T.auxiliaryLookup.symm.trans htargetLookup)
  have hauxiliaryLevels : T.auxiliaryLevels.length = sourceDecl.uvars := by
    have htranslatedLength :=
      checkPositivityStep.List.mapM_some_length T.auxiliaryLevelsTranslation
    rw [T.auxiliaryConcreteArity, hauxInfo] at htranslatedLength
    exact htranslatedLength.symm.trans
      (HtargetType.header.uvars.trans huvars.symm)
  have hfamily : Nsource.source ∈ N.generated := by
    rw [hsourceEq]
    exact List.getElem_mem hi
  have hinput : sourceValue = VExpr.mkApps
      (.const Nsource.containerFamily.name Nsource.levels)
      (S.baseArgsAtDepth ++ S.trailing) := by
    calc
      sourceValue = VExpr.mkApps (.const T.targetName S.sourceLevels)
          (S.baseArgsAtDepth ++ S.trailing) := S.sourceValue_eq
      _ = _ := congrArg
        (fun head => VExpr.mkApps head (S.baseArgsAtDepth ++ S.trailing))
        ((congrArg (fun name => VExpr.const name S.sourceLevels) hinputName).trans
          (congrArg (VExpr.const Nsource.containerFamily.name) hinputLevels))
  have houtput : targetValue = VExpr.mkApps
      (.const Nsource.source.name T.auxiliaryLevels)
      (sourceDecl.paramVars fieldDepth ++ T.trailing) := by
    calc
      targetValue = VExpr.mkApps (.const T.auxName T.auxiliaryLevels)
          (sourceDecl.paramVars fieldDepth ++ T.trailing) := T.targetValue_eq
      _ = _ := congrArg
        (fun head => VExpr.mkApps head
          (sourceDecl.paramVars fieldDepth ++ T.trailing))
        (congrArg (fun name => VExpr.const name T.auxiliaryLevels)
          (Nsource.sourceName.trans Ocanonical.auxName_eq).symm)
  have Hrelative := Nsource.nestedOccurrenceReplacement sourceDecl N.generated
    hsourceTypes huvars (hnparams.trans Nsource.sourceParamsLength.symm)
      hfamily S.baseArgsAtDepth
      S.trailing T.trailing T.auxiliaryLevels hauxiliaryLevels HbaseWF
      HtrailingWF hinput houtput
  exact ⟨fieldDepth, by omega, Hrelative⟩

/-- Project the sources of the auxiliary families to the ordered expansion of the
auxiliary slots, using the `LoweredAuxiliaryFamily` stored at each slot. -/
theorem NestedLowering.auxiliaryExpansionsOfSources
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLowering prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (henv : baseVEnv.WF)
    (HtargetTypesWF : targetEnvTypes.WF)
    (N : AuxiliaryFamilySources Hrun baseVEnv sourceTypesVEnv
      lparams loweredDecl)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (Henv : EnvironmentTypesClosed prodEnv)
    (hclosures : MutualInductivesClosed prodEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (hsourceTypes : baseVEnv.addConstVals sourceDecl.typeConstants =
      some sourceTypesVEnv)
    (resultSelection : CDeclArray result.lctx result.params)
    (hresultNodup : resultSelection.fvars.Nodup)
    (hempty : initialState.nestedAux = #[])
    (huvars : sourceDecl.uvars = lparams.length)
    (hnparams : sourceDecl.nparams = nparams) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion baseVEnv sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs baseVEnv sourceDecl
          N.generated))
      N.generated (loweredDecl.types.drop sourceTypes.length) := by
  have hloweredLength : loweredDecl.types.length = result.types.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget).symm
  have hdropLength : (loweredDecl.types.drop sourceTypes.length).length =
      N.generated.length := by
    rw [List.length_drop, hloweredLength]
    have hlength := N.length
    omega
  apply List.forall₂_of_getElem (by omega)
  intro i hgenerated htargetDrop
  have hresult : sourceTypes.length + i < result.types.length := by
    have := htargetDrop
    simp only [List.length_drop, hloweredLength] at this
    omega
  have htarget : sourceTypes.length + i < loweredDecl.types.length := by
    simpa [hloweredLength] using hresult
  rcases N.sourceAt i hgenerated hresult htarget with
    ⟨Horigin, Nsource, hsourceEq⟩
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget (sourceTypes.length + i) hresult htarget
  have Hmap := Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have Hhit : NestedFormationReplacementCompat prodEnv result baseVEnv
      sourceTypesVEnv targetEnvTypes lparams sourceDecl N.generated :=
    N.replacementCompat Htarget Henv hclosures Hsources hsourceTypes
      resultSelection hresultNodup hempty huvars hnparams
  have Hexpansion := Horigin.abstractExpansion Nsource HtargetType
    Hmap henv huvars HsourceTypesWF HtargetTypesWF Hrun.resultParamsSize
      hnparams.symm N.generated Hhit
  have hdropGet :
      (loweredDecl.types.drop sourceTypes.length)[i] =
        loweredDecl.types[sourceTypes.length + i] := by
    simp only [List.getElem_drop]
  rw [hsourceEq] at Hexpansion
  rw [hdropGet]
  exact Hexpansion

/-- Ordered formation expansion for the entire lowered queue, assembled only
from the source translation and the sources of the auxiliary families. -/
theorem NestedLowering.allExpansionsOfSources
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLowering prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (Hsource : TrInductDeclCore baseVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Henv : EnvironmentTypesClosed prodEnv)
    (hclosures : MutualInductivesClosed prodEnv)
    (henv : baseVEnv.WF)
    (hempty : initialState.nestedAux = #[])
    (N : AuxiliaryFamilySources Hrun baseVEnv sourceEnvTypes
      lparams loweredDecl)
    (resultSelection : CDeclArray result.lctx result.params) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion baseVEnv sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs baseVEnv sourceDecl
          N.generated))
      (sourceDecl.types ++ N.generated) loweredDecl.types := by
  let Hclosed : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  have hresultNodup := Hclosed.selectionNodup resultSelection
  have Hhit : NestedFormationReplacementCompat prodEnv result baseVEnv
      sourceEnvTypes targetEnvTypes lparams sourceDecl N.generated :=
    N.replacementCompat Htarget Henv hclosures Hsources Hsource.typesAdded
      resultSelection hresultNodup hempty Hsource.uvars Hsource.nparams
  have Horiginal := Hclosed.sourceExpansions Hsource Htarget Hmetadata
    Hsources (by simpa using hempty) henv N.generated Hhit
  have HsourceTypesWF : sourceEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource henv
  have HtargetTypesWF : targetEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget henv
  have Hgenerated := Hrun.auxiliaryExpansionsOfSources Htarget henv
    HtargetTypesWF N HsourceTypesWF Henv hclosures Hsources Hsource.typesAdded
      resultSelection hresultNodup hempty Hsource.uvars Hsource.nparams
  have Hall := _root_.List.Forall₂.append' Horiginal
    Hgenerated
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
  have htargetSplit :
      loweredDecl.types.take sourceDecl.types.length ++
          loweredDecl.types.drop sourceTypes.length = loweredDecl.types := by
    rw [hsourceLength]
    exact List.take_append_drop sourceTypes.length loweredDecl.types
  simpa only [htargetSplit] using Hall

end VerifyInductive
end Lean4Lean
