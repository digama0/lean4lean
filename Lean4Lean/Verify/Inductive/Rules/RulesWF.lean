import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped

/-! # `rules_wf` from the generated equations

The rule clause of `VInductDecl.WF` (`rules_wf`) types each model rule of the installed
recursors as a schematic ι rule (`VEnv.PatTyped`). On the source branch the rules were stored
equations and their typing was the `VDefEq.WF` of the generated equations; here the rule is a
pattern and its typing is restated from that `VDefEq.WF` (PORT_PLAN section 2.3,
`InductiveSignature.Instance.equation_patTyped`). This file identifies each model rule with
its generated equation through the kernel recursor it translates (`TrRecursor`, functional by
`TrExprS.unique`) and the generator's coverage of the kernel rules (`TrRecursorRule`), and
reads the counts off the recursor metadata (`RecursorMetadata`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Transport of a typed ι rule along equalities of its data. -/
theorem VEnv.patTyped_iota_congr {env : VEnv} {r r' c c' : Name}
    {np np' nm nm' nmin nmin' nind nind' cnp cnp' nf nf' : Nat} {rhs rhs' : VExpr}
    {hc : rhs.Closed} {hc' : rhs'.Closed}
    (hr : r = r') (hcn : c = c') (hnp : np = np') (hnm : nm = nm') (hnmin : nmin = nmin')
    (hnind : nind = nind') (hcnp : cnp = cnp') (hnf : nf = nf') (hrhs : rhs = rhs')
    (H : env.PatTyped (SimplePattern.iota r (np+nm+nmin+nind) c (cnp+nf)).toPattern
      (SimplePattern.iotaRHS r c np nm nmin nind cnp nf rhs hc, .true)) :
    env.PatTyped (SimplePattern.iota r' (np'+nm'+nmin'+nind') c' (cnp'+nf')).toPattern
      (SimplePattern.iotaRHS r' c' np' nm' nmin' nind' cnp' nf' rhs' hc', .true) := by
  subst hr hcn hnp hnm hnmin hnind hcnp hnf hrhs; exact H

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT

/-- The rule coverage of a recursor check (the `trRules` clause of `RuleTranslations`): each
kernel recursor's rules are, in order, the generated equations of the constructors it owns. -/
def RecursorCheck.RulesCovered (H : RecursorCheck R outEnv) : Prop :=
  List.Forall₂ (fun (owner : Fin H.signature.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule H.generation H.outVEnv rval.levelParams)
        (H.signature.ownedConstructors owner) rval.rules)
    (List.finRange H.signature.families.size) H.rvals

/-- The generated equations are well formed in the recursor stage (the `equationsWF` clause
of `RuleTranslations`). -/
def RecursorCheck.EquationsWF (H : RecursorCheck R outEnv) : Prop :=
  ∀ df ∈ H.generation.equations, df.WF H.outVEnv

/-- Every model rule fires on a constructor with the signature's parameter count: the
constructor parameter count `TrRecursor` reads off the output map is the declaration's. -/
def RecursorCheck.RuleCtorParams (H : RecursorCheck R outEnv) : Prop :=
  ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ru.ctorParams = H.signature.params.length

/-- The data a model rule shares with its generated equation. -/
structure RuleEquationData (H : RecursorCheck R outEnv) (r : VRecursor) (ru : VRecRule)
    (index : Fin H.signature.constructors.size) : Prop where
  name : r.name = H.generation.recursorName H.signature.constructors[index].owner
  numParams : r.numParams = H.signature.params.length
  numMotives : r.numMotives = H.signature.families.size
  numMinors : r.numMinors = H.signature.constructors.size
  numIndices : r.numIndices = H.signature.constructors[index].indices.length
  ctor : ru.ctor = H.signature.constructors[index].name
  ctorParams : ru.ctorParams = H.signature.params.length
  nfields : ru.nfields = H.signature.constructors[index].fields.length
  rhs : ru.rhs = (H.generation.equation index).rhs

theorem RecursorCheck.families_size_eq (H : RecursorCheck R outEnv) (hcov : H.RulesCovered) :
    H.signature.families.size = H.recs.length := by
  have := List.Forall₂.length_eq hcov
  simp only [List.length_finRange] at this
  rw [this, H.recs_length]

/-- The `j`-th rule of the `i`-th model recursor is, reduct for reduct, the generated equation
of the `j`-th constructor owned by family `i`, with the generated counts. -/
theorem RecursorCheck.rule_equation_getElem (H : RecursorCheck R outEnv)
    (hcov : H.RulesCovered) (hparams : H.RuleCtorParams) (i : Nat) (hi : i < H.recs.length)
    (j : Nat) (hj : j < H.recs[i].rules.length) :
    ∃ (hiF : i < H.signature.families.size)
      (hjO : j < (H.signature.ownedConstructors ⟨i, hiF⟩).length),
      RuleEquationData H H.recs[i] H.recs[i].rules[j]
        (H.signature.ownedConstructors ⟨i, hiF⟩)[j] := by
  have hlenR : H.recs.length = H.rvals.length := H.recs_length
  have hiR : i < H.rvals.length := hlenR ▸ hi
  have hiF : i < H.signature.families.size := H.families_size_eq hcov ▸ hi
  have Htr := List.forall₂_getElem H.trRecs i hiR hi
  have Hmeta := List.forall₂_getElem H.metadata i (by simpa using hiF) hiR
  have Hcov := List.forall₂_getElem hcov i (by simpa using hiF) hiR
  simp only [List.getElem_finRange, Fin.cast_mk] at Hmeta Hcov
  -- the model recursor is the generated recursor of family `i`
  have hrec : H.recs[i].toVConstVal = H.generation.recursor ⟨i, hiF⟩ := by
    have h := congrArg (·[i]?) H.recursors_eq
    simpa [List.getElem?_eq_getElem hi, InductiveSignature.Instance.recursors, hiF] using h
  have hjK : j < H.rvals[i].rules.length := (List.Forall₂.length_eq Htr.rules) ▸ hj
  have Hrule := List.forall₂_getElem Htr.rules j hjK hj
  obtain ⟨hctor, hnf, -, hrhs⟩ := Hrule
  have hjO : j < (H.signature.ownedConstructors ⟨i, hiF⟩).length :=
    (List.Forall₂.length_eq Hcov) ▸ hjK
  have Hgen := List.forall₂_getElem Hcov j hjO hjK
  refine ⟨hiF, hjO, ?_⟩
  generalize hindex : (H.signature.ownedConstructors ⟨i, hiF⟩)[j] = index at Hgen
  have hown : H.signature.constructors[index].owner = ⟨i, hiF⟩ := by
    have hmem : index ∈ H.signature.ownedConstructors ⟨i, hiF⟩ := hindex ▸ List.getElem_mem _
    simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
    exact hmem.2
  have harity :=
    H.models.constructorArity _ (Array.getElem_mem_toList (i := index.val) index.isLt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hparams _ (List.getElem_mem _) _ (List.getElem_mem _), ?_, ?_⟩
  · rw [hown]; have := congrArg VConstVal.name hrec; simpa [InductiveSignature.Instance.recursor]
  · rw [Htr.numParams]; exact Hmeta.numParams
  · rw [Htr.numMotives]; exact Hmeta.numMotives
  · rw [Htr.numMinors]; exact Hmeta.numMinors
  · rw [Htr.numIndices, Hmeta.numIndices]
    have hfam := congrArg (fun o : Fin H.signature.families.size =>
      H.signature.families[o].indices.length) hown
    exact (harity.trans hfam).symm
  · rw [hctor]; exact Hgen.ctor
  · rw [hnf]; exact Hgen.nfields
  · exact (TrExprS.unique Hgen.rhs hrhs).symm

/-- Every model rule of a recursor check is a generated equation. -/
theorem RecursorCheck.rule_equation (H : RecursorCheck R outEnv) (hcov : H.RulesCovered)
    (hparams : H.RuleCtorParams) {r : VRecursor} (hr : r ∈ H.recs) {ru : VRecRule}
    (hru : ru ∈ r.rules) :
    ∃ index : Fin H.signature.constructors.size, RuleEquationData H r ru index := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hru
  obtain ⟨_, _, D⟩ := H.rule_equation_getElem hcov hparams i hi j hj
  exact ⟨_, D⟩

/-- Every generated equation is a model rule of a recursor check: the rule of the owner's
recursor at the constructor's position among the owner's constructors. -/
theorem RecursorCheck.equation_rule (H : RecursorCheck R outEnv) (hcov : H.RulesCovered)
    (hparams : H.RuleCtorParams) (index : Fin H.signature.constructors.size) :
    ∃ r ∈ H.recs, ∃ ru ∈ r.rules, RuleEquationData H r ru index := by
  let o := H.signature.constructors[index].owner
  have hmem : index ∈ H.signature.ownedConstructors o := by
    simp [InductiveSignature.ownedConstructors, o]
  obtain ⟨j, hjO, hjeq⟩ := List.mem_iff_getElem.1 hmem
  have hi : o.val < H.recs.length := H.families_size_eq hcov ▸ o.isLt
  have hlenR : H.recs.length = H.rvals.length := H.recs_length
  have hiR : o.val < H.rvals.length := hlenR ▸ hi
  have Htr := List.forall₂_getElem H.trRecs o.val hiR hi
  have Hcov := List.forall₂_getElem hcov o.val (by simp) hiR
  simp only [List.getElem_finRange, Fin.cast_mk] at Hcov
  have hjK : j < H.rvals[o.val].rules.length := (List.Forall₂.length_eq Hcov) ▸ hjO
  have hj : j < H.recs[o.val].rules.length := (List.Forall₂.length_eq Htr.rules) ▸ hjK
  obtain ⟨_, _, D⟩ := H.rule_equation_getElem hcov hparams o.val hi j hj
  refine ⟨_, List.getElem_mem hi, _, List.getElem_mem hj, ?_⟩
  simpa [hjeq] using D

/-- A λ-telescope over an application has that application as its body. -/
theorem VExpr.lamBody_wrapLams_app (doms : List VExpr) (f a : VExpr) :
    (VExpr.wrapLams doms (.app f a)).lamBody = .app f a := by
  induction doms with
  | nil => rfl
  | cons d ds ih => exact ih

/-- A model rule sharing its data with a generated equation is that equation
(`VRecRule.OfEquation`, the `rules` clauses of `VInductDecl.RecsOf`). -/
theorem RuleEquationData.ofEquation {H : RecursorCheck R outEnv} {r : VRecursor}
    {ru : VRecRule} {index : Fin H.signature.constructors.size}
    (D : RuleEquationData H r ru index) :
    VRecRule.OfEquation r ru (H.generation.equation index) := by
  unfold VRecRule.OfEquation
  simp only [InductiveSignature.Instance.equation, InductiveSignature.Instance.recursorHead,
    InductiveSignature.Instance.constructorApp]
  rw [VExpr.mkApps_snoc, VExpr.lamBody_wrapLams_app]
  refine ⟨D.rhs.symm, ?_, ?_, _, List.getLast?_concat .., ?_, ?_⟩
  · simp [VExpr.headConst?, VExpr.getAppFn, D.name]
  · simp [VRecursor.getMajorIdx, VExpr.getAppArgs, InductiveSignature.vars_length, D.numParams,
      D.numMotives, D.numMinors, D.numIndices]; omega
  · simp [VExpr.headConst?, VExpr.getAppFn, D.ctor]
  · simp [VExpr.getAppArgs, InductiveSignature.vars_length, D.ctorParams, D.nfields]

/-- The rules of the model recursors are the generated equations, both ways (the `rules` and
`rules_total` clauses of `VInductDecl.RecsOf`). -/
theorem RecursorCheck.rules_ofEquation (H : RecursorCheck R outEnv) (hcov : H.RulesCovered)
    (hparams : H.RuleCtorParams) :
    (∀ r ∈ H.recs, ∀ ru ∈ r.rules, ∃ df ∈ H.generation.equations, VRecRule.OfEquation r ru df) ∧
    (∀ df ∈ H.generation.equations, ∃ r ∈ H.recs, ∃ ru ∈ r.rules,
      VRecRule.OfEquation r ru df) := by
  refine ⟨fun r hr ru hru => ?_, fun df hdf => ?_⟩
  · obtain ⟨index, D⟩ := H.rule_equation hcov hparams hr hru
    exact ⟨_, List.mem_map.2 ⟨index, List.mem_finRange _, rfl⟩, D.ofEquation⟩
  · obtain ⟨index, -, rfl⟩ := List.mem_map.1 hdf
    obtain ⟨r, hr, ru, hru, D⟩ := H.equation_rule hcov hparams index
    exact ⟨r, hr, ru, hru, D.ofEquation⟩

/-- `VInductDecl.WF.rules_wf` of a recursor check, from the rule coverage, the
well-formedness of the generated equations and the constructor parameter counts. -/
theorem RecursorCheck.rules_wf_of (H : RecursorCheck R outEnv) (hcov : H.RulesCovered)
    (hwf : H.EquationsWF) (hparams : H.RuleCtorParams) :
    ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
      H.outVEnv.PatTyped
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor
          r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
          .true) := by
  intro r hr ru hru hc
  obtain ⟨index, ⟨hname, hnp, hnm, hnmin, hnind, hctor, hcnp, hnf, hrhs⟩⟩ :=
    H.rule_equation hcov hparams hr hru
  have hc' : (H.generation.equation index).rhs.Closed := hrhs ▸ hc
  have hdf := hwf _ (List.mem_map.2 ⟨index, List.mem_finRange _, rfl⟩)
  exact VEnv.patTyped_iota_congr hname.symm hctor.symm hnp.symm hnm.symm hnmin.symm
    hnind.symm hcnp.symm hnf.symm hrhs.symm
    (H.generation.equation_patTyped H.outVEnv_wf index hdf hc')

end
end VerifyInductive
end Lean4Lean
