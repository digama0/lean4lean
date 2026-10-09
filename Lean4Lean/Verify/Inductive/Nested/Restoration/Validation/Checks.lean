import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ParameterPrefix
import Lean4Lean.Verify.Inductive.Nested.Lowering.Basic
import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope
import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Inductive.Nested.Lowering.Queue

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- If `List.forM` succeeds, the step succeeds on every member of the list.
This selects one constructor from the whole-block validation run. -/
private theorem listForM_eq_ok_of_mem
    (step : α → Except ε Unit) :
    ∀ {items : List α}, items.forM step = .ok () →
      ∀ {item}, item ∈ items → step item = .ok () := by
  intro items hrun item hitem
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
    simp only [List.forM] at hrun
    cases hhead : step head with
    | error err =>
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
    | ok value =>
      rcases value with ⟨⟩
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact hhead
      · exact ih hrun htail

private theorem forallExists_to_forall₂
    (H : ∀ item ∈ items, ∃ target, relation item target) :
    ∃ targets, List.Forall₂ relation items targets := by
  induction items with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
    rcases H head (by simp) with ⟨target, Htarget⟩
    rcases ih (fun item hitem => H item (by simp [hitem])) with
      ⟨targets, Htargets⟩
    exact ⟨target :: targets, .cons Htarget Htargets⟩

private theorem validateSourceConstructorTypes.constructorStep_eq_ok_of_run
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams
      safety fuel types = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    (do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel) do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type) = .ok () := by
  unfold Lean4Lean.validateSourceConstructorTypes.run at hrun
  have hfamily := listForM_eq_ok_of_mem
    (fun type : InductiveType => type.ctors.forM fun ctor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel) do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type)
    hrun htype
  have hconstructor := listForM_eq_ok_of_mem
    (fun ctor : Constructor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel) do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type)
    hfamily hctor
  exact hconstructor

/-- The successful source-type check of one constructor, selected from the
successful whole-block validation run. -/
theorem validateSourceConstructorTypes.typeCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams
      safety fuel types = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    ∃ checked, TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := lparams) (fuel := fuel) (do
        let type ← TypeChecker.checkType ctor.type
        TypeChecker.ensureSort type ctor.type) = .ok checked := by
  have hconstructor :=
    validateSourceConstructorTypes.constructorStep_eq_ok_of_run
      hrun htype hctor
  cases hcheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := lparams) (fuel := fuel)
      (do
        let type ← TypeChecker.checkType ctor.type
        TypeChecker.ensureSort type ctor.type) with
  | error err =>
    rw [hcheck] at hconstructor
    cases hconstructor
  | ok checked =>
    exact ⟨checked, rfl⟩

/-- The executable source-type check gives the abstract source constant
needed by constructor restoration, read off the successful validation run. -/
theorem validateSourceConstructorTypes.sourceConst_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (Hsources : SourceSyntaxChecks types)
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams
      safety fuel types = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    ∃ constructor : VConstVal,
      TrSourceConst venv lparams ctor.name ctor.type constructor := by
  rcases validateSourceConstructorTypes.typeCheck_eq_ok_of_run
      hrun htype hctor with ⟨checked, hcheck⟩
  have hclosed := Hsources.constructorsClosed htype ctor hctor
  have hfvars : ctor.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid lparams fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType ctor.type
      TypeChecker.ensureSort type ctor.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid lparams fuel) {}
      fun _ _ => ∃ type', TrExprS venv lparams [] ctor.type type' ∧
        venv.IsType lparams.length [] type' := by
    refine (TypeChecker.checkType.WF (e := ctor.type) hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype,
        ⟨_, hhasType.defeqU_r hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid Hcheck hmode
  rcases Hrun checked hcheck with ⟨type', Htype, HtypeWF⟩
  let constructor : VConstVal := {
    uvars := lparams.length
    name := ctor.name
    type := type' }
  exact ⟨constructor, ⟨rfl, rfl, Htype, HtypeWF⟩⟩

/-- The source constants of all constructors of a family, pointwise along the
constructor list, from the successful validation run. -/
theorem validateSourceConstructorTypes.sourceConsts_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (Hsources : SourceSyntaxChecks types)
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams
      safety fuel types = .ok ())
    (htype : indType ∈ types) :
    ∃ constructors : List VConstVal,
      List.Forall₂ (fun source constructor =>
        TrSourceConst venv lparams source.name source.type constructor)
        indType.ctors constructors := by
  apply forallExists_to_forall₂
  intro ctor hctor
  exact validateSourceConstructorTypes.sourceConst_of_run hvalid
    hmode Hsources hrun htype hctor

private theorem validateRestoredRecursorTypes.sourceCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types) :
    Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
      safety fuel result recNameMap allIndNames (Lean.mkRecName indType.name) =
        .ok () := by
  unfold Lean4Lean.validateRestoredRecursorTypes.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
        safety fuel result recNameMap allIndNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok done =>
      rcases done with ⟨⟩
      exact listForM_eq_ok_of_mem
        (fun type : InductiveType =>
          Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
            safety fuel result recNameMap allIndNames
              (Lean.mkRecName type.name)) hprimary htype

/-- The successful type check of one restored source recursor, selected from
the successful whole-block validation run. -/
theorem validateRestoredRecursorTypes.typeCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      (Lean.mkRecName indType.name) newRecName oldInfo
    ∃ checked,
      env.checkNoMVarNoFVar restored.name restored.type = .ok () ∧
      TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) (do
          let type ← TypeChecker.checkType restored.type
          TypeChecker.ensureSort type restored.type) = .ok checked := by
  dsimp only
  have hcheck :=
    validateRestoredRecursorTypes.sourceCheck_eq_ok_of_run hrun htype
  unfold Lean4Lean.validateRestoredRecursorTypes.check at hcheck
  rw [hlookup] at hcheck
  simp only at hcheck
  cases hclosed : env.checkNoMVarNoFVar
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).name
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).type with
  | error err =>
      rw [hclosed] at hcheck
      simp only [bind, Except.bind] at hcheck
      cases hcheck
  | ok done =>
      rcases done with ⟨⟩
      cases htypecheck : TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := (result.restoreRecursor loweredEnv recNameMap allIndNames
            (Lean.mkRecName indType.name)
            (recNameMap.getD (Lean.mkRecName indType.name)
              (Lean.mkRecName indType.name)) oldInfo).levelParams)
          (fuel := fuel) (do
            let type ← TypeChecker.checkType
              (result.restoreRecursor loweredEnv recNameMap allIndNames
                (Lean.mkRecName indType.name)
                (recNameMap.getD (Lean.mkRecName indType.name)
                  (Lean.mkRecName indType.name)) oldInfo).type
            TypeChecker.ensureSort type
              (result.restoreRecursor loweredEnv recNameMap allIndNames
                (Lean.mkRecName indType.name)
                (recNameMap.getD (Lean.mkRecName indType.name)
                  (Lean.mkRecName indType.name)) oldInfo).type) with
      | error err =>
          rw [hclosed, htypecheck] at hcheck
          simp only [bind, Except.bind] at hcheck
          cases hcheck
      | ok checked => exact ⟨checked, by simp, rfl⟩

/-- The executable recursor-type pass gives a translation of the restored
source recursor type, which is a type. -/
theorem validateRestoredRecursorTypes.translation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      (Lean.mkRecName indType.name) newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  dsimp only
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    (Lean.mkRecName indType.name)
    (recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)) oldInfo
  rcases validateRestoredRecursorTypes.typeCheck_eq_ok_of_run hrun htype
      hlookup with ⟨checked, hclosedRunFull, hcheck⟩
  have hclosedRun : env.checkNoMVarNoFVar restored.name restored.type =
      .ok () := by
    simpa only [restored] using hclosedRunFull
  have hclosed : restored.type.FVarsIn fun _ => False :=
    checkNoMVarNoFVar.closed hclosedRun
  have hfvars : restored.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams
        fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType restored.type
      TypeChecker.ensureSort type restored.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams fuel) {}
      fun _ _ => ∃ type', TrExprS venv restored.levelParams []
          restored.type type' ∧
        venv.IsType restored.levelParams.length [] type' := by
    refine (TypeChecker.checkType.WF (e := restored.type) hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype,
        ⟨_, hhasType.defeqU_r hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid Hcheck hmode
  exact Hrun checked hcheck

private theorem validateRestoredRecursorTypes.auxiliaryCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames) :
    Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
      safety fuel result recNameMap allIndNames recName = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorTypes.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
        safety fuel result recNameMap allIndNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok done =>
      rcases done with ⟨⟩
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      exact listForM_eq_ok_of_mem
        (Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
          safety fuel result recNameMap allIndNames) hrun hrec

/-- A successful check of any restored recursor (source or auxiliary)
gives a translation of the type produced by `restoreRecursor`, which is a type. -/
theorem validateRestoredRecursorTypes.translation_of_check
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (hstep : Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv safety fuel result recNameMap allIndNames recName = .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  dsimp only
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName (recNameMap.getD recName recName) oldInfo
  unfold Lean4Lean.validateRestoredRecursorTypes.check at hstep
  rw [hlookup] at hstep
  simp only at hstep
  have hclosedRun : env.checkNoMVarNoFVar restored.name restored.type =
      .ok () := by
    cases hclosed : env.checkNoMVarNoFVar restored.name restored.type with
    | error err =>
        rw [hclosed] at hstep
        simp only [bind, Except.bind] at hstep
        cases hstep
    | ok done =>
        rcases done with ⟨⟩
        simp
  have hclosed : restored.type.FVarsIn fun _ => False :=
    checkNoMVarNoFVar.closed hclosedRun
  have hfvars : restored.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams
        fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType restored.type
      TypeChecker.ensureSort type restored.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams fuel) {}
      fun _ _ => ∃ type', TrExprS venv restored.levelParams []
          restored.type type' ∧
        venv.IsType restored.levelParams.length [] type' := by
    refine (TypeChecker.checkType.WF (e := restored.type) hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype,
        ⟨_, hhasType.defeqU_r hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid Hcheck hmode
  cases htypecheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := restored.levelParams) (fuel := fuel) (do
        let type ← TypeChecker.checkType restored.type
        TypeChecker.ensureSort type restored.type) with
  | error err =>
      rw [hclosedRun, htypecheck] at hstep
      simp only [bind, Except.bind] at hstep
      cases hstep
  | ok checked => exact Hrun checked htypecheck

/-- The translation of one restored auxiliary recursor type, selected from the
successful whole-block validation run. -/
theorem validateRestoredRecursorTypes.auxiliaryTranslation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  exact validateRestoredRecursorTypes.translation_of_check hvalid
    hmode (validateRestoredRecursorTypes.auxiliaryCheck_eq_ok_of_run hrun hrec)
      hlookup

private theorem validateRestoredRecursorRules.sourceCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types) :
    Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      safety fuel result recNameMap allIndNames
        (Lean.mkRecName indType.name) = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorRules.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
        safety fuel result recNameMap allIndNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok done =>
      rcases done with ⟨⟩
      exact listForM_eq_ok_of_mem
        (fun type : InductiveType =>
          Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
            safety fuel result recNameMap allIndNames
              (Lean.mkRecName type.name)) hprimary htype

private theorem validateRestoredRecursorRules.auxiliaryCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames) :
    Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      safety fuel result recNameMap allIndNames recName = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorRules.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
        safety fuel result recNameMap allIndNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok done =>
      rcases done with ⟨⟩
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      exact listForM_eq_ok_of_mem
        (Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
          safety fuel result recNameMap allIndNames) hrun hrec

/-- A successful restored-rule check gives a translated typing (`TrTyping`) of
the right-hand side of every rule of the restored recursor, read off the
executable's validation of the restored rules. -/
theorem validateRestoredRecursorRules.translation_of_check
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (hstep : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv safety fuel result recNameMap allIndNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams []
        rule.rhs inferred target targetType := by
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName (recNameMap.getD recName recName) oldInfo
  unfold Lean4Lean.validateRestoredRecursorRules.check at hstep
  rw [hlookup] at hstep
  simp only at hstep
  have hruleStep : (do
      env.checkNoMVarNoFVar restored.name rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          TypeChecker.checkType rule.rhs) = .ok () := by
    apply listForM_eq_ok_of_mem
      (fun candidate : RecursorRule => do
        env.checkNoMVarNoFVar restored.name candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            TypeChecker.checkType candidate.rhs)
    · simpa only [restored] using hstep
    · simpa only [restored] using hrule
  have hclosedRun : env.checkNoMVarNoFVar restored.name rule.rhs = .ok () := by
    cases hclosed : env.checkNoMVarNoFVar restored.name rule.rhs with
    | error err =>
        rw [hclosed] at hruleStep
        simp only [bind, Except.bind] at hruleStep
        cases hruleStep
    | ok done =>
        rcases done with ⟨⟩
        simp
  have hclosed : rule.rhs.FVarsIn fun _ => False :=
    checkNoMVarNoFVar.closed hclosedRun
  have hfvars : rule.rhs.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams
        fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck := TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := restored.levelParams) (fuel := fuel)
    (TypeChecker.checkType.WF (e := rule.rhs) hfvars) hmode
  cases htypecheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := restored.levelParams) (fuel := fuel)
      (TypeChecker.checkType rule.rhs) with
  | error err =>
      rw [hclosedRun, htypecheck] at hruleStep
      simp only [bind, Except.bind] at hruleStep
      cases hruleStep
  | ok inferred =>
      rcases Hcheck inferred htypecheck with ⟨target, targetType, Htyping⟩
      exact ⟨inferred, target, targetType, Htyping⟩

/-- `translation_of_check` for a source recursor, selected from the
successful whole-block rule-validation run. -/
theorem validateRestoredRecursorRules.sourceTranslation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).rules) :
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).levelParams []
        rule.rhs inferred target targetType := by
  exact validateRestoredRecursorRules.translation_of_check hvalid
    hmode (validateRestoredRecursorRules.sourceCheck_eq_ok_of_run hrun htype)
      hlookup hrule

/-- `translation_of_check` for an auxiliary recursor, selected from the
successful whole-block rule-validation run. -/
theorem validateRestoredRecursorRules.auxiliaryTranslation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams []
        rule.rhs inferred target targetType := by
  exact validateRestoredRecursorRules.translation_of_check hvalid
    hmode (validateRestoredRecursorRules.auxiliaryCheck_eq_ok_of_run hrun hrec)
      hlookup hrule

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The concrete parameter context returned by an actual lowering run has a
semantic metacontext in the source environment.  Its free variables are also
fresh for the independent type-checker run used by restored-constructor
validation; both facts follow from the lowering run `NestedLowering`. -/
theorem NestedLowering.resultParameterMLCtx
    (H : NestedLowering env fuel nparams types initialState out)
    (henv : venv.WF)
    (Hfirst : ∀ first rest, types = first :: rest →
      ∃ target, TrExprS venv Us [] first.type target)
    (hprefix : initialState.ngen.namePrefix = `_nested_fresh) :
    ∃ mlctx : TypeChecker.MLCtx,
      mlctx.lctx = out.1.lctx ∧
      mlctx.WF venv Us ∧
      (∀ fv ∈ mlctx.vlctx.fvars,
        ({} : TypeChecker.State).ngen.Reserves fv) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _hparamsPrefix, Hctx,
      _Hselection, Hqueue⟩
  rcases Hfirst first rest htypes with ⟨target, Htype⟩
  rcases Hopening.toMLCtx henv Hctx.wf .nil rfl trivial Htype with
    ⟨mlctx, _targetTail, hlctx, hmlctx, _Htail⟩
  refine ⟨mlctx, ?_, hmlctx, ?_⟩
  · exact hlctx.trans Hqueue.resultContext.1.symm
  · intro fv hfv
    apply H.resultContextKernelFresh hprefix fv
    rw [Hqueue.resultContext.1, ← hlctx, hmlctx.tr.fvars_eq]
    exact hfv

end VerifyInductive
end Lean4Lean
