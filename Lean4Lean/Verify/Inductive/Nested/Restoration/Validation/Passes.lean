import Lean4Lean.Verify.Inductive.Nested.Restoration.RestorationRun
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Stripped

/-! # The validation passes (owner: Restoration-A)

The semantic content of the four validation passes of `restoreNestedAfterInstall`
(`RestorationRun`), each stated against a checker environment `CheckerEnv safety E V` for the
side environment `E` it runs in, as the wave 1A checker verification reads it
(`TypeChecker.checkType.WF`, `ensureSort.WF`, `checkNoMVarNoFVar.WF`): the checked syntax
translates and is typed in the model `V`. These are the boundary theorems of the
`Validation/` directory; the restoration owner (Restoration-B) instantiates them with the
models of the side environments it builds from the restoration folds, and the stripped
environment's model is `stripRecursorRules.checkingValid`.

Source branch: `Nested/Restoration/Validation/{Checks,Environment,ConstructorEnvironment,
StrippedEnvironment,StrippedRecursorShapes,ParameterScopes,ParameterPrefix,Result}.lean` and
`Nested/Restoration/Uniform/{Declarations,Recursors,Whnf}.lean` (parameter uniformity of the
restored telescopes under `whnf`, read by the recursor-type validation). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv}

/-- The restored recursor read by the recursor validation passes. -/
abbrev restoredRecursorOf (res : ElimNestedInductive.Result) (loweredEnv : Environment)
    (recNameMap : NameMap Name) (allIndNames : List Name) (recName : Name)
    (recInfo : RecursorVal) : RecursorVal :=
  res.restoreRecursor loweredEnv recNameMap allIndNames recName (recNameMap.getD recName recName)
    recInfo

/-- `validateSourceConstructorTypes`: every source constructor type is a type of the checker's
model (the restored header environment). The pass runs the checker in the empty local
context without checking for free variables, so the closedness of the constructor types is a
premise: the source checks establish it (`SourceSyntaxChecks.ctorTypesClosed`). -/
theorem validateSourceConstructorTypes.run.WF (C : CheckerEnv safety env venv)
    (lparams : List Name) (fuel : FuelConfig) (types : List InductiveType)
    (hclosed : ∀ type ∈ types, ∀ ctor ∈ type.ctors, ctor.type.FVarsIn fun _ => False)
    (h : validateSourceConstructorTypes.run env lparams safety fuel types = .ok ()) :
    ∀ type ∈ types, ∀ ctor ∈ type.ctors,
      ∃ T, TrExprS venv lparams [] ctor.type T ∧ venv.IsType lparams.length [] T := by
  intro type htype ctor hctor
  unfold validateSourceConstructorTypes.run at h
  have hstep := listForM_eq_ok_of_mem (fun ctor : Constructor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel)
        (do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type))
    (listForM_eq_ok_of_mem _ h htype) hctor
  obtain ⟨checked, hrun, -⟩ := except_bind_eq_ok hstep
  exact checkTypeSort.WF C (hclosed type htype ctor hctor) checked hrun

/-- `validateRestoredRecursorTypes.check`: the lowered recursor exists and its restored type is
closed and a type of the checker's model (the restored constructor environment). -/
theorem validateRestoredRecursorTypes.check.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (recName : Name)
    (h : validateRestoredRecursorTypes.check env loweredEnv safety fuel res recNameMap
      allIndNames recName = .ok ()) :
    ∃ recInfo, loweredEnv.find? recName = some (.recInfo recInfo) ∧
      ∃ T, TrExprS venv (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
          recInfo).levelParams []
        (restoredRecursorOf res loweredEnv recNameMap allIndNames recName recInfo).type T ∧
      venv.IsType (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
        recInfo).levelParams.length [] T := by
  unfold validateRestoredRecursorTypes.check at h
  split at h
  · rename_i recInfo hfind
    refine ⟨recInfo, hfind, ?_⟩
    obtain ⟨⟨⟩, hclosed, h⟩ := except_bind_eq_ok h
    obtain ⟨checked, hrun, -⟩ := except_bind_eq_ok h
    exact checkTypeSort.WF C (checkNoMVarNoFVar.closed hclosed) checked hrun
  · cases h

/-- `validateRestoredRecursorTypes.run`, over the source and auxiliary recursors. -/
theorem validateRestoredRecursorTypes.run.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name)
    (h : validateRestoredRecursorTypes.run env loweredEnv safety fuel res recNameMap allIndNames
      types auxRecNames = .ok ()) :
    ∀ recName ∈ types.map (mkRecName ·.name) ++ auxRecNames,
      validateRestoredRecursorTypes.check env loweredEnv safety fuel res recNameMap allIndNames
        recName = .ok () := by
  have := C
  exact forM_append_names_eq_ok _ h

/-- `validateRestoredRecursorRules.check`: the lowered recursor exists and the reduct of every
restored rule is closed and typed in the checker's model (the stripped restored
environment). -/
theorem validateRestoredRecursorRules.check.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (recName : Name)
    (h : validateRestoredRecursorRules.check env loweredEnv safety fuel res recNameMap
      allIndNames recName = .ok ()) :
    ∃ recInfo, loweredEnv.find? recName = some (.recInfo recInfo) ∧
      ∀ rule ∈ (restoredRecursorOf res loweredEnv recNameMap allIndNames recName recInfo).rules,
        ∃ rhs T, TrExprS venv (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
            recInfo).levelParams [] rule.rhs rhs ∧
          venv.HasType (restoredRecursorOf res loweredEnv recNameMap allIndNames recName
            recInfo).levelParams.length [] rhs T := by
  unfold validateRestoredRecursorRules.check at h
  split at h
  · rename_i recInfo hfind
    refine ⟨recInfo, hfind, fun rule hrule => ?_⟩
    have hstep := listForM_eq_ok_of_mem _ h hrule
    obtain ⟨⟨⟩, hclosed, hstep⟩ := except_bind_eq_ok hstep
    obtain ⟨checked, hrun, -⟩ := except_bind_eq_ok hstep
    exact checkTypeClosed.WF C (checkNoMVarNoFVar.closed hclosed) checked hrun
  · cases h

/-- `validateRestoredRecursorRules.run`, over the source and auxiliary recursors. -/
theorem validateRestoredRecursorRules.run.WF (C : CheckerEnv safety env venv)
    (loweredEnv : Environment) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (recNameMap : NameMap Name) (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name)
    (h : validateRestoredRecursorRules.run env loweredEnv safety fuel res recNameMap allIndNames
      types auxRecNames = .ok ()) :
    ∀ recName ∈ types.map (mkRecName ·.name) ++ auxRecNames,
      validateRestoredRecursorRules.check env loweredEnv safety fuel res recNameMap allIndNames
        recName = .ok () := by
  have := C
  exact forM_append_names_eq_ok _ h

/-- `validateNestedAuxiliaries`, with the inferred types: in a well-formed checker context
`mlctx` of the model (the restored header environment) whose local context is the lowering's,
every cached nested occurrence `I Ds` has a translated typing (`TrTyping`: the occurrence, its
inferred source type and their translations). This is the source branch's
`NestedOccurrencesTyped`. The pass runs the checker in `res.lctx` without checking it, so the
context `mlctx` (its translation, the freshness of its free variables for the checker's name
generator, and the scoping of the cached occurrences) is a premise:
`NestedLoweringOutput.parameterMLCtx` (`Validation/ParameterPrefix.lean`) supplies it. -/
theorem validateNestedAuxiliaries.WF_typing (C : CheckerEnv safety env venv)
    (lparams : List Name) (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams) (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv)
    (hfvars : ∀ n nested, res.aux2nested.find? n = some nested →
      nested.FVarsIn (· ∈ mlctx.vlctx.fvars))
    (h : validateNestedAuxiliaries env lparams safety fuel res = .ok ()) :
    ∀ n nested, res.aux2nested.find? n = some nested →
      ∃ ty e' ty', TrTyping venv lparams mlctx.vlctx nested ty e' ty' := by
  have H : (validateNestedAuxiliaries env lparams safety fuel res).WF fun _ =>
      ∀ n nested, res.aux2nested.find? n = some nested →
        ∃ ty e' ty', TrTyping venv lparams mlctx.vlctx nested ty e' ty' := by
    unfold validateNestedAuxiliaries
    rw [← hlctx]
    change (TypeChecker.M.run env safety mlctx.lctx lparams fuel
      ((show Std.TreeMap Name Expr Name.quickCmp from res.aux2nested).forM
        fun _ e => do
          _ ← TypeChecker.checkType e)).WF _
    rw [Std.TreeMap.forM_eq_forM, Std.TreeMap.forM_eq_forM_toList]
    refine TypeChecker.M.WF.runCheckingMLC (trenv := C) (mlctx_wf := hmlctx) hfresh ?_
    refine (checkTypeList.WF
      (c := TypeChecker.VContext.mkCheckingMLC C mlctx hmlctx fuel)
      (s := {}) res.aux2nested.toList ?_).mono ?_
    · intro item hitem
      apply hfvars item.1 item.2
      change (show Std.TreeMap Name Expr Name.quickCmp from
        res.aux2nested)[item.1]? = some item.2
      exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hitem
    · intro _ _ _ hall name e hfind
      apply hall (name, e)
      apply Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
      change (show Std.TreeMap Name Expr Name.quickCmp from
        res.aux2nested)[name]? = some e
      exact hfind
  exact H () h

/-- `validateNestedAuxiliaries`: in a well-formed checker context `mlctx` of the model whose
local context is the lowering's, every cached nested occurrence `I Ds` translates and is typed
(`validateNestedAuxiliaries.WF_typing` without the inferred type). -/
theorem validateNestedAuxiliaries.WF (C : CheckerEnv safety env venv) (lparams : List Name)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams) (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv)
    (hfvars : ∀ n nested, res.aux2nested.find? n = some nested →
      nested.FVarsIn (· ∈ mlctx.vlctx.fvars))
    (h : validateNestedAuxiliaries env lparams safety fuel res = .ok ()) :
    ∀ n nested, res.aux2nested.find? n = some nested →
      ∃ e T, TrExprS venv lparams mlctx.vlctx nested e ∧
        venv.HasType lparams.length mlctx.vlctx.toCtx e T := by
  intro n nested hfind
  obtain ⟨_, e, T, -, he, -, hT⟩ :=
    validateNestedAuxiliaries.WF_typing C lparams fuel res mlctx hmlctx hlctx hfresh hfvars h
      n nested hfind
  exact ⟨e, T, he, hT⟩

/-- **The stripped restored environment** (the output with the new recursors' rules removed,
in which the restored rules are validated) is a valid checking environment of the recursor
stage. It is stated through the rule-free installation `H` of the restored declaration with
every recursor's rules removed into the stripped map, so that no premise mentions the rules
being validated: the model is the recursor stage `H.envR`, where none of the block's ι rules is
registered (`RuleFreeStage`, `Validation/Stripped.lean`). -/
theorem stripRecursorRules.checkingValid {outEnv : Environment} {names : List Name}
    {decl : VInductDecl} {venv₂ : VEnv} (hin : CheckingEnv.Valid safety env venv)
    (H : AddInduct safety env.constants venv decl (stripRecursorRules outEnv names).constants
      venv₂)
    (F : RuleFreeStage safety env venv decl (stripRecursorRules outEnv names) venv₂ H) :
    CheckingEnv.Valid safety (stripRecursorRules outEnv names) H.envR :=
  F.checkingValid hin

/-- The stripped restored environment is a checker environment of the recursor stage, the
input of `validateRestoredRecursorRules.check.WF`. -/
theorem stripRecursorRules.checkerEnv {outEnv : Environment} {names : List Name}
    {decl : VInductDecl} {venv₂ : VEnv} (C : CheckerEnv safety env venv)
    (H : AddInduct safety env.constants venv decl (stripRecursorRules outEnv names).constants
      venv₂)
    (F : RuleFreeStage safety env venv decl (stripRecursorRules outEnv names) venv₂ H) :
    CheckerEnv safety (stripRecursorRules outEnv names) H.envR :=
  F.checkerEnv C

end VerifyInductive
end Lean4Lean
