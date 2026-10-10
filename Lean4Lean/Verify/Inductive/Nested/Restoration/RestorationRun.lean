import Lean4Lean.Verify.Inductive.Nested.Lowering.Basic

/-! # The executable restoration, as a record of its steps

`Environment.restoreNestedAfterInstall` restores the source declaration from the lowered
environment (`restoreNestedDeclarations`), builds two side environments (the restored headers
and constructors without recursors, `restoreNestedConstructors`; the restored headers alone,
`restoreNestedHeaders`) and runs four validation passes in them: the source constructor types
(`validateSourceConstructorTypes`), the restored recursor types
(`validateRestoredRecursorTypes`), the right-hand sides of the restored rules in the restored
environment with the new recursors' rules removed (`validateRestoredRecursorRules` in
`stripRecursorRules`), and the cached nested occurrences `I Ds` in the lowering's parameter
context (`validateNestedAuxiliaries`). `RestorationRun` records the successful steps and
`Environment.restoreNestedAfterInstall.WF` proves it (shared interface, proved); the restoration
owners read the steps off it. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The auxiliary recursor names of a lowered environment and their renaming. -/
abbrev auxRecNames (loweredEnv : Environment) (types : List InductiveType) : List Name :=
  (mkAuxRecNameMap loweredEnv types).1

abbrev auxRecNameMap (loweredEnv : Environment) (types : List InductiveType) : NameMap Name :=
  (mkAuxRecNameMap loweredEnv types).2

/-- The steps of a successful `restoreNestedAfterInstall`, each recorded as the executable's
own verdict. -/
structure RestorationRun (res : ElimNestedInductive.Result) (loweredEnv env : Environment)
    (lparams : List Name) (types : List InductiveType) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig) (outEnv : Environment) : Prop where
  /-- The restoration fold returns the output environment. -/
  restored : (restoreNestedDeclarations res loweredEnv (auxRecNameMap loweredEnv types)
    (types.map (·.name)) allowPrimitive types (auxRecNames loweredEnv types)).run env =
      .ok ((), outEnv)
  /-- The side environment of the restored headers and constructors, in which the restored
  recursor types were checked. -/
  validation : ∃ validationEnv,
    (restoreNestedConstructors res loweredEnv (types.map (·.name)) allowPrimitive types).run
      env = .ok ((), validationEnv) ∧
    validateRestoredRecursorTypes.run validationEnv loweredEnv safety fuel res
      (auxRecNameMap loweredEnv types) (types.map (·.name)) types
      (auxRecNames loweredEnv types) = .ok ()
  /-- The side environment of the restored headers, in which the source constructor types and
  the cached nested occurrences were checked. -/
  headers : ∃ auxiliaryHeaderEnv,
    (restoreNestedHeaders loweredEnv (types.map (·.name)) allowPrimitive types).run env =
      .ok ((), auxiliaryHeaderEnv) ∧
    validateSourceConstructorTypes.run auxiliaryHeaderEnv lparams safety fuel types = .ok () ∧
    validateNestedAuxiliaries auxiliaryHeaderEnv lparams safety fuel res = .ok ()
  /-- The restored rules' reducts were checked in the output with the new rules stripped. -/
  rules : validateRestoredRecursorRules.run
    (stripRecursorRules outEnv
      (restoredRecursorNames (auxRecNameMap loweredEnv types) types (auxRecNames loweredEnv types)))
    loweredEnv safety fuel res (auxRecNameMap loweredEnv types) (types.map (·.name)) types
    (auxRecNames loweredEnv types) = .ok ()

private theorem Except.WF.self {x : Except ε α} : x.WF fun a => x = .ok a := fun _ h => h

private theorem Except.WF.unit {x : Except ε Unit} : x.WF fun _ => x = .ok () :=
  fun a h => by cases a; exact h

private theorem Except.WF.stateRun {m : StateT σ (Except ε) Unit} {s : σ} :
    ((·.2) <$> m.run s).WF fun s' => m.run s = .ok ((), s') :=
  Except.WF.map Except.WF.self fun a h => by
    obtain ⟨⟨⟩, s'⟩ := a
    exact h

/-- `restoreNestedAfterInstall` records its steps. -/
theorem Environment.restoreNestedAfterInstall.WF (env loweredEnv : Environment)
    (lparams : List Name) (types : List InductiveType) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig) (res : ElimNestedInductive.Result) :
    (Environment.restoreNestedAfterInstall env loweredEnv lparams types safety allowPrimitive
      fuel res).WF
      (RestorationRun res loweredEnv env lparams types safety allowPrimitive fuel) := by
  unfold Environment.restoreNestedAfterInstall
  rcases hp : mkAuxRecNameMap loweredEnv types with ⟨recNames, recNameMap⟩
  refine Except.WF.bind Except.WF.stateRun fun restoredEnv hrestored => ?_
  refine Except.WF.bind Except.WF.stateRun fun validationEnv hvalidation => ?_
  refine Except.WF.bind Except.WF.stateRun fun auxiliaryHeaderEnv hheaders => ?_
  refine Except.WF.bind Except.WF.unit fun _ hsources => ?_
  refine Except.WF.bind Except.WF.unit fun _ hrecTypes => ?_
  refine Except.WF.bind Except.WF.unit fun _ hrules => ?_
  refine Except.WF.bind Except.WF.unit fun _ haux => ?_
  refine Except.WF.pure {
    restored := ?_
    validation := ⟨validationEnv, hvalidation, ?_⟩
    headers := ⟨auxiliaryHeaderEnv, hheaders, hsources, haux⟩
    rules := ?_ }
  · simpa [auxRecNameMap, auxRecNames, hp] using hrestored
  · simpa [auxRecNameMap, auxRecNames, hp] using hrecTypes
  · simpa [auxRecNameMap, auxRecNames, hp] using hrules

end VerifyInductive
end Lean4Lean
