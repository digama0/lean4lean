import Lean4Lean.Verify.TypeChecker

/-!
The checker's soundness applies in an ambient local context, not only in the empty one: a
context holding one variable of type `Prop` is well formed over every environment model, its
variable is never produced by the kernel's name generator, and inferring the variable's type
there is sound.
-/

namespace Lean4Lean.Tests.AmbientContext

open Lean hiding Environment Exception
open Kernel TypeChecker

/-- `x : Prop`. -/
def ambient : MLCtx := .vlam ⟨`x⟩ `x (.sort .zero) (.sort .zero) .default .nil

theorem ambient_wf {venv : VEnv} : ambient.WF venv [] :=
  ⟨trivial, LocalContext.find?_empty _, .sort rfl, ⟨_, .sort trivial⟩⟩

theorem ambient_fresh : ∀ fv ∈ ambient.vlctx.fvars, ({} : State).ngen.Reserves fv := by
  simp [ambient, NameGenerator.Reserves]

example {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) :
    (M.run env safety ambient.lctx [] {} (inferType (.fvar ⟨`x⟩))).WF fun ty =>
      ∃ e' ty', TrTyping venv [] ambient.vlctx (.fvar ⟨`x⟩) ty e' ty' :=
  M.WF.run1' wf ambient_wf ambient_fresh <| (inferType.WF (.fvar rfl)).mono
    fun _ _ _ ⟨ty', h⟩ => ⟨_, ty', h⟩

end Lean4Lean.Tests.AmbientContext
