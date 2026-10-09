import Lean4Lean.Verify.Inductive.Recursor.Signature.Assembly
import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorSpine
import Lean4Lean.Verify.Inductive.Recursor.Context.DeclarationUniverses
import Lean4Lean.Verify.Inductive.Recursor.Binders.InductionHypothesisUniverses

/-! Universe support of the higher-order argument telescope of an induction
hypothesis.

The executable `loopUArgs` infers the type of a recursive field, normalizes it
and then repeatedly opens a forall binder and normalizes the instantiated body.
Each of these type-checker calls preserves the universe-parameter support of
its input (`VContext.LevelsBelow`), relative to any universe scope of the
local context.  Starting from a universe scope containing the field, every
argument declaration opened by the traversal, and the exposed family
application, therefore mention only the universe parameters of that scope. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-! ### Induction-hypothesis argument universes -/

/-! ### The recursor construction -/

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The recursive calls recorded in the rule templates mention only the declaration's universe
parameters (`ArgumentUniverses`). This is read off the typed call templates
(`TypedCallTemplate.universes`): each template's root context extends the recursor context and
so has the declaration's universe parameters. -/
theorem RecursorConstruction.argumentUniverses (H : RecursorConstruction R) :
    H.ArgumentUniverses := by
  intro owner howner localIndex hlocal
  dsimp only
  intro j hj
  obtain ⟨⟨_, _, _, _, F, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨HcallAt⟩⟩⟩ :=
    H.templateTyping.entry owner howner localIndex hlocal
  have hj' : j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size := by
    rw [← HcallAt.size_eq]
    exact hj
  obtain ⟨originRoot, Rorigin, prior, Hprior, _, _, ⟨Csem⟩⟩ := HcallAt.entry j hj'
  have hl : originRoot.lparams = c.lparams := by
    rw [Hprior.contextLE.lparams_eq, ← F.terminalExtension.contextLE.lparams_eq,
      H.localExtends.lparams_eq]
  have hU := Csem.universes
  rw [hl] at hU
  exact hU

end

end Lean4Lean.VerifyInductive
