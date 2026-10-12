import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorFields
import Lean4Lean.Verify.Inductive.Recursor.Context.DeclarationUniverses

/-! Uniqueness of translated binder telescopes.

A list of abstract domains translating a list of source domains, each in the
abstract context of the earlier ones, is determined by the sources.  A
well-formed lambda-only typechecker metacontext supplies such a telescope:
each stored binder type, abstracted over the earlier identifiers, translates
to the stored abstract domain in the abstract context of the earlier
domains. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

namespace VerifyInductive

/-- Two telescopes of abstract domains translating the same source domains,
each in the context of the earlier ones, coincide. -/
theorem TrExprS.telescope_unique {env : VEnv} {Us : List Name} (Δ : VLCtx) :
    ∀ (sources : List Lean.Expr) (L₁ L₂ : List VExpr),
      (h₁ : L₁.length = sources.length) → (h₂ : L₂.length = sources.length) →
      (∀ i (h : i < sources.length), TrExprS env Us (abstractForallContext (L₁.take i) Δ)
        sources[i] (L₁[i]'(by omega))) →
      (∀ i (h : i < sources.length), TrExprS env Us (abstractForallContext (L₂.take i) Δ)
        sources[i] (L₂[i]'(by omega))) →
      L₁ = L₂ := by
  intro sources L₁ L₂ h₁ h₂ H₁ H₂
  have key : ∀ n, n ≤ sources.length → L₁.take n = L₂.take n := by
    intro n
    induction n with
    | zero => intro; simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hn' : n < sources.length := by omega
      have heq : L₁[n]'(by omega) = L₂[n]'(by omega) := by
        have a := H₁ n hn'
        have b := H₂ n hn'
        rw [hprev] at a
        exact a.unique b
      rw [List.take_add_one, List.take_add_one, hprev, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (h := by omega), heq]
  have := key sources.length (Nat.le_refl _)
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this

end VerifyInductive
end Lean4Lean
