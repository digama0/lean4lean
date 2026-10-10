import Lean4Lean.Verify.Inductive.Recursor.Installation
import Lean4Lean.Verify.Inductive.Recursor.InstanceAlignment

/-! Facts about the recursor installation used by the rule typing (source branch:
`Install/BlockCertificate.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}

theorem RecursorInstallation.generatedTelescopeTranslations
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) :
    RecursorTypeTelescopes
      R.context.venv stats
      H.recInfos H.entries := by
  intro ownerIdx hentry
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [← H.generated.length]
    exact hentry
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    ownerIdx hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  refine ⟨E.info, E.source_eq, ?_⟩
  exact E.telescopeTranslation selections hrecInfo hnoalias

theorem RecursorInstallation.generatedRecursorCommonPrefixBinderDomainAt
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (i : Nat)
    (hi : i < stats.params.size +
      (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size)
    {domain₁ domain₂ : Expr}
    (Hbinder₁ : Expr.ForallBinderAt
      (H.generated.entry owner₁ howner₁).info.type i domain₁)
    (Hbinder₂ : Expr.ForallBinderAt
      (H.generated.entry owner₂ howner₂).info.type i domain₂) :
    domain₁ = domain₂ := by
  have hrecInfo₁ : owner₁ < H.recInfos.size := by
    simpa [H.generated.length] using howner₁
  have hrecInfo₂ : owner₂ < H.recInfos.size := by
    simpa [H.generated.length] using howner₂
  let E₁ := H.generated.entry owner₁ howner₁
  let E₂ := H.generated.entry owner₂ howner₂
  let S₁ := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner₁ hrecInfo₁
  let S₂ := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner₂ hrecInfo₂
  have hnoalias₁ : S₁.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₁ hrecInfo₁
  have hnoalias₂ : S₂.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₂ hrecInfo₂
  by_cases hparam : i < stats.params.size
  · rcases H.params.declarationAt H.localWF i hparam with ⟨D⟩
    have Hcanonical₁ := S₁.parameterBinderAt hnoalias₁ D
    have Hcanonical₂ := S₂.parameterBinderAt hnoalias₂ D
    dsimp only at Hcanonical₁ Hcanonical₂
    rw [← E₁.type] at Hcanonical₁
    rw [← E₂.type] at Hcanonical₂
    exact (Hbinder₁.unique Hcanonical₁).trans
      (Hbinder₂.unique Hcanonical₂).symm
  · let motiveIdx := i - stats.params.size
    by_cases hmotive : motiveIdx < (H.recInfos.map (·.motive)).size
    · rcases H.bindings.motives.declarationAt H.localWF motiveIdx hmotive with
        ⟨D⟩
      have Hcanonical₁ := S₁.motiveBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.motiveBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size + motiveIdx = i := by
        dsimp [motiveIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm
    · let minorIdx := i - stats.params.size -
        (H.recInfos.map (·.motive)).size
      have hminor : minorIdx <
          (H.recInfos.flatMap (·.minors)).size := by
        dsimp [motiveIdx, minorIdx] at hmotive ⊢
        omega
      rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx hminor with
        ⟨D⟩
      have Hcanonical₁ := S₁.minorBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.minorBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size +
          (H.recInfos.map (·.motive)).size + minorIdx = i := by
        dsimp [minorIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm



end VerifyInductive
end Lean4Lean
