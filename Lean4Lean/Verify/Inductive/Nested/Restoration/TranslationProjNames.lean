import Lean4Lean.Verify.Inductive.Nested.Restoration.ProjNamesOK
import Lean4Lean.Verify.ParamUniformEnv
import Lean4Lean.Verify.Typing.Syntactic.Basic

/-! # Projection names of translated syntax

A projection condition `ok` on the type names of the projections of the source syntax
(`Expr.ProjsOK`) holds for its translation (`VExpr.ProjNamesOK`), given it for the values
of the translation context (`TrSyn.projNamesOK_of_source`, `TrExprS.projNamesOK_of_source`). -/

namespace Lean4Lean

open Lean hiding Environment Exception

/-- Every value of the context satisfies the projection condition. -/
def VLCtx.ProjNamesOK (ok : Name → Prop) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) → mapped.ProjNamesOK ok

theorem VLCtx.ProjNamesOK.nil {ok : Name → Prop} : VLCtx.ProjNamesOK ok [] := by
  intro v mapped type h
  cases v <;> simp [VLCtx.find?] at h

theorem VLCtx.ProjNamesOK.cons {ok : Name → Prop} {Δ : VLCtx} {d : VLocalDecl}
    {ofv : Option (FVarId × List FVarId)}
    (H : VLCtx.ProjNamesOK ok Δ) (hvalue : d.value.ProjNamesOK ok) :
    VLCtx.ProjNamesOK ok ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    exact (H hfind).liftN

theorem VLocalDecl.value_vlam_projNamesOK {ok : Name → Prop} {ty : VExpr} :
    (VLocalDecl.vlam ty).value.ProjNamesOK ok := trivial

theorem Literal.toConstructor_projsOK {ok : Name → Prop} :
    ∀ l : Literal, l.toConstructor.ProjsOK ok
  | .natVal _ => Expr.ProjsOK.natLitToConstructor
  | .strVal _ => Expr.ProjsOK.strLitToConstructor

/-- **Translation keeps projection names**: a projection condition on the
source syntax holds for its translation, given it for the values of the
context. -/
theorem TrSyn.projNamesOK_of_source {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrSyn Us Δ e e') {ok : Name → Prop}
    (hsrc : e.ProjsOK ok) (hΔ : VLCtx.ProjNamesOK ok Δ) : e'.ProjNamesOK ok := by
  induction H with
  | bvar hfind | fvar hfind => exact hΔ hfind
  | sort _ => trivial
  | const => trivial
  | app _ _ ihf iha => exact ⟨ihf hsrc.1 hΔ, iha hsrc.2 hΔ⟩
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    exact ⟨iht hsrc.1 hΔ, ihb hsrc.2 (hΔ.cons VLocalDecl.value_vlam_projNamesOK)⟩
  | letE _ _ _ _ ihv ihb =>
    exact ihb hsrc.2.2 (hΔ.cons (d := .vlet _ _) (ihv hsrc.2.1 hΔ))
  | lit _ ih => exact ih (Literal.toConstructor_projsOK _) hΔ
  | mdata _ ih => exact ih hsrc hΔ
  | proj _ ih => exact ⟨hsrc.1, ih hsrc.2 hΔ⟩

theorem TrExprS.projNamesOK_of_source {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') {ok : Name → Prop}
    (hsrc : e.ProjsOK ok) (hΔ : VLCtx.ProjNamesOK ok Δ) : e'.ProjNamesOK ok :=
  H.toTrSyn.projNamesOK_of_source hsrc hΔ

end Lean4Lean
