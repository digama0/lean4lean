import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.Typing

/-! # The family header of a projection-registered structure

For a projection entry `S`, `info` of the declaration history (`VEnv.ProjDecl`), the
family constant `S` is installed at the projection's universe arity, and its declared type is
definitionally a telescope over the header's own parameter domains and the index domains,
ending in the recorded result sort. The header's parameter domains and the constructor's raw
parameter domains are both context-convertible to the declaration's common parameter
telescope (`VEnv.ProjDeclAt.familyTele_data`).

Composing the header conversion and the two parameter conversions into a single
definitional equality at a sort needs uniqueness of types: `TypeShape` types the header
conversion at an arbitrary `exprType`, and the two context conversions are typed at possibly
different sorts per domain, so the conversions are kept separate (type classes of the model
absorb them, `Model/CommonParams.lean`). This file imports only the uniqueness-free base. -/

namespace Lean4Lean
namespace VEnv
variable {env : VEnv} {U : Nat}

/-- The body of a well-formed Pi telescope is a type in the telescope's context. -/
theorem IsType.wrapForalls_body (henv : env.Ordered) :
    ∀ {ds : List VExpr} {Γ : List VExpr} {R : VExpr},
      env.IsType U Γ (VExpr.wrapForalls ds R) → env.IsType U (ds.reverse ++ Γ) R
  | [], _, _, h => by simpa [VExpr.wrapForalls] using h
  | d :: ds, Γ, R, h => by
    obtain ⟨-, hB⟩ := IsType.forallE_inv henv h
    simpa [List.reverse_cons, List.append_assoc] using IsType.wrapForalls_body henv hB

/-- The head of a typed application spine is typed. -/
theorem HasType.mkApps_fn (henv : env.Ordered) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {f V : VExpr}, env.HasType U Γ (VExpr.mkApps f args) V →
      ∃ V', env.HasType U Γ f V'
  | [], _, _, h => ⟨_, h⟩
  | a :: as, f, V, h => by
    obtain ⟨V', h'⟩ := HasType.mkApps_fn henv hΓ (args := as) (f := .app f a) h
    obtain ⟨A, B, hf, -⟩ := HasType.app_inv henv hΓ h'
    exact ⟨_, hf⟩

/-- Congruence of a typed Pi telescope in its body. -/
theorem HasType.wrapForalls_congr_body (henv : env.Ordered) :
    ∀ {ds : List VExpr} {Γ : List VExpr} {B B' V : VExpr} {v : VLevel},
      env.HasType U Γ (VExpr.wrapForalls ds B) V →
      env.IsDefEq U (ds.reverse ++ Γ) B B' (.sort v) →
      ∃ w, env.IsDefEq U Γ (VExpr.wrapForalls ds B) (VExpr.wrapForalls ds B') (.sort w)
  | [], _, _, _, _, _, _, h => ⟨_, by simpa [VExpr.wrapForalls] using h⟩
  | d :: ds, Γ, B, B', V, v, hT, h => by
    obtain ⟨⟨u, hd⟩, ⟨u', hB⟩⟩ := HasType.forallE_inv henv hT
    obtain ⟨w, hw⟩ := HasType.wrapForalls_congr_body henv (Γ := d :: Γ) hB
      (by simpa [List.reverse_cons, List.append_assoc] using h)
    exact ⟨_, .forallEDF hd hw⟩
