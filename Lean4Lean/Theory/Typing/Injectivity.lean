import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! Structural inversion theorems for definitional equality.

Each inversion converts an `IsDefEqU` between a type of known sort and anything into a
one-link `TypeChain` (using `IsDefEq.uniq` to retype it at that sort), then reads off a field
of `HeadInversion`. All of them depend only on the base obligation
`VEnv.WF.headInversion`. -/

namespace Lean4Lean
namespace VEnv

/-- An `IsDefEqU` whose left side has type `sort u` is a one-link chain. -/
theorem IsDefEqU.typeChain (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A B) (h2 : env.HasType U Γ A (.sort u)) :
    env.TypeChain U Γ A B := .single (h1.of_l henv hΓ h2)

theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  have ⟨_, h⟩ := h1
  henv.headInversion.sort_sort hΓ (h1.typeChain henv hΓ (.sort (h.sort_inv_l henv.ordered)))

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  have ⟨_, h⟩ := h1
  have ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := h.hasType.1.forallE_inv henv.ordered
  henv.headInversion.forallE_forallE hΓ (h1.typeChain henv hΓ (.forallE hA hB))

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := fun h1 =>
  have ⟨_, h⟩ := h1
  henv.headInversion.sort_forallE hΓ
    (h1.typeChain henv hΓ (.sort (h.sort_inv_l henv.ordered)))

/-- Injectivity of applications of a rigid constant, at the type level: two definitionally
equal types headed by the same rigid constant have equivalent universe levels and pairwise
definitionally equal arguments. The sort-typing hypothesis is essential: at term level
rigid heads are not injective (proof irrelevance, `structEta`). -/
theorem IsDefEqU.rigidApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : env.Rigid c)
    (h1 : env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c ls') args'))
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args' :=
  (henv.headInversion.rigid_rigid hΓ hrigid hrigid (h1.typeChain henv hΓ h2)).2

/-- A registered structure head is rigid by its declaration history, so the
general rigid-head injectivity theorem applies. -/
theorem IsDefEqU.structApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections c info)
    (h1 : env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c ls') args'))
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args' :=
  IsDefEqU.rigidApp_inv henv hΓ (henv.projectionRigid hinfo) h1 h2

/-- A type headed by a rigid constant is not a Pi type. -/
theorem IsDefEqU.rigidApp_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : env.Rigid c)
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    ¬env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (.forallE A B) := fun h1 =>
  henv.headInversion.forallE_rigid hΓ hrigid (h1.typeChain henv hΓ h2).symm

/-- Types headed by distinct rigid constants are not definitionally equal. -/
theorem IsDefEqU.rigidApp_ne (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hc : env.Rigid c) (hc' : env.Rigid c') (hne : c ≠ c')
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    ¬env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c' ls') args') :=
  fun h1 => hne (henv.headInversion.rigid_rigid hΓ hc hc' (h1.typeChain henv hΓ h2)).1

/-- An application headed by a type former of a declared inductive block is defeq to
neither a sort nor a Π-type: the type former is rigid (`VEnv.WF'.inductTypeRigid`), so
`HeadInversion.sort_rigid`/`forallE_rigid` apply. The typing hypothesis is kept for
compatibility with the statement of PR #43; the typing is read off the definitional equality. -/
theorem IsDefEqU.const_arity_inv {ds : List VDecl} {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : env.WF' ds) (hΓ : OnCtx Γ (env.IsType U))
    {decl : VInductDecl} {t : VInductiveType} {us : List VLevel} {args : List VExpr}
    (hdecl : VDecl.induct decl ∈ ds) (htype : t ∈ decl.types)
    (_hty : ∃ V, env.HasType U Γ ((VExpr.const t.name us).mkApps args) V) :
    (∀ u, ¬ env.IsDefEqU U Γ ((VExpr.const t.name us).mkApps args) (.sort u)) ∧
    (∀ A B, ¬ env.IsDefEqU U Γ ((VExpr.const t.name us).mkApps args) (.forallE A B)) := by
  have hwf : env.WF := ⟨ds, henv⟩
  have hrigid := henv.inductTypeRigid hdecl htype
  refine ⟨fun u ⟨B, h⟩ => ?_, fun A B' ⟨B, h⟩ => ?_⟩
  · have hu : u.WF U := h.symm.sort_inv_l hwf.ordered
    have ⟨_, hB⟩ := IsDefEq.uniq hwf hΓ h.hasType.2 (HasType.sort hu)
    have hA : env.HasType U Γ ((VExpr.const t.name us).mkApps args) (.sort (.succ u)) :=
      .defeqDF hB h.hasType.1
    exact hwf.headInversion.sort_rigid hΓ hrigid (IsDefEqU.typeChain hwf hΓ ⟨_, h⟩ hA).symm
  · have ⟨⟨u, hA⟩, ⟨v, hB'⟩⟩ := h.hasType.2.forallE_inv hwf.ordered
    have ⟨_, hB⟩ := IsDefEq.uniq hwf hΓ h.hasType.2 (HasType.forallE hA hB')
    have hA' : env.HasType U Γ ((VExpr.const t.name us).mkApps args) (.sort (.imax u v)) :=
      .defeqDF hB h.hasType.1
    exact hwf.headInversion.forallE_rigid hΓ hrigid (IsDefEqU.typeChain hwf hΓ ⟨_, h⟩ hA').symm
