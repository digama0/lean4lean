import Lean4Lean.Theory.Inductive.Restoration

namespace Lean4Lean.Tests.InductiveRestoration
open Lean4Lean.InductiveSignature

private def pair (a b : VExpr) := VExpr.mkApps (.const `Pair []) [a, b]

/-- Open arguments must be substituted simultaneously. Sequential substitution
would change the first inserted argument when inserting the second. -/
theorem simultaneousOpenParameters :
    instantiateParams (pair (.bvar 1) (.bvar 0)) [.bvar 0, .bvar 1] =
      pair (.bvar 0) (.bvar 1) := rfl

/-- A local binder is retained; inserted free variables are lifted past it. -/
theorem parametersUnderBinder :
    instantiateParams (.lam (.sort .zero)
      (pair (pair (.bvar 2) (.bvar 1)) (.bvar 0))) [.bvar 0, .bvar 1] =
    .lam (.sort .zero) (pair (pair (.bvar 1) (.bvar 2)) (.bvar 0)) := rfl

example : instantiateParams (.bvar 3) [.bvar 0, .bvar 1] = .bvar 1 := rfl

example : specializeType
    (.forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (pair (.bvar 2) (.bvar 1)))))
    [.bvar 0, .bvar 1] =
    some (.forallE (.bvar 0) (pair (.bvar 1) (.bvar 2))) := rfl

example : specializeType (.forallE (.sort .zero) (.sort .zero))
    [.bvar 0, .bvar 1] = none := rfl

private def parametricHead : HeadSpecialization where
  auxiliary := `Aux
  uvars := 1
  nparams := 2
  target := `Container
  levels := [.succ (.param 0)]
  arguments := [.sort (.param 0), pair (.bvar 1) (.bvar 0)]

/-- Specialization changes universes in both the head and its argument types,
preserves argument order, and retains trailing indices. -/
example : parametricHead.apply [.succ .zero] [.bvar 0, .bvar 1, .bvar 2] =
    some (VExpr.mkApps (.const `Container [.succ (.succ .zero)])
      [.sort (.succ .zero), pair (.bvar 0) (.bvar 1), .bvar 2]) := rfl

example : parametricHead.apply [] [.bvar 0, .bvar 1] = none := rfl
example : parametricHead.apply [.zero, .zero] [.bvar 0, .bvar 1] = none := rfl
example : parametricHead.apply [.zero] [.bvar 0] = none := rfl

private def parametricRestoration : Restoration := { heads := [parametricHead] }

/-- Traversal reaches occurrences in trailing indices before substituting the
outer head. An inner index must not retain the auxiliary constant. -/
example : parametricRestoration.expr
    (VExpr.mkApps (.const `Aux [.zero])
      [.bvar 0, .bvar 1,
        VExpr.mkApps (.const `Aux [.zero]) [.bvar 2, .bvar 3]]) =
    some (VExpr.mkApps (.const `Container [.succ .zero])
      [.sort .zero, pair (.bvar 0) (.bvar 1),
        VExpr.mkApps (.const `Container [.succ .zero])
          [.sort .zero, pair (.bvar 2) (.bvar 3)]]) := rfl

/-- Both domains and bodies of higher-order fields are restored, using the
actual arguments at their respective binder depths. -/
example : parametricRestoration.expr
    (.forallE (VExpr.mkApps (.const `Aux [.zero]) [.bvar 0, .bvar 1])
      (.lam (.sort .zero)
        (VExpr.mkApps (.const `Aux [.zero]) [.bvar 2, .bvar 1, .bvar 0]))) =
    some (.forallE (VExpr.mkApps (.const `Container [.succ .zero])
      [.sort .zero, pair (.bvar 0) (.bvar 1)])
      (.lam (.sort .zero) (VExpr.mkApps (.const `Container [.succ .zero])
        [.sort .zero, pair (.bvar 2) (.bvar 1), .bvar 0]))) := rfl

/-- Failure in an argument propagates through an otherwise valid outer spine. -/
example : parametricRestoration.expr
    (VExpr.mkApps (.const `Aux [.zero])
      [.bvar 0, .bvar 1, .const `Aux [.zero]]) = none := rfl

private def tree : VExpr := .const `Tree []
private def list : VExpr := .app (.const `List [.succ .zero]) tree
private def nil : VExpr := .app (.const `List.nil [.succ .zero]) tree
private def cons (a b : VExpr) : VExpr :=
  VExpr.mkApps (.const `List.cons [.succ .zero]) [tree, a, b]

private def listSignature : Lean4Lean.InductiveSignature where
  uvars := 0
  params := []
  families := #[{ name := `AuxList, indices := [], resultLevel := .succ .zero }]
  constructors := #[
    { name := `AuxList.nil, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `AuxList.cons, owner := ⟨0, by decide⟩,
      fields := [.external tree,
        .recursive (.const `AuxList [])
          { binders := [], target := ⟨0, by decide⟩, indices := [] }], indices := [] }]

private def listInstance : Instance listSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `AuxList.rec

private def listRestoration : Restoration where
  heads := [
    { auxiliary := `AuxList, uvars := 0, nparams := 0,
      target := `List, levels := [.succ .zero], arguments := [tree] },
    { auxiliary := `AuxList.nil, uvars := 0, nparams := 0,
      target := `List.nil, levels := [.succ .zero], arguments := [tree] },
    { auxiliary := `AuxList.cons, uvars := 0, nparams := 0,
      target := `List.cons, levels := [.succ .zero], arguments := [tree] }]
  recursors := [(`AuxList.rec, `Tree.rec_1)]

private def motive : VExpr := .forallE list (.sort (.param 0))
private def nilMinor : VExpr := .app (.bvar 0) nil
private def consMinor : VExpr :=
  VExpr.wrapForalls [tree, list, .app (.bvar 3) (.bvar 0)]
    (.app (.bvar 4) (cons (.bvar 2) (.bvar 1)))

/-- The auxiliary recursor has no common parameters, while restored List
constructors have one. Generation and restoration preserve this distinction
in every binder domain, both equation sides, and the equation type. -/
theorem specializedConstructorEquation :
    listRestoration.equation (listInstance.equation ⟨1, by decide⟩) =
    some {
      uvars := 1
      lhs := VExpr.wrapLams [motive, nilMinor, consMinor, tree, list]
        (VExpr.mkApps (.const `Tree.rec_1 [.param 0])
          [.bvar 4, .bvar 3, .bvar 2, cons (.bvar 1) (.bvar 0)])
      rhs := VExpr.wrapLams [motive, nilMinor, consMinor, tree, list]
        (VExpr.mkApps (.bvar 2) [.bvar 1, .bvar 0,
          VExpr.mkApps (.const `Tree.rec_1 [.param 0])
            [.bvar 4, .bvar 3, .bvar 2, .bvar 0]])
      type := VExpr.wrapForalls [motive, nilMinor, consMinor, tree, list]
        (.app (.bvar 4) (cons (.bvar 1) (.bvar 0))) } := rfl

example : (listInstance.restoredEquations listRestoration).map List.length = some 2 := rfl

/-- Renaming applies to the declaration and its generated type together. -/
example : listRestoration.recursor (listInstance.recursor ⟨0, by decide⟩) =
    some {
      name := `Tree.rec_1
      uvars := 1
      type := VExpr.wrapForalls [motive, nilMinor, consMinor, list]
        (.app (.bvar 3) (.bvar 0)) } := rfl

end Lean4Lean.Tests.InductiveRestoration
