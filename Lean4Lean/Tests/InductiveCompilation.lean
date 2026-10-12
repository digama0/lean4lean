import Lean4Lean.Theory.Inductive.Compilation

namespace Lean4Lean.Tests.InductiveCompilation
open Lean4Lean.InductiveSignature

private def list (u : VLevel) (a : VExpr) : VExpr :=
  .app (.const `ContainerList [u]) a

private def listSignature : Lean4Lean.InductiveSignature where
  uvars := 1
  params := [.sort (.param 0)]
  families := #[{ name := `ContainerList, indices := [], resultLevel := .param 0 }]
  constructors := #[
    { name := `ContainerList.nil, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `ContainerList.cons, owner := ⟨0, by decide⟩,
      fields := [.external (.bvar 0),
        .recursive (list (.param 0) (.bvar 1))
          { binders := [], target := ⟨0, by decide⟩, indices := [] }], indices := [] }]

private def box (a : VExpr) : VExpr := .app (.const `Box [.param 0]) a

private def dependentSpecialization : ContainerSpecialization where
  container := listSignature.declaration
  family := ⟨0, by decide⟩
  auxiliary := `AuxBoxList
  levels := [.param 0]
  arguments := [box (.bvar 0)]

/-- The direct auxiliary retains its common parameter and substitutes it at
the correct depth in each field and result. Its recursive domains still name
the source container: recursive expansion is a subsequent operation. -/
theorem dependentDirectFamily :
    dependentSpecialization.specializedFamily 1 [.sort (.param 0)] =
    some {
      name := `AuxBoxList
      uvars := 1
      type := .forallE (.sort (.param 0)) (.sort (.param 0))
      numIndices := 0
      resultLevel := .param 0
      ctors := [
        { name := `AuxBoxList.nil, uvars := 1,
          type := .forallE (.sort (.param 0)) (list (.param 0) (box (.bvar 0))) },
        { name := `AuxBoxList.cons, uvars := 1,
          type := VExpr.wrapForalls
            [.sort (.param 0), box (.bvar 0), list (.param 0) (box (.bvar 1))]
            (list (.param 0) (box (.bvar 2))) }] } := rfl

/-- Family and constructor restoration heads have the source's exact order;
the caller supplies neither the constructor list nor replacement targets. -/
theorem orderedRestorationHeads : dependentSpecialization.heads 1 1 = [
    { auxiliary := `AuxBoxList, uvars := 1, nparams := 1,
      target := `ContainerList, levels := [.param 0], arguments := [box (.bvar 0)] },
    { auxiliary := `AuxBoxList.nil, uvars := 1, nparams := 1,
      target := `ContainerList.nil, levels := [.param 0], arguments := [box (.bvar 0)] },
    { auxiliary := `AuxBoxList.cons, uvars := 1, nparams := 1,
      target := `ContainerList.cons, levels := [.param 0], arguments := [box (.bvar 0)] }
    ] := rfl

private def missingFamilyParameter : ContainerSpecialization :=
  { dependentSpecialization with container := {
      listSignature.declaration with types := [{
        name := `ContainerList, uvars := 1, type := .sort (.param 0),
        numIndices := 0, resultLevel := .param 0, ctors := [] }] } }

private def missingConstructorParameter : ContainerSpecialization :=
  { dependentSpecialization with container := {
      listSignature.declaration with types := [{
        name := `ContainerList, uvars := 1,
        type := .forallE (.sort (.param 0)) (.sort (.param 0)),
        numIndices := 0, resultLevel := .param 0,
        ctors := [{
          name := `ContainerList.nil
          uvars := 1
          type := list (.param 0) (.bvar 0) }] }] } }

example : missingFamilyParameter.specializedFamily 1 [.sort (.param 0)] = none := rfl
example : missingConstructorParameter.specializedFamily 1 [.sort (.param 0)] = none := rfl

private def tree : VExpr := .const `Tree []

private def collisionSource : VInductDecl where
  uvars := 0
  nparams := 0
  isUnsafe := false
  types := [{
    name := `Tree
    uvars := 0
    type := .sort (.succ .zero)
    numIndices := 0
    resultLevel := .succ .zero
    ctors := [] }]

private def collidingSpecialization : ContainerSpecialization where
  container := listSignature.declaration
  family := ⟨0, by decide⟩
  auxiliary := `Tree.rec
  levels := [.succ .zero]
  arguments := [tree]

private def collidingSignature : Lean4Lean.InductiveSignature where
  uvars := 0
  params := []
  families := #[
    { name := `Tree, indices := [], resultLevel := .succ .zero },
    { name := `Tree.rec, indices := [], resultLevel := .succ .zero }]
  constructors := #[
    { name := `Tree.rec.nil, owner := ⟨1, by decide⟩, fields := [], indices := [] },
    { name := `Tree.rec.cons, owner := ⟨1, by decide⟩,
      fields := [.external tree,
        .recursive (.const `Tree.rec [])
          { binders := [], target := ⟨1, by decide⟩, indices := [] }], indices := [] }]

private def collidingInstance : Instance collidingSignature where
  uvars := 0
  levels := []
  targetLevel := .zero
  recursorName := fun owner => collidingSignature.families[owner].name.str "rec"

/-- Unique table keys alone cannot prevent an auxiliary from intercepting a
generated source recursor. This table is scoped, but Tree.rec is ambiguous. -/
theorem collidingRestorationScoped :
    (compilationRestoration collisionSource [collidingSpecialization]).Scoped := by
  simp [Restoration.Scoped, compilationRestoration, collisionSource,
    collidingSpecialization, ContainerSpecialization.heads,
    ContainerSpecialization.constructorName, ContainerSpecialization.source,
    listSignature, InductiveSignature.declaration, HeadSpecialization.Scoped,
    tree, VExpr.ClosedN, VLevel.WF]
  decide

example : (compilationRestoration collisionSource [collidingSpecialization]).expr
    (.const `Tree.rec []) = some (list (.succ .zero) tree) := rfl

/-- The generated-name condition rejects the collision before restoration
can reinterpret the source recursor as the specialized container. -/
theorem collidingGenerationRejected (env : VEnv) (block : VInductBlock) :
    ¬ CompilationData env collisionSource collidingSignature.declaration
      collidingSignature collidingInstance [collidingSpecialization] block := by
  intro h
  have notNodup : ¬ ((collidingSignature.declaration.typeConstants ++
      collidingSignature.declaration.constructorConstants ++
      collidingInstance.recursors).map (·.name)).Nodup := by decide
  exact notNodup h.generatedNames

end Lean4Lean.Tests.InductiveCompilation
