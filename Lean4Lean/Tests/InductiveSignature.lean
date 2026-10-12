import Lean4Lean.Theory.Inductive.Signature

namespace Lean4Lean.Tests.InductiveSignature
open Lean4Lean.InductiveSignature

private def nat : VExpr := .const `SigNat []
private def zero : VExpr := .const `SigNat.zero []
private def succ (n : VExpr) : VExpr := .app (.const `SigNat.succ []) n

def natSignature : Lean4Lean.InductiveSignature where
  uvars := 0
  params := []
  families := #[{ name := `SigNat, indices := [], resultLevel := .succ .zero }]
  constructors := #[
    { name := `SigNat.zero, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `SigNat.succ, owner := ⟨0, by decide⟩,
      fields := [.recursive nat { binders := [], target := ⟨0, by decide⟩, indices := [] }],
      indices := [] }]

def natInstance : Instance natSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `SigNat.rec

example : natInstance.motives = [.forallE nat (.sort (.param 0))] := rfl

/-- The zero minor and the induction hypothesis of the successor minor have
exactly their prescribed types and binder references. -/
example : natInstance.minors = [
    .app (.bvar 0) zero,
    .forallE nat (.forallE (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (succ (.bvar 1))))] := rfl

example : natInstance.recursorType ⟨0, by decide⟩ =
    VExpr.wrapForalls (natInstance.motives ++ natInstance.minors ++ [nat])
      (.app (.bvar 3) (.bvar 0)) := rfl

example : (natInstance.equation ⟨0, by decide⟩).rhs.stripLams = .bvar 1 := rfl

/-- Succ selects the succ minor and recurses on its predecessor, using all
of the same parameters, motives, and minors. -/
example : (natInstance.equation ⟨1, by decide⟩).rhs.stripLams =
    VExpr.mkApps (.bvar 1) [.bvar 0,
      VExpr.mkApps (.const `SigNat.rec [.param 0]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]] := rfl

example : natInstance.equations.length = 2 := rfl

/-- Changing the chosen minor is a different equation, not another valid
choice of output from the same signature. -/
example : (natInstance.equation ⟨0, by decide⟩).rhs.stripLams ≠ .bvar 0 := by
  change VExpr.bvar 1 ≠ .bvar 0
  intro h
  cases h

def higherOrderSignature : Lean4Lean.InductiveSignature :=
  { natSignature with constructors := #[
    { name := `SigNat.zero, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `SigNat.branch, owner := ⟨0, by decide⟩,
      fields := [.recursive (.forallE (.const ``Nat []) nat)
        { binders := [.const ``Nat []], target := ⟨0, by decide⟩, indices := [] }],
      indices := [] }] }

def higherOrderInstance : Instance higherOrderSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `SigNat.rec

example : (higherOrderInstance.equation ⟨1, by decide⟩).rhs.stripLams =
    VExpr.mkApps (.bvar 1) [.bvar 0,
      .lam (.const ``Nat []) (VExpr.mkApps (.const `SigNat.rec [.param 0])
        [.bvar 4, .bvar 3, .bvar 2, .app (.bvar 1) (.bvar 0)])] := rfl

def twoFieldsSignature : Lean4Lean.InductiveSignature :=
  { natSignature with constructors := #[
    { name := `SigNat.zero, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `SigNat.fork, owner := ⟨0, by decide⟩,
      fields := [
        .recursive nat { binders := [], target := ⟨0, by decide⟩, indices := [] },
        .recursive nat { binders := [], target := ⟨0, by decide⟩, indices := [] }],
      indices := [] }] }

def twoFieldsInstance : Instance twoFieldsSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `SigNat.rec

/-- Hypotheses follow all fields. The second hypothesis also accounts for
the first hypothesis's binder, without changing which field it describes. -/
example : twoFieldsInstance.minors = [
    .app (.bvar 0) zero,
    VExpr.wrapForalls [nat, nat, .app (.bvar 3) (.bvar 1), .app (.bvar 4) (.bvar 1)]
      (.app (.bvar 5) (VExpr.mkApps (.const `SigNat.fork []) [.bvar 3, .bvar 2]))] := rfl

def aliasSignature : Lean4Lean.InductiveSignature :=
  { natSignature with constructors := #[
    { name := `SigNat.zero, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `SigNat.succ, owner := ⟨0, by decide⟩,
      fields := [.recursive (.const `AliasNat [])
        { binders := [], target := ⟨0, by decide⟩, indices := [] }], indices := [] }] }

def aliasInstance : Instance aliasSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `SigNat.rec

/-- Classification can unfold AliasNat, while the generated minor retains
the declared field domain. Establishing Models must justify that unfolding. -/
example : aliasInstance.minors = [
    .app (.bvar 0) zero,
    .forallE (.const `AliasNat []) (.forallE (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (succ (.bvar 1))))] := rfl

/-- A dependent nonrecursive field must retain the preceding field variable
while parameter references move past the motive binder. -/
def dependentSignature : Lean4Lean.InductiveSignature where
  uvars := 0
  params := [.sort (.succ .zero), .forallE (.bvar 0) (.sort (.succ .zero))]
  families := #[{ name := `SigSigma, indices := [], resultLevel := .succ .zero }]
  constructors := #[{
    name := `SigSigma.mk, owner := ⟨0, by decide⟩,
    fields := [.external (.bvar 1), .external (.app (.bvar 1) (.bvar 0))], indices := [] }]

def dependentInstance : Instance dependentSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `SigSigma.rec

example : dependentInstance.minors = [
    .forallE (.bvar 2) (.forallE (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 2) (VExpr.mkApps (.const `SigSigma.mk [])
        [.bvar 4, .bvar 3, .bvar 1, .bvar 0])))] := rfl

def mutualSignature : Lean4Lean.InductiveSignature where
  uvars := 0
  params := []
  families := #[
    { name := `SigA, indices := [], resultLevel := .succ .zero },
    { name := `SigB, indices := [], resultLevel := .succ .zero }]
  constructors := #[
    { name := `SigA.fromB, owner := ⟨0, by decide⟩,
      fields := [.recursive (.const `SigB [])
        { binders := [], target := ⟨1, by decide⟩, indices := [] }], indices := [] },
    { name := `SigB.base, owner := ⟨1, by decide⟩, fields := [], indices := [] }]

def mutualInstance : Instance mutualSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun i => if i.val = 0 then `SigA.rec else `SigB.rec

example : (mutualInstance.equation ⟨0, by decide⟩).rhs.stripLams =
    VExpr.mkApps (.bvar 2) [.bvar 0,
      VExpr.mkApps (.const `SigB.rec [.param 0])
        [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]] := rfl

private def vector (a n : VExpr) : VExpr := VExpr.mkApps (.const `SigVec []) [a, n]

def indexedSignature : Lean4Lean.InductiveSignature where
  uvars := 0
  params := [.sort (.succ .zero)]
  families := #[{ name := `SigVec, indices := [.const ``Nat []], resultLevel := .succ .zero }]
  constructors := #[
    { name := `SigVec.nil, owner := ⟨0, by decide⟩, fields := [], indices := [.const ``Nat.zero []] },
    { name := `SigVec.cons, owner := ⟨0, by decide⟩,
      fields := [.external (.const ``Nat []), .external (.bvar 1),
        .recursive (vector (.bvar 2) (.bvar 1))
          { binders := [], target := ⟨0, by decide⟩, indices := [.bvar 1] }],
      indices := [.app (.const ``Nat.succ []) (.bvar 2)] }]

def indexedInstance : Instance indexedSignature where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => `SigVec.rec

example : (indexedInstance.equation ⟨1, by decide⟩).lhs.stripLams =
    VExpr.mkApps (.const `SigVec.rec [.param 0])
      [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .app (.const ``Nat.succ []) (.bvar 2),
        VExpr.mkApps (.const `SigVec.cons []) [.bvar 6, .bvar 2, .bvar 1, .bvar 0]] := rfl

example : (indexedInstance.equation ⟨1, by decide⟩).rhs.stripLams =
    VExpr.mkApps (.bvar 3) [.bvar 2, .bvar 1, .bvar 0,
      VExpr.mkApps (.const `SigVec.rec [.param 0])
        [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]] := rfl

/-- Two constructors rule out singleton elimination independently of any
unproved typing inversion lemma. -/
def sortSignature : Lean4Lean.InductiveSignature :=
  { natSignature with
    uvars := 1
    families := #[{ name := `SigNat, indices := [], resultLevel := .param 0 }] }

def specializedInstance : Instance sortSignature where
  uvars := 0
  levels := [.succ .zero]
  targetLevel := .succ .zero
  recursorName := fun _ => `SigNat.rec

example : specializedInstance.Admissible env := by
  refine ⟨rfl, ?_, trivial, .inl ?_⟩
  · simp [specializedInstance, VLevel.WF]
  · simp [sortSignature, VLevel.inst, VLevel.IsNeverZero, VLevel.eval, specializedInstance]

def unspecializedInstance : Instance sortSignature where
  uvars := 1
  levels := [.param 0]
  targetLevel := .succ .zero
  recursorName := fun _ => `SigNat.rec

example : ¬ unspecializedInstance.Admissible env := by
  intro h
  rcases h.elimination with hn | hz | hs
  · have hn := hn { name := `SigNat, indices := [], resultLevel := .param 0 } (by simp [sortSignature]) []
    simp [unspecializedInstance, VLevel.inst, VLevel.eval] at hn
  · have hz := congrFun hz []
    simp [unspecializedInstance, VLevel.eval] at hz
  · have hsize := hs.1.2.1
    change 2 ≤ 1 at hsize
    omega

end Lean4Lean.Tests.InductiveSignature
