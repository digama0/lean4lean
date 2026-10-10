import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.CanonicalEq

/-! # The generated iota rule of canonical equality

A normalized signature with one family, one constructor and two parameters
whose generated recursor has the stored type of `Eq.rec` (`canonicalEqRecType`)
generates exactly the stored iota rule `canonicalEqRecRule`.  The generator
(`Instance.recursorType`, `Instance.equation`) builds the rule's binder domains
from the same parameter, motive and minor terms as the recursor type, and the
minor premise of the recursor type fixes the constructor's name, universe
arguments and index. -/

namespace Lean4Lean
namespace InductiveSignature

private theorem liftN_one_eq_bvar_one {e : VExpr} (h : e.liftN 1 0 = .bvar 1) :
    e = .bvar 0 := by
  cases e <;> simp_all [VExpr.liftN, liftVar]

private theorem mkApps_append (f : VExpr) (l₁ l₂ : List VExpr) :
    VExpr.mkApps f (l₁ ++ l₂) = VExpr.mkApps (VExpr.mkApps f l₁) l₂ := by
  simp [VExpr.mkApps, List.foldl_append]

private theorem mkApps_app_app_ne {f a b x : VExpr} {i : Nat} :
    ∀ l : List VExpr, VExpr.mkApps (.app (.app f a) b) l ≠ .app (.bvar i) x
  | [], h => by cases h
  | c :: l, h => mkApps_app_app_ne (f := .app f a) (a := b) (b := c) l h

/-- The generator's equations for a one-family, one-constructor signature with
two parameters, whose recursor `Eq.rec` has two universe parameters and the
stored type of `Eq.rec`, are exactly the stored iota rule. -/
theorem Instance.eqRecEquations {s : InductiveSignature} (g : Instance s)
    (hfamilies : s.families.size = 1) (hconstructors : s.constructors.size = 1)
    (hparams : s.params.length = 2) (huvars : g.uvars = 2)
    (hname : g.recursorName ⟨0, by omega⟩ = ``Eq.rec)
    (htype : g.recursorType ⟨0, by omega⟩ = canonicalEqRecType) :
    g.equations = [canonicalEqRecRule] := by
  rcases s with ⟨uvars, params, ⟨families⟩, ⟨constructors⟩, isUnsafe⟩
  rcases g with ⟨guvars, levels, targetLevel, recursorName⟩
  simp only [List.size_toArray] at hfamilies hconstructors
  subst huvars
  match families, constructors, params, hfamilies, hconstructors, hparams with
  | [f], [c], [p₀, p₁], _, _, _ =>
  simp only [Instance.recursorType, Instance.params, Instance.motives, Instance.minors,
    Instance.familyApp, InductiveSignature.familyApp] at htype
  simp [insertBinders, vars, VExpr.wrapForalls, canonicalEqRecType, List.zipIdx] at htype
  obtain ⟨hp₀, hp₁, hM, hN, -⟩ := htype
  have hminor := hN
  rcases c with ⟨cname, cowner, cfields, cindices⟩
  cases cfields with
  | cons field fields =>
    simp [Instance.minor, insertBinders, VExpr.wrapForalls, canonicalEqRecMinor,
      InductiveSignature.fieldTypes, List.zipIdx_cons] at hN
  | nil =>
  simp [Instance.minor, insertBinders, VExpr.wrapForalls, canonicalEqRecMinor,
    recursiveFields, Instance.constructorApp, vars, InductiveSignature.fieldTypes] at hN
  rcases cindices with _ | ⟨j, _ | ⟨j', rest⟩⟩
  · simp [VExpr.mkApps, List.range, List.range.loop] at hN
  rotate_left
  · rw [List.map_cons, List.map_cons, List.cons_append, List.cons_append,
      ← List.cons_append, ← List.cons_append, mkApps_append] at hN
    simp only [VExpr.mkApps, List.foldl, VExpr.app.injEq] at hN
    exact absurd hN.1 (mkApps_app_app_ne _)
  simp [VExpr.mkApps, List.range, List.range.loop] at hN
  obtain ⟨hj, rfl, rfl⟩ := hN
  have hj := liftN_one_eq_bvar_one hj
  have hcowner : cowner = ⟨0, by simp⟩ :=
    Fin.ext (Nat.lt_one_iff.mp (cowner.isLt : (cowner : Nat) < 1))
  subst hcowner
  have hname' : recursorName 0 = ``Eq.rec := hname
  simp [Instance.equations, Instance.equation, List.finRange, Instance.constructorApp,
    Instance.recursorHead, insertBinders, vars, VExpr.wrapLams, VExpr.wrapForalls,
    Instance.params, Instance.motives, Instance.minors, List.zipIdx, recursiveFields,
    InductiveSignature.fieldTypes, hp₀, hp₁, hM, hj, hname', canonicalEqRecRule,
    VExpr.mkApps, List.range, List.range.loop, VLevel.params, VExpr.liftN, liftVar]
  exact hminor

/-- An ordinary compilation of a one-family, one-constructor declaration with
two parameters, named `Eq`, generates exactly the stored iota rule as soon as
its generated recursor `Eq.rec` has the stored universe arity and type. -/
theorem Compiles.eqRecRules {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : Compiles env decl block) {family : VInductiveType}
    (htypes : decl.types = [family]) (hname : family.name = ``Eq)
    (hctors : family.ctors.length = 1) (hnparams : decl.nparams = 2)
    (hrec : ∀ recursor ∈ block.recursors, recursor.name = ``Eq.rec →
      recursor.uvars = 2 ∧ recursor.type = canonicalEqRecType) :
    block.rules = [canonicalEqRecRule] := by
  rcases H.generated with
    ⟨s, g, _envTypes, Hmodel, _hadded, _Hadmissible, _Hrec, hrecNames, hrecs, hrules⟩
  rw [hrules]
  have hfamily := Hmodel.families
  have hparams : s.params.length = 2 := Hmodel.nparams.trans hnparams
  rw [htypes] at hfamily
  rcases s with ⟨uvars, params, ⟨families⟩, ⟨constructors⟩, isUnsafe⟩
  have hfamiliesLen := Lean4Lean.List.Forall₂.length_eq hfamily
  simp only [InductiveSignature.declaration, List.length_map, List.length_zipIdx,
    List.length_singleton] at hfamiliesLen
  match families, constructors, hfamiliesLen, hfamily, g, hrecNames, hrecs with
  | [f], constructors, _, hfamily, g, hrecNames, hrecs =>
  simp [InductiveSignature.declaration, List.zipIdx] at hfamily
  obtain ⟨hfamName, _, _, _, hctorNames⟩ := hfamily
  have hctorLen := congrArg List.length hctorNames
  have hnameRec : g.recursorName ⟨0, by simp⟩ = ``Eq.rec := by
    rw [hrecNames]
    simp [hfamName, hname]
  have hmem : g.recursor ⟨0, by simp⟩ ∈ block.recursors := by
    rw [hrecs]
    simp [Instance.recursors, List.finRange]
  obtain ⟨huvars, htype⟩ := hrec _ hmem hnameRec
  exact g.eqRecEquations rfl (by simpa [hctors] using hctorLen) hparams huvars hnameRec htype

end InductiveSignature
end Lean4Lean
