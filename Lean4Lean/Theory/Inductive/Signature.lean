import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Typing.Lemmas

/-! Typed models and elimination admissibility for the pure signature generator (section 2.2
of the design notes): `Models` relates a signature to a source declaration,
`Instance.Admissible` fixes the elimination universe, and `Compiles` is ordinary compilation. -/

namespace Lean4Lean
namespace InductiveSignature

/-- Exact family/constructor names and constructor types modulo typed
definitional equality.  The source constructor types are compared in the
environment containing the source family headers, before any recursor or
equation is installed.  The family types are not compared: a family's
signature telescope is required only to be well formed and to type the family
applications at the recorded sort (`FamilyTypesWF`, a clause of `Compiles`),
because the recursor phase computes the index telescope in a context in which
definitional agreement with the declared one is not derivable. -/
structure Models (s : InductiveSignature) (env : VEnv) (decl : VInductDecl) : Prop where
  uvars : s.uvars = decl.uvars
  nparams : s.params.length = decl.nparams
  safety : s.isUnsafe = decl.isUnsafe
  families : List.Forall₂ (fun normalized source =>
    normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
    normalized.numIndices = source.numIndices ∧
    normalized.resultLevel ≈ source.resultLevel ∧
    normalized.ctors.map VConstVal.name = source.ctors.map VConstVal.name)
    s.declaration.types decl.types
  constructors : ∃ envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    List.Forall₂ (fun normalized source =>
      normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
      envTypes.IsDefEqU decl.uvars [] normalized.type source.type)
      s.declaration.constructorConstants decl.constructorConstants
  /-- Every field type is, in its own scope (the parameters and the earlier
  fields), definitionally a strictly positive normal form at the source
  universes, in the branch its classification names
  (`VInductDecl.ClassifiedFieldNormalForm`): an `external` field is
  definitionally a type free of the families being defined, a `recursive` field
  is definitionally a telescope over family-free domains ending in a family
  applied to the parameters and family-free indices.  So the generator gives an
  induction hypothesis exactly to the fields whose positive normal form ends in a
  family: a recursive field cannot be declared `external`, and a family-free field
  cannot be declared `recursive`.  The recorded shape of a recursive field (its
  binders, target family and indices) is constrained by the typing of its generated
  induction hypothesis (`Instance.GeneratedIHsWellTyped`): together with this clause, it
  has the target family and the number of binders of the normal form, and binders and
  indices definitionally equal to the normal form's, compared under the hypothesis binders
  (`Instance.recursiveShape_correspondence`).  Unsafe declarations, which are not checked
  for positivity, are exempt. -/
  classifiedFields : s.isUnsafe = true ∨ ∃ envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
      ∃ normalized,
        envTypes.IsDefEqU decl.uvars (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
          (s.fieldType i ctor.fields[i]) normalized ∧
        decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) i ctor.fields[i].isRecursive
          normalized
  /-- The checked constructor result has the owning family's exact index
  count. Normalization retains this finite syntactic fact independently of
  the typed correspondence between the selected and source telescopes. -/
  constructorArity : ∀ ctor ∈ s.constructors.toList,
    ctor.indices.length = s.families[ctor.owner].indices.length

/-- Every field type is, in its own scope, definitionally a strictly positive normal form
(`VInductDecl.UniformFieldNormalForm`), forgetting which branch. -/
theorem Models.positiveFields {s : InductiveSignature} {env : VEnv} {decl : VInductDecl}
    (H : s.Models env decl) :
    s.isUnsafe = true ∨ ∃ envTypes,
      env.addConstVals decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
        ∃ normalized,
          envTypes.IsDefEqU decl.uvars (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
            (s.fieldType i ctor.fields[i]) normalized ∧
          decl.UniformFieldNormalForm (VLevel.params decl.uvars) i normalized := by
  rcases H.classifiedFields with hunsafe | ⟨envTypes, htypes, hfields⟩
  · exact .inl hunsafe
  · refine .inr ⟨envTypes, htypes, fun ctor hctor i hi => ?_⟩
    obtain ⟨normalized, hdefeq, hshape⟩ := hfields ctor hctor i hi
    exact ⟨normalized, hdefeq, hshape.uniform⟩

/-- Singleton elimination is certified from the constructor fields. A field
is either a proof or is determined by an index of the constructor's result.
The test is made after universe specialization. -/
def SingletonElimination (s : InductiveSignature) (envTypes : VEnv)
    (uvars : Nat) (levels : List VLevel) : Prop :=
  s.families.size = 1 ∧ s.constructors.size ≤ 1 ∧
  ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
    envTypes.HasType uvars
      ((((s.fieldTypes ctor).take i).map (·.instL levels)).reverse ++
        (s.params.map (·.instL levels)).reverse)
      ((s.fieldType i ctor.fields[i]).instL levels) (.sort .zero) ∨
    VExpr.bvar (ctor.fields.length - 1 - i) ∈ ctor.indices

/-- The elimination universe is a universe parameter on which the source
universes do not depend, so the recursor can be specialized to any motive
universe, in particular to `Prop`, without changing the family. This is the
shape of Lean's recursors (`getElimLevel` returns a fresh parameter). -/
def Instance.FreeTarget {s : InductiveSignature} (g : Instance s) : Prop :=
  ∃ k, g.targetLevel = .param k ∧
    ∀ l ∈ g.levels, ∀ (ls : List VLevel) (u : VLevel), l.inst (ls.set k u) = l.inst ls

/-- Admissibility is checked at the instance's source universes. In particular,
a Sort-polymorphic family can acquire large elimination after specialization
without changing its recursor's type.

Singleton (large) elimination additionally requires a free elimination universe
(`Instance.FreeTarget`). Without it, `VEnv.WF` would admit a large-eliminating inductive
proposition whose only recursor has motive universe `succ u`; its proof fields could then
not be extracted (there is no elimination into `Prop`), so its iota rule would have no
reconstruction step and `FullEquationCoverage` would fail. Lean never produces such
recursors, and the executable's recursor construction satisfies the free shape (section 2.4
of the design notes). -/
structure Instance.Admissible {s : InductiveSignature} (g : Instance s)
    (envTypes : VEnv) : Prop where
  levels_length : g.levels.length = s.uvars
  levels_wf : ∀ level ∈ g.levels, level.WF g.uvars
  target_wf : g.targetLevel.WF g.uvars
  elimination :
    (∀ family ∈ s.families.toList, (family.resultLevel.inst g.levels).IsNeverZero) ∨
    g.targetLevel ≈ .zero ∨
    (s.SingletonElimination envTypes g.uvars g.levels ∧ g.FreeTarget)

/-- Each generated induction hypothesis is a well-formed type in the context in
which the generated minor premise binds it: parameters, motives, earlier
minors, the constructor's fields and the earlier hypotheses.  This is the
typing fact the generated recursor needs from the recursive shapes.  Which
fields get a hypothesis is fixed by `Models.classifiedFields`.  It is
stated in the recursor-checking environment, that is after the family headers, the
constructors and the declaration's projection entries,
since that is where the executable checks the generated types.  A
definitional-equality form in a smaller context is not derivable from the
checker's runs without context strengthening of definitional equality, which is false
in general (section 5.1 of the design notes). -/
def Instance.GeneratedIHsWellTyped {s : InductiveSignature} (g : Instance s) (env : VEnv) : Prop :=
  ∀ (index : Fin s.constructors.size) (j : Nat)
    (hj : j < (recursiveFields s.constructors[index]).length),
    env.IsType g.uvars (g.hypothesisContext s.constructors[index] index.val j)
      (g.hypothesis s.constructors[index] index.val j
        (recursiveFields s.constructors[index])[j].1
        (recursiveFields s.constructors[index])[j].2)

/-- Well-formed family applications: the signature's parameter and index
telescope is a well-formed context, and each family applied to its parameters
and indices has the recorded result sort, in the recursor-checking
environment.  Definitional agreement of each index domain with the
declared family type in its own prefix is not derivable from the checker's
runs (context strengthening of definitional equality), so this clause
records what the generated motive types need. -/
def FamilyTypesWF (s : InductiveSignature) (env : VEnv) (uvars : Nat) : Prop :=
  ∀ owner : Fin s.families.size,
    OnCtx (s.families[owner].indices.reverse ++ s.params.reverse) (env.IsType uvars) ∧
    env.HasType uvars (s.families[owner].indices.reverse ++ s.params.reverse)
      (s.familyApp owner (VLevel.params uvars) (vars s.params.length s.families[owner].indices.length)
        (vars s.families[owner].indices.length 0))
      (.sort s.families[owner].resultLevel)

/-- Ordinary compilation: generation fixes every motive, minor, recursive call,
and both sides of every equation. This certificate does not accept an
arbitrary list of equations on the strength of their typing. -/
structure Compiles (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop where
  generated : ∃ (s : InductiveSignature) (g : Instance s) (envTypes : VEnv),
    s.Models env decl ∧
    env.addConstVals decl.typeConstants = some envTypes ∧
    g.Admissible envTypes ∧
    (∃ envCtors, envTypes.addConstVals decl.constructorConstants = some envCtors ∧
      g.GeneratedIHsWellTyped (envCtors.addProjections decl.projectionEntries) ∧
      s.FamilyTypesWF (envCtors.addProjections decl.projectionEntries) decl.uvars) ∧
    (∀ owner, g.recursorName owner = s.families[owner].name.str "rec") ∧
    block.recursors = g.recursors ∧ block.rules = g.equations

end InductiveSignature
end Lean4Lean
