import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas

/-! Translation relations between the executable's recursor values and the generated
recursors of a signature instance: `TrRecursorRule`, `RecursorMetadata`, `TrRecursorVal`,
`TrRecursorEntry` and `TrCompilation`.

`TrConstVal` relates only a name, universe arity and type; it says nothing about rules,
parameter counts or the K flag. `TrRecursorVal` records those facts explicitly against the
signature generator (section 3.2 of the design notes): it extends
`RecursorMetadata`, the facts available before the rules exist, with the rule coverage.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- The source constructor indices owned by this recursor, in generation order. -/
def ownedConstructors (s : InductiveSignature) (owner : Fin s.families.size) :
    List (Fin s.constructors.size) :=
  (List.finRange s.constructors.size).filter fun i => s.constructors[i].owner == owner

/-- The concrete rule's constructor, field count, and RHS all correspond to
the same generated equation. Typing its RHS alone is insufficient. -/
structure TrRecursorRule {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (lparams : List Name) (index : Fin s.constructors.size)
    (rule : Lean.RecursorRule) : Prop where
  ctor : rule.ctor = s.constructors[index].name
  nfields : rule.nfields = s.constructors[index].fields.length
  rhs : TrExprS venv lparams [] rule.rhs (g.equation index).rhs

/-- The metadata of one concrete recursor, against the signature instance that generated
it: the name, universe arity, translated type, cardinalities, major premise, mutual block,
safety, and K flag. Everything recursor reduction consults except the rule list.
`RecursorCheck.trMetadata` establishes it for each installed entry before any rule exists;
`TrRecursorVal` adds the rule coverage. `venv` is the abstract environment of the block in
which the type is translated; the executable installation may still be in progress. -/
structure RecursorMetadata {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size) (rec : Lean.RecursorVal) : Prop where
  name : rec.name = g.recursorName owner
  uvars : rec.levelParams.length = g.uvars
  type : TrExprS venv rec.levelParams [] rec.type (g.recursorType owner)
  numParams : rec.numParams = s.params.length
  numIndices : rec.numIndices = s.families[owner].indices.length
  numMotives : rec.numMotives = s.families.size
  numMinors : rec.numMinors = s.constructors.size
  major : rec.getMajorInduct = s.families[owner].name
  all : rec.all = s.families.toList.map (·.name)
  isUnsafe : rec.isUnsafe = s.isUnsafe
  k : rec.k = true →
    s.families.size = 1 ∧ s.constructors.size = 1 ∧
    s.families[owner].resultLevel ≈ .zero ∧
    ∀ ctor ∈ s.constructors.toList, ctor.fields = []

/-- All metadata consulted by recursor reduction is justified by the same signature as its
type and rules: the `RecursorMetadata` of the recursor together with its rule coverage.
`venv` is the abstract environment of the block in which the type and the rule right-hand
sides are translated; the executable installation may still be in progress. -/
structure TrRecursorVal {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size) (rec : Lean.RecursorVal) : Prop
    extends RecursorMetadata g venv owner rec where
  rules : List.Forall₂ (TrRecursorRule g venv rec.levelParams)
    (s.ownedConstructors owner) rec.rules

/-- An installed executable entry and its abstract constant are the executable and the
generated recursor of the same owner. A type translation alone would lose the executable
metadata. -/
def TrRecursorEntry {s : InductiveSignature} (g : Instance s)
    (venv : VEnv) (owner : Fin s.families.size)
    (entry : Lean.ConstantInfo × VConstVal) : Prop :=
  ∃ rec : Lean.RecursorVal, entry.1 = .recInfo rec ∧
    entry.2 = g.recursor owner ∧ TrRecursorVal g venv owner rec

/-- One signature and instance serve both the abstract compilation and the executable
entries, so the recursor types cannot be certified with one signature and the rule list or
metadata with another. `venv` is the abstract environment in which the right-hand sides
are translated. -/
structure TrCompilation (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) (venv : VEnv)
    (entries : List (Lean.ConstantInfo × VConstVal)) : Prop where
  generated : ∃ (s : InductiveSignature) (g : Instance s) (envTypes : VEnv),
    s.Models env decl ∧
    env.addConstVals decl.typeConstants = some envTypes ∧
    g.Admissible envTypes ∧
    (∃ envCtors es, envTypes.addConstVals decl.constructorConstants = some envCtors ∧
      decl.OwnCaseEliminators env es ∧
      g.GeneratedIHsWellTyped ((envCtors.addEliminators es).addProjections decl.projectionEntries) ∧
      s.FamilyTypesWF ((envCtors.addEliminators es).addProjections decl.projectionEntries)
        decl.uvars) ∧
    (∀ owner, g.recursorName owner = s.families[owner].name.str "rec") ∧
    block.recursors = g.recursors ∧ block.rules = g.equations ∧
    List.Forall₂ (TrRecursorEntry g venv)
      (List.finRange s.families.size) entries

theorem TrCompilation.compiles
    (H : TrCompilation env decl block venv entries) :
    Compiles env decl block := by
  rcases H.generated with ⟨s, g, envTypes, hm, ht, ha, hrec, hn, hr, he, _⟩
  exact ⟨s, g, envTypes, hm, ht, ha, hrec, hn, hr, he⟩

/-- The parameter count is fixed by the source declaration even when the
signature witness is existential. Choosing a different witness cannot repair
corrupted executable metadata. -/
theorem TrCompilation.parameterCount
    (H : TrCompilation env decl block venv entries)
    {rec : Lean.RecursorVal} {value : VConstVal}
    (hmem : (Lean.ConstantInfo.recInfo rec, value) ∈ entries) :
    rec.numParams = decl.nparams := by
  rcases H.generated with ⟨s, g, _, hm, _, _, _, _, _, _, hentries⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r hentries _ hmem with
    ⟨owner, _, concrete, he, _, hrec⟩
  cases he
  exact hrec.numParams.trans hm.nparams

end InductiveSignature
end Lean4Lean
