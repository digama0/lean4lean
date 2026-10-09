import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

/-! Translation of the restored recursors of a nested block (`TrRestoredRecursorVal`,
`TrRestoredCompilation`): each executable recursor entry translates the restoration of a
generated recursor of one finite compilation (section 3.3 of the design notes).

Restoration changes a recursor's name, type, constructor names, and rule RHSs.
It preserves the expanded block's parameter/index/motive/minor counts and its
K flag. In particular an auxiliary recursor's constructor may have more
parameters than the recursor itself. Its major family is the restored prior
container, whereas its `all` metadata lists the source families.

The structures below record the restored generated equations themselves and
explicit equalities for the specialized major and constructor applications;
the left-hand side shape is not inferred from right-hand side typing or metadata.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- Each restored constructor application uses exactly the specialization
parameters of the major family, lifted past motives, minors, and fields.
The concrete rule's RHS translates the exact restored generated equation. -/
structure TrRestoredRecursorRule {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (venv : VEnv) (lparams : List Name)
    (head : RestoredFamilyHead) (index : Fin s.constructors.size)
    (rule : Lean.RecursorRule) : Prop where
  ctor : rule.ctor = r.restoredHeadName s.constructors[index].name
  nfields : rule.nfields = s.constructors[index].fields.length
  constructorApplication :
    r.expr (g.constructorApp s.constructors[index]
      (s.families.size + s.constructors.size) 0) =
    some (VExpr.mkApps (.const rule.ctor head.levels)
      (head.arguments.map (fun arg => arg.liftN
        (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
        vars s.constructors[index].fields.length 0))
  equation : ∃ df, r.equation (g.equation index) = some df ∧
    df.lhs.stripLams.getAppFnArgs.1 =
      .const (r.recursorName (g.recursorName s.constructors[index].owner))
        (VLevel.params g.uvars) ∧
    TrExprS venv lparams [] rule.rhs df.rhs

/-- Metadata and type for one restored recursor. `sourceNames` is the
source family list, even for auxiliary recursors. The specialized family head
separately fixes the major inductive and constructor parameters. -/
structure TrRestoredRecursorVal {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (sourceNames : List Name) (venv : VEnv)
    (owner : Fin s.families.size) (rec : Lean.RecursorVal) : Prop where
  name : rec.name = r.recursorName (g.recursorName owner)
  uvars : rec.levelParams.length = g.uvars
  type : ∃ type, r.expr (g.recursorType owner) = some type ∧
    TrExprS venv rec.levelParams [] rec.type type
  numParams : rec.numParams = s.params.length
  numIndices : rec.numIndices = s.families[owner].indices.length
  numMotives : rec.numMotives = s.families.size
  numMinors : rec.numMinors = s.constructors.size
  all : rec.all = sourceNames
  isUnsafe : rec.isUnsafe = s.isUnsafe
  specialization : ∃ head,
    g.restoredFamilyHead r owner = some head ∧
    rec.getMajorInduct = head.name ∧
    (∀ level ∈ head.levels, level.WF g.uvars) ∧
    (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
    r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0)) ∧
    List.Forall₂ (TrRestoredRecursorRule g r venv rec.levelParams head)
      (s.ownedConstructors owner) rec.rules
  k : rec.k = true →
    s.families.size = 1 ∧ s.constructors.size = 1 ∧
    s.families[owner].resultLevel ≈ .zero ∧
    ∀ ctor ∈ s.constructors.toList, ctor.fields = []

/-- The concrete entry and its abstract constant have the same generated
owner, universe arity, restored type, and executable metadata. -/
def TrRestoredRecursorEntry {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (sourceNames : List Name) (venv : VEnv)
    (owner : Fin s.families.size) (entry : Lean.ConstantInfo × VConstVal) : Prop :=
  ∃ rec : Lean.RecursorVal, entry.1 = .recInfo rec ∧
    r.recursor (g.recursor owner) = some entry.2 ∧
    TrRestoredRecursorVal g r sourceNames venv owner rec

/-- One existential fixes the formation, the finite certificates of the prior
containers, all generated equations, their restoration, and every executable
recursor entry. There is no separately chosen rule batch or restoration callback. -/
structure TrRestoredCompilation (env : VEnv) (source : VInductDecl)
    (block : VInductBlock) (venv : VEnv)
    (entries : List (Lean.ConstantInfo × VConstVal)) : Prop where
  generated : ∃ (expanded : VInductDecl) (s : InductiveSignature) (g : Instance s)
      (auxiliaries : List ContainerSpecialization),
    CompilationData env source expanded s g auxiliaries block ∧
    ContainersInstalled env auxiliaries ∧
    List.Forall₂
      (TrRestoredRecursorEntry g (compilationRestoration source auxiliaries)
        (source.types.map (·.name)) venv)
      (List.finRange s.families.size) entries

theorem TrRestoredCompilation.compiles
    (H : TrRestoredCompilation env source block venv entries) :
    CompiledInductive env source block := by
  rcases H.generated with ⟨_, _, _, _, hdata, hprior, _⟩
  exact .intro hdata hprior

/-- `TrRestoredCompilation` does not read the block's case eliminators. -/
theorem TrRestoredCompilation.congr_eliminators
    (H : TrRestoredCompilation env source block venv entries)
    (es : List (Name × InductiveSignature.CaseSchema)) :
    TrRestoredCompilation env source { block with eliminators := es } venv entries := by
  rcases H.generated with ⟨expanded, s, g, auxiliaries, hdata, hprior, hentries⟩
  exact ⟨expanded, s, g, auxiliaries, hdata.congr_eliminators es, hprior, hentries⟩

/-- The source parameter count is fixed even if the restored constructor has
additional specialized parameters. Corrupting this concrete count cannot be
repaired by choosing another existential signature. -/
theorem TrRestoredCompilation.parameterCount
    (H : TrRestoredCompilation env source block venv entries)
    {rec : Lean.RecursorVal} {value : VConstVal}
    (hmem : (Lean.ConstantInfo.recInfo rec, value) ∈ entries) :
    rec.numParams = source.nparams := by
  rcases H.generated with ⟨expanded, s, g, auxiliaries, hdata, _, hentries⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r hentries _ hmem with
    ⟨owner, _, concrete, he, _, hrec⟩
  cases he
  exact hrec.numParams.trans (hdata.model.nparams.trans hdata.nparams)

theorem TrRestoredCompilation.all
    (H : TrRestoredCompilation env source block venv entries)
    {rec : Lean.RecursorVal} {value : VConstVal}
    (hmem : (Lean.ConstantInfo.recInfo rec, value) ∈ entries) :
    rec.all = source.types.map (·.name) := by
  rcases H.generated with ⟨_, _, _, _, _, _, hentries⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r hentries _ hmem with
    ⟨owner, _, concrete, he, _, hrec⟩
  cases he
  exact hrec.all

end InductiveSignature
end Lean4Lean
