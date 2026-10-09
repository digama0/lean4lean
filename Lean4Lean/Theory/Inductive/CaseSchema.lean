import Lean4Lean.Theory.Inductive.Restoration

/-! Per-family abstract case eliminators, generated from normalized declaration
syntax (section 2.3 of the design notes). The full signature and restoration table
are retained so certification can identify this data with a compilation of the declaration.

Case analysis has one motive and the selected family's constructors. Recursive
fields retain their domains but introduce no induction hypotheses.
The existing signature generator supplies every telescope and equation; this
module accepts no eliminator types or equation bodies as input.
-/

namespace Lean4Lean.InductiveSignature

structure CaseSchema where
  /-- Source families owned by this block, excluding auxiliary families.
  Certification identifies this list with the checked source declaration. -/
  sourceFamilies : List Name
  signature : InductiveSignature
  restoration : Restoration

namespace CaseSchema

/-- Preserve a constructor's raw field domains when selecting case analysis.
Recursive classification belongs to the certified signature; treating
these fields as case arguments does not assert a new formation derivation. -/
def caseConstructor (schema : CaseSchema)
    (ctor : Constructor schema.signature.families.size) : Constructor 1 where
  name := ctor.name
  owner := ⟨0, by decide⟩
  fields := (schema.signature.fieldTypes ctor).map Field.external
  indices := ctor.indices

/-- A one-family view in the signature's constructor order. This is generator
input only, not a separately claimed well-formed inductive declaration. -/
def view (schema : CaseSchema) (owner : Fin schema.signature.families.size) :
    InductiveSignature where
  uvars := schema.signature.uvars
  params := schema.signature.params
  families := #[schema.signature.families[owner]]
  constructors := (schema.signature.constructors.toList.filterMap fun ctor =>
    if ctor.owner == owner then some (schema.caseConstructor ctor) else none).toArray
  isUnsafe := schema.signature.isUnsafe

@[simp] theorem view_familyCount (schema : CaseSchema)
    (owner : Fin schema.signature.families.size) : (schema.view owner).families.size = 1 := rfl

/-- The instance's recursor name is irrelevant to the case type and is replaced by the
abstract head `.elim` in every generated case equation. -/
def specialize (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (uvars : Nat) (levels : List VLevel) (target : VLevel) : Instance (schema.view owner) where
  uvars := uvars
  levels := levels
  targetLevel := target
  recursorName := fun _ => schema.signature.families[owner].name.str "rec"

/-- The unique motive in a per-family case view. -/
def viewOwner (schema : CaseSchema) (owner : Fin schema.signature.families.size) :
    Fin (schema.view owner).families.size := ⟨0, by simp⟩

/-- Restore the generated case type, including dependent indices and every
constructor field domain. Restoration failure is retained explicitly. -/
def type (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (uvars : Nat) (levels : List VLevel) (target : VLevel) : Option VExpr :=
  schema.restoration.expr <|
    (schema.specialize owner uvars levels target).recursorType (schema.viewOwner owner)

/-- Abstract equation heads retain the owner slot of the full signature, including slots
for auxiliary families. Both sides and the type undergo the same restoration. -/
def equations (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size)
    (uvars : Nat) (levels : List VLevel) (target : VLevel) : Option (List VDefEq) :=
  ((schema.specialize owner uvars levels target).equations (.elim block owner.val)).mapM
    schema.restoration.equation

/-- Generic schemas reserve universe parameter zero for the elimination
universe. The remaining parameters are exactly the source universes. -/
def genericUvars (schema : CaseSchema) : Nat := schema.signature.uvars + 1

def genericLevels (schema : CaseSchema) : List VLevel :=
  (List.range schema.signature.uvars).map fun i => .param (i + 1)

def genericType (schema : CaseSchema)
    (owner : Fin schema.signature.families.size) : Option VExpr :=
  schema.type owner schema.genericUvars schema.genericLevels (.param 0)

def genericEquations (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) : Option (List VDefEq) :=
  schema.equations block owner schema.genericUvars schema.genericLevels (.param 0)

/-- The source sort is specialized at the occurrence, independently of the
recursor's permitted elimination universe. -/
def sourceLevel (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (levels : List VLevel) : VLevel :=
  schema.signature.families[owner].resultLevel.inst levels

/-- The permission needed by projection case analysis: either the specialized
source is always a type, or elimination remains in Prop. Singleton elimination
is a separate principle and is not assumed by this predicate. -/
def ProjectionAdmissible (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (levels : List VLevel) (target : VLevel) : Prop :=
  (schema.sourceLevel owner levels).IsNeverZero ∨ target ≈ .zero

/-- Scoped universe specialization for an abstract case occurrence. -/
structure Permission (schema : CaseSchema) (U : Nat)
    (owner : Fin schema.signature.families.size) (levels : List VLevel) (target : VLevel) : Prop where
  length : levels.length = schema.signature.uvars
  levels_wf : ∀ level ∈ levels, level.WF U
  target_wf : target.WF U
  admissible : schema.ProjectionAdmissible owner levels target

theorem Permission.instL {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (H : schema.Permission U owner levels target)
    (hsub : ∀ level ∈ substitution, level.WF U') :
    schema.Permission U' owner (levels.map (·.inst substitution)) (target.inst substitution) where
  length := by simpa using H.length
  levels_wf := by
    intro level hlevel
    rcases List.mem_map.mp hlevel with ⟨source, _, rfl⟩
    exact VLevel.WF.inst hsub
  target_wf := VLevel.WF.inst hsub
  admissible := by
    rcases H.admissible with h | h
    · exact Or.inl (by simpa [sourceLevel, ← VLevel.inst_inst] using h.inst (ls := substitution))
    · exact Or.inr (VLevel.inst_congr_l h)

/-- Generic rule templates have no free term variables. This syntactic
premise makes their use stable under local-context substitution. -/
def RuleClosed (rule : VDefEq) : Prop :=
  rule.lhs.Closed ∧ rule.rhs.Closed ∧ rule.type.Closed

end CaseSchema
end Lean4Lean.InductiveSignature
