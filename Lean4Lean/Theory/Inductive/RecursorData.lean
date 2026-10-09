import Lean4Lean.Theory.Inductive.SingletonReconstruction
import Lean4Lean.Theory.Inductive.CaseReductionData

/-! Pure metadata of a recursor occurrence (`RecursorData`), used by singleton reconstruction and
prefix unfolding. Every field is generated from one compilation instance and its case schema; no typing relation, matching
oracle, or arbitrary replacement term is part of the data. -/

namespace Lean4Lean.InductiveSignature

structure RecursorData where
  block : Name
  schema : CaseSchema
  owner : Fin schema.signature.families.size
  uvars : Nat
  levels : List VLevel
  target : VLevel

namespace RecursorData

def ofInstance (block : Name) (schema : CaseSchema) (g : Instance schema.signature)
    (owner : Fin schema.signature.families.size) : RecursorData :=
  ⟨block, schema, owner, g.uvars, g.levels, g.targetLevel⟩

def name (data : RecursorData) : Name :=
  data.schema.restoration.recursorName (data.schema.signature.families[data.owner].name.str "rec")

def numParams (data : RecursorData) : Nat := data.schema.signature.params.length

def indexOffset (data : RecursorData) : Nat :=
  data.numParams + data.schema.signature.families.size + data.schema.signature.constructors.size

def numIndices (data : RecursorData) : Nat :=
  data.schema.signature.families[data.owner].indices.length

def majorOffset (data : RecursorData) : Nat := data.indexOffset + data.numIndices

/-- The instance's source universe substitution, including
parameter-specialized auxiliary recursors. -/
def sourceLevels (data : RecursorData) (packed : List VLevel) : List VLevel :=
  data.levels.map (·.inst packed)

/-- Rebuild the constructor at one exactly saturated recursor occurrence.
Offsets belong to the full mutual recursor, while field projections
use the selected one-family case schema. Extra application arguments remain
outside this head computation. -/
def reconstruct (data : RecursorData) (U : Nat) (packed fieldSorts : List VLevel)
    (arguments : List VExpr) : Option VExpr := do
  if packed.length != data.uvars || arguments.length != data.majorOffset + 1 then none else
  let major ← arguments[data.majorOffset]?
  data.schema.singletonReconstructAt data.block data.owner U (data.sourceLevels packed) fieldSorts
    (arguments.take data.numParams)
    ((arguments.drop data.indexOffset).take data.numIndices) major

/-- Singleton reconstruction uses index selectors wherever possible and
Prop selectors for every remaining field. Singleton elimination of the compilation
must justify those remaining proof fields. The sort
annotations do not choose any reconstructed value. -/
def reconstructWithPropFields (data : RecursorData) (U : Nat) (packed : List VLevel)
    (arguments : List VExpr) : Option VExpr := do
  let source ← data.schema.structureTelescope data.owner (data.sourceLevels packed)
  data.reconstruct U packed (List.replicate source.fields.length .zero) arguments

/-- The instance of the compilation, rebuilt from the data. -/
def recursorInstance (data : RecursorData) : Instance data.schema.signature := {
  uvars := data.uvars
  levels := data.levels
  targetLevel := data.target
  recursorName := fun owner => data.schema.signature.families[owner].name.str "rec" }

/-- The unique singleton iota equation of the recursor, after exact restoration. -/
def singletonEquation (data : RecursorData) : Option VDefEq := do
  let s := data.schema.signature
  let [ctorIndex] := (List.finRange s.constructors.size).filter
    (fun i => s.constructors[i].owner == data.owner) | none
  data.schema.restoration.equation (data.recursorInstance.equation ctorIndex)

/-- The exact restored recursor type; constrained indices are retained. -/
def recursorType (data : RecursorData) : Option VExpr :=
  data.schema.restoration.expr (data.recursorInstance.recursorType data.owner)

theorem singletonEquation_uvars {data : RecursorData} {equation : VDefEq}
    (h : data.singletonEquation = some equation) : equation.uvars = data.uvars := by
  unfold singletonEquation at h
  dsimp only at h
  split at h <;> try contradiction
  unfold Restoration.equation at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨lhs, _, rhs, _, type, _, h⟩ := h
  cases h
  rfl

/-- Whether the generic elimination universe of the recursor admits Type-valued
instances. The source universe is tested at each occurrence, not globally. -/
def largeTarget (data : RecursorData) : Bool :=
  data.target.eval (List.replicate data.uvars 1) != 0

/-- Source sort at the occurrence's universe specialization. -/
def sourceLevel (data : RecursorData) (packed : List VLevel) : VLevel :=
  (data.schema.sourceLevel data.owner data.levels).inst packed

end RecursorData
end Lean4Lean.InductiveSignature
