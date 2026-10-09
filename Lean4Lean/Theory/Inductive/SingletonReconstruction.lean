import Lean4Lean.Theory.Inductive.CaseProjections

/-! Deterministic constructor reconstruction for singleton elimination.
Index-determined data fields are read from the index spine. Remaining
fields are projected into Prop by generated abstract case functions. In
particular an earlier data field is never projected out of a proof into Type.
This module contains only syntax generation; typing and installation are
separate obligations. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- Select the first index that is literally the chosen constructor field.
An arbitrary equality between field and index terms is not a reconstruction
program and is deliberately not searched for here. -/
def StructureTelescope.fieldIndex (data : StructureTelescope) (field : Nat) : Option Nat :=
  (data.constructorIndices.zipIdx.find? fun (index, _) =>
    match index with
    | .bvar i => i == data.fields.length - 1 - field
    | _ => false).map Prod.snd

/-- A closed selector for an index, retaining the generated dependent
field type after earlier reconstruction steps. -/
def StructureTelescope.indexSelector (data : StructureTelescope) (domain : VExpr)
    (target : VLevel) (previous : List ProjectionFunction) (index : Nat) : ProjectionFunction :=
  let domains := data.params ++ data.indices ++ [data.major]
  { targetLevel := target
    value := VExpr.wrapLams domains (.bvar (data.indices.length - index))
    type := VExpr.wrapForalls domains (data.fieldTarget domain previous) }

/-- A single normalized sort is supplied per source field. Only a literal
zero sort permits proof projection (the case projection `StructureTelescope.step`
at target level zero; earlier fields may be index selectors as well as proof
projections); all other fields require a direct index selector. Typing must establish those normalized sort assignments. -/
def StructureTelescope.reconstructionPrefix (data : StructureTelescope) (block : Name)
    (owner : Nat) (levels : List VLevel) : List VExpr → List VLevel →
      List ProjectionFunction → Option (List ProjectionFunction)
  | [], [], previous => some previous
  | domain :: domains, target :: targets, previous => do
    let next ← match data.fieldIndex previous.length with
      | some index =>
        if index < data.indices.length then
          some (data.indexSelector domain target previous index)
        else none
      | none =>
        match target with
        | .zero => some (data.step block owner levels domain .zero previous)
        | _ => none
    data.reconstructionPrefix block owner levels domains targets (previous ++ [next])
  | _, _, _ => none

/-- Construct the unique declared constructor by substituting deterministic
field selectors into its restored source application. Failed restoration,
wrong telescope arity, a non-index data field, or a non-Prop projection is
rejected. The resulting function takes parameters, indices, and the major. -/
def singletonReconstruction (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (U : Nat)
    (levels fieldSorts : List VLevel) : Option VExpr := do
  if !(levels.all (fun level => decide (level.WF U)) &&
      fieldSorts.all (fun level => decide (level.WF U))) then none else
  let data ← schema.structureTelescope owner levels
  let fields ← data.reconstructionPrefix block owner.val levels data.fields fieldSorts []
  let constructor := instantiateParams data.constructor <|
    vars data.params.length (data.indices.length + 1) ++
      fields.map (fun field => VExpr.mkApps field.value data.arguments)
  return VExpr.wrapLams (data.params ++ data.indices ++ [data.major]) constructor

/-- Apply the reconstruction program directly at an occurrence. Only field
projection functions retain beta redexes; the reconstructed constructor head
is exposed immediately for the recursor's iota rule. -/
def singletonReconstructAt (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (U : Nat)
    (levels fieldSorts : List VLevel) (parameters indices : List VExpr)
    (major : VExpr) : Option VExpr := do
  if !(levels.all (fun level => decide (level.WF U)) &&
      fieldSorts.all (fun level => decide (level.WF U))) then none else
  let data ← schema.structureTelescope owner levels
  if parameters.length != data.params.length || indices.length != data.indices.length then none else
  let fields ← data.reconstructionPrefix block owner.val levels data.fields fieldSorts []
  return instantiateParams data.constructor <|
    parameters ++ fields.map (fun field => VExpr.mkApps field.value (parameters ++ indices ++ [major]))

end Lean4Lean.InductiveSignature.CaseSchema
