import Lean4Lean.Theory.Inductive.CaseSchema

/-! Total projection programs built from abstract case analysis.

The selected family may be indexed and its fields may depend on earlier
fields. Each preceding field is replaced by the already generated projection
applied to the same parameters, indices, and major premise. Universe levels
are finite input data; their typing and case admissibility are separate proof
obligations. No projection term or field type is accepted as input.
-/

namespace Lean4Lean

private instance decidableClosedN : ∀ (e : VExpr) (n : Nat), Decidable (e.ClosedN n)
  | .bvar _, _ => Nat.decLt ..
  | .sort .., _ | .const .., _ | .elim .., _ => instDecidableTrue
  | .app f a, n => @instDecidableAnd _ _ (decidableClosedN f n) (decidableClosedN a n)
  | .proj _ _ e, n => decidableClosedN e n
  | .lam t b, n | .forallE t b, n =>
    @instDecidableAnd _ _ (decidableClosedN t n) (decidableClosedN b (n + 1))

namespace InductiveSignature.CaseSchema

/-- Restored syntax in the source common-parameter context. Index domains
are scoped over parameters and preceding indices; field domains over
parameters and preceding fields. `major` is under parameters and all indices,
while `constructor` and `constructorIndices` are under parameters and fields. -/
structure StructureTelescope where
  params : List VExpr
  indices : List VExpr
  major : VExpr
  fields : List VExpr
  constructor : VExpr
  constructorIndices : List VExpr

/-- Scope checks reject malformed raw telescopes without inferring types. -/
def telescopeScoped (outer : Nat) (domains : List VExpr) : Bool :=
  domains.zipIdx.all fun (domain, i) => decide (domain.ClosedN (outer + i))

/-- Extract exactly one constructor and restore its source syntax before
building dependent projections. No identity of restored parameter spines is
assumed, so auxiliary families retain their certified specializations. -/
def structureTelescope (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (levels : List VLevel) : Option StructureTelescope := do
  if levels.length != schema.signature.uvars then none else
  let [ctor] := schema.signature.constructors.toList.filter (fun c => c.owner == owner)
    | none
  let family := schema.signature.families[owner]
  if ctor.indices.length != family.indices.length then none else
  let restore := fun e => schema.restoration.expr (e.instL levels)
  let params ← schema.signature.params.mapM restore
  let indices ← family.indices.mapM restore
  let fields ← (schema.signature.fieldTypes ctor).mapM restore
  let constructorIndices ← ctor.indices.mapM restore
  let major ← schema.restoration.expr <|
    schema.signature.familyApp owner levels
      (vars params.length indices.length) (vars indices.length 0)
  let constructor ← schema.restoration.expr <|
    VExpr.mkApps (.const ctor.name levels)
      (vars params.length fields.length ++ vars fields.length 0)
  if !(telescopeScoped 0 params && telescopeScoped params.length indices &&
      telescopeScoped params.length fields &&
      decide (major.ClosedN (params.length + indices.length)) &&
      decide (constructor.ClosedN (params.length + fields.length)) &&
      constructorIndices.all (fun e => decide (e.ClosedN (params.length + fields.length)))) then
    none
  else
    return { params, indices, major, fields, constructor, constructorIndices }

/-- A closed function together with its generated dependent function type.
`targetLevel` is input sort data; this record alone asserts no typing theorem. -/
structure ProjectionFunction where
  targetLevel : VLevel
  value : VExpr
  type : VExpr

/-- Arguments in the complete parameter/index/major context. -/
def StructureTelescope.arguments (data : StructureTelescope) : List VExpr :=
  vars data.params.length (data.indices.length + 1) ++
    vars data.indices.length 1 ++ [.bvar 0]

/-- The selected field's domain after simultaneous substitution of parameters
and previously generated field projections. The result is scoped under all
parameters, indices, and the major premise. -/
def StructureTelescope.fieldTarget (data : StructureTelescope) (domain : VExpr)
    (previous : List ProjectionFunction) : VExpr :=
  instantiateParams domain <|
    vars data.params.length (data.indices.length + 1) ++
      previous.map (fun projection => VExpr.mkApps projection.value data.arguments)

/-- Build one case call from its derived field domain. Its motive abstracts
all indices and the major; its sole minor abstracts every constructor field and
selects the current one. Motive and minor are lifted past the call's indices
and major while their common parameters remain free. -/
def StructureTelescope.step (data : StructureTelescope) (block : Name) (owner : Nat)
    (levels : List VLevel) (domain : VExpr) (target : VLevel)
    (previous : List ProjectionFunction) : ProjectionFunction :=
  let fieldType := data.fieldTarget domain previous
  let motive := VExpr.wrapLams (data.indices ++ [data.major]) fieldType
  let minor := VExpr.wrapLams data.fields (.bvar (data.fields.length - 1 - previous.length))
  let below := data.indices.length + 1
  let body := VExpr.mkApps (.elim block owner (target :: levels))
    (vars data.params.length below ++ [motive.liftN below, minor.liftN below] ++
      vars data.indices.length 1 ++ [.bvar 0])
  let domains := data.params ++ data.indices ++ [data.major]
  { targetLevel := target
    value := VExpr.wrapLams domains body
    type := VExpr.wrapForalls domains fieldType }

def StructureTelescope.prefix (data : StructureTelescope) (block : Name) (owner : Nat)
    (levels : List VLevel) : List VExpr → List VLevel → List ProjectionFunction →
      Option (List ProjectionFunction)
  | _, [], previous => some previous
  | [], _ :: _, _ => none
  | domain :: domains, target :: targets, previous =>
    data.prefix block owner levels domains targets
      (previous ++ [data.step block owner levels domain target previous])

/-- Generate a prefix of field projections, in constructor order. A sort
level is required for every field through the desired projection. Invalid
universe arity, multiple constructors, malformed telescopes, failed
restoration, or an overlong requested prefix return `none`.

The generated values use abstract case eliminators only; the generator never
inserts primitive projections or references a recursor constant. -/
def projectionPrefix (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (uvars : Nat)
    (levels fieldSorts : List VLevel) : Option (List ProjectionFunction) := do
  if !(levels.all (fun level => decide (level.WF uvars)) &&
      fieldSorts.all (fun level => decide (level.WF uvars))) then none else
  let data ← schema.structureTelescope owner levels
  data.prefix block owner.val levels data.fields fieldSorts []

end InductiveSignature.CaseSchema
end Lean4Lean

namespace Lean4Lean
namespace VExpr

/-- A scoped simultaneous substitution preserves the indicated scope. -/
theorem ClosedN.subst_closed {e : VExpr} (he : e.ClosedN k)
    (hσ : ∀ i < k, (σ i).ClosedN n) : (e.subst σ).ClosedN n := by
  induction e generalizing k n σ with (simp only [ClosedN, subst] at he ⊢)
  | bvar i => exact hσ i he
  | app _ _ ih1 ih2 => exact ⟨ih1 he.1 hσ, ih2 he.2 hσ⟩
  | proj _ _ _ ih => exact ih he hσ
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    refine ⟨ih1 he.1 hσ, ih2 he.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact (hσ i (by omega)).liftN

theorem ClosedN.mkApps_closed (hf : fn.ClosedN n)
    (ha : ∀ arg ∈ args, arg.ClosedN n) : (VExpr.mkApps fn args).ClosedN n := by
  induction args generalizing fn with
  | nil => exact hf
  | cons a args ih => exact ih ⟨hf, ha _ (.head _)⟩ (fun _ h => ha _ (.tail _ h))

/-- Close a lambda telescope whose domains are scoped in binder order. -/
theorem ClosedN.wrapLams_closed
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapLams domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

theorem ClosedN.wrapForalls_closed
    (hdomains : ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i))
    (hbody : body.ClosedN (n + domains.length)) :
    (VExpr.wrapForalls domains body).ClosedN n := by
  induction domains generalizing n with
  | nil => exact hbody
  | cons d ds ih =>
    refine ⟨hdomains 0 (by simp), ih (n := n + 1) ?_ ?_⟩
    · intro i hi
      have hh := hdomains (i + 1) (by simp; omega)
      change ds[i].ClosedN (n + (i + 1)) at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hh
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hbody

end VExpr
namespace InductiveSignature.CaseSchema

theorem telescopeScoped_iff : telescopeScoped n domains = true ↔
    ∀ i (hi : i < domains.length), domains[i].ClosedN (n + i) := by
  simp only [telescopeScoped, List.all_eq_true, Prod.forall, decide_eq_true_eq]
  constructor
  · intro h i hi
    exact h _ i (List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi))
  · intro h e i hi
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hi)
    exact h i hlt

variable {left right domains : List VExpr} {e domain : VExpr}
  {data : StructureTelescope} {previous result : List ProjectionFunction}
  {block : Name} {owner : Nat} {levels targets : List VLevel} {target : VLevel}
  {n : Nat}

/-- Fixed projection templates reserve the first universe parameters for the
field sorts in prefix order, followed by the source declaration universes.
An occurrence specializes these templates with `fieldSorts ++ sourceLevels`. -/
def genericProjectionPrefix (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (fieldCount : Nat) :
    Option (List ProjectionFunction) :=
  schema.projectionPrefix block owner (schema.signature.uvars + fieldCount)
    ((List.range schema.signature.uvars).map fun i => .param (fieldCount + i))
    (VLevel.params fieldCount)

end InductiveSignature.CaseSchema
end Lean4Lean

/-! Declaration-generated structure eta templates. Eta is a separate equality
principle; generating these terms does not derive eta from case iota. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- Reconstruct the constructor application from all its generated field
projections in the common-parameter/major context. -/
def StructureTelescope.etaReconstruction (data : StructureTelescope)
    (projections : List ProjectionFunction) : VExpr :=
  instantiateParams data.constructor <|
    vars data.params.length 1 ++ projections.map fun projection =>
      VExpr.mkApps projection.value (vars data.params.length 1 ++ [.bvar 0])

/-- A complete, closed template for the structure eta equality. Indexed
families are rejected, matching the separate structure eta principle. Every
field is supplied by this schema's projection generator. -/
def structureEta (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (uvars : Nat)
    (levels fieldSorts : List VLevel) : Option VDefEq := do
  let data ← schema.structureTelescope owner levels
  if data.indices.length != 0 || data.fields.length != fieldSorts.length then none else
  let projections ← schema.projectionPrefix block owner uvars levels fieldSorts
  let domains := data.params ++ [data.major]
  return {
    uvars := uvars
    lhs := VExpr.wrapLams domains (data.etaReconstruction projections)
    rhs := VExpr.wrapLams domains (.bvar 0)
    type := VExpr.wrapForalls domains data.major.lift }

end Lean4Lean.InductiveSignature.CaseSchema
