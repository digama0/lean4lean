import Lean4Lean.Theory.DeclarationData

/-! Normalized inductive signatures and total eliminator generation.

The input contains families, constructor fields, and recursive occurrences.
It contains no recursor types, minor types, or equations. Those are generated
here, independently of the executable inductive compiler. Formation and the
connection to source declarations are separate judgments.

Telescope domains use de Bruijn indices and are listed outermost first.
Each domain is scoped over the common parameters and its preceding binders.
-/

namespace Lean4Lean
namespace InductiveSignature

structure Family where
  name : Name
  indices : List VExpr
  resultLevel : VLevel

/-- A higher-order recursive field ends at a specified mutual family. Its
binder domains and indices are scoped over parameters and preceding fields. -/
structure Recursive (families : Nat) where
  binders : List VExpr
  target : Fin families
  indices : List VExpr

inductive Field (families : Nat) where
  | external (type : VExpr)
  | recursive (type : VExpr) (shape : Recursive families)

/-- Whether the generator gives the field an induction hypothesis. -/
def Field.isRecursive : Field families → Bool
  | .external _ => false
  | .recursive _ _ => true

structure Constructor (families : Nat) where
  name : Name
  owner : Fin families
  fields : List (Field families)
  indices : List VExpr

end InductiveSignature

structure InductiveSignature where
  uvars : Nat
  params : List VExpr
  families : Array InductiveSignature.Family
  constructors : Array (InductiveSignature.Constructor families.size)
  isUnsafe : Bool := false

namespace InductiveSignature

/-- `count` variables, in binder order, beneath `below` other binders. -/
def vars (count below : Nat) : List VExpr :=
  (List.range count).reverse.map fun i => .bvar (below + i)

/-- Insert binders between the parameters and a telescope. -/
def insertBinders (domains : List VExpr) (count : Nat) : List VExpr :=
  domains.zipIdx.map fun (type, i) => type.liftN count i

def familyApp (s : InductiveSignature) (owner : Fin s.families.size)
    (levels : List VLevel) (params indices : List VExpr) : VExpr :=
  VExpr.mkApps (.const s.families[owner].name levels) (params ++ indices)

def recursiveType (s : InductiveSignature) (depth : Nat) (r : Recursive s.families.size) : VExpr :=
  VExpr.wrapForalls r.binders <|
    s.familyApp r.target (VLevel.params s.uvars)
      (vars s.params.length (depth + r.binders.length)) r.indices

/-- Retain the field's checked domain even when its recursive classification
requires unfolding. Generation must preserve these domains in minor types. -/
def fieldType (_s : InductiveSignature) (_depth : Nat) : Field _s.families.size → VExpr
  | .external type | .recursive type _ => type

def fieldTypes (s : InductiveSignature) (ctor : Constructor s.families.size) : List VExpr :=
  ctor.fields.zipIdx.map fun (field, i) => s.fieldType i field

def constructorType (s : InductiveSignature) (ctor : Constructor s.families.size) : VExpr :=
  VExpr.wrapForalls (s.params ++ s.fieldTypes ctor) <|
    s.familyApp ctor.owner (VLevel.params s.uvars)
      (vars s.params.length ctor.fields.length) ctor.indices

/-- The normalized declaration whose constructors the signature describes. -/
def declaration (s : InductiveSignature) : VInductDecl where
  uvars := s.uvars
  nparams := s.params.length
  isUnsafe := s.isUnsafe
  types := s.families.toList.zipIdx.map fun (family, i) => {
    name := family.name
    uvars := s.uvars
    type := VExpr.wrapForalls (s.params ++ family.indices) (.sort family.resultLevel)
    numIndices := family.indices.length
    resultLevel := family.resultLevel
    ctors := s.constructors.toList.filterMap fun ctor =>
      if ctor.owner.val = i then
        some { name := ctor.name, uvars := s.uvars, type := s.constructorType ctor }
      else none }

/-- Universe-specialized generation. Names are supplied separately so the
same generator can describe concrete names and fresh abstract eliminators.
Admissibility of the elimination universe is a formation obligation. -/
structure Instance (s : InductiveSignature) where
  uvars : Nat
  levels : List VLevel
  targetLevel : VLevel
  recursorName : Fin s.families.size → Name

/-- The head of a generated equation: a recursor constant. (The branch's abstract case
eliminators, the former second mode, are gone with `VExpr.elim`.)
Abstract symbols are disjoint syntax, indexed within their certified block. -/
inductive HeadMode where
  | recursor

namespace Instance

variable {s : InductiveSignature}

@[simp] def recursorHead (g : Instance s) (mode : HeadMode)
    (owner : Fin s.families.size) : VExpr :=
  match mode with
  | .recursor => .const (g.recursorName owner) (VLevel.params g.uvars)

def params (g : Instance s) : List VExpr := s.params.map (·.instL g.levels)

def familyApp (g : Instance s) (owner : Fin s.families.size)
    (params indices : List VExpr) : VExpr := s.familyApp owner g.levels params indices

/-- The motive of a family is fixed by its index telescope and its major
premise. `prior` counts the motives already in scope. -/
def motive (g : Instance s) (family : Family) (prior : Nat) : VExpr :=
  let indices := insertBinders (family.indices.map (·.instL g.levels)) prior
  let major := VExpr.mkApps (.const family.name g.levels)
    (vars s.params.length (prior + indices.length) ++ vars indices.length 0)
  VExpr.wrapForalls (indices ++ [major]) (.sort g.targetLevel)

def motives (g : Instance s) : List VExpr :=
  s.families.toList.zipIdx.map fun (family, i) => g.motive family i

/-- Embed a recursive field's local syntax into a context containing all
constructor fields, `ihs` previous induction hypotheses, and `extra` binders
between parameters and fields. The field's own higher-order binders remain
innermost. -/
def underFields (e : VExpr) (field totalFields ihs extra localDepth : Nat) : VExpr :=
  (e.liftN (totalFields - field + ihs) localDepth).liftN extra
    (totalFields + ihs + localDepth)

def recursiveFields (ctor : Constructor s.families.size) :
    List (Nat × Recursive s.families.size) :=
  ctor.fields.zipIdx.filterMap fun (field, i) =>
    match field with
    | .external _ => none
    | .recursive _ r => some (i, r)

/-- The induction hypothesis for a field is generated from that field's
recursive target and arguments, including every higher-order binder. -/
def hypothesis (g : Instance s) (ctor : Constructor s.families.size)
    (priorMinors priorIHs field : Nat) (r : Recursive s.families.size) : VExpr :=
  let nf := ctor.fields.length
  let extra := s.families.size + priorMinors
  let embed := fun e localDepth =>
    underFields (e.instL g.levels) field nf priorIHs extra localDepth
  let domains := r.binders.zipIdx.map fun (e, i) => embed e i
  let depth := domains.length
  let major := VExpr.mkApps (.bvar (nf - 1 - field + priorIHs + depth)) (vars depth 0)
  let motive := VExpr.bvar
    (nf + priorIHs + depth + priorMinors + (s.families.size - 1 - r.target.val))
  VExpr.wrapForalls domains <|
    VExpr.mkApps motive (r.indices.map (fun e => embed e depth) ++ [major])

def constructorApp (g : Instance s) (ctor : Constructor s.families.size)
    (extra below : Nat) : VExpr :=
  VExpr.mkApps (.const ctor.name g.levels)
    (vars s.params.length (extra + ctor.fields.length + below) ++
      vars ctor.fields.length below)

def minor (g : Instance s) (ctor : Constructor s.families.size) (prior : Nat) : VExpr :=
  let nf := ctor.fields.length
  let extra := s.families.size + prior
  let fields := insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let ihs := (recursiveFields ctor).zipIdx.map fun ((field, r), i) =>
    g.hypothesis ctor prior i field r
  let indices := ctor.indices.map fun e =>
    ((e.instL g.levels).liftN ihs.length).liftN extra (nf + ihs.length)
  let motive := VExpr.bvar (nf + ihs.length + prior + (s.families.size - 1 - ctor.owner.val))
  VExpr.wrapForalls (fields ++ ihs) <|
    VExpr.mkApps motive (indices ++ [g.constructorApp ctor extra ihs.length])

def minors (g : Instance s) : List VExpr :=
  s.constructors.toList.zipIdx.map fun (ctor, i) => g.minor ctor i

/-- The abstract context, innermost first, in which the `j`-th induction
hypothesis of the `prior`-th constructor's minor premise is formed:
parameters, motives, the earlier minors, all fields, and the earlier
hypotheses. -/
def hypothesisContext (g : Instance s) (ctor : Constructor s.families.size)
    (prior j : Nat) : List VExpr :=
  let extra := s.families.size + prior
  let fields := insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let ihs := ((recursiveFields ctor).zipIdx.map fun ((field, r), i) =>
    g.hypothesis ctor prior i field r).take j
  ihs.reverse ++ fields.reverse ++ (g.minors.take prior).reverse ++ g.motives.reverse ++
    g.params.reverse

def recursorType (g : Instance s) (owner : Fin s.families.size) : VExpr :=
  let family := s.families[owner]
  let extra := s.families.size + s.constructors.size
  let indices := insertBinders (family.indices.map (·.instL g.levels)) extra
  let major := g.familyApp owner
    (vars s.params.length (extra + indices.length)) (vars indices.length 0)
  let motive := VExpr.bvar
    (indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val))
  VExpr.wrapForalls (g.params ++ g.motives ++ g.minors ++ indices ++ [major]) <|
    VExpr.mkApps motive (vars indices.length 1 ++ [.bvar 0])

def recursor (g : Instance s) (owner : Fin s.families.size) : VConstVal where
  name := g.recursorName owner
  uvars := g.uvars
  type := g.recursorType owner

/-- Recursive calls in an equation are generated from the same field data as
its minor's induction hypotheses. No call template is accepted as input. -/
def recursiveCall (g : Instance s) (ctor : Constructor s.families.size)
    (field : Nat) (r : Recursive s.families.size) (mode : HeadMode := .recursor) : VExpr :=
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let embed := fun e localDepth => underFields (e.instL g.levels) field nf 0 extra localDepth
  let domains := r.binders.zipIdx.map fun (e, i) => embed e i
  let depth := domains.length
  let major := VExpr.mkApps (.bvar (nf - 1 - field + depth)) (vars depth 0)
  VExpr.wrapLams domains <|
    VExpr.mkApps (g.recursorHead mode r.target)
      (vars (s.params.length + extra) (nf + depth) ++
        r.indices.map (fun e => embed e depth) ++ [major])

/-- One equation per constructor, with its exact owner and minor position.
Both sides and the equation type are generated, including the binder domains. -/
def equation (g : Instance s) (index : Fin s.constructors.size)
    (mode : HeadMode := .recursor) : VDefEq :=
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  let lhs := VExpr.mkApps (g.recursorHead mode ctor.owner)
    (vars (s.params.length + extra) nf ++ indices ++ [major])
  let minor := VExpr.bvar (nf + s.constructors.size - 1 - index.val)
  let calls := (recursiveFields ctor).map fun (field, r) => g.recursiveCall ctor field r mode
  let rhs := VExpr.mkApps minor (vars nf 0 ++ calls)
  let motive := VExpr.bvar (nf + s.constructors.size + (s.families.size - 1 - ctor.owner.val))
  { uvars := g.uvars
    lhs := VExpr.wrapLams domains lhs
    rhs := VExpr.wrapLams domains rhs
    type := VExpr.wrapForalls domains (VExpr.mkApps motive (indices ++ [major])) }

def recursors (g : Instance s) : List VConstVal :=
  (List.finRange s.families.size).map g.recursor

def equations (g : Instance s) (mode : HeadMode := .recursor) : List VDefEq :=
  (List.finRange s.constructors.size).map fun index => g.equation index mode

variable (g : Instance s)

/-- The index telescope at the instance's universes. -/
def indicesAt (owner : Fin s.families.size) : List VExpr :=
  s.families[owner].indices.map (·.instL g.levels)

/-- The family applied to its parameter and index variables. -/
def majorType (owner : Fin s.families.size) : VExpr :=
  VExpr.mkApps (.const s.families[owner].name g.levels)
    (vars s.params.length s.families[owner].indices.length ++
      vars s.families[owner].indices.length 0)

/-- The field telescope at the instance's universes. -/
def fieldsAt (c : Constructor s.families.size) : List VExpr :=
  (s.fieldTypes c).map (·.instL g.levels)

/-- The constructor's result indices at the instance's universes. -/
def ctorIndicesAt (c : Constructor s.families.size) : List VExpr :=
  c.indices.map (·.instL g.levels)

end Instance

end InductiveSignature
end Lean4Lean
