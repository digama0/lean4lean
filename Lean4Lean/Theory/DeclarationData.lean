import Lean4Lean.Theory.VExpr.Telescope

/-! Declaration payloads containing only syntax. Environment operations and
well-formedness judgments live in later modules. -/

namespace Lean4Lean

structure VConstant where
  uvars : Nat
  type : VExpr

structure VDefEq where
  uvars : Nat
  lhs : VExpr
  rhs : VExpr
  type : VExpr

/-- Kernel data needed to type primitive projections.  Unlike a synthesized
eliminator term, this record contains only declaration data: all projection
types are computed from the constructor telescope below. -/
structure VProjectionInfo where
  uvars : Nat
  nparams : Nat
  nindices : Nat
  resultLevel : VLevel
  ctorName : Name
  ctorType : VExpr

structure VProjectionEntry where
  typeName : Name
  info : VProjectionInfo

/-- Number of constructor fields: the syntactic forall arity of the constructor
type beyond the common parameters. -/
def VProjectionInfo.numFields (info : VProjectionInfo) : Nat :=
  info.ctorType.forallArity - info.nparams

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name (VLevel.params v.uvars), v.value, v.type⟩

structure VInductiveType extends VConstVal where
  /-- Number of indices after the common parameters. This is recovered from
  the checked source arity by the executable implementation. -/
  numIndices : Nat
  /-- Sort level at the end of the parameter/index telescope. -/
  resultLevel : VLevel
  ctors : List VConstVal

structure VInductDecl where
  uvars : Nat
  nparams : Nat
  types : List VInductiveType
  /-- Unsafe inductive declarations skip the strict-positivity check. They are
  represented explicitly so that the abstract declaration judgment does not
  accidentally ascribe the safe formation rule to them. -/
  isUnsafe : Bool

def VInductDecl.typeConstants (decl : VInductDecl) : List VConstVal :=
  decl.types.map VInductiveType.toVConstVal

def VInductDecl.constructorConstants (decl : VInductDecl) : List VConstVal :=
  decl.types.flatMap VInductiveType.ctors

def VInductDecl.sourceNames (decl : VInductDecl) : List Name :=
  decl.typeConstants.map VConstVal.name ++
    decl.constructorConstants.map VConstVal.name

/-- Projection metadata is derived solely from singleton-constructor source
families. -/
def VInductDecl.projectionEntries (decl : VInductDecl) : List VProjectionEntry :=
  decl.types.filterMap fun type =>
    match type.ctors with
    | [ctor] => some {
        typeName := type.name
        info := {
          uvars := decl.uvars
          nparams := decl.nparams
          nindices := type.numIndices
          resultLevel := type.resultLevel
          ctorName := ctor.name
          ctorType := ctor.type } }
    | _ => none

/-- A declaration without families has no projection entries. -/
theorem VInductDecl.projectionEntries_eq_nil {decl : VInductDecl} (h : decl.types = []) :
    decl.projectionEntries = [] := by
  simp [VInductDecl.projectionEntries, h]

/-- The common parameters as de Bruijn variables beneath `depth` additional
constructor-field binders. -/
def VInductDecl.paramVars (decl : VInductDecl) (depth : Nat) : List VExpr :=
  (List.range decl.nparams).reverse.map fun i => .bvar (depth + i)

inductive VDecl where
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl)
  | mutualDef (_ : List VDefVal)


end Lean4Lean
