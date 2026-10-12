import Init.Data.Array.Lemmas
import Init.Data.List.Sublist
import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.TypeChecker


namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

/-! # Concrete inductive verification adapters

Metadata prefix bookkeeping and concrete source-expression substitution used by inductive
verification. Abstract telescope syntax, typing, and guarded-iota closure are supplied by the
imported theory modules, which preserve their existing qualified names.
-/

namespace VerifyInductive

/-- Building a source declaration from a prefix of an expanded
declaration's recovered header metadata preserves the index count at every
source position.  This is the metadata-level fact needed after nested
lowering: source families keep their positions, while auxiliary families
are appended to the expanded declaration. -/
theorem VInductDeclSkeleton.withMetadataPrefix_numIndices
    (skeleton : VInductDeclSkeleton) (expanded source : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length)
    (Hmaterialize : skeleton.withMetadata
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel)) = some source)
    (i : Nat) (hi : i < skeleton.types.length)
    (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).numIndices =
      (expanded.types[i]'hexpanded).numIndices := by
  rcases VInductDeclSkeleton.withMetadata_typeAt Hmaterialize hi with
    ⟨data, hdata, hsourceLookup⟩
  have hmetadata :
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel))[i]? =
        some (expanded.types[i].numIndices,
          expanded.types[i].resultLevel) := by
    simp [hi, hle]
  have hdataEq : data =
      (expanded.types[i].numIndices, expanded.types[i].resultLevel) := by
    rw [hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have hsourceEq : source.types[i] =
      skeleton.types[i].toVInductiveType expanded.types[i].numIndices
        expanded.types[i].resultLevel := by
    rw [List.getElem?_eq_getElem hsource] at hsourceLookup
    exact Option.some.inj hsourceLookup
  have hindices := congrArg VInductiveType.numIndices hsourceEq
  simpa [VInductiveTypeSkeleton.toVInductiveType] using hindices

/-- The source declaration is obtained by `VInductDeclSkeleton.withMetadata` from exactly the
metadata prefix of an expanded declaration.  Nested lowering appends auxiliary families, so
this is the declaration-level certificate connecting independently recovered
source metadata to the lowered checker result. -/
inductive SourcePrefixOfLowered
    (source expanded : VInductDecl) : Prop
  | intro (skeleton : VInductDeclSkeleton)
      (materialized : skeleton.withMetadata
        ((expanded.types.take skeleton.types.length).map fun type =>
          (type.numIndices, type.resultLevel)) = some source) :
      SourcePrefixOfLowered source expanded

theorem SourcePrefixOfLowered.numIndices
    {source expanded : VInductDecl}
    (H : SourcePrefixOfLowered source expanded)
    (hle : source.types.length ≤ expanded.types.length)
    (i : Nat) (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).numIndices =
      (expanded.types[i]'hexpanded).numIndices := by
  rcases H with ⟨skeleton, Hmaterialize⟩
  have hskeleton : skeleton.types.length = source.types.length :=
    (VInductDeclSkeleton.withMetadata_fields Hmaterialize).2.2.2.symm
  apply VInductDeclSkeleton.withMetadataPrefix_numIndices skeleton expanded
    source
  · simpa [hskeleton] using hle
  · exact Hmaterialize
  · simpa [hskeleton] using hsource

/-- Every sufficiently long expanded declaration determines a source declaration from a
metadata-free skeleton, of the skeleton's size, by taking the expanded
metadata prefix.  This is the constructor used by the outer nested verifier;
the source declaration is produced rather than supplied with unconstrained
semantic arities. -/
theorem VInductDeclSkeleton.withMetadataExpandedPrefix
    (skeleton : VInductDeclSkeleton) (expanded : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length) :
    ∃ source,
      skeleton.withMetadata
        ((expanded.types.take skeleton.types.length).map fun type =>
          (type.numIndices, type.resultLevel)) = some source ∧
      SourcePrefixOfLowered source expanded := by
  let metadata :=
    (expanded.types.take skeleton.types.length).map fun type =>
      (type.numIndices, type.resultLevel)
  have hmetadata : metadata.length = skeleton.types.length := by
    simp [metadata, List.length_take, Nat.min_eq_left hle]
  let source : VInductDecl := {
    uvars := skeleton.uvars
    nparams := skeleton.nparams
    types := List.zipWith (fun type data =>
      type.toVInductiveType data.1 data.2) skeleton.types metadata
    isUnsafe := skeleton.isUnsafe }
  have Hmaterialize : skeleton.withMetadata metadata = some source := by
    simp [VInductDeclSkeleton.withMetadata, hmetadata, source]
  exact ⟨source, Hmaterialize, ⟨skeleton, Hmaterialize⟩⟩

/-- Rebuilding an expression from its application head and left-to-right
argument list is exact. -/
theorem VExpr.mkApps_getAppFnArgs (e : VExpr) :
    let (fn, args) := e.getAppFnArgs
    VExpr.mkApps fn args = e := by
  exact _root_.Lean4Lean.VExpr.mkApps_getAppFnArgs e

/-- A dependency-ordered list of well-formed constants may be viewed as a
sequence of abstract axioms extending a well-formed environment.  Stating
the input typing in the base environment is sufficient because each
constant can be weakened through the preceding fresh additions. -/
theorem VEnv.WF.addConstVals
    {env env' : VEnv} {cis : List VConstVal}
    (Henv : env.WF)
    (Hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (Hadd : env.addConstVals cis = some env') : env'.WF :=
  _root_.Lean4Lean.VEnv.WF.addConstVals Henv Hwf Hadd

/-- Source-side residual substitution matching complete application of a
forall telescope.  At each step the outer binder lies beneath all still-inner
binders in the already-open body, hence the decreasing `args.length` cutoff. -/
def Expr.instantiateForallBody : Expr → List Expr → Expr
  | body, [] => body
  | body, arg :: args =>
      instantiateForallBody (body.instantiate1' arg args.length) args


end VerifyInductive

/-- The declaration with its recursors replaced: the pipeline fixes the source part of the
declaration at the constructor phase and adds the generated recursors (with their ι rules) at
the recursor phase. The source fields (`uvars`, `nparams`, `types`, `isUnsafe`) are unchanged, so
`typeConstants`, `constructorConstants`, `projectionEntries`, `SourceWF`, `TypeShape`, ... reduce
to those of `decl`. -/
def VInductDecl.withRecs (decl : VInductDecl) (recs : List VRecursor) : VInductDecl :=
  { decl with recs := recs }

@[simp] theorem VInductDecl.withRecs_types (decl : VInductDecl) (recs : List VRecursor) :
    (decl.withRecs recs).types = decl.types := rfl
@[simp] theorem VInductDecl.withRecs_uvars (decl : VInductDecl) (recs : List VRecursor) :
    (decl.withRecs recs).uvars = decl.uvars := rfl
@[simp] theorem VInductDecl.withRecs_nparams (decl : VInductDecl) (recs : List VRecursor) :
    (decl.withRecs recs).nparams = decl.nparams := rfl
@[simp] theorem VInductDecl.withRecs_isUnsafe (decl : VInductDecl) (recs : List VRecursor) :
    (decl.withRecs recs).isUnsafe = decl.isUnsafe := rfl
@[simp] theorem VInductDecl.withRecs_recs (decl : VInductDecl) (recs : List VRecursor) :
    (decl.withRecs recs).recs = recs := rfl
@[simp] theorem VInductDecl.withRecs_typeConstants (decl : VInductDecl) (recs : List VRecursor) :
    (decl.withRecs recs).typeConstants = decl.typeConstants := rfl
@[simp] theorem VInductDecl.withRecs_constructorConstants (decl : VInductDecl)
    (recs : List VRecursor) :
    (decl.withRecs recs).constructorConstants = decl.constructorConstants := rfl
@[simp] theorem VInductDecl.withRecs_projectionEntries (decl : VInductDecl)
    (recs : List VRecursor) :
    (decl.withRecs recs).projectionEntries = decl.projectionEntries := rfl

/-- `Except.WF.bind` for the reader monad of the inductive checker (`AddInductive.M`). -/
theorem AddInductive.M.WF_bind {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context} {P : α → Prop} {Q : β → Prop}
    (h1 : (x c).WF P) (h2 : ∀ a, P a → (f a c).WF Q) :
    ((x >>= f) c).WF Q :=
  Except.WF.bind h1 h2

@[simp] theorem AddInductive.withEnv_apply (env : Environment) (x : AddInductive.M α)
    (c : AddInductive.Context) : AddInductive.withEnv env x c = x { c with env := env } := rfl

@[simp] theorem AddInductive.withTypeCheckerLParams_apply (lparams : List Name)
    (x : AddInductive.M α) (c : AddInductive.Context) :
    AddInductive.withTypeCheckerLParams lparams x c =
      x { c with typeCheckerLParams := some lparams } := rfl

end Lean4Lean
