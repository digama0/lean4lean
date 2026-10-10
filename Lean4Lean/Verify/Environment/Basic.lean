import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Inductive.Add

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

namespace VerifyInductive

/-- Inductive-header lookups for the members named by `InductiveVal.all`, kept
in the same order as the kernel metadata.  This lives at the generic
environment layer because nested-inductive recognition needs it before the
inductive checker itself starts. -/
inductive InductiveMemberInfos (env : Environment) : List Name → Prop
  | nil : InductiveMemberInfos env []
  | cons : env.find? name = some (.inductInfo info) →
      InductiveMemberInfos env names →
      InductiveMemberInfos env (name :: names)

theorem InductiveMemberInfos.find
    (H : InductiveMemberInfos env names)
    (hname : name ∈ names) :
    ∃ info, env.find? name = some (.inductInfo info) := by
  induction H with
  | nil => simp at hname
  | @cons head info tail hhead _ ih =>
    simp only [List.mem_cons] at hname
    rcases hname with rfl | htail
    · exact ⟨info, hhead⟩
    · exact ih htail

/-- One kernel inductive header has a complete, duplicate-free mutual
family, including the header through which it was discovered. -/
structure MutualInductiveClosure
    (env : Environment) (targetName : Name) (value : InductiveVal) : Prop where
  members : InductiveMemberInfos env value.all
  target : targetName ∈ value.all
  names : value.all.Nodup
  /-- Every header in the mutual block was emitted with the
  same common-parameter count. -/
  parameters : ∀ member info, member ∈ value.all →
    env.find? member = some (.inductInfo info) →
    info.numParams = value.numParams

/-- Every kernel inductive header has complete mutual-family metadata.
Nested lowering follows `InductiveVal.all`, so this is part of the persistent
kernel-environment invariant rather than a per-declaration callback. -/
def MutualInductivesClosed (env : Environment) : Prop :=
  ∀ targetName value, env.find? targetName = some (.inductInfo value) →
    MutualInductiveClosure env targetName value

/-- Kernel environments do not contain dangling or unlisted constructor
metadata: every constructor's recorded inductive owner is itself present,
lists the constructor, and has the constructor's `isUnsafe`.  This is a
persistent kernel-environment invariant, not a nested-lowering premise.  It
also holds in the environments an inductive declaration builds while it is
checked, because a constructor is only added after the header that lists it. -/
def ConstructorOwnersPresent (env : Environment) : Prop :=
  ∀ name info, env.find? name = some (.ctorInfo info) →
    ∃ owner, env.find? info.induct = some (.inductInfo owner) ∧
      name ∈ owner.ctors ∧ info.isUnsafe = owner.isUnsafe

/-- Every constructor name that a present inductive header lists is, if present, a
constructor whose recorded inductive is that header, with the header's `isUnsafe`.  Presence
is a premise because while an inductive declaration is checked its headers are installed
before the constructors they list; on a complete environment this follows from
`InductiveConstructorsCoherent`. -/
def ListedConstructorsCoherent (env : Environment) : Prop :=
  ∀ familyName familyInfo, env.find? familyName = some (.inductInfo familyInfo) →
    ∀ name ∈ familyInfo.ctors, ∀ ci, env.find? name = some ci →
      ∃ info, ci = .ctorInfo info ∧ info.induct = familyName ∧
        info.isUnsafe = familyInfo.isUnsafe

/-- Every constructor name that a present inductive header lists is present: no header is
waiting for its constructors.  This holds for the environments a declaration starts from,
and is what makes a fresh name unlisted. -/
def ListedConstructorsPresent (env : Environment) : Prop :=
  ∀ familyName familyInfo, env.find? familyName = some (.inductInfo familyInfo) →
    ∀ name ∈ familyInfo.ctors, ∃ ci, env.find? name = some ci

/-- `InductiveMemberInfos` depends only on kernel constant lookup. -/
theorem InductiveMemberInfos.mapEnvironmentEq
    {source targetEnv : Environment}
    (H : InductiveMemberInfos source names)
    (heq : ∀ name, source.find? name = targetEnv.find? name) :
    InductiveMemberInfos targetEnv names := by
  induction H with
  | nil => exact .nil
  | @cons name info names hfind _ ih =>
    exact .cons (by rw [← heq name]; exact hfind) ih

/-- One closed mutual family transports across extensionally equal kernel
constant maps. -/
theorem MutualInductiveClosure.mapEnvironmentEq
    {source targetEnv : Environment}
    (H : MutualInductiveClosure source targetName value)
    (heq : ∀ name, source.find? name = targetEnv.find? name) :
    MutualInductiveClosure targetEnv targetName value where
  members := H.members.mapEnvironmentEq heq
  target := H.target
  names := H.names
  parameters := by
    intro member info hmember hfind
    exact H.parameters member info hmember (by
      rw [heq member]
      exact hfind)

/-- Closure of every mutual family is invariant under extensional equality of
kernel constant lookup. -/
theorem MutualInductivesClosed.mapEnvironmentEq
    {source targetEnv : Environment}
    (H : MutualInductivesClosed source)
    (heq : ∀ name, source.find? name = targetEnv.find? name) :
    MutualInductivesClosed targetEnv := by
  intro targetName value htarget
  have hsource : source.find? targetName = some (.inductInfo value) := by
    rw [heq targetName]
    exact htarget
  exact (H targetName value hsource).mapEnvironmentEq heq

/-- The kernel metadata for one constructor listed by an inductive
header agrees with that header at every field needed to specialize the
constructor at the family's common parameters. -/
structure CtorInfoCoherentAt
    (env : Environment) (familyName : Name) (familyInfo : InductiveVal)
    (i : Nat) (hi : i < familyInfo.ctors.length) where
  info : ConstructorVal
  lookup : env.find? familyInfo.ctors[i] = some (.ctorInfo info)
  induct : info.induct = familyName
  cidx : info.cidx = i
  numParams : info.numParams = familyInfo.numParams
  levelParams : info.levelParams = familyInfo.levelParams
  isUnsafe : info.isUnsafe = familyInfo.isUnsafe

/-- Every constructor name listed by a kernel inductive header resolves
to coherent constructor metadata. -/
def InductiveConstructorsCoherent (env : Environment) : Prop :=
  ∀ familyName familyInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    ∀ i (hi : i < familyInfo.ctors.length),
      Nonempty (CtorInfoCoherentAt env familyName familyInfo i hi)

/-- Semantic common-parameter coherence for one visible kernel
constructor.  Concrete parameter domains need only be definitionally equal;
the independently translated family and constructor types are normalized in
the shared abstract environment before their parameter contexts are compared. -/
structure ConstructorParameterAlignmentAt
    (env : Environment) (venv : VEnv)
    (familyName : Name) (familyInfo : InductiveVal)
    (i : Nat) (hi : i < familyInfo.ctors.length)
    extends CtorInfoCoherentAt env familyName familyInfo i hi where
  familyTarget : VConstant
  constructorTarget : VConstant
  familyLookup : venv.constants familyName = some familyTarget
  constructorLookup : venv.constants familyInfo.ctors[i] = some constructorTarget
  familyUvars : familyTarget.uvars = familyInfo.levelParams.length
  constructorUvars : constructorTarget.uvars = familyInfo.levelParams.length
  familyNormalized : VExpr
  constructorNormalized : VExpr
  familyDomains : List VExpr
  constructorDomains : List VExpr
  familyTail : VExpr
  constructorTail : VExpr
  familyType : VExpr
  constructorType : VExpr
  familyDefEq : venv.IsDefEq familyInfo.levelParams.length []
    familyTarget.type familyNormalized familyType
  constructorDefEq : venv.IsDefEq familyInfo.levelParams.length []
    constructorTarget.type constructorNormalized constructorType
  familyParams : familyNormalized.takeForalls familyInfo.numParams =
    some (familyDomains, familyTail)
  constructorParams : constructorNormalized.takeForalls familyInfo.numParams =
    some (constructorDomains, constructorTail)
  parameterDomains : venv.IsDefEqCtx familyInfo.levelParams.length []
    familyDomains.reverse constructorDomains.reverse

/-- Every constructor visible in one safety-indexed abstract environment has
kernel metadata and definitionally equal translated common parameters. -/
def ConstructorParameterAlignment
    (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  ∀ familyName familyInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    safety ≤ (if familyInfo.isUnsafe then .unsafe else .safe) →
    ∀ i (hi : i < familyInfo.ctors.length),
      Nonempty (ConstructorParameterAlignmentAt
        env venv familyName familyInfo i hi)

end VerifyInductive

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]


/-- Kernel-environment contract for a unary type-annotation wrapper.

Lean's `Expr.consumeTypeAnnotations` recognizes these wrappers by
name alone.  Recording the actual environment lookup and delta body prevents a
hostile declaration at the reserved name from being silently treated as an
identity wrapper. -/
structure UnaryTypeAnnotationWrapper (env : Environment) (name : Name) : Prop where
  operational : ∃ info value,
    env.find? name = some info ∧
    info.safety = .safe ∧
    info.deltaValue? = some value ∧
    ∀ (levels : List Level) {arg : Expr}, arg.Closed →
      BetaReduce
        (.app (value.instantiateLevelParams info.levelParams levels) arg) arg

/-- Kernel-environment contract for a binary type-annotation
wrapper whose result is its first argument. -/
structure BinaryTypeAnnotationWrapper (env : Environment) (name : Name) : Prop where
  operational : ∃ info value,
    env.find? name = some info ∧
    info.safety = .safe ∧
    info.deltaValue? = some value ∧
    ∀ (levels : List Level) {first second : Expr},
      first.Closed → second.Closed →
      BetaReduce
        (.app (.app (value.instantiateLevelParams info.levelParams levels)
          first) second) first

/-- The wrapper names accepted by `ok` have their real, identity-like delta
bodies in `env`.  The inductive checker strips an annotation only if
`Kernel.Environment.isTypeAnnotationWrapper env` accepts its head, which
establishes this for `env` itself (`TypeAnnotationWrappers.of_env`), so no
invariant on the environment is involved. -/
structure TypeAnnotationWrappers (env : Environment) (ok : Name → Bool) : Prop where
  optParam : ok ``optParam = true → BinaryTypeAnnotationWrapper env ``optParam
  autoParam : ok ``autoParam = true → BinaryTypeAnnotationWrapper env ``autoParam
  outParam : ok ``outParam = true → UnaryTypeAnnotationWrapper env ``outParam
  semiOutParam : ok ``semiOutParam = true → UnaryTypeAnnotationWrapper env ``semiOutParam

private theorem binaryWrapperBody {value : Expr} {n₁ n₂ : Name} {t₁ t₂ : Expr}
    {bi₁ bi₂ : BinderInfo} (hvalue : value = .lam n₁ t₁ (.lam n₂ t₂ (.bvar 1) bi₂) bi₁)
    (ps : List Name) (levels : List Level) {first second : Expr}
    (hfirst : first.Closed) (hsecond : second.Closed) :
    BetaReduce
      (.app (.app (value.instantiateLevelParams ps levels) first) second) first := by
  subst hvalue
  have h1 := hfirst.looseBVarRange_zero
  have h2 := hsecond.looseBVarRange_zero
  rw [Expr.instantiateLevelParams_eq]
  simp only [Expr.instantiateLevelParamsCore']
  generalize Expr.instantiateLevelParamsCore' _ _ t₁ = t₁'
  generalize Expr.instantiateLevelParamsCore' _ _ t₂ = t₂'
  refine .trans (.app (.beta h1)) ?_
  have hbody : (Expr.lam n₂ t₂' (.bvar 1) bi₂).instantiate1' first =
      .lam n₂ (t₂'.instantiate1' first) first bi₂ := by
    simp [Expr.instantiate1', Expr.liftLooseBVars_eq_self, h1]
  rw [hbody]
  have := BetaReduce.beta (i := n₂) (ty := t₂'.instantiate1' first) (body := first)
    (bi := bi₂) h2
  rwa [Expr.instantiate1_eq_self h1] at this

private theorem unaryWrapperBody {value : Expr} {n₁ : Name} {t₁ : Expr} {bi₁ : BinderInfo}
    (hvalue : value = .lam n₁ t₁ (.bvar 0) bi₁)
    (ps : List Name) (levels : List Level) {arg : Expr} (harg : arg.Closed) :
    BetaReduce (.app (value.instantiateLevelParams ps levels) arg) arg := by
  subst hvalue
  have h := harg.looseBVarRange_zero
  rw [Expr.instantiateLevelParams_eq]
  simp only [Expr.instantiateLevelParamsCore']
  generalize Expr.instantiateLevelParamsCore' _ _ t₁ = t₁'
  have := BetaReduce.beta (i := n₁) (ty := t₁') (body := .bvar 0) (bi := bi₁) h
  simpa [Expr.instantiate1', Expr.liftLooseBVars_eq_self, h] using this

/-- The names that `Kernel.Environment.isTypeAnnotationWrapper env` accepts are
declared as identity-like safe definitions in every environment `target` that
has the definitions of `env`. -/
theorem TypeAnnotationWrappers.of_reflect (env target : Environment)
    (hreflect : ∀ {n v}, env.find? n = some (.defnInfo v) →
      target.find? n = some (.defnInfo v)) :
    TypeAnnotationWrappers target env.isTypeAnnotationWrapper := by
  have key : ∀ name, env.isTypeAnnotationWrapper name = true →
      ∃ v, env.find? name = some (.defnInfo v) ∧ v.safety = .safe ∧
        ((name = `optParam ∨ name = `autoParam) →
          ∃ n₁ t₁ n₂ t₂ bi₁ bi₂, v.value = .lam n₁ t₁ (.lam n₂ t₂ (.bvar 1) bi₂) bi₁) ∧
        ((name = `outParam ∨ name = `semiOutParam) →
          ∃ n₁ t₁ bi₁, v.value = .lam n₁ t₁ (.bvar 0) bi₁) := by
    intro name h
    unfold Kernel.Environment.isTypeAnnotationWrapper at h
    split at h
    · rename_i v hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hsafe, _⟩, h⟩ := h
      refine ⟨v, hfind, hsafe, fun hn => ?_, fun hn => ?_⟩
      · have hn' : (name == `optParam || name == `autoParam) = true := by
          rcases hn with rfl | rfl <;> rfl
        rw [if_pos hn'] at h
        split at h
        · rename_i n₁ t₁ n₂ t₂ bi₂ bi₁ hv; exact ⟨_, _, _, _, _, _, hv⟩
        · simp at h
      · have hn' : (name == `optParam || name == `autoParam) = false := by
          rcases hn with rfl | rfl <;> rfl
        have hn'' : (name == `outParam || name == `semiOutParam) = true := by
          rcases hn with rfl | rfl <;> rfl
        rw [if_neg (by simp [hn']), if_pos hn''] at h
        split at h
        · rename_i n₁ t₁ bi₁ hv; exact ⟨_, _, _, hv⟩
        · simp at h
    · simp at h
  have hsafety (v : DefinitionVal) (h : v.safety = .safe) :
      (ConstantInfo.defnInfo v).safety = .safe := by
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨v, hfind, hsafe, hb, -⟩ := key _ h
    obtain ⟨_, _, _, _, _, _, hv⟩ := hb (.inl rfl)
    exact ⟨⟨_, v.value, hreflect hfind, hsafety v hsafe, rfl,
      fun levels _ _ h1 h2 => binaryWrapperBody hv _ levels h1 h2⟩⟩
  · obtain ⟨v, hfind, hsafe, hb, -⟩ := key _ h
    obtain ⟨_, _, _, _, _, _, hv⟩ := hb (.inr rfl)
    exact ⟨⟨_, v.value, hreflect hfind, hsafety v hsafe, rfl,
      fun levels _ _ h1 h2 => binaryWrapperBody hv _ levels h1 h2⟩⟩
  · obtain ⟨v, hfind, hsafe, -, hu⟩ := key _ h
    obtain ⟨_, _, _, hv⟩ := hu (.inl rfl)
    exact ⟨⟨_, v.value, hreflect hfind, hsafety v hsafe, rfl,
      fun levels _ h1 => unaryWrapperBody hv _ levels h1⟩⟩
  · obtain ⟨v, hfind, hsafe, -, hu⟩ := key _ h
    obtain ⟨_, _, _, hv⟩ := hu (.inr rfl)
    exact ⟨⟨_, v.value, hreflect hfind, hsafety v hsafe, rfl,
      fun levels _ h1 => unaryWrapperBody hv _ levels h1⟩⟩

/-- The names that `Kernel.Environment.isTypeAnnotationWrapper env` accepts are
declared in `env` as identity-like safe definitions. -/
theorem TypeAnnotationWrappers.of_env (env : Environment) :
    TypeAnnotationWrappers env env.isTypeAnnotationWrapper :=
  .of_reflect env env id

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

/-- Translation of a source constant before the kernel has assigned it a
`ConstantInfo` variant. This is used for inductive headers and constructors,
whose types are translated at different environment stages. -/
structure TrSourceConst (env : VEnv) (lparams : List Name)
    (name : Name) (type : Expr) (ci' : VConstVal) : Prop where
  uvars : ci'.uvars = lparams.length
  name : ci'.name = name
  type : TrExprS env lparams [] type ci'.type
  wf : ci'.toVConstant.WF env

/-- Syntactic source-constant translation before its type has been checked in
the header or constructor environment. -/
structure TrSourceConstRaw (env : VEnv) (lparams : List Name)
    (name : Name) (type : Expr) (ci' : VConstVal) : Prop where
  uvars : ci'.uvars = lparams.length
  name : ci'.name = name
  type : TrExprS env lparams [] type ci'.type

theorem TrSourceConst.raw
    {env : VEnv} {lparams : List Name} {constName : Name}
    {type : Expr} {ci' : VConstVal}
    (H : TrSourceConst env lparams constName type ci') :
    TrSourceConstRaw env lparams constName type ci' :=
  ⟨H.uvars, H.name, H.type⟩

/-- Translation of an inductive family before header checking has recovered
the semantic arity and result universe.  Those two fields are deliberately
absent: they are outputs of `checkInductiveTypes`, not assumptions supplied by
the source-translation relation. -/
structure VInductiveTypeSkeleton extends VConstVal where
  ctors : List VConstVal

/-- Metadata-free translation of a complete source inductive declaration. -/
structure VInductDeclSkeleton where
  uvars : Nat
  nparams : Nat
  types : List VInductiveTypeSkeleton
  isUnsafe : Bool

def VInductiveTypeSkeleton.toVInductiveType
    (type : VInductiveTypeSkeleton) (numIndices : Nat)
    (resultLevel : VLevel) : VInductiveType where
  toVConstVal := type.toVConstVal
  numIndices := numIndices
  resultLevel := resultLevel
  ctors := type.ctors

def VInductiveType.toSkeleton
    (type : VInductiveType) : VInductiveTypeSkeleton where
  toVConstVal := type.toVConstVal
  ctors := type.ctors

def VInductDecl.toSkeleton (decl : VInductDecl) : VInductDeclSkeleton where
  uvars := decl.uvars
  nparams := decl.nparams
  types := decl.types.map VInductiveType.toSkeleton
  isUnsafe := decl.isUnsafe

/-- Assemble the abstract declaration from source translations and the
metadata recovered by the executable header traversal.  Requiring an exact
metadata length prevents `List.zipWith` from silently dropping a family
member. -/
def VInductDeclSkeleton.withMetadata (decl : VInductDeclSkeleton)
    (metadata : List (Nat × VLevel)) : Option VInductDecl :=
  if metadata.length = decl.types.length then
    some {
      uvars := decl.uvars
      nparams := decl.nparams
      types := List.zipWith (fun type data =>
        type.toVInductiveType data.1 data.2) decl.types metadata
      isUnsafe := decl.isUnsafe }
  else none

@[simp] theorem VInductiveTypeSkeleton.toVInductiveType_toSkeleton
    (type : VInductiveTypeSkeleton) (numIndices : Nat)
    (resultLevel : VLevel) :
    (type.toVInductiveType numIndices resultLevel).toSkeleton = type := by
  cases type
  rfl

theorem VInductDeclSkeleton.withMetadata_length
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.withMetadata metadata = some materialized) :
    metadata.length = decl.types.length := by
  simp only [VInductDeclSkeleton.withMetadata] at H
  split at H
  · assumption
  · contradiction

theorem VInductDeclSkeleton.withMetadata_fields
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.withMetadata metadata = some materialized) :
    materialized.uvars = decl.uvars ∧
    materialized.nparams = decl.nparams ∧
    materialized.isUnsafe = decl.isUnsafe ∧
    materialized.types.length = decl.types.length := by
  simp only [VInductDeclSkeleton.withMetadata] at H
  split at H
  · next hlength =>
    simp only [Option.some.injEq] at H
    subst materialized
    simp [hlength]
  · contradiction

theorem VInductDeclSkeleton.withMetadata_toSkeleton
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.withMetadata metadata = some materialized) :
    materialized.toSkeleton = decl := by
  have zipErase : ∀ (types : List VInductiveTypeSkeleton)
      (metadata : List (Nat × VLevel)),
      metadata.length = types.length →
      List.zipWith (fun type data =>
        (type.toVInductiveType data.1 data.2).toSkeleton)
        types metadata = types := by
    intro types metadata hlength
    induction types generalizing metadata with
    | nil => simp at hlength; simp
    | cons type types ih =>
      cases metadata with
      | nil => simp at hlength
      | cons data metadata =>
        have hlength' : metadata.length = types.length := by
          simp only [List.length_cons] at hlength
          omega
        simp only [List.zipWith_cons_cons,
          VInductiveTypeSkeleton.toVInductiveType_toSkeleton]
        congr 1
        simpa only [VInductiveTypeSkeleton.toVInductiveType_toSkeleton]
          using ih metadata hlength'
  simp only [VInductDeclSkeleton.withMetadata] at H
  split at H
  · next hlength =>
    simp only [Option.some.injEq] at H
    subst materialized
    cases decl
    simp only [VInductDecl.toSkeleton, List.map_zipWith]
    rw [zipErase _ _ (by simpa using hlength)]
  · simp at H

theorem VInductDeclSkeleton.withMetadata_typeAt
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.withMetadata metadata = some materialized)
    (hi : i < decl.types.length) :
    ∃ data,
      metadata[i]? = some data ∧
      materialized.types[i]? = some
        (decl.types[i].toVInductiveType data.1 data.2) := by
  have hlength := VInductDeclSkeleton.withMetadata_length H
  have himetadata : i < metadata.length := by omega
  refine ⟨metadata[i], by simp [himetadata], ?_⟩
  simp only [VInductDeclSkeleton.withMetadata] at H
  split at H
  · simp only [Option.some.injEq] at H
    subst materialized
    rw [List.getElem?_zipWith]
    simp [hi, himetadata]
  · contradiction

/-- Transport a per-family relation along `withMetadata`.  A translation
that holds for a skeleton family at every choice of arity metadata holds for
the materialized family.  This is how metadata-free translations are stated:
`TrInductiveType` and `TrInductiveTypeHeaders` read only the header constant
and the constructor list, so a skeleton translation is the relation at
`target.toVInductiveType numIndices resultLevel` for all metadata. -/
theorem VInductDeclSkeleton.withMetadata_forall₂
    {α : Type _} {R : α → VInductiveType → Prop} {sources : List α}
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (Hmaterialize : decl.withMetadata metadata = some materialized)
    (H : List.Forall₂ (fun source target => ∀ numIndices resultLevel,
      R source (target.toVInductiveType numIndices resultLevel))
      sources decl.types) :
    List.Forall₂ R sources materialized.types := by
  have go : ∀ {sources : List α} {types : List VInductiveTypeSkeleton}
      (metadata : List (Nat × VLevel)), metadata.length = types.length →
      List.Forall₂ (fun source target => ∀ numIndices resultLevel,
        R source (target.toVInductiveType numIndices resultLevel))
        sources types →
      List.Forall₂ R sources (List.zipWith (fun type data =>
        type.toVInductiveType data.1 data.2) types metadata) := by
    intro sources types metadata hlength H
    induction H generalizing metadata with
    | nil => exact .nil
    | cons Hhead _ ih =>
      cases metadata with
      | nil => simp at hlength
      | cons data metadata =>
        simp only [List.length_cons] at hlength
        exact .cons (Hhead data.1 data.2) (ih metadata (by omega))
  have hlength := VInductDeclSkeleton.withMetadata_length Hmaterialize
  simp only [VInductDeclSkeleton.withMetadata] at Hmaterialize
  split at Hmaterialize
  · simp only [Option.some.injEq] at Hmaterialize
    subst materialized
    exact go metadata hlength H
  · contradiction

def VInductDeclSkeleton.typeConstants
    (decl : VInductDeclSkeleton) : List VConstVal :=
  decl.types.map VInductiveTypeSkeleton.toVConstVal

def VInductDeclSkeleton.constructorConstants
    (decl : VInductDeclSkeleton) : List VConstVal :=
  decl.types.flatMap VInductiveTypeSkeleton.ctors

@[simp] theorem VInductDecl.toSkeleton_typeConstants
    (decl : VInductDecl) :
    decl.toSkeleton.typeConstants = decl.typeConstants := by
  simp [VInductDecl.toSkeleton, VInductDeclSkeleton.typeConstants,
    VInductDecl.typeConstants, VInductiveType.toSkeleton]

@[simp] theorem VInductDecl.toSkeleton_constructorConstants
    (decl : VInductDecl) :
    decl.toSkeleton.constructorConstants = decl.constructorConstants := by
  cases decl with
  | mk uvars nparams types isUnsafe =>
    induction types with
    | nil => rfl
    | cons type types ih =>
      have ih' :
          List.flatMap VInductiveTypeSkeleton.ctors
              (List.map VInductiveType.toSkeleton types) =
            List.flatMap VInductiveType.ctors types := by
        simpa [VInductDecl.toSkeleton,
          VInductDeclSkeleton.constructorConstants,
          VInductDecl.constructorConstants] using ih
      simp [VInductDecl.toSkeleton,
        VInductDeclSkeleton.constructorConstants,
        VInductDecl.constructorConstants, VInductiveType.toSkeleton, ih']

/-- Source translation of one inductive family: its header and constructor
types.  Only the header constant and the constructor list are read, so a
metadata-free family `target : VInductiveTypeSkeleton` is translated by
`∀ numIndices resultLevel, TrInductiveType env envTypes lparams type
(target.toVInductiveType numIndices resultLevel)`; see
`VInductDeclSkeleton.withMetadata_forall₂`. -/
structure TrInductiveType (env envTypes : VEnv) (lparams : List Name)
    (type : InductiveType) (type' : VInductiveType) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' => TrSourceConst envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

/-- Header checking retains raw constructor correspondence, but deliberately
does not claim constructor well-formedness before the mutual headers have
been installed.  Metadata-free families are handled as for
`TrInductiveType`. -/
structure TrInductiveTypeHeaders (env envTypes : VEnv) (lparams : List Name)
    (type : InductiveType) (type' : VInductiveType) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' =>
      TrSourceConstRaw envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

/-- Translation of the source (pre-lowering) inductive declaration. The
constructor relation deliberately uses `envTypes`, obtained by installing all
translated mutual headers, so an ill-typed nested parameter cannot disappear
behind auxiliary declarations. -/
def TrInductDecl (env : VEnv) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧
  decl.uvars = lparams.length ∧
  decl.nparams = nparams ∧
  decl.isUnsafe = isUnsafe ∧
  ∃ envTypes envCtors,
    env.addConstVals decl.typeConstants = some envTypes ∧
    envTypes.addConstVals decl.constructorConstants = some envCtors ∧
    List.Forall₂ (TrInductiveType env envTypes lparams) types decl.types

/-- Source translation without assuming the aggregate `SourceWF` judgment.
The pointwise `TrSourceConst` translations still retain the independently checked
typing of every source header and constructor; only block nonemptiness and
global name uniqueness are intentionally absent. -/
structure TrInductDeclCore (env : VEnv) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDecl) (envTypes envCtors : VEnv) : Prop where
  uvars : decl.uvars = lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  typesAdded : env.addConstVals decl.typeConstants = some envTypes
  ctorsAdded : envTypes.addConstVals decl.constructorConstants = some envCtors
  types : List.Forall₂ (TrInductiveType env envTypes lparams)
    types decl.types

/-- Header-phase translation in the exact form available after
`checkInductiveTypes` and mutual header installation. Constructor translation
is intentionally absent until `checkConstructors` has run in `envTypes`. -/
structure TrInductDeclHeaders (env : VEnv) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDecl) (envTypes : VEnv) : Prop where
  uvars : decl.uvars = lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  typesAdded : env.addConstVals decl.typeConstants = some envTypes
  types : List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
    types decl.types

/-- Constructor-phase translation produced after all mutual headers are
installed. It records both pointwise source typing and the exact abstract
constructor environment. -/
structure TrInductDeclConstructors (envTypes : VEnv) (lparams : List Name)
    (types : List InductiveType) (decl : VInductDecl)
    (envCtors : VEnv) : Prop where
  ctorsAdded : envTypes.addConstVals decl.constructorConstants = some envCtors
  types : List.Forall₂
    (fun source target => List.Forall₂
      (fun ctor ctor' =>
        TrSourceConst envTypes lparams ctor.name ctor.type ctor')
      source.ctors target.ctors)
    types decl.types

theorem TrInductDecl.sourceWF
    (H : TrInductDecl env lparams nparams types isUnsafe decl) : decl.SourceWF env :=
  H.1

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

/-- The step an abstract environment takes when `ci`, modelled by `ci'`, is added.

At safety levels where the declaration is visible the constant is added; where it is not, the
environment is unchanged, matching `TrEnv'.ignore`. Stating this rather than just `venv ≤ venv'`
is what lets a caller see *which* constant a step added. -/
def VEnv.AddConst (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VConstant) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    TrConstant safety venv ci ci' ∧ ci'.WF venv ∧ venv.addConst ci.name ci' = some venv'
  else
    venv' = venv

theorem VEnv.AddConst.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddConst venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddConst at H; split at H
  · exact addConst_le H.2.2
  · exact H ▸ VEnv.LE.rfl

/-- As `VEnv.AddConst`, for a definition: the constant is added and then its defining equation,
matching `TrEnv'.defn`. -/
def VEnv.AddDef (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VDefVal) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    ∃ base, TrDefVal safety venv ci ci' ∧ ci'.WF venv ∧
      venv.addConst ci.name ci'.toVConstant = some base ∧
      venv' = base.addDefEq ci'.toDefEq
  else
    venv' = venv

theorem VEnv.AddDef.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddDef venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddDef at H; split at H
  · obtain ⟨base, _, _, hadd, rfl⟩ := H
    exact (addConst_le hadd).trans (VEnv.addDefEq_le ..)
  · exact H ▸ VEnv.LE.rfl

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H

/-- Exact kernel metadata for one constructor in an abstract inductive
family installed by the current declaration.  This prevents a flat constant
lookup from being mistaken for membership in an inductive declaration. -/
structure CtorInfoAlignment
    (C : ConstMap) (decl : VInductDecl) (familyIdx ctorIdx : Nat)
    (familyInfo : InductiveVal) where
  familyIdx_lt : familyIdx < decl.types.length
  ctorIdx_lt : ctorIdx < decl.types[familyIdx].ctors.length
  familyInfo_ctorIdx_lt : ctorIdx < familyInfo.ctors.length
  info : ConstructorVal
  name : familyInfo.ctors[ctorIdx] =
    decl.types[familyIdx].ctors[ctorIdx].name
  lookup : C.find? familyInfo.ctors[ctorIdx] = some (.ctorInfo info)
  induct : info.induct = familyInfo.name
  cidx : info.cidx = ctorIdx
  numParams : info.numParams = decl.nparams
  /-- The projection field count is the exact executable telescope arity
  after removing the independently aligned common parameters. -/
  numFields : info.numFields =
    AddInductive.constructorArity info.type - decl.nparams
  /-- The executable field count agrees with the syntactic forall arity of the
  abstract constructor type: the constructor check walks syntactic binders and
  requires a constant-headed codomain, which translation preserves. -/
  numFields_forallArity : info.numFields =
    (decl.types[familyIdx].ctors[ctorIdx]).type.forallArity - decl.nparams
  levelParamsExact : info.levelParams = familyInfo.levelParams
  levelParams : info.levelParams.length = decl.uvars
  isUnsafe : info.isUnsafe = decl.isUnsafe

/-- Exact mutual-family metadata installed by one abstract declaration. -/
structure InductInfoAlignment
    (C : ConstMap) (decl : VInductDecl) (familyIdx : Nat)
    (familyInfo : InductiveVal) : Prop where
  familyIdx_lt : familyIdx < decl.types.length
  name : familyInfo.name = decl.types[familyIdx].name
  lookup : C.find? familyInfo.name = some (.inductInfo familyInfo)
  all : familyInfo.all = decl.types.map (fun family => family.name)
  levelParams : familyInfo.levelParams.length = decl.uvars
  numParams : familyInfo.numParams = decl.nparams
  numIndices : familyInfo.numIndices = decl.types[familyIdx].numIndices
  constructors : familyInfo.ctors.length =
    decl.types[familyIdx].ctors.length
  isUnsafe : familyInfo.isUnsafe = decl.isUnsafe
  constructor : ∀ ctorIdx
    (_hctor : ctorIdx < decl.types[familyIdx].ctors.length),
    Nonempty (CtorInfoAlignment C decl familyIdx ctorIdx
      familyInfo)

/-- Every inductive header visible after an inductive installation either
already existed or is one exact family of the declaration just installed. -/
def InductInfosFromDecl
    (source target : ConstMap) (decl : VInductDecl) : Prop :=
  ∀ familyName familyInfo,
    target.find? familyName = some (.inductInfo familyInfo) →
    source.find? familyName = some (.inductInfo familyInfo) ∨
      ∃ familyIdx, familyName = familyInfo.name ∧
        Nonempty (InductInfoAlignment target decl familyIdx familyInfo)

def CtorInfoAlignment.rebase
    (H : CtorInfoAlignment source decl familyIdx ctorIdx
      familyInfo)
    (hpreserves : ∀ {name ci}, source.find? name = some ci →
      target.find? name = some ci) :
    CtorInfoAlignment target decl familyIdx ctorIdx familyInfo :=
  { H with lookup := hpreserves H.lookup }

theorem InductInfoAlignment.rebase
    (H : InductInfoAlignment source decl familyIdx familyInfo)
    (hfamily : target.find? familyInfo.name = some (.inductInfo familyInfo))
    (hpreserves : ∀ {name ci}, source.find? name = some ci →
      target.find? name = some ci) :
    InductInfoAlignment target decl familyIdx familyInfo where
  familyIdx_lt := H.familyIdx_lt
  name := H.name
  lookup := hfamily
  all := H.all
  levelParams := H.levelParams
  numParams := H.numParams
  numIndices := H.numIndices
  constructors := H.constructors
  isUnsafe := H.isUnsafe
  constructor ctorIdx hctor := by
    rcases H.constructor ctorIdx hctor with ⟨C⟩
    exact ⟨C.rebase hpreserves⟩

/-- Exact agreement between a concrete singleton inductive family and the
primitive-projection entry available in its abstract checking environment.
This is the persistent invariant consumed by projection inference: it records
precisely the executable metadata read by `inferProj` and `reduceProjCore`
(parameter and index counts, universe arity, the constructor's identity and
field count) against the registered abstract entry, and the abstract
constants named by that entry. -/
structure ProjectionRegistryAlignmentAt
    (C : ConstMap) (env : VEnv) (familyName : Name)
    (familyInfo : InductiveVal) (constructorName : Name) where
  info : VProjectionInfo
  projection : env.projections familyName info
  ctorName : info.ctorName = constructorName
  uvars : familyInfo.levelParams.length = info.uvars
  nparams : familyInfo.numParams = info.nparams
  nindices : familyInfo.numIndices = info.nindices
  constructorInfo : ConstructorVal
  constructor_lookup : C.find? constructorName = some (.ctorInfo constructorInfo)
  constructor_induct : constructorInfo.induct = familyName
  constructor_levelParams : constructorInfo.levelParams = familyInfo.levelParams
  constructor_numParams : constructorInfo.numParams = familyInfo.numParams
  constructor_isUnsafe : constructorInfo.isUnsafe = familyInfo.isUnsafe
  constructor_numFields : constructorInfo.numFields = info.numFields
  /-- The field count is the syntactic arity of the stored constructor type beyond the
  parameters (`AddInductive.constructorInfo`); the projection walk reads it to know that the
  stored type is a syntactic `forallE` spine up to the selected field. -/
  constructor_arity : constructorInfo.numFields =
    AddInductive.constructorArity constructorInfo.type - constructorInfo.numParams
  familyType : VExpr
  family_lookup : env.constants familyName = some ⟨info.uvars, familyType⟩
  constructor_abstract :
    env.constants constructorName = some ⟨info.uvars, info.ctorType⟩

/-- Every executable singleton-family lookup that is visible at this safety
level, whose listed constructor is present and names the family as its
owner, has matching primitive-projection metadata in the abstract model. -/
def ProjectionRegistryCoherent
    (safety : DefinitionSafety) (C : ConstMap) (env : VEnv) : Prop :=
  ∀ familyName familyInfo constructorName constructorInfo,
    C.find? familyName = some (.inductInfo familyInfo) →
    safety ≤ (ConstantInfo.inductInfo familyInfo).safety →
    familyInfo.ctors = [constructorName] →
    C.find? constructorName = some (.ctorInfo constructorInfo) →
    constructorInfo.induct = familyName →
    Nonempty (ProjectionRegistryAlignmentAt C env familyName familyInfo
      constructorName)

/-! ### Inserting a block of constants into the constant map

`insertConsts` is the `SMap` fold the kernel performs for every constant of a block.
Its lemmas need only well-formedness of the starting map, freshness of the block's names
in it and their duplicate-freedom. -/

/-- Insert a block of constant infos into the constant map, keyed by name. -/
def insertConsts (C : ConstMap) (cis : List ConstantInfo) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name ci) C

theorem insertConsts_cons {C : ConstMap} {ci : ConstantInfo} {cis : List ConstantInfo} :
    insertConsts C (ci :: cis) = insertConsts (C.insert ci.name ci) cis := rfl

/-- Fresh, duplicate-free names stay fresh after inserting the head of the block. -/
theorem insertConsts_fresh_tail {C : ConstMap} {ci : ConstantInfo} {cis : List ConstantInfo}
    (wf : C.map₂.WF) (hfr : ∀ d ∈ ci :: cis, C.find? d.name = none)
    (hnd : ((ci :: cis).map (·.name)).Nodup) :
    ∀ d ∈ cis, (C.insert ci.name ci).find? d.name = none := by
  rw [List.map_cons, List.nodup_cons] at hnd
  intro d hd
  exact SMap.find?_insert_none wf (fun e => hnd.1 (e ▸ List.mem_map_of_mem hd)) (hfr d (.tail _ hd))

theorem insertConsts_wf : ∀ {cis : List ConstantInfo} {C : ConstMap}, C.WF →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup → (insertConsts C cis).WF
  | [], _, hC, _, _ => hC
  | ci :: cis, C, hC, hfr, hnd => by
    rw [insertConsts_cons]
    refine insertConsts_wf (hC.insert _ _ (hfr _ (.head _)))
      (insertConsts_fresh_tail hC.map₂ hfr hnd) ?_
    rw [List.map_cons, List.nodup_cons] at hnd; exact hnd.2

theorem insertConsts_find?_mono {cis : List ConstantInfo} {C : ConstMap} {x v} (wf : C.map₂.WF)
    (hne : ∀ ci ∈ cis, ci.name ≠ x) (h : C.find? x = some v) :
    (insertConsts C cis).find? x = some v := by
  unfold insertConsts
  exact SMap.insertList_find?_mono (nm := (·.name)) (val := id) wf hne h

/-- A constant resolvable before inserting a block of fresh names is still resolvable, to
the same value, afterwards. -/
theorem insertConsts_find?_mono_of_fresh {cis : List ConstantInfo} {C : ConstMap} {x v}
    (wf : C.map₂.WF) (hfr : ∀ ci ∈ cis, C.find? ci.name = none) (h : C.find? x = some v) :
    (insertConsts C cis).find? x = some v :=
  insertConsts_find?_mono wf (fun ci hci e => by have := hfr ci hci; rw [e, h] at this; cases this) h

theorem insertConsts_find?_none : ∀ {cis : List ConstantInfo} {C : ConstMap} {x}, C.map₂.WF →
    (∀ ci ∈ cis, ci.name ≠ x) → C.find? x = none → (insertConsts C cis).find? x = none
  | [], _, _, _, _, h => h
  | ci :: cis, C, x, wf, hne, h => by
    rw [insertConsts_cons]
    exact insertConsts_find?_none (SMap.insert_map₂ wf) (fun d hd => hne d (.tail _ hd))
      (SMap.find?_insert_none wf (hne ci (.head _)) h)

/-- A constant resolvable after inserting a block was resolvable before, or is one of the
block's constants under its own name. -/
theorem insertConsts_find? : ∀ {cis : List ConstantInfo} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertConsts C cis).find? name = some ci →
    C.find? name = some ci ∨ ci ∈ cis ∧ ci.name = name
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    rw [insertConsts_cons] at h
    have hnd' := hnd; rw [List.map_cons, List.nodup_cons] at hnd'
    rcases insertConsts_find? (hC.insert _ _ (hfr _ (.head _)))
        (insertConsts_fresh_tail hC.map₂ hfr hnd) hnd'.2 h with h | ⟨he, h1⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h; exact .inr ⟨.head _, by simpa using hb⟩
      · exact .inl h
    · exact .inr ⟨.tail _ he, h1⟩

/-- Every constant of an inserted block resolves to itself under its name. -/
theorem insertConsts_find?_self : ∀ {cis : List ConstantInfo} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    ∀ ci ∈ cis, (insertConsts C cis).find? ci.name = some ci
  | [], _, _, _, _, _, h => by cases h
  | d :: ds, C, hC, hfr, hnd, ci, hci => by
    rw [insertConsts_cons]
    have hnd' := hnd; rw [List.map_cons, List.nodup_cons] at hnd'
    rcases List.mem_cons.1 hci with rfl | hci'
    · refine insertConsts_find?_mono (hC.insert _ _ (hfr _ (.head _))).map₂
        (fun e he heq => hnd'.1 (heq ▸ List.mem_map_of_mem he)) ?_
      rw [hC.find?_insert, if_pos (by simp)]
    · exact insertConsts_find?_self (hC.insert _ _ (hfr _ (.head _)))
        (insertConsts_fresh_tail hC.map₂ hfr hnd) hnd'.2 ci hci'

/-! ### Translation of an inductive block -/

/-- Translation of one type former with its constructors, at safety level `safety`. The
type former's `inductInfo` translates in the environment before the block (`env₁`); the
constructors' `ctorInfo`s in the environment holding the type formers (`envT`), where their
types are meaningful, and their `numParams + numFields` is the Π-arity of the model type,
which is how the kernel's `nfields` reaches the ι bookkeeping (`AddInduct.ctor_find`).
`ival.ctors` lists exactly the translated constructors. -/
structure TrIndType (safety : DefinitionSafety) (env₁ envT : VEnv) (ival : InductiveVal)
    (cvals : List ConstructorVal) (t : VInductiveType) : Prop where
  tr : TrConstVal safety env₁ (.inductInfo ival) t.toVConstVal
  ctor_names : ival.ctors = cvals.map (·.name)
  ctors : List.Forall₂ (fun cval c => TrConstVal safety envT (.ctorInfo cval) c ∧
    cval.numParams + cval.numFields = c.type.piArity) cvals t.ctors

/-- Translation of one recursor, at safety level `safety`: its `recInfo` in the environment
holding the type formers and constructors (`envC`), the telescope split and `k` flag copied,
and its rules matched one-to-one with the model's, each firing on the same constructor
(whose parameter count is read off its `ctorInfo` in the final map `m₂`, so that the
auxiliary recursors of nested blocks, which fire on older constructors, are covered) with
the same field count and a reduct translating in the environment holding the recursors
(`envR`, since reducts mention the recursors of the block). -/
structure TrRecursor (safety : DefinitionSafety) (envC envR : VEnv) (m₂ : ConstMap)
    (rval : RecursorVal) (r : VRecursor) : Prop where
  tr : TrConstVal safety envC (.recInfo rval) r.toVConstVal
  all : r.all = rval.all
  numParams : r.numParams = rval.numParams
  numMotives : r.numMotives = rval.numMotives
  numMinors : r.numMinors = rval.numMinors
  numIndices : r.numIndices = rval.numIndices
  k : r.k = rval.k
  rules : List.Forall₂ (fun rule ru => ru.ctor = rule.ctor ∧ ru.nfields = rule.nfields ∧
    (∃ cval : ConstructorVal,
      m₂.find? rule.ctor = some (.ctorInfo cval) ∧ ru.ctorParams = cval.numParams) ∧
    TrExprS envR rval.levelParams [] rule.rhs ru.rhs) rval.rules r.rules

/-- The constants an inductive block adds to the constant map, by kind: all type formers,
all constructors (in block order), all recursors. This is the model's stage order
(`VInductDecl.consts`); the kernel inserts them in this order for a non-nested block
(`Inductive/Add.lean`, `run`) and type by type — each type former, its constructors, its
recursor, then the auxiliary recursors — for a nested one (`Environment.addInductive`), so
`AddInduct` records the actual insertion order separately (`order`). -/
def AddInduct.consts (ivals : List (InductiveVal × List ConstructorVal))
    (rvals : List RecursorVal) : List ConstantInfo :=
  ivals.map (.inductInfo ·.1) ++ ivals.flatMap (·.2.map .ctorInfo) ++ rvals.map .recInfo

/-- Refinement witness that translating an inductive declaration extends the constant
map `m₁ → m₂` and model environment `env₁ → env₂` coherently, at safety level `safety`,
in the `AddQuot`/`TrDefBlock` idiom: it records the kernel-side data (`ivals`, `rvals`),
the four successful stages of `VEnv.addInduct` (`stT`…`stP`, with their intermediate
environments), the translation of each type former, constructor and recursor at the
stage where the kernel checks it (`types`, `recs`), freshness of every inserted name in
`m₁`, and that `m₂` is the insertion of the block's constants in the order the kernel
inserted them (`order`, a permutation of `consts`). Everything else — `env_eq`, `wf`,
`find?_mono`, `value_find`, `rec_find`, `rec_reg`, `ctor_find` — is derived below. -/
structure AddInduct (safety : DefinitionSafety) (m₁ : ConstMap) (env₁ : VEnv)
    (decl : VInductDecl) (m₂ : ConstMap) (env₂ : VEnv) where
  ivals : List (InductiveVal × List ConstructorVal)
  rvals : List RecursorVal
  envT : VEnv
  envC : VEnv
  envR : VEnv
  stT : decl.addTypes env₁ = some envT
  stC : decl.addCtors envT = some envC
  /-- The recursors are added after the (total) projection stage `addProjs`. -/
  stR : decl.addRecs (decl.addProjs envC) = some envR
  stP : decl.addRules envR = some env₂
  types : List.Forall₂ (fun iv t => TrIndType safety env₁ envT iv.1 iv.2 t) ivals decl.types
  recs : List.Forall₂ (TrRecursor safety (decl.addProjs envC) envR m₂) rvals decl.recs  -- WAVE 2 rec COMPAT
  /-- The block's constants in the order the kernel inserted them. -/
  order : List ConstantInfo
  order_perm : order.Perm (AddInduct.consts ivals rvals)
  fresh : ∀ ci ∈ AddInduct.consts ivals rvals, m₁.find? ci.name = none
  map_eq : m₂ = insertConsts m₁ order

namespace AddInduct

variable {safety : DefinitionSafety} {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {decl : VInductDecl}

/-- The projection-stage environment: the constructor stage with the block's projection
entries registered. -/
def envP (H : AddInduct safety m₁ env₁ decl m₂ env₂) : VEnv := decl.addProjs H.envC

theorem addTypesCtors (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    decl.addTypesCtors env₁ = some H.envC := by
  rw [VInductDecl.addTypesCtors, H.stT]; simp [H.stC]

theorem addTypesCtorsProjs (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    decl.addTypesCtorsProjs env₁ = some H.envP :=
  VEnv.addTypesCtorsProjs_eq_some H.addTypesCtors

theorem addTypesCtorsProjsRecs (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    decl.addTypesCtorsProjsRecs env₁ = some H.envR := by
  rw [VInductDecl.addTypesCtorsProjsRecs, H.addTypesCtorsProjs]; exact H.stR

theorem env_eq (H : AddInduct safety m₁ env₁ decl m₂ env₂) : env₁.addInduct decl = some env₂ := by
  rw [VEnv.addInduct, H.addTypesCtorsProjsRecs]; exact H.stP

theorem le (H : AddInduct safety m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := VEnv.addInduct_le H.env_eq
theorem leR (H : AddInduct safety m₁ env₁ decl m₂ env₂) : H.envR ≤ env₂ := VEnv.addRules_le H.stP

/-- Membership in the block's constants, by kind. -/
theorem mem_consts {ivals : List (InductiveVal × List ConstructorVal)} {rvals : List RecursorVal}
    {ci : ConstantInfo} : ci ∈ consts ivals rvals ↔
      (∃ iv ∈ ivals, ci = .inductInfo iv.1) ∨
      (∃ iv ∈ ivals, ∃ cval ∈ iv.2, ci = .ctorInfo cval) ∨
      (∃ rval ∈ rvals, ci = .recInfo rval) := by
  simp only [consts, List.mem_append, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ((⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cval, hcval, rfl⟩) | ⟨rval, hrval, rfl⟩)
    · exact .inl ⟨iv, hiv, rfl⟩
    · exact .inr (.inl ⟨iv, hiv, cval, hcval, rfl⟩)
    · exact .inr (.inr ⟨rval, hrval, rfl⟩)
  · rintro (⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cval, hcval, rfl⟩ | ⟨rval, hrval, rfl⟩)
    · exact .inl (.inl ⟨iv, hiv, rfl⟩)
    · exact .inl (.inr ⟨iv, hiv, cval, hcval, rfl⟩)
    · exact .inr ⟨rval, hrval, rfl⟩

/-- The block's constants carry no value, in particular none for δ-reduction. -/
theorem novalue {ivals : List (InductiveVal × List ConstructorVal)} {rvals : List RecursorVal} :
    ∀ ci ∈ consts ivals rvals, ci.value? = none ∧ ci.deltaValue? = none := by
  intro ci hci
  rcases mem_consts.1 hci with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem types_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (H.ivals.map (·.1.name)) = decl.types.map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.tr.2) H.types

theorem ctors_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ((H.ivals.flatMap (·.2)).map (·.name)) = (decl.types.flatMap (·.ctors)).map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.1.2)
    (List.Forall₂.flatMap (fun _ _ h => h.ctors) H.types)

theorem recs_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (H.rvals.map (·.name)) = decl.recs.map (·.name) :=
  List.Forall₂.map_eq (fun _ _ h => h.tr.2) H.recs

/-- The names of the block's constants, in insertion order. -/
theorem consts_names (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (consts H.ivals H.rvals).map (·.name) =
      decl.types.map (·.name) ++ (decl.types.flatMap (·.ctors)).map (·.name) ++
        decl.recs.map (·.name) := by
  rw [← H.types_names, ← H.ctors_names, ← H.recs_names]
  simp only [consts, List.map_append, List.map_map, List.map_flatMap, Function.comp_def]
  rfl

/-- The names of the block's constants are distinct: each stage's names are distinct
(the `addConst` folds succeed) and a later stage's names are fresh in the environment
where the earlier stages' names are already bound. -/
theorem names_nodup (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ((consts H.ivals H.rvals).map (·.name)).Nodup := by
  rw [H.consts_names, List.nodup_append, List.nodup_append]
  refine ⟨⟨VEnv.addTypes_nodup H.stT, VEnv.addCtors_nodup H.stC, fun a ha b hb hab => ?_⟩,
    VEnv.addRecs_nodup H.stR, fun a ha b hb hab => ?_⟩
  · subst hab
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    obtain ⟨c, hc, hcn⟩ := List.mem_map.1 hb
    obtain ⟨t', ht', hc'⟩ := List.mem_flatMap.1 hc
    have h1 := VEnv.addTypes_find H.stT t ht
    have h2 := VEnv.addCtors_fresh H.stC t' ht' c hc'
    rw [hcn, h1] at h2; cases h2
  · subst hab
    obtain ⟨r, hr, hrn⟩ := List.mem_map.1 hb
    have h2 := VEnv.addRecs_fresh H.stR r hr
    rw [VEnv.addProjs_constants, hrn] at h2
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
      have h1 := (VEnv.addCtors_le H.stC).constants (VEnv.addTypes_find H.stT t ht)
      rw [h1] at h2; cases h2
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
      obtain ⟨t', ht', hc'⟩ := List.mem_flatMap.1 hc
      have h1 := VEnv.addCtors_find H.stC t' ht' c hc'
      rw [h1] at h2; cases h2

/-- Freshness, in the kernel's insertion order. -/
theorem order_fresh (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ∀ ci ∈ H.order, m₁.find? ci.name = none :=
  fun ci h => H.fresh ci (H.order_perm.mem_iff.1 h)

/-- Distinctness of the names, in the kernel's insertion order. -/
theorem order_nodup (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    (H.order.map (·.name)).Nodup :=
  (H.order_perm.map _).nodup_iff.2 H.names_nodup

/-- Adding an inductive block preserves constant-map well-formedness. -/
theorem wf (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF) : m₂.WF :=
  H.map_eq ▸ insertConsts_wf wf H.order_fresh H.order_nodup

/-- A constant resolvable before adding an inductive block is still resolvable, to the
same value, afterwards: every name the block inserts is fresh in `m₁`. -/
theorem find?_mono {x v} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₁.find? x = some v) : m₂.find? x = some v := by
  rw [H.map_eq]; exact insertConsts_find?_mono_of_fresh wf.map₂ H.order_fresh h

/-- A constant resolvable after adding an inductive block was resolvable before, or is
one of the block's constants under its own name. -/
theorem find? {name ci} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? name = some ci) :
    m₁.find? name = some ci ∨ ci ∈ consts H.ivals H.rvals ∧ ci.name = name := by
  rw [H.map_eq] at h
  rcases insertConsts_find? wf H.order_fresh H.order_nodup h with h | ⟨hci, hn⟩
  · exact .inl h
  · exact .inr ⟨H.order_perm.mem_iff.1 hci, hn⟩

/-- Every constant of the block resolves to itself in `m₂`. -/
theorem find?_self {ci} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (hci : ci ∈ consts H.ivals H.rvals) : m₂.find? ci.name = some ci := by
  rw [H.map_eq]
  exact insertConsts_find?_self wf H.order_fresh H.order_nodup ci (H.order_perm.mem_iff.2 hci)

/-- A constant with a δ-value resolvable after the block was resolvable before: the
block's constants have none. -/
theorem value_find {name : Name} {ci : ConstantInfo} {v : Expr}
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? name = some ci) (hv : ci.deltaValue? = some v) : m₁.find? name = some ci := by
  rcases H.find? wf h with h | ⟨hci, _⟩
  · exact h
  · rw [(novalue ci hci).2] at hv; cases hv

/-- A kernel recursor resolvable after the block was resolvable before, or is one of the
block's recursors: then some `r ∈ decl.recs` carries its name and telescope split, and
every kernel rule has a model rule with the same constructor (of the parameter count read
off its `ctorInfo` in `m₂`), the same field count, and a closed reduct translating the
kernel rule's reduct. This is what ties a kernel recursor lookup to `VEnv.addInduct_pat`. -/
theorem rec_find {recName : Name} {rval : RecursorVal}
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? recName = some (.recInfo rval)) :
    m₁.find? recName = some (.recInfo rval) ∨
    ∃ r ∈ decl.recs,
      r.name = recName ∧ r.getMajorIdx = rval.getMajorIdx ∧ r.numParams = rval.numParams ∧
      r.numMotives = rval.numMotives ∧ r.numMinors = rval.numMinors ∧
      r.numIndices = rval.numIndices ∧
      ∀ rule ∈ rval.rules, ∃ ru ∈ r.rules,
        ru.ctor = rule.ctor ∧ ru.nfields = rule.nfields ∧
        (∃ cval : ConstructorVal,
          m₂.find? rule.ctor = some (.ctorInfo cval) ∧ ru.ctorParams = cval.numParams) ∧
        ru.rhs.Closed ∧ TrExprS env₂ rval.levelParams [] rule.rhs ru.rhs := by
  rcases H.find? wf h with h | ⟨hci, hname⟩
  · exact .inl h
  · right
    rcases mem_consts.1 hci with ⟨_, _, h'⟩ | ⟨_, _, _, _, h'⟩ | ⟨_, hrval, h'⟩ <;> cases h'
    obtain ⟨r, hr, htr⟩ := H.recs.forall_exists_l _ hrval
    refine ⟨r, hr, htr.tr.2.symm.trans hname, ?_, htr.numParams, htr.numMotives,
      htr.numMinors, htr.numIndices, fun rule hrule => ?_⟩
    · simp only [VRecursor.getMajorIdx, RecursorVal.getMajorIdx, htr.numParams, htr.numMotives,
        htr.numMinors, htr.numIndices]
    · obtain ⟨ru, hru, h1, h2, h3, h4⟩ := htr.rules.forall_exists_l rule hrule
      exact ⟨ru, hru, h1, h2, h3, VEnv.addRules_closed H.stP r hr ru hru, h4.mono H.leR⟩

/-- The theory→kernel dual of `rec_find`: each `r ∈ decl.recs` is registered in `m₂` as a
kernel `recInfo` under `r.name`, with the same telescope split, and each of its rules is
found (keyed by constructor, uniquely by `VInductDecl.WF.rules_nodup`) among the kernel
recursor's rules, with the same field count, the constructor's parameter count, and a
reduct translating the kernel rule's. -/
theorem rec_reg {r : VRecursor} (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (hwf : decl.WF env₁) (hr : r ∈ decl.recs) :
    ∃ rval : RecursorVal,
      m₂.find? r.name = some (.recInfo rval) ∧
      r.getMajorIdx = rval.getMajorIdx ∧ r.numParams = rval.numParams ∧
      r.numMotives = rval.numMotives ∧ r.numMinors = rval.numMinors ∧
      r.numIndices = rval.numIndices ∧
      ∀ ru ∈ r.rules, ∃ rule : RecursorRule,
        rval.rules.find? (·.ctor == ru.ctor) = some rule ∧ ru.nfields = rule.nfields ∧
        (∃ cval : ConstructorVal,
          m₂.find? ru.ctor = some (.ctorInfo cval) ∧ ru.ctorParams = cval.numParams) ∧
        TrExprS env₂ rval.levelParams [] rule.rhs ru.rhs := by
  obtain ⟨rval, hrval, htr⟩ := H.recs.forall_exists_r r hr
  have hmem : ConstantInfo.recInfo rval ∈ consts H.ivals H.rvals :=
    mem_consts.2 (.inr (.inr ⟨rval, hrval, rfl⟩))
  refine ⟨rval, ?_, ?_, htr.numParams, htr.numMotives, htr.numMinors, htr.numIndices,
    fun ru hru => ?_⟩
  · have := H.find?_self wf hmem; rwa [htr.tr.2] at this
  · simp only [VRecursor.getMajorIdx, RecursorVal.getMajorIdx, htr.numParams, htr.numMotives,
      htr.numMinors, htr.numIndices]
  · obtain ⟨rule, hrule, h1, h2, h3, h4⟩ := htr.rules.forall_exists_r ru hru
    have hnd : (rval.rules.map (·.ctor)).Nodup := by
      rw [List.Forall₂.map_eq (fun _ _ h => h.1.symm) htr.rules]; exact hwf.rules_nodup r hr
    refine ⟨rule, ?_, h2, by rw [h1]; exact h3, h4.mono H.leR⟩
    rw [h1]; exact List.find?_eq_of_nodup_map hnd rule hrule

/-- A kernel constructor resolvable after the block was resolvable before, or is one of
the block's constructors: then it is registered in the constructor stage, and the
kernel's `numParams + numFields` is the Π-arity of its model type (`TrIndType`).

PR #43 additionally concluded that some rule of the block fires on it with
`ctorParams = numParams` of its own recursor; that reading (`ctors_have_rules`,
`rules_own_params`) is false for the auxiliary recursors of a nested block, so the rule
side is read from `rec_reg` instead. -/
theorem ctor_find {ctorName : Name} {cval : ConstructorVal}
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) (wf : m₁.WF)
    (h : m₂.find? ctorName = some (.ctorInfo cval)) :
    m₁.find? ctorName = some (.ctorInfo cval) ∨
    ∃ t ∈ decl.types, ∃ c ∈ t.ctors, c.name = ctorName ∧
      H.envC.constants ctorName = some c.toVConstant ∧
      cval.numParams + cval.numFields = c.type.piArity := by
  rcases H.find? wf h with h' | ⟨hci, hname⟩
  · exact .inl h'
  · right
    rcases mem_consts.1 hci with ⟨_, _, h'⟩ | ⟨iv, hiv, _, hcval, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
    obtain ⟨t, ht, htr⟩ := H.types.forall_exists_l iv hiv
    obtain ⟨c, hc, hctr, harity⟩ := htr.ctors.forall_exists_l _ hcval
    have hcn : c.name = ctorName := hctr.2.symm.trans hname
    exact ⟨t, ht, c, hc, hcn, hcn ▸ VEnv.addCtors_find H.stC t ht c hc, harity⟩

end AddInduct

/-- Insert a whole block of definitions into the constant map. -/
def insertDefs (C : ConstMap) (cis : List DefinitionVal) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name (.defnInfo ci)) C

variable (safety : DefinitionSafety) (env env' : VEnv) in
/-- Translation data for a mutual block: the headers are translated against the environment
before the block is added, the values against the environment that already has every constant
of the block, mirroring the kernel adding them all as axioms first. -/
def TrDefBlock (cis : List DefinitionVal) (cis' : List VDefVal) : Prop :=
  List.Forall₂ (fun ci ci' =>
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal ∧
    TrExprS env' ci.levelParams [] ci.value ci'.value) cis cis'

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  /-- The empty constant map, in either stage: the executable replays from
  `Kernel.Environment.empty` with `stage₁ := false`. -/
  | empty {s : Bool} : TrEnv' { stage₁ := s } false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  /-- A mutual block, and an unsafe definition as the one-element case. -/
  | mutualDef {cis : List DefinitionVal} {cis' : List VDefVal} :
    TrDefBlock safety env env' cis cis' →
    -- the block's names are distinct; `addMutual` checks this, as does lean4#14632
    (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci' ∈ cis', ci'.toVConstant.WF env) →
    env.addConsts cis' = some env' →
    (∀ ci' ∈ cis', ci'.WF env') →
    TrEnv' C Q env →
    TrEnv' (insertDefs C cis) Q (env'.addDefEqs cis')
  | thm {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    AddInduct safety C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'
  /-- The projection stage of an inductive declaration (`VInductDecl.addProjs`,
  `VEnv.WF'.inductProjections`): projection entries registered in a well-formed environment add
  no kernel constant. This is the environment the recursors of a block are checked in. -/
  | inductProjections {entries : List VProjectionEntry} :
    (env.addProjections entries).WF →
    TrEnv' C Q env →
    TrEnv' C Q (env.addProjections entries)

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | mutualDef _ _ _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutualDef h2 h3 h4⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.env_eq⟩
  | inductProjections h _ _ => exact h
