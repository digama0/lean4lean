import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Declaration
import Lean4Lean.Inductive.Add
import Lean4Lean.Std.SMap
import Lean4Lean.Verify.Environment.RecursorAlignment
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

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

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  /-- The empty constant map, in either stage. -/
  | empty {s : Bool} : Aligned { stage₁ := s } .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  | projections : Aligned C venv → Aligned C (venv.addProjections entries)
  /-- Abstract case eliminators are absent from the kernel constant map. Their
  well-formedness is certified separately (`VInductBlock.EliminatorsWF`). -/
  | eliminators : Aligned C venv → Aligned C (venv.addEliminator block schema)
  /-- Kernel constant maps are implementation maps rather than ordered
  declaration lists.  A bulk declaration such as nested restoration may
  insert fresh entries in a different order from the dependency order used
  to type their abstract counterparts.  Exact lookup equivalence, together
  with well-formedness of the target representation, permits transport
  between those insertion histories without changing their semantics. -/
  | mapExt : Aligned C venv → C'.WF →
      (∀ name, C.find? name = C'.find? name) → Aligned C' venv

/-- Constructive implementation boundary for an inductive extension at one
observer safety. Besides the independent compilation and installation
certificates, it records exact kernel-map alignment at that safety, and the
alignment of the recursors it installs with the stored iota equations
(`NewRecursorsAligned`). -/
inductive AddInduct (safety : DefinitionSafety)
    (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  | intro (_block : VInductBlock) :
    decl.WF env₁ →
    VInductDecl.CompilesTo env₁ decl _block →
    VInductBlock.WF env₁ _block →
    VInductBlock.install env₁ _block = some env₂ →
    (∀ {name ci}, m₁.find? name = some ci → m₂.find? name = some ci) →
    (Aligned safety m₁ env₁ → Aligned safety m₂ env₂) →
    (∀ {name ci}, m₂.find? name = some ci → ci.deltaValue?.isSome →
      m₁.find? name = some ci) →
    NewRecursorsAligned safety m₁ env₁ m₂ env₂ →
    VInductBlock.EliminatorsWF env₁ decl _block →
    AddInduct safety m₁ env₁ decl m₂ env₂

theorem AddInduct.toVEnv
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    VEnv.AddInduct env₁ decl env₂ :=
  match H with
  | .intro _ hdecl hcompile hblock hinstall _ _ _ _ helim =>
    .intro hdecl hcompile hblock helim hinstall

theorem AddInduct.declWF
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) : decl.WF env₁ := by
  cases H with
  | intro _ hdecl => exact hdecl

theorem AddInduct.le
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := by
  cases H with
  | intro _ _ _ _ hinstall => exact VInductBlock.install_le hinstall

theorem AddInduct.preservesSourceFind
    (H : AddInduct safety m₁ env₁ decl m₂ env₂)
    (hfind : m₁.find? name = some ci) : m₂.find? name = some ci := by
  cases H with
  | intro _ _ _ _ _ hpreserves => exact hpreserves hfind

theorem AddInduct.newRecursorsAligned
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    NewRecursorsAligned safety m₁ env₁ m₂ env₂ := by
  cases H with
  | intro _ _ _ _ _ _ _ _ hrecursors => exact hrecursors

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

theorem AddInduct.installedCertificate
    (H : AddInduct safety source base decl target installed) :
    VEnv.InstalledBelow installed decl := by
  cases H with
  | intro block hdecl hcompile hblock hinstall =>
    exact .intro hdecl.1 hdecl.2 hcompile hblock hinstall VEnv.LE.rfl

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
    AddInduct safety C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

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
  | induct h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h2.toVEnv⟩
