import Lean4Lean.Verify.Inductive.Basic
import Lean4Lean.Theory.Inductive.Normalization

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

/-! # Formation certificates and source translations

The certificates that the header and constructor phases of section 3.2 of the design notes
assemble (`HeaderCertificate`, `ConstructorCertificate` and their prefix invariants,
`FormationCertificate`, which yields `VInductDecl.OrdinaryFormationWF`), and the source
translation of a declaration (`TrInductDeclCore`, wave 1B's `Verify/Environment/Basic.lean`):
its passage from the two checking phases and the well-formedness facts it carries
(`TrInductDeclCore.sourceWF`).

Wave 2 scaffold: the certificate structures are the interface (frozen); the proofs that are
not mechanical are named stubs owned by the `Header/`+`Context/`+`Formation` agent. -/

namespace VerifyInductive

/-- Output of the mutual-header traversal: a common parameter telescope and result level,
and the type shape of every family. -/
structure HeaderCertificate (env : VEnv) (decl : VInductDecl) where
  params : List VExpr
  resultLevel : VLevel
  commonLevels : ∀ type ∈ decl.types, type.resultLevel ≈ resultLevel
  typeShapes : ∀ type ∈ decl.types, decl.TypeShape env params type

theorem typeShape_mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.TypeShape env decl params type) :
    VInductDecl.TypeShape env' decl params type := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, hindicesTake, hparams, hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnormalized.mono henv, hparamsTake, hindicesTake,
    hparams.mono henv, hresult.mono henv⟩

/-- Common-parameter agreement `ConstructorParameterAlignmentAt` of one constructor, from the
family and constructor shape judgments.  The two concrete parameter
telescopes may differ syntactically; both are compared to the declaration's
parameter context `params` in a common environment `finalEnv` extending both. -/
theorem ConstructorParameterAlignmentAt.ofShapes
    {decl : VInductDecl}
    (C : CtorInfoCoherentAt
      prodEnv familyName familyInfo i hi)
    (henv : finalEnv.WF)
    (family : VInductiveType) (ctor : VConstVal)
    (hfamilyLookup : finalEnv.constants familyName =
      some family.toVConstant)
    (hctorLookup : finalEnv.constants familyInfo.ctors[i] =
      some ctor.toVConstant)
    (hfamilyUvars : family.uvars = decl.uvars)
    (hctorUvars : ctor.uvars = decl.uvars)
    (hlevelParams : familyInfo.levelParams.length = decl.uvars)
    (hnumParams : familyInfo.numParams = decl.nparams)
    (Hfamily : decl.TypeShape familyEnv params family)
    (Hctor : decl.CtorShape ctorEnv params family ctor)
    (hfamilyLE : familyEnv ≤ finalEnv)
    (hctorLE : ctorEnv ≤ finalEnv) :
    Nonempty (ConstructorParameterAlignmentAt
      prodEnv finalEnv familyName familyInfo i hi) := by
  rcases Hfamily with
    ⟨familyNormalized, familyDomains, familyAfterParams, familyIndices,
      familyResult, familyType, HfamilyDefEq, HfamilyParams,
      _HfamilyIndices, HfamilyDomains, _HfamilyResult⟩
  rcases Hctor with
    ⟨constructorNormalized, constructorDomains, constructorTail,
      constructorType, _constructorTailCtx, HconstructorDefEq,
      HconstructorParams, HconstructorDomains, _HconstructorCtx,
      _HconstructorTail⟩
  have HfamilyToCanonical : finalEnv.IsDefEqCtx decl.uvars []
      familyDomains.reverse params.reverse :=
    (HfamilyDomains.mono hfamilyLE).symm henv.ordered
  have HcanonicalToConstructor : finalEnv.IsDefEqCtx decl.uvars []
      params.reverse constructorDomains.reverse :=
    HconstructorDomains.mono hctorLE
  have Hdomains : finalEnv.IsDefEqCtx decl.uvars []
      familyDomains.reverse constructorDomains.reverse :=
    VEnv.IsDefEqCtx.trans_empty henv HfamilyToCanonical
      HcanonicalToConstructor
  exact ⟨{
    toCtorInfoCoherentAt := C
    familyTarget := family.toVConstant
    constructorTarget := ctor.toVConstant
    familyLookup := hfamilyLookup
    constructorLookup := hctorLookup
    familyUvars := hfamilyUvars.trans hlevelParams.symm
    constructorUvars := hctorUvars.trans hlevelParams.symm
    familyNormalized := familyNormalized
    constructorNormalized := constructorNormalized
    familyDomains := familyDomains
    constructorDomains := constructorDomains
    familyTail := familyAfterParams
    constructorTail := constructorTail
    familyType := familyType
    constructorType := constructorType
    familyDefEq := by
      simpa [hlevelParams] using HfamilyDefEq.mono hfamilyLE
    constructorDefEq := by
      simpa [hlevelParams] using HconstructorDefEq.mono hctorLE
    familyParams := by simpa [hnumParams] using HfamilyParams
    constructorParams := by simpa [hnumParams] using HconstructorParams
    parameterDomains := by simpa [hlevelParams] using Hdomains }⟩

/-- A successful `takeForalls` peels exactly `arity` binders. -/
theorem VExpr.takeForalls_rebuild
    (H : type.takeForalls arity = some (domains, result)) :
    type = VExpr.wrapForalls domains result ∧ domains.length = arity := by
  induction arity generalizing type domains result with
  | zero =>
    change some ([], type) = some (domains, result) at H
    have hp : ([], type) = (domains, result) := Option.some.inj H
    cases hp
    exact ⟨rfl, rfl⟩
  | succ arity ih =>
    cases type with
    | forallE domain body =>
      cases htail : body.takeForalls arity with
      | none => simp [VExpr.takeForalls, htail] at H
      | some out =>
        rcases out with ⟨tailDomains, tailResult⟩
        rw [VExpr.takeForalls, htail] at H
        change some (domain :: tailDomains, tailResult) =
          some (domains, result) at H
        have hp : (domain :: tailDomains, tailResult) =
            (domains, result) := Option.some.inj H
        cases hp
        rcases ih htail with ⟨hrebuild, hlength⟩
        exact ⟨by simp [VExpr.wrapForalls, hrebuild], by simp [hlength]⟩
    | _ => simp [VExpr.takeForalls] at H

/-- Expose the next family-local parameter from `TypeShape` as a certified
presentation of the whole source header. -/
theorem VInductDecl.TypeShape.nextParameter
    {decl : VInductDecl} {env : VEnv} {params : List VExpr}
    {target : VInductiveType} {i : Nat}
    (H : decl.TypeShape env params target)
    (hi : i < decl.nparams) :
    ∃ (ownParams : List VExpr)
        (expectedDomain expectedBody targetType : VExpr),
      ownParams.length = decl.nparams ∧
      ownParams[i]? = some expectedDomain ∧
      decl.ParamsDefEq env params ownParams ∧
      env.IsDefEq decl.uvars [] target.type
        (VExpr.wrapForalls (ownParams.take i)
          (.forallE expectedDomain expectedBody)) targetType := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, _hindicesTake, hparams, _hresult⟩
  rcases VExpr.takeForalls_rebuild hparamsTake with
    ⟨hnormalizedEq, hownLength⟩
  have hiOwn : i < ownParams.length := by omega
  let expectedBody :=
    VExpr.wrapForalls (ownParams.drop (i + 1)) afterParams
  have hdecomp : ownParams =
      ownParams.take i ++ ownParams[i] :: ownParams.drop (i + 1) := by
    calc
      ownParams = ownParams.take (i + 1) ++ ownParams.drop (i + 1) :=
        (List.take_append_drop (i + 1) ownParams).symm
      _ = (ownParams.take i ++ [ownParams[i]]) ++
          ownParams.drop (i + 1) := by
        rw [List.take_succ_eq_append_getElem hiOwn]
      _ = ownParams.take i ++ ownParams[i] :: ownParams.drop (i + 1) := by
        simp
  refine ⟨ownParams, ownParams[i], expectedBody, exprType, hownLength,
    List.getElem?_eq_getElem hiOwn, hparams, ?_⟩
  have hwrap : VExpr.wrapForalls ownParams afterParams =
      VExpr.wrapForalls (ownParams.take i)
        (.forallE ownParams[i] expectedBody) := by
    calc
      VExpr.wrapForalls ownParams afterParams =
          VExpr.wrapForalls
            (ownParams.take i ++ ownParams[i] :: ownParams.drop (i + 1))
            afterParams := congrArg (fun xs =>
              VExpr.wrapForalls xs afterParams) hdecomp
      _ = VExpr.wrapForalls (ownParams.take i)
          (VExpr.wrapForalls
            (ownParams[i] :: ownParams.drop (i + 1)) afterParams) :=
        VExpr.wrapForalls_append _ _ _
      _ = VExpr.wrapForalls (ownParams.take i)
          (.forallE ownParams[i] expectedBody) := rfl
  rw [hnormalizedEq, hwrap] at hnormalized
  exact hnormalized

def HeaderCertificate.mono {env env' : VEnv} (henv : env ≤ env')
    (H : HeaderCertificate env decl) : HeaderCertificate env' decl where
  params := H.params
  resultLevel := H.resultLevel
  commonLevels := H.commonLevels
  typeShapes type htype := typeShape_mono henv (H.typeShapes type htype)

/-- Prefix invariant threaded through `checkInductiveTypes.loopInd`. -/
structure HeaderPrefixCertificate (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) (done : Nat) : Prop where
  commonLevels : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.types[i].resultLevel ≈ resultLevel
  typeShapes : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.TypeShape env params decl.types[i]

theorem HeaderPrefixCertificate.empty (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) :
    HeaderPrefixCertificate env decl params resultLevel 0 where
  commonLevels _ h := by omega
  typeShapes _ h := by omega

/-- Output of the flattened constructor traversal: the shape of every owned constructor. -/
structure ConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  shapes : ∀ owned ∈ decl.ownedConstructors,
    decl.CtorShape envTypes params owned.1 owned.2

/-- Raw common-parameter shapes retained separately from normalized
constructor formation. -/
structure ConstructorParameterCertificate (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) : Prop where
  shapes : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
    decl.CtorParameterShape env params ctor

theorem ConstructorParameterCertificate.ctorParameterShape
    (H : ConstructorParameterCertificate env decl params)
    (htype : type ∈ decl.types) (hctor : ctor ∈ type.ctors) :
    decl.CtorParameterShape env params ctor :=
  H.shapes type htype ctor hctor

/-- Constructor-tail formation together with the typing fact recovered by
fully applying the checked inductive header. `classes` is the field
classification returned by the executable's positivity check. -/
structure ConstructorTailCertificate (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) (ctx : List VExpr) (depth : Nat)
    (tail : VExpr) (classes : List Bool) : Prop where
  shape : decl.CtorTailWF env target ctx depth tail
  isType : env.IsType decl.uvars ctx tail
  /-- The executable check walks syntactic binders and then requires a valid
  application of the target family at the block's universe parameters, so the
  translated tail is literally a forall telescope over such a codomain. -/
  raw : ∃ doms result,
    tail = VExpr.wrapForalls doms result ∧
    decl.ValidIndAppAt (some target.name) (depth + doms.length) result ∧
    result.getAppFnArgs.1 = .const target.name (VLevel.params decl.uvars)
  /-- Actual source-field domains and contexts carry the uniform recursive
  normal forms checked before introducing the eliminator universe. -/
  uniform : decl.UniformCtorTail env target (VLevel.params decl.uvars) ctx depth tail classes

structure CheckedConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  formation : ConstructorCertificate env decl envTypes params
  types : ∀ ctor ∈ decl.constructorConstants,
    envTypes.IsType decl.uvars [] ctor.type

/-- The first `done` positions of a sequence of length `len` satisfy `P`: the invariant of a
loop that has processed `done` entries. The constructor loops of `checkConstructors`
instantiate it for the constructors of one family and for the families of a block. -/
structure IndexedPrefix (len : Nat) (P : (i : Nat) → i < len → Prop) (done : Nat) : Prop where
  covered : done ≤ len
  holds : ∀ i, i < done → (hi : i < len) → P i hi

theorem IndexedPrefix.empty {len : Nat} {P : (i : Nat) → i < len → Prop} :
    IndexedPrefix len P 0 :=
  ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem IndexedPrefix.push {len : Nat} {P : (i : Nat) → i < len → Prop} {done : Nat}
    (H : IndexedPrefix len P done) (hi : done < len) (h : P done hi) :
    IndexedPrefix len P (done + 1) where
  covered := hi
  holds i hidone hi' := by
    by_cases hlast : i = done
    · subst i; exact h
    · exact H.holds i (by omega) hi'

/-- A complete prefix covers every position. -/
theorem IndexedPrefix.all {len : Nat} {P : (i : Nat) → i < len → Prop}
    (H : IndexedPrefix len P len) (i : Nat) (hi : i < len) : P i hi :=
  H.holds i hi hi

theorem getElem!_append_singleton_self {α : Type} [Inhabited α] {l : List α} {x : α} {n : Nat}
    (h : l.length = n) : (l ++ [x])[n]! = x := by
  subst h
  rw [getElem!_pos (l ++ [x]) l.length (by simp)]
  simp

theorem getElem!_append_singleton_lt {α : Type} [Inhabited α] {l : List α} {x : α} {i : Nat}
    (h : i < l.length) : (l ++ [x])[i]! = l[i]! := by
  rw [getElem!_pos (l ++ [x]) i (by simp; omega), getElem!_pos l i h]
  exact List.getElem_append_left h

/-- `push` for a prefix whose positions also read an output list `out` recorded by the loop,
one entry per processed position. -/
theorem IndexedPrefix.snoc {α : Type} [Inhabited α] {len : Nat}
    {P : (i : Nat) → i < len → α → Prop} {out : List α} {x : α} {done : Nat}
    (H : IndexedPrefix len (fun i hi => P i hi out[i]!) done) (hout : out.length = done)
    (hi : done < len) (h : P done hi x) :
    IndexedPrefix len (fun i hi => P i hi (out ++ [x])[i]!) (done + 1) where
  covered := hi
  holds i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      rw [getElem!_append_singleton_self hout]
      exact h
    · have hlt : i < out.length := by omega
      rw [getElem!_append_singleton_lt hlt]
      exact H.holds i (by omega) hi'

theorem ConstructorCertificate.ctorShape
    (H : ConstructorCertificate env decl envTypes params)
    (htype : type ∈ decl.types) (hctor : ctor ∈ type.ctors) :
    decl.CtorShape envTypes params type ctor := by
  apply H.shapes (type, ctor)
  simp [VInductDecl.ownedConstructors, htype, hctor]

/-- What the constructor loop establishes for one constructor `ctor` of `target`: its shape
and the typing of its type in the header environment. -/
def CtorTypeChecked (envTypes : VEnv) (decl : VInductDecl) (params : List VExpr)
    (target : VInductiveType) (ctor : VConstVal) : Prop :=
  decl.CtorShape envTypes params target ctor ∧ envTypes.IsType decl.uvars [] ctor.type

theorem ConstructorCertificate.ofCtorTypesChecked
    (H : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
      CtorTypeChecked envTypes decl params decl.types[i] decl.types[i].ctors[j]) :
    ConstructorCertificate env decl envTypes params where
  shapes owned howned := by
    rcases List.mem_flatMap.1 howned with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    simp only [List.mem_map] at hctor
    rcases hctor with ⟨ctor, hctor, hpair⟩
    cases hpair
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, hctorEq⟩
    cases hctorEq
    simpa using (H i hi j hj).1

theorem CheckedConstructorCertificate.ofCtorTypesChecked
    (H : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
      CtorTypeChecked envTypes decl params decl.types[i] decl.types[i].ctors[j]) :
    CheckedConstructorCertificate env decl envTypes params where
  formation := .ofCtorTypesChecked H
  types ctor hctor := by
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, rfl⟩
    exact (H i hi j hj).2

/-- Fielded aggregation target for the executable header and constructor
traversals. The public specification remains `VInductDecl.OrdinaryFormationWF`; this
certificate gives the refinement proof stable, named obligations instead of
repeatedly unpacking a large existential. -/
structure FormationCertificate (env : VEnv) (decl : VInductDecl) where
  headers : HeaderCertificate env decl
  envTypes : VEnv
  typesInstalled : env.addConstVals decl.typeConstants = some envTypes
  constructorParameters : ConstructorParameterCertificate envTypes decl
    headers.params
  constructors : ConstructorCertificate env decl envTypes headers.params
  /-- Raw syntactic shape of every source constructor, derived from the
  executable binder walk and its final `isValidIndAppIdx` check. -/
  rawShapes : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
    decl.RawCtorShape type ctor

theorem FormationCertificate.formationWF
    (H : FormationCertificate env decl) : decl.OrdinaryFormationWF env := by
  exact ⟨H.headers.params, H.headers.resultLevel, H.envTypes, H.typesInstalled,
    fun type htype => ⟨H.headers.commonLevels type htype,
      H.headers.typeShapes type htype⟩,
    fun type htype ctor hctor =>
      ⟨H.constructorParameters.ctorParameterShape htype hctor,
        H.constructors.ctorShape htype hctor⟩,
    H.rawShapes⟩

/-- The recursor half of `VInductDecl.WF`: everything but `source` and `formation`. The
recursor and rule phases deliver it (`RecursorCheck`, `RuleTranslations`); together with a
formation certificate and the source judgment it gives `decl.WF env`
(`FormationCertificate.wf`). -/
structure RecursorsWF (env : VEnv) (decl : VInductDecl) : Prop where
  recsCompiled : decl.RecsCompiled env
  recs_wf : ∀ envP, decl.addTypesCtorsProjs env = some envP →
    ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF envP
  rec_shape : ∀ r ∈ decl.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  rules_nodup : ∀ r ∈ decl.recs, (r.rules.map (·.ctor)).Nodup
  rules_ctor : ∀ envC, decl.addTypesCtors env = some envC → ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∃ ci, envC.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  rule_shape : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  rules_wf : ∀ envR, decl.addTypesCtorsProjsRecs env = some envR →
    ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
    envR.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

theorem VInductDecl.WF.recursorsWF {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    RecursorsWF env decl :=
  ⟨H.recsCompiled, H.recs_wf, H.rec_shape, H.rules_nodup, H.rules_ctor, H.rule_shape, H.rules_wf⟩

/-- The declaration judgment from a formation certificate, the source judgment and the
recursor half. -/
theorem FormationCertificate.wf
    (H : FormationCertificate env decl) (hsource : decl.SourceWF env)
    (hrecs : RecursorsWF env decl) : decl.WF env where
  source := hsource
  formation := .ordinary H.formationWF
  recsCompiled := hrecs.recsCompiled
  recs_wf := hrecs.recs_wf
  rec_shape := hrecs.rec_shape
  rules_nodup := hrecs.rules_nodup
  rules_ctor := hrecs.rules_ctor
  rule_shape := hrecs.rule_shape
  rules_wf := hrecs.rules_wf

/-- `List.Forall₂` from equal lengths and the relation at every index. Recursor and rule
loops use it to turn indexed facts into a pointwise relation. -/
theorem List.forall₂_of_getElem
    {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (hlen : as.length = bs.length)
    (H : ∀ i (ha : i < as.length) (hb : i < bs.length),
      R as[i] bs[i]) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil =>
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst bs
    exact .nil
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have htail : as.length = bs.length := by simpa using hlen
      apply List.Forall₂.cons (H 0 (by simp) (by simp))
      apply ih htail
      intro i ha hb
      have h := H (i + 1) (by simpa) (by simpa)
      change R as[i] bs[i] at h
      exact h

/-- Two pointwise translations of a source spine have the same target spine. -/
theorem List.Forall₂.targets_eq_of_unique
    (H₁ : List.Forall₂ (TrExprS env Us Δ) source target₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ) source target₂) : target₁ = target₂ := by
  induction H₁ generalizing target₂ with
  | nil => cases H₂; rfl
  | cons Hhead _ ih =>
    let .cons Hhead' Htail' := H₂
    rw [Hhead.unique_of_syn Hhead', ih Htail']

theorem Expr.getAppFn_mkAppN (fn : Expr) (args : Array Expr) :
    (mkAppN fn args).getAppFn = fn.getAppFn := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons]
    simpa [Expr.getAppFn] using ih (.app fn arg)

/-- An application spine headed by a local variable cannot be one of Lean's
distinguished parameter-annotation applications. -/
theorem Expr.isAppOfArity_eq_false_of_getAppFn_fvar
    {e : Expr} (h : e.getAppFn = .fvar fv) (name : Name) (arity : Nat) :
    e.isAppOfArity name arity = false := by
  induction e generalizing arity with
  | app fn arg ihFn _ =>
    cases arity with
    | zero => rfl
    | succ arity =>
      apply ihFn
      simpa only [Expr.getAppFn] using h
  | _ => cases arity <;> simp_all [Expr.getAppFn, Expr.isAppOfArity]

theorem Expr.getAppArgsList_mkAppN (fn : Expr) (args : Array Expr) :
    (mkAppN fn args).getAppArgsList = fn.getAppArgsList ++ args.toList := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [Expr.getAppArgsList_app, List.append_assoc]

@[simp] theorem Expr.foldl_mkApp_eq (args : List Expr) (fn : Expr) :
    args.foldl Lean.mkApp fn = args.foldl Expr.app fn := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons, Lean.mkApp]
    exact ih (.app fn arg)

/-- Remove equally long outer prefixes from a context conversion.  Since
`IsDefEqCtx` is built from the shared innermost suffix outwards, the proof is
just inversion through the two prefixes. -/
theorem VEnv.IsDefEqCtx.dropPrefixes
    (H : VEnv.IsDefEqCtx env U [] (xs ++ Γ₁) (ys ++ Γ₂))
    (hlen : xs.length = ys.length) :
    VEnv.IsDefEqCtx env U [] Γ₁ Γ₂ := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simpa [this] using H
  | cons _ xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons _ ys =>
      simp only [List.cons_append] at H
      cases H with
      | succ H _ =>
        apply ih H
        simpa using Nat.succ.inj hlen

/-- Remove the same number of newest declarations from both sides of a
complete context conversion. -/
theorem VEnv.IsDefEqCtx.dropHeads
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂) (n : Nat) :
    VEnv.IsDefEqCtx env U [] (Γ₁.drop n) (Γ₂.drop n) := by
  induction n generalizing Γ₁ Γ₂ with
  | zero => simpa using H
  | succ n ih =>
    cases H with
    | zero => exact .zero
    | succ H _ =>
      simpa only [List.drop_succ_cons] using ih H

/-- Close the same number of newest declarations on both sides of a context
conversion.  Corresponding domains may differ definitionally, so the two
resulting forall telescopes need not be syntactically equal; `forallEDF`
turns the context conversion into exactly the required type equality. -/
theorem VEnv.IsDefEqCtx.closeHeads
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (n : Nat) (hn : n ≤ Γ₁.length)
    (Hbody : env.IsDefEq U Γ₁ body₁ body₂ (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U (Γ₁.drop n)
      (VExpr.wrapForalls (Γ₁.take n).reverse body₁)
      (VExpr.wrapForalls (Γ₂.take n).reverse body₂)
      (.sort resultLevel) := by
  induction n generalizing Γ₁ Γ₂ body₁ body₂ bodyLevel with
  | zero =>
    exact ⟨bodyLevel, by simpa [VExpr.wrapForalls] using Hbody⟩
  | succ n ih =>
    cases H with
    | zero => simp at hn
    | @succ Γ₁ Γ₂ domain₁ domain₂ domainLevel Hctx Hdomain =>
      have hn' : n ≤ Γ₁.length := by simpa using hn
      have Hforall : env.IsDefEq U Γ₁
          (.forallE domain₁ body₁) (.forallE domain₂ body₂)
          (.sort (.imax domainLevel bodyLevel)) :=
        .forallEDF Hdomain Hbody
      rcases ih Hctx hn' Hforall with ⟨resultLevel, Hclosed⟩
      refine ⟨resultLevel, ?_⟩
      simpa [VExpr.wrapForalls, List.take_succ_cons,
        List.reverse_cons, VExpr.wrapForalls_append] using Hclosed

/-- A function whose type is a forall telescope over `installedDomains`, convertible as a
context to the closed domains `types` lifted into one telescope (`VExpr.liftClosedDomains`),
applied to arguments typed at `types`, has the type obtained by instantiating the converted
telescope (with the installed residual `resultType`) at those arguments. -/
theorem VEnv.HasType.mkApps_of_defeqLiftClosedDomains_exact
    (henv : env.WF) (Hctx : OnCtx ctx (env.IsType uvars))
    (Hfn : env.HasType uvars ctx fn
      (VExpr.wrapForalls installedDomains resultType))
    (Hdomains : VEnv.IsDefEqCtx env uvars []
      (installedDomains.reverse ++ ctx)
      ((VExpr.liftClosedDomains types 0).reverse ++ ctx))
    (Hargs : List.Forall₂
      (env.HasType uvars ctx) args types) :
    env.HasType uvars ctx (VExpr.mkApps fn args)
      (VExpr.applyForallType
        (VExpr.wrapForalls (VExpr.liftClosedDomains types 0) resultType)
        args) := by
  have hlength : installedDomains.length = types.length := by
    have hcontexts := Hdomains.length_eq
    simp only [List.length_append, List.length_reverse,
      VExpr.liftClosedDomains_length] at hcontexts
    omega
  have HtelescopeType : env.IsType uvars ctx
      (VExpr.wrapForalls installedDomains resultType) :=
    Hfn.isType henv Hctx
  have Hopened := VEnv.IsType.wrapForalls_inv henv.ordered Hctx
    HtelescopeType
  have HresultType : env.IsType uvars
      (installedDomains.reverse ++ ctx) resultType := Hopened.2
  rcases HresultType with ⟨resultLevel, HresultType⟩
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads Hdomains
      installedDomains.length (by simp) HresultType with
    ⟨closedLevel, Hclosed⟩
  have Hwhole : env.IsDefEqU uvars ctx
      (VExpr.wrapForalls installedDomains resultType)
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
        resultType) := by
    refine ⟨.sort closedLevel, ?_⟩
    simpa [hlength] using Hclosed
  have HfnCanonical : env.HasType uvars ctx fn
      (VExpr.wrapForalls (VExpr.liftClosedDomains types 0)
        resultType) :=
    Hfn.defeqU_r henv Hctx Hwhole
  rcases VEnv.TypedApplicationSpine.liftClosedDomains
      HfnCanonical Hargs with ⟨finalType, Hspine⟩
  rw [← Hspine.result_eq_applyForallType]
  exact Hspine.hasType

/-- Select one corresponding declaration from a complete context
conversion.  The selected types are compared in the older left-hand suffix,
which is the context in which that declaration was originally formed. -/
theorem VEnv.IsDefEqCtx.getElem
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (hi : i < Γ₁.length) :
    ∃ u, env.IsDefEq U (Γ₁.drop (i + 1)) Γ₁[i]
      (Γ₂[i]'(H.length_eq ▸ hi)) (.sort u) := by
  induction H generalizing i with
  | zero => simp at hi
  | @succ Γ₁ Γ₂ A₁ A₂ u H hhead ih =>
    cases i with
    | zero =>
      exact ⟨u, by simpa using hhead⟩
    | succ i =>
      have hi' : i < Γ₁.length := by simpa using hi
      simpa only [List.length_cons, List.getElem_cons_succ,
        List.drop_succ_cons, Nat.succ_eq_add_one] using ih hi'

/-- Right-context form of `IsDefEqCtx.getElem`.  This is convenient when the
consumer has already moved into the converted telescope. -/
theorem VEnv.IsDefEqCtx.getElemRight
    (henv : VEnv.Ordered env)
    (H : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (hi : i < Γ₁.length) :
    ∃ u, env.IsDefEq U (Γ₂.drop (i + 1)) Γ₁[i]
      (Γ₂[i]'(H.length_eq ▸ hi)) (.sort u) := by
  induction H generalizing i with
  | zero => simp at hi
  | @succ Γ₁ Γ₂ A₁ A₂ u H hhead ih =>
    cases i with
    | zero =>
      exact ⟨u, by simpa using hhead.defeqDFC henv H⟩
    | succ i =>
      have hi' : i < Γ₁.length := by simpa using hi
      simpa only [List.length_cons, List.getElem_cons_succ,
        List.drop_succ_cons, Nat.succ_eq_add_one] using ih hi'

/-- Pointwise form of `ParamsDefEq`.  Parameter `i` is compared with the
corresponding family-local parameter in precisely the context of the earlier
parameters, matching the order in which cached headers are replayed. -/
theorem VInductDecl.ParamsDefEq.getElem
    {decl : VInductDecl} {env : VEnv} {params ownParams : List VExpr}
    {i : Nat}
    (H : decl.ParamsDefEq env params ownParams)
    (hi : i < params.length) :
    ∃ u, env.IsDefEq decl.uvars (params.take i).reverse
      params[i] (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using H.length_eq
        omega)) (.sort u) := by
  have hlen : params.length = ownParams.length := by
    simpa using H.length_eq
  have hrev : params.length - 1 - i < params.reverse.length := by
    simp
    omega
  have hentry := VEnv.IsDefEqCtx.getElem H hrev
  have htake :
      params.length - (params.length - (1 + i) + 1) = i := by omega
  have hindex :
      params.length - (1 + (params.length - (1 + i))) = i := by omega
  simpa [List.getElem_reverse, List.drop_reverse, hlen.symm, Nat.sub_sub,
    htake, hindex] using hentry

theorem VInductDecl.paramsDefEq_reflOfAppend
    {decl : VInductDecl} {env : VEnv} {indices params : List VExpr}
    (H : OnCtx (indices.reverse ++ params.reverse)
      (env.IsType decl.uvars)) :
    decl.ParamsDefEq env params params := by
  exact VEnv.IsDefEqCtx.refl (OnCtx.of_append H)

theorem VEnv.addConstVals_append
    {env middle out : VEnv} {xs ys : List VConstVal}
    (hxs : env.addConstVals xs = some middle)
    (hys : middle.addConstVals ys = some out) :
    env.addConstVals (xs ++ ys) = some out := by
  induction xs generalizing env with
  | nil =>
    simp [VEnv.addConstVals] at hxs
    subst middle
    exact hys
  | cons x xs ih =>
    simp only [List.cons_append, VEnv.addConstVals] at hxs ⊢
    cases hnext : env.addConst x.name x.toVConstant with
    | none => simp [hnext] at hxs
    | some next =>
      rw [hnext] at hxs
      simpa [hnext] using ih (by simpa using hxs)

theorem VEnv.addConstVals_append_inv
    {env out : VEnv} {xs ys : List VConstVal}
    (H : env.addConstVals (xs ++ ys) = some out) :
    ∃ middle, env.addConstVals xs = some middle ∧
      middle.addConstVals ys = some out := by
  induction xs generalizing env with
  | nil =>
    exact ⟨env, by simp [VEnv.addConstVals], by simpa [VEnv.addConstVals] using H⟩
  | cons x xs ih =>
    simp only [List.cons_append, VEnv.addConstVals] at H
    cases hnext : env.addConst x.name x.toVConstant with
    | none => simp [hnext] at H
    | some next =>
      rw [hnext] at H
      rcases ih H with ⟨middle, hprefix, hsuffix⟩
      exact ⟨middle, by simp [VEnv.addConstVals, hnext, hprefix], hsuffix⟩

/-- Successful left-to-right abstract installation implies both freshness in
the input environment and pairwise distinctness of all installed names. -/
theorem VEnv.addConstVals_names_fresh
    {env out : VEnv} {constants : List VConstVal}
    (H : env.addConstVals constants = some out) :
    (constants.map (·.name)).Nodup ∧
      ∀ ci ∈ constants, env.constants ci.name = none := by
  induction constants generalizing env with
  | nil => simp
  | cons ci constants ih =>
    simp only [VEnv.addConstVals] at H
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [hadd] at H
    | some next =>
      rw [hadd] at H
      rcases ih H with ⟨htail, hfresh⟩
      have hinstalled : next.constants ci.name = some ci.toVConstant :=
        VEnv.addConst_self hadd
      have hhead : ci.name ∉ constants.map (·.name) := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨later, hlater, hname⟩
        have habsent := hfresh later hlater
        rw [hname, hinstalled] at habsent
        contradiction
      refine ⟨List.nodup_cons.mpr ⟨hhead, htail⟩, ?_⟩
      intro later hlater
      simp only [List.mem_cons] at hlater
      rcases hlater with rfl | hlater
      · unfold VEnv.addConst at hadd
        split at hadd <;> cases hadd
        assumption
      · have habsent := hfresh later hlater
        have hne : ci.name ≠ later.name := by
          intro heq
          apply hhead
          exact List.mem_map.mpr ⟨later, hlater, heq.symm⟩
        rw [VEnv.addConst_constants_of_ne hadd hne] at habsent
        exact habsent

/-- Installing constants whose names all differ from an observed name leaves
that lookup unchanged.  This is the absence-preservation counterpart of
`addConstVals_le`, which only transports successful lookups. -/
theorem VEnv.addConstVals_constants_of_forall_ne
    {env out : VEnv} {constants : List VConstVal}
    (H : env.addConstVals constants = some out)
    (hne : ∀ ci ∈ constants, ci.name ≠ name) :
    out.constants name = env.constants name := by
  induction constants generalizing env with
  | nil =>
    simp [VEnv.addConstVals] at H
    subst out
    rfl
  | cons ci constants ih =>
    simp only [VEnv.addConstVals] at H
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [hadd] at H
    | some next =>
      rw [hadd] at H
      rw [ih H (fun later hlater => hne later (by simp [hlater]))]
      exact VEnv.addConst_constants_of_ne hadd (hne ci (by simp))


theorem TrInductDeclCore.sourceNames_nodup
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    decl.sourceNames.Nodup := by
  have hadd : env.addConstVals
      (decl.typeConstants ++ decl.constructorConstants) = some envCtors :=
    VEnv.addConstVals_append H.typesAdded H.ctorsAdded
  simpa [VInductDecl.sourceNames, List.map_append] using
    VEnv.addConstVals_names_nodup hadd

/-- The two executable checking phases jointly recover the pointwise core
translation, without assuming aggregate source well-formedness. -/
theorem TrInductDeclCore.ofPhases
    (Hheaders : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (Hctors : TrInductDeclConstructors envTypes lparams types decl envCtors) :
    TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors := by
  have combine : ∀ {sources targets},
      List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
        sources targets →
      List.Forall₂
        (fun source target => List.Forall₂
          (fun ctor ctor' =>
            TrSourceConst envTypes lparams ctor.name ctor.type ctor')
          source.ctors target.ctors)
        sources targets →
      List.Forall₂ (TrInductiveType env envTypes lparams)
        sources targets := by
    intro sources targets hheaders hctors
    induction hheaders with
    | nil =>
      cases hctors
      exact .nil
    | cons hheader _ ih =>
      cases hctors with
      | cons hctor hctors =>
        exact .cons ⟨hheader.header, hctor⟩ (ih hctors)
  exact {
    uvars := Hheaders.uvars
    nparams := Hheaders.nparams
    isUnsafe := Hheaders.isUnsafe
    typesAdded := Hheaders.typesAdded
    ctorsAdded := Hctors.ctorsAdded
    types := combine Hheaders.types Hctors.types }

/-- The source family headers are well formed in the source environment. -/
theorem TrInductDeclCore.typeHeadersWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors) :
    ∀ type ∈ decl.types, type.toVConstant.WF env := by
  intro type member
  obtain ⟨source, _, translated⟩ := Lean4Lean.List.Forall₂.forall_exists_r H.types type member
  exact translated.header.wf

/-- The constructor environment of the core translation is well formed whenever the
source environment is: translated headers may be added as axioms first, followed by the
independently checked source constructors. -/
theorem TrInductDeclCore.envCtorsWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (henv : env.WF) : envCtors.WF := by
  have htypes : ∀ ci ∈ decl.typeConstants,
      ci.toVConstant.WF env := by
    intro ci hci
    simp only [VInductDecl.typeConstants] at hci
    rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
      ⟨source, _hsource, Htarget⟩
    exact Htarget.header.wf
  have henvTypes : envTypes.WF :=
    VEnv.WF.addConstVals henv htypes H.typesAdded
  have hctors : ∀ ci ∈ decl.constructorConstants,
      ci.toVConstant.WF envTypes := by
    intro ci hci
    simp only [VInductDecl.constructorConstants] at hci
    rcases List.mem_flatMap.mp hci with ⟨target, htarget, hctor⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
      ⟨source, _hsource, Htarget⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ci hctor with
      ⟨sourceCtor, _hsourceCtor, Hctor⟩
    exact Hctor.wf
  exact VEnv.WF.addConstVals henvTypes hctors H.ctorsAdded

/-- Every translated constructor is well formed in the mutual header
environment. -/
theorem TrInductDeclCore.constructorsWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF envTypes := by
  intro ci hci
  simp only [VInductDecl.constructorConstants] at hci
  rcases List.mem_flatMap.mp hci with ⟨target, htarget, hctor⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
    ⟨source, _hsource, Htarget⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ci hctor with
    ⟨sourceCtor, _hsourceCtor, Hctor⟩
  exact Hctor.wf

/-- Header constants are typed in the source environment, so their exact
installation is well formed independently of constructor installation. -/
theorem TrInductDeclCore.envTypesWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (henv : env.WF) : envTypes.WF := by
  apply VEnv.WF.addConstVals henv _ H.typesAdded
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
    ⟨_source, _hsource, Htarget⟩
  exact Htarget.header.wf

/-- Pointwise source translations already contain all typing and
universe facts required by `SourceWF`. Thus the aggregate source judgment
adds only nonemptiness and global name uniqueness. Nonemptiness comes from
the lowering entry point; uniqueness follows from the `addConstVals`
equalities of the header and constructor environments kept by the core translation. -/
theorem TrInductDeclCore.sourceWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ [])
    (hnames : decl.sourceNames.Nodup) :
    decl.SourceWF env := by
  have hproperties : ∀ target ∈ decl.types,
      target.uvars = decl.uvars ∧
      target.toVConstant.WF env ∧
      ∀ ctor ∈ target.ctors,
        ctor.uvars = decl.uvars ∧
        ctor.toVConstant.WF envTypes := by
    intro target htarget
    rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
      ⟨source, _, Htarget⟩
    refine ⟨Htarget.header.uvars.trans H.uvars.symm,
      Htarget.header.wf, ?_⟩
    intro ctor hctor
    rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ctor hctor with
      ⟨sourceCtor, _, Hctor⟩
    exact ⟨Hctor.uvars.trans H.uvars.symm, Hctor.wf⟩
  refine ⟨hnonempty, hnames, ?_, ?_, envTypes, envCtors,
    H.typesAdded, H.ctorsAdded, ?_, ?_⟩
  · intro target htarget
    exact (hproperties target htarget).1
  · intro ctor hctor
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    exact (hproperties target htarget).2.2 ctor hctor |>.1
  · intro target htarget
    exact (hproperties target htarget).2.1
  · intro ctor hctor
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    exact (hproperties target htarget).2.2 ctor hctor |>.2

/-- Constructor universe arities are already fixed by the pointwise source
translation; unlike the aggregate `SourceWF` theorem, this fact needs no
nonemptiness or global-name premise. -/
theorem TrInductDeclCore.constructorUvars
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars := by
  intro ctor hctor
  simp only [VInductDecl.constructorConstants] at hctor
  rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
    ⟨source, _hsource, Htarget⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ctor hctor with
    ⟨sourceCtor, _hsourceCtor, Hctor⟩
  exact Hctor.uvars.trans H.uvars.symm

theorem TrInductDeclCore.toTrInductDecl
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ [])
    (hnames : decl.sourceNames.Nodup) :
    TrInductDecl env lparams nparams types isUnsafe decl := by
  exact ⟨TrInductDeclCore.sourceWF H hnonempty hnames,
    H.uvars, H.nparams, H.isUnsafe,
    envTypes, envCtors, H.typesAdded, H.ctorsAdded, H.types⟩

theorem TrInductDeclCore.sourceWF_ofNonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ []) :
    decl.SourceWF env :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF H hnonempty
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup H)

theorem TrInductDeclCore.toTrInductDeclOfNonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ []) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDecl H hnonempty
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup H)

theorem TrInductDeclCore.nonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ []) :
    decl.types ≠ [] := by
  intro htarget
  have hlength :=
    List.Forall₂.length_eq H.types
  rw [htarget] at hlength
  exact hsource (List.eq_nil_of_length_eq_zero hlength)

theorem TrInductDeclCore.types_length
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    types.length = decl.types.length :=
  List.Forall₂.length_eq H.types

theorem TrInductDeclCore.typeAt
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    TrInductiveType env envTypes lparams types[i] decl.types[i] :=
  List.forall₂_getElem H.types i hsource htarget

theorem TrInductiveType.ctors_length
    (H : TrInductiveType env envTypes lparams type target) :
    type.ctors.length = target.ctors.length :=
  List.Forall₂.length_eq H.ctors

theorem TrInductiveType.ctorAt
    (H : TrInductiveType env envTypes lparams type target)
    (i : Nat) (hsource : i < type.ctors.length)
    (htarget : i < target.ctors.length) :
    TrSourceConst envTypes lparams type.ctors[i].name type.ctors[i].type
      target.ctors[i] :=
  List.forall₂_getElem H.ctors i hsource htarget

theorem TrInductiveType.headers
    (H : TrInductiveType env envTypes lparams type target) :
    TrInductiveTypeHeaders env envTypes lparams type target where
  header := H.header
  ctors := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => h.raw) H.ctors

theorem TrInductiveTypeHeaders.ctors_length
    (H : TrInductiveTypeHeaders env envTypes lparams type target) :
    type.ctors.length = target.ctors.length :=
  List.Forall₂.length_eq H.ctors

theorem TrInductiveTypeHeaders.ctorAt
    (H : TrInductiveTypeHeaders env envTypes lparams type target)
    (i : Nat) (hsource : i < type.ctors.length)
    (htarget : i < target.ctors.length) :
    TrSourceConstRaw envTypes lparams type.ctors[i].name type.ctors[i].type
      target.ctors[i] :=
  List.forall₂_getElem H.ctors i hsource htarget

theorem TrSourceConstRaw.checked
    (H : TrSourceConstRaw env lparams name type ci')
    (hwf : ci'.toVConstant.WF env) :
    TrSourceConst env lparams name type ci' :=
  ⟨H.uvars, H.name, H.type, hwf⟩

/-- Constructor checking supplies exactly the typing facts missing from
the header phase's raw constructor translations. -/
theorem CheckedConstructorCertificate.translated
    {types : List InductiveType}
    (H : CheckedConstructorCertificate sourceEnv decl envTypes params)
    (Hdecl : TrInductDeclHeaders sourceEnv lparams nparams types isUnsafe
      decl envTypes) :
    List.Forall₂
      (fun (source : InductiveType) (target : VInductiveType) => List.Forall₂
        (fun (ctor : Constructor) (ctor' : VConstVal) =>
          TrSourceConst envTypes lparams ctor.name ctor.type ctor')
        source.ctors target.ctors)
      types decl.types := by
  have hlength : types.length = decl.types.length :=
    List.Forall₂.length_eq Hdecl.types
  apply List.forall₂_of_getElem hlength
  intro i hsource htarget
  have Htype := List.forall₂_getElem
    Hdecl.types i hsource htarget
  have hctorLength : types[i].ctors.length = decl.types[i].ctors.length :=
    List.Forall₂.length_eq Htype.ctors
  apply List.forall₂_of_getElem hctorLength
  intro j hsourceCtor htargetCtor
  have Hctor := List.forall₂_getElem
    Htype.ctors j hsourceCtor htargetCtor
  apply Lean4Lean.VerifyInductive.TrSourceConstRaw.checked Hctor
  have hwf := H.types decl.types[i].ctors[j] (by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[i], List.getElem_mem htarget,
      List.getElem_mem htargetCtor⟩)
  have huvars : decl.types[i].ctors[j].uvars = decl.uvars :=
    Hctor.uvars.trans Hdecl.uvars.symm
  simpa [VConstant.WF, huvars] using hwf

theorem TrInductDeclCore.headers
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    TrInductDeclHeaders env lparams nparams types isUnsafe decl envTypes where
  uvars := H.uvars
  nparams := H.nparams
  isUnsafe := H.isUnsafe
  typesAdded := H.typesAdded
  types := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => TrInductiveType.headers h) H.types

/-- Inductive metadata does not affect translation of the source header:
only visibility, universe parameters, name, and type enter the translation from the kernel
environment. -/
theorem TrSourceConst.inductInfo
    (H : TrSourceConst env lparams name type ci')
    (hlevelParams : info.levelParams = lparams)
    (hname : info.name = name)
    (htype : info.type = type)
    (hvisible : safety ≤
      (if info.isUnsafe then DefinitionSafety.unsafe else .safe)) :
    TrConstVal safety env (.inductInfo info) ci' := by
  subst lparams
  subst name
  subst type
  constructor
  · exact ⟨by simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hvisible,
      H.uvars.symm, H.type⟩
  · exact H.name.symm

theorem TrSourceConst.ctorInfo
    (H : TrSourceConst env lparams name type ci')
    (hlevelParams : info.levelParams = lparams)
    (hname : info.name = name)
    (htype : info.type = type)
    (hvisible : safety ≤
      (if info.isUnsafe then DefinitionSafety.unsafe else .safe)) :
    TrConstVal safety env (.ctorInfo info) ci' := by
  subst lparams
  subst name
  subst type
  constructor
  · exact ⟨by simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hvisible,
      H.uvars.symm, H.type⟩
  · exact H.name.symm

def ownedConstructors
    (types : List InductiveType) : List (InductiveType × Constructor) :=
  types.flatMap fun type => type.ctors.map (type, ·)

def TrOwnedConstructor (env envTypes : VEnv) (lparams : List Name) :
    (InductiveType × Constructor) →
      (VInductiveType × VConstVal) → Prop
  | (type, ctor), (target, ctor') =>
    TrInductiveType env envTypes lparams type target ∧
      TrSourceConst envTypes lparams ctor.name ctor.type ctor'

theorem TrInductiveType.ownedConstructors
    (H : TrInductiveType env envTypes lparams type target) :
    List.Forall₂ (TrOwnedConstructor env envTypes lparams)
      (type.ctors.map (type, ·)) (target.ctors.map (target, ·)) := by
  have aux : ∀ {ctors ctors'},
      List.Forall₂ (fun ctor ctor' =>
        TrSourceConst envTypes lparams ctor.name ctor.type ctor')
        ctors ctors' →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (ctors.map (type, ·)) (ctors'.map (target, ·)) := by
    intro ctors ctors' hctors
    induction hctors with
    | nil => exact .nil
    | cons h _ ih => exact .cons ⟨H, h⟩ ih
  exact aux H.ctors

theorem TrInductDeclCore.ownedConstructors
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    List.Forall₂ (TrOwnedConstructor env envTypes lparams)
      (Lean4Lean.VerifyInductive.ownedConstructors types)
      decl.ownedConstructors := by
  have aux : ∀ {types targets},
      List.Forall₂ (TrInductiveType env envTypes lparams) types targets →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (Lean4Lean.VerifyInductive.ownedConstructors types)
        (targets.flatMap fun target => target.ctors.map (target, ·)) := by
    intro types targets htypes
    induction htypes with
    | nil => exact .nil
    | cons h _ ih =>
      simpa [Lean4Lean.VerifyInductive.ownedConstructors] using
        List.Forall₂.append'
          (Lean4Lean.VerifyInductive.TrInductiveType.ownedConstructors h) ih
  simpa [VInductDecl.ownedConstructors] using aux H.types

theorem TrInductDeclCore.ownedConstructors_length
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    (Lean4Lean.VerifyInductive.ownedConstructors types).length =
      decl.ownedConstructors.length :=
  List.Forall₂.length_eq
    (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors H)


/-! ## Transport along `VInductDecl.withRecs`

The source fields of `decl.withRecs recs` are those of `decl`, so every judgment that reads only
them transports by reassembling its fields. -/

theorem TrInductDeclCore.withRecs
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors)
    (recs : List VRecursor) :
    TrInductDeclCore env lparams nparams types isUnsafe (decl.withRecs recs) envTypes envCtors :=
  ⟨H.uvars, H.nparams, H.isUnsafe, H.typesAdded, H.ctorsAdded, H.types⟩

def HeaderCertificate.withRecs (H : HeaderCertificate env decl) (recs : List VRecursor) :
    HeaderCertificate env (decl.withRecs recs) where
  params := H.params
  resultLevel := H.resultLevel
  commonLevels := H.commonLevels
  typeShapes := H.typeShapes

theorem _root_.Lean4Lean.VInductDecl.Positive.withRecs {env : VEnv} {decl : VInductDecl}
    (recs : List VRecursor) (H : decl.Positive env ctx depth e) :
    (decl.withRecs recs).Positive env ctx depth e :=
  VInductDecl.Positive.rec (env := env) (decl := decl)
    (motive_1 := fun ctx depth e _ => (decl.withRecs recs).Positive env ctx depth e)
    (motive_2 := fun ctx depth e _ => (decl.withRecs recs).SyntacticallyPositive env ctx depth e)
    (fun hdef _ ih => .unfold hdef ih)
    (fun h => .nonrecursive h)
    (fun hcontains hdom hbody _ ih => .forallE hcontains hdom hbody ih)
    (fun h => .recursive h) H

theorem _root_.Lean4Lean.VInductDecl.CtorTailWF.withRecs {env : VEnv} {decl : VInductDecl}
    (recs : List VRecursor) (H : decl.CtorTailWF env target ctx depth e) :
    (decl.withRecs recs).CtorTailWF env target ctx depth e := by
  induction H with
  | result happ hdef => exact .result happ hdef
  | field htype hlevel hpositive hdom hbody _ ih =>
    exact .field htype hlevel (hpositive.elim .inl fun h => .inr (h.withRecs recs)) hdom hbody ih

theorem ConstructorCertificate.withRecs (H : ConstructorCertificate env decl envTypes params)
    (recs : List VRecursor) : ConstructorCertificate env (decl.withRecs recs) envTypes params where
  shapes owned howned := by
    obtain ⟨normalized, ownParams, tail, exprType, tailCtx, h1, h2, h3, h4, h5⟩ :=
      H.shapes owned howned
    exact ⟨normalized, ownParams, tail, exprType, tailCtx, h1, h2, h3, h4, h5.withRecs recs⟩

theorem ConstructorParameterCertificate.withRecs
    (H : ConstructorParameterCertificate env decl params) (recs : List VRecursor) :
    ConstructorParameterCertificate env (decl.withRecs recs) params :=
  ⟨H.shapes⟩

def FormationCertificate.withRecs (H : FormationCertificate env decl) (recs : List VRecursor) :
    FormationCertificate env (decl.withRecs recs) where
  headers := H.headers.withRecs recs
  envTypes := H.envTypes
  typesInstalled := H.typesInstalled
  constructorParameters := H.constructorParameters.withRecs recs
  constructors := H.constructors.withRecs recs
  rawShapes := H.rawShapes

theorem VInductDecl.SourceWF.withRecs {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) (recs : List VRecursor) : (decl.withRecs recs).SourceWF env := H

end VerifyInductive
end Lean4Lean
