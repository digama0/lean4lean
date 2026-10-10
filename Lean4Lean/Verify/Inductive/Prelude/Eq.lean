import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension
import Lean4Lean.Verify.Inductive.Prelude.EqSyntax
import Lean4Lean.Verify.Inductive.Prelude.EqReady

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! # Checking the prelude's `Eq` declaration

`Init.Prelude` declares `Eq` as an ordinary inductive, before any quotient. This file follows
that one declaration (`PreludeEqShape`) through the executable: the primitive Bool/Nat
recognizer rejects it, lowering leaves it unchanged, and the ordinary path of section 3.1 of
the design notes installs it. From the source translation of the installed declaration it
derives that every safety-indexed model of the output contains abstract `Eq` with the prelude's
type (`QuotReadyEnvs`). PR #43 derives `QuotReady` at quotient initialization from
`checkEqType`, so this is not needed by `addDecl.WF`; the canonical `Eq.rec` facts
(`HasCanonicalEq`) of the source branch stay with `Tests/PreludeEq` (wave 4). -/

namespace VerifyInductive

private theorem vconstant_eq_of_fields {a b : VConstant}
    (huvars : a.uvars = b.uvars) (htype : a.type = b.type) : a = b := by
  cases a
  cases b
  simp_all

/-- The exact syntax of the prelude's ordinary (non-primitive) `Eq`
declaration, modulo binder and universe-parameter names.  As
submitted by `Init.Prelude`, `Eq` has two parameters (`α` and the left
endpoint `a`) and one index (the right endpoint), so `nparams = 2`. -/
def PreludeEqShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  ∃ u alphaName lhsName rhsName reflAlphaName reflValueName,
    lparams = [u] ∧ nparams = 2 ∧ isUnsafe = false ∧
    types = [{
      name := ``Eq
      type := preludeEqType u alphaName lhsName rhsName
      ctors := [{
        name := ``Eq.refl
        type := preludeEqReflType u reflAlphaName reflValueName }] }]

/-- The source translation of the exact prelude `Eq` declaration fixes the
abstract declaration: one family `Eq` with the stored type of `Eq`, one
constructor `Eq.refl` with the stored type of `Eq.refl`, two parameters. -/
theorem TrInductDeclCore.preludeEqDecl
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    ∃ family refl, decl.types = [family] ∧ family.name = ``Eq ∧
      family.toVConstant = ⟨1, canonicalEqType⟩ ∧ family.ctors = [refl] ∧
      refl.name = ``Eq.refl ∧ refl.toVConstant = ⟨1, canonicalEqReflType⟩ ∧
      decl.nparams = 2 := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  rcases List.Forall₂.leftSingleton H.types with ⟨family, hdecl, Hfamily⟩
  rcases List.Forall₂.leftSingleton Hfamily.ctors with ⟨refl, hctors, Hrefl⟩
  refine ⟨family, refl, hdecl, Hfamily.header.name, ?_, hctors, Hrefl.name, ?_,
    H.nparams⟩
  · apply vconstant_eq_of_fields
    · simpa using Hfamily.header.uvars
    · exact TrExprS.eq_canonicalEqType Hfamily.header.type
  · apply vconstant_eq_of_fields
    · simpa using Hrefl.uvars
    · exact TrExprS.eq_canonicalEqReflType Hrefl.type

/-- The installed model of the prelude's `Eq` contains abstract `Eq` with its canonical type. -/
theorem SourceAddInduct.quotReady
    (H : SourceAddInduct base lparams nparams types isUnsafe out)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) : out.QuotReady := by
  obtain ⟨family, -, hdeclTypes, hfamilyName, hfamilyConst, -⟩ :=
    TrInductDeclCore.preludeEqDecl H.source Hshape
  have hmem : (family.name, family.toVConstVal.toVConstant) ∈ H.decl.consts := by
    simp [VInductDecl.consts, hdeclTypes]
  have h := VEnv.addInduct_constants_mem H.installed hmem
  rw [hfamilyName] at h
  rw [VEnv.QuotReady, h, show family.toVConstVal.toVConstant = family.toVConstant from rfl,
    hfamilyConst]
  rfl

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

set_option linter.unusedSimpArgs false in
/-- Nested-inductive lowering is a literal no-op for the prelude `Eq`
syntax: its recursive constructor occurrence is the family currently being
defined, not a nested occurrence through another inductive. -/
theorem ElimNestedInductive.run'.preludeEqNoop
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (res : ElimNestedInductive.Result)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe)
    (hAbsent : env.find? ``Eq = none)
    (hout : ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }) = .ok res) :
    res.types = types ∧ res.aux2nested.size = 0 := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  have hheaderInstantiate (fv : FVarId) :
      (Expr.forallE lhsName (.bvar 0)
        (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default).instantiate1'
          (.fvar fv) =
        Expr.forallE lhsName (.fvar fv)
          (.forallE rhsName (.fvar fv) (.sort .zero) .default) .default := by
    rfl
  have hctorInstantiate (fv : FVarId) :
      (Expr.forallE reflValueName (.bvar 0)
        (.app (.app (.app (.const ``Eq [.param u]) (.bvar 1)) (.bvar 0))
          (.bvar 0)) .default).instantiate1' (.fvar fv) =
        Expr.forallE reflValueName (.fvar fv)
          (.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.bvar 0))
            (.bvar 0)) .default := by
    rfl
  have hctorBodyInstantiate (fv fv' : FVarId) :
      (Expr.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.bvar 0))
          (.bvar 0)).instantiate1' (.fvar fv') =
        Expr.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.fvar fv'))
          (.fvar fv') := by
    rfl
  have hclose (id id' : FVarId) (hne : id ≠ id') :
      ((({} : LocalContext).mkLocalDecl id reflAlphaName
          (.sort (.param u)) .implicit).mkLocalDecl id' reflValueName
          (.fvar id) .default).mkForall #[.fvar id, .fvar id']
          (.app (.app (.app (.const ``Eq [.param u]) (.fvar id)) (.fvar id'))
            (.fvar id')) =
        preludeEqReflType u reflAlphaName reflValueName := by
    let lctx0 := ({} : LocalContext).mkLocalDecl id reflAlphaName
      (.sort (.param u)) .implicit
    let lctx := lctx0.mkLocalDecl id' reflValueName (.fvar id) .default
    have hmapWF : ({} : PersistentHashMap FVarId LocalDecl).WF := .empty
    have hid : lctx.find? id = some (.cdecl 0 id reflAlphaName
        (.sort (.param u)) .implicit .default) := by
      simp only [lctx, lctx0, LocalContext.mkLocalDecl, LocalContext.find?]
      rw [hmapWF.insert.find?_insert, hmapWF.find?_insert]
      simp [Ne.symm hne]
    have hid' : lctx.find? id' = some (.cdecl 1 id' reflValueName
        (.fvar id) .default .default) := by
      simp only [lctx, lctx0, LocalContext.mkLocalDecl, LocalContext.find?]
      rw [hmapWF.insert.find?_insert]
      simp
    have hfind : ∀ x ∈ [id, id'], ∃ decl, lctx.find? x = some decl := by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, hid⟩
      · exact ⟨_, hid'⟩
    have hnd : [id, id'].Nodup := by simp [hne]
    rw [LocalContext.mkForall]
    change LocalContext.mkBinding false _
      ⟨[id, id'].map Expr.fvar⟩ _ = _
    rw [LocalContext.mkBinding_eq' hfind hnd (by simp [Lean4Lean.Closed])
      (fun x hx d hd => by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl
        · rw [hid] at hd
          cases hd
          trivial
        · rw [hid'] at hd
          cases hd
          trivial)]
    rw [LocalContext.mkBindingList_eq_fold hfind hnd]
    simp [LocalContext.mkBindingList1, hid, hid', Expr.abstract1,
      preludeEqReflType, Ne.symm hne, hne]
  cases fuel with
  | zero =>
    simp [preludeEqType, preludeEqReflType, hheaderInstantiate, hAbsent, Lean.mkFreshId,
      getNGen, setNGen, StateT.run', ElimNestedInductive.run,
      ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
      ElimNestedInductive.run.loop, MonadExcept.throw,
      instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
      StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
      MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
      ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
      ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
      StateT.get, StateT.set, StateT.modifyGet, getThe, modifyGetThe,
      MonadState.get, MonadState.set, MonadState.modifyGet,
      MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet,
      instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
      instMonadStateOfStateTOfMonad, _root_.modify,
      Bind.bind, Monad.toBind, ReaderT.instMonad, StateT.instMonad,
      Except.instMonad, Pure.pure, Applicative.toPure,
      Applicative.toFunctor, Monad.toApplicative,
      Functor.map, StateT.map, Except.bind, Except.pure, Except.map] at hout
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [preludeEqType, preludeEqReflType, hheaderInstantiate, hctorInstantiate,
        hctorBodyInstantiate, hAbsent, Lean.mkFreshId,
        getNGen, setNGen, StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.run.loop, ElimNestedInductive.withParams,
        ElimNestedInductive.withParams.loop,
        ElimNestedInductive.lowerNext, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
        StateT.get, StateT.modifyGet, getThe, modifyGetThe,
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, instMonadStateOfMonadStateOf,
        instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
        _root_.modify, Bind.bind, Monad.toBind, ReaderT.instMonad,
        StateT.instMonad, Except.instMonad, Pure.pure,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        Except.bind, Except.pure, Except.map, Functor.map,
        ElimNestedInductive.lowerInductive,
        ElimNestedInductive.lowerConstructor,
        ElimNestedInductive.replaceAllNested,
        ElimNestedInductive.replaceIfNested,
        ElimNestedInductive.isNestedInductiveApp?,
        ElimNestedInductive.isNestedInductiveAppConst?, Expr.replaceM,
        Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
        Expr.getAppArgs] at hout
    | succ fuel =>
      simp [preludeEqType, preludeEqReflType, hheaderInstantiate, hctorInstantiate,
        hctorBodyInstantiate, hAbsent, Lean.mkFreshId,
        getNGen, setNGen, StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.run.loop, ElimNestedInductive.withParams,
        ElimNestedInductive.withParams.loop,
        ElimNestedInductive.lowerNext, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
        StateT.get, StateT.modifyGet, StateT.map, getThe, modifyGetThe,
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, instMonadStateOfMonadStateOf,
        instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
        _root_.modify, Bind.bind, Monad.toBind, ReaderT.instMonad,
        StateT.instMonad, Except.instMonad, Pure.pure,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        Except.bind, Except.pure, Except.map, Functor.map,
        ElimNestedInductive.lowerInductive,
        ElimNestedInductive.lowerConstructor,
        ElimNestedInductive.replaceAllNested,
        ElimNestedInductive.replaceIfNested,
        ElimNestedInductive.isNestedInductiveApp?,
        ElimNestedInductive.isNestedInductiveAppConst?, Expr.replaceM,
        Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
        Expr.getAppArgs] at hout
      subst res
      have habstract (e : Expr) : e.abstract #[] = e := by
        simpa [Expr.abstractN_nil] using Expr.abstractN_eq e []
      simp [preludeEqType, preludeEqReflType, habstract]
      constructor
      · exact hclose _ _ (by simp [NameGenerator.curr, NameGenerator.next])
      · rfl

/-- Predicate-transformer form of the exact `Eq` lowering no-op. -/
theorem ElimNestedInductive.run'.preludeEqNoopWF
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe)
    (hAbsent : env.find? ``Eq = none) :
    ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }).WF fun res =>
        res.types = types ∧ res.aux2nested.size = 0 :=
  fun res hout => preludeEqNoop env fuel lparams nparams types isUnsafe res
    Hshape hAbsent hout

/-- The exact prelude `Eq` syntax is necessarily dispatched through the
ordinary branch: it has one universe parameter and two inductive parameters
(`α` and the left endpoint), whereas primitive Bool/Nat recognition requires
both lists to be empty. -/
theorem checkPrimitiveInductive_eq_false_of_preludeEqShape
    (env : Environment)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    Primitive.checkInductive env lparams nparams types isUnsafe =
      .ok false := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  simp [Primitive.checkInductive]
  rfl

/-- `addInductive` on the prelude `Eq` declaration installs it through the ordinary branch:
the output models extend the source models, contain canonical `Eq` at every safety level, and
carry the source judgment of the submitted declaration. -/
theorem Environment.addInductive.preludeEqExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hAbsent : env.constants.find? ``Eq = none)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe false fuel).WF
      fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyEnvs ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
            nparams types false (ves'.venv .safe)) := by
  have hAbsentFind : env.find? ``Eq = none := by
    rw [Lean.Kernel.Environment.find?,
      (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hAbsent
  have hisUnsafe : isUnsafe = false := by
    obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := Hshape; exact h
  subst isUnsafe
  have hnonempty : types ≠ [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := Hshape; rw [h]; simp
  refine Environment.addInductive.WF env lparams nparams types false false fuel _
    fun res _ hres => ?_
  obtain ⟨htypes, haux⟩ := ElimNestedInductive.run'.preludeEqNoop env fuel.inductiveFuel
    lparams nparams types false res Hshape hAbsentFind hres
  refine (Environment.addInductiveAfterLowering.ordinaryExtensionModelWF env lparams nparams
    types false fuel res ves wf htypes hnonempty haux).mono fun _ ⟨ves', wf', hle, ⟨S⟩⟩ => ?_
  have hEq : (ves'.venv .safe).QuotReady := S.quotReady Hshape
  exact ⟨ves', wf', fun safety => (wf'.mono DefinitionSafety.le_safe).constants hEq, hle, ⟨S⟩⟩

end VerifyInductive
end Lean4Lean
