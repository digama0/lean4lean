import Lean4Lean.Primitive
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Inductive.Lowering

/-!
# The primitive declaration shapes

Primitive declarations are `Bool` and `Nat`, recognized by `Primitive.checkInductive`
(section 3.1 of the design notes). `PrimitiveInductiveShape` is the dispatch predicate: a
successful recognition has exactly the canonical `Bool` or `Nat` syntax
(`checkPrimitiveInductive_eq_true_iff`), so the primitive path is verified for two finite
declarations.

Wave 2 scaffold: owned by the `Install/`+`Primitive/`+`Prelude/` agent (source branch:
`Primitive/{Shape,Lowering}.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two declaration shapes for which the executable kernel checker enables
the primitive-name exception. This is an operational dispatch predicate, not
the abstract inductive well-formedness specification. -/
def PrimitiveInductiveShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  lparams = [] ∧ nparams = 0 ∧ isUnsafe = false ∧
    (types = [{
        name := ``Bool
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Bool.false, type := .const ``Bool [] },
          { name := ``Bool.true, type := .const ``Bool [] }] }] ∨
      ∃ binderName binderInfo,
        types = [{
          name := ``Nat
          type := .sort (.succ .zero)
          ctors := [
            { name := ``Nat.zero, type := .const ``Nat [] },
            { name := ``Nat.succ,
              type := .forallE binderName (.const ``Nat [])
                (.const ``Nat []) binderInfo }] }])

/-- Successful primitive recognition has exactly the canonical `Bool` or `Nat` syntax. In
particular the `true` branch is finite and can be verified separately from the ordinary
fresh-name pipeline. -/
theorem checkPrimitiveInductive_eq_true_iff
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) :
    Primitive.checkInductive env lparams nparams types isUnsafe = .ok true ↔
      PrimitiveInductiveShape lparams nparams types isUnsafe := by
  unfold Primitive.checkInductive PrimitiveInductiveShape
  constructor
  · intro h
    split at h
    · rename_i hpre
      have hpre' : (!isUnsafe && lparams.isEmpty && nparams == 0) = true :=
        hpre
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hpre'
      obtain ⟨⟨hisUnsafe, hlparams⟩, hnparams⟩ := hpre'
      have hisUnsafe' : isUnsafe = false := by
        cases isUnsafe <;> simp_all
      subst isUnsafe
      subst lparams
      subst nparams
      cases types with
      | nil =>
        simp only at h
        cases h
      | cons type tail =>
        cases tail with
        | cons other rest =>
          simp only at h
          cases h
        | nil =>
          simp only at h
          by_cases htype : (type.type == .sort (.succ .zero)) = true
          · rw [if_pos htype] at h
            by_cases hbool : type.name = ``Bool
            · simp only [hbool] at h
              split at h
              · rename_i _ hctors
                refine ⟨rfl, rfl, rfl, Or.inl ?_⟩
                congr 1
                have htypeEq : type.type = .sort (.succ .zero) :=
                  Expr.eqv_sort.mp htype
                cases type
                simp_all
              · change Except.error _ = Except.ok true at h
                cases h
            · by_cases hnat : type.name = ``Nat
              · simp only [hnat] at h
                split at h
                · rename_i _ binderName binderInfo hctors
                  refine ⟨rfl, rfl, rfl, Or.inr
                    ⟨binderName, binderInfo, ?_⟩⟩
                  congr 1
                  have htypeEq : type.type = .sort (.succ .zero) :=
                    Expr.eqv_sort.mp htype
                  cases type
                  simp_all
                · change Except.error _ = Except.ok true at h
                  cases h
              · simp only at h
                change Except.ok false = Except.ok true at h
                cases h
          · rw [if_neg htype] at h
            change Except.ok false = Except.ok true at h
            cases h
    · change Except.ok false = Except.ok true at h
      cases h
  · rintro ⟨rfl, rfl, rfl, hshape⟩
    rcases hshape with hbool | ⟨binderName, binderInfo, hnat⟩
    · subst types
      simp
      change Except.ok true = Except.ok true
      rfl
    · subst types
      simp
      change Except.ok true = Except.ok true
      rfl

theorem PrimitiveInductiveShape.types_nonempty
    (H : PrimitiveInductiveShape lparams nparams types isUnsafe) : types ≠ [] := by
  rcases H with ⟨-, -, -, h | ⟨_, _, h⟩⟩ <;> simp [h]

theorem PrimitiveInductiveShape.isUnsafe_eq
    (H : PrimitiveInductiveShape lparams nparams types isUnsafe) : isUnsafe = false := H.2.2.1

set_option linter.unusedSimpArgs false in
/-- Lowering a recognized primitive declaration is atomic: every successful
run returns the submitted Bool/Nat declaration unchanged and introduces no nested
auxiliaries.  This is proved from the executable lowering clauses for the two
finite primitive shapes; it does not assert validity for an intermediate
header-only context. -/
theorem ElimNestedInductive.run'.primitiveNoop
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (res : ElimNestedInductive.Result)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hout : ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }) = .ok res) :
    res.types = types ∧ res.aux2nested.size = 0 := by
  rcases Hshape with ⟨rfl, rfl, rfl, hshape⟩
  rcases hshape with rfl | ⟨binderName, binderInfo, rfl⟩
  all_goals
    cases fuel with
    | zero =>
      simp [StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
        ElimNestedInductive.run.loop, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        Functor.map, StateT.map, Except.map] at hout
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [StateT.run', ElimNestedInductive.run,
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
          ElimNestedInductive.isNestedInductiveApp?, Expr.replaceM,
          Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
          Expr.getAppArgs] at hout
      | succ fuel =>
        simp [StateT.run', ElimNestedInductive.run,
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
          ElimNestedInductive.isNestedInductiveApp?, Expr.replaceM,
          Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
          Expr.getAppArgs, LocalContext.mkForall] at hout
        subst res
        have habstract (e : Expr) : e.abstract #[] = e := by
          simpa [Expr.abstractN_nil] using Expr.abstractN_eq e []
        simp only [LocalContext.mkBinding, habstract]
        repeat' constructor <;> rfl

/-- The generated recursor names are not themselves primitive-reserved, even
on the finite `Bool`/`Nat` branch. -/
theorem PrimitiveInductiveShape.recursorsNonprimitive
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    ∀ owner (_howner : owner < types.toArray.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName types.toArray[owner]!.name) := by
  rcases Hshape with ⟨rfl, rfl, rfl, htypes | htypes⟩
  · subst types
    intro owner howner
    have : owner = 0 := by simpa using howner
    subst owner
    simp
    simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList,
      Lean.mkRecName]
  · rcases htypes with ⟨binderName, binderInfo, htypes⟩
    subst types
    intro owner howner
    have : owner = 0 := by simpa using howner
    subst owner
    simp
    simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList,
      Lean.mkRecName]

/-- The lowering run is the identity on a primitive declaration: no nested occurrence. -/
theorem loweringRun.primitiveNoop (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (loweringRun env fuel nparams types lparams).WF fun res =>
      res.types = types ∧ res.aux2nested.size = 0 :=
  fun res hout => ElimNestedInductive.run'.primitiveNoop env fuel lparams nparams types isUnsafe
    res Hshape hout

end VerifyInductive
end Lean4Lean
