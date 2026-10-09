import Lean4Lean.Verify.Inductive.Primitive.ConstructorParams
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations

/-!
# Lowering is the identity on primitive declarations

Nested lowering of a recognized `Bool` or `Nat` declaration returns it unchanged with no
auxiliary families (`ElimNestedInductive.run'.primitiveNoop`), so the primitive path never
reaches the nested pipeline.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

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

/-- Predicate-transformer form of `primitiveNoop`, suitable for direct
composition with the source-check and lowering prefixes. -/
theorem ElimNestedInductive.run'.primitiveNoopWF
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }).WF fun res =>
        res.types = types ∧ res.aux2nested.size = 0 :=
  fun res hout => primitiveNoop env fuel lparams nparams types isUnsafe res
    Hshape hout

end VerifyInductive
end Lean4Lean
