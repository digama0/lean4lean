import Lean4Lean.Inductive.Add

/-! `whnf` returns a constant that has no definition to unfold unchanged, so the positivity
check classifies a field whose type is literally a valid application of a family constant as
recursive. The primitive path (`Bool`, `Nat`) reads its constructor classifications from these
facts, since its header environment carries no valid checking context. -/
namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- The `whnf` loop returns a constant without a definition unchanged. -/
theorem whnf'_loop_const_noDelta {n : Name} {us : List Level} {m : Methods} {ctx : Context}
    {s : State} {r : Expr} {s' : State} {fuel : Nat}
    (hdelta : Inner.isDelta ctx.env (.const n us) = none)
    (h : Inner.whnf'.loop (.const n us) fuel m ctx s = .ok (r, s')) : r = .const n us := by
  cases fuel with
  | zero => simp [Inner.whnf'.loop] at h; cases h
  | succ fuel =>
    have hnargs : (Expr.const n us).getAppNumArgs = 0 := rfl
    unfold Inner.whnf'.loop at h
    simp only [Inner.whnfCore', Inner.reduceNative, Inner.reduceNat,
      Inner.unfoldDefinition, Inner.unfoldDefinitionCore, Expr.isApp] at h
    simp [bind, ReaderT.bind, StateT.bind, Except.bind, getEnv, pure, ReaderT.pure,
      StateT.pure, Except.pure, liftM, monadLift, MonadLift.monadLift, read, MonadReader.read,
      MonadReaderOf.read, readThe, ReaderT.read, StateT.lift] at h
    rw [hnargs] at h
    simp [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
      StateT.pure, Except.pure, hdelta] at h
    exact h.1.symm

/-- `whnf'` returns a constant without a definition unchanged when its cache has no entry. -/
theorem whnf'_const_noDelta {n : Name} {us : List Level} {m : Methods} {ctx : Context}
    {s : State} {r : Expr} {s' : State}
    (hdelta : Inner.isDelta ctx.env (.const n us) = none)
    (hcache : s.whnfCache[Expr.const n us]? = none)
    (h : Inner.whnf' (.const n us) m ctx s = .ok (r, s')) : r = .const n us := by
  unfold Inner.whnf' at h
  simp [bind, ReaderT.bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure, get, getThe, MonadStateOf.get, StateT.get, hcache, liftM, monadLift,
    MonadLift.monadLift, readThe, MonadReaderOf.read, ReaderT.read, read, MonadReader.read,
    modify, modifyGet, MonadStateOf.modifyGet] at h
  generalize (if ctx.eagerReduce = true then ctx.fuel.whnfEager else ctx.fuel.whnf) = fuel at h
  cases hw : Inner.whnf'.loop (Expr.const n us) fuel m ctx s with
  | error e => simp [hw] at h
  | ok p =>
    obtain ⟨w, s2⟩ := p
    have hwc := whnf'_loop_const_noDelta hdelta hw
    subst hwc
    simp [hw] at h
    split at h <;> simp_all [ReaderT.bind, StateT.modifyGet, StateT.bind, ReaderT.pure, StateT.pure, bind, pure, Except.bind, Except.pure]
end Lean4Lean.TypeChecker

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- A run of `whnf` from the initial state returns a constant without a definition
unchanged. -/
theorem whnf_const_noDelta {n : Name} {us : List Level} {ctx : Context}
    {r : Expr} {s' : State}
    (hdelta : Inner.isDelta ctx.env (.const n us) = none)
    (h : TypeChecker.whnf (.const n us) ctx {} = .ok (r, s')) : r = .const n us := by
  unfold TypeChecker.whnf RecM.run Inner.whnf at h
  simp [bind, ReaderT.bind, StateT.bind, Except.bind, readThe, MonadReaderOf.read,
    ReaderT.read] at h
  change (Methods.withFuel ctx.fuel.recDepth).whnf (Expr.const n us) ctx {} = _ at h
  cases hd : ctx.fuel.recDepth with
  | zero => rw [hd] at h; cases h
  | succ d =>
    rw [hd] at h
    exact whnf'_const_noDelta hdelta (by simp) h
end Lean4Lean.TypeChecker

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Positivity on a constant that has no definition to unfold and is a valid application of
one of the families reports the field recursive. -/
theorem checkPositivity_const_valid {stats : AddInductive.InductiveStats} {n : Name}
    {us : List Level} {c : AddInductive.Context} {ctor : Name} {idx : Nat} {b : Bool} {k : Nat}
    (hdelta : TypeChecker.Inner.isDelta c.env (.const n us) = none)
    (hocc : AddInductive.hasIndOcc stats.indConsts (.const n us) = true)
    (hvalid : AddInductive.isValidIndApp? stats (.const n us) = some k)
    (h : AddInductive.checkPositivity stats (.const n us) ctor idx c = .ok b) : b = true := by
  unfold AddInductive.checkPositivity at h
  change AddInductive.checkPositivity.loop stats ctor idx (.const n us)
    c.fuel.inductiveFuel c = .ok b at h
  generalize c.fuel.inductiveFuel = fuel at h
  cases fuel with
  | zero => simp [AddInductive.checkPositivity.loop] at h
  | succ fuel =>
    unfold AddInductive.checkPositivity.loop at h
    simp only [bind, ReaderT.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i t ht
      have ht' : t = .const n us := by
        simp only [liftM, monadLift, MonadLift.monadLift, TypeChecker.M.run, StateT.run'] at ht
        cases hw : TypeChecker.whnf (.const n us)
            { env := c.env, safety := c.safety, lctx := c.checkLCtx,
              lparams := c.typeCheckerLParams.getD c.lparams, fuel := c.fuel } {} with
        | error e => rw [hw] at ht; cases ht
        | ok p =>
          rw [hw] at ht
          cases ht
          exact TypeChecker.whnf_const_noDelta hdelta hw
      subst ht'
      simp [AddInductive.checkPositivityStep, hocc, hvalid] at h
      simp [pure, ReaderT.pure, Except.pure] at h
      exact h
end Lean4Lean.VerifyInductive
