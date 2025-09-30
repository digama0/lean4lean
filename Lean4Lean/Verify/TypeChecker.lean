import Lean4Lean.Verify.TypeChecker.InferType
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.TypeChecker.IsDefEq

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

structure VEnvs where
  venv : DefinitionSafety → VEnv

structure VEnvs.WF (env : Environment) (ves : VEnvs) where
  tr : TrEnv safety env (ves.venv safety)
  hasPrimitives : VEnv.HasPrimitives (ves.venv safety)
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → isAsSafeAs .safe ci ∧ ci.levelParams = []

namespace TypeChecker
open Inner

theorem Methods.withFuel.WF : ∀ {n}, (withFuel n).WF
  | 0 =>
    { isDefEqCore _ _ := .throw
      whnfCore _ := .throw
      whnf _ := .throw
      inferType _ _ := .throw }
  | n + 1 =>
    have := withFuel.WF (n := n)
    { isDefEqCore h1 h2 := isDefEqCore'.WF h1 h2 _ this
      whnfCore h1 := whnfCore'.WF h1 _ this
      whnf h1 := whnf'.WF h1 _ this
      inferType h1 h2 := inferType'.WF h1 h2 _ this }

theorem RecM.WF.run {x : RecM α} (H : x.WF c s Q) : (RecM.run x).WF c s Q :=
  H _ Methods.withFuel.WF

def VContext.mk' {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety := .safe) (lparams : List Name := []) : VContext where
  env; safety; lparams
  venv := ves.venv safety
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  trenv := wf.tr
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl

theorem VState.WF.empty {env : Environment} {ves : VEnvs} {wf : ves.WF env}
    {safety : DefinitionSafety} {lparams : List Name} :
    VState.WF (.mk' wf safety lparams) {} where
  trctx := .nil
  ngen_wf := nofun
  ectx := ⟨[], .refl, trivial, .refl, .empty, nofun⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty

theorem M.WF.runU {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {x : M α} {Q} (H : x.WF (.mk' wf safety lparams) {} fun a _ => Q a) :
    (M.run env safety {} (withReader ({ · with lparams }) x)).WF Q := by
  intro a eq
  simp [run, withReader, withTheReader, MonadWithReaderOf.withReader, Functor.map,
    Except.map, StateT.run] at eq
  split at eq <;> cases eq; rename_i eq
  let ⟨_, _, _, _, H⟩ := H .empty _ _ eq
  exact H

theorem M.WF.run {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {x : M α} {Q} (H : x.WF (.mk' wf safety) {} fun a _ => Q a) :
    (M.run env safety {} x).WF Q := H.runU wf

nonrec theorem whnf.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (whnf e) fun e₁ _ => c.TrExpr e₁ e' :=
  (whnf.WF he).run.mono fun _ _ _ h => h.2

nonrec theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (inferType e) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' :=
  (inferType.WF he).run

nonrec theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (checkType e) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  (checkType.WF h1).run

nonrec theorem isDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    M.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  (isDefEq.WF he₁ he₂).run

nonrec theorem isProp.WF {c : VContext} {s : VState}
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ => b → c.HasType e' (.sort .zero) :=
  (isProp.WF he).run

nonrec theorem ensureSort.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (ensureSort e e₀) fun e1 _ => c.TrExpr e1 e' ∧ ∃ u, e1 = .sort u :=
  (ensureSortCore.WF he).run.mono fun _ _ _ h => ⟨h.2.1, h.1⟩

nonrec theorem ensureForall.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (ensureForall e) fun e1 _ =>
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  (ensureForallCore.WF he).run.mono fun _ _ _ h => h.2

nonrec theorem ensureType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (ensureType e) fun e1 _ => ∃ e', c.TrExprS e e' ∧ ∃ u u', e1 = .sort u ∧
      VLevel.ofLevel c.lparams u = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF he).bind fun _ _ _ ⟨_, _, a1, a2, a3⟩ => ?_
  refine (ensureSort.WF a2).mono fun _ _ _ ⟨⟨_, b1, b2⟩, b3⟩ => ?_
  obtain ⟨_, rfl⟩ := b3; let .sort b1 := b1
  exact ⟨_, a1, _, _, rfl, b1, a3.defeqU_r c.Ewf c.Δwf b2.symm⟩
