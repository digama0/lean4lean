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

theorem M.WF.run {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {x : M α} {Q} (H : x.WF (.mk' wf safety lparams) {} fun a _ => Q a) :
    (M.run env safety {} lparams x).WF Q := by
  intro a eq
  simp [M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  let ⟨_, _, _, _, H⟩ := H .empty _ _ eq
  exact H

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

/- See [axioms.md](../../axioms.md) for an explanation of all these axioms -/
/--
info: 'Lean4Lean.TypeChecker.checkType.WF' depends on axioms:
[propext,
 Classical.choice,
 Lean4Lean.TrProj,
 Lean4Lean.ptrEqConstantInfo_eq,
 Lean4Lean.ptrEqExpr_eq,
 Quot.sound,
 Lean.Expr.abstractRange_eq,
 Lean.Expr.abstract_eq,
 Lean.Expr.eqv_eq,
 Lean.Expr.hasLevelParam_eq,
 Lean.Expr.hasLooseBVar_eq,
 Lean.Expr.instantiate1_eq,
 Lean.Expr.instantiateRange_eq,
 Lean.Expr.instantiateRevRange_eq,
 Lean.Expr.instantiateRev_eq,
 Lean.Expr.instantiate_eq,
 Lean.Expr.looseBVarRange_eq,
 Lean.Expr.lowerLooseBVars_eq,
 Lean.Expr.replace_eq,
 Lean.Level.hasMVar_eq,
 Lean.Level.hasParam_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Level.isEquiv'_wf,
 Lean.PersistentArray.toList'_push,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.Substring.beq_refl,
 Lean.Syntax.structEq_eq,
 Lean4Lean.TrProj.defeqDFC,
 Lean4Lean.TrProj.instL,
 Lean4Lean.TrProj.instN,
 Lean4Lean.TrProj.uniq,
 Lean4Lean.TrProj.weak',
 Lean4Lean.TrProj.weak'_inv,
 Lean4Lean.TrProj.wf,
 Lean4Lean.VEnv.addInduct,
 Lean4Lean.VEnv.addInduct_WF,
 Lean4Lean.VInductDecl.WF,
 Lean.Expr.mkAppRangeAux.eq_def,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.VEnv.IsDefEq.uniq,
 Lean4Lean.VEnv.IsDefEqU.forallE_inv,
 Lean4Lean.VEnv.IsDefEqU.weakN_inv,
 Lean4Lean.TypeChecker.Inner.inferProj.WF,
 Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF,
 Lean4Lean.TypeChecker.Inner.reduceProj.WF,
 Lean4Lean.TypeChecker.Inner.reduceRecursor.WF,
 Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkType.WF
