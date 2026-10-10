import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Lowered

/-! # Forall binders of generated recursors (owner: Restoration-A)

The generic part of the source branch's `Nested/Restoration/Validation/StrippedRecursorShapes.lean`:
forall binders under instantiation and replacement, the head constant of a translated
application, the major binder of a generated recursor (`RecursorInstallation.generated_majorBinder`),
and parameter uniformity of a binder domain. The `NestedRun` part (the major inductive of a
restored recursor, the shapes of the stripped recursors) follows once the run is ported. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open InductiveSignature

namespace VerifyInductive

/-- Local copies of two lemmas of the source branch's `Restoration/ContainerSpecializations.lean`
(Restoration-B), kept private here to avoid a duplicate declaration. -/
private theorem getAppFn_abstractN_const_aux {e : Expr} {xs : List FVarId} {k : Nat}
    {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.abstractN xs k).getAppFn = .const n ls := by
  induction e generalizing k with
  | app f a ihf _ =>
    simp only [Expr.abstractN, Expr.getAppFn] at H ⊢
    exact ihf H
  | const => simpa [Expr.abstractN] using H
  | _ => simp [Expr.getAppFn] at H

private theorem getAppFn_instantiate1'_of_const_aux {e s : Expr} {d : Nat}
    {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.instantiate1' s d).getAppFn = .const n ls := by
  induction e generalizing d with
  | app f a ihf _ =>
    simp only [Expr.instantiate1', Expr.getAppFn] at H ⊢
    exact ihf H
  | const => simpa [Expr.instantiate1'] using H
  | _ => simp [Expr.getAppFn] at H

/-! ### Forall binders under instantiation and replacement -/

theorem Expr.ForallBinderAt.instantiate1'
    (H : Expr.ForallBinderAt source i domain) (a : Expr) (k : Nat := 0) :
    Expr.ForallBinderAt (source.instantiate1' a k) i
      (domain.instantiate1' a (k + i)) := by
  induction H generalizing k with
  | @here name domain body bi =>
      simpa [Expr.instantiate1'] using
        (Expr.ForallBinderAt.here (name := name)
          (body := body.instantiate1' a (k + 1))
          (bi := bi) (domain := domain.instantiate1' a k))
  | @there body i domain name outerDomain bi H ih =>
      have Htail := ih (k + 1)
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain.instantiate1' a k)
        (bi := bi) Htail
      simpa [Expr.instantiate1', Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Hresult

theorem Expr.ForallBinderAt.instantiateRevList
    (H : Expr.ForallBinderAt source i domain) (as : List Expr) (k : Nat := 0) :
    Expr.ForallBinderAt (source.instantiateRevList as k) i
      (domain.instantiateRevList as (k + i)) := by
  induction as with
  | nil => simpa using H
  | cons a as ih =>
      simpa only [Expr.instantiateRevList] using ih.instantiate1' a k

theorem Expr.getAppFn_instantiateRevList_of_const {e : Expr} {as : List Expr}
    {k : Nat} {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.instantiateRevList as k).getAppFn = .const n ls := by
  induction as with
  | nil => simpa using H
  | cons a as ih =>
      simp only [Expr.instantiateRevList]
      exact getAppFn_instantiate1'_of_const_aux ih

/-- A forall prefix followed by a binder selects that binder of the
residual. -/
theorem Expr.ForallTelescope.dropBinderAt
    (Hprefix : Expr.ForallTelescope outer n middle)
    (Hbinder : Expr.ForallBinderAt outer (n + i) domain) :
    Expr.ForallBinderAt middle i domain := by
  induction Hprefix with
  | nil => simpa using Hbinder
  | @cons body arity result name dom bi Hprefix ih =>
      have : arity + 1 + i = (arity + i) + 1 := by omega
      rw [this] at Hbinder
      cases Hbinder with
      | there H => exact ih H

/-- A replacement which never fires at a forall node keeps every forall
binder, replacing its domain. -/
theorem ExprReplacement.binderAt
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Hbinder : Expr.ForallBinderAt input i domain) :
    ∃ domain', Expr.ForallBinderAt output i domain' ∧
      ExprReplacement replaceNode domain domain' := by
  induction Hbinder generalizing output with
  | @here name dom body bi =>
      cases Hreplace with
      | occurrence h => rw [Hnone] at h; contradiction
      | forallE h hdom hbody =>
          refine ⟨_, ?_, hdom⟩
          simpa [Expr.updateForallE!] using
            (Expr.ForallBinderAt.here (name := name) (body := _) (bi := bi)
              (domain := _))
  | @there body i domain name outerDomain bi H ih =>
      cases Hreplace with
      | occurrence h => rw [Hnone] at h; contradiction
      | forallE h hdom hbody =>
          rcases ih hbody with ⟨domain', Hd, Hr⟩
          refine ⟨domain', ?_, Hr⟩
          simpa [Expr.updateForallE!] using
            (Expr.ForallBinderAt.there (name := name) (outerDomain := _)
              (bi := bi) Hd)

/-- The application head of a replaced expression: a constant head `c`
satisfying `Good` stays a constant head satisfying `Good`, provided every
replacement on the spine produces such a head. -/
theorem ExprReplacement.constHead {Good : Name → Prop}
    (Hhit : ∀ t out, (∃ ls, t.getAppFn = .const c ls) →
      replaceNode t = some out → ∃ c' ls', out.getAppFn = .const c' ls' ∧ Good c')
    (hc : Good c)
    (Hreplace : ExprReplacement replaceNode input output)
    (hhead : input.getAppFn = .const c ls) :
    ∃ c' ls', output.getAppFn = .const c' ls' ∧ Good c' := by
  induction Hreplace with
  | occurrence h => exact Hhit _ _ ⟨ls, hhead⟩ h
  | @const name levels h =>
      exact ⟨name, levels, rfl, by
        simp only [Expr.getAppFn, Expr.const.injEq] at hhead
        rw [hhead.1]; exact hc⟩
  | @app fn arg fn' arg' h hfn harg ihfn _ =>
      have hfnHead : fn.getAppFn = .const c ls := by
        simpa [Expr.getAppFn] using hhead
      rcases ihfn hfnHead with ⟨c', ls', hout, hgood⟩
      exact ⟨c', ls', by simpa [Expr.updateApp!, Expr.getAppFn] using hout, hgood⟩
  | bvar | fvar | mvar | sort | lit | lam | forallE | letE | mdata | proj =>
      simp [Expr.getAppFn] at hhead

/-- A translated concrete expression with a constant application head
translates to an application spine of the same constant. -/
theorem TrExprS.constHead_eq {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfn : e.getAppFn = .const c ls)
    (he' : e' = VExpr.mkApps (.const n us) args) : c = n := by
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at H
  rcases checkPositivityStep.TrExprS.mkAppList_inv H with ⟨fn', args', hfn', -, rfl⟩
  cases hfn' with
  | const _ _ _ =>
    have h := congrArg VExpr.getAppFnArgs he'
    rw [VExpr.getAppFnArgs_mkApps_const, VExpr.getAppFnArgs_mkApps_const] at h
    simp only [Prod.mk.injEq, VExpr.const.injEq] at h
    exact h.1.1

/-! ### The major binder of a generated recursor -/

/-- The domain at the major position of a generated recursor type is an
application of the owner family constant. -/
theorem RecursorInstallation.generated_majorBinder
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    ∃ domain, Expr.ForallBinderAt (H.generated.entry owner howner).info.type
        (H.generated.entry owner howner).info.getMajorIdx domain ∧
      domain.getAppFn = .const (decl.types[owner]'(by
        rw [← H.cardinality.records, ← H.generated.length]; exact howner)).name
        stats.levels := by
  have hrecInfo : owner < H.recInfos.size := by
    rw [← H.generated.length]; exact howner
  let E := H.generated.entry owner howner
  let S := H.bindings.toRecursorBinderGroups H.localWF H.params owner hrecInfo
  have hnoalias : S.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  obtain ⟨D⟩ := (H.bindings.major owner hrecInfo).declarationAt H.localWF 0 (by simp)
  have Hbinder := S.majorBinderAt hnoalias D
  dsimp only at Hbinder
  rw [← E.type] at Hbinder
  have hidx : E.info.getMajorIdx = stats.params.size + (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size := by
    simp only [Lean.RecursorVal.getMajorIdx, E.numParams, E.numMotives, E.numMinors,
      E.numIndices, H.arities owner hrecInfo]
  rw [← hidx] at Hbinder
  refine ⟨_, Hbinder, ?_⟩
  apply getAppFn_abstractN_const_aux
  rw [H.majorSourceType owner hrecInfo D]
  simp [Expr.getAppFn_mkAppN, Expr.getAppFn]

theorem _root_.Lean.Expr.ParamUniform.binderAt {heads : List Name} {params : List Expr}
    {ls : List Level} {e : Expr} (H : e.ParamUniform heads params ls)
    (Hbinder : Expr.ForallBinderAt e i domain) : domain.ParamUniform heads params ls := by
  induction Hbinder with
  | here => exact H.forallE_inv.1
  | there _ ih => exact ih H.forallE_inv.2

/-! ### The major inductive of a restored recursor -/

end VerifyInductive
end Lean4Lean
