import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Base
import Lean4Lean.Verify.Inductive.Nested.Lowering.Queue

/-! # Parameter uniformity of lowered constructor types (owner: Restoration-A)

The lowering-side lemmas of the source branch's `Nested/Restoration/Uniform/Recursors.lean`:
lowering an input that mentions no head produces a parameter-uniform output
(`ExprLowering.Resolved.paramUniform`), and a lowered constructor type is a parameter-uniform
parameter telescope (`ConstructorLowering.Resolved.paramUniformTele`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! ### Lowered constructor types -/

theorem _root_.Lean.Expr.AvoidsConsts.of_mem_getAppArgsList {names : List Name}
    {e : Expr} (h : e.AvoidsConsts names) :
    ∀ a ∈ e.getAppArgsList, a.AvoidsConsts names := by
  induction h with
  | app _ _ _ hx ihf _ =>
    intro a ha
    rw [Expr.getAppArgsList_app] at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ihf a ha
    · rw [List.mem_singleton.1 ha]; exact hx
  | _ => intro a ha; simp [Expr.getAppArgsList] at ha

/-- **Lowering produces parameter-uniform head occurrences.** The semantic lowering map
of an input that mentions no head produces an output that is parameter-uniform over the
opened parameters `As`: every replacement is
`mkAppN (.const auxName state.lvls) As` applied to untouched source arguments,
with `auxName` an auxiliary family (a key of `aux2nested`). -/
theorem ExprLowering.Resolved.paramUniform {heads : List Name} {ls : List Level}
    {env : Environment} {lctx : LocalContext} {params As : Array Expr}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {input : Expr} {state : Lean4Lean.ElimNestedInductive.State}
    {out : Expr × Lean4Lean.ElimNestedInductive.State}
    (H : ExprLowering.Resolved env lctx params As finalResult input state out)
    (hkeys : ∀ auxName nested, finalResult.aux2nested.find? auxName = some nested →
      auxName ∈ heads)
    (hin : input.AvoidsConsts heads) (hlvls : state.lvls = ls) :
    out.1.ParamUniform heads As.toList ls := by
  induction H with
  | occurrence Hnode =>
    rcases Hnode.mapping with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, hauxLevels, hhead, hlowered, hnested, hlookup⟩
    rw [hlowered, Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity,
      Lean.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append,
      hauxLevels, hlvls]
    refine Expr.ParamUniform.mkAppList_const_head (hkeys _ _ hlookup) fun a ha => ?_
    refine Expr.ParamUniform.of_avoidsConsts (hin.of_mem_getAppArgsList a ?_)
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop ha
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => cases hin with | const _ _ h => exact .const h
  | lit => exact .lit _
  | app Hnode Hfn Harg ihFn ihArg =>
    cases hin with
    | app _ _ hf ha =>
      simpa [Expr.updateApp!] using
        Expr.ParamUniform.app (ihFn hf hlvls) (ihArg ha (Hfn.lvls.trans hlvls))
  | lam Hnode Hdom Hbody ihDom ihBody =>
    cases hin with
    | lam _ _ _ _ hd hb =>
      simpa [Expr.updateLambdaE!] using
        Expr.ParamUniform.lam (ihDom hd hlvls) (ihBody hb (Hdom.lvls.trans hlvls))
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    cases hin with
    | forallE _ _ _ _ hd hb =>
      simpa [Expr.updateForallE!] using
        Expr.ParamUniform.forallE (ihDom hd hlvls) (ihBody hb (Hdom.lvls.trans hlvls))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    cases hin with
    | letE _ _ _ _ _ ht hv hb =>
      simpa [Expr.updateLet!] using
        Expr.ParamUniform.letE (ihType ht hlvls) (ihValue hv (Htype.lvls.trans hlvls))
          (ihBody hb (Hvalue.lvls.trans (Htype.lvls.trans hlvls)))
  | mdata Hnode Hbody ihBody =>
    cases hin with
    | mdata _ _ hb => simpa [Expr.updateMData!] using Expr.ParamUniform.mdata (ihBody hb hlvls)
  | proj Hnode Hbody ihBody =>
    cases hin with
    | proj _ _ _ hb => simpa [Expr.updateProj!] using Expr.ParamUniform.proj (ihBody hb hlvls)

theorem _root_.Lean.Expr.AvoidsConsts.instantiate1'_fvar {names : List Name} {e : Expr}
    (h : e.AvoidsConsts names) (fv : FVarId) (k : Nat) :
    (e.instantiate1' (.fvar fv) k).AvoidsConsts names := by
  induction h generalizing k with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · exact .bvar _
    · split
      · simp only [Expr.liftLooseBVars']; exact .fvar _
      · exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const _ _ h => exact .const _ _ h
  | app _ _ _ _ ihf iha => exact .app _ _ (ihf k) (iha k)
  | lam _ _ _ _ _ _ iht ihb => exact .lam _ _ _ _ (iht k) (ihb (k + 1))
  | forallE _ _ _ _ _ _ iht ihb => exact .forallE _ _ _ _ (iht k) (ihb (k + 1))
  | letE _ _ _ _ _ _ _ _ iht ihv ihb =>
    exact .letE _ _ _ _ _ (iht k) (ihv k) (ihb (k + 1))
  | lit _ h _ => exact .lit _ h
  | mdata _ _ _ ih => exact .mdata _ _ (ih k)
  | proj _ _ _ _ ih => exact .proj _ _ _ (ih k)

/-- Opening a parameter telescope with free variables keeps name avoidance. -/
theorem LoweringParamOpening.tailAvoidsConsts {names : List Name}
    {lctx : LocalContext} {params : Array Expr} {type : Expr} {n : Nat}
    {outLctx : LocalContext} {tail : Expr} {outParams : Array Expr}
    (H : LoweringParamOpening lctx params type n outLctx tail outParams)
    (h : type.AvoidsConsts names) : tail.AvoidsConsts names := by
  induction H with
  | done => exact h
  | step _ ih =>
    cases h with
    | forallE _ _ _ _ _ hb =>
      apply ih
      rw [Expr.instantiate1_eq]
      exact hb.instantiate1'_fvar _ 0

/-- **Lowered constructor types are parameter-uniform parameter telescopes**, given
that the constructor's source type mentions no head, every key of the final
`aux2nested` map is a head, and the lowering state carries the levels `ls`. -/
theorem ConstructorLowering.Resolved.paramUniformTele {heads : List Name} {ls : List Level}
    {env : Environment} {params : Array Expr} {nparams : Nat}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {source : Constructor} {state : Lean4Lean.ElimNestedInductive.State}
    {out : Constructor × Lean4Lean.ElimNestedInductive.State}
    (H : ConstructorLowering.Resolved env params nparams finalResult source state out)
    (hkeys : ∀ auxName nested, finalResult.aux2nested.find? auxName = some nested →
      auxName ∈ heads)
    (hsource : source.type.AvoidsConsts heads) (hlvls : state.lvls = ls) :
    Expr.ParamUniformTele heads nparams ls out.1.type := by
  obtain ⟨lctx, tail, As, lowered, openedState, Hopen, -, Hselection, hnodup, -, -, -,
    hsize, Hmap, htype⟩ := H.mapped
  have hopenedLvls : openedState.lvls = ls := by
    rw [← Hmap.lvls, H.lvls, hlvls]
  have Hlowered := Hmap.paramUniform hkeys (Hopen.tailAvoidsConsts hsource) hopenedLvls
  rw [htype, ← hsize]
  refine Expr.ParamUniform.mkForall_params Hlowered
    (by have h := congrArg Array.toList Hselection.expressions; simpa using h)
    hnodup fun x hx => ?_
  obtain ⟨index, name, type, bi, kind, hfind⟩ := Hselection.declarations x hx
  exact ⟨index, x, name, type, bi, kind, hfind⟩

private theorem not_mem_of_not_reserved {heads : List Name}
    (hheads : ∀ h ∈ heads, (`_nested).isPrefixOf h = true) {c : Name}
    (hc : (`_nested).isPrefixOf c = false) : c ∉ heads := fun h => by
  rw [hheads c h] at hc; cases hc

/-- Literals expand to constructor applications of `Nat`, `Char`, `List` and
`String`, none of which is reserved. -/
theorem avoidsConsts_lit_of_reserved {heads : List Name}
    (hheads : ∀ h ∈ heads, (`_nested).isPrefixOf h = true) (l : Literal) :
    (Expr.lit l).AvoidsConsts heads := by
  have hnat : ∀ n : Nat, (Expr.lit (.natVal n)).AvoidsConsts heads := by
    intro n
    induction n with
    | zero =>
      exact .lit _ (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
    | succ n ih =>
      exact .lit _ (.app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide))) ih)
  cases l with
  | natVal n => exact hnat n
  | strVal s =>
    refine .lit _ ?_
    simp only [Literal.toConstructor, Expr.strLitToConstructor]
    refine .app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide))) ?_
    induction s.toList with
    | nil =>
      exact .app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
        (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
    | cons ch rest ih =>
      exact .app _ _ (.app _ _ (.app _ _
        (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
        (.const _ _ (not_mem_of_not_reserved hheads (by decide))))
        (.app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide))) (hnat _))) ih

end VerifyInductive
end Lean4Lean
