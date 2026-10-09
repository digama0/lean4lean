import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.ExprUniverses

/-! Universe substitution in translations, used to drop the recursor's elimination universe.

`TrExprS.substLevelParamsCore` instantiates the universe parameters of a translated term
with the executable's non-reducing level substitution. Its instance
`TrExprS.dropFreshLevelParam` replaces the extra elimination universe of a recursor
context by zero and leaves the declaration's universe parameters unchanged, which brings a
translation over the recursor's universe parameters back to the declaration's. -/

namespace Lean4Lean
open Lean hiding Environment Exception

/-- Translations are preserved by the executable's non-reducing level substitution
(`instantiateLevelParamsCore' false`), provided it agrees with the abstract instantiation
`ls` on every level of the source. Because the substitution does not simplify, the other
universe expressions of the term are kept as they are. -/
theorem TrExprS.substLevelParamsCore
    (hΔ : VLCtx.WF env ps.length Δ)
    (hls : ∀ level ∈ ls, level.WF Us.length)
    (hlevels : ∀ u u', VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F false) = some (u'.inst ls))
    (H : TrExprS env ps Δ e e') :
    TrExprS env Us (Δ.instL ls) (Expr.instantiateLevelParamsCore' false F e)
      (e'.instL ls) := by
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (hlevels _ _ hlevel)
  | @const _ _ sourceLevels targetLevels info hlookup hlevel harity =>
    apply TrExprS.const hlookup ?_ (by simpa using harity)
    have Hmap := List.mapM_eq_some.mp hlevel
    apply List.mapM_eq_some.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.imp (fun u u' hu => hlevels u u' hu) Hmap
  | app hfn harg _ _ ihFn ihArg =>
    exact .app (VLCtx.instL_toCtx _ ▸ hfn.instL hls)
      (VLCtx.instL_toCtx _ ▸ harg.instL hls) (ihFn hΔ) (ihArg hΔ)
  | lam hdom _ _ ihDom ihBody =>
    exact .lam (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (ihDom hΔ) (ihBody ⟨hΔ, nofun, hdom⟩)
  | forallE hdom hbody _ _ ihDom ihBody =>
    exact .forallE (VLCtx.instL_toCtx _ ▸ hdom.instL hls)
      (VLCtx.instL_toCtx _ ▸ hbody.instL hls)
      (ihDom hΔ) (ihBody ⟨hΔ, nofun, hdom⟩)
  | letE hval _ _ _ ihTy ihVal ihBody =>
    exact .letE (VLCtx.instL_toCtx _ ▸ hval.instL hls)
      (ihTy hΔ) (ihVal hΔ) (ihBody ⟨hΔ, nofun, hval⟩)
  | lit hlit _ ih =>
    exact .lit hlit (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ hproj ih =>
    exact .proj (ih hΔ) (VLCtx.instL_toCtx _ ▸ hproj.instL hls)

/-- Replace the extra elimination universe `fresh` by zero and leave every other universe
parameter unchanged. -/
def recursorDropLevel (fresh : Name) (name : Name) : Level :=
  if name = fresh then .zero else .param name

def recursorDropLevels (n : Nat) : List VLevel := .zero :: VLevel.params n

theorem levelParamsIn_fixed_dropFresh {e : Expr}
    (H : e.levelParamsIn Us = true) (hfresh : fresh ∉ Us) :
    Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e = e := by
  apply Expr.levelParamsIn_subst_fixed H
  intro name hname
  simp [recursorDropLevel, show name ≠ fresh from fun heq => hfresh (heq ▸ hname)]

theorem recursorDropLevels_wf : ∀ level ∈ recursorDropLevels n, level.WF n := by
  simp only [recursorDropLevels, List.mem_cons, forall_eq_or_imp]
  exact ⟨True.intro, fun _ h => VLevel.params_wf h⟩

theorem ofLevel_dropFresh
    (H : VLevel.ofLevel (fresh :: Us) u = some u') :
    VLevel.ofLevel Us (u.substParams' (recursorDropLevel fresh) false) =
      some (u'.inst (recursorDropLevels Us.length)) := by
  induction u generalizing u' with
  | zero =>
    simp only [VLevel.ofLevel] at H
    cases H
    rfl
  | succ u ih =>
    simp only [VLevel.ofLevel, bind] at H
    obtain ⟨target, htarget, ⟨⟩⟩ := Option.bind_eq_some_iff.mp H
    simpa [Level.substParams', VLevel.ofLevel, VLevel.inst] using ih htarget
  | max left right ihLeft ihRight | imax left right ihLeft ihRight =>
    simp only [VLevel.ofLevel, bind] at H
    obtain ⟨leftTarget, hleft, hrest⟩ := Option.bind_eq_some_iff.mp H
    obtain ⟨rightTarget, hright, ⟨⟩⟩ := Option.bind_eq_some_iff.mp hrest
    simp [Level.substParams', VLevel.ofLevel, VLevel.inst, ihLeft hleft, ihRight hright]
  | param name =>
    by_cases heq : name = fresh
    · subst name
      simp [VLevel.ofLevel] at H
      cases H
      simp [Level.substParams', recursorDropLevel, recursorDropLevels, VLevel.ofLevel, VLevel.inst]
    · have hbeq : (fresh == name) = false := by
        simp [show fresh ≠ name from Ne.symm heq]
      simp [VLevel.ofLevel, List.idxOf_cons, hbeq] at H
      obtain ⟨hindex, rfl⟩ := H
      simp [Level.substParams', recursorDropLevel, heq, VLevel.ofLevel, hindex,
        VLevel.inst, recursorDropLevels, VLevel.params, List.getD_eq_getElem?_getD]
  | mvar => simp [VLevel.ofLevel] at H

theorem TrExprS.dropFreshLevelParam
    (hΔ : VLCtx.WF env (fresh :: Us).length Δ)
    (H : TrExprS env (fresh :: Us) Δ e e') :
    TrExprS env Us (Δ.instL (recursorDropLevels Us.length))
      (Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e)
      (e'.instL (recursorDropLevels Us.length)) :=
  H.substLevelParamsCore hΔ recursorDropLevels_wf
    (fun _ _ hu => ofLevel_dropFresh hu)

theorem VLCtx.WF.instL_id (H : VLCtx.WF env U Δ) :
    Δ.instL (VLevel.params U) = Δ := by
  induction Δ with
  | nil => rfl
  | cons entry Δ ih =>
    obtain ⟨ofv, d⟩ := entry
    have hctx := OnCtx.levelWF_of_isType H.1.toCtx
    have htail := ih H.1
    cases d with
    | vlam ty =>
      obtain ⟨level, htype⟩ := H.2.2
      have hlevels := (htype.levelWF hctx).1
      simp [VLCtx.instL, VLocalDecl.instL, htail, hlevels.instL_id]
    | vlet ty value =>
      have hlevels := H.2.2.levelWF hctx
      simp [VLCtx.instL, VLocalDecl.instL, htail, hlevels.1.instL_id, hlevels.2.2.instL_id]

theorem recursorDropLevels_prependShift :
    (VLevel.prependShift n).map (VLevel.inst (recursorDropLevels n)) = VLevel.params n := by
  simp only [VLevel.prependShift, VLevel.params, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  simp [VLevel.inst, recursorDropLevels, VLevel.params,
    List.getD_eq_getElem?_getD, hi']

theorem VLCtx.instL_instL {Δ : VLCtx} :
    (Δ.instL ls).instL ls' = Δ.instL (ls.map (VLevel.inst ls')) := by
  induction Δ with
  | nil => rfl
  | cons entry Δ ih =>
    obtain ⟨ofv, d⟩ := entry
    cases d <;> simp [VLCtx.instL, VLocalDecl.instL, ih, VExpr.instL_instL]

theorem VLCtx.WF.prepend_drop_levels (H : VLCtx.WF env U Δ) :
    (Δ.instL (VLevel.prependShift U)).instL (recursorDropLevels U) = Δ := by
  rw [VLCtx.instL_instL, recursorDropLevels_prependShift, H.instL_id]

end Lean4Lean
