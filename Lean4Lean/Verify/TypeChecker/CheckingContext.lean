import Lean4Lean.Verify.TypeChecker.MLCtxLemmas
import Lean4Lean.Verify.Typing.CheckingContext
import Lean4Lean.Verify.LocalContext.SubContext

/-! Concrete checking contexts and their semantic embeddings into a main context. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Rebuilding a context from the declarations of a larger one, for the free
variables of a lambda-only `MLCtx` whose declarations it contains, gives back
that `MLCtx`'s local context. -/
theorem _root_.Lean.LocalContext.restrictTo_mlctx {env : VEnv} {Us : List Name}
    {l : LocalContext} {m : TypeChecker.MLCtx} (honly : MLCtxOnlyLams m) (hwf : m.WF env Us)
    (hsub : m.lctx.SubContextOf l) : l.restrictTo m.fvarList = m.lctx := by
  induction m with
  | nil => rfl
  | vlam id name ty ty' bi tail ih =>
    have htailMap : tail.lctx.fvarIdToDecl.WF := hwf.1.tr.1.map_wf
    have hfresh : tail.lctx.find? id = none := hwf.2.1
    have hsubTail : tail.lctx.SubContextOf l := by
      intro x d hd
      apply hsub x d
      change (tail.lctx.mkLocalDecl id name ty bi).find? x = some d
      rw [LocalContext.find?_mkLocalDecl htailMap]
      have hne : (id == x) = false := by
        cases h : id == x
        · rfl
        · have : id = x := LawfulBEq.eq_of_beq h
          subst this; rw [hfresh] at hd; cases hd
      rw [hne]; exact hd
    have ih' := ih honly.tail_vlam hwf.1 hsubTail
    have hself : (tail.lctx.mkLocalDecl id name ty bi).find? id =
        some (.cdecl tail.lctx.decls.size id name ty bi .default) := by
      rw [LocalContext.find?_mkLocalDecl htailMap]; simp
    obtain ⟨d', hd', heq⟩ := hsub id _ hself
    have hd'' : ∃ i, d' = .cdecl i id name ty bi .default := by
      cases d' with
      | cdecl i a b c d e =>
        simp only [LocalDecl.setIndex, LocalDecl.cdecl.injEq] at heq
        obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := heq
        exact ⟨i, rfl⟩
      | ldecl => simp [LocalDecl.setIndex] at heq
    obtain ⟨i, rfl⟩ := hd''
    unfold LocalContext.restrictTo at ih' ⊢
    rw [TypeChecker.MLCtx.fvarList, List.foldl_append, ih']
    simp only [List.foldl_cons, List.foldl_nil, hd']
    rfl
  | vlet => exact honly.vlet_false.elim

/-- The checker context and the main context of a semantic inductive-checker
context: a sub-context description of a candidate checker context `l`. -/
structure CheckBase (venv : VEnv) (Us : List Name) (main : TypeChecker.MLCtx)
    (lctx : LocalContext) (l : LocalContext) where
  m : TypeChecker.MLCtx
  wf : m.WF venv Us
  onlyLams : MLCtxOnlyLams m
  lctx_eq : m.lctx = l
  embed : ChkEmbeds venv Us.length m.vlctx main.vlctx
  sub : l.SubContextOf lctx

namespace CheckBase

variable {venv : VEnv} {Us : List Name} {main : TypeChecker.MLCtx} {lctx : LocalContext}

def cast {l l' : LocalContext} (B : CheckBase venv Us main lctx l) (h : l = l') :
    CheckBase venv Us main lctx l' where
  m := B.m
  wf := B.wf
  onlyLams := B.onlyLams
  lctx_eq := B.lctx_eq.trans h
  embed := B.embed
  sub := h ▸ B.sub

@[simp] theorem cast_m {l l' : LocalContext} (B : CheckBase venv Us main lctx l)
    (h : l = l') : (B.cast h).m = B.m := rfl

def nil (henv : VEnv.Ordered venv) (hmain : main.WF venv Us) :
    CheckBase venv Us main lctx {} where
  m := .nil
  wf := trivial
  onlyLams := .nil
  lctx_eq := rfl
  embed := .from_nil henv hmain.tr.wf main.noBV
  sub := .empty

/-- The bottom of the main context. -/
def ofMain (henv : VEnv.Ordered venv) (hmain : main.WF venv Us) (honly : MLCtxOnlyLams main)
    (hlctx : main.lctx = lctx) (j : Nat) (hj : j ≤ main.length) :
    CheckBase venv Us main lctx (main.dropN j hj).lctx where
  m := main.dropN j hj
  wf := hmain.dropN j hj
  onlyLams := honly.dropN j hj
  lctx_eq := rfl
  embed := .of_fvLift (honly.dropN_fvlift j hj).toFVLift' (.refl henv hmain.tr.wf)
  sub := by
    intro fv d hd
    have hmem : fv ∈ (main.dropN j hj).vlctx.fvars :=
      ((hmain.dropN j hj).tr.find?_eq_some).1 ⟨d, hd⟩
    refine ⟨d, ?_, rfl⟩
    rw [← hlctx, honly.dropN_find?_eq hmain j hj hmem]
    exact hd

/-- The bottom of an embedded checker context. -/
def below {l : LocalContext} (B : CheckBase venv Us main lctx l) (j : Nat) (hj : j ≤ B.m.length) :
    CheckBase venv Us main lctx (B.m.dropN j hj).lctx where
  m := B.m.dropN j hj
  wf := B.wf.dropN j hj
  onlyLams := B.onlyLams.dropN j hj
  lctx_eq := rfl
  embed := .of_fvLift (B.onlyLams.dropN_fvlift j hj).toFVLift' B.embed
  sub := by
    intro fv d hd
    have hmem : fv ∈ (B.m.dropN j hj).vlctx.fvars :=
      ((B.wf.dropN j hj).tr.find?_eq_some).1 ⟨d, hd⟩
    have h1 : B.m.lctx.find? fv = some d := by
      rw [B.onlyLams.dropN_find?_eq B.wf j hj hmem]; exact hd
    rw [B.lctx_eq] at h1
    exact B.sub fv d h1

/-- A checker base stays a checker base when the main context is extended by
one fresh lambda declaration. -/
def skip {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (henv : VEnv.Ordered venv) (hmain : main.WF venv Us)
    (hlctx : main.lctx = lctx)
    {id : FVarId} {name : Name} {ty : Expr} {ty' : VExpr} {bi : BinderInfo}
    (hwf' : (TypeChecker.MLCtx.vlam id name ty ty' bi main).WF venv Us) :
    CheckBase venv Us (.vlam id name ty ty' bi main) (lctx.mkLocalDecl id name ty bi) l where
  m := B.m
  wf := B.wf
  onlyLams := B.onlyLams
  lctx_eq := B.lctx_eq
  embed := B.embed.skip henv (hmain.tr.find?_eq_none.1 hwf'.2.1) hwf'.2.2.1.fvarsList hwf'.2.2.2
  sub := B.sub.mkLocalDecl_right (by rw [← hlctx]; exact hmain.tr.1.map_wf)
    (by rw [← hlctx]; exact hwf'.2.1)

/-- Open one checked binder on top of a checker base. -/
def cons {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (henv : VEnv.WF venv)
    {id : FVarId} {name : Name} {ty : Expr} {ty' ty₀ : VExpr} {bi : BinderInfo}
    (hlctx : main.lctx = lctx)
    (hwf' : (TypeChecker.MLCtx.vlam id name ty ty' bi main).WF venv Us)
    (htr₀ : TrExprS venv Us B.m.vlctx ty ty₀)
    (hty₀ : venv.IsType Us.length B.m.vlctx.toCtx ty₀) :
    CheckBase venv Us (.vlam id name ty ty' bi main) (lctx.mkLocalDecl id name ty bi)
      (l.mkLocalDecl id name ty bi) where
  m := .vlam id name ty ty₀ bi B.m
  wf := ⟨B.wf, B.wf.tr.find?_eq_none.2 fun h =>
      (hwf'.1.tr.find?_eq_none.1 hwf'.2.1) (B.embed.fvars_subset h), htr₀, hty₀⟩
  onlyLams := B.onlyLams.vlam
  lctx_eq := by
    change B.m.lctx.mkLocalDecl id name ty bi = l.mkLocalDecl id name ty bi
    rw [B.lctx_eq]
  embed := B.embed.cons henv (hwf'.1.tr.find?_eq_none.1 hwf'.2.1) htr₀ hwf'.2.2.1 hwf'.2.2.2
  sub := B.sub.mkLocalDecl_both (by rw [← B.lctx_eq]; exact B.wf.tr.1.map_wf)
    (by rw [← hlctx]; exact hwf'.1.tr.1.map_wf)

def mono {venv' : VEnv} {l : LocalContext} (B : CheckBase venv Us main lctx l)
    (hle : venv ≤ venv') : CheckBase venv' Us main lctx l where
  m := B.m
  wf := B.wf.mono hle
  onlyLams := B.onlyLams
  lctx_eq := B.lctx_eq
  embed := B.embed.mono hle
  sub := B.sub

def prependLevelParam {l : LocalContext} {fresh : Name} (B : CheckBase venv Us main lctx l)
    (henv : VEnv.WF venv) (hfresh : fresh ∉ Us) :
    CheckBase venv (fresh :: Us) (main.prependLevelParam Us.length) lctx l where
  m := B.m.prependLevelParam Us.length
  wf := B.wf.prependLevelParam henv hfresh
  onlyLams := by
    intro d hd
    apply B.onlyLams d
    simpa using hd
  lctx_eq := by simpa using B.lctx_eq
  embed := by
    simpa using B.embed.instL (U' := (fresh :: Us).length)
      (by simpa using VLevel.prependShift_wf (n := Us.length))
  sub := B.sub

/-- The free variables of the checker context, in order, restrict the main
local context to the checker context. -/
theorem restrictTo_eq {l : LocalContext} (B : CheckBase venv Us main lctx l) : lctx.restrictTo B.m.fvarList = l := by
  have hsub : B.m.lctx.SubContextOf lctx := by rw [B.lctx_eq]; exact B.sub
  rw [LocalContext.restrictTo_mlctx B.onlyLams B.wf hsub, B.lctx_eq]

end CheckBase

end VerifyInductive

end Lean4Lean
