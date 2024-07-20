import Lean4Lean.Verify.Axioms
import Lean4Lean.Verify.Typing.Expr

namespace Lean4Lean

open Lean
open scoped List

noncomputable def _root_.Lean.LocalContext.toList (lctx : LocalContext) : List LocalDecl :=
  lctx.decls.toList'.reverse.filterMap id

noncomputable def _root_.Lean.LocalContext.fvars (lctx : LocalContext) : List FVarId :=
  lctx.toList.map (·.fvarId)

variable (env : VEnv) (Us : List Name) (Δ : VLCtx) in
inductive TrLocalDecl : LocalDecl → VLocalDecl → Prop
  | vlam : TrExpr env Us Δ ty ty' → env.IsType Us.length Δ.toCtx ty' →
    TrLocalDecl (.cdecl n fv name ty bi kind) (.vlam ty')
  | vlet :
    TrExpr env Us Δ ty ty' → TrExpr env Us Δ val val' →
    env.HasType Us.length Δ.toCtx val' ty' →
    TrLocalDecl (.ldecl n fv name ty val bi kind) (.vlet ty' val')

theorem TrLocalDecl.wf : TrLocalDecl env Us Δ d d' → d'.WF env Us.length Δ.toCtx
  | .vlam _ h | .vlet _ _ h => h

variable (env : VEnv) (Us : List Name) in
inductive TrLCtx : LocalContext → VLCtx → Prop
  | nil : TrLCtx ⟨.empty, .empty⟩ []
  | cons :
    d.fvarId = fv → map.find? fv = none → d.index = arr.size →
    TrLCtx ⟨map, arr⟩ Δ → TrLocalDecl env Us Δ d d' →
    TrLCtx ⟨map.insert fv d, arr.push d⟩ ((some fv, d') :: Δ)

theorem TrLCtx.map_wf : TrLCtx env Us lctx Δ → lctx.fvarIdToDecl.WF
  | .nil => .empty
  | .cons _ h1 _ h2 _ => .insert h1 h2.map_wf

theorem TrLCtx.decls_wf : TrLCtx env Us lctx Δ → lctx.decls.WF
  | .nil => .empty
  | .cons _ _ _ h2 _ => .push h2.decls_wf

theorem TrLCtx.map_toList : TrLCtx env Us lctx Δ →
    lctx.fvarIdToDecl.toList' ~ lctx.toList.map fun d => (d.fvarId, d)
  | .nil => by simp [LocalContext.toList]
  | .cons h1 h2 _ h4 h5 => by
    subst h1; simp [LocalContext.toList]
    exact h4.map_wf.toList'_insert _ _ (by rwa [h4.map_wf.find?_eq] at h2)
      |>.trans (.cons _ h4.map_toList)

theorem TrLCtx.forall₂ :
    TrLCtx env Us lctx Δ → lctx.toList.Forall₂ Δ (R := fun d d' => d'.1 = some d.fvarId)
  | .nil => by simp [LocalContext.toList]
  | .cons h1 _ _ h4 _ => by subst h1; simp [LocalContext.toList]; exact h4.forall₂

theorem TrLCtx.fvars_eq (H : TrLCtx env Us lctx Δ) : lctx.fvars = Δ.fvars := by
  simp [LocalContext.fvars, VLCtx.fvars, LocalContext.toList]
  induction H with
  | nil => rfl
  | cons h1 _ _ _ _ ih => simp [h1, ← ih]

theorem TrLCtx.find?_isSome (H : TrLCtx env Us lctx Δ) :
    (lctx.find? fv).isSome = (Δ.find? (.inr fv)).isSome := by
  rw [LocalContext.find?, H.map_wf.find?_eq, ← VLCtx.lookup_isSome,
    H.map_toList.lookup_eq H.map_wf.nodupKeys, List.map_fst_lookup]
  have := H.forall₂; generalize lctx.toList = l at this ⊢; clear H
  induction this with
  | nil => rfl
  | @cons d d' _ _ eq _ ih =>
    cases d'; cases eq
    simp [List.find?, List.lookup, show (some fv == some d.fvarId) = (fv == d.fvarId) from rfl]
    split <;> simp [*]

theorem TrLCtx.find?_eq_some (H : TrLCtx env Us lctx Δ) :
    (∃ d, lctx.find? fv = some d) ↔ fv ∈ Δ.fvars := by
  rw [← Option.isSome_iff_exists, H.find?_isSome, Option.isSome_iff_exists, VLCtx.find?_eq_some]

theorem TrLCtx.contains (H : TrLCtx env Us lctx Δ) : lctx.contains fv ↔ fv ∈ Δ.fvars := by
  rw [LocalContext.contains, PersistentHashMap.find?_isSome, Option.isSome_iff_exists]
  exact H.find?_eq_some

theorem TrLCtx.wf : TrLCtx env Us lctx Δ → Δ.WF env Us.length
  | .nil => ⟨⟩
  | .cons _ h2 _ h4 h5 => ⟨h4.wf, by simpa [← h4.find?_eq_some], h5.wf⟩

theorem TrLCtx.mkLocalDecl
    (h1 : TrLCtx env Us lctx Δ) (h2 : lctx.find? fv = none) (h3 : TrExpr env Us Δ ty ty')
    (h4 : env.IsType Us.length Δ.toCtx ty') :
    TrLCtx env Us (lctx.mkLocalDecl fv name ty bi kind) ((some fv, .vlam ty') :: Δ) :=
  .cons rfl h2 rfl h1 (.vlam h3 h4)

theorem TrLCtx.mkLetDecl
    (h1 : TrLCtx env Us lctx Δ) (h2 : lctx.find? fv = none)
    (h3 : TrExpr env Us Δ ty ty') (h4 : TrExpr env Us Δ val val')
    (h5 : env.HasType Us.length Δ.toCtx val' ty') :
    TrLCtx env Us (lctx.mkLetDecl fv name ty val bi kind) ((some fv, .vlet ty' val') :: Δ) :=
  .cons rfl h2 rfl h1 (.vlet h3 h4 h5)
