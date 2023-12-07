import Lean4Lean.Verify.Axioms
import Lean4Lean.Verify.Expr

namespace Lean4Lean

open Lean

variable (Us : List Name) (Δ : VLCtx) in
inductive TrLocalDecl : LocalDecl → VLocalDecl → Prop
  | vlam : TrExpr Us Δ ty ty' →
    TrLocalDecl (.cdecl n fv name ty bi kind) (.vlam ty')
  | vlet : TrExpr Us Δ ty ty' → TrExpr Us Δ val val' →
    TrLocalDecl (.ldecl n fv name ty val bi kind) (.vlet ty' val')

variable (Us : List Name) in
inductive TrLCtx : LocalContext → VLCtx → Prop
  | nil : TrLCtx ⟨.empty, .empty⟩ []
  | cons :
    d.fvarId = fv → map.find? fv = none → d.index = arr.size →
    TrLCtx ⟨map, arr⟩ Δ → TrLocalDecl Us Δ d d' →
    TrLCtx ⟨map.insert fv d, arr.push d⟩ ((some fv, d') :: Δ)

theorem TrLCtx.map_WF : TrLCtx Us lctx Δ → lctx.fvarIdToDecl.WF
  | .nil => .empty
  | .cons _ h1 _ h2 _ => .insert h1 h2.map_WF

theorem TrLCtx.decls_WF : TrLCtx Us lctx Δ → lctx.decls.WF
  | .nil => .empty
  | .cons _ _ _ h2 _ => .push h2.decls_WF

theorem TrLCtx.mkLocalDecl
    (h1 : TrLCtx Us lctx Δ) (h2 : lctx.find? fv = none) (h3 : TrExpr Us Δ ty ty') :
    TrLCtx Us (lctx.mkLocalDecl fv name ty bi kind) ((some fv, .vlam ty') :: Δ) :=
  .cons rfl h2 rfl h1 (.vlam h3)

theorem TrLCtx.mkLetDecl
    (h1 : TrLCtx Us lctx Δ) (h2 : lctx.find? fv = none)
    (h3 : TrExpr Us Δ ty ty') (h4 : TrExpr Us Δ val val') :
    TrLCtx Us (lctx.mkLetDecl fv name ty val bi kind) ((some fv, .vlet ty' val') :: Δ) :=
  .cons rfl h2 rfl h1 (.vlet h3 h4)

end Lean4Lean

-- namespace Lean.LocalContext
-- open Lean4Lean

-- inductive WF : LocalContext → List LocalDecl → Prop
--   | nil : WF ⟨.empty, .empty⟩ []
--   | cons :
--     map.find? d.fvarId = none → d.index = arr.size →
--     WF ⟨map, arr⟩ ds → WF ⟨map.insert d.fvarId d, arr.push d⟩ (d::ds)

-- theorem WF.fvarIdToDecl : WF lctx ds → lctx.fvarIdToDecl.WF
--   | .nil => .empty
--   | .cons h1 _ h2 => .insert h1 h2.fvarIdToDecl

-- theorem WF.decls : WF lctx ds → lctx.decls.WF
--   | .nil => .empty
--   | .cons _ _ h2 => .push h2.decls

-- theorem WF.decls_toList' : WF lctx ds → lctx.decls.toList'.reverse = ds.map some
--   | .nil => PersistentArray.toList'_empty
--   | .cons _ _ h => by simp [PersistentArray.toList'_push]; rw [decls_toList' h]

-- theorem WF.decls_size (h : WF lctx ds) : lctx.decls.size = ds.length := by
--   rw [← h.decls.toList'_length, ← lctx.decls.toList'.reverse_reverse, h.decls_toList']; simp

-- theorem WF.mkLocalDecl (h1 : WF lctx ds) (h2 : lctx.find? fv = none) :
--     WF (lctx.mkLocalDecl fv name type bi kind) (.cdecl ds.length fv name type bi kind :: ds) := by
--   simp [mkLocalDecl, ← h1.decls_size]; exact .cons (d := .cdecl ..) h2 rfl h1

-- theorem WF.mkLetDecl (h1 : WF lctx ds) (h2 : lctx.find? fv = none) :
--     WF (lctx.mkLetDecl fv name type bi nonDep kind)
--        (.ldecl ds.length fv name type bi nonDep kind :: ds) := by
--   simp [mkLetDecl, ← h1.decls_size]; exact .cons (d := .ldecl ..) h2 rfl h1

-- theorem WF.find?_eq (h : WF lctx ds) : lctx.find? fv = ds.find? fun d => fv == d.fvarId := by
--   simp [find?, h.fvarIdToDecl.find?_eq]
--   induction h with
--   | nil => simp
--   | @cons _ _ _ d h1 h2 h3 ih =>
--     have nd := (h3.fvarIdToDecl.insert (b := d) h1).nodupKeys
--     rw [h3.fvarIdToDecl.find?_eq] at h1
--     rw [(h3.fvarIdToDecl.toList'_insert _ _ h1).lookup_eq nd]
--     simp [List.find?, List.lookup]; split <;> [rfl; simpa using ih]
