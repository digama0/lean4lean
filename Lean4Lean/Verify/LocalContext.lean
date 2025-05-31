import Lean4Lean.Verify.Axioms
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Typing.Expr

namespace Lean.LocalContext

noncomputable def toList (lctx : LocalContext) : List LocalDecl :=
  lctx.decls.toList'.reverse.filterMap id

noncomputable def fvars (lctx : LocalContext) : List FVarId :=
  lctx.toList.map (·.fvarId)

def mkBindingList1 (isLambda : Bool) (lctx : LocalContext)
    (xs : List FVarId) (x : FVarId) (b : Expr) : Expr :=
  match lctx.find? x with
  | some (.cdecl _ _ n ty bi _) =>
    let ty := ty.abstractList (xs.map .fvar)
    if isLambda then
      .lam n ty b bi
    else
      .forallE n ty b bi
  | some (.ldecl _ _ n ty val nonDep _) =>
    if b.hasLooseBVar' 0 then
      let ty  := ty.abstractList (xs.map .fvar)
      let val := val.abstractList (xs.map .fvar)
      .letE n ty val b nonDep
    else
      b.lowerLooseBVars' 1 1
  | none => panic! "unknown free variable"

def mkBindingList (isLambda : Bool) (lctx : LocalContext) (xs : List FVarId) (b : Expr) : Expr :=
  core (b.abstractList (xs.map .fvar))
where
  core := go xs.reverse
  go : List FVarId → Expr → Expr
  | [], b => b
  | x :: xs, b => go xs (mkBindingList1 isLambda lctx xs.reverse x b)

theorem mkBinding'_eq :
    mkBinding' isLambda lctx ⟨xs.map .fvar⟩ b = mkBindingList isLambda lctx xs b := by
  simp only [mkBinding', List.getElem_toArray, Expr.abstractRange',
    Expr.abstract', ← Array.take_eq_extract, List.take_toArray, Nat.sub_zero, List.drop_zero,
    ← List.map_take, List.getElem_map]
  dsimp only [Array.size]
  simp only [List.getElem_eq_getElem?_get, Option.get_eq_getD (fallback := default)]
  change Nat.foldRev _ (fun i x =>
    mkBindingList1 isLambda lctx (xs.take i) (xs[i]?.getD default)) .. = mkBindingList.go ..
  rw [List.length_map]; generalize eq : xs.length = n
  generalize b.abstractList (xs.map .fvar) = b
  induction n generalizing xs b with
  | zero => let [] := xs; simp [mkBindingList.go]
  | succ n ih =>
    obtain rfl | ⟨xs, a, rfl⟩ := List.eq_nil_or_concat xs; · cases eq
    simp at eq ⊢; subst eq
    simp +contextual only [Nat.le_of_lt, List.take_append_of_le_length,
      List.getElem?_append_left, mkBindingList.go, ih]; simp

theorem mkBindingList1_abstract {xs : List FVarId}
    (hx : lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    (mkBindingList1 isLambda lctx xs x b).abstractFVar a xs.length =
    mkBindingList1 isLambda lctx (a :: xs) x (b.abstractFVar a (xs.length + 1)) := by
  have (e) := Nat.zero_add _ ▸ Expr.abstractFVar_abstractList' (k := 0) (e := e) nd
  simp [mkBindingList1, hx]; cases decl with simp
  | cdecl _ _ _ ty =>
    split <;> simp [Expr.abstractFVar, Expr.abstract1, this]
  | ldecl =>
    have := Expr.abstractFVar_hasLooseBVar a b (xs.length + 1) 0
    simp at this; simp [this]; clear this
    split
    · simp [Expr.abstractFVar, Expr.abstract1, this]
    · rename_i h; simp at h
      rw [Expr.abstractFVar_lower h (Nat.zero_le _)]

theorem mkBindingList_core_cons {xs : List FVarId} {b : Expr}
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    mkBindingList.core isLambda lctx (a :: xs) (b.abstractFVar a xs.length) =
    mkBindingList1 isLambda lctx [] a
      ((mkBindingList.core isLambda lctx xs b).abstractFVar a) := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp [mkBindingList.core] at *
  induction xs generalizing b with
  | nil => simp [mkBindingList.go]
  | cons c xs ih =>
    simp at hx nd ih
    let ⟨decl, eq⟩ := hx.1
    simp [← List.map_reverse, mkBindingList.go]
    rw [← xs.length_reverse, ← mkBindingList1_abstract eq (by simp [*])]
    simp [ih hx.2 nd.1.2 nd.2.2]

@[simp] theorem mkBindingList_nil : mkBindingList isLambda lctx [] b = b := rfl

theorem mkBindingList_cons
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    mkBindingList isLambda lctx (a :: xs) b =
    mkBindingList1 isLambda lctx [] a ((mkBindingList isLambda lctx xs b).abstractFVar a) := by
  simp [Expr.abstractList_append, Expr.abstract1, mkBindingList]
  rw [← Expr.abstractFVar_abstractList' nd]
  rw [Nat.zero_add, mkBindingList_core_cons hx nd]

theorem mkBindingList_eq_fold
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : xs.Nodup) :
    mkBindingList isLambda lctx xs b =
    xs.foldr (fun a e => mkBindingList1 isLambda lctx [] a (e.abstractFVar a)) b := by
  induction xs <;> simp_all [mkBindingList_cons]

theorem mkBindingList1_congr (H : lctx₁.find? x = lctx₂.find? x) :
    mkBindingList1 isLambda lctx₁ xs x b = mkBindingList1 isLambda lctx₂ xs x b := by
  simp [mkBindingList1, H]

theorem mkBindingList_congr
    (H : ∀ x ∈ xs, lctx₁.find? x = lctx₂.find? x) :
    mkBindingList isLambda lctx₁ xs b = mkBindingList isLambda lctx₂ xs b := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp [mkBindingList, mkBindingList.core] at *
  generalize b.abstractList _ = b
  induction xs generalizing b <;> simp_all [mkBindingList.go]
  simp [mkBindingList1_congr H.1]

end Lean.LocalContext

namespace Lean4Lean

open Lean
open scoped List

attribute [-simp] List.filterMap_reverse

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
  | nil : TrLCtx ⟨.empty, .empty, .empty⟩ []
  | cons :
    d.fvarId = fv → map.find? fv = none → d.index = arr.size →
    TrLCtx ⟨map, arr, fvmap⟩ Δ → TrLocalDecl env Us Δ d d' →
    TrLCtx ⟨map.insert fv d, arr.push d, fvmap⟩ ((some fv, d') :: Δ)

theorem TrLCtx.map_wf : TrLCtx env Us lctx Δ → lctx.fvarIdToDecl.WF
  | .nil => .empty
  | .cons _ h1 _ h2 _ => .insert h1 h2.map_wf

theorem TrLCtx.decls_wf : TrLCtx env Us lctx Δ → lctx.decls.WF
  | .nil => .empty
  | .cons _ _ _ h2 _ => .push h2.decls_wf

theorem TrLCtx.noBV : TrLCtx env Us lctx Δ → Δ.NoBV
  | .nil => rfl
  | .cons _ _ _ h2 _ => h2.noBV

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

theorem TrLCtx.find?_eq_find?_toList (H : TrLCtx env Us lctx Δ) :
    lctx.find? fv = lctx.toList.find? (fv == ·.fvarId) := by
  rw [LocalContext.find?, H.map_wf.find?_eq,
    H.map_toList.lookup_eq H.map_wf.nodupKeys, List.map_fst_lookup]

theorem TrLCtx.find?_isSome (H : TrLCtx env Us lctx Δ) :
    (lctx.find? fv).isSome = (Δ.find? (.inr fv)).isSome := by
  rw [H.find?_eq_find?_toList, ← VLCtx.lookup_isSome]
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

theorem TrLCtx.find?_eq_none (H : TrLCtx env Us lctx Δ) :
    lctx.find? fv = none ↔ ¬fv ∈ Δ.fvars := by simp [← H.find?_eq_some]

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
