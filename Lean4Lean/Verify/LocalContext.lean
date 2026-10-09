import Lean4Lean.Std.PersistentHashMap
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas

open Lean4Lean

namespace Lean.LocalContext

theorem find?_empty (fv : FVarId) : ({} : LocalContext).find? fv = none := by
  show PersistentHashMap.find? PersistentHashMap.empty fv = none
  rw [PersistentHashMap.WF.empty.find?_eq, PersistentHashMap.toList'_empty]
  rfl

theorem find?_mkLocalDecl
    {l : LocalContext} {fv fv' : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (hwf : l.fvarIdToDecl.WF) :
    (l.mkLocalDecl fv name ty bi kind).find? fv' =
      if fv == fv' then some (.cdecl l.decls.size fv name ty bi kind)
      else l.find? fv' := by
  simp only [LocalContext.mkLocalDecl, LocalContext.find?]
  exact hwf.find?_insert

noncomputable def toList (lctx : LocalContext) : List LocalDecl :=
  lctx.decls.toList'.reverse.filterMap id

noncomputable def fvars (lctx : LocalContext) : List FVarId :=
  lctx.toList.map (·.fvarId)

def mkBindingList1 (isLambda : Bool) (lctx : LocalContext)
    (xs : List FVarId) (x : FVarId) (b : Expr) : Expr :=
  match lctx.find? x with
  | some (.cdecl _ _ n ty bi _) =>
    let ty := ty.abstractList xs
    if isLambda then
      .lam n ty b bi
    else
      .forallE n ty b bi
  | some (.ldecl _ _ n ty val nonDep _) =>
    if b.hasLooseBVar' 0 then
      let ty  := ty.abstractList xs
      let val := val.abstractList xs
      .letE n ty val b nonDep
    else
      b.lowerLooseBVars' 1 1
  | none => panic! "unknown free variable"

def mkBindingList (isLambda : Bool) (lctx : LocalContext) (xs : List FVarId) (b : Expr) : Expr :=
  core (b.abstractList xs)
where
  core := go xs.reverse
  go : List FVarId → Expr → Expr
  | [], b => b
  | x :: xs, b => go xs (mkBindingList1 isLambda lctx xs.reverse x b)


theorem mkBindingList1_abstract {xs : List FVarId}
    (hx : lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    (mkBindingList1 isLambda lctx xs x b).abstract1 a xs.length =
    mkBindingList1 isLambda lctx (a :: xs) x (b.abstract1 a (xs.length + 1)) := by
  have (e:_) := Nat.zero_add _ ▸ Expr.abstract1_abstractList' (k := 0) (e := e) nd
  simp [mkBindingList1, hx]; cases decl with simp
  | cdecl _ _ _ ty => split <;> simp [Expr.abstract1, Expr.abstract1, this]
  | ldecl =>
    have := Expr.abstract1_hasLooseBVar a b (xs.length + 1) 0
    simp at this; simp [this]; clear this
    split
    · simp [Expr.abstract1, Expr.abstract1, this]
    · rename_i h; simp at h
      rw [Expr.abstract1_lower h (Nat.zero_le _)]

theorem mkBindingList_core_cons {xs : List FVarId} {b : Expr}
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    mkBindingList.core isLambda lctx (a :: xs) (b.abstract1 a xs.length) =
    mkBindingList1 isLambda lctx [] a
      ((mkBindingList.core isLambda lctx xs b).abstract1 a) := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp [mkBindingList.core] at *
  induction xs generalizing b with
  | nil => simp [mkBindingList.go]
  | cons c xs ih =>
    simp at hx nd ih
    let ⟨decl, eq⟩ := hx.1
    simp [mkBindingList.go]
    rw [← xs.length_reverse, ← mkBindingList1_abstract eq (by simp [*])]
    simp [ih hx.2 nd.1.2 nd.2.2]

@[simp] theorem mkBindingList_nil : mkBindingList isLambda lctx [] b = b := rfl

theorem mkBindingList_cons
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    mkBindingList isLambda lctx (a :: xs) b =
    mkBindingList1 isLambda lctx [] a ((mkBindingList isLambda lctx xs b).abstract1 a) := by
  simp [mkBindingList]
  rw [← Expr.abstract1_abstractList' nd]
  rw [Nat.zero_add, mkBindingList_core_cons hx nd]

theorem mkBindingList_eq_fold
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : xs.Nodup) :
    mkBindingList isLambda lctx xs b =
    xs.foldr (fun a e => mkBindingList1 isLambda lctx [] a (e.abstract1 a)) b := by
  induction xs <;> simp_all [mkBindingList_cons]

/-! ### Exact (simultaneous-abstraction) model of `mkBinding`

`mkBindingListN` models `LocalContext.mkBinding` with Lean's actual abstraction
(`Expr.abstractN`, linked to `Expr.abstract` by the axiom `Expr.abstractN_eq`). It agrees with the sequential
`mkBindingList` when the body and binder types are locally closed and the variables are
duplicate-free, and it is the model to use wherever a body may contain loose bound variables
(for example the recursor-placeholder templates of recursive calls). -/

def mkBindingList1N (isLambda : Bool) (lctx : LocalContext)
    (xs : List FVarId) (x : FVarId) (b : Expr) : Expr :=
  match lctx.find? x with
  | some (.cdecl _ _ n ty bi _) =>
    let ty := ty.abstractN xs
    if isLambda then
      .lam n ty b bi
    else
      .forallE n ty b bi
  | some (.ldecl _ _ n ty val nonDep _) =>
    if b.hasLooseBVar' 0 then
      let ty  := ty.abstractN xs
      let val := val.abstractN xs
      .letE n ty val b nonDep
    else
      b.lowerLooseBVars' 1 1
  | none => panic! "unknown free variable"

def mkBindingListN (isLambda : Bool) (lctx : LocalContext) (xs : List FVarId) (b : Expr) :
    Expr :=
  core (b.abstractN xs)
where
  core := go xs.reverse
  go : List FVarId → Expr → Expr
  | [], b => b
  | x :: xs, b => go xs (mkBindingList1N isLambda lctx xs.reverse x b)

theorem mkBinding_eqN :
    mkBinding isLambda lctx ⟨xs.map .fvar⟩ b = mkBindingListN isLambda lctx xs b := by
  simp only [mkBinding, List.getElem_toArray, Expr.abstractRange_eq, Expr.hasLooseBVar_eq,
    Expr.abstractN_eq, ← Array.take_eq_extract, List.take_toArray, Bool.and_false,
    ← List.map_take, List.getElem_map, Expr.lowerLooseBVars_eq]
  dsimp only [Array.size]
  simp only [List.getElem_eq_getElem?_get, Option.get_eq_getD (fallback := default)]
  change Nat.foldRev _ (fun i x =>
    mkBindingList1N isLambda lctx (xs.take i) (xs[i]?.getD default)) .. = mkBindingListN.go ..
  rw [List.length_map]; generalize eq : xs.length = n
  generalize b.abstractN xs = b
  induction n generalizing xs b with
  | zero => let [] := xs; simp [mkBindingListN.go]
  | succ n ih =>
    obtain rfl | ⟨xs, a, rfl⟩ := List.eq_nil_or_concat xs; · cases eq
    simp at eq ⊢; subst eq
    simp +contextual only [Nat.le_of_lt, List.take_append_of_le_length,
      List.getElem?_append_left, mkBindingListN.go, ih]; simp

theorem mkBindingList1N_abstract {xs : List FVarId}
    (hx : lctx.find? x = some decl) (ha : a ∉ xs) :
    (mkBindingList1N isLambda lctx xs x b).abstractN [a] xs.length =
    mkBindingList1N isLambda lctx (a :: xs) x (b.abstractN [a] (xs.length + 1)) := by
  simp [mkBindingList1N, hx]; cases decl with simp
  | cdecl _ _ _ ty => split <;> simp [Expr.abstractN, Expr.abstractN_cons ha]
  | ldecl =>
    rw [Expr.abstractN_hasLooseBVar_zero]
    split
    · simp [Expr.abstractN, Expr.abstractN_cons ha]
    · rename_i h; simp at h
      rw [Expr.abstractN_lower _ _ _ h]

theorem mkBindingListN_core_cons {xs : List FVarId} {b : Expr}
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    mkBindingListN.core isLambda lctx (a :: xs) (b.abstractN [a] xs.length) =
    mkBindingList1N isLambda lctx [] a
      ((mkBindingListN.core isLambda lctx xs b).abstractN [a]) := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp [mkBindingListN.core] at *
  induction xs generalizing b with
  | nil => simp [mkBindingListN.go]
  | cons c xs ih =>
    simp at hx nd ih
    let ⟨decl, eq⟩ := hx.1
    simp [mkBindingListN.go]
    rw [← xs.length_reverse, ← mkBindingList1N_abstract eq (by simp [*])]
    simp [ih hx.2 nd.1.2 nd.2.2]

@[simp] theorem mkBindingListN_nil : mkBindingListN isLambda lctx [] b = b := by
  simp [mkBindingListN, mkBindingListN.core, mkBindingListN.go, Expr.abstractN_nil]

theorem mkBindingListN_cons
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : (a :: xs).Nodup) :
    mkBindingListN isLambda lctx (a :: xs) b =
    mkBindingList1N isLambda lctx [] a ((mkBindingListN isLambda lctx xs b).abstractN [a]) := by
  simp only [mkBindingListN]
  rw [Expr.abstractN_cons (by simpa using (List.nodup_cons.1 nd).1), Nat.zero_add,
    mkBindingListN_core_cons hx nd]

theorem mkBindingListN_eq_fold
    (hx : ∀ x ∈ xs, ∃ decl, lctx.find? x = some decl) (nd : xs.Nodup) :
    mkBindingListN isLambda lctx xs b =
    xs.foldr (fun a e => mkBindingList1N isLambda lctx [] a (e.abstractN [a])) b := by
  induction xs <;> simp_all [mkBindingListN_cons]

theorem mkBindingList1N_congr (H : lctx₁.find? x = lctx₂.find? x) :
    mkBindingList1N isLambda lctx₁ xs x b = mkBindingList1N isLambda lctx₂ xs x b := by
  simp [mkBindingList1N, H]

/-- A local declaration whose type (and value) are locally closed. -/
def DeclClosed : LocalDecl → Prop
  | .cdecl _ _ _ ty _ _ => Closed ty
  | .ldecl _ _ _ ty val _ _ => Closed ty ∧ Closed val

/-- Closedness of the declarations selected by a binding. -/
def DeclsClosed (lctx : LocalContext) (xs : List FVarId) : Prop :=
  ∀ x ∈ xs, ∀ d, lctx.find? x = some d → DeclClosed d

theorem DeclsClosed.tail (h : DeclsClosed lctx (a :: xs)) : DeclsClosed lctx xs :=
  fun x hx => h x (List.mem_cons_of_mem a hx)

private theorem closed_lower_of_abstract1 (he : Closed e)
    (h : (e.abstract1 a).hasLooseBVar' 0 = false) :
    Closed ((e.abstract1 a).lowerLooseBVars' 1 1) := by
  rw [Expr.lowerLooseBVars_eq_instantiate h (v := .sort .zero)]
  exact Closed.instantiate1 he.abstract1 trivial

/-- One binding step of the exact model agrees with the sequential model on a closed body with
closed declaration, and the result is closed again. -/
theorem mkBindingList1N_eq_mkBindingList1 (hx : lctx.find? x = some d)
    (hd : DeclClosed d) (hb : Closed b) :
    mkBindingList1N isLambda lctx [] x (b.abstractN [x]) =
      mkBindingList1 isLambda lctx [] x (b.abstract1 x) ∧
    Closed (mkBindingList1 isLambda lctx [] x (b.abstract1 x)) := by
  have hsingle : b.abstractN [x] = b.abstract1 x :=
    Expr.abstractN_singleton hb.looseBVarRange_le
  cases d with
  | cdecl _ _ _ ty bi _ =>
    simp only [DeclClosed] at hd
    simp only [mkBindingList1N, mkBindingList1, hx, hsingle, Expr.abstractN_nil, Expr.abstractList]
    cases isLambda
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨trivial, hd, hb.abstract1⟩
    · simp only [ite_true]
      exact ⟨trivial, hd, hb.abstract1⟩
  | ldecl _ _ _ ty val _ _ =>
    simp only [DeclClosed] at hd
    simp only [mkBindingList1N, mkBindingList1, hx, hsingle, Expr.abstractN_nil, Expr.abstractList]
    by_cases h : (b.abstract1 x).hasLooseBVar' 0 = true
    · simp only [h, ite_true]
      exact ⟨trivial, hd.1, hd.2, hb.abstract1⟩
    · simp only [h, Bool.false_eq_true, ite_false]
      exact ⟨trivial, closed_lower_of_abstract1 hb (by simpa using h)⟩

/-- The exact and the sequential binding models agree when the body and the selected
declarations are locally closed and the variables are duplicate-free. -/
theorem mkBindingListN_eq_mkBindingList (hex : ∀ x ∈ xs, ∃ d, lctx.find? x = some d)
    (nd : xs.Nodup) (hb : Closed b) (hdecl : DeclsClosed lctx xs) :
    mkBindingListN isLambda lctx xs b = mkBindingList isLambda lctx xs b ∧
      Closed (mkBindingList isLambda lctx xs b) := by
  rw [mkBindingListN_eq_fold hex nd, mkBindingList_eq_fold hex nd]
  induction xs with
  | nil => exact ⟨rfl, hb⟩
  | cons a xs ih =>
    have hex' : ∀ x ∈ xs, ∃ d, lctx.find? x = some d := fun x hx => hex x (List.mem_cons_of_mem a hx)
    obtain ⟨heq, hcl⟩ := ih hex' (List.nodup_cons.1 nd).2 hdecl.tail
    obtain ⟨d, hd⟩ := hex a (List.mem_cons_self ..)
    simp only [List.foldr_cons]
    rw [heq]
    exact mkBindingList1N_eq_mkBindingList1 hd (hdecl a (List.mem_cons_self ..) d hd) hcl

/-- `mkBinding` agrees with the sequential `mkBindingList` under the hypotheses that make the
sequential model correct: every variable is declared, the variables are duplicate-free, and the
body and the selected declarations are locally closed. Without them use `mkBinding_eqN`. -/
theorem mkBinding_eq' (hex : ∀ x ∈ xs, ∃ d, lctx.find? x = some d)
    (nd : xs.Nodup) (hb : Closed b) (hdecl : DeclsClosed lctx xs) :
    mkBinding isLambda lctx ⟨xs.map .fvar⟩ b = mkBindingList isLambda lctx xs b := by
  rw [mkBinding_eqN]
  exact (mkBindingListN_eq_mkBindingList hex nd hb hdecl).1

/-- Every declaration of `lctx` is locally closed. Translated contexts satisfy this
(`Lean4Lean.TrLCtx.lctxClosed`). -/
def LctxClosed (lctx : LocalContext) : Prop :=
  ∀ fv d, lctx.find? fv = some d → DeclClosed d

theorem LctxClosed.declsClosed (h : LctxClosed lctx) : DeclsClosed lctx xs :=
  fun x _ d hd => h x d hd

theorem LctxClosed.cdecl (h : LctxClosed lctx)
    (hd : lctx.find? fv = some (.cdecl index fv' name type bi kind)) : Closed type :=
  h _ _ hd

theorem mkBinding_closed (hex : ∀ x ∈ xs, ∃ d, lctx.find? x = some d) (nd : xs.Nodup)
    (hb : Closed b) (hdecl : DeclsClosed lctx xs) :
    Closed (mkBinding isLambda lctx ⟨xs.map .fvar⟩ b) := by
  rw [mkBinding_eq' hex nd hb hdecl]
  exact (mkBindingListN_eq_mkBindingList hex nd hb hdecl).2

theorem _root_.Lean.Expr.abstractN_eq_abstractList_of_closed {xs : List FVarId}
    (hnd : xs.Nodup) (h : Closed e) : e.abstractN xs = e.abstractList xs :=
  Expr.abstractN_eq_abstractList hnd e 0 h.looseBVarRange_le

theorem mkBindingListN_congr
    (H : ∀ x ∈ xs, lctx₁.find? x = lctx₂.find? x) :
    mkBindingListN isLambda lctx₁ xs b = mkBindingListN isLambda lctx₂ xs b := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp [mkBindingListN, mkBindingListN.core] at *
  generalize b.abstractN _ = b
  induction xs generalizing b <;> simp_all [mkBindingListN.go]
  simp [mkBindingList1N_congr H.1]

theorem mkBindingList1N_congr_setIndex
    (H : (lctx₁.find? x).map (·.setIndex 0) = (lctx₂.find? x).map (·.setIndex 0)) :
    mkBindingList1N isLambda lctx₁ xs x b = mkBindingList1N isLambda lctx₂ xs x b := by
  unfold mkBindingList1N
  rcases h1 : lctx₁.find? x with _ | d1 <;> rcases h2 : lctx₂.find? x with _ | d2 <;>
    rw [h1, h2] at H <;> simp only [Option.map_some, Option.map_none, Option.some.injEq,
      reduceCtorEq] at H
  case some.some =>
    cases d1 <;> cases d2 <;> simp only [LocalDecl.setIndex, LocalDecl.cdecl.injEq,
      LocalDecl.ldecl.injEq, reduceCtorEq, true_and] at H
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := H; rfl
    · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := H; rfl

/-- `mkBindingListN` only reads the selected declarations, and ignores their
indices. -/
theorem mkBindingListN_congr_setIndex
    (H : ∀ x ∈ xs, (lctx₁.find? x).map (·.setIndex 0) = (lctx₂.find? x).map (·.setIndex 0)) :
    mkBindingListN isLambda lctx₁ xs b = mkBindingListN isLambda lctx₂ xs b := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp [mkBindingListN, mkBindingListN.core] at *
  generalize b.abstractN _ = b
  induction xs generalizing b <;> simp_all [mkBindingListN.go]
  simp [mkBindingList1N_congr_setIndex H.1]

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

inductive WF : LocalContext → Prop
  | nil : WF ⟨.empty, .empty, .empty⟩
  | cons :
    d.fvarId = fv → map.find? fv = none → d.index = arr.size →
    WF ⟨map, arr, fvmap⟩ →
    WF ⟨map.insert fv d, arr.push d, fvmap⟩

theorem WF.map_wf {lctx : LocalContext} : lctx.WF → lctx.fvarIdToDecl.WF
  | .nil => .empty
  | .cons _ _ _ h2 => .insert h2.map_wf

theorem WF.decls_wf {lctx : LocalContext} : lctx.WF → lctx.decls.WF
  | .nil => .empty
  | .cons _ _ _ h2 => .push h2.decls_wf

attribute [-simp] List.filterMap_reverse in
open scoped _root_.List in
theorem WF.map_toList : WF lctx →
    lctx.fvarIdToDecl.toList' ~ lctx.toList.map fun d => (d.fvarId, d)
  | .nil => by simp [LocalContext.toList]
  | .cons h1 h2 _ h4 => by
    subst h1; simp [LocalContext.toList]
    refine h4.map_wf.toList'_insert _ _ |>.trans (.cons _ ?_)
    rw [List.filter_eq_self.2]; · exact h4.map_toList
    simp; rintro _ b h rfl
    have := (h4.map_wf.find?_eq _).symm.trans h2
    simp [List.lookup_eq_none_iff] at this
    exact this _ _ h rfl

theorem WF.find?_eq_find?_toList (H : WF lctx) :
    lctx.find? fv = lctx.toList.find? (fv == ·.fvarId) := by
  rw [LocalContext.find?, H.map_wf.find?_eq,
    H.map_toList.lookup_eq H.map_wf.nodupKeys, List.map_fst_lookup]

theorem WF.nodup : WF lctx → (lctx.toList.map (·.fvarId)).Nodup
  | .nil => .nil
  | .cons h1 h2 h3 h4 => by
    have := h4.nodup
    have := h4.find?_eq_find?_toList.symm.trans h2
    simp_all [toList]
    simpa [eq_comm] using this

protected theorem WF.mkLocalDecl
    (h1 : WF lctx) (h2 : lctx.find? fv = none) : WF (lctx.mkLocalDecl fv name ty bi kind) :=
  .cons rfl h2 rfl h1

protected theorem WF.mkLetDecl
    (h1 : WF lctx) (h2 : lctx.find? fv = none) : WF (lctx.mkLetDecl fv name ty val bi kind) :=
  .cons rfl h2 rfl h1

@[simp] theorem mkLocalDecl_toList {lctx : LocalContext} :
    (lctx.mkLocalDecl fv name ty bi kind).toList =
    .cdecl lctx.decls.size fv name ty bi kind :: lctx.toList := by
  simp [mkLocalDecl, toList]

@[simp] theorem mkLetDecl_toList {lctx : LocalContext} :
    (lctx.mkLetDecl fv name ty val bi kind).toList =
    .ldecl lctx.decls.size fv name ty val bi kind :: lctx.toList := by
  simp [mkLetDecl, toList]

end Lean.LocalContext

namespace Lean4Lean

open Lean
open scoped _root_.List

attribute [-simp] List.filterMap_reverse

variable (env : VEnv) (Us : List Name) (Δ : VLCtx) in
inductive TrLocalDecl : LocalDecl → VLocalDecl → Prop
  | vlam : TrExprS env Us Δ ty ty' → env.IsType Us.length Δ.toCtx ty' →
    TrLocalDecl (.cdecl n fv name ty bi kind) (.vlam ty')
  | vlet :
    TrExprS env Us Δ ty ty' → TrExprS env Us Δ val val' →
    env.HasType Us.length Δ.toCtx val' ty' →
    TrLocalDecl (.ldecl n fv name ty val bi kind) (.vlet ty' val')

theorem TrLocalDecl.wf : TrLocalDecl env Us Δ d d' → d'.WF env Us.length Δ.toCtx
  | .vlam _ h | .vlet _ _ h => h

def _root_.Lean.LocalDecl.deps : LocalDecl → List FVarId
  | .cdecl (type := t) .. => t.fvarsList
  | .ldecl (type := t) (value := v) .. => t.fvarsList ++ v.fvarsList

theorem TrLocalDecl.deps_wf : TrLocalDecl env Us Δ d d' → d.deps ⊆ Δ.fvars
  | .vlam h _ => h.fvarsList
  | .vlet h1 h2 _ => by simp [LocalDecl.deps, h1.fvarsList, h2.fvarsList]

variable (env : VEnv) (Us : List Name) in
inductive TrLCtx' : List LocalDecl → VLCtx → Prop
  | nil : TrLCtx' [] []
  | cons :
    TrLCtx' ds Δ → TrLocalDecl env Us Δ d d' →
    TrLCtx' (d :: ds) ((some (d.fvarId, d.deps), d') :: Δ)

def TrLCtx (env : VEnv) (Us : List Name) (lctx : LocalContext) (Δ : VLCtx) : Prop :=
  lctx.WF ∧ TrLCtx' env Us lctx.toList Δ

theorem TrLCtx.nil {env : VEnv} {Us : List Name} : TrLCtx env Us {} [] := ⟨.nil, .nil⟩

theorem TrLCtx'.noBV : TrLCtx' env Us ds Δ → Δ.NoBV
  | .nil => rfl
  | .cons h _ => h.noBV

theorem TrLocalDecl.closed (H : TrLocalDecl env Us Δ d d') (hΔ : Δ.NoBV) :
    LocalContext.DeclClosed d := by
  have hΔ' : Δ.bvars = 0 := hΔ
  cases H with
  | vlam h _ =>
    have hc := h.closed; rw [hΔ'] at hc; exact hc
  | vlet h1 h2 _ =>
    have h1c := h1.closed; rw [hΔ'] at h1c
    have h2c := h2.closed; rw [hΔ'] at h2c
    exact ⟨h1c, h2c⟩

theorem TrLCtx'.declClosed : TrLCtx' env Us ds Δ → d ∈ ds → LocalContext.DeclClosed d
  | .nil, h => by cases h
  | .cons h1 h2, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact h2.closed h1.noBV
    · exact h1.declClosed h

/-- Every declaration of a translated local context is locally closed. -/
theorem TrLCtx.lctxClosed (H : TrLCtx env Us lctx Δ) : LocalContext.LctxClosed lctx := by
  intro fv d hd
  rw [H.1.find?_eq_find?_toList] at hd
  exact H.2.declClosed (List.mem_of_find?_eq_some hd)

theorem TrLCtx'.forall₂ :
    TrLCtx' env Us ds Δ → ds.Forall₂ Δ (R := fun d d' => d'.1 = some (d.fvarId, d.deps))
  | .nil => by simp
  | .cons h _ => by simp; exact h.forall₂

theorem TrLCtx'.fvars_eq (H : TrLCtx' env Us ds Δ) : ds.map (·.fvarId) = Δ.fvars := by
  simp [VLCtx.fvars]
  induction H with
  | nil => rfl
  | cons h1 _ ih => simp [← ih]

theorem TrLCtx.fvars_eq (H : TrLCtx env Us lctx Δ) : lctx.fvars = Δ.fvars :=
  H.2.fvars_eq

theorem TrLCtx'.find?_eq_some (H : TrLCtx' env Us ds Δ) :
    (∃ d, ds.find? (fv == ·.fvarId) = some d) ↔ fv ∈ Δ.fvars := by
  rw [← Option.isSome_iff_exists, List.find?_isSome]
  induction H with simp
  | @cons _ _ d d' _ _ ih => simp [← ih]

theorem TrLCtx'.find?_isSome (H : TrLCtx' env Us ds Δ) :
    (ds.find? (fv == ·.fvarId)).isSome = (Δ.find? (.inr fv)).isSome := by
  rw [Bool.eq_iff_iff, Option.isSome_iff_exists, Option.isSome_iff_exists,
    H.find?_eq_some, VLCtx.find?_eq_some]

theorem TrLCtx.find?_isSome (H : TrLCtx env Us lctx Δ) :
    (lctx.find? fv).isSome = (Δ.find? (.inr fv)).isSome := by
  rw [H.1.find?_eq_find?_toList, H.2.find?_isSome]

theorem TrLCtx.find?_eq_some (H : TrLCtx env Us lctx Δ) :
    (∃ d, lctx.find? fv = some d) ↔ fv ∈ Δ.fvars := by
  rw [H.1.find?_eq_find?_toList, H.2.find?_eq_some]

theorem TrLCtx.find?_eq_none (H : TrLCtx env Us lctx Δ) :
    lctx.find? fv = none ↔ ¬fv ∈ Δ.fvars := by simp [← H.find?_eq_some]

theorem TrLCtx.contains (H : TrLCtx env Us lctx Δ) : lctx.contains fv ↔ fv ∈ Δ.fvars := by
  rw [LocalContext.contains, PersistentHashMap.find?_isSome, Option.isSome_iff_exists]
  exact H.find?_eq_some

theorem TrLCtx'.wf : TrLCtx' env Us ds Δ → (ds.map (·.fvarId)).Nodup → Δ.WF env Us.length
  | .nil, _ => ⟨⟩
  | .cons h1 h2, .cons H1 H2 => by
    refine ⟨h1.wf H2, fun _ _ => ?_, h2.wf⟩
    rintro ⟨⟩; exact ⟨by simpa [← h1.find?_eq_some] using H1, h2.deps_wf⟩

theorem TrLCtx.wf (H : TrLCtx env Us lctx Δ) : Δ.WF env Us.length := H.2.wf H.1.nodup

def _root_.Lean.LocalDecl.value' : LocalDecl → Expr
  | .ldecl (value := v) .. => v
  | .cdecl (fvarId := fv) .. => .fvar fv

theorem TrLCtx'.find?_of_mem (henv : env.WF) (H : TrLCtx' env Us ds Δ)
    (nd : (ds.map (·.fvarId)).Nodup) (hm : decl ∈ ds) :
    ∃ e A, Δ.find? (.inr decl.fvarId) = some (e, A) ∧
      FVarsBelow Δ (.fvar decl.fvarId) decl.value' ∧ FVarsBelow Δ (.fvar decl.fvarId) decl.type ∧
      TrExprS env Us Δ decl.value' e ∧ TrExprS env Us Δ decl.type A := by
  have := H.wf nd
  match H with
  | .nil => cases hm
  | .cons (ds := ds) h1 h2 =>
    simp [VLCtx.find?, VLCtx.next]
    obtain _ | ⟨_, hm : decl ∈ ds⟩ := hm
    · simp [and_assoc]
      cases h2 with
      | vlam h2 h3 =>
        refine ⟨.rfl, ?_, .fvar <| by simp [VLCtx.find?, VLCtx.next, LocalDecl.fvarId]; rfl, ?_⟩
        · intro P hP he; exact fvarsIn_iff.2 ⟨hP.2 he, h2.fvarsIn.mono fun _ _ => ⟨⟩⟩
        · exact h2.weakFV henv (.skip_fvar _ _ .refl) this
      | vlet h2 h3 =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro P hP he; have := hP.2 he; simp [LocalDecl.deps, or_imp, forall_and] at this
          exact fvarsIn_iff.2 ⟨this.2, h3.fvarsIn.mono fun _ _ => ⟨⟩⟩
        · intro P hP he; have := hP.2 he; simp [LocalDecl.deps, or_imp, forall_and] at this
          exact fvarsIn_iff.2 ⟨this.1, h2.fvarsIn.mono fun _ _ => ⟨⟩⟩
        · simpa [LocalDecl.value', VLocalDecl.value, VLocalDecl.depth] using
            h3.weakFV henv (.skip_fvar _ _ .refl) this
        · simpa [LocalDecl.type, VLocalDecl.type, VLocalDecl.depth] using
            h2.weakFV henv (.skip_fvar _ _ .refl) this
    · simp at nd; rw [if_neg (by simpa using Ne.symm (nd.1 _ hm))]; simp
      have ⟨_, _, h1, h2, h3, h4, h5⟩ := h1.find?_of_mem henv nd.2 hm
      refine ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, fun _ h => h2 _ h.1, fun _ h => h3 _ h.1, ?_, ?_⟩
      · simpa using h4.weakFV henv (.skip_fvar _ _ .refl) this
      · simpa using h5.weakFV henv (.skip_fvar _ _ .refl) this

theorem TrLCtx.find?_of_mem (henv : env.WF) (H : TrLCtx env Us lctx Δ)
    (hm : decl ∈ lctx.toList) :
    ∃ e A, Δ.find? (.inr decl.fvarId) = some (e, A) ∧
      FVarsBelow Δ (.fvar decl.fvarId) decl.value' ∧ FVarsBelow Δ (.fvar decl.fvarId) decl.type ∧
      TrExprS env Us Δ decl.value' e ∧ TrExprS env Us Δ decl.type A :=
  H.2.find?_of_mem henv H.1.nodup hm

theorem TrLCtx.mkLocalDecl
    (h1 : TrLCtx env Us lctx Δ) (h2 : lctx.find? fv = none) (h3 : TrExprS env Us Δ ty ty')
    (h4 : env.IsType Us.length Δ.toCtx ty') :
    TrLCtx env Us (lctx.mkLocalDecl fv name ty bi kind)
      ((some (fv, ty.fvarsList), .vlam ty') :: Δ) :=
  ⟨h1.1.mkLocalDecl h2, by simpa using .cons h1.2 (.vlam h3 h4)⟩

theorem TrLCtx.mkLetDecl
    (h1 : TrLCtx env Us lctx Δ) (h2 : lctx.find? fv = none)
    (h3 : TrExprS env Us Δ ty ty') (h4 : TrExprS env Us Δ val val')
    (h5 : env.HasType Us.length Δ.toCtx val' ty') :
    TrLCtx env Us (lctx.mkLetDecl fv name ty val bi kind)
      ((some (fv, ty.fvarsList ++ val.fvarsList), .vlet ty' val') :: Δ) :=
  ⟨h1.1.mkLetDecl h2, by simpa using .cons h1.2 (.vlet h3 h4 h5)⟩

/-- Closing no free variables leaves the body unchanged. -/
theorem _root_.Lean.LocalContext.mkForall_empty
    (lctx : LocalContext) (body : Expr) :
    lctx.mkForall #[] body = body := by
  rw [LocalContext.mkForall]
  change LocalContext.mkBinding false lctx
    (([] : List FVarId).map Expr.fvar).toArray body = body
  rw [LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_nil

/-- With distinct selected declarations, closing a concatenated free-variable
list is exactly the same as closing the suffix and then the prefix. -/
theorem _root_.Lean.LocalContext.mkBindingList_append
    (hdecl : ∀ fv ∈ xs ++ ys, ∃ decl, lctx.find? fv = some decl)
    (hnodup : (xs ++ ys).Nodup) :
    LocalContext.mkBindingList isLambda lctx (xs ++ ys) body =
      LocalContext.mkBindingList isLambda lctx xs
        (LocalContext.mkBindingList isLambda lctx ys body) := by
  rcases List.nodup_append.mp hnodup with ⟨hxs, hys, _⟩
  have hdeclXs : ∀ fv ∈ xs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    exact hdecl fv (List.mem_append_left ys hfv)
  have hdeclYs : ∀ fv ∈ ys, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    exact hdecl fv (List.mem_append_right xs hfv)
  rw [LocalContext.mkBindingList_eq_fold hdecl hnodup,
    LocalContext.mkBindingList_eq_fold hdeclXs hxs,
    LocalContext.mkBindingList_eq_fold hdeclYs hys,
    List.foldr_append]

/-- With distinct selected declarations, closing a concatenated free-variable
list is exactly the same as closing the suffix and then the prefix. -/
theorem _root_.Lean.LocalContext.mkBindingListN_append
    (hdecl : ∀ fv ∈ xs ++ ys, ∃ decl, lctx.find? fv = some decl)
    (hnodup : (xs ++ ys).Nodup) :
    LocalContext.mkBindingListN isLambda lctx (xs ++ ys) body =
      LocalContext.mkBindingListN isLambda lctx xs
        (LocalContext.mkBindingListN isLambda lctx ys body) := by
  rcases List.nodup_append.mp hnodup with ⟨hxs, hys, _⟩
  have hdeclXs : ∀ fv ∈ xs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    exact hdecl fv (List.mem_append_left ys hfv)
  have hdeclYs : ∀ fv ∈ ys, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv
    exact hdecl fv (List.mem_append_right xs hfv)
  rw [LocalContext.mkBindingListN_eq_fold hdecl hnodup,
    LocalContext.mkBindingListN_eq_fold hdeclXs hxs,
    LocalContext.mkBindingListN_eq_fold hdeclYs hys,
    List.foldr_append]

/-- Closing an older selected list after extending the local context by one
fresh selected declaration is the same as closing the new declaration first
and then using the old context. -/
theorem _root_.Lean.LocalContext.mkForall_append_fresh
    {lctx : LocalContext} {selected : List FVarId} {fv : FVarId}
    {name : Name} {type body : Expr} {bi : BinderInfo}
    (hwf : lctx.WF) (hfind : lctx.find? fv = none)
    (hdecl : ∀ other ∈ selected, ∃ decl,
      lctx.find? other = some decl)
    (hnodup : selected.Nodup) :
    let next := lctx.mkLocalDecl fv name type bi
    next.mkForall
        ((selected ++ [fv]).map Expr.fvar).toArray body =
      lctx.mkForall (selected.map Expr.fvar).toArray
        (.forallE name type (body.abstractN [fv]) bi) := by
  dsimp only
  let next := lctx.mkLocalDecl fv name type bi
  have hfresh : fv ∉ selected := by
    intro hmem
    rcases hdecl fv hmem with ⟨decl, hsome⟩
    rw [hfind] at hsome
    contradiction
  have hselectedNext : ∀ other ∈ selected, ∃ decl,
      next.find? other = some decl := by
    intro other hother
    rcases hdecl other hother with ⟨decl, hlookup⟩
    refine ⟨decl, ?_⟩
    simp only [next, LocalContext.mkLocalDecl, LocalContext.find?,
      hwf.map_wf.find?_insert]
    rw [if_neg]
    · exact hlookup
    · intro heq
      have : fv = other := beq_iff_eq.mp heq
      exact hfresh (this.symm ▸ hother)
  have hnewNext : next.find? fv = some
      (.cdecl lctx.decls.size fv name type bi .default) := by
    simp [next, LocalContext.mkLocalDecl, LocalContext.find?,
      hwf.map_wf.find?_insert]
  have hallNext : ∀ other ∈ selected ++ [fv], ∃ decl,
      next.find? other = some decl := by
    intro other hother
    rcases List.mem_append.mp hother with hother | hother
    · exact hselectedNext other hother
    · simp only [List.mem_singleton] at hother
      subst other
      exact ⟨_, hnewNext⟩
  have hallNodup : (selected ++ [fv]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnodup, by simp, ?_⟩
    intro a ha b hb hab
    have hb' : b = fv := by simpa using hb
    apply hfresh
    rw [← hb', ← hab]
    exact ha
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkForall, LocalContext.mkBinding_eqN]
  rw [LocalContext.mkBindingListN_append hallNext hallNodup]
  have hsingle : LocalContext.mkBindingListN false next [fv] body =
      .forallE name type (body.abstractN [fv]) bi := by
    simp [LocalContext.mkBindingListN_eq_fold, hnewNext,
      LocalContext.mkBindingList1N, Expr.abstractN_nil]
  rw [hsingle]
  exact LocalContext.mkBindingListN_congr (by
    intro other hother
    simp only [next, LocalContext.mkLocalDecl, LocalContext.find?,
      hwf.map_wf.find?_insert]
    rw [if_neg]
    intro heq
    have : fv = other := beq_iff_eq.mp heq
    exact hfresh (this.symm ▸ hother))

/-- Extending a local context by a fresh declaration not selected for
closure leaves the selected forall expression unchanged. -/
theorem _root_.Lean.LocalContext.mkForall_skip_fresh
    {lctx : LocalContext} {selected : List FVarId} {fv : FVarId}
    {name : Name} {type body : Expr} {bi : BinderInfo}
    (hwf : lctx.WF)
    (hselected : fv ∉ selected) :
    let next := lctx.mkLocalDecl fv name type bi
    next.mkForall (selected.map Expr.fvar).toArray body =
      lctx.mkForall (selected.map Expr.fvar).toArray body := by
  dsimp only
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkForall, LocalContext.mkBinding_eqN]
  apply LocalContext.mkBindingListN_congr
  intro other hother
  simp only [LocalContext.mkLocalDecl, LocalContext.find?,
    hwf.map_wf.find?_insert]
  rw [if_neg]
  intro heq
  have : fv = other := beq_iff_eq.mp heq
  exact hselected (this.symm ▸ hother)

end Lean4Lean

namespace Lean.Expr

open Lean4Lean

/-! ### Leading binders -/

/-- `LeadingBinders k e body`: `e` is `k` nested `forallE`/`lam` binders (in any mix) around
`body`. Binder domains are unconstrained. This is exactly the input shape that
`ElimNestedInductive.Result.openRestoreParams k` consumes without reaching `unreachable!`. -/
inductive LeadingBinders : Nat → Expr → Expr → Prop
  | zero (e : Expr) : LeadingBinders 0 e e
  | forallE {k : Nat} {n : Name} {t b body : Expr} {bi : BinderInfo} :
      LeadingBinders k b body → LeadingBinders (k + 1) (.forallE n t b bi) body
  | lam {k : Nat} {n : Name} {t b body : Expr} {bi : BinderInfo} :
      LeadingBinders k b body → LeadingBinders (k + 1) (.lam n t b bi) body

namespace LeadingBinders

theorem trans {k m : Nat} {e mid body : Expr} (H₁ : LeadingBinders k e mid)
    (H₂ : LeadingBinders m mid body) : LeadingBinders (m + k) e body := by
  induction H₁ with
  | zero => exact H₂
  | forallE _ ih => exact .forallE (ih H₂)
  | lam _ ih => exact .lam (ih H₂)

theorem instantiate1' {k : Nat} {e body : Expr} (H : LeadingBinders k e body) (a : Expr)
    (j : Nat) : LeadingBinders k (e.instantiate1' a j) (body.instantiate1' a (j + k)) := by
  induction H generalizing j with
  | zero => exact .zero _
  | @forallE k _ _ _ _ _ _ ih =>
    have := ih (j + 1)
    rw [show j + 1 + k = j + (k + 1) by omega] at this
    exact .forallE this
  | @lam k _ _ _ _ _ _ ih =>
    have := ih (j + 1)
    rw [show j + 1 + k = j + (k + 1) by omega] at this
    exact .lam this

end LeadingBinders

private theorem leadingBinders_go {isLambda : Bool} {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind)) →
    ∀ b, LeadingBinders l.length (LocalContext.mkBindingListN.go isLambda lctx l b) b
  | [], _, b => .zero b
  | x :: l, hx, b => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind⟩ := hx x (.head _)
    have ih := leadingBinders_go (isLambda := isLambda) (lctx := lctx) (l := l) (fun y hy => hx y (.tail _ hy))
      (LocalContext.mkBindingList1N isLambda lctx l.reverse x b)
    have hstep : LeadingBinders 1 (LocalContext.mkBindingList1N isLambda lctx l.reverse x b) b := by
      simp only [LocalContext.mkBindingList1N, hfind]
      cases isLambda
      · exact .forallE (.zero b)
      · exact .lam (.zero b)
    simpa [LocalContext.mkBindingListN.go, Nat.add_comm] using ih.trans hstep

/-- When every bound variable is a `cdecl`, `mkBindingListN` (the exact model of
`LocalContext.mkBinding`) adds exactly one binder per variable around `b.abstractN xs`. -/
theorem LeadingBinders.mkBindingListN {isLambda : Bool} {lctx : LocalContext}
    {xs : List FVarId} (hx : ∀ x ∈ xs, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind)) (b : Expr) :
    LeadingBinders xs.length (LocalContext.mkBindingListN isLambda lctx xs b) (b.abstractN xs) := by
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  simpa using leadingBinders_go (l := xs.reverse) (fun x hx' => hx x (List.mem_reverse.1 hx'))
    (b.abstractN xs)

end Lean.Expr
