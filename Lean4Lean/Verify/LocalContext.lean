import Lean4Lean.Std.PersistentHashMap
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean.LocalContext

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

theorem mkBinding_eq :
    mkBinding isLambda lctx ⟨xs.map .fvar⟩ b = mkBindingList isLambda lctx xs b := by
  simp only [mkBinding, List.getElem_toArray, Expr.abstractRange_eq, Expr.hasLooseBVar_eq,
    Expr.abstract_eq, ← Array.take_eq_extract, List.take_toArray, Bool.and_false,
    ← List.map_take, List.getElem_map, Expr.lowerLooseBVars_eq]
  dsimp only [Array.size]
  simp only [List.getElem_eq_getElem?_get, Option.get_eq_getD (fallback := default)]
  change Nat.foldRev _ (fun i x =>
    mkBindingList1 isLambda lctx (xs.take i) (xs[i]?.getD default)) .. = mkBindingList.go ..
  rw [List.length_map]; generalize eq : xs.length = n
  generalize b.abstractList xs = b
  induction n generalizing xs b with
  | zero => let [] := xs; simp [mkBindingList.go]
  | succ n ih =>
    obtain rfl | ⟨xs, a, rfl⟩ := List.eq_nil_or_concat xs; · cases eq
    simp at eq ⊢; subst eq
    simp +contextual only [Nat.le_of_lt, List.take_append_of_le_length,
      List.getElem?_append_left, mkBindingList.go, ih]; simp

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
open scoped List

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

theorem TrLCtx'.noBV : TrLCtx' env Us ds Δ → Δ.NoBV
  | .nil => rfl
  | .cons h _ => h.noBV

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

theorem TrLCtx'.find?_of_mem (henv : env.WF) (H : TrLCtx' env Us ds Δ)
    (nd : (ds.map (·.fvarId)).Nodup) (hm : decl ∈ ds) :
    ∃ e A, Δ.find? (.inr decl.fvarId) = some (e, A) ∧
      FVarsBelow Δ (.fvar decl.fvarId) decl.type ∧
      TrExprS env Us Δ decl.type A := by
  have := H.wf nd
  match H with
  | .nil => cases hm
  | .cons (ds := ds) h1 h2 =>
    simp [VLCtx.find?, VLCtx.next]
    obtain _ | ⟨_, hm : decl ∈ ds⟩ := hm
    · simp [and_assoc]
      cases h2 with
      | vlam h2 h3 =>
        constructor
        · intro P hP he; exact fvarsIn_iff.2 ⟨(hP.1 he).1, h2.fvarsIn.mono fun _ _ => ⟨⟩⟩
        · exact h2.weakFV henv (.skip_fvar _ _ .refl) this
      | vlet h2 h3 =>
        constructor
        · intro P hP he; have := hP.1 he; simp [LocalDecl.deps, or_imp, forall_and] at this
          exact fvarsIn_iff.2 ⟨this.1.1, h2.fvarsIn.mono fun _ _ => ⟨⟩⟩
        · simpa [VLocalDecl.depth] using h2.weakFV henv (.skip_fvar _ _ .refl) this
    · simp at nd; rw [if_neg (by simpa using Ne.symm (nd.1 _ hm))]; simp
      have ⟨_, _, h1, h2, h3⟩ := h1.find?_of_mem henv nd.2 hm
      refine ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, fun _ h => h2 _ h.2, ?_⟩
      simpa using h3.weakFV henv (.skip_fvar _ _ .refl) this

theorem TrLCtx.find?_of_mem (henv : env.WF) (H : TrLCtx env Us lctx Δ)
    (hm : decl ∈ lctx.toList) :
    ∃ e A, Δ.find? (.inr decl.fvarId) = some (e, A) ∧
      FVarsBelow Δ (.fvar decl.fvarId) decl.type ∧
      TrExprS env Us Δ decl.type A :=
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
