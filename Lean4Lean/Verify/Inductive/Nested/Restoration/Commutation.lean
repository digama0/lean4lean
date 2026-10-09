import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Restoration.TrRestoredRecursorVal
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

/-! Commutation of executable nested restoration with `Restoration.expr`.

`ElimNestedInductive.Result.restoreNested` opens the common parameters as
free variables and runs `Expr.replace` with `restoreNestedNode`. A matched
auxiliary node `auxI As args` is replaced by the container specialization
applied to `args`; the matched node's parameter arguments are discarded (the
executable assumes they are literally the opened parameters) and its other
arguments are not traversed. `Restoration.expr` instead restores every
argument and substitutes the actual parameter arguments into the head
specialization.

This file provides the executable-side infrastructure: the replacement head
`restoreHead`, the characterisation of `restoreNestedNode` by it, the table
correspondence `RestorationMapAgreement`, the opening of closed parameter
telescopes (`TrExprS.instantiateRevFVars`), and name agreement. The
commutation theorem itself, under the parameter-uniformity side condition
(`Expr.ParamUniform`), is `restorationCommutes` in
`Nested/Restoration/CommutationUniform.lean`.
-/

namespace Lean4Lean.InductiveSignature


theorem Restoration.expr.go_mkApps (r : Restoration) {xs ys : List VExpr}
    (H : List.Forall₂ (fun x y => Restoration.expr.go r x [] = some y) xs ys)
    (f : VExpr) (args : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps f xs) args =
      Restoration.expr.go r f (ys ++ args) := by
  induction H generalizing f with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
    show Restoration.expr.go r (VExpr.mkApps (.app f x) xs) args = _
    rw [ih]
    simp [Restoration.expr.go, hxy]


theorem Restoration.recursorName_of_not_mem {r : Restoration} {name : Name}
    (h : name ∉ r.recursors.map Prod.fst) : r.recursorName name = name := by
  have hnone : r.recursors.find? (fun pair => pair.1 == name) = none := by
    apply List.find?_eq_none.mpr
    intro pair hmem heq
    exact h (List.mem_map.mpr ⟨pair, hmem, by simpa using heq⟩)
  simp [Restoration.recursorName, hnone]

/-- Restoration is the identity on syntax mentioning none of its names. -/
theorem Restoration.expr.go_of_not_contains (r : Restoration) {e : VExpr}
    (H : e.containsAnyConst r.restorableNames = false) (args : List VExpr) :
    Restoration.expr.go r e args = some (VExpr.mkApps e args) := by
  induction e generalizing args with
  | bvar | sort | elim => rfl
  | const name levels =>
    have hname : name ∉ r.restorableNames := by
      simpa [VExpr.containsAnyConst] using H
    simp only [Restoration.restorableNames, List.mem_append, not_or] at hname
    simp [Restoration.expr.go, Restoration.heads_find?_eq_none hname.1,
      Restoration.recursorName_of_not_mem hname.2]
  | app fn arg ihfn iharg =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, iharg H.2, ihfn H.1, VExpr.mkApps]
  | lam domain body ihd ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, ihd H.1, ihb H.2, VExpr.mkApps]
  | forallE domain body ihd ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, ihd H.1, ihb H.2, VExpr.mkApps]
  | proj name i major ih =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, ih H.2, VExpr.mkApps]

end Lean4Lean.InductiveSignature

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature (Restoration HeadSpecialization instantiateParams)

namespace VerifyInductive

/-- The executable replacement head for one restorable auxiliary name: the
expression `restoreNestedNode` applies to the non-parameter arguments of a
matched node. -/
def restoreHead (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (c : Name) : Option Expr :=
  match result.aux2nested.find? c with
  | some nested => some ((nested.abstract result.params).instantiateRev As)
  | none =>
    match result.getNestedIfAuxCtor env c with
    | some (nested, auxI) =>
      let nested' := (nested.abstract result.params).instantiateRev As
      match nested'.getAppFn with
      | .const I_c I_ls =>
        some (mkAppN (.const (c.replacePrefix auxI I_c) I_ls) nested'.getAppArgs)
      | _ => none
    | none => none

theorem restoreNestedNode_eq_of_notRecursor
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr)
    (hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none) :
    result.restoreNestedNode env As auxRec t =
      match t.getAppFn with
      | .const c _ => (restoreHead result env As c).bind fun H =>
          if result.nparams ≤ t.getAppArgs.size then
            some (mkAppRange H result.nparams t.getAppArgs.size t.getAppArgs)
          else none
      | _ => none := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreNestedNode
  simp only []
  split
  · rename_i c ls
    simp only [hnotrec c ls rfl]
    generalize (Expr.const c ls).getAppArgs = args
    generalize (Expr.const c ls).getAppFn = fn
    cases fn with
    | const c us =>
      simp only [restoreHead]
      cases hn : result.aux2nested.find? c with
      | some nested => simp [panicWithPosWithDecl, panic, panicCore]; rfl
      | none =>
        cases hc : result.getNestedIfAuxCtor env c with
        | none => simp
        | some pair =>
          rcases pair with ⟨nested, auxI⟩
          simp only [Expr.withApp_eq]
          split <;> split <;> simp_all [panicWithPosWithDecl, panic, panicCore] <;> rfl
    | _ => rfl
  · generalize t.getAppArgs = args
    generalize t.getAppFn = fn
    cases fn with
    | const c us =>
      simp only [restoreHead]
      cases hn : result.aux2nested.find? c with
      | some nested => simp [panicWithPosWithDecl, panic, panicCore]; rfl
      | none =>
        cases hc : result.getNestedIfAuxCtor env c with
        | none => simp
        | some pair =>
          rcases pair with ⟨nested, auxI⟩
          simp only [Expr.withApp_eq]
          split <;> split <;> simp_all [panicWithPosWithDecl, panic, panicCore] <;> rfl
    | _ => rfl

/-- Two binder-only contexts with the same variable naming. -/
inductive VLCtx.VLamShape : VLCtx → VLCtx → Prop
  | nil : VLCtx.VLamShape [] []
  | cons {left right : VLCtx} {ofv : Option (FVarId × List FVarId)} {x y : VExpr} :
      VLCtx.VLamShape left right →
      VLCtx.VLamShape ((ofv, .vlam x) :: left) ((ofv, .vlam y) :: right)

theorem VLCtx.VLamShape.append {a b c d : VLCtx} (H₁ : VLCtx.VLamShape a b)
    (H₂ : VLCtx.VLamShape c d) : VLCtx.VLamShape (a ++ c) (b ++ d) := by
  induction H₁ with
  | nil => simpa using H₂
  | cons _ ih => exact .cons ih

theorem restoreNestedNode_eq_none_of_restoreHead
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr)
    (hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none)
    (hhead : ∀ c ls, t.getAppFn = .const c ls → restoreHead result env As c = none) :
    result.restoreNestedNode env As auxRec t = none := by
  rw [restoreNestedNode_eq_of_notRecursor result env As auxRec t hnotrec]
  cases hfn : t.getAppFn with
  | const c ls => simp [hhead c ls hfn]
  | _ => rfl

theorem restoreNestedNode_eq_of_restoreHead
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr)
    (hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none)
    (hfn : t.getAppFn = .const c ls) (hhead : restoreHead result env As c = some H)
    (hsize : result.nparams ≤ t.getAppArgsList.length) :
    result.restoreNestedNode env As auxRec t =
      some (Expr.mkAppList H (t.getAppArgsList.drop result.nparams)) := by
  rw [restoreNestedNode_eq_of_notRecursor result env As auxRec t hnotrec, hfn]
  have hsize' : result.nparams ≤ t.getAppArgs.size := by
    rw [← Array.length_toList, Expr.getAppArgs_toList]; exact hsize
  simp only [hhead, Option.bind_some, if_pos hsize']
  congr 1
  apply Expr.mkAppRange_eq (l₁ := t.getAppArgsList.take result.nparams) (l₃ := [])
  · simp [Expr.getAppArgs_toList]
  · simp; omega
  · simp [← Array.length_toList, Expr.getAppArgs_toList]

/-- A successful callback at the root fixes the output of `Expr.replace`. -/
theorem ExprReplacement.output_of_occurrence
    (H : ExprReplacement replaceNode input output)
    (h : replaceNode input = some out) : output = out := by
  rw [H.eq_replace]
  simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]

/-- Correspondence between the executable restoration tables and an abstract
restoration `r` (intended: `compilationRestoration source auxiliaries`).

* `recursorName`: `auxRec` (from `mkAuxRecNameMap`) is `r.recursorName`.
* `recursorNotHead`: renamed recursors are not specialization heads.
* `headNone`/`head`: a name has an executable replacement head
  (`restoreHead`: an `aux2nested` family, or a constructor of one) exactly
  when it is an abstract head. For a head, the specialization has the
  executable's parameter count, the auxiliary constant's universe arity, and
  the executable replacement head translates to the specialization applied
  to the translated parameters, at the levels `auxLevels` (on the lowered
  side, `lparams.map .param`). The translation clause is only required for
  the opened parameters of a matched node: free variables, exactly
  `result.nparams` of them (the executable instantiation is sequential, so
  it is not a simultaneous substitution for open arguments). -/
structure RestorationMapAgreement (r : Restoration)
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (auxRec : NameMap Name) (targetEnv : VEnv) (Us : List Name)
    (auxLevels : List Level) : Prop where
  recursorName : ∀ c, r.recursorName c = (auxRec.find? c).getD c
  recursorNotHead : ∀ c new, auxRec.find? c = some new →
    c ∉ r.heads.map (·.auxiliary)
  headNone : ∀ As c, restoreHead result env As c = none →
    c ∉ r.heads.map (·.auxiliary)
  head : ∀ As c H, restoreHead result env As c = some H →
    ∃ h : HeadSpecialization, r.heads.find? (fun h => h.auxiliary == c) = some h ∧
      h.nparams = result.nparams ∧
      ∀ levels, auxLevels.mapM (VLevel.ofLevel Us) = some levels →
        h.uvars = levels.length ∧
        ∀ (Δ : VLCtx) (params : List VExpr) (v : VExpr),
          (∀ a ∈ As.toList, ∃ fv, a = .fvar fv) → As.size = result.nparams →
          List.Forall₂ (TrExprS targetEnv Us Δ) As.toList params →
          TrExprS targetEnv Us Δ H v →
          v = VExpr.mkApps (.const h.target (h.levels.map (·.inst levels)))
            (h.arguments.map fun arg => instantiateParams (arg.instL levels) params)
  /-- The executable constructor renaming (`restoreCtorName`, a prefix
  replacement by the container family's name) is the abstract head target. -/
  ctorTarget : ∀ c nested auxI, result.aux2nested.find? c = none →
    result.getNestedIfAuxCtor env c = some (nested, auxI) →
    ∃ I ls, nested.getAppFn = .const I ls ∧
      r.restoredHeadName c = c.replacePrefix auxI I

theorem RestorationMapAgreement.notRecursor_of_head
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hhead : restoreHead result env As c ≠ none) : auxRec.find? c = none := by
  cases hfind : auxRec.find? c with
  | none => rfl
  | some new =>
    exfalso
    apply A.recursorNotHead c new hfind
    rcases Option.ne_none_iff_exists.mp hhead with ⟨H, hH⟩
    rcases A.head As c H hH.symm with ⟨h, hh, _⟩
    exact List.mem_map.mpr ⟨h, List.mem_of_find?_eq_some hh,
      by simpa using List.find?_some hh⟩

/-- Restoration of a constant that is not an executable replacement head is
the executable recursor renaming. -/
theorem RestorationMapAgreement.go_const
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hhead : restoreHead result env As c = none) (levels : List VLevel)
    (args : List VExpr) :
    Restoration.expr.go r (.const c levels) args =
      some (VExpr.mkApps (.const ((auxRec.find? c).getD c) levels) args) := by
  simp [Restoration.expr.go,
    Restoration.heads_find?_eq_none (A.headNone As c hhead), A.recursorName]

/-! ### Opening closed translations -/

/-- Converse of `TrExprS.abstract`: instantiating an abstracted binder with
the free variable it stands for preserves the translation. -/
theorem TrExprS.instantiateFVar {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    {e : Expr} {e' : VExpr}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrExprS env Us Δ e e') (hfresh : e.FVarIdsIn (· ≠ v₀)) :
    TrExprS env Us Δ₁ (e.instantiate1' (.fvar v₀) dk) e' := by
  induction H generalizing dk k Δ₁ with
  | bvar h1 =>
    rename_i x A Δ' i
    have hfind := W.find? (v := .inl i) (by nofun)
    simp only [Expr.instantiate1']
    by_cases hlt : i < dk
    · simp only [hlt, if_true] at hfind ⊢
      exact .bvar (hfind ▸ h1)
    · by_cases heq : i = dk
      · subst heq
        simp only [Nat.lt_irrefl, if_true, if_false] at hfind ⊢
        rw [hfind] at h1
        simpa [Expr.liftLooseBVars'] using (TrExprS.fvar h1 : TrExprS env Us Δ₁ (.fvar v₀) x)
      · simp only [hlt, heq, if_false] at hfind ⊢
        exact .bvar (hfind ▸ h1)
  | @fvar Δ x A fv h1 =>
    have hne : fv ≠ v₀ := hfresh
    have hfind := W.find? (v := .inr fv) (by simpa using hne)
    exact .fvar (hfind ▸ h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hfresh.1) (ih2 W hfresh.2)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (W.toCtx ▸ h1) (ih1 W hfresh.1) (ih2 W.succ hfresh.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hfresh.1) (ih2 W.succ hfresh.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W hfresh.1) (ih2 W hfresh.2.1) (ih3 W.succ hfresh.2.2)
  | lit h1 h2 ih =>
    refine .lit h1 ?_
    have := ih W (FVarsIn_to_FVarIdsIn FVarsIn.toConstructor)
    rwa [Expr.instantiate1'_eq_self Closed.toConstructor.looseBVarRange_le] at this
  | mdata _ ih => exact .mdata (ih W hfresh)
  | proj _ h2 ih => exact .proj (ih W hfresh) (W.toCtx ▸ h2)


/-- The fvar-form context of an opened parameter telescope: the innermost
parameter first, every entry an ordinary binder with no dependencies. -/
def fvarScope : List FVarId → List VExpr → VLCtx
  | f :: fs, d :: ds => fvarScope fs ds ++ [(some (f, []), .vlam d)]
  | _, _ => []

theorem fvarScope_vlamShape :
    ∀ (fvars : List FVarId) (left right : List VExpr),
      left.length = right.length →
      VLCtx.VLamShape (fvarScope fvars left) (fvarScope fvars right)
  | [], _, _, _ => by simp [fvarScope]; exact .nil
  | _ :: _, [], [], _ => by simp [fvarScope]; exact .nil
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | f :: fs, l :: ls, r :: rs, h => by
    simp only [fvarScope]
    exact VLCtx.VLamShape.append (fvarScope_vlamShape fs ls rs (by simpa using h))
      (.cons .nil)

private theorem abstract_prefix (Δb : VLCtx) (f : FVarId) (d : VLocalDecl) :
    ∀ pre : List VExpr,
      VLCtx.Abstract Δb f d pre.length pre.length
        (pre.map (fun t => ((none : Option (FVarId × List FVarId)), VLocalDecl.vlam t)) ++
          (some (f, []), d) :: Δb)
        (pre.map (fun t => ((none : Option (FVarId × List FVarId)), VLocalDecl.vlam t)) ++
          (none, d) :: Δb)
  | [] => .zero
  | t :: pre => by
    simpa [VLocalDecl.depth] using (abstract_prefix Δb f d pre).succ (d := .vlam t)

/-- Opening a de Bruijn parameter telescope with fresh free variables
preserves the translation of its body. -/
theorem TrExprS.instantiateRevFVars {env : VEnv} {Us : List Name} :
    ∀ (fvars : List FVarId) (domains : List VExpr) (Δb : VLCtx) (X : Expr) (v : VExpr),
      fvars.length = domains.length → fvars.Nodup → X.FVarIdsIn (· ∉ fvars) →
      TrExprS env Us (abstractForallContext domains Δb) X v →
      TrExprS env Us (fvarScope fvars domains ++ Δb)
        (X.instantiateRevList (fvars.map .fvar)) v
  | [], domains, Δb, X, v, hlen, _, _, H => by
    have : domains = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst this
    simpa [fvarScope, abstractForallContext] using H
  | f :: fs, [], _, _, _, hlen, _, _, _ => by simp at hlen
  | f :: fs, d :: ds, Δb, X, v, hlen, hnodup, hfresh, H => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.nodup_cons] at hnodup
    have W := abstract_prefix Δb f (.vlam d) ds.reverse
    have Hctx : abstractForallContext (d :: ds) Δb =
        ds.reverse.map (fun t => ((none : Option (FVarId × List FVarId)),
          VLocalDecl.vlam t)) ++ (none, .vlam d) :: Δb := by
      simp [abstractForallContext]
    rw [Hctx] at H
    have H1 := TrExprS.instantiateFVar W H
      (hfresh.mono fun fv hfv heq => hfv (heq ▸ List.mem_cons_self))
    have Hctx' : ds.reverse.map (fun t => ((none : Option (FVarId × List FVarId)),
          VLocalDecl.vlam t)) ++ (some (f, []), .vlam d) :: Δb =
        abstractForallContext ds ((some (f, []), .vlam d) :: Δb) := by
      simp [abstractForallContext]
    rw [Hctx'] at H1
    have hfresh1 : (X.instantiate1' (.fvar f) ds.reverse.length).FVarIdsIn (· ∉ fs) :=
      (hfresh.mono fun fv hfv hmem => hfv (List.mem_cons_of_mem _ hmem)).instantiate1_go
        (show (Expr.fvar f).FVarIdsIn (· ∉ fs) from hnodup.1)
    have IH := TrExprS.instantiateRevFVars fs ds _ _ v hlen hnodup.2 hfresh1 H1
    have hcomm := Expr.instantiateRevList_instantiate1'_fvars X f fs 0 0
    simp only [Nat.zero_add, Nat.add_zero] at hcomm
    rw [List.length_reverse, ← hlen, hcomm] at IH
    simpa [fvarScope, List.append_assoc] using IH

/-! ### Names -/

theorem nameMap_getD_eq (m : NameMap Name) (k d : Name) :
    Std.TreeMap.getD m k d = (m.find? k).getD d := by
  simp only [NameMap.find?]
  exact Std.TreeMap.getD_eq_getD_getElem?

end VerifyInductive
end Lean4Lean
