import Lean4Lean.Verify.TypeChecker.Basic

/-! Lambda-only metacontexts, telescope domains, and agreement of binder prefixes. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Every declaration of the `MLCtx` is a local assumption (`cdecl`), as in the local
contexts the inductive checker builds: it opens binders but never adds let declarations. -/
def MLCtxOnlyLams (m : TypeChecker.MLCtx) : Prop :=
  ∀ d ∈ m.decls, ∃ index fv name type bi kind,
    d = .cdecl index fv name type bi kind

theorem MLCtxOnlyLams.nil : MLCtxOnlyLams .nil := by
  intro d hd
  simp [TypeChecker.MLCtx.decls] at hd

theorem MLCtxOnlyLams.vlam
    (H : MLCtxOnlyLams m) :
    MLCtxOnlyLams (.vlam fv name type type' bi m) := by
  intro d hd
  simp only [TypeChecker.MLCtx.decls, List.mem_cons] at hd
  rcases hd with rfl | hd
  · exact ⟨_, _, _, _, _, _, rfl⟩
  · exact H d hd

theorem MLCtxOnlyLams.tail_vlam
    (H : MLCtxOnlyLams (.vlam fv name type type' bi m)) :
    MLCtxOnlyLams m := by
  intro d hd
  exact H d (by simp [TypeChecker.MLCtx.decls, hd])

theorem MLCtxOnlyLams.vlet_false
    (H : MLCtxOnlyLams (.vlet fv name type value type' value' m)) : False := by
  rcases H (.ldecl m.length fv name type value false default)
      (by simp [TypeChecker.MLCtx.decls]) with
    ⟨index, fv', name', type', bi, kind, h⟩
  cases h

/-- An all-lambda metacontext loses no declarations when projected to its
anonymous typing context. -/
theorem MLCtxOnlyLams.toCtx_length
    (H : MLCtxOnlyLams m) : m.vlctx.toCtx.length = m.length := by
  induction m with
  | nil => rfl
  | vlam fv name type type' bi tail ih =>
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.toCtx,
      TypeChecker.MLCtx.length, List.length_cons]
    rw [ih H.tail_vlam]
  | vlet fv name type value type' value' tail ih =>
    exact H.vlet_false.elim

/-- Every declaration of an all-lambda metacontext owns one free-variable
identifier, so its concrete free-variable list also preserves length. -/
theorem MLCtxOnlyLams.fvars_length
    (H : MLCtxOnlyLams m) : m.vlctx.fvars.length = m.length := by
  induction m with
  | nil => rfl
  | vlam fv name type type' bi tail ih =>
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      TypeChecker.MLCtx.length, List.length_cons]
    rw [ih H.tail_vlam]
  | vlet fv name type value type' value' tail ih =>
    exact H.vlet_false.elim

theorem MLCtxOnlyLams.dropN
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length) :
    MLCtxOnlyLams (m.dropN n hn) := by
  induction n generalizing m with
  | zero => simpa using H
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simpa only [TypeChecker.MLCtx.dropN] using
        ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Dropping a recent all-lambda prefix does not change lookup of any free
variable that remains in the older context. -/
theorem MLCtxOnlyLams.dropN_find?_eq
    (H : MLCtxOnlyLams m) (Hwf : m.WF env Us)
    (n : Nat) (hn : n ≤ m.length)
    (hfv : fv ∈ (m.dropN n hn).vlctx.fvars) :
    m.lctx.find? fv = (m.dropN n hn).lctx.find? fv := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam current name type type' bi tail =>
      have htailMem : fv ∈ tail.vlctx.fvars :=
        TypeChecker.MLCtx.dropN_fvars_subset n
          (Nat.le_of_succ_le_succ hn) hfv
      have hcurrentFresh : current ∉ tail.vlctx.fvars :=
        Hwf.1.tr.find?_eq_none.1 Hwf.2.1
      have hne : current ≠ fv := by
        intro heq
        exact hcurrentFresh (heq ▸ htailMem)
      simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
        LocalContext.find?]
      rw [Hwf.1.tr.1.map_wf.find?_insert, if_neg]
      · exact ih H.tail_vlam Hwf.1 (Nat.le_of_succ_le_succ hn) hfv
      · intro heq
        exact hne (LawfulBEq.eq_of_beq heq)
    | vlet current name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Abstract domains introduced by `MLCtx.mkForall'`, in outermost-to-
innermost order. Local lets are discharged by `mkForall'` and contribute no
domain. -/
def MLCtxForallDomains (c : TypeChecker.MLCtx) :
    (n : Nat) → n ≤ c.length → List VExpr
  | 0, _ => []
  | n + 1, h =>
    match c with
    | .vlam _ _ _ type' _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h) ++ [type']
    | .vlet _ _ _ _ _ _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h)

theorem TypeChecker.MLCtx.mkForall'_eq_wrapForalls
    (c : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ c.length) (body : VExpr) :
    c.mkForall' n hn body =
      VExpr.wrapForalls (MLCtxForallDomains c n hn) body := by
  induction n generalizing c body with
  | zero => simp [TypeChecker.MLCtx.mkForall', MLCtxForallDomains,
      VExpr.wrapForalls]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      rw [ih, VExpr.wrapForalls_append]
      rfl
    | vlet fv name type value type' value' c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      exact ih c (Nat.le_of_succ_le_succ hn) body

theorem TypeChecker.MLCtx.mkLambda'_eq_wrapLams
    (c : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ c.length) (body : VExpr) :
    c.mkLambda' n hn body =
      VExpr.wrapLams (MLCtxForallDomains c n hn) body := by
  induction n generalizing c body with
  | zero => simp [TypeChecker.MLCtx.mkLambda', MLCtxForallDomains,
      VExpr.wrapLams]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi c =>
      simp only [TypeChecker.MLCtx.mkLambda', MLCtxForallDomains]
      rw [ih, VExpr.wrapLams_append]
      rfl
    | vlet fv name type value type' value' c =>
      simp only [TypeChecker.MLCtx.mkLambda', MLCtxForallDomains]
      exact ih c (Nat.le_of_succ_le_succ hn) body

theorem MLCtxOnlyLams.forallDomains_length
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    (MLCtxForallDomains c n hn).length = n := by
  induction n generalizing c with
  | zero => simp [MLCtxForallDomains]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [MLCtxForallDomains, List.length_append,
        List.length_singleton]
      rw [ih H.tail_vlam (Nat.le_of_succ_le_succ hn)]
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

theorem MLCtxOnlyLams.forallDomains_eq_take_reverse
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    MLCtxForallDomains c n hn = (c.vlctx.toCtx.take n).reverse := by
  induction n generalizing c with
  | zero => simp [MLCtxForallDomains]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [MLCtxForallDomains, TypeChecker.MLCtx.vlctx,
        VLCtx.toCtx, List.take_succ_cons, List.reverse_cons]
      rw [ih H.tail_vlam (Nat.le_of_succ_le_succ hn)]
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Splitting an all-lambda checker context after a recent prefix exposes
exactly the reversed `MLCtxForallDomains` followed by the older context. -/
theorem MLCtxOnlyLams.toCtx_eq_forallDomains_reverse_append_dropN
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    c.vlctx.toCtx =
      (MLCtxForallDomains c n hn).reverse ++ (c.dropN n hn).vlctx.toCtx := by
  induction n generalizing c with
  | zero => simp [MLCtxForallDomains]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, VLCtx.toCtx,
        MLCtxForallDomains, List.reverse_append, List.reverse_singleton,
        List.singleton_append, TypeChecker.MLCtx.dropN]
      simpa [List.append_assoc] using congrArg (type' :: ·)
        (ih H.tail_vlam (Nat.le_of_succ_le_succ hn))
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- For a verifier context containing only local declarations, dropping the
newest `n` entries before or after erasing local metadata gives the same
ordinary typing context. -/
theorem MLCtxOnlyLams.toCtx_dropN
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    (c.dropN n hn).vlctx.toCtx = c.vlctx.toCtx.drop n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simpa only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx,
        VLCtx.toCtx, List.drop_succ_cons] using
          ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

theorem MLCtxOnlyLams.vlctx_dropN
    (H : MLCtxOnlyLams c) (n : Nat) (hn : n ≤ c.length) :
    (c.dropN n hn).vlctx = c.vlctx.drop n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simpa only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx,
        List.drop_succ_cons] using
          ih H.tail_vlam (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- Dropping an ordinary-local suffix and then restoring it is precisely a
free-variable weakening.  The generated inductive contexts contain no local
lets, so the lift amount agrees with the number of dropped declarations. -/
theorem MLCtxOnlyLams.dropN_fvlift
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length) :
    VLCtx.FVLift (m.dropN n hn).vlctx m.vlctx 0 n 0 := by
  induction n generalizing m with
  | zero => exact .refl
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      have Htail := H.tail_vlam
      have W := ih Htail (Nat.le_of_succ_le_succ hn)
      simpa only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx,
        VLocalDecl.depth, Nat.add_comm] using
          VLCtx.FVLift.skip_fvar (fv, type.fvarsList) (.vlam type') W
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

@[simp] theorem TypeChecker.MLCtx.vlctx_length
    (m : TypeChecker.MLCtx) : m.vlctx.length = m.length := by
  induction m <;> simp_all [TypeChecker.MLCtx.vlctx]

/-- The newest `n` local declarations are exactly the prefix removed by
`dropN`.  This purely structural fact is useful when a semantic invariant
describes the older context as a distinguished suffix. -/
theorem TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    (m : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ m.length) :
    m.vlctx = m.vlctx.take n ++ (m.dropN n hn).vlctx := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        TypeChecker.MLCtx.dropN, List.cons_append]
      congr 1
      exact ih tail (Nat.le_of_succ_le_succ hn)
    | vlet fv name type value type' value' tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        TypeChecker.MLCtx.dropN, List.cons_append]
      congr 1
      exact ih tail (Nat.le_of_succ_le_succ hn)

/-- The free-variable identifiers in the newest `n` verifier declarations
are exactly `fvarRevList`. -/
theorem TypeChecker.MLCtx.vlctx_take_fvars
    (m : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ m.length) :
    VLCtx.fvars (m.vlctx.take n) = m.fvarRevList n hn := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        VLCtx.fvars_cons_some, TypeChecker.MLCtx.fvarRevList,
        List.cons.injEq]
      exact ⟨trivial, ih tail (Nat.le_of_succ_le_succ hn)⟩
    | vlet fv name type value type' value' tail =>
      simp only [TypeChecker.MLCtx.vlctx, List.take_succ_cons,
        VLCtx.fvars_cons_some, TypeChecker.MLCtx.fvarRevList,
        List.cons.injEq]
      exact ⟨trivial, ih tail (Nat.le_of_succ_le_succ hn)⟩

/-- The free variables of an `MLCtx` in insertion order. -/
def _root_.Lean4Lean.TypeChecker.MLCtx.fvarList : TypeChecker.MLCtx → List FVarId
  | .nil => []
  | .vlam id _ _ _ _ c => c.fvarList ++ [id]
  | .vlet id _ _ _ _ _ c => c.fvarList ++ [id]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.fvarList_length (m : TypeChecker.MLCtx) :
    m.fvarList.length = m.length := by
  induction m <;> simp_all [TypeChecker.MLCtx.fvarList]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.decls_fvarId (m : TypeChecker.MLCtx) :
    m.decls.map (·.fvarId) = m.fvarList.reverse := by
  induction m <;> simp_all [TypeChecker.MLCtx.fvarList, TypeChecker.MLCtx.decls,
    LocalDecl.fvarId]

/-- The entry of a lambda-only `MLCtx` holding its `k`-th free variable, and
the context of the entries before it. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.dropN_of_fvarList_getElem? :
    ∀ (m : TypeChecker.MLCtx), MLCtxOnlyLams m → ∀ {k : Nat} {fv : FVarId},
      m.fvarList[k]? = some fv →
      ∃ (j : Nat) (hj : j + 1 ≤ m.length) (name : Name) (ty : Expr) (ty' : VExpr)
        (bi : BinderInfo),
        m.dropN j (Nat.le_of_succ_le hj) =
          .vlam fv name ty ty' bi (m.dropN (j + 1) hj) ∧
        m.fvarList.take k = (m.dropN (j + 1) hj).fvarList
  | .nil, _, _, _, h => by simp [TypeChecker.MLCtx.fvarList] at h
  | .vlet .., honly, _, _, _ => honly.vlet_false.elim
  | .vlam id name ty ty' bi c, honly, k, fv, h => by
    simp only [TypeChecker.MLCtx.fvarList] at h
    by_cases hk : k < c.fvarList.length
    · rw [List.getElem?_append_left hk] at h
      obtain ⟨j, hj, name', ty₁, ty₁', bi', heq, htake⟩ :=
        TypeChecker.MLCtx.dropN_of_fvarList_getElem? c honly.tail_vlam h
      refine ⟨j + 1, by simp; omega, name', ty₁, ty₁', bi', heq, ?_⟩
      simp only [TypeChecker.MLCtx.fvarList]
      rw [List.take_append_of_le_length (by omega)]
      exact htake
    · rw [List.getElem?_append_right (by omega)] at h
      have hk' : k = c.fvarList.length := by
        have := List.getElem?_eq_some_iff.mp h
        simp at this; omega
      subst hk'
      simp at h
      subst h
      refine ⟨0, by simp, name, ty, ty', bi, rfl, ?_⟩
      simp [TypeChecker.MLCtx.fvarList]

/-- Two executable contexts agree on their `n` most recent declarations: the
same named lambdas with the same source domains, possibly translated
differently.  This relates a main context to the checker context of the same
run. -/
inductive MLCtxTopAgree : TypeChecker.MLCtx → TypeChecker.MLCtx → Nat → Prop
  | zero (a b : TypeChecker.MLCtx) : MLCtxTopAgree a b 0
  | vlam {a b : TypeChecker.MLCtx} {n : Nat} (h : MLCtxTopAgree a b n)
      (fv name ty t₁ t₂ bi) :
      MLCtxTopAgree (.vlam fv name ty t₁ bi a) (.vlam fv name ty t₂ bi b) (n + 1)

theorem MLCtxTopAgree.fvarRevList_eq {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (ha : n ≤ a.length) (hb : n ≤ b.length) :
    a.fvarRevList n ha = b.fvarRevList n hb := by
  induction H with
  | zero => simp
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [TypeChecker.MLCtx.fvarRevList]
    rw [ih]

theorem MLCtxTopAgree.stepDropEq {a b M : TypeChecker.MLCtx} {n : Nat}
    (fv name ty t₁ t₂ bi)
    (h : ∃ hn : n ≤ b.length, MLCtxTopAgree a b n ∧ b.dropN n hn = M) :
    ∃ hn : n + 1 ≤ (TypeChecker.MLCtx.vlam fv name ty t₂ bi b).length,
      MLCtxTopAgree (.vlam fv name ty t₁ bi a) (.vlam fv name ty t₂ bi b) (n + 1) ∧
        (TypeChecker.MLCtx.vlam fv name ty t₂ bi b).dropN (n + 1) hn = M := by
  obtain ⟨hn, hag, hd⟩ := h
  exact ⟨by simpa using hn, hag.vlam fv name ty t₁ t₂ bi, by simpa using hd⟩

/-- `MLCtxTopAgree.stepDropEq`, additionally carrying the closure of the checker translation
of the current telescope back to the base context. -/
theorem MLCtxTopAgree.stepDropForall {env : VEnv} {U : Nat}
    {a b : TypeChecker.MLCtx} {n : Nat} {V : VLCtx} {T₀ X : VExpr}
    (fv name ty t₁ t₂ bi)
    (h : ∃ hn : n ≤ b.length, MLCtxTopAgree a b n ∧ (b.dropN n hn).vlctx = V ∧
      env.IsDefEqU U V.toCtx T₀ (b.mkForall' n hn (.forallE t₂ X))) :
    ∃ hn : n + 1 ≤ (TypeChecker.MLCtx.vlam fv name ty t₂ bi b).length,
      MLCtxTopAgree (.vlam fv name ty t₁ bi a) (.vlam fv name ty t₂ bi b) (n + 1) ∧
        ((TypeChecker.MLCtx.vlam fv name ty t₂ bi b).dropN (n + 1) hn).vlctx = V ∧
        env.IsDefEqU U V.toCtx T₀
          ((TypeChecker.MLCtx.vlam fv name ty t₂ bi b).mkForall' (n + 1) hn X) := by
  obtain ⟨hn, hag, hd, he⟩ := h
  exact ⟨by simpa using hn, hag.vlam fv name ty t₁ t₂ bi, by simpa using hd,
    by simpa using he⟩

theorem MLCtxTopAgree.forallDomains_length {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hn : n ≤ b.length) :
    (MLCtxForallDomains b n hn).length = n := by
  induction H with
  | zero => simp [MLCtxForallDomains]
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [MLCtxForallDomains, List.length_append, List.length_singleton]
    rw [ih]

theorem MLCtxTopAgree.toCtx_split {a b : TypeChecker.MLCtx} {n : Nat}
    (H : MLCtxTopAgree a b n) (hn : n ≤ b.length) :
    b.vlctx.toCtx =
      (MLCtxForallDomains b n hn).reverse ++ (b.dropN n hn).vlctx.toCtx := by
  induction H with
  | zero => simp [MLCtxForallDomains]
  | vlam h fv name ty t₁ t₂ bi ih =>
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.toCtx,
      MLCtxForallDomains, List.reverse_append, List.reverse_singleton,
      List.singleton_append, TypeChecker.MLCtx.dropN]
    simpa [List.append_assoc] using congrArg (t₂ :: ·)
      (ih (Nat.le_of_succ_le_succ hn))

end VerifyInductive

end Lean4Lean
