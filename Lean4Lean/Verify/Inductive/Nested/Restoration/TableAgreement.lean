import Lean4Lean.Verify.Inductive.Nested.Install.RunView
import Lean4Lean.Verify.Inductive.Nested.Restoration.CommutationUniform
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExpansionInverse
import Lean4Lean.Std.List

/-! Agreement of the executable nested restoration tables with the abstract
`compilationRestoration`.

The executable restores an auxiliary node by reopening the container
application `nested` recorded in `aux2nested` at the opened parameters
(`(nested.abstract result.params).instantiateRev As`). The abstract
restoration instead substitutes the translated parameters into the
specialisation arguments (`instantiateParams`). The link between the two is
an inversion lemma for translation (`TrExprS.instantiateRevList_inv`): the
translation of an instantiation at free variables is the substitution of
their translations into any translation of the abstracted body, at any
universe-parameter list into which the body's parameter names translate.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! ### Universe reindexing -/

theorem VLevel.ofLevel_reindex {Us₀ Us : List Name} {ls : List VLevel}
    (hls : (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some ls) :
    ∀ {l : Level} {l' : VLevel}, VLevel.ofLevel Us₀ l = some l' →
      VLevel.ofLevel Us l = some (l'.inst ls) := by
  have hfor := List.mapM_eq_some.1 hls
  intro l
  induction l with
  | zero => intro l' h; simp [VLevel.ofLevel] at h; subst h; simp [VLevel.ofLevel, VLevel.inst]
  | succ l ih =>
    intro l' h
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    rcases h with ⟨a, ha, rfl⟩
    simp [VLevel.ofLevel, ih ha, VLevel.inst]
  | max l₁ l₂ ih₁ ih₂ =>
    intro l' h
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    rcases h with ⟨a, ha, b, hb, rfl⟩
    simp [VLevel.ofLevel, ih₁ ha, ih₂ hb, VLevel.inst]
  | imax l₁ l₂ ih₁ ih₂ =>
    intro l' h
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    rcases h with ⟨a, ha, b, hb, rfl⟩
    simp [VLevel.ofLevel, ih₁ ha, ih₂ hb, VLevel.inst]
  | param n =>
    intro l' h
    simp only [VLevel.ofLevel] at h
    split at h
    · rename_i hi
      cases h
      have hlen := Lean4Lean.List.Forall₂.length_eq hfor
      simp only [List.length_map] at hlen
      have hget := Lean4Lean.List.Forall₂.getElem_of hfor (Us₀.idxOf n)
        (by simpa using hi) (by omega)
      simp only [List.getElem_map, List.getElem_idxOf] at hget
      simp only [VLevel.inst, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show Us₀.idxOf n < ls.length by omega),
        Option.getD_some]
      exact hget
    · cases h
  | mvar => intro l' h; simp [VLevel.ofLevel] at h

theorem VLevel.mapM_ofLevel_reindex {Us₀ Us : List Name} {ls : List VLevel}
    (hls : (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some ls) :
    ∀ {us : List Level} {us' : List VLevel}, us.mapM (VLevel.ofLevel Us₀) = some us' →
      us.mapM (VLevel.ofLevel Us) = some (us'.map (VLevel.inst ls))
  | [], us', h => by simp at h; subst h; rfl
  | u :: us, us', h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    rcases h with ⟨a, ha, b, hb, rfl⟩
    simp [VLevel.ofLevel_reindex hls ha, VLevel.mapM_ofLevel_reindex hls hb]

/-! ### Substitution under binders -/

theorem VExpr.subst_liftN_liftN (σ : VExpr.Subst) (x : VExpr) (m k : Nat) :
    (x.liftN m).subst (σ.liftN (k + m)) = (x.subst (σ.liftN k)).liftN m := by
  rw [VExpr.liftN_subst, ← VExpr.lift'_consN_skipN, VExpr.lift'_subst]
  congr 1
  funext j
  simp only [VExpr.Subst.lift_l, VExpr.Subst.lift_r, Lift.liftVar_consN_skipN,
    liftVar_base', VExpr.lift'_consN_skipN, VExpr.Subst.liftN_apply]
  by_cases hj : j < k
  · rw [if_pos (by omega), if_pos hj]
    simp [VExpr.liftN, liftVar_base']
  · rw [if_neg (by omega), if_neg hj, VExpr.liftN_liftN]
    congr 2
    omega

namespace VerifyInductive

/-- The abstract image of a source translation under the parameter
substitution at binder depth `k`, after universe reindexing. -/
def instRevTarget (ls : List VLevel) (params : List VExpr) (k : Nat) (e : VExpr) : VExpr :=
  (e.instL ls).subst ((VExpr.Subst.ofList params).liftN k)

theorem instRevTarget_liftN (ls : List VLevel) (params : List VExpr) (k m : Nat)
    (e : VExpr) :
    instRevTarget ls params (k + m) (e.liftN m) =
      (instRevTarget ls params k e).liftN m := by
  simp only [instRevTarget, VExpr.instL_liftN]
  exact VExpr.subst_liftN_liftN _ _ m k

/-- Correspondence between the source context of an abstracted body (the
parameter telescope as bound variables, below `dk` further source binders)
and the target context of its instantiation (an arbitrary context `Δ` below
the corresponding target binders). Let values correspond by
`instRevTarget`; binder types are irrelevant to translation. -/
inductive InstRevCtx (Δ : VLCtx) (n : Nat) (ls : List VLevel) (params : List VExpr) :
    VLCtx → VLCtx → Nat → Nat → Prop
  | base {domains : List VExpr} : domains.length = n →
      InstRevCtx Δ n ls params (abstractForallContext domains []) Δ 0 0
  | lam {Δs Δt : VLCtx} {dk k : Nat} (A B : VExpr) :
      InstRevCtx Δ n ls params Δs Δt dk k →
      InstRevCtx Δ n ls params ((none, .vlam A) :: Δs) ((none, .vlam B) :: Δt)
        (dk + 1) (k + 1)
  | letE {Δs Δt : VLCtx} {dk k : Nat} (A B v : VExpr) :
      InstRevCtx Δ n ls params Δs Δt dk k →
      InstRevCtx Δ n ls params ((none, .vlet A v) :: Δs)
        ((none, .vlet B (instRevTarget ls params k v)) :: Δt) (dk + 1) k

private theorem lamEntries_find_inl :
    ∀ (L : List VExpr) {i : Nat} {e A : VExpr},
      VLCtx.find? (L.map fun t => ((none : Option (FVarId × List FVarId)),
        VLocalDecl.vlam t)) (.inl i) = some (e, A) →
      i < L.length ∧ e = .bvar i
  | [], _, _, _, h => by simp [VLCtx.find?] at h
  | t :: L, i, e, A, h => by
    cases i with
    | zero =>
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value] at h
      exact ⟨by simp, h.1.symm⟩
    | succ i =>
      simp only [List.map_cons, VLCtx.find?, VLCtx.next] at h
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨e', A'⟩, hf, he, _⟩
      rcases lamEntries_find_inl L hf with ⟨hi, rfl⟩
      subst he
      exact ⟨by simpa using hi, by simp [VExpr.liftN, VLocalDecl.depth]⟩

private theorem lamEntries_find_inr :
    ∀ (L : List VExpr) (fv : FVarId),
      VLCtx.find? (L.map fun t => ((none : Option (FVarId × List FVarId)),
        VLocalDecl.vlam t)) (.inr fv) = none
  | [], _ => rfl
  | t :: L, fv => by
    simp [VLCtx.find?, VLCtx.next, lamEntries_find_inr L fv]

theorem InstRevCtx.find_inr (W : InstRevCtx Δ n ls params Δs Δt dk k) (fv : FVarId) :
    Δs.find? (.inr fv) = none := by
  induction W with
  | base =>
    simp only [abstractForallContext, List.append_nil]
    exact lamEntries_find_inr _ fv
  | lam _ _ _ ih => simp [VLCtx.find?, VLCtx.next, ih]
  | letE _ _ _ _ ih => simp [VLCtx.find?, VLCtx.next, ih]

theorem InstRevCtx.find_inl (W : InstRevCtx Δ n ls params Δs Δt dk k)
    {i : Nat} {e A : VExpr} (h : Δs.find? (.inl i) = some (e, A)) :
    (i < dk ∧ ∃ B, Δt.find? (.inl i) = some (instRevTarget ls params k e, B)) ∨
      (dk ≤ i ∧ i - dk < n ∧ e = .bvar (i - dk + k)) := by
  induction W generalizing i e A with
  | @base domains hlen =>
    simp only [abstractForallContext, List.append_nil] at h
    rcases lamEntries_find_inl _ h with ⟨hi, rfl⟩
    right
    simp at hi
    exact ⟨Nat.zero_le _, by omega, by simp⟩
  | @lam Δs Δt dk k A' B' W ih =>
    cases i with
    | zero =>
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value] at h
      left
      refine ⟨by omega, (VLocalDecl.vlam B').type, ?_⟩
      rw [← h.1]
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, instRevTarget,
        VExpr.instL, VExpr.Subst.liftN_apply]
    | succ i =>
      simp only [VLCtx.find?, VLCtx.next] at h
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨e', A''⟩, hf, he, _⟩
      subst he
      rcases ih hf with ⟨hi, B, hB⟩ | ⟨hi, hn, rfl⟩
      · left
        refine ⟨by omega, B.liftN 1, ?_⟩
        simp only [VLCtx.find?, VLCtx.next, hB, bind, Option.bind_some,
          VLocalDecl.depth]
        rw [instRevTarget_liftN]
      · right
        refine ⟨by omega, by omega, ?_⟩
        simp [VExpr.liftN, VLocalDecl.depth]
        omega
  | @letE Δs Δt dk k A' B' v W ih =>
    cases i with
    | zero =>
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value] at h
      left
      refine ⟨by omega, (VLocalDecl.vlet B' (instRevTarget ls params k v)).type, ?_⟩
      rw [← h.1]
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value]
    | succ i =>
      simp only [VLCtx.find?, VLCtx.next] at h
      simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨e', A''⟩, hf, he, _⟩
      subst he
      simp only [VLocalDecl.depth, VExpr.liftN_zero]
      rcases ih hf with ⟨hi, B, hB⟩ | ⟨hi, hn, rfl⟩
      · left
        refine ⟨by omega, B, ?_⟩
        simp [VLCtx.find?, VLCtx.next, hB, VLocalDecl.depth]
      · right
        exact ⟨by omega, by omega, by congr 1; omega⟩

theorem InstRevCtx.bvLift (W : InstRevCtx Δ n ls params Δs Δt dk k) :
    VLCtx.BVLift Δ Δt dk 0 k 0 := by
  induction W with
  | base => exact .refl
  | lam _ B _ ih => exact .skip (.vlam B) ih
  | letE _ B v _ ih => exact .skip (.vlet B _) ih

/-! ### Inverting translation of an instantiation -/

theorem instantiateRevList_bvar_fvars {As : List Expr}
    (hAs : ∀ a ∈ As, ∃ fv, a = .fvar fv) (i dk : Nat) :
    (Expr.bvar i).instantiateRevList As dk =
      if i < dk then .bvar i
      else if h : i - dk < As.length then As[As.length - 1 - (i - dk)]
      else .bvar (i - As.length) := by
  induction As with
  | nil =>
    simp only [Expr.instantiateRevList, List.length_nil, Nat.not_lt_zero, dite_false,
      Nat.sub_zero]
    split <;> rfl
  | cons a as ih =>
    have hih := ih (fun b hb => hAs b (by simp [hb]))
    rcases hAs a (by simp) with ⟨fa, rfl⟩
    simp only [Expr.instantiateRevList, hih]
    by_cases hi : i < dk
    · simp [hi, Expr.instantiate1']
    · simp only [hi, if_false]
      by_cases hlt : i - dk < as.length
      · rw [dif_pos hlt, dif_pos (by simp; omega)]
        rcases hAs as[as.length - 1 - (i - dk)] (by simp) with ⟨fv, hfv⟩
        rw [hfv]
        simp only [Expr.instantiate1', List.length_cons]
        rw [List.getElem_cons, dif_neg (by omega)]
        rw [← hfv]
        congr 1
        omega
      · rw [dif_neg hlt]
        by_cases heq : i - dk = as.length
        · rw [dif_pos (by simp; omega)]
          simp only [Expr.instantiate1', List.length_cons]
          rw [if_neg (by omega), if_pos (by omega)]
          simp [heq, Expr.liftLooseBVars']
        · rw [dif_neg (by simp; omega)]
          simp only [Expr.instantiate1', List.length_cons]
          rw [if_neg (by omega), if_neg (by omega)]
          congr 1

theorem instantiateRevList_closed {e : Expr} (h : e.looseBVarRange' = 0) (As : List Expr)
    (dk : Nat) : e.instantiateRevList As dk = e :=
  Expr.instantiateRevList'_eq_self (by omega)

/-- **Inversion of translation through instantiation at free variables.**
If the abstracted body `e` translates to `e₁` in a source context whose
bottom is the parameter telescope (as bound variables, universe parameters
`Us₀`), then every translation of `e` instantiated at the free variables
`As` (translating to `params` in `Δ`, universe parameters `Us`) is the
parameter substitution of `e₁`, reindexed along `Us₀ ↦ Us`. No typing or
environment relation is required: translation is syntactically determined. -/
theorem TrExprS.instantiateRevList_inv {env₁ env₂ : VEnv} {Us₀ Us : List Name}
    {ls : List VLevel}
    (hls : (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some ls)
    {As : List Expr} {params : List VExpr} {Δ : VLCtx}
    (hAs : ∀ a ∈ As, ∃ fv, a = .fvar fv)
    (hTr : List.Forall₂ (TrExprS env₂ Us Δ) As params)
    {Δs : VLCtx} {e : Expr} {e₁ : VExpr}
    (H₁ : TrExprS env₁ Us₀ Δs e e₁) :
    ∀ {Δt : VLCtx} {dk k : Nat} {v : VExpr},
      InstRevCtx Δ As.length ls params Δs Δt dk k →
      TrExprS env₂ Us Δt (e.instantiateRevList As dk) v →
      v = instRevTarget ls params k e₁ := by
  have hlen := Lean4Lean.List.Forall₂.length_eq hTr
  induction H₁ with
  | @bvar _ _ _ i h1 =>
    intro Δt dk k v W H
    rw [instantiateRevList_bvar_fvars hAs] at H
    rcases W.find_inl h1 with ⟨hi, B, hB⟩ | ⟨hi, hn, rfl⟩
    · rw [if_pos hi] at H
      cases H with
      | bvar h => rw [hB] at h; cases h; rfl
    · rw [if_neg (by omega), dif_pos hn] at H
      have hj : As.length - 1 - (i - dk) < As.length := by omega
      have hjp : As.length - 1 - (i - dk) < params.length := by omega
      have hTrj := Lean4Lean.List.Forall₂.getElem_of hTr _ hj hjp
      rcases hAs _ (List.getElem_mem hj) with ⟨fv, hfv⟩
      rw [hfv] at H hTrj
      cases hTrj with
      | fvar hf =>
        have hf' := W.bvLift.find? hf
        simp only [VLCtx.liftVar] at hf'
        cases H with
        | fvar h =>
          rw [hf'] at h
          cases h
          simp only [instRevTarget, VExpr.instL, VExpr.subst, VExpr.Subst.liftN_apply]
          rw [if_neg (by omega), Nat.add_sub_cancel,
            VExpr.Subst.ofList_lt _ (by omega)]
          congr 2
          omega
  | fvar h1 =>
    intro Δt dk k v W H
    rw [W.find_inr] at h1
    cases h1
  | sort h1 =>
    intro Δt dk k v W H
    rw [instantiateRevList_closed rfl] at H
    cases H with
    | sort h =>
      rw [VLevel.ofLevel_reindex hls h1] at h
      cases h
      rfl
  | const h1 h2 h3 =>
    intro Δt dk k v W H
    rw [instantiateRevList_closed rfl] at H
    cases H with
    | const _ h _ =>
      rw [VLevel.mapM_ofLevel_reindex hls h2] at h
      cases h
      rfl
  | app _ _ _ _ ih1 ih2 =>
    intro Δt dk k v W H
    rw [Expr.instantiateRevList_app] at H
    cases H with
    | app _ _ hf ha =>
      rw [ih1 W hf, ih2 W ha]
      rfl
  | lam _ _ _ ih1 ih2 =>
    intro Δt dk k v W H
    rw [Expr.instantiateRevList_lam] at H
    cases H with
    | lam _ hty hbody =>
      have e1 := ih1 W hty
      subst e1
      rw [ih2 (W.lam _ _) hbody]
      rfl
  | forallE _ _ _ _ ih1 ih2 =>
    intro Δt dk k v W H
    rw [Expr.instantiateRevList_forallE] at H
    cases H with
    | forallE _ _ hty hbody =>
      have e1 := ih1 W hty
      subst e1
      rw [ih2 (W.lam _ _) hbody]
      rfl
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro Δt dk k v W H
    rw [Expr.instantiateRevList_letE] at H
    cases H with
    | letE _ hty hval hbody =>
      have e1 := ih1 W hty
      have e2 := ih2 W hval
      subst e1 e2
      exact ih3 (W.letE _ _ _) hbody
  | lit _ _ ih =>
    intro Δt dk k v W H
    rw [instantiateRevList_closed rfl] at H
    cases H with
    | lit _ h =>
      apply ih W
      rw [Expr.instantiateRevList'_eq_self Closed.toConstructor.looseBVarRange_le]
      exact h
  | mdata _ ih =>
    intro Δt dk k v W H
    rw [Expr.instantiateRevList_mdata] at H
    cases H with
    | mdata h => exact ih W h
  | proj _ hp ih =>
    intro Δt dk k v W H
    rw [Expr.instantiateRevList_proj] at H
    cases H with
    | proj h hp' =>
      rw [ih W h]
      rfl

theorem instantiateRevList_mkAppList (As : List Expr) (dk : Nat) :
    ∀ (Ys : List Expr) (f : Expr),
      (Expr.mkAppList f Ys).instantiateRevList As dk =
        Expr.mkAppList (f.instantiateRevList As dk)
          (Ys.map (·.instantiateRevList As dk))
  | [], f => by simp
  | y :: Ys, f => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [instantiateRevList_mkAppList As dk Ys (.app f y),
      Expr.instantiateRevList_app]

/-! ### Container applications recorded by lowering -/

private theorem forall₂_instantiate_inv {envS env : VEnv} {Us₀ Us : List Name}
    {ls : List VLevel}
    (hls : (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some ls)
    {As : List Expr} {params : List VExpr} {Δ : VLCtx}
    (hAs : ∀ a ∈ As, ∃ fv, a = .fvar fv)
    (hTr : List.Forall₂ (TrExprS env Us Δ) As params)
    {domains : List VExpr} (hdomains : domains.length = As.length) :
    ∀ {Ys : List Expr} {args vs : List VExpr},
      List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys args →
      List.Forall₂ (TrExprS env Us Δ) (Ys.map (·.instantiateRevList As 0)) vs →
      vs = args.map fun arg => InductiveSignature.instantiateParams (arg.instL ls) params
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨TrExprS.instantiateRevList_inv hls hAs hTr h₁ (.base hdomains) h₂,
      forall₂_instantiate_inv hls hAs hTr hdomains t₁ t₂⟩

/-- The translation of a reopened container application, possibly with its
head renamed (a constructor), is the abstract specialisation. -/
theorem AuxiliaryContainerApp.reopenedTranslation {result : Lean4Lean.ElimNestedInductive.Result}
    {Us₀ Us : List Name} {a : InductiveSignature.ContainerSpecialization}
    {envS : VEnv} {domains : List VExpr} {lvls : List Level} {Ys : List Expr}
    (hdomains : domains.length = result.nparams)
    (hlvls : lvls.mapM (VLevel.ofLevel Us₀) = some a.levels)
    (hYs : List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys
      a.arguments)
    {levels : List VLevel}
    (hlevels : (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some levels)
    {targetEnv : VEnv} {Δ : VLCtx} {As : Array Expr} {params : List VExpr}
    (hAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    (hTr : List.Forall₂ (TrExprS targetEnv Us Δ) As.toList params)
    (target : Name) {v : VExpr}
    (H : TrExprS targetEnv Us Δ
      (Expr.mkAppList (.const target lvls) (Ys.map (·.instantiateRevList As.toList 0))) v) :
    v = VExpr.mkApps (.const target (a.levels.map (·.inst levels)))
      (a.arguments.map fun arg =>
        InductiveSignature.instantiateParams (arg.instL levels) params) := by
  rcases checkPositivityStep.TrExprS.mkAppList_inv H with ⟨fn', args', hfn, hargs, rfl⟩
  cases hfn with
  | const _ hl _ =>
    rw [VLevel.mapM_ofLevel_reindex hlevels hlvls] at hl
    cases hl
    rw [forall₂_instantiate_inv hlevels hAs hTr
      (by rw [hdomains, Array.length_toList, hsize]) hYs hargs]

theorem abstractN_getAppFn_const {xs : List FVarId} {name : Name} {lvls : List Level} :
    ∀ (e : Expr) (k : Nat), (Expr.abstractN xs e k).getAppFn = .const name lvls →
      e.getAppFn = .const name lvls
  | .bvar _, _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .fvar v, k, h => by
    simp only [Expr.abstractN] at h
    split at h <;> simp [Expr.getAppFn] at h
  | .mdata _ _, _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .proj _ _ _, _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .app f _, k, h => by
    simp only [Expr.abstractN, Expr.getAppFn] at h ⊢
    exact abstractN_getAppFn_const f k h
  | .lam .., _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .forallE .., _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .letE .., _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .const _ _, _, h => by simpa [Expr.abstractN, Expr.getAppFn] using h
  | .sort _, _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .mvar _, _, h => by simp [Expr.abstractN, Expr.getAppFn] at h
  | .lit _, _, h => by simp [Expr.abstractN, Expr.getAppFn] at h

theorem AuxiliaryContainerApp.reopen {result : Lean4Lean.ElimNestedInductive.Result}
    {nested : Expr} {name : Name} {lvls : List Level} {Ys : List Expr}
    (h : nested.abstract result.params = Expr.mkAppList (.const name lvls) Ys)
    (As : Array Expr) :
    (nested.abstract result.params).instantiateRev As =
      Expr.mkAppList (.const name lvls) (Ys.map (·.instantiateRevList As.toList 0)) := by
  rw [h, Expr.instantiateRev_eq_instantiateList, Expr.instantiateList_reverse,
    instantiateRevList_mkAppList,
    instantiateRevList_closed rfl]

theorem getNestedIfAuxCtor_eq_some {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {c : Name} {nested : Expr} {auxI : Name}
    (h : result.getNestedIfAuxCtor env c = some (nested, auxI)) :
    ∃ info, env.find? c = some (.ctorInfo info) ∧
      result.aux2nested.find? info.induct = some nested ∧ auxI = info.induct := by
  unfold Lean4Lean.ElimNestedInductive.Result.getNestedIfAuxCtor at h
  cases hc : env.find? c with
  | none => simp [hc] at h
  | some ci =>
    cases ci with
    | ctorInfo info =>
      cases hn : result.aux2nested.find? info.induct with
      | none => simp [hc, hn] at h
      | some n =>
        simp [hc, hn] at h
        exact ⟨info, rfl, by rw [← h.1, hn], h.2.symm⟩
    | _ => simp [hc] at h

theorem getNestedIfAuxCtor_of {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {c : Name} {nested : Expr} {info : ConstructorVal}
    (hc : env.find? c = some (.ctorInfo info))
    (hn : result.aux2nested.find? info.induct = some nested) :
    result.getNestedIfAuxCtor env c = some (nested, info.induct) := by
  unfold Lean4Lean.ElimNestedInductive.Result.getNestedIfAuxCtor
  simp [hc, hn]

open _root_.Lean4Lean.InductiveSignature (compilationRestoration compilationRestoration_heads_auxiliary
  compilationRestoration_restoredHeadName_constructor) in
/-- **The executable restoration tables agree with `compilationRestoration`**
for every target environment and universe-parameter list, at the lowered
universe arguments `Us₀.map .param`. -/
theorem RestorationTablesAgree.agreement {decl : VInductDecl}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    (targetEnv : VEnv) (Us : List Name) :
    RestorationMapAgreement (compilationRestoration decl auxiliaries) result env auxRec
      targetEnv Us (Us₀.map Level.param) := by
  have hheadsNodup :
      ((compilationRestoration decl auxiliaries).heads.map (·.auxiliary)).Nodup := by
    rw [compilationRestoration_heads_auxiliary]
    exact D.headNodup
  have hlevelsLength : ∀ levels : List VLevel,
      (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some levels →
      decl.uvars = levels.length := by
    intro levels h
    have := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 h)
    simp only [List.length_map] at this
    rw [D.uvars, this]
  have hrename : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      (a.constructorName ctor).replacePrefix a.auxiliary a.source.name = ctor.name :=
    fun a ha ctor hctor =>
      (namePrefix_of_replacePrefix_ne (D.ctorRenamed a ha ctor hctor)).replacePrefix_replacePrefix _
  refine {
    recursorName := D.recursorName
    recursorNotHead := ?_
    headNone := ?_
    head := ?_
    ctorTarget := ?_ }
  · intro c new h hmem
    rw [compilationRestoration_heads_auxiliary] at hmem
    exact D.recursorNotHead c new h hmem
  · intro As c hnone hmem
    rw [compilationRestoration_heads_auxiliary] at hmem
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hmem
    simp only [InductiveSignature.ContainerSpecialization.headNames, List.mem_cons,
      List.mem_map] at hc
    unfold restoreHead at hnone
    rcases hc with rfl | ⟨ctor, hctor, rfl⟩
    · obtain ⟨nested, hn⟩ := D.familyLookup a ha
      rw [hn] at hnone
      cases hnone
    · cases hfind : result.aux2nested.find? (a.constructorName ctor) with
      | some _ => rw [hfind] at hnone; cases hnone
      | none =>
        rw [hfind] at hnone
        obtain ⟨info, hc, hind⟩ := D.ctorInstalled a ha ctor hctor
        obtain ⟨nested, hn⟩ := D.familyLookup a ha
        rw [← hind] at hn
        rw [getNestedIfAuxCtor_of hc hn] at hnone
        obtain ⟨_, _, _, _, _, _, _, _, hab, _⟩ := D.familyKey _ nested hn
        simp only [AuxiliaryContainerApp.reopen hab, Expr.getAppFn_mkAppList_const] at hnone
        cases hnone
  · intro As c H hH
    unfold restoreHead at hH
    cases hfind : result.aux2nested.find? c with
    | some nested =>
      rw [hfind] at hH
      cases hH
      obtain ⟨a, ha, rfl, envS, domains, lvls, Ys, hdom, hab, hlvls, hYs⟩ :=
        D.familyKey _ nested hfind
      have hmem : InductiveSignature.HeadSpecialization.mk a.auxiliary decl.uvars
          decl.nparams a.source.name a.levels a.arguments ∈
          (compilationRestoration decl auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
      refine ⟨_, InductiveSignature.Restoration.find?_of_nodup hheadsNodup hmem, D.nparams,
        fun levels hlevels => ⟨hlevelsLength levels hlevels, ?_⟩⟩
      intro Δ params v hAs hsize hTr hv
      rw [AuxiliaryContainerApp.reopen hab] at hv
      exact AuxiliaryContainerApp.reopenedTranslation hdom hlvls hYs hlevels hAs hsize hTr _ hv
    | none =>
      rw [hfind] at hH
      cases hget : result.getNestedIfAuxCtor env c with
      | none => rw [hget] at hH; cases hH
      | some pair =>
        obtain ⟨nested, auxI⟩ := pair
        rw [hget] at hH
        obtain ⟨info, hc, hn, rfl⟩ := getNestedIfAuxCtor_eq_some hget
        obtain ⟨a, ha, hauxEq, envS, domains, lvls, Ys, hdom, hab, hlvls, hYs⟩ :=
          D.familyKey _ nested hn
        obtain ⟨ctor, hctor, rfl⟩ := D.ctorLookup c info hc a ha hauxEq.symm
        simp only [AuxiliaryContainerApp.reopen hab, Expr.getAppFn_mkAppList_const,
          Option.some.injEq] at hH
        subst hH
        have hmem : InductiveSignature.HeadSpecialization.mk (a.constructorName ctor)
            decl.uvars decl.nparams ctor.name a.levels a.arguments ∈
            (compilationRestoration decl auxiliaries).heads :=
          List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
        refine ⟨_, InductiveSignature.Restoration.find?_of_nodup hheadsNodup hmem, D.nparams,
          fun levels hlevels => ⟨hlevelsLength levels hlevels, ?_⟩⟩
        intro Δ params v hAs hsize hTr hv
        rw [Expr.getAppArgs_eq, Expr.getAppArgsList_mkAppList_const,
          Expr.mkAppN_eq_mkAppList, ← hauxEq, hrename a ha ctor hctor] at hv
        exact AuxiliaryContainerApp.reopenedTranslation hdom hlvls hYs hlevels hAs hsize hTr _
          (by simpa using hv)
  · intro c nested auxI _ hget
    obtain ⟨info, hc, hn, rfl⟩ := getNestedIfAuxCtor_eq_some hget
    obtain ⟨a, ha, hauxEq, envS, domains, lvls, Ys, hdom, hab, hlvls, hYs⟩ :=
      D.familyKey _ nested hn
    obtain ⟨ctor, hctor, rfl⟩ := D.ctorLookup c info hc a ha hauxEq.symm
    refine ⟨a.source.name, lvls, ?_, ?_⟩
    · obtain ⟨xs, hxs⟩ := D.paramsFVars
      rw [hxs, Expr.abstractN_eq] at hab
      exact abstractN_getAppFn_const nested 0
        (by rw [hab, Expr.getAppFn_mkAppList_const])
    · rw [compilationRestoration_restoredHeadName_constructor D.headNodup ha hctor,
        ← hauxEq, hrename a ha ctor hctor]

/-! ### Per-family link data of a lowering run -/

private theorem inductInfo_safety_of_visible' {info : InductiveVal} {isUnsafe : Bool}
    (h : (if isUnsafe then DefinitionSafety.unsafe else .safe) ≤
      (ConstantInfo.inductInfo info).safety) :
    isUnsafe = true ∨ info.isUnsafe = false := by
  cases isUnsafe
  · right
    cases hi : info.isUnsafe
    · rfl
    · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hi] at h
      exact absurd h (by decide)
  · left; rfl

open _root_.Lean4Lean.InductiveSignature in
/-- `AuxiliaryFamilySource.auxiliarySpecialization`, also
recording that the specialisation's universe and parameter arguments are those
of the source data `N` (`N.levels`, `N.baseArgs`). -/
theorem AuxiliaryFamilySource.linkedSpecialization
    {ves : VEnvs} {isUnsafe : Bool} {prodEnv : Environment}
    {params : Array Expr} {nparams : Nat}
    {finalState : Lean4Lean.ElimNestedInductive.State}
    {targetConcrete : InductiveType}
    {H : LoweredAuxiliaryFamily prodEnv params nparams finalState
      targetConcrete}
    {sourceTypesVEnv : VEnv} {lparams : List Name} {target : VInductiveType}
    {baseVEnv : VEnv}
    (N : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (hbase : baseVEnv = ves.venv (if isUnsafe then .unsafe else .safe))
    (wf : ves.WF prodEnv) (decl : VInductDecl)
    (huvars : decl.uvars = lparams.length) (hnparams : decl.nparams = nparams)
    (hunsafe : decl.isUnsafe = isUnsafe)
    (hle : baseVEnv ≤ sourceTypesVEnv) {paramCtx : List VExpr}
    (hctx : VEnv.IsDefEqCtx baseVEnv lparams.length [] N.sourceParams.reverse
      paramCtx) :
    ∃ a : ContainerSpecialization,
      SpecializationGenerates
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceTypesVEnv paramCtx
        decl a N.source ∧
      a.auxiliary = N.source.name ∧ a.source = N.containerFamily ∧
      a.levels = N.levels ∧ a.arguments = N.baseArgs := by
  subst hbase
  rcases List.mem_iff_getElem.mp N.familyMember with ⟨idx, hidx, hfamily⟩
  let a : ContainerSpecialization := {
    container := N.container
    family := ⟨idx, hidx⟩
    auxiliary := N.source.name
    levels := N.levels
    arguments := N.baseArgs }
  have hsource : a.source = N.containerFamily := hfamily
  have habstract : (ves.venv (if isUnsafe then .unsafe else .safe)).constants
      H.generated.sourceName = some N.container.types[idx].toVConstant := by
    rw [← N.containerName, ← hfamily]
    exact N.installedBase.familyConstant idx hidx
  have htrConst := ((wf.tr (safety := if isUnsafe then .unsafe else .safe)).find?_uniq
    H.generated.built.lookup habstract).2
  have hvisible := htrConst.1
  have hfamilyPrefix : HasForallPrefix a.source.type a.arguments.length := by
    rcases H.generated.built.opening with ⟨_, Htelescope, _⟩
    rcases Htelescope.reflect_instantiateLevelParams with ⟨_, Hsource, _⟩
    have Hshape := TrExprS.targetArityOfForallTelescope htrConst.2.2 Hsource
    have hlength : a.arguments.length = H.generated.nestedNParams := by
      have h := Lean4Lean.List.Forall₂.length_eq N.baseTranslations
      simp only [List.length_map, List.length_take, Array.length_toList] at h
      change N.baseArgs.length = _
      rw [← h]
      exact Nat.min_eq_left H.generated.argsArity
    rw [hlength, hsource, ← hfamily]
    exact sameTelescopeArity_hasForallPrefix Hshape
  have hsafety : decl.isUnsafe = true ∨ N.container.isUnsafe = false := by
    rw [hunsafe, ← N.containerUnsafe]
    exact inductInfo_safety_of_visible' hvisible
  refine ⟨a, ?_, rfl, hsource, rfl, rfl⟩
  refine {
    installed := N.installedBase
    auxiliary := rfl
    generatedUvars := N.sourceUvars.trans huvars.symm
    argumentsLength := N.baseArgsLength
    argumentsClosed := ?_
    levelsLength := N.levelsLength
    levelsWF := by rw [huvars]; exact N.levelsWF
    safety := hsafety
    familyForallPrefix := hfamilyPrefix
    application := ?_
    constructorShapes := ?_ }
  · intro arg harg
    rw [hnparams, ← N.sourceParamsLength]
    exact N.baseArgsClosed arg harg
  · refine ⟨N.sourceParams, N.sourceParamsLength.trans hnparams.symm,
      by rw [huvars]; exact VEnv.IsDefEqCtx.mono hle hctx,
      by rw [huvars]; exact N.sourceParamsWF, ?_, ?_, ?_⟩
    · rw [hsource, huvars]
      simpa only [abstractForallContext_toCtx, VLCtx.toCtx, List.append_nil]
        using N.familyApplicationTyping
    · rw [hsource, huvars]
      exact N.familyType
    · rw [hsource, huvars]
      exact N.constructors
  · refine ⟨N.sourceParams, N.sourceParamsLength.trans hnparams.symm, ?_⟩
    rw [hsource, huvars]
    exact N.constructorShapes

/-- The container application recorded for a generated family, abstracted
over the final lowering parameters, is the container application of its source
data. -/
theorem AuxiliaryFamilySource.auxiliaryContainerApp
    {prodEnv : Environment} {result : Lean4Lean.ElimNestedInductive.Result}
    {nparams : Nat} {finalState : Lean4Lean.ElimNestedInductive.State}
    {targetConcrete : InductiveType}
    {H : LoweredAuxiliaryFamily prodEnv result.params nparams finalState
      targetConcrete}
    {baseVEnv sourceTypesVEnv : VEnv} {lparams : List Name} {target : VInductiveType}
    (N : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (a : InductiveSignature.ContainerSpecialization)
    (hsrcName : a.source.name = H.generated.sourceName)
    (hlevels : a.levels = N.levels) (hargs : a.arguments = N.baseArgs)
    {fvars : List FVarId} (hfvars : result.params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup) (sel : CDeclArray result.lctx result.params)
    (hclosed : H.generated.data.nested.looseBVarRange' = 0)
    (hnp : result.nparams = nparams) :
    AuxiliaryContainerApp result lparams H.generated.data.nested a := by
  have hsel : sel.fvars = fvars := by
    have h : (sel.fvars.map Expr.fvar).toArray = (fvars.map Expr.fvar).toArray :=
      sel.expressions.symm.trans hfvars
    have h' := congrArg Array.toList h
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp (by simpa using h')
  refine ⟨sourceTypesVEnv, N.sourceParams, H.generated.levels,
    (H.generated.args.toList.take H.generated.nestedNParams).map
      (·.abstractList H.generated.selection.fvars), ?_, ?_, ?_, ?_⟩
  · rw [N.sourceParamsLength, hnp]
  · have habs : H.generated.data.nested.abstract result.params =
        H.generated.data.nested.abstractList fvars :=
      (congrArg H.generated.data.nested.abstract hfvars).trans
        (Expr.abstract_eq_of_closed _ fvars hnodup hclosed)
    rw [habs, ← hsel, H.generated.cachedClosureAlpha sel (hsel ▸ hnodup),
      Expr.mkAppRange_from_zero _ _ _ H.generated.argsArity,
      Expr.abstractList_mkAppList, Expr.abstractList_const, hsrcName]
  · rw [hlevels]; exact N.levelsTranslation
  · rw [hargs]; exact N.baseTranslations

/-- `AuxiliaryFamilySource.auxiliaryContainerApp` in the source
header environment, with the source-data parameters definitionally equal to
a given context. -/
theorem AuxiliaryFamilySource.auxiliaryContainerAppAt
    {prodEnv : Environment} {result : Lean4Lean.ElimNestedInductive.Result}
    {nparams : Nat} {finalState : Lean4Lean.ElimNestedInductive.State}
    {targetConcrete : InductiveType}
    {H : LoweredAuxiliaryFamily prodEnv result.params nparams finalState
      targetConcrete}
    {baseVEnv sourceTypesVEnv : VEnv} {lparams : List Name} {target : VInductiveType}
    (N : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (a : InductiveSignature.ContainerSpecialization)
    (hsrcName : a.source.name = H.generated.sourceName)
    (hlevels : a.levels = N.levels) (hargs : a.arguments = N.baseArgs)
    {fvars : List FVarId} (hfvars : result.params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup) (sel : CDeclArray result.lctx result.params)
    (hclosed : H.generated.data.nested.looseBVarRange' = 0)
    (hnp : result.nparams = nparams) {ctx : List VExpr}
    (hctx : VEnv.IsDefEqCtx sourceTypesVEnv lparams.length [] N.sourceParams.reverse ctx) :
    AuxiliaryContainerAppAt sourceTypesVEnv ctx result lparams H.generated.data.nested a := by
  have hsel : sel.fvars = fvars := by
    have h : (sel.fvars.map Expr.fvar).toArray = (fvars.map Expr.fvar).toArray :=
      sel.expressions.symm.trans hfvars
    have h' := congrArg Array.toList h
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp (by simpa using h')
  refine ⟨N.sourceParams, H.generated.levels,
    (H.generated.args.toList.take H.generated.nestedNParams).map
      (·.abstractList H.generated.selection.fvars), ?_, hctx, ?_, ?_, ?_⟩
  · rw [N.sourceParamsLength, hnp]
  · have habs : H.generated.data.nested.abstract result.params =
        H.generated.data.nested.abstractList fvars :=
      (congrArg H.generated.data.nested.abstract hfvars).trans
        (Expr.abstract_eq_of_closed _ fvars hnodup hclosed)
    rw [habs, ← hsel, H.generated.cachedClosureAlpha sel (hsel ▸ hnodup),
      Expr.mkAppRange_from_zero _ _ _ H.generated.argsArity,
      Expr.abstractList_mkAppList, Expr.abstractList_const, hsrcName]
  · rw [hlevels]; exact N.levelsTranslation
  · rw [hargs]; exact N.baseTranslations

/-! ### Restoring leaves of a lowering run

The container application recorded for an auxiliary is unique, so the
specialisation of the restoration table named by a replaced node is the one
the node was replaced from. -/

/-- Translation is syntactically independent of the environment and of the
types in the local context. -/
theorem TrExprS.uniqueCtxEnv {env₁ env₂ : VEnv} {Us : List Name} {Δ₁ Δ₂ : VLCtx}
    {e : Lean.Expr} {e₁ e₂ : VExpr} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H1 : TrExprS env₁ Us Δ₁ e e₁) (H2 : TrExprS env₂ Us Δ₂ e e₂) : e₁ = e₂ := by
  induction H1 generalizing Δ₂ e₂ with cases H2
  | bvar => exact hΔ.find?_uniq ‹_› ‹_›
  | fvar => exact hΔ.find?_uniq ‹_› ‹_›
  | sort h1
  | const _ h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 hΔ ‹_›; rfl
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlam) ‹_›; rfl
  | letE _ _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlet) ‹_›; rfl
  | lit _ _ ih => exact ih hΔ ‹_›
  | mdata _ ih => exact ih hΔ ‹_›
  | proj _ _ ih => cases ih hΔ ‹_›; rfl

private theorem forall₂_trExprS_uniqueCtxEnv {env₁ env₂ : VEnv} {Us : List Name}
    {Δ₁ Δ₂ : VLCtx} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂) :
    ∀ {es : List Lean.Expr} {xs ys : List VExpr},
      List.Forall₂ (TrExprS env₁ Us Δ₁) es xs →
      List.Forall₂ (TrExprS env₂ Us Δ₂) es ys → xs = ys
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [TrExprS.uniqueCtxEnv hΔ h₁ h₂, forall₂_trExprS_uniqueCtxEnv hΔ t₁ t₂]

/-- Two specialisations recorded for the same container application agree on
their head, universe arguments and parameter arguments. -/
theorem AuxiliaryContainerApp.unique {result : Lean4Lean.ElimNestedInductive.Result}
    {Us₀ : List Name} {nested : Expr} {a b : InductiveSignature.ContainerSpecialization}
    (ha : AuxiliaryContainerApp result Us₀ nested a) (hb : AuxiliaryContainerApp result Us₀ nested b) :
    a.source.name = b.source.name ∧ a.levels = b.levels ∧ a.arguments = b.arguments := by
  obtain ⟨_, domA, lvlA, YsA, hdA, habA, hlA, hYA⟩ := ha
  obtain ⟨_, domB, lvlB, YsB, hdB, habB, hlB, hYB⟩ := hb
  have heq := habA.symm.trans habB
  have hfn := congrArg Expr.getAppFn heq
  have hargs := congrArg Expr.getAppArgsList heq
  rw [Expr.getAppFn_mkAppList_const, Expr.getAppFn_mkAppList_const] at hfn
  rw [Expr.getAppArgsList_mkAppList_const, Expr.getAppArgsList_mkAppList_const] at hargs
  injection hfn with hname hlvl
  subst hlvl hargs
  refine ⟨hname, Option.some.inj (hlA.symm.trans hlB), ?_⟩
  exact forall₂_trExprS_uniqueCtxEnv
    (abstractForallContext.isUniqueCtx (hdA.trans hdB.symm)) hYA hYB

private theorem nestedExprExpansion_false_eq :
    ∀ {depth : Nat} {source target : VExpr},
      VExpr.NestedExprExpansion (fun _ _ _ => False) depth source target →
        source = target := by
  intro depth source target H
  induction H with
  | occurrence h => exact h.elim
  | bvar | sort | const | elim => rfl
  | proj _ ih => rw [ih]
  | app _ _ ihf iha => rw [ihf, iha]
  | lam _ _ ihd ihb | forallE _ _ ihd ihb => rw [ihd, ihb]

private theorem forall₂_nestedExprExpansion_false_eq :
    ∀ {depth : Nat} {xs ys : List VExpr},
      List.Forall₂ (VExpr.NestedExprExpansion (fun _ _ _ => False) depth) xs ys →
        xs = ys
  | _, [], [], .nil => rfl
  | _, _ :: _, _ :: _, .cons h t => by
    rw [nestedExprExpansion_false_eq h, forall₂_nestedExprExpansion_false_eq t]

theorem VExpr.levelWF_mkApps {U : Nat} :
    ∀ {fn : VExpr} {args : List VExpr}, (VExpr.mkApps fn args).LevelWF U ↔
      fn.LevelWF U ∧ ∀ arg ∈ args, arg.LevelWF U
  | fn, [] => by simp [VExpr.mkApps]
  | fn, arg :: args => by
    rw [show VExpr.mkApps fn (arg :: args) = VExpr.mkApps (.app fn arg) args from rfl,
      VExpr.levelWF_mkApps]
    simp [VExpr.LevelWF, and_assoc]

/-- The specialisation arguments of an auxiliary with `SpecializationGenerates` use only the
declaration's universe parameters. -/
theorem SpecializationGenerates.argumentsLevelWF
    {sourceEnv envTypes : VEnv} {paramCtx : List VExpr} {decl : VInductDecl}
    {a : InductiveSignature.ContainerSpecialization} {generated : VInductiveType}
    (H : SpecializationGenerates sourceEnv envTypes paramCtx decl a generated) :
    ∀ arg ∈ a.arguments, arg.LevelWF decl.uvars := by
  obtain ⟨sourceParams, -, -, hon, htyping, -⟩ := H.application
  exact (VExpr.levelWF_mkApps.mp (htyping.levelWF (OnCtx.levelWF_of_isType hon)).1).2

private theorem restoration_expr_paramVars {r : InductiveSignature.Restoration}
    (decl : VInductDecl) (depth : Nat) :
    List.Forall₂ (fun x y => InductiveSignature.Restoration.expr.go r x [] = some y)
      (decl.paramVars depth) (decl.paramVars depth) := by
  unfold VInductDecl.paramVars
  generalize (List.range decl.nparams).reverse = is
  induction is with
  | nil => exact .nil
  | cons i is ih => exact .cons rfl ih

open _root_.Lean4Lean.InductiveSignature in
/-- **Every nested occurrence replaced by a lowering run is a restoring leaf** for the
restoration table of a specialisation list keyed by the run's `aux2nested`
map (`RestorationTablesAgree.familyKey`). The specialisation keyed by the
auxiliary name is identified with the source data of the occurrence by
`AuxiliaryContainerApp.unique`; the universe arguments of the auxiliary occurrence are
the identity by the `ConstLevelsAt` premise of the leaf. -/
theorem AuxiliaryFamilySources.restoringReplacement
    {isUnsafe : Bool} {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hrun : NestedLowering prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState)}
    (N : AuxiliaryFamilySources Hrun baseVEnv sourceTypesVEnv
      lparams loweredDecl)
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetTypesVEnv targetCtorsVEnv)
    (Henv : EnvironmentTypesClosed prodEnv)
    (hclosures : MutualInductivesClosed prodEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (resultSelection : CDeclArray result.lctx result.params)
    (hresultNodup : resultSelection.fvars.Nodup)
    (hempty : initialState.nestedAux = #[])
    (hnparams : sourceDecl.nparams = nparams)
    {fvars : List FVarId} (hfvars : result.params = (fvars.map Expr.fvar).toArray)
    (hfvarsNodup : fvars.Nodup) (hnp : result.nparams = nparams)
    (hclosedNested : ∀ c nested, result.aux2nested.find? c = some nested →
      nested.looseBVarRange' = 0)
    {auxiliaries : List ContainerSpecialization}
    (hfamilyKey : ∀ c nested, result.aux2nested.find? c = some nested →
      ∃ a ∈ auxiliaries, a.auxiliary = c ∧ AuxiliaryContainerApp result lparams nested a)
    (hheadNodup :
      ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary)).Nodup)
    (hargs : ∀ a ∈ auxiliaries, ∀ arg ∈ a.arguments,
      arg.ClosedN sourceDecl.nparams ∧ arg.LevelWF sourceDecl.uvars)
    (hlevels : ∀ a ∈ auxiliaries, ∀ l ∈ a.levels, l.WF sourceDecl.uvars)
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams
      ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
        (VLevel.params sourceDecl.uvars))) :
    ∀ {lctx : LocalContext} {As : Array Expr}
      {input state output nextState traceFinalState depth fieldDepth sourceValue
        targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx result.params As input state output
        nextState result traceFinalState →
      NestedExpansionLookupCtx
        ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
          (VLevel.params sourceDecl.uvars)) depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = result.params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue →
      TrExprS targetTypesVEnv lparams targetCtx output targetValue →
      (compilationRestoration sourceDecl auxiliaries).RestoringLeaf
        (VLevel.params sourceDecl.uvars) depth sourceValue targetValue := by
  intro lctx As input state output nextState traceFinalState depth fieldDepth
    sourceValue targetValue sourceCtx targetCtx Htrace Hctx selection
    hselectionNodup Harity Hdepth HsourceParams HtargetParams Hscope HsourceExpr
    HtargetExpr
  let r := compilationRestoration sourceDecl auxiliaries
  have hselectionLength : selection.fvars.length = sourceDecl.nparams := by
    calc
      selection.fvars.length = As.size := selection.size.symm
      _ = result.params.size := Harity
      _ = nparams := Hrun.resultParamsSize
      _ = sourceDecl.nparams := hnparams.symm
  have HbaseDepth : sourceDecl.nparams ≤ depth := by
    rw [Hdepth, ← hselectionLength]
    omega
  rcases Htrace.targetSpine selection Harity HtargetParams
      (Hrun.resultParamsSize.trans hnparams.symm) HtargetExpr with ⟨T⟩
  rcases T.sourceSpine HsourceExpr with ⟨S⟩
  have Htrailing := TrExprS.forall₂_abstractExpansionAbove Hlift Hctx HbaseDepth
    S.trailingTranslation T.trailingTranslation
  rcases T.resolvedAuxiliaryFamily Hrun Henv hclosures Hsources rfl hempty
      with ⟨O⟩
  rcases N.sourceForReplacement Htarget T O hempty with
    ⟨i, hi, hresult, htarget, Ocanonical, hresultFinal, Nsource, hsourceEq⟩
  have hparamLength : Nsource.sourceParams.length = selection.fvars.length := by
    exact Nsource.sourceParamsLength.trans (hnparams ▸ hselectionLength.symm)
  have Hbase := Nsource.baseExpansionsAtReplacement T S Ocanonical
    resultSelection hresultNodup hselectionNodup Harity HsourceParams
      hparamLength Hscope
  have hbaseEq : S.baseArgsAtDepth =
      Nsource.baseArgs.map (fun arg => arg.liftN fieldDepth 0) :=
    (forall₂_nestedExprExpansion_false_eq Hbase).symm
  rcases T.cachedSourceSpines Ocanonical resultSelection hresultNodup
      hselectionNodup Harity Hscope with
    ⟨hheadName, hheadLevels, _Halpha⟩
  have hinputName : T.targetName = Nsource.containerFamily.name :=
    hheadName.trans Nsource.containerName.symm
  have hinputLevels : S.sourceLevels = Nsource.levels := by
    have HmapLevels := congrArg
      (fun levels => levels.mapM (VLevel.ofLevel lparams)) hheadLevels
    exact Option.some.inj (S.sourceLevelsTranslation.symm.trans
      (HmapLevels.trans Nsource.levelsTranslation))
  have hinput : sourceValue = VExpr.mkApps
      (.const Nsource.containerFamily.name Nsource.levels)
      (S.baseArgsAtDepth ++ S.trailing) := by
    calc
      sourceValue = VExpr.mkApps (.const T.targetName S.sourceLevels)
          (S.baseArgsAtDepth ++ S.trailing) := S.sourceValue_eq
      _ = _ := congrArg
        (fun head => VExpr.mkApps head (S.baseArgsAtDepth ++ S.trailing))
        ((congrArg (fun name => VExpr.const name S.sourceLevels) hinputName).trans
          (congrArg (VExpr.const Nsource.containerFamily.name) hinputLevels))
  -- the specialisation recorded for the source data of the occurrence
  rcases List.mem_iff_getElem.mp Nsource.familyMember with ⟨idx, hidx, hfamily⟩
  let aN : ContainerSpecialization := {
    container := Nsource.container
    family := ⟨idx, hidx⟩
    auxiliary := T.auxName
    levels := Nsource.levels
    arguments := Nsource.baseArgs }
  have hnestedClosed : Ocanonical.origin.generated.data.nested.looseBVarRange' = 0 := by
    rw [Ocanonical.nested_eq]
    exact hclosedNested _ _ T.resultLookup
  have hspecN : AuxiliaryContainerApp result lparams T.nested aN := by
    have h := Nsource.auxiliaryContainerApp aN
      (by
        change Nsource.container.types[idx].name = _
        rw [hfamily]
        exact Nsource.containerName)
      rfl rfl hfvars hfvarsNodup resultSelection hnestedClosed hnp
    rwa [Ocanonical.nested_eq] at h
  obtain ⟨a, ha, haux, hspec⟩ := hfamilyKey _ _ T.resultLookup
  obtain ⟨hsrcName, hlevelsEq, hargsEq⟩ := hspec.unique hspecN
  have hsrcName' : a.source.name = Nsource.containerFamily.name := by
    rw [hsrcName]
    change Nsource.container.types[idx].name = _
    rw [hfamily]
  -- the leaf
  have htargetValue := T.targetValue_eq
  have hlv : Nsource.levels = a.levels := hlevelsEq.symm
  have hav : Nsource.baseArgs = a.arguments := hargsEq.symm
  rw [← hsrcName', hlv] at hinput
  rw [hav] at hbaseEq
  generalize S.baseArgsAtDepth = sBase at hinput hbaseEq
  generalize S.trailing = sTr at hinput Htrailing
  generalize T.trailing = tTr at htargetValue Htrailing
  generalize T.auxiliaryLevels = auxLv at htargetValue
  generalize T.auxName = auxName at htargetValue haux
  subst hinput hbaseEq
  intro hs ht
  rw [htargetValue] at ht ⊢
  rw [VExpr.containsAnyConst_mkApps_eq_false_iff] at hs
  rw [VExpr.constLevelsAt_mkApps] at ht
  have hmem : HeadSpecialization.mk a.auxiliary sourceDecl.uvars sourceDecl.nparams
      a.source.name a.levels a.arguments ∈ r.heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have hauxLevels : auxLv = VLevel.params sourceDecl.uvars := by
    apply ht.1
    rw [← haux]
    exact List.mem_map_of_mem hmem
  have htrailingRestore : List.Forall₂
      (fun x y => Restoration.expr.go r x [] = some y) tTr sTr :=
    VExpr.NestedExprExpansion.forall₂_restore Htrailing
      (fun s hsMem => hs.2 s (List.mem_append_right _ hsMem))
      (fun t htMem => ht.2 t (List.mem_append_right _ htMem))
  have hargsRestore := _root_.List.Forall₂.append'
    (restoration_expr_paramVars (r := r) sourceDecl fieldDepth) htrailingRestore
  change Restoration.expr.go r _ [] = _
  rw [Restoration.expr.go_mkApps r hargsRestore, List.append_nil]
  have hfind : r.heads.find? (fun h => h.auxiliary == auxName) =
      some (HeadSpecialization.mk a.auxiliary sourceDecl.uvars sourceDecl.nparams
        a.source.name a.levels a.arguments) := by
    rw [← haux]
    exact InductiveSignature.Restoration.find?_of_nodup hheadNodup hmem
  have hparamVarsLength : (sourceDecl.paramVars fieldDepth).length = sourceDecl.nparams := by
    simp [VInductDecl.paramVars]
  subst hauxLevels
  have hcond : ((VLevel.params sourceDecl.uvars).length != sourceDecl.uvars ||
      decide ((sourceDecl.paramVars fieldDepth ++ sTr).length < sourceDecl.nparams)) =
        false := by
    simp [VLevel.params, hparamVarsLength]
  have hlv' : a.levels.map (·.inst (VLevel.params sourceDecl.uvars)) = a.levels :=
    (List.map_congr_left fun l hl => VLevel.inst_id (hlevels a ha l hl)).trans
      (List.map_id _)
  have hav' : a.arguments.map (fun arg => instantiateParams
      (arg.instL (VLevel.params sourceDecl.uvars))
      ((sourceDecl.paramVars fieldDepth ++ sTr).take sourceDecl.nparams)) =
      a.arguments.map (fun arg => arg.liftN fieldDepth 0) := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    apply List.map_congr_left
    intro arg harg
    obtain ⟨hclosed, hwf⟩ := hargs a ha arg harg
    rw [hwf.instL_id]
    exact instantiateParams_vars hclosed fieldDepth
  have hdrop : (sourceDecl.paramVars fieldDepth ++ sTr).drop sourceDecl.nparams = sTr := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
  simp only [Restoration.expr.go, hfind, HeadSpecialization.apply, hcond,
    Bool.false_eq_true, if_false, Option.pure_def]
  rw [hlv', hav', hdrop]

/-! ### Lowered constructors and auxiliary keys of a lowering run -/

private theorem forall₂_trCtor_names
    {ctors : List Constructor} {ctors' : List VConstVal}
    (H : List.Forall₂
      (fun ctor ctor' => TrSourceConst envTypes lparams ctor.name ctor.type ctor')
      ctors ctors') :
    ctors'.map (·.name) = ctors.map (·.name) := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih, ← h.name]

theorem ConstructorListEntries.ctorOfEntry
    {stats : AddInductive.InductiveStats} {lparams : List Name}
    {isUnsafe : Bool} {owner : InductiveType} {ctors : List Constructor}
    {entries : List (ConstantInfo × VConstVal)} {initial : Nat}
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      initial ctors entries)
    {entry : ConstantInfo × VConstVal} (hentry : entry ∈ entries) :
    ∃ ctor ∈ ctors, ∃ info : ConstructorVal,
      entry.1 = .ctorInfo info ∧ info.name = ctor.name ∧ info.induct = owner.name := by
  induction H with
  | nil => simp at hentry
  | @cons start ctors tailEntries ctor value Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact ⟨ctor, List.mem_cons_self, _, rfl,
        by simp [AddInductive.constructorInfo], by simp [AddInductive.constructorInfo]⟩
    · rcases ih htail with ⟨c, hc, info, he, hn, hi⟩
      exact ⟨c, List.mem_cons_of_mem _ hc, info, he, hn, hi⟩

theorem ConstructorTypeEntries.ctorOfEntry
    {stats : AddInductive.InductiveStats} {lparams : List Name}
    {isUnsafe : Bool} {owners : List InductiveType}
    {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) owners entries)
    {entry : ConstantInfo × VConstVal} (hentry : entry ∈ entries) :
    ∃ owner ∈ owners, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
      entry.1 = .ctorInfo info ∧ info.name = ctor.name ∧ info.induct = owner.name := by
  induction H with
  | nil => simp at hentry
  | cons Hhead Htail ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · rcases Hhead.ctorOfEntry hhead with ⟨ctor, hctor, info, he, hn, hi⟩
      exact ⟨_, List.mem_cons_self, ctor, hctor, info, he, hn, hi⟩
    · rcases ih htail with ⟨owner, howner, ctor, hctor, info, he, hn, hi⟩
      exact ⟨owner, List.mem_cons_of_mem _ howner, ctor, hctor, info, he, hn, hi⟩

/-- Every constructor visible in the kernel environment after the lowered run either
predates the inductive installation or is a constructor of one of the
installed families, recording that family as its owner. -/
theorem RecursorCheck.ctorInfoOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv) (hwf : c.env.constants.WF)
    {n : Name} {info : ConstructorVal}
    (hfind : outEnv.find? n = some (.ctorInfo info)) :
    c.env.find? n = some (.ctorInfo info) ∨
      ∃ owner ∈ indTypes.toList, ∃ ctor ∈ owner.ctors,
        n = ctor.name ∧ info.induct = owner.name := by
  rcases H.installation.atomic.entryOrigin hwf hfind with hold | ⟨entry, hentry, hname, hfound⟩
  · exact .inl hold
  · right
    rcases List.mem_append.mp hentry with h12 | hrec
    · rcases List.mem_append.mp h12 with hhead | hctor
      · exfalso
        obtain ⟨k, hk⟩ := Hheaders.infos
        have hm : entry.1 ∈ Hheaders.entries.map Prod.fst := List.mem_map_of_mem hhead
        rw [hk] at hm
        obtain ⟨i, _, he⟩ := List.mem_map.mp hm
        rw [← he] at hfound
        cases hfound
      · obtain ⟨owner, howner, ctor, hctor, info', he, hn, hi⟩ :=
          R.declared.sourceAligned.ctorOfEntry hctor
        rw [he] at hfound hname
        cases hfound
        exact ⟨owner, howner, ctor, hctor, hname.trans hn, hi⟩
    · exfalso
      rcases List.mem_iff_getElem.mp hrec with ⟨i, hi, rfl⟩
      have := (H.generated.entry i hi).source_eq
      rw [this] at hfound
      cases hfound

theorem NestedLowering.resultTypes_eq
    (H : NestedLowering env fuel nparams types initialState out) :
    out.1.types = out.2.newTypes.toList := by
  rcases H.source with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultTypes

/-! ### The restoration tables of a validated nested run -/

open _root_.Lean4Lean.InductiveSignature in
/-- The container specialisations of a validated nested run (as in
`NestedRun.containerSpecializations`), together with the
executable restoration-table data relating them to the run's `aux2nested`
map, lowered constructors and auxiliary-recursor map, and the expansion of
the source constructors into the lowered ones by leaves that the restoration
table inverts (`Restoration.RestoringLeaf`), for the source families and
for the auxiliary families alike. -/
theorem NestedRun.restorationTablesRestoringAllSpec
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (generated : List VInductiveType)
        (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      List.Forall₂ (SpecializationGenerates
        (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
        E.lowered.headers.commonParameterContext sourceDecl)
        auxiliaries generated ∧
      List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          (VInductDecl.NestedOccurrenceReplacementAbs
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
        generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
      result.params.size = result.nparams ∧
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams ∧
      List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length) ∧
      List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
            (VLevel.params sourceDecl.uvars)))
        generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
      ∀ a ∈ auxiliaries, ∃ nested, result.aux2nested.find? a.auxiliary = some nested ∧
        AuxiliaryContainerAppAt envTypes E.lowered.headers.commonParameterContext result lparams
          nested a := by
  have hloweredNodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : P.nparams = nparams := E.lowered_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  let initialState := E.initialState
  have Hlower : NestedLoweringOutputClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hpack := E.phases
  let R := Hpack.constructors
  let Hprod := Hpack.recursors
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.sourceCoreDecl_eq] using E.sourceCore.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hpack.headers.context.venv
        R.declared.venvCtors := by
    exact R.core
  have Hmetadata : SourcePrefixOfLowered sourceDecl P.loweredDecl := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.checked
  have wfP : ves.WF P.c.env := by
    simpa only [henv] using wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.sourceCore.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    simpa only [hinitial, safety] using E.sourceCore.sourceAdded
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource
      (by simpa only [hinitial, safety] using
        (wf.tr (safety := safety)).wf)
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := by
    rfl
  rcases Hrun.auxiliaryFamilySources Hcache Hparams wfP
      hinitial HcP Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, hNctx⟩
  have hctxEq : N.parameterContext = P.headers.commonParameterContext := by
    exact hNctx.trans E.phases_commonParameterContext
  have Htypes := Hrun.allExpansionsOfSources Hcache Hparams Hsource
    Htarget Hmetadata Hsources
      (VEnvs.WF.environmentTypesClosed wfP) wfP.inductivesClosed
      (by simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf)
      hempty N E.auxiliarySelection
  have hsourceLength : sourceTypes.length = sourceDecl.types.length :=
    TrInductDeclCore.types_length Hsource
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  have hgeneratedLength := N.length
  have hvals : sourceDecl.typeConstants =
      (P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal := by
    have h := E.sourceCore.sourceTypeValues
    rw [E.sourceCoreDecl_eq] at h
    exact h
  have hadded : (ves.venv safety).addConstVals sourceDecl.typeConstants =
      some E.sourceCore.envTypes := by
    have h := HsourceAdded
    rw [hinitial, ← hvals] at h
    exact h
  have hprefixLength : sourceDecl.types.length =
      (P.loweredDecl.types.take sourceDecl.types.length).length := by
    simp only [List.length_take]
    omega
  have Hparts := (Lean4Lean.List.Forall₂.append_of_left hprefixLength).mp
    (by rw [List.take_append_drop]; exact Htypes)
  have hbaseLE : P.initialEnv ≤ E.sourceCore.envTypes :=
    VEnv.addConstVals_le HsourceAdded
  have Hmap : NestedAuxMapModels result finalState :=
    Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  obtain ⟨fvars, hfvars, hfvarsNodup⟩ := Hparams
  have hnp : result.nparams = P.nparams := Hrun.resultNParams
  have hparamsSize : result.params.size = result.nparams :=
    Hrun.resultParamsSize.trans hnp.symm
  have Hpoint : ∀ family ∈ N.generated, ∃ a,
      SpecializationGenerates (ves.venv safety) E.sourceCore.envTypes
        N.parameterContext sourceDecl a family ∧
      ∃ nested, result.aux2nested.find? a.auxiliary = some nested ∧
        AuxiliaryContainerApp result P.c.lparams nested a ∧
        AuxiliaryContainerAppAt E.sourceCore.envTypes N.parameterContext result P.c.lparams
          nested a := by
    intro family hfamily
    rcases List.mem_iff_getElem.mp hfamily with ⟨i, hi, rfl⟩
    have hresult : sourceTypes.length + i < result.types.length := by omega
    have hlowered : sourceTypes.length + i < P.loweredDecl.types.length := by
      omega
    rcases N.parametersAt i hi hresult hlowered with ⟨Horigin, NN, hNN, hctx⟩
    rw [← hNN]
    rcases NN.linkedSpecialization hinitial wfP sourceDecl Hsource.uvars
      Hsource.nparams (Hsource.isUnsafe.trans hisUnsafe) hbaseLE hctx with
      ⟨a, hev, haux, hsrc, hlev, hargs⟩
    have hfind : result.aux2nested.find? a.auxiliary =
        some Horigin.generated.data.nested := by
      rw [haux, NN.sourceName]
      exact Hmap _ _ Horigin.generated.cached
    rcases Htranslations _ _ hfind with ⟨Htr⟩
    refine ⟨a, hev, Horigin.generated.data.nested, hfind, ?_, ?_⟩
    · exact NN.auxiliaryContainerApp a (by rw [hsrc, NN.containerName]) hlev hargs hfvars
        hfvarsNodup E.auxiliarySelection Htr.sourceClosed.looseBVarRange_zero hnp
    · exact NN.auxiliaryContainerAppAt a (by rw [hsrc, NN.containerName]) hlev hargs hfvars
        hfvarsNodup E.auxiliarySelection Htr.sourceClosed.looseBVarRange_zero hnp
        (VEnv.IsDefEqCtx.mono hbaseLE hctx)
  rcases exists_forall₂_of_forall Hpoint with ⟨auxiliaries, Haux'⟩
  have Haux := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) Haux'
  have Hexpansion := Hparts.2
  have hauxNames := auxiliarySpecializations_names Haux Hexpansion
  rw [hctxEq] at Haux Haux'
  obtain ⟨generated, hgenEq⟩ : ∃ g, g = N.generated := ⟨_, rfl⟩
  rw [← hgenEq] at Haux Haux' Hexpansion
  rw [hinitial] at Hexpansion
  have D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams := by
    rw [hlparams] at Haux'
    have hloweredNames : P.loweredDecl.types.map (·.name) = result.types.map (·.name) :=
      forall₂_trInductiveType_names Htarget.types
    have htypesNodup : (P.loweredDecl.types.map (·.name)).Nodup := by
      have h := (List.nodup_append.mp
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)).1
      simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
        Function.comp_def] using h
    have hwfMap : P.c.env.constants.WF := HcP.checking.tr.map_wf
    have Hfresh : RestoreAuxFamiliesFresh result P.c.env :=
      Hrun.resultFamilyNamesFreshOfEmpty hwfMap rfl
    -- per-auxiliary data
    have Hper : ∀ a ∈ auxiliaries, ∃ g t,
        SpecializationGenerates (ves.venv safety) E.sourceCore.envTypes
          P.headers.commonParameterContext sourceDecl a g ∧
        VInductDecl.NestedTypeExpansion (ves.venv safety) sourceDecl
          (VInductDecl.NestedOccurrenceReplacementAbs (ves.venv safety) sourceDecl
            generated) g t ∧
        t ∈ P.loweredDecl.types ∧ t.name = a.auxiliary ∧
        t.ctors.map (·.name) = a.source.ctors.map a.constructorName ∧
        ∃ nested, result.aux2nested.find? a.auxiliary = some nested ∧
          AuxiliaryContainerApp result lparams nested a := by
      intro a ha
      rcases Lean4Lean.List.Forall₂.forall_exists_l Haux' a ha with
        ⟨g, hg, hev, nested, hfind, hspec, -⟩
      rcases Lean4Lean.List.Forall₂.forall_exists_l Hexpansion g hg with
        ⟨t, ht, hexp⟩
      exact ⟨g, t, hev, hexp, List.mem_of_mem_drop ht,
        hexp.name.trans hev.auxiliary.symm,
        (nestedConstructorExpansions_names hexp.constructors).trans
          hev.generatedCtorNames, nested, hfind, hspec⟩
    -- lowered constructors are installed as constructors of their family
    have HctorFacts : ∀ t ∈ P.loweredDecl.types, ∀ ctor ∈ t.ctors,
        (∃ info : ConstructorVal,
          E.loweredEnv.find? ctor.name = some (.ctorInfo info) ∧ info.induct = t.name) ∧
        P.initialEnv.constants ctor.name = none := by
      intro t ht ctor hctor
      constructor
      · rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types t ht with
          ⟨T, hT, htrT⟩
        rcases Lean4Lean.List.Forall₂.forall_exists_r htrT.ctors ctor hctor with
          ⟨C, hC, htrC⟩
        rcases ConstructorTypeEntries.findInduct R.declared.sourceAligned
            (by simpa using hT) hC with ⟨info, value, hmem, hname, hinduct⟩
        refine ⟨info, ?_, ?_⟩
        · rw [htrC.name, ← hname]
          exact Hprod.findConstructorOfMem hmem
        · rw [hinduct, ← htrT.header.name]
      · have hmem : ctor ∈ P.loweredDecl.constructorConstants := by
          simp only [VInductDecl.constructorConstants, List.mem_flatMap]
          exact ⟨t, ht, hctor⟩
        have hfresh := (VEnv.addConstVals_names_fresh R.core.ctorsAdded).2 ctor hmem
        cases hsource : P.initialEnv.constants ctor.name with
        | none => rfl
        | some ci =>
          have := (VEnv.addConstVals_le R.core.typesAdded).constants hsource
          rw [hfresh] at this
          cases this
    -- the main family's recursor metadata
    rcases Hrun.source with
      ⟨main, rest, _tail, _paramsState, _lctx, _params, hsourceTypes, _⟩
    have hmainMem : main ∈ sourceTypes := by rw [hsourceTypes]; simp
    rcases Hrun.preservesInitialTypeName ⟨main, by simpa using hmainMem, rfl⟩ with
      ⟨loweredMain, hloweredMain, hloweredName⟩
    rcases Hprod.findSourceHeader HcP (by simpa using hloweredMain) with
      ⟨info, hfindMain, _hctors, hall⟩
    rw [hloweredName] at hfindMain
    have hsourceNames := forall₂_trInductiveType_names Hsource.types
    have hfirst : sourceDecl.types.head?.map (·.name) = some main.name := by
      have h := congrArg List.head? hsourceNames
      rw [hsourceTypes] at h
      simpa [List.head?_map] using h
    have hnames : auxiliaries.map (·.auxiliary) =
        info.all.drop (main :: rest).length := by
      rw [hauxNames, hall, List.map_drop, hloweredNames, ← hsourceLength,
        hsourceTypes]
    have hnodupAux : (auxiliaries.map (·.auxiliary)).Nodup := by
      rw [hauxNames, List.map_drop]
      exact htypesNodup.sublist (List.drop_sublist _ _)
    have hauxRec : (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 =
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2 := by
      generalize E.loweredEnv = L
      rw [hsourceTypes]
    rw [hauxRec]
    have hheadsNodup : (auxiliaries.flatMap (·.headNames)).Nodup := by
      rw [auxiliarySpecializations_headNames Haux Hexpansion]
      exact (List.nodup_append.mp hloweredNodup).1.sublist (familyNames_drop_sublist _ _)
    refine {
      headNodup := hheadsNodup
      uvars := by rw [← hlparams]; exact Hsource.uvars
      nparams := Hsource.nparams.trans hnp.symm
      paramsFVars := ⟨fvars, hfvars⟩
      recursorName := compilationRestoration_recursorName_eq_mkAuxRecNameMap sourceDecl
        auxiliaries main rest E.loweredEnv info hfindMain hfirst hnames hnodupAux
      recursorNotHead := ?_
      familyKey := ?_
      familyLookup := ?_
      ctorLookup := ?_
      ctorInstalled := ?_
      ctorRenamed := ?_ }
    · intro c new hc hmem
      have hcmem : c ∈ (info.all.drop (main :: rest).length).map Lean.mkRecName := by
        by_contra hnot
        rw [mkAuxRecNameMap_recMap_find_none main rest E.loweredEnv info hfindMain hnot]
          at hc
        cases hc
      rw [← hnames, List.map_map] at hcmem
      rcases List.mem_map.mp hcmem with ⟨a, ha, rfl⟩
      rcases Hper a ha with ⟨_, t, _, _, ht, htname, _⟩
      rw [auxiliarySpecializations_headNames Haux Hexpansion] at hmem
      have hfam : (Function.comp Lean.mkRecName (·.auxiliary)) a ∈
          familyNames P.loweredDecl.types :=
        (familyNames_drop_sublist _ _).subset hmem
      have hrec : (Function.comp Lean.mkRecName (·.auxiliary)) a ∈
          P.loweredDecl.types.map (fun t => t.name.str "rec") :=
        List.mem_map.mpr ⟨t, ht, by rw [htname]; rfl⟩
      exact (List.nodup_append.mp hloweredNodup).2.2 _ hfam _ hrec rfl
    · intro c nested hfind
      have hmem := Hrun.resolvedCacheEntryOfResultLookup hfind
      rcases (Hrun.resolvedAuxFamilyPosition rfl).position nested c hmem with
        ⟨j, hj, hinit, hname⟩
      have htypesEq := Hrun.resultTypes_eq
      simp only [List.size_toArray] at hinit hj
      have hcmem : c ∈ auxiliaries.map (·.auxiliary) := by
        rw [hauxNames, List.map_drop, hloweredNames, ← hsourceLength]
        change c ∈ List.drop sourceTypes.length (List.map (·.name) result.types)
        rw [htypesEq, List.mem_iff_getElem]
        refine ⟨j - sourceTypes.length, by simp at hinit hj ⊢; omega, ?_⟩
        simp only [List.getElem_drop, List.getElem_map, Array.getElem_toList]
        rw [← hname]
        congr 2
        omega
      rcases List.mem_map.mp hcmem with ⟨a, ha, rfl⟩
      rcases Hper a ha with ⟨_, _, _, _, _, _, _, nested', hfind', hspec⟩
      rw [hfind] at hfind'
      cases hfind'
      exact ⟨a, ha, rfl, hspec⟩
    · intro a ha
      rcases Hper a ha with ⟨_, _, _, _, _, _, _, nested, hfind, _⟩
      exact ⟨nested, hfind⟩
    · intro c cinfo hfind a ha hinduct
      rcases Hprod.ctorInfoOrigin hwfMap hfind with hold | ⟨owner, howner, ctor, hctor, rfl, hown⟩
      · exfalso
        rcases wfP.constructorOwners c cinfo hold with ⟨ownerInfo, hownerFind, -⟩
        rcases Hper a ha with ⟨_, _, _, _, _, _, _, nested, hfindAux, _⟩
        have := Hfresh _ nested hfindAux
        rw [← hinduct, hownerFind] at this
        cases this
      · rcases Hper a ha with ⟨_, t, _, _, ht, htname, hctorNames, _⟩
        have howner' : owner ∈ result.types := by simpa using howner
        rcases Lean4Lean.List.Forall₂.forall_exists_l Htarget.types owner howner' with
          ⟨T, hT, htrT⟩
        have hTname : T.name = owner.name := htrT.header.name
        have hTt : T = t := by
          apply Lean4Lean.List.nodup_map_inj htypesNodup hT ht
          rw [hTname, ← hown, hinduct, htname]
        subst hTt
        have hmem : ctor.name ∈ T.ctors.map (·.name) := by
          rw [forall₂_trCtor_names htrT.ctors]
          exact List.mem_map_of_mem hctor
        rw [hctorNames] at hmem
        rcases List.mem_map.mp hmem with ⟨ctor', hctor', heq⟩
        exact ⟨ctor', hctor', heq.symm⟩
    · intro a ha ctor hctor
      rcases Hper a ha with ⟨_, t, _, _, ht, htname, hctorNames, _⟩
      have hcmem : a.constructorName ctor ∈ t.ctors.map (·.name) := by
        rw [hctorNames]; exact List.mem_map_of_mem hctor
      rcases List.mem_map.mp hcmem with ⟨c', hc', hc'name⟩
      rcases (HctorFacts t ht c' hc').1 with ⟨cinfo, hfind, hinduct⟩
      rw [hc'name] at hfind
      exact ⟨cinfo, hfind, hinduct.trans htname⟩
    · intro a ha ctor hctor heq
      rcases Hper a ha with ⟨_, t, hev, _, ht, _, hctorNames, _⟩
      have hcmem : a.constructorName ctor ∈ t.ctors.map (·.name) := by
        rw [hctorNames]; exact List.mem_map_of_mem hctor
      rcases List.mem_map.mp hcmem with ⟨c', hc', hc'name⟩
      have hfresh := (HctorFacts t ht c' hc').2
      rw [hc'name, heq] at hfresh
      rcases List.mem_iff_getElem.mp hctor with ⟨k, hk, hkEq⟩
      have hlookup := hev.installed.constructorConstant a.family k a.family.isLt hk
      have hsome : (ves.venv safety).constants ctor.name ≠ none := by
        rw [← hkEq]
        change (ves.venv safety).constants
          ((a.container.types[(a.family : Nat)]'a.family.isLt).ctors[k]'hk).name
            ≠ none
        rw [hlookup]
        simp
      rw [← hinitial, hfresh] at hsome
      exact hsome rfl

  have Hspec : ∀ a ∈ auxiliaries, ∃ nested, result.aux2nested.find? a.auxiliary = some nested ∧
      AuxiliaryContainerAppAt E.sourceCore.envTypes E.lowered.headers.commonParameterContext
        result lparams nested a := by
    intro a ha
    rcases Lean4Lean.List.Forall₂.forall_exists_l Haux' a ha with
      ⟨g, -, -, nested, hfind, -, hspec⟩
    rw [hlparams] at hspec
    exact ⟨nested, hfind, hspec⟩
  refine ⟨E.sourceCore.envTypes, generated, auxiliaries, hadded,
    HsourceTypesWF, Haux, Hexpansion, hparamsSize, D, ?_⟩
  -- the restoring expansion of the source families
  let r := compilationRestoration sourceDecl auxiliaries
  have hscopedArgs : ∀ a ∈ auxiliaries, ∀ arg ∈ a.arguments,
      arg.ClosedN sourceDecl.nparams ∧ arg.LevelWF sourceDecl.uvars := by
    intro a ha arg harg
    obtain ⟨g, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    exact ⟨hev.argumentsClosed arg harg, hev.argumentsLevelWF arg harg⟩
  have hlevelsWF : ∀ a ∈ auxiliaries, ∀ l ∈ a.levels, l.WF sourceDecl.uvars := by
    intro a ha l hl
    obtain ⟨g, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    exact hev.levelsWF l hl
  have hheadsClosed : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams := by
    intro h hh e he
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hh
    simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
    rcases hh with rfl | ⟨_, _, rfl⟩ <;> exact (hscopedArgs a ha e he).1
  have Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams
      (r.RestoringLeaf (VLevel.params sourceDecl.uvars)) :=
    Restoration.restoringLeaf_liftAbove r hheadsClosed
      (VLevel.params sourceDecl.uvars) sourceDecl.nparams
  have hheadNodup : (r.heads.map (·.auxiliary)).Nodup := by
    rw [compilationRestoration_heads_auxiliary]
    exact D.headNodup
  have hkey : ∀ c nested, result.aux2nested.find? c = some nested →
      ∃ a ∈ auxiliaries, a.auxiliary = c ∧ AuxiliaryContainerApp result P.c.lparams nested a := by
    rw [hlparams]
    exact D.familyKey
  have hclosedNested : ∀ c nested, result.aux2nested.find? c = some nested →
      nested.looseBVarRange' = 0 := by
    intro c nested hfind
    rcases Htranslations _ _ hfind with ⟨Htr⟩
    exact Htr.sourceClosed.looseBVarRange_zero
  let Hclosed : NestedLoweringOutputClosed P.c.env E.validationFuel.inductiveFuel
      P.nparams sourceTypes { initialState with newTypes := sourceTypes.toArray }
      result := ⟨finalState, Hrun, Hcache, ⟨fvars, hfvars, hfvarsNodup⟩⟩
  have hresultNodup := Hclosed.selectionNodup E.auxiliarySelection
  have Horiginal := Hclosed.sourceExpansionsAbove Hlift Hsource Htarget Hmetadata
    Hsources hempty
    (by simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf)
    (N.restoringReplacement Htarget
      (VEnvs.WF.environmentTypesClosed wfP) wfP.inductivesClosed Hsources
      E.auxiliarySelection hresultNodup hempty Hsource.nparams hfvars hfvarsNodup hnp
      hclosedNested hkey hheadNodup hscopedArgs hlevelsWF Hlift)
  refine ⟨Lean4Lean.List.Forall₂.imp (fun _ _ h =>
    Lean4Lean.List.Forall₂.imp (fun _ _ hc => hc.type) h.constructors) Horiginal, ?_⟩
  -- the restoring expansion of the auxiliary families
  have hbaseWF : P.initialEnv.WF := by
    simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf
  have HtargetTypesWF : Hpack.headers.context.venv.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget hbaseWF
  have Hall : List.Forall₂ (VInductDecl.NestedTypeExpansion P.initialEnv sourceDecl
      (r.RestoringLeaf (VLevel.params sourceDecl.uvars)))
      generated (P.loweredDecl.types.drop sourceDecl.types.length) := by
    subst hgenEq
    have hdropLength : (P.loweredDecl.types.drop sourceDecl.types.length).length =
        N.generated.length := by
      rw [List.length_drop]
      omega
    apply List.forall₂_of_getElem hdropLength.symm
    intro i hgen hdrop
    have hresult : sourceTypes.length + i < result.types.length := by omega
    have htarget : sourceTypes.length + i < P.loweredDecl.types.length := by omega
    rcases N.sourceAt i hgen hresult htarget with ⟨Horigin, Nsource, hsourceEq⟩
    have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
      Htarget (sourceTypes.length + i) hresult htarget
    have Hmapping := Horigin.resolvedMapping Hmap
    have Hheader : NestedTypeExpansionHeader P.initialEnv sourceDecl
        Nsource.source P.loweredDecl.types[sourceTypes.length + i] :=
      Hmapping.abstractHeaderExpansion Nsource.translation HtargetType hbaseWF
        Hsource.uvars Nsource.numIndices Nsource.resultLevel
    have hstep : Horigin.stepState.lvls = finalState.lvls :=
      Horigin.lowered.nestedAuxLE.lvls.symm.trans Horigin.later.lvls.symm
    have Hexp := Hmapping.abstractExpansionAbove Hlift hstep Nsource.translation
      HtargetType Hheader
      (Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.constructorsClosed
        Nsource.translation)
      HsourceTypesWF HtargetTypesWF Hrun.resultParamsSize Hsource.nparams.symm
      (fun Htrace Hctx selection hnd Harity Hdepth hsp htp hscope hse hte _ =>
        N.restoringReplacement Htarget
          (VEnvs.WF.environmentTypesClosed wfP) wfP.inductivesClosed Hsources
          E.auxiliarySelection hresultNodup hempty Hsource.nparams hfvars hfvarsNodup hnp
          hclosedNested hkey hheadNodup hscopedArgs hlevelsWF Hlift
          Htrace Hctx selection hnd Harity Hdepth hsp htp hscope hse hte)
    rw [hsourceEq] at Hexp
    have hdropGet : (P.loweredDecl.types.drop sourceDecl.types.length)[i] =
        P.loweredDecl.types[sourceTypes.length + i] := by
      simp only [List.getElem_drop, hsourceLength]
    rw [hdropGet]
    exact Hexp
  rw [hinitial] at Hall
  exact ⟨Hall, Hspec⟩

open _root_.Lean4Lean.InductiveSignature in
theorem NestedRun.restorationTablesRestoringAll
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (generated : List VInductiveType)
        (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      List.Forall₂ (SpecializationGenerates
        (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
        E.lowered.headers.commonParameterContext sourceDecl)
        auxiliaries generated ∧
      List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          (VInductDecl.NestedOccurrenceReplacementAbs
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
        generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
      result.params.size = result.nparams ∧
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams ∧
      List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length) ∧
      List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
            (VLevel.params sourceDecl.uvars)))
        generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
  obtain ⟨envTypes, generated, auxiliaries, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
    E.restorationTablesRestoringAllSpec wf Hsources
  exact ⟨envTypes, generated, auxiliaries, h1, h2, h3, h4, h5, h6, h7, h8⟩

open _root_.Lean4Lean.InductiveSignature in
/-- `restorationTablesRestoringAll` without the auxiliary families' restoring
expansion. -/
theorem NestedRun.restorationTablesRestoring
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (generated : List VInductiveType)
        (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      List.Forall₂ (SpecializationGenerates
        (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
        E.lowered.headers.commonParameterContext sourceDecl)
        auxiliaries generated ∧
      List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          (VInductDecl.NestedOccurrenceReplacementAbs
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
        generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
      result.params.size = result.nparams ∧
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams ∧
      List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.lowered.loweredDecl.types.take sourceDecl.types.length) := by
  obtain ⟨envTypes, generated, auxiliaries, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    E.restorationTablesRestoringAll wf Hsources
  exact ⟨envTypes, generated, auxiliaries, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### Instantiating parameter telescopes at free variables -/

/-! ### Closure of the restored body -/

theorem Closed.instantiate1'_of_closed {a : Expr} (ha : Closed a) :
    ∀ (e : Expr) (K d : Nat), Closed e K → Closed (e.instantiate1' a d) K
  | .bvar i, K, d, h => by
    simp only [Expr.instantiate1']
    split
    · exact h
    · split
      · rw [Expr.liftLooseBVars_eq_self (by simp [ha.looseBVarRange_zero])]
        exact ha.mono (Nat.zero_le _)
      · simp only [Closed] at h ⊢; omega
  | .app f x, K, d, h => ⟨Closed.instantiate1'_of_closed ha f K d h.1,
      Closed.instantiate1'_of_closed ha x K d h.2⟩
  | .lam _ t b _, K, d, h => ⟨Closed.instantiate1'_of_closed ha t K d h.1,
      Closed.instantiate1'_of_closed ha b (K + 1) (d + 1) h.2⟩
  | .forallE _ t b _, K, d, h => ⟨Closed.instantiate1'_of_closed ha t K d h.1,
      Closed.instantiate1'_of_closed ha b (K + 1) (d + 1) h.2⟩
  | .letE _ t v b _, K, d, h => ⟨Closed.instantiate1'_of_closed ha t K d h.1,
      Closed.instantiate1'_of_closed ha v K d h.2.1,
      Closed.instantiate1'_of_closed ha b (K + 1) (d + 1) h.2.2⟩
  | .mdata _ e, K, d, h => Closed.instantiate1'_of_closed ha e K d h
  | .proj _ _ e, K, d, h => Closed.instantiate1'_of_closed ha e K d h
  | .fvar _, _, _, h => h
  | .sort _, _, _, h => h
  | .const _ _, _, _, h => h
  | .lit _, _, _, h => h
  | .mvar _, _, _, h => h

theorem Closed.instantiateRevList_le {As : List Expr} (hAs : ∀ a ∈ As, Closed a)
    {e : Expr} {K d : Nat} (h : Closed e K) : Closed (e.instantiateRevList As d) K := by
  induction As with
  | nil => simpa using h
  | cons a as ih =>
    simp only [Expr.instantiateRevList]
    exact Closed.instantiate1'_of_closed (hAs a (by simp)) _ K d
      (ih (fun b hb => hAs b (by simp [hb])))

theorem Closed.instantiateRevList {As : List Expr} (hAs : ∀ a ∈ As, Closed a)
    {e : Expr} {k : Nat} (h : Closed e (k + As.length)) :
    Closed (e.instantiateRevList As k) k := by
  apply Closed.of_closed_looseBVarRange (Closed.instantiateRevList_le hAs h)
  rw [← Expr.instantiateList_reverse]
  have := Expr.instantiateList_looseBVarRange (e := e) (as := As.reverse) (k := k) (n := 0)
    (by simpa [Nat.add_comm] using h.looseBVarRange_le)
    (fun a ha => by simp [(hAs a (by simpa using ha)).looseBVarRange_zero])
  simpa using this

theorem Closed.mkAppList_iff {f : Expr} {k : Nat} :
    ∀ {args : List Expr},
      Closed (Expr.mkAppList f args) k ↔ Closed f k ∧ ∀ a ∈ args, Closed a k
  | [] => by simp
  | a :: args => by
    simp only [Expr.mkAppList, List.mem_cons, forall_eq_or_imp]
    rw [Closed.mkAppList_iff]
    simp only [Closed, and_assoc]

theorem ExprReplacement.closed {replaceNode : Expr → Option Expr}
    (hnode : ∀ t out k, replaceNode t = some out → Closed t k → Closed out k)
    {input output : Expr} (H : ExprReplacement replaceNode input output) :
    ∀ k, Closed input k → Closed output k := by
  induction H with
  | occurrence h => exact fun k hk => hnode _ _ k h hk
  | bvar | fvar | mvar | sort | const | lit => exact fun _ hk => hk
  | app _ _ _ ihf iha =>
    intro k hk
    simp only [Expr.updateApp!]
    exact ⟨ihf k hk.1, iha k hk.2⟩
  | lam _ _ _ ihd ihb =>
    intro k hk
    simp only [Expr.updateLambdaE!]
    exact ⟨ihd k hk.1, ihb (k + 1) hk.2⟩
  | forallE _ _ _ ihd ihb =>
    intro k hk
    simp only [Expr.updateForallE!]
    exact ⟨ihd k hk.1, ihb (k + 1) hk.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro k hk
    simp only [Expr.updateLetE!]
    exact ⟨iht k hk.1, ihv k hk.2.1, ihb (k + 1) hk.2.2⟩
  | mdata _ _ ih =>
    intro k hk
    simp only [Expr.updateMData!]
    exact ih k hk
  | proj _ _ ih =>
    intro k hk
    simp only [Expr.updateProj!]
    exact ih k hk

/-- A restoration node preserves closure when every executable replacement
head is closed. -/
theorem restoreNestedNode_closed
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {As : Array Expr} {auxRec : NameMap Name}
    (hH : ∀ c H, restoreHead result env As c = some H → Closed H)
    {t out : Expr} {k : Nat}
    (h : result.restoreNestedNode env As auxRec t = some out) (ht : Closed t k) :
    Closed out k := by
  by_cases hrec : ∃ c ls new, t = .const c ls ∧ auxRec.find? c = some new
  · rcases hrec with ⟨c, ls, new, rfl, hnew⟩
    rw [restoreNestedNode_recursor result env As auxRec c new ls hnew] at h
    cases h
    trivial
  · have hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none := by
      intro c ls heq
      cases hfind : auxRec.find? c with
      | none => rfl
      | some new => exact absurd ⟨c, ls, new, heq, hfind⟩ hrec
    cases hfn : t.getAppFn with
    | const c ls =>
      cases hhead : restoreHead result env As c with
      | none =>
        rw [restoreNestedNode_eq_none_of_restoreHead result env As auxRec t hnotrec
          (fun c' ls' h' => by rw [hfn] at h'; cases h'; exact hhead)] at h
        cases h
      | some H =>
        by_cases hsize : result.nparams ≤ t.getAppArgsList.length
        · rw [restoreNestedNode_eq_of_restoreHead result env As auxRec t hnotrec hfn hhead
            hsize] at h
          cases h
          have ht' : Closed (Expr.mkAppList t.getAppFn t.getAppArgsList) k := by
            rw [Expr.mkAppList_getAppArgsList]; exact ht
          rw [Closed.mkAppList_iff] at ht' ⊢
          exact ⟨(hH c H hhead).mono (Nat.zero_le _),
            fun a ha => ht'.2 a (List.mem_of_mem_drop ha)⟩
        · rw [restoreNestedNode_eq_of_notRecursor result env As auxRec t hnotrec, hfn] at h
          simp only [hhead, Option.bind_some] at h
          rw [if_neg (by rwa [← Array.length_toList, Expr.getAppArgs_toList])] at h
          cases h
    | _ =>
      rw [restoreNestedNode_eq_of_notRecursor result env As auxRec t hnotrec, hfn] at h
      cases h

theorem AuxiliaryContainerApp.reopen_closed {result : Lean4Lean.ElimNestedInductive.Result}
    {Us₀ : List Name} {a : InductiveSignature.ContainerSpecialization}
    {envS : VEnv} {domains : List VExpr} {Ys : List Expr}
    (hdomains : domains.length = result.nparams)
    (hYs : List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys
      a.arguments)
    {As : Array Expr} (hAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv)
    (hsize : As.size = result.nparams) :
    ∀ Y ∈ Ys, Closed (Y.instantiateRevList As.toList 0) := by
  intro Y hY
  rcases Lean4Lean.List.Forall₂.forall_exists_l hYs Y hY with ⟨_, _, hY'⟩
  apply Closed.instantiateRevList
  · intro b hb
    rcases hAs b hb with ⟨fv, rfl⟩
    trivial
  · have := hY'.closed
    simpa [hdomains, hsize, VLCtx.bvars] using this

/-- Every executable replacement head is closed, at the opened parameters. -/
theorem RestorationTablesAgree.restoreHead_closed {decl : VInductDecl}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    {As : Array Expr} (hAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv)
    (hsize : As.size = result.nparams) :
    ∀ c H, restoreHead result env As c = some H → Closed H := by
  intro c H hH
  unfold restoreHead at hH
  cases hfind : result.aux2nested.find? c with
  | some nested =>
    rw [hfind] at hH
    cases hH
    obtain ⟨a, _, _, envS, domains, lvls, Ys, hdom, hab, _, hYs⟩ :=
      D.familyKey _ nested hfind
    rw [AuxiliaryContainerApp.reopen hab, Closed.mkAppList_iff]
    exact ⟨trivial, fun Y hY => by
      rcases List.mem_map.mp hY with ⟨Y', hY', rfl⟩
      exact AuxiliaryContainerApp.reopen_closed hdom hYs hAs hsize Y' hY'⟩
  | none =>
    rw [hfind] at hH
    cases hget : result.getNestedIfAuxCtor env c with
    | none => rw [hget] at hH; cases hH
    | some pair =>
      obtain ⟨nested, auxI⟩ := pair
      rw [hget] at hH
      obtain ⟨info, _, hn, rfl⟩ := getNestedIfAuxCtor_eq_some hget
      obtain ⟨a, _, _, envS, domains, lvls, Ys, hdom, hab, _, hYs⟩ :=
        D.familyKey _ nested hn
      simp only [AuxiliaryContainerApp.reopen hab, Expr.getAppFn_mkAppList_const,
        Option.some.injEq] at hH
      subst hH
      rw [Expr.getAppArgs_eq, Expr.getAppArgsList_mkAppList_const,
        Expr.mkAppN_eq_mkAppList]
      rw [Closed.mkAppList_iff]
      exact ⟨trivial, fun Y hY => by
        rcases List.mem_map.mp hY with ⟨Y', hY', rfl⟩
        exact AuxiliaryContainerApp.reopen_closed hdom hYs hAs hsize Y' hY'⟩

/-- The restored body of every opening of a closed lowered type is closed. -/
theorem NestedRestorationOpening.restoredBody_closed {decl : VInductDecl}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    {input output suffix : Expr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (hclosed : Closed input) : Closed Hopen.restoredBody := by
  rcases Hopen.opening.forallResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have hparams : Hopen.params.toList = fvars.map Expr.fvar := by simpa using hAs
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    rcases List.mem_map.mp ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := by
    rw [← Array.length_toList, hparams, List.length_map, hlen]
  have hbodyClosed : Closed Hopen.body := by
    rw [hbody]
    apply Closed.instantiateRevList
    · intro b hb
      rcases List.mem_map.mp hb with ⟨fv, _, rfl⟩
      trivial
    · simpa [hlen] using Htel.closed_result hclosed
  exact Hopen.replacement.closed
    (fun t out k h ht => restoreNestedNode_closed (D.restoreHead_closed HAs hsize) h ht)
    0 hbodyClosed

/-! ### Restored recursor types -/

/-- The specialization arguments of a scoped restoration are scoped by their
parameters. -/
theorem _root_.Lean4Lean.InductiveSignature.Restoration.Scoped.argumentsClosed
    {r : InductiveSignature.Restoration} (H : r.Scoped) :
    ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams :=
  fun h hh e he => (H.2.2.1 h hh).2 e he

end VerifyInductive
end Lean4Lean
