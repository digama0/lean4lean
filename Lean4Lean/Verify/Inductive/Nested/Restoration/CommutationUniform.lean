import Lean4Lean.Verify.Inductive.Nested.Restoration.ExpansionInverse
import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.ExprParamUniform
import Lean4Lean.Verify.Inductive.Rules.Translation
import Lean4Lean.Std.Basic

/-! Commutation of executable nested restoration with `Restoration.expr`,
under the parameter-uniformity side condition.

`ElimNestedInductive.Result.restoreNested` opens the common parameters as
free variables `As` and runs `Expr.replace` with `restoreNestedNode`. A node
whose application head is an auxiliary family or constructor (a *head
occurrence*) is
replaced by the container specialization applied to the arguments after the
parameters; the parameter arguments, the universe levels and the trailing
arguments are not inspected. `Restoration.expr` instead restores every
argument and substitutes the actual parameter arguments.

The two agree (`restorationCommutes`) when

* every head occurrence is applied literally to `As` at the agreed levels
  (`Expr.ParamUniform`, a purely syntactic condition on the input), and
* the translation of the executable output exists in an environment in which
  the restorable names are fresh. This translation forces every untraversed
  trailing argument (and every literal) to avoid the restorable names
  (`TrExprS.sourceAvoidsFresh`), so its two translations agree up to
  restoration (`RestoreCtxRel.translate_avoids`).

Contexts may contain `let` entries (`RestoreCtxRel`): the restored context
stores the restoration of the source value. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature (Restoration HeadSpecialization instantiateParams)

namespace VerifyInductive

/-- Two translation contexts of the same variable naming, where every `let`
value of the restored side is the restoration of the corresponding source
value. Binder types are unrelated. -/
inductive RestoreCtxRel (r : Restoration) : VLCtx → VLCtx → Prop
  | nil : RestoreCtxRel r [] []
  | vlam {Δs Δt : VLCtx} {ofv : Option (FVarId × List FVarId)} {x y : VExpr} :
      RestoreCtxRel r Δs Δt →
      RestoreCtxRel r ((ofv, .vlam x) :: Δs) ((ofv, .vlam y) :: Δt)
  | vlet {Δs Δt : VLCtx} {ofv : Option (FVarId × List FVarId)} {x y vs vt : VExpr} :
      RestoreCtxRel r Δs Δt → r.expr vs = some vt →
      RestoreCtxRel r ((ofv, .vlet x vs) :: Δs) ((ofv, .vlet y vt) :: Δt)

theorem VLCtx.VLamShape.restoreCtxRel {r : Restoration} {Δs Δt : VLCtx}
    (H : VLCtx.VLamShape Δs Δt) : RestoreCtxRel r Δs Δt := by
  induction H with
  | nil => exact .nil
  | cons _ ih => exact .vlam ih

/-- Variable lookup in related contexts: the restored lookup exists and is
the restoration of the source lookup. -/
theorem RestoreCtxRel.find? {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {Δs Δt : VLCtx} (H : RestoreCtxRel r Δs Δt) {v : Nat ⊕ FVarId} {es A : VExpr}
    (hs : Δs.find? v = some (es, A)) :
    ∃ et B, Δt.find? v = some (et, B) ∧ r.expr es = some et := by
  induction H generalizing v es A with
  | nil => cases hs
  | @vlam Δs Δt ofv x y _ ih =>
    simp only [VLCtx.find?] at hs ⊢
    cases hn : VLCtx.next ofv v with
    | none =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, -⟩
      exact ⟨_, _, rfl, rfl⟩
    | some v' =>
      simp only [hn, Option.bind_eq_bind] at hs ⊢
      cases hf : Δs.find? v' with
      | none => simp [hf] at hs
      | some p =>
        rcases p with ⟨e, A'⟩
        simp only [hf, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, -⟩
        rcases ih hf with ⟨et, B, hft, hr⟩
        refine ⟨et.liftN 1, B.liftN 1, by simp [hft, VLocalDecl.depth], ?_⟩
        show r.expr (e.liftN 1) = _
        rw [← InductiveSignature.Restoration.expr_liftN r hc, hr]
        rfl
  | @vlet Δs Δt ofv x y vs vt _ hv ih =>
    simp only [VLCtx.find?] at hs ⊢
    cases hn : VLCtx.next ofv v with
    | none =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, -⟩
      exact ⟨_, _, rfl, hv⟩
    | some v' =>
      simp only [hn, Option.bind_eq_bind] at hs ⊢
      cases hf : Δs.find? v' with
      | none => simp [hf] at hs
      | some p =>
        rcases p with ⟨e, A'⟩
        simp only [hf, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, -⟩
        rcases ih hf with ⟨et, B, hft, hr⟩
        refine ⟨et.liftN 0, B.liftN 0, by simp [hft, VLocalDecl.depth], ?_⟩
        show r.expr (e.liftN 0) = _
        rw [← InductiveSignature.Restoration.expr_liftN r hc, hr]
        rfl

theorem restoration_expr_app {r : Restoration} {f a f' a' : VExpr}
    (hf : r.expr f = some f') (ha : r.expr a = some a') :
    r.expr (.app f a) = some (.app f' a') := by
  have := InductiveSignature.Restoration.expr.go_append r f (args₀ := []) hf [a']
  simp only [Restoration.expr] at ha ⊢
  simpa [Restoration.expr.go, ha, VExpr.mkApps] using this

theorem restoration_expr_lam {r : Restoration} {d b d' b' : VExpr}
    (hd : r.expr d = some d') (hb : r.expr b = some b') :
    r.expr (.lam d b) = some (.lam d' b') := by
  simp only [Restoration.expr] at hd hb ⊢
  simp [Restoration.expr.go, hd, hb, VExpr.mkApps]

theorem restoration_expr_forallE {r : Restoration} {d b d' b' : VExpr}
    (hd : r.expr d = some d') (hb : r.expr b = some b') :
    r.expr (.forallE d b) = some (.forallE d' b') := by
  simp only [Restoration.expr] at hd hb ⊢
  simp [Restoration.expr.go, hd, hb, VExpr.mkApps]

theorem restoration_expr_proj {r : Restoration} {s : Name} {i : Nat} {e e' : VExpr}
    (he : r.expr e = some e') :
    r.expr (.proj s i e) = some (.proj s i e') := by
  simp only [Restoration.expr] at he ⊢
  simp [Restoration.expr.go, he, VExpr.mkApps]

/-- **Untraversed syntax.** Two translations, in related contexts, of an
expression avoiding the restorable names agree up to restoration. This
covers the trailing arguments of a head occurrence, which the executable copies
verbatim. -/
theorem RestoreCtxRel.translate_avoids {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {envS envT : VEnv} {Us : List Name} {Δs Δt : VLCtx} {e : Expr} {s t : VExpr}
    (Hctx : RestoreCtxRel r Δs Δt) (Havoid : e.AvoidsConsts r.restorableNames)
    (Hs : TrExprS envS Us Δs e s) (Ht : TrExprS envT Us Δt e t) : r.expr s = some t := by
  induction Hs generalizing Δt t with
  | bvar h =>
    cases Ht with
    | bvar h' =>
      rcases Hctx.find? hc h with ⟨et, B, hf, hr⟩
      rw [hf] at h'; cases h'; exact hr
  | fvar h =>
    cases Ht with
    | fvar h' =>
      rcases Hctx.find? hc h with ⟨et, B, hf, hr⟩
      rw [hf] at h'; cases h'; exact hr
  | sort h =>
    cases Ht with
    | sort h' => cases h.symm.trans h'; rfl
  | const _ h _ =>
    cases Ht with
    | const _ h' _ =>
      cases h.symm.trans h'
      cases Havoid with
      | const _ _ hfresh =>
        simp only [Restoration.restorableNames, List.mem_append, not_or] at hfresh
        simp [Restoration.expr, Restoration.expr.go,
          Restoration.heads_find?_eq_none hfresh.1,
          Restoration.recursorName_of_not_mem hfresh.2, VExpr.mkApps]
  | app _ _ _ _ ihf iha =>
    cases Ht with
    | app _ _ hf ha =>
      cases Havoid with
      | app _ _ Hf Ha => exact restoration_expr_app (ihf Hctx Hf hf) (iha Hctx Ha ha)
  | lam _ _ _ ihd ihb =>
    cases Ht with
    | lam _ hd hb =>
      cases Havoid with
      | lam _ _ _ _ Hd Hb =>
        exact restoration_expr_lam (ihd Hctx Hd hd) (ihb Hctx.vlam Hb hb)
  | forallE _ _ _ _ ihd ihb =>
    cases Ht with
    | forallE _ _ hd hb =>
      cases Havoid with
      | forallE _ _ _ _ Hd Hb =>
        exact restoration_expr_forallE (ihd Hctx Hd hd) (ihb Hctx.vlam Hb hb)
  | letE _ _ _ _ _ ihv ihb =>
    cases Ht with
    | letE _ _ hv hb =>
      cases Havoid with
      | letE _ _ _ _ _ _ Hv Hb => exact ihb (Hctx.vlet (ihv Hctx Hv hv)) Hb hb
  | lit _ _ ih =>
    cases Ht with
    | lit _ h =>
      cases Havoid with
      | lit _ Ha => exact ih Hctx Ha h
  | mdata _ ih =>
    cases Ht with
    | mdata h =>
      cases Havoid with
      | mdata _ _ Ha => exact ih Hctx Ha h
  | proj _ hp ih =>
    cases Ht with
    | proj h hp' =>
      cases Havoid with
      | proj _ _ _ Ha =>
        exact restoration_expr_proj (ih Hctx Ha h)

theorem RestoreCtxRel.translate_avoids_forall₂ {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {envS envT : VEnv} {Us : List Name} {Δs Δt : VLCtx} (Hctx : RestoreCtxRel r Δs Δt) :
    ∀ {es : List Expr} {ss ts : List VExpr}, (∀ e ∈ es, e.AvoidsConsts r.restorableNames) →
      List.Forall₂ (TrExprS envS Us Δs) es ss → List.Forall₂ (TrExprS envT Us Δt) es ts →
      List.Forall₂ (fun x y => Restoration.expr.go r x [] = some y) ss ts
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _, ha, .cons hs ts, .cons ht tt =>
    .cons (Hctx.translate_avoids hc (ha _ List.mem_cons_self) hs ht)
      (RestoreCtxRel.translate_avoids_forall₂ hc Hctx
        (fun e he => ha e (List.mem_cons_of_mem _ he)) ts tt)

/-- The opened parameters (free variables) translate in the restored context
to the restorations of their source translations. -/
theorem RestoreCtxRel.translate_fvars {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {envS envT : VEnv} {Us : List Name} {Δs Δt : VLCtx} (Hctx : RestoreCtxRel r Δs Δt) :
    ∀ {as : List Expr} {ps : List VExpr}, (∀ a ∈ as, ∃ fv, a = .fvar fv) →
      List.Forall₂ (TrExprS envS Us Δs) as ps →
      ∃ qs, List.Forall₂ (TrExprS envT Us Δt) as qs ∧
        List.Forall₂ (fun x y => Restoration.expr.go r x [] = some y) ps qs
  | _, _, _, .nil => ⟨[], .nil, .nil⟩
  | _, _, has, .cons h t => by
    obtain ⟨fv, rfl⟩ := has _ List.mem_cons_self
    obtain ⟨qs, hq, hr⟩ := RestoreCtxRel.translate_fvars hc Hctx
      (fun a ha => has a (List.mem_cons_of_mem _ ha)) t
    cases h with
    | fvar hf =>
      obtain ⟨et, B, hft, hre⟩ := Hctx.find? hc hf
      exact ⟨et :: qs, .cons (.fvar hft) hq, .cons hre hr⟩

/-- Under the agreement, the executable replacement heads are exactly the
abstract restoration heads, for every parameter array. -/
theorem RestorationMapAgreement.restoreHead_ne_none_iff
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {targetEnv : VEnv} {Us : List Name} {auxLevels : List Level}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (As : Array Expr) (c : Name) :
    restoreHead result env As c ≠ none ↔ c ∈ r.heads.map (·.auxiliary) := by
  constructor
  · intro hne
    rcases Option.ne_none_iff_exists.mp hne with ⟨H, hH⟩
    rcases A.head As c H hH.symm with ⟨h, hh, _⟩
    exact List.mem_map.mpr ⟨h, List.mem_of_find?_eq_some hh,
      by simpa using List.find?_some hh⟩
  · intro hmem hnone
    exact A.headNone As c hnone hmem

theorem RestorationMapAgreement.restoreHead_eq_none
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {targetEnv : VEnv} {Us : List Name} {auxLevels : List Level}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    {As : Array Expr} {c : Name} (h : c ∉ r.heads.map (·.auxiliary)) :
    restoreHead result env As c = none := by
  by_contra hne
  exact h ((A.restoreHead_ne_none_iff As c).mp hne)

/-- The head-occurrence case of `restorationCommutes`: a node whose application head is
a restoration head. -/
theorem restorationCommutes'_paramUniform
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    (Hfresh : ∀ n ∈ r.restorableNames, targetEnv.constants n = none)
    {e : Expr} {c : Name} {us : List Level} {Δs Δt : VLCtx} {s t : VExpr}
    (hfn : e.getAppFn = .const c us) (hmem : c ∈ r.heads.map (·.auxiliary))
    (Hshape : e.ParamUniform (r.heads.map (·.auxiliary)) As.toList auxLevels)
    (Hctx : RestoreCtxRel r Δs Δt)
    (Hs : TrExprS sourceEnv Us Δs e s)
    (Ht : TrExprS targetEnv Us Δt (e.replace (result.restoreNestedNode env As auxRec)) t) :
    r.expr s = some t := by
  obtain ⟨hus, rest, hargs, -⟩ := Hshape.getAppFn_const_head_inv hfn hmem
  subst us
  have hhead : restoreHead result env As c ≠ none :=
    (A.restoreHead_ne_none_iff As c).mpr hmem
  rcases Option.ne_none_iff_exists.mp hhead with ⟨H, hH⟩
  have hH := hH.symm
  have hnotrec := A.notRecursor_of_head hhead
  have hAsLen : As.toList.length = result.nparams := by simpa using hsize
  have hnode := restoreNestedNode_eq_of_restoreHead result env As auxRec e
    (fun c' ls' heq => by subst heq; cases hfn; exact hnotrec) hfn hH
    (by rw [hargs]; simp [hAsLen])
  rw [Expr.replace_of_some hnode, hargs, ← hAsLen, List.drop_left] at Ht
  have he : e = Expr.mkAppList (.const c auxLevels) (As.toList ++ rest) := by
    rw [← hargs, ← hfn, Expr.mkAppList_getAppArgsList]
  subst he
  rcases checkPositivityStep.TrExprS.mkAppList_inv Hs with ⟨fn', L', hfn', hL', rfl⟩
  cases hfn' with
  | const _ hlsV _ =>
  obtain ⟨P', R'', rfl, hP', hR''⟩ := List.Forall₂.append_inv hL'
  rcases checkPositivityStep.TrExprS.mkAppList_inv Ht with ⟨Hv, R', hHv, hR', rfl⟩
  rcases A.head As c H hH with ⟨h, hfind, hnparams, hlevels⟩
  rcases hlevels _ hlsV with ⟨huvars, hsem⟩
  obtain ⟨PT, hPT, hPr⟩ := Hctx.translate_fvars hc HAs hP'
  have hHvEq := hsem Δt PT Hv HAs hsize hPT hHv
  subst hHvEq
  have hrest : ∀ a ∈ rest, a.AvoidsConsts r.restorableNames := by
    intro a ha
    obtain ⟨b, -, hab⟩ := Lean4Lean.List.Forall₂.forall_exists_l hR' a ha
    exact checkPositivityStep.TrExprS.sourceAvoidsFresh Hfresh hab
  have hRr := Hctx.translate_avoids_forall₂ hc hrest hR'' hR'
  have hPTlen : PT.length = result.nparams := by
    rw [← Lean4Lean.List.Forall₂.length_eq hPT, hAsLen]
  simp only [Restoration.expr]
  rw [Restoration.expr.go_mkApps r (List.Forall₂.append' hPr hRr), List.append_nil]
  have hle : h.nparams ≤ (PT ++ R').length := by simp [hnparams, hPTlen]
  simp [Restoration.expr.go, hfind, HeadSpecialization.apply, huvars, hnparams, hPTlen,
    Lean4Lean.VExpr.mkApps_append]

/-- **Commutation of executable restoration with `Restoration.expr`** on an
opened body `e`, under the parameter-uniformity condition. `e` is traversed by
`Expr.replace` with `restoreNestedNode` over the opened parameters `As`; its
translation `s` (in any environment) and any translation `t` of the
executable output in an environment `targetEnv` lacking the restorable names
are related by `r.expr s = some t`, in related contexts. -/
theorem restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    (Hfresh : ∀ n ∈ r.restorableNames, targetEnv.constants n = none)
    {e : Expr} {Δs Δt : VLCtx} {s t : VExpr}
    (Hshape : e.ParamUniform (r.heads.map (·.auxiliary)) As.toList auxLevels)
    (Hctx : RestoreCtxRel r Δs Δt)
    (Hs : TrExprS sourceEnv Us Δs e s)
    (Ht : TrExprS targetEnv Us Δt (e.replace (result.restoreNestedNode env As auxRec)) t) :
    r.expr s = some t := by
  -- a node whose head is not an application of a constant is never replaced
  have hmiss : ∀ x : Expr, (∀ c us, x ≠ .const c us) → (∀ c us, x.getAppFn ≠ .const c us) →
      result.restoreNestedNode env As auxRec x = none := fun x h1 h2 =>
    restoreNestedNode_eq_none_of_restoreHead result env As auxRec x
      (fun c us h => absurd h (h1 c us)) (fun c us h => absurd h (h2 c us))
  induction Hs generalizing Δt t with
  | bvar h =>
    rw [Expr.replace_bvar_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | bvar h' =>
      rcases Hctx.find? hc h with ⟨et, B, hf, hr⟩
      rw [hf] at h'; cases h'; exact hr
  | fvar h =>
    rw [Expr.replace_fvar_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | fvar h' =>
      rcases Hctx.find? hc h with ⟨et, B, hf, hr⟩
      rw [hf] at h'; cases h'; exact hr
  | sort h =>
    rw [Expr.replace_sort_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | sort h' => cases h.symm.trans h'; rfl
  | @const c _ _ _ us hcs hls hlen =>
    by_cases hmem : c ∈ r.heads.map (·.auxiliary)
    · exact restorationCommutes'_paramUniform A hc HAs hsize Hfresh rfl hmem Hshape Hctx
        (.const hcs hls hlen) Ht
    · have hnone := A.restoreHead_eq_none (As := As) hmem
      cases hrec : auxRec.find? c with
      | some new =>
        rw [Expr.replace_of_some (restoreNestedNode_recursor result env As auxRec c new us
          hrec)] at Ht
        cases Ht with
        | const _ hls' _ =>
          cases hls.symm.trans hls'
          simp only [Restoration.expr]
          rw [A.go_const (As := As) hnone]
          simp [hrec, VExpr.mkApps]
      | none =>
        rw [Expr.replace_const_of_none (restoreNestedNode_eq_none_of_restoreHead result env
          As auxRec _ (fun c' ls' heq => by cases heq; exact hrec)
          (fun c' ls' h => by
            simp only [Expr.getAppFn, Expr.const.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact hnone))] at Ht
        cases Ht with
        | const _ hls' _ =>
          cases hls.symm.trans hls'
          simp only [Restoration.expr]
          rw [A.go_const (As := As) hnone]
          simp [hrec, VExpr.mkApps]
  | @app _ _ _ _ _ f a h1 h2 hf ha ihf iha =>
    by_cases hhit : ∃ c us, (Expr.app f a).getAppFn = .const c us ∧
        c ∈ r.heads.map (·.auxiliary)
    · obtain ⟨c, us, hfn, hmem⟩ := hhit
      exact restorationCommutes'_paramUniform A hc HAs hsize Hfresh hfn hmem Hshape Hctx
        (.app h1 h2 hf ha) Ht
    · have hnot : ∀ c us, f.getAppFn = .const c us → c ∉ r.heads.map (·.auxiliary) :=
        fun c us hfn hmem => hhit ⟨c, us, by simpa [Expr.getAppFn] using hfn, hmem⟩
      obtain ⟨Hf, Ha⟩ := Hshape.app_inv hnot
      have hnone : result.restoreNestedNode env As auxRec (.app f a) = none :=
        restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
          (by intro _ _ h; cases h)
          (fun c us hfn => A.restoreHead_eq_none
            (hnot c us (by simpa [Expr.getAppFn] using hfn)))
      rw [Expr.replace_app_of_none hnone] at Ht
      cases Ht with
      | app _ _ htf hta => exact restoration_expr_app (ihf Hf Hctx htf) (iha Ha Hctx hta)
  | lam _ _ _ ihd ihb =>
    obtain ⟨Hd, Hb⟩ := Hshape.lam_inv
    rw [Expr.replace_lam_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | lam _ htd htb => exact restoration_expr_lam (ihd Hd Hctx htd) (ihb Hb Hctx.vlam htb)
  | forallE _ _ _ _ ihd ihb =>
    obtain ⟨Hd, Hb⟩ := Hshape.forallE_inv
    rw [Expr.replace_forallE_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | forallE _ _ htd htb =>
      exact restoration_expr_forallE (ihd Hd Hctx htd) (ihb Hb Hctx.vlam htb)
  | letE _ _ _ _ _ ihv ihb =>
    obtain ⟨-, Hv, Hb⟩ := Hshape.letE_inv
    rw [Expr.replace_letE_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | letE _ _ htv htb => exact ihb Hb (Hctx.vlet (ihv Hv Hctx htv)) htb
  | lit _ hs _ =>
    rw [Expr.replace_lit_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    have Havoid := checkPositivityStep.TrExprS.sourceAvoidsFresh Hfresh Ht
    cases Ht with
    | lit _ ht =>
      cases Havoid with
      | lit _ Ha => exact Hctx.translate_avoids hc Ha hs ht
  | mdata _ ih =>
    have He := Hshape.mdata_inv
    rw [Expr.replace_mdata_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | mdata ht => exact ih He Hctx ht
  | proj _ hp ih =>
    have He := Hshape.proj_inv
    rw [Expr.replace_proj_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))] at Ht
    cases Ht with
    | proj ht hp' =>
      exact restoration_expr_proj (ih He Hctx ht)

/-! ### Closed telescopes -/

theorem restoration_expr_wrapForalls {r : Restoration} :
    ∀ {D₁ D₂ : List VExpr}, List.Forall₂ (fun x y => r.expr x = some y) D₁ D₂ →
      ∀ {body body' : VExpr}, r.expr body = some body' →
        r.expr (VExpr.wrapForalls D₁ body) = some (VExpr.wrapForalls D₂ body')
  | _, _, .nil, _, _, h => by simpa [VExpr.wrapForalls] using h
  | _, _, .cons hd t, _, _, h => by
    have := restoration_expr_wrapForalls t h
    simp only [VExpr.wrapForalls, List.foldr_cons] at this ⊢
    exact restoration_expr_forallE hd this

/-- The unchanged parameter prefix of a restoration: the translated domains
of the input and of the output are related by restoration, because the output
domains translate in an environment lacking the restorable names. -/
theorem Expr.SameForallPrefix.translatedDomains_restore {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {envS envT : VEnv} {Us : List Name}
    (Hfresh : ∀ n ∈ r.restorableNames, envT.constants n = none)
    {n : Nat} {left right : Expr} (Hsame : Expr.SameForallPrefix n left right) :
    ∀ {Δ₁ Δ₂ : VLCtx} {D₁ D₂ : List VExpr} {X₁ X₂ : VExpr},
      RestoreCtxRel r Δ₁ Δ₂ →
      TrExprS envS Us Δ₁ left (VExpr.wrapForalls D₁ X₁) →
      TrExprS envT Us Δ₂ right (VExpr.wrapForalls D₂ X₂) →
      D₁.length = n → D₂.length = n →
      List.Forall₂ (fun x y => r.expr x = some y) D₁ D₂ := by
  induction Hsame with
  | nil =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ _ _ _ h₁ h₂
    rw [List.eq_nil_of_length_eq_zero h₁, List.eq_nil_of_length_eq_zero h₂]
    exact .nil
  | cons _ ih =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ Hctx H₁ H₂ h₁ h₂
    cases D₁ with
    | nil => simp at h₁
    | cons d₁ D₁ =>
    cases D₂ with
    | nil => simp at h₂
    | cons d₂ D₂ =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at H₁ H₂
    cases H₁ with
    | forallE _ _ hd₁ hb₁ =>
    cases H₂ with
    | forallE _ _ hd₂ hb₂ =>
    exact .cons
      (Hctx.translate_avoids hc (checkPositivityStep.TrExprS.sourceAvoidsFresh Hfresh hd₂)
        hd₁ hd₂)
      (ih Hctx.vlam hb₁ hb₂ (by simpa using h₁) (by simpa using h₂))

theorem fvarIdsIn_of_trExprS_abstractForallContext
    {env : VEnv} {Us : List Name} {domains : List VExpr} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us (abstractForallContext domains []) e e') (P : FVarId → Prop) :
    e.FVarIdsIn P := by
  apply FVarsIn_to_FVarIdsIn
  apply H.fvarsIn.mono
  intro fv hfv
  simp [abstractForallContext, VLCtx.fvars] at hfv

/-- A forall telescope stripped by `LeadingBinders` is the telescope's
residual. -/
theorem Expr.ForallTelescope.leadingBinders_eq {e suffix body : Expr} {n : Nat}
    (Htel : Expr.ForallTelescope e n suffix) (Hlead : Expr.LeadingBinders n e body) :
    body = suffix := by
  induction Htel generalizing body with
  | nil => cases Hlead; rfl
  | cons _ ih => cases Hlead with | forallE Hb => exact ih Hb

/-- **Parameter uniformity of every opening** of a stored term whose parameter
telescope is parameter-uniform in bound-variable form. -/
theorem NestedRestorationOpening.paramUniform_of_lowered
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {heads : List Name} {auxLevels : List Level}
    {input output suffix : Expr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hshape : Expr.ParamUniformTele heads result.nparams auxLevels input) :
    Hopen.body.ParamUniform heads Hopen.params.toList auxLevels ∧
      Hopen.params.size = result.nparams ∧
      ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
  rcases Hopen.opening.forallResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have hparams : Hopen.params.toList = fvars.map Expr.fvar := by simpa using hAs
  obtain ⟨body, Hlead, HB⟩ := Hshape
  cases Htel.leadingBinders_eq Hlead
  refine ⟨?_, by rw [← Array.length_toList, hparams, List.length_map, hlen], ?_⟩
  · rw [hbody, hparams]
    rw [← hlen] at HB
    exact HB.instantiateRevList_fvars
  · intro a ha
    rw [hparams] at ha
    rcases List.mem_map.mp ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩

/-- **Closed-term commutation for forall telescopes** under the parameter-uniformity
condition (generated recursor and constructor types). -/
theorem NestedRestorationOpening.restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input output suffix : Expr}
    {s t : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hfresh : ∀ n ∈ r.restorableNames, targetEnv.constants n = none)
    (Hshape : Hopen.body.ParamUniform (r.heads.map (·.auxiliary)) Hopen.params.toList auxLevels)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input)
    (hrestored : Closed Hopen.restoredBody)
    (Hs : TrExprS sourceEnv Us [] input s) (Ht : TrExprS targetEnv Us [] output t) :
    r.expr s = some t := by
  have hnodup := Hopen.selectionNodup
  have hlen : Hopen.selection.fvars.length = result.nparams :=
    Hopen.selection.size.symm.trans Hopen.opening.initial_size
  have hparams := Hopen.selection.expressions
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    simp at ha
    rcases ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := by
    rw [hparams]; simpa using hlen
  rcases Hopen.opening.forallResidualData Htel with ⟨fvars', hAs, _, hbody⟩
  have hfvars : fvars'.map Expr.fvar = Hopen.selection.fvars.map Expr.fvar := by
    have h1 : Hopen.params.toList = Hopen.selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList hparams
    rw [h1] at hAs
    simpa using hAs.symm
  rw [hfvars] at hbody
  rcases TrExprS.forallTelescope_shape_with_context Htel Hs with
    ⟨Ds, sR, hDs, rfl, HsR⟩
  have HbodyS := TrExprS.instantiateRevFVars Hopen.selection.fvars Ds [] suffix sR
    (hlen.trans hDs.symm) hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext HsR _) HsR
  rw [← hbody, List.append_nil] at HbodyS
  rcases TrExprS.forallTelescope_shape_with_context
      (Hopen.outputPrefixTelescope Htel) Ht with ⟨Dt, tR, hDt, rfl, HtR⟩
  rw [Expr.abstractN_eq_abstractList_of_closed hnodup hrestored] at HtR
  have HbodyT := TrExprS.instantiateRevFVars Hopen.selection.fvars Dt [] _ tR
    (hlen.trans hDt.symm) hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext HtR _) HtR
  rw [TypeChecker.Expr.abstractList_instantiateRevList_eq_self hnodup hrestored,
    List.append_nil, Hopen.replacement.eq_replace] at HbodyT
  have Hbody := _root_.Lean4Lean.VerifyInductive.restorationCommutes A hc HAs hsize Hfresh Hshape
    (fvarScope_vlamShape _ Ds Dt (hDs.trans hDt.symm)).restoreCtxRel HbodyS HbodyT
  have Hsame := Hopen.sameForallPrefix Htel (FVarsIn_to_FVarIdsIn Hinput) hclosed
  exact restoration_expr_wrapForalls
    (Hsame.translatedDomains_restore hc Hfresh .nil Hs Ht hDs hDt) Hbody

/-- `restoreNested` form of `NestedRestorationOpening.restorationCommutes`,
from the bound-variable parameter uniformity of the stored input. -/
theorem NestedRestoration.restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input output suffix : Expr}
    {s t : VExpr}
    (H : NestedRestoration result env auxRec input output)
    (hparams : result.params.size = result.nparams)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hfresh : ∀ n ∈ r.restorableNames, targetEnv.constants n = none)
    (Hshape : Expr.ParamUniformTele (r.heads.map (·.auxiliary)) result.nparams auxLevels input)
    (Hclosed : ∀ Hopen : NestedRestorationOpening result env auxRec input output,
      Closed Hopen.restoredBody)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input)
    (Hs : TrExprS sourceEnv Us [] input s) (Ht : TrExprS targetEnv Us [] output t) :
    r.expr s = some t := by
  rcases H.opening hparams with ⟨Hopen⟩
  exact Hopen.restorationCommutes A hc Hfresh (Hopen.paramUniform_of_lowered Htel Hshape).1
    Htel Hinput hclosed (Hclosed Hopen) Hs Ht

/-- The restored recursor type is the abstract restoration of the lowered
recursor type, under the parameter-uniformity condition. -/
theorem RecursorRestoration.typeRestorationCommutes
    {r : Restoration} {auxLevels : List Level} {sourceEnv targetEnv : VEnv}
    {suffix : Expr} {s t : VExpr}
    (H : RecursorRestoration result env auxRec allIndNames oldRecName newRecName
      oldInfo newInfo)
    (hparams : result.params.size = result.nparams)
    (A : RestorationMapAgreement r result env auxRec targetEnv oldInfo.levelParams
      auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hfresh : ∀ n ∈ r.restorableNames, targetEnv.constants n = none)
    (Hshape : Expr.ParamUniformTele (r.heads.map (·.auxiliary)) result.nparams auxLevels
      oldInfo.type)
    (Hclosed : ∀ Hopen : NestedRestorationOpening result env auxRec oldInfo.type
        newInfo.type, Closed Hopen.restoredBody)
    (Htel : Expr.ForallTelescope oldInfo.type result.nparams suffix)
    (Hinput : oldInfo.type.FVarsIn fun _ => False) (hclosed : Closed oldInfo.type)
    (Hs : TrExprS sourceEnv oldInfo.levelParams [] oldInfo.type s)
    (Ht : TrExprS targetEnv newInfo.levelParams [] newInfo.type t) :
    r.expr s = some t := by
  rw [H.levelParams] at Ht
  exact H.type.restorationCommutes hparams A hc Hfresh Hshape Hclosed Htel Hinput hclosed
    Hs Ht

/-! ### Whole rule right-hand sides -/

end VerifyInductive
end Lean4Lean
