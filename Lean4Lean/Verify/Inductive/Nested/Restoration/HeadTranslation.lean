import Lean4Lean.Verify.Inductive.Nested.Restoration.TranslationPreservation
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement

/-! # Translation of the executable replacement heads

`restorationTranslates` (`Nested/Restoration/TranslationPreservation.lean`) takes the
hypothesis `RestoreHeadsTranslate`: at every context lifting the base context
of the opened parameters by bound binders, each executable replacement head
(`restoreHead`) is a constant applied to arguments that translate to the
abstract specialisation of the matching restoration head. This file discharges
it from the restoration tables (`RestorationTablesAgree`) and a translation of
each recorded container application in the target environment.

The existence of the translations is transported from the abstracted
parameter telescope to the opened one (`TrExprS.instantiateRevFVars`), across
a definitionally equal context (`TrExprS.defeqDFC`), up to dependency lists
(`TrExprS.sameUpToDeps`) and through the bound-binder lift (`TrExprS.weakBV`,
the opened arguments being closed). The values are then fixed by
`TrExprS.instantiateRevList_inv`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature (Restoration HeadSpecialization instantiateParams)

namespace VerifyInductive

private theorem find?_auxiliary_of_nodup {l : List InductiveSignature.HeadSpecialization}
    (hnodup : (l.map (·.auxiliary)).Nodup) {x : InductiveSignature.HeadSpecialization}
    (hx : x ∈ l) : l.find? (fun y => y.auxiliary == x.auxiliary) = some x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : y.auxiliary ≠ x.auxiliary := fun h => hnodup.1 ⟨x, hx, h.symm⟩
      simp [hne, ih hnodup.2 hx]

/-- Pointwise existence of translations, with values fixed by the inversion
lemma, assembles into the abstract specialisation of the arguments. -/
private theorem forall₂_instantiate_of_exists {envS env : VEnv} {Us₀ Us : List Name}
    {ls : List VLevel}
    (hls : (Us₀.map Level.param).mapM (VLevel.ofLevel Us) = some ls)
    {As : List Expr} {params : List VExpr} {Δ : VLCtx}
    (hAs : ∀ a ∈ As, ∃ fv, a = .fvar fv)
    (hTr : List.Forall₂ (TrExprS env Us Δ) As params)
    {domains : List VExpr} (hdomains : domains.length = As.length) :
    ∀ {Ys : List Expr} {args : List VExpr},
      List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys args →
      (∀ Y ∈ Ys, ∃ v, TrExprS env Us Δ (Y.instantiateRevList As 0) v) →
      List.Forall₂ (TrExprS env Us Δ) (Ys.map (·.instantiateRevList As 0))
        (args.map fun arg => instantiateParams (arg.instL ls) params)
  | [], [], .nil, _ => .nil
  | Y :: _, _ :: _, .cons h₁ t₁, hex => by
    obtain ⟨v, hv⟩ := hex Y List.mem_cons_self
    have heq := TrExprS.instantiateRevList_inv hls hAs hTr h₁ (.base hdomains) hv
    subst heq
    exact .cons hv (forall₂_instantiate_of_exists hls hAs hTr hdomains t₁
      fun Y' hY' => hex Y' (List.mem_cons_of_mem _ hY'))

/-- The opened arguments of a recorded container application translate in
every bound-binder lift of the base context. -/
private theorem reopenedArgs_translate {result : Lean4Lean.ElimNestedInductive.Result}
    {envT : VEnv} (hT : envT.WF) {Us : List Name}
    {doms : List VExpr} (hdoms : doms.length = result.nparams)
    {Ys : List Expr}
    (HY : ∀ Y ∈ Ys, ∃ v, TrExprS envT Us (abstractForallContext doms []) Y v)
    {ats : List FVarId}
    (hclosed : ∀ Y ∈ Ys, Closed (Y.instantiateRevList (ats.map Expr.fvar) 0))
    (hnodup : ats.Nodup) (hlen : ats.length = result.nparams)
    {Dt : List VExpr}
    (hΔ : VLCtx.IsDefEq envT Us.length (fvarScope ats doms) (fvarScope ats Dt))
    {Δt0 : VLCtx} (hsame : VLCtx.SameUpToDeps (fvarScope ats Dt) Δt0)
    {Δt : VLCtx} {dn n : Nat} (hlift : VLCtx.BVLift Δt0 Δt dn 0 n 0) :
    ∀ Y ∈ Ys, ∃ v, TrExprS envT Us Δt (Y.instantiateRevList (ats.map Expr.fvar) 0) v := by
  intro Y hY
  obtain ⟨_, hY'⟩ := HY Y hY
  have hfresh : Y.FVarIdsIn (· ∉ ats) := by
    have h := FVarsIn_to_FVarIdsIn hY'.fvarsIn
    refine Expr.FVarIdsIn.mono h ?_
    intro fv hfv
    rw [abstractForallContext_fvars] at hfv
    simp [VLCtx.fvars] at hfv
  have H1 := TrExprS.instantiateRevFVars ats doms [] Y _ (hlen.trans hdoms.symm) hnodup
    hfresh hY'
  rw [List.append_nil] at H1
  obtain ⟨_, H2⟩ := H1.defeqDFC hT hΔ
  have H3 := (VerifyInductive.TrExprS.sameUpToDeps H2 hsame).weakBV hT.ordered hlift
  rw [Expr.liftLooseBVars_eq_self (hclosed Y hY).looseBVarRange_le] at H3
  exact ⟨_, H3⟩

open _root_.Lean4Lean.InductiveSignature (compilationRestoration
  compilationRestoration_heads_auxiliary) in
/-- **The executable replacement heads translate** to the abstract
specialisations of `compilationRestoration`, at every bound-binder lift of a
base context in which the opened parameters live. -/
theorem RestorationTablesAgree.restoreHeadsTranslate
    {decl : VInductDecl} {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ Us : List Name}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    {envT : VEnv} (hT : envT.WF)
    {ats : List FVarId} {Dt : List VExpr}
    (Hval : ∀ name nested, result.aux2nested.find? name = some nested →
      ∀ (c : Name) (lvls : List Level) (Ys : List Expr),
        nested.abstract result.params = Expr.mkAppList (.const c lvls) Ys →
      ∃ doms : List VExpr, doms.length = result.nparams ∧
        (∀ Y ∈ Ys, ∃ v, TrExprS envT Us (abstractForallContext doms []) Y v) ∧
        VLCtx.IsDefEq envT Us.length (fvarScope ats doms) (fvarScope ats Dt))
    (Hconsts : ∀ a ∈ auxiliaries,
      (∃ ci, envT.constants a.source.name = some ci ∧ ci.uvars = a.levels.length) ∧
      ∀ ctor ∈ a.source.ctors, ∃ ci, envT.constants ctor.name = some ci ∧
        ci.uvars = a.levels.length)
    (hnodup : ats.Nodup) (hlen : ats.length = result.nparams)
    {Δt0 : VLCtx} (hsame : VLCtx.SameUpToDeps (fvarScope ats Dt) Δt0) :
    RestoreHeadsTranslate (InductiveSignature.compilationRestoration decl auxiliaries) result
      env envT Us (Us₀.map Level.param) ⟨ats.map .fvar⟩ Δt0 := by
  have hheadsNodup :
      ((compilationRestoration decl auxiliaries).heads.map (·.auxiliary)).Nodup := by
    rw [compilationRestoration_heads_auxiliary]
    exact D.headNodup
  have hrename : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      (a.constructorName ctor).replacePrefix a.auxiliary a.source.name = ctor.name :=
    fun a ha ctor hctor =>
      (namePrefix_of_replacePrefix_ne (D.ctorRenamed a ha ctor hctor)).replacePrefix_replacePrefix _
  have hAs : ∀ a ∈ (⟨ats.map .fvar⟩ : Array Expr).toList, ∃ fv, a = .fvar fv := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨fv, _, rfl⟩ := ha
    exact ⟨fv, rfl⟩
  have hsize : (⟨ats.map .fvar⟩ : Array Expr).size = result.nparams := by
    simp [hlen]
  intro Δt dn n hlift c H hH h hh levels hlevels PT hPT
  /- The common tail: the head constant `target` applied to the reopened arguments. -/
  have key : ∀ (a : InductiveSignature.ContainerSpecialization) (nested : Expr)
      (target : Name) (envS : VEnv) (domains : List VExpr) (lvls : List Level)
      (Ys : List Expr), result.aux2nested.find? a.auxiliary = some nested →
      domains.length = result.nparams →
      nested.abstract result.params = Expr.mkAppList (.const a.source.name lvls) Ys →
      lvls.mapM (VLevel.ofLevel Us₀) = some a.levels →
      List.Forall₂ (TrExprS envS Us₀ (abstractForallContext domains [])) Ys a.arguments →
      (∃ ci, envT.constants target = some ci ∧ ci.uvars = a.levels.length) →
      TrExprS envT Us Δt (.const target lvls)
          (.const target (a.levels.map (·.inst levels))) ∧
        List.Forall₂ (TrExprS envT Us Δt) (Ys.map (·.instantiateRevList (ats.map .fvar) 0))
          (a.arguments.map fun arg => instantiateParams (arg.instL levels) PT) := by
    intro a nested target envS domains lvls Ys hn hdom hab hlvls hYs ⟨ci, hci, huv⟩
    refine ⟨.const hci (VLevel.mapM_ofLevel_reindex hlevels hlvls) ?_, ?_⟩
    · rw [huv]
      exact Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlvls)
    · have hclosed := AuxiliaryContainerApp.reopen_closed hdom hYs hAs hsize
      exact forall₂_instantiate_of_exists hlevels hAs hPT
        (by simp [hdom, hlen]) hYs
        (by
          obtain ⟨doms, hdoms, HY, hΔ⟩ := Hval _ nested hn _ _ _ hab
          exact reopenedArgs_translate hT hdoms HY hclosed hnodup hlen hΔ
            hsame hlift)
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
    rw [find?_auxiliary_of_nodup hheadsNodup hmem] at hh
    cases hh
    obtain ⟨hfn, hargs⟩ := key a nested a.source.name envS domains lvls Ys hfind hdom hab
      hlvls hYs (Hconsts a ha).1
    exact ⟨_, _, AuxiliaryContainerApp.reopen hab _, hfn, hargs⟩
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
      rw [find?_auxiliary_of_nodup hheadsNodup hmem] at hh
      cases hh
      rw [← hauxEq] at hn
      obtain ⟨hfn, hargs⟩ := key a nested ctor.name envS domains lvls Ys hn hdom hab
        hlvls hYs ((Hconsts a ha).2 ctor hctor)
      refine ⟨_, _, ?_, hfn, hargs⟩
      rw [Expr.getAppArgs_eq, Expr.getAppArgsList_mkAppList_const,
        Expr.mkAppN_eq_mkAppList, ← hauxEq, hrename a ha ctor hctor]

end VerifyInductive
end Lean4Lean
