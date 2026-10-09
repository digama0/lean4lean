import Lean4Lean.Verify.Inductive.Nested.Restoration.CommutationUniform
import Lean4Lean.Theory.Inductive.RestorationInterpretation

/-! # Restoration preserves translation

`restorationCommutes` (`Nested/Restoration/CommutationUniform.lean`) shows that a
translation of the executable restoration of a lowered term, if one exists, is
the abstract restoration of the lowered translation. This file proves that one
exists: restoration preserves translation, typing side conditions included.

The lowered term is translated in a lowered environment `envL`; a
restoration substitution (`r.Substitution envT envL I`) transports every
typing judgment of `envL` along the interpretation `I` to the target environment
`envT`, and beta subject reduction of `envT` identifies `I.expr` with
the restoration `r.expr` at every type (`Restoration.Substitution.expr_simAt`). Each typing side
condition of the lowered translation is transported in this way
(`RestoreTypedCtx.hasType`), along a context invariant relating the two
translation contexts (`RestoreTypedCtx`).

* `translate_avoids_exists`: syntax avoiding the restorable names translates in
  `envT` to the restoration of its lowered translation (the trailing arguments
  of a head occurrence, which the executable copies verbatim, and literals).
* `restorationTranslates`: the opened body of a lowered term, traversed by
  `Expr.replace` with `restoreNestedNode`, translates in `envT` to the
  restoration of its lowered translation. At a head occurrence (an application of
  an auxiliary family or constructor), the executable replacement
  head is the container (or container constructor) applied to the parameter
  arguments recorded by lowering; their translations are supplied by the
  hypothesis `RestoreHeadsTranslate`, and the typing of the head spine is read
  off the transported typing of the whole occurrence by inversion.
-/

namespace Lean.Expr

/-- `TrailingArgs heads np Q e`: in `e`, every argument after the first `np` of an
application spine headed by a constant of `heads` satisfies `Q`. The generalization of
`TrailingArgsAvoid` (without its literal clause) to an arbitrary condition. -/
inductive TrailingArgs (heads : List Name) (np : Nat) (Q : Expr → Prop) : Expr → Prop
  | bvar (i : Nat) : TrailingArgs heads np Q (.bvar i)
  | fvar (fv : FVarId) : TrailingArgs heads np Q (.fvar fv)
  | mvar (mv : MVarId) : TrailingArgs heads np Q (.mvar mv)
  | sort (u : Level) : TrailingArgs heads np Q (.sort u)
  | const (c : Name) (us : List Level) : TrailingArgs heads np Q (.const c us)
  | lit (l : Literal) : TrailingArgs heads np Q (.lit l)
  | app {f a : Expr} : TrailingArgs heads np Q f → TrailingArgs heads np Q a →
      (∀ c us, (Expr.app f a).getAppFn = .const c us → c ∈ heads →
        ∀ x ∈ ((Expr.app f a).getAppArgsList).drop np, Q x) →
      TrailingArgs heads np Q (.app f a)
  | lam {n : Name} {t b : Expr} {bi : BinderInfo} :
      TrailingArgs heads np Q t → TrailingArgs heads np Q b →
      TrailingArgs heads np Q (.lam n t b bi)
  | forallE {n : Name} {t b : Expr} {bi : BinderInfo} :
      TrailingArgs heads np Q t → TrailingArgs heads np Q b →
      TrailingArgs heads np Q (.forallE n t b bi)
  | letE {n : Name} {t v b : Expr} {nd : Bool} :
      TrailingArgs heads np Q t → TrailingArgs heads np Q v →
      TrailingArgs heads np Q b →
      TrailingArgs heads np Q (.letE n t v b nd)
  | mdata {m : MData} {e : Expr} : TrailingArgs heads np Q e →
      TrailingArgs heads np Q (.mdata m e)
  | proj {s : Name} {i : Nat} {e : Expr} : TrailingArgs heads np Q e →
      TrailingArgs heads np Q (.proj s i e)

end Lean.Expr

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature (Restoration HeadSpecialization instantiateParams)

/-! ### Projection names of translated syntax -/

/-- Every value of the context satisfies the projection condition. -/
def VLCtx.ProjNamesOK (ok : Name → Prop) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) → mapped.ProjNamesOK ok

theorem VLCtx.ProjNamesOK.nil {ok : Name → Prop} : VLCtx.ProjNamesOK ok [] := by
  intro v mapped type h
  cases v <;> simp [VLCtx.find?] at h

theorem VLCtx.ProjNamesOK.cons {ok : Name → Prop} {Δ : VLCtx} {d : VLocalDecl}
    {ofv : Option (FVarId × List FVarId)}
    (H : VLCtx.ProjNamesOK ok Δ) (hvalue : d.value.ProjNamesOK ok) :
    VLCtx.ProjNamesOK ok ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    exact (H hfind).liftN

theorem VLocalDecl.value_vlam_projNamesOK {ok : Name → Prop} {ty : VExpr} :
    (VLocalDecl.vlam ty).value.ProjNamesOK ok := trivial

theorem Literal.toConstructor_projsOK {ok : Name → Prop} :
    ∀ l : Literal, l.toConstructor.ProjsOK ok
  | .natVal _ => Expr.ProjsOK.natLitToConstructor
  | .strVal _ => Expr.ProjsOK.strLitToConstructor

/-- **Translation keeps projection names**: a projection condition on the
source syntax holds for its translation, given it for the values of the
context. -/
theorem TrSyn.projNamesOK_of_source {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrSyn Us Δ e e') {ok : Name → Prop}
    (hsrc : e.ProjsOK ok) (hΔ : VLCtx.ProjNamesOK ok Δ) : e'.ProjNamesOK ok := by
  induction H with
  | bvar hfind | fvar hfind => exact hΔ hfind
  | sort _ => trivial
  | const => trivial
  | app _ _ ihf iha => exact ⟨ihf hsrc.1 hΔ, iha hsrc.2 hΔ⟩
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    exact ⟨iht hsrc.1 hΔ, ihb hsrc.2 (hΔ.cons VLocalDecl.value_vlam_projNamesOK)⟩
  | letE _ _ _ _ ihv ihb =>
    exact ihb hsrc.2.2 (hΔ.cons (d := .vlet _ _) (ihv hsrc.2.1 hΔ))
  | lit _ ih => exact ih (Literal.toConstructor_projsOK _) hΔ
  | mdata _ ih => exact ih hsrc hΔ
  | proj _ ih => exact ⟨hsrc.1, ih hsrc.2 hΔ⟩

theorem TrExprS.projNamesOK_of_source {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') {ok : Name → Prop}
    (hsrc : e.ProjsOK ok) (hΔ : VLCtx.ProjNamesOK ok Δ) : e'.ProjNamesOK ok :=
  H.toTrSyn.projNamesOK_of_source hsrc hΔ

namespace VerifyInductive

variable {r : Restoration} {envT envL : VEnv} {I : VEnv.Interpretation}

/-- Projection names avoiding the restorable names are fixed by the interpretation of
a restoration substitution. -/
theorem RestorationSubstitution.projNamesFixed
    (S : r.Substitution envT envL I) :
    ∀ {e : VExpr}, e.ProjNamesOK (· ∉ r.restorableNames) → e.ProjNamesFixed I.projOwner
  | .bvar _, _ | .sort _, _ | .elim .., _ | .const .., _ => trivial
  | .app f a, h | .lam f a, h | .forallE f a, h =>
    ⟨RestorationSubstitution.projNamesFixed S h.1,
      RestorationSubstitution.projNamesFixed S h.2⟩
  | .proj n _ e, h => by
    exact ⟨S.agrees.projOwner n h.1, RestorationSubstitution.projNamesFixed S h.2⟩

/-- A name that is not a restoration head is not replaced. -/
theorem RestorationSubstitution.replacement_eq_none
    (S : r.Substitution envT envL I)
    {c : Name} (hc : c ∉ r.heads.map (·.auxiliary)) : I.consts c = none := by
  cases hρ : I.consts c with
  | none => rfl
  | some t =>
    obtain ⟨h, _, hf, _⟩ := S.agrees.shape c t hρ
    exact absurd (List.mem_map.mpr ⟨h, List.mem_of_find?_eq_some hf,
      by simpa using List.find?_some hf⟩) hc

/-! ### The context invariant -/

/-- Two translation contexts related by restoration: the same variable naming,
`let` values related by restoration, and the restored binder types
definitionally equal, in the target environment, to the replaced lowered ones.
The values of the lowered context project only out of non-restorable
structures. -/
structure RestoreTypedCtx (r : Restoration) (envL envT : VEnv) (I : VEnv.Interpretation)
    (U : Nat) (Δs Δt : VLCtx) : Prop where
  wfs : Δs.WF envL U
  rel : RestoreCtxRel r Δs Δt
  defeq : envT.IsDefEqCtx U [] (Δs.toCtx.map I.expr) Δt.toCtx
  projs : VLCtx.ProjNamesOK (· ∉ r.restorableNames) Δs

theorem RestoreTypedCtx.nil : RestoreTypedCtx r envL envT I U [] [] :=
  ⟨trivial, .nil, .zero, VLCtx.ProjNamesOK.nil⟩

theorem RestoreTypedCtx.onCtxImage (H : RestoreTypedCtx r envL envT I U Δs Δt) :
    OnCtx (Δs.toCtx.map I.expr) (envT.IsType U) :=
  H.defeq.isType' trivial

theorem RestoreTypedCtx.onCtx (H : RestoreTypedCtx r envL envT I U Δs Δt)
    (henv : envT.Ordered) : OnCtx Δt.toCtx (envT.IsType U) :=
  (H.defeq.symm henv).isType' trivial

/-- **Transport of a typing judgment** of the lowered context to the related
target context, at the replaced type. -/
theorem RestoreTypedCtx.hasType
    (S : r.Substitution envT envL I)
    (hβ : envT.BetaSubjectReduction U) (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {e A e' : VExpr} (He : envL.HasType U Δs.toCtx e A) (he : r.expr e = some e')
    (hok : e.ProjNamesOK (· ∉ r.restorableNames)) :
    envT.HasType U Δt.toCtx e' (I.expr A) := by
  have hΓ := H.onCtxImage
  have Hσ := S.sound.isDefEq (.typed S.ordered) He hΓ
  have h1 := S.expr_simAt hβ hΓ (RestorationSubstitution.projNamesFixed S hok)
    he _ Hσ
  exact h1.hasType.2.defeqDFC S.ordered H.defeq

/-- Transport of a typing judgment whose type also restores. -/
theorem RestoreTypedCtx.hasType_restored
    (S : r.Substitution envT envL I)
    (hβ : envT.BetaSubjectReduction U) (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {e A e' A' : VExpr} (He : envL.HasType U Δs.toCtx e A) (he : r.expr e = some e')
    (hA : r.expr A = some A')
    (hok : e.ProjNamesOK (· ∉ r.restorableNames))
    (hokA : A.ProjNamesOK (· ∉ r.restorableNames)) :
    envT.HasType U Δt.toCtx e' A' := by
  have hΓ := H.onCtxImage
  have Hσ := S.sound.isDefEq (.typed S.ordered) He hΓ
  have h1 := S.expr_simAt hβ hΓ (RestorationSubstitution.projNamesFixed S hok)
    he _ Hσ
  obtain ⟨u, hAσ⟩ := VEnv.IsDefEq.isType S.ordered hΓ Hσ
  have h3 := S.expr_simAt hβ hΓ (RestorationSubstitution.projNamesFixed S hokA)
    hA _ hAσ
  exact (VEnv.IsDefEq.defeqDF h3 h1.hasType.2).defeqDFC S.ordered H.defeq

theorem RestoreTypedCtx.isType
    (S : r.Substitution envT envL I)
    (hβ : envT.BetaSubjectReduction U) (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {A A' : VExpr} (HA : envL.IsType U Δs.toCtx A) (hA : r.expr A = some A')
    (hok : A.ProjNamesOK (· ∉ r.restorableNames)) :
    envT.IsType U Δt.toCtx A' := by
  obtain ⟨u, hu⟩ := HA
  exact ⟨u, H.hasType S hβ hu hA hok⟩

theorem RestoreTypedCtx.wf
    (S : r.Substitution envT envL I)
    (hβ : envT.BetaSubjectReduction U) (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {e e' : VExpr} (He : VExpr.WF envL U Δs.toCtx e) (he : r.expr e = some e')
    (hok : e.ProjNamesOK (· ∉ r.restorableNames)) :
    VExpr.WF envT U Δt.toCtx e' := by
  obtain ⟨A, hA⟩ := He
  exact ⟨_, H.hasType S hβ hA he hok⟩

/-- Extend the invariant under a binder. -/
theorem RestoreTypedCtx.vlam
    (S : r.Substitution envT envL I)
    (hβ : envT.BetaSubjectReduction U) (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {d d' : VExpr}
    (Hd : envL.IsType U Δs.toCtx d) (hd : r.expr d = some d')
    (hok : d.ProjNamesOK (· ∉ r.restorableNames)) :
    RestoreTypedCtx r envL envT I U ((none, .vlam d) :: Δs) ((none, .vlam d') :: Δt) := by
  refine ⟨⟨H.wfs, by simp, Hd⟩, H.rel.vlam, ?_,
    VLCtx.ProjNamesOK.cons H.projs VLocalDecl.value_vlam_projNamesOK⟩
  obtain ⟨u, hu⟩ := Hd
  have hΓ := H.onCtxImage
  have Hσ := S.sound.isDefEq (.typed S.ordered) hu hΓ
  have h1 := S.expr_simAt hβ hΓ (RestorationSubstitution.projNamesFixed S hok)
    hd _ Hσ
  exact .succ H.defeq h1

/-- Extend the invariant by a `let`. -/
theorem RestoreTypedCtx.vlet (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {ty ty' v v' : VExpr} (Hv : envL.HasType U Δs.toCtx v ty)
    (hv : r.expr v = some v') (hok : v.ProjNamesOK (· ∉ r.restorableNames)) :
    RestoreTypedCtx r envL envT I U ((none, .vlet ty v) :: Δs) ((none, .vlet ty' v') :: Δt) :=
  ⟨⟨H.wfs, by simp, Hv⟩, H.rel.vlet hv, by simpa [VLCtx.toCtx] using H.defeq,
    VLCtx.ProjNamesOK.cons (d := .vlet ty v) H.projs hok⟩


theorem restoration_expr_sort {r : Restoration} {u : VLevel} :
    r.expr (.sort u) = some (.sort u) := by
  simp [Restoration.expr, Restoration.expr.go, VExpr.mkApps]

theorem restoration_expr_const_of_not_mem {r : Restoration} {c : Name} {ls : List VLevel}
    (hc : c ∉ r.restorableNames) : r.expr (.const c ls) = some (.const c ls) := by
  have h1 : c ∉ r.heads.map (·.auxiliary) := fun hm => hc (List.mem_append_left _ hm)
  have h2 : c ∉ r.recursors.map Prod.fst := fun hm => hc (List.mem_append_right _ hm)
  simp [Restoration.expr, Restoration.expr.go, Restoration.heads_find?_eq_none h1,
    Restoration.recursorName_of_not_mem h2, VExpr.mkApps]

/-- A constant that is not restorable is kept by the substitution under its own
name. -/
theorem RestorationSubstitution.kept_of_not_mem
    (S : r.Substitution envT envL I)
    {c : Name} {ci : VConstant} (hci : envL.constants c = some ci)
    (hc : c ∉ r.restorableNames) :
    ∃ ci', envT.constants c = some ci' ∧ ci'.uvars = ci.uvars := by
  have h1 : c ∉ r.heads.map (·.auxiliary) := fun hm => hc (List.mem_append_left _ hm)
  have h2 : c ∉ r.recursors.map Prod.fst := fun hm => hc (List.mem_append_right _ hm)
  obtain ⟨ci', hci', huv, _⟩ := (S.sound.constants c ci hci).2
    (RestorationSubstitution.replacement_eq_none S h1)
  rw [S.agrees.renamed c (Restoration.heads_find?_eq_none h1),
    Restoration.recursorName_of_not_mem h2] at hci'
  exact ⟨ci', hci', huv⟩

/-! ### Syntax avoiding the restorable names -/

/-- **Syntax avoiding the restorable names translates in the target
environment**, to the restoration of its lowered translation. -/
theorem translate_avoids_exists
    (S : r.Substitution envT envL I)
    {Us : List Name} (hβ : envT.BetaSubjectReduction Us.length)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l)
    {e : Expr} {Δs Δt : VLCtx} {s : VExpr}
    (Havoid : e.AvoidsConsts r.restorableNames)
    (Hprojs : e.ProjsOK (· ∉ r.restorableNames))
    (Hctx : RestoreTypedCtx r envL envT I Us.length Δs Δt)
    (Hs : TrExprS envL Us Δs e s) :
    ∃ t, TrExprS envT Us Δt e t ∧ r.expr s = some t := by
  induction Hs generalizing Δt with
  | bvar h =>
    rcases Hctx.rel.find? hc h with ⟨et, B, hf, hr⟩
    exact ⟨et, .bvar hf, hr⟩
  | fvar h =>
    rcases Hctx.rel.find? hc h with ⟨et, B, hf, hr⟩
    exact ⟨et, .fvar hf, hr⟩
  | sort h => exact ⟨_, .sort h, restoration_expr_sort⟩
  | const hcs hls hlen =>
    cases Havoid with
    | const _ _ hfresh =>
      obtain ⟨ci', hci', huv⟩ :=
        RestorationSubstitution.kept_of_not_mem S hcs hfresh
      exact ⟨_, .const hci' hls (hlen.trans huv.symm),
        restoration_expr_const_of_not_mem hfresh⟩
  | app h1 h2 hf ha ihf iha =>
    cases Havoid with
    | app _ _ Hf Ha =>
      obtain ⟨tf, Htf, hrf⟩ := ihf Hf Hprojs.1 Hctx
      obtain ⟨ta, Hta, hra⟩ := iha Ha Hprojs.2 Hctx
      have h1' := Hctx.hasType S hβ h1 hrf (hf.projNamesOK_of_source Hprojs.1 Hctx.projs)
      have h2' := Hctx.hasType S hβ h2 hra (ha.projNamesOK_of_source Hprojs.2 Hctx.projs)
      exact ⟨_, .app h1' h2' Htf Hta, restoration_expr_app hrf hra⟩
  | lam h1 hty hb ihty ihb =>
    cases Havoid with
    | lam _ _ _ _ Hty Hb =>
      obtain ⟨tty, Htty, hrty⟩ := ihty Hty Hprojs.1 Hctx
      have hok := hty.projNamesOK_of_source Hprojs.1 Hctx.projs
      have Hctx' := Hctx.vlam S hβ h1 hrty hok
      obtain ⟨tb, Htb, hrb⟩ := ihb Hb Hprojs.2 Hctx'
      exact ⟨_, .lam (Hctx.isType S hβ h1 hrty hok) Htty Htb, restoration_expr_lam hrty hrb⟩
  | forallE h1 h2 hty hb ihty ihb =>
    cases Havoid with
    | forallE _ _ _ _ Hty Hb =>
      obtain ⟨tty, Htty, hrty⟩ := ihty Hty Hprojs.1 Hctx
      have hok := hty.projNamesOK_of_source Hprojs.1 Hctx.projs
      have Hctx' := Hctx.vlam S hβ h1 hrty hok
      obtain ⟨tb, Htb, hrb⟩ := ihb Hb Hprojs.2 Hctx'
      have hokb := hb.projNamesOK_of_source Hprojs.2
        (VLCtx.ProjNamesOK.cons Hctx.projs VLocalDecl.value_vlam_projNamesOK)
      exact ⟨_, .forallE (Hctx.isType S hβ h1 hrty hok) (Hctx'.isType S hβ h2 hrb hokb)
        Htty Htb, restoration_expr_forallE hrty hrb⟩
  | letE h1 hty hval hb ihty ihval ihb =>
    cases Havoid with
    | letE _ _ _ _ _ Hty Hval Hb =>
      obtain ⟨tty, Htty, hrty⟩ := ihty Hty Hprojs.1 Hctx
      obtain ⟨tval, Htval, hrval⟩ := ihval Hval Hprojs.2.1 Hctx
      have hokty := hty.projNamesOK_of_source Hprojs.1 Hctx.projs
      have hokval := hval.projNamesOK_of_source Hprojs.2.1 Hctx.projs
      obtain ⟨tb, Htb, hrb⟩ := ihb Hb Hprojs.2.2 (Hctx.vlet (ty' := tty) h1 hrval hokval)
      exact ⟨_, .letE (Hctx.hasType_restored S hβ h1 hrval hrty hokval hokty) Htty Htval Htb, hrb⟩
  | lit hcont _ ih =>
    cases Havoid with
    | lit _ Ha =>
      obtain ⟨t, Ht, hr⟩ := ih Ha (Literal.toConstructor_projsOK _) Hctx
      exact ⟨t, .lit (Hlits _ hcont) Ht, hr⟩
  | mdata _ ih =>
    cases Havoid with
    | mdata _ _ Ha =>
      obtain ⟨t, Ht, hr⟩ := ih Ha Hprojs Hctx
      exact ⟨t, .mdata Ht, hr⟩
  | proj he hp ih =>
    cases Havoid with
    | proj _ _ _ Ha =>
      obtain ⟨te, Hte, hre⟩ := ih Ha Hprojs.2 Hctx
      have hok := he.projNamesOK_of_source Hprojs.2 Hctx.projs
      refine ⟨_, .proj Hte
        (Hctx.wf S hβ hp (restoration_expr_proj hre) ⟨Hprojs.1, hok⟩),
        restoration_expr_proj hre⟩


/-! ### Restoration of opened bodies -/

/-- The executable replacement heads translate: at every context lifting a
base context `Δt0` by binders, in which the opened parameters `As` translate
to `PT`, the replacement head of a restorable name is a constant applied to
arguments translating to the specialization's arguments at `PT`. -/
def RestoreHeadsTranslate (r : Restoration) (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (envT : VEnv) (Us : List Name) (auxLevels : List Level)
    (As : Array Expr) (Δt0 : VLCtx) : Prop :=
  ∀ Δt dn n, VLCtx.BVLift Δt0 Δt dn 0 n 0 →
  ∀ c H, restoreHead result env As c = some H →
  ∀ h : HeadSpecialization, r.heads.find? (fun h => h.auxiliary == c) = some h →
  ∀ levels, auxLevels.mapM (VLevel.ofLevel Us) = some levels →
  ∀ PT, List.Forall₂ (TrExprS envT Us Δt) As.toList PT →
    ∃ fn args, H = Expr.mkAppList fn args ∧
      TrExprS envT Us Δt fn (.const h.target (h.levels.map (·.inst levels))) ∧
      List.Forall₂ (TrExprS envT Us Δt) args
        (h.arguments.map fun arg => instantiateParams (arg.instL levels) PT)

/-- The head-occurrence case of `restorationTranslates`. -/
theorem restorationTranslates'_paramUniform
    (S : r.Substitution envT envL I)
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (hL : envL.Ordered) (hβ : envT.BetaSubjectReduction Us.length)
    (A : RestorationMapAgreement r result env auxRec envT Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l)
    {Δt0 : VLCtx} (Hheads : RestoreHeadsTranslate r result env envT Us auxLevels As Δt0)
    {e : Expr} {c : Name} {us : List Level} {Δs Δt : VLCtx} {s : VExpr}
    (hfn : e.getAppFn = .const c us) (hmem : c ∈ r.heads.map (·.auxiliary))
    (Hshape : e.ParamUniform (r.heads.map (·.auxiliary)) As.toList auxLevels)
    (Htrail : ∀ x ∈ e.getAppArgsList.drop result.nparams, x.AvoidsConsts r.restorableNames)
    (Hprojs : e.ProjsOK (· ∉ r.restorableNames))
    (Hctx : RestoreTypedCtx r envL envT I Us.length Δs Δt)
    (Hlift : ∃ dn n, VLCtx.BVLift Δt0 Δt dn 0 n 0)
    (Hs : TrExprS envL Us Δs e s) :
    ∃ t, TrExprS envT Us Δt (e.replace (result.restoreNestedNode env As auxRec)) t ∧
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
  have hrestTrail : ∀ x ∈ rest, x.AvoidsConsts r.restorableNames := by
    intro x hx
    apply Htrail
    rw [hargs, ← hAsLen, List.drop_left]
    exact hx
  rw [Expr.replace_of_some hnode, hargs, ← hAsLen, List.drop_left]
  have he : e = Expr.mkAppList (.const c auxLevels) (As.toList ++ rest) := by
    rw [← hargs, ← hfn, Expr.mkAppList_getAppArgsList]
  subst he
  have hokS := Hs.projNamesOK_of_source Hprojs Hctx.projs
  have HsWF := Hs.wf hL Hctx.wfs
  rcases checkPositivityStep.TrExprS.mkAppList_inv Hs with ⟨fn', L', hfn', hL', rfl⟩
  obtain ⟨lv, rfl, hlsV⟩ : ∃ lv, fn' = .const c lv ∧
      auxLevels.mapM (VLevel.ofLevel Us) = some lv := by
    cases hfn' with
    | const _ h _ => exact ⟨_, rfl, h⟩
  obtain ⟨P', R'', rfl, hP', hR''⟩ := List.Forall₂.append_inv hL'
  rcases A.head As c H hH with ⟨h, hfind, hnparams, hlevels⟩
  rcases hlevels _ hlsV with ⟨huvars, -⟩
  obtain ⟨PT, hPT, hPr⟩ := Hctx.rel.translate_fvars hc HAs hP'
  have hrestProjs : ∀ x ∈ rest, x.ProjsOK (· ∉ r.restorableNames) := by
    intro x hx
    exact (Expr.ProjsOK.mkAppList_iff.1 Hprojs).2 x (List.mem_append_right _ hx)
  have hRest : ∀ {xs : List Expr} {ys : List VExpr}, (∀ x ∈ xs, x ∈ rest) →
      List.Forall₂ (TrExprS envL Us Δs) xs ys →
      ∃ zs, List.Forall₂ (TrExprS envT Us Δt) xs zs ∧
        List.Forall₂ (fun x y => Restoration.expr.go r x [] = some y) ys zs := by
    intro xs ys hxs H
    induction H with
    | nil => exact ⟨[], .nil, .nil⟩
    | @cons x y xs ys hxy _ ih =>
      have hx := hxs x List.mem_cons_self
      obtain ⟨z, Hz, hz⟩ := translate_avoids_exists S hβ hc Hlits (hrestTrail x hx)
        (hrestProjs x hx) Hctx hxy
      obtain ⟨zs, Hzs, hzs⟩ := ih (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
      exact ⟨z :: zs, .cons Hz Hzs, .cons hz hzs⟩
  obtain ⟨R', hR', hRr⟩ := hRest (fun x hx => hx) hR''
  obtain ⟨dn, n, W⟩ := Hlift
  obtain ⟨fn, args, rfl, Hfn, Hargs⟩ := Hheads Δt dn n W c H hH h hfind _ hlsV PT hPT
  have hPTlen : PT.length = result.nparams := by
    rw [← Lean4Lean.List.Forall₂.length_eq hPT, hAsLen]
  have hr : r.expr (VExpr.mkApps (.const c lv) (P' ++ R'')) =
      some (VExpr.mkApps (.const h.target (h.levels.map (·.inst lv)))
        (h.arguments.map (fun arg => instantiateParams (arg.instL lv) PT) ++ R')) := by
    simp only [Restoration.expr]
    rw [Restoration.expr.go_mkApps r (List.Forall₂.append' hPr hRr), List.append_nil]
    have hle : h.nparams ≤ (PT ++ R').length := by simp [hnparams, hPTlen]
    simp [Restoration.expr.go, hfind, HeadSpecialization.apply, huvars, hnparams, hPTlen,
      Lean4Lean.VExpr.mkApps_append]
  refine ⟨_, ?_, hr⟩
  have hwf := Hctx.wf S hβ HsWF hr hokS
  rw [← Expr.mkAppList_append]
  exact checkPositivityStep.TrExprS.mkAppList S.ordered (Hctx.onCtx S.ordered) Hfn
    (List.Forall₂.append' Hargs hR') hwf


/-- **Restoration preserves translation** on an opened body traversed by
`Expr.replace` with `restoreNestedNode`: the executable output translates in
the target environment, to the restoration of the lowered translation. -/
theorem restorationTranslates
    (S : r.Substitution envT envL I)
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (hL : envL.Ordered) (hβ : envT.BetaSubjectReduction Us.length)
    (A : RestorationMapAgreement r result env auxRec envT Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv) (hsize : As.size = result.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l)
    (Hlitnames : ∀ l : Literal, l.toConstructor.AvoidsConsts r.restorableNames)
    {Δt0 : VLCtx} (Hheads : RestoreHeadsTranslate r result env envT Us auxLevels As Δt0)
    {e : Expr} {Δs Δt : VLCtx} {s : VExpr}
    (Hshape : e.ParamUniform (r.heads.map (·.auxiliary)) As.toList auxLevels)
    (Htrail : e.TrailingArgs (r.heads.map (·.auxiliary)) result.nparams
      (·.AvoidsConsts r.restorableNames))
    (Hprojs : e.ProjsOK (· ∉ r.restorableNames))
    (Hctx : RestoreTypedCtx r envL envT I Us.length Δs Δt)
    (Hlift : ∃ dn n, VLCtx.BVLift Δt0 Δt dn 0 n 0)
    (Hs : TrExprS envL Us Δs e s) :
    ∃ t, TrExprS envT Us Δt (e.replace (result.restoreNestedNode env As auxRec)) t ∧
      r.expr s = some t := by
  have hmiss : ∀ x : Expr, (∀ c us, x ≠ .const c us) → (∀ c us, x.getAppFn ≠ .const c us) →
      result.restoreNestedNode env As auxRec x = none := fun x h1 h2 =>
    restoreNestedNode_eq_none_of_restoreHead result env As auxRec x
      (fun c us h => absurd h (h1 c us)) (fun c us h => absurd h (h2 c us))
  have hliftV : ∀ {Δt : VLCtx} (d : VLocalDecl), (∃ dn n, VLCtx.BVLift Δt0 Δt dn 0 n 0) →
      ∃ dn n, VLCtx.BVLift Δt0 ((none, d) :: Δt) dn 0 n 0 := by
    rintro Δt d ⟨dn, n, W⟩
    exact ⟨_, _, .skip d W⟩
  induction Hs generalizing Δt with
  | bvar h =>
    rw [Expr.replace_bvar_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    rcases Hctx.rel.find? hc h with ⟨et, B, hf, hr⟩
    exact ⟨et, .bvar hf, hr⟩
  | fvar h =>
    rw [Expr.replace_fvar_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    rcases Hctx.rel.find? hc h with ⟨et, B, hf, hr⟩
    exact ⟨et, .fvar hf, hr⟩
  | sort h =>
    rw [Expr.replace_sort_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    exact ⟨_, .sort h, restoration_expr_sort⟩
  | @const c ci _ _ us hcs hls hlen =>
    by_cases hmem : c ∈ r.heads.map (·.auxiliary)
    · exact restorationTranslates'_paramUniform S hL hβ A hc HAs hsize Hlits Hheads rfl hmem Hshape
        (fun x hx => by
          rw [show (Expr.const c us).getAppArgsList = [] from rfl] at hx; simp at hx)
        Hprojs Hctx Hlift (.const hcs hls hlen)
    · have hnone := A.restoreHead_eq_none (As := As) hmem
      have hρ := RestorationSubstitution.replacement_eq_none S hmem
      obtain ⟨ci', hci', huv, -⟩ := (S.sound.constants c ci hcs).2 hρ
      rw [S.agrees.renamed c (Restoration.heads_find?_eq_none hmem), A.recursorName] at hci'
      cases hrec : auxRec.find? c with
      | some new =>
        rw [Expr.replace_of_some (restoreNestedNode_recursor result env As auxRec c new us
          hrec)]
        rw [hrec] at hci'
        refine ⟨_, .const hci' hls (hlen.trans huv.symm), ?_⟩
        simp only [Restoration.expr]
        rw [A.go_const (As := As) hnone]
        simp [hrec, VExpr.mkApps]
      | none =>
        rw [Expr.replace_const_of_none (restoreNestedNode_eq_none_of_restoreHead result env
          As auxRec _ (fun c' ls' heq => by cases heq; exact hrec)
          (fun c' ls' h => by
            simp only [Expr.getAppFn, Expr.const.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact hnone))]
        rw [hrec] at hci'
        refine ⟨_, .const hci' hls (hlen.trans huv.symm), ?_⟩
        simp only [Restoration.expr]
        rw [A.go_const (As := As) hnone]
        simp [hrec, VExpr.mkApps]
  | @app _ _ _ _ _ f a h1 h2 hf ha ihf iha =>
    by_cases hhit : ∃ c us, (Expr.app f a).getAppFn = .const c us ∧
        c ∈ r.heads.map (·.auxiliary)
    · obtain ⟨c, us, hfn, hmem⟩ := hhit
      have htr : ∀ x ∈ (Expr.app f a).getAppArgsList.drop result.nparams,
          x.AvoidsConsts r.restorableNames := by
        cases Htrail with
        | app _ _ hQ => exact hQ c us hfn hmem
      exact restorationTranslates'_paramUniform S hL hβ A hc HAs hsize Hlits Hheads hfn hmem Hshape
        htr Hprojs Hctx Hlift (.app h1 h2 hf ha)
    · have hnot : ∀ c us, f.getAppFn = .const c us → c ∉ r.heads.map (·.auxiliary) :=
        fun c us hfn hmem => hhit ⟨c, us, by simpa [Expr.getAppFn] using hfn, hmem⟩
      obtain ⟨Hf, Ha⟩ := Hshape.app_inv hnot
      have hnone : result.restoreNestedNode env As auxRec (.app f a) = none :=
        restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
          (by intro _ _ h; cases h)
          (fun c us hfn => A.restoreHead_eq_none
            (hnot c us (by simpa [Expr.getAppFn] using hfn)))
      rw [Expr.replace_app_of_none hnone]
      cases Htrail with
      | app Tf Ta _ =>
      obtain ⟨tf, Htf, hrf⟩ := ihf Hf Tf Hprojs.1 Hctx Hlift
      obtain ⟨ta, Hta, hra⟩ := iha Ha Ta Hprojs.2 Hctx Hlift
      have h1' := Hctx.hasType S hβ h1 hrf (hf.projNamesOK_of_source Hprojs.1 Hctx.projs)
      have h2' := Hctx.hasType S hβ h2 hra (ha.projNamesOK_of_source Hprojs.2 Hctx.projs)
      exact ⟨_, .app h1' h2' Htf Hta, restoration_expr_app hrf hra⟩
  | lam h1 hty hb ihty ihb =>
    obtain ⟨Sty, Sb⟩ := Hshape.lam_inv
    rw [Expr.replace_lam_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    cases Htrail with
    | lam Tty Tb =>
    obtain ⟨tty, Htty, hrty⟩ := ihty Sty Tty Hprojs.1 Hctx Hlift
    have hok := hty.projNamesOK_of_source Hprojs.1 Hctx.projs
    have Hctx' := Hctx.vlam S hβ h1 hrty hok
    obtain ⟨tb, Htb, hrb⟩ := ihb Sb Tb Hprojs.2 Hctx' (hliftV _ Hlift)
    exact ⟨_, .lam (Hctx.isType S hβ h1 hrty hok) Htty Htb, restoration_expr_lam hrty hrb⟩
  | forallE h1 h2 hty hb ihty ihb =>
    obtain ⟨Sty, Sb⟩ := Hshape.forallE_inv
    rw [Expr.replace_forallE_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    cases Htrail with
    | forallE Tty Tb =>
    obtain ⟨tty, Htty, hrty⟩ := ihty Sty Tty Hprojs.1 Hctx Hlift
    have hok := hty.projNamesOK_of_source Hprojs.1 Hctx.projs
    have Hctx' := Hctx.vlam S hβ h1 hrty hok
    obtain ⟨tb, Htb, hrb⟩ := ihb Sb Tb Hprojs.2 Hctx' (hliftV _ Hlift)
    have hokb := hb.projNamesOK_of_source Hprojs.2
      (VLCtx.ProjNamesOK.cons Hctx.projs VLocalDecl.value_vlam_projNamesOK)
    exact ⟨_, .forallE (Hctx.isType S hβ h1 hrty hok) (Hctx'.isType S hβ h2 hrb hokb)
      Htty Htb, restoration_expr_forallE hrty hrb⟩
  | letE h1 hty hval hb ihty ihval ihb =>
    obtain ⟨-, Sval, Sb⟩ := Hshape.letE_inv
    rw [Expr.replace_letE_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    cases Htrail with
    | letE Tty Tval Tb =>
    obtain ⟨Sty, -, -⟩ := Hshape.letE_inv
    obtain ⟨tty, Htty, hrty⟩ := ihty Sty Tty Hprojs.1 Hctx Hlift
    obtain ⟨tval, Htval, hrval⟩ := ihval Sval Tval Hprojs.2.1 Hctx Hlift
    have hokty := hty.projNamesOK_of_source Hprojs.1 Hctx.projs
    have hokval := hval.projNamesOK_of_source Hprojs.2.1 Hctx.projs
    obtain ⟨tb, Htb, hrb⟩ := ihb Sb Tb Hprojs.2.2 (Hctx.vlet (ty' := tty) h1 hrval hokval)
      (hliftV _ Hlift)
    exact ⟨_, .letE (Hctx.hasType_restored S hβ h1 hrval hrty hokval hokty) Htty Htval Htb, hrb⟩
  | lit hcont htc _ =>
    rw [Expr.replace_lit_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    obtain ⟨t, Ht, hr⟩ := translate_avoids_exists S hβ hc Hlits (Hlitnames _)
      (Literal.toConstructor_projsOK _) Hctx htc
    exact ⟨t, .lit (Hlits _ hcont) Ht, hr⟩
  | mdata _ ih =>
    have He := Hshape.mdata_inv
    rw [Expr.replace_mdata_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    cases Htrail with
    | mdata Te =>
    obtain ⟨t, Ht, hr⟩ := ih He Te Hprojs Hctx Hlift
    exact ⟨t, .mdata Ht, hr⟩
  | proj he hp ih =>
    have He := Hshape.proj_inv
    rw [Expr.replace_proj_of_none (hmiss _ (by simp) (by simp [Expr.getAppFn]))]
    cases Htrail with
    | proj Te =>
    obtain ⟨te, Hte, hre⟩ := ih He Te Hprojs.2 Hctx Hlift
    have hok := he.projNamesOK_of_source Hprojs.2 Hctx.projs
    exact ⟨_, .proj Hte
      (Hctx.wf S hβ hp (restoration_expr_proj hre) ⟨Hprojs.1, hok⟩),
      restoration_expr_proj hre⟩


/-! ### Closing the opened parameters -/

/-- A metacontext of binders whose types avoid the restorable names. -/
def MLCtxAvoids (r : Restoration) : TypeChecker.MLCtx → Prop
  | .nil => True
  | .vlam _ _ ty _ _ c =>
    ty.AvoidsConsts r.restorableNames ∧ ty.ProjsOK (· ∉ r.restorableNames) ∧ MLCtxAvoids r c
  | .vlet .. => False


theorem _root_.Lean.Expr.AvoidsConsts.instantiate1'_fvar {names : List Name} {e : Expr}
    (H : e.AvoidsConsts names) (fv : FVarId) (d : Nat) :
    (e.instantiate1' (.fvar fv) d).AvoidsConsts names := by
  induction H generalizing d with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · exact .bvar _
    · split
      · simp only [Expr.liftLooseBVars']; exact .fvar _
      · exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const _ _ h => exact .const _ _ h
  | app _ _ _ _ ihf iha => exact .app _ _ (ihf d) (iha d)
  | lam _ _ _ _ _ _ iht ihb => exact .lam _ _ _ _ (iht d) (ihb (d + 1))
  | forallE _ _ _ _ _ _ iht ihb => exact .forallE _ _ _ _ (iht d) (ihb (d + 1))
  | letE _ _ _ _ _ _ _ _ iht ihv ihb =>
    exact .letE _ _ _ _ _ (iht d) (ihv d) (ihb (d + 1))
  | lit _ h => exact .lit _ h
  | mdata _ _ _ ih => exact .mdata _ _ (ih d)
  | proj _ _ _ _ ih => exact .proj _ _ _ (ih d)

theorem Expr.forallDomainsOnly_instantiate1'_fvar :
    ∀ (n : Nat) (e : Expr) (fv : FVarId) (d : Nat),
      (Expr.forallDomainsOnly n e).instantiate1' (.fvar fv) d =
        Expr.forallDomainsOnly n (e.instantiate1' (.fvar fv) d)
  | 0, _, _, _ => by simp [Expr.forallDomainsOnly, Expr.instantiate1']
  | n + 1, .forallE _ _ body _, fv, d => by
    simp [Expr.forallDomainsOnly, Expr.instantiate1',
      Expr.forallDomainsOnly_instantiate1'_fvar n body fv (d + 1)]
  | n + 1, .bvar i, fv, d => by
    simp only [Expr.forallDomainsOnly, Expr.instantiate1']
    split
    · rfl
    · split
      · simp [Expr.liftLooseBVars', Expr.forallDomainsOnly]
      · rfl
  | n + 1, .fvar _, _, _ | n + 1, .mvar _, _, _ | n + 1, .sort _, _, _
  | n + 1, .const .., _, _ | n + 1, .lit _, _, _ | n + 1, .app .., _, _
  | n + 1, .lam .., _, _ | n + 1, .letE .., _, _ | n + 1, .mdata .., _, _
  | n + 1, .proj .., _, _ => by simp [Expr.forallDomainsOnly, Expr.instantiate1']

/-- The leading lambda domains of a term, with the residual body replaced by
`Sort 0`. -/
def Expr.lamDomainsOnly : Nat → Expr → Expr
  | 0, _ => .sort .zero
  | n + 1, .lam name domain body bi => .lam name domain (lamDomainsOnly n body) bi
  | _, _ => .sort .zero

theorem Expr.lamDomainsOnly_instantiate1'_fvar :
    ∀ (n : Nat) (e : Expr) (fv : FVarId) (d : Nat),
      (Expr.lamDomainsOnly n e).instantiate1' (.fvar fv) d =
        Expr.lamDomainsOnly n (e.instantiate1' (.fvar fv) d)
  | 0, _, _, _ => by simp [Expr.lamDomainsOnly, Expr.instantiate1']
  | n + 1, .lam _ _ body _, fv, d => by
    simp [Expr.lamDomainsOnly, Expr.instantiate1',
      Expr.lamDomainsOnly_instantiate1'_fvar n body fv (d + 1)]
  | n + 1, .bvar i, fv, d => by
    simp only [Expr.lamDomainsOnly, Expr.instantiate1']
    split
    · rfl
    · split
      · simp [Expr.liftLooseBVars', Expr.lamDomainsOnly]
      · rfl
  | n + 1, .fvar _, _, _ | n + 1, .mvar _, _, _ | n + 1, .sort _, _, _
  | n + 1, .const .., _, _ | n + 1, .lit _, _, _ | n + 1, .app .., _, _
  | n + 1, .forallE .., _, _ | n + 1, .letE .., _, _ | n + 1, .mdata .., _, _
  | n + 1, .proj .., _, _ => by simp [Expr.lamDomainsOnly, Expr.instantiate1']

theorem MLCtx.length_dropN : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length),
    (c.dropN n h).length = c.length - n
  | _, 0, _ => by simp
  | .vlam _ _ _ _ _ c, n + 1, h => by
    simp only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.length]
    rw [MLCtx.length_dropN c n]; omega
  | .vlet _ _ _ _ _ _ c, n + 1, h => by
    simp only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.length]
    rw [MLCtx.length_dropN c n]; omega

theorem MLCtx.dropN_succ_of_vlam : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n + 1 ≤ c.length)
    {id name ty ty' bi c0},
    c.dropN n (Nat.le_of_succ_le h) = .vlam id name ty ty' bi c0 →
    c.dropN (n + 1) h = c0
  | .vlam .., 0, _, _, _, _, _, _, _, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd ⊢; cases hd; rfl
  | .vlet .., 0, _, _, _, _, _, _, _, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd; cases hd
  | .vlam _ _ _ _ _ c, n + 1, h, _, _, _, _, _, _, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd ⊢
    exact MLCtx.dropN_succ_of_vlam c n _ hd
  | .vlet _ _ _ _ _ _ c, n + 1, h, _, _, _, _, _, _, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd ⊢
    exact MLCtx.dropN_succ_of_vlam c n _ hd

theorem MLCtx.mkForall'_succ : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n + 1 ≤ c.length)
    {id name ty ty' bi c0} (e : VExpr),
    c.dropN n (Nat.le_of_succ_le h) = .vlam id name ty ty' bi c0 →
    c.mkForall' (n + 1) h e = .forallE ty' (c.mkForall' n (Nat.le_of_succ_le h) e)
  | .vlam .., 0, _, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd; cases hd; simp
  | .vlet .., 0, _, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd; cases hd
  | .vlam _ _ _ _ _ c, n + 1, h, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd
    simp only [TypeChecker.MLCtx.mkForall']
    exact MLCtx.mkForall'_succ c n _ _ hd
  | .vlet _ _ _ _ _ _ c, n + 1, h, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd
    simp only [TypeChecker.MLCtx.mkForall']
    exact MLCtx.mkForall'_succ c n _ _ hd

theorem MLCtx.mkLambda'_succ : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n + 1 ≤ c.length)
    {id name ty ty' bi c0} (e : VExpr),
    c.dropN n (Nat.le_of_succ_le h) = .vlam id name ty ty' bi c0 →
    c.mkLambda' (n + 1) h e = .lam ty' (c.mkLambda' n (Nat.le_of_succ_le h) e)
  | .vlam .., 0, _, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd; cases hd; simp
  | .vlet .., 0, _, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd; cases hd
  | .vlam _ _ _ _ _ c, n + 1, h, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd
    simp only [TypeChecker.MLCtx.mkLambda']
    exact MLCtx.mkLambda'_succ c n _ _ hd
  | .vlet _ _ _ _ _ _ c, n + 1, h, _, _, _, _, _, _, e, hd => by
    simp only [TypeChecker.MLCtx.dropN] at hd
    simp only [TypeChecker.MLCtx.mkLambda']
    exact MLCtx.mkLambda'_succ c n _ _ hd

/-- The parameter opening of restoration, applied to a translated forall
telescope, extends a semantic metacontext by the opened parameters: the opened
body translates in the extended metacontext, and the telescope is the closure
of that translation over the new parameters. -/
theorem ParamOpening.toMLCtxForall {env : VEnv} {Us : List Name}
    (henv : env.WF) {r : Restoration}
    {lctx : LocalContext} {As : Array Expr} {e : Expr} {n : Nat}
    {outLctx : LocalContext} {outAs : Array Expr} {tail residual : Expr}
    (Hopen : ParamOpening lctx As e n outLctx outAs tail)
    (Htel : Expr.ForallTelescope e n residual)
    (houtWF : outLctx.WF)
    (m : TypeChecker.MLCtx) (hm : m.lctx = lctx) (hmWF : m.WF env Us)
    {target : VExpr} (He : TrExprS env Us m.vlctx e target)
    (HeTy : env.IsType Us.length m.vlctx.toCtx target)
    (Hav : (Expr.forallDomainsOnly n e).AvoidsConsts r.restorableNames)
    (Hpj : (Expr.forallDomainsOnly n e).ProjsOK (· ∉ r.restorableNames))
    (Hm : MLCtxAvoids r m) :
    ∃ (m' : TypeChecker.MLCtx) (tgt : VExpr) (hn : n ≤ m'.length),
      m'.lctx = outLctx ∧ m'.WF env Us ∧ m'.dropN n hn = m ∧ MLCtxAvoids r m' ∧
      TrExprS env Us m'.vlctx tail tgt ∧
      env.IsType Us.length m'.vlctx.toCtx tgt ∧
      target = m'.mkForall' n hn tgt := by
  induction Hopen generalizing m target residual with
  | done => exact ⟨m, target, Nat.zero_le _, hm, hmWF, rfl, Hm, He, HeTy, rfl⟩
  | lam Hnext ih => cases Htel
  | forallE Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Htel' =>
    cases He with
    | forallE HdomainType HbodyType Hdomain Hbody =>
      rename_i domainTarget bodyTarget
      have hcurrentWF : lctx'.WF := hm ▸ hmWF.tr.1
      have hidFresh : lctx'.find? id = none := by
        rcases Hnext.context_extension with
          ⟨decls, hlctx, _hparams, _hlength⟩
        have hnodup := houtWF.nodup
        rw [hlctx, List.map_append] at hnodup
        simp only [LocalContext.mkLocalDecl_toList, List.map_cons,
          LocalDecl.fvarId] at hnodup
        have hidNotMem : id ∉ lctx'.toList.map (fun d => d.fvarId) := by
          exact (List.nodup_cons.mp
            (List.nodup_append.mp hnodup).2.1).1
        rw [hcurrentWF.find?_eq_find?_toList]
        exact List.find?_eq_none.mpr (by
          intro decl hdecl hmatch
          have hfv : decl.fvarId = id := (LawfulBEq.eq_of_beq hmatch).symm
          exact hidNotMem (List.mem_map.mpr ⟨decl, hdecl, hfv⟩))
      let nextMLCtx := TypeChecker.MLCtx.vlam id name dom domainTarget bi m
      have hnextWF : nextMLCtx.WF env Us :=
        ⟨hmWF, by simpa [nextMLCtx, hm] using hidFresh,
          Hdomain, HdomainType⟩
      have Hbody' : TrExprS env Us nextMLCtx.vlctx
          (body.instantiate1 (.fvar id)) bodyTarget := by
        rw [Expr.instantiate1_eq]
        exact Hbody.inst_fvar henv.ordered hnextWF.tr.wf
      have HbodyTy : env.IsType Us.length nextMLCtx.vlctx.toCtx bodyTarget := HbodyType
      simp only [Expr.forallDomainsOnly] at Hav Hpj
      cases Hav with
      | forallE _ _ _ _ HavDom HavBody =>
      have HavBody' : (Expr.forallDomainsOnly n' (body.instantiate1 (.fvar id))).AvoidsConsts
          r.restorableNames := by
        rw [Expr.instantiate1_eq, ← Expr.forallDomainsOnly_instantiate1'_fvar]
        exact HavBody.instantiate1'_fvar id 0
      have HpjBody' : (Expr.forallDomainsOnly n' (body.instantiate1 (.fvar id))).ProjsOK
          (· ∉ r.restorableNames) := by
        rw [Expr.instantiate1_eq, ← Expr.forallDomainsOnly_instantiate1'_fvar]
        exact Hpj.2.instantiate1' Expr.ProjsOK.fvar 0
      rcases ih (by rw [Expr.instantiate1_eq]; exact Htel'.instantiate1' _ 0) houtWF nextMLCtx
          (by simp [nextMLCtx, TypeChecker.MLCtx.lctx, hm]) hnextWF Hbody' HbodyTy
          HavBody' HpjBody' ⟨HavDom, Hpj.1, Hm⟩ with
        ⟨m', tgt, hn, hlctx', hwf', hdrop, hav', Htail, HtailTy, htarget⟩
      have hn' : n' + 1 ≤ m'.length := by
        have := congrArg TypeChecker.MLCtx.length hdrop
        rw [MLCtx.length_dropN] at this
        simp [nextMLCtx] at this
        omega
      refine ⟨m', tgt, hn', hlctx', hwf', ?_, hav', Htail, HtailTy, ?_⟩
      · exact MLCtx.dropN_succ_of_vlam m' n' hn' hdrop
      · rw [MLCtx.mkForall'_succ m' n' hn' tgt hdrop, ← htarget]


/-- Extend the invariant under a binder of any naming, given the
well-formedness of the extended lowered context. -/
theorem RestoreTypedCtx.vlam_wf
    (S : r.Substitution envT envL I)
    (hβ : envT.BetaSubjectReduction U) (H : RestoreTypedCtx r envL envT I U Δs Δt)
    {ofv : Option (FVarId × List FVarId)} {d d' : VExpr}
    (hwfs : VLCtx.WF envL U ((ofv, .vlam d) :: Δs)) (hd : r.expr d = some d')
    (hok : d.ProjNamesOK (· ∉ r.restorableNames)) :
    RestoreTypedCtx r envL envT I U ((ofv, .vlam d) :: Δs) ((ofv, .vlam d') :: Δt) := by
  refine ⟨hwfs, H.rel.vlam, ?_,
    VLCtx.ProjNamesOK.cons H.projs VLocalDecl.value_vlam_projNamesOK⟩
  obtain ⟨u, hu⟩ := hwfs.2.2
  have hΓ := H.onCtxImage
  have Hσ := S.sound.isDefEq (.typed S.ordered) hu hΓ
  have h1 := S.expr_simAt hβ hΓ (RestorationSubstitution.projNamesFixed S hok)
    hd _ Hσ
  exact .succ H.defeq h1

/-! ### Contexts differing only in recorded dependencies -/

/-- Two translation contexts with the same declarations and the same free
variables, whose recorded dependency lists may differ. Lookups and the typing
context ignore the dependency lists. -/
inductive VLCtx.SameUpToDeps : VLCtx → VLCtx → Prop
  | nil : VLCtx.SameUpToDeps [] []
  | none {Δ₁ Δ₂ : VLCtx} {d : VLocalDecl} :
      VLCtx.SameUpToDeps Δ₁ Δ₂ → VLCtx.SameUpToDeps ((none, d) :: Δ₁) ((none, d) :: Δ₂)
  | some {Δ₁ Δ₂ : VLCtx} {d : VLocalDecl} {fv : FVarId} {deps₁ deps₂ : List FVarId} :
      VLCtx.SameUpToDeps Δ₁ Δ₂ →
      VLCtx.SameUpToDeps ((some (fv, deps₁), d) :: Δ₁) ((some (fv, deps₂), d) :: Δ₂)

theorem VLCtx.SameUpToDeps.find? {Δ₁ Δ₂ : VLCtx} (H : VLCtx.SameUpToDeps Δ₁ Δ₂) :
    ∀ v, Δ₁.find? v = Δ₂.find? v := by
  induction H with
  | nil => intro v; rfl
  | none _ ih => intro v; simp only [VLCtx.find?, ih]
  | some _ ih =>
    intro v
    cases v with
    | inl n => simp only [VLCtx.find?, VLCtx.next, ih]
    | inr fv' =>
      simp only [VLCtx.find?, VLCtx.next]
      split <;> simp [ih]

theorem VLCtx.SameUpToDeps.toCtx {Δ₁ Δ₂ : VLCtx} (H : VLCtx.SameUpToDeps Δ₁ Δ₂) :
    Δ₁.toCtx = Δ₂.toCtx := by
  induction H with
  | nil => rfl
  | @none _ _ d _ ih | @some _ _ d _ _ _ _ ih => cases d <;> simp [VLCtx.toCtx, ih]

theorem TrExprS.sameUpToDeps {env : VEnv} {Us : List Name} {Δ₁ Δ₂ : VLCtx}
    {e : Expr} {v : VExpr} (H : TrExprS env Us Δ₁ e v)
    (hΔ : VLCtx.SameUpToDeps Δ₁ Δ₂) : TrExprS env Us Δ₂ e v := by
  induction H generalizing Δ₂ with
  | bvar h => exact .bvar (hΔ.find? _ ▸ h)
  | fvar h => exact .fvar (hΔ.find? _ ▸ h)
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (hΔ.toCtx ▸ h1) (hΔ.toCtx ▸ h2) (ih1 hΔ) (ih2 hΔ)
  | lam h1 _ _ ih1 ih2 => exact .lam (hΔ.toCtx ▸ h1) (ih1 hΔ) (ih2 hΔ.none)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (hΔ.toCtx ▸ h1) (hΔ.toCtx ▸ h2) (ih1 hΔ) (ih2 hΔ.none)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (hΔ.toCtx ▸ h1) (ih1 hΔ) (ih2 hΔ) (ih3 hΔ.none)
  | lit h _ ih => exact .lit h (ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ hp ih => exact .proj (ih hΔ) (hΔ.toCtx ▸ hp)


/-- The binder types of a metacontext, outermost first (lets are skipped). -/
def MLCtx.types : TypeChecker.MLCtx → List VExpr
  | .nil => []
  | .vlam _ _ _ ty' _ c => MLCtx.types c ++ [ty']
  | .vlet _ _ _ _ _ _ c => MLCtx.types c

/-- The free variables of a metacontext, outermost first. -/
def MLCtx.fvarsOuter : TypeChecker.MLCtx → List FVarId
  | .nil => []
  | .vlam id _ _ _ _ c => MLCtx.fvarsOuter c ++ [id]
  | .vlet id _ _ _ _ _ c => MLCtx.fvarsOuter c ++ [id]

theorem MLCtx.mkLambda'_full : ∀ (c : TypeChecker.MLCtx), MLCtxAvoids r c → ∀ (X : VExpr),
    c.mkLambda' c.length (Nat.le_refl _) X = VExpr.wrapLams (MLCtx.types c) X
  | .nil, _, _ => rfl
  | .vlet .., h, _ => h.elim
  | .vlam _ _ _ ty' _ c, ⟨_, _, h⟩, X => by
    simp only [TypeChecker.MLCtx.mkLambda', TypeChecker.MLCtx.length, MLCtx.types]
    rw [MLCtx.mkLambda'_full c h]
    simp [VExpr.wrapLams]

theorem fvarScope_append_single : ∀ (fs : List FVarId) (ds : List VExpr) (f : FVarId)
    (d : VExpr), fs.length = ds.length →
    fvarScope (fs ++ [f]) (ds ++ [d]) = (some (f, []), .vlam d) :: fvarScope fs ds
  | [], [], _, _, _ => by simp [fvarScope]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | f' :: fs, d' :: ds, f, d, h => by
    simp only [List.cons_append, fvarScope]
    rw [fvarScope_append_single fs ds f d (by simpa using h)]
    rfl

theorem MLCtx.types_length : ∀ (c : TypeChecker.MLCtx), MLCtxAvoids r c →
    (MLCtx.types c).length = (MLCtx.fvarsOuter c).length
  | .nil, _ => rfl
  | .vlet .., h => h.elim
  | .vlam _ _ _ _ _ c, ⟨_, _, h⟩ => by
    simp [MLCtx.types, MLCtx.fvarsOuter, MLCtx.types_length c h]

theorem MLCtx.sameUpToDeps_fvarScope : ∀ (c : TypeChecker.MLCtx), MLCtxAvoids r c →
    VLCtx.SameUpToDeps (fvarScope (MLCtx.fvarsOuter c) (MLCtx.types c)) c.vlctx
  | .nil, _ => .nil
  | .vlet .., h => h.elim
  | .vlam _ _ _ _ _ c, ⟨_, _, h⟩ => by
    simp only [MLCtx.fvarsOuter, MLCtx.types, TypeChecker.MLCtx.vlctx]
    rw [fvarScope_append_single _ _ _ _ (MLCtx.types_length c h).symm]
    exact .some (MLCtx.sameUpToDeps_fvarScope c h)

theorem MLCtx.fvarRevList_full_eq : ∀ (c : TypeChecker.MLCtx),
    c.fvarRevList c.length (Nat.le_refl _) = (MLCtx.fvarsOuter c).reverse
  | .nil => rfl
  | .vlam _ _ _ _ _ c | .vlet _ _ _ _ _ _ c => by
    simp [TypeChecker.MLCtx.fvarRevList, MLCtx.fvarsOuter, MLCtx.fvarRevList_full_eq c]

/-- **Restoration of a metacontext of binders**: the binder types translate in
the target environment to the restorations of their lowered translations. -/
theorem MLCtx.restore
    (S : r.Substitution envT envL I)
    {Us : List Name} (hβ : envT.BetaSubjectReduction Us.length)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l) :
    ∀ (ML : TypeChecker.MLCtx), ML.WF envL Us → MLCtxAvoids r ML →
    ∃ MT : TypeChecker.MLCtx, MT.lctx = ML.lctx ∧ MT.WF envT Us ∧
      MT.length = ML.length ∧
      RestoreTypedCtx r envL envT I Us.length ML.vlctx MT.vlctx ∧
      (∀ n hn hn' X Y, r.expr X = some Y →
        r.expr (ML.mkForall' n hn X) = some (MT.mkForall' n hn' Y)) ∧
      (∀ n hn hn' X Y, r.expr X = some Y →
        r.expr (ML.mkLambda' n hn X) = some (MT.mkLambda' n hn' Y)) ∧
      MLCtxAvoids r MT ∧ MLCtx.fvarsOuter MT = MLCtx.fvarsOuter ML ∧
      List.Forall₂ (fun x y => r.expr x = some y) (MLCtx.types ML) (MLCtx.types MT)
  | .nil, _, _ => ⟨.nil, rfl, trivial, rfl, RestoreTypedCtx.nil,
      fun n hn hn' X Y h => by
        cases n with
        | zero => simpa using h
        | succ n => simp at hn,
      fun n hn hn' X Y h => by
        cases n with
        | zero => simpa using h
        | succ n => simp at hn, trivial, rfl, .nil⟩
  | .vlet .., _, h => h.elim
  | .vlam id name ty tyL bi c, hwf, ⟨hav, hprojs, hrest⟩ => by
    obtain ⟨hcwf, hfresh, Hty, HtyType⟩ := hwf
    obtain ⟨MT, hlctx, hMwf, hlen, Hctx, hfor, hlam, havT, hfvT, htysT⟩ :=
      MLCtx.restore S hβ hc Hlits c hcwf hrest
    obtain ⟨tyT, HtyT, hr⟩ := translate_avoids_exists S hβ hc Hlits hav hprojs Hctx Hty
    have hok := Hty.projNamesOK_of_source hprojs Hctx.projs
    refine ⟨.vlam id name ty tyT bi MT, by simp [TypeChecker.MLCtx.lctx, hlctx],
      ⟨hMwf, by rw [hlctx]; exact hfresh, HtyT, Hctx.isType S hβ HtyType hr hok⟩,
      by simp [hlen], ?_, ?_, ?_, ⟨hav, hprojs, havT⟩,
      by simp [MLCtx.fvarsOuter, hfvT], ?_⟩
    · have hwf' : (TypeChecker.MLCtx.vlam id name ty tyL bi c).WF envL Us :=
        ⟨hcwf, hfresh, Hty, HtyType⟩
      exact Hctx.vlam_wf S hβ hwf'.tr.wf hr hok
    · intro n hn hn' X Y h
      cases n with
      | zero => simpa using h
      | succ n =>
        simp only [TypeChecker.MLCtx.mkForall']
        exact hfor n _ _ _ _ (restoration_expr_forallE hr h)
    · intro n hn hn' X Y h
      cases n with
      | zero => simpa using h
      | succ n =>
        simp only [TypeChecker.MLCtx.mkLambda']
        exact hlam n _ _ _ _ (restoration_expr_lam hr h)
    · simp only [MLCtx.types]
      exact List.Forall₂.append' htysT (.cons hr .nil)


theorem MLCtx.eq_nil_of_length : ∀ {c : TypeChecker.MLCtx}, c.length = 0 → c = .nil
  | .nil, _ => rfl

theorem MLCtx.dropN_length_eq_nil (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length)
    (hn : c.length = n) : c.dropN n h = .nil :=
  MLCtx.eq_nil_of_length (by rw [MLCtx.length_dropN]; omega)

/-- **Restoration of a closed forall telescope translates.** The lowered
input is opened at restoration's parameters, its body restored by
`restorationTranslates`, and the output closed over the restored parameter
domains (which the executable copies verbatim). -/
theorem NestedRestorationOpening.translatesForall
    (S : r.Substitution envT envL I)
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us : List Name} {auxLevels : List Level}
    {input output suffix : Expr} {s : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (hLwf : envL.WF) (hTwf : envT.WF) (hβ : envT.BetaSubjectReduction Us.length)
    (A : RestorationMapAgreement r result env auxRec envT Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l)
    (Hlitnames : ∀ l : Literal, l.toConstructor.AvoidsConsts r.restorableNames)
    (Hheads : ∀ MT : TypeChecker.MLCtx, MT.lctx = Hopen.lctx → MT.WF envT Us →
      RestoreHeadsTranslate r result env envT Us auxLevels Hopen.params MT.vlctx)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hav : (Expr.forallDomainsOnly result.nparams input).AvoidsConsts r.restorableNames)
    (Hpj : (Expr.forallDomainsOnly result.nparams input).ProjsOK (· ∉ r.restorableNames))
    (Hshape : Hopen.body.ParamUniform (r.heads.map (·.auxiliary)) Hopen.params.toList auxLevels)
    (Htrail : Hopen.body.TrailingArgs (r.heads.map (·.auxiliary)) result.nparams
      (·.AvoidsConsts r.restorableNames))
    (Hprojs : Hopen.body.ProjsOK (· ∉ r.restorableNames))
    (Hrestored : Closed Hopen.restoredBody)
    (Hs : TrExprS envL Us [] input s) (HsTy : envL.IsType Us.length [] s) :
    ∃ t, TrExprS envT Us [] output t ∧ envT.IsType Us.length [] t ∧ r.expr s = some t := by
  rcases ParamOpening.toMLCtxForall hLwf (r := r) Hopen.opening Htel Hopen.lctxWF
      .nil rfl trivial Hs HsTy Hav Hpj trivial with
    ⟨ML, sR, hn, hML, hMLwf, hdrop, havML, HsR, HsRTy, hs⟩
  have hMLlen : ML.length = result.nparams := by
    have := MLCtx.length_dropN ML result.nparams hn
    rw [hdrop] at this
    simp at this
    omega
  rcases MLCtx.restore S hβ hc Hlits ML hMLwf havML with
    ⟨MT, hMT, hMTwf, hlen, Hctx, hfor, -, -, -, -⟩
  have hn' : result.nparams ≤ MT.length := by omega
  have hparams := Hopen.selection.expressions
  have hlenSel : Hopen.selection.fvars.length = result.nparams :=
    Hopen.selection.size.symm.trans Hopen.opening.initial_size
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    simp at ha
    rcases ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := Hopen.opening.initial_size
  rcases restorationTranslates S hLwf.ordered hβ A hc HAs hsize Hlits Hlitnames
      (Hheads MT (hMT.trans hML) hMTwf) Hshape Htrail Hprojs Hctx ⟨0, 0, .refl⟩ HsR with
    ⟨tR, HtR, hr⟩
  rw [← Hopen.replacement.eq_replace] at HtR
  have hokR := HsR.projNamesOK_of_source Hprojs Hctx.projs
  have HtRTy := Hctx.isType S hβ HsRTy hr hokR
  have Hclose := hMTwf.mkForall_trS hTwf HtR HtRTy result.nparams hn'
  rw [MLCtx.dropN_length_eq_nil MT result.nparams hn' (by omega)] at Hclose
  have harr : Hopen.params.toList.reverse =
      (MT.fvarRevList result.nparams hn').map Expr.fvar := by
    have hall : MT.fvarRevList result.nparams hn' = MT.vlctx.fvars := by
      have key : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length), n = c.length →
          c.fvarRevList n h = c.vlctx.fvars := by
        rintro c n h rfl; exact c.fvarRevList_all
      exact key MT _ hn' (by omega)
    rw [hall, ← hMTwf.tr.fvars_eq, hMT, hML]
    exact Hopen.opening.root_params_reverse_fvars
  have houtput : output = MT.mkForall result.nparams hn' Hopen.restoredBody := by
    have h1 := hMTwf.mkForall_eq result.nparams hn' harr Hrestored
    rw [hMT, hML] at h1
    refine Hopen.output_eq.trans ?_
    rw [← h1]
    cases hk : result.nparams with
    | zero =>
      have hsize0 : Hopen.params.size = 0 := by rw [hsize, hk]
      have hnil : Hopen.params = #[] := Array.size_eq_zero_iff.mp hsize0
      have hlambda : Hopen.lctx.mkLambda #[] Hopen.restoredBody = Hopen.restoredBody := by
        rw [LocalContext.mkLambda]
        change LocalContext.mkBinding true Hopen.lctx
          (([] : List FVarId).map Expr.fvar).toArray Hopen.restoredBody =
            Hopen.restoredBody
        rw [LocalContext.mkBinding_eqN]
        exact LocalContext.mkBindingListN_nil
      rw [hnil]
      split
      · rfl
      · rw [hlambda, LocalContext.mkForall_empty]
    | succ k =>
      have hfor : input.isForall = true := Htel.isForall_of_pos (by omega)
      simp [hfor]
  refine ⟨_, houtput ▸ Hclose.1, Hclose.2, ?_⟩
  rw [hs]
  exact hfor _ _ _ _ _ hr


/-- Lambda counterpart of `ParamOpening.toMLCtxForall`. -/
theorem ParamOpening.toMLCtxLambda {env : VEnv} {Us : List Name}
    (henv : env.WF) {r : Restoration}
    {lctx : LocalContext} {As : Array Expr} {e : Expr} {n : Nat}
    {outLctx : LocalContext} {outAs : Array Expr} {tail residual : Expr}
    (Hopen : ParamOpening lctx As e n outLctx outAs tail)
    (Htel : Expr.LambdaTelescope e n residual)
    (houtWF : outLctx.WF)
    (m : TypeChecker.MLCtx) (hm : m.lctx = lctx) (hmWF : m.WF env Us)
    {target : VExpr} (He : TrExprS env Us m.vlctx e target)
    (Hav : (Expr.lamDomainsOnly n e).AvoidsConsts r.restorableNames)
    (Hpj : (Expr.lamDomainsOnly n e).ProjsOK (· ∉ r.restorableNames))
    (Hm : MLCtxAvoids r m) :
    ∃ (m' : TypeChecker.MLCtx) (tgt : VExpr) (hn : n ≤ m'.length),
      m'.lctx = outLctx ∧ m'.WF env Us ∧ m'.dropN n hn = m ∧ MLCtxAvoids r m' ∧
      TrExprS env Us m'.vlctx tail tgt ∧
      target = m'.mkLambda' n hn tgt := by
  induction Hopen generalizing m target residual with
  | done => exact ⟨m, target, Nat.zero_le _, hm, hmWF, rfl, Hm, He, rfl⟩
  | forallE Hnext ih => cases Htel
  | lam Hnext ih =>
    rename_i n' outLctx' outAs' tail' lctx' As' name dom body bi id
    cases Htel with
    | cons Htel' =>
    cases He with
    | lam HdomainType Hdomain Hbody =>
      rename_i domainTarget bodyTarget
      have hcurrentWF : lctx'.WF := hm ▸ hmWF.tr.1
      have hidFresh : lctx'.find? id = none := by
        rcases Hnext.context_extension with
          ⟨decls, hlctx, _hparams, _hlength⟩
        have hnodup := houtWF.nodup
        rw [hlctx, List.map_append] at hnodup
        simp only [LocalContext.mkLocalDecl_toList, List.map_cons,
          LocalDecl.fvarId] at hnodup
        have hidNotMem : id ∉ lctx'.toList.map (fun d => d.fvarId) := by
          exact (List.nodup_cons.mp
            (List.nodup_append.mp hnodup).2.1).1
        rw [hcurrentWF.find?_eq_find?_toList]
        exact List.find?_eq_none.mpr (by
          intro decl hdecl hmatch
          have hfv : decl.fvarId = id := (LawfulBEq.eq_of_beq hmatch).symm
          exact hidNotMem (List.mem_map.mpr ⟨decl, hdecl, hfv⟩))
      let nextMLCtx := TypeChecker.MLCtx.vlam id name dom domainTarget bi m
      have hnextWF : nextMLCtx.WF env Us :=
        ⟨hmWF, by simpa [nextMLCtx, hm] using hidFresh,
          Hdomain, HdomainType⟩
      have Hbody' : TrExprS env Us nextMLCtx.vlctx
          (body.instantiate1 (.fvar id)) bodyTarget := by
        rw [Expr.instantiate1_eq]
        exact Hbody.inst_fvar henv.ordered hnextWF.tr.wf
      simp only [Expr.lamDomainsOnly] at Hav Hpj
      cases Hav with
      | lam _ _ _ _ HavDom HavBody =>
      have HavBody' : (Expr.lamDomainsOnly n' (body.instantiate1 (.fvar id))).AvoidsConsts
          r.restorableNames := by
        rw [Expr.instantiate1_eq, ← Expr.lamDomainsOnly_instantiate1'_fvar]
        exact HavBody.instantiate1'_fvar id 0
      have HpjBody' : (Expr.lamDomainsOnly n' (body.instantiate1 (.fvar id))).ProjsOK
          (· ∉ r.restorableNames) := by
        rw [Expr.instantiate1_eq, ← Expr.lamDomainsOnly_instantiate1'_fvar]
        exact Hpj.2.instantiate1' Expr.ProjsOK.fvar 0
      rcases ih (by rw [Expr.instantiate1_eq]; exact Htel'.instantiate1' _ 0) houtWF nextMLCtx
          (by simp [nextMLCtx, TypeChecker.MLCtx.lctx, hm]) hnextWF Hbody'
          HavBody' HpjBody' ⟨HavDom, Hpj.1, Hm⟩ with
        ⟨m', tgt, hn, hlctx', hwf', hdrop, hav', Htail, htarget⟩
      have hn' : n' + 1 ≤ m'.length := by
        have := congrArg TypeChecker.MLCtx.length hdrop
        rw [MLCtx.length_dropN] at this
        simp [nextMLCtx] at this
        omega
      refine ⟨m', tgt, hn', hlctx', hwf', ?_, hav', Htail, ?_⟩
      · exact MLCtx.dropN_succ_of_vlam m' n' hn' hdrop
      · rw [MLCtx.mkLambda'_succ m' n' hn' tgt hdrop, ← htarget]

/-- **Restoration of a closed lambda telescope translates** (the
counterpart of `translatesForall` for rule right-hand sides). -/
theorem NestedRestorationOpening.translatesLambda
    (S : r.Substitution envT envL I)
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us : List Name} {auxLevels : List Level}
    {input output suffix : Expr} {s : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (hLwf : envL.WF) (hTwf : envT.WF) (hβ : envT.BetaSubjectReduction Us.length)
    (A : RestorationMapAgreement r result env auxRec envT Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l)
    (Hlitnames : ∀ l : Literal, l.toConstructor.AvoidsConsts r.restorableNames)
    (Hheads : ∀ (Ds Dt : List VExpr) (Δt0 : VLCtx) (sR : VExpr),
      s = VExpr.wrapLams Ds sR → Ds.length = result.nparams →
      List.Forall₂ (fun x y => r.expr x = some y) Ds Dt →
      VLCtx.SameUpToDeps (fvarScope Hopen.selection.fvars Dt) Δt0 →
      RestoreHeadsTranslate r result env envT Us auxLevels Hopen.params Δt0)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (Hav : (Expr.lamDomainsOnly result.nparams input).AvoidsConsts r.restorableNames)
    (Hpj : (Expr.lamDomainsOnly result.nparams input).ProjsOK (· ∉ r.restorableNames))
    (Hshape : Hopen.body.ParamUniform (r.heads.map (·.auxiliary)) Hopen.params.toList auxLevels)
    (Htrail : Hopen.body.TrailingArgs (r.heads.map (·.auxiliary)) result.nparams
      (·.AvoidsConsts r.restorableNames))
    (Hprojs : Hopen.body.ProjsOK (· ∉ r.restorableNames))
    (Hrestored : Closed Hopen.restoredBody)
    (Hs : TrExprS envL Us [] input s) :
    ∃ t, TrExprS envT Us [] output t ∧ VExpr.WF envT Us.length [] t ∧
      r.expr s = some t := by
  rcases ParamOpening.toMLCtxLambda hLwf (r := r) Hopen.opening Htel Hopen.lctxWF
      .nil rfl trivial Hs Hav Hpj trivial with
    ⟨ML, sR, hn, hML, hMLwf, hdrop, havML, HsR, hs⟩
  have hMLlen : ML.length = result.nparams := by
    have := MLCtx.length_dropN ML result.nparams hn
    rw [hdrop] at this
    simp at this
    omega
  rcases MLCtx.restore S hβ hc Hlits ML hMLwf havML with
    ⟨MT, hMT, hMTwf, hlen, Hctx, -, hlam, havMT, hfvMT, htysMT⟩
  have hn' : result.nparams ≤ MT.length := by omega
  have hparams := Hopen.selection.expressions
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    simp at ha
    rcases ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := Hopen.opening.initial_size
  have harr : Hopen.params.toList.reverse =
      (MT.fvarRevList result.nparams hn').map Expr.fvar := by
    have hall : MT.fvarRevList result.nparams hn' = MT.vlctx.fvars := by
      have key : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length), n = c.length →
          c.fvarRevList n h = c.vlctx.fvars := by
        rintro c n h rfl; exact c.fvarRevList_all
      exact key MT _ hn' (by omega)
    rw [hall, ← hMTwf.tr.fvars_eq, hMT, hML]
    exact Hopen.opening.root_params_reverse_fvars
  have hfvOuter : MLCtx.fvarsOuter MT = Hopen.selection.fvars := by
    have key : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length), n = c.length →
        c.fvarRevList n h = (MLCtx.fvarsOuter c).reverse := by
      rintro c n h rfl; exact MLCtx.fvarRevList_full_eq c
    have h1 := harr
    rw [key MT _ hn' (by omega), hparams] at h1
    simp only [List.map_reverse] at h1
    have h2 := congrArg List.reverse h1
    simp only [List.reverse_reverse] at h2
    exact ((List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp h2).symm
  have hDs : s = VExpr.wrapLams (MLCtx.types ML) sR := by
    rw [hs]
    have key : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length), n = c.length →
        MLCtxAvoids r c → c.mkLambda' n h sR = VExpr.wrapLams (MLCtx.types c) sR := by
      rintro c n h rfl hc; exact MLCtx.mkLambda'_full c hc sR
    exact key ML _ hn (by omega) havML
  have hDsLen : (MLCtx.types ML).length = result.nparams := by
    rw [MLCtx.types_length ML havML]
    have key : ∀ (c : TypeChecker.MLCtx), (MLCtx.fvarsOuter c).length = c.length := by
      intro c; induction c <;> simp [MLCtx.fvarsOuter, *]
    rw [key]; omega
  have Hheads' := Hheads (MLCtx.types ML) (MLCtx.types MT) MT.vlctx sR hDs hDsLen htysMT
    (by rw [← hfvOuter]; exact MLCtx.sameUpToDeps_fvarScope MT havMT)
  rcases restorationTranslates S hLwf.ordered hβ A hc HAs hsize Hlits Hlitnames
      Hheads' Hshape Htrail Hprojs Hctx ⟨0, 0, .refl⟩ HsR with
    ⟨tR, HtR, hr⟩
  rw [← Hopen.replacement.eq_replace] at HtR
  have hokR := HsR.projNamesOK_of_source Hprojs Hctx.projs
  obtain ⟨T, HtRTy⟩ := Hctx.wf S hβ (HsR.wf hLwf.ordered Hctx.wfs) hr hokR
  have Hclose := hMTwf.mkLambda_trS hTwf HtR HtRTy result.nparams hn'
  rw [MLCtx.dropN_length_eq_nil MT result.nparams hn' (by omega)] at Hclose
  have harr : Hopen.params.toList.reverse =
      (MT.fvarRevList result.nparams hn').map Expr.fvar := by
    have hall : MT.fvarRevList result.nparams hn' = MT.vlctx.fvars := by
      have key : ∀ (c : TypeChecker.MLCtx) (n : Nat) (h : n ≤ c.length), n = c.length →
          c.fvarRevList n h = c.vlctx.fvars := by
        rintro c n h rfl; exact c.fvarRevList_all
      exact key MT _ hn' (by omega)
    rw [hall, ← hMTwf.tr.fvars_eq, hMT, hML]
    exact Hopen.opening.root_params_reverse_fvars
  have houtput : output = MT.mkLambda result.nparams hn' Hopen.restoredBody := by
    have h1 := hMTwf.mkLambda_eq result.nparams hn' harr Hrestored
    rw [hMT, hML] at h1
    refine Hopen.output_eq.trans ?_
    rw [← h1]
    cases hk : result.nparams with
    | zero =>
      have hsize0 : Hopen.params.size = 0 := by rw [hsize, hk]
      have hnil : Hopen.params = #[] := Array.size_eq_zero_iff.mp hsize0
      have hlambda : Hopen.lctx.mkLambda #[] Hopen.restoredBody = Hopen.restoredBody := by
        rw [LocalContext.mkLambda]
        change LocalContext.mkBinding true Hopen.lctx
          (([] : List FVarId).map Expr.fvar).toArray Hopen.restoredBody =
            Hopen.restoredBody
        rw [LocalContext.mkBinding_eqN]
        exact LocalContext.mkBindingListN_nil
      rw [hnil]
      split
      · rw [hlambda, LocalContext.mkForall_empty]
      · rfl
    | succ k =>
      have hnotFor : input.isForall = false := by
        have Htel' := Htel
        rw [hk] at Htel'
        cases Htel'
        rfl
      simp [hnotFor]
  refine ⟨_, houtput ▸ Hclose.1, ⟨_, Hclose.2⟩, ?_⟩
  rw [hs]
  exact hlam _ _ _ _ _ hr


end VerifyInductive
end Lean4Lean
