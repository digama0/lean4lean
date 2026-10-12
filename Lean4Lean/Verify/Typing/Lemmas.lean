import Batteries.Data.String.Lemmas
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Verify.Typing.PrimSpec
import Lean4Lean.Verify.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ConstructorCaptureTransport
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Instantiate
import Lean4Lean.Verify.Typing.Syntactic.TypedAPI

namespace Lean4Lean
open Lean4Lean VEnv Lean
open scoped _root_.List


variable! (henv : OrderedStrong env) in
theorem TrExprS.weakFV' (W : VLCtx.FVLift' Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ e e') : TrExprS env Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? hΔ'.fvars_nodup h1)
  | fvar h1 => exact .fvar (W.find? hΔ'.fvars_nodup h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx) (ih1 W hΔ') (ih2 W hΔ')
  | lam h1 _ _ ih1 ih2 =>
    have h1 := h1.weak' henv W.toCtx
    exact .lam h1 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    have h1 := h1.weak' henv W.toCtx
    have h2 := h2.weak' henv W.toCtx.cons
    exact .forallE h1 h2 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    have h1 := h1.weak' henv W.toCtx
    exact .letE h1 (ih1 W hΔ') (ih2 W hΔ') (ih3 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | lit h1 _ ih => exact .lit h1 (ih W hΔ')
  | mdata _ ih => exact .mdata (ih W hΔ')
  | proj _ h2 ih => exact .proj (ih W hΔ') (h2.weak' henv W.toCtx)

variable! (henv : WF env) in
theorem TrExpr.weakFV' (W : VLCtx.FVLift' Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExpr env Us Δ e e') : TrExpr env Us Δ' e (e'.lift' (n.consN k)) :=
  let ⟨_, H1, H2⟩ := H
  ⟨_, H1.weakFV' henv W hΔ', H2.weak' henv W.toCtx⟩

variable! (henv : OrderedStrong env) in
theorem TrExprS.weakFV (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ e e') : TrExprS env Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using H.weakFV' henv W.toFVLift' hΔ'

variable! (henv : WF env) in
theorem TrExpr.weakFV (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExpr env Us Δ e e') : TrExpr env Us Δ' e (e'.liftN n k) :=
  let ⟨_, H1, H2⟩ := H
  ⟨_, H1.weakFV henv W hΔ', H2.weakN henv W.toCtx⟩

variable! (henv : OrderedStrong env) in
theorem TrExprS.weakBV (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrExprS env Us Δ e e') : TrExprS env Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? h1)
  | fvar h1 => exact .fvar (W.find? h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.weakN henv W.toCtx) (ih1 W) (ih2 (W.cons _))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx.succ) (ih1 W) (ih2 (W.cons _))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.weakN henv W.toCtx) (ih1 W) (ih2 W) (ih3 (W.cons _))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (h2.weakN henv W.toCtx)

variable! (henv : WF env) in
theorem TrExpr.weakBV (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrExpr env Us Δ e e') : TrExpr env Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) :=
  let ⟨_, H1, H2⟩ := H
  ⟨_, H1.weakBV henv W, H2.weakN henv W.toCtx⟩

/-- A well-formed primitive projection stays well formed when its major is replaced by a
definitionally equal one in a definitionally equal context. -/
theorem VExpr.WF.proj_defeqDFC (henv : VEnv.WF env) (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (he : env.IsDefEqU U Γ₁ e₁ e₂)
    (H : VExpr.WF env U Γ₁ (.proj s i e₁)) :
    VExpr.WF env U Γ₂ (.proj s i e₂) := by
  have hΓ₂ : OnCtx Γ₂ (env.IsType U) := (hΓ.symm henv.orderedStrong).isType
  obtain ⟨_, he₂'⟩ := he.defeqDFC henv.orderedStrong hΓ
  obtain ⟨resultType, htarget⟩ := H
  obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType,
      fieldLevel, hinfo, hlevels, huvars, hparams, hindices, hfield,
      hfieldTyping, hsource, hclosed, hguard⟩ :=
    HasType.proj_inv henv.orderedStrong hΓ.isType htarget
  have hfieldTyping₂ := hfieldTyping.defeqDFC henv.orderedStrong hΓ
  have hsource₂ := hsource.defeqDFC henv.orderedStrong hΓ
  have hsourceMajor₂ := hsource₂.trans_l henv hΓ₂ he₂'
  exact ⟨fieldType, .projDF hinfo hlevels huvars hparams hindices
    hfield hfieldTyping₂ hsourceMajor₂ hsourceMajor₂ hclosed hguard⟩

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem TrExprS.mono (H : TrExprS env Us Δ e e') : TrExprS env' Us Δ e e' := by
  induction H with
  | bvar h1 => exact .bvar h1
  | fvar h1 => exact .fvar h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const (henv.1 h1) h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app (h1.mono henv) (h2.mono henv) ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.mono henv) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE (h1.mono henv) (h2.mono henv) ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 => exact .letE (h1.mono henv) ih1 ih2 ih3
  | lit h1 _ ih => refine .lit (h1.mono henv) ih
  | mdata _ ih => exact .mdata ih
  | proj _ h2 ih => exact .proj ih (h2.mono henv)

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem TrExpr.mono (H : TrExpr env Us Δ e e') : TrExpr env' Us Δ e e' :=
  let ⟨_, H1, H2⟩ := H; ⟨_, H1.mono henv, H2.mono henv⟩

theorem VLocalDecl.IsDefEq.mono
    {env env' : VEnv} (henv : env ≤ env')
    (H : VLocalDecl.IsDefEq env U Γ d₁ d₂) :
    VLocalDecl.IsDefEq env' U Γ d₁ d₂ := by
  cases H with
  | vlam h => exact .vlam (h.mono henv)
  | vlet hv ht => exact .vlet (hv.mono henv) (ht.mono henv)

variable! (env : VEnv) (U : Nat) in
inductive VLCtx.IsDefEq : VLCtx → VLCtx → Prop
  | nil : VLCtx.IsDefEq [] []
  | cons {Δ₁ Δ₂ : VLCtx} :
    VLCtx.IsDefEq Δ₁ Δ₂ →
    (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ₁.fvars ∧ deps ⊆ Δ₁.fvars) →
    VLocalDecl.IsDefEq env U Δ₁.toCtx d₁ d₂ →
    VLCtx.IsDefEq ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem VLCtx.IsDefEq.mono {env env' : VEnv} (henv : env ≤ env')
    (H : VLCtx.IsDefEq env U Δ₁ Δ₂) :
    VLCtx.IsDefEq env' U Δ₁ Δ₂ := by
  induction H with
  | nil => exact .nil
  | cons hctx hfresh hdecl ih =>
    exact .cons ih hfresh (hdecl.mono henv)

variable! (henv : OrderedStrong env) (hΓ : OnCtx Γ (IsType env U)) in
theorem VLocalDecl.IsDefEq.refl : ∀ {d}, VLocalDecl.WF env U Γ d → VLocalDecl.IsDefEq env U Γ d d
  | .vlam _, ⟨_, h1⟩ => .vlam h1
  | .vlet .., h1 => let ⟨_, h2⟩ := h1.isType henv hΓ; .vlet h1 h2

variable! (henv : OrderedStrong env) in
theorem VLCtx.IsDefEq.refl : ∀ {Δ}, VLCtx.WF env U Δ → VLCtx.IsDefEq env U Δ Δ
  | [], _ => .nil
  | (_, _) :: _, ⟨h1, h2, h3⟩ => .cons (IsDefEq.refl h1) h2 (.refl henv h1.toCtx h3)

theorem VLCtx.IsDefEq.defeqCtx : VLCtx.IsDefEq env U Δ₁ Δ₂ → env.IsDefEqCtx U [] Δ₁.toCtx Δ₂.toCtx
  | .nil => .zero
  | .cons h1 _ (.vlam h2) => .succ h1.defeqCtx h2
  | .cons h1 _ (.vlet ..) => h1.defeqCtx

/-- A conversion between ordinary typing contexts induces a conversion
between their completely anonymous verifier contexts. -/
theorem VLCtx.IsDefEq.ofDefEqCtxAnonymous
    (H : VEnv.IsDefEqCtx env U [] left right) :
    VLCtx.IsDefEq env U
      (left.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl))
      (right.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) := by
  induction H with
  | zero => exact .nil
  | succ H Htype ih =>
    exact .cons ih (by simp) (.vlam (by simpa using Htype))

theorem VLCtx.IsDefEq.fvars : VLCtx.IsDefEq env U Δ₁ Δ₂ → Δ₁.fvars = Δ₂.fvars
  | .nil => by simp
  | .cons (ofv := none) h1 h2 _ => h1.fvars
  | .cons (ofv := some fv) h1 h2 _ => by simp [h1.fvars]

theorem VLocalDecl.IsDefEq.wf : VLocalDecl.IsDefEq env U Γ d₁ d₂ → VLocalDecl.WF env U Γ d₁
  | .vlam h3 => ⟨_, h3.hasType.1⟩
  | .vlet h3 _ => h3.hasType.1

theorem VLCtx.IsDefEq.wf : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.WF env U Δ₁
  | .nil => ⟨⟩
  | .cons h1 h2 h3 => ⟨h1.wf, h2, h3.wf⟩

theorem VLocalDecl.IsDefEq.symm :
    VLocalDecl.IsDefEq env U Δ d₁ d₂ → VLocalDecl.IsDefEq env U Δ d₂ d₁
  | .vlam h1 => .vlam h1.symm
  | .vlet h1 h2 => .vlet (h2.defeqDF h1.symm) h2.symm

theorem VLocalDecl.IsDefEq.defeqDFC (henv : OrderedStrong env) (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    : VLocalDecl.IsDefEq env U Γ₁ d₁ d₂ → VLocalDecl.IsDefEq env U Γ₂ d₁ d₂
  | .vlam h1 => .vlam (h1.defeqDFC henv hΓ)
  | .vlet h1 h2 => .vlet (h1.defeqDFC henv hΓ) (h2.defeqDFC henv hΓ)

variable! (henv : OrderedStrong env) in
theorem VLCtx.IsDefEq.symm : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.IsDefEq env U Δ₂ Δ₁
  | .nil => .nil
  | .cons h1 h2 h3 =>
    .cons h1.symm (by simpa [h1.fvars] using h2) (h3.symm.defeqDFC henv h1.defeqCtx)

variable! (henv : VEnv.WF env) in
theorem VLCtx.IsDefEq.find?_uniq (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) :
    env.IsDefEqU U Δ₁.toCtx A₁ A₂ ∧ env.IsDefEq U Δ₁.toCtx e₁ e₂ A₁ := by
  let .cons hΔ h1 h2 := hΔ
  match h2 with
  | .vlam (type₁ := A₁) (type₂ := A₂) h2 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h2.weak henv⟩, .bvar .zero⟩
    · simp
      rintro d₁' n₁' H1' rfl rfl d₂' n₂' H2' rfl rfl
      obtain ⟨h2, h3⟩ := find?_uniq hΔ H1' H2'
      exact ⟨h2.weakN henv .one, h3.weak henv⟩
  | .vlet h3 h4 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h4⟩, h3⟩
    · simp
      rintro d₁' n₁' H1' rfl rfl d₂' n₂' H2' rfl rfl
      simpa [VLocalDecl.depth, VLCtx.toCtx] using find?_uniq hΔ H1' H2'

theorem VLCtx.IsDefEq.find?_defeqDFC (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂)
    (H : Δ₁.find? v = some (e₁, A₁)) :
    ∃ e₂ A₂, Δ₂.find? v = some (e₂, A₂) := by
  let .cons hΔ _ _ := hΔ
  revert H; unfold VLCtx.find?; split
  · exact fun _ => ⟨_, _, rfl⟩
  · simp; rintro e A H rfl rfl
    obtain ⟨_, _, H⟩ := find?_defeqDFC hΔ H
    exact ⟨_, _, _, _, H, rfl, rfl⟩

theorem TrExprS.closed (H : TrExprS env Us Δ e e') : Closed e Δ.bvars := H.toTrSyn.closed

theorem TrExprS.fvarsIn (H : TrExprS env Us Δ e e') : FVarsIn (· ∈ Δ.fvars) e :=
  H.toTrSyn.fvarsIn

theorem TrExprS.fvarsList (H : TrExprS env Us Δ e e') : e.fvarsList ⊆ Δ.fvars :=
  (fvarsIn_iff.1 H.fvarsIn).1

theorem TrExpr.closed (H : TrExpr env Us Δ e e') : Closed e Δ.bvars :=
  let ⟨_, H, _⟩ := H; H.closed

theorem TrExpr.fvarsIn (H : TrExpr env Us Δ e e') : FVarsIn (· ∈ Δ.fvars) e :=
  let ⟨_, H, _⟩ := H; H.fvarsIn

theorem TrExpr.fvarsList (H : TrExpr env Us Δ e e') : e.fvarsList ⊆ Δ.fvars :=
  (fvarsIn_iff.1 H.fvarsIn).1

theorem TrExpr.wf (H : TrExpr env Us Δ e e') : VExpr.WF env Us.length Δ.toCtx e' :=
  let ⟨_, _, _, H⟩ := H; ⟨_, H.hasType.2⟩

variable! (henv : OrderedStrong env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
theorem TrExprS.trExpr (H : TrExprS env Us Δ e e') : TrExpr env Us Δ e e' :=
  ⟨_, H, H.wf henv hΔ⟩

theorem TrExpr.defeq (henv : VEnv.WF env) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    (h1 : TrExpr env Us Δ e e₁) (h2 : env.IsDefEqU Us.length Δ.toCtx e₁ e₂) :
    TrExpr env Us Δ e e₂ := let ⟨_, H, h1⟩ := h1; ⟨_, H, h1.trans henv hΔ h2⟩

theorem TrExpr.app (henv : VEnv.WF env) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    (h1 : env.HasType Us.length Δ.toCtx f' (.forallE A B))
    (h2 : env.HasType Us.length Δ.toCtx a' A)
    (h3 : TrExpr env Us Δ f f')
    (h4 : TrExpr env Us Δ a a') :
    TrExpr env Us Δ (.app f a) (.app f' a') :=
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, h4⟩ := h4
  have h3 := h3.of_r henv hΔ h1
  have h4 := h4.of_r henv hΔ h2
  ⟨_, .app h3.hasType.1 h4.hasType.1 s3 s4, _, h3.appDF h4⟩

variable! (henv : VEnv.WF env) (hΓ : IsDefEqCtx env U [] Γ₁ Γ₂) in
/-- Primitive projections of definitionally equal majors are definitionally equal. -/
theorem VExpr.WF.proj_uniq
    (H1 : VExpr.WF env U Γ₁ (.proj s i e₁))
    (H : env.IsDefEqU U Γ₁ e₁ e₂) :
    env.IsDefEqU U Γ₁ (.proj s i e₁) (.proj s i e₂) := by
  obtain ⟨resultType, htarget⟩ := H1
  obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType,
      fieldLevel, hinfo, hlevels, huvars, hparams, hindices, hfield,
      hfieldTyping, hsource, hclosed, hguard⟩ :=
    HasType.proj_inv henv.orderedStrong hΓ.isType htarget
  have hsourceMajor₂ := hsource.transU_l henv hΓ.isType H
  exact ⟨fieldType, .projDF hinfo hlevels huvars hparams hindices hfield
    hfieldTyping hsource hsourceMajor₂ hclosed hguard⟩

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExprS.uniq (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) :
    env.IsDefEqU Us.length Δ₁.toCtx e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with
  | bvar l1 => let .bvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 => let .fvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 =>
    let .sort r1 := H2; cases l1.symm.trans r1; exact ⟨_, HasType.sort (.of_ofLevel l1)⟩
  | const l1 l2 l3 =>
    let .const r1 r2 r3 := H2; cases l1.symm.trans r1; cases l2.symm.trans r2
    exact (TrExprS.const l1 l2 l3).wf henv hΔ.wf
  | app l1 l2 _ _ ih3 ih4 =>
    let .app _ _ r3 r4 := H2
    exact ⟨_, .appDF
      (ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1)
      (ih4 hΔ r4 |>.of_l henv hΔ.wf.toCtx l2)⟩
  | lam l1 _ _ ih2 ih3 =>
    let ⟨_, l1⟩ := l1; let .lam _ r2 r3 := H2
    have hA := ih2 hΔ r2 |>.of_l henv hΔ.wf.toCtx l1
    have ⟨_, hb⟩ := ih3 (hΔ.cons nofun <| .vlam hA) r3
    exact ⟨_, .lamDF hA hb⟩
  | forallE l1 l2 _ _ ih3 ih4 =>
    let ⟨_, l1'⟩ := l1; let ⟨_, l2⟩ := l2; let .forallE _ _ r3 r4 := H2
    have hA := ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (hΔ.cons nofun <| .vlam hA) r4 |>.of_l (Γ := _::_) henv ⟨hΔ.wf.toCtx, l1⟩ l2
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    have hΓ := hΔ.wf.toCtx
    let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    refine ih4 (hΔ.cons nofun ?_) r4
    exact .vlet (ih3 hΔ r3 |>.of_l henv hΓ l1) (ih2 hΔ r2 |>.of_l henv hΓ hb)
  | lit _ _ ih1 => let .lit _ r2 := H2; exact ih1 hΔ r2
  | mdata _ ih1 => let .mdata r1 := H2; exact ih1 hΔ r1
  | proj _ l2 ih1 => let .proj r1 _ := H2; exact l2.proj_uniq henv hΔ.defeqCtx (ih1 hΔ r1)

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExpr.uniq (H1 : TrExpr env Us Δ₁ e e₁) (H2 : TrExpr env Us Δ₂ e e₂) :
    env.IsDefEqU Us.length Δ₁.toCtx e₁ e₂ := by
  let ⟨_, H1, eq1⟩ := H1
  let ⟨_, H2, eq2⟩ := H2
  exact eq1.symm.trans henv hΔ.wf <| (H1.uniq henv hΔ H2).trans henv hΔ.wf <|
    eq2.defeqDFC henv (hΔ.defeqCtx.symm henv)

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExprS.defeqDFC (H : TrExprS env Us Δ₁ e e₁) : ∃ e₂, TrExprS env Us Δ₂ e e₂ := by
  induction H generalizing Δ₂ with
  | bvar h1 => have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1; exact ⟨_, .bvar h1⟩
  | fvar h1 => have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1; exact ⟨_, .fvar h1⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h3'⟩ := ih3 hΔ
    let ⟨_, h4'⟩ := ih4 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h3'.uniq henv (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ.symm henv).wf (h4'.uniq henv (hΔ.symm henv) h4).symm
    exact ⟨_, .app h1 h2 h3' h4'⟩
  | lam h1 h2 h3 ih2 ih3 =>
    let ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := ih2 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h2'.uniq henv (hΔ.symm henv) h2).symm
    have ht := (h2.uniq henv hΔ h2').of_l henv hΔ.wf h1'
    let ⟨_, h3'⟩ := ih3 (hΔ.cons nofun <| .vlam ht)
    exact ⟨_, .lam h1 h2' h3'⟩
  | forallE h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := h2
    let ⟨_, h3'⟩ := ih3 hΔ
    have ht := (h3.uniq henv hΔ h3').of_l henv hΔ.wf h1'
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlam ht)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv (hΔ.defeqCtx.succ ht)
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h3'.uniq henv (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ'.symm henv).wf (h4'.uniq henv (hΔ'.symm henv) h4).symm
    exact ⟨_, .forallE h1 h2 h3' h4'⟩
  | letE h1 h2 h3 h4 ih2 ih3 ih4 =>
    let ⟨_, h2'⟩ := ih2 hΔ
    let ⟨_, h3'⟩ := ih3 hΔ
    have ⟨_, h0⟩ := h1.isType henv hΔ.wf
    have t0 := (h2.uniq henv hΔ h2').of_l henv hΔ.wf h0
    have t1 := (h3.uniq henv hΔ h3').of_l henv hΔ.wf h1
    have t2 := (h2'.uniq henv (hΔ.symm henv) h2).symm
    have t3 := (h3'.uniq henv (hΔ.symm henv) h3).symm
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlet t1 t0)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h0 := h0.defeqDFC henv hΔ.defeqCtx
    have h0 := h0.defeqU_l henv (hΔ.symm henv).wf t2
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf t3
    have h1 := h1.defeqU_r henv (hΔ.symm henv).wf t2
    exact ⟨_, .letE h1 h2' h3' h4'⟩
  | lit h1 _ ih1 => let ⟨_, h2⟩ := ih1 hΔ; exact ⟨_, .lit h1 h2⟩
  | mdata _ ih1 => let ⟨_, h1⟩ := ih1 hΔ; exact ⟨_, .mdata h1⟩
  | proj h1 h2 ih1 =>
    let ⟨_, h1'⟩ := ih1 hΔ
    exact ⟨_, .proj h1' (h2.proj_defeqDFC henv hΔ.defeqCtx (h1.uniq henv hΔ h1'))⟩

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExprS.defeqDFC' (H : TrExprS env Us Δ₁ e e') : TrExpr env Us Δ₂ e e' := by
  let ⟨_, H'⟩ := H.defeqDFC henv hΔ
  refine ⟨_, H', H'.uniq henv (hΔ.symm henv) H⟩

theorem TrExpr.lam (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (h1 : env.IsType Us.length Δ.toCtx ty')
    (h2 : TrExpr env Us Δ ty ty')
    (h3 : TrExpr env Us ((none, .vlam ty') :: Δ) body body') :
    TrExpr env Us Δ (.lam name ty body bi) (.lam ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, s2, h2⟩ := h2
  let ⟨_, s3, _, h3⟩ := h3
  have := h2.symm.of_l henv hΔ h1
  have hΔΔ := .cons (.refl henv hΔ) (ofv := none) nofun (.vlam this)
  let ⟨_, s3'⟩ := s3.defeqDFC henv hΔΔ
  let ⟨_, h3'⟩ := s3.uniq henv hΔΔ s3'
  ⟨_, .lam ⟨_, this.hasType.2⟩ s2 s3', _,
    .symm <| .lamDF this <| h3.symm.trans_l henv hΔΔ.wf.toCtx h3'⟩

theorem TrExpr.forallE (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (h1 : env.IsType Us.length Δ.toCtx ty')
    (h2 : env.IsType Us.length (ty' :: Δ.toCtx) body')
    (h3 : TrExpr env Us Δ ty ty')
    (h4 : TrExpr env Us ((none, .vlam ty') :: Δ) body body') :
    TrExpr env Us Δ (.forallE name ty body bi) (.forallE ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, h2⟩ := h2
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, _, h4⟩ := h4
  have := h3.symm.of_l henv hΔ h1
  have hΔΔ := .cons (.refl henv hΔ) (ofv := none) nofun (.vlam this)
  let ⟨_, s4'⟩ := s4.defeqDFC henv hΔΔ
  let ⟨_, h4'⟩ := s4.uniq henv hΔΔ s4'
  have h4 := h4.trans_r henv hΔΔ.wf h2 |>.symm.trans_l henv hΔΔ.wf h4'
  have h5 := h4.hasType.2.defeq_l henv this
  ⟨_, .forallE ⟨_, this.hasType.2⟩ ⟨_, h5⟩ s3 s4', _, .symm <| .forallEDF this h4⟩

theorem TrExpr.letE (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (h1 : env.HasType Us.length Δ.toCtx val' ty')
    (h2 : TrExpr env Us Δ ty ty')
    (h3 : TrExpr env Us Δ val val')
    (h4 : TrExpr env Us ((none, .vlet ty' val') :: Δ) body body') :
    TrExpr env Us Δ (.letE name ty val body nd) body' :=
  have ⟨_, h0⟩ := h1.isType henv hΔ
  let ⟨_, s2, h2⟩ := h2
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, _, h4⟩ := h4
  have h1' := h1.defeqU_r henv hΔ h2.symm |>.defeqU_l henv hΔ h3.symm
  have h2' := h2.symm.of_l henv hΔ h0
  have h3' := h3.symm.of_l henv hΔ h1
  have hΔΔ := VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none) nofun (.vlet h3' h2')
  let ⟨_, s4'⟩ := s4.defeqDFC henv hΔΔ
  let ⟨_, h4'⟩ := s4.uniq henv hΔΔ s4'
  ⟨_, .letE h1' s2 s3 s4', _, h4'.symm.trans_l henv hΔ h4⟩

theorem TrExpr.lit (h1 : env.ContainsLits l)
    (h : TrExpr env Us Δ l.toConstructor e') : TrExpr env Us Δ (.lit l) e' :=
  let ⟨_, s2, h2⟩ := h; ⟨_, .lit h1 s2, h2⟩

theorem TrExpr.mdata (h : TrExpr env Us Δ e e') : TrExpr env Us Δ (.mdata d e) e' :=
  let ⟨_, s2, h2⟩ := h; ⟨_, .mdata s2, h2⟩

theorem TrExpr.proj {env Us Δ e e' s i} (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (H : TrExpr env Us Δ e e')
    (H2 : VExpr.WF env Us.length Δ.toCtx (.proj s i e')) :
    TrExpr env Us Δ (.proj s i e) (.proj s i e') :=
  let ⟨_, s2, h2⟩ := H
  have H2' := H2.proj_defeqDFC henv (.refl hΔ) h2.symm
  ⟨_, .proj s2 H2', H2'.proj_uniq henv (.refl hΔ) h2⟩

variable! (henv : OrderedStrong env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_var (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : Δ₁.find? v = some (e', A)) :
    TrExprS env Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) (e'.inst e₀' k) := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value, VExpr.inst]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value, VExpr.inst, VLocalDecl.depth]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV henv (.skip (d.inst e₀' k) .refl)
        cases d <;> simpa [← VExpr.lift_instN_lo, VExpr.liftN_zero,
          VLocalDecl.inst, VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]

variable! (henv : OrderedStrong env) (h₀ : TrExprS env Us Δ₀ e₀ e₀')
  (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀) in
theorem TrExprS.instN (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrExprS env Us Δ₁ e e') :
    TrExprS env Us Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_var henv h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx t₀) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.instN henv W.toCtx t₀) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx.succ t₀)
      (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.instN henv W.toCtx t₀) (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (h2.instN henv W.toCtx t₀)

theorem TrExprS.inst {Δ : VLCtx} (henv : OrderedStrong env)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExprS env Us ((none, .vlam A₀) :: Δ) e e')
    (h₀ : TrExprS env Us Δ e₀ e₀') :
    TrExprS env Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  h₀.instN henv t₀ .zero H

theorem TrExpr.inst (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExpr env Us ((none, .vlam A₀) :: Δ) e e')
    (h₀ : TrExpr env Us Δ e₀ e₀') :
    TrExpr env Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  have ⟨_, h0⟩ := t₀.isType henv hΔ
  have ⟨_, s1, _, h1⟩ := H
  have ⟨_, s2, h2⟩ := h₀
  have h2' := h2.symm.of_l henv hΔ t₀
  have hΔΔ := VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none) nofun (.vlam h0)
  let ⟨_, s1'⟩ := s1.defeqDFC henv hΔΔ
  let ⟨_, h1'⟩ := s1.uniq henv hΔΔ s1'
  ⟨_, .inst henv h2'.hasType.2 s1' s2, _,
    .instDF henv hΔ (h1'.symm.trans_l henv hΔΔ.wf.toCtx h1) h2'.symm⟩

variable! (henv : OrderedStrong env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_let_var (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    (H : Δ₁.find? v = some (e', A)) :
    TrExprS env Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) e' := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV henv (.skip d .refl)
        cases d <;> simpa [VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth]

variable! (henv : OrderedStrong env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_let (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrExprS env Us Δ₁ e e') :
    TrExprS env Us Δ (Expr.instantiate1' e e₀ dk) e' := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_let_var henv h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2)
      (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (W.toCtx ▸ h2)

theorem TrExprS.inst_let {Δ : VLCtx} (henv : OrderedStrong env)
    (H : TrExprS env Us ((none, .vlet A₀ e₀') :: Δ) e e')
    (h₀ : TrExprS env Us Δ e₀ e₀') :
    TrExprS env Us Δ (e.instantiate1' e₀) e' :=
  h₀.instN_let henv .zero H

theorem TrExpr.inst_let (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExpr env Us ((none, .vlet A₀ e₀') :: Δ) e e')
    (h₀ : TrExpr env Us Δ e₀ e₀') :
    TrExpr env Us Δ (e.instantiate1' e₀) e' :=
  have ⟨_, h0⟩ := t₀.isType henv hΔ
  have ⟨_, s1, _, h1⟩ := H
  have ⟨_, s2, h2⟩ := h₀
  have h2' := h2.symm.of_l henv hΔ t₀
  have hΔΔ := VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none) nofun (.vlet h2' h0)
  let ⟨_, s1'⟩ := s1.defeqDFC henv hΔΔ
  let ⟨_, h1'⟩ := s1.uniq henv hΔΔ s1'
  ⟨_, .inst_let henv s1' s2, _, h1'.symm.trans_l henv hΔ h1⟩

/-- Universe weakening for strict concrete-expression translation.  A fresh
concrete parameter is prepended, the concrete expression is unchanged, and
all existing abstract universe indices are shifted by one. -/
theorem TrExprS.prependLevelParam
    (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (hfresh : fresh ∉ Us)
    (H : TrExprS env Us Δ e e') :
    TrExprS env (fresh :: Us)
      (Δ.instL (VLevel.prependShift Us.length)) e
      (e'.instL (VLevel.prependShift Us.length)) :=
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  (iff_typed henv.orderedStrong (VLCtx.WF.instL hshift (by simpa using hΔ))).2
    (((iff_typed henv.orderedStrong hΔ).1 H).prependLevelParam hfresh)

section

variable (henv : VEnv.WF env) {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (hΔ : VLCtx.WF env ls'.length Δ)
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)

include Hls eq

include henv hΔ

theorem TrExprS.instL (H : TrExprS env ps Δ e e') :
    TrExpr env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) (e'.instL ls') := by
  simp [Expr.instantiateLevelParams_eq]
  generalize (_ && _) = red, eqF : (fun x : Name => _) = F
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  have eq' := eq.trans (List.mapM_eq_some.1 Hls).length_eq
  induction H with
  | bvar h1 => exact (bvar (VLCtx.find?_instL h1)).trExpr henv (hΔ.instL Hls')
  | fvar h1 => exact (fvar (VLCtx.find?_instL h1)).trExpr henv (hΔ.instL Hls')
  | sort h1 =>
    simp [Expr.instantiateLevelParamsCore']
    have ⟨_, a1, a2⟩ := substParams_wf Hls eq eqF red h1
    exact ⟨_, .sort a1, _, .sortDF (.of_ofLevel a1) (.inst Hls') a2⟩
  | const h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := substParams_wf_list Hls eq eqF red h2
    refine ⟨_, .const h1 a1 (by simp [h3]), _, .constDF h1 (.of_mapM_ofLevel a1) ?_ ?_ a2⟩
    · simp; exact fun _ _ => .inst Hls'
    · simp [← (List.mapM_eq_some.1 a1).length_eq, h3]
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls') (ih1 hΔ) (ih2 hΔ)
  | lam h1 h2 _ ih1 ih2 =>
    exact .lam henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hΔ) (ih2 ⟨hΔ, nofun, eq' ▸ h1⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls') (ih1 hΔ) (ih2 ⟨hΔ, nofun, eq' ▸ h1⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hΔ) (ih2 hΔ) (ih3 ⟨hΔ, nofun, eq' ▸ h1⟩)
  | lit h1 _ ih =>
    refine .lit h1 (Expr.instantiateLevelParamsCore_eq_self ?_ ▸ ih hΔ :)
    exact Literal.toConstructor_hasLevelParam
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ h2 ih =>
    exact .proj henv (hΔ.instL Hls') (ih hΔ)
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls')

theorem TrExpr.instL (H : TrExpr env ps Δ e e') :
    TrExpr env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) (e'.instL ls') :=
  let ⟨_, s1, h1⟩ := H
  have Hls' := .of_mapM_ofLevel Hls
  (s1.instL henv hΔ Hls eq).defeq henv (hΔ.instL Hls') (VLCtx.instL_toCtx _ ▸ h1.instL Hls')

end

theorem TrExprS.abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (H : TrExprS env Us Δ₁ e e') :
    TrExprS env Us Δ (e.abstract1 v₀ dk) e' := by
  induction H generalizing dk k Δ with
  | bvar h1 =>
    exact .bvar <| (W.find? (by nofun)).trans <| by
      simp; split <;> [skip; rw [if_neg (by omega), if_neg (by omega)]] <;> exact h1
  | @fvar _ _ _ fv h1 =>
    if h : fv = v₀ then
      rw [h, W.find?_self] at h1; cases h1
      rw [Expr.abstract1, if_pos (by simp [h])]
      exact .bvar <| (W.find? (by nofun)).trans (by simpa using W.find?_self)
    else
      have := W.find? (v := .inr fv) (by rintro ⟨⟩; trivial)
      simp at this
      rw [Expr.abstract1, if_neg]
      · exact .fvar (this.trans h1)
      · simp; rintro rfl; trivial
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 => exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 W.succ)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W.succ)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 W.succ)
  | lit h1 _ ih =>
    exact .lit h1 (FVarsIn.toConstructor.abstract_eq_self .toConstructor ▸ ih W)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (W.toCtx ▸ h2)

theorem TrExpr.abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (H : TrExpr env Us Δ₁ e e') :
    TrExpr env Us Δ (e.abstract1 v₀ dk) e' :=
  let ⟨_, s, h⟩ := H; ⟨_, s.abstract W, W.toCtx ▸ h⟩

/-- Translation is unique (`TrExprS.unique_of_syn`). -/
theorem TrExprS.unique (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂ :=
  H1.unique_of_syn H2

/-- Translation is syntactically unique: every constructor of `TrExprS` is
determined by the source syntax and the context, including projections. -/
theorem TrExprS.uniqueCtx {env : VEnv} {Us : List Name} {Δ₁ Δ₂ : VLCtx} {e : Expr}
    {e₁ e₂ : VExpr} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) : e₁ = e₂ :=
  H1.toTrSyn.uniqueCtx hΔ H2.toTrSyn

theorem TrExprS.boolFalse (henv : env.HasPrimitives) (H : env.contains ``Bool) :
    TrExprS env Us Δ (toExpr false) .boolFalse ∧
    env.HasType Us.length Δ.toCtx .boolFalse .bool := by
  let ⟨⟨_, H⟩, _⟩ := henv.bool H
  cases henv.boolFalse H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

@[simp] theorem VExpr.instL_boolFalse : VExpr.boolFalse.instL ls = VExpr.boolFalse := by
  simp [boolFalse, instL]

theorem TrExprS.boolTrue (henv : env.HasPrimitives) (H : env.contains ``Bool) :
    TrExprS env Us Δ (toExpr true) .boolTrue ∧
    env.HasType Us.length Δ.toCtx .boolTrue .bool := by
  let ⟨_, _, H⟩ := henv.bool H
  cases henv.boolTrue H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

@[simp] theorem VExpr.instL_boolTrue : VExpr.boolTrue.instL ls = VExpr.boolTrue := by
  simp [boolTrue, instL]

theorem TrExprS.boolLit (henv : env.HasPrimitives) (H : env.contains ``Bool) (b : Bool) :
    TrExprS env Us Δ (toExpr b) (.boolLit b) ∧
    env.HasType Us.length Δ.toCtx (.boolLit b) .bool := by
  match b with
  | false => exact TrExprS.boolFalse henv H
  | true => exact TrExprS.boolTrue henv H

@[simp] theorem VExpr.instL_boolLit : (VExpr.boolLit b).instL ls = VExpr.boolLit b := by
  cases b <;> simp [boolLit]

theorem FVarsIn.boolLit {b : Bool} : FVarsIn P (toExpr b) := by cases b <;> exact nofun

theorem VExpr.WF.boolLit_has_type (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (hΓ : OnCtx Γ (env.IsType U)) (H : VExpr.WF env U Γ (.boolLit b)) : env.contains ``Bool := by
  suffices env.HasType U Γ (.boolLit b) .bool by
    have ⟨_, H⟩ := this.isType wf hΓ
    have ⟨_, H, _⟩ := HasType.const_inv wf hΓ H
    exact ⟨_, H⟩
  cases b with have ⟨_, h1, h2, h3⟩ := let ⟨_, H⟩ := H; HasType.const_inv wf hΓ H
  | false => cases henv.boolFalse h1; exact .const h1 h2 h3
  | true => cases henv.boolTrue h1; exact .const h1 h2 h3

theorem TrExprS.lit_has_type (H : TrExprS env Us Δ (.lit l) e') : env.ContainsLits l :=
  let .lit H _ := H; H

theorem TrExprS.nat_of_natZero (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (H : TrExprS env Us Δ .natZero e') : env.contains ``Nat := by
  let .const H .. := H
  have ⟨_, H⟩ := henv.natZero H ▸ wf.ordered.constWF H
  have ⟨_, H, _⟩ := H.const_inv wf (by trivial)
  exact ⟨_, H⟩

theorem TrExprS.natZero (henv : env.HasPrimitives) (H : env.contains ``Nat) :
    TrExprS env Us Δ .natZero .natZero ∧ env.HasType Us.length Δ.toCtx .natZero .nat := by
  let ⟨⟨_, H⟩, _⟩ := henv.nat H
  cases henv.natZero H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

@[simp] theorem VExpr.instL_natZero : VExpr.natZero.instL ls = .natZero := by
  simp [natZero, instL]

theorem TrExprS.natSucc (henv : env.HasPrimitives) (H : env.contains ``Nat) :
    TrExprS env Us Δ .natSucc .natSucc ∧
    env.HasType Us.length Δ.toCtx .natSucc (.forallE .nat .nat) := by
  let ⟨_, _, H⟩ := henv.nat H
  cases henv.natSucc H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

@[simp] theorem VExpr.instL_natSucc : VExpr.natSucc.instL ls = .natSucc := by
  simp [natSucc, instL]

theorem TrExprS.natLit (henv : env.HasPrimitives) (H : env.contains ``Nat) (n) :
    TrExprS env Us Δ (.lit (.natVal n)) (.natLit n) ∧
    env.HasType Us.length Δ.toCtx (.natLit n) .nat := by
  induction n with
  | zero => exact let ⟨h1, h2⟩ := natZero henv H; ⟨.lit H h1, h2⟩
  | succ n ih => exact let ⟨h1, h2⟩ := natSucc henv H; ⟨.lit H (.app h2 ih.2 h1 ih.1), .app h2 ih.2⟩

@[simp] theorem VExpr.instL_natLit : (VExpr.natLit n).instL ls = VExpr.natLit n := by
  induction n <;> simp [*, natLit, instL]

theorem TrExprS.stringOfList (henv : env.HasPrimitives) (H : env.contains ``String.ofList) :
    TrExprS env Us Δ (.const ``String.ofList []) .stringOfList ∧
    env.HasType Us.length Δ.toCtx .stringOfList (.forallE .listChar .string) := by
  let ⟨_, H⟩ := H
  cases (henv.stringOfList H).1
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

theorem TrExprS.charOfNat (henv : env.HasPrimitives) (H : env.contains ``Char.ofNat) :
    TrExprS env Us Δ (.const ``Char.ofNat []) .charOfNat ∧
    env.HasType Us.length Δ.toCtx .charOfNat (.forallE .nat .char) := by
  let ⟨_, H⟩ := H
  cases henv.charOfNat H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

theorem VEnv.HasPrimitives.nat_of_charOfNat (wf : OrderedStrong env) (henv : env.HasPrimitives)
    (H : env.contains ``Char.ofNat) : env.contains ``Nat := by
  let ⟨_, H⟩ := H
  have ⟨_, H⟩ := wf.ordered.constWF (henv.charOfNat H ▸ H)
  let ⟨⟨_, H⟩, _⟩ := H.forallE_inv wf
  let ⟨_, H, _⟩ := H.const_inv wf trivial
  exact ⟨_, H⟩

theorem TrExprS.listChar (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (H : env.contains ``String.ofList) :
    TrExprS env Us Δ (.app (.const ``List [.zero]) (.const ``Char [])) .listChar ∧
    env.IsType Us.length Δ.toCtx .listChar := by
  let ⟨_, H⟩ := H
  let ⟨_, H, _⟩ := henv.stringOfList H
  let ⟨_, H⟩ := H.isType wf (by trivial)
  refine ⟨?_, _, (H.instL (ls := []) nofun).weak0 wf⟩
  let ⟨_, _, A, B⟩ := H.app_inv wf trivial
  let ⟨_, A1, _, A3⟩ := A.const_inv wf trivial
  let ⟨_, B1, _, B3⟩ := B.const_inv wf trivial
  exact .app ((A.instL (ls := []) nofun).weak0 wf) ((B.instL (ls := []) nofun).weak0 wf)
    (.const A1 rfl A3) (.const B1 rfl B3)

theorem TrExprS.listCharNil (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (H : env.contains ``String.ofList) :
    TrExprS env Us Δ (.app (.const ``List.nil [.zero]) (.const ``Char [])) .listCharNil ∧
    env.HasType Us.length Δ.toCtx .listCharNil .listChar := by
  let ⟨_, H⟩ := H
  let ⟨_, H, _⟩ := henv.stringOfList H
  refine ⟨?_, (H.instL (ls := []) nofun).weak0 wf⟩
  let ⟨_, _, A, B⟩ := H.app_inv wf trivial
  let ⟨_, A1, _, A3⟩ := A.const_inv wf trivial
  let ⟨_, B1, _, B3⟩ := B.const_inv wf trivial
  exact .app ((A.instL (ls := []) nofun).weak0 wf) ((B.instL (ls := []) nofun).weak0 wf)
    (.const A1 rfl A3) (.const B1 rfl B3)

theorem TrExprS.listCharCons (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (H : env.contains ``String.ofList) :
    TrExprS env Us Δ (.app (.const ``List.cons [.zero]) (.const ``Char [])) .listCharCons ∧
    env.HasType Us.length Δ.toCtx .listCharCons
      (.forallE .char <| .forallE .listChar .listChar) := by
  let ⟨_, H⟩ := H
  let ⟨_, _, H⟩ := henv.stringOfList H
  refine ⟨?_, (H.instL (ls := []) nofun).weak0 wf⟩
  let ⟨_, _, A, B⟩ := H.app_inv wf trivial
  let ⟨_, A1, _, A3⟩ := A.const_inv wf trivial
  let ⟨_, B1, _, B3⟩ := B.const_inv wf trivial
  exact .app ((A.instL (ls := []) nofun).weak0 wf) ((B.instL (ls := []) nofun).weak0 wf)
    (.const A1 rfl A3) (.const B1 rfl B3)

theorem TrExprS.listCharLit (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (H : env.ContainsLits (.strVal l)) (s : List Char) :
    TrExprS env Us Δ (s.foldr
      (init := .app (.const ``List.nil [.zero]) (.const ``Char []))
      (fun c e => .app (.app
        (.app (.const ``List.cons [.zero]) (.const ``Char []))
        (.app (.const ``Char.ofNat []) (.lit (.natVal c.toNat)))) e)) (.listCharLit s) ∧
    env.HasType Us.length Δ.toCtx (.listCharLit s) .listChar := by
  induction s with
  | nil => exact TrExprS.listCharNil wf henv H.2
  | cons x _ ih =>
    have a := TrExprS.listCharCons wf henv H.2 (Us := Us) (Δ := Δ)
    have b := TrExprS.charOfNat henv H.1 (Us := Us) (Δ := Δ)
    have c := TrExprS.natLit henv (henv.nat_of_charOfNat wf H.1) (Us := Us) (Δ := Δ) (n := x.toNat)
    have d1 := b.1.app b.2 c.2 c.1; have d2 := b.2.app c.2
    have e1 := a.1.app a.2 d2 d1; have e2 := a.2.app d2
    exact ⟨e1.app e2 ih.2 ih.1, e2.app ih.2⟩

theorem TrExprS.trLiteral (wf : env.OrderedStrong) (henv : env.HasPrimitives)
    (l) (H : env.ContainsLits l) :
    TrExprS env Us Δ (.lit l) (.trLiteral l) ∧
    env.HasType Us.length Δ.toCtx (.trLiteral l) (.const l.typeName []) := by
  match l with
  | .natVal n => exact TrExprS.natLit henv H _
  | .strVal s =>
    have a := TrExprS.stringOfList henv H.2 (Us := Us) (Δ := Δ)
    have b := TrExprS.listCharLit wf henv H (Us := Us) (Δ := Δ) s.toList
    exact ⟨.lit H (.app a.2 b.2 a.1 (String.foldr_eq .. ▸ b.1)), a.2.app b.2⟩

def VLocalDecl.ClosedN : VLocalDecl → (k : Nat := 0) → Prop
  | .vlam A, k => A.ClosedN k
  | .vlet A e, k => A.ClosedN k ∧ e.ClosedN k

def VLCtx.Closed : VLCtx → Prop
  | [] => True
  | (none, _) :: _ => False
  | (some _, d) :: (Δ : VLCtx) => Δ.Closed ∧ d.ClosedN Δ.bvars

def IsFVarUpSet (P : FVarId → Prop) : VLCtx → Prop
  | [] => True
  | (none, _) :: Δ => IsFVarUpSet P Δ
  | (some (fv, deps), _) :: (Δ : VLCtx) =>
    IsFVarUpSet P Δ ∧
    (P fv → ∀ fv' ∈ deps, P fv')

theorem IsFVarUpSet.congr : ∀ {Δ}, VLCtx.FVWF Δ →
    (H : ∀ fv ∈ VLCtx.fvars Δ, P fv ↔ Q fv) → IsFVarUpSet P Δ ↔ IsFVarUpSet Q Δ
  | [], _, _ => .rfl
  | (none, _) :: Δ, ⟨h1, _⟩, H => congr (Δ := Δ) h1 H
  | (some (fv, deps), d) :: (Δ : VLCtx), ⟨h1, h2⟩, H => by
    refine and_congr (congr h1 fun fv h => H _ (.tail _ h)) (imp_congr (H _ (.head _)) ?_)
    refine forall_congr' fun fv => imp_congr_right fun h => ?_
    exact H _ (by simp [(h2 _ _ rfl).2 h])

theorem IsFVarUpSet.and_fvars (H : VLCtx.FVWF Δ) :
    IsFVarUpSet P Δ ↔ IsFVarUpSet (fun fv => P fv ∧ fv ∈ Δ.fvars) Δ :=
  IsFVarUpSet.congr H fun _ h => (and_iff_left h).symm

theorem IsFVarUpSet.trivial : ∀ {Δ}, IsFVarUpSet (fun _ => True) Δ
  | [] => ⟨⟩
  | (none, _) :: Δ => trivial (Δ := Δ)
  | (some _, _) :: _ => ⟨trivial, fun _ _ _ => ⟨⟩⟩

theorem IsFVarUpSet.fvars (H : VLCtx.FVWF Δ) : IsFVarUpSet (· ∈ Δ.fvars) Δ :=
  (IsFVarUpSet.congr H fun _ => iff_true_intro).2 trivial

/-- Membership in the free variables of a well-formed context suffix is an
up-set throughout any larger context obtained by prepending declarations.
Freshness of every prepended free variable makes its dependency obligation
vacuous. -/
theorem IsFVarUpSet.suffixFVars (suffix : VLCtx) : ∀ (added : VLCtx),
    VLCtx.WF env U (added ++ suffix) →
    IsFVarUpSet (· ∈ suffix.fvars) (added ++ suffix)
  | [], h => IsFVarUpSet.fvars h.fvwf
  | (none, d) :: added, h => suffixFVars suffix added h.1
  | (some (fv, deps), d) :: added, h => by
      refine ⟨suffixFVars suffix added h.1, fun hfv => ?_⟩
      have hmem : fv ∈ VLCtx.fvars (added ++ suffix) := by
        rw [VLCtx.fvars_append]
        simp [hfv]
      exact False.elim ((h.2.1 fv deps rfl).1 hmem)

/-- Prepending declarations whose free-variable binders lie outside an
up-set preserves that up-set: fresh
local binders may depend on the retained root scope, but do not themselves
become members of it. -/
theorem IsFVarUpSet.prependFresh (P : FVarId → Prop) (suffix : VLCtx) :
    ∀ (added : VLCtx),
      IsFVarUpSet P suffix →
      (∀ fv, fv ∈ added.fvars → ¬ P fv) →
      IsFVarUpSet P (added ++ suffix)
  | [], H, _ => H
  | (none, d) :: added, H, hfresh =>
      prependFresh P suffix added H fun fv h => hfresh fv h
  | (some (fv, deps), d) :: added, H, hfresh => by
      refine ⟨prependFresh P suffix added H
        (fun fv' h => hfresh fv' (.tail _ h)), ?_⟩
      exact fun hP => False.elim (hfresh fv (.head _) hP)

def AllAbove (Δ : VLCtx) (P : FVarId → Prop) (fv : FVarId) : Prop := fv ∈ Δ.fvars → P fv

theorem AllAbove.wf (H : Δ.FVWF) : IsFVarUpSet (AllAbove Δ P) Δ ↔ IsFVarUpSet P Δ :=
  IsFVarUpSet.congr H fun _ h => by simp [h, AllAbove]

def FVarsBelow (Δ e e') := ∀ P, IsFVarUpSet P Δ → FVarsIn P e → FVarsIn P e'

theorem FVarsBelow.rfl : FVarsBelow Δ e e := fun _ _ => id

theorem FVarsBelow.trans (H1 : FVarsBelow Δ e₁ e₂) (H2 : FVarsBelow Δ e₂ e₃) :
    FVarsBelow Δ e₁ e₃ := fun _ h => H2 _ h ∘ H1 _ h

def TrTyping (env : VEnv) (Us : List Name) (Δ : VLCtx) (e A : Expr) (e' A' : VExpr) : Prop :=
  FVarsBelow Δ e A ∧ TrExprS env Us Δ e e' ∧ TrExprS env Us Δ A A' ∧
  env.HasType Us.length Δ.toCtx e' A'

theorem FVarsIn.mkAppList :
    FVarsIn P (e.mkAppList es) ↔ FVarsIn P e ∧ ∀ a ∈ es, FVarsIn P a := by
  simp [← Expr.mkAppRevList_reverse, FVarsIn.mkAppRevList]

theorem FVarsBelow.mkAppList (H : FVarsBelow Δ e₁ e₂) :
    FVarsBelow Δ (e₁.mkAppList es) (e₂.mkAppList es) := by
  simp [FVarsBelow, FVarsIn.mkAppList] at H ⊢; grind

theorem FVarsBelow.mkAppRevList (H : FVarsBelow Δ e₁ e₂) :
    FVarsBelow Δ (e₁.mkAppRevList es) (e₂.mkAppRevList es) := by
  simpa [← Expr.mkAppList_reverse] using H.mkAppList

inductive LambdaBodyN : Nat → Expr → Expr → Prop
  | zero : LambdaBodyN 0 e e
  | succ : LambdaBodyN n body e → LambdaBodyN (n+1) (.lam i ty body bi) e

theorem LambdaBodyN.closed (H : LambdaBodyN n e1 e2) : e1.Closed k → e2.Closed (k + n) := by
  induction H generalizing k with
  | zero => exact id
  | succ _ ih => exact fun h => (Nat.add_right_comm .. ▸ ih h.2 :)

theorem LambdaBodyN.add (H1 : LambdaBodyN m e1 e2) (H2 : LambdaBodyN n e2 e3) :
    LambdaBodyN (n + m) e1 e3 := by
  induction H1 with
  | zero => exact H2
  | succ _ ih => exact .succ (ih H2)

theorem LambdaBodyN.instantiateList (H1 : LambdaBodyN n e1 e2) :
    LambdaBodyN n (e1.instantiateList es k) (e2.instantiateList es (k+n)) := by
  induction H1 generalizing k with
  | zero => exact .zero
  | succ _ ih =>
    rw [Expr.instantiateList_lam]
    refine .succ ?_
    conv => arg 3; rw [← Nat.add_assoc, Nat.add_right_comm]
    exact ih

theorem LambdaBodyN.instantiateRevList (H1 : LambdaBodyN n e1 e2) :
    LambdaBodyN n (e1.instantiateRevList es k) (e2.instantiateRevList es (k+n)) := by
  simp only [← Expr.instantiateList_reverse]; exact H1.instantiateList

inductive BetaReduce : Expr → Expr → Prop
  | refl : BetaReduce e e
  | trans : BetaReduce e₁ e₂ → BetaReduce e₂ e₃ → BetaReduce e₁ e₃
  | app : BetaReduce f f' → BetaReduce (.app f a) (.app f' a)
  | beta : e.looseBVarRange' = 0 → BetaReduce (.app (.lam i ty body bi) e) (body.instantiate1' e)

theorem BetaReduce.mkAppRevList (H : BetaReduce f f') :
    BetaReduce (f.mkAppRevList es) (f'.mkAppRevList es) := by
  induction es with
  | nil => exact H
  | cons _ _ ih => exact .app ih

theorem BetaReduce.mkAppList (H : BetaReduce f f') :
    BetaReduce (f.mkAppList es) (f'.mkAppList es) := by
  induction es generalizing f f' with
  | nil => exact H
  | cons _ _ ih => exact ih (.app H)

theorem BetaReduce.instantiateList (H : BetaReduce f f') :
    BetaReduce (f.instantiateList es) (f'.instantiateList es) := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ ih => simp only [Expr.instantiateList_app]; exact .app ih
  | beta h =>
    simp only [Expr.instantiateList_app, Expr.instantiateList_lam]
    rw [← Expr.instantiateList_instantiate1_comm h]
    refine' cast _ (BetaReduce.beta _); congr 2
    · rw [Expr.instantiateList_eq_self h]
    · rwa [Expr.instantiateList_eq_self h]

theorem BetaReduce.instantiateRevList (H : BetaReduce f f') :
    BetaReduce (f.instantiateRevList es) (f'.instantiateRevList es) := by
  simp only [← Expr.instantiateList_reverse]; exact H.instantiateList

theorem FVarsBelow.betaReduce (H : BetaReduce e e') : FVarsBelow Δ e e' := by
  intro P hP he
  induction H with
  | refl => exact he
  | trans _ _ ih1 ih2 => exact ih2 (ih1 he)
  | app _ ih => exact ⟨ih he.1, he.2⟩
  | beta => exact he.1.2.instantiate1 he.2

theorem BetaReduce.inst_reduce {l₁ : List Expr} {fn e₀ : Expr}
    (h : ∀ x ∈ l₁, x.Closed) (l₂)
    (h1 : LambdaBodyN l₁.length e₀ fn)
    (hr : fn.instantiateList (l₁.reverse ++ l₂) = r) :
    BetaReduce ((e₀.instantiateList l₂).mkAppList l₁) r := by
  subst r
  induction l₁ generalizing e₀ fn l₂ with
  | nil => let .zero := h1; exact .refl
  | cons a l ih =>
    let .succ (body := body) h1 := h1
    rw [Expr.instantiateList_lam]; simp at h ⊢
    have h' := h.1.looseBVarRange_zero
    refine .trans (.mkAppList (.beta h')) ?_
    exact Expr.instantiateList_instantiate1_comm h' ▸ ih h.2 (a::l₂) h1

theorem BetaReduce.cheapBetaReduce (hc : e.Closed) : BetaReduce e e.cheapBetaReduce := by
  simp [Expr.cheapBetaReduce]
  split; · exact .refl
  split; · exact .refl
  let rec loop {e' i fn args} (H : LambdaBodyN i e' fn) (hi : i ≤ args.size) :
    ∃ n fn', LambdaBodyN n e' fn' ∧ n ≤ args.size ∧
      Expr.cheapBetaReduce.loop e args i fn = Expr.cheapBetaReduce.cont e args n fn' := by
    unfold Expr.cheapBetaReduce.loop; split
    · split
      · exact loop (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
      · exact ⟨_, _, H, Nat.le_of_lt ‹_›, rfl⟩
    · exact ⟨_, _, H, hi, rfl⟩
  refine let ⟨i, fn, h1, h2, eq⟩ := loop .zero (Nat.zero_le _); eq ▸ ?_; clear eq
  simp [Expr.getAppArgs_eq] at h2 ⊢
  obtain ⟨l₁, l₂, rfl, eq⟩ : ∃ l₁ l₂, l₁.length = i ∧ e.getAppArgsList = l₁ ++ l₂ :=
    ⟨_, _, List.length_take_of_le (by simp [h2]), (List.take_append_drop ..).symm⟩
  have eqr := congrArg List.reverse eq; simp at eqr
  have hl₁ : ∀ x ∈ l₁, x.Closed := by
    have := eqr ▸ hc.getAppArgsList; simp [or_imp, forall_and] at this
    exact this.1
  unfold Expr.cheapBetaReduce.cont; split <;> rename_i h3
  · simp [Expr.hasLooseBVars] at h3
    rw [Expr.mkAppRange_eq (l₂ := l₂) (l₃ := []) (by simp [eq]) rfl (by simp [← eq])]
    rw [← e.mkAppList_getAppArgsList, eqr]; simp
    refine .mkAppList <| .inst_reduce hl₁ [] h1 (Expr.instantiateList_eq_self h3)
  split <;> [rename_i n; exact .refl]
  have hc := h1.closed hc.getAppFn
  simp [Closed] at hc; rw [if_pos hc]
  rw [Expr.mkAppRange_eq (l₂ := l₂) (l₃ := []) (by simp [eq]) rfl (by simp [← eq])]
  conv => lhs; rw [← e.mkAppList_getAppArgsList]
  simp [eqr]
  refine .mkAppList <| .inst_reduce hl₁ [] h1 ?_
  rw [List.getElem?_append_left (by omega), Nat.sub_right_comm, ← List.getElem?_reverse hc]
  suffices ∀ l₁, (∀ x ∈ l₁, x.Closed) → ∀ n < l₁.length,
      (Expr.bvar n).instantiateList l₁ = l₁[n]?.getD default by
    simpa [Expr.liftLooseBVars_zero] using this l₁.reverse (by simpa using hl₁) n (by simp [hc])
  intro l₁ hl₁ n lt
  induction l₁ generalizing n with
  | nil => cases lt
  | cons a l ih =>
    simp at hl₁
    obtain _ | n := n <;> simp [Expr.instantiate1']
    · exact Expr.instantiateList_eq_self hl₁.1.looseBVarRange_zero
    · exact ih hl₁.2 _ (Nat.lt_of_succ_lt_succ lt)

/-- Retain the original application's result conversions, including their
individual universe sorts, instead of comparing two independently recovered typings. -/
private theorem betaAppView (henv : env.OrderedStrong)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.app f a) V) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A ∧
      TypeConversion env U Γ (B.inst a) V := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : f.app a = e' at H
  induction H with cases eq
  | defeq _ edge _ _ _ _ _ ih =>
    obtain ⟨A, B, hf, ha, path⟩ := ih hΓ rfl eq'
    exact ⟨A, B, hf, ha, .tail path edge.defeq⟩
  | base H =>
    subst eq'
    let .app _ _ _ _ _ hf ha _ := H
    exact ⟨_, _, hf.hasType, ha.hasType, .refl⟩

/-- The lambda's original body typing and natural Pi type, followed by its
actual conversion path. Structural inversion supplies this without uniqueness. -/
private theorem betaLamView (henv : env.OrderedStrong)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.lam A body) V) :
    ∃ B, env.HasType U (A :: Γ) body B ∧ env.IsType U Γ (.forallE A B) ∧
      TypeConversion env U Γ (.forallE A B) V := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : A.lam body = e' at H
  induction H with cases eq
  | defeq _ edge _ _ _ _ _ ih =>
    obtain ⟨B, hb, hPi, path⟩ := ih hΓ rfl eq'
    exact ⟨B, hb, hPi, .tail path edge.defeq⟩
  | base H =>
    subst eq'
    let .lam _ _ _ _ hb hPi := H
    exact ⟨_, hb.hasType, ⟨_, hPi.hasType⟩, .refl⟩

/-- The alignment needed by converted beta: type the actual argument at the
lambda's written domain and connect this one instantiated result to the caller's
result. No stratification bound is needed by the consumer.

This remains a boundary to the existing foundation: composing the original conversion path
uses `IsDefEqU.trans` (and hence uniqueness), followed by Pi inversion. The views
and the beta branch below do not require those results independently. -/
private theorem betaLambdaAlignment (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ (.lam A body) (.forallE C D))
    (ha : env.HasType U Γ a C) :
    ∃ B, env.HasType U (A :: Γ) body B ∧ env.HasType U Γ a A ∧
      TypeConversion env U Γ (B.inst a) (D.inst a) := by
  obtain ⟨B, hb, ⟨u, hPi⟩, path⟩ := betaLamView henv hΓ hf
  have closePath {X Y} (path : TypeConversion env U Γ X Y)
      (hX : env.IsType U Γ X) : env.IsDefEqU U Γ X Y := by
    induction path with
    | refl => obtain ⟨_, hX⟩ := hX; exact ⟨_, hX⟩
    | tail _ edge ih => exact ih.trans henv hΓ ⟨_, edge⟩
  have hWhole := closePath path ⟨u, hPi⟩
  obtain ⟨⟨_, hAC⟩, _, hBD⟩ := hWhole.forallE_inv henv hΓ
  have haA : env.HasType U Γ a A := .defeqDF hAC.symm ha
  exact ⟨B, hb, haA, .single (hBD.instN henv haA .zero)⟩

theorem TrExpr.beta (H : TrExpr env Us Δ e e')
    (henv : VEnv.WF env) (hΓ : VLCtx.WF env Us.length Δ)
    (H : BetaReduce e e₂) : TrExpr env Us Δ e₂ e' := by
  induction H generalizing e' with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih2 (ih1 H)
  | app _ ih =>
    let ⟨_, .app hf ha tf ta, _, df⟩ := H
    have ⟨_, _, hf', ha'⟩ := df.hasType.1.app_inv henv hΓ
    exact ((ih ⟨_, tf, _, hf'⟩).app henv hΓ hf' ha' (ta.trExpr henv hΓ)).defeq henv hΓ ⟨_, df⟩
  | beta =>
    let ⟨_, .app _ _ tf ta, _, df⟩ := H
    let .lam _ _ tb := tf
    obtain ⟨_, _, hf, ha, resultPath⟩ := betaAppView henv hΓ df.hasType.1
    obtain ⟨_, hb, haA, bodyPath⟩ := betaLambdaAlignment henv hΓ hf ha
    have beta := resultPath.cast (bodyPath.cast (.beta hb haA))
    exact ⟨_, .inst henv haA tb ta, _, beta.symm.trans df⟩

theorem FVarsBelow.cheapBetaReduce (he : e.Closed) : FVarsBelow Δ e e.cheapBetaReduce :=
  .betaReduce (.cheapBetaReduce he)

theorem TrExpr.cheapBetaReduce (H : TrExpr env Us Δ e e')
    (henv : VEnv.WF env) (hΓ : VLCtx.WF env Us.length Δ)
    (noBV : Δ.NoBV) : TrExpr env Us Δ e.cheapBetaReduce e' :=
  H.beta henv hΓ <| .cheapBetaReduce <| noBV ▸ H.closed.mono (by simp)

theorem TrExprS.uninstantiateN
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrExprS env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) e')
    (sc : FVarsIn (· ≠ v₀) e) :
    TrExprS env Us Δ e e' := by
  have := H.abstract W
  rwa [sc.abstract_instantiate1] at this

theorem TrExpr.uninstantiateN
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrExpr env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) e')
    (sc : FVarsIn (· ≠ v₀) e) :
    TrExpr env Us Δ e e' :=
  let ⟨_, s, h⟩ := H; ⟨_, s.uninstantiateN W sc, W.toCtx ▸ h⟩

theorem TrExprS.uninstantiate
    (H : TrExprS env Us ((some (v, deps), d) :: Δ) (e.instantiate1' (.fvar v)) e')
    (sc : FVarsIn (· ≠ v) e) :
    TrExprS env Us ((none, d) :: Δ) e e' := H.uninstantiateN .zero sc

theorem TrExpr.uninstantiate
    (H : TrExpr env Us ((some (v, deps), d) :: Δ) (e.instantiate1' (.fvar v)) e')
    (sc : FVarsIn (· ≠ v) e) :
    TrExpr env Us ((none, d) :: Δ) e e' := H.uninstantiateN .zero sc

theorem TrExprS.inst_fvar {Δ : VLCtx} (henv : OrderedStrong env)
    (hΔ : VLCtx.WF env Us.length ((some (a, deps), d) :: Δ))
    (H : TrExprS env Us ((none, d) :: Δ) e e') :
    TrExprS env Us ((some (a, deps), d) :: Δ) (e.instantiate1' (.fvar a)) e' :=
  (iff_typed henv hΔ).2 <|
    ((iff_typed (Δ := (none, d) :: Δ) henv ⟨hΔ.1, nofun, hΔ.2.2⟩).1 H).inst_fvar henv
      hΔ.fvars_nodup

theorem TrExpr.rebuild_mkAppRevList (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (he : TrExprS env Us Δ e e') (h1 : TrExprS env Us Δ (e.mkAppRevList as) ea')
    (h2 : TrExpr env Us Δ e₁ e') : TrExpr env Us Δ (e₁.mkAppRevList as) ea' := by
  induction as generalizing ea' with
  | nil => exact h2.defeq henv hΔ (he.uniq henv (.refl henv hΔ) h1)
  | cons a as ih =>
    let .app a1 a2 a3 a4 := h1
    have := ih a3
    exact .app henv hΔ a1 a2 (ih a3) (a4.trExpr henv hΔ)

theorem TrExpr.rebuild_mkAppList (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (he : TrExprS env Us Δ e e') (h1 : TrExprS env Us Δ (e.mkAppList as) ea')
    (h2 : TrExpr env Us Δ e₁ e') : TrExpr env Us Δ (e₁.mkAppList as) ea' := by
  rw [← Expr.mkAppRevList_reverse] at h1 ⊢
  exact h2.rebuild_mkAppRevList henv hΔ he h1

theorem TrExprS.eqv (H : TrExprS env Us Δ e₁ e') : e₁ == e₂ → TrExprS env Us Δ e₂ e' := by
  simp [(· == ·)]
  induction H generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; grind [TrExprS]

theorem TrExpr.eqv (H : TrExpr env Us Δ e₁ e') (h : e₁ == e₂) : TrExpr env Us Δ e₂ e' :=
  let ⟨_, h1, h2⟩ := H; ⟨_, h1.eqv h, h2⟩

theorem fvarsList_eqv {e₁ e₂ : Expr} : e₁ == e₂ → e₁.fvarsList = e₂.fvarsList := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; simp [Expr.fvarsList]
  all_goals grind

theorem FVarsIn.eqv : e₁ == e₂ → FVarsIn P e₁ → FVarsIn P e₂ := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; revert ‹FVarsIn ..›; simp [FVarsIn]
  all_goals grind

theorem FVarsBelow.eqv (H : FVarsBelow Δ e₁ ty₁)
    (eq : e₁ == e₂) (eq' : ty₁ == ty₂) : FVarsBelow Δ e₂ ty₂ :=
  fun _ hP he => .eqv eq' (H _ hP (.eqv (BEq.symm eq) he))

theorem TrTyping.eqv (H : TrTyping env Us Δ e₁ ty₁ e' ty')
    (eq : e₁ == e₂) (eq' : ty₁ == ty₂) : TrTyping env Us Δ e₂ ty₂ e' ty' :=
  let ⟨h1, h2, h3, h4⟩ := H
  ⟨.eqv h1 eq eq', h2.eqv eq, h3.eqv eq', h4⟩

variable (env : VEnv) (Us : List Name) (Δ : VLCtx) in
inductive AppStack : Expr → VExpr → List Expr → Prop where
  | head : TrExprS env Us Δ f f' → AppStack f f' []
  | app :
    env.HasType Us.length Δ.toCtx f' (.forallE A B) →
    env.HasType Us.length Δ.toCtx a' A →
    TrExprS env Us Δ f f' →
    TrExprS env Us Δ a a' →
    AppStack (.app f a) (.app f' a') as →
    AppStack f f' (a :: as)

theorem AppStack.build_rev {e : Expr} :
    ∀ {as}, TrExprS env Us Δ (e.mkAppRevList as) e' →
      AppStack env Us Δ (e.mkAppRevList as) e' as' →
      ∃ e', AppStack env Us Δ e e' (as.reverseAux as')
  | [], _, H2 => ⟨_, H2⟩
  | _ :: as, .app h1 h2 h3 h4, H2 =>
    AppStack.build_rev (as := as) h3 (.app h1 h2 h3 h4 H2)

theorem AppStack.tr : AppStack env Us Δ e e' as → TrExprS env Us Δ e e'
  | .head H | .app _ _ H _ _ => H

theorem AppStack.append {e : Expr} (H : AppStack env Us Δ (e.mkAppList as) e' bs) :
    ∃ e', AppStack env Us Δ e e' (as ++ bs) := by
  rw [← Expr.mkAppRevList_reverse] at H
  simpa using AppStack.build_rev H.tr H

theorem AppStack.build {e : Expr} (H : TrExprS env Us Δ (e.mkAppList as) e') :
    ∃ e', AppStack env Us Δ e e' as := by simpa using AppStack.append (.head H)

/-- Recover the ordered abstract argument spine represented by an
`AppStack`. -/
theorem AppStack.translatedArguments
    (H : AppStack env Us Δ fn fn' args) :
    ∃ args' : List VExpr,
      List.Forall₂ (TrExprS env Us Δ) args args' ∧
      TrExprS env Us Δ (fn.mkAppList args) (VExpr.mkApps fn' args') := by
  induction H with
  | head Hfn =>
      exact ⟨[], .nil, by simpa [VExpr.mkApps] using Hfn⟩
  | @app fn arg fn' arg' domain body args _ _ Hfn Harg Htail ih =>
      rcases ih with ⟨args', Hargs, Hfull⟩
      refine ⟨arg' :: args', .cons Harg Hargs, ?_⟩
      simpa [VExpr.mkApps] using Hfull

/-- A translated constant-headed application has one exact translated
universe spine and one ordered abstract term spine. -/
theorem AppStack.constantApplication
    (H : AppStack env Us Δ (.const name levels) abstractHead args) :
    ∃ translatedLevels translatedArgs,
      levels.mapM (VLevel.ofLevel Us) = some translatedLevels ∧
      abstractHead = VExpr.const name translatedLevels ∧
      List.Forall₂ (TrExprS env Us Δ) args translatedArgs ∧
      TrExprS env Us Δ
        ((Expr.const name levels).mkAppList args)
        (VExpr.mkApps (VExpr.const name translatedLevels) translatedArgs) := by
  have Hhead := H.tr
  cases Hhead with
  | const hlookup hlevels hlength =>
      rcases H.translatedArguments with ⟨translatedArgs, Hargs, Hfull⟩
      exact ⟨_, translatedArgs, hlevels, rfl, Hargs, Hfull⟩

/-- Inversion for an application spine: the translation of `f` applied to `as` is the
translation of `f` applied to translations of `as`. -/
theorem TrExprS.mkAppList_inv : ∀ {as : List Expr} {f : Expr} {e'},
    TrExprS env Us Δ (f.mkAppList as) e' →
    ∃ f' as', TrExprS env Us Δ f f' ∧ List.Forall₂ (TrExprS env Us Δ) as as' ∧
      e' = f'.mkApps as'
  | [], _, _, H => ⟨_, [], H, .nil, rfl⟩
  | _ :: as, f, _, H => by
    obtain ⟨_, as', hg, has, rfl⟩ := mkAppList_inv (as := as) (f := .app f _) H
    let .app _ _ hf ha := hg
    exact ⟨_, _ :: as', hf, .cons ha has, rfl⟩

/-! ### Strengthening of translations

Master's inverse weakening lemmas, on `IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean`). -/

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' n Γ Γ') in
theorem VLocalDecl.weak'_iff : VLocalDecl.WF env U Γ' (d.lift' n) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weak'_iff henv hΓ' W
  | .vlet .. => HasType.weak'_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') in
theorem VLocalDecl.weakN_iff : VLocalDecl.WF env U Γ' (d.liftN n k) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weakN_iff henv hΓ' W
  | .vlet .. => HasType.weakN_iff henv hΓ' W

namespace VLCtx

variable! (henv : VEnv.WF env) in
theorem FVLift'.wf (W : FVLift' Δ Δ' dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip_fvar _ _ _ ih => exact ih hΔ'.1
  | cons_fvar _ _ hd W ih =>
    let ⟨hΔ', h1, h2⟩ := hΔ'
    refine ⟨ih hΔ', ?_, (VLocalDecl.weak'_iff henv hΔ'.toCtx W.toCtx).1 h2⟩
    rintro _ _ ⟨⟩; exact ⟨fun h => (h1 _ _ rfl).1 <| W.fvars_sublist.subset h, hd⟩
  | cons_bvar _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weak'_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

variable! (henv : VEnv.WF env) in
theorem BVLift.wf (W : BVLift Δ Δ' dn dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip _ _ ih => exact ih hΔ'.1
  | cons _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weakN_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

end VLCtx

theorem TrExprS.weakFV'_inv (henv : VEnv.WF env)
    (W : VLCtx.FVLift' Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExprS env Us Δ₁ e e') (hc : Closed e dk) (hv : FVarsIn (· ∈ VLCtx.fvars Δ) e) :
    ∃ e', TrExprS env Us Δ e e' := by
  induction H generalizing Δ Δ₂ dk k with
  | @bvar e A Δ₁ i h1 =>
    suffices ∃ p, Δ.find? (.inl i) = some p from let ⟨_, h⟩ := this; ⟨_, .bvar h⟩
    simp [Closed] at hc
    induction W generalizing i e A Δ₁ with | @cons_bvar _ Δ₂ _ _ _ d _ ih => ?_ | _ => cases hc
    obtain ⟨d, Δ₂, rfl, hΔ₁⟩ : ∃ d Δ₁', Δ₁ = (none, d) :: Δ₁' ∧
        VLCtx.IsDefEq env Us.length Δ₁' Δ₂ := by cases d <;> cases hΔ <;> exact ⟨_, _, rfl, ‹_›⟩
    simp [VLCtx.find?] at h1 ⊢
    rcases i with _ | i <;> simp [VLCtx.next] at h1 ⊢
    obtain ⟨_, _, h1, _⟩ := h1
    have ⟨_, h1⟩ := ih h1 hΔ₁ (Nat.lt_of_succ_lt_succ hc) hv
    exact ⟨_, _, _, _, h1, rfl, rfl⟩
  | @fvar _ _ _ fv => let ⟨_, h⟩ := VLCtx.find?_eq_some.2 hv; exact ⟨_, .fvar h⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 hf ha ih1 ih2 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨f₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    let ⟨a₁, ih2⟩ := ih2 W hΔ hc.2 hv.2
    have h1 := h1.defeqU_l henv hΔ₁.toCtx <| hf.uniq henv hΔ (ih1.weakFV' henv W hΔ₂)
    have h2 := h2.defeqU_l henv hΔ₁.toCtx <| ha.uniq henv hΔ (ih2.weakFV' henv W hΔ₂)
    have := VExpr.WF.weak'_iff henv hΔ₂.toCtx W.toCtx (e := f₁.app a₁)
    have := this.1 ⟨_, (h1.app h2).defeqDFC henv hΔ.defeqCtx⟩
    have ⟨_, _, h1, h2⟩ := this.app_inv henv (W.wf henv hΔ₂).toCtx
    exact ⟨_, .app h1 h2 ih1 ih2⟩
  | lam h1 ht _ ih1 ih2 =>
    let ⟨_, h1⟩ := h1
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    have htt := ht.uniq henv hΔ (ih1.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _))
      (hΔ.cons (ofv := none) nofun <| .vlam htt) hc.2 hv.2.fvars_cons
    have h1 := HasType.weak'_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx
      |>.1 (htt.hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .lam ⟨_, h1⟩ ih1 ih2⟩
  | forallE h1 h2 ht hb ih1 ih2 =>
    let ⟨_, h1⟩ := h1; let ⟨_, h2⟩ := h2
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    have htt := ht.uniq henv hΔ (ih1.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have hΔ' := hΔ.cons (ofv := none) nofun <| .vlam htt
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _)) hΔ' hc.2 hv.2.fvars_cons
    have h1' := htt.hasType.2.defeqDFC henv hΔ.defeqCtx
    have h1 := HasType.weak'_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx |>.1 h1'
    have hΔ₂' : VLCtx.WF _ _ ((none, .vlam _) :: _) := ⟨hΔ₂, nofun, _, h1'⟩
    have h2 := (HasType.weak'_iff (A := .sort _) henv hΔ₂'.toCtx (W.cons_bvar (.vlam _)).toCtx).1 <|
      hb.uniq henv hΔ' (ih2.weakFV' henv (W.cons_bvar _) hΔ₂')
      |>.of_l (Γ := _::_) henv ⟨hΔ₁.toCtx, _, htt.hasType.1⟩ h2
      |>.hasType.2.defeqDFC henv (.succ hΔ.defeqCtx htt)
    exact ⟨_, .forallE ⟨_, h1⟩ ⟨_, h2⟩ ih1 ih2⟩
  | letE h1 ht ha _ ih1 ih2 ih3 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    let ⟨val₁, ih2⟩ := ih2 W hΔ hc.2.1 hv.2.1
    have hvv := ha.uniq henv hΔ (ih2.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    let ⟨_, h2⟩ := h1.isType henv hΔ₁.toCtx
    have htt := ht.uniq henv hΔ (ih1.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h2
    have ⟨_, ih3⟩ := ih3 (W.cons_bvar (.vlet ..))
      (hΔ.cons nofun <| .vlet hvv htt) hc.2.2 hv.2.2.fvars_cons
    have h1 := HasType.weak'_iff henv hΔ₂.toCtx W.toCtx
      |>.1 ((htt.defeqDF hvv).hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .letE h1 ih1 ih2 ih3⟩
  | lit h1 _ ih => let ⟨_, ih⟩ := ih W hΔ .toConstructor .toConstructor; exact ⟨_, .lit h1 ih⟩
  | mdata _ ih => let ⟨_, ih⟩ := ih W hΔ hc hv; exact ⟨_, .mdata ih⟩
  | proj h1 h2 ih =>
    have hΔ₂ := (hΔ.symm henv).wf
    let ⟨_, ih⟩ := ih W hΔ hc hv
    have htt := h1.uniq henv hΔ (ih.weakFV' henv W hΔ₂)
    have h2 := VExpr.WF.proj_defeqDFC henv hΔ.defeqCtx htt h2
    exact ⟨_, .proj ih ((VExpr.WF.weak'_iff henv hΔ₂.toCtx W.toCtx).1 h2)⟩

theorem TrExprS.weakFV_inv (henv : VEnv.WF env)
    (W : VLCtx.FVLift Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExprS env Us Δ₁ e e') (hc : Closed e dk) (hv : FVarsIn (· ∈ VLCtx.fvars Δ) e) :
    ∃ e', TrExprS env Us Δ e e' := H.weakFV'_inv henv W.toFVLift' hΔ hc hv

