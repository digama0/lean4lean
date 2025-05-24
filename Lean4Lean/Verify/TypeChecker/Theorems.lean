import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.TypeChecker

namespace Lean4Lean

namespace TypeChecker
open Lean

def Methods.WF : Methods → Prop := sorry

structure VContext extends Context where
  venv : VEnv
  venv_wf : VEnv.WF venv
  trenv : TrEnv safety env venv
  vlctx : VLCtx

nonrec abbrev VContext.TrExpr (c : VContext) : Expr → VExpr → Prop :=
  TrExpr c.venv c.lparams c.vlctx
nonrec abbrev VContext.IsType (c : VContext) : VExpr → Prop :=
  c.venv.IsType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.HasType (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.IsDefEqU (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx

structure VState extends State where

class VState.WF (c : VContext) (s : VState) where
  trctx : TrLCtx c.venv c.lparams c.lctx c.vlctx
  vlctx_wf : OnCtx c.vlctx.toCtx (c.venv.IsType c.lparams.length)
  ngen_wf : ∀ fv ∈ c.vlctx.fvars, s.ngen.Reserves fv

def VState.LE (s₁ s₂ : VState) : Prop :=
  s₁.ngen ≤ s₂.ngen

theorem VState.LE.rfl {s : VState} : s.LE s := NameGenerator.LE.rfl

theorem VState.LE.trans {s₁ : VState} {s₂ : VState} {s₃ : VState}
    (h₁ : s₁.LE s₂) (h₂ : s₂.LE s₃) : s₁.LE s₃ :=
  NameGenerator.LE.trans h₁ h₂

def M.WF (c : VContext) (vs : VState) (x : M α) (Q : α → VState → Prop) : Prop :=
  vs.WF c → ∀ a s', x c.toContext vs.toState = .ok (a, s') →
    ∃ vs', vs'.toState = s' ∧ vs.LE vs' ∧ vs'.WF c ∧ Q a vs'

theorem M.WF.bind {c : VContext} {s : VState} {x : M α} {f : α → M β} {Q R}
    (h1 : x.WF c s Q)
    (h2 : ∀ a s', s.LE s' → Q a s' → (f a).WF c s' R) :
    (x >>= f).WF c s R := by
  intro wf₁ a vs₁
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨vs₂, eq1, le1, wf₂, h1⟩ := h1 wf₁ _ _ eq
  obtain ⟨vs₃, rfl, le2, wf₃, h2⟩ := h2 _ _ le1 h1 wf₂ _ _ (eq1 ▸ h)
  exact ⟨_, rfl, le1.trans le2, wf₃, h2⟩

theorem M.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) :
    (pure a : M α).WF c s Q := by rintro h _ _ ⟨⟩; exact ⟨_, rfl, .rfl, h, H⟩

theorem M.WF.le {c : VContext} {s : VState} {Q R} {x : M α}
    (h1 : x.WF c s Q) (H : ∀ a s', s.LE s' → Q a s' → R a s') :
    x.WF c s R := fun wf _ _ e =>
  let ⟨_, a1, a2, a3, a4⟩ := h1 wf _ _ e
  ⟨_, a1, a2, a3, H _ _ a2 a4⟩

def RecM.WF (c : VContext) (s : VState) (x : RecM α) (Q : α → VState → Prop) : Prop :=
  ∀ m, m.WF → M.WF c s (x m) Q

theorem M.WF.lift {c : VContext} {s : VState} {x : M α} {Q} (h : x.WF c s Q) :
    RecM.WF c s x Q := fun _ _ => h

instance : Coe (M.WF c s x Q) (RecM.WF c s x Q) := ⟨M.WF.lift⟩

theorem RecM.WF.bind {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s.LE s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  fun _ h => M.WF.bind (h1 _ h) (fun _ _ h1' h2' => h2 _ _ h1' h2' _ h)

theorem RecM.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) : (pure a : RecM α).WF c s Q :=
  fun _ _ => .pure H

theorem RecM.WF.le {c : VContext} {s : VState} {Q R} {x : RecM α}
    (h1 : x.WF c s Q) (H : ∀ a s', s.LE s' → Q a s' → R a s') :
    x.WF c s R := fun _ h => (h1 _ h).le H

theorem mkFreshId.WF {c : VContext} {s : VState} :
    M.WF c s mkFreshId fun a s' => s'.ngen.Reserves ⟨a⟩ ∧ c.lctx.find? ⟨a⟩ = none :=
  sorry

theorem getLCtx.WF {c : VContext} {s : VState} :
    M.WF c s getLCtx fun a s' => c.lctx = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.getLCtx {c : VContext} {s : VState} {f : LocalContext → RecM α} {Q}
    (H : WF c s (f c.lctx) Q) : (getLCtx >>= f).WF c s Q :=
  getLCtx.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.stateWF {c : VContext} {s : VState} {x : RecM α} {Q}
    (H : s.WF c → WF c s x Q) : WF c s x Q :=
  fun _ h wf => H wf _ h wf

def VContext.pushLDecl (c : VContext)
    (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) : VContext :=
  { c with
    vlctx := (some id, .vlam ty') :: c.vlctx
    lctx := c.lctx.mkLocalDecl id name ty bi }

theorem RecM.WF.withLam {c : VContext} {s : VState} {f : RecM α} {Q}
    {id name ty ty' bi}
    (h0 : s.ngen.Reserves id)
    (h1 : c.lctx.find? id = none)
    (h2 : c.TrExpr ty ty')
    (h3 : c.IsType ty')
    (H : WF (c.pushLDecl id name ty ty' bi) s f Q) :
    (Inner.withLCtx (c.lctx.mkLocalDecl id name ty bi) f).WF c s Q := by
  intro _ h wf a s' e
  have : VState.WF (c.pushLDecl id name ty ty' bi) s := {
    ngen_wf := by simpa [VContext.pushLDecl] using ⟨h0, wf.ngen_wf⟩
    trctx := wf.trctx.mkLocalDecl h1 h2 h3
    vlctx_wf := ⟨wf.vlctx_wf, h3⟩
  }
  obtain ⟨s', hs1, hs2, wf', hs4⟩ := H _ h this a s' e
  refine ⟨s', hs1, hs2, { wf with ngen_wf := ?_ }, hs4⟩
  have := wf'.ngen_wf; simp [VContext.pushLDecl] at this; exact this.2

namespace Inner

theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExpr e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  sorry

theorem checkType.WF {c : VContext} {s : VState} :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty',
      c.TrExpr e e' ∧ c.TrExpr ty ty' ∧ c.HasType e' ty' :=
  sorry

theorem ensureSortCore.WF {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      ∃ u, c.IsDefEqU e' (.sort u) ∧ c.TrExpr e1 (.sort u) :=
  sorry

theorem inferLambda.loop.WF
    (he : c.TrExpr e e')
    (hty : c.HasType e' ty') :
    (inferLambda.loop true fvars e).WF c s Q := by
  unfold inferLambda.loop; split
  · rename_i name dom body bi; simp
    refine mkFreshId.WF.lift.bind fun a s' le ⟨res, h6⟩ => .getLCtx ?_
    refine .stateWF fun wf => ?_
    let ⟨_, .lam h1 h2 h3, _⟩ := he
    have := h2.trExpr c.venv_wf wf.trctx.wf
    -- refine RecM.WF.withLam res h6 h1 ⟨_, h3.defeqU_r c.venv_wf wf.vlctx_wf h4⟩ ?_
    -- exact inferLambda.loop.WF
    sorry
  · sorry

theorem checkLambda.loop.WF {c₀ : VContext} {e₀ : Expr}
    : (inferLambda.loop false fvars e).WF c s (fun ty _ => ∃ e' ty',
      c₀.TrExpr e₀ e' ∧ c₀.TrExpr ty ty' ∧ c₀.HasType e' ty') := by
  unfold inferLambda.loop; split <;> simp only [pure_bind] <;>
    refine checkType.WF.bind fun ty _ _ ⟨ty', uv', h1, h2, h3⟩ => ?_
  · refine (ensureSortCore.WF h2).bind fun _ _ _ ⟨u, h4, h5⟩ => ?_
    refine mkFreshId.WF.lift.bind fun a s' le ⟨res, h6⟩ => .getLCtx ?_
    refine .stateWF fun wf => ?_
    refine RecM.WF.withLam res h6 h1 ⟨_, h3.defeqU_r c.venv_wf wf.vlctx_wf h4⟩ ?_
    exact checkLambda.loop.WF
  · refine .getLCtx <| .pure ?_
    sorry

theorem inferLambda.WF : (inferLambda e true).WF c s Q := by
  simp [inferLambda]
  sorry
