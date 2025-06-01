import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.EnvLemmas
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Level
import Lean4Lean.Verify.LocalContext
import Lean4Lean.TypeChecker

namespace Except

def WF (x : Except ε α) (Q : α → Prop) : Prop := ∀ a, x = .ok a → Q a

theorem WF.bind {x : Except ε α} {f : α → Except ε β} {Q R}
    (h1 : x.WF Q)
    (h2 : ∀ a, Q a → (f a).WF R) :
    (x >>= f).WF R := by
  intro b
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  exact h2 _ (h1 _ rfl) _

theorem WF.pure {Q} (H : Q a) :
    (pure a : Except ε α).WF Q := by rintro _ ⟨⟩; exact H

theorem WF.map {x : Except ε α} {f : α → β} {Q R}
    (h1 : x.WF Q)
    (h2 : ∀ a, Q a → R (f a)) :
    (f <$> x).WF R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ h => .pure (h2 _ h)

theorem WF.throw {Q} : (throw e : Except ε α).WF Q := nofun

theorem WF.le {Q R} {x : Except ε α}
    (h1 : x.WF Q) (H : ∀ a, Q a → R a) :
    x.WF R := fun _ e => H _ (h1 _ e)

end Except

namespace Lean4Lean

namespace TypeChecker
open Lean hiding Environment Exception
open Kernel

inductive MLCtx where
  | nil : MLCtx
  | vlam (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) : MLCtx → MLCtx
  | vlet (id : FVarId) (name : Name) (ty v : Expr) (ty' v' : VExpr) : MLCtx → MLCtx

@[simp] def MLCtx.vlctx : MLCtx → VLCtx
  | .nil => []
  | .vlam id _ _ ty _ c => (some id, .vlam ty) :: c.vlctx
  | .vlet id _ _ _ ty v c => (some id, .vlet ty v) :: c.vlctx

def MLCtx.lctx : MLCtx → LocalContext
  | .nil => {}
  | .vlam id name ty _ bi c => c.lctx.mkLocalDecl id name ty bi
  | .vlet id name ty val _ _ c => c.lctx.mkLetDecl id name ty val

@[simp] def MLCtx.length : MLCtx → Nat
  | .nil => 0
  | .vlam _ _ _ _ _ c
  | .vlet _ _ _ _ _ _ c => c.length + 1

def MLCtx.decls : MLCtx → List LocalDecl
  | .nil => {}
  | .vlam x name ty _ bi c => .cdecl c.length x name ty bi .default :: c.decls
  | .vlet x name ty v _ _ c => .ldecl c.length x name ty v false default :: c.decls

@[simp] def MLCtx.fvarRevList (c : MLCtx) (n) (hn : n ≤ c.length) : List FVarId :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam id _ _ _ _ c, h
  | n+1, .vlet id _ _ _ _ _ c, h => id :: c.fvarRevList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] def MLCtx.dropN (c : MLCtx) (n) (hn : n ≤ c.length) : MLCtx :=
  match n, c, hn with
  | 0, c, _ => c
  | n+1, .vlam _ _ _ _ _ c, h
  | n+1, .vlet _ _ _ _ _ _ c, h => c.dropN n (Nat.le_of_succ_le_succ h)
termination_by structural n

def MLCtx.WF (env : VEnv) (Us : List Name) : MLCtx → Prop
  | .nil => True
  | .vlam fv _ ty ty' _ c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧
    env.IsType Us.length c.vlctx.toCtx ty'
  | .vlet fv _ ty v ty' v' c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧ TrExprS env Us c.vlctx v v' ∧
    env.HasType Us.length c.vlctx.toCtx v' ty'

theorem MLCtx.WF.tr : ∀ {c : MLCtx}, c.WF env Us → TrLCtx env Us c.lctx c.vlctx
  | .nil, _ => ⟨.nil, .nil⟩
  | .vlam .., ⟨h1, h2, h3, h4⟩ => .mkLocalDecl h1.tr h2 h3 h4
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => .mkLetDecl h1.tr h2 h3 h4 h5

theorem MLCtx.WF.dropN {c : MLCtx} (n hn) : c.WF env Us → (c.dropN n hn).WF env Us :=
  match n, c, hn with
  | 0, _, _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h => fun H => H.1.dropN n (Nat.le_of_succ_le_succ h)

theorem MLCtx.noBV (c : MLCtx) : c.vlctx.NoBV := by
  induction c <;> trivial

structure VContext extends Context where
  venv : VEnv
  venv_wf : VEnv.WF venv
  trenv : TrEnv safety env venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx

@[simp] abbrev VContext.lctx' (c : VContext) := c.mlctx.lctx
@[simp] abbrev VContext.vlctx (c : VContext) := c.mlctx.vlctx

theorem VContext.trlctx (c : VContext) : TrLCtx c.venv c.lparams c.lctx' c.vlctx :=
  c.mlctx_wf.tr

nonrec abbrev VContext.TrExprS (c : VContext) : Expr → VExpr → Prop :=
  TrExprS c.venv c.lparams c.vlctx
nonrec abbrev VContext.TrExpr (c : VContext) : Expr → VExpr → Prop :=
  TrExpr c.venv c.lparams c.vlctx
nonrec abbrev VContext.IsType (c : VContext) : VExpr → Prop :=
  c.venv.IsType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.HasType (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.IsDefEqU (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.TrLCtx (c : VContext) : Prop :=
  TrLCtx c.venv c.lparams c.lctx' c.vlctx

class VContext.MLCWF (c : VContext) (m : MLCtx) : Prop where
  wf : m.WF c.venv c.lparams

instance (c : VContext) : c.MLCWF c.mlctx := ⟨c.mlctx_wf⟩

structure VState extends State where

class VState.WF (c : VContext) (s : VState) where
  trctx : c.TrLCtx
  ngen_wf : ∀ fv ∈ c.vlctx.fvars, s.ngen.Reserves fv

theorem VState.WF.find?_eq_none {id}
    (wf : VState.WF c s) (H : ¬s.ngen.Reserves id) : c.lctx'.find? id = none :=
  wf.trctx.find?_eq_none.2 fun h => H (wf.ngen_wf _ h)

def VState.LE (s₁ s₂ : VState) : Prop :=
  s₁.ngen ≤ s₂.ngen

theorem VState.LE.rfl {s : VState} : s.LE s := NameGenerator.LE.rfl

theorem VState.LE.trans {s₁ s₂ s₃ : VState} (h₁ : s₁.LE s₂) (h₂ : s₂.LE s₃) : s₁.LE s₃ :=
  NameGenerator.LE.trans h₁ h₂

theorem VState.LE.reservesV {s₁ s₂ : VState} (h : s₁.LE s₂) {{fv}} :
    s₁.ngen.Reserves fv → s₂.ngen.Reserves fv :=
  (·.mono h)

theorem VState.LE.reserves {s₁ s₂ : VState} (h : s₁.LE s₂) {{e}} :
    FVarsIn s₁.ngen.Reserves e → FVarsIn s₂.ngen.Reserves e :=
  (·.mono h.reservesV)

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

theorem M.WF.throw {c : VContext} {s : VState} {Q} : (throw e : M α).WF c s Q := nofun

theorem M.WF.le {c : VContext} {s : VState} {Q R} {x : M α}
    (h1 : x.WF c s Q) (H : ∀ a s', s.LE s' → Q a s' → R a s') :
    x.WF c s R := fun wf _ _ e =>
  let ⟨_, a1, a2, a3, a4⟩ := h1 wf _ _ e
  ⟨_, a1, a2, a3, H _ _ a2 a4⟩

structure Methods.WF (m : Methods) where
  isDefEqCore : c.TrExpr e₁ e₁' → c.TrExpr e₂ e₂' →
    M.WF c s (m.isDefEqCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂'
  whnfCore : c.TrExpr e e' → M.WF c s (m.whnfCore e cheapRec cheapProj) fun e₁ _ => c.TrExpr e₁ e'
  whnf : c.TrExpr e e' → M.WF c s (m.whnf e) fun e₁ _ => c.TrExpr e₁ e'
  checkType : e.FVarsIn s.ngen.Reserves →
    M.WF c s (m.inferType e false) fun ty _ => ∃ e' ty',
      c.TrExprS e e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty'
  inferType : c.TrExprS e e' → c.HasType e' ty' →
    M.WF c s (m.inferType e true) fun ty _ => c.TrExpr ty ty'

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

theorem RecM.WF.throw {c : VContext} {s : VState} {Q} : (throw e : RecM α).WF c s Q := nofun

theorem RecM.WF.le {c : VContext} {s : VState} {Q R} {x : RecM α}
    (h1 : x.WF c s Q) (H : ∀ a s', s.LE s' → Q a s' → R a s') :
    x.WF c s R := fun _ h => (h1 _ h).le H

theorem mkFreshId.WF {c : VContext} {s : VState} :
    M.WF c s mkFreshId fun a s' => s'.ngen.Reserves ⟨a⟩ ∧ ¬s.ngen.Reserves ⟨a⟩ := by
  rintro wf n s ⟨⟩
  refine have le := .next; ⟨{ s with toState := _ }, rfl, le, ?_, ?_, ?_⟩
  · exact { wf with ngen_wf _ h := le.reservesV (wf.ngen_wf _ h) }
  · exact s.ngen.next_reserves_self
  · exact s.ngen.not_reserves_self

theorem getEnv.WF {c : VContext} {s : VState} :
    M.WF c s getEnv fun a s' => c.env = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.getEnv {c : VContext} {s : VState} {f : Environment → RecM α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q :=
  getEnv.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem getLCtx.WF {c : VContext} {s : VState} :
    M.WF c s getLCtx fun a s' => c.lctx' = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, c.lctx_eq, rfl⟩

theorem RecM.WF.getLCtx {c : VContext} {s : VState} {f : LocalContext → RecM α} {Q}
    (H : WF c s (f c.lctx') Q) : (getLCtx >>= f).WF c s Q :=
  getLCtx.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem getNGen.WF {c : VContext} {s : VState} :
    M.WF c s getNGen fun a s' => s.ngen = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → M α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q :=
  getNGen.WF.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → RecM α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q :=
  getNGen.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.stateWF {c : VContext} {s : VState} {x : RecM α} {Q}
    (H : s.WF c → WF c s x Q) : WF c s x Q :=
  fun _ h wf => H wf _ h wf

def VContext.withMLC (c : VContext) (m : MLCtx) [wf : c.MLCWF m] : VContext :=
  { c with
    mlctx := m
    mlctx_wf := wf.1
    lctx := m.lctx
    lctx_eq := rfl }

@[simp] theorem VContext.withMLC_self (c : VContext) : c.withMLC c.mlctx = c := by
  simp [withMLC, c.lctx_eq]

protected theorem RecM.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → RecM α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (H : ∀ id cwf' s', s.LE s' →
      s'.ngen.Reserves id →
      ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLocalDecl name ty bi f).WF (c.withMLC m) s Q := by
  simp [withLocalDecl, withFreshId]
  refine .stateWF fun wf => ?_
  refine fun _ mwf => mkFreshId.WF.bind fun id s le ⟨h0, h1⟩ wf' a s' e => ?_
  have h1' := wf.find?_eq_none h1
  have cwf' : c.MLCWF (.vlam ⟨id⟩ name ty ty' bi m) := ⟨cwf.1, h1', hty, hty'⟩
  have : VState.WF (c.withMLC (.vlam ⟨id⟩ name ty ty' bi m)) s := {
    ngen_wf := by simp [VContext.withMLC]; exact ⟨h0, wf'.ngen_wf⟩
    trctx := wf.trctx.mkLocalDecl h1' hty hty'
  }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ le h0 h1 _ mwf this a s' e
  refine ⟨s', hs1, hs2, { wf with ngen_wf := ?_ }, hs4⟩
  have := wf'.ngen_wf; simp [VContext.withMLC] at this; exact this.2

protected theorem RecM.WF.withLetDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → RecM α} {Q name ty ty'}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hval : (c.withMLC m).TrExprS val val')
    (hval' : (c.withMLC m).HasType val' ty')
    (H : ∀ id cwf' s', s.LE s' →
      s'.ngen.Reserves id →
      ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlet id name ty val ty' val' m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLetDecl name ty val f).WF (c.withMLC m) s Q := by
  simp [withLetDecl, withFreshId]
  refine .stateWF fun wf => ?_
  refine fun _ mwf => mkFreshId.WF.bind fun id s le ⟨h0, h1⟩ wf' a s' e => ?_
  have h1' := wf.find?_eq_none h1
  have cwf' : c.MLCWF (.vlet ⟨id⟩ name ty val ty' val' m) := ⟨cwf.1, h1', hty, hval, hval'⟩
  have : VState.WF (c.withMLC (.vlet ⟨id⟩ name ty val ty' val' m)) s := {
    ngen_wf := by simp [VContext.withMLC]; exact ⟨h0, wf'.ngen_wf⟩
    trctx := wf.trctx.mkLetDecl h1' hty hval hval'
  }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ le h0 h1 _ mwf this a s' e
  refine ⟨s', hs1, hs2, { wf with ngen_wf := ?_ }, hs4⟩
  have := wf'.ngen_wf; simp [VContext.withMLC] at this; exact this.2

@[simp] def MLCtx.mkForall (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, e =>
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstractFVar x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkForall n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstractFVar x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

@[simp] def MLCtx.mkForall' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) (.forallE ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

@[simp] def MLCtx.mkLambda (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) (.lam name ty (.abstractFVar x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstractFVar x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

@[simp] def MLCtx.mkLambda' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) (.lam ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkForall_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  induction n generalizing c e e' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, h4⟩ := wf
      refine ih h1 ?_ (.forallE h4 H2) _
      exact .forallE h4 H2 h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.WF.mkForall'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ (.sort u)) (n hn) :
    ∃ u, env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkForall' n hn e₁) (c.mkForall' n hn e₂) (.sort u) := by
  induction n generalizing c e₁ e₂ u with
  | zero => exact ⟨_, H⟩
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.forallEDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkForall_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  let ⟨_, H1, eq⟩ := H1
  let ⟨_, H2⟩ := H2
  have eq := eq.of_r henv wf.tr.wf H2
  have ⟨_, H⟩ := wf.mkForall'_congr eq n hn
  have := wf.mkForall_trS henv H1 ⟨_, eq.hasType.1⟩ n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLambda_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf
      refine ih h1 ?_ (.lam h4 H2) _
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.WF.mkLambda'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ ty) (n hn) :
    env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e₁) (c.mkLambda' n hn e₂) (c.mkForall' n hn ty) := by
  induction n generalizing c e₁ e₂ ty with
  | zero => exact H
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.lamDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkLambda_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  let ⟨_, H1, eq⟩ := H1
  have eq := eq.of_r henv wf.tr.wf H2
  have H := wf.mkLambda'_congr eq n hn
  have := wf.mkLambda_trS henv H1 eq.hasType.1 n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

theorem MLCtx.fvarRevList_prefix (c : MLCtx)
    {n hn} : c.fvarRevList n hn <+: c.vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => match c with | .vlam .. | .vlet .. => simp [ih]

theorem MLCtx.WF.fvars_nodup : ∀ {c : MLCtx}, c.WF env Us → c.vlctx.fvars.Nodup
  | .nil, _ => .nil
  | .vlam _ _ _ _ _ c, ⟨h1, h2, _⟩
  | .vlet _ _ _ _ _ _ c, ⟨h1, h2, _⟩ => by simp [h1.fvars_nodup, h1.tr.find?_eq_none.1 h2]

theorem MLCtx.WF.fvarRevList_nodup {c : MLCtx} (wf : c.WF env Us)
    (n hn) : (c.fvarRevList n hn).Nodup :=
  c.fvarRevList_prefix.sublist.nodup wf.fvars_nodup

theorem MLCtx.WF.decls_size {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.decls.size = c.length := by
  rw [← wf.tr.1.decls_wf.toList'_length]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLocalDecl, ih wf.1]
  | vlet _ _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLetDecl, ih wf.1]

theorem MLCtx.WF.toList_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.toList = c.decls := by
  simp [LocalContext.toList]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLocalDecl, decls, ih wf.1, wf.1.decls_size]
  | vlet _ _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLetDecl, decls, ih wf.1, wf.1.decls_size]

theorem MLCtx.WF.find?_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.find? x = c.decls.find? (x == ·.fvarId) := by
  simp [wf.tr.1.find?_eq_find?_toList, wf.toList_eq]

theorem MLCtx.WF.mkForall_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) :
    c.lctx.mkForall' arr e = c.mkForall n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkForall', this, ← List.map_reverse, LocalContext.mkBinding'_eq,
    LocalContext.mkBindingList_eq_fold, List.foldr_reverse]
  · clear harr this
    induction n generalizing c e with
    | zero => simp [tr]
    | succ n ih =>
      match c with
      | .vlam .. | .vlet .. =>
        simp
        refine (List.foldl_congr fun _ y h => ?_).trans <|
          .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
        · refine LocalContext.mkBindingList1_congr ?_
          rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
          simp [LocalDecl.fvarId]; rintro ⟨⟩
          have := wf.fvarRevList_nodup (n+1) hn; simp_all
        · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
  · intro _ h
    exact wf.tr.find?_eq_some.2 ((MLCtx.fvarRevList_prefix ..).subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (wf.fvarRevList_nodup ..)

theorem MLCtx.WF.mkLambda_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) :
    c.lctx.mkLambda' arr e = c.mkLambda n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkLambda', this, ← List.map_reverse, LocalContext.mkBinding'_eq,
    LocalContext.mkBindingList_eq_fold, List.foldr_reverse]
  · clear harr this
    induction n generalizing c e with
    | zero => simp [tr]
    | succ n ih =>
      match c with
      | .vlam .. | .vlet .. =>
        simp
        refine (List.foldl_congr fun _ y h => ?_).trans <|
          .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
        · refine LocalContext.mkBindingList1_congr ?_
          rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
          simp [LocalDecl.fvarId]; rintro ⟨⟩
          have := wf.fvarRevList_nodup (n+1) hn; simp_all
        · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
  · intro _ h
    exact wf.tr.find?_eq_some.2 ((MLCtx.fvarRevList_prefix ..).subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (wf.fvarRevList_nodup ..)

namespace Inner

theorem whnfCore.WF {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (whnfCore e cheapRec cheapProj) fun e₁ _ => c.TrExpr e₁ e' :=
  fun _ wf => wf.whnfCore he

theorem whnf.WF {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.TrExpr e₁ e' :=
  fun _ wf => wf.whnf he

theorem isDefEqCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExpr e₁ e₁') (he₂ : c.TrExpr e₂ e₂') :
    RecM.WF c s (isDefEqCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  fun _ wf => wf.isDefEqCore he₁ he₂

theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  fun _ wf => wf.inferType he hty

theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn s.ngen.Reserves) :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty',
      c.TrExprS e e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty' :=
  fun _ wf => wf.checkType h1

theorem ensureSortCore.WF {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      (∃ u, e1 = .sort u) ∧ c.TrExpr e1 e' := by
  simp [ensureSortCore]; split
  · let .sort _ := e --; let ⟨_, .sort _, h⟩ := he
    exact .pure ⟨⟨_, rfl⟩, he⟩
  refine (whnf.WF he).bind fun e _ _ he => ?_; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ =>
      (∃ name ty body bi, e1 = .forallE name ty body bi) ∧ c.TrExpr e1 e' := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨⟨_, _, _, _, rfl⟩, he⟩
  refine (whnf.WF he).bind fun e _ _ he => ?_; split
  · let .forallE .. := e
    exact .pure ⟨⟨_, _, _, _, rfl⟩, he⟩
  exact .getEnv <| .getLCtx .throw

theorem checkLevel.WF {c : VContext} (H : l.realHasMVar = false) :
    (checkLevel c.toContext l).WF fun _ => ∃ u', VLevel.ofLevel c.lparams l = some u' := by
  simp [checkLevel]; split <;> [exact .throw; refine .pure ?_]
  have := l.safeSorry -- FIXME
  exact Level.getUndefParam_none this H (by rename_i h; simpa using h)

theorem inferFVar.WF {c : VContext} :
    (inferFVar c.toContext name).WF fun ty =>
      ∃ e' ty', c.TrExprS (.fvar name) e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty' := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  rw [c.mlctx_wf.tr.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, h2⟩ := c.mlctx_wf.tr.find?_of_mem c.venv_wf (List.mem_of_find?_eq_some h)
  exact ⟨_, (.fvar h1), _, h2,
    c.mlctx_wf.tr.wf.find?_wf c.venv_wf h1⟩

theorem envGet.WF {c : VContext} :
    (c.env.get name).WF fun ci => c.env.find? name = some ci := by
  simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]

theorem checkConstant.WF {c : VContext}
    (H : ∀ l ∈ ls, l.realHasMVar = false) :
    (inferConstant c.toContext name ls false).WF fun ty =>
      ∃ e' ty', c.TrExprS (.const name ls) e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty' := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq => ?_
  have : (ls.foldlM (fun b a => checkLevel c.toContext a) PUnit.unit).WF (fun _ =>
      ∃ ls', List.mapM (VLevel.ofLevel c.lparams) ls = some ls') := by
    induction ls with
    | nil => exact .pure ⟨_, rfl⟩
    | cons l ls ih =>
      simp at H
      refine (checkLevel.WF H.1).bind fun ⟨⟩ ⟨_, h1⟩ => ?_
      refine (ih H.2).le fun _ ⟨_, h2⟩ => ?_
      simp [h1, h2]
  split <;> [skip; exact .throw]
  split <;> [exact .throw; skip]
  generalize eq1 : _ <$> (_ : Except Exception _) = F
  generalize eq2 : (fun ty : Expr => _) = P
  suffices ci.isPartial = false ∨ (c.safety == .safe) = false → F.WF P by
    split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
    split <;> [exact .throw; skip]
    rename_i h; simp [ConstantInfo.isPartial, Decidable.imp_iff_not_or] at h
    exact this h
  subst eq1 eq2; rename_i h1 h2; intro h3
  refine this.map fun _ ⟨_, H⟩ => ?_
  have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq <| by
    revert h2 h3
    cases c.safety <;> simp [isAsSafeAs] <;> cases ci.isUnsafe <;> simp +decide
  have eq := h1.symm.trans h5
  refine ⟨_, .const h4 H eq, _, ?_, .const h4 ?_ ((List.length_option_mapM H).symm.trans eq)⟩
  · sorry
  · intro _ h
    have ⟨_, h1, h2⟩ := List.mem_option_mapM H _ h
    exact VLevel.WF.of_ofLevel h2

theorem checkLambda.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn (e.instantiateList ((m.fvarRevList n hn).map .fvar)))
    (hr1 : e.FVarsIn s.ngen.Reserves)
    (hr2 : ∀ v ∈ m.vlctx.fvars, s.ngen.Reserves v) :
    (inferLambda.loop false arr e).WF (c.withMLC m) s (fun ty _ =>
      ∃ e', c.TrExprS e₀ e' ∧ ∃ ty', c.TrExprS ty ty' ∧ c.HasType e' ty') := by
  unfold inferLambda.loop
  simp [Expr.instantiateRev', Expr.instantiate', harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    refine (checkType.WF ?_).bind fun uv _ le₁ ⟨dom', uv', h1, h2, h3⟩ => ?_
    · apply hr1.1.instantiateList; simp
      exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
    refine (ensureSortCore.WF (h2.trExpr c.venv_wf mwf.1.tr.wf)).bind fun _ _ le₂ ⟨h4, h5⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' fun a mwf' s' le₃ res h6 => ?_
    have h6' := wf.find?_eq_none h6
    refine .stateWF fun wf' => ?_
    have := le₁.trans le₂ |>.trans le₃
    refine checkLambda.loop.WF (Nat.succ_le_succ hn)
      (by simp [hdrop]) (by simp [harr]) ?_ (this.reserves hr1).2 ?_ --?_
    · simp [he₀]; congr 1
      simp [Expr.instantiateRev', Expr.instantiate', harr, Expr.instantiateList_lam]
      conv => enter [2,2]; exact (Expr.instantiateList_instantiate1_comm (by trivial)).symm
      refine (FVarsIn.abstract_instantiate1 ((hr1.2.instantiateList ?_).mono ?_)).symm
      · simp [FVarsIn]; exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
      · rintro _ h rfl; exact h6 <| (le₁.trans le₂).reservesV h
    · simp [or_imp, forall_and, FVarsIn]
      exact ⟨res, fun _ h => this.reservesV (hr2 _ h)⟩
  · refine (checkType.WF ?_).bind fun ty _ _ ⟨e', ty', h1, h2, h3⟩ => ?_
    · apply hr1.instantiateList; simp
      exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have := ty.safeSorry -- FIXME
    have ⟨_, h2, e2⟩ := h2.trExpr c.venv_wf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.venv_wf wf.trctx.wf this m.noBV
    have h3 := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLambda_trS c.venv_wf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.venv_wf h2 (h3.isType c.venv_wf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    exact ⟨_, he₀ ▸ h1', _, mwf.1.mkForall_eq _ _ harr ▸ h3', h2'⟩

theorem checkLambda.WF
    (h1 : e.FVarsIn s.ngen.Reserves) :
    (inferLambda e false).WF c s (fun ty _ => ∃ e',
      c.TrExprS e e' ∧ ∃ ty', c.TrExprS ty ty' ∧ c.HasType e' ty') :=
  .stateWF fun wf =>
  c.withMLC_self ▸ checkLambda.loop.WF (Nat.zero_le _) rfl rfl rfl h1 wf.ngen_wf

theorem inferLambda.loop.WF {c : VContext}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (hr : ∀ v ∈ m.vlctx.fvars, s.ngen.Reserves v)
    (h1 : (c.withMLC m).TrExprS (e.instantiateList ((m.fvarRevList n hn).map .fvar)) e')
    (h2 : (c.withMLC m).HasType e' ty') :
    (inferLambda.loop true arr e).WF (c.withMLC m) s (fun ty₀ _ =>
      c.TrExpr ty₀ (m.mkForall' n hn ty')) := by
  unfold inferLambda.loop
  simp [Expr.instantiateRev', Expr.instantiate', harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    refine .stateWF fun wf => ?_
    simp [Expr.instantiateList_lam] at h1
    have .lam (ty' := dom') (body' := body') ⟨_, domty'⟩ hdom hbody := h1
    have hdom' := hdom.trExpr c.venv_wf mwf.1.tr.wf
    refine .withLocalDecl hdom ⟨_, domty'⟩ fun a mwf' s' le res h6 => ?_
    have h6' := wf.find?_eq_none h6
    refine .stateWF fun wf' => ?_
    have hbody₂ := hbody.inst_fvar c.venv_wf mwf'.1.tr.wf
    have ⟨ty₂, hty₂⟩ := hbody₂.wf c.venv_wf mwf'.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by trivial)] at hbody₂
    -- have := h2.defeqU_l c.venv_wf mwf.1.tr.wf.toCtx he'.symm
    refine (inferLambda.loop.WF (Nat.succ_le_succ hn)
      (by simp [hdrop]) (by simp [harr]) ?_ ?_ hty₂).le fun a s' le H => ?_
    · simpa using ⟨res, fun _ h => le.reservesV (hr _ h)⟩
    · exact hbody₂
    simp at H
    have ⟨_, h⟩ := (domty'.lam hty₂).uniq c.venv_wf mwf.1.tr.wf.toCtx h2
    have ⟨_, h⟩ := mwf.1.mkForall'_congr h n hn; simp [hdrop] at h
    exact H.defeq c.venv_wf c.mlctx_wf.tr.wf ⟨_, h⟩
  · refine (inferType.WF h1 h2).bind fun ty _ _ hty => ?_
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    let ⟨h1', h2'⟩ := mwf.1.mkLambda_trS c.venv_wf h1 h2 n hn
    have := ty.safeSorry -- FIXME
    have hty := hty.cheapBetaReduce c.venv_wf wf.trctx.wf this m.noBV
    have h3' := (mwf.1.mkForall_tr c.venv_wf hty (h2.isType c.venv_wf mwf.1.tr.wf) n hn).1
    simp [hdrop] at h1' h2' h3'
    exact mwf.1.mkForall_eq _ _ harr ▸ h3'

theorem inferLambda.WF
    (h1 : c.TrExprS e e') (h2 : c.HasType e' ty') :
    (inferLambda e true).WF c s (fun ty _ => c.TrExpr ty ty') :=
  .stateWF fun wf =>
  c.withMLC_self ▸ inferLambda.loop.WF (Nat.zero_le _) rfl rfl wf.ngen_wf h1 h2
