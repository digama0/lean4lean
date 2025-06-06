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

theorem M.WF.map {c : VContext} {s : VState} {x : M α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s.LE s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

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
  inferType : e.FVarsIn s.ngen.Reserves →
    (inferOnly = true → ∃ e', c.TrExprS e e') →
    M.WF c s (m.inferType e inferOnly) fun ty _ => ∃ e' ty',
      c.TrExprS e e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty'

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

theorem RecM.WF.map {c : VContext} {s : VState} {x : RecM α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s.LE s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

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
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkForall n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
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
    c.mkLambda n (Nat.le_of_succ_le_succ h) (.lam name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
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

theorem mkForall_hasType {c : MLCtx}
    (hus : us.Forall₂ (VLevel.ofLevel Us · = some ·) us')
    (hΔ : c.vlctx.SortList env Us.length us')
    (hu : VLevel.ofLevel Us u = some u')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' (.sort u')) (n hn)
    (hus : us.length = n) :
    ∃ u₀', VLevel.ofLevel Us (List.foldl (fun x y => mkLevelIMax' y x) u us) = some u₀' ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') (.sort u₀') := by
  subst hus
  induction hus generalizing c e' u u' with
  | nil => exact ⟨_, hu, H2⟩
  | cons h _ ih =>
    match c, hΔ with
    | .vlam x name ty ty' bi c, .cons hΔ hu₁ =>
      have ⟨_, h5, h6⟩ := ofLevel_mkLevelIMax' h hu
      refine ih hΔ h5 ?_ (Nat.le_of_succ_le_succ hn)
      refine .defeq (.sortDF ?_ (.of_ofLevel h5) h6.symm) (hu₁.forallE H2)
      exact ⟨.of_ofLevel h, .of_ofLevel hu⟩

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
    c.lctx.mkForall arr e = c.mkForall n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkForall, this, ← List.map_reverse, LocalContext.mkBinding_eq,
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
    c.lctx.mkLambda arr e = c.mkLambda n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkLambda, this, ← List.map_reverse, LocalContext.mkBinding_eq,
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

theorem inferType.WF' {c : VContext} {s : VState} (h1 : e.FVarsIn s.ngen.Reserves)
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ e' ty',
      c.TrExprS e e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty' :=
  fun _ wf => wf.inferType h1 hinf

theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e true) fun ty _ => ∃ ty', c.TrExprS ty ty' ∧ c.HasType e' ty' := by
  refine .stateWF fun wf => ?_
  refine (inferType.WF' (he.fvarsIn.mono wf.ngen_wf) fun _ => ⟨_, he⟩).le
    fun _ _ _ ⟨_, _, h1, h2, h3⟩ => ⟨_, h2, ?_⟩
  have := h1.uniq c.venv_wf (.refl c.venv_wf c.mlctx_wf.tr.wf) he
  exact h3.defeqU_l c.venv_wf c.mlctx_wf.tr.wf this

theorem inferType.WF_uniq {c : VContext} {s : VState}
    (he : c.TrExprS e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  (inferType.WF he).le fun _ _ _ ⟨_, h1, h2⟩ =>
  ⟨_, h1, h2.uniqU c.venv_wf c.mlctx_wf.tr.wf hty⟩

theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn s.ngen.Reserves) :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty',
      c.TrExprS e e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty' := inferType.WF' h1 nofun

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

theorem checkLevel.WF {c : VContext} (H : l.hasMVar' = false) :
    (checkLevel c.toContext l).WF fun _ => ∃ u', VLevel.ofLevel c.lparams l = some u' := by
  simp [checkLevel]; split <;> [exact .throw; refine .pure ?_]
  exact Level.getUndefParam_none H (by rename_i h; simpa using h)

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

theorem inferConstant.WF {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      ∃ e' ty', c.TrExprS (.const name ls) e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty' := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq1 => ?_
  have : (ls.foldlM (fun b a => checkLevel c.toContext a) PUnit.unit).WF (fun _ =>
      ∃ ls', ls.Forall₂ (VLevel.ofLevel c.lparams · = some ·) ls') := by
    clear hinf
    induction ls with
    | nil => exact .pure ⟨_, .nil⟩
    | cons l ls ih =>
      simp at H
      refine (checkLevel.WF H.1).bind fun ⟨⟩ ⟨_, h1⟩ => ?_
      exact (ih H.2).le fun _ ⟨_, h2⟩ => ⟨_, .cons h1 h2⟩
  split <;> [rename_i h1; exact .throw]
  have main {e'} (he : c.TrExprS (.const name ls) e') : ∃ e', c.TrExprS (.const name ls) e' ∧
      ∃ x, c.TrExprS (ci.instantiateTypeLevelParams ls) x ∧ c.HasType e' x := by
    refine ⟨_, he, ?_⟩; let .const h4 H' eq := he
    have ⟨_, h5, h6⟩ := c.trenv.find?_uniq eq1 h4
    have H := List.mapM_eq_some.1 H'
    have s1 := h6.instL c.venv_wf (Δ := []) trivial H' (h5.trans eq.symm)
    have s1 := s1.weakFV c.venv_wf (.from_nil c.mlctx.noBV) c.mlctx_wf.tr.wf
    rw [(c.venv_wf.ordered.closedC h4).instL.liftN_eq (Nat.le_refl _)] at s1
    have ⟨_, s1, s2⟩ := s1
    refine ⟨_, s1, .defeqU_r c.venv_wf c.mlctx_wf.tr.wf s2.symm ?_⟩
    exact .const h4 (.of_mapM_ofLevel H') (H.length_eq.symm.trans eq)
  split
  · split <;> [exact .throw; rename_i h2]
    generalize eq1 : _ <$> (_ : Except Exception _) = F
    generalize eq2 : (fun ty : Expr => _) = P
    suffices ci.isPartial = false ∨ (c.safety == .safe) = false → F.WF P by
      split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
      split <;> [exact .throw; skip]
      rename_i h; simp [ConstantInfo.isPartial, Decidable.imp_iff_not_or] at h
      exact this h
    subst eq1 eq2; intro h3
    refine this.map fun _ ⟨_, H⟩ => ?_
    have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq1 <| by
      revert h2 h3
      cases c.safety <;> simp [isAsSafeAs] <;> cases ci.isUnsafe <;> simp +decide
    have eq := h1.symm.trans h5
    exact main (.const h4 (List.mapM_eq_some.2 H) eq)
  · simp_all; let ⟨_, h⟩ := hinf; refine .pure (main h)

theorem inferLambda.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr1 : e.FVarsIn s.ngen.Reserves)
    (hr2 : ∀ v ∈ m.vlctx.fvars, s.ngen.Reserves v)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLambda.loop inferOnly arr e).WF (c.withMLC m) s (fun ty _ =>
      ∃ e', c.TrExprS e₀ e' ∧ ∃ ty', c.TrExprS ty ty' ∧ c.HasType e' ty') := by
  unfold inferLambda.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    generalize eqF : withLocalDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_lam] at hei; subst ei
    have main {s₁} (le₁ : s.LE s₁) {dom'}
        (domty : (c.withMLC m).venv.IsType (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx dom')
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, VLocalDecl.vlam dom') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.venv_wf mwf.1.tr.wf
      subst eqF eqP
      refine .withLocalDecl hdom domty fun a mwf' s' le₂ res h6 => ?_
      have h6' := wf.find?_eq_none h6
      refine .stateWF fun wf' => ?_
      have := le₁.trans le₂
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLambda.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
        (by simp [← eqfvs, harr]) ?_ (by simp [← eqfvs]; rfl) (this.reserves hr1).2 ?_ ?_
      · rw [he₀, eqfvs, ← eq]; simp; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr1.2.instantiateList ?_).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
        · rintro _ h rfl; exact h6 <| le₁.reservesV h
      · simp [or_imp, forall_and, FVarsIn]
        exact ⟨res, fun _ h => this.reservesV (hr2 _ h)⟩
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.venv_wf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le₁ ⟨dom', uv', h1, h2, h3⟩ => ?_
      · apply hr1.1.instantiateList; simp [← eqfvs]
        exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
      refine (ensureSortCore.WF (h2.trExpr c.venv_wf mwf.1.tr.wf)).bind fun _ _ le₂ ⟨h4, h5⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5
      refine .stateWF fun wf => ?_
      have domty := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx h5.symm
      have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
      exact main (le₁.trans le₂) domty' h1 nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .lam (ty' := dom') (body' := body') domty hdom hbody := h1
      exact main .rfl domty hdom _ hbody
  · subst ei
    refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', h1, h2, h3⟩ => ?_
    · apply hr1.instantiateList; simp [← eqfvs]
      exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, h2, e2⟩ := h2.trExpr c.venv_wf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.venv_wf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLambda_trS c.venv_wf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.venv_wf h2 (h3.isType c.venv_wf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    exact ⟨_, he₀ ▸ h1', _, mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) ▸ h3', h2'⟩

theorem inferLambda.WF
    (h1 : e.FVarsIn s.ngen.Reserves)
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLambda e inferOnly).WF c s (fun ty _ => ∃ e',
      c.TrExprS e e' ∧ ∃ ty', c.TrExprS ty ty' ∧ c.HasType e' ty') :=
  .stateWF fun wf =>
  (c.withMLC_self ▸ inferLambda.loop.WF (Nat.zero_le _) rfl rfl rfl rfl h1 wf.ngen_wf) hinf

theorem checkForall.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkForall n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr1 : e.FVarsIn s.ngen.Reserves)
    (hr2 : ∀ v ∈ m.vlctx.fvars, s.ngen.Reserves v)
    (hus : us.toList.reverse.Forall₂ (VLevel.ofLevel c.lparams · = some ·) us')
    (hΔ : m.vlctx.SortList c.venv c.lparams.length us')
    (hlen : us'.length = n)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferForall.loop inferOnly arr us e).WF (c.withMLC m) s (fun ty _ =>
      ∃ e', c.TrExprS e₀ e' ∧ ∃ u, c.TrExprS ty (.sort u) ∧ c.HasType e' (.sort u)) := by
  unfold inferForall.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [harr, -bind_pure_comp]; split
  · rename_i name dom body bi
    rw [Expr.instantiateList_forallE] at hei; subst ei
    refine (inferType.WF' ?_ ?_).bind fun uv _ le₁ ⟨dom', uv', h1, h2, h3⟩ => ?_
    · apply hr1.1.instantiateList; simp [← eqfvs]
      exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
    · intro h; let ⟨_, .forallE _ _ h _⟩ := hinf h; exact ⟨_, h⟩
    refine (ensureSortCore.WF (h2.trExpr c.venv_wf mwf.1.tr.wf)).bind fun _ _ le₂ ⟨h4, h5⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort h4, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' fun a mwf' s' le₃ res h6 => ?_
    have h6' := wf.find?_eq_none h6
    refine .stateWF fun wf' => ?_
    have := le₁.trans le₂ |>.trans le₃
    have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
    refine checkForall.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
      (by simp [eqfvs, harr]) ?_ (by simp [eqfvs]; rfl) (this.reserves hr1).2 ?_
      (by simpa using ⟨h4, hus⟩) (.cons hΔ domty) (by simp [hlen]) ?_
    · simp [he₀, ← eq]; congr 2
      refine (FVarsIn.abstract_instantiate1 ((hr1.2.instantiateList ?_).mono ?_)).symm
      · simp [← eqfvs, FVarsIn]; exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
      · rintro _ h rfl; exact h6 <| (le₁.trans le₂).reservesV h
    · simp [or_imp, forall_and, FVarsIn]
      exact ⟨res, fun _ h => this.reservesV (hr2 _ h)⟩
    · intro h; let ⟨_, .forallE (body' := body') _ _ hdom₁ hbody₁⟩ := hinf h
      refine have hΔ := .refl c.venv_wf mwf.1.tr.wf; have H := hdom₁.uniq c.venv_wf hΔ h1; ?_
      have H := H.of_r c.venv_wf mwf.1.tr.wf.toCtx domty
      have ⟨_, hbody₂⟩ := hbody₁.defeqDFC c.venv_wf <| .cons hΔ (ofv := none) nofun (.vlam H)
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.venv_wf.ordered mwf'.1.tr.wf⟩
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', h1, h2, h3⟩ => ?_
    · apply hr1.instantiateList; simp [← eqfvs]
      exact fun _ h => hr2 _ (m.fvarRevList_prefix.subset h)
    refine (ensureSortCore.WF (h2.trExpr c.venv_wf mwf.1.tr.wf)).bind fun _ _ le₂ ⟨h4, h5⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort (u' := u') h4, h5⟩ := h5
    refine .stateWF fun wf => .pure ?_
    obtain ⟨us, rfl⟩ : ∃ l, ⟨List.reverse l⟩ = us := ⟨us.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at hus ⊢
    have h3 := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx h5.symm
    let ⟨h1', h2'⟩ := mwf.1.mkForall_trS c.venv_wf h1 ⟨_, h3⟩ n hn
    have ⟨_, h3', h4'⟩ := mkForall_hasType hus hΔ h4 h3 n hn (hus.length_eq.trans hlen)
    simp [hdrop] at h1' h2' h4'
    exact ⟨_, he₀ ▸ h1', _, .sort h3', h4'⟩

theorem checkForall.WF
    (h1 : e.FVarsIn s.ngen.Reserves)
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferForall e inferOnly).WF c s (fun ty _ =>
      ∃ e', c.TrExprS e e' ∧ ∃ u, c.TrExprS ty (.sort u) ∧ c.HasType e' (.sort u)) :=
  .stateWF fun wf =>
  (c.withMLC_self ▸ checkForall.loop.WF (Nat.zero_le _)
    rfl rfl rfl rfl h1 wf.ngen_wf .nil .nil rfl) hinf

theorem addEquiv.WF {c : VContext} {s : VState} :
    RecM.WF c s (modify fun st => { st with eqvManager := st.eqvManager.addEquiv e₁ e₂ })
      fun _ _ => True := by
  rintro _ mwf wf _ _ ⟨⟩
  exact ⟨{ s with toState := _ }, rfl, NameGenerator.LE.rfl, { wf with }, trivial⟩

theorem isDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExpr e₁ e₁') (he₂ : c.TrExpr e₂ e₂') :
    RecM.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  refine (isDefEqCore.WF he₁ he₂).bind fun b _ _ hb => ?_
  simp; split
  · exact addEquiv.WF.map fun _ _ _ _ => hb
  · exact .pure hb

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

theorem AppStack.build {e : Expr} :
    ∀ {as}, TrExprS env Us Δ (e.mkAppList as) e' → ∃ e', AppStack env Us Δ e e' as := by
  intro as H
  rw [← Expr.mkAppRevList_reverse] at H
  simpa using AppStack.build_rev H (.head H)

theorem AppStack.tr : AppStack env Us Δ e e' as → TrExprS env Us Δ e e'
  | .head H | .app _ _ H _ _ => H

theorem inferApp.loop.WF {c : VContext} {s : VState}
    {ll lm lr : List _}
    (stk : AppStack c.venv c.lparams c.vlctx (.mkAppRevList e lm) e' lr)
    (hfty : c.TrExpr (fType.instantiateList lm) fty') (hety : c.HasType e' fty')
    (hargs : args = ll ++ lm.reverse ++ lr)
    (hj : j = ll.length) (hi : i = ll.length + lm.length) :
    RecM.WF c s
      (inferApp.loop e₀ ⟨args⟩ fType j i)
      fun ty _ => ∃ e₁', c.TrExprS (e.mkAppRevList lm |>.mkAppList lr) e₁' ∧
        ∃ ty', c.TrExprS ty ty' ∧ c.HasType e₁' ty' := by
  subst i j; rw [inferApp.loop.eq_def]
  simp [hargs, Expr.instantiateList_reverse]
  have henv := c.venv_wf; have hΔ := c.mlctx_wf.tr.wf
  cases lr with simp
  | cons a lr =>
    let .app hf' ha' hf ha stk := stk
    have uf := hf'.uniqU henv hΔ hety
    split
    · rw [Expr.instantiateList_forallE] at hfty
      let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (lm := a::lm) stk ?_ (.app hf' ha') (by simp) rfl rfl
      have ha0 := c.mlctx.noBV ▸ ha.closed
      simp [← Expr.instantiateList_instantiate1_comm ha0.looseBVarRange_zero]
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
    · simp [Nat.add_sub_cancel_left, Expr.instantiateRevList_reverse]
      refine (ensureForallCore.WF hfty).bind fun _ _ _ ⟨h1, _, h2, h3⟩ => ?_
      obtain ⟨name, ty, body, bi, rfl⟩ := h1; simp [Expr.bindingBody!]
      let .forallE _ _ hty hbody := h2
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (ll := ll ++ lm.reverse) (lm := [a]) stk ?_
        (.app hf' ha') (by simp) (by simp) (by simp)
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
  | nil =>
    rw [← List.length_reverse, List.take_length, Expr.instantiateRevList_reverse]
    have ⟨_, hfty, h2⟩ := hfty
    exact .pure ⟨_, stk.tr, _, hfty, hety.defeqU_r henv hΔ h2.symm⟩

theorem inferApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferApp e) fun ty _ => ∃ ty', c.TrExprS ty ty' ∧ c.HasType e' ty' := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, he'⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
  refine (inferType.WF he'.tr).bind fun ty _ _ ⟨ty', hty', ety⟩ => ?_
  have henv := c.venv_wf; have hΔ := c.mlctx_wf.tr.wf
  refine (inferApp.loop.WF (ll := []) (lm := []) he'
    (hty'.trExpr henv hΔ) ety rfl rfl rfl).le fun _ _ _ ⟨_, h1, _, h2, h3⟩ => ?_
  have := (e.mkAppList_getAppArgsList ▸ h1).uniq henv (.refl henv hΔ) he
  exact ⟨_, h2, h3.defeqU_l henv hΔ this⟩
