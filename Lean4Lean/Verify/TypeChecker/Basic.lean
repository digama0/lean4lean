import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.ConditionallyTyped
import Lean4Lean.TypeChecker

namespace Except

def WF (x : Except ε α) (Q : α → Prop) : Prop := ∀ a, x = .ok a → Q a

theorem WF.bind {x : Except ε α} {f : α → Except ε β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → (f a).WF R) : (x >>= f).WF R := by
  intro b
  simp [(· >>= ·), Except.bind]
  split; · simp
  exact h2 _ (h1 _ rfl) _

theorem WF.pure {Q} (H : Q a) :
    (pure a : Except ε α).WF Q := by rintro _ ⟨⟩; exact H

theorem WF.map {x : Except ε α} {f : α → β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R (f a)) : (f <$> x).WF R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ h => .pure (h2 _ h)

theorem WF.mono {x : Except ε α} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R a) : x.WF R := by
  simpa using h1.bind fun _ h => .pure (h2 _ h)

theorem WF.throw {Q} : (throw e : Except ε α).WF Q := nofun

theorem WF.le {Q R} {x : Except ε α}
    (h1 : x.WF Q) (H : ∀ a, Q a → R a) :
    x.WF R := fun _ e => H _ (h1 _ e)

theorem WF.pureBind  {f : β → Except ε α} {Q}
    {x : β} (H : WF (f x) Q) : ((Pure.pure x : Except ε β) >>= f).WF Q := H

end Except

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped List

namespace EquivManager

variable {env : VEnv} {Us : List Name} {Δ : VLCtx}
variable (env Us Δ) in
inductive IsDefEqE : Expr → Expr → Prop
  | rfl : IsDefEqE e e
  | trans : IsDefEqE e₁ e₂ → IsDefEqE e₂ e₃ → IsDefEqE e₁ e₃
  | defeq : TrExprS env Us Δ e₁ e' → TrExpr env Us Δ e₂ e' → IsDefEqE e₁ e₂
  | app : IsDefEqE f₁ f₂ → IsDefEqE a₁ a₂ → IsDefEqE (.app f₁ a₁) (.app f₂ a₂)
  | lam : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.lam _ d₁ b₁ _) (.lam _ d₂ b₂ _)
  | forallE : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.forallE _ d₁ b₁ _) (.forallE _ d₂ b₂ _)
  | letE : IsDefEqE t₁ t₂ → IsDefEqE v₁ v₂ → IsDefEqE b₁ b₂ →
    IsDefEqE (.letE _ t₁ v₁ b₁ _) (.letE _ t₂ v₂ b₂ _)
  | mdata : IsDefEqE e₁ e₂ → IsDefEqE (.mdata _ e₁) (.mdata _ e₂)
  | proj : IsDefEqE e₁ e₂ → IsDefEqE (.proj _ i e₁) (.proj _ i e₂)

theorem IsDefEqE.symm (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ e₂ e₁ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1
  | defeq h1 h2 => let ⟨_, h2, h3⟩ := h2; exact .defeq h2 ⟨_, h1, h3.symm⟩
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem IsDefEqE.weak' (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ' e₁ e₂ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | defeq h1 h2 => exact .defeq (h1.weakFV' henv W hΔ) (h2.weakFV' henv W hΔ)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable (env Us Δ) in
structure WF (m : EquivManager) where
  wf {i} : i < m.uf.size ↔ ∃ e : Expr, m.toNodeMap[e]? = some i
  defeq {e₁ e₂ : Expr} {i₁ i₂} :
    m.toNodeMap[e₁]? = some i₁ → m.toNodeMap[e₂]? = some i₂ → m.uf.Equiv i₁ i₂ →
    IsDefEqE env Us Δ e₁ e₂

theorem WF.empty : WF env Us Δ {} where
  wf := by simp
  defeq := by simp

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem WF.weak' (wf : WF env Us Δ m) : WF env Us Δ' m where
  wf := wf.wf
  defeq h1 h2 h3 := wf.defeq h1 h2 h3 |>.weak' henv W hΔ

end EquivManager

namespace TypeChecker

inductive MLCtx where
  | nil : MLCtx
  | vlam (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) : MLCtx → MLCtx
  | vlet (id : FVarId) (name : Name) (ty v : Expr) (ty' v' : VExpr) : MLCtx → MLCtx

@[simp] def MLCtx.vlctx : MLCtx → VLCtx
  | .nil => []
  | .vlam id _ ty ty' _ c => (some (id, ty.fvarsList), .vlam ty') :: c.vlctx
  | .vlet id _ ty v ty' v' c => (some (id, ty.fvarsList ++ v.fvarsList), .vlet ty' v') :: c.vlctx

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

@[simp] theorem MLCtx.fvarRevList_length {c n hn} : (MLCtx.fvarRevList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.letValList (c : MLCtx) (n) (hn : n ≤ c.length) : List (Option (Expr × Expr)) :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam _ _ _ _ _ c, h => none :: c.letValList n (Nat.le_of_succ_le_succ h)
  | n+1, .vlet _ _ ty v _ _ c, h => some (ty, v) :: c.letValList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.letValList_length {c n hn} : (MLCtx.letValList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

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

theorem MLCtx.dropN_fvars_subset {c : MLCtx} (n hn) : (c.dropN n hn).vlctx.fvars ⊆ c.vlctx.fvars :=
  match n, c, hn with
  | 0, _, _ => fun _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h =>
    List.subset_cons_of_subset _ <| dropN_fvars_subset n (Nat.le_of_succ_le_succ h)

theorem MLCtx.noBV (c : MLCtx) : c.vlctx.NoBV := by
  induction c <;> trivial

structure VContext extends Context where
  venv : VEnv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  trenv : TrEnv safety env venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx

@[simp] abbrev VContext.lctx' (c : VContext) := c.mlctx.lctx
@[simp] abbrev VContext.vlctx (c : VContext) := c.mlctx.vlctx

theorem VContext.trlctx (c : VContext) : TrLCtx c.venv c.lparams c.lctx' c.vlctx := c.mlctx_wf.tr
theorem VContext.Ewf (c : VContext) : VEnv.WF c.venv := c.trenv.wf
theorem VContext.Δwf (c : VContext) : c.vlctx.WF c.venv c.lparams.length := c.trlctx.wf

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
nonrec abbrev VContext.FVarsBelow (c : VContext) : Expr → Expr → Prop :=
  FVarsBelow c.vlctx
nonrec abbrev VContext.TrTyping (c : VContext) : Expr → Expr → VExpr → VExpr → Prop :=
  TrTyping c.venv c.lparams c.vlctx

class VContext.MLCWF (c : VContext) (m : MLCtx) : Prop where
  wf : m.WF c.venv c.lparams

instance (c : VContext) : c.MLCWF c.mlctx := ⟨c.mlctx_wf⟩

structure VState extends State where

def _root_.Lean4Lean.InferCache.WF (c : VContext) (s : VState) (m : InferCache) : Prop :=
  ∀ ⦃e ty : Expr⦄, m[e]? = some ty → ConditionallyHasType s.ngen c.venv c.lparams c.vlctx e ty

theorem _root_.Lean4Lean.InferCache.WF.empty : InferCache.WF c s {} := fun _ => by simp

def WHNFCache.WF (c : VContext) (s : VState) (m : InferCache) : Prop :=
  ∀ ⦃e ty : Expr⦄, m[e]? = some ty → ConditionallyWHNF s.ngen c.venv c.lparams c.vlctx e ty

theorem WHNFCache.WF.empty : WHNFCache.WF c s {} := fun _ => by simp

class VState.WF (c : VContext) (s : VState) where
  trctx : c.TrLCtx
  ngen_wf : ∀ fv ∈ c.vlctx.fvars, s.ngen.Reserves fv
  ectx : ∃ Δ' n, Δ'.WF c.venv c.lparams.length ∧ c.vlctx.FVLift' Δ' 0 n 0 ∧
    s.eqvManager.WF c.venv c.lparams Δ' ∧ ∀ fv ∈ Δ'.fvars, s.ngen.Reserves fv
  inferTypeI_wf : s.inferTypeI.WF c s
  inferTypeC_wf : s.inferTypeC.WF c s
  whnfCore_wf : WHNFCache.WF c s s.whnfCoreCache
  whnf_wf : WHNFCache.WF c s s.whnfCache

theorem VState.WF.find?_eq_none {id}
    (wf : VState.WF c s) (H : ¬s.ngen.Reserves id) : c.lctx'.find? id = none :=
  wf.trctx.find?_eq_none.2 fun h => H (wf.ngen_wf _ h)

def VState.LE (s₁ s₂ : VState) : Prop :=
  s₁.ngen ≤ s₂.ngen

instance : LE VState := ⟨VState.LE⟩

theorem VState.LE.rfl {s : VState} : s ≤ s := NameGenerator.LE.rfl

theorem VState.LE.trans {s₁ s₂ s₃ : VState} (h₁ : s₁ ≤ s₂) (h₂ : s₂ ≤ s₃) : s₁ ≤ s₃ :=
  NameGenerator.LE.trans h₁ h₂

theorem VState.LE.reservesV {s₁ s₂ : VState} (h : s₁ ≤ s₂) {{fv}} :
    s₁.ngen.Reserves fv → s₂.ngen.Reserves fv :=
  (·.mono h)

theorem VState.LE.reserves {s₁ s₂ : VState} (h : s₁ ≤ s₂) {{e}} :
    FVarsIn s₁.ngen.Reserves e → FVarsIn s₂.ngen.Reserves e :=
  (·.mono h.reservesV)

def M.WF (c : VContext) (vs : VState) (x : M α) (Q : α → VState → Prop) : Prop :=
  vs.WF c → ∀ a s', x c.toContext vs.toState = .ok (a, s') →
    ∃ vs', vs'.toState = s' ∧ vs ≤ vs' ∧ vs'.WF c ∧ Q a vs'

theorem M.WF.bind {c : VContext} {s : VState} {x : M α} {f : α → M β} {Q R}
    (h1 : x.WF c s Q)
    (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) :
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
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem M.WF.mono {c : VContext} {s : VState} {x : M α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  simpa using h1.bind fun _ _ a1 a2 => .pure (h2 _ _ a1 a2)

theorem M.WF.throw {c : VContext} {s : VState} {Q} : (throw e : M α).WF c s Q := nofun

theorem M.WF.le {c : VContext} {s : VState} {Q R} {x : M α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun wf _ _ e =>
  let ⟨_, a1, a2, a3, a4⟩ := h1 wf _ _ e
  ⟨_, a1, a2, a3, H _ _ a2 a4⟩

structure Methods.WF (m : Methods) where
  isDefEqCore : c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
    (m.isDefEqCore e₁ e₂).WF c s fun b _ => b → c.IsDefEqU e₁' e₂'
  whnfCore : c.TrExprS e e' →
    (m.whnfCore e cheapRec cheapProj).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  whnf : c.TrExprS e e' →
    (m.whnf e).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  inferType : e.FVarsIn (· ∈ c.vlctx.fvars) →
    (inferOnly = true → ∃ e', c.TrExprS e e') →
    (m.inferType e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'

def RecM.WF (c : VContext) (s : VState) (x : RecM α) (Q : α → VState → Prop) : Prop :=
  ∀ m, m.WF → M.WF c s (x m) Q

theorem M.WF.liftExcept {c : VContext} {s : VState} {x : Except Exception α} {Q} (h : x.WF Q) :
    M.WF c s (liftM x) fun a _ => Q a := by
  rintro wf _ _ eq
  cases x <;> cases eq
  exact ⟨s, rfl, .rfl, wf, h _ rfl⟩

theorem M.WF.lift {c : VContext} {s : VState} {x : M α} {Q} (h : x.WF c s Q) :
    RecM.WF c s x Q := fun _ _ => h

instance : Coe (M.WF c s x Q) (RecM.WF c s x Q) := ⟨M.WF.lift⟩

theorem RecM.WF.bind {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  fun _ h => M.WF.bind (h1 _ h) fun _ _ h1' h2' => h2 _ _ h1' h2' _ h

theorem RecM.WF.bind_le {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (hs : s₀ ≤ s)
    (h2 : ∀ a s', s₀ ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  RecM.WF.bind h1 fun _ _ h => h2 _ _ (hs.trans h)

theorem RecM.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) : (pure a : RecM α).WF c s Q :=
  fun _ _ => .pure H

theorem RecM.WF.map {c : VContext} {s : VState} {x : RecM α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem RecM.WF.mono {c : VContext} {s : VState} {x : RecM α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  rw [← id_map x]; exact h1.map h2

theorem RecM.WF.throw {c : VContext} {s : VState} {Q} : (throw e : RecM α).WF c s Q := nofun

theorem RecM.WF.le {c : VContext} {s : VState} {Q R} {x : RecM α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun _ h => (h1 _ h).le H

theorem RecM.WF.pureBind {c : VContext} {s : VState} {f : β → RecM α} {Q}
    {x : β} (H : WF c s (f x) Q) : ((Pure.pure x : RecM β) >>= f).WF c s Q := H

theorem get.WF {c : VContext} {s : VState} :
    M.WF c s get fun a s' => s.toState = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.get {c : VContext} {s : VState} {f : State → RecM α} {Q}
    (H : WF c s (f s.toState) Q) : (get >>= f).WF c s Q := H

theorem getEnv.WF {c : VContext} {s : VState} :
    M.WF c s getEnv fun a s' => c.env = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.getEnv {c : VContext} {s : VState} {f : Environment → RecM α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q := H

theorem getLCtx.WF {c : VContext} {s : VState} :
    M.WF c s getLCtx fun a s' => c.lctx' = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, c.lctx_eq, rfl⟩

theorem RecM.WF.getLCtx {c : VContext} {s : VState} {f : LocalContext → RecM α} {Q}
    (H : WF c s (f c.lctx') Q) : (getLCtx >>= f).WF c s Q :=
  getLCtx.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.readThe {c : VContext} {s : VState} {f : Context → RecM α} {Q}
    (H : WF c s (f c.toContext) Q) : (readThe Context >>= f).WF c s Q := H

theorem getNGen.WF {c : VContext} {s : VState} :
    M.WF c s getNGen fun a s' => s.ngen = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → M α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → RecM α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.stateWF {c : VContext} {s : VState} {x : RecM α} {Q}
    (H : s.WF c → WF c s x Q) : WF c s x Q :=
  fun _ h wf => H wf _ h wf

@[simp] theorem toLBool_true {b : Bool} : b.toLBool = .true ↔ b = true := by
  cases b <;> simp [Bool.toLBool]

theorem RecM.WF.toLBoolM {Q : VState → Prop} {x : RecM Bool}
    (H : x.WF c s fun b s => b → Q s) : (toLBoolM x).WF c s fun b s => b = .true → Q s :=
  H.bind fun _ _ _ H => .pure fun h => H (by simpa using h)

def VContext.withMLC (c : VContext) (m : MLCtx) [wf : c.MLCWF m] : VContext :=
  { c with
    mlctx := m
    mlctx_wf := wf.1
    lctx := m.lctx
    lctx_eq := rfl }

@[simp] theorem VContext.withMLC_self (c : VContext) : c.withMLC c.mlctx = c := by
  simp [withMLC, c.lctx_eq]

def VState.next (s : VState) : VState := { s with ngen := s.ngen.next }

protected theorem RecM.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → RecM α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro _ mwf wf a s' e
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlam ⟨id⟩ name ty ty' bi
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hty'⟩
  have : VState.WF (c.withMLC m') s.next :=
    have trctx := wf.trctx.mkLocalDecl h1' hty hty'
    have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) : InferCache.WF (c.withMLC m') s.next ic :=
      fun _ _ h => ((H h).fresh c.Ewf.ordered trctx.wf).mono le
    have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) : WHNFCache.WF (c.withMLC m') s.next wc :=
      fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
    { ngen_wf := by
        simp [m', VContext.withMLC]; exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
      ectx := by
        let ⟨_, _, a1, a2, a3, a4⟩ := wf.ectx
        refine
          have b1 := ⟨a1, ?_, hty'.weak' c.Ewf.ordered a2.toCtx⟩
          ⟨_, _, b1, a2.cons_fvar _ _ hty.fvarsList, a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
            fun _ h => by obtain _ | ⟨_, h⟩ := h <;> [exact h0; exact (a4 _ h).mono le]⟩
        rintro _ _ ⟨⟩; exact ⟨mt (a4 _) h1, hty.fvarsList.trans a2.fvars_sublist.subset⟩
      trctx, inferTypeI_wf := hic wf.inferTypeI_wf, inferTypeC_wf := hic wf.inferTypeC_wf
      whnfCore_wf := hwc wf.whnfCore_wf, whnf_wf := hwc wf.whnf_wf }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 _ mwf this a s' e
  refine have le' := le.trans hs2; ⟨s', hs1, le', ?_, hs4⟩
  have hic {ic} (H : InferCache.WF (c.withMLC m') s' ic) :
      InferCache.WF (c.withMLC m) s' ic := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m') s' wc) :
      WHNFCache.WF (c.withMLC m) s' wc := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  let ⟨_, _, a1, a2, a3⟩ := wf'.ectx
  exact {
    ngen_wf := (by simpa [VContext.withMLC] using wf'.ngen_wf :).2
    ectx := ⟨_, _, a1, .comp (.skip_fvar _ _ .refl) a2, a3⟩
    trctx := wf.trctx
    inferTypeI_wf := hic wf'.inferTypeI_wf, inferTypeC_wf := hic wf'.inferTypeC_wf
    whnfCore_wf := hwc wf'.whnfCore_wf, whnf_wf := hwc wf'.whnf_wf
  }

protected theorem RecM.WF.withLetDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → RecM α} {Q name ty ty'}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hval : (c.withMLC m).TrExprS val val')
    (hval' : (c.withMLC m).HasType val' ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlet id name ty val ty' val' m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLetDecl name ty val f).WF (c.withMLC m) s Q := by
  intro _ mwf wf a s' e
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlet ⟨id⟩ name ty val ty' val'
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hval, hval'⟩
  have : VState.WF (c.withMLC m') s.next :=
    have trctx := wf.trctx.mkLetDecl h1' hty hval hval'
    have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) :
        InferCache.WF (c.withMLC m') s.next ic :=
      fun _ _ h => ((H h).fresh c.Ewf.ordered trctx.wf).mono le
    have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) : WHNFCache.WF (c.withMLC m') s.next wc :=
      fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
    { ngen_wf := by
        simp [m', VContext.withMLC]; exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
      ectx := by
        let ⟨_, _, a1, a2, a3, a4⟩ := wf.ectx
        have hv := List.append_subset.2 ⟨hty.fvarsList, hval.fvarsList⟩
        refine
          have b1 := ⟨a1, ?_, hval'.weak' c.Ewf.ordered a2.toCtx⟩
          ⟨_, _, b1, a2.cons_fvar _ _ hv, a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
            fun _ h => by obtain _ | ⟨_, h⟩ := h <;> [exact h0; exact (a4 _ h).mono le]⟩
        rintro _ _ ⟨⟩; exact ⟨mt (a4 _) h1, hv.trans a2.fvars_sublist.subset⟩
      trctx, inferTypeI_wf := hic wf.inferTypeI_wf, inferTypeC_wf := hic wf.inferTypeC_wf
      whnfCore_wf := hwc wf.whnfCore_wf, whnf_wf := hwc wf.whnf_wf }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 _ mwf this a s' e
  refine ⟨s', hs1, le.trans hs2, ?_, hs4⟩
  have hic {ic} (H : InferCache.WF (c.withMLC m') s' ic) :
      InferCache.WF (c.withMLC m) s' ic := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m') s' wc) :
      WHNFCache.WF (c.withMLC m) s' wc := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  let ⟨_, _, a1, a2, a3⟩ := wf'.ectx
  exact {
    ngen_wf := (by simpa [VContext.withMLC] using wf'.ngen_wf :).2
    ectx := ⟨_, _, a1, .comp (.skip_fvar _ _ .refl) a2, a3⟩
    trctx := wf.trctx
    inferTypeI_wf := hic wf'.inferTypeI_wf, inferTypeC_wf := hic wf'.inferTypeC_wf
    whnfCore_wf := hwc wf'.whnfCore_wf, whnf_wf := hwc wf'.whnf_wf
  }

@[simp] def MLCtx.mkForall (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn with
  | 0, _, _ => e
  | n+1, .vlam x name ty _ bi c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

def AllAbove (Δ : VLCtx) (P : FVarId → Prop) (fv : FVarId) : Prop := fv ∈ Δ.fvars → P fv

theorem AllAbove.wf (H : Δ.FVWF) : IsFVarUpSet (AllAbove Δ P) Δ ↔ IsFVarUpSet P Δ :=
  IsFVarUpSet.congr H fun _ h => by simp [h, AllAbove]

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

@[simp] def MLCtx.mkLet (c : MLCtx) (n) (hn : n ≤ c.length)
    (nds : List (Option Bool)) (eq : nds.length = n) (e : Expr) (asForall := false) : Expr :=
  match n, c, hn, nds, eq, e with
  | 0, _, _, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, _ :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <|
      if asForall then .forallE name ty (.abstract1 x e) bi else .lam name ty (.abstract1 x e) bi
  | n+1, .vlet x name ty val _ _ c, h, nd :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' (nd.getD false)
      else if let some nd := nd then
        .letE name ty val e' nd
      else
        e'.lowerLooseBVars' 1 1
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

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLet_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn nds hnds) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLet n hn nds hnds e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' nds with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ (.lam h4 H2) ..
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ H2 ..; dsimp; split <;> [skip; split]
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h _ _ _; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

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

inductive MLCtx.PartialForall : MLCtx → Nat → List FVarId → Expr → Prop where
  | nil : PartialForall c 0 [] e
  | vlam : PartialForall c n fvs (.forallE x ty (.abstract1 fv e) bi) →
    PartialForall (c.vlam fv x ty ty' bi) (n+1) (fv :: fvs) e
  | vlet : PartialForall c n fvs (
      let e' := Expr.abstract1 fv e
      if e'.hasLooseBVar' 0 then .letE x ty v e' false
      else e'.lowerLooseBVars' 1 1) →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) (fv :: fvs) e
  | skip : e.looseBVarRange' = 0 → e' = Expr.abstract1 fv e → e'.hasLooseBVar' 0 = false →
    PartialForall c n fvs e →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) fvs e

theorem MLCtx.PartialForall.full : MLCtx.PartialForall c n (c.fvarRevList n hn) e := by
  induction n generalizing c e with
  | zero => exact .nil
  | succ n ih => match c with | .vlam .. | .vlet .. => constructor; apply ih

theorem MLCtx.PartialForall.sublist (H : MLCtx.PartialForall c n l e) : l <+ c.vlctx.fvars := by
  induction H with
  | nil => simp
  | vlam _ ih | vlet _ ih => simp [ih]
  | skip _ _ _ _ ih => exact ih.trans (List.sublist_cons_self ..)

theorem MLCtx.WF.mkForall_partial {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = l.map .fvar) (hp : MLCtx.PartialForall c n l e) :
    c.lctx.mkForall arr e = c.mkForall n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkForall, this, ← List.map_reverse, LocalContext.mkBinding_eq,
    LocalContext.mkBindingList_eq_fold, List.foldr_reverse]
  · clear harr this
    induction hp with
    | nil => simp
    | vlam hp ih | vlet hp ih =>
      simp
      refine (List.foldl_congr fun _ y h => ?_).trans <|
        .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
      · refine LocalContext.mkBindingList1_congr ?_
        rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
        simp [LocalDecl.fvarId]; rintro ⟨⟩
        have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
      · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
    | skip h1 h2 h3 hp ih =>
      subst h2; simp [h3]
      rw [Expr.lowerLooseBVars_eq_instantiate h3 (v := default),
        Expr.abstract1_eq_liftLooseBVars h3, Expr.liftLooseBVars_eq_self (by simp [h1]),
        Expr.instantiate1_eq_self h1]
      refine (List.foldl_congr fun _ y h => ?_).trans (ih wf.1 _)
      refine LocalContext.mkBindingList1_congr ?_
      rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
      simp [LocalDecl.fvarId]; rintro ⟨⟩
      have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
  · intro _ h
    exact wf.tr.find?_eq_some.2 (hp.sublist.subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (hp.sublist.nodup wf.fvars_nodup)

theorem MLCtx.WF.mkForall_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) :
    c.lctx.mkForall arr e = c.mkForall n hn e := mkForall_partial wf n hn harr .full

theorem MLCtx.WF.mkLambda_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) :
    c.lctx.mkLambda arr e = c.mkLambda n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkLambda, this, ← List.map_reverse, LocalContext.mkBinding_eq,
    LocalContext.mkBindingList_eq_fold, List.foldr_reverse]
  · clear harr this
    induction n generalizing c e with
    | zero => simp
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

theorem whnf.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnf he

theorem isDefEqCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  fun _ wf => wf.isDefEqCore he₁ he₂

theorem inferType.WF' {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  fun _ wf => wf.inferType h1 hinf

theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e true) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (inferType.WF' he.fvarsIn fun _ => ⟨_, he⟩).le
    fun _ _ _ ⟨_, _, h1, h2, h3, h4⟩ => ⟨_, h1, he, h3, ?_⟩
  have := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  exact h4.defeqU_l c.Ewf c.Δwf this

theorem inferType.WF_uniq {c : VContext} {s : VState}
    (he : c.TrExprS e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  (inferType.WF he).le fun _ _ _ ⟨_, _, _, h1, h2⟩ =>
  ⟨_, h1, h2.uniqU c.Ewf c.Δwf hty⟩

theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  inferType.WF' h1 nofun

theorem whnfCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapRec cheapProj) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnfCore he

theorem isDelta_is_some : isDelta env e = some ci ↔
    ∃ n, env.find? n = some ci ∧ (∃ v, ci.value? = some v) ∧ ∃ ls, e.getAppFn = .const n ls := by
  simp [isDelta]
  split <;> [split <;> [split; skip]; skip] <;>
    simp_all [ConstantInfo.hasValue_eq, Option.isSome_iff_exists] <;>
    rintro rfl <;> assumption

theorem unfoldDefinitionCore.WF {c : VContext} (he : c.TrExprS e e') :
    unfoldDefinitionCore c.env e = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  simp [unfoldDefinitionCore]; (iterate 3 split <;> [skip; nofun])
  rintro ⟨⟩; rename_i h1 h2
  obtain ⟨_, h3, ⟨_, h4⟩, _, ⟨⟩⟩ := isDelta_is_some.1 h1
  let .const a1 a2 a3 := he
  have ⟨rfl, b1, b2, b3⟩ := c.trenv.find?_uniq h3 a1
  simp [ConstantInfo.instantiateValueLevelParams!, ConstantInfo.value!_eq, h4]
  have c1 := c.trenv.of_value h3 b1 h4 |>.instL c.Ewf (by trivial) a2 (b2.trans a3.symm)
  have := c1.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
  rw [c1.wf.closedN c.Ewf trivial |>.liftN_eq (Nat.zero_le _)] at this
  simp [VExpr.instL] at this; rw [VLevel.inst_map_id] at this
  · exact ⟨fun _ _ _ => c1.fvarsIn.mono nofun, this⟩
  · exact (List.mapM_eq_some.1 a2).length_eq.symm.trans <| a3.trans b2.symm

theorem unfoldDefinition.WF {c : VContext} (he : c.TrExprS e e') :
    unfoldDefinition c.env e = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  simp [unfoldDefinition]; split <;> [split <;> rintro ⟨⟩; exact unfoldDefinitionCore.WF he]
  rename_i f₁ eq
  have ⟨f', stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
  have ⟨h1, h2⟩ := unfoldDefinitionCore.WF stk.tr eq
  rw [Expr.mkAppRevRange_eq (l₁ := []) (l₂ := e.getAppArgsRevList) (l₃ := [])
    (by simp [Expr.getAppRevArgs_toList]) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
  simp only [Expr.getAppArgsRevList_reverse]; constructor
  · exact (e.mkAppList_getAppArgsList ▸ h1.mkAppList :)
  · exact h2.rebuild_mkAppList c.Ewf c.Δwf stk.tr (e.mkAppList_getAppArgsList ▸ he :)
