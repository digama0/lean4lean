import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.TypeChecker

namespace Lean4Lean

namespace TypeChecker
open Lean

def Methods.WF : Methods → Prop := sorry

inductive MLCtx where
  | nil : MLCtx
  | vlam (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) :
    MLCtx → MLCtx

@[simp] def MLCtx.vlctx : MLCtx → VLCtx
  | .nil => []
  | .vlam id _ _ ty _ c => (some id, .vlam ty) :: c.vlctx

def MLCtx.lctx : MLCtx → LocalContext
  | .nil => {}
  | .vlam id name ty _ bi c => c.lctx.mkLocalDecl id name ty bi

@[simp] def MLCtx.length : MLCtx → Nat
  | .nil => 0
  | .vlam _ _ _ _ _ c => c.length + 1

@[simp] def MLCtx.fvarRevList (c : MLCtx) (n) (hn : n ≤ c.length) : List FVarId :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam id _ _ _ _ c, h =>
    id :: c.fvarRevList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] def MLCtx.dropN (c : MLCtx) (n) (hn : n ≤ c.length) : MLCtx :=
  match n, c, hn with
  | 0, c, _ => c
  | n+1, .vlam _ _ _ _ _ c, h =>
      c.dropN n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] def MLCtx.findDecl? (c : MLCtx) (x : FVarId) : Option LocalDecl :=
  match c with
  | .nil => none
  | .vlam v name ty _ bi c =>
    if x == v then some (.cdecl c.length v name ty bi default) else c.findDecl? x

def MLCtx.WF (env : VEnv) (Us : List Name) : MLCtx → Prop
  | .nil => True
  | .vlam fv _ ty ty' _ c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExpr env Us c.vlctx ty ty' ∧
    env.IsType Us.length c.vlctx.toCtx ty'

theorem MLCtx.WF.tr : ∀ {c : MLCtx}, c.WF env Us → TrLCtx env Us c.lctx c.vlctx
  | .nil, _ => .nil
  | .vlam .., ⟨h1, h2, h3, h4⟩ => .mkLocalDecl h1.tr h2 h3 h4

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
    M.WF c s mkFreshId fun a s' => s'.ngen.Reserves ⟨a⟩ ∧ ¬s.ngen.Reserves ⟨a⟩ :=
  sorry

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
    (hty : (c.withMLC m).TrExpr ty ty')
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

@[simp] def MLCtx.mkForall (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, e =>
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstractFVar x e) bi)
termination_by structural n

@[simp] def MLCtx.mkForall' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e =>
    c.mkForall' n (Nat.le_of_succ_le_succ h) (.forallE ty e)
termination_by structural n

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkForall_tr {c : MLCtx} (wf : c.WF env Us)
    (tr : TrExpr env Us c.vlctx e e' ∧ env.IsType Us.length c.vlctx.toCtx e')
    (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  induction n generalizing c e e' with
  | zero => exact tr
  | succ n ih =>
    let .vlam x name ty ty' bi c := c
    refine ih wf.1 ⟨?_, .forallE wf.2.2.2 tr.2⟩ _
    exact .forallE henv wf.1.tr.wf wf.2.2.2 tr.2 wf.2.2.1 (.abstract .zero tr.1)

theorem MLCtx.fvarRevList_prefix (c : MLCtx)
    {n hn} : c.fvarRevList n hn <+: c.vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    let .vlam x name ty ty' bi c := c
    simp [ih]

theorem MLCtx.WF.fvars_nodup : ∀ {c : MLCtx}, c.WF env Us → c.vlctx.fvars.Nodup
  | .nil, _ => .nil
  | .vlam _ _ _ _ _ c, ⟨h1, h2, h3, h4⟩ => by
    simp [h1.fvars_nodup, h1.tr.find?_eq_none.1 h2]

theorem MLCtx.WF.fvarRevList_nodup {c : MLCtx} (wf : c.WF env Us)
    (n hn) : (c.fvarRevList n hn).Nodup :=
  c.fvarRevList_prefix.sublist.nodup wf.fvars_nodup

theorem MLCtx.WF.find?_eq_findDecl? {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.find? x = c.findDecl? x := sorry

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
      let .vlam x name ty ty' bi c := c; simp
      refine (List.foldl_congr fun _ _ h => ?_).trans <|
        .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
      · refine LocalContext.mkBindingList1_congr ?_
        rw [wf.find?_eq_findDecl?, wf.1.find?_eq_findDecl?, findDecl?, if_neg]
        simp; rintro ⟨⟩
        have := wf.fvarRevList_nodup (n+1) hn; simp_all
      · simp [LocalContext.mkBindingList1, wf.find?_eq_findDecl?, findDecl?]
  · intro _ h
    exact wf.tr.find?_eq_some.2 ((MLCtx.fvarRevList_prefix ..).subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (wf.fvarRevList_nodup ..)

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

theorem checkLambda.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (hr : e.FVarsIn s.ngen.Reserves ∧ ∀ v ∈ m.vlctx.fvars, s.ngen.Reserves v)
    (ih : ∀ e' ty',
      (c.withMLC m).TrExpr (e.instantiateList ((m.fvarRevList n hn).map .fvar)) e' →
      (c.withMLC m).HasType e' ty' →
      ∃ e₀', c.TrExpr e₀ e₀' ∧ c.HasType e₀' (m.mkForall' n hn ty')) :
    (inferLambda.loop false arr e).WF (c.withMLC m) s (fun ty _ => ∃ e' ty',
      c.TrExpr e₀ e' ∧ c.TrExpr ty ty' ∧ c.HasType e' ty') := by
  unfold inferLambda.loop; split <;> simp only [pure_bind]
  · rename_i name dom body bi
    refine checkType.WF.bind fun uv _ le₁ ⟨dom', uv', h1, h2, h3⟩ => ?_
    refine (ensureSortCore.WF h2).bind fun _ _ le₂ ⟨u, h4, h5⟩ => ?_
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.venv_wf mwf.1.tr.wf.toCtx h4
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' fun a mwf' s' le₃ res h6 => ?_
    have h6' := wf.find?_eq_none h6
    refine .stateWF fun wf' => ?_
    refine checkLambda.loop.WF (mwf := mwf') (arr := arr.push _) (Nat.succ_le_succ hn)
      (by simp [hdrop]) (by simp [harr]) ?_ ?_
    · have := le₁.trans le₂ |>.trans le₃
      simp [or_imp, forall_and, FVarsIn]
      exact ⟨(this.reserves hr.1).2, res, fun _ h => this.reservesV (hr.2 _ h)⟩
    intro e ty' h7 h9
    dsimp [VContext.TrExpr, VContext.HasType] at h7 h9
    simp [Expr.instantiateRev', Expr.instantiate', harr] at h1
    simp [Expr.instantiateList_lam] at ih
    conv at h7 => arg 4; exact (Expr.instantiateList_instantiate1_comm (by trivial)).symm
    have h7 := h7.uninstantiate ((hr.1.2.instantiateList ?r).mono ?a)
    case r => simp [FVarsIn]; exact fun _ h => hr.2 _ (m.fvarRevList_prefix.subset h)
    case a => rintro _ h rfl; exact h6 <| (le₁.trans le₂).reservesV h
    refine ih _ _ (.lam c.venv_wf mwf.1.tr.wf domty' h1 h7) (.lam domty h9)
  · refine checkType.WF.bind fun ty _ _ ⟨e', ty', h1, h2, h3⟩ => ?_
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    simp [Expr.instantiateRev', Expr.instantiate', harr] at h1
    have ⟨e₀', h1', h2'⟩ := ih _ _ h1 h3
    refine ⟨_, m.mkForall' n hn ty', h1', ?_, h2'⟩
    simp [VContext.withMLC]; rw [mwf.1.mkForall_eq _ _ harr]
    change TrExpr _ _ c.mlctx.vlctx ..; rw [← hdrop]
    refine (mwf.1.mkForall_tr c.venv_wf ⟨?_, h3.isType c.venv_wf mwf.1.tr.wf.toCtx⟩ _ _).1
    have : ty.Safe := sorry -- FIXME: I don't think this is provable
    exact h2.cheapBetaReduce c.venv_wf wf.trctx.wf this m.noBV

theorem checkLambda.WF
    (h1 : e.FVarsIn s.ngen.Reserves) :
    (inferLambda e false).WF c s (fun ty _ => ∃ e' ty',
      c.TrExpr e e' ∧ c.TrExpr ty ty' ∧ c.HasType e' ty') :=
  .stateWF fun wf =>
  c.withMLC_self ▸ checkLambda.loop.WF (Nat.zero_le _) rfl rfl ⟨h1, wf.ngen_wf⟩
    fun _ _ h1 h2 => ⟨_, h1, h2⟩

theorem inferLambda.loop.WF
    (he : c.TrExpr e e')
    (hty : c.HasType e' ty') :
    (inferLambda.loop true fvars e).WF c s Q := by
  unfold inferLambda.loop; split
  · rename_i name dom body bi; simp
    refine .stateWF fun wf => ?_
    let ⟨_, .lam h1 h2 h3, _⟩ := he
    have := h2.trExpr c.venv_wf wf.trctx.wf
    -- refine .withLocalDecl h1 ⟨_, h3.defeqU_r c.venv_wf wf.vlctx_wf h4⟩ fun a s' le res h6 => ?_
    -- refine RecM.WF.withLam res h6 h1 ⟨_, h3.defeqU_r c.venv_wf wf.vlctx_wf h4⟩ ?_
    -- exact inferLambda.loop.WF
    sorry
  · sorry

theorem inferLambda.WF : (inferLambda e true).WF c s Q := by
  simp [inferLambda]
  sorry
