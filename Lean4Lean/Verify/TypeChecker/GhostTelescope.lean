import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.TypeChecker.Frame
import Lean4Lean.Verify.Typing.TelescopeTranslationFVar

/-!
# Ghost verification of the telescope check

`checkType.WF_telTr`: a successful checking run of an expression yields a telescope certificate
(`TelTrN` along the whole syntactic `forallE` spine), from which the constructor telescope
certificates are built (section 5.3 of the design notes).

`inferForall.loop` opens one free variable per binder of the `forallE` spine. The proof reads the
one actual run in every *view*: an `MLCtx` holding the binders that are kept, and a set `G` of
*ghosts*, binders of the run that the view deletes. Each domain and result check of the run is
replayed by the frame lemma (`Methods.withFuel_locality`) in the local context of the view, where
the existing verification (`inferType.WF'`, `ensureSortCore.WF`) translates it. The state stays
well formed for the view throughout: at a kept binder it is extended as by
`RecM.WF.withLocalDecl`, at a ghost binder only the name generator advances. The keep and delete
branches of the certificate at a binder are the two views extending the current one by that
binder; the lowered translation of the delete branch is `TrSyn.lower`, and what the run supplies
there is the typing of the residual telescope (`TelWF`).
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel Inner

namespace GhostTel

theorem bind_ok {x : M α} {f : α → M β} {c : Context} {s s' : State} {b : β}
    (h : (x >>= f) c s = .ok (b, s')) :
    ∃ a s₁, x c s = .ok (a, s₁) ∧ f a c s₁ = .ok (b, s') := by
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind] at h
  split at h
  · cases h
  · exact ⟨_, _, ‹_›, h⟩

theorem bind_ok_rec {x : RecM α} {f : α → RecM β} {m : Methods} {c : Context} {s s' : State}
    {b : β} (h : (x >>= f) m c s = .ok (b, s')) :
    ∃ a s₁, x m c s = .ok (a, s₁) ∧ f a m c s₁ = .ok (b, s') :=
  bind_ok (x := x m) (f := fun a => f a m) h

theorem withLocalDecl_run {f : Expr → RecM α} {m : Methods} {c : Context} {s : State} :
    (withLocalDecl name bi ty f : RecM α) m c s =
      (f (.fvar ⟨s.ngen.curr⟩) m { c with lctx := c.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
        { s with ngen := s.ngen.next }).map fun p => (p.1, s.exitScope c.fuel.cacheMode p.2) :=
  withFreshId_eq _ _ _

theorem loop_forallE_run {m : Methods} {c : Context} {s s' : State}
    (h : inferForall.loop io arr us (.forallE name dom body bi) m c s = .ok (r, s')) :
    ∃ T s₁ t s₂, m.inferType (dom.instantiateRev arr) io c s = .ok (T, s₁) ∧
      ensureSortCore T (dom.instantiateRev arr) m c s₁ = .ok (t, s₂) ∧
      ∃ r' s'', inferForall.loop io (arr.push (.fvar ⟨s₂.ngen.curr⟩)) (us.push t.sortLevel!) body
        m { c with lctx := c.lctx.mkLocalDecl ⟨s₂.ngen.curr⟩ name (dom.instantiateRev arr) bi }
        { s₂ with ngen := s₂.ngen.next } = .ok (r', s'') := by
  unfold inferForall.loop at h
  obtain ⟨T, s₁, h1, h⟩ := bind_ok_rec h
  obtain ⟨t, s₂, h2, h⟩ := bind_ok_rec h
  refine ⟨T, s₁, t, s₂, h1, h2, ?_⟩
  rw [withLocalDecl_run] at h
  revert h; cases inferForall.loop io _ _ body m _ _ <;> simp [Except.map]
  intros; exact ⟨_, _, rfl⟩

theorem loop_other_run {m : Methods} {c : Context} {s s' : State}
    (he : ∀ n d b bi, e ≠ .forallE n d b bi)
    (h : inferForall.loop io arr us e m c s = .ok (r, s')) :
    ∃ T s₁ t s₂, m.inferType (e.instantiateRev arr) io c s = .ok (T, s₁) ∧
      ensureSortCore T e m c s₁ = .ok (t, s₂) := by
  unfold inferForall.loop at h
  split at h
  · exact (he _ _ _ _ rfl).elim
  obtain ⟨T, s₁, h1, h⟩ := bind_ok_rec h
  obtain ⟨t, s₂, h2, h⟩ := bind_ok_rec h
  exact ⟨T, s₁, t, s₂, h1, h2⟩

theorem inferType'_forallE_run {m : Methods} {c : Context} {s s' : State}
    (hc : s.inferTypeC[Expr.forallE name dom body bi]? = none)
    (h : inferType' (.forallE name dom body bi) false m c s = .ok (r, s')) :
    ∃ r₁ s₁, inferForall (.forallE name dom body bi) false m c s = .ok (r₁, s₁) := by
  unfold inferType' at h
  by_cases hb : (Expr.forallE name dom body bi).hasLooseBVars
  · simp only [hb, if_true] at h; exact (nomatch h)
  simp only [hb, if_false, Bool.false_eq_true] at h
  obtain ⟨st, s₀, h0, h⟩ := bind_ok_rec h
  cases h0
  simp only [cond_false, hc] at h
  obtain ⟨r₁, s₁, h1, -⟩ := bind_ok_rec h
  exact ⟨r₁, s₁, h1⟩

/-! ### The bound-variable form of a telescope -/

/-- The local context `m.vlctx` with its top `n` binders turned into bound variables. -/
@[simp] def vlctxBV (m : MLCtx) (n : Nat) (hn : n ≤ m.length) : VLCtx :=
  match n, m, hn with
  | 0, m, _ => m.vlctx
  | n+1, .vlam _ _ _ ty' _ m, h => (none, .vlam ty') :: vlctxBV m n (Nat.le_of_succ_le_succ h)
  | n+1, .vlet _ _ _ _ ty' v' m, h =>
    (none, .vlet ty' v') :: vlctxBV m n (Nat.le_of_succ_le_succ h)
termination_by structural n

theorem vlctxBV_toCtx : ∀ (m : MLCtx) n hn, (vlctxBV m n hn).toCtx = m.vlctx.toCtx
  | _, 0, _ => rfl
  | .vlam _ _ _ _ _ m, n+1, _ => by
    simp [vlctxBV, VLCtx.toCtx, vlctxBV_toCtx m n]
  | .vlet _ _ _ _ _ _ m, n+1, _ => by
    simp [vlctxBV, VLCtx.toCtx, vlctxBV_toCtx m n]

theorem abstract_prefix {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {deps} :
    ∀ (Γ : VLCtx), (∀ x ∈ Γ, x.1 = none) → ∃ k, VLCtx.Abstract Δ₀ v₀ d₀ Γ.length k
      (Γ ++ (some (v₀, deps), d₀) :: Δ₀) (Γ ++ (none, d₀) :: Δ₀)
  | [], _ => ⟨0, .zero⟩
  | (o, d) :: Γ, h => by
    obtain rfl : o = none := h _ (.head _)
    obtain ⟨k, W⟩ := abstract_prefix Γ fun x hx => h x (.tail _ hx)
    exact ⟨_, .succ W⟩

/-- Turning the free variables of the top `n` binders of `m` back into bound variables. -/
theorem uninstantiate_vlctxBV {env : VEnv} {Us : List Name} :
    ∀ (m : MLCtx) (n) (hn : n ≤ m.length) (Γ : VLCtx) {e : Expr} {e' : VExpr},
    (∀ x ∈ Γ, x.1 = none) → (m.fvarRevList n hn).Nodup →
    FVarsIn (· ∉ m.fvarRevList n hn) e →
    TrExprS env Us (Γ ++ m.vlctx)
      (e.instantiateList ((m.fvarRevList n hn).map .fvar) Γ.length) e' →
    TrExprS env Us (Γ ++ vlctxBV m n hn) e e'
  | m, 0, _, Γ, _, _, _, _, _, H => H
  | .vlam a _ _ ty' _ m, n+1, hn, Γ, e, e', hΓ, hnd, he, H
  | .vlet a _ _ _ ty' _ m, n+1, hn, Γ, e, e', hΓ, hnd, he, H => by
    simp only [MLCtx.fvarRevList, List.map_cons, Expr.instantiateList, List.nodup_cons,
      List.mem_cons, not_or] at hnd he H ⊢
    rw [← TelTrFVar.instantiateList_instantiate1_comm (by rfl)
      (by simp; intros; rfl)] at H
    obtain ⟨_, W⟩ := abstract_prefix (Δ₀ := m.vlctx) (v₀ := a) (deps := _) (d₀ := _) Γ hΓ
    have H := H.uninstantiateN W <| by
      refine (he.mono fun _ h => h.1).instantiateList ?_ (Γ.length + 1)
      simp only [List.mem_map]
      rintro _ ⟨f, hf, rfl⟩; rintro rfl; exact hnd.1 hf
    have := uninstantiate_vlctxBV m n _ (Γ ++ [(none, _)])
      (by simpa [or_imp, forall_and] using hΓ) hnd.2 (he.mono fun _ h => h.2)
      (by simpa using H)
    simpa using this

/-! ### Well-formed states across a binder -/

/-- Advancing the name generator keeps a state well formed (the state at a ghost binder). -/
theorem State.WF.next {c : VContext} {s : State} (wf : s.WF c) : s.next.WF c :=
  wf.leaveScope (s := s.next) (show s ≤ s.next from .next) wf.unfold_wf

theorem mlcwf_vlam {c : VContext} {m} [cwf : c.MLCWF m] {s : State}
    (wf : s.WF (c.withMLC m)) (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty') :
    c.MLCWF (m.vlam ⟨s.ngen.curr⟩ name ty ty' bi) :=
  ⟨cwf.1, wf.find?_eq_none s.ngen.not_reserves_self, hty, hty'⟩

/-! ### Ghost-extended local contexts -/

theorem find?_mkLocalDecl {l : LocalContext} {fv fv' : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} (hwf : l.WF) :
    (l.mkLocalDecl fv name ty bi).find? fv' =
      if fv == fv' then some (.cdecl l.decls.size fv name ty bi .default) else l.find? fv' := by
  simp only [LocalContext.mkLocalDecl, LocalContext.find?]
  exact hwf.map_wf.find?_insert

/-- The ghost relation between the actual context and the context of a view. -/
theorem ghostRel_mk {G : FVarId → Prop} {c : VContext} {m} [c.MLCWF m] {s : State}
    {ctx₁ : Context} (wf : s.WF (c.withMLC m)) (hG : ∀ fv ∈ m.vlctx.fvars, ¬ G fv)
    (hlwf : ctx₁.lctx.WF) (henv : EnvGhostFree (fun _ => True) c.env)
    (hctx : ctx₁ = { c.toContext with lctx := ctx₁.lctx })
    (hfind : ∀ ⦃fv⦄, ¬ G fv →
      (ctx₁.lctx.find? fv).map (·.setIndex 0) = (m.lctx.find? fv).map (·.setIndex 0)) :
    GhostRel G ctx₁ (c.withMLC m).toContext where
  eq := hctx
  find? := hfind
  wf₁ := hlwf.map_wf
  wf₂ := wf.trctx.1.map_wf
  env _ _ h := let H := henv h
    have F : ∀ fv, ¬ True → ¬ G fv := fun _ h => (h trivial).elim
    ⟨H.type.mono F, fun _ h => (H.deltaValue h).mono F,
      fun _ h r hr => (H.rules h r hr).mono F⟩
  decls := by
    intro fv d hd
    have hd' : d ∈ (c.withMLC m).lctx'.toList := by
      change (c.withMLC m).lctx'.find? fv = some d at hd
      rw [wf.trctx.1.find?_eq_find?_toList] at hd
      exact List.mem_of_find?_eq_some hd
    obtain ⟨_, _, -, -, -, h4, h5⟩ := wf.trctx.find?_of_mem c.Ewf hd'
    have hP : ∀ fv, fv ∈ (c.withMLC m).vlctx.fvars → ¬ G fv := hG
    refine ⟨h5.fvarsIn.mono hP, fun v hv => ?_⟩
    cases d with
    | cdecl => simp [LocalDecl.value?] at hv
    | ldecl _ _ _ _ _ nd =>
      cases nd <;> simp [LocalDecl.value?] at hv <;> subst hv <;> exact h4.fvarsIn.mono hP

/-! ### Ghost-free states -/

/-- The cached values of a well-formed state do not mention the next fresh variable, so the state
is ghost-free for the ghosts extended by it. -/
theorem GhostFreeState.ghost {G : FVarId → Prop} {c : VContext} {s : State} (h : GhostFreeState G s)
    (wf : State.WF c s) (henv : EnvGhostFree (fun _ => True) c.env) :
    GhostFreeState (fun fv => G fv ∨ fv = ⟨s.ngen.curr⟩) { s with ngen := s.ngen.next } := by
  have hres {r : Expr} (h1 : GhostFree G r) (h2 : FVarsIn s.ngen.Reserves r) :
      GhostFree (fun fv => G fv ∨ fv = ⟨s.ngen.curr⟩) r :=
    FVarsIn.mp (fun _ a b => by
      rintro (h | rfl)
      · exact a h
      · exact s.ngen.not_reserves_self b) h1 h2
  refine ⟨fun _ _ e => hres (h.inferTypeI e) (wf.inferTypeI_wf e).2.2.2.1,
    fun _ _ e => hres (h.inferTypeC e) (wf.inferTypeC_wf e).2.2.2.1,
    fun _ _ e => hres (h.whnfCore e) (wf.whnfCore_wf e).2.2.2.1,
    fun _ _ e => hres (h.whnf e) (wf.whnf_wf e).2.2.2.1, fun _ r e => ?_, ?_⟩
  · obtain ⟨n, ls, ci, -, hci, rfl⟩ := wf.unfold_wf e
    refine fvarsIn_iff.2 ⟨fun fv hfv => ?_, (fvarsIn_iff.1 (h.unfold e)).2⟩
    exfalso
    simp only [Inner.instantiateDeltaValue, TelTrFVar.fvarsList_instantiateLevelParams] at hfv
    cases hv : ci.deltaValue? with
    | none => simp [hv] at hfv; cases hfv
    | some v =>
      simp only [hv, Option.get!_some] at hfv
      exact (fvarsIn_iff.1 ((henv hci).deltaValue hv)).1 _ hfv trivial
  · rintro fv (hg | rfl)
    · exact (h.reserved hg).mono .next
    · exact s.ngen.next_reserves_self

/-! ### Sub-runs, replayed in the ghost-free context -/

/-- A domain or result check of the loop, run in the ghost-extended context, is the same run in the
context of the view, where the existing verification gives its translation. -/
theorem check_sort {c : VContext} {m} [c.MLCWF m] {G : FVarId → Prop} {ctx₁ : Context}
    {s s₁ s₂ : State} {E T t X : Expr} {k : Nat}
    (hR : GhostRel G ctx₁ (c.withMLC m).toContext) (hS : GhostFreeState G s)
    (wf : State.WF (c.withMLC m) s)
    (hE : FVarsIn (· ∈ m.vlctx.fvars) E) (hG : ∀ fv ∈ m.vlctx.fvars, ¬ G fv)
    (h1 : (Methods.withFuel k).inferType E false ctx₁ s = .ok (T, s₁))
    (h2 : ensureSortCore T X (Methods.withFuel k) ctx₁ s₁ = .ok (t, s₂)) :
    ∃ e', (c.withMLC m).TrExprS E e' ∧ (c.withMLC m).IsType e' ∧
      GhostFreeState G s₂ ∧ State.WF (c.withMLC m) s₂ := by
  have hGF : GhostFree G E := hE.mono hG
  have F := Methods.withFuel_locality G k
  obtain ⟨h1', gT, gs1, -⟩ := F.inferType false hGF hR hS h1
  obtain ⟨⟨s₁'⟩, eq, -, wf1, e', T', -, he', hT', hty⟩ :=
    Inner.inferType.WF' (c := c.withMLC m) (s := s) (inferOnly := false) hE nofun _
      Methods.withFuel.WF wf _ _ h1'
  cases eq
  obtain ⟨h2', -, gs2, -⟩ := ensureSortCore.framed gT F hR gs1 h2
  obtain ⟨⟨s₂'⟩, eq, -, wf2, ⟨u, rfl⟩, h5, -⟩ :=
    Inner.ensureSortCore.WF (c := c.withMLC m) (e₀ := X) hT' _
      Methods.withFuel.WF wf1 _ _ h2'
  cases eq
  let ⟨_, .sort _, h5⟩ := h5
  have := hty.defeqU_r (c.withMLC m).Ewf (c.withMLC m).Δwf.toCtx h5.symm
  exact ⟨e', he', ⟨_, this⟩, gs2, wf2⟩

/-! ### The loop -/

theorem fvs_closed {l : List FVarId} : ∀ x ∈ l.map Expr.fvar, x.looseBVarRange' = 0 := by
  simp; intros; rfl

theorem arr_closed {arr : Array Expr} (harr : ∀ x ∈ arr.toList, ∃ f, x = .fvar f) :
    ∀ x ∈ arr.toList.reverse, x.looseBVarRange' = 0 := by
  intro x hx; obtain ⟨f, rfl⟩ := harr x (List.mem_reverse.1 hx); rfl

theorem fvarsIn_inst {c : VContext} {m : MLCtx} {n hn} (hdrop : m.dropN n hn = c.mlctx)
    {e : Expr} (he : FVarsIn (· ∈ c.vlctx.fvars) e) :
    FVarsIn (· ∈ m.vlctx.fvars) (e.instantiateList ((m.fvarRevList n hn).map .fvar)) := by
  refine (he.mono fun _ h => ?_).instantiateList ?_
  · exact m.dropN_fvars_subset n hn (hdrop ▸ h)
  · simp [FVarsIn]; exact fun _ h => m.fvarRevList_prefix.subset h

theorem fvarsIn_low {c : VContext} {m : MLCtx} [cwf : c.MLCWF m] {n hn}
    (hdrop : m.dropN n hn = c.mlctx) {e : Expr} (he : FVarsIn (· ∈ c.vlctx.fvars) e) :
    FVarsIn (· ∉ m.fvarRevList n hn) e := by
  refine he.mono fun fv h h' => ?_
  have nd := cwf.1.fvars_nodup
  rw [m.fvars_eq_append (n := n) (hn := hn), hdrop] at nd
  exact (List.nodup_append.1 nd).2.2 _ h' _ h rfl

theorem uninst_view {c : VContext} {m : MLCtx} [cwf : c.MLCWF m] {n hn}
    (hdrop : m.dropN n hn = c.mlctx) {e : Expr} {e' : VExpr} (he : FVarsIn (· ∈ c.vlctx.fvars) e)
    (H : (c.withMLC m).TrExprS (e.instantiateList ((m.fvarRevList n hn).map .fvar)) e') :
    TrExprS c.venv c.lparams (vlctxBV m n hn) e e' :=
  uninstantiate_vlctxBV m n hn [] nofun (cwf.1.fvarRevList_nodup n hn) (fvarsIn_low hdrop he) H

theorem loop_base {c : VContext} {k : Nat} (henv : EnvGhostFree (fun _ => True) c.env)
    {e : Expr} (hne : ∀ n d b bi, e ≠ .forallE n d b bi)
    {m : MLCtx} [cwf : c.MLCWF m] {n : Nat} {hn : n ≤ m.length}
    {arr : Array Expr} {us : Array Level} {G : FVarId → Prop} {L : LocalContext}
    {s s' : State} {r e_low : Expr}
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : ∀ x ∈ arr.toList, ∃ f, x = .fvar f)
    (hei : e.instantiateList arr.toList.reverse =
      e_low.instantiateList ((m.fvarRevList n hn).map .fvar))
    (hlow : FVarsIn (· ∈ c.vlctx.fvars) e_low)
    (hG : ∀ fv ∈ m.vlctx.fvars, ¬ G fv) (hlwf : L.WF)
    (hfind : ∀ ⦃fv⦄, ¬ G fv →
      (L.find? fv).map (·.setIndex 0) = (m.lctx.find? fv).map (·.setIndex 0))
    (hS : GhostFreeState G s) (wf : State.WF (c.withMLC m) s)
    (hrun : inferForall.loop false arr us e (Methods.withFuel k) { c.toContext with lctx := L } s =
      .ok (r, s')) :
    ∃ e', TelTrN c.venv c.lparams (AddInductive.constructorArity e_low) (vlctxBV m n hn) e_low e' ∧
      c.venv.IsType c.lparams.length (vlctxBV m n hn).toCtx e' := by
  obtain ⟨T, s₁, t, s₂, h1, h2⟩ := loop_other_run hne hrun
  rw [Expr.instantiateRev_eq_instantiateList, hei] at h1
  have hR := ghostRel_mk (ctx₁ := { c.toContext with lctx := L }) wf hG hlwf henv rfl hfind
  obtain ⟨e', he', hty, -⟩ := check_sort hR hS wf (fvarsIn_inst hdrop hlow) hG h1 h2
  have H : ∀ {n d b bi}, e_low ≠ .forallE n d b bi := by
    rintro _ _ _ _ rfl
    rw [Expr.instantiateList_forallE] at hei
    obtain ⟨_, _, rfl⟩ := TelTrFVar.instantiateList_fvars_forallE
      (fun x hx => harr x (List.mem_reverse.1 hx)) hei
    exact hne _ _ _ _ rfl
  have h0 : AddInductive.constructorArity e_low = 0 := by
    cases e_low <;> first | rfl | exact (H rfl).elim
  have hty' : c.venv.IsType c.lparams.length (vlctxBV m n hn).toCtx e' := vlctxBV_toCtx .. ▸ hty
  have S := uninst_view hdrop hlow he'
  rw [h0]
  exact ⟨e', ⟨S.toTrSyn, .zero (let ⟨_, h⟩ := hty'; ⟨_, h⟩) S.residual⟩, hty'⟩

/-- The loop of `inferForall`, read in every *view*: an `MLCtx` `m` holding the kept binders (its
top `n` entries) and a set `G` of ghosts (binders of the actual run that are absent from `m`).
The remaining telescope `e` of the run and its ghost-free form `e_low` agree after instantiation.
The conclusion is the telescope certificate of `e_low`, along its whole syntactic spine, in the
bound-variable form of `m`. -/
theorem loop_telTr {c : VContext} {k : Nat} (henv : EnvGhostFree (fun _ => True) c.env) :
    ∀ (e : Expr) {m : MLCtx} [c.MLCWF m] {n : Nat} (hn : n ≤ m.length)
      {arr : Array Expr} {us : Array Level} {G : FVarId → Prop} {L : LocalContext}
      {s s' : State} {r e_low : Expr},
    m.dropN n hn = c.mlctx →
    (∀ x ∈ arr.toList, ∃ f, x = .fvar f) →
    e.instantiateList arr.toList.reverse =
      e_low.instantiateList ((m.fvarRevList n hn).map .fvar) →
    FVarsIn (· ∈ c.vlctx.fvars) e_low →
    (∀ fv ∈ m.vlctx.fvars, ¬ G fv) →
    L.WF →
    (∀ ⦃fv⦄, ¬ G fv → (L.find? fv).map (·.setIndex 0) = (m.lctx.find? fv).map (·.setIndex 0)) →
    GhostFreeState G s →
    State.WF (c.withMLC m) s →
    inferForall.loop false arr us e (Methods.withFuel k) { c.toContext with lctx := L } s =
      .ok (r, s') →
    ∃ e', TelTrN c.venv c.lparams (AddInductive.constructorArity e_low) (vlctxBV m n hn) e_low e' ∧
      c.venv.IsType c.lparams.length (vlctxBV m n hn).toCtx e' := by
  intro e
  induction e with
  | forallE name dom body bi _ ih =>
    intro m cwf n hn arr us G L s s' r e_low hdrop harr hei hlow hG hlwf hfind hS wf hrun
    obtain ⟨T, s₁, t, s₂, h1, h2, r', s'', hrun'⟩ := loop_forallE_run hrun
    -- the ghost-free form of the telescope is a `forallE` too
    rw [Expr.instantiateList_forallE] at hei
    obtain ⟨d_low, b_low, rfl⟩ := TelTrFVar.instantiateList_fvars_forallE
      (by simp) hei.symm
    rw [Expr.instantiateList_forallE, Expr.forallE.injEq] at hei
    obtain ⟨-, hd, hb, -⟩ := hei
    have hfvs := fvs_closed (l := m.fvarRevList n hn)
    have harr' := arr_closed harr
    -- the domain check, replayed in the view
    rw [Expr.instantiateRev_eq_instantiateList, hd] at h1
    have hR := ghostRel_mk (ctx₁ := { c.toContext with lctx := L }) wf hG hlwf henv rfl hfind
    obtain ⟨d', hd', domty, gs2, wf2⟩ := check_sort hR hS wf (fvarsIn_inst hdrop hlow.1) hG h1 h2
    rw [Expr.instantiateRev_eq_instantiateList, hd] at hrun'
    generalize hE : d_low.instantiateList ((m.fvarRevList n hn).map .fvar) = E at hd' hrun'
    -- the fresh variable
    generalize ha : (⟨s₂.ngen.curr⟩ : FVarId) = a at hrun'
    have ha_res : ¬ s₂.ngen.Reserves a := ha ▸ s₂.ngen.not_reserves_self
    have hGa : ¬ G a := fun h => ha_res (gs2.reserved h)
    have ha_m : a ∉ m.vlctx.fvars := fun h => ha_res (wf2.ngen_wf _ h)
    have hma : m.lctx.find? a = none := wf2.find?_eq_none ha_res
    have hLa : L.find? a = none := by
      have := hfind hGa; rw [hma] at this; simpa using this
    have hmwf : m.lctx.WF := wf2.trctx.1
    have hlwf' : (L.mkLocalDecl a name E bi).WF := hlwf.mkLocalDecl hLa
    have hdlow : TrExprS c.venv c.lparams (vlctxBV m n hn) d_low d' :=
      uninst_view hdrop hlow.1 (hE ▸ hd')
    have domty' : c.venv.IsType c.lparams.length (vlctxBV m n hn).toCtx d' :=
      vlctxBV_toCtx .. ▸ domty
    -- the kept binder
    have cwf' : c.MLCWF (m.vlam a name E d' bi) := ha ▸ mlcwf_vlam (s := s₂) wf2 hd' domty
    have wf' : State.WF (c.withMLC (m.vlam a name E d' bi)) { s₂ with ngen := s₂.ngen.next } := by
      subst ha; exact State.WF.vlam (s := s₂) wf2 hd' domty
    obtain ⟨b', hTb, hIb⟩ := ih (m := m.vlam a name E d' bi) (n := n + 1) (Nat.succ_le_succ hn)
      (G := G) (L := L.mkLocalDecl a name E bi) (e_low := b_low) (by simpa using hdrop)
      (by
        intro x hx; simp at hx
        rcases hx with hx | rfl
        · exact harr x (by simpa using hx)
        · exact ⟨_, rfl⟩)
      (by
        simp only [Array.toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, MLCtx.fvarRevList, List.map_cons]
        show (body.instantiate1' (.fvar a) 0).instantiateList _ =
          (b_low.instantiate1' (.fvar a) 0).instantiateList _
        rw [← TelTrFVar.instantiateList_instantiate1_comm (k := 0) rfl harr', hb,
          TelTrFVar.instantiateList_instantiate1_comm (k := 0) rfl hfvs])
      hlow.2
      (by simp; exact ⟨hGa, hG⟩) hlwf'
      (by
        intro fv hfv
        show _ = Option.map _ ((m.lctx.mkLocalDecl a name E bi).find? fv)
        rw [find?_mkLocalDecl hlwf, find?_mkLocalDecl hmwf]
        split
        · simp [LocalDecl.setIndex]
        · exact hfind hfv)
      (GhostFreeState.next gs2) wf' hrun'
    have hIb' : c.venv.IsType c.lparams.length (d' :: (vlctxBV m n hn).toCtx) b' := hIb
    have hFT := domty'.forallE hIb'
    refine ⟨.forallE d' b', ⟨.forallE hdlow.toTrSyn hTb.syn,
      .succ (let ⟨_, h⟩ := hFT; ⟨_, h⟩) (.forallE hdlow.toTrSyn hdlow.residual hTb.tel.residual)
        hTb.tel ?_⟩, hFT⟩
    · intro b₀ b₀' hb0 hb0'
      subst hb0
      -- the ghosted binder: same actual run, the fresh variable joins the ghosts
      have wfg : State.WF (c.withMLC m) { s₂ with ngen := s₂.ngen.next } :=
        State.WF.next (s := s₂) wf2
      have gsg := GhostFreeState.ghost (c := c.withMLC m) gs2 wf2 henv
      rw [ha] at gsg
      obtain ⟨b₀'', hT0, -⟩ := ih (m := m) hn (G := fun fv => G fv ∨ fv = a)
        (L := L.mkLocalDecl a name E bi) (e_low := b₀) hdrop
        (by
          intro x hx; simp at hx
          rcases hx with hx | rfl
          · exact harr x (by simpa using hx)
          · exact ⟨_, rfl⟩)
        (by
          simp only [Array.toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.cons_append]
          show (body.instantiate1' (.fvar a) 0).instantiateList _ = _
          rw [← TelTrFVar.instantiateList_instantiate1_comm (k := 0) rfl harr', hb,
            TelTrFVar.instantiateList_delete rfl hfvs])
        (TelTrFVar.FVarsIn.of_liftLooseBVars hlow.2)
        (by rintro fv hfv (h | rfl); exacts [hG _ hfv h, ha_m hfv]) hlwf'
        (by
          rintro fv hfv
          simp only [not_or] at hfv
          rw [find?_mkLocalDecl hlwf, if_neg (by simpa using Ne.symm hfv.2)]
          exact hfind hfv.1)
        gsg wfg hrun'
      obtain ⟨x, sx, hx⟩ := hTb.syn.lower
      change _ = VExpr.lift x at hx
      cases sx.unique hT0.syn
      rw [hb0'] at hx
      cases VExpr.liftN_inj.1 hx
      rw [AddInductive.constructorArity_liftLooseBVars']
      exact hT0.tel
  | _ =>
    intro m cwf n hn arr us G L s s' r e_low hdrop harr hei hlow hG hlwf hfind hS wf hrun
    exact loop_base henv (fun _ _ _ _ h => by cases h) hdrop harr hei hlow hG hlwf hfind hS wf hrun

theorem checkType_run {e : Expr} {ctx : Context} {s : State} :
    (checkType e : M Expr) ctx s =
      (Methods.withFuel ctx.fuel.recDepth).inferType e false ctx s := rfl

end GhostTel

open GhostTel in
/-- A successful checking run of `e` yields a telescope certificate of `e`: its syntactic
translation, with the typing of the translation and of every residual telescope obtained by
deleting any subset of the unused binders of its leading `forallE` spine. The deleted forms are derived by the verified checker itself, from the
same run read in the local context without the deleted binders (`Methods.withFuel_locality`).

`henv`: no constant of the environment mentions a free variable (every environment built by the
checker satisfies this; the frame lemma needs it for the ghosts). `hunf`, `hcache`: the start
state has no metavariable in its `unfold` cache and no checking-mode cache entry for `e`; a fresh
state, as used for every constructor type, has both. -/
theorem checkType.WF_telTr {c : VContext} {s : State} {e : Expr}
    (henv : EnvGhostFree (fun _ => True) c.env)
    (hunf : ∀ ⦃k r : Expr⦄, s.unfold[k]? = some r → FVarsIn (fun _ => True) r)
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) (hcache : s.inferTypeC[e]? = none) :
    M.WF c s (checkType e) fun _ _ =>
      ∃ e', TelTrN c.venv c.lparams (AddInductive.constructorArity e) c.vlctx e e' := by
  intro wf a s' hrun
  obtain ⟨vs', h1', h2', h3', e', ty', htyping⟩ := checkType.WF h1 wf a s' hrun
  refine ⟨vs', h1', h2', h3', ?_⟩
  by_cases hfa : ∃ n d b bi, e = .forallE n d b bi
  case neg =>
    have h0 : AddInductive.constructorArity e = 0 := by
      cases e <;> first | rfl | exact (hfa ⟨_, _, _, _, rfl⟩).elim
    rw [h0]
    exact ⟨e', .zero c.Ewf.ordered c.Δwf htyping.2.1⟩
  obtain ⟨name, dom, body, bi, rfl⟩ := hfa
  rw [checkType_run] at hrun
  generalize c.fuel.recDepth = N at hrun
  cases N with
  | zero => cases hrun
  | succ k =>
  obtain ⟨r₁, s₁, hrun⟩ := inferType'_forallE_run hcache hrun
  have hgf : GhostFreeState (fun _ => False) s :=
    { inferTypeI := fun _ _ h => (wf.inferTypeI_wf h).2.2.2.1.mono fun _ _ => not_false
      inferTypeC := fun _ _ h => (wf.inferTypeC_wf h).2.2.2.1.mono fun _ _ => not_false
      whnfCore := fun _ _ h => (wf.whnfCore_wf h).2.2.2.1.mono fun _ _ => not_false
      whnf := fun _ _ h => (wf.whnf_wf h).2.2.2.1.mono fun _ _ => not_false
      unfold := fun _ _ h => (hunf h).mono fun _ _ => not_false
      reserved := nofun }
  have wf' : State.WF (c.withMLC c.mlctx) s := by rw [c.withMLC_self]; exact wf
  have hlwf : c.lctx.WF := c.lctx_eq ▸ wf.trctx.1
  obtain ⟨e', H, -⟩ := loop_telTr (k := k) henv (.forallE name dom body bi) (m := c.mlctx) (n := 0)
    (Nat.zero_le _) (arr := #[]) (G := fun _ => False) (L := c.lctx) rfl (by simp) rfl h1
    (fun _ _ => not_false) hlwf (fun _ _ => by rw [c.lctx_eq]) hgf wf' hrun
  exact ⟨e', H⟩
