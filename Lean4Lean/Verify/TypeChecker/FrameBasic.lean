import Lean4Lean.Verify.TypeChecker.FrameDefs
import Lean4Lean.Verify.LocalContext

/-!
# Frame lemma: combinators

Monadic combinators for `M.PreservesGhostRestriction` and `RecM.PreservesGhostRestriction` (see
`FrameDefs.lean`): bind, pure, throw, state access, reads of the context, local-context lookups at
non-ghosts, binders.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

/-! ### The relation between the contexts -/

theorem GhostRel.ctx_eq {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) :
    c₁.env = c₂.env ∧ c₁.safety = c₂.safety ∧ c₁.eagerReduce = c₂.eagerReduce ∧
    c₁.lparams = c₂.lparams ∧ c₁.fuel = c₂.fuel := by
  have := h.eq; revert this; cases c₁; cases c₂; simp +contextual

theorem GhostRel.env_eq {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) : c₁.env = c₂.env :=
  h.ctx_eq.1

theorem GhostRel.withLCtx {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) {l₁ l₂ : LocalContext}
    (hf : ∀ ⦃fv⦄, ¬ G fv → (l₁.find? fv).map (·.setIndex 0) = (l₂.find? fv).map (·.setIndex 0))
    (hd : ∀ ⦃fv d⦄, l₂.find? fv = some d →
      GhostFree G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GhostFree G v)
    (hw₁ : l₁.fvarIdToDecl.WF) (hw₂ : l₂.fvarIdToDecl.WF) :
    GhostRel G { c₁ with lctx := l₁ } { c₂ with lctx := l₂ } where
  eq := by have := h.eq; revert this; cases c₁; cases c₂; simp +contextual
  find? := hf
  decls := hd
  wf₁ := hw₁
  wf₂ := hw₂
  env := h.env

theorem find?_mkLetDecl {l : LocalContext} {fv fv' : FVarId} {name : Name} {ty val : Expr}
    {nonDep : Bool} {kind : LocalDeclKind} (hwf : l.fvarIdToDecl.WF) :
    (l.mkLetDecl fv name ty val nonDep kind).find? fv' =
      if fv == fv' then some (.ldecl l.decls.size fv name ty val nonDep kind)
      else l.find? fv' := by
  simp only [LocalContext.mkLetDecl, LocalContext.find?]
  exact hwf.find?_insert

theorem GhostRel.mkLocalDecl {c₁ c₂ : Context} {id : FVarId} (h : GhostRel G c₁ c₂)
    (hty : GhostFree G ty) :
    GhostRel G { c₁ with lctx := c₁.lctx.mkLocalDecl id name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl id name ty bi } := by
  refine h.withLCtx (fun fv hfv => ?_) (fun fv d hd => ?_)
    (by simp only [LocalContext.mkLocalDecl]; exact h.wf₁.insert)
    (by simp only [LocalContext.mkLocalDecl]; exact h.wf₂.insert)
  · rw [LocalContext.find?_mkLocalDecl h.wf₁, LocalContext.find?_mkLocalDecl h.wf₂]
    split
    · simp [LocalDecl.setIndex]
    · exact h.find? hfv
  · rw [LocalContext.find?_mkLocalDecl h.wf₂] at hd
    split at hd
    · cases hd; exact ⟨hty, by simp [LocalDecl.value?]⟩
    · exact h.decls hd

theorem GhostRel.mkLetDecl {c₁ c₂ : Context} {id : FVarId} (h : GhostRel G c₁ c₂)
    (hty : GhostFree G ty) (hval : GhostFree G val) :
    GhostRel G { c₁ with lctx := c₁.lctx.mkLetDecl id name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl id name ty val } := by
  refine h.withLCtx (fun fv hfv => ?_) (fun fv d hd => ?_)
    (by simp only [LocalContext.mkLetDecl]; exact h.wf₁.insert)
    (by simp only [LocalContext.mkLetDecl]; exact h.wf₂.insert)
  · rw [find?_mkLetDecl h.wf₁, find?_mkLetDecl h.wf₂]
    split
    · simp [LocalDecl.setIndex]
    · exact h.find? hfv
  · rw [find?_mkLetDecl h.wf₂] at hd
    split at hd
    · cases hd; exact ⟨hty, by simp [LocalDecl.value?]; exact hval⟩
    · exact h.decls hd

theorem GhostRel.eager {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) :
    GhostRel G { c₁ with eagerReduce := true } { c₂ with eagerReduce := true } where
  eq := by have := h.eq; revert this; cases c₁; cases c₂; simp +contextual
  find? := h.find?
  decls := h.decls
  wf₁ := h.wf₁
  wf₂ := h.wf₂
  env := h.env

/-! ### `M.PreservesGhostRestriction` -/

theorem M.PreservesGhostRestriction.bind {x : M α} {f : α → M β} {P Q}
    (h1 : M.PreservesGhostRestriction G x P) (h2 : ∀ a, P a → M.PreservesGhostRestriction G (f a) Q) : M.PreservesGhostRestriction G (x >>= f) Q := by
  intro c₁ c₂ s b s' hr hs e
  simp only [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind] at e ⊢
  cases ex : x c₁ s with
  | error => rw [ex] at e; cases e
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [ex] at e
    obtain ⟨h1a, h1b, h1c, h1d⟩ := h1 hr hs ex
    rw [h1a]
    obtain ⟨h2a, h2b, h2c, h2d⟩ := h2 a h1b hr h1c e
    exact ⟨h2a, h2b, h2c, h1d.trans h2d⟩

theorem M.PreservesGhostRestriction.pure {a : α} {R} (h : R a) : M.PreservesGhostRestriction G (pure a) R := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨rfl, h, hs, .rfl⟩

theorem M.PreservesGhostRestriction.throw {R} : M.PreservesGhostRestriction G (throw e : M α) R := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩

theorem M.PreservesGhostRestriction.getEnv : M.PreservesGhostRestriction G TypeChecker.getEnv fun _ => True := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨by rw [hr.env_eq]; rfl, trivial, hs, .rfl⟩

theorem M.PreservesGhostRestriction.getEnv_ghostFree : M.PreservesGhostRestriction G TypeChecker.getEnv (EnvGhostFree G) := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨by rw [hr.env_eq]; rfl, hr.env_eq ▸ hr.env, hs, .rfl⟩

/-- A read of the context whose continuation does not depend on the local context. -/
theorem M.PreservesGhostRestriction.read {f : Context → M α} {R}
    (hf : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → f c₁ = f c₂)
    (H : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → M.PreservesGhostRestriction G (f c₂) R) :
    M.PreservesGhostRestriction G (MonadReader.read >>= f) R := by
  intro c₁ c₂ s b s' hr hs e
  change f c₁ c₁ s = _ at e
  have : (MonadReader.read >>= f) c₂ s = f c₂ c₂ s := rfl
  rw [this]; rw [hf hr] at e; exact H hr hr hs e

theorem M.PreservesGhostRestriction.get : M.PreservesGhostRestriction G (MonadState.get : M State) (GhostFreeState G) := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨rfl, hs, hs, .rfl⟩

theorem M.PreservesGhostRestriction.modify {f : State → State}
    (hf : ∀ s, GhostFreeState G s → GhostFreeState G (f s) ∧ s.ngen ≤ (f s).ngen) :
    M.PreservesGhostRestriction G (modify f : M Unit) fun _ => True := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨rfl, trivial, (hf s hs).1, (hf s hs).2⟩

theorem M.PreservesGhostRestriction.modifyGet {f : State → β × State}
    (hf : ∀ s, GhostFreeState G s → GhostFreeState G (f s).2 ∧ s.ngen ≤ (f s).2.ngen) :
    M.PreservesGhostRestriction G (modifyGet f : M β) fun _ => True := by
  intro c₁ c₂ s b s' hr hs e
  have h1 : f s = (b, s') := Except.ok.inj e
  have h2 : (f s).2 = s' := by rw [h1]
  exact ⟨e, trivial, h2 ▸ (hf s hs).1, h2 ▸ (hf s hs).2⟩

theorem M.PreservesGhostRestriction.liftExcept {x : Except Exception α} {R} (h : ∀ a, x = .ok a → R a) :
    M.PreservesGhostRestriction G (liftM x : M α) R := by
  intro c₁ c₂ s b s' hr hs e
  cases x with
  | error => cases e
  | ok a => cases e; exact ⟨rfl, h _ rfl, hs, .rfl⟩

/-- A read of the local context at a non-ghost. -/
theorem M.PreservesGhostRestriction.getLCtx_find {id : FVarId} (hid : ¬ G id) {f : LocalContext → M α} {R}
    (hf : ∀ ⦃l₁ l₂ : LocalContext⦄,
      (l₁.find? id).map (·.setIndex 0) = (l₂.find? id).map (·.setIndex 0) → f l₁ = f l₂)
    (H : ∀ l : LocalContext, (∀ ⦃d⦄, l.find? id = some d →
      GhostFree G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GhostFree G v) → M.PreservesGhostRestriction G (f l) R) :
    M.PreservesGhostRestriction G (getLCtx >>= f) R := by
  intro c₁ c₂ s b s' hr hs e
  change f c₁.lctx c₁ s = _ at e
  have : (getLCtx >>= f) c₂ s = f c₂.lctx c₂ s := rfl
  rw [this]
  rw [hf (hr.find? hid)] at e
  exact H _ (fun _ hd => hr.decls hd) hr hs e

/-! ### Binders -/

theorem GhostFreeState.next {s : State} (h : GhostFreeState G s) : GhostFreeState G { s with ngen := s.ngen.next } :=
  { h with reserved := fun _ hg => (h.reserved hg).mono NameGenerator.LE.next }

theorem GhostFreeState.leaveScope {saved s : State} (h₁ : GhostFreeState G saved) (h₂ : GhostFreeState G s) :
    GhostFreeState G (saved.leaveScope s) :=
  { h₁ with unfold := h₂.unfold, reserved := h₂.reserved }

theorem GhostFreeState.exitScope {saved s : State} (h₁ : GhostFreeState G saved)
    (h₂ : GhostFreeState G s) : GhostFreeState G (saved.exitScope mode s) := by
  cases mode <;> [exact h₁.leaveScope h₂; exact h₂]

theorem M.PreservesGhostRestriction.withFreshId {x : Name → M α} {R}
    (H : ∀ (n : Name) (s : State) (c₁ c₂ : Context), GhostRel G c₁ c₂ → GhostFreeState G s →
      ¬ G ⟨n⟩ → ∀ a s', x n c₁ s = .ok (a, s') →
        x n c₂ s = .ok (a, s') ∧ R a ∧ GhostFreeState G s' ∧ s.ngen ≤ s'.ngen) :
    M.PreservesGhostRestriction G (withFreshId x) R := by
  intro c₁ c₂ s b s' hr hs e
  rw [withFreshId_eq] at e ⊢
  have hfresh : ¬ G ⟨s.ngen.curr⟩ := fun hg =>
    NameGenerator.not_reserves_self (hs.reserved hg)
  cases ex : x s.ngen.curr c₁ { s with ngen := s.ngen.next } with
  | error => rw [ex] at e; cases e
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [ex] at e; cases e
    obtain ⟨h1, h2, h3, h4⟩ := H _ _ _ _ hr hs.next hfresh _ _ ex
    rw [h1, hr.ctx_eq.2.2.2.2]
    exact ⟨rfl, h2, hs.exitScope h3, by rw [State.exitScope_ngen]; exact NameGenerator.LE.next.trans h4⟩

theorem M.PreservesGhostRestriction.withLocalDecl {f : Expr → M α} {R} (hty : GhostFree G ty)
    (H : ∀ id, ¬ G id → M.PreservesGhostRestriction G (f (.fvar id)) R) :
    M.PreservesGhostRestriction G (withLocalDecl name bi ty f) R := by
  refine .withFreshId fun n s c₁ c₂ hr hs hn a s' e => ?_
  exact H _ hn (hr.mkLocalDecl hty) hs e

theorem M.PreservesGhostRestriction.withLetDecl {f : Expr → M α} {R} (hty : GhostFree G ty) (hval : GhostFree G val)
    (H : ∀ id, ¬ G id → M.PreservesGhostRestriction G (f (.fvar id)) R) :
    M.PreservesGhostRestriction G (withLetDecl name ty val f) R := by
  refine .withFreshId fun n s c₁ c₂ hr hs hn a s' e => ?_
  exact H _ hn (hr.mkLetDecl hty hval) hs e

theorem M.PreservesGhostRestriction.withEager {x : M α} {R} (h : M.PreservesGhostRestriction G x R) :
    M.PreservesGhostRestriction G (withTheReader Context (fun s => { s with eagerReduce := true }) x) R :=
  fun _ _ _ _ _ hr hs e => h hr.eager hs e

/-! ### `RecM.PreservesGhostRestriction` -/

theorem RecM.PreservesGhostRestriction.bind {x : RecM α} {f : α → RecM β} {P Q}
    (h1 : RecM.PreservesGhostRestriction G x P) (h2 : ∀ a, P a → RecM.PreservesGhostRestriction G (f a) Q) :
    RecM.PreservesGhostRestriction G (x >>= f) Q :=
  fun _ hm => M.PreservesGhostRestriction.bind (h1 hm) fun a ha => h2 a ha hm

theorem RecM.PreservesGhostRestriction.pure {a : α} {R} (h : R a) : RecM.PreservesGhostRestriction G (pure a) R :=
  fun _ _ => .pure h

theorem RecM.PreservesGhostRestriction.throw {R} : RecM.PreservesGhostRestriction G (throw e : RecM α) R := fun _ _ => .throw

theorem RecM.PreservesGhostRestriction.throw_bind {f : α → RecM β} {R} :
    RecM.PreservesGhostRestriction G (MonadExcept.throw e >>= f) R :=
  RecM.PreservesGhostRestriction.bind (P := fun _ => False) .throw nofun

theorem RecM.PreservesGhostRestriction.panic [Inhabited α] {R : α → Prop} (h : R default) :
    RecM.PreservesGhostRestriction G (panicWithPosWithDecl m d l c msg : RecM α) R := by
  simp only [panicWithPosWithDecl]; exact RecM.PreservesGhostRestriction.pure h

theorem RecM.PreservesGhostRestriction.ite {c : Prop} [Decidable c] {x y : RecM α} {R}
    (h1 : RecM.PreservesGhostRestriction G x R) (h2 : RecM.PreservesGhostRestriction G y R) :
    RecM.PreservesGhostRestriction G (if c then x else y) R := by
  split
  · exact h1
  · exact h2

theorem RecM.PreservesGhostRestriction.lift {x : M α} {R} (h : M.PreservesGhostRestriction G x R) : RecM.PreservesGhostRestriction G (liftM x) R :=
  fun _ _ => h

theorem RecM.PreservesGhostRestriction.getEnv : RecM.PreservesGhostRestriction G (liftM TypeChecker.getEnv) fun _ => True := .lift .getEnv

theorem RecM.PreservesGhostRestriction.getEnv_ghostFree : RecM.PreservesGhostRestriction G (liftM TypeChecker.getEnv) (EnvGhostFree G) := .lift .getEnv_ghostFree

theorem RecM.PreservesGhostRestriction.getLCtx_throw {f : LocalContext → Exception} {R} :
    RecM.PreservesGhostRestriction G (getLCtx >>= fun l => (MonadExcept.throw (f l) : RecM α)) R := by
  rintro _ _ c₁ c₂ s b s' hr hs ⟨⟩

theorem RecM.PreservesGhostRestriction.getLCtx_throw_bind {f : LocalContext → Exception}
    {g : LocalContext → α → RecM β} {R} :
    RecM.PreservesGhostRestriction G (getLCtx >>= fun l => (MonadExcept.throw (f l) : RecM α) >>= g l) R := by
  rintro _ _ c₁ c₂ s b s' hr hs ⟨⟩

theorem RecM.PreservesGhostRestriction.read {f : Context → RecM α} {R}
    (hf : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → f c₁ = f c₂)
    (H : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → RecM.PreservesGhostRestriction G (f c₂) R) :
    RecM.PreservesGhostRestriction G (readThe Context >>= f) R :=
  fun m hm => M.PreservesGhostRestriction.read (f := fun c => f c m) (fun _ _ h => by rw [hf h])
    fun _ _ hc => H hc hm

theorem RecM.PreservesGhostRestriction.get : RecM.PreservesGhostRestriction G (MonadState.get : RecM State) (GhostFreeState G) :=
  fun _ _ => .get

theorem RecM.PreservesGhostRestriction.modify {f : State → State}
    (hf : ∀ s, GhostFreeState G s → GhostFreeState G (f s) ∧ s.ngen ≤ (f s).ngen) :
    RecM.PreservesGhostRestriction G (modify f : RecM Unit) fun _ => True := fun _ _ => .modify hf

theorem RecM.PreservesGhostRestriction.modifyGet {f : State → β × State}
    (hf : ∀ s, GhostFreeState G s → GhostFreeState G (f s).2 ∧ s.ngen ≤ (f s).2.ngen) :
    RecM.PreservesGhostRestriction G (modifyGet f : RecM β) fun _ => True := fun _ _ => .modifyGet hf

theorem RecM.PreservesGhostRestriction.liftExcept {x : Except Exception α} {R} (h : ∀ a, x = .ok a → R a) :
    RecM.PreservesGhostRestriction G (liftM x : RecM α) R := fun _ _ => .liftExcept h

theorem RecM.PreservesGhostRestriction.getLCtx_find {id : FVarId} (hid : ¬ G id) {f : LocalContext → RecM α} {R}
    (hf : ∀ ⦃l₁ l₂ : LocalContext⦄,
      (l₁.find? id).map (·.setIndex 0) = (l₂.find? id).map (·.setIndex 0) → f l₁ = f l₂)
    (H : ∀ l : LocalContext, (∀ ⦃d⦄, l.find? id = some d →
      GhostFree G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GhostFree G v) → RecM.PreservesGhostRestriction G (f l) R) :
    RecM.PreservesGhostRestriction G (getLCtx >>= f) R :=
  fun m hm => M.PreservesGhostRestriction.getLCtx_find (f := fun l => f l m) hid
    (fun _ _ h => by rw [hf h]) fun l hl => H l hl hm

theorem RecM.PreservesGhostRestriction.withLocalDecl {f : Expr → RecM α} {R} (hty : GhostFree G ty)
    (H : ∀ id, ¬ G id → RecM.PreservesGhostRestriction G (f (.fvar id)) R) :
    RecM.PreservesGhostRestriction G (withLocalDecl name bi ty f) R :=
  fun m hm => M.PreservesGhostRestriction.withLocalDecl (f := fun e => f e m) hty fun id hid => H id hid hm

theorem RecM.PreservesGhostRestriction.withLetDecl {f : Expr → RecM α} {R} (hty : GhostFree G ty) (hval : GhostFree G val)
    (H : ∀ id, ¬ G id → RecM.PreservesGhostRestriction G (f (.fvar id)) R) :
    RecM.PreservesGhostRestriction G (withLetDecl name ty val f) R :=
  fun m hm => M.PreservesGhostRestriction.withLetDecl (f := fun e => f e m) hty hval fun id hid => H id hid hm

theorem RecM.PreservesGhostRestriction.withEager {x : RecM α} {R} (h : RecM.PreservesGhostRestriction G x R) :
    RecM.PreservesGhostRestriction G (withTheReader Context (fun s => { s with eagerReduce := true }) x) R :=
  fun _ hm => (h hm).withEager

/-! ### Methods -/

theorem RecM.PreservesGhostRestriction.whnf (h : GhostFree G e) : RecM.PreservesGhostRestriction G (Inner.whnf e) (GhostFree G) :=
  fun _ hm => hm.whnf h

theorem RecM.PreservesGhostRestriction.whnfCore (h : GhostFree G e) : RecM.PreservesGhostRestriction G (Inner.whnfCore e cheapProj) (GhostFree G) :=
  fun _ hm => hm.whnfCore cheapProj h

theorem RecM.PreservesGhostRestriction.inferType (h : GhostFree G e) :
    RecM.PreservesGhostRestriction G (Inner.inferType e inferOnly) (GhostFree G) :=
  fun _ hm => hm.inferType inferOnly h

theorem RecM.PreservesGhostRestriction.isDefEqCore (h₁ : GhostFree G t) (h₂ : GhostFree G s) :
    RecM.PreservesGhostRestriction G (Inner.isDefEqCore t s) fun _ => True :=
  fun _ hm => hm.isDefEqCore h₁ h₂

theorem RecM.PreservesGhostRestriction.isDefEq (h₁ : GhostFree G t) (h₂ : GhostFree G s) :
    RecM.PreservesGhostRestriction G (Inner.isDefEq t s) fun _ => True := by
  unfold Inner.isDefEq
  refine (RecM.PreservesGhostRestriction.isDefEqCore h₁ h₂).bind fun r _ => ?_
  split
  · refine RecM.PreservesGhostRestriction.bind (RecM.PreservesGhostRestriction.modify ?_) fun _ _ => .pure trivial
    intro s hs
    exact ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6⟩, .rfl⟩
  · exact .pure trivial

end Lean4Lean.TypeChecker
