import Lean4Lean.Verify.Inductive.Nested.Install.RunView
import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Recursors
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationDataConstructors
import Lean4Lean.Verify.Inductive.Nested.Lowering.Levels
import Lean4Lean.Verify.Inductive.Nested.Restoration.Commutation

/-! # Discharging the non-`whnf` parameter-uniformity inputs of a nested run

For a validated nested run `E`, at the auxiliary heads `E.auxHeads`
(the names of the lowered families after the source families and of their
constructors):

* `NestedRun.auxHeadsFacts`: the auxiliary heads are fresh in
  the source environment (and after the source headers are added), lie in the
  reserved `_nested` namespace, and contain every key of `aux2nested`.
* Ingredients of `RecursorConstruction.ParamUniformDeclarations` (assembled at
  the head set `E.uniformHeads` by `NestedRun.paramUniformDeclarations_of` in
  `Nested/Restoration/Uniform/Whnf.lean`):
  - `RecursorConstruction.paramDecls_paramUniformIn`: the parameters are
    declarations of the source context, translated in the source environment
    where the heads are fresh (`TrExprS.sourceAvoidsFresh`) and only its
    structures are registered
    (`TrExprS.projsRegistered`).
  - `NestedRun.loweredFamilyMappings`: every lowered family
    has a lowering mapping from a pre-lowering family whose constructor types
    are translated in the source-header environment (the source translations
    for the source families, the pre-lowering data `AuxiliaryFamilySources`
    for the auxiliary ones), so
    `ConstructorLowering.Resolved.paramUniformTele` applies
    (`NestedRun.constructorTypesParamUniform`). The family headers are handled
    in `Nested/Restoration/Uniform/Whnf.lean` (`NestedRun.familyType_tr`).
  - `RecursorConstruction.recursorNames_not_mem`: from the
    distinctness of family and recursor names.
* `NestedRun.normalizedTotal_of`: `Restoration.expr` is total
  on every normalized constructor type of the compilation signature. The
  predicate `VExpr.HeadsApplied` (every head occurrence is applied to at least
  `nparams` arguments at `uvars` levels) makes `Restoration.expr` total
  (`VExpr.HeadsApplied.restorationExpr`); it is transported from the arity
  form `Expr.HeadsApplied` of `ParamUniform` along `TrExprS`
  (`Expr.HeadsApplied.trExprS`), applied to the field-telescope replay
  `sourceConstructorIndices_replay` of every unannotated constructor. This is
  the `normalizedTotal` field of `LoweredConstructorsRestore`, used by
  `NestedRun.compilationData_of_tables`. -/

namespace Lean.Expr

open Lean4Lean

/-- `HeadsApplied heads n k e`: every application spine of `e` headed by a constant
`c ∈ heads` has at least `n` arguments and exactly `k` universe levels. This is
the arity content of `ParamUniform`, forgetting which arguments the head occurrence
carries. -/
inductive HeadsApplied (heads : List Name) (n k : Nat) : Expr → Prop
  | occurrence {c : Name} {us : List Level} {args : List Expr} : c ∈ heads → us.length = k →
      n ≤ args.length → (∀ a ∈ args, HeadsApplied heads n k a) →
      HeadsApplied heads n k (mkAppList (.const c us) args)
  | app {f a : Expr} : HeadsApplied heads n k f → HeadsApplied heads n k a →
      HeadsApplied heads n k (.app f a)
  | const {c : Name} {us : List Level} : c ∉ heads → HeadsApplied heads n k (.const c us)
  | bvar (i : Nat) : HeadsApplied heads n k (.bvar i)
  | fvar (fv : FVarId) : HeadsApplied heads n k (.fvar fv)
  | mvar (mv : MVarId) : HeadsApplied heads n k (.mvar mv)
  | sort (u : Level) : HeadsApplied heads n k (.sort u)
  | lit (l : Literal) : HeadsApplied heads n k (.lit l)
  | lam {nm : Name} {t b : Expr} {bi : BinderInfo} :
      HeadsApplied heads n k t → HeadsApplied heads n k b → HeadsApplied heads n k (.lam nm t b bi)
  | forallE {nm : Name} {t b : Expr} {bi : BinderInfo} :
      HeadsApplied heads n k t → HeadsApplied heads n k b → HeadsApplied heads n k (.forallE nm t b bi)
  | letE {nm : Name} {t v b : Expr} {nd : Bool} :
      HeadsApplied heads n k t → HeadsApplied heads n k v → HeadsApplied heads n k b →
      HeadsApplied heads n k (.letE nm t v b nd)
  | mdata {m : MData} {e : Expr} : HeadsApplied heads n k e → HeadsApplied heads n k (.mdata m e)
  | proj {s : Name} {i : Nat} {e : Expr} : HeadsApplied heads n k e →
      HeadsApplied heads n k (.proj s i e)

theorem ParamUniform.headsApplied {heads : List Name} {params : List Expr} {ls : List Level}
    {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, HeadsApplied heads params.length ls.length p) :
    HeadsApplied heads params.length ls.length e := by
  induction H with
  | head hc => exact .occurrence hc rfl (Nat.le_refl _) hp
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

private theorem abstract1_mkAppList (v : FVarId) (d : Nat) (f : Expr) (args : List Expr) :
    abstract1 v (mkAppList f args) d = mkAppList (abstract1 v f d) (args.map (abstract1 v · d)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simp only [mkAppList, List.map_cons]; rw [ih]; rfl

theorem HeadsApplied.abstract1 {heads : List Name} {n k : Nat} {e : Expr}
    (H : HeadsApplied heads n k e) (v : FVarId) (d : Nat) :
    HeadsApplied heads n k (Expr.abstract1 v e d) := by
  induction H generalizing d with
  | @occurrence c us args hc hus hlen _ ih =>
    rw [abstract1_mkAppList]
    refine .occurrence hc hus (by simpa using hlen) fun a ha => ?_
    simp only [List.mem_map] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact ih a ha d
  | app _ _ ihf iha => exact .app (ihf d) (iha d)
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar fv =>
    simp only [Expr.abstract1]; split
    · exact .bvar _
    · exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam (iht d) (ihb (d + 1))
  | forallE _ _ iht ihb => exact .forallE (iht d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht d) (ihv d) (ihb (d + 1))
  | mdata _ ih => exact .mdata (ih d)
  | proj _ ih => exact .proj (ih d)

theorem HeadsApplied.abstractList {heads : List Name} {n k : Nat} {e : Expr}
    (H : HeadsApplied heads n k e) (xs : List FVarId) (d : Nat) :
    HeadsApplied heads n k (Expr.abstractList e xs d) := by
  induction xs generalizing e with
  | nil => simpa using H
  | cons x xs ih => simp only [Expr.abstractList]; exact ih (H.abstract1 x d)

end Lean.Expr

namespace Lean4Lean

open Lean hiding Environment Exception

/-- `HeadsApplied heads n k e`: every occurrence of a constant `c ∈ heads` in
`e` heads an application spine with at least `n` arguments, at exactly `k`
universe levels. On such terms `Restoration.expr` is total. -/
inductive VExpr.HeadsApplied (heads : List Name) (n k : Nat) : VExpr → Prop
  | occurrence {c : Name} {us : List VLevel} {args : List VExpr} : c ∈ heads → us.length = k →
      n ≤ args.length → (∀ a ∈ args, HeadsApplied heads n k a) →
      HeadsApplied heads n k (VExpr.mkApps (.const c us) args)
  | app {f a : VExpr} : HeadsApplied heads n k f → HeadsApplied heads n k a →
      HeadsApplied heads n k (.app f a)
  | const {c : Name} {us : List VLevel} : c ∉ heads → HeadsApplied heads n k (.const c us)
  | bvar (i : Nat) : HeadsApplied heads n k (.bvar i)
  | sort (u : VLevel) : HeadsApplied heads n k (.sort u)
  | elim (b : Name) (o : Nat) (us : List VLevel) : HeadsApplied heads n k (.elim b o us)
  | lam {t b : VExpr} : HeadsApplied heads n k t → HeadsApplied heads n k b →
      HeadsApplied heads n k (.lam t b)
  | forallE {t b : VExpr} : HeadsApplied heads n k t → HeadsApplied heads n k b →
      HeadsApplied heads n k (.forallE t b)
  | proj {s : Name} {i : Nat} {e : VExpr} : HeadsApplied heads n k e →
      HeadsApplied heads n k (.proj s i e)

namespace VExpr.HeadsApplied

variable {heads : List Name} {n k : Nat}

theorem liftN {e : VExpr} (H : HeadsApplied heads n k e) (m j : Nat) :
    HeadsApplied heads n k (e.liftN m j) := by
  induction H generalizing j with
  | @occurrence c us args hc hus hlen _ ih =>
    rw [VExpr.liftN_mkApps]
    refine .occurrence hc hus (by simpa using hlen) fun a ha => ?_
    simp only [List.mem_map] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact ih a ha j
  | app _ _ ihf iha => exact .app (ihf j) (iha j)
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | sort => exact .sort _
  | elim => exact .elim _ _ _
  | lam _ _ iht ihb => exact .lam (iht j) (ihb (j + 1))
  | forallE _ _ iht ihb => exact .forallE (iht j) (ihb (j + 1))
  | proj _ ih => exact .proj (ih j)

theorem mkApps {f : VExpr} {args : List VExpr} (hf : HeadsApplied heads n k f)
    (hargs : ∀ a ∈ args, HeadsApplied heads n k a) :
    HeadsApplied heads n k (VExpr.mkApps f args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a args ih =>
    exact ih (.app hf (hargs a (by simp))) fun b hb => hargs b (by simp [hb])

theorem wrapForalls {doms : List VExpr} {body : VExpr}
    (hdoms : ∀ d ∈ doms, HeadsApplied heads n k d) (hbody : HeadsApplied heads n k body) :
    HeadsApplied heads n k (VExpr.wrapForalls doms body) := by
  induction doms with
  | nil => exact hbody
  | cons d doms ih =>
    exact .forallE (hdoms d (by simp)) (ih fun x hx => hdoms x (by simp [hx]))

theorem of_containsAnyConst {e : VExpr} (h : e.containsAnyConst heads = false) :
    HeadsApplied heads n k e := by
  induction e with
  | bvar => exact .bvar _
  | sort => exact .sort _
  | const c us =>
    refine .const fun hc => ?_
    simp [VExpr.containsAnyConst, hc] at h
  | elim => exact .elim _ _ _
  | app f a ihf iha =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    exact .app (ihf h.1) (iha h.2)
  | proj s i e ih =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    exact .proj (ih h.2)
  | lam t b iht ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    exact .lam (iht h.1) (ihb h.2)
  | forallE t b iht ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    exact .forallE (iht h.1) (ihb h.2)

/-- Application spine of a `VExpr`: head and arguments. -/
def appSpine : VExpr → VExpr × List VExpr
  | .app f a => ((appSpine f).1, (appSpine f).2 ++ [a])
  | e => (e, [])

theorem appSpine_mkApps (f : VExpr) (xs : List VExpr) :
    appSpine (VExpr.mkApps f xs) = ((appSpine f).1, (appSpine f).2 ++ xs) := by
  induction xs generalizing f with
  | nil => simp [VExpr.mkApps]
  | cons x xs ih =>
    show appSpine (VExpr.mkApps (.app f x) xs) = _
    rw [ih]; simp [appSpine]

theorem spine {e : VExpr} (H : HeadsApplied heads n k e) :
    (∀ a ∈ (appSpine e).2, HeadsApplied heads n k a) ∧
      ∀ c us, (appSpine e).1 = .const c us → c ∈ heads →
        us.length = k ∧ n ≤ (appSpine e).2.length := by
  induction H with
  | @occurrence c us args hc hus hlen hargs _ =>
    rw [appSpine_mkApps]
    simp only [appSpine, List.nil_append]
    refine ⟨hargs, fun c' us' h _ => ?_⟩
    cases h; exact ⟨hus, hlen⟩
  | @app f a _ ha ihf _ =>
    simp only [appSpine]
    refine ⟨fun x hx => ?_, fun c us h hc => ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact ihf.1 x hx
      · rw [List.mem_singleton.1 hx]; exact ha
    · obtain ⟨h1, h2⟩ := ihf.2 c us h hc
      exact ⟨h1, by simp; omega⟩
  | const hc =>
    simp only [appSpine]
    refine ⟨by simp, fun c us h hc' => ?_⟩
    cases h; exact absurd hc' hc
  | _ => simp [appSpine]

theorem args_of_mkApps_const {c : Name} {us : List VLevel} {args : List VExpr}
    (H : HeadsApplied heads n k (VExpr.mkApps (.const c us) args)) :
    ∀ a ∈ args, HeadsApplied heads n k a := by
  have := H.spine.1
  rw [appSpine_mkApps] at this
  simpa [appSpine] using this

theorem forallE_inv {A B : VExpr} (H : HeadsApplied heads n k (.forallE A B)) :
    HeadsApplied heads n k A ∧ HeadsApplied heads n k B := by
  generalize he : VExpr.forallE A B = e at H
  cases H with
  | forallE ht hb => cases he; exact ⟨ht, hb⟩
  | occurrence =>
    have := congrArg (fun e => (appSpine e).1) he
    simp [appSpine_mkApps, appSpine] at this
  | _ => cases he

theorem wrapForalls_inv {doms : List VExpr} {body : VExpr}
    (H : HeadsApplied heads n k (VExpr.wrapForalls doms body)) :
    (∀ d ∈ doms, HeadsApplied heads n k d) ∧ HeadsApplied heads n k body := by
  induction doms with
  | nil => exact ⟨by simp, H⟩
  | cons d doms ih =>
    obtain ⟨hd, hrest⟩ := forallE_inv H
    obtain ⟨hdoms, hbody⟩ := ih hrest
    refine ⟨fun x hx => ?_, hbody⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hd
    · exact hdoms x hx

end VExpr.HeadsApplied

/-! ### Totality of restoration -/

private theorem exists_forall₂_of_forall {P : α → β → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ y, P x y) → ∃ ys, List.Forall₂ P l ys
  | [], _ => ⟨[], .nil⟩
  | x :: l, H => by
    obtain ⟨y, hy⟩ := H x (by simp)
    obtain ⟨ys, hys⟩ := exists_forall₂_of_forall (l := l) fun z hz => H z (by simp [hz])
    exact ⟨y :: ys, .cons hy hys⟩

open InductiveSignature in
/-- `Restoration.expr` is total on terms whose head occurrences are fully
applied at the uniform arity of the table. -/
theorem VExpr.HeadsApplied.restorationGo {heads : List Name} {n k : Nat}
    (r : Restoration)
    (hheads : ∀ h ∈ r.heads, h.auxiliary ∈ heads ∧ h.uvars = k ∧ h.nparams = n)
    {e : VExpr} (H : VExpr.HeadsApplied heads n k e) :
    ∀ args, ∃ e', Restoration.expr.go r e args = some e' := by
  induction H with
  | @occurrence c us xs hc hus hlen _ ih =>
    intro args
    obtain ⟨ys, hys⟩ := exists_forall₂_of_forall
      (P := fun x y => Restoration.expr.go r x [] = some y) fun x hx => ih x hx []
    rw [Restoration.expr.go_mkApps r hys]
    have hlenys : xs.length = ys.length := List.Forall₂.length_eq hys
    simp only [Restoration.expr.go]
    split
    · rename_i h hfind
      have hmem := List.mem_of_find?_eq_some hfind
      obtain ⟨-, huv, hnp⟩ := hheads h hmem
      simp only [HeadSpecialization.apply, huv, hnp, hus, List.length_append]
      have : ¬ (ys.length + args.length < n) := by omega
      simp [this]
    · exact ⟨_, rfl⟩
  | @app f a _ _ ihf iha =>
    intro args
    obtain ⟨a', ha'⟩ := iha []
    obtain ⟨e', he'⟩ := ihf (a' :: args)
    exact ⟨e', by simp [Restoration.expr.go, ha', he']⟩
  | @const c us hc =>
    intro args
    simp only [Restoration.expr.go]
    split
    · rename_i h hfind
      have hmem := List.mem_of_find?_eq_some hfind
      have hname : h.auxiliary = c := by simpa using List.find?_some hfind
      exact absurd (hname ▸ (hheads h hmem).1) hc
    · exact ⟨_, rfl⟩
  | bvar => intro args; exact ⟨_, rfl⟩
  | sort => intro args; exact ⟨_, rfl⟩
  | elim => intro args; exact ⟨_, rfl⟩
  | lam _ _ iht ihb =>
    intro args
    obtain ⟨t', ht'⟩ := iht []
    obtain ⟨b', hb'⟩ := ihb []
    exact ⟨VExpr.mkApps (.lam t' b') args, by simp [Restoration.expr.go, ht', hb']⟩
  | forallE _ _ iht ihb =>
    intro args
    obtain ⟨t', ht'⟩ := iht []
    obtain ⟨b', hb'⟩ := ihb []
    exact ⟨VExpr.mkApps (.forallE t' b') args, by simp [Restoration.expr.go, ht', hb']⟩
  | @proj s i _ _ ih =>
    intro args
    obtain ⟨e', he'⟩ := ih []
    exact ⟨VExpr.mkApps (.proj s i e') args, by simp [Restoration.expr.go, he']⟩

open InductiveSignature in
theorem VExpr.HeadsApplied.restorationExpr {heads : List Name} {n k : Nat}
    (r : Restoration)
    (hheads : ∀ h ∈ r.heads, h.auxiliary ∈ heads ∧ h.uvars = k ∧ h.nparams = n)
    {e : VExpr} (H : VExpr.HeadsApplied heads n k e) :
    ∃ e', r.expr e = some e' :=
  H.restorationGo r hheads []

/-! ### Transport along the expression translation -/

section Transport

variable {heads : List Name} {n k : Nat}

theorem VLCtx.find?_headsApplied :
    ∀ {Δ : VLCtx}, (∀ x ∈ Δ, VExpr.HeadsApplied heads n k x.2.value) →
      ∀ {v e A}, Δ.find? v = some (e, A) → VExpr.HeadsApplied heads n k e
  | [], _, _, _, _, h => by simp [VLCtx.find?] at h
  | (ofv, d) :: Δ, hΔ, v, e, A, h => by
    simp only [VLCtx.find?] at h
    split at h
    · cases h; exact hΔ (ofv, d) (by simp)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨e0, A0⟩, h0, rfl, -⟩ := h
      exact (VLCtx.find?_headsApplied (fun x hx => hΔ x (by simp [hx])) h0).liftN _ _

private theorem forall₂_concat {R : α → β → Prop} {a : α} {b : β} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → R a b →
      List.Forall₂ R (l ++ [a]) (r ++ [b])
  | _, _, .nil, h => .cons h .nil
  | _, _, .cons h t, hab => .cons h (forall₂_concat t hab)

theorem TrSyn.mkAppList_const_inv {Us : List Name} {Δ : VLCtx}
    {c : Name} {us : List Level} :
    ∀ {args : List Expr} {e' : VExpr},
      TrSyn Us Δ (Expr.mkAppList (.const c us) args) e' →
      ∃ us' args', e' = VExpr.mkApps (.const c us') args' ∧ us'.length = us.length ∧
        List.Forall₂ (TrSyn Us Δ) args args' := by
  intro args
  obtain ⟨rargs, rfl⟩ : ∃ r : List Expr, args = r.reverse := ⟨args.reverse, by simp⟩
  induction rargs with
  | nil =>
    intro e' H
    cases H with
    | const hus =>
      exact ⟨_, [], rfl, (VerifyInductive.checkPositivityStep.List.mapM_some_length hus).symm, .nil⟩
  | cons a init ih =>
    intro e' H
    rw [List.reverse_cons, Expr.mkAppList_append] at H
    simp only [Expr.mkAppList] at H
    cases H with
    | app Hf Ha =>
      obtain ⟨us', args', rfl, hus, Hargs⟩ := ih Hf
      refine ⟨us', args' ++ [_], ?_, hus,
        by rw [List.reverse_cons]; exact forall₂_concat Hargs Ha⟩
      simp [VExpr.mkApps]

private theorem ctx_cons {Δ : VLCtx}
    (hΔ : ∀ x ∈ Δ, VExpr.HeadsApplied heads n k x.2.value)
    {o : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (hd : VExpr.HeadsApplied heads n k d.value) :
    ∀ x ∈ ((o, d) :: Δ : VLCtx), VExpr.HeadsApplied heads n k x.2.value := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hd
  · exact hΔ x hx

/-- Translation of head-free source syntax is head-applied (heads may still
enter through let-bound values of the context, which are assumed applied). -/
theorem TrSyn.headsApplied_of_avoids {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrSyn Us Δ e e') :
    e.AvoidsConsts heads → (∀ x ∈ Δ, VExpr.HeadsApplied heads n k x.2.value) →
      VExpr.HeadsApplied heads n k e' := by
  induction H with
  | bvar h => exact fun _ hΔ => VLCtx.find?_headsApplied hΔ h
  | fvar h => exact fun _ hΔ => VLCtx.find?_headsApplied hΔ h
  | sort => exact fun _ _ => .sort _
  | const =>
    intro hav _
    cases hav with | const _ _ h => exact .const h
  | app _ _ ihf iha =>
    intro hav hΔ
    cases hav with | app _ _ hf ha => exact .app (ihf hf hΔ) (iha ha hΔ)
  | lam _ _ iht ihb =>
    intro hav hΔ
    cases hav with
    | lam _ _ _ _ ht hb => exact .lam (iht ht hΔ) (ihb hb (ctx_cons hΔ (.bvar 0)))
  | forallE _ _ iht ihb =>
    intro hav hΔ
    cases hav with
    | forallE _ _ _ _ ht hb => exact .forallE (iht ht hΔ) (ihb hb (ctx_cons hΔ (.bvar 0)))
  | letE _ _ _ _ ihv ihb =>
    intro hav hΔ
    cases hav with
    | letE _ _ _ _ _ _ hv hb => exact ihb hb (ctx_cons hΔ (ihv hv hΔ))
  | lit _ ih =>
    intro hav hΔ
    cases hav with | lit _ h => exact ih h hΔ
  | mdata _ ih =>
    intro hav hΔ
    cases hav with | mdata _ _ h => exact ih h hΔ
  | proj _ ih =>
    intro hav hΔ
    cases hav with | proj _ _ _ h => exact .proj (ih h hΔ)

theorem TrExprS.headsApplied_of_avoids {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    e.AvoidsConsts heads → (∀ x ∈ Δ, VExpr.HeadsApplied heads n k x.2.value) →
      VExpr.HeadsApplied heads n k e' := H.toTrSyn.headsApplied_of_avoids

/-- **Transport of head arity along the expression translation.** -/
theorem _root_.Lean.Expr.HeadsApplied.trSyn {Us : List Name}
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads)
    {e : Expr} (H : e.HeadsApplied heads n k) :
    ∀ {Δ : VLCtx} {e' : VExpr}, (∀ x ∈ Δ, VExpr.HeadsApplied heads n k x.2.value) →
      TrSyn Us Δ e e' → VExpr.HeadsApplied heads n k e' := by
  induction H with
  | @occurrence c us args hc hus hlen _ ih =>
    intro Δ e' hΔ Htr
    obtain ⟨us', args', rfl, hus', Hargs⟩ := TrSyn.mkAppList_const_inv Htr
    refine .occurrence hc (hus'.trans hus) (by rw [← List.Forall₂.length_eq Hargs]; exact hlen)
      fun a' ha' => ?_
    obtain ⟨a, ha, Ha⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hargs a' ha'
    exact ih a ha hΔ Ha
  | app _ _ ihf iha =>
    intro Δ e' hΔ Htr
    cases Htr with | app Hf Ha => exact .app (ihf hΔ Hf) (iha hΔ Ha)
  | const hc =>
    intro Δ e' hΔ Htr
    cases Htr with | const => exact .const hc
  | bvar =>
    intro Δ e' hΔ Htr
    cases Htr with | bvar h => exact VLCtx.find?_headsApplied hΔ h
  | fvar =>
    intro Δ e' hΔ Htr
    cases Htr with | fvar h => exact VLCtx.find?_headsApplied hΔ h
  | mvar => intro Δ e' hΔ Htr; cases Htr
  | sort => intro Δ e' hΔ Htr; cases Htr with | sort => exact .sort _
  | lit l =>
    intro Δ e' hΔ Htr
    cases Htr with
    | lit Hl =>
      cases hlit l with | lit _ h => exact TrSyn.headsApplied_of_avoids Hl h hΔ
  | lam _ _ iht ihb =>
    intro Δ e' hΔ Htr
    cases Htr with
    | lam Ht Hb => exact .lam (iht hΔ Ht) (ihb (ctx_cons hΔ (.bvar 0)) Hb)
  | forallE _ _ iht ihb =>
    intro Δ e' hΔ Htr
    cases Htr with
    | forallE Ht Hb => exact .forallE (iht hΔ Ht) (ihb (ctx_cons hΔ (.bvar 0)) Hb)
  | letE _ _ _ _ ihv ihb =>
    intro Δ e' hΔ Htr
    cases Htr with
    | letE _ Hv Hb => exact ihb (ctx_cons (d := .vlet _ _) hΔ (ihv hΔ Hv)) Hb
  | mdata _ ih =>
    intro Δ e' hΔ Htr
    cases Htr with | mdata He => exact ih hΔ He
  | proj _ ih =>
    intro Δ e' hΔ Htr
    cases Htr with
    | proj He => exact .proj (ih hΔ He)

theorem _root_.Lean.Expr.HeadsApplied.trExprS {env : VEnv} {Us : List Name}
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads)
    {e : Expr} (H : e.HeadsApplied heads n k) {Δ : VLCtx} {e' : VExpr}
    (hΔ : ∀ x ∈ Δ, VExpr.HeadsApplied heads n k x.2.value)
    (Htr : TrExprS env Us Δ e e') : VExpr.HeadsApplied heads n k e' :=
  H.trSyn hlit hΔ Htr.toTrSyn

end Transport

/-! ### Names -/

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

private def nameDepth' : Name → Nat
  | .anonymous => 0
  | .str p _ => nameDepth' p + 1
  | .num p _ => nameDepth' p + 1

private theorem NamePrefix.depth_le' {P x : Name} (H : NamePrefix P x) :
    nameDepth' P ≤ nameDepth' x := by
  induction H with
  | refl => exact Nat.le_refl _
  | str _ _ ih => simp only [nameDepth']; omega
  | num _ _ ih => simp only [nameDepth']; omega

theorem NamePrefix.trans {Q A B : Name} (h₁ : NamePrefix Q A) (h₂ : NamePrefix A B) :
    NamePrefix Q B := by
  induction h₂ with
  | refl => exact h₁
  | str s _ ih => exact .str s ih
  | num k _ ih => exact .num k ih

/-- Replacing a prefix `P` of `x` by `A` yields a name with prefix `A`. -/
theorem NamePrefix.replacePrefix_prefix {P x : Name} (H : NamePrefix P x) (A : Name) :
    NamePrefix A (x.replacePrefix P A) := by
  induction H with
  | refl => rw [Name.replacePrefix_self]; exact .refl
  | @str p s H ih =>
    have hne : Name.str p s ≠ P := by
      intro h; have := H.depth_le'; rw [← h] at this; simp [nameDepth'] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkStr]
    exact .str s ih
  | @num p k H ih =>
    have hne : Name.num p k ≠ P := by
      intro h; have := H.depth_le'; rw [← h] at this; simp [nameDepth'] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkNum]
    exact .num k ih

theorem NamePrefix.isPrefixOf {P x : Name} (H : NamePrefix P x) : P.isPrefixOf x = true := by
  induction H with
  | refl => cases P <;> simp [Name.isPrefixOf]
  | str s _ ih => simp [Name.isPrefixOf, ih]
  | num k _ ih => simp [Name.isPrefixOf, ih]

theorem namePrefix_of_isPrefixOf {P : Name} :
    ∀ {x : Name}, P.isPrefixOf x = true → NamePrefix P x
  | .anonymous, h => by
    simp only [Name.isPrefixOf, beq_iff_eq] at h
    subst h; exact .refl
  | .str p s, h => by
    simp only [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .str s (namePrefix_of_isPrefixOf h)
  | .num p k, h => by
    simp only [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .num k (namePrefix_of_isPrefixOf h)

/-! ### Run-level facts about the auxiliary heads -/

/-- **The auxiliary heads of a validated nested run** are fresh in the
source environment (and in the environment extended by the source family
headers), lie in the reserved `_nested` namespace, and contain every key of
the `aux2nested` map of the lowering result. The lowered family and recursor names are
moreover pairwise distinct. -/
theorem NestedRun.auxHeadsFacts
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ envTypes : VEnv,
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      (∀ name ∈ E.auxHeads, envTypes.constants name = none) ∧
      (∀ name ∈ E.auxHeads,
        (ves.venv (if isUnsafe then .unsafe else .safe)).constants name = none) ∧
      (∀ name ∈ E.auxHeads, (`_nested).isPrefixOf name = true) ∧
      (∀ c nested, result.aux2nested.find? c = some nested → c ∈ E.auxHeads) ∧
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoring wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      _hparamsSize, D, _Hrestoring⟩
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hheadNames : auxiliaries.flatMap (·.headNames) = E.auxHeads :=
    auxiliarySpecializations_headNames Haux Hexpansion
  have hfresh : ∀ name ∈ E.auxHeads, envTypes.constants name = none := by
    intro name hname
    apply hfreshAll
    rw [← hheadNames, ← compilationRestoration_heads_auxiliary sourceDecl] at hname
    exact List.mem_append_left _ hname
  rcases E.lowering with ⟨finalState, Hrun, -, -⟩
  have hres := Hrun.resultFamilyNamesReservedOfEmpty rfl
  have hauxRes : ∀ a ∈ auxiliaries, (`_nested).isPrefixOf a.auxiliary = true := by
    intro a ha
    obtain ⟨nested, hfind⟩ := D.familyLookup a ha
    exact hres _ _ hfind
  refine ⟨envTypes, hadded, henvTypes, hfresh,
    fun name hname => (VEnv.addConstVals_le hadded).constants_eq_none_left
      (hfresh name hname), ?_, ?_, hnodup⟩
  · intro name hname
    rw [← hheadNames] at hname
    obtain ⟨a, ha, hn⟩ := List.mem_flatMap.1 hname
    simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨ctor, hctor, rfl⟩
    · exact hauxRes a ha
    · have hP := namePrefix_of_replacePrefix_ne (D.ctorRenamed a ha ctor hctor)
      exact ((namePrefix_of_isPrefixOf (hauxRes a ha)).trans
        (hP.replacePrefix_prefix a.auxiliary)).isPrefixOf
  · intro c nested hfind
    obtain ⟨a, ha, rfl, -⟩ := D.familyKey c nested hfind
    rw [← hheadNames]
    exact List.mem_flatMap.2 ⟨a, ha, by simp [ContainerSpecialization.headNames]⟩

/-! ### Projections in translated syntax -/

/-- Every projection node of translated syntax names a structure registered in
the abstract environment. -/
theorem _root_.Lean4Lean.TrExprS.projsRegistered {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {e' : VExpr} (henv : env.Ordered) (H : TrExprS env Us Δ e e')
    (hΔ : Δ.WF env Us.length) :
    e.ProjsOK (fun s => ∃ info, env.projections s info) := by
  induction H with
  | bvar | fvar | sort | const | lit => trivial
  | app _ _ _ _ ihf iha => exact ⟨ihf hΔ, iha hΔ⟩
  | lam hty _ _ iht ihb => exact ⟨iht hΔ, ihb ⟨hΔ, by rintro _ _ ⟨⟩, hty⟩⟩
  | forallE hty _ _ _ iht ihb => exact ⟨iht hΔ, ihb ⟨hΔ, by rintro _ _ ⟨⟩, hty⟩⟩
  | letE hval _ _ _ iht ihv ihb => exact ⟨iht hΔ, ihv hΔ, ihb ⟨hΔ, by rintro _ _ ⟨⟩, hval⟩⟩
  | mdata _ ih => exact ih hΔ
  | proj _ hproj ih =>
    refine ⟨?_, ih hΔ⟩
    obtain ⟨_, hty⟩ := hproj
    obtain ⟨info, -, -, -, -, -, -, hinfo, -⟩ := VEnv.HasType.proj_inv henv hΔ.toCtx hty
    exact ⟨info, hinfo⟩



/-! ### Generic discharges at a recursor construction -/

section Completed

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

theorem familyNames_drop_subset {types : List VInductiveType} {k : Nat} {name : Name}
    (h : name ∈ familyNames (types.drop k)) : name ∈ familyNames types := by
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 h
  exact List.mem_flatMap.2 ⟨t, List.mem_of_mem_drop ht, hn⟩

theorem RecursorConstruction.indTypeName_eq (H : RecursorConstruction R)
    {i : Nat} (hi : i < decl.types.length) :
    (decl.types[i]'hi).name = indTypes[i]!.name := by
  have hrec : i < H.recInfos.size := by rw [H.recInfos_size_eq]; exact hi
  have hsrc : i < indTypes.size := H.sourceOwner hrec
  have htr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core i
    (by simpa using hsrc) hi
  rw [getElem!_pos indTypes i hsrc]
  simpa using htr.header.name

/-- **Recursor names are not heads**, when the heads are family or
constructor names of the declaration and the family names are distinct from
the recursor names. -/
theorem RecursorConstruction.recursorNames_not_mem
    (H : RecursorConstruction R) {heads : List Name}
    (hheads : ∀ h ∈ heads, h ∈ familyNames decl.types)
    (hnodup : (familyNames decl.types ++
      decl.types.map (fun t => t.name.str "rec")).Nodup) :
    ∀ i, i < stats.indConsts.size → Lean.mkRecName indTypes[i]!.name ∉ heads := by
  intro i hi hmem
  have hrec : i < H.recInfos.size := by
    rw [H.recInfos_size_eq, ← H.validStats.types_size]; exact hi
  have hdecl : i < decl.types.length := by rw [← H.recInfos_size_eq]; exact hrec
  have h2 : Lean.mkRecName indTypes[i]!.name ∈
      decl.types.map (fun t => t.name.str "rec") := by
    rw [← H.indTypeName_eq hdecl]
    exact List.mem_map_of_mem (List.getElem_mem hdecl)
  exact (List.nodup_append.1 hnodup).2.2 _ (hheads _ hmem) _ h2 rfl

/-- Every declaration of a well-formed source context avoids the names that
are fresh in its environment. -/
theorem ContextWF.declAvoids {c : AddInductive.Context} (Hc : ContextWF c)
    {names : List Name} (hfresh : ∀ name ∈ names, Hc.venv.constants name = none)
    {fv : FVarId} {d : LocalDecl} (hfind : c.lctx.find? fv = some d) :
    d.type.AvoidsConsts names ∧ d.value'.AvoidsConsts names := by
  have hfind' : Hc.mlctx.lctx.find? fv = some d := by rw [Hc.lctx_eq]; exact hfind
  rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hfind'
  have hmem : d ∈ Hc.mlctx.lctx.toList := List.mem_of_find?_eq_some hfind'
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hmem with
    ⟨valueTarget, typeTarget, -, -, -, hvalueTr, htypeTr⟩
  exact ⟨checkPositivityStep.TrExprS.sourceAvoidsFresh hfresh htypeTr,
    checkPositivityStep.TrExprS.sourceAvoidsFresh hfresh hvalueTr⟩

/-- Every declaration of a well-formed source context projects only out of
structures registered in its environment. -/
theorem ContextWF.declProjsOK {c : AddInductive.Context} (Hc : ContextWF c)
    {ok : Name → Prop} (hproj : ∀ s info, Hc.venv.projections s info → ok s)
    {fv : FVarId} {d : LocalDecl} (hfind : c.lctx.find? fv = some d) :
    d.type.ProjsOK ok ∧ d.value'.ProjsOK ok := by
  have hfind' : Hc.mlctx.lctx.find? fv = some d := by rw [Hc.lctx_eq]; exact hfind
  rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hfind'
  have hmem : d ∈ Hc.mlctx.lctx.toList := List.mem_of_find?_eq_some hfind'
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hmem with
    ⟨valueTarget, typeTarget, -, -, -, hvalueTr, htypeTr⟩
  have hΔ := Hc.mlctx_wf.tr.wf
  have hord := Hc.checking.tr.wf.ordered
  exact ⟨(htypeTr.projsRegistered hord hΔ).mono fun s ⟨info, h⟩ => hproj s info h,
    (hvalueTr.projsRegistered hord hΔ).mono fun s ⟨info, h⟩ => hproj s info h⟩

/-- **Parameter declarations satisfy `ParamUniformIn`**: they are the source parameter
declarations of the header check, translated before any family of the block
is installed, so they mention no head fresh in the source environment and
project only out of structures registered there. -/
theorem RecursorConstruction.paramDecls_paramUniformIn
    (H : RecursorConstruction R) {env : Environment} {heads : List Name}
    (hfresh : ∀ name ∈ heads, sourceEnv.constants name = none)
    (hproj : ∀ s info, sourceEnv.projections s info → projAvoidsHeads env heads s) :
    ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
      d.ParamUniformIn env heads stats.params.toList stats.levels := by
  intro fv hfv d hfind
  have hparam : Expr.fvar fv ∈ stats.params := H.params.mem_fvars_iff.1 hfv
  have hc : fv ∈ c.lctx.fvars := by
    obtain ⟨fvars, hparams, hdecls⟩ :=
      cachedParameterDecls_fvars R.sourceStatsWF.cachedScope
    have hmem : Expr.fvar fv ∈ stats.params.toList.reverse := by simpa using hparam
    rw [hparams] at hmem
    simp only [List.mem_map, Expr.fvar.injEq, exists_eq_right] at hmem
    rw [← R.sourceContext.lctx_eq, R.sourceContext.mlctx_wf.tr.fvars_eq,
      R.sourceStatsWF.scopeDecomposition, VLCtx.fvars_append, hdecls]
    exact List.mem_append_right _ hmem
  have hfind' : c.lctx.find? fv = some d := by
    rw [← hfind]; exact (H.localExtends.declarations fv hc).symm
  have hfresh' : ∀ name ∈ heads, R.sourceContext.venv.constants name = none := by
    rw [R.sourceContextVEnv]; exact hfresh
  have hproj' : ∀ s info, R.sourceContext.venv.projections s info →
      projAvoidsHeads env heads s := by
    rw [R.sourceContextVEnv]; exact hproj
  obtain ⟨htype, hvalue⟩ := R.sourceContext.declAvoids hfresh' hfind'
  obtain ⟨ptype, pvalue⟩ := R.sourceContext.declProjsOK hproj' hfind'
  refine ⟨⟨Expr.ParamUniform.of_avoidsConsts htype, ptype⟩, fun v hv => ?_⟩
  cases d with
  | cdecl => simp [LocalDecl.value?] at hv
  | ldecl _ _ _ _ val nd _ =>
    have hval : val = v := by cases nd <;> simpa [LocalDecl.value?] using hv
    subst hval
    exact ⟨Expr.ParamUniform.of_avoidsConsts hvalue, pvalue⟩

/-! #### Normalized constructor types -/

theorem abstractForallContext_headsApplied {heads : List Name} {n k : Nat}
    (doms : List VExpr) :
    ∀ x ∈ abstractForallContext doms [], VExpr.HeadsApplied heads n k x.2.value := by
  intro x hx
  simp only [abstractForallContext, List.append_nil, List.mem_map] at hx
  obtain ⟨t, -, rfl⟩ := hx
  exact .bvar 0

/-- The source expression replayed by `sourceConstructorIndices_replay` (the
constructor's field telescope over its checked result, with the parameters
abstracted) is head-applied, given the parameter uniformity of the lowered
constructor types. -/
theorem RecursorConstruction.minorSourceHeadsApplied
    (H : RecursorConstruction R) {heads : List Name}
    (hctorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
      Expr.ParamUniformTele heads stats.params.size stats.levels ctor.type)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    ((H.localContext.lctx.mkForall (H.origins.minorShapes owner howner localIndex hlocal).fields
      (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.terminal).abstractList
        H.params.fvars).HeadsApplied heads stats.params.size stats.levels.length := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hfresh := H.templates.fields_outer_fresh owner howner localIndex hlocal
  generalize H.sourceMinorTyping owner howner localIndex hlocal = HS
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hfresh HS ⊢
  obtain ⟨-, -, hsourceCtors, -, traversal, htrav, hctorEq, hfieldsEq, -, hstatsEq, -, -, -,
    hTL, -⟩ := hsrc
  have hT : HS.semantic.traversal = traversal :=
    Option.some.inj (HS.semantic.traversal_eq.symm.trans htrav)
  have Hroot := HS.semantic.rootWF.toBindingContextWF
  rw [hT] at Hroot
  rw [hT]
  have hp := H.params_fvar
  have Hprefix : ParameterPrefix stats 0 S.constructor.type traversal.parameterTail := by
    have := traversal.parameterPrefix
    rwa [hstatsEq, hctorEq] at this
  have hctorMem : S.constructor ∈ indTypes[owner]!.ctors := by
    rw [← hsourceCtors]; exact List.mem_of_getElem? S.sourceConstructor
  have Htail := Hprefix.paramUniform H.params.expressions
    (hctorTypes owner hsourceOwner _ hctorMem)
  obtain ⟨hterm, hfieldsTerm⟩ := traversal.decisions.paramUniform Hroot hp Htail
  rw [hfieldsEq] at hfieldsTerm
  have Hfor : (H.localContext.lctx.mkForall S.fields traversal.terminal).ParamUniform heads
      stats.params.toList stats.levels := by
    refine Expr.ParamUniform.mkForall_of_disjoint S.fields_bound.expressions hterm ?_ ?_
    · intro p hpm
      obtain ⟨pv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
      refine ⟨pv, rfl, fun hy => hfresh pv hy ?_⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm)))
    · intro y hy
      obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
        hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
      cases hfv
      refine ⟨.cdecl index y name type bi kind, ?_, htype⟩
      rw [hTL.declarations y hmem, hfind]
  have hA := Hfor.headsApplied fun p hpm => by
    obtain ⟨fv, rfl⟩ := hp p hpm
    exact .fvar fv
  simp only [Array.length_toList] at hA
  exact hA.abstractList _ 0

/-- The field domains and result indices selected for an unannotated constructor
are head-applied. -/
theorem RecursorConstruction.minorReplayHeadsApplied
    (H : RecursorConstruction R) {heads : List Name}
    (hctorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
      Expr.ParamUniformTele heads stats.params.size stats.levels ctor.type)
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (∀ d ∈ H.declFieldDomains owner howner localIndex hlocal,
      VExpr.HeadsApplied heads stats.params.size stats.levels.length d) ∧
    ∀ x ∈ H.declConstructorIndices owner howner localIndex hlocal,
      VExpr.HeadsApplied heads stats.params.size stats.levels.length x := by
  have Hrep := (H.sourceConstructorIndices_replay owner howner localIndex hlocal).1
  have hA := (H.minorSourceHeadsApplied hctorTypes owner howner localIndex hlocal).trExprS hlit
    (abstractForallContext_headsApplied _) Hrep
  obtain ⟨hdoms, hres⟩ := VExpr.HeadsApplied.wrapForalls_inv hA
  exact ⟨hdoms, fun x hx =>
    VExpr.HeadsApplied.args_of_mkApps_const hres x (List.mem_append_right _ hx)⟩

/-- The common parameter domains mention no name that is fresh in the source
environment. -/
theorem RecursorConstruction.paramsFree_of_fresh
    (_H : RecursorConstruction R) {heads : List Name}
    (hfresh : ∀ name ∈ heads, sourceEnv.constants name = none) :
    ∀ A ∈ R.parameterScope.toCtx, A.containsAnyConst heads = false := by
  have hwf := R.sourceContext.mlctx_wf.tr.wf
  rw [R.sourceStatsWF.scopeDecomposition, R.sourceParameterScope] at hwf
  have hon := VLCtx.WF.toCtx (VLCtx.WF.append_right hwf)
  have hfresh' : ∀ name ∈ heads, R.sourceContext.venv.constants name = none := by
    rw [R.sourceContextVEnv]; exact hfresh
  exact VEnv.Ordered.ctxNoFreshConsts R.sourceContext.checking.tr.wf.ordered hfresh' hon

/-- **Every normalized constructor type of the construction's signature
is head-applied** at the parameter count and universe arity of the
construction. -/
theorem RecursorConstruction.normalizedHeadsApplied
    (H : RecursorConstruction R) {heads : List Name}
    (hctorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
      Expr.ParamUniformTele heads stats.params.size stats.levels ctor.type)
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads)
    (hparamsFree : ∀ A ∈ R.parameterScope.toCtx, A.containsAnyConst heads = false) :
    ∀ normalized ∈ H.generator.signature.declaration.types,
      ∀ ctor ∈ normalized.ctors,
        VExpr.HeadsApplied heads stats.params.size stats.levels.length ctor.type := by
  intro normalized hnorm ctor hctor
  simp only [InductiveSignature.declaration, List.mem_map] at hnorm
  obtain ⟨⟨fam, i⟩, -, rfl⟩ := hnorm
  simp only [List.mem_filterMap] at hctor
  obtain ⟨cc, hcc, hsome⟩ := hctor
  split at hsome
  case isFalse => cases hsome
  cases hsome
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcc
  have hk' : k < decl.ownedConstructors.length := by
    rw [← H.generator.constructorCount]; simpa using hk
  obtain ⟨owner, howner, localIndex, hlocal, hkeq⟩ := H.flatMinorIndex k hk'
  obtain ⟨index, hidx, -, hft, hind, -⟩ :=
    H.generator.sourceOrigins owner howner localIndex hlocal
  have hindex : index = ⟨k, by simpa using hk⟩ := Fin.ext (hidx.trans hkeq.symm)
  subst hindex
  have hget : H.generator.signature.constructors.toList[k] =
      H.generator.signature.constructors[(⟨k, by simpa using hk⟩ : Fin _)] := by
    simp
  rw [hget]
  obtain ⟨hfields, hindices⟩ :=
    H.minorReplayHeadsApplied hctorTypes hlit owner howner localIndex hlocal
  have hsu : H.generator.signature.uvars = decl.uvars := by
    rw [H.generatedBy_signature]
  have hsp : H.generator.signature.params.length = stats.params.size := by
    rw [H.generator.params, List.length_reverse, H.sourceParameterCount]
  have hlevels : stats.levels.length = decl.uvars := R.sourceStatsWF.levels
  simp only [InductiveSignature.constructorType, InductiveSignature.familyApp]
  refine VExpr.HeadsApplied.wrapForalls (fun d hd => ?_) ?_
  · rcases List.mem_append.1 hd with hd | hd
    · rw [H.generator.params, List.mem_reverse] at hd
      exact .of_containsAnyConst (hparamsFree d hd)
    · rw [hft] at hd
      exact hfields d hd
  · have hargs : ∀ a ∈ InductiveSignature.vars H.generator.signature.params.length
        (H.generator.signature.constructors[(⟨k, by simpa using hk⟩ : Fin _)]).fields.length ++
        (H.generator.signature.constructors[(⟨k, by simpa using hk⟩ : Fin _)]).indices,
        VExpr.HeadsApplied heads stats.params.size stats.levels.length a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · simp only [InductiveSignature.vars, List.mem_map] at ha
        obtain ⟨_, _, rfl⟩ := ha
        exact .bvar _
      · rw [hind] at ha
        exact hindices a ha
    by_cases hname : (H.generator.signature.families[
        (H.generator.signature.constructors[(⟨k, by simpa using hk⟩ : Fin _)]).owner]).name
        ∈ heads
    · refine .occurrence hname (by simp [VLevel.params, hsu, hlevels]) ?_ hargs
      simp [InductiveSignature.vars, hsp]
    · exact .mkApps (.const hname) hargs

end Completed

/-! ### Lowered constructor types of a run -/

theorem ConstructorLowerings.Resolved.forall_mem
    {env : Environment} {params : Array Expr} {nparams : Nat}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {sources : List Constructor} {state : Lean4Lean.ElimNestedInductive.State}
    {out : List Constructor × Lean4Lean.ElimNestedInductive.State}
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources state out) :
    ∀ t ∈ out.1, ∃ source ∈ sources, ∃ before after,
      before.lvls = state.lvls ∧
      ConstructorLowering.Resolved env params nparams finalResult source before (t, after) := by
  induction H with
  | nil => intro t ht; simp at ht
  | @cons source state step sources out Hhead Htail ih =>
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨source, List.mem_cons_self, state, step.2, rfl, Hhead⟩
    · obtain ⟨src, hsrc, before, after, hlv, M⟩ := ih t ht
      exact ⟨src, List.mem_cons_of_mem _ hsrc, before, after, hlv.trans Hhead.lvls, M⟩

/-- **Every lowered family of a validated nested run has a lowering
mapping from a pre-lowering family whose constructor types avoid the
auxiliary heads**, at a state carrying the declaration's universe levels.
Source families use the checked source translations; auxiliary families use
the pre-lowering data of the run (`AuxiliaryFamilySources`),
whose constructor types are translated in the environment of the source
headers, where the auxiliary names are fresh. -/
theorem NestedRun.loweredFamilyMappings
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ i (hi : i < result.types.length), ∃ source stepState loweredState,
      (∀ ctor ∈ source.ctors, ctor.type.AvoidsConsts E.auxHeads) ∧
      source.type.AvoidsConsts E.auxHeads ∧
      stepState.lvls = lparams.map Level.param ∧
      FamilyLowering.Resolved sourceProdEnv result.params nparams result source stepState
        (result.types[i], loweredState) := by
  obtain ⟨envTypes, hadded, _henvTypes, hfreshTypes, hfreshSrc, _hreserved, _hkeys,
    _hnodup⟩ := E.auxHeadsFacts wf Hsources
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : P.nparams = nparams := E.lowered_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  let initialState := E.initialState
  have Hlower : NestedLoweringOutputClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hpack := E.phases
  let R := Hpack.constructors
  let Hprod := Hpack.recursors
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.sourceCoreDecl_eq] using E.sourceCore.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hpack.headers.context.venv
        R.declared.venvCtors := R.core
  have wfP : ves.WF P.c.env := by
    simpa only [henv] using wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.sourceCore.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    simpa only [hinitial, safety] using E.sourceCore.sourceAdded
  have HbaseWF : P.initialEnv.WF := by
    simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource HbaseWF
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := rfl
  rcases Hrun.auxiliaryFamilySources Hcache Hparams wfP
      hinitial HcP Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, -⟩
  have HsourceCore := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at HsourceCore
  have htypesEq : E.sourceCore.envTypes = envTypes :=
    Option.some.inj (HsourceCore.typesAdded.symm.trans hadded)
  have hfreshN : ∀ name ∈ E.auxHeads, E.sourceCore.envTypes.constants name = none := by
    rw [htypesEq]; exact hfreshTypes
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  have hinitLvls : initialState.lvls = lparams.map Level.param := by
    simp only [initialState, NestedRun.initialState, E.lowered_lparams]
  have hfreshInit : ∀ name ∈ E.auxHeads, P.initialEnv.constants name = none := by
    rw [hinitial]; exact hfreshSrc
  suffices key : ∀ i (hi : i < result.types.length), ∃ source stepState loweredState,
      (∀ ctor ∈ source.ctors, ctor.type.AvoidsConsts E.auxHeads) ∧
      source.type.AvoidsConsts E.auxHeads ∧
      stepState.lvls = lparams.map Level.param ∧
      FamilyLowering.Resolved P.c.env result.params P.nparams result source stepState
        (result.types[i], loweredState) by
    intro i hi
    obtain ⟨source, st, ls, h1, h0, h2, M⟩ := key i hi
    rw [henv, hnparams] at M
    exact ⟨source, st, ls, h1, h0, h2, M⟩
  intro i hi
  by_cases hsrc : i < sourceTypes.length
  · have hj : i < ({ initialState with newTypes := sourceTypes.toArray }).newTypes.size := by
      simpa using hsrc
    rcases Hrun.resolvedMappingAtInitialAlignedLvls
        (Hrun.resultNamesNodupOfEmpty (by simpa using hempty)) hj with
      ⟨params, stepState, target, loweredState, hresultParams,
        _hsize, Hmapping, htarget, hstepLvls⟩
    subst hresultParams
    have htargetEq : target = result.types[i] := by
      rw [List.getElem?_eq_getElem hi] at htarget
      exact (Option.some.inj htarget).symm
    subst htargetEq
    have hsrcDecl : i < sourceDecl.types.length := by
      rw [← TrInductDeclCore.types_length Hsource]; exact hsrc
    have HT := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource i hsrc hsrcDecl
    refine ⟨_, stepState, loweredState, ?_,
      checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshInit HT.header.type,
      hstepLvls.trans hinitLvls, Hmapping⟩
    intro ctor hctor
    have hctor' : ctor ∈ sourceTypes[i].ctors := by simpa using hctor
    obtain ⟨ctor', -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT.ctors ctor hctor'
    exact checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshN hC.type
  · have hge : sourceTypes.length ≤ i := Nat.le_of_not_gt hsrc
    obtain ⟨k, rfl⟩ : ∃ k, i = sourceTypes.length + k := ⟨i - sourceTypes.length, by omega⟩
    have hgeneratedLength := N.length
    have hgen : k < N.generated.length := by omega
    have htarget : sourceTypes.length + k < P.loweredDecl.types.length := by omega
    rcases N.sourceAt k hgen hi htarget with ⟨Horigin, Nsource, -⟩
    have Hmap := Hrun.resultAuxMapModelsOfEmpty (by simpa using hempty)
    have M := Horigin.lowered.resolvedMapping Horigin.later Hmap
    have hlv : Horigin.stepState.lvls = lparams.map Level.param :=
      ((Horigin.lowered.nestedAuxLE.lvls.symm.trans Horigin.later.lvls.symm).trans
        Hrun.lvls).trans hinitLvls
    refine ⟨Horigin.source, Horigin.stepState, Horigin.loweredState, ?_,
      checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshInit
        Nsource.translation.header.type, hlv, M⟩
    intro ctor hctor
    obtain ⟨ctor', -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      Nsource.translation.ctors ctor hctor
    exact checkPositivityStep.TrExprS.sourceAvoidsFresh hfreshN hC.type

/-- **Lowered constructor types of a validated nested run are parameter-uniform
parameter telescopes** for the auxiliary heads, at the lowered run's
parameter count and levels. -/
theorem NestedRun.constructorTypesParamUniform
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ i, i < E.lowered.indTypes.size → ∀ ctor ∈ E.lowered.indTypes[i]!.ctors,
      Expr.ParamUniformTele E.auxHeads E.lowered.stats.params.size
        E.lowered.stats.levels ctor.type := by
  obtain ⟨-, -, -, -, -, -, hkeys, -⟩ := E.auxHeadsFacts wf Hsources
  have hmaps := E.loweredFamilyMappings wf Hsources
  have hnp : result.nparams = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    exact Hrun.resultNParams
  rw [E.lowered_indTypes, E.statsLevels, E.statsParamsSize, hnp]
  intro i hi ctor hctor
  have hi' : i < result.types.length := by simpa using hi
  have hget : result.types.toArray[i]! = result.types[i] := by
    simp [getElem!_pos result.types.toArray i hi]
  rw [hget] at hctor
  obtain ⟨source, st, ls, havoid, -, hlv, M⟩ := hmaps i hi'
  obtain ⟨src, hsrc, before, after, hbefore, Mc⟩ := M.constructors.forall_mem ctor hctor
  exact Mc.paramUniformTele hkeys (havoid src hsrc) (hbefore.trans hlv)

/-! ### Totality of restoration on the normalized constructor types -/

/-- **Restoration is total on the normalized constructor types of a
validated nested run** (source and auxiliary families alike), for every
specialisation list whose head names are the run's auxiliary family and
constructor names. This gives the `normalizedTotal` field of
`LoweredConstructorsRestore` (used by `NestedRun.compilationData_of_tables`). -/
theorem NestedRun.normalizedTotal_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (hheadNames : auxiliaries.flatMap (·.headNames) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)) :
    ∀ normalized ∈ E.lowered.signature.declaration.types,
      ∀ ctor ∈ normalized.ctors, ∃ restored,
        (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored := by
  obtain ⟨-, -, -, -, hfreshSrc, hreserved, -, -⟩ := E.auxHeadsFacts wf Hsources
  have hfresh : ∀ name ∈ E.auxHeads, E.lowered.initialEnv.constants name = none := by
    rw [E.lowered_initialEnv]; exact hfreshSrc
  have hN := E.lowered.recursorConstruction.normalizedHeadsApplied
    (E.constructorTypesParamUniform wf Hsources)
    (fun l => avoidsConsts_lit_of_reserved hreserved l)
    (E.lowered.recursorConstruction.paramsFree_of_fresh hfresh)
  have Hsource := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at Hsource
  have hnp : E.lowered.stats.params.size = sourceDecl.nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    rw [E.statsParamsSize, Hrun.resultNParams, Hsource.nparams]
  have hlv : E.lowered.stats.levels.length = sourceDecl.uvars := by
    rw [E.statsLevels, List.length_map, Hsource.uvars]
  have hheads : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.auxiliary ∈ E.auxHeads ∧ h.uvars = sourceDecl.uvars ∧
        h.nparams = sourceDecl.nparams := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.1 hh
    obtain ⟨hu, hn, -, -⟩ := ContainerSpecialization.mem_heads hh
    refine ⟨?_, hu, hn⟩
    show h.auxiliary ∈ familyNames _
    rw [← hheadNames]
    refine List.mem_flatMap.2 ⟨a, ha, ?_⟩
    rw [← ContainerSpecialization.heads_map_auxiliary a sourceDecl.uvars sourceDecl.nparams]
    exact List.mem_map_of_mem hh
  intro normalized hn ctor hc
  have hA := hN normalized hn ctor hc
  rw [hnp, hlv] at hA
  exact hA.restorationExpr _ hheads

end VerifyInductive

end Lean4Lean
