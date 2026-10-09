import Lean4Lean.Theory.Typing.Strengthening.Exposure

/-! # Typing strengthening: spine exposure and the projection closure

The projection analogue of `Exposure.lean`.

* An eta chain above from the lift of a type into a constant spine starts at a constant spine with
  the same head and levels (`EtaChain.const_spine_inv`), so the replay obligation `EtaReplay`
  gives reduction-form spine exposure (`SpineExposureRedN`, `spineExposureRed_of_etaReplay`).
* Above, a type convertible to a rigid type-former spine reduces to a spine with the same head
  (`spine_exposure_reduces`): through Church-Rosser, the reduct of the spine is an `EtaSpine`
  (head, applications, lambdas), preserved by `FullStep` because no node of a type former's spine
  is structure-typed, and a sort-typed eta spine beta-reduces back to a syntactic spine;
  `NormalEqN.spine_expose` transfers the exposure across the join.
* `ProjFrontN.of_spineExposure`: the projection closure from spine exposure and the field-type
  closure `ProjFieldFrontN`; `ProjFrontN.of_etaReplay`.
* `projField_of_neverZero`: outside `Prop` every projection of a typed major is typable, so the
  field-type closure reduces to its instances at structures whose sort at the given levels is not
  never-zero (`ProjFieldFrontPropN`, `ProjFieldFrontN.of_notNeverZero`). -/

namespace Lean4Lean.VEnv.StrengtheningSpineExposure
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr} {A B F T e f a x : VExpr}
  {S : Name} {ls : List VLevel} {args : List VExpr}

section
open VEnv.Params
variable [VEnv.Params]

/-- A term typed at a sort or at a `Π`: the typing status of every node on the spine of a
type. -/
def TypeLike (Γ : List VExpr) (x : VExpr) : Prop :=
  (∃ u, Params.env.HasType univs Γ x (.sort u)) ∨
    ∃ A B, Params.env.HasType univs Γ x (.forallE A B)

theorem TypeLike.app_inv (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : TypeLike Γ (.app f a)) :
    TypeLike Γ f := by
  rcases H with ⟨u, h⟩ | ⟨A, B, h⟩
  · obtain ⟨A, B, hf, _⟩ := h.app_inv henv.ordered hΓ
    exact .inr ⟨A, B, hf⟩
  · obtain ⟨A, B, hf, _⟩ := h.app_inv henv.ordered hΓ
    exact .inr ⟨A, B, hf⟩

/-- A type-like term is not typed at a structure type. -/
theorem TypeLike.not_struct (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : TypeLike Γ x)
    (hi : Params.env.projections family info)
    (hs : Params.env.HasType univs Γ x (mkApps (.const family ls) args)) : False := by
  rcases H with ⟨u, h⟩ | ⟨A, B, h⟩
  · exact type_not_structure hΓ h hi hs
  · obtain ⟨w, hw⟩ := hs.isType henv.ordered hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hw (hs.uniqU henv hΓ h)

/-- A parallel eta expansion into a constant spine comes from a constant spine, at every
type-like node: `funEta` produces a lambda and `structEta` needs a structure-typed subject. -/
theorem EtaPar.const_spine_inv_r (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {args : List VExpr} {x : VExpr}, EtaPar Γ x (mkApps (.const S ls) args) → TypeLike Γ x →
      ∃ args₀, x = mkApps (.const S ls) args₀ := by
  intro args
  induction args using List.snoc_induction with
  | nil =>
    intro x H hx
    generalize he : mkApps (.const S ls) [] = r at H
    cases H with
    | const => cases he; exact ⟨[], rfl⟩
    | structEta _ _ _ hi _ _ hs _ => exact (hx.not_struct hΓ hi hs).elim
    | _ => cases he
  | snoc args a ih =>
    intro x H hx
    generalize he : mkApps (.const S ls) (args ++ [a]) = r at H
    rw [mkApps_snoc] at he
    cases H with
    | app hf ha =>
      cases he
      obtain ⟨args₀, rfl⟩ := ih hf (hx.app_inv hΓ)
      exact ⟨args₀ ++ [_], (mkApps_snoc ..).symm⟩
    | structEta _ _ _ hi _ _ hs _ => exact (hx.not_struct hΓ hi hs).elim
    | _ => cases he

/-- An eta chain from a type into a constant spine starts at a constant spine with the same
head and levels. -/
theorem EtaChain.const_spine_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaChain Γ x (mkApps (.const S ls) args))
    (hx : Params.env.HasType univs Γ x (.sort u)) :
    ∃ args₀, x = mkApps (.const S ls) args₀ := by
  generalize hr : mkApps (.const S ls) args = r at H
  induction H generalizing args with
  | rfl => exact ⟨_, hr.symm⟩
  | tail hchain hstep ih =>
    subst hr
    obtain ⟨args₁, rfl⟩ :=
      EtaPar.const_spine_inv_r hΓ hstep (.inl ⟨_, EtaChain.hasType hΓ hchain hx⟩)
    exact ih rfl

end

/-- Existential spine exposure in reduction form: a type of `Γ`, inhabited in `Γ`, whose lift
reduces above to a constant spine, reduces below to a spine with the same head and levels. -/
def SpineExposureRedN {E : VEnv} (hE : E.WF) : Prop :=
  ∀ ⦃U k Γ Γ' f F u S ls args⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (E.IsType U) →
    OnCtx Γ' (E.IsType U) → E.HasType U Γ f F → E.HasType U Γ F (.sort u) →
    (letI := hE.params U; FullReduction Γ' (F.liftN 1 k) (mkApps (.const S ls) args)) →
    ∃ args₀, letI := hE.params U; FullReduction Γ F (mkApps (.const S ls) args₀)

/-- Reduction-form spine exposure from the replay obligation (`piExposureRed_of_etaReplay` with
the spine inversion of eta chains in place of the `Π` inversion). -/
theorem spineExposureRed_of_etaReplay (henv : env.WF)
    (H : ∀ U, @EtaReplay (henv.params U)) : SpineExposureRedN henv := by
  intro U k Γ Γ' f F u S ls args W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', hred, hchain⟩ := path_replay (H U) W hΓ hΓ' hF (FullReduction.upSteps hr)
  have hF' : env.HasType U Γ' (F'.liftN 1 k) (.sort u) :=
    (hred.hasType hΓ hF).weakN henv.ordered W
  obtain ⟨args₁, hsp⟩ := EtaChain.const_spine_inv hΓ' hchain hF'
  obtain ⟨args₀, rfl, -⟩ := liftN_eq_mkApps_const_inv hsp
  exact ⟨args₀, hred⟩


/-! ## Rigid spines under reduction

A sort-typed spine `S a₁ … aₙ` of a rigid constant `S` reduces only inside its arguments, by
eta expansion of its partial applications (`S a ↦ λ x. S a x`) and by beta steps undoing them.
`EtaSpine` is the closure of these shapes; it is preserved by `FullStep` when `S` is a type
former (so `structEta` never applies to a node), and a sort-typed `EtaSpine` reduces back to a
syntactic spine by beta. -/

/-- The constant `S` at levels `ls` is a type former: every application of it is typed at a
`Π`-telescope ending in a sort. -/
def TypeFormerHead (E : VEnv) (U : Nat) (S : Name) (ls : List VLevel) : Prop :=
  ∀ ⦃Γ args T⦄, OnCtx Γ (E.IsType U) → E.HasType U Γ (mkApps (.const S ls) args) T →
    ∃ ds w, E.IsDefEqU U Γ T (wrapForalls ds (.sort w))

theorem mkApps_head_typed (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {fn T : VExpr}, env.HasType U Γ (mkApps fn args) T →
      ∃ T', env.HasType U Γ fn T'
  | [], _, _, h => ⟨_, h⟩
  | _ :: _, fn, _, h => by
    obtain ⟨_, h⟩ := mkApps_head_typed henv hΓ (fn := .app fn _) h
    obtain ⟨_, _, hf, _⟩ := h.app_inv henv hΓ
    exact ⟨_, hf⟩

theorem mkApps_append' (fn : VExpr) (l₁ l₂ : List VExpr) :
    mkApps fn (l₁ ++ l₂) = mkApps (mkApps fn l₁) l₂ := by
  simp [mkApps, List.foldl_append]

theorem instOuter_wrapForalls_sort (w : VLevel) :
    ∀ (as ds : List VExpr), ∃ ds', (wrapForalls ds (.sort w)).instOuter as = wrapForalls ds' (.sort w)
  | [], ds => ⟨ds, rfl⟩
  | a :: as, ds => by
    rw [instOuter_cons, wrapForalls_inst]
    exact instOuter_wrapForalls_sort w as _

/-- A constant whose type is a `Π`-telescope ending in a sort is a type former. -/
theorem TypeFormerHead.of_telescope (henv : env.WF) {D : List VExpr} {w : VLevel}
    (hconst : env.HasType U [] (.const S ls) (wrapForalls D (.sort w))) :
    TypeFormerHead env U S ls := by
  intro Γ args T hΓ ht
  have hc : env.HasType U Γ (.const S ls) (wrapForalls D (.sort w)) := hconst.weak0 henv.ordered
  rcases Nat.lt_or_ge D.length args.length with hlt | hle
  · exfalso
    obtain ⟨args₁, args₂, rfl, hlen⟩ : ∃ l₁ l₂, args = l₁ ++ l₂ ∧ l₁.length = D.length :=
      ⟨args.take D.length, args.drop D.length, (List.take_append_drop _ _).symm,
        List.length_take_of_le (Nat.le_of_lt hlt)⟩
    rw [mkApps_append'] at ht
    have hfull := (HasType.mkApps_wrapForalls henv hΓ hc
      (mkApps_head_typed henv.ordered hΓ ht |>.elim fun _ h => ⟨_, h⟩) hlen).2
    rw [instOuter_sort] at hfull
    cases args₂ with
    | nil => simp [hlen] at hlt
    | cons a rest =>
      obtain ⟨_, happ⟩ := mkApps_head_typed henv.ordered hΓ (fn := .app _ a) ht
      obtain ⟨A, B, hf, _⟩ := happ.app_inv henv.ordered hΓ
      exact IsDefEqU.sort_forallE_inv henv hΓ (hfull.uniqU henv hΓ hf)
  · have hsplit : wrapForalls D (.sort w) =
        wrapForalls (D.take args.length) (wrapForalls (D.drop args.length) (.sort w)) := by
      rw [← wrapForalls_append, List.take_append_drop]
    rw [hsplit] at hc
    have hlen : args.length = (D.take args.length).length := by
      rw [List.length_take_of_le hle]
    have h := (HasType.mkApps_wrapForalls henv hΓ hc ⟨_, ht⟩ hlen).2
    obtain ⟨ds', hds'⟩ := instOuter_wrapForalls_sort w args (D.drop args.length)
    rw [hds'] at h
    exact ⟨_, _, ht.uniqU henv hΓ h⟩

section
open VEnv.Params
variable [VEnv.Params]

/-- The shapes a constant spine takes under reduction: the head, applications and lambdas
(eta expansions and their beta contractions). The index is the number of nodes above the
head; substitution and lifting preserve it. -/
inductive EtaSpine (S : Name) (ls : List VLevel) : Nat → VExpr → Prop where
  | head : EtaSpine S ls 0 (.const S ls)
  | app {n : Nat} {g b : VExpr} : EtaSpine S ls n g → EtaSpine S ls (n + 1) (.app g b)
  | lam {n : Nat} {D b : VExpr} : EtaSpine S ls n b → EtaSpine S ls (n + 1) (.lam D b)

omit [VEnv.Params] in
theorem EtaSpine.of_spine :
    ∀ args : List VExpr, EtaSpine S ls args.length (mkApps (.const S ls) args) := by
  intro args
  induction args using List.snoc_induction with
  | nil => exact .head
  | snoc args a ih => rw [mkApps_snoc]; simpa using ih.app (b := a)

omit [VEnv.Params] in
theorem EtaSpine.inst : ∀ {n : Nat} {x : VExpr}, EtaSpine S ls n x → ∀ (a : VExpr) (k : Nat),
    EtaSpine S ls n (x.inst a k)
  | _, _, .head, _, _ => .head
  | _, _, .app h, a, k => .app (h.inst a k)
  | _, _, .lam h, a, k => .lam (h.inst a (k + 1))

omit [VEnv.Params] in
theorem EtaSpine.liftN : ∀ {n : Nat} {x : VExpr}, EtaSpine S ls n x → ∀ (m k : Nat),
    EtaSpine S ls n (x.liftN m k)
  | _, _, .head, _, _ => .head
  | _, _, .app h, m, k => .app (h.liftN m k)
  | _, _, .lam h, m, k => .lam (h.liftN m (k + 1))

omit [VEnv.Params] in
theorem EtaSpine.lift {n : Nat} (H : EtaSpine S ls n x) : EtaSpine S ls n x.lift :=
  H.liftN 1 0

omit [VEnv.Params] in
theorem EtaSpine.head_cases {n : Nat} (H : EtaSpine S ls n x) :
    x.getAppFnArgs.1 = .const S ls ∨ ∃ A b, x.getAppFnArgs.1 = .lam A b := by
  induction H with
  | head => exact .inl rfl
  | app _ ih => rwa [case_spine_app]
  | lam => exact .inr ⟨_, _, rfl⟩

omit [VEnv.Params] in
theorem EtaSpine.lam_inv {n : Nat} (H : EtaSpine S ls n (.lam A b)) : ∃ m, EtaSpine S ls m b := by
  cases H with
  | lam h => exact ⟨_, h⟩

/-- Every node of an eta spine of a type former is typed at a `Π`-telescope ending in a
sort. -/
theorem EtaSpine.typeFormer (hS : TypeFormerHead Params.env univs S ls) :
    ∀ {n : Nat} {x : VExpr} {Γ : List VExpr} {T : VExpr}, EtaSpine S ls n x →
      OnCtx Γ (Params.env.IsType univs) → Params.env.HasType univs Γ x T →
      ∃ ds w, Params.env.IsDefEqU univs Γ T (wrapForalls ds (.sort w))
  | _, _, _, _, .head, hΓ, hx => hS hΓ (args := []) hx
  | _, _, Γ, T, .app hf, hΓ, hx => by
    obtain ⟨A, B, hf', ha⟩ := hx.app_inv henv.ordered hΓ
    obtain ⟨ds, w, hd⟩ := EtaSpine.typeFormer hS hf hΓ hf'
    cases ds with
    | nil => exact (IsDefEqU.sort_forallE_inv henv hΓ hd.symm).elim
    | cons d ds =>
      obtain ⟨-, v, hB⟩ := hd.forallE_inv henv hΓ
      change Params.env.IsDefEq univs (A :: Γ) B (wrapForalls ds (.sort w)) (.sort v) at hB
      have hBa := hB.instN henv.ordered ha .zero
      rw [wrapForalls_inst] at hBa
      exact ⟨_, w, ((hf'.app ha).uniqU henv hΓ hx).symm.trans henv hΓ ⟨_, hBa⟩⟩
  | _, _, Γ, T, .lam hb, hΓ, hx => by
    obtain ⟨B, hPi, hb'⟩ := hx.lam_inv_forallE henv hΓ
    obtain ⟨⟨u, hA⟩, _⟩ := hx.lam_inv henv.ordered hΓ
    have hΓA : OnCtx (_ :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨ds, w, hd⟩ := EtaSpine.typeFormer hS hb hΓA hb'
    obtain ⟨v, hBs⟩ := hb'.isType henv.ordered hΓA
    refine ⟨_ :: ds, w, hPi.symm.trans henv hΓ ⟨_, IsDefEq.forallEDF hA (hd.of_l henv hΓA hBs)⟩⟩

/-- No node of an eta spine of a type former is structure-typed. -/
theorem EtaSpine.not_struct (hS : TypeFormerHead Params.env univs S ls) {n : Nat}
    (hx : EtaSpine S ls n x) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hi : Params.env.projections family info)
    (hs : Params.env.HasType univs Γ x (mkApps (.const family levels) params)) : False := by
  obtain ⟨ds, w, hd⟩ := hx.typeFormer hS hΓ hs
  obtain ⟨u, hsort⟩ := hs.isType henv.ordered hΓ
  cases ds with
  | nil =>
    have hsw := (hd.of_l henv hΓ hsort).hasType.2
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (hd.symm.typeChain henv hΓ hsw)
  | cons d ds =>
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hsort hd

omit [VEnv.Params] in
theorem const_eq_mkApps_const {c : Name} {ls : List VLevel} {name : Name} {levels : List VLevel}
    {arguments : List VExpr} (h : VExpr.const c ls = mkApps (.const name levels) arguments) :
    c = name ∧ ls = levels ∧ arguments = [] := by
  have := congrArg VExpr.getAppFnArgs h
  rw [getAppFnArgs_mkApps_const] at this
  simp only [getAppFnArgs, getAppFnArgs.go, Prod.mk.injEq, VExpr.const.injEq] at this
  exact ⟨this.1.1, this.1.2, this.2.symm⟩

omit [VEnv.Params] in
theorem app_head_eq_mkApps_const {f a : VExpr} {name : Name} {levels : List VLevel}
    {arguments : List VExpr} (h : VExpr.app f a = mkApps (.const name levels) arguments) :
    f.getAppFnArgs.1 = .const name levels := by
  have := congrArg (fun e : VExpr => e.getAppFnArgs.1) h
  rw [getAppFnArgs_mkApps_const, case_spine_app] at this
  exact this

omit [VEnv.Params] in
theorem lam_ne_mkApps_const {A b : VExpr} {name : Name} {levels : List VLevel}
    {arguments : List VExpr} (h : VExpr.lam A b = mkApps (.const name levels) arguments) : False := by
  have := congrArg (fun e : VExpr => e.getAppFnArgs.1) h
  rw [getAppFnArgs_mkApps_const] at this
  simp [getAppFnArgs, getAppFnArgs.go] at this

omit [VEnv.Params] in
/-- The head of an eta spine, when a constant, is `S`. -/
theorem EtaSpine.no_rigid_head {n : Nat}
    (hx : EtaSpine S ls n x) {name : Name} {levels : List VLevel}
    (hh : x.getAppFnArgs.1 = .const name levels) : name = S := by
  rcases hx.head_cases with h | ⟨A, b, h⟩
  · rw [h] at hh; cases hh; rfl
  · rw [h] at hh; cases hh

/-- `EtaSpine` is preserved by one full step. -/
theorem EtaSpine.fullStep (hrig : Params.env.Rigid S)
    (hS : TypeFormerHead Params.env univs S ls) :
    ∀ {n : Nat} {x : VExpr} {Γ : List VExpr} {y T : VExpr}, EtaSpine S ls n x →
      OnCtx Γ (Params.env.IsType univs) → Params.env.HasType univs Γ x T → FullStep Γ x y →
      ∃ m, EtaSpine S ls m y := by
  intro n x Γ y T hx hΓ ht hstep
  induction hx generalizing Γ y T with
  | head =>
    generalize he : (VExpr.const S ls) = src at hstep
    cases hstep with
    | core h =>
      subst he
      obtain ⟨args', rfl, -⟩ := ParRed.rigid_const_spine hrig (args := []) h
      exact ⟨_, EtaSpine.of_spine args'⟩
    | delta h =>
      obtain ⟨rfl, -, -⟩ := const_eq_mkApps_const he
      exact (h.not_rigid hrig).elim
    | quotDelta h =>
      obtain ⟨rfl, -, -⟩ := const_eq_mkApps_const he
      exact (h.not_rigid hrig).elim
    | structEta hi _ _ hs _ => subst he; exact (EtaSpine.not_struct hS .head hΓ hi hs).elim
    | funEta _ => subst he; exact ⟨_, .lam (.app .head)⟩
    | _ => cases he
  | @app n f a hf ih =>
    obtain ⟨A, B, hf', ha⟩ := ht.app_inv henv.ordered hΓ
    generalize he : (VExpr.app f a) = src at hstep
    cases hstep with
    | core h =>
      generalize he' : src = src' at h
      cases h with
      | schema hm =>
        exfalso
        have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) (he.trans he')
        rw [InductiveSignature.CaseSchema.Application.head, case_spine_app] at hh
        rcases hf.head_cases with h | ⟨_, _, h⟩ <;> rw [h] at hh <;> cases hh
      | app hf₀ ha₀ =>
        cases he.trans he'
        obtain ⟨m, hm⟩ := ih hΓ hf' (.core hf₀)
        exact ⟨_, .app hm⟩
      | beta hb ha₀ =>
        cases he.trans he'
        obtain ⟨m, hm⟩ := ih hΓ hf' (.core (.lam .rfl hb))
        obtain ⟨m', hm'⟩ := hm.lam_inv
        exact ⟨_, hm'.inst _ _⟩
      | extra hp hm _ _ =>
        exfalso
        subst he'; subst he
        obtain ⟨name, hh⟩ := (Params.constHeaded hp).matches_head hm
        have := hf.no_rigid_head (by rwa [case_spine_app] at hh)
        subst this
        exact Params.not_rigid_match hrig hp hm hh
      | _ => cases he.trans he'
    | delta h =>
      exfalso
      cases hf.no_rigid_head (app_head_eq_mkApps_const he)
      exact h.not_rigid hrig
    | quotDelta h =>
      exfalso
      cases hf.no_rigid_head (app_head_eq_mkApps_const he)
      exact h.not_rigid hrig
    | structEta hi _ _ hs _ => subst he; exact (EtaSpine.not_struct hS (.app hf) hΓ hi hs).elim
    | funEta _ => subst he; exact ⟨_, .lam (.app (EtaSpine.app hf).lift)⟩
    | app hf₀ _ =>
      cases he
      obtain ⟨m, hm⟩ := ih hΓ hf' hf₀
      exact ⟨_, .app hm⟩
    | _ => cases he
  | @lam n A b hb ih =>
    obtain ⟨⟨u, hA⟩, _, hb'⟩ := ht.lam_inv henv.ordered hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    generalize he : (VExpr.lam A b) = src at hstep
    cases hstep with
    | core h =>
      generalize he' : src = src' at h
      cases h with
      | schema hm =>
        exfalso
        have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) (he.trans he')
        rw [InductiveSignature.CaseSchema.Application.head] at hh
        cases hh
      | lam _ hb₀ =>
        cases he.trans he'
        obtain ⟨m, hm⟩ := ih hΓA hb' (.core hb₀)
        exact ⟨_, .lam hm⟩
      | extra hp hm _ _ =>
        exfalso
        subst he'; subst he
        obtain ⟨name, hh⟩ := (Params.constHeaded hp).matches_head hm
        cases hh
      | _ => cases he.trans he'
    | delta h => exact (lam_ne_mkApps_const he).elim
    | quotDelta h => exact (lam_ne_mkApps_const he).elim
    | structEta hi _ _ hs _ => subst he; exact (EtaSpine.not_struct hS (.lam hb) hΓ hi hs).elim
    | funEta _ => subst he; exact ⟨_, .lam (.app (EtaSpine.lam hb).lift)⟩
    | lam _ hb₀ =>
      cases he
      obtain ⟨m, hm⟩ := ih hΓA hb' hb₀
      exact ⟨_, .lam hm⟩
    | _ => cases he

theorem EtaSpine.fullReduction (hrig : Params.env.Rigid S)
    (hS : TypeFormerHead Params.env univs S ls) (hΓ : OnCtx Γ (Params.env.IsType univs)) {n : Nat}
    (hx : EtaSpine S ls n x) (ht : Params.env.HasType univs Γ x T) (H : FullReduction Γ x y) :
    ∃ m, EtaSpine S ls m y := by
  induction H with
  | rfl => exact ⟨_, hx⟩
  | tail hr hs ih =>
    obtain ⟨m, hm⟩ := ih
    exact EtaSpine.fullStep hrig hS hm hΓ (FullReduction.hasType hΓ hr ht) hs

theorem forall₂_refl_full : ∀ (bs : List VExpr), List.Forall₂ (FullReduction Γ) bs bs
  | [] => .nil
  | _ :: bs => .cons .rfl (forall₂_refl_full bs)

/-- A sort-typed eta spine reduces to a syntactic spine, by beta. -/
theorem EtaSpine.reduces_to_spine (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ (n : Nat) {x : VExpr} {bs : List VExpr} {u : VLevel}, EtaSpine S ls n x →
      Params.env.HasType univs Γ (mkApps x bs) (.sort u) →
      ∃ args', FullReduction Γ (mkApps x bs) (mkApps (.const S ls) args') := by
  intro n
  induction n with
  | zero =>
    intro x bs u hx _
    cases hx with
    | head => exact ⟨bs, .rfl⟩
  | succ n ih =>
    intro x bs u hx ht
    cases hx with
    | @app _ g b hf => exact ih (bs := b :: bs) hf ht
    | @lam _ A b hb =>
      cases bs with
      | nil =>
        obtain ⟨B, hPi, _⟩ := ht.lam_inv_forallE henv hΓ
        exact (IsDefEqU.sort_forallE_inv henv hΓ hPi.symm).elim
      | cons b₀ bs =>
        have hred : FullReduction Γ (mkApps (.app (.lam A b) b₀) bs) (mkApps (b.inst b₀) bs) :=
          FullReduction.mkApps (.tail .rfl (.core (.beta .rfl .rfl))) (forall₂_refl_full bs)
        obtain ⟨args', h⟩ := ih (hb.inst b₀ 0) (hred.hasType hΓ ht)
        exact ⟨args', hred.trans h⟩

/-- Every reduct of a sort-typed rigid type-former spine reduces back to a spine with the same
head and levels. -/
theorem rigid_spine_reduct (hrig : Params.env.Rigid S)
    (hS : TypeFormerHead Params.env univs S ls) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (mkApps (.const S ls) args) (.sort u))
    (H : FullReduction Γ (mkApps (.const S ls) args) y) :
    ∃ args', FullReduction Γ y (mkApps (.const S ls) args') := by
  obtain ⟨m, hm⟩ := EtaSpine.fullReduction hrig hS hΓ (EtaSpine.of_spine args) ht H
  exact EtaSpine.reduces_to_spine hΓ m (bs := []) hm (H.hasType hΓ ht)

end

/-- A type convertible to a rigid type-former spine reduces to a spine with the same head
(canonical `Eq`, through Church-Rosser, the stability of rigid spines and spine exposure of
normal equality). -/
theorem spine_exposure_reduces {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (hT : E.HasType U Γ T (.sort u)) (hrig : E.Rigid S)
    (hS : TypeFormerHead E U S ls) (H : E.IsDefEqU U Γ T (mkApps (.const S ls) args)) :
    letI := hE.params U
    ∃ ls' args', FullReduction Γ T (mkApps (.const S ls') args') := by
  letI := hE.params U
  have hd := H.of_l hE hΓ hT
  obtain ⟨x, y, hx, hy, hn⟩ := hE.church_rosser hEq hΓ hd
  have hsp : E.HasType U Γ (mkApps (.const S ls) args) (.sort u) := hd.hasType.2
  obtain ⟨args', hy'⟩ := rigid_spine_reduct hrig hS hΓ hsp hy
  obtain ⟨x', hx', hn'⟩ := hn.fullReduction hΓ hy'
  have hxs : E.HasType U Γ x' (.sort u) := FullReduction.hasType hΓ (hx.trans hx') hT
  obtain ⟨n, hn'⟩ := hn'
  rcases NormalEqN.spine_expose hΓ .const n hn' .nil hxs with hp | ⟨h', targs', he, hr, -⟩ |
      ⟨A, g, m, targs₁, B, -, hr, -, -, -⟩
  · exfalso
    have h2 := ((HasType.sort (hxs.sort_r hE.ordered hΓ)).uniqU hE hΓ hp).sort_inv hE hΓ
    have h3 := congrFun h2 []
    simp [VLevel.eval] at h3
  · cases he with
    | const _ => exact ⟨_, _, (hx.trans hx').trans hr⟩
  · exfalso
    have hl := FullReduction.hasType hΓ hr hxs
    obtain ⟨⟨v, hA⟩, _, hg⟩ := hl.lam_inv hE.ordered hΓ
    exact type_not_function hΓ hl (.lam hA hg)


/-! ## Projection structures are type formers -/

theorem typeFormerHead_of_projections (henv : env.WF) {info : VProjectionInfo}
    (hinfo : env.projections S info) (hls : ls.length = info.uvars) :
    TypeFormerHead env U S ls := by
  intro Γ args T hΓ ht
  obtain ⟨decl, familyType, ctor, _, _, _, _, huvars, _, _, _, _, _, hlookup, _,
    ⟨common, Hshape, _⟩, _, _⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnorm, hown, hidx, _, hresult⟩ := Hshape
  have hnormEq : normalized = wrapForalls (ownParams ++ indices) result := by
    rw [VExpr.eq_wrapForalls_of_takeForalls hown, VExpr.eq_wrapForalls_of_takeForalls hidx,
      wrapForalls_append]
  subst hnormEq
  have hctx : env.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ []) result
      (.sort familyType.resultLevel) (.sort (.succ familyType.resultLevel)) := by
    simpa only [List.reverse_append, List.append_nil] using hresult
  obtain ⟨v, hcongr⟩ := wrapForalls_congr henv.ordered hnorm.hasType.2 hctx
  have hty : env.IsDefEqU decl.uvars [] familyType.type
      (wrapForalls (ownParams ++ indices) (.sort familyType.resultLevel)) :=
    IsDefEqU.trans henv trivial ⟨_, hnorm⟩ ⟨_, hcongr⟩
  obtain ⟨_, hhead⟩ := mkApps_head_typed henv.ordered hΓ ht
  obtain ⟨ci, hci, hlsWF, hlen⟩ := hhead.const_inv henv.ordered hΓ
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hfam : familyType.uvars = decl.uvars := by
    change ls.length = familyType.uvars at hlen
    omega
  rw [← hfam] at hty
  have hinst := hty.instL hlsWF
  simp only [List.map_nil, instL_wrapForalls, VExpr.instL] at hinst
  have hconst : env.HasType U [] (.const S ls) (familyType.type.instL ls) :=
    HasType.const hlookup hlsWF hlen
  exact TypeFormerHead.of_telescope henv (hconst.defeqU_r henv trivial hinst) hΓ ht

/-! ## The projection closure

`ProjFrontN` splits into the exposure of the major's type below (spine exposure, from
`EtaReplay`) and the typing of the field type below (`ProjFieldFrontN`, the exact remaining
obligation of the projection case, see the log). -/

/-- OPEN: the field-type closure. For a major typed below at a structure type whose projection
is typable above, the field type computed from the data below is typed at a sort below, with
the universe guard of `projDF`. -/
def ProjFieldFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' S info ls ps idx m i T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) →
    OnCtx Γ' (env.IsType U) → env.projections S info → ls.length = info.uvars →
    ps.length = info.nparams → idx.length = info.nindices →
    env.HasType U Γ m (mkApps (.const S ls) (ps ++ idx)) →
    env.HasType U Γ' (.proj S i (m.liftN 1 k)) T →
    ∃ F l, info.fieldType S ls ps i m = some F ∧ env.HasType U Γ F (.sort l) ∧
      ((info.resultLevel.inst ls).IsNeverZero ∨ l ≈ .zero)

/-- The projection closure from spine exposure and the field-type closure. The major's type
below is convertible, above, to the structure type of the typing above, so it exposes below to
a spine of the same structure (`spine_exposure_reduces` above, then `SpineExposureRedN`); the
field type for the data below is typed by `ProjFieldFrontN`; `projDF` closes. -/
theorem ProjFrontN.of_spineExposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hSpine : SpineExposureRedN henv) (hField : ProjFieldFrontN env) : ProjFrontN env := by
  intro U k Γ Γ' S i m M T W hΓ hΓ' hm he
  obtain ⟨info, levels, params, indexArgs, sourceMajor, Fa, fl, hinfo, hlevels, hlen, hparams,
    hidx, -, -, hmajor, hclosed, -⟩ := he.proj_inv henv.ordered hΓ'
  have hm' : env.HasType U Γ' (m.liftN 1 k) (mkApps (.const S levels) (params ++ indexArgs)) :=
    hmajor.hasType.2
  have hM : env.IsDefEqU U Γ' (M.liftN 1 k) (mkApps (.const S levels) (params ++ indexArgs)) :=
    (hm.weakN henv.ordered W).uniqU henv hΓ' hm'
  obtain ⟨u, hMs⟩ := hm.isType henv.ordered hΓ
  letI := henv.params U
  obtain ⟨ls', args', hred'⟩ := spine_exposure_reduces henv heq hΓ' (hMs.weakN henv.ordered W)
    (henv.projectionRigid hinfo) (typeFormerHead_of_projections henv hinfo hlen) hM
  obtain ⟨args₀, hred⟩ := hSpine W hΓ hΓ' hm hMs hred'
  have hMdef : env.IsDefEq U Γ M (mkApps (.const S ls') args₀) (.sort u) :=
    FullReduction.defeq hΓ hred hMs
  have hm₀ : env.HasType U Γ m (mkApps (.const S ls') args₀) := hm.defeqU_r henv hΓ ⟨_, hMdef⟩
  have hsp : env.HasType U Γ (mkApps (.const S ls') args₀) (.sort u) := hMdef.hasType.2
  have hsp' : env.HasType U Γ' (mkApps (.const S ls') (args₀.map (·.liftN 1 k))) (.sort u) := by
    simpa only [liftN_mkApps, liftN] using hsp.weakN henv.ordered W
  have hrel : env.IsDefEqU U Γ' (mkApps (.const S ls') (args₀.map (·.liftN 1 k)))
      (mkApps (.const S levels) (params ++ indexArgs)) := by
    have := hMdef.weakN henv.ordered W
    simp only [liftN_mkApps, liftN] at this
    exact IsDefEqU.trans henv hΓ' (IsDefEqU.symm ⟨_, this⟩) hM
  obtain ⟨hls, hargs⟩ := IsDefEqU.rigidApp_inv henv hΓ' (henv.projectionRigid hinfo) hrel hsp'
  have hls'len : ls'.length = info.uvars := by rw [Lean4Lean.List.Forall₂.length_eq hls, hlen]
  have hargslen : args₀.length = info.nparams + info.nindices := by
    have := Lean4Lean.List.Forall₂.length_eq hargs
    simp only [List.length_map, List.length_append] at this
    omega
  have hsplit : args₀ = args₀.take info.nparams ++ args₀.drop info.nparams :=
    (List.take_append_drop _ _).symm
  have hps : (args₀.take info.nparams).length = info.nparams :=
    List.length_take_of_le (by omega)
  have hidx' : (args₀.drop info.nparams).length = info.nindices := by
    simp only [List.length_drop]; omega
  rw [hsplit] at hm₀
  obtain ⟨F, l, hF, hFs, hguard⟩ := hField W hΓ hΓ' hinfo hls'len hps hidx' hm₀ he
  obtain ⟨_, hhead⟩ := mkApps_head_typed henv.ordered hΓ hsp
  obtain ⟨_, _, hlsWF, _⟩ := hhead.const_inv henv.ordered hΓ
  exact ⟨_, .projDF hinfo hlsWF hls'len hps hidx' hF hFs hm₀ hm₀ hclosed hguard⟩

/-- The projection closure from the replay obligation and the field-type closure. -/
theorem ProjFrontN.of_etaReplay (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : ∀ U, @EtaReplay (henv.params U)) (hField : ProjFieldFrontN env) : ProjFrontN env :=
  ProjFrontN.of_spineExposure henv heq (spineExposureRed_of_etaReplay henv H) hField


/-! ## The field-type closure outside `Prop`

When the structure's sort at the given levels is never zero, every projection of a typed major is
typable (the guard of `projDF` holds by its left disjunct), so the field type of field `i` is
typed by the typed substitution of the constructor telescope: the parameters are typed at the
constructor's parameter domains (convertible to the type former's, `CtorParameterShape` and
`TypeShape` through the common `params`), and the earlier projections at their own field types,
by induction on the field index. No information from above is used. The field-type closure is
therefore exactly its instances at structures whose sort is not never-zero
(`ProjFieldFrontN.of_notNeverZero`). -/

variable {U₀ : Nat}

/-- A closed telescope domain instantiated at arguments typed along the telescope is a type in
any context. -/
theorem IsType.closed_telescope_instOuter (henv : env.WF) {Γ : List VExpr}
    {Δ : List VExpr} {A : VExpr} (hΔ : OnCtx Δ.reverse (env.IsType U₀))
    (hA : env.IsType U₀ Δ.reverse A) (hls : ∀ l ∈ ls, l.WF U) {args : List VExpr}
    (hlen : args.length = Δ.length)
    (hty : ∀ k (hk : k < args.length) (hk' : k < (Δ.map (VExpr.instL ls)).length),
      env.HasType U Γ args[k] ((Δ.map (VExpr.instL ls))[k].instOuter (args.take k))) :
    env.IsType U Γ ((A.instL ls).instOuter args) := by
  have hA' := hA.instL hls
  have hΔ' : OnCtx (Δ.reverse.map (VExpr.instL ls)) (env.IsType U) := hΔ.instL hls
  have hclosed := CtxWF.closed henv.ordered hΔ'
  obtain ⟨u, h⟩ := hA
  have hAc : (A.instL ls).ClosedN Δ.length := by
    have := (VExpr.WF.closedN henv.ordered ⟨_, h⟩ (CtxWF.closed henv.ordered hΔ)).instL (ls := ls)
    simpa using this
  have W := Ctx.LiftN.right hclosed Γ
  have hA'' := hA'.weakN henv.ordered W
  simp only [List.length_map, List.length_reverse] at hA''
  rw [hAc.liftN_eq (Nat.le_refl _)] at hA''
  exact IsType.instOuter_telescope henv (doms := Δ.map (VExpr.instL ls))
    (by rw [← List.map_reverse]; exact hA'') (by simpa using hlen) hty

/-- Outside `Prop`, the field type of every field of a typed major is typed, with no information
from any other context. -/
theorem projField_of_neverZero (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {info : VProjectionInfo} {ps idx : List VExpr} {m : VExpr} {i : Nat}
    (hinfo : env.projections S info) (hls : ls.length = info.uvars)
    (hps : ps.length = info.nparams) (hidx : idx.length = info.nindices)
    (hm : env.HasType U Γ m (mkApps (.const S ls) (ps ++ idx)))
    (hnz : (info.resultLevel.inst ls).IsNeverZero) (hi : i < info.numFields) :
    ∃ F l, info.fieldType S ls ps i m = some F ∧ env.HasType U Γ F (.sort l) := by
  obtain ⟨decl, type, ctor, -, -, -, -, huvars, hnparams, hnidx, hlevel, -, hctorType, hlookup,
    hwf, ⟨params, Hshape, Hparams⟩, Hraw, -⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, -, -, harity⟩ := Hraw.forallArity
  -- the structure type is a sort; the levels are well formed
  have hfamWF : VExpr.WF env U Γ (mkApps (.const S ls) (ps ++ idx)) :=
    let ⟨_, h⟩ := hm.isType henv.ordered hΓ; ⟨_, h⟩
  have hfam := HasType.projectionFamily_sort henv hΓ hinfo hls hps hidx hfamWF
  obtain ⟨_, hhead⟩ := mkApps_head_typed henv.ordered hΓ hfam
  obtain ⟨ci, hci, hlsWF, hlen⟩ := hhead.const_inv henv.ordered hΓ
  rw [hlookup] at hci
  cases Option.some.inj hci
  have hfamU : type.uvars = decl.uvars := by
    change ls.length = type.uvars at hlen
    omega
  have hnum : info.numFields = doms.length - info.nparams := by
    rw [VProjectionInfo.numFields, ← hctorType, harity]
  have hshape' : info.ctorType = wrapForalls doms result := by rw [← hctorType, hshape]
  have hclosed : info.ctorType.Closed := by
    rw [← hctorType]
    obtain ⟨_, h⟩ := hwf
    exact VExpr.WF.closedN henv.ordered ⟨_, h⟩ trivial
  -- the normalized header of the type former
  obtain ⟨normalized, ownParams, afterParams, indices, result', exprType, hnorm, hown, hidxT,
    hPD, hresult⟩ := Hshape
  obtain ⟨rfl, hownLen⟩ := VExpr.takeForalls_eq_wrapForalls hown
  obtain ⟨rfl, hindLen⟩ := VExpr.takeForalls_eq_wrapForalls hidxT
  rw [← wrapForalls_append] at hnorm
  have hctx : env.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ []) result'
      (.sort type.resultLevel) (.sort (.succ type.resultLevel)) := by
    simpa only [List.reverse_append, List.append_nil] using hresult
  obtain ⟨v, hcongr⟩ := wrapForalls_congr henv.ordered hnorm.hasType.2 hctx
  have hty : env.IsDefEqU decl.uvars [] type.type
      (wrapForalls (ownParams ++ indices) (.sort type.resultLevel)) :=
    IsDefEqU.trans henv trivial ⟨_, hnorm⟩ ⟨_, hcongr⟩
  rw [← hfamU] at hty
  have hinst := hty.instL hlsWF
  simp only [List.map_nil, instL_wrapForalls, VExpr.instL] at hinst
  have hconst : env.HasType U Γ (.const S ls)
      (wrapForalls ((ownParams ++ indices).map (VExpr.instL ls)) (.sort (type.resultLevel.inst ls))) := by
    have hc0 : env.HasType U [] (.const S ls) (type.toVConstant.type.instL ls) :=
      HasType.const hlookup hlsWF hlen
    exact (hc0.defeqU_r henv (by trivial) hinst).weak0 henv.ordered
  have hlenD : (ps ++ idx).length = ((ownParams ++ indices).map (VExpr.instL ls)).length := by
    simp only [List.length_append, List.length_map]
    omega
  have hargsT := (HasType.mkApps_wrapForalls henv hΓ hconst hfamWF hlenD).1
  -- the parameters are typed at the type former's parameter domains
  have hpsOwn : ∀ k (hk : k < ps.length) (hk' : k < ownParams.length),
      env.HasType U Γ ps[k] ((ownParams[k].instL ls).instOuter (ps.take k)) := by
    intro k hk hk'
    have h := hargsT k (by simp; omega) (by simp; omega)
    rw [List.getElem_append_left hk, List.take_append_of_le_length (Nat.le_of_lt hk),
      List.getElem_map, List.getElem_append_left hk'] at h
    exact h
  -- the constructor's parameter domains are the type former's, up to conversion
  obtain ⟨ownParams', tail, htake, hPD'⟩ := Hparams
  have hsplitTake := takeForalls_wrapForalls_append (doms.take decl.nparams)
    (doms.drop decl.nparams) result
  rw [List.take_append_drop, List.length_take_of_le hle] at hsplitTake
  rw [hshape, hsplitTake] at htake
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj htake)
  have hOO : IsDefEqCtx env decl.uvars [] ownParams.reverse (doms.take decl.nparams).reverse :=
    IsDefEqCtx.trans_empty henv (hPD.symm henv.ordered) hPD'
  have hOwnCtx : OnCtx ownParams.reverse (env.IsType decl.uvars) :=
    (hPD.symm henv.ordered).isType
  have hpsCtor : ∀ k (hk : k < ps.length) (hk'' : k < (doms.take decl.nparams).length),
      env.HasType U Γ ps[k] ((((doms.take decl.nparams)[k]).instL ls).instOuter (ps.take k)) := by
    intro k hk hk''
    have hk' : k < ownParams.length := by omega
    obtain ⟨u, hu⟩ := hOO.reverse_getElem k hk' hk''
    have hΔ₀ : OnCtx (ownParams.take k).reverse (env.IsType decl.uvars) := by
      have : ownParams.reverse = (ownParams.drop k).reverse ++ (ownParams.take k).reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      rw [this] at hOwnCtx
      exact OnCtx.of_append hOwnCtx
    have hconv := IsDefEqU.closed_telescope_instOuter henv hΔ₀ ⟨_, hu⟩ hlsWF
      (args := ps.take k) (by simp only [List.length_take, List.length_reverse]; omega)
      (by
        intro k' hk1 hk2
        simp only [List.length_take, List.reverse_reverse, List.length_map] at hk1 hk2
        have hk1' : k' < ps.length := by omega
        have h := hpsOwn k' hk1' (by omega)
        simp only [List.reverse_reverse, List.getElem_map, List.getElem_take, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt (show k' < k by omega))]
        exact h)
    exact (hpsOwn k hk hk').defeqU_r henv hΓ hconv
  -- the field domains are types in their closed telescopes
  have hdomsCtx : OnCtx (doms.reverse ++ []) (env.IsType decl.uvars) := by
    rw [hshape] at hwf
    exact (IsType.wrapForalls_inv henv (by trivial) hwf).1
  have hdom : ∀ n (hn : n < doms.length),
      OnCtx (doms.take n).reverse (env.IsType decl.uvars) ∧
        env.IsType decl.uvars (doms.take n).reverse doms[n] := by
    intro n hn
    have := OnCtx.getElem_reverse_append hdomsCtx n hn
    simp only [List.append_nil] at this
    exact ⟨this.1, this.2⟩
  -- the field type of field `j`, given the earlier projections typed
  let projs : Nat → List VExpr := fun j => (List.range j).map fun j' => VExpr.proj S j' m
  have hprojsLen : ∀ j, (projs j).length = j := by intro j; simp [projs]
  have isTypeF : ∀ j (hlt : info.nparams + j < doms.length),
      (∀ j' (hj' : j' < j), env.HasType U Γ (.proj S j' m)
        (((doms[info.nparams + j']'(by omega)).instL ls).instOuter (ps ++ projs j'))) →
      env.IsType U Γ (((doms[info.nparams + j]'hlt).instL ls).instOuter (ps ++ projs j)) := by
    intro j hlt hprojs
    obtain ⟨hΔ, hA⟩ := hdom (info.nparams + j) hlt
    refine IsType.closed_telescope_instOuter henv hΔ hA hlsWF
      (by simp only [List.length_append, hprojsLen, hps, List.length_take_of_le (Nat.le_of_lt hlt)])
      ?_
    intro k hk hk'
    simp only [List.length_append, hprojsLen, hps] at hk
    rcases Nat.lt_or_ge k info.nparams with hkp | hkp
    · have hkps : k < ps.length := by omega
      have h := hpsCtor k hkps (by rw [List.length_take_of_le hle]; omega)
      rw [List.getElem_append_left hkps, List.take_append_of_le_length (Nat.le_of_lt hkps),
        List.getElem_map, List.getElem_take]
      rw [List.getElem_take] at h
      exact h
    · obtain ⟨j', rfl⟩ : ∃ j', k = info.nparams + j' := ⟨k - info.nparams, by omega⟩
      have hj' : j' < j := by omega
      have h := hprojs j' hj'
      have e1 : (ps ++ projs j)[info.nparams + j']'(by simp [hprojsLen, hps]; omega) =
          VExpr.proj S j' m := by
        rw [List.getElem_append_right (by omega)]
        simp [projs, hps]
      have e2 : (ps ++ projs j).take (info.nparams + j') = ps ++ projs j' := by
        rw [← hps, List.take_append, List.take_of_length_le (by omega)]
        simp only [Nat.add_sub_cancel_left, projs, ← List.map_take, List.take_range,
          Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [e1, e2, List.getElem_map, List.getElem_take]
      exact h
  -- the earlier projections are typed, by induction on the field index
  have hbound : ∀ j', j' ≤ i → info.nparams + j' < doms.length := by
    intro j' hj'
    rw [hnum] at hi
    omega
  have hQ : ∀ j (hji : j ≤ i) j' (hj' : j' < j), env.HasType U Γ (.proj S j' m)
      (((doms[info.nparams + j']'(hbound j' (Nat.le_trans (Nat.le_of_lt hj') hji))).instL ls).instOuter
        (ps ++ projs j')) := by
    intro j
    induction j with
    | zero => intro _ j' hj'; cases hj'
    | succ j ih =>
      intro hji j' hj'
      rcases Nat.lt_or_ge j' j with hlt | hge
      · exact ih (Nat.le_of_succ_le hji) j' hlt
      · obtain rfl : j = j' := by omega
        have hltD : info.nparams + j < doms.length := hbound j (Nat.le_of_succ_le hji)
        obtain ⟨l, hFs⟩ := isTypeF j hltD (ih (Nat.le_of_succ_le hji))
        have hF := VProjectionInfo.fieldType_eq_instOuter info (typeName := S) (major := m)
          hshape' hls hps hltD
        exact .projDF hinfo hlsWF hls hps hidx hF hFs hm hm hclosed (Or.inl hnz)
  have hltD : info.nparams + i < doms.length := hbound i (Nat.le_refl _)
  obtain ⟨l, hFs⟩ := isTypeF i hltD (hQ i (Nat.le_refl _))
  exact ⟨_, l, VProjectionInfo.fieldType_eq_instOuter info hshape' hls hps hltD, hFs⟩

/-- The field-type closure at structures whose sort at the given levels is not never-zero:
the exact remaining content of `ProjFieldFrontN`. For a major typed below at a structure type
whose projection `i` is typable above, the field type `fieldType S ls ps i m` (the constructor's
field domain instantiated at the parameters and the earlier projections,
`fieldType_eq_instOuter`) is typed at a sort below, with `projDF`'s universe guard. Outside
`Prop` this is a library fact (`projField_of_neverZero`: every earlier projection is typable
and the closed constructor telescope instantiates, `IsType.closed_telescope_instOuter`). For a
`Prop` structure with a data field `j < i` the projection `proj j m` is not typable, so if the
field domain does not mention binder `j` its instance is typed only by thinning binder `j` out
of the closed constructor telescope: a closed-telescope strengthening instance with an
uninhabited removed binder. It is used twice in `Final.lean`: for `ProjFrontN` (through spine
exposure) and for the descent of the composite major-eta step (`majorEtaDescends`), whose
structure eta step below needs the projections of the major typed below. `Cancel` implies it
up to the congruence of `fieldType` along convertible data (`structApp_inv` relates the given
`(ls, ps, m)` to the data of the typing derivation below), which needs a substitution congruence
through unmentioned, possibly unprojectable binders that the library does not provide
(`proj_fieldType` compares two field types that are both already typed). -/
def ProjFieldFrontPropN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' S info ls ps idx m i T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) →
    OnCtx Γ' (env.IsType U) → env.projections S info → ls.length = info.uvars →
    ps.length = info.nparams → idx.length = info.nindices →
    env.HasType U Γ m (mkApps (.const S ls) (ps ++ idx)) →
    env.HasType U Γ' (.proj S i (m.liftN 1 k)) T →
    ¬ (info.resultLevel.inst ls).IsNeverZero →
    ∃ F l, info.fieldType S ls ps i m = some F ∧ env.HasType U Γ F (.sort l) ∧
      ((info.resultLevel.inst ls).IsNeverZero ∨ l ≈ .zero)

/-- The field-type closure reduces to its instances at structures in (or possibly in) `Prop`. -/
theorem ProjFieldFrontN.of_notNeverZero (henv : env.WF) (H : ProjFieldFrontPropN env) :
    ProjFieldFrontN env := by
  intro U k Γ Γ' S info ls ps idx m i T W hΓ hΓ' hinfo hls hps hidx hm he
  by_cases hnz : (info.resultLevel.inst ls).IsNeverZero
  · obtain ⟨F, l, hF, hFs⟩ := projField_of_neverZero henv hΓ hinfo hls hps hidx hm hnz
      (HasType.proj_index_lt henv hΓ' he hinfo)
    exact ⟨F, l, hF, hFs, .inl hnz⟩
  · exact H W hΓ hΓ' hinfo hls hps hidx hm he hnz

end Lean4Lean.VEnv.StrengtheningSpineExposure
