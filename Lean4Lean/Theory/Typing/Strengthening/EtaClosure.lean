import Lean4Lean.Theory.Typing.Strengthening.EtaPostponement

/-! # Closure of the eta-normal relation under eta-free steps on the right

Direction B3, step 6: the replay obligation
`UpStepFClosure`, that is `EtaNE Γ s X → UpStepF Γ X Y → EtaNE Γ s Y`, by induction on the
`EtaNE` derivation. The congruence cases push the step into the sub-derivations; a redex fired on
the reduct is fired on the source as a recorded step (`redL`), after the spine of the source is
exposed by `EtaNE.const_spine_inv` (the source is the same spine up to the relation, or a neutral
of structure type whose junk expansion is the constructor application: the composite step
`MajorEtaIota`). -/

namespace Lean4Lean.VEnv.StrengtheningEtaClosure
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => Params.env.IsDefEq univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => Params.env.IsDefEqU univs Γ e1 e2

/-! ## Chains of source steps -/

theorem EtaNE.redL_chain {Γ : List VExpr} {s s' X : VExpr} (h : ReflTransGen (LStep Γ) s s')
    (H : EtaNE Γ s' X) : EtaNE Γ s X := by
  induction h with
  | rfl => exact H
  | tail _ hstep ih => exact ih (.redL hstep H)

theorem LStep.app_l {Γ : List VExpr} {f f' a : VExpr} (h : LStep Γ f f') :
    LStep Γ (.app f a) (.app f' a) := by
  rcases h with (h | h) | h
  · exact .inl (.inl (.app h .rfl))
  · exact .inl (.inr (.app h .rfl))
  · exact .inr (.appL h)

theorem LStep.app_r {Γ : List VExpr} {f a a' : VExpr} (h : LStep Γ a a') :
    LStep Γ (.app f a) (.app f a') := by
  rcases h with (h | h) | h
  · exact .inl (.inl (.app .rfl h))
  · exact .inl (.inr (.app .rfl h))
  · exact .inr (.appR h)

theorem LStep.proj {Γ : List VExpr} {m m' : VExpr} {S : Name} {i : Nat} (h : LStep Γ m m') :
    LStep Γ (.proj S i m) (.proj S i m') := by
  rcases h with (h | h) | h
  · exact .inl (.inl (.proj h))
  · exact .inl (.inr (.proj h))
  · exact .inr (.proj h)

theorem LStep.chain_app_l {Γ : List VExpr} {f f' a : VExpr} (h : ReflTransGen (LStep Γ) f f') :
    ReflTransGen (LStep Γ) (.app f a) (.app f' a) := by
  induction h with
  | rfl => exact .rfl
  | tail _ hstep ih => exact ih.tail (LStep.app_l hstep)

theorem LStep.chain_app_r {Γ : List VExpr} {f a a' : VExpr} (h : ReflTransGen (LStep Γ) a a') :
    ReflTransGen (LStep Γ) (.app f a) (.app f a') := by
  induction h with
  | rfl => exact .rfl
  | tail _ hstep ih => exact ih.tail (LStep.app_r hstep)

theorem LStep.hasType_chain {Γ : List VExpr} {s s' A : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (h : ReflTransGen (LStep Γ) s s') (hs : Γ ⊢ s : A) :
    Γ ⊢ s' : A := by
  induction h with
  | rfl => exact hs
  | tail _ hstep ih => exact hstep.hasType hΓ ih

theorem LStep.defeq_chain {Γ : List VExpr} {s s' A : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (h : ReflTransGen (LStep Γ) s s') (hs : Γ ⊢ s : A) :
    Γ ⊢ s ≡ s' := by
  induction h with
  | rfl => exact ⟨_, hs⟩
  | @tail s₁ s₂ hpre hstep ih =>
    have hs₁ : Γ ⊢ s₁ : A := LStep.hasType_chain hΓ hpre hs
    exact ih.trans henv hΓ ⟨_, hstep.defeq hΓ hs₁⟩

/-! ## Heads of patterns and spines -/

omit [Params] in
theorem head_app (f a : VExpr) : (VExpr.app f a).getAppFnArgs.1 = f.getAppFnArgs.1 := by
  simp [VExpr.getAppFnArgs_app]
omit [Params] in
theorem head_lam (A b : VExpr) : (VExpr.lam A b).getAppFnArgs.1 = .lam A b := rfl
omit [Params] in
theorem head_const (c : Name) (ls : List VLevel) : (VExpr.const c ls).getAppFnArgs.1 = .const c ls := rfl
omit [Params] in
theorem head_elim (b : Name) (o : Nat) (ls : List VLevel) :
    (VExpr.elim b o ls).getAppFnArgs.1 = .elim b o ls := rfl
omit [Params] in
theorem head_proj (S : Name) (i : Nat) (m : VExpr) :
    (VExpr.proj S i m).getAppFnArgs.1 = .proj S i m := rfl
omit [Params] in
theorem head_forallE (A B : VExpr) : (VExpr.forallE A B).getAppFnArgs.1 = .forallE A B := rfl
omit [Params] in
theorem head_bvar (i : Nat) : (VExpr.bvar i).getAppFnArgs.1 = .bvar i := rfl
omit [Params] in
theorem head_sort (u : VLevel) : (VExpr.sort u).getAppFnArgs.1 = .sort u := rfl

omit [Params] in
/-- Two spines with different atomic heads are different. -/
theorem mkApps_head_ne {f g : VExpr} {args args' : List VExpr}
    (hf : f.getAppFnArgs.1 = f) (hg : g.getAppFnArgs.1 = g) (hne : f ≠ g) :
    mkApps f args ≠ mkApps g args' := by
  intro h
  have := congrArg (fun e : VExpr => e.getAppFnArgs.1) h
  simp only [VExpr.getAppFnArgs_mkApps_head, hf, hg] at this
  exact hne this

omit [Params] in
theorem Pattern.Matches.head {p : Pattern} {e : VExpr} {ls : List VLevel} {vals : p.Path → VExpr}
    (hm : p.Matches e ls vals) :
    (∃ c ls', e.getAppFnArgs.1 = .const c ls') ∨ (∃ b o ls', e.getAppFnArgs.1 = .elim b o ls') := by
  induction hm with
  | const => exact .inl ⟨_, _, rfl⟩
  | elim => exact .inr ⟨_, _, _, rfl⟩
  | var _ ih => simpa [VExpr.getAppFnArgs_app] using ih
  | app _ _ ih _ => simpa [VExpr.getAppFnArgs_app] using ih

omit [Params] in
theorem Pattern.Matches.app_inv {p₁ p₂ : Pattern} {X₁ X₂ : VExpr} {ls : List VLevel}
    {m : (Pattern.app p₁ p₂).Path → VExpr} (hm : (Pattern.app p₁ p₂).Matches (.app X₁ X₂) ls m) :
    ∃ g1 ls₂ g2, p₁.Matches X₁ ls g1 ∧ p₂.Matches X₂ ls₂ g2 ∧ m = Sum.elim g1 g2 := by
  cases hm with
  | app hF hM => exact ⟨_, _, _, hF, hM, rfl⟩

/-- A parallel core step on a spine whose head is an application with a lambda head is a step on
the head and on the arguments. -/
theorem ParRed.spine_lamHead {Γ : List VExpr} {H₁ H₂ A b Y : VExpr} {args : List VExpr}
    (hH : (VExpr.app H₁ H₂).getAppFnArgs.1 = .lam A b)
    (H : ParRed Γ (mkApps (.app H₁ H₂) args) Y) :
    ∃ H' args', ParRed Γ (.app H₁ H₂) H' ∧ List.Forall₂ (ParRed Γ) args args' ∧
      Y = mkApps H' args' := by
  induction args using List.snoc_induction generalizing Y with
  | nil => exact ⟨Y, [], H, .nil, rfl⟩
  | snoc args₀ x ih =>
    rw [VExpr.mkApps_snoc] at H
    generalize hs : VExpr.app (mkApps (.app H₁ H₂) args₀) x = s at H
    cases H with
    | app hf ha =>
      cases hs
      obtain ⟨H', args₀', h1, h2, rfl⟩ := ih hf
      exact ⟨H', args₀' ++ [_], h1, List.Forall₂.append' h2 (.cons ha .nil), (VExpr.mkApps_snoc ..).symm⟩
    | beta =>
      exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ (VExpr.app.inj hs).1).elim
    | extra hp hm =>
      exfalso
      subst hs
      have hH' : H₁.getAppFnArgs.1 = .lam A b := by simpa [VExpr.getAppFnArgs_app] using hH
      rcases Pattern.Matches.head hm with ⟨c, ls', hc⟩ | ⟨b', o, ls', hc⟩ <;>
        simp [VExpr.getAppFnArgs_app, VExpr.getAppFnArgs_mkApps_head, hH'] at hc
    | schema hm =>
      exfalso
      have hH' : H₁.getAppFnArgs.1 = .lam A b := by simpa [VExpr.getAppFnArgs_app] using hH
      have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hs
      rw [InductiveSignature.CaseSchema.Application.head] at this
      simp [VExpr.getAppFnArgs_app, VExpr.getAppFnArgs_mkApps_head, hH'] at this
    | _ => cases hs

/-- A parallel core step on a constructor spine reduces the arguments. -/
theorem ParRed.ctor_spine {Γ : List VExpr} {S : Name} {info : VProjectionInfo} {ls : List VLevel}
    {args : List VExpr} {Y : VExpr} (hl : Params.env.projections S info)
    (H : ParRed Γ (mkApps (.const info.ctorName ls) args) Y) :
    ∃ args', Y = mkApps (.const info.ctorName ls) args' ∧ List.Forall₂ (ParRed Γ) args args' :=
  ParRed.const_spine_of args.length
    (fun hp _ hm => Params.not_rigid_match (projection_ctor_rigid hl) hp hm
      (by rw [VExpr.getAppFnArgs_mkApps_head]; rfl))
    (Nat.le_refl _) H

/-! ## Spine inversion: the source of a constant spine -/

/-- The source of a constant-headed spine is, after recorded steps, the same spine up to the
relation, or a neutral of structure type whose expansion is the constructor spine. -/
theorem EtaNE.const_spine_inv {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {s X T : VExpr}, EtaNE Γ s X → Γ ⊢ s : T →
      ∀ {c : Name} {ls : List VLevel} {args : List VExpr}, X = mkApps (.const c ls) args →
      ∃ s', ReflTransGen (LStep Γ) s s' ∧
        ((∃ args_s, s' = mkApps (.const c ls) args_s ∧ List.Forall₂ (EtaNE Γ) args_s args) ∨
         (∃ family info params, Params.env.projections family info ∧ c = info.ctorName ∧
            params.length = info.nparams ∧ info.nindices = 0 ∧
            Γ ⊢ s' : mkApps (.const family ls) params ∧
            Γ ⊢ structExpand family info ls params s' : mkApps (.const family ls) params ∧
            (structArgs family info params s').length = args.length ∧
            ∀ i (hi : i < (structArgs family info params s').length) (hi' : i < args.length),
              EtaNE Γ (structArgs family info params s')[i] args[i])) := by
  intro s X T H
  induction H generalizing T with
  | bvar =>
    intro hs c ls args he
    rcases mkApps_const_eq_cases he.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | sort =>
    intro hs c ls args he
    rcases mkApps_const_eq_cases he.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | elim =>
    intro hs c ls args he
    rcases mkApps_const_eq_cases he.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | const =>
    intro hs c ls args he
    rcases mkApps_const_eq_cases he.symm with ⟨rfl, h⟩ | ⟨_, _, _, h⟩
    · cases h; exact ⟨_, .rfl, .inl ⟨[], rfl, .nil⟩⟩
    · cases h
  | @app Γ s₁ f s₂ a H₁ H₂ ih₁ _ =>
    intro hs c ls args he
    rcases mkApps_const_eq_cases he.symm with ⟨_, h⟩ | ⟨args₀, x, rfl, h⟩
    · cases h
    · cases h
      obtain ⟨_, _, hs₁, hs₂⟩ := hs.app_inv henv hΓ
      obtain ⟨s₁', hchain, hcase⟩ := ih₁ hΓ hs₁ rfl
      rcases hcase with ⟨args_s₀, rfl, hF⟩ | ⟨family, info, params, hl, -, -, -, hs₁', -, -, -⟩
      · exact ⟨.app (mkApps (.const c ls) args_s₀) s₂, LStep.chain_app_l hchain,
          .inl ⟨args_s₀ ++ [s₂], (VExpr.mkApps_snoc ..).symm, List.Forall₂.append' hF (.cons H₂ .nil)⟩⟩
      · exfalso
        have hX := (EtaNE.app H₁ H₂).hasType hΓ hs
        obtain ⟨_, _, hf, -⟩ := hX.app_inv henv hΓ
        have h1 : Γ ⊢ s₁ ≡ s₁' := LStep.defeq_chain hΓ hchain hs₁
        have h2 := H₁.defeq hΓ hs₁
        have hfS : Γ ⊢ mkApps (.const c ls) args₀ : mkApps (.const family ls) params :=
          hs₁'.defeqU_l henv hΓ (h1.symm.trans henv hΓ h2)
        exact pi_not_struct hΓ hl hf hfS
  | proj => intro hs c ls args he; exact (mkApps_const_ne_proj he.symm).elim
  | lamC => intro hs c ls args he; exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm).elim
  | lamD => intro hs c ls args he; exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm).elim
  | forallEC =>
    intro hs c ls args he
    exact (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ he.symm).elim
  | funEta => intro hs c ls args he; exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm).elim
  | structEta hl hp hi hs' hexp hlen hargs =>
    intro hs c ls args he
    obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he.symm
    exact ⟨_, .rfl, .inr ⟨_, _, _, hl, rfl, hp, hi, hs', hexp, hlen, hargs⟩⟩
  | betaR =>
    intro hs c ls args he
    have := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    simp only [VExpr.getAppFnArgs_mkApps_head, head_app, head_lam, head_const] at this
    cases this
  | redL h _ ih =>
    intro hs c ls args he
    obtain ⟨s', hchain, hcase⟩ := ih hΓ (h.hasType hΓ hs) he
    exact ⟨s', .trans (.tail .rfl h) hchain, hcase⟩

/-- The source of an eliminator-headed spine is, after recorded steps, the same spine up to the
relation. -/
theorem EtaNE.elim_spine_inv {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {s X T : VExpr}, EtaNE Γ s X → Γ ⊢ s : T →
      ∀ {b : Name} {o : Nat} {ls : List VLevel} {args : List VExpr},
      X = mkApps (.elim b o ls) args →
      ∃ s' args_s, ReflTransGen (LStep Γ) s s' ∧ s' = mkApps (.elim b o ls) args_s ∧
        List.Forall₂ (EtaNE Γ) args_s args := by
  intro s X T H
  induction H generalizing T with
  | bvar =>
    intro hs b o ls args he
    rcases mkApps_elim_eq_cases he.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | sort =>
    intro hs b o ls args he
    rcases mkApps_elim_eq_cases he.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | const =>
    intro hs b o ls args he
    rcases mkApps_elim_eq_cases he.symm with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | elim =>
    intro hs b o ls args he
    rcases mkApps_elim_eq_cases he.symm with ⟨rfl, h⟩ | ⟨_, _, _, h⟩
    · cases h; exact ⟨_, [], .rfl, rfl, .nil⟩
    · cases h
  | @app Γ s₁ f s₂ a H₁ H₂ ih₁ _ =>
    intro hs b o ls args he
    rcases mkApps_elim_eq_cases he.symm with ⟨_, h⟩ | ⟨args₀, x, rfl, h⟩
    · cases h
    · cases h
      obtain ⟨_, _, hs₁, hs₂⟩ := hs.app_inv henv hΓ
      obtain ⟨s₁', args_s₀, hchain, rfl, hF⟩ := ih₁ hΓ hs₁ rfl
      exact ⟨.app (mkApps (.elim b o ls) args_s₀) s₂, args_s₀ ++ [s₂], LStep.chain_app_l hchain,
        (VExpr.mkApps_snoc ..).symm, List.Forall₂.append' hF (.cons H₂ .nil)⟩
  | @proj _ m m' S i _ =>
    intro hs b o ls args he
    exact (mkApps_head_ne (f := .proj S i m') (args := []) (head_proj ..) (head_elim ..)
      (by intro h; cases h) he).elim
  | @lamC _ A A' b b' _ _ =>
    intro hs b₀ o ls args he
    exact (mkApps_head_ne (f := .lam A' b') (args := []) (head_lam ..) (head_elim ..)
      (by intro h; cases h) he).elim
  | @lamD _ A A' b b' _ _ _ =>
    intro hs b₀ o ls args he
    exact (mkApps_head_ne (f := .lam A' b') (args := []) (head_lam ..) (head_elim ..)
      (by intro h; cases h) he).elim
  | @forallEC _ A A' B B' _ _ =>
    intro hs b o ls args he
    exact (mkApps_head_ne (f := .forallE A' B') (args := []) (head_forallE ..) (head_elim ..)
      (by intro h; cases h) he).elim
  | @funEta _ e A B A' body u _ _ _ =>
    intro hs b₀ o ls args he
    exact (mkApps_head_ne (f := .lam A' body) (args := []) (head_lam ..) (head_elim ..)
      (by intro h; cases h) he).elim
  | structEta =>
    intro hs b o ls args he
    exact (mkApps_head_ne (head_const ..) (head_elim ..) (by intro h; cases h) he).elim
  | betaR =>
    intro hs b o ls args he
    have := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    simp only [VExpr.getAppFnArgs_mkApps_head, head_app, head_lam, head_elim] at this
    cases this
  | redL h _ ih =>
    intro hs b o ls args he
    obtain ⟨s', args_s, hchain, hs', hF⟩ := ih hΓ (h.hasType hΓ hs) he
    exact ⟨s', args_s, .trans (.tail .rfl h) hchain, hs', hF⟩

/-! ## The collapse of a related lambda in function position -/

/-- If the function part is related to a lambda, the application is related to the instantiated
body: the source either is a lambda (beta on the source, then substitution) or expanded to it
(substitution of the new variable). -/
theorem EtaNE.app_lam_inst {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {s₁ X A B A₁ b₁ s₂ a : VExpr}, EtaNE Γ s₁ X → X = .lam A₁ b₁ → Γ ⊢ s₁ : .forallE A B →
      Γ ⊢ s₂ : A → EtaNE Γ s₂ a → EtaNE Γ (.app s₁ s₂) (b₁.inst a) := by
  intro s₁ X A B A₁ b₁ s₂ a H₁
  induction H₁ generalizing A B A₁ b₁ with
  | @lamC Γ D D' t t' _ Ht =>
    intro he hs₁ hs₂ H₂
    cases he
    obtain ⟨B₀, hPi, ht⟩ := hs₁.lam_inv_forallE henv hΓ
    obtain ⟨⟨_, hD⟩, -⟩ := hs₁.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
    have hs₂' : Γ ⊢ s₂ : D := hDA.defeq' hs₂
    exact .redL (.inl (.inl (.beta .rfl .rfl)))
      (EtaNE.instN .zero ⟨hΓ, _, hD⟩ H₂ hs₂' Ht ht)
  | @lamD Γ D D' t t' u hDD' Ht =>
    intro he hs₁ hs₂ H₂
    cases he
    obtain ⟨B₀, hPi, ht⟩ := hs₁.lam_inv_forallE henv hΓ
    obtain ⟨⟨_, hD⟩, -⟩ := hs₁.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
    have hs₂' : Γ ⊢ s₂ : D := hDA.defeq' hs₂
    exact .redL (.inl (.inl (.beta .rfl .rfl)))
      (EtaNE.instN .zero ⟨hΓ, _, hD⟩ H₂ hs₂' Ht ht)
  | @funEta Γ e A' B' A₁' body u hPi hA Hb =>
    intro he hs₁ hs₂ H₂
    cases he
    obtain ⟨⟨_, hAA'⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ (hs₁.uniqU henv hΓ hPi)
    have hs₂' : Γ ⊢ s₂ : A₁' := hA.defeq (hAA'.defeq hs₂)
    have hΓ' : OnCtx (A₁' :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
    have hbody : A₁' :: Γ ⊢ .app e.lift (.bvar 0) : B' := by
      have h1 : A₁' :: Γ ⊢ e.lift : .forallE A'.lift (B'.liftN 1 1) := hPi.weak henv.ordered
      have h0 : A₁' :: Γ ⊢ .bvar 0 : A'.lift :=
        (hA.weak henv.ordered (B := A₁')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    have := EtaNE.instN .zero hΓ' H₂ hs₂' Hb hbody
    simpa [inst, instVar, inst_lift] using this
  | redL h _ ih =>
    intro he hs₁ hs₂ H₂
    exact .redL (LStep.app_l h) (ih hΓ he (h.hasType hΓ hs₁) hs₂ H₂)
  | betaR =>
    intro he
    exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he).elim
  | structEta =>
    intro he
    exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he).elim
  | bvar | sort | const | elim | app | proj | forallEC => intro he; cases he

/-! ## Closure under parallel core steps -/

/-- Fire a case step at a source whose two spines are related (argument-wise) to the developed
spines of a case redex. The source captures are related to the reduced arguments, so the
right-hand sides are related by congruence. -/
theorem EtaNE.schema_fire {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    {rule : InductiveSignature.CaseSchema.AppliedRule}
    {actual : InductiveSignature.CaseSchema.Application}
    (hm : CaseRedex Params.env univs Γ rule actual) {arguments : List VExpr}
    (hl : arguments.length = (rule.capture actual).length)
    (hr : ∀ i (hi : i < (rule.capture actual).length),
      ParRed Γ (rule.capture actual)[i] (arguments[i]'(by omega)))
    {cn : Name} (hcn : cn = actual.ctorName) {As Cs A' C' : List VExpr}
    (hcapD : A'.take rule.numPrefix ++
      C'.drop (actual.ctorArguments.length - rule.numFields) = arguments)
    (hlA : A'.length = actual.arguments.length) (hlC : C'.length = actual.ctorArguments.length)
    (hAs : List.Forall₂ (EtaNE Γ) As A') (hCs : List.Forall₂ (EtaNE Γ) Cs C') {T : VExpr}
    (hs : Γ ⊢ .app (mkApps (.elim actual.block actual.owner actual.levels) As)
      (mkApps (.const cn actual.ctorLevels) Cs) : T)
    (hdef : Γ ⊢ actual.expr ≡ .app (mkApps (.elim actual.block actual.owner actual.levels) As)
      (mkApps (.const cn actual.ctorLevels) Cs)) :
    ∃ R, RootFire Γ (.app (mkApps (.elim actual.block actual.owner actual.levels) As)
      (mkApps (.const cn actual.ctorLevels) Cs)) R ∧
      EtaNE Γ R (rule.rhs actual.levels arguments) := by
  let actual_s : InductiveSignature.CaseSchema.Application :=
    { actual with arguments := As, ctorName := cn, ctorArguments := Cs }
  have hlAs : As.length = actual.arguments.length :=
    (Lean4Lean.List.Forall₂.length_eq hAs).trans hlA
  have hlCs : Cs.length = actual.ctorArguments.length :=
    (Lean4Lean.List.Forall₂.length_eq hCs).trans hlC
  have hcapη : List.Forall₂ (EtaNE Γ) (rule.capture actual_s) arguments := by
    rw [← hcapD]
    unfold InductiveSignature.CaseSchema.AppliedRule.capture
    simp only [actual_s, hlCs]
    exact List.Forall₂.append' (List.forall₂_take hAs _) (List.forall₂_drop hCs _)
  obtain ⟨_, _, hs₁, hs₂⟩ := hs.app_inv henv hΓ
  have htcap_s : ∀ x ∈ rule.capture actual_s, ∃ T, Γ ⊢ x : T := by
    intro x hx
    unfold InductiveSignature.CaseSchema.AppliedRule.capture at hx
    rcases List.mem_append.1 hx with h | h
    · exact schema_mkApps_arg_type hΓ hs₁ (List.mem_of_mem_take h)
    · exact schema_mkApps_arg_type hΓ hs₂ (List.mem_of_mem_drop h)
  have hcapdef : List.Forall₂ (IsDefEqU Params.env univs Γ)
      (rule.capture actual) (rule.capture actual_s) := by
    have hl2 := Lean4Lean.List.Forall₂.length_eq hcapη
    apply List.forall₂_of_getElem (by omega)
    intro i hi hi'
    obtain ⟨_, ht⟩ := hm.capture_typed (List.getElem_mem hi)
    obtain ⟨_, hts⟩ := htcap_s _ (List.getElem_mem hi')
    have d1 : Γ ⊢ (rule.capture actual)[i] ≡ arguments[i]'(by omega) :=
      ⟨_, ParRed.defeq hΓ (hr i hi) ht⟩
    have d2 := (case_forall₂_get hcapη hi' (by omega)).defeq hΓ hts
    exact d1.trans henv hΓ d2.symm
  have hm_s := hm.transport hΓ (actual' := actual_s) rfl rfl rfl hcn
    (VLevel.forall₂_equiv_refl _) hlAs hlCs hcapdef hdef
  refine ⟨_, .inr ⟨rule, actual_s, hm_s, rfl, rfl⟩, ?_⟩
  simp only [InductiveSignature.CaseSchema.AppliedRule.rhs]
  exact EtaNE.congrRel.instantiateParams_args hcapη

/-- Closure of the eta-normal relation under a parallel core step on the right. -/
theorem EtaNE.parRed_r {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {s X T Y : VExpr}, EtaNE Γ s X → Γ ⊢ s : T → ParRed Γ X Y → EtaNE Γ s Y := by
  intro s X T Y H
  induction H generalizing T Y with
  | bvar | sort | const | elim => intro hs HX; exact .redL (.inl (.inl HX)) EtaNE.rfl
  | @app Γ s₁ X₁ s₂ X₂ H₁ H₂ ih₁ ih₂ =>
    intro hs HX
    obtain ⟨A, B, hs₁, hs₂⟩ := hs.app_inv henv hΓ
    cases HX with
    | app h₁ h₂ => exact .app (ih₁ hΓ hs₁ h₁) (ih₂ hΓ hs₂ h₂)
    | beta hb ha =>
      exact EtaNE.app_lam_inst hΓ (ih₁ hΓ hs₁ (ParRed.lam .rfl hb)) rfl hs₁ hs₂ (ih₂ hΓ hs₂ ha)
    | @extra p r _ m1 m2 _ m2' hp hm hck hargs =>
      have hX := (EtaNE.app H₁ H₂).hasType hΓ hs
      obtain ⟨sp, rfl⟩ := pat_simple hp
      cases sp with
      | defn c => cases hm
      | iota rc mr cc kc =>
        have hm₀ := hm
        obtain ⟨g1, f2, g2, hF, hM, rfl⟩ := Pattern.Matches.app_inv hm
        have hX₁ := hF.const_arguments
        have hX₂ := hM.const_arguments
        subst hX₁ hX₂
        -- the reduced capture spines
        have hvsD := Pattern.Matches.constVarN_of_values (c := rc) (ls := m1) mr
          (fun v => m2' (.inl v))
        have hfsD := Pattern.Matches.constVarN_of_values (c := cc) (ls := f2) kc
          (fun v => m2' (.inr v))
        have hvs := Pattern.Matches.constVarN_forall₂ (R := ParRed Γ) mr hF hvsD
          (fun v => hargs (.inl v))
        have hfs := Pattern.Matches.constVarN_forall₂ (R := ParRed Γ) kc hM hfsD
          (fun v => hargs (.inr v))
        have h₁ := ParRed.congrRel.mkApps (.rfl (e := .const rc m1)) hvs
        have h₂ := ParRed.congrRel.mkApps (.rfl (e := .const cc f2)) hfs
        have E₁ := ih₁ hΓ hs₁ h₁
        have E₂ := ih₂ hΓ hs₂ h₂
        obtain ⟨s₁', hch₁, hc₁⟩ := EtaNE.const_spine_inv hΓ E₁ hs₁ rfl
        obtain ⟨vs_s, rfl, hFs₁⟩ : ∃ vs_s, s₁' = mkApps (.const rc m1) vs_s ∧
            List.Forall₂ (EtaNE Γ) vs_s _ := by
          rcases hc₁ with h | ⟨family, info, params, hl, hcc, -, -, -, -, -, -⟩
          · exact h
          · exfalso
            refine Params.not_rigid_match (us := m1) (hcc ▸ projection_ctor_rigid hl) hp hm₀ ?_
            simp [VExpr.getAppFnArgs_mkApps_head]
        obtain ⟨g1s, hg1s, hr1⟩ :=
          Pattern.Matches.constVarN_transport (R := EtaNE Γ) mr hvsD hFs₁
        obtain ⟨s₂', hch₂, hc₂⟩ := EtaNE.const_spine_inv hΓ E₂ hs₂ rfl
        have hch : ReflTransGen (LStep Γ) (.app s₁ s₂) (.app (mkApps (.const rc m1) vs_s) s₂') :=
          (LStep.chain_app_l hch₁).trans (LStep.chain_app_r hch₂)
        have hs' := LStep.hasType_chain hΓ hch hs
        have hcap : ∀ a, ∃ A, Γ ⊢ Sum.elim g1 g2 a : A := hm₀.hasType hΓ hX
        rcases hc₂ with ⟨fs_s, rfl, hFs₂⟩ |
          ⟨family, info, params, hl, hcc, hp', hi, hs₂', hexp, hlen, hargs₂⟩
        · obtain ⟨g2s, hg2s, hr2⟩ :=
            Pattern.Matches.constVarN_transport (R := EtaNE Γ) kc hfsD hFs₂
          have hm_s := Pattern.Matches.app hg1s hg2s
          have hcap_s := hm_s.hasType hΓ hs'
          have hrel : ∀ a, EtaNE Γ (Sum.elim g1s g2s a) (m2' a) := fun a => by
            cases a with
            | inl v => exact hr1 v
            | inr v => exact hr2 v
          have hck_s := by
            refine Pattern.Check.OK.defeq_values (ck := r.2) (m' := Sum.elim g1s g2s) hΓ (fun a => ?_) hck
            obtain ⟨_, ht⟩ := hcap a
            obtain ⟨_, hts⟩ := hcap_s a
            have e1 : Γ ⊢ Sum.elim g1 g2 a ≡ m2' a := ⟨_, (hargs a).defeq hΓ ht⟩
            have e2 := (hrel a).defeq hΓ hts
            exact e1.trans henv hΓ e2.symm
          have hfire := ParRed.extra hp hm_s hck_s (fun _ => .rfl)
          exact EtaNE.redL_chain hch (.redL (.inl (.inl hfire))
            (EtaNE.congrRel.apply_rhs r.1 hrel))
        · subst hcc
          have hFs₂ : List.Forall₂ (EtaNE Γ) (structArgs family info params s₂') _ :=
            List.forall₂_of_getElem hlen hargs₂
          obtain ⟨g2s, hg2s, hr2⟩ :=
            Pattern.Matches.constVarN_transport (R := EtaNE Γ) kc hfsD hFs₂
          have hm_s : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const info.ctorName).varN kc)).Matches
              (.app (mkApps (.const rc m1) vs_s) (structExpand family info f2 params s₂')) m1
              (Sum.elim g1s g2s) := Pattern.Matches.app hg1s hg2s
          -- typing of the expanded source
          have hexp' : Γ ⊢ structExpand family info f2 params s₂' ≡ s₂' :
              mkApps (.const family f2) params := IsDefEq.structEta hl hp' hi hs₂' hexp
          obtain ⟨_, _, hf', ha'⟩ := hs'.app_inv henv hΓ
          obtain ⟨_, hmT⟩ := hs₂'.isType henv hΓ
          have hconv := (hs₂'.uniqU henv hΓ ha').of_l henv hΓ hmT
          have hsE : Γ ⊢ .app (mkApps (.const rc m1) vs_s) (structExpand family info f2 params s₂') :
              T := hs'.defeqU_l henv hΓ ⟨_, IsDefEq.appDF hf' (.defeqDF hconv hexp'.symm)⟩
          have hcap_s := hm_s.hasType hΓ hsE
          have hrel : ∀ a, EtaNE Γ (Sum.elim g1s g2s a) (m2' a) := fun a => by
            cases a with
            | inl v => exact hr1 v
            | inr v => exact hr2 v
          have hck_s := by
            refine Pattern.Check.OK.defeq_values (ck := r.2) (m' := Sum.elim g1s g2s) hΓ (fun a => ?_) hck
            obtain ⟨_, ht⟩ := hcap a
            obtain ⟨_, hts⟩ := hcap_s a
            have e1 : Γ ⊢ Sum.elim g1 g2 a ≡ m2' a := ⟨_, (hargs a).defeq hΓ ht⟩
            have e2 := (hrel a).defeq hΓ hts
            exact e1.trans henv hΓ e2.symm
          have hfire : RootFire Γ (.app (mkApps (.const rc m1) vs_s)
              (structExpand family info f2 params s₂'))
              (Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr)
                ((Pattern.const info.ctorName).varN kc)) m1 (Sum.elim g1s g2s) r.1) :=
            .inl ⟨_, r, m1, Sum.elim g1s g2s, hp, hm_s, hck_s, rfl⟩
          exact EtaNE.redL_chain hch (.redL (.inr (.root ⟨_, _, family, info, f2, params, rfl, hl,
            hp', hi, hs₂', hexp, hfire⟩)) (EtaNE.congrRel.apply_rhs r.1 hrel))
    | @schema _ arguments rule actual hm hl hr =>
      have hcapP : List.Forall₂ (ParRed Γ) (rule.capture actual) arguments :=
        List.forall₂_of_getElem hl.symm fun i hi _ => hr i hi
      obtain ⟨A', C', hcapD, hA', hC', hlA, hlC⟩ := capture_replace (fun _ => .rfl) hcapP
      have E₁ := ih₁ hΓ hs₁ (ParRed.congrRel.mkApps .rfl hA')
      have E₂ := ih₂ hΓ hs₂ (ParRed.congrRel.mkApps .rfl hC')
      obtain ⟨s₁', As, hch₁, rfl, hAs⟩ := EtaNE.elim_spine_inv hΓ E₁ hs₁ rfl
      obtain ⟨s₂', hch₂, hc₂⟩ := EtaNE.const_spine_inv hΓ E₂ hs₂ rfl
      have hch : ReflTransGen (LStep Γ) (.app s₁ s₂)
          (.app (mkApps (.elim actual.block actual.owner actual.levels) As) s₂') :=
        (LStep.chain_app_l hch₁).trans (LStep.chain_app_r hch₂)
      have hs' := LStep.hasType_chain hΓ hch hs
      have hdef₀ : Γ ⊢ actual.expr ≡
          .app (mkApps (.elim actual.block actual.owner actual.levels) As) s₂' :=
        ((EtaNE.app H₁ H₂).defeq hΓ hs).symm.trans henv hΓ (LStep.defeq_chain hΓ hch hs)
      rcases hc₂ with ⟨Cs, rfl, hCs⟩ |
        ⟨family, info, params, hl', hcc, hp', hi, hs₂', hexp, hlen, hargs₂⟩
      · obtain ⟨R, hfire, hR⟩ :=
          EtaNE.schema_fire hΓ hm hl hr rfl hcapD hlA hlC hAs hCs hs' hdef₀
        exact EtaNE.redL_chain hch (.redL (.inl (.inl hfire.parRed)) hR)
      · have hCs : List.Forall₂ (EtaNE Γ) (structArgs family info params s₂') C' :=
          List.forall₂_of_getElem hlen hargs₂
        have hexp' : Γ ⊢ structExpand family info actual.ctorLevels params s₂' ≡ s₂' :
            mkApps (.const family actual.ctorLevels) params :=
          IsDefEq.structEta hl' hp' hi hs₂' hexp
        obtain ⟨_, _, hf', ha'⟩ := hs'.app_inv henv hΓ
        obtain ⟨_, hmT⟩ := hs₂'.isType henv hΓ
        have hconv := (hs₂'.uniqU henv hΓ ha').of_l henv hΓ hmT
        have hstep : Γ ⊢ .app (mkApps (.elim actual.block actual.owner actual.levels) As) s₂' ≡
            .app (mkApps (.elim actual.block actual.owner actual.levels) As)
              (structExpand family info actual.ctorLevels params s₂') :=
          ⟨_, IsDefEq.appDF hf' (.defeqDF hconv hexp'.symm)⟩
        have hsE := hs'.defeqU_l henv hΓ hstep
        have hdefE := hdef₀.trans henv hΓ hstep
        obtain ⟨R, hfire, hR⟩ :=
          EtaNE.schema_fire hΓ hm hl hr hcc.symm hcapD hlA hlC hAs hCs hsE hdefE
        exact EtaNE.redL_chain hch (.redL (.inr (.root ⟨_, _, family, info, actual.ctorLevels,
          params, rfl, hl', hp', hi, hs₂', hexp, hfire⟩)) hR)
  | @proj Γ m m' S i H ih =>
    intro hs HX
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv hΓ
    generalize hXe : VExpr.proj S i m' = Xe at HX
    cases HX with
    | proj h => cases hXe; exact .proj (ih hΓ hm.hasType.2 h)
    | schema hc =>
      have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hXe
      rw [InductiveSignature.CaseSchema.Application.head] at this
      cases this
    | extra hp hm' =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      cases sp with
      | defn c => cases hm'; cases hXe
      | iota r m c n => cases hm'; cases hXe
    | _ => cases hXe
  | @lamC Γ A A' b b' HA Hb ihA ihb =>
    intro hs HX
    obtain ⟨⟨u, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hAA' : Γ ⊢ A ≡ A' : .sort u := (HA.defeq hΓ hd).of_l henv hΓ hd
    have hX := (EtaNE.lamC HA Hb).hasType hΓ hs
    obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
    generalize hXe : VExpr.lam A' b' = Xe at HX
    cases HX with
    | lam h₁ h₂ =>
      cases hXe
      exact .lamC (ihA hΓ hd h₁) (ihb hΓ' hb (h₂.defeqDFC hΓ (.succ .zero hAA'.symm) hb'))
    | schema hc =>
      have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hXe
      rw [InductiveSignature.CaseSchema.Application.head] at this
      cases this
    | extra hp hm' =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      cases sp with
      | defn c => cases hm'; cases hXe
      | iota r m c n => cases hm'; cases hXe
    | _ => cases hXe
  | @lamD Γ A A' b b' u hA Hb ih =>
    intro hs HX
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.lamD hA Hb).hasType hΓ hs
    obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
    generalize hXe : VExpr.lam A' b' = Xe at HX
    cases HX with
    | lam h₁ h₂ =>
      cases hXe
      exact .lamD (hA.trans (h₁.defeq hΓ hA.hasType.2))
        (ih hΓ' hb (h₂.defeqDFC hΓ (.succ .zero hA.symm) hb'))
    | schema hc =>
      have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hXe
      rw [InductiveSignature.CaseSchema.Application.head] at this
      cases this
    | extra hp hm' =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      cases sp with
      | defn c => cases hm'; cases hXe
      | iota r m c n => cases hm'; cases hXe
    | _ => cases hXe
  | @forallEC Γ A A' B B' HA HB ihA ihB =>
    intro hs HX
    obtain ⟨⟨u, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hAA' : Γ ⊢ A ≡ A' : .sort u := (HA.defeq hΓ hd).of_l henv hΓ hd
    have hX := (EtaNE.forallEC HA HB).hasType hΓ hs
    obtain ⟨-, _, hb'⟩ := hX.forallE_inv henv.ordered
    generalize hXe : VExpr.forallE A' B' = Xe at HX
    cases HX with
    | forallE h₁ h₂ =>
      cases hXe
      exact .forallEC (ihA hΓ hd h₁) (ihB hΓ' hb (h₂.defeqDFC hΓ (.succ .zero hAA'.symm) hb'))
    | schema hc =>
      have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hXe
      rw [InductiveSignature.CaseSchema.Application.head] at this
      cases this
    | extra hp hm' =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      cases sp with
      | defn c => cases hm'; cases hXe
      | iota r m c n => cases hm'; cases hXe
    | _ => cases hXe
  | @funEta Γ e A B A' body u hPi hA Hb ih =>
    intro hs HX
    have hΓ' : OnCtx (A' :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
    have hbody : A' :: Γ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv.ordered
      have h0 : A' :: Γ ⊢ .bvar 0 : A.lift := (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    generalize hXe : VExpr.lam A' body = Xe at HX
    cases HX with
    | lam h₁ h₂ =>
      cases hXe
      have hA'' : Γ ⊢ A' ≡ _ : .sort u := h₁.defeq hΓ hA.hasType.2
      exact .funEta hPi (hA.trans hA'') ((ih hΓ' hbody h₂).defeqDFC hΓ (.succ .zero hA'') hbody)
    | schema hc =>
      have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hXe
      rw [InductiveSignature.CaseSchema.Application.head] at this
      cases this
    | extra hp hm' =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      cases sp with
      | defn c => cases hm'; cases hXe
      | iota r m c n => cases hm'; cases hXe
    | _ => cases hXe
  | @structEta Γ family info levels params args e hl hp hi hs' hexp hlen hargs ih =>
    intro hs HX
    obtain ⟨args', rfl, hF⟩ := ParRed.ctor_spine hl HX
    have hX := (EtaNE.structEta hl hp hi hs' hexp hlen hargs).hasType hΓ hs
    have hlen₂ := Lean4Lean.List.Forall₂.length_eq hF
    have hlenS : (structArgs family info params e).length = params.length + info.numFields := by
      simp [structArgs]
    -- typing of the arguments of the expansion and of the reduct
    have hargsT : ∀ i (hi : i < (structArgs family info params e).length),
        ∃ A, Γ ⊢ (structArgs family info params e)[i] : A := fun i hi => by
      rw [structExpand_eq] at hexp
      exact schema_mkApps_arg_type hΓ hexp (List.getElem_mem hi)
    have hargsX : ∀ i (hi : i < args.length), ∃ A, Γ ⊢ args[i] : A := fun i hi =>
      schema_mkApps_arg_type hΓ hX (List.getElem_mem hi)
    -- the new parameters: the reduced parameter arguments of the reduct
    let params' := args'.take info.nparams
    have hp' : params'.length = info.nparams := by
      simp only [params', List.length_take]; omega
    have hparams : List.Forall₂ (Params.env.IsDefEqU univs Γ) params params' := by
      refine List.forall₂_of_getElem (by omega) fun i hi hi' => ?_
      have hi₁ : i < (structArgs family info params e).length := by omega
      have hi₂ : i < args.length := by omega
      obtain ⟨_, hT⟩ := hargsT i hi₁
      have e1 := (hargs i hi₁ hi₂).defeq hΓ hT
      have hget : (structArgs family info params e)[i] = params[i] := by
        simp [structArgs, List.getElem_append_left hi]
      rw [hget] at e1 hT
      have e2 : Γ ⊢ args[i] ≡ args'[i]'(by omega) :=
        ⟨_, (case_forall₂_get hF hi₂ (by omega)).defeq hΓ (hargsX i hi₂).choose_spec⟩
      have hget' : params'[i]'(by omega) = args'[i]'(by omega) := by simp [params']
      rw [hget']
      exact e1.trans henv hΓ e2
    obtain ⟨_, hTy⟩ := hs'.isType henv hΓ
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hTy⟩
    have hTyEq : Γ ⊢ mkApps (.const family levels) params ≡ mkApps (.const family levels) params' :=
      IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ hparams hTy
    have hs'' : Γ ⊢ e : mkApps (.const family levels) params' := hs'.defeqU_r henv hΓ hTyEq
    have hexp' : Γ ⊢ structExpand family info levels params' e : mkApps (.const family levels) params' := by
      refine (hexp.defeqU_r henv hΓ hTyEq).defeqU_l henv hΓ ?_
      simp only [structExpand_eq] at hexp ⊢
      obtain ⟨_, hhead'⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hexp⟩
      refine IsDefEqU.mkApps_args hΓ ⟨_, hhead'⟩
        (List.Forall₂.append' hparams (List.forall₂_of_getElem rfl fun j hj hj' => ?_)) hexp
      have hjmem : j ∈ List.range info.numFields := by simpa using hj
      obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ hexp
        (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
      simp only [List.getElem_map, List.getElem_range]
      exact ⟨_, hpj⟩
    refine .structEta hl hp' hi hs'' hexp' ?_ fun i hi hi' => ?_
    · simp [structArgs, hp']; omega
    · have hi₂ : i < args.length := by omega
      by_cases hlt : i < info.nparams
      · have hget : (structArgs family info params' e)[i] = args'[i] := by
          simp [structArgs, List.getElem_append_left (show i < params'.length by omega), params']
        rw [hget]
        exact EtaNE.rfl
      · have hi₁ : i < (structArgs family info params e).length := by omega
        have hget : (structArgs family info params' e)[i] = (structArgs family info params e)[i] := by
          simp only [structArgs]
          rw [List.getElem_append_right (by simp [params']; omega),
            List.getElem_append_right (by omega)]
          simp [hp', hp]
        rw [hget]
        obtain ⟨_, hT⟩ := hargsT i hi₁
        exact ih i hi₁ hi₂ hΓ hT (case_forall₂_get hF hi₂ hi')
  | @betaR Γ A b a s' T' args hT Hc ih =>
    intro hs HX
    have hY := HX.hasType hΓ hT
    obtain ⟨H', args', hH, hF, rfl⟩ := ParRed.spine_lamHead rfl HX
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hT⟩
    have hhead' : Γ ⊢ .app (.lam A b) a : _ := hhead
    obtain ⟨A₁, B₁, hlam, ha₁⟩ := hhead'.app_inv henv hΓ
    obtain ⟨B, hPi, hb⟩ := hlam.lam_inv_forallE henv hΓ
    obtain ⟨⟨_, hAA₁⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
    have ha : Γ ⊢ a : A := hAA₁.defeq' ha₁
    rcases ParRed.app_lam_cases hH with ⟨fn', a', hfn, hae, rfl⟩ | ⟨b', a', hb', hae, rfl⟩
    · generalize hfe : VExpr.lam A b = fe at hfn
      cases hfn with
      | @lam _ A₁ A₁' b₁ b₁' hA' hb₁ =>
        cases hfe
        have hstep : ParRed Γ (mkApps (b.inst a) args) (mkApps (b₁'.inst a') args') :=
          ParRed.congrRel.mkApps (ParRed.instN (H₀ := hae) (H₀' := ha) .zero hb₁) hF
        exact .betaR hY (ih hΓ hs hstep)
      | schema hc =>
        have := congrArg (fun e : VExpr => e.getAppFnArgs.1) hfe
        rw [InductiveSignature.CaseSchema.Application.head] at this
        cases this
      | extra hp hm' =>
        obtain ⟨sp, rfl⟩ := pat_simple hp
        cases sp with
        | defn c => cases hm'; cases hfe
        | iota r m c n => cases hm'; cases hfe
      | _ => cases hfe
    · have hstep : ParRed Γ (mkApps (b.inst a) args) (mkApps (b'.inst a') args') :=
        ParRed.congrRel.mkApps (ParRed.instN (H₀ := hae) (H₀' := ha) .zero hb') hF
      exact ih hΓ hs hstep
  | redL h _ ih => intro hs HX; exact .redL h (ih hΓ (h.hasType hΓ hs) HX)

/-! ## Closure under parallel unfolding steps -/

omit [Params] in
theorem forall₂_snoc_inv {α β : Type _} {R : α → β → Prop} {l : List α} {a : α} {l' : List β}
    (h : List.Forall₂ R (l ++ [a]) l') : ∃ l₀ b, l' = l₀ ++ [b] ∧ List.Forall₂ R l l₀ ∧ R a b := by
  induction l generalizing l' with
  | nil =>
    simp only [List.nil_append] at h
    cases h with | cons hab hnil => cases hnil; exact ⟨[], _, rfl, .nil, hab⟩
  | cons y l ih =>
    cases h with | cons hy ht =>
      obtain ⟨l₀, b, rfl, h1, h2⟩ := ih ht
      exact ⟨_ :: l₀, b, rfl, .cons hy h1, h2⟩

theorem LStep.chain_proj {Γ : List VExpr} {m m' : VExpr} {S : Name} {i : Nat}
    (h : ReflTransGen (LStep Γ) m m') :
    ReflTransGen (LStep Γ) (.proj S i m) (.proj S i m') := by
  induction h with
  | rfl => exact .rfl
  | tail _ hstep ih => exact ih.tail (LStep.proj hstep)

theorem EtaNE.argRel : ArgRel EtaNE :=
  EtaNE.congrRel.argRel fun hΓ h ha => (h.defeq hΓ ha).of_l henv hΓ ha

/-- A change of binder domains by typed conversion is absorbed by `lamD`. -/
theorem EtaNE.wrapLams_defeq {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {ds ds' : List VExpr} {res res' body body' : VExpr}, ds.length = ds'.length →
      Γ ⊢ VExpr.wrapForalls ds res ≡ VExpr.wrapForalls ds' res' →
      EtaNE (ds.reverse ++ Γ) body body' →
      EtaNE Γ (VExpr.wrapLams ds body) (VExpr.wrapLams ds' body') := by
  intro ds
  induction ds generalizing Γ with
  | nil =>
    intro ds' res res' body body' hlen hfa hb
    cases ds' with
    | nil => exact hb
    | cons => simp at hlen
  | cons d ds ih =>
    intro ds' res res' body body' hlen hfa hb
    cases ds' with
    | nil => simp at hlen
    | cons d' ds' =>
      have hfa' : Γ ⊢ .forallE d (VExpr.wrapForalls ds res) ≡
          .forallE d' (VExpr.wrapForalls ds' res') := hfa
      obtain ⟨⟨u, hd⟩, _, hB⟩ := IsDefEqU.forallE_inv henv hΓ hfa'
      have hΓ' : OnCtx (d :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd.hasType.1⟩
      have hb' : EtaNE (ds.reverse ++ (d :: Γ)) body body' := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hb
      exact .lamD hd (ih hΓ' (by simpa using hlen) ⟨_, hB⟩ hb')

/-- Replay a prefix unfolding (singleton or quotient) fired on the reduct at the source: the
source spine unfolds at convertible arguments, and the two right-hand sides are related by
congruence under a change of binder domains. -/
theorem EtaNE.unfold_r {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    {U : List VExpr → VExpr → Prop} {name : Name} {ls : List VLevel}
    (huniq : ∀ {a r r'}, U a r → U a r' → r = r')
    (hcongr : ∀ {a a' r}, U a r → List.Forall₂ (IsDefEqU Params.env univs Γ) a a' → ∃ r', U a' r')
    (hrel : ∀ {a a' r}, U a r → List.Forall₂ (EtaNE Γ) a a' →
      ∃ r', U a' r' ∧ ∃ ds ds' body body' res res', r = VExpr.wrapLams ds body ∧
        r' = VExpr.wrapLams ds' body' ∧ ds.length = ds'.length ∧
        IsDefEqU Params.env univs Γ (VExpr.wrapForalls ds res) (VExpr.wrapForalls ds' res') ∧
        EtaNE (ds.reverse ++ Γ) body body')
    (hstep : ∀ {a r}, U a r → DeltaPar Γ (mkApps (.const name ls) a) r)
    (hrig : ∀ {a r}, U a r → ¬ Params.env.Rigid name)
    {s T : VExpr} {args' : List VExpr} {rhs : VExpr}
    (H : EtaNE Γ s (mkApps (.const name ls) args')) (hs : Γ ⊢ s : T) (hr : U args' rhs) :
    EtaNE Γ s rhs := by
  obtain ⟨s', hch, hc⟩ := EtaNE.const_spine_inv hΓ H hs rfl
  obtain ⟨args_s, rfl, hFs⟩ : ∃ args_s, s' = mkApps (.const name ls) args_s ∧
      List.Forall₂ (EtaNE Γ) args_s args' := by
    rcases hc with h | ⟨family, info, params, hl, hcc, -, -, -, -, -, -⟩
    · exact h
    · exact (hrig hr (hcc ▸ projection_ctor_rigid hl)).elim
  have hs' := LStep.hasType_chain hΓ hch hs
  have hdef : List.Forall₂ (IsDefEqU Params.env univs Γ) args' args_s := by
    refine List.forall₂_of_getElem (Lean4Lean.List.Forall₂.length_eq hFs).symm fun i hi hi' => ?_
    obtain ⟨_, ht⟩ := schema_mkApps_arg_type hΓ hs' (List.getElem_mem hi')
    exact ((case_forall₂_get hFs hi' hi).defeq hΓ ht).symm
  obtain ⟨rhs_s, hr_s⟩ := hcongr hr hdef
  obtain ⟨rhs', hr', ds, ds', body, body', res, res', rfl, rfl, hlen, hfa, hb⟩ := hrel hr_s hFs
  cases huniq hr hr'
  exact EtaNE.redL_chain hch (.redL (.inl (.inr (hstep hr_s))) (EtaNE.wrapLams_defeq hΓ hlen hfa hb))

/-- A parallel unfolding step on a spine with a `λ` head moves the head and the arguments
separately. -/
theorem DeltaPar.spine_lamHead {Γ : List VExpr} {A b a Y : VExpr} {args : List VExpr}
    (H : DeltaPar Γ (mkApps (.app (.lam A b) a) args) Y) :
    ∃ A' b' a' args', DeltaPar Γ A A' ∧ DeltaPar (A :: Γ) b b' ∧ DeltaPar Γ a a' ∧
      List.Forall₂ (DeltaPar Γ) args args' ∧ Y = mkApps (.app (.lam A' b') a') args' := by
  induction args using List.snoc_induction generalizing Y with
  | nil =>
    obtain ⟨f', a', rfl, hf, ha⟩ := DeltaPar.app_inv_head (h := .lam A b) (as := [])
      (by intros; intro h; cases h) (by intros; intro h; cases h) H
    obtain ⟨A', b', hA, hb, rfl⟩ := DeltaPar.lam_inv hf
    exact ⟨A', b', a', [], hA, hb, ha, .nil, rfl⟩
  | snoc args₀ x ih =>
    rw [VExpr.mkApps_snoc] at H
    obtain ⟨f', x', rfl, hf, hx⟩ := DeltaPar.app_inv_head (h := .lam A b) (as := a :: args₀)
      (by intros; intro h; cases h) (by intros; intro h; cases h) H
    obtain ⟨A', b', a', args₀', hA, hb, ha, hF, rfl⟩ := ih hf
    exact ⟨A', b', a', args₀' ++ [x'], hA, hb, ha, List.Forall₂.append' hF (.cons hx .nil),
      (VExpr.mkApps_snoc ..).symm⟩

/-- The structure-eta case of the closures: the reduct's arguments move to convertible
arguments, related to the expansion's arguments. -/
theorem EtaNE.structEta_args {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    {family : Name} {info : VProjectionInfo} {levels : List VLevel} {params args args' : List VExpr}
    {e T : VExpr} (hl : Params.env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hs' : Γ ⊢ e : mkApps (.const family levels) params)
    (hexp : Γ ⊢ structExpand family info levels params e : mkApps (.const family levels) params)
    (hlen : (structArgs family info params e).length = args.length)
    (hargs : ∀ i (hi : i < (structArgs family info params e).length) (hi' : i < args.length),
      EtaNE Γ (structArgs family info params e)[i] args[i])
    (_hX : Γ ⊢ mkApps (.const info.ctorName levels) args : T)
    (hF : List.Forall₂ (IsDefEqU Params.env univs Γ) args args')
    (ih : ∀ i (hi : i < (structArgs family info params e).length) (hi' : i < args'.length),
      EtaNE Γ (structArgs family info params e)[i] args'[i]) :
    EtaNE Γ e (mkApps (.const info.ctorName levels) args') := by
  have hlen₂ := Lean4Lean.List.Forall₂.length_eq hF
  have hlenS : (structArgs family info params e).length = params.length + info.numFields := by
    simp [structArgs]
  have hargsT : ∀ i (hi : i < (structArgs family info params e).length),
      ∃ A, Γ ⊢ (structArgs family info params e)[i] : A := fun i hi => by
    rw [structExpand_eq] at hexp
    exact schema_mkApps_arg_type hΓ hexp (List.getElem_mem hi)
  let params' := args'.take info.nparams
  have hp' : params'.length = info.nparams := by
    simp only [params', List.length_take]; omega
  have hparams : List.Forall₂ (Params.env.IsDefEqU univs Γ) params params' := by
    refine List.forall₂_of_getElem (by omega) fun i hi hi' => ?_
    have hi₁ : i < (structArgs family info params e).length := by omega
    have hi₂ : i < args.length := by omega
    obtain ⟨_, hT⟩ := hargsT i hi₁
    have e1 := (hargs i hi₁ hi₂).defeq hΓ hT
    have hget : (structArgs family info params e)[i] = params[i] := by
      simp [structArgs, List.getElem_append_left hi]
    rw [hget] at e1
    have e2 : Γ ⊢ args[i] ≡ args'[i]'(by omega) := case_forall₂_get hF hi₂ (by omega)
    have hget' : params'[i]'(by omega) = args'[i]'(by omega) := by simp [params']
    rw [hget']
    exact e1.trans henv hΓ e2
  obtain ⟨_, hTy⟩ := hs'.isType henv hΓ
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hTy⟩
  have hTyEq : Γ ⊢ mkApps (.const family levels) params ≡ mkApps (.const family levels) params' :=
    IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ hparams hTy
  have hs'' : Γ ⊢ e : mkApps (.const family levels) params' := hs'.defeqU_r henv hΓ hTyEq
  have hexp' : Γ ⊢ structExpand family info levels params' e :
      mkApps (.const family levels) params' := by
    refine (hexp.defeqU_r henv hΓ hTyEq).defeqU_l henv hΓ ?_
    simp only [structExpand_eq] at hexp ⊢
    obtain ⟨_, hhead'⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hexp⟩
    refine IsDefEqU.mkApps_args hΓ ⟨_, hhead'⟩
      (List.Forall₂.append' hparams (List.forall₂_of_getElem rfl fun j hj hj' => ?_)) hexp
    have hjmem : j ∈ List.range info.numFields := by simpa using hj
    obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ hexp
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
    simp only [List.getElem_map, List.getElem_range]
    exact ⟨_, hpj⟩
  refine .structEta hl hp' hi hs'' hexp' ?_ fun i hi hi' => ?_
  · simp [structArgs, hp']; omega
  · by_cases hlt : i < info.nparams
    · have hget : (structArgs family info params' e)[i] = args'[i] := by
        simp [structArgs, List.getElem_append_left (show i < params'.length by omega), params']
      rw [hget]
      exact EtaNE.rfl
    · have hi₁ : i < (structArgs family info params e).length := by omega
      have hget : (structArgs family info params' e)[i] = (structArgs family info params e)[i] := by
        simp only [structArgs]
        rw [List.getElem_append_right (by simp [params']; omega),
          List.getElem_append_right (by omega)]
        simp [hp', hp]
      rw [hget]
      exact ih i hi₁ hi'

/-- Closure of the eta-normal relation under a parallel unfolding step on the right. -/
theorem EtaNE.deltaPar_r {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {s X T Y : VExpr}, EtaNE Γ s X → Γ ⊢ s : T → DeltaPar Γ X Y → EtaNE Γ s Y := by
  intro s X T Y H
  induction H generalizing T Y with
  | bvar | sort | const | elim => intro hs HX; exact .redL (.inl (.inr HX)) EtaNE.rfl
  | @app Γ s₁ X₁ s₂ X₂ H₁ H₂ ih₁ ih₂ =>
    intro hs HX
    obtain ⟨A, B, hs₁, hs₂⟩ := hs.app_inv henv hΓ
    generalize hE : VExpr.app X₁ X₂ = E at HX
    cases HX with
    | app h₁ h₂ => cases hE; exact .app (ih₁ hΓ hs₁ h₁) (ih₂ hΓ hs₂ h₂)
    | @delta _ name ls rhs args args' hlen hd hr =>
      rcases mkApps_const_eq_cases hE.symm with ⟨_, he⟩ | ⟨args₀, x, rfl, he⟩
      · cases he
      · cases he
        obtain ⟨args₀', x', rfl, hF₀, hx⟩ :=
          forall₂_snoc_inv (List.forall₂_of_getElem hlen hd)
        have E : EtaNE Γ (.app s₁ s₂) (mkApps (.const name ls) (args₀' ++ [x'])) := by
          rw [VExpr.mkApps_snoc]
          exact .app (ih₁ hΓ hs₁ (DeltaPar.congrRel.mkApps .rfl hF₀)) (ih₂ hΓ hs₂ hx)
        exact EtaNE.unfold_r hΓ (U := PrefixUnfold Params.env univs Params.recursorData Γ name ls)
          PrefixUnfold.unique (fun h ha => PrefixUnfold.congr_defeq hΓ h ha)
          (fun h ha => PrefixUnfold.congr_rel EtaNE.argRel hΓ h ha)
          (fun h => .delta rfl (fun _ _ _ => .rfl) h) (fun h => h.not_rigid) E hs hr
    | @quotDelta _ ls rhs args args' hlen hd hr =>
      rcases mkApps_const_eq_cases hE.symm with ⟨_, he⟩ | ⟨args₀, x, rfl, he⟩
      · cases he
      · cases he
        obtain ⟨args₀', x', rfl, hF₀, hx⟩ :=
          forall₂_snoc_inv (List.forall₂_of_getElem hlen hd)
        have E : EtaNE Γ (.app s₁ s₂) (mkApps (.const ``Quot.lift ls) (args₀' ++ [x'])) := by
          rw [VExpr.mkApps_snoc]
          exact .app (ih₁ hΓ hs₁ (DeltaPar.congrRel.mkApps .rfl hF₀)) (ih₂ hΓ hs₂ hx)
        exact EtaNE.unfold_r hΓ (U := QuotPrefixUnfold Params.env univs Γ ls)
          QuotPrefixUnfold.unique (fun h ha => QuotPrefixUnfold.congr_defeq hΓ h ha)
          (fun h ha => QuotPrefixUnfold.congr_rel EtaNE.argRel hΓ h ha)
          (fun h => .quotDelta rfl (fun _ _ _ => .rfl) h) (fun h => h.not_rigid) E hs hr
    | _ => cases hE
  | @proj Γ m m' S i H ih =>
    intro hs HX
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv hΓ
    have hX := (EtaNE.proj H).hasType hΓ hs
    generalize hE : VExpr.proj S i m' = E at HX
    cases HX with
    | proj h => cases hE; exact .proj (ih hΓ hm.hasType.2 h)
    | @projIota _ family info index ls fieldType field args args' hlen hd hl hsI hfi ht =>
      injection hE with hf hidx hM
      subst hf hidx hM
      have hF : List.Forall₂ (DeltaPar Γ) args args' := List.forall₂_of_getElem hlen hd
      have hstep : DeltaPar Γ (mkApps (.const info.ctorName ls) args)
          (mkApps (.const info.ctorName ls) args') := DeltaPar.congrRel.mkApps .rfl hF
      have E := ih hΓ hm.hasType.2 hstep
      have hX' : Γ ⊢ .proj S i (mkApps (.const info.ctorName ls) args') : T :=
        (DeltaPar.full (.proj hstep)).hasType hΓ hX
      have hTfield : Γ ⊢ Y : T :=
        ht.defeqU_r henv hΓ (hsI.uniqU henv hΓ hX')
      obtain ⟨m_s, hch, hc⟩ := EtaNE.const_spine_inv hΓ E hm.hasType.2 rfl
      have hchP : ReflTransGen (LStep Γ) (.proj S i m) (.proj S i m_s) := LStep.chain_proj hch
      have hsP := LStep.hasType_chain hΓ hchP hs
      rcases hc with ⟨args_s, rfl, hFs⟩ |
        ⟨family', info', params, hl', hcc, hp', hi', hs_m, hexp, hlenS, hargsS⟩
      · obtain ⟨field_s, hfs, hrel⟩ := forall₂_getElem?_right hFs hfi
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm_s, _, _⟩ := hsP.proj_inv henv hΓ
        obtain ⟨_, hts⟩ := schema_mkApps_arg_type hΓ hm_s.hasType.2 (List.mem_of_getElem? hfs)
        have hTfield_s : Γ ⊢ field_s : T :=
          hTfield.defeqU_l henv hΓ (hrel.defeq hΓ hts).symm
        have hδ : DeltaPar Γ (.proj S i (mkApps (.const info.ctorName ls) args_s)) field_s :=
          .projIota rfl (fun _ _ _ => .rfl) hl hsP hfs hTfield_s
        exact EtaNE.redL_chain hchP (.redL (.inl (.inr hδ)) hrel)
      · obtain ⟨rfl, hl''⟩ := struct_family_eq hΓ hl' hs_m hsP
        cases henv.ordered.projections_unique hl hl''
        obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hfi
        have hlt' : info.nparams + i < (structArgs family' info params m_s).length := by omega
        have hgetS : (structArgs family' info params m_s)[info.nparams + i] = .proj family' i m_s := by
          simp only [structArgs]
          rw [List.getElem_append_right (by omega)]
          simp [hp']
        have := hargsS (info.nparams + i) hlt' hlt
        rw [hgetS, hget] at this
        exact EtaNE.redL_chain hchP this
    | delta => exact absurd hE.symm mkApps_const_ne_proj
    | quotDelta => exact absurd hE.symm mkApps_const_ne_proj
    | _ => cases hE
  | @lamC Γ A A' b b' HA Hb ihA ihb =>
    intro hs HX
    obtain ⟨⟨u, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hAA' : Γ ⊢ A ≡ A' : .sort u := (HA.defeq hΓ hd).of_l henv hΓ hd
    have hX := (EtaNE.lamC HA Hb).hasType hΓ hs
    obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
    obtain ⟨A₂, b₂, h₁, h₂, rfl⟩ := DeltaPar.lam_inv HX
    exact .lamC (ihA hΓ hd h₁) (ihb hΓ' hb (h₂.defeqDFC hΓ (.succ .zero hAA'.symm) hb'))
  | @lamD Γ A A' b b' u hA Hb ih =>
    intro hs HX
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.lamD hA Hb).hasType hΓ hs
    obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
    obtain ⟨A₂, b₂, h₁, h₂, rfl⟩ := DeltaPar.lam_inv HX
    exact .lamD (hA.trans ((DeltaPar.full h₁).defeq hΓ hA.hasType.2))
      (ih hΓ' hb (h₂.defeqDFC hΓ (.succ .zero hA.symm) hb'))
  | @forallEC Γ A A' B B' HA HB ihA ihB =>
    intro hs HX
    obtain ⟨⟨u, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hAA' : Γ ⊢ A ≡ A' : .sort u := (HA.defeq hΓ hd).of_l henv hΓ hd
    have hX := (EtaNE.forallEC HA HB).hasType hΓ hs
    obtain ⟨-, _, hb'⟩ := hX.forallE_inv henv.ordered
    obtain ⟨A₂, B₂, h₁, h₂, rfl⟩ := DeltaPar.forallE_inv HX
    exact .forallEC (ihA hΓ hd h₁) (ihB hΓ' hb (h₂.defeqDFC hΓ (.succ .zero hAA'.symm) hb'))
  | @funEta Γ e A B A' body u hPi hA Hb ih =>
    intro hs HX
    have hΓ' : OnCtx (A' :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
    have hbody : A' :: Γ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv.ordered
      have h0 : A' :: Γ ⊢ .bvar 0 : A.lift := (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    obtain ⟨A₂, body₂, h₁, h₂, rfl⟩ := DeltaPar.lam_inv HX
    have hA'' : Γ ⊢ A' ≡ A₂ : .sort u := (DeltaPar.full h₁).defeq hΓ hA.hasType.2
    exact .funEta hPi (hA.trans hA'') ((ih hΓ' hbody h₂).defeqDFC hΓ (.succ .zero hA'') hbody)
  | @structEta Γ family info levels params args e hl hp hi hs' hexp hlen hargs ih =>
    intro hs HX
    obtain ⟨args', rfl, hF⟩ := DeltaPar.rigid_spine (projection_ctor_rigid hl) HX
    have hX := (EtaNE.structEta hl hp hi hs' hexp hlen hargs).hasType hΓ hs
    have hargsX : ∀ x ∈ args, ∃ A, Γ ⊢ x : A := fun x hx => schema_mkApps_arg_type hΓ hX hx
    have hFd : List.Forall₂ (IsDefEqU Params.env univs Γ) args args' :=
      List.forall₂_of_getElem (Lean4Lean.List.Forall₂.length_eq hF) fun i hi hi' =>
        ⟨_, (DeltaPar.full (case_forall₂_get hF hi hi')).defeq hΓ
          (hargsX _ (List.getElem_mem hi)).choose_spec⟩
    refine EtaNE.structEta_args hΓ hl hp hi hs' hexp hlen hargs hX hFd fun i hi₁ hi' => ?_
    have hi₂ : i < args.length := by omega
    have hT : ∃ A, Γ ⊢ (structArgs family info params e)[i] : A := by
      rw [structExpand_eq] at hexp
      exact schema_mkApps_arg_type hΓ hexp (List.getElem_mem hi₁)
    exact ih i hi₁ hi₂ hΓ hT.choose_spec (case_forall₂_get hF hi₂ hi')
  | @betaR Γ A b a s' T' args hT Hc ih =>
    intro hs HX
    have hY := (DeltaPar.full HX).hasType hΓ hT
    obtain ⟨A', b', a', args', hA, hb', ha', hF, rfl⟩ := DeltaPar.spine_lamHead HX
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hT⟩
    have hhead' : Γ ⊢ .app (.lam A b) a : _ := hhead
    obtain ⟨A₁, B₁, hlam, ha₁⟩ := hhead'.app_inv henv hΓ
    obtain ⟨B, hPi, hb⟩ := hlam.lam_inv_forallE henv hΓ
    obtain ⟨⟨_, hAA₁⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
    have ha : Γ ⊢ a : A := hAA₁.defeq' ha₁
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hAA₁.hasType.1⟩
    have hstep : DeltaPar Γ (mkApps (b.inst a) args) (mkApps (b'.inst a') args') :=
      DeltaPar.congrRel.mkApps (DeltaPar.instN .zero hΓ' ha' ha hb' hb) hF
    exact .betaR hY (ih hΓ hs hstep)
  | redL h _ ih => intro hs HX; exact .redL h (ih hΓ (h.hasType hΓ hs) HX)

/-- The closure of the eta-normal relation under eta-free parallel steps on the right. -/
theorem upStepFClosure : UpStepFClosure := by
  intro Γ s X Y T hΓ hs H HX
  rcases HX with h | h
  · exact EtaNE.parRed_r hΓ H hs h
  · exact EtaNE.deltaPar_r hΓ H hs h

end

/-- `Cancel ↔ TypedFront`, with the replay obligation discharged: the remaining hypotheses are
the three guard descents (`CaseRedexDescends`, `UnfoldingCheckDescends`, `MajorEtaDescends`) and
the projection and eliminator closures (`ProjFrontN`, `ElimFrontN`). -/
theorem cancel_iff_typedFront_B3 {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U))
    (hProj : ProjFrontN env) (hElim : ElimFrontN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  cancel_iff_typedFront_of_closure henv heq hcase hunfold hmajor
    (fun U => @upStepFClosure (henv.params U)) hProj hElim

end Lean4Lean.VEnv.StrengtheningEtaClosure
