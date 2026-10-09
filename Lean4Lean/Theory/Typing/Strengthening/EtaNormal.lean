import Lean4Lean.Theory.Typing.Strengthening.Exposure

/-! # The eta-normal relation

Direction B3. `EtaNE Γ s X` ("`X` is an eta-normal
reduct of `s`") is the relation between a source and the terms that eta expansions and eta-free
steps produce above a lift, organised so that eta-free steps are recorded on the *source side*
(`redL`) and eta expansions on the *reduct side*:

* the untyped congruences (`bvar`, `sort`, `const`, `elim`, `app`, `proj`, `lamC`, `forallEC`);
* `funEta`: a source of function type expands to a lambda whose body is related to the source
  applied to the new variable;
* `structEta`: a source of structure type expands to a constructor application whose arguments
  are related to the parameters and the projections of the source;
* `betaR`: the reduct may carry the administrative redex left by a junk expansion of a lambda or
  of a partial application, when the source is related to its contractum;
* `redL`: the source may take a step (`LStep`): an eta-free parallel step (`UpStepF`: `ParRed` or
  `DeltaPar`), or structure eta at a firing major followed by the iota (`MajorEtaIota`).

`EtaNE` is closed under eta steps on the right (`EtaNE.etaPar_r`), so it contains every eta chain
(`EtaNE.of_etaChain`); its closure under eta-free steps on the right is the content of the replay
obligation (`EtaClosure.lean`). The end lemma `EtaNE.forallE_inv_lift` descends the `redL` steps
at the root of a lift (`Replay.lean`'s descents) and finds the `Π` below. -/

namespace Lean4Lean.VEnv.StrengtheningEtaNormal
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure

/-- The arguments of the structure eta expansion of `e`: the parameters and the projections. -/
def structArgs (family : Name) (info : VProjectionInfo) (params : List VExpr) (e : VExpr) :
    List VExpr :=
  params ++ (List.range info.numFields).map fun i => VExpr.proj family i e

theorem structExpand_eq (family : Name) (info : VProjectionInfo) (levels : List VLevel)
    (params : List VExpr) (e : VExpr) :
    structExpand family info levels params e =
      mkApps (.const info.ctorName levels) (structArgs family info params e) := rfl

theorem structArgs_lift' (family : Name) (info : VProjectionInfo) (params : List VExpr)
    (e : VExpr) (l : Lift) :
    structArgs family info (params.map (·.lift' l)) (e.lift' l) =
      (structArgs family info params e).map (·.lift' l) := by
  simp [structArgs, List.map_append, List.map_map, Function.comp_def]

theorem structArgs_liftN (family : Name) (info : VProjectionInfo) (params : List VExpr)
    (e : VExpr) (n k : Nat) :
    structArgs family info (params.map (·.liftN n k)) (e.liftN n k) =
      (structArgs family info params e).map (·.liftN n k) := by
  simp [structArgs, List.map_append, List.map_map, Function.comp_def, liftN]

theorem structArgs_inst (family : Name) (info : VProjectionInfo) (params : List VExpr)
    (e a : VExpr) (k : Nat) :
    structArgs family info (params.map (·.inst a k)) (e.inst a k) =
      (structArgs family info params e).map (·.inst a k) := by
  simp [structArgs, List.map_append, List.map_map, Function.comp_def, inst]

theorem lift_lift'_cons (e : VExpr) (l : Lift) : (lift e).lift' (.cons l) = lift (e.lift' l) := by
  show (liftN 1 e 0).lift' (.cons l) = liftN 1 (e.lift' l) 0
  rw [← lift'_consN_skipN, ← lift'_consN_skipN, ← lift'_comp, ← lift'_comp]
  simp

theorem lift'_mkApps (f : VExpr) (args : List VExpr) (l : Lift) :
    (mkApps f args).lift' l = mkApps (f.lift' l) (args.map (·.lift' l)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

theorem mkApps_eq_cases' {H Z : VExpr} {args : List VExpr} (he : mkApps H args = Z) :
    (args = [] ∧ Z = H) ∨ ∃ args₀ x, args = args₀ ++ [x] ∧ Z = .app (mkApps H args₀) x := by
  rcases eq_nil_or_snoc' args with rfl | ⟨args₀, x, rfl⟩
  · exact .inl ⟨rfl, he.symm⟩
  · exact .inr ⟨args₀, x, rfl, by rw [← he, VExpr.mkApps_snoc]⟩

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => Params.env.IsDefEq univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => Params.env.IsDefEqU univs Γ e1 e2

/-! ## Eta-free parallel steps -/

/-- An eta-free parallel step: a parallel core step or a parallel delta step. -/
def UpStepF (Γ : List VExpr) (a b : VExpr) : Prop := ParRed Γ a b ∨ DeltaPar Γ a b

theorem UpStepF.upStep {Γ : List VExpr} {a b : VExpr} (h : UpStepF Γ a b) : UpStep Γ a b :=
  h.elim .inl (.inr ∘ .inl)

theorem UpStepF.full {Γ : List VExpr} {a b : VExpr} (h : UpStepF Γ a b) : FullReduction Γ a b :=
  h.elim (fun h => .tail .rfl (.core h)) DeltaPar.full

theorem UpStepF.defeq {Γ : List VExpr} {a b A : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (h : UpStepF Γ a b) (ha : Γ ⊢ a : A) : Γ ⊢ a ≡ b : A :=
  h.elim (fun h => h.defeq hΓ ha) (fun h => (DeltaPar.full h).defeq hΓ ha)

theorem UpStepF.hasType {Γ : List VExpr} {a b A : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (h : UpStepF Γ a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := (h.defeq hΓ ha).hasType.2

theorem UpStepF.weakN {Γ Γ' : List VExpr} {n k : Nat} {a b : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (h : UpStepF Γ a b) : UpStepF Γ' (a.liftN n k) (b.liftN n k) :=
  h.elim (fun h => .inl (h.weakN W)) (fun h => .inr (h.weakN W))

theorem UpStepF.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {a b A : VExpr}
    (hΓ : OnCtx Γ₀ (Params.env.IsType univs)) (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (h : UpStepF Γ₁ a b) (ha : Γ₁ ⊢ a : A) : UpStepF Γ₂ a b :=
  h.elim (fun h => .inl (h.defeqDFC hΓ W ha)) (fun h => .inr (h.defeqDFC hΓ W ha))

theorem UpStepF.instN {Γ₀ Γ₁ Γ : List VExpr} {a₁ A₀ e e' T : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ a₁ : A₀) (h : UpStepF Γ₁ e e') (he : Γ₁ ⊢ e : T) :
    UpStepF Γ (e.inst a₁ k) (e'.inst a₁ k) :=
  h.elim (fun h => .inl (ParRed.instN (H₀ := ParRed.rfl) (H₀' := h₀) W h))
    (fun h => .inr (DeltaPar.instN W hΓ₁ DeltaPar.rfl h₀ h he))

/-! ## Structure eta at a firing major

The one eta step that an eta-free step above may force on the source: a neutral major of
structure type is expanded and the parallel core step (an iota) consumes the expansion. -/

/-- A redex fired at the root with its arguments left in place: a stored rule (`ParRed.extra`
with the identity on the values) or a case step (`ParRed.schema` with the identity on the
captures). Recording the shape of the step (rather than an arbitrary `ParRed`) is what makes the
descent of the composite step below (`MajorEtaDescends`) plausible: the right-hand side of an
iota at a structure constructor does not read the parameters of the constructor spine
(`pat_iota_params`, `schema_struct_major`). -/
def RootFire (Γ : List VExpr) (X c : VExpr) : Prop :=
  (∃ (p : Pattern) (r : p.RHS × p.Check) (m1 : List VLevel) (m2 : p.Path → VExpr),
    Pat p r ∧ p.Matches X m1 m2 ∧ r.2.OK (IsDefEqU Params.env univs Γ) m1 m2 ∧
    c = r.1.apply m1 m2) ∨
  (∃ (rule : InductiveSignature.CaseSchema.AppliedRule)
    (actual : InductiveSignature.CaseSchema.Application),
    CaseRedex Params.env univs Γ rule actual ∧ X = actual.expr ∧
    c = rule.rhs actual.levels (rule.capture actual))

theorem RootFire.parRed {Γ : List VExpr} {X c : VExpr} (h : RootFire Γ X c) : ParRed Γ X c := by
  rcases h with ⟨p, r, m1, m2, hp, hm, hck, rfl⟩ | ⟨rule, actual, hm, rfl, rfl⟩
  · exact .extra hp hm hck fun _ => .rfl
  · exact .schema hm rfl fun _ _ => .rfl

theorem RootFire.weakN {Γ Γ' : List VExpr} {n k : Nat} {X c : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (h : RootFire Γ X c) : RootFire Γ' (X.liftN n k) (c.liftN n k) := by
  rcases h with ⟨p, r, m1, m2, hp, hm, hck, rfl⟩ | ⟨rule, actual, hm, rfl, rfl⟩
  · exact .inl ⟨p, r, m1, fun a => (m2 a).liftN n k, hp,
      Pattern.matches_liftN.2 ⟨_, hm, fun _ => rfl⟩, hck.weakN W, Pattern.RHS.liftN_apply r.1⟩
  · have hc : (rule.body.rhs.instL actual.levels).ClosedN (rule.capture actual).length :=
      hm.source.closed.2.1.instL
    refine .inr ⟨rule, CaseApplicationMap actual fun e => e.liftN n k, hm.weakN henv W,
      (case_application_liftN actual).symm, ?_⟩
    show (rule.rhs actual.levels (rule.capture actual)).liftN n k =
      rule.rhs actual.levels (rule.capture (CaseApplicationMap actual fun e => e.liftN n k))
    rw [case_capture_map]
    simp only [InductiveSignature.CaseSchema.AppliedRule.rhs]
    exact instantiateParams_liftN hc

theorem RootFire.instN {Γ₀ Γ₁ Γ : List VExpr} {a₁ A₀ X c : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (h₀ : Γ₀ ⊢ a₁ : A₀) (h : RootFire Γ₁ X c) :
    RootFire Γ (X.inst a₁ k) (c.inst a₁ k) := by
  rcases h with ⟨p, r, m1, m2, hp, hm, hck, rfl⟩ | ⟨rule, actual, hm, rfl, rfl⟩
  · exact .inl ⟨p, r, m1, fun a => (m2 a).inst a₁ k, hp, Pattern.matches_instN hm,
      hck.instN W h₀, Pattern.RHS.instN_apply r.1⟩
  · have hc : (rule.body.rhs.instL actual.levels).ClosedN (rule.capture actual).length :=
      hm.source.closed.2.1.instL
    refine .inr ⟨rule, CaseApplicationMap actual fun e => e.inst a₁ k, hm.instN henv h₀ W,
      (case_application_instN actual).symm, ?_⟩
    show (rule.rhs actual.levels (rule.capture actual)).inst a₁ k =
      rule.rhs actual.levels (rule.capture (CaseApplicationMap actual fun e => e.inst a₁ k))
    rw [case_capture_map]
    simp only [InductiveSignature.CaseSchema.AppliedRule.rhs]
    exact instantiateParams_instN hc

theorem RootFire.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {X c : VExpr}
    (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) (h : RootFire Γ₁ X c) : RootFire Γ₂ X c := by
  rcases h with ⟨p, r, m1, m2, hp, hm, hck, rfl⟩ | ⟨rule, actual, hm, rfl, rfl⟩
  · exact .inl ⟨p, r, m1, m2, hp, hm, hck.map fun a b h => h.defeqDFC henv W, rfl⟩
  · exact .inr ⟨rule, actual, hm.defeqDFC henv W, rfl, rfl⟩

/-- A composite left step: structure eta at the major of an application, then a redex fired at
the root of the result (an iota or a case step consuming the expansion). -/
def MajorEtaIota (Γ : List VExpr) (s c : VExpr) : Prop :=
  ∃ f m family info levels params, s = .app f m ∧ Params.env.projections family info ∧
    params.length = info.nparams ∧ info.nindices = 0 ∧
    Γ ⊢ m : mkApps (.const family levels) params ∧
    Γ ⊢ structExpand family info levels params m : mkApps (.const family levels) params ∧
    RootFire Γ (.app f (structExpand family info levels params m)) c

/-- The congruence closure (one position) of the composite step. -/
inductive MajorEtaIotaC : List VExpr → VExpr → VExpr → Prop where
  | root {Γ : List VExpr} {s c : VExpr} : MajorEtaIota Γ s c → MajorEtaIotaC Γ s c
  | appL {Γ : List VExpr} {f f' a : VExpr} :
      MajorEtaIotaC Γ f f' → MajorEtaIotaC Γ (.app f a) (.app f' a)
  | appR {Γ : List VExpr} {f a a' : VExpr} :
      MajorEtaIotaC Γ a a' → MajorEtaIotaC Γ (.app f a) (.app f a')
  | proj {Γ : List VExpr} {m m' : VExpr} {S : Name} {i : Nat} :
      MajorEtaIotaC Γ m m' → MajorEtaIotaC Γ (.proj S i m) (.proj S i m')
  | lamA {Γ : List VExpr} {A A' b : VExpr} :
      MajorEtaIotaC Γ A A' → MajorEtaIotaC Γ (.lam A b) (.lam A' b)
  | lamB {Γ : List VExpr} {A b b' : VExpr} :
      MajorEtaIotaC (A :: Γ) b b' → MajorEtaIotaC Γ (.lam A b) (.lam A b')
  | forallEA {Γ : List VExpr} {A A' B : VExpr} :
      MajorEtaIotaC Γ A A' → MajorEtaIotaC Γ (.forallE A B) (.forallE A' B)
  | forallEB {Γ : List VExpr} {A B B' : VExpr} :
      MajorEtaIotaC (A :: Γ) B B' → MajorEtaIotaC Γ (.forallE A B) (.forallE A B')

/-- The steps recorded on the source side: an eta-free parallel step, or structure eta at a
firing major followed by the iota, at one position. -/
def LStep (Γ : List VExpr) (s c : VExpr) : Prop := UpStepF Γ s c ∨ MajorEtaIotaC Γ s c

theorem MajorEtaIota.defeq {Γ : List VExpr} {s c A : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (h : MajorEtaIota Γ s c) (hs : Γ ⊢ s : A) : Γ ⊢ s ≡ c : A := by
  obtain ⟨f, m, family, info, levels, params, rfl, hl, hp, hi, hm, hexp, hstep⟩ := h
  obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ
  have hexp' : Γ ⊢ structExpand family info levels params m ≡ m :
      mkApps (.const family levels) params := IsDefEq.structEta hl hp hi hm hexp
  obtain ⟨_, hmT⟩ := hm.isType henv hΓ
  have hconv := (hm.uniqU henv hΓ ha).of_l henv hΓ hmT
  have h1 : Γ ⊢ .app f m ≡ .app f (structExpand family info levels params m) : A :=
    .trans_l henv hΓ hs (.appDF hf (.defeqDF hconv hexp'.symm))
  exact h1.trans ((RootFire.parRed hstep).defeq hΓ h1.hasType.2)

theorem MajorEtaIota.weakN {Γ Γ' : List VExpr} {n k : Nat} {s c : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (h : MajorEtaIota Γ s c) : MajorEtaIota Γ' (s.liftN n k) (c.liftN n k) := by
  obtain ⟨f, m, family, info, levels, params, rfl, hl, hp, hi, hm, hexp, hstep⟩ := h
  refine ⟨f.liftN n k, m.liftN n k, family, info, levels, params.map (·.liftN n k), rfl, hl,
    by simpa using hp, hi, ?_, ?_, ?_⟩
  · simpa [VExpr.liftN_mkApps, liftN] using hm.weakN henv W
  · simpa [VExpr.liftN_mkApps, structExpand_liftN, liftN] using hexp.weakN henv W
  · simpa [liftN, structExpand_liftN] using RootFire.weakN W hstep

theorem MajorEtaIota.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {s c A : VExpr}
    (hΓ : OnCtx Γ₀ (Params.env.IsType univs)) (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (h : MajorEtaIota Γ₁ s c) (hs : Γ₁ ⊢ s : A) : MajorEtaIota Γ₂ s c := by
  obtain ⟨f, m, family, info, levels, params, rfl, hl, hp, hi, hm, hexp, hstep⟩ := h
  have hΓ₁ := W.isType' hΓ
  obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ₁
  have hexp' : Γ₁ ⊢ structExpand family info levels params m ≡ m :
      mkApps (.const family levels) params := IsDefEq.structEta hl hp hi hm hexp
  obtain ⟨_, hmT⟩ := hm.isType henv hΓ₁
  have hconv := (hm.uniqU henv hΓ₁ ha).of_l henv hΓ₁ hmT
  have h1 : Γ₁ ⊢ .app f m ≡ .app f (structExpand family info levels params m) : A :=
    .trans_l henv hΓ₁ hs (.appDF hf (.defeqDF hconv hexp'.symm))
  exact ⟨f, m, family, info, levels, params, rfl, hl, hp, hi, hm.defeqDFC henv.ordered W,
    hexp.defeqDFC henv.ordered W, RootFire.defeqDFC W hstep⟩

theorem MajorEtaIota.instN {Γ₀ Γ₁ Γ : List VExpr} {a₁ A₀ s c T : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (_hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ a₁ : A₀) (h : MajorEtaIota Γ₁ s c) (hs : Γ₁ ⊢ s : T) :
    MajorEtaIota Γ (s.inst a₁ k) (c.inst a₁ k) := by
  obtain ⟨f, m, family, info, levels, params, rfl, hl, hp, hi, hm, hexp, hstep⟩ := h
  refine ⟨f.inst a₁ k, m.inst a₁ k, family, info, levels, params.map (·.inst a₁ k), rfl, hl,
    by simpa using hp, hi, ?_, ?_, ?_⟩
  · simpa [VExpr.inst_mkApps, inst] using hm.instN henv W h₀
  · simpa [VExpr.inst_mkApps, structExpand_inst, inst] using hexp.instN henv W h₀
  · simpa [inst, structExpand_inst] using RootFire.instN W h₀ hstep

theorem MajorEtaIotaC.defeq {Γ : List VExpr} {s c A : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (h : MajorEtaIotaC Γ s c) (hs : Γ ⊢ s : A) :
    Γ ⊢ s ≡ c : A := by
  induction h generalizing A with
  | root h => exact h.defeq hΓ hs
  | appL _ ih =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ
    exact .trans_l henv hΓ hs (.appDF (ih hΓ hf) ha)
  | appR _ ih =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ
    exact .trans_l henv hΓ hs (.appDF hf (ih hΓ ha))
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv hΓ
    exact (IsDefEq.proj_congr hΓ hs ⟨_, ih hΓ hm.hasType.2⟩)
  | lamA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    exact .trans_l henv hΓ hs (.lamDF (ih hΓ hd) hb)
  | lamB _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    exact .trans_l henv hΓ hs (.lamDF hd (ih ⟨hΓ, _, hd⟩ hb))
  | forallEA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    exact .trans_l henv hΓ hs (.forallEDF (ih hΓ hd) hb)
  | forallEB _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    exact .trans_l henv hΓ hs (.forallEDF hd (ih ⟨hΓ, _, hd⟩ hb))

theorem MajorEtaIotaC.weakN {Γ Γ' : List VExpr} {n k : Nat} {s c : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (h : MajorEtaIotaC Γ s c) : MajorEtaIotaC Γ' (s.liftN n k) (c.liftN n k) := by
  induction h generalizing k Γ' with
  | root h => exact .root (h.weakN W)
  | appL _ ih => exact .appL (ih W)
  | appR _ ih => exact .appR (ih W)
  | proj _ ih => exact .proj (ih W)
  | lamA _ ih => exact .lamA (ih W)
  | lamB _ ih => exact .lamB (ih W.succ)
  | forallEA _ ih => exact .forallEA (ih W)
  | forallEB _ ih => exact .forallEB (ih W.succ)

theorem MajorEtaIotaC.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {s c A : VExpr}
    (hΓ : OnCtx Γ₀ (Params.env.IsType univs)) (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (h : MajorEtaIotaC Γ₁ s c) (hs : Γ₁ ⊢ s : A) : MajorEtaIotaC Γ₂ s c := by
  induction h generalizing Γ₂ A with
  | root h => exact .root (h.defeqDFC hΓ W hs)
  | appL _ ih =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv (W.isType' hΓ)
    exact .appL (ih W hf)
  | appR _ ih =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv (W.isType' hΓ)
    exact .appR (ih W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lamA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv (W.isType' hΓ)
    exact .lamA (ih W hd)
  | lamB _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv (W.isType' hΓ)
    exact .lamB (ih (.succ W hd) hb)
  | forallEA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    exact .forallEA (ih W hd)
  | forallEB _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    exact .forallEB (ih (.succ W hd) hb)

theorem MajorEtaIotaC.instN {Γ₀ Γ₁ Γ : List VExpr} {a₁ A₀ s c T : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ a₁ : A₀) (h : MajorEtaIotaC Γ₁ s c) (hs : Γ₁ ⊢ s : T) :
    MajorEtaIotaC Γ (s.inst a₁ k) (c.inst a₁ k) := by
  induction h generalizing Γ k T with
  | root h => exact .root (h.instN W hΓ₁ h₀ hs)
  | appL _ ih =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ₁
    exact .appL (ih W hΓ₁ hf)
  | appR _ ih =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ₁
    exact .appR (ih W hΓ₁ ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv hΓ₁
    exact .proj (ih W hΓ₁ hm.hasType.2)
  | lamA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ₁
    exact .lamA (ih W hΓ₁ hd)
  | lamB _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ₁
    exact .lamB (ih W.succ ⟨hΓ₁, _, hd⟩ hb)
  | forallEA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    exact .forallEA (ih W hΓ₁ hd)
  | forallEB _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    exact .forallEB (ih W.succ ⟨hΓ₁, _, hd⟩ hb)

theorem LStep.defeq {Γ : List VExpr} {s c A : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (h : LStep Γ s c) (hs : Γ ⊢ s : A) : Γ ⊢ s ≡ c : A :=
  h.elim (fun h => h.defeq hΓ hs) (fun h => h.defeq hΓ hs)

theorem LStep.hasType {Γ : List VExpr} {s c A : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (h : LStep Γ s c) (hs : Γ ⊢ s : A) : Γ ⊢ c : A := (h.defeq hΓ hs).hasType.2

theorem LStep.weakN {Γ Γ' : List VExpr} {n k : Nat} {s c : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (h : LStep Γ s c) : LStep Γ' (s.liftN n k) (c.liftN n k) :=
  h.elim (fun h => .inl (h.weakN W)) (fun h => .inr (h.weakN W))

theorem LStep.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {s c A : VExpr}
    (hΓ : OnCtx Γ₀ (Params.env.IsType univs)) (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (h : LStep Γ₁ s c) (hs : Γ₁ ⊢ s : A) : LStep Γ₂ s c :=
  h.elim (fun h => .inl (h.defeqDFC hΓ W hs)) (fun h => .inr (h.defeqDFC hΓ W hs))

theorem LStep.instN {Γ₀ Γ₁ Γ : List VExpr} {a₁ A₀ s c T : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (h₀ : Γ₀ ⊢ a₁ : A₀) (h : LStep Γ₁ s c) (hs : Γ₁ ⊢ s : T) :
    LStep Γ (s.inst a₁ k) (c.inst a₁ k) :=
  h.elim (fun h => .inl (h.instN W hΓ₁ h₀ hs)) (fun h => .inr (h.instN W hΓ₁ h₀ hs))

/-! ## The relation -/

/-- The eta-normal relation (see the module docstring). -/
inductive EtaNE : List VExpr → VExpr → VExpr → Prop where
  | bvar {Γ : List VExpr} {i : Nat} : EtaNE Γ (.bvar i) (.bvar i)
  | sort {Γ : List VExpr} {u : VLevel} : EtaNE Γ (.sort u) (.sort u)
  | const {Γ : List VExpr} {c : Name} {ls : List VLevel} : EtaNE Γ (.const c ls) (.const c ls)
  | elim {Γ : List VExpr} {block : Name} {owner : Nat} {ls : List VLevel} :
      EtaNE Γ (.elim block owner ls) (.elim block owner ls)
  | app {Γ : List VExpr} {f f' a a' : VExpr} :
      EtaNE Γ f f' → EtaNE Γ a a' → EtaNE Γ (.app f a) (.app f' a')
  | proj {Γ : List VExpr} {m m' : VExpr} {S : Name} {i : Nat} :
      EtaNE Γ m m' → EtaNE Γ (.proj S i m) (.proj S i m')
  | lamC {Γ : List VExpr} {A A' b b' : VExpr} :
      EtaNE Γ A A' → EtaNE (A :: Γ) b b' → EtaNE Γ (.lam A b) (.lam A' b')
  | lamD {Γ : List VExpr} {A A' b b' : VExpr} {u : VLevel} :
      Γ ⊢ A ≡ A' : .sort u → EtaNE (A :: Γ) b b' → EtaNE Γ (.lam A b) (.lam A' b')
  | forallEC {Γ : List VExpr} {A A' B B' : VExpr} :
      EtaNE Γ A A' → EtaNE (A :: Γ) B B' → EtaNE Γ (.forallE A B) (.forallE A' B')
  | funEta {Γ : List VExpr} {e A B A' body : VExpr} {u : VLevel} : Γ ⊢ e : .forallE A B →
      Γ ⊢ A ≡ A' : .sort u → EtaNE (A' :: Γ) (.app e.lift (.bvar 0)) body →
      EtaNE Γ e (.lam A' body)
  | structEta {Γ : List VExpr} {family : Name} {info : VProjectionInfo} {levels : List VLevel}
      {params args : List VExpr} {e : VExpr} : Params.env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ e : mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params e : mkApps (.const family levels) params →
      (hlen : (structArgs family info params e).length = args.length) →
      (∀ i (hi : i < (structArgs family info params e).length) (hi' : i < args.length),
        EtaNE Γ (structArgs family info params e)[i] args[i]) →
      EtaNE Γ e (mkApps (.const info.ctorName levels) args)
  | betaR {Γ : List VExpr} {A b a s T : VExpr} {args : List VExpr} :
      Γ ⊢ mkApps (.app (.lam A b) a) args : T →
      EtaNE Γ s (mkApps (b.inst a) args) → EtaNE Γ s (mkApps (.app (.lam A b) a) args)
  | redL {Γ : List VExpr} {s c X : VExpr} : LStep Γ s c → EtaNE Γ c X → EtaNE Γ s X

/-- A typed beta redex is convertible to its contractum. -/
theorem beta_defeqU {Γ : List VExpr} {A b a T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : Γ ⊢ .app (.lam A b) a : T) : Γ ⊢ .app (.lam A b) a ≡ b.inst a := by
  obtain ⟨A₁, B₁, hlam, ha⟩ := H.app_inv henv hΓ
  obtain ⟨B, hPi, hb⟩ := hlam.lam_inv_forallE henv hΓ
  obtain ⟨⟨u, hA⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
  exact ⟨_, .beta hb (hA.defeq' ha)⟩

/-- A typed beta redex applied to arguments is convertible to its contractum applied to them. -/
theorem beta_spine_defeqU {Γ : List VExpr} {A b a T : VExpr} {args : List VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hT : Γ ⊢ mkApps (.app (.lam A b) a) args : T) :
    Γ ⊢ mkApps (.app (.lam A b) a) args ≡ mkApps (b.inst a) args := by
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hT⟩
  have hhead' : Γ ⊢ .app (.lam A b) a : _ := hhead
  refine IsDefEqU.mkApps_args hΓ (beta_defeqU hΓ hhead')
    (List.forall₂_of_getElem rfl fun i hi hi' => ?_) hT
  obtain ⟨_, hx⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
  exact ⟨_, hx⟩

/-- Soundness: a source and its reduct are convertible. -/
theorem EtaNE.defeq {Γ : List VExpr} {e e' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaNE Γ e e') (he : Γ ⊢ e : T) : Γ ⊢ e ≡ e' := by
  induction H generalizing T with
  | bvar | sort | const | elim => exact ⟨_, he⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    exact ⟨_, .appDF ((ih1 hΓ hf).of_l henv hΓ hf) ((ih2 hΓ ha).of_l henv hΓ ha)⟩
  | proj _ ih =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := he.proj_inv henv hΓ
    have majorEq := (ih hΓ hmajor.hasType.2).of_l henv hΓ hmajor.hasType.2
    exact ⟨_, .projDF hinfo hlevels huvars hparams hindices hfield
      hfieldTyping hmajor (hmajor.trans majorEq) hclosed hguard⟩
  | lamC _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA₀⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hAA := (ih1 hΓ hA₀).of_l henv hΓ hA₀
    have ⟨_, hB⟩ := ih2 ⟨hΓ, _, hA₀⟩ hb
    exact ⟨_, .lamDF hAA hB⟩
  | lamD hA _ ih =>
    obtain ⟨⟨_, hA₀⟩, _, hb⟩ := he.lam_inv henv hΓ
    have ⟨_, hB⟩ := ih ⟨hΓ, _, hA₀⟩ hb
    exact ⟨_, .lamDF hA hB⟩
  | forallEC _ _ ih1 ih2 =>
    obtain ⟨⟨_, hA₀⟩, _, hb⟩ := he.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ, _, hA₀⟩
    have hAA := (ih1 hΓ hA₀).of_l henv hΓ hA₀
    have hB := (ih2 hΓ' hb).of_l henv hΓ' hb
    exact ⟨_, .forallEDF hAA hB⟩
  | @funEta Γ₀ e A B A' body u hPi hA _ ih =>
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨_, hA₀⟩, _, hB⟩ := hPiT.forallE_inv henv
    have hΓ' : OnCtx (A' :: Γ₀) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
    have hbody : A' :: Γ₀ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ₀ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv
      have h0 : A' :: Γ₀ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    have ih' := (ih hΓ' hbody).of_l henv hΓ' hbody
    have hPiEq : Γ₀ ⊢ .forallE A' B ≡ .forallE A B : .sort (.imax u _) :=
      .forallEDF hA.symm (hB.defeqDFC henv.ordered (.succ .zero hA))
    have heta : Γ₀ ⊢ .lam A' (.app e.lift (.bvar 0)) ≡ .lam A (.app e.lift (.bvar 0)) :
        .forallE A B :=
      .defeqDF hPiEq (.lamDF hA.symm hbody)
    exact ⟨_, IsDefEq.trans (IsDefEq.trans heta (.eta hPi)).symm
      (.defeqDF hPiEq (.lamDF hA.hasType.2 ih'))⟩
  | structEta hl hp hi hs ht hlen _ ih =>
    have hexp : _ ⊢ _ ≡ structExpand _ _ _ _ _ := ⟨_, (IsDefEq.structEta hl hp hi hs ht).symm⟩
    refine hexp.trans henv hΓ ?_
    rw [structExpand_eq] at ht ⊢
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
    refine IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ (List.forall₂_of_getElem hlen fun i hi hi' => ?_) ht
    obtain ⟨_, hx⟩ := schema_mkApps_arg_type hΓ ht (List.getElem_mem hi)
    exact ih i hi hi' hΓ hx
  | betaR hT _ ih =>
    have hred := beta_spine_defeqU hΓ hT
    exact (ih hΓ he).trans henv hΓ hred.symm
  | redL h _ ih =>
    have h1 : _ ⊢ _ ≡ _ := ⟨_, h.defeq hΓ he⟩
    exact h1.trans henv hΓ (ih hΓ (h.hasType hΓ he))

theorem EtaNE.hasType {Γ : List VExpr} {e e' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaNE Γ e e') (he : Γ ⊢ e : T) : Γ ⊢ e' : T :=
  he.defeqU_l henv hΓ (H.defeq hΓ he)

/-- Weakening. -/
theorem EtaNE.weakN {Γ Γ' : List VExpr} {n k : Nat} {e e' : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (H : EtaNE Γ e e') : EtaNE Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lamC _ _ ih1 ih2 => exact .lamC (ih1 W) (ih2 W.succ)
  | lamD hA _ ih => exact .lamD (hA.weakN henv W) (ih W.succ)
  | forallEC _ _ ih1 ih2 => exact .forallEC (ih1 W) (ih2 W.succ)
  | funEta hPi hA _ ih =>
    refine .funEta (hPi.weakN henv W) (hA.weakN henv W) ?_
    have := ih W.succ
    simpa [liftN, ← VExpr.lift_liftN'] using this
  | @structEta Γ₀ family info levels params args e hl hp hi hs ht hlen hargs ih =>
    have hs' := hs.weakN henv W
    have ht' := ht.weakN henv W
    simp only [structExpand_eq, VExpr.liftN_mkApps, liftN, ← structArgs_liftN] at hs' ht' ⊢
    refine .structEta hl (by simpa using hp) hi hs' ht' ?_ ?_
    · rw [structArgs_liftN]; simp [hlen]
    · intro i hi hi'
      simp only [structArgs_liftN, List.getElem_map]
      exact ih i (by simpa [structArgs_liftN] using hi) (by simpa using hi') W
  | betaR hT _ ih =>
    have hT' := hT.weakN henv W
    have := ih W
    rw [VExpr.liftN_mkApps, VExpr.liftN_inst_hi] at this
    simp only [VExpr.liftN_mkApps, liftN] at hT' ⊢
    exact .betaR hT' this
  | redL h _ ih => exact .redL (h.weakN W) (ih W)

theorem EtaNE.weak {Γ : List VExpr} {e e' B : VExpr} (H : EtaNE Γ e e') :
    EtaNE (B :: Γ) e.lift e'.lift := H.weakN .one

/-- Context conversion. -/
theorem EtaNE.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr} {e e' T : VExpr}
    (hΓ : OnCtx Γ₀ (Params.env.IsType univs)) (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂)
    (he : Γ₁ ⊢ e : T) (H : EtaNE Γ₁ e e') : EtaNE Γ₂ e e' := by
  induction H generalizing Γ₂ T with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lamC _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lamC (ih1 W hd) (ih2 (.succ W hd) hb)
  | lamD hA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lamD (hA.defeqDFC henv.ordered W) (ih (.succ W hd) hb)
  | forallEC _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv.ordered
    exact .forallEC (ih1 W hd) (ih2 (.succ W hd) hb)
  | @funEta Γ₁ e A B A' body u hPi hA _ ih =>
    have hΓ₁ := W.isType' hΓ
    have hΓ' : OnCtx (A' :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, _, hA.hasType.2⟩
    have hbody : A' :: Γ₁ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ₁ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv.ordered
      have h0 : A' :: Γ₁ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    exact .funEta (hPi.defeqDFC henv.ordered W) (hA.defeqDFC henv.ordered W)
      (ih (.succ W hA.hasType.2) hbody)
  | structEta hl hp hi hs ht hlen _ ih =>
    refine .structEta hl hp hi (hs.defeqDFC henv.ordered W) (ht.defeqDFC henv.ordered W) hlen
      fun i hi hi' => ?_
    rw [structExpand_eq] at ht
    obtain ⟨_, hx⟩ := schema_mkApps_arg_type (W.isType' hΓ) ht (List.getElem_mem hi)
    exact ih i hi hi' W hx
  | betaR hT _ ih => exact .betaR (hT.defeqDFC henv.ordered W) (ih W he)
  | redL h _ ih =>
    exact .redL (h.defeqDFC hΓ W he) (ih W (h.hasType (W.isType' hΓ) he))

/-- Reflexivity (untyped). -/
protected theorem EtaNE.rfl {Γ : List VExpr} : ∀ {e : VExpr}, EtaNE Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app EtaNE.rfl EtaNE.rfl
  | .proj .. => .proj EtaNE.rfl
  | .lam .. => .lamC EtaNE.rfl EtaNE.rfl
  | .forallE .. => .forallEC EtaNE.rfl EtaNE.rfl

theorem EtaNE.congrRel : CongrRel EtaNE where
  rfl := EtaNE.rfl
  app := .app
  proj := .proj
  lam := .lamC
  forallE := .forallEC
  weakN W h := h.weakN W

/-- Substituting related terms for a variable. -/
theorem EtaNE.inst_r {Γ₀ : List VExpr} {a₁ a₂ A₀ : VExpr} (H₀ : EtaNE Γ₀ a₁ a₂) :
    ∀ (e : VExpr) {k : Nat} {Γ₁ Γ : List VExpr}, Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ →
      EtaNE Γ (e.inst a₁ k) (e.inst a₂ k)
  | .bvar i, k, Γ₁, Γ, W => by
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .bvar
    | succ _ ih =>
      cases i with simp
      | zero => exact .bvar
      | succ h => exact (ih ..).weakN .one
  | .sort .., _, _, _, _ => .sort
  | .const .., _, _, _, _ => .const
  | .elim .., _, _, _, _ => .elim
  | .app f a, _, _, _, W => .app (EtaNE.inst_r H₀ f W) (EtaNE.inst_r H₀ a W)
  | .proj _ _ m, _, _, _, W => .proj (EtaNE.inst_r H₀ m W)
  | .lam A b, _, _, _, W => .lamC (EtaNE.inst_r H₀ A W) (EtaNE.inst_r H₀ b W.succ)
  | .forallE A B, _, _, _, W => .forallEC (EtaNE.inst_r H₀ A W) (EtaNE.inst_r H₀ B W.succ)

/-- Two-sided substitution: related terms substituted into related terms. -/
theorem EtaNE.instN {Γ₀ Γ₁ Γ : List VExpr} {a₁ a₂ A₀ e e' T : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (H₀ : EtaNE Γ₀ a₁ a₂) (h₀ : Γ₀ ⊢ a₁ : A₀) (H : EtaNE Γ₁ e e') (he : Γ₁ ⊢ e : T) :
    EtaNE Γ (e.inst a₁ k) (e'.inst a₂ k) := by
  have hΓ₀ := (W.wf henv.ordered h₀ hΓ₁).1
  have ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀ := (H₀.defeq hΓ₀ h₀).of_l henv hΓ₀ h₀
  induction H generalizing Γ k T with
  | bvar => exact EtaNE.inst_r H₀ _ W
  | sort | const | elim => exact EtaNE.rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha'⟩ := he.app_inv henv hΓ₁
    exact .app (ih1 W hΓ₁ hf) (ih2 W hΓ₁ ha')
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    exact .proj (ih W hΓ₁ hm.hasType.2)
  | lamC _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv hΓ₁
    exact .lamC (ih1 W hΓ₁ hd) (ih2 W.succ ⟨hΓ₁, _, hd⟩ hb)
  | lamD hA _ ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv hΓ₁
    exact .lamD ((hA.instN henv h₀ W).trans (HasType.instN_DF W hΓ₁ ha hA.hasType.2))
      (ih W.succ ⟨hΓ₁, _, hd⟩ hb)
  | forallEC _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv.ordered
    exact .forallEC (ih1 W hΓ₁ hd) (ih2 W.succ ⟨hΓ₁, _, hd⟩ hb)
  | @funEta Γ₁ e A B A' body u hPi hA _ ih =>
    have hΓ' : OnCtx (A' :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, _, hA.hasType.2⟩
    have hbody : A' :: Γ₁ ⊢ .app e.lift (.bvar 0) : B := by
      have h1 : A' :: Γ₁ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) := hPi.weak henv.ordered
      have h0 : A' :: Γ₁ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app h1 h0
    have := ih W.succ hΓ' hbody
    simp only [VExpr.inst, ← VExpr.lift_instN_lo, instVar, if_pos (Nat.zero_lt_succ k)] at this
    have hΓ := (W.wf henv.ordered h₀ hΓ₁).2
    have hA'' : Γ ⊢ A'.inst a₁ k ≡ A'.inst a₂ k : .sort u := HasType.instN_DF W hΓ₁ ha hA.hasType.2
    have hbody' := hbody.instN henv W.succ h₀
    simp only [VExpr.inst, ← VExpr.lift_instN_lo, instVar, if_pos (Nat.zero_lt_succ k)] at hbody'
    exact .funEta (hPi.instN henv W h₀)
      ((hA.instN henv h₀ W).trans hA'') (this.defeqDFC hΓ (.succ .zero hA'') hbody')
  | @structEta Γ₁ family info levels params args e hl hp hi hs hexp hlen hargs ih =>
    obtain ⟨_, hT⟩ := hs.isType henv hΓ₁
    have hs' := hs.instN henv W h₀
    have hexp' := hexp.instN henv W h₀
    simp only [VExpr.inst_mkApps, VExpr.inst, structExpand_inst] at hs' hexp' ⊢
    have hargsT : ∀ i (hi : i < (structArgs family info params e).length),
        ∃ T, Γ₁ ⊢ (structArgs family info params e)[i] : T := fun i hi => by
      rw [structExpand_eq] at hexp
      exact schema_mkApps_arg_type hΓ₁ hexp (List.getElem_mem hi)
    refine .structEta hl (by simpa using hp) hi hs' hexp' ?_ ?_
    · simpa [structArgs] using hlen
    · intro i hi hi'
      have hi₀ : i < (structArgs family info params e).length := by
        simpa [structArgs] using hi
      obtain ⟨_, hiT⟩ := hargsT i hi₀
      have := ih i hi₀ (by simpa using hi') W hΓ₁ hiT
      simpa only [structArgs_inst, List.getElem_map] using this
  | @betaR Γ₁ A b a s T' args hT _ ih =>
    have := ih W hΓ₁ he
    have hT' := (HasType.instN_DF W hΓ₁ ha hT).hasType.2
    simp only [VExpr.inst_mkApps, VExpr.inst] at hT' this ⊢
    have h := inst_inst_hi b a a₂ 0 k
    simp only [Nat.add_zero] at h
    rw [h] at this
    exact .betaR hT' this
  | redL h _ ih =>
    exact .redL (h.instN W hΓ₁ h₀ he) (ih W hΓ₁ (h.hasType hΓ₁ he))

/-- A parallel eta step from a typed term is an eta-normal expansion. -/
theorem EtaNE.of_etaPar {Γ : List VExpr} {e e' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : EtaPar Γ e e') (he : Γ ⊢ e : T) :
    EtaNE Γ e e' := by
  induction H generalizing T with
  | bvar | sort | const | elim => exact EtaNE.rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    exact .app (ih1 hΓ hf) (ih2 hΓ ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2)
  | lam hA _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv hΓ
    exact .lamC (ih1 hΓ hd) (ih2 ⟨hΓ, _, hd⟩ hb)
  | forallE hA _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv.ordered
    exact .forallEC (ih1 hΓ hd) (ih2 ⟨hΓ, _, hd⟩ hb)
  | @funEta Γ e e' A A' B H₀ HA hPi ih _ =>
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨u, hA₀⟩, _, hB⟩ := hPiT.forallE_inv henv.ordered
    have hAA : Γ ⊢ A ≡ A' : .sort u := (EtaPar.full hΓ HA hA₀).defeq hΓ hA₀
    exact .funEta hPi hAA (.app (ih hΓ hPi).weak EtaNE.bvar)
  | @structEta Γ e e' family info levels params params' H₀ hlen hps hl hp hi hs hexp ih ihp =>
    have hee' := ih hΓ hs
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    have hF : List.Forall₂ (EtaNE Γ) (structArgs family info params e)
        (structArgs family info params' e') := by
      refine List.Forall₂.append' (List.forall₂_of_getElem hlen fun i hi hi' => ?_)
        (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
      · obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
        exact ihp i hi hi' hΓ hpT
      · simp only [List.getElem_map, List.getElem_range]
        exact .proj hee'
    obtain ⟨hlen', hargs'⟩ := getElem_of_forall₂ hF
    exact .structEta hl hp hi hs hexp hlen' hargs'

/-- The structure expansion of a term convertible to `X` is typed like the expansion of `X`. -/
theorem structExpand_typed_of_defeqU {Γ : List VExpr} {s X T : VExpr} {family : Name}
    {info : VProjectionInfo} {levels : List VLevel} {params : List VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (h : Γ ⊢ X ≡ s)
    (ht : Γ ⊢ structExpand family info levels params X : T) :
    Γ ⊢ structExpand family info levels params s : T := by
  rw [structExpand_eq] at ht ⊢
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  refine ht.defeqU_l henv hΓ (IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ ?_ ht)
  refine List.Forall₂.append' (List.forall₂_of_getElem rfl fun i hi hi' => ?_)
    (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
  · obtain ⟨_, hx⟩ := schema_mkApps_arg_type hΓ ht (List.mem_append_left _ (List.getElem_mem hi))
    exact ⟨_, hx⟩
  · have hjmem : j ∈ List.range info.numFields := by simpa using hj
    obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ ht
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
    simp only [List.getElem_map, List.getElem_range]
    exact ⟨_, IsDefEq.proj_congr hΓ hpj h⟩

/-- The eta body of a function. -/
theorem eta_body_typed {Γ : List VExpr} {X A B : VExpr} (hX : Γ ⊢ X : .forallE A B) :
    A :: Γ ⊢ .app X.lift (.bvar 0) : B := by
  have := HasType.app (hX.weak henv.ordered (B := A)) (.bvar .zero)
  simpa [VExpr.inst_liftN_bvar] using this

/-- A root function eta expansion of the right side. -/
theorem EtaNE.root_funEta {Γ : List VExpr} {s X A A' B T : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (H : EtaNE Γ s X)
    (hX : Γ ⊢ X : .forallE A B) (hA : Γ ⊢ A ≡ A' : .sort u) :
    EtaNE Γ s (.lam A' (.app X.lift (.bvar 0))) := by
  have hsPi : Γ ⊢ s : .forallE A B := hX.defeqU_l henv hΓ (H.defeq hΓ hs).symm
  exact .funEta hsPi hA (.app H.weak EtaNE.bvar)

/-- A root structure eta expansion of the right side. -/
theorem EtaNE.root_structEta {Γ : List VExpr} {s X T : VExpr} {family : Name}
    {info : VProjectionInfo} {levels : List VLevel} {params params' : List VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (H : EtaNE Γ s X)
    (hl : Params.env.projections family info) (hp : params.length = info.nparams)
    (hi : info.nindices = 0) (hX : Γ ⊢ X : mkApps (.const family levels) params)
    (hexp : Γ ⊢ structExpand family info levels params X : mkApps (.const family levels) params)
    (hlen : params.length = params'.length)
    (hps : ∀ i (hi : i < params.length) (hi' : i < params'.length), EtaNE Γ params[i] params'[i]) :
    EtaNE Γ s (structExpand family info levels params' X) := by
  have hsX := (H.defeq hΓ hs).symm
  have hsS : Γ ⊢ s : mkApps (.const family levels) params := hX.defeqU_l henv hΓ hsX
  have hexp' := structExpand_typed_of_defeqU hΓ hsX hexp
  have hF : List.Forall₂ (EtaNE Γ) (structArgs family info params s)
      (structArgs family info params' X) := by
    refine List.Forall₂.append' (List.forall₂_of_getElem hlen hps)
      (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
    simp only [List.getElem_map, List.getElem_range]
    exact .proj H
  obtain ⟨hlen', hargs'⟩ := getElem_of_forall₂ hF
  exact .structEta hl hp hi hsS hexp' hlen' hargs'

/-- Eta wrappers around a spine: expansions of partial applications, which the following
applications turn into beta redexes. -/
inductive Wrap (Γ : List VExpr) : VExpr → VExpr → Prop where
  | rfl {Y : VExpr} : Wrap Γ Y Y
  | eta {Y Y' A A' B : VExpr} {u : VLevel} : Wrap Γ Y Y' → Γ ⊢ Y' : .forallE A B →
      Γ ⊢ A ≡ A' : .sort u → Wrap Γ Y (.lam A' (.app Y'.lift (.bvar 0)))
  | struct {Y Y' : VExpr} {family : Name} {info : VProjectionInfo} {levels : List VLevel}
      {params params' : List VExpr} : Wrap Γ Y Y' → Params.env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ Y' : mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params Y' : mkApps (.const family levels) params →
      params.length = params'.length →
      (∀ i (hi : i < params.length) (hi' : i < params'.length), EtaNE Γ params[i] params'[i]) →
      Wrap Γ Y (structExpand family info levels params' Y')
  | app {F F' a : VExpr} : Wrap Γ F F' → Wrap Γ (.app F a) (.app F' a)

theorem Wrap.defeq {Γ : List VExpr} {Y Y' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (W : Wrap Γ Y Y') (hY : Γ ⊢ Y : T) : Γ ⊢ Y ≡ Y' := by
  induction W generalizing T with
  | rfl => exact ⟨_, hY⟩
  | @eta Y Y' A A' B u _ hY' hA ih =>
    have h1 := ih hY
    have hbody : A' :: Γ ⊢ .app Y'.lift (.bvar 0) : B := by
      have h0 : A' :: Γ ⊢ .bvar 0 : A.lift :=
        (hA.weak henv.ordered (B := A')).defeq' (.bvar .zero)
      simpa [VExpr.inst_liftN_bvar] using HasType.app (hY'.weak henv.ordered) h0
    have hlam : Γ ⊢ .lam A' (.app Y'.lift (.bvar 0)) ≡ .lam A (.app Y'.lift (.bvar 0)) :
        .forallE A' B := .lamDF hA.symm hbody
    have h2 : Γ ⊢ Y' ≡ .lam A (.app Y'.lift (.bvar 0)) := ⟨_, (IsDefEq.eta hY').symm⟩
    have h3 : Γ ⊢ .lam A (.app Y'.lift (.bvar 0)) ≡ .lam A' (.app Y'.lift (.bvar 0)) :=
      ⟨_, hlam.symm⟩
    exact h1.trans henv hΓ (h2.trans henv hΓ h3)
  | struct _ hl hp hi hY' hexp hlen hps ih =>
    have h1 := ih hY
    have h2 : _ ⊢ _ ≡ structExpand _ _ _ _ _ := ⟨_, (IsDefEq.structEta hl hp hi hY' hexp).symm⟩
    refine (h1.trans henv hΓ h2).trans henv hΓ ?_
    simp only [structExpand_eq] at hexp ⊢
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hexp⟩
    refine IsDefEqU.mkApps_args hΓ ⟨_, hhead⟩ ?_ hexp
    refine List.Forall₂.append' (List.forall₂_of_getElem hlen fun i hi hi' => ?_)
      (List.forall₂_of_getElem (by simp) fun j hj hj' => ?_)
    · obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hexp
        (List.mem_append_left _ (List.getElem_mem hi))
      exact (hps i hi hi').defeq hΓ hpT
    · obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ hexp
        (List.mem_append_right _ (List.mem_map.mpr ⟨j, by simpa using hj, Eq.refl _⟩))
      simp only [List.getElem_map, List.getElem_range]
      exact ⟨_, hpj⟩
  | app _ ih =>
    obtain ⟨_, _, hF, ha⟩ := hY.app_inv henv hΓ
    exact ⟨_, .appDF ((ih hF).of_l henv hΓ hF) ha⟩

/-- A parallel eta step on a spine reduces the head and the arguments and wraps partial
applications. -/
theorem EtaPar.spine_inv {Γ : List VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ∀ {Z X' T : VExpr} {H : VExpr} {args : List VExpr}, EtaPar Γ Z X' → mkApps H args = Z →
      Γ ⊢ Z : T →
      ∃ H' args', EtaPar Γ H H' ∧ List.Forall₂ (EtaPar Γ) args args' ∧
        Wrap Γ (mkApps H' args') X' := by
  intro Z X' T H args HX
  induction HX generalizing H args T with
  | app hf ha ihf _ =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .app hf ha, .nil, .rfl⟩
    · cases he'
      obtain ⟨_, _, hF, -⟩ := hZ.app_inv henv hΓ
      obtain ⟨H', args₀', hH, hargs, hW⟩ := ihf hΓ rfl hF
      refine ⟨H', args₀' ++ [_], hH, List.Forall₂.append' hargs (.cons ha .nil), ?_⟩
      rw [VExpr.mkApps_snoc]
      exact .app hW
  | funEta H₀ HA hPi ih _ =>
    intro he hZ
    obtain ⟨H', args', hH, hargs, hW⟩ := ih hΓ he hZ
    subst he
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨u, hA⟩, -⟩ := hPiT.forallE_inv henv.ordered
    exact ⟨H', args', hH, hargs, .eta hW ((EtaPar.full hΓ H₀ hPi).hasType hΓ hPi)
      ((EtaPar.full hΓ HA hA).defeq hΓ hA)⟩
  | structEta H₀ hlen hps hl hp hi hs hexp ih _ =>
    intro he hZ
    obtain ⟨H', args', hH, hargs, hW⟩ := ih hΓ he hZ
    subst he
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    refine ⟨H', args', hH, hargs, .struct hW hl hp hi ((EtaPar.full hΓ H₀ hs).hasType hΓ hs)
      ((FullReduction.structExpand (EtaPar.full hΓ H₀ hs)).hasType hΓ hexp) hlen
      fun i hi hi' => ?_⟩
    obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
    exact EtaNE.of_etaPar hΓ (hps i hi hi') hpT
  | bvar | sort | const | elim =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .rfl, .nil, .rfl⟩
    · cases he'
  | proj h =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .proj h, .nil, .rfl⟩
    · cases he'
  | lam h1 h2 =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .lam h1 h2, .nil, .rfl⟩
    · cases he'
  | forallE h1 h2 =>
    intro he hZ
    rcases mkApps_eq_cases' he with ⟨rfl, rfl⟩ | ⟨args₀, x, rfl, he'⟩
    · exact ⟨_, [], .forallE h1 h2, .nil, .rfl⟩
    · cases he'

/-- Eta wrappers on the right are absorbed. -/
theorem EtaNE.wrap_r {Γ : List VExpr} {s Y Y' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hs : Γ ⊢ s : T) (W : Wrap Γ Y Y') :
    ∀ {as : List VExpr}, EtaNE Γ s (mkApps Y as) → EtaNE Γ s (mkApps Y' as) := by
  induction W with
  | rfl => intro _ H; exact H
  | @eta Y Y' A A' B u W hY' hA ih =>
    intro as H
    have H' := ih H
    have hY'as : Γ ⊢ mkApps Y' as : T := H'.hasType hΓ hs
    cases as with
    | nil => exact EtaNE.root_funEta hΓ hs H' hY' hA
    | cons a rest =>
      have hT : Γ ⊢ mkApps (.app (.lam A' (.app Y'.lift (.bvar 0))) a) rest : T := by
        have h2 : Γ ⊢ Y' ≡ .lam A' (.app Y'.lift (.bvar 0)) :=
          (Wrap.eta (Y := Y') .rfl hY' hA).defeq hΓ hY'
        have h3 : Γ ⊢ mkApps Y' (a :: rest) ≡ mkApps (.lam A' (.app Y'.lift (.bvar 0))) (a :: rest) :=
          IsDefEqU.mkApps_args hΓ h2 (List.forall₂_of_getElem rfl fun i hi hi' =>
            let ⟨_, hx⟩ := schema_mkApps_arg_type hΓ hY'as (List.getElem_mem hi); ⟨_, hx⟩) hY'as
        exact hY'as.defeqU_l henv hΓ h3
      refine .betaR hT ?_
      have hr : mkApps Y' (a :: rest) = mkApps (.app Y' a) rest := rfl
      rw [hr] at H'
      simpa [inst, instVar, inst_lift] using H'
  | struct W hl hp hi hY' hexp hlen hps ih =>
    intro as H
    have H' := ih H
    cases as with
    | nil => exact EtaNE.root_structEta hΓ hs H' hl hp hi hY' hexp hlen hps
    | cons a rest =>
      exfalso
      have hY'as : Γ ⊢ mkApps _ (a :: rest) : T := H'.hasType hΓ hs
      have hY'a : Γ ⊢ mkApps (.app _ a) rest : T := hY'as
      obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hY'a⟩
      have hhead' : Γ ⊢ .app _ a : _ := hhead
      obtain ⟨_, _, hPi, -⟩ := hhead'.app_inv henv hΓ
      exact pi_not_struct hΓ hl hPi hY'
  | app W ih =>
    intro as H
    exact ih (as := _ :: as) H

/-- The congruence part of a parallel eta step: no expansion at the root. -/
inductive EtaParC (Γ : List VExpr) : VExpr → VExpr → Prop where
  | bvar {i : Nat} : EtaParC Γ (.bvar i) (.bvar i)
  | sort {u : VLevel} : EtaParC Γ (.sort u) (.sort u)
  | const {c : Name} {ls : List VLevel} : EtaParC Γ (.const c ls) (.const c ls)
  | elim {block : Name} {owner : Nat} {ls : List VLevel} :
      EtaParC Γ (.elim block owner ls) (.elim block owner ls)
  | app {f f' a a' : VExpr} : EtaPar Γ f f' → EtaPar Γ a a' → EtaParC Γ (.app f a) (.app f' a')
  | proj {m m' : VExpr} {S : Name} {i : Nat} : EtaPar Γ m m' → EtaParC Γ (.proj S i m) (.proj S i m')
  | lam {A A' b b' : VExpr} : EtaPar Γ A A' → EtaPar (A :: Γ) b b' →
      EtaParC Γ (.lam A b) (.lam A' b')
  | forallE {A A' B B' : VExpr} : EtaPar Γ A A' → EtaPar (A :: Γ) B B' →
      EtaParC Γ (.forallE A B) (.forallE A' B')

theorem EtaParC.toEtaPar {Γ : List VExpr} {X X' : VExpr} (H : EtaParC Γ X X') : EtaPar Γ X X' := by
  cases H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app h1 h2 => exact .app h1 h2
  | proj h => exact .proj h
  | lam h1 h2 => exact .lam h1 h2
  | forallE h1 h2 => exact .forallE h1 h2

/-- A root eta expansion: function or structure eta of the whole term. -/
inductive RootStep (Γ : List VExpr) : VExpr → VExpr → Prop where
  | funEta {Y A A' B : VExpr} {u : VLevel} : Γ ⊢ Y : .forallE A B → Γ ⊢ A ≡ A' : .sort u →
      RootStep Γ Y (.lam A' (.app Y.lift (.bvar 0)))
  | structEta {Y : VExpr} {family : Name} {info : VProjectionInfo} {levels : List VLevel}
      {params params' : List VExpr} : Params.env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ Y : mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params Y : mkApps (.const family levels) params →
      params.length = params'.length →
      (∀ i (hi : i < params.length) (hi' : i < params'.length), EtaNE Γ params[i] params'[i]) →
      RootStep Γ Y (structExpand family info levels params' Y)

abbrev RootChain (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (RootStep Γ)

/-- A parallel eta step is a congruence step followed by root expansions. -/
theorem EtaPar.root_decomp {Γ : List VExpr} {X X' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (HX : EtaPar Γ X X') (hX : Γ ⊢ X : T) :
    ∃ X₀, EtaParC Γ X X₀ ∧ RootChain Γ X₀ X' := by
  induction HX generalizing T with
  | bvar => exact ⟨_, .bvar, .rfl⟩
  | sort => exact ⟨_, .sort, .rfl⟩
  | const => exact ⟨_, .const, .rfl⟩
  | elim => exact ⟨_, .elim, .rfl⟩
  | app h1 h2 => exact ⟨_, .app h1 h2, .rfl⟩
  | proj h => exact ⟨_, .proj h, .rfl⟩
  | lam h1 h2 => exact ⟨_, .lam h1 h2, .rfl⟩
  | forallE h1 h2 => exact ⟨_, .forallE h1 h2, .rfl⟩
  | funEta H₀ HA hPi ih _ =>
    obtain ⟨X₀, hc, hchain⟩ := ih hΓ hPi
    obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
    obtain ⟨⟨u, hA⟩, -⟩ := hPiT.forallE_inv henv.ordered
    exact ⟨X₀, hc, hchain.tail (.funEta ((EtaPar.full hΓ H₀ hPi).hasType hΓ hPi)
      ((EtaPar.full hΓ HA hA).defeq hΓ hA))⟩
  | structEta H₀ hlen hps hl hp hi hs hexp ih _ =>
    obtain ⟨X₀, hc, hchain⟩ := ih hΓ hs
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    refine ⟨X₀, hc, hchain.tail (.structEta hl hp hi ((EtaPar.full hΓ H₀ hs).hasType hΓ hs)
      ((FullReduction.structExpand (EtaPar.full hΓ H₀ hs)).hasType hΓ hexp) hlen
      fun i hi hi' => ?_)⟩
    obtain ⟨_, hpT⟩ := schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)
    exact EtaNE.of_etaPar hΓ (hps i hi hi') hpT

theorem RootStep.defeq {Γ : List VExpr} {Y Y' T : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (R : RootStep Γ Y Y') (hY : Γ ⊢ Y : T) : Γ ⊢ Y ≡ Y' := by
  cases R with
  | funEta hY' hA => exact (Wrap.eta .rfl hY' hA).defeq hΓ hY
  | structEta hl hp hi hY' hexp hlen hps => exact (Wrap.struct .rfl hl hp hi hY' hexp hlen hps).defeq hΓ hY

/-- Root expansions of the head of a spine on the right are absorbed. -/
theorem EtaNE.rootChain_spine_r {Γ : List VExpr} {s Y Y' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (hchain : RootChain Γ Y Y') :
    ∀ {as : List VExpr}, EtaNE Γ s (mkApps Y as) → EtaNE Γ s (mkApps Y' as) := by
  induction hchain with
  | rfl => intro _ H; exact H
  | tail _ step ih =>
    intro as H
    have H' := ih H
    cases step with
    | funEta hY₁ hA => exact EtaNE.wrap_r hΓ hs (.eta .rfl hY₁ hA) H'
    | structEta hl hp hi hY₁ hexp hlen hps =>
      exact EtaNE.wrap_r hΓ hs (.struct .rfl hl hp hi hY₁ hexp hlen hps) H'

/-- A step inside a lambda body is transported to the source's binder context. -/
theorem EtaPar.body_transport {Γ : List VExpr} {A A' b b' T : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hA : Γ ⊢ A ≡ A' : .sort u)
    (hb : A' :: Γ ⊢ b : T) (H : EtaPar (A' :: Γ) b b') : EtaPar (A :: Γ) b b' :=
  H.defeqDFC hΓ (.succ .zero hA.symm) hb

/-- Closure of the eta-normal relation under a parallel eta step on the right. -/
theorem EtaNE.etaPar_r {Γ : List VExpr} {s X X' T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hs : Γ ⊢ s : T) (H : EtaNE Γ s X)
    (HX : EtaPar Γ X X') : EtaNE Γ s X' := by
  induction H generalizing X' T with
  | bvar =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hs
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) EtaNE.bvar
  | sort =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hs
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) EtaNE.sort
  | const =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hs
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) EtaNE.const
  | elim =>
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hs
    cases hc
    exact EtaNE.rootChain_spine_r hΓ hs hchain (as := []) EtaNE.elim
  | @lamC Γ A A' b b' HA Hb ih1 ih2 =>
    obtain ⟨⟨u, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.lamC HA Hb).hasType hΓ hs
    have hAA' : Γ ⊢ A ≡ A' : .sort u := (HA.defeq hΓ hd).of_l henv hΓ hd
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | lam h1 h2 =>
      obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
      exact .lamC (ih1 hΓ hd h1) (ih2 hΓ' hb (EtaPar.body_transport hΓ hAA' hb' h2))
  | @lamD Γ A A' b b' u hA Hb ih =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hs.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.lamD hA Hb).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | lam h1 h2 =>
      obtain ⟨-, _, hb'⟩ := hX.lam_inv henv hΓ
      have hAA : Γ ⊢ A ≡ _ : .sort u :=
        hA.trans ((EtaPar.full hΓ h1 hA.hasType.2).defeq hΓ hA.hasType.2)
      exact .lamD hAA (ih hΓ' hb (EtaPar.body_transport hΓ hA hb' h2))
  | @forallEC Γ A A' B B' HA HB ih1 ih2 =>
    obtain ⟨⟨u, hd⟩, _, hb⟩ := hs.forallE_inv henv.ordered
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hd⟩
    have hX := (EtaNE.forallEC HA HB).hasType hΓ hs
    have hAA' : Γ ⊢ A ≡ A' : .sort u := (HA.defeq hΓ hd).of_l henv hΓ hd
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | forallE h1 h2 =>
      obtain ⟨-, _, hb'⟩ := hX.forallE_inv henv.ordered
      exact .forallEC (ih1 hΓ hd h1) (ih2 hΓ' hb (EtaPar.body_transport hΓ hAA' hb' h2))
  | app H1 H2 ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ
    have hX := (EtaNE.app H1 H2).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | app h1 h2 => exact .app (ih1 hΓ hf h1) (ih2 hΓ ha h2)
  | proj H1 ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hs.proj_inv henv hΓ
    have hX := (EtaNE.proj H1).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | proj h => exact .proj (ih hΓ hm.hasType.2 h)
  | @funEta Γ e A B A' body u hPi hA Hb ih =>
    have hX := (EtaNE.funEta hPi hA Hb).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    cases hc with
    | lam h1 h2 =>
      obtain ⟨_, hPiT⟩ := hPi.isType henv hΓ
      obtain ⟨-, _, hB⟩ := hPiT.forallE_inv henv.ordered
      have hΓ' : OnCtx (A' :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA.hasType.2⟩
      have hPi' : Γ ⊢ e : .forallE A' B := (IsDefEq.forallEDF hA hB).defeq hPi
      have hbody := eta_body_typed hPi'
      have hA'A'' : Γ ⊢ A' ≡ _ : .sort u := (EtaPar.full hΓ h1 hA.hasType.2).defeq hΓ hA.hasType.2
      have inner := ih hΓ' hbody h2
      exact .funEta hPi (hA.trans hA'A'') (inner.defeqDFC hΓ (.succ .zero hA'A'') hbody)
  | @structEta Γ family info levels params args e hl hp hi hs' hexp hlen hargs ih =>
    have hX := (EtaNE.structEta hl hp hi hs' hexp hlen hargs).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    have hargsT : ∀ i (hi : i < (structArgs family info params e).length),
        ∃ T, Γ ⊢ (structArgs family info params e)[i] : T := fun i hi => by
      rw [structExpand_eq] at hexp
      exact schema_mkApps_arg_type hΓ hexp (List.getElem_mem hi)
    -- the step on the constructor spine
    obtain ⟨H', args', hH, hF, hW⟩ :=
      EtaPar.spine_inv hΓ (args := args) hc.toEtaPar rfl hX
    have hlen' : (structArgs family info params e).length = args'.length :=
      hlen.trans (Lean4Lean.List.Forall₂.length_eq hF)
    have h1 : EtaNE Γ e (mkApps (.const info.ctorName levels) args') := by
      refine .structEta hl hp hi hs' hexp hlen' fun i hi hi' => ?_
      obtain ⟨_, hT⟩ := hargsT i hi
      exact ih i hi (by omega) hΓ hT (case_forall₂_get hF (by omega) hi')
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hX⟩
    obtain ⟨H₀, hc', hchain'⟩ := EtaPar.root_decomp hΓ hH hhead
    cases hc'
    exact EtaNE.wrap_r hΓ hs hW (as := []) (EtaNE.rootChain_spine_r hΓ hs hchain' h1)
  | @betaR Γ A b a s' T' args hT Hc ih =>
    have hX := (EtaNE.betaR hT Hc).hasType hΓ hs
    obtain ⟨X₀, hc, hchain⟩ := EtaPar.root_decomp hΓ HX hX
    refine EtaNE.rootChain_spine_r hΓ hs hchain (as := []) ?_
    obtain ⟨H', as', hH, hF, hW⟩ :=
      EtaPar.spine_inv hΓ (H := .lam A b) (args := a :: args) hc.toEtaPar rfl hX
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hT⟩
    have hhead' : Γ ⊢ .app (.lam A b) a : _ := hhead
    obtain ⟨A₁, B₁, hlam, ha⟩ := hhead'.app_inv henv hΓ
    obtain ⟨B, hPi, hb⟩ := hlam.lam_inv_forallE henv hΓ
    obtain ⟨⟨u, hAA₁⟩, -⟩ := IsDefEqU.forallE_inv henv hΓ hPi
    have ha' : Γ ⊢ a : A := hAA₁.defeq' ha
    obtain ⟨⟨_, hA⟩, -⟩ := hlam.lam_inv henv hΓ
    have hΓ' : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨L₀, hc', hchain'⟩ := EtaPar.root_decomp hΓ hH hlam
    cases hF with
    | cons ha₁ hargs =>
      cases hc' with
      | lam h1 h2 =>
        have hstep := EtaPar.congrRel.mkApps (EtaPar.instN .zero hΓ' ha₁ ha' h2 hb) hargs
        have h1' := ih hΓ hs hstep
        have hred : EtaPar Γ (mkApps (.app (.lam A b) a) args) (mkApps (.app (.lam _ _) _) _) :=
          EtaPar.congrRel.mkApps (.app (.lam h1 h2) ha₁) hargs
        have h2' := EtaNE.betaR ((EtaPar.full hΓ hred hT).hasType hΓ hT) h1'
        exact EtaNE.wrap_r hΓ hs hW (as := [])
          (EtaNE.rootChain_spine_r hΓ hs hchain' (as := _ :: _) h2')
  | redL h Hc ih => exact .redL h (ih hΓ (h.hasType hΓ hs) HX)

/-- Every eta chain from a typed term is an eta-normal expansion. -/
theorem EtaNE.of_etaChain {Γ : List VExpr} {e X T : VExpr}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : EtaChain Γ e X) (he : Γ ⊢ e : T) :
    EtaNE Γ e X := by
  induction H with
  | rfl => exact EtaNE.rfl
  | tail _ step ih => exact ih.etaPar_r hΓ he step

/-- OPEN: descent of the composite step (structure eta at a firing major, then the iota) on a
lift of a term typed below: the enclosing application is typed below, so the major has its
structure type below, and the iota discards the parameters (B2's analysis, not mechanised). -/
def MajorEtaDescends : Prop :=
  ∀ ⦃k Γ Γ' e T c⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ' (Params.env.IsType univs) → Γ ⊢ e : T → MajorEtaIota Γ' (e.liftN 1 k) c →
    ∃ e', c = e'.liftN 1 k ∧ FullReduction Γ e e'

/-- The descent of the composite step at any position follows from its descent at the root. -/
theorem MajorEtaIotaC.descend (hmajor : MajorEtaDescends) {k : Nat} {Γ Γ' : List VExpr}
    {e T c : VExpr} (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (he : Γ ⊢ e : T)
    (h : MajorEtaIotaC Γ' (e.liftN 1 k) c) : ∃ e', c = e'.liftN 1 k ∧ FullReduction Γ e e' := by
  generalize hs : e.liftN 1 k = s at h
  induction h generalizing e T k Γ with
  | root h => subst hs; exact hmajor W hΓ hΓ' he h
  | appL _ ih =>
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨_, _, hf, -⟩ := he.app_inv henv hΓ
    obtain ⟨f₁, rfl, hred⟩ := ih W hΓ hΓ' hf rfl
    exact ⟨.app f₁ a₀, rfl, hred.app .rfl⟩
  | appR _ ih =>
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨_, _, -, ha⟩ := he.app_inv henv hΓ
    obtain ⟨a₁, rfl, hred⟩ := ih W hΓ hΓ' ha rfl
    exact ⟨.app f₀ a₁, rfl, FullReduction.app .rfl hred⟩
  | proj _ ih =>
    obtain ⟨m₀, rfl, rfl⟩ := liftN_eq_proj_inv hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    obtain ⟨m₁, rfl, hred⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    exact ⟨_, rfl, hred.proj⟩
  | lamA _ ih =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hs
    obtain ⟨⟨_, hd⟩, _, -⟩ := he.lam_inv henv hΓ
    obtain ⟨A₁, rfl, hred⟩ := ih W hΓ hΓ' hd rfl
    exact ⟨.lam A₁ b₀, rfl, FullReduction.lam hred .rfl⟩
  | lamB _ ih =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hs
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv hΓ
    obtain ⟨b₁, rfl, hred⟩ := ih W.succ ⟨hΓ, _, hd⟩ ⟨hΓ', _, hd.weakN henv W⟩ hb rfl
    exact ⟨.lam A₀ b₁, rfl, FullReduction.lam .rfl hred⟩
  | forallEA _ ih =>
    obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := liftN_eq_forallE_inv hs
    obtain ⟨⟨_, hd⟩, _, -⟩ := he.forallE_inv henv.ordered
    obtain ⟨A₁, rfl, hred⟩ := ih W hΓ hΓ' hd rfl
    exact ⟨.forallE A₁ B₀, rfl, FullReduction.forallE hred .rfl⟩
  | forallEB _ ih =>
    obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := liftN_eq_forallE_inv hs
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv.ordered
    obtain ⟨B₁, rfl, hred⟩ := ih W.succ ⟨hΓ, _, hd⟩ ⟨hΓ', _, hd.weakN henv W⟩ hb rfl
    exact ⟨.forallE A₀ B₁, rfl, FullReduction.forallE .rfl hred⟩

/-- A lift of a type related to a `Π` reduces below to a `Π`: the steps at the root of the lift
descend (`Replay.lean` and `MajorEtaDescends`), the eta expansions at the root are excluded by
typing. -/
theorem EtaNE.forallE_inv_lift (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hunfold : UnfoldingCheckDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hmajor : MajorEtaDescends)
    {k : Nat} {Γ Γ' : List VExpr} {F A B : VExpr} {u : VLevel} (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (hF : Γ ⊢ F : .sort u) (H : EtaNE Γ' (F.liftN 1 k) (.forallE A B)) :
    ∃ A₀ B₀, FullReduction Γ F (.forallE A₀ B₀) := by
  generalize hs : F.liftN 1 k = s at H
  generalize hr : VExpr.forallE A B = r at H
  induction H generalizing F A B with
  | forallEC =>
    cases hr
    obtain ⟨A₀, B₀, rfl, -, -⟩ := liftN_eq_forallE_inv hs
    exact ⟨A₀, B₀, .rfl⟩
  | funEta hPi =>
    subst hs
    exact (type_not_function hΓ' (hF.weakN henv.ordered W) hPi).elim
  | structEta hl _ _ hs' =>
    subst hs
    exact (type_not_structure hΓ' (hF.weakN henv.ordered W) hl hs').elim
  | betaR hT =>
    exact (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ hr.symm).elim
  | redL h _ ih =>
    subst hs hr
    rcases h with (h | h) | h
    · obtain ⟨F₁, rfl, h'⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' hF h
      obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' ((FullStep.core h').hasType hΓ hF) rfl rfl
      exact ⟨A₂, B₂, (ReflTransGen.tail .rfl (.core h')).trans hred⟩
    · obtain ⟨F₁, rfl, h'⟩ := DeltaPar.descend hTF hunfold W hΓ hΓ' hF h
      obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' (h'.full.hasType hΓ hF) rfl rfl
      exact ⟨A₂, B₂, h'.full.trans hred⟩
    · obtain ⟨F₁, rfl, h'⟩ := MajorEtaIotaC.descend hmajor W hΓ hΓ' hF h
      obtain ⟨A₂, B₂, hred⟩ := ih W hΓ' (h'.hasType hΓ hF) rfl rfl
      exact ⟨A₂, B₂, h'.trans hred⟩
  | bvar | sort | const | elim | app | proj | lamC | lamD => cases hr

end

end Lean4Lean.VEnv.StrengtheningEtaNormal
