import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.Typing.PrefixUnfolding.ArgumentCongruence
import Lean4Lean.Theory.Typing.PrefixUnfolding.GenerationSupply
import Lean4Lean.Theory.Typing.ProjectionConstructorFamily
import Lean4Lean.Theory.LevelledConfluence
import Lean4Lean.Std.List

/-! # Levelled parallel relations for the full presentation

The full step relation is split into four parallel relations, ordered by
level for the decreasing-diagram criterion of `Lean4Lean.Levelled`:

0. normal equality without eta (`NormalEq₀`): structural, universe levels and
   proof irrelevance;
1. parallel reduction (`ParRed`): beta, stored-rule and registered case-schema patterns;
2. `DeltaPar`: parallel singleton prefix unfolding, quotient prefix unfolding and
   projection of constructor applications;
3. `EtaPar`: parallel function and structure eta expansion.

Eta expansion sits above beta. An expansion in the function position of a
redex blocks that redex, and the other side of the peak can only recover it by
a beta step followed by the original contraction, so the expansion side must
be allowed any number of lower steps.

## Why `FullStep.funEta` is not restricted to non-head positions

The alternative design keeps `FullStep` strongly closed by forbidding function
eta expansion in the function position of an application. The transports of
computation through normal equality need exactly those expansions:
`NormalEqN.beta_aux` (in `FullReduction`) matches a beta step on one side of a
normal equality whose eta derivation ends in `etaBoth`, by expanding the other
side with `FullStep.funEta`; through the `appDF` case that side is the function
of an application. `NormalEq.parRed` and `NormalEq.fullStep`, and hence
`FullReduction.church_rosser` and `IsDefEq.full_church_rosser`, depend on these
transports. Restricting `funEta` would have meant redesigning them, whereas the
levelled route keeps `FullStep` and its transports unchanged.

## Local diagrams

`levelled_joinable` (in `Lean4Lean.Theory.LevelledConfluence`) needs, for every
level, a same-level peak lemma and a peak lemma against each lower level:

* level 0: `NormalEq₀` is an equivalence, so its peaks close trivially;
* level 1: `ParRed.church_rosser` for `NormalEqF false`;
* level 2: `DeltaPar.peak` and `DeltaPar.parRed_peak`;
* level 3: `EtaPar.peak`, `EtaPar.deltaPar_peak` and `EtaPar.parRed_peak`;
* each level against level 0 by the `normalEq₀_mirror` lemmas.

The eta lemmas proceed by induction on the size of the source. A root eta
expansion on one side is peeled off with `Join3.fun_left` or
`Join3.struct_left`, and a root computation on the other side meets an eta
expansion of its head or major, which the `collapse_*` lemmas undo with a beta
or projection step at a lower level.

## Assumptions on `Params`

The prefix computation lemmas use the `Params` fields `pat_const_not_unfolding`,
`recursorData_quot`, `pat_ctor_rigid`, `projection_ctor_rigid`,
`pat_struct_major`, `pat_iota_params` and `schema_struct_major`. They state that
registered definition patterns do not overlap singleton and quotient prefix
unfolding, that constructors are rigid, and that recursor iota and case rules at
a structure constructor read its fields and not its parameters. Without them, a
pattern could overlap a singleton unfolding at the same head, and a structure eta
expansion of a major could not be undone by projection.
-/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- The structure eta expansion of `e` at the given structure. -/
def structExpand (family : Name) (info : VProjectionInfo) (levels : List VLevel)
    (params : List VExpr) (e : VExpr) : VExpr :=
  VExpr.mkApps (.const info.ctorName levels)
    (params ++ (List.range info.numFields).map fun index => .proj family index e)

/-- Parallel contraction of singleton prefix unfoldings, quotient prefix
unfoldings and projections of constructor applications. Arguments are
developed before the redex is contracted. -/
inductive DeltaPar : List VExpr → VExpr → VExpr → Prop where
  | bvar : DeltaPar Γ (.bvar i) (.bvar i)
  | sort : DeltaPar Γ (.sort u) (.sort u)
  | const : DeltaPar Γ (.const c ls) (.const c ls)
  | elim : DeltaPar Γ (.elim block owner ls) (.elim block owner ls)
  | app : DeltaPar Γ f f' → DeltaPar Γ a a' → DeltaPar Γ (.app f a) (.app f' a')
  | proj : DeltaPar Γ major major' →
      DeltaPar Γ (.proj family index major) (.proj family index major')
  | lam : DeltaPar Γ A A' → DeltaPar (A :: Γ) body body' →
      DeltaPar Γ (.lam A body) (.lam A' body')
  | forallE : DeltaPar Γ A A' → DeltaPar (A :: Γ) body body' →
      DeltaPar Γ (.forallE A body) (.forallE A' body')
  | delta {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      PrefixUnfold env univs recursorData Γ name levels args' rhs →
      DeltaPar Γ (VExpr.mkApps (.const name levels) args) rhs
  | quotDelta {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      QuotPrefixUnfold env univs Γ levels args' rhs →
      DeltaPar Γ (VExpr.mkApps (.const ``Quot.lift levels) args) rhs
  | projIota {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      env.projections family info →
      Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName levels) args') : fieldType →
      args'[info.nparams + index]? = some field → Γ ⊢ field : fieldType →
      DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) field

/-- Parallel function and structure eta expansion. The expanded term is
developed before it is expanded. -/
inductive EtaPar : List VExpr → VExpr → VExpr → Prop where
  | bvar : EtaPar Γ (.bvar i) (.bvar i)
  | sort : EtaPar Γ (.sort u) (.sort u)
  | const : EtaPar Γ (.const c ls) (.const c ls)
  | elim : EtaPar Γ (.elim block owner ls) (.elim block owner ls)
  | app : EtaPar Γ f f' → EtaPar Γ a a' → EtaPar Γ (.app f a) (.app f' a')
  | proj : EtaPar Γ major major' →
      EtaPar Γ (.proj family index major) (.proj family index major')
  | lam : EtaPar Γ A A' → EtaPar (A :: Γ) body body' →
      EtaPar Γ (.lam A body) (.lam A' body')
  | forallE : EtaPar Γ A A' → EtaPar (A :: Γ) body body' →
      EtaPar Γ (.forallE A body) (.forallE A' body')
  | funEta : EtaPar Γ e e' → EtaPar Γ A A' → Γ ⊢ e : .forallE A B →
      EtaPar Γ e (.lam A' (.app e'.lift (.bvar 0)))
  | structEta {params params' : List VExpr} : EtaPar Γ e e' →
      (hlen : params.length = params'.length) →
      (∀ i (hi : i < params.length) (hi' : i < params'.length),
        EtaPar Γ params[i] params'[i]) →
      env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ e : VExpr.mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params e : VExpr.mkApps (.const family levels) params →
      EtaPar Γ e (structExpand family info levels params' e')

section Basic

omit [Params] in
theorem getElem_of_forall₂ {R : α → β → Prop} {l : List α} {l' : List β}
    (H : List.Forall₂ R l l') : l.length = l'.length ∧
      ∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i] :=
  ⟨Lean4Lean.List.Forall₂.length_eq H, fun _ hi hi' => case_forall₂_get H hi hi'⟩

protected theorem DeltaPar.rfl : ∀ {e}, DeltaPar Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app DeltaPar.rfl DeltaPar.rfl
  | .proj .. => .proj DeltaPar.rfl
  | .lam .. => .lam DeltaPar.rfl DeltaPar.rfl
  | .forallE .. => .forallE DeltaPar.rfl DeltaPar.rfl

protected theorem EtaPar.rfl : ∀ {e}, EtaPar Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app EtaPar.rfl EtaPar.rfl
  | .proj .. => .proj EtaPar.rfl
  | .lam .. => .lam EtaPar.rfl EtaPar.rfl
  | .forallE .. => .forallE EtaPar.rfl EtaPar.rfl

theorem FullReduction.mkApps_args (H : List.Forall₂ (FullReduction Γ) args args') :
    FullReduction Γ (VExpr.mkApps fn args) (VExpr.mkApps fn args') :=
  FullReduction.mkApps .rfl H

theorem DeltaPar.full (H : DeltaPar Γ e e') : FullReduction Γ e e' := by
  induction H with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | proj _ ih => exact ih.proj
  | lam _ _ ih1 ih2 => exact ih1.lam ih2
  | forallE _ _ ih1 ih2 => exact ih1.forallE ih2
  | delta hlen _ hr ih =>
    exact (FullReduction.mkApps_args (List.forall₂_of_getElem hlen ih)).tail (.delta hr)
  | quotDelta hlen _ hr ih =>
    exact (FullReduction.mkApps_args (List.forall₂_of_getElem hlen ih)).tail (.quotDelta hr)
  | projIota hlen _ hl hs hi ht ih =>
    exact (FullReduction.mkApps_args (List.forall₂_of_getElem hlen ih)).proj.tail
      (.projIota hl hs hi ht)

theorem FullReduction.structExpand (H : FullReduction Γ e e') :
    FullReduction Γ (structExpand family info levels params e)
      (structExpand family info levels params e') := by
  refine FullReduction.mkApps_args (List.Forall₂.append' ?_ ?_)
  · exact List.Forall₂.rfl fun _ _ => .rfl
  · induction (List.range info.numFields) with
    | nil => exact .nil
    | cons _ _ ih => exact .cons H.proj ih

theorem EtaPar.full (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaPar Γ e e')
    (he : Γ ⊢ e : T) : FullReduction Γ e e' := by
  induction H generalizing T with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact (ih1 hΓ h1).app (ih2 hΓ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    exact (ih hΓ hm.hasType.2).proj
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact (ih1 hΓ h1).lam (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact (ih1 hΓ h1).forallE (ih2 ⟨hΓ, _, h1⟩ h2)
  | funEta _ _ ht ih ihA =>
    have h := ih hΓ ht
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv hΓ; h.forallE_inv henv
    exact (h.tail (.funEta (h.hasType hΓ ht))).trans ((ihA hΓ hA).lam .rfl)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    have h := ih hΓ hs
    obtain ⟨_, hT⟩ := hs.isType henv hΓ
    have hps : List.Forall₂ (FullReduction _) _ _ := List.forall₂_of_getElem hlen fun i hi hi' =>
      ihp i hi hi' hΓ (schema_mkApps_arg_type hΓ hT (List.getElem_mem hi)).choose_spec
    refine (h.tail (.structEta hl hp hi (h.hasType hΓ hs)
      ((FullReduction.structExpand h).hasType hΓ hc))).trans ?_
    exact FullReduction.mkApps_args (List.Forall₂.append' hps (List.Forall₂.rfl fun _ _ => .rfl))

/-! ### Substitution of definitionally equal arguments -/

theorem _root_.Lean4Lean.Ctx.InstN.substEq (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀) :
    Ctx.SubstEq env univs Γ ((VExpr.Subst.one a₁).liftN k) ((VExpr.Subst.one a₂).liftN k) Γ₁ := by
  induction W with
  | zero =>
    obtain ⟨hΓ₀, _, hA⟩ := hΓ₁
    refine .cons (Ctx.SubstEq.id henv.ordered hΓ₀) hA ?_
    show Γ₀ ⊢ a₁ ≡ a₂ : A₀.subst .id
    rw [subst_id]; exact ha
  | succ W ih =>
    obtain ⟨hΓ₁', _, hA⟩ := hΓ₁
    have := (ih hΓ₁').lift henv.ordered hA
    rwa [← instN_eq] at this

theorem HasType.instN_DF (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀) (H : Γ₁ ⊢ e : A) : Γ ⊢ e.inst a₁ k ≡ e.inst a₂ k : A.inst a₁ k := by
  have hΓ := (W.wf henv.ordered ha.hasType.1 hΓ₁).2
  simpa only [← instN_eq] using IsDefEq.substDF henv.ordered hΓ₁ hΓ (W.substEq hΓ₁ ha) H

theorem _root_.Lean4Lean.Ctx.InstN.defeqCtx (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (ha : Γ₀ ⊢ a₁ ≡ a₂ : A₀) :
    ∃ Γ', Ctx.InstN Γ₀ a₂ A₀ k Γ₁ Γ' ∧ IsDefEqCtx env univs Γ₀ Γ' Γ := by
  induction W with
  | zero => exact ⟨_, .zero, .zero⟩
  | succ W ih =>
    obtain ⟨hΓ₁', _, hA⟩ := hΓ₁
    obtain ⟨Γ', W', hc⟩ := ih hΓ₁'
    exact ⟨_, .succ W', .succ hc (HasType.instN_DF W' hΓ₁' ha.symm hA)⟩

/-! ### Weakening, context conversion and substitution -/

theorem DeltaPar.weakN (W : Ctx.LiftN n k Γ Γ') (H : DeltaPar Γ e e') :
    DeltaPar Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | delta hlen _ hr ih =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .delta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W)
      (hr.weakN henv W)
  | quotDelta hlen _ hr ih =>
    simp only [VExpr.liftN_mkApps, VExpr.liftN]
    exact .quotDelta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W)
      (hr.weakN henv W)
  | projIota hlen _ hl hs hi ht ih =>
    have hs' := hs.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN] at hs' ⊢
    exact .projIota (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W)
      hl hs' (by simp [hi]) (ht.weakN henv W)

theorem DeltaPar.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : DeltaPar Γ₁ e e') (he : Γ₁ ⊢ e : A) : DeltaPar Γ₂ e e' := by
  induction H generalizing Γ₂ A with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hd) (ih2 (.succ W hd) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hd) (ih2 (.succ W hd) hb)
  | delta hlen _ hr ih =>
    exact .delta hlen (fun i hi hi' => ih i hi hi' W
      (schema_mkApps_arg_type (W.isType' hΓ) he (List.getElem_mem hi)).choose_spec)
      (hr.defeqDFC henv hΓ W)
  | quotDelta hlen _ hr ih =>
    exact .quotDelta hlen (fun i hi hi' => ih i hi hi' W
      (schema_mkApps_arg_type (W.isType' hΓ) he (List.getElem_mem hi)).choose_spec)
      (hr.defeqDFC henv hΓ W)
  | projIota hlen _ hl hs hi ht ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .projIota hlen (fun i hi' hi'' => ih i hi' hi'' W
      (schema_mkApps_arg_type (W.isType' hΓ) hm.hasType.2 (List.getElem_mem hi')).choose_spec)
      hl (hs.defeqDFC henv W) hi (ht.defeqDFC henv W)

theorem DeltaPar.instN (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (H₀ : DeltaPar Γ₀ a₁ a₂) (h₀ : Γ₀ ⊢ a₁ : A₀)
    (H : DeltaPar Γ₁ e e') (he : Γ₁ ⊢ e : T) : DeltaPar Γ (e.inst a₁ k) (e'.inst a₂ k) := by
  have hΓ₀ := (W.wf henv.ordered h₀ hΓ₁).1
  have ha := (DeltaPar.full H₀).defeq hΓ₀ h₀
  have h₂ := ha.hasType.2
  induction H generalizing Γ k T with
  | @bvar _ i =>
    clear he hΓ₁
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact (ih ..).weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ₁
    exact .app (ih1 W hΓ₁ h1) (ih2 W hΓ₁ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    exact .proj (ih W hΓ₁ hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ₁
    exact .lam (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | delta hlen _ hr ih =>
    obtain ⟨Γ', W', hc⟩ := W.defeqCtx hΓ₁ ha
    have hr' := (hr.instN henv W' h₂).defeqDFC henv hΓ₀ hc
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .delta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ he (List.getElem_mem (by simpa using hi))).choose_spec)
      hr'
  | quotDelta hlen _ hr ih =>
    obtain ⟨Γ', W', hc⟩ := W.defeqCtx hΓ₁ ha
    have hr' := (hr.instN henv W' h₂).defeqDFC henv hΓ₀ hc
    simp only [VExpr.inst_mkApps, VExpr.inst]
    exact .quotDelta (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ he (List.getElem_mem (by simpa using hi))).choose_spec)
      hr'
  | projIota hlen _ hl hs hi ht ih =>
    obtain ⟨Γ', W', hc⟩ := W.defeqCtx hΓ₁ ha
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    have hs' := (hs.instN henv W' h₂).defeqDFC henv hc
    have ht' := (ht.instN henv W' h₂).defeqDFC henv hc
    simp only [VExpr.inst_mkApps, VExpr.inst] at hs' ⊢
    exact .projIota (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ih i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ hm.hasType.2
            (List.getElem_mem (by simpa using hi))).choose_spec)
      hl hs' (by simp [hi]) ht'

omit [Params] in
theorem structExpand_liftN :
    (structExpand family info levels params e).liftN n k =
      structExpand family info levels (params.map (·.liftN n k)) (e.liftN n k) := by
  simp [structExpand, VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map,
    Function.comp_def]

omit [Params] in
theorem structExpand_inst :
    (structExpand family info levels params e).inst a k =
      structExpand family info levels (params.map (·.inst a k)) (e.inst a k) := by
  simp [structExpand, VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
    Function.comp_def]

theorem EtaPar.weakN (W : Ctx.LiftN n k Γ Γ') (H : EtaPar Γ e e') :
    EtaPar Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | funEta _ _ ht ih ihA =>
    simpa only [VExpr.liftN, ← VExpr.lift_liftN', liftVar_zero] using
      EtaPar.funEta (ih W) (ihA W) (ht.weakN henv W)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    have hs' := hs.weakN henv W
    have hc' := hc.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, structExpand_liftN] at hs' hc' ⊢
    exact .structEta (ih W) (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ihp i (by simpa using hi) (by simpa using hi') W)
      hl (by simpa using hp) hi hs' hc'

theorem EtaPar.defeqDFC (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : EtaPar Γ₁ e e') (he : Γ₁ ⊢ e : A) : EtaPar Γ₂ e e' := by
  induction H generalizing Γ₂ A with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv (W.isType' hΓ)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      he.proj_inv henv (W.isType' hΓ)
    exact .proj (ih W hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.lam_inv henv (W.isType' hΓ)
    exact .lam (ih1 W hd) (ih2 (.succ W hd) hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hd) (ih2 (.succ W hd) hb)
  | funEta _ _ ht ih ihA =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv (W.isType' hΓ); h.forallE_inv henv
    exact .funEta (ih W ht) (ihA W hA) (ht.defeqDFC henv W)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    obtain ⟨_, hT⟩ := hs.isType henv (W.isType' hΓ)
    exact .structEta (ih W hs) hlen (fun i hi hi' => ihp i hi hi' W
      (schema_mkApps_arg_type (W.isType' hΓ) hT (List.getElem_mem hi)).choose_spec)
      hl hp hi (hs.defeqDFC henv W) (hc.defeqDFC henv W)

theorem EtaPar.instN (W : Ctx.InstN Γ₀ a₁ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (H₀ : EtaPar Γ₀ a₁ a₂) (h₀ : Γ₀ ⊢ a₁ : A₀)
    (H : EtaPar Γ₁ e e') (he : Γ₁ ⊢ e : T) : EtaPar Γ (e.inst a₁ k) (e'.inst a₂ k) := by
  induction H generalizing Γ k T with
  | @bvar _ i =>
    clear he hΓ₁
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact (ih ..).weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ₁
    exact .app (ih1 W hΓ₁ h1) (ih2 W hΓ₁ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    exact .proj (ih W hΓ₁ hm.hasType.2)
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ₁
    exact .lam (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .forallE (ih1 W hΓ₁ h1) (ih2 W.succ ⟨hΓ₁, _, h1⟩ h2)
  | funEta _ _ ht ih ihA =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv hΓ₁; h.forallE_inv henv
    simpa only [VExpr.inst, ← VExpr.lift_instN_lo, instVar, if_pos (Nat.zero_lt_succ k)] using
      EtaPar.funEta (ih W hΓ₁ ht) (ihA W hΓ₁ hA) (ht.instN henv W h₀)
  | structEta _ hlen _ hl hp hi hs hc ih ihp =>
    obtain ⟨_, hT⟩ := hs.isType henv hΓ₁
    have hs' := hs.instN henv W h₀
    have hc' := hc.instN henv W h₀
    simp only [VExpr.inst_mkApps, VExpr.inst, structExpand_inst] at hs' hc' ⊢
    exact .structEta (ih W hΓ₁ hs) (by simpa using hlen)
      (fun i hi hi' => by
        simpa only [List.getElem_map] using ihp i (by simpa using hi) (by simpa using hi') W hΓ₁
          (schema_mkApps_arg_type hΓ₁ hT (List.getElem_mem (by simpa using hi))).choose_spec)
      hl (by simpa using hp) hi hs' hc'

end Basic

section LevelDefs

/-- The untyped level relations. -/
def LevelStep (Γ : List VExpr) : Nat → VExpr → VExpr → Prop
  | 0 => NormalEq₀ Γ
  | 1 => ParRed Γ
  | 2 => DeltaPar Γ
  | 3 => EtaPar Γ
  | _ + 4 => fun _ _ => False

/-- Some step below level `n`. -/
def Below (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop := ∃ k, k < n ∧ LevelStep Γ k a b

/-- The level relations restricted to typed sources, for the abstract criterion. -/
def LevelRel (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop :=
  (∃ A, Γ ⊢ a : A) ∧ LevelStep Γ n a b

theorem LevelStep.full (hΓ : OnCtx Γ (env.IsType univs)) (hn : 0 < n)
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : FullReduction Γ a b := by
  match n, H with
  | 1, H => exact .tail .rfl (.core H)
  | 2, H => exact DeltaPar.full H
  | 3, H => exact EtaPar.full hΓ H ha

theorem LevelStep.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  match n, H with
  | 0, H => exact ((NormalEqF.defeq hΓ H).of_l henv hΓ ha).hasType.2
  | n + 1, H => exact (LevelStep.full hΓ (Nat.succ_pos _) H ha).hasType hΓ ha

theorem Below.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  induction H with
  | rfl => exact ha
  | tail _ h ih => obtain ⟨_, _, h⟩ := h; exact h.hasType hΓ ih

theorem Below.loStar (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) :
    Levelled.LoStar (LevelRel Γ) n a b := by
  induction H with
  | rfl => exact .rfl
  | tail h₁ h ih =>
    obtain ⟨k, hk, h⟩ := h
    exact .tail ih ⟨k, hk, ⟨_, Below.hasType hΓ h₁ ha⟩, h⟩

theorem Below.ofLoStar (H : Levelled.LoStar (LevelRel Γ) n a b) :
    ReflTransGen (Below Γ n) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => obtain ⟨k, hk, _, h⟩ := h; exact .tail ih ⟨k, hk, h⟩

theorem Below.single (hk : k < n) (H : LevelStep Γ k a b) : ReflTransGen (Below Γ n) a b :=
  .tail .rfl ⟨k, hk, H⟩

/-- Pushing the normal equalities of a levelled reduction to its end. -/
theorem Below.full (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) :
    ∃ a', FullReduction Γ a a' ∧ NormalEq Γ a' b := by
  induction H with
  | rfl => exact ⟨_, .rfl, .refl ha⟩
  | tail h₁ h ih =>
    obtain ⟨a', hr, he⟩ := ih
    obtain ⟨k, _, h⟩ := h
    have hm := Below.hasType hΓ h₁ ha
    cases k with
    | zero => exact ⟨a', hr, he.trans hΓ (NormalEqF.toNormalEq h)⟩
    | succ k =>
      obtain ⟨out, h1, h2⟩ := he.fullReduction hΓ (h.full hΓ (Nat.succ_pos _) hm)
      exact ⟨out, hr.trans h1, h2⟩


theorem LevelStep.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : Γ ⊢ a ≡ b : A := by
  match n, H with
  | 0, H => exact (NormalEqF.defeq hΓ H).of_l henv hΓ ha
  | n + 1, H => exact (LevelStep.full hΓ (Nat.succ_pos _) H ha).defeq hΓ ha

theorem Below.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) : Γ ⊢ a ≡ b : A := by
  induction H with
  | rfl => exact ha
  | tail h₁ h ih =>
    obtain ⟨_, _, h⟩ := h
    exact ih.trans (h.defeq hΓ (Below.hasType hΓ h₁ ha))

theorem Below.pres {P : VExpr → Prop}
    (hpres : ∀ {k a b}, P a → LevelStep Γ' k a b → P b)
    (H : ReflTransGen (Below Γ' n) a b) (ha : P a) : P b := by
  induction H with
  | rfl => exact ha
  | tail _ h ih => obtain ⟨_, _, h⟩ := h; exact hpres ih h

/-- Lift a levelled reduction through a congruence, one step at a time. -/
theorem Below.congr {f : VExpr → VExpr} {P : VExpr → Prop}
    (hstep : ∀ {k a b}, P a → LevelStep Γ' k a b → LevelStep Γ k (f a) (f b))
    (hpres : ∀ {k a b}, P a → LevelStep Γ' k a b → P b)
    (H : ReflTransGen (Below Γ' n) a b) (ha : P a) :
    ReflTransGen (Below Γ n) (f a) (f b) := by
  induction H with
  | rfl => exact .rfl
  | @tail b' c' h₁ h ih =>
    obtain ⟨k, hk, h⟩ := h
    have hP : P b' := Below.pres hpres h₁ ha
    exact ih.tail ⟨k, hk, hstep hP h⟩

theorem LevelStep.app_l (hf : Γ ⊢ f : .forallE X Y) (hx : Γ ⊢ x : X)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : LevelStep Γ k f f') :
    LevelStep Γ k (.app f x) (.app f' x) := by
  match k, H with
  | 0, H => exact NormalEqF.appDF hf (H.hasType hΓ hf) hx hx H (.refl hx)
  | 1, H => exact ParRed.app H .rfl
  | 2, H => exact DeltaPar.app H .rfl
  | 3, H => exact EtaPar.app H .rfl
  | _ + 4, H => exact H.elim

theorem LevelStep.app_r (hf : Γ ⊢ f : .forallE X Y) (hx : Γ ⊢ x : X)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : LevelStep Γ k x x') :
    LevelStep Γ k (.app f x) (.app f x') := by
  match k, H with
  | 0, H => exact NormalEqF.appDF hf hf hx (H.hasType hΓ hx) (.refl hf) H
  | 1, H => exact ParRed.app .rfl H
  | 2, H => exact DeltaPar.app .rfl H
  | 3, H => exact EtaPar.app .rfl H
  | _ + 4, H => exact H.elim

theorem Below.app (hΓ : OnCtx Γ (env.IsType univs))
    (hf : ReflTransGen (Below Γ n) f f') (hx : ReflTransGen (Below Γ n) x x')
    (ht : Γ ⊢ .app f x : T) : ReflTransGen (Below Γ n) (.app f x) (.app f' x') := by
  obtain ⟨X, Y, tf, tx⟩ := ht.app_inv henv hΓ
  have h1 := Below.congr (f := (VExpr.app · x)) (P := fun g => Γ ⊢ g : .forallE X Y)
    (fun hP h => h.app_l hP tx hΓ) (fun hP h => h.hasType hΓ hP) hf tf
  have tf' := Below.hasType hΓ hf tf
  have h2 := Below.congr (f := VExpr.app f') (P := fun g => Γ ⊢ g : X)
    (fun hP h => h.app_r tf' hP hΓ) (fun hP h => h.hasType hΓ hP) hx tx
  exact h1.trans h2

theorem Below.mkApps (hΓ : OnCtx Γ (env.IsType univs))
    (hf : ReflTransGen (Below Γ n) f f') (hs : List.Forall₂ (ReflTransGen (Below Γ n)) as as')
    (ht : Γ ⊢ VExpr.mkApps f as : T) :
    ReflTransGen (Below Γ n) (VExpr.mkApps f as) (VExpr.mkApps f' as') := by
  induction hs generalizing f f' with
  | nil => exact hf
  | cons h _ ih =>
    obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app f _) ht
    exact ih (Below.app hΓ hf h happ) ht

theorem LevelStep.proj
    (ht : Γ ⊢ .proj s i m : T) (H : LevelStep Γ k m m') :
    LevelStep Γ k (.proj s i m) (.proj s i m') := by
  match k, H with
  | 0, H => exact NormalEqF.projDF ht H
  | 1, H => exact ParRed.proj H
  | 2, H => exact DeltaPar.proj H
  | 3, H => exact EtaPar.proj H
  | _ + 4, H => exact H.elim

theorem Below.proj (hΓ : OnCtx Γ (env.IsType univs))
    (hm : ReflTransGen (Below Γ n) m m') (ht : Γ ⊢ .proj s i m : T) :
    ReflTransGen (Below Γ n) (.proj s i m) (.proj s i m') := by
  have := Below.congr (f := VExpr.proj s i) (P := fun g => Γ ⊢ .proj s i g : T)
    (fun hP h => LevelStep.proj hP h)
    (fun hP h => (LevelStep.proj hP h).hasType hΓ hP) hm ht
  exact this

theorem LevelStep.lam_body (hD : Γ ⊢ D : .sort u)
    (H : LevelStep (D :: Γ) k b b') :
    LevelStep Γ k (.lam D b) (.lam D b') := by
  match k, H with
  | 0, H => exact NormalEqF.lamDF hD hD H
  | 1, H => exact ParRed.lam .rfl H
  | 2, H => exact DeltaPar.lam .rfl H
  | 3, H => exact EtaPar.lam .rfl H
  | _ + 4, H => exact H.elim

theorem LevelStep.lam_dom (hΓ : OnCtx Γ (env.IsType univs)) (hD : Γ ⊢ D : .sort u)
    (hb : D :: Γ ⊢ b : B) (H : LevelStep Γ k D D') :
    LevelStep Γ k (.lam D b) (.lam D' b) := by
  match k, H with
  | 0, H =>
    have hDD := (NormalEqF.defeq hΓ H).of_l henv hΓ hD
    exact NormalEqF.lamDF hD hDD (.refl hb)
  | 1, H => exact ParRed.lam H .rfl
  | 2, H => exact DeltaPar.lam H .rfl
  | 3, H => exact EtaPar.lam H .rfl
  | _ + 4, H => exact H.elim

theorem Below.lam (hΓ : OnCtx Γ (env.IsType univs))
    (hD : ReflTransGen (Below Γ n) D D') (hb : ReflTransGen (Below (D :: Γ) n) b b')
    (ht : Γ ⊢ .lam D b : T) : ReflTransGen (Below Γ n) (.lam D b) (.lam D' b') := by
  obtain ⟨⟨_, tD⟩, _, tb⟩ := ht.lam_inv henv hΓ
  have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have h1 := Below.congr (f := VExpr.lam D) (P := fun g => D :: Γ ⊢ g : _)
    (fun hP h => h.lam_body tD) (fun hP h => h.hasType hΓ' hP) hb tb
  have tb' := Below.hasType hΓ' hb tb
  have hDD := Below.defeq hΓ hD tD
  have h2 := Below.congr (f := (VExpr.lam · b')) (P := fun g => Γ ⊢ g : _ ∧ Γ ⊢ D ≡ g)
    (fun hP h => by
      have tb'' := tb'.defeqDFC henv (.succ .zero (hP.2.of_l henv hΓ tD))
      exact h.lam_dom hΓ hP.1 tb'' )
    (fun hP h => ⟨h.hasType hΓ hP.1, hP.2.trans henv hΓ ⟨_, h.defeq hΓ hP.1⟩⟩) hD ⟨tD, ⟨_, tD⟩⟩
  exact h1.trans h2

theorem LevelStep.forallE_body (hD : Γ ⊢ D : .sort u)
    (hb : D :: Γ ⊢ b : .sort v) (H : LevelStep (D :: Γ) k b b') :
    LevelStep Γ k (.forallE D b) (.forallE D b') := by
  match k, H with
  | 0, H => exact NormalEqF.forallEDF hD (.refl hD) hb H
  | 1, H => exact ParRed.forallE .rfl H
  | 2, H => exact DeltaPar.forallE .rfl H
  | 3, H => exact EtaPar.forallE .rfl H
  | _ + 4, H => exact H.elim

theorem LevelStep.forallE_dom (hD : Γ ⊢ D : .sort u)
    (hb : D :: Γ ⊢ b : .sort v) (H : LevelStep Γ k D D') :
    LevelStep Γ k (.forallE D b) (.forallE D' b) := by
  match k, H with
  | 0, H =>
    exact NormalEqF.forallEDF hD H hb (.refl hb)
  | 1, H => exact ParRed.forallE H .rfl
  | 2, H => exact DeltaPar.forallE H .rfl
  | 3, H => exact EtaPar.forallE H .rfl
  | _ + 4, H => exact H.elim

theorem Below.forallE (hΓ : OnCtx Γ (env.IsType univs))
    (hD : ReflTransGen (Below Γ n) D D') (hb : ReflTransGen (Below (D :: Γ) n) b b')
    (ht : Γ ⊢ .forallE D b : T) : ReflTransGen (Below Γ n) (.forallE D b) (.forallE D' b') := by
  obtain ⟨⟨_, tD⟩, _, tb⟩ := ht.forallE_inv henv
  have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have h1 := Below.congr (f := VExpr.forallE D) (P := fun g => D :: Γ ⊢ g : .sort _)
    (fun hP h => h.forallE_body tD hP) (fun hP h => h.hasType hΓ' hP) hb tb
  have tb' := Below.hasType hΓ' hb tb
  have hDD := Below.defeq hΓ hD tD
  have h2 := Below.congr (f := (VExpr.forallE · b')) (P := fun g => Γ ⊢ g : _ ∧ Γ ⊢ D ≡ g)
    (fun hP h => by
      have tb'' := tb'.defeqDFC henv (.succ .zero (hP.2.of_l henv hΓ tD))
      exact h.forallE_dom hP.1 tb'')
    (fun hP h => ⟨h.hasType hΓ hP.1, hP.2.trans henv hΓ ⟨_, h.defeq hΓ hP.1⟩⟩) hD ⟨tD, ⟨_, tD⟩⟩
  exact h1.trans h2

theorem Below.ofParRedS (H : ReflTransGen (ParRed Γ) a b) (hn : 1 < n) :
    ReflTransGen (Below Γ n) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.tail ⟨1, hn, h⟩


theorem LevelStep.weakN (W : Ctx.LiftN n k Γ Γ') (H : LevelStep Γ m a b) :
    LevelStep Γ' m (a.liftN n k) (b.liftN n k) := by
  match m, H with
  | 0, H => exact NormalEqF.weakN W H
  | 1, H => exact ParRed.weakN W H
  | 2, H => exact DeltaPar.weakN W (H : DeltaPar _ _ _)
  | 3, H => exact EtaPar.weakN W (H : EtaPar _ _ _)
  | _ + 4, H => exact H.elim

theorem Below.weakN (W : Ctx.LiftN n k Γ Γ') (H : ReflTransGen (Below Γ m) a b) :
    ReflTransGen (Below Γ' m) (a.liftN n k) (b.liftN n k) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => obtain ⟨j, hj, h⟩ := h; exact ih.tail ⟨j, hj, h.weakN W⟩

/-- A levelled step of the body, instantiated at the outermost variable. -/
theorem LevelStep.inst0 (hΓ : OnCtx Γ (env.IsType univs)) (hx : Γ ⊢ x : D)
    (H : LevelStep (D :: Γ) m t t') (ht : D :: Γ ⊢ t : B) :
    LevelStep Γ m (t.inst x) (t'.inst x) := by
  have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, (hx.isType henv hΓ)⟩
  match m, H with
  | 0, H => exact NormalEqF.instN hx .zero H
  | 1, H => exact ParRed.instN (H₀ := .rfl) (H₀' := hx) .zero H
  | 2, H => exact DeltaPar.instN .zero hΓ' .rfl hx (H : DeltaPar _ _ _) ht
  | 3, H => exact EtaPar.instN .zero hΓ' .rfl hx (H : EtaPar _ _ _) ht
  | _ + 4, H => exact H.elim

/-- A levelled step of the argument, substituted into a fixed body. -/
theorem LevelStep.inst0_r (hΓ : OnCtx Γ (env.IsType univs)) (hx : Γ ⊢ x : D)
    (H : LevelStep Γ m x x') (ht : D :: Γ ⊢ t : B) :
    LevelStep Γ m (t.inst x) (t.inst x') := by
  have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, (hx.isType henv hΓ)⟩
  match m, H with
  | 0, H => exact NormalEqF.instN_r hΓ' hx H .zero ht
  | 1, H => exact ParRed.instN (H₀ := H) (H₀' := hx) .zero .rfl
  | 2, H => exact DeltaPar.instN .zero hΓ' (H : DeltaPar _ _ _) hx .rfl ht
  | 3, H => exact EtaPar.instN .zero hΓ' (H : EtaPar _ _ _) hx .rfl ht
  | _ + 4, H => exact H.elim

theorem Below.inst0 (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below (D :: Γ) m) t t') (Hx : ReflTransGen (Below Γ m) x x')
    (ht : D :: Γ ⊢ t : B) (hx : Γ ⊢ x : D) :
    ReflTransGen (Below Γ m) (t.inst x) (t'.inst x') := by
  have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, (hx.isType henv hΓ)⟩
  have h1 := Below.congr (f := (·.inst x)) (P := fun g => D :: Γ ⊢ g : B)
    (fun hP h => h.inst0 hΓ hx hP) (fun hP h => h.hasType hΓ' hP) H ht
  have ht' := Below.hasType hΓ' H ht
  have h2 := Below.congr (f := t'.inst) (P := fun g => Γ ⊢ g : D)
    (fun hP h => h.inst0_r hΓ hP ht') (fun hP h => h.hasType hΓ hP) Hx hx
  exact h1.trans h2

end LevelDefs




section Relations

theorem ParRed.congrRel : CongrRel ParRed where
  rfl := ParRed.rfl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN W h := h.weakN W

theorem DeltaPar.congrRel : CongrRel DeltaPar where
  rfl := DeltaPar.rfl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN W h := h.weakN W

theorem EtaPar.congrRel : CongrRel EtaPar where
  rfl := EtaPar.rfl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN W h := h.weakN W

theorem ParRed.argRel : ArgRel ParRed :=
  ParRed.congrRel.argRel fun hΓ h ha => h.defeq hΓ ha

theorem DeltaPar.argRel : ArgRel DeltaPar :=
  DeltaPar.congrRel.argRel fun hΓ h ha => (DeltaPar.full h).defeq hΓ ha

theorem EtaPar.argRel : ArgRel EtaPar :=
  EtaPar.congrRel.argRel fun hΓ h ha => (EtaPar.full hΓ h ha).defeq hΓ ha

theorem HasType.wrapLams_body (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ {ds : List VExpr} {body T}, Γ ⊢ VExpr.wrapLams ds body : T →
      OnCtx (ds.reverse ++ Γ) (env.IsType univs) ∧ ∃ B, (ds.reverse ++ Γ) ⊢ body : B
  | [], _, _, h => ⟨hΓ, _, h⟩
  | d :: ds, body, T, h => by
    have h' : Γ ⊢ .lam d (VExpr.wrapLams ds body) : T := h
    obtain ⟨⟨_, hd⟩, _, hb⟩ := h'.lam_inv henv hΓ
    have := HasType.wrapLams_body (Γ := d :: Γ) ⟨hΓ, _, hd⟩ hb
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using this

/-- A related right-hand side: related body, then a change of definitionally
equal binder domains. -/
theorem rhs_rel_join {R : List VExpr → VExpr → VExpr → Prop} (I : CongrRel R) (J : ArgRel R)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : ds.length = ds'.length)
    (ht : IsDefEqU env univs Γ (VExpr.wrapForalls ds res) (VExpr.wrapForalls ds' res'))
    (hb : R (ds.reverse ++ Γ) body body') (hrhs : Γ ⊢ VExpr.wrapLams ds body : T) :
    R Γ (VExpr.wrapLams ds body) (VExpr.wrapLams ds body') ∧
      NormalEq₀ Γ (VExpr.wrapLams ds body') (VExpr.wrapLams ds' body') := by
  obtain ⟨hctx, _, hB⟩ := HasType.wrapLams_body hΓ hrhs
  have hB' := (J.defeq hctx hb hB).hasType.2
  exact ⟨I.wrapLams hb, NormalEqF.wrapLams_congr hΓ hl ht (.refl hB')⟩

theorem PrefixUnfold.congr_red {R : List VExpr → VExpr → VExpr → Prop}
    (I : CongrRel R) (J : ArgRel R) (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (ha : List.Forall₂ (R Γ) args args') :
    ∃ rhs' X, PrefixUnfold env univs recursorData Γ name levels args' rhs' ∧
      R Γ rhs X ∧ NormalEq₀ Γ X rhs' := by
  obtain ⟨_, hd⟩ := H.defeq henv hΓ
  obtain ⟨rhs', hr, ds, ds', B, B', res, res', rfl, rfl, hl, ht, hb⟩ := H.congr_rel J hΓ ha
  obtain ⟨h1, h2⟩ := rhs_rel_join I J hΓ hl ht hb hd.hasType.2
  exact ⟨_, _, hr, h1, h2⟩

theorem QuotPrefixUnfold.congr_red {R : List VExpr → VExpr → VExpr → Prop}
    (I : CongrRel R) (J : ArgRel R) (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (ha : List.Forall₂ (R Γ) args args') :
    ∃ rhs' X, QuotPrefixUnfold env univs Γ levels args' rhs' ∧ R Γ rhs X ∧ NormalEq₀ Γ X rhs' := by
  obtain ⟨_, hd⟩ := H.defeq henv hΓ
  obtain ⟨rhs', hr, ds, ds', B, B', res, res', rfl, rfl, hl, ht, hb⟩ := H.congr_rel J hΓ ha
  obtain ⟨h1, h2⟩ := rhs_rel_join I J hΓ hl ht hb hd.hasType.2
  exact ⟨_, _, hr, h1, h2⟩

omit [Params] in
theorem CongrRel.apply_rhs {R : List VExpr → VExpr → VExpr → Prop} (I : CongrRel R)
    {p : Pattern} (r : p.RHS) {m m' : p.Path → VExpr} (H : ∀ a, R Γ (m a) (m' a)) :
    R Γ (r.apply ls m) (r.apply ls m') := by
  induction r with
  | fixed => exact I.rfl
  | app _ _ ih1 ih2 => exact I.app ih1 ih2
  | var a => exact H a

/-- A pattern check is a list of definitional equalities, so it transports
along definitionally equal values. -/
theorem _root_.Lean4Lean.Pattern.Check.OK.defeq_values (hΓ : OnCtx Γ (env.IsType univs))
    {p : Pattern} {ck : p.Check} {m m' : p.Path → VExpr}
    (hv : ∀ a, IsDefEqU env univs Γ (m a) (m' a))
    (H : ck.OK (IsDefEqU env univs Γ) ls m) : ck.OK (IsDefEqU env univs Γ) ls m' := by
  refine H.map fun a b h => ?_
  obtain ⟨_, h⟩ := h
  have ih : ∀ x A, Γ ⊢ m x : A → Γ ⊢ m x ≡ m' x := fun x _ _ => hv x
  have ha := IsDefEq.apply_pat hΓ (r := a) ih h.hasType.1
  have hb := IsDefEq.apply_pat hΓ (r := b) ih h.hasType.2
  exact ⟨_, ha.symm.trans (h.trans hb)⟩

end Relations


section DefRel

theorem IsDefEq.proj_congr (hΓ : OnCtx Γ (env.IsType univs))
    (he : Γ ⊢ .proj s i m : A) (hm : Γ ⊢ m ≡ m') : Γ ⊢ .proj s i m ≡ .proj s i m' : A := by
  obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
    hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
    hmajor, hclosed, hguard⟩ := he.proj_inv henv hΓ
  have majorEq := hm.of_l henv hΓ hmajor.hasType.2
  have projected := IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
    hmajor (hmajor.trans majorEq) hclosed hguard
  have ⟨_, typeToA⟩ := projected.hasType.1.uniq henv hΓ he
  exact .defeqDF typeToA projected

theorem IsDefEq.subst_args {e : VExpr} {σ σ' : VExpr.Subst} (hΓ : OnCtx Γ (env.IsType univs))
    (hs : ∀ i, σ i = σ' i ∨ IsDefEqU env univs Γ (σ i) (σ' i))
    (ht : Γ ⊢ e.subst σ : T) : Γ ⊢ e.subst σ ≡ e.subst σ' : T := by
  induction e generalizing Γ σ σ' T with
  | bvar i =>
    rcases hs i with he | he
    · rw [VExpr.subst, VExpr.subst, ← he]; exact ht
    · exact he.of_l henv hΓ ht
  | sort | const | elim => exact ht
  | app fn arg ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact IsDefEq.trans_l henv hΓ ht (.appDF (ihf hΓ hs hf) (iha hΓ hs ha))
  | proj family index major ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := ht.proj_inv henv hΓ
    exact IsDefEq.proj_congr hΓ ht ⟨_, ih hΓ hs hmajor.hasType.2⟩
  | lam domain body ihd ihb =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hctx : OnCtx (domain.subst σ :: Γ) (env.IsType univs) := ⟨hΓ, _, hd⟩
    refine IsDefEq.trans_l henv hΓ ht (.lamDF (ihd hΓ hs hd) (ihb hctx ?_ hb))
    intro i
    cases i with
    | zero => exact .inl (Eq.refl _)
    | succ i =>
      rcases hs i with he | he
      · exact .inl (congrArg VExpr.lift he)
      · exact .inr (he.weakN henv.ordered .one)
  | forallE domain body ihd ihb =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := ht.forallE_inv henv
    have hctx : OnCtx (domain.subst σ :: Γ) (env.IsType univs) := ⟨hΓ, _, hd⟩
    refine IsDefEq.trans_l henv hΓ ht (.forallEDF (ihd hΓ hs hd) (ihb hctx ?_ hb))
    intro i
    cases i with
    | zero => exact .inl (Eq.refl _)
    | succ i =>
      rcases hs i with he | he
      · exact .inl (congrArg VExpr.lift he)
      · exact .inr (he.weakN henv.ordered .one)

theorem IsDefEqU.mkApps_args (hΓ : OnCtx Γ (env.IsType univs)) (hf : Γ ⊢ f ≡ f')
    (hs : List.Forall₂ (IsDefEqU env univs Γ) as as') (ht : Γ ⊢ VExpr.mkApps f as : T) :
    Γ ⊢ VExpr.mkApps f as ≡ VExpr.mkApps f' as' := by
  induction hs generalizing f f' with
  | nil => exact hf
  | cons h _ ih =>
    obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app f _) ht
    obtain ⟨_, _, hft, hat⟩ := happ.app_inv henv hΓ
    exact ih ⟨_, .appDF (hf.of_l henv hΓ hft) (h.of_l henv hΓ hat)⟩ ht

/-- Definitional equality as an argument relation. -/
theorem defeqU_argRel : ArgRel (fun Γ a b => IsDefEqU env univs Γ a b) where
  refl _ h := ⟨_, h⟩
  weakN W h := h.weakN henv.ordered W
  defeq hΓ h ha := h.of_l henv hΓ ha
  mkApps hΓ hf hs ht := IsDefEqU.mkApps_args hΓ hf hs ht
  instantiateParams {Γ cs cs' e T} hΓ hs ht := by
    refine ⟨_, IsDefEq.subst_args hΓ ?_ ht⟩
    intro i
    have hlen := Lean4Lean.List.Forall₂.length_eq hs
    simp only [← hlen]
    split
    · rename_i hi
      exact .inr (List.forall₂_getElem hs _ (by omega) (by omega))
    · exact .inl (Eq.refl _)

theorem PrefixUnfold.congr_defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (ha : List.Forall₂ (IsDefEqU env univs Γ) args args') :
    ∃ rhs', PrefixUnfold env univs recursorData Γ name levels args' rhs' :=
  let ⟨rhs', h, _⟩ := H.congr_rel defeqU_argRel hΓ ha; ⟨rhs', h⟩

theorem QuotPrefixUnfold.congr_defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (ha : List.Forall₂ (IsDefEqU env univs Γ) args args') :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels args' rhs' :=
  let ⟨rhs', h, _⟩ := H.congr_rel defeqU_argRel hΓ ha; ⟨rhs', h⟩

end DefRel

section Disjoint

omit [Params] in
theorem eq_nil_or_snoc' (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact .inl h
  · exact .inr ⟨L, b, by simpa using h⟩



theorem PrefixUnfold.not_rigid
    (H : PrefixUnfold env univs recursorData Γ name ls args rhs) :
    ¬ env.Rigid name := by
  intro hrig
  cases H with
  | @intro data program hl hreg hname _ _ _ hg _ =>
    obtain ⟨_, _, _, _, hse, _, _⟩ := InductiveSignature.RecursorData.singletonUnfolding_spec hg
    have hinst := hreg.singletonEquation hse
    unfold InductiveSignature.RecursorData.singletonEquation at hse
    dsimp only at hse
    split at hse <;> try contradiction
    rename_i ctorIndex hfilter
    have hmem : ctorIndex ∈ (List.finRange data.schema.signature.constructors.size).filter
        (fun i => data.schema.signature.constructors[i].owner == data.owner) := by
      rw [hfilter]; exact List.mem_singleton_self _
    have howner : data.schema.signature.constructors[ctorIndex].owner = data.owner := by
      simpa using (List.mem_filter.mp hmem).2
    have hhead := hreg.equation_head howner (equation := program.equation) hse
    subst hname
    exact hrig _ hinst _ hhead

theorem QuotPrefixUnfold.not_rigid (H : QuotPrefixUnfold env univs Γ ls args rhs) :
    ¬ env.Rigid ``Quot.lift := by
  intro hrig
  cases H with
  | intro hr _ _ _ _ => exact hrig _ hr.equation _ rfl

omit [Params] in
theorem iota_matches_spine
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2) :
    ∃ vs M, e = .app (VExpr.mkApps (.const rc m1) vs) M ∧ vs.length = mr := by
  cases hm with
  | app hF hM =>
    exact ⟨_, _, by rw [hF.const_arguments], by simp [Pattern.argumentRHS_length]⟩

theorem Params.no_match_delta_prefix (hdata : recursorData name = some data) (hp : Pat p r)
    (hlen : pre.length ≤ data.majorOffset)
    (hm : p.Matches (VExpr.mkApps (.const name ls) pre) lv vals) : False := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hp
  cases sp with
  | defn c =>
    generalize he : VExpr.mkApps (.const name ls) pre = E at hm
    cases hm
    obtain ⟨rfl, -, -⟩ := VExpr.mkApps_const_inj (as' := []) he
    rw [(pat_const_not_unfolding hp).1] at hdata
    cases hdata
  | iota rc mr cc kc =>
    obtain ⟨vs, M, he, hvs⟩ := iota_matches_spine hm
    rw [← VExpr.mkApps_snoc] at he
    obtain ⟨rfl, -, rfl⟩ := VExpr.mkApps_const_inj he
    rcases pat_recursor hp with ⟨data', _, _, hmo, hrd, _⟩ | ⟨hqr, hq, _⟩
    · rw [hrd] at hdata
      cases hdata
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    · subst hq
      rw [recursorData_quot hqr] at hdata
      cases hdata

theorem Params.no_match_quot_prefix (hqr : QuotRegistered env) (hp : Pat p r)
    (hlen : pre.length ≤ 5)
    (hm : p.Matches (VExpr.mkApps (.const ``Quot.lift ls) pre) lv vals) : False := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hp
  cases sp with
  | defn c =>
    generalize he : VExpr.mkApps (.const ``Quot.lift ls) pre = E at hm
    cases hm
    obtain ⟨rfl, -, -⟩ := VExpr.mkApps_const_inj (as' := []) he
    exact (pat_const_not_unfolding hp).2 hqr rfl
  | iota rc mr cc kc =>
    obtain ⟨vs, M, he, hvs⟩ := iota_matches_spine hm
    rw [← VExpr.mkApps_snoc] at he
    obtain ⟨rfl, -, rfl⟩ := VExpr.mkApps_const_inj he
    rcases pat_recursor hp with ⟨data', _, _, _, hrd, _⟩ | ⟨_, _, hmr, _⟩
    · rw [recursorData_quot hqr] at hrd
      cases hrd
    · simp only [List.length_append, List.length_singleton] at hlen
      omega

/-- The large-elimination guard of recursor iota excludes prefix unfolding. -/
theorem Params.iota_no_delta
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hck : r.2.OK df m1 m2)
    (H : PrefixUnfold env univs recursorData Γ rc m1 pre rhs) : False := by
  cases H with
  | @intro data program hl _ hname hlarge _ hz _ _ =>
    rcases pat_recursor (recursor := rc) (major := mr) (ctor := cc) (fields := kc) hp with
      ⟨data', _, _, _, hrd, _, hguard⟩ | ⟨_, hq, _⟩
    · rw [hrd] at hl
      cases hl
      obtain ⟨rest, hr⟩ := hguard hlarge
      rw [hr] at hck
      exact hck.1 hz
    · subst hq
      rw [recursorData_quot (by assumption)] at hl
      cases hl

/-- The nonzero guard of quotient iota excludes quotient prefix unfolding. -/
theorem Params.iota_no_quotDelta
    (hp : Pat (.app ((Pattern.const ``Quot.lift).varN mr) ((Pattern.const cc).varN kc)) r)
    (hck : r.2.OK df m1 m2)
    (H : QuotPrefixUnfold env univs Γ m1 pre rhs) : False := by
  cases H with
  | intro _ _ hz _ _ =>
    rcases pat_recursor (recursor := ``Quot.lift) (major := mr) (ctor := cc) (fields := kc) hp with
      ⟨data', _, _, _, hrd, _, _⟩ | ⟨_, _, _, _, _, rest, hr⟩
    · rw [recursorData_quot (by assumption)] at hrd
      cases hrd
    · rw [hr] at hck
      apply hck.1
      simpa [VLevel.inst, List.getD_eq_getElem?_getD] using hz


theorem ParRed.const_spine_of (n : Nat)
    (hno : ∀ {p r pre lv vals}, Pat p r → pre.length ≤ n →
      p.Matches (VExpr.mkApps (.const name levels) pre) lv vals → False)
    (hlen : args.length ≤ n) (H : ParRed Γ (VExpr.mkApps (.const name levels) args) out) :
    ∃ args', out = VExpr.mkApps (.const name levels) args' ∧ List.Forall₂ (ParRed Γ) args args' := by
  induction args using List.snoc_induction generalizing out with
  | nil =>
    generalize he : VExpr.mkApps (.const name levels) [] = src at H
    cases H with
    | const => cases he; exact ⟨[], rfl, .nil⟩
    | extra hp hm => subst he; exact (hno hp (by simp) hm).elim
    | schema hm =>
      have := congrArg (fun e => (VExpr.getAppFnArgs e).1) he
      simp only [InductiveSignature.spine_mkApps_exact (VExpr.const name levels) [] rfl,
        InductiveSignature.CaseSchema.Application.head] at this
      cases this
    | _ => cases he
  | snoc args arg ih =>
    generalize he : VExpr.mkApps (.const name levels) (args ++ [arg]) = src at H
    have hshape : src = .app (VExpr.mkApps (.const name levels) args) arg := by
      rw [← he, VExpr.mkApps_snoc]
    have hhead : src.getAppFnArgs.1 = .const name levels := by
      rw [← he, InductiveSignature.spine_mkApps_exact _ _ rfl]
    cases H with
    | schema hm =>
      rw [InductiveSignature.CaseSchema.Application.head] at hhead
      cases hhead
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih (by simp at hlen; omega) hf
      exact ⟨args' ++ [arg'], (VExpr.mkApps_snoc ..).symm, List.Forall₂.append' hargs (.cons ha .nil)⟩
    | beta =>
      have hfn := VExpr.app.inj hshape |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
    | extra hp hm => subst he; exact (hno hp hlen hm).elim
    | _ => cases hshape

theorem DeltaPar.const_spine_of (n : Nat)
    (hno : ∀ {pre rhs}, pre.length ≤ n →
      ¬ PrefixUnfold env univs recursorData Γ name levels pre rhs)
    (hnoq : ∀ {pre rhs}, pre.length ≤ n → name = ``Quot.lift →
      ¬ QuotPrefixUnfold env univs Γ levels pre rhs)
    (hlen : args.length ≤ n) (H : DeltaPar Γ (VExpr.mkApps (.const name levels) args) out) :
    ∃ args', out = VExpr.mkApps (.const name levels) args' ∧
      List.Forall₂ (DeltaPar Γ) args args' := by
  induction args using List.snoc_induction generalizing out with
  | nil =>
    generalize he : VExpr.mkApps (.const name levels) [] = src at H
    cases H with
    | const => cases he; exact ⟨[], rfl, .nil⟩
    | delta hl _ hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      exact (hno (by simp at hl ⊢; omega) hr).elim
    | quotDelta hl _ hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      exact (hnoq (by simp at hl ⊢; omega) rfl hr).elim
    | _ => cases he
  | snoc args arg ih =>
    generalize he : VExpr.mkApps (.const name levels) (args ++ [arg]) = src at H
    have hshape : src = .app (VExpr.mkApps (.const name levels) args) arg := by
      rw [← he, VExpr.mkApps_snoc]
    cases H with
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih (by simp at hlen; omega) hf
      exact ⟨args' ++ [arg'], (VExpr.mkApps_snoc ..).symm, List.Forall₂.append' hargs (.cons ha .nil)⟩
    | delta hl _ hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      exact (hno (by omega) hr).elim
    | quotDelta hl _ hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      exact (hnoq (by omega) rfl hr).elim
    | projIota => cases hshape
    | _ => cases hshape

theorem DeltaPar.elim_spine (H : DeltaPar Γ (VExpr.mkApps (.elim block owner levels) args) out) :
    ∃ args', out = VExpr.mkApps (.elim block owner levels) args' ∧
      List.Forall₂ (DeltaPar Γ) args args' := by
  induction args using List.snoc_induction generalizing out with
  | nil =>
    generalize he : VExpr.mkApps (.elim block owner levels) [] = src at H
    cases H with
    | elim => cases he; exact ⟨[], rfl, .nil⟩
    | delta =>
      have := congrArg VExpr.getAppFnArgs he
      rw [InductiveSignature.spine_mkApps_exact _ _ rfl,
        InductiveSignature.spine_mkApps_exact _ _ rfl] at this
      cases this
    | quotDelta =>
      have := congrArg VExpr.getAppFnArgs he
      rw [InductiveSignature.spine_mkApps_exact _ _ rfl,
        InductiveSignature.spine_mkApps_exact _ _ rfl] at this
      cases this
    | _ => cases he
  | snoc args arg ih =>
    generalize he : VExpr.mkApps (.elim block owner levels) (args ++ [arg]) = src at H
    have hshape : src = .app (VExpr.mkApps (.elim block owner levels) args) arg := by
      rw [← he, VExpr.mkApps_snoc]
    cases H with
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih hf
      exact ⟨args' ++ [arg'], (VExpr.mkApps_snoc ..).symm, List.Forall₂.append' hargs (.cons ha .nil)⟩
    | delta =>
      have := congrArg VExpr.getAppFnArgs he
      rw [InductiveSignature.spine_mkApps_exact _ _ rfl,
        InductiveSignature.spine_mkApps_exact _ _ rfl] at this
      cases this
    | quotDelta =>
      have := congrArg VExpr.getAppFnArgs he
      rw [InductiveSignature.spine_mkApps_exact _ _ rfl,
        InductiveSignature.spine_mkApps_exact _ _ rfl] at this
      cases this
    | projIota => cases hshape
    | _ => cases hshape

theorem DeltaPar.rigid_spine (hrig : env.Rigid name)
    (H : DeltaPar Γ (VExpr.mkApps (.const name levels) args) out) :
    ∃ args', out = VExpr.mkApps (.const name levels) args' ∧
      List.Forall₂ (DeltaPar Γ) args args' :=
  DeltaPar.const_spine_of args.length (fun _ hr => hr.not_rigid hrig)
    (fun _ h hr => by subst h; exact hr.not_rigid hrig) (Nat.le_refl _) H

end Disjoint

section EtaMirror

theorem NormalEqF.structExpand_congr (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ e₁ e₂) (hps : List.Forall₂ (NormalEqF η Γ) ps₁ ps₂)
    (ht : Γ ⊢ structExpand family info levels ps₁ e₁ : T) :
    NormalEqF η Γ (structExpand family info levels ps₁ e₁)
      (structExpand family info levels ps₂ e₂) := by
  unfold VEnv.structExpand at ht ⊢
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  have hfields : List.Forall₂ (NormalEqF η Γ)
      ((List.range info.numFields).map fun index => .proj family index e₁)
      ((List.range info.numFields).map fun index => .proj family index e₂) := by
    apply List.forall₂_of_getElem (by simp)
    intro i hi hi'
    have himem : i ∈ List.range info.numFields := by simpa using hi
    obtain ⟨_, h⟩ := schema_mkApps_arg_type hΓ ht
      (List.mem_append_right _ (List.mem_map.mpr ⟨i, himem, rfl⟩))
    simpa only [List.getElem_map, List.getElem_range] using NormalEqF.projDF h H
  exact NormalEqF.mkApps_spine hΓ (.refl hhead) (List.Forall₂.append' hps hfields) ht

theorem structExpand_params_typed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ structExpand family info levels ps e : T) : ∀ p ∈ ps, ∃ A, Γ ⊢ p : A :=
  fun _ hp => schema_mkApps_arg_type hΓ ht (List.mem_append_left _ hp)

/-- Typing transports along a normally equal expanded term. -/
theorem structExpand_typed_of_normal (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ e₁ e₂) (ht : Γ ⊢ structExpand family info levels ps e₂ : T) :
    Γ ⊢ structExpand family info levels ps e₁ : T :=
  ht.defeqU_l henv hΓ (NormalEqF.defeq hΓ (NormalEqF.structExpand_congr hΓ (H.symm hΓ)
    (NormalEqF.forall₂_refl (structExpand_params_typed hΓ ht)) ht))

/-- The normal equality of two eta bodies at the same domain. -/
theorem NormalEqF.etaBody
    (H : NormalEqF η Γ e₁ e₂) (h1 : Γ ⊢ e₁ : .forallE D B) (h2 : Γ ⊢ e₂ : .forallE D B)
    (hD : Γ ⊢ D ≡ D₁ : .sort u) (hD' : Γ ⊢ D ≡ D₂ : .sort u) :
    NormalEqF η Γ (.lam D₁ (.app e₁.lift (.bvar 0))) (.lam D₂ (.app e₂.lift (.bvar 0))) :=
  NormalEqF.lamDF hD hD' (NormalEqF.appDF (h1.weak henv) (h2.weak henv) (.bvar .zero)
    (.bvar .zero) (H.weakN .one) (.refl (.bvar .zero)))

theorem EtaPar.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', EtaPar Γ c c' ∧ NormalEq₀ Γ c' b := by
  induction H generalizing c A with
  | bvar | sort | const | elim => exact ⟨c, .rfl, hc⟩
  | @app _ f f' x x' h1 h2 ih1 ih2 =>
    have hb := (EtaPar.full hΓ (.app h1 h2) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.app f x = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .app h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.app h1 h2) l3).hasType hΓ l3)⟩
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      obtain ⟨F, hF, eF⟩ := ih1 hΓ ⟨_, l5⟩ l2
      obtain ⟨X, hX, eX⟩ := ih2 hΓ ⟨_, l6⟩ l4
      exact ⟨_, .app hF hX, .appDF ((EtaPar.full hΓ hF l1).hasType hΓ l1)
        ((EtaPar.full hΓ h1 l2).hasType hΓ l2) ((EtaPar.full hΓ hX l3).hasType hΓ l3)
        ((EtaPar.full hΓ h2 l4).hasType hΓ l4) eF eX⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF => cases hR
  | @proj _ m m' family index h1 ih =>
    have hb := (EtaPar.full hΓ (.proj h1) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.proj family index m = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .proj h1, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.proj h1) l3).hasType hΓ l3)⟩
    | projDF l1 l2 =>
      cases hR
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, hM, eM⟩ := ih hΓ ⟨_, l2⟩ hm.hasType.2
      exact ⟨_, .proj hM, .projDF ((EtaPar.full hΓ (.proj hM) l1).hasType hΓ l1) eM⟩
    | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR
  | @lam _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (EtaPar.full hΓ (.lam h1 h2) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.lam D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .lam h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.lam h1 h2) l3).hasType hΓ l3)⟩
    | lamDF l1 l2 l3 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have l3' := l3.defeqDFC hΓ (.succ .zero l2)
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l3'⟩ ht
      have hDD₁ := l2.symm.trans l1
      have ht₁ := ((NormalEqN.defeq hΓ' l3').of_r henv hΓ' ht).hasType.1
      refine ⟨_, .lam .rfl (hT.defeqDFC hΓ (.succ .zero hDD₁) ht₁), ?_⟩
      have hD2 := l2.hasType.2
      have hDD' := (EtaPar.full hΓ h1 hD2).defeq hΓ hD2
      exact .lamDF hDD₁ hDD' eT
    | sortDF | constDF | elimDF | appDF | projDF | forallEDF => cases hR
  | @forallE _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (EtaPar.full hΓ (.forallE h1 h2) ha).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.forallE D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .forallE h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((EtaPar.full hΓ (.forallE h1 h2) l3).hasType hΓ l3)⟩
    | forallEDF l1 l2 l3 l4 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.forallE_inv henv
      obtain ⟨D₁', hD₁, eD⟩ := ih1 hΓ ⟨_, l2⟩ hD
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have W' := l1.transU_l henv hΓ (NormalEqN.defeq hΓ l2)
      have l4' := l4.defeqDFC hΓ (.succ .zero W')
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l4'⟩ ht
      have l3'' := l3.defeqDFC henv (.succ .zero W')
      have hA₁ := l1.hasType.2
      have hD₁T := (EtaPar.full hΓ hD₁ hA₁).defeq hΓ hA₁
      refine ⟨_, .forallE hD₁ (hT.defeqDFC hΓ (.succ .zero (W'.symm.trans l1)) l3''), ?_⟩
      have hT1 := (EtaPar.full hΓ' hT l3'').hasType hΓ' l3''
      exact .forallEDF (W'.symm.trans (l1.trans hD₁T)) eD hT1 eT
    | sortDF | constDF | elimDF | appDF | projDF | lamDF => cases hR
  | funEta H1 HA ht ih ihA =>
    obtain ⟨c₀, hc₀, ec₀⟩ := ih hΓ hc ht
    have hcT := ht.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
    refine ⟨_, .funEta hc₀ HA hcT, ?_⟩
    have ⟨⟨_, hD⟩, _⟩ := let ⟨_, h⟩ := ht.isType henv hΓ; h.forallE_inv henv
    have hDD := (EtaPar.full hΓ HA hD).defeq hΓ hD
    exact NormalEqF.etaBody ec₀ ((EtaPar.full hΓ hc₀ hcT).hasType hΓ hcT)
      ((EtaPar.full hΓ H1 ht).hasType hΓ ht) hDD hDD
  | structEta H1 hlen hps hl hp hi hs hexp ih ihp =>
    obtain ⟨c₀, hc₀, ec₀⟩ := ih hΓ hc hs
    have hcS := hs.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
    have hcexp := structExpand_typed_of_normal hΓ hc hexp
    have hstep := EtaPar.structEta hc₀ hlen hps hl hp hi hcS hcexp
    refine ⟨_, hstep, ?_⟩
    have ht' := (EtaPar.full hΓ hstep hcS).hasType hΓ hcS
    exact NormalEqF.structExpand_congr hΓ ec₀
      (NormalEqF.forall₂_refl (structExpand_params_typed hΓ ht')) ht'

end EtaMirror


section DeltaMirror

omit [Params] in
theorem List.Forall₂.exists_mid {R S U V : α → α → Prop} :
    ∀ {l₁ l l'}, List.Forall₂ R l₁ l → List.Forall₂ S l l' →
      (∀ x y z, y ∈ l → R x y → S y z → ∃ w, U x w ∧ V w z) →
      ∃ ws, List.Forall₂ U l₁ ws ∧ List.Forall₂ V ws l'
  | [], [], [], .nil, .nil, _ => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2, H => by
    obtain ⟨w, hu, hv⟩ := H _ _ _ (List.mem_cons_self ..) h1 h2
    obtain ⟨ws, hus, hvs⟩ := List.Forall₂.exists_mid t1 t2
      fun x y z hy => H x y z (List.mem_cons_of_mem _ hy)
    exact ⟨w :: ws, .cons hu hus, .cons hv hvs⟩

/-- Spine exposure without eta. A term normally equal to a rigid-headed spine
is a proof or literally a spine with an equivalent head. -/
theorem NormalEq₀.spine_expose (hΓ : OnCtx Γ (env.IsType univs)) (hh : RigidHead h)
    (H : NormalEq₀ Γ x (VExpr.mkApps h targs)) (hx : Γ ⊢ x : T) :
    (Γ ⊢ T : .sort .zero) ∨
    ∃ h' targs', HeadEquiv h' h ∧ x = VExpr.mkApps h' targs' ∧
      List.Forall₂ (NormalEq₀ Γ) targs' targs := by
  induction targs using List.snoc_induction generalizing x T with
  | nil =>
    obtain ⟨n, H⟩ := H
    cases hh with
    | const =>
      generalize hR : VExpr.mkApps (.const _ _) [] = R at H
      cases H with
      | refl _ => subst hR; exact .inr ⟨_, [], RigidHead.const.equiv_rfl, rfl, .nil⟩
      | constDF _ _ _ _ h5 => cases hR; exact .inr ⟨_, [], .const h5, rfl, .nil⟩
      | proofIrrel l1 l2 _ => exact .inl (l1.defeqU_l henv hΓ (l2.uniqU henv hΓ hx))
      | _ => cases hR
    | elim =>
      generalize hR : VExpr.mkApps (.elim _ _ _) [] = R at H
      cases H with
      | refl _ => subst hR; exact .inr ⟨_, [], RigidHead.elim.equiv_rfl, rfl, .nil⟩
      | elimDF _ h2 => cases hR; exact .inr ⟨_, [], .elim h2, rfl, .nil⟩
      | proofIrrel l1 l2 _ => exact .inl (l1.defeqU_l henv hΓ (l2.uniqU henv hΓ hx))
      | _ => cases hR
  | snoc targs t ih =>
    obtain ⟨n, H⟩ := H
    rw [VExpr.mkApps_snoc] at H
    generalize hR : VExpr.app (VExpr.mkApps h targs) t = R at H
    cases H with
    | refl _ =>
      subst hR
      have hx' : Γ ⊢ VExpr.mkApps h (targs ++ [t]) : T := by rwa [VExpr.mkApps_snoc]
      exact .inr ⟨h, targs ++ [t], hh.equiv_rfl, (VExpr.mkApps_snoc ..).symm,
        NormalEqF.forall₂_refl fun _ hm => schema_mkApps_arg_type hΓ hx' hm⟩
    | proofIrrel l1 l2 _ => exact .inl (l1.defeqU_l henv hΓ (l2.uniqU henv hΓ hx))
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      rcases ih ⟨_, l5⟩ l1 with hp | ⟨h', targs', he, rfl, hargs⟩
      · exact .inl (HasType.mkApps_proof hΓ hp l1 (bs := [_]) hx)
      · exact .inr ⟨h', targs' ++ [_], he, (VExpr.mkApps_snoc ..).symm,
          List.Forall₂.append' hargs (.cons ⟨_, l6⟩ .nil)⟩
    | _ => cases hR

theorem PrefixUnfold.congr₀ (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (hw : ∀ level ∈ levels', level.WF univs) (hls : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (NormalEq₀ Γ) args args') :
    ∃ rhs', PrefixUnfold env univs recursorData Γ name levels' args' rhs' ∧
      NormalEq₀ Γ rhs rhs' := by
  obtain ⟨rhs₁, h1, e1⟩ := H.congr_normal hΓ ha
  obtain ⟨rhs₂, h2, e2⟩ := h1.congr_levels henv hΓ hw hls
    (eqUpToLevels_forall₂_rfl hΓ (NormalEqF.forall₂_typed_right hΓ ha))
  obtain ⟨_, hd⟩ := h1.defeq henv hΓ
  exact ⟨rhs₂, h2, e1.trans hΓ (NormalEqF.of_levelEquiv hΓ (.of_eqUpToLevels e2) hd.hasType.2)⟩

theorem QuotPrefixUnfold.congr₀ (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (hw : ∀ level ∈ levels', level.WF univs) (hls : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (NormalEq₀ Γ) args args') :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels' args' rhs' ∧ NormalEq₀ Γ rhs rhs' := by
  obtain ⟨rhs₁, h1, e1⟩ := H.congr_normal hΓ ha
  obtain ⟨rhs₂, h2, e2⟩ := h1.congr_levels henv hΓ hw hls
    (eqUpToLevels_forall₂_rfl hΓ (NormalEqF.forall₂_typed_right hΓ ha))
  obtain ⟨_, hd⟩ := h1.defeq henv hΓ
  exact ⟨rhs₂, h2, e1.trans hΓ (NormalEqF.of_levelEquiv hΓ (.of_eqUpToLevels e2) hd.hasType.2)⟩


theorem DeltaPar.mkApps (hf : DeltaPar Γ f f') (H : List.Forall₂ (DeltaPar Γ) args args') :
    DeltaPar Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') := by
  induction H generalizing f f' with
  | nil => exact hf
  | cons h _ ih => exact ih (.app hf h)

theorem DeltaPar.mkApps_args (H : List.Forall₂ (DeltaPar Γ) args args') :
    DeltaPar Γ (VExpr.mkApps f args) (VExpr.mkApps f args') := DeltaPar.mkApps .rfl H

omit [Params] in
theorem forall₂_getElem?_right {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {i : Nat} {y : β}, List.Forall₂ R l l' → l'[i]? = some y →
      ∃ x, l[i]? = some x ∧ R x y
  | _ :: _, _ :: _, 0, _, .cons h _, hy => by cases hy; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ t, hy => by
    simp only [List.getElem?_cons_succ] at hy ⊢; exact forall₂_getElem?_right t hy
  | [], [], _, _, .nil, hy => by cases hy

/-- Pointwise mirrors of developed arguments. -/
theorem DeltaPar.mirror_args (hΓ : OnCtx Γ (env.IsType univs))
    (ha : Γ ⊢ VExpr.mkApps f args : A) (hlen : args.length = args'.length)
    (ih : ∀ i (hi : i < args.length) (hi' : i < args'.length) {c A}, OnCtx Γ (env.IsType univs) →
      NormalEq₀ Γ c args[i] → Γ ⊢ args[i] : A → ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' args'[i])
    (hrel : List.Forall₂ (NormalEq₀ Γ) args₁ args) :
    ∃ Xs, List.Forall₂ (DeltaPar Γ) args₁ Xs ∧ List.Forall₂ (NormalEq₀ Γ) Xs args' := by
  have hS : List.Forall₂ (fun y z => ∀ {c A}, NormalEq₀ Γ c y → Γ ⊢ y : A →
      ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' z) args args' :=
    List.forall₂_of_getElem hlen fun i hi hi' _ _ h1 h2 => ih i hi hi' hΓ h1 h2
  exact List.Forall₂.exists_mid hrel hS fun x y z hy h1 h2 =>
    h2 h1 (schema_mkApps_arg_type hΓ ha hy).choose_spec


/-- The induction hypothesis of a mirror for developed arguments. -/
abbrev MirrorArgs (Γ : List VExpr) (args args' : List VExpr) : Prop :=
  ∀ i (hi : i < args.length) (hi' : i < args'.length) {c A}, OnCtx Γ (env.IsType univs) →
    NormalEq₀ Γ c args[i] → Γ ⊢ args[i] : A → ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' args'[i]

theorem DeltaPar.mirror_delta (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hr : PrefixUnfold env univs recursorData Γ name ls args' rhs)
    (ih : MirrorArgs Γ args args')
    (hc : NormalEq₀ Γ c (VExpr.mkApps (.const name ls) args))
    (ha : Γ ⊢ VExpr.mkApps (.const name ls) args : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' rhs := by
  have hb := (DeltaPar.full (.delta hlen hargs hr)).hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  rcases NormalEq₀.spine_expose hΓ .const hc hcT with hp | ⟨h', args₁, he, rfl, hrel⟩
  · exact ⟨c, .rfl, .proofIrrel hp hcT hb⟩
  obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const name ls₁ ∧ List.Forall₂ (· ≈ ·) ls₁ ls := by
    cases he with | const h => exact ⟨_, rfl, h⟩
  obtain ⟨Xs, hXs, eXs⟩ := DeltaPar.mirror_args hΓ ha hlen ih hrel
  obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ hcT
  obtain ⟨_, _, hw₁, _⟩ := hh₁.const_inv henv hΓ
  obtain ⟨rhs', hr', e'⟩ := hr.congr₀ hΓ hw₁
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => NormalEqF.symm hΓ h) (Lean4Lean.List.Forall₂.flip eXs))
  have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
  exact ⟨rhs', .delta hl' hx' hr', e'.symm hΓ⟩

theorem DeltaPar.mirror_quotDelta (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hr : QuotPrefixUnfold env univs Γ ls args' rhs)
    (ih : MirrorArgs Γ args args')
    (hc : NormalEq₀ Γ c (VExpr.mkApps (.const ``Quot.lift ls) args))
    (ha : Γ ⊢ VExpr.mkApps (.const ``Quot.lift ls) args : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' rhs := by
  have hb := (DeltaPar.full (.quotDelta hlen hargs hr)).hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  rcases NormalEq₀.spine_expose hΓ .const hc hcT with hp | ⟨h', args₁, he, rfl, hrel⟩
  · exact ⟨c, .rfl, .proofIrrel hp hcT hb⟩
  obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const ``Quot.lift ls₁ ∧
      List.Forall₂ (· ≈ ·) ls₁ ls := by
    cases he with | const h => exact ⟨_, rfl, h⟩
  obtain ⟨Xs, hXs, eXs⟩ := DeltaPar.mirror_args hΓ ha hlen ih hrel
  obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ hcT
  obtain ⟨_, _, hw₁, _⟩ := hh₁.const_inv henv hΓ
  obtain ⟨rhs', hr', e'⟩ := hr.congr₀ hΓ hw₁
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => NormalEqF.symm hΓ h) (Lean4Lean.List.Forall₂.flip eXs))
  have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
  exact ⟨rhs', .quotDelta hl' hx' hr', e'.symm hΓ⟩

theorem DeltaPar.mirror_projIota (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args') : fieldType)
    (hi : args'[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (ih : MirrorArgs Γ args args')
    (hc : NormalEq₀ Γ c (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)))
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' field := by
  have hstep := DeltaPar.projIota hlen hargs hl hs hi ht
  have hb := (DeltaPar.full hstep).hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  obtain ⟨n, hc'⟩ := hc
  generalize hR : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = R at hc'
  cases hc' with
  | refl _ => subst hR; exact ⟨_, hstep, .refl hb⟩
  | proofIrrel l1 l2 l3 =>
    subst hR; exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full hstep).hasType hΓ l3)⟩
  | projDF l1 l2 =>
    cases hR
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm₁, _, _⟩ := hcT.proj_inv henv hΓ
    rcases NormalEq₀.spine_expose hΓ .const ⟨_, l2⟩ hm₁.hasType.2 with
      hp | ⟨h', args₁, he, hM, hrel⟩
    · have hA := HasType.proj_result_prop_of_major_proof henv hΓ hcT hp hm₁.hasType.2
      exact ⟨_, .rfl, .proofIrrel hA hcT hb⟩
    subst hM
    obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const info.ctorName ls₁ ∧
        List.Forall₂ (· ≈ ·) ls₁ ls := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    obtain ⟨Xs, hXs, eXs⟩ := DeltaPar.mirror_args hΓ hm.hasType.2 hlen ih hrel
    obtain ⟨X, hX, eX⟩ := forall₂_getElem?_right eXs hi
    have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
    have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls₁) args₁))
        (.proj family index (VExpr.mkApps (.const info.ctorName ls₁) Xs)) :=
      .proj (DeltaPar.mkApps_args hXs)
    have hT := (DeltaPar.full hcong).hasType hΓ hcT
    have hXT := hb.defeqU_l henv hΓ (NormalEqF.defeq hΓ eX).symm
    exact ⟨X, .projIota hl' hx' hl hT hX hXT, eX⟩
  | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR

theorem DeltaPar.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' b := by
  induction H generalizing c A with
  | bvar | sort | const | elim => exact ⟨c, .rfl, hc⟩
  | @app _ f f' x x' h1 h2 ih1 ih2 =>
    have hb := (DeltaPar.full (.app h1 h2)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.app f x = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .app h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.app h1 h2)).hasType hΓ l3)⟩
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      obtain ⟨F, hF, eF⟩ := ih1 hΓ ⟨_, l5⟩ l2
      obtain ⟨X, hX, eX⟩ := ih2 hΓ ⟨_, l6⟩ l4
      exact ⟨_, .app hF hX, .appDF ((DeltaPar.full hF).hasType hΓ l1)
        ((DeltaPar.full h1).hasType hΓ l2) ((DeltaPar.full hX).hasType hΓ l3)
        ((DeltaPar.full h2).hasType hΓ l4) eF eX⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF => cases hR
  | @proj _ m m' family index h1 ih =>
    have hb := (DeltaPar.full (.proj h1)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.proj family index m = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .proj h1, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.proj h1)).hasType hΓ l3)⟩
    | projDF l1 l2 =>
      cases hR
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, hM, eM⟩ := ih hΓ ⟨_, l2⟩ hm.hasType.2
      exact ⟨_, .proj hM, .projDF ((DeltaPar.full (.proj hM)).hasType hΓ l1) eM⟩
    | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR
  | @lam _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (DeltaPar.full (.lam h1 h2)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.lam D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .lam h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.lam h1 h2)).hasType hΓ l3)⟩
    | lamDF l1 l2 l3 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have l3' := l3.defeqDFC hΓ (.succ .zero l2)
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l3'⟩ ht
      have hDD₁ := l2.symm.trans l1
      have ht₁ := ((NormalEqN.defeq hΓ' l3').of_r henv hΓ' ht).hasType.1
      refine ⟨_, .lam .rfl (hT.defeqDFC hΓ (.succ .zero hDD₁) ht₁), ?_⟩
      have hD2 := l2.hasType.2
      have hDD' := (DeltaPar.full h1).defeq hΓ hD2
      exact .lamDF hDD₁ hDD' eT
    | sortDF | constDF | elimDF | appDF | projDF | forallEDF => cases hR
  | @forallE _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (DeltaPar.full (.forallE h1 h2)).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.forallE D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .forallE h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((DeltaPar.full (.forallE h1 h2)).hasType hΓ l3)⟩
    | forallEDF l1 l2 l3 l4 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.forallE_inv henv
      obtain ⟨D₁', hD₁, eD⟩ := ih1 hΓ ⟨_, l2⟩ hD
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have W' := l1.transU_l henv hΓ (NormalEqN.defeq hΓ l2)
      have l4' := l4.defeqDFC hΓ (.succ .zero W')
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l4'⟩ ht
      have l3'' := l3.defeqDFC henv (.succ .zero W')
      have hA₁ := l1.hasType.2
      have hD₁T := (DeltaPar.full hD₁).defeq hΓ hA₁
      refine ⟨_, .forallE hD₁ (hT.defeqDFC hΓ (.succ .zero (W'.symm.trans l1)) l3''), ?_⟩
      have hT1 := (DeltaPar.full hT).hasType hΓ' l3''
      exact .forallEDF (W'.symm.trans (l1.trans hD₁T)) eD hT1 eT
    | sortDF | constDF | elimDF | appDF | projDF | lamDF => cases hR
  | delta hlen hargs hr ih => exact DeltaPar.mirror_delta hΓ hlen hargs hr ih hc ha
  | quotDelta hlen hargs hr ih => exact DeltaPar.mirror_quotDelta hΓ hlen hargs hr ih hc ha
  | projIota hlen hargs hl hs hi ht ih =>
    exact DeltaPar.mirror_projIota hΓ hlen hargs hl hs hi ht ih hc ha

end DeltaMirror

section ParRedMirror

/-- The mirror property of one parallel step, used as an induction hypothesis. -/
abbrev MirrorP (Γ : List VExpr) (x y : VExpr) : Prop :=
  ∀ {c A}, OnCtx Γ (env.IsType univs) → NormalEq₀ Γ c x → Γ ⊢ x : A →
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' y

theorem ParRed.mirror_beta (hΓ : OnCtx Γ (env.IsType univs))
    (h1 : ParRed (D :: Γ) t t') (h2 : ParRed Γ u u')
    (ih1 : MirrorP (D :: Γ) t t') (ih2 : MirrorP Γ u u')
    (hc : NormalEq₀ Γ c (.app (.lam D t) u)) (ha : Γ ⊢ .app (.lam D t) u : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' (t'.inst u') := by
  have hstep : ParRed Γ (.app (.lam D t) u) (t'.inst u') := .beta h1 h2
  have hb := hstep.hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  obtain ⟨n, hc'⟩ := hc
  generalize hR : VExpr.app (.lam D t) u = R at hc'
  cases hc' with
  | refl _ => subst hR; exact ⟨_, hstep, .refl hb⟩
  | proofIrrel l1 l2 l3 => subst hR; exact ⟨c, .rfl, .proofIrrel l1 l2 (hstep.hasType hΓ l3)⟩
  | @appDF _ f₁ _ _ _ u₁ _ _ _ _ l1 l2 l3 l4 l5 l6 =>
    cases hR
    let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
    let ⟨⟨_, u1⟩, _⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
    have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, d1⟩
    obtain ⟨U₁, hU, eU⟩ := ih2 hΓ ⟨_, l6⟩ l4
    have hU₁D := hU.hasType hΓ (u1.symm.defeq l3)
    have ht' := h1.hasType hΓ' d2
    have hinst : ∀ {T}, NormalEq₀ (D :: Γ) T t' → NormalEq₀ Γ (T.inst U₁) (t'.inst u') :=
      fun eT => (NormalEqF.instN hU₁D .zero eT).trans hΓ (NormalEqF.instN_r hΓ' hU₁D eU .zero ht')
    generalize hL : VExpr.lam D t = L at l5
    cases l5 with
    | refl _ =>
      subst hL
      obtain ⟨T, hT, eT⟩ := ih1 hΓ' (.refl d2) d2
      exact ⟨_, .beta hT hU, hinst eT⟩
    | lamDF k1 k2 k3 =>
      cases hL
      have k3' := k3.defeqDFC hΓ (.succ .zero k2)
      obtain ⟨T, hT, eT⟩ := ih1 hΓ' ⟨_, k3'⟩ d2
      have ht₁ := ((NormalEqN.defeq hΓ' k3').of_r henv hΓ' d2).hasType.1
      exact ⟨_, .beta (hT.defeqDFC hΓ (.succ .zero (k2.symm.trans k1)) ht₁) hU, hinst eT⟩
    | proofIrrel k1 k2 _ =>
      exact ⟨_, .rfl, .proofIrrel (HasType.mkApps_proof hΓ k1 k2 (bs := [_]) hcT) hcT hb⟩
    | _ => cases hL
  | _ => cases hR

theorem ParRed.mirror_defn {r : (Pattern.const name).RHS × (Pattern.const name).Check}
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : Pat (.const name) r)
    (hm : (Pattern.const name).Matches e m1 m2) (hck : r.2.OK (IsDefEqU env univs Γ) m1 m2)
    (hargs : ∀ a, ParRed Γ (m2 a) (m2' a))
    (hc : NormalEq₀ Γ c e) (ha : Γ ⊢ e : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' (r.1.apply m1 m2') := by
  have hstep : ParRed Γ e (r.1.apply m1 m2') := .extra hp hm hck hargs
  have hb := hstep.hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  cases hm
  rcases NormalEq₀.spine_expose hΓ .const (targs := []) hc hcT with hP | ⟨h', targs', he, rfl, hrel⟩
  · exact ⟨c, .rfl, .proofIrrel hP hcT hb⟩
  cases hrel
  obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const name ls₁ ∧ List.Forall₂ (· ≈ ·) ls₁ m1 := by
    cases he with | const h => exact ⟨_, rfl, h⟩
  obtain ⟨_, _, hw, _⟩ := ha.const_inv henv hΓ
  obtain ⟨_, _, hw₁, _⟩ := hcT.const_inv henv hΓ
  let zeroArgs : (Pattern.const name).Path → VExpr := nofun
  have hck₁ := Pattern.Check.const_levels hΓ hw hw₁
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls)) hck
    (values' := zeroArgs)
  have hr₁ : ParRed Γ (.const name ls₁) (r.1.apply ls₁ zeroArgs) :=
    .extra hp .const hck₁ (fun a => nomatch a)
  exact ⟨_, hr₁, NormalEqF.of_levelEquiv hΓ (r.1.const_levelEquiv hw₁ hw hls)
    (hr₁.hasType hΓ hcT)⟩

theorem ParRed.mirror_iota
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hck : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hargs : ∀ a, ParRed Γ (m2 a) (m2' a))
    (ih : ∀ a, MirrorP Γ (m2 a) (m2' a))
    (hc : NormalEq₀ Γ c e) (ha : Γ ⊢ e : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' (r.1.apply m1 m2') := by
  classical
  have hstep : ParRed Γ e (r.1.apply m1 m2') := .extra hp hm hck hargs
  have hb := hstep.hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  have hm₀ := hm
  obtain ⟨F, M, lsc, g1, g2, hF, hM, rfl, rfl⟩ :
      ∃ F M lsc g1 g2, ((Pattern.const rc).varN mr).Matches F m1 g1 ∧
        ((Pattern.const cc).varN kc).Matches M lsc g2 ∧ e = .app F M ∧ m2 = Sum.elim g1 g2 := by
    cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
  obtain ⟨vsF, rfl⟩ : ∃ vs, F = VExpr.mkApps (.const rc m1) vs := ⟨_, hF.const_arguments⟩
  obtain ⟨fsM, rfl⟩ : ∃ fs, M = VExpr.mkApps (.const cc lsc) fs := ⟨_, hM.const_arguments⟩
  obtain ⟨n, hc'⟩ := hc
  generalize hR : VExpr.app (VExpr.mkApps (.const rc m1) vsF) (VExpr.mkApps (.const cc lsc) fsM) = R
    at hc'
  cases hc' with
  | refl _ => subst hR; exact ⟨_, hstep, .refl hb⟩
  | proofIrrel l1 l2 l3 => subst hR; exact ⟨c, .rfl, .proofIrrel l1 l2 (hstep.hasType hΓ l3)⟩
  | appDF l1 l2 l3 l4 l5 l6 =>
    cases hR
    rcases NormalEq₀.spine_expose hΓ .const ⟨_, l5⟩ l1 with hP | ⟨h', vs₁, he, rfl, hvs⟩
    · exact ⟨_, .rfl, .proofIrrel (HasType.mkApps_proof hΓ hP l1 (bs := [_]) hcT) hcT hb⟩
    obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .const rc ls₁ ∧ List.Forall₂ (· ≈ ·) ls₁ m1 := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    rcases NormalEq₀.spine_expose hΓ .const ⟨_, l6⟩ l3 with hP | ⟨h'', fs₂, he', rfl, hfs⟩
    · exact ⟨_, .rfl, .proofIrrel (Params.major_proof hΓ hp hm₀ hck ha l4 hP) hcT hb⟩
    obtain ⟨lsc₂, rfl, _⟩ : ∃ lsc₂, h'' = .const cc lsc₂ ∧ List.Forall₂ (· ≈ ·) lsc₂ lsc := by
      cases he' with | const h => exact ⟨_, rfl, h⟩
    obtain ⟨m3₁, hm3₁, hr₁⟩ := Pattern.Matches.constVarN_transport mr hF hvs (ls' := ls₁)
    obtain ⟨m3₂, hm3₂, hr₂⟩ := Pattern.Matches.constVarN_transport kc hM hfs (ls' := lsc₂)
    have hm₃ := Pattern.Matches.app hm3₁ hm3₂
    have hrel3 : ∀ a, NormalEq₀ Γ (Sum.elim m3₁ m3₂ a) (Sum.elim g1 g2 a) := by
      intro a; cases a with
      | inl a => exact hr₁ a
      | inr a => exact hr₂ a
    obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ l1
    obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ l2
    obtain ⟨_, _, hw₁, _⟩ := hh₁.const_inv henv hΓ
    obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
    have hc₃ := hck.normal_congr hΓ (ls₁ := ls₁)
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
      hw hw₁ (fun a => (hrel3 a).symm hΓ)
    have hcap : ∀ a, ∃ Y, ParRed Γ (Sum.elim m3₁ m3₂ a) Y ∧ NormalEq₀ Γ Y (m2' a) := fun a =>
      ih a hΓ (hrel3 a) (hm₀.hasType hΓ ha a).choose_spec
    let m4 := fun a => Classical.choose (hcap a)
    have hm4r : ∀ a, ParRed Γ (Sum.elim m3₁ m3₂ a) (m4 a) :=
      fun a => (Classical.choose_spec (hcap a)).1
    have hm4n : ∀ a, NormalEq₀ Γ (m4 a) (m2' a) := fun a => (Classical.choose_spec (hcap a)).2
    have hfire := ParRed.extra (Γ := Γ) hp hm₃ hc₃ hm4r
    exact ⟨_, hfire, NormalEqF.apply_congr hΓ r.1 hls hw₁ hw hm4n (hfire.hasType hΓ hcT)⟩
  | _ => cases hR

theorem ParRed.mirror_schema {rule : InductiveSignature.CaseSchema.AppliedRule}
    {actual : InductiveSignature.CaseSchema.Application}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : CaseRedex env univs Γ rule actual)
    (hl : arguments.length = (rule.capture actual).length)
    (hr : ∀ i (hi : i < (rule.capture actual).length),
      ParRed Γ (rule.capture actual)[i] (arguments[i]'(by omega)))
    (ih : ∀ i (hi : i < (rule.capture actual).length),
      MirrorP Γ (rule.capture actual)[i] (arguments[i]'(by omega)))
    (hc : NormalEq₀ Γ c actual.expr) (ha : Γ ⊢ actual.expr : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' (rule.rhs actual.levels arguments) := by
  have hstep : ParRed Γ actual.expr (rule.rhs actual.levels arguments) := .schema hm hl hr
  have hb := hstep.hasType hΓ ha
  have hcT := ha.defeqU_l henv hΓ (NormalEqF.defeq hΓ hc).symm
  obtain ⟨n, hc'⟩ := hc
  generalize hR : actual.expr = R at hc'
  cases hc' with
  | refl _ => subst hR; exact ⟨_, hstep, .refl hb⟩
  | proofIrrel l1 l2 l3 => subst hR; exact ⟨c, .rfl, .proofIrrel l1 l2 (hstep.hasType hΓ l3)⟩
  | appDF l1 l2 l3 l4 l5 l6 =>
    simp only [InductiveSignature.CaseSchema.Application.expr, VExpr.app.injEq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    rcases NormalEq₀.spine_expose hΓ .elim ⟨_, l5⟩ l1 with hP | ⟨h', vs₁, he, rfl, hvs⟩
    · exact ⟨_, .rfl, .proofIrrel (HasType.mkApps_proof hΓ hP l1 (bs := [_]) hcT) hcT hb⟩
    obtain ⟨ls₁, rfl, hls⟩ : ∃ ls₁, h' = .elim actual.block actual.owner ls₁ ∧
        List.Forall₂ (· ≈ ·) ls₁ actual.levels := by
      cases he with | elim h => exact ⟨_, rfl, h⟩
    rcases NormalEq₀.spine_expose hΓ .const ⟨_, l6⟩ l3 with hP | ⟨h'', cs₂, he', rfl, hcs⟩
    · obtain ⟨resultType, hres, hEres⟩ := hm.result_prop_of_major_proof henv hΓ hP l4
      exact ⟨_, .rfl, .proofIrrel (hres.defeqU_l henv hΓ (hEres.uniqU henv hΓ ha)) hcT hb⟩
    obtain ⟨ls₂, rfl, hls₂⟩ : ∃ ls₂, h'' = .const actual.ctorName ls₂ ∧
        List.Forall₂ (· ≈ ·) ls₂ actual.ctorLevels := by
      cases he' with | const h => exact ⟨_, rfl, h⟩
    obtain ⟨_, hh₁⟩ := schema_mkApps_head_type hΓ l1
    have hw₁ := HasType.elim_levels_wf hΓ hh₁
    obtain ⟨_, hch⟩ := schema_mkApps_head_type hΓ l3
    obtain ⟨_, _, hw₂, _⟩ := hch.const_inv henv hΓ
    let actual'' : InductiveSignature.CaseSchema.Application :=
      { actual with levels := ls₁, ctorLevels := ls₂ }
    let actual₃ : InductiveSignature.CaseSchema.Application :=
      { actual'' with arguments := vs₁, ctorArguments := cs₂ }
    have hlsSymm : List.Forall₂ (· ≈ ·) actual.levels ls₁ :=
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls)
    have hls₂Symm : List.Forall₂ (· ≈ ·) actual.ctorLevels ls₂ :=
      Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls₂)
    have hL : VExpr.LEquiv univs actual.expr actual''.expr :=
      .app (VExpr.LEquiv.mkApps_fn (.elim hlsSymm hw₁) _) (VExpr.LEquiv.mkApps_fn (.const hls₂Symm hw₂) _)
    have he'' := (NormalEqF.of_levelEquiv (η := false) hΓ hL ha).defeq hΓ
    have hm' := hm.congr_levels henv hΓ hw₁ hlsSymm hls₂Symm he''
    have hspine : CaseApplicationRelated (NormalEq₀ Γ) actual₃ actual'' :=
      ⟨rfl, rfl, rfl, rfl, rfl, hvs, hcs⟩
    have hm₃ := CaseRedex.of_normalEq_spine hΓ hm' hspine
    have hcap : List.Forall₂ (NormalEq₀ Γ) (rule.capture actual₃) (rule.capture actual) :=
      hspine.capture
    have hS : List.Forall₂ (MirrorP Γ) (rule.capture actual) arguments :=
      List.forall₂_of_getElem hl.symm fun i hi _ => ih i hi
    obtain ⟨Xs, hXs, eXs⟩ := List.Forall₂.exists_mid hcap hS fun x y z hy h1 h2 =>
      h2 hΓ h1 (hm.capture_typed hy).choose_spec
    have ⟨hl', hx'⟩ := getElem_of_forall₂ hXs
    have hfire : ParRed Γ actual₃.expr (rule.rhs actual₃.levels Xs) :=
      .schema hm₃ hl'.symm fun i hi => hx' i hi (by omega)
    have hvars := hm.source.rhs_variables
    have hT := hfire.hasType hΓ hcT
    refine ⟨_, hfire, ?_⟩
    simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at hT ⊢
    exact NormalEqF.instantiateParams_args hΓ eXs hT
  | _ =>
    simp only [InductiveSignature.CaseSchema.Application.expr] at hR
    cases hR

end ParRedMirror

theorem ParRed.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : ParRed Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' b := by
  induction H generalizing c A with
  | schema hm hl hr ih => exact ParRed.mirror_schema hΓ hm hl hr ih hc ha
  | bvar | sort | const | elim => exact ⟨c, .rfl, hc⟩
  | @app _ f f' x x' h1 h2 ih1 ih2 =>
    have hb := (ParRedS.full (.tail .rfl (.app h1 h2))).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.app f x = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .app h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((ParRedS.full (.tail .rfl (.app h1 h2))).hasType hΓ l3)⟩
    | appDF l1 l2 l3 l4 l5 l6 =>
      cases hR
      obtain ⟨F, hF, eF⟩ := ih1 hΓ ⟨_, l5⟩ l2
      obtain ⟨X, hX, eX⟩ := ih2 hΓ ⟨_, l6⟩ l4
      exact ⟨_, .app hF hX, .appDF ((ParRedS.full (.tail .rfl hF)).hasType hΓ l1)
        ((ParRedS.full (.tail .rfl h1)).hasType hΓ l2) ((ParRedS.full (.tail .rfl hX)).hasType hΓ l3)
        ((ParRedS.full (.tail .rfl h2)).hasType hΓ l4) eF eX⟩
    | sortDF | constDF | elimDF | projDF | lamDF | forallEDF => cases hR
  | @proj _ m m' family index h1 ih =>
    have hb := (ParRedS.full (.tail .rfl (.proj h1))).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.proj family index m = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .proj h1, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((ParRedS.full (.tail .rfl (.proj h1))).hasType hΓ l3)⟩
    | projDF l1 l2 =>
      cases hR
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M, hM, eM⟩ := ih hΓ ⟨_, l2⟩ hm.hasType.2
      exact ⟨_, .proj hM, .projDF ((ParRedS.full (.tail .rfl (.proj hM))).hasType hΓ l1) eM⟩
    | sortDF | constDF | elimDF | appDF | lamDF | forallEDF => cases hR
  | @lam _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (ParRedS.full (.tail .rfl (.lam h1 h2))).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.lam D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .lam h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((ParRedS.full (.tail .rfl (.lam h1 h2))).hasType hΓ l3)⟩
    | lamDF l1 l2 l3 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have l3' := l3.defeqDFC hΓ (.succ .zero l2)
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l3'⟩ ht
      have hDD₁ := l2.symm.trans l1
      have ht₁ := ((NormalEqN.defeq hΓ' l3').of_r henv hΓ' ht).hasType.1
      refine ⟨_, .lam .rfl (hT.defeqDFC hΓ (.succ .zero hDD₁) ht₁), ?_⟩
      have hD2 := l2.hasType.2
      have hDD' := (ParRedS.full (.tail .rfl h1)).defeq hΓ hD2
      exact .lamDF hDD₁ hDD' eT
    | sortDF | constDF | elimDF | appDF | projDF | forallEDF => cases hR
  | @forallE _ D D' t t' h1 h2 ih1 ih2 =>
    have hb := (ParRedS.full (.tail .rfl (.forallE h1 h2))).hasType hΓ ha
    obtain ⟨n, hc⟩ := hc
    generalize hR : VExpr.forallE D t = R at hc
    cases hc with
    | refl _ => subst hR; exact ⟨_, .forallE h1 h2, .refl hb⟩
    | proofIrrel l1 l2 l3 =>
      subst hR
      exact ⟨c, .rfl, .proofIrrel l1 l2 ((ParRedS.full (.tail .rfl (.forallE h1 h2))).hasType hΓ l3)⟩
    | forallEDF l1 l2 l3 l4 =>
      cases hR
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.forallE_inv henv
      obtain ⟨D₁', hD₁, eD⟩ := ih1 hΓ ⟨_, l2⟩ hD
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have W' := l1.transU_l henv hΓ (NormalEqN.defeq hΓ l2)
      have l4' := l4.defeqDFC hΓ (.succ .zero W')
      obtain ⟨T, hT, eT⟩ := ih2 hΓ' ⟨_, l4'⟩ ht
      have l3'' := l3.defeqDFC henv (.succ .zero W')
      have hA₁ := l1.hasType.2
      have hD₁T := (ParRedS.full (.tail .rfl hD₁)).defeq hΓ hA₁
      refine ⟨_, .forallE hD₁ (hT.defeqDFC hΓ (.succ .zero (W'.symm.trans l1)) l3''), ?_⟩
      have hT1 := (ParRedS.full (.tail .rfl hT)).hasType hΓ' l3''
      exact .forallEDF (W'.symm.trans (l1.trans hD₁T)) eD hT1 eT
    | sortDF | constDF | elimDF | appDF | projDF | lamDF => cases hR
  | beta h1 h2 ih1 ih2 => exact ParRed.mirror_beta hΓ h1 h2 ih1 ih2 hc ha
  | extra hp hm hck hargs ih =>
    obtain ⟨sp, rfl⟩ := Params.pat_simple hp
    cases sp with
    | defn name => exact ParRed.mirror_defn hΓ hp hm hck hargs hc ha
    | iota rc mr cc kc => exact ParRed.mirror_iota hΓ hp hm hck hargs ih hc ha



section DeltaParRed

omit [Params] in
theorem sizeOf_mkApps_head (f : VExpr) (args : List VExpr) :
    sizeOf f ≤ sizeOf (VExpr.mkApps f args) := by
  induction args generalizing f with
  | nil => exact Nat.le_refl _
  | cons a args ih => exact Nat.le_trans (by simp; omega) (ih (.app f a))

omit [Params] in
theorem sizeOf_mkApps_arg (h : a ∈ args) : sizeOf a < sizeOf (VExpr.mkApps f args) := by
  induction args generalizing f with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.lt_of_lt_of_le (by simp; omega) (sizeOf_mkApps_head (.app f a) xs)
    · exact ih h

omit [Params] in
theorem _root_.Lean4Lean.Pattern.Matches.sizeOf_lt {p : Pattern} {m1 : List VLevel}
    {m2 : p.Path → VExpr} (hm : p.Matches e m1 m2)
    (v : p.Path) : sizeOf (m2 v) < sizeOf e := by
  induction hm with
  | const | elim => exact v.elim
  | var _ ih =>
    cases v with
    | none => simp; omega
    | some w => have := ih w; simp; omega
  | app _ _ ih1 ih2 =>
    cases v with
    | inl w => have := ih1 w; simp; omega
    | inr w => have := ih2 w; simp; omega

omit [Params] in
theorem sizeOf_capture {rule : InductiveSignature.CaseSchema.AppliedRule}
    {actual : InductiveSignature.CaseSchema.Application} (h : x ∈ rule.capture actual) :
    sizeOf x < sizeOf actual.expr := by
  simp only [InductiveSignature.CaseSchema.AppliedRule.capture] at h
  simp only [InductiveSignature.CaseSchema.Application.expr]
  rcases List.mem_append.mp h with h | h
  · have := sizeOf_mkApps_arg (f := .elim actual.block actual.owner actual.levels)
      (List.mem_of_mem_take h)
    simp; omega
  · have := sizeOf_mkApps_arg (f := .const actual.ctorName actual.ctorLevels)
      (List.mem_of_mem_drop h)
    simp; omega

theorem DeltaPar.lam_inv (H : DeltaPar Γ (.lam A t) X) :
    ∃ A' t', DeltaPar Γ A A' ∧ DeltaPar (A :: Γ) t t' ∧ X = .lam A' t' := by
  generalize he : VExpr.lam A t = src at H
  cases H with
  | lam h1 h2 => cases he; exact ⟨_, _, h1, h2, rfl⟩
  | delta => exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm).elim
  | quotDelta => exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm).elim
  | _ => cases he



omit [Params] in
theorem forall₂_getElem?_left {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {i : Nat} {x : α}, List.Forall₂ R l l' → l[i]? = some x →
      ∃ y, l'[i]? = some y ∧ R x y
  | _ :: _, _ :: _, 0, _, .cons h _, hx => by cases hx; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ t, hx => by
    simp only [List.getElem?_cons_succ] at hx ⊢; exact forall₂_getElem?_left t hx
  | [], [], _, _, .nil, hx => by cases hx

theorem PrefixUnfold.length_le (H : PrefixUnfold env univs recursorData Γ name ls args rhs) :
    ∃ data, recursorData name = some data ∧ args.length ≤ data.majorOffset := by
  cases H with
  | @intro data program hl _ _ _ _ _ hg _ =>
    exact ⟨data, hl, (InductiveSignature.RecursorData.singletonUnfolding_spec hg).1⟩

theorem QuotPrefixUnfold.length_le (H : QuotPrefixUnfold env univs Γ ls args rhs) : args.length ≤ 5 := by
  cases H with
  | intro _ _ _ hg _ => exact (QuotPrefixUnfolding.generate_spec hg).2.1

theorem HasType.mkApps_args_typed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ VExpr.mkApps f args : T) : ∀ x ∈ args, ∃ A, Γ ⊢ x : A :=
  fun _ hx => schema_mkApps_arg_type hΓ ht hx

/-- The diamond property of `DeltaPar` against `ParRed` for terms below a size. -/
abbrev DPDiaBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → DeltaPar Γ a b → ParRed Γ a c →
    Γ ⊢ a : A → ∃ d₁ d₂, ParRed Γ b d₁ ∧ DeltaPar Γ c d₂ ∧ NormalEq₀ Γ d₁ d₂

omit [Params] in
theorem List.Forall₂.exists_join {R₁ R₂ S T U : α → α → Prop} :
    ∀ {l l₁ l₂}, List.Forall₂ R₁ l l₁ → List.Forall₂ R₂ l l₂ →
      (∀ x y z, x ∈ l → R₁ x y → R₂ x z → ∃ u v, S y u ∧ T z v ∧ U u v) →
      ∃ us vs, List.Forall₂ S l₁ us ∧ List.Forall₂ T l₂ vs ∧ List.Forall₂ U us vs
  | [], [], [], .nil, .nil, _ => ⟨[], [], .nil, .nil, .nil⟩
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2, H => by
    obtain ⟨u, v, hs, ht, hu⟩ := H _ _ _ (List.mem_cons_self ..) h1 h2
    obtain ⟨us, vs, hss, hts, hus⟩ := List.Forall₂.exists_join t1 t2
      fun x y z hx => H x y z (List.mem_cons_of_mem _ hx)
    exact ⟨u :: us, v :: vs, .cons hs hss, .cons ht hts, .cons hu hus⟩

theorem DeltaPar.parRed_args {a : VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DPDiaBelow (sizeOf a)) (hsub : ∀ x ∈ args, sizeOf x < sizeOf a)
    (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h1 : List.Forall₂ (DeltaPar Γ) args args') (h2 : List.Forall₂ (ParRed Γ) args argsP) :
    ∃ D₁ D₂, List.Forall₂ (ParRed Γ) args' D₁ ∧ List.Forall₂ (DeltaPar Γ) argsP D₂ ∧
      List.Forall₂ (NormalEq₀ Γ) D₁ D₂ :=
  List.Forall₂.exists_join h1 h2 fun x _ _ hx d p =>
    IH (hsub x hx) hΓ d p (htyped x hx).choose_spec

theorem DeltaPar.parRed_iota
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hΓ : OnCtx Γ (env.IsType univs)) (IH : DPDiaBelow (sizeOf e))
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hck : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hargs : ∀ v, ParRed Γ (m2 v) (m2' v))
    (H : DeltaPar Γ e b) (ha : Γ ⊢ e : A) :
    ∃ d₁ d₂, ParRed Γ b d₁ ∧ DeltaPar Γ (r.1.apply m1 m2') d₂ ∧ NormalEq₀ Γ d₁ d₂ := by
  classical
  have hm₀ := hm
  obtain ⟨F, M, lsc, g1, g2, hF, hM, rfl, rfl⟩ :
      ∃ F M lsc g1 g2, ((Pattern.const rc).varN mr).Matches F m1 g1 ∧
        ((Pattern.const cc).varN kc).Matches M lsc g2 ∧ e = .app F M ∧ m2 = Sum.elim g1 g2 := by
    cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
  obtain ⟨vsF, rfl⟩ : ∃ vs, F = VExpr.mkApps (.const rc m1) vs := ⟨_, hF.const_arguments⟩
  obtain ⟨fsM, rfl⟩ : ∃ fs, M = VExpr.mkApps (.const cc lsc) fs := ⟨_, hM.const_arguments⟩
  rw [← VExpr.mkApps_snoc] at H
  obtain ⟨args', rfl, hargs'⟩ := DeltaPar.const_spine_of (vsF ++ [_]).length
    (fun _ hr => Params.iota_no_delta hp hck hr)
    (fun _ hq hr => by subst hq; exact Params.iota_no_quotDelta hp hck hr) (Nat.le_refl _) H
  obtain ⟨vs', M', rfl, hvs', hM'⟩ := List.forall₂_snoc_left hargs'
  obtain ⟨fs', rfl, hfs'⟩ := DeltaPar.rigid_spine (pat_ctor_rigid hp) hM'
  obtain ⟨m3₁, hm3₁, hr₁⟩ := Pattern.Matches.constVarN_transport (R := fun x y => DeltaPar Γ y x)
    mr hF (Lean4Lean.List.Forall₂.flip hvs') (ls' := m1)
  obtain ⟨m3₂, hm3₂, hr₂⟩ := Pattern.Matches.constVarN_transport (R := fun x y => DeltaPar Γ y x)
    kc hM (Lean4Lean.List.Forall₂.flip hfs') (ls' := lsc)
  have hm₃ := Pattern.Matches.app hm3₁ hm3₂
  have hrel : ∀ v, DeltaPar Γ (Sum.elim g1 g2 v) (Sum.elim m3₁ m3₂ v) := by
    intro v; cases v with
    | inl v => exact hr₁ v
    | inr v => exact hr₂ v
  have htv : ∀ v, ∃ T, Γ ⊢ Sum.elim g1 g2 v : T := fun v => hm₀.hasType hΓ ha v
  have hj : ∀ v, ∃ d₁ d₂, ParRed Γ (Sum.elim m3₁ m3₂ v) d₁ ∧ DeltaPar Γ (m2' v) d₂ ∧
      NormalEq₀ Γ d₁ d₂ := fun v =>
    IH (hm₀.sizeOf_lt v) hΓ (hrel v) (hargs v) (htv v).choose_spec
  let D₁ := fun v => (hj v).choose
  let D₂ := fun v => (hj v).choose_spec.choose
  have pD₁ : ∀ v, ParRed Γ (Sum.elim m3₁ m3₂ v) (D₁ v) := fun v => (hj v).choose_spec.choose_spec.1
  have pD₂ : ∀ v, DeltaPar Γ (m2' v) (D₂ v) := fun v => (hj v).choose_spec.choose_spec.2.1
  have eD : ∀ v, NormalEq₀ Γ (D₁ v) (D₂ v) := fun v => (hj v).choose_spec.choose_spec.2.2
  have hck₃ := Pattern.Check.OK.defeq_values hΓ
    (p := Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
    (m' := Sum.elim m3₁ m3₂)
    (fun v => ⟨_, (DeltaPar.full (hrel v)).defeq hΓ (htv v).choose_spec⟩) hck
  have hfire := ParRed.extra (Γ := Γ) hp hm₃ hck₃ pD₁
  have hbT : Γ ⊢ VExpr.app (VExpr.mkApps (.const rc m1) vs') (VExpr.mkApps (.const cc lsc) fs') : A := by
    have := (DeltaPar.full H).hasType hΓ (by rwa [VExpr.mkApps_snoc])
    rwa [VExpr.mkApps_snoc] at this
  obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ (ha.app_inv henv hΓ).choose_spec.choose_spec.1
  obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
  refine ⟨_, _, by rw [VExpr.mkApps_snoc]; exact hfire, DeltaPar.congrRel.apply_rhs r.1 pD₂, ?_⟩
  exact NormalEqF.apply_congr hΓ r.1 (VLevel.forall₂_equiv_refl m1) hw hw eD (hfire.hasType hΓ hbT)


omit [Params] in
theorem case_expr_spine (actual : InductiveSignature.CaseSchema.Application) :
    actual.expr = VExpr.mkApps (.elim actual.block actual.owner actual.levels)
      (actual.arguments ++ [VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
        actual.ctorArguments]) := by
  rw [VExpr.mkApps_snoc]; rfl

theorem forall₂_defeq_of_rel {R : List VExpr → VExpr → VExpr → Prop}
    (hdef : ∀ {a b A}, R Γ a b → Γ ⊢ a : A → Γ ⊢ a ≡ b : A)
    (htyped : ∀ x ∈ l, ∃ T, Γ ⊢ x : T) (H : List.Forall₂ (R Γ) l l') :
    List.Forall₂ (IsDefEqU env univs Γ) l l' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih =>
    obtain ⟨_, ht⟩ := htyped _ (List.mem_cons_self ..)
    exact .cons ⟨_, hdef h ht⟩ (ih fun x hx => htyped x (List.mem_cons_of_mem _ hx))

theorem DeltaPar.parRed_schema {rule : InductiveSignature.CaseSchema.AppliedRule}
    {actual : InductiveSignature.CaseSchema.Application}
    (hΓ : OnCtx Γ (env.IsType univs)) (IH : DPDiaBelow (sizeOf actual.expr))
    (hm : CaseRedex env univs Γ rule actual)
    (hl : arguments.length = (rule.capture actual).length)
    (hr : ∀ i (hi : i < (rule.capture actual).length),
      ParRed Γ (rule.capture actual)[i] (arguments[i]'(by omega)))
    (H : DeltaPar Γ actual.expr b) (ha : Γ ⊢ actual.expr : A) :
    ∃ d₁ d₂, ParRed Γ b d₁ ∧ DeltaPar Γ (rule.rhs actual.levels arguments) d₂ ∧
      NormalEq₀ Γ d₁ d₂ := by
  have ha' := ha
  rw [case_expr_spine] at H ha'
  obtain ⟨args', rfl, hargs'⟩ := DeltaPar.elim_spine H
  obtain ⟨vs', M', rfl, hvs', hM'⟩ := List.forall₂_snoc_left hargs'
  obtain ⟨cs', rfl, hcs'⟩ := DeltaPar.rigid_spine hm.ctor_rigid hM'
  let actual' : InductiveSignature.CaseSchema.Application :=
    { actual with arguments := vs', ctorArguments := cs' }
  have hspine : CaseApplicationRelated (DeltaPar Γ) actual actual' :=
    ⟨rfl, rfl, rfl, rfl, rfl, hvs', hcs'⟩
  obtain ⟨_, _, hfn, hmaj⟩ := ha.app_inv henv hΓ
  have hdefs : CaseApplicationRelated (IsDefEqU env univs Γ) actual actual' :=
    ⟨rfl, rfl, rfl, rfl, rfl,
      forall₂_defeq_of_rel (fun h ht => (DeltaPar.full h).defeq hΓ ht)
        (fun _ hx => schema_mkApps_arg_type hΓ hfn hx) hvs',
      forall₂_defeq_of_rel (fun h ht => (DeltaPar.full h).defeq hΓ ht)
        (fun _ hx => schema_mkApps_arg_type hΓ hmaj hx) hcs'⟩
  have hexpr : actual'.expr = VExpr.mkApps (.elim actual.block actual.owner actual.levels)
      (vs' ++ [VExpr.mkApps (.const actual.ctorName actual.ctorLevels) cs']) :=
    case_expr_spine actual'
  have hb := (DeltaPar.full H).hasType hΓ ha'
  have hdef := (DeltaPar.full H).defeq hΓ ha'
  rw [← case_expr_spine actual, ← hexpr] at hdef
  have hm' := hm.congr henv hΓ hdefs ⟨_, hdef⟩
  have hcap := hspine.capture (rule := rule)
  have hargsP : List.Forall₂ (ParRed Γ) (rule.capture actual) arguments :=
    List.forall₂_of_getElem hl.symm fun i hi _ => hr i hi
  obtain ⟨D₁, D₂, pD₁, pD₂, eD⟩ := List.Forall₂.exists_join hcap hargsP
    fun x _ _ hx d p => IH (sizeOf_capture hx) hΓ d p (hm.capture_typed hx).choose_spec
  have ⟨hl₁, hx₁⟩ := getElem_of_forall₂ pD₁
  have hfire : ParRed Γ actual'.expr (rule.rhs actual'.levels D₁) :=
    .schema hm' hl₁.symm fun i hi => hx₁ i hi (by omega)
  rw [hexpr] at hfire
  refine ⟨_, rule.rhs actual.levels D₂, hfire, ?_, ?_⟩
  · simp only [InductiveSignature.CaseSchema.AppliedRule.rhs]
    exact DeltaPar.congrRel.instantiateParams_args pD₂
  · have hT := hfire.hasType hΓ hb
    simp only [InductiveSignature.CaseSchema.AppliedRule.rhs] at hT ⊢
    exact NormalEqF.instantiateParams_args hΓ eD hT

theorem DeltaPar.parRed_projIota (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DPDiaBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args') : fieldType)
    (hi : args'[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (H2 : ParRed Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) c)
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A) :
    ∃ d₁ d₂, ParRed Γ field d₁ ∧ DeltaPar Γ c d₂ ∧ NormalEq₀ Γ d₁ d₂ := by
  have hb := (DeltaPar.full (.projIota hlen hargs hl hs hi ht)).hasType hΓ ha
  have hc := H2.hasType hΓ ha
  cases H2 with
  | proj hM =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨argsP, rfl, hP⟩ := ParRed.rigid_const_spine (projection_ctor_rigid hl) hM
    obtain ⟨D₁, D₂, pD₁, pD₂, eD⟩ := DeltaPar.parRed_args hΓ IH
      (fun _ hx => by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hx; simp; omega)
      (HasType.mkApps_args_typed hΓ lm.hasType.2) (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨d₁, hd₁, pd₁⟩ := forall₂_getElem?_left pD₁ hi
    obtain ⟨d₂, hd₂, ed⟩ := forall₂_getElem?_left eD hd₁
    have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) argsP))
        (.proj family index (VExpr.mkApps (.const info.ctorName ls) D₂)) :=
      .proj (DeltaPar.mkApps_args pD₂)
    have hT := (DeltaPar.full hcong).hasType hΓ hc
    have hd₁T := pd₁.hasType hΓ hb
    have hd₂T := hd₁T.defeqU_l henv hΓ (NormalEqF.defeq hΓ ed)
    have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ pD₂
    exact ⟨d₁, d₂, pd₁, .projIota hl₂ hx₂ hl hT hd₂ hd₂T, ed⟩
  | extra _ hm => cases hm

theorem DeltaPar.parRed_diamond_aux : ∀ n, DPDiaBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have hb := (DeltaPar.full H).hasType hΓ ha
  have hc := H2.hasType hΓ ha
  by_cases hprop : Γ ⊢ A : .sort .zero
  · exact ⟨b, c, .rfl, .rfl, .proofIrrel hprop hb hc⟩
  have IH : DPDiaBelow (sizeOf a) := fun h => ih (by omega)
  cases H with
  | bvar | sort | const | elim => exact ⟨c, c, H2, .rfl, .refl hc⟩
  | @app _ f f' x x' hF hX =>
    cases H2 with
    | app hf hx =>
      obtain ⟨_, _, lf, lx⟩ := ha.app_inv henv hΓ
      obtain ⟨F₁, F₂, pF, dF, eF⟩ := IH (by simp; omega) hΓ hF hf lf
      obtain ⟨X₁, X₂, pX, dX, eX⟩ := IH (by simp; omega) hΓ hX hx lx
      have tF₁ := pF.hasType hΓ ((DeltaPar.full hF).hasType hΓ lf)
      have tF₂ := (DeltaPar.full dF).hasType hΓ (hf.hasType hΓ lf)
      have tX₁ := pX.hasType hΓ ((DeltaPar.full hX).hasType hΓ lx)
      have tX₂ := (DeltaPar.full dX).hasType hΓ (hx.hasType hΓ lx)
      exact ⟨_, _, .app pF pX, .app dF dX, .appDF tF₁ tF₂ tX₁ tX₂ eF eX⟩
    | beta ht hu =>
      obtain ⟨_, _, lf, lx⟩ := ha.app_inv henv hΓ
      have ⟨⟨_, lD⟩, _, lt⟩ := lf.lam_inv henv hΓ
      have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lD lt)).forallE_inv henv hΓ
      have lx' := hw.defeq lx
      obtain ⟨D', t', hD, ht', rfl⟩ := DeltaPar.lam_inv hF
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨T₁, T₂, pT, dT, eT⟩ := IH (by simp; omega) hΓ' ht' ht lt
      obtain ⟨U₁, U₂, pU, dU, eU⟩ := IH (by simp; omega) hΓ hX hu lx'
      have hDD := (DeltaPar.full hD).defeq hΓ lD
      have tt' := (DeltaPar.full ht').hasType hΓ' lt
      have tU₁ := pU.hasType hΓ ((DeltaPar.full hX).hasType hΓ lx')
      have tu₂ := hu.hasType hΓ lx'
      have tt₂ := ht.hasType hΓ' lt
      have tT₂ := (DeltaPar.full dT).hasType hΓ' tt₂
      refine ⟨T₁.inst U₁, T₂.inst U₂,
        .beta (pT.defeqDFC hΓ (.succ .zero hDD) tt') pU,
        DeltaPar.instN .zero hΓ' dU tu₂ dT tt₂, ?_⟩
      exact (NormalEqF.instN tU₁ .zero eT).trans hΓ (NormalEqF.instN_r hΓ' tU₁ eU .zero tT₂)
    | extra hp hm hck hargs =>
      obtain ⟨sp, rfl⟩ := Params.pat_simple hp
      cases sp with
      | defn => cases hm
      | iota rc mr cc kc => exact DeltaPar.parRed_iota hΓ IH hp hm hck hargs (.app hF hX) ha
    | schema hm hl hr => exact DeltaPar.parRed_schema hΓ IH hm hl hr (.app hF hX) ha
  | @delta _ name ls rhs args args' hlen hargs hr =>
    obtain ⟨data, hdata, hle⟩ := hr.length_le
    have hle' : args.length ≤ data.majorOffset := hlen ▸ hle
    obtain ⟨argsP, rfl, hP⟩ := ParRed.const_spine_of args.length
      (fun hp hpre hm => Params.no_match_delta_prefix hdata hp (by omega) hm) (Nat.le_refl _) H2
    obtain ⟨D₁, D₂, pD₁, pD₂, eD⟩ := DeltaPar.parRed_args hΓ IH
      (fun _ hx => sizeOf_mkApps_arg hx) (HasType.mkApps_args_typed hΓ ha)
      (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨rhs₁, X, hr₁, pX, eX⟩ := hr.congr_red ParRed.congrRel ParRed.argRel hΓ pD₁
    obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ ha
    obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
    obtain ⟨rhs₂, hr₂, e₂⟩ := hr₁.congr₀ hΓ hw (VLevel.forall₂_equiv_refl ls) eD
    have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ pD₂
    exact ⟨X, rhs₂, pX, .delta hl₂ hx₂ hr₂, eX.trans hΓ e₂⟩
  | @quotDelta _ ls rhs args args' hlen hargs hr =>
    have hle : args.length ≤ 5 := hlen ▸ hr.length_le
    obtain ⟨argsP, rfl, hP⟩ := ParRed.const_spine_of args.length
      (fun hp hpre hm => Params.no_match_quot_prefix hr.registered hp (by omega) hm) (Nat.le_refl _) H2
    obtain ⟨D₁, D₂, pD₁, pD₂, eD⟩ := DeltaPar.parRed_args hΓ IH
      (fun _ hx => sizeOf_mkApps_arg hx) (HasType.mkApps_args_typed hΓ ha)
      (List.forall₂_of_getElem hlen hargs) hP
    obtain ⟨rhs₁, X, hr₁, pX, eX⟩ := hr.congr_red ParRed.congrRel ParRed.argRel hΓ pD₁
    obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ ha
    obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
    obtain ⟨rhs₂, hr₂, e₂⟩ := hr₁.congr₀ hΓ hw (VLevel.forall₂_equiv_refl ls) eD
    have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ pD₂
    exact ⟨X, rhs₂, pX, .quotDelta hl₂ hx₂ hr₂, eX.trans hΓ e₂⟩
  | projIota hlen hargs hl hs hi ht =>
    exact DeltaPar.parRed_projIota hΓ IH hlen hargs hl hs hi ht H2 ha
  | proj hM =>
    cases H2 with
    | proj hm =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨M₁, M₂, pM, dM, eM⟩ := IH (by simp; omega) hΓ hM hm lm.hasType.2
      exact ⟨_, _, .proj pM, .proj dM, .projDF ((ParRed.proj pM).hasType hΓ hb) eM⟩
    | extra _ hm => cases hm
  | lam hD hT =>
    cases H2 with
    | lam hD₂ hT₂ =>
      obtain ⟨⟨_, lD⟩, _, lt⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨E₁, E₂, pE, dE, eE⟩ := IH (by simp; omega) hΓ hD hD₂ lD
      obtain ⟨T₁, T₂, pT, dT, eT⟩ := IH (by simp; omega) hΓ' hT hT₂ lt
      have hDD' := (DeltaPar.full hD).defeq hΓ lD
      have hDD₂ := hD₂.defeq hΓ lD
      have tE₁ := pE.defeq hΓ hDD'.hasType.2
      have tE₂ := (DeltaPar.full dE).defeq hΓ hDD₂.hasType.2
      have tT := (DeltaPar.full hT).hasType hΓ' lt
      have tT₂ := hT₂.hasType hΓ' lt
      exact ⟨_, _, .lam pE (pT.defeqDFC hΓ (.succ .zero hDD') tT),
        .lam dE (dT.defeqDFC hΓ (.succ .zero hDD₂) tT₂),
        .lamDF (hDD'.trans tE₁) (hDD₂.trans tE₂) eT⟩
    | extra _ hm => cases hm
  | forallE hD hT =>
    cases H2 with
    | forallE hD₂ hT₂ =>
      obtain ⟨⟨_, lD⟩, _, lt⟩ := ha.forallE_inv henv
      have hΓ' : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, lD⟩
      obtain ⟨E₁, E₂, pE, dE, eE⟩ := IH (by simp; omega) hΓ hD hD₂ lD
      obtain ⟨T₁, T₂, pT, dT, eT⟩ := IH (by simp; omega) hΓ' hT hT₂ lt
      have hDD' := (DeltaPar.full hD).defeq hΓ lD
      have hDD₂ := hD₂.defeq hΓ lD
      have tE₁ := pE.defeq hΓ hDD'.hasType.2
      have tE₂ := (DeltaPar.full dE).defeq hΓ hDD₂.hasType.2
      have tT := (DeltaPar.full hT).hasType hΓ' lt
      have tT₂ := hT₂.hasType hΓ' lt
      have tT₁ := pT.hasType hΓ' tT
      exact ⟨_, _, .forallE pE (pT.defeqDFC hΓ (.succ .zero hDD') tT),
        .forallE dE (dT.defeqDFC hΓ (.succ .zero hDD₂) tT₂),
        .forallEDF (hDD'.trans tE₁) eE tT₁ eT⟩
    | extra _ hm => cases hm

theorem DeltaPar.parRed_diamond (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d₁ d₂, ParRed Γ b d₁ ∧ DeltaPar Γ c d₂ ∧ NormalEq₀ Γ d₁ d₂ :=
  DeltaPar.parRed_diamond_aux _ (Nat.lt_succ_self _) hΓ H H2 ha

end DeltaParRed



section DeltaPeakTools

theorem ParRed.mkApps_head (hf : ParRed Γ f f') (args : List VExpr) :
    ParRed Γ (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact hf
  | cons a args ih => exact ih (.app hf .rfl)

theorem ParRedS.mkApps_head (hf : ReflTransGen (ParRed Γ) f f') (args : List VExpr) :
    ReflTransGen (ParRed Γ) (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  induction hf with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.tail (ParRed.mkApps_head h args)

theorem prefixUnfolding_supply_many {data : InductiveSignature.RecursorData}
    {packed : List VLevel} (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero) :
    ∀ (more : List VExpr) {xs : List VExpr} {p q : InductiveSignature.RecursorData.PrefixUnfolding},
      data.singletonUnfolding env univs levels xs = some p →
      data.singletonUnfolding env univs levels (xs ++ more) = some q →
      p.equationBody.rhs.ClosedN p.captures.length →
      ReflTransGen (ParRed Γ) (VExpr.mkApps p.rhs more) q.rhs
  | [], xs, p, q, hp, hq, _ => by
    rw [List.append_nil] at hq
    cases hp.symm.trans hq
    exact .rfl
  | m :: rest, xs, p, q, hp, hq, hclosed => by
    have hbound := (InductiveSignature.RecursorData.singletonUnfolding_spec hq).1
    obtain ⟨p₁, hp₁⟩ := InductiveSignature.RecursorData.singletonUnfolding_anyArity hp
      (args' := xs ++ [m]) (by simp at hbound ⊢; omega)
    obtain ⟨d, body, he, hb⟩ :=
      InductiveSignature.RecursorData.singletonUnfolding_supply_one henv hr hlarge hzero hp hp₁ hclosed
    have hspec := InductiveSignature.RecursorData.singletonUnfolding_spec hp
    have hspec₁ := InductiveSignature.RecursorData.singletonUnfolding_spec hp₁
    have heq : p.equation = p₁.equation :=
      Option.some.inj (hspec.2.2.2.2.1.symm.trans hspec₁.2.2.2.2.1)
    have hbody : p.equationBody = p₁.equationBody := by
      have h1 := hspec.2.2.2.2.2.1
      have h2 := hspec₁.2.2.2.2.2.1
      rw [heq] at h1
      exact Option.some.inj (h1.symm.trans h2)
    have hclosed₁ : p₁.equationBody.rhs.ClosedN p₁.captures.length := by
      rw [hspec₁.2.2.2.2.2.2, ← hbody, ← hspec.2.2.2.2.2.2]; exact hclosed
    have hq' : data.singletonUnfolding env univs levels ((xs ++ [m]) ++ rest) = some q := by
      simpa using hq
    have ih := prefixUnfolding_supply_many (Γ := Γ) hr hlarge hzero rest hp₁ hq' hclosed₁
    refine ReflTransGen.trans (.tail .rfl ?_) ih
    show ParRed Γ (VExpr.mkApps (.app p.rhs m) rest) _
    rw [he, ← hb]
    exact ParRed.mkApps_head (.beta .rfl .rfl) rest

theorem PrefixUnfold.supply_many
    (H₁ : PrefixUnfold env univs recursorData Γ name levels xs rhs₁)
    (H₂ : PrefixUnfold env univs recursorData Γ name levels (xs ++ more) rhs₂) :
    ReflTransGen (ParRed Γ) (VExpr.mkApps rhs₁ more) rhs₂ := by
  cases H₁ with
  | @intro data p hl hr _ hlarge _ hz hp replay =>
    cases H₂ with
    | @intro data' q hl' _ _ _ _ _ hq _ =>
      cases hl.symm.trans hl'
      exact prefixUnfolding_supply_many hr hlarge hz more hp hq (replay.templateScope henv).2.1

theorem quot_supply_many {levels : List VLevel} :
    ∀ (more : List VExpr) {xs : List VExpr} {p q : InductiveSignature.RecursorData.PrefixUnfolding},
      QuotPrefixUnfolding.generate levels xs = some p →
      QuotPrefixUnfolding.generate levels (xs ++ more) = some q →
      p.equationBody.rhs.ClosedN p.captures.length →
      ReflTransGen (ParRed Γ) (VExpr.mkApps p.rhs more) q.rhs
  | [], xs, p, q, hp, hq, _ => by
    rw [List.append_nil] at hq
    cases hp.symm.trans hq
    exact .rfl
  | m :: rest, xs, p, q, hp, hq, hclosed => by
    have hbound := (QuotPrefixUnfolding.generate_spec hq).2.1
    obtain ⟨p₁, hp₁⟩ := QuotPrefixUnfolding.generate_anyArity hp
      (args' := xs ++ [m]) (by simp at hbound ⊢; omega)
    obtain ⟨d, body, he, hb⟩ := QuotPrefixUnfolding.generate_supply_one hp hp₁ hclosed
    have hspec := QuotPrefixUnfolding.generate_spec hp
    have hspec₁ := QuotPrefixUnfolding.generate_spec hp₁
    have hbody : p.equationBody = p₁.equationBody := by
      have h1 := hspec.2.2.2.2.2.1
      have h2 := hspec₁.2.2.2.2.2.1
      rw [hspec.2.2.2.2.1] at h1
      rw [hspec₁.2.2.2.2.1] at h2
      exact Option.some.inj (h1.symm.trans h2)
    have hclosed₁ : p₁.equationBody.rhs.ClosedN p₁.captures.length := by
      rw [hspec₁.2.2.2.2.2.2, ← hbody, ← hspec.2.2.2.2.2.2]; exact hclosed
    have hq' : QuotPrefixUnfolding.generate levels ((xs ++ [m]) ++ rest) = some q := by
      simpa using hq
    have ih := quot_supply_many (Γ := Γ) rest hp₁ hq' hclosed₁
    refine ReflTransGen.trans (.tail .rfl ?_) ih
    show ParRed Γ (VExpr.mkApps (.app p.rhs m) rest) _
    rw [he, ← hb]
    exact ParRed.mkApps_head (.beta .rfl .rfl) rest

theorem QuotPrefixUnfold.supply_many
    (H₁ : QuotPrefixUnfold env univs Γ levels xs rhs₁)
    (H₂ : QuotPrefixUnfold env univs Γ levels (xs ++ more) rhs₂) :
    ReflTransGen (ParRed Γ) (VExpr.mkApps rhs₁ more) rhs₂ := by
  cases H₁ with
  | intro _ _ _ hp replay =>
    cases H₂ with
    | intro _ _ _ hq _ =>
      exact quot_supply_many more hp hq (replay.templateScope henv).2.1

/-- The shapes of a parallel prefix step on a constant spine. -/
theorem DeltaPar.const_spine_cases
    (H : DeltaPar Γ (VExpr.mkApps (.const name ls) args) out) :
    ∃ args', List.Forall₂ (DeltaPar Γ) args args' ∧
      (out = VExpr.mkApps (.const name ls) args' ∨
        ∃ k rhs, k ≤ args.length ∧
          (PrefixUnfold env univs recursorData Γ name ls (args'.take k) rhs ∨
            (name = ``Quot.lift ∧ QuotPrefixUnfold env univs Γ ls (args'.take k) rhs)) ∧
          out = VExpr.mkApps rhs (args'.drop k)) := by
  induction args using List.snoc_induction generalizing out with
  | nil =>
    generalize he : VExpr.mkApps (.const name ls) [] = src at H
    cases H with
    | const => cases he; exact ⟨[], .nil, .inl rfl⟩
    | delta hl hargs hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      cases List.length_eq_zero_iff.mp hl.symm
      exact ⟨[], .nil, .inr ⟨0, _, Nat.le_refl _, .inl hr, rfl⟩⟩
    | quotDelta hl hargs hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      cases List.length_eq_zero_iff.mp hl.symm
      exact ⟨[], .nil, .inr ⟨0, _, Nat.le_refl _, .inr ⟨rfl, hr⟩, rfl⟩⟩
    | _ => cases he
  | snoc args x ih =>
    generalize he : VExpr.mkApps (.const name ls) (args ++ [x]) = src at H
    have hshape : src = .app (VExpr.mkApps (.const name ls) args) x := by
      rw [← he, VExpr.mkApps_snoc]
    cases H with
    | @app _ _ _ _ x' hf hx =>
      cases hshape
      obtain ⟨args', hargs', hcase⟩ := ih hf
      refine ⟨args' ++ [x'], List.Forall₂.append' hargs' (.cons hx .nil), ?_⟩
      have hl := Lean4Lean.List.Forall₂.length_eq hargs'
      rcases hcase with rfl | ⟨k, rhs, hk, hr, rfl⟩
      · exact .inl (VExpr.mkApps_snoc ..).symm
      · refine .inr ⟨k, rhs, by simp; omega, ?_, ?_⟩
        · rwa [List.take_append_of_le_length (by omega)]
        · rw [List.drop_append_of_le_length (by omega), VExpr.mkApps_snoc]
    | delta hl hargs hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      have h2 := List.forall₂_of_getElem hl hargs
      refine ⟨_, h2, .inr ⟨(args ++ [x]).length, out, Nat.le_refl _, ?_, ?_⟩⟩
      · rw [hl, List.take_length]; exact .inl hr
      · rw [hl, List.drop_length]; rfl
    | quotDelta hl hargs hr =>
      obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj he
      have h2 := List.forall₂_of_getElem hl hargs
      refine ⟨_, h2, .inr ⟨(args ++ [x]).length, out, Nat.le_refl _, ?_, ?_⟩⟩
      · rw [hl, List.take_length]; exact .inr ⟨rfl, hr⟩
      · rw [hl, List.drop_length]; rfl
    | projIota => cases hshape
    | _ => cases hshape


omit [Params] in
theorem forall₂_update {R : α → α → Prop} (hrefl : ∀ z ∈ pre ++ xs, R z z) (h : R x x') :
    List.Forall₂ R (pre ++ x :: xs) (pre ++ x' :: xs) := by
  induction pre with
  | nil =>
    exact .cons h (List.Forall₂.rfl fun z hz => hrefl z (by simpa using hz))
  | cons p pre ih =>
    exact .cons (hrefl p (by simp)) (ih fun z hz => hrefl z (by
      simp only [List.cons_append, List.mem_cons]; exact .inr hz))

theorem rule_chain {Rule : List VExpr → VExpr → Prop}
    (hpar : ∀ {xs ys rhs}, Rule xs rhs → List.Forall₂ (ParRed Γ) xs ys →
      ∃ rhs' X, Rule ys rhs' ∧ ParRed Γ rhs X ∧ NormalEq₀ Γ X rhs')
    (hnrm : ∀ {xs ys rhs}, Rule xs rhs → List.Forall₂ (NormalEq₀ Γ) xs ys →
      ∃ rhs', Rule ys rhs' ∧ NormalEq₀ Γ rhs rhs')
    (htyped : ∀ {xs rhs}, Rule xs rhs → ∀ x ∈ xs, ∃ T, Γ ⊢ x : T) :
    ∀ {pre xs ys rhs}, Rule (pre ++ xs) rhs → List.Forall₂ (ReflTransGen (Below Γ 2)) xs ys →
      ∃ rhs', Rule (pre ++ ys) rhs' ∧ ReflTransGen (Below Γ 2) rhs rhs' := by
  intro pre xs ys rhs H hc
  induction hc generalizing pre rhs with
  | nil => exact ⟨rhs, H, .rfl⟩
  | @cons x y xs ys hxy _ ih =>
    have step : ∀ {y'}, ReflTransGen (Below Γ 2) x y' →
        ∃ rhs', Rule (pre ++ y' :: xs) rhs' ∧ ReflTransGen (Below Γ 2) rhs rhs' := by
      intro y' hc'
      induction hc' with
      | rfl => exact ⟨rhs, H, .rfl⟩
      | @tail y₁ y₂ _ hst ih' =>
        obtain ⟨rhs₁, H₁, c₁⟩ := ih'
        obtain ⟨k, hk, hst⟩ := hst
        match k, hk, hst with
        | 0, _, hst =>
          have hrefl : ∀ z ∈ pre ++ xs, NormalEq₀ Γ z z := fun z hz => by
            have hz' : z ∈ pre ++ y₁ :: xs := by
              rcases List.mem_append.mp hz with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
            exact NormalEqF.refl (Exists.choose_spec (htyped H₁ z hz'))
          obtain ⟨rhs₂, H₂, e⟩ := hnrm H₁ (forall₂_update hrefl hst)
          exact ⟨rhs₂, H₂, c₁.tail ⟨0, by decide, e⟩⟩
        | 1, _, hst =>
          obtain ⟨rhs₂, X, H₂, pX, e⟩ := hpar H₁ (forall₂_update (fun _ _ => ParRed.rfl) hst)
          exact ⟨rhs₂, H₂, (c₁.tail ⟨1, by decide, pX⟩).tail ⟨0, by decide, e⟩⟩
        | k + 2, hk, _ => omega
    obtain ⟨rhs₁, H₁, c₁⟩ := step hxy
    obtain ⟨rhs₂, H₂, c₂⟩ := ih (pre := pre ++ [y]) (by simpa using H₁)
    exact ⟨rhs₂, by simpa using H₂, c₁.trans c₂⟩

theorem PrefixUnfold.chain (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels xs rhs)
    (hc : List.Forall₂ (ReflTransGen (Below Γ 2)) xs ys) :
    ∃ rhs', PrefixUnfold env univs recursorData Γ name levels ys rhs' ∧
      ReflTransGen (Below Γ 2) rhs rhs' := by
  have htyped : ∀ {xs rhs}, PrefixUnfold env univs recursorData Γ name levels xs rhs →
      ∀ x ∈ xs, ∃ T, Γ ⊢ x : T := fun H => by
    obtain ⟨_, hd⟩ := H.defeq henv hΓ
    exact HasType.mkApps_args_typed hΓ hd.hasType.1
  exact rule_chain (pre := [])
    (Rule := fun xs rhs => PrefixUnfold env univs recursorData Γ name levels xs rhs)
    (fun H h => H.congr_red ParRed.congrRel ParRed.argRel hΓ h)
    (fun H h => by
      obtain ⟨_, hd⟩ := H.defeq henv hΓ
      obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ hd.hasType.1
      obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
      exact H.congr₀ hΓ hw (VLevel.forall₂_equiv_refl _) h)
    htyped H hc

theorem QuotPrefixUnfold.chain (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels xs rhs)
    (hc : List.Forall₂ (ReflTransGen (Below Γ 2)) xs ys) :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels ys rhs' ∧ ReflTransGen (Below Γ 2) rhs rhs' := by
  have htyped : ∀ {xs rhs}, QuotPrefixUnfold env univs Γ levels xs rhs →
      ∀ x ∈ xs, ∃ T, Γ ⊢ x : T := fun H => by
    obtain ⟨_, hd⟩ := H.defeq henv hΓ
    exact HasType.mkApps_args_typed hΓ hd.hasType.1
  exact rule_chain (pre := [])
    (Rule := fun xs rhs => QuotPrefixUnfold env univs Γ levels xs rhs)
    (fun H h => H.congr_red ParRed.congrRel ParRed.argRel hΓ h)
    (fun H h => by
      obtain ⟨_, hd⟩ := H.defeq henv hΓ
      obtain ⟨_, hh⟩ := schema_mkApps_head_type hΓ hd.hasType.1
      obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
      exact H.congr₀ hΓ hw (VLevel.forall₂_equiv_refl _) h)
    htyped H hc

end DeltaPeakTools

section Join2Tools

theorem LevelStep.defeqDFC (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (H : LevelStep Γ₁ k a b) (ha : Γ₁ ⊢ a : A) :
    LevelStep Γ₂ k a b := by
  match k, H with
  | 0, H => exact NormalEqF.defeqDFC hΓ₀ W H
  | 1, H => exact ParRed.defeqDFC hΓ₀ W ha H
  | 2, H => exact DeltaPar.defeqDFC hΓ₀ W (H : DeltaPar _ _ _) ha
  | 3, H => exact EtaPar.defeqDFC hΓ₀ W (H : EtaPar _ _ _) ha
  | _ + 4, H => exact H.elim

theorem Below.defeqDFC (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (H : ReflTransGen (Below Γ₁ n) a b) (ha : Γ₁ ⊢ a : A) :
    ReflTransGen (Below Γ₂ n) a b :=
  Below.congr (f := id) (P := fun x => Γ₁ ⊢ x : A)
    (fun hP h => h.defeqDFC hΓ₀ W hP) (fun hP h => h.hasType (W.isType' hΓ₀) hP) H ha

omit [Params] in
theorem exists_spine : ∀ e : VExpr, ∃ h args, e = VExpr.mkApps h args ∧ ∀ f x, h ≠ .app f x
  | .app f x => by
    obtain ⟨h, args, rfl, hh⟩ := exists_spine f
    exact ⟨h, args ++ [x], (VExpr.mkApps_snoc ..).symm, hh⟩
  | .bvar i => ⟨_, [], rfl, nofun⟩
  | .sort u => ⟨_, [], rfl, nofun⟩
  | .const c ls => ⟨_, [], rfl, nofun⟩
  | .elim b o ls => ⟨_, [], rfl, nofun⟩
  | .proj s i m => ⟨_, [], rfl, nofun⟩
  | .lam A b => ⟨_, [], rfl, nofun⟩
  | .forallE A b => ⟨_, [], rfl, nofun⟩

/-- A singleton or quotient prefix rule at a constant spine. -/
def SpineRule (Γ : List VExpr) (name : Name) (ls : List VLevel) (xs : List VExpr) (rhs : VExpr) :
    Prop :=
  PrefixUnfold env univs recursorData Γ name ls xs rhs ∨
    (name = ``Quot.lift ∧ QuotPrefixUnfold env univs Γ ls xs rhs)

theorem SpineRule.step (hs : List.Forall₂ (DeltaPar Γ) xs ys) (hr : SpineRule Γ name ls ys rhs) :
    DeltaPar Γ (VExpr.mkApps (.const name ls) xs) rhs := by
  have ⟨hl, hx⟩ := getElem_of_forall₂ hs
  rcases hr with hr | ⟨rfl, hr⟩
  · exact .delta hl hx hr
  · exact .quotDelta hl hx hr

theorem SpineRule.unique (H : SpineRule Γ name ls xs rhs) (H' : SpineRule Γ name ls xs rhs') :
    rhs = rhs' := by
  rcases H with H | ⟨rfl, H⟩ <;> rcases H' with H' | ⟨h, H'⟩
  · exact H.unique H'
  · subst h; obtain ⟨_, hd, _⟩ := H.length_le; rw [recursorData_quot H'.registered] at hd; cases hd
  · obtain ⟨_, hd, _⟩ := H'.length_le; rw [recursorData_quot H.registered] at hd; cases hd
  · exact H.unique H'

theorem SpineRule.defeq (hΓ : OnCtx Γ (env.IsType univs)) (H : SpineRule Γ name ls xs rhs) :
    Γ ⊢ VExpr.mkApps (.const name ls) xs ≡ rhs := by
  rcases H with H | ⟨rfl, H⟩
  · exact H.defeq henv hΓ
  · exact H.defeq henv hΓ

theorem SpineRule.congr_defeq (hΓ : OnCtx Γ (env.IsType univs)) (H : SpineRule Γ name ls xs rhs)
    (ha : List.Forall₂ (IsDefEqU env univs Γ) xs ys) : ∃ rhs', SpineRule Γ name ls ys rhs' := by
  rcases H with H | ⟨rfl, H⟩
  · obtain ⟨_, h⟩ := H.congr_defeq hΓ ha; exact ⟨_, .inl h⟩
  · obtain ⟨_, h⟩ := H.congr_defeq hΓ ha; exact ⟨_, .inr ⟨rfl, h⟩⟩

theorem SpineRule.congr_delta (hΓ : OnCtx Γ (env.IsType univs)) (H : SpineRule Γ name ls xs rhs)
    (ha : List.Forall₂ (DeltaPar Γ) xs ys) :
    ∃ rhs' X, SpineRule Γ name ls ys rhs' ∧ DeltaPar Γ rhs X ∧ NormalEq₀ Γ X rhs' := by
  rcases H with H | ⟨rfl, H⟩
  · obtain ⟨_, _, h, h1, h2⟩ := H.congr_red DeltaPar.congrRel DeltaPar.argRel hΓ ha
    exact ⟨_, _, .inl h, h1, h2⟩
  · obtain ⟨_, _, h, h1, h2⟩ := H.congr_red DeltaPar.congrRel DeltaPar.argRel hΓ ha
    exact ⟨_, _, .inr ⟨rfl, h⟩, h1, h2⟩

theorem SpineRule.chain (hΓ : OnCtx Γ (env.IsType univs)) (H : SpineRule Γ name ls xs rhs)
    (hc : List.Forall₂ (ReflTransGen (Below Γ 2)) xs ys) :
    ∃ rhs', SpineRule Γ name ls ys rhs' ∧ ReflTransGen (Below Γ 2) rhs rhs' := by
  rcases H with H | ⟨rfl, H⟩
  · obtain ⟨_, h, c⟩ := H.chain hΓ hc; exact ⟨_, .inl h, c⟩
  · obtain ⟨_, h, c⟩ := H.chain hΓ hc; exact ⟨_, .inr ⟨rfl, h⟩, c⟩

theorem SpineRule.supply_many (H₁ : SpineRule Γ name ls xs r₁)
    (H₂ : SpineRule Γ name ls (xs ++ more) r₂) :
    ReflTransGen (ParRed Γ) (VExpr.mkApps r₁ more) r₂ := by
  rcases H₁ with H₁ | ⟨rfl, H₁⟩ <;> rcases H₂ with H₂ | ⟨h, H₂⟩
  · exact H₁.supply_many H₂
  · subst h; obtain ⟨_, hd, _⟩ := H₁.length_le; rw [recursorData_quot H₂.registered] at hd; cases hd
  · obtain ⟨_, hd, _⟩ := H₂.length_le; rw [recursorData_quot H₁.registered] at hd; cases hd
  · exact H₁.supply_many H₂

/-- Two developments each extended by one parallel prefix step meet after
lower steps. -/
def Join2 (Γ : List VExpr) (b c : VExpr) : Prop :=
  ∃ d, (∃ b₁, DeltaPar Γ b b₁ ∧ ReflTransGen (Below Γ 2) b₁ d) ∧
    (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d)

theorem Join2.app (hΓ : OnCtx Γ (env.IsType univs)) (hf : Join2 Γ f₁ f₂) (hx : Join2 Γ x₁ x₂)
    (h₁ : Γ ⊢ .app f₁ x₁ : T) (h₂ : Γ ⊢ .app f₂ x₂ : T) : Join2 Γ (.app f₁ x₁) (.app f₂ x₂) := by
  obtain ⟨df, ⟨F₁, pF₁, cF₁⟩, ⟨F₂, pF₂, cF₂⟩⟩ := hf
  obtain ⟨dx, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hx
  have s₁ : DeltaPar Γ (.app f₁ x₁) (.app F₁ X₁) := .app pF₁ pX₁
  have s₂ : DeltaPar Γ (.app f₂ x₂) (.app F₂ X₂) := .app pF₂ pX₂
  exact ⟨_, ⟨_, s₁, Below.app hΓ cF₁ cX₁ ((DeltaPar.full s₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.app hΓ cF₂ cX₂ ((DeltaPar.full s₂).hasType hΓ h₂)⟩⟩

theorem Join2.proj (hΓ : OnCtx Γ (env.IsType univs)) (hm : Join2 Γ m₁ m₂)
    (h₁ : Γ ⊢ .proj s i m₁ : T) (h₂ : Γ ⊢ .proj s i m₂ : T) :
    Join2 Γ (.proj s i m₁) (.proj s i m₂) := by
  obtain ⟨dm, ⟨M₁, pM₁, cM₁⟩, ⟨M₂, pM₂, cM₂⟩⟩ := hm
  have s₁ : DeltaPar Γ (.proj s i m₁) (.proj s i M₁) := .proj pM₁
  have s₂ : DeltaPar Γ (.proj s i m₂) (.proj s i M₂) := .proj pM₂
  exact ⟨_, ⟨_, s₁, Below.proj hΓ cM₁ ((DeltaPar.full s₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.proj hΓ cM₂ ((DeltaPar.full s₂).hasType hΓ h₂)⟩⟩


omit [Params] in
theorem List.forall₂_snoc_right {P Q : α → α → Prop} :
    ∀ {l E}, List.Forall₂ (fun y e => ∃ y', P y y' ∧ Q y' e) l E →
      ∃ B, List.Forall₂ P l B ∧ List.Forall₂ Q B E
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons ⟨y', h1, h2⟩ t =>
    let ⟨B, hB, hE⟩ := List.forall₂_snoc_right t
    ⟨y' :: B, .cons h1 hB, .cons h2 hE⟩

omit [Params] in
theorem forall₂_eq_imp : ∀ {l l' : List α}, List.Forall₂ Eq l l' → l = l'
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons rfl t => by rw [forall₂_eq_imp t]

/-- The side of a constant-spine peak that contracted at prefix `k`. -/
theorem DeltaPar.side_contr {X Y E : List VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (hrule : SpineRule Γ name ls (X.take k) r) (hX : List.Forall₂ (DeltaPar Γ) X Y)
    (hYE : List.Forall₂ (ReflTransGen (Below Γ 2)) Y E)
    (hb : Γ ⊢ VExpr.mkApps r (X.drop k) : T) :
    ∃ rE, SpineRule Γ name ls (E.take k) rE ∧
      ∃ b₁, DeltaPar Γ (VExpr.mkApps r (X.drop k)) b₁ ∧
        ReflTransGen (Below Γ 2) b₁ (VExpr.mkApps rE (E.drop k)) := by
  obtain ⟨rY, X₁, hrY, pX, eX⟩ := hrule.congr_delta hΓ (List.forall₂_take hX k)
  obtain ⟨rE, hrE, cE⟩ := hrY.chain hΓ (List.forall₂_take hYE k)
  refine ⟨rE, hrE, _, DeltaPar.mkApps pX (Lean4Lean.List.forall₂_drop hX k), ?_⟩
  have hstep : DeltaPar Γ (VExpr.mkApps r (X.drop k)) (VExpr.mkApps X₁ (Y.drop k)) :=
    DeltaPar.mkApps pX (Lean4Lean.List.forall₂_drop hX k)
  have h1 := (DeltaPar.full hstep).hasType hΓ hb
  have tX₁ : ∃ T, Γ ⊢ X₁ : T := schema_mkApps_head_type hΓ h1
  have hrY' := hrY.defeq hΓ
  obtain ⟨_, tX₁⟩ := tX₁
  have e₁ : ReflTransGen (Below Γ 2) X₁ rY := .tail .rfl ⟨0, by decide, eX⟩
  exact Below.mkApps hΓ (e₁.trans cE) (Lean4Lean.List.forall₂_drop hYE k) h1

/-- The side of a constant-spine peak that only developed its arguments, contracting
at the prefix chosen by the other side. -/
theorem DeltaPar.side_cong {Z X Y E : List VExpr} (hΓ : OnCtx Γ (env.IsType univs))
    (hrule : SpineRule Γ name ls (Z.take k) rZ)
    (hdef : List.Forall₂ (IsDefEqU env univs Γ) (Z.take k) (Y.take k))
    (hX : List.Forall₂ (DeltaPar Γ) X Y)
    (hYE : List.Forall₂ (ReflTransGen (Below Γ 2)) Y E)
    (hb : Γ ⊢ VExpr.mkApps (.const name ls) X : T) :
    ∃ rE, SpineRule Γ name ls (E.take k) rE ∧
      ∃ b₁, DeltaPar Γ (VExpr.mkApps (.const name ls) X) b₁ ∧
        ReflTransGen (Below Γ 2) b₁ (VExpr.mkApps rE (E.drop k)) := by
  obtain ⟨rY, hrY⟩ := hrule.congr_defeq hΓ hdef
  obtain ⟨rE, hrE, cE⟩ := hrY.chain hΓ (List.forall₂_take hYE k)
  have hstep : DeltaPar Γ (VExpr.mkApps (.const name ls) X) (VExpr.mkApps rY (Y.drop k)) := by
    rw [← List.take_append_drop k X, VExpr.mkApps_append]
    exact DeltaPar.mkApps (hrY.step (List.forall₂_take hX k)) (Lean4Lean.List.forall₂_drop hX k)
  refine ⟨rE, hrE, _, hstep, ?_⟩
  exact Below.mkApps hΓ cE (Lean4Lean.List.forall₂_drop hYE k) ((DeltaPar.full hstep).hasType hΓ hb)

/-- Extending a prefix contraction by beta reduction to a longer prefix. -/
theorem DeltaPar.side_extend {E : List VExpr} {k₁ k₂ : Nat}
    (hk : k₁ ≤ k₂)
    (H₁ : SpineRule Γ name ls (E.take k₁) r₁) (H₂ : SpineRule Γ name ls (E.take k₂) r₂) :
    ReflTransGen (Below Γ 2) (VExpr.mkApps r₁ (E.drop k₁)) (VExpr.mkApps r₂ (E.drop k₂)) := by
  have he : E.take k₂ = E.take k₁ ++ (E.drop k₁).take (k₂ - k₁) := by
    rw [List.take_drop]; rw [show k₁ + (k₂ - k₁) = k₂ by omega]
    exact (List.take_append_drop k₁ (E.take k₂) |>.symm.trans (by
      rw [List.take_take, Nat.min_eq_left hk, List.drop_take]))
  rw [he] at H₂
  have hs := H₁.supply_many H₂
  have hd : E.drop k₁ = (E.drop k₁).take (k₂ - k₁) ++ E.drop k₂ := by
    have := List.take_append_drop (k₂ - k₁) (E.drop k₁)
    rw [List.drop_drop] at this
    first
      | rw [show k₁ + (k₂ - k₁) = k₂ by omega] at this; exact this.symm
      | rw [show k₂ - k₁ + k₁ = k₂ by omega] at this; exact this.symm
  rw [hd, VExpr.mkApps_append]
  exact Below.ofParRedS (ParRedS.mkApps_head hs _) (by decide)

theorem Join2.lam (hΓ : OnCtx Γ (env.IsType univs)) (tD : Γ ⊢ D : .sort u)
    (hD : Join2 Γ D₁ D₂) (ht : Join2 (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (h₁ : Γ ⊢ .lam D₁ t₁ : T₁) (h₂ : Γ ⊢ .lam D₂ t₂ : T₂) :
    Join2 Γ (.lam D₁ t₁) (.lam D₂ t₂) := by
  obtain ⟨dD, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hD
  obtain ⟨dt, ⟨S₁, pS₁, cS₁⟩, ⟨S₂, pS₂, cS₂⟩⟩ := ht
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have tS₁ := (DeltaPar.full pS₁).hasType hΓD tt₁
  have tS₂ := (DeltaPar.full pS₂).hasType hΓD tt₂
  have eX₁ := e₁.trans ((DeltaPar.full pX₁).defeq hΓ e₁.hasType.2)
  have eX₂ := e₂.trans ((DeltaPar.full pX₂).defeq hΓ e₂.hasType.2)
  have s₁ : DeltaPar Γ (.lam D₁ t₁) (.lam X₁ S₁) := .lam pX₁ (pS₁.defeqDFC hΓ (.succ .zero e₁) tt₁)
  have s₂ : DeltaPar Γ (.lam D₂ t₂) (.lam X₂ S₂) := .lam pX₂ (pS₂.defeqDFC hΓ (.succ .zero e₂) tt₂)
  exact ⟨_, ⟨_, s₁, Below.lam hΓ cX₁ (Below.defeqDFC hΓ (.succ .zero eX₁) cS₁ tS₁)
      ((DeltaPar.full s₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.lam hΓ cX₂ (Below.defeqDFC hΓ (.succ .zero eX₂) cS₂ tS₂)
      ((DeltaPar.full s₂).hasType hΓ h₂)⟩⟩

theorem Join2.forallE (hΓ : OnCtx Γ (env.IsType univs)) (tD : Γ ⊢ D : .sort u)
    (hD : Join2 Γ D₁ D₂) (ht : Join2 (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (h₁ : Γ ⊢ .forallE D₁ t₁ : T₁) (h₂ : Γ ⊢ .forallE D₂ t₂ : T₂) :
    Join2 Γ (.forallE D₁ t₁) (.forallE D₂ t₂) := by
  obtain ⟨dD, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hD
  obtain ⟨dt, ⟨S₁, pS₁, cS₁⟩, ⟨S₂, pS₂, cS₂⟩⟩ := ht
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have tS₁ := (DeltaPar.full pS₁).hasType hΓD tt₁
  have tS₂ := (DeltaPar.full pS₂).hasType hΓD tt₂
  have eX₁ := e₁.trans ((DeltaPar.full pX₁).defeq hΓ e₁.hasType.2)
  have eX₂ := e₂.trans ((DeltaPar.full pX₂).defeq hΓ e₂.hasType.2)
  have s₁ : DeltaPar Γ (.forallE D₁ t₁) (.forallE X₁ S₁) :=
    .forallE pX₁ (pS₁.defeqDFC hΓ (.succ .zero e₁) tt₁)
  have s₂ : DeltaPar Γ (.forallE D₂ t₂) (.forallE X₂ S₂) :=
    .forallE pX₂ (pS₂.defeqDFC hΓ (.succ .zero e₂) tt₂)
  exact ⟨_, ⟨_, s₁, Below.forallE hΓ cX₁ (Below.defeqDFC hΓ (.succ .zero eX₁) cS₁ tS₁)
      ((DeltaPar.full s₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.forallE hΓ cX₂ (Below.defeqDFC hΓ (.succ .zero eX₂) cS₂ tS₂)
      ((DeltaPar.full s₂).hasType hΓ h₂)⟩⟩

/-- Peaks of parallel prefix steps below a size. -/
abbrev DDBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → DeltaPar Γ a b → DeltaPar Γ a c →
    Γ ⊢ a : A → Join2 Γ b c

theorem DeltaPar.join_args (hΓ : OnCtx Γ (env.IsType univs)) (IH : DDBelow s)
    (hsub : ∀ x ∈ args, sizeOf x < s) (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h₁ : List.Forall₂ (DeltaPar Γ) args args₁) (h₂ : List.Forall₂ (DeltaPar Γ) args args₂) :
    ∃ B C E, List.Forall₂ (DeltaPar Γ) args₁ B ∧ List.Forall₂ (ReflTransGen (Below Γ 2)) B E ∧
      List.Forall₂ (DeltaPar Γ) args₂ C ∧ List.Forall₂ (ReflTransGen (Below Γ 2)) C E := by
  obtain ⟨us, vs, hus, hvs, heq⟩ := List.Forall₂.exists_join
    (S := fun y e => ∃ y', DeltaPar Γ y y' ∧ ReflTransGen (Below Γ 2) y' e)
    (T := fun z e => ∃ z', DeltaPar Γ z z' ∧ ReflTransGen (Below Γ 2) z' e) (U := Eq) h₁ h₂
    fun x _ _ hx p q => by
      obtain ⟨d, hb, hc⟩ := IH (hsub x hx) hΓ p q (htyped x hx).choose_spec
      exact ⟨d, d, hb, hc, rfl⟩
  cases forall₂_eq_imp heq
  obtain ⟨B, hB, hBE⟩ := List.forall₂_snoc_right hus
  obtain ⟨C, hC, hCE⟩ := List.forall₂_snoc_right hvs
  exact ⟨B, C, us, hB, hBE, hC, hCE⟩

theorem forall₂_defeq_trans (hΓ : OnCtx Γ (env.IsType univs))
    (H₁ : List.Forall₂ (IsDefEqU env univs Γ) l₁ l₂) (H₂ : List.Forall₂ (IsDefEqU env univs Γ) l₂ l₃) :
    List.Forall₂ (IsDefEqU env univs Γ) l₁ l₃ :=
  Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans henv hΓ h') H₁ H₂

theorem forall₂_defeq_symm (H : List.Forall₂ (IsDefEqU env univs Γ) l₁ l₂) :
    List.Forall₂ (IsDefEqU env univs Γ) l₂ l₁ :=
  Lean4Lean.List.Forall₂.imp (fun _ _ h => IsDefEqU.symm h) (Lean4Lean.List.Forall₂.flip H)

theorem forall₂_deltaPar_defeq (hΓ : OnCtx Γ (env.IsType univs))
    (htyped : ∀ x ∈ l, ∃ T, Γ ⊢ x : T) (H : List.Forall₂ (DeltaPar Γ) l l') :
    List.Forall₂ (IsDefEqU env univs Γ) l l' :=
  forall₂_defeq_of_rel (fun h ht => (DeltaPar.full h).defeq hΓ ht) htyped H

theorem forall₂_typed_of_deltaPar (hΓ : OnCtx Γ (env.IsType univs))
    (htyped : ∀ x ∈ l, ∃ T, Γ ⊢ x : T) (H : List.Forall₂ (DeltaPar Γ) l l') :
    ∀ x ∈ l', ∃ T, Γ ⊢ x : T := by
  have := forall₂_deltaPar_defeq hΓ htyped H
  intro x hx
  obtain ⟨y, _, ⟨_, h⟩⟩ := Lean4Lean.List.Forall₂.forall_exists_r this x hx
  exact ⟨_, h.hasType.2⟩

theorem DeltaPar.peak_spine (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DDBelow (sizeOf (VExpr.mkApps (.const name ls) args)))
    (ha : Γ ⊢ VExpr.mkApps (.const name ls) args : A)
    (H1 : DeltaPar Γ (VExpr.mkApps (.const name ls) args) b)
    (H2 : DeltaPar Γ (VExpr.mkApps (.const name ls) args) c) : Join2 Γ b c := by
  have hb := (DeltaPar.full H1).hasType hΓ ha
  have hc := (DeltaPar.full H2).hasType hΓ ha
  obtain ⟨args₁, h₁, cb⟩ := DeltaPar.const_spine_cases H1
  obtain ⟨args₂, h₂, cc⟩ := DeltaPar.const_spine_cases H2
  have targs := HasType.mkApps_args_typed hΓ ha
  obtain ⟨B, C, E, hB, hBE, hC, hCE⟩ := DeltaPar.join_args hΓ IH
    (fun _ hx => sizeOf_mkApps_arg hx) targs h₁ h₂
  have targs₁ := forall₂_typed_of_deltaPar hΓ targs h₁
  have targs₂ := forall₂_typed_of_deltaPar hΓ targs h₂
  have d₁ := forall₂_deltaPar_defeq hΓ targs h₁
  have d₂ := forall₂_deltaPar_defeq hΓ targs h₂
  have dB := forall₂_deltaPar_defeq hΓ targs₁ hB
  have dC := forall₂_deltaPar_defeq hΓ targs₂ hC
  -- definitional equality between the two developments of the arguments
  have d₂B : List.Forall₂ (IsDefEqU env univs Γ) args₂ B :=
    forall₂_defeq_trans hΓ (forall₂_defeq_trans hΓ (forall₂_defeq_symm d₂) d₁) dB
  have d₁C : List.Forall₂ (IsDefEqU env univs Γ) args₁ C :=
    forall₂_defeq_trans hΓ (forall₂_defeq_trans hΓ (forall₂_defeq_symm d₁) d₂) dC
  rcases cb with rfl | ⟨k₁, r₁, hk₁, hr₁, rfl⟩ <;> rcases cc with rfl | ⟨k₂, r₂, hk₂, hr₂, rfl⟩
  · have s₁ := DeltaPar.mkApps_args (f := .const name ls) hB
    have s₂ := DeltaPar.mkApps_args (f := .const name ls) hC
    exact ⟨_, ⟨_, s₁, Below.mkApps hΓ .rfl hBE ((DeltaPar.full s₁).hasType hΓ hb)⟩,
      ⟨_, s₂, Below.mkApps hΓ .rfl hCE ((DeltaPar.full s₂).hasType hΓ hc)⟩⟩
  · obtain ⟨rE, hrE, b₁, pb, cb⟩ := DeltaPar.side_cong hΓ hr₂ (List.forall₂_take d₂B k₂) hB hBE hb
    obtain ⟨rE', hrE', c₁, pc, cc⟩ := DeltaPar.side_contr hΓ hr₂ hC hCE hc
    cases hrE.unique hrE'
    exact ⟨_, ⟨_, pb, cb⟩, ⟨_, pc, cc⟩⟩
  · obtain ⟨rE, hrE, b₁, pb, cb⟩ := DeltaPar.side_contr hΓ hr₁ hB hBE hb
    obtain ⟨rE', hrE', c₁, pc, cc⟩ := DeltaPar.side_cong hΓ hr₁ (List.forall₂_take d₁C k₁) hC hCE hc
    cases hrE.unique hrE'
    exact ⟨_, ⟨_, pb, cb⟩, ⟨_, pc, cc⟩⟩
  · obtain ⟨rE₁, hrE₁, b₁, pb, cb⟩ := DeltaPar.side_contr hΓ hr₁ hB hBE hb
    obtain ⟨rE₂, hrE₂, c₁, pc, cc⟩ := DeltaPar.side_contr hΓ hr₂ hC hCE hc
    rcases Nat.le_total k₁ k₂ with hk | hk
    · exact ⟨_, ⟨_, pb, cb.trans (DeltaPar.side_extend hk hrE₁ hrE₂)⟩, ⟨_, pc, cc⟩⟩
    · exact ⟨_, ⟨_, pb, cb⟩, ⟨_, pc, cc.trans (DeltaPar.side_extend hk hrE₂ hrE₁)⟩⟩

omit [Params] in
theorem mkApps_const_ne_proj : VExpr.mkApps (.const n ls) args ≠ .proj s i m := by
  rcases eq_nil_or_snoc' args with rfl | ⟨l, a, rfl⟩
  · intro h; cases h
  · rw [VExpr.mkApps_snoc]; intro h; cases h

theorem Join2.symm (H : Join2 Γ b c) : Join2 Γ c b :=
  let ⟨d, h1, h2⟩ := H; ⟨d, h2, h1⟩

theorem DeltaPar.peak_cong_iota (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DDBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A)
    (hm₁ : DeltaPar Γ (VExpr.mkApps (.const info.ctorName ls) args) m₁)
    (hlen : args.length = args₂.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args₂.length), DeltaPar Γ args[i] args₂[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args₂) : fieldType)
    (hi : args₂[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType) :
    Join2 Γ (.proj family index m₁) field := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
  obtain ⟨args₁, rfl, h₁⟩ := DeltaPar.rigid_spine (projection_ctor_rigid hl) hm₁
  have h₂ := List.forall₂_of_getElem hlen hargs
  have hb := (DeltaPar.full (.proj hm₁)).hasType hΓ ha
  have hc := (DeltaPar.full (.projIota hlen hargs hl hs hi ht)).hasType hΓ ha
  have targs := HasType.mkApps_args_typed hΓ lm.hasType.2
  obtain ⟨B, C, E, hB, hBE, hC, hCE⟩ := DeltaPar.join_args hΓ IH
    (fun _ hx => by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hx; simp; omega)
    targs h₁ h₂
  have targs₁ := forall₂_typed_of_deltaPar hΓ targs h₁
  have targs₂ := forall₂_typed_of_deltaPar hΓ targs h₂
  have d₁ := forall₂_deltaPar_defeq hΓ targs h₁
  have d₂ := forall₂_deltaPar_defeq hΓ targs h₂
  have dB := forall₂_deltaPar_defeq hΓ targs₁ hB
  have d₂B : List.Forall₂ (IsDefEqU env univs Γ) args₂ B :=
    forall₂_defeq_trans hΓ (forall₂_defeq_trans hΓ (forall₂_defeq_symm d₂) d₁) dB
  obtain ⟨bk, hbk, ebk⟩ := forall₂_getElem?_left d₂B hi
  obtain ⟨ek, hek, cbk⟩ := forall₂_getElem?_left hBE hbk
  obtain ⟨ck, hck, pck⟩ := forall₂_getElem?_left hC hi
  obtain ⟨ek', hek', cck⟩ := forall₂_getElem?_left hCE hck
  cases hek.symm.trans hek'
  have hcong : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args₁))
      (.proj family index (VExpr.mkApps (.const info.ctorName ls) B)) :=
    .proj (DeltaPar.mkApps_args hB)
  have hT := (DeltaPar.full hcong).hasType hΓ hb
  have hbkT := hc.defeqU_l henv hΓ ebk
  have ⟨hl₂, hx₂⟩ := getElem_of_forall₂ hB
  exact ⟨ek, ⟨bk, .projIota hl₂ hx₂ hl hT hbk hbkT, cbk⟩, ⟨ck, pck, cck⟩⟩

theorem DeltaPar.peak_iota (hΓ : OnCtx Γ (env.IsType univs))
    (IH : DDBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A)
    (hlen : args.length = args₁.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args₁.length), DeltaPar Γ args[i] args₁[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args₁) : fieldType)
    (hi : args₁[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (H2 : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) c) :
    Join2 Γ field c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
  generalize hE : VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args) = E at H2
  cases H2 with
  | proj hm₂ =>
    cases hE
    exact (DeltaPar.peak_cong_iota hΓ IH ha hm₂ hlen hargs hl hs hi ht).symm
  | projIota hlen' hargs' hl' hs' hi' ht' =>
    injection hE with hf hidx hM
    subst hf hidx
    obtain ⟨hc', rfl, rfl⟩ := VExpr.mkApps_const_inj hM
    cases henv.ordered.projections_unique hl hl'
    have targs := HasType.mkApps_args_typed hΓ lm.hasType.2
    have h₁ := List.forall₂_of_getElem hlen hargs
    have h₂ := List.forall₂_of_getElem hlen' hargs'
    obtain ⟨x, hx, hx₁⟩ := forall₂_getElem?_right h₁ hi
    obtain ⟨y, hy, hy₂⟩ := forall₂_getElem?_left h₂ hx
    rw [hi'] at hy
    cases hy
    have hxmem : x ∈ args := List.mem_of_getElem? hx
    exact IH (by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hxmem; simp; omega)
      hΓ hx₁ hy₂ (targs x hxmem).choose_spec
  | delta => exact absurd hE.symm mkApps_const_ne_proj
  | quotDelta => exact absurd hE.symm mkApps_const_ne_proj
  | _ => cases hE

theorem DeltaPar.app_inv_head (hh : ∀ c ls, h ≠ .const c ls) (hh' : ∀ f x, h ≠ .app f x)
    (H : DeltaPar Γ (.app (VExpr.mkApps h as) x) out) :
    ∃ f' x', out = .app f' x' ∧ DeltaPar Γ (VExpr.mkApps h as) f' ∧ DeltaPar Γ x x' := by
  generalize hE : VExpr.app (VExpr.mkApps h as) x = E at H
  have hhead : ∀ c ls args, VExpr.mkApps (.const c ls) args ≠ E := by
    intro c ls args he
    have := congrArg (fun e => (VExpr.getAppFnArgs e).1) (he.trans hE.symm)
    rw [← VExpr.mkApps_snoc] at this
    simp only [InductiveSignature.spine_mkApps_exact (VExpr.const c ls) _ rfl] at this
    rw [InductiveSignature.spine_mkApps_exact h _ (by
      cases h <;> first | rfl | exact absurd rfl (hh' _ _))] at this
    exact hh _ _ this.symm
  cases H with
  | app hf hx => cases hE; exact ⟨_, _, rfl, hf, hx⟩
  | delta => exact (hhead _ _ _ rfl).elim
  | quotDelta => exact (hhead _ _ _ rfl).elim
  | _ => cases hE

theorem DeltaPar.forallE_inv (H : DeltaPar Γ (.forallE A t) X) :
    ∃ A' t', DeltaPar Γ A A' ∧ DeltaPar (A :: Γ) t t' ∧ X = .forallE A' t' := by
  generalize he : VExpr.forallE A t = src at H
  cases H with
  | forallE h1 h2 => cases he; exact ⟨_, _, h1, h2, rfl⟩
  | delta => exact absurd he.symm VExpr.mkApps_const_ne_forallE
  | quotDelta => exact absurd he.symm VExpr.mkApps_const_ne_forallE
  | _ => cases he

theorem DeltaPar.atom_inv (hh : ∀ c ls, h ≠ .const c ls) (hh₁ : ∀ f x, h ≠ .app f x)
    (hh₂ : ∀ s i m, h ≠ .proj s i m) (hh₃ : ∀ A t, h ≠ .lam A t) (hh₄ : ∀ A t, h ≠ .forallE A t)
    (H : DeltaPar Γ h X) : X = h := by
  cases H with
  | bvar | sort | const | elim => rfl
  | app => exact absurd rfl (hh₁ _ _)
  | proj => exact absurd rfl (hh₂ _ _ _)
  | lam => exact absurd rfl (hh₃ _ _)
  | forallE => exact absurd rfl (hh₄ _ _)
  | @delta _ name ls rhs args args' _ _ _ =>
    rcases eq_nil_or_snoc' args with rfl | ⟨l, a, rfl⟩
    · exact absurd rfl (hh _ _)
    · exact absurd (VExpr.mkApps_snoc ..) (hh₁ _ _)
  | @quotDelta _ ls rhs args args' _ _ _ =>
    rcases eq_nil_or_snoc' args with rfl | ⟨l, a, rfl⟩
    · exact absurd rfl (hh _ _)
    · exact absurd (VExpr.mkApps_snoc ..) (hh₁ _ _)
  | projIota => exact absurd rfl (hh₂ _ _ _)

theorem DeltaPar.peak_aux : ∀ n, DDBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H1 H2 ha
  have hb := (DeltaPar.full H1).hasType hΓ ha
  have hc := (DeltaPar.full H2).hasType hΓ ha
  by_cases hprop : Γ ⊢ A : .sort .zero
  · exact ⟨c, ⟨b, .rfl, .tail .rfl ⟨0, by decide, .proofIrrel hprop hb hc⟩⟩, ⟨c, .rfl, .rfl⟩⟩
  have IH : DDBelow (sizeOf a) := fun h => ih (by omega)
  obtain ⟨h, as, rfl, hh⟩ := exists_spine a
  rcases eq_nil_or_snoc' as with rfl | ⟨as₀, x, rfl⟩
  · change Γ ⊢ h : A at ha
    change DeltaPar Γ h b at H1
    change DeltaPar Γ h c at H2
    change DDBelow (sizeOf h) at IH
    cases h with
    | const name ls => exact DeltaPar.peak_spine (args := []) hΓ IH ha H1 H2
    | app => exact absurd rfl (hh _ _)
    | proj s i m =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      generalize hE : VExpr.proj s i m = E at H1
      cases H1 with
      | proj hm₁ =>
        cases hE
        generalize hE₂ : VExpr.proj s i m = E₂ at H2
        cases H2 with
        | proj hm₂ =>
          cases hE₂
          exact Join2.proj hΓ (IH (by simp; omega) hΓ hm₁ hm₂ lm.hasType.2) hb hc
        | projIota hlen hargs hl hs hi ht =>
          injection hE₂ with hf hidx hM
          subst hf hidx hM
          exact DeltaPar.peak_cong_iota hΓ IH ha hm₁ hlen hargs hl hs hi ht
        | delta => exact absurd hE₂.symm mkApps_const_ne_proj
        | quotDelta => exact absurd hE₂.symm mkApps_const_ne_proj
        | _ => cases hE₂
      | projIota hlen hargs hl hs hi ht =>
        injection hE with hf hidx hM
        subst hf hidx hM
        exact DeltaPar.peak_iota hΓ IH ha hlen hargs hl hs hi ht H2
      | delta => exact absurd hE.symm mkApps_const_ne_proj
      | quotDelta => exact absurd hE.symm mkApps_const_ne_proj
      | _ => cases hE
    | lam D t =>
      obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨D₁, t₁, hD₁, ht₁, rfl⟩ := DeltaPar.lam_inv H1
      obtain ⟨D₂, t₂, hD₂, ht₂, rfl⟩ := DeltaPar.lam_inv H2
      exact Join2.lam hΓ tD (IH (by simp; omega) hΓ hD₁ hD₂ tD) (IH (by simp; omega) hΓ' ht₁ ht₂ tt)
        ((DeltaPar.full hD₁).defeq hΓ tD) ((DeltaPar.full hD₂).defeq hΓ tD)
        ((DeltaPar.full ht₁).hasType hΓ' tt) ((DeltaPar.full ht₂).hasType hΓ' tt) hb hc
    | forallE D t =>
      obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.forallE_inv henv
      have hΓ' : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨D₁, t₁, hD₁, ht₁, rfl⟩ := DeltaPar.forallE_inv H1
      obtain ⟨D₂, t₂, hD₂, ht₂, rfl⟩ := DeltaPar.forallE_inv H2
      exact Join2.forallE hΓ tD (IH (by simp; omega) hΓ hD₁ hD₂ tD)
        (IH (by simp; omega) hΓ' ht₁ ht₂ tt)
        ((DeltaPar.full hD₁).defeq hΓ tD) ((DeltaPar.full hD₂).defeq hΓ tD)
        ((DeltaPar.full ht₁).hasType hΓ' tt) ((DeltaPar.full ht₂).hasType hΓ' tt) hb hc
    | bvar | sort | elim =>
      rw [DeltaPar.atom_inv (by intros; intro h; cases h) (by intros; intro h; cases h)
        (by intros; intro h; cases h) (by intros; intro h; cases h) (by intros; intro h; cases h) H1,
        DeltaPar.atom_inv (by intros; intro h; cases h) (by intros; intro h; cases h)
        (by intros; intro h; cases h) (by intros; intro h; cases h) (by intros; intro h; cases h) H2]
      exact ⟨_, ⟨_, .rfl, .rfl⟩, ⟨_, .rfl, .rfl⟩⟩
  · by_cases hconst : ∃ c ls, h = .const c ls
    · obtain ⟨c, ls, rfl⟩ := hconst
      exact DeltaPar.peak_spine hΓ IH ha H1 H2
    · have hnc : ∀ c ls, h ≠ .const c ls := fun c ls he => hconst ⟨c, ls, he⟩
      rw [VExpr.mkApps_snoc] at ha H1 H2 IH
      obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
      obtain ⟨f₁, x₁, rfl, hf₁, hx₁⟩ := DeltaPar.app_inv_head hnc hh H1
      obtain ⟨f₂, x₂, rfl, hf₂, hx₂⟩ := DeltaPar.app_inv_head hnc hh H2
      exact Join2.app hΓ (IH (by simp; omega) hΓ hf₁ hf₂ tf) (IH (by simp; omega) hΓ hx₁ hx₂ tx) hb hc
end Join2Tools


section EtaTools

/-- A saturated structure constructor application has its structure type at
its own parameters and levels. -/
theorem HasType.ctorApp_type (hΓ : OnCtx Γ (env.IsType univs))
    (hinfo : env.projections S info)
    (H : Γ ⊢ VExpr.mkApps (.const info.ctorName ls) args : T)
    (hlen : args.length = info.nparams + info.numFields) :
    ∃ idx, Γ ⊢ T ≡ VExpr.mkApps (.const S ls) (args.take info.nparams ++ idx) := by
  obtain ⟨decl, type, ctor, _, _, hname, _, huvars, hnparams, _, _, hctorName, hctorType,
    _, hwf, _, Hraw, _⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  subst hname
  have hctor := henv.ordered.projectionConstructor hinfo
  rw [hctorType] at hshape harity
  have hlen' : args.length = doms.length := by
    rw [hlen, VProjectionInfo.numFields, harity]; omega
  have ⟨ci, hci, hls', hlenl⟩ :=
    (VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, H⟩).elim fun _ h => HasType.const_inv henv.ordered hΓ h
  rw [hctor] at hci
  cases Option.some.inj hci
  have hconst : Γ ⊢ .const info.ctorName ls : info.ctorType.instL ls := HasType.const hctor hls' hlenl
  have hT : (info.ctorType.instL ls).takeForalls args.length =
      some (doms.map (·.instL ls), result.instL ls) := by
    rw [hshape, VExpr.instL_wrapForalls,
      show args.length = (doms.map (·.instL ls)).length by simp [hlen']]
    exact VExpr.takeForalls_wrapForalls _ _
  obtain ⟨res, Hw, hres⟩ := HasType.mkApps_telescope henv hΓ hconst ⟨_, H⟩ hT
  have hresEq : res = (result.instL ls).instOuter args := by
    have := Hw
    rw [hshape, VExpr.instL_wrapForalls] at this
    exact this.wrapForalls_eq (by simp [hlen'])
  have hhead' : (result.instL ls).getAppFnArgs.1 = .const type.name ls := by
    rw [VExpr.getAppFnArgs_instL]
    show (result.getAppFnArgs.1.instL ls) = _
    rw [hhead]
    have hl : ls.length = decl.uvars := by rw [huvars]; exact hlenl
    simp [VExpr.instL, VLevel.params_map_inst ls hl]
  obtain ⟨idx, hresEq', -⟩ := (hvalid.instL ls).instOuter hhead' args (by omega)
  rw [hresEq', hnparams] at hresEq
  subst hresEq
  exact ⟨idx, H.uniqU henv hΓ hres⟩

/-- The selected field of a saturated structure constructor application has the
type of its projection. -/
theorem HasType.projIota_field (hΓ : OnCtx Γ (env.IsType univs))
    (hinfo : env.projections S info)
    (H : Γ ⊢ .proj S index (VExpr.mkApps (.const info.ctorName ls) args) : F)
    (hlen : args.length = info.nparams + info.numFields)
    (hk : args[info.nparams + index]? = some field) : Γ ⊢ field : F := by
  obtain ⟨decl, type, ctor, _, _, hname, _, huvars, hnparams, _, _, hctorName, hctorType,
    _, hwf, _, Hraw, _⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  subst hname
  have hctor := henv.ordered.projectionConstructor hinfo
  rw [hctorType] at hshape harity hwf
  rw [huvars] at hwf
  have hlen' : args.length = doms.length := by
    rw [hlen, VProjectionInfo.numFields, harity]; omega
  exact VProjectionInfo.field_typing_of_ctorApp henv hΓ hinfo hwf hctor hshape hvalid hhead
    hnparams huvars (hnparams ▸ hle) index H hlen' hk

theorem EtaPar.root_fun (hΓ : OnCtx Γ (env.IsType univs)) (HD : EtaPar Γ D D')
    (hc : Γ ⊢ c : .forallE D B) (hchain : ReflTransGen (Below Γ n) b₀ d₀)
    (hcd : EtaPar Γ c d₀) (hb : Γ ⊢ .lam D' (.app b₀.lift (.bvar 0)) : T) :
    ReflTransGen (Below Γ n) (.lam D' (.app b₀.lift (.bvar 0))) (.lam D' (.app d₀.lift (.bvar 0))) ∧
      EtaPar Γ c (.lam D' (.app d₀.lift (.bvar 0))) := by
  refine ⟨?_, .funEta hcd HD hc⟩
  obtain ⟨⟨_, tD'⟩, _, tbody⟩ := hb.lam_inv henv hΓ
  have hΓ' : OnCtx (D' :: Γ) (env.IsType univs) := ⟨hΓ, _, tD'⟩
  have hl := Below.weakN (Γ' := D' :: Γ) .one hchain
  exact Below.lam hΓ .rfl (Below.app hΓ' hl .rfl tbody) hb

theorem Below.expand (hΓ : OnCtx Γ (env.IsType univs))
    (hchain : ReflTransGen (Below Γ n) b₀ d₀)
    (hb : Γ ⊢ structExpand family info levels ps' b₀ : T) :
    ReflTransGen (Below Γ n) (structExpand family info levels ps' b₀)
        (structExpand family info levels ps' d₀) := by
  unfold VEnv.structExpand at hb ⊢
  refine Below.mkApps hΓ .rfl (List.Forall₂.append' (List.Forall₂.rfl fun _ _ => .rfl) ?_) hb
  apply List.forall₂_of_getElem (by simp)
  intro j hj hj'
  have hjmem : j ∈ List.range info.numFields := by simpa using hj
  obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ hb
    (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
  simpa only [List.getElem_map, List.getElem_range] using Below.proj hΓ hchain hpj

theorem EtaPar.root_struct (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.projections family info) (hp : ps.length = info.nparams) (hi : info.nindices = 0)
    (hlen : ps.length = ps'.length)
    (hps : ∀ i (h : i < ps.length) (h' : i < ps'.length), EtaPar Γ ps[i] ps'[i])
    (hc : Γ ⊢ c : VExpr.mkApps (.const family levels) ps)
    (hcexp : Γ ⊢ structExpand family info levels ps c : VExpr.mkApps (.const family levels) ps)
    (hchain : ReflTransGen (Below Γ n) b₀ d₀) (hcd : EtaPar Γ c d₀)
    (hb : Γ ⊢ structExpand family info levels ps' b₀ : T) :
    ReflTransGen (Below Γ n) (structExpand family info levels ps' b₀)
        (structExpand family info levels ps' d₀) ∧
      EtaPar Γ c (structExpand family info levels ps' d₀) := by
  refine ⟨?_, .structEta hcd hlen hps hl hp hi hc hcexp⟩
  unfold structExpand at hb ⊢
  refine Below.mkApps hΓ .rfl (List.Forall₂.append' (List.Forall₂.rfl fun _ _ => .rfl) ?_) hb
  apply List.forall₂_of_getElem (by simp)
  intro j hj hj'
  have hjmem : j ∈ List.range info.numFields := by simpa using hj
  obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ hb
    (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
  simpa only [List.getElem_map, List.getElem_range] using Below.proj hΓ hchain hpj

theorem pi_not_struct (hΓ : OnCtx Γ (env.IsType univs)) (hl : env.projections family info)
    (h1 : Γ ⊢ e : .forallE D B) (h2 : Γ ⊢ e : VExpr.mkApps (.const family levels) ps) : False := by
  have hu := h2.uniqU henv hΓ h1
  obtain ⟨_, hsort⟩ := h2.isType henv hΓ
  exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hl) hsort hu

theorem ParRed.eta_beta (y : VExpr) :
    ParRed Γ (.app (.lam A (.app e.lift (.bvar 0))) y) (.app e y) := by
  have := ParRed.beta (Γ := Γ) (A := A) (e₁ := .app e.lift (.bvar 0))
    (e₁' := .app e.lift (.bvar 0)) (e₂ := y) (e₂' := y) .rfl .rfl
  simpa [VExpr.inst, VExpr.inst_lift] using this

/-- Collapse eta expansions of a lambda in function position by beta. -/
theorem EtaPar.collapse_lam (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ (.lam D t) F) (ht : Γ ⊢ .lam D t : T) :
    ∃ D' t', EtaPar Γ D D' ∧ EtaPar (D :: Γ) t t' ∧
      ∀ y, ReflTransGen (ParRed Γ) (.app F y) (.app (.lam D' t') y) := by
  generalize hsrc : VExpr.lam D t = src at H ht
  induction H with
  | lam hD ht' => cases hsrc; exact ⟨_, _, hD, ht', fun _ => .rfl⟩
  | funEta H₀ HA hty ih =>
    subst hsrc
    obtain ⟨D', t', hD, ht', hy⟩ := ih hΓ rfl ht
    exact ⟨D', t', hD, ht', fun y => ReflTransGen.trans (.tail .rfl (ParRed.eta_beta _)) (hy y)⟩
  | structEta H₀ _ _ hl _ _ hs _ =>
    subst hsrc
    have ⟨⟨_, hD⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact (pi_not_struct hΓ hl (HasType.lam hD hb) hs).elim
  | _ => cases hsrc


omit [Params] in
theorem mkApps_const_eq_cases (he : VExpr.mkApps (.const n ls) vs = e) :
    (vs = [] ∧ e = .const n ls) ∨
      ∃ vs₀ x, vs = vs₀ ++ [x] ∧ e = .app (VExpr.mkApps (.const n ls) vs₀) x := by
  rcases eq_nil_or_snoc' vs with rfl | ⟨vs₀, x, rfl⟩
  · exact .inl ⟨rfl, he.symm⟩
  · exact .inr ⟨vs₀, x, rfl, by rw [← he, VExpr.mkApps_snoc]⟩

/-- Collapse eta expansions inside a constant spine in function position. -/
theorem EtaPar.collapse_spine (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ (VExpr.mkApps (.const h ls) vs) F)
    (ht : Γ ⊢ VExpr.mkApps (.const h ls) vs : .forallE X Y) :
    ∃ vs', List.Forall₂ (EtaPar Γ) vs vs' ∧
      ∀ y, ReflTransGen (ParRed Γ) (.app F y) (.app (VExpr.mkApps (.const h ls) vs') y) := by
  generalize hsrc : VExpr.mkApps (.const h ls) vs = src at H ht
  induction H generalizing vs X Y with
  | @app _ f f' x x' hf hx ih₁ _ =>
    rcases mkApps_const_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he
    · cases he
      obtain ⟨_, _, tf, _⟩ := ht.app_inv henv hΓ
      obtain ⟨vs₀', h₀, hy⟩ := ih₁ hΓ rfl tf
      refine ⟨vs₀' ++ [x'], List.Forall₂.append' h₀ (.cons hx .nil), fun y => ?_⟩
      rw [VExpr.mkApps_snoc]
      exact ParRedS.app (hy x') .rfl
  | funEta H₀ HA hty ih =>
    subst hsrc
    obtain ⟨vs', h', hy⟩ := ih hΓ rfl ht
    exact ⟨vs', h', fun y => ReflTransGen.trans (.tail .rfl (ParRed.eta_beta _)) (hy y)⟩
  | structEta H₀ _ _ hl _ _ hs _ =>
    subst hsrc
    exact (pi_not_struct hΓ hl ht hs).elim
  | const =>
    rcases mkApps_const_eq_cases hsrc with ⟨rfl, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he; exact ⟨[], .nil, fun _ => .rfl⟩
    · cases he
  | bvar | sort | elim | proj | lam | forallE =>
    rcases mkApps_const_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, _, he⟩ <;> cases he

theorem struct_family_eq (hΓ : OnCtx Γ (env.IsType univs)) (hl : env.projections fam info')
    (hM : Γ ⊢ M : VExpr.mkApps (.const fam ls) ps) (hp : Γ ⊢ .proj s i M : T) :
    fam = s ∧ env.projections s info' := by
  obtain ⟨info, levels, params, indexArgs, _, _, _, hinfo, _, _, _, _, _, _, hmajor, _, _⟩ :=
    hp.proj_inv henv hΓ
  have hu := hM.uniqU henv hΓ hmajor.hasType.2
  obtain ⟨_, hsort⟩ := hM.isType henv hΓ
  by_cases hne : fam = s
  · subst hne; exact ⟨rfl, hl⟩
  · exact (IsDefEqU.rigidApp_ne henv hΓ (henv.projectionRigid hl) (henv.projectionRigid hinfo)
      hne hsort hu).elim

/-- Collapse eta expansions of a constructor-spine major beneath a projection,
by beta reduction and by projection of structure expansions. -/
theorem EtaPar.collapse_proj (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ (VExpr.mkApps (.const ctor ls) args) M')
    (hs : Γ ⊢ .proj s i (VExpr.mkApps (.const ctor ls) args) : T) :
    ∃ args', List.Forall₂ (EtaPar Γ) args args' ∧
      ReflTransGen (Below Γ 3) (.proj s i M') (.proj s i (VExpr.mkApps (.const ctor ls) args')) := by
  generalize hsrc : VExpr.mkApps (.const ctor ls) args = src at H hs
  induction H generalizing args T with
  | @app _ f f' x x' hf hx ih₁ _ =>
    rcases mkApps_const_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he
    · cases he
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := hs.proj_inv henv hΓ
      obtain ⟨_, _, tf, _⟩ := hmajor.hasType.2.app_inv henv hΓ
      obtain ⟨vs₀', h₀, hy⟩ := EtaPar.collapse_spine hΓ hf tf
      refine ⟨vs₀' ++ [x'], List.Forall₂.append' h₀ (.cons hx .nil), ?_⟩
      rw [VExpr.mkApps_snoc]
      exact Below.ofParRedS (ParRedS.proj (hy x')) (by decide)
  | funEta H₀ HA hty ih =>
    subst hsrc
    obtain ⟨_, _, _, _, _, _, _, hinfo, _, _, _, _, _, _, hmajor', _, _⟩ := hs.proj_inv henv hΓ
    exact (pi_not_struct hΓ hinfo hty hmajor'.hasType.2).elim
  | @structEta _ M M₀ fam info' levels ps ps' H₀ hlen hps hl hp hi hsM hexp ih =>
    subst hsrc
    obtain ⟨rfl, hl'⟩ := struct_family_eq hΓ hl hsM hs
    have hidx : i < info'.numFields := hs.proj_index_lt henv hΓ hl'
    have hstep := EtaPar.structEta H₀ hlen hps hl hp hi hsM hexp
    have hb := (EtaPar.full hΓ (.proj hstep) hs).hasType hΓ hs
    have h₀ := (EtaPar.full hΓ (.proj H₀) hs).hasType hΓ hs
    have hget : (ps' ++ (List.range info'.numFields).map fun j => VExpr.proj fam j M₀)[info'.nparams + i]? =
        some (.proj fam i M₀) := by
      rw [List.getElem?_append_right (by omega)]
      simp [← hp, hlen, hidx]
    have hδ : DeltaPar _ (.proj fam i (structExpand fam info' levels ps' M₀)) (.proj fam i M₀) :=
      .projIota rfl (fun _ _ _ => .rfl) hl' hb hget h₀
    obtain ⟨args', h', hc⟩ := ih hΓ rfl hs
    exact ⟨args', h', ReflTransGen.trans (.tail .rfl ⟨2, by decide, hδ⟩) hc⟩
  | const =>
    rcases mkApps_const_eq_cases hsrc with ⟨rfl, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he; exact ⟨[], .nil, .rfl⟩
    · cases he
  | bvar | sort | elim | proj | lam | forallE =>
    rcases mkApps_const_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, _, he⟩ <;> cases he

/-- Project every field of a saturated structure constructor application. -/
theorem DeltaPar.project_fields (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.projections family info)
    (hlen : ps₀.length = info.nparams + info.numFields)
    (ht : Γ ⊢ structExpand family info levels ps (VExpr.mkApps (.const info.ctorName lsc) ps₀) : T) :
    DeltaPar Γ (structExpand family info levels ps (VExpr.mkApps (.const info.ctorName lsc) ps₀))
      (VExpr.mkApps (.const info.ctorName levels) (ps ++ ps₀.drop info.nparams)) := by
  unfold structExpand at ht ⊢
  refine DeltaPar.mkApps_args (List.Forall₂.append' (List.Forall₂.rfl fun _ _ => .rfl) ?_)
  apply List.forall₂_of_getElem (by simp; omega)
  intro j hj hj'
  have hjmem : j ∈ List.range info.numFields := by simpa using hj
  obtain ⟨_, hpj⟩ := schema_mkApps_arg_type hΓ ht
    (List.mem_append_right _ (List.mem_map.mpr ⟨j, hjmem, rfl⟩))
  have hjn : j < info.numFields := by simpa using hj
  have hget : ps₀[info.nparams + j]? = some (ps₀.drop info.nparams)[j] := by
    rw [List.getElem_drop]; exact List.getElem?_eq_getElem (by omega)
  simp only [List.getElem_map, List.getElem_range]
  exact .projIota rfl (fun _ _ _ => .rfl) hl hpj hget
    (HasType.projIota_field hΓ hl hpj hlen hget)

/-- Collapse eta expansions of a constructor major of a recursor iota pattern. -/
theorem EtaPar.collapse_major
    (hΓ : OnCtx Γ (env.IsType univs))
    (hstruct : ∀ {family info ls ps}, env.projections family info →
      Γ ⊢ VExpr.mkApps (.const cc lsc) fs : VExpr.mkApps (.const family ls) ps →
      cc = info.ctorName ∧ kc = info.nparams + info.numFields)
    (H : EtaPar Γ (VExpr.mkApps (.const cc lsc) fs) M')
    (ht : Γ ⊢ VExpr.mkApps (.const cc lsc) fs : T)
    (hnotpi : ∀ D B, ¬ Γ ⊢ VExpr.mkApps (.const cc lsc) fs : .forallE D B)
    (hlen : fs.length = kc) :
    ∃ fs₀ lsc' ps₀, List.Forall₂ (EtaPar Γ) fs fs₀ ∧
      ReflTransGen (Below Γ 3) M' (VExpr.mkApps (.const cc lsc') ps₀) ∧
      ((lsc' = lsc ∧ ps₀ = fs₀) ∨
        ∃ family info ps, env.projections family info ∧ cc = info.ctorName ∧
          kc = info.nparams + info.numFields ∧ ps₀.length = kc ∧
          ps₀.drop info.nparams = fs₀.drop info.nparams ∧
          Γ ⊢ VExpr.mkApps (.const cc lsc) fs : VExpr.mkApps (.const family lsc') ps) := by
  generalize hsrc : VExpr.mkApps (.const cc lsc) fs = src at H ht hnotpi hstruct
  induction H generalizing fs T with
  | @app _ f f' x x' hf hx _ _ =>
    rcases mkApps_const_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he
    · cases he
      obtain ⟨_, _, tf, _⟩ := ht.app_inv henv hΓ
      obtain ⟨vs₀', h₀, hy⟩ := EtaPar.collapse_spine hΓ hf tf
      refine ⟨vs₀' ++ [x'], lsc, vs₀' ++ [x'], List.Forall₂.append' h₀ (.cons hx .nil), ?_,
        .inl ⟨rfl, rfl⟩⟩
      rw [VExpr.mkApps_snoc]
      exact Below.ofParRedS (hy x') (by decide)
  | funEta H₀ HA hty ih =>
    subst hsrc
    exact (hnotpi _ _ hty).elim
  | @structEta _ M M₀ fam info levels ps ps' H₀ hlen' hps hl hp' hi hs hexp ih =>
    subst hsrc
    obtain ⟨hcc, hkc⟩ := hstruct hl hs
    obtain ⟨fs₀, lsc'', ps₀', hfs, c₀, hdisj⟩ := ih hΓ hlen rfl hs hnotpi hstruct
    have hps₀len : ps₀'.length = info.nparams + info.numFields := by
      rcases hdisj with ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, h, _⟩
      · rw [← Lean4Lean.List.Forall₂.length_eq hfs, hlen, hkc]
      · rw [h, hkc]
    have hstep := EtaPar.structEta H₀ hlen' hps hl hp' hi hs hexp
    have hb := (EtaPar.full hΓ hstep hs).hasType hΓ hs
    have c₁ := Below.expand hΓ c₀ hb
    have hb₁ := Below.hasType hΓ c₁ hb
    subst hcc
    have hδ := DeltaPar.project_fields hΓ hl hps₀len hb₁
    have hpl : ps'.length = info.nparams := hlen'.symm.trans hp'
    refine ⟨fs₀, levels, ps' ++ ps₀'.drop info.nparams, hfs, c₁.tail ⟨2, by decide, hδ⟩,
      .inr ⟨fam, info, ps, hl, rfl, hkc, by simp; omega, ?_, hs⟩⟩
    rw [List.drop_left' hpl]
    rcases hdisj with ⟨_, rfl⟩ | ⟨fam₂, info₂, _, hl₂, hc₂, _, _, h, _⟩
    · rfl
    · obtain ⟨-, rfl⟩ := henv.ordered.projectionConstructor_family hl hl₂ hc₂
      exact h
  | const =>
    rcases mkApps_const_eq_cases hsrc with ⟨rfl, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he; exact ⟨[], lsc, [], .nil, .rfl, .inl ⟨rfl, rfl⟩⟩
    · cases he
  | bvar | sort | elim | proj | lam | forallE =>
    rcases mkApps_const_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, _, he⟩ <;> cases he

omit [Params] in
theorem _root_.Lean4Lean.Pattern.Matches.constVarN_forall₂ {R : VExpr → VExpr → Prop} :
    ∀ (k : Nat) {vs vs' : List VExpr} {ls ls' : List VLevel} {m m'},
      ((Pattern.const c).varN k).Matches (VExpr.mkApps (.const c ls) vs) ls m →
      ((Pattern.const c).varN k).Matches (VExpr.mkApps (.const c ls') vs') ls' m' →
      (∀ a, R (m a) (m' a)) → List.Forall₂ R vs vs'
  | 0, vs, vs', ls, ls', m, m', H, H', _ => by
    generalize hE : VExpr.mkApps (.const c ls) vs = E at H
    generalize hE' : VExpr.mkApps (.const c ls') vs' = E' at H'
    cases H; cases H'
    rcases eq_nil_or_snoc' vs with rfl | ⟨_, _, rfl⟩
    · rcases eq_nil_or_snoc' vs' with rfl | ⟨_, _, rfl⟩
      · exact .nil
      · rw [VExpr.mkApps_snoc] at hE'; cases hE'
    · rw [VExpr.mkApps_snoc] at hE; cases hE
  | k + 1, vs, vs', ls, ls', m, m', H, H', hR => by
    generalize hE : VExpr.mkApps (.const c ls) vs = E at H
    generalize hE' : VExpr.mkApps (.const c ls') vs' = E' at H'
    cases H with
    | var H₀ =>
      cases H' with
      | var H₀' =>
        obtain ⟨vs₀, rfl, rfl⟩ := RigidHead.const.mkApps_eq_app hE
        obtain ⟨vs₀', rfl, rfl⟩ := RigidHead.const.mkApps_eq_app hE'
        exact List.Forall₂.append'
          (Pattern.Matches.constVarN_forall₂ k H₀ H₀' fun a => hR (some a)) (.cons (hR none) .nil)

omit [Params] in
theorem _root_.Lean4Lean.Pattern.Matches.constVarN_exists :
    ∀ (k : Nat) {vs : List VExpr} {ls : List VLevel}, vs.length = k →
      ∃ m, ((Pattern.const c).varN k).Matches (VExpr.mkApps (.const c ls) vs) ls m
  | 0, vs, ls, h => by
    cases List.length_eq_zero_iff.mp h
    exact ⟨_, .const⟩
  | k + 1, vs, ls, h => by
    rcases eq_nil_or_snoc' vs with rfl | ⟨vs₀, x, rfl⟩
    · simp at h
    · obtain ⟨m, hm⟩ := Pattern.Matches.constVarN_exists k (vs := vs₀) (ls := ls) (by simpa using h)
      rw [VExpr.mkApps_snoc]
      exact ⟨_, .var hm⟩

omit [Params] in
theorem _root_.Lean4Lean.Pattern.Matches.constVarN_of_values :
    ∀ (k : Nat) (vals : ((Pattern.const c).varN k).Path → VExpr),
      ((Pattern.const c).varN k).Matches
        (VExpr.mkApps (.const c ls) (((Pattern.const c).argumentRHS k).map (·.apply ls vals))) ls vals
  | 0, vals => by
    have : vals = nofun := funext fun a => nomatch a
    subst this; exact .const
  | k + 1, vals => by
    have ih := Pattern.Matches.constVarN_of_values (ls := ls) k (fun a => vals (some a))
    have hmap : (((Pattern.const c).argumentRHS (k + 1)).map (·.apply ls vals)) =
        (((Pattern.const c).argumentRHS k).map (·.apply ls (fun a => vals (some a)))) ++
          [vals none] := by
      simp only [Pattern.argumentRHS, List.map_append, List.map_map, List.map_cons, List.map_nil,
        Function.comp_def, Pattern.RHS.apply]
      congr 1
      apply List.map_congr_left
      intro x _
      exact Pattern.RHS.mapPaths_apply _ _
    rw [hmap, VExpr.mkApps_snoc]
    have := Pattern.Matches.var (a' := vals none) ih
    have hv : (fun x => Option.elim x (vals none) fun a => vals (some a)) = vals := by
      funext x; cases x <;> rfl
    exact hv ▸ this

theorem CaseRedex.transport (hΓ : OnCtx Γ (env.IsType univs))
    (H : CaseRedex env univs Γ rule actual)
    {actual' : InductiveSignature.CaseSchema.Application}
    (hb : actual'.block = actual.block) (ho : actual'.owner = actual.owner)
    (hlv : actual'.levels = actual.levels) (hc : actual'.ctorName = actual.ctorName)
    (hcl : List.Forall₂ (· ≈ ·) actual'.ctorLevels actual.ctorLevels)
    (hal : actual'.arguments.length = actual.arguments.length)
    (hcal : actual'.ctorArguments.length = actual.ctorArguments.length)
    (hcap : List.Forall₂ (IsDefEqU env univs Γ) (rule.capture actual) (rule.capture actual'))
    (he : IsDefEqU env univs Γ actual.expr actual'.expr) :
    CaseRedex env univs Γ rule actual' := by
  have hlen := (Lean4Lean.List.Forall₂.length_eq hcap).symm
  have hargs := fun (i : Nat) hi hi' => case_forall₂_get (i := i) hcap hi hi'
  refine {
    source := ?_
    block_eq := hb.trans H.block_eq
    owner_eq := ho.trans H.owner_eq
    ctor_eq := hc.trans H.ctor_eq
    arguments_length := hal.trans H.arguments_length
    ctorArguments_length := hcal.trans H.ctorArguments_length
    levels_eq := ?_
    ctorLevels_eq := ?_
    guard := ?_ }
  · rw [hlv]; exact H.source.congr henv hΓ hlen hargs
  · rw [hlv]; exact H.levels_eq
  · rw [hlv]; exact Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') hcl H.ctorLevels_eq
  · rw [hlv]
    exact (he.symm.trans henv hΓ H.guard).trans henv hΓ (H.source.lhs_congr henv hΓ hlen hargs)
omit [Params] in
theorem mkApps_elim_eq_cases (he : VExpr.mkApps (.elim n o ls) vs = e) :
    (vs = [] ∧ e = .elim n o ls) ∨
      ∃ vs₀ x, vs = vs₀ ++ [x] ∧ e = .app (VExpr.mkApps (.elim n o ls) vs₀) x := by
  rcases eq_nil_or_snoc' vs with rfl | ⟨vs₀, x, rfl⟩
  · exact .inl ⟨rfl, he.symm⟩
  · exact .inr ⟨vs₀, x, rfl, by rw [← he, VExpr.mkApps_snoc]⟩

/-- Collapse eta expansions inside an eliminator spine in function position. -/
theorem EtaPar.collapse_elim (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ (VExpr.mkApps (.elim h o ls) vs) F)
    (ht : Γ ⊢ VExpr.mkApps (.elim h o ls) vs : .forallE X Y) :
    ∃ vs', List.Forall₂ (EtaPar Γ) vs vs' ∧
      ∀ y, ReflTransGen (ParRed Γ) (.app F y) (.app (VExpr.mkApps (.elim h o ls) vs') y) := by
  generalize hsrc : VExpr.mkApps (.elim h o ls) vs = src at H ht
  induction H generalizing vs X Y with
  | @app _ f f' x x' hf hx ih₁ _ =>
    rcases mkApps_elim_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he
    · cases he
      obtain ⟨_, _, tf, _⟩ := ht.app_inv henv hΓ
      obtain ⟨vs₀', h₀, hy⟩ := ih₁ hΓ rfl tf
      refine ⟨vs₀' ++ [x'], List.Forall₂.append' h₀ (.cons hx .nil), fun y => ?_⟩
      rw [VExpr.mkApps_snoc]
      exact ParRedS.app (hy x') .rfl
  | funEta H₀ HA hty ih =>
    subst hsrc
    obtain ⟨vs', h', hy⟩ := ih hΓ rfl ht
    exact ⟨vs', h', fun y => ReflTransGen.trans (.tail .rfl (ParRed.eta_beta _)) (hy y)⟩
  | structEta H₀ _ _ hl _ _ hs _ =>
    subst hsrc
    exact (pi_not_struct hΓ hl ht hs).elim
  | elim =>
    rcases mkApps_elim_eq_cases hsrc with ⟨rfl, he⟩ | ⟨vs₀, x₀, rfl, he⟩
    · cases he; exact ⟨[], .nil, fun _ => .rfl⟩
    · cases he
  | bvar | sort | const | proj | lam | forallE =>
    rcases mkApps_elim_eq_cases hsrc with ⟨_, he⟩ | ⟨vs₀, x₀, _, he⟩ <;> cases he
end EtaTools


section EtaDelta

/-- Peaks of eta expansion against parallel prefix computation, below a size. -/
abbrev EDBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → EtaPar Γ a b → DeltaPar Γ a c →
    Γ ⊢ a : A → ∃ d, ReflTransGen (Below Γ 3) b d ∧ EtaPar Γ c d

theorem EtaPar.delta_join_args (hΓ : OnCtx Γ (env.IsType univs)) (IH : EDBelow s)
    (hsub : ∀ x ∈ args, sizeOf x < s) (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h₁ : List.Forall₂ (EtaPar Γ) args argsB) (h₂ : List.Forall₂ (DeltaPar Γ) args args') :
    ∃ D, List.Forall₂ (ReflTransGen (Below Γ 3)) argsB D ∧ List.Forall₂ (EtaPar Γ) args' D := by
  obtain ⟨us, vs, hus, hvs, heq⟩ := List.Forall₂.exists_join (U := Eq) h₁ h₂
    fun x _ _ hx p q => by
      obtain ⟨d, h1, h2⟩ := IH (hsub x hx) hΓ p q (htyped x hx).choose_spec
      exact ⟨d, d, h1, h2, rfl⟩
  cases forall₂_eq_imp heq
  exact ⟨us, hus, hvs⟩

theorem EtaPar.delta_spine (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EDBelow (sizeOf (VExpr.mkApps (.const name ls) args)))
    (hF : EtaPar Γ (VExpr.mkApps (.const name ls) args₀) f') (hX : EtaPar Γ x x')
    (hargs : args = args₀ ++ [x])
    (hlen : args.length = args'.length)
    (hd : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hr : SpineRule Γ name ls args' rhs)
    (ha : Γ ⊢ VExpr.mkApps (.const name ls) args : A) :
    ∃ d, ReflTransGen (Below Γ 3) (.app f' x') d ∧ EtaPar Γ rhs d := by
  subst hargs
  have ha' := ha
  rw [VExpr.mkApps_snoc] at ha'
  obtain ⟨_, _, tf, tx⟩ := ha'.app_inv henv hΓ
  obtain ⟨args₀', h₀, hy⟩ := EtaPar.collapse_spine hΓ hF tf
  have hB : List.Forall₂ (EtaPar Γ) (args₀ ++ [x]) (args₀' ++ [x']) :=
    List.Forall₂.append' h₀ (.cons hX .nil)
  have targs := HasType.mkApps_args_typed hΓ ha
  obtain ⟨D, hBD, hD⟩ := EtaPar.delta_join_args hΓ IH (fun _ hx => sizeOf_mkApps_arg hx) targs hB
    (List.forall₂_of_getElem hlen hd)
  obtain ⟨rhsD, X, hrD, pX, eX⟩ : ∃ rhsD X, SpineRule Γ name ls D rhsD ∧ EtaPar Γ rhs X ∧
      NormalEq₀ Γ X rhsD := by
    rcases hr with hr | ⟨rfl, hr⟩
    · obtain ⟨_, _, h, h1, h2⟩ := hr.congr_red EtaPar.congrRel EtaPar.argRel hΓ hD
      exact ⟨_, _, .inl h, h1, h2⟩
    · obtain ⟨_, _, h, h1, h2⟩ := hr.congr_red EtaPar.congrRel EtaPar.argRel hΓ hD
      exact ⟨_, _, .inr ⟨rfl, h⟩, h1, h2⟩
  have hb := (EtaPar.full hΓ (.app hF hX) ha').hasType hΓ ha'
  have c₁ : ReflTransGen (Below Γ 3) (.app f' x') (VExpr.mkApps (.const name ls) (args₀' ++ [x'])) := by
    rw [VExpr.mkApps_snoc]; exact Below.ofParRedS (hy x') (by decide)
  have tB := Below.hasType hΓ c₁ hb
  have c₂ := Below.mkApps hΓ .rfl hBD tB
  have hδ : DeltaPar Γ (VExpr.mkApps (.const name ls) D) rhsD :=
    hrD.step (List.Forall₂.rfl fun _ _ => .rfl)
  have tD := Below.hasType hΓ c₂ tB
  have tX := ((DeltaPar.full hδ).hasType hΓ tD).defeqU_l henv hΓ (NormalEqF.defeq hΓ eX).symm
  refine ⟨X, (c₁.trans c₂).tail ⟨2, by decide, hδ⟩ |>.tail ⟨0, by decide, ?_⟩, pX⟩
  exact NormalEqF.symm hΓ eX

theorem EtaPar.delta_projIota (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EDBelow (sizeOf (VExpr.proj family index (VExpr.mkApps (.const info.ctorName ls) args))))
    (hM : EtaPar Γ (VExpr.mkApps (.const info.ctorName ls) args) M')
    (hlen : args.length = args'.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i])
    (hl : env.projections family info)
    (hs : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args') : fieldType)
    (hi : args'[info.nparams + index]? = some field) (ht : Γ ⊢ field : fieldType)
    (ha : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName ls) args) : A) :
    ∃ d, ReflTransGen (Below Γ 3) (.proj family index M') d ∧ EtaPar Γ field d := by
  obtain ⟨argsB, hB, c₁⟩ := EtaPar.collapse_proj hΓ hM ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
  have targs := HasType.mkApps_args_typed hΓ lm.hasType.2
  obtain ⟨D, hBD, hD⟩ := EtaPar.delta_join_args hΓ IH
    (fun _ hx => by have := sizeOf_mkApps_arg (f := .const info.ctorName ls) hx; simp; omega)
    targs hB (List.forall₂_of_getElem hlen hargs)
  have hb := (EtaPar.full hΓ (.proj hM) ha).hasType hΓ ha
  have hc := (DeltaPar.full (.projIota hlen hargs hl hs hi ht)).hasType hΓ ha
  have tB := Below.hasType hΓ c₁ hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm', _, _⟩ := tB.proj_inv henv hΓ
  have c₂ := Below.proj hΓ (Below.mkApps hΓ .rfl hBD lm'.hasType.2) tB
  have tD := Below.hasType hΓ c₂ tB
  obtain ⟨dk, hdk, pdk⟩ := forall₂_getElem?_left hD hi
  have tdk := (EtaPar.full hΓ pdk hc).hasType hΓ hc
  have hδ : DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) D)) dk :=
    .projIota rfl (fun _ _ _ => .rfl) hl tD hdk tdk
  exact ⟨dk, (c₁.trans c₂).tail ⟨2, by decide, hδ⟩, pdk⟩


theorem EtaPar.deltaPar_aux : ∀ n, EDBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have IH : EDBelow (sizeOf a) := fun h => ih (by omega)
  clear ih hsz
  induction H generalizing c A with
  | bvar | sort | const | elim =>
    exact ⟨c, .tail .rfl ⟨2, by decide, H2⟩, .rfl⟩
  | @app _ f f' x x' hF hX _ _ =>
    have hb := (EtaPar.full hΓ (.app hF hX) ha).hasType hΓ ha
    generalize hE : VExpr.app f x = E at H2 ha IH
    cases H2 with
    | app hf hx =>
      cases hE
      obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
      obtain ⟨df, cf, ef⟩ := IH (by simp; omega) hΓ hF hf tf
      obtain ⟨dx, cx, ex⟩ := IH (by simp; omega) hΓ hX hx tx
      exact ⟨_, Below.app hΓ cf cx hb, .app ef ex⟩
    | @delta _ name ls rhs args args' hlen hargs hr =>
      rcases mkApps_const_eq_cases hE.symm with ⟨_, he⟩ | ⟨args₀, x₀, rfl, he⟩
      · cases he
      · cases he
        exact EtaPar.delta_spine hΓ IH hF hX rfl hlen hargs (.inl hr) ha
    | @quotDelta _ ls rhs args args' hlen hargs hr =>
      rcases mkApps_const_eq_cases hE.symm with ⟨_, he⟩ | ⟨args₀, x₀, rfl, he⟩
      · cases he
      · cases he
        exact EtaPar.delta_spine hΓ IH hF hX rfl hlen hargs (.inr ⟨rfl, hr⟩) ha
    | _ => cases hE
  | @proj _ m m' family index hM _ =>
    have hb := (EtaPar.full hΓ (.proj hM) ha).hasType hΓ ha
    generalize hE : VExpr.proj family index m = E at H2 ha IH
    cases H2 with
    | proj hm =>
      cases hE
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨dm, cm, em⟩ := IH (by simp; omega) hΓ hM hm lm.hasType.2
      exact ⟨_, Below.proj hΓ cm hb, .proj em⟩
    | projIota hlen hargs hl hs hi ht =>
      injection hE with hf hidx hm
      subst hf hidx hm
      exact EtaPar.delta_projIota hΓ IH hM hlen hargs hl hs hi ht ha
    | delta => exact absurd hE.symm mkApps_const_ne_proj
    | quotDelta => exact absurd hE.symm mkApps_const_ne_proj
    | _ => cases hE
  | @lam _ D D' t t' hD ht _ _ =>
    have hb := (EtaPar.full hΓ (.lam hD ht) ha).hasType hΓ ha
    obtain ⟨D₂, t₂, hD₂, ht₂, rfl⟩ := DeltaPar.lam_inv H2
    obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.lam_inv henv hΓ
    have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
    obtain ⟨dD, cD, eD⟩ := IH (by simp; omega) hΓ hD hD₂ tD
    obtain ⟨dt, ct, et⟩ := IH (by simp; omega) hΓ' ht ht₂ tt
    have hDD' := (EtaPar.full hΓ hD tD).defeq hΓ tD
    have hDD₂ := (DeltaPar.full hD₂).defeq hΓ tD
    have tt' := (EtaPar.full hΓ' ht tt).hasType hΓ' tt
    have tt₂ := (DeltaPar.full ht₂).hasType hΓ' tt
    exact ⟨_, Below.lam hΓ cD (Below.defeqDFC hΓ (.succ .zero hDD') ct tt') hb,
      .lam eD (et.defeqDFC hΓ (.succ .zero hDD₂) tt₂)⟩
  | @forallE _ D D' t t' hD ht _ _ =>
    have hb := (EtaPar.full hΓ (.forallE hD ht) ha).hasType hΓ ha
    obtain ⟨D₂, t₂, hD₂, ht₂, rfl⟩ := DeltaPar.forallE_inv H2
    obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.forallE_inv henv
    have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
    obtain ⟨dD, cD, eD⟩ := IH (by simp; omega) hΓ hD hD₂ tD
    obtain ⟨dt, ct, et⟩ := IH (by simp; omega) hΓ' ht ht₂ tt
    have hDD' := (EtaPar.full hΓ hD tD).defeq hΓ tD
    have hDD₂ := (DeltaPar.full hD₂).defeq hΓ tD
    have tt' := (EtaPar.full hΓ' ht tt).hasType hΓ' tt
    have tt₂ := (DeltaPar.full ht₂).hasType hΓ' tt
    exact ⟨_, Below.forallE hΓ cD (Below.defeqDFC hΓ (.succ .zero hDD') ct tt') hb,
      .forallE eD (et.defeqDFC hΓ (.succ .zero hDD₂) tt₂)⟩
  | funEta H₀ HD hty ih =>
    obtain ⟨d₀, c₀, e₀⟩ := ih hΓ H2 ha IH
    have hc := (DeltaPar.full H2).hasType hΓ hty
    have hb := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    obtain ⟨h1, h2⟩ := EtaPar.root_fun hΓ HD hc c₀ e₀ hb
    exact ⟨_, h1, h2⟩
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    obtain ⟨d₀, c₀, e₀⟩ := ih hΓ H2 ha IH
    have hc := (DeltaPar.full H2).hasType hΓ hs
    have hcexp := (FullReduction.structExpand (DeltaPar.full H2)).hasType hΓ hexp
    have hb := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    obtain ⟨h1, h2⟩ := EtaPar.root_struct hΓ hl hp hi hlen hps hc hcexp c₀ e₀ hb
    exact ⟨_, h1, h2⟩
end EtaDelta


section EtaParRed

/-- Peaks of eta expansion against parallel reduction, below a size. -/
abbrev EPBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → EtaPar Γ a b → ParRed Γ a c →
    Γ ⊢ a : A → ∃ d, ReflTransGen (Below Γ 3) b d ∧ EtaPar Γ c d

omit [Params] in
theorem forall₂_rtg_refl {R : α → α → Prop} : ∀ (l : List α), List.Forall₂ (ReflTransGen R) l l
  | [] => .nil
  | _ :: l => .cons .rfl (forall₂_rtg_refl l)

theorem EtaPar.parRed_iota
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hΓ : OnCtx Γ (env.IsType univs)) (IH : EPBelow (sizeOf e))
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hck : r.2.OK (IsDefEqU env univs Γ) m1 m2) (hargs : ∀ v, ParRed Γ (m2 v) (m2' v))
    (hF : EtaPar Γ F F') (hM : EtaPar Γ M M') (he : e = .app F M) (ha : Γ ⊢ e : A) :
    ∃ d, ReflTransGen (Below Γ 3) (.app F' M') d ∧ EtaPar Γ (r.1.apply m1 m2') d := by
  classical
  have hm₀ := hm
  subst he
  obtain ⟨g1, g2, lsc, hF₀, hM₀, rfl⟩ :
      ∃ g1 g2 lsc, ((Pattern.const rc).varN mr).Matches F m1 g1 ∧
        ((Pattern.const cc).varN kc).Matches M lsc g2 ∧ m2 = Sum.elim g1 g2 := by
    cases hm with | app hF hM => exact ⟨_, _, _, hF, hM, rfl⟩
  obtain ⟨vsF, rfl⟩ : ∃ vs, F = VExpr.mkApps (.const rc m1) vs := ⟨_, hF₀.const_arguments⟩
  obtain ⟨fsM, rfl⟩ : ∃ fs, M = VExpr.mkApps (.const cc lsc) fs := ⟨_, hM₀.const_arguments⟩
  have hfsLen : fsM.length = kc := by
    obtain ⟨-, -, h⟩ := VExpr.mkApps_const_inj hM₀.const_arguments
    rw [h]; simp [Pattern.argumentRHS_length]
  obtain ⟨_, _, tF, tM⟩ := ha.app_inv henv hΓ
  -- collapse the function spine and the major
  obtain ⟨vs', hvs', hy⟩ := EtaPar.collapse_spine hΓ hF tF
  have hnotpi : ∀ D B, ¬ Γ ⊢ VExpr.mkApps (.const cc lsc) fsM : .forallE D B :=
    fun _ _ hpi => Params.major_not_pi hΓ hp hm₀ ha hpi
  obtain ⟨fs₀, lsc', ps₀, hfs₀, cM, hdisj⟩ := EtaPar.collapse_major hΓ
    (fun hl hs => pat_struct_major hp hΓ hl hs hfsLen) hM tM hnotpi hfsLen
  have hb := (EtaPar.full hΓ (.app hF hM) ha).hasType hΓ ha
  have c₁ : ReflTransGen (Below Γ 3) (.app F' M') (.app (VExpr.mkApps (.const rc m1) vs') M') :=
    Below.ofParRedS (hy M') (by decide)
  have tb₁ := Below.hasType hΓ c₁ hb
  have c₂ := Below.app hΓ .rfl cM tb₁
  have tb₂ := Below.hasType hΓ c₂ tb₁
  -- the values of the eta side, and the induction hypothesis on every value
  obtain ⟨g1', hg1', hr1⟩ := Pattern.Matches.constVarN_transport (R := fun x y => EtaPar Γ y x)
    mr hF₀ (Lean4Lean.List.Forall₂.flip hvs') (ls' := m1)
  obtain ⟨g2₀, hg2₀, hr2⟩ := Pattern.Matches.constVarN_transport (R := fun x y => EtaPar Γ y x)
    kc hM₀ (Lean4Lean.List.Forall₂.flip hfs₀) (ls' := lsc)
  have hrel : ∀ v, EtaPar Γ (Sum.elim g1 g2 v) (Sum.elim g1' g2₀ v) := by
    intro v; cases v with
    | inl v => exact hr1 v
    | inr v => exact hr2 v
  have htv : ∀ v, ∃ T, Γ ⊢ Sum.elim g1 g2 v : T := fun v => hm₀.hasType hΓ ha v
  have hj : ∀ v, ∃ d, ReflTransGen (Below Γ 3) (Sum.elim g1' g2₀ v) d ∧ EtaPar Γ (m2' v) d :=
    fun v => IH (hm₀.sizeOf_lt v) hΓ (hrel v) (hargs v) (htv v).choose_spec
  let D := fun v => (hj v).choose
  have cD : ∀ v, ReflTransGen (Below Γ 3) (Sum.elim g1' g2₀ v) (D v) :=
    fun v => (hj v).choose_spec.1
  have eD : ∀ v, EtaPar Γ (m2' v) (D v) := fun v => (hj v).choose_spec.2
  -- lists of the joined values
  have hvsD := Pattern.Matches.constVarN_of_values (c := rc) (ls := m1) mr (fun v => D (.inl v))
  have hfsD := Pattern.Matches.constVarN_of_values (c := cc) (ls := lsc) kc (fun v => D (.inr v))
  have cvs := Pattern.Matches.constVarN_forall₂ mr hg1' hvsD fun v => cD (.inl v)
  have cfs := Pattern.Matches.constVarN_forall₂ kc hg2₀ hfsD fun v => cD (.inr v)
  have hDsum : (Sum.elim (fun v => D (.inl v)) (fun v => D (.inr v))) = D := by
    funext v; cases v <;> rfl
  have hdef : ∀ v, IsDefEqU env univs Γ (Sum.elim g1 g2 v) (D v) := fun v =>
    ⟨_, ((EtaPar.full hΓ (hrel v) (htv v).choose_spec).defeq hΓ (htv v).choose_spec).trans
      (Below.defeq hΓ (cD v) ((EtaPar.full hΓ (hrel v) (htv v).choose_spec).hasType hΓ
        (htv v).choose_spec))⟩
  have hckD := Pattern.Check.OK.defeq_values hΓ
    (p := Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) (m' := D) hdef hck
  obtain ⟨_, _, tF₂, tM₂⟩ := tb₂.app_inv henv hΓ
  have cF := Below.mkApps hΓ (f := .const rc m1) .rfl cvs tF₂
  refine ⟨_, ?_, EtaPar.congrRel.apply_rhs r.1 eD⟩
  rcases hdisj with ⟨rfl, rfl⟩ | ⟨fam, info, _, hl, hcc, hkc, hlen₀, hdrop, _⟩
  · have cM₂ := Below.mkApps hΓ (f := .const cc _) .rfl cfs tM₂
    have hmD := Pattern.Matches.app hvsD hfsD
    rw [hDsum] at hmD
    have hfire := ParRed.extra (Γ := Γ) hp hmD hckD (fun _ => .rfl)
    exact (c₁.trans c₂).trans ((Below.app hΓ cF cM₂ tb₂).tail ⟨1, by decide, hfire⟩)
  · subst hcc
    have hnp : info.nparams ≤ kc := by omega
    have hfsDlen : (((Pattern.const info.ctorName).argumentRHS kc).map
        (·.apply lsc (fun v => D (.inr v)))).length = kc := by simp [Pattern.argumentRHS_length]
    let fsD := ((Pattern.const info.ctorName).argumentRHS kc).map (·.apply lsc (fun v => D (.inr v)))
    have hfsDlen' : fsD.length = kc := hfsDlen
    have cps : List.Forall₂ (ReflTransGen (Below Γ 3)) ps₀ (ps₀.take info.nparams ++ fsD.drop info.nparams) := by
      have := List.Forall₂.append' (forall₂_rtg_refl (ps₀.take info.nparams))
        (show List.Forall₂ (ReflTransGen (Below Γ 3)) (ps₀.drop info.nparams) (fsD.drop info.nparams) by
          rw [hdrop]; exact Lean4Lean.List.forall₂_drop cfs _)
      rwa [List.take_append_drop] at this
    have cM₂ := Below.mkApps hΓ (f := .const info.ctorName lsc') .rfl cps tM₂
    obtain ⟨gP, hgP⟩ := Pattern.Matches.constVarN_exists (c := info.ctorName) kc
      (vs := ps₀.take info.nparams ++ fsD.drop info.nparams) (ls := lsc')
      (by simp only [List.length_append, List.length_take, List.length_drop, hfsDlen', hlen₀]; omega)
    have hfsD' : ((Pattern.const info.ctorName).varN kc).Matches
        (VExpr.mkApps (.const info.ctorName lsc) (fsD.take info.nparams ++ fsD.drop info.nparams))
        lsc (fun v => D (.inr v)) := by
      rw [List.take_append_drop]; exact hfsD
    obtain ⟨happ, hchk⟩ := pat_iota_params hp hl rfl hfsD' hgP
      (by simp only [List.length_take, hfsDlen']; omega)
      (by simp only [List.length_take, hlen₀]; omega)
    have hmD := Pattern.Matches.app hvsD hgP
    have hfire := ParRed.extra (Γ := Γ) hp hmD
      (hchk m1 (fun v => D (.inl v)) _ (by rw [hDsum]; exact hckD)) (fun _ => .rfl)
    have heq := happ m1 (fun v => D (.inl v))
    rw [hDsum] at heq
    rw [heq]
    exact (c₁.trans c₂).trans ((Below.app hΓ cF cM₂ tb₂).tail ⟨1, by decide, hfire⟩)


theorem EtaPar.parRed_join_args (hΓ : OnCtx Γ (env.IsType univs)) (IH : EPBelow s)
    (hsub : ∀ x ∈ args, sizeOf x < s) (htyped : ∀ x ∈ args, ∃ T, Γ ⊢ x : T)
    (h₁ : List.Forall₂ (EtaPar Γ) args argsB) (h₂ : List.Forall₂ (ParRed Γ) args args') :
    ∃ D, List.Forall₂ (ReflTransGen (Below Γ 3)) argsB D ∧ List.Forall₂ (EtaPar Γ) args' D := by
  obtain ⟨us, vs, hus, hvs, heq⟩ := List.Forall₂.exists_join (U := Eq) h₁ h₂
    fun x _ _ hx p q => by
      obtain ⟨d, h1, h2⟩ := IH (hsub x hx) hΓ p q (htyped x hx).choose_spec
      exact ⟨d, d, h1, h2, rfl⟩
  cases forall₂_eq_imp heq
  exact ⟨us, hus, hvs⟩

omit [Params] in
theorem take_append_of_cases {l₁ l₂ : List α} (hle : l₁.length ≤ p) (h : l₁.length = p ∨ l₂ = []) :
    (l₁ ++ l₂).take p = l₁ := by
  rcases h with h | rfl
  · subst h; simp
  · simp only [List.append_nil]; exact List.take_of_length_le hle

omit [Params] in
theorem drop_append_of_cases {l₁ l₂ : List α} (hle : l₁.length ≤ q) (h : l₁.length = q ∨ l₂ = []) :
    (l₁ ++ l₂).drop q = l₂ := by
  rcases h with h | rfl
  · subst h; simp
  · simp only [List.append_nil]; exact List.drop_eq_nil_of_le hle

omit [Params] in
/-- Replace the captured positions of two argument lists by related values. -/
theorem capture_replace {R : α → α → Prop} (hrefl : ∀ x, R x x) {A C D : List α} {p q : Nat}
    (H : List.Forall₂ R (A.take p ++ C.drop q) D) :
    ∃ A' C', A'.take p ++ C'.drop q = D ∧ List.Forall₂ R A A' ∧ List.Forall₂ R C C' ∧
      A'.length = A.length ∧ C'.length = C.length := by
  have hD := List.take_append_drop (A.take p).length D
  rw [← hD] at H
  obtain ⟨H1, H2⟩ := Lean4Lean.List.forall₂_append_split H
    (by have := Lean4Lean.List.Forall₂.length_eq H; simp at this ⊢; omega)
  have hl1 := Lean4Lean.List.Forall₂.length_eq H1
  have hl2 := Lean4Lean.List.Forall₂.length_eq H2
  have h1 := hl1; have h2 := hl2
  simp only [List.length_take, List.length_drop] at h1 h2
  refine ⟨D.take (A.take p).length ++ A.drop p, C.take q ++ D.drop (A.take p).length, ?_, ?_, ?_, ?_, ?_⟩
  · rw [take_append_of_cases (by simp only [List.length_take]; omega) (by
        by_cases hp : p ≤ A.length
        · exact .inl (by simp only [List.length_take]; omega)
        · exact .inr (List.drop_eq_nil_of_le (by omega))),
      drop_append_of_cases (by simp only [List.length_take]; omega) (by
        by_cases hq : q ≤ C.length
        · exact .inl (by simp only [List.length_take]; omega)
        · exact .inr (List.eq_nil_of_length_eq_zero (by
            simp only [List.length_drop, List.length_take]; omega)))]
    exact hD
  · have := List.Forall₂.append' H1
      (List.Forall₂.rfl fun x _ => hrefl x : List.Forall₂ R (A.drop p) (A.drop p))
    rwa [List.take_append_drop] at this
  · have := List.Forall₂.append'
      (List.Forall₂.rfl fun x _ => hrefl x : List.Forall₂ R (C.take q) (C.take q)) H2
    rwa [List.take_append_drop] at this
  · simp only [List.length_append, List.length_take, List.length_drop]; omega
  · simp only [List.length_append, List.length_take, List.length_drop]; omega

theorem EtaPar.parRed_schema {rule : InductiveSignature.CaseSchema.AppliedRule}
    {actual : InductiveSignature.CaseSchema.Application}
    (hΓ : OnCtx Γ (env.IsType univs)) (IH : EPBelow (sizeOf actual.expr))
    (hm : CaseRedex env univs Γ rule actual)
    (hl : arguments.length = (rule.capture actual).length)
    (hr : ∀ i (hi : i < (rule.capture actual).length),
      ParRed Γ (rule.capture actual)[i] (arguments[i]'(by omega)))
    (hF : EtaPar Γ (VExpr.mkApps (.elim actual.block actual.owner actual.levels) actual.arguments) F')
    (hM : EtaPar Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments) M')
    (ha : Γ ⊢ actual.expr : A) :
    ∃ d, ReflTransGen (Below Γ 3) (.app F' M') d ∧ EtaPar Γ (rule.rhs actual.levels arguments) d := by
  classical
  have ha' : Γ ⊢ .app (VExpr.mkApps (.elim actual.block actual.owner actual.levels) actual.arguments)
      (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments) : A := ha
  obtain ⟨_, _, tF, tM⟩ := ha'.app_inv henv hΓ
  obtain ⟨args', hargs', hy⟩ := EtaPar.collapse_elim hΓ hF tF
  have hnotpi : ∀ D B, ¬ Γ ⊢ VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
      actual.ctorArguments : .forallE D B := fun _ _ h => CaseRedex.major_not_pi henv hΓ hm h
  obtain ⟨fs₀, lsc', ps₀, hfs₀, cM, hdisj⟩ := EtaPar.collapse_major
    (kc := actual.ctorArguments.length) hΓ
    (fun hl' hs => let ⟨h1, h2, _⟩ := schema_struct_major hm hΓ hl' hs; ⟨h1, h2⟩) hM tM hnotpi rfl
  have hb := (EtaPar.full hΓ (.app hF hM) ha').hasType hΓ ha'
  have c₁ : ReflTransGen (Below Γ 3) (.app F' M')
      (.app (VExpr.mkApps (.elim actual.block actual.owner actual.levels) args') M') :=
    Below.ofParRedS (hy M') (by decide)
  have tb₁ := Below.hasType hΓ c₁ hb
  have c₂ := Below.app hΓ .rfl cM tb₁
  have tb₂ := Below.hasType hΓ c₂ tb₁
  have hps₀len : ps₀.length = actual.ctorArguments.length := by
    rcases hdisj with ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, h, _, _⟩
    · exact (Lean4Lean.List.Forall₂.length_eq hfs₀).symm
    · exact h
  -- the captured arguments of the collapsed eta side
  let nP := rule.numPrefix
  let nF := rule.numFields
  let len := actual.ctorArguments.length
  have hcapη : List.Forall₂ (EtaPar Γ) (rule.capture actual) (args'.take nP ++ ps₀.drop (len - nF)) := by
    unfold InductiveSignature.CaseSchema.AppliedRule.capture
    refine List.Forall₂.append' (List.forall₂_take hargs' _) ?_
    rcases hdisj with ⟨_, rfl⟩ | ⟨fam, info, _, hl', hcc, hkc, hlen₀, hdrop, hs'⟩
    · exact Lean4Lean.List.forall₂_drop hfs₀ _
    · obtain ⟨_, _, hnf⟩ := schema_struct_major hm hΓ hl' hs'
      have hk : len - nF = info.nparams + (len - nF - info.nparams) := by
        simp only [len, nF]; omega
      have hd : ps₀.drop (len - nF) = fs₀.drop (len - nF) := by
        rw [hk, ← List.drop_drop, ← List.drop_drop, hdrop]
      rw [hd]
      exact Lean4Lean.List.forall₂_drop hfs₀ _
  have htcap : ∀ x ∈ rule.capture actual, ∃ T, Γ ⊢ x : T := fun _ hx => hm.capture_typed hx
  obtain ⟨D, hD, eD⟩ := EtaPar.parRed_join_args hΓ IH (fun _ hx => sizeOf_capture hx) htcap
    hcapη (List.forall₂_of_getElem hl.symm fun i hi _ => hr i hi)
  obtain ⟨A', C', hcapD, hA', hC', hlA, hlC⟩ := capture_replace (fun _ => .rfl) hD
  let actual₃ : InductiveSignature.CaseSchema.Application :=
    { actual with arguments := A', ctorLevels := lsc', ctorArguments := C' }
  have hcap₃ : rule.capture actual₃ = D := by
    unfold InductiveSignature.CaseSchema.AppliedRule.capture
    simp only [actual₃, hlC, hps₀len]
    exact hcapD
  have hexpr₃ : actual₃.expr = .app (VExpr.mkApps (.elim actual.block actual.owner actual.levels) A')
      (VExpr.mkApps (.const actual.ctorName lsc') C') := rfl
  obtain ⟨_, _, tF₂, tM₂⟩ := tb₂.app_inv henv hΓ
  have c₃ : ReflTransGen (Below Γ 3)
      (.app (VExpr.mkApps (.elim actual.block actual.owner actual.levels) args')
        (VExpr.mkApps (.const actual.ctorName lsc') ps₀)) actual₃.expr := by
    rw [hexpr₃]
    exact Below.app hΓ (Below.mkApps hΓ .rfl hA' tF₂) (Below.mkApps hΓ .rfl hC' tM₂) tb₂
  have tb₃ := Below.hasType hΓ c₃ tb₂
  -- the case step at the developed application
  have hdefa : Γ ⊢ actual.expr ≡ actual₃.expr := by
    have h1 := (EtaPar.full hΓ (.app hF hM) ha').defeq hΓ ha'
    have h2 := Below.defeq hΓ ((c₁.trans c₂).trans c₃) hb
    exact ⟨_, h1.trans h2⟩
  have hcapdef : List.Forall₂ (IsDefEqU env univs Γ) (rule.capture actual) (rule.capture actual₃) := by
    rw [hcap₃]
    have hl1 := Lean4Lean.List.Forall₂.length_eq hcapη
    have hl2 := Lean4Lean.List.Forall₂.length_eq hD
    apply List.forall₂_of_getElem (hl1.trans hl2)
    intro i hi hi'
    have h1 := case_forall₂_get hcapη hi (by omega)
    have h2 := case_forall₂_get hD (by omega) hi'
    obtain ⟨T, ht⟩ := htcap _ (List.getElem_mem hi)
    have d1 := (EtaPar.full hΓ h1 ht).defeq hΓ ht
    exact ⟨_, d1.trans (Below.defeq hΓ h2 d1.hasType.2)⟩
  have hcl : List.Forall₂ (· ≈ ·) actual₃.ctorLevels actual.ctorLevels := by
    rcases hdisj with ⟨rfl, _⟩ | ⟨fam, info, ps, hl', hcc, hkc, hlen₀, _, hs'⟩
    · exact VLevel.forall₂_equiv_refl _
    · rw [hcc] at hs'
      obtain ⟨idx, hT⟩ := HasType.ctorApp_type hΓ hl' hs' (by rw [← hkc])
      obtain ⟨_, hsort⟩ := hs'.isType henv hΓ
      exact (IsDefEqU.structApp_inv henv hΓ hl' hT hsort).1
  have hm₃ := hm.transport hΓ (actual' := actual₃) rfl rfl rfl rfl hcl (by simp [actual₃, hlA, Lean4Lean.List.Forall₂.length_eq hargs'])
    (by simp [actual₃, hlC, hps₀len]) hcapdef hdefa
  have hlen₃ : D.length = (rule.capture actual₃).length := by rw [hcap₃]
  have hfire : ParRed Γ actual₃.expr (rule.rhs actual₃.levels D) :=
    .schema hm₃ hlen₃ fun i hi => by
      have : (rule.capture actual₃)[i] = D[i]'(by rw [← hcap₃]; exact hi) := by
        simp only [hcap₃]
      rw [this]; exact .rfl
  refine ⟨_, ((c₁.trans c₂).trans c₃).tail ⟨1, by decide, hfire⟩, ?_⟩
  simp only [InductiveSignature.CaseSchema.AppliedRule.rhs]
  exact EtaPar.congrRel.instantiateParams_args eD

theorem EtaPar.parRed_aux : ∀ n, EPBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have IH : EPBelow (sizeOf a) := fun h => ih (by omega)
  clear ih hsz
  induction H generalizing c A with
  | bvar | sort | const | elim =>
    exact ⟨c, .tail .rfl ⟨1, by decide, H2⟩, .rfl⟩
  | @app _ f f' x x' hF hX _ _ =>
    have hb := (EtaPar.full hΓ (.app hF hX) ha).hasType hΓ ha
    cases H2 with
    | app hf hx =>
      obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
      obtain ⟨df, cf, ef⟩ := IH (by simp; omega) hΓ hF hf tf
      obtain ⟨dx, cx, ex⟩ := IH (by simp; omega) hΓ hX hx tx
      exact ⟨_, Below.app hΓ cf cx hb, .app ef ex⟩
    | beta ht hu =>
      obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
      have ⟨⟨_, tD⟩, _, tt⟩ := tf.lam_inv henv hΓ
      have ⟨⟨_, hw⟩, _⟩ := (tf.uniqU henv hΓ (HasType.lam tD tt)).forallE_inv henv hΓ
      have tx' := hw.defeq tx
      have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨D', t', hD', ht', hy⟩ := EtaPar.collapse_lam hΓ hF tf
      obtain ⟨dt, ct, et⟩ := IH (by simp; omega) hΓ' ht' ht tt
      obtain ⟨dx, cx, ex⟩ := IH (by simp; omega) hΓ hX hu tx'
      have c₁ : ReflTransGen (Below _ 3) (.app f' x') (.app (.lam D' t') x') :=
        Below.ofParRedS (hy x') (by decide)
      have tt' := (EtaPar.full hΓ' ht' tt).hasType hΓ' tt
      have tx'' := (EtaPar.full hΓ hX tx').hasType hΓ tx'
      have c₂ := Below.inst0 hΓ ct cx tt' tx''
      refine ⟨_, (c₁.tail ⟨1, by decide, (ParRed.beta .rfl .rfl : ParRed _ _ (t'.inst x'))⟩).trans c₂, ?_⟩
      exact EtaPar.instN .zero hΓ' ex (hu.hasType hΓ tx') et (ht.hasType hΓ' tt)
    | extra hp hm hck hargs =>
      obtain ⟨sp, rfl⟩ := Params.pat_simple hp
      cases sp with
      | defn => cases hm
      | iota rc mr cc kc => exact EtaPar.parRed_iota hΓ IH hp hm hck hargs hF hX rfl ha
    | schema hm hl hr => exact EtaPar.parRed_schema hΓ IH hm hl hr hF hX ha
  | @proj _ m m' family index hM _ =>
    have hb := (EtaPar.full hΓ (.proj hM) ha).hasType hΓ ha
    cases H2 with
    | proj hm =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨dm, cm, em⟩ := IH (by simp; omega) hΓ hM hm lm.hasType.2
      exact ⟨_, Below.proj hΓ cm hb, .proj em⟩
    | extra _ hm => cases hm
  | @lam _ D D' t t' hD ht _ _ =>
    have hb := (EtaPar.full hΓ (.lam hD ht) ha).hasType hΓ ha
    cases H2 with
    | lam hD₂ ht₂ =>
      obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.lam_inv henv hΓ
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨dD, cD, eD⟩ := IH (by simp; omega) hΓ hD hD₂ tD
      obtain ⟨dt, ct, et⟩ := IH (by simp; omega) hΓ' ht ht₂ tt
      have hDD' := (EtaPar.full hΓ hD tD).defeq hΓ tD
      have hDD₂ := hD₂.defeq hΓ tD
      have tt' := (EtaPar.full hΓ' ht tt).hasType hΓ' tt
      have tt₂ := ht₂.hasType hΓ' tt
      exact ⟨_, Below.lam hΓ cD (Below.defeqDFC hΓ (.succ .zero hDD') ct tt') hb,
        .lam eD (et.defeqDFC hΓ (.succ .zero hDD₂) tt₂)⟩
    | extra _ hm => cases hm
  | @forallE _ D D' t t' hD ht _ _ =>
    have hb := (EtaPar.full hΓ (.forallE hD ht) ha).hasType hΓ ha
    cases H2 with
    | forallE hD₂ ht₂ =>
      obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.forallE_inv henv
      have hΓ' : OnCtx (D :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
      obtain ⟨dD, cD, eD⟩ := IH (by simp; omega) hΓ hD hD₂ tD
      obtain ⟨dt, ct, et⟩ := IH (by simp; omega) hΓ' ht ht₂ tt
      have hDD' := (EtaPar.full hΓ hD tD).defeq hΓ tD
      have hDD₂ := hD₂.defeq hΓ tD
      have tt' := (EtaPar.full hΓ' ht tt).hasType hΓ' tt
      have tt₂ := ht₂.hasType hΓ' tt
      exact ⟨_, Below.forallE hΓ cD (Below.defeqDFC hΓ (.succ .zero hDD') ct tt') hb,
        .forallE eD (et.defeqDFC hΓ (.succ .zero hDD₂) tt₂)⟩
    | extra _ hm => cases hm
  | funEta H₀ HD hty ih =>
    obtain ⟨d₀, c₀, e₀⟩ := ih hΓ H2 ha IH
    have hc := H2.hasType hΓ hty
    have hb := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    obtain ⟨h1, h2⟩ := EtaPar.root_fun hΓ HD hc c₀ e₀ hb
    exact ⟨_, h1, h2⟩
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    obtain ⟨d₀, c₀, e₀⟩ := ih hΓ H2 ha IH
    have hc := H2.hasType hΓ hs
    have hcexp := (FullReduction.structExpand (.tail .rfl (.core H2))).hasType hΓ hexp
    have hb := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    obtain ⟨h1, h2⟩ := EtaPar.root_struct hΓ hl hp hi hlen hps hc hcexp c₀ e₀ hb
    exact ⟨_, h1, h2⟩
end EtaParRed


section EtaPeak

/-- Two eta developments each extended by one parallel eta step meet after lower steps. -/
def Join3 (Γ : List VExpr) (b c : VExpr) : Prop :=
  ∃ d, (∃ b₁, EtaPar Γ b b₁ ∧ ReflTransGen (Below Γ 3) b₁ d) ∧
    (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d)

theorem Join3.symm (H : Join3 Γ b c) : Join3 Γ c b := let ⟨d, h1, h2⟩ := H; ⟨d, h2, h1⟩

theorem EtaPar.mkApps_args (H : List.Forall₂ (EtaPar Γ) args args') :
    EtaPar Γ (VExpr.mkApps f args) (VExpr.mkApps f args') := EtaPar.congrRel.mkApps .rfl H

theorem EtaPar.expand_congr (H : EtaPar Γ e e') :
    EtaPar Γ (structExpand family info levels ps e) (structExpand family info levels ps e') := by
  unfold structExpand
  refine EtaPar.mkApps_args (List.Forall₂.append' (List.Forall₂.rfl fun _ _ => .rfl) ?_)
  apply List.forall₂_of_getElem (by simp)
  intro j _ _
  simpa only [List.getElem_map, List.getElem_range] using EtaPar.proj H

theorem Below.etaBody (hΓ : OnCtx Γ (env.IsType univs))
    (hchain : ReflTransGen (Below Γ n) b₀ d₀) (hb : Γ ⊢ .lam D' (.app b₀.lift (.bvar 0)) : T) :
    ReflTransGen (Below Γ n) (.lam D' (.app b₀.lift (.bvar 0))) (.lam D' (.app d₀.lift (.bvar 0))) := by
  obtain ⟨⟨_, tD'⟩, _, tbody⟩ := hb.lam_inv henv hΓ
  have hΓ' : OnCtx (D' :: Γ) (env.IsType univs) := ⟨hΓ, _, tD'⟩
  exact Below.lam hΓ .rfl (Below.app hΓ' (Below.weakN (Γ' := D' :: Γ) .one hchain) .rfl tbody) hb

theorem Join3.fun_left (hΓ : OnCtx Γ (env.IsType univs)) (J : Join3 Γ b₀ c)
    (HD : EtaPar Γ D D') (hc : Γ ⊢ c : .forallE D B)
    (hb : Γ ⊢ .lam D' (.app b₀.lift (.bvar 0)) : T) :
    Join3 Γ (.lam D' (.app b₀.lift (.bvar 0))) c := by
  obtain ⟨d₀, ⟨b₁, pb, cb⟩, ⟨c₁, pc, cc⟩⟩ := J
  have sb : EtaPar Γ (.lam D' (.app b₀.lift (.bvar 0))) (.lam D' (.app b₁.lift (.bvar 0))) :=
    .lam .rfl (.app (pb.weakN .one) .rfl)
  have tb₁ := (EtaPar.full hΓ sb hb).hasType hΓ hb
  have tc := (EtaPar.full hΓ pc hc).hasType hΓ hc
  have sc : EtaPar Γ c (.lam D' (.app c₁.lift (.bvar 0))) := .funEta pc HD hc
  have tc₁ := (EtaPar.full hΓ sc hc).hasType hΓ hc
  exact ⟨_, ⟨_, sb, Below.etaBody hΓ cb tb₁⟩, ⟨_, sc, Below.etaBody hΓ cc tc₁⟩⟩

theorem Join3.struct_left (hΓ : OnCtx Γ (env.IsType univs)) (J : Join3 Γ b₀ c)
    (hl : env.projections family info) (hp : ps.length = info.nparams) (hi : info.nindices = 0)
    (hlen : ps.length = ps'.length)
    (hps : ∀ i (h : i < ps.length) (h' : i < ps'.length), EtaPar Γ ps[i] ps'[i])
    (hc : Γ ⊢ c : VExpr.mkApps (.const family levels) ps)
    (hcexp : Γ ⊢ structExpand family info levels ps c : VExpr.mkApps (.const family levels) ps)
    (hb : Γ ⊢ structExpand family info levels ps' b₀ : T) :
    Join3 Γ (structExpand family info levels ps' b₀) c := by
  obtain ⟨d₀, ⟨b₁, pb, cb⟩, ⟨c₁, pc, cc⟩⟩ := J
  have sb := EtaPar.expand_congr (family := family) (info := info) (levels := levels) (ps := ps') pb
  have tb₁ := (EtaPar.full hΓ sb hb).hasType hΓ hb
  have sc : EtaPar Γ c (structExpand family info levels ps' c₁) :=
    .structEta pc hlen hps hl hp hi hc hcexp
  have tc₁ := (EtaPar.full hΓ sc hc).hasType hΓ hc
  exact ⟨_, ⟨_, sb, Below.expand hΓ cb tb₁⟩, ⟨_, sc, Below.expand hΓ cc tc₁⟩⟩

theorem Join3.app (hΓ : OnCtx Γ (env.IsType univs)) (hf : Join3 Γ f₁ f₂) (hx : Join3 Γ x₁ x₂)
    (h₁ : Γ ⊢ .app f₁ x₁ : T) (h₂ : Γ ⊢ .app f₂ x₂ : T) : Join3 Γ (.app f₁ x₁) (.app f₂ x₂) := by
  obtain ⟨df, ⟨F₁, pF₁, cF₁⟩, ⟨F₂, pF₂, cF₂⟩⟩ := hf
  obtain ⟨dx, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hx
  have s₁ : EtaPar Γ (.app f₁ x₁) (.app F₁ X₁) := .app pF₁ pX₁
  have s₂ : EtaPar Γ (.app f₂ x₂) (.app F₂ X₂) := .app pF₂ pX₂
  exact ⟨_, ⟨_, s₁, Below.app hΓ cF₁ cX₁ ((EtaPar.full hΓ s₁ h₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.app hΓ cF₂ cX₂ ((EtaPar.full hΓ s₂ h₂).hasType hΓ h₂)⟩⟩

theorem Join3.proj (hΓ : OnCtx Γ (env.IsType univs)) (hm : Join3 Γ m₁ m₂)
    (h₁ : Γ ⊢ .proj s i m₁ : T) (h₂ : Γ ⊢ .proj s i m₂ : T) :
    Join3 Γ (.proj s i m₁) (.proj s i m₂) := by
  obtain ⟨dm, ⟨M₁, pM₁, cM₁⟩, ⟨M₂, pM₂, cM₂⟩⟩ := hm
  have s₁ : EtaPar Γ (.proj s i m₁) (.proj s i M₁) := .proj pM₁
  have s₂ : EtaPar Γ (.proj s i m₂) (.proj s i M₂) := .proj pM₂
  exact ⟨_, ⟨_, s₁, Below.proj hΓ cM₁ ((EtaPar.full hΓ s₁ h₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.proj hΓ cM₂ ((EtaPar.full hΓ s₂ h₂).hasType hΓ h₂)⟩⟩


theorem Join3.lam (hΓ : OnCtx Γ (env.IsType univs)) (tD : Γ ⊢ D : .sort u)
    (hD : Join3 Γ D₁ D₂) (ht : Join3 (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (h₁ : Γ ⊢ .lam D₁ t₁ : T₁) (h₂ : Γ ⊢ .lam D₂ t₂ : T₂) :
    Join3 Γ (.lam D₁ t₁) (.lam D₂ t₂) := by
  obtain ⟨dD, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hD
  obtain ⟨dt, ⟨S₁, pS₁, cS₁⟩, ⟨S₂, pS₂, cS₂⟩⟩ := ht
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have tS₁ := (EtaPar.full hΓD pS₁ tt₁).hasType hΓD tt₁
  have tS₂ := (EtaPar.full hΓD pS₂ tt₂).hasType hΓD tt₂
  have eX₁ := e₁.trans ((EtaPar.full hΓ pX₁ e₁.hasType.2).defeq hΓ e₁.hasType.2)
  have eX₂ := e₂.trans ((EtaPar.full hΓ pX₂ e₂.hasType.2).defeq hΓ e₂.hasType.2)
  have s₁ : EtaPar Γ (.lam D₁ t₁) (.lam X₁ S₁) := .lam pX₁ (pS₁.defeqDFC hΓ (.succ .zero e₁) tt₁)
  have s₂ : EtaPar Γ (.lam D₂ t₂) (.lam X₂ S₂) := .lam pX₂ (pS₂.defeqDFC hΓ (.succ .zero e₂) tt₂)
  exact ⟨_, ⟨_, s₁, Below.lam hΓ cX₁ (Below.defeqDFC hΓ (.succ .zero eX₁) cS₁ tS₁)
      ((EtaPar.full hΓ s₁ h₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.lam hΓ cX₂ (Below.defeqDFC hΓ (.succ .zero eX₂) cS₂ tS₂)
      ((EtaPar.full hΓ s₂ h₂).hasType hΓ h₂)⟩⟩

theorem Join3.forallE (hΓ : OnCtx Γ (env.IsType univs)) (tD : Γ ⊢ D : .sort u)
    (hD : Join3 Γ D₁ D₂) (ht : Join3 (D :: Γ) t₁ t₂)
    (e₁ : Γ ⊢ D ≡ D₁ : .sort u) (e₂ : Γ ⊢ D ≡ D₂ : .sort u)
    (tt₁ : D :: Γ ⊢ t₁ : B₁) (tt₂ : D :: Γ ⊢ t₂ : B₂)
    (h₁ : Γ ⊢ .forallE D₁ t₁ : T₁) (h₂ : Γ ⊢ .forallE D₂ t₂ : T₂) :
    Join3 Γ (.forallE D₁ t₁) (.forallE D₂ t₂) := by
  obtain ⟨dD, ⟨X₁, pX₁, cX₁⟩, ⟨X₂, pX₂, cX₂⟩⟩ := hD
  obtain ⟨dt, ⟨S₁, pS₁, cS₁⟩, ⟨S₂, pS₂, cS₂⟩⟩ := ht
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, tD⟩
  have tS₁ := (EtaPar.full hΓD pS₁ tt₁).hasType hΓD tt₁
  have tS₂ := (EtaPar.full hΓD pS₂ tt₂).hasType hΓD tt₂
  have eX₁ := e₁.trans ((EtaPar.full hΓ pX₁ e₁.hasType.2).defeq hΓ e₁.hasType.2)
  have eX₂ := e₂.trans ((EtaPar.full hΓ pX₂ e₂.hasType.2).defeq hΓ e₂.hasType.2)
  have s₁ : EtaPar Γ (.forallE D₁ t₁) (.forallE X₁ S₁) :=
    .forallE pX₁ (pS₁.defeqDFC hΓ (.succ .zero e₁) tt₁)
  have s₂ : EtaPar Γ (.forallE D₂ t₂) (.forallE X₂ S₂) :=
    .forallE pX₂ (pS₂.defeqDFC hΓ (.succ .zero e₂) tt₂)
  exact ⟨_, ⟨_, s₁, Below.forallE hΓ cX₁ (Below.defeqDFC hΓ (.succ .zero eX₁) cS₁ tS₁)
      ((EtaPar.full hΓ s₁ h₁).hasType hΓ h₁)⟩,
    ⟨_, s₂, Below.forallE hΓ cX₂ (Below.defeqDFC hΓ (.succ .zero eX₂) cS₂ tS₂)
      ((EtaPar.full hΓ s₂ h₂).hasType hΓ h₂)⟩⟩


/-- Peaks of parallel eta steps below a size. -/
abbrev EEBelow (s : Nat) : Prop :=
  ∀ {Γ a b c A}, sizeOf a < s → OnCtx Γ (env.IsType univs) → EtaPar Γ a b → EtaPar Γ a c →
    Γ ⊢ a : A → Join3 Γ b c

theorem EtaPar.peak_app (hΓ : OnCtx Γ (env.IsType univs)) (IH : EEBelow (sizeOf (VExpr.app f x)))
    (hF : EtaPar Γ f f₁) (hX : EtaPar Γ x x₁) (H2 : EtaPar Γ (.app f x) c)
    (ha : Γ ⊢ .app f x : A) : Join3 Γ (.app f₁ x₁) c := by
  have HB : EtaPar Γ (.app f x) (.app f₁ x₁) := .app hF hX
  generalize hE : VExpr.app f x = E at H2 ha IH HB
  induction H2 generalizing A with
  | app hf₂ hx₂ =>
    cases hE
    obtain ⟨_, _, tf, tx⟩ := ha.app_inv henv hΓ
    exact Join3.app hΓ (IH (by simp; omega) hΓ hF hf₂ tf) (IH (by simp; omega) hΓ hX hx₂ tx)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.app hf₂ hx₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hF hX rfl ha IH HB
    exact (Join3.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hF hX rfl ha IH HB
    exact (Join3.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

theorem EtaPar.peak_proj (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EEBelow (sizeOf (VExpr.proj s i m)))
    (hM : EtaPar Γ m m₁) (H2 : EtaPar Γ (.proj s i m) c)
    (ha : Γ ⊢ .proj s i m : A) : Join3 Γ (.proj s i m₁) c := by
  have HB : EtaPar Γ (.proj s i m) (.proj s i m₁) := .proj hM
  generalize hE : VExpr.proj s i m = E at H2 ha IH HB
  induction H2 generalizing A with
  | proj hm₂ =>
    cases hE
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, lm, _, _⟩ := ha.proj_inv henv hΓ
    exact Join3.proj hΓ (IH (by simp; omega) hΓ hM hm₂ lm.hasType.2)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.proj hm₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hM rfl ha IH HB
    exact (Join3.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hM rfl ha IH HB
    exact (Join3.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

theorem EtaPar.peak_lam (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EEBelow (sizeOf (VExpr.lam D t)))
    (hD : EtaPar Γ D D₁) (ht : EtaPar (D :: Γ) t t₁) (H2 : EtaPar Γ (.lam D t) c)
    (ha : Γ ⊢ .lam D t : A) : Join3 Γ (.lam D₁ t₁) c := by
  have HB : EtaPar Γ (.lam D t) (.lam D₁ t₁) := .lam hD ht
  generalize hE : VExpr.lam D t = E at H2 ha IH HB
  induction H2 generalizing A with
  | lam hD₂ ht₂ =>
    cases hE
    obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.lam_inv henv hΓ
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
    exact Join3.lam hΓ tD (IH (by simp; omega) hΓ hD hD₂ tD) (IH (by simp; omega) hΓ' ht ht₂ tt)
      ((EtaPar.full hΓ hD tD).defeq hΓ tD) ((EtaPar.full hΓ hD₂ tD).defeq hΓ tD)
      ((EtaPar.full hΓ' ht tt).hasType hΓ' tt) ((EtaPar.full hΓ' ht₂ tt).hasType hΓ' tt)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.lam hD₂ ht₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (Join3.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (Join3.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

theorem EtaPar.peak_forallE (hΓ : OnCtx Γ (env.IsType univs))
    (IH : EEBelow (sizeOf (VExpr.forallE D t)))
    (hD : EtaPar Γ D D₁) (ht : EtaPar (D :: Γ) t t₁) (H2 : EtaPar Γ (.forallE D t) c)
    (ha : Γ ⊢ .forallE D t : A) : Join3 Γ (.forallE D₁ t₁) c := by
  have HB : EtaPar Γ (.forallE D t) (.forallE D₁ t₁) := .forallE hD ht
  generalize hE : VExpr.forallE D t = E at H2 ha IH HB
  induction H2 generalizing A with
  | forallE hD₂ ht₂ =>
    cases hE
    obtain ⟨⟨_, tD⟩, _, tt⟩ := ha.forallE_inv henv
    have hΓ' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, tD⟩
    exact Join3.forallE hΓ tD (IH (by simp; omega) hΓ hD hD₂ tD) (IH (by simp; omega) hΓ' ht ht₂ tt)
      ((EtaPar.full hΓ hD tD).defeq hΓ tD) ((EtaPar.full hΓ hD₂ tD).defeq hΓ tD)
      ((EtaPar.full hΓ' ht tt).hasType hΓ' tt) ((EtaPar.full hΓ' ht₂ tt).hasType hΓ' tt)
      ((EtaPar.full hΓ HB ha).hasType hΓ ha) ((EtaPar.full hΓ (.forallE hD₂ ht₂) ha).hasType hΓ ha)
  | funEta H₀ HD hty ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hty
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (Join3.fun_left hΓ hj.symm HD hb' hc).symm
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    subst hE
    have hc := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hb' := (EtaPar.full hΓ HB ha).hasType hΓ hs
    have hbexp := (FullReduction.structExpand (EtaPar.full hΓ HB ha)).hasType hΓ hexp
    have hj := ih hΓ hD ht rfl ha IH HB
    exact (Join3.struct_left hΓ hj.symm hl hp hi hlen hps hb' hbexp hc).symm
  | _ => cases hE

theorem EtaPar.peak_aux : ∀ n, EEBelow n := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ a b c A hsz hΓ H H2 ha
  have IH : EEBelow (sizeOf a) := fun h => ih (by omega)
  clear ih hsz
  induction H generalizing c A with
  | bvar | sort | const | elim => exact ⟨c, ⟨c, H2, .rfl⟩, ⟨c, .rfl, .rfl⟩⟩
  | app hF hX _ _ => exact EtaPar.peak_app hΓ IH hF hX H2 ha
  | proj hM _ => exact EtaPar.peak_proj hΓ IH hM H2 ha
  | lam hD ht _ _ => exact EtaPar.peak_lam hΓ IH hD ht H2 ha
  | forallE hD ht _ _ => exact EtaPar.peak_forallE hΓ IH hD ht H2 ha
  | funEta H₀ HD hty ih =>
    have hb := (EtaPar.full hΓ (.funEta H₀ HD hty) ha).hasType hΓ ha
    have hc := (EtaPar.full hΓ H2 ha).hasType hΓ hty
    exact Join3.fun_left hΓ (ih hΓ H2 ha IH) HD hc hb
  | structEta H₀ hlen hps hl hp hi hs hexp ih =>
    have hb := (EtaPar.full hΓ (.structEta H₀ hlen hps hl hp hi hs hexp) ha).hasType hΓ ha
    have hc := (EtaPar.full hΓ H2 ha).hasType hΓ hs
    have hcexp := (FullReduction.structExpand (EtaPar.full hΓ H2 ha)).hasType hΓ hexp
    exact Join3.struct_left hΓ (ih hΓ H2 ha IH) hl hp hi hlen hps hc hcexp hb

end EtaPeak

section Levels

/-! ### Local diagrams -/

theorem levelZero_joinable (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (LevelRel Γ 0) := by
  have key : ∀ {a b}, ReflTransGen (LevelRel Γ 0) a b → a = b ∨ NormalEq₀ Γ a b := by
    intro a b H
    induction H with
    | rfl => exact .inl rfl
    | tail _ h ih =>
      obtain ⟨_, h⟩ := h
      rcases ih with rfl | ih
      · exact .inr h
      · exact .inr (ih.trans hΓ h)
  intro a b c hb hc
  rcases key hb with rfl | hb'
  · exact ⟨c, hc, .rfl⟩
  have ⟨_, hab⟩ := NormalEqF.defeq hΓ hb'
  rcases key hc with rfl | hc'
  · exact ⟨b, .rfl, .tail .rfl ⟨⟨_, hab.hasType.1⟩, hb'⟩⟩
  · exact ⟨c, .tail .rfl ⟨⟨_, hab.hasType.2⟩, (hb'.symm hΓ).trans hΓ hc'⟩, .rfl⟩




theorem DeltaPar.peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, (∃ b₁, DeltaPar Γ b b₁ ∧ ReflTransGen (Below Γ 2) b₁ d) ∧
      (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d) :=
  DeltaPar.peak_aux _ (Nat.lt_succ_self _) hΓ H1 H2 ha

theorem DeltaPar.parRed_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 2) b d ∧
      (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d) := by
  obtain ⟨d₁, d₂, h1, h2, h3⟩ := DeltaPar.parRed_diamond hΓ H1 H2 ha
  exact ⟨d₂, (Below.single (k := 1) (by decide) h1).tail ⟨0, by decide, h3⟩, d₂, h2, .rfl⟩

theorem EtaPar.peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : EtaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, (∃ b₁, EtaPar Γ b b₁ ∧ ReflTransGen (Below Γ 3) b₁ d) ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) :=
  EtaPar.peak_aux _ (Nat.lt_succ_self _) hΓ H1 H2 ha

theorem EtaPar.parRed_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 3) b d ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := by
  obtain ⟨d, h1, h2⟩ := EtaPar.parRed_aux _ (Nat.lt_succ_self _) hΓ H1 H2 ha
  exact ⟨d, h1, d, h2, .rfl⟩

theorem EtaPar.deltaPar_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 3) b d ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := by
  obtain ⟨d, h1, h2⟩ := EtaPar.deltaPar_aux _ (Nat.lt_succ_self _) hΓ H1 H2 ha
  exact ⟨d, h1, d, h2, .rfl⟩

/-! ### Assembly -/

theorem levelled_loOptLo (hΓ : OnCtx Γ (env.IsType univs)) (hb : Γ ⊢ b : A)
    (H1 : LevelStep Γ n b b₁) (H2 : ReflTransGen (Below Γ n) b₁ d) :
    Levelled.LoOptLo (LevelRel Γ) n b d :=
  ⟨b, b₁, .rfl, .inr ⟨⟨_, hb⟩, H1⟩, Below.loStar hΓ H2 (H1.hasType hΓ hb)⟩

theorem levelled_optLo (hΓ : OnCtx Γ (env.IsType univs)) (hb : Γ ⊢ b : A)
    (H1 : LevelStep Γ n b b₁) (H2 : ReflTransGen (Below Γ n) b₁ d) :
    Levelled.OptLo (LevelRel Γ) n b d :=
  ⟨b₁, .inr ⟨⟨_, hb⟩, H1⟩, Below.loStar hΓ H2 (H1.hasType hΓ hb)⟩

theorem levelled_peak₁ (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, LevelRel Γ n a b → LevelRel Γ n a c →
      ∃ d, Levelled.LoOptLo (LevelRel Γ) n b d ∧ Levelled.LoOptLo (LevelRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨_, H2⟩
  have hb := H1.hasType hΓ ha
  have hc := H2.hasType hΓ ha
  match n, H1, H2 with
  | 1, H1, H2 =>
    obtain ⟨b₁, c₁, h1, h2, h3⟩ := ParRed.church_rosser (η := false) hΓ ha H1 H2
    exact ⟨b₁, levelled_loOptLo hΓ hb (n := 1) h1 .rfl,
      levelled_loOptLo hΓ hc (n := 1) h2 (Below.single (k := 0) (by decide) (h3.symm hΓ))⟩
  | 2, H1, H2 =>
    obtain ⟨d, ⟨b₁, h1, h2⟩, ⟨c₁, h3, h4⟩⟩ := DeltaPar.peak hΓ H1 H2 ha
    exact ⟨d, levelled_loOptLo hΓ hb (n := 2) h1 h2, levelled_loOptLo hΓ hc (n := 2) h3 h4⟩
  | 3, H1, H2 =>
    obtain ⟨d, ⟨b₁, h1, h2⟩, ⟨c₁, h3, h4⟩⟩ := EtaPar.peak hΓ H1 H2 ha
    exact ⟨d, levelled_loOptLo hΓ hb (n := 3) h1 h2, levelled_loOptLo hΓ hc (n := 3) h3 h4⟩
  | n + 4, H1, _ => exact H1.elim

theorem levelled_peak₂ (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, LevelRel Γ n a b → Levelled.Lo (LevelRel Γ) n a c →
      ∃ d, Levelled.LoStar (LevelRel Γ) n b d ∧ Levelled.OptLo (LevelRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨k, hk, _, H2⟩
  have hb := H1.hasType hΓ ha
  have hc := H2.hasType hΓ ha
  have mirror : ∀ {c'}, LevelStep Γ n c c' → NormalEq₀ Γ c' b →
      ∃ d, Levelled.LoStar (LevelRel Γ) n b d ∧ Levelled.OptLo (LevelRel Γ) n c d :=
    fun h1 h2 => ⟨b, .rfl, levelled_optLo hΓ hc h1 (Below.single (k := 0) hn h2)⟩
  match n, k, hk, H1, H2 with
  | 1, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 2, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 3, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 2, 1, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := DeltaPar.parRed_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 2) h2 h3⟩
  | 3, 1, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := EtaPar.parRed_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 3) h2 h3⟩
  | 3, 2, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := EtaPar.deltaPar_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 3) h2 h3⟩
  | n + 4, _, _, H1, _ => exact H1.elim

theorem levelled_joinable (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (Levelled.Lo (LevelRel Γ) 4) :=
  Levelled.joinable (levelZero_joinable hΓ) (levelled_peak₁ hΓ) (levelled_peak₂ hΓ) 3

end Levels

section Strip

/-- Union of the three reducing level relations. -/
def UpStep (Γ : List VExpr) (a b : VExpr) : Prop :=
  ParRed Γ a b ∨ DeltaPar Γ a b ∨ EtaPar Γ a b

theorem UpStep.below (H : ReflTransGen (UpStep Γ) a b) : ReflTransGen (Below Γ 4) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih =>
    refine .tail ih ?_
    rcases h with h | h | h
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩

theorem UpStep.congr {f : VExpr → VExpr} {g : List VExpr → List VExpr}
    (hf : ∀ {a b}, UpStep (g Γ) a b → UpStep Γ (f a) (f b))
    (H : ReflTransGen (UpStep (g Γ)) a b) : ReflTransGen (UpStep Γ) (f a) (f b) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (hf h)

theorem FullStep.upStep (H : FullStep Γ e e') : ReflTransGen (UpStep Γ) e e' := by
  induction H with
  | core h => exact .tail .rfl (.inl h)
  | delta h => exact .tail .rfl (.inr (.inl (.delta rfl (fun _ _ _ => .rfl) h)))
  | quotDelta h => exact .tail .rfl (.inr (.inl (.quotDelta rfl (fun _ _ _ => .rfl) h)))
  | projIota hl hs hi ht =>
    exact .tail .rfl (.inr (.inl (.projIota rfl (fun _ _ _ => .rfl) hl hs hi ht)))
  | structEta hl hp hi hs ht =>
    exact .tail .rfl (.inr (.inr (.structEta .rfl rfl (fun _ _ _ => .rfl) hl hp hi hs ht)))
  | funEta ht => exact .tail .rfl (.inr (.inr (.funEta .rfl .rfl ht)))
  | @app _ f f' a a' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := id) (f := (VExpr.app · a)) ?_ ih1).trans
      (UpStep.congr (g := id) (f := VExpr.app f') ?_ ih2)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.app h .rfl)
        | exact .inr (.inl (.app h .rfl))
        | exact .inr (.inr (.app h .rfl))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.app .rfl h)
        | exact .inr (.inl (.app .rfl h))
        | exact .inr (.inr (.app .rfl h))
  | proj _ ih =>
    refine UpStep.congr (g := id) ?_ ih
    rintro _ _ (h | h | h) <;> first
      | exact .inl (.proj h)
      | exact .inr (.inl (.proj h))
      | exact .inr (.inr (.proj h))
  | @lam _ d d' b b' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := (d :: ·)) (f := VExpr.lam d) ?_ ih2).trans
      (UpStep.congr (g := id) (f := (VExpr.lam · b')) ?_ ih1)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.lam .rfl h)
        | exact .inr (.inl (.lam .rfl h))
        | exact .inr (.inr (.lam .rfl h))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.lam h .rfl)
        | exact .inr (.inl (.lam h .rfl))
        | exact .inr (.inr (.lam h .rfl))
  | @forallE _ d d' b b' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := (d :: ·)) (f := VExpr.forallE d) ?_ ih2).trans
      (UpStep.congr (g := id) (f := (VExpr.forallE · b')) ?_ ih1)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.forallE .rfl h)
        | exact .inr (.inl (.forallE .rfl h))
        | exact .inr (.inr (.forallE .rfl h))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.forallE h .rfl)
        | exact .inr (.inl (.forallE h .rfl))
        | exact .inr (.inr (.forallE h .rfl))

theorem FullReduction.below (H : FullReduction Γ e e') : ReflTransGen (Below Γ 4) e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.trans (UpStep.below h.upStep)

/-- The required global strip property: one full step commutes with an entire
finite development, up to normal equality. -/
theorem FullStep.strip (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (step : FullStep Γ source left) (development : FullReduction Γ source right) :
    ∃ left' right', FullReduction Γ left left' ∧ FullReduction Γ right right' ∧
      NormalEq Γ left' right' := by
  have hl := UpStep.below step.upStep
  have hr := development.below
  obtain ⟨d, h1, h2⟩ := levelled_joinable hΓ source left right
    (Below.loStar hΓ hl ht) (Below.loStar hΓ hr ht)
  obtain ⟨l', a1, a2⟩ := Below.full hΓ (Below.ofLoStar h1) (step.hasType hΓ ht)
  obtain ⟨r', b1, b2⟩ := Below.full hΓ (Below.ofLoStar h2) (development.hasType hΓ ht)
  exact ⟨l', r', a1, b1, a2.trans hΓ (b2.symm hΓ)⟩

/-- Full confluence follows from the global strip property and transport
through normal equality. -/
theorem FullReduction.church_rosser (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (left : FullReduction Γ source l) (right : FullReduction Γ source r) :
    ∃ l' r', FullReduction Γ l l' ∧ FullReduction Γ r r' ∧ NormalEq Γ l' r' := by
  induction left with
  | rfl => exact ⟨_, _, right, .rfl, .refl (right.hasType hΓ ht)⟩
  | tail before step ih =>
    obtain ⟨l', r', hl, hr, heq⟩ := ih
    obtain ⟨l'', r'', hl'', hr'', heq'⟩ := step.strip hΓ (FullReduction.hasType hΓ before ht) hl
    obtain ⟨out, hout, heqOut⟩ := (heq.symm hΓ).fullReduction hΓ hr''
    exact ⟨l'', out, hl'', hr.trans hout, heq'.trans hΓ (heqOut.symm hΓ)⟩

end Strip

end Lean4Lean.VEnv
