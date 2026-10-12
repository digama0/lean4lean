import Lean4Lean.Theory.Typing.FullChurchRosser

/-! # Joinable typing

`HasTypeJ Γ e A` is a typing of `e` at `A` whose applications and constants are syntax-directed
and whose conversions are joins in the full presentation (`FullCRDefEq`). The confluence theorem
is strengthened to produce it: `IsDefEqStrong.church_rosserJ` proves, by induction on strong
derivations, that both sides of a definitional equality join and have joinable typings. The
strong system records the typings that the conversion nodes need (`IsDefEqStrong.hasType'`), so
every conversion of the produced typing is an instance of the induction hypothesis.

The coverage of the registered rules may then use the joinable typing of the instance
(`FullPatCoverageJ`): the arguments of a typed application are related to the domains of the
function's declared type by joins rather than by arbitrary definitional equalities. -/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

/-- Typing with joinable conversions. Applications and constants are typed structurally; other
terms by any declarative typing; conversions are joins. Every node records its declarative
typing. -/
inductive HasTypeJ : List VExpr → VExpr → VExpr → Prop where
  | const : env.constants c = some ci → Γ ⊢ .const c ls : ci.type.instL ls →
      HasTypeJ Γ (.const c ls) (ci.type.instL ls)
  | app : HasTypeJ Γ f (.forallE A B) → HasTypeJ Γ a A → Γ ⊢ .app f a : B.inst a →
      HasTypeJ Γ (.app f a) (B.inst a)
  | other : (∀ f a, e ≠ .app f a) → (∀ c ls, e ≠ .const c ls) → Γ ⊢ e : A → HasTypeJ Γ e A
  | defeq : Γ ⊢ A ≫≪ B → HasTypeJ Γ e A → Γ ⊢ e : B → HasTypeJ Γ e B

theorem HasTypeJ.hasType : HasTypeJ Γ e A → Γ ⊢ e : A
  | .const _ h | .app _ _ h | .other _ _ h | .defeq _ _ h => h

/-- Coverage of the registered rules, given the joinable typing of the instance. -/
class FullPatCoverageJ : Prop where
  pats : OnCtx Γ (env.IsType univs) → env.pats p r → p.Matches e m1 m2 →
    Γ ⊢ e : A → HasTypeJ Γ e A → r.2.Realizes m1 m2 chk →
    (∀ t ∈ chk, Γ ⊢ t.1 ≡ t.2.1 : t.2.2) →
    ∃ left right, FullReduction Γ e left ∧ FullReduction Γ (r.1.apply m1 m2) right ∧
      NormalEq Γ left right

omit [Params] in theorem not_app_bvar : ∀ f a, VExpr.bvar i ≠ .app f a := fun _ _ h => nomatch h
omit [Params] in theorem not_const_bvar : ∀ c ls, VExpr.bvar i ≠ .const c ls := fun _ _ h => nomatch h
omit [Params] in theorem not_app_sort : ∀ f a, VExpr.sort u ≠ .app f a := fun _ _ h => nomatch h
omit [Params] in theorem not_const_sort : ∀ c ls, VExpr.sort u ≠ .const c ls := fun _ _ h => nomatch h
omit [Params] in theorem not_app_lam : ∀ f a, VExpr.lam A b ≠ .app f a := fun _ _ h => nomatch h
omit [Params] in theorem not_const_lam : ∀ c ls, VExpr.lam A b ≠ .const c ls := fun _ _ h => nomatch h
omit [Params] in theorem not_app_forallE : ∀ f a, VExpr.forallE A b ≠ .app f a := fun _ _ h => nomatch h
omit [Params] in theorem not_const_forallE : ∀ c ls, VExpr.forallE A b ≠ .const c ls := fun _ _ h => nomatch h
omit [Params] in theorem not_app_proj : ∀ f a, VExpr.proj n i m ≠ .app f a := fun _ _ h => nomatch h
omit [Params] in theorem not_const_proj : ∀ c ls, VExpr.proj n i m ≠ .const c ls := fun _ _ h => nomatch h

/-- **Church-Rosser with joinable typings, for an earlier environment.** Both sides of a strong
definitional equality of an environment `E ≤ env` join in the full presentation of `env` and have
joinable typings at its type, given coverage of the registered rules of `E`. -/
theorem IsDefEqStrong.church_rosserJ_of [FullEquationCoverage] {E : VEnv} (hE : E ≤ env)
    (hcov : ∀ {Γ p r e m1 m2 A chk}, OnCtx Γ (env.IsType univs) → E.pats p r →
      p.Matches e m1 m2 → Γ ⊢ e : A → HasTypeJ Γ e A → r.2.Realizes m1 m2 chk →
      (∀ t ∈ chk, Γ ⊢ t.1 ≡ t.2.1 : t.2.2) →
      ∃ left right, FullReduction Γ e left ∧ FullReduction Γ (r.1.apply m1 m2) right ∧
        NormalEq Γ left right)
    (H : E.IsDefEqStrong univs Γ e₁ e₂ A) (hΓ : OnCtx Γ (env.IsType univs)) :
    Γ ⊢ e₁ ≫≪ e₂ ∧ HasTypeJ Γ e₁ A ∧ HasTypeJ Γ e₂ A := by
  have mk {Γ e₁ e₂ A e₁' e₂'} (H : Γ ⊢ e₁ ≡ e₂ : A)
      (h1 : FullReduction Γ e₁ e₁') (h2 : FullReduction Γ e₂ e₂') (h3 : NormalEq Γ e₁' e₂') :
      Γ ⊢ e₁ ≫≪ e₂ :=
    ⟨⟨_, H.hasType.1⟩, ⟨_, H.hasType.2⟩, _, _, h1, h2, h3⟩
  induction H with
  | bvar h1 h2 h3 =>
    have D := ((IsDefEqStrong.bvar h1 h2 h3).mono hE).defeq
    exact ⟨.refl hΓ D, .other not_app_bvar not_const_bvar D, .other not_app_bvar not_const_bvar D⟩
  | symm _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih hΓ
    exact ⟨h1.symm hΓ, h3, h2⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨h1, h2, -⟩ := ih1 hΓ
    obtain ⟨h1', -, h3'⟩ := ih2 hΓ
    exact ⟨h1.trans hΓ h1', h2, h3'⟩
  | sortDF h1 h2 h3 =>
    refine ⟨.normalEq hΓ (.sortDF h1 h2 h3), .other not_app_sort not_const_sort ?_,
      .other not_app_sort not_const_sort ?_⟩
    · exact ((IsDefEqStrong.sortDF h1 h2 h3).mono hE).defeq.hasType.1
    · exact ((IsDefEqStrong.sortDF h1 h2 h3).mono hE).defeq.hasType.2
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 _ ih8 =>
    have D := ((IsDefEqStrong.constDF h1 h2 h3 h4 h5 h6 h7 h8).mono hE).defeq
    exact ⟨.normalEq hΓ (.constDF (hE.constants h1) h2 h3 h4 h5), .const (hE.constants h1) D.hasType.1,
      .defeq ((ih8 hΓ).1.symm hΓ) (.const (hE.constants h1) (HasType.const (hE.constants h1) h3
        ((Lean4Lean.List.Forall₂.length_eq h5).symm.trans h4))) D.hasType.2⟩
  | appDF h1 h2 h3 h4 h5 h6 h7 _ _ ih5 ih6 ih7 =>
    have D := ((IsDefEqStrong.appDF h1 h2 h3 h4 h5 h6 h7).mono hE).defeq
    have d5 := (h5.mono hE).defeq
    have d6 := (h6.mono hE).defeq
    obtain ⟨c5, j5, j5'⟩ := ih5 hΓ
    obtain ⟨c6, j6, j6'⟩ := ih6 hΓ
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := c5
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := c6
    refine ⟨mk D (.app a1 b1) (.app a2 b2) <|
      .appDF (a1.hasType hΓ d5.hasType.1) (a2.hasType hΓ d5.hasType.2)
        (b1.hasType hΓ d6.hasType.1) (b2.hasType hΓ d6.hasType.2) a3 b3,
      .app j5 j6 D.hasType.1, ?_⟩
    exact .defeq ((ih7 hΓ).1.symm hΓ) (.app j5' j6' (d5.hasType.2.app d6.hasType.2)) D.hasType.2
  | projDF hinfo hlevels huvars hparams hindices hfield hfieldLevel hfieldTyping
      hLeft hRight hclosed hguard _ ihLeft ihRight =>
    have D := ((IsDefEqStrong.projDF hinfo hlevels huvars hparams hindices hfield hfieldLevel
      hfieldTyping hLeft hRight hclosed hguard).mono hE).defeq
    have majorCR := (ihLeft hΓ).1.symm hΓ |>.trans hΓ (ihRight hΓ).1
    obtain ⟨-, -, _, _, majorLeft, majorRight, majorNormal⟩ := majorCR
    have reducedAtLeft := majorLeft.proj.hasType hΓ D.hasType.1
    exact ⟨mk D majorLeft.proj majorRight.proj (.projDF reducedAtLeft majorNormal),
      .other not_app_proj not_const_proj D.hasType.1,
      .other not_app_proj not_const_proj D.hasType.2⟩
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih3 _ _ ih6 _ =>
    have D := ((IsDefEqStrong.lamDF h1 h2 h3 h4 h5 h6 h7).mono hE).defeq
    have d3 := (h3.mono hE).defeq
    have d6 := (h6.mono hE).defeq
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := (ih3 hΓ).1
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := (ih6 ⟨hΓ, _, d3.hasType.1⟩).1
    have b2' := b2.defeqDFC hΓ (.succ .zero d3) d6.hasType.2
    have := (a1.defeq hΓ d3.hasType.1).symm
    exact ⟨mk D (.lam a1 b1) (.lam a2 b2') <|
      .lamDF this.symm (this.symm.transU_l henv hΓ (a3.defeq hΓ)) b3,
      .other not_app_lam not_const_lam D.hasType.1,
      .other not_app_lam not_const_lam D.hasType.2⟩
  | forallEDF h1 h2 h3 h4 h5 ih3 ih4 _ =>
    have D := ((IsDefEqStrong.forallEDF h1 h2 h3 h4 h5).mono hE).defeq
    have d3 := (h3.mono hE).defeq
    have d4 := (h4.mono hE).defeq
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := (ih3 hΓ).1
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := (ih4 ⟨hΓ, _, d3.hasType.1⟩).1
    have b2' := b2.defeqDFC hΓ (.succ .zero d3) d4.hasType.2
    exact ⟨mk D (.forallE a1 b1) (.forallE a2 b2') <|
      .forallEDF (a1.defeq hΓ d3.hasType.1) a3 (b1.hasType ⟨hΓ, _, d3.hasType.1⟩ d4.hasType.1) b3,
      .other not_app_forallE not_const_forallE D.hasType.1,
      .other not_app_forallE not_const_forallE D.hasType.2⟩
  | defeqDF h1 h2 h3 ih2 ih3 =>
    have D := ((IsDefEqStrong.defeqDF h1 h2 h3).mono hE).defeq
    obtain ⟨c, j1, j2⟩ := ih3 hΓ
    have cA := (ih2 hΓ).1
    exact ⟨c, .defeq cA j1 D.hasType.1, .defeq cA j2 D.hasType.2⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ ih8 =>
    have D := ((IsDefEqStrong.beta h1 h2 h3 h4 h5 h6 h7 h8).mono hE).defeq
    have hlam := HasType.lam (h3.mono hE).defeq (h5.mono hE).defeq
    refine ⟨mk D (.tail .rfl (.core (.beta .rfl .rfl))) .rfl (.refl D.hasType.2),
      .app (.other not_app_lam not_const_lam hlam) (ih6 hΓ).2.1 D.hasType.1, (ih8 hΓ).2.1⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    have D := ((IsDefEqStrong.eta h1 h2 h3 h4 h5 h6 h7 h8).mono hE).defeq
    have := (h6.mono hE).defeq
    exact ⟨.normalEq hΓ <| .etaL this <| .refl <| .app (this.weak henv) (.bvar .zero),
      .other not_app_lam not_const_lam D.hasType.1, (ih6 hΓ).2.1⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 =>
    exact ⟨.normalEq hΓ <| .proofIrrel (h1.mono hE).defeq (h2.mono hE).defeq (h3.mono hE).defeq, (ih2 hΓ).2.1, (ih3 hΓ).2.1⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    have D := ((IsDefEqStrong.extra h1 h2 h3 h4 h5 h6 h7 h8 h9).mono hE).defeq
    obtain ⟨_, _, hleft, hright, hnormal⟩ := FullEquationCoverage.equations hΓ (hE.defeqs h1) h2 h3
    exact ⟨mk D hleft hright hnormal, (ih8 hΓ).2.1, (ih9 hΓ).2.1⟩
  | pat hp hm he hred hr hall ihe ihred _ =>
    have D := ((IsDefEqStrong.pat hp hm he hred hr hall).mono hE).defeq
    obtain ⟨_, _, hleft, hright, hnormal⟩ := hcov hΓ hp hm (he.mono hE).defeq
      (ihe hΓ).2.1 hr (fun t ht => ((hall t ht).mono hE).defeq)
    exact ⟨mk D hleft hright hnormal, (ihe hΓ).2.1, (ihred hΓ).2.1⟩
  | projIota hl hs hi ht ih2 ih4 =>
    have D := ((IsDefEqStrong.projIota hl hs hi ht).mono hE).defeq
    exact ⟨mk D (.tail .rfl (.projIota (hE.projections hl) (hs.mono hE).defeq hi (ht.mono hE).defeq)) .rfl (.refl (ht.mono hE).defeq),
      (ih2 hΓ).2.1, (ih4 hΓ).2.1⟩
  | structEta hl hp hi hs ht ih4 ih5 =>
    have D := ((IsDefEqStrong.structEta hl hp hi hs ht).mono hE).defeq
    exact ⟨mk D .rfl (.tail .rfl (.structEta (hE.projections hl) hp hi (hs.mono hE).defeq (ht.mono hE).defeq)) (.refl (ht.mono hE).defeq),
      (ih5 hΓ).2.1, (ih4 hΓ).2.1⟩
  | unitLike hl hp hi hf hs ht ih5 ih6 =>
    have D := ((IsDefEqStrong.unitLike hl hp hi hf hs ht).mono hE).defeq
    have hc := HasType.unitLike_constructor henv hΓ (hE.projections hl) hp hi hf (hs.mono hE).defeq
    have stepLeft := FullStep.structEta (hE.projections hl) hp hi (hs.mono hE).defeq (by simpa only [hf, List.range_zero,
      List.map_nil, List.append_nil] using hc)
    have stepRight := FullStep.structEta (hE.projections hl) hp hi (ht.mono hE).defeq (by simpa only [hf, List.range_zero,
      List.map_nil, List.append_nil] using hc)
    simp only [hf, List.range_zero, List.map_nil, List.append_nil] at stepLeft stepRight
    exact ⟨mk D (.tail .rfl stepLeft) (.tail .rfl stepRight) (.refl hc),
      (ih5 hΓ).2.1, (ih6 hΓ).2.1⟩


/-- **Church-Rosser with joinable typings.** Both sides of a strong definitional equality join
in the full presentation and have joinable typings at its type. -/
theorem IsDefEqStrong.church_rosserJ [FullEquationCoverage] [FullPatCoverageJ]
    (H : env.IsDefEqStrong univs Γ e₁ e₂ A) (hΓ : OnCtx Γ (env.IsType univs)) :
    Γ ⊢ e₁ ≫≪ e₂ ∧ HasTypeJ Γ e₁ A ∧ HasTypeJ Γ e₂ A :=
  H.church_rosserJ_of VEnv.LE.rfl (fun hΓ hp hm he hJ hr hall =>
    FullPatCoverageJ.pats hΓ hp hm he hJ hr hall) hΓ

/-- Coverage with joinable typings gives coverage: the joinable typing of a typed instance is
produced by `IsDefEqStrong.church_rosserJ`. -/
theorem FullPatCoverageJ.toFull [FullEquationCoverage] [FullPatCoverageJ] : FullPatCoverage where
  pats hΓ hp hm he hr hall :=
    FullPatCoverageJ.pats hΓ hp hm he
      ((IsDefEq.strong henv.orderedStrong hΓ he).church_rosserJ hΓ).2.1 hr hall

end Lean4Lean.VEnv
