import Lean4Lean.Theory.Typing.Strengthening.Pilot
import Lean4Lean.Theory.Typing.Strengthening.Kripke

/-! # Proof-irrelevance-aware certificates for the pilot calculus

Library integration of Astra's round 7(A) file (gpt-6-astra, 2026-10-09; the checked source
is `strengthening-context/round7/proof_aware/Round7.lean`), adapted to the `VEnv` namespace.
Everything is about the pilot calculus `Cert` of `Pilot.lean`.

* `Cert.weakN` (alias `pilot_weakN`): every pilot certificate is stable under insertion of
  binders, the converse of `Cert.descend`.
* `ProofLeaf Γ h h'`: a proof-irrelevance leaf that retains both synthesised propositions,
  their alignment certificate and the certified propositionhood of the left one. `toNorm`
  reads it as the `norm_proofIrrel` constructor; `sound`, `descend`, `weakN` are inherited.
* `ProofApp Γ f g a b`: the fused congruence `f a ~ g b` whose argument comparison is a
  `ProofLeaf`; it has no recursive proof-comparison premise (`proofApp_rule` is the derived
  pilot rule). Same three theorems.
* `ProofAware.no_phase_order`: no well-founded order on two global phase labels `type`,
  `proof` puts both prerequisites (`alignment : type → proof`, `argument : proof → type`)
  earlier.
* `ProofAware.no_layer_universe_rank`: for the rank (phase, universe of the common
  comparison type, any suffix), the two inequalities demanded by one alternation
  type-under-proof and proof-under-type are jointly unsatisfiable, for every suffix order.
* `ProofAware.Alternation`: the concrete six-entry context `P : Prop`, `F : P → Prop`,
  `h₀ h₁ : P`, `k₀ : F h₀`, `k₁ : F h₁`, with the actual pilot certificates
  `P ~ P` (`p_compare`), `h₀ ~ h₁` (`h_compare`, proof irrelevance), `F h₀ ~ F h₁`
  (`a_compare`, congruence through a proof) and `k₀ ~ k₁` (`k_compare`, proof irrelevance
  whose alignment is `a_compare`): proof, type, proof, type inside one finite certificate.
  `constructor_rank_obstruction` packages the certificates with `no_layer_universe_rank`;
  `local_stages_decrease` records the occurrence-dependent stage assignment that does order
  these four calls (a local observation, not a bound for substitution).
* Erasure: `typed_token_iff` (two proofs are equal iff their propositions are, given one
  proposition); `incompatible_proofs` (two well-formed proofs with non-convertible
  propositions); `untyped_erasure_reflection_false` and `single_token_typing_false`: any
  erasure sending every proof to one token neither reflects equality of the originals nor
  preserves their types, so an erasure must keep proposition alignment. -/

namespace Lean4Lean
namespace VEnv
open VExpr

variable {env : VEnv} {U : Nat}

/-! ## Weakening -/

/-- **Weakening.** Every pilot certificate survives the insertion of binders; the converse of
`Cert.descend`. Constant types and stored equations are closed, so their instances are fixed
by `liftN`; substitution and eta expansion commute with `liftN`. -/
theorem Cert.weakN (henv : env.WF) (h : Cert env U j Γ a b) (W : Ctx.LiftN n k Γ Δ) :
    Cert env U j Δ (a.liftN n k) (b.liftN n k) := by
  induction h generalizing k Δ with
  | ty_bvar h => exact .ty_bvar (h.weakN W)
  | ty_sort h => exact .ty_sort h
  | ty_const h1 h2 h3 =>
    simpa only [liftN, ((henv.ordered.closedC h1).instL).liftN_eq (Nat.zero_le k)] using
      (Cert.ty_const (Γ := Δ) h1 h2 h3)
  | ty_app _ _ _ _ ihf ihF iha ihA =>
    simpa only [liftN, liftN_inst_hi] using Cert.ty_app (ihf W) (ihF W) (iha W) (ihA W)
  | ty_lam _ _ _ ihA ihS ihb => exact .ty_lam (ihA W) (ihS W) (ihb W.succ)
  | ty_forallE _ _ _ _ ihA ihS ihB ihS' =>
    exact .ty_forallE (ihA W) (ihS W) (ihB W.succ) (ihS' W.succ)
  | step_bvar => exact .step_bvar
  | step_sort => exact .step_sort
  | step_const => exact .step_const
  | step_app _ _ ihf iha => exact .step_app (ihf W) (iha W)
  | step_lam _ _ ihA ihb => exact .step_lam (ihA W) (ihb W.succ)
  | step_forallE _ _ ihA ihB => exact .step_forallE (ihA W) (ihB W.succ)
  | step_beta _ _ ihb iha =>
    simpa only [liftN, liftN_inst_hi] using Cert.step_beta (ihb W.succ) (iha W)
  | step_extra h1 h2 h3 =>
    have ⟨hl, hr⟩ := henv.ordered.defEqWF h1
    simpa only [((hl.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le k),
      ((hr.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le k)] using
      (Cert.step_extra (Γ := Δ) h1 h2 h3)
  | step_eta _ _ ihe ihF =>
    simpa only [liftN_etaExpand] using Cert.step_eta (ihe W) (ihF W)
  | red_refl => exact .red_refl
  | red_step _ _ ih1 ih2 => exact .red_step (ih1 W) (ih2 W)
  | norm_bvar => exact .norm_bvar
  | norm_sort h1 h2 h3 => exact .norm_sort h1 h2 h3
  | norm_const h1 h2 h3 h4 h5 => exact .norm_const h1 h2 h3 h4 h5
  | norm_app _ _ ihf iha => exact .norm_app (ihf W) (iha W)
  | norm_lam _ _ ihA ihb => exact .norm_lam (ihA W) (ihb W.succ)
  | norm_forallE _ _ ihA ihB => exact .norm_forallE (ihA W) (ihB W.succ)
  | norm_etaL _ _ _ _ ihe ihF ihA ihb =>
    have hb := ihb W.succ
    rw [liftN_etaBody] at hb
    exact .norm_etaL (ihe W) (ihF W) (ihA W) hb
  | norm_etaR _ _ _ _ ihe ihF ihA ihb =>
    have hb := ihb W.succ
    rw [liftN_etaBody] at hb
    exact .norm_etaR (ihe W) (ihF W) (ihA W) hb
  | norm_etaBoth _ _ _ _ _ _ ihe ihF ihe' ihF' ihA ihb =>
    have hb := ihb W.succ
    simp only [liftN_etaBody] at hb
    exact .norm_etaBoth (ihe W) (ihF W) (ihe' W) (ihF' W) (ihA W) hb
  | norm_proofIrrel _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .norm_proofIrrel (ih1 W) (ih2 W) (ih3 W) (ih4 W) (ih5 W)
  | conv_mk _ _ _ ih1 ih2 ih3 => exact .conv_mk (ih1 W) (ih2 W) (ih3 W)

/-- Weakening of every pilot certificate, under Astra's name. -/
theorem pilot_weakN (henv : env.WF) (h : Cert env U j Γ a b) (W : Ctx.LiftN n k Γ Δ) :
    Cert env U j Δ (a.liftN n k) (b.liftN n k) := h.weakN henv W

/-! ## Fused proof leaves -/

/-- A proof leaf retains its two synthesised proposition types and their alignment. Every
typing and conversion premise is a pilot certificate, not declarative evidence. -/
structure ProofLeaf (env : VEnv) (U : Nat) (Γ : List VExpr) (h h' : VExpr) : Prop where
  cert : ∃ P Q S, CTy env U Γ h P ∧ CTy env U Γ h' Q ∧
    CConv env U Γ P Q ∧ CTy env U Γ P S ∧ CRed env U Γ S (.sort .zero)

/-- A proof leaf is the `norm_proofIrrel` constructor. -/
theorem ProofLeaf.toNorm (h : ProofLeaf env U Γ a b) : CNorm env U Γ a b := by
  obtain ⟨P, Q, S, ha, hb, hPQ, hP, hS⟩ := h.cert
  exact .norm_proofIrrel ha hb hPQ hP hS

/-- Soundness of a proof leaf; the endpoint typings come from the leaf itself. -/
theorem ProofLeaf.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h : ProofLeaf env U Γ a b) : env.IsDefEqU U Γ a b := by
  obtain ⟨P, Q, S, ha, hb, hPQ, hP, hS⟩ := h.cert
  exact (Cert.norm_proofIrrel ha hb hPQ hP hS).sound henv hΓ _ _
    (ha.hasType henv hΓ) (hb.hasType henv hΓ)

/-- Descent of a proof leaf, componentwise from `Cert.descend`. -/
theorem ProofLeaf.descend (henv : env.WF) (W : Ctx.LiftN n k Γ Δ)
    (h : ProofLeaf env U Δ (a.liftN n k) (b.liftN n k)) : ProofLeaf env U Γ a b := by
  obtain ⟨P, Q, S, ha, hb, hPQ, hP, hS⟩ := h.cert
  obtain ⟨P₀, rfl, ha₀⟩ := ha.descend henv W
  obtain ⟨Q₀, rfl, hb₀⟩ := hb.descend henv W
  obtain ⟨S₀, rfl, hP₀⟩ := hP.descend henv W
  obtain ⟨Z, hz, hS₀⟩ := Cert.descend henv hS W rfl
  obtain rfl := VExpr.liftN_eq_sort hz.symm
  exact ⟨P₀, Q₀, S₀, ha₀, hb₀, hPQ.descend henv W, hP₀, hS₀⟩

/-- Weakening of a proof leaf. -/
theorem ProofLeaf.weakN (henv : env.WF) (W : Ctx.LiftN n k Γ Δ) (h : ProofLeaf env U Γ a b) :
    ProofLeaf env U Δ (a.liftN n k) (b.liftN n k) := by
  obtain ⟨P, Q, S, ha, hb, hPQ, hP, hS⟩ := h.cert
  exact ⟨P.liftN n k, Q.liftN n k, S.liftN n k, ha.weakN henv W, hb.weakN henv W,
    hPQ.weakN henv W, hP.weakN henv W, hS.weakN henv W⟩

/-- Fused congruence for proof arguments. Its premises are function comparison, structural
typing, and proposition alignment; there is no recursive proof-comparison premise. This is a
conservative derived pilot rule. -/
theorem proofApp_rule (hf : CNorm env U Γ f g) (ha : CTy env U Γ a P) (hb : CTy env U Γ b Q)
    (hPQ : CConv env U Γ P Q) (hP : CTy env U Γ P S) (hS : CRed env U Γ S (.sort .zero)) :
    CNorm env U Γ (.app f a) (.app g b) :=
  .norm_app hf (.norm_proofIrrel ha hb hPQ hP hS)

/-- A conservative certificate form exposing the fused proof-argument rule. -/
structure ProofApp (env : VEnv) (U : Nat) (Γ : List VExpr) (f g a b : VExpr) : Prop where
  functions : CNorm env U Γ f g
  arguments : ProofLeaf env U Γ a b

/-- A fused proof application is a pilot `norm_app` over a proof leaf. -/
theorem ProofApp.toNorm (h : ProofApp env U Γ f g a b) :
    CNorm env U Γ (.app f a) (.app g b) :=
  .norm_app h.functions h.arguments.toNorm

/-- Soundness of the fused proof application, for typed endpoints. -/
theorem ProofApp.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h : ProofApp env U Γ f g a b)
    (hl : env.HasType U Γ (.app f a) A) (hr : env.HasType U Γ (.app g b) B) :
    env.IsDefEqU U Γ (.app f a) (.app g b) := h.toNorm.sound henv hΓ _ _ hl hr

/-- Descent of the fused proof application. -/
theorem ProofApp.descend (henv : env.WF) (W : Ctx.LiftN n k Γ Δ)
    (h : ProofApp env U Δ (f.liftN n k) (g.liftN n k) (a.liftN n k) (b.liftN n k)) :
    ProofApp env U Γ f g a b :=
  ⟨Cert.descend henv h.functions W rfl rfl, h.arguments.descend henv W⟩

/-- Weakening of the fused proof application. -/
theorem ProofApp.weakN (henv : env.WF) (W : Ctx.LiftN n k Γ Δ)
    (h : ProofApp env U Γ f g a b) :
    ProofApp env U Δ (f.liftN n k) (g.liftN n k) (a.liftN n k) (b.liftN n k) :=
  ⟨h.functions.weakN henv W, h.arguments.weakN henv W⟩

namespace ProofAware

/-! ## Two global phases cannot be ordered -/

/-- The semantic two phases proposed for the cut-elimination order. -/
inductive Phase | type | proof deriving DecidableEq

/-- A recursive premise phase and its enclosing conclusion phase: the alignment of a proof
leaf is a type comparison inside a proof comparison; a proof argument is a proof comparison
inside a type comparison. -/
inductive Dependency : Phase → Phase → Prop
  | alignment : Dependency .type .proof
  | argument : Dependency .proof .type

/-- **No phase order.** No well-founded relation on any type, through any assignment of the
two phases, makes every recursive premise phase smaller than its conclusion phase. -/
theorem no_phase_order {α : Type} (r : α → α → Prop) (wf : WellFounded r) (phase : Phase → α) :
    ¬ (∀ {a b}, Dependency a b → r (phase a) (phase b)) := by
  intro h
  have hab := h Dependency.alignment
  have hba := h Dependency.argument
  have bad : ∀ x, Acc r x → (x = phase .type ∨ x = phase .proof) → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      rintro (rfl | rfl)
      · exact ih _ hba (Or.inr rfl)
      · exact ih _ hab (Or.inl rfl)
  exact bad _ (wf.apply _) (Or.inl rfl)

/-- A rank: phase number, universe of the common comparison type, then any suffix (cut-type
syntax complexity, multiset, size, or other metadata). -/
abbrev Rank (α : Type) := Nat × (Nat × α)

/-- Lexicographic order on ranks over a suffix order `r`. -/
def RankLT (r : α → α → Prop) : Rank α → Rank α → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) r)

theorem rank_wellFounded (r : α → α → Prop) (wf : WellFounded r) : WellFounded (RankLT r) :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel ⟨r, wf⟩)).wf

/-- **No layer-universe rank.** Universe 1 is the type of a proposition comparison; universe 0
is the type of a proof comparison. The two inequalities demanded by a type comparison under a
proof comparison and a proof comparison under a type comparison cannot both hold, whatever
the suffix order and the suffix values. -/
theorem no_layer_universe_rank (r : α → α → Prop) (types proofs : Nat) (a b c d : α) :
    ¬ (RankLT r (types, 1, a) (proofs, 0, b) ∧ RankLT r (proofs, 0, c) (types, 1, d)) := by
  rintro ⟨h₁, h₂⟩
  have htp : types < proofs := by
    cases h₁ with
    | left _ _ h => exact h
    | right _ h => cases h with
      | left _ _ h => omega
  cases h₂ with
  | left _ _ h => omega
  | right _ h => omega

/-! ## The concrete alternation -/

namespace Alternation

/-- `P : Prop, F : P → Prop, h₀ h₁ : P, k₀ : F h₀, k₁ : F h₁`. List entries are stored in
their respective tail contexts. -/
def Γ₆ : List VExpr :=
  [.app (.bvar 3) (.bvar 1), .app (.bvar 2) (.bvar 1),
   .bvar 2, .bvar 1, .forallE (.bvar 0) (.sort .zero), .sort .zero]
def P : VExpr := .bvar 5
def F : VExpr := .bvar 4
def h₀ : VExpr := .bvar 3
def h₁ : VExpr := .bvar 2
def k₀ : VExpr := .bvar 1
def k₁ : VExpr := .bvar 0
def A₀ : VExpr := .app F h₀
def A₁ : VExpr := .app F h₁

theorem p_lookup : Lookup Γ₆ 5 (.sort .zero) := .succ (.succ (.succ (.succ (.succ .zero))))
theorem f_lookup : Lookup Γ₆ 4 (.forallE P (.sort .zero)) := .succ (.succ (.succ (.succ .zero)))
theorem h₀_lookup : Lookup Γ₆ 3 P := .succ (.succ (.succ .zero))
theorem h₁_lookup : Lookup Γ₆ 2 P := .succ (.succ .zero)
theorem k₀_lookup : Lookup Γ₆ 1 A₀ := .succ .zero
theorem k₁_lookup : Lookup Γ₆ 0 A₁ := .zero

theorem Γ₆_wf : OnCtx Γ₆ (env.IsType U) := by
  have hp : env.HasType U [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  have hf : env.IsType U [.sort .zero] (.forallE (.bvar 0) (.sort .zero)) :=
    ⟨_, .forallE hp (.sort trivial)⟩
  refine ⟨⟨⟨⟨⟨⟨trivial, _, .sort trivial⟩, hf⟩,
    _, .bvar (.succ .zero)⟩, _, .bvar (.succ (.succ .zero))⟩, ?_⟩, ?_⟩
  · exact ⟨_, .app (B := .sort .zero) (.bvar (.succ (.succ .zero))) (.bvar (.succ .zero))⟩
  · exact ⟨_, .app (B := .sort .zero) (.bvar (.succ (.succ (.succ .zero)))) (.bvar (.succ .zero))⟩

theorem p_synth : CTy env U Γ₆ P (.sort .zero) := .ty_bvar p_lookup
theorem h₀_synth : CTy env U Γ₆ h₀ P := .ty_bvar h₀_lookup
theorem h₁_synth : CTy env U Γ₆ h₁ P := .ty_bvar h₁_lookup
theorem p_compare : CConv env U Γ₆ P P := .conv_mk .red_refl .red_refl .norm_bvar

/-- A proof comparison by proof irrelevance (stage 1). -/
theorem h_compare : CNorm env U Γ₆ h₀ h₁ :=
  .norm_proofIrrel h₀_synth h₁_synth p_compare p_synth .red_refl

theorem a₀_synth : CTy env U Γ₆ A₀ (.sort .zero) :=
  .ty_app (.ty_bvar f_lookup) .red_refl h₀_synth p_compare

theorem a₁_synth : CTy env U Γ₆ A₁ (.sort .zero) :=
  .ty_app (.ty_bvar f_lookup) .red_refl h₁_synth p_compare

/-- A type-level comparison with a proof-level recursive argument (stage 2). -/
theorem a_compare : CConv env U Γ₆ A₀ A₁ :=
  .conv_mk .red_refl .red_refl (.norm_app .norm_bvar h_compare)

/-- The same type comparison is obtainable with the fused rule. -/
theorem a_compare_fused : ProofApp env U Γ₆ F F h₀ h₁ :=
  ⟨.norm_bvar, ⟨P, P, .sort .zero, h₀_synth, h₁_synth, p_compare, p_synth, .red_refl⟩⟩

/-- A proof comparison whose proposition alignment is the preceding type comparison
(stage 3): proof, type, proof, type inside one finite pilot certificate. -/
theorem k_compare : ProofLeaf env U Γ₆ k₀ k₁ :=
  ⟨A₀, A₁, .sort .zero, .ty_bvar k₀_lookup, .ty_bvar k₁_lookup, a_compare, a₀_synth, .red_refl⟩

theorem actual_type_equality (henv : env.WF) : env.IsDefEq U Γ₆ A₀ A₁ (.sort .zero) :=
  (a_compare.defeq henv Γ₆_wf (a₀_synth.hasType henv Γ₆_wf)
    (a₁_synth.hasType henv Γ₆_wf)).of_l henv Γ₆_wf (a₀_synth.hasType henv Γ₆_wf)

theorem actual_proof_equality (henv : env.WF) : env.IsDefEqU U Γ₆ k₀ k₁ :=
  k_compare.sound henv Γ₆_wf

/-- The failed rank calls occur in the displayed, well-typed certificate, not in an invented
dependency graph with no object-language inhabitants. -/
theorem constructor_rank_obstruction (henv : env.WF) (r : α → α → Prop) (types proofs : Nat)
    (a b c d : α) :
    OnCtx Γ₆ (env.IsType U) ∧
    env.IsDefEq U Γ₆ A₀ A₁ (.sort .zero) ∧
    CNorm env U Γ₆ h₀ h₁ ∧ ProofLeaf env U Γ₆ k₀ k₁ ∧
    ¬ (RankLT r (types, 1, a) (proofs, 0, b) ∧ RankLT r (proofs, 0, c) (types, 1, d)) :=
  ⟨Γ₆_wf, actual_type_equality henv, h_compare, k_compare,
    no_layer_universe_rank r types proofs a b c d⟩

/-- The smallest rank-level repair of this particular cycle is an occurrence-dependent stage:
`P ~ P` at 0, `h₀ ~ h₁` at 1, `F h₀ ~ F h₁` at 2, `k₀ ~ k₁` at 3. Arbitrary suffixes are
harmless for these three calls. This is not a substitution or cut-elimination bound on such
stages. -/
theorem local_stages_decrease (r : α → α → Prop) (a b c d : α) :
    RankLT r (0, 1, a) (1, 0, b) ∧ RankLT r (1, 0, b) (2, 1, c) ∧ RankLT r (2, 1, c) (3, 0, d) :=
  ⟨.left _ _ (by decide), .left _ _ (by decide), .left _ _ (by decide)⟩

end Alternation

/-! ## Proof erasure must keep proposition alignment -/

/-- Each proof token retains its proposition. This is the minimum information needed at a
heterogeneous proof-comparison boundary. -/
def ProofTokenEq (env : VEnv) (U : Nat) (Γ : List VExpr) (P Q : VExpr) : Prop :=
  env.IsDefEqU U Γ P Q

/-- Typed proof erasure reflects and preserves equality precisely when the proposition labels
are compared. The erased proof payload is irrelevant. -/
theorem typed_token_iff (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hP : env.HasType U Γ P (.sort .zero))
    (ha : env.HasType U Γ a P) (hb : env.HasType U Γ b Q) :
    env.IsDefEqU U Γ a b ↔ ProofTokenEq env U Γ P Q := by
  constructor
  · intro h
    exact (h.of_l henv hΓ ha).uniqU henv hΓ hb
  · intro h
    exact ⟨P, .proofIrrel hP ha (h.symm.defeqDF henv hΓ hb)⟩

/-- Top-level part required of any global single-token erasure, including one that also
recursively erases proof subterms. -/
def CollapsesProofs (env : VEnv) (U : Nat) (erase : List VExpr → VExpr → VExpr)
    (token : VExpr) : Prop :=
  ∀ Γ h P, env.HasType U Γ P (.sort .zero) → env.HasType U Γ h P → erase Γ h = token

/-- Equality of erased syntax reflects declarative equality of well-typed originals. -/
def ReflectsUntyped (env : VEnv) (U : Nat) (erase : List VExpr → VExpr → VExpr) : Prop :=
  ∀ Γ a b P Q, OnCtx Γ (env.IsType U) →
    env.HasType U Γ a P → env.HasType U Γ b Q →
    erase Γ a = erase Γ b → env.IsDefEqU U Γ a b

/-- The erased proof keeps the original proof's proposition. -/
def PreservesProofTypes (env : VEnv) (U : Nat) (erase : List VExpr → VExpr → VExpr) : Prop :=
  ∀ Γ h P, env.HasType U Γ P (.sort .zero) → env.HasType U Γ h P →
    env.HasType U Γ (erase Γ h) P

/-- Two incompatible proposition labels (`∀ p : Prop, p` and `∀ p : Prop, p → p`),
instantiated in a well-formed context. -/
theorem incompatible_proofs (henv : env.WF) :
    ∃ Γ a b P Q, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ P (.sort .zero) ∧ env.HasType U Γ Q (.sort .zero) ∧
      env.HasType U Γ a P ∧ env.HasType U Γ b Q ∧ ¬ env.IsDefEqU U Γ P Q := by
  open StrengtheningKripke in
  let Γ := [propIdArrow, propId]
  have hΓ : OnCtx Γ (env.IsType U) :=
    ⟨⟨trivial, _, StrengtheningKripke.propId_typed []⟩, _,
      StrengtheningKripke.propIdArrow_typed henv.ordered _⟩
  have ha : env.HasType U Γ (.bvar 1) StrengtheningKripke.propId := by
    simpa [Γ, StrengtheningKripke.propId, StrengtheningKripke.propIdArrow, lift, liftN,
      liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.succ (A := StrengtheningKripke.propIdArrow)
        (Lookup.zero (Γ := []) (ty := StrengtheningKripke.propId))))
  have hb : env.HasType U Γ (.bvar 0) StrengtheningKripke.propIdArrow := by
    simpa [Γ, StrengtheningKripke.propId, StrengtheningKripke.propIdArrow, lift, liftN,
      liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.zero (Γ := [StrengtheningKripke.propId])
        (ty := StrengtheningKripke.propIdArrow)))
  refine ⟨Γ, .bvar 1, .bvar 0, StrengtheningKripke.propId, StrengtheningKripke.propIdArrow, hΓ,
    StrengtheningKripke.propId_typed Γ, StrengtheningKripke.propIdArrow_typed henv.ordered Γ,
    ha, hb, ?_⟩
  intro h
  obtain ⟨u, hd⟩ := (h.forallE_inv henv hΓ).1
  exact IsDefEqU.sort_forallE_inv henv hΓ ⟨_, hd⟩

/-- **Untyped erasure does not reflect.** Any context-sensitive erasure that sends every
proof to one token identifies two proofs of non-convertible propositions. -/
theorem untyped_erasure_reflection_false (henv : env.WF)
    (erase : List VExpr → VExpr → VExpr) (token : VExpr)
    (hc : CollapsesProofs env U erase token) : ¬ ReflectsUntyped env U erase := by
  intro hr
  obtain ⟨Γ, a, b, P, Q, hΓ, hP, hQ, ha, hb, hn⟩ := incompatible_proofs (U := U) henv
  have he := hr Γ a b P Q hΓ ha hb ((hc Γ a P hP ha).trans (hc Γ b Q hQ hb).symm)
  exact hn ((he.of_l henv hΓ ha).uniqU henv hΓ hb)

/-- **A single token has no type.** An ordinary `VExpr` token cannot have every erased
proof's proposition as its type in the unchanged context. -/
theorem single_token_typing_false (henv : env.WF)
    (erase : List VExpr → VExpr → VExpr) (token : VExpr)
    (hc : CollapsesProofs env U erase token) : ¬ PreservesProofTypes env U erase := by
  intro ht
  obtain ⟨Γ, a, b, P, Q, hΓ, hP, hQ, ha, hb, hn⟩ := incompatible_proofs (U := U) henv
  have h₁ := ht Γ a P hP ha
  have h₂ := ht Γ b Q hQ hb
  rw [hc Γ a P hP ha] at h₁
  rw [hc Γ b Q hQ hb] at h₂
  exact hn (h₁.uniqU henv hΓ h₂)

end ProofAware
end VEnv
end Lean4Lean
