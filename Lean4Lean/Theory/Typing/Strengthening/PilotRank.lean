import Lean4Lean.Theory.Typing.Strengthening.PilotTrans

/-! # Size-indexed pilot certificates and the duplication obstruction

`Cert` is `Prop`-valued, so no rank can be defined as a function of a certificate (Astra round
8, `proof_rank_constant`). `CertN` is the same calculus with the derivation size as an index
(`CertN.erase`, `Cert.toN`), which is what a size rank on certificates means.

The obstruction to the transitivity recursion of the direction-A attempt
is then exhibited on the obligation `NormTransport` (transport of normal equality along a
certified reduction, `PilotTrans.lean`): at a beta step under `norm_app`, the proof must
substitute the (transported) argument comparison into the body comparison, once per occurrence
of the bound variable, so the output is not bounded by the inputs, and the heterogeneous
substitution it calls (which re-enters typing substitution and hence transport) receives
larger inputs than the transport call itself.

* `IrredIn`: terms without certified reducts; sorts, variables of sort type, and `Π`s of
  irreducible parts (`IrredIn.sort`, `IrredIn.bvar_sort`, `IrredIn.forallE`).
* `Duplication`: the closed example. `A`, `A'` are `Π`-towers of sorts differing only by
  equivalent level expressions (`l₁ = 1`, `l₂ = max 1 0`), `w = Π A. P₀`, `w' = Π A'. P₀`
  with `P₀ = ∀ p : Prop, p`, `n = Π x₀:X. Π x₁:X. Π x₂:X. Π x₃:X. X` (five occurrences of the
  bound `X : Prop`), `u = (λ X:Prop. n) w`, `u' = (λ X:Prop. n) w'`, and
  `a = (λ X:Prop. X) u`, `b = (λ X:Prop. X) u'`.
* `norm_tower_ge`: every normal-equality certificate against `Π w'. ... Π w'. w'` (`j`
  binders) has size at least `18 + 20 j`, whatever its left side: the right side forces a
  `norm_forallE` with a domain conversion against `w'` (at least 21) or a `norm_proofIrrel`
  whose typing of the `Π` is at least as large, at every level.
* `transport_output_exceeds_inputs`: the typed instance `N u u'` (size 53) along the beta
  step of size 21 has every transported certificate of size at least 98.
* `substitution_call_not_decreasing`: in the instance `N a b` (size 60) along the beta step
  of size 23, the heterogeneous substitution call receives inputs of total size at least 99,
  more than the 83 of the transport call; `no_monotone_size_rank` draws the consequence for
  every rank that is a monotone function of the total input size. -/


namespace Lean4Lean
namespace VEnv
open VExpr

variable (env : VEnv) (U : Nat)

/-- Size-indexed pilot certificates: the constructors of `Cert` with the derivation size
(leaves 1, every node 1 plus its premises) as an index. -/
inductive CertN : CKind → Nat → List VExpr → VExpr → VExpr → Prop
  | ty_bvar : Lookup Γ i A → CertN .ty 1 Γ (.bvar i) A
  | ty_sort : l.WF U → CertN .ty 1 Γ (.sort l) (.sort (.succ l))
  | ty_const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
      CertN .ty 1 Γ (.const c ls) (ci.type.instL ls)
  | ty_app : CertN .ty n₁ Γ f F → CertN .red n₂ Γ F (.forallE A B) → CertN .ty n₃ Γ a A' →
      CertN .conv n₄ Γ A' A → CertN .ty (n₁ + n₂ + n₃ + n₄ + 1) Γ (.app f a) (B.inst a)
  | ty_lam : CertN .ty n₁ Γ A S → CertN .red n₂ Γ S (.sort u) → CertN .ty n₃ (A::Γ) b B →
      CertN .ty (n₁ + n₂ + n₃ + 1) Γ (.lam A b) (.forallE A B)
  | ty_forallE : CertN .ty n₁ Γ A S → CertN .red n₂ Γ S (.sort u) → CertN .ty n₃ (A::Γ) B S' →
      CertN .red n₄ (A::Γ) S' (.sort v) →
      CertN .ty (n₁ + n₂ + n₃ + n₄ + 1) Γ (.forallE A B) (.sort (.imax u v))
  | step_bvar : CertN .step 1 Γ (.bvar i) (.bvar i)
  | step_sort : CertN .step 1 Γ (.sort l) (.sort l)
  | step_const : CertN .step 1 Γ (.const c ls) (.const c ls)
  | step_app : CertN .step n₁ Γ f f' → CertN .step n₂ Γ a a' →
      CertN .step (n₁ + n₂ + 1) Γ (.app f a) (.app f' a')
  | step_lam : CertN .step n₁ Γ A A' → CertN .step n₂ (A::Γ) b b' →
      CertN .step (n₁ + n₂ + 1) Γ (.lam A b) (.lam A' b')
  | step_forallE : CertN .step n₁ Γ A A' → CertN .step n₂ (A::Γ) B B' →
      CertN .step (n₁ + n₂ + 1) Γ (.forallE A B) (.forallE A' B')
  | step_beta : CertN .step n₁ (A::Γ) b b' → CertN .step n₂ Γ a a' →
      CertN .step (n₁ + n₂ + 1) Γ (.app (.lam A b) a) (b'.inst a')
  | step_extra : env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
      CertN .step 1 Γ (df.lhs.instL ls) (df.rhs.instL ls)
  | step_eta : CertN .ty n₁ Γ e F → CertN .red n₂ Γ F (.forallE A B) →
      CertN .step (n₁ + n₂ + 1) Γ e (.lam A (.app e.lift (.bvar 0)))
  | red_refl : CertN .red 1 Γ e e
  | red_step : CertN .step n₁ Γ a b → CertN .red n₂ Γ b c → CertN .red (n₁ + n₂ + 1) Γ a c
  | norm_bvar : CertN .norm 1 Γ (.bvar i) (.bvar i)
  | norm_sort : l₁.WF U → l₂.WF U → l₁ ≈ l₂ → CertN .norm 1 Γ (.sort l₁) (.sort l₂)
  | norm_const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
      ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
      CertN .norm 1 Γ (.const c ls) (.const c ls')
  | norm_app : CertN .norm n₁ Γ f f' → CertN .norm n₂ Γ a a' →
      CertN .norm (n₁ + n₂ + 1) Γ (.app f a) (.app f' a')
  | norm_lam : CertN .conv n₁ Γ A A' → CertN .norm n₂ (A::Γ) b b' →
      CertN .norm (n₁ + n₂ + 1) Γ (.lam A b) (.lam A' b')
  | norm_forallE : CertN .conv n₁ Γ A A' → CertN .norm n₂ (A::Γ) B B' →
      CertN .norm (n₁ + n₂ + 1) Γ (.forallE A B) (.forallE A' B')
  | norm_etaL : CertN .ty n₁ Γ e' F → CertN .red n₂ Γ F (.forallE A' B) →
      CertN .conv n₃ Γ A A' → CertN .norm n₄ (A::Γ) e (.app e'.lift (.bvar 0)) →
      CertN .norm (n₁ + n₂ + n₃ + n₄ + 1) Γ (.lam A e) e'
  | norm_etaR : CertN .ty n₁ Γ e F → CertN .red n₂ Γ F (.forallE A' B) →
      CertN .conv n₃ Γ A A' → CertN .norm n₄ (A::Γ) (.app e.lift (.bvar 0)) e' →
      CertN .norm (n₁ + n₂ + n₃ + n₄ + 1) Γ e (.lam A e')
  | norm_etaBoth : CertN .ty n₁ Γ e F → CertN .red n₂ Γ F (.forallE A B) →
      CertN .ty n₃ Γ e' F' → CertN .red n₄ Γ F' (.forallE A' B') → CertN .conv n₅ Γ A A' →
      CertN .norm n₆ (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) →
      CertN .norm (n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + 1) Γ e e'
  | norm_proofIrrel : CertN .ty n₁ Γ h p → CertN .ty n₂ Γ h' p' → CertN .conv n₃ Γ p p' →
      CertN .ty n₄ Γ p S → CertN .red n₅ Γ S (.sort .zero) →
      CertN .norm (n₁ + n₂ + n₃ + n₄ + n₅ + 1) Γ h h'
  | conv_mk : CertN .red n₁ Γ a a' → CertN .red n₂ Γ b b' → CertN .norm n₃ Γ a' b' →
      CertN .conv (n₁ + n₂ + n₃ + 1) Γ a b

variable {env U}

/-- Forgetting the size. -/
theorem CertN.erase (h : CertN env U k n Γ a b) : Cert env U k Γ a b := by
  induction h with
  | ty_bvar h => exact .ty_bvar h
  | ty_sort h => exact .ty_sort h
  | ty_const h1 h2 h3 => exact .ty_const h1 h2 h3
  | ty_app _ _ _ _ ih1 ih2 ih3 ih4 => exact .ty_app ih1 ih2 ih3 ih4
  | ty_lam _ _ _ ih1 ih2 ih3 => exact .ty_lam ih1 ih2 ih3
  | ty_forallE _ _ _ _ ih1 ih2 ih3 ih4 => exact .ty_forallE ih1 ih2 ih3 ih4
  | step_bvar => exact .step_bvar
  | step_sort => exact .step_sort
  | step_const => exact .step_const
  | step_app _ _ ih1 ih2 => exact .step_app ih1 ih2
  | step_lam _ _ ih1 ih2 => exact .step_lam ih1 ih2
  | step_forallE _ _ ih1 ih2 => exact .step_forallE ih1 ih2
  | step_beta _ _ ih1 ih2 => exact .step_beta ih1 ih2
  | step_extra h1 h2 h3 => exact .step_extra h1 h2 h3
  | step_eta _ _ ih1 ih2 => exact .step_eta ih1 ih2
  | red_refl => exact .red_refl
  | red_step _ _ ih1 ih2 => exact .red_step ih1 ih2
  | norm_bvar => exact .norm_bvar
  | norm_sort h1 h2 h3 => exact .norm_sort h1 h2 h3
  | norm_const h1 h2 h3 h4 h5 => exact .norm_const h1 h2 h3 h4 h5
  | norm_app _ _ ih1 ih2 => exact .norm_app ih1 ih2
  | norm_lam _ _ ih1 ih2 => exact .norm_lam ih1 ih2
  | norm_forallE _ _ ih1 ih2 => exact .norm_forallE ih1 ih2
  | norm_etaL _ _ _ _ ih1 ih2 ih3 ih4 => exact .norm_etaL ih1 ih2 ih3 ih4
  | norm_etaR _ _ _ _ ih1 ih2 ih3 ih4 => exact .norm_etaR ih1 ih2 ih3 ih4
  | norm_etaBoth _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .norm_etaBoth ih1 ih2 ih3 ih4 ih5 ih6
  | norm_proofIrrel _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .norm_proofIrrel ih1 ih2 ih3 ih4 ih5
  | conv_mk _ _ _ ih1 ih2 ih3 => exact .conv_mk ih1 ih2 ih3

/-- Every certificate has a size. -/
theorem Cert.toN (h : Cert env U k Γ a b) : ∃ n, CertN env U k n Γ a b := by
  induction h with
  | ty_bvar h => exact ⟨_, .ty_bvar h⟩
  | ty_sort h => exact ⟨_, .ty_sort h⟩
  | ty_const h1 h2 h3 => exact ⟨_, .ty_const h1 h2 h3⟩
  | ty_app _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3; obtain ⟨_, ih4⟩ := ih4
    exact ⟨_, .ty_app ih1 ih2 ih3 ih4⟩
  | ty_lam _ _ _ ih1 ih2 ih3 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3
    exact ⟨_, .ty_lam ih1 ih2 ih3⟩
  | ty_forallE _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3; obtain ⟨_, ih4⟩ := ih4
    exact ⟨_, .ty_forallE ih1 ih2 ih3 ih4⟩
  | step_bvar => exact ⟨_, .step_bvar⟩
  | step_sort => exact ⟨_, .step_sort⟩
  | step_const => exact ⟨_, .step_const⟩
  | step_app _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .step_app ih1 ih2⟩
  | step_lam _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .step_lam ih1 ih2⟩
  | step_forallE _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .step_forallE ih1 ih2⟩
  | step_beta _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .step_beta ih1 ih2⟩
  | step_extra h1 h2 h3 => exact ⟨_, .step_extra h1 h2 h3⟩
  | step_eta _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .step_eta ih1 ih2⟩
  | red_refl => exact ⟨_, .red_refl⟩
  | red_step _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .red_step ih1 ih2⟩
  | norm_bvar => exact ⟨_, .norm_bvar⟩
  | norm_sort h1 h2 h3 => exact ⟨_, .norm_sort h1 h2 h3⟩
  | norm_const h1 h2 h3 h4 h5 => exact ⟨_, .norm_const h1 h2 h3 h4 h5⟩
  | norm_app _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .norm_app ih1 ih2⟩
  | norm_lam _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .norm_lam ih1 ih2⟩
  | norm_forallE _ _ ih1 ih2 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2
    exact ⟨_, .norm_forallE ih1 ih2⟩
  | norm_etaL _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3; obtain ⟨_, ih4⟩ := ih4
    exact ⟨_, .norm_etaL ih1 ih2 ih3 ih4⟩
  | norm_etaR _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3; obtain ⟨_, ih4⟩ := ih4
    exact ⟨_, .norm_etaR ih1 ih2 ih3 ih4⟩
  | norm_etaBoth _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3; obtain ⟨_, ih4⟩ := ih4
    obtain ⟨_, ih5⟩ := ih5; obtain ⟨_, ih6⟩ := ih6
    exact ⟨_, .norm_etaBoth ih1 ih2 ih3 ih4 ih5 ih6⟩
  | norm_proofIrrel _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3; obtain ⟨_, ih4⟩ := ih4
    obtain ⟨_, ih5⟩ := ih5
    exact ⟨_, .norm_proofIrrel ih1 ih2 ih3 ih4 ih5⟩
  | conv_mk _ _ _ ih1 ih2 ih3 =>
    obtain ⟨_, ih1⟩ := ih1; obtain ⟨_, ih2⟩ := ih2; obtain ⟨_, ih3⟩ := ih3
    exact ⟨_, .conv_mk ih1 ih2 ih3⟩

/-- Sizes are positive. -/
theorem CertN.pos (h : CertN env U k n Γ a b) : 1 ≤ n := by
  cases h <;> omega

/-! ## Irreducible terms -/

/-- `e` has no certified reduct but itself, in context `Γ`. -/
def IrredIn (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ Z, CRed env U Γ e Z → Z = e

theorem IrredIn.step (h : IrredIn env U Γ e) (H : CStep env U Γ e Z) : Z = e :=
  h Z (.red_step H .red_refl)

theorem IrredIn.sort (hex : ConstHeadedEquations env) : IrredIn env U Γ (.sort l) :=
  fun _ h => CRed.sort_inv hex h

theorem _root_.Lean4Lean.VExpr.mkApps_ne_bvar {fn : VExpr} (hfn : ∀ i, fn ≠ .bvar i)
    (args : List VExpr) : mkApps fn args ≠ .bvar i := by
  induction args generalizing fn with
  | nil => exact hfn _
  | cons a as ih => exact ih fun _ h => by cases h

theorem ConstHeadedEquations.lhs_ne_bvar (hex : ConstHeadedEquations env) (h : env.defeqs df) :
    df.lhs.instL ls ≠ .bvar i := by
  obtain ⟨c, ls', args, hl⟩ := hex df h
  rw [hl, instL_mkApps]
  exact mkApps_ne_bvar (fun _ h => by cases h) _

/-- The irreducibility statement for a fixed term `e` in a fixed context `Γ`. -/
def Cert.IrredShape (Γ₀ : List VExpr) (e : VExpr) : CKind → List VExpr → VExpr → VExpr → Prop
  | .step, Γ, a, b | .red, Γ, a, b => Γ = Γ₀ → a = e → b = e
  | _, _, _, _ => True

/-- A variable whose type is a sort has no reducts (it cannot eta-expand). -/
theorem IrredIn.bvar_sort (hex : ConstHeadedEquations env) (hl : Lookup Γ i (.sort l)) :
    IrredIn env U Γ (.bvar i) := by
  suffices ∀ {k Γ' a b}, Cert env U k Γ' a b → Cert.IrredShape Γ (.bvar i) k Γ' a b from
    fun Z h => this h rfl rfl
  intro k Γ' a b H
  induction H with
  | step_bvar => exact fun _ h => h
  | step_eta h1 h2 =>
    intro hΓ he
    subst hΓ he
    cases h1 with | ty_bvar h1 =>
    cases h1.uniq hl
    cases CRed.sort_inv hex h2
  | step_extra h => exact fun _ h' => absurd h' (hex.lhs_ne_bvar h)
  | red_refl => exact fun _ h => h
  | red_step _ _ ih1 ih2 => exact fun hΓ ha => ih2 hΓ (ih1 hΓ ha)
  | step_sort | step_const | step_app | step_lam | step_forallE | step_beta =>
    intro _ h; cases h
  | _ => trivial

/-- A `Π` with irreducible domain and body is irreducible. -/
theorem IrredIn.forallE (hex : ConstHeadedEquations env) (hX : IrredIn env U Γ X)
    (hY : IrredIn env U (X :: Γ) Y) : IrredIn env U Γ (.forallE X Y) := by
  suffices ∀ {k Γ' a b}, Cert env U k Γ' a b → Cert.IrredShape Γ (.forallE X Y) k Γ' a b from
    fun Z h => this h rfl rfl
  intro k Γ' a b H
  induction H with
  | step_forallE h1 h2 =>
    intro hΓ he
    subst hΓ
    cases he
    rw [hX.step h1, hY.step h2]
  | step_eta h1 h2 =>
    intro hΓ he
    subst hΓ he
    cases h1
    cases CRed.sort_inv hex h2
  | step_extra h => exact fun _ h' => absurd h' (hex.lhs_ne_forallE h)
  | red_refl => exact fun _ h => h
  | red_step _ _ ih1 ih2 => exact fun hΓ ha => ih2 hΓ (ih1 hΓ ha)
  | step_bvar | step_sort | step_const | step_app | step_lam | step_beta =>
    intro _ h; cases h
  | _ => trivial


/-! ## The duplication example -/

namespace Duplication

def l₁ : VLevel := .succ .zero
def l₂ : VLevel := .max (.succ .zero) .zero
theorem l₁_wf : l₁.WF U := trivial
theorem l₂_wf : l₂.WF U := ⟨trivial, trivial⟩
theorem l₁_equiv_l₂ : l₁ ≈ l₂ := by funext ls; rfl

/-- `Π (sort l₂)^j. sort l₁`. -/
def sortTower : Nat → VExpr
  | 0 => .sort l₁
  | j+1 => .forallE (.sort l₂) (sortTower j)
/-- `Π (sort l₁)^j. sort l₁`. -/
def sortTowerL : Nat → VExpr
  | 0 => .sort l₁
  | j+1 => .forallE (.sort l₁) (sortTowerL j)
def A : VExpr := sortTowerL 3
def A' : VExpr := sortTower 3
def P₀ : VExpr := .forallE (.sort .zero) (.bvar 0)
def w : VExpr := .forallE A P₀
def w' : VExpr := .forallE A' P₀
/-- `Π w'^j. w'`. -/
def tower : Nat → VExpr
  | 0 => w'
  | j+1 => .forallE w' (tower j)
def n : VExpr :=
  .forallE (.bvar 0) (.forallE (.bvar 1) (.forallE (.bvar 2) (.forallE (.bvar 3) (.bvar 4))))
def u : VExpr := .app (.lam (.sort .zero) n) w
def u' : VExpr := .app (.lam (.sort .zero) n) w'
def a : VExpr := .app (.lam (.sort .zero) (.bvar 0)) u
def b : VExpr := .app (.lam (.sort .zero) (.bvar 0)) u'

theorem n_inst_w' : n.inst w' = tower 4 := rfl
theorem bvar_inst : (VExpr.bvar 0).inst (n.inst w') = tower 4 := rfl

/-! ### Irreducibility of the closed towers -/

theorem irred_sortTower (hex : ConstHeadedEquations env) :
    ∀ j Γ, IrredIn env U Γ (sortTower j)
  | 0, _ => IrredIn.sort hex
  | j+1, _ => IrredIn.forallE hex (IrredIn.sort hex) (irred_sortTower hex j _)

theorem irred_P₀ (hex : ConstHeadedEquations env) : IrredIn env U Γ P₀ :=
  IrredIn.forallE hex (IrredIn.sort hex) (IrredIn.bvar_sort hex .zero)

theorem irred_w' (hex : ConstHeadedEquations env) : IrredIn env U Γ w' :=
  IrredIn.forallE hex (irred_sortTower hex 3 _) (irred_P₀ hex)

/-! ### Lower bounds for every certificate against the right-hand sides -/

theorem conv_ge (h : CertN env U .conv m Γ x y) : 4 ≤ m := by
  cases h with
  | conv_mk h1 h2 h3 => have := h1.pos; have := h2.pos; have := h3.pos; omega

theorem ty_sortTower_ge : ∀ j, CertN env U .ty m Γ (sortTower j) S → 4 * j + 1 ≤ m
  | 0, h => h.pos
  | j+1, h => by
    change CertN env U .ty m Γ (.forallE (.sort l₂) (sortTower j)) S at h
    cases h with
    | ty_forallE h1 h2 h3 h4 =>
      have := h1.pos; have := h2.pos; have := ty_sortTower_ge j h3; have := h4.pos; omega

theorem norm_sortTower_ge (hex : ConstHeadedEquations env) :
    ∀ j x, CertN env U .norm m Γ x (sortTower j) → 4 * j + 1 ≤ m
  | 0, x, h => h.pos
  | j+1, x, h => by
    change CertN env U .norm m Γ x (.forallE (.sort l₂) (sortTower j)) at h
    cases h with
    | norm_forallE h1 h2 => have := conv_ge h1; have := norm_sortTower_ge hex j _ h2; omega
    | norm_proofIrrel h1 h2 h3 h4 h5 =>
      have := h1.pos; have := ty_sortTower_ge (j+1) h2; have := conv_ge h3
      have := h4.pos; have := h5.pos; omega
    | norm_etaL h1 h2 => cases h1; cases CRed.sort_inv hex h2.erase
    | norm_etaBoth _ _ h3 h4 => cases h3; cases CRed.sort_inv hex h4.erase

theorem ty_A'_ge (h : CertN env U .ty m Γ A' S) : 13 ≤ m := ty_sortTower_ge 3 h

theorem conv_A'_ge (hex : ConstHeadedEquations env) (h : CertN env U .conv m Γ x A') : 16 ≤ m := by
  cases h with
  | conv_mk h1 h2 h3 =>
    cases irred_sortTower hex 3 Γ _ h2.erase
    have := h1.pos; have := h2.pos; have := norm_sortTower_ge hex 3 _ h3; omega

theorem ty_w'_ge (h : CertN env U .ty m Γ w' S) : 17 ≤ m := by
  change CertN env U .ty m Γ (.forallE A' P₀) S at h
  cases h with
  | ty_forallE h1 h2 h3 h4 => have := ty_A'_ge h1; have := h2.pos; have := h3.pos; have := h4.pos; omega

theorem norm_w'_ge (hex : ConstHeadedEquations env) (h : CertN env U .norm m Γ x w') : 18 ≤ m := by
  change CertN env U .norm m Γ x (.forallE A' P₀) at h
  cases h with
  | norm_forallE h1 h2 => have := conv_A'_ge hex h1; have := h2.pos; omega
  | norm_proofIrrel h1 h2 h3 h4 h5 =>
    have := h1.pos; have := ty_w'_ge h2; have := conv_ge h3; have := h4.pos; have := h5.pos; omega
  | norm_etaL h1 h2 => cases h1; cases CRed.sort_inv hex h2.erase
  | norm_etaBoth _ _ h3 h4 => cases h3; cases CRed.sort_inv hex h4.erase

theorem conv_w'_ge (hex : ConstHeadedEquations env) (h : CertN env U .conv m Γ x w') : 21 ≤ m := by
  cases h with
  | conv_mk h1 h2 h3 =>
    cases irred_w' hex _ h2.erase
    have := h1.pos; have := h2.pos; have := norm_w'_ge hex h3; omega

theorem ty_tower_ge : ∀ j, CertN env U .ty m Γ (tower j) S → 17 + 20 * j ≤ m
  | 0, h => ty_w'_ge h
  | j+1, h => by
    change CertN env U .ty m Γ (.forallE w' (tower j)) S at h
    cases h with
    | ty_forallE h1 h2 h3 h4 =>
      have := ty_w'_ge h1; have := h2.pos; have := ty_tower_ge j h3; have := h4.pos; omega

/-- **Lower bound.** Every normal-equality certificate whose right side is the tower
`Π w'. Π w'. ... w'` with `j` binders has size at least `18 + 20 j`, whatever its left side. -/
theorem norm_tower_ge (hex : ConstHeadedEquations env) :
    ∀ j x, CertN env U .norm m Γ x (tower j) → 18 + 20 * j ≤ m
  | 0, x, h => norm_w'_ge hex h
  | j+1, x, h => by
    change CertN env U .norm m Γ x (.forallE w' (tower j)) at h
    cases h with
    | norm_forallE h1 h2 => have := conv_w'_ge hex h1; have := norm_tower_ge hex j _ h2; omega
    | norm_proofIrrel h1 h2 h3 h4 h5 =>
      have := h1.pos; have := ty_tower_ge (j+1) h2; have := conv_ge h3
      have := h4.pos; have := h5.pos; omega
    | norm_etaL h1 h2 => cases h1; cases CRed.sort_inv hex h2.erase
    | norm_etaBoth _ _ h3 h4 => cases h3; cases CRed.sort_inv hex h4.erase

/-! ### The input certificates, with their exact sizes -/

theorem convSort (l : VLevel) (hl : l.WF U) : CertN env U .conv 4 Γ (.sort l) (.sort l) :=
  .conv_mk .red_refl .red_refl (.norm_sort hl hl rfl)

theorem convBvar : CertN env U .conv 4 Γ (.bvar i) (.bvar i) := .conv_mk .red_refl .red_refl .norm_bvar

theorem normAA' : CertN env U .norm 16 Γ A A' :=
  .norm_forallE (.conv_mk .red_refl .red_refl (.norm_sort l₁_wf l₂_wf l₁_equiv_l₂))
    (.norm_forallE (.conv_mk .red_refl .red_refl (.norm_sort l₁_wf l₂_wf l₁_equiv_l₂))
      (.norm_forallE (.conv_mk .red_refl .red_refl (.norm_sort l₁_wf l₂_wf l₁_equiv_l₂))
        (.norm_sort l₁_wf l₁_wf rfl)))

theorem normP₀ : CertN env U .norm 6 Γ P₀ P₀ := .norm_forallE (convSort .zero trivial) .norm_bvar

theorem normWW' : CertN env U .norm 26 Γ w w' :=
  .norm_forallE (.conv_mk .red_refl .red_refl normAA') normP₀

theorem normN : CertN env U .norm 21 Γ n n :=
  .norm_forallE convBvar (.norm_forallE convBvar (.norm_forallE convBvar
    (.norm_forallE convBvar .norm_bvar)))

theorem normUU' : CertN env U .norm 53 Γ u u' :=
  .norm_app (.norm_lam (convSort .zero trivial) normN) normWW'

theorem normAB : CertN env U .norm 60 Γ a b :=
  .norm_app (.norm_lam (convSort .zero trivial) .norm_bvar) normUU'

theorem stepN : CertN env U .step 9 Γ n n :=
  .step_forallE .step_bvar (.step_forallE .step_bvar (.step_forallE .step_bvar
    (.step_forallE .step_bvar .step_bvar)))

theorem stepA' : CertN env U .step 7 Γ A' A' :=
  .step_forallE .step_sort (.step_forallE .step_sort (.step_forallE .step_sort .step_sort))

theorem stepP₀ : CertN env U .step 3 Γ P₀ P₀ := .step_forallE .step_sort .step_bvar

theorem stepW' : CertN env U .step 11 Γ w' w' := .step_forallE stepA' stepP₀

theorem stepU' : CertN env U .step 21 Γ u' (tower 4) := .step_beta stepN stepW'

theorem stepB : CertN env U .step 23 Γ b (tower 4) := .step_beta .step_bvar stepU'

/-! ### Typing of the endpoints -/

theorem tyA : CTy env U Γ A (.sort (.imax (.succ l₁) (.imax (.succ l₁) (.imax (.succ l₁) (.succ l₁))))) :=
  .ty_forallE (.ty_sort l₁_wf) .red_refl (.ty_forallE (.ty_sort l₁_wf) .red_refl
    (.ty_forallE (.ty_sort l₁_wf) .red_refl (.ty_sort l₁_wf) .red_refl) .red_refl) .red_refl

theorem tyA' : CTy env U Γ A' (.sort (.imax (.succ l₂) (.imax (.succ l₂) (.imax (.succ l₂) (.succ l₁))))) :=
  .ty_forallE (.ty_sort l₂_wf) .red_refl (.ty_forallE (.ty_sort l₂_wf) .red_refl
    (.ty_forallE (.ty_sort l₂_wf) .red_refl (.ty_sort l₁_wf) .red_refl) .red_refl) .red_refl

theorem tyP₀ : CTy env U Γ P₀ (.sort (.imax (.succ .zero) .zero)) :=
  .ty_forallE (.ty_sort trivial) .red_refl (.ty_bvar .zero) .red_refl

theorem tyW : CTy env U Γ w (.sort (.imax (.imax (.succ l₁) (.imax (.succ l₁) (.imax (.succ l₁) (.succ l₁)))) (.imax (.succ .zero) .zero))) :=
  .ty_forallE tyA .red_refl tyP₀ .red_refl

theorem tyW' : CTy env U Γ w' (.sort (.imax (.imax (.succ l₂) (.imax (.succ l₂) (.imax (.succ l₂) (.succ l₁)))) (.imax (.succ .zero) .zero))) :=
  .ty_forallE tyA' .red_refl tyP₀ .red_refl

theorem tyN : CTy env U (.sort .zero :: Γ) n
    (.sort (.imax .zero (.imax .zero (.imax .zero (.imax .zero .zero))))) :=
  .ty_forallE (.ty_bvar .zero) .red_refl (.ty_forallE (.ty_bvar (.succ .zero)) .red_refl
    (.ty_forallE (.ty_bvar (.succ (.succ .zero))) .red_refl
      (.ty_forallE (.ty_bvar (.succ (.succ (.succ .zero)))) .red_refl
        (.ty_bvar (.succ (.succ (.succ (.succ .zero))))) .red_refl) .red_refl) .red_refl) .red_refl

theorem tyLamN : CTy env U Γ (.lam (.sort .zero) n)
    (.forallE (.sort .zero) (.sort (.imax .zero (.imax .zero (.imax .zero (.imax .zero .zero)))))) :=
  .ty_lam (.ty_sort trivial) .red_refl tyN

theorem tyU : CTy env U Γ u (.sort (.imax .zero (.imax .zero (.imax .zero (.imax .zero .zero))))) :=
  .ty_app tyLamN .red_refl tyW
    (.conv_mk .red_refl .red_refl (.norm_sort (by simp [VLevel.WF, l₁]) trivial (by funext ls; rfl)))

theorem tyU' : CTy env U Γ u' (.sort (.imax .zero (.imax .zero (.imax .zero (.imax .zero .zero))))) :=
  .ty_app tyLamN .red_refl tyW'
    (.conv_mk .red_refl .red_refl (.norm_sort (by simp [VLevel.WF, l₁, l₂]) trivial (by funext ls; rfl)))

theorem tyLamId : CTy env U Γ (.lam (.sort .zero) (.bvar 0)) (.forallE (.sort .zero) (.sort .zero)) :=
  .ty_lam (.ty_sort trivial) .red_refl (.ty_bvar .zero)

theorem tyAcert : CTy env U Γ a (.sort .zero) :=
  .ty_app tyLamId .red_refl tyU
    (.conv_mk .red_refl .red_refl (.norm_sort (by simp [VLevel.WF]) trivial (by funext ls; rfl)))

theorem tyBcert : CTy env U Γ b (.sort .zero) :=
  .ty_app tyLamId .red_refl tyU'
    (.conv_mk .red_refl .red_refl (.norm_sort (by simp [VLevel.WF]) trivial (by funext ls; rfl)))

/-! ### The theorems -/

/-- **Transport is not size-bounded.** The typed instance `N u u'` (size 53) along the beta
step `u' → Π w'. Π w'. Π w'. Π w'. w'` (size 21) has every possible transported certificate
`N u₁ (Π w' ...)` of size at least 98, whatever the reduct `u₁` of `u`: the argument
comparison `C A A'` of size 19 inside `N w w'` must appear once per occurrence of the bound
variable in the body. -/
theorem transport_output_exceeds_inputs (henv : env.WF) (hex : ConstHeadedEquations env) :
    env.HasType U [] u (.sort (.imax .zero (.imax .zero (.imax .zero (.imax .zero .zero))))) ∧
    env.HasType U [] u' (.sort (.imax .zero (.imax .zero (.imax .zero (.imax .zero .zero))))) ∧
    CertN env U .norm 53 [] u u' ∧ CertN env U .step 21 [] u' (tower 4) ∧
    ∀ Γ x m, CertN env U .norm m Γ x (tower 4) → 53 + 21 < m :=
  ⟨tyU.hasType henv trivial, tyU'.hasType henv trivial, normUU', stepU',
    fun _ _ _ h => by have := norm_tower_ge hex 4 _ h; omega⟩

/-- **The required substitution call does not decrease.** In the transport of `N a b`
(size 60) along the beta step `b → Π w' ...` (size 23), the beta case calls heterogeneous
substitution on the body certificate `N (bvar 0) (bvar 0)` (size 1) and the transported
argument certificate, whose size is at least 98: the total input size of the call, at least
99, exceeds the total input size 83 of the transport instance. -/
theorem substitution_call_not_decreasing (henv : env.WF) (hex : ConstHeadedEquations env) :
    env.HasType U [] a (.sort .zero) ∧ env.HasType U [] b (.sort .zero) ∧
    CertN env U .norm 60 [] a b ∧ CertN env U .step 23 [] b (tower 4) ∧
    ∀ Γ x m, CertN env U .norm m Γ x (tower 4) → 60 + 23 < 1 + m :=
  ⟨tyAcert.hasType henv trivial, tyBcert.hasType henv trivial, normAB, stepB,
    fun _ _ _ h => by have := norm_tower_ge hex 4 _ h; omega⟩

/-- No rank that is a monotone function of the total input size decreases on this call. -/
theorem no_monotone_size_rank (hex : ConstHeadedEquations env) (ρ : Nat → Nat)
    (hρ : ∀ i j, i ≤ j → ρ i ≤ ρ j) :
    ∀ Γ x m, CertN env U .norm m Γ x (tower 4) → ¬ ρ (1 + m) < ρ (60 + 23) := by
  intro Γ x m h hlt
  have := norm_tower_ge hex 4 _ h
  exact absurd hlt (Nat.not_lt.2 (hρ _ _ (by omega)))

end Duplication

end VEnv
end Lean4Lean
