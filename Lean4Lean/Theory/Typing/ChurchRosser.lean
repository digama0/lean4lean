import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift

namespace Lean4Lean
open Lean4Lean

namespace VEnv

open VExpr

/-- A finite structural derivation realizing an installed equation in the
chosen stored-rule/case-schema reduction presentation. The full presentation adds
singleton and quotient prefix unfolding for zero-source occurrences. -/
inductive PatternReductionTrace (env : VEnv) (U : Nat)
    (Pat : (p : Pattern) → p.RHS × p.Check → Prop) :
    List VExpr → VExpr → VExpr → Prop where
  | refl : PatternReductionTrace env U Pat Γ e e
  | trans : PatternReductionTrace env U Pat Γ e e' →
      PatternReductionTrace env U Pat Γ e' e'' → PatternReductionTrace env U Pat Γ e e''
  | pattern : Pat p r → p.Matches e levels values →
      r.2.OK (IsDefEqU env U Γ) levels values →
      PatternReductionTrace env U Pat Γ e (r.1.apply levels values)
  | schema : CaseIota env U Γ e e' → PatternReductionTrace env U Pat Γ e e'
  | beta : PatternReductionTrace env U Pat Γ (.app (.lam domain body) arg) (body.inst arg)
  | app : PatternReductionTrace env U Pat Γ fn fn' → PatternReductionTrace env U Pat Γ arg arg' →
      PatternReductionTrace env U Pat Γ (.app fn arg) (.app fn' arg')
  | lam : PatternReductionTrace env U Pat (domain :: Γ) body body' →
      PatternReductionTrace env U Pat Γ (.lam domain body) (.lam domain body')

class Params where
  env : VEnv
  henv : env.WF
  univs : Nat
  recursorData : Name → Option InductiveSignature.RecursorData
  recursorData_registered : recursorData name = some data →
    RecursorRegistered env data ∧ data.name = name
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  pat_storedRule : Pat p r → PatternHeadsStoredRule env p
  /-- Inductive iota heads retain finite compilation and their case registry.
  Primitive quotient iota retains its exact installed declarations instead.
  Both large-elimination paths exclude zero-source computation here. -/
  pat_recursor : Pat (SimplePattern.iota recursor major ctor fields).toPattern r →
    (∃ data, RecursorRegistered env data ∧ data.name = recursor ∧ data.majorOffset = major ∧ recursorData recursor = some data ∧
      (∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner) ∧
      (data.largeTarget = true → ∃ rest,
        r.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest)) ∨
    (QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, r.2 = .nonzero (.param 0) rest)
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  pat_wf : OnCtx Γ (env.IsType univs) → Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  /-- Definition patterns unfold definitions, never a recursor or the
  registered quotient lift, whose prefixes compute by singleton and quotient prefix
  unfolding. Without the quotient declaration, `Quot.lift` is an ordinary name. -/
  pat_const_not_unfolding : Pat (.const c) r → recursorData c = none ∧ (QuotRegistered env → c ≠ ``Quot.lift)
  /-- The registered quotient lift is not a recursor. -/
  recursorData_quot : QuotRegistered env → recursorData ``Quot.lift = none
  /-- The constructor of a recursor iota pattern carries no computation of its own. -/
  pat_ctor_rigid : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
    env.Rigid cc
  /-- Structure constructors carry no computation of their own. -/
  projection_ctor_rigid : env.projections family info → env.Rigid info.ctorName
  /-- A recursor iota major of structure type is a saturated application of the
  structure's constructor. -/
  pat_struct_major : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
    OnCtx Γ (env.IsType univs) → env.projections family info →
    HasType env univs Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps) →
    fs.length = kc → cc = info.ctorName ∧ kc = info.nparams + info.numFields
  /-- Recursor iota computation at a structure constructor reads only its fields,
  not its parameters. -/
  pat_iota_params {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check} :
    Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
    env.projections family info → cc = info.ctorName →
    ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc) (ps ++ fields)) lsc g →
    ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc') (ps' ++ fields)) lsc' g' →
    ps.length = info.nparams → ps'.length = info.nparams →
    (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr),
      Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          m1 (Sum.elim g1 g) r.1 =
        Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          m1 (Sum.elim g1 g') r.1) ∧
    (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr)
      (df : VExpr → VExpr → Prop),
      Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          df m1 (Sum.elim g1 g) r.2 →
        Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          df m1 (Sum.elim g1 g') r.2)
  /-- A case major of structure type is a saturated application of the structure's
  constructor, and the case rule captures only its fields. -/
  schema_struct_major : CaseRedex env univs Γ rule actual → OnCtx Γ (env.IsType univs) →
    env.projections family info →
    HasType env univs Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
      (VExpr.mkApps (.const family ls) ps) →
    actual.ctorName = info.ctorName ∧
      actual.ctorArguments.length = info.nparams + info.numFields ∧ rule.numFields ≤ info.numFields
variable [Params]
open Params

theorem Params.pat_not_var : ¬Pat (.var p) r := (nomatch pat_simple ·)

theorem Params.pat_not_elim (H : Pat p r)
    (hm : p.Matches (.elim block owner levels) m1 m2) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple H
  cases sp <;> cases hm

/-- Every fixed node of a stored-rule pattern has a constant head. -/
def ConstHeaded : Pattern → Prop
  | .const _ => True
  | .elim _ _ => False
  | .app fn arg => ConstHeaded fn ∧ ConstHeaded arg
  | .var fn => ConstHeaded fn

omit [Params] in
theorem ConstHeaded.varN (h : ConstHeaded p) : ConstHeaded (p.varN n) := by
  induction n with
  | zero => exact h
  | succ _ ih => exact ih

theorem Params.constHeaded (h : Pat p r) : ConstHeaded p := by
  obtain ⟨sp, rfl⟩ := pat_simple h
  cases sp with
  | defn => trivial
  | iota => exact ⟨ConstHeaded.varN trivial, ConstHeaded.varN trivial⟩

omit [Params] in
private theorem constSpine_go_head (e : VExpr) (args : List VExpr) :
    (VExpr.getAppFnArgs.go e args).1 = e.getAppFnArgs.1 := by
  induction e generalizing args with
  | app fn arg ih _ => exact (ih (arg :: args)).trans (ih [arg]).symm
  | _ => rfl

omit [Params] in
theorem ConstHeaded.matches_head (hp : ConstHeaded p) (hm : p.Matches e levels values) :
    ∃ name, e.getAppFnArgs.1 = .const name levels := by
  induction hm with
  | const => exact ⟨_, rfl⟩
  | elim => cases hp
  | app hf ha ih _ =>
    obtain ⟨name, h⟩ := ih hp.1
    exact ⟨name, (constSpine_go_head _ [_]).trans h⟩
  | var hf ih =>
    obtain ⟨name, h⟩ := ih hp
    exact ⟨name, (constSpine_go_head _ [_]).trans h⟩

omit [Params] in
theorem ConstHeaded.subpattern (H : ConstHeaded parent) (hs : Subpattern child parent) : ConstHeaded child := by
  induction hs with
  | refl => exact H
  | appL _ ih => exact ih H.1
  | appR _ ih => exact ih H.2
  | varL _ ih => exact ih H

omit [Params] in
theorem matches_constHead {p : Pattern} {e : VExpr} {levels : List VLevel} {values : p.Path → VExpr} (hm : p.Matches e levels values)
    (hh : e.getAppFnArgs.1 = .const name us) : p.constHead = some name := by
  induction hm with
  | const => cases hh; rfl
  | elim => cases hh
  | app _ _ ih _ => exact ih ((constSpine_go_head _ [_]).symm.trans hh)
  | var _ ih => exact ih ((constSpine_go_head _ [_]).symm.trans hh)

theorem Params.not_rigid_match (h : env.Rigid name) (hp : Pat p r)
    (hm : p.Matches e levels values) (hh : e.getAppFnArgs.1 = .const name us) : False := by
  obtain ⟨equation, originalName, originalLevels, hd, hn, he⟩ := pat_storedRule hp
  have hname := matches_constHead hm hh
  have heq : originalName = name := Option.some.inj (hn.symm.trans hname)
  subst originalName
  exact h equation hd originalLevels ((VExpr.equationHead_eq _).symm.trans he)

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

theorem _root_.Lean4Lean.Pattern.Check.OK.weakN (W : Ctx.LiftN n k Γ Γ') {p : Pattern}
    (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ) m1 m2) :
    ck.OK (IsDefEqU env univs Γ') m1 fun x => (m2 x).liftN n k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.liftN_apply]
  exact h.weakN henv W

theorem _root_.Lean4Lean.Pattern.Check.OK.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H₀ : Γ₀ ⊢ e₀ : A₀)
    {p : Pattern} (ck : p.Check) {m1 m2} (H : ck.OK (IsDefEqU env univs Γ₁) m1 m2) :
    ck.OK (IsDefEqU env univs Γ) m1 fun x => (m2 x).inst e₀ k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.instN_apply]
  exact h.instN henv W H₀

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem IsDefEq.apply_pat
    (ih : ∀ a A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ m2' a)
    (he : Γ ⊢ apply m1 m2 r : A) : Γ ⊢ apply m1 m2 r ≡ apply m1 m2' r : A := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c => exact he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact he.trans_l henv hΓ <| .appDF (ih1 h1) (ih2 h2)
  | var path => exact (ih path _ he).of_l henv hΓ he

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem _root_.Lean4Lean.Pattern.Matches.hasType {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) (H2 : Γ ⊢ e : V) (a) : ∃ A, Γ ⊢ m2 a : A := by
  induction H generalizing V with
  | const | elim => cases a
  | var _ ih =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    exact a.rec ⟨_, ha⟩ (ih hf)
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H2.app_inv henv hΓ
    exact a.rec (ih1 hf) (ih2 ha)

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≡ₚ{" b "}[" n "] " e2:30 => NormalEqN b n Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ[" n "] " e2:30 => NormalEqN true n Γ e1 e2

/-- Normal equality indexed by a bound on the size of the comparison. Leaves
charge zero, congruences charge one plus their premises, and the three eta
constructors charge two. Weakening, substitution and context conversion
preserve the bound. Transitivity recurses on the sum of the bounds; this is
what lets the extensionality constructor `etaBoth` compose with an arbitrary
comparison (removing eta costs two, expanding the other side costs one)
without any inverse weakening. -/
inductive NormalEqN : Bool → Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ{b}[0] e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≡ₚ{b}[0] .sort l₂
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) →
    (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ₚ{b}[0] .const c ls'
  /-- Universe congruence at a disjoint abstract eliminator head. The typing
  witness certifies the selected schema; this rule introduces no computation. -/
  | elimDF :
    Γ ⊢ .elim block owner levels ≡ .elim block owner levels' : A →
    List.Forall₂ (· ≈ ·) levels levels' →
    Γ ⊢ .elim block owner levels ≡ₚ{b}[0] .elim block owner levels'
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≡ₚ{b}[n₁] f₂ → Γ ⊢ a₁ ≡ₚ{b}[n₂] a₂ →
    Γ ⊢ .app f₁ a₁ ≡ₚ{b}[n₁ + n₂ + 1] .app f₂ a₂
  | projDF :
    Γ ⊢ .proj typeName index major : resultType →
    Γ ⊢ major ≡ₚ{b}[n] major' →
    Γ ⊢ .proj typeName index major ≡ₚ{b}[n + 1] .proj typeName index major'
  | lamDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
    A::Γ ⊢ body₁ ≡ₚ{b}[n] body₂ →
    Γ ⊢ .lam A₁ body₁ ≡ₚ{b}[n + 1] .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A₁ ≡ₚ{b}[n₁] A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ{b}[n₂] B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ{b}[n₁ + n₂ + 1] .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ[n] .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≡ₚ[n + 2] e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ[n] e →
    Γ ⊢ e' ≡ₚ[n + 2] .lam A e
  /-- Extensionality: two functions are normally equal when their
  applications to a fresh variable are. -/
  | etaBoth :
    Γ ⊢ e : .forallE A B → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e.lift (.bvar 0) ≡ₚ[n] .app e'.lift (.bvar 0) →
    Γ ⊢ e ≡ₚ[n + 2] e'
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ₚ{b}[0] h'

/-- Normal equality with (`b = true`) or without (`b = false`) eta. -/
def NormalEqF (b : Bool) (Γ : List VExpr) (e1 e2 : VExpr) : Prop := ∃ n, NormalEqN b n Γ e1 e2

/-- Normal equality: some bounded comparison derivation exists. -/
abbrev NormalEq (Γ : List VExpr) (e1 e2 : VExpr) : Prop := NormalEqF true Γ e1 e2

/-- Normal equality without eta: structural congruence up to universe levels and
proof irrelevance. -/
abbrev NormalEq₀ := NormalEqF false

local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ{" b "}" e2:30 => NormalEqF b Γ e1 e2

theorem NormalEqN.normalEq (H : Γ ⊢ e1 ≡ₚ[n] e2) : Γ ⊢ e1 ≡ₚ e2 := ⟨_, H⟩

theorem NormalEq.refl (h : Γ ⊢ e : A) : Γ ⊢ e ≡ₚ e := ⟨_, .refl h⟩
theorem NormalEq.sortDF (h1 : l₁.WF univs) (h2 : l₂.WF univs) (h3 : l₁ ≈ l₂) :
    Γ ⊢ .sort l₁ ≡ₚ .sort l₂ := ⟨_, .sortDF h1 h2 h3⟩
theorem NormalEq.constDF (h1 : env.constants c = some ci) (h2 : ∀ l ∈ ls, l.WF univs)
    (h3 : ∀ l ∈ ls', l.WF univs) (h4 : ls.length = ci.uvars)
    (h5 : List.Forall₂ (· ≈ ·) ls ls') : Γ ⊢ .const c ls ≡ₚ .const c ls' :=
  ⟨_, .constDF h1 h2 h3 h4 h5⟩
theorem NormalEq.elimDF (h1 : Γ ⊢ .elim block owner levels ≡ .elim block owner levels' : A)
    (h2 : List.Forall₂ (· ≈ ·) levels levels') :
    Γ ⊢ .elim block owner levels ≡ₚ .elim block owner levels' := ⟨_, .elimDF h1 h2⟩
theorem NormalEq.appDF (h1 : Γ ⊢ f₁ : .forallE A B) (h2 : Γ ⊢ f₂ : .forallE A B)
    (h3 : Γ ⊢ a₁ : A) (h4 : Γ ⊢ a₂ : A) :
    Γ ⊢ f₁ ≡ₚ f₂ → Γ ⊢ a₁ ≡ₚ a₂ → Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂
  | ⟨_, h5⟩, ⟨_, h6⟩ => ⟨_, .appDF h1 h2 h3 h4 h5 h6⟩
theorem NormalEq.projDF (h1 : Γ ⊢ .proj typeName index major : resultType) :
    Γ ⊢ major ≡ₚ major' → Γ ⊢ .proj typeName index major ≡ₚ .proj typeName index major'
  | ⟨_, h2⟩ => ⟨_, .projDF h1 h2⟩
theorem NormalEq.lamDF (h1 : Γ ⊢ A ≡ A₁ : .sort u) (h2 : Γ ⊢ A ≡ A₂ : .sort u) :
    A::Γ ⊢ body₁ ≡ₚ body₂ → Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂
  | ⟨_, h3⟩ => ⟨_, .lamDF h1 h2 h3⟩
theorem NormalEq.forallEDF (h1 : Γ ⊢ A ≡ A₁ : .sort u) :
    Γ ⊢ A₁ ≡ₚ A₂ → A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂
  | ⟨_, h2⟩, h3, ⟨_, h4⟩ => ⟨_, .forallEDF h1 h2 h3 h4⟩
theorem NormalEq.etaL (h1 : Γ ⊢ e' : .forallE A B) :
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) → Γ ⊢ .lam A e ≡ₚ e'
  | ⟨_, h2⟩ => ⟨_, .etaL h1 h2⟩
theorem NormalEq.etaR (h1 : Γ ⊢ e' : .forallE A B) :
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e → Γ ⊢ e' ≡ₚ .lam A e
  | ⟨_, h2⟩ => ⟨_, .etaR h1 h2⟩
theorem NormalEq.proofIrrel (h1 : Γ ⊢ p : .sort .zero) (h2 : Γ ⊢ h : p) (h3 : Γ ⊢ h' : p) :
    Γ ⊢ h ≡ₚ h' := ⟨_, .proofIrrel h1 h2 h3⟩


theorem NormalEqF.refl (h : Γ ⊢ e : A) : NormalEqF b Γ e e := ⟨_, .refl h⟩
theorem NormalEqF.sortDF (h1 : l₁.WF univs) (h2 : l₂.WF univs) (h3 : l₁ ≈ l₂) :
    NormalEqF b Γ (.sort l₁) (.sort l₂) := ⟨_, .sortDF h1 h2 h3⟩
theorem NormalEqF.constDF (h1 : env.constants c = some ci) (h2 : ∀ l ∈ ls, l.WF univs)
    (h3 : ∀ l ∈ ls', l.WF univs) (h4 : ls.length = ci.uvars)
    (h5 : List.Forall₂ (· ≈ ·) ls ls') : NormalEqF b Γ (.const c ls) (.const c ls') :=
  ⟨_, .constDF h1 h2 h3 h4 h5⟩
theorem NormalEqF.elimDF (h1 : Γ ⊢ .elim block owner levels ≡ .elim block owner levels' : A)
    (h2 : List.Forall₂ (· ≈ ·) levels levels') :
    NormalEqF b Γ (.elim block owner levels) (.elim block owner levels') := ⟨_, .elimDF h1 h2⟩
theorem NormalEqF.appDF (h1 : Γ ⊢ f₁ : .forallE A B) (h2 : Γ ⊢ f₂ : .forallE A B)
    (h3 : Γ ⊢ a₁ : A) (h4 : Γ ⊢ a₂ : A) :
    NormalEqF b Γ f₁ f₂ → NormalEqF b Γ a₁ a₂ → NormalEqF b Γ (.app f₁ a₁) (.app f₂ a₂)
  | ⟨_, h5⟩, ⟨_, h6⟩ => ⟨_, .appDF h1 h2 h3 h4 h5 h6⟩
theorem NormalEqF.projDF (h1 : Γ ⊢ .proj typeName index major : resultType) :
    NormalEqF b Γ major major' →
      NormalEqF b Γ (.proj typeName index major) (.proj typeName index major')
  | ⟨_, h2⟩ => ⟨_, .projDF h1 h2⟩
theorem NormalEqF.lamDF (h1 : Γ ⊢ A ≡ A₁ : .sort u) (h2 : Γ ⊢ A ≡ A₂ : .sort u) :
    NormalEqF b (A::Γ) body₁ body₂ → NormalEqF b Γ (.lam A₁ body₁) (.lam A₂ body₂)
  | ⟨_, h3⟩ => ⟨_, .lamDF h1 h2 h3⟩
theorem NormalEqF.forallEDF (h1 : Γ ⊢ A ≡ A₁ : .sort u) :
    NormalEqF b Γ A₁ A₂ → A::Γ ⊢ B₁ : .sort v → NormalEqF b (A::Γ) B₁ B₂ →
    NormalEqF b Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | ⟨_, h2⟩, h3, ⟨_, h4⟩ => ⟨_, .forallEDF h1 h2 h3 h4⟩
theorem NormalEqF.etaL (h1 : Γ ⊢ e' : .forallE A B) :
    NormalEqF true (A::Γ) e (.app e'.lift (.bvar 0)) → NormalEqF true Γ (.lam A e) e'
  | ⟨_, h2⟩ => ⟨_, .etaL h1 h2⟩
theorem NormalEqF.etaR (h1 : Γ ⊢ e' : .forallE A B) :
    NormalEqF true (A::Γ) (.app e'.lift (.bvar 0)) e → NormalEqF true Γ e' (.lam A e)
  | ⟨_, h2⟩ => ⟨_, .etaR h1 h2⟩
theorem NormalEqF.etaBoth (h1 : Γ ⊢ e : .forallE A B) (h2 : Γ ⊢ e' : .forallE A B) :
    NormalEqF true (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) →
      NormalEqF true Γ e e'
  | ⟨_, h3⟩ => ⟨_, .etaBoth h1 h2 h3⟩
theorem NormalEqF.proofIrrel (h1 : Γ ⊢ p : .sort .zero) (h2 : Γ ⊢ h : p) (h3 : Γ ⊢ h' : p) :
    NormalEqF b Γ h h' := ⟨_, .proofIrrel h1 h2 h3⟩

theorem NormalEqN.toTrue (H : Γ ⊢ e1 ≡ₚ{b}[n] e2) : Γ ⊢ e1 ≡ₚ[n] e2 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | elimDF h1 h2 => exact .elimDF h1 h2
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h1 h2 h3 h4 ih1 ih2
  | projDF h1 _ ih => exact .projDF h1 ih
  | lamDF h1 h2 _ ih => exact .lamDF h1 h2 ih
  | forallEDF h1 _ h3 _ ih1 ih2 => exact .forallEDF h1 ih1 h3 ih2
  | etaL h1 _ ih => exact .etaL h1 ih
  | etaR h1 _ ih => exact .etaR h1 ih
  | etaBoth h1 h2 _ ih => exact .etaBoth h1 h2 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqN.defeq (H : Γ ⊢ e1 ≡ₚ{b}[n] e2) : Γ ⊢ e1 ≡ e2 := by
  induction H with
  | elimDF h _ => exact ⟨_, h⟩
  | refl h => exact ⟨_, h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 =>
    exact ⟨_, .appDF ((ih1 hΓ).of_l henv hΓ hf₁) ((ih2 hΓ).of_l henv hΓ ha₁)⟩
  | projDF hproj _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := hproj.proj_inv henv hΓ
    have majorEq := (ihMajor hΓ).of_l henv hΓ hmajor.hasType.2
    exact ⟨_, .projDF hinfo hlevels huvars hparams hindices hfield
      hfieldTyping hmajor (hmajor.trans majorEq) hclosed hguard⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | lamDF hA₁ hA₂ _ ihB =>
    have ⟨_, hB⟩ := ihB ⟨hΓ, _, hA₁.hasType.1⟩
    exact ⟨_, .trans (.symm <| .lamDF hA₁ hB.symm) (.lamDF hA₂ hB.hasType.2)⟩
  | forallEDF hA₁ hA hB₁ _ ihA ihB =>
    exact have hΓ' := ⟨hΓ, _, hA₁.hasType.1⟩
      ⟨_, .trans (.symm <| .forallEDF hA₁ hB₁)
        (.forallEDF (hA₁.transU_l henv hΓ (ihA hΓ)) ((ihB hΓ').of_l henv hΓ' hB₁))⟩
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_r henv hΓ ⟨_, .lamDF hA he⟩ (.eta h1)⟩
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_l henv hΓ (.symm (.eta h1)) ⟨_, .lamDF hA he⟩⟩
  | etaBoth h1 h2 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := AB.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA.hasType.1⟩; have ⟨_, he⟩ := ih hΓ'; ?_
    exact ⟨_, .transU_l henv hΓ (.symm (.eta h1))
      ⟨_, .transU_r henv hΓ ⟨_, .lamDF hA he⟩ (.eta h2)⟩⟩
  | proofIrrel h1 h2 h3 => exact ⟨_, .proofIrrel h1 h2 h3⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.defeq : Γ ⊢ e1 ≡ₚ e2 → Γ ⊢ e1 ≡ e2
  | ⟨_, H⟩ => H.defeq hΓ

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqF.defeq : NormalEqF b Γ e1 e2 → Γ ⊢ e1 ≡ e2
  | ⟨_, H⟩ => H.defeq hΓ

theorem NormalEqF.toNormalEq : NormalEqF b Γ e1 e2 → Γ ⊢ e1 ≡ₚ e2
  | ⟨_, H⟩ => ⟨_, H.toTrue⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqN.symm (H : Γ ⊢ e1 ≡ₚ{b}[n] e2) : Γ ⊢ e2 ≡ₚ{b}[n] e1 := by
  induction H with
  | elimDF h heq => exact .elimDF h.symm (heq.flip.imp fun _ _ h => h.symm)
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 (ih1 hΓ) (ih2 hΓ)
  | projDF hproj hMajor ihMajor =>
    have ⟨_, whole⟩ := (NormalEqN.projDF hproj hMajor).defeq hΓ
    exact .projDF whole.hasType.2 (ihMajor hΓ)
  | lamDF h1 h2 h3 ih1 => exact .lamDF h2 h1 (ih1 ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF h1 h2 h4 h5 ih1 ih2 =>
    exact have hΓ' := ⟨hΓ, _, h1.hasType.1⟩
      .forallEDF (h1.transU_l henv hΓ (h2.defeq hΓ)) (ih1 hΓ)
        (.defeqU_l henv hΓ' (h5.defeq hΓ') h4) (ih2 hΓ')
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaR h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaL h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | etaBoth h1 h2 _ ih =>
    have ⟨_, AB⟩ := h1.isType henv hΓ
    exact .etaBoth h2 h1 (ih ⟨hΓ, (AB.forallE_inv henv).1⟩)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.symm : Γ ⊢ e1 ≡ₚ e2 → Γ ⊢ e2 ≡ₚ e1
  | ⟨_, H⟩ => ⟨_, H.symm hΓ⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqF.symm : NormalEqF b Γ e1 e2 → NormalEqF b Γ e2 e1
  | ⟨_, H⟩ => ⟨_, H.symm hΓ⟩

theorem NormalEqN.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ≡ₚ{b}[m] e2) :
    Γ' ⊢ e1.liftN n k ≡ₚ{b}[m] e2.liftN n k := by
  induction H generalizing k Γ' with
  | elimDF h heq => exact .elimDF (h.weakN henv W) heq
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN henv W) (h2.weakN henv W)
      (h3.weakN henv W) (h4.weakN henv W) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (hproj.weakN henv W) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
     exact .lamDF (h1.weakN henv W) (h2.weakN henv W) (ih1 W.succ)
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN henv W) (ih1 W) (h3.weakN henv W.succ) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR h1 _ ih =>
    refine .etaR (h1.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaBoth h1 h2 _ ih =>
    refine .etaBoth (h1.weakN henv W) (h2.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN', lift_liftN']
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W)

theorem NormalEq.weakN (W : Ctx.LiftN n k Γ Γ') : Γ ⊢ e1 ≡ₚ e2 →
    Γ' ⊢ e1.liftN n k ≡ₚ e2.liftN n k
  | ⟨_, H⟩ => ⟨_, H.weakN W⟩

theorem NormalEqF.weakN (W : Ctx.LiftN n k Γ Γ') : NormalEqF b Γ e1 e2 →
    NormalEqF b Γ' (e1.liftN n k) (e2.liftN n k)
  | ⟨_, H⟩ => ⟨_, H.weakN W⟩

variable! (h₀ : Γ₀ ⊢ e₀ : A₀) in
theorem NormalEqN.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e1 ≡ₚ{b}[m] e2) :
    Γ ⊢ e1.inst e₀ k ≡ₚ{b}[m] e2.inst e₀ k := by
  induction H generalizing Γ k with
  | elimDF h heq => exact .elimDF (h.instN henv h₀ W) heq
  | refl h => exact .refl (h.instN henv W h₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀) (h4.instN henv W h₀) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (hproj.instN henv W h₀) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (h1.instN henv h₀ W) (h2.instN henv h₀ W) (ih1 W.succ)
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (h1.instN henv h₀ W) (ih1 W) (h3.instN henv W.succ h₀) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | etaR h1 _ ih =>
    refine .etaR (h1.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | etaBoth h1 h2 _ ih =>
    refine .etaBoth (h1.instN henv W h₀) (h2.instN henv W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.instN henv W h₀) (h2.instN henv W h₀) (h3.instN henv W h₀)

variable! (h₀ : Γ₀ ⊢ e₀ : A₀) in
theorem NormalEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) : Γ₁ ⊢ e1 ≡ₚ e2 →
    Γ ⊢ e1.inst e₀ k ≡ₚ e2.inst e₀ k
  | ⟨_, H⟩ => ⟨_, H.instN h₀ W⟩

variable! (h₀ : Γ₀ ⊢ e₀ : A₀) in
theorem NormalEqF.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) : NormalEqF b Γ₁ e1 e2 →
    NormalEqF b Γ (e1.inst e₀ k) (e2.inst e₀ k)
  | ⟨_, H⟩ => ⟨_, H.instN h₀ W⟩

variable! (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : Γ₀ ⊢ e₀ : A₀) (H' : Γ₀ ⊢ e₀ ≡ₚ{η} e₀') in
theorem NormalEqF.instN_r (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Γ₁ ⊢ e : A) :
    Γ ⊢ e.inst e₀ k ≡ₚ{η} e.inst e₀' k := by
  induction e generalizing Γ₁ Γ k A with dsimp [inst]
  | bvar i =>
    have ⟨ty, h⟩ := H.bvar_inv henv hΓ₁; clear H hΓ₁
    induction W generalizing i ty with
    | zero =>
      cases h with simp
      | zero => exact H'
      | succ h => exact .refl (.bvar h)
    | succ _ ih =>
      cases h with simp
      | zero => exact .refl (.bvar .zero)
      | succ h => exact (ih _ _ h).weakN .one
  | sort => exact .refl (.sort (H.sort_inv henv))
  | const =>
    let ⟨_, h1, h2, h3⟩ := H.const_inv henv hΓ₁
    exact .refl (.const h1 h2 h3)
  | elim => exact .refl (H.instN henv W h₀)
  | app fn arg ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := H.app_inv henv hΓ₁
    specialize ih1 hΓ₁ W h1; have hf := h1.instN henv W h₀
    specialize ih2 hΓ₁ W h2; have ha := h2.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .appDF hf (.defeqU_l henv hΓ (ih1.defeq hΓ) hf) ha
      (.defeqU_l henv hΓ (ih2.defeq hΓ) ha) ih1 ih2
  | proj typeName index major ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := H.proj_inv henv hΓ₁
    have majorNormal := ihMajor hΓ₁ W hmajor.hasType.2
    have natural : Γ₁ ⊢ .proj typeName index major : fieldType :=
      .projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
        hmajor hmajor hclosed hguard
    exact .projDF (natural.instN henv W h₀) majorNormal
  | lam A body ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.lam_inv henv hΓ₁
    have hA := h1.instN henv W h₀
    let ⟨hΓ₀, hΓ⟩ := W.wf henv h₀ hΓ₁
    exact .lamDF hA (((ih1 hΓ₁ W h1).defeq hΓ).of_l henv hΓ hA)
      (ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2)
  | forallE A B ih1 ih2 =>
    let ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv
    have hA := h1.instN henv W h₀
    exact .forallEDF hA (ih1 hΓ₁ W h1) (h2.instN henv W.succ h₀)
      (ih2 (by exact ⟨hΓ₁, _, h1⟩) W.succ h2)

alias NormalEq.instN_r := NormalEqF.instN_r

variable! (H₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEqN.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ{b}[m] e2) : Γ₂ ⊢ e1 ≡ₚ{b}[m] e2 := by
  induction H generalizing Γ₂ with
  | elimDF h heq => exact .elimDF (h.defeqDFC henv W) heq
  | refl h => refine .refl (.defeqDFC henv W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (.defeqDFC henv W h1) (.defeqDFC henv W h2)
      (.defeqDFC henv W h3) (.defeqDFC henv W h4) (ih1 W) (ih2 W)
  | projDF hproj _ ihMajor =>
    exact .projDF (.defeqDFC henv W hproj) (ihMajor W)
  | lamDF h1 h2 h3 ih1 =>
    exact .lamDF (.defeqDFC henv W h1) (.defeqDFC henv W h2) (ih1 (W.succ h1.hasType.1))
  | forallEDF h1 h2 h3 _ ih1 ih2 =>
    exact .forallEDF (.defeqDFC henv W h1) (ih1 W)
      (.defeqDFC henv (W.succ h1.hasType.1) h3) (ih2 (W.succ h1.hasType.1))
  | etaL h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaL (.defeqDFC henv W h1) (ih (W.succ h2))
  | etaR h1 _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaR (.defeqDFC henv W h1) (ih (W.succ h2))
  | etaBoth h1 h1' _ ih =>
    have ⟨⟨_, h2⟩, _⟩ := let ⟨_, h⟩ := h1.isType henv (W.isType' H₀); h.forallE_inv henv
    refine .etaBoth (.defeqDFC henv W h1) (.defeqDFC henv W h1') (ih (W.succ h2))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (.defeqDFC henv W h1)
      (.defeqDFC henv W h2) (.defeqDFC henv W h3)

variable! (H₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEq.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) :
    Γ₁ ⊢ e1 ≡ₚ e2 → Γ₂ ⊢ e1 ≡ₚ e2
  | ⟨_, H⟩ => ⟨_, H.defeqDFC H₀ W⟩

variable! (H₀ : OnCtx Γ₀ (IsType env univs)) in
theorem NormalEqF.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) :
    NormalEqF b Γ₁ e1 e2 → NormalEqF b Γ₂ e1 e2
  | ⟨_, H⟩ => ⟨_, H.defeqDFC H₀ W⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEqN.defeq_l (W : Γ ⊢ A ≡ A' : sort u) (H : A::Γ ⊢ e1 ≡ₚ{b}[m] e2) :
    A'::Γ ⊢ e1 ≡ₚ{b}[m] e2 := defeqDFC hΓ (.succ .zero W) H

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.defeq_l (W : Γ ⊢ A ≡ A' : sort u) (H : A::Γ ⊢ e1 ≡ₚ e2) :
    A'::Γ ⊢ e1 ≡ₚ e2 := defeqDFC hΓ (.succ .zero W) H

theorem NormalEqN.trans (hΓ : OnCtx Γ (IsType env univs)) :
    Γ ⊢ e1 ≡ₚ{b}[n₁] e2 → Γ ⊢ e2 ≡ₚ{b}[n₂] e3 → NormalEqF b Γ e1 e3
  | .elimDF l1 l2, .elimDF r1 r2 =>
    .elimDF (l1.trans_l henv hΓ r1) (l2.trans (fun _ _ _ h1 => h1.trans) r2)
  | .sortDF l1 _ l3, .sortDF r1 r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 ((r1.uniqU henv hΓ l2).defeqDF henv hΓ r2) l3
      ((r3.uniqU henv hΓ l4).defeqDF henv hΓ r4) (l5.trans hΓ r5) (l6.trans hΓ r6)
  | .projDF l1 l2, .projDF _ r2 =>
    .projDF l1 (l2.trans hΓ r2)
  | .lamDF l1 l2 l3, .lamDF r1 r2 r3 =>
    have aa := r1.trans_r henv hΓ l2.symm
    .lamDF l1 (aa.symm.trans_l henv hΓ r2) (l3.trans ⟨hΓ, _, l1.hasType.1⟩ (r3.defeq_l hΓ aa))
  | .forallEDF l1 l2 l3 l4, .forallEDF r1 r2 r3 r4 =>
    have r4' := r4.defeq_l hΓ (.trans_l henv hΓ (.transU_l henv hΓ r1 (l2.defeq hΓ).symm) l1.symm)
    .forallEDF l1 (l2.trans hΓ r2) l3 (l4.trans ⟨hΓ, _, l1.hasType.1⟩ r4')
  | .etaR l1 ih, .lamDF r1 r2 r3 =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have eq := r1.symm.trans r2
    .etaR (IsDefEq.defeq (.forallEDF eq hB) l1) <|
      (ih.defeq_l hΓ eq).trans ⟨hΓ, _, r2.hasType.2⟩ (r3.defeq_l hΓ r2)
  | .lamDF l1 l2 l3, .etaL r1 ih =>
    have ⟨_, _, hB⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    have eq := l2.symm.trans l1
    .etaL (IsDefEq.defeq (.forallEDF eq hB) r1) <|
      (l3.defeq_l hΓ l1).trans ⟨hΓ, _, l1.hasType.2⟩ (ih.defeq_l hΓ eq)
  | H1@(.etaR l1 ihl), H2@(.etaL r1 ihr) => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have hd := (H1.defeq hΓ).trans henv hΓ (H2.defeq hΓ)
    exact .etaBoth l1 (.defeqU_l henv hΓ hd l1) (ihl.trans (by exact ⟨hΓ, _, hA⟩) ihr)
  | .refl _, H2 => ⟨_, H2⟩
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (.defeqU_l henv hΓ (H2.defeq hΓ) l3)
  | .etaL l1 ih, H2 => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have h2 := NormalEqN.appDF (l1.weakN henv .one)
      ((l1.defeqU_l henv hΓ (H2.defeq hΓ)).weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H2) (.refl (.bvar .zero))
    exact .etaL (.defeqU_l henv hΓ (H2.defeq hΓ) l1) (ih.trans ⟨hΓ, _, hA⟩ h2)
  | .etaBoth l1 l2 ih, H2 => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    have h2 := NormalEqN.appDF (l2.weakN henv .one)
      ((l2.defeqU_l henv hΓ (H2.defeq hΓ)).weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H2) (.refl (.bvar .zero))
    exact .etaBoth l1 (.defeqU_l henv hΓ (H2.defeq hΓ) l2) (ih.trans ⟨hΓ, _, hA⟩ h2)
  | H1, .refl _ => ⟨_, H1⟩
  | H1, .etaR r1 ih => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    have h1 := NormalEqN.appDF ((r1.defeqU_l henv hΓ (H1.defeq hΓ).symm).weakN henv .one)
      (r1.weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H1) (.refl (.bvar .zero))
    exact .etaR (.defeqU_l henv hΓ (H1.defeq hΓ).symm r1) (h1.trans ⟨hΓ, _, hA⟩ ih)
  | H1, .etaBoth r1 r2 ih => by
    have ⟨⟨_, hA⟩, _⟩ := let ⟨_, h⟩ := r1.isType henv hΓ; h.forallE_inv henv
    have h1 := NormalEqN.appDF ((r1.defeqU_l henv hΓ (H1.defeq hΓ).symm).weakN henv .one)
      (r1.weakN henv .one) (.bvar .zero) (.bvar .zero)
      (.weakN .one H1) (.refl (.bvar .zero))
    exact .etaBoth (.defeqU_l henv hΓ (H1.defeq hΓ).symm r1) r2 (h1.trans ⟨hΓ, _, hA⟩ ih)
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (.defeqU_l henv hΓ (H1.defeq hΓ).symm h2) h3
termination_by n₁ + n₂

theorem NormalEq.trans (hΓ : OnCtx Γ (IsType env univs)) :
    Γ ⊢ e1 ≡ₚ e2 → Γ ⊢ e2 ≡ₚ e3 → Γ ⊢ e1 ≡ₚ e3
  | ⟨_, H1⟩, ⟨_, H2⟩ => H1.trans hΓ H2

theorem NormalEqF.trans (hΓ : OnCtx Γ (IsType env univs)) :
    NormalEqF b Γ e1 e2 → NormalEqF b Γ e2 e3 → NormalEqF b Γ e1 e3
  | ⟨_, H1⟩, ⟨_, H2⟩ => H1.trans hΓ H2

open Pattern.RHS in
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEqF.apply_pat
    (ih : ∀ a A, Γ ⊢ m2 a : A → Γ ⊢ m2 a ≡ₚ{η} m2' a)
    (he : Γ ⊢ apply m1 m2 r : A) :
    Γ ⊢ apply m1 m2 r ≡ₚ{η} apply m1 m2' r := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed c => exact .refl he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .appDF h1 (.defeqU_l henv hΓ ((ih1 h1).defeq hΓ) h1)
      h2 (.defeqU_l henv hΓ ((ih2 h2).defeq hΓ) h2) (ih1 h1) (ih2 h2)
  | var path => exact ih path _ he

alias NormalEq.apply_pat := NormalEqF.apply_pat

set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ⋙ " e2:36 => CParRed Γ e1 e2

inductive ParRed : List VExpr → VExpr → VExpr → Prop where
  | schema {rule : InductiveSignature.CaseSchema.AppliedRule}
      {actual : InductiveSignature.CaseSchema.Application} :
    CaseRedex env univs Γ rule actual →
    (hlength : arguments.length = (rule.capture actual).length) →
    (∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ≫ arguments[i]'(by omega)) →
    Γ ⊢ actual.expr ≫ rule.rhs actual.levels arguments
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | elim : Γ ⊢ .elim block owner ls ≫ .elim block owner ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | proj : Γ ⊢ major ≫ major' →
      Γ ⊢ .proj typeName index major ≫ .proj typeName index major'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'

/-- The concrete stored-rule and registered-schema head developments, including
parallel reduction of their captured arguments. -/
inductive HeadParallelReduction (Γ : List VExpr) : VExpr → VExpr → Prop where
  | pattern : Pat p r → p.Matches e m1 m2 →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) →
    HeadParallelReduction Γ e (r.1.apply m1 m2')
  | schema {rule : InductiveSignature.CaseSchema.AppliedRule}
      {actual : InductiveSignature.CaseSchema.Application} :
    CaseRedex env univs Γ rule actual →
    (hlength : arguments.length = (rule.capture actual).length) →
    (∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ≫ arguments[i]'(by omega)) →
    HeadParallelReduction Γ actual.expr (rule.rhs actual.levels arguments)

/-- A beta-redex cannot simultaneously have an abstract case head. -/
theorem ParRed.app_lam_cases (H : Γ ⊢ .app (.lam A body) arg ≫ out) :
    (∃ fn' arg', Γ ⊢ .lam A body ≫ fn' ∧ Γ ⊢ arg ≫ arg' ∧ out = .app fn' arg') ∨
    (∃ body' arg', A :: Γ ⊢ body ≫ body' ∧ Γ ⊢ arg ≫ arg' ∧ out = body'.inst arg') := by
  generalize he : VExpr.app (.lam A body) arg = source at H
  cases H with
  | schema hm hl hr =>
    have hfn := VExpr.app.inj he |>.1
    exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
  | app hf ha => cases he; exact .inl ⟨_, _, hf, ha, rfl⟩
  | beta hb ha => cases he; exact .inr ⟨_, _, hb, ha, rfl⟩
  | extra hp hm =>
    obtain ⟨sp, rfl⟩ := pat_simple hp
    obtain ⟨name, hhead⟩ := InductiveSignature.CaseSchema.recursor_pattern_head hm
    rw [← he] at hhead
    cases hhead
  | _ => cases he

def NonNeutral (Γ : List VExpr) (e : VExpr) : Prop :=
  (∃ A e₁ e₂, e = .app (.lam A e₁) e₂) ∨
  ((∃ p r m1 m2, Pat p r ∧ p.Matches e m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2) ∨
    ∃ rule actual, CaseRedex env univs Γ rule actual ∧ e = actual.expr)

inductive CParRed : List VExpr → VExpr → VExpr → Prop where
  | schema {rule : InductiveSignature.CaseSchema.AppliedRule}
      {actual : InductiveSignature.CaseSchema.Application} :
    CaseRedex env univs Γ rule actual →
    (hlength : arguments.length = (rule.capture actual).length) →
    (∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ⋙ arguments[i]'(by omega)) →
    Γ ⊢ actual.expr ⋙ rule.rhs actual.levels arguments
  | bvar : Γ ⊢ .bvar i ⋙ .bvar i
  | sort : Γ ⊢ .sort u ⋙ .sort u
  | const : ¬NonNeutral Γ (.const c ls) → Γ ⊢ .const c ls ⋙ .const c ls
  | elim : ¬NonNeutral Γ (.elim block owner ls) → Γ ⊢ .elim block owner ls ⋙ .elim block owner ls
  | app : ¬NonNeutral Γ (.app f a) → Γ ⊢ f ⋙ f' → Γ ⊢ a ⋙ a' → Γ ⊢ .app f a ⋙ .app f' a'
  | proj : ¬NonNeutral Γ (.proj typeName index major) →
      Γ ⊢ major ⋙ major' →
      Γ ⊢ .proj typeName index major ⋙ .proj typeName index major'
  | lam : Γ ⊢ A ⋙ A' → A::Γ ⊢ body ⋙ body' → Γ ⊢ .lam A body ⋙ .lam A' body'
  | forallE : Γ ⊢ A ⋙ A' → A::Γ ⊢ B ⋙ B' → Γ ⊢ .forallE A B ⋙ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ⋙ e₁' → Γ ⊢ e₂ ⋙ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ⋙ e₁'.inst e₂'
  | extra : Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ⋙ m2' a) → Γ ⊢ e ⋙ r.1.apply m1 m2'

protected theorem ParRed.rfl : ∀ {e}, Γ ⊢ e ≫ e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app ParRed.rfl ParRed.rfl
  | .proj .. => .proj ParRed.rfl
  | .lam .. => .lam ParRed.rfl ParRed.rfl
  | .forallE .. => .forallE ParRed.rfl ParRed.rfl


theorem schema_mkApps_head_type (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ mkApps fn args : type) : ∃ headType, Γ ⊢ fn : headType := by
  induction args generalizing fn with
  | nil => exact ⟨_, ht⟩
  | cons arg args ih =>
    obtain ⟨_, happ⟩ := ih ht
    obtain ⟨_, _, hfn, _⟩ := happ.app_inv henv hΓ
    exact ⟨_, hfn⟩


theorem schema_mkApps_arg_type (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ mkApps fn args : type) (hmem : arg ∈ args) : ∃ argType, Γ ⊢ arg : argType := by
  induction args generalizing fn with
  | nil => cases hmem
  | cons first args ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem
    · obtain ⟨_, hhead⟩ := schema_mkApps_head_type hΓ (fn := .app fn _) ht
      obtain ⟨_, _, _, ha⟩ := hhead.app_inv henv hΓ
      exact ⟨_, ha⟩
    · exact ih ht hmem

theorem ParRed.elim_prefix
    (Hfixed : CaseStep env univs Γ rule levels captured)
    (hlen : args.length ≤ rule.application.arguments.length)
    (H : Γ ⊢ VExpr.mkApps (.elim rule.application.block rule.application.owner packed) args ≫ out) :
    ∃ args', out = VExpr.mkApps (.elim rule.application.block rule.application.owner packed) args' ∧
      List.Forall₂ (ParRed Γ) args args' := by
  induction args using List.snoc_induction generalizing out with
  | nil =>
    cases H with
    | elim => exact ⟨[], rfl, .nil⟩
    | extra hp hm => exact False.elim (Params.pat_not_elim hp hm)
  | snoc args arg ih =>
    generalize he : VExpr.mkApps (.elim rule.application.block rule.application.owner packed) (args ++ [arg]) = source at H
    have hshape : source = .app (VExpr.mkApps (.elim rule.application.block rule.application.owner packed) args) arg := by
      rw [← he]
      simp [VExpr.mkApps, List.foldl_append]
    cases H with
    | schema hm => exact False.elim (hm.not_elim_prefix henv Hfixed he.symm hlen)
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih (by simp only [List.length_append, List.length_singleton] at hlen; omega) hf
      refine ⟨args' ++ [arg'], ?_, ?_⟩
      · simp [VExpr.mkApps, List.foldl_append]
      · exact List.Forall₂.append' hargs (.cons ha .nil)
    | beta =>
      have hfn := VExpr.app.inj hshape |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
    | extra hp hm =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      obtain ⟨name, hh⟩ := InductiveSignature.CaseSchema.recursor_pattern_head hm
      rw [← he, InductiveSignature.spine_mkApps_exact _ _ rfl] at hh
      cases hh
    | _ => cases hshape

theorem ParRed.rigid_const_spine (hrigid : env.Rigid name)
    (H : Γ ⊢ VExpr.mkApps (.const name levels) args ≫ out) :
    ∃ args', out = VExpr.mkApps (.const name levels) args' ∧
      List.Forall₂ (ParRed Γ) args args' := by
  induction args using List.snoc_induction generalizing out with
  | nil =>
    cases H with
    | const => exact ⟨[], rfl, .nil⟩
    | extra hp hm => exact False.elim (Params.not_rigid_match hrigid hp hm rfl)
  | snoc args arg ih =>
    generalize he : VExpr.mkApps (.const name levels) (args ++ [arg]) = source at H
    have hshape : source = .app (VExpr.mkApps (.const name levels) args) arg := by
      rw [← he]
      simp [VExpr.mkApps, List.foldl_append]
    have hhead : source.getAppFnArgs.1 = .const name levels := by
      rw [← he, InductiveSignature.spine_mkApps_exact _ _ rfl]
    cases H with
    | schema hm =>
      rw [InductiveSignature.CaseSchema.Application.head] at hhead
      cases hhead
    | @app _ _ _ _ arg' hf ha =>
      cases hshape
      obtain ⟨args', rfl, hargs⟩ := ih hf
      refine ⟨args' ++ [arg'], ?_, List.Forall₂.append' hargs (.cons ha .nil)⟩
      simp [VExpr.mkApps, List.foldl_append]
    | beta =>
      have hfn := VExpr.app.inj hshape |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn.symm)
    | extra hp hm => exact False.elim (Params.not_rigid_match hrigid hp hm hhead)
    | _ => cases hshape

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqF.instantiate_variables (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      Γ ⊢ arguments[i] ≡ₚ{η} arguments'[i])
    (ht : Γ ⊢ InductiveSignature.instantiateParams body arguments : type) :
    Γ ⊢ InductiveSignature.instantiateParams body arguments ≡ₚ{η}
      InductiveSignature.instantiateParams body arguments' := by
  induction H generalizing type with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by change i < arguments.length at hc; omega)
      (by change i < arguments.length at hc; omega)
  | app hf ha ihf iha =>
    have ⟨_, _, hfn, harg⟩ := ht.app_inv henv hΓ
    have hnf := ihf hc.1 hfn
    have hna := iha hc.2 harg
    exact .appDF hfn ((hnf.defeq hΓ).of_l henv hΓ hfn).hasType.2
      harg ((hna.defeq hΓ).of_l henv hΓ harg).hasType.2 hnf hna

alias NormalEq.instantiate_variables := NormalEqF.instantiate_variables


theorem ParRed.of_schema (H : CaseIota env univs Γ e e') : Γ ⊢ e ≫ e' := by
  cases H with
  | iota hm => exact .schema hm rfl fun _ _ => .rfl

theorem ParRed.wrapLams (H : domains.reverse ++ Γ ⊢ body ≫ body') :
    Γ ⊢ VExpr.wrapLams domains body ≫ VExpr.wrapLams domains body' := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons domain domains ih =>
    apply ParRed.lam .rfl
    apply ih
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H

theorem ParRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e1 ≫ e2) :
    Γ' ⊢ e1.liftN n k ≫ e2.liftN n k := by
  induction H generalizing k Γ' with
  | @schema Γ args rule actual hm hl _ ih =>
    have hc : (rule.body.rhs.instL actual.levels).ClosedN args.length := by
      simpa [hl] using hm.source.closed.2.1.instL
    have hnew : Γ' ⊢ (CaseApplicationMap actual fun e => e.liftN n k).expr ≫
        rule.rhs actual.levels (args.map fun e => e.liftN n k) := by
      refine .schema (hm.weakN henv W) (by simpa only [List.length_map, case_capture_map] using hl) ?_
      intro i hi
      have hi' : i < (rule.capture actual).length := by simpa only [case_capture_map, List.length_map] using hi
      simpa only [case_capture_map, List.getElem_map] using ih i hi' W
    simpa only [case_application_liftN, InductiveSignature.CaseSchema.AppliedRule.rhs,
      instantiateParams_liftN hc] using hnew
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ihMajor => exact .proj (ihMajor W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.liftN_apply]
    refine .extra h1 (Pattern.matches_liftN.2 ⟨_, h2, funext_iff.1 rfl⟩)
      (h3.weakN W) (fun a => ih _ W)

variable! (H₀ : Γ₀ ⊢ a1 ≫ a2) (H₀' : Γ₀ ⊢ a1 : A₀) in
theorem ParRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ≫ e2) : Γ ⊢ e1.inst a1 k ≫ e2.inst a2 k := by
  induction H generalizing Γ k with
  | @schema sourceCtx args rule actual hm hl _ ih =>
    have hc : (rule.body.rhs.instL actual.levels).ClosedN args.length := by
      simpa [hl] using hm.source.closed.2.1.instL
    have hnew : Γ ⊢ (CaseApplicationMap actual fun e => e.inst a1 k).expr ≫
        rule.rhs actual.levels (args.map fun e => e.inst a2 k) := by
      refine .schema (hm.instN henv H₀' W) (by simpa only [List.length_map, case_capture_map] using hl) ?_
      intro i hi
      have hi' : i < (rule.capture actual).length := by simpa only [case_capture_map, List.length_map] using hi
      simpa only [case_capture_map, List.getElem_map] using ih i hi' W
    simpa only [case_application_instN, InductiveSignature.CaseSchema.AppliedRule.rhs,
      instantiateParams_instN hc] using hnew
  | @bvar _ i =>
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact ih.weakN .one
  | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ihMajor => exact .proj (ihMajor W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [inst, inst0_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.instN_apply]
    exact .extra h1 (Pattern.matches_instN h2) (h3.instN W H₀') (fun a => ih _ W)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.defeq (H : Γ ⊢ e ≫ e') (he : Γ ⊢ e : A) : Γ ⊢ e ≡ e' : A := by
  induction H generalizing A with
  | schema hm hl _ ih =>
    have hbase := (CaseIota.iota hm).defeq henv hΓ
    have hargs := hm.source.rhs_congr henv hΓ hl fun i hi _ =>
      let ⟨_, ht⟩ := hm.capture_typed (List.getElem_mem hi)
      ⟨_, ih i hi hΓ ht⟩
    exact (hbase.trans henv hΓ hargs).of_l henv hΓ he

  | bvar | sort | const | elim => exact he
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact .trans_l henv hΓ he <| .appDF (ih1 hΓ h1) (ih2 hΓ h2)
  | proj _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, hclosed, hguard⟩ := he.proj_inv henv hΓ
    have majorEq := ihMajor hΓ hmajor.hasType.2
    have projected := IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hmajor (hmajor.trans majorEq) hclosed hguard
    have ⟨_, typeToA⟩ := projected.hasType.1.uniq henv hΓ he
    exact .defeqDF typeToA projected
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact .trans_l henv hΓ he <| .lamDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact .trans_l henv hΓ he <| .forallEDF (ih1 hΓ h1) (ih2 ⟨hΓ, _, h1⟩ h2)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    have hf' := hA.lam hb
    have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (hf.uniqU henv hΓ hf')
    replace ha := ha.defeqU_r henv hΓ ⟨_, u1⟩
    exact .trans_l henv hΓ he <| .trans
      (.symm <| .appDF (.symm <| .lamDF hA (ih1 ⟨hΓ, _, hA⟩ hb)) (.symm <| ih2 hΓ ha))
      (.beta (ih1 ⟨hΓ, _, hA⟩ hb).hasType.2 (ih2 hΓ ha).hasType.2)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .trans_l henv hΓ he <| .transU_r henv hΓ (pat_wf hΓ h1 h2 he h3) <|
     .apply_pat hΓ (fun _ _ h => ⟨_, ih _ hΓ h⟩) (.defeqU_l henv hΓ (pat_wf hΓ h1 h2 he h3) he)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.hasType (H : Γ ⊢ e ≫ e') (he : Γ ⊢ e : A) : Γ ⊢ e' : A :=
  (H.defeq hΓ he).hasType.2

variable! (hΓ₀ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRed.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ≫ e2) : Γ₂ ⊢ e1 ≫ e2 := by
  induction H generalizing Γ₂ A with
  | schema hm hl _ ih =>
    exact .schema (hm.defeqDFC henv W) hl fun i hi =>
      let ⟨_, ht⟩ := hm.capture_typed (List.getElem_mem hi)
      ih i hi W ht
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    exact .app (ih1 W hf) (ih2 W ha)
  | proj _ ihMajor =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      h.proj_inv henv (W.isType' hΓ₀)
    exact .proj (ihMajor W hmajor.hasType.2)
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := h.lam_inv henv (W.isType' hΓ₀)
    exact .lam (ih1 W hA) (ih2 (W.succ hA) he)
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := h.forallE_inv henv
    exact .forallE (ih1 W hA) (ih2 (W.succ hA) hB)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := h.app_inv henv (W.isType' hΓ₀)
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv (W.isType' hΓ₀)
    exact .beta (ih1 (W.succ hA) hb) (ih2 W ha)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .extra h1 h2 (h3.map fun a b h => h.defeqDFC henv W) fun a =>
      let ⟨_, h⟩ := h2.hasType (W.isType' hΓ₀) h a; ih a W h

theorem ParRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, Γ ⊢ m2 a ≫ m3 a) : Γ ⊢ r.apply m1 m2 ≫ r.apply m1 m3 := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

omit [Params] in
theorem _root_.Lean4Lean.Pattern.RHS.apply_lift' {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).lift' ρ = r.apply m1 (fun a => (m2 a).lift' ρ) := by
  induction r with simp! [*]
  | fixed _ h => exact instL_lift'.symm.trans ((h.lift'_eq trivial).symm ▸ rfl)

omit [Params] in
theorem _root_.Lean4Lean.Pattern.RHS.apply_liftN {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).liftN k n = r.apply m1 (fun a => (m2 a).liftN k n) := by
  simp [← lift'_consN_skipN, Pattern.RHS.apply_lift']

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem HasType.matches_inv {p : Pattern} {m1 m2} (H : Γ ⊢ e : A)
    (H2 : p.Matches e m1 m2) : ∀ a, ∃ A, Γ ⊢ m2 a : A := by
  induction H2 generalizing A with
  | const | elim => nofun
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    rintro (h|h) <;> [exact ih1 hf h; exact ih2 ha h]
  | var _ ih1 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    rintro (_|h) <;> [exact ⟨_, ha⟩; exact ih1 hf h]


theorem CParRed.toParRed (H : Γ ⊢ e ⋙ e') : Γ ⊢ e ≫ e' := by
  induction H with
  | schema hm hl _ ih => exact .schema hm hl ih
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | elim => exact .elim
  | app _ _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ _ ihMajor => exact .proj ihMajor
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih3 => exact .extra h1 h2 h3 ih3

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CParRed.exists (H : Γ ⊢ e : A) : ∃ e', Γ ⊢ e ⋙ e' := by
  induction e using VExpr.brecOn generalizing Γ A with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  have neut {e} (H' : Γ ⊢ e : A) (e_ih : e.below (motive := motive)) :
      NonNeutral Γ e → ∃ e', Γ ⊢ e ⋙ e' := by
    rintro (⟨A, e, a, rfl⟩ | ⟨p, r, m1, m2, h1, hp2, hp3⟩ | ⟨rule, actual, hmatch, rfl⟩)
    · have ⟨_, _, hf, ha⟩ := H'.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, he⟩ := hf.lam_inv henv hΓ
      have ⟨_, he⟩ := e_ih.1.2.2.1 (by exact ⟨hΓ, _, hA⟩) he
      have ⟨_, ha⟩ := e_ih.2.1 hΓ ha
      exact ⟨_, .beta he ha⟩
    · suffices ∃ m3 : p.Path → VExpr, ∀ a, Γ ⊢ m2 a ⋙ m3 a from
        let ⟨_, h3⟩ := this; ⟨_, .extra h1 hp2 hp3 h3⟩
      clear H r h1 hp3
      induction p generalizing e m1 A with
      | const | elim => exact ⟨nofun, nofun⟩
      | app f a ih1 ih2 =>
        let .app hm1 hm2 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih1 H1 e_ih.1.2 _ _ hm1
        have ⟨m2r, hr⟩ := ih2 H2 e_ih.2.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := H'.app_inv henv hΓ
        have ⟨m2l, hl⟩ := ih H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1 hΓ H2
        exact ⟨Option.rec e' m2l, Option.rec hs hl⟩
    · have recargs : ∀ i : Fin (rule.capture actual).length,
          ∃ out, Γ ⊢ (rule.capture actual)[i] ⋙ out := by
        intro i
        have hm := List.getElem_mem i.isLt
        obtain ⟨ty, ht⟩ := hmatch.capture_typed hm
        exact below_case_capture e_ih _ hm hΓ ht
      classical
      let args := List.ofFn fun i => (recargs i).choose
      refine ⟨_, .schema (arguments := args) hmatch (by simp [args]) ?_⟩
      intro i hi
      simpa [args] using (recargs ⟨i, hi⟩).choose_spec

  cases e with
  | bvar i => exact ⟨_, .bvar⟩
  | sort => exact ⟨_, .sort⟩
  | const n ls => exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .const hn⟩
  | elim block owner ls => exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .elim hn⟩
  | app ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hf
    have ⟨_, h2⟩ := e_ih.2.1 hΓ ha
    exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .app hn h1 h2⟩
  | proj ihMajor =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      H.proj_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1 hΓ hmajor.hasType.2
    exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .proj hn h1⟩
  | lam ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, he⟩ := H.lam_inv henv hΓ
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) he
    exact ⟨_, .lam h1 h2⟩
  | forallE ih1 ih2 =>
    have ⟨⟨_, hA⟩, _, hB⟩ := H.forallE_inv henv
    have ⟨_, h1⟩ := e_ih.1.1 hΓ hA
    have ⟨_, h2⟩ := e_ih.2.1 (by exact ⟨hΓ, _, hA⟩) hB
    exact ⟨_, .forallE h1 h2⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqF.instantiate_variables_parRed (H : VariableApplications body)
    (hc : body.ClosedN arguments.length) (hlen : arguments'.length = arguments.length)
    (hargs : ∀ i (hi : i < arguments.length) (hi' : i < arguments'.length),
      ∃ out, Γ ⊢ arguments[i] ≫ out ∧ Γ ⊢ out ≡ₚ{η} arguments'[i])
    (ht : Γ ⊢ InductiveSignature.instantiateParams body arguments : type) :
    ∃ out, Γ ⊢ InductiveSignature.instantiateParams body arguments ≫ out ∧
      Γ ⊢ out ≡ₚ{η} InductiveSignature.instantiateParams body arguments' := by
  induction H generalizing type with
  | @bvar i =>
    change i < arguments.length at hc
    rw [instantiateParams_eq_instOuter, instantiateParams_eq_instOuter,
      VExpr.instOuter_bvar arguments hc, VExpr.instOuter_bvar arguments' (by simpa [hlen] using hc)]
    simpa only [hlen] using hargs (arguments.length - 1 - i) (by change i < arguments.length at hc; omega)
      (by change i < arguments.length at hc; omega)
  | app hf ha ihf iha =>
    have ⟨_, _, hfn, harg⟩ := ht.app_inv henv hΓ
    obtain ⟨fn', hfnRed, hfnNormal⟩ := ihf hc.1 hfn
    obtain ⟨arg', hargRed, hargNormal⟩ := iha hc.2 harg
    have hfn' := hfnRed.hasType hΓ hfn
    have harg' := hargRed.hasType hΓ harg
    exact ⟨_, .app hfnRed hargRed, .appDF hfn'
      ((hfnNormal.defeq hΓ).of_l henv hΓ hfn').hasType.2
      harg' ((hargNormal.defeq hΓ).of_l henv hΓ harg').hasType.2 hfnNormal hargNormal⟩

alias NormalEq.instantiate_variables_parRed := NormalEqF.instantiate_variables_parRed


variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem CaseApplicationRelated.parRed_defeq
    (H : CaseApplicationRelated (ParRed Γ) actual actual')
    (ht : Γ ⊢ actual.expr : type) : CaseApplicationRelated (IsDefEqU env univs Γ) actual actual' := by
  obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
  refine { H with arguments := ?_, ctorArguments := ?_ }
  · exact H.arguments.and_mem.imp fun _ _ h => by
      obtain ⟨type, ht⟩ := schema_mkApps_arg_type hΓ hf h.2.1
      exact ⟨type, h.1.defeq hΓ ht⟩
  · exact H.ctorArguments.and_mem.imp fun _ _ h => by
      obtain ⟨type, ht⟩ := schema_mkApps_arg_type hΓ ha h.2.1
      exact ⟨type, h.1.defeq hΓ ht⟩

/-- A structural parallel step keeps a registered case application's fixed
heads and moves only its two argument spines. -/
theorem ParRed.case_spines (hm : CaseRedex env univs Γ rule actual)
    (hrigid : env.Rigid actual.ctorName)
    (hf : Γ ⊢ mkApps (.elim actual.block actual.owner actual.levels) actual.arguments ≫ fn')
    (ha : Γ ⊢ mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments ≫ major') :
    ∃ actual', actual'.expr = .app fn' major' ∧ CaseApplicationRelated (ParRed Γ) actual actual' := by
  have hf' := hf
  rw [hm.block_eq, hm.owner_eq] at hf'
  obtain ⟨args', hefn, hargs⟩ := ParRed.elim_prefix hm.source (Nat.le_of_eq hm.arguments_length) hf'
  obtain ⟨fields', hemajor, hfields⟩ := ha.rigid_const_spine hrigid
  refine ⟨{ actual with arguments := args', ctorArguments := fields' }, ?_,
    ⟨rfl, rfl, rfl, rfl, rfl, hargs, hfields⟩⟩
  simp only [InductiveSignature.CaseSchema.Application.expr, hefn, hemajor, hm.block_eq, hm.owner_eq]

theorem CaseRedex.ctor_rigid (H : CaseRedex env univs Γ rule actual) :
    env.Rigid actual.ctorName := by
  obtain ⟨schema, block, owner, hl, hg⟩ := H.source.generates
  rw [H.ctor_eq]
  exact henv.case_constructor_rigid hl hg

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.schema_app_triangle
    (hm : CaseRedex env univs Γ rule actual)
    (hrigid : env.Rigid actual.ctorName)
    (hlen : args.length = (rule.capture actual).length)
    (hcomplete : ∀ i (hi : i < (rule.capture actual).length),
      Γ ⊢ (rule.capture actual)[i] ⋙ args[i]'(by omega))
    (ht : Γ ⊢ actual.expr : type)
    (hf : Γ ⊢ mkApps (.elim actual.block actual.owner actual.levels) actual.arguments ≫ fn')
    (ha : Γ ⊢ mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments ≫ major')
    (hrec : ∀ i (hi : i < (rule.capture actual).length) {a b},
      (Γ ⊢ (rule.capture actual)[i] ≫ a) → (Γ ⊢ (rule.capture actual)[i] ⋙ b) →
      ∃ out, Γ ⊢ a ≫ out ∧ Γ ⊢ out ≡ₚ{η} b) :
    ∃ out, Γ ⊢ .app fn' major' ≫ out ∧ Γ ⊢ out ≡ₚ{η} rule.rhs actual.levels args := by
  obtain ⟨actual', he, hspines⟩ := ParRed.case_spines hm hrigid hf ha
  have hstruct : Γ ⊢ actual.expr ≫ actual'.expr := by rw [he]; exact .app hf ha
  have hm' := hm.congr henv hΓ (hspines.parRed_defeq hΓ ht) ⟨_, hstruct.defeq hΓ ht⟩
  have hcapture := hspines.capture (rule := rule)
  have hcaplen := hcapture.length_eq
  have recargs : ∀ i : Fin (rule.capture actual).length,
      ∃ out, Γ ⊢ (rule.capture actual')[i.val]'(by omega) ≫ out ∧
        Γ ⊢ out ≡ₚ{η} args[i.val]'(by omega) := by
    intro i
    exact hrec i.val i.isLt (case_forall₂_get hcapture i.isLt (by omega)) (hcomplete i.val i.isLt)
  classical
  let outputs := List.ofFn fun i => (recargs i).choose
  have hschema : Γ ⊢ actual'.expr ≫ rule.rhs actual'.levels outputs := by
    refine .schema hm' (by simp [outputs]; omega) ?_
    intro i hi
    have hi' : i < (rule.capture actual).length := by omega
    simpa [outputs] using (recargs ⟨i, hi'⟩).choose_spec.1
  refine ⟨_, he ▸ hschema, ?_⟩
  have hvars := hm.source.rhs_variables
  have htyped := hschema.hasType hΓ (hstruct.hasType hΓ ht)
  simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at htyped ⊢
  apply NormalEq.instantiate_variables hΓ hvars
    (by simpa [outputs] using hm.source.closed.2.1) (by simpa [outputs] using hlen) ?_ htyped
  intro i hi hi'
  have hi'' : i < (rule.capture actual).length := by simpa [outputs] using hi
  simpa [outputs] using (recargs ⟨i, hi''⟩).choose_spec.2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.triangle (H1 : Γ ⊢ e : A) (H : Γ ⊢ e ≫ e') (H2 : Γ ⊢ e ⋙ o) :
    ∃ o', Γ ⊢ e' ≫ o' ∧ Γ ⊢ o' ≡ₚ{η} o := by
  induction e using VExpr.brecOn generalizing Γ A e' o with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  induction H2 generalizing A e' with
  | @schema Γ args rule actual hm hl hargs ih =>
    generalize he : actual.expr = source at H
    cases H with
    | @schema _ args' rule' actual' hm' hl' hargs' =>
      cases case_application_injective he
      cases hm.rule_unique henv hm'
      have hvars := hm.source.rhs_variables
      have hc : rule.body.rhs.ClosedN args'.length := by simpa only [hl'] using hm.source.closed.2.1
      have hlen : args.length = args'.length := hl.trans hl'.symm
      have hargJoin : ∀ i (hi : i < args'.length) (hi' : i < args.length),
          ∃ out, Γ ⊢ args'[i] ≫ out ∧ Γ ⊢ out ≡ₚ{η} args[i] := by
        intro i hi hi'
        have hiC : i < (rule.capture actual).length := by omega
        obtain ⟨ty, ht⟩ := hm.capture_typed (List.getElem_mem hiC)
        exact below_case_capture e_ih _ (List.getElem_mem hiC) hΓ ht (hargs' i hiC) (hargs i hiC)
      have htyped := (ParRed.schema hm' hl' hargs').hasType hΓ H1
      simp only [InductiveSignature.CaseSchema.AppliedRule.rhs, hvars.instL_eq] at htyped ⊢
      exact NormalEq.instantiate_variables_parRed hΓ hvars hc hlen hargJoin htyped
    | app hf ha =>
      cases he
      apply ParRed.schema_app_triangle hΓ hm hm.ctor_rigid hl hargs H1 hf ha
      intro i hi a b hr hc
      obtain ⟨type, ht⟩ := hm.capture_typed (List.getElem_mem hi)
      exact below_case_capture e_ih _ (List.getElem_mem hi) hΓ ht hr hc
    | beta =>
      have hfn := VExpr.app.inj he |>.1
      exact False.elim (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ hfn)
    | extra hp hmatch =>
      obtain ⟨sp, rfl⟩ := pat_simple hp
      obtain ⟨name, hh⟩ := InductiveSignature.CaseSchema.recursor_pattern_head hmatch
      rw [← he, InductiveSignature.CaseSchema.Application.head] at hh
      cases hh
    | bvar | sort | const | elim | proj | lam | forallE => cases he
  | bvar =>
    cases H with
    | bvar => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | sort =>
    cases H with
    | sort => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | const hn =>
    cases H with
    | const => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
  | elim hn =>
    cases H with
    | elim => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
  | app hn _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := H1.app_inv henv hΓ
    cases H with
    | app r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2; let ⟨_, p2, n2⟩ := ih2 hΓ l2 r2 e_ih.2.2
      have o1 := p1.hasType hΓ (r1.hasType hΓ l1); have o2 := p2.hasType hΓ (r2.hasType hΓ l2)
      exact ⟨_, .app p1 p2, .appDF o1 (.defeqU_l henv hΓ (n1.defeq hΓ) o1)
        o2 (.defeqU_l henv hΓ (n2.defeq hΓ) o2) n1 n2⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
    | schema hm => cases hn (.inr (.inr ⟨_, _, hm, rfl⟩))
    | beta => cases hn (.inl ⟨_, _, _, rfl⟩)
  | proj hn _ ihMajor =>
    obtain ⟨info, levels, params, indexArgs, sourceMajor, fieldType, fieldLevel,
      hinfo, hlevels, huvars, hparams, hindices, hfield, hfieldTyping,
      hmajor, _, _⟩ := H1.proj_inv henv hΓ
    cases H with
    | proj rMajor =>
      let ⟨_, pMajor, nMajor⟩ := ihMajor hΓ hmajor.hasType.2 rMajor e_ih.2
      have targetNatural := (ParRed.proj pMajor).hasType hΓ
        ((ParRed.proj rMajor).hasType hΓ H1)
      exact ⟨_, .proj pMajor, .projDF targetNatural nMajor⟩
    | extra h1 h2 h3 => cases hn (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩))
  | lam _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.lam_inv henv hΓ
    cases H with
    | lam r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := ih2 hΓ' l2 r2 e_ih.2.2; ?_
      have := (r1.defeq hΓ l1).trans (p1.defeq hΓ (r1.hasType hΓ l1)) |>.symm
      refine ⟨_, .lam p1 ?_, .lamDF this.symm (this.symm.transU_l henv hΓ (n1.defeq hΓ)) n2⟩
      exact p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType (by exact ⟨hΓ, _, l1⟩) l2)
    | extra h1 h2 => cases h2
  | forallE _ _ ih1 ih2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := H1.forallE_inv henv
    cases H with
    | forallE r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 hΓ l1 r1 e_ih.1.2
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := ih2 hΓ' l2 r2 e_ih.2.2; ?_
      exact ⟨_, .forallE p1 (p2.defeqDFC hΓ (.succ .zero (r1.defeq hΓ l1)) (r2.hasType hΓ' l2)),
        .forallEDF (.trans (r1.defeq hΓ l1) (p1.defeq hΓ (r1.hasType hΓ l1)))
          n1 (p2.hasType hΓ' (r2.hasType hΓ' l2)) n2⟩
    | extra h1 h2 => cases h2
  | beta l1 l2 ih1 ih2 =>
    have ⟨_, _, lf, la⟩ := H1.app_inv henv hΓ
    have ⟨⟨_, lA⟩, _, le⟩ := lf.lam_inv henv hΓ
    have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lA le)).forallE_inv henv hΓ
    have la' := hw.defeq la
    obtain ⟨⟨-, ⟨-, e_ih1 : VExpr.below ..⟩, ⟨he, e_ih2 : VExpr.below ..⟩⟩,
      ⟨ha, e_ih3 : VExpr.below ..⟩⟩ := e_ih
    rcases H.app_lam_cases with ⟨_, _, rf, ra, rfl⟩ | ⟨_, _, re, ra, rfl⟩
    ·
      let ⟨_, p3, n3⟩ := ha hΓ la ra l2
      cases rf with
      | lam rA re =>
        refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := he hΓ' le re l1; ?_
        refine ⟨_, .beta (p2.defeqDFC hΓ (.succ .zero (rA.defeq hΓ lA)) (re.hasType hΓ' le)) p3, ?_⟩
        refine .trans hΓ
          (.instN_r hΓ' (p3.hasType hΓ (ra.hasType hΓ la')) n3 .zero
            (p2.hasType hΓ' (re.hasType hΓ' le)))
          (.instN (l2.toParRed.hasType hΓ la') .zero n2)
      | extra h1 h2 => cases h2
    ·
      refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := he hΓ' le re l1; ?_
      let ⟨_, p3, n3⟩ := ha hΓ la ra l2
      refine ⟨_, .instN p3 (ra.hasType hΓ la') .zero p2, ?_⟩
      refine .trans hΓ
        (.instN_r hΓ' (p3.hasType hΓ (ra.hasType hΓ la')) n3 .zero
          (p2.hasType hΓ' (re.hasType hΓ' le)))
        (.instN (l2.toParRed.hasType hΓ la') .zero n2)
  | @extra p r e m1 m2 Γ m2' l1 l2 l3 l4 ih =>
    have :
      (∃ m3 m3' : p.Path → VExpr, p.Matches e' m1 m3 ∧
        (∀ a, Γ ⊢ m2 a ≫ m3 a) ∧ (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧ (∀ a, Γ ⊢ m3' a ≡ₚ{η} m2' a)) ∨
      (∃ p₁ e₁' e₁ m1₁ m2₁, Subpattern p₁ p ∧ (p₁ = p → e₁ = e ∧ e₁' = e' ∧ m1₁ ≍ m1 ∧ m2₁ ≍ m2) ∧
        p₁.Matches e₁ m1₁ m2₁ ∧ ∃ p' r m1 m2 m2',
        Pat p' r ∧ p'.Matches e₁ m1 m2 ∧ (∀ a, Γ ⊢ m2 a ≫ m2' a) ∧ e₁' = r.1.apply m1 m2') := by
      have hnative := Params.constHeaded l1
      clear l1 l3 l4 r
      induction H generalizing p m1 A with
      | schema hm =>
        obtain ⟨name, hn⟩ := hnative.matches_head l2
        rw [InductiveSignature.CaseSchema.Application.head] at hn
        cases hn
      | const | elim =>
        cases id l2; exact .inl ⟨_, _, l2, nofun, fun _ => .rfl, nofun⟩
      | @app Γ f f' a a' hf ha ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        cases l2 with
        | var lf =>
          match ih1 lf (ih <| some ·) hΓ Hf e_ih.1.2 hnative with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.varL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.varL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            have ⟨_, a3, a4⟩ := ih none hΓ Ha ha e_ih.2.2
            exact .inl ⟨_, (·.elim _ _), .var f1,
              (·.casesOn ha f2), (·.casesOn a3 f3), (·.casesOn a4 f4)⟩
        | app lf la =>
          match ih1 lf (ih <| .inl ·) hΓ Hf e_ih.1.2 hnative.1 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.appL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.appL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            match ih2 la (ih <| .inr ·) hΓ Ha e_ih.2.2 hnative.2 with
            | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
              refine .inr ⟨_, _, _, _, _, h1.appR, ?_, h3⟩
              rintro rfl; cases h1.antisymm (.appR .refl)
            | .inl ⟨_, _, a1, a2, a3, a4⟩ =>
              exact .inl ⟨_, Sum.elim _ _, .app f1 a1,
                (·.casesOn f2 a2), (·.casesOn f3 a3), (·.casesOn f4 a4)⟩
      | beta _ _ => cases l2 with | var h | app h => cases h
      | @extra _ _ _ _ _ _ _ r1 r2 _ r4 =>
        exact .inr ⟨_, _, _, _, _, .refl, fun _ => ⟨rfl, rfl, .rfl, .rfl⟩,
          l2, _, _, _, _, _, r1, r2, r4, rfl⟩
      | _ => cases l2
    match this with
    | .inl ⟨m3, m3', h1, h2, h3, h4⟩ =>
      refine
        have h := .extra l1 h1 (l3.map fun _ _ ⟨_, h1⟩ => ?_) h3
        ⟨_, h, .apply_pat hΓ (fun a _ _ => h4 a) (h.hasType hΓ (H.hasType hΓ H1))⟩
      refine ⟨_, .trans
        (.symm <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.1)
        (.trans h1 <| .apply_pat hΓ (fun _ _ h => ⟨_, (h2 _).defeq hΓ h⟩) h1.hasType.2)⟩
    | .inr ⟨_, _, _, _, _, h1, h2, l2', _, _, _, _, m3, r1, r2, r4, e⟩ =>
      obtain ⟨_, -, -, hr, -⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, l2'⟩⟩
      obtain ⟨rfl, rfl, ⟨⟩⟩ := pat_uniq l1 r1 h1 hr
      obtain ⟨rfl, rfl, ⟨⟩, ⟨⟩⟩ := h2 rfl; subst e
      obtain ⟨rfl, rfl⟩ := l2'.uniq r2
      suffices ∃ m3' : p.Path → VExpr, (∀ a, Γ ⊢ m3 a ≫ m3' a) ∧ (∀ a, Γ ⊢ m3' a ≡ₚ{η} m2' a) by
        let ⟨m3', h3, h4⟩ := this
        refine ⟨_, ?h3, .apply_pat hΓ (fun a _ _ => h4 a) ((?h3).hasType hΓ (H.hasType hΓ H1))⟩
        exact .apply_pat _ h3
      clear H r l1 l2 l3 l4 this h1 h2 r1 r2 hr
      induction l2' generalizing A with
      | const | elim => exact ⟨nofun, nofun, nofun⟩
      | app _ _ ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| .inl ·) _ Hf e_ih1 (r4 <| .inl ·)
        have ⟨g2, r1, r2⟩ := ih2 (ih <| .inr ·) _ Ha e_ih2 (r4 <| .inr ·)
        exact ⟨Sum.elim g1 g2, (·.casesOn l1 r1), (·.casesOn l2 r2)⟩
      | var _ ih1 =>
        have ⟨_, _, Hf, Ha⟩ := H1.app_inv henv hΓ
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| some ·) _ Hf e_ih1 (r4 <| some ·)
        have ⟨g2, r1, r2⟩ := ih none hΓ Ha (r4 none) e_ih2
        exact ⟨(·.elim g2 g1), (·.casesOn r1 l1), (·.casesOn r2 l2)⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRed.church_rosser (H : Γ ⊢ e : A)
    (H1 : Γ ⊢ e ≫ e₁) (H2 : Γ ⊢ e ≫ e₂) :
      ∃ e₁' e₂', Γ ⊢ e₁ ≫ e₁' ∧ Γ ⊢ e₂ ≫ e₂' ∧ Γ ⊢ e₁' ≡ₚ{η} e₂' := by
  let ⟨e', h'⟩ := CParRed.exists hΓ H
  let ⟨_, l1, l2⟩ := H1.triangle (η := η) hΓ H h'
  let ⟨_, r1, r2⟩ := H2.triangle (η := η) hΓ H h'
  exact ⟨_, _, l1, r1, l2.trans hΓ (r2.symm hΓ)⟩

def ParRedS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRed Γ)
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.hasType (H : Γ ⊢ e ≫* e') : Γ ⊢ e : A → Γ ⊢ e' : A := by
  induction H with
  | rfl => exact id
  | tail h1 h2 ih => exact h2.hasType hΓ ∘ ih

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.defeq (H : Γ ⊢ e ≫* e') (h : Γ ⊢ e : A) : Γ ⊢ e ≡ e' : A := by
  induction H with
  | rfl => exact h
  | tail h1 h2 ih => exact ih.trans (h2.defeq hΓ (hasType hΓ h1 h))

variable! (hΓ : OnCtx Γ₀ (IsType env univs)) in
theorem ParRedS.defeqDFC (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (h : Γ₁ ⊢ e1 : A) (H : Γ₁ ⊢ e1 ≫* e2) : Γ₂ ⊢ e1 ≫* e2 := by
  induction H with
  | rfl => exact .rfl
  | tail h1 h2 ih => refine .tail ih (h2.defeqDFC hΓ W (hasType (W.isType' hΓ) h1 h))

theorem ParRedS.app (hf : Γ ⊢ f ≫* f') (ha : Γ ⊢ a ≫* a') :
    Γ ⊢ f.app a ≫* f'.app a' := by
  have : Γ ⊢ f.app a ≫* f.app a' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.app .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.app f2 .rfl)

theorem ParRedS.proj (hmajor : Γ ⊢ major ≫* major') :
    Γ ⊢ VExpr.proj typeName index major ≫*
      VExpr.proj typeName index major' := by
  induction hmajor with
  | rfl => exact .rfl
  | tail h1 h2 ih => exact .tail ih (.proj h2)

theorem ParRedS.lam (hf : Γ ⊢ A ≫* A') (ha : A::Γ ⊢ body ≫* body') :
    Γ ⊢ A.lam body ≫* A'.lam body' := by
  have : Γ ⊢ A.lam body ≫* A.lam body' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.lam .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.lam f2 .rfl)

theorem ParRedS.forallE (hf : Γ ⊢ A ≫* A') (ha : A::Γ ⊢ body ≫* body') :
    Γ ⊢ A.forallE body ≫* A'.forallE body' := by
  have : Γ ⊢ A.forallE body ≫* A.forallE body' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.forallE .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.forallE f2 .rfl)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedS.inst (Ha : Γ ⊢ a : A)
    (hf : A :: Γ ⊢ f ≫* f') (ha : Γ ⊢ a ≫* a') : Γ ⊢ f.inst a ≫* f'.inst a' := by
  have : Γ ⊢ f.inst a ≫* f.inst a' := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.instN a2 (ParRedS.hasType hΓ a1 Ha) .zero .rfl)
  replace Ha := ha.hasType hΓ Ha
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail _ h ihf => exact .tail ihf (.instN .rfl Ha .zero h)

theorem ParRedS.weakN (W : Ctx.LiftN n k Γ Γ') (H : Γ ⊢ e ≫* e') :
    Γ' ⊢ e.liftN n k ≫* e'.liftN n k := by
  induction H with
  | rfl =>  exact .rfl
  | tail _ h ih => exact .tail ih (.weakN W h)

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqF.mkApps_spine
    (hfn : Γ ⊢ fn ≡ₚ{η} fn') (hargs : List.Forall₂ (NormalEqF η Γ) args args')
    (ht : Γ ⊢ mkApps fn args : type) : Γ ⊢ mkApps fn args ≡ₚ{η} mkApps fn' args' := by
  induction hargs generalizing fn fn' with
  | nil => exact hfn
  | cons harg hargs ih =>
    obtain ⟨_, happ⟩ := schema_mkApps_head_type hΓ (fn := .app fn _) ht
    obtain ⟨_, _, hfnType, hargType⟩ := happ.app_inv henv hΓ
    apply ih _ ht
    exact .appDF hfnType ((hfn.defeq hΓ).of_l henv hΓ hfnType).hasType.2
      hargType ((harg.defeq hΓ).of_l henv hΓ hargType).hasType.2 hfn harg

alias NormalEq.mkApps_spine := NormalEqF.mkApps_spine

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseApplicationRelated.normalEq
    (H : CaseApplicationRelated (NormalEqF η Γ) actual actual')
    (ht : Γ ⊢ actual.expr : type) : Γ ⊢ actual.expr ≡ₚ{η} actual'.expr := by
  obtain ⟨_, _, hfn, hmajor⟩ := ht.app_inv henv hΓ
  obtain ⟨_, hhead⟩ := schema_mkApps_head_type hΓ hfn
  obtain ⟨_, hctor⟩ := schema_mkApps_head_type hΓ hmajor
  have hnfn := NormalEqF.mkApps_spine hΓ (.refl hhead) H.arguments hfn
  have hnmajor := NormalEqF.mkApps_spine hΓ (.refl hctor) H.ctorArguments hmajor
  change NormalEqF η Γ (.app _ _) (.app _ _)
  rw [← H.block_eq, ← H.owner_eq, ← H.levels_eq, ← H.ctor_eq, ← H.ctorLevels_eq]
  apply NormalEqF.appDF hfn ?_ hmajor ?_ hnfn hnmajor
  · exact ((hnfn.defeq hΓ).of_l henv hΓ hfn).hasType.2
  · exact ((hnmajor.defeq hΓ).of_l henv hΓ hmajor).hasType.2

private theorem normalEq_forall2_symm (hΓ : OnCtx Γ (env.IsType univs)) (H : List.Forall₂ (NormalEqF η Γ) args args') :
    List.Forall₂ (NormalEqF η Γ) args' args := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.symm hΓ) ih

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseApplicationRelated.normalEq_symm
    (H : CaseApplicationRelated (NormalEqF η Γ) actual actual') :
    CaseApplicationRelated (NormalEqF η Γ) actual' actual where
  block_eq := H.block_eq.symm
  owner_eq := H.owner_eq.symm
  levels_eq := H.levels_eq.symm
  ctor_eq := H.ctor_eq.symm
  ctorLevels_eq := H.ctorLevels_eq.symm
  arguments := normalEq_forall2_symm hΓ H.arguments
  ctorArguments := normalEq_forall2_symm hΓ H.ctorArguments

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseApplicationRelated.normalEq_defeq
    (H : CaseApplicationRelated (NormalEqF η Γ) actual actual') :
    CaseApplicationRelated (IsDefEqU env univs Γ) actual actual' where
  block_eq := H.block_eq
  owner_eq := H.owner_eq
  levels_eq := H.levels_eq
  ctor_eq := H.ctor_eq
  ctorLevels_eq := H.ctorLevels_eq
  arguments := H.arguments.imp fun _ _ h => h.defeq hΓ
  ctorArguments := H.ctorArguments.imp fun _ _ h => h.defeq hΓ

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem CaseRedex.of_normalEq_spine
    (H : CaseRedex env univs Γ rule actual')
    (hspine : CaseApplicationRelated (NormalEqF η Γ) actual actual') :
    CaseRedex env univs Γ rule actual := by
  obtain ⟨_, hactual⟩ := H.guard
  have hs := hspine.normalEq_symm hΓ
  exact H.congr henv hΓ (hs.normalEq_defeq hΓ)
    ((hs.normalEq hΓ hactual.hasType.1).defeq hΓ)

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEqF.of_levelEquiv (L : VExpr.LEquiv univs e e') (ht : Γ ⊢ e : type) :
    Γ ⊢ e ≡ₚ{η} e' := by
  induction L generalizing Γ type with
  | refl => exact .refl ht
  | sort he hw => exact .sortDF (ht.sort_inv henv.ordered) hw he
  | const he hw =>
    obtain ⟨ci, hc, hu, hn⟩ := ht.const_inv henv.ordered hΓ
    exact .constDF hc hu hw hn he
  | elim he hw =>
    exact .elimDF ((VExpr.LEquiv.defeq henv hΓ (.elim he hw) ⟨_, ht⟩).of_l henv hΓ ht) he
  | app hf ha ihf iha =>
    obtain ⟨_, _, hft, hat⟩ := ht.app_inv henv.ordered hΓ
    have hnf := ihf hΓ hft
    have hna := iha hΓ hat
    exact .appDF hft ((hnf.defeq hΓ).of_l henv hΓ hft).hasType.2
      hat ((hna.defeq hΓ).of_l henv hΓ hat).hasType.2 hnf hna
  | proj hm ihm =>
    obtain ⟨info, ls, params, indices, major, field, level, hi, hlu, hun, hp, hix, hf,
      hfield, hmajor, hclosed, hguard⟩ := ht.proj_inv henv.ordered hΓ
    exact .projDF ht (ihm hΓ hmajor.hasType.2)
  | lam hd hb ihd ihb =>
    obtain ⟨⟨_, hdomain⟩, _, hbody⟩ := ht.lam_inv henv.ordered hΓ
    have hctx : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hdomain⟩
    exact .lamDF hdomain ((ihd hΓ hdomain).defeq hΓ |>.of_l henv hΓ hdomain)
      (ihb hctx hbody)
  | forallE hd hb ihd ihb =>
    obtain ⟨⟨_, hdomain⟩, _, hbody⟩ := ht.forallE_inv henv.ordered
    have hctx : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hdomain⟩
    exact .forallEDF hdomain (ihd hΓ hdomain) hbody (ihb hctx hbody)

alias NormalEq.of_levelEquiv := NormalEqF.of_levelEquiv

theorem _root_.Lean4Lean.Pattern.RHS.const_levelEquiv
    (r : (Pattern.const name).RHS) (hls : ∀ l ∈ ls, l.WF univs)
    (hls' : ∀ l ∈ ls', l.WF univs) (he : List.Forall₂ (· ≈ ·) ls ls') :
    VExpr.LEquiv univs (r.apply ls values) (r.apply ls' values') := by
  induction r with
  | fixed c hc => exact .instL_expr c hls hls' he
  | app _ _ ihf iha => exact .app ihf iha
  | var i => cases i

theorem _root_.Lean4Lean.Pattern.Check.const_levels
    (hΓ : OnCtx Γ (env.IsType univs))
    {check : (Pattern.const name).Check}
    (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls')
    (H : check.OK (IsDefEqU env univs Γ) ls values) :
    check.OK (IsDefEqU env univs Γ) ls' values' := by
  induction check with
  | true => trivial
  | nonzero level rest ih =>
    refine ⟨fun hz => H.1 ((VLevel.inst_congr rfl he).trans hz), ih H.2⟩
  | defeq left right rest ih =>
    obtain ⟨ht, hr⟩ := H
    obtain ⟨type, ht⟩ := ht
    have hl := NormalEq.of_levelEquiv (η := true) hΓ (left.const_levelEquiv (values' := values') hls hls' he) ht.hasType.1
    have hh := NormalEq.of_levelEquiv (η := true) hΓ (right.const_levelEquiv (values' := values') hls hls' he) ht.hasType.2
    exact ⟨(hl.defeq hΓ).symm.trans henv hΓ (IsDefEqU.trans henv hΓ ⟨_, ht⟩ (hh.defeq hΓ)), ih hr⟩

variable! (hΓ : OnCtx Γ (env.IsType univs)) in
theorem NormalEq.const_stored_parallel
    (hc : env.constants name = some ci)
    (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (hlen : ls.length = ci.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    {p : Pattern} {r : p.RHS × p.Check} {levels : List VLevel}
    {values : p.Path → VExpr}
    (hp : Pat p r) (hm : p.Matches (.const name ls') levels values)
    (hcheck : r.2.OK (IsDefEqU env univs Γ) levels values)
    {values' : p.Path → VExpr} (hargs : ∀ a, Γ ⊢ values a ≫ values' a) :
    ∃ out, Γ ⊢ .const name ls ≫* out ∧ Γ ⊢ out ≡ₚ r.1.apply levels values' := by
  cases hm
  let zeroArgs : (Pattern.const name).Path → VExpr := nofun
  have hcheckLeft := Pattern.Check.const_levels hΓ hls' hls
    (he.flip.imp fun _ _ h => h.symm) hcheck (values' := zeroArgs)
  have hrLeft : Γ ⊢ .const name ls ≫ r.1.apply ls zeroArgs :=
    .extra hp .const hcheckLeft (fun a => nomatch a)
  have ht : Γ ⊢ .const name ls : ci.type.instL ls := .const hc hls hlen
  exact ⟨_, .tail .rfl hrLeft,
    NormalEq.of_levelEquiv hΓ (r.1.const_levelEquiv hls hls' he) (hrLeft.hasType hΓ ht)⟩
