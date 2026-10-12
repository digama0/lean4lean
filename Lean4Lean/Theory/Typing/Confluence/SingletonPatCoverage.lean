import Lean4Lean.Theory.Typing.Confluence.SingletonEquation
import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.Confluence.StageJoins

/-! # Coverage of a registered ι rule at a `Prop` source

A registered ι rule of a large-eliminating singleton recursor fires (`IsDefEq.pat`, check
`.true`) at instances whose major's source sort is `Prop`. The confluence engine's pattern of the
rule is guarded there (`RecursorData.guard`), and the singleton prefix unfolding computes
instead. Its coverage (`VEnv.WF.singletonPatCoverageJ`) chains three joins:

1. the instance `rec A (c B)` joins the β-redex of the rule's generic equation at the
   recursor's parameters, motives and minors and the major's fields
   (`singletonInstance_alignJ`, from the joinable typing of the instance and the joins of the
   constructor's normalization at the stage the declaration was installed at);
2. the generic equation joins at a `Prop` source by the prefix unfolding
   (`RecursorRegistered.zero_join`), here applied to
   the equation's registered rule (`RecursorRegistered.patEquation_of_empty`);
3. the right side of the generic equation applied to those arguments is the rule's reduct. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

section
variable [Params]
open Params

theorem FullCRDefEq.mkApps_fn (hΓ : OnCtx Γ (env.IsType univs))
    {f f' f₁ f₁' : VExpr} (hf : FullReduction Γ f f₁) (hf' : FullReduction Γ f' f₁')
    (hn : NormalEq Γ f₁ f₁') (hdef : env.IsDefEqU univs Γ f f') :
    ∀ {args : List VExpr} {T : VExpr}, env.HasType univs Γ (VExpr.mkApps f args) T →
      FullCRDefEq Γ (VExpr.mkApps f args) (VExpr.mkApps f' args) := by
  intro args
  induction args generalizing f f' f₁ f₁' with
  | nil =>
    intro T ht
    obtain ⟨_, hd⟩ := hdef
    exact ⟨⟨_, ht⟩, ⟨_, hd.hasType.2⟩, _, _, hf, hf', hn⟩
  | cons a as ih =>
    intro T ht
    obtain ⟨_, hfa⟩ := HasType.mkApps_head henv.orderedStrong hΓ (as := as) (f := .app f a) ht
    obtain ⟨A, B, hft, hat⟩ := hfa.app_inv henv.orderedStrong hΓ
    obtain ⟨C, hd⟩ := hdef
    have hf't : env.HasType univs Γ f' (.forallE A B) :=
      (hd.hasType.1.uniqU henv hΓ hft).defeqDF henv hΓ hd |>.hasType.2
    have hf₁t := hf.hasType hΓ hft
    have hf₁'t := hf'.hasType hΓ hf't
    refine ih (f := .app f a) (f' := .app f' a) (f₁ := .app f₁ a) (f₁' := .app f₁' a)
      (hf.app .rfl) (hf'.app .rfl) (.appDF hf₁t hf₁'t hat hat hn (.refl hat))
      ⟨_, .appDF ((hd.hasType.1.uniqU henv hΓ hft).defeqDF henv hΓ hd) hat⟩ ht


end

variable {env : VEnv}

theorem WF.singletonPatCoverageJ (henv : env.WF) (U : Nat) (heq : env.HasCanonicalEq) :
    letI := henv.params U
    ∀ {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 : List VLevel}
      {m2 : p.Path → VExpr} {data : RecursorData},
      OnCtx Γ (env.IsType U) → env.pats p r → env.recursorRegistry p.headConst = some data →
      data.largeTarget = true → (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero →
      p.Matches e m1 m2 → env.IsDefEq U Γ e (r.1.apply m1 m2) A → HasTypeJ Γ e A →
      (∀ {decl env₀ env₁ rec}, RecursorRegisteredAt env data decl env₀ env₁ → env₀ ∈ env.stages →
        rec ∈ decl.recs → rec.name = p.headConst → ∀ {base E : VEnv}, base ≤ env₀ → base.addConstVals decl.typeConstants = some E →
        ∀ {A B : VExpr}, E.IsDefEqU decl.uvars [] A B → ∀ {Γ' : List VExpr} {cls : List VLevel},
          OnCtx Γ' (env.IsType U) → (∀ l ∈ cls, l.WF U) → cls.length = decl.uvars →
          FullCRDefEq Γ' (A.instL cls) (B.instL cls)) →
      ∃ left right, FullReduction Γ e left ∧ FullReduction Γ (r.1.apply m1 m2) right ∧
        NormalEq Γ left right := by
  letI := henv.params U
  intro Γ p r t T m1 m2 data hΓ hp hreg hlarge hzero hm hred hJ hNJ
  have ht := hred.hasType.1
  have hentry := recursorRegistry_entry hreg
  obtain ⟨decl, env₀, env₁, rec, hAt, hstage, hrec, hrname, hdname, -, covers⟩ := hentry
  obtain ⟨index, equation, ru, howner, hgen, hru, hof, hc, e, he⟩ := covers p r hp rfl
  subst e
  have he' : r = _ := he
  subst he'
  obtain ⟨recArgs, ctorArgs, lsC, h1, h2, rfl, happly⟩ :=
    SimplePattern.iotaRHS_apply_of_matches (k := rec.numParams + rec.numMotives + rec.numMinors)
      (nind := rec.numIndices) (cnp := ru.ctorParams) (nf := ru.nfields) (rhs := ru.rhs)
      (hc := hc) hm
  have H := hAt.registered
  have hmo : data.majorOffset = rec.getMajorIdx :=
    henv.recursorEntry_majorOffset hp
      (by simpa [SimplePattern.iota_headConst] using recursorRegistry_entry hreg)
  have hdn : data.name = rec.name := hdname.trans (by simp [SimplePattern.iota_headConst])
  have ht' : env.HasType U Γ (.app (VExpr.mkApps (.const data.name m1) recArgs)
      (VExpr.mkApps (.const ru.ctor lsC) ctorArgs)) T := by
    rw [hdn]; simpa [VExpr.mkApps_append] using ht
  obtain ⟨hw, hlen, -⟩ := RecursorRegistered.major_type henv hΓ H ht' (h1.trans hmo.symm)
  have F := RecursorData.singletonSignature H hlarge (packed := m1) hzero
  have hpe := H.patEquation_of_empty henv F.restoration hgen
  obtain ⟨hlT, hrT⟩ := H.equation_typed hgen
  have hl : m1.length = equation.uvars := hlen.trans (H.equation_uvars' hgen).symm
  have hlookup : Params.recursorData data.name = some data := by
    show env.recursorRegistry data.name = some data
    rw [hdn]; simpa [SimplePattern.iota_headConst] using hreg
  obtain ⟨L, R, hL, hR, hn⟩ := H.zero_join heq hΓ hlookup howner hgen hpe hlT hrT hw hl hlarge
    hzero
  have hlΓ : env.HasType U Γ (equation.lhs.instL m1) (equation.type.instL m1) :=
    (by simpa using hlT.instL hw : env.HasType U [] _ _).weak0 henv.ordered
  have hrΓ : env.HasType U Γ (equation.rhs.instL m1) (equation.type.instL m1) :=
    (by simpa using hrT.instL hw : env.HasType U [] _ _).weak0 henv.ordered
  have hdef : env.IsDefEqU U Γ (equation.lhs.instL m1) (equation.rhs.instL m1) := by
    exact IsDefEqU.trans henv hΓ (IsDefEqU.trans henv hΓ ⟨_, hL.defeq hΓ hlΓ⟩ (hn.defeq hΓ))
      ⟨_, (hR.defeq hΓ hrΓ).symm⟩
  have hrhs : (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply m1 m2 =
      VExpr.mkApps (equation.rhs.instL m1)
        (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
          ctorArgs.drop ru.ctorParams) := by
    rw [hof.1]; exact happly
  -- the β-redex of the generic equation is typed: the reduct is, and the sides are equal
  have hrT' := hred.hasType.2
  rw [hrhs] at hrT'
  have hargs : List.Forall₂ (IsDefEqU env U Γ)
      (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
        ctorArgs.drop ru.ctorParams)
      (recArgs.take (rec.numParams + rec.numMotives + rec.numMinors) ++
        ctorArgs.drop ru.ctorParams) := by
    refine Lean4Lean.List.Forall₂.rfl fun a ha => ?_
    obtain ⟨_, h⟩ := mkApps_arg_type hΓ hrT' ha
    exact ⟨_, h⟩
  obtain ⟨_, hβd⟩ := IsDefEqU.mkApps_args hΓ hdef.symm hargs hrT'
  have hβT := hβd.hasType.2
  have halign := singletonInstance_alignJ hΓ hAt hdn.symm hrec hru hgen hof hlarge hzero h1 h2 ht
    hJ hβT (hNJ hAt hstage hrec (by rw [SimplePattern.iota_headConst]))
  have hj2 := FullCRDefEq.mkApps_fn hΓ hL hR hn hdef hβT
  obtain ⟨-, -, l, r', h1', h2', h3'⟩ := FullCRDefEq.trans hΓ halign hj2
  exact ⟨l, r', h1', hrhs ▸ h2', h3'⟩

end Lean4Lean.VEnv
