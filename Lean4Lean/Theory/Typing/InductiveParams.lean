import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.PatsIota

namespace Lean4Lean
namespace VEnv

open VExpr

/-!
# A concrete `Params` instance from `env.pats`

`VEnv.toParams` instantiates `ChurchRosser`'s abstract pattern-reduction relation
`Params.Pat` with the environment's own registered ι rules `env.pats`. Its engine is the
population invariant `VEnv.PatsIota`: every registered pattern is a `SimplePattern.iota`
redex whose recursor head is a registered `RecHeaded` constant of a spine arity fixed by
the recursor name, whose constructor is a registered `CtorHeaded` constant, and whose
reduct is determined by the pattern. The invariant comes from `VInductDecl.WF` and the
stage lemmas of `addInduct`, and discharges every `Params` side condition except
`extra_pat`, which `toParams` takes as the hypothesis `VEnv.DefEqsAsPats`.
-/

/-! ### Combinatorics of ι redexes -/

/-- The only application subpattern of an ι redex is its top-level one: the recursor
spine applied to the constructor spine. -/
theorem app_subpattern_iota' {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m ∧ b = (Pattern.const c).varN n := by
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | appL h => exact absurd h Pattern.not_app_subpattern_varN_const
  | appR h => exact absurd h Pattern.not_app_subpattern_varN_const

/-- The only application subpattern of an ι redex is its top-level one, whose left
factor is the recursor spine. -/
theorem app_subpattern_iota {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m :=
  (app_subpattern_iota' hs).1

/-- An application pattern does not intersect a constant. -/
theorem _root_.Lean4Lean.Pattern.inter_app_const {f a : Pattern} {c : Name} :
    (Pattern.app f a).inter (.const c) = none := by
  simp [Pattern.inter]

/-- An application pattern intersects a variable pattern only through its function
part. -/
theorem _root_.Lean4Lean.Pattern.inter_app_var {f a f' q : Pattern}
    (h : (Pattern.app f a).inter (.var f') = some q) :
    ∃ g, f.inter f' = some g ∧ q = .app g a := by
  cases hf : f.inter f' with
  | none => simp [Pattern.inter, hf] at h
  | some g => simp [Pattern.inter, hf] at h; exact ⟨g, rfl, h.symm⟩

/-- Two application patterns intersect componentwise. -/
theorem _root_.Lean4Lean.Pattern.inter_app_app {f a f' a' q : Pattern}
    (h : (Pattern.app f a).inter (.app f' a') = some q) :
    ∃ g b, f.inter f' = some g ∧ a.inter a' = some b ∧ q = .app g b := by
  cases hf : f.inter f' with
  | none => simp [Pattern.inter, hf] at h
  | some g =>
    cases ha : a.inter a' with
    | none => simp [Pattern.inter, hf, ha] at h
    | some b => simp [Pattern.inter, hf, ha] at h; exact ⟨g, b, rfl, rfl, h.symm⟩

/-! ### The discharged `Params` side conditions -/

/-- `Params.pat_simple` for `env.pats`: every registered pattern is a `SimplePattern`. -/
theorem WF.pat_simple {env : VEnv} (H : env.WF) {p rr} (hp : env.pats p rr) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  obtain ⟨recN, M, ctorN, N, _, hform, _⟩ := H.patsIota.shape hp
  exact ⟨.iota recN M ctorN N, hform⟩

/-- `Params.pat_uniq` for `env.pats`: if a subpattern `p₃` of a registered redex `p₁`
intersects a registered redex `p₂`, then `p₁ = p₂ = p₃` and the reducts agree. The
intersection forces the recursor spines to agree: at the top (`refl`) both spines
match and `functional` closes; inside the recursor spine (`appL`) the arity would drop
below `arity`; inside the constructor spine (`appR`) a recursor would be a
constructor (`rec_ne_ctor`). -/
theorem WF.pat_uniq {env : VEnv} (H : env.WF) {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (h1 : env.pats p₁ r) (h2 : env.pats p₂ r') (hs : Subpattern p₃ p₁)
    (hi : p₂.inter p₃ = some p₄) : p₁ = p₂ ∧ p₂ = p₃ ∧ HEq r r' := by
  have HI := H.patsIota
  obtain ⟨R₁, M₁, C₁, N₁, c₁, rfl, -, -⟩ := HI.shape h1
  obtain ⟨R₂, M₂, C₂, N₂, c₂, rfl, -, -⟩ := HI.shape h2
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl =>
    simp only [SimplePattern.toPattern] at hi
    obtain ⟨g, b, hg, hb, -⟩ := Pattern.inter_app_app hi
    obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hg
    obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hb
    exact ⟨rfl, rfl, heq_of_eq (HI.functional h1 h2)⟩
  | appL hs' =>
    obtain ⟨i, hi', rfl⟩ := Pattern.subpattern_varN_const hs'
    cases i with
    | zero => simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter_app_const] at hi
    | succ i =>
      simp only [SimplePattern.toPattern, Pattern.varN] at hi
      obtain ⟨g, hg, -⟩ := Pattern.inter_app_var hi
      obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hg
      have := HI.arity h1 h2
      omega
  | appR hs' =>
    obtain ⟨i, hi', rfl⟩ := Pattern.subpattern_varN_const hs'
    cases i with
    | zero => simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter_app_const] at hi
    | succ i =>
      simp only [SimplePattern.toPattern, Pattern.varN] at hi
      obtain ⟨g, hg, -⟩ := Pattern.inter_app_var hi
      obtain ⟨rfl, -, -⟩ := Pattern.varN_const_inter hg
      exact absurd rfl (HI.rec_ne_ctor h2 h1)

/-- `Params.pat_app_l` for `env.pats`: the left factor of an ι redex's application
subpattern (the recursor spine) has no application subpattern of its own. -/
theorem WF.pat_app_l {env : VEnv} (H : env.WF) {p p₁ p₂ p₃ p₄ rr} (hp : env.pats p rr)
    (hs : Subpattern (.app p₁ p₂) p) : ¬ Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨recN, M, ctorN, N, _, rfl, _⟩ := H.patsIota.shape hp
  rw [app_subpattern_iota hs]
  exact Pattern.not_app_subpattern_varN_const

/-- `Params.pat_app_l_uniq` for `env.pats`: a variable-argument slot of one ι redex's
recursor spine never intersects another ι redex's recursor spine, since the recursor
name fixes the spine arity (`PatsIota.arity`). -/
theorem WF.pat_app_l_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (hv : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  have HI := H.patsIota
  obtain ⟨recN, M, ctorN, N, c, rfl, hc⟩ := HI.shape hp
  obtain ⟨recN', M', ctorN', N', c', rfl, hc'⟩ := HI.shape hp'
  have e1 : p₁ = (Pattern.const recN).varN M := app_subpattern_iota hs
  have e1' : p₁' = (Pattern.const recN').varN M' := app_subpattern_iota hs'
  subst e1 e1'
  obtain ⟨k, hk, hkk⟩ := Pattern.subpattern_varN_const hv
  cases k with
  | zero => simp [Pattern.varN] at hkk
  | succ i =>
    simp only [Pattern.varN] at hkk
    injection hkk with hkk; subst hkk
    cases hinter : ((Pattern.const recN').varN M').inter ((Pattern.const recN).varN i) with
    | none => rfl
    | some r₄ =>
      exfalso
      obtain ⟨hrr, hMi, _⟩ := Pattern.varN_const_inter hinter
      subst hrr
      have hMM : M = M' := HI.arity hp hp'
      omega

/-- `Params.pat_app_uniq` for `env.pats`: a subpattern of one ι redex's recursor spine
never intersects a subpattern of another ι redex's constructor spine, since a recursor
is never a constructor (`PatsIota.rec_ne_ctor`). -/
theorem WF.pat_app_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃ p₃'}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (h3 : Subpattern p₃ p₁) (h3' : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  have HI := H.patsIota
  obtain ⟨R, M, C, N, c, rfl, -, -⟩ := HI.shape hp
  obtain ⟨R', M', C', N', c', rfl, -, -⟩ := HI.shape hp'
  obtain ⟨rfl, -⟩ := app_subpattern_iota' hs
  obtain ⟨-, rfl⟩ := app_subpattern_iota' hs'
  obtain ⟨i, -, rfl⟩ := Pattern.subpattern_varN_const h3
  obtain ⟨j, -, rfl⟩ := Pattern.subpattern_varN_const h3'
  cases hinter : ((Pattern.const R).varN i).inter ((Pattern.const C').varN j) with
  | none => rfl
  | some q =>
    obtain ⟨rfl, -, -⟩ := Pattern.varN_const_inter hinter
    exact absurd rfl (HI.rec_ne_ctor hp hp')

/-- Every registered definitional equation is realised by a registered pattern: the
content of `Params.extra_pat`, stated verbatim for `env.pats` (in particular the level
bound `uvars` of the instantiating levels is arbitrary there, as in the class field).

This is a **design hypothesis** of `toParams`, inherited from `Params`, not a deferred proof.
`ChurchRosser`'s `Params` reads every `defeqs` entry as realised by a `Pat` rule, while in
this model the δ rules of definitions (`VDecl.WF.def`/`mutualDef`) and the quotient rule
(`VDecl.WF.quot`) are definitional axioms in `defeqs` and are not registered as `pats`:
`pats` holds the ι rules, whose reducts have the computational shape `VEnv.PatWF` asks of a
reduction rule, whereas a δ reduct is the definition's closed body, of arbitrary shape, and
the quotient rule's redex `Quot.lift f h (Quot.mk r a)` is written under binders that no
`SimplePattern` matches (`SimplePattern.defn` is unused). `DefEqsAsPats` therefore holds of
an environment built from axioms and inductives only and fails for any environment containing
a `def` or `quot`; `toParams` is a `Params` instance exactly for the environments that satisfy
it; discharging `extra_pat` for the δ and quotient rules is the remaining gap between
`Params` and `VDecl.WF`.

`DefEqsAsPats.of_no_defeqs` gives the vacuous case, and `inductParams` the resulting
instance for an environment consisting of one inductive block. -/
def DefEqsAsPats (env : VEnv) (U : Nat) : Prop :=
  ∀ {df : VDefEq} {ls : List VLevel} {uvars : Nat} {Γ : List VExpr},
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    ∃ (p : Pattern) (r : p.RHS × p.Check) (m1 : List VLevel) (m2 : p.Path → VExpr),
      env.pats p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧
      r.2.OK (env.IsDefEqU U Γ) m1 m2 ∧ df.rhs.instL ls = r.1.apply m1 m2

/-- The `Params` structure induced by a well-formed environment `env`, taking the
abstract reduction relation `Pat` to be `env.pats`. Five side conditions are
discharged from `VEnv.PatsIota`; `pat_wf` is `IsDefEq.pat` (recovering a `Realizes`
witness from `Check.OK`); `pat_env` is the identity; `extra_pat` is the design hypothesis
`hδ : env.DefEqsAsPats U` (see `DefEqsAsPats`). `inductParams` instantiates it, and
`IsDefEq.crDefEq_of_induct` runs Church–Rosser through the result. -/
@[reducible] def toParams (env : VEnv) (henv : env.WF) (U : Nat) (hδ : env.DefEqsAsPats U)
    (hproj : ∀ n info, ¬ env.projections n info) : Params where
  env := env
  henv := henv
  univs := U
  Pat := env.pats
  pat_simple := fun hp => henv.pat_simple hp
  pat_uniq := fun h1 h2 hs hi => henv.pat_uniq h1 h2 hs hi
  pat_wf := fun {_ _ _ _ _ Γ A} hpat hmatch hty hok =>
    let ⟨_, hr, hall⟩ := hok.exists_realizer (rel := fun a b t => IsDefEq env U Γ a b t)
    ⟨A, IsDefEq.pat hpat hmatch hty hr hall⟩
  pat_app_l := fun hp hs => henv.pat_app_l hp hs
  pat_app_l_uniq := fun hp hp' hs hs' hv => henv.pat_app_l_uniq hp hp' hs hs' hv
  pat_app_uniq := fun hp hp' hs hs' h3 h3' => henv.pat_app_uniq hp hp' hs hs' h3 h3'
  extra_pat := fun h1 h2 h3 => hδ h1 h2 h3
  pat_env := id
  no_projections := hproj

/-! ### An environment the instance applies to -/

/-- An environment with no definitional axiom satisfies `DefEqsAsPats` vacuously. -/
theorem DefEqsAsPats.of_no_defeqs {env : VEnv} {U : Nat} (h : ∀ df, ¬ env.defeqs df) :
    env.DefEqsAsPats U := fun hdf _ _ => absurd hdf (h _)

/-- The `Params` instance for an environment consisting of a single well-formed inductive
block without structures (`hp`: no projection entries, i.e. no family with exactly one
constructor): `addInduct` registers ι rules and no definitional axiom (`addInduct_defeqs`), so
`DefEqsAsPats` holds vacuously, and no projection, so `no_projections` holds, and `toParams`
applies. -/
@[reducible] def inductParams {decl : VInductDecl} {env : VEnv} (hdecl : decl.WF ∅)
    (h : VEnv.addInduct ∅ decl = some env) (hp : decl.projectionEntries = []) (U : Nat) :
    Params :=
  env.toParams ⟨[.induct decl], .decl (.induct hdecl h) .empty⟩ U
    (DefEqsAsPats.of_no_defeqs fun _ hdf => by rw [addInduct_defeqs h] at hdf; exact hdf)
    fun n info hi => by
      rcases (addInduct_projections_iff h).1 hi with ⟨entry, he, -⟩ | h0
      · rw [hp] at he; cases he
      · exact h0.elim

/-- Church–Rosser for such an environment: definitionally equal terms have parallel
reduction sequences meeting at `NormalEq` terms. -/
theorem IsDefEq.crDefEq_of_induct {decl : VInductDecl} {env : VEnv} (hdecl : decl.WF ∅)
    (h : VEnv.addInduct ∅ decl = some env) (hp : decl.projectionEntries = []) {U Γ e₁ e₂ A}
    (hΓ : OnCtx Γ (env.IsType U)) (he : env.IsDefEq U Γ e₁ e₂ A) :
    @CRDefEq (inductParams hdecl h hp U) Γ e₁ e₂ :=
  letI := inductParams hdecl h hp U
  IsDefEq.church_rosser hΓ he

end VEnv
end Lean4Lean
