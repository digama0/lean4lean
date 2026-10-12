import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Theory.Inductive.RecursorSchema

/-! # Equations realised by the environment

On the ι pattern calculus the generated recursor equations are not stored: each is registered
as the ι pattern of its recursor rule (`VEnv.addRecRule`). The singleton prefix unfolding
(`Theory/Typing/PrefixUnfolding/`) applies such an equation at an instance of its λ-telescope.
`VEnv.PatEquation` abstracts what the unfolding needs of an equation: its three sides are
closed and, at every universe instantiation and every well-typed instance of its telescope
(the common λ/∀ telescope of its sides, `RecursorSchema.EquationBody.extract`) whose redex is
typed, the two instantiated bodies are convertible. A stored equation realises
it (`PatEquation.of_defeq`); the singleton equation of a registered recursor realises it through
`IsDefEq.pat` (`Theory/Typing/Confluence/SingletonCoverage.lean`). -/

namespace Lean4Lean.VEnv
open VExpr

/-- An equation the environment realises at every typed instance of its telescope. -/
structure PatEquation (env : VEnv) (df : VDefEq) : Prop where
  lhs_closed : df.lhs.Closed
  rhs_closed : df.rhs.Closed
  type_closed : df.type.Closed
  instOuter : ∀ {U : Nat} {Γ : List VExpr} {ls : List VLevel}
    {body : InductiveSignature.RecursorSchema.EquationBody} {T : VExpr} {args : List VExpr},
    OnCtx Γ (env.IsType U) → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    InductiveSignature.RecursorSchema.EquationBody.extract df.lhs df.rhs df.type = some body →
    args.length = body.domains.length →
    (∀ j (hj : j < args.length) (hj' : j < body.domains.length),
      env.HasType U Γ args[j] (((body.domains[j]).instL ls).instOuter (args.take j))) →
    env.HasType U Γ ((body.lhs.instL ls).instOuter args) T →
    env.IsDefEqU U Γ ((body.lhs.instL ls).instOuter args) ((body.rhs.instL ls).instOuter args)

/-- A stored equation of a well-formed environment is realised. -/
theorem PatEquation.of_defeq {env : VEnv} (henv : env.WF) {df : VDefEq} (hdf : env.defeqs df) :
    env.PatEquation df := by
  have hwf := henv.ordered.defEqWF hdf
  have hl : df.lhs.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env df.uvars [] _ from ⟨_, hwf.1⟩) trivial
  have hr : df.rhs.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env df.uvars [] _ from ⟨_, hwf.2⟩) trivial
  have hleft : env.HasType df.uvars [] df.lhs df.type := hwf.1
  obtain ⟨u, ht⟩ := hleft.isType henv.ordered (show OnCtx [] (env.IsType df.uvars) from trivial)
  have ht : df.type.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env df.uvars [] _ from ⟨_, ht⟩) trivial
  refine ⟨hl, hr, ht, ?_⟩
  intro U Γ ls body T args hΓ hls hlen hbody hargs hty _
  obtain ⟨hlhs, hrhs, htype⟩ := InductiveSignature.RecursorSchema.EquationBody.extract_sound hbody
  exact ⟨_, IsDefEq.extra_instOuter henv hΓ hdf hls hlen hlhs.symm hrhs.symm htype.symm
    hargs hty⟩

end Lean4Lean.VEnv
