import Lean4Lean.Theory.Typing.ChurchRosser

namespace Lean4Lean
namespace VEnv

open VExpr

/-!
# A concrete `Params` instance from `env.pats`

`ChurchRosser`'s development is parameterised over an abstract pattern-reduction
relation `Params.Pat`. `VEnv.toParams` instantiates it with the environment's own
registered ι rules (`env.pats`), which is the relation actually driving the
`IsDefEq.pat` rule.

Only `pat_wf` is proved here — it is a direct repackaging of `IsDefEq.pat` via the
`Check.OK`/`Realizes` bridge. The structural side conditions
(`pat_simple`/`pat_uniq`/`pat_app_l`/`pat_app_l_uniq`/`pat_app_uniq`/`extra_pat`)
are properties of *how* `env.pats` is populated by `addInduct` (only
`SimplePattern.iota` shapes, added disjointly), and are left as `IOTA-TODO`s. -/

/-- The `Params` structure induced by a well-formed environment `env`, taking the
abstract reduction relation `Pat` to be `env.pats`. -/
@[reducible] def toParams (env : VEnv) (henv : env.WF) (U : Nat) : Params where
  env := env
  henv := henv
  univs := U
  Pat := env.pats
  -- IOTA-TODO(soundness): `env.pats` only ever holds `SimplePattern.iota`-shaped
  -- patterns (`addRecRule` registers exactly those); needs an invariant on how
  -- `addInduct` populates `pats`.
  pat_simple := sorry
  -- IOTA-TODO(soundness): distinct registered ι patterns are equal-or-disjoint;
  -- needs the same population invariant plus injectivity of recursor spines.
  pat_uniq := sorry
  -- `pat_wf` is the genuine content: an `env.pats` reduction is a definitional
  -- equality. Recover a `Realizes` witness from the abstract `Check.OK` premise
  -- and feed it to `IsDefEq.pat`.
  pat_wf := fun {p r e m1 m2 Γ A} hpat hmatch hty hok =>
    let ⟨_, hr, hall⟩ := hok.exists_realizer (rel := fun a b t => IsDefEq env U Γ a b t)
    ⟨A, IsDefEq.pat hpat hmatch hty hr hall⟩
  -- IOTA-TODO(soundness): ι pattern heads (`(varN (const r) m)`) are not nested
  -- applications; structural property of `SimplePattern.iota`.
  pat_app_l := sorry
  -- IOTA-TODO(soundness): argument/variable disjointness across registered ι
  -- patterns; population invariant.
  pat_app_l_uniq := sorry
  -- IOTA-TODO(soundness): subpattern disjointness across registered ι patterns;
  -- population invariant.
  pat_app_uniq := sorry
  -- IOTA-TODO(soundness): `defeqs` are never realised by an ι pattern; population
  -- invariant separating `defeqs` from `pats`.
  extra_pat := sorry

end VEnv
end Lean4Lean
