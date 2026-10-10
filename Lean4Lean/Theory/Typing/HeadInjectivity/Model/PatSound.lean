import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound

/-! # Validity of the registered ι rules

`Model.PatValid.iota`: every registered pattern of a well-formed environment is valid in the
model (`Model.PatValid`, the `pat` case of `Model.sound`). The rule is an ι rule of an
installed block (`VEnv.WF'.pats_origin`): its recursor head has a `pat` clause in `Obs`
(`Obs.pat`), whose binding of the rule's variables from the keys of a head chain is the
`RuleBind` of the stored-rule clause with the reduct template `rhs = wrapLams doms body`
read off `SimplePattern.iotaRHS'`. Soundness of an *instance* `rec us args ≡ rhs us pmm fields`
then follows the two directions of `Model/RuleSound.lean` (`pat_lhs_sub`, `pat_rhs_sub_head`,
which is already stated for an abstract head clause `hrule`) with the instance's spine in place
of the λ-wrapped generic sides, from the semantic typing of the redex (`HTS.spine` gives the
keys of its arguments typed against the recursor's telescope) and of the reduct (the λ-telescope
of `rhs`, `HTS.lamSpine`), and from the static facts of the block: the recursor's telescope
shape (`VInductDecl.WF.rec_shape`, which supplies the `dsH`/`I`/`lsI` data of the clause), the
constructor's shape (`rules_ctor`), uniqueness of the rule per head and constructor
(`PatsIota`, `rules_nodup`), the family's recorded sort (`Model/FamSort.lean`, from soundness of
the environment before the block, along the history), the proof binders of a singleton
elimination (mode C), and the projection entry of a structure family (eta mode,
`Model/EtaBind.lean`).

WAVE 1C STUB: the theorem is stated at the level of `env.WF`; the instance-level soundness and
the static facts above are the remaining material. Every use of the model's conclusions
(`VEnv.WF.chainHeadInjectivity`, `VEnv.WF.headSeparationModel`) depends on it. -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- **Validity of a registered ι rule** in the model of a well-formed environment. -/
theorem PatValid.iota {env : VEnv} (henv : env.WF) {p : Pattern} {r : p.RHS × p.Check}
    (hp : env.pats p r) : PatValid env p r := by
  -- WAVE 1C STUB
  sorry

end Model
end VEnv
end Lean4Lean
