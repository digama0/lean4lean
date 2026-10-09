import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.HeadInjectivity.Fields
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Separation

/-! # Head inversion for types: the base obligation of the inversion layer

The statements (`HeadInversion`, `HeadSeparation`, `HeadInjectivity`) and the chain lemmas are in
`HeadInversionDefs.lean`. Both halves are proved for every well-formed environment from the glued
observation model (`Theory/Typing/HeadInjectivity/Model/`): separation by
`VEnv.WF.headSeparationModel`, injectivity by `VEnv.WF.chainHeadInjectivity`.

This file and the model do not import `UniqueTyping`, `Injectivity`, `ChurchRosser`,
`FullReduction` or `HeadReduction`. Uniqueness of types (`IsDefEq.uniq`) is derived from the
chain-level core `VEnv.WF.chainHeadInjectivity`, and every inversion lemma in
`Injectivity.lean` from `VEnv.WF.headInversion`, assembled here (section 4.1 of
the design notes). -/

namespace Lean4Lean
namespace VEnv

/-- Separation for every well-formed environment, from the glued observation model. -/
theorem _root_.Lean4Lean.VEnv.WF.headSeparation {env : VEnv} (henv : env.WF) :
    env.HeadSeparation :=
  henv.headSeparationModel

/-- Injectivity of type heads for every well-formed environment: the chain-level core from
soundness of the glued observation model (`VEnv.WF.chainHeadInjectivity`,
`Theory/Typing/HeadInjectivity/Model/EnvValid.lean`), lifted by the syntactic layer
(`VEnv.ChainHeadInjectivity.toHeadInjectivity`). -/
theorem _root_.Lean4Lean.VEnv.WF.headInjectivity {env : VEnv} (henv : env.WF) :
    env.HeadInjectivity :=
  henv.chainHeadInjectivity.toHeadInjectivity henv

/-- The base obligation of the inversion layer, assembled from separation and injectivity.

All inversion lemmas in `Injectivity.lean` and `VConstructorShape.saturated_of_hasType` are
derived from it; uniqueness of types (`IsDefEq.uniq`) uses the chain-level core directly. -/
theorem _root_.Lean4Lean.VEnv.WF.headInversion {env : VEnv} (henv : env.WF) :
    env.HeadInversion :=
  have hs := henv.headSeparation
  have hi := henv.headInjectivity
  { sort_sort := hs.sort_sort
    forallE_forallE := hi.forallE_forallE
    rigid_rigid := fun hΓ hc hc' H =>
      have ⟨h1, h2⟩ := hs.rigid_heads hΓ hc hc' H
      ⟨h1, h2, by subst h1; exact hi.rigid_args hΓ hc H⟩
    former_args := hi.former_args
    sort_forallE := hs.sort_forallE
    sort_rigid := hs.sort_rigid
    forallE_rigid := hs.forallE_rigid
    proj_fieldType := hi.proj_fieldType }

end VEnv
end Lean4Lean
