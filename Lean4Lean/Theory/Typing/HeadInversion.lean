import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.HeadInjectivity.Fields
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Separation
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EnvValid

/-! # Head inversion for types: the base obligation of the inversion layer

The statements (`HeadInversion`, `HeadSeparation`, `HeadInjectivity`) and the chain lemmas are in
`HeadInversionDefs.lean`. Both halves are proved for every well-formed environment from the glued
observation model (`Theory/Typing/HeadInjectivity/Model/`): separation by
`VEnv.WF.headSeparationModel`, injectivity by `VEnv.WF.chainHeadInjectivity`. Every inversion
lemma of `Injectivity.lean` and uniqueness of types (`IsDefEq.uniq`) are derived from these two
statements through the syntactic layer (`HeadInjectivity/{ChainInjectivity, Congruence,
FieldType, Uniqueness, Fields}.lean`).

**What the model's theorems depend on, on the ι pattern calculus.** The model interprets
*strong* derivations (`IsDefEqStrong`), and its extraction turns a weak `TypeChain` link into a
strong derivation by `IsDefEq.strong` (`Model.chain_sub`, `Model.spine_data`), which on this
calculus takes `VEnv.OrderedStrong`, whose `pats` field is `VEnv.WF.patsStrong` (subject
reduction of the registered ι rules, the open theorem of PR #43). The substitution theorems the
model uses (`IsDefEq.substDF`, `IsDefEqStrong.substEq'`, `HasType.subst`) and the inversion
lemmas (`HasType.app_inv`, `HasType.const_inv`) take `OrderedStrong` for the same reason. So
`VEnv.WF.chainHeadInjectivity`, `VEnv.WF.headSeparationModel`, and everything below them
(`VEnv.WF.headInversion`, `IsDefEq.uniq`, `Injectivity.lean`) are conditional on
`VEnv.WF.patsStrong`, through `VEnv.WF.orderedStrong`; the model does not use `patsStrong`
anywhere else, and no history-induction organisation avoids the use, since the extraction's
input is a weak chain. They are also conditional on the two wave 1C stubs recorded in
`STUBS.md`: `Model.PatValid.iota` (the `pat` case of soundness for the registered ι rules,
`Model/PatSound.lean`) and `VEnv.WF.patCtor_rigid` (`Model/WFFacts.lean`).

This file and the model do not import `UniqueTyping`, `Injectivity`, `ChurchRosser`,
`FullReduction` or `HeadReduction` (section 4.1 of the design notes). -/

namespace Lean4Lean
namespace VEnv

/-- **Chain-level head injectivity** for every well-formed environment, from soundness of the
glued observation model (`VEnv.WF.soundEnv`, `HeadInjectivity/Model/EnvValid.lean`). -/
theorem _root_.Lean4Lean.VEnv.WF.chainHeadInjectivity {env : VEnv} (henv : env.WF) :
    env.ChainHeadInjectivity :=
  WF.chainHeadInjectivity_of_sound henv henv.soundEnv

/-- **Head separation** for every well-formed environment, from the glued observation model
(`HeadInjectivity/Model/Separation.lean`): a sort has a `sort` observation, a Pi type a `piDom`
observation, a rigid spine neither. -/
theorem _root_.Lean4Lean.VEnv.WF.headSeparationModel {env : VEnv} (henv : env.WF) :
    env.HeadSeparation :=
  WF.headSeparation_of_sound henv henv.soundEnv

/-- Separation for every well-formed environment, from the glued observation model. -/
theorem _root_.Lean4Lean.VEnv.WF.headSeparation {env : VEnv} (henv : env.WF) :
    env.HeadSeparation :=
  henv.headSeparationModel

/-- Injectivity of type heads for every well-formed environment: the chain-level core from
soundness of the glued observation model (`VEnv.WF.chainHeadInjectivity`), lifted by the
syntactic layer (`VEnv.ChainHeadInjectivity.toHeadInjectivity`). -/
theorem _root_.Lean4Lean.VEnv.WF.headInjectivity {env : VEnv} (henv : env.WF) :
    env.HeadInjectivity :=
  henv.chainHeadInjectivity.toHeadInjectivity henv

/-- The base obligation of the inversion layer, assembled from separation and injectivity.

All inversion lemmas in `Injectivity.lean` are derived from it; uniqueness of types
(`IsDefEq.uniq`) uses the chain-level core directly. -/
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
