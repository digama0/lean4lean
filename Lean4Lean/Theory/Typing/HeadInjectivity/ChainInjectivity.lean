import Lean4Lean.Theory.Typing.HeadInversionDefs

/-! # Chain-level head injectivity and the injectivity fields of head inversion

`ChainHeadInjectivity` is the hypothesis of the syntactic layer: injectivity of type heads
along `TypeChain`s, supplied for every well-formed environment by the glued observation model
(`VEnv.WF.chainHeadInjectivity`, `Model/EnvValid.lean`; section 4.1 of
the design notes). `HeadInjectivity` is what the
syntactic layer derives from it: the structure `VEnv.HeadInjectivity` of
`HeadInversionDefs.lean` (uniqueness-free, so importable here). This directory must not import
`HeadInversion.lean`, `UniqueTyping.lean`, `Injectivity.lean`, `ChurchRosser.lean`,
`FullReduction.lean` or `HeadReduction.lean`. -/

namespace Lean4Lean
namespace VEnv

/-- Chain-level head injectivity: the hypothesis of the syntactic layer.

`sort_sort`, `rigid_rigid` and `former_args` are the fields of `HeadInversion` of the
same names; `forallE_chain` is the chain-level form of `forallE_forallE`, relating the
domains and codomains by chains rather than by single definitional equalities. -/
structure ChainHeadInjectivity (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  forallE_chain : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    env.TypeChain U Γ A A' ∧ env.TypeChain U (A :: Γ) B B'
  rigid_rigid : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : ∀ {U Γ c ci doms w ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'

end VEnv
end Lean4Lean
