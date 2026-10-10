import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.TypeChain
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! # Head inversion for types: the statements

The definitions of the base obligation of the inversion layer (`HeadInversion`, its separation
half `HeadSeparation` and its injectivity half `HeadInjectivity`) and the chain lemmas. The
theorems `VEnv.WF.headSeparation`, `VEnv.WF.headInjectivity` and `VEnv.WF.headInversion` are in
`HeadInversion.lean`, which also imports the observation model proving both halves.

This file imports only the uniqueness-free base (`Lemmas`, `Strong`, `EnvLemmas`,
`ProjectionRigidity`). It must not import `UniqueTyping`, `Injectivity`, `ChurchRosser`,
`FullReduction` or `HeadReduction`. See section 4.1 of the design notes. -/

namespace Lean4Lean
namespace VEnv

/-- Head inversion for types: what the semantic layer delivers.

Every field speaks about `TypeChain`s, that is about types related by definitional
equalities each typed at a sort. "Typed at a sort" is essential: rigid heads are not
injective at term level (`Or.inl h ≡ Or.inr h'` by proof irrelevance, `S.mk (proj e) ≡ e`
by `structEta`), but at the type level they are.

The fields `sort_sort` through `forallE_rigid` are head separation and head injectivity
(section 4.1 of the design notes). The last field, `proj_fieldType`, is the
projection case of uniqueness
of types, stated without uniqueness. It is not derivable from `rigid_rigid` and
`former_args` by substitution in this calculus, for the following reason. A projection's
field type is the constructor telescope instantiated by the parameters and by the
projections of the major onto all *earlier* fields, including fields that the selected
field type does not mention. To compare two such instantiations by a typed simultaneous
substitution (`IsDefEq.substDF`) or by repeated `IsDefEq.instDF`, every earlier projection
must be typed. Under the `projDF` guard `resultLevel.IsNeverZero ∨ fieldLevel ≈ 0` the
projection of a data field out of a structure that may live in `Prop` is untypable, so the
substitution is not typed whenever such a field precedes the selected one, even if the
selected field type does not depend on it. Removing the unused binder instead needs
strengthening, which is not available (section 5.1 of the design notes). A
comparison of the typed occurrences only would need uniqueness of types at arbitrary
subterms of the field type, which is circular inside the induction proving uniqueness. So
the projection case is a field of the obligation; it is proved together with uniqueness up to
chains by the induction of `HeadInjectivity/Uniqueness.lean`. -/
structure HeadInversion (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  forallE_forallE : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ v, env.IsDefEq U (A :: Γ) B B' (.sort v)
  rigid_rigid : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : ∀ {U Γ c ci doms w ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'
  sort_forallE : ∀ {U Γ u A B}, OnCtx Γ (env.IsType U) →
    ¬env.TypeChain U Γ (.sort u) (.forallE A B)
  sort_rigid : ∀ {U Γ c u ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)
  forallE_rigid : ∀ {U Γ c A B ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)
  /-- Two typings of one projection select chain-related field types, given the data of
  both projection typings, sources related at the first major type, and the two major
  types related by a chain. -/
  proj_fieldType : ∀ {U Γ typeName info index
      levels₁ params₁ indexArgs₁ sourceMajor₁ fieldType₁ fieldLevel₁
      levels₂ params₂ indexArgs₂ sourceMajor₂ fieldType₂ fieldLevel₂},
    OnCtx Γ (env.IsType U) → env.projections typeName info → info.ctorType.Closed →
    (∀ l ∈ levels₁, l.WF U) → levels₁.length = info.uvars →
    params₁.length = info.nparams → indexArgs₁.length = info.nindices →
    info.fieldType typeName levels₁ params₁ index sourceMajor₁ = some fieldType₁ →
    env.HasType U Γ fieldType₁ (.sort fieldLevel₁) →
    (info.resultLevel.inst levels₁).IsNeverZero ∨ fieldLevel₁ ≈ .zero →
    (∀ l ∈ levels₂, l.WF U) → levels₂.length = info.uvars →
    params₂.length = info.nparams → indexArgs₂.length = info.nindices →
    info.fieldType typeName levels₂ params₂ index sourceMajor₂ = some fieldType₂ →
    env.HasType U Γ fieldType₂ (.sort fieldLevel₂) →
    (info.resultLevel.inst levels₂).IsNeverZero ∨ fieldLevel₂ ≈ .zero →
    env.IsDefEq U Γ sourceMajor₁ sourceMajor₂
      (.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁)) →
    env.TypeChain U Γ (.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁))
      (.mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)) →
    env.TypeChain U Γ fieldType₁ fieldType₂

/-- The separation half of `HeadInversion`: chains cannot connect types with different head
classes, and equal rigid heads have equivalent universe levels. It is proved from a sound
denotational model of the calculus (`Theory/Typing/EnvTables/`), with no adequacy theorem. -/
structure HeadSeparation (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  sort_forallE : ∀ {U Γ u A B}, OnCtx Γ (env.IsType U) →
    ¬env.TypeChain U Γ (.sort u) (.forallE A B)
  sort_rigid : ∀ {U Γ c u ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)
  forallE_rigid : ∀ {U Γ c A B ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)
  rigid_heads : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls'

/-- The injectivity half of `HeadInversion`: the fields that produce declarative derivations
between components. `rigid_args` is the argument conjunct of `rigid_rigid`, stated for a
single head (the head and level conjuncts are `HeadSeparation.rigid_heads`). -/
structure HeadInjectivity (env : VEnv) : Prop where
  forallE_forallE : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ v, env.IsDefEq U (A :: Γ) B B' (.sort v)
  rigid_args : ∀ {U Γ c ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : ∀ {U Γ c ci doms w ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'
  proj_fieldType : ∀ {U Γ typeName info index
      levels₁ params₁ indexArgs₁ sourceMajor₁ fieldType₁ fieldLevel₁
      levels₂ params₂ indexArgs₂ sourceMajor₂ fieldType₂ fieldLevel₂},
    OnCtx Γ (env.IsType U) → env.projections typeName info → info.ctorType.Closed →
    (∀ l ∈ levels₁, l.WF U) → levels₁.length = info.uvars →
    params₁.length = info.nparams → indexArgs₁.length = info.nindices →
    info.fieldType typeName levels₁ params₁ index sourceMajor₁ = some fieldType₁ →
    env.HasType U Γ fieldType₁ (.sort fieldLevel₁) →
    (info.resultLevel.inst levels₁).IsNeverZero ∨ fieldLevel₁ ≈ .zero →
    (∀ l ∈ levels₂, l.WF U) → levels₂.length = info.uvars →
    params₂.length = info.nparams → indexArgs₂.length = info.nindices →
    info.fieldType typeName levels₂ params₂ index sourceMajor₂ = some fieldType₂ →
    env.HasType U Γ fieldType₂ (.sort fieldLevel₂) →
    (info.resultLevel.inst levels₂).IsNeverZero ∨ fieldLevel₂ ≈ .zero →
    env.IsDefEq U Γ sourceMajor₁ sourceMajor₂
      (.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁)) →
    env.TypeChain U Γ (.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁))
      (.mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)) →
    env.TypeChain U Γ fieldType₁ fieldType₂

/-! ## Chain lemmas

Chains inherit the structural operations of `IsDefEq` link by link; none of these
lemmas uses uniqueness. -/

end VEnv
end Lean4Lean
