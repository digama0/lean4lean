import Lean4Lean.Theory.Typing.Confluence.RecursorRegistryOfWF
import Lean4Lean.Theory.Typing.Confluence.RegistryMetadata
import Lean4Lean.Theory.Typing.Confluence.RegistrySeparation
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory

/-! A complete syntax registry is chosen from actual environment formation.
The contract records installed metadata and exact equation dispatch; semantic
normalization of the selected rules is a separate obligation. -/
namespace Lean4Lean.HeadRegistry
open VEnv InductiveSignature
set_option Elab.async false
set_option maxRecDepth 2048
variable {env : VEnv} {declarations : List VDecl} {registry : Registry}

/-- The concrete tables combine actual environment metadata with the two
history-derived name tables. Only computationally empty recursor entries vanish. -/
noncomputable def Registry.ofEnvironment (env : VEnv) (declarations : List VDecl)
    (recursors : Name → Option RecursorData) : Registry := by
  classical
  exact (Registry.ofDataHistory declarations recursors
    (environmentCases env) (environmentProjections env) (environmentStructures env)
    (decide (VDecl.quot ∈ declarations))).removeEmptyRecursors

/-- Each installed equation has its actual dispatch data and priority
exclusions. This does not assert a semantic reduction or its typed guards. -/
inductive Registry.EquationOrigin (registry : Registry) (env : VEnv) (equation : VDefEq) : Prop where
  | definition (value : VDefVal)
      (lookup : registry.definitions value.name = some value)
      (registered : DefinitionRegistered env value)
      (equal : equation = value.toDefEq) : EquationOrigin registry env equation
  | quotient (registered : QuotRegistered env)
      (enabled : registry.quotient = true)
      (notDefinition : registry.definitions ``Quot.lift = none)
      (notRecursor : registry.recursors ``Quot.lift = none)
      (equal : equation = quotDefEq) : EquationOrigin registry env equation
  | recursor (data : RecursorData)
      (lookup : registry.recursors data.name = some data)
      (notDefinition : registry.definitions data.name = none)
      (registered : RecursorRegistered env data)
      (index : Fin data.schema.signature.constructors.size)
      (owner : data.schema.signature.constructors[index].owner = data.owner)
      (generated : data.equation index = some equation) : EquationOrigin registry env equation

/-- The exact environmental facts consumed by recursor/data dispatch, including
provenance of each surviving recursor and completeness for primitive metadata. -/
structure Registry.EnvironmentContract (registry : Registry) (env : VEnv)
    (declarations : List VDecl) : Prop where
  history : env.WF' declarations
  scope : registry.Scoped
  definitions : ∀ name value, registry.definitions name = some value →
    DefinitionRegistered env value ∧ value.name = name
  recursors : ∀ name data, registry.recursors name = some data →
    RecursorRegistered env data ∧ data.name = name ∧
      Nonempty (RecursorDeclarationOrigin env declarations data)
  recursorNotDefinition : ∀ name data, registry.recursors name = some data →
    registry.definitions name = none
  projections : ∀ name info, registry.projections name = some info ↔ env.projections name info
  structures : ∀ name entry, registry.structureConstructors name = some entry ↔
    env.projections entry.typeName entry.info ∧ entry.info.ctorName = name
  caseLookup : ∀ block owner entry, registry.cases block owner = some entry ↔
    env.eliminators block entry.schema ∧ entry.owner.val = owner ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed
  quotient : registry.quotient = true ↔ VDecl.quot ∈ declarations
  quotientRegistered : registry.quotient = true → QuotRegistered env
  rigid : ∀ name, env.Rigid name → HeadInert registry name
  equations : ∀ equation, env.defeqs equation → registry.EquationOrigin env equation

private theorem fromHistory_scoped
    (history : RecursorRegistryHistory env declarations recursors) :
    (Registry.ofEnvironment env declarations recursors).Scoped := by
  apply HeadRegistry.Registry.Scoped.removeEmptyRecursors
  apply Registry.ofDataHistory_scoped history
  intro block owner entry lookup
  obtain ⟨registered, _, header⟩ := environmentCases_sound lookup
  exact ⟨registered, header⟩

/-- Well-formedness constructs the final registry, with no table, schema,
closure, rigidity, disjointness or equation-coverage premise. -/
theorem _root_.Lean4Lean.VEnv.WF'.headRegistry
    (formed : env.WF' declarations) :
    ∃ registry : Registry, registry.EnvironmentContract env declarations := by
  classical
  obtain ⟨recursors, history, coverage⟩ := formed.recursorRegistry
  let raw := Registry.ofDataHistory declarations recursors
    (environmentCases env) (environmentProjections env) (environmentStructures env)
    (decide (VDecl.quot ∈ declarations))
  let registry := raw.removeEmptyRecursors
  have formedEnv : env.WF := ⟨declarations, formed⟩
  have definitions : ∀ name value, raw.definitions name = some value →
      DefinitionRegistered env value ∧ value.name = name := fun _ _ lookup =>
    formed.definitionRegistry_registered lookup
  have recursorSound : ∀ name data, raw.recursors name = some data →
      RecursorRegistered env data ∧ data.name = name := fun _ _ lookup => history.registered lookup
  have quotientSound : raw.quotient = true → QuotRegistered env := by
    intro enabled
    exact (history.quotient (of_decide_eq_true enabled)).1
  refine ⟨registry, {
    history := formed
    scope := fromHistory_scoped history
    definitions := definitions
    recursors := ?_
    recursorNotDefinition := fun _ _ lookup =>
      raw.removeEmptyRecursors_notDefinition formedEnv definitions recursorSound lookup
    projections := ?_
    structures := ?_
    caseLookup := ?_
    quotient := ?_
    quotientRegistered := quotientSound
    rigid := fun name rigid => raw.removeEmptyRecursors_headInert definitions recursorSound
      (fun enabled => (quotientSound enabled).equation) rigid
    equations := ?_ }⟩
  · intro name data lookup
    have actual := (raw.removeEmptyRecursors_lookup.mp lookup).1
    exact ⟨(recursorSound name data actual).1, history.origin actual⟩
  · intro name info
    exact ⟨environmentProjections_sound,
      environmentProjections_complete formedEnv.ordered⟩
  · intro name entry
    refine ⟨environmentStructures_sound, ?_⟩
    rintro ⟨registered, named⟩
    rw [← named]
    exact environmentStructures_complete formedEnv.ordered registered
  · intro block owner entry
    refine ⟨environmentCases_sound, ?_⟩
    rintro ⟨registered, named, header, selected, closed⟩
    rw [← named]
    exact environmentCases_complete formedEnv registered selected closed
  · exact decide_eq_true_iff
  · intro equation present
    rcases coverage equation present with ⟨value, lookup, equal⟩ |
      ⟨quotientMember, equal⟩ | ⟨data, lookup, index, owner, generated⟩
    · exact .definition value lookup (formed.definitionRegistry_registered lookup).1 equal
    · obtain ⟨registered, absent⟩ := history.quotient quotientMember
      have notDefinition : registry.definitions ``Quot.lift = none := by
        change definitionRegistry declarations ``Quot.lift = none
        cases lookup : definitionRegistry declarations ``Quot.lift with
        | none => rfl
        | some value =>
          obtain ⟨defined, named⟩ := formed.definitionRegistry_registered lookup
          apply False.elim
          apply defined.not_constructor_equation formedEnv registered.equation
            (levels := [VLevel.param 0, VLevel.param 1]) (ctorName := ``Quot.mk)
          · rw [named]; rfl
          · exact ⟨_, [VLevel.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
      have notRecursor : registry.recursors ``Quot.lift = none := by
        change (do let data ← recursors ``Quot.lift
                   if data.constructorIndices.isEmpty then none else some data) = none
        rw [absent]
        rfl
      exact .quotient registered (by exact decide_eq_true quotientMember) notDefinition notRecursor equal
    · have retained : registry.recursors data.name = some data :=
        raw.removeEmptyRecursors_preserves_owned lookup owner
      exact .recursor data retained
        (raw.removeEmptyRecursors_notDefinition formedEnv definitions recursorSound retained)
        (history.registered lookup).1 index owner generated

/-- The public environment hypothesis suffices to choose both the declaration
history and its final concrete dispatch registry. -/
theorem _root_.Lean4Lean.VEnv.WF.headRegistry (formed : env.WF) :
    ∃ (declarations : List VDecl) (registry : Registry), registry.EnvironmentContract env declarations := by
  obtain ⟨declarations, history⟩ := formed
  obtain ⟨registry, contract⟩ := history.headRegistry
  exact ⟨declarations, registry, contract⟩

end Lean4Lean.HeadRegistry
