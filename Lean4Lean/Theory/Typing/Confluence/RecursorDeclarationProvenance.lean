import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.InductiveDeclarationHistory
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryScope
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.InductiveDeclarationStages
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Inductive.SourceShape

/-! Recursor table installation with original declaration provenance.

`RecursorRegistered` checks a final environment.  It does not identify
the declaration whose pre-equation header may be used by stage induction.
The finite construction here follows the actual `WF'` constructors and the
existing `installEntries` operation.  Lookup therefore returns the original
header and its ordinal, rather than an unrelated existential predecessor.
-/
namespace Lean4Lean.VEnv
open InductiveSignature RecursorData
open private declaration_le from Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
variable {name key : Name} {env extended base envTypes envCtors : VEnv}
  {source expanded : VInductDecl} {block : VInductBlock} {schema : CaseSchema}
  {signature : InductiveSignature} {generated : Instance signature}
  {auxiliaries : List ContainerSpecialization} {equation : VDefEq}

/-- A lookup packet, produced from a concrete table history below. -/
structure RecursorDeclarationOrigin (env : VEnv) (declarations : List VDecl)
    (data : RecursorData) where
  source : VInductDecl
  stage : InductiveStage env source declarations.length
  laterDeclarations : List VDecl
  declarations_eq : declarations = laterDeclarations ++ .induct source :: stage.earlierDeclarations
  expanded : VInductDecl
  signature : InductiveSignature
  generated : Instance signature
  auxiliaries : List ContainerSpecialization
  key : Name
  compilationBase : VEnv
  compilationBelow : compilationBase ≤ stage.base
  compilation : CompilationData compilationBase source expanded signature generated auxiliaries stage.block
  specializations : ContainersInstalled compilationBase auxiliaries
  entry : data ∈ compilationEntries key source signature auxiliaries generated

namespace RecursorDeclarationOrigin

def later (origin : RecursorDeclarationOrigin env declarations data)
    (declaration : VDecl.WF env d extended) : RecursorDeclarationOrigin extended (d :: declarations) data where
  source := origin.source
  stage := origin.stage.later (declaration_le declaration) (Nat.le_succ _)
  laterDeclarations := d :: origin.laterDeclarations
  declarations_eq := by simpa only [List.cons_append, InductiveStage.later] using congrArg (List.cons d) origin.declarations_eq
  expanded := origin.expanded
  signature := origin.signature
  generated := origin.generated
  auxiliaries := origin.auxiliaries
  key := origin.key
  compilationBase := origin.compilationBase
  compilationBelow := origin.compilationBelow
  compilation := origin.compilation
  specializations := origin.specializations
  entry := origin.entry

def metadata (origin : RecursorDeclarationOrigin env declarations data)
    (hle : env ≤ extended) : RecursorDeclarationOrigin extended declarations data where
  source := origin.source
  stage := origin.stage.later hle (Nat.le_refl _)
  laterDeclarations := origin.laterDeclarations
  declarations_eq := origin.declarations_eq
  expanded := origin.expanded
  signature := origin.signature
  generated := origin.generated
  auxiliaries := origin.auxiliaries
  key := origin.key
  compilationBase := origin.compilationBase
  compilationBelow := origin.compilationBelow
  compilation := origin.compilation
  specializations := origin.specializations
  entry := origin.entry

theorem installed (origin : RecursorDeclarationOrigin env declarations data) :
    origin.stage.block.install origin.stage.base = some origin.stage.installed := by
  simp [VInductBlock.install, origin.stage.typing.addTypes,
    origin.stage.typing.addConstructors, origin.stage.typing.addRecursors,
    Option.bind_some, origin.stage.typing.installed_eq]

theorem registered (origin : RecursorDeclarationOrigin env declarations data) :
    RecursorRegistered env data :=
  RecursorRegistered.compilationEntries origin.compilation origin.specializations
    origin.compilationBelow origin.installed origin.stage.installedBelow origin.entry

end RecursorDeclarationOrigin

/-- A finite recursor registry built along an actual declaration history.
The `induct` constructor registers all family descriptors from the very block
whose constants and equations are installed by that declaration.  Ordinary
declarations and metadata preserve previously recorded entries. -/
inductive RecursorRegistryHistory : VEnv → List VDecl → (Name → Option RecursorData) → Prop where
  | empty : RecursorRegistryHistory .empty [] (fun _ => none)
  | decl {env extended : VEnv} {declarations : List VDecl} {table : Name → Option RecursorData} (previous : RecursorRegistryHistory env declarations table)
      (declaration : VDecl.WF env d extended) :
      RecursorRegistryHistory extended (d :: declarations) table
  | induct {base extended compilationBase : VEnv} {declarations : List VDecl} {table : Name → Option RecursorData}
      {source expanded : VInductDecl} {block : VInductBlock} {signature : InductiveSignature}
      {generated : Instance signature} {auxiliaries : List ContainerSpecialization} {key : Name}
      (previous : RecursorRegistryHistory base declarations table)
      (original : source.WF base)
      (compiled : source.CompilesTo base block)
      (formed : block.WF base)
      (eliminatorsWF : VInductBlock.EliminatorsWF base source block)
      (installed : block.install base = some extended)
      (compilation : CompilationData compilationBase source expanded signature generated auxiliaries block)
      (specializations : ContainersInstalled compilationBase auxiliaries)
      (compilationBelow : compilationBase ≤ base) :
      RecursorRegistryHistory extended (.induct source :: declarations)
        (installEntries table (compilationEntries key source signature auxiliaries generated))
  | eliminators {env base : VEnv} {declarations baseDeclarations : List VDecl}
      {table : Name → Option RecursorData} {source : VInductDecl} {block : VInductBlock}
      {schema : CaseSchema} {key : Name} (previous : RecursorRegistryHistory env declarations table)
      (baseHistory : base.WF' baseDeclarations)
      (hle : base ≤ env)
      (registered : schema.RegistrationCertificate base source block key)
      (constants : ∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant)
      (equations : env.defeqs = base.defeqs)
      (projectionNames : schema.ProjNamesRegistered env key)
      (coherent : source.ProjectionsCoherent env)
      (fresh : schema.Fresh env key)
      (compat : schema.StructCompat env) :
      RecursorRegistryHistory (env.addEliminator key schema) declarations table
  | projections {base envTypes envCtors : VEnv} {declarations baseDeclarations : List VDecl}
      {table : Name → Option RecursorData} {source : VInductDecl} {block : VInductBlock}
      (previous : RecursorRegistryHistory (envCtors.addEliminators block.eliminators)
        declarations table)
      (baseHistory : base.WF' baseDeclarations)
      (covered : ∃ key schema, block.eliminators = [(key, schema)] ∧
        schema.RegistrationCertificate base source block key)
      (sourceNames : source.sourceNames.Nodup)
      (typeHeadersWF : ∀ type ∈ source.types, type.toVConstant.WF base)
      (constructorUvars : ∀ ctor ∈ source.constructorConstants, ctor.uvars = source.uvars)
      (constructorsWF : ∀ ctor ∈ source.constructorConstants, ctor.toVConstant.WF envTypes)
      (parameters : source.SourceParameterWF base)
      (shape : ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor)
      (types : block.types = source.typeConstants)
      (constructors : block.ctors = source.constructorConstants)
      (projections : block.projections = source.projectionEntries)
      (addTypes : base.addConstVals block.types = some envTypes)
      (addConstructors : envTypes.addConstVals block.ctors = some envCtors) :
      RecursorRegistryHistory ((envCtors.addEliminators block.eliminators).addProjections
        block.projections) declarations table

namespace RecursorRegistryHistory

theorem history (H : RecursorRegistryHistory env declarations table) : env.WF' declarations := by
  induction H with
  | empty => exact .empty
  | decl _ declaration ih => exact .decl declaration ih
  | induct _ original compiled formed eliminatorsWF installed _ _ _ ih =>
    exact .decl (.induct (.intro original compiled formed eliminatorsWF installed)) ih
  | eliminators _ baseHistory hle registered constants equations projectionNames coherent fresh
      compat ih =>
    exact .inductEliminators baseHistory ih hle registered constants equations projectionNames
      coherent fresh compat
  | projections _ baseHistory covered sourceNames typeHeadersWF constructorUvars constructorsWF parameters shape types constructors projections addTypes addConstructors ih =>
    exact .inductProjections baseHistory ih covered sourceNames typeHeadersWF constructorUvars constructorsWF
      parameters shape types constructors projections addTypes addConstructors

/-- Lookup follows the concrete list installation, retaining exactly one
original compilation and header. No current/final-environment Strong proof
is reinterpreted as an earlier induction hypothesis. -/
theorem origin (H : RecursorRegistryHistory env declarations table)
    (lookup : table name = some data) :
    data.name = name ∧ Nonempty (RecursorDeclarationOrigin env declarations data) := by
  induction H with
  | empty => cases lookup
  | decl _ declaration ih =>
    obtain ⟨same, ⟨origin⟩⟩ := ih lookup
    exact ⟨same, ⟨origin.later declaration⟩⟩
  | @induct base extended compilationBase declarations table source expanded block signature generated auxiliaries key
      previous original compiled formed eliminatorsWF installed compilation specializations
      compilationBelow ih =>
    unfold installEntries at lookup
    cases found : (compilationEntries key source signature auxiliaries generated).find?
        (fun value => value.name == name) with
    | none =>
      obtain ⟨same, ⟨origin⟩⟩ := ih (by simpa only [found, Option.orElse_none] using lookup)
      exact ⟨same, ⟨origin.later (.induct
        (.intro original compiled formed eliminatorsWF installed))⟩⟩
    | some selected =>
      simp only [found, Option.orElse_some, Option.some.injEq] at lookup
      subst selected
      obtain ⟨stages⟩ := VInductBlock.TypingStages.ofInstallation
        ⟨declarations, previous.history⟩ original compiled formed eliminatorsWF installed
      refine ⟨by simpa only [beq_iff_eq] using List.find?_some found, ⟨{
        source := source
        stage := ⟨base, extended, block, declarations, previous.history,
          Nat.lt_succ_self _, original, compiled, stages, .rfl⟩
        laterDeclarations := []
        declarations_eq := rfl
        expanded := expanded
        signature := signature
        generated := generated
        auxiliaries := auxiliaries
        key := key
        compilationBase := compilationBase
        compilationBelow := compilationBelow
        compilation := compilation
        specializations := specializations
        entry := List.mem_of_find?_eq_some found }⟩⟩
  | eliminators _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨same, ⟨origin⟩⟩ := ih lookup
    exact ⟨same, ⟨origin.metadata VEnv.addEliminator_le⟩⟩
  | projections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨same, ⟨origin⟩⟩ := ih lookup
    exact ⟨same, ⟨origin.metadata VEnv.addProjections_le⟩⟩

/-- The actual table history supplies recursor registration independently of
optional abstract-schema metadata. -/
theorem registered (H : RecursorRegistryHistory env declarations table)
    (lookup : table name = some data) : RecursorRegistered env data ∧ data.name = name := by
  obtain ⟨same, ⟨origin⟩⟩ := H.origin lookup
  exact ⟨origin.registered, same⟩

end RecursorRegistryHistory

/-- A recursor installation cannot manufacture a new metadata entry for an
already present constant. This is the backward lookup used when interpreting
an earlier source header against a later final registry. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.installEntries_previous
    (compiled : CompilationData base source expanded signature generated auxiliaries block)
    (installed : block.install installBase = some extended)
    (present : installBase.constants name = some value)
    (lookup : installEntries table (compilationEntries key source signature auxiliaries generated)
      name = some data) : table name = some data := by
  unfold installEntries at lookup
  cases found : (compilationEntries key source signature auxiliaries generated).find?
      (fun value => value.name == name) with
  | none => simpa only [found, Option.orElse_none] using lookup
  | some newEntry =>
    have same : newEntry.name = name := by simpa only [beq_iff_eq] using List.find?_some found
    have fresh := compiled.recursorEntries_fresh installed (List.mem_of_find?_eq_some found)
    rw [same, present] at fresh
    cases fresh

end Lean4Lean.VEnv
