import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.CaseFormation

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | mutualDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.mutualDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    VEnv.AddInduct env decl env' →
    VDecl.WF env (.induct decl) env'

/-- Projection metadata already registered for a declaration's families agrees
with that declaration's own projection entries. A case schema may only be
registered for a declaration coherent in this sense: otherwise one structure
could carry projections (hence structure eta and the unit-like rule) from one
declaration and a case schema from another, e.g. projections with constructor
`S.a` and a case rule for an unrelated constant `S.b : S`, and `VEnv.IsDefEq`
would not be confluent (`Theory/Typing/EliminatorCoherence.lean`). -/
def VInductDecl.ProjectionsCoherent (env : VEnv) (source : VInductDecl) : Prop :=
  ∀ type ∈ source.types, ∀ info, env.projections type.name info →
    (⟨type.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)
  /-- Register the abstract schemas of a formed finite compilation after its
  exact source constants are present. A fresh key fixes the meaning of every
  owner slot, including nested auxiliaries, for all later environments.
  The schema projects only out of structures registered at this point
  (`CaseSchema.ProjNamesRegistered`), hence never out of a name that is not
  an installed constant, and the projections already registered for its
  families are those of the certified declaration
  (`VInductDecl.ProjectionsCoherent`). Every structure already registered
  over one of its source families has, in the schema, exactly its
  registered constructor (`CaseSchema.StructCompat`): otherwise a schema
  could add constructors to a registered structure, which structure eta
  makes inconsistent.

  The certificate `CaseSchema.RegistrationCertificate` consists of `CaseSchema.Certified`,
  the case part of a compilation (`CaseCompilationData`: formation, model,
  restoration correspondence and scoping, installed source constants, family
  typing) together with freshness of the restoration's auxiliary recursor
  names; the key of the first source family; and the agreement of the
  declared family headers with the restored normalized ones
  (`CaseSchema.HeaderAgreement`). The eliminator rules `elimDF`/`elimIota`
  read only the schema data fixed by the case part, never the generated
  recursors, so a declaration registers its case schema once its constructors
  are installed, before its recursors are generated and checked. -/
  | inductEliminators {base env : VEnv} {source : VInductDecl}
      {block : VInductBlock} {schema : InductiveSignature.CaseSchema} :
    VEnv.WF' baseDecls base →
    VEnv.WF' ds env →
    base ≤ env →
    schema.RegistrationCertificate base source block key →
    (∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant) →
    env.defeqs = base.defeqs →
    schema.ProjNamesRegistered env key →
    source.ProjectionsCoherent env →
    schema.Fresh env key →
    schema.StructCompat env →
    VEnv.WF' ds (env.addEliminator key schema)
  | inductProjections {base envTypes envCtors : VEnv}
      {decl : VInductDecl} {block : VInductBlock} :
    VEnv.WF' baseDecls base →
    VEnv.WF' ds (envCtors.addEliminators block.eliminators) →
    (∃ key schema, block.eliminators = [(key, schema)] ∧
      schema.RegistrationCertificate base decl block key) →
    decl.sourceNames.Nodup →
    (∀ type ∈ decl.types, type.toVConstant.WF base) →
    (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) →
    (∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes) →
    decl.SourceParameterWF base →
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor) →
    block.types = decl.typeConstants →
    block.ctors = decl.constructorConstants →
    block.projections = decl.projectionEntries →
    base.addConstVals block.types = some envTypes →
    envTypes.addConstVals block.ctors = some envCtors →
    VEnv.WF' ds ((envCtors.addEliminators block.eliminators).addProjections block.projections)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

theorem VEnv.WF.inductEliminators {base env : VEnv}
    {source : VInductDecl} {block : VInductBlock}
    {schema : InductiveSignature.CaseSchema}
    (hbase : base.WF) (henv : env.WF) (hle : base ≤ env)
    (hreg : schema.RegistrationCertificate base source block key)
    (hconstants : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hequations : env.defeqs = base.defeqs)
    (hprojs : schema.ProjNamesRegistered env key)
    (hcoherent : source.ProjectionsCoherent env)
    (hfresh : schema.Fresh env key)
    (hcompat : schema.StructCompat env) :
    (env.addEliminator key schema).WF := by
  rcases hbase with ⟨baseDecls, hbase⟩
  rcases henv with ⟨ds, henv⟩
  exact ⟨ds, .inductEliminators hbase henv hle hreg hconstants hequations hprojs hcoherent
    hfresh hcompat⟩

/-- Register the projection table of one exact inductive prefix before its
recursors are installed.  Both the source base and the constructor-complete
environment retain independent declaration traces; the remaining premises
tie the new metadata to that precise prefix. -/
theorem VEnv.WF.inductProjections
    {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock}
    (hbase : base.WF) (hctorsWF : (envCtors.addEliminators block.eliminators).WF)
    (hcovered : ∃ key schema, block.eliminators = [(key, schema)] ∧
      schema.RegistrationCertificate base decl block key)
    (hsource : decl.sourceNames.Nodup)
    (htypesWF : ∀ type ∈ decl.types, type.toVConstant.WF base)
    (hconstructorUvars :
      ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (hctorsWF' : ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes)
    (hparams : decl.SourceParameterWF base)
    (hshape : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    ((envCtors.addEliminators block.eliminators).addProjections block.projections).WF := by
  rcases hbase with ⟨baseDecls, hbase⟩
  rcases hctorsWF with ⟨decls, hctorsWF⟩
  exact ⟨decls, .inductProjections hbase hctorsWF hcovered hsource htypesWF
    hconstructorUvars hctorsWF' hparams hshape htypesSource hctorsSource hprojections
    htypes hctors⟩
