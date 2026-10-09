import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.CompilationNames

/-! Certification and registration of case schemas (section 2.3 of
the design notes). A schema is certified by the case part of the same finite
compilation certificate that inductive installation uses (`Certified`,
`RegistrationCertificate`); no case types or equations are supplied by a caller.

Registration additionally certifies `CaseSchema.ProjNamesRegistered`: the
schema's generic type and generic equations project only out of structures
registered (as projections) in the environment at registration time. This is
an obligation on whoever constructs a registration (`VEnv.WF'.inductEliminators`),
not a consequence of `Certified`: the normalized index telescopes and recursive
shapes are checked in the expanded environment, whose projection table may
contain never-installed auxiliary structure families. -/

namespace Lean4Lean

namespace VExpr

/-- Every projection type name of the term satisfies `ok`. -/
def ProjNamesOK (ok : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ | .const .. | .elim .. => True
  | .app f a | .lam f a | .forallE f a => f.ProjNamesOK ok ∧ a.ProjNamesOK ok
  | .proj n _ e => ok n ∧ e.ProjNamesOK ok

theorem ProjNamesOK.mono {ok ok' : Name → Prop} (hok : ∀ s, ok s → ok' s) :
    ∀ {e : VExpr}, e.ProjNamesOK ok → e.ProjNamesOK ok'
  | .bvar _, _ | .sort _, _ | .const .., _ | .elim .., _ => trivial
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => ⟨ProjNamesOK.mono hok h.1, ProjNamesOK.mono hok h.2⟩
  | .proj _ _ _, h => ⟨hok _ h.1, ProjNamesOK.mono hok h.2⟩

theorem ProjNamesOK.liftN {ok : Name → Prop} {n : Nat} :
    ∀ {e : VExpr} {k : Nat}, e.ProjNamesOK ok → (e.liftN n k).ProjNamesOK ok
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .elim .., _, _ => trivial
  | .app _ _, _, h => ⟨ProjNamesOK.liftN h.1, ProjNamesOK.liftN h.2⟩
  | .lam _ _, _, h => ⟨ProjNamesOK.liftN h.1, ProjNamesOK.liftN h.2⟩
  | .forallE _ _, _, h => ⟨ProjNamesOK.liftN h.1, ProjNamesOK.liftN h.2⟩
  | .proj _ _ _, _, h => ⟨h.1, ProjNamesOK.liftN h.2⟩

end VExpr

namespace InductiveSignature.CaseSchema

/-- The generic type and generic equations (at registry key `key`) of the
schema project only out of structures registered in `env`. -/
def ProjNamesRegistered (schema : CaseSchema) (env : VEnv) (key : Name) : Prop :=
  (∀ owner type, schema.genericType owner = some type →
    type.ProjNamesOK fun S => ∃ info, env.projections S info) ∧
  (∀ owner rules, schema.genericEquations key owner = some rules → ∀ df ∈ rules,
    df.lhs.ProjNamesOK (fun S => ∃ info, env.projections S info) ∧
    df.rhs.ProjNamesOK (fun S => ∃ info, env.projections S info) ∧
    df.type.ProjNamesOK (fun S => ∃ info, env.projections S info))

/-- Registration of projections is monotone along environment extension. -/
theorem ProjNamesRegistered.mono {schema : CaseSchema} {env env' : VEnv}
    (H : schema.ProjNamesRegistered env key) (hle : env ≤ env') :
    schema.ProjNamesRegistered env' key := by
  have hok : ∀ S, (∃ info, env.projections S info) → ∃ info, env'.projections S info :=
    fun _ ⟨info, h⟩ => ⟨info, hle.projections h⟩
  refine ⟨fun owner type h => (H.1 owner type h).mono hok, fun owner rules h df hdf => ?_⟩
  obtain ⟨hl, hr, ht⟩ := H.2 owner rules h df hdf
  exact ⟨hl.mono hok, hr.mono hok, ht.mono hok⟩

/-- Every structure registered in `env` that is a source family of the
schema (at source slot `owner`) has, in the schema, exactly its registered
constructor. Without this, a schema could add constructors to a registered
structure, and structure eta (`unitLike`) would identify the extra
constructors with the registered one (see `SchemaStructCompat`). -/
def StructCompat (schema : CaseSchema) (env : VEnv) : Prop :=
  ∀ {s : Name} {info : VProjectionInfo}, env.projections s info →
    ∀ owner : Fin schema.signature.families.size,
      schema.sourceFamilies[owner.val]? = some s →
      (schema.view owner).constructors.toList.map (·.name) = [info.ctorName]

/-- Compatibility is antitone in the projection table. -/
theorem StructCompat.of_projections {schema : CaseSchema} {env env' : VEnv}
    (H : schema.StructCompat env')
    (hproj : ∀ {s info}, env.projections s info → env'.projections s info) :
    schema.StructCompat env :=
  fun hinfo owner hname => H (hproj hinfo) owner hname

/-- The abstract registry entry is determined by the same normalized
signature and restoration data as the generated recursors of the installed block. -/
def ofCompilation (source : VInductDecl) (signature : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) : CaseSchema where
  sourceFamilies := source.types.map (·.name)
  signature := signature
  restoration := compilationRestoration source auxiliaries

/-- Retain the normalized signature and exact restoration of one finite
compilation. Concrete recursor checking is not needed to register its abstract
case schemas once the source constructors and expanded formation are checked:
the certificate is the case part `CaseCompilationData` of a compilation, which
fixes everything the eliminator rules read and nothing about the generated
recursors. -/
def Certified (schema : CaseSchema) (base : VEnv)
    (source : VInductDecl) (block : VInductBlock) : Prop :=
  ∃ expanded, ∃ auxiliaries,
    CaseCompilationData base source expanded schema.signature auxiliaries block ∧
    ContainersInstalled base auxiliaries ∧
    schema.restoration = compilationRestoration source auxiliaries ∧
    schema.sourceFamilies = source.types.map (·.name) ∧
    RecursorNamesFresh base source expanded auxiliaries

/-- The family index domains of the signature restore, and the declared header of every source
family is, in the environment with the declaration's family headers, its restored normalized
header. Registration requires this (`VEnv.WF'.inductEliminators`): the restored case type of an
indexed family needs restored index domains, and the case eliminator of an indexed structure
needs its index telescope to agree with the declared one. -/
def HeaderAgreement (schema : CaseSchema) (base : VEnv) (source : VInductDecl) : Prop :=
  ∃ RP, schema.signature.params.mapM schema.restoration.expr = some RP ∧
    ∀ owner : Fin schema.signature.families.size,
      ∃ RI, schema.signature.families[owner].indices.mapM schema.restoration.expr = some RI ∧
        ∀ type ∈ source.types, type.name = schema.signature.families[owner].name →
          ∃ envTypes, base.addConstVals source.typeConstants = some envTypes ∧
            envTypes.IsDefEqU source.uvars [] type.type
              (VExpr.wrapForalls (RP ++ RI) (.sort schema.signature.families[owner].resultLevel))

/-- **The registration certificate of a case schema.** The schema is certified by the case part
of a compilation of `source` with block `block` over `base` (`Certified`), it is registered under
the key of the first source family, and the declared header of every source family is its
restored normalized header (`HeaderAgreement`). Every registration point
(`VEnv.WF'.inductEliminators`, `VEnv.WF'.inductProjections`, `VInductBlock.EliminatorsWF`)
carries exactly this certificate. -/
structure RegistrationCertificate (schema : CaseSchema) (base : VEnv) (source : VInductDecl)
    (block : VInductBlock) (key : Name) : Prop where
  certified : schema.Certified base source block
  keyHead : source.types.head?.map (·.name) = some key
  headerAgreement : schema.HeaderAgreement base source

/-- The key is fresh and the source families are disjoint from those of every registered
schema. Auxiliary families reserve no names: they are identified by their block and owner
slot. -/
def Fresh (schema : CaseSchema) (env : VEnv) (key : Name) : Prop :=
  (∀ previous, ¬env.eliminators key previous) ∧
  ∀ previousKey previous, env.eliminators previousKey previous →
    List.Disjoint schema.sourceFamilies previous.sourceFamilies

theorem ofCaseCompilation_certified {s : InductiveSignature}
    (H : CaseCompilationData base source expanded s auxiliaries block)
    (hprior : ContainersInstalled base auxiliaries)
    (hdisj : RecursorNamesFresh base source expanded auxiliaries) :
    (ofCompilation source s auxiliaries).Certified base source block :=
  ⟨expanded, auxiliaries, H, hprior, rfl, rfl, hdisj⟩

end InductiveSignature.CaseSchema

end Lean4Lean
