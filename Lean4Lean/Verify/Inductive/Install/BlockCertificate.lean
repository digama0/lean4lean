import Lean4Lean.Verify.Inductive.Recursor.Check

/-! The block installation (`BlockInstallation`: headers, constructors, case
eliminators, projections and recursors, in the order of `VInductBlock.install`)
and the block certificate (`BlockCertificate`) shared by the ordinary,
primitive and nested paths.  From a block certificate the file derives
`AddInduct`, its replay in larger safety models, and the safety-indexed
extension of the environment model for safe and unsafe blocks ("Assembly" in
section 3.2 of the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Installation certificate matching the executable order: mutual headers,
constructors, then recursors.  Header and constructor installation may be
ordinary (one validated constant at a time) or an atomic primitive batch; see
`FormationInstallation`.  Between the constructors and the recursors
the abstract environment registers the block's case eliminators and then its
projections (`VInductBlock.install`); both are abstract-only, so the
kernel environment is unchanged there.  Recursors are always added to the
constructor environment one validated constant at a time (`AddConstants`).
Reduction equations are not included here because their
validity depends on the independent iota schema. -/
structure BlockInstallation (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (projections : List VProjectionEntry)
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  formation : FormationInstallation safety env venv types
    envTypes venvTypes ctors envCtors venvCtors
  eliminators : List (Name × InductiveSignature.CaseSchema)
  casesWF : (venvCtors.addEliminators eliminators).WF
  projectedWF : ((venvCtors.addEliminators eliminators).addProjections projections).WF
  recursorsAdded : AddConstants safety envCtors
    ((venvCtors.addEliminators eliminators).addProjections projections) recursors
    outEnv outVEnv

def BlockInstallation.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : BlockInstallation checkSafety env venv types ctors recursors projections
      outEnv outVEnv) :
    BlockInstallation safety env venv types ctors recursors projections
      outEnv outVEnv where
  envTypes := H.envTypes
  venvTypes := H.venvTypes
  envCtors := H.envCtors
  venvCtors := H.venvCtors
  formation := H.formation.sf_mono hsafety
  eliminators := H.eliminators
  casesWF := H.casesWF
  projectedWF := H.projectedWF
  recursorsAdded := H.recursorsAdded.sf_mono hsafety

theorem BlockInstallation.abstract_types
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    venv.addConstVals (types.map Prod.snd) = some H.venvTypes :=
  H.formation.headerAbstract

theorem BlockInstallation.abstract_ctors
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    H.venvTypes.addConstVals (ctors.map Prod.snd) = some H.venvCtors :=
  H.formation.constructorAbstract

theorem BlockInstallation.abstract_recursors
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    ((H.venvCtors.addEliminators H.eliminators).addProjections projections).addConstVals
      (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

/-- Collapse the formation prefix and the recursor suffix into one atomic
installation of the whole block. This needs no validity judgment for a
primitive header prefix. -/
theorem BlockInstallation.atomic
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    AtomicAddConstants safety env
      ((venv.addEliminators H.eliminators).addProjections projections) (types ++ ctors ++ recursors)
      outEnv outVEnv := by
  have Hformation' : AtomicAddConstants safety env
      ((venv.addEliminators H.eliminators).addProjections projections) (types ++ ctors) H.envCtors
      ((H.venvCtors.addEliminators H.eliminators).addProjections projections) := by
    exact H.formation.atomic.addEliminators.addProjections
  simpa [List.append_assoc] using
    Hformation'.append
      (AtomicAddConstants.ofAddConstants H.recursorsAdded)

theorem BlockInstallation.quotInit_eq
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) : outEnv.quotInit = env.quotInit :=
  H.recursorsAdded.quotInit_eq.trans H.formation.quotInit_eq

/-- The block installation preserves the local checking invariants. -/
theorem BlockInstallation.validCore
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv)
    (hvalid : CheckingEnv.ValidCore safety env venv) :
    CheckingEnv.ValidCore safety outEnv outVEnv :=
  H.recursorsAdded.validCore
    (((H.formation.validCore hvalid).addEliminators H.casesWF).addProjections
      H.projectedWF)

/-- The block installation adds no stored equation. -/
theorem BlockInstallation.defeqs
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    ∀ df, outVEnv.defeqs df → venv.defeqs df := by
  intro df hdf
  have h1 := H.recursorsAdded.defeqs df hdf
  rw [VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs] at h1
  exact H.formation.atomic.defeqs df h1

theorem BlockInstallation.le
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv) :
    venv ≤ outVEnv :=
  H.formation.atomic.le.trans
    (VEnv.addEliminators_addProjections_le.trans H.recursorsAdded.le)

theorem BlockInstallation.aligned
    (H : BlockInstallation checkSafety env venv types ctors recursors
      projections outEnv outVEnv)
    (Halign : Aligned checkSafety env.constants venv) :
    Aligned checkSafety outEnv.constants outVEnv :=
  H.atomic.aligned (.projections (Aligned.addEliminators Halign))

theorem BlockInstallation.trEnvIgnore
    (H : BlockInstallation checkSafety prodEnv venv types ctors recursors
      projections outEnv outVEnv)
    (htypes : ∀ entry ∈ types, ¬ observerSafety ≤ entry.1.safety)
    (hctors : ∀ entry ∈ ctors, ¬ observerSafety ≤ entry.1.safety)
    (hrecursors : ∀ entry ∈ recursors,
      ¬ observerSafety ≤ entry.1.safety)
    (htr : TrEnv' observerSafety prodEnv.constants quotInit observerEnv) :
    TrEnv' observerSafety outEnv.constants quotInit observerEnv := by
  apply H.recursorsAdded.trEnvIgnore hrecursors
  apply H.formation.atomic.trEnvIgnore _ htr
  intro entry hentry
  rcases List.mem_append.mp hentry with htype | hctor
  · exact htypes entry htype
  · exact hctors entry hctor

theorem BlockInstallation.deltaConservative
    (H : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv)
    (Halign : Aligned safety env.constants venv) :
    ∀ {name ci}, outEnv.constants.find? name = some ci →
      ci.deltaValue?.isSome → env.constants.find? name = some ci :=
  H.atomic.deltaConservative (.projections (Aligned.addEliminators Halign))

/-- The complete semantic certificate for the block assembled by the three
executable installation stages, whose formation prefix may be ordinary or an
atomic primitive batch.  The installation records the per-step checking
environment; the `*WF` fields deliberately record the stronger stage-wide
facts required by the independent `VInductBlock.WF` specification.  This
distinction matters for mutual declarations: typing a later header only after
installing an earlier sibling would not establish formation of the mutual
block.  Well-formedness depends only on the three abstract `addConstVals`
equations, never on partial-batch validity. -/
structure BlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  projections : List VProjectionEntry
  installation : BlockInstallation safety env venv types ctors recursors
    projections outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF installation.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF ((installation.venvCtors.addEliminators installation.eliminators).addProjections
      projections)
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

def BlockCertificate.sf_mono
    (hsafety : safety ≤ checkSafety)
    (H : BlockCertificate checkSafety env venv types ctors recursors
      rules outEnv outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  projections := H.projections
  installation := H.installation.sf_mono hsafety
  typesWF := H.typesWF
  ctorsWF := H.ctorsWF
  recursorsWF := H.recursorsWF
  rulesWF := H.rulesWF

def BlockCertificate.block
    (_H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules
  projections := _H.projections
  eliminators := _H.installation.eliminators

/-- The header environment of a certified block is below its installed environment. -/
theorem BlockCertificate.typesLe
    (H : BlockCertificate safety env venv types ctors recursors rules outEnv outVEnv)
    (htypes : venv.addConstVals (types.map Prod.snd) = some venvH) :
    venvH ≤ (outVEnv.addDefEqRules rules) := by
  rw [H.installation.abstract_types] at htypes
  cases htypes
  exact (VEnv.addConstVals_le H.installation.abstract_ctors).trans
    (VEnv.addEliminators_addProjections_le.trans
      (H.installation.recursorsAdded.le.trans VEnv.addDefEqRules_le))

theorem BlockCertificate.block_eq_of_projections_eq
    (H₁ : BlockCertificate safety₁ env₁ venv₁ types ctors recursors
      rules outEnv₁ outVEnv₁)
    (H₂ : BlockCertificate safety₂ env₂ venv₂ types ctors recursors
      rules outEnv₂ outVEnv₂)
    (h : H₁.projections = H₂.projections)
    (he : H₁.installation.eliminators = H₂.installation.eliminators) : H₁.block = H₂.block := by
  simp [BlockCertificate.block, h, he]

theorem BlockCertificate.wf
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.installation.venvTypes, H.installation.venvCtors,
    outVEnv,
    H.installation.abstract_types, H.installation.abstract_ctors,
    H.installation.abstract_recursors, H.typesWF, H.ctorsWF,
    H.recursorsWF, H.rulesWF⟩

theorem BlockCertificate.install
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some (outVEnv.addDefEqRules rules) := by
  simp [BlockCertificate.block, VInductBlock.install,
    H.installation.abstract_types, H.installation.abstract_ctors,
    H.installation.abstract_recursors]

theorem BlockCertificate.names
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    List.Nodup
      ((H.block.types ++ H.block.ctors ++ H.block.recursors).map
        (·.name)) := by
  have hall : ((venv.addEliminators H.installation.eliminators).addProjections H.projections).addConstVals
      (types.map Prod.snd ++ ctors.map Prod.snd ++ recursors.map Prod.snd) =
      some outVEnv := by
    simpa [List.map_append, List.append_assoc] using
      H.installation.atomic.abstract
  simpa [BlockCertificate.block, List.map_append] using
    VEnv.addConstVals_names_nodup hall

/-- Replay a certified block in a larger abstract source model.  Formation is
replayed with `FormationInstallation.rebase`, so the atomic primitive case
never requires a valid header-only environment. -/
theorem BlockCertificate.rebaseCertificate
    {decl : VInductDecl}
    (H : BlockCertificate checkSafety prodEnv base types ctors
      recursors rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety <= checkSafety)
    (hbase : base <= largerBase)
    (Hdecl : decl.WF base)
    (Hcompile : decl.CompilesTo base H.block)
    (Hreplay : VInductBlock.EliminatorsReplay largerBase decl H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : BlockCertificate safety prodEnv largerBase types
        ctors recursors rules outEnv largerOutBase,
      outBase ≤ largerOutBase ∧ Hlarger.projections = H.projections ∧
        Hlarger.installation.eliminators = H.installation.eliminators := by
  rcases H.installation.formation.rebase Hvalid.tr hsafety hbase with
    ⟨largerTypes, largerCtors, ⟨Hformation⟩, htypes, hctors⟩
  have HcheckingCtors : CheckingEnv safety H.installation.envCtors largerCtors :=
    Hformation.checking Hvalid.tr
  have htypes' : largerBase.addConstVals decl.typeConstants = some largerTypes := by
    rw [← Hcompile.types]
    exact Hformation.headerAbstract
  have hctors' : largerTypes.addConstVals decl.constructorConstants = some largerCtors := by
    rw [← Hcompile.ctors]
    exact Hformation.constructorAbstract
  have Hcases := Hreplay _ _ htypes' hctors'
  have hcasesWF : (largerCtors.addEliminators H.installation.eliminators).WF :=
    Hcases.elimWF Hvalid.tr.wf (Hdecl.1.mono_of_addConstVals hbase htypes' hctors')
      Hcompile.types Hcompile.ctors Hformation.headerAbstract Hformation.constructorAbstract
  have hprojectedWF :
      ((largerCtors.addEliminators H.installation.eliminators).addProjections H.projections).WF := by
    obtain ⟨_, _, _, _, hc⟩ := Hcases
    rcases hc with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, _⟩
    · have hP' : H.projections = [] :=
        Hcompile.projections.trans (VInductDecl.projectionEntries_eq_nil hT)
      have hcasesWF' := hcasesWF
      generalize H.installation.eliminators = es at hcasesWF' ⊢
      rw [hP']
      exact hcasesWF'
    apply VEnv.WF.inductProjections
        (base := largerBase) (envTypes := largerTypes)
        (decl := decl) (block := H.block)
    · exact Hvalid.tr.wf
    · exact hcasesWF
    · exact ⟨key, schema, hE, hreg⟩
    · exact Hcompile.sourceNames
    · exact fun type member => (Hdecl.1.sourceTypes type member).mono hbase
    · exact Hdecl.1.2.2.2.1
    · rcases Hdecl.1.sourceConstructors with ⟨baseTypes, hbaseTypes, hwf⟩
      have hle : baseTypes ≤ largerTypes :=
        VEnv.addConstVals_mono hbase hbaseTypes htypes'
      exact fun ctor hctor => (hwf ctor hctor).mono hle
    · rcases Hdecl.1.sourceConstructors with ⟨baseTypes, hbaseTypes, _⟩
      exact (Hdecl.sourceParameterWF hbaseTypes).mono_of_addConstVals hbase htypes'
    · rcases Hdecl.1.sourceConstructors with ⟨baseTypes, hbaseTypes, _⟩
      exact (Hdecl.sourceParameterWF hbaseTypes).rawCtorShape
    · exact Hcompile.types
    · exact Hcompile.ctors
    · exact Hcompile.projections
    · exact Hformation.headerAbstract
    · exact Hformation.constructorAbstract
  have HcheckingProjected : CheckingEnv safety H.installation.envCtors
      ((largerCtors.addEliminators H.installation.eliminators).addProjections H.projections) :=
    (HcheckingCtors.addEliminators hcasesWF).addProjections hprojectedWF
  have hctorsProjected :
      (H.installation.venvCtors.addEliminators H.installation.eliminators).addProjections H.projections ≤
        (largerCtors.addEliminators H.installation.eliminators).addProjections H.projections :=
    VEnv.addProjections_mono (VEnv.addEliminators_mono hctors)
  rcases H.installation.recursorsAdded.rebase HcheckingProjected hsafety
      hctorsProjected with ⟨largerOutBase, Hrecursors, hout⟩
  let Hlarger : BlockCertificate safety prodEnv largerBase types
      ctors recursors rules outEnv largerOutBase := {
    projections := H.projections
    installation := {
      envTypes := H.installation.envTypes
      venvTypes := largerTypes
      envCtors := H.installation.envCtors
      venvCtors := largerCtors
      formation := Hformation
      eliminators := H.installation.eliminators
      casesWF := hcasesWF
      projectedWF := hprojectedWF
      recursorsAdded := Hrecursors }
    typesWF := fun ci hci => (H.typesWF ci hci).mono hbase
    ctorsWF := fun ci hci => (H.ctorsWF ci hci).mono htypes
    recursorsWF := fun ci hci =>
      (H.recursorsWF ci hci).mono hctorsProjected
    rulesWF := fun df hdf => (H.rulesWF df hdf).mono hout }
  exact ⟨largerOutBase, Hlarger, hout, rfl, rfl⟩

/-- The executable installation of a certified block satisfies `AddInduct`.
Whole-block alignment and delta conservation use the atomic installation
(`BlockInstallation.atomic`), which is valid for ordinary and primitive
formation alike. -/
theorem BlockCertificate.addInduct
    (H : BlockCertificate checkSafety prodEnv venv types ctors
      recursors rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      venv outEnv.constants (outVEnv.addDefEqRules rules))
    (hsourceAligned : Aligned checkSafety prodEnv.constants venv)
    (helim : VInductBlock.EliminatorsWF venv decl H.block) :
    AddInduct checkSafety prodEnv.constants venv decl outEnv.constants
      (outVEnv.addDefEqRules rules) := by
  apply AddInduct.intro H.block hdecl hcompile H.wf H.install
  · intro name ci hfind
    have hfindEnv : prodEnv.find? name = some ci := by
      rw [Lean.Kernel.Environment.find?,
        hsourceAligned.map_wf.find?'_eq_find?]
      exact hfind
    have hout := H.installation.atomic.preservesSourceFind
      hsourceAligned.map_wf hfindEnv
    have houtWF := H.installation.atomic.targetMapWF
      hsourceAligned.map_wf
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hout
    exact hout
  · intro Haligned
    exact aligned_addDefEqs
      (H.installation.atomic.aligned (.projections (Aligned.addEliminators Haligned))) rules
  · exact H.installation.atomic.deltaConservative
      (.projections (Aligned.addEliminators hsourceAligned))
  · exact hprovenance.ofUnsafe
  · exact helim

/-- Replay a safe certified block into one observer model and prove the
corresponding concrete `AddInduct`. -/
theorem BlockCertificate.rebaseAddInductSafe
    (H : BlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid targetSafety prodEnv largerBase)
    (hbase : base <= largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      base outEnv.constants (outBase.addDefEqRules rules))
    (Hreplay : VInductBlock.EliminatorsReplay largerBase decl H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : BlockCertificate targetSafety prodEnv largerBase
        types ctors recursors rules outEnv largerOutBase,
      AddInduct targetSafety prodEnv.constants largerBase decl outEnv.constants
        (largerOutBase.addDefEqRules rules) ∧
      (outBase.addDefEqRules rules) ≤
        (largerOutBase.addDefEqRules rules) ∧
      Hlarger.projections = H.projections ∧
      Hlarger.installation.eliminators = H.installation.eliminators := by
  rcases H.rebaseCertificate Hvalid DefinitionSafety.le_safe hbase hdecl
      hcompile Hreplay with
    ⟨largerOutBase, Hlarger, houtBase, hprojections, heliminators⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hblock := Hlarger.block_eq_of_projections_eq H hprojections heliminators
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    by
      rw [← hblock] at hcompile
      exact hcompile.mono hbase Hlarger.wf
  have helimLarger : VInductBlock.EliminatorsWF largerBase decl Hlarger.block :=
    (Hreplay.congr_block hblock).eliminatorsWF hdeclLarger.1
  have hprovenanceLarger := hprovenance.rebaseBlock hbase
    (VEnv.addDefEqRules_mono houtBase) H.install Hlarger.install rfl
  have hadd : AddInduct targetSafety prodEnv.constants largerBase decl
      outEnv.constants
        (largerOutBase.addDefEqRules rules) := by
    simpa [hprojections] using
      Hlarger.addInduct hdeclLarger hcompileLarger hprovenanceLarger Hvalid.tr.aligned
        helimLarger
  exact ⟨largerOutBase, Hlarger, hadd,
    VEnv.addDefEqRules_mono houtBase, hprojections, heliminators⟩

theorem BlockCertificate.hasPrimitives
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hprimitives : venv.HasPrimitives) :
    (outVEnv.addDefEqRules rules).HasPrimitives := by
  apply hasPrimitives_addDefEqs
  exact H.installation.recursorsAdded.hasPrimitives
    (H.installation.formation.hasPrimitives Hprimitives).addEliminators.addProjections

/-- The block installation preserves `CheckingEnv.ValidCore`, for ordinary and
primitive formation alike.  The well-formedness of the projection stage is a
field of the installation, so callers do not have to reconstruct it from a
separate compilation certificate. -/
theorem BlockCertificate.validCore
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv)
    (Hvalid : CheckingEnv.ValidCore safety env venv) :
    CheckingEnv.ValidCore safety outEnv outVEnv :=
  H.installation.validCore Hvalid

/-- Replay a complete inductive refinement in a larger safety-indexed model.
The fresh block supplies the source-installation facts that plain weakening
cannot preserve, while source well-formedness and compilation semantics are
transported from the source model. -/
theorem BlockCertificate.rebaseAddInduct
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hvalid : CheckingEnv.Valid safety prodEnv largerBase)
    (hsafety : safety ≤ checkSafety)
    (hbase : base ≤ largerBase)
    (hdecl : decl.WF base)
    (hcompile : decl.CompilesTo base H.block)
    (Hreplay : VInductBlock.EliminatorsReplay largerBase decl H.block) :
    ∃ largerOutBase,
      ∃ Hlarger : BlockCertificate safety prodEnv largerBase types ctors
        recursors rules outEnv largerOutBase,
      Hlarger.projections = H.projections ∧
      VEnv.AddInduct largerBase decl (largerOutBase.addDefEqRules rules) ∧
      (outBase.addDefEqRules rules) ≤ (largerOutBase.addDefEqRules rules) ∧
      Hlarger.installation.eliminators = H.installation.eliminators := by
  rcases H.rebaseCertificate Hvalid hsafety hbase hdecl hcompile Hreplay with
    ⟨largerOutBase, Hlarger, houtBase, hprojections, heliminators⟩
  have hdeclLarger : decl.WF largerBase :=
    VInductDecl.WF.rebaseOfBlock hdecl hbase Hlarger.wf
      hcompile.types hcompile.ctors
  have hblock := Hlarger.block_eq_of_projections_eq H hprojections heliminators
  have hcompileLarger : decl.CompilesTo largerBase Hlarger.block :=
    by
      rw [← hblock] at hcompile
      exact hcompile.mono hbase Hlarger.wf
  have helimLarger : VInductBlock.EliminatorsWF largerBase decl Hlarger.block :=
    (Hreplay.congr_block hblock).eliminatorsWF hdeclLarger.1
  refine ⟨largerOutBase, Hlarger, hprojections, ?_, ?_, heliminators⟩
  · simpa [hprojections] using
      VEnv.AddInduct.intro hdeclLarger hcompileLarger Hlarger.wf helimLarger Hlarger.install
  · exact VEnv.addDefEqRules_mono houtBase

/-- Every new constant of a certified block installation carries the batch's `isUnsafe`. -/
theorem BlockCertificate.newUnsafe
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors rules outEnv outBase)
    (hwf : prodEnv.constants.WF)
    (hb : ∀ e ∈ types ++ ctors ++ recursors, e.1.isUnsafe = b)
    (hfind : outEnv.find? n = some ci) (hnone : prodEnv.find? n = none) : ci.isUnsafe = b := by
  rcases H.installation.atomic.entryOrigin hwf hfind with hold | ⟨e, he, -, rfl⟩
  · rw [hold] at hnone; cases hnone
  · exact hb e he

/-- Every entry of a block certified at `.safe` is safe. -/
theorem BlockCertificate.entriesSafe
    (H : BlockCertificate .safe prodEnv base types ctors recursors rules outEnv outBase) :
    ∀ e ∈ types ++ ctors ++ recursors, e.1.isUnsafe = false := by
  rintro ⟨info, value⟩ he
  have hs := H.installation.atomic.entrySafety he
  cases h : info.isUnsafe
  · rfl
  · simp [ConstantInfo.safety, h] at hs
    exact absurd hs (by decide)

/-- The declaration of a certified block has the `isUnsafe` of its new headers. -/
theorem BlockCertificate.declUnsafe {decl : VInductDecl}
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors rules outEnv outBase)
    (hwf : prodEnv.constants.WF) (houtWF : outEnv.constants.WF)
    (hb : ∀ e ∈ types ++ ctors ++ recursors, e.1.isUnsafe = b)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ prodEnv.find? T.name = none)
    (hnonempty : decl.types ≠ []) : decl.isUnsafe = b := by
  exact horigins.declUnsafe hwf houtWF hcover hnonempty fun hv hnone => by
    simpa [ConstantInfo.isUnsafe] using H.newUnsafe hwf hb hv hnone

/-- The block invariant at one observer after the installation of a certified block: the
source blocks, together with the complete descriptor of the new block
(`InstalledBlocks.addInduct`). -/
theorem BlockCertificate.installedBlocks {decl : VInductDecl} {venvH : VEnv}
    (H : BlockCertificate checkSafety prodEnv base types ctors recursors rules outEnv outBase)
    (Hsource : InstalledBlocks safety prodEnv venv .complete)
    (hwf : prodEnv.constants.WF) (hchk' : CheckingEnv safety outEnv venv')
    (hle : venv ≤ venv')
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants decl)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ prodEnv.find? T.name = none)
    (hclosed : MutualInductivesClosed outEnv)
    (howners : ConstructorOwnersPresent outEnv)
    (hb : ∀ e ∈ types ++ ctors ++ recursors, e.1.isUnsafe = decl.isUnsafe)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants b₁ outEnv.constants b₂)
    (hadd : safety ≤ (if decl.isUnsafe then .unsafe else .safe) →
      AddInduct safety prodEnv.constants venv decl outEnv.constants venv')
    (hhidden : ¬ safety ≤ (if decl.isUnsafe then .unsafe else .safe) → venv' = venv)
    (hparams : safety ≤ (if decl.isUnsafe then .unsafe else .safe) →
      ConstructorParameterAlignment safety outEnv venv')
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      prodEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt venvH ci))
    (hH : safety ≤ (if decl.isUnsafe then .unsafe else .safe) → venvH ≤ venv') :
    InstalledBlocks safety outEnv venv' .complete := by
  have houtWF : outEnv.constants.WF := hchk'.map_wf
  refine Hsource.addInduct hwf hchk' (H.installation.atomic.preservesSourceFind hwf) hle
    horigins hcover hclosed howners ?_ hadd hhidden hparams ?_ ?_
  · intro n r hf hnone
    have hfMap : outEnv.constants.find? n = some (.recInfo r) := by
      rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hf
    rcases hprovenance.recursor hfMap with hold | hnew
    · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
    · obtain ⟨-, -, info, hmajor⟩ := hnew DefinitionSafety.unsafe_le
      exact ⟨info, by rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]⟩
  · intro hvis n c hf hnone
    rcases hctorOrigin hf with hold | ⟨-, htel⟩
    · rw [hold] at hnone; cases hnone
    · exact htel.mono (hH hvis)
  · intro n r hf hnone hrvis
    have hrU : r.isUnsafe = decl.isUnsafe := by
      simpa [ConstantInfo.isUnsafe] using H.newUnsafe hwf hb hf hnone
    have hvis : safety ≤ (if decl.isUnsafe then .unsafe else .safe) := by
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hrU] using hrvis
    have hfMap : outEnv.constants.find? n = some (.recInfo r) := by
      rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hf
    rcases (hadd hvis).newRecursorsAligned.recursor hfMap with hold | hnew
    · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
    · obtain ⟨hcore, hk, -⟩ := hnew hrvis
      exact ⟨hcore, hk⟩

/-- Lift one unsafe block installation to the three safety-indexed abstract
environments.  The partial and safe translations come from ignoring the newly
installed unsafe kernel constants. -/
theorem BlockCertificate.extendUnsafeExact
    {ves : VEnvs}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WF prodEnv)
    (htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      (outVEnv.addDefEqRules rules))
    (htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial))
    (htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe))
    (hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hblocks : ∀ safety, InstalledBlocks safety outEnv
        (match safety with
        | .unsafe => (outVEnv.addDefEqRules rules)
        | .partial => ves.venv .partial
        | .safe => ves.venv .safe) .complete) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      ves'.venv .unsafe = (outVEnv.addDefEqRules rules) := by
  apply Lean4Lean.VEnvs.WF.extendUnsafeExact wf
    (outVEnv.addDefEqRules rules)
    htrUnsafe htrPartial htrSafe
  · exact H.hasPrimitives wf.hasPrimitives
  · exact hsafePrimitives
  · exact hblocks
  · exact VInductBlock.install_le H.install

/-- Reconstruct constructor semantics for one replay of a safe block.  Base
families are transported from the corresponding source safety model.  A new
family is necessarily safe because the certified batch was checked at
`.safe`, so its constructor typing in the installed environment transports
along the replay monotonicity `hreplay`. -/
theorem BlockCertificate.replaySafeConstructorTyping
    (H : BlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hreplay : BlockCertificate observer prodEnv observerBase types ctors
      recursors rules outEnv replayBase)
    (hwf : prodEnv.constants.WF)
    (Hsource : ConstructorParameterAlignment
      observer prodEnv observerBase)
    (Hcompleted : ConstructorParameterAlignment .safe outEnv
      (outBase.addDefEqRules rules))
    (hreplay : (outBase.addDefEqRules rules) ≤ (replayBase.addDefEqRules rules)) :
    ConstructorParameterAlignment observer outEnv
      (replayBase.addDefEqRules rules) := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := Hreplay.installation.atomic
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    have hlookup := Hinstall.preservesSourceFind hwf C.lookup
    have hle : observerBase ≤ (replayBase.addDefEqRules rules) :=
      VEnv.addEliminators_addProjections_le.trans (Hinstall.le.trans VEnv.addDefEqRules_le)
    exact ⟨C.rebaseKernel hlookup hle⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    have hsafe : .safe ≤ (ConstantInfo.inductInfo familyInfo).safety := by
      rw [hinfo]
      exact H.installation.atomic.entrySafety hentry
    have hsafe' : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hsafe
    have hfamilySafe : familyInfo.isUnsafe = false := by
      cases h : familyInfo.isUnsafe
      · rfl
      · have hsafeUnsafe : DefinitionSafety.safe ≤
            DefinitionSafety.unsafe := by simpa [h] using hsafe'
        have heq : DefinitionSafety.safe = DefinitionSafety.unsafe :=
          DefinitionSafety.le_antisymm hsafeUnsafe DefinitionSafety.unsafe_le
        contradiction
    have hsafeVisible : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simp [hfamilySafe]
    rcases Hcompleted familyName familyInfo hfamily hsafeVisible i hi with ⟨C⟩
    exact ⟨C.mono hreplay⟩

/-- A safe executable block, ordinary or primitive, extends all three abstract
safety models.  Each model is replayed independently, while monotonicity of
the resulting family is recovered from the shared abstract block
installation.  For a primitive Bool/Nat block `HasPrimitives` is restored only
at the complete formation batch (`FormationInstallation.hasPrimitives`). -/
theorem BlockCertificate.extendSafeExact
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      (ves.venv .safe) outEnv.constants (outBase.addDefEqRules rules))
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .safe outEnv
        (outBase.addDefEqRules rules))
    (Hreplay : ∀ safety, VInductBlock.EliminatorsReplay (ves.venv safety) decl H.block)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ prodEnv.find? T.name = none)
    {isUnsafe : Bool} {venvH : VEnv}
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      prodEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt venvH ci))
    (hH : venvH ≤ (outBase.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) ∧
      (outBase.addDefEqRules rules) ≤ ves'.venv .safe := by
  have valid (safety : DefinitionSafety) :
      CheckingEnv.Valid safety prodEnv (ves.venv safety) :=
    wf.toCheckingValid (safety)
  rcases H.rebaseAddInductSafe (valid .unsafe)
      (wf.mono DefinitionSafety.unsafe_le) hdecl hcompile hprovenance
      (Hreplay .unsafe) with
    ⟨unsafeBase, Hunsafe, HunsafeAdd, hunsafeLE, hunsafeProj, hunsafeElim⟩
  rcases H.rebaseAddInductSafe (valid .partial)
      (wf.mono DefinitionSafety.le_safe) hdecl hcompile hprovenance
      (Hreplay .partial) with
    ⟨partialBase, Hpartial, HpartialAdd, hpartialLE, hpartialProj, hpartialElim⟩
  rcases H.rebaseAddInductSafe (valid .safe) VEnv.LE.rfl
      hdecl hcompile hprovenance (Hreplay .safe) with
    ⟨safeBase, Hsafe, HsafeAdd, hsafeLE, hsafeProj, hsafeElim⟩
  let pre : DefinitionSafety → VEnv
    | .unsafe => unsafeBase
    | .partial => partialBase
    | .safe => safeBase
  let next (safety : DefinitionSafety) :=
    (pre safety).addDefEqRules rules
  let cert : ∀ safety,
      BlockCertificate safety prodEnv (ves.venv safety) types ctors
        recursors rules outEnv (pre safety)
    | .unsafe => Hunsafe
    | .partial => Hpartial
    | .safe => Hsafe
  have certProjections : ∀ safety, (cert safety).projections = H.projections
    | .unsafe => hunsafeProj
    | .partial => hpartialProj
    | .safe => hsafeProj
  have certEliminators : ∀ safety, (cert safety).installation.eliminators = H.installation.eliminators
    | .unsafe => hunsafeElim
    | .partial => hpartialElim
    | .safe => hsafeElim
  let adds : ∀ safety,
      AddInduct safety prodEnv.constants (ves.venv safety) decl outEnv.constants
        (next safety)
    | .unsafe => HunsafeAdd
    | .partial => HpartialAdd
    | .safe => HsafeAdd
  let outputLE : ∀ safety,
      (outBase.addDefEqRules rules) ≤ next safety
    | .unsafe => hunsafeLE
    | .partial => hpartialLE
    | .safe => hsafeLE
  have hprimitives : ∀ safety, (next safety).HasPrimitives := by
    intro safety
    simpa [next] using
      (cert safety).hasPrimitives (wf.hasPrimitives (safety := safety))
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] :=
    (Hsafe.validCore (valid .safe).toValidCore).safePrimitives
  have hsemantics : ∀ safety,
      ConstructorParameterAlignment safety outEnv
        (next safety) := by
    intro safety
    have hreplay : (outBase.addDefEqRules rules) ≤ ((pre safety).addDefEqRules rules) := by
      simpa [next] using
        outputLE safety
    simpa [next] using
      H.replaySafeConstructorTyping (cert safety)
        (wf.tr (safety := safety)).map_wf
        (wf.constructorParameterAlignment (safety := safety)) hconstructorSemantics
        hreplay
  have hmono : ∀ {safety safety'}, safety ≤ safety' →
      next safety' ≤ next safety := by
    intro safety safety' hle
    have hblock' := (cert safety').block_eq_of_projections_eq H
      (certProjections safety') (certEliminators safety')
    have hblock := (cert safety).block_eq_of_projections_eq H
      (certProjections safety) (certEliminators safety)
    have hi' : H.block.install (ves.venv safety') = some (next safety') := by
      simpa [next, hblock'] using
        (cert safety').install
    have hi : H.block.install (ves.venv safety) = some (next safety) := by
      simpa [next, hblock] using
        (cert safety).install
    exact VInductBlock.install_mono (wf.mono hle)
      hi' hi
  have hwf : prodEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hdeclSafe : decl.isUnsafe = false :=
    H.declUnsafe hwf (H.installation.atomic.targetMapWF hwf) H.entriesSafe horigins hcover
      hdecl.1.1
  have hblocks : ∀ safety, InstalledBlocks safety outEnv (next safety) .complete := by
    intro safety
    have htrOut : TrEnv safety outEnv (next safety) := by
      unfold TrEnv
      rw [H.installation.quotInit_eq]
      exact .induct (adds safety) (wf.tr (safety := safety))
    have hvis : safety ≤ (if decl.isUnsafe then .unsafe else .safe) := by
      rw [hdeclSafe]; exact DefinitionSafety.le_safe
    exact H.installedBlocks (wf.blocks (safety := safety)) hwf htrOut.toChecking
      (adds safety).le horigins hcover hclosed hconstructorOwners
      (by rw [hdeclSafe]; exact H.entriesSafe) hprovenance (fun _ => adds safety)
      (fun h => absurd hvis h) (fun _ => hsemantics safety) hctorOrigin
      (fun _ => hH.trans (outputLE safety))
  rcases wf.extendInductExact decl next adds H.installation.quotInit_eq
      hprimitives hsafePrimitives hblocks hmono with
    ⟨ves', wf', hsourceLE, hexact⟩
  refine ⟨ves', wf', hsourceLE, ?_, ?_⟩
  rw [hexact .safe]
  exact (adds .safe).toVEnv
  rw [hexact .safe]
  exact outputLE .safe

/-- Install a certified inductive block directly into the concrete
environment-refinement judgment.  This is the abstract/executable seam used
by the inductive branch of declaration verification. -/
theorem BlockCertificate.trEnv
    {decl : VInductDecl}
    (H : BlockCertificate checkSafety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      venv outEnv.constants (outVEnv.addDefEqRules rules))
    (hsource : TrEnv' checkSafety prodEnv.constants quotInit venv)
    (helim : VInductBlock.EliminatorsWF venv decl H.block) :
    TrEnv' checkSafety outEnv.constants quotInit
      (outVEnv.addDefEqRules rules) :=
  .induct
    (H.addInduct hdecl hcompile hprovenance hsource.aligned helim) hsource

/-- Unsafe inductives extend only the unsafe abstract model; partial and safe
models replay the concrete additions through `TrEnv'.ignore`. -/
theorem BlockCertificate.extendUnsafeOfHiddenExact
    {ves : VEnvs} {decl : VInductDecl}
    (H : BlockCertificate .unsafe prodEnv (ves.venv .unsafe) types ctors
      recursors rules outEnv outVEnv)
    (wf : ves.WF prodEnv)
    (hdecl : decl.WF (ves.venv .unsafe))
    (hcompile : decl.CompilesTo (ves.venv .unsafe) H.block)
    (horigins : InductInfosFromDecl prodEnv.constants outEnv.constants
      decl)
    (hprovenance : NewRecursorsAligned .unsafe prodEnv.constants
      (ves.venv .unsafe) outEnv.constants (outVEnv.addDefEqRules rules))
    (hunsafe : ∀ entry ∈ types ++ ctors ++ recursors,
      entry.1.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .unsafe outEnv
        (outVEnv.addDefEqRules rules))
    (helim : VInductBlock.EliminatorsWF (ves.venv .unsafe) decl H.block)
    (hcover : ∀ T ∈ decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ prodEnv.find? T.name = none)
    {isUnsafe : Bool} {venvH : VEnv}
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      prodEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt venvH ci))
    (hH : venvH ≤ (outVEnv.addDefEqRules rules)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      VEnv.AddInduct (ves.venv .unsafe) decl (ves'.venv .unsafe) ∧
      (outVEnv.addDefEqRules rules) ≤ ves'.venv .unsafe := by
  have validUnsafe : CheckingEnv.Valid .unsafe prodEnv
      (ves.venv .unsafe) :=
    wf.toCheckingValid (.unsafe)
  have hiddenPartial : ∀ entry ∈ types ++ ctors ++ recursors,
      ¬ DefinitionSafety.partial ≤ entry.1.safety := by
    intro entry hentry
    rw [hunsafe entry hentry]
    decide
  have hiddenSafe : ∀ entry ∈ types ++ ctors ++ recursors,
      ¬ DefinitionSafety.safe ≤ entry.1.safety := by
    intro entry hentry
    rw [hunsafe entry hentry]
    decide
  have htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      (outVEnv.addDefEqRules rules) := by
    rw [H.installation.quotInit_eq]
    exact H.trEnv hdecl hcompile hprovenance
      (wf.tr (safety := .unsafe)) helim
  have htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial) := by
    rw [H.installation.quotInit_eq]
    apply H.installation.trEnvIgnore
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · intro entry hentry
      exact hiddenPartial entry (by simp [hentry])
    · exact wf.tr (safety := .partial)
  have htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe) := by
    rw [H.installation.quotInit_eq]
    apply H.installation.trEnvIgnore
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · intro entry hentry
      exact hiddenSafe entry (by simp [hentry])
    · exact wf.tr (safety := .safe)
  have haddUnsafe : AddInduct .unsafe prodEnv.constants
      (ves.venv .unsafe) decl outEnv.constants
      (outVEnv.addDefEqRules rules) :=
    H.addInduct hdecl hcompile hprovenance
      (wf.tr (safety := .unsafe)).aligned helim
  have hwf : prodEnv.constants.WF := (wf.tr (safety := .unsafe)).map_wf
  have hb : ∀ e ∈ types ++ ctors ++ recursors, e.1.isUnsafe = true := by
    intro e he
    have := hunsafe e he
    cases h : e.1.isUnsafe
    · revert this
      simp only [ConstantInfo.safety, h, Bool.false_eq_true, ↓reduceIte]
      split <;> exact nofun
    · rfl
  have hdeclUnsafe : decl.isUnsafe = true :=
    H.declUnsafe hwf (H.installation.atomic.targetMapWF hwf) hb horigins hcover
      hdecl.1.1
  have hb' : ∀ e ∈ types ++ ctors ++ recursors, e.1.isUnsafe = decl.isUnsafe := by
    rw [hdeclUnsafe]; exact hb
  have hhidden (observer : DefinitionSafety) (hobserver : observer ≠ .unsafe) :
      ¬ observer ≤ (if decl.isUnsafe then .unsafe else .safe) := by
    rw [hdeclUnsafe]
    intro hle
    exact hobserver (DefinitionSafety.le_antisymm hle DefinitionSafety.unsafe_le)
  have hblocks : ∀ safety, InstalledBlocks safety outEnv
      (match safety with
      | .unsafe => (outVEnv.addDefEqRules rules)
      | .partial => ves.venv .partial
      | .safe => ves.venv .safe) .complete
    | .unsafe => H.installedBlocks (wf.blocks (safety := .unsafe)) hwf
        (show TrEnv .unsafe outEnv (outVEnv.addDefEqRules rules) from htrUnsafe).toChecking
        haddUnsafe.le horigins hcover hclosed hconstructorOwners hb' hprovenance
        (fun _ => haddUnsafe) (fun h => absurd DefinitionSafety.unsafe_le h)
        (fun _ => hconstructorSemantics) hctorOrigin (fun _ => hH)
    | .partial => H.installedBlocks (wf.blocks (safety := .partial)) hwf
        (show TrEnv .partial outEnv (ves.venv .partial) from htrPartial).toChecking
        VEnv.LE.rfl horigins hcover hclosed hconstructorOwners hb' hprovenance
        (fun h => absurd h (hhidden .partial (by decide))) (fun _ => rfl)
        (fun h => absurd h (hhidden .partial (by decide))) hctorOrigin
        (fun h => absurd h (hhidden .partial (by decide)))
    | .safe => H.installedBlocks (wf.blocks (safety := .safe)) hwf
        (show TrEnv .safe outEnv (ves.venv .safe) from htrSafe).toChecking
        VEnv.LE.rfl horigins hcover hclosed hconstructorOwners hb' hprovenance
        (fun h => absurd h (hhidden .safe (by decide))) (fun _ => rfl)
        (fun h => absurd h (hhidden .safe (by decide))) hctorOrigin
        (fun h => absurd h (hhidden .safe (by decide)))
  rcases H.extendUnsafeExact wf htrUnsafe htrPartial htrSafe
      (H.validCore validUnsafe.toValidCore).safePrimitives hblocks with
    ⟨ves', wf', hle, hexact⟩
  refine ⟨ves', wf', hle, ?_, hexact ▸ VEnv.LE.rfl⟩
  rw [hexact]
  exact haddUnsafe.toVEnv



def GeneratedRecursors.toBlockCertificate
    (projections : List VProjectionEntry)
    (installation : BlockInstallation safety env venv types ctors recursors
      projections outEnv outVEnv)
    (H : GeneratedRecursors safety
      ((installation.venvCtors.addEliminators installation.eliminators).addProjections projections)
      lparams elimLevel c stats
      indTypes recInfos recursors)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (htypes : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv)
    (hctors : ∀ ci ∈ ctors.map Prod.snd,
      ci.toVConstant.WF installation.venvTypes)
    (hrules : ∀ df ∈ rules, df.WF outVEnv) :
    BlockCertificate safety env venv types ctors recursors rules
      outEnv outVEnv where
  projections := projections
  installation := installation
  typesWF := htypes
  ctorsWF := hctors
  recursorsWF := H.recursorsWF Hc Hbindings Hparams
  rulesWF := hrules

theorem ConstructorCheck.typesWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ∀ ci ∈ R.headerEntries.map Prod.snd,
      ci.toVConstant.WF sourceEnv := by
  rw [R.headerValues]
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types target htarget with
    ⟨source, _, Htarget⟩
  exact Htarget.header.wf

theorem ConstructorCheck.ctorsWF
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    ∀ ci ∈ R.constructorEntries.map Prod.snd,
      ci.toVConstant.WF R.headerVEnv := by
  rw [R.constructorValues]
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  rcases hci with ⟨target, htarget, hci⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types target htarget with
    ⟨source, _, Htarget⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ci hci with
    ⟨ctor, _, Hctor⟩
  exact Hctor.wf

def RecursorCheck.installation
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    BlockInstallation c.safety c.env sourceEnv R.headerEntries
      R.constructorEntries H.entries decl.projectionEntries outEnv H.outVEnv where
  envTypes := R.headerEnv
  venvTypes := R.headerVEnv
  envCtors := ctorEnv
  venvCtors := R.ctorVEnv
  formation := R.installation
  eliminators := R.eliminators
  casesWF := R.casesWF
  projectedWF := R.projectedWF
  recursorsAdded := by
    rw [← R.contextVEnv]
    simpa [H.localExtends.safety_eq, H.localExtends.env_eq] using H.installed

def RecursorCheck.blockCertificate
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    BlockCertificate c.safety c.env sourceEnv R.headerEntries
      R.constructorEntries H.entries rules outEnv H.outVEnv := by
  let Hgenerated : GeneratedRecursors c.safety
      ((R.ctorVEnv.addEliminators R.eliminators).addProjections decl.projectionEntries) c.lparams
      H.elimLevel H.localContext stats indTypes H.recInfos H.entries := by
    rw [← R.contextVEnv]
    simpa [H.localExtends.safety_eq, H.localExtends.lparams_eq] using
      H.generated
  exact Hgenerated.toBlockCertificate decl.projectionEntries H.installation
    H.localWF H.bindings H.params R.typesWF R.ctorsWF hrules

@[simp] theorem RecursorCheck.blockCertificate_projections
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    (H.blockCertificate rules hrules).projections = decl.projectionEntries := by
  rfl

/-- The certified block registers the declaration's certified case eliminators. -/
theorem RecursorCheck.blockEliminatorsWF
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    VInductBlock.EliminatorsWF sourceEnv decl (H.blockCertificate rules hrules).block :=
  R.eliminatorsWF.congr_block R.headerValues R.constructorValues rfl rfl

/-- The certified block's case eliminators are certified over every larger environment in
which its families and constructors install. -/
theorem RecursorCheck.blockEliminatorsReplay
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) {env' : VEnv} (hle : sourceEnv ≤ env') :
    VInductBlock.EliminatorsReplay env' decl (H.blockCertificate rules hrules).block :=
  R.eliminatorsCertified.replay hle (fun _ h => h.elim) R.headerValues R.constructorValues rfl rfl

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem RecursorCheck.minorPrefixLength_eq
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) (owner : Nat)
    (howner : owner ≤ H.recInfos.size) :
    ((H.recInfos.toList.take owner).flatMap
      (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  have hsizes : H.recInfos.size = indTypes.size := by
    calc
      H.recInfos.size = decl.types.length := H.cardinality.records
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < H.recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos H.recInfos owner hrec,
        getElem!_pos indTypes owner hind] using H.minorCounts owner hrec

theorem RecursorCheck.outVEnvWF
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : H.outVEnv.WF := by
  have hvalid : CheckingEnv.ValidCore H.localContext.safety
      H.localContext.env
        R.context.venv := by
    rw [H.localExtends.safety_eq, H.localExtends.env_eq]
    exact R.context.checking.toValidCore
  exact (H.installed.validCore hvalid).tr.wf

/-- Recursor installation preserves the constructor semantics established at
the checked formation. -/
theorem RecursorCheck.constructorParameterAlignment
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (Hsource : ConstructorParameterAlignment
      safety c.env sourceEnv) :
    ConstructorParameterAlignment safety outEnv H.outVEnv := by
  apply H.installed.preservesConstructorTyping
  · rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  · rw [H.localExtends.env_eq]
    exact (R.constructorParameterAlignment Hsource).mono R.ctorLE
  · exact H.generated.nonInductive

/-- Every family of the declaration is a new kernel header of the output. -/
theorem RecursorCheck.cover
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    ∀ T ∈ decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ c.env.find? T.name = none := by
  intro T hT
  have hwf := R.sourceContext.checking.tr.map_wf
  have hmem : T.toVConstVal ∈ R.headerEntries.map Prod.snd := by
    rw [R.headerValues]; exact List.mem_map_of_mem hT
  obtain ⟨⟨ci, val⟩, he, hval⟩ := List.mem_map.mp hmem
  obtain ⟨numNested, Hheaders⟩ := R.headerSourceAligned
  obtain ⟨info, -, hci⟩ := Hheaders.originInfo he
  have hname : ci.name = T.name := by
    have := R.installation.atomic.entryNames (List.mem_append_left _ he)
    simp only at this hval
    rw [this, hval]
  have hfind := R.installation.findHeaderEntry hwf he
  have hfresh := R.installation.atomic.entryFresh hwf (List.mem_append_left _ he)
  simp only at hci
  subst hci
  have hctorWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  have hout := H.installed.preservesSourceFind hctorWF
    (by rw [H.localExtends.env_eq]; exact hfind)
  refine ⟨info, ?_, ?_⟩
  · rw [← hname]; exact hout
  · rw [← hname]; exact hfresh

theorem RecursorCheck.inductInfosFromDecl
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants decl := by
  have hctorOrigins : InductInfosFromDecl c.env.constants
      H.localContext.env.constants decl := by
    simpa [H.localExtends.env_eq] using R.inductInfosFromDecl
  apply InductInfosFromDecl.addConstants hctorOrigins H.installed
  · rw [H.localExtends.env_eq]
    exact R.context.checking.tr.map_wf
  · exact H.generated.nonInductive

theorem RecursorCheck.constructorTyping
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (Hsource : ConstructorParameterAlignment
      safety c.env sourceEnv) (rules : List VDefEq) :
    ConstructorParameterAlignment safety outEnv
      (H.outVEnv.addDefEqRules rules) :=
  (H.constructorParameterAlignment Hsource).mono
    VEnv.addDefEqRules_le

theorem RecursorCheck.generatedTelescopeTranslations
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) :
    RecursorTypeTelescopes
      R.context.venv stats
      H.recInfos H.entries := by
  intro ownerIdx hentry
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [← H.generated.length]
    exact hentry
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    ownerIdx hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  refine ⟨E.info, E.source_eq, ?_⟩
  exact E.telescopeTranslation selections hrecInfo hnoalias

theorem RecursorCheck.generatedRecursorCommonPrefixBinderDomainAt
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (i : Nat)
    (hi : i < stats.params.size +
      (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size)
    {domain₁ domain₂ : Expr}
    (Hbinder₁ : Expr.ForallBinderAt
      (H.generated.entry owner₁ howner₁).info.type i domain₁)
    (Hbinder₂ : Expr.ForallBinderAt
      (H.generated.entry owner₂ howner₂).info.type i domain₂) :
    domain₁ = domain₂ := by
  have hrecInfo₁ : owner₁ < H.recInfos.size := by
    simpa [H.generated.length] using howner₁
  have hrecInfo₂ : owner₂ < H.recInfos.size := by
    simpa [H.generated.length] using howner₂
  let E₁ := H.generated.entry owner₁ howner₁
  let E₂ := H.generated.entry owner₂ howner₂
  let S₁ := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner₁ hrecInfo₁
  let S₂ := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner₂ hrecInfo₂
  have hnoalias₁ : S₁.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₁ hrecInfo₁
  have hnoalias₂ : S₂.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias
      owner₂ hrecInfo₂
  by_cases hparam : i < stats.params.size
  · rcases H.params.declarationAt H.localWF i hparam with ⟨D⟩
    have Hcanonical₁ := S₁.parameterBinderAt hnoalias₁ D
    have Hcanonical₂ := S₂.parameterBinderAt hnoalias₂ D
    dsimp only at Hcanonical₁ Hcanonical₂
    rw [← E₁.type] at Hcanonical₁
    rw [← E₂.type] at Hcanonical₂
    exact (Hbinder₁.unique Hcanonical₁).trans
      (Hbinder₂.unique Hcanonical₂).symm
  · let motiveIdx := i - stats.params.size
    by_cases hmotive : motiveIdx < (H.recInfos.map (·.motive)).size
    · rcases H.bindings.motives.declarationAt H.localWF motiveIdx hmotive with
        ⟨D⟩
      have Hcanonical₁ := S₁.motiveBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.motiveBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size + motiveIdx = i := by
        dsimp [motiveIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm
    · let minorIdx := i - stats.params.size -
        (H.recInfos.map (·.motive)).size
      have hminor : minorIdx <
          (H.recInfos.flatMap (·.minors)).size := by
        dsimp [motiveIdx, minorIdx] at hmotive ⊢
        omega
      rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx hminor with
        ⟨D⟩
      have Hcanonical₁ := S₁.minorBinderAt hnoalias₁ D
      have Hcanonical₂ := S₂.minorBinderAt hnoalias₂ D
      dsimp only at Hcanonical₁ Hcanonical₂
      have hiEq : stats.params.size +
          (H.recInfos.map (·.motive)).size + minorIdx = i := by
        dsimp [minorIdx]
        omega
      rw [hiEq, ← E₁.type] at Hcanonical₁
      rw [hiEq, ← E₂.type] at Hcanonical₂
      exact (Hbinder₁.unique Hcanonical₁).trans
        (Hbinder₂.unique Hcanonical₂).symm

end VerifyInductive
end Lean4Lean
