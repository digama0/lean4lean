import Lean4Lean.Verify.Inductive.Nested.Install.Certificate
import Lean4Lean.Verify.Inductive.Nested.Install.AddInduct
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledFamilyLookups
import Lean4Lean.Verify.Inductive.Prelude.EqReady
import Lean4Lean.Verify.Inductive.Install.Result

/-! The block certificate of a restored nested block
(`RestoredBlockCertificate.blockCertificate`) and the safety-indexed
extension of the environment model that it yields for safe and unsafe nested
declarations, with the source-family lookups and the constructor-owner
invariant read off the restoration folds. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem FreshExtension.trEnvIgnore
    (H : FreshExtension source entries target)
    (hsourceWF : source.constants.WF)
    (hhidden : ∀ ci ∈ entries, ¬ observer ≤ ci.safety)
    (htr : TrEnv' observer source.constants source.quotInit venv) :
    TrEnv' observer target.constants target.quotInit venv := by
  induction H generalizing venv with
  | nil => exact htr
  | @cons rest target source ci hfresh Htail ih =>
      have hfreshMap : source.constants.find? ci.name = none := by
        rw [← hsourceWF.find?'_eq_find?]
        exact hfresh
      have hnextWF : (source.add ci).constants.WF :=
        constantsWF_add_checked hsourceWF hfresh
      have hhead : TrEnv' observer (source.add ci).constants
          (source.add ci).quotInit venv := by
        exact .ignore hfreshMap (hhidden ci (by simp)) htr
      exact ih hnextWF (fun entry hentry =>
        hhidden entry (by simp [hentry])) hhead

private def ConstructorParameterAlignmentAt.mapKernel
    (H : ConstructorParameterAlignmentAt source venv familyName
      familyInfo i hi)
    (heq : ∀ name, source.find? name = target.find? name) :
    ConstructorParameterAlignmentAt target venv familyName
      familyInfo i hi where
  info := H.info
  lookup := by
    rw [← heq]
    exact H.lookup
  induct := H.induct
  cidx := H.cidx
  numParams := H.numParams
  levelParams := H.levelParams
  isUnsafe := H.isUnsafe
  familyTarget := H.familyTarget
  constructorTarget := H.constructorTarget
  familyLookup := H.familyLookup
  constructorLookup := H.constructorLookup
  familyUvars := H.familyUvars
  constructorUvars := H.constructorUvars
  familyNormalized := H.familyNormalized
  constructorNormalized := H.constructorNormalized
  familyDomains := H.familyDomains
  constructorDomains := H.constructorDomains
  familyTail := H.familyTail
  constructorTail := H.constructorTail
  familyType := H.familyType
  constructorType := H.constructorType
  familyDefEq := H.familyDefEq
  constructorDefEq := H.constructorDefEq
  familyParams := H.familyParams
  constructorParams := H.constructorParams
  parameterDomains := H.parameterDomains

private theorem ConstructorParameterAlignment.mapKernel
    (H : ConstructorParameterAlignment safety source venv)
    (heq : ∀ name, source.find? name = target.find? name) :
    ConstructorParameterAlignment safety target venv := by
  intro familyName familyInfo hfamily hvisible i hi
  have hfamily' : source.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [heq]
    exact hfamily
  rcases H familyName familyInfo hfamily' hvisible i hi with ⟨C⟩
  exact ⟨C.mapKernel heq⟩

/-- Recover the replayable block certificate before `NestedInstallResult`
projects it to the independent `VEnv.AddInduct` judgment.  This is the
dependency-order block installation retained by the restored block
certificate; in particular, its kernel endpoint is the environment actually
returned by restoration. -/
def RestoredBlockCertificate.blockCertificate
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    BlockCertificate safety sourceProdEnv sourceEnv C.typeEntries
      C.constructorEntries C.recursorEntries
      (C.sourceRules ++ C.auxiliaryRules) C.installedEnv
        C.recursorVEnv where
  installation := C.install
  projections := decl.projectionEntries
  typesWF := by
    rw [C.typeValues]
    exact C.sourceTranslations.typeConstantsWF C.typesSource
  ctorsWF := by
    rw [C.constructorValues]
    exact C.sourceTranslations.constructorConstantsWF C.typesSource
  recursorsWF := by
    rw [C.recursorValues]
    intro ci hci
    rcases List.mem_append.mp hci with hprimary | hauxiliary
    · exact C.sourceTranslations.sourceRecursorsWF ci hprimary
    · exact C.auxiliaryWF.recursorsWF (by simp) ci hauxiliary
  rulesWF := by
    intro df hdf
    rcases List.mem_append.mp hdf with hprimary | hauxiliary
    · exact C.sourceIota.rulesWF df hprimary
    · exact C.auxiliaryWF.rulesWF (by simp) df hauxiliary

theorem RestoredBlockCertificate.block_eq_restoredBlock
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    C.blockCertificate.block =
      { restoredBlock decl C.sourceRecursors C.auxiliaryRecursors
        C.sourceRules C.auxiliaryRules with eliminators := C.install.eliminators } := by
  simp [BlockCertificate.block, restoredBlock,
    RestoredBlockCertificate.blockCertificate, C.typeValues,
    C.constructorValues, C.recursorValues]

/-- The replayable block is the same source nested compilation used by the
independent `AddInduct` result. -/
theorem RestoredBlockCertificate.compilation
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) :
    decl.CompilesTo sourceEnv C.blockCertificate.block := by
  rw [C.block_eq_restoredBlock]
  exact (C.trCompilation.congr_eliminators C.install.eliminators).compiles

theorem RestoredBlockCertificate.declWF
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety) : decl.WF sourceEnv := by
  let Hsource := C.sourceTranslations.core C.typesSource C.uvars C.numParams
    C.unsafeEq C.typesAdded C.constructorsAdded
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource
        C.sourceNonempty)
  exact ⟨Lean4Lean.TrInductDecl.sourceWF Htranslated,
    .nested C.formationAssembly.formation VEnv.LE.rfl⟩

/-- The lowered run retained by the restored block certificate and the
restoration folds determine the source-family lookups (`InductInfosFromDecl`).
The equalities are only the indices erased when the executable run is
unpacked; no independent lookup fact remains. -/
theorem RestoredBlockCertificate.inductInfosFromDecl
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv)
    (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name)) :
    InductInfosFromDecl sourceProdEnv.constants outEnv.constants
      decl := by
  have Hsource : TrInductDeclCore sourceEnv c.lparams nparams sourceTypes
      isUnsafe decl C.install.venvTypes
        C.install.venvCtors := by
    simpa only [hlparams] using
      C.sourceTranslations.core C.typesSource C.uvars C.numParams C.unsafeEq
        C.typesAdded C.constructorsAdded
  have Hrestored : NestedRestorationFolds result loweredEnv
      c.env auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv) := by
    simpa only [henv, hnames] using H
  have Horigins := Hrestored.inductInfosFromDecl Hlower Hc Hprod
    Hsource Hmetadata Hsources Harity Howners hempty
  simpa only [henv] using Horigins

/-- Every family of a restored source declaration is a new kernel header of the restored
environment. -/
theorem RestoredBlockCertificate.cover
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv)
    (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name)) :
    ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      sourceProdEnv.find? T.name = none := by
  have Hsource : TrInductDeclCore sourceEnv c.lparams nparams sourceTypes
      isUnsafe decl C.install.venvTypes
        C.install.venvCtors := by
    simpa only [hlparams] using
      C.sourceTranslations.core C.typesSource C.uvars C.numParams C.unsafeEq
        C.typesAdded C.constructorsAdded
  have Hrestored : NestedRestorationFolds result loweredEnv
      c.env auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv) := by
    simpa only [henv, hnames] using H
  intro T hT
  obtain ⟨v, hv, hnone⟩ := Hrestored.cover Hlower Hc Hprod Hsource Hmetadata Hsources Harity
    Howners hempty T hT
  exact ⟨v, hv, henv ▸ hnone⟩

/-- The restoration folds, reindexed to the context of the lowered run
retained by the restored block certificate, preserve the constructor owner
invariant. -/
theorem NestedRestorationFolds.constructorOwnersPresentOfContext
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    {sourceEnv : VEnv} {nparams : Nat} {isUnsafe : Bool}
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name)) :
    ConstructorOwnersPresent outEnv := by
  have Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv) := by
    simpa only [henv, hnames] using H
  exact Hrestored.constructorOwnersPresent Hlower Hc Hprod hempty Howners

/-- A safe nested restoration extends every safety-indexed observer by
replaying the restored block in dependency order.  The result retains both the
complete installed model and the source-facing nested judgment produced by
the same restored block certificate. -/
private theorem RestoredBlockCertificate.extendSafe
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {ves : VEnvs}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool}
    (C : RestoredBlockCertificate H (ves.venv .safe) decl lparams
      nparams isUnsafe .safe)
    (wf : ves.WF sourceProdEnv)
    (Horigins : InductInfosFromDecl sourceProdEnv.constants
      outEnv.constants decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .safe outEnv
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)))
    (hcover : ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      sourceProdEnv.find? T.name = none)
    {venvH : VEnv}
    (htypesH : (ves.venv .safe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt venvH ci)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (NestedInstallResult (ves.venv .safe) decl lparams
        nparams sourceTypes isUnsafe .safe outEnv) ∧
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) ∧
      ∀ venvH, (ves.venv .safe).addConstVals decl.typeConstants = some venvH →
        venvH ≤ ves'.venv .safe := by
  let B := C.blockCertificate
  have Hvalid : CheckingEnv.Valid .safe sourceProdEnv (ves.venv .safe) :=
    wf.toCheckingValid (.safe)
  let HactualExists : Nonempty { entries : List ConstantInfo //
      FreshExtension sourceProdEnv entries outEnv } := by
    rcases H.freshExtension Hvalid.tr.map_wf with ⟨entries, Hentries⟩
    exact ⟨⟨entries, Hentries⟩⟩
  let actual := Classical.choice HactualExists
  have hlookup : ∀ name, outEnv.constants.find? name =
      C.installedEnv.constants.find? name :=
    actual.property.lookupEqOfPerm C.install.atomic.freshExtension
      Hvalid.tr.map_wf (C.executableOrder_perm actual.val actual.property)
  have hlookupEnv : ∀ name, outEnv.find? name =
      C.installedEnv.find? name := by
    intro name
    change outEnv.constants.find?' name =
      C.installedEnv.constants.find?' name
    rw [(actual.property.targetWF Hvalid.tr.map_wf).find?'_eq_find?,
      (C.install.atomic.targetMapWF Hvalid.tr.map_wf).find?'_eq_find?]
    exact hlookup name
  have valid (observer : DefinitionSafety) :
      CheckingEnv.Valid observer sourceProdEnv (ves.venv observer) :=
    wf.toCheckingValid (observer)
  have replay (observer : DefinitionSafety) :
      ∃ replayBase,
        ∃ Breplay : BlockCertificate observer sourceProdEnv
          (ves.venv observer) C.typeEntries C.constructorEntries
          C.recursorEntries (C.sourceRules ++ C.auxiliaryRules)
          C.installedEnv replayBase,
        Breplay.projections = decl.projectionEntries ∧
        AddInduct observer sourceProdEnv.constants (ves.venv observer) decl
          outEnv.constants (replayBase.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) ∧
        (C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) ≤
          (replayBase.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) ∧
        Breplay.installation.eliminators = B.installation.eliminators := by
    have hB : B.block = _ := C.block_eq_restoredBlock
    have Hreplay : VInductBlock.EliminatorsReplay (ves.venv observer) decl B.block :=
      (C.eliminatorsCertified (ves.venv observer) (wf.mono DefinitionSafety.le_safe)
        (fun n hn => by
          cases h : (ves.venv observer).constants n with
          | none => rfl
          | some ci =>
            obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := observer)).aligned.find?_iff.mpr ⟨ci, h⟩
            rw [hn] at hfind; cases hfind)).congr_fields
        (by rw [hB]; rfl) (by rw [hB]; rfl) (by rw [hB]; rfl) (by rw [hB]; rfl)
    rcases B.rebaseAddInduct (valid observer) DefinitionSafety.le_safe
        (wf.mono DefinitionSafety.le_safe) C.declWF
        C.compilation Hreplay with
      ⟨replayBase, Breplay, hprojections, Habstract, hout, heliminators⟩
    have HcheckingCanonical : CheckingEnv observer C.installedEnv
        replayBase := (Breplay.installation.validCore (valid observer).toValidCore).tr
    have Hchecking : CheckingEnv observer outEnv replayBase :=
      CheckingEnv.mapExt HcheckingCanonical
        (actual.property.targetWF Hvalid.tr.map_wf)
        (fun name => (hlookup name).symm)
    have HcheckingRules : CheckingEnv observer outEnv
        (replayBase.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) := {
      aligned := by
        exact aligned_addDefEqs Hchecking.aligned
          (C.sourceRules ++ C.auxiliaryRules)
      wf := by
        rcases (wf.tr (safety := observer)).wf with ⟨ds, Hds⟩
        exact ⟨.induct decl :: ds,
          Hds.decl (.induct Habstract)⟩
      of_value := by
        intro name ci value hfind hs hvalue
        exact (Hchecking.of_value hfind hs hvalue).mono
          VEnv.addDefEqRules_le
    }
    have Hprovenance : NewRecursorsAligned observer
        sourceProdEnv.constants (ves.venv observer) outEnv.constants
        (replayBase.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) :=
      (C.recursorsAligned.rebaseBlock (wf.mono DefinitionSafety.le_safe) hout
        B.install Breplay.install rfl).ofUnsafe
    have Hadd := H.addInductConcrete Habstract HcheckingRules Hprovenance
      Hvalid.tr.map_wf
    exact ⟨replayBase, Breplay,
      hprojections.trans (by rfl), Hadd, hout, heliminators⟩
  let pre (observer : DefinitionSafety) :=
    Classical.choose (replay observer)
  have replaySpec (observer : DefinitionSafety) :=
    Classical.choose_spec (replay observer)
  let cert (observer : DefinitionSafety) :=
    Classical.choose (replaySpec observer)
  have certSpec (observer : DefinitionSafety) :=
    Classical.choose_spec (replaySpec observer)
  let adds (observer : DefinitionSafety) := (certSpec observer).2.1
  let outputLE (observer : DefinitionSafety) := (certSpec observer).2.2.1
  let next (observer : DefinitionSafety) :=
    (pre observer).addDefEqRules (C.sourceRules ++ C.auxiliaryRules)
  have hcompletedCanonical :
      ConstructorParameterAlignment .safe C.installedEnv
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)) :=
    hconstructorSemantics.mapKernel hlookupEnv
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci hfind hprimitive
    apply (C.install.validCore Hvalid.toValidCore).safePrimitives
    · rw [← hlookupEnv]
      exact hfind
    · exact hprimitive
  have Hmodels : ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ observer, ves.venv observer ≤ ves'.venv observer) ∧
      ∀ observer, ves'.venv observer = next observer := by
    apply wf.extendInductExact decl next adds actual.property.quotInit_eq
    · intro observer
      exact (cert observer).hasPrimitives
        (wf.hasPrimitives (safety := observer))
    · exact hsafePrimitives
    · intro observer
      have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := observer)).map_wf
      have houtWF : outEnv.constants.WF := actual.property.targetWF hwf
      have hdeclSafe : decl.isUnsafe = false :=
        Horigins.declUnsafe hwf houtWF hcover C.declWF.1.1 fun hv hnone => by
          rw [hlookupEnv] at hv
          simpa [ConstantInfo.isUnsafe] using B.newUnsafe hwf B.entriesSafe hv hnone
      have htrOut : TrEnv observer outEnv (next observer) := by
        unfold TrEnv
        rw [actual.property.quotInit_eq]
        exact .induct (adds observer) (wf.tr (safety := observer))
      have hvis : observer ≤ (if decl.isUnsafe then .unsafe else .safe) := by
        rw [hdeclSafe]; exact DefinitionSafety.le_safe
      have hHle : venvH ≤ next observer := by
        rw [← C.typeValues] at htypesH
        exact (B.typesLe htypesH).trans (outputLE observer)
      refine (wf.blocks (safety := observer)).addInduct hwf htrOut.toChecking
        (fun {n ci} h => by
          have := (adds observer).preservesSourceFind
            (by rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h)
          rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?])
        (adds observer).le Horigins hcover hclosed hconstructorOwners ?_
        (fun _ => adds observer) (fun h => absurd hvis h) ?_ ?_ ?_
      · intro n r hf hnone
        have hfMap : outEnv.constants.find? n = some (.recInfo r) := by
          rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hf
        rcases C.recursorsAligned.recursor hfMap with hold | hnew
        · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
        · obtain ⟨-, -, info, hmajor⟩ := hnew DefinitionSafety.unsafe_le
          exact ⟨info, by rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]⟩
      · intro _
        have Hcanonical := B.replaySafeConstructorTyping
          (cert observer) Hvalid.tr.map_wf
          (wf.constructorParameterAlignment (safety := observer)) hcompletedCanonical
          (outputLE observer)
        exact Hcanonical.mapKernel (fun name => (hlookupEnv name).symm)
      · intro _ n c hf hnone
        rcases hctorOrigin hf with hold | ⟨-, htel⟩
        · rw [hold] at hnone; cases hnone
        · exact htel.mono hHle
      · intro n r hf hnone hrvis
        have hfMap : outEnv.constants.find? n = some (.recInfo r) := by
          rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hf
        rcases (adds observer).newRecursorsAligned.recursor hfMap with hold | hnew
        · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
        · obtain ⟨hcore, hk, -⟩ := hnew hrvis
          exact ⟨hcore, hk⟩
    · intro observer observer' hle
      have hblock : (cert observer').block = (cert observer).block :=
        (cert observer').block_eq_of_projections_eq (cert observer)
          ((certSpec observer').1.trans (certSpec observer).1.symm)
          ((certSpec observer').2.2.2.trans (certSpec observer).2.2.2.symm)
      have hinstall := (cert observer').install
      rw [hblock] at hinstall
      exact VInductBlock.install_mono (wf.mono hle)
        hinstall
        (cert observer).install
  rcases Hmodels with ⟨ves', wf', hle, hexact⟩
  refine ⟨ves', wf', hle, ⟨C.extension Hvalid⟩, ?_, fun venvH htypesH => ?_⟩
  · rw [hexact .safe]
    exact (adds .safe).toVEnv
  · rw [hexact .safe]
    rw [← C.typeValues] at htypesH
    exact (B.typesLe htypesH).trans (outputLE .safe)

/-- Declaration-dispatch form of the safe restoration replay theorem. -/
private theorem RestoredBlockCertificate.safeInductiveExtension
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : RestoredBlockCertificate H (ves.venv .safe) decl lparams
      nparams false .safe)
    (wf : ves.WF sourceProdEnv)
    (Horigins : InductInfosFromDecl sourceProdEnv.constants
      outEnv.constants decl)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .safe outEnv
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)))
    (hcover : ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      sourceProdEnv.find? T.name = none)
    {venvH : VEnv}
    (htypesH : (ves.venv .safe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = false ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      false) := by
  rcases C.extendSafe wf Horigins hclosed
      hconstructorOwners hconstructorSemantics hcover htypesH hctorOrigin with
    ⟨ves', wf', hle, ⟨Hfinal⟩, hadd, -⟩
  exact ⟨InductiveExtension.ofModel ves' wf' hle
    { decl := decl
      envTypes := Hfinal.envTypes
      envCtors := Hfinal.envCtors
      source := Hfinal.sourceCore
      extension := hadd }⟩

/-- Safe installed-model assembly with the kernel family lookups discharged
from the closed lowering, the lowered run, and the restoration folds. -/
theorem RestoredBlockCertificate.safeInductiveExtensionOfKernel
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : RestoredBlockCertificate H (ves.venv .safe) decl lparams
      nparams false .safe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams false depth
      (ves.venv .safe) result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (wf : ves.WF sourceProdEnv)
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .safe outEnv
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)))
    {venvH : VEnv}
    (htypesH : (ves.venv .safe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = false ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      false) := by
  have Howners : ConstructorOwnersPresent c.env := by
    rw [henv]
    exact wf.constructorOwners
  exact C.safeInductiveExtension wf
    (C.inductInfosFromDecl Hlower Hc Hprod Hmetadata Hsources Harity
      Howners hempty henv hlparams hnames)
    hclosed
    (H.constructorOwnersPresentOfContext Hlower Hc Hprod Howners hempty henv hnames)
    hconstructorSemantics
    (C.cover Hlower Hc Hprod Hmetadata Hsources Harity Howners hempty henv hlparams hnames)
    htypesH hctorOrigin

/-- An unsafe restoration changes only the unsafe abstract observer.
The premise is indexed by every fresh extension of the restoration, ruling out
an unrelated list of kernel constants; it is precisely the kernel
metadata fact needed to justify `TrEnv'.ignore` at partial and safe. -/
private theorem RestoredBlockCertificate.unsafeInductiveExtension
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : RestoredBlockCertificate H (ves.venv .unsafe) decl lparams
      nparams true .unsafe)
    (wf : ves.WF sourceProdEnv)
    (Horigins : InductInfosFromDecl sourceProdEnv.constants
      outEnv.constants decl)
    (hentriesUnsafe : ∀ entries
      (_Hentries : FreshExtension sourceProdEnv entries outEnv),
      ∀ entry ∈ entries, entry.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .unsafe outEnv
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)))
    (hcover : ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      sourceProdEnv.find? T.name = none)
    {venvH : VEnv}
    (htypesH : (ves.venv .unsafe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = true ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      true) := by
  let B := C.blockCertificate
  have Hvalid : CheckingEnv.Valid .unsafe sourceProdEnv (ves.venv .unsafe) :=
    wf.toCheckingValid (.unsafe)
  let HactualExists : Nonempty { entries : List ConstantInfo //
      FreshExtension sourceProdEnv entries outEnv } := by
    rcases H.freshExtension Hvalid.tr.map_wf with ⟨entries, Hentries⟩
    exact ⟨⟨entries, Hentries⟩⟩
  let actual := Classical.choice HactualExists
  have hperm := C.executableOrder_perm actual.val actual.property
  have hlookup : ∀ name, outEnv.constants.find? name =
      C.installedEnv.constants.find? name :=
    actual.property.lookupEqOfPerm C.install.atomic.freshExtension
      Hvalid.tr.map_wf hperm
  have hlookupEnv : ∀ name, outEnv.find? name =
      C.installedEnv.find? name := by
    intro name
    change outEnv.constants.find?' name =
      C.installedEnv.constants.find?' name
    rw [(actual.property.targetWF Hvalid.tr.map_wf).find?'_eq_find?,
      (C.install.atomic.targetMapWF Hvalid.tr.map_wf).find?'_eq_find?]
    exact hlookup name
  let F := C.extension Hvalid
  have HcheckingRules : CheckingEnv .unsafe outEnv
      (C.recursorVEnv.addDefEqRules
        (C.sourceRules ++ C.auxiliaryRules)) := {
    aligned := aligned_addDefEqs F.checking.aligned
      (C.sourceRules ++ C.auxiliaryRules)
    wf := by
      rcases (wf.tr (safety := .unsafe)).wf with ⟨ds, Hds⟩
      exact ⟨.induct decl :: ds,
        Hds.decl (.induct F.addInduct)⟩
    of_value := by
      intro name ci value hfind hs hvalue
      exact (F.checking.of_value hfind hs hvalue).mono
        VEnv.addDefEqRules_le
  }
  have Hadd : AddInduct .unsafe sourceProdEnv.constants (ves.venv .unsafe)
      decl outEnv.constants
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)) :=
    H.addInductConcrete F.addInduct HcheckingRules C.recursorsAligned Hvalid.tr.map_wf
  have htrUnsafe : TrEnv' .unsafe outEnv.constants outEnv.quotInit
      (C.recursorVEnv.addDefEqRules
        (C.sourceRules ++ C.auxiliaryRules)) := by
    rw [actual.property.quotInit_eq]
    exact .induct Hadd (wf.tr (safety := .unsafe))
  have hactualUnsafe : ∀ entry ∈ actual.val,
      entry.safety = .unsafe := hentriesUnsafe actual.val actual.property
  have htrPartial : TrEnv' .partial outEnv.constants outEnv.quotInit
      (ves.venv .partial) := by
    apply actual.property.trEnvIgnore Hvalid.tr.map_wf
    · intro entry hentry
      rw [hactualUnsafe entry hentry]
      decide
    · exact wf.tr (safety := .partial)
  have htrSafe : TrEnv' .safe outEnv.constants outEnv.quotInit
      (ves.venv .safe) := by
    apply actual.property.trEnvIgnore Hvalid.tr.map_wf
    · intro entry hentry
      rw [hactualUnsafe entry hentry]
      decide
    · exact wf.tr (safety := .safe)
  have hcanonicalUnsafe : ∀ entry ∈
      C.typeEntries ++ C.constructorEntries ++ C.recursorEntries,
      entry.1.safety = .unsafe := by
    intro entry hentry
    have hcanonical : entry.1 ∈
        (C.typeEntries ++ C.constructorEntries ++
          C.recursorEntries).map Prod.fst :=
      List.mem_map.mpr ⟨entry, hentry, rfl⟩
    exact hactualUnsafe entry.1 (hperm.mem_iff.mpr hcanonical)
  have hwf : sourceProdEnv.constants.WF := Hvalid.tr.map_wf
  have houtWF : outEnv.constants.WF := actual.property.targetWF hwf
  have hb : ∀ e ∈ C.typeEntries ++ C.constructorEntries ++ C.recursorEntries,
      e.1.isUnsafe = true := by
    intro e he
    have := hcanonicalUnsafe e he
    cases h : e.1.isUnsafe
    · revert this
      simp only [ConstantInfo.safety, h, Bool.false_eq_true, ↓reduceIte]
      split <;> exact nofun
    · rfl
  have hdeclUnsafe : decl.isUnsafe = true :=
    Horigins.declUnsafe hwf houtWF hcover C.declWF.1.1 fun hv hnone => by
      rw [hlookupEnv] at hv
      simpa [ConstantInfo.isUnsafe] using B.newUnsafe hwf hb hv hnone
  have hrecUnsafe : ∀ {n r}, outEnv.find? n = some (.recInfo r) →
      sourceProdEnv.find? n = none → r.isUnsafe = decl.isUnsafe := by
    intro n r hf hnone
    rw [hlookupEnv] at hf
    rw [hdeclUnsafe]
    simpa [ConstantInfo.isUnsafe] using B.newUnsafe hwf hb hf hnone
  have hrecMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) →
      sourceProdEnv.find? n = none →
      ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info) := by
    intro n r hf hnone
    have hfMap : outEnv.constants.find? n = some (.recInfo r) := by
      rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hf
    rcases C.recursorsAligned.recursor hfMap with hold | hnew
    · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
    · obtain ⟨-, -, info, hmajor⟩ := hnew DefinitionSafety.unsafe_le
      exact ⟨info, by rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]⟩
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci → outEnv.find? n = some ci :=
    fun h => actual.property.preservesSourceFind hwf h
  have hhidden (observer : DefinitionSafety) (hobserver : observer ≠ .unsafe) :
      ¬ observer ≤ (if decl.isUnsafe then .unsafe else .safe) := by
    rw [hdeclUnsafe]
    intro hle
    exact hobserver (DefinitionSafety.le_antisymm hle DefinitionSafety.unsafe_le)
  have hHle : venvH ≤ C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules) := by
    rw [← C.typeValues] at htypesH
    exact B.typesLe htypesH
  have htelsNew : ∀ {venv'}, venvH ≤ venv' → ∀ {n c},
      outEnv.find? n = some (.ctorInfo c) → sourceProdEnv.find? n = none →
      CtorTelescopeAt venv' c := by
    intro venv' hle n c hf hnone
    rcases hctorOrigin hf with hold | ⟨-, htel⟩
    · rw [hold] at hnone; cases hnone
    · exact htel.mono hle
  have hblocks : ∀ observer, InstalledBlocks observer outEnv
      (match observer with
      | .unsafe => C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)
      | .partial => ves.venv .partial
      | .safe => ves.venv .safe) .complete
    | .unsafe => (wf.blocks (safety := .unsafe)).addInduct hwf
        (show TrEnv .unsafe outEnv _ from htrUnsafe).toChecking hpres Hadd.le Horigins
        hcover hclosed hconstructorOwners hrecMajor (fun _ => Hadd)
        (fun h => absurd DefinitionSafety.unsafe_le h) (fun _ => hconstructorSemantics)
        (fun _ => htelsNew hHle) (fun {n r} hf hnone hrvis => by
          have hfMap : outEnv.constants.find? n = some (.recInfo r) := by
            rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hf
          rcases Hadd.newRecursorsAligned.recursor hfMap with hold | hnew
          · rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, hold] at hnone; cases hnone
          · obtain ⟨hcore, hk, -⟩ := hnew hrvis
            exact ⟨hcore, hk⟩)
    | .partial => (wf.blocks (safety := .partial)).addInduct hwf
        (show TrEnv .partial outEnv _ from htrPartial).toChecking hpres VEnv.LE.rfl
        Horigins hcover hclosed hconstructorOwners hrecMajor
        (fun h => absurd h (hhidden .partial (by decide))) (fun _ => rfl)
        (fun h => absurd h (hhidden .partial (by decide)))
        (fun h => absurd h (hhidden .partial (by decide)))
        (fun hf hnone hrvis => absurd (by
          have := hrecUnsafe hf hnone
          simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, this,
            hdeclUnsafe] using hrvis) (hhidden .partial (by decide)))
    | .safe => (wf.blocks (safety := .safe)).addInduct hwf
        (show TrEnv .safe outEnv _ from htrSafe).toChecking hpres VEnv.LE.rfl
        Horigins hcover hclosed hconstructorOwners hrecMajor
        (fun h => absurd h (hhidden .safe (by decide))) (fun _ => rfl)
        (fun h => absurd h (hhidden .safe (by decide)))
        (fun h => absurd h (hhidden .safe (by decide)))
        (fun hf hnone hrvis => absurd (by
          have := hrecUnsafe hf hnone
          simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, this,
            hdeclUnsafe] using hrvis) (hhidden .safe (by decide)))
  have hsafePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci hfind hprimitive
    apply (C.install.validCore Hvalid.toValidCore).safePrimitives
    · rw [← hlookupEnv]
      exact hfind
    · exact hprimitive
  rcases VEnvs.WF.extendUnsafeExact wf
      (C.recursorVEnv.addDefEqRules
        (C.sourceRules ++ C.auxiliaryRules))
      htrUnsafe htrPartial htrSafe
      (B.hasPrimitives (wf.hasPrimitives (safety := .unsafe)))
      hsafePrimitives hblocks (VInductBlock.install_le B.install) with
    ⟨ves', wf', hle, hexact⟩
  have haddExact : VEnv.AddInduct (ves.venv .unsafe) decl
      (ves'.venv .unsafe) := by
    rw [hexact]
    exact Hadd.toVEnv
  exact ⟨InductiveExtension.ofModel ves' wf' hle
    { decl := decl
      envTypes := F.envTypes
      envCtors := F.envCtors
      source := F.sourceCore
      extension := haddExact }⟩

/-- Unsafe installed-model assembly with the kernel family lookups discharged
from the closed lowering, the lowered run, and the restoration folds. -/
theorem RestoredBlockCertificate.unsafeInductiveExtensionOfKernel
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    (C : RestoredBlockCertificate H (ves.venv .unsafe) decl lparams
      nparams true .unsafe)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams true depth
      (ves.venv .unsafe) result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {fuel : Nat} {initialState : Lean4Lean.ElimNestedInductive.State}
    (wf : ves.WF sourceProdEnv)
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hmetadata : SourcePrefixOfLowered decl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : decl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (henv : c.env = sourceProdEnv) (hlparams : c.lparams = lparams)
    (hnames : allIndNames = sourceTypes.map (fun type => type.name))
    (hentriesUnsafe : ∀ entries
      (_Hentries : FreshExtension sourceProdEnv entries outEnv),
      ∀ entry ∈ entries, entry.safety = .unsafe)
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorSemantics :
      ConstructorParameterAlignment .unsafe outEnv
        (C.recursorVEnv.addDefEqRules
          (C.sourceRules ++ C.auxiliaryRules)))
    {venvH : VEnv}
    (htypesH : (ves.venv .unsafe).addConstVals decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = true ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      true) := by
  have Howners : ConstructorOwnersPresent c.env := by
    rw [henv]
    exact wf.constructorOwners
  exact C.unsafeInductiveExtension wf
    (C.inductInfosFromDecl Hlower Hc Hprod Hmetadata Hsources Harity
      Howners hempty henv hlparams hnames)
    hentriesUnsafe hclosed
    (H.constructorOwnersPresentOfContext Hlower Hc Hprod Howners hempty henv hnames)
    hconstructorSemantics
    (C.cover Hlower Hc Hprod Hmetadata Hsources Harity Howners hempty henv hlparams hnames)
    htypesH hctorOrigin

end VerifyInductive
end Lean4Lean
