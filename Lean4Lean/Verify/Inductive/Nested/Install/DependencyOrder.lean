import Lean4Lean.Verify.Inductive.Nested.Install.Permutation
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledFamilyLookups
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryRecursorsWF
import Lean4Lean.Verify.Inductive.Nested.Restoration.Nonprimitive

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

theorem AtomicAddConstants.freshExtension
    (H : AtomicAddConstants safety source sourceVEnv entries target targetVEnv) :
    FreshExtension source (entries.map Prod.fst) target := by
  induction H with
  | nil => exact .nil
  | cons hfresh _ _ _ _ _ ih => exact .cons hfresh ih

/-- Transfer the validity proved by a dependency-ordered block installation
to a concrete installation of the same constants in any fresh order.  The
permutation argument is used only to identify kernel constant maps; abstract
typing remains tied to the header/constructor/projection/recursor stages. -/
theorem BlockInstallation.validCoreOfFreshPermutation
    (H : BlockInstallation safety source sourceVEnv types ctors recursors
      projections canonicalTarget targetVEnv)
    (Hactual : FreshExtension source actualEntries actualTarget)
    (hperm : actualEntries ~ (types ++ ctors ++ recursors).map Prod.fst)
    (Hsource : CheckingEnv.ValidCore safety source sourceVEnv) :
    CheckingEnv.ValidCore safety actualTarget targetVEnv := by
  have HcanonicalValid := H.validCore Hsource
  have heq := Hactual.lookupEqOfPerm H.atomic.freshExtension
    Hsource.tr.map_wf hperm
  exact CheckingEnv.ValidCore.mapExt HcanonicalValid
    (Hactual.targetWF Hsource.tr.map_wf) fun name => (heq name).symm

open private Lean.Kernel.Environment.add from Lean.Environment

/-! # Dependency-order replay of a fresh restoration batch

Restoration installs declarations family by family, whereas the abstract
inductive judgment checks all headers, then all constructors, then all
recursors.  This file relates the two orders.  It does not assume an endpoint
correspondence: a fresh extension is replayed in any permutation, and the
endpoint correspondence is then proved extensionally.
-/

/-- A finite list of pairwise-distinct constants that is fresh in the source
environment can be installed in its listed order. -/
theorem FreshExtension.exists_of_sourceFresh_nodup
    (hsourceWF : source.constants.WF)
    (hsourceFresh : ∀ ci ∈ entries, source.find? ci.name = none)
    (hnodup : (entries.map (·.name)).Nodup) :
    ∃ target, FreshExtension source entries target := by
  induction entries generalizing source with
  | nil => exact ⟨source, .nil⟩
  | cons ci entries ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    have hciFresh : source.find? ci.name = none :=
      hsourceFresh ci (by simp)
    have hnextWF : (source.add ci).constants.WF :=
      constantsWF_add_checked hsourceWF hciFresh
    have htailFresh : ∀ entry ∈ entries,
        (source.add ci).find? entry.name = none := by
      intro entry hentry
      apply Environment.find?_add_of_ne hsourceWF ci hciFresh
      · intro heq
        exact hnodup.1 (List.mem_map.mpr ⟨entry, hentry, heq.symm⟩)
      · exact hsourceFresh entry (by simp [hentry])
    rcases ih hnextWF htailFresh hnodup.2 with ⟨target, Htail⟩
    exact ⟨target, .cons hciFresh Htail⟩

/-- Replay a fresh extension of the kernel environment in any permuted order. -/
theorem FreshExtension.exists_permuted
    (H : FreshExtension source actualEntries actualTarget)
    (hsourceWF : source.constants.WF)
    (hperm : actualEntries ~ canonicalEntries) :
    ∃ canonicalTarget,
      FreshExtension source canonicalEntries canonicalTarget := by
  apply FreshExtension.exists_of_sourceFresh_nodup hsourceWF
  · intro ci hci
    exact H.sourceFresh hsourceWF (hperm.mem_iff.mpr hci)
  · exact (hperm.map (·.name)).nodup_iff.mp (H.namesNodup hsourceWF)

/-- The endpoint of the permuted replay has exactly the lookup behavior of
the executable restoration endpoint. -/
theorem FreshExtension.exists_permuted_lookupEq
    (H : FreshExtension source actualEntries actualTarget)
    (hsourceWF : source.constants.WF)
    (hperm : actualEntries ~ canonicalEntries) :
    ∃ canonicalTarget,
      FreshExtension source canonicalEntries canonicalTarget ∧
      ∀ name, actualTarget.constants.find? name =
        canonicalTarget.constants.find? name := by
  rcases H.exists_permuted hsourceWF hperm with
    ⟨canonicalTarget, Hcanonical⟩
  exact ⟨canonicalTarget, Hcanonical,
    H.lookupEqOfPerm Hcanonical hsourceWF hperm⟩

/-- Split a fresh replay at an exact list boundary, retaining the concrete
intermediate environment produced by the prefix. -/
theorem FreshExtension.split_append
    (H : FreshExtension source (firstEntries ++ suffix) target) :
    ∃ middle, FreshExtension source firstEntries middle ∧
      FreshExtension middle suffix target := by
  induction firstEntries generalizing source with
  | nil => exact ⟨source, .nil, H⟩
  | cons head tail ih =>
    cases H with
    | cons hfresh Htail =>
      rcases ih Htail with ⟨middle, Hprefix, Hsuffix⟩
      exact ⟨middle, .cons hfresh Hprefix, Hsuffix⟩

/-- A pointwise property of the payload of one exact fresh replay transfers
to every entry of another replay with the same source and target.  This is
the property-level form of order-insensitive restoration alignment. -/
theorem FreshExtension.transferForallSameTarget
    {P : ConstantInfo → Prop}
    (Hleft : FreshExtension source leftEntries target)
    (Hright : FreshExtension source rightEntries target)
    (hsourceWF : source.constants.WF)
    (hproperty : ∀ entry ∈ rightEntries, P entry) :
    ∀ entry ∈ leftEntries, P entry := by
  intro entry hentry
  have hfind := Hleft.findEntry hsourceWF hentry
  rcases Hright.entryOrigin hsourceWF hfind with hsource |
      ⟨found, hfound, _hname, heq⟩
  · rw [Hleft.sourceFresh hsourceWF hentry] at hsource
    contradiction
  · simpa [heq] using hproperty found hfound

/-- Turn a fresh concrete replay and an exact abstract `addConstVals` result
into the lockstep `AddConstants` certificate.  Translation and typing may be
proved in a fixed smaller environment; monotonicity transports them to each
successive abstract installation point. -/
theorem AddConstants.ofFreshAbstract
    (Hfresh : FreshExtension prodEnv (entries.map Prod.fst) outProd)
    (Htranslated : ∀ entry ∈ entries,
      TrConstVal safety base entry.1 entry.2)
    (Hwf : ∀ entry ∈ entries, entry.2.toVConstant.WF base)
    (Hnonprimitive : ∀ entry ∈ entries,
      ¬ Kernel.Environment.primitives.contains entry.1.name)
    (Hnondelta : ∀ entry ∈ entries, entry.1.deltaValue? = none)
    (Habstract : venv.addConstVals (entries.map Prod.snd) = some outVEnv)
    (hle : base ≤ venv) :
    AddConstants safety prodEnv venv entries outProd outVEnv := by
  induction entries generalizing prodEnv venv outProd outVEnv with
  | nil =>
    cases Hfresh
    have hout : venv = outVEnv := by
      simpa using Option.some.inj Habstract
    subst outVEnv
    exact .nil
  | cons entry entries ih =>
    simp only [List.map_cons] at Hfresh Habstract
    cases Hfresh with
    | cons hfresh Htail =>
      simp only [VEnv.addConstVals] at Habstract
      cases hadd : venv.addConst entry.2.name entry.2.toVConstant with
      | none => simp [hadd] at Habstract
      | some nextVEnv =>
        rw [hadd] at Habstract
        have htr := (Htranslated entry (by simp)).mono hle
        have hwf := (Hwf entry (by simp)).mono hle
        have hname : entry.1.name = entry.2.name := htr.2
        have hadd' : venv.addConst entry.1.name entry.2.toVConstant =
            some nextVEnv := by simpa [hname] using hadd
        apply AddConstants.cons hfresh
          (Hnonprimitive entry (by simp)) htr hwf hadd'
          (Hnondelta entry (by simp))
        apply ih Htail
        · intro tail htail
          exact Htranslated tail (by simp [htail])
        · intro tail htail
          exact Hwf tail (by simp [htail])
        · intro tail htail
          exact Hnonprimitive tail (by simp [htail])
        · intro tail htail
          exact Hnondelta tail (by simp [htail])
        · exact Habstract
        · exact hle.trans (VEnv.addConst_le hadd)

/-- Construct the abstract endpoint while replaying an exact fresh concrete
batch.  No abstract environment is selected by a caller: freshness and the
checking invariant force each successive `addConst` to succeed. -/
theorem AddConstants.exists_ofFresh
    (Hfresh : FreshExtension prodEnv (entries.map Prod.fst) outProd)
    (Htranslated : ∀ entry ∈ entries,
      TrConstVal safety base entry.1 entry.2)
    (Hwf : ∀ entry ∈ entries, entry.2.toVConstant.WF base)
    (Hnonprimitive : ∀ entry ∈ entries,
      ¬ Kernel.Environment.primitives.contains entry.1.name)
    (Hnondelta : ∀ entry ∈ entries, entry.1.deltaValue? = none)
    (Hchecking : CheckingEnv safety prodEnv venv)
    (hle : base ≤ venv) :
    ∃ outVEnv, AddConstants safety prodEnv venv entries outProd outVEnv := by
  induction entries generalizing prodEnv venv outProd with
  | nil =>
    cases Hfresh
    exact ⟨venv, .nil⟩
  | cons entry entries ih =>
    simp only [List.map_cons] at Hfresh
    cases Hfresh with
    | cons hfresh Htail =>
      have htr := (Htranslated entry (by simp)).mono hle
      have hwf := (Hwf entry (by simp)).mono hle
      rcases CheckingEnv.exists_addConst Hchecking hfresh
          entry.2.toVConstant with ⟨nextVEnv, hadd⟩
      have HcheckingNext : CheckingEnv safety (prodEnv.add entry.1)
          nextVEnv := Hchecking.add hfresh htr.1 hwf hadd
            (Hnondelta entry (by simp))
      rcases ih Htail
          (fun tail htail => Htranslated tail (by simp [htail]))
          (fun tail htail => Hwf tail (by simp [htail]))
          (fun tail htail => Hnonprimitive tail (by simp [htail]))
          (fun tail htail => Hnondelta tail (by simp [htail]))
          HcheckingNext (hle.trans (VEnv.addConst_le hadd)) with
        ⟨outVEnv, Hrest⟩
      exact ⟨outVEnv, .cons hfresh (Hnonprimitive entry (by simp)) htr hwf
        hadd (Hnondelta entry (by simp)) Hrest⟩

/-- The exact restored header selected by one family restoration step
translates to the independently specified source-family constant.  All
concrete metadata comes from the lowered run at the same lowering
index; lowering's family mapping supplies the unchanged source name and
type. -/
theorem RestoredInductiveStep.restoredHeaderTranslationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      stepSource stepTarget)
    (Hheader : TrSourceConst sourceVEnv c.lparams
      sourceTypes[familyIdx].name sourceTypes[familyIdx].type header)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    TrConstVal c.safety sourceVEnv
      (.inductInfo Hstep.restored.header.newInfo) header := by
  rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _mappingState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultFamily, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hresultArray : familyIdx < result.types.toArray.size := by
    simpa using hresultFamily
  have htargetArrayEq : result.types.toArray[familyIdx] = target := by
    simpa using htargetEq
  rcases Hprod.findSourceHeaderAt familyIdx hresultArray with
    ⟨installedInfo, hinstalledLookup, hinstalledName, hinstalledType,
      _hinstalledCtors, _hinstalledAll, hinstalledLevels,
      _hinstalledParams, hinstalledUnsafe⟩
  have hinstalledLookup' : loweredEnv.find? target.name =
      some (.inductInfo installedInfo) := by
    simpa [htargetArrayEq] using hinstalledLookup
  have hstepLookup : loweredEnv.find? target.name =
      some (.inductInfo Hstep.oldInfo) := by
    rw [Hmapping.name]
    exact Hstep.lookup
  have holdInfo : Hstep.oldInfo = installedInfo :=
    ConstantInfo.inductInfo.inj
      (Option.some.inj (hstepLookup.symm.trans hinstalledLookup'))
  apply Hstep.restored.header.translated
  apply Lean4Lean.VerifyInductive.TrSourceConst.inductInfo Hheader
  · calc
      Hstep.oldInfo.levelParams = installedInfo.levelParams := by
        rw [holdInfo]
      _ = c.lparams := hinstalledLevels
  · calc
      Hstep.oldInfo.name = installedInfo.name := by rw [holdInfo]
      _ = target.name := by simpa [htargetArrayEq] using hinstalledName
      _ = sourceTypes[familyIdx].name := Hmapping.name
  · calc
      Hstep.oldInfo.type = installedInfo.type := by rw [holdInfo]
      _ = target.type := by simpa [htargetArrayEq] using hinstalledType
      _ = sourceTypes[familyIdx].type := Hmapping.type
  · have holdUnsafe : Hstep.oldInfo.isUnsafe = isUnsafe := by
      calc
        Hstep.oldInfo.isUnsafe = installedInfo.isUnsafe := by rw [holdInfo]
        _ = isUnsafe := hinstalledUnsafe
    simpa [holdUnsafe] using hvisible

/-- Constructor translations and the executable constructor fold select the
same exact concrete entries, not merely entries with matching names. -/
theorem RestoredConstructorTranslations.existsEntriesFresh
    (H : RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv names
      sourceProdEnv targetProdEnv sources constructors)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries : List (ConstantInfo × VConstVal),
      FreshExtension sourceProdEnv (entries.map Prod.fst) targetProdEnv ∧
      entries.map Prod.snd = constructors ∧
      ∀ entry ∈ entries,
        TrConstVal safety canonicalEnv entry.1 entry.2 ∧
        entry.2.toVConstant.WF canonicalEnv := by
  induction H with
  | nil => exact ⟨[], .nil, rfl, by simp⟩
  | @cons ctorName stepSource middleSource source tailNames
      stepTarget tailSources tailConstructors Hstep Hsemantic Hrest ih =>
    let head : ConstantInfo × VConstVal :=
      (.ctorInfo Hstep.restored.newInfo, Hsemantic.constructor)
    have hheadFresh : stepSource.find? head.1.name = none :=
      find?_none_of_contains_false hsourceWF Hstep.restored.fresh
    have hmiddle : middleSource = stepSource.add head.1 :=
      congrArg Prod.snd Hstep.restored.output
    have hmiddleWF : middleSource.constants.WF :=
      hmiddle.symm ▸ constantsWF_add_checked hsourceWF hheadFresh
    rcases ih hmiddleWF with ⟨entries, Hfresh, hvalues, Hentries⟩
    have Hfresh' : FreshExtension (stepSource.add head.1)
        (entries.map Prod.fst) stepTarget := by
      rw [← hmiddle]
      exact Hfresh
    refine ⟨head :: entries, .cons hheadFresh Hfresh',
      by simp [head, hvalues], ?_⟩
    intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | htail
    · exact ⟨Hsemantic.restoredTranslation,
        Hsemantic.sourceTranslation.wf⟩
    · exact Hentries entry htail

/-- Regroup one family-interleaved constant segment into global dependency
order. -/
private theorem perm_group_familyEntries
    (header recursor : α)
    (tailTypes familyCtors tailCtors tailRecursors : List α) :
    (header :: tailTypes) ++ (familyCtors ++ tailCtors) ++
        (recursor :: tailRecursors) ~
      (header :: familyCtors ++ [recursor]) ++
        (tailTypes ++ tailCtors ++ tailRecursors) := by
  apply List.Perm.cons header
  have htypes : tailTypes ++ familyCtors ~ familyCtors ++ tailTypes :=
    List.perm_append_comm
  have hfirst :
      tailTypes ++ familyCtors ++ tailCtors ++ recursor :: tailRecursors ~
        familyCtors ++ tailTypes ++ tailCtors ++ recursor :: tailRecursors := by
    simpa only [List.append_assoc] using
      htypes.append_right (tailCtors ++ recursor :: tailRecursors)
  have hrecursor : tailTypes ++ tailCtors ++ [recursor] ~
      [recursor] ++ tailTypes ++ tailCtors := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm :
        (tailTypes ++ tailCtors) ++ [recursor] ~
          [recursor] ++ (tailTypes ++ tailCtors))
  have hsecond :
      familyCtors ++ tailTypes ++ tailCtors ++ recursor :: tailRecursors ~
        familyCtors ++
          (recursor :: (tailTypes ++ tailCtors ++ tailRecursors)) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using
      (List.Perm.refl familyCtors).append
        (hrecursor.append_right tailRecursors)
  have h := hfirst.trans hsecond
  have hleft :
      (tailTypes.append (familyCtors ++ tailCtors)).append
          (recursor :: tailRecursors) =
        ((tailTypes.append familyCtors).append tailCtors).append
          (recursor :: tailRecursors) := by
    exact congrArg (· ++ (recursor :: tailRecursors))
      (List.append_assoc tailTypes familyCtors tailCtors).symm
  have hright :
      (familyCtors.append [recursor]).append
          (tailTypes ++ tailCtors ++ tailRecursors) =
        familyCtors ++
          (recursor :: (tailTypes ++ tailCtors ++ tailRecursors)) := by
    exact (List.append_assoc familyCtors [recursor]
      (tailTypes ++ tailCtors ++ tailRecursors)).trans <|
        congrArg (familyCtors ++ ·) List.singleton_append
  exact hleft.symm ▸ hright.symm ▸ h

/-- Source-family restoration replay, retaining both the executable's
family-interleaved order and dependency order. -/
structure SourceFamilyTranslations.InDependencyOrder
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {primaryRecursors : List VConstVal}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners primaryRecursors)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (actualEntries : List ConstantInfo) : Prop where
  fresh : FreshExtension sourceProdEnv actualEntries targetProdEnv
  kernelOrder : actualEntries ~
    (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  typeValues : typeEntries.map Prod.snd =
    owners.map VInductiveType.toVConstVal
  constructorValues : constructorEntries.map Prod.snd =
    owners.flatMap VInductiveType.ctors
  recursorValues : recursorEntries.map Prod.snd = primaryRecursors
  types : ∀ entry ∈ typeEntries,
    TrConstVal safety sourceVEnv entry.1 entry.2 ∧
      entry.2.toVConstant.WF sourceVEnv
  constructors : ∀ entry ∈ constructorEntries,
    TrConstVal safety envTypes entry.1 entry.2 ∧
      entry.2.toVConstant.WF envTypes
  recursors : ∀ entry ∈ recursorEntries,
    TrConstVal safety envCtors entry.1 entry.2 ∧
      entry.2.toVConstant.WF envCtors

/-- Fold the exact source semantics together with the exact executable
restoration steps.  The result proves the grouping permutation;
it does not ask a caller to identify two independently selected endpoints. -/
theorem SourceFamilyTranslations.existsInDependencyOrder
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {primaryRecursors : List VConstVal}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners primaryRecursors)
    (Hheaders : ∀ indType stepSource stepTarget (owner : VInductiveType)
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal) →
      TrConstVal safety sourceVEnv
        (.inductInfo Hstep.restored.header.newInfo) owner.toVConstVal)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ typeEntries constructorEntries recursorEntries actualEntries,
      H.InDependencyOrder typeEntries constructorEntries recursorEntries
        actualEntries := by
  induction H with
  | nil => exact ⟨[], [], [], [], {
      fresh := .nil
      kernelOrder := .refl []
      typeValues := rfl
      constructorValues := rfl
      recursorValues := rfl
      types := by simp
      constructors := by simp
      recursors := by simp }⟩
  | @cons indType stepSource middleSource tailTypesSource stepTarget owner
      tailOwners tailRecursors Hstep Htail Hheader Hconstructors Hrecursor
      Hrest ih =>
    have HheaderTr := Hheaders _ _ _ _ Hstep (by simp) Hheader
    let headerEntry : ConstantInfo × VConstVal :=
      (.inductInfo Hstep.restored.header.newInfo, owner.toVConstVal)
    have hheaderFresh : stepSource.find? headerEntry.1.name = none :=
      find?_none_of_contains_false hsourceWF Hstep.restored.header.fresh
    have hheaderEnv : Hstep.restored.headerEnv =
        stepSource.add headerEntry.1 :=
      congrArg Prod.snd Hstep.restored.header.output
    have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
      hheaderEnv.symm ▸ constantsWF_add_checked hsourceWF hheaderFresh
    rcases Hconstructors.existsEntriesFresh hheaderWF with
      ⟨familyConstructors, HconstructorFresh, hconstructorValues,
        HconstructorEntries⟩
    have HconstructorFresh' : FreshExtension
        (stepSource.add headerEntry.1) (familyConstructors.map Prod.fst)
          Hstep.restored.constructorEnv := by
      rw [← hheaderEnv]
      exact HconstructorFresh
    have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
      HconstructorFresh.targetWF hheaderWF
    let recursorEntry : ConstantInfo × VConstVal :=
      (.recInfo Hstep.restored.recursor.restored.newInfo,
        Hrecursor.recursor)
    have hrecursorFresh : Hstep.restored.constructorEnv.find?
        recursorEntry.1.name = none :=
      find?_none_of_contains_false hconstructorWF
        Hstep.restored.recursor.restored.fresh
    have htarget : middleSource =
        Hstep.restored.constructorEnv.add recursorEntry.1 :=
      congrArg (fun out : Unit × Environment => out.2)
        Hstep.restored.recursor.restored.output
    have HrecursorFresh : FreshExtension
        Hstep.restored.constructorEnv [recursorEntry.1] middleSource := by
      have Hraw : FreshExtension Hstep.restored.constructorEnv
          [recursorEntry.1]
          (Hstep.restored.constructorEnv.add recursorEntry.1) :=
        .cons hrecursorFresh .nil
      exact Eq.mp (congrArg (fun target => FreshExtension
        Hstep.restored.constructorEnv [recursorEntry.1] target) htarget).symm
          Hraw
    let familyEntries : List ConstantInfo :=
      headerEntry.1 :: familyConstructors.map Prod.fst ++ [recursorEntry.1]
    have HfamilyFresh : FreshExtension stepSource familyEntries
        middleSource := by
      exact .cons hheaderFresh
        (HconstructorFresh'.append HrecursorFresh)
    have hstepTargetWF : middleSource.constants.WF :=
      HfamilyFresh.targetWF hsourceWF
    rcases ih (fun indType stepSource stepTarget owner Hstep hmem Hheader =>
      Hheaders indType stepSource stepTarget owner Hstep (by simp [hmem])
        Hheader) hstepTargetWF with
      ⟨tailTypes, tailConstructors, tailRecursorEntries, tailActual,
        HtailReplay⟩
    let typeEntries := headerEntry :: tailTypes
    let constructorEntries := familyConstructors ++ tailConstructors
    let recursorEntries := recursorEntry :: tailRecursorEntries
    let actualEntries := familyEntries ++ tailActual
    have Hfresh : FreshExtension stepSource actualEntries
        stepTarget := HfamilyFresh.append HtailReplay.fresh
    have hgroup := perm_group_familyEntries headerEntry recursorEntry
      tailTypes familyConstructors tailConstructors tailRecursorEntries
    have hfamilyTail : familyEntries ++ tailActual ~
        familyEntries ++
          (tailTypes ++ tailConstructors ++ tailRecursorEntries).map
            Prod.fst := by
      apply (List.Perm.refl familyEntries).append
      exact HtailReplay.kernelOrder
    have hgrouped :
        (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst ~
          familyEntries ++
            (tailTypes ++ tailConstructors ++ tailRecursorEntries).map
              Prod.fst := by
      simpa [typeEntries, constructorEntries, recursorEntries, familyEntries]
        using hgroup.map Prod.fst
    refine ⟨typeEntries, constructorEntries, recursorEntries, actualEntries, {
      fresh := Hfresh
      kernelOrder := hfamilyTail.trans hgrouped.symm
      typeValues := ?_
      constructorValues := ?_
      recursorValues := ?_
      types := ?_
      constructors := ?_
      recursors := ?_ }⟩
    · simp [typeEntries, headerEntry, HtailReplay.typeValues]
    · simp [constructorEntries, hconstructorValues,
        HtailReplay.constructorValues]
    · simp [recursorEntries, recursorEntry, HtailReplay.recursorValues]
    · intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | htail
      · exact ⟨HheaderTr, Hheader.wf⟩
      · exact HtailReplay.types entry htail
    · intro entry hentry
      rcases List.mem_append.mp hentry with hhead | htail
      · exact HconstructorEntries entry hhead
      · exact HtailReplay.constructors entry htail
    · intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | htail
      · refine ⟨?_, Hrecursor.wf⟩
        exact Hstep.restored.recursor.restored.restoration.translatedOfMetadata
          Hrecursor.safety_le Hrecursor.uvars Hrecursor.type Hrecursor.name
      · exact HtailReplay.recursors entry htail

/-- Specialization of `SourceFamilyTranslations.existsInDependencyOrder` to
the lowering and the lowered run.  The returned order permutation and all
three source batches are consequences of the executable runs. -/
theorem SourceFamilyTranslations.existsExactCanonicalSourceReplay
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv sourceProdEnv targetProdEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      sourceTypes sourceProdEnv targetProdEnv}
    {primaryRecursors : List VConstVal}
    (H : SourceFamilyTranslations decl c.lparams c.safety
      sourceVEnv envTypes envCtors Htrace owners primaryRecursors)
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ typeEntries constructorEntries recursorEntries actualEntries,
      H.InDependencyOrder typeEntries constructorEntries recursorEntries
        actualEntries := by
  apply H.existsInDependencyOrder
  · intro indType stepSource stepTarget owner Hstep hmem Hheader
    rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
    subst indType
    exact Hstep.restoredHeaderTranslationAtFresh Hlower Hprod hempty
      familyIdx hfamily Hheader hvisible
  · exact hsourceWF

/-- The pre-rule semantic content of one restored auxiliary recursor.  This
record deliberately does not mention the installed block, generated name scheme,
or any restored rule: only the concrete recursor translation and its
well-formedness are needed to construct the recursor environment. -/
structure AuxiliaryRecursorTranslation
    (safety : DefinitionSafety) (trEnv recursorEnv : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv) where
  recursor : VConstVal
  translated : TrConstVal safety trEnv
    (.recInfo Hstep.restored.newInfo) recursor
  wf : recursor.toVConstant.WF recursorEnv

/-- Construct the pre-rule recursor payload from the exact translated and
typed restored telescope.  Names and universe arity are fixed directly by
the executable `RecursorVal`; no separately chosen abstract constant remains. -/
def AuxiliaryRecursorTranslation.ofTypeTranslation
    (targetType : VExpr)
    (hsafety : safety ≤ (ConstantInfo.recInfo
      Hstep.restored.newInfo).safety)
    (Htranslation : TrExprS trEnv Hstep.restored.newInfo.levelParams []
      Hstep.restored.newInfo.type targetType)
    (Htype : recursorEnv.IsType Hstep.restored.newInfo.levelParams.length []
      targetType) :
    AuxiliaryRecursorTranslation safety trEnv recursorEnv Hstep where
  recursor := {
    name := Hstep.restored.newInfo.name
    uvars := Hstep.restored.newInfo.levelParams.length
    type := targetType }
  translated := ⟨⟨hsafety, rfl, Htranslation⟩, rfl⟩
  wf := Htype

/-- A restoration step whose source name occurs in the exact generated
recursor batch determines its generated owner and complete restoration
telescope alignment.  No semantic recursor payload is selected here: the
installed entry position and the concrete restoration lookup force the
owner and old `RecursorVal`. -/
theorem RecursorCheck.restoredTelescopeAlignmentOfGeneratedName
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (hgenerated : oldRecName ∈
      (Hprod.entries.map Prod.snd).map (·.name))
    (hresultNparams : result.nparams = nparams)
    (hresultParams : result.params.size = result.nparams) :
    ∃ ownerIdx, ∃ hentry : ownerIdx < Hprod.entries.length,
      oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name ∧
        Nonempty (RestoredRecursorTelescopeAlignment result
          loweredEnv auxRec Hstep.restored.newInfo
            (Hprod.generated.entry ownerIdx hentry)) := by
  rcases List.mem_map.mp hgenerated with ⟨value, hvalue, hvalueName⟩
  rcases List.mem_iff_getElem.mp hvalue with ⟨ownerIdx, hentry, hentryValue⟩
  have hentry' : ownerIdx < Hprod.entries.length := by simpa using hentry
  let E := Hprod.generated.entry ownerIdx hentry'
  have hentryValue' : Hprod.entries[ownerIdx].2 = value := by
    simpa using hentryValue
  have hentryNames : Hprod.entries[ownerIdx].1.name =
      Hprod.entries[ownerIdx].2.name :=
    Hprod.installed.entryNames (List.getElem_mem hentry')
  have holdRecName : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name := by
    calc
      oldRecName = value.name := hvalueName.symm
      _ = Hprod.entries[ownerIdx].2.name := by rw [hentryValue']
      _ = Hprod.entries[ownerIdx].1.name := hentryNames.symm
      _ = E.info.name := by
        rw [E.source_eq]
        rfl
      _ = Lean.mkRecName indTypes[ownerIdx]!.name := E.name
  exact ⟨ownerIdx, hentry', holdRecName,
    Hprod.restoredSourceTelescopeAlignment ownerIdx hentry' Hstep
      holdRecName hresultNparams hresultParams⟩

/-- Generated-entry alignment for one concrete auxiliary restoration
step.  The owner is an output, not a caller-selected index. -/
structure AuxiliaryRecursorGeneratedAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv) where
  ownerIdx : Nat
  entry_lt : ownerIdx < Hprod.entries.length
  oldRecName_eq : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name
  alignment : RestoredRecursorTelescopeAlignment result
    loweredEnv auxRec Hstep.restored.newInfo
      (Hprod.generated.entry ownerIdx entry_lt)

/-- The concrete auxiliary fold, together with generated-name membership,
determines a generated-entry telescope alignment at every state transition.
This relation retains no translated target and no caller-supplied step
semantics. -/
inductive AuxiliaryRecursorGeneratedAlignments
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {auxRec : NameMap Name} {allIndNames : List Name} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment},
      FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv → Prop
  | nil (sourceEnv : Environment) :
      AuxiliaryRecursorGeneratedAlignments Hprod (.nil)
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hhead : AuxiliaryRecursorGeneratedAlignment Hprod Hstep)
      (Hrest : AuxiliaryRecursorGeneratedAlignments Hprod Htail) :
      AuxiliaryRecursorGeneratedAlignments Hprod (.cons Hstep Htail)

theorem FoldSteps.generatedAlignmentTrace
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    (Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hgenerated : ∀ name ∈ names,
      name ∈ (Hprod.entries.map Prod.snd).map (·.name))
    (hresultNparams : result.nparams = nparams)
    (hresultParams : result.params.size = result.nparams) :
    AuxiliaryRecursorGeneratedAlignments Hprod Htrace := by
  induction Htrace with
  | @nil source => exact .nil source
  | @cons head source middle tail target Hstep Htail ih =>
      rcases Hprod.restoredTelescopeAlignmentOfGeneratedName Hstep
          (hgenerated head (by simp)) hresultNparams hresultParams with
        ⟨ownerIdx, hentry, holdRecName, ⟨Halignment⟩⟩
      have hgeneratedTail : ∀ name ∈ tail,
          name ∈ (Hprod.entries.map Prod.snd).map (·.name) := by
        intro name hname
        exact hgenerated name (by simp [hname])
      exact .cons Hstep Htail ⟨ownerIdx, hentry, holdRecName, Halignment⟩
        (ih hgeneratedTail)

/-- Every name selected by the executable auxiliary-recursion suffix is an
entry of the exact generated recursor batch.  The proof follows the fresh
lowering queue and `mkAuxRecNameMap`; no name-based semantic lookup is
assumed. -/
theorem NestedLoweringOutputClosed.auxRecNameGeneratedAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (hrecName : recName ∈
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1) :
    recName ∈ (Hprod.entries.map Prod.snd).map (·.name) := by
  rcases Hlower.sourceResolvedMappingAtFreshAligned hempty (j := 0) (by simp) with
    ⟨_mainFVars, _mainState, mainTarget, _mainLoweredState, _mainParams,
      _mainNodup, _mainSize, Hmain, hmainTarget⟩
  have hmainMem : mainTarget ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? hmainTarget
  rcases Hprod.findSourceHeader Hc hmainMem with
    ⟨mainInfo, hmainFind, _hmainCtors, hall⟩
  have hmainFind' : loweredEnv.find? main.name =
      some (.inductInfo mainInfo) := by
    have hmainName : mainTarget.name = main.name := by
      simpa using Hmain.name
    rw [← hmainName]
    exact hmainFind
  rcases mkAuxRecNameMap_recNames_mem main rest loweredEnv mainInfo hmainFind'
      hrecName with ⟨familyName, hfamilyName, hrecEq⟩
  rw [hall] at hfamilyName
  rcases List.mem_map.mp hfamilyName with
    ⟨family, hfamily, hfamilyEq⟩
  rcases List.mem_iff_getElem.mp hfamily with
    ⟨familyIdx, hfamilyIdx, hfamilyGet⟩
  have hrecords : Hprod.recInfos.size = result.types.toArray.size := by
    rw [Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simp
  have hgenerated := Hprod.generated.recursorName_mem hrecords familyIdx
    (by simpa using hfamilyIdx)
  have hget : result.types.toArray[familyIdx]! =
      result.types.toArray.toList[familyIdx] := by
    rw [Array.getElem!_eq_getD,
      ← Array.getElem_eq_getD (h := by simpa using hfamilyIdx) default]
    exact (Array.getElem_toList hfamilyIdx).symm
  have hname : recName =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rw [hrecEq, ← hfamilyEq, ← hfamilyGet, ← hget]
  rwa [hname]

/-- The restoration folds of the kernel environment carry generated-entry
alignment at every auxiliary state transition.  This is the structural
predecessor of restored recursor translation/WF construction. -/
theorem NestedRestorationFolds.generatedAlignmentTraceOfKernel
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).2
      ((main :: rest).map (fun type => type.name)) (main :: rest)
      (Lean4Lean.mkAuxRecNameMap loweredEnv (main :: rest)).1
      ((), targetProdEnv)) :
    AuxiliaryRecursorGeneratedAlignments Hprod H.auxiliaries := by
  apply H.auxiliaries.generatedAlignmentTrace Hprod
  · intro name hname
    exact Hlower.auxRecNameGeneratedAtFresh Hc Hprod hempty hname
  · exact Hlower.toResult.resultNParams
  · exact Hlower.resultParamsSize

/-- Pre-rule auxiliary recursor translations, synchronized directly with
the executable restoration fold.  Unlike
`RestoredAuxiliaryRecursorsWF`, this relation has no dependency on an
already selected block or rule semantics, so it can be used to construct the
recursor environment without a circular premise. -/
inductive AuxiliaryRecursorTranslations
    (safety : DefinitionSafety) (trEnv recursorEnv : VEnv)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment},
      FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv →
      List VConstVal → List VConstVal → Prop
  | nil (sourceEnv : Environment) (recursors : List VConstVal) :
      AuxiliaryRecursorTranslations safety trEnv recursorEnv
        (.nil) recursors recursors
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hhead : AuxiliaryRecursorTranslation safety trEnv recursorEnv Hstep)
      (Hrest : AuxiliaryRecursorTranslations safety trEnv
        recursorEnv Htail (priorRecursors ++ [Hhead.recursor])
          finalRecursors) :
      AuxiliaryRecursorTranslations safety trEnv recursorEnv
        (.cons Hstep Htail) priorRecursors finalRecursors

/-- Dependency-order concrete replay of the block-independent auxiliary
recursor translations. -/
structure AuxiliaryRecursorTranslations.InDependencyOrder
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (H : AuxiliaryRecursorTranslations safety trEnv recursorEnv
      Htrace priorRecursors finalRecursors)
    (entries : List (ConstantInfo × VConstVal)) : Prop where
  fresh : FreshExtension sourceProdEnv (entries.map Prod.fst) targetProdEnv
  recursorValues : finalRecursors = priorRecursors ++ entries.map Prod.snd
  recursors : ∀ entry ∈ entries,
    TrConstVal safety trEnv entry.1 entry.2 ∧
      entry.2.toVConstant.WF recursorEnv

/-- Recover the exact concrete auxiliary-recursion suffix from its
block-independent translations. -/
theorem AuxiliaryRecursorTranslations.existsInDependencyOrder
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (H : AuxiliaryRecursorTranslations safety trEnv recursorEnv
      Htrace priorRecursors finalRecursors)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ entries : List (ConstantInfo × VConstVal),
      H.InDependencyOrder entries :=
  match H with
  | .nil source recursors => by
      refine ⟨[], ?_⟩
      exact { fresh := .nil, recursorValues := by simp, recursors := by simp }
  | .cons Hstep Htail Hhead Hrest => by
      let head : ConstantInfo × VConstVal :=
        (.recInfo Hstep.restored.newInfo, Hhead.recursor)
      have hheadFresh : sourceProdEnv.find? head.1.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle := congrArg Prod.snd Hstep.restored.output
      simp only at hmiddle
      have haddWF := constantsWF_add_checked hsourceWF hheadFresh
      dsimp [head] at haddWF
      have hmiddleWF := hmiddle.symm ▸ haddWF
      rcases Hrest.existsInDependencyOrder hmiddleWF with
        ⟨entries, HtailReplay⟩
      have Hfresh' : FreshExtension (sourceProdEnv.add head.1)
          (entries.map Prod.fst) targetProdEnv := by
        rw [← hmiddle]
        exact HtailReplay.fresh
      refine ⟨head :: entries, {
        fresh := .cons hheadFresh Hfresh'
        recursorValues := ?_
        recursors := ?_ }⟩
      · simpa [head, List.append_assoc] using HtailReplay.recursorValues
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | htail
        · exact ⟨Hhead.translated, Hhead.wf⟩
        · exact HtailReplay.recursors entry htail

/-- Dependency-order view of the complete executable restoration batch.
Source-family restoration supplies headers, constructors, and source
recursors; auxiliary restoration contributes exactly the trailing recursor
suffix. -/
structure RestorationInDependencyOrder
    (safety : DefinitionSafety)
    (sourceProdEnv outProdEnv : Environment)
    (sourceVEnv envTypes envCtors : VEnv)
    (owners : List VInductiveType)
    (primaryRecursors auxiliaryRecursors : List VConstVal) where
  typeEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  recursorEntries : List (ConstantInfo × VConstVal)
  actualEntries : List ConstantInfo
  fresh : FreshExtension sourceProdEnv actualEntries outProdEnv
  kernelOrder : actualEntries ~
    (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  typeValues : typeEntries.map Prod.snd =
    owners.map VInductiveType.toVConstVal
  constructorValues : constructorEntries.map Prod.snd =
    owners.flatMap VInductiveType.ctors
  recursorValues : recursorEntries.map Prod.snd =
    primaryRecursors ++ auxiliaryRecursors
  types : ∀ entry ∈ typeEntries,
    TrConstVal safety sourceVEnv entry.1 entry.2 ∧
      entry.2.toVConstant.WF sourceVEnv
  constructors : ∀ entry ∈ constructorEntries,
    TrConstVal safety envTypes entry.1 entry.2 ∧
      entry.2.toVConstant.WF envTypes
  recursors : ∀ entry ∈ recursorEntries,
    TrConstVal safety envCtors entry.1 entry.2 ∧
      entry.2.toVConstant.WF envCtors

/-- Replay the exact restoration payload in dependency order.  The
new endpoint is selected by freshness and is proved extensionally equal to
the executable restoration endpoint. -/
theorem RestorationInDependencyOrder.existsCanonicalFresh
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes envCtors owners primaryRecursors
        auxiliaryRecursors)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∃ canonicalTarget,
      FreshExtension sourceProdEnv
        ((H.typeEntries ++ H.constructorEntries ++ H.recursorEntries).map
          Prod.fst) canonicalTarget ∧
      ∀ name, outProdEnv.constants.find? name =
        canonicalTarget.constants.find? name :=
  H.fresh.exists_permuted_lookupEq hsourceWF H.kernelOrder

/-- Transfer any concrete entry property retained by a companion fresh
extension of the same run to the dependency-ordered payload. -/
theorem RestorationInDependencyOrder.canonicalProperty
    {P : ConstantInfo → Prop}
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes envCtors owners primaryRecursors
        auxiliaryRecursors)
    (Hcompanion : FreshExtension sourceProdEnv companionEntries
      outProdEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (hproperty : ∀ entry ∈ companionEntries, P entry) :
    ∀ entry ∈ H.typeEntries ++ H.constructorEntries ++
        H.recursorEntries, P entry.1 := by
  intro entry hentry
  have hcanonical : entry.1 ∈
      (H.typeEntries ++ H.constructorEntries ++ H.recursorEntries).map
        Prod.fst := List.mem_map.mpr ⟨entry, hentry, rfl⟩
  have hactual : entry.1 ∈ H.actualEntries :=
    H.kernelOrder.mem_iff.mpr hcanonical
  exact H.fresh.transferForallSameTarget Hcompanion hsourceWF hproperty
    entry.1 hactual

/-- The primitive-safe companion extension supplies the nonprimitive side
condition for every reordered restoration entry. -/
theorem RestorationInDependencyOrder.canonicalNonprimitive
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes envCtors owners primaryRecursors
        auxiliaryRecursors)
    (Hprimitive : FreshNonprimitiveExtension false sourceProdEnv
      primitiveEntries outProdEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    ∀ entry ∈ H.typeEntries ++ H.constructorEntries ++
        H.recursorEntries,
      ¬ Kernel.Environment.primitives.contains entry.1.name :=
  H.canonicalProperty Hprimitive.fresh hsourceWF Hprimitive.nonprimitive

/-- A non-delta fresh extension of the same run supplies the delta side
condition for every reordered restoration entry. -/
theorem RestorationInDependencyOrder.canonicalNondelta
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes envCtors owners primaryRecursors
        auxiliaryRecursors)
    (Hnondelta : FreshExtension sourceProdEnv nondeltaEntries outProdEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (hnondelta : ∀ entry ∈ nondeltaEntries,
      entry.deltaValue? = none) :
    ∀ entry ∈ H.typeEntries ++ H.constructorEntries ++
        H.recursorEntries, entry.1.deltaValue? = none :=
  H.canonicalProperty Hnondelta hsourceWF hnondelta

/-- Construct the three-stage abstract installation directly from the
restoration replay and its two executable side-condition extensions.
The source specification fixes the mutual-header and constructor abstract
endpoints; the checking invariant constructs the recursor endpoint.
No endpoint or installation certificate is selected by a caller. -/
theorem RestorationInDependencyOrder.existsBlockInstallation
    (projections : List VProjectionEntry)
    (es : List (Name × InductiveSignature.CaseSchema))
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes ((envCtors.addEliminators es).addProjections projections) owners
        primaryRecursors auxiliaryRecursors)
    (Hchecking : CheckingEnv safety sourceProdEnv sourceVEnv)
    (HcasesWF : (envCtors.addEliminators es).WF)
    (HprojectedWF : ((envCtors.addEliminators es).addProjections projections).WF)
    (Hprimitive : FreshNonprimitiveExtension false sourceProdEnv
      primitiveEntries outProdEnv)
    (Hnondelta : FreshExtension sourceProdEnv nondeltaEntries outProdEnv)
    (hnondelta : ∀ entry ∈ nondeltaEntries,
      entry.deltaValue? = none)
    (htypesAbstract : sourceVEnv.addConstVals
      (H.typeEntries.map Prod.snd) = some envTypes)
    (hconstructorsAbstract : envTypes.addConstVals
      (H.constructorEntries.map Prod.snd) = some envCtors) :
    ∃ canonicalProdEnv installedVEnv,
      Nonempty { S : BlockInstallation safety sourceProdEnv sourceVEnv H.typeEntries
        H.constructorEntries H.recursorEntries projections canonicalProdEnv
          installedVEnv // S.eliminators = es } ∧
      ∀ name, outProdEnv.constants.find? name =
        canonicalProdEnv.constants.find? name := by
  rcases H.existsCanonicalFresh Hchecking.map_wf with
    ⟨canonicalProdEnv, HcanonicalFresh, hlookup⟩
  have HcanonicalFresh' : FreshExtension sourceProdEnv
      (H.typeEntries.map Prod.fst ++ (H.constructorEntries.map Prod.fst ++
        H.recursorEntries.map Prod.fst)) canonicalProdEnv := by
    simpa [List.map_append, List.append_assoc] using HcanonicalFresh
  rcases HcanonicalFresh'.split_append with
    ⟨prodTypes, HtypesFresh, HafterTypes⟩
  rcases HafterTypes.split_append with
    ⟨prodCtors, HconstructorsFresh, HrecursorsFresh⟩
  have hnonprimitive := H.canonicalNonprimitive Hprimitive Hchecking.map_wf
  have hnondeltaCanonical := H.canonicalNondelta Hnondelta
    Hchecking.map_wf hnondelta
  have HtypesAdded : AddConstants safety sourceProdEnv sourceVEnv
      H.typeEntries prodTypes envTypes := by
    apply AddConstants.ofFreshAbstract HtypesFresh
      (fun entry hentry => (H.types entry hentry).1)
      (fun entry hentry => (H.types entry hentry).2)
    · intro entry hentry
      exact hnonprimitive entry (by simp [hentry])
    · intro entry hentry
      exact hnondeltaCanonical entry (by simp [hentry])
    · exact htypesAbstract
    · exact VEnv.LE.rfl
  have HcheckingTypes : CheckingEnv safety prodTypes envTypes :=
    HtypesAdded.checking Hchecking
  have HconstructorsAdded : AddConstants safety prodTypes envTypes
      H.constructorEntries prodCtors envCtors := by
    apply AddConstants.ofFreshAbstract HconstructorsFresh
      (fun entry hentry => (H.constructors entry hentry).1)
      (fun entry hentry => (H.constructors entry hentry).2)
    · intro entry hentry
      exact hnonprimitive entry (by simp [hentry])
    · intro entry hentry
      exact hnondeltaCanonical entry (by simp [hentry])
    · exact hconstructorsAbstract
    · exact VEnv.LE.rfl
  have HcheckingCtors : CheckingEnv safety prodCtors envCtors :=
    HconstructorsAdded.checking HcheckingTypes
  have HcheckingProjected : CheckingEnv safety prodCtors
      ((envCtors.addEliminators es).addProjections projections) :=
    (HcheckingCtors.addEliminators HcasesWF).addProjections HprojectedWF
  rcases AddConstants.exists_ofFresh HrecursorsFresh
      (fun entry hentry => (H.recursors entry hentry).1)
      (fun entry hentry => (H.recursors entry hentry).2)
      (fun entry hentry => hnonprimitive entry (by simp [hentry]))
      (fun entry hentry => hnondeltaCanonical entry (by simp [hentry]))
      HcheckingProjected VEnv.LE.rfl with ⟨installedVEnv, HrecursorsAdded⟩
  exact ⟨canonicalProdEnv, installedVEnv, ⟨⟨{
    envTypes := prodTypes
    venvTypes := envTypes
    envCtors := prodCtors
    venvCtors := envCtors
    formation := .ordinary HtypesAdded HconstructorsAdded
    eliminators := es
    casesWF := HcasesWF
    projectedWF := HprojectedWF
    recursorsAdded := HrecursorsAdded }, rfl⟩⟩, hlookup⟩

/-- Append the block-independent auxiliary recursors to the source-family
replay, constructing the recursor environment before any restored rule is
interpreted or typed. -/
def SourceFamilyTranslations.InDependencyOrder.appendAuxiliaryRecursors
    {sourceTypes : List InductiveType} {auxRecNames : List Name}
    {sourceProdEnv primaryProdEnv outProdEnv : Environment}
    {sourceVEnv envTypes envCtors : VEnv}
    {owners : List VInductiveType}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {HprimaryTrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv primaryProdEnv}
    {Hsource : SourceFamilyTranslations decl lparams safety
      sourceVEnv envTypes envCtors HprimaryTrace owners primaryRecursors}
    {HauxTrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      auxRecNames primaryProdEnv outProdEnv}
    {Haux : AuxiliaryRecursorTranslations safety envCtors
      envCtors HauxTrace [] auxiliaryRecursors}
    {typeEntries constructorEntries primaryRecursorEntries :
      List (ConstantInfo × VConstVal)}
    {primaryActualEntries : List ConstantInfo}
    (Hprimary : Hsource.InDependencyOrder typeEntries constructorEntries
      primaryRecursorEntries primaryActualEntries)
    {auxiliaryEntries : List (ConstantInfo × VConstVal)}
    (Hauxiliary : Haux.InDependencyOrder auxiliaryEntries) :
    RestorationInDependencyOrder safety sourceProdEnv outProdEnv sourceVEnv
      envTypes envCtors owners primaryRecursors auxiliaryRecursors := by
  let recursorEntries := primaryRecursorEntries ++ auxiliaryEntries
  let actualEntries := primaryActualEntries ++ auxiliaryEntries.map Prod.fst
  refine {
    typeEntries := typeEntries
    constructorEntries := constructorEntries
    recursorEntries := recursorEntries
    actualEntries := actualEntries
    fresh := Hprimary.fresh.append Hauxiliary.fresh
    kernelOrder := ?_
    typeValues := Hprimary.typeValues
    constructorValues := Hprimary.constructorValues
    recursorValues := ?_
    types := Hprimary.types
    constructors := Hprimary.constructors
    recursors := ?_ }
  · have h := Hprimary.kernelOrder.append
      (List.Perm.refl (auxiliaryEntries.map Prod.fst))
    simpa [recursorEntries, actualEntries, List.map_append,
      List.append_assoc] using h
  · simp only [recursorEntries, List.map_append]
    rw [Hprimary.recursorValues]
    have haux : auxiliaryEntries.map Prod.snd = auxiliaryRecursors := by
      simpa using Hauxiliary.recursorValues.symm
    rw [haux]
  · intro entry hentry
    rcases List.mem_append.mp hentry with hprimary | hauxiliary
    · exact Hprimary.recursors entry hprimary
    · rcases Hauxiliary.recursors entry hauxiliary with ⟨htr, hwf⟩
      exact ⟨htr, hwf⟩

/-- Assemble the complete dependency-order block installation from the
source-family translations and the block-independent auxiliary recursor
translations.  Every layout, concrete endpoint, value split, and installation
field is derived before restored rule semantics; the remaining inputs are the
primitive-safe and non-delta companion extensions from the same executable run. -/
theorem SourceFamilyTranslations.existsExactRestoration
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv primaryProdEnv outProdEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {HprimaryTrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      sourceTypes c.env primaryProdEnv}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {auxRecNames : List Name}
    {es : List (Name × InductiveSignature.CaseSchema)}
    {HauxTrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      auxRecNames primaryProdEnv outProdEnv}
    (Hsource : SourceFamilyTranslations decl c.lparams c.safety
      sourceVEnv envTypes ((envCtors.addEliminators es).addProjections decl.projectionEntries)
      HprimaryTrace decl.types primaryRecursors)
    (Haux : AuxiliaryRecursorTranslations c.safety
      ((envCtors.addEliminators es).addProjections decl.projectionEntries)
      ((envCtors.addEliminators es).addProjections decl.projectionEntries) HauxTrace []
      auxiliaryRecursors)
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hcore : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe decl envTypes envCtors)
    (Hparams : decl.SourceParameterWF sourceVEnv)
    (hempty : initialState.nestedAux = #[])
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (Hprimitive : FreshNonprimitiveExtension false c.env
      primitiveEntries outProdEnv)
    (Hnondelta : FreshExtension c.env nondeltaEntries outProdEnv)
    (hnondelta : ∀ entry ∈ nondeltaEntries,
      entry.deltaValue? = none)
    (Hcases : VInductBlock.EliminatorsWF sourceVEnv decl (decl.caseBlock es)) :
    ∃ replay : RestorationInDependencyOrder c.safety c.env outProdEnv
        sourceVEnv envTypes ((envCtors.addEliminators es).addProjections decl.projectionEntries)
        decl.types primaryRecursors auxiliaryRecursors,
      ∃ canonicalProdEnv installedVEnv,
        Nonempty { S : BlockInstallation c.safety c.env sourceVEnv replay.typeEntries
          replay.constructorEntries replay.recursorEntries
            decl.projectionEntries canonicalProdEnv installedVEnv // S.eliminators = es } ∧
        ∀ name, outProdEnv.constants.find? name =
          canonicalProdEnv.constants.find? name := by
  rcases Hsource.existsExactCanonicalSourceReplay Hlower Hprod hempty
      hvisible Hc.checking.tr.map_wf with
      ⟨typeEntries, constructorEntries, primaryRecursorEntries,
        primaryActualEntries, Hprimary⟩
  have hprimaryWF : primaryProdEnv.constants.WF :=
    Hprimary.fresh.targetWF Hc.checking.tr.map_wf
  rcases Haux.existsInDependencyOrder hprimaryWF with
    ⟨auxiliaryEntries, Hauxiliary⟩
  let replay := Hprimary.appendAuxiliaryRecursors Hauxiliary
  have htypesAbstract : sourceVEnv.addConstVals
      (replay.typeEntries.map Prod.snd) = some envTypes := by
    rw [replay.typeValues]
    simpa [VInductDecl.typeConstants] using Hcore.typesAdded
  have hconstructorsAbstract : envTypes.addConstVals
      (replay.constructorEntries.map Prod.snd) = some envCtors := by
    rw [replay.constructorValues]
    simpa [VInductDecl.constructorConstants] using Hcore.ctorsAdded
  have HsourceChecking : CheckingEnv c.safety c.env sourceVEnv := by
    simpa only [Hheaders.sourceContextVEnv] using
      Hheaders.sourceContext.checking.tr
  obtain ⟨HcasesWF, HprojectedWF⟩ := Hcases.recursorCheckingEnvWF HsourceChecking.wf Hcore Hparams
  rcases replay.existsBlockInstallation decl.projectionEntries es HsourceChecking
      HcasesWF HprojectedWF Hprimitive Hnondelta
      hnondelta htypesAbstract hconstructorsAbstract with
    ⟨canonicalProdEnv, installedVEnv, Hstaged, hlookup⟩
  exact ⟨replay, canonicalProdEnv, installedVEnv, Hstaged, hlookup⟩

end VerifyInductive
end Lean4Lean
