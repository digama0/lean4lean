import Lean4Lean.Verify.Inductive.Nested.Lowering.Output
import Lean4Lean.Verify.Inductive.Nested.Restoration.Lookups
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorTranslations
import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Verify.Inductive.Nested.Lowering.OccurrenceTyping

/-! # The restoration side of the lowering verification

The lowering theorems that read the restoration steps
(`ConstructorLowering.Resolved.constructorRestoration_inverse`, `restoredType_translation`,
`LoweredRestoredConstructors`, `NestedLowering.restoreAuxConstructorsFreshOfInstallation`); the
rest of the lowering verification is under `Nested/Lowering/`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
/-- Metadata-facing form of the constructor inverse.  Installation exposes a
`ConstructorVal`, while lowering is indexed by the corresponding
`Constructor`; the explicit type equality is the only alignment fact needed
to connect the two verified relations. -/
theorem ConstructorLowering.Resolved.constructorRestoration_inverse
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type)
    (hparamsSize : params.size = nparams)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    HsourceClosed hsourceBVar hparamsSize restoreEnv HsourceDisjoint hresultNParams
  simpa [htype] using Hrestored.type

/-- Transport source translation across constructor restoration using
source disjointness (`RestoreSourceDisjoint`), without imposing a namespace convention on
auxiliary constructor names. -/
theorem ConstructorLowering.Resolved.restoredType_translation
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type)
    (hparamsSize : params.size = nparams)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  rcases H.constructorRestoration_inverse hresultParams paramFvars hparams
      hnodup HsourceClosed hsourceBVar hparamsSize restoreEnv HsourceDisjoint
      hresultNParams Hrestored
      htype with
    ⟨Hinverse⟩
  apply Hsource.eqv
  simpa [beq_comm] using Hinverse.restoredType_eqv_source


/-- Lockstep alignment of the state-threaded constructor lowering relation
with the executable restoration fold.  The kernel lookup theorem
has already identified the `oldInfo.type` read at every step with that step's
positionally corresponding lowered constructor type. -/
inductive LoweredRestoredConstructors
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      LoweredRestoredConstructors result mappingEnv loweredEnv params
        nparams safety lparams [] state [] state sourceProdEnv sourceProdEnv
  | cons
      (Hmapping : ConstructorLowering.Resolved mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hrest : LoweredRestoredConstructors result mappingEnv loweredEnv params
        nparams safety lparams sources nextState targets finalState
          middleProdEnv targetProdEnv) :
      LoweredRestoredConstructors result mappingEnv loweredEnv params nparams
        safety lparams (source :: sources) state (target :: targets) finalState
          sourceProdEnv targetProdEnv


/-- Interpret the lockstep lowering/restoration relation against the
independently translated source constructors.  This connects the executable and the
specification for the constructor list: every executable restoration step is
shown to translate the same abstract constructor that appears in the source
inductive specification. -/
theorem LoweredRestoredConstructors.sourceTyping
    (H : LoweredRestoredConstructors result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsources : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams)
    (hparamsSize : params.size = nparams) :
    RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv
        sources constructors := by
  induction H generalizing constructors with
  | nil =>
    cases Hsources
    exact .nil _
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsources with
    | cons Hsource Hsources =>
      rename_i vctor vconstructors
      cases Hsyntax with
      | cons HsourceSyntax Hsyntax =>
        have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            source.type vctor.type := by
          simpa [hlevels] using Hsource.type
        have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            Hstep.restored.newInfo.type vctor.type :=
          Hmapping.restoredType_translation hresultParams paramFvars hparams
            hnodup HsourceSyntax.closed
            (by simpa [VLCtx.bvars] using HsourceType.closed) hparamsSize loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) vctor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredConstructorTranslations.cons Hstep
          { constructor := vctor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

/-- Build the lockstep constructor relation `LoweredRestoredConstructors` from the
verified lowered installation.  The only list premise is that all mapped targets belong
to the installed owner; in the family specialization this is immediate because `targets`
is that owner's constructor list. -/
theorem LoweredRestoredConstructors.ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (Hprod : RecursorInstallation R loweredEnv)
    (howner : owner ∈ indTypes.toList)
    (Hmapping : ConstructorLowerings.Resolved mappingEnv params nparams result
      sources state (targets, finalState))
    (Htrace : FoldSteps (RestoredConstructorStep result loweredEnv)
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv)
    (Htargets : ∀ target ∈ targets, target ∈ owner.ctors) :
    LoweredRestoredConstructors result mappingEnv loweredEnv params nparams
      c.safety c.lparams sources state targets finalState sourceProdEnv
        targetProdEnv := by
  cases Hmapping with
  | nil =>
    cases Htrace
    exact .nil _ _
  | cons Hhead Htail =>
    cases Htrace with
    | cons Hstep Hsteps =>
      have Hmetadata := Hstep.metadataOfInstalled Hprod howner
        (Htargets _ (by simp)) rfl
      apply LoweredRestoredConstructors.cons Hhead Hstep
      · exact Hmetadata.1
      · exact Hmetadata.2.1
      · exact Hmetadata.2.2.1
      · exact Hstep.oldType_eq_ofInstalled Hprod howner
          (Htargets _ (by simp)) rfl
      · apply LoweredRestoredConstructors.ofInstalled Hprod howner
          Htail Hsteps
        intro target htarget
        exact Htargets target (by simp [htarget])

/-- Freshness of auxiliary constructors for restoration: lowering proves auxiliary
families fresh in the source kernel environment, and lockstep installation turns that
into abstract freshness for every constructor recognized through those
families. -/
theorem NestedLowering.restoreAuxConstructorsFreshOfInstallation
    (H : NestedLowering sourceProdEnv fuel nparams types initialState
      (result, finalState))
    (Hinstall : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv :=
  Hinstall.restoreAuxConstructorsFresh hwf Howners
    (H.resultFamilyNamesFreshOfEmpty hwf hempty)


/-- Over the lowered run's installation: every constructor recognized as belonging to a fresh
auxiliary family is absent from the source model. -/
theorem RecursorInstallation.restoreAuxConstructorsFreshOfInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv loweredEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceVEnv indTypes ctorEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    (H : RecursorInstallation R loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (Hfamilies : RestoreAuxFamiliesFresh result c.env) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  intro name nested auxFamily hrecognized
  rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
      hrecognized with ⟨⟨info, hlookup, hfamily, hmap⟩⟩
  rcases H.outOrigin hlookup with hctor | ⟨r, -, h⟩
  · rcases R.ctorEnv_cases hctor with hhdr | ⟨iv, hiv, cval, hc, heq, hname⟩
    · rcases R.headerEnv_cases hhdr with hold | ⟨info', -, heq, -⟩
      · rcases Howners name info hold with ⟨owner, howner, -⟩
        have hfresh := Hfamilies info.induct nested hmap
        rw [howner] at hfresh
        contradiction
      · cases heq
    · cases heq
      have hmem : name ∈ decl.constructorConstants.map (·.name) := by
        rw [← R.ctorCis_names, ← hname]
        exact List.mem_map.mpr ⟨_, List.mem_flatMap.mpr ⟨iv, hiv, List.mem_map_of_mem hc⟩, rfl⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmem
      have hfreshT := Lean4Lean.VEnv.addConstVals_names_fresh R.core.ctorsAdded v hv
      cases hs : sourceVEnv.constants v.name with
      | none => rfl
      | some x =>
        have := (VEnv.addConstVals_le R.core.typesAdded).constants hs
        rw [hfreshT] at this; cases this
  · cases h

end VerifyInductive
end Lean4Lean
