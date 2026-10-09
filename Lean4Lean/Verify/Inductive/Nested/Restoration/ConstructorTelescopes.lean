import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledConstructorTypes
import Lean4Lean.Verify.Inductive.Constructor.Telescopes
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceHeaders
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ConstructorEnvironment
import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshExtensions
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations

/-!
# Telescope certificates of restored nested constructors

A successful nested run stores, for every source constructor, the restoration of the lowered
constructor type, which is `Expr.eqv` to the source type
(`NestedRun.installedConstructorSource`). The source type itself is checked by
`validateSourceConstructorTypes.run` in the header-only validation environment, before
any environment containing the restored constructors is used by the checker; that run certifies
its telescope (`checkType.WF_telTr`), and `Expr.eqv` transports the certificate.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The executable source-type check of the nested constructor validation certifies the
telescope of every source constructor type in the validation environment. -/
theorem validateSourceConstructorTypes.telTr_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hmode : fuel.cacheMode.Sound venv)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) env)
    (Hsources : SourceSyntaxChecks types)
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams
      safety fuel types = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    ∃ T, TelTrN venv lparams (AddInductive.constructorArity ctor.type) [] ctor.type T := by
  rcases validateSourceConstructorTypes.typeCheck_eq_ok_of_run
      hrun htype hctor with ⟨checked, hcheck⟩
  have hclosed := Hsources.constructorsClosed htype ctor hctor
  have hfvars : ctor.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid lparams fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType ctor.type
      TypeChecker.ensureSort type ctor.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid lparams fuel) {}
      fun _ _ => ∃ T, TelTrN venv lparams (AddInductive.constructorArity ctor.type) [] ctor.type T := by
    refine ((TypeChecker.checkType.WF (e := ctor.type) hfvars).and
      (TypeChecker.checkType.WF_telTr henv (by intro k r h; simp at h) hfvars
        (by simp))).bind fun _ _ _ ⟨⟨_, _, _, _, hsort, _⟩, htel⟩ => ?_
    exact (TypeChecker.ensureSort.WF hsort).mono fun _ _ _ _ => htel
  exact TypeChecker.M.WF.runCheckingValid Hcheck hmode checked hcheck

/-- The validation runs of a nested declaration use a cache mode sound for its source-type
environment, an extension of the checked context's. -/
theorem NestedRun.cacheSound
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    E.validationFuel.cacheMode.Sound E.sourceCore.envTypes := by
  have h := E.contextWF.cacheSound
  rw [E.context_fuel, E.context_venv] at h
  exact h.mono (VEnv.addConstVals_le E.sourceCore.sourceAdded)

/-- The validation runs' cache mode is sound for every extension of the source environment. -/
theorem NestedRun.cacheSound_of_le
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) (h : sourceVEnv ≤ venv) :
    E.validationFuel.cacheMode.Sound venv := by
  have hs := E.contextWF.cacheSound
  rw [E.context_fuel, E.context_venv] at hs
  exact hs.mono h

/-- Every constructor visible after a successful validated nested run is old, or a new
constructor carrying the declaration's safety flag and certified in the source header
environment. -/
theorem NestedRun.restoredCtorOrigin
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) sourceProdEnv)
    {name : Name} {ci : ConstructorVal} (hfind : outEnv.find? name = some (.ctorInfo ci)) :
    sourceProdEnv.find? name = some (.ctorInfo ci) ∨
      (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt E.sourceCore.envTypes ci) := by
  have hwf : sourceProdEnv.constants.WF := by
    have h := E.contextWF.checking.tr.map_wf
    rwa [E.context_env] at h
  -- the restored headers have the source header types
  have hheaderType : ∀ indType ∈ sourceTypes, ∀ oldInfo : InductiveVal,
      E.loweredEnv.find? indType.name = some (.inductInfo oldInfo) →
      oldInfo.type = indType.type := by
    intro indType hmem oldInfo hlookup
    rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, rfl⟩
    have key : ∀ P : LoweredRun E.loweredEnv,
        P.c.env = sourceProdEnv → P.nparams = nparams →
        P.indTypes = result.types.toArray → ContextWF P.c →
        oldInfo.type = sourceTypes[familyIdx].type := by
      intro P henv' hnparams hindTypes Hc
      rcases P with ⟨c, stats, loweredDecl, nparams', depth, isUnsafe',
        initialEnv, indTypes, headerEnv, ctorEnv, Hheaders, R, Hprod⟩
      dsimp only at henv' hnparams hindTypes Hc
      subst hnparams hindTypes
      let initialState : Lean4Lean.ElimNestedInductive.State :=
        { lvls := lparams.map .param, newTypes := #[] }
      have hempty : initialState.nestedAux = #[] := by
        apply Array.ext
        · rfl
        · intro i _hi₁ hi₂
          simp at hi₂
      have Hlower : NestedLoweringOutputClosed c.env
          E.validationFuel.inductiveFuel nparams' sourceTypes
          { initialState with newTypes := sourceTypes.toArray } result := by
        rw [henv']
        simpa [initialState] using E.lowering
      rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hfamily with
        ⟨_, _, loweredTarget, _, _, _, _, Hmapping, htarget⟩
      obtain ⟨hresultFamily, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
      rcases Hprod.findSourceHeaderAt familyIdx (by simpa using hresultFamily) with
        ⟨info, hinfoLookup, -, hinfoType, -⟩
      have hinfoLookup' : E.loweredEnv.find? sourceTypes[familyIdx].name =
          some (.inductInfo info) := by
        rw [← Hmapping.name]
        simpa [htargetEq] using hinfoLookup
      cases ConstantInfo.inductInfo.inj (Option.some.inj (hlookup.symm.trans hinfoLookup'))
      rw [hinfoType, ← Hmapping.type]
      simp [htargetEq]
    exact key E.lowered
      ((congrArg AddInductive.Context.env E.lowered_c).trans
        E.context_env)
      E.lowered_nparams E.lowered_indTypes
      (E.lowered_c ▸ E.contextWF)
  -- the header-only validation environment is ghost-free
  have hgf : TypeChecker.EnvGhostFree (fun _ => True) E.auxiliaryHeaderEnv := by
    intro n ci hfind
    rcases E.headerValidationEnvironment.headers.headerFindCases hwf hfind with
      hold | ⟨indType, hmem, oldInfo, hlookup, -, rfl⟩
    · exact henv hold
    · refine ⟨?_, fun v hv => by simp [ConstantInfo.deltaValue?] at hv, fun r hr => by
        cases hr⟩
      show TypeChecker.GhostFree _ oldInfo.type
      rw [hheaderType indType hmem oldInfo hlookup]
      exact (Hsources.typeClosed hmem).mono fun _ h => h.elim
  -- every source constructor type is certified by the validation run
  have hsrc : ∀ type ∈ sourceTypes, ∀ source ∈ type.ctors,
      ∃ T, TelTrN E.sourceCore.envTypes lparams (AddInductive.constructorArity source.type) []
        source.type T :=
    fun _ htype _ hsource => validateSourceConstructorTypes.telTr_of_run
      E.sourceCore.headerValidationValid E.cacheSound hgf Hsources E.parameterValidation htype hsource
  rcases E.installedConstructorSource Hsources Howners hfind with
    hold | ⟨type, htype, source, hsource, -, hlp, heqv, -, hu⟩
  · exact .inl hold
  · obtain ⟨T, hT⟩ := hsrc type htype source hsource
    refine .inr ⟨hu, ?_⟩
    have hord := E.sourceCore.headerValidationValid.tr.wf.ordered
    have := CtorTelescopeAt.of_telTrN (venv := E.sourceCore.envTypes) (ci := ci)
      (T := T) (by rw [hlp]; exact hT.eqv_arity hord (BEq.symm heqv))
    exact this

/-- Every constructor visible after a successful validated nested run, and every constructor of
its constructor-validation environment, is certified in the source header environment. -/
theorem NestedRun.restoredCtorTelescopes
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (henv : TypeChecker.EnvGhostFree (fun _ => True) sourceProdEnv)
    (hbase : CtorTelescopes safety sourceProdEnv sourceVEnv) :
    CtorTelescopes safety outEnv E.sourceCore.envTypes ∧
      CtorTelescopes safety E.validationEnv E.sourceCore.envTypes := by
  have hwf : sourceProdEnv.constants.WF := by
    have h := E.contextWF.checking.tr.map_wf
    rwa [E.context_env] at h
  have hle : sourceVEnv ≤ E.sourceCore.envTypes :=
    VEnv.addConstVals_le E.sourceCore.core.typesAdded
  have hout : CtorTelescopes safety outEnv E.sourceCore.envTypes := by
    intro name ci hfind hvis
    rcases E.restoredCtorOrigin Hsources Howners henv hfind with hold | ⟨-, hc⟩
    · exact (hbase hold hvis).mono hle
    · exact hc
  refine ⟨hout, ?_⟩
  intro name ci hfind hvis
  refine hout (name := name) (ci := ci) ?_ hvis
  -- the constructors of the validation environment are those of the output
  rcases E.restoration.inductives.inductiveFreshExtension hwf with ⟨_, Hprimary⟩
  have hprimaryWF := Hprimary.targetWF hwf
  rcases E.restoration.auxiliaries.recursorFreshExtension hprimaryWF with ⟨_, Hauxiliary⟩
  rcases E.validationEnvironment.findCases hwf hfind with hold | ⟨_, _, _, _, _, hci⟩ |
      ⟨indType, hmem, oldInfo, hlookup, cn, hcn, ctorOld, hctorLookup, rfl, hci⟩
  · exact Hauxiliary.preservesSourceFind hprimaryWF
      (Hprimary.preservesSourceFind hwf hold)
  · cases hci
  · rcases E.restoration.inductives.inductiveHeaderFindOfMem hwf hmem with
      ⟨oldInfo', hlookup', _, hctors⟩
    cases ConstantInfo.inductInfo.inj (Option.some.inj (hlookup.symm.trans hlookup'))
    rcases hctors cn hcn with ⟨ctorOld', hctorLookup', hctorFind⟩
    cases ConstantInfo.ctorInfo.inj (Option.some.inj (hctorLookup.symm.trans hctorLookup'))
    rw [hci]
    exact Hauxiliary.preservesSourceFind hprimaryWF hctorFind

end VerifyInductive
end Lean4Lean
