import Lean4Lean.Verify.Inductive.Recursor.Context.FVarArrays
import Lean4Lean.Verify.Inductive.Constructor.ParameterPrefixes

/-! The owner normal forms of the constructor types (`ConstructorOwnerNormalForms`), recorded by
a successful run of the constructor check. Ported from the source branch's
`Recursor/Context/FVarArrays.lean` (the constructor-check part; the free-variable-array
infrastructure stays in `Recursor/Context/`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-- A successful run of the constructor check `loopCtor` yields the owner normal form of
the constructor type. This is separate from `CtorTailWF`: both read the same run, but this
one keeps the executable normal form that `mkRecInfos` needs later. -/
theorem checkConstructors.loopCtor.ownerNormalFormWF
    {decl : VInductDecl} {scope : VLCtx} {depth : Nat}
    {narrowType fullType : VExpr}
    {root c : AddInductive.Context} {Hroot : ContextWF root}
    {fields : Array Expr} {source : Expr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (Hparams : FVarArrayIn root stats.params)
    (Hfields : FVarSuffix Hroot Hc fields)
    (Hopening : ConstructorFieldOpening source type fields)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => Nonempty
        (ConstructorOwnerNormalForm stats targetIdx source)) := by
  induction fuel generalizing c type scope narrowType fullType depth i fields with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, _hfullTarget⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType _hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases halign.forallE_align Hc.checking.tr.wf hdomNarrow
              hdomNarrowType hbodyNarrow with
            ⟨dom₀, _, hdom₀, hdom₀Type, _, hbody₀, _⟩
          rcases hconsume _ Hc.atCheckLCtx hdom₀ hdom₀Type with
            ⟨consumedDom₀, Hdom₀⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.unannotatedDomain Hc Hdom hdomNarrow with
            ⟨_domainLevel, hdomain⟩
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.refinesScoped
              (ctor := ctor) (idx := i) Hc Hruntime halign Hstats
              hconsume hlit hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            refine checkConstructors.loopCtor.safeField.sourceWF
              (Q := fun _ => Nonempty
                (ConstructorOwnerNormalForm stats targetIdx source))
              Hc hparamAt Hdom hbodyFull Hdom₀ hbody₀ Hpos ?_
            intro _fieldType _fieldLevel _fieldLevel' _hfield _hlevel
              _htyped _ _ _ _hfieldBound _recursive _hpositive bodyFull' _hbodyFullEq
              _ _ hopenedFull _
            let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
              Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
            let Hruntime' :
                checkInductiveTypes.loopType.FrontScopeEmbedding
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain hdomNarrowType
            have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
              Hdom Hdom₀ hdomNarrow hdomNarrowType hdeps
            have hscopeWF := halign'.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.orderedStrong hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            let Hfields' := Hfields.pushCurrentChecked name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom bi
              Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
            have hopenFvars : Hopening.fvars =
                Hfields.toFVarArrayIn.fvars :=
              Hopening.fvars_eq_bound Hfields.toFVarArrayIn
            have hcurrentFresh :
                (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
              rw [hopenFvars]
              intro hmem
              exact Hc.toBindingContextWF.current_not_mem
                (Hfields.toFVarArrayIn.members _ hmem)
            have hbodyFresh : body.FVarsIn
                (fun other => other ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
              apply hbodyFull.fvarsIn.mono
              intro other hother heq
              subst other
              have hbase : (⟨c.ngen.curr⟩ : FVarId) ∈
                  Hc.mlctx.vlctx.fvars := by simpa using hother
              exact Hc.current_not_mem hbase
            let Hopening' := Hopening.push hcurrentFresh hbodyFresh
            exact ih Hc' Hruntime' halign' Hstats' hparamNext hlit Hfields'
              Hopening' hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              (Q := fun _ => Nonempty
                (ConstructorOwnerNormalForm stats targetIdx source))
              Hc hparamAt Hdom hbodyFull Hdom₀ hbody₀ ?_
            intro _fieldType _fieldLevel _fieldLevel' _hfield _hlevel
              _htyped _ _ _ _hfieldBound bodyFull' _hbodyFullEq _ _
              hopenedFull _
            let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
              Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
            let Hruntime' :
                checkInductiveTypes.loopType.FrontScopeEmbedding
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain hdomNarrowType
            have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
              Hdom Hdom₀ hdomNarrow hdomNarrowType hdeps
            have hscopeWF := halign'.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.orderedStrong hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            let Hfields' := Hfields.pushCurrentChecked name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom bi
              Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
            have hopenFvars : Hopening.fvars =
                Hfields.toFVarArrayIn.fvars :=
              Hopening.fvars_eq_bound Hfields.toFVarArrayIn
            have hcurrentFresh :
                (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
              rw [hopenFvars]
              intro hmem
              exact Hc.toBindingContextWF.current_not_mem
                (Hfields.toFVarArrayIn.members _ hmem)
            have hbodyFresh : body.FVarsIn
                (fun other => other ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
              apply hbodyFull.fvarsIn.mono
              intro other hother heq
              subst other
              have hbase : (⟨c.ngen.curr⟩ : FVarId) ∈
                  Hc.mlctx.vlctx.fvars := by simpa using hother
              exact Hc.current_not_mem hbase
            let Hopening' := Hopening.push hcurrentFresh hbodyFresh
            exact ih Hc' Hruntime' halign' Hstats' hparamNext hlit Hfields'
              Hopening' hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
    · cases hvalid :
          AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · exact checkConstructors.loopCtor.result.WF hforall hvalid
          ⟨ConstructorOwnerNormalForm.ofOpening Hopening Hparams
            Hfields.toFVarArrayAfter (Hstats.indConstAt hi)
            (by cases type <;> simp_all [Expr.isForall]) hvalid⟩

/-- The owner normal form from the start of a constructor type. The cached parameters are
instantiated as in `refinesCtorShape`; only the constructor fields enter the normal form. -/
theorem checkConstructors.loopCtor.ownerNormalFormFromStartWF
    {decl : VInductDecl} {ctorVal : VConstVal}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (Hctor : TrSourceConstRaw Hc.venv c.lparams ctor source ctorVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source checkedType fullType checkedType')
    (hi : targetIdx < decl.types.length)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source 0 fuel c).WF
      (fun _ => ∃ tail,
        ParameterPrefix stats 0 source tail ∧
        Nonempty
          (ConstructorOwnerNormalForm stats targetIdx tail)) := by
  have hnoFVars : FVarsIn (fun _ => False) source := by
    simpa [VLCtx.fvars] using Hctor.type.fvarsIn
  by_cases hzero : decl.nparams = 0
  · have hscopeLength : Hsuffix.parameterDecls.length = 0 := by
      simpa [Hstats.params_size, hzero] using
        Hsuffix.parameterDecls_length
    have hscope : Hsuffix.parameterDecls = [] :=
      List.eq_nil_of_length_eq_zero hscopeLength
    cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hparamAt : stats.params[0]? = none := by
        rw [Array.getElem?_eq_none_iff, Hstats.params_size, hzero]
        omega
      have Hnormal := checkConstructors.loopCtor.ownerNormalFormWF
        (type := source) (source := source) (fields := #[])
        (i := 0) (ctor := ctor) (fuel := fuel + 1)
        (isUnsafe := isUnsafe)
        (Hroot := Hc) Hc
        (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
          Hc Hsuffix) halign
        Hstats hi hparamAt hconsume hlit Hsuffix.paramsBound
        (FVarSuffix.empty Hc)
        (ConstructorFieldOpening.empty source)
        (by simpa [hscope] using Hctor.type)
        (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      exact Hnormal.mono fun _ Hnormal =>
        ⟨source, .done (by rw [Hstats.params_size, hzero]), Hnormal⟩
  by_cases hforall : ∃ name dom body bi,
      source = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have htype : Hc.venv.IsType c.lparams.length [] ctorVal.type := by
      rcases TrExpr.forallE_source
          (Hctor.type.trExpr Hc.checking.tr.wf (by trivial)) with
        ⟨dom', body', _hdom, _hbody, hdomType, hbodyType, heq⟩
      exact (VEnv.IsType.forallE hdomType hbodyType).defeqU_l
        Hc.checking.tr.wf (by trivial) heq
    let Hinitial := ConstructorSynthesisState.initial htype
    apply checkConstructors.loopCtor.parameterTelescopeWF
      (decl := decl) (ctorVal := ctorVal) Hc
      (Q := fun _ => ∃ tail,
        ParameterPrefix stats 0 (.forallE name dom body bi) tail ∧
        Nonempty
          (ConstructorOwnerNormalForm stats targetIdx tail))
      (Hresult := by
        intro source' current' fullCurrent' fuel' sourceDomains
          _Hsynthesis htrNarrow htrFull Hsegment _Hcomparisons
        have hparamAt : stats.params[decl.nparams]? = none := by
          rw [Array.getElem?_eq_none_iff]
          exact Nat.le_of_eq Hstats.params_size
        have Hnormal := checkConstructors.loopCtor.ownerNormalFormWF
          (type := source') (source := source') (fields := #[])
          (i := decl.nparams) (ctor := ctor) (fuel := fuel' + 1)
          (isUnsafe := isUnsafe)
          (Hroot := Hc) Hc
          (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
            Hc Hsuffix) halign
          Hstats hi hparamAt hconsume hlit Hsuffix.paramsBound
          (FVarSuffix.empty Hc)
          (ConstructorFieldOpening.empty source') htrNarrow htrFull
        exact Hnormal.mono fun _ Hnormal =>
          ⟨source', by
            have Hcomplete : ParameterSegment stats 0 stats.params.size
                (.forallE name dom body bi) source' := by
              simpa only [Hstats.params_size] using Hsegment
            exact Hcomplete.complete rfl,
            Hnormal⟩)
      (Hearly := by
        intro source' scope' current' fullCurrent' i' fuel' sourceDomains hi'
          hforall Hscope' _Hsynthesis _htrNarrow _htrFull _Hcomparisons
        exact checkConstructors.loopCtor.earlyParameterResult.WF
          (fuel := fuel') Hc Hscope'
          (by simpa [Hstats.params_size] using hi') hforall)
      Hstats.params_size (by omega) (.done)
      (fun h =>
        checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars h hnoFVars)
      (fun h =>
        (checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars
          h hnoFVars).older_eq_nil h |>.symm)
      (by
        intro hdone
        have hlength := Hsuffix.parameterDecls_length
        have hempty : Hsuffix.parameterDecls = [] :=
          List.eq_nil_of_length_eq_zero (by
            rw [hlength, Hstats.params_size, hdone])
        exact hempty.symm)
      Hinitial Hctor.type
      (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      CheckedConstructorParameterPrefix.zero
  · cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hiStats : 0 < stats.params.size := by
        rw [Hstats.params_size]
        omega
      exact checkConstructors.loopCtor.earlyParameterResult.WF
        (Hsuffix := Hsuffix) (fuel := fuel) Hc
        (checkInductiveTypes.loopType.ReusedParameterScope.ofNoFVars
          (Hsuffix := Hsuffix) hiStats hnoFVars)
        (by omega) hforall


structure ConstructorOwnerNormalFormRow
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (ctors : List Constructor) (done : Nat) : Prop where
  covered : done ≤ ctors.length
  entries : ∀ i, i < done → (hi : i < ctors.length) →
    ConstructorOwnerNormalFormAt stats targetIdx ctors[i]

theorem ConstructorOwnerNormalFormRow.empty
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (ctors : List Constructor) :
    ConstructorOwnerNormalFormRow stats targetIdx ctors 0 where
  covered := Nat.zero_le _
  entries _ hi := by omega

theorem ConstructorOwnerNormalFormRow.push
    (H : ConstructorOwnerNormalFormRow stats targetIdx ctors done)
    (hi : done < ctors.length)
    (Hentry : ConstructorOwnerNormalFormAt stats targetIdx ctors[done]) :
    ConstructorOwnerNormalFormRow stats targetIdx ctors (done + 1) where
  covered := by omega
  entries i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hentry
    · exact H.entries i (by omega) hi'

structure ConstructorOwnerNormalFormRows
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (done : Nat) : Prop where
  covered : done ≤ indTypes.size
  rows : ∀ i, i < done → (hi : i < indTypes.size) →
    ConstructorOwnerNormalFormRow stats i indTypes[i].ctors
      indTypes[i].ctors.length

theorem ConstructorOwnerNormalFormRows.empty
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) :
    ConstructorOwnerNormalFormRows stats indTypes 0 where
  covered := Nat.zero_le _
  rows _ hi := by omega

theorem ConstructorOwnerNormalFormRows.push
    (H : ConstructorOwnerNormalFormRows stats indTypes done)
    (hi : done < indTypes.size)
    (Hrow : ConstructorOwnerNormalFormRow stats done
      indTypes[done].ctors indTypes[done].ctors.length) :
    ConstructorOwnerNormalFormRows stats indTypes (done + 1) where
  covered := by omega
  rows i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hrow
    · exact H.rows i (by omega) hi'


theorem ConstructorOwnerNormalFormRows.complete
    (H : ConstructorOwnerNormalFormRows stats indTypes indTypes.size) :
    ConstructorOwnerNormalForms stats indTypes where
  replay familyIdx hfamily ctorIdx hctor :=
    (H.rows familyIdx hfamily hfamily).entries ctorIdx hctor hctor

namespace checkConstructors.loopCtors

/-- The constructor loop of one family records the owner normal form of each of its
constructors. -/
theorem ownerNormalFormsWF
    {decl : VInductDecl} {sourceEnv : VEnv}
    {source : InductiveType} {target : VInductiveType}
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
      source target)
    (Hrow : ConstructorOwnerNormalFormRow stats targetIdx
      source.ctors ctorIdx)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (htargetIdx : targetIdx < decl.types.length)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (Hfinish : ConstructorOwnerNormalFormRow stats targetIdx source.ctors
        source.ctors.length → ∀ out, Q out) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length
        Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepPrefix.checkedWF (stats := stats) (isUnsafe := isUnsafe)
      (targetIdx := targetIdx) (Q := Q) Hc hidx
    intro checkedType type' checkedType' hchecked
    have Hnormal :=
      checkConstructors.loopCtor.ownerNormalFormFromStartWF
        (fuel := c.fuel.inductiveFuel) (isUnsafe := isUnsafe)
        Hc Hsuffix Hstats halign Hctor hchecked
        htargetIdx hconsume hlit
    exact Hnormal.mono fun fields Hentry =>
      ownerNormalFormsWF (Q := fun rest => Q (fields :: rest)) Hc Htarget
        (Hrow.push hidx Hentry) Hsuffix Hstats halign htargetIdx
        hconsume hlit (fun h _ => Hfinish h _)
  · have heq : ctorIdx = source.ctors.length := by
      have := Hrow.covered
      omega
    apply result.WF (Q := Q) hidx
    exact Hfinish (by simpa [heq] using Hrow) _
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

/-- The family loop records the owner normal forms of the constructors of every family. -/
theorem ownerNormalFormsWF
    {decl : VInductDecl} {sourceEnv : VEnv}
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams)
      indTypes.toList decl.types)
    (Hrows : ConstructorOwnerNormalFormRows stats indTypes targetIdx)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (Hfinish : ConstructorOwnerNormalFormRows stats indTypes indTypes.size →
      ∀ out, Q out) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      omega
    have Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := List.forall₂_getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.ownerNormalFormsWF
      (Q := fun fields =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF fun rest => Q (fields :: rest))
      Hc Htarget
      (ConstructorOwnerNormalFormRow.empty stats targetIdx
        indTypes[targetIdx].ctors)
      Hsuffix Hstats halign htarget hconsume hlit
    intro Hrow fields
    exact ownerNormalFormsWF (Q := fun rest => Q (fields :: rest)) Hc Htypes
      (Hrows.push hidx Hrow)
      Hsuffix Hstats halign hconsume hlit (fun h _ => Hfinish h _)
  · have heq : targetIdx = indTypes.size := by
      have := Hrows.covered
      omega
    apply result.WF (Q := Q) hidx
    exact Hfinish (by simpa [heq] using Hrows) _
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

end VerifyInductive
end Lean4Lean
