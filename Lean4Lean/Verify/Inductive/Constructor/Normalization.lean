import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Theory.Inductive.Normalization

/-! Successful positivity determines the uniform strictly positive normal form of
every field, including the universe spine checked at each recursive head, in the
branch named by the classification the check returns (the `classifiedFields` clause
of `InductiveSignature.Models`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The actual recursive-application test retains the whole universe spine,
not only the arity exposed by `ValidIndAppAt`. -/
theorem checkPositivityStep.isValidIndApp?.uniformNormalForm
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlevels : stats.levels.mapM (VLevel.ofLevel Us) = some levels)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ) :
    decl.ClassifiedFieldNormalForm levels depth true type' := by
  rcases checkPositivityStep.isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalidIdx (H.indConstAt hi')
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels', _⟩
  have heq : levels' = levels := Option.some.inj (hlevels'.symm.trans hlevels)
  subst levels'
  refine ⟨[], type', rfl, by simp, ?_,
    decl.types[typeIdx], List.getElem_mem hi', ?_⟩
  · simpa using checkPositivityStep.isValidIndApp?.validIndAppAt H htr hvalid hlit hctx
  · exact congrArg Prod.fst hspine

/-- Replay successful positivity in the checking scope, retaining every
source-free binder and the exact universe spine checked at a recursive head. The
returned classification names the branch of the normal form. -/
theorem checkPositivity.loop.uniformNormalFormScoped
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) = some levels)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun recursive => ∃ normalized,
        Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowType normalized ∧
        decl.ClassifiedFieldNormalForm levels depth recursive normalized) := by
  induction fuel generalizing c type scope narrowType fullType depth with
  | zero => exact checkPositivity.loop.zero.WF
  | succ fuel ih =>
    have henv := Hc.checking.tr.wf
    have hscopeWF₀ := halign.wf
    rcases htypeFull with ⟨sourceFull, hsourceFull, _hsourceTarget⟩
    obtain ⟨type₀, htype₀, _⟩ := htypeNarrow.alignTo henv halign
    refine checkPositivity.loop.succ.scopeWF Hc hsourceFull htype₀ ?_
    intro normalized hbelow hnormalized _hbelow₀ hnormalized₀
    have hnormalizedFVars : FVarsIn (· ∈ scope.fvars) normalized :=
      hbelow _ Hruntime.upset htypeNarrow.fvarsIn
    rcases hnormalized with
      ⟨exposedFull, hexposedFull, _hexposedTarget⟩
    rcases TrExpr.alignBack henv halign htypeNarrow htype₀ hnormalized₀ with
      ⟨exposed, hexposed, hexposedEq⟩
    rcases hexposedEq.symm with ⟨exprType, htypeExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun recursive => ∃ result,
            Hc.venv.IsDefEqU decl.uvars scope.toCtx exposed result ∧
            decl.ClassifiedFieldNormalForm levels depth recursive result)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun recursive => ∃ result,
            Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowType result ∧
            decl.ClassifiedFieldNormalForm levels depth recursive result) :=
      Hstep.mono fun _ ⟨result, hresult, hshape⟩ =>
        ⟨result, VEnv.IsDefEqU.trans Hc.checking.tr.wf
          (by simpa [Hstats.uvars] using hscopeWF₀.toCtx)
          (by simpa [Hstats.uvars] using
            (show Hc.venv.IsDefEqU c.lparams.length scope.toCtx narrowType exposed from
              ⟨exprType, htypeExposed⟩)) hresult, hshape⟩
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · apply finish
      exact checkPositivityStep.noOccurrence.WF hocc
        ⟨exposed, (by simpa [Hstats.uvars] using
          (VEnv.IsDefEqU.refl (TrExprS.wf Hc.checking.tr.wf.orderedStrong hscopeWF₀ hexposed))),
          (checkPositivityStep.TrExprS.noIndOccAvailable Hstats.consts.names hlit
            (Hruntime.noIndConsts (decl.types.map (·.name))) hexposed hocc :
            decl.FamilyFreeNormalForm exposed)⟩
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hexposedFull with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases halign.forallE_align henv hdomNarrow hdomNarrowType hbodyNarrow with
            ⟨dom₀, body₀, hdom₀, hdom₀Type, _hdomU, hbody₀, _⟩
          rcases hconsume _ Hc.atCheckLCtx hdom₀ hdom₀Type with
            ⟨consumedDom₀, Hdom₀⟩
          refine finish <| checkPositivityStep.forallE.sourceWF
            (Q := fun recursive => ∃ result,
              Hc.venv.IsDefEqU decl.uvars scope.toCtx (.forallE narrowDom narrowBody) result ∧
              decl.ClassifiedFieldNormalForm levels depth recursive result)
            (recur := fun body =>
              AddInductive.checkPositivity.loop stats ctor idx body fuel)
            Hc hocc' hdomOcc' Hdom hbodyFull Hdom₀ hbody₀ ?_
          intro bodyFull' _hbodyFullEq body₀' _hbody₀Eq hopenedFull _hopened₀
          let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
          have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hnormalizedFVars.1)).1
          rcases Hruntime.unannotatedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
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
          have Hrec := ih Hc' Hruntime' halign' Hstats' hlevels hlit hopenedNarrow
            (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          exact Hrec.mono fun _ ⟨result, hresult, hshape⟩ => by
            obtain ⟨domLevel, hdomTyped⟩ := hdomNarrowType
            obtain ⟨bodyLevel, hbodyTyped⟩ := hbodyNarrowType
            have hdomTyped' : Hc.venv.HasType decl.uvars scope.toCtx narrowDom (.sort domLevel) := by
              simpa [Hstats.uvars] using hdomTyped
            have hbodyTyped' : Hc.venv.HasType decl.uvars
                (narrowDom :: scope.toCtx) narrowBody (.sort bodyLevel) := by
              simpa [Hstats.uvars] using hbodyTyped
            have hbodyctx : OnCtx (narrowDom :: scope.toCtx)
                (Hc.venv.IsType decl.uvars) := by
              refine ⟨?_, _, hdomTyped'⟩
              simpa [Hstats.uvars] using hscopeWF₀.toCtx
            have hresult' : Hc.venv.IsDefEqU decl.uvars
                (narrowDom :: scope.toCtx) narrowBody result := hresult
            exact ⟨.forallE narrowDom result,
              ⟨_, .forallEDF hdomTyped'
                (hresult'.of_l Hc.checking.tr.wf hbodyctx hbodyTyped')⟩,
              hshape.forallE
                (checkPositivityStep.TrExprS.noIndOccAvailable Hstats.consts.names
                  hlit (Hruntime.noIndConsts (decl.types.map (·.name))) hdomNarrow hdomOcc')⟩
    · cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        apply finish
        exact checkPositivityStep.validApplication.WF hocc' hforall hvalid
          ⟨exposed, (by simpa [Hstats.uvars] using
            (VEnv.IsDefEqU.refl (TrExprS.wf Hc.checking.tr.wf.orderedStrong hscopeWF₀ hexposed))),
            checkPositivityStep.isValidIndApp?.uniformNormalForm Hstats hexposed
              hvalid hlevels hlit (Hruntime.noIndConsts (decl.types.map (·.name)))⟩

/-- Source-facing form of the executable positivity check. The levels
premise is obtained from `HeaderStatsWF.levelParamsTranslation`;
it is preserved while recursive binders are opened. -/
theorem checkPositivity.uniformNormalFormScoped
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hlevels : stats.levels.mapM (VLevel.ofLevel c.lparams) = some levels)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun recursive => ∃ normalized,
        Hc.venv.IsDefEqU decl.uvars scope.toCtx narrowType normalized ∧
        decl.ClassifiedFieldNormalForm levels depth recursive normalized) := by
  apply checkPositivity.WF
  exact checkPositivity.loop.uniformNormalFormScoped Hc Hruntime halign Hstats
    hlevels hconsume hlit htypeNarrow htypeFull


end VerifyInductive
end Lean4Lean
