import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Formation
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expression
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Nested.Lowering.OccurrenceTyping

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Typing of the head of an auxiliary family

`AuxiliaryHeadTyping` records the restored nested application `I Ds` of an auxiliary family,
closed over the parameter context, with its translation and typing (section 3.3 of
the design notes). The file reads the container application, its arguments and its
universe arity off the validated translation of the cached nested application. -/

/-- Source-facing typing of the head of an auxiliary family: the
restored nested application `I Ds`, closed over the common parameter
context, together with its translation and its typing there.  No index
telescope or result sort is fixed: for a nested occurrence of an indexed
family `I` the head is a type family rather than a type. -/
structure AuxiliaryHeadTyping
    (env : VEnv) (levelParams : List Name)
    (parameterDomains : List VExpr) (sourceFamily : Expr) where
  family : VExpr
  familyType : VExpr
  familyTyping : env.HasType levelParams.length parameterDomains.reverse
    family familyType
  sourceTranslation : TrExprS env levelParams
    (abstractForallContext parameterDomains []) sourceFamily family

/-- Context transport also retains the pointwise definitional equality to
the targets translated in the source context.  It is used when the cached application
and the generated header expose definitionally equal, but not syntactically
identical, parameter telescopes. -/
theorem TrExprS.forall₂DefEqDFCWithTargets
    (henv : env.WF)
    (Hctx : VLCtx.IsDefEq env lparams.length sourceCtx targetCtx)
    (H : List.Forall₂ (TrExprS env lparams sourceCtx) sources targets) :
    ∃ targets',
      List.Forall₂ (TrExprS env lparams targetCtx) sources targets' ∧
      List.Forall₂
        (env.IsDefEqU lparams.length targetCtx.toCtx) targets' targets := by
  induction H with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons Hhead Htail ih =>
    rcases Hhead.defeqDFC henv Hctx with ⟨target, Htarget⟩
    rcases ih with ⟨targets, Htargets, Heq⟩
    have HtargetEq := Htarget.uniq henv (Hctx.symm henv.orderedStrong) Hhead
    exact ⟨target :: targets, .cons Htarget Htargets,
      .cons HtargetEq Heq⟩

/-- The validated translation of a generated family's cached source
application exposes the exact abstract container application and an ordered
translation of every specialized parameter.  In particular, the abstract
arguments are closed in precisely the common-parameter context; no
constructor-field binder can occur in them.

This is the source spine needed both to construct the specialized
auxiliary family (`VInductiveType.directAuxiliary`) and, after weakening, to interpret an
actual replaced occurrence.
-/
theorem AuxiliaryFamilySpecialization.abstractContainerApplication
    (H : AuxiliaryFamilySpecialization prodEnv params nestedAux family)
    (R : AuxiliaryHeadTyping venv lparams parameterDomains
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars))
    (henv : venv.WF)
    (hparams : OnCtx parameterDomains.reverse
      (venv.IsType lparams.length)) :
    ∃ abstractLevels baseArgs,
      H.levels.mapM (VLevel.ofLevel lparams) = some abstractLevels ∧
      baseArgs.length = H.nestedNParams ∧
      List.Forall₂
        (TrExprS venv lparams
          (abstractForallContext parameterDomains []))
        ((H.args.toList.take H.nestedNParams).map
          (fun arg => arg.abstractList H.selection.fvars))
        baseArgs ∧
      (∀ arg ∈ baseArgs, arg.ClosedN parameterDomains.length) ∧
      R.family = VExpr.mkApps
      (.const H.sourceName abstractLevels) baseArgs := by
  have hsourceApp :
      mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams H.args =
        Expr.mkAppList (.const H.sourceName H.levels)
          (H.args.toList.take H.nestedNParams) := by
    apply Expr.mkAppRange_eq
        (l₁ := []) (l₂ := H.args.toList.take H.nestedNParams)
        (l₃ := H.args.toList.drop H.nestedNParams)
    · simp
    · rfl
    · simpa using Nat.min_eq_left H.argsArity
  have habstractApp :
      (Expr.mkAppList (.const H.sourceName H.levels)
        (H.args.toList.take H.nestedNParams)).abstractList
          H.selection.fvars =
        Expr.mkAppList (.const H.sourceName H.levels)
          ((H.args.toList.take H.nestedNParams).map
            (fun arg => arg.abstractList H.selection.fvars)) := by
    have go : ∀ (args : List Expr) (head : Expr),
        (Expr.mkAppList head args).abstractList H.selection.fvars =
          Expr.mkAppList (head.abstractList H.selection.fvars)
            (args.map (fun arg => arg.abstractList H.selection.fvars)) := by
      intro args
      induction args with
      | nil => simp
      | cons arg args ih =>
        intro head
        simp [Expr.mkAppList, Expr.abstractList_app, ih]
    simpa using go (H.args.toList.take H.nestedNParams)
      (.const H.sourceName H.levels)
  let targetFamily : VExpr := R.family
  have Htranslated : TrExprS venv lparams
      (abstractForallContext parameterDomains [])
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars) targetFamily :=
    R.sourceTranslation
  rw [hsourceApp, habstractApp] at Htranslated
  rcases checkPositivityStep.TrExprS.mkAppList_inv Htranslated with
    ⟨abstractHead, baseArgs, Hhead, HbaseArgs, hfamily⟩
  have hvlctxWF :
      (abstractForallContext parameterDomains []).WF venv lparams.length := by
    have go : ∀ domains : List VExpr,
        OnCtx domains (venv.IsType lparams.length) →
        VLCtx.WF venv lparams.length
          (domains.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl)) := by
      intro domains Hdomains
      induction domains with
      | nil => trivial
      | cons domain domains ih =>
        have Hdomain : venv.IsType lparams.length
            (VLCtx.toCtx (domains.map fun type =>
              ((none, .vlam type) :
                Option (FVarId × List FVarId) × VLocalDecl))) domain := by
          rw [VLCtx.toCtx_map_anonymousLams]
          exact Hdomains.2
        exact ⟨ih Hdomains.1, nofun, Hdomain⟩
    simpa [abstractForallContext] using go parameterDomains.reverse hparams
  cases Hhead with
  | const _ hlevels _ =>
    refine ⟨_, baseArgs, hlevels, ?_, HbaseArgs, ?_, ?_⟩
    · have hlength := Lean4Lean.List.Forall₂.length_eq HbaseArgs
      simpa using hlength.symm.trans (by
        simp [Nat.min_eq_left H.argsArity])
    · intro arg harg
      rcases Lean4Lean.List.Forall₂.forall_exists_r HbaseArgs arg harg with
        ⟨sourceArg, _hsourceArg, Harg⟩
      have HargWF := Harg.wf henv.orderedStrong hvlctxWF
      have hctxClosed : CtxClosed
          (abstractForallContext parameterDomains []).toCtx := by
        simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
          VEnv.CtxWF.closed henv.ordered hparams
      have Hclosed := HargWF.closedN henv.ordered hctxClosed
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hclosed
    · simpa [targetFamily] using hfamily

/-- The source head of a restored auxiliary-family application exposes the
exact abstract constant installed for its container.  This is deliberately a
single environment-indexed lookup: it does not assert that translating an
arbitrary constant is preserved by unrelated environment extensions. -/
theorem AuxiliaryFamilySpecialization.abstractContainerLookup
    (H : AuxiliaryFamilySpecialization prodEnv params nestedAux family)
    (R : AuxiliaryHeadTyping venv lparams parameterDomains
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars)) :
    ∃ abstractFamily,
      venv.constants H.sourceName = some abstractFamily := by
  have hsourceApp :
      mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams H.args =
        Expr.mkAppList (.const H.sourceName H.levels)
          (H.args.toList.take H.nestedNParams) := by
    apply Expr.mkAppRange_eq
        (l₁ := []) (l₂ := H.args.toList.take H.nestedNParams)
        (l₃ := H.args.toList.drop H.nestedNParams)
    · simp
    · rfl
    · simpa using Nat.min_eq_left H.argsArity
  have habstractApp :
      (Expr.mkAppList (.const H.sourceName H.levels)
        (H.args.toList.take H.nestedNParams)).abstractList
          H.selection.fvars =
        Expr.mkAppList (.const H.sourceName H.levels)
          ((H.args.toList.take H.nestedNParams).map
            (fun arg => arg.abstractList H.selection.fvars)) := by
    have go : ∀ (args : List Expr) (head : Expr),
        (Expr.mkAppList head args).abstractList H.selection.fvars =
          Expr.mkAppList (head.abstractList H.selection.fvars)
            (args.map (fun arg => arg.abstractList H.selection.fvars)) := by
      intro args
      induction args with
      | nil => simp
      | cons arg args ih =>
        intro head
        simp [Expr.mkAppList, Expr.abstractList_app, ih]
    simpa using go (H.args.toList.take H.nestedNParams)
      (.const H.sourceName H.levels)
  rcases R with ⟨_family, _familyType, _familyTyping, Htranslated⟩
  rw [hsourceApp, habstractApp] at Htranslated
  rcases checkPositivityStep.TrExprS.mkAppList_inv Htranslated with
    ⟨_abstractHead, _baseArgs, Hhead, _HbaseArgs, _hfamily⟩
  cases Hhead with
  | const hlookup _hlevels _huvars => exact ⟨_, hlookup⟩

/-- The concrete universe specialization recorded by the auxiliary builder
has exactly the arity of the environment-indexed abstract container selected
by the restored source application.  This is read from the `TrExprS.const`
node of that exact application; it is not a global constant-preservation
principle. -/
theorem AuxiliaryFamilySpecialization.levelsLengthOfAbstractLookup
    (H : AuxiliaryFamilySpecialization prodEnv params nestedAux family)
    (R : AuxiliaryHeadTyping venv lparams parameterDomains
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars))
    (hlookup : venv.constants H.sourceName = some abstractFamily) :
    H.levels.length = abstractFamily.uvars := by
  have hsourceApp :
      mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams H.args =
        Expr.mkAppList (.const H.sourceName H.levels)
          (H.args.toList.take H.nestedNParams) := by
    apply Expr.mkAppRange_eq
        (l₁ := []) (l₂ := H.args.toList.take H.nestedNParams)
        (l₃ := H.args.toList.drop H.nestedNParams)
    · simp
    · rfl
    · simpa using Nat.min_eq_left H.argsArity
  have habstractApp :
      (Expr.mkAppList (.const H.sourceName H.levels)
        (H.args.toList.take H.nestedNParams)).abstractList
          H.selection.fvars =
        Expr.mkAppList (.const H.sourceName H.levels)
          ((H.args.toList.take H.nestedNParams).map
            (fun arg => arg.abstractList H.selection.fvars)) := by
    have go : ∀ (args : List Expr) (head : Expr),
        (Expr.mkAppList head args).abstractList H.selection.fvars =
          Expr.mkAppList (head.abstractList H.selection.fvars)
            (args.map (fun arg => arg.abstractList H.selection.fvars)) := by
      intro args
      induction args with
      | nil => simp
      | cons arg args ih =>
        intro head
        simp [Expr.mkAppList, Expr.abstractList_app, ih]
    simpa using go (H.args.toList.take H.nestedNParams)
      (.const H.sourceName H.levels)
  let targetFamily : VExpr := R.family
  have Htranslated : TrExprS venv lparams
      (abstractForallContext parameterDomains [])
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars) targetFamily :=
    R.sourceTranslation
  rw [hsourceApp, habstractApp] at Htranslated
  rcases checkPositivityStep.TrExprS.mkAppList_inv Htranslated with
    ⟨_abstractHead, _baseArgs, Hhead, _HbaseArgs, _hfamily⟩
  cases Hhead with
  | const habstract _hlevels harity =>
    have hfamily : _ = abstractFamily :=
      Option.some.inj (habstract.symm.trans hlookup)
    simpa [hfamily] using harity

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive


/-- A validated nested application gives the `AuxiliaryHeadTyping` of an auxiliary
family head after its independently recovered parameter context is converted
to the given parameter context. -/
theorem ClosedNestedOccurrenceTyping.toAuxiliaryHeadTyping
    (H : ClosedNestedOccurrenceTyping venv lparams res selection e)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse) :
    Nonempty (AuxiliaryHeadTyping venv lparams parameterDomains
      (e.abstractList selection.fvars)) := by
  rcases H.residualAtDefEqParameterDomains henv parameterDomains Hcontexts with
    ⟨family, familyType, Hfamily, HfamilyType⟩
  exact ⟨{
    family := family
    familyType := familyType
    familyTyping := by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HfamilyType
    sourceTranslation := Hfamily }⟩

/-- The concrete source head retained for an auxiliary family is the container
family constant applied to exactly the arguments used by auxiliary
construction, closed over that construction's parameter selection.  Its
translation is retained exactly, rather than only up to typing. -/
theorem AuxiliaryFamilySpecialization.cachedAuxiliaryHeadTyping
    (H : AuxiliaryFamilySpecialization sourceEnv result.params
      finalState.nestedAux family)
    (Hmap : NestedAuxMapModels result finalState)
    {resultSelection : CDeclArray result.lctx result.params}
    (hresultNodup : resultSelection.fvars.Nodup)
    (Htranslations : ClosedNestedOccurrenceTypings venv lparams result
      resultSelection)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : ∀ Haux : ClosedNestedOccurrenceTyping venv lparams
      result resultSelection H.data.nested,
      VEnv.IsDefEqCtx venv lparams.length [] parameterDomains.reverse
        Haux.domains.reverse) :
    Nonempty (AuxiliaryHeadTyping venv lparams parameterDomains
      ((mkAppRange (.const H.sourceName H.levels) 0 H.nestedNParams
        H.args).abstractList H.selection.fvars)) := by
  rcases H.closedAuxiliaryTranslation Hmap Htranslations with ⟨Haux⟩
  have Hrealized := Haux.toAuxiliaryHeadTyping henv
    parameterDomains (Hcontexts Haux)
  simpa only [H.cachedClosureAlpha resultSelection hresultNodup] using Hrealized

end VerifyInductive
end Lean4Lean
