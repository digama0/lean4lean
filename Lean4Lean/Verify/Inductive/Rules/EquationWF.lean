import Lean4Lean.Verify.Inductive.Rules.Lhs
import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursiveShapeTranslations
import Lean4Lean.Verify.Inductive.Recursor.Metadata

/-! Well-formedness of the generator's equations for the instance of the recursor
construction (`RecursorCheck.canonicalGeneration`), part of the typing of the iota rules
(section 3.2 of the design notes).

Each generated rule of the executable is typed in the fixed equation context
`parameterDecls ++ motives ++ minors ++ equationFields` (`canonicalEquationDomains`).
This file

* packages that typing with its context as `EquationFrame` (`equationFrame`,
  with the minor-domain split and the field alignment);
* identifies the context with the generator's equation domains
  `g.params ++ g.motives ++ g.minors ++ insertBinders (fieldTypes.map instL) extra`
  up to `IsDefEqCtx` (parameters, motives and minors syntactically, fields by
  the retained field alignment);
* transports the typing of the executable rule to the generator's equation bodies once
  those bodies are translations of the same residual sources;
* closes everything under `wrapLams`/`wrapForalls` and indexes the flattened
  constructor list to obtain `VDefEq.WF` for every generated equation.

The input is `EquationBodyTranslations`: the generator's LHS, RHS and type
bodies translate the rule's residual sources in the generator's own telescope.
`rhsResidualOfClosed` derives the RHS component from a closed translation
`TrExprS [] rule.rhs (g.equation k).rhs`, and
`RecursorCheck.equationBodyTranslations_of` (`Rules/RuleTranslations.lean`)
derives all of it.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

/-! ### The generator's equation, by components -/

namespace InductiveSignature
namespace Instance
variable {s : InductiveSignature}

/-- The binder domains of the generated equation for constructor `index`. -/
def equationDomains (g : Instance s) (index : Fin s.constructors.size) : List VExpr :=
  g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
      (s.families.size + s.constructors.size)

/-- The constructor indices of equation `index`, beneath its telescope. -/
def equationIndices (g : Instance s) (index : Fin s.constructors.size) : List VExpr :=
  s.constructors[index].indices.map fun e =>
    (e.instL g.levels).liftN (s.families.size + s.constructors.size)
      s.constructors[index].fields.length

/-- The constructor application that is the major premise of equation `index`. -/
def equationMajor (g : Instance s) (index : Fin s.constructors.size) : VExpr :=
  g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0

/-- The open left-hand side of equation `index`. -/
def equationLhsBody (g : Instance s) (index : Fin s.constructors.size)
    (mode : HeadMode := .recursor) : VExpr :=
  VExpr.mkApps (g.recursorHead mode s.constructors[index].owner)
    (vars (s.params.length + (s.families.size + s.constructors.size))
        s.constructors[index].fields.length ++
      g.equationIndices index ++ [g.equationMajor index])

/-- The open right-hand side of equation `index`. -/
def equationRhsBody (g : Instance s) (index : Fin s.constructors.size)
    (mode : HeadMode := .recursor) : VExpr :=
  VExpr.mkApps
    (.bvar (s.constructors[index].fields.length + s.constructors.size - 1 - index.val))
    (vars s.constructors[index].fields.length 0 ++
      (recursiveFields s.constructors[index]).map fun (field, r) =>
        g.recursiveCall s.constructors[index] field r mode)

/-- The open type of equation `index`: its motive at the constructor. -/
def equationTypeBody (g : Instance s) (index : Fin s.constructors.size) : VExpr :=
  VExpr.mkApps
    (.bvar (s.constructors[index].fields.length + s.constructors.size +
      (s.families.size - 1 - s.constructors[index].owner.val)))
    (g.equationIndices index ++ [g.equationMajor index])

/-- `equation` is the telescope closure of its components. -/
theorem equation_eq (g : Instance s) (index : Fin s.constructors.size)
    (mode : HeadMode := .recursor) :
    g.equation index mode =
      { uvars := g.uvars
        lhs := VExpr.wrapLams (g.equationDomains index) (g.equationLhsBody index mode)
        rhs := VExpr.wrapLams (g.equationDomains index) (g.equationRhsBody index mode)
        type := VExpr.wrapForalls (g.equationDomains index) (g.equationTypeBody index) } :=
  rfl

theorem minors_getElem (g : Instance s) (k : Nat) (hk : k < s.constructors.size) :
    g.minors[k]'(by rw [length_minors]; exact hk) = g.minor s.constructors[k] k := by
  simp [minors]

end Instance
end InductiveSignature

namespace VerifyInductive

/-! ### Generic transport of wrapped equations -/

/-- A closed wrapped equation remains well formed when its domains are
replaced by a definitionally equal telescope and its three bodies by
definitionally equal bodies (all compared in the original open context). -/
theorem VDefEq.WF.transportWrapped {env : VEnv} (henv : env.WF)
    {uvars : Nat} {domains domains' : List VExpr}
    {lhsBody rhsBody typeBody lhsBody' rhsBody' typeBody' : VExpr}
    (hctx : OnCtx domains.reverse (env.IsType uvars))
    (hlhs : env.HasType uvars domains.reverse lhsBody typeBody)
    (hrhs : env.HasType uvars domains.reverse rhsBody typeBody)
    (hdomains : VEnv.IsDefEqCtx env uvars [] domains.reverse domains'.reverse)
    (hlhsEq : env.IsDefEqU uvars domains.reverse lhsBody lhsBody')
    (hrhsEq : env.IsDefEqU uvars domains.reverse rhsBody rhsBody')
    (htypeEq : env.IsDefEqU uvars domains.reverse typeBody typeBody') :
    ({ uvars := uvars
       lhs := VExpr.wrapLams domains' lhsBody'
       rhs := VExpr.wrapLams domains' rhsBody'
       type := VExpr.wrapForalls domains' typeBody' } : VDefEq).WF env := by
  have hlhs' : env.HasType uvars domains.reverse lhsBody' typeBody' :=
    (hlhs.defeqU_l henv hctx hlhsEq).defeqU_r henv hctx htypeEq
  have hrhs' : env.HasType uvars domains.reverse rhsBody' typeBody' :=
    (hrhs.defeqU_l henv hctx hrhsEq).defeqU_r henv hctx htypeEq
  exact VDefEq.wf_of_wrappedBodies
    (hdomains.symm henv.ordered).isType
    (hlhs'.defeqDFC henv.ordered hdomains)
    (hrhs'.defeqDFC henv.ordered hdomains)

/-- Variant of `transportWrapped` in which the bodies are compared through
translations of common residual sources over the two telescopes. -/
theorem VDefEq.WF.transportTranslatedWrapped {env : VEnv} (henv : env.WF)
    {Us : List Name} {domains domains' : List VExpr}
    {lhsSource rhsSource typeSource : Expr}
    {lhsBody rhsBody typeBody lhsBody' rhsBody' typeBody' : VExpr}
    (hctx : OnCtx domains.reverse (env.IsType Us.length))
    (hlhs : env.HasType Us.length domains.reverse lhsBody typeBody)
    (hrhs : env.HasType Us.length domains.reverse rhsBody typeBody)
    (hdomains : VEnv.IsDefEqCtx env Us.length [] domains.reverse
      domains'.reverse)
    (Hlhs : TrExprS env Us (abstractForallContext domains []) lhsSource lhsBody)
    (Hrhs : TrExprS env Us (abstractForallContext domains []) rhsSource rhsBody)
    (Htype : TrExprS env Us (abstractForallContext domains []) typeSource typeBody)
    (Hlhs' : TrExprS env Us (abstractForallContext domains' []) lhsSource lhsBody')
    (Hrhs' : TrExprS env Us (abstractForallContext domains' []) rhsSource rhsBody')
    (Htype' : TrExprS env Us (abstractForallContext domains' []) typeSource
      typeBody') :
    ({ uvars := Us.length
       lhs := VExpr.wrapLams domains' lhsBody'
       rhs := VExpr.wrapLams domains' rhsBody'
       type := VExpr.wrapForalls domains' typeBody' } : VDefEq).WF env :=
  VDefEq.WF.transportWrapped henv hctx hlhs hrhs hdomains
    (TrExprS.uniqAbstractForallContext Hlhs Hlhs' henv hdomains)
    (TrExprS.uniqAbstractForallContext Hrhs Hrhs' henv hdomains)
    (TrExprS.uniqAbstractForallContext Htype Htype' henv hdomains)

/-! ### The executable rule's equation frame, with its context exposed -/

/-- The fixed equation context of a generated rule: cached parameters, the
inserted motive/minor block, and the field domains of the field frame weakened
beneath that block. -/
def canonicalEquationDomains (params motives minors fieldDomains : List VExpr) :
    List VExpr :=
  params ++ (motives ++ minors) ++
    (liftContextPrefix (motives ++ minors).length fieldDomains.reverse).reverse

/-- The equation of one generated rule of the executable together with the
context in which it is typed: the domains are `canonicalEquationDomains` of the
recursor telescope `telescope` and the field frame `frame`; the selected minor
domain splits into `fieldDomains ++ hypothesisDomains`, and the frame's fields are definitionally
equal to the minor's fields re-weakened beneath the later minors. -/
structure RecursorCheck.RuleAlignment.EquationFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) where
  frame : A.FieldFrame
  telescope : RecursorTypeTelescope H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (H.generated.entry owner howner).info.type H.entries[owner].2.type
    stats.params.size (H.recInfos.map (·.motive)).size
    (H.recInfos.flatMap (·.minors)).size
    H.recInfos[owner]!.indices.size owner
  fieldDomains : List VExpr
  hypothesisDomains : List VExpr
  targetResidual : VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  fieldDomains_length : fieldDomains.length = A.rule.allArgs.size
  hypothesisDomains_length :
    hypothesisDomains.length = A.rule.recursiveArgs.size
  minor_eq : telescope.minors[recursorMinorOffset indTypes owner + i]! =
    VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual
  fields_defeq :
    let inserted := telescope.motives ++ telescope.minors
    let outer := inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx
    let later := telescope.minors.drop (recursorMinorOffset indTypes owner + i + 1)
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      ((liftContextPrefix inserted.length frame.fieldDomains.reverse).reverse.reverse ++
        outer)
      ((liftContextPrefix (later.length + 1) fieldDomains.reverse).reverse.reverse ++
        outer)
  ctx : OnCtx
    (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
      telescope.motives telescope.minors frame.fieldDomains).reverse
    (H.outVEnv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)
  lhs_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
        telescope.motives telescope.minors frame.fieldDomains) [])
    (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody
  rhs_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
        telescope.motives telescope.minors frame.fieldDomains) [])
    (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody
  type_translation : TrExprS H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
        telescope.motives telescope.minors frame.fieldDomains) [])
    ((Expr.app
      (mkAppN H.recInfos[owner]!.motive
        (AddInductive.getIIndices stats A.rule.target).2)
      A.rule.sourceConstructorMajor).abstractList A.rule.binders)
    typeBody
  lhs_typing : H.outVEnv.HasType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
      telescope.motives telescope.minors frame.fieldDomains).reverse
    lhsBody typeBody
  rhs_typing : H.outVEnv.HasType
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
      telescope.motives telescope.minors frame.fieldDomains).reverse
    rhsBody typeBody

/-- Positive-arity case of `equationFrame`. -/
theorem
    RecursorCheck.RuleAlignment.positiveEquationFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    Nonempty A.EquationFrame := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.installedRhsPositiveArityDetailed hpositive with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      equationFields, rhsBody, _rhsType, hfields, hhypotheses,
      hminorType, hequationFieldsLength, hequationFields, _hrhsType,
      hrhsBody, Hpartial, Hfield, Hctx, HrhsTranslation, _HrhsTyping⟩
  subst equationFields
  let equationFields :=
    (liftContextPrefix (T.motives ++ T.minors).length
      B.fieldDomains.reverse).reverse
  let inserted := T.motives ++ T.minors
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedResidual := targetResidual.liftN remaining.length
    (fieldDomains.length + hypothesisDomains.length)
  let canonicalDomains := VExpr.liftClosedDomains C.bodyTypes 0
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  rcases A.installedFixedLhsBodyFor B T with
    ⟨lhsBody, lhsType, HlhsCtx, HlhsTranslation, HlhsTyping,
      HlhsType, HexpectedTranslation⟩
  have HlhsCtx' : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls]
      using HlhsCtx
  have HlhsTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls]
      using HlhsTranslation
  have HlhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody lhsType := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls]
      using HlhsTyping
  have HexpectedTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (expected.abstractList A.rule.binders) lhsType := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls,
      expected] using HexpectedTranslation
  rcases A.installedSelectedMinorAlignedResidual with
    ⟨Tsource, S, traversal, HS, _hypothesisOrigins,
      sourceFieldDomains, sourceHypothesisDomains, sourceResidual,
      _hhypothesisStats, _hhypothesisRecInfos, hconstructor,
      htraversalFields, hfieldFVars, hclosedTargets, _hselectedOwner,
      hvalid, hmotiveApp, hsourceFields, hsourceHypotheses,
      hsourceFieldDomains, hsourceHypothesisDomains, hsourceMinorType,
      HsourceResidual, HsourceResidualType⟩
  have hTsource : Tsource = T := Tsource.eq T
  subst Tsource
  have hsourceDomains :
      sourceFieldDomains ++ sourceHypothesisDomains =
        fieldDomains ++ hypothesisDomains := by
    exact VExpr.wrapForalls_prefix_domains_eq
      (n := A.rule.allArgs.size + A.rule.recursiveArgs.size)
      (suffix := [])
      (by simp [hsourceFieldDomains, hsourceHypothesisDomains])
      (by simp [hfields, hhypotheses])
      (by simpa using hsourceMinorType.symm.trans hminorType)
  have hsourceFieldsDomains : sourceFieldDomains = fieldDomains :=
    List.append_inj_left hsourceDomains
      (hsourceFieldDomains.trans hfields.symm)
  have hsourceHypothesesDomains :
      sourceHypothesisDomains = hypothesisDomains :=
    List.append_inj_right hsourceDomains
      (hsourceFieldDomains.trans hfields.symm)
  subst sourceFieldDomains
  subst sourceHypothesisDomains
  have hsourceResidual : sourceResidual = targetResidual := by
    apply VExpr.wrapForalls_left_cancel (fieldDomains ++ hypothesisDomains)
    rw [← hsourceMinorType, ← hminorType]
  subst sourceResidual
  have hfieldClosure := A.alignedMotiveAppFieldClosure S traversal
    hconstructor hclosedTargets hvalid
      hmotiveApp hsourceFields
  have hsourceAligned := A.alignedPositiveResidualSource S HS traversal
    hmotiveApp hfieldClosure hsourceFields hsourceHypotheses
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simp [remaining, later]
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
  have hremainingSourceLength :
      (A.rule.minors_bound.fvars.drop minorIdx).length = remaining.length := by
    simp [remaining, A.rule.minors_bound.length_fvars, T.minors_length]
  let sourceOuter := T.params ++ T.motives ++ T.minors.take minorIdx
  have HsourceResidual' : TrExprS H.outVEnv Us
      (abstractForallContext
        (sourceOuter ++ (fieldDomains ++ hypothesisDomains)) [])
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size))
      targetResidual := by
    simpa [sourceOuter, abstractForallContext, List.reverse_append,
      List.map_append, List.append_assoc] using HsourceResidual
  have Hinserted₀ := Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
    (outer := sourceOuter) (inner := fieldDomains ++ hypothesisDomains)
    H.outVEnvWF.ordered HsourceResidual' remaining
  have houterRemaining : sourceOuter ++ remaining =
      T.params ++ T.motives ++ T.minors := by
    simp [sourceOuter, remaining, List.append_assoc]
  have hliftedInner :
      (liftContextPrefix remaining.length
        (fieldDomains ++ hypothesisDomains).reverse).reverse =
        installedFields ++ installedHypotheses := by
    simpa [installedFields, installedHypotheses] using
      liftContextPrefix_reverse_append remaining.length fieldDomains
        hypothesisDomains
  have Hinserted : TrExprS H.outVEnv Us
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++ installedFields ++
          installedHypotheses) [])
      ((expected.abstractList A.rule.binders).liftLooseBVars' 0
        A.rule.recursiveArgs.size)
      installedResidual := by
    have hinnerLength : (fieldDomains ++ hypothesisDomains).length =
        A.rule.allArgs.size + A.rule.recursiveArgs.size := by
      simp [hfields, hhypotheses]
    have hsourceAligned' := hsourceAligned
    simp only [minorIdx, hremainingSourceLength] at hsourceAligned'
    rw [hinnerLength] at Hinserted₀
    rw [hsourceAligned'] at Hinserted₀
    dsimp only at Hinserted₀
    rw [houterRemaining, hliftedInner] at Hinserted₀
    simpa [installedResidual, expected, Expr.abstractList_app,
      hinnerLength.symm, List.append_assoc] using Hinserted₀
  have Hparams := H.installedRecursorParameterContextFor howner T
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [Us, ← H.parameterDecls] using Hparams
  let equationPrefix := equationFields.reverse ++ inserted.reverse
  let installedPrefix := installedFields.reverse ++ inserted.reverse
  have Hfield' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ H.parameterSuffix.parameterDecls.toCtx)
      (installedPrefix ++ H.parameterSuffix.parameterDecls.toCtx) := by
    simpa [Us, equationPrefix, installedPrefix, installedFields,
      equationFields, inserted, later, minorIdx, hremainingLength,
      List.append_assoc]
      using Hfield
  have HfieldT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ T.params.reverse)
      (installedPrefix ++ T.params.reverse) := by
    have Hrebased := VEnv.IsDefEqCtx.rebaseCommonSuffix
      H.outVEnvWF Hparams' Hfield'
    simpa [equationPrefix, installedPrefix, installedFields,
      List.append_assoc] using Hrebased
  have HequationParams := VEnv.IsDefEqCtx.extendSamePrefix
    Hparams' HfieldT.isType
  have HbaseMixed := VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
    (HfieldT.symm H.outVEnvWF.ordered) HequationParams
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      equationDomains.reverse := by
    simpa [equationPrefix, installedPrefix, equationDomains,
      equationFields, inserted, List.reverse_append, List.append_assoc]
      using HbaseMixed
  have Hpartial' : H.outVEnv.HasType Us.length equationDomains.reverse
      (VExpr.mkApps (.bvar (equationFields.length + later.length))
        (bvarSpine equationFields.length))
      (VExpr.wrapForalls installedHypotheses installedResidual) := by
    simpa [equationDomains, installedHypotheses, installedResidual,
      equationFields, hremainingLength, later, remaining, inserted,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc]
      using Hpartial
  have HpartialTypeInstalled : H.outVEnv.IsType Us.length
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      (VExpr.wrapForalls installedHypotheses installedResidual) :=
    (Hpartial'.isType H.outVEnvWF HlhsCtx').defeqDFC
      H.outVEnvWF.ordered (Hbase.symm H.outVEnvWF.ordered)
  have HopenedInstalled := VEnv.IsType.wrapForalls_inv
    H.outVEnvWF.ordered Hbase.isType HpartialTypeInstalled
  have HfullBase := VEnv.IsDefEqCtx.extendSamePrefix Hbase
    HopenedInstalled.1
  have HinsertedExact : TrExpr H.outVEnv Us
      (abstractForallContext (equationDomains ++ installedHypotheses) [])
      ((expected.abstractList A.rule.binders).liftLooseBVars' 0
        A.rule.recursiveArgs.size)
      installedResidual := by
    have HfullBase' : VEnv.IsDefEqCtx H.outVEnv Us.length []
        (T.params ++ T.motives ++ T.minors ++ installedFields ++
          installedHypotheses).reverse
        (equationDomains ++ installedHypotheses).reverse := by
      simpa [List.reverse_append, List.append_assoc] using HfullBase
    have Hvlctx := abstractForallContext.isDefEq HfullBase'
    simpa [abstractForallContext, List.reverse_append, List.map_append,
      List.append_assoc] using Hinserted.defeqDFC' H.outVEnvWF Hvlctx
  have Hhypotheses := A.installedRecursiveHypothesisContext B T C
    fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      hminorType (by simpa [minorIdx, remaining, installedFields,
        equationDomains, equationFields, inserted, List.append_assoc]
        using Hbase)
  have Hhypotheses' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ equationDomains.reverse)
      (canonicalDomains.reverse ++ equationDomains.reverse) := by
    simpa [installedHypotheses, canonicalDomains, equationDomains,
      equationFields, inserted, remaining, minorIdx,
      abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc]
      using Hhypotheses
  have HexpectedWeak : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ canonicalDomains) [])
      ((expected.abstractList A.rule.binders).liftLooseBVars' 0
        canonicalDomains.length)
      (lhsType.liftN canonicalDomains.length 0) := by
    have W := abstractForallContext.bvLift canonicalDomains
      (abstractForallContext equationDomains [])
    simpa [abstractForallContext, List.reverse_append, List.map_append,
      List.append_assoc] using
      HexpectedTranslation'.weakBV H.outVEnvWF.ordered W
  have hcanonicalLength : canonicalDomains.length =
      A.rule.recursiveArgs.size := by
    simp [canonicalDomains]
  rw [hcanonicalLength] at HexpectedWeak
  have HhypothesesDomains : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationDomains ++ installedHypotheses).reverse
      (equationDomains ++ canonicalDomains).reverse := by
    simpa [List.reverse_append, List.append_assoc] using Hhypotheses'
  have HhypothesesV := abstractForallContext.isDefEq HhypothesesDomains
  have HexpectedWeak' := HexpectedWeak.trExpr H.outVEnvWF.ordered
    (HhypothesesV.symm H.outVEnvWF).wf
  have HresidualU := HinsertedExact.uniq H.outVEnvWF
    HhypothesesV HexpectedWeak'
  have HresidualU' : H.outVEnv.IsDefEqU Us.length
      (installedHypotheses.reverse ++ equationDomains.reverse)
      installedResidual (lhsType.liftN A.rule.recursiveArgs.size 0) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append, List.append_assoc] using HresidualU
  rcases HopenedInstalled.2 with
    ⟨residualLevel, HinstalledResidualType⟩
  have HinstalledResidualType' : H.outVEnv.HasType Us.length
      (installedHypotheses.reverse ++ equationDomains.reverse)
      installedResidual (.sort residualLevel) :=
    HinstalledResidualType.defeqDFC H.outVEnvWF.ordered HfullBase
  have Hresidual : H.outVEnv.IsDefEq Us.length
      (installedHypotheses.reverse ++ equationDomains.reverse)
      installedResidual (lhsType.liftN A.rule.recursiveArgs.size 0)
      (.sort residualLevel) :=
    HresidualU'.of_l H.outVEnvWF Hhypotheses'.isType
      HinstalledResidualType'
  rcases VEnv.IsDefEqCtx.closeHeads Hhypotheses'
      A.rule.recursiveArgs.size
      (by simp [installedHypotheses, hhypotheses]) Hresidual with
    ⟨closedLevel, Hclosed⟩
  have Hwhole : H.outVEnv.IsDefEqU Us.length equationDomains.reverse
      (VExpr.wrapForalls installedHypotheses installedResidual)
      (VExpr.wrapForalls canonicalDomains
        (lhsType.liftN canonicalDomains.length 0)) := by
    refine ⟨.sort closedLevel, ?_⟩
    simpa [installedHypotheses, canonicalDomains, hcanonicalLength,
      hhypotheses] using Hclosed
  have HfnCanonical : H.outVEnv.HasType Us.length equationDomains.reverse
      (VExpr.mkApps (.bvar (equationFields.length + later.length))
        (bvarSpine equationFields.length))
      (VExpr.wrapForalls canonicalDomains
        (lhsType.liftN canonicalDomains.length 0)) :=
    Hpartial'.defeqU_r H.outVEnvWF HlhsCtx' Hwhole
  have HbodyTypings : List.Forall₂
      (H.outVEnv.HasType Us.length equationDomains.reverse)
      C.bodies C.bodyTypes := by
    simpa [equationDomains, equationFields, inserted,
      abstractForallContext_toCtx, VLCtx.toCtx, List.reverse_append,
      List.append_assoc] using C.bodyTypings
  rcases VEnv.TypedApplicationSpine.liftClosedDomains
      HfnCanonical HbodyTypings with
    ⟨finalType, Hspine⟩
  have hfinalType : finalType = lhsType := by
    rw [Hspine.result_eq_applyForallType]
    exact VExpr.applyForallType_wrapForalls_liftN canonicalDomains
      C.bodies lhsType (by simp [canonicalDomains])
  have HrhsAtLhs : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody lhsType := by
    rw [hrhsBody]
    rw [← hfinalType]
    simpa [equationFields, later, inserted, equationDomains,
      List.append_assoc]
      using Hspine.hasType
  exact ⟨{
    frame := B
    telescope := T
    fieldDomains := fieldDomains
    hypothesisDomains := hypothesisDomains
    targetResidual := targetResidual
    lhsBody := lhsBody
    rhsBody := rhsBody
    typeBody := lhsType
    fieldDomains_length := hfields
    hypothesisDomains_length := hhypotheses
    minor_eq := hminorType
    fields_defeq := by
      simpa [equationPrefix, installedPrefix, installedFields,
        equationFields, inserted, later, minorIdx, remaining,
        hremainingLength, List.append_assoc] using Hfield'
    ctx := HlhsCtx'
    lhs_translation := HlhsTranslation'
    rhs_translation := HrhsTranslation
    type_translation := HexpectedTranslation'
    lhs_typing := HlhsTyping'
    rhs_typing := HrhsAtLhs }⟩

/-- Zero-arity case of `equationFrame`. -/
theorem
    RecursorCheck.RuleAlignment.zeroEquationFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0) :
    Nonempty A.EquationFrame := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hhypothesesZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.installedMinorApplicationZeroArity hzero with
    ⟨B, T, C, targetResidual, hbodies, hminorType, Hctx, Hminor⟩
  have hframeFields : B.fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (B.fieldDomains_length.trans hfieldsZero)
  let inserted := T.motives ++ T.minors
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let rhsBody : VExpr := .bvar later.length
  let installedResidual := targetResidual.liftN remaining.length 0
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  have Hctx' : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, abstractForallContext_toCtx, VLCtx.toCtx,
      List.append_assoc] using Hctx
  rcases A.installedFixedLhsBodyFor B T with
    ⟨lhsBody, lhsType, HlhsCtx, HlhsTranslation, HlhsTyping,
      HlhsType, HexpectedTranslation⟩
  have HlhsTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls] using HlhsTranslation
  have HlhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody lhsType := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls] using HlhsTyping
  have HlhsType' : H.outVEnv.IsType Us.length equationDomains.reverse
      lhsType := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls] using HlhsType
  have HexpectedTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (expected.abstractList A.rule.binders) lhsType := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls, expected]
      using HexpectedTranslation
  rcases A.installedSelectedMinorAlignedResidual with
    ⟨Tsource, S, traversal, HS, _hypothesisOrigins,
      sourceFieldDomains, sourceHypothesisDomains, sourceResidual,
      _hhypothesisStats, _hhypothesisRecInfos, hconstructor,
      htraversalFields, hfieldFVars, hclosedTargets, _hselectedOwner,
      hvalid, hmotiveApp, hsourceFields, hsourceHypotheses,
      hsourceFieldDomains, hsourceHypothesisDomains, hsourceMinorType,
      HsourceResidual, _HsourceResidualType⟩
  have hTsource : Tsource = T := Tsource.eq T
  subst Tsource
  have hsourceFieldDomainsZero : sourceFieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hsourceFieldDomains.trans hfieldsZero)
  have hsourceHypothesisDomainsZero : sourceHypothesisDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hsourceHypothesisDomains.trans hhypothesesZero)
  subst sourceFieldDomains
  subst sourceHypothesisDomains
  have hsourceResidual : sourceResidual = targetResidual := by
    simpa [VExpr.wrapForalls] using
      hsourceMinorType.symm.trans hminorType
  subst sourceResidual
  have hfieldClosure := A.alignedMotiveAppFieldClosure S traversal
    hconstructor hclosedTargets hvalid
      hmotiveApp hsourceFields
  have hsourceAligned := A.alignedPositiveResidualSource S HS traversal
    hmotiveApp hfieldClosure hsourceFields hsourceHypotheses
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simp [remaining, later]
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
  have hremainingSourceLength :
      (A.rule.minors_bound.fvars.drop minorIdx).length = remaining.length := by
    simp [remaining, A.rule.minors_bound.length_fvars, T.minors_length]
  let sourceOuter := T.params ++ T.motives ++ T.minors.take minorIdx
  have HsourceResidual' : TrExprS H.outVEnv Us
      (abstractForallContext (sourceOuter ++ []) [])
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx) 0)
      targetResidual := by
    simpa [sourceOuter, hzero, abstractForallContext,
      List.reverse_append, List.map_append, List.append_assoc]
      using HsourceResidual
  have Hinserted₀ := Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
    (outer := sourceOuter) (inner := []) H.outVEnvWF.ordered
      HsourceResidual' remaining
  have houterRemaining : sourceOuter ++ remaining =
      T.params ++ T.motives ++ T.minors := by
    simp [sourceOuter, remaining, List.append_assoc]
  have Hinserted : TrExprS H.outVEnv Us
      (abstractForallContext (T.params ++ T.motives ++ T.minors) [])
      (expected.abstractList A.rule.binders) installedResidual := by
    have hsourceAligned' := hsourceAligned
    simp [minorIdx, hfieldsZero, hhypothesesZero,
      hremainingSourceLength] at hsourceAligned'
    rw [← List.append_assoc] at hsourceAligned'
    dsimp only [minorIdx] at Hinserted₀
    simp only [List.length_nil] at Hinserted₀
    rw [hsourceAligned'] at Hinserted₀
    simp [liftContextPrefix, liftContextPrefixAt] at Hinserted₀
    rw [houterRemaining] at Hinserted₀
    simpa [installedResidual, expected, Expr.abstractList_app,
      List.append_assoc] using Hinserted₀
  have Hparams := H.installedRecursorParameterContextFor howner T
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [Us, ← H.parameterDecls] using Hparams
  have HctxPlain : OnCtx
      (inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, inserted, List.reverse_append,
      List.append_assoc] using Hctx'
  have HequationToGenerated := VEnv.IsDefEqCtx.extendSamePrefix
    (Hparams'.symm H.outVEnvWF.ordered) HctxPlain
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors).reverse
      equationDomains.reverse := by
    have Hbase' := HequationToGenerated.symm H.outVEnvWF.ordered
    simpa [equationDomains, inserted, List.reverse_append,
      List.append_assoc] using Hbase'
  have HinsertedExact : TrExpr H.outVEnv Us
      (abstractForallContext equationDomains [])
      (expected.abstractList A.rule.binders) installedResidual :=
    Hinserted.defeqDFC' H.outVEnvWF
      (abstractForallContext.isDefEq Hbase)
  have Hrefl : VEnv.IsDefEqCtx H.outVEnv Us.length []
      equationDomains.reverse equationDomains.reverse :=
    VEnv.IsDefEqCtx.refl Hctx'
  have HreflV := abstractForallContext.isDefEq Hrefl
  have Hexpected' := HexpectedTranslation'.trExpr
    H.outVEnvWF.ordered HreflV.wf
  have HtypeU₀ := HinsertedExact.uniq H.outVEnvWF HreflV Hexpected'
  have HtypeU : H.outVEnv.IsDefEqU Us.length equationDomains.reverse
      installedResidual lhsType := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HtypeU₀
  rcases HlhsType' with ⟨lhsLevel, HlhsSort⟩
  have Htype : H.outVEnv.IsDefEq Us.length equationDomains.reverse
      installedResidual lhsType (.sort lhsLevel) :=
    HtypeU.of_r H.outVEnvWF Hctx' HlhsSort
  have Hminor' : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody installedResidual := by
    simpa [rhsBody, installedResidual, equationDomains, inserted,
      remaining, later, hremainingLength, hframeFields,
      liftContextPrefix, liftContextPrefixAt,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc]
      using Hminor
  have HrhsAtLhs : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody lhsType :=
    Hminor'.defeqU_r H.outVEnvWF Hctx' ⟨.sort lhsLevel, Htype⟩
  have hminorVar : later.length < equationDomains.length := by
    dsimp only [later, equationDomains, inserted]
    simp only [List.length_append, List.length_drop]
    omega
  have HvarTranslation : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar later.length) rhsBody :=
    TrExprS.bvar_of_abstractForallContext equationDomains []
      later.length hminorVar
  have hallArgs : A.rule.allArgs = #[] :=
    Array.eq_empty_of_size_eq_zero hfieldsZero
  have hrecursiveResultsSize : A.rule.recursiveResults.size = 0 := by
    rw [A.rule.recursive_calls.size]
    exact hhypothesesZero
  have hrecursiveResults : A.rule.recursiveResults = #[] :=
    Array.eq_empty_of_size_eq_zero hrecursiveResultsSize
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        later.length := by
    dsimp only [later]
    simp only [List.length_drop, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have hsourceRhs : A.rule.sourceRhsBody.abstractList A.rule.binders =
      .bvar later.length := by
    simpa [hallArgs, hrecursiveResults, Expr.mkAppN_eq_mkAppList,
      Expr.mkAppList] using hsourceShape
  have HrhsTranslation : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsourceRhs]
    exact HvarTranslation
  have hdomainsEq : canonicalEquationDomains
      H.parameterSuffix.parameterDecls.toCtx.reverse T.motives T.minors
      B.fieldDomains = equationDomains := by
    simp [canonicalEquationDomains, equationDomains, inserted, hframeFields,
      liftContextPrefix, liftContextPrefixAt]
  have Houter : OnCtx (inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, List.reverse_append] using Hctx'
  exact ⟨{
    frame := B
    telescope := T
    fieldDomains := []
    hypothesisDomains := []
    targetResidual := T.minors[minorIdx]!
    lhsBody := lhsBody
    rhsBody := rhsBody
    typeBody := lhsType
    fieldDomains_length := by simp [hfieldsZero]
    hypothesisDomains_length := by simp [hhypothesesZero]
    minor_eq := by simp [VExpr.wrapForalls, minorIdx]
    fields_defeq := by
      simpa [hframeFields, liftContextPrefix, liftContextPrefixAt, inserted,
        List.reverse_append, List.append_assoc]
        using VEnv.IsDefEqCtx.refl Houter
    ctx := by rw [hdomainsEq]; exact Hctx'
    lhs_translation := by rw [hdomainsEq]; exact HlhsTranslation'
    rhs_translation := by rw [hdomainsEq]; exact HrhsTranslation
    type_translation := by rw [hdomainsEq]; exact HexpectedTranslation'
    lhs_typing := by rw [hdomainsEq]; exact HlhsTyping'
    rhs_typing := by rw [hdomainsEq]; exact HrhsAtLhs }⟩

/-- Every generated rule has an equation frame. -/
theorem
    RecursorCheck.RuleAlignment.equationFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    Nonempty A.EquationFrame := by
  by_cases hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0
  · exact A.zeroEquationFrame hzero
  · exact A.positiveEquationFrame (Nat.pos_of_ne_zero hzero)

/-! ### The generator's telescope against the equation frame -/

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The installed recursor type is the canonical generation's recursor type. -/
theorem RecursorCheck.entry_type_eq
    (H : RecursorCheck R outEnv) (owner : Nat)
    (howner : owner < H.entries.length)
    (hf : owner < H.generationSignature.families.size) :
    H.entries[owner].2.type = H.canonicalGeneration.recursorType ⟨owner, hf⟩ := by
  rw [H.targets owner howner]
  unfold RecursorConstruction.recursorTarget
  rw [dif_pos hf]
  rfl

theorem RecursorCheck.params_size_eq
    (H : RecursorCheck R outEnv) :
    stats.params.size = H.generationSignature.params.length :=
  H.cardinality.params.trans H.generator.models.nparams.symm

theorem RecursorCheck.motives_size_eq
    (H : RecursorCheck R outEnv) :
    (H.recInfos.map (·.motive)).size = H.generationSignature.families.size := by
  rw [Array.size_map, ← H.families_size]
  change _ = H.generator.signature.families.size
  rw [H.generator.families]

theorem RecursorCheck.minors_size_eq
    (H : RecursorCheck R outEnv) :
    (H.recInfos.flatMap (·.minors)).size = H.generationSignature.constructors.size :=
  H.cardinality.minors.trans H.generator.constructorCount.symm

/-- The cached parameter declarations are the canonical generation's parameters. -/
theorem RecursorCheck.parameterDecls_eq_generation
    (H : RecursorCheck R outEnv) :
    H.parameterSuffix.parameterDecls.toCtx.reverse = H.canonicalGeneration.params := by
  rw [H.toRecursorConstruction.parameterDomains]
  change _ = H.generator.signature.params.map
    (·.instL H.generator.generation.levels)
  rw [H.generator.params, H.generator.levels]

/-- Any telescope decomposition of an installed recursor type has the
canonical generation's parameter, motive and minor groups, syntactically. -/
theorem RecursorCheck.telescope_groups
    (H : RecursorCheck R outEnv)
    {env : VEnv} {Us : List Name} {source : Expr} {n owner : Nat}
    (howner : owner < H.entries.length)
    (T : RecursorTypeTelescope env Us source H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size n owner) :
    T.params = H.canonicalGeneration.params ∧
      T.motives = H.canonicalGeneration.motives ∧
      T.minors = H.canonicalGeneration.minors := by
  have hf : owner < H.generationSignature.families.size := by
    rw [← H.entries_length_eq]; exact howner
  have htype := H.entry_type_eq owner howner hf
  have htarget := htype.symm.trans T.target_eq
  unfold InductiveSignature.Instance.recursorType at htarget
  have hp : T.params.length = H.canonicalGeneration.params.length := by
    rw [T.params_length, H.params_size_eq]
    simp [InductiveSignature.Instance.params]
  have hm : T.motives.length = H.canonicalGeneration.motives.length := by
    rw [T.motives_length, H.motives_size_eq]
    simp [InductiveSignature.Instance.motives]
  have hmi : T.minors.length = H.canonicalGeneration.minors.length := by
    rw [T.minors_length, H.minors_size_eq, InductiveSignature.Instance.length_minors]
  have hP := VExpr.wrapForalls_prefix_domains_eq
    (left := T.params ++ T.motives ++ T.minors)
    (right := H.canonicalGeneration.params ++ H.canonicalGeneration.motives ++
      H.canonicalGeneration.minors)
    (n := (H.canonicalGeneration.params ++ H.canonicalGeneration.motives ++
      H.canonicalGeneration.minors).length) (by simp [hp, hm, hmi]) rfl
    (leftBody := VExpr.wrapForalls (T.indices ++ T.major) T.result)
    (by rw [← VExpr.wrapForalls_append]; simpa [List.append_assoc] using htarget.symm)
  obtain ⟨h12, h3⟩ := List.append_inj hP (by simp [hp, hm])
  obtain ⟨h1, h2⟩ := List.append_inj h12 hp
  exact ⟨h1, h2, h3⟩

/-- The rule's field count is the field count of its retained minor shape. -/
theorem RecursorCheck.RuleAlignment.allArgs_size_eq
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    A.rule.allArgs.size = (H.origins.minorShapes owner A.minorOrigin.owner_lt i
      A.minorOrigin.local_lt).fields.size := by
  rcases A.installedSelectedMinorShape with
    ⟨_T, _D, _O, S, _horigin, _hlocal, _hconstructors, _hconstructor,
      hsourceFields, _HS, _hypothesisOrigins,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      _traversal, _htraversal, _htraversalConstructor, _htraversalFields,
      _htraversalRecursiveFields, _htraversalStats, _hvalid, _hmotiveApp,
      _hrootContext, _hterminalContext, _hsourceContext, _hpositions,
      hproducerShape, _Hdomain, _HdomainType⟩
  rw [← hsourceFields, ← hproducerShape]
  exact congrArg (fun S => S.fields.size) A.minorOrigin.shape_eq

/-- The generated constructor of the rule's flattened position: it is owned by
the rule's family and has the rule's field count. -/
theorem RecursorCheck.RuleAlignment.generatedConstructor
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    ∃ hk : recursorMinorOffset indTypes owner + i <
        H.generationSignature.constructors.size,
      (H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).owner.val =
        owner ∧
      (H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).fields.length =
        A.rule.allArgs.size := by
  have hrec : owner < H.recInfos.size := A.minorOrigin.owner_lt
  have hlocal : i < H.origins.minorTypes[owner]!.size := A.minorOrigin.local_lt
  obtain ⟨index, hindex, hown, hfields, -, -⟩ :=
    H.generator.sourceOrigins owner hrec i hlocal
  have hk : recursorMinorOffset indTypes owner + i <
      H.generationSignature.constructors.size := hindex ▸ index.isLt
  refine ⟨hk, ?_, ?_⟩
  · have : H.generationSignature.constructors[recursorMinorOffset indTypes owner + i] =
        H.generator.signature.constructors[index] := by
      simp only [Fin.getElem_fin, hindex]; rfl
    rw [this]; exact hown
  · have : H.generationSignature.constructors[recursorMinorOffset indTypes owner + i] =
        H.generator.signature.constructors[index] := by
      simp only [Fin.getElem_fin, hindex]; rfl
    have hlen := congrArg List.length hfields
    simp only [InductiveSignature.fieldTypes, List.length_map, List.length_zipIdx] at hlen
    rw [this]
    exact hlen.trans ((H.sourceFields_length owner hrec i hlocal).trans
      A.allArgs_size_eq.symm)

/-- The selected minor's field domains are the generator's field domains,
weakened beneath the motives and the earlier minors. -/
theorem RecursorCheck.RuleAlignment.EquationFrame.fieldDomains_eq
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    (F : A.EquationFrame)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size)
    (hnf : (H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).fields.length =
        A.rule.allArgs.size) :
    F.fieldDomains = InductiveSignature.insertBinders
      ((H.generationSignature.fieldTypes
        H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).map
          (·.instL H.canonicalGeneration.levels))
      (H.generationSignature.families.size + (recursorMinorOffset indTypes owner + i)) := by
  obtain ⟨-, -, hminors⟩ := H.telescope_groups howner F.telescope
  have hminor := F.minor_eq
  have hkm : recursorMinorOffset indTypes owner + i < F.telescope.minors.length := by
    rw [hminors, InductiveSignature.Instance.length_minors]; exact hk
  rw [getElem!_pos F.telescope.minors _ hkm] at hminor
  have hget : F.telescope.minors[recursorMinorOffset indTypes owner + i] =
      H.canonicalGeneration.minor
        H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]
        (recursorMinorOffset indTypes owner + i) := by
    rw [List.getElem_of_eq hminors hkm]
    exact InductiveSignature.Instance.minors_getElem _ _ hk
  rw [hget] at hminor
  unfold InductiveSignature.Instance.minor at hminor
  rw [VExpr.wrapForalls_append F.fieldDomains] at hminor
  exact VExpr.wrapForalls_prefix_domains_eq (n := A.rule.allArgs.size)
    F.fieldDomains_length
    (by simp [InductiveSignature.insertBinders, InductiveSignature.fieldTypes, hnf])
    hminor.symm

/-- The equation frame's context is definitionally the generator's
equation telescope: parameters, motives and minors coincide syntactically, and
the frame's fields are aligned with the generator's weakened field types. -/
theorem RecursorCheck.RuleAlignment.EquationFrame.domains_defeq
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    (F : A.EquationFrame)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size)
    (hnf : (H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).fields.length =
        A.rule.allArgs.size) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (canonicalEquationDomains H.parameterSuffix.parameterDecls.toCtx.reverse
        F.telescope.motives F.telescope.minors F.frame.fieldDomains).reverse
      (H.canonicalGeneration.equationDomains
        ⟨recursorMinorOffset indTypes owner + i, hk⟩).reverse := by
  obtain ⟨-, hmotives, hminors⟩ := H.telescope_groups howner F.telescope
  have hfields := F.fieldDomains_eq hk hnf
  have Hfields := F.fields_defeq
  dsimp only at Hfields
  have hlater : (F.telescope.minors.drop (recursorMinorOffset indTypes owner + i + 1)).length + 1 =
      H.generationSignature.constructors.size - (recursorMinorOffset indTypes owner + i) := by
    rw [List.length_drop, hminors, InductiveSignature.Instance.length_minors]
    omega
  rw [hlater, hfields] at Hfields
  simp only [liftContextPrefix_reverse_reverse,
    InductiveSignature.insertBinders_insertBinders] at Hfields
  have hsum : H.generationSignature.families.size + (recursorMinorOffset indTypes owner + i) +
      (H.generationSignature.constructors.size - (recursorMinorOffset indTypes owner + i)) =
      H.generationSignature.families.size + H.generationSignature.constructors.size := by
    omega
  rw [hsum] at Hfields
  unfold canonicalEquationDomains InductiveSignature.Instance.equationDomains
  rw [← hmotives, ← hminors, ← H.parameterDecls_eq_generation]
  simp only [liftContextPrefix_reverse_reverse]
  simpa [List.reverse_append, List.append_assoc] using Hfields

/-- The generator's three equation bodies for the rule's flattened position
translate the rule's residual sources (LHS, RHS, and constructor motive
application) in the generator's own equation telescope.  This is the input
of `generatorEquationWF`; `RecursorCheck.equationBodyTranslations_of` derives
it from the right-hand-side translations. -/
structure RecursorCheck.RuleAlignment.EquationBodyTranslations
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size) :
    Prop where
  lhs : TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
    (A.rule.sourceLhsBody.abstractList A.rule.binders)
    (H.canonicalGeneration.equationLhsBody ⟨recursorMinorOffset indTypes owner + i, hk⟩)
  rhs : TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
    (A.rule.sourceRhsBody.abstractList A.rule.binders)
    (H.canonicalGeneration.equationRhsBody ⟨recursorMinorOffset indTypes owner + i, hk⟩)
  type : TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
    ((Expr.app
      (mkAppN H.recInfos[owner]!.motive
        (AddInductive.getIIndices stats A.rule.target).2)
      A.rule.sourceConstructorMajor).abstractList A.rule.binders)
    (H.canonicalGeneration.equationTypeBody ⟨recursorMinorOffset indTypes owner + i, hk⟩)

/-- One generated equation is well formed once its bodies translate the
rule's residual sources: the equation frame supplies the typing, which is
transported along the context alignment `domains_defeq`. -/
theorem RecursorCheck.RuleAlignment.generatorEquationWF
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size)
    (Htr : A.EquationBodyTranslations hk) :
    (H.canonicalGeneration.equation ⟨recursorMinorOffset indTypes owner + i, hk⟩).WF
      H.outVEnv := by
  rcases A.equationFrame with ⟨F⟩
  obtain ⟨_hk, -, hnf⟩ := A.generatedConstructor
  have D := F.domains_defeq hk hnf
  have huvars : H.canonicalGeneration.uvars =
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length :=
    H.generator.uvars
  rw [InductiveSignature.Instance.equation_eq, huvars]
  exact VDefEq.WF.transportTranslatedWrapped H.outVEnvWF F.ctx F.lhs_typing F.rhs_typing D
    F.lhs_translation F.rhs_translation F.type_translation Htr.lhs Htr.rhs Htr.type

/-- The remaining input of `equationsWF`: for every generated rule, some
alignment of it whose sources the generator's bodies translate. -/
def RecursorCheck.EquationBodyTranslations
    (H : RecursorCheck R outEnv) : Prop :=
  ∀ owner (howner : owner < H.entries.length)
    i (hctor : i < indTypes[owner]!.ctors.length)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size),
    ∃ A : H.RuleAlignment owner howner i hctor, A.EquationBodyTranslations hk

/-- Every equation of the canonical generation is well formed in the output
environment, given the generator body translations. -/
theorem RecursorCheck.equationsWF
    (H : RecursorCheck R outEnv)
    (Htr : H.EquationBodyTranslations) :
    ∀ df ∈ H.canonicalGeneration.equations, df.WF H.outVEnv := by
  intro df hdf
  simp only [InductiveSignature.Instance.equations, List.mem_map, List.mem_finRange,
    true_and] at hdf
  obtain ⟨k, rfl⟩ := hdf
  have hkOwned : k.val < decl.ownedConstructors.length := by
    have := k.isLt
    change k.val < H.generator.signature.constructors.size at this
    rwa [H.generator.constructorCount] at this
  obtain ⟨owner, hrec, localIndex, hlocal, hkEq⟩ :=
    H.toRecursorConstruction.flatMinorIndex k.val hkOwned
  have howner : owner < H.entries.length := by
    rw [H.generated.length]; exact hrec
  have hctor : localIndex < indTypes[owner]!.ctors.length := by
    rw [← H.toRecursorConstruction.minorTypes_size owner hrec]; exact hlocal
  have hk : recursorMinorOffset indTypes owner + localIndex <
      H.generationSignature.constructors.size := hkEq ▸ k.isLt
  obtain ⟨A, HA⟩ := Htr owner howner localIndex hctor hk
  have hkFin : k = ⟨recursorMinorOffset indTypes owner + localIndex, hk⟩ := Fin.ext hkEq
  rw [hkFin]
  exact A.generatorEquationWF hk HA

/-- The generator's equation telescope has exactly the rule's binder count. -/
theorem RecursorCheck.RuleAlignment.equationDomains_length
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size) :
    (H.canonicalGeneration.equationDomains
      ⟨recursorMinorOffset indTypes owner + i, hk⟩).length = A.rule.binders.length := by
  rcases A.equationFrame with ⟨F⟩
  obtain ⟨_hk, -, hnf⟩ := A.generatedConstructor
  have hlen := (F.domains_defeq hk hnf).length_eq
  simp only [List.length_reverse] at hlen
  rw [← hlen]
  have hcached := A.cachedEquationDomains_length F.telescope
    (liftContextPrefix (F.telescope.motives ++ F.telescope.minors).length
      F.frame.fieldDomains.reverse).reverse
    (by simp [F.frame.fieldDomains_length])
  simpa [canonicalEquationDomains, H.parameterDecls, List.append_assoc] using hcached

/-- Adapter from a closed translation of the installed rule RHS to the
generator's equation RHS (the form `TrExprS [] rule.rhs (g.equation k).rhs`)
into the residual form required by `EquationBodyTranslations.rhs`. -/
theorem RecursorCheck.RuleAlignment.rhsResidualOfClosed
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size)
    (hclosed : Closed A.rule.sourceRhsBody)
    (Htr : TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      ((H.generated.entry owner howner).info.rules[i]'A.sourceRule_lt).rhs
      (H.canonicalGeneration.equation ⟨recursorMinorOffset indTypes owner + i, hk⟩).rhs) :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (H.canonicalGeneration.equationDomains ⟨recursorMinorOffset indTypes owner + i, hk⟩) [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders)
      (H.canonicalGeneration.equationRhsBody ⟨recursorMinorOffset indTypes owner + i, hk⟩) := by
  have H' := TrExprS.lambdaTelescope_exact_residual A.rule.rhsLambdaTelescope
    (A.equationDomains_length hk) Htr
  have heq : A.rule.sourceRhsBody.abstractN A.rule.binders =
      A.rule.sourceRhsBody.abstractList A.rule.binders :=
    Lean.Expr.abstractN_eq_abstractList_of_closed A.rule.binders_nodup hclosed
  rwa [heq] at H'

end

end VerifyInductive
end Lean4Lean
