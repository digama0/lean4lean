import Lean4Lean.Verify.Inductive.Rules.RecursiveBody

/-! The recursive results of a rule (`RecursorInstallation.RuleAlignment.RecursiveResult`), each closed
and typed in the fixed equation context, with its translation reconstructed from its
eta-expanded field template, and compared with the corresponding induction hypothesis of the
selected minor premise.

The selected-hypothesis comparison uses named source/provenance, replay, typing,
and residual-translation obligations. `HypothesisDomainFrame` transports that
comparison into the installed and canonical whole contexts. Internal consumers
use those records directly. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Fixed-frame package for one complete recursive result.  The generated
recursor telescope and rule-wide field frame are parameters, so every
array position is closed and typed in the same literal `equationDomains`;
only its higher-order local telescope varies with the recursive field. -/
theorem
    RecursorInstallation.RuleAlignment.recursiveResultTypingFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.FieldFrame)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    ∃ F : A.RecursiveCallFrame j hj,
      ∃ (localDomains : List VExpr)
          (resultBody resultType templateTarget : VExpr),
        equationDomains.length = A.rule.binders.length ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        OnCtx (abstractForallContext equationDomains []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext equationDomains [])
          ((F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs (.sort .zero)).abstractList
              A.rule.binders)
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        Expr.LambdaTelescope
          (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
          localDomains.length
          (F.semantic.generated.body.abstractList
        A.rule.binders F.semantic.generated.localArgs.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.body.abstractList
        A.rule.binders F.semantic.generated.localArgs.size)
          resultBody ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMajor A.rule.binders)
          templateTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
          resultType ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (equationDomains ++ localDomains) []).toCtx resultType ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
          (VExpr.wrapLams localDomains resultBody)
          (VExpr.wrapForalls localDomains resultType) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  rcases A.recursiveCallFrame j hj with ⟨F⟩
  rcases F.recursiveCallBodyWF T (B := B) with
    ⟨actualDomains, localDomains, prefixTarget, indexTargets,
      majorTarget, ownerTarget, hlocal, hdomains, hequation, _Hctx,
      HlocalTemplate, Hbody, HtemplateResidual, HmotiveApplication,
      HbodyType, Hclosed, _HbodyWF⟩
  have hactual : actualDomains = equationDomains := by
    exact hdomains
  subst actualDomains
  let args := indexTargets ++ [majorTarget]
  let resultBody := VExpr.mkApps prefixTarget args
  let resultType := VExpr.mkApps ownerTarget args
  have Htelescope :=
    F.semantic.generated.outerAbstractedLambdaTelescope A.rule.binders
  have Htelescope' : Expr.LambdaTelescope
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      localDomains.length
      (F.semantic.generated.body.abstractList
        A.rule.binders F.semantic.generated.localArgs.size) := by
    simpa [hlocal] using Htelescope
  have HequationCtx : OnCtx
      (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    have Hbase := _Hctx.drop localDomains.length
    simpa [equationDomains, Us, abstractForallContext_toCtx,
      List.reverse_append, List.drop_append, List.length_reverse,
      List.append_assoc] using Hbase
  have HresultType : H.outVEnv.IsType Us.length
      (abstractForallContext (equationDomains ++ localDomains) []).toCtx
      resultType := by
    simpa [equationDomains, Us, resultType, args,
      abstractForallContext_toCtx, List.reverse_append,
      List.append_assoc] using HbodyType.isType H.outVEnvWF _Hctx
  exact ⟨F, localDomains, resultBody, resultType, majorTarget,
    hequation, hlocal, HequationCtx, HlocalTemplate, Htelescope',
    by simpa [resultBody, args] using Hbody,
    HtemplateResidual,
    by simpa [resultType, args] using HmotiveApplication,
    HresultType,
    by simpa [resultBody, resultType, args] using Hclosed⟩

/-- One recursive result in the fixed rule-wide equation context.  The
higher-order local telescope remains entry-specific, while its closed lambda
and forall type both live in the single context shared by the whole RHS. -/
structure
    RecursorInstallation.RuleAlignment.RecursiveResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.FieldFrame)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) where
  frame : A.RecursiveCallFrame j hj
  localDomains : List VExpr
  resultBody : VExpr
  resultType : VExpr
  templateTarget : VExpr
  equation_length :
    (H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse).length = A.rule.binders.length
  local_length : localDomains.length = frame.semantic.generated.localArgs.size
  equation_context :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    OnCtx (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length)
  local_forall_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((frame.semantic.generated.current.lctx.mkForall
        frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      (VExpr.wrapForalls localDomains (.sort .zero))
  source_telescope : Expr.LambdaTelescope
    (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
    localDomains.length
    (frame.semantic.generated.body.abstractList
      A.rule.binders frame.semantic.generated.localArgs.size)
  template_telescope : Expr.LambdaTelescope
    ((frame.semantic.generated.current.lctx.mkLambda
        frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          frame.semantic.generated.localArgs)).abstractList A.rule.binders)
    localDomains.length
    (frame.semantic.generated.outerAbstractedMajor A.rule.binders)
  source_template_prefix : Expr.SameLambdaPrefix localDomains.length
    (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
    ((frame.semantic.generated.current.lctx.mkLambda
        frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          frame.semantic.generated.localArgs)).abstractList A.rule.binders)
  residual_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (frame.semantic.generated.body.abstractList
      A.rule.binders frame.semantic.generated.localArgs.size)
      resultBody
  template_residual_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (frame.semantic.generated.outerAbstractedMajor A.rule.binders)
      templateTarget
  result_type_translation :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      resultType
  result_type_isType :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    H.outVEnv.IsType Us.length
      (abstractForallContext (equationDomains ++ localDomains) []).toCtx
      resultType
  closed_typing :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.wrapLams localDomains resultBody)
      (VExpr.wrapForalls localDomains resultType)

theorem
    RecursorInstallation.RuleAlignment.recursiveResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.FieldFrame)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    Nonempty (A.RecursiveResult T B j hj) := by
  rcases A.recursiveResultTypingFor T B j hj with
    ⟨F, localDomains, resultBody, resultType, templateTarget, hequation,
      hlocal, HequationCtx, HlocalForall, Htelescope, Htranslation,
      HtemplateResidual, HtypeTranslation, HresultType, Htyping⟩
  have HtemplateTelescope : Expr.LambdaTelescope
      ((F.semantic.generated.current.lctx.mkLambda
          F.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs)).abstractList A.rule.binders)
      localDomains.length
      (F.semantic.generated.outerAbstractedMajor A.rule.binders) := by
    simpa [hlocal, RecursiveCall.outerAbstractedMajor] using
      ((F.semantic.generated.appliedFieldLambdaTelescope
        F.semantic.fieldClosed).abstractList A.rule.binders)
  have HsamePrefix : Expr.SameLambdaPrefix localDomains.length
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      ((F.semantic.generated.current.lctx.mkLambda
          F.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            F.semantic.generated.localArgs)).abstractList A.rule.binders) := by
    simpa [hlocal] using
      F.semantic.sameOuterAppliedFieldLambdaPrefix A.rule.binders
  exact ⟨{
    frame := F
    localDomains := localDomains
    resultBody := resultBody
    resultType := resultType
    templateTarget := templateTarget
    equation_length := hequation
    local_length := hlocal
    equation_context := HequationCtx
    local_forall_translation := HlocalForall
    source_telescope := Htelescope
    template_telescope := HtemplateTelescope
    source_template_prefix := HsamePrefix
    residual_translation := Htranslation
    template_residual_translation := HtemplateResidual
    result_type_translation := HtypeTranslation
    result_type_isType := HresultType
    closed_typing := Htyping }⟩

/-- Replace the neutral codomain in the retained local-forall template by
the independently checked selected-motive application.  The source is the
exact complete higher-order domain produced by the recursive-call replay,
closed over the executable's full rule binder list. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveResult.fullForallTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.RecursiveResult T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let motiveApp := Expr.app
      (mkAppN
        (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
        E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j]
        E.frame.semantic.generated.localArgs)
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      (VExpr.wrapForalls E.localDomains E.resultType) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let motiveApp := Expr.app
    (mkAppN
      (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let selection :=
    E.frame.semantic.generated.arguments_bound.toFVarArrayIn.toCDeclArray
      E.frame.semantic.generated.current_wf
  have Hsame := (selection.sameForallPrefix
    E.frame.semantic.generated.arguments_bound.nodup
    (.sort (.zero : Level)) motiveApp).abstractList A.rule.binders
  rcases E.frame.motiveApplication with ⟨HproducerMotive⟩
  have hmotiveAppClosed : Closed motiveApp := by
    have hclosed := HproducerMotive.translation.closed
    rw [E.frame.semantic.current_context.mlctx.noBV] at hclosed
    simpa [motiveApp] using hclosed
  have Htemplate₀ := (selection.forallTelescopeList
    (.sort (.zero : Level)) E.frame.semantic.generated.arguments_bound.nodup
    trivial).abstractList A.rule.binders
  have Hreplacement₀ :=
    (selection.forallTelescopeList motiveApp
      E.frame.semantic.generated.arguments_bound.nodup
      hmotiveAppClosed).abstractList A.rule.binders
  have hselectionFVars : selection.fvars =
      E.frame.semantic.generated.arguments_bound.fvars := rfl
  rw [hselectionFVars] at Htemplate₀ Hreplacement₀
  have hsortLocal : (Expr.sort (.zero : Level)).abstractList
      E.frame.semantic.generated.arguments_bound.fvars = .sort .zero := by
    induction E.frame.semantic.generated.arguments_bound.fvars <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortLocal] at Htemplate₀
  simp only [Nat.zero_add] at Htemplate₀
  have hsortOuter : (Expr.sort (.zero : Level)).abstractList
      A.rule.binders E.frame.semantic.generated.localArgs.size = .sort .zero := by
    induction A.rule.binders <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortOuter] at Htemplate₀
  have Htemplate : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size (.sort .zero) := by
    exact Htemplate₀
  have hresidual := E.frame.semantic.generated.outerAbstractedMotiveApp_eq
    A.rule.binders E.frame.semantic.fieldClosed
  have HreplacementRaw : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size
      ((motiveApp.abstractList
        E.frame.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders E.frame.semantic.generated.localArgs.size) := by
    simpa using Hreplacement₀
  have Hreplacement : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders) := by
    rw [← hresidual]
    exact HreplacementRaw
  have HresultTranslation : TrExprS H.outVEnv Us
      (abstractForallContext E.localDomains
        (abstractForallContext equationDomains []))
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa [equationDomains, Us, abstractForallContext_append,
      List.append_assoc] using E.result_type_translation
  have HresultType : H.outVEnv.IsType Us.length
      (abstractForallContext E.localDomains
        (abstractForallContext equationDomains [])).toCtx E.resultType := by
    simpa [equationDomains, Us, abstractForallContext_append,
      List.append_assoc] using E.result_type_isType
  exact Hsame.replaceTranslatedResidual Htemplate Hreplacement
    H.outVEnvWF E.equation_context E.local_length
    E.local_forall_translation HresultTranslation HresultType

/-- Insert an already applied prefix of recursive hypotheses beneath the
fixed equation context while retaining the complete canonical higher-order
domain.  Both its dependent local domains and its real residual are lifted
at their exact respective cutoffs. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveResult.fullForallTranslationAfter
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.RecursiveResult T B j hj)
    (previous : List VExpr) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let motiveApp := Expr.app
      (mkAppN
        (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
        E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j]
        E.frame.semantic.generated.localArgs)
    let liftedLocals :=
      (liftContextPrefix previous.length E.localDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ previous) [])
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs motiveApp).abstractList
          A.rule.binders).liftLooseBVars' 0 previous.length)
      (VExpr.wrapForalls liftedLocals
        (E.resultType.liftN previous.length E.localDomains.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let motiveApp := Expr.app
    (mkAppN
      (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let liftedLocals :=
    (liftContextPrefix previous.length E.localDomains.reverse).reverse
  have Hbase := E.fullForallTranslation
  have Hinserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := []) H.outVEnvWF.orderedStrong
      (by simpa [equationDomains, motiveApp] using Hbase) previous
  simpa [equationDomains, liftedLocals, VExpr.liftN_wrapForalls,
    VExpr.liftN, liftContextPrefix, liftContextPrefixAt,
    List.append_assoc] using Hinserted

/-- The checked local forall telescope supplies the strict domain
translations for the eta-expanded recursive-field lambda over the same local
selection. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveResult.templateTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.RecursiveResult T B j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((E.frame.semantic.generated.current.lctx.mkLambda
          E.frame.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            E.frame.semantic.generated.localArgs)).abstractList
        A.rule.binders)
      (VExpr.wrapLams E.localDomains E.templateTarget) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let selection :=
    E.frame.semantic.generated.arguments_bound.toFVarArrayIn.toCDeclArray
      E.frame.semantic.generated.current_wf
  have Hsame := (selection.sameForallLambdaPrefix
    E.frame.semantic.generated.arguments_bound.nodup
    (.sort (.zero : Level))
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)).abstractList A.rule.binders
  have Hforall₀ := (selection.forallTelescopeList
    (.sort (.zero : Level)) E.frame.semantic.generated.arguments_bound.nodup
    trivial).abstractList A.rule.binders
  have hselectionFVars : selection.fvars =
      E.frame.semantic.generated.arguments_bound.fvars := rfl
  rw [hselectionFVars] at Hforall₀
  have hsortLocal : (Expr.sort (.zero : Level)).abstractList
      E.frame.semantic.generated.arguments_bound.fvars = .sort .zero := by
    induction E.frame.semantic.generated.arguments_bound.fvars <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortLocal] at Hforall₀
  simp only [Nat.zero_add] at Hforall₀
  have hsortOuter : (Expr.sort (.zero : Level)).abstractList
      A.rule.binders E.frame.semantic.generated.localArgs.size = .sort .zero := by
    induction A.rule.binders <;>
      simp_all [Expr.abstractList, Expr.abstract1]
  rw [hsortOuter] at Hforall₀
  have HforallTelescope : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      E.frame.semantic.generated.localArgs.size (.sort .zero) := Hforall₀
  have Hsame' : Expr.SameForallLambdaPrefix E.localDomains.length
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      ((E.frame.semantic.generated.current.lctx.mkLambda
        E.frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs)).abstractList
            A.rule.binders) := by
    simpa [E.local_length] using Hsame
  have HforallTelescope' : Expr.ForallTelescope
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      E.localDomains.length (.sort .zero) := by
    simpa [E.local_length] using HforallTelescope
  exact Hsame'.translateLambda HforallTelescope' E.template_telescope
    rfl E.local_forall_translation (by
      simpa [equationDomains, Us, abstractForallContext_append,
        List.append_assoc] using E.template_residual_translation)

/-- Reconstruct the strict translation of the complete generated recursive
result from any translation of its eta-expanded field template in the fixed
equation context.  The template contributes only the shared lambda-domain
derivations; the actual recursive-call residual is the independently checked
one retained by `RecursiveResult`. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveResult.fullTranslationOfTemplate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (E : A.RecursiveResult T B j hj)
    (templateTarget : VExpr)
    (Htemplate :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      TrExprS H.outVEnv Us
        (abstractForallContext equationDomains [])
        ((E.frame.semantic.generated.current.lctx.mkLambda
            E.frame.semantic.generated.localArgs
            (mkAppN A.rule.recursiveArgs[j]
              E.frame.semantic.generated.localArgs)).abstractList
          A.rule.binders)
        (VExpr.wrapLams E.localDomains templateTarget)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      (VExpr.wrapLams E.localDomains E.resultBody) := by
  dsimp only at Htemplate ⊢
  exact E.source_template_prefix.symm.replaceTranslatedResidual
    E.template_telescope E.source_telescope rfl Htemplate
    (by simpa [abstractForallContext_append] using E.residual_translation)

/-- Equality of the closed local telescopes fixes their forall prefixes even
when the residual bodies differ. Each side abstracts its own field context. -/
private theorem sameForallPrefix_of_localTelescope
    {leftCtx rightCtx : LocalContext} {leftArgs rightArgs : Array Expr}
    (leftSelection : CDeclArray leftCtx leftArgs)
    (rightSelection : CDeclArray rightCtx rightArgs)
    (leftNodup : leftSelection.fvars.Nodup)
    (rightNodup : rightSelection.fvars.Nodup)
    (leftFields rightFields : List FVarId)
    (arity : leftArgs.size = rightArgs.size)
    (telescope :
      (leftCtx.mkForall leftArgs (.sort .zero)).abstractList leftFields =
      (rightCtx.mkForall rightArgs (.sort .zero)).abstractList rightFields)
    (left right : Expr) :
    Expr.SameForallPrefix leftArgs.size
      ((leftCtx.mkForall leftArgs left).abstractList leftFields)
      ((rightCtx.mkForall rightArgs right).abstractList rightFields) := by
  have Hleft := (leftSelection.sameForallPrefix leftNodup left
    (.sort .zero)).abstractList leftFields
  have Hright := ((rightSelection.sameForallPrefix rightNodup right
    (.sort .zero)).symm).abstractList rightFields
  rw [telescope] at Hleft
  exact Hleft.trans (by simpa [arity] using Hright)

/-- In the source context, parameters precede motives and the earlier minors.
Opening a motive at offset `k` therefore uses its position in that literal order. -/
private theorem abstractMotiveInSourceContext
    (params motives priorMinors : List FVarId)
    (nodup : (params ++ motives ++ priorMinors).Nodup)
    (owner : Nat) (howner : owner < motives.length) (k : Nat) :
    (Expr.fvar motives[owner]).abstractList (params ++ motives ++ priorMinors) k =
      .bvar (k + ((params ++ motives ++ priorMinors).length - 1 -
        (params.length + owner))) := by
  have hwithin : params.length + owner < (params ++ motives).length := by
    simp only [List.length_append]
    omega
  have hposition : params.length + owner <
      (params ++ motives ++ priorMinors).length := by
    simp only [List.length_append]
    omega
  have H := Expr.abstractList_fvar_getElem nodup (params.length + owner)
    hposition (k := k)
  rw [List.getElem_append_left hwithin] at H
  simpa [howner] using H

section HypothesisComparison

variable

    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}

variable
    (A : H.RuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.FieldFrame)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (E : A.RecursiveResult T B j hj)

/-- Insert the earlier hypotheses between the fixed equation context and the
recursive call's local telescope. Translation and typing use the same lifted
context, so callers need not reconstruct this weakening argument separately. -/
theorem RecursorInstallation.RuleAlignment.recursiveResultResidualAfter
    (previous : List VExpr) :
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++ T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
    let locals := (liftContextPrefix previous.length E.localDomains.reverse).reverse
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (equationDomains ++ previous ++ locals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size previous.length)
      (E.resultType.liftN previous.length E.localDomains.length) ∧
    H.outVEnv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext (equationDomains ++ previous ++ locals) []).toCtx
      (E.resultType.liftN previous.length E.localDomains.length) := by
  dsimp only
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ T.motives ++ T.minors ++
      (liftContextPrefix (T.motives ++ T.minors).length
        B.fieldDomains.reverse).reverse
  let liftedCanonicalLocals :=
    (liftContextPrefix previous.length E.localDomains.reverse).reverse
  have HcanonicalResidual₀ : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa [equationDomains] using E.result_type_translation
  have HcanonicalResidualInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := E.localDomains)
      H.outVEnvWF.orderedStrong HcanonicalResidual₀ previous
  have HcanonicalResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (equationDomains ++ previous ++ liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size previous.length)
      (E.resultType.liftN previous.length E.localDomains.length) := by
    simpa [liftedCanonicalLocals, E.local_length, List.append_assoc] using
      HcanonicalResidualInserted
  have Wcanonical : Ctx.LiftN previous.length E.localDomains.length
      (abstractForallContext
        (equationDomains ++ E.localDomains) []).toCtx
      (abstractForallContext
        (equationDomains ++ previous ++ liftedCanonicalLocals) []).toCtx := by
    have W := Ctx.LiftN.insertAfterPrefix E.localDomains.reverse
      previous.reverse equationDomains.reverse
    simpa [liftedCanonicalLocals, List.reverse_append,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc] using W
  have HcanonicalResidualType : H.outVEnv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (equationDomains ++ previous ++ liftedCanonicalLocals) []).toCtx
      (E.resultType.liftN previous.length E.localDomains.length) := by
    exact E.result_type_isType.weakN H.outVEnvWF.ordered Wcanonical
  exact ⟨HcanonicalResidual, HcanonicalResidualType⟩

/-- Source declarations and traversal provenance for one selected minor hypothesis.
The installed minor opens fields first, then the earlier hypotheses; the cached
parameter, motive, and earlier-minor binders form its outer context. -/
structure RecursorInstallation.RuleAlignment.HypothesisSource where
  shape : MinorPremiseType
  origins : MinorInductionHypothesisTypes shape.sourceFullContext
    shape.recursiveFields shape.hypotheses
  traversal : ConstructorFieldTraversal
  fieldDomains : List VExpr
  hypothesisDomains : List VExpr
  targetResidual : VExpr
  declaration : FVarDeclAt shape.sourceFullContext shape.hypotheses j
  originRoot : AddInductive.Context
  sourceType : Expr
  origin : InductionHypothesisType origins.stats origins.recInfos
    originRoot shape.recursiveFields[j]! sourceType
  origins_eq :
    shape.hypothesis_type_origins = some origins
  stats_eq :
    origins.stats = stats
  motives_eq :
    origins.recInfos.map (·.motive) =
    H.recInfos.map (·.motive)
  owner_lt :
    origin.ownerIdx < H.recInfos.size
  motive_snapshot :
    origins.recInfos[origin.ownerIdx]!.motive =
    H.recInfos[origin.ownerIdx]!.motive
  motive_position :
    (let sourceBinders := H.params.fvars ++
      H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take (recursorMinorOffset indTypes owner + i)
    let position := A.rule.allArgs.size + j
    let motivePosition := H.params.fvars.length + origin.ownerIdx
    ∃ motiveFVar,
      H.recInfos[origin.ownerIdx]!.motive = .fvar motiveFVar ∧
      (Expr.fvar motiveFVar).abstractList sourceBinders position =
        .bvar (position +
          (sourceBinders.length - 1 - motivePosition)))
  traversal_eq :
    shape.traversal = some traversal
  fields_eq :
    traversal.fields = shape.fields
  recursive_fields_eq :
    traversal.recursiveFields = shape.recursiveFields
  traversal_stats_eq :
    traversal.stats = stats
  parameter_tail_eq :
    traversal.parameterTail = A.typing.parameterTail
  recursive_positions_eq :
    traversal.recursivePositions = A.typing.recursivePositions
  source_selected :
    shape.recursiveFields[j]! =
    shape.fields[A.typing.recursivePositions[j]!]!
  rule_selected :
    A.rule.recursiveArgs[j]! =
    A.rule.allArgs[A.typing.recursivePositions[j]!]!
  local_index_eq :
    shape.localIndex = i
  source_fields_length :
    shape.fields.size = A.rule.allArgs.size
  source_hypotheses_length :
    shape.hypotheses.size = A.rule.recursiveArgs.size
  context_le :
    BindingContextLE shape.sourceFullContext H.localContext
  semantic :
    Nonempty (TypedMinorTraversalAt H.recursorWF shape
    H.parameterSuffix.parameterDecls)
  fields_length :
    fieldDomains.length = A.rule.allArgs.size
  hypotheses_length :
    hypothesisDomains.length = A.rule.recursiveArgs.size
  selected_minor_eq :
    T.minors[(recursorMinorOffset indTypes owner + i)]! = VExpr.wrapForalls
    (fieldDomains ++ hypothesisDomains) targetResidual
  declaration_type_eq :
    declaration.type = sourceType

/-- The outer binders are ordered parameters, motives, then preceding minors. -/
abbrev RecursorInstallation.RuleAlignment.HypothesisSource.binders
    (_source : RecursorInstallation.RuleAlignment.HypothesisSource A j T) : List FVarId :=
  H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take (recursorMinorOffset indTypes owner + i)

abbrev RecursorInstallation.RuleAlignment.HypothesisSource.position
    (_source : RecursorInstallation.RuleAlignment.HypothesisSource A j T) : Nat :=
  A.rule.allArgs.size + j

abbrev RecursorInstallation.RuleAlignment.HypothesisSource.declarationDomain
    (source : RecursorInstallation.RuleAlignment.HypothesisSource A j T) : Expr :=
  ((source.declaration.type.abstractList
      (source.shape.hypotheses_bound.fvars.take j)).abstractList
    source.shape.fields_bound.fvars j).abstractList source.binders source.position

/-- Exact syntax shared by the first-pass hypothesis and second-pass call.
These fields compare their alpha-closed local telescopes before typed context
transport; they do not replace the typing obligations below. -/
structure RecursorInstallation.RuleAlignment.HypothesisReplay
    (source : RecursorInstallation.RuleAlignment.HypothesisSource A j T) : Prop where
  source_major_eq :
    source.origin.outerAbstractedField source.shape.fields_bound.fvars =
    mkAppN
      (.bvar (source.origin.args.size +
        (source.shape.fields_bound.fvars.length - 1 -
          A.typing.recursivePositions[j]!)))
      (source.origin.localIndices.map Expr.bvar).toArray
  generated_major_eq :
    E.frame.semantic.generated.outerAbstractedMajor A.rule.binders =
    mkAppN
      (.bvar (E.frame.semantic.generated.localArgs.size +
        (A.rule.allArgs.size - 1 -
          A.typing.recursivePositions[j]!)))
      (E.frame.semantic.generated.localIndices.map Expr.bvar).toArray
  replay_eq :
    source.origin.replayTrace source.shape.fields_bound.fvars =
    E.frame.semantic.generated.replayTrace
      A.rule.all_args_bound.fvars
  local_telescope_eq :
    (source.origin.current.lctx.mkForall source.origin.args (.sort .zero)).abstractList
      source.shape.fields_bound.fvars =
    (E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
      A.rule.all_args_bound.fvars
  lambda_prefix :
    Expr.SameLambdaPrefix E.localDomains.length
    (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
    ((E.frame.semantic.generated.current.lctx.mkLambda
        E.frame.semantic.generated.localArgs
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs)).abstractList
      A.rule.binders)
  forall_prefix :
    (∀ left right,
    Expr.SameForallPrefix source.origin.args.size
      ((source.origin.current.lctx.mkForall source.origin.args left).abstractList
        source.shape.fields_bound.fvars)
      ((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs right).abstractList
        A.rule.all_args_bound.fvars))
  motive_replay_eq :
    ((source.origins.recInfos[source.origin.ownerIdx]!.motive.abstractList
        source.origin.arguments_bound.fvars).abstractList
      source.shape.fields_bound.fvars source.origin.args.size) =
    ((((H.recInfos.map
          (fun info : AddInductive.RecInfo => info.motive))[
          E.frame.semantic.generated.ownerIdx]!).abstractList
        E.frame.semantic.generated.arguments_bound.fvars).abstractList
      A.rule.all_args_bound.fvars
        E.frame.semantic.generated.localArgs.size)
  indices_replay_eq :
    (((source.origin.exposedType.getAppArgs[
        source.origins.stats.params.size:] : Array Expr).map
      fun index =>
        (index.abstractList source.origin.arguments_bound.fvars).abstractList
          source.shape.fields_bound.fvars source.origin.args.size) =
    ((E.frame.semantic.generated.exposedType.getAppArgs[
          stats.params.size:] : Array Expr).map
      fun index =>
        (index.abstractList
          E.frame.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            E.frame.semantic.generated.localArgs.size))
  owner_eq :
    source.origin.ownerIdx = E.frame.semantic.generated.ownerIdx
  local_length_eq :
    source.origin.args.size = E.frame.semantic.generated.localArgs.size
  major_eq :
    source.origin.outerAbstractedField source.shape.fields_bound.fvars =
    E.frame.semantic.generated.outerAbstractedMajor A.rule.binders
  motive_app_eq :
    source.origin.outerAbstractedMotiveApp source.shape.fields_bound.fvars =
    E.frame.semantic.generated.outerAbstractedMotiveApp
      A.rule.all_args_bound.fvars
  motive_closed :
    Closed (source.origin.outerAbstractedMotiveApp source.shape.fields_bound.fvars)
    (source.origin.args.size + source.shape.fields.size)
  generated_field_closed :
    (let generatedMotiveApp := Expr.app
      (mkAppN
        H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive
        E.frame.semantic.generated.exposedType.getAppArgs[
          stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j]
        E.frame.semantic.generated.localArgs);
    Closed
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs generatedMotiveApp
        ).abstractList A.rule.all_args_bound.fvars)
      A.rule.allArgs.size)

/-- Translation and closed typing in the selected minor and fixed equation contexts. -/
structure RecursorInstallation.RuleAlignment.HypothesisTyping
    (source : RecursorInstallation.RuleAlignment.HypothesisSource A j T) : Prop where
  declaration_translation :
    (let sourceBinders := H.params.fvars ++
      H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take (recursorMinorOffset indTypes owner + i)
    let position := A.rule.allArgs.size + j
    let declarationDomain :=
      ((source.declaration.type.abstractList
          (source.shape.hypotheses_bound.fvars.take j)).abstractList
        source.shape.fields_bound.fvars j).abstractList sourceBinders position
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        ((source.fieldDomains ++ source.hypothesisDomains).take position)
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take (recursorMinorOffset indTypes owner + i)) []))
      declarationDomain source.hypothesisDomains[j]!)
  closed_typing :
    H.outVEnv.HasType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext
      (H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse) []).toCtx
    (VExpr.wrapLams E.localDomains E.resultBody)
    (VExpr.wrapForalls E.localDomains E.resultType)

/-- Residual comparison after opening the higher-order local telescope.
The hypothesis context contains earlier hypotheses; the canonical context is
fixed at all fields. The transport equations retain that distinction. -/
structure RecursorInstallation.RuleAlignment.HypothesisResidual
    (source : RecursorInstallation.RuleAlignment.HypothesisSource A j T) where
  hypothesisLocalDomains : List VExpr
  sourceResidual : Expr
  hypothesisResidual : VExpr
  local_length :
    hypothesisLocalDomains.length = source.origin.args.size
  source_telescope :
    Expr.ForallTelescope source.declarationDomain source.origin.args.size
    sourceResidual
  source_eq :
    sourceResidual =
    (((((Expr.app
        (mkAppN source.origins.recInfos[source.origin.ownerIdx]!.motive
          source.origin.exposedType.getAppArgs[
            source.origins.stats.params.size:])
        (mkAppN source.shape.recursiveFields[j]! source.origin.args)).abstractList
          source.origin.arguments_bound.fvars).abstractList
        (source.shape.hypotheses_bound.fvars.take j) source.origin.args.size).abstractList
      source.shape.fields_bound.fvars (source.origin.args.size + j)).abstractList
    source.binders (source.origin.args.size + source.position))
  structured_eq :
    sourceResidual =
    ((((Expr.app
        (mkAppN
          (source.origins.recInfos[source.origin.ownerIdx]!.motive.abstractList
            source.origin.arguments_bound.fvars)
          (((source.origin.exposedType.getAppArgs[
              source.origins.stats.params.size:] : Array Expr)
            ).map fun index =>
            index.abstractList source.origin.arguments_bound.fvars))
        source.origin.abstractedField).abstractList
      (source.shape.hypotheses_bound.fvars.take j) source.origin.args.size).abstractList
    source.shape.fields_bound.fvars (source.origin.args.size + j)).abstractList
    source.binders (source.origin.args.size + source.position))
  normalized_eq :
    sourceResidual =
    ((source.origin.outerAbstractedMotiveApp
        source.shape.fields_bound.fvars).liftLooseBVars'
      source.origin.args.size j).abstractList source.binders
        (source.origin.args.size + source.position)
  outer_transport_eq :
    sourceResidual =
    ((source.origin.outerAbstractedMotiveApp
        source.shape.fields_bound.fvars).abstractList source.binders
      (source.origin.args.size + source.shape.fields.size)).liftLooseBVars'
        source.origin.args.size j
  generated_prefix_eq :
    sourceResidual =
    ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars).abstractList
      (A.rule.params_bound.fvars ++
        A.rule.motives_bound.fvars ++
          A.rule.minors_bound.fvars.take (recursorMinorOffset indTypes owner + i))
      (E.frame.semantic.generated.localArgs.size +
        A.rule.allArgs.size)).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j
  full_transport_eq :
    sourceResidual.liftLooseBVars'
      (E.frame.semantic.generated.localArgs.size +
        A.rule.allArgs.size + j)
      (A.rule.minors_bound.fvars.drop (recursorMinorOffset indTypes owner + i)).length =
    (E.frame.semantic.generated.outerAbstractedMotiveApp
      A.rule.binders).liftLooseBVars'
        E.frame.semantic.generated.localArgs.size j
  hypothesis_translation :
    (let hypothesisInner :=
      ((source.fieldDomains ++ source.hypothesisDomains).take source.position) ++
        hypothesisLocalDomains
    let remainingMinorDomains := T.minors.drop (recursorMinorOffset indTypes owner + i)
    let liftedHypothesisInner :=
      (liftContextPrefix remainingMinorDomains.length
        hypothesisInner.reverse).reverse
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++
          liftedHypothesisInner) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (hypothesisResidual.liftN remainingMinorDomains.length
        hypothesisInner.length))
  canonical_translation :
    (let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let previousHypothesisDomains := source.hypothesisDomains.take j
    let liftedCanonicalLocals :=
      (liftContextPrefix previousHypothesisDomains.length
        E.localDomains.reverse).reverse
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (equationDomains ++ previousHypothesisDomains ++
          liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (E.resultType.liftN previousHypothesisDomains.length
        E.localDomains.length))
  hypothesis_domain_eq :
    source.hypothesisDomains[j]! = VExpr.wrapForalls
    hypothesisLocalDomains hypothesisResidual
  residual_translation :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext hypothesisLocalDomains
      (abstractForallContext
        ((source.fieldDomains ++ source.hypothesisDomains).take source.position)
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take (recursorMinorOffset indTypes owner + i)) [])))
    sourceResidual hypothesisResidual
  residual_type :
    H.outVEnv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext hypothesisLocalDomains
      (abstractForallContext
        ((source.fieldDomains ++ source.hypothesisDomains).take source.position)
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take (recursorMinorOffset indTypes owner + i)) []))).toCtx
    hypothesisResidual

/-- Named implementation view of the selected hypothesis comparison. -/
structure RecursorInstallation.RuleAlignment.HypothesisFrame where
  source : RecursorInstallation.RuleAlignment.HypothesisSource A j T
  replay : RecursorInstallation.RuleAlignment.HypothesisReplay A j hj B T E source
  typing : RecursorInstallation.RuleAlignment.HypothesisTyping A j hj B T E source
  residual : RecursorInstallation.RuleAlignment.HypothesisResidual A j hj B T E source

/-- Construct the named comparison view used by domain transport. -/
theorem RecursorInstallation.RuleAlignment.installedHypothesisFrame :
    Nonempty (A.HypothesisFrame j hj B T E) := by
  rcases A.installedSelectedMinorHypothesisDeclarationDomainAt j hj with
    ⟨T₀, S, hypothesisOrigins, traversal, fieldDomains,
      hypothesisDomains, targetResidual, D, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
      hsourceSelected,
      hruleSelected, hlocal, hsourceFields, hsourceHypotheses,
      hsourceContext,
      HminorSemantic,
      hproducerShape, hfields, hhypotheses, htarget, _Hbinder, Hdomain,
      HdomainType, originRoot, sourceType, O, _hdeclarationConsumed,
      hdeclarationExact, HproducerReplay⟩
  have htelescope : T₀ = T := T₀.eq T
  subst T₀
  subst stats
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  have hjTraversal : j < traversal.recursiveFields.size := by
    rw [htraversalRecursiveFields, ← S.hypotheses_size,
      hsourceHypotheses]
    exact hj
  have hjSourceRecursive : j < S.recursiveFields.size := by
    rw [← S.hypotheses_size, hsourceHypotheses]
    exact hj
  have HminorDecisions : RecursorFieldDecisions hypothesisOrigins.stats
      traversal.rootContext traversal.parameterTail traversal.terminalContext
      traversal.terminal S.fields S.recursiveFields
      traversal.recursivePositions := by
    simpa [htraversalStats, htraversalFields,
      htraversalRecursiveFields] using traversal.decisions
  have HruleDecisions : RecursorFieldDecisions hypothesisOrigins.stats
      A.typing.fieldRoot traversal.parameterTail A.rule.root
      A.rule.target A.rule.allArgs A.rule.recursiveArgs
      A.typing.recursivePositions := by
    rw [hparameterTail]
    exact A.typing.decisions
  have Hreplay :
      O.replayTrace S.fields_bound.fvars =
        E.frame.semantic.generated.replayTrace
          A.rule.all_args_bound.fvars := by
    exact HproducerReplay.trans E.frame.producerReplay_eq
  have HlocalTelescopeReplay :
      (O.current.lctx.mkForall O.args (.sort .zero)).abstractList
          S.fields_bound.fvars =
        (E.frame.semantic.generated.current.lctx.mkForall
            E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars := by
    exact congrArg InductionHypothesisShape.localTelescope Hreplay
  have hownerReplay : O.ownerIdx =
      E.frame.semantic.generated.ownerIdx :=
    congrArg InductionHypothesisShape.ownerIdx Hreplay
  have hmotiveReplay :
      ((hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
            O.arguments_bound.fvars).abstractList
          S.fields_bound.fvars O.args.size) =
        ((((H.recInfos.map
              (fun info : AddInductive.RecInfo => info.motive))[
              E.frame.semantic.generated.ownerIdx]!).abstractList
            E.frame.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars
            E.frame.semantic.generated.localArgs.size) := by
    exact congrArg InductionHypothesisShape.motive Hreplay
  have hindicesReplay :
      (((O.exposedType.getAppArgs[
            hypothesisOrigins.stats.params.size:] : Array Expr).map
          fun index =>
            (index.abstractList O.arguments_bound.fvars).abstractList
              S.fields_bound.fvars O.args.size) =
        ((E.frame.semantic.generated.exposedType.getAppArgs[
              hypothesisOrigins.stats.params.size:] : Array Expr).map
          fun index =>
            (index.abstractList
              E.frame.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.all_args_bound.fvars
                E.frame.semantic.generated.localArgs.size)) := by
    exact congrArg InductionHypothesisShape.indices Hreplay
  have hlocalArity : O.args.size =
      E.frame.semantic.generated.localArgs.size :=
    congrArg InductionHypothesisShape.localArity Hreplay
  have HlocalForallReplay : ∀ left right,
      Expr.SameForallPrefix O.args.size
        ((O.current.lctx.mkForall O.args left).abstractList
          S.fields_bound.fvars)
        ((E.frame.semantic.generated.current.lctx.mkForall
            E.frame.semantic.generated.localArgs right).abstractList
          A.rule.all_args_bound.fvars) := by
    intro left right
    exact sameForallPrefix_of_localTelescope
      (O.arguments_bound.toFVarArrayIn.toCDeclArray O.current_wf)
      (E.frame.semantic.generated.arguments_bound.toFVarArrayIn.toCDeclArray
        E.frame.semantic.generated.current_wf)
      O.arguments_bound.nodup E.frame.semantic.generated.arguments_bound.nodup
      S.fields_bound.fvars A.rule.all_args_bound.fvars hlocalArity
      HlocalTelescopeReplay left right
  have HlocalLambdaReplay : Expr.SameLambdaPrefix E.localDomains.length
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      ((E.frame.semantic.generated.current.lctx.mkLambda
          E.frame.semantic.generated.localArgs
          (mkAppN A.rule.recursiveArgs[j]
            E.frame.semantic.generated.localArgs)).abstractList
        A.rule.binders) := by
    exact E.source_template_prefix
  have hownerStats : O.ownerIdx < hypothesisOrigins.stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some O.owner_valid).1
  have hownerRecInfos : O.ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records, ← H.cardinality.families]
    exact hownerStats
  have hownerOrigin : O.ownerIdx < hypothesisOrigins.recInfos.size := by
    have hsizes := congrArg Array.size hhypothesisRecInfos
    simp only [Array.size_map] at hsizes
    omega
  have hmotiveSnapshot :
      hypothesisOrigins.recInfos[O.ownerIdx]!.motive =
        H.recInfos[O.ownerIdx]!.motive := by
    have hget := congrArg (fun motives => motives[O.ownerIdx]!)
      hhypothesisRecInfos
    rw [getElem!_pos (hypothesisOrigins.recInfos.map (·.motive))
      O.ownerIdx (by simpa using hownerOrigin)] at hget
    rw [getElem!_pos (H.recInfos.map (·.motive)) O.ownerIdx
      (by simpa using hownerRecInfos)] at hget
    rw [getElem!_pos hypothesisOrigins.recInfos O.ownerIdx hownerOrigin,
      getElem!_pos H.recInfos O.ownerIdx hownerRecInfos]
    simpa only [Array.getElem_map] using hget
  rcases O.motive_is_fvar with
    ⟨motiveFVar, hmotiveOrigin, hmotiveOriginRoot⟩
  have hmotiveFinal : H.recInfos[O.ownerIdx]!.motive =
      .fvar motiveFVar := hmotiveSnapshot.symm.trans hmotiveOrigin
  have hownerMotiveArray : O.ownerIdx <
      (H.recInfos.map (·.motive)).size := by simpa using hownerRecInfos
  have hownerMotiveFVars : O.ownerIdx <
      H.bindings.motives.fvars.length := by
    rw [H.bindings.motives.length_fvars]
    exact hownerMotiveArray
  rcases H.bindings.motives.getElem_eq_fvar O.ownerIdx
      hownerMotiveArray with ⟨_hownerMotiveFVars, hmotiveAt⟩
  have hmotiveAt' : H.recInfos[O.ownerIdx]!.motive =
      .fvar H.bindings.motives.fvars[O.ownerIdx] := by
    rw [getElem!_pos H.recInfos O.ownerIdx hownerRecInfos]
    simpa only [Array.getElem_map] using hmotiveAt
  have hmotiveFVarExact : motiveFVar =
      H.bindings.motives.fvars[O.ownerIdx] :=
    Expr.fvar.inj (hmotiveFinal.symm.trans hmotiveAt')
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  let position := A.rule.allArgs.size + j
  let motivePosition := H.params.fvars.length + O.ownerIdx
  have hsourceBindersNodup : sourceBinders.Nodup := by
    have houter := H.bindings.outerNodup H.params H.noAlias
    have hsub :
        (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars.take
              (recursorMinorOffset indTypes owner + i) <+
          (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars :=
      (List.Sublist.refl
        (H.params.fvars ++ H.bindings.motives.fvars)).append
          (List.take_sublist _ H.bindings.flatMinors.fvars)
    simpa [sourceBinders, List.append_assoc] using houter.sublist hsub
  have hmotiveNormal : (Expr.fvar motiveFVar).abstractList
      sourceBinders position =
      .bvar (position + (sourceBinders.length - 1 - motivePosition)) := by
    rw [hmotiveFVarExact]
    exact abstractMotiveInSourceContext H.params.fvars H.bindings.motives.fvars
      (H.bindings.flatMinors.fvars.take (recursorMinorOffset indTypes owner + i))
      hsourceBindersNodup O.ownerIdx hownerMotiveFVars position
  let fieldPosition := A.typing.recursivePositions[j]!
  have hfieldPositionRule : fieldPosition < A.rule.allArgs.size :=
    (A.typing.decisions.selected_at j hj).1
  have hfieldPositionSource : fieldPosition < S.fields.size := by
    rw [hsourceFields]
    exact hfieldPositionRule
  have hfieldPositionFVars : fieldPosition <
      S.fields_bound.fvars.length := by
    rw [S.fields_bound.length_fvars]
    exact hfieldPositionSource
  rcases S.fields_bound.getElem_eq_fvar fieldPosition
      hfieldPositionSource with ⟨_hfieldPositionFVars, hfieldAt⟩
  have hsourceFieldExact : S.recursiveFields[j]! =
      .fvar S.fields_bound.fvars[fieldPosition] :=
    hsourceSelected.trans <| (getElem!_pos S.fields fieldPosition
      hfieldPositionSource).trans hfieldAt
  rcases O.field_fvar with ⟨sourceFVar, hsourceFVar, hsourceFVarRoot⟩
  have hsourceFVarExact : sourceFVar =
      S.fields_bound.fvars[fieldPosition] :=
    Expr.fvar.inj (hsourceFVar.symm.trans hsourceFieldExact)
  have houterField := O.outerAbstractedField_eq_bvar_at hsourceFVar
    hsourceFVarRoot S.fields_nodup hfieldPositionFVars
      hsourceFVarExact.symm
  have hrecursiveMajor := E.frame.outerAbstractedAppliedMajorOrdinal
  have hfieldBinderLength : S.fields_bound.fvars.length =
      A.rule.allArgs.size :=
    S.fields_bound.length_fvars.trans hsourceFields
  have horiginLocal : O.arguments_bound.fvars.length = O.args.size :=
    O.arguments_bound.toFVarArrayIn.length_fvars
  have hgeneratedLocal :
      E.frame.semantic.generated.arguments_bound.fvars.length =
        E.frame.semantic.generated.localArgs.size :=
    E.frame.semantic.generated.arguments_bound.toFVarArrayIn.length_fvars
  have hlocalIndices : O.localIndices =
      E.frame.semantic.generated.localIndices := by
    apply List.ext_getElem
    · simp [InductionHypothesisType.localIndices,
        RecursiveCall.localIndices, horiginLocal,
        hgeneratedLocal, hlocalArity]
    · intro k hkOrigin hkGenerated
      simp [InductionHypothesisType.localIndices,
        RecursiveCall.localIndices, horiginLocal,
        hgeneratedLocal, hlocalArity]
  have hmajorAlignment :
      O.outerAbstractedField S.fields_bound.fvars =
        E.frame.semantic.generated.outerAbstractedMajor A.rule.binders := by
    rw [show O.outerAbstractedField S.fields_bound.fvars =
        mkAppN
          (.bvar (O.args.size +
            (S.fields_bound.fvars.length - 1 - fieldPosition)))
          (O.localIndices.map Expr.bvar).toArray by
        simpa [fieldPosition] using houterField]
    rw [hrecursiveMajor, hfieldBinderLength, hlocalArity, hlocalIndices]
  have hfieldPositionRuleFVars : fieldPosition <
      A.rule.all_args_bound.fvars.length := by
    rw [A.rule.all_args_bound.length_fvars]
    exact hfieldPositionRule
  rcases A.rule.all_args_bound.getElem_eq_fvar fieldPosition
      hfieldPositionRule with ⟨_hfieldPositionRuleFVars, hruleFieldAt⟩
  have hruleFieldExact : A.rule.recursiveArgs[j] =
      .fvar A.rule.all_args_bound.fvars[fieldPosition] := by
    rw [← getElem!_pos A.rule.recursiveArgs j hj]
    exact hruleSelected.trans <| (getElem!_pos A.rule.allArgs fieldPosition
      hfieldPositionRule).trans hruleFieldAt
  have hgeneratedMajorFields :=
    E.frame.semantic.generated.outerAbstractedMajor_eq_bvar_at
      hruleFieldExact
      (E.frame.field_mem_originRoot
        (List.getElem_mem hfieldPositionRuleFVars))
      A.rule.all_args_nodup hfieldPositionRuleFVars rfl
  have hmajorFieldAlignment :
      O.outerAbstractedField S.fields_bound.fvars =
        E.frame.semantic.generated.outerAbstractedMajor
          A.rule.all_args_bound.fvars := by
    rw [show O.outerAbstractedField S.fields_bound.fvars =
        mkAppN
          (.bvar (O.args.size +
            (S.fields_bound.fvars.length - 1 - fieldPosition)))
          (O.localIndices.map Expr.bvar).toArray by
        simpa [fieldPosition] using houterField]
    rw [hgeneratedMajorFields, hfieldBinderLength,
      A.rule.all_args_bound.length_fvars, hlocalArity, hlocalIndices]
  have hmotiveAppAlignment :
      O.outerAbstractedMotiveApp S.fields_bound.fvars =
        E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.all_args_bound.fvars := by
    unfold InductionHypothesisType.outerAbstractedMotiveApp
      RecursiveCall.outerAbstractedMotiveApp
    rw [Hreplay, hmajorFieldAlignment]
  rcases E.frame.motiveApplication with ⟨HproducerMotive⟩
  have HrawGeneratedMotiveClosed : Closed
      (Expr.app
        (mkAppN
          (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
          E.frame.semantic.generated.exposedType.getAppArgs[
            hypothesisOrigins.stats.params.size:])
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs)) 0 := by
    have hclosed := HproducerMotive.translation.closed
    rw [E.frame.semantic.current_context.mlctx.noBV] at hclosed
    exact hclosed
  have HlocalGeneratedMotiveClosed : Closed
      ((Expr.app
        (mkAppN
          (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
          E.frame.semantic.generated.exposedType.getAppArgs[
            hypothesisOrigins.stats.params.size:])
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs)).abstractList
            E.frame.semantic.generated.arguments_bound.fvars)
      E.frame.semantic.generated.localArgs.size := by
    have hclosed := Closed.abstractList_at
      (fvars := E.frame.semantic.generated.arguments_bound.fvars)
      (depth := 0) (outer := 0) HrawGeneratedMotiveClosed
    simpa [E.frame.semantic.generated.arguments_bound.length_fvars] using
      hclosed
  have hfieldLoose : A.rule.recursiveArgs[j].looseBVarRange' = 0 := by
    have hclosed := E.frame.semantic.field_translation.closed
    rw [E.frame.originContext.mlctx.noBV] at hclosed
    exact hclosed.looseBVarRange_zero
  have HgeneratedMotiveClosed : Closed
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars)
      (E.frame.semantic.generated.localArgs.size + A.rule.allArgs.size) := by
    have hclosed := Closed.abstractList_at
      (fvars := A.rule.all_args_bound.fvars)
      (depth := E.frame.semantic.generated.localArgs.size) (outer := 0)
      HlocalGeneratedMotiveClosed
    have hnormalize :=
      E.frame.semantic.generated.outerAbstractedMotiveApp_eq
        A.rule.all_args_bound.fvars hfieldLoose
    dsimp only at hnormalize
    rw [hnormalize] at hclosed
    simpa [A.rule.all_args_bound.length_fvars] using hclosed
  rcases E.frame.cachedCallArgumentFrame (B := B) with
    ⟨_binding, _evidence, _scope, _Hscope, _fieldDomains, _localDomains,
      _narrowIndices, _narrowMajor, _narrowExposed, _hscopeContext,
      _hfields, _hfieldEq, _hlocal, HneutralTranslation,
      _HneutralType, _Hctx, _hlength, _Hindices, _Hmajor,
      _Hexposed, _Htyping, _HindexEq, _HmajorEq⟩
  have HgeneratedNeutralClosed : Closed
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars) A.rule.allArgs.size := by
    have hraw := HneutralTranslation.closed
    rw [B.runtime.noBV] at hraw
    have hclosed := Closed.abstractList_at
      (fvars := A.rule.all_args_bound.fvars)
      (depth := 0) (outer := 0) hraw
    simpa [A.rule.all_args_bound.length_fvars] using hclosed
  let generatedMotiveApp := Expr.app
    (mkAppN H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive
      E.frame.semantic.generated.exposedType.getAppArgs[
        hypothesisOrigins.stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let generatedFieldSource :=
    (E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
        A.rule.all_args_bound.fvars
  let generatedNeutralSource :=
    (E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars
  let Gselection :=
    E.frame.semantic.generated.arguments_bound.toFVarArrayIn.toCDeclArray
      E.frame.semantic.generated.current_wf
  have HgeneratedActualNeutral : Expr.SameForallPrefix
      E.frame.semantic.generated.localArgs.size
      generatedFieldSource generatedNeutralSource := by
    have Hprefix := (Gselection.sameForallPrefix
      E.frame.semantic.generated.arguments_bound.nodup
      generatedMotiveApp (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars
    simpa [generatedFieldSource, generatedNeutralSource,
      generatedMotiveApp, Gselection] using Hprefix
  have HgeneratedTelescope : Expr.ForallTelescope generatedFieldSource
      E.frame.semantic.generated.localArgs.size
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars) := by
    have hresidual :=
      E.frame.semantic.generated.outerAbstractedMotiveApp_eq
        A.rule.all_args_bound.fvars hfieldLoose
    have hgeneratedOwnerRecInfos :
        E.frame.semantic.generated.ownerIdx < H.recInfos.size := by
      simpa [H.generated.length] using E.frame.entry_lt
    have hselectedMotive :
        (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]! =
          H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive := by
      rw [getElem!_pos (H.recInfos.map (·.motive))
          E.frame.semantic.generated.ownerIdx
            (by simpa using hgeneratedOwnerRecInfos),
        getElem!_pos H.recInfos E.frame.semantic.generated.ownerIdx
          hgeneratedOwnerRecInfos]
      simp
    rw [hselectedMotive] at hresidual
    rcases E.frame.motiveApplication with ⟨HproducerMotive'⟩
    have hgenClosed : Closed generatedMotiveApp := by
      have hclosed := HproducerMotive'.translation.closed
      rw [E.frame.semantic.current_context.mlctx.noBV, hselectedMotive] at hclosed
      simpa [generatedMotiveApp] using hclosed
    have Hsource :=
      E.frame.semantic.generated.arguments_bound.toFVarArrayIn.mkForall_forallTelescopeList
        E.frame.semantic.generated.current_wf generatedMotiveApp
        E.frame.semantic.generated.arguments_bound.nodup hgenClosed
    have Hsource' := Hsource.abstractList
      A.rule.all_args_bound.fvars 0
    have hresidual' :
        (generatedMotiveApp.abstractList
          E.frame.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
              E.frame.semantic.generated.localArgs.size =
          E.frame.semantic.generated.outerAbstractedMotiveApp
            A.rule.all_args_bound.fvars := by
      simpa [generatedMotiveApp] using hresidual
    simpa [generatedFieldSource, Nat.zero_add, hresidual'] using Hsource'
  have HgeneratedFieldClosed : Closed generatedFieldSource
      A.rule.allArgs.size := by
    exact HgeneratedActualNeutral.leftClosed HgeneratedTelescope
      (by simpa [generatedNeutralSource] using HgeneratedNeutralClosed)
      (by simpa [Nat.add_comm] using HgeneratedMotiveClosed)
  let localMotiveApp :=
    (Expr.app
      (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
        O.exposedType.getAppArgs[hypothesisOrigins.stats.params.size:])
      (mkAppN S.recursiveFields[j]! O.args)).abstractList
        O.arguments_bound.fvars
  have hfieldClosedMotiveApp :
      localMotiveApp.abstractList S.fields_bound.fvars O.args.size =
        O.outerAbstractedMotiveApp S.fields_bound.fvars := by
    simpa [localMotiveApp] using
      O.outerAbstractedMotiveApp_eq S.fields_bound.fvars
  have HgeneratedMotiveScope :=
    E.frame.fieldAbstractedNormalizedMotiveSourceScope
  have HoriginMotiveScope :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn fun fv =>
        fv ∈ ExprArrayFVarIds hypothesisOrigins.stats.params ++
          ExprArrayFVarIds (H.recInfos.map (·.motive)) := by
    rw [hmotiveAppAlignment]
    exact HgeneratedMotiveScope
  have HoriginMotiveAvoidsHypotheses :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn
        (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HoriginMotiveScope.mono
    intro fv houter hhypothesis
    apply hypothesisOrigins.hypotheses_outer_fresh fv
    · simpa [hhypothesisRecInfos] using houter
    · rw [S.hypotheses_bound.exprArrayFVarIds]
      exact hhypothesis
  have HoriginMotiveClosed : Closed
      (O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (O.args.size + S.fields.size) := by
    rw [hmotiveAppAlignment]
    simpa [hlocalArity, hsourceFields] using HgeneratedMotiveClosed
  have HlocalMotiveClosed : Closed localMotiveApp O.args.size := by
    apply Expr.closed_of_abstractList
    rw [hfieldClosedMotiveApp]
    simpa [S.fields_bound.length_fvars] using HoriginMotiveClosed
  have HlocalMotiveScope : localMotiveApp.FVarsIn fun fv =>
      fv ∈ S.fields_bound.fvars ∨
        fv ∉ S.hypotheses_bound.fvars := by
    apply FVarsIn.of_abstractList
    rw [hfieldClosedMotiveApp]
    exact HoriginMotiveAvoidsHypotheses
  have HlocalMotiveAvoidsHypotheses :
      localMotiveApp.FVarsIn
        (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HlocalMotiveScope.mono
    intro fv hfv hhypothesis
    rcases hfv with hfield | hnotHypothesis
    · exact S.hypotheses_fields_fresh fv hhypothesis hfield
    · exact hnotHypothesis hhypothesis
  let previousHypothesisFVars := S.hypotheses_bound.fvars.take j
  have hpreviousHypothesisFVarsLength :
      previousHypothesisFVars.length = j := by
    simp only [previousHypothesisFVars, List.length_take]
    have hjHypothesisFVars : j < S.hypotheses_bound.fvars.length := by
      rw [S.hypotheses_bound.length_fvars, hsourceHypotheses]
      exact hj
    omega
  have HlocalMotiveAvoidsPrevious : localMotiveApp.FVarsIn
      (fun fv => fv ∉ previousHypothesisFVars) := by
    apply HlocalMotiveAvoidsHypotheses.mono
    intro fv hnotAll hprevious
    exact hnotAll (List.mem_of_mem_take hprevious)
  have hpreviousMotiveAbstract :
      localMotiveApp.abstractList previousHypothesisFVars O.args.size =
        localMotiveApp :=
    HlocalMotiveAvoidsPrevious.abstractList_eq_self HlocalMotiveClosed
  have hfieldMotiveShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := localMotiveApp) (fvars := S.fields_bound.fvars)
    (depth := O.args.size) (extra := j)
    HlocalMotiveClosed S.fields_nodup
  have hpreviousFieldMotiveNormalization :
      (localMotiveApp.abstractList previousHypothesisFVars
          O.args.size).abstractList
        S.fields_bound.fvars (O.args.size + j) =
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).liftLooseBVars'
        O.args.size j := by
    rw [hpreviousMotiveAbstract, hfieldMotiveShift,
      hfieldClosedMotiveApp]
  subst sourceType
  have HsourceTelescope := O.sourceTelescopeList
    (O.motiveApp_closed_of_outer S.fields_bound.fvars
      (by simpa [S.fields_bound.length_fvars] using HoriginMotiveClosed))
  have HpreviousHypotheses := HsourceTelescope.abstractList
    (S.hypotheses_bound.fvars.take j) 0
  have HsourceFields := HpreviousHypotheses.abstractList
    S.fields_bound.fvars j
  have HsourceOuter := HsourceFields.abstractList sourceBinders position
  let declarationDomain :=
    ((D.type.abstractList
        (S.hypotheses_bound.fvars.take j)).abstractList
      S.fields_bound.fvars j).abstractList sourceBinders position
  change Expr.ForallTelescope declarationDomain O.args.size _ at HsourceOuter
  have HtypedDeclaration :=
    Expr.ForallTelescopeTypeTranslation.ofTrExprS
      HsourceOuter Hdomain HdomainType
  rcases HtypedDeclaration.toWrapForalls with
    ⟨hypothesisLocalDomains, sourceResidual, hypothesisResidual,
      hhypothesisLocalDomains, _HsourceResidual, hhypothesisDomain,
      HhypothesisResidual, HhypothesisResidualType⟩
  have hsourceResidual := _HsourceResidual.residual_eq HsourceOuter
  have hlocalMotiveApp := O.abstractedMotiveApp_eq
  have hlocalMotiveApp' :
      (Expr.app
        (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
          O.exposedType.getAppArgs[hypothesisOrigins.stats.params.size:])
        (mkAppN S.recursiveFields[j]! O.args)).abstractList
          O.arguments_bound.fvars =
        Expr.app
          (mkAppN
            (hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
              O.arguments_bound.fvars)
            (((O.exposedType.getAppArgs[
                hypothesisOrigins.stats.params.size:] : Array Expr)
              ).map fun index =>
              index.abstractList O.arguments_bound.fvars))
          O.abstractedField := by
    simpa [InductionHypothesisType.abstractedField,
      InductionHypothesisType.localIndices, List.map_ofFn,
      Function.comp_def] using hlocalMotiveApp
  have hsourceResidualStructured : sourceResidual =
      ((((Expr.app
          (mkAppN
            (hypothesisOrigins.recInfos[O.ownerIdx]!.motive.abstractList
              O.arguments_bound.fvars)
            (((O.exposedType.getAppArgs[
                hypothesisOrigins.stats.params.size:] : Array Expr)
              ).map fun index =>
              index.abstractList O.arguments_bound.fvars))
          O.abstractedField).abstractList
        (S.hypotheses_bound.fvars.take j) O.args.size).abstractList
      S.fields_bound.fvars (O.args.size + j)).abstractList
      sourceBinders (O.args.size + position)) := by
    rw [← hlocalMotiveApp']
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hsourceResidual
  have hsourceResidualNormalized : sourceResidual =
      ((O.outerAbstractedMotiveApp
          S.fields_bound.fvars).liftLooseBVars'
        O.args.size j).abstractList sourceBinders
          (O.args.size + position) := by
    have hsourceResidualLocal : sourceResidual =
        ((localMotiveApp.abstractList previousHypothesisFVars
            O.args.size).abstractList S.fields_bound.fvars
          (O.args.size + j)).abstractList sourceBinders
            (O.args.size + position) := by
      simpa [localMotiveApp, previousHypothesisFVars, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hsourceResidual
    rw [hsourceResidualLocal, hpreviousFieldMotiveNormalization]
  have hsourceResidualOuterTransport : sourceResidual =
      ((O.outerAbstractedMotiveApp
          S.fields_bound.fvars).abstractList sourceBinders
        (O.args.size + S.fields.size)).liftLooseBVars'
          O.args.size j := by
    rw [hsourceResidualNormalized]
    have hcommute := Expr.liftLooseBVars'_abstractList_add
      (e := O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (fvars := sourceBinders) (start := O.args.size)
      (cutoff := O.args.size + S.fields.size) (amount := j)
      (by omega) hsourceBindersNodup
    simpa [position, hsourceFields, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hcommute
  have hsourceParamsRule : H.params.fvars =
      A.rule.params_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.params
      A.rule.params_bound rfl
  have hsourceMotivesRule : H.bindings.motives.fvars =
      A.rule.motives_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.bindings.motives
      A.rule.motives_bound rfl
  have hsourceMinorsRule : H.bindings.flatMinors.fvars =
      A.rule.minors_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.bindings.flatMinors
      A.rule.minors_bound rfl
  have hsourceBindersRule : sourceBinders =
      A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars ++
        A.rule.minors_bound.fvars.take
          (recursorMinorOffset indTypes owner + i) := by
    dsimp only [sourceBinders]
    rw [hsourceParamsRule, hsourceMotivesRule, hsourceMinorsRule]
  have hsourceResidualGeneratedPrefix : sourceResidual =
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.all_args_bound.fvars).abstractList
        (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars ++
          A.rule.minors_bound.fvars.take
            (recursorMinorOffset indTypes owner + i))
        (E.frame.semantic.generated.localArgs.size +
          A.rule.allArgs.size)).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j := by
    rw [hsourceResidualOuterTransport, hmotiveAppAlignment,
      hsourceBindersRule, hlocalArity, hsourceFields]
  let generatedBase :=
    E.frame.semantic.generated.outerAbstractedMotiveApp
      A.rule.all_args_bound.fvars
  let generatedPrefix :=
    (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
      A.rule.minors_bound.fvars.take
        (recursorMinorOffset indTypes owner + i)
  let remainingMinorFVars := A.rule.minors_bound.fvars.drop
    (recursorMinorOffset indTypes owner + i)
  let generatedCutoff :=
    E.frame.semantic.generated.localArgs.size + A.rule.allArgs.size
  have HgeneratedBaseClosed : Closed generatedBase generatedCutoff := by
    dsimp only [generatedBase, generatedCutoff]
    rw [← hmotiveAppAlignment, ← hlocalArity, ← hsourceFields]
    exact HoriginMotiveClosed
  have HgeneratedBaseAvoidsRemaining : generatedBase.FVarsIn
      (fun fv => fv ∉ remainingMinorFVars) := by
    apply HgeneratedMotiveScope.mono
    intro fv houter hremaining
    have houter' : fv ∈ A.rule.params_bound.fvars ++
        A.rule.motives_bound.fvars := by
      simpa [A.rule.params_bound.exprArrayFVarIds,
        A.rule.motives_bound.exprArrayFVarIds] using houter
    have hminor : fv ∈ A.rule.minors_bound.fvars :=
      List.mem_of_mem_drop hremaining
    have hdisjoint :=
      (List.nodup_append.mp A.rule.outer_binders_nodup).2.2
    exact hdisjoint fv houter' fv hminor rfl
  have hremainingAbstract : generatedBase.abstractList
      remainingMinorFVars generatedCutoff = generatedBase :=
    HgeneratedBaseAvoidsRemaining.abstractList_eq_self
      HgeneratedBaseClosed
  have hgeneratedPrefixNodup : generatedPrefix.Nodup := by
    have hsub : generatedPrefix <+
        (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
          A.rule.minors_bound.fvars :=
      (List.Sublist.refl
        (A.rule.params_bound.fvars ++
          A.rule.motives_bound.fvars)).append
            (List.take_sublist _ A.rule.minors_bound.fvars)
    exact A.rule.outer_binders_nodup.sublist hsub
  have hgeneratedOuterSplit : generatedPrefix ++ remainingMinorFVars =
      (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
        A.rule.minors_bound.fvars := by
    simp [generatedPrefix, remainingMinorFVars, List.append_assoc]
  have hgeneratedOuterNodup :
      (generatedPrefix ++ remainingMinorFVars).Nodup := by
    rw [hgeneratedOuterSplit]
    exact A.rule.outer_binders_nodup
  have hprefixShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := generatedBase) (fvars := generatedPrefix)
    (depth := generatedCutoff) (extra := remainingMinorFVars.length)
    HgeneratedBaseClosed hgeneratedPrefixNodup
  have hprefixAppend := Expr.abstractList_after_inner
    (e := generatedBase) (outer := generatedPrefix)
    (inner := remainingMinorFVars) (k := generatedCutoff)
    hgeneratedOuterNodup
  rw [hremainingAbstract] at hprefixAppend
  have hprefixToFull :
      (generatedBase.abstractList generatedPrefix generatedCutoff
        ).liftLooseBVars' generatedCutoff remainingMinorFVars.length =
      E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders := by
    have hcombined :
        (generatedBase.abstractList generatedPrefix generatedCutoff
          ).liftLooseBVars' generatedCutoff remainingMinorFVars.length =
        generatedBase.abstractList
          (generatedPrefix ++ remainingMinorFVars) generatedCutoff :=
      hprefixShift.symm.trans hprefixAppend
    rw [hgeneratedOuterSplit] at hcombined
    have hfullSource :=
      E.frame.outerAbstractedNormalizedMotiveSource
    rw [A.rule.all_args_bound.length_fvars] at hfullSource
    exact hcombined.trans <| by
      simpa [generatedBase, generatedCutoff] using hfullSource
  have hsourceResidualFullTransport :
      sourceResidual.liftLooseBVars'
          (E.frame.semantic.generated.localArgs.size +
            A.rule.allArgs.size + j) remainingMinorFVars.length =
        (E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.binders).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j := by
    have hsourcePrefix : sourceResidual =
        (generatedBase.abstractList generatedPrefix generatedCutoff
          ).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j := by
      simpa [generatedBase, generatedPrefix, generatedCutoff,
        List.append_assoc] using hsourceResidualGeneratedPrefix
    rw [hsourcePrefix]
    have hcommute := Expr.liftLooseBVars_comm
      (generatedBase.abstractList generatedPrefix generatedCutoff)
      remainingMinorFVars.length j generatedCutoff
      E.frame.semantic.generated.localArgs.size (by
        simp [generatedCutoff])
    rw [← hprefixToFull]
    simpa [generatedCutoff, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcommute.symm
  let hypothesisInner :=
    ((fieldDomains ++ hypothesisDomains).take position) ++
      hypothesisLocalDomains
  let remainingMinorDomains := T.minors.drop
    (recursorMinorOffset indTypes owner + i)
  let liftedHypothesisInner :=
    (liftContextPrefix remainingMinorDomains.length
      hypothesisInner.reverse).reverse
  have hpositionLE : position ≤
      (fieldDomains ++ hypothesisDomains).length := by
    simp only [position, List.length_append]
    rw [hfields, hhypotheses]
    omega
  have hhypothesisInnerLength : hypothesisInner.length =
      E.frame.semantic.generated.localArgs.size +
        A.rule.allArgs.size + j := by
    simp only [hypothesisInner, List.length_append]
    rw [List.length_take_of_le hpositionLE, hhypothesisLocalDomains,
      hlocalArity]
    simp only [position]
    omega
  have hremainingMinorDomainsLength : remainingMinorDomains.length =
      remainingMinorFVars.length := by
    simp only [remainingMinorDomains, remainingMinorFVars,
      List.length_drop]
    rw [T.minors_length, A.rule.minors_bound.length_fvars]
  have HhypothesisResidualFlat : TrExprS H.outVEnv Us
      (abstractForallContext
        ((T.params ++ T.motives ++ T.minors.take
            (recursorMinorOffset indTypes owner + i)) ++
          hypothesisInner) [])
      sourceResidual hypothesisResidual := by
    simpa only [hypothesisInner, abstractForallContext_append,
      List.append_assoc] using HhypothesisResidual
  have HhypothesisResidualInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := T.params ++ T.motives ++ T.minors.take
        (recursorMinorOffset indTypes owner + i))
      (inner := hypothesisInner) H.outVEnvWF.orderedStrong
      HhypothesisResidualFlat remainingMinorDomains
  have HhypothesisResidualFull : TrExprS H.outVEnv Us
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++
          liftedHypothesisInner) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (hypothesisResidual.liftN remainingMinorDomains.length
        hypothesisInner.length) := by
    rw [← hsourceResidualFullTransport,
      ← hremainingMinorDomainsLength, ← hhypothesisInnerLength]
    simpa [remainingMinorDomains, liftedHypothesisInner,
      List.append_assoc] using HhypothesisResidualInserted
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let previousHypothesisDomains := hypothesisDomains.take j
  let liftedCanonicalLocals :=
    (liftContextPrefix previousHypothesisDomains.length
      E.localDomains.reverse).reverse
  have hpreviousHypothesisDomainsLength :
      previousHypothesisDomains.length = j := by
    simp only [previousHypothesisDomains, List.length_take]
    rw [hhypotheses]
    omega
  have HcanonicalResultType : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa only [equationDomains] using E.result_type_translation
  have HcanonicalResultTypeInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := E.localDomains)
      H.outVEnvWF.orderedStrong HcanonicalResultType previousHypothesisDomains
  have HcanonicalResultTypeFull : TrExprS H.outVEnv Us
      (abstractForallContext
        (equationDomains ++ previousHypothesisDomains ++
          liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (E.resultType.liftN previousHypothesisDomains.length
        E.localDomains.length) := by
    simpa [liftedCanonicalLocals, hpreviousHypothesisDomainsLength,
      E.local_length] using HcanonicalResultTypeInserted
  let source : A.HypothesisSource j T := {
    shape := S
    origins := hypothesisOrigins
    traversal := traversal
    fieldDomains := fieldDomains
    hypothesisDomains := hypothesisDomains
    targetResidual := targetResidual
    declaration := D
    originRoot := originRoot
    sourceType := D.type
    origin := O
    origins_eq := hhypothesisOrigins
    stats_eq := rfl
    motives_eq := hhypothesisRecInfos
    owner_lt := hownerRecInfos
    motive_snapshot := hmotiveSnapshot
    motive_position := ⟨motiveFVar, hmotiveFinal, hmotiveNormal⟩
    traversal_eq := htraversal
    fields_eq := htraversalFields
    recursive_fields_eq := htraversalRecursiveFields
    traversal_stats_eq := htraversalStats
    parameter_tail_eq := hparameterTail
    recursive_positions_eq := hpositions
    source_selected := hsourceSelected
    rule_selected := hruleSelected
    local_index_eq := hlocal
    source_fields_length := hsourceFields
    source_hypotheses_length := hsourceHypotheses
    context_le := hsourceContext
    semantic := HminorSemantic
    fields_length := hfields
    hypotheses_length := hhypotheses
    selected_minor_eq := htarget
    declaration_type_eq := rfl
  }
  refine ⟨{
    source := source
    replay := {
      source_major_eq := by simpa [fieldPosition] using houterField
      generated_major_eq := hrecursiveMajor
      replay_eq := Hreplay
      local_telescope_eq := HlocalTelescopeReplay
      lambda_prefix := HlocalLambdaReplay
      forall_prefix := HlocalForallReplay
      motive_replay_eq := hmotiveReplay
      indices_replay_eq := hindicesReplay
      owner_eq := hownerReplay
      local_length_eq := hlocalArity
      major_eq := hmajorAlignment
      motive_app_eq := hmotiveAppAlignment
      motive_closed := HoriginMotiveClosed
      generated_field_closed := (by simpa [generatedFieldSource, generatedMotiveApp] using
          HgeneratedFieldClosed)
    }
    typing := {
      declaration_translation := Hdomain
      closed_typing := E.closed_typing
    }
    residual := {
      hypothesisLocalDomains := hypothesisLocalDomains
      sourceResidual := sourceResidual
      hypothesisResidual := hypothesisResidual
      local_length := hhypothesisLocalDomains
      source_telescope := _HsourceResidual
      source_eq := by
        simpa [source, sourceBinders, position, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hsourceResidual
      structured_eq := by
        simpa [source, sourceBinders, position, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hsourceResidualStructured
      normalized_eq := by
        simpa [sourceBinders, position] using hsourceResidualNormalized
      outer_transport_eq := by
        simpa [sourceBinders] using hsourceResidualOuterTransport
      generated_prefix_eq := by
        simpa using hsourceResidualGeneratedPrefix
      full_transport_eq := by
        simpa [remainingMinorFVars] using hsourceResidualFullTransport
      hypothesis_translation := by
        simpa [hypothesisInner, remainingMinorDomains,
          liftedHypothesisInner] using HhypothesisResidualFull
      canonical_translation := by
        simpa [equationDomains, previousHypothesisDomains,
              liftedCanonicalLocals] using HcanonicalResultTypeFull
      hypothesis_domain_eq := hhypothesisDomain
      residual_translation := HhypothesisResidual
      residual_type := HhypothesisResidualType
    }
  }⟩

end HypothesisComparison

section HypothesisDomainComparison

variable

    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.FieldFrame)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (E : A.RecursiveResult T B j hj)

/- The installed side starts after the earlier minors and opens fields, earlier
hypotheses, and higher-order locals. The canonical side starts in the fixed
parameter/motive/minor/field context and inserts the earlier hypotheses. -/
abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.minorIndex
    (_F : A.HypothesisFrame j hj B T E) : Nat :=
  recursorMinorOffset indTypes owner + i

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.prior
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  (F.source.fieldDomains ++ F.source.hypothesisDomains).take F.source.position

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.remaining
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  T.minors.drop F.minorIndex

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.previous
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  F.source.hypothesisDomains.take j

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.liftedPrior
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  (liftContextPrefix F.remaining.length F.prior.reverse).reverse

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.liftedFields
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  (liftContextPrefix F.remaining.length F.source.fieldDomains.reverse).reverse

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.liftedPrevious
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  (liftContextPrefixAt F.remaining.length F.source.fieldDomains.length
      F.previous.reverse).reverse

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.liftedHypothesisLocals
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  (liftContextPrefixAt F.remaining.length F.source.position
      F.residual.hypothesisLocalDomains.reverse).reverse

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.equationDomains
    (_F : A.HypothesisFrame j hj B T E) : List VExpr :=
  H.parameterSuffix.parameterDecls.toCtx.reverse ++ T.motives ++ T.minors ++
      (liftContextPrefix (T.motives ++ T.minors).length B.fieldDomains.reverse).reverse

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.motiveApp
    (_F : A.HypothesisFrame j hj B T E) : Expr :=
  Expr.app
      (mkAppN (H.recInfos.map (·.motive))[E.frame.semantic.generated.ownerIdx]!
        E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
      (mkAppN A.rule.recursiveArgs[j] E.frame.semantic.generated.localArgs)

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.liftedCanonicalLocals
    (F : A.HypothesisFrame j hj B T E) : List VExpr :=
  (liftContextPrefix F.liftedPrevious.length E.localDomains.reverse).reverse

abbrev RecursorInstallation.RuleAlignment.HypothesisFrame.residualSource
    (_F : A.HypothesisFrame j hj B T E) : Expr :=
  (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders).liftLooseBVars'
      E.frame.semantic.generated.localArgs.size j

/-- Typed whole-domain comparison in the two displayed contexts.
The inherited frame supplies source provenance and residual equations; these
fields retain only the additional domain transport and alignment facts. -/
structure RecursorInstallation.RuleAlignment.HypothesisDomainFrame where
  frame : A.HypothesisFrame j hj B T E
  prior_split :
    frame.liftedPrior = frame.liftedFields ++ frame.liftedPrevious
  local_length :
    frame.residual.hypothesisLocalDomains.length = E.localDomains.length
  hypothesis_translation :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (T.params ++ T.motives ++ T.minors ++ frame.liftedPrior) [])
    (frame.source.declarationDomain.liftLooseBVars' frame.source.position frame.remaining.length)
    (VExpr.wrapForalls frame.liftedHypothesisLocals
      (frame.residual.hypothesisResidual.liftN frame.remaining.length
        (frame.source.position + frame.residual.hypothesisLocalDomains.length)))
  canonical_translation :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext (frame.equationDomains ++ frame.liftedPrevious) [])
    (((E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs frame.motiveApp).abstractList
        A.rule.binders).liftLooseBVars' 0 frame.liftedPrevious.length)
    (VExpr.wrapForalls frame.liftedCanonicalLocals
      (E.resultType.liftN frame.liftedPrevious.length
        E.localDomains.length))
  forall_prefix :
    Expr.SameForallPrefix E.localDomains.length
    (frame.source.declarationDomain.liftLooseBVars' frame.source.position frame.remaining.length)
    (((E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs frame.motiveApp).abstractList
        A.rule.binders).liftLooseBVars' 0 frame.liftedPrevious.length)
  hypothesis_residual_translation :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (T.params ++ T.motives ++ T.minors ++ frame.liftedPrior ++
        frame.liftedHypothesisLocals) [])
    frame.residualSource
    (frame.residual.hypothesisResidual.liftN frame.remaining.length
      (frame.source.position + frame.residual.hypothesisLocalDomains.length))
  canonical_residual_translation :
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (abstractForallContext
      (frame.equationDomains ++ frame.liftedPrevious ++ frame.liftedCanonicalLocals) [])
    frame.residualSource
    (E.resultType.liftN frame.liftedPrevious.length E.localDomains.length)
  canonical_residual_type :
    H.outVEnv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
    (abstractForallContext
      (frame.equationDomains ++ frame.liftedPrevious ++ frame.liftedCanonicalLocals) []).toCtx
    (E.resultType.liftN frame.liftedPrevious.length E.localDomains.length)

/-- Build the implementation view consumed by recursive-result application. -/
theorem RecursorInstallation.RuleAlignment.installedHypothesisDomains :
    Nonempty (A.HypothesisDomainFrame j hj B T E) := by
  rcases A.installedHypothesisFrame j hj B T E with ⟨F⟩
  let S := F.source.shape
  let hypothesisOrigins := F.source.origins
  let fieldDomains := F.source.fieldDomains
  let hypothesisDomains := F.source.hypothesisDomains
  let targetResidual := F.source.targetResidual
  let D := F.source.declaration
  let originRoot := F.source.originRoot
  let sourceType := F.source.sourceType
  let O := F.source.origin
  have hhypothesisStats :
      hypothesisOrigins.stats = stats := F.source.stats_eq
  have hhypothesisRecInfos :
      hypothesisOrigins.recInfos.map (·.motive) =
      H.recInfos.map (·.motive) := F.source.motives_eq
  have hownerRecInfos :
      O.ownerIdx < H.recInfos.size := F.source.owner_lt
  have hsourceFields :
      S.fields.size = A.rule.allArgs.size := F.source.source_fields_length
  have hsourceHypotheses :
      S.hypotheses.size = A.rule.recursiveArgs.size := F.source.source_hypotheses_length
  have hfields :
      fieldDomains.length = A.rule.allArgs.size := F.source.fields_length
  have hhypotheses :
      hypothesisDomains.length = A.rule.recursiveArgs.size := F.source.hypotheses_length
  have htarget :
      T.minors[(recursorMinorOffset indTypes owner + i)]! = VExpr.wrapForalls
      (fieldDomains ++ hypothesisDomains) targetResidual := F.source.selected_minor_eq
  have hdeclarationType :
      D.type = sourceType := F.source.declaration_type_eq
  have HlocalForallReplay :
      (∀ left right,
      Expr.SameForallPrefix O.args.size
        ((O.current.lctx.mkForall O.args left).abstractList
          S.fields_bound.fvars)
        ((E.frame.semantic.generated.current.lctx.mkForall
            E.frame.semantic.generated.localArgs right).abstractList
          A.rule.all_args_bound.fvars)) := F.replay.forall_prefix
  have hlocalArity :
      O.args.size = E.frame.semantic.generated.localArgs.size := F.replay.local_length_eq
  have hmotiveAppAlignment :
      O.outerAbstractedMotiveApp S.fields_bound.fvars =
      E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars := F.replay.motive_app_eq
  have HoriginMotiveClosedRaw :
      Closed (O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (O.args.size + S.fields.size) := F.replay.motive_closed
  have HgeneratedFieldClosed :
      (let generatedMotiveApp := Expr.app
        (mkAppN
          H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive
          E.frame.semantic.generated.exposedType.getAppArgs[
            stats.params.size:])
        (mkAppN A.rule.recursiveArgs[j]
          E.frame.semantic.generated.localArgs);
      Closed
        ((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs generatedMotiveApp
          ).abstractList A.rule.all_args_bound.fvars)
        A.rule.allArgs.size) := F.replay.generated_field_closed
  have Hdomain := F.typing.declaration_translation
  let hypothesisLocalDomains := F.residual.hypothesisLocalDomains
  let hypothesisResidual := F.residual.hypothesisResidual
  have hhypothesisLocalDomains := F.residual.local_length
  have HhypothesisResidualFull := F.residual.hypothesis_translation
  have hhypothesisDomain := F.residual.hypothesis_domain_eq
  let minorIdx := recursorMinorOffset indTypes owner + i
  let position := A.rule.allArgs.size + j
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let declarationDomain :=
    ((D.type.abstractList
        (S.hypotheses_bound.fvars.take j)).abstractList
      S.fields_bound.fvars j).abstractList sourceBinders position
  let prior := (fieldDomains ++ hypothesisDomains).take position
  let remaining := T.minors.drop minorIdx
  let previous := hypothesisDomains.take j
  let liftedPrior :=
    (liftContextPrefix remaining.length prior.reverse).reverse
  let liftedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let liftedPrevious :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      previous.reverse).reverse
  let liftedHypothesisLocals :=
    (liftContextPrefixAt remaining.length position
      hypothesisLocalDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let liftedCanonicalLocals :=
    (liftContextPrefix liftedPrevious.length
      E.localDomains.reverse).reverse
  have hpositionLE : position ≤
      (fieldDomains ++ hypothesisDomains).length := by
    simp only [position, List.length_append]
    rw [hfields, hhypotheses]
    omega
  have hprior : prior.length = position := by
    simp [prior, List.length_take_of_le hpositionLE]
  have hpriorSplit : prior = fieldDomains ++ previous := by
    unfold prior position previous
    rw [← hfields, List.take_length_add_append]
  have hpreviousLength₀ : previous.length = j := by
    simp only [previous, List.length_take]
    rw [hhypotheses]
    omega
  have hliftedPreviousLength₀ : liftedPrevious.length = j := by
    simp [liftedPrevious, hpreviousLength₀]
  have hliftedPriorSplit : liftedPrior = liftedFields ++ liftedPrevious := by
    simpa [liftedPrior, liftedFields, liftedPrevious, hpriorSplit] using
      liftContextPrefix_reverse_append remaining.length fieldDomains previous
  have HdomainFlat : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        ((T.params ++ T.motives ++ T.minors.take minorIdx) ++ prior) [])
      declarationDomain (VExpr.wrapForalls
        hypothesisLocalDomains hypothesisResidual) := by
    rw [hhypothesisDomain] at Hdomain
    simpa [minorIdx, position, sourceBinders, declarationDomain, prior,
      abstractForallContext_append, List.append_assoc] using Hdomain
  have Hinstalled₀ :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := T.params ++ T.motives ++ T.minors.take minorIdx)
      (inner := prior) H.outVEnvWF.orderedStrong HdomainFlat remaining
  have Hinstalled : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++ liftedPrior) [])
      (declarationDomain.liftLooseBVars' position remaining.length)
      (VExpr.wrapForalls liftedHypothesisLocals
        (hypothesisResidual.liftN remaining.length
          (position + hypothesisLocalDomains.length))) := by
    simpa [remaining, liftedPrior, liftedHypothesisLocals, hprior,
      VExpr.liftN_wrapForalls, List.append_assoc] using Hinstalled₀
  have Hcanonical := E.fullForallTranslationAfter liftedPrevious
  have hlocalLength : hypothesisLocalDomains.length = E.localDomains.length :=
    hhypothesisLocalDomains.trans (hlocalArity.trans E.local_length.symm)
  have hliftedHypothesisInner :
      (liftContextPrefix remaining.length
        (prior ++ hypothesisLocalDomains).reverse).reverse =
        liftedPrior ++ liftedHypothesisLocals := by
    simpa [liftedPrior, liftedHypothesisLocals, hprior] using
      liftContextPrefix_reverse_append remaining.length prior
        hypothesisLocalDomains
  have HinstalledResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++ liftedPrior ++
          liftedHypothesisLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size j)
      (hypothesisResidual.liftN remaining.length
        (position + hypothesisLocalDomains.length)) := by
    have HinstalledResidual₀ : TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors ++
            (liftContextPrefix remaining.length
              (prior ++ hypothesisLocalDomains).reverse).reverse) [])
        ((E.frame.semantic.generated.outerAbstractedMotiveApp
          A.rule.binders).liftLooseBVars'
            E.frame.semantic.generated.localArgs.size j)
        (hypothesisResidual.liftN remaining.length
          (prior ++ hypothesisLocalDomains).length) := by
      simpa only [minorIdx, position, prior, remaining] using
        HhypothesisResidualFull
    rw [hliftedHypothesisInner, List.length_append, hprior] at HinstalledResidual₀
    simpa [List.append_assoc] using HinstalledResidual₀
  rcases A.recursiveResultResidualAfter j hj B T E liftedPrevious with
    ⟨HcanonicalResidual, HcanonicalResidualType⟩
  let originMotiveApp := Expr.app
    (mkAppN hypothesisOrigins.recInfos[O.ownerIdx]!.motive
      O.exposedType.getAppArgs[hypothesisOrigins.stats.params.size:])
    (mkAppN S.recursiveFields[j]! O.args)
  let generatedMotiveApp := Expr.app
    (mkAppN
      H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive
      E.frame.semantic.generated.exposedType.getAppArgs[stats.params.size:])
    (mkAppN A.rule.recursiveArgs[j]
      E.frame.semantic.generated.localArgs)
  let originFieldSource :=
    D.type.abstractList S.fields_bound.fvars
  let generatedFieldSource :=
    (E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
        A.rule.all_args_bound.fvars
  have horiginSourceShape : D.type =
      O.current.lctx.mkForall O.args originMotiveApp := by
    exact hdeclarationType.trans (by simpa [originMotiveApp] using O.type_eq)
  have HfieldPrefix : Expr.SameForallPrefix O.args.size
      originFieldSource generatedFieldSource := by
    have Hprefix := HlocalForallReplay originMotiveApp generatedMotiveApp
    dsimp only [originFieldSource, generatedFieldSource]
    rw [horiginSourceShape]
    simpa [originMotiveApp, generatedMotiveApp] using Hprefix
  have HoriginTelescope : Expr.ForallTelescope originFieldSource O.args.size
      (O.outerAbstractedMotiveApp S.fields_bound.fvars) := by
    have Hsource := (O.sourceTelescopeList
      (O.motiveApp_closed_of_outer S.fields_bound.fvars
        (by simpa [S.fields_bound.length_fvars, hsourceFields, Nat.add_comm] using
          HoriginMotiveClosedRaw))).abstractList S.fields_bound.fvars 0
    have hresidual :
        (originMotiveApp.abstractList
          O.arguments_bound.fvars).abstractList
            S.fields_bound.fvars O.args.size =
          O.outerAbstractedMotiveApp S.fields_bound.fvars := by
      simpa [originMotiveApp] using
        O.outerAbstractedMotiveApp_eq S.fields_bound.fvars
    have Hsource' : Expr.ForallTelescope
        (sourceType.abstractList S.fields_bound.fvars) O.args.size
        ((originMotiveApp.abstractList
          O.arguments_bound.fvars).abstractList
            S.fields_bound.fvars O.args.size) := by
      simpa [originMotiveApp] using Hsource
    rw [hresidual] at Hsource'
    simpa [originFieldSource, hdeclarationType] using Hsource'
  have HgeneratedNeutralScope :=
    E.frame.fieldAbstractedNeutralLocalForallSourceScope B
  have HgeneratedNeutralAvoidsHypotheses :
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars).FVarsIn
            (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HgeneratedNeutralScope.mono
    intro fv hparam hhypothesis
    apply hypothesisOrigins.hypotheses_outer_fresh fv
    · apply List.mem_append_left
      simpa [hhypothesisStats] using hparam
    · rw [S.hypotheses_bound.exprArrayFVarIds]
      exact hhypothesis
  have HgeneratedMotiveScope :=
    E.frame.fieldAbstractedNormalizedMotiveSourceScope
  have HoriginMotiveScope :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn fun fv =>
        fv ∈ ExprArrayFVarIds stats.params ++
          ExprArrayFVarIds (H.recInfos.map (·.motive)) := by
    rw [hmotiveAppAlignment]
    exact HgeneratedMotiveScope
  have HoriginMotiveAvoidsHypotheses :
      (O.outerAbstractedMotiveApp S.fields_bound.fvars).FVarsIn
        (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply HoriginMotiveScope.mono
    intro fv houter hhypothesis
    apply hypothesisOrigins.hypotheses_outer_fresh fv
    · simpa [hhypothesisStats, hhypothesisRecInfos] using houter
    · rw [S.hypotheses_bound.exprArrayFVarIds]
      exact hhypothesis
  have HneutralPrefix : Expr.SameForallPrefix O.args.size
      originFieldSource
      ((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars) := by
    have Hprefix := HlocalForallReplay originMotiveApp (.sort .zero)
    dsimp only [originFieldSource]
    rw [horiginSourceShape]
    simpa [originMotiveApp] using Hprefix
  have HoriginFieldAvoidsHypotheses : originFieldSource.FVarsIn
      (fun fv => fv ∉ S.hypotheses_bound.fvars) :=
    HneutralPrefix.leftFVarsIn HoriginTelescope
      HgeneratedNeutralAvoidsHypotheses HoriginMotiveAvoidsHypotheses
  have HDomainAvoidsHypotheses : D.type.FVarsIn
      (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    have Hraw := FVarsIn.of_abstractList HoriginFieldAvoidsHypotheses
    apply Hraw.mono
    intro fv hfv hhypothesis
    rcases hfv with hfield | hnotHypothesis
    · exact S.hypotheses_fields_fresh fv hhypothesis hfield
    · exact hnotHypothesis hhypothesis
  have HoriginMotiveClosed : Closed
      (O.outerAbstractedMotiveApp S.fields_bound.fvars)
      (A.rule.allArgs.size + O.args.size) := by
    simpa [hsourceFields, Nat.add_comm] using HoriginMotiveClosedRaw
  have HoriginFieldClosed : Closed originFieldSource
      A.rule.allArgs.size := by
    exact HfieldPrefix.leftClosed HoriginTelescope HgeneratedFieldClosed
      (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        HoriginMotiveClosed)
  have HDomainClosed : Closed D.type 0 := by
    apply Expr.closed_of_abstractList
      (e := D.type) (fvars := S.fields_bound.fvars) (depth := 0)
    simpa [originFieldSource, S.fields_bound.length_fvars,
      hsourceFields] using HoriginFieldClosed
  let previousHypothesisFVars := S.hypotheses_bound.fvars.take j
  have hpreviousHypothesisFVarsLength : previousHypothesisFVars.length = j := by
    simp only [previousHypothesisFVars, List.length_take]
    have hjHypothesisFVars : j < S.hypotheses_bound.fvars.length := by
      rw [S.hypotheses_bound.length_fvars, hsourceHypotheses]
      exact hj
    omega
  have HDomainAvoidsPrevious : D.type.FVarsIn
      (fun fv => fv ∉ previousHypothesisFVars) := by
    apply HDomainAvoidsHypotheses.mono
    intro fv hnotAll hprevious
    exact hnotAll (List.mem_of_mem_take hprevious)
  have hpreviousDomainAbstract :
      D.type.abstractList previousHypothesisFVars = D.type :=
    HDomainAvoidsPrevious.abstractList_eq_self HDomainClosed
  have hfieldDomainShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := D.type) (fvars := S.fields_bound.fvars)
    (depth := 0) (extra := j) HDomainClosed S.fields_nodup
  have hleftFieldNormalization :
      (D.type.abstractList previousHypothesisFVars).abstractList
          S.fields_bound.fvars j =
        originFieldSource.liftLooseBVars' 0 j := by
    rw [hpreviousDomainAbstract]
    simpa [originFieldSource] using hfieldDomainShift
  let generatedNeutralSource :=
    (E.frame.semantic.generated.current.lctx.mkForall
      E.frame.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars
  let Gselection :=
    E.frame.semantic.generated.arguments_bound.toFVarArrayIn.toCDeclArray
      E.frame.semantic.generated.current_wf
  have HgeneratedActualNeutral : Expr.SameForallPrefix
      E.frame.semantic.generated.localArgs.size
      generatedFieldSource generatedNeutralSource := by
    have Hprefix := (Gselection.sameForallPrefix
      E.frame.semantic.generated.arguments_bound.nodup
      generatedMotiveApp (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars
    simpa [generatedFieldSource, generatedNeutralSource,
      generatedMotiveApp, Gselection] using Hprefix
  have HgeneratedTelescope : Expr.ForallTelescope generatedFieldSource
      E.frame.semantic.generated.localArgs.size
      (E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.all_args_bound.fvars) := by
    have hresidual :=
      E.frame.semantic.generated.outerAbstractedMotiveApp_eq
        A.rule.all_args_bound.fvars E.frame.semantic.fieldClosed
    have hgeneratedOwnerRecInfos :
        E.frame.semantic.generated.ownerIdx < H.recInfos.size := by
      simpa [H.generated.length] using E.frame.entry_lt
    have hselectedMotive :
        (H.recInfos.map (·.motive))[
            E.frame.semantic.generated.ownerIdx]! =
          H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive := by
      rw [getElem!_pos (H.recInfos.map (·.motive))
          E.frame.semantic.generated.ownerIdx
            (by simpa using hgeneratedOwnerRecInfos),
        getElem!_pos H.recInfos E.frame.semantic.generated.ownerIdx
          hgeneratedOwnerRecInfos]
      simp
    rw [hselectedMotive] at hresidual
    rcases E.frame.motiveApplication with ⟨HproducerMotive'⟩
    have hgenClosed : Closed generatedMotiveApp := by
      have hclosed := HproducerMotive'.translation.closed
      rw [E.frame.semantic.current_context.mlctx.noBV, hselectedMotive] at hclosed
      simpa [generatedMotiveApp] using hclosed
    have Hsource :=
      E.frame.semantic.generated.arguments_bound.toFVarArrayIn.mkForall_forallTelescopeList
        E.frame.semantic.generated.current_wf generatedMotiveApp
        E.frame.semantic.generated.arguments_bound.nodup hgenClosed
    have Hsource' := Hsource.abstractList
      A.rule.all_args_bound.fvars 0
    have hresidual' :
        (generatedMotiveApp.abstractList
          E.frame.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
              E.frame.semantic.generated.localArgs.size =
          E.frame.semantic.generated.outerAbstractedMotiveApp
            A.rule.all_args_bound.fvars := by
      simpa [generatedMotiveApp] using hresidual
    simpa [generatedFieldSource, Nat.zero_add, hresidual'] using Hsource'
  have HgeneratedNeutralScope' : generatedNeutralSource.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) := by
    simpa [generatedNeutralSource] using HgeneratedNeutralScope
  have HgeneratedNeutralOuterScope : generatedNeutralSource.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (H.recInfos.map (·.motive))) := by
    exact HgeneratedNeutralScope'.mono fun fv hfv =>
      List.mem_append_left _ hfv
  have HgeneratedFieldOuterScope : generatedFieldSource.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (H.recInfos.map (·.motive))) :=
    HgeneratedActualNeutral.leftFVarsIn HgeneratedTelescope
      HgeneratedNeutralOuterScope HgeneratedMotiveScope
  let generatedOuter :=
    A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars
  let generatedPrefix := generatedOuter ++
    A.rule.minors_bound.fvars.take minorIdx
  let remainingMinorFVars := A.rule.minors_bound.fvars.drop minorIdx
  have HgeneratedFieldScope : generatedFieldSource.FVarsIn
      (fun fv => fv ∈ generatedOuter) := by
    simpa [generatedOuter, A.rule.params_bound.exprArrayFVarIds,
      A.rule.motives_bound.exprArrayFVarIds] using HgeneratedFieldOuterScope
  have HgeneratedFieldAvoidsRemaining : generatedFieldSource.FVarsIn
      (fun fv => fv ∉ remainingMinorFVars) := by
    apply HgeneratedFieldScope.mono
    intro fv houter hremaining
    have hminor : fv ∈ A.rule.minors_bound.fvars :=
      List.mem_of_mem_drop hremaining
    have hdisjoint :=
      (List.nodup_append.mp A.rule.outer_binders_nodup).2.2
    exact hdisjoint fv houter fv hminor rfl
  have hsourceParamsRule : H.params.fvars =
      A.rule.params_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.params
      A.rule.params_bound rfl
  have hsourceMotivesRule : H.bindings.motives.fvars =
      A.rule.motives_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.bindings.motives
      A.rule.motives_bound rfl
  have hsourceMinorsRule : H.bindings.flatMinors.fvars =
      A.rule.minors_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.bindings.flatMinors
      A.rule.minors_bound rfl
  have hsourceBindersRule : sourceBinders = generatedPrefix := by
    dsimp only [sourceBinders, generatedPrefix, generatedOuter]
    rw [hsourceParamsRule, hsourceMotivesRule, hsourceMinorsRule]
  have hremainingLength : remaining.length = remainingMinorFVars.length := by
    simp only [remaining, remainingMinorFVars, List.length_drop]
    rw [T.minors_length, A.rule.minors_bound.length_fvars]
  have hgeneratedPrefixNodup : generatedPrefix.Nodup := by
    have hsub : generatedPrefix <+
        generatedOuter ++ A.rule.minors_bound.fvars :=
      (List.Sublist.refl generatedOuter).append
        (List.take_sublist _ A.rule.minors_bound.fvars)
    exact A.rule.outer_binders_nodup.sublist <| by
      simpa [generatedPrefix, generatedOuter, List.append_assoc] using hsub
  have hgeneratedOuterSplit : generatedPrefix ++ remainingMinorFVars =
      generatedOuter ++ A.rule.minors_bound.fvars := by
    simp [generatedPrefix, generatedOuter, remainingMinorFVars,
      List.append_assoc]
  have hgeneratedOuterNodup :
      (generatedPrefix ++ remainingMinorFVars).Nodup := by
    rw [hgeneratedOuterSplit]
    simpa [generatedOuter, List.append_assoc] using
      A.rule.outer_binders_nodup
  have hremainingAbstract : generatedFieldSource.abstractList
      remainingMinorFVars A.rule.allArgs.size = generatedFieldSource :=
    HgeneratedFieldAvoidsRemaining.abstractList_eq_self
      HgeneratedFieldClosed
  have hprefixShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := generatedFieldSource) (fvars := generatedPrefix)
    (depth := A.rule.allArgs.size) (extra := remainingMinorFVars.length)
    HgeneratedFieldClosed hgeneratedPrefixNodup
  have hprefixAppend := Expr.abstractList_after_inner
    (e := generatedFieldSource) (outer := generatedPrefix)
    (inner := remainingMinorFVars) (k := A.rule.allArgs.size)
    hgeneratedOuterNodup
  rw [hremainingAbstract] at hprefixAppend
  have hgeneratedOuterFull :
      (generatedFieldSource.abstractList generatedPrefix
        A.rule.allArgs.size).liftLooseBVars'
          A.rule.allArgs.size remainingMinorFVars.length =
        (E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
            A.rule.binders := by
    have hcombined :
        (generatedFieldSource.abstractList generatedPrefix
          A.rule.allArgs.size).liftLooseBVars'
            A.rule.allArgs.size remainingMinorFVars.length =
          generatedFieldSource.abstractList
            (generatedPrefix ++ remainingMinorFVars)
              A.rule.allArgs.size :=
      hprefixShift.symm.trans hprefixAppend
    rw [hgeneratedOuterSplit] at hcombined
    have hclose := Expr.abstractList_after_inner
      (e := E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs generatedMotiveApp)
      (outer := generatedOuter ++ A.rule.minors_bound.fvars)
      (inner := A.rule.all_args_bound.fvars) (k := 0)
      (by simpa [generatedOuter, RecursorRuleSyntax.binders,
        List.append_assoc] using A.rule.binders_nodup)
    exact hcombined.trans <| by
      simpa [generatedFieldSource, generatedOuter,
        RecursorRuleSyntax.binders,
        A.rule.all_args_bound.length_fvars, List.append_assoc] using hclose
  have Htransformed := ((HfieldPrefix.liftLooseBVars' 0 j).abstractList
    sourceBinders position).liftLooseBVars' position remaining.length
  have hleftTransformed :
      ((originFieldSource.liftLooseBVars' 0 j).abstractList
        sourceBinders position).liftLooseBVars'
          position remaining.length =
        declarationDomain.liftLooseBVars' position remaining.length := by
    rw [← hleftFieldNormalization]
  have hrightAbstract :
      (generatedFieldSource.liftLooseBVars' 0 j).abstractList
          sourceBinders position =
        (generatedFieldSource.abstractList generatedPrefix
          A.rule.allArgs.size).liftLooseBVars' 0 j := by
    rw [hsourceBindersRule]
    have hcommute := Expr.liftLooseBVars'_abstractList_add
      (e := generatedFieldSource) (fvars := generatedPrefix)
      (start := 0) (cutoff := A.rule.allArgs.size) (amount := j)
      (by omega) hgeneratedPrefixNodup
    simpa [position, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hcommute
  have hrightTransformed :
      ((generatedFieldSource.liftLooseBVars' 0 j).abstractList
        sourceBinders position).liftLooseBVars'
          position remaining.length =
        ((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
            A.rule.binders).liftLooseBVars' 0 j := by
    rw [hrightAbstract, hremainingLength]
    have hcommute := Expr.liftLooseBVars_comm
      (generatedFieldSource.abstractList generatedPrefix
        A.rule.allArgs.size)
      remainingMinorFVars.length j A.rule.allArgs.size 0 (by omega)
    rw [← hgeneratedOuterFull]
    simpa [position, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcommute.symm
  have HwholePrefixJ : Expr.SameForallPrefix O.args.size
      (declarationDomain.liftLooseBVars' position remaining.length)
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs generatedMotiveApp).abstractList
          A.rule.binders).liftLooseBVars' 0 j) := by
    rw [← hleftTransformed, ← hrightTransformed]
    exact Htransformed
  have hpreviousLength : previous.length = j := by
    simp only [previous, List.length_take]
    rw [hhypotheses]
    omega
  have hliftedPreviousLength : liftedPrevious.length = j := by
    simp [liftedPrevious, hpreviousLength]
  have hselectedMotive :
      (H.recInfos.map (·.motive))[
          E.frame.semantic.generated.ownerIdx]! =
        H.recInfos[E.frame.semantic.generated.ownerIdx]!.motive := by
    have hgeneratedOwnerRecInfos :
        E.frame.semantic.generated.ownerIdx < H.recInfos.size := by
      simpa [H.generated.length] using E.frame.entry_lt
    rw [getElem!_pos (H.recInfos.map (·.motive))
        E.frame.semantic.generated.ownerIdx
          (by simpa using hgeneratedOwnerRecInfos),
      getElem!_pos H.recInfos E.frame.semantic.generated.ownerIdx
        hgeneratedOwnerRecInfos]
    simp
  have HwholePrefix : Expr.SameForallPrefix E.localDomains.length
      (declarationDomain.liftLooseBVars' position remaining.length)
      (((E.frame.semantic.generated.current.lctx.mkForall
        E.frame.semantic.generated.localArgs
          (Expr.app
            (mkAppN
              (H.recInfos.map (·.motive))[
                E.frame.semantic.generated.ownerIdx]!
              E.frame.semantic.generated.exposedType.getAppArgs[
                stats.params.size:])
            (mkAppN A.rule.recursiveArgs[j]
              E.frame.semantic.generated.localArgs))).abstractList
          A.rule.binders).liftLooseBVars' 0 liftedPrevious.length) := by
    simpa [generatedMotiveApp, hselectedMotive, hliftedPreviousLength,
      hlocalArity, E.local_length] using HwholePrefixJ
  let motiveApp := F.motiveApp
  let residualSource := F.residualSource
  refine ⟨{
    frame := F
    prior_split := by
      exact hliftedPriorSplit
    local_length := by
      exact hlocalLength
    hypothesis_translation := by
      exact Hinstalled
    canonical_translation := by
      change
        TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (equationDomains ++ liftedPrevious) [])
        (((E.frame.semantic.generated.current.lctx.mkForall
          E.frame.semantic.generated.localArgs motiveApp).abstractList
            A.rule.binders).liftLooseBVars' 0 liftedPrevious.length)
        (VExpr.wrapForalls liftedCanonicalLocals
          (E.resultType.liftN liftedPrevious.length
            E.localDomains.length))
      simpa [equationDomains, liftedCanonicalLocals, liftedPrevious,
        remaining, previous, motiveApp,
        RecursorInstallation.RuleAlignment.HypothesisFrame.motiveApp] using Hcanonical
    forall_prefix := by
      exact HwholePrefix
    hypothesis_residual_translation := by
      exact HinstalledResidual
    canonical_residual_translation := by
      change
        TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext
          (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) [])
        residualSource
        (E.resultType.liftN liftedPrevious.length E.localDomains.length)
      simpa [equationDomains, liftedCanonicalLocals,
      liftedPrevious, hliftedPreviousLength₀, hpreviousLength₀,
      hhypotheses, remaining, previous] using
        HcanonicalResidual
    canonical_residual_type := by
      change
        H.outVEnv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        (abstractForallContext
          (equationDomains ++ liftedPrevious ++ liftedCanonicalLocals) []).toCtx
        (E.resultType.liftN liftedPrevious.length E.localDomains.length)
      simpa [equationDomains, liftedCanonicalLocals,
      liftedPrevious, hliftedPreviousLength₀, hpreviousLength₀,
      hhypotheses, remaining, previous] using
        HcanonicalResidualType
  }⟩

end HypothesisDomainComparison

end VerifyInductive
end Lean4Lean
