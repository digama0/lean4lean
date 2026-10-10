import Lean4Lean.Verify.Inductive.Rules.RecursiveCall

/-! Typing of the recursive calls in a rule's right-hand side: the call-argument frame of
recursive indices and major, insertion of the motive/minor block, translation of the selected
recursor head (which in a mutual block may belong to another family than the rule's owner),
and typing of its application to the common parameter/motive/minor prefix and to the owner
motive's index/major suffix. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Cached call-argument frame for one recursive result.  Semantic indices
and the eta-expanded constructor field are restricted to a dependency-selected
scope and then closed through the same replayed front, so their targets
cannot come from unrelated existential telescope choices. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.cachedCallArgumentFrame
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (B : A.FieldFrame :=
      Classical.choice A.fieldFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ binding : MotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : MotiveAppliesTo
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.FVarCheckingScopeCore
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ fieldDomains localDomains narrowIndices narrowMajor
                narrowExposed,
              scope.toCtx = localDomains.reverse ++ B.fieldScope.toCtx ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              fieldDomains = B.fieldDomains ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              TrExprS H.outVEnv Us B.fieldScope
                (F.semantic.generated.current.lctx.mkForall
                  F.semantic.generated.localArgs (.sort .zero))
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              H.outVEnv.IsType Us.length B.fieldScope.toCtx
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              OnCtx
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext (fieldDomains ++ localDomains)
                    parameterDecls))
                (sourceIndices.map fun index =>
                  (index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size)
                narrowIndices ∧
              TrExprS H.outVEnv Us
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls)
                (F.semantic.generated.outerAbstractedMajor
                  A.rule.all_args_bound.fvars) narrowMajor ∧
              TrExprS H.outVEnv Us
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls)
                ((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.all_args_bound.fvars
                    F.semantic.generated.localArgs.size) narrowExposed ∧
              H.outVEnv.HasType Us.length
                (abstractForallContext (fieldDomains ++ localDomains)
                  parameterDecls).toCtx narrowMajor narrowExposed ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices ∧
              H.outVEnv.IsDefEqU Us.length
                F.semantic.current_context.mlctx.vlctx.toCtx
                F.semantic.appliedFieldTarget
                (narrowMajor.lift' Hscope.shift) := by
  exact F.cachedCoreCallArgumentFrame B

/-- The generated recursive major is the selected constructor field at its
reverse ordinal, applied to the exact call-local de Bruijn spine.  This
source identity is independent of the intervening hypotheses of the minor pass. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.outerAbstractedAppliedMajorOrdinal
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let fieldPosition := A.typing.recursivePositions[j]!
    F.semantic.generated.outerAbstractedMajor A.rule.binders =
      mkAppN
        (.bvar (F.semantic.generated.localArgs.size +
          (A.rule.allArgs.size - 1 - fieldPosition)))
        (F.semantic.generated.localIndices.map Expr.bvar).toArray := by
  dsimp only
  let fieldPosition := A.typing.recursivePositions[j]!
  have hfieldPosition : fieldPosition < A.rule.allArgs.size :=
    (A.typing.decisions.selected_at j hj).1
  have hfieldPositionFVars : fieldPosition <
      A.rule.all_args_bound.fvars.length := by
    rw [A.rule.all_args_bound.length_fvars]
    exact hfieldPosition
  rcases A.rule.all_args_bound.getElem_eq_fvar fieldPosition
      hfieldPosition with ⟨_hpositionFVars, hfieldAt⟩
  have hfieldBang : A.rule.allArgs[fieldPosition]! =
      .fvar A.rule.all_args_bound.fvars[fieldPosition] :=
    (getElem!_pos A.rule.allArgs fieldPosition hfieldPosition).trans hfieldAt
  have hselected := (A.typing.decisions.selected_at j hj).2
  let fv := A.rule.all_args_bound.fvars[fieldPosition]
  have hsource : A.rule.recursiveArgs[j] = .fvar fv := by
    rw [← getElem!_pos A.rule.recursiveArgs j hj]
    exact hselected.trans hfieldBang
  have hfield : fv ∈ A.rule.all_args_bound.fvars :=
    List.getElem_mem hfieldPositionFVars
  have hfieldRoot : fv ∈ F.originRoot.lctx.fvars :=
    F.field_mem_originRoot hfield
  have hfieldFull : fv ∈ A.rule.binders := by
    exact List.mem_append_right _ hfield
  rcases F.semantic.generated.outerAbstractedMajor_eq_bvar_of_field_eq
      hsource hfieldRoot A.rule.binders_nodup hfieldFull with
    ⟨fieldVar, _hfieldVar, hfieldSource, hmajor⟩
  have hfieldExact := Expr.abstractList_fvar_getElem
    A.rule.all_args_nodup fieldPosition hfieldPositionFVars (k := 0)
  have hnotOuter : fv ∉
      (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
        A.rule.minors_bound.fvars :=
    A.rule.all_args_outer_fresh fv hfield
  have hfieldFullExact : (Expr.fvar fv).abstractList A.rule.binders =
      .bvar (A.rule.allArgs.size - 1 - fieldPosition) := by
    unfold RecursorRuleSyntax.binders
    rw [Expr.abstractList_append,
      Expr.abstractList_fvar_of_not_mem hnotOuter]
    simpa [A.rule.all_args_bound.length_fvars] using hfieldExact
  have hfieldVarExact : fieldVar =
      A.rule.allArgs.size - 1 - fieldPosition :=
    Expr.bvar.inj (hfieldSource.symm.trans hfieldFullExact)
  have hmajor' :
      F.semantic.generated.outerAbstractedMajor A.rule.binders =
        mkAppN (.bvar (F.semantic.generated.localArgs.size + fieldVar))
          (F.semantic.generated.localIndices.map Expr.bvar).toArray := by
    simpa only [RecursorRuleSyntax.binders] using hmajor
  simpa [fieldPosition, hfieldVarExact] using hmajor'

/-- Closing the neutral call-local telescope over constructor fields leaves
only cached inductive parameters free. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.fieldAbstractedNeutralLocalForallSourceScope
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (B : A.FieldFrame) :
    ((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
      A.rule.all_args_bound.fvars).FVarsIn
        (fun fv => fv ∈ ExprArrayFVarIds stats.params) := by
  rcases F.cachedCallArgumentFrame (B := B) with
    ⟨_binding, _evidence, _scope, _Hscope, _fieldDomains, _localDomains,
      _narrowIndices, _narrowMajor, _narrowExposed, _hscopeContext,
      _hfields, _hfieldEq, _hlocal, HlocalTemplate,
      _HlocalTemplateType, _Hctx, _hlength, _Hindices,
      _Hmajor, _Hexposed, _Htyping, _HindexEq, _HmajorEq⟩
  have HsourceScope :
      (F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).FVarsIn
          (fun fv => fv ∈ A.rule.all_args_bound.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params) := by
    apply HlocalTemplate.fvarsIn.mono
    intro fv hfv
    rw [B.scope_fvars, A.parameterDecls_eq,
      H.parameterSuffix.parameterDecls_fvars] at hfv
    rcases List.mem_append.mp hfv with hfield | hparam
    · left
      have hfield' : fv ∈ A.typing.fieldsRecent.fvars :=
        List.mem_reverse.mp hfield
      rw [FVarArrayIn.fvars_eq
        A.typing.fieldsRecent.toFVarArrayAfter.toFVarArrayIn
        A.rule.all_args_bound rfl] at hfield'
      exact hfield'
    · exact Or.inr (List.mem_reverse.mp hparam)
  have Hclosed := FVarsIn.abstractList_of
    (selected := A.rule.all_args_bound.fvars) (k := 0) HsourceScope
  simpa using Hclosed


/-- Close cached parameters for the shared index/major frame.  Both argument
groups remain paired with the same dependency-selected targets, and the resulting
sources are ready for insertion of the generated motive/minor block. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.parameterClosedCallArgumentFrame
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (B : A.FieldFrame :=
      Classical.choice A.fieldFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    ∃ binding : MotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : MotiveAppliesTo
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.FVarCheckingScopeCore
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ fieldDomains localDomains narrowIndices narrowMajor
                narrowExposed,
              scope.toCtx = localDomains.reverse ++ B.fieldScope.toCtx ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              fieldDomains = B.fieldDomains ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains) [])
                (((F.semantic.generated.current.lctx.mkForall
                    F.semantic.generated.localArgs (.sort .zero)).abstractList
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars A.rule.allArgs.size)
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              H.outVEnv.IsType Us.length
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains) []).toCtx
                (VExpr.wrapForalls localDomains (.sort .zero)) ∧
              OnCtx
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) []).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext
                    (parameterDecls.toCtx.reverse ++ fieldDomains ++
                      localDomains) []))
                (sourceIndices.map fun index =>
                  (((index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size).abstractList
                        A.rule.params_bound.fvars cutoff))
                narrowIndices ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) [])
                ((F.semantic.generated.outerAbstractedMajor
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars cutoff) narrowMajor ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) [])
                (((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.all_args_bound.fvars
                    F.semantic.generated.localArgs.size).abstractList
                      A.rule.params_bound.fvars cutoff) narrowExposed ∧
              H.outVEnv.HasType Us.length
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ fieldDomains ++
                    localDomains) []).toCtx narrowMajor narrowExposed ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices ∧
              H.outVEnv.IsDefEqU Us.length
                F.semantic.current_context.mlctx.vlctx.toCtx
                F.semantic.appliedFieldTarget
                (narrowMajor.lift' Hscope.shift) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  rcases F.cachedCallArgumentFrame (B := B) with
    ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
      narrowIndices, narrowMajor, narrowExposed, hscopeContext, hfields, hfieldEq,
      hlocal, HlocalTemplate, HlocalTemplateType,
      Hctx, hlength, Hindices, Hmajor, Hexposed, Htyping,
      HindexEq, HmajorEq⟩
  have hparamsNodup : A.rule.params_bound.fvars.Nodup :=
    (List.nodup_append.mp
      (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have closeSource : ∀ {source target},
      TrExprS H.outVEnv Us
        (abstractForallContext (fieldDomains ++ localDomains)
          parameterDecls) source target →
      TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) [])
        (source.abstractList A.rule.params_bound.fvars cutoff) target := by
    intro source target Hsource
    have Hclosed := H.parameterSuffix.abstractParameters
      A.rule.params_bound hparamsNodup Hsource
    have hdomains : (fieldDomains ++ localDomains).length = cutoff := by
      simp [cutoff, hfields, hlocal, Nat.add_comm]
    rw [hdomains] at Hclosed
    simpa [parameterDecls, List.append_assoc] using Hclosed
  have closeSources : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ localDomains)
            parameterDecls)) sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []))
        (sources.map fun source =>
          source.abstractList A.rule.params_bound.fvars cutoff) targets := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | cons Hsource _ ih => exact .cons (closeSource Hsource) ih
  have HclosedIndices := closeSources Hindices
  have HclosedIndices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []))
      (sourceIndices.map fun index =>
        (((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff))
      narrowIndices := by
    simpa [List.map_map, Function.comp_def] using HclosedIndices
  have HclosedMajor := closeSource Hmajor
  have HclosedExposed := closeSource Hexposed
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
  have hfieldBase : A.typing.fieldRootContext.venv ≤ H.outVEnv := by
    rw [← A.typing.fieldRootExtension.venv_eq]
    exact hbase
  let HfieldRuntime := B.runtime.mono hfieldBase
  have HfieldTemplate := HfieldRuntime.abstractFront
    H.outVEnvWF B.scope_base HlocalTemplate
  have hfieldFVars :
      (VLCtx.fvars
        (B.fieldScope.take HfieldRuntime.frontSourceDomains.length)).reverse =
          A.rule.all_args_bound.fvars := by
    simpa [HfieldRuntime,
      checkInductiveTypes.loopType.FrontScopeEmbedding.mono] using
      B.frontFVars
  rw [hfieldFVars] at HfieldTemplate
  have hfieldFront : HfieldRuntime.frontSourceDomains = B.fieldDomains := by
    simpa [HfieldRuntime,
      checkInductiveTypes.loopType.FrontScopeEmbedding.mono] using B.front
  have HfieldTemplate' : TrExprS H.outVEnv Us
      (abstractForallContext HfieldRuntime.frontSourceDomains
        H.parameterSuffix.parameterDecls)
      ((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.all_args_bound.fvars)
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    simpa [A.parameterDecls_eq] using HfieldTemplate
  have HparameterTemplate := H.parameterSuffix.abstractParameters
    A.rule.params_bound hparamsNodup HfieldTemplate'
  rw [hfieldFront] at HparameterTemplate
  have HparameterTemplate' : TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) [])
      (((F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size)
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    rw [hfieldEq]
    simpa [parameterDecls, B.fieldDomains_length] using HparameterTemplate
  have HparameterTemplateType : H.outVEnv.IsType Us.length
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) []).toCtx
      (VExpr.wrapForalls localDomains (.sort .zero)) := by
    have Htype := HlocalTemplateType
    rw [B.fieldScope_eq] at Htype
    rw [hfieldEq]
    simpa [parameterDecls, A.parameterDecls_eq,
      List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using Htype
  have HclosedCtx : OnCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [parameterDecls, Us, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using Hctx
  have HclosedTyping : H.outVEnv.HasType Us.length
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx
      narrowMajor narrowExposed := by
    have hcontext :
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx =
        (abstractForallContext (fieldDomains ++ localDomains)
          parameterDecls).toCtx := by
      simp [parameterDecls, List.reverse_append, List.append_assoc,
        VLCtx.toCtx]
    rw [hcontext]
    exact Htyping
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    narrowIndices, narrowMajor, narrowExposed, hscopeContext, hfields, hfieldEq,
    hlocal, HparameterTemplate', HparameterTemplateType,
    HclosedCtx, hlength, HclosedIndices', HclosedMajor, HclosedExposed,
    HclosedTyping, HindexEq, HmajorEq⟩

/-- Insert motives and minors into the shared recursive-call argument frame.
The dependency-selected indices and major are lifted at one common field/local cutoff,
ready to be used as a single generated-recursor suffix. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.insertedCallArgumentFrame
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.FieldFrame :=
      Classical.choice A.fieldFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let parameterDecls := H.parameterSuffix.parameterDecls
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    let inserted := T.motives ++ T.minors
    ∃ binding : MotiveBinding F.semantic.current_context
        H.recInfos[selectedOwner]! H.elimLevel,
      ∃ evidence : MotiveAppliesTo
          F.semantic.current_context stats H.recInfos[selectedOwner]!
          binding F.semantic.generated.exposedType F.semantic.exposedTarget,
        ∃ scope,
          ∃ Hscope : checkInductiveTypes.loopType.FVarCheckingScopeCore
              H.outVEnv Us scope F.semantic.current_context.mlctx.vlctx,
            ∃ (fieldDomains localDomains liftedFront : List VExpr)
                (narrowIndices : List VExpr) (narrowMajor narrowExposed : VExpr),
              scope.toCtx = localDomains.reverse ++ B.fieldScope.toCtx ∧
              liftedFront =
                (liftContextPrefix inserted.length
                  (fieldDomains ++ localDomains).reverse).reverse ∧
              fieldDomains.length = A.rule.allArgs.size ∧
              fieldDomains = B.fieldDomains ∧
              localDomains.length = F.semantic.generated.localArgs.size ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++
                    (liftContextPrefix inserted.length
                      fieldDomains.reverse).reverse) [])
                (((((F.semantic.generated.current.lctx.mkForall
                    F.semantic.generated.localArgs (.sort .zero)).abstractList
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars A.rule.allArgs.size
                  ).liftLooseBVars' fieldDomains.length inserted.length))
                (VExpr.wrapForalls
                  ((liftContextPrefixAt inserted.length fieldDomains.length
                    localDomains.reverse).reverse) (.sort .zero)) ∧
              OnCtx
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront)
                  []).toCtx
                (H.outVEnv.IsType Us.length) ∧
              evidence.indices.length = F.telescope.indices.length ∧
              List.Forall₂
                (TrExprS H.outVEnv Us
                  (abstractForallContext
                    (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront)
                    []))
                (sourceIndices.map fun index =>
                  ((((index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.all_args_bound.fvars
                      F.semantic.generated.localArgs.size).abstractList
                        A.rule.params_bound.fvars cutoff).liftLooseBVars'
                          cutoff inserted.length))
                (narrowIndices.map fun target =>
                  target.liftN inserted.length cutoff) ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
                (((F.semantic.generated.outerAbstractedMajor
                  A.rule.all_args_bound.fvars).abstractList
                    A.rule.params_bound.fvars cutoff).liftLooseBVars'
                      cutoff inserted.length)
                (narrowMajor.liftN inserted.length cutoff) ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
                (((((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.all_args_bound.fvars
                    F.semantic.generated.localArgs.size).abstractList
                      A.rule.params_bound.fvars cutoff).liftLooseBVars'
                        cutoff inserted.length))
                (narrowExposed.liftN inserted.length cutoff) ∧
              H.outVEnv.HasType Us.length
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront)
                  []).toCtx
                (narrowMajor.liftN inserted.length cutoff)
                (narrowExposed.liftN inserted.length cutoff) ∧
              List.Forall₂
                (fun narrow full => H.outVEnv.IsDefEqU Us.length
                  F.semantic.current_context.mlctx.vlctx.toCtx
                  (narrow.lift' Hscope.shift) full)
                narrowIndices evidence.indices ∧
              H.outVEnv.IsDefEqU Us.length
                F.semantic.current_context.mlctx.vlctx.toCtx
                F.semantic.appliedFieldTarget
                (narrowMajor.lift' Hscope.shift) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  let inserted := T.motives ++ T.minors
  rcases F.parameterClosedCallArgumentFrame (B := B) with
    ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
      narrowIndices, narrowMajor, narrowExposed, hscopeContext, hfields, hfieldEq,
      hlocal, HparameterTemplate, _HparameterTemplateType,
      HclosedCtx, hlength, Hindices, Hmajor, Hexposed, Htyping,
      HindexEq, HmajorEq⟩
  let liftedFront :=
    (liftContextPrefix inserted.length
      (fieldDomains ++ localDomains).reverse).reverse
  rcases A.installedRecursorParameterContext with ⟨T₀, hparams⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparamsT, _hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparamsT] at hparams
  have HprefixCanonical := T.prefixContext H.outVEnvWF.ordered
  have HprefixCanonical' : OnCtx
      (inserted.reverse ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [inserted, Us, List.reverse_append, List.append_assoc] using
      HprefixCanonical
  have HprefixEq :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      hparams HprefixCanonical'
  have Hinserted : OnCtx
      (inserted.reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    have := (HprefixEq.symm H.outVEnvWF.ordered).isType
    simpa [inserted, parameterDecls, H.parameterDecls, Us,
      List.reverse_append, List.append_assoc] using this
  have Hrecent : OnCtx
      ((fieldDomains ++ localDomains).reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [parameterDecls, Us, List.reverse_append,
      List.append_assoc, VLCtx.toCtx] using HclosedCtx
  have HliftedCtx := Lean4Lean.OnCtx.insertAfterPrefix
    H.outVEnvWF.ordered Hrecent Hinserted
  have HequationCtx : OnCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [liftedFront, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using HliftedCtx
  have hcutoff : (fieldDomains ++ localDomains).length = cutoff := by
    simp [cutoff, hfields, hlocal, Nat.add_comm]
  have HinsertedTemplate₀ :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := parameterDecls.toCtx.reverse)
      (inner := fieldDomains)
      H.outVEnvWF.orderedStrong HparameterTemplate inserted
  have HinsertedTemplate : TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++
          (liftContextPrefix inserted.length fieldDomains.reverse).reverse) [])
      (((((F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size
        ).liftLooseBVars' fieldDomains.length inserted.length))
      (VExpr.wrapForalls
        ((liftContextPrefixAt inserted.length fieldDomains.length
          localDomains.reverse).reverse) (.sort .zero)) := by
    simpa [VExpr.liftN_wrapForalls, VExpr.liftN,
      List.append_assoc] using HinsertedTemplate₀
  have liftSource : ∀ {source target},
      TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) [])
        source target →
      TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
        (source.liftLooseBVars' cutoff inserted.length)
        (target.liftN inserted.length cutoff) := by
    intro source target Hsource
    have Hsource' : TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++
            (fieldDomains ++ localDomains)) []) source target := by
      simpa only [List.append_assoc] using Hsource
    have Hlifted :=
      Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
        (outer := parameterDecls.toCtx.reverse)
        (inner := fieldDomains ++ localDomains)
        H.outVEnvWF.orderedStrong Hsource' inserted
    simpa [liftedFront, hcutoff, List.append_assoc] using Hlifted
  have liftSources : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []))
        sources targets →
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext
            (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []))
        (sources.map fun source =>
          source.liftLooseBVars' cutoff inserted.length)
        (targets.map fun target => target.liftN inserted.length cutoff) := by
    intro sources targets Hsources
    induction Hsources with
    | nil => exact .nil
    | cons Hsource _ ih => exact .cons (liftSource Hsource) ih
  have HliftedIndices := liftSources Hindices
  have HliftedExposed := liftSource Hexposed
  have HliftedIndices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext
          (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []))
      (sourceIndices.map fun index =>
        ((((index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).abstractList
              A.rule.params_bound.fvars cutoff).liftLooseBVars'
                cutoff inserted.length))
      (narrowIndices.map fun target =>
        target.liftN inserted.length cutoff) := by
    simpa [List.map_map, Function.comp_def] using HliftedIndices
  have W : Ctx.LiftN inserted.length cutoff
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains ++ localDomains) []).toCtx
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) []).toCtx := by
    rw [← hcutoff]
    have W' := Ctx.LiftN.insertAfterPrefix
      (fieldDomains ++ localDomains).reverse inserted.reverse
      parameterDecls.toCtx
    simpa [liftedFront, Nat.add_comm, List.reverse_append, List.append_assoc,
      VLCtx.toCtx] using W'
  have HliftedTyping := Htyping.weakN H.outVEnvWF.ordered W
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    liftedFront, narrowIndices, narrowMajor, narrowExposed, hscopeContext, rfl,
    hfields, hfieldEq, hlocal, HinsertedTemplate, HequationCtx,
    hlength, HliftedIndices',
    liftSource Hmajor,
    HliftedExposed, HliftedTyping, HindexEq, HmajorEq⟩

/-- The executable recursor level-parameter list and any installed abstract
recursor selected from the mutual batch have the same arity. -/
theorem RecursorInstallation.recursorUvarsAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length =
      H.entries[owner].2.uvars := by
  let E := H.generated.entry owner howner
  have htranslated : E.info.levelParams.length =
      H.entries[owner].2.uvars := by
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal, E] using
      E.translated.1.2.1
  simpa [E.levels, H.localExtends.lparams_eq] using htranslated

/-- Rule-local specialization of `recursorUvarsAt`. -/
theorem RecursorInstallation.RuleAlignment.recursorUvars
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.RuleAlignment owner howner i hctor) :
    (AddInductive.getRecLevelParams H.elimLevel c.lparams).length =
      H.entries[owner].2.uvars := by
  exact H.recursorUvarsAt owner howner

/-- Context-polymorphic translation of any installed mutual recursor head at
its identity universe instantiation.  The owner index is supplied directly,
so recursive calls may select a family different from the equation owner. -/
theorem RecursorInstallation.installedRecursorHeadTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    TrExprS H.outVEnv Us Delta
      (.const (Lean.mkRecName indTypes[owner]!.name)
        (AddInductive.getRecLevels H.elimLevel stats.levels))
      (.const recursor.name (VLevel.params Us.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let E := H.generated.entry owner howner
  have hmem : recursor ∈ H.entries.map Prod.snd := by
    exact List.mem_map.mpr
      ⟨H.entries[owner], List.getElem_mem howner, rfl⟩
  have hlookup : H.outVEnv.constants recursor.name =
      some recursor.toVConstant := by
    apply VEnv.addConstVals_get H.installed.abstract
    exact hmem
  have hnameInfo : E.info.name = recursor.name := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal, E, recursor] using
      E.translated.2
  have hname : Lean.mkRecName indTypes[owner]!.name = recursor.name :=
    E.name.symm.trans hnameInfo
  have hlevels := R.recursorHeaders.recursorLevelsTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hlength :
      (AddInductive.getRecLevels H.elimLevel stats.levels).length =
        recursor.uvars := by
    calc
      _ = (VLevel.params Us.length).length :=
        checkPositivityStep.List.mapM_some_length hlevels
      _ = Us.length := VLevel.params_length
      _ = recursor.uvars := H.recursorUvarsAt owner howner
  rw [hname]
  exact TrExprS.const hlookup hlevels hlength

/-- The recursor head selected by a validated recursive call translates to
the installed recursor for that call's target family.  In a mutual block this
family need not be the owner of the equation currently being generated. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.headTranslation
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    TrExprS H.outVEnv Us Delta
      (.const F.semantic.generated.recursorName
        (AddInductive.getRecLevels H.elimLevel stats.levels))
      (.const recursor.name (VLevel.params Us.length)) := by
  rw [F.semantic.generated.recursorName_eq_owner]
  exact H.installedRecursorHeadTranslationAt
    F.semantic.generated.ownerIdx F.entry_lt Delta

/-- The selected recursive recursor, canonically applied to the common
parameter/motive/minor prefix of its retained telescope, is well typed and
leaves precisely its target-family index/major suffix. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.prefixTyping
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    H.outVEnv.HasType Us.length
      (F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors).reverse
      (VExpr.mkApps
        ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
          (F.telescope.params ++ F.telescope.motives ++
            F.telescope.minors).length 0)
        (bvarSpine
          (F.telescope.params ++ F.telescope.motives ++
            F.telescope.minors).length))
      (VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  have huvars := H.recursorUvarsAt selectedOwner F.entry_lt
  change Us.length = recursor.uvars at huvars
  have hrec := F.typing
  change H.outVEnv.HasType recursor.uvars []
    (.const recursor.name (VLevel.params recursor.uvars)) recursor.type at hrec
  rw [← huvars] at hrec
  exact F.telescope.prefixTyping H.outVEnvWF.ordered hrec

/-- Transport the selected mutual recursor's common-prefix application into
the current equation owner's canonical common prefix, then weaken it under
the constructor fields.  This is the typing premise required to translate a
cross-family recursive-call prefix. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.prefixTypingInEquationContext
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    H.outVEnv.HasType Us.length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      ((VExpr.mkApps
          ((VExpr.const recursor.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (bvarSpine
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0)
      ((VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result).liftN fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let ownerOuter := T.params ++ T.motives ++ T.minors
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  have Hcommon := H.installedRecursorCommonPrefixContextAt
    owner howner selectedOwner F.entry_lt T F.telescope
  have HownerCtx : OnCtx (fieldDomains.reverse ++ ownerOuter.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [ownerOuter, List.reverse_append, List.append_assoc] using Hctx
  have Hfull :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hcommon HownerCtx
  have Hselected := F.prefixTyping
  have HselectedWeak := Hselected.weakN H.outVEnvWF.ordered
    (Ctx.LiftN.zero fieldDomains.reverse)
  have Htransported := HselectedWeak.defeqDFC H.outVEnvWF.ordered
    (Hfull.symm H.outVEnvWF.ordered)
  have hparamsLength : F.telescope.params.length = T.params.length := by
    rw [F.telescope.params_length, T.params_length]
  have hmotivesLength : F.telescope.motives.length = T.motives.length := by
    rw [F.telescope.motives_length, T.motives_length]
  have hminorsLength : F.telescope.minors.length = T.minors.length := by
    rw [F.telescope.minors_length, T.minors_length]
  have houterLength :
      (F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors).length =
      (T.params ++ T.motives ++ T.minors).length := by
    simp only [List.length_append, hparamsLength, hmotivesLength,
      hminorsLength]
  rw [houterLength] at Htransported
  simpa [selectedOuter, ownerOuter, List.reverse_append,
    List.append_assoc] using Htransported

/-- The motive binder selected by a recursive call is definitionally equal
to the independently reconstructed canonical motive type for that call's
mutual-family owner.  This is stated against the frame's fixed generated
telescope, so the subsequent index/major application cannot silently switch
to another structural decomposition of the recursor type. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.ownerMotiveDomain
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ S : MotiveDecl H.recursorWF stats decl
        selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          F.telescope.params.reverse S.motiveSourceScope.toCtx ∧
      H.outVEnv.IsDefEqU Us.length
        (abstractForallContext
          (F.telescope.params ++
            F.telescope.motives.take selectedOwner) []).toCtx
        F.telescope.motives[selectedOwner]!
        (S.canonical.motiveType.liftN
          (F.telescope.motives.take selectedOwner).length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.installedOwnerMotiveDomainAt selectedOwner F.entry_lt with
    ⟨T, S, hparameters, Hdomain⟩
  rcases T.groupsResult_eq F.telescope with
    ⟨hparams, hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams] at hparameters
  rw [hparams, hmotives] at Hdomain
  exact ⟨S, hparameters, Hdomain⟩

/-- Complete dependent alignment between the selected recursor's generated
index/major suffix and the domains exposed by its selected motive binder.
Unlike the equation-owner specialization, this follows the owner recorded
by the validated recursive call and is fixed to `F.telescope`. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.ownerMotiveSuffixContextAlignment
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ S : MotiveDecl H.recursorWF stats decl
        selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          F.telescope.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
        F.telescope.motives[selectedOwner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        let outer := F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors
        let suffix := F.telescope.indices ++ F.telescope.major
        let later := F.telescope.motives.drop (selectedOwner + 1) ++
          F.telescope.minors
        let expected :=
          (liftContextPrefixAt (later.length + 1) 0
            motiveDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (suffix.reverse ++ outer.reverse)
          (expected.reverse ++ outer.reverse) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.installedOwnerMotiveTelescopeShapeForAt selectedOwner F.entry_lt
      F.telescope with
    ⟨S, hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hownerMotive :
      selectedOwner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have Hsuffix := H.ownerMotiveSuffixContextFor selectedOwner F.entry_lt
    F.telescope motiveDomains resultLevel hmotive hdomainLength
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Hsuffix⟩

/-- Insert an arbitrary well-formed inner front beneath the suffix alignment
selected by a recursive call.  This is the mutual-recursion counterpart of
`installedOwnerMotiveSuffixAlignmentUnderFields`: the owner is read from the
validated call rather than from the equation currently being generated. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.ownerMotiveSuffixAlignmentUnderFront
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (frontDomains : List VExpr)
    (hctx : OnCtx
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (liftContextPrefix frontDomains.length suffix.reverse ++
          frontDomains.reverse ++ outer.reverse)
        (liftContextPrefix frontDomains.length expected.reverse ++
          frontDomains.reverse ++ outer.reverse) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.ownerMotiveSuffixContextAlignment with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Hsuffix⟩
  let outer := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have hsuffixLength : suffix.reverse.length = expected.reverse.length := by
    have htotal := Hsuffix.length_eq
    simp [suffix, later, expected] at htotal ⊢
    omega
  have hfrontCtx : OnCtx (frontDomains.reverse ++ outer.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [outer, List.reverse_append, List.append_assoc] using hctx
  have Haligned := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered suffix.reverse expected.reverse
      frontDomains.reverse outer.reverse Hsuffix hsuffixLength hfrontCtx
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_⟩
  simpa only [outer, suffix, later, expected, List.reverse_append,
    List.append_assoc, List.length_reverse] using Haligned

/-- The motive variable selected by a recursive call, weakened beneath an
arbitrary inner front, exposes exactly the independently reconstructed
index/major domains for that selected mutual-family owner. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.ownerMotiveFrontWitnessTyping
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (frontDomains : List VExpr) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length
        (frontDomains.reverse ++ outer.reverse)
        (.bvar (frontDomains.length + later.length))
        (VExpr.wrapForalls
          ((liftContextPrefix frontDomains.length expected.reverse).reverse)
          (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases H.installedOwnerMotiveTelescopeShapeForAt selectedOwner F.entry_lt
      F.telescope with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hownerMotive : selectedOwner < F.telescope.motives.length := by
    rw [F.telescope.motives_length]
    simpa using hownerRecInfo
  let outer := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have Hmotive := F.telescope.ownerMotiveOuterBvarTyping hownerMotive
  have W : Ctx.LiftN frontDomains.length 0 outer.reverse
      (frontDomains.reverse ++ outer.reverse) := by
    exact .zero frontDomains.reverse (by simp)
  have Hweak := Hmotive.weakN H.outVEnvWF.ordered W
  rw [show F.telescope.motives[selectedOwner]'hownerMotive =
      F.telescope.motives[selectedOwner]! by
        exact (getElem!_pos F.telescope.motives selectedOwner
          hownerMotive).symm,
    hmotive] at Hweak
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive, by
    simpa [outer, later, expected, VExpr.liftN_wrapForalls,
      liftContextPrefix, VExpr.liftN_liftN, VExpr.liftN, liftVar_base,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Hweak⟩

/-- Re-close the call-selected suffix conversion as equality of function
types.  The residual stays the selected recursor's generated result; only
the dependent domains are replaced by those exposed by its owner motive. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.ownerMotiveSuffixTypeAlignmentUnderFront
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (frontDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result).liftN frontDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix frontDomains.length expected.reverse).reverse
      H.outVEnv.IsDefEqU Us.length
        (frontDomains.reverse ++
          (F.telescope.params ++ F.telescope.motives ++
            F.telescope.minors).reverse)
        ((VExpr.wrapForalls suffix F.telescope.result).liftN
          frontDomains.length 0)
        (VExpr.wrapForalls expectedDomains
          (F.telescope.result.liftN frontDomains.length suffix.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  rcases F.ownerMotiveSuffixAlignmentUnderFront frontDomains hctx with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Haligned⟩
  let outer := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let actualRecent := liftContextPrefix frontDomains.length suffix.reverse
  let expectedRecent :=
    liftContextPrefix frontDomains.length expected.reverse
  let base := frontDomains.reverse ++ outer.reverse
  have Haligned' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (actualRecent ++ base) (expectedRecent ++ base) := by
    simpa [Us, actualRecent, expectedRecent, base, outer, suffix, later,
      expected] using Haligned
  have HprefixType := Hprefix.isType H.outVEnvWF hctx
  rw [VExpr.liftN_wrapForalls] at HprefixType
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    (ctx := base) (domains := actualRecent.reverse)
    (result := F.telescope.result.liftN frontDomains.length suffix.length)
    (by simpa [base, outer] using hctx) (by
      simpa [actualRecent, suffix, base, outer, liftContextPrefix,
        Nat.add_comm] using HprefixType)
  rcases Hopened.2 with ⟨bodyLevel, Hbody⟩
  have Hbody' : H.outVEnv.HasType Us.length
      (actualRecent ++ base)
      (F.telescope.result.liftN frontDomains.length suffix.length)
      (.sort bodyLevel) := by
    simpa [actualRecent, base, outer, suffix] using Hbody
  have hrecentLength : expectedRecent.length = actualRecent.length := by
    have hlength := Haligned'.length_eq
    simp only [List.length_append] at hlength
    omega
  have Hclosed := VEnv.IsDefEqCtx.closeHeads Haligned'
    actualRecent.length (by simp [actualRecent, suffix]) Hbody'
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  have Hclosed' : H.outVEnv.IsDefEq Us.length base
      (VExpr.wrapForalls actualRecent.reverse
        (F.telescope.result.liftN frontDomains.length suffix.length))
      (VExpr.wrapForalls expectedRecent.reverse
        (F.telescope.result.liftN frontDomains.length suffix.length))
      (.sort closedLevel) := by
    have hrightTake : (expectedRecent ++ base).take actualRecent.length =
        expectedRecent := by
      rw [← hrecentLength]
      simp
    rw [List.drop_left, List.take_left, hrightTake] at Hclosed
    exact Hclosed
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_⟩
  refine ⟨.sort closedLevel, ?_⟩
  change H.outVEnv.IsDefEq Us.length base
    ((VExpr.wrapForalls suffix F.telescope.result).liftN
      frontDomains.length 0)
    (VExpr.wrapForalls expectedRecent.reverse
      (F.telescope.result.liftN frontDomains.length suffix.length))
    (.sort closedLevel)
  rw [VExpr.liftN_wrapForalls]
  simpa [actualRecent, base, outer, suffix,
    liftContextPrefix, Nat.add_comm] using Hclosed'

/-- In a call-selected recursor context, the common prefix and selected
owner motive take literally the same dependent index/major telescope.
This is the application-facing mutual analogue of
`installedCachedPrefixOwnerTelescope`; context transport to the equation owner's
cached parameters is deliberately left to the caller. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.prefixOwnerTelescopeUnderFront
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (frontDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((F.telescope.params ++ F.telescope.motives ++
          F.telescope.minors) ++ frontDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls
        (F.telescope.indices ++ F.telescope.major)
        F.telescope.result).liftN frontDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let selectedOuter := F.telescope.params ++ F.telescope.motives ++
      F.telescope.minors
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix frontDomains.length expected.reverse).reverse
      H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length)) ∧
        H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ selectedOuter.reverse)
          (.bvar (frontDomains.length + later.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) ∧
        SameTelescopeDomains expectedDomains.length
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  rcases F.ownerMotiveSuffixTypeAlignmentUnderFront
      frontDomains prefixTarget hctx Hprefix with
    ⟨alignedDomains, alignedLevel, halignedLength, halignedMotive,
      Haligned⟩
  rcases F.ownerMotiveFrontWitnessTyping frontDomains with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Hmotive⟩
  have hdomains : motiveDomains = alignedDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq hdomainLength halignedLength
      (suffix := [])
    simpa using hmotive.symm.trans halignedMotive
  subst alignedDomains
  have hresultLevel : resultLevel = alignedLevel := by
    have hsort : VExpr.sort resultLevel = VExpr.sort alignedLevel := by
      apply VExpr.wrapForalls_left_cancel motiveDomains
      exact hmotive.symm.trans halignedMotive
    exact VExpr.sort.inj hsort
  subst alignedLevel
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix frontDomains.length expected.reverse).reverse
  have hctx' : OnCtx (frontDomains.reverse ++ selectedOuter.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [selectedOuter, List.reverse_append, List.append_assoc] using hctx
  have Hprefix' : H.outVEnv.HasType Us.length
      (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
      ((VExpr.wrapForalls suffix F.telescope.result).liftN
        frontDomains.length 0) := by
    simpa [selectedOuter, suffix, List.reverse_append,
      List.append_assoc] using Hprefix
  have HprefixExpected : H.outVEnv.HasType Us.length
      (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
      (VExpr.wrapForalls expectedDomains
        (F.telescope.result.liftN frontDomains.length suffix.length)) := by
    exact Hprefix'.defeqU_r H.outVEnvWF hctx' (by
      simpa [selectedOuter, suffix, later, expected, expectedDomains,
        List.reverse_append, List.append_assoc] using Haligned)
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
    HprefixExpected, ?_, ?_⟩
  · simpa [selectedOuter, suffix, later, expected, expectedDomains,
      List.reverse_append, List.append_assoc] using Hmotive
  · exact SameTelescopeDomains.wrapForalls expectedDomains _ _

/-- Transport the call-selected prefix/motive telescope to an independently
cached outer context.  Context conversion preserves the exact prefix term,
selected motive de Bruijn variable, and shared dependent domains. -/
theorem
    RecursorInstallation.RuleAlignment.RecursiveCallFrame.cachedPrefixOwnerTelescopeUnderFront
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
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (frontDomains cachedBase : List VExpr) (prefixTarget : VExpr)
    (Hfull :
      let selectedOuter := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        (frontDomains.reverse ++ selectedOuter.reverse)
        (frontDomains.reverse ++ cachedBase))
    (HprefixSelected :
      let selectedOuter := F.telescope.params ++ F.telescope.motives ++
        F.telescope.minors
      H.outVEnv.HasType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        (frontDomains.reverse ++ selectedOuter.reverse) prefixTarget
        ((VExpr.wrapForalls
          (F.telescope.indices ++ F.telescope.major)
          F.telescope.result).liftN frontDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[selectedOwner]!.indices.size + 1 ∧
      F.telescope.motives[selectedOwner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := F.telescope.indices ++ F.telescope.major
      let later := F.telescope.motives.drop (selectedOwner + 1) ++
        F.telescope.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix frontDomains.length expected.reverse).reverse
      H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ cachedBase) prefixTarget
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length)) ∧
        H.outVEnv.HasType Us.length
          (frontDomains.reverse ++ cachedBase)
          (.bvar (frontDomains.length + later.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) ∧
        SameTelescopeDomains expectedDomains.length
          (VExpr.wrapForalls expectedDomains
            (F.telescope.result.liftN frontDomains.length suffix.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  have HselectedCtx : OnCtx
      (frontDomains.reverse ++ selectedOuter.reverse)
      (H.outVEnv.IsType Us.length) := Hfull.isType
  rcases F.prefixOwnerTelescopeUnderFront frontDomains prefixTarget
      (by simpa [selectedOuter, List.reverse_append,
        List.append_assoc] using HselectedCtx)
      (by simpa [selectedOuter] using HprefixSelected) with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
      HprefixExpected, HownerExpected, Hsame⟩
  let suffix := F.telescope.indices ++ F.telescope.major
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix frontDomains.length expected.reverse).reverse
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_, ?_, Hsame⟩
  · exact HprefixExpected.defeqDFC H.outVEnvWF.ordered Hfull
  · exact HownerExpected.defeqDFC H.outVEnvWF.ordered Hfull

/-- The concrete constructor constant at the head of the generated major
premise translates under recursor universes to the installed abstract
constructor at the declaration-level universe instantiation. -/
theorem
    RecursorInstallation.RuleAlignment.installedConstructorHeadTranslation
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
    (Delta : VLCtx) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let sourceCtor :=
      (indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt
    TrExprS H.outVEnv Us Delta
      (.const sourceCtor.name stats.levels)
      (.const sourceCtor.name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let sourceCtor :=
    (indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt
  let ctorVal :=
    (decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt
  have hctorMem : ctorVal ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[owner]'A.abstractOwner_lt,
      List.getElem_mem A.abstractOwner_lt,
      List.getElem_mem A.abstractCtor_lt⟩
  have hlookupBase : R.context.venv.constants ctorVal.name =
      some ctorVal.toVConstant := by
    apply R.ctorLE.constants
    exact VEnv.addConstVals_get R.core.ctorsAdded hctorMem
  have hlookup : H.outVEnv.constants ctorVal.name =
      some ctorVal.toVConstant :=
    H.constructorVEnv_le.constants hlookupBase
  have hlevels := R.recursorHeaders.recursorLevelTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hlength : stats.levels.length = ctorVal.uvars := by
    calc
      stats.levels.length = decl.uvars := R.recursorHeaders.levels
      _ = c.lparams.length := R.recursorHeaders.uvars.symm
      _ = ctorVal.uvars := A.ctorTranslation.uvars.symm
  have hname : ctorVal.name = sourceCtor.name := by
    simpa [ctorVal, sourceCtor] using A.ctorTranslation.name
  dsimp only [Us, sourceCtor, ctorVal]
  rw [← hname]
  exact TrExprS.const hlookup hlevels hlength

/-- Weaken the common recursor application below the genuine constructor
fields.  This packages it with the exact dependent equation context and the
checked constructor major already living there, so applying it to the remaining
index/major suffix cannot accidentally choose a different telescope witness. -/
theorem
    RecursorInstallation.RuleAlignment.installedRecursorPrefixEquationContextWithFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (originalDomains fieldDomains : List VExpr)
          (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.typing.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (bvarSpine A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              ((VExpr.const recursor.name
                (VLevel.params Us.length)).liftN
                (T.params ++ T.motives ++ T.minors).length 0)
              (bvarSpine
                (T.params ++ T.motives ++ T.minors).length)).liftN
            fieldDomains.length 0)
          ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
            fieldDomains.length 0) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (bvarSpine stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.installedCheckedConstructorEquationContextWithFrame with
    ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
      hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx,
      Hmajor, Htarget, HintroShape⟩
  have hrec := A.recursorTyping
  have huvars := A.recursorUvars
  change Us.length = recursor.uvars at huvars
  change H.outVEnv.HasType recursor.uvars []
    (.const recursor.name (VLevel.params recursor.uvars)) recursor.type at hrec
  rw [← huvars] at hrec
  have Hprefix := T.prefixTyping H.outVEnvWF.ordered hrec
  have Hprefix' := Hprefix.weakN H.outVEnvWF.ordered
    (Ctx.LiftN.zero fieldDomains.reverse)
  exact ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
    hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx, Hmajor, by
    simpa [List.reverse_append, List.append_assoc] using Hprefix',
    Htarget, HintroShape⟩

end VerifyInductive
end Lean4Lean
