import Lean4Lean.Verify.Inductive.Rules.RecursiveApplication

/-! `RecursorCheck.IotaEquationTranslations`, the owner-indexed batches of equations that
translate the generated rules, and the de Bruijn bookkeeping of a rule's binder abstraction:
the closed binder groups of the equation context, the constructor major, the recursor prefix,
and the recursive-call arguments after closing call-local binders. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Equation-only payload for the generated rule batches of a recursor check.
It does not ask its caller to reconstruct field selection or recursive-result
semantics: each equation is paired with the exact rule alignment
(`RuleAlignment`) of its rule. -/
inductive RecursorCheck.IotaEquationTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (Us : List Name) (Delta : VLCtx) :
    Nat → List VDefEq → Prop
  | nil : H.IotaEquationTranslations Us Delta 0 []
  | cons
      (Hprior : H.IotaEquationTranslations Us Delta owner prior)
      (howner : owner < H.entries.length)
      (batch : List VDefEq)
      (hlength : batch.length =
        (H.generated.entry owner howner).info.rules.length)
      (hroom : batch.length + prior.length ≤
        decl.ownedConstructors.length)
      (equations : ∀ i
        (hctor : i < indTypes[owner]!.ctors.length)
        (_hsource : i <
          (H.generated.entry owner howner).info.rules.length)
        (habstract : i < batch.length)
        (_hindex : prior.length + i < decl.ownedConstructors.length),
        ∃ A : H.RuleAlignment owner howner i hctor,
          Nonempty (A.rule.EquationTranslation H.outVEnv Us Delta batch[i]) ∧
          batch[i].uvars = H.entries[owner].2.uvars) :
      H.IotaEquationTranslations Us Delta (owner + 1)
        (prior ++ batch)

/-- The independently translated recursor prefix and the genuine constructor
field suffix have exactly the binder count retained by the executable rule.
This is the shared context-length invariant for all canonical equation-body
translations. -/
theorem RecursorCheck.RuleAlignment.canonicalEquationDomains_length
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    ((T.params ++ T.motives ++ T.minors) ++ fieldDomains).length =
      A.rule.binders.length := by
  have hparams : A.rule.params_bound.fvars.length = stats.params.size := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length =
      (H.recInfos.map (·.motive)).size := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length =
      (H.recInfos.flatMap (·.minors)).size := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    simpa using h.symm
  have hallArgs : A.rule.all_args_bound.fvars.length =
      A.rule.allArgs.size := by
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  unfold RecursorRuleSyntax.binders
  simp only [List.length_append]
  rw [T.params_length, T.motives_length, T.minors_length,
    hfields, hparams, hmotives, hminors, hallArgs]

/-- Replacing the executable parameter domains by the independently checked
cached parameter declarations preserves the exact executable binder count.
This is the length invariant used by the generator's equation. -/
theorem
    RecursorCheck.RuleAlignment.cachedEquationDomains_length
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains).length = A.rule.binders.length := by
  let parameterSuffix :=
    R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible
  let parameterDecls := parameterSuffix.parameterDecls
  have hparameterDeclsLength : parameterDecls.toCtx.length =
      stats.params.size := by
    have hcached := parameterSuffix.cached
    have htoCtx :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        hcached
    calc
      parameterDecls.toCtx.length = parameterDecls.length := by
        simpa [parameterDecls, parameterSuffix] using htoCtx
      _ = stats.params.size := by
        simpa [parameterDecls, parameterSuffix] using
          parameterSuffix.parameterDecls_length
  have hcanonical := A.canonicalEquationDomains_length T fieldDomains hfields
  have hparameterDeclsLength' :
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx.length =
          stats.params.size := by
    simpa [parameterDecls, parameterSuffix] using hparameterDeclsLength
  dsimp only
  simp only [List.length_append, List.length_reverse]
  rw [hparameterDeclsLength']
  simpa only [List.length_append, T.params_length] using hcanonical

/-- Every retained source-binder group has its exact canonical de Bruijn
translation in the independently typed equation context.  Keeping the four
groups separate mirrors the two generated equation spines: the recursor uses
parameters, motives, and minors, while the constructor uses parameters and
fields. -/
theorem
    RecursorCheck.RuleAlignment.equationBinderTranslations
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        ((stats.params.map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin stats.params.size =>
          VExpr.bvar (A.rule.binders.length - 1 - i)) ∧
      List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        (((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin (H.recInfos.map (·.motive)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            (A.rule.params_bound.fvars.length + i))) ∧
      List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        (((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin (H.recInfos.flatMap (·.minors)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            ((A.rule.params_bound.fvars ++
              A.rule.motives_bound.fvars).length + i))) ∧
      List.Forall₂
        (TrExprS H.outVEnv Us (abstractForallContext domains []))
        ((A.rule.allArgs.map fun arg =>
          arg.abstractList A.rule.binders).toList)
        (List.ofFn fun i : Fin A.rule.allArgs.size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            (((A.rule.params_bound.fvars ++
              A.rule.motives_bound.fvars) ++
              A.rule.minors_bound.fvars).length + i))) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  exact ⟨A.rule.abstractedParamsTranslation domains [] hdomains,
    A.rule.abstractedMotivesTranslation domains [] hdomains,
    A.rule.abstractedMinorsTranslation domains [] hdomains,
    A.rule.abstractedAllArgsTranslation domains [] hdomains⟩

/-- The owner motive selected from the globally abstracted motive array has
the same de Bruijn index as the owner-motive witness obtained by weakening
the generated telescope beneath minors and constructor fields. -/
theorem
    RecursorCheck.RuleAlignment.ownerMotiveBvarIndex
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    A.rule.binders.length - 1 -
        (A.rule.params_bound.fvars.length + owner) =
      fieldDomains.length +
        (T.motives.drop (owner + 1) ++ T.minors).length := by
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hownerRecInfo
  have hownerMotiveCount :
      owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have hparams := A.rule.params_bound.length_fvars
  have hmotives := A.rule.motives_bound.length_fvars
  have hminors := A.rule.minors_bound.length_fvars
  have hallArgs := A.rule.all_args_bound.length_fvars
  unfold RecursorRuleSyntax.binders
  simp only [List.length_append, List.length_drop]
  rw [hparams, hmotives, hminors, hallArgs, hfields,
    T.motives_length, T.minors_length]
  rw [Nat.sub_sub]
  omega

/-- In the canonical equation context, the retained constructor fields close
to precisely the innermost canonical variables.  This identifies the direct
source translation with the field application typed by the framed equation
context construction. -/
theorem
    RecursorCheck.RuleAlignment.allArgsTranslation
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext domains []))
      ((A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders).toList)
      (bvarSpine fieldDomains.length) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  have Htr := A.rule.abstractedAllArgsTranslation
    (env := H.outVEnv) (Us := Us) domains [] hdomains
  have hparams : A.rule.params_bound.fvars.length = T.params.length := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    rw [T.params_length]
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length = T.motives.length := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    rw [T.motives_length]
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length = T.minors.length := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    rw [T.minors_length]
    simpa using h.symm
  have htarget :
      (List.ofFn fun i : Fin A.rule.allArgs.size =>
        VExpr.bvar (A.rule.binders.length - 1 -
          (((A.rule.params_bound.fvars ++
            A.rule.motives_bound.fvars) ++
            A.rule.minors_bound.fvars).length + i))) =
        bvarSpine fieldDomains.length := by
    rw [bvarSpine_eq_ofFn]
    apply List.ext_getElem
    · simpa using hfields.symm
    · intro j hleft hright
      simp only [List.getElem_ofFn]
      congr 1
      simp only [List.length_append] at hdomains hparams hmotives hminors ⊢
      omega
  rw [← htarget]
  exact Htr

/-- Transport the canonical constructor-field translations through the exact
checked-to-frame equation-context conversion.  The targets remain the
literal innermost de Bruijn variables: syntax-directed uniqueness rules out
the otherwise existential targets produced by context transport. -/
theorem
    RecursorCheck.RuleAlignment.installedScopedEquationFieldTranslationsFor
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
    (B : A.FieldFrame)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let inserted := T.motives ++ T.minors
    let equationFieldDomains :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
        equationFieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext equationDomains []))
      ((A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders).toList)
      (bvarSpine equationFieldDomains.length) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  rcases A.installedCheckedScopedEquationContextAlignmentFor B T with
    ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      hcheckedEquationFields, Hcontext⟩
  have hcheckedEquationLength : checkedEquationFieldDomains.length =
      A.rule.allArgs.size := by
    simp [hcheckedEquationFields, hchecked]
  have hfieldLength : checkedEquationFieldDomains.length =
      equationFieldDomains.length := by
    simp [equationFieldDomains, hcheckedEquationFields, hchecked,
      B.fieldDomains_length]
  have Hcanonical := A.allArgsTranslation T
    checkedEquationFieldDomains hcheckedEquationLength
  let checkedEquationDomains :=
    (T.params ++ inserted) ++ checkedEquationFieldDomains
  have Hcanonical' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext checkedEquationDomains []))
      ((A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders).toList)
      (bvarSpine checkedEquationFieldDomains.length) := by
    simpa [checkedEquationDomains, inserted, List.append_assoc] using
      Hcanonical
  have HdomainContext : VEnv.IsDefEqCtx H.outVEnv Us.length []
      checkedEquationDomains.reverse equationDomains.reverse := by
    simpa [checkedEquationDomains, equationDomains, equationFieldDomains,
      inserted, List.reverse_append, List.append_assoc] using
        Hcontext
  have Hvlctx := abstractForallContext.isDefEq HdomainContext
  have HuniqueCtx := abstractForallContext.isUniqueCtx
    (by simpa using HdomainContext.length_eq)
  have transport : ∀ {sources targets},
      List.Forall₂
        (TrExprS H.outVEnv Us
          (abstractForallContext checkedEquationDomains []))
        sources targets →
      ∃ transported,
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext equationDomains []))
          sources transported := by
    intro sources targets Htranslations
    induction Htranslations with
    | nil => exact ⟨[], .nil⟩
    | cons Hhead Htail ih =>
      rcases Hhead.defeqDFC H.outVEnvWF Hvlctx with
        ⟨target, Htarget⟩
      rcases ih with ⟨targets, Htargets⟩
      exact ⟨target :: targets, .cons Htarget Htargets⟩
  have Htransported := transport Hcanonical'
  rcases Htransported with ⟨targets, Htargets⟩
  have htargets : bvarSpine checkedEquationFieldDomains.length =
      targets :=
    Lean4Lean.VerifyInductive.TrExprS.forall₂_unique HuniqueCtx
      Hcanonical' Htargets
  rw [hfieldLength] at htargets
  rw [← htargets] at Htargets
  simpa only [Us, inserted, equationFieldDomains, equationDomains] using
    Htargets

/-- The source constructor arguments close to the parameter variables shifted
below motives, minors, and fields, followed by the innermost canonical field
variables.  This is the exact spine of the independently checked constructor
major in the canonical equation context. -/
theorem
    RecursorCheck.RuleAlignment.constructorArgsTranslation
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext domains []))
      ((stats.params.map fun arg =>
          arg.abstractList A.rule.binders).toList ++
        (A.rule.allArgs.map fun arg =>
          arg.abstractList A.rule.binders).toList)
      (List.append
        ((bvarSpine T.params.length).map (fun arg =>
          arg.liftN
            ((T.motives ++ T.minors).length + fieldDomains.length) 0))
        (bvarSpine fieldDomains.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  rcases A.equationBinderTranslations T fieldDomains hfields with
    ⟨Hp, _Hm, _Hmi, _Ha⟩
  have Ha := A.allArgsTranslation T fieldDomains hfields
  have Htr := List.Forall₂.append' Hp Ha
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  have hparams : A.rule.params_bound.fvars.length = T.params.length := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    rw [T.params_length]
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length = T.motives.length := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    rw [T.motives_length]
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length = T.minors.length := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    rw [T.minors_length]
    simpa using h.symm
  have hallArgs : A.rule.all_args_bound.fvars.length = fieldDomains.length := by
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa [hfields] using h.symm
  have htarget :
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (A.rule.binders.length - 1 - i)) =
      (bvarSpine T.params.length).map (fun arg =>
        arg.liftN
          ((T.motives ++ T.minors).length + fieldDomains.length) 0) := by
    rw [bvarSpine_eq_ofFn]
    apply List.ext_getElem
    · simp [T.params_length]
    · intro j hleft hright
      simp only [List.getElem_ofFn, List.getElem_map, VExpr.liftN,
        liftVar_base']
      congr 1
      have hj : j < T.params.length := by simpa using hright
      have hbinders := hdomains.symm
      simp only [List.length_append] at hbinders
      rw [hbinders]
      have hle : 1 + j ≤ T.params.length := by omega
      rw [Nat.sub_sub, Nat.sub_sub]
      simpa [List.length_append, Nat.add_assoc] using
        (Nat.sub_add_comm (n := T.params.length)
          (m := (T.motives ++ T.minors).length + fieldDomains.length) hle)
  rw [← htarget]
  exact Htr

/-- Normal form of the checked constructor major after inserting the
motive/minor block.  Its apparent two-stage lifting is precisely the flat
constructor spine produced by translating the source parameter and field
arguments in the full equation context. -/
theorem
    RecursorCheck.RuleAlignment.constructorMajor_eq
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (introTarget : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (HintroShape : introTarget = VExpr.mkApps
      (.const
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible))
      (bvarSpine stats.params.size)) :
    VExpr.mkApps
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          (recursorDeclarationAbstractLevels c.lparams
            H.elimLevelAdmissible))
        (List.append
          ((bvarSpine T.params.length).map (fun arg =>
            arg.liftN
              ((T.motives ++ T.minors).length + fieldDomains.length) 0))
          (bvarSpine fieldDomains.length)) =
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (bvarSpine A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  have hcanonicalVars :
      bvarSpine stats.params.size =
        bvarSpine T.params.length := by
    exact congrArg bvarSpine T.params_length.symm
  rw [HintroShape, hcanonicalVars, ← hfields]
  simp only [VExpr.liftN_mkApps, VExpr.liftN,
    bvarSpine_liftN_at_length]
  rw [bvarSpine_liftN_comp]
  simp [VExpr.mkApps, List.foldl_append, Nat.add_comm]

/-- Translate the concrete constructor major in the generated equation to
the exact checked abstract major retained by the constructor phase. -/
theorem
    RecursorCheck.RuleAlignment.constructorMajorResidualTranslation
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult introTarget : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hmajor : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (bvarSpine A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size)
      (fieldResult.liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size))
    (HintroShape : introTarget = VExpr.mkApps
      (.const
        ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
        (recursorDeclarationAbstractLevels c.lparams
          H.elimLevelAdmissible))
      (bvarSpine stats.params.size)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext domains [])
      (mkAppN
        (mkAppN
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            stats.levels)
          (stats.params.map fun arg =>
            arg.abstractList A.rule.binders))
        (A.rule.allArgs.map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (bvarSpine A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  let directMajor := VExpr.mkApps
    (.const
      ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
      (recursorDeclarationAbstractLevels c.lparams
        H.elimLevelAdmissible))
    (List.append
      ((bvarSpine T.params.length).map (fun arg =>
        arg.liftN
          ((T.motives ++ T.minors).length + fieldDomains.length) 0))
      (bvarSpine fieldDomains.length))
  have hmajorShape : directMajor =
      ((VExpr.mkApps
          (introTarget.liftN A.rule.allArgs.size 0)
          (bvarSpine A.rule.allArgs.size)).liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
    exact A.constructorMajor_eq T fieldDomains introTarget
      hfields HintroShape
  have Hhead := A.installedConstructorHeadTranslation
    (abstractForallContext domains [])
  have Hargs := A.constructorArgsTranslation
    T fieldDomains hfields
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have htoCtxReverse : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)).reverse =
        types.reverse := by
    intro types
    rw [← List.map_reverse]
    exact htoCtx types.reverse
  have Hctx' : OnCtx (abstractForallContext domains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains] using Hctx
  have Hwf : VExpr.WF H.outVEnv Us.length
      (abstractForallContext domains []).toCtx directMajor := by
    rw [hmajorShape]
    refine ⟨fieldResult.liftN
      (T.motives ++ T.minors).length A.rule.allArgs.size, ?_⟩
    change H.outVEnv.IsDefEq Us.length
      (abstractForallContext domains []).toCtx _ _ _
    change H.outVEnv.IsDefEq Us.length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      _ _ _ at Hmajor
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains]
      using Hmajor
  have Htr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx' Hhead Hargs Hwf
  change TrExprS H.outVEnv Us (abstractForallContext domains []) _
    directMajor at Htr
  rw [hmajorShape] at Htr
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append, directMajor,
    domains, List.append_assoc]
    using Htr

/-- The retained parameter, motive, and minor groups close to the canonical
recursor-prefix variables, shifted below the genuine field telescope.  This
is the exact argument list appearing in the weakened prefix typing theorem. -/
theorem
    RecursorCheck.RuleAlignment.recursorPrefixTranslation
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext domains []))
      (((stats.params.map fun arg =>
          arg.abstractList A.rule.binders).toList ++
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders).toList) ++
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders).toList)
      ((bvarSpine
        (T.params ++ T.motives ++ T.minors).length).map fun arg =>
          arg.liftN fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have hdomains := A.canonicalEquationDomains_length T fieldDomains hfields
  rcases A.equationBinderTranslations T fieldDomains hfields with
    ⟨Hp, Hm, Hmi, _Ha⟩
  have Htr := List.Forall₂.append' (List.Forall₂.append' Hp Hm) Hmi
  have hparams : A.rule.params_bound.fvars.length = T.params.length := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    rw [T.params_length]
    simpa using h.symm
  have hmotives : A.rule.motives_bound.fvars.length = T.motives.length := by
    have h := congrArg Array.size A.rule.motives_bound.expressions
    rw [T.motives_length]
    simpa using h.symm
  have hminors : A.rule.minors_bound.fvars.length = T.minors.length := by
    have h := congrArg Array.size A.rule.minors_bound.expressions
    rw [T.minors_length]
    simpa using h.symm
  have hstatsParams : stats.params.size = T.params.length :=
    T.params_length.symm
  have hstatsMotives : (H.recInfos.map (·.motive)).size = T.motives.length :=
    T.motives_length.symm
  have hstatsMinors : (H.recInfos.flatMap (·.minors)).size = T.minors.length :=
    T.minors_length.symm
  have htarget :
      (((List.ofFn fun i : Fin stats.params.size =>
          VExpr.bvar (A.rule.binders.length - 1 - i)) ++
        (List.ofFn fun i : Fin (H.recInfos.map (·.motive)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            (A.rule.params_bound.fvars.length + i)))) ++
        (List.ofFn fun i : Fin (H.recInfos.flatMap (·.minors)).size =>
          VExpr.bvar (A.rule.binders.length - 1 -
            ((A.rule.params_bound.fvars ++
              A.rule.motives_bound.fvars).length + i)))) =
        (bvarSpine
          (T.params ++ T.motives ++ T.minors).length).map fun arg =>
            arg.liftN fieldDomains.length 0 := by
    rw [bvarSpine_eq_ofFn]
    apply List.ext_getElem
    · simp only [List.length_append, List.length_ofFn, List.length_map]
      rw [T.params_length, T.motives_length, T.minors_length]
    · intro j hleft hright
      simp only [List.getElem_append, List.length_append,
        List.length_ofFn, List.getElem_ofFn, List.getElem_map,
        VExpr.liftN, liftVar_base']
      split <;> rename_i hjp
      · split <;> rename_i hjpm
        · congr 1
          simp only [List.length_append, List.length_ofFn,
            List.length_map] at hdomains hparams hmotives hminors hleft hright ⊢
          omega
        · congr 1
          simp only [List.length_append, List.length_ofFn,
            List.length_map] at hdomains hparams hmotives hminors hleft hright ⊢
          omega
      · congr 1
        simp only [List.length_append, List.length_ofFn,
          List.length_map] at hdomains hparams hmotives hminors hleft hright ⊢
        omega
  rw [← htarget]
  exact Htr

/-- Assemble the translated recursor head and the three translated outer
binder groups into the exact weakened canonical prefix application.  The
independently established typing derivation supplies every application
premise required by `TrExprS`. -/
theorem
    RecursorCheck.RuleAlignment.recursorPrefixResidualTranslation
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
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      ((VExpr.mkApps
          ((VExpr.const H.entries[owner].2.name
            (VLevel.params
              (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (bvarSpine
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0)
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext domains [])
      (mkAppN
        (mkAppN
          (mkAppN
            (.const (Lean.mkRecName indTypes[owner]!.name)
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          ((VExpr.const H.entries[owner].2.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (bvarSpine
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have Hhead := H.installedRecursorHeadTranslationAt owner howner
    (abstractForallContext domains [])
  have Hargs := A.recursorPrefixTranslation T fieldDomains hfields
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have htoCtxReverse : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)).reverse =
        types.reverse := by
    intro types
    rw [← List.map_reverse]
    exact htoCtx types.reverse
  have Hctx' : OnCtx (abstractForallContext domains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains] using Hctx
  have Hwf : VExpr.WF H.outVEnv Us.length
      (abstractForallContext domains []).toCtx
      (VExpr.mkApps
        (.const H.entries[owner].2.name (VLevel.params Us.length))
        ((bvarSpine
          (T.params ++ T.motives ++ T.minors).length).map fun arg =>
            arg.liftN fieldDomains.length 0)) := by
    exact ⟨_, by
      change H.outVEnv.HasType Us.length
        (abstractForallContext domains []).toCtx
        (VExpr.mkApps
          (.const H.entries[owner].2.name (VLevel.params Us.length))
          ((bvarSpine
            (T.params ++ T.motives ++ T.minors).length).map fun arg =>
              arg.liftN fieldDomains.length 0)) _
      simpa [abstractForallContext, htoCtx, htoCtxReverse, domains,
        VExpr.liftN_mkApps, VExpr.liftN] using Hprefix⟩
  have Htr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx' Hhead Hargs Hwf
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append,
    VExpr.liftN_mkApps, VExpr.liftN, domains,
    List.append_assoc] using Htr

/-- Cached parameters are already present in the recursive-call root, hence
cannot collide with the call-local binders freshly introduced above it. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.parameterFVarsFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    ∀ fv ∈ A.rule.params_bound.fvars,
      fv ∉ F.semantic.generated.arguments_bound.fvars := by
  intro fv hparam
  intro hlocal
  have hsource : Expr.fvar fv ∈ stats.params.toList := by
    rw [A.rule.params_bound.expressions]
    simpa using hparam
  have go : ∀ {sources : List Expr} {targets : List VExpr},
      List.Forall₂
        (TrExprS A.typing.context.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          A.typing.context.mlctx.vlctx) sources targets →
      Expr.fvar fv ∈ sources →
      fv ∈ A.typing.context.mlctx.vlctx.fvars := by
    intro sources targets Htr
    induction Htr with
    | nil => simp
    | cons Hhead _ ih =>
      simp only [List.mem_cons]
      intro hmem
      rcases hmem with rfl | hmem
      · simpa only [FVarsIn] using Hhead.fvarsIn
      · exact ih hmem
  have hscope := go A.typing.validStats.params hsource
  have hrootScope : F.semantic.rootScope fv := by
    rw [F.root_scope]
    exact Or.inr (by
      rw [A.rule.params_bound.exprArrayFVarIds]
      exact hparam)
  have hrootContext := F.rootScope_mem_originContext hrootScope
  have hroot : fv ∈ F.originRoot.lctx.fvars := by
    rw [← F.originContext.lctx_eq,
      F.originContext.mlctx_wf.tr.fvars_eq]
    exact hrootContext
  exact F.semantic.generated.arguments_bound.fresh fv hlocal hroot

/-- The common parameter/motive/minor part of a generated recursive call,
after closing its call-local arguments and then the surrounding rule binders,
is exactly the canonical equation prefix weakened below the local lambdas. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.rawRecursorPrefixClosed
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    Closed (mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          stats.params)
        (H.recInfos.map (·.motive)))
      (H.recInfos.flatMap (·.minors))) := by
  have mkAppNClosed : ∀ (head : Expr) (args : Array Expr),
      Closed head → (∀ arg ∈ args, Closed arg) →
      Closed (mkAppN head args) := by
    intro head args hhead hargs
    unfold mkAppN
    rw [← Array.foldl_toList]
    have go : ∀ (xs : List Expr) (acc : Expr),
        Closed acc → (∀ arg ∈ xs, Closed arg) →
        Closed (xs.foldl Expr.app acc) := by
      intro xs
      induction xs with
      | nil => simp
      | cons first rest ih =>
        intro acc hacc hall
        simp only [List.foldl_cons]
        apply ih (.app acc first)
        · exact ⟨hacc, hall first (by simp)⟩
        · intro arg harg
          exact hall arg (by simp [harg])
    exact go args.toList head hhead (by
      intro arg harg
      exact hargs arg (by simpa using harg))
  have boundClosed : ∀ {root xs} (B : FVarArrayIn root xs),
      ∀ arg ∈ xs, Closed arg := by
    intro root xs B arg harg
    rw [B.expressions] at harg
    simp at harg
    rcases harg with ⟨fv, _hfv, rfl⟩
    trivial
  apply mkAppNClosed
  · apply mkAppNClosed
    · apply mkAppNClosed
      · trivial
      · exact boundClosed A.rule.params_bound
    · exact boundClosed A.rule.motives_bound
  · exact boundClosed A.rule.minors_bound

/-- The instantiated call template has the raw recursor prefix followed by
the locally abstracted recursive indices.  Closing rule binders distributes
structurally over that exact spine. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.outerAbstractedRecursor_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let sourceIndices := Std.Slice.toList
      (F.semantic.generated.exposedType.getAppArgs.toSubarray
        stats.params.size)
    let localPrefix := mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          stats.params)
        (H.recInfos.map (·.motive)))
      (H.recInfos.flatMap (·.minors))
    F.semantic.generated.outerAbstractedRecursor A.rule.binders =
      Expr.mkAppList
        (localPrefix.abstractList A.rule.binders
          F.semantic.generated.localArgs.size)
        (sourceIndices.map fun index =>
          (index.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.binders F.semantic.generated.localArgs.size) := by
  dsimp only
  unfold RecursiveCall.outerAbstractedRecursor
  rw [TypedRecursiveCall.abstractedRecursor_eq
    F.originContext F.semantic]
  have hclosed := F.rawRecursorPrefixClosed
  rw [Expr.liftLooseBVars_eq_self hclosed.looseBVarRange_le]
  rw [Expr.abstractList_mkAppN, Expr.mkAppN_eq_mkAppList]
  have hidx : ∀ index ∈ Std.Slice.toList
      (F.semantic.generated.exposedType.getAppArgs.toSubarray stats.params.size),
      index.abstractN F.semantic.generated.arguments_bound.fvars =
        index.abstractList F.semantic.generated.arguments_bound.fvars := by
    intro index hmem
    have hexposedClosed : Closed F.semantic.generated.exposedType := by
      have h := F.semantic.exposed_translation.closed
      rwa [F.semantic.current_context.mlctx.noBV] at h
    have hmem' : index ∈ F.semantic.generated.exposedType.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      have hsub : index ∈ (F.semantic.generated.exposedType.getAppArgs.toSubarray
          stats.params.size).toList := hmem
      rw [Subarray.toList_eq_drop_take, Array.array_toSubarray] at hsub
      exact List.mem_of_mem_take (List.mem_of_mem_drop hsub)
    exact Expr.abstractN_eq_abstractList F.semantic.generated.arguments_bound.nodup index 0
      (hexposedClosed.getAppArgsList hmem').looseBVarRange_le
  simp [AddInductive.getIIndices, Function.comp_def]
  congr 1
  exact List.map_congr_left fun index hmem => by rw [hidx index hmem]

theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.outerAbstractedCommonPrefix_eq_lift
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let localPrefix :=
      mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            stats.params)
          (H.recInfos.map (·.motive)))
        (H.recInfos.flatMap (·.minors))
    let canonicalPrefix :=
      mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders)
    localPrefix.abstractList A.rule.binders
        F.semantic.generated.localArgs.size =
      canonicalPrefix.liftLooseBVars' 0
        F.semantic.generated.localArgs.size := by
  dsimp only
  let rawPrefix := mkAppN
    (mkAppN
      (mkAppN
        (.const F.semantic.generated.recursorName
          (AddInductive.getRecLevels H.elimLevel stats.levels))
        stats.params)
      (H.recInfos.map (·.motive)))
    (H.recInfos.flatMap (·.minors))
  have mkAppNClosed : ∀ (head : Expr) (args : Array Expr),
      Closed head → (∀ arg ∈ args, Closed arg) →
      Closed (mkAppN head args) := by
    intro head args hhead hargs
    unfold mkAppN
    rw [← Array.foldl_toList]
    have go : ∀ (xs : List Expr) (acc : Expr),
        Closed acc → (∀ arg ∈ xs, Closed arg) →
        Closed (xs.foldl Expr.app acc) := by
      intro xs
      induction xs with
      | nil => simp
      | cons first rest ih =>
        intro acc hacc hall
        simp only [List.foldl_cons]
        apply ih (.app acc first)
        · exact ⟨hacc, hall first (by simp)⟩
        · intro arg harg
          exact hall arg (by simp [harg])
    exact go args.toList head hhead (by
      intro arg harg
      exact hargs arg (by simpa using harg))
  have boundClosed : ∀ {root xs} (B : FVarArrayIn root xs),
      ∀ arg ∈ xs, Closed arg := by
    intro root xs B arg harg
    rw [B.expressions] at harg
    simp at harg
    rcases harg with ⟨fv, _hfv, rfl⟩
    trivial
  have hclosed : Closed rawPrefix := by
    apply mkAppNClosed
    · apply mkAppNClosed
      · apply mkAppNClosed
        · trivial
        · exact boundClosed A.rule.params_bound
      · exact boundClosed A.rule.motives_bound
    · exact boundClosed A.rule.minors_bound
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := rawPrefix) (fvars := A.rule.binders) (depth := 0)
    (extra := F.semantic.generated.localArgs.size)
    hclosed A.rule.binders_nodup
  simpa [rawPrefix, Expr.abstractList_mkAppN, Array.map_map,
    Function.comp_def] using hshift

/-- Closing semantic recursive indices first over constructor fields and then
over the outer parameter/motive/minor groups is exactly the executable's single
rule-binder abstraction at the call-local cutoff.  This removes all remaining
order arithmetic from the later context-transport proof. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.outerAbstractedIndexSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj) :
    let outer := (A.rule.params_bound.fvars ++
      A.rule.motives_bound.fvars) ++ A.rule.minors_bound.fvars
    let sourceIndices :=
      F.semantic.generated.exposedType.getAppArgs[stats.params.size:].toList
    ((sourceIndices.map fun index =>
        (index.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.all_args_bound.fvars
            F.semantic.generated.localArgs.size).map fun index =>
      index.abstractList outer
        (F.semantic.generated.localArgs.size +
          A.rule.all_args_bound.fvars.length)) =
    sourceIndices.map fun index =>
      (index.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size := by
  let outer := (A.rule.params_bound.fvars ++
    A.rule.motives_bound.fvars) ++ A.rule.minors_bound.fvars
  let sourceIndices :=
    F.semantic.generated.exposedType.getAppArgs[stats.params.size:].toList
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro index hindex
  have Habstract := Expr.abstractList_after_inner
    (e := index.abstractList
      F.semantic.generated.arguments_bound.fvars)
    (outer := outer) (inner := A.rule.all_args_bound.fvars)
    (k := F.semantic.generated.localArgs.size)
    (by
      simpa [outer, RecursorRuleSyntax.binders,
        List.append_assoc] using A.rule.binders_nodup)
  simpa [outer, RecursorRuleSyntax.binders,
    List.append_assoc] using Habstract

/-- The source produced by closing cached parameters and then inserting the
motive/minor block is not merely equivalent to the executable's source: it is
literally the same complete rule-binder abstraction. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.insertedIndexSources_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
      H.recInfos[owner]!.indices.size owner) :
    let sourceIndices :=
      (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    let inserted := T.motives ++ T.minors
    (sourceIndices.map fun index =>
      (((index.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.all_args_bound.fvars
          F.semantic.generated.localArgs.size).abstractList
            A.rule.params_bound.fvars cutoff).liftLooseBVars'
              cutoff inserted.length) =
    sourceIndices.map fun index =>
      (index.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size := by
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  let inserted := T.motives ++ T.minors
  let insertedFVars :=
    A.rule.motives_bound.fvars ++ A.rule.minors_bound.fvars
  let closedSources := sourceIndices.map fun index =>
    (index.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
        F.semantic.generated.localArgs.size
  rcases F.cachedCallArgumentFrame with
    ⟨_binding, _evidence, _scope, _Hscope, fieldDomains, localDomains,
      _narrowIndices, _narrowMajor, _narrowExposed, _hscopeContext,
      hfields, _hfieldEq, hlocal, _HlocalTemplate,
      _HlocalTemplateType, _Hctx, _hlength, Htranslated,
      _Hmajor, _Hexposed, _Htyping, _HindexEq, _HmajorEq⟩
  have Htranslated' : List.Forall₂
      (TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (fieldDomains ++ localDomains)
          H.parameterSuffix.parameterDecls))
      closedSources _narrowIndices := by
    simpa [closedSources, hlocal] using Htranslated
  have Hscoped := F.fieldAbstractedIndexSourcesScoped
  have houterNodup :
      (A.rule.params_bound.fvars ++ insertedFVars).Nodup := by
    simpa [insertedFVars, List.append_assoc] using
      A.rule.outer_binders_nodup
  have hparamsNodup : A.rule.params_bound.fvars.Nodup :=
    (List.nodup_append.mp houterNodup).1
  have hinsertedLength : inserted.length = insertedFVars.length := by
    simp [inserted, insertedFVars,
      T.motives_length, T.minors_length,
      A.rule.motives_bound.length_fvars,
      A.rule.minors_bound.length_fvars]
  have hcutoff : (fieldDomains ++ localDomains).length = cutoff := by
    simp [cutoff, hfields, hlocal, Nat.add_comm]
  have hparameterNoBV : H.parameterSuffix.parameterDecls.bvars = 0 := by
    have h := H.recursorWF.mlctx.noBV
    rw [H.parameterSuffix.context] at h
    change (H.parameterSuffix.ambientDecls ++
      H.parameterSuffix.parameterDecls).bvars = 0 at h
    rw [VLCtx.bvars_append] at h
    omega
  have hsourceShape : ∀ source ∈ closedSources,
      (source.abstractList A.rule.params_bound.fvars cutoff).liftLooseBVars'
          cutoff inserted.length =
        source.abstractList
          (A.rule.params_bound.fvars ++ insertedFVars) cutoff := by
    intro source hsource
    rcases Lean4Lean.List.Forall₂.forall_exists_l Htranslated'
        source hsource with
      ⟨target, _htarget, Hsource⟩
    have hclosed : Closed source cutoff := by
      have h := Hsource.closed
      rw [abstractForallContext_bvars,
        hparameterNoBV, Nat.add_zero, hcutoff] at h
      exact h
    have hscope : source.FVarsIn
        (· ∈ A.rule.params_bound.fvars) := by
      have hsourceOriginal : source ∈
          sourceIndices.map fun index =>
            (index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.all_args_bound.fvars
                F.semantic.generated.localArgs.size := by
        simpa [closedSources] using hsource
      have hparams := Hscoped source hsourceOriginal
      simpa [A.rule.params_bound.exprArrayFVarIds] using hparams
    have havoids : source.FVarsIn (· ∉ insertedFVars) := by
      exact hscope.mono fun fv hparam hinserted => by
        have hdisjoint := (List.nodup_append.mp houterNodup).2.2
        exact hdisjoint fv hparam fv hinserted rfl
    have hinsertedAbstract :
        source.abstractList insertedFVars cutoff = source :=
      havoids.abstractList_eq_self hclosed
    have hshift := Expr.abstractList_add_eq_liftLooseBVars
      (e := source) (fvars := A.rule.params_bound.fvars)
      (depth := cutoff) (extra := insertedFVars.length)
      hclosed hparamsNodup
    have happend := Expr.abstractList_after_inner
      (e := source) (outer := A.rule.params_bound.fvars)
      (inner := insertedFVars) (k := cutoff) houterNodup
    rw [hinsertedAbstract] at happend
    rw [hinsertedLength]
    exact hshift.symm.trans happend
  have hfirst :
      (closedSources.map fun source =>
        (source.abstractList A.rule.params_bound.fvars cutoff).liftLooseBVars'
          cutoff inserted.length) =
      closedSources.map fun source => source.abstractList
        (A.rule.params_bound.fvars ++ insertedFVars) cutoff := by
    apply List.map_congr_left
    exact hsourceShape
  have houter := F.outerAbstractedIndexSources
  dsimp only at houter
  calc
    _ = closedSources.map fun source =>
        (source.abstractList A.rule.params_bound.fvars cutoff).liftLooseBVars'
          cutoff inserted.length := by
      simp [closedSources, sourceIndices, cutoff, inserted,
        List.map_map, Function.comp_def]
    _ = closedSources.map fun source => source.abstractList
        (A.rule.params_bound.fvars ++ insertedFVars) cutoff := hfirst
    _ = _ := by
      simpa [closedSources, sourceIndices, cutoff, insertedFVars,
        RecursorRuleSyntax.binders,
        A.rule.all_args_bound.length_fvars,
        List.append_assoc] using houter

/-- The exposed recursive-field result type obeys the same parameter closure
and motive/minor insertion equation as each of its index arguments.  Stating
the whole application separately lets later spine inversion use the executable's
two-stage abstraction directly. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.insertedExposedSource_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
      H.recInfos[owner]!.indices.size owner) :
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    let inserted := T.motives ++ T.minors
    (((((F.semantic.generated.exposedType.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
        F.semantic.generated.localArgs.size).abstractList
          A.rule.params_bound.fvars cutoff).liftLooseBVars'
            cutoff inserted.length)) =
      (F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size := by
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  let inserted := T.motives ++ T.minors
  let insertedFVars :=
    A.rule.motives_bound.fvars ++ A.rule.minors_bound.fvars
  let source :=
    (F.semantic.generated.exposedType.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.all_args_bound.fvars
        F.semantic.generated.localArgs.size
  dsimp only
  rcases F.cachedCallArgumentFrame with
    ⟨_binding, _evidence, _scope, _Hscope, fieldDomains, localDomains,
      _narrowIndices, _narrowMajor, _narrowExposed, _hfront, hfields,
      _hfieldEq, hlocal, _HlocalTemplate, _HlocalTemplateType,
      _Hctx, _hlength, _Hindices, _Hmajor, Hexposed, _Htyping,
      _HindexEq, _HmajorEq⟩
  have houterNodup :
      (A.rule.params_bound.fvars ++ insertedFVars).Nodup := by
    simpa [insertedFVars, List.append_assoc] using
      A.rule.outer_binders_nodup
  have hparamsNodup : A.rule.params_bound.fvars.Nodup :=
    (List.nodup_append.mp houterNodup).1
  have hinsertedLength : inserted.length = insertedFVars.length := by
    simp [inserted, insertedFVars,
      T.motives_length, T.minors_length,
      A.rule.motives_bound.length_fvars,
      A.rule.minors_bound.length_fvars]
  have hcutoff : (fieldDomains ++ localDomains).length = cutoff := by
    simp [cutoff, hfields, hlocal, Nat.add_comm]
  have hparameterNoBV : H.parameterSuffix.parameterDecls.bvars = 0 := by
    have h := H.recursorWF.mlctx.noBV
    rw [H.parameterSuffix.context] at h
    change (H.parameterSuffix.ambientDecls ++
      H.parameterSuffix.parameterDecls).bvars = 0 at h
    rw [VLCtx.bvars_append] at h
    omega
  have hclosed : Closed source cutoff := by
    have h := Hexposed.closed
    rw [abstractForallContext_bvars, hparameterNoBV,
      Nat.add_zero] at h
    simpa [source, cutoff, hfields, hlocal, Nat.add_comm] using h
  have hscope : source.FVarsIn (· ∈ A.rule.params_bound.fvars) := by
    have hlocalFvars : F.semantic.recent.fvars =
        F.semantic.generated.arguments_bound.fvars :=
      FVarArrayIn.fvars_eq
        F.semantic.recent.toFVarArrayAfter.toFVarArrayIn
        F.semantic.generated.arguments_bound.toFVarArrayIn rfl
    have Hlocal := FVarsIn.abstractList_of
      (selected := F.semantic.recent.fvars) (k := 0)
      F.semantic.exposed_scope
    rw [F.root_scope] at Hlocal
    have Hfield := FVarsIn.abstractList_of
      (selected := A.typing.fieldOpening.fvars)
      (k := F.semantic.generated.localArgs.size) Hlocal
    have hopenFvars : A.typing.fieldOpening.fvars =
        A.rule.all_args_bound.fvars :=
      A.typing.fieldOpening.fvars_eq_bound A.rule.all_args_bound
    simpa [source, hlocalFvars, hopenFvars,
      A.rule.params_bound.exprArrayFVarIds] using Hfield
  have havoids : source.FVarsIn (· ∉ insertedFVars) := by
    exact hscope.mono fun fv hparam hinserted => by
      have hdisjoint := (List.nodup_append.mp houterNodup).2.2
      exact hdisjoint fv hparam fv hinserted rfl
  have hinsertedAbstract :
      source.abstractList insertedFVars cutoff = source :=
    havoids.abstractList_eq_self hclosed
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := source) (fvars := A.rule.params_bound.fvars)
    (depth := cutoff) (extra := insertedFVars.length)
    hclosed hparamsNodup
  have happend := Expr.abstractList_after_inner
    (e := source) (outer := A.rule.params_bound.fvars)
      (inner := insertedFVars) (k := cutoff) houterNodup
  rw [hinsertedAbstract] at happend
  have hfirst :
      (source.abstractList A.rule.params_bound.fvars cutoff).liftLooseBVars'
          cutoff inserted.length =
        source.abstractList
          (A.rule.params_bound.fvars ++ insertedFVars) cutoff := by
    rw [hinsertedLength]
    exact hshift.symm.trans happend
  have houter := Expr.abstractList_after_inner
    (e := F.semantic.generated.exposedType.abstractList
      F.semantic.generated.arguments_bound.fvars)
    (outer := A.rule.params_bound.fvars ++ insertedFVars)
    (inner := A.rule.all_args_bound.fvars)
    (k := F.semantic.generated.localArgs.size)
    (by simpa [insertedFVars, RecursorRuleSyntax.binders,
      List.append_assoc] using A.rule.binders_nodup)
  calc
    _ = source.abstractList
        (A.rule.params_bound.fvars ++ insertedFVars) cutoff := hfirst
    _ = _ := by
      simpa [source, cutoff, insertedFVars,
        RecursorRuleSyntax.binders,
        A.rule.all_args_bound.length_fvars,
        List.append_assoc] using houter

/-- Parameter closure and motive/minor insertion leave the recursive major's
canonical field/local de Bruijn spine unchanged.  The result is exactly the
complete rule-binder abstraction emitted by the executable. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.insertedMajorSource_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
      H.recInfos[owner]!.indices.size owner) :
    let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
    let inserted := T.motives ++ T.minors
    (((F.semantic.generated.outerAbstractedMajor
      A.rule.all_args_bound.fvars).abstractList
        A.rule.params_bound.fvars cutoff).liftLooseBVars'
          cutoff inserted.length) =
      F.semantic.generated.outerAbstractedMajor A.rule.binders := by
  let cutoff := F.semantic.generated.localArgs.size + A.rule.allArgs.size
  let inserted := T.motives ++ T.minors
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
  have hfieldEq : A.rule.recursiveArgs[j] =
      .fvar A.rule.all_args_bound.fvars[fieldPosition] := by
    rw [← getElem!_pos A.rule.recursiveArgs j hj]
    exact (A.typing.decisions.selected_at j hj).2.trans hfieldBang
  have hfieldRoot : A.rule.all_args_bound.fvars[fieldPosition] ∈
      F.originRoot.lctx.fvars :=
    F.field_mem_originRoot (List.getElem_mem hfieldPositionFVars)
  have hallShape :=
    F.semantic.generated.outerAbstractedMajor_eq_bvar_at hfieldEq
      hfieldRoot A.rule.all_args_nodup hfieldPositionFVars rfl
  have hfieldMem : A.rule.all_args_bound.fvars[fieldPosition] ∈
      A.rule.all_args_bound.fvars :=
    List.getElem_mem hfieldPositionFVars
  have hfieldFull : A.rule.all_args_bound.fvars[fieldPosition] ∈
      A.rule.binders := by
    unfold RecursorRuleSyntax.binders
    exact List.mem_append_right _ hfieldMem
  rcases F.semantic.generated.outerAbstractedMajor_eq_bvar_of_field_eq
      hfieldEq hfieldRoot A.rule.binders_nodup hfieldFull with
    ⟨fullFieldVar, _hfullFieldVar, hfullFieldSource, hfullShape⟩
  have hfieldExact := Expr.abstractList_fvar_getElem
    A.rule.all_args_nodup fieldPosition hfieldPositionFVars (k := 0)
  have hnotOuter : A.rule.all_args_bound.fvars[fieldPosition] ∉
      (A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars) ++
        A.rule.minors_bound.fvars :=
    A.rule.all_args_outer_fresh _ hfieldMem
  have hfieldFullExact :
      (Expr.fvar A.rule.all_args_bound.fvars[fieldPosition]).abstractList
          A.rule.binders =
        .bvar (A.rule.allArgs.size - 1 - fieldPosition) := by
    unfold RecursorRuleSyntax.binders
    rw [Expr.abstractList_append,
      Expr.abstractList_fvar_of_not_mem hnotOuter]
    simpa [A.rule.all_args_bound.length_fvars] using hfieldExact
  have hfullFieldVar : fullFieldVar =
      A.rule.allArgs.size - 1 - fieldPosition :=
    Expr.bvar.inj (hfullFieldSource.symm.trans hfieldFullExact)
  have hfullShape' :
      F.semantic.generated.outerAbstractedMajor A.rule.binders =
        mkAppN
          (.bvar (F.semantic.generated.localArgs.size + fullFieldVar))
          (F.semantic.generated.localIndices.map Expr.bvar).toArray := by
    simpa only [RecursorRuleSyntax.binders] using hfullShape
  have hbaseFull :
      F.semantic.generated.outerAbstractedMajor
          A.rule.all_args_bound.fvars =
        F.semantic.generated.outerAbstractedMajor A.rule.binders := by
    rw [hallShape, hfullShape']
    simp [hfullFieldVar, A.rule.all_args_bound.length_fvars]
  rcases F.cachedCallArgumentFrame with
    ⟨_binding, _evidence, _scope, _Hscope,
      cachedFields, cachedLocals, _narrowIndices, _narrowMajor,
      _narrowExposed,
      _hfront, hcachedFields, _hfieldEq, hcachedLocals,
      _HlocalTemplate, _HlocalTemplateType, _Hctx, _hlength,
      _Hindices, HcachedMajor, _Hexposed, _Htyping,
      _HindexEq, _HmajorEq⟩
  have hparameterNoBV : H.parameterSuffix.parameterDecls.bvars = 0 := by
    have h := H.recursorWF.mlctx.noBV
    rw [H.parameterSuffix.context] at h
    change (H.parameterSuffix.ambientDecls ++
      H.parameterSuffix.parameterDecls).bvars = 0 at h
    rw [VLCtx.bvars_append] at h
    omega
  have hclosed : Closed
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars) cutoff := by
    have h := HcachedMajor.closed
    rw [abstractForallContext_bvars, hparameterNoBV,
      Nat.add_zero] at h
    simpa [cutoff, hcachedFields, hcachedLocals,
      Nat.add_comm] using h
  have hnoFVars :
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars).FVarsIn (fun _ => False) := by
    rw [hallShape, Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · trivial
    · intro arg harg
      have harg' : arg ∈
          F.semantic.generated.localIndices.map Expr.bvar := by
        simpa using harg
      rcases List.mem_map.mp harg' with ⟨index, _hindex, rfl⟩
      trivial
  have havoidsParams :
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars).FVarsIn
          (· ∉ A.rule.params_bound.fvars) :=
    hnoFVars.mono fun _ h => False.elim h
  have hparamAbstract :
      (F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars cutoff =
      F.semantic.generated.outerAbstractedMajor
        A.rule.all_args_bound.fvars := by
    exact havoidsParams.abstractList_eq_self hclosed
  dsimp only
  rw [hparamAbstract,
    Expr.liftLooseBVars_eq_self hclosed.looseBVarRange_le,
    hbaseFull]

/-- The neutral local-forall template carried through field closure,
parameter closure, and motive/minor insertion has exactly the executable's
single rule-binder abstraction as its source.  This is the source-side
counterpart of the lifted-domain identity retained by the inserted call
frame. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.insertedLocalForallSource_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
    let inserted := T.motives ++ T.minors
    (((((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
      A.rule.all_args_bound.fvars).abstractList
        A.rule.params_bound.fvars A.rule.allArgs.size
      ).liftLooseBVars' A.rule.allArgs.size inserted.length)) =
      (F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders := by
  let inserted := T.motives ++ T.minors
  let insertedFVars :=
    A.rule.motives_bound.fvars ++ A.rule.minors_bound.fvars
  let raw := F.semantic.generated.current.lctx.mkForall
    F.semantic.generated.localArgs (.sort .zero)
  let source := raw.abstractList A.rule.all_args_bound.fvars
  rcases F.parameterClosedCallArgumentFrame (B := B) with
    ⟨_binding, _evidence, _scope, _Hscope, fieldDomains, _localDomains,
      _narrowIndices, _narrowMajor, _narrowExposed, _hfront, hfields,
      _hfieldEq, _hlocal, HparameterTemplate, _HparameterTemplateType,
      _Hctx, _hlength, _Hindices, _Hmajor, _Hexposed, _Htyping,
      _HindexEq, _HmajorEq⟩
  have houterNodup :
      (A.rule.params_bound.fvars ++ insertedFVars).Nodup := by
    simpa [insertedFVars, List.append_assoc] using
      A.rule.outer_binders_nodup
  have hparamsNodup : A.rule.params_bound.fvars.Nodup :=
    (List.nodup_append.mp houterNodup).1
  have hinsertedLength : inserted.length = insertedFVars.length := by
    simp [inserted, insertedFVars,
      T.motives_length, T.minors_length,
      A.rule.motives_bound.length_fvars,
      A.rule.minors_bound.length_fvars]
  have hparameterLength :
      H.parameterSuffix.parameterDecls.toCtx.length =
        A.rule.params_bound.fvars.length := by
    calc
      _ = H.parameterSuffix.parameterDecls.length := by
        exact
          checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
            H.parameterSuffix.cached
      _ = stats.params.size := H.parameterSuffix.parameterDecls_length
      _ = A.rule.params_bound.fvars.length := by
        simpa using A.rule.params_bound.length_fvars.symm
  have hclosedClosed := HparameterTemplate.closed
  rw [abstractForallContext_bvars] at hclosedClosed
  have hclosedAfterParams : Closed
      (source.abstractList A.rule.params_bound.fvars A.rule.allArgs.size)
      (A.rule.allArgs.size + A.rule.params_bound.fvars.length) := by
    simpa [source, raw, hfields, hparameterLength, Nat.add_comm,
      List.append_assoc, VLCtx.bvars] using hclosedClosed
  have hclosed : Closed source A.rule.allArgs.size :=
    Expr.closed_of_abstractList hclosedAfterParams
  have hclosedFVars :
      (source.abstractList A.rule.params_bound.fvars A.rule.allArgs.size
        ).FVarsIn (fun _ => False) := by
    have h := HparameterTemplate.fvarsIn
    simpa [source, raw, VLCtx.fvars, abstractForallContext,
      List.append_assoc] using h
  have hscope : source.FVarsIn
      (fun fv => fv ∈ A.rule.params_bound.fvars) := by
    exact (FVarsIn.of_abstractList hclosedFVars).mono fun fv h => by
      rcases h with h | h
      · exact h
      · exact False.elim h
  have havoids : source.FVarsIn (· ∉ insertedFVars) := by
    exact hscope.mono fun fv hparam hinserted => by
      have hdisjoint := (List.nodup_append.mp houterNodup).2.2
      exact hdisjoint fv hparam fv hinserted rfl
  have hinsertedAbstract :
      source.abstractList insertedFVars A.rule.allArgs.size = source :=
    havoids.abstractList_eq_self hclosed
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := source) (fvars := A.rule.params_bound.fvars)
    (depth := A.rule.allArgs.size) (extra := insertedFVars.length)
    hclosed hparamsNodup
  have happend := Expr.abstractList_after_inner
    (e := source) (outer := A.rule.params_bound.fvars)
    (inner := insertedFVars) (k := A.rule.allArgs.size) houterNodup
  rw [hinsertedAbstract] at happend
  have hfirst :
      (source.abstractList A.rule.params_bound.fvars A.rule.allArgs.size
        ).liftLooseBVars' A.rule.allArgs.size inserted.length =
      source.abstractList
        (A.rule.params_bound.fvars ++ insertedFVars) A.rule.allArgs.size := by
    rw [hinsertedLength]
    exact hshift.symm.trans happend
  have houter := Expr.abstractList_after_inner
    (e := raw)
    (outer := A.rule.params_bound.fvars ++ insertedFVars)
    (inner := A.rule.all_args_bound.fvars) (k := 0)
    (by simpa [insertedFVars, RecursorRuleSyntax.binders,
      List.append_assoc] using A.rule.binders_nodup)
  dsimp only
  calc
    _ = source.abstractList
        (A.rule.params_bound.fvars ++ insertedFVars)
          A.rule.allArgs.size := by
      simpa [source, raw, inserted] using hfirst
    _ = _ := by
      simpa [source, raw, insertedFVars,
        RecursorRuleSyntax.binders,
        A.rule.all_args_bound.length_fvars,
        List.append_assoc] using houter


/-- Canonical-source form of the shared inserted call-argument frame.  This
is the application-ready handoff: the executable's exact recursive index spine
and major translate together in one typed equation context. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.canonicalInsertedCallArgumentFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
                ((F.semantic.generated.current.lctx.mkForall
                  F.semantic.generated.localArgs (.sort .zero)).abstractList
                    A.rule.binders)
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
                  (index.abstractList
                    F.semantic.generated.arguments_bound.fvars).abstractList
                      A.rule.binders F.semantic.generated.localArgs.size)
                (narrowIndices.map fun target =>
                  target.liftN inserted.length cutoff) ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
                (F.semantic.generated.outerAbstractedMajor A.rule.binders)
                (narrowMajor.liftN inserted.length cutoff) ∧
              TrExprS H.outVEnv Us
                (abstractForallContext
                  (parameterDecls.toCtx.reverse ++ inserted ++ liftedFront) [])
                ((F.semantic.generated.exposedType.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.binders F.semantic.generated.localArgs.size)
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
  let inserted := T.motives ++ T.minors
  rcases F.insertedCallArgumentFrame T (B := B) with
    ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
      liftedFront, narrowIndices, narrowMajor, narrowExposed, hfront,
      hliftedFront, hfields, hfieldEq, hlocal, HlocalTemplate,
      Hctx, hlength, Hindices, Hmajor,
      Hexposed, Htyping,
      HindexEq, HmajorEq⟩
  have hindices := F.insertedIndexSources_eq T
  dsimp only at hindices
  rw [hindices] at Hindices
  have hmajor := F.insertedMajorSource_eq T
  dsimp only at hmajor
  rw [hmajor] at Hmajor
  have hexposed := F.insertedExposedSource_eq T
  dsimp only at hexposed
  rw [hexposed] at Hexposed
  have hlocalSource := F.insertedLocalForallSource_eq T (B := B)
  dsimp only at hlocalSource
  have hlocalSource' :
      (((((F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
        A.rule.all_args_bound.fvars).abstractList
          A.rule.params_bound.fvars A.rule.allArgs.size
        ).liftLooseBVars' fieldDomains.length inserted.length)) =
        (F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
            A.rule.binders := by
    rw [hfields]
    exact hlocalSource
  rw [hlocalSource'] at HlocalTemplate
  exact ⟨binding, evidence, scope, Hscope, fieldDomains, localDomains,
    liftedFront, narrowIndices, narrowMajor, narrowExposed, hfront,
    hliftedFront, hfields, hfieldEq, hlocal, HlocalTemplate,
    Hctx, hlength, Hindices, Hmajor,
    Hexposed, Htyping,
    HindexEq, HmajorEq⟩

/-- Invert the normalized exposed recursive-field type at its selected mutual
family head.  The suffix extracted from the complete application is related
pointwise to the exact recursive-index targets retained by the call frame;
the relation is definitional equality, which is the strongest conclusion
available for arbitrary translated index expressions. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.insertedExposedSpine
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
    let inserted := T.motives ++ T.minors
    ∃ (equationDomains fieldDomains localDomains added
        frontDomains : List VExpr)
        (exactIndexTargets : List VExpr) (majorTarget exposedTarget : VExpr),
      equationDomains ++ localDomains =
          parameterDecls.toCtx.reverse ++ added ∧
        equationDomains =
          parameterDecls.toCtx.reverse ++ inserted ++ fieldDomains ∧
        added = inserted ++ frontDomains ∧
        frontDomains = fieldDomains ++ localDomains ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        equationDomains.length = A.rule.binders.length ∧
        OnCtx
          (abstractForallContext (equationDomains ++ localDomains) []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext equationDomains [])
          ((F.semantic.generated.current.lctx.mkForall
            F.semantic.generated.localArgs (.sort .zero)).abstractList
              A.rule.binders)
          (VExpr.wrapForalls localDomains (.sort .zero)) ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext (equationDomains ++ localDomains) []).toCtx
          majorTarget exposedTarget ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              (equationDomains ++ localDomains) []))
          (sourceIndices.map fun index =>
            (index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.binders F.semantic.generated.localArgs.size)
          exactIndexTargets ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMajor A.rule.binders)
          majorTarget ∧
        exactIndexTargets.length = F.telescope.indices.length ∧
        ∃ levels parameterTargets spineIndexTargets,
          exposedTarget.getAppFnArgs =
            (.const (decl.types[selectedOwner]'F.semantic.validated.target_lt).name
              levels, parameterTargets ++ spineIndexTargets) ∧
          stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext
                (equationDomains ++ localDomains) []))
            ((stats.params.map fun param =>
              (param.abstractList
                F.semantic.generated.arguments_bound.fvars).abstractList
                  A.rule.binders
                  F.semantic.generated.localArgs.size).toList)
            parameterTargets ∧
          parameterTargets =
            (List.ofFn fun i : Fin stats.params.size =>
              VExpr.bvar (A.rule.binders.length - 1 - i)).map
                (fun target => target.liftN localDomains.length 0) ∧
          List.Forall₂
            (fun spine exact => H.outVEnv.IsDefEqU Us.length
              (abstractForallContext
                (equationDomains ++ localDomains) []).toCtx spine exact)
            spineIndexTargets exactIndexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let parameterDecls := H.parameterSuffix.parameterDecls
  let inserted := T.motives ++ T.minors
  rcases F.canonicalInsertedCallArgumentFrame T (B := B) with
    ⟨_binding, _evidence, _scope, _Hscope, fieldDomains, rawLocalDomains,
      liftedFront, narrowIndices, narrowMajor, narrowExposed, _hfront,
      hliftedFront, hfields, hfieldEq, hlocal, HlocalTemplate,
      Hctx, hlength, Hindices, _Hmajor,
      Hexposed, Htyping, _HindexEq, _HmajorEq⟩
  let liftedFields :=
    (liftContextPrefix inserted.length fieldDomains.reverse).reverse
  let liftedLocals :=
    (liftContextPrefixAt inserted.length fieldDomains.length
      rawLocalDomains.reverse).reverse
  let equationDomains :=
    parameterDecls.toCtx.reverse ++ inserted ++ liftedFields
  let added := inserted ++ liftedFields ++ liftedLocals
  let frontDomains := liftedFields ++ liftedLocals
  let exactIndexTargets := narrowIndices.map fun target =>
    target.liftN inserted.length
      (F.semantic.generated.localArgs.size + A.rule.allArgs.size)
  let majorTarget := narrowMajor.liftN inserted.length
    (F.semantic.generated.localArgs.size + A.rule.allArgs.size)
  let exposedTarget := narrowExposed.liftN inserted.length
    (F.semantic.generated.localArgs.size + A.rule.allArgs.size)
  have hsplitFront : liftedFront = liftedFields ++ liftedLocals := by
    rw [hliftedFront]
    exact liftContextPrefix_reverse_append inserted.length
      fieldDomains rawLocalDomains
  have Hctx' : OnCtx
      (abstractForallContext (equationDomains ++ liftedLocals) []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, parameterDecls, inserted, hsplitFront,
      List.append_assoc] using Hctx
  have HlocalTemplate' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((F.semantic.generated.current.lctx.mkForall
        F.semantic.generated.localArgs (.sort .zero)).abstractList
          A.rule.binders)
      (VExpr.wrapForalls liftedLocals (.sort .zero)) := by
    simpa [equationDomains, parameterDecls, inserted, liftedFields,
      liftedLocals, List.append_assoc] using HlocalTemplate
  have Htyping' : H.outVEnv.HasType Us.length
      (abstractForallContext (equationDomains ++ liftedLocals) []).toCtx
      majorTarget exposedTarget := by
    simpa [equationDomains, parameterDecls, inserted, majorTarget,
      exposedTarget, hsplitFront, List.append_assoc] using Htyping
  have Hmajor' : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ liftedLocals) [])
      (F.semantic.generated.outerAbstractedMajor A.rule.binders)
      majorTarget := by
    simpa [equationDomains, parameterDecls, inserted, majorTarget,
      hsplitFront, List.append_assoc] using _Hmajor
  have hexactIndexLength : exactIndexTargets.length =
      F.telescope.indices.length := by
    simp only [exactIndexTargets, List.length_map]
    exact (List.Forall₂.length_eq
      _HindexEq).trans hlength
  have Hexposed' : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ liftedLocals) [])
      ((F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size)
      exposedTarget := by
    simpa [equationDomains, parameterDecls, inserted, exposedTarget,
      hsplitFront, List.append_assoc] using Hexposed
  have hvalid := (checkPositivityStep.isValidIndApp?_some
    F.semantic.generated.owner_valid).2
  have hconst := H.validStats.indConstAt F.semantic.validated.target_lt
  have hhead : F.semantic.generated.exposedType.getAppFn =
      .const (decl.types[selectedOwner]'F.semantic.validated.target_lt).name
        stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead hvalid hconst
  have hheadClosed :
      ((F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size).getAppFn =
      .const (decl.types[selectedOwner]'F.semantic.validated.target_lt).name
        stats.levels := by
    rw [Expr.getAppFn_abstractList
      (F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars)
      A.rule.binders F.semantic.generated.localArgs.size]
    rw [Expr.getAppFn_abstractList F.semantic.generated.exposedType
      F.semantic.generated.arguments_bound.fvars 0, hhead]
    simp [Expr.abstractList_const]
  rcases checkPositivityStep.TrExprS.constAppSpine Hexposed' hheadClosed with
    ⟨levels, translatedArgs, hspine, hlevels, Hargs⟩
  have hsourcePrefix := H.validStats.sourceParameterPrefix hvalid
  have hrawArgs : F.semantic.generated.exposedType.getAppArgsList =
      stats.params.toList ++ sourceIndices := by
    calc
      F.semantic.generated.exposedType.getAppArgsList =
          F.semantic.generated.exposedType.getAppArgsList.take
              stats.params.size ++
            F.semantic.generated.exposedType.getAppArgsList.drop
              stats.params.size :=
        (List.take_append_drop _ _).symm
      _ = stats.params.toList ++ sourceIndices := by
        rw [hsourcePrefix]
        congr 1
        have hsuffix :
            (F.semantic.generated.exposedType.getAppArgs[
              stats.params.size:]).toList =
            F.semantic.generated.exposedType.getAppArgs.toList.drop
              stats.params.size := by
          rw [List.drop_eq_drop_min]
          simp only [Subarray.toList_eq, Array.array_toSubarray,
            Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
            Array.toList_extract, List.extract_eq_take_drop,
            Array.length_toList]
          apply List.take_of_length_le
          simp
        simpa [sourceIndices, Expr.getAppArgs_toList] using hsuffix.symm
  let parameterSources := stats.params.toList.map fun param =>
    (param.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.binders F.semantic.generated.localArgs.size
  let indexSources := sourceIndices.map fun index =>
    (index.abstractList
      F.semantic.generated.arguments_bound.fvars).abstractList
        A.rule.binders F.semantic.generated.localArgs.size
  have hsourceArgs :
      ((F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders
          F.semantic.generated.localArgs.size).getAppArgsList =
        parameterSources ++ indexSources := by
    rw [Expr.getAppArgsList_abstractList
      (F.semantic.generated.exposedType.abstractList
        F.semantic.generated.arguments_bound.fvars)
      A.rule.binders F.semantic.generated.localArgs.size]
    rw [Expr.getAppArgsList_abstractList F.semantic.generated.exposedType
      F.semantic.generated.arguments_bound.fvars 0, hrawArgs]
    simp [parameterSources, indexSources, List.map_map,
      Function.comp_def]
  rw [hsourceArgs] at Hargs
  rcases checkPositivityStep.List.Forall₂.split_left Hargs with
    ⟨parameterTargets, spineIndexTargets, htranslatedArgs,
      Hparameters, HspineIndices⟩
  have HparametersOriginal := Hparameters
  have HouterParameters :=
    F.semantic.generated.outerAbstractedBoundArray_eq_lift_of_fresh
      A.rule.params_bound F.parameterFVarsFresh
      A.rule.binders_nodup
  have hparameterSources :
      ((stats.params.map fun param =>
        (param.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.binders F.semantic.generated.localArgs.size).toList) =
        (List.ofFn fun i : Fin stats.params.size =>
          Expr.bvar (A.rule.binders.length - 1 - i)).map
            (fun source => source.liftLooseBVars' 0
              F.semantic.generated.localArgs.size) := by
    have HouterParameters' := congrArg Array.toList HouterParameters
    simp only [Array.toList_map] at HouterParameters'
    have HouterParameters'' :
        ((stats.params.map fun param =>
          (param.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.binders F.semantic.generated.localArgs.size).toList) =
          ((stats.params.map fun param =>
            param.abstractList A.rule.binders).toList).map
              (fun source => source.liftLooseBVars' 0
                F.semantic.generated.localArgs.size) := by
      simpa [RecursorRuleSyntax.binders] using HouterParameters'
    exact HouterParameters''.trans (congrArg
      (List.map fun source => source.liftLooseBVars' 0
        F.semantic.generated.localArgs.size)
      A.rule.abstractedParams_eq)
  dsimp only [parameterSources] at Hparameters
  have hparameterSources' :
      (stats.params.toList.map fun param =>
        (param.abstractList
          F.semantic.generated.arguments_bound.fvars).abstractList
            A.rule.binders F.semantic.generated.localArgs.size) =
        (List.ofFn fun i : Fin stats.params.size =>
          Expr.bvar (A.rule.binders.length - 1 - i)).map
            (fun source => source.liftLooseBVars' 0
              F.semantic.generated.localArgs.size) := by
    simpa only [Array.toList_map] using hparameterSources
  rw [hparameterSources'] at Hparameters
  have hfieldsLifted : liftedFields.length = A.rule.allArgs.size := by
    simp [liftedFields, hfields]
  have hlocalsLifted : liftedLocals.length =
      F.semantic.generated.localArgs.size := by
    simp [liftedLocals, hlocal]
  have hequationLength : equationDomains.length = A.rule.binders.length := by
    have hparameterLength : parameterDecls.toCtx.length = stats.params.size := by
      calc
        parameterDecls.toCtx.length = parameterDecls.length := by
          simpa [parameterDecls] using
            checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
              H.parameterSuffix.cached
        _ = stats.params.size := by
          simpa [parameterDecls] using H.parameterSuffix.parameterDecls_length
    have hcanonical :=
      A.canonicalEquationDomains_length T liftedFields hfieldsLifted
    simp only [equationDomains, inserted, List.length_append]
    simp only [List.length_reverse]
    simp only [List.length_append] at hcanonical
    rw [hparameterLength]
    rw [T.params_length] at hcanonical
    omega
  have hparameterBound : stats.params.size ≤ A.rule.binders.length := by
    have hparams : A.rule.params_bound.fvars.length = stats.params.size := by
      have h := congrArg Array.size A.rule.params_bound.expressions
      simpa using h.symm
    unfold RecursorRuleSyntax.binders
    simp only [List.length_append]
    omega
  have hparameterTargets : parameterTargets =
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (A.rule.binders.length - 1 - i)).map
          (fun target => target.liftN liftedLocals.length 0) := by
    apply List.ext_getElem
    · simpa using
        (List.Forall₂.length_eq Hparameters).symm
    · intro k htarget hcanonical
      have hsource : k <
          ((List.ofFn fun i : Fin stats.params.size =>
            Expr.bvar (A.rule.binders.length - 1 - i)).map
              (fun source => source.liftLooseBVars' 0
                F.semantic.generated.localArgs.size)).length := by
        simpa using hcanonical
      have Hparameter :=
        List.forall₂_getElem Hparameters k
          hsource htarget
      have Hparameter' : TrExprS H.outVEnv Us
          (abstractForallContext
            (equationDomains ++ liftedLocals) [])
          (.bvar (A.rule.binders.length - 1 - k + liftedLocals.length))
          parameterTargets[k] := by
        simpa [Expr.liftLooseBVars', hlocalsLifted] using Hparameter
      have hbound : A.rule.binders.length - 1 - k + liftedLocals.length <
          (equationDomains ++ liftedLocals).length := by
        have hk : k < stats.params.size := by simpa using hcanonical
        simp only [List.length_append, hequationLength]
        omega
      have htargetEq :=
        TrExprS.bvar_eq_of_abstractForallContext Hparameter' hbound
      simpa [VExpr.liftN, liftVar, Nat.add_comm] using htargetEq
  have Hindices' : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext (equationDomains ++ liftedLocals) []))
      indexSources exactIndexTargets := by
    simpa [equationDomains, parameterDecls, inserted, indexSources,
      exactIndexTargets, hsplitFront, List.append_assoc] using Hindices
  have anonymousWF : ∀ types : List VExpr,
      OnCtx types (H.outVEnv.IsType Us.length) →
      VLCtx.WF H.outVEnv Us.length
        (types.map fun type =>
          ((none, .vlam type) :
            Option (FVarId × List FVarId) × VLocalDecl)) := by
    intro types Htypes
    induction types with
    | nil => trivial
    | cons type types ih =>
      have Htype : H.outVEnv.IsType Us.length
          (VLCtx.toCtx (types.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl))) type := by
        rw [VLCtx.toCtx_map_anonymousLams]
        exact Htypes.2
      exact ⟨ih Htypes.1, nofun, Htype⟩
  have HvlctxWF : VLCtx.WF H.outVEnv Us.length
      (abstractForallContext (equationDomains ++ liftedLocals) []) := by
    have Hwf := anonymousWF
      (equationDomains ++ liftedLocals).reverse (by
        simpa [VLCtx.toCtx, List.append_assoc] using Hctx')
    simpa [abstractForallContext] using Hwf
  have HindexDefEq : List.Forall₂
      (fun spine exact => H.outVEnv.IsDefEqU Us.length
        (abstractForallContext
          (equationDomains ++ liftedLocals) []).toCtx spine exact)
      spineIndexTargets exactIndexTargets := by
    have align : ∀ {sources spines exacts : List _},
        List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext
                (equationDomains ++ liftedLocals) []))
            sources spines →
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext
                (equationDomains ++ liftedLocals) []))
            sources exacts →
          List.Forall₂
            (fun spine exact => H.outVEnv.IsDefEqU Us.length
              (abstractForallContext
                (equationDomains ++ liftedLocals) []).toCtx spine exact)
            spines exacts := by
      intro sources spines exacts Hleft Hright
      induction Hleft generalizing exacts with
      | nil =>
        cases Hright
        exact .nil
      | @cons source spine sources spines Hspine _ ih =>
        cases Hright with
        | cons Hexact Htail =>
          exact .cons
            (Hspine.uniq H.outVEnvWF
              (.refl H.outVEnvWF HvlctxWF) Hexact)
            (ih Htail)
    exact align HspineIndices Hindices'
  refine ⟨equationDomains, liftedFields, liftedLocals, added, frontDomains,
    exactIndexTargets, majorTarget, exposedTarget, ?_, rfl, ?_, rfl,
    hfieldsLifted, ?_, hlocalsLifted, hequationLength, Hctx',
    HlocalTemplate', Htyping', Hindices', Hmajor', hexactIndexLength, levels,
    parameterTargets, spineIndexTargets, ?_, hlevels, ?_, hparameterTargets,
    HindexDefEq⟩
  · simp [equationDomains, added, parameterDecls, List.append_assoc]
  · simp [added, frontDomains, inserted, List.append_assoc]
  · dsimp only [liftedFields]
    rw [hfieldEq]
  simpa [htranslatedArgs] using hspine
  simpa [parameterSources] using HparametersOriginal

end VerifyInductive
end Lean4Lean
