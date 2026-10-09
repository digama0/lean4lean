import Lean4Lean.Verify.Inductive.Rules.RecursiveResults

/-! The right-hand side of a rule: all recursive results (`RuleAlignment.RecursiveResults`)
fixed to one recursor telescope and one field frame, the application of the selected minor
premise to the constructor fields and the recursive results, and the typed translation of the
right-hand side in the fixed equation context (zero- and positive-arity cases). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One dependent recursive-hypothesis step, after the already-applied
hypotheses have been aligned.  Syntactic uniqueness of the selected minor
telescope identifies the caller's installed domains with the domains used by
the source replay; the common residual translation then closes the complete
higher-order domain on both sides. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorHypothesisWholeDomainDefEq
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
    (installedFieldDomains installedHypothesisDomains : List VExpr)
    (installedResidual : VExpr)
    (hinstalledFields : installedFieldDomains.length = A.rule.allArgs.size)
    (hinstalledHypotheses :
      installedHypothesisDomains.length = A.rule.recursiveArgs.size)
    (B : A.FieldFrame)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (htarget :
      T.minors[recursorMinorOffset indTypes owner + i]! =
        VExpr.wrapForalls
          (installedFieldDomains ++ installedHypothesisDomains)
          installedResidual)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (E : A.RecursiveResult T B j hj)
    (canonicalPrevious : List VExpr)
    (hcanonicalPreviousLength : canonicalPrevious.length = j)
    (Hbase :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let position := A.rule.allArgs.size + j
      let prior :=
        (installedFieldDomains ++ installedHypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (T.params ++ T.motives ++ T.minors ++ liftedPrior).reverse
        (equationDomains ++ canonicalPrevious).reverse) :
    ∃ hypothesisLocalDomains : List VExpr,
    ∃ hypothesisResidual : VExpr,
      installedHypothesisDomains[j]! =
        VExpr.wrapForalls hypothesisLocalDomains hypothesisResidual ∧
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let position := A.rule.allArgs.size + j
      let prior :=
        (installedFieldDomains ++ installedHypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let liftedHypothesisLocals :=
        (liftContextPrefixAt remaining.length position
          hypothesisLocalDomains.reverse).reverse
      let liftedCanonicalLocals :=
        (liftContextPrefix canonicalPrevious.length
          E.localDomains.reverse).reverse
      ∃ level, H.outVEnv.IsDefEq Us.length
        (T.params ++ T.motives ++ T.minors ++ liftedPrior).reverse
        (VExpr.wrapForalls liftedHypothesisLocals
          (hypothesisResidual.liftN remaining.length
            (position + hypothesisLocalDomains.length)))
        (VExpr.wrapForalls liftedCanonicalLocals
          (E.resultType.liftN canonicalPrevious.length
            E.localDomains.length)) (.sort level) := by
  dsimp only at Hbase ⊢
  rcases A.installedHypothesisDomains j hj B T E with ⟨C⟩
  let F := C.frame
  let fieldDomains := F.source.fieldDomains
  let hypothesisDomains := F.source.hypothesisDomains
  let hypothesisLocalDomains := F.residual.hypothesisLocalDomains
  let hypothesisResidual := F.residual.hypothesisResidual
  have hfields : fieldDomains.length = A.rule.allArgs.size := F.source.fields_length
  have hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size :=
    F.source.hypotheses_length
  have htarget' : T.minors[recursorMinorOffset indTypes owner + i]! =
      VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) F.source.targetResidual :=
    F.source.selected_minor_eq
  have hliftedPrior := C.prior_split
  have hlocal : hypothesisLocalDomains.length = E.localDomains.length := C.local_length
  have hhypothesisDomain : hypothesisDomains[j]! =
      VExpr.wrapForalls hypothesisLocalDomains hypothesisResidual :=
    F.residual.hypothesis_domain_eq
  have Hinstalled := C.hypothesis_translation
  have Hprefix := C.forall_prefix
  have HinstalledResidual := C.hypothesis_residual_translation
  have hdomains : fieldDomains ++ hypothesisDomains =
      installedFieldDomains ++ installedHypothesisDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq
      (n := A.rule.allArgs.size + A.rule.recursiveArgs.size)
      (suffix := [])
    · simp [hfields, hhypotheses]
    · simp [hinstalledFields, hinstalledHypotheses]
    · simpa [VExpr.wrapForalls_append] using htarget'.symm.trans htarget
  have hfieldDomains : fieldDomains = installedFieldDomains := by
    have Htake := congrArg
      (List.take A.rule.allArgs.size) hdomains
    simpa [hfields, hinstalledFields] using Htake
  have hfieldSource : C.frame.source.fieldDomains = installedFieldDomains := hfieldDomains
  subst fieldDomains
  have hhypothesisDomains :
      hypothesisDomains = installedHypothesisDomains := by
    have Hdrop := congrArg
      (List.drop A.rule.allArgs.size) hdomains
    simpa [hfields, hinstalledFields] using Hdrop
  have hhypothesisSource : C.frame.source.hypothesisDomains = installedHypothesisDomains :=
    hhypothesisDomains
  subst hypothesisDomains
  dsimp only [RecursorCheck.RuleAlignment.HypothesisFrame.liftedPrior,
    RecursorCheck.RuleAlignment.HypothesisFrame.liftedPrevious,
    RecursorCheck.RuleAlignment.HypothesisFrame.prior,
    RecursorCheck.RuleAlignment.HypothesisFrame.previous,
    RecursorCheck.RuleAlignment.HypothesisFrame.remaining,
    RecursorCheck.RuleAlignment.HypothesisFrame.minorIndex,
    RecursorCheck.RuleAlignment.HypothesisFrame.liftedHypothesisLocals,
    RecursorCheck.RuleAlignment.HypothesisFrame.liftedCanonicalLocals,
    RecursorCheck.RuleAlignment.HypothesisFrame.motiveApp,
    RecursorCheck.RuleAlignment.HypothesisFrame.residualSource,
    RecursorCheck.RuleAlignment.HypothesisFrame.equationDomains,
    RecursorCheck.RuleAlignment.HypothesisSource.position] at Hinstalled Hprefix HinstalledResidual
  rw [hfieldSource, hhypothesisSource] at Hinstalled HinstalledResidual
  rw [hhypothesisSource] at Hprefix
  have hhypothesisSourceF : F.source.hypothesisDomains = installedHypothesisDomains :=
    hhypothesisSource
  rw [hhypothesisSourceF] at hhypothesisDomain
  refine ⟨hypothesisLocalDomains, hypothesisResidual,
    hhypothesisDomain, ?_⟩
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let liftedCanonicalLocals :=
    (liftContextPrefix canonicalPrevious.length
      E.localDomains.reverse).reverse
  have Hcanonical := E.fullForallTranslationAfter canonicalPrevious
  rcases A.recursiveResultResidualAfter j hj B T E canonicalPrevious with
    ⟨HcanonicalResidual, HcanonicalResidualType⟩
  have Hprefix' := Hprefix
  simp only [List.length_reverse, liftContextPrefixAt_length,
    List.length_take, hinstalledHypotheses,
    Nat.min_eq_left (Nat.le_of_lt hj)] at Hprefix'
  exact Hprefix'.translatedWholeTargetsOfResidualRightSort
    H.outVEnvWF Hbase
      (by simpa using Hinstalled)
      (by simpa [equationDomains, liftedCanonicalLocals,
        hcanonicalPreviousLength] using Hcanonical)
      (by simpa using hlocal) (by simp)
      (by simpa using HinstalledResidual)
      (by simpa [equationDomains, liftedCanonicalLocals,
        hcanonicalPreviousLength] using HcanonicalResidual)
      (by simpa [equationDomains, liftedCanonicalLocals] using
        HcanonicalResidualType)

/-- All recursive results of one generated rule, chosen in their executable
array order and fixed to one recursor telescope and one field frame. -/
structure
    RecursorCheck.RuleAlignment.RecursiveResults
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
    (B : A.FieldFrame) where
  resultAt : ∀ j (hj : j < A.rule.recursiveArgs.size),
    A.RecursiveResult T B j hj

def
    RecursorCheck.RuleAlignment.RecursiveResults.bodies
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B) : List VExpr :=
  List.ofFn fun j : Fin A.rule.recursiveArgs.size =>
    let E := C.resultAt j j.isLt
    VExpr.wrapLams E.localDomains E.resultBody

/-- The closed dependent types corresponding pointwise to `bodies`.  Keeping
this as a parallel list makes the later minor-application fold explicit:
each recursive-result term is applied at exactly the same ordinal as the
installed minor hypothesis it discharges. -/
def
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTypes
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B) : List VExpr :=
  List.ofFn fun j : Fin A.rule.recursiveArgs.size =>
    let E := C.resultAt j j.isLt
    VExpr.wrapForalls E.localDomains E.resultType

@[simp] theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodies_length
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B) :
    C.bodies.length = A.rule.recursiveArgs.size := by
  simp [RecursiveResults.bodies]

@[simp] theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTypes_length
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B) :
    C.bodyTypes.length = A.rule.recursiveArgs.size := by
  simp [RecursiveResults.bodyTypes]

/-- Exact pointwise typing of the two parallel recursive-result lists in the
fixed equation context.  This is stronger than `bodyWF`: the latter is useful
for translation constructors, while this theorem retains the dependent type
required by the application spine. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTyping
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let hjType : j < C.bodyTypes.length := by simpa using hj
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      C.bodies[j]
      (C.bodyTypes)[j] := by
  let E := C.resultAt j (by simpa using hj)
  simpa [RecursiveResults.bodies,
    RecursiveResults.bodyTypes, E] using E.closed_typing

/-- Ordered list-level form of `bodyTyping`, ready for the generic closed
domain application fold. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTypings
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    List.Forall₂
      (H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx)
      C.bodies C.bodyTypes := by
  dsimp only
  apply Lean4Lean.VerifyInductive.List.forall₂_of_getElem
  · simp
  · intro j hjBodies hjTypes
    simpa using C.bodyTyping j hjBodies

/-- The chronological `j`th closed-domain entry is exactly the canonical
higher-order result type weakened below the `j` earlier hypotheses. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.liftClosedBodyType_getElem
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B)
    (j : Nat) (hj : j < C.bodyTypes.length) :
    let E := C.resultAt j (by simpa using hj)
    (VExpr.liftClosedDomains C.bodyTypes 0)[j]'(by simpa using hj) =
      VExpr.wrapForalls
        (liftContextPrefix j E.localDomains.reverse).reverse
        (E.resultType.liftN j E.localDomains.length) := by
  dsimp only
  let E := C.resultAt j (by simpa using hj)
  rw [VExpr.liftClosedDomains_getElem C.bodyTypes 0 j hj]
  have hbodyType : C.bodyTypes[j] =
      VExpr.wrapForalls E.localDomains E.resultType := by
    simp [RecursiveResults.bodyTypes, E]
  rw [hbodyType, VExpr.liftN_wrapForalls]
  simp [E, liftContextPrefix, Nat.add_comm]

/-- Inductively align the complete installed recursive-hypothesis telescope
with the canonical closed result types.  At ordinal `j`, the induction
hypothesis is exactly the base-context conversion required by
`installedSelectedMinorHypothesisWholeDomainDefEq`. -/
theorem
    RecursorCheck.RuleAlignment.installedRecursiveHypothesisContext
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
      H.recInfos[owner]!.indices.size owner)
    (C : A.RecursiveResults T B)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size)
    (htarget :
      T.minors[recursorMinorOffset indTypes owner + i]! =
        VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual)
    (Hbase :
      let minorIdx := recursorMinorOffset indTypes owner + i
      let remaining := T.minors.drop minorIdx
      let installedFields :=
        (liftContextPrefix remaining.length fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
        equationDomains.reverse) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let remaining := T.minors.drop minorIdx
    let installedHypotheses :=
      (liftContextPrefixAt remaining.length fieldDomains.length
        hypothesisDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ equationDomains.reverse)
      ((VExpr.liftClosedDomains C.bodyTypes 0).reverse ++
        equationDomains.reverse) := by
  dsimp only at Hbase ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let installedBase :=
    (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
  let canonicalDomains := VExpr.liftClosedDomains C.bodyTypes 0
  have hinstalledLength : installedHypotheses.length =
      A.rule.recursiveArgs.size := by
    simp [installedHypotheses, hhypotheses]
  have hcanonicalLength : canonicalDomains.length =
      A.rule.recursiveArgs.size := by
    simp [canonicalDomains]
  have go : ∀ n, n ≤ A.rule.recursiveArgs.size →
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        ((installedHypotheses.take n).reverse ++ installedBase)
        ((canonicalDomains.take n).reverse ++ equationDomains.reverse) := by
    intro n hn
    induction n with
    | zero =>
      simpa [Us, remaining, installedFields, installedBase,
        equationDomains] using Hbase
    | succ n ih =>
      have hnlt : n < A.rule.recursiveArgs.size := by omega
      have Hprior := ih (by omega)
      let E := C.resultAt n hnlt
      let canonicalPrevious := canonicalDomains.take n
      have hcanonicalPreviousLength : canonicalPrevious.length = n := by
        exact List.length_take_of_le (by rw [hcanonicalLength]; omega)
      have hpriorSplit :
          (fieldDomains ++ hypothesisDomains).take
              (A.rule.allArgs.size + n) =
            fieldDomains ++ hypothesisDomains.take n := by
        rw [← hfields, List.take_length_add_append]
      have hnHypotheses : n ≤ hypothesisDomains.length := by
        rw [hhypotheses]
        omega
      have hinstalledPrevious : installedHypotheses.take n =
          (liftContextPrefixAt remaining.length fieldDomains.length
            (hypothesisDomains.take n).reverse).reverse := by
        have Htake := liftContextPrefixAt_reverse_append_take_left
          remaining.length fieldDomains.length
          (hypothesisDomains.take n) (hypothesisDomains.drop n)
        rw [List.take_append_drop n hypothesisDomains] at Htake
        simpa only [installedHypotheses,
          List.length_take_of_le hnHypotheses] using Htake
      have HpointBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
          (T.params ++ T.motives ++ T.minors ++
            (liftContextPrefix remaining.length
              ((fieldDomains ++ hypothesisDomains).take
                (A.rule.allArgs.size + n)).reverse).reverse).reverse
          (equationDomains ++ canonicalPrevious).reverse := by
        rw [hpriorSplit, liftContextPrefix_reverse_append,
          ← hinstalledPrevious]
        simpa [installedFields, installedBase, equationDomains,
          canonicalPrevious,
          List.reverse_append, List.append_assoc] using Hprior
      rcases A.installedSelectedMinorHypothesisWholeDomainDefEq
          fieldDomains hypothesisDomains targetResidual hfields hhypotheses
          B T htarget n hnlt E canonicalPrevious hcanonicalPreviousLength
          HpointBase with
        ⟨localDomains, residual, hhypothesisDomain, Hdomain⟩
      have hinstalledDomain : installedHypotheses[n] =
          VExpr.wrapForalls
            ((liftContextPrefixAt remaining.length
              (A.rule.allArgs.size + n) localDomains.reverse).reverse)
            (residual.liftN remaining.length
              (A.rule.allArgs.size + n + localDomains.length)) := by
        rw [← getElem!_pos installedHypotheses n (by
          rw [hinstalledLength]; exact hnlt)]
        simp only [installedHypotheses]
        rw [liftContextPrefixAt_reverse_getElem
          remaining.length fieldDomains.length hypothesisDomains n
          (by simpa [hhypotheses] using hnlt),
          hhypothesisDomain, VExpr.liftN_wrapForalls]
        simp [hfields, Nat.add_assoc]
      have hcanonicalDomain : canonicalDomains[n] =
          VExpr.wrapForalls
            (liftContextPrefix n E.localDomains.reverse).reverse
            (E.resultType.liftN n E.localDomains.length) := by
        simpa [canonicalDomains, E] using
          C.liftClosedBodyType_getElem n (by
            simpa [canonicalDomains, hcanonicalLength] using hnlt)
      have Hdomain' : ∃ level, H.outVEnv.IsDefEq Us.length
          ((installedHypotheses.take n).reverse ++ installedBase)
          installedHypotheses[n] canonicalDomains[n] (.sort level) := by
        rw [hinstalledDomain, hcanonicalDomain]
        have hliftedPriorCtx := congrArg List.reverse
          (liftContextPrefix_reverse_append remaining.length fieldDomains
            (hypothesisDomains.take n))
        dsimp only at Hdomain
        rw [hpriorSplit] at Hdomain
        simp only [List.reverse_append, List.reverse_reverse] at Hdomain hliftedPriorCtx
        rw [hliftedPriorCtx] at Hdomain
        simpa [Us, remaining, hinstalledPrevious, installedFields, installedBase,
          equationDomains, canonicalPrevious, hcanonicalPreviousLength,
          E, List.reverse_append, List.append_assoc] using Hdomain
      rcases Hdomain' with ⟨level, Hdomain'⟩
      have Hnext := VEnv.IsDefEqCtx.succ Hprior Hdomain'
      have hinstalledTakeSucc : installedHypotheses.take (n + 1) =
          installedHypotheses.take n ++ [installedHypotheses[n]] :=
        List.take_succ_eq_append_getElem (by
          rw [hinstalledLength]; exact hnlt)
      have hcanonicalTakeSucc : canonicalDomains.take (n + 1) =
          canonicalDomains.take n ++ [canonicalDomains[n]] :=
        List.take_succ_eq_append_getElem (by
          rw [hcanonicalLength]; exact hnlt)
      rw [hinstalledTakeSucc]
      rw [hcanonicalTakeSucc]
      simp only [List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact Hnext
  have Hmixed := go A.rule.recursiveArgs.size (by omega)
  have HmixedFull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ installedBase)
      (canonicalDomains.reverse ++ equationDomains.reverse) := by
    have hinstalledTake : installedHypotheses.take
        A.rule.recursiveArgs.size = installedHypotheses :=
      by rw [← hinstalledLength, List.take_length]
    have hcanonicalTake : canonicalDomains.take
        A.rule.recursiveArgs.size = canonicalDomains :=
      by rw [← hcanonicalLength, List.take_length]
    simpa only [hinstalledTake, hcanonicalTake] using Hmixed
  have Hleft := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
    Hbase HmixedFull.isType
  have Hresult := VEnv.IsDefEqCtx.trans_empty
    H.outVEnvWF (Hleft.symm H.outVEnvWF.ordered) HmixedFull
  simpa [remaining, installedHypotheses, canonicalDomains, equationDomains,
    installedBase, hinstalledLength, hcanonicalLength,
    List.append_assoc] using Hresult

/-- Pointwise strict source translation for the canonical result list, once
the shared lambda-domain template has been translated in the fixed equation
context.  The same `resultAt` witness determines the source array position,
the target body, and the retained typing used by `bodyTyping`. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTranslationOfTemplate
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length)
    (templateTarget : VExpr)
    (Htemplate :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
      let E := C.resultAt j hjArg
      TrExprS H.outVEnv Us
        (abstractForallContext equationDomains [])
        ((E.frame.semantic.generated.current.lctx.mkLambda
            E.frame.semantic.generated.localArgs
            (mkAppN (A.rule.recursiveArgs)[j]
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
      C.bodies[j] := by
  let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
  let E := C.resultAt j hjArg
  have Hfull := E.fullTranslationOfTemplate templateTarget (by
    simpa only [E] using Htemplate)
  simpa [RecursiveResults.bodies, E] using Hfull

/-- Pointwise strict translation of a generated recursive result to its
canonical closed body in the fixed equation context. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTranslation
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      C.bodies[j] := by
  let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
  let E := C.resultAt j hjArg
  apply C.bodyTranslationOfTemplate j hj E.templateTarget
  simpa only [E] using E.templateTranslation

/-- List-level strict translation for the complete generated recursive-result
spine. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyTranslations
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext equationDomains []))
      (A.rule.recursiveResults.toList.map
        (fun result => result.abstractList A.rule.binders))
      C.bodies := by
  apply List.forall₂_of_getElem
  · simp [C.bodies_length, A.rule.recursive_calls.size]
  · intro j hsource htarget
    have hj : j < C.bodies.length := htarget
    have hresult : j < A.rule.recursiveResults.size := by
      rw [A.rule.recursive_calls.size]
      simpa [C.bodies_length] using hj
    have Htranslation := C.bodyTranslation j hj
    rw [getElem!_pos A.rule.recursiveResults j hresult] at Htranslation
    simpa using Htranslation

/-- Every selected recursive-result body is already well formed in the one
fixed equation context shared by the entire rule.  This is the list-level
typing invariant used by the minor-application fold. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveResults.bodyWF
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
    {T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.FieldFrame}
    (C : A.RecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    VExpr.WF H.outVEnv Us.length
      (abstractForallContext equationDomains []).toCtx C.bodies[j] := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  have hj' : j < A.rule.recursiveArgs.size := by
    simpa using hj
  let E := C.resultAt j hj'
  have hbody : C.bodies[j] =
      VExpr.wrapLams E.localDomains E.resultBody := by
    simp [RecursiveResults.bodies, E]
  rw [hbody]
  refine ⟨VExpr.wrapForalls E.localDomains E.resultType, ?_⟩
  change H.outVEnv.HasType Us.length
    (abstractForallContext equationDomains []).toCtx
    (VExpr.wrapLams E.localDomains E.resultBody)
    (VExpr.wrapForalls E.localDomains E.resultType)
  simpa only [Us, equationDomains] using E.closed_typing

theorem
    RecursorCheck.RuleAlignment.recursiveResults
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
    (B : A.FieldFrame) :
    Nonempty (A.RecursiveResults T B) := by
  classical
  exact ⟨{
    resultAt := fun j hj => Classical.choice
      (A.recursiveResult T B j hj) }⟩

/-- Synchronize the selected minor and every canonical recursive result on one
recursor telescope, one field frame, and one literal anonymous
equation context.  No existential witness chosen by a pointwise theorem may
drift after this boundary. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorApplicationFrame
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.FieldFrame,
      ∃ T : RecursorTypeTelescope H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.RecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationFieldDomains :=
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFieldDomains.length + later.length
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          (∃ checkedDomains checkedEquationFieldDomains : List VExpr,
            checkedDomains.length = A.rule.allArgs.size ∧
            checkedEquationFieldDomains =
              (liftContextPrefix inserted.length
                checkedDomains.reverse).reverse ∧
            VEnv.IsDefEqCtx H.outVEnv Us.length []
              (checkedEquationFieldDomains.reverse ++
                (T.params ++ inserted).reverse)
              (abstractForallContext equationDomains []).toCtx) ∧
          H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
            (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + equationFieldDomains.length) 0) ∧
          (∀ j (hj : j < C.bodies.length),
            let hjType : j < C.bodyTypes.length := by simpa using hj
            H.outVEnv.HasType Us.length
              (abstractForallContext equationDomains []).toCtx C.bodies[j]
              (C.bodyTypes)[j]) ∧
          (∀ j (hj : j < A.rule.recursiveArgs.size),
            let E := C.resultAt j hj
            OnCtx
                (E.localDomains.reverse ++
                  (abstractForallContext equationDomains []).toCtx)
                (H.outVEnv.IsType Us.length) ∧
              H.outVEnv.HasType Us.length
                (E.localDomains.reverse ++
                  (abstractForallContext equationDomains []).toCtx)
                E.resultBody E.resultType) ∧
          ∀ j (hj : j < C.bodies.length),
            VExpr.WF H.outVEnv Us.length
              (abstractForallContext equationDomains []).toCtx C.bodies[j] := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.fieldFrame with ⟨B⟩
  rcases A.installedScopedSelectedMinorTypeFrame B with
    ⟨T, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, HfixedContext, Hminor⟩
  rcases A.recursiveResults T B with ⟨C⟩
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFieldDomains.length + later.length
  have hequationContext :
      (abstractForallContext equationDomains []).toCtx =
        (liftContextPrefix inserted.length B.fieldDomains.reverse) ++
          inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx := by
    rw [abstractForallContext_toCtx]
    simp [equationDomains, equationFieldDomains, List.reverse_append,
      List.append_assoc, VLCtx.toCtx]
  have HfixedEquationContext : OnCtx
      (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    rw [hequationContext]
    simpa only [inserted] using HfixedContext
  rcases A.installedCheckedScopedEquationContextAlignmentFor B T with
    ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      hcheckedEquationFields, HcheckedEquation⟩
  have HcheckedEquation' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (checkedEquationFieldDomains.reverse ++
        (T.params ++ inserted).reverse)
      (abstractForallContext equationDomains []).toCtx := by
    rw [hequationContext]
    simpa only [inserted, List.append_assoc] using HcheckedEquation
  refine ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, hminorType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact HfixedEquationContext
  · exact ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      by simpa only [inserted] using hcheckedEquationFields,
      HcheckedEquation'⟩
  · rw [hequationContext]
    simpa only [inserted, equationFieldDomains, later, minorVar,
      List.length_reverse] using Hminor
  · intro j hj
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using C.bodyTyping j hj
  · intro j hj
    let E := C.resultAt j hj
    have Hclosed : H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.wrapLams E.localDomains E.resultBody)
        (VExpr.wrapForalls E.localDomains E.resultType) := by
      simpa only [equationDomains, inserted, equationFieldDomains,
        List.append_assoc] using E.closed_typing
    have Hopen := VEnv.HasType.wrapLams_inv H.outVEnvWF
      HfixedEquationContext Hclosed
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using Hopen
  · intro j hj
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using C.bodyWF j hj

theorem liftContextPrefixAt_liftContextPrefixAt (a b k : Nat) :
    ∀ ds : List VExpr, liftContextPrefixAt a k (liftContextPrefixAt b k ds) =
      liftContextPrefixAt (b + a) k ds
  | [] => rfl
  | d :: ds => by
    simp only [liftContextPrefixAt, liftContextPrefixAt_length]
    rw [VExpr.liftN'_liftN_hi, liftContextPrefixAt_liftContextPrefixAt a b k ds]

theorem liftContextPrefix_liftContextPrefix (a b : Nat) (ds : List VExpr) :
    liftContextPrefix a (liftContextPrefix b ds) = liftContextPrefix (b + a) ds :=
  liftContextPrefixAt_liftContextPrefixAt a b 0 ds

/-- Once the fixed equation fields agree with the installed field telescope,
the selected minor applies to the canonical field variables.  The selected
minor is stored outside the equation fields, so its declared type is read
off directly by a variable lookup in the outer telescope. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorFieldContextOfApplication
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
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hminorType :
      T.minors[recursorMinorOffset indTypes owner + i]! = VExpr.wrapForalls
        (fieldDomains ++ hypothesisDomains) targetResidual)
    (HfieldContext :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let outer := inserted.reverse ++
        H.parameterSuffix.parameterDecls.toCtx
      let later := T.minors.drop (minorIdx + 1)
      let installedEquationFields :=
        (liftContextPrefix (later.length + 1) fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFieldDomains.reverse ++ outer)
        (installedEquationFields.reverse ++ outer)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let inserted := T.motives ++ T.minors
    let equationFieldDomains :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let outer := inserted.reverse ++
      H.parameterSuffix.parameterDecls.toCtx
    let later := T.minors.drop (minorIdx + 1)
    let shift := later.length + 1
    let installedEquationFields :=
      (liftContextPrefix shift fieldDomains.reverse).reverse
    let installedEquationHypotheses :=
      (liftContextPrefixAt shift fieldDomains.length
        hypothesisDomains.reverse).reverse
    let installedEquationResidual := targetResidual.liftN shift
      (fieldDomains.length + hypothesisDomains.length)
    VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFieldDomains.reverse ++ outer)
        (installedEquationFields.reverse ++ outer) ∧
      H.outVEnv.HasType Us.length
        (equationFieldDomains.reverse ++ outer)
        (VExpr.mkApps (.bvar
          (equationFieldDomains.length + later.length))
          (bvarSpine equationFieldDomains.length))
        (VExpr.wrapForalls installedEquationHypotheses
          installedEquationResidual) := by
  dsimp only at HfieldContext ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let outer := inserted.reverse ++
    H.parameterSuffix.parameterDecls.toCtx
  let later := T.minors.drop (recursorMinorOffset indTypes owner + i + 1)
  let shift := later.length + 1
  let installedEquationFields :=
    (liftContextPrefix shift fieldDomains.reverse).reverse
  let installedEquationHypotheses :=
    (liftContextPrefixAt shift fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedEquationResidual := targetResidual.liftN shift
    (fieldDomains.length + hypothesisDomains.length)
  have hequationLength : equationFieldDomains.length =
      fieldDomains.length := by
    simp [equationFieldDomains, hfields, B.fieldDomains_length]
  have hctxShape :
      (abstractForallContext
        (H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains) []).toCtx =
        equationFieldDomains.reverse ++ outer := by
    simp [abstractForallContext_toCtx, equationFieldDomains, outer,
      List.reverse_append, List.append_assoc, VLCtx.toCtx]
  have htermShape :
      (VExpr.bvar later.length).liftN equationFieldDomains.length 0 =
        .bvar (equationFieldDomains.length + later.length) := by
    simp [VExpr.liftN, Nat.add_comm]
  -- The selected minor is a variable of `outer`; its declared type is the
  -- installed minor type, so its typing there is a direct lookup.
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hlater : later.length = T.minors.length - 1 - minorIdx := by
    simp only [later, List.length_drop]
    omega
  have Hlookup := Lookup.reverse_append T.minors
    (T.motives.reverse ++ H.parameterSuffix.parameterDecls.toCtx)
    minorIdx hminor
  have houter : outer = T.minors.reverse ++
      (T.motives.reverse ++ H.parameterSuffix.parameterDecls.toCtx) := by
    simp [outer, inserted, List.reverse_append, List.append_assoc]
  have hminorGet : T.minors[minorIdx] = VExpr.wrapForalls
      (fieldDomains ++ hypothesisDomains) targetResidual := by
    rw [← hminorType, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hminor]
    rfl
  have hshiftEq : T.minors.length - minorIdx = later.length + 1 := by
    omega
  rw [← houter, ← hlater, hminorGet, hshiftEq] at Hlookup
  have hbaseShape :
      (VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
          targetResidual).liftN (later.length + 1) =
        VExpr.wrapForalls installedEquationFields
          (VExpr.wrapForalls installedEquationHypotheses
            installedEquationResidual) := by
    rw [VExpr.liftN_wrapForalls]
    simp only [Nat.zero_add]
    have hprefix : liftContextPrefixAt (later.length + 1) 0
        (fieldDomains ++ hypothesisDomains).reverse =
        liftContextPrefix (later.length + 1)
          (fieldDomains ++ hypothesisDomains).reverse := rfl
    rw [hprefix]
    rw [liftContextPrefix_reverse_append]
    simp [shift, installedEquationFields, installedEquationHypotheses,
      installedEquationResidual, VExpr.wrapForalls_append]
  rw [hbaseShape] at Hlookup
  have HminorBase : H.outVEnv.HasType Us.length outer
      (.bvar later.length)
      (VExpr.wrapForalls installedEquationFields
        (VExpr.wrapForalls installedEquationHypotheses
          installedEquationResidual)) :=
    .bvar Hlookup
  have HminorBase' : H.outVEnv.HasType Us.length outer
      (.bvar later.length)
      (VExpr.wrapForalls
        (installedEquationFields ++ installedEquationHypotheses)
        installedEquationResidual) := by
    rw [VExpr.wrapForalls_append]
    exact HminorBase
  have HpartialInstalled :=
    VEnv.HasType.mkApps_wrapForalls_prefix_bvarSpine
      H.outVEnvWF.ordered
      (initial := installedEquationFields)
      (suffix := installedEquationHypotheses) HminorBase'
  have HpartialFixed := HpartialInstalled.defeqDFC
    H.outVEnvWF.ordered (HfieldContext.symm H.outVEnvWF.ordered)
  exact ⟨HfieldContext, by
    simpa [Us, inserted, equationFieldDomains, outer, later, shift,
      installedEquationFields, installedEquationHypotheses,
      installedEquationResidual, hequationLength, hfields,
      B.fieldDomains_length, VExpr.liftN, bvarSpine,
      List.length_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      HpartialFixed⟩

/-- Positive-arity selected minors admit their canonical field application
in the one fixed equation context shared by all recursive results.  The
application is first typed using the source-stable outer telescope, then
transported through the exact same checked field frame to the fixed
equation fields.  Inverting that well-formed application additionally
identifies those fixed fields with the selected minor's installed fields. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorApplicationPositiveArity
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.FieldFrame,
      ∃ T : RecursorTypeTelescope H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ _C : A.RecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationFieldDomains :=
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFieldDomains.length + later.length
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + equationFieldDomains.length) 0) ∧
          VExpr.WF H.outVEnv Us.length
            (abstractForallContext equationDomains []).toCtx
            (VExpr.mkApps (.bvar minorVar)
              (bvarSpine equationFieldDomains.length)) ∧
          let outer := inserted.reverse ++
            H.parameterSuffix.parameterDecls.toCtx
          let shift := later.length + 1
          let installedEquationFields :=
            (liftContextPrefix shift fieldDomains.reverse).reverse
          let installedEquationHypotheses :=
            (liftContextPrefixAt shift fieldDomains.length
              hypothesisDomains.reverse).reverse
          let installedEquationResidual := targetResidual.liftN shift
            (fieldDomains.length + hypothesisDomains.length)
          VEnv.IsDefEqCtx H.outVEnv Us.length []
              (equationFieldDomains.reverse ++ outer)
              (installedEquationFields.reverse ++ outer) ∧
            H.outVEnv.HasType Us.length
              (abstractForallContext equationDomains []).toCtx
              (VExpr.mkApps (.bvar minorVar)
                (bvarSpine equationFieldDomains.length))
              (VExpr.wrapForalls installedEquationHypotheses
                installedEquationResidual) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.installedMinorApplicationFrame with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, HfixedContext,
      _HcheckedFrame, Hminor, _HbodyTyping, _HopenTyping, _HbodyWF⟩
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFieldDomains.length + later.length
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hequationContext :
      (abstractForallContext equationDomains []).toCtx =
        equationFieldDomains.reverse ++ inserted.reverse ++
          H.parameterSuffix.parameterDecls.toCtx := by
    rw [abstractForallContext_toCtx]
    simp [equationDomains, equationFieldDomains, List.reverse_append,
      List.append_assoc, VLCtx.toCtx]
  have HinsP : OnCtx (inserted.reverse ++
      H.parameterSuffix.parameterDecls.toCtx) (H.outVEnv.IsType Us.length) := by
    have h := HfixedContext
    rw [hequationContext] at h
    simp only [List.append_assoc] at h
    exact OnCtx.of_append h
  rcases A.installedCheckedScopedFieldAlignment B with
    ⟨checkedDomains, checkedResidual, hchecked, Hchecked, HcheckedB⟩
  have Hlink := A.installedInstalledCheckedFieldLink T hpositive checkedDomains
    checkedResidual hchecked Hchecked fieldDomains hypothesisDomains
    targetResidual hfields hminorType
  have Ha := VEnv.IsDefEqCtx.insertSameMiddle H.outVEnvWF.ordered
    checkedDomains.reverse B.fieldDomains.reverse inserted.reverse
    H.parameterSuffix.parameterDecls.toCtx HcheckedB
    (by simp [hchecked, B.fieldDomains_length]) HinsP
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  let remaining := (T.minors.drop minorIdx).reverse
  have Hremaining : OnCtx (remaining ++ base.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hprefix := T.prefixContext H.outVEnvWF.ordered
    have hminors := List.take_append_drop minorIdx T.minors
    have hreverse : T.minors.reverse =
        (T.minors.drop minorIdx).reverse ++
          (T.minors.take minorIdx).reverse := by
      simpa only [List.reverse_append] using
        (congrArg List.reverse hminors).symm
    simp only [List.reverse_append] at Hprefix
    rw [hreverse] at Hprefix
    simpa [base, remaining, List.reverse_append, List.append_assoc] using
      Hprefix
  have Hb := VEnv.IsDefEqCtx.insertSameMiddle H.outVEnvWF.ordered
    (liftContextPrefix (T.motives ++ T.minors.take minorIdx).length
      checkedDomains.reverse)
    fieldDomains.reverse remaining base.reverse Hlink
    (by simp [hchecked, hfields]) Hremaining
  have hfullContext : remaining ++ base.reverse =
      (T.params ++ T.motives ++ T.minors).reverse := by
    have hminorPrefix : (T.minors.drop minorIdx).reverse ++
        (T.minors.take minorIdx).reverse = T.minors.reverse := by
      simpa only [List.reverse_append] using congrArg List.reverse
        (List.take_append_drop minorIdx T.minors)
    simp only [remaining, base, List.reverse_append]
    rw [← List.append_assoc, hminorPrefix]
  have hdrop : T.minors.drop minorIdx = T.minors[minorIdx] :: later := by
    simp [later]
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [remaining, hdrop]
  rw [liftContextPrefix_liftContextPrefix] at Hb
  simp only [List.append_assoc] at Hb
  rw [hfullContext, hremainingLength] at Hb
  have Hparams := H.installedRecursorParameterContextFor howner T
  rw [← H.parameterDecls] at Hparams
  have HouterT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx)
      (T.params ++ T.motives ++ T.minors).reverse := by
    have h := VEnv.IsDefEqCtx.extendSamePrefix
      (Hparams.symm H.outVEnvWF.ordered) HinsP
    simpa [inserted, List.reverse_append, List.append_assoc] using h
  have Hb' := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF HouterT Hb
  have hlen : (T.motives ++ T.minors.take minorIdx).length +
      (later.length + 1) = inserted.length := by
    have hlater : later.length = T.minors.length - (minorIdx + 1) := by
      simp [later]
    simp only [inserted, List.length_append, List.length_take]
    omega
  rw [hlen] at Hb'
  have Ha' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftContextPrefix inserted.length checkedDomains.reverse ++
        (inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx))
      (liftContextPrefix inserted.length B.fieldDomains.reverse ++
        (inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx)) := by
    simpa [List.append_assoc] using Ha
  have HfieldContext := VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
    (Ha'.symm H.outVEnvWF.ordered) Hb'
  have HinstalledFields :=
    A.installedMinorFieldContextOfApplication B T fieldDomains
      hypothesisDomains targetResidual hfields hminorType (by
        simpa [equationFieldDomains, inserted, later] using HfieldContext)
  have HinstalledTyping : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps (.bvar minorVar)
        (bvarSpine equationFieldDomains.length))
      (VExpr.wrapForalls
        (liftContextPrefixAt (later.length + 1) fieldDomains.length
          hypothesisDomains.reverse).reverse
        (targetResidual.liftN (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length))) := by
    rw [hequationContext]
    simpa only [Us, minorIdx, equationFieldDomains, inserted, later,
      minorVar, List.append_assoc] using HinstalledFields.2
  exact ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, hminorType, HfixedContext, Hminor,
    ⟨_, HinstalledTyping⟩, HinstalledFields.1, HinstalledTyping⟩

/-- Apply all canonical recursive results to a selected minor that has
already been applied to the fixed equation fields. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorRecursiveApplicationOfContext
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
      H.recInfos[owner]!.indices.size owner)
    (C : A.RecursiveResults T B)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size)
    (htarget : T.minors[recursorMinorOffset indTypes owner + i]! =
      VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual)
    (Hctx :
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFields
      OnCtx (abstractForallContext equationDomains []).toCtx
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hfield :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let later := T.minors.drop (minorIdx + 1)
      let installedFields :=
        (liftContextPrefix (later.length + 1) fieldDomains.reverse).reverse
      let outer := inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFields.reverse ++ outer)
        (installedFields.reverse ++ outer))
    (Hpartial :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFields
      let later := T.minors.drop (minorIdx + 1)
      let installedHypotheses :=
        (liftContextPrefixAt (later.length + 1) fieldDomains.length
          hypothesisDomains.reverse).reverse
      let installedResidual := targetResidual.liftN (later.length + 1)
        (fieldDomains.length + hypothesisDomains.length)
      H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.mkApps (.bvar (equationFields.length + later.length))
          (bvarSpine equationFields.length))
        (VExpr.wrapForalls installedHypotheses installedResidual)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let inserted := T.motives ++ T.minors
    let equationFields :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
        equationFields
    let later := T.minors.drop (minorIdx + 1)
    let fn := VExpr.mkApps
      (.bvar (equationFields.length + later.length))
      (bvarSpine equationFields.length)
    let finalType := VExpr.applyForallType
      (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
        (targetResidual.liftN (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length)))
      C.bodies
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps fn C.bodies) finalType := by
  dsimp only at Hctx Hfield Hpartial ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++ equationFields
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedResidual := targetResidual.liftN remaining.length
    (fieldDomains.length + hypothesisDomains.length)
  let fn := VExpr.mkApps
    (.bvar (equationFields.length + later.length))
    (bvarSpine equationFields.length)
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simp [remaining, later]
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
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
      equationFields, inserted, later, hremainingLength,
      List.append_assoc] using Hfield
  have HfieldT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ T.params.reverse)
      (installedPrefix ++ T.params.reverse) := by
    have Hrebased := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.rebaseCommonSuffix
      H.outVEnvWF Hparams' Hfield'
    simpa [equationPrefix, installedPrefix, installedFields,
      hremainingLength, List.append_assoc] using Hrebased
  have HequationParams :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hparams' HfieldT.isType
  have HbaseMixed := VEnv.IsDefEqCtx.trans_empty
    H.outVEnvWF (HfieldT.symm H.outVEnvWF.ordered) HequationParams
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      equationDomains.reverse := by
    simpa [equationPrefix, installedPrefix, equationDomains,
      equationFields, inserted, List.reverse_append,
      List.append_assoc] using HbaseMixed
  have Hhypotheses := A.installedRecursiveHypothesisContext B T C
    fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      htarget (by simpa [Us, minorIdx, remaining, installedFields,
        equationDomains, equationFields, inserted,
        List.append_assoc] using Hbase)
  have Hhypotheses' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++
        (abstractForallContext equationDomains []).toCtx)
      ((VExpr.liftClosedDomains C.bodyTypes 0).reverse ++
        (abstractForallContext equationDomains []).toCtx) := by
    simpa [remaining, installedHypotheses, equationDomains,
      equationFields, inserted, abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc] using Hhypotheses
  have Hpartial' : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx fn
      (VExpr.wrapForalls installedHypotheses installedResidual) := by
    simpa [remaining, installedHypotheses, installedResidual,
      hremainingLength, equationDomains, equationFields, inserted,
      later, fn] using Hpartial
  have HbodyTypings := C.bodyTypings
  have Hexact := VEnv.HasType.mkApps_of_defeqLiftClosedDomains_exact
    (installedDomains := installedHypotheses)
    (resultType := installedResidual) (types := C.bodyTypes)
    (args := C.bodies) H.outVEnvWF Hctx Hpartial' Hhypotheses' (by
      simpa only [Us, equationDomains, inserted, equationFields,
        List.append_assoc] using HbodyTypings)
  simpa [installedResidual, hremainingLength, fn, later, equationFields,
    inserted, B.fieldDomains_length] using Hexact

/-- Degenerate generated rules need no application fold: when the selected
constructor has neither fields nor recursive hypotheses, the selected minor
variable itself is the complete RHS and is already typed in the fixed
equation context.  Isolating this case lets the positive-arity replay theorem
remain honest about the nonempty telescope premise it uses. -/
theorem
    RecursorCheck.RuleAlignment.installedMinorApplicationZeroArity
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.FieldFrame,
      ∃ T : RecursorTypeTelescope H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.RecursiveResults T B,
      ∃ targetResidual : VExpr,
        C.bodies = [] ∧
        T.minors[minorIdx]! = targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted
        let later := T.minors.drop (minorIdx + 1)
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (.bvar later.length)
            (targetResidual.liftN (later.length + 1) 0) := by
  dsimp only
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hhypothesesZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.installedMinorApplicationFrame with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, Hctx, _HcheckedEquation, Hminor,
      _HbodyTyping, _HopenBodyTyping, _HbodyWF⟩
  have hfieldDomains : fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero (hfields.trans hfieldsZero)
  have hhypothesisDomains : hypothesisDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hhypotheses.trans hhypothesesZero)
  have hframeFields : B.fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (B.fieldDomains_length.trans hfieldsZero)
  have hbodies : C.bodies = [] :=
    List.eq_nil_of_length_eq_zero (by
      rw [C.bodies_length, hhypothesesZero])
  subst fieldDomains
  subst hypothesisDomains
  exact ⟨B, T, C, targetResidual, hbodies,
    by simpa [VExpr.wrapForalls] using hminorType,
    by simpa [hframeFields, liftContextPrefix, liftContextPrefixAt,
      List.append_assoc] using Hctx,
    by simpa [hframeFields, liftContextPrefix, liftContextPrefixAt,
      VExpr.wrapForalls, VLCtx.toCtx, List.append_assoc] using Hminor⟩

/-- Positive-arity generated RHS in its fixed equation context.
The selected minor, constructor fields, and generated recursive results are
all translated strictly to the same application spine that is independently
typed by the canonical minor fold. -/
theorem
    RecursorCheck.RuleAlignment.installedRhsPositiveArityDetailed
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.FieldFrame,
      ∃ T : RecursorTypeTelescope H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.RecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
      ∃ equationFields : List VExpr,
      ∃ rhsBody typeBody : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        equationFields.length = A.rule.allArgs.size ∧
        equationFields =
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse ∧
        typeBody = VExpr.applyForallType
          (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
            (targetResidual.liftN
              ((T.minors.drop (minorIdx + 1)).length + 1)
              (fieldDomains.length + hypothesisDomains.length)))
          C.bodies ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFields.length + later.length
        let outer := inserted.reverse ++
          H.parameterSuffix.parameterDecls.toCtx
        let installedEquationFields :=
          (liftContextPrefix (later.length + 1)
            fieldDomains.reverse).reverse
        let installedEquationHypotheses :=
          (liftContextPrefixAt (later.length + 1) fieldDomains.length
            hypothesisDomains.reverse).reverse
        let installedEquationResidual := targetResidual.liftN
          (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length)
        rhsBody = VExpr.mkApps
            (VExpr.mkApps (.bvar minorVar)
              (bvarSpine equationFields.length)) C.bodies ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (VExpr.mkApps (.bvar minorVar)
              (bvarSpine equationFields.length))
            (VExpr.wrapForalls installedEquationHypotheses
              installedEquationResidual) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (equationFields.reverse ++ outer)
            (installedEquationFields.reverse ++ outer) ∧
          OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            rhsBody typeBody := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.installedMinorApplicationPositiveArity hpositive with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, Hctx, _Hminor, HpartialWF,
      Hfield, Hpartial⟩
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFields.length + later.length
  let fn := VExpr.mkApps (.bvar minorVar)
    (bvarSpine equationFields.length)
  have Hrhs := A.installedMinorRecursiveApplicationOfContext B T C
      fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      hminorType Hctx Hfield Hpartial
  let finalType := VExpr.applyForallType
    (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
      (targetResidual.liftN (later.length + 1)
        (fieldDomains.length + hypothesisDomains.length)))
    C.bodies
  let rhsBody := VExpr.mkApps fn C.bodies
  have HrhsTyped : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx rhsBody finalType := by
    simpa only [Us, minorIdx, inserted, equationFields, equationDomains,
      later, minorVar, fn, rhsBody, List.append_assoc] using Hrhs
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorVar : minorVar < equationDomains.length := by
    dsimp only [minorVar, equationDomains, equationFields, inserted, later]
    simp only [List.length_append, List.length_reverse,
      liftContextPrefix_length, List.length_drop]
    omega
  have HminorTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar minorVar) (.bvar minorVar) :=
    TrExprS.bvar_of_abstractForallContext equationDomains [] minorVar hminorVar
  have HfieldsTr := A.installedScopedEquationFieldTranslationsFor B T
  have HpartialTr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HminorTr HfieldsTr HpartialWF
  have HresultsTr : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext equationDomains []))
      ((A.rule.recursiveResults.map fun result =>
        result.abstractList A.rule.binders).toList) C.bodies := by
    simpa only [Us, equationDomains, inserted, equationFields,
      Array.toList_map, List.append_assoc] using C.bodyTranslations
  have HrhsTr₀ := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HpartialTr HresultsTr
      (show VExpr.WF H.outVEnv Us.length
        (abstractForallContext equationDomains []).toCtx rhsBody from
          ⟨finalType, HrhsTyped⟩)
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        minorVar := by
    dsimp only [minorVar, equationFields, inserted, later]
    simp only [List.length_reverse, liftContextPrefix_length,
      List.length_drop, B.fieldDomains_length, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have HrhsTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsourceShape]
    simpa [rhsBody, fn, Expr.mkAppN_eq_mkAppList, equationFields,
      equationDomains, inserted, B.fieldDomains_length,
      List.append_assoc] using HrhsTr₀
  exact ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    equationFields, rhsBody, finalType, hfields, hhypotheses, hminorType,
    by simp [equationFields, B.fieldDomains_length], rfl, rfl, rfl,
    Hpartial, Hfield, Hctx, HrhsTr, HrhsTyped⟩

end VerifyInductive
end Lean4Lean
