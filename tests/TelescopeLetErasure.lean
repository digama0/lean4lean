import Lean4Lean.Verify.TypeChecker.InferType
import Lean.Util.CollectAxioms

/-! Reconstruct actual mixed telescopes over a dependent proof context. An
unused native let may contain a projection; dropping it reuses all retained
projection evidence in the same model context. Used and explicitly requested
lets remain present. -/
namespace TelescopeLetErasureTest
open Lean Lean4Lean Lean4Lean.TypeChecker

abbrev propositionId : FVarId := ⟨`proposition⟩
abbrev proofId : FVarId := ⟨`proof⟩
abbrev removedId : FVarId := ⟨`removed⟩
abbrev argumentId : FVarId := ⟨`argument⟩

abbrev propositions : MLCtx :=
  .vlam propositionId `proposition (.sort .zero) (.sort .zero) .default .nil
abbrev base : MLCtx :=
  .vlam proofId `proof (.fvar propositionId) (.bvar 0) .default propositions
abbrev projected : Expr := .proj `Structure 3 (.fvar proofId)
abbrev extended : MLCtx :=
  .vlet removedId `removed (.fvar propositionId) projected (.bvar 1) (.bvar 0) base
abbrev mixed : MLCtx :=
  .vlam argumentId `argument (.fvar propositionId) (.bvar 1) .default extended

-- A real model context containing a proposition and a dependent proof.
theorem emptyWF : VEnv.empty.WF := ⟨[], .empty⟩

theorem propositionsWF : propositions.WF VEnv.empty [] := by
  refine ⟨trivial, ?_, .sort rfl, _, .sort trivial⟩
  exact (show MLCtx.nil.WF VEnv.empty [] from trivial).tr.find?_eq_none.mpr (by
    simp [MLCtx.vlctx, VLCtx.fvars])

theorem baseWF : base.WF VEnv.empty [] := by
  refine ⟨propositionsWF, ?_, .fvar rfl, _, .bvar .zero⟩
  exact propositionsWF.tr.find?_eq_none.mpr (by
    simp [MLCtx.vlctx, VLCtx.fvars, propositionId, proofId])

abbrev Projection := TrProj base.vlctx.toCtx `Structure 3 (.bvar 0) (.bvar 0)

theorem extendedWF (projection : Projection) : extended.WF VEnv.empty [] := by
  refine ⟨baseWF, ?_, .fvar rfl, .proj (.fvar rfl) projection, .bvar .zero⟩
  exact baseWF.tr.find?_eq_none.mpr (by
    simp [MLCtx.vlctx, VLCtx.fvars, propositionId, proofId, removedId])

theorem mixedWF (projection : Projection) : mixed.WF VEnv.empty [] := by
  refine ⟨extendedWF projection, ?_, .fvar rfl, _, .bvar (.succ .zero)⟩
  exact (extendedWF projection).tr.find?_eq_none.mpr (by
    simp [MLCtx.vlctx, VLCtx.fvars,
      propositionId, proofId, removedId, argumentId])

abbrev nested : Expr := .lam `x (.fvar propositionId)
  (.letE `alias (.fvar propositionId) (.bvar 0) (.bvar 0) false) .default
abbrev nestedModel : VExpr := .lam (.bvar 1) (.bvar 0)
abbrev nestedType : VExpr := .forallE (.bvar 1) (.bvar 2)

theorem nestedTranslation : TrExprS VEnv.empty [] extended.vlctx nested nestedModel :=
  .lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl)
    (.letE (.bvar .zero) (.fvar rfl) (.bvar rfl) (.bvar rfl))

theorem nestedTyped : VEnv.empty.HasType 0 extended.vlctx.toCtx nestedModel nestedType :=
  .lam (.bvar (.succ .zero)) (.bvar .zero)

theorem rebuildLambda (projection : Projection) : TrExprS VEnv.empty [] base.vlctx nested nestedModel := by
  have rebuilt := (extendedWF projection).mkLambda_trS (Us := []) emptyWF
    nestedTranslation nestedTyped 1 (by decide)
  exact rebuilt.1

theorem rebuildForall (projection : Projection) : TrExprS VEnv.empty [] base.vlctx
    (.fvar propositionId) (.bvar 1) := by
  have source : TrExprS VEnv.empty [] extended.vlctx (.fvar propositionId) (.bvar 1) := .fvar rfl
  have rebuilt := (extendedWF projection).mkForall_trS (Us := []) emptyWF
    source ⟨_, VEnv.HasType.bvar (.succ .zero)⟩ 1 (by decide)
  exact rebuilt.1

theorem rebuildLet (projection : Projection) : TrExprS VEnv.empty [] base.vlctx nested nestedModel := by
  have rebuilt := (extendedWF projection).mkLet_trS (Us := []) emptyWF
    nestedTranslation nestedTyped 1 (by decide) [none] rfl
  exact rebuilt.1

-- Retained projection evidence is not transported to a different context.
theorem rebuildProjection (projection : Projection) : TrExprS VEnv.empty [] base.vlctx projected (.bvar 0) := by
  have source : TrExprS VEnv.empty [] extended.vlctx projected (.bvar 0) :=
    .proj (.fvar rfl) projection
  exact ((extendedWF projection).mkLambda_trS (Us := []) emptyWF source
    (VEnv.HasType.bvar .zero) 1 (by decide)).1

-- A lambda introduced above the dead let survives reconstruction.
theorem rebuildMixed (projection : Projection) : TrExprS VEnv.empty [] base.vlctx
    (.lam `argument (.fvar propositionId) (.fvar propositionId) .default)
    (.lam (.bvar 1) (.bvar 2)) := by
  have source : TrExprS VEnv.empty [] mixed.vlctx (.fvar propositionId) (.bvar 2) := .fvar rfl
  exact ((mixedWF projection).mkLambda_trS (Us := []) emptyWF source
    (VEnv.HasType.bvar (.succ (.succ .zero))) 2 (by decide)).1

-- The used-let branch keeps the original value, including its projection.
theorem retainUsedLet (projection : Projection) : TrExprS VEnv.empty [] base.vlctx
    (.letE `removed (.fvar propositionId) projected (.bvar 0) false) (.bvar 0) := by
  have source : TrExprS VEnv.empty [] extended.vlctx (.fvar removedId) (.bvar 0) := .fvar rfl
  exact ((extendedWF projection).mkLet_trS (Us := []) emptyWF source
    (VEnv.HasType.bvar .zero) 1 (by decide) [none] rfl).1

-- Explicit nd flags preserve even an unused let.
theorem retainRequestedLet (projection : Projection) (flag : Bool) : TrExprS VEnv.empty [] base.vlctx
    (.letE `removed (.fvar propositionId) projected nested flag) nestedModel := by
  cases flag <;>
    exact ((extendedWF projection).mkLet_trS (Us := []) emptyWF nestedTranslation
      nestedTyped 1 (by decide) [some _] rfl).1

example : extended.mkLambda 1 (by decide) nested = nested := rfl
example : extended.mkForall 1 (by decide) (.fvar propositionId) = .fvar propositionId := rfl
example : extended.mkLet 1 (by decide) [none] rfl nested = nested := rfl
example : mixed.mkLambda 2 (by decide) (.fvar propositionId) =
    .lam `argument (.fvar propositionId) (.fvar propositionId) .default := rfl

run_meta
  let environment ← getEnv
  let structural := [``MLCtx.WF.mkForall_trS, ``MLCtx.WF.mkLambda_trS, ``MLCtx.WF.mkLet_trS,
    ``TrExprS.eraseAbstractedLet]
  let converted := [``MLCtx.WF.mkForall_tr, ``MLCtx.WF.mkLambda_tr]
  let fixtures := [``emptyWF, ``propositionsWF, ``baseWF, ``extendedWF, ``mixedWF,
    ``nestedTranslation, ``nestedTyped, ``rebuildLambda, ``rebuildForall,
    ``rebuildLet, ``rebuildProjection, ``rebuildMixed, ``retainUsedLet, ``retainRequestedLet]
  let logic := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let native := [``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let conversionAdmissions := [``TrProj, ``VEnv.IsDefEqU.sort_inv, ``VEnv.IsDefEqU.forallE_inv_stratified,
    ``VEnv.addInduct_WF, ``VEnv.addInduct, ``VInductDecl.WF]
  let forbidden := [``TrProj.weak', ``TrProj.instN, ``TrProj.wf, ``TrProj.uniq,
    ``TrExprS.weakFV, ``TrExprS.weakFV', ``TrExprS.weakBV,
    ``TrExprS.inst_let, ``TrExprS.instN_let, ``TrExprS.instN, ``TrExprS.inst,
    ``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv,
    ``VEnv.IsDefEqU.weakN_iff, `Lean4Lean.VEnv.NormalEq.parRed,
    `Lean4Lean.VEnv.NormalEq.parRedS, `Lean4Lean.VEnv.IsDefEq.church_rosser,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj]
  for root in structural ++ converted ++ fixtures do
    let declaration ← getConstInfo root
    if declaration matches .axiomInfo _ then throwError "new telescope erasure axiom {root}"
    let some value := declaration.value? (allowOpaque := true)
      | throwError "missing telescope erasure proof {root}"
    if value.hasSorry then throwError "direct telescope erasure admission {root}"
    let pure := [``emptyWF, ``propositionsWF, ``baseWF, ``nestedTranslation, ``nestedTyped].contains root
    let expectedAdmissions := if pure then []
      else if converted.contains root then conversionAdmissions else [``TrProj]
    let expectedAxioms := if root == ``emptyWF then [``propext, ``Quot.sound, ``sorryAx]
      else if root == ``nestedTyped then [``propext]
      else if structural.contains root || root == ``nestedTranslation then logic else logic ++ native
    let axioms ← collectAxioms root
    unless expectedAxioms.length == axioms.size && expectedAxioms.all axioms.contains do
      throwError "telescope erasure axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden telescope erasure dependency {name} in {root}"
      if let some info := environment.find? name then
        pending := pending ++ info.type.getUsedConstants
        if let some proof := info.value? (allowOpaque := true) then
          if proof.hasSorry then
            unless expectedAdmissions.contains name do
              throwError "unapproved telescope erasure admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ proof.getUsedConstants
    unless pending.isEmpty do throwError "telescope erasure traversal exceeded bound"
    unless expectedAdmissions.length == admissions.size && expectedAdmissions.all admissions.contains do
      throwError "telescope erasure admission manifest changed for {root}: {repr admissions}"
    if (structural ++ converted).contains root then
      unless visited.contains ``TrExprS.eraseAbstractedLet do
        throwError "reconstruction bypassed unused-let erasure: {root}"
    logInfo m!"{root}: {visited.size} dependencies; exact admissions {repr admissions}; exact axioms {repr axioms}"

  -- Whole inference still has independent obligations; pin those rather than
  -- extrapolating the smaller builder trust boundary to the full checker.
  let common := [``TrProj, ``TrProj.weak', ``TrProj.defeqDFC, ``TrProj.uniq, ``TrProj.wf,
    ``VEnv.IsDefEqU.sort_inv, ``VEnv.IsDefEqU.forallE_inv_stratified,
    ``VEnv.addInduct_WF, ``VEnv.addInduct, ``VInductDecl.WF]
  let forallAdmissions := common ++ [``VEnv.IsDefEqU.weakN_iff, ``TrProj.weak'_inv, ``TrProj.instN]
  let lambdaAdmissions := forallAdmissions
  let letAdmissions := common ++ [``TrProj.instN]
  let forallAxioms := logic ++ native ++ [``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq,
    ``Lean.Level.hasMVar_eq, ``Lean.Level.hasParam_eq, ``Lean.Level.instLawfulBEqLevel]
  let lambdaAxioms := logic ++ native ++ [``Lean.Expr.abstractRange_eq, ``Lean.Expr.abstract_eq,
    ``Lean.Expr.hasLooseBVar_eq, ``Lean.Expr.instantiateRev_eq, ``Lean.Expr.instantiate_eq,
    ``Lean.Expr.looseBVarRange_eq, ``Lean.Expr.lowerLooseBVars_eq]
  let letAxioms := lambdaAxioms ++ [``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel,
    ``Lean.Syntax.structEq_eq]
  for root in [``Inner.inferForall.WF, ``Inner.inferLambda.WF, ``Inner.inferLet.WF] do
    let isForall := root == ``Inner.inferForall.WF
    let isLambda := root == ``Inner.inferLambda.WF
    let expectedAdmissions := if isForall then forallAdmissions
      else if isLambda then lambdaAdmissions else letAdmissions
    let expectedAxioms := if isForall then forallAxioms
      else if isLambda then lambdaAxioms else letAxioms
    let axioms ← collectAxioms root
    unless expectedAxioms.length == axioms.size && expectedAxioms.all axioms.contains do
      throwError "whole inference axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if let some info := environment.find? name then
        pending := pending ++ info.type.getUsedConstants
        if let some proof := info.value? (allowOpaque := true) then
          if proof.hasSorry then
            unless expectedAdmissions.contains name do throwError "unapproved inference admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ proof.getUsedConstants
    unless pending.isEmpty do throwError "inference traversal exceeded bound"
    unless expectedAdmissions.length == admissions.size && expectedAdmissions.all admissions.contains do
      throwError "inference admission manifest changed for {root}: {repr admissions}"
    let builders := if isForall then [``MLCtx.WF.mkForall_trS]
      else if isLambda then [``MLCtx.WF.mkLambda_trS, ``MLCtx.WF.mkForall_trS]
      else [``MLCtx.WF.mkLet_trS, ``MLCtx.WF.mkForall_trS]
    unless builders.all visited.contains do throwError "inference bypassed repaired builders: {root}"
    logInfo m!"{root}: {visited.size} dependencies; exact whole-inference admission/axiom manifests retained"

end TelescopeLetErasureTest
