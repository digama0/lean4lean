import Lean4Lean.Theory.Typing.SimultaneousNormalSubstitution
import Lean4Lean.Theory.Typing.Meta
import Lean.Util.CollectAxioms

namespace NormalSubstitutionTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Params
variable [parameters : Params]

def locals : List VExpr :=
  [.bvar 2, .bvar 1, .forallE (.bvar 0) (.sort .zero), .sort .zero]
def source : List VExpr := .bvar 3 :: locals

theorem localsWF : OnCtx locals (env.IsType univs) := by
  unfold locals
  exact ⟨⟨⟨⟨trivial, _, HasType.sort (by trivial)⟩,
    _, HasType.forallE (HasType.bvar .zero) (HasType.sort (by trivial))⟩,
    _, HasType.bvar (.succ .zero)⟩, _, HasType.bvar (.succ (.succ .zero))⟩

theorem propositionTyped : env.HasType univs locals (.bvar 3) (.sort .zero) := by unfold locals; type_tac
theorem leftTyped : env.HasType univs locals (.bvar 1) (.bvar 3) := by unfold locals; type_tac
theorem rightTyped : env.HasType univs locals (.bvar 0) (.bvar 3) := by unfold locals; type_tac
theorem argumentsNormal : NormalEq locals (.bvar 1) (.bvar 0) :=
  .proofIrrel propositionTyped leftTyped rightTyped

def domain : VExpr := .app (.bvar 3) (.bvar 0)
def leftDomain : VExpr := .app (.bvar 2) (.bvar 1)
def rightDomain : VExpr := .app (.bvar 2) (.bvar 0)
def identity : VExpr := .lam domain (.bvar 0)
def identityType : VExpr := .forallE domain domain.lift

theorem sourceWF : OnCtx source (env.IsType univs) := ⟨localsWF, _, propositionTyped⟩
theorem domainTyped : env.HasType univs source domain (.sort .zero) := by
  unfold source locals domain
  type_tac

theorem identityTyped : env.HasType univs source identity identityType :=
  domainTyped.lam (HasType.bvar .zero)

theorem etaBodyTyped {context : List VExpr} {function domain body : VExpr}
    (typed : env.HasType univs context function (.forallE domain body)) :
    env.HasType univs (domain :: context) (.app function.lift (.bvar 0)) body := by
  have lifted := typed.weak henv.ordered (B := domain)
  change env.HasType univs (domain :: context) function.lift
    (.forallE domain.lift (body.liftN 1 1)) at lifted
  simpa only [HasType, VExpr.instN_bvar0] using lifted.appDF (HasType.bvar .zero)

def etaIdentity : VExpr := .lam domain (.app identity.lift (.bvar 0))

theorem bothEtaRight : NormalEq locals (identity.inst (.bvar 1)) (etaIdentity.inst (.bvar 0)) := by
  have normal : NormalEq source identity etaIdentity := .etaR identityTyped (.refl (etaBodyTyped identityTyped))
  exact NormalEq.instDF localsWF propositionTyped leftTyped argumentsNormal normal

theorem bothEtaLeft : NormalEq locals (etaIdentity.inst (.bvar 1)) (identity.inst (.bvar 0)) := by
  have normal : NormalEq source etaIdentity identity := .etaL identityTyped (.refl (etaBodyTyped identityTyped))
  exact NormalEq.instDF localsWF propositionTyped leftTyped argumentsNormal normal

theorem bothLambda : NormalEq locals (identity.inst (.bvar 1)) (identity.inst (.bvar 0)) := by
  have normal : NormalEq source identity identity := .lamDF domainTyped domainTyped (.refl (HasType.bvar .zero))
  exact NormalEq.instDF localsWF propositionTyped leftTyped argumentsNormal normal

theorem bothReflexive : NormalEq locals (identity.inst (.bvar 1)) (identity.inst (.bvar 0)) :=
  NormalEq.instDF localsWF propositionTyped leftTyped argumentsNormal (.refl identityTyped)

theorem bothForall : NormalEq locals (identityType.inst (.bvar 1)) (identityType.inst (.bvar 0)) := by
  have bodyTyped := domainTyped.weak henv.ordered (B := domain)
  have normal : NormalEq source identityType identityType :=
    .forallEDF domainTyped (.refl domainTyped) bodyTyped (.refl bodyTyped)
  exact NormalEq.instDF localsWF propositionTyped leftTyped argumentsNormal normal

theorem bothApplication : NormalEq locals (domain.inst (.bvar 1)) (domain.inst (.bvar 0)) := by
  have functionTyped : env.HasType univs source (.bvar 3) (.forallE (.bvar 4) (.sort .zero)) := by
    unfold source locals; type_tac
  have valueTyped : env.HasType univs source (.bvar 0) (.bvar 4) := by unfold source locals; type_tac
  have normal : NormalEq source domain domain := .appDF functionTyped functionTyped valueTyped valueTyped
    (.refl functionTyped) (.refl valueTyped)
  exact NormalEq.instDF localsWF propositionTyped leftTyped argumentsNormal normal

example : domain.inst (.bvar 1) = leftDomain := rfl
example : domain.inst (.bvar 0) = rightDomain := rfl
example : leftDomain ≠ rightDomain := by intro equal; cases equal
example : identity.inst (.bvar 1) = .lam leftDomain (.bvar 0) := rfl
example : identity.inst (.bvar 0) = .lam rightDomain (.bvar 0) := rfl

-- Two independent variable images also change in a single simultaneous map.
def twiceLeft : VExpr.Subst := (VExpr.Subst.one (.bvar 1)).cons (.bvar 1)
def twiceRight : VExpr.Subst := (VExpr.Subst.one (.bvar 0)).cons (.bvar 0)

theorem doubleSubstitution : NormalSubstitution locals twiceLeft twiceRight (.bvar 4 :: source) := by
  have first := NormalSubstitution.one localsWF propositionTyped leftTyped argumentsNormal
  refine ⟨Ctx.SubstEq.cons (u := .zero) (σ := twiceLeft) (σ' := twiceRight) first.typed ?_ ?_, ?_⟩
  · unfold source locals
    type_tac
  · simpa [twiceLeft, twiceRight, VExpr.Subst.head, VExpr.Subst.tail, VExpr.Subst.cons,
      VExpr.inst_eq, VExpr.subst, VExpr.Subst.id] using
      (argumentsNormal.defeq localsWF).of_l henv localsWF leftTyped
  · intro index type lookup
    cases lookup with
    | zero => exact argumentsNormal
    | succ lookup => exact first.normal lookup

def twoVariableBody : VExpr :=
  .forallE (.app (.bvar 4) (.bvar 0)) (.app (.bvar 5) (.bvar 2))

theorem twoVariableImages : NormalEq locals
    (twoVariableBody.subst twiceLeft) (twoVariableBody.subst twiceRight) := by
  apply NormalSubstitution.expression (type := .sort (.imax .zero .zero)) localsWF doubleSubstitution
  unfold twoVariableBody
  apply HasType.forallE
  · exact HasType.app' (B := .sort .zero) (by unfold source locals; type_tac)
      (by unfold source locals; type_tac) rfl
  · exact HasType.app' (B := .sort .zero) (by unfold source locals; type_tac)
      (by unfold source locals; type_tac) rfl

example : twoVariableBody.subst twiceLeft =
    .forallE (.app (.bvar 2) (.bvar 1)) (.app (.bvar 3) (.bvar 2)) := rfl
example : twoVariableBody.subst twiceRight =
    .forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.bvar 1)) := rfl

run_meta
  let environment ← getEnv
  let roots := [``NormalSubstitution.lift_at, ``NormalSubstitution.lift, ``NormalSubstitution.expression, ``NormalEq.substDF, ``NormalSubstitution.id, ``NormalSubstitution.one, ``NormalEq.instDF, ``localsWF, ``propositionTyped, ``leftTyped, ``rightTyped, ``argumentsNormal, ``sourceWF, ``domainTyped, ``identityTyped, ``etaBodyTyped, ``bothEtaRight, ``bothEtaLeft, ``bothLambda, ``bothReflexive, ``bothForall, ``bothApplication, ``doubleSubstitution, ``twoVariableImages]
  let forbidden := [``NormalEq.parRed, ``NormalEq.parRedS, ``IsDefEq.church_rosser,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, ``IsDefEqU.weakN_iff, ``NormalEq.weakN_iff, ``NormalEq.weakN_inv_DFC,
    ``ParRed.weakN_inv, ``NormalEq.trans,
    `Lean4Lean.TrProj, `Lean4Lean.TrProj.weak', `Lean4Lean.TrProj.instN, ``Classical.choice]
  let manifests : List (Name × List Name × List Name) := [
    (`Lean4Lean.VEnv.NormalSubstitution.lift_at, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.addInduct_WF], [`propext, `sorryAx, `Quot.sound]),
    (`Lean4Lean.VEnv.NormalSubstitution.lift, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.addInduct_WF], [`propext, `sorryAx, `Quot.sound]),
    (`Lean4Lean.VEnv.NormalSubstitution.expression, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.addInduct_WF], [`propext, `sorryAx, `Quot.sound]),
    (`Lean4Lean.VEnv.NormalEq.substDF, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.addInduct_WF], [`propext, `sorryAx, `Quot.sound]),
    (`Lean4Lean.VEnv.NormalSubstitution.id, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.addInduct_WF], [`propext, `sorryAx, `Quot.sound]),
    (`Lean4Lean.VEnv.NormalSubstitution.one, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`Lean4Lean.VEnv.NormalEq.instDF, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.localsWF, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.propositionTyped, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.leftTyped, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.rightTyped, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.argumentsNormal, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.sourceWF, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.domainTyped, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.identityTyped, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.etaBodyTyped, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.addInduct_WF], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.bothEtaRight, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.bothEtaLeft, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.bothLambda, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.bothReflexive, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.bothForall, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.bothApplication, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.doubleSubstitution, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound]),
    (`NormalSubstitutionTest.twoVariableImages, [`Lean4Lean.VEnv.addInduct, `Lean4Lean.VInductDecl.WF, `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.addInduct_WF, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified], [`propext, `sorryAx, `Quot.sound])]
  for root in roots do
    let some (_, expectedAdmissions, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing proof {root}"
    if proof.hasSorry then throwError "direct admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut admissions : Array Name := #[]
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden dependency {name} in {root}"
      if let some declaration := environment.find? name then
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if declaration.type.hasSorry then
          throwError "admitted declaration type {name} in {root}"
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then
            unless expectedAdmissions.contains name do
              throwError "unapproved admission {name} in {root}"
            admissions := admissions.push name
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "traversal exceeded bound"
    unless admissions.size == expectedAdmissions.length && expectedAdmissions.all admissions.contains do
      throwError "admission manifest changed for {root}: {repr admissions}"
    let required :=
      if root == ``NormalSubstitution.lift_at then [``Ctx.SubstEq.lift_at, ``NormalEq.weakN]
      else if root == ``NormalSubstitution.expression then [``NormalSubstitution.lift, ``NormalEq.lamDF, ``NormalEq.forallEDF, ``NormalEq.appDF]
      else if root == ``NormalEq.substDF then [``NormalSubstitution.expression, ``NormalSubstitution.lift_at, ``NormalEq.etaR, ``NormalEq.etaL]
      else if root == ``NormalEq.instDF then [``NormalEq.substDF, ``NormalSubstitution.one]
      else if root == ``bothEtaRight then [``NormalEq.instDF, ``NormalEq.etaR, ``NormalSubstitution.lift_at]
      else if root == ``bothEtaLeft then [``NormalEq.instDF, ``NormalEq.etaL]
      else if root == ``bothLambda then [``NormalEq.instDF, ``NormalEq.lamDF]
      else if root == ``bothReflexive then [``NormalEq.instDF, ``NormalSubstitution.expression]
      else if root == ``bothForall then [``NormalEq.instDF, ``NormalEq.forallEDF]
      else if root == ``bothApplication then [``NormalEq.instDF, ``NormalEq.appDF]
      else if root == ``twoVariableImages then [``NormalSubstitution.expression, ``doubleSubstitution]
      else []
    unless required.all visited.contains do
      throwError "control bypassed a required proof in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|{repr admissions}|{repr axioms}"

end NormalSubstitutionTest
