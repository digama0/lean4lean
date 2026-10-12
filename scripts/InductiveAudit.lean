import Lean4Lean.Verify.Inductive.Dispatch
import Lean4Lean.Verify.Inductive.Nested.Install.Extension
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.CanonicalEq
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.ConstructorCaptureTransport
import Lean4Lean.Verify.Replay
import Lean4Lean.Theory.Typing.BVarConversion
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.EtaOpening

/-! Audit the transitive dependency closure, including opaque theorem bodies.
Run through `scripts/check-inductive-audit.py`; this file emits one JSON record
per root. A successful Lean build alone does not check these obligations. -/

open Lean Meta Elab Command

private structure AuditDependency where
  name : String
  path : Array String
  deriving ToJson

private structure AuditReport where
  root : String
  visited : Nat
  axioms : Array AuditDependency
  sorrySources : Array AuditDependency
  deriving ToJson

private def dependencyPath (parent : Std.HashMap Name Name) (name : Name) : Array String := Id.run do
  let mut path := #[name.toString]
  let mut current := name
  for _ in [:parent.size] do
    let some previous := parent[current]? | break
    if previous == current then break
    path := path.push previous.toString
    current := previous
  return path.reverse

elab "#inductive_audit " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let root ← liftCoreM <| realizeGlobalConstNoOverload id
    let mut parent : Std.HashMap Name Name := ({} : Std.HashMap Name Name).insert root root
    let mut queue := #[root]
    let mut i := 0
    let mut axioms := #[]
    let mut sorrySources := #[]
    while i < queue.size do
      let name := queue[i]!
      i := i + 1
      let some ci := env.find? name | throwError "missing dependency {name}"
      let dependency := { name := name.toString, path := dependencyPath parent name : AuditDependency }
      let mut deps := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      match ci with
      | .axiomInfo _ => axioms := axioms.push dependency
      | .inductInfo v => deps := deps ++ v.ctors.toArray
      | .recInfo v => for rule in v.rules do deps := deps ++ rule.rhs.getUsedConstants
      | .ctorInfo v => deps := deps.push v.induct
      | _ => pure ()
      if deps.contains ``sorryAx then sorrySources := sorrySources.push dependency
      for dep in deps do
        unless parent.contains dep do
          parent := parent.insert dep name
          queue := queue.push dep
    let report := { root := root.toString, visited := queue.size, axioms, sorrySources : AuditReport }
    liftIO <| IO.println s!"INDUCTIVE_AUDIT {(toJson report).compress}"


-- The top-level verification theorems: checked addition of
-- every declaration form, the inductive pipelines, the checker, the realizability of canonical
-- `Eq`, and the replay driver.
#inductive_audit Lean4Lean.addDecl.WF
#inductive_audit Lean4Lean.addQuot.WF
#inductive_audit Lean4Lean.VerifyInductive.addInductiveDeclaration.preserves
#inductive_audit Lean4Lean.VerifyInductive.Environment.addInductive.inductiveExtensionWF
#inductive_audit Lean4Lean.VerifyInductive.Environment.addInductive.primitiveInductiveExtensionWF
#inductive_audit Lean4Lean.VerifyInductive.Environment.addInductiveAfterLowering.nestedInductiveExtensionWF
#inductive_audit Lean4Lean.TypeChecker.whnf.WF
#inductive_audit Lean4Lean.TypeChecker.Inner.reduceRecursor.WF
#inductive_audit Lean4Lean.VerifyInductive.RecursorConstruction.typeTranslations
#inductive_audit Lean4Lean.addDecl.preludeEq_hasCanonicalEq

-- The replay driver (`Lean4Lean/Verify/Replay.lean`).
#inductive_audit Lean4Lean.Replay.replayFresh.WF
#inductive_audit Lean4Lean.Replay.replayFresh.WF_target
#inductive_audit Lean4Lean.Replay.replayPure.WF_fromImports
#inductive_audit Lean4Lean.Replay.Replayed.foldlM

-- Generator and specification definitions: strict roots.
#inductive_audit Lean4Lean.VEnv.DefinitionRegistered
#inductive_audit Lean4Lean.VEnv.DefinitionPattern
#inductive_audit Lean4Lean.InductiveSignature.RecursorData.compilationEntries
#inductive_audit Lean.Level.paramsIn
#inductive_audit Lean.Expr.levelParamsIn
#inductive_audit Lean4Lean.InductiveSignature.TrRestoredCompilation
#inductive_audit Lean4Lean.InductiveSignature.Restoration.expr
#inductive_audit Lean4Lean.CompiledInductive
#inductive_audit Lean4Lean.InductiveSignature.Instance.equation
#inductive_audit Lean4Lean.InductiveSignature.Compiles
#inductive_audit Lean4Lean.InductiveSignature.TrRecursorVal
#inductive_audit Lean4Lean.InductiveSignature.RecursorData.singletonEquation
#inductive_audit Lean4Lean.VEnv.RecursorRegistered
#inductive_audit Lean4Lean.VEnv.HasCanonicalEq

-- Foundational lemmas: strict roots
-- (`FOUNDATION_ROOTS` in `scripts/check-inductive-audit.py`).
#inductive_audit Lean4Lean.VEnv.IsDefEq.strong
#inductive_audit Lean4Lean.VEnv.IsDefEqStrong.subst
#inductive_audit Lean4Lean.VEnv.IsDefEq.transport_bvar
#inductive_audit Lean4Lean.VEnv.ConstructorCaptureReplay.transport
#inductive_audit Lean4Lean.VEnv.HasType.etaOpen_wf
#inductive_audit Lean4Lean.VEnv.HasType.etaOpen_defeq
#inductive_audit Lean4Lean.VEnv.IsDefEq.etaOpen_wrapLams
