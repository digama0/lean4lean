import Lean4Lean.TypeChecker

namespace Lean4Lean.Tests.ProjectionInference

open Lean Lean4Lean TypeChecker TypeChecker.Inner

structure Wrap (alpha : Type u) where
  value : alpha
  tag : Bool

run_meta do
  let env := (← getEnv).toKernelEnv
  let wrapNat := mkApp (mkConst ``Wrap [.zero]) (mkConst ``Nat)
  let constructor := mkAppN (mkConst ``Wrap.mk [.zero])
    #[mkConst ``Nat, mkNatLit 3, mkConst ``false]
  match TypeChecker.M.run env .safe {} [] {}
      (inferProj ``Wrap 0 constructor wrapNat).run with
  | .error exception =>
      throwError "projection inference failed: {
        ← (exception.toMessageData {}).toString}"
  | .ok type =>
      unless type == mkConst ``Nat do
        throwError "projection inference returned the wrong type"
  -- the last field
  match TypeChecker.M.run env .safe {} [] {}
      (inferProj ``Wrap 1 constructor wrapNat).run with
  | .error exception =>
      throwError "projection inference failed: {
        ← (exception.toMessageData {}).toString}"
  | .ok type =>
      unless type == mkConst ``Bool do
        throwError "projection inference returned the wrong type for the last field"
  -- past the fields: as in `type_checker::infer_proj`, the telescope walk reaches the
  -- structure type, which is not a binder, and the projection is rejected
  for idx in [2, 3, 10] do
    match TypeChecker.M.run env .safe {} [] {}
        (inferProj ``Wrap idx constructor wrapNat).run with
    | .error (.invalidProj ..) => pure ()
    | .error exception =>
        throwError "projection {idx} failed for the wrong reason: {
          ← (exception.toMessageData {}).toString}"
    | .ok _ => throwError "projection {idx} past the fields was accepted"

end Lean4Lean.Tests.ProjectionInference
