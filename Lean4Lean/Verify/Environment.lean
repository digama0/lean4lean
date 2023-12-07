import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
open Lean

def isAsSafeAs : DefinitionSafety → ConstantInfo → Bool
  | .unsafe, _ => true
  | .partial, ci => !ci.isUnsafe
  | .safe, ci => !ci.isUnsafe && !ci.isPartial

variable (safety : DefinitionSafety) (ci : ConstantInfo) in
inductive TrConstant : Option VConstant → Prop where
  | safe : isAsSafeAs safety ci →
    ci.levelParams.length = ci'.uvars →
    TrExpr ci.levelParams [] ci.type ci'.type →
    TrConstant (some ci')
  | «unsafe» : ¬isAsSafeAs safety ci → TrConstant none

def TrRecDefEq : RecursorVal → RecursorRule → VDefEq → Prop := sorry

def TrDefEq : ConstantInfo → VDefEq → Prop
  | .defnInfo ci, df => ∃ ty' val',
    TrExpr ci.levelParams [] ci.type ty' ∧
    TrExpr ci.levelParams [] ci.value val' ∧
    df = VDefVal.toDefEq ⟨⟨⟨ci.levelParams.length, ty'⟩, ci.name⟩, val'⟩
  | .quotInfo _, df => df = quotDefEq
  | .recInfo ci, df => ∃ rule ∈ ci.rules, TrRecDefEq ci rule df
  | _, _ => False

structure TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop where
  constants : env.find? n = some ci →
    ∃ ci', TrConstant safety ci ci' ∧ venv.constants n = some ci'
  defeqs : venv.defeqs df ↔ ∃ ci, isAsSafeAs safety ci ∧ TrDefEq ci df
