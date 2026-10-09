import Lean4Lean.Verify.Environment.Primitive

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.defnInfo_safety (v : DefinitionVal) :
    (ConstantInfo.defnInfo v).safety = v.safety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  cases v.safety <;> rfl

theorem checkName.WF (mapWF : env.constants.WF) (name : Name) (allowPrimitive : Bool) :
    (Environment.checkName env name allowPrimitive).WF fun _ =>
      env.find? name = none ∧ (Environment.primitives.contains name → allowPrimitive) := by
  intro _ h
  have hn : env.contains name = false := by
    cases hfind : env.contains name <;> [rfl; skip]
    simp [Environment.checkName, hfind, (· >>= ·), Except.bind] at h
  change env.constants.contains name = false at hn
  rw [SMap.find?_isSome] at hn
  refine ⟨?_, fun ha => ?_⟩
  · rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]
    cases hfind : env.constants.find? name <;> simp_all
  · have hc : env.constants.contains name = false := by rwa [SMap.find?_isSome]
    simpa only [Environment.checkName, Kernel.Environment.contains, hc, ↓reduceIte, ha,
      ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false,
      show (pure PUnit.unit : Except Exception PUnit) = .ok PUnit.unit from rfl] using h

private theorem checkNoMVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVar env name e).WF fun _ => e.hasMVar = false := by
  intro _ h; cases hmv : e.hasMVar <;> [rfl; simp [Environment.checkNoMVar, hmv] at h]

private theorem checkNoFVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoFVar env name e).WF fun _ => e.hasFVar = false := by
  intro _ h; cases hfv : e.hasFVar <;> [rfl; simp [Environment.checkNoFVar, hfv] at h]

theorem checkNoMVarNoFVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVarNoFVar env name e).WF fun _ => e.FVarsIn fun _ => False := by
  refine (checkNoMVar.WF env name e).bind fun _ hm =>
    (checkNoFVar.WF env name e).mono fun _ hf => ?_
  refine fvarsIn_iff.2 ⟨fun fv hmem => ?_, fvarsIn_iff_hasMVar.2 hm⟩
  rw [fvarsList_eq_nil.2 hf] at hmem
  simp at hmem

private theorem Except.WF.trivial (x : Except ε α) : x.WF fun _ => True :=
  fun _ _ => True.intro

private theorem TypeChecker.M.WF.pureBind {c : VContext}
    {s : State} {f : β → M α} {Q} {x : β}
    (H : (f x).WF c s Q) : ((Pure.pure x : M β) >>= f).WF c s Q := H

/-- The part of `checkConstantVal` that does not check the name. `addDefinition` runs it before
`Primitive.checkDef`, so that the latter's `isDefEq` calls act on terms already known to be well
typed, and defers the name check until the primitive verdict is available. -/
theorem checkConstantValBody.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env)
    (ci : ConstantInfo) (state : State := {}) :
    (checkConstantValBody env ci.toConstantVal).WF (.mk' wf safety ci.levelParams fuel) state fun _ _ =>
      ∃ ci' : VConstVal,
        ci.levelParams.length = ci'.uvars ∧
        TrExprS (ves.venv safety) ci.levelParams [] ci.type ci'.type ∧
        ci.name = ci'.name ∧
        ci'.toVConstant.WF (ves.venv safety) := by
  -- Duplicate level parameters are rejected operationally; no later proof needs that fact.
  refine (M.WF.liftExcept (Except.WF.trivial _)).bind fun _ _ _ _ => ?_
  refine (M.WF.liftExcept
    (checkNoMVarNoFVar.WF env ci.name ci.type)).bind fun _ _ _ hclosed => ?_
  have hclosed' : ci.type.FVarsIn
      (· ∈ (VContext.mk' wf safety ci.levelParams fuel).vlctx.fvars) := by
    simpa [VContext.mk', VContext.mk1, VContext.mkCheckingValid, VContext.mkChecking] using hclosed
  refine (checkType.WF hclosed').bind fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
  refine (ensureSort.WF hsort).bind fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => .pure ?_
  obtain ⟨u, rfl⟩ := hsortEq
  cases hsort' with | sort hu
  refine ⟨{ name := ci.name, uvars := ci.levelParams.length, type := type' }, rfl, htype, rfl, ?_⟩
  exact ⟨_, hhasType.defeqU_r (wf.tr (safety := safety)).wf (by trivial) hdefeq.symm⟩

theorem checkConstantValCore.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (state : State := {}) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams fuel) state fun _ _ =>
        ∃ ci' : VConstVal,
          ci.levelParams.length = ci'.uvars ∧
          TrExprS (ves.venv safety) ci.levelParams [] ci.type ci'.type ∧
          ci.name = ci'.name ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (Environment.primitives.contains ci.name → allowPrimitive) := by
  refine (M.WF.liftExcept
    (checkName.WF (wf.tr (safety := safety)).map_wf ci.name allowPrimitive)).bind
    fun _ _ _ hname => ?_
  exact (checkConstantValBody.WF wf ci _).mono fun _ _ _ ⟨ci', hu, ht, hn', hci⟩ =>
    ⟨ci', hu, ht, hn', hci, hname⟩

theorem checkConstantVal.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (hs : safety ≤ ci.safety) (state : State := {}) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams fuel) state fun _ _ =>
        ∃ ci' : VConstVal, TrConstVal safety (ves.venv safety) ci ci' ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (Environment.primitives.contains ci.name → allowPrimitive) :=
  (checkConstantValCore.WF wf ci allowPrimitive state).mono
    fun _ _ _ ⟨ci', hu, ht, hn', hci, hn, hp⟩ => ⟨ci', ⟨⟨hs, hu, ht⟩, hn'⟩, hci, hn, hp⟩

def checkBodyCore (env : Environment) (decl : Declaration) (type value : Expr) : M Unit := do
  let valueType ← checkType value
  if !(← isDefEq valueType type) then
    throw <| Exception.declTypeMismatch env decl valueType

/-- The body check proper, with the mvar/fvar check already discharged. `addDefinition` runs
the two in the same `do` block for a safe definition but splits them for an unsafe one (the
mvar/fvar check happens before the constant is added as an axiom), so they are verified
separately.

Stated against a single-level model (`VEnvAt`): a mutual block's bodies are checked in the
temporary environment holding the whole block as axioms, which has no model at every level. -/
theorem checkBodyCore.WF {env : Environment} {venv : VEnv} {fuel : FuelConfig} (wf : VEnvAt env safety venv)
    (decl : Declaration) (levelParams : List Name) (type value : Expr)
    (type' : VExpr) (hdeclType : TrExprS venv levelParams [] type type')
    (hclosed : value.FVarsIn fun _ => False) (state : State := {}) :
    (checkBodyCore env decl type value).WF (.mk1 wf levelParams fuel) state fun _ _ =>
      ∃ value', TrExprS venv levelParams [] value value' ∧
        venv.HasType levelParams.length [] value' type' := by
  have hclosed' : value.FVarsIn (· ∈ (VContext.mk1 wf levelParams fuel).vlctx.fvars) := by
    simpa [VContext.mk1, VContext.mkCheckingValid, VContext.mkChecking] using hclosed
  refine (checkType.WF hclosed').bind
    fun valueType _ _ ⟨value', _, _, hvalue, hvalueType, hhasType⟩ => ?_
  refine (isDefEq.WF hvalueType hdeclType).bind fun equal _ _ hequal => ?_
  split <;> [exact .throw; rename_i hnot]
  exact .pure ⟨value', hvalue, hhasType.defeqU_r wf.tr.wf trivial (hequal (by simpa using hnot))⟩

def checkBody (env : Environment) (name : Name)
    (type value : Expr) (decl : Declaration) : M Unit := do
  Environment.checkNoMVarNoFVar env name value
  checkBodyCore env decl type value

theorem checkBody.WF {env : Environment} {fuel : FuelConfig} (wf : VEnvAt env safety venv)
    (decl : Declaration) (name : Name) (value : Expr)
    (hdeclType : TrExprS venv levelParams [] type type')
    (state : State := {}) :
    (checkBody env name type value decl).WF (.mk1 wf levelParams fuel) state fun _ _ =>
      ∃ value', TrExprS venv levelParams [] value value' ∧
        venv.HasType levelParams.length [] value' type' :=
  (M.WF.liftExcept (checkNoMVarNoFVar.WF env name value)).bind fun _ _ _ hclosed =>
  checkBodyCore.WF wf decl levelParams type value type' hdeclType hclosed _

def checkTheorem (env : Environment) (v : TheoremVal) : M Unit := do
  checkConstantVal env v.toConstantVal
  if !(← isProp v.type) then
    throw <| Exception.thmTypeIsNotProp env v.name v.type
  Environment.checkNoMVarNoFVar env v.name v.value
  let valueType ← checkType v.value
  if !(← isDefEq valueType v.type) then
    throw <| Exception.declTypeMismatch env (.thmDecl v) valueType

theorem checkTheorem.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env) (v : TheoremVal) :
    (checkTheorem env v).WF (.mk' wf .safe v.levelParams fuel) {} fun _ _ =>
      ∃ ci' : VDefVal, TrDefVal .safe (ves.venv .safe) (.thmInfo v) ci' ∧
        ci'.WF (ves.venv .safe) ∧
        (ves.venv .safe).HasType ci'.uvars [] ci'.type (.sort .zero) ∧
        env.find? v.name = none ∧ Environment.primitives.contains v.name = false := by
  refine (checkConstantVal.WF wf (.thmInfo v) false DefinitionSafety.le_rfl).bind
    fun _ state _ ⟨ci', htr, hci, hn, hnonprim⟩ => ?_
  refine (isProp.WF htr.1.2.2).bind fun isProp state' _ hprop => ?_
  split <;> [exact .throw; rename_i hnot]
  have hisProp : isProp = true := by cases isProp <;> simp_all
  refine .pureBind <| checkBody.WF _ _ _ _ htr.1.2.2 _
    |>.mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => ?_
  let ci'' : VDefVal := { ci' with value := value' }
  refine ⟨ci'', ⟨htr, hvalue⟩, ?_, htr.1.2.1 ▸ hprop hisProp, hn, ?_⟩
  · rwa [VDefVal.WF, ← htr.1.2.1]
  · simp at hnonprim; exact hnonprim

/-- The type and the body, with neither the name check nor the primitive check. -/
theorem checkDefinitionBody.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env)
    (v : DefinitionVal) (state : State := {}) :
    (checkDefinitionBody env v).WF (.mk' wf safety v.levelParams fuel) state fun _ _ => ∃ ci' : VDefVal,
      v.levelParams.length = ci'.uvars ∧
      TrExprS (ves.venv safety) v.levelParams [] v.type ci'.type ∧
      v.name = ci'.name ∧
      TrExprS (ves.venv safety) v.levelParams [] v.value ci'.value ∧
      ci'.WF (ves.venv safety) := by
  refine (checkConstantValBody.WF wf (.defnInfo v) state).bind
    fun _ state' _ ⟨ci', hu, ht, hname, hci⟩ => ?_
  exact (checkBody.WF _ _ _ _ ht _).mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ =>
    ⟨{ ci' with value := value' }, hu, ht, hname, hvalue, (hu ▸ hvalueType :)⟩

def checkDefinition (env : Environment) (v : DefinitionVal) : M Unit := do
  checkDefinitionBody env v
  Environment.checkName env v.name (← Primitive.checkDef v)

theorem checkDefinition.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env)
    (v : DefinitionVal) :
    (checkDefinition env v).WF (.mk' wf .safe v.levelParams fuel) {} fun _ _ => ∃ ci' : VDefVal,
      (Environment.primitives.contains v.name → Primitive.PrimitiveResult (ves.venv .safe) v ci') ∧
      v.levelParams.length = ci'.uvars ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
      v.name = ci'.name ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value ∧
      ci'.WF (ves.venv .safe) ∧ env.find? v.name = none := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state _ ⟨ci', hu, ht, hname, hvalue, hci⟩ => ?_
  refine (Primitive.checkDef.WF wf v ci' hu ht hvalue hci state).bind fun allow state' _ hp => ?_
  exact (M.WF.liftExcept (checkName.WF (wf.tr (safety := .safe)).map_wf v.name allow)).mono
    fun _ _ _ hn => ⟨ci', hp ∘ hn.2, hu, ht, hname, hvalue, hci, hn.1⟩

def checkOpaque (env : Environment) (v : OpaqueVal) : M Unit := do
  checkConstantVal env v.toConstantVal
  Environment.checkNoMVarNoFVar env v.name v.value
  let valueType ← checkType v.value
  if !(← isDefEq valueType v.type) then
    throw <| Exception.declTypeMismatch env (.opaqueDecl v) valueType

/-- Verify the complete opaque-declaration check. The body is checked, so it is packaged into
the resulting `VDefVal`; `TrEnv'.opaque` consumes it. An opaque body still contributes no
definitional equality -- that is `TrEnv'.opaque` adding no `addDefEq`, not the body going
unrecorded. -/
theorem checkOpaque.WF {env : Environment} {ves : VEnvs} {fuel : FuelConfig} (wf : ves.WF env) (v : OpaqueVal) :
    (checkOpaque env v).WF (.mk' wf .safe v.levelParams fuel) {} fun _ _ => ∃ ci' : VDefVal,
      v.levelParams.length = ci'.uvars ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
      v.name = ci'.name ∧
      TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value ∧
      ci'.toVConstant.WF (ves.venv .safe) ∧
      ci'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
      Environment.primitives.contains v.name = false := by
  refine (checkConstantValCore.WF wf (.opaqueInfo v) false).bind
    fun _ state _ ⟨ci', hu, ht, hname, hci, hfresh, hnonprim⟩ => ?_
  refine checkBody.WF _ _ _ _ ht _ |>.mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => ?_
  refine ⟨{ ci' with value := value' }, hu, ht, hname, hvalue, hci, ?_, hfresh, ?_⟩
  · rwa [VDefVal.WF, ← hu]
  · simp at hnonprim; exact hnonprim
