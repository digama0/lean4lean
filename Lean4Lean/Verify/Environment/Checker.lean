import Lean4Lean.Verify.Environment.Boundaries

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.defnInfo_safety (v : DefinitionVal) :
    (ConstantInfo.defnInfo v).safety = v.safety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  cases v.safety <;> rfl

theorem checkName.WF (mapWF : env.constants.WF) (name : Name) (allowPrimitive : Bool) :
    (Environment.checkName env name allowPrimitive).WF fun _ =>
      env.find? name = none ∧ (allowPrimitive = false → Environment.primitives.contains name = false) := by
  intro _ h
  have hn : env.contains name = false := by
    cases hfind : env.contains name
    · rfl
    · simp [Environment.checkName, hfind, (· >>= ·), Except.bind] at h
  change env.constants.contains name = false at hn
  rw [SMap.find?_isSome] at hn
  constructor
  · rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]
    cases hfind : env.constants.find? name <;> simp_all
  · intro ha
    cases hp : Environment.primitives.contains name
    · rfl
    · have hc : env.contains name = false := by
        change env.constants.contains name = false
        rw [SMap.find?_isSome]
        exact hn
      simp only [Environment.checkName, hc, ha, hp, ↓reduceIte] at h
      rw [show (pure PUnit.unit : Except Exception PUnit) = .ok PUnit.unit from rfl] at h
      contradiction

private theorem checkNoMVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVar env name e).WF fun _ => e.hasMVar = false := by
  intro _ h
  cases hmv : e.hasMVar
  · rfl
  · simp [Environment.checkNoMVar, hmv] at h

private theorem checkNoFVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoFVar env name e).WF fun _ => e.hasFVar = false := by
  intro _ h
  cases hfv : e.hasFVar
  · rfl
  · simp [Environment.checkNoFVar, hfv] at h

theorem checkNoMVarNoFVar.WF (env : Environment) (name : Name) (e : Expr) :
    (Environment.checkNoMVarNoFVar env name e).WF fun _ => e.FVarsIn fun _ => False := by
  unfold Environment.checkNoMVarNoFVar
  refine (checkNoMVar.WF env name e).bind fun _ hm =>
    (checkNoFVar.WF env name e).mono fun _ hf => ?_
  apply fvarsIn_iff.2
  refine ⟨?_, fvarsIn_iff_hasMVar.2 hm⟩
  intro fv hmem
  rw [fvarsList_eq_nil.2 hf] at hmem
  simp at hmem

private theorem Except.WF.trivial (x : Except ε α) : x.WF fun _ => True :=
  fun _ _ => True.intro

private theorem TypeChecker.M.WF.pureBind {c : TypeChecker.VContext}
    {s : TypeChecker.VState} {f : β → TypeChecker.M α} {Q} {x : β}
    (H : (f x).WF c s Q) : ((Pure.pure x : TypeChecker.M β) >>= f).WF c s Q := H

theorem checkConstantValCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (state : TypeChecker.VState := {}) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams) state fun _ _ =>
        ∃ ci' : VConstVal,
          ci.levelParams.length = ci'.uvars ∧
          TrExprS (ves.venv safety) ci.levelParams [] ci.type ci'.type ∧
          ci.name = ci'.name ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (allowPrimitive = false → Environment.primitives.contains ci.name = false) := by
  unfold checkConstantVal
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := safety)).map_wf ci.name allowPrimitive)).bind
    fun _ _ _ hname => ?_
  -- Duplicate level parameters are rejected operationally; no later proof needs that fact.
  refine (TypeChecker.M.WF.liftExcept (Except.WF.trivial _)).bind fun _ _ _ _ => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkNoMVarNoFVar.WF env ci.name ci.type)).bind fun _ _ _ hclosed => ?_
  have hclosed' : ci.type.FVarsIn (· ∈ (TypeChecker.VContext.mk' wf safety ci.levelParams).vlctx.fvars) := by
    simpa [TypeChecker.VContext.mk'] using hclosed
  refine (TypeChecker.checkType.WF hclosed').bind
    fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
  refine (TypeChecker.ensureSort.WF hsort).bind
    fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => .pure ?_
  obtain ⟨u, rfl⟩ := hsortEq
  cases hsort' with
  | sort hu =>
    refine ⟨{ name := ci.name, uvars := ci.levelParams.length, type := type' },
      rfl, htype, rfl, ?_, hname⟩
    exact ⟨_, hhasType.defeqU_r (wf.tr (safety := safety)).wf (by trivial) hdefeq.symm⟩

theorem checkConstantVal.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (hs : safety ≤ ci.safety)
    (state : TypeChecker.VState := {}) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams) state fun _ _ =>
        ∃ ci' : VConstVal, TrConstVal safety (ves.venv safety) ci ci' ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (allowPrimitive = false → Environment.primitives.contains ci.name = false) := by
  exact (checkConstantValCore.WF wf ci allowPrimitive state).mono fun _ _ _ h => by
    obtain ⟨ci', hu, ht, hn', hci, hn, hp⟩ := h
    exact ⟨ci', ⟨⟨hs, hu, ht⟩, hn'⟩, hci, hn, hp⟩

theorem checkBody.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (name : Name) (levelParams : List Name) (type value : Expr)
    (type' : VExpr) (hdeclType : TrExprS (ves.venv safety) levelParams [] type type')
    (state : TypeChecker.VState := {}) :
    ((do
      Environment.checkNoMVarNoFVar env name value
      let valueType ← TypeChecker.checkType value
      if !(← TypeChecker.isDefEq valueType type) then
        throw <| Exception.declTypeMismatch env decl valueType) : TypeChecker.M Unit).WF
      (.mk' wf safety levelParams) state fun _ _ =>
        ∃ value', TrExprS (ves.venv safety) levelParams [] value value' ∧
          (ves.venv safety).HasType levelParams.length [] value' type' := by
  refine (TypeChecker.M.WF.liftExcept
    (checkNoMVarNoFVar.WF env name value)).bind fun _ _ _ hclosed => ?_
  have hclosed' : value.FVarsIn
      (· ∈ (TypeChecker.VContext.mk' wf safety levelParams).vlctx.fvars) := by
    simpa [TypeChecker.VContext.mk'] using hclosed
  refine (TypeChecker.checkType.WF hclosed').bind
    fun valueType _ _ ⟨value', valueType', _, hvalue, hvalueType, hhasType⟩ => ?_
  refine (TypeChecker.isDefEq.WF hvalueType hdeclType).bind fun equal _ _ hequal => ?_
  split
  · exact .throw
  · rename_i hnot
    refine .pure ⟨value', hvalue, ?_⟩
    have heq : equal = true := by cases equal <;> simp_all
    exact hhasType.defeqU_r (wf.tr (safety := safety)).wf (by trivial) (hequal heq)

theorem checkTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : TheoremVal) :
    ((do
      checkConstantVal env v.toConstantVal
      if !(← TypeChecker.isProp v.type) then
        throw <| Exception.thmTypeIsNotProp env v.name v.type
      Environment.checkNoMVarNoFVar env v.name v.value
      let valueType ← TypeChecker.checkType v.value
      if !(← TypeChecker.isDefEq valueType v.type) then
        throw <| Exception.declTypeMismatch env (.thmDecl v) valueType) : TypeChecker.M Unit).WF
      (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ ci' : VDefVal, TrDefVal .safe (ves.venv .safe) (.thmInfo v) ci' ∧
          ci'.WF (ves.venv .safe) ∧
          (ves.venv .safe).HasType ci'.uvars [] ci'.type (.sort .zero) ∧
          env.find? v.name = none ∧ Environment.primitives.contains v.name = false := by
  refine (checkConstantVal.WF wf (.thmInfo v) false DefinitionSafety.le_rfl).bind
    fun _ state _ ⟨ci', htr, hci, hn, hnonprim⟩ => ?_
  refine (TypeChecker.isProp.WF htr.1.2.2).bind fun isProp state' _ hprop => ?_
  split
  · exact .throw
  · rename_i hnot
    have hisProp : isProp = true := by cases isProp <;> simp_all
    refine .pureBind <| (checkBody.WF wf (.thmDecl v) v.name v.levelParams v.type
      v.value ci'.type htr.1.2.2 state').mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => ?_
    let ci'' : VDefVal := { ci' with value := value' }
    refine ⟨ci'', ⟨htr, hvalue⟩, ?_, ?_, hn, hnonprim rfl⟩
    · change (ves.venv .safe).HasType ci'.uvars [] value' ci'.type
      rw [← htr.1.2.1]
      exact hvalueType
    · change (ves.venv .safe).HasType ci'.uvars [] ci'.type (.sort .zero)
      rw [← htr.1.2.1]
      exact hprop hisProp

theorem checkDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    ((do
      checkConstantVal env v.toConstantVal (← Environment.checkPrimitiveDef v)
      Environment.checkNoMVarNoFVar env v.name v.value
      let valueType ← TypeChecker.checkType v.value
      if !(← TypeChecker.isDefEq valueType v.type) then
        throw <| Exception.declTypeMismatch env (.defnDecl v) valueType) : TypeChecker.M Unit).WF
      (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ allow : Bool, ∃ ci' : VDefVal, PrimitiveResult (ves.venv .safe) v allow ∧
          v.levelParams.length = ci'.uvars ∧
          TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
          v.name = ci'.name ∧
          TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value ∧
          ci'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          (allow = false → Environment.primitives.contains v.name = false) := by
  refine (checkPrimitiveDef.WF wf v).bind fun allow state _ hp => ?_
  refine (checkConstantValCore.WF (safety := .safe) wf (.defnInfo v) allow state).bind
    fun _ state' _ ⟨ci', hu, ht, hname, hci, hfresh, hnonprim⟩ => ?_
  exact (checkBody.WF wf (.defnDecl v) v.name v.levelParams v.type v.value
    ci'.type ht state').mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => by
      let ci'' : VDefVal := { ci' with value := value' }
      refine ⟨allow, ci'', hp, hu, ht, hname, hvalue, ?_, hfresh, hnonprim⟩
      change (ves.venv .safe).HasType ci'.uvars [] value' ci'.type
      rw [← hu]
      exact hvalueType

/-- Verify the complete opaque-declaration check. The body is checked, so it is packaged into
the resulting `VDefVal`; `TrEnv'.opaque` consumes it. An opaque body still contributes no
definitional equality -- that is `TrEnv'.opaque` adding no `addDefEq`, not the body going
unrecorded. -/
theorem checkOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : OpaqueVal) :
    ((do
      checkConstantVal env v.toConstantVal
      Environment.checkNoMVarNoFVar env v.name v.value
      let valueType ← TypeChecker.checkType v.value
      if !(← TypeChecker.isDefEq valueType v.type) then
        throw <| Exception.declTypeMismatch env (.opaqueDecl v) valueType) : TypeChecker.M Unit).WF
      (.mk' wf .safe v.levelParams) {} fun _ _ =>
      ∃ ci' : VDefVal,
        v.levelParams.length = ci'.uvars ∧
        TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
        v.name = ci'.name ∧
        TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value ∧
        ci'.toVConstant.WF (ves.venv .safe) ∧
        ci'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
        Environment.primitives.contains v.name = false := by
  refine (checkConstantValCore.WF (safety := .safe) wf (.opaqueInfo v) false).bind
    fun _ state _ ⟨ci', hu, ht, hname, hci, hfresh, hnonprim⟩ => ?_
  exact (checkBody.WF wf (.opaqueDecl v) v.name v.levelParams v.type v.value
    ci'.type ht state).mono fun _ _ _ ⟨value', hvalue, hvalueType⟩ => by
      let ci'' : VDefVal := { ci' with value := value' }
      refine ⟨ci'', hu, ht, hname, hvalue, hci, ?_, hfresh, hnonprim rfl⟩
      rwa [VDefVal.WF, ← hu]
