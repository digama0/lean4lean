import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Environment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

theorem checkName.WF (mapWF : env.constants.WF) (name : Name) (allowPrimitive : Bool) :
    (Environment.checkName env name allowPrimitive).WF fun _ => env.find? name = none := by
  intro _ h
  have hn : env.contains name = false := by
    cases hfind : env.contains name
    · rfl
    · simp [Environment.checkName, hfind, (· >>= ·), Except.bind] at h
  change env.constants.contains name = false at hn
  rw [SMap.find?_isSome] at hn
  rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]
  cases hfind : env.constants.find? name <;> simp_all

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

theorem checkConstantVal.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (allowPrimitive : Bool) (hs : safety ≤ ci.safety) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams) {} fun _ _ =>
        ∃ ci' : VConstVal, TrConstVal safety (ves.venv safety) ci ci' ∧ ci'.toVConstant.WF (ves.venv safety) := by
  unfold checkConstantVal
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := safety)).map_wf ci.name allowPrimitive)).bind
    fun _ _ _ _ => ?_
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
    refine ⟨{ name := ci.name, uvars := ci.levelParams.length, type := type' }, ?_, ?_⟩
    · exact ⟨⟨hs, rfl, htype⟩, rfl⟩
    · exact ⟨_, hhasType.defeqU_r (wf.tr (safety := safety)).wf (by trivial) hdefeq.symm⟩

theorem checkValue.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (ci : ConstantInfo) (ci' : VConstVal)
    (hci : TrConstVal safety (ves.venv safety) ci ci') :
    ((do
      Environment.checkNoMVarNoFVar env ci.name ci.value!
      let valueType ← TypeChecker.checkType ci.value!
      if !(← TypeChecker.isDefEq valueType ci.type) then
        throw <| Exception.declTypeMismatch env decl valueType) : TypeChecker.M Unit).WF
      (.mk' wf safety ci.levelParams) {} fun _ _ =>
        ∃ ci'' : VDefVal, TrDefVal safety (ves.venv safety) ci ci'' ∧ ci''.WF (ves.venv safety) := by
  refine (TypeChecker.M.WF.liftExcept
    (checkNoMVarNoFVar.WF env ci.name ci.value!)).bind fun _ _ _ hclosed => ?_
  have hclosed' : ci.value!.FVarsIn
      (· ∈ (TypeChecker.VContext.mk' wf safety ci.levelParams).vlctx.fvars) := by
    simpa [TypeChecker.VContext.mk'] using hclosed
  refine (TypeChecker.checkType.WF hclosed').bind
    fun valueType _ _ ⟨value', type', _, hvalue, htype, hhasType⟩ => ?_
  refine (TypeChecker.isDefEq.WF htype hci.1.2.2).bind fun equal _ _ hequal => ?_
  split
  · exact .throw
  · rename_i hnot
    refine .pure ⟨{
      name := ci'.name
      uvars := ci'.uvars
      type := ci'.type
      value := value' }, ?_, ?_⟩
    · exact ⟨hci, hvalue⟩
    · have heq : equal = true := by cases equal <;> simp_all
      change (ves.venv safety).HasType ci'.uvars [] value' ci'.type
      rw [← hci.1.2.1]
      exact hhasType.defeqU_r (wf.tr (safety := safety)).wf (by trivial) (hequal heq)

/-- The intended main theorem of the `Verify` development, currently unproved:
if `env` is well-formed and `addDecl env decl` (in checking mode) succeeds,
then the resulting environment is also well-formed, and it extends `env`.

None of the pieces of this theorem exist yet: nothing relates
`Lean.Kernel.Environment.add` to the `TrEnv` relation, and nothing repackages
the `checkType.WF`/`isDefEq.WF` postconditions at the empty local context into
the abstract `VDecl.WF` premises needed to extend `TrEnv`. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration) :
    (addDecl env decl).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  sorry
