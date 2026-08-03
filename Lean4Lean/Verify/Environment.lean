import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Environment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

theorem checkNoMVarNoFVar.WF {env : Environment} {n : Name} {e : Expr} :
    (Lean.Kernel.Environment.checkNoMVarNoFVar env n e).WF fun _ =>
      e.hasMVar = false ∧ e.hasFVar = false := by
  intro _ h
  simp [Lean.Kernel.Environment.checkNoMVarNoFVar,
    Lean.Kernel.Environment.checkNoMVar,
    Lean.Kernel.Environment.checkNoFVar] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · simp_all

theorem checkName.WF {env : Environment} {n : Name} {allowPrimitive : Bool}
    (hmap : env.constants.WF) :
    (Lean.Kernel.Environment.checkName env n allowPrimitive).WF fun _ =>
      env.find? n = none ∧
      (Lean.Kernel.Environment.primitives.contains n → allowPrimitive = true) := by
  intro _ h
  by_cases hfresh : env.constants.contains n = true
  · unfold Lean.Kernel.Environment.checkName at h
    rw [if_pos (by simpa [Lean.Kernel.Environment.contains] using hfresh)] at h
    change (Except.error (.alreadyDeclared env n) : Except Exception Unit) =
      .ok _ at h
    contradiction
  · have hfresh' : env.constants.contains n = false := by
      simpa using hfresh
    have hfind : env.find? n = none := by
      rw [SMap.find?_isSome] at hfresh'
      have hm : env.constants.find? n = none := by
        cases hm : env.constants.find? n <;> simp_all
      change env.constants.find?' n = none
      rwa [hmap.find?'_eq_find?]
    by_cases hallow : allowPrimitive = true
    · exact ⟨hfind, fun _ => hallow⟩
    · have hallow' : allowPrimitive = false := by simpa using hallow
      by_cases hp :
          Lean.Kernel.Environment.primitives.contains n = true
      · unfold Lean.Kernel.Environment.checkName at h
        rw [if_neg (by simpa [Lean.Kernel.Environment.contains] using hfresh),
          if_neg hallow, if_pos hp] at h
        change (Except.error _ : Except Exception Unit) = .ok _ at h
        contradiction
      · exact ⟨hfind, fun hp' => (hp hp').elim⟩

theorem checkConstantValBody.WF
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {env : Environment} {v : ConstantVal} :
    TypeChecker.M.WF c s (checkConstantValBody env v) fun _ _ =>
      ∃ type', c.TrExprS v.type type' ∧ c.IsType type' := by
  simp only [checkConstantValBody]
  have hdup :
      (Lean.Kernel.Environment.checkDuplicatedUnivParams v.levelParams).WF
        fun _ => True :=
    fun _ _ => trivial
  refine (TypeChecker.M.WF.liftExcept hdup).bind fun _ _ _ _ => ?_
  refine (TypeChecker.M.WF.liftExcept checkNoMVarNoFVar.WF).bind
    fun _ _ _ hclosed => ?_
  have hfvars : v.type.FVarsIn (· ∈ c.vlctx.fvars) := by
    apply fvarsIn_iff.mpr
    refine ⟨?_, fvarsIn_iff_hasMVar.mpr hclosed.1⟩
    intro fv hfv
    have hempty : v.type.fvarsList = [] := fvarsList_eq_nil.2 hclosed.2
    simp [hempty] at hfv
  refine (TypeChecker.checkType.WF hfvars).bind fun sort _ _ hsort => ?_
  rcases hsort with ⟨type', sort', _, htype, hsort, htypeT⟩
  refine (TypeChecker.ensureSort.WF hsort).bind fun _ _ _ h => .pure ?_
  rcases h with ⟨⟨sort'', hsort'', heq⟩, u, rfl⟩
  cases hsort'' with
  | sort hu =>
    exact ⟨type', htype, _, htypeT.defeqU_r c.Ewf c.Δwf heq.symm⟩

theorem checkConstantVal.WF
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {env : Environment} {v : ConstantVal} {allowPrimitive : Bool}
    (hmap : env.constants.WF) :
    TypeChecker.M.WF c s (checkConstantVal env v allowPrimitive) fun _ _ =>
      env.find? v.name = none ∧
      (Lean.Kernel.Environment.primitives.contains v.name →
        allowPrimitive = true) ∧
      ∃ type', c.TrExprS v.type type' ∧ c.IsType type' := by
  simp only [checkConstantVal]
  refine (TypeChecker.M.WF.liftExcept (checkName.WF hmap)).bind
    fun _ _ _ hname => ?_
  exact checkConstantValBody.WF.mono fun _ _ _ hbody =>
    ⟨hname.1, hname.2, hbody⟩

theorem TrEnv.addConst_of_find?_eq_none
    {env : Environment} {venv : VEnv} {n : Name} {ci : VConstant}
    (htr : TrEnv safety env venv) (hfresh : env.find? n = none) :
    ∃ venv', venv.addConst n ci = some venv' := by
  have hnone : venv.constants n = none := by
    cases h : venv.constants n with
    | none => rfl
    | some ci' =>
      have hs := (htr.find?_iff (name := n)).2 ⟨ci', h⟩
      rcases hs with ⟨ci₀, hci₀, _⟩
      rw [hfresh] at hci₀
      contradiction
  unfold VEnv.addConst
  rw [hnone]
  exact ⟨_, rfl⟩

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv}
    (hle : env₁ ≤ env₂)
    (hadd₁ : env₁.addConst n ci = some env₁')
    (hadd₂ : env₂.addConst n ci = some env₂') : env₁' ≤ env₂' := by
  constructor
  · intro m a hm
    by_cases hnm : n = m
    · subst m
      rw [VEnv.addConst_self hadd₁] at hm
      cases hm
      exact VEnv.addConst_self hadd₂
    · rw [VEnv.addConst_constants_of_ne hadd₁ hnm] at hm
      rw [VEnv.addConst_constants_of_ne hadd₂ hnm]
      exact hle.constants hm
  · intro df hdf
    have hdef₁ : env₁'.defeqs = env₁.defeqs := by
      unfold VEnv.addConst at hadd₁
      split at hadd₁ <;> cases hadd₁
      rfl
    have hdef₂ : env₂'.defeqs = env₂.defeqs := by
      unfold VEnv.addConst at hadd₂
      split at hadd₂ <;> cases hadd₂
      rfl
    rw [hdef₁] at hdf
    rw [hdef₂]
    exact hle.defeqs hdf

theorem VEnv.addDefEq_mono {env₁ env₂ : VEnv} (hle : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df := by
  constructor
  · exact hle.constants
  · intro df' hdf'
    change df' = df ∨ env₁.defeqs df' at hdf'
    change df' = df ∨ env₂.defeqs df'
    exact hdf'.imp id hle.defeqs

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
