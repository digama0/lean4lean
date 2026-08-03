import Lean4Lean.Verify.ModDivReflect
import Lean4Lean.Verify.BitwiseReflect
import Lean4Lean.Environment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

open private Lean.Kernel.Environment.add from Lean.Environment

theorem ConstantInfo.defnInfo_safety (v : DefinitionVal) :
    (ConstantInfo.defnInfo v).safety = v.safety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
  cases v.safety <;> rfl

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

theorem checkBodyCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (name : Name) (levelParams : List Name)
    (type value : Expr) (type' : VExpr)
    (hdeclType : TrExprS (ves.venv safety) levelParams [] type type')
    (hclosed : value.hasMVar = false ∧ value.hasFVar = false)
    (state : TypeChecker.VState := {}) :
    ((do
      let valueType ← TypeChecker.checkType value
      if !(← TypeChecker.isDefEq valueType type) then
        throw <| Exception.declTypeMismatch env decl valueType) :
      TypeChecker.M Unit).WF
      (.mk' wf safety levelParams) state fun _ _ =>
        ∃ value', TrExprS (ves.venv safety) levelParams [] value value' ∧
          (ves.venv safety).HasType levelParams.length [] value' type' := by
  have hfvars : value.FVarsIn
      (· ∈ (TypeChecker.VContext.mk' wf safety levelParams).vlctx.fvars) := by
    apply fvarsIn_iff.mpr
    refine ⟨?_, fvarsIn_iff_hasMVar.mpr hclosed.1⟩
    intro fv hfv
    have hempty : value.fvarsList = [] := fvarsList_eq_nil.2 hclosed.2
    simp [hempty] at hfv
  refine (TypeChecker.checkType.WF hfvars).bind
    fun _ _ _ ⟨value', valueType', _, hvalue, hvalueType, hhasType⟩ => ?_
  refine (TypeChecker.isDefEq.WF hvalueType hdeclType).bind
    fun equal _ _ hequal => ?_
  split
  · exact .throw
  · rename_i hnot
    refine .pure ⟨value', hvalue, ?_⟩
    have heq : equal = true := by cases equal <;> simp_all
    exact hhasType.defeqU_r (wf.tr (safety := safety)).wf trivial
      (hequal heq)

theorem checkBody.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (name : Name) (levelParams : List Name)
    (type value : Expr) (type' : VExpr)
    (hdeclType : TrExprS (ves.venv safety) levelParams [] type type')
    (state : TypeChecker.VState := {}) :
    ((do
      Lean.Kernel.Environment.checkNoMVarNoFVar env name value
      let valueType ← TypeChecker.checkType value
      if !(← TypeChecker.isDefEq valueType type) then
        throw <| Exception.declTypeMismatch env decl valueType) :
      TypeChecker.M Unit).WF
      (.mk' wf safety levelParams) state fun _ _ =>
        ∃ value', TrExprS (ves.venv safety) levelParams [] value value' ∧
          (ves.venv safety).HasType levelParams.length [] value' type' := by
  refine (TypeChecker.M.WF.liftExcept checkNoMVarNoFVar.WF).bind
    fun _ state' _ hclosed => ?_
  exact checkBodyCore.WF wf decl name levelParams type value type'
    hdeclType hclosed state'

theorem checkDefinitionBody.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (state : TypeChecker.VState := {}) :
    (checkDefinitionBody env v).WF
      (.mk' wf .safe v.levelParams) state fun _ _ =>
        ∃ v' : VDefVal,
          v.levelParams.length = v'.uvars ∧
          TrExprS (ves.venv .safe) v.levelParams [] v.type v'.type ∧
          v.name = v'.name ∧
          TrExprS (ves.venv .safe) v.levelParams [] v.value v'.value ∧
          v'.WF (ves.venv .safe) := by
  unfold checkDefinitionBody
  refine checkConstantValBody.WF.bind fun _ state' _ hheader => ?_
  obtain ⟨type', htype, _⟩ := hheader
  exact (checkBody.WF wf (.defnDecl v) v.name v.levelParams
    v.type v.value type' htype state').mono fun _ _ _ hbody => by
      obtain ⟨value', hvalue, hvalueT⟩ := hbody
      exact ⟨{
        name := v.name, uvars := v.levelParams.length,
        type := type', value := value' },
        rfl, htype, rfl, hvalue, hvalueT⟩

theorem checkSafeNatAddDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app .natSucc (.app (.app v'.value (.bvar 1)) (.bvar 0))) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natAdd.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatModDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatModPrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natMod.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl rfl htype hvalue).bind fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := by
    rcases hevidence with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlevels, _⟩
    exact hlevels
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatDivDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatDivPrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natDiv.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl rfl htype hvalue).bind fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := by
    rcases hevidence with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlevels, _⟩
    exact hlevels
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatGcdDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.gcd)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatGcdPrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natGcd.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind
      fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := hevidence.choose_spec.1
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatBitwiseDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.bitwise)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          Environment.NatBitwisePrimitiveEvidence
            (.mk' wf .safe v.levelParams) v v'.type := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natBitwise.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) hname rfl rfl htype).bind
      fun allow _ _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  have hevidence := hcheck hallow
  have hlevels : v.levelParams = [] := by
    rcases hevidence with ⟨_, _, _, hlevels, _⟩
    exact hlevels
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hevidence⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatPredDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app v'.value .natZero) .natZero ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app v'.value (.app .natSucc (.bvar 0)))
            (.lam .nat <| .bvar 0) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natPred.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatSubDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.pred ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.const ``Nat.pred [])
                (.app (.app v'.value (.bvar 1)) (.bvar 0))) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natSub.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hpred, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hpred, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatMulDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.add ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat .natZero) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app (.const ``Nat.add [])
                (.app (.app v'.value (.bvar 1)) (.bvar 0))) (.bvar 1)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natMul.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, haddC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, haddC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatPowDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.mul ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .app .natSucc .natZero) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app (.const ``Nat.mul [])
                (.app (.app v'.value (.bvar 1)) (.bvar 0))) (.bvar 1)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natPow.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hmulC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hmulC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩


theorem checkSafeNatShiftLeftDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.mul ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 0)) (.app .natSucc (.bvar 1)))
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value
                (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
                (.bvar 1)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natShiftLeft.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hmulC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hmulC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩


theorem checkSafeNatShiftRightDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat.div ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.bvar 0)) .natZero)
            (.lam .nat <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 0)) (.app .natSucc (.bvar 1)))
            (.lam .nat <| .lam .nat <|
              .app (.app (.const ``Nat.div [])
                (.app (.app v'.value (.bvar 0)) (.bvar 1))) (.natLit 2)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natShiftRight.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hdivC, hty, hz, hs⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hdivC, hty, hz, hs⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatBEqDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app v'.value .natZero) .natZero) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value .natZero)
              (.app .natSucc (.bvar 0))) (.lam .nat .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.app .natSucc (.bvar 0)))
              .natZero) (.lam .nat .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.app .natSucc (.bvar 1)))
                (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.bvar 0)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natBEq.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩



theorem checkSafeNatBLEDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app v'.value .natZero) .natZero) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value .natZero)
              (.app .natSucc (.bvar 0))) (.lam .nat .boolTrue) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .app (.app v'.value (.app .natSucc (.bvar 0)))
              .natZero) (.lam .nat .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.app .natSucc (.bvar 1)))
                (.app .natSucc (.bvar 0)))
            (.lam .nat <| .lam .nat <|
              .app (.app v'.value (.bvar 1)) (.bvar 0)) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  have hvalueT' := hvalueT
  change (ves.venv .safe).HasType v'.uvars [] v'.value v'.type at hvalueT'
  rw [← huvars] at hvalueT'
  refine (Environment.checkPrimitiveDef.natBLE.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname rfl htype hvalue hvalueT').bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1,
    hlevels, hnat, hbool, hty, h00, h0s, hs0, hss⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatXorDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.xor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal, ∃ op' : VExpr,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Nat.bitwise ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          v'.value = .app (.const ``Nat.bitwise []) op' ∧
          (ves.venv .safe).HasType v.levelParams.length [] op'
            (.forallE .bool <| .forallE .bool .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolFalse) .boolFalse) .boolFalse ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolTrue) .boolFalse) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolFalse) .boolTrue) .boolTrue ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.app (.app op' .boolTrue) .boolTrue) .boolFalse := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natXor.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname hshape htype hvalue).bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, _, hbitwise, hty, op', hvalueShape,
    hopTy, hff, htf, hft, htt⟩ := hcheck hallow
  refine ⟨v', op', ?_, hvalueT, hcheckedName.1, hlevels,
    hnat, hbitwise, hty, hvalueShape, hopTy, hff, htf, hft, htt⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeNatLandDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.land)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal, ∃ op' : VExpr,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).contains ``Nat.bitwise ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          v'.value = .app (.const ``Nat.bitwise []) op' ∧
          (ves.venv .safe).HasType v.levelParams.length [] op'
            (.forallE .bool <| .forallE .bool .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0))
            (.lam .bool .boolFalse) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0))
            (.lam .bool <| .bvar 0) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natLand.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname hshape rfl htype hvalue).bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hbitwise, hty, op', hvalueShape,
    hopTy, hf, ht⟩ := hcheck hallow
  refine ⟨v', op', ?_, hvalueT, hcheckedName.1, hlevels,
    hnat, hbool, hbitwise, hty, hvalueShape, hopTy, hf, ht⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩


theorem checkSafeNatLorDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.lor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal, ∃ op' : VExpr,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).contains ``Bool ∧
          (ves.venv .safe).contains ``Nat.bitwise ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat <| .forallE .nat .nat) ∧
          v'.value = .app (.const ``Nat.bitwise []) op' ∧
          (ves.venv .safe).HasType v.levelParams.length [] op'
            (.forallE .bool <| .forallE .bool .bool) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0))
            (.lam .bool <| .bvar 0) ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length []
            (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0))
            (.lam .bool .boolTrue) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.natLor.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) (value' := v'.value)
    hname hshape rfl htype hvalue).bind fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hbool, hbitwise, hty, op', hvalueShape,
    hopTy, hf, ht⟩ := hcheck hallow
  refine ⟨v', op', ?_, hvalueT, hcheckedName.1, hlevels,
    hnat, hbool, hbitwise, hty, hvalueShape, hopTy, hf, ht⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeCharOfNatDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Char.ofNat)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).contains ``Nat ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .nat .char) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.charOfNat.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) hname hsafety rfl htype).bind
      fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hnat, hty⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels, hnat, hty⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩

theorem checkSafeStringOfListDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``String.ofList)
    (hsafety : v.safety = .safe) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧
          (ves.venv .safe).IsDefEqU v.levelParams.length [] v'.type
            (.forallE .listChar .string) ∧
          (ves.venv .safe).HasType v.levelParams.length []
            .listCharNil .listChar ∧
          (ves.venv .safe).HasType v.levelParams.length []
            .listCharCons
              (.forallE .char <| .forallE .listChar .listChar) := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.stringOfList.WF_typed
    (c := .mk' wf .safe v.levelParams) (s := state')
    (ty' := v'.type) hname hsafety rfl htype).bind
      fun allow state'' _ hcheck => ?_
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hcheckedName => ?_
  have hallow : allow = true := hcheckedName.2 (by
    rw [hname]
    simp [Lean.Kernel.Environment.primitives,
      NameSet.contains, NameSet.ofList])
  obtain ⟨hlevels, hty, hnil, hcons⟩ := hcheck hallow
  refine ⟨v', ?_, hvalueT, hcheckedName.1, hlevels,
    hty, hnil, hcons⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype⟩, hvname⟩, hvalue⟩



theorem checkSafeNonprimitiveDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.WF_of_not_primitive (v := v) hn).bind
    fun allow state'' _ hallow => ?_
  subst allow
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hname => ?_
  refine ⟨v', ?_, ?_, hname.1⟩
  · exact ⟨⟨⟨by
      rw [ConstantInfo.defnInfo_safety, hsafety]
      exact DefinitionSafety.le_rfl,
      huvars, htype⟩, hvname⟩, hvalue⟩
  · exact hvalueT

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

theorem TrEnv.block
    (htr : TrEnv safety env venv)
    (hfresh : env.find? ci.name = none)
    (hsafety : ¬safety ≤ ci.safety) :
    TrEnv safety (env.add ci) venv := by
  change TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv
  exact .block (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hsafety htr

theorem TrEnv.addAxiom
    (htr : TrEnv safety env venv)
    (hci : TrConstant safety venv (.axiomInfo ci) ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv') :
    TrEnv safety (env.add (.axiomInfo ci)) venv' := by
  change TrEnv' safety
    (env.constants.insert ci.name (.axiomInfo ci)) env.quotInit venv'
  exact .axiom hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

theorem TrEnv.addDefinition
    (htr : TrEnv safety env venv)
    (hci : TrDefVal safety venv (.defnInfo ci) ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv') :
    TrEnv safety (env.add (.defnInfo ci))
      (venv'.addDefEq ci'.toDefEq) := by
  change TrEnv' safety
    (env.constants.insert ci.name (.defnInfo ci)) env.quotInit
    (venv'.addDefEq ci'.toDefEq)
  exact .defn hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

theorem TrEnv.addUnsafeDefinition
    {ci : DefinitionVal} {ci' : VDefVal}
    (htr : TrEnv .unsafe env venv)
    (hheader : TrConstVal .unsafe venv (.defnInfo ci) ci'.toVConstVal)
    (hfresh : env.find? ci.name = none)
    (hheaderWF : ci'.toVConstant.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv')
    (hvalue : TrExprS venv' ci.levelParams [] ci.value ci'.value)
    (hvalueWF : ci'.WF venv') :
    TrEnv .unsafe (env.add (.defnInfo ci))
      (venv'.addDefEq ci'.toDefEq) := by
  change TrEnv' .unsafe
    (env.constants.insert ci.name (.defnInfo ci)) env.quotInit
    (venv'.addDefEq ci'.toDefEq)
  exact .unsafeDefn hheader (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hheaderWF hadd hvalue hvalueWF htr

theorem TrEnv.addOpaque
    (htr : TrEnv safety env venv)
    (hci : TrDefVal safety venv (.opaqueInfo ci) ci')
    (hfresh : env.find? ci.name = none)
    (hciWF : ci'.WF venv)
    (hadd : venv.addConst ci.name ci'.toVConstant = some venv') :
    TrEnv safety (env.add (.opaqueInfo ci)) venv' := by
  change TrEnv' safety
    (env.constants.insert ci.name (.opaqueInfo ci)) env.quotInit venv'
  exact .opaque hci (by
    rw [← htr.map_wf.find?'_eq_find?]
    exact hfresh) hciWF hadd htr

theorem Environment.safePrimitives_add_of_not_primitive
    {env : Environment} {ci ci' : ConstantInfo} {n : Name}
    (hmap : env.constants.WF)
    (hfresh : env.find? ci.name = none)
    (hold : env.find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [])
    (hn : ¬Lean.Kernel.Environment.primitives.contains ci.name) :
    (env.add ci).find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [] := by
  intro hfind hprim
  have hfresh' : SMap.find? env.constants ci.name = none := by
    rw [← hmap.find?'_eq_find?]
    exact hfresh
  have hmap' := hmap.insert ci.name ci hfresh'
  change (env.constants.insert ci.name ci).find?' n = some ci' at hfind
  rw [hmap'.find?'_eq_find?, hmap.find?_insert] at hfind
  split at hfind
  · rename_i hname
    have hname' : ci.name = n := LawfulBEq.eq_of_beq hname
    subst n
    exact (hn hprim).elim
  · apply hold ?_ hprim
    change env.constants.find?' n = some ci'
    rw [hmap.find?'_eq_find?]
    exact hfind

theorem Environment.safePrimitives_add_of_safe_primitive
    {env : Environment} {ci ci' : ConstantInfo} {n : Name}
    (hmap : env.constants.WF)
    (hfresh : env.find? ci.name = none)
    (hold : env.find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [])
    (hnewSafety : ci.safety = .safe) (hnewLevels : ci.levelParams = []) :
    (env.add ci).find? n = some ci' →
      Lean.Kernel.Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [] := by
  intro hfind hprim
  have hfresh' : SMap.find? env.constants ci.name = none := by
    rw [← hmap.find?'_eq_find?]
    exact hfresh
  have hmap' := hmap.insert ci.name ci hfresh'
  change (env.constants.insert ci.name ci).find?' n = some ci' at hfind
  rw [hmap'.find?'_eq_find?, hmap.find?_insert] at hfind
  split at hfind
  · cases hfind
    exact ⟨hnewSafety, hnewLevels⟩
  · apply hold ?_ hprim
    change env.constants.find?' n = some ci'
    rw [hmap.find?'_eq_find?]
    exact hfind

theorem VEnvs.WF.addSafeDefinition_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal}
    (hsafety : v.safety = .safe)
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .safe (ves.venv .safe) (.defnInfo v) v')
    (hvWF : v'.WF (ves.venv .safe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => (added safety).addDefEq v'.toDefEq⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hsafe : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have hsafety' : safety ≤ (ConstantInfo.defnInfo v).safety := by
        simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
          ConstantInfo.isPartial, hsafety] using
          (DefinitionSafety.le_safe (a := safety))
      have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) v' := by
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨hsafety',
          hconst.2.1, hconst.2.2.mono hsafe⟩, hname⟩,
          hvalue.mono hsafe⟩
      exact TrEnv.addDefinition (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hsafe) (hadd safety)
    · intro safety
      exact (wf.hasPrimitives (safety := safety)).addDef_of_not_primitive
        (hadd safety) hn
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      have hbase := wf.mono hs
      have haddMono := VEnv.addConst_mono hbase (hadd safety') (hadd safety)
      exact VEnv.addDefEq_mono haddMono
  · intro safety
    exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le

theorem VEnvs.WF.addSafePrimitiveDefinition
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal}
    (hsafety : v.safety = .safe) (hlevels : v.levelParams = [])
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .safe (ves.venv .safe) (.defnInfo v) v')
    (hvWF : v'.WF (ves.venv .safe))
    (hpreserves : ∀ (safety : DefinitionSafety) {out : VEnv},
      (ves.venv safety).addConst v.name v'.toVConstant = some out →
      (out.addDefEq v'.toDefEq).WF →
      (out.addDefEq v'.toDefEq).HasPrimitives) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => (added safety).addDefEq v'.toDefEq⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      have hsafe : ves.venv .safe ≤ ves.venv safety :=
        wf.mono DefinitionSafety.le_safe
      have hsafety' : safety ≤ (ConstantInfo.defnInfo v).safety := by
        rw [ConstantInfo.defnInfo_safety, hsafety]
        exact DefinitionSafety.le_safe
      have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) v' := by
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨hsafety', hconst.2.1, hconst.2.2.mono hsafe⟩,
          hname⟩, hvalue.mono hsafe⟩
      exact TrEnv.addDefinition (wf.tr (safety := safety)) htr' hfresh
        (hvWF.mono hsafe) (hadd safety)
    · intro safety
      apply hpreserves safety (hadd safety)
      exact (TrEnv.addDefinition (wf.tr (safety := safety)) (by
        have hsafe : ves.venv .safe ≤ ves.venv safety :=
          wf.mono DefinitionSafety.le_safe
        rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
        exact ⟨⟨⟨by
          rw [ConstantInfo.defnInfo_safety, hsafety]
          exact DefinitionSafety.le_safe,
          hconst.2.1, hconst.2.2.mono hsafe⟩, hname⟩,
          hvalue.mono hsafe⟩) hfresh
        (hvWF.mono (wf.mono DefinitionSafety.le_safe))
        (hadd safety)).wf
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_safe_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf hfresh
        wf.safePrimitives (by rw [ConstantInfo.defnInfo_safety, hsafety])
        (by simpa using hlevels) hfind hprim
    · intro safety safety' hs
      have haddMono := VEnv.addConst_mono (wf.mono hs)
        (hadd safety') (hadd safety)
      exact VEnv.addDefEq_mono haddMono
  · intro safety
    exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le

theorem VEnvs.WF.addPartialDefinition_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal}
    (hsafety : v.safety = .partial)
    (hfresh : env.find? v.name = none)
    (htr : TrDefVal .partial (ves.venv .partial) (.defnInfo v) v')
    (hvWF : v'.WF (ves.venv .partial))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v'.toVConstant = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) : VEnv :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v'.toVConstant = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => if safety ≤ .partial then
      (added safety).addDefEq v'.toDefEq else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .partial
      · have hbase : ves.venv .partial ≤ ves.venv safety := wf.mono hs
        have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) v' := by
          rcases htr with ⟨⟨hconst, hname⟩, hvalue⟩
          exact ⟨⟨⟨by
            rw [ConstantInfo.defnInfo_safety, hsafety]
            exact hs,
            hconst.2.1, hconst.2.2.mono hbase⟩, hname⟩,
            hvalue.mono hbase⟩
        simpa [ves', hs] using
          TrEnv.addDefinition (wf.tr (safety := safety)) htr' hfresh
            (hvWF.mono hbase) (hadd safety)
      · simpa [ves', hs] using
          TrEnv.block (ci := .defnInfo v)
            (wf.tr (safety := safety)) hfresh (by
            rw [ConstantInfo.defnInfo_safety, hsafety]
            exact hs)
    · intro safety
      by_cases hs : safety ≤ .partial
      · simp only [ves', hs, ↓reduceIte]
        exact (wf.hasPrimitives (safety := safety)).addDef_of_not_primitive
          (hadd safety) hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hsp : safety ≤ .partial
      · by_cases hsp' : safety' ≤ .partial
        · simp only [ves', hsp, hsp', ↓reduceIte]
          exact VEnv.addDefEq_mono <|
            VEnv.addConst_mono (wf.mono hs) (hadd safety') (hadd safety)
        · simp only [ves', hsp, hsp', ↓reduceIte]
          exact (wf.mono hs).trans <|
            (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le
      · have hsp' : ¬safety' ≤ .partial := fun h =>
          hsp (DefinitionSafety.le_trans hs h)
        simpa [ves', hsp, hsp'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .partial
    · simp only [ves', hs, ↓reduceIte]
      exact (VEnv.addConst_le (hadd safety)).trans VEnv.addDefEq_le
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl

theorem VEnvs.WF.addUnsafeAxiom_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : AxiomVal} {v' : VConstant}
    (hunsafe : v.isUnsafe = true)
    (hfresh : env.find? v.name = none)
    (htr : TrConstant .unsafe (ves.venv .unsafe) (.axiomInfo v) v')
    (hvWF : v'.WF (ves.venv .unsafe))
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.axiomInfo v)) ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      (ves.venv .unsafe).addConst v.name v' = some (ves'.venv .unsafe) := by
  classical
  have haddExists (safety : DefinitionSafety) :
      ∃ out, (ves.venv safety).addConst v.name v' = some out :=
    TrEnv.addConst_of_find?_eq_none (wf.tr (safety := safety)) hfresh
  let added (safety : DefinitionSafety) :=
    Classical.choose (haddExists safety)
  have hadd (safety : DefinitionSafety) :
      (ves.venv safety).addConst v.name v' = some (added safety) :=
    Classical.choose_spec (haddExists safety)
  let ves' : VEnvs :=
    ⟨fun safety => if safety ≤ .unsafe then added safety else ves.venv safety⟩
  refine ⟨ves', ?_, ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have hbase : ves.venv .unsafe ≤ ves.venv safety := wf.mono hs
        have htr' : TrConstant safety (ves.venv safety) (.axiomInfo v) v' :=
          (htr.sf_mono hs).mono hbase
        simpa [ves', hs] using
          TrEnv.addAxiom (wf.tr (safety := safety)) htr' hfresh
            (hvWF.mono hbase) (hadd safety)
      · simpa [ves', hs] using
          TrEnv.block (ci := .axiomInfo v)
            (wf.tr (safety := safety)) hfresh (by
              simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
                ConstantInfo.isPartial, hunsafe] using hs)
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · simp only [ves', hs, ↓reduceIte]
        exact (wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
          (hadd safety) hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .axiomInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hu : safety ≤ .unsafe
      · by_cases hu' : safety' ≤ .unsafe
        · simp only [ves', hu, hu', ↓reduceIte]
          exact VEnv.addConst_mono (wf.mono hs)
            (hadd safety') (hadd safety)
        · simp only [ves', hu, hu', ↓reduceIte]
          exact (wf.mono hs).trans (VEnv.addConst_le (hadd safety))
      · have hu' : ¬safety' ≤ .unsafe := fun h =>
          hu (DefinitionSafety.le_trans hs h)
        simpa [ves', hu, hu'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .unsafe
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.addConst_le (hadd safety)
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl
  · simpa [ves', DefinitionSafety.le_rfl] using hadd .unsafe

theorem VEnvs.WF.addUnsafeDefinition_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {v : DefinitionVal} {v' : VDefVal} {out : VEnv}
    (hsafety : v.safety = .unsafe)
    (hfresh : env.find? v.name = none)
    (hheader : TrConstVal .unsafe (ves.venv .unsafe)
      (.defnInfo v) v'.toVConstVal)
    (hheaderWF : v'.toVConstant.WF (ves.venv .unsafe))
    (hadd : (ves.venv .unsafe).addConst v.name v'.toVConstant = some out)
    (hvalue : TrExprS out v.levelParams [] v.value v'.value)
    (hvalueWF : v'.WF out)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let ves' : VEnvs := ⟨fun safety => if safety ≤ .unsafe then
    out.addDefEq v'.toDefEq else ves.venv safety⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := ?_
      mono := ?_ }
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have heq := DefinitionSafety.le_antisymm hs
            (DefinitionSafety.unsafe_le (a := safety))
        subst safety
        simpa [ves'] using TrEnv.addUnsafeDefinition
          (wf.tr (safety := .unsafe)) hheader hfresh hheaderWF hadd
          hvalue hvalueWF
      · simpa [ves', hs] using
          TrEnv.block (ci := .defnInfo v)
            (wf.tr (safety := safety)) hfresh (by
              simpa [ConstantInfo.defnInfo_safety, hsafety] using hs)
    · intro safety
      by_cases hs : safety ≤ .unsafe
      · have heq := DefinitionSafety.le_antisymm hs
            (DefinitionSafety.unsafe_le (a := safety))
        subst safety
        simp only [ves', DefinitionSafety.le_rfl, ↓reduceIte]
        exact (wf.hasPrimitives (safety := .unsafe)).addDef_of_not_primitive
          hadd hn
      · simpa [ves', hs] using wf.hasPrimitives (safety := safety)
    · intro n ci hfind hprim
      exact Environment.safePrimitives_add_of_not_primitive
        (ci := .defnInfo v) (wf.tr (safety := .safe)).map_wf
        hfresh wf.safePrimitives hn hfind hprim
    · intro safety safety' hs
      by_cases hu : safety ≤ .unsafe
      · have heq := DefinitionSafety.le_antisymm hu
            (DefinitionSafety.unsafe_le (a := safety))
        subst safety
        by_cases hu' : safety' ≤ .unsafe
        · have heq' := DefinitionSafety.le_antisymm hu'
              (DefinitionSafety.unsafe_le (a := safety'))
          subst safety'
          exact VEnv.LE.rfl
        · simp only [ves', DefinitionSafety.le_rfl, hu', ↓reduceIte]
          exact (wf.mono DefinitionSafety.unsafe_le).trans <|
            (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
      · have hu' : ¬safety' ≤ .unsafe := fun h =>
          hu (DefinitionSafety.le_trans hs h)
        simpa [ves', hu, hu'] using wf.mono hs
  · intro safety
    by_cases hs : safety ≤ .unsafe
    · have heq := DefinitionSafety.le_antisymm hs
          (DefinitionSafety.unsafe_le (a := safety))
      subst safety
      simp only [ves', DefinitionSafety.le_rfl, ↓reduceIte]
      exact (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
    · simp only [ves', hs, ↓reduceIte]
      exact VEnv.LE.rfl

theorem addDefinition.WF_safe_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNonprimitiveDefinition.WF wf v hsafety hn).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh⟩ := h
  exact wf.addSafeDefinition_of_not_primitive hsafety hfresh htr hvWF hn

theorem checkPartialNonprimitiveDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      if allowPrimitive then
        throw <| Exception.other
          s!"primitive definition {v.name} must be safe"
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .partial (ves.venv .partial) (.defnInfo v) v' ∧
          v'.WF (ves.venv .partial) ∧ env.find? v.name = none := by
  refine (checkDefinitionBody.WF wf v).bind fun _ state' _ hbody => ?_
  obtain ⟨v', huvars, htype, hvname, hvalue, hvalueT⟩ := hbody
  refine (Environment.checkPrimitiveDef.WF_of_not_primitive
    (c := .mk' wf .safe v.levelParams) (s := state') hn).bind
      fun allow _ _ hallow => ?_
  subst allow
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine (TypeChecker.M.WF.liftExcept
    (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
    fun _ _ _ hname => ?_
  have hmono : ves.venv .safe ≤ ves.venv .partial :=
    wf.mono (by decide)
  refine ⟨v', ?_, hvalueT.mono hmono, hname.1⟩
  exact ⟨⟨⟨by
    rw [ConstantInfo.defnInfo_safety, hsafety]
    exact DefinitionSafety.le_rfl,
    huvars, htype.mono hmono⟩, hvname⟩, hvalue.mono hmono⟩

theorem addDefinition.WF_partial_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hn : ¬Lean.Kernel.Environment.primitives.contains v.name) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkPartialNonprimitiveDefinition.WF wf v hsafety hn).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh⟩ := h
  exact wf.addPartialDefinition_of_not_primitive
    hsafety hfresh htr hvWF hn

theorem addDefinition.WF_partial_of_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hp : Lean.Kernel.Environment.primitives.contains v.name) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind] at hrun
  split at hrun <;> cases hrun
  rename_i _ _ hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i _ primitiveResult hprimitive
      clear hbody
      split at hrun
      · change (Except.error _ : Except Exception (Unit × State)) =
          Except.ok _ at hrun
        contradiction
      · rename_i hfalse
        have hfalse' : primitiveResult.fst = false := by
          cases h : primitiveResult.fst <;> simp_all
        rw [hfalse'] at hrun
        change ((fun x => (x, _)) <$> env.checkName v.name false) =
          Except.ok _ at hrun
        simp [Lean.Kernel.Environment.checkName, hp] at hrun
        split at hrun <;>
          change (Except.error _ : Except Exception (Unit × State)) =
            Except.ok _ at hrun <;>
          contradiction

theorem addDefinition.WF_safe_natAdd
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatAddDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.add := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.add v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatAddDef
    hnat' hname' hadd' hwf' huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natMod
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatModDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.mod := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.mod v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatModPrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨zeroL', zeroR', go', goTy', topL', topR', goL', goR',
        hzeroL, hzeroR, hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hparams, hnat, hbool, hble, hsub, hty, hzeroEq,
        selector, hgoHas, htopEq, hgoEq⟩
    exact ⟨zeroL', zeroR', go', goTy', topL', topR', goL', goR',
      hzeroL.mono hmono, hzeroR.mono hmono, hgoS.mono hmono,
      hgoTyS.mono hmono, htopL.mono hmono, htopR.mono hmono,
      hgoL.mono hmono, hgoR.mono hmono, hparams,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbool; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hble; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hsub; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono, hzeroEq.mono hmono, selector.mono hmono,
      hgoHas.mono hmono, htopEq.mono hmono, hgoEq.mono hmono⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natDiv
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatDivDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.div := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.div v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatDivPrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨go', goTy', topL', topR', goL', goR',
        hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hparams, hnat, hbool, hble, hsub, hty,
        selector, hgoHas, htopEq, hgoEq⟩
    exact ⟨go', goTy', topL', topR', goL', goR',
      hgoS.mono hmono, hgoTyS.mono hmono,
      htopL.mono hmono, htopR.mono hmono,
      hgoL.mono hmono, hgoR.mono hmono, hparams,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbool; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hble; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hsub; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono, selector.mono hmono,
      hgoHas.mono hmono, htopEq.mono hmono, hgoEq.mono hmono⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natGcd
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.gcd)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatGcdDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.gcd := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.gcd v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatGcdPrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨cert, hparams, hnat, hbeq, hmod, hty, hvalid, hshape⟩
    exact ⟨cert, hparams,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbeq; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hmod; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono, hvalid.mono hmono rfl rfl, hshape⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natBitwise
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.bitwise)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBitwiseDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hevidence⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hname' : v'.name = ``Nat.bitwise := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have hadd' : (ves.venv safety).addConst ``Nat.bitwise v'.toVConstant =
      some out := by simpa [hname] using hadd
  have hevidence' : Environment.NatBitwisePrimitiveEvidence
      (.mk' wf safety v.levelParams) v v'.type := by
    rcases hevidence with
      ⟨cert, ite, decide, hparams, hbool, hnat, hbeq,
        haddC, hmodC, hdivC, hty, hcert,
        hiteS, hite, hdecideS, hdecide⟩
    exact ⟨cert, ite, decide, hparams,
      let ⟨ci, hci⟩ := hbool; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hnat; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hbeq; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := haddC; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hmodC; ⟨ci, hmono.constants hci⟩,
      let ⟨ci, hci⟩ := hdivC; ⟨ci, hmono.constants hci⟩,
      hty.mono hmono,
      hcert.mono hmono rfl rfl,
      hiteS.mono hmono,
      ⟨hite.1.mono hmono,
        fun b x y => (hite.2 b x y).mono hmono⟩,
      hdecideS.mono hmono,
      hdecide.mono hmono⟩
  exact hevidence'.conservesHasPrimitives rfl rfl
    (htr.2.mono hmono) hname' huvars hadd' hwf'

theorem addDefinition.WF_safe_natPred
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatPredDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.pred := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.pred v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatPredDef
    hnat' hname' hadd' hwf' huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natSub
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatSubDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hpred, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hpred' : (ves.venv safety).contains ``Nat.pred := by
    obtain ⟨ci, hci⟩ := hpred
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.sub := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.sub v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatSubDef
    (wf.tr (safety := safety)).wf hpred' hname' hadd' hwf'
    huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natMul
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatMulDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, haddC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have haddC' : (ves.venv safety).contains ``Nat.add := by
    obtain ⟨ci, hci⟩ := haddC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.mul := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.mul v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatMulDef
    (wf.tr (safety := safety)).wf haddC' hname' hadd' hwf'
    huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natPow
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatPowDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hmulC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hmulC' : (ves.venv safety).contains ``Nat.mul := by
    obtain ⟨ci, hci⟩ := hmulC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.pow := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.pow v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatPowDef
    (wf.tr (safety := safety)).wf hmulC' hname' hadd' hwf'
    huvars' hty' hz' hs'


theorem addDefinition.WF_safe_natShiftLeft
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatShiftLeftDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hmulC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hmulC' : (ves.venv safety).contains ``Nat.mul := by
    obtain ⟨ci, hci⟩ := hmulC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.shiftLeft := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.shiftLeft v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatShiftLeftDef
    (wf.tr (safety := safety)).wf hmulC' hname' hadd' hwf'
    huvars' hty' hz' hs'


theorem addDefinition.WF_safe_natShiftRight
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatShiftRightDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hdivC, hty, hz, hs⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hdivC' : (ves.venv safety).contains ``Nat.div := by
    obtain ⟨ci, hci⟩ := hdivC
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.shiftRight := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hz' := hz.mono hmono
  have hs' := hs.mono hmono
  rw [hlevels] at hty' hz' hs'
  have hadd' : (ves.venv safety).addConst ``Nat.shiftRight v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatShiftRightDef
    (wf.tr (safety := safety)).wf hdivC' hname' hadd' hwf'
    huvars' hty' hz' hs'

theorem addDefinition.WF_safe_natBEq
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBEqDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hbool,
    hty, h00, h0s, hs0, hss⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.beq := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have h00' := h00.mono hmono
  have h0s' := h0s.mono hmono
  have hs0' := hs0.mono hmono
  have hss' := hss.mono hmono
  rw [hlevels] at hty' h00' h0s' hs0' hss'
  have hadd' : (ves.venv safety).addConst ``Nat.beq v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatBEqDef
    hnat' hbool' hname' hadd' hwf' huvars' hty' h00' h0s' hs0' hss'



theorem addDefinition.WF_safe_natBLE
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBLEDefinition.WF wf v hname hsafety).run wf |>.map
    fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hnat, hbool,
    hty, h00, h0s, hs0, hss⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.ble := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have h00' := h00.mono hmono
  have h0s' := h0s.mono hmono
  have hs0' := hs0.mono hmono
  have hss' := hss.mono hmono
  rw [hlevels] at hty' h00' h0s' hs0' hss'
  have hadd' : (ves.venv safety).addConst ``Nat.ble v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatBLEDef
    hnat' hbool' hname' hadd' hwf' huvars' hty' h00' h0s' hs0' hss'

theorem addDefinition.WF_safe_charOfNat
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Char.ofNat)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeCharOfNatDefinition.WF
    wf v hname hsafety).run wf |>.map fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, _, hty⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  rw [hlevels] at hty'
  have hadd' : (ves.venv safety).addConst ``Char.ofNat v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addCharOfNat
    hadd' hwf' huvars' hty'

theorem addDefinition.WF_safe_stringOfList
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``String.ofList)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeStringOfListDefinition.WF
    wf v hname hsafety).run wf |>.map fun _ h => ?_
  obtain ⟨v', htr, hvWF, hfresh, hlevels, hty, hnil, hcons⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hnil' := hnil.mono hmono
  have hcons' := hcons.mono hmono
  rw [hlevels] at hty' hnil' hcons'
  have hadd' : (ves.venv safety).addConst
      ``String.ofList v'.toVConstant = some out := by
    simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addStringOfList
    hadd' hwf' huvars' hty' hnil' hcons'

theorem addDefinition.WF_safe_natLand_of_shape
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.land)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatLandDefinition.WF wf v op hname hshape hsafety).run wf
    |>.map fun _ h => ?_
  obtain ⟨v', op', htr, hvWF, hfresh, hlevels, hnat, hbool, hbitwise,
    hty, hvalue, hopTy, hf, ht⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hbitwise' : (ves.venv safety).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwise
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.land := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hf' := hf.mono hmono
  have ht' := ht.mono hmono
  rw [hlevels] at hty' hopTy' hf' ht'
  have hadd' : (ves.venv safety).addConst ``Nat.land v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatLandDef
    (wf.tr (safety := safety)).wf hnat' hbool' hbitwise'
    hname' hadd' hwf' huvars' hty' hvalue
    hopTy' hf' ht'

theorem addDefinition.WF_safe_natLor_of_shape
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.lor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatLorDefinition.WF wf v op hname hshape hsafety).run wf
    |>.map fun _ h => ?_
  obtain ⟨v', op', htr, hvWF, hfresh, hlevels, hnat, hbool, hbitwise,
    hty, hvalue, hopTy, hf, ht⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbool' : (ves.venv safety).contains ``Bool := by
    obtain ⟨ci, hci⟩ := hbool
    exact ⟨ci, hmono.constants hci⟩
  have hbitwise' : (ves.venv safety).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwise
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.lor := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hf' := hf.mono hmono
  have ht' := ht.mono hmono
  rw [hlevels] at hty' hopTy' hf' ht'
  have hadd' : (ves.venv safety).addConst ``Nat.lor v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatLorDef
    (wf.tr (safety := safety)).wf hnat' hbool' hbitwise'
    hname' hadd' hwf' huvars' hty' hvalue
    hopTy' hf' ht'

theorem addDefinition.WF_safe_natXor_of_shape
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (op : Expr)
    (hname : v.name = ``Nat.xor)
    (hshape : v.value = .app (.const ``Nat.bitwise []) op)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatXorDefinition.WF wf v op hname hshape hsafety).run wf
    |>.map fun _ h => ?_
  obtain ⟨v', op', htr, hvWF, hfresh, hlevels, hnat, hbitwise,
    hty, hvalue, hopTy, hff, htf, hft, htt⟩ := h
  apply wf.addSafePrimitiveDefinition hsafety hlevels hfresh htr hvWF
  intro safety out hadd hwf'
  have hmono : ves.venv .safe ≤ ves.venv safety :=
    wf.mono DefinitionSafety.le_safe
  have hnat' : (ves.venv safety).contains ``Nat := by
    obtain ⟨ci, hci⟩ := hnat
    exact ⟨ci, hmono.constants hci⟩
  have hbitwise' : (ves.venv safety).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwise
    exact ⟨ci, hmono.constants hci⟩
  have hname' : v'.name = ``Nat.xor := htr.1.2.symm.trans hname
  have huvars : v.levelParams.length = v'.uvars := htr.1.1.2.1
  have huvars' : v'.uvars = 0 := by simpa [hlevels] using huvars.symm
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hff' := hff.mono hmono
  have htf' := htf.mono hmono
  have hft' := hft.mono hmono
  have htt' := htt.mono hmono
  rw [hlevels] at hty' hopTy' hff' htf' hft' htt'
  have hadd' : (ves.venv safety).addConst ``Nat.xor v'.toVConstant =
      some out := by simpa [hname] using hadd
  exact (wf.hasPrimitives (safety := safety)).addNatXorDef
    hnat' hbitwise' hname' hadd' hwf' huvars' hty' hvalue
    hopTy' hff' htf' hft' htt'

private theorem addDefinition.success_natLand_value_shape
    {env env' : Environment} {v : DefinitionVal}
    (hname : v.name = ``Nat.land) (hsafety : v.safety = .safe)
    (hsuccess : addDefinition env v = .ok env') :
    ∃ op, v.value = .app (.const ``Nat.bitwise []) op := by
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  split at hrun <;> cases hrun
  rename_i _ _ _ _ hrun
  simp [(· >>= ·), ReaderT.bind] at hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i hprimitive
      clear hrun hbody
      simp only [Environment.checkPrimitiveDef, hname] at hprimitive
      simp [TypeChecker.getEnv, (· >>= ·), ReaderT.bind,
        MonadReader.read, readThe, MonadReaderOf.read, Pure.pure,
        ReaderT.read, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at hprimitive
      split at hprimitive
      · split at hprimitive
        · rename_i and hshape
          exact ⟨and, hshape⟩
        · exfalso
          change Except.error _ = Except.ok _ at hprimitive
          cases hprimitive
      · exfalso
        change Except.error _ = Except.ok _ at hprimitive
        cases hprimitive

theorem addDefinition.WF_safe_natLand
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.land)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  obtain ⟨op, hshape⟩ :=
    addDefinition.success_natLand_value_shape hname hsafety hsuccess
  exact addDefinition.WF_safe_natLand_of_shape
    wf v op hname hshape hsafety env' hsuccess

private theorem addDefinition.success_natLor_value_shape
    {env env' : Environment} {v : DefinitionVal}
    (hname : v.name = ``Nat.lor) (hsafety : v.safety = .safe)
    (hsuccess : addDefinition env v = .ok env') :
    ∃ op, v.value = .app (.const ``Nat.bitwise []) op := by
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  split at hrun <;> cases hrun
  rename_i _ _ _ _ hrun
  simp [(· >>= ·), ReaderT.bind] at hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i hprimitive
      clear hrun hbody
      simp only [Environment.checkPrimitiveDef, hname] at hprimitive
      simp [TypeChecker.getEnv, (· >>= ·), ReaderT.bind,
        MonadReader.read, readThe, MonadReaderOf.read, Pure.pure,
        ReaderT.read, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at hprimitive
      split at hprimitive
      · split at hprimitive
        · rename_i or hshape
          exact ⟨or, hshape⟩
        · exfalso
          change Except.error _ = Except.ok _ at hprimitive
          cases hprimitive
      · exfalso
        change Except.error _ = Except.ok _ at hprimitive
        cases hprimitive

theorem addDefinition.WF_safe_natLor
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.lor)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  obtain ⟨op, hshape⟩ :=
    addDefinition.success_natLor_value_shape hname hsafety hsuccess
  exact addDefinition.WF_safe_natLor_of_shape
    wf v op hname hshape hsafety env' hsuccess

private theorem addDefinition.success_natXor_value_shape
    {env env' : Environment} {v : DefinitionVal}
    (hname : v.name = ``Nat.xor) (hsafety : v.safety = .safe)
    (hsuccess : addDefinition env v = .ok env') :
    ∃ op, v.value = .app (.const ``Nat.bitwise []) op := by
  unfold addDefinition at hsuccess
  simp [hsafety] at hsuccess
  simp [M.run, Functor.map, Except.map] at hsuccess
  split at hsuccess <;> cases hsuccess
  rename_i _ _ hrun
  split at hrun <;> cases hrun
  rename_i _ _ _ _ hrun
  simp [(· >>= ·), ReaderT.bind] at hrun
  unfold StateT.bind StateT.run at hrun
  dsimp only [Bind.bind, Except.instMonad] at hrun
  unfold Except.bind at hrun
  split at hrun
  · cases hrun
  · rename_i hbody
    simp only at hrun
    split at hrun
    · cases hrun
    · rename_i hprimitive
      clear hrun hbody
      simp only [Environment.checkPrimitiveDef, hname] at hprimitive
      simp [TypeChecker.getEnv, (· >>= ·), ReaderT.bind,
        MonadReader.read, readThe, MonadReaderOf.read, Pure.pure,
        ReaderT.read, ReaderT.pure, StateT.bind, StateT.pure,
        Except.pure, Except.bind] at hprimitive
      split at hprimitive
      · split at hprimitive
        · rename_i xor hshape
          exact ⟨xor, hshape⟩
        · exfalso
          change Except.error _ = Except.ok _ at hprimitive
          cases hprimitive
      · exfalso
        change Except.error _ = Except.ok _ at hprimitive
        cases hprimitive

theorem addDefinition.WF_safe_natXor
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.xor)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro env' hsuccess
  obtain ⟨op, hshape⟩ :=
    addDefinition.success_natXor_value_shape hname hsafety hsuccess
  exact addDefinition.WF_safe_natXor_of_shape
    wf v op hname hshape hsafety env' hsuccess

theorem addDefinition.WF_safe_inductiveName
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hname : v.name = ``Bool ∨ v.name = ``Bool.false ∨
      v.name = ``Bool.true ∨ v.name = ``Nat ∨
      v.name = ``Nat.zero ∨ v.name = ``Nat.succ) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  have hrun : ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Lean.Kernel.Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ => False := by
    refine (checkDefinitionBody.WF wf v).bind fun _ state' _ _ => ?_
    refine (Environment.checkPrimitiveDef.WF_of_inductive_name
      (c := .mk' wf .safe v.levelParams) (s := state') hname).bind
      fun allow _ _ hallow => ?_
    refine (TypeChecker.M.WF.liftExcept
      (checkName.WF (wf.tr (safety := .safe)).map_wf)).mono
      fun _ _ _ hcheckedName => ?_
    have : allow = true := hcheckedName.2 (by
      rcases hname with hname | hname | hname | hname | hname | hname
      all_goals
        rw [hname]
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    simp_all
  exact hrun.run wf |>.map fun _ h => False.elim h

set_option maxRecDepth 4000 in
theorem addDefinition.WF_safe
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  by_cases hn : ¬Lean.Kernel.Environment.primitives.contains v.name
  · exact addDefinition.WF_safe_of_not_primitive wf v hsafety hn
  · have hp₀ : Lean.Kernel.Environment.primitives.contains v.name :=
      Classical.byContradiction fun h => hn h
    have hp : v.name = ``Bool ∨ v.name = ``Bool.false ∨
        v.name = ``Bool.true ∨ v.name = ``Nat ∨
        v.name = ``Nat.zero ∨ v.name = ``Nat.succ ∨
        v.name = ``Nat.add ∨ v.name = ``Nat.pred ∨
        v.name = ``Nat.sub ∨ v.name = ``Nat.mul ∨
        v.name = ``Nat.pow ∨ v.name = ``Nat.gcd ∨
        v.name = ``Nat.mod ∨ v.name = ``Nat.div ∨
        v.name = ``Nat.beq ∨ v.name = ``Nat.ble ∨
        v.name = ``Nat.bitwise ∨ v.name = ``Nat.land ∨
        v.name = ``Nat.lor ∨ v.name = ``Nat.xor ∨
        v.name = ``Nat.shiftLeft ∨ v.name = ``Nat.shiftRight ∨
        v.name = ``String.ofList ∨ v.name = ``Char.ofNat := by
      simp [Lean.Kernel.Environment.primitives,
        NameSet.contains, NameSet.ofList] at hp₀
      simpa only [eq_comm] using hp₀
    rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h
    · exact addDefinition.WF_safe_inductiveName wf v hsafety (.inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety (.inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inr <| .inr <| .inl h)
    · exact addDefinition.WF_safe_inductiveName wf v hsafety
        (.inr <| .inr <| .inr <| .inr <| .inr h)
    · exact addDefinition.WF_safe_natAdd wf v h hsafety
    · exact addDefinition.WF_safe_natPred wf v h hsafety
    · exact addDefinition.WF_safe_natSub wf v h hsafety
    · exact addDefinition.WF_safe_natMul wf v h hsafety
    · exact addDefinition.WF_safe_natPow wf v h hsafety
    · exact addDefinition.WF_safe_natGcd wf v h hsafety
    · exact addDefinition.WF_safe_natMod wf v h hsafety
    · exact addDefinition.WF_safe_natDiv wf v h hsafety
    · exact addDefinition.WF_safe_natBEq wf v h hsafety
    · exact addDefinition.WF_safe_natBLE wf v h hsafety
    · exact addDefinition.WF_safe_natBitwise wf v h hsafety
    · exact addDefinition.WF_safe_natLand wf v h hsafety
    · exact addDefinition.WF_safe_natLor wf v h hsafety
    · exact addDefinition.WF_safe_natXor wf v h hsafety
    · exact addDefinition.WF_safe_natShiftLeft wf v h hsafety
    · exact addDefinition.WF_safe_natShiftRight wf v h hsafety
    · exact addDefinition.WF_safe_stringOfList wf v h hsafety
    · exact addDefinition.WF_safe_charOfNat wf v h hsafety

theorem addDefinition.WF_partial
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  by_cases hn : ¬Lean.Kernel.Environment.primitives.contains v.name
  · exact addDefinition.WF_partial_of_not_primitive wf v hsafety hn
  · exact addDefinition.WF_partial_of_primitive wf v hsafety
      (Classical.byContradiction fun h => hn h)

theorem addDefinition.WF_unsafe
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .unsafe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  simp [hsafety]
  refine (checkConstantVal.WF
    (c := .mk' wf .unsafe v.levelParams) (s := {})
    (env := env) (v := v.toConstantVal)
    (wf.tr (safety := .unsafe)).map_wf).run wf |>.bind
      fun _ hchecked => ?_
  obtain ⟨hfresh, hreserved, type', htype, htypeWF⟩ := hchecked
  have hn : ¬Lean.Kernel.Environment.primitives.contains v.name := by
    intro hp
    have := hreserved hp
    contradiction
  let header : AxiomVal := { v.toConstantVal with isUnsafe := true }
  let vconst : VConstant := {
    uvars := v.levelParams.length
    type := type' }
  have hheaderTr : TrConstant .unsafe (ves.venv .unsafe)
      (.axiomInfo header) vconst := by
    exact ⟨by
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial, header], rfl, htype⟩
  have hheaderWF : vconst.WF (ves.venv .unsafe) := htypeWF
  obtain ⟨vesH, wfH, hmonoH, haddH⟩ :=
    wf.addUnsafeAxiom_of_not_primitive (v := header) (v' := vconst)
      (by simp [header]) hfresh hheaderTr hheaderWF hn
  refine checkNoMVarNoFVar.WF.bind fun _ hclosed => ?_
  have htypeH : TrExprS (vesH.venv .unsafe) v.levelParams []
      v.type type' := htype.mono (hmonoH .unsafe)
  have hbodyRun := (checkBodyCore.WF
    (env := env.add (.axiomInfo header)) wfH
    (.defnDecl v) v.name v.levelParams v.type v.value type'
    htypeH hclosed).run wfH
  simp only [header, Bool.not_eq_true'] at hbodyRun
  refine hbodyRun.map fun _ hbody => ?_
  obtain ⟨value', hvalue, hvalueWF⟩ := hbody
  let v' : VDefVal := {
    name := v.name
    uvars := v.levelParams.length
    type := type'
    value := value' }
  have hfinalHeader : TrConstVal .unsafe (ves.venv .unsafe)
      (.defnInfo v) v'.toVConstVal := by
    exact ⟨⟨by
      rw [ConstantInfo.defnInfo_safety, hsafety]
      exact DefinitionSafety.le_rfl,
      rfl, htype⟩, rfl⟩
  have hfinalHeaderWF : v'.toVConstant.WF (ves.venv .unsafe) :=
    htypeWF
  exact wf.addUnsafeDefinition_of_not_primitive hsafety hfresh
    hfinalHeader hfinalHeaderWF (by simpa [v', vconst] using haddH)
    (by simpa [v'] using hvalue) (by simpa [v'] using hvalueWF) hn

theorem addDefinition.WF
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases hsafety : v.safety with
  | «unsafe» => exact addDefinition.WF_unsafe wf v hsafety
  | safe => exact addDefinition.WF_safe wf v hsafety
  | «partial» => exact addDefinition.WF_partial wf v hsafety



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
