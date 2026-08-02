import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Environment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

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
    (ci : ConstantInfo) (allowPrimitive : Bool) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams) {} fun _ _ =>
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
    (ci : ConstantInfo) (allowPrimitive : Bool) (hs : safety ≤ ci.safety) :
    (checkConstantVal env ci.toConstantVal allowPrimitive).WF
      (.mk' wf safety ci.levelParams) {} fun _ _ =>
        ∃ ci' : VConstVal, TrConstVal safety (ves.venv safety) ci ci' ∧
          ci'.toVConstant.WF (ves.venv safety) ∧ env.find? ci.name = none ∧
          (allowPrimitive = false → Environment.primitives.contains ci.name = false) := by
  exact (checkConstantValCore.WF wf ci allowPrimitive).mono fun _ _ _ h => by
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

theorem checkValue.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (ci : ConstantInfo) (ci' : VConstVal)
    (hci : TrConstVal safety (ves.venv safety) ci ci') (state : TypeChecker.VState := {}) :
    ((do
      Environment.checkNoMVarNoFVar env ci.name ci.value!
      let valueType ← TypeChecker.checkType ci.value!
      if !(← TypeChecker.isDefEq valueType ci.type) then
        throw <| Exception.declTypeMismatch env decl valueType) : TypeChecker.M Unit).WF
      (.mk' wf safety ci.levelParams) state fun _ _ =>
        ∃ ci'' : VDefVal, TrDefVal safety (ves.venv safety) ci ci'' ∧ ci''.WF (ves.venv safety) := by
  refine (checkBody.WF wf decl ci.name ci.levelParams ci.type ci.value! ci'.type hci.1.2.2 state).mono
    fun _ _ _ ⟨value', hvalue, hvalueType⟩ => ?_
  refine ⟨{ name := ci'.name, uvars := ci'.uvars, type := ci'.type, value := value' },
    ⟨hci, hvalue⟩, ?_⟩
  change (ves.venv safety).HasType ci'.uvars [] value' ci'.type
  rw [← hci.1.2.1]
  exact hvalueType

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
        ∃ ci' : VDefVal, TrThmVal .safe (ves.venv .safe) v ci' ∧ ci'.WF (ves.venv .safe) ∧
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

theorem TrEnv.exists_addConst (H : TrEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) : ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci =>
    exfalso
    obtain ⟨ci, hci, _⟩ := H.find?_iff.2 ⟨ci, hfind⟩
    rw [hn] at hci
    contradiction

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addConst name ci = some env₁') (h₂ : env₂.addConst name ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  constructor
  · intro n a ha
    simp at ha ⊢
    split at ha <;> split <;> simp_all
    exact H.constants ha
  · exact H.defeqs

theorem VEnv.addConst_eq_of_ne
    {env env' : VEnv}
    (hadd : env.addConst name ci = some env') (hne : name ≠ n) :
    env'.constants n = env.constants n := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  simp [hne]

theorem VEnv.HasPrimitives.addConst {env env' : VEnv} (H : env.HasPrimitives)
    (hname : Environment.primitives.contains name = false)
    (hadd : env.addConst name ci = some env') : env'.HasPrimitives := by
  have le := VEnv.addConst_le hadd
  have same (n : Name) (hp : Environment.primitives.contains n = true) :
      env'.constants n = env.constants n :=
    VEnv.addConst_eq_of_ne hadd fun h => by subst h; simp_all
  have oldContains (n : Name) (hp : Environment.primitives.contains n = true) :
      env'.contains n → env.contains n := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, (same n hp) ▸ hci⟩
  have newContains (n : Name) : env.contains n → env'.contains n := by
    rintro ⟨ci, hci⟩
    exact ⟨ci, le.constants hci⟩
  have primBool : Environment.primitives.contains ``Bool = true := by native_decide
  have primBoolFalse : Environment.primitives.contains ``Bool.false = true := by native_decide
  have primBoolTrue : Environment.primitives.contains ``Bool.true = true := by native_decide
  have primNat : Environment.primitives.contains ``Nat = true := by native_decide
  have primNatZero : Environment.primitives.contains ``Nat.zero = true := by native_decide
  have primNatSucc : Environment.primitives.contains ``Nat.succ = true := by native_decide
  have prim (n : Name) (h : n ∈ [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd,
      ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
      ``Nat.shiftLeft, ``Nat.shiftRight, ``Char.ofNat, ``String.ofList]) :
      Environment.primitives.contains n = true := by
    simp at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> native_decide
  constructor
  · intro h
    let ⟨h1, h2⟩ := H.bool (oldContains _ primBool h)
    exact ⟨newContains _ h1, newContains _ h2⟩
  · intro ci h; apply H.boolFalse; rwa [← same _ primBoolFalse]
  · intro ci h; apply H.boolTrue; rwa [← same _ primBoolTrue]
  · intro h
    let ⟨h1, h2⟩ := H.nat (oldContains _ primNat h)
    exact ⟨newContains _ h1, newContains _ h2⟩
  · intro ci h; apply H.natZero; rwa [← same _ primNatZero]
  · intro ci h; apply H.natSucc; rwa [← same _ primNatSucc]
  · intro h a b; exact (H.natAdd (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natSub (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natMul (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natPow (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natGcd (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natMod (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natDiv (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natBEq (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natBLE (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natLAnd (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natLOr (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natXor (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natShiftLeft (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro h a b; exact (H.natShiftRight (oldContains _ (prim _ (by simp)) h) a b).mono le
  · intro ci h; apply H.charOfNat; rwa [← same _ (prim _ (by simp))]
  · intro ci h
    obtain ⟨rfl, h2, h3⟩ := H.stringOfList (by rwa [← same _ (prim _ (by simp))])
    exact ⟨rfl, h2.mono le, h3.mono le⟩

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} (H : env.HasPrimitives) :
    (env.addDefEq df).HasPrimitives :=
  { H with
    natAdd := fun h a b => (H.natAdd h a b).mono VEnv.addDefEq_le
    natSub := fun h a b => (H.natSub h a b).mono VEnv.addDefEq_le
    natMul := fun h a b => (H.natMul h a b).mono VEnv.addDefEq_le
    natPow := fun h a b => (H.natPow h a b).mono VEnv.addDefEq_le
    natGcd := fun h a b => (H.natGcd h a b).mono VEnv.addDefEq_le
    natMod := fun h a b => (H.natMod h a b).mono VEnv.addDefEq_le
    natDiv := fun h a b => (H.natDiv h a b).mono VEnv.addDefEq_le
    natBEq := fun h a b => (H.natBEq h a b).mono VEnv.addDefEq_le
    natBLE := fun h a b => (H.natBLE h a b).mono VEnv.addDefEq_le
    natLAnd := fun h a b => (H.natLAnd h a b).mono VEnv.addDefEq_le
    natLOr := fun h a b => (H.natLOr h a b).mono VEnv.addDefEq_le
    natXor := fun h a b => (H.natXor h a b).mono VEnv.addDefEq_le
    natShiftLeft := fun h a b => (H.natShiftLeft h a b).mono VEnv.addDefEq_le
    natShiftRight := fun h a b => (H.natShiftRight h a b).mono VEnv.addDefEq_le
    stringOfList := fun h =>
      let ⟨h1, h2, h3⟩ := H.stringOfList h
      ⟨h1, h2.mono VEnv.addDefEq_le, h3.mono VEnv.addDefEq_le⟩ }

theorem VEnvs.WF.safePrimitives_add {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hn : Environment.primitives.contains ci.name = false) :
    (env.add ci).find? (n : Name) = some (ci' : ConstantInfo) → Environment.primitives.contains n →
      ci'.safety = .safe ∧ ci'.levelParams = [] := by
  intro hfind hp
  have mapWF := (wf.tr (safety := .safe)).map_wf
  have hnone : env.constants.find? ci.name = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hfresh
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = some ci' at hfind
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert] at hfind
  split at hfind
  · cases hfind
    rename_i heq
    have heq' := LawfulBEq.eq_of_beq heq
    cases heq'
    simp_all
  · apply wf.safePrimitives ?_ hp
    rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]
    exact hfind

theorem addConst.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (hnonprim : Environment.primitives.contains ci.name = false)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  classical
  have hnMap : env.constants.find? ci.name = none := by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hn
  have visible_tr (safety) (hvisible : safety ≤ ci.safety) :
      TrConstant safety (ves.venv safety) ci ci'.toVConstant :=
    (htr.1.sf_mono (visible_le safety hvisible)).mono (wf.mono (visible_le safety hvisible))
  have visible_wf (safety) (hvisible : safety ≤ ci.safety) :
      ci'.toVConstant.WF (ves.venv safety) :=
    hci.mono (wf.mono (visible_le safety hvisible))
  have hex (safety) (hvisible : safety ≤ ci.safety) :=
    (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
  let next (safety : DefinitionSafety) : VEnv :=
    if hvisible : safety ≤ ci.safety then Classical.choose (hex safety hvisible)
    else ves.venv safety
  have hadd (safety) (hvisible : safety ≤ ci.safety) :
      (ves.venv safety).addConst ci.name ci'.toVConstant = some (next safety) := by
    simpa [next, hvisible] using Classical.choose_spec (hex safety hvisible)
  let ves' : VEnvs := ⟨next⟩
  refine ⟨ves', ?_, ?_⟩
  · refine {
      tr := ?_
      hasPrimitives := ?_
      safePrimitives := wf.safePrimitives_add ci hn hnonprim
      mono := ?_ }
    · intro safety
      change TrEnv' safety (env.constants.insert ci.name ci) env.quotInit (next safety)
      by_cases hvisible : safety ≤ ci.safety
      · exact step safety _ (visible_tr safety hvisible) (visible_wf safety hvisible)
          (hadd safety hvisible) (wf.tr (safety := safety))
      · simpa [next, hvisible] using
          TrEnv'.ignore (ci := ci) hnMap hvisible (wf.tr (safety := safety))
    · intro safety
      by_cases hvisible : safety ≤ ci.safety
      · exact (wf.hasPrimitives (safety := safety)).addConst hnonprim (hadd safety hvisible)
      · simpa [ves', next, hvisible] using wf.hasPrimitives (safety := safety)
    · intro safety safety' hle
      change next safety' ≤ next safety
      by_cases hvisible' : safety' ≤ ci.safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        rw [show next safety' = Classical.choose (hex safety' hvisible') by simp [next, hvisible'],
          show next safety = Classical.choose (hex safety hvisible) by simp [next, hvisible]]
        exact VEnv.addConst_mono (wf.mono hle)
          (Classical.choose_spec (hex safety' hvisible'))
          (Classical.choose_spec (hex safety hvisible))
      · rw [show next safety' = ves.venv safety' by simp [next, hvisible']]
        by_cases hvisible : safety ≤ ci.safety
        · rw [show next safety = Classical.choose (hex safety hvisible) by simp [next, hvisible]]
          exact (wf.mono hle).trans
            (VEnv.addConst_le (Classical.choose_spec (hex safety hvisible)))
        · rw [show next safety = ves.venv safety by simp [next, hvisible]]
          exact wf.mono hle
  · intro safety
    change ves.venv safety ≤ next safety
    by_cases hvisible : safety ≤ ci.safety
    · simpa [next, hvisible] using VEnv.addConst_le (hadd safety hvisible)
    · simp [next, hvisible, VEnv.LE.rfl]

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf (.axiomInfo v) false hsafety).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hci, hn, hnonprim⟩ := h
  refine .pure <| addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (hnonprim rfl) fun _ _ htr hci hadd old => ?_
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr
      (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addTheorem
  refine (checkTheorem.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  refine .pure <| addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn hnonprim
    fun safety _ hheader _ hadd old => ?_
  have hle := wf.mono hheader.1
  have htr' : TrThmVal safety (ves.venv safety) v ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem checkOpaqueHeader.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : OpaqueVal) :
    (TypeChecker.M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := {}) (do
      checkConstantVal env v.toConstantVal
      let valueType ← TypeChecker.checkType v.value
      if !(← TypeChecker.isDefEq valueType v.type) then
        throw <| Exception.declTypeMismatch env (.opaqueDecl v) valueType)).WF fun _ =>
      ∃ ci' : VConstVal,
        v.levelParams.length = ci'.uvars ∧
        TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type ∧
        v.name = ci'.name ∧
        ci'.toVConstant.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
        Environment.primitives.contains v.name = false := by
  intro _ hrun
  simp only [TypeChecker.M.run, StateT.run', Functor.map, Except.map] at hrun
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind] at hrun
  generalize hhead : checkConstantVal env v.toConstantVal false
    { env := env, lctx := {}, lparams := v.levelParams } ({} : TypeChecker.State) = r at hrun
  cases r with
  | error e => simp at hrun
  | ok p =>
    rcases p with ⟨u, state⟩
    have hw := checkConstantValCore.WF (safety := .safe) wf (.opaqueInfo v) false
    obtain ⟨_, _, _, _, h⟩ := hw TypeChecker.VState.WF.empty u state hhead
    simpa [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal] using h

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  unfold addOpaque
  refine (checkOpaqueHeader.WF wf v).bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hci, hfresh, hnonprim⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci' :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  refine .pure <| addConst.WF wf (.opaqueInfo v) ci' checkSafety ?_ htr
    (hci.mono hmono) hfresh hnonprim fun _ _ htr hci hadd old => ?_
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · exact .opaque ⟨htr, hname⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

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
