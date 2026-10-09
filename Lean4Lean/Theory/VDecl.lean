import Lean4Lean.Theory.VEnv

namespace Lean4Lean

namespace VEnv

/-- Add constants from left to right, failing on the first collision. -/
def addConstVals : VEnv → List VConstVal → Option VEnv
  | env, [] => some env
  | env, ci :: cis => do
    let env ← env.addConst ci.name ci.toVConstant
    env.addConstVals cis

/-- Add reduction equations from left to right. -/
def addDefEqRules : VEnv → List VDefEq → VEnv
  | env, [] => env
  | env, df :: dfs => addDefEqRules (env.addDefEq df) dfs

@[simp] theorem addDefEqRules_eliminators
    (env : VEnv) (rules : List VDefEq) :
    (env.addDefEqRules rules).eliminators = env.eliminators := by
  induction rules generalizing env with
  | nil => rfl
  | cons rule rules ih => exact ih (env := env.addDefEq rule)

@[simp] theorem addDefEqRules_projections
    (env : VEnv) (rules : List VDefEq) :
    (env.addDefEqRules rules).projections = env.projections := by
  induction rules generalizing env with
  | nil => rfl
  | cons rule rules ih =>
      exact (ih (env := env.addDefEq rule)).trans rfl

@[simp] theorem addDefEqRules_constants
    (env : VEnv) (rules : List VDefEq) :
    (env.addDefEqRules rules).constants = env.constants := by
  induction rules generalizing env with
  | nil => rfl
  | cons rule rules ih => exact ih (env := env.addDefEq rule)

end VEnv

theorem VInductDecl.typeNames_nodup
    {decl : VInductDecl} (H : decl.sourceNames.Nodup) :
    (decl.types.map (·.name)).Nodup := by
  have hprefix := (List.nodup_append.mp H).1
  simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
    VInductiveType.toVConstVal, Function.comp_def] using hprefix

theorem VInductDecl.type_eq_of_mem_name
    {decl : VInductDecl} (H : decl.sourceNames.Nodup)
    {left right : VInductiveType}
    (hleft : left ∈ decl.types) (hright : right ∈ decl.types)
    (hname : left.name = right.name) : left = right := by
  have aux : ∀ (types : List VInductiveType) {left right},
      (types.map (·.name)).Nodup → left ∈ types → right ∈ types →
      left.name = right.name → left = right := by
    intro types
    induction types with
    | nil => simp
    | cons head tail ih =>
      intro left right hnodup hleft hright hname
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · exact False.elim (hnodup.1 (by
          rw [hname]
          exact List.mem_map.mpr ⟨right, hright, rfl⟩))
      · exact False.elim (hnodup.1 (by
          rw [← hname]
          exact List.mem_map.mpr ⟨left, hleft, rfl⟩))
      · exact ih hnodup.2 hleft hright hname
  exact aux decl.types (decl.typeNames_nodup H) hleft hright hname

theorem VInductDecl.projectionEntries_origin
    {decl : VInductDecl} {entry : VProjectionEntry}
    (H : entry ∈ decl.projectionEntries) :
    ∃ type ∈ decl.types, ∃ ctor, type.ctors = [ctor] ∧
      entry = {
        typeName := type.name
        info := {
          uvars := decl.uvars
          nparams := decl.nparams
          nindices := type.numIndices
          resultLevel := type.resultLevel
          ctorName := ctor.name
          ctorType := ctor.type } } := by
  rw [VInductDecl.projectionEntries, List.mem_filterMap] at H
  rcases H with ⟨type, htype, H⟩
  cases hctors : type.ctors with
  | nil => simp [hctors] at H
  | cons ctor tail =>
    cases tail with
    | nil =>
      simp [hctors] at H
      subst entry
      exact ⟨type, htype, ctor, hctors, rfl⟩
    | cons next rest => simp [hctors] at H

theorem VInductDecl.projectionEntries_unique
    {decl : VInductDecl} (H : decl.sourceNames.Nodup)
    {left right : VProjectionEntry}
    (hleft : left ∈ decl.projectionEntries)
    (hright : right ∈ decl.projectionEntries)
    (hname : left.typeName = right.typeName) : left = right := by
  rcases decl.projectionEntries_origin hleft with
    ⟨leftType, hleftType, leftCtor, hleftCtors, rfl⟩
  rcases decl.projectionEntries_origin hright with
    ⟨rightType, hrightType, rightCtor, hrightCtors, rfl⟩
  simp only at hname
  have htype := decl.type_eq_of_mem_name H hleftType hrightType hname
  subst rightType
  rw [hleftCtors] at hrightCtors
  cases hrightCtors
  rfl

namespace VEnv

theorem addProjections_addConst
    (env : VEnv) (entries : List VProjectionEntry) (name : Name)
    (constant : VConstant) :
    (env.addProjections entries).addConst name constant =
      (env.addConst name constant).map (·.addProjections entries) := by
  unfold VEnv.addConst
  simp only [VEnv.addProjections_constants]
  split
  · rfl
  · simp only [Option.map_some]
    congr 1
    apply VEnv.ext
    · simp only [VEnv.addProjections_constants]
    · simp only [VEnv.addProjections_defeqs]
    · funext projectionName projectionInfo
      apply propext
      simp only [VEnv.addProjections_iff]
    · simp only [VEnv.addProjections_eliminators]

theorem addProjections_addConstVals
    (env : VEnv) (entries : List VProjectionEntry)
    (constants : List VConstVal) :
    (env.addProjections entries).addConstVals constants =
      (env.addConstVals constants).map (·.addProjections entries) := by
  induction constants generalizing env with
  | nil => rfl
  | cons constant constants ih =>
      simp only [VEnv.addConstVals, VEnv.addProjections_addConst]
      cases hadd : env.addConst constant.name constant.toVConstant with
      | none => rfl
      | some next => simpa [hadd] using ih next

theorem addEliminators_addConst
    (env : VEnv) (es : List (Name × InductiveSignature.CaseSchema)) (name : Name)
    (constant : VConstant) :
    (env.addEliminators es).addConst name constant =
      (env.addConst name constant).map (·.addEliminators es) := by
  unfold VEnv.addConst
  simp only [VEnv.addEliminators_constants]
  split
  · rfl
  · simp only [Option.map_some]
    congr 1
    apply VEnv.ext
    · simp only [VEnv.addEliminators_constants]
    · simp only [VEnv.addEliminators_defeqs]
    · simp only [VEnv.addEliminators_projections]
    · funext n s
      apply propext
      simp only [VEnv.addEliminators_iff]

theorem addEliminators_addConstVals
    (env : VEnv) (es : List (Name × InductiveSignature.CaseSchema))
    (constants : List VConstVal) :
    (env.addEliminators es).addConstVals constants =
      (env.addConstVals constants).map (·.addEliminators es) := by
  induction constants generalizing env with
  | nil => rfl
  | cons constant constants ih =>
      simp only [VEnv.addConstVals, VEnv.addEliminators_addConst]
      cases hadd : env.addConst constant.name constant.toVConstant with
      | none => rfl
      | some next => simpa [hadd] using ih next

end VEnv

/-- Install a compiled block in dependency order. -/
def VInductBlock.install (env : VEnv) (block : VInductBlock) : Option VEnv := do
  let env ← env.addConstVals block.types
  let env ← env.addConstVals block.ctors
  let env := env.addEliminators block.eliminators
  let env := env.addProjections block.projections
  let env ← env.addConstVals block.recursors
  return env.addDefEqRules block.rules

namespace VEnv

theorem addConstVals_defeqs {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') : env'.defeqs = env.defeqs := by
  induction cis generalizing env with
  | nil => cases H; rfl
  | cons ci cis ih =>
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some middle =>
      simp [VEnv.addConstVals, hadd] at H
      exact (ih H).trans (VEnv.addConst_defeqs hadd)

theorem addConstVals_le {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') : env ≤ env' := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConstVals] at H; subst env'; exact .rfl
  | cons ci cis ih =>
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some env₁ =>
      simp [VEnv.addConstVals, hadd] at H
      exact (VEnv.addConst_le hadd).trans (ih H)

theorem addConstVals_get {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') (hci : ci ∈ cis) :
    env'.constants ci.name = some ci.toVConstant := by
  induction cis generalizing env with
  | nil => simp at hci
  | cons head tail ih =>
    cases hadd : env.addConst head.name head.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some middle =>
      simp [VEnv.addConstVals, hadd] at H
      simp only [List.mem_cons] at hci
      rcases hci with hci | hci
      · subst head
        exact (addConstVals_le H).constants (VEnv.addConst_self hadd)
      · exact ih H hci

theorem addConstVals_names_fresh {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') :
    ∀ ci ∈ cis, env.constants ci.name = none := by
  induction cis generalizing env with
  | nil => simp
  | cons head tail ih =>
    cases hadd : env.addConst head.name head.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some middle =>
      simp [VEnv.addConstVals, hadd] at H
      intro ci hci
      simp only [List.mem_cons] at hci
      rcases hci with rfl | hci
      · unfold VEnv.addConst at hadd
        split at hadd <;> cases hadd
        assumption
      · have hfresh := ih H ci hci
        unfold VEnv.addConst at hadd
        split at hadd <;> cases hadd
        rename_i hnone
        simp only at hfresh
        split at hfresh
        · contradiction
        · exact hfresh

theorem addConstVals_projections {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') :
    env'.projections = env.projections := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConstVals] at H; subst env'; rfl
  | cons ci cis ih =>
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some middle =>
      simp [VEnv.addConstVals, hadd] at H
      exact (ih H).trans (by
        simp [VEnv.addConst] at hadd
        split at hadd <;> cases hadd
        rfl)

theorem addConstVals_eliminators {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') :
    env'.eliminators = env.eliminators := by
  induction cis generalizing env with
  | nil => simp [VEnv.addConstVals] at H; subst env'; rfl
  | cons ci cis ih =>
    cases hadd : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some middle =>
      simp [VEnv.addConstVals, hadd] at H
      exact (ih H).trans (VEnv.addConst_eliminators hadd)

theorem addConstVals_names_nodup {env env' : VEnv} {cis : List VConstVal}
    (H : env.addConstVals cis = some env') : (cis.map (·.name)).Nodup := by
  induction cis generalizing env with
  | nil => simp
  | cons head tail ih =>
    cases hadd : env.addConst head.name head.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at H
    | some middle =>
      simp [VEnv.addConstVals, hadd] at H
      have hfresh := addConstVals_names_fresh H
      have hmid := VEnv.addConst_self hadd
      refine List.nodup_cons.2 ⟨fun hm => ?_, ih H⟩
      obtain ⟨c, hc, e⟩ := List.mem_map.1 hm
      have := hfresh c hc; rw [e, hmid] at this; cases this

end VEnv
