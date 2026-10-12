import Lean4Lean.Theory.Inductive
import Lean4Lean.Tests.ShapeDecide
import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped

namespace Lean4Lean.Tests.InductiveTheory

open Lean4Lean

def enumCtor : VConstVal where
  name := `Enum0.mk
  uvars := 0
  type := .const `Enum0 []

def enumType : VInductiveType where
  name := `Enum0
  uvars := 0
  type := .sort (.succ .zero)
  numIndices := 0
  resultLevel := .succ .zero
  ctors := [enumCtor]

def enumSignature : InductiveSignature where
  uvars := 0
  params := []
  families := #[{ name := `Enum0, indices := [], resultLevel := .succ .zero }]
  constructors := #[{ name := `Enum0.mk, owner := ⟨0, by decide⟩, fields := [], indices := [] }]

def enumInstance : InductiveSignature.Instance enumSignature where
  uvars := 0
  levels := []
  targetLevel := .zero
  recursorName := fun _ => `Enum0.rec

def enumMotive : VExpr := .forallE (.const `Enum0 []) (.sort .zero)
def enumMinor : VExpr := .app (.bvar 0) (.const `Enum0.mk [])

def enumRecursor : VConstVal := enumInstance.recursor ⟨0, by decide⟩

def enumRule : VDefEq := enumInstance.equation ⟨0, by decide⟩

/-- The kernel's rule of `Enum0.rec`: on `Enum0.mk`, return the minor premise. -/
def enumRecRule : VRecRule where
  ctor := `Enum0.mk
  ctorParams := 0
  nfields := 0
  rhs := enumRule.rhs

/-- The kernel's recursor of `Enum0`, with its rule. -/
def enumVRec : VRecursor :=
  { enumRecursor with
    all := [`Enum0]
    numParams := 0
    numMotives := 1
    numMinors := 1
    numIndices := 0
    k := false
    rules := [enumRecRule] }

def enumDecl : VInductDecl where
  uvars := 0
  nparams := 0
  types := [enumType]
  isUnsafe := false
  recs := [enumVRec]

def enumTypesEnv : VEnv where
  constants := fun n => if `Enum0 = n then some enumType.toVConstant else none
  defeqs := fun _ => False
  pats := fun _ _ => False

def enumCtorsEnv : VEnv where
  constants := fun n =>
    if `Enum0.mk = n then some enumCtor.toVConstant else enumTypesEnv.constants n
  defeqs := fun _ => False
  pats := fun _ _ => False

theorem enumDecl_wf : enumDecl.SourceWF .empty ∧ enumDecl.FormationWF .empty := by
  unfold VInductDecl.SourceWF
  have haddType : VEnv.empty.addConstVals enumDecl.typeConstants = some enumTypesEnv := by
    simp [enumDecl, enumType, enumTypesEnv, VInductDecl.typeConstants,
      VEnv.addConstVals, VEnv.addConst, VEnv.empty]
  have haddCtor : enumTypesEnv.addConstVals enumDecl.constructorConstants = some enumCtorsEnv := by
    simp [enumDecl, enumType, enumCtor, enumTypesEnv, enumCtorsEnv,
      VInductDecl.constructorConstants, VEnv.addConstVals, VEnv.addConst]
  have htype : enumType.toVConstant.WF VEnv.empty := by
    exact ⟨_, .sortDF (by trivial) (by trivial) (by rfl)⟩
  have hlookup : enumTypesEnv.constants `Enum0 = some enumType.toVConstant := by
    simp [enumTypesEnv]
  have hctor : enumCtor.toVConstant.WF enumTypesEnv := by
    exact ⟨_, .constDF hlookup nofun nofun rfl .nil⟩
  constructor
  · refine ⟨by simp [enumDecl], by simp [enumDecl, VInductDecl.sourceNames,
      VInductDecl.typeConstants, VInductDecl.constructorConstants, enumType, enumCtor], ?_, ?_,
      enumTypesEnv, enumCtorsEnv, haddType, haddCtor, ?_, ?_⟩
    · simp [enumDecl, enumType]
    · simp [enumDecl, enumType, enumCtor, VInductDecl.constructorConstants]
    · intro type hmem
      simp only [enumDecl, List.mem_singleton] at hmem
      subst type
      exact htype
    · intro ctor hmem
      simp only [enumDecl, enumType, VInductDecl.constructorConstants,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hmem
      subst ctor
      exact hctor
  · apply VInductDecl.FormationWF.ordinary
    unfold VInductDecl.OrdinaryFormationWF
    refine ⟨[], .succ .zero, enumTypesEnv, haddType, ?_, ?_⟩
    · intro type hmem
      simp [enumDecl] at hmem
      subst type
      refine ⟨rfl, .sort (.succ .zero), [], .sort (.succ .zero), [],
        .sort (.succ .zero), .sort (.succ (.succ .zero)), ?_, rfl, rfl, ?_, ?_⟩
      · exact .sortDF (by trivial) (by trivial) rfl
      · exact .zero
      · exact .sortDF (by trivial) (by trivial) rfl
    · refine ⟨fun type htypeMem ctor hctorMem => ?_, fun type htypeMem ctor hctorMem => ?_⟩
      · simp [enumDecl] at htypeMem
        subst type
        simp [enumType] at hctorMem
        subst ctor
        refine ⟨?_, ?_⟩
        · exact ⟨[], enumCtor.type, rfl, .zero⟩
        · refine ⟨.const `Enum0 [], [], .const `Enum0 [], .sort (.succ .zero), [],
            ?_, rfl, .zero, .zero, ?_⟩
          · exact .constDF hlookup nofun nofun rfl .nil
          · apply VInductDecl.CtorTailWF.result
              (result' := .const `Enum0 []) (type := .sort (.succ .zero))
            · simp [VInductDecl.ValidIndAppAt, VInductDecl.RawIndAppAt, VExpr.getAppFnArgs, enumDecl,
                enumType, VExpr.getAppFnArgs.go, VInductDecl.paramVars]
            · exact .constDF hlookup nofun nofun rfl .nil
      · simp [enumDecl] at htypeMem
        subst type
        simp [enumType] at hctorMem
        subst ctor
        refine ⟨[], .const `Enum0 [], rfl, by simp [enumDecl], ?_, rfl⟩
        simp [VInductDecl.ValidIndAppAt, VInductDecl.RawIndAppAt, VExpr.getAppFnArgs, enumDecl,
          enumType, VExpr.getAppFnArgs.go, VInductDecl.paramVars]

theorem recursiveOccurrence_positive :
    enumDecl.SyntacticallyPositive {} [] 0 (.const `Enum0 []) := by
  apply VInductDecl.SyntacticallyPositive.recursive
  simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go,
    enumDecl, enumType, VInductDecl.paramVars]

theorem negativeOccurrence_not_positive :
    ¬enumDecl.SyntacticallyPositive {} [] 0
      (.forallE (.const `Enum0 []) (.const `Enum0 [])) := by
  intro h
  cases h with
  | nonrecursive h =>
      cases h with
      | forallE hdom _ =>
          cases hdom with
          | const _ _ hf => exact hf (by simp [enumDecl, enumType])
  | forallE h _ _ _ =>
      cases h with
      | const _ _ hf => exact hf (by simp [enumDecl, enumType])
  | recursive h =>
    simp [VInductDecl.ValidIndAppAt, VExpr.getAppFnArgs, VExpr.getAppFnArgs.go,
      enumDecl, enumType] at h


def enumRecursorShape : enumDecl.RecursorShape enumType enumRecursor where
  ownerIdx := 0
  owner_lt := by simp [enumDecl]
  owner_eq := rfl
  name := by rfl
  uvars := Or.inl rfl
  params := []
  motives := [enumMotive]
  minors := [enumMinor]
  indices := []
  major := [.const `Enum0 []]
  afterParams := enumRecursor.type
  afterMotives := .forallE enumMinor
    (.forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0)))
  afterMinors := .forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0))
  afterIndices := .forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0))
  result := .app (.bvar 2) (.bvar 0)
  params_take := rfl
  motives_take := rfl
  minors_take := rfl
  indices_take := rfl
  major_take := rfl
  result_eq := by
    simp [VInductDecl.recursorResult, VInductDecl.recursorResultWithCounts,
      enumDecl, enumType, VExpr.mkApps]

def enumNestedRecursorShape :
    enumDecl.NestedRecursorShape enumType enumRecursor :=
  enumRecursorShape.toNested.ofCompatible
    (by simpa [enumDecl] using enumRecursorShape.toNested.owner_lt)
    (by simp [enumDecl, enumType])
    (by rfl)
    (Or.inl rfl) rfl
    enumRecursorShape.toNested.source_motives
    enumRecursorShape.toNested.source_minors rfl


def enumBlock : VInductBlock where
  types := enumDecl.typeConstants
  ctors := enumDecl.constructorConstants
  recursors := [enumRecursor]
  rules := [enumRule]
  projections := enumDecl.projectionEntries

def enumIota : enumDecl.IotaRule enumCtorsEnv enumBlock enumType enumCtor
    enumRule where
  recursor := enumRecursor
  recursor_mem := by simp [enumBlock]
  recursor_name := by rfl
  rule_uvars := rfl
  domains := [enumMotive, enumMinor]
  lhsBody := VExpr.mkApps (.const `Enum0.rec [])
    [.bvar 1, .bvar 0, .const `Enum0.mk []]
  rhsBody := .bvar 0
  typeBody := .app (.bvar 1) (.const `Enum0.mk [])
  lhs_wrapped := rfl
  rhs_wrapped := rfl
  type_wrapped := rfl
  recursorLevels := []
  leadingArgs := [.bvar 1, .bvar 0]
  ctorLevels := []
  ctorArgs := []
  lhs_pattern := rfl
  recursor_levels := rfl
  ctor_levels := rfl
  leading_arity := rfl
  constructor_arity := by simp [enumDecl]
  parameter_args := rfl
  domains_arity := rfl
  recursiveFields := []
  fieldPositions := []
  fieldPositions_eq := rfl
  fieldPositions_ordered := by simp
  fields_at_positions := by simp
  recursiveArgs := []
  recursiveArgs_eq := rfl
  recursive_args := .slnil
  fieldVars := []
  fieldVars_eq := rfl
  fields_in_scope := by simp
  minorVar := 0
  minor_in_scope := by simp
  rhsArgs := []
  rhs_spine := rfl
  field_args := rfl
  recursive_results := rfl
  rhs_guarded := .bvar

theorem enumCanonicalCompilation : InductiveSignature.Compiles .empty enumDecl enumBlock := by
  have hadd : VEnv.empty.addConstVals enumDecl.typeConstants = some enumTypesEnv := by
    simp [enumDecl, enumType, enumTypesEnv, VInductDecl.typeConstants,
      VEnv.addConstVals, VEnv.addConst, VEnv.empty]
  refine ⟨enumSignature, enumInstance, enumTypesEnv, ?_, hadd, ?_, ?_, ?_, rfl, rfl⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_, Or.inr ?_, ?_⟩
    · change List.Forall₂ _ [enumType] [enumType]
      exact .cons ⟨rfl, rfl, rfl, (by rfl), rfl⟩ .nil
    · refine ⟨enumTypesEnv, hadd, ?_⟩
      change List.Forall₂ _ [enumCtor] [enumCtor]
      refine .cons ⟨rfl, rfl, ?_⟩ .nil
      exact ⟨_, .constDF (ci := enumType.toVConstant) (by simp [enumTypesEnv]) nofun nofun rfl .nil⟩
    · refine ⟨enumTypesEnv, hadd, ?_⟩
      intro ctor hctor i hi
      have hctor := List.mem_singleton.mp hctor
      subst ctor
      exact (Nat.not_lt_zero i hi).elim
    · intro ctor hctor
      have hctor := List.mem_singleton.mp hctor
      subst ctor
      rfl
  · exact ⟨rfl, nofun, by trivial, Or.inr (Or.inl (by rfl))⟩
  · refine ⟨enumCtorsEnv, ?_, ?_, ?_⟩
    · simp [enumDecl, enumType, enumCtor, enumTypesEnv, enumCtorsEnv,
        VInductDecl.constructorConstants, VEnv.addConstVals, VEnv.addConst]
    · intro index j hj
      rcases index with ⟨_ | k, hk⟩
      · have h0 : (InductiveSignature.Instance.recursiveFields
            enumSignature.constructors[(⟨0, hk⟩ : Fin enumSignature.constructors.size)]).length = 0 := rfl
        omega
      · simp [enumSignature] at hk
    · -- The family has no parameters or indices: `Enum0 : Sort 1`.
      intro owner
      have h : owner = (⟨0, by decide⟩ : Fin enumSignature.families.size) := by
        apply Fin.ext
        have hi : owner.val < 1 := owner.isLt
        change owner.val = 0
        omega
      subst owner
      refine ⟨trivial, ?_⟩
      change (enumCtorsEnv.addProjections enumDecl.projectionEntries).HasType 0 []
        (.const `Enum0 []) (.sort (.succ .zero))
      exact .constDF (ci := enumType.toVConstant)
        (by simp [enumCtorsEnv, enumTypesEnv, VEnv.addProjections_constants]) nofun nofun rfl .nil
  · intro owner
    have h : owner = (⟨0, by decide⟩ : Fin enumSignature.families.size) := by
      apply Fin.ext
      have hi : owner.val < 1 := owner.isLt
      change owner.val = 0
      omega
    subst owner
    rfl

private theorem addEnumTypes :
    VEnv.empty.addConstVals enumDecl.typeConstants = some enumTypesEnv := by
  simp [enumDecl, enumType, enumTypesEnv, VInductDecl.typeConstants,
    VEnv.addConstVals, VEnv.addConst, VEnv.empty]

private theorem addEnumConstructors :
    enumTypesEnv.addConstVals enumDecl.constructorConstants = some enumCtorsEnv := by
  simp [enumDecl, enumType, enumCtor, enumTypesEnv, enumCtorsEnv,
    VInductDecl.constructorConstants, VEnv.addConstVals, VEnv.addConst]

/-- Formation is proved independently of the generated recursor and equation. -/
theorem enumFormation : VInductDecl.OrdinaryFormationWF .empty enumDecl := by
  have hlookup : enumTypesEnv.constants `Enum0 = some enumType.toVConstant := by
    simp [enumTypesEnv]
  refine ⟨[], .succ .zero, enumTypesEnv, addEnumTypes, ?_, ?_, ?_⟩
  · intro type hmem
    simp [enumDecl] at hmem
    subst type
    refine ⟨rfl, .sort (.succ .zero), [], .sort (.succ .zero), [],
      .sort (.succ .zero), .sort (.succ (.succ .zero)), ?_, rfl, rfl, ?_, ?_⟩
    · exact .sortDF (by trivial) (by trivial) rfl
    · exact .zero
    · exact .sortDF (by trivial) (by trivial) rfl
  · intro type htype ctor hctor
    simp [enumDecl] at htype
    subst type
    simp [enumType] at hctor
    subst ctor
    refine ⟨⟨[], enumCtor.type, rfl, .zero⟩, ?_⟩
    refine ⟨.const `Enum0 [], [], .const `Enum0 [], .sort (.succ .zero), [],
      ?_, rfl, .zero, .zero, ?_⟩
    · exact .constDF hlookup nofun nofun rfl .nil
    · apply VInductDecl.CtorTailWF.result
        (result' := .const `Enum0 []) (type := .sort (.succ .zero))
      · simp [VInductDecl.ValidIndAppAt, VInductDecl.RawIndAppAt, VExpr.getAppFnArgs, enumDecl,
          enumType, VExpr.getAppFnArgs.go, VInductDecl.paramVars]
      · exact .constDF hlookup nofun nofun rfl .nil
  · intro type htype ctor hctor
    simp [enumDecl] at htype
    subst type
    simp [enumType] at hctor
    subst ctor
    refine ⟨[], .const `Enum0 [], rfl, by simp [enumDecl], ?_, rfl⟩
    simp [VInductDecl.ValidIndAppAt, VInductDecl.RawIndAppAt, VExpr.getAppFnArgs, enumDecl,
      enumType, VExpr.getAppFnArgs.go, VInductDecl.paramVars]

private def projectedCtorsEnv : VEnv := enumCtorsEnv.addProjections enumBlock.projections

private def enumRecursorsEnv : VEnv where
  constants := fun n => if `Enum0.rec = n then some enumRecursor.toVConstant
    else projectedCtorsEnv.constants n
  defeqs := projectedCtorsEnv.defeqs
  pats := projectedCtorsEnv.pats
  projections := projectedCtorsEnv.projections

private theorem addEnumRecursor :
    projectedCtorsEnv.addConstVals enumBlock.recursors = some enumRecursorsEnv := by
  simp [enumBlock, VEnv.addConstVals, VEnv.addConst, enumRecursor,
    InductiveSignature.Instance.recursor, enumInstance, enumRecursorsEnv,
    projectedCtorsEnv, enumCtorsEnv, enumTypesEnv]

private theorem enumTypeTyping {env : VEnv} (Γ : List VExpr)
    (h : env.constants `Enum0 = some enumType.toVConstant) :
    env.HasType 0 Γ (.const `Enum0 []) (.sort (.succ .zero)) :=
  .constDF h nofun nofun rfl .nil

private theorem enumConstructorTyping {env : VEnv} (Γ : List VExpr)
    (h : env.constants `Enum0.mk = some enumCtor.toVConstant) :
    env.HasType 0 Γ (.const `Enum0.mk []) (.const `Enum0 []) :=
  .constDF h nofun nofun rfl .nil

private theorem enumMotiveTyping {env : VEnv} (Γ : List VExpr)
    (h : env.constants `Enum0 = some enumType.toVConstant) :
    env.HasType 0 Γ enumMotive (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF (enumTypeTyping Γ h) (.sortDF trivial trivial rfl)

private theorem enumMinorTyping {env : VEnv}
    (h : env.constants `Enum0.mk = some enumCtor.toVConstant) :
    env.HasType 0 [enumMotive] enumMinor (.sort .zero) := by
  have hm : env.HasType 0 [enumMotive] (.bvar 0) enumMotive := .bvar .zero
  exact hm.app (enumConstructorTyping _ h)

private theorem enumRecursorTyping : enumRecursor.toVConstant.WF projectedCtorsEnv := by
  have ht : projectedCtorsEnv.constants `Enum0 = some enumType.toVConstant := by
    simp [projectedCtorsEnv, enumCtorsEnv, enumTypesEnv]
  have hc : projectedCtorsEnv.constants `Enum0.mk = some enumCtor.toVConstant := by
    simp [projectedCtorsEnv, enumCtorsEnv]
  have hm : projectedCtorsEnv.HasType 0 [.const `Enum0 [], enumMinor, enumMotive]
      (.bvar 2) enumMotive := .bvar (.succ (.succ .zero))
  have hx : projectedCtorsEnv.HasType 0 [.const `Enum0 [], enumMinor, enumMotive]
      (.bvar 0) (.const `Enum0 []) := .bvar .zero
  exact ⟨_, .forallEDF (enumMotiveTyping [] ht)
    (.forallEDF (enumMinorTyping hc) (.forallEDF (enumTypeTyping _ ht) (hm.app hx)))⟩

private theorem enumEquationTyping : enumRule.WF enumRecursorsEnv := by
  have ht : enumRecursorsEnv.constants `Enum0 = some enumType.toVConstant := by
    simp [enumRecursorsEnv, projectedCtorsEnv, enumCtorsEnv, enumTypesEnv]
  have hc : enumRecursorsEnv.constants `Enum0.mk = some enumCtor.toVConstant := by
    simp [enumRecursorsEnv, projectedCtorsEnv, enumCtorsEnv]
  have hr : enumRecursorsEnv.constants `Enum0.rec = some enumRecursor.toVConstant := by
    simp [enumRecursorsEnv]
  have hrec : enumRecursorsEnv.HasType 0 [enumMinor, enumMotive]
      (.const `Enum0.rec []) enumRecursor.type := .constDF hr nofun nofun rfl .nil
  have hm : enumRecursorsEnv.HasType 0 [enumMinor, enumMotive]
      (.bvar 1) enumMotive := .bvar (.succ .zero)
  have hminor : enumRecursorsEnv.HasType 0 [enumMinor, enumMotive]
      (.bvar 0) (.app (.bvar 1) (.const `Enum0.mk [])) := .bvar .zero
  constructor
  · refine .lamDF (enumMotiveTyping [] ht) (.lamDF (enumMinorTyping hc) ?_)
    exact ((hrec.app hm).app hminor).app (enumConstructorTyping _ hc)
  · exact .lamDF (enumMotiveTyping [] ht)
      (.lamDF (enumMinorTyping hc) (.bvar .zero))

/-- Every generated declaration is typed at its installation stage; the
equation sides are typed before adding that equation to the environment. -/
theorem enumBlockWellFormed : enumBlock.WF .empty := by
  refine ⟨enumTypesEnv, enumCtorsEnv, enumRecursorsEnv,
    addEnumTypes, addEnumConstructors, addEnumRecursor, ?_, ?_, ?_, ?_⟩
  · intro ci hci
    change ci ∈ [enumType.toVConstVal] at hci
    have := List.mem_singleton.mp hci
    subst ci
    exact ⟨_, .sortDF trivial trivial rfl⟩
  · intro ci hci
    change ci ∈ [enumCtor] at hci
    have := List.mem_singleton.mp hci
    subst ci
    exact ⟨_, enumTypeTyping [] (by simp [enumTypesEnv])⟩
  · intro ci hci
    have := List.mem_singleton.mp hci
    subst ci
    exact enumRecursorTyping
  · intro df hdf
    have := List.mem_singleton.mp hdf
    subst df
    exact enumEquationTyping

theorem enumOrdinaryCompilation : enumDecl.CompilesTo .empty enumBlock :=
  CompiledInductive.ordinary enumDecl_wf.1 enumFormation
    enumCanonicalCompilation enumBlockWellFormed rfl rfl rfl (by
      simp [enumBlock, enumDecl, enumType, enumCtor, enumRecursor,
        VInductDecl.typeConstants, VInductDecl.constructorConstants,
        InductiveSignature.Instance.recursor, enumInstance])

theorem enumCompiles : VInductDecl.CompilesTo .empty enumDecl enumBlock :=
  enumOrdinaryCompilation

/-! ### The full judgment

`enumDecl` carries the kernel's recursor `Enum0.rec` with its rule (`enumVRec`), so it satisfies
every clause of `VInductDecl.WF`: its recursor and rule are read off the compiled block
(`RecsOf`), the recursor is typed in the projection-stage environment, its telescope and rule
have the kernel's shapes, and the rule is a typed schematic reduction rule (`VEnv.PatTyped`) in
the recursor-stage environment, as `VEnv.addInduct` registers it in `pats`. -/

theorem enumRecsOf : enumDecl.RecsOf enumBlock where
  recursors := rfl
  rules := by
    intro r hr ru hru
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    simp only [enumVRec, List.mem_singleton] at hru
    subst ru
    exact ⟨enumRule, List.mem_singleton_self _, rfl, rfl, rfl, _, rfl, rfl, rfl⟩
  rules_total := by
    intro df hdf
    simp only [enumBlock, List.mem_singleton] at hdf
    subst df
    exact ⟨enumVRec, List.mem_singleton_self _, enumRecRule, List.mem_singleton_self _,
      rfl, rfl, rfl, _, rfl, rfl, rfl⟩

private theorem addEnumTypesCtors : enumDecl.addTypesCtors .empty = some enumCtorsEnv := by
  simp only [VInductDecl.addTypesCtors, VInductDecl.addTypes_eq_addConstVals, addEnumTypes,
    Option.bind_eq_bind, Option.bind_some, VInductDecl.addCtors_eq_addConstVals,
    addEnumConstructors]

private theorem addEnumTypesCtorsProjs :
    enumDecl.addTypesCtorsProjs .empty = some projectedCtorsEnv := by
  simp only [VInductDecl.addTypesCtorsProjs, addEnumTypesCtors, Option.map_some]
  rfl

private theorem addEnumTypesCtorsProjsRecs :
    enumDecl.addTypesCtorsProjsRecs .empty = some enumRecursorsEnv := by
  simp only [VInductDecl.addTypesCtorsProjsRecs, addEnumTypesCtorsProjs, Option.bind_eq_bind,
    Option.bind_some]
  simpa [VInductDecl.addRecs, enumDecl, enumBlock, VEnv.addConstVals, enumVRec] using
    addEnumRecursor

private theorem enumMinorTyping' {env : VEnv} (Γ : List VExpr)
    (h : env.constants `Enum0.mk = some enumCtor.toVConstant) :
    env.HasType 0 (enumMotive :: Γ) enumMinor (.sort .zero) := by
  have hm : env.HasType 0 (enumMotive :: Γ) (.bvar 0) enumMotive := .bvar .zero
  exact hm.app (enumConstructorTyping _ h)

/-- The rule of `Enum0.rec` is a typed ι rule of the recursor-stage environment: the generic
redex `Enum0.rec motive minor Enum0.mk` and the reduct `(λ motive minor. minor) motive minor`
both have type `motive Enum0.mk` in the context of the motive and the minor premise. -/
private theorem enumRulePatTyped (hc : enumRecRule.rhs.Closed) :
    enumRecursorsEnv.PatTyped
      (SimplePattern.iota `Enum0.rec (2 + 0) `Enum0.mk (0 + 0)).toPattern
      (SimplePattern.iotaRHS' `Enum0.rec `Enum0.mk 2 0 0 0 enumRecRule.rhs hc, .true) := by
  have ht : enumRecursorsEnv.constants `Enum0 = some enumType.toVConstant := by
    simp [enumRecursorsEnv, projectedCtorsEnv, enumCtorsEnv, enumTypesEnv]
  have hk : enumRecursorsEnv.constants `Enum0.mk = some enumCtor.toVConstant := by
    simp [enumRecursorsEnv, projectedCtorsEnv, enumCtorsEnv]
  have hr : enumRecursorsEnv.constants `Enum0.rec = some enumRecursor.toVConstant := by
    simp [enumRecursorsEnv]
  let recArgs : List VExpr := [.bvar 1, .bvar 0]
  let ctorArgs : List VExpr := []
  have h1 : recArgs.length = 2 + 0 := rfl
  have h2 : ctorArgs.length = 0 + 0 := rfl
  obtain ⟨g1, hm1, hg1⟩ := Pattern.matches_varN_const (c := `Enum0.rec) (ls := []) _ _ h1
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := `Enum0.mk) (ls := []) _ _ h2
  have hpaths := SimplePattern.iotaPaths_map (m2 := Sum.elim g1 g2) h1 h2 hg1 hg2
  have happ := SimplePattern.iotaRHS'_apply `Enum0.rec `Enum0.mk 2 0 0 0 enumRecRule.rhs hc
    (VLevel.params 0)
    (Sum.elim g1 g2) h1 h2 hg1 hg2
  refine ⟨0, [enumMinor, enumMotive], _, Sum.elim g1 g2, .app (.bvar 1) (.const `Enum0.mk []),
    .app hm1 hm2, ?_, ?_, ?_⟩
  · exact Pattern.RHS.generic_foldl_var (hpaths.trans rfl)
  · have hrec : enumRecursorsEnv.HasType 0 [enumMinor, enumMotive]
        (.const `Enum0.rec []) enumRecursor.type := .constDF hr nofun nofun rfl .nil
    exact ((hrec.app (.bvar (.succ .zero))).app (.bvar .zero)).app (enumConstructorTyping _ hk)
  · dsimp only
    rw [happ]
    have hlam : enumRecursorsEnv.HasType 0 [enumMinor, enumMotive] enumRecRule.rhs
        (.forallE enumMotive (.forallE enumMinor (.app (.bvar 1) (.const `Enum0.mk [])))) :=
      .lamDF (enumMotiveTyping _ ht) (.lamDF (enumMinorTyping' _ hk) (.bvar .zero))
    exact (hlam.app (.bvar (.succ .zero))).app (.bvar .zero)

/-- The full well-formedness judgment of the enumeration, with its recursor and rule. -/
theorem enumDecl_WF : enumDecl.WF .empty where
  source := enumDecl_wf.1
  formation := enumDecl_wf.2
  recsCompiled := ⟨enumBlock, enumCompiles, enumRecsOf, enumBlockWellFormed⟩
  recs_wf := by
    intro envP hP r hr
    rw [addEnumTypesCtorsProjs] at hP
    cases hP
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    exact enumRecursorTyping
  rec_shape := by
    intro r hr
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    decide
  rules_nodup := by
    intro r hr
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    decide
  rules_ctor := by
    intro envC hC r hr ru hru
    rw [addEnumTypesCtors] at hC
    cases hC
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    simp only [enumVRec, List.mem_singleton] at hru
    subst ru
    exact ⟨enumCtor.toVConstant, by simp [enumCtorsEnv, enumRecRule], by decide⟩
  rules_ctorParams := by
    intro r hr ru hru
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    simp only [enumVRec, List.mem_singleton] at hru
    subst ru
    exact Or.inl ⟨enumCtor, by simp [enumDecl, enumType, VInductDecl.constructorConstants],
      rfl, rfl⟩
  rule_shape := by
    intro r hr ru hru
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    simp only [enumVRec, List.mem_singleton] at hru
    subst ru
    exact ⟨0, by decide, enumMinor, rfl, by decide, by decide, by decide⟩
  rules_wf := by
    intro envR hR r hr ru hru hc
    rw [addEnumTypesCtorsProjsRecs] at hR
    cases hR
    simp only [enumDecl, List.mem_singleton] at hr
    subst r
    simp only [enumVRec, List.mem_singleton] at hru
    subst ru
    exact enumRulePatTyped hc

/-- The staged installation `VEnv.addInduct` succeeds: it adds the type, constructor and
recursor, and registers the rule of `Enum0.rec` in `pats` (its reduct is closed). -/
theorem enumInstalls : ∃ installed, VEnv.empty.addInduct enumDecl = some installed := by
  have hc : enumRecRule.rhs.Closed := by decide
  simp only [VEnv.addInduct, addEnumTypesCtorsProjsRecs, Option.bind_eq_bind, Option.bind_some,
    VInductDecl.addRules, enumDecl, enumVRec, List.foldlM_cons, List.foldlM_nil,
    VEnv.addRecRule, dif_pos hc]
  exact ⟨_, rfl⟩

open InductiveSignature

private theorem parameterless_recursor_motive
    {s : InductiveSignature} (g : Instance s) (owner : Fin s.families.size)
    (hp : s.params = []) :
    ∃ d e body, g.recursorType owner = .forallE (.forallE d e) body := by
  have hne : s.families.toList ≠ [] := by
    intro hn
    have hsize : s.families.size = 0 := by
      have := congrArg List.length hn
      simpa using this
    have := owner.isLt
    omega
  obtain ⟨f, fs, hfs⟩ := List.exists_cons_of_ne_nil hne
  simp only [Instance.recursorType, Instance.params, hp, List.map_nil, List.nil_append,
    Instance.motives, hfs]
  simp only [List.zipIdx_cons, List.map_cons, List.cons_append, VExpr.wrapForalls]
  simp only [Instance.motive, VExpr.wrapForalls_append]
  cases hi : insertBinders (List.map (VExpr.instL g.levels) f.indices) 0 with
  | nil => exact ⟨_, _, _, rfl⟩
  | cons a as => exact ⟨_, _, _, rfl⟩
/-- A recursor type with an arbitrary sort in place of the motive.
No signature modelling this source can generate that recursor. -/
private def malformedEnumRecursor : VConstVal where
  name := `Enum0.rec
  uvars := 0
  type := .forallE (.sort (.succ .zero))
    (.forallE (.sort .zero)
      (.forallE (.const `Enum0 []) (.app (.bvar 2) (.bvar 0))))

private def malformedEnumBlock : VInductBlock :=
  { enumBlock with recursors := [malformedEnumRecursor] }

theorem malformed_enum_not_canonical :
    ¬ InductiveSignature.Compiles .empty enumDecl malformedEnumBlock := by
  intro h
  rcases h.generated with ⟨s, g, _, hm, _, _, _, _, hr, _⟩
  have hp : s.params = [] := List.length_eq_zero_iff.mp hm.nparams
  have hmem : malformedEnumRecursor ∈ g.recursors := by
    rw [← hr]
    exact List.mem_singleton_self _
  rcases List.mem_map.mp hmem with ⟨owner, _, he⟩
  have ht := congrArg (fun c : VConstVal => c.type) he
  obtain ⟨d, e, body, ht'⟩ := parameterless_recursor_motive g owner hp
  change g.recursorType owner = _ at ht
  rw [ht'] at ht
  cases ht

/-- The ordinary entry into the finite judgment, `CompiledInductive.ordinary`,
needs `InductiveSignature.Compiles` (a signature generating the block), which the malformed
block lacks. -/
theorem malformed_enum_not_ordinary :
    ¬ ∃ _ : InductiveSignature.Compiles .empty enumDecl malformedEnumBlock,
      enumDecl.CompilesTo .empty malformedEnumBlock :=
  fun ⟨h, _⟩ => malformed_enum_not_canonical h

end Lean4Lean.Tests.InductiveTheory
