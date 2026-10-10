import Lean4Lean.Verify.Inductive.Recursor.InstanceAlignment
import Lean4Lean.Verify.Inductive.Rules.Coverage
import Lean4Lean.Verify.Inductive.Recursor.Signature.GeneratedShapes
import Lean4Lean.Verify.Inductive.Constructor.Install

/-! # The model recursors of a recursor installation

The kernel recursors of an installation (`rvals`, read off the generated entries) and the model
recursors (`recs`, PR #43's `VRecursor`) they translate to: the generated recursor constant of
each owner with the kernel's telescope split and K flag, and one `VRecRule` per kernel rule,
firing on its constructor with the declaration's parameter count and reducing to the generated
equation's right-hand side. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RecursorInstallation

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

theorem entries_lt (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) : owner.val < H.entries.length := by
  rw [H.entries_length_eq]; exact owner.isLt

/-- The kernel recursor installed for an owner. -/
noncomputable def rvalAt (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) : RecursorVal :=
  (H.generated.entry owner.val (H.entries_lt owner)).info

/-- The kernel recursors, in family order. -/
noncomputable def rvals (H : RecursorInstallation R outEnv) : List RecursorVal :=
  List.ofFn H.rvalAt

/-- The model rule of a kernel rule firing on the constructor `index`. -/
noncomputable def modelRule (H : RecursorInstallation R outEnv)
    (index : Fin H.generationSignature.constructors.size) (rule : RecursorRule) : VRecRule where
  ctor := rule.ctor
  ctorParams := decl.nparams
  nfields := rule.nfields
  rhs := (H.generationInstance.equation index).rhs

/-- The model recursor of an owner. -/
noncomputable def modelRecursor (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) : VRecursor where
  toVConstVal := H.generationInstance.recursor owner
  all := (H.rvalAt owner).all
  numParams := (H.rvalAt owner).numParams
  numMotives := (H.rvalAt owner).numMotives
  numMinors := (H.rvalAt owner).numMinors
  numIndices := (H.rvalAt owner).numIndices
  k := (H.rvalAt owner).k
  rules := List.zipWith H.modelRule (H.generationSignature.ownedConstructors owner)
    (H.rvalAt owner).rules

/-- The model recursors, in family order. -/
noncomputable def recs (H : RecursorInstallation R outEnv) : List VRecursor :=
  List.ofFn H.modelRecursor

@[simp] theorem rvals_length (H : RecursorInstallation R outEnv) :
    H.rvals.length = H.generationSignature.families.size := by simp [rvals]

@[simp] theorem recs_length (H : RecursorInstallation R outEnv) :
    H.recs.length = H.generationSignature.families.size := by simp [recs]

theorem entry_fst (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    (H.entries[owner.val]'(H.entries_lt owner)).1 = .recInfo (H.rvalAt owner) :=
  (H.generated.entry owner.val (H.entries_lt owner)).source_eq

theorem entry_snd (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    (H.entries[owner.val]'(H.entries_lt owner)).2 = H.generationInstance.recursor owner := by
  rw [H.targets owner.val (H.entries_lt owner)]
  unfold RecursorConstruction.recursorTarget
  rw [dif_pos owner.isLt]

theorem entries_fst (H : RecursorInstallation R outEnv) :
    H.entries.map Prod.fst = H.rvals.map .recInfo := by
  apply List.ext_getElem
  · simp [H.entries_length_eq]
  · intro i h₁ h₂
    have hi : i < H.generationSignature.families.size := by simpa using h₂
    simp only [List.getElem_map, rvals, List.getElem_ofFn]
    exact H.entry_fst ⟨i, hi⟩

theorem entries_snd (H : RecursorInstallation R outEnv) :
    H.entries.map Prod.snd = H.recs.map (·.toVConstVal) := by
  apply List.ext_getElem
  · simp [H.entries_length_eq]
  · intro i h₁ h₂
    have hi : i < H.generationSignature.families.size := by simpa using h₂
    simp only [List.getElem_map, recs, List.getElem_ofFn]
    exact H.entry_snd ⟨i, hi⟩

theorem recs_recursors (H : RecursorInstallation R outEnv) :
    H.recs.map (·.toVConstVal) = H.generationInstance.recursors := by
  simp only [recs, InductiveSignature.Instance.recursors, List.map_ofFn, modelRecursor,
    Function.comp_def]
  simp [List.finRange, List.map_ofFn, Function.comp_def]

theorem rvalAt_metadata (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    InductiveSignature.RecursorMetadata H.generationInstance H.outVEnv owner (H.rvalAt owner) := by
  obtain ⟨rec, h1, -, hm⟩ := H.trMetadata owner
  have : rec = H.rvalAt owner := by
    have h := h1.symm.trans (H.entry_fst owner)
    cases h; rfl
  subst this; exact hm

/-- The rule coverage of the installation, owner by owner. -/
def RulesCoverage (H : RecursorInstallation R outEnv) : Prop :=
  ∀ owner, List.Forall₂ (InductiveSignature.TrRecursorRule H.generationInstance H.outVEnv
      (H.rvalAt owner).levelParams)
    (H.generationSignature.ownedConstructors owner) (H.rvalAt owner).rules

theorem rulesCoverage (H : RecursorInstallation R outEnv) : H.RulesCoverage := by
  intro owner
  have hcov := H.rulesCovered
  obtain ⟨_, hget⟩ := List.forall₂_getElem_exists hcov owner.val (by simp)
  simp only [List.getElem_finRange] at hget
  obtain ⟨rval, h1, h2⟩ := hget
  have : rval = H.rvalAt owner := by
    have h := h1.symm.trans (H.entry_fst owner)
    cases h; rfl
  subst this
  simpa using h2

private theorem forall₂_zipWith {α β γ} {P : α → β → Prop} (f : α → β → γ) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ P as bs →
      List.Forall₂ (fun b c => ∃ a, P a b ∧ c = f a b) bs (List.zipWith f as bs)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons ⟨_, h, rfl⟩ (forall₂_zipWith f t)

/-- The constructor of a signature constructor is a new constructor of the block. -/
theorem ctorOfSignature (H : RecursorInstallation R outEnv)
    (index : Fin H.generationSignature.constructors.size) :
    ∃ iv ∈ R.ivals, ∃ cv ∈ iv.2, cv.name = H.generationSignature.constructors[index].name := by
  have horder := H.generator.constructorOrder
  have hlen := List.Forall₂.length_eq horder
  obtain ⟨hj, -, hname⟩ := List.forall₂_getElem_exists horder index.val
    (by rw [Array.length_toList]; exact index.isLt)
  have hmem : (decl.ownedConstructors[index.val]'hj).2 ∈ decl.constructorConstants := by
    have h := List.getElem_mem hj
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp h
    obtain ⟨cv, hcv, heq⟩ := List.mem_map.mp hc
    rw [← heq]
    exact List.mem_flatMap.mpr ⟨t, ht, hcv⟩
  have hname' : (decl.ownedConstructors[index.val]'hj).2.name ∈
      (R.ivals.flatMap fun iv => iv.2.map ConstantInfo.ctorInfo).map (·.name) := by
    rw [R.ctorInfoNames]; exact List.mem_map_of_mem hmem
  obtain ⟨ci, hci, hcin⟩ := List.mem_map.mp hname'
  obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.mp hci
  obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hci
  refine ⟨iv, hiv, cv, hcv, ?_⟩
  simp only [Array.getElem_toList] at hname
  exact hcin.trans hname.symm

/-- Constants of the constructor environment stay in the output. -/
theorem outFind (H : RecursorInstallation R outEnv) {n : Name} {ci : ConstantInfo}
    (h : ctorEnv.find? n = some ci) : outEnv.constants.find? n = some ci := by
  have hctorWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf
  have hout := H.installed.preservesFind hctorWF (by rw [H.localExtends.env_eq]; exact h)
  rwa [Lean.Kernel.Environment.find?, (H.installed.targetMapWF hctorWF).find?'_eq_find?] at hout

/-- Each kernel recursor translates to its model recursor (PR #43's `TrRecursor`), the type
in the projection stage. -/
theorem trRecursor (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    TrRecursor c.safety R.envP H.outVEnv outEnv.constants (H.rvalAt owner)
      (H.modelRecursor owner) := by
  have E := H.generated.entry owner.val (H.entries_lt owner)
  refine {
    tr := ?_
    all := rfl, numParams := rfl, numMotives := rfl, numMinors := rfl, numIndices := rfl,
    k := rfl
    rules := ?_ }
  · obtain ⟨⟨hs, hl, ht⟩, hn⟩ := (H.generated.entry owner.val (H.entries_lt owner)).translated
    rw [H.entry_snd owner] at hl ht hn
    rw [← R.envP_eq]
    exact ⟨⟨H.localExtends.safety_eq ▸ hs, hl, ht⟩, hn⟩
  · refine List.Forall₂.imp ?_ (forall₂_zipWith H.modelRule (H.rulesCoverage owner))
    rintro rule ru ⟨index, hr, rfl⟩
    obtain ⟨iv, hiv, cv, hcv, hcvname⟩ := H.ctorOfSignature index
    refine ⟨rfl, rfl, ⟨cv, ?_, (R.ctor_numParams iv hiv cv hcv).symm⟩, hr.rhs⟩
    rw [hr.ctor, ← hcvname]
    exact H.outFind (R.ctorInfo_find hiv hcv)

theorem _root_.Lean4Lean.VerifyInductive.RecursorRulesSyntax.length_eq
    {motives minors : Array Expr} {lvls : List Level} :
    ∀ {ctors : List Constructor} {start : Nat} {rules : List RecursorRule},
      RecursorRulesSyntax indTypes stats motives minors lvls ctors start rules →
      rules.length = ctors.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ t => by simp [t.length_eq]

/-- The kernel rule at a local position fires on that constructor, with the kernel's field
count of its type. -/
theorem ruleAt (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) (l : Nat)
    (hl : l < (H.rvalAt owner).rules.length) :
    ∃ hc : l < indTypes[owner.val]!.ctors.length,
      (H.rvalAt owner).rules[l].ctor = indTypes[owner.val]!.ctors[l].name ∧
      (H.rvalAt owner).rules[l].nfields =
        AddInductive.constructorArity indTypes[owner.val]!.ctors[l].type - stats.params.size := by
  have hlen : (H.rvalAt owner).rules.length = indTypes[owner.val]!.ctors.length :=
    (H.generated.entry owner.val (H.entries_lt owner)).rules.length_eq
  have hc : l < indTypes[owner.val]!.ctors.length := by
    rw [← hlen]; exact hl
  refine ⟨hc, ?_⟩
  obtain ⟨info, hinfo, Hrules, -, hrows⟩ :=
    H.ruleTyping.entry owner.val (H.entries_lt owner)
  have hinfoEq : info = H.rvalAt owner := by
    have h := hinfo.symm.trans (H.entry_fst owner)
    cases h; rfl
  subst hinfoEq
  simp only [Nat.zero_add] at hrows
  obtain ⟨Hrule, S, -, -⟩ := hrows l hc hl
  have hctorEq := Hrule.ctor_eq
  simp only [Nat.zero_add] at hctorEq
  refine ⟨hctorEq, ?_⟩
  rw [Hrule.fields_eq]
  have hA := (S.parameterPrefix.constructorArity (R.statsWF.paramFVars)).2
  have hB := S.fieldOpening.telescope.constructorArity
  simp only [Nat.zero_add] at hA
  have hres : AddInductive.constructorArity S.fieldOpening.residual = 0 := by
    apply AddInductive.constructorArity_eq_zero_of_not_forallE
    intro name dom body bi heq
    have h := S.target_not_forall
    rw [← Expr.abstractList_isForall (fvars := S.fieldOpening.fvars), S.fieldOpening.closed,
      heq] at h
    cases h
  omega

/-- `VInductDecl.WF.rules_ctor` for the model recursor of an owner. -/
theorem rulesCtor (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    ∀ ru ∈ (H.modelRecursor owner).rules,
      ∃ ci, R.ctorVEnv.constants ru.ctor = some ci ∧
        ci.type.CtorShape (ru.ctorParams + ru.nfields) := by
  intro ru hru
  simp only [modelRecursor] at hru
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hru
  rw [List.getElem_zipWith]
  simp only [List.length_zipWith] at hl
  have hl' : l < (H.rvalAt owner).rules.length := by omega
  obtain ⟨hc, hctor, hnf⟩ := H.ruleAt owner l hl'
  have hown : owner.val < indTypes.size := H.generator.familyCount ▸ owner.isLt
  have hbang : indTypes[owner.val]! = indTypes[owner.val] := by simp [hown]
  generalize hT : indTypes[owner.val]! = T at hc hctor hnf
  rw [hbang] at hT
  subst hT
  obtain ⟨t, ht, ctor, hctorMem, hname, harity, hparams⟩ := R.modelCtorAt owner.val hown l hc
  refine ⟨ctor.toVConstant, ?_, ?_, ?_⟩
  · simp only [modelRule]
    rw [hctor, ← hname]
    exact VEnv.addConstVals_get R.core.ctorsAdded
      (List.mem_flatMap.mpr ⟨t, ht, hctorMem⟩)
  · simp only [modelRule]
    change ctor.type.piArity = decl.nparams + _
    rw [harity, hnf, hparams]
  · obtain ⟨doms, result, htype, -, -, hhead⟩ := R.formation.rawShapes t ht ctor hctorMem
    refine ⟨t.name, VLevel.params decl.uvars, ?_⟩
    have hr : result = VExpr.mkApps (.const t.name (VLevel.params decl.uvars))
        result.getAppFnArgs.2 := by
      rw [← hhead]; exact (VExpr.mkApps_getAppFnArgs_eq result).symm
    have hfn : result.getAppFn = .const t.name (VLevel.params decl.uvars) := by
      rw [hr]; simp [VExpr.getAppFn]
    have hbody : result.piBody = result := by
      clear hr htype hhead; cases result <;> simp_all [VExpr.piBody, VExpr.getAppFn]
    have hpb : ∀ ds : List VExpr, (VExpr.wrapForalls ds result).piBody = result.piBody := by
      intro ds; induction ds with
      | nil => rfl
      | cons d ds ih => exact ih
    rw [htype, hpb, hbody, hfn]

theorem modelRecursor_type (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    (H.modelRecursor owner).type = H.generationInstance.recursorType owner := rfl

/-- `VInductDecl.WF.rec_shape` for the model recursor of an owner. -/
theorem recShape (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    let r := H.modelRecursor owner
    r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices := by
  have M := H.rvalAt_metadata owner
  simp only [modelRecursor_type]
  simp only [modelRecursor, M.numParams, M.numMotives, M.numMinors, M.numIndices]
  exact H.generationInstance.recursorType_recShape owner

theorem rules_length (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    (H.generationSignature.ownedConstructors owner).length = (H.rvalAt owner).rules.length :=
  List.Forall₂.length_eq (H.rulesCoverage owner)

/-- A model rule of an owner, read off its position. -/
theorem modelRule_at (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) {ru : VRecRule}
    (hru : ru ∈ (H.modelRecursor owner).rules) :
    ∃ index ∈ H.generationSignature.ownedConstructors owner, ∃ rule ∈ (H.rvalAt owner).rules,
      InductiveSignature.TrRecursorRule H.generationInstance H.outVEnv
        (H.rvalAt owner).levelParams index rule ∧ ru = H.modelRule index rule := by
  simp only [modelRecursor] at hru
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hru
  simp only [List.length_zipWith] at hl
  have hl1 : l < (H.generationSignature.ownedConstructors owner).length := by omega
  have hl2 : l < (H.rvalAt owner).rules.length := by omega
  obtain ⟨_, hr⟩ := List.forall₂_getElem_exists (H.rulesCoverage owner) l hl1
  exact ⟨_, List.getElem_mem hl1, _, List.getElem_mem hl2, hr, List.getElem_zipWith ..⟩

/-- `VInductDecl.WF.rules_nodup` for the model recursor of an owner. -/
theorem rulesNodup (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    ((H.modelRecursor owner).rules.map (·.ctor)).Nodup := by
  have hown : owner.val < indTypes.size := H.generator.familyCount ▸ owner.isLt
  have heq : (H.modelRecursor owner).rules.map (·.ctor) =
      indTypes[owner.val].ctors.map (·.name) := by
    apply List.ext_getElem
    · simp only [modelRecursor, List.length_map, List.length_zipWith, H.rules_length]
      have := (H.generated.entry owner.val (H.entries_lt owner)).rules.length_eq
      change (H.rvalAt owner).rules.length = _ at this
      rw [this]; simp [hown]
    · intro l h₁ h₂
      simp only [List.getElem_map, modelRecursor, List.getElem_zipWith, modelRule]
      have hl : l < (H.rvalAt owner).rules.length := by
        simp only [modelRecursor, List.length_map, List.length_zipWith] at h₁; omega
      obtain ⟨hc, hctor, -⟩ := H.ruleAt owner l hl
      rw [hctor]
      simp [hown]
  rw [heq]
  have hnd := R.kernelConstructorNames_nodup
  refine (List.Sublist.map _ ?_).nodup hnd
  rw [List.flatMap_def]
  exact List.sublist_flatten_of_mem
    (List.mem_map_of_mem (List.getElem_mem (l := indTypes.toList) (by simpa using hown)))

/-- Every model rule reduct is closed. -/
theorem rulesClosed (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    ∀ ru ∈ (H.modelRecursor owner).rules, ru.rhs.Closed := by
  intro ru hru
  obtain ⟨index, -, rule, -, hr, rfl⟩ := H.modelRule_at owner hru
  exact TrExprS.closedN_nil H.outVEnvWF.orderedStrong hr.rhs

/-- `VInductDecl.WF.rule_shape` for the model recursor of an owner. -/
theorem ruleShape (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    let r := H.modelRecursor owner
    ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
      r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
      ru.nfields ≤ A.piArity ∧
      ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j := by
  intro r ru hru
  obtain ⟨index, hidx, rule, -, hr, rfl⟩ := H.modelRule_at owner hru
  have M := H.rvalAt_metadata owner
  have hown : H.generationSignature.constructors[index].owner = owner := by
    simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hidx
    exact hidx.2
  obtain ⟨A, hA, hfor, hle, hshape⟩ := H.generationInstance.equation_ruleShape index
  rw [hown] at hA
  refine ⟨index.val, ?_, A, ?_, ?_, ?_, ?_⟩
  · simp only [r, modelRecursor, M.numMinors]; exact index.isLt
  · simp only [r, modelRecursor_type, modelRecursor, M.numParams, M.numMotives]; exact hA
  · simp only [modelRule, hr.ctor]; exact hfor
  · simp only [modelRule, hr.nfields]; exact hle
  · simp only [r, modelRecursor, modelRule, M.numParams, M.numMotives, M.numMinors, hr.nfields]
    exact hshape

/-- `VInductDecl.WF.recs_wf`: the model recursors are typed in the projection stage. -/
theorem recsWF (H : RecursorInstallation R outEnv) :
    ∀ r ∈ H.recs, r.toVConstVal.toVConstant.WF R.envP := by
  intro r hr
  have h := H.generated.recursorsWF H.localWF H.bindings H.params
  rw [H.entries_snd, R.contextVEnv] at h
  exact h _ (List.mem_map_of_mem hr)

open private Lean.Kernel.Environment.add from Lean.Environment in
theorem _root_.Lean4Lean.VerifyInductive.AddConstants.constants_eq
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment} {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    outEnv.constants = insertConsts env.constants (entries.map Prod.fst) := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => rw [ih]; rfl

theorem rvals_mem (H : RecursorInstallation R outEnv) {rval : RecursorVal}
    (h : rval ∈ H.rvals) : ∃ owner, H.rvalAt owner = rval := by
  simpa [rvals, List.mem_ofFn] using h

/-- The output constant map is the constructor environment's with the recursors inserted. -/
theorem mapEq (H : RecursorInstallation R outEnv) :
    outEnv.constants = insertConsts ctorEnv.constants (H.rvals.map .recInfo) := by
  rw [H.installed.constants_eq, H.entries_fst, H.localExtends.env_eq]

theorem quotInitEq (H : RecursorInstallation R outEnv) : outEnv.quotInit = ctorEnv.quotInit := by
  rw [H.installed.quotInit_eq, H.localExtends.env_eq]

theorem freshRvals (H : RecursorInstallation R outEnv) :
    ∀ rval ∈ H.rvals, ctorEnv.find? rval.name = none := by
  intro rval hr
  obtain ⟨owner, rfl⟩ := H.rvals_mem hr
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf
  have hmem : (H.entries[owner.val]'(H.entries_lt owner)) ∈ H.entries := List.getElem_mem _
  have h := H.installed.entryFresh hwf (info := (H.entries[owner.val]'(H.entries_lt owner)).1)
    (value := (H.entries[owner.val]'(H.entries_lt owner)).2) hmem
  rw [H.entry_fst owner, H.localExtends.env_eq] at h
  exact h

theorem kLike (H : RecursorInstallation R outEnv) :
    ∀ rval ∈ H.rvals, KLikeRecursor outEnv.constants H.outVEnv rval := by
  intro rval hr
  obtain ⟨owner, rfl⟩ := H.rvals_mem hr
  exact H.kOfMetadata H.generator.models H.generationInstance (H.rvalAt_metadata owner)

/-- The output's inductive headers are the source's or the declaration's. -/
theorem inductInfos (H : RecursorInstallation R outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants decl := by
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf
  have houtWF := H.installed.targetMapWF hwf
  have hpres : ∀ {name ci}, ctorEnv.constants.find? name = some ci →
      outEnv.constants.find? name = some ci := by
    intro name ci h
    apply H.outFind
    rwa [Lean.Kernel.Environment.find?, R.context.checking.tr.map_wf.find?'_eq_find?]
  intro familyName familyInfo hfind
  have hfind' : outEnv.find? familyName = some (.inductInfo familyInfo) := by
    rwa [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
  rcases H.installed.origin hwf hfind' with hold | ⟨entry, hentry, -, hfound⟩
  · rw [H.localExtends.env_eq, Lean.Kernel.Environment.find?,
      R.context.checking.tr.map_wf.find?'_eq_find?] at hold
    rcases R.inductInfosFromDecl familyName familyInfo hold with hsrc | ⟨idx, hname, ⟨A⟩⟩
    · exact .inl hsrc
    · exact .inr ⟨idx, hname, ⟨A.rebase (hname ▸ hfind) hpres⟩⟩
  · exact absurd hfound.symm (H.generated.nonInductive entry.1 entry.2 hentry familyInfo)

theorem ctorParamAlignment (H : RecursorInstallation R outEnv) {safety : DefinitionSafety}
    (Hsource : ConstructorParameterAlignment safety c.env sourceEnv) :
    ConstructorParameterAlignment safety outEnv H.outVEnv := by
  have hwf : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf
  have h := (R.constructorParameterAlignment Hsource).mono R.ctorLE
  have he : H.localContext.env = ctorEnv := H.localExtends.env_eq
  have h' : ∀ V, ConstructorParameterAlignment safety ctorEnv V →
      ConstructorParameterAlignment safety H.localContext.env V := fun _ h => by rw [he]; exact h
  exact H.installed.preservesConstructorTyping hwf (h' _ h)
    (fun info value hmem v => H.generated.nonInductive info value hmem v)

end RecursorInstallation

end VerifyInductive
end Lean4Lean
