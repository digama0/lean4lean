import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.Typing.SingletonExtraction.TelescopeTyping
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.CaseReduction

/-! # Singleton extraction data of a recursor

The cast specification and the elimination into `Prop` of a registered recursor
of a large-eliminating inductive proposition, at an occurrence's universes. Pure
definitions; their scoping is in `RecursorScope.lean` (`propElim_closed`) and their
universe congruence in `RecursorLevels.lean` (`propElim_levels`). -/

namespace Lean4Lean
open VExpr InductiveSignature VEnv

namespace InductiveSignature.RecursorData

/-- Universe instantiation of a cast specification. -/
def _root_.Lean4Lean.SingletonLayout.instL (S : SingletonLayout) (ls : List VLevel) : SingletonLayout where
  fields := S.fields.map (·.instL ls)
  indices := S.indices.map (·.instL ls)
  slot := S.slot
  sorts := S.sorts.map (·.inst ls)

/-- The free elimination universe parameter. -/
def targetParam (data : RecursorData) : Option Nat :=
  match data.target with
  | .param k => some k
  | _ => none

/-- The owner's unique constructor. -/
def singletonCtor (data : RecursorData) : Option (Fin data.schema.signature.constructors.size) :=
  match (List.finRange data.schema.signature.constructors.size).filter
      (fun i => data.schema.signature.constructors[i].owner == data.owner) with
  | [i] => some i
  | _ => none

/-- The sorts of the data fields, chosen at the generic universes. Proof fields get `Prop`. -/
noncomputable def genericSorts (env : VEnv) (data : RecursorData)
    (c : Constructor data.schema.signature.families.size) : List VLevel :=
  (List.range (data.recursorInstance.fieldsAt c).length).map fun i =>
    match fieldSlot (data.recursorInstance.ctorIndicesAt c) (data.recursorInstance.fieldsAt c).length i with
    | some _ => Classical.epsilon fun u =>
      env.HasType data.uvars
        (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take i).reverse
        ((data.recursorInstance.fieldsAt c).getD i default) (.sort u)
    | none => .zero

/-- The cast specification at the generic universes. -/
noncomputable def singletonLayoutGeneric (env : VEnv) (data : RecursorData) : Option SingletonLayout := do
  let i ← data.singletonCtor
  let c := data.schema.signature.constructors[i]
  return data.recursorInstance.singletonCast data.owner c (data.genericSorts env c)

/-- The cast specification at an occurrence's universes: the generic one, instantiated. -/
noncomputable def singletonLayout (env : VEnv) (data : RecursorData) (packed : List VLevel) :
    Option SingletonLayout :=
  (data.singletonLayoutGeneric env).map (·.instL packed)

/-- The parameter telescope at an occurrence's universes. -/
def propParams (data : RecursorData) (packed : List VLevel) : List VExpr :=
  data.recursorInstance.params.map (·.instL packed)

/-- Elimination into `Prop` through the recursor itself, at an occurrence's universes
with the free elimination universe set to zero. -/
def propElim (data : RecursorData) (packed : List VLevel) : Option PropElim := do
  let k ← data.targetParam
  let i ← data.singletonCtor
  return (data.recursorInstance.specialize 0 (packed.set k .zero)).singletonElim data.owner
    data.schema.signature.constructors[i] (.const data.name (packed.set k .zero))

end InductiveSignature.RecursorData
end Lean4Lean

/-! # Facts about a registered large-eliminating proposition

A registered recursor whose target universe can be large and whose source sort is
`Prop` at an occurrence comes from a singleton signature with identity restoration and a
free elimination universe (`Instance.FreeTarget`). -/

namespace Lean4Lean
open VExpr InductiveSignature VEnv

namespace InductiveSignature.RecursorData
variable {env : VEnv}

/-- What a registered large-eliminating proposition provides: a singleton
signature, identity restoration, free elimination universe, and the installed
recursor typed by the generator. -/
structure SingletonSignature (env : VEnv) (data : RecursorData) : Prop where
  families : data.schema.signature.families.size = 1
  constructors : data.schema.signature.constructors.size ≤ 1
  restoration : data.schema.restoration = {}
  free : ∃ k, data.target = .param k ∧ k < data.uvars ∧
    ∀ l ∈ data.levels, ∀ (ls : List VLevel) (u : VLevel), l.inst (ls.set k u) = l.inst ls
  levels_wf : ∀ l ∈ data.levels, l.WF data.uvars
  recursor : env.constants data.name =
    some { uvars := data.uvars, type := data.recursorInstance.recursorType data.owner }
  singleton : ∃ envTypes, envTypes ≤ env ∧
    data.schema.signature.SingletonElimination envTypes data.uvars data.levels
  arity : ∀ ctor ∈ data.schema.signature.constructors.toList,
    ctor.indices.length = data.schema.signature.families[ctor.owner].indices.length
  uvars : data.levels.length = data.schema.signature.uvars

theorem singletonSignature (H : RecursorRegistered env data) (hlarge : data.largeTarget = true)
    (hzero : data.sourceLevel packed ≈ .zero) : SingletonSignature env data := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, hbase, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinstance : data.recursorInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [RecursorData.recursorInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  obtain ⟨envTypes, htypes0, hadm⟩ := hdata.admissible
  have hsingle : data.schema.signature.SingletonElimination envTypes g.uvars g.levels ∧
      g.FreeTarget := by
    rcases hadm.elimination with hnz | hz | hs
    · exfalso
      have hfam := hnz _ (Array.getElem_mem_toList (i := data.owner.val) data.owner.isLt)
      unfold sourceLevel CaseSchema.sourceLevel at hzero
      rw [← hl] at hfam
      have h1 := (hfam.inst (ls := packed)) []
      have h2 := congrFun hzero []
      exact h1 (by simpa [VLevel.eval] using h2)
    · exfalso
      unfold largeTarget at hlarge
      rw [ht] at hlarge
      have := congrFun hz (List.replicate data.uvars 1)
      simp [VLevel.eval] at this
      simp [this] at hlarge
    · exact hs
  have hfam := hsingle.1.1
  have hrest : data.schema.restoration = {} := hr.trans (hdata.restoration_of_singleton hfam)
  -- the installed environment contains the checked headers
  have hinst := hi
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hinst
  obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := hinst
  have hle1 : e1 ≤ env := (VEnv.addConstVals_le he2).trans
    (VEnv.addEliminators_addProjections_le.trans ((VEnv.addConstVals_le he3).trans
      (VEnv.addDefEqRules_le.trans he)))
  have hbaseLE : base ≤ env := hbase.trans ((VEnv.addConstVals_le he1).trans hle1)
  have htypesLE : envTypes ≤ env := by
    have he1' := he1
    rw [hdata.types, hdata.typeConstants_of_singleton hfam] at he1'
    exact (VEnv.addConstVals_mono hbase htypes0 he1').trans hle1
  refine {
    families := hfam
    constructors := hsingle.1.2.1
    restoration := hrest
    free := ?_
    levels_wf := by rw [hl, hu]; exact hadm.levels_wf
    recursor := ?_
    singleton := ?_
    arity := hdata.model.constructorArity
    uvars := ?_ }
  · obtain ⟨k, hk, hlv⟩ := hsingle.2
    have hwf := hadm.target_wf
    rw [hk] at hwf
    exact ⟨k, ht.trans hk, by rw [hu]; simpa [VLevel.WF] using hwf, by rw [hl]; exact hlv⟩
  · have hgen : data.recursorType = some (data.recursorInstance.recursorType data.owner) := by
      simp [recursorType, hrest]
    exact RecursorRegistered.recursorType
      ⟨base, installBase, source, expanded, g, auxiliaries, block, _, hdata, ‹_›, hbase, hr, ‹_›,
        hu, hl, ht, hi, he⟩ hgen
  · exact ⟨envTypes, htypesLE, by rw [hu, hl]; exact hsingle.1⟩
  · rw [hl]; exact hadm.levels_length

end InductiveSignature.RecursorData
end Lean4Lean

/-! Scope and term-renaming facts for the actual singleton reconstruction.
These facts retain its selected index and proof-field extractions. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr

/-- Closed declaration syntax commutes with renaming the simultaneous
occurrence arguments. It cannot retain any unrenamed free variable. -/
theorem instantiateParams_lift' {body : VExpr} {args : List VExpr}
    (hbody : body.ClosedN args.length) :
    (instantiateParams body args).lift' ρ =
      instantiateParams body (args.map (·.lift' ρ)) := by
  let σ : VExpr.Subst := fun i =>
    if hi : i < args.length then args[args.length - 1 - i] else .bvar (i - args.length)
  change (body.subst σ).lift' ρ = _
  rw [VExpr.lift'_subst]
  unfold instantiateParams
  dsimp only [σ]
  apply VExpr.subst_congr_closedN hbody
  intro i hi
  simp only [VExpr.Subst.lift_r, List.length_map, dif_pos hi, List.getElem_map]

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr CaseSchema
variable {levels : List VLevel}

end Lean4Lean.InductiveSignature.RecursorData
