import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.SignatureVars
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean

theorem VEnv.addConsts_eliminators {env env' : VEnv} :
    ∀ {cis}, env.addConsts cis = some env' → env'.eliminators = env.eliminators
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hfirst, hrest⟩ := h
    exact (VEnv.addConsts_eliminators hrest).trans (VEnv.addConst_eliminators hfirst)

@[simp] theorem VEnv.addDefEqs_eliminators (env : VEnv) (cis : List VDefVal) :
    (env.addDefEqs cis).eliminators = env.eliminators := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem VEnv.addEliminators_eliminators_congr {env₁ env₂ : VEnv} {es}
    (h : env₁.eliminators = env₂.eliminators) :
    (env₁.addEliminators es).eliminators = (env₂.addEliminators es).eliminators := by
  funext n s
  apply propext
  rw [VEnv.addEliminators_iff, VEnv.addEliminators_iff, h]

/-- An installed block registers exactly its case eliminators. -/
theorem VInductBlock.install_eliminators {env env' : VEnv}
    (H : VInductBlock.install env block = some env') :
    env'.eliminators = (env.addEliminators block.eliminators).eliminators := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := H
  rw [VEnv.addDefEqRules_eliminators, VEnv.addConstVals_eliminators hr,
    VEnv.addProjections_eliminators]
  exact VEnv.addEliminators_eliminators_congr
    ((VEnv.addConstVals_eliminators hc).trans (VEnv.addConstVals_eliminators ht))

theorem VInductBlock.install_eliminators_iff {env env' : VEnv}
    (H : VInductBlock.install env block = some env') :
    env'.eliminators n s ↔ (n, s) ∈ block.eliminators ∨ env.eliminators n s := by
  rw [VInductBlock.install_eliminators H, VEnv.addEliminators_iff]

/-- The case eliminator registered by one checked inductive declaration, with the data of its
registration at the constructor stage. -/
def VEnv.InductRegistration (env : VEnv) (decl : VInductDecl) (key : Name)
    (schema : InductiveSignature.CaseSchema) (env' : VEnv) : Prop :=
  ∃ (block : VInductBlock) (envTypes envCtors : VEnv),
    decl.WF env ∧ VInductDecl.CompilesTo env decl block ∧ block.WF env ∧
    VInductBlock.install env block = some env' ∧
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    block.eliminators = [(key, schema)] ∧ schema.RegistrationCertificate env decl block key ∧
    schema.ProjNamesRegistered envCtors key

theorem VEnv.AddInduct.eliminators_iff (H : VEnv.AddInduct env decl env') :
    env'.eliminators n s ↔ VEnv.InductRegistration env decl n s env' ∨ env.eliminators n s := by
  cases H with
  | intro hdecl hcompile hblock helim hinstall =>
    obtain ⟨envTypes, envCtors, ht, hc, helim⟩ := helim
    rcases helim with ⟨-, hE⟩ | ⟨key, schema, hE, hreg, hprojs⟩
    · rw [VInductBlock.install_eliminators_iff hinstall, hE]
      constructor
      · rintro (h | h)
        · simp at h
        · exact .inr h
      · rintro (⟨block', envTypes', envCtors', -, -, -, hinstall', -, -, hE', -⟩ | h)
        · have := VInductBlock.install_eliminators_iff (n := n) (s := s) hinstall'
          rw [hE'] at this
          have h2 := VInductBlock.install_eliminators_iff (n := n) (s := s) hinstall
          rw [hE] at h2
          exact .inr (by simpa using h2.mp (this.mpr (by simp)))
        · exact .inr h
    rw [VInductBlock.install_eliminators_iff hinstall, hE]
    simp only [List.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | h)
      · exact .inl ⟨_, envTypes, envCtors, hdecl, hcompile, hblock, hinstall, ht, hc, hE, hreg,
          hprojs⟩
      · exact .inr h
    · rintro (⟨block', envTypes', envCtors', -, -, -, hinstall', ht', hc', hE', -⟩ | h)
      · have := VInductBlock.install_eliminators_iff (n := n) (s := s) hinstall'
        rw [hE'] at this
        have h2 := VInductBlock.install_eliminators_iff (n := n) (s := s) hinstall
        rw [hE] at h2
        simpa using h2.mp (this.mpr (by simp))
      · exact .inr h

theorem VEnv.addConsts_projections {env env' : VEnv} :
    ∀ {cis}, env.addConsts cis = some env' → env'.projections = env.projections
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hfirst, hrest⟩ := h
    exact (VEnv.addConsts_projections hrest).trans (VEnv.addConst_projections hfirst)

@[simp] theorem VEnv.addDefEqs_projections (env : VEnv) (cis : List VDefVal) :
    (env.addDefEqs cis).projections = env.projections := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem VEnv.addQuot_projections {env env' : VEnv}
    (H : env.addQuot = some env') : env'.projections = env.projections := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at H
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := H
  exact (VEnv.addConst_projections hd).trans <|
    (VEnv.addConst_projections hc).trans <|
      (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)

theorem VEnv.addQuot_eliminators {env env' : VEnv}
    (H : env.addQuot = some env') : env'.eliminators = env.eliminators := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at H
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := H
  exact (VEnv.addConst_eliminators hd).trans <|
    (VEnv.addConst_eliminators hc).trans <|
      (VEnv.addConst_eliminators hb).trans (VEnv.addConst_eliminators ha)

/-- A declaration step registers a case eliminator only for an inductive declaration, and then
exactly its certified one. -/
theorem VDecl.WF.eliminators_iff (H : VDecl.WF env decl env') :
    env'.eliminators n s ↔
      (∃ source, decl = .induct source ∧ VEnv.InductRegistration env source n s env') ∨
        env.eliminators n s := by
  cases H with
  | «axiom» _ h | «opaque» _ h => simp [VEnv.addConst_eliminators h]
  | «def» _ h => simp [(VEnv.addConst_eliminators h : _ = env.eliminators)]
  | «example» => simp
  | mutualDef _ h _ =>
    rw [VEnv.addDefEqs_eliminators, VEnv.addConsts_eliminators h]
    simp
  | quot _ h => simp [VEnv.addQuot_eliminators h]
  | induct h =>
    rw [h.eliminators_iff]
    simp

/-- The stages of an installed block. -/
theorem VInductBlock.install_stages {env env' : VEnv}
    (H : VInductBlock.install env block = some env') :
    ∃ envTypes envCtors envRecursors, env.addConstVals block.types = some envTypes ∧
      envTypes.addConstVals block.ctors = some envCtors ∧
      ((envCtors.addEliminators block.eliminators).addProjections block.projections).addConstVals
        block.recursors = some envRecursors ∧
      env' = envRecursors.addDefEqRules block.rules := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := H
  exact ⟨types, ctors, recs, ht, hc, hr, rfl⟩

theorem VInductBlock.install_base_le {env env' : VEnv}
    (H : VInductBlock.install env block = some env') : env ≤ env' := by
  obtain ⟨_, _, _, ht, hc, hr, rfl⟩ := VInductBlock.install_stages H
  exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
    VEnv.addEliminators_addProjections_le.trans <| (VEnv.addConstVals_le hr).trans
      VEnv.addDefEqRules_le

/-- The constructor stage of an installed block is below the installed environment. -/
theorem VInductBlock.install_ctors_le {env env' envTypes envCtors : VEnv}
    (H : VInductBlock.install env block = some env')
    (ht : env.addConstVals block.types = some envTypes)
    (hc : envTypes.addConstVals block.ctors = some envCtors) : envCtors ≤ env' := by
  obtain ⟨_, _, _, ht', hc', hr, rfl⟩ := VInductBlock.install_stages H
  cases ht.symm.trans ht'
  cases hc.symm.trans hc'
  exact VEnv.addEliminators_addProjections_le.trans <| (VEnv.addConstVals_le hr).trans
      VEnv.addDefEqRules_le

theorem VEnv.addConsts_le {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' → env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConsts_le h2)

theorem VEnv.addConst_eq_none {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

theorem VEnv.addConst_constants_eq {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

/-- A block of constants can be added as long as each name is fresh and the block has no
duplicates; the latter is what `addMutual`'s `found` set checks. -/
theorem VEnv.exists_addConsts {env : VEnv} : ∀ {cis : List VDefVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConsts cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConsts (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConsts, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VEnv.addConsts_congr {env : VEnv} : ∀ {cis cis' : List VDefVal},
    List.Forall₂ (fun a b => a.toVConstVal = b.toVConstVal) cis cis' →
    env.addConsts cis = env.addConsts cis'
  | [], [], _ => rfl
  | a :: _, b :: _, .cons h t => by
    have h1 : a.name = b.name := congrArg VConstVal.name h
    have h2 : a.toVConstant = b.toVConstant := congrArg VConstVal.toVConstant h
    show (env.addConst a.name a.toVConstant).bind _ = (env.addConst b.name b.toVConstant).bind _
    rw [h1, h2]
    cases env.addConst b.name b.toVConstant
    · rfl
    · exact VEnv.addConsts_congr t

theorem VEnv.addConsts_ordered {env env' : VEnv} : ∀ {cis}, Ordered env →
    (∀ ci ∈ cis, ci.toVConstant.WF env) → env.addConsts cis = some env' → Ordered env'
  | [], h, _, e => by cases e; exact h
  | _ :: _, h, hw, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine VEnv.addConsts_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (VEnv.addConst_le h1)

theorem VEnv.addConsts_constants {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' →
    ∀ ci ∈ cis, env'.constants ci.name = some ci.toVConstant
  | [], _, _, hc => nomatch hc
  | _ :: _, e, c, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact (VEnv.addConsts_le h2).constants (VEnv.addConst_self h1)
    | tail _ hc => exact VEnv.addConsts_constants h2 c hc

theorem VEnv.addDefEqs_ordered : ∀ {env : VEnv} {cis}, Ordered env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) →
    (∀ ci ∈ cis, ci.WF env) → Ordered (env.addDefEqs cis)
  | _, [], h, _, _ => h
  | env, ci :: cis, h, hmem, hw => by
    have hci : ci.WF env := hw _ (.head _)
    have hord : Ordered (env.addDefEq ci.toDefEq) := by
      refine .defeq h ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    show Ordered ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine VEnv.addDefEqs_ordered hord (fun c hc => ?_) (fun c hc => ?_)
    · exact (VEnv.addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc))
    · exact (hw c (.tail _ hc)).mono VEnv.addDefEq_le

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H with
    | empty => exact .empty
    | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih => exact .eliminator ih
    | decl h _ ih =>
      cases h with
      | «axiom» h1 h2 => exact .const ih h1 h2
      | @«def» env env' ci h1 h2 =>
        refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
        · simp [VDefVal.toDefEq]
          rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
          exact .const (addConst_self h2) VLevel.id_WF (by simp)
        · exact h1.mono (addConst_le h2)
      | mutualDef h0 h1 h2 =>
        exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h0 h1)
          (VEnv.addConsts_constants h1) h2
      | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
      | «example» _ => exact ih
      | quot h1 h2 => exact addQuot_WF ih h1 h2
      | induct h2 => exact addInduct_WF ih h2.sourceWF h2
    | inductProjections _ _ _ hsource htypesWF hconstructorUvars hctorsWF hparams hshape htypesSource
        hctorsSource hprojections htypes hctors ihBase _ =>
      have hT := ihBase.addConstVals (by
        intro ci hci
        rw [htypesSource] at hci
        obtain ⟨type, htype, rfl⟩ := List.mem_map.mp hci
        exact htypesWF type htype) htypes
      have hC := hT.addConstVals (by
        intro ci hci
        rw [hctorsSource] at hci
        exact hctorsWF ci hci) hctors
      exact .inductProjections ihBase hC hsource htypesWF hconstructorUvars hctorsWF hparams
        hshape htypesSource hctorsSource hprojections htypes hctors

/-- A dependency-ordered list of well-formed constants may be viewed as a
sequence of abstract axioms extending a well-formed environment.  Stating
the input typing in the starting environment is sufficient because each
constant can be weakened through the preceding fresh additions. -/
theorem VEnv.WF.addConstVals
    {env env' : VEnv} {cis : List VConstVal}
    (Henv : env.WF)
    (Hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (Hadd : env.addConstVals cis = some env') : env'.WF := by
  induction cis generalizing env env' with
  | nil =>
    simp [VEnv.addConstVals] at Hadd
    subst env'
    exact Henv
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hci] at Hadd
    | some next =>
      simp [VEnv.addConstVals, hci] at Hadd
      have hhead : ci.toVConstant.WF env := Hwf ci (by simp)
      have Hnext : next.WF := by
        rcases Henv with ⟨ds, Hds⟩
        exact ⟨.axiom ci :: ds, .decl (.axiom hhead hci) Hds⟩
      apply ih Hnext (env' := env')
      · intro ci' hmem
        exact (Hwf ci' (by simp [hmem])).mono (VEnv.addConst_le hci)
      · exact Hadd

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩

end Lean4Lean

/-! Formation of every constant header in an earlier environment.

A constant's closed type was checked before its own fresh installation. This
also covers the family and constructor prefixes within one inductive declaration,
where the length of the declaration list is not a decreasing measure. The finite
constant domain gives a strict measure at every such header edge.
-/
namespace Lean4Lean.VEnv
variable {env : VEnv}

namespace ConstantDomain

variable {env extended : VEnv}

end ConstantDomain

namespace ConstantHeaderOrigin
variable {env extended : VEnv} {name : Name} {value : VConstant}

end ConstantHeaderOrigin

/-- No lookup can appear except from the old environment or a literal
member of the installed block. -/
theorem addConstVals_lookup_cases {base extended : VEnv}
    (installed : base.addConstVals values = some extended)
    (lookup : extended.constants name = some value) :
    base.constants name = some value ∨
      ∃ entry ∈ values, entry.name = name ∧ entry.toVConstant = value := by
  induction values generalizing base with
  | nil => cases installed; exact Or.inl lookup
  | cons entry entries ih =>
    simp only [addConstVals, Option.bind_eq_bind, Option.bind_eq_some_iff] at installed
    obtain ⟨middle, first, rest⟩ := installed
    rcases ih rest with old | added
    · rw [VEnv.addConst_constants_eq first] at old
      dsimp only at old
      by_cases same : entry.name = name
      · simp only [same, ite_true, Option.some.injEq] at old
        exact Or.inr ⟨entry, List.mem_cons_self, same, old⟩
      · exact Or.inl (by simpa only [same, ite_false] using old)
    · obtain ⟨selected, member, sameName, sameValue⟩ := added
      exact Or.inr ⟨selected, List.mem_cons_of_mem _ member, sameName, sameValue⟩

end Lean4Lean.VEnv

namespace Lean4Lean.VerifyInductive

theorem VEnv.addConstVals_projections_eq
    {base out : VEnv} {constants : List VConstVal}
    (H : base.addConstVals constants = some out) :
    out.projections = base.projections := by
  induction constants generalizing base with
  | nil =>
      simp [VEnv.addConstVals] at H
      subst out
      rfl
  | cons ci constants ih =>
      simp only [VEnv.addConstVals] at H
      cases hadd : base.addConst ci.name ci.toVConstant with
      | none => simp [hadd] at H
      | some next =>
          rw [hadd] at H
          rw [ih H]
          unfold VEnv.addConst at hadd
          split at hadd <;> cases hadd
          rfl

end Lean4Lean.VerifyInductive
