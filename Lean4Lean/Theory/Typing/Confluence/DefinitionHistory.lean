import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.QuotPrefixTyping
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.VExpr
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.RecursorEquationCoverage
import Lean4Lean.Std.List
import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.ProjectionRigidity

namespace Lean4Lean
open Lean4Lean
namespace VEnv
open VExpr
variable [Params]
open Params
theorem PatternReductionTrace.parRedS
    (H : PatternReductionTrace env univs Pat Γ e e') : ParRedS Γ e e' := by
  induction H with
  | refl => exact .rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | pattern hp hm hc => exact .tail .rfl (.extra hp hm hc fun _ => .rfl)
  | schema hs => exact .tail .rfl (ParRed.of_schema hs)
  | beta => exact .tail .rfl (.beta .rfl .rfl)
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | lam _ ih => exact .lam .rfl ih
end VEnv
end Lean4Lean

namespace Lean4Lean.VEnv
variable {env extended : VEnv} {value : VDefVal}
theorem DefinitionRegistered.mono (H : DefinitionRegistered env value) (hle : env ≤ env') :
    DefinitionRegistered env' value := ⟨hle.constants H.1, hle.defeqs H.2⟩
theorem DefinitionRegistered.closed (henv : env.WF)
    (H : DefinitionRegistered env value) : value.value.Closed := by
  have hw := (henv.ordered.defEqWF H.2).2
  exact VExpr.WF.closedN henv.ordered ⟨_, hw⟩ (by trivial)
namespace DefinitionPattern
variable {registry : Name → Option VDefVal}
theorem simple (H : DefinitionPattern registry p rhs) :
    ∃ shape : SimplePattern, p = shape.toPattern := by
  cases H with | intro _ _ => exact ⟨.defn _, rfl⟩
theorem origin
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionPattern registry p rhs) : PatternHeadsStoredRule env p := by
  cases H with
  | @intro value hl hc =>
    exact ⟨value.toDefEq, value.name, VLevel.params value.uvars,
      (hregistry _ _ hl).2, rfl, rfl⟩
theorem not_iota (H : DefinitionPattern registry
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) : False := by
  cases H
theorem unique (H : DefinitionPattern registry p rhs)
    (H' : DefinitionPattern registry q rhs') (hs : Subpattern sub p)
    (hi : q.inter sub = some intersection) : p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  cases H with
  | @intro value hl hc =>
    cases H' with
    | @intro value' hl' hc' =>
      cases hs
      simp only [Pattern.inter] at hi
      split at hi <;> try contradiction
      rename_i hname
      have hn : value'.name = value.name := by simpa using hname
      rw [hn] at hl'
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl, HEq.rfl⟩
theorem no_app_subpattern (H : DefinitionPattern registry p rhs)
    (hs : Subpattern (.app fn arg) p) : False := by
  cases H
  cases hs
/-- Soundness uses the installed equation at the occurrence's actual
universe list, recovered from its typing and constant lookup. -/
theorem sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionPattern registry p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) := by
  cases H with
  | @intro value hl hc =>
    cases hm
    obtain ⟨constant, hconstant, hlevels, hlength⟩ := ht.const_inv henv.ordered hΓ
    have hregistered := hregistry _ _ hl
    cases Option.some.inj (hconstant.symm.trans hregistered.1)
    have he := IsDefEq.extra (Γ := Γ) hregistered.2 hlevels hlength
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlength,
      Pattern.RHS.apply] using (show env.IsDefEqU U Γ _ _ from ⟨_, he⟩)
/-- Every actual definition equation has a concrete one-step pattern trace;
there are no captured terms or additional equality guards. -/
theorem equation_trace (hlookup : registry value.name = some value)
    (hclosed : value.value.Closed) (hlength : levels.length = value.uvars) :
    PatternReductionTrace env U (DefinitionPattern registry) Γ
      (value.toDefEq.lhs.instL levels) (value.toDefEq.rhs.instL levels) := by
  simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlength]
  exact .pattern (DefinitionPattern.intro hlookup hclosed) .const trivial
end DefinitionPattern
end Lean4Lean.VEnv

namespace Lean4Lean.VEnv
variable {env extended : VEnv} {values : List VDefVal} {value : VDefVal}
theorem DefinitionRegistered.of_addConsts
    (hadd : env.addConsts values = some extended) (hvalue : value ∈ values) :
    DefinitionRegistered (extended.addDefEqs values) value := by
  rw [VEnv.addDefEqs_eq_addDefEqRules]
  exact ⟨by simpa only [VEnv.addDefEqRules_constants] using
      VEnv.addConsts_constants hadd value hvalue,
    VEnv.addDefEqRules_mem (List.mem_map.mpr ⟨value, hvalue, rfl⟩)⟩
private theorem definition_names_nodup
    (hadd : env.addConsts values = some extended) : (values.map (·.name)).Nodup := by
  induction values generalizing env with
  | nil => trivial
  | cons value values ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hadd
    obtain ⟨middle, hfirst, hrest⟩ := hadd
    have hrest : middle.addConsts values = some extended := hrest
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hrest⟩
    intro hm
    obtain ⟨other, hm, hn⟩ := List.mem_map.mp hm
    have hf := VEnv.addConstVals_names_fresh (VEnv.addConsts_eq_addConstVals ▸ hrest)
      other.toVConstVal (List.mem_map.mpr ⟨other, hm, rfl⟩)
    have hs := VEnv.addConst_self hfirst
    change middle.constants other.name = none at hf
    rw [hn, hs] at hf
    contradiction
private theorem definition_find (hnd : (values.map (·.name)).Nodup)
    (hmem : value ∈ values) :
    values.find? (fun other => other.name == value.name) = some value := by
  induction values with
  | nil => cases hmem
  | cons first tail ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem
    · simp
    · have hn : first.name ≠ value.name := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨value, hmem, he.symm⟩)
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hn]
      exact ih hnd.2 hmem
/-- Successful declaration installation gives every definition its own
lookup entry, including mutually recursive definitions. -/
theorem installDefinitions_lookup
    (hadd : env.addConsts values = some extended) (hvalue : value ∈ values) :
    installDefinitions old values value.name = some value := by
  unfold installDefinitions
  rw [definition_find (definition_names_nodup hadd) hvalue]
  rfl
/-- New definitions cannot shadow an earlier registered definition. -/
theorem installDefinitions_preserves
    (hadd : env.addConsts values = some extended)
    (hregistered : DefinitionRegistered env previous) (hold : old previous.name = some previous) :
    installDefinitions old values previous.name = some previous := by
  unfold installDefinitions
  cases hf : values.find? (fun value => value.name == previous.name) with
  | none => exact hold
  | some fresh =>
    have hn : fresh.name = previous.name := by simpa using List.find?_some hf
    have hnone := VEnv.addConstVals_names_fresh (VEnv.addConsts_eq_addConstVals ▸ hadd)
      fresh.toVConstVal (List.mem_map.mpr ⟨fresh, List.mem_of_find?_eq_some hf, rfl⟩)
    change env.constants fresh.name = none at hnone
    rw [hn, hregistered.1] at hnone
    contradiction
/-- The new table contains only actual installed values and defining
equations; the earlier table is transported through this concrete extension. -/
theorem installDefinitions_registered
    (hadd : env.addConsts values = some extended)
    (hold : ∀ name value, old name = some value → DefinitionRegistered env value ∧ value.name = name)
    (hlookup : installDefinitions old values name = some value) :
    DefinitionRegistered (extended.addDefEqs values) value ∧ value.name = name := by
  unfold installDefinitions at hlookup
  cases hf : values.find? (fun value => value.name == name) with
  | none =>
    have hlookup : old name = some value := by simpa [hf] using hlookup
    have hle : env ≤ extended.addDefEqs values := by
      rw [VEnv.addDefEqs_eq_addDefEqRules]
      exact (VEnv.addConsts_le hadd).trans VEnv.addDefEqRules_le
    exact ⟨(hold _ _ hlookup).1.mono hle, (hold _ _ hlookup).2⟩
  | some found =>
    simp only [hf, Option.orElse_some, Option.some.injEq] at hlookup
    subst found
    exact ⟨.of_addConsts hadd (List.mem_of_find?_eq_some hf), by simpa using List.find?_some hf⟩
end Lean4Lean.VEnv

/-! The actual environment declaration history determines its ordinary
definition pattern table, including mutually recursive definitions. -/

namespace Lean4Lean

/-- Only transparent definitions contribute prefix unfolding equations. -/
def VDecl.definitionEntries : VDecl → List VDefVal
  | .def value => [value]
  | .mutualDef values => values
  | _ => []

/-- Declaration histories store their newest declaration first. -/
def VEnv.definitionRegistry : List VDecl → Name → Option VDefVal
  | [] => fun _ => none
  | declaration :: declarations =>
    VEnv.installDefinitions (VEnv.definitionRegistry declarations) declaration.definitionEntries

namespace VEnv
variable {env : VEnv}

private theorem declaration_le (H : VDecl.WF env declaration extended) : env ≤ extended := by
  cases H with
  | «axiom» _ ha | «opaque» _ ha => exact VEnv.addConst_le ha
  | «def» _ ha => exact (VEnv.addConst_le ha).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ ha _ =>
    rw [VEnv.addDefEqs_eq_addDefEqRules]
    exact (VEnv.addConsts_le ha).trans VEnv.addDefEqRules_le
  | quot _ ha =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ha
    exact ((((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)).trans
      (VEnv.addConst_le hc)).trans (VEnv.addConst_le hd)).trans VEnv.addDefEq_le
  | induct ha =>
    cases ha with
    | intro _ _ _ _ hi =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hi
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hi
      exact (((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
        (VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le hr))).trans VEnv.addDefEqRules_le

private theorem definitionRegistry_decl
    (H : VDecl.WF env declaration extended)
    (hold : ∀ name value, old name = some value → DefinitionRegistered env value ∧ value.name = name)
    (hlookup : installDefinitions old declaration.definitionEntries name = some value) :
    DefinitionRegistered extended value ∧ value.name = name := by
  have hm := declaration_le H
  cases H with
  | «def» hw ha =>
    rename_i next ci
    have ha' : env.addConsts [ci] = some next := by simpa [VEnv.addConsts] using ha
    exact installDefinitions_registered ha' hold hlookup
  | mutualDef _ ha _ => exact installDefinitions_registered ha hold hlookup
  | «axiom» | «opaque» | «example» | quot | induct =>
    have hh : old name = some value := hlookup
    exact ⟨(hold _ _ hh).1.mono hm, (hold _ _ hh).2⟩

private theorem definitionRegistry_decl_new
    (H : VDecl.WF env declaration extended)
    (hmem : value ∈ declaration.definitionEntries) :
    installDefinitions old declaration.definitionEntries value.name = some value := by
  cases H with
  | «def» hw ha =>
    rename_i next ci
    have ha' : env.addConsts [ci] = some next := by simpa [VEnv.addConsts] using ha
    exact installDefinitions_lookup ha' hmem
  | mutualDef _ ha _ => exact installDefinitions_lookup ha hmem
  | «axiom» | «opaque» | «example» | quot | induct => cases hmem

private theorem definitionRegistry_decl_preserves
    (H : VDecl.WF env declaration extended)
    (hregistered : DefinitionRegistered env value) (hold : old value.name = some value) :
    installDefinitions old declaration.definitionEntries value.name = some value := by
  cases H with
  | «def» hw ha =>
    rename_i next ci
    have ha' : env.addConsts [ci] = some next := by simpa [VEnv.addConsts] using ha
    exact installDefinitions_preserves ha' hregistered hold
  | mutualDef _ ha _ => exact installDefinitions_preserves ha hregistered hold
  | «axiom» | «opaque» | «example» | quot | induct => exact hold

/-- A bare recursor constant equation can only be a transparent definition;
inductive and quotient equations have a constructor application as major. -/
private theorem declaration_constEquation_origin
    (H : VDecl.WF env declaration extended) (hdf : extended.defeqs equation)
    (hhead : equation.lhs = VExpr.const name levels) :
    (∃ value ∈ declaration.definitionEntries, equation = value.toDefEq) ∨ env.defeqs equation := by
  cases H with
  | «axiom» _ ha | «opaque» _ ha =>
    exact .inr (by rwa [VEnv.addConst_defeqs ha] at hdf)
  | «example» => exact .inr hdf
  | «def» _ ha =>
    rcases hdf with rfl | hdf
    · exact .inl ⟨_, List.mem_singleton_self _, rfl⟩
    · exact .inr (by rwa [VEnv.addConst_defeqs ha] at hdf)
  | mutualDef _ ha _ =>
    rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or] at hdf
    rcases hdf with hmem | hdf
    · obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hmem
      exact .inl ⟨value, hvalue, rfl⟩
    · have he := VEnv.addConstVals_defeqs (VEnv.addConsts_eq_addConstVals ▸ ha)
      exact .inr (by rwa [he] at hdf)
  | quot _ ha =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ha
    rcases hdf with rfl | hdf
    · cases hhead
    · exact .inr (by rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
        VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at hdf)
  | induct ha =>
    cases ha with
    | intro _ hcompile _ _ hi =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hi
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hi
      rw [VEnv.addDefEqRules_defeqs_iff_mem_or] at hdf
      rcases hdf with hmem | hdf
      · obtain ⟨_, ⟨fn, us, args, hmajor⟩, _⟩ := hcompile.equation_major_cases equation hmem
        rw [hhead] at hmajor
        cases hmajor
      · exact .inr (by rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hdf)

/-- Every entry of the history-derived table is an actual installed
constant and defining equation at the indicated name. -/
theorem WF'.definitionRegistry_registered (H : env.WF' declarations)
    (hlookup : definitionRegistry declarations name = some value) :
    DefinitionRegistered env value ∧ value.name = name := by
  induction H generalizing name value with
  | empty => cases hlookup
  | decl hd _ ih =>
    exact definitionRegistry_decl hd (fun _ _ h => ih h) hlookup
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hr, hn⟩ := ih hlookup
    exact ⟨hr.mono VEnv.addProjections_le, hn⟩
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hr, hn⟩ := ih hlookup
    exact ⟨hr.mono VEnv.addEliminator_le, hn⟩

/-- Every actual bare-constant equation is represented by the exact value
in the extracted table. Other equation kinds are excluded by generation. -/
theorem WF'.definitionRegistry_of_constantEquation (H : env.WF' declarations)
    (hdf : env.defeqs equation) (hhead : equation.lhs = VExpr.const name levels) :
    ∃ value, definitionRegistry declarations name = some value ∧ equation = value.toDefEq := by
  induction H generalizing name levels with
  | empty => cases hdf
  | decl hd henv ih =>
    rcases declaration_constEquation_origin hd hdf hhead with ⟨value, hmem, rfl⟩ | hold
    · have hn : value.name = name := (VExpr.const.inj hhead).1
      rw [← hn]
      exact ⟨value, definitionRegistry_decl_new hd hmem, rfl⟩
    · obtain ⟨value, hlookup, heq⟩ := ih hold hhead
      have hr := henv.definitionRegistry_registered hlookup
      rw [← hr.2] at hlookup ⊢
      exact ⟨value, definitionRegistry_decl_preserves hd hr.1 hlookup, heq⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih (by simpa only [VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using hdf) hhead
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih hdf hhead

end VEnv
end Lean4Lean

/-! Definition heads are exclusive in the actual declaration history.
Later inductive or quotient equations cannot acquire an occupied head. -/

namespace Lean4Lean.VEnv
variable {env : VEnv}

private theorem declaration_old_equation
    (H : VDecl.WF env declaration extended)
    (hoccupied : env.constants name = some constant) (hdf : extended.defeqs equation)
    (hhead : equation.lhs.equationHead = VExpr.const name levels) :
    env.defeqs equation := by
  have exclude {later : VEnv} (hle : env ≤ later) (hf : later.constants name = none) : False := by
    have hs := hle.constants hoccupied
    rw [hf] at hs
    contradiction
  cases H with
  | «axiom» _ ha | «opaque» _ ha => rwa [VEnv.addConst_defeqs ha] at hdf
  | «example» => exact hdf
  | «def» _ ha =>
    rcases hdf with rfl | hdf
    · have hn := (VExpr.const.inj hhead).1
      have hf := VEnv.addConst_fresh ha
      rw [hn] at hf
      exact (exclude .rfl hf).elim
    · rwa [VEnv.addConst_defeqs ha] at hdf
  | mutualDef _ ha _ =>
    rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or] at hdf
    rcases hdf with hmem | hdf
    · obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hmem
      have hn := (VExpr.const.inj hhead).1
      have hf := VEnv.addConstVals_names_fresh (VEnv.addConsts_eq_addConstVals ▸ ha)
        value.toVConstVal (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
      change env.constants value.name = none at hf
      rw [hn] at hf
      exact (exclude .rfl hf).elim
    · rwa [VEnv.addConstVals_defeqs (VEnv.addConsts_eq_addConstVals ▸ ha)] at hdf
  | quot _ ha =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ha
    rcases hdf with rfl | hdf
    · have hn : ``Quot.lift = name := (VExpr.const.inj hhead).1
      have hf := VEnv.addConst_fresh hc
      rw [hn] at hf
      exact (exclude ((VEnv.addConst_le ha).trans (VEnv.addConst_le hb)) hf).elim
    · rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
        VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at hdf
  | induct ha =>
    cases ha with
    | intro _ hcompile _ _ hi =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hi
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hi
      rw [VEnv.addDefEqRules_defeqs_iff_mem_or] at hdf
      rcases hdf with hmem | hdf
      · obtain ⟨rec, hrec, us, howned⟩ := hcompile.equation_head_owned equation hmem
        rw [VExpr.equationHead_eq] at hhead
        have hn := (VExpr.const.inj (howned.symm.trans hhead)).1
        have hf := VEnv.addConstVals_names_fresh hr rec hrec
        rw [hn] at hf
        exact (exclude (((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
          VEnv.addEliminators_addProjections_le) hf).elim
      · rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hdf

private theorem declaration_new_definition_head
    (hordered : env.Ordered) (H : VDecl.WF env declaration extended)
    (hvalue : value ∈ declaration.definitionEntries) (hdf : extended.defeqs equation)
    (hhead : equation.lhs.equationHead = VExpr.const value.name levels) :
    equation = value.toDefEq := by
  have exclude (hfresh : env.constants value.name = none) (hdf : env.defeqs equation) : False := by
    exact hordered.rigid_of_absent hfresh equation hdf levels
      ((VExpr.equationHead_eq _).symm.trans hhead)
  cases H with
  | «axiom» | «opaque» | «example» | quot | induct => cases hvalue
  | «def» hw ha =>
    have hv : value = _ := List.mem_singleton.mp hvalue
    subst value
    rcases hdf with rfl | hdf
    · rfl
    · have hh : env.defeqs equation := by rwa [VEnv.addConst_defeqs ha] at hdf
      exact (exclude (VEnv.addConst_fresh ha) hh).elim
  | mutualDef htypes ha hvalues =>
    rename_i values next
    rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or] at hdf
    rcases hdf with hmem | hdf
    · obtain ⟨other, hother, rfl⟩ := List.mem_map.mp hmem
      have hn : other.name = value.name := (VExpr.const.inj hhead).1
      have hleft := installDefinitions_lookup (old := fun _ => none) ha hother
      have hright := installDefinitions_lookup (old := fun _ => none) ha hvalue
      rw [hn] at hleft
      cases Option.some.inj (hleft.symm.trans hright)
      rfl
    · have hf := VEnv.addConstVals_names_fresh (VEnv.addConsts_eq_addConstVals ▸ ha)
        value.toVConstVal (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
      have hh : env.defeqs equation := by
        rwa [VEnv.addConstVals_defeqs (VEnv.addConsts_eq_addConstVals ▸ ha)] at hdf
      exact (exclude hf hh).elim

/-- All equations at an ordinary definition's computational head are its
one exact defining equation. This excludes definition/generated-iota overlap. -/
theorem WF'.definition_head_exclusive (H : env.WF' declarations)
    (hlookup : definitionRegistry declarations name = some value)
    (hdf : env.defeqs equation)
    (hhead : equation.lhs.equationHead = VExpr.const name levels) :
    equation = value.toDefEq := by
  induction H generalizing name value with
  | empty => cases hdf
  | decl hd henv ih =>
    rename_i declaration next ds previous
    change installDefinitions _ _ _ = some value at hlookup
    unfold installDefinitions at hlookup
    cases hf : declaration.definitionEntries.find? (fun value => value.name == name) with
    | none =>
      have hold : definitionRegistry ds name = some value := by simpa [hf] using hlookup
      have hr := henv.definitionRegistry_registered hold
      have heq := declaration_old_equation hd (hr.2 ▸ hr.1.1) hdf hhead
      exact ih hold heq hhead
    | some found =>
      simp only [hf, Option.orElse_some, Option.some.injEq] at hlookup
      subst found
      have hn : value.name = name := by simpa using List.find?_some hf
      exact declaration_new_definition_head (VEnv.WF.ordered ⟨_, henv⟩) hd
        (List.mem_of_find?_eq_some hf) hdf (hn ▸ hhead)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih hlookup (by simpa only [VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using hdf) hhead
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hlookup hdf hhead

/-- The public registration witness inherits head exclusivity from the
actual well-formed environment history. -/
theorem DefinitionRegistered.head_exclusive (henv : env.WF)
    (H : DefinitionRegistered env value) (hdf : env.defeqs equation)
    (hhead : equation.lhs.equationHead = VExpr.const value.name levels) :
    equation = value.toDefEq := by
  obtain ⟨declarations, hwf⟩ := henv
  obtain ⟨stored, hl, he⟩ := hwf.definitionRegistry_of_constantEquation H.2 rfl
  exact (hwf.definition_head_exclusive hl hdf hhead).trans he.symm

/-- A real constructor-major equation cannot overlap a transparent
definition at its computational head. -/
theorem DefinitionRegistered.not_constructor_equation (henv : env.WF)
    (H : DefinitionRegistered env value) (hdf : env.defeqs equation)
    (hhead : equation.lhs.equationHead = VExpr.const value.name levels)
    (hmajor : equation.HasConstructorMajor ctorName) : False := by
  rw [H.head_exclusive henv hdf hhead] at hmajor
  obtain ⟨fn, levels, args, he⟩ := hmajor
  cases he

end Lean4Lean.VEnv
