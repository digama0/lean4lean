import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Inductive.RestorationHead

/-! The source sort of a restored case family is justified by its installed
family header and the finite compilation correspondence. -/

namespace Lean4Lean.InductiveSignature

/-- The installed header of a source family is definitionally a telescope whose body is
definitionally the family sort recorded by the normalized source signature.
This open form needs no well-formedness of the environment; it is closed by
`VEnv.IsDefEq.close_sort_header`. -/
theorem CompilationData.source_family_header {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g auxiliaries block)
    (hfamily : family ∈ source.types) :
    ∃ envTypes, base.addConstVals source.typeConstants = some envTypes ∧
      ∃ domains body level exprType, level ≈ family.resultLevel ∧
        envTypes.IsDefEq source.uvars [] family.type (VExpr.wrapForalls domains body) exprType ∧
        envTypes.IsDefEq source.uvars domains.reverse body (.sort level) (.sort (.succ level)) := by
  obtain ⟨envTypes, direct, htypes, _, _, hfamilies⟩ := H.correspondence
  obtain ⟨normalized, hnormalized, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    hfamilies family (List.mem_append_left _ hfamily)
  obtain ⟨domains, body, level, exprType, hlevel, htype, hbody⟩ := hrel.type
  exact ⟨envTypes, htypes, domains, body, level, exprType, hlevel.trans hrel.resultLevel,
    htype, hbody⟩

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv

private theorem addConst_le_target {base added current : VEnv}
    (hle : base ≤ current) (hadd : base.addConst name ci = some added)
    (hvalue : current.constants name = some ci) : added ≤ current := by
  unfold VEnv.addConst at hadd
  split at hadd
  · cases hadd
  · cases hadd
    refine ⟨?_, hle.defeqs, hle.pats, hle.projections⟩
    intro n value hv
    change (if name = n then some ci else base.constants n) = some value at hv
    split at hv
    · rename_i hn
      cases hn
      cases Option.some.inj hv
      exact hvalue
    · exact hle.constants hv

/-- A successful header extension embeds into any later environment that
contains the same exact headers and extends its base. -/
theorem addConstVals_le_target {base added current : VEnv}
    (hle : base ≤ current) (hadd : base.addConstVals values = some added)
    (hvalues : ∀ value ∈ values, current.constants value.name = some value.toVConstant) :
    added ≤ current := by
  induction values generalizing base with
  | nil =>
    have he : base = added := Option.some.inj hadd
    cases he
    exact hle
  | cons value values ih =>
    cases hv : base.addConst value.name value.toVConstant with
    | none => simp [VEnv.addConstVals, hv] at hadd
    | some next =>
      have ht : next.addConstVals values = some added := by
        simpa only [VEnv.addConstVals, hv, bind, Option.bind_some] using hadd
      exact ih (addConst_le_target hle hv (hvalues value (.head _))) ht
        fun value hmem => hvalues value (.tail _ hmem)

end Lean4Lean.VEnv

namespace Lean4Lean

/-- Every finite source header retains a normalized telescope ending in its
recorded family sort in an environment where its exact constants are present. -/
theorem CompiledInductive.source_family_header (H : CompiledInductive base source block) :
    ∀ (current : VEnv), current.WF → base ≤ current →
      (∀ family ∈ source.types,
        current.constants family.name = some family.toVConstant) →
      ∀ family ∈ source.types, ∃ domains level,
        family.uvars = source.uvars ∧ level ≈ family.resultLevel ∧
          current.IsDefEqU source.uvars [] family.type (VExpr.wrapForalls domains (.sort level)) := by
  exact CompiledInductive.rec
    (motive_1 := fun base source _ _ =>
      ∀ current : VEnv, current.WF → base ≤ current →
        (∀ family ∈ source.types, current.constants family.name = some family.toVConstant) →
        ∀ family ∈ source.types, ∃ domains level,
          family.uvars = source.uvars ∧ level ≈ family.resultLevel ∧
            current.IsDefEqU source.uvars [] family.type (VExpr.wrapForalls domains (.sort level)))
    (motive_2 := fun _ _ _ => True)
    (fun hdata _ _ current hcurrentWF hle hconstants family hfamily => by
      obtain ⟨envTypes, htypes, domains, body, level, exprType, hlevel, htype, hbody⟩ :=
        hdata.source_family_header hfamily
      have htypesLE := VEnv.addConstVals_le_target hle htypes (by
        intro value hvalue
        obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
        exact hconstants family hfamily)
      have huvars := hdata.sourceWF.2.2.1 family hfamily
      obtain ⟨_, _, _, _, _, _, _, _, hheaders, _⟩ := hdata.sourceWF
      have hwf := (hheaders family hfamily).mono hle
      change current.IsType family.uvars [] family.type at hwf
      rw [huvars] at hwf
      exact ⟨domains, level, huvars, hlevel,
        VEnv.IsDefEq.close_sort_header hcurrentWF hwf (htype.mono htypesLE)
          (hbody.mono htypesLE)⟩)
    (fun _ hle _ ih current hcurrentWF hcurrent hconstants family hfamily =>
      ih current hcurrentWF (hle.trans hcurrent) hconstants family hfamily)
    trivial (fun _ _ _ _ _ _ _ _ => trivial) H

/-- Every certified container retains both its exact installed family lookup
and its normalized result-sort telescope in every well-formed extension of
the specialization environment. -/
theorem ContainersInstalled.family_header (H : ContainersInstalled env auxiliaries) :
    ∀ current : VEnv, current.WF → env ≤ current →
    ∀ a ∈ auxiliaries, ∀ family ∈ a.container.types,
      env.constants family.name = some family.toVConstant ∧
      ∃ domains level, family.uvars = a.container.uvars ∧ level ≈ family.resultLevel ∧
        current.IsDefEqU a.container.uvars [] family.type (VExpr.wrapForalls domains (.sort level)) := by
  exact ContainersInstalled.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun env auxiliaries _ =>
      ∀ current : VEnv, current.WF → env ≤ current →
      ∀ a ∈ auxiliaries, ∀ family ∈ a.container.types,
        env.constants family.name = some family.toVConstant ∧
        ∃ domains level, family.uvars = a.container.uvars ∧ level ≈ family.resultLevel ∧
          current.IsDefEqU a.container.uvars [] family.type
            (VExpr.wrapForalls domains (.sort level)))
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (by simp)
    (fun {env a rest base block installed} hcompile _ _ hinstall hle _ _ ih => by
      intro current hcurrent hcurrentLE a ha family hfamily
      rcases List.mem_cons.mp ha with rfl | ha
      · have hconstants : ∀ family ∈ a.container.types,
            env.constants family.name = some family.toVConstant := by
          intro family hfamily
          exact hle.constants (VEnv.addInduct_type_find hinstall hfamily)
        exact ⟨hconstants family hfamily,
          hcompile.source_family_header current hcurrent
            (((VEnv.addInduct_le hinstall).trans hle).trans hcurrentLE)
            (fun family hfamily => hcurrentLE.constants (hconstants family hfamily))
            family hfamily⟩
      · exact ih current hcurrent hcurrentLE a ha family hfamily)
    H

end Lean4Lean

namespace Lean4Lean.VEnv
open Lean4Lean
variable {env : VEnv} {U : Nat}
open VExpr

private theorem constant_normalized_header (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hlookup : env.constants name = some ci)
    (hheader : env.IsDefEqU N [] ci.type (VExpr.wrapForalls domains (.sort level)))
    (hlevels : ∀ l ∈ levels, l.WF U) (hlen : levels.length = ci.uvars) :
    env.HasType U Γ (.const name levels)
      (VExpr.wrapForalls (domains.map (instL levels)) (.sort (level.inst levels))) := by
  have hconst := HasType.const hlookup hlevels hlen (Γ := Γ)
  have he := (hheader.instL hlevels).weak0 henv.ordered (Γ := Γ)
  simpa only [instL_wrapForalls, instL] using hconst.defeqU_r henv hΓ he

end Lean4Lean.VEnv

namespace Lean4Lean.InductiveSignature

private theorem ContainerSpecialization.directFamily_resultLevel
    {a : ContainerSpecialization} {U : Nat} {params : List VExpr} {direct : VInductiveType}
    (H : a.specializedFamily U params = some direct) :
    direct.resultLevel = a.source.resultLevel.inst a.levels := by
  unfold ContainerSpecialization.specializedFamily at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, ctors, _, he⟩ := H
  cases Option.some.inj he
  rfl

/-- A restored case family's installed head has a telescope ending in the
specialized source sort. Both source families and certified containers are
justified by their installed header constants. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.family_head_type
    {s : InductiveSignature} {g : Instance s}
    (hdata : CompilationData base source expanded s g auxiliaries sourceBlock)
    (hprior : ContainersInstalled base auxiliaries)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hle : base ≤ env)
    (hconstants : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant)
    (owner : Fin s.families.size)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlen : levels.length = s.uvars) :
    ∃ domains level,
      env.HasType U Γ
        (.const ((compilationRestoration source auxiliaries).headName s.families[owner].name)
          ((compilationRestoration source auxiliaries).headLevels s.families[owner].name levels))
        (VExpr.wrapForalls domains (.sort level)) ∧ level ≈ s.families[owner].resultLevel.inst levels := by
  obtain ⟨envTypes, direct, htypes, hdirect, hargs, hfamilies⟩ := hdata.correspondence
  have htypesLE := VEnv.addConstVals_le_target hle htypes (by
    intro value hvalue
    obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
    exact hconstants family hfamily)
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem owner)
  have hname : s.families[owner].name = family.name := hrel.name
  have hsourceUvars : s.uvars = source.uvars := hdata.model.uvars.trans hdata.uvars
  rcases List.mem_append.mp hfamily with hfamily | hfamily
  · have hfamilyName : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hfamily, List.mem_cons_self⟩
    obtain ⟨domains, body, level, exprType, hlevel, htype, hbody⟩ := hrel.type
    have huvars := hdata.sourceWF.2.2.1 family hfamily
    have hwf : env.IsType source.uvars [] family.type := by
      obtain ⟨_, _, _, _, _, _, _, _, hheaders, _⟩ := hdata.sourceWF
      have := (hheaders family hfamily).mono hle
      change env.IsType family.uvars [] family.type at this
      rwa [huvars] at this
    have hheader := VEnv.IsDefEq.close_sort_header henv hwf (htype.mono htypesLE)
      (hbody.mono htypesLE)
    have htyped := VEnv.constant_normalized_header henv hΓ (hconstants family hfamily)
      hheader hlevels (hlen.trans (hsourceUvars.trans huvars.symm))
    rw [hname, hdata.headName_source hfamilyName, hdata.headLevels_source hfamilyName]
    refine ⟨_, _, htyped, ?_⟩
    exact VLevel.inst_congr_l (by simpa only [declarationFamily] using hlevel)
  · obtain ⟨a, ha, hfamily⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) family hfamily
    have hfamilyName := ContainerSpecialization.directFamily_name hfamily
    have hfamilyLevel := ContainerSpecialization.directFamily_resultLevel hfamily
    let spec : HeadSpecialization := {
      auxiliary := a.auxiliary, uvars := source.uvars, nparams := source.nparams,
      target := a.source.name, levels := a.levels, arguments := a.arguments }
    have hspec : spec ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hhead := Restoration.headName_of_mem hdata.restorationScoped hspec
    have hheadLevels := Restoration.headLevels_of_mem (levels := levels) hdata.restorationScoped hspec
    obtain ⟨hlookup, domains, level, hfamilyUvars, hlevel, hheader⟩ :=
      hprior.family_header env henv hle a ha a.source (List.getElem_mem a.family.isLt)
    have hnativeWF : ∀ l ∈ a.levels.map (·.inst levels), l.WF U := by
      intro l hl
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hl
      exact VLevel.WF.inst hlevels
    have hnativeLength : (a.levels.map (·.inst levels)).length = a.source.uvars := by
      simpa only [List.length_map, hfamilyUvars] using (hargs a ha).2.2.1
    have htyped := VEnv.constant_normalized_header henv hΓ (hle.constants hlookup)
      hheader hnativeWF hnativeLength
    rw [hname, hfamilyName, hhead, hheadLevels]
    refine ⟨_, _, htyped, ?_⟩
    have hsourceLevel : s.families[owner].resultLevel ≈
        a.source.resultLevel.inst a.levels := by
      simpa only [hfamilyLevel, declarationFamily] using hrel.resultLevel
    exact (VLevel.inst_congr_l hlevel).trans (by
      rw [← VLevel.inst_inst]
      exact (VLevel.inst_congr_l hsourceLevel).symm)


namespace RecursorSchema

end RecursorSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.InductiveSignature.RecursorSchema

end Lean4Lean.InductiveSignature.RecursorSchema

namespace Lean4Lean.VEnv
open Lean4Lean VExpr InductiveSignature InductiveSignature.RecursorSchema
variable {env : VEnv} {U : Nat}

end Lean4Lean.VEnv
