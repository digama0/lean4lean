import Lean4Lean.Theory.Typing.CaseMotive
import Lean4Lean.Theory.Typing.CaseMajorDomain
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

private theorem isType_wrapForalls_inv {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {domains Γ : List VExpr} {body : VExpr}, OnCtx Γ (env.IsType U) →
      env.IsType U Γ (VExpr.wrapForalls domains body) →
      OnCtx (domains.reverse ++ Γ) (env.IsType U)
  | [], _, _, hΓ, _ => hΓ
  | d :: ds, Γ, body, hΓ, H => by
    have hinv := IsType.forallE_inv henv H
    have := isType_wrapForalls_inv henv (domains := ds) (Γ := d :: Γ) (body := body)
      ⟨hΓ, hinv.1⟩ hinv.2
    simpa [List.reverse_cons, List.append_assoc] using this

/-- Close the open header form: a well-formed type definitionally equal to a
telescope whose body is definitionally a sort in the telescope's scope is
definitionally the telescope ending in that sort. -/
theorem IsDefEq.close_sort_header {env : VEnv} {U : Nat} {T A body : VExpr}
    {domains : List VExpr} {level : VLevel}
    (henv : env.WF) (hT : env.IsType U [] T)
    (h1 : env.IsDefEq U [] T (VExpr.wrapForalls domains body) A)
    (h2 : env.IsDefEq U domains.reverse body (.sort level) (.sort (.succ level))) :
    env.IsDefEqU U [] T (VExpr.wrapForalls domains (.sort level)) := by
  have hW : env.IsType U [] (VExpr.wrapForalls domains body) :=
    hT.defeqU_l henv trivial ⟨A, h1⟩
  have hctx := isType_wrapForalls_inv henv.ordered (Γ := []) trivial hW
  obtain ⟨_, hw⟩ := VExpr.wrapForalls_defeq (Γ := []) (by simpa using hctx) (by simpa using h2)
  exact IsDefEqU.trans henv trivial ⟨_, h1⟩ ⟨_, hw⟩

private theorem addConst_le_target {base added current : VEnv}
    (hle : base ≤ current) (hadd : base.addConst name ci = some added)
    (hvalue : current.constants name = some ci) : added ≤ current := by
  unfold VEnv.addConst at hadd
  split at hadd
  · cases hadd
  · cases hadd
    refine ⟨?_, hle.defeqs, hle.projections, hle.eliminators⟩
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
    trivial (fun _ _ _ _ _ _ _ => trivial) H

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
    (fun {env a rest base block installed} hcompile _ hinstall hle _ _ ih => by
      intro current hcurrent hcurrentLE a ha family hfamily
      rcases List.mem_cons.mp ha with rfl | ha
      · have hconstants : ∀ family ∈ a.container.types,
            env.constants family.name = some family.toVConstant := by
          intro family hfamily
          apply hle.constants
          apply VInductBlock.install_type_lookup hinstall
          rw [hcompile.types_eq]
          exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
        exact ⟨hconstants family hfamily,
          hcompile.source_family_header current hcurrent
            (((VInductBlock.install_base_le hinstall).trans hle).trans hcurrentLE)
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
theorem _root_.Lean4Lean.InductiveSignature.CaseCompilationData.family_head_type
    {s : InductiveSignature}
    (hdata : CaseCompilationData base source expanded s auxiliaries sourceBlock)
    (hdisj : RecursorNamesFresh base source expanded auxiliaries)
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
    rw [hname, hdata.headName_source hdisj hfamilyName, hdata.headLevels_source hfamilyName]
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


namespace CaseSchema

/-- A restored case family's installed head has a telescope ending in the
specialized source sort. Both source families and certified containers are
justified by their installed header constants. -/
theorem Certified.family_head_type {schema : CaseSchema}
    (H : schema.Certified base source sourceBlock)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hle : base ≤ env)
    (hconstants : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant)
    (owner : Fin schema.signature.families.size)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlen : levels.length = schema.signature.uvars) :
    ∃ domains level,
      env.HasType U Γ
        (.const (schema.restoration.headName schema.signature.families[owner].name)
          (schema.restoration.headLevels schema.signature.families[owner].name levels))
        (VExpr.wrapForalls domains (.sort level)) ∧ level ≈ schema.sourceLevel owner levels := by
  obtain ⟨expanded, auxiliaries, hdata, hprior, hr, _, hdisj⟩ := H
  rw [hr]
  exact hdata.family_head_type hdisj hprior henv hΓ hle hconstants owner hlevels hlen

end CaseSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.InductiveSignature.CaseSchema

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.VEnv
open Lean4Lean VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

/-- The major argument's family type has the source universe recorded by
the installed schema, including universe specialization through restoration. -/
theorem HasType.caseMajor_source_sort (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {levels : List VLevel} {target : VLevel} {args : List VExpr} {major : VExpr}
    (hlookup : env.eliminators block schema)
    (hpermission : schema.Permission U owner levels target)
    (hlen : args.length = caseMajorArity schema owner)
    (H : VExpr.WF env U Γ
      (VExpr.mkApps (.elim block owner.val (target :: levels)) (args ++ [major]))) :
    ∃ type level, env.HasType U Γ major type ∧ env.HasType U Γ type (.sort level) ∧
      level ≈ schema.sourceLevel owner levels := by
  obtain ⟨base, source, native, _, hle, hcert, _, hconstants⟩ :=
    henv.eliminator_installed hlookup
  have hsource : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant := by
    intro family hfamily
    obtain ⟨expanded, auxiliaries, hdata, _⟩ := hcert
    apply hconstants family.toVConstVal
    apply List.mem_append_left
    rw [hdata.types]
    exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
  obtain ⟨domains, level, hhead, hlevel⟩ := hcert.family_head_type henv
    (Γ := []) (U := schema.genericUvars) True.intro hle hsource owner
    (levels := schema.genericLevels)
    (by simp [genericLevels, genericUvars, VLevel.WF])
    (by simp [genericLevels])
  have hhead' := (hhead.instL hpermission.packedWF).weak0 henv.ordered (Γ := Γ)
  simp only [instL_wrapForalls, VExpr.instL] at hhead'
  obtain ⟨familyArgs, hmajor⟩ := HasType.caseMajor_type henv hΓ hlookup hlen H
  obtain ⟨_, hfamily⟩ := hmajor.isType henv.ordered hΓ
  have hargsLength := HasType.mkApps_sort_arity henv hΓ hhead' hfamily
  have hfamilySort := (HasType.mkApps_wrapForalls henv hΓ hhead' ⟨_, hfamily⟩
    hargsLength).2
  simp only [instOuter_sort] at hfamilySort
  refine ⟨_, _, hmajor, hfamilySort, ?_⟩
  have heq := VLevel.inst_congr_l (ls := target :: levels) hlevel
  simpa only [sourceLevel, VLevel.inst_inst, genericLevels_inst hpermission.length] using heq

/-- A case application whose source is always nonzero cannot inspect a
proof. This is derived from typing, rather than added to the schema contract. -/
theorem HasType.caseMajor_not_proof (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {levels : List VLevel} {target : VLevel} {args : List VExpr} {major proposition : VExpr}
    (hlookup : env.eliminators block schema)
    (hpermission : schema.Permission U owner levels target)
    (hlen : args.length = caseMajorArity schema owner)
    (H : VExpr.WF env U Γ
      (VExpr.mkApps (.elim block owner.val (target :: levels)) (args ++ [major])))
    (hnever : (schema.sourceLevel owner levels).IsNeverZero)
    (hprop : env.HasType U Γ proposition (.sort .zero))
    (hproof : env.HasType U Γ major proposition) : False := by
  obtain ⟨type, level, hmajor, htype, hlevel⟩ :=
    HasType.caseMajor_source_sort henv hΓ hlookup hpermission hlen H
  have hsame := hmajor.uniqU henv hΓ hproof
  have hprop' := htype.defeqU_l henv hΓ hsame
  have hzero := (hprop'.uniqU henv hΓ hprop).sort_inv henv hΓ
  exact hnever [] (VLevel.equiv_def.mp (hlevel.symm.trans hzero) [])

/-- When a matched constructor is a proof, the case permission forces the
result into Prop. This supplies the proof-irrelevance branch of compatibility. -/
theorem CaseRedex.result_prop_of_major_proof (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : CaseRedex env U Γ rule actual)
    {proposition : VExpr}
    (hprop : env.HasType U Γ proposition (.sort .zero))
    (hproof : env.HasType U Γ
      (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
      proposition) :
    ∃ resultType, env.HasType U Γ resultType (.sort .zero) ∧
      env.HasType U Γ actual.expr resultType := by
  apply H.result_prop_of_target_zero henv hΓ
  have hsource := H.source
  generalize hpacked : actual.levels = packed at hsource
  cases hsource with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    have htarget : target ≈ .zero := by
      rcases hp.admissible with hnever | hzero
      · obtain ⟨base, source, sourceBlock, _, _, hcert, _, _⟩ :=
          henv.eliminator_installed hl
        have harity := hcert.arguments_length hg
        obtain ⟨hb, ho⟩ := hg.owned
        have hab : actual.block = block := H.block_eq.trans hb
        have hao : actual.owner = owner.val := H.owner_eq.trans ho
        have ht : VExpr.WF env U Γ (VExpr.mkApps
            (.elim block owner.val (target :: levels))
            (actual.arguments ++ [VExpr.mkApps (.const actual.ctorName actual.ctorLevels)
              actual.ctorArguments])) := by
          obtain ⟨type, hguard⟩ := H.guard
          refine ⟨type, ?_⟩
          simpa only [HasType, Application.expr, VExpr.mkApps, List.foldl_append,
            List.foldl_cons, List.foldl_nil,
            hab, hao, hpacked] using hguard.hasType.1
        exact False.elim (HasType.caseMajor_not_proof henv hΓ hl hp
          (H.arguments_length.trans harity) ht hnever hprop hproof)
      · exact hzero
    simpa only [hpacked, List.head?_cons, Option.getD_some] using htarget

end Lean4Lean.VEnv
