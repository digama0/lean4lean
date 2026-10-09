import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CaseRule

/-! # The projection facts of rule majors (`ProjMajor`) in a well-formed environment

`ProjMajor` (`Model/RecursorRule.lean`) of the family of a rule's major: the family is not
projection-registered and the constructor is not a projection constructor, or the family's entry
is valid, has the major's constructor, parameter count and field count, and the family's result
level. The parameter count is fixed by the declaration that registered the entry, which is the
declaration of the rule (`projMajor_of_entry`): for a recursor rule the installing block's own
entry (`projMajor_source`), for a generic case equation the certified declaration's entry
(`ProjectionsCoherent`), for a container constructor the container's entry
(`projMajor_container`). The field count is the syntactic arity of the constructor, from
soundness of the header environment (`CaseCompilationData.source_arity_sem`).

`ProjsClosed envF env`: the projection entries of `envF` whose constructor is a constructor of a
rule of `env` are entries of `env`. It is carried down the declaration history (no later
declaration registers an entry for an existing constructor), and lets the history induction use
the validity of the entry proved when it was registered. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

/-- The entries of `envF` for constructors of rules of `env` are entries of `env`. -/
def ProjsClosed (envF env : VEnv) : Prop :=
  ∀ S info, envF.projections S info → Model.IsCtor env info.ctorName → env.projections S info

theorem Model.IsInstalledCtor.mono {env env' : VEnv} {c : Name}
    (hdf : ∀ df, env.defeqs df → env'.defeqs df) (h : Model.IsInstalledCtor env c) :
    Model.IsInstalledCtor env' c :=
  let ⟨df, h, hm⟩ := h; ⟨df, hdf df h, hm⟩

theorem Model.IsCtor.mono {env env' : VEnv} {c : Name}
    (hdf : ∀ df, env.defeqs df → env'.defeqs df)
    (hel : ∀ b s, env.eliminators b s → env'.eliminators b s) (h : Model.IsCtor env c) :
    Model.IsCtor env' c := by
  rcases h with h | ⟨b, s, o, r, h, hg, hc⟩
  · exact .inl (h.mono hdf)
  · exact .inr ⟨b, s, o, r, hel b s h, hg, hc⟩

/-- `ProjsClosed` down a step whose new entries have constructors fresh before the step. -/
theorem ProjsClosed.down {envF env0 env' : VEnv} (H : ProjsClosed envF env') (h0 : env0.WF)
    (hdf : ∀ df, env0.defeqs df → env'.defeqs df)
    (hel : ∀ b s, env0.eliminators b s → env'.eliminators b s)
    (hnew : ∀ S info, env'.projections S info →
      env0.projections S info ∨ env0.constants info.ctorName = none) :
    ProjsClosed envF env0 := by
  intro S info hp hc
  rcases hnew S info (H S info hp (hc.mono hdf hel)) with h | h
  · exact h
  · obtain ⟨ci, hci⟩ := h0.isCtor_const hc
    rw [h] at hci; cases hci

/-- The family slot of an auxiliary family: its restored head is the container family, and its
result level is the container's at the specialization levels. -/
theorem CaseCompilationData.aux_slot {base : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (C : CaseCompilationData base source expanded s aux block)
    (o : Fin s.families.size) (ho : source.types.length ≤ o.val) {a : ContainerSpecialization}
    (ha : aux[o.val - source.types.length]? = some a) :
    (compilationRestoration source aux).headName s.families[o].name = a.source.name ∧
      s.families[o].resultLevel ≈ a.source.resultLevel.inst a.levels := by
  obtain ⟨_, direct, _, hdirect, hlt, hrel⟩ := EnvTables.CaseCompilationData.family_slot C o
  have hrel' := List.mapM_eq_some.mp hdirect
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hdi, hdf⟩ := List.forall₂_getElem_exists hrel' (o.val - source.types.length) hi
  rw [List.getElem_append_right ho] at hrel
  rw [hai] at hdf
  have hname : s.families[o].name = a.auxiliary :=
    hrel.name.trans (ContainerSpecialization.directFamily_name hdf)
  refine ⟨?_, ?_⟩
  · rw [hname]
    exact Restoration.headName_of_mem (spec := HeadSpecialization.mk a.auxiliary source.uvars
      source.nparams a.source.name a.levels a.arguments) C.restorationScoped
      (List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, List.mem_cons_self⟩)
  · have := hrel.resultLevel
    rw [ContainerSpecialization.directFamily_resultLevel_nested hdf] at this
    exact this

namespace Model

theorem ProjMajor.congr_level {env : VEnv} {I c : Name} {np nf : Nat} {L L' : VLevel}
    (h : ProjMajor env I c np nf L) (hL : L ≈ L') : ProjMajor env I c np nf L' := by
  rcases h with h | ⟨info, h1, h2, h3, h4, h5, h6⟩
  · exact .inl h
  · exact .inr ⟨info, h1, h2, h3, h4, h5, (Eq.trans h6 hL : info.resultLevel ≈ L')⟩

/-- **`ProjMajor` of a source family**, given that its entries in `envF` are entries of the
source declaration and valid. -/
theorem projMajor_of_entry {envF base E : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hF : envF.WF)
    (C : CaseCompilationData base source expanded s aux block)
    (hfresh : RecursorNamesFresh base source expanded aux)
    (hprior : ContainersInstalled base aux) (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → SoundTypedIn envF E U Δ) (hbE : base ≤ E)
    (htypesE : ∀ t ∈ source.types, E.constants t.name = some t.toVConstant)
    (index : Fin s.constructors.size)
    (ho : s.constructors[index].owner.val < source.types.length)
    (hrigF : envF.Rigid ((compilationRestoration source aux).headName
      s.families[s.constructors[index].owner].name))
    {c : VConstVal} (hc : c ∈ source.types[s.constructors[index].owner.val].ctors)
    (hcn : c.name = s.constructors[index].name)
    (hcconst : envF.constants c.name = some c.toVConstant) (hcis : IsCtor envF c.name)
    (hentry : ∀ info, envF.projections source.types[s.constructors[index].owner.val].name info →
      (⟨source.types[s.constructors[index].owner.val].name, info⟩ : VProjectionEntry) ∈
        source.projectionEntries ∧
      ProjValid envF source.types[s.constructors[index].owner.val].name info) :
    ProjMajor envF source.types[s.constructors[index].owner.val].name c.name s.params.length
      s.constructors[index].fields.length source.types[s.constructors[index].owner.val].resultLevel := by
  have hFm := List.getElem_mem ho
  obtain ⟨_, _, _, _, _, hraw⟩ := C.sourceParameters
  obtain ⟨doms, result, heq, _, _, hhead, -⟩ := (hraw _ hFm c hc).forallArity
  have hcf : CtorFam envF c.name source.types[s.constructors[index].owner.val].name :=
    ⟨_, _, hcconst, by
      show c.type.forallResult.getAppFnArgs.1 = _
      rw [heq, VExpr.forallResult_wrapForalls, VExpr.forallResult_of_head hhead, hhead]⟩
  by_cases hex : ∃ info, envF.projections source.types[s.constructors[index].owner.val].name info
  · obtain ⟨info, hp⟩ := hex
    have hcn2 : c.name = info.ctorName := hF.ctor_of_projFamily hp hcis hcf
    obtain ⟨hmem, hPV⟩ := hentry info hp
    obtain ⟨type, htype, ctor0, hctors, he⟩ := VInductDecl.projectionEntries_origin hmem
    simp only [VProjectionEntry.mk.injEq] at he
    obtain ⟨hS, rfl⟩ := he
    have htt : type = source.types[s.constructors[index].owner.val] :=
      VInductDecl.type_eq_of_mem_name C.sourceWF.2.1 htype hFm hS.symm
    subst htt
    have hc0 : c = ctor0 := by rw [hctors] at hc; exact List.mem_singleton.1 hc
    subst hc0
    have harity := CaseCompilationData.source_arity_sem C hfresh hprior hE hEF hsnd hbE htypesE index hrigF
      hFm hc hcn
    have hnp : s.params.length = source.nparams := by rw [C.model.nparams, C.nparams]
    refine .inr ⟨_, hp, hPV, rfl, hnp.symm, ?_, VLevel.equiv_def'.2 rfl⟩
    simp only [VProjectionInfo.numFields]
    omega
  · exact .inl ⟨fun info h => hex ⟨info, h⟩, fun hpc' =>
      let ⟨info, h, _⟩ := hF.projCtor_family hpc' hcf; hex ⟨info, h⟩⟩

/-- **`ProjMajor` of a source family of an installed compilation.** -/
theorem projMajor_source {envF env0 installed base E : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hF : envF.WF)
    (C : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) (h0 : env0.Ordered)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (hpc : ProjsClosed envF installed)
    (hPV : ∀ S info, installed.projections S info → ProjValid envF S info)
    (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → SoundTypedIn envF E U Δ) (hbE : base ≤ E)
    (htypesE : ∀ t ∈ source.types, E.constants t.name = some t.toVConstant)
    (index : Fin s.constructors.size)
    (ho : s.constructors[index].owner.val < source.types.length)
    (hrigF : envF.Rigid ((compilationRestoration source aux).headName
      s.families[s.constructors[index].owner].name)) :
    ProjMajor envF ((compilationRestoration source aux).headName
        s.families[s.constructors[index].owner].name)
      ((compilationRestoration source aux).headName s.constructors[index].name)
      s.params.length s.constructors[index].fields.length
      s.families[s.constructors[index].owner].resultLevel := by
  obtain ⟨hfn, -, hctorOf⟩ := EnvTables.CaseCompilationData.source_slot C.toCaseCompilationData _ ho
  obtain ⟨c, hc, hcn⟩ := hctorOf index rfl
  have hFm := List.getElem_mem ho
  have hfnF : s.families[s.constructors[index].owner].name ∈ familyNames source.types := by
    rw [hfn]; exact List.mem_flatMap.mpr ⟨_, hFm, List.mem_cons_self⟩
  have hcnF : c.name ∈ familyNames source.types :=
    List.mem_flatMap.mpr ⟨_, hFm, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  rw [C.headName_source hfnF, ← hcn, C.headName_source hcnF, hfn]
  -- the result level
  obtain ⟨_, direct, _, _, hlt, hrel⟩ := EnvTables.CaseCompilationData.family_slot C.toCaseCompilationData
    s.constructors[index].owner
  have hget : (source.types ++ direct)[s.constructors[index].owner.val] =
      source.types[s.constructors[index].owner.val] := List.getElem_append_left ho
  rw [hget] at hrel
  have hlev : s.families[s.constructors[index].owner].resultLevel ≈
      source.types[s.constructors[index].owner.val].resultLevel := hrel.resultLevel
  refine ProjMajor.congr_level ?_ (Eq.symm hlev : _ ≈ _)
  -- the installed constructor
  obtain ⟨ρ, hρmem, hρ⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp C.equations) (g.equation index)
    (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)
  have hρI : installed.defeqs ρ := VInductBlock.install_rule hinst hρmem
  obtain ⟨Ds, idx, hρlhs⟩ := EnvTables.CompilationData.source_rule C index ho hc hcn hρ
  have hcis : IsInstalledCtor installed c.name :=
    ⟨ρ, hρI, _, _, _, by rw [hρlhs, EnvTables.ruleBody_stripLams]⟩
  have hcconst : envF.constants c.name = some c.toVConstant :=
    hle.constants (VInductBlock.install_ctor_lookup hinst (by
      rw [C.ctors]; exact List.mem_flatMap.mpr ⟨_, hFm, hc⟩))
  refine projMajor_of_entry hF C.toCaseCompilationData C.recursorNamesFresh hprior hE hEF hsnd hbE htypesE index ho hrigF hc hcn hcconst
    (.inl (hcis.mono fun _ => hle.defeqs)) fun info hp => ?_
  have hcn2 : c.name = info.ctorName := hF.ctor_of_projFamily hp
    (.inl (hcis.mono fun _ => hle.defeqs))
    ⟨_, _, hcconst, by
      obtain ⟨_, _, _, _, _, hraw⟩ := C.sourceParameters
      obtain ⟨doms, result, heq, _, _, hhead, -⟩ := (hraw _ hFm c hc).forallArity
      show c.type.forallResult.getAppFnArgs.1 = _
      rw [heq, VExpr.forallResult_wrapForalls, VExpr.forallResult_of_head hhead, hhead]⟩
  have hpI := hpc _ _ hp (by rw [← hcn2]; exact .inl hcis)
  refine ⟨?_, hPV _ _ hpI⟩
  rcases (EnvTables.install_projections hinst).1 hpI with ⟨entry, hentry, hS, hinfo⟩ | hold
  · rw [C.projections] at hentry
    rw [hS, hinfo]; exact hentry
  · exfalso
    obtain ⟨_, hci⟩ := h0.projectionConstant hold
    obtain ⟨types, ht, -⟩ := install_parts hinst
    rw [C.types] at ht
    have := addConstVals_names_fresh ht _ (List.mem_map_of_mem hFm)
    rw [this] at hci; cases hci

/-- **`ProjMajor` of a container family.** -/
theorem projMajor_container {envF env0 base : VEnv} {aux : List ContainerSpecialization}
    (hF : envF.WF) (hprior : ContainersInstalled base aux) (hb0 : base ≤ env0)
    (h0F : env0 ≤ envF) (hpc : ProjsClosed envF env0)
    (hPV : ∀ S info, env0.projections S info → ProjValid envF S info)
    {a : ContainerSpecialization} (ha : a ∈ aux) {c : VConstVal} (hc : c ∈ a.source.ctors)
    {nf : Nat} (harity : nf + a.container.nparams = c.type.forallArity) :
    ProjMajor envF a.source.name c.name a.container.nparams nf a.source.resultLevel := by
  have hcis : IsInstalledCtor env0 c.name := container_ctor_installed hprior hb0 ha hc
  obtain ⟨h1, ls, h2⟩ := hprior.container_ctor a ha c hc
  have hcf : CtorFam envF c.name a.source.name := ⟨_, ls, (hb0.trans h0F).constants h1, h2⟩
  by_cases hex : ∃ info, envF.projections a.source.name info
  · obtain ⟨info, hp⟩ := hex
    obtain ⟨-, hinfo⟩ := hF.container_entry hprior (hb0.trans h0F) ha hc hp
    have hp0 := hpc _ _ hp (by rw [hinfo]; exact .inl hcis)
    refine .inr ⟨info, hp, hPV _ _ hp0, by rw [hinfo], by rw [hinfo], ?_, ?_⟩
    · rw [hinfo]; simp only [VProjectionInfo.numFields]; omega
    · rw [hinfo]; exact VLevel.equiv_def'.2 rfl
  · exact .inl ⟨fun info h => hex ⟨info, h⟩, fun hpc' =>
      let ⟨info, h, _⟩ := hF.projCtor_family hpc' hcf; hex ⟨info, h⟩⟩

/-- **`ProjMajor` at a restored recursor equation** (ordinary or nested), in the form taken by
`RuleValid.nested`. -/
theorem projMajor_restored {envF env0 installed base E : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} {df : VDefEq} (hF : envF.WF)
    (C : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) (h0 : env0.Ordered)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (hpc : ProjsClosed envF installed)
    (hPV : ∀ S info, installed.projections S info → ProjValid envF S info)
    (hb0 : base ≤ env0) (hle0 : env0 ≤ envF) (hpc0 : ProjsClosed envF env0)
    (hPV0 : ∀ S info, env0.projections S info → ProjValid envF S info)
    (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → SoundTypedIn envF E U Δ) (hbE : base ≤ E)
    (htypesE : ∀ t ∈ source.types, E.constants t.name = some t.toVConstant)
    (index : Fin s.constructors.size)
    (hres : (compilationRestoration source aux).equation (g.equation index) = some df)
    (hrigF : envF.Rigid ((compilationRestoration source aux).headName
      s.families[s.constructors[index].owner].name)) :
    ∀ fn lsC' ms', df.lhs.stripLams = .app fn (.mkApps
        (.const ((compilationRestoration source aux).headName s.constructors[index].name) lsC')
        (ms' ++ (eqFs index).map .bvar)) →
      ∃ L', ProjMajor envF ((compilationRestoration source aux).headName
          s.families[s.constructors[index].owner].name)
        ((compilationRestoration source aux).headName s.constructors[index].name)
        ms'.length (eqFs index).length L' ∧
        ((∀ fam ∈ s.families.toList, (fam.resultLevel.inst g.levels).IsNeverZero) →
          (L'.inst lsC').IsNeverZero) := by
  intro fn lsC' ms' hm
  obtain ⟨Ds, idx, major, hlhs, _, hcases⟩ := EnvTables.CompilationData.major_cases C index hres
  have hmaj : major = .mkApps (.const ((compilationRestoration source aux).headName
      s.constructors[index].name) lsC') (ms' ++ (eqFs index).map .bvar) := by
    rw [hlhs, EnvTables.ruleBody_stripLams] at hm; exact (VExpr.app.inj hm).2
  have hfs : (eqFs index).map VExpr.bvar = vars s.constructors[index].fields.length 0 := by
    simp [eqFs, vars]
  rw [hfs] at hmaj
  have hmemF : s.families[s.constructors[index].owner] ∈ s.families.toList :=
    Array.mem_toList_iff.2 (Array.getElem_mem _)
  have hfl : (eqFs index).length = s.constructors[index].fields.length := by simp [eqFs]
  rw [hfl]
  rcases hcases with ⟨F, hF', hFget, c, hc, hcn, rfl⟩ | ⟨a, ha, hge, haget, c, hc, hcn, rfl⟩
  · obtain ⟨-, rfl, hargs⟩ := EnvTables.mkApps_const_inj hmaj
    have hms := (List.append_inj' hargs (by simp)).1
    have ho : s.constructors[index].owner.val < source.types.length :=
      (List.getElem?_eq_some_iff.1 hFget).1
    refine ⟨s.families[s.constructors[index].owner].resultLevel, ?_, fun hnz => hnz _ hmemF⟩
    rw [← hms, InductiveSignature.length_vars]
    exact projMajor_source hF C hprior h0 hinst hle hpc hPV hE hEF hsnd hbE htypesE index ho hrigF
  · obtain ⟨hcn', rfl, hargs⟩ := EnvTables.mkApps_const_inj hmaj
    have hms := (List.append_inj' hargs (by simp)).1
    obtain ⟨hhd, hlev⟩ := CaseCompilationData.aux_slot C.toCaseCompilationData _ hge haget
    obtain ⟨_, _, _, _, hwf, _⟩ := C.correspondence
    have hargsl : a.arguments.length = a.container.nparams := (hwf a ha).1
    have harity := CaseCompilationData.container_arity_sem C.toCaseCompilationData C.recursorNamesFresh hprior hE hEF hsnd hbE htypesE index
      hrigF ha hc hcn
    have hpmC := projMajor_container (nf := s.constructors[index].fields.length) hF hprior hb0 hle0
      hpc0 hPV0 ha hc (by omega)
    refine ⟨a.source.resultLevel, ?_, fun hnz => ?_⟩
    · rw [hhd, ← hcn', ← hms, List.length_map, hargsl]; exact hpmC
    · rw [← VLevel.inst_inst]
      exact (hnz _ hmemF).of_equiv (VLevel.inst_congr_l hlev)

/-- **`ProjMajor` at a generic case equation** of a registered certified schema, in the form taken
by `ElimValid.of_certified`. `env` is the environment at the registration; a projection entry
of `envF` for a family of the certified declaration whose constructor is a case constructor of the
registration is one of the declaration's own entries, and valid (`hsrc`). -/
theorem projMajor_generic {envF env base : VEnv} {source expanded : VInductDecl}
    {schema : CaseSchema} {aux : List ContainerSpecialization}
    {block : VInductBlock} {key : Name} {owner : Fin schema.signature.families.size}
    {rules : List VDefEq} {df : VDefEq} (hF : envF.WF) (hW : env.Ordered)
    (hle : env.addEliminator key schema ≤ envF)
    (C : CaseCompilationData base source expanded schema.signature aux block)
    (hfresh : RecursorNamesFresh base source expanded aux)
    (hprior : ContainersInstalled base aux)
    (hrr : schema.restoration = compilationRestoration source aux) (hble : base ≤ env)
    (hpc0 : ProjsClosed envF env) (V : EnvValid envF env)
    (hsrc : ∀ F ∈ source.types, ∀ info, envF.projections F.name info →
      IsCaseCtor (env.addEliminator key schema) info.ctorName →
      (⟨F.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries ∧ ProjValid envF F.name info)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hr : schema.genericEquations key owner = some rules) (hm : df ∈ rules)
    (hIrig : envF.Rigid (schema.restoration.headName schema.signature.families[owner].name)) :
    ∀ (i : Fin schema.signature.constructors.size) (e : Nat) (c : Name) (lsC : List VLevel)
      (ms : List VExpr) (fn : VExpr), schema.signature.constructors[i].owner = owner → 1 ≤ e →
      df.lhs.stripLams = .app fn (VExpr.mkApps (.const c lsC)
        (ms ++ vars schema.signature.constructors[i].fields.length 0)) →
      schema.restoration.expr (VExpr.mkApps
        (.const schema.signature.constructors[i].name schema.genericLevels)
        (vars schema.signature.params.length (e + schema.signature.constructors[i].fields.length) ++
          vars schema.signature.constructors[i].fields.length 0)) =
        some (VExpr.mkApps (.const c lsC) (ms ++ vars schema.signature.constructors[i].fields.length 0)) →
      ∃ L', ProjMajor envF (schema.restoration.headName schema.signature.families[owner].name) c
          ms.length schema.signature.constructors[i].fields.length L' ∧
        ∀ levels target, levels.length = schema.signature.uvars →
          (schema.sourceLevel owner levels).IsNeverZero →
          ((L'.inst lsC).inst (target :: levels)).IsNeverZero := by
  intro i e c lsC ms fn hown he hmaj hR
  have hle0 : env ≤ envF := (show env ≤ env.addEliminator key schema from
    ⟨id, id, id, fun h => .inr h⟩).trans hle
  -- the major's constructor is a case constructor of the registration
  have hcisE : IsCaseCtor (env.addEliminator key schema) c := by
    obtain ⟨rule', hgen', hreq'⟩ := CaseSchema.generates_of_genericEquation hr hm
    obtain ⟨fn', ls', args', hm'⟩ := generates_major hgen'
    rw [hreq', hmaj] at hm'
    obtain ⟨hc, -, -⟩ := VExpr.mkApps_const_inj (VExpr.app.inj hm').2
    exact ⟨key, schema, owner, rule', .inl ⟨rfl, rfl⟩, hgen', hc.symm⟩
  have htypesE : ∀ t ∈ source.types, env.constants t.name = some t.toVConstant := fun t ht =>
    hconsts t.toVConstVal (List.mem_append_left _ (by rw [C.types]; exact List.mem_map_of_mem ht))
  have hsnd := V.soundAtH hF.ordered hle0
  have hfo : schema.signature.families[schema.signature.constructors[i].owner] =
      schema.signature.families[owner] :=
    congrArg (fun o : Fin schema.signature.families.size => schema.signature.families[o]) hown
  have hrigF : envF.Rigid ((compilationRestoration source aux).headName
      schema.signature.families[schema.signature.constructors[i].owner].name) := by
    rw [hfo, ← hrr]; exact hIrig
  rw [hrr] at hR ⊢
  rcases EnvTables.CaseCompilationData.ctorApp_cases C hfresh i hR with
    ⟨F, hF', hFget, c', hc', hcn, hmj⟩ | ⟨a, ha, hge, haget, c', hc', hcn, hmj⟩
  · obtain ⟨hcc, rfl, hargs⟩ := EnvTables.mkApps_const_inj hmj
    subst hcc
    have hms := (List.append_inj' hargs (by simp)).1
    have ho : schema.signature.constructors[i].owner.val < source.types.length :=
      (List.getElem?_eq_some_iff.1 hFget).1
    have hFe : F = source.types[schema.signature.constructors[i].owner.val] :=
      (Option.some.inj ((List.getElem?_eq_getElem ho).symm.trans hFget)).symm
    subst hFe
    have hFm := List.getElem_mem ho
    have hcconst : envF.constants c'.name = some c'.toVConstant :=
      hle0.constants (hconsts c' (List.mem_append_right _ (by
        rw [C.ctors]; exact List.mem_flatMap.mpr ⟨_, hFm, hc'⟩)))
    have hcis : IsCtor envF c'.name :=
      .inr (let ⟨b, s, o, r, h, hg, hc⟩ := hcisE; ⟨b, s, o, r, hle.eliminators h, hg, hc⟩)
    obtain ⟨_, _, _, _, _, hraw⟩ := C.sourceParameters
    obtain ⟨doms, result, heq, _, _, hhead, -⟩ := (hraw _ hFm c' hc').forallArity
    have hcf : CtorFam envF c'.name source.types[schema.signature.constructors[i].owner.val].name :=
      ⟨_, _, hcconst, by
        show c'.type.forallResult.getAppFnArgs.1 = _
        rw [heq, VExpr.forallResult_wrapForalls, VExpr.forallResult_of_head hhead, hhead]⟩
    have hpm := projMajor_of_entry hF C hfresh hprior hW hle0 hsnd hble htypesE i ho hrigF hc'
      hcn hcconst hcis fun info hp => by
        have hcn2 : c'.name = info.ctorName := hF.ctor_of_projFamily hp hcis hcf
        exact hsrc _ hFm info hp (by rw [← hcn2]; exact hcisE)
    obtain ⟨hfn, -, -⟩ := EnvTables.CaseCompilationData.source_slot C _ ho
    have hhd : (compilationRestoration source aux).headName
        schema.signature.families[owner].name =
        source.types[schema.signature.constructors[i].owner.val].name := by
      rw [← hfo, hfn]
      exact C.headName_source hfresh (List.mem_flatMap.mpr ⟨_, hFm, List.mem_cons_self⟩)
    obtain ⟨_, direct, _, _, hlt, hrel⟩ := EnvTables.CaseCompilationData.family_slot C
      schema.signature.constructors[i].owner
    rw [List.getElem_append_left ho] at hrel
    have hlev := hrel.resultLevel
    refine ⟨source.types[schema.signature.constructors[i].owner.val].resultLevel, ?_,
      fun levels target hlen hnz => ?_⟩
    · rw [hhd, hms, InductiveSignature.length_vars]; exact hpm
    · rw [VLevel.inst_inst, InductiveSignature.CaseSchema.genericLevels_inst hlen]
      have : (schema.sourceLevel owner levels) ≈
          (source.types[schema.signature.constructors[i].owner.val].resultLevel.inst levels) := by
        unfold CaseSchema.sourceLevel
        rw [← hown]
        exact VLevel.inst_congr_l hlev
      exact hnz.of_equiv this
  · obtain ⟨hcc, rfl, hargs⟩ := EnvTables.mkApps_const_inj hmj
    subst hcc
    have hms := (List.append_inj' hargs (by simp)).1
    obtain ⟨hhd, hlev⟩ := CaseCompilationData.aux_slot C _ hge haget
    obtain ⟨_, _, _, _, hwf, _⟩ := C.correspondence
    have hargsl : a.arguments.length = a.container.nparams := (hwf a ha).1
    have harity := CaseCompilationData.container_arity_sem C hfresh hprior hW hle0 hsnd hble htypesE
      i hrigF ha hc' hcn
    have hpmC := projMajor_container (nf := schema.signature.constructors[i].fields.length) hF hprior
      hble hle0 hpc0 V.proj ha hc' (by omega)
    refine ⟨a.source.resultLevel, ?_, fun levels target hlen hnz => ?_⟩
    · rw [← hfo, hhd, hms, List.length_map, hargsl]; exact hpmC
    · rw [VLevel.inst_inst, List.map_map]
      have e : (VLevel.inst (target :: levels) ∘ VLevel.inst schema.genericLevels) =
          VLevel.inst levels := by
        funext x
        simp only [Function.comp_apply, VLevel.inst_inst, InductiveSignature.CaseSchema.genericLevels_inst hlen]
      rw [e, ← VLevel.inst_inst]
      have : (schema.sourceLevel owner levels) ≈ ((a.source.resultLevel.inst a.levels).inst levels) := by
        unfold CaseSchema.sourceLevel
        rw [← hfo]
        exact VLevel.inst_congr_l hlev
      exact hnz.of_equiv this

end Model
end VEnv
end Lean4Lean
