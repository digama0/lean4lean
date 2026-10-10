import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.RestorationNames
import Lean4Lean.Theory.Inductive.RestorationHead
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ConstructorMajor
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! # The constructor of a rule of a compiled block

What the rigidity of pattern constructors (`VEnv.WF.patCtor_rigid`,
`Theory/Typing/HeadInjectivity/Model/WFFacts.lean`) needs from the compilation of a block: the
constructor of every rule of every recursor read off a compiled block (`VInductDecl.RecsOf`)
is a constructor of the block itself or of a container whose own ι rules are registered in the
environment the block was compiled in (`ContainersInstalled`: the container was installed by
`VEnv.addInduct`, whose rule stage registers one ι rule per constructor of the container's
recursors). The second alternative is `VEnv.IsPatCtor env ru.ctor`
(`Theory/Typing/HeadInjectivity/Rules/ConstructorMajor.lean`).

WAVE 3 COMPAT (Restoration-B): ports the source branch's `Instance.restored_equation_major`
(`RecursorEquationHeads.lean`), `CompilationData.constructor_name_cases`,
`CompilationData.constructor_equation` (`RecursorEquationCoverage.lean`), the restored-name
lemmas of `CaseRuleConstructors.lean` (`headName_source`, `headName_auxiliary_constructor`,
`directFamily_restored_constructor_names`) and `CompiledInductive.equation_major_cases`
(`ConstructorRigidity.lean`), with the stored-equation alternative replaced by a registered
pattern (`VEnv.IsPatCtor`). -/

namespace Lean4Lean

namespace VExpr

theorem lamBody_eq_stripLams : ∀ e : VExpr, e.lamBody = e.stripLams
  | .lam _ b => lamBody_eq_stripLams b
  | .bvar _ | .sort _ | .const .. | .app .. | .proj .. | .forallE .. => rfl

end VExpr

/-- The constructor major of an equation is the constructor of every rule read off it. -/
theorem VDefEq.HasConstructorMajor.ofEquation {df : VDefEq} {name : Name} {r : VRecursor}
    {ru : VRecRule} (hm : df.HasConstructorMajor name) (hof : VRecRule.OfEquation r ru df) :
    ru.ctor = name := by
  obtain ⟨fn, levels, args, hl⟩ := hm
  obtain ⟨-, -, -, major, hlast, hhead, -⟩ := hof
  rw [VExpr.lamBody_eq_stripLams, hl, VExpr.getAppArgs_app, List.getLast?_append] at hlast
  simp only [List.getLast?_singleton, Option.some_or] at hlast
  cases hlast
  simp only [VExpr.headConst?, VExpr.getAppFn_mkApps] at hhead
  exact (Option.some.inj hhead).symm

namespace InductiveSignature

theorem Restoration.expr_lam_parts {r : Restoration} {domain body restored : VExpr}
    (h : r.expr (.lam domain body) = some restored) :
    ∃ domain' body', r.expr domain = some domain' ∧ r.expr body = some body' ∧
      restored = .lam domain' body' := by
  change (do
    let domain' ← r.expr domain
    let body' ← r.expr body
    pure (.lam domain' body')) = some restored at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨domain', hd, body', hb, h⟩ := h
  exact ⟨domain', body', hd, hb, Option.some.inj h.symm⟩

/-- Restoration of a λ-telescope restores its body under a restored telescope. -/
theorem Restoration.expr_wrapLams_parts {r : Restoration} {domains : List VExpr}
    {e out : VExpr} (h : r.expr (VExpr.wrapLams domains e) = some out) :
    ∃ domains' e', r.expr e = some e' ∧ out = VExpr.wrapLams domains' e' := by
  induction domains generalizing out with
  | nil => exact ⟨[], out, h, rfl⟩
  | cons d ds ih =>
    obtain ⟨d', b', -, hb, rfl⟩ := Restoration.expr_lam_parts h
    obtain ⟨ds', e', he, rfl⟩ := ih hb
    exact ⟨d' :: ds', e', he, rfl⟩

/-- The restored equation of constructor `index` has the restored constructor as the head of
its major argument. -/
theorem Instance.restored_equation_major {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {equation : VDefEq}
    (hrestore : (compilationRestoration source auxiliaries).equation
      (g.equation index) = some equation) :
    equation.HasConstructorMajor
      ((compilationRestoration source auxiliaries).headName s.constructors[index].name) := by
  let r := compilationRestoration source auxiliaries
  obtain ⟨hl, -, -⟩ := Restoration.equation_parts hrestore
  let ctor := s.constructors[index]
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra ctor.fields.length
  let preArgs := vars (s.params.length + extra) ctor.fields.length ++ indices
  let head := g.recursorHead .recursor ctor.owner
  change r.expr (VExpr.wrapLams domains
    (VExpr.mkApps head (preArgs ++ [g.constructorApp ctor extra 0]))) = some equation.lhs at hl
  obtain ⟨ds', lhs', hl', heq⟩ := Restoration.expr_wrapLams_parts hl
  simp only [VExpr.mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil] at hl'
  change (do let major' ← r.expr (g.constructorApp ctor extra 0)
             Restoration.expr.go r (VExpr.mkApps head preArgs) [major']) = some lhs' at hl'
  simp only [bind, Option.bind_eq_some_iff] at hl'
  obtain ⟨major', hmajor, hfn⟩ := hl'
  obtain ⟨ctorArgs, rfl⟩ := r.const_mkApps_exact hmajor
  rw [restoration_mkApps] at hfn
  simp only [bind, Option.bind_eq_some_iff] at hfn
  obtain ⟨args, _, hout⟩ := hfn
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using H.heads_not_recursors ctor.owner spec hs
  have hlhs : lhs' = .app
      (VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner))
        (VLevel.params g.uvars)) args)
      (VExpr.mkApps (.const (r.headName ctor.name) (r.headLevels ctor.name g.levels))
        ctorArgs) := by
    simpa [head, Instance.recursorHead, Restoration.expr.go, hnone, VExpr.mkApps,
      List.foldl_append] using hout.symm
  refine ⟨VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner))
    (VLevel.params g.uvars)) args, r.headLevels ctor.name g.levels, ctorArgs, ?_⟩
  rw [heq, VExpr.stripLams_wrapLams, hlhs]
  rfl

theorem Restoration.headName_of_mem {r : Restoration} (hr : r.Scoped)
    (hmem : spec ∈ r.heads) : r.headName spec.auxiliary = spec.target := by
  unfold headName
  cases hf : r.heads.find? (fun h => h.auxiliary == spec.auxiliary) with
  | none =>
    have hfalse := List.find?_eq_none.mp hf spec hmem
    simp at hfalse
  | some found =>
    have hfound := List.mem_of_find?_eq_some hf
    have hname : found.auxiliary = spec.auxiliary := by
      simpa using List.find?_some hf
    have heq := List.eq_of_mem_of_nodup_map hr.1 hfound hmem hname
    cases heq
    rfl

theorem CompilationData.headName_source
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).headName name = name := by
  unfold Restoration.headName
  cases hf : (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == name) with
  | some found =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : found.auxiliary = name := by simpa using List.find?_some hf
    exact (H.toCaseCompilationData.source_head_disjoint hname (List.mem_map.mpr ⟨found, hm, hn⟩)).elim
  | none =>
    unfold Restoration.recursorName
    cases hr : (compilationRestoration source auxiliaries).recursors.find?
        (fun p => p.1 == name) with
    | none => rfl
    | some pair =>
      have hm := List.mem_of_find?_eq_some hr
      have hn : pair.1 = name := by simpa using List.find?_some hr
      have hrec := H.recursor_source_mem hm
      rw [hn] at hrec
      exact (H.source_recursors_disjoint hname hrec).elim

theorem CaseCompilationData.headName_auxiliary_constructor
    {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (ha : a ∈ auxiliaries) (hc : ctor ∈ a.source.ctors) :
    (compilationRestoration source auxiliaries).headName (a.constructorName ctor) =
      ctor.name := by
  apply Restoration.headName_of_mem H.restorationScoped (spec := {
    auxiliary := a.constructorName ctor, uvars := source.uvars, nparams := source.nparams,
    target := ctor.name, levels := a.levels, arguments := a.arguments })
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, List.mem_cons_of_mem _ ?_⟩
  exact List.mem_map.mpr ⟨ctor, hc, rfl⟩

theorem CaseCompilationData.directFamily_restored_constructor_names
    {s : InductiveSignature} {params : List VExpr}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (ha : a ∈ auxiliaries) (hd : a.specializedFamily U params = some direct) :
    direct.ctors.map
        (fun ctor => (compilationRestoration source auxiliaries).headName ctor.name) =
      a.source.ctors.map (·.name) := by
  have hnames := a.directFamily_heads hd
  simp only [ContainerSpecialization.heads, List.map_cons, List.cons.injEq,
    List.map_map, Function.comp_def] at hnames
  change List.map ((compilationRestoration source auxiliaries).headName ∘ VConstVal.name) _ = _
  rw [← List.map_map, ← hnames.2, List.map_map]
  apply List.map_congr_left
  intro ctor hc
  exact H.headName_auxiliary_constructor ha hc

/-- The restored constructor name of constructor `index` is a constructor of the source
declaration or of the container family of one of the auxiliaries. -/
theorem CompilationData.constructor_name_cases {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) :
    (∃ ctor ∈ source.constructorConstants,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name =
        ctor.name) ∨
    (∃ a ∈ auxiliaries, ∃ ctor ∈ a.source.ctors,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name =
        ctor.name) := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
    (s.declarationFamily_mem s.constructors[index].owner)
  obtain ⟨ctor, hctor, hrelctor⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
    (s.declarationCtor_family index)
  have hname : s.constructors[index].name = ctor.name := hrelctor.1
  rcases List.mem_append.mp hfamily with hfamily | hfamily
  · left
    refine ⟨ctor, List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩, ?_⟩
    rw [hname]
    apply H.headName_source
    exact List.mem_flatMap.mpr ⟨family, hfamily, List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) _ hfamily
    have hm : (compilationRestoration source auxiliaries).headName ctor.name ∈
        a.source.ctors.map (·.name) := by
      rw [← H.toCaseCompilationData.directFamily_restored_constructor_names ha hdf]
      exact List.mem_map.mpr ⟨ctor, hctor, rfl⟩
    obtain ⟨original, horiginal, hrestored⟩ := List.mem_map.mp hm
    exact ⟨a, ha, original, horiginal, by rw [hname]; exact hrestored.symm⟩

theorem declarationCtor_index_of_mem (s : InductiveSignature)
    (hctor : ctor ∈ s.declaration.constructorConstants) :
    ∃ index : Fin s.constructors.size, s.declarationCtor index = ctor := by
  obtain ⟨family, hfamily, hctor⟩ := List.mem_flatMap.mp hctor
  obtain ⟨⟨family, owner⟩, howner, rfl⟩ := List.mem_map.mp hfamily
  obtain ⟨sigctor, hsigctor, hvalue⟩ := List.mem_filterMap.mp hctor
  split at hvalue
  · have hvalue := Option.some.inj hvalue
    obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hsigctor
    refine ⟨⟨index, by simpa using hindex⟩, ?_⟩
    simpa only [declarationCtor, ← hget, Array.getElem_toList, Fin.getElem_fin] using hvalue
  · cases hvalue

theorem CompilationData.source_constructor_index
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (hctor : ctor ∈ source.constructorConstants) :
    ∃ index : Fin s.constructors.size,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name =
        ctor.name := by
  obtain ⟨family, hfamily, hctor⟩ := List.mem_flatMap.mp hctor
  obtain ⟨envTypes, direct, _, _, _, hfamilies⟩ := H.correspondence
  obtain ⟨normalized, hnormalized, hrestored⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hfamilies family (List.mem_append_left _ hfamily)
  obtain ⟨normalizedCtor, hnormalizedCtor, hctorRestore⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hrestored.constructors ctor hctor
  obtain ⟨index, hindex⟩ := s.declarationCtor_index_of_mem
    (List.mem_flatMap.mpr ⟨normalized, hnormalized, hnormalizedCtor⟩)
  have hname : s.constructors[index].name = ctor.name := by
    exact (congrArg VConstVal.name hindex).trans hctorRestore.1
  refine ⟨index, ?_⟩
  rw [hname]
  apply H.headName_source
  exact List.mem_flatMap.mpr ⟨family, hfamily,
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩

/-- Every source constructor has its own restored equation in the block. -/
theorem CompilationData.constructor_equation
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (hctor : ctor ∈ source.constructorConstants) :
    ∃ equation ∈ block.rules, equation.HasConstructorMajor ctor.name := by
  obtain ⟨index, hname⟩ := H.source_constructor_index hctor
  have hgenerated : g.equation index ∈ g.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨equation, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp H.equations) _ hgenerated
  have hmajor := g.restored_equation_major H index hrestore
  rw [hname] at hmajor
  exact ⟨equation, hmem, hmajor⟩

end InductiveSignature

/-- Every source constructor of a compiled block has an equation of the block on it. -/
theorem CompiledInductive.constructor_equation {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block) :
    ∀ ctor ∈ source.constructorConstants, ∃ equation ∈ block.rules,
      equation.HasConstructorMajor ctor.name := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source block _ => ∀ ctor ∈ source.constructorConstants,
      ∃ equation ∈ block.rules, equation.HasConstructorMajor ctor.name)
    (motive_2 := fun _ _ _ => True)
    (fun data _ _ _ hctor => data.constructor_equation hctor)
    (fun _ _ _ ih => ih) trivial (fun _ _ _ _ _ _ _ _ => trivial) H

/-- Every constructor of a container of an installed specialization list is the constructor of
a registered ι rule: the container's recursor has a rule on it, and the container was installed
by `VEnv.addInduct` below `env`. -/
theorem ContainersInstalled.constructor_isPatCtor {env : VEnv}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    (H : ContainersInstalled env auxiliaries) {a : InductiveSignature.ContainerSpecialization}
    (ha : a ∈ auxiliaries) {ctor : VConstVal} (hc : ctor ∈ a.source.ctors) :
    VEnv.IsPatCtor env ctor.name := by
  induction auxiliaries generalizing env with
  | nil => cases ha
  | cons a' rest ih =>
    cases H with
    | @cons _ _ _ base block installed hcompile _ hrecs hinstall hle hrest =>
    rcases List.mem_cons.mp ha with rfl | ha
    · have hsource : ctor ∈ a.container.constructorConstants :=
        List.mem_flatMap.mpr ⟨a.source, List.getElem_mem a.family.isLt, hc⟩
      obtain ⟨df, hdf, hmajor⟩ := hcompile.constructor_equation ctor hsource
      obtain ⟨r, hr, ru, hru, hof⟩ := hrecs.rules_total df hdf
      have hname := hmajor.ofEquation hof
      obtain ⟨_, _, _, _, _, _, hR⟩ := VEnv.addInduct_stages hinstall
      have hclosed := VEnv.addRules_closed hR r hr ru hru
      refine ⟨_, _, r.name, r.getMajorIdx, ru.ctorParams + ru.nfields,
        hle.pats (VEnv.addInduct_pat hr hru hclosed hinstall), ?_⟩
      rw [hname]
    · exact ih hrest ha

/-- The constructor majors of the equations of a compiled block: a constructor of the block, or
the constructor of a ι rule registered in the compilation environment (a container's). -/
theorem CompiledInductive.equation_major_cases {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block) :
    ∀ df ∈ block.rules, ∃ name, df.HasConstructorMajor name ∧
      ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨ VEnv.IsPatCtor env name) := by
  exact CompiledInductive.rec
    (motive_1 := fun env source block _ =>
      ∀ df ∈ block.rules, ∃ name, df.HasConstructorMajor name ∧
        ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨ VEnv.IsPatCtor env name))
    (motive_2 := fun _ _ _ => True)
    (fun hdata hprior _ df hdf => by
      obtain ⟨generated, hgenerated, hrestored⟩ := Lean4Lean.List.Forall₂.forall_exists_r
        (List.mapM_eq_some.mp hdata.equations) _ hdf
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp hgenerated
      refine ⟨_, InductiveSignature.Instance.restored_equation_major hdata index hrestored, ?_⟩
      rcases hdata.constructor_name_cases index with ho | ⟨a, ha, ctor, hc, he⟩
      · exact Or.inl ho
      · right
        rw [he]
        exact hprior.constructor_isPatCtor ha hc)
    (fun _ hle _ ih df hdf => by
      obtain ⟨name, hm, ho | ⟨p, rr, recN, M, N, hp, hpe⟩⟩ := ih df hdf
      · exact ⟨name, hm, Or.inl ho⟩
      · exact ⟨name, hm, Or.inr ⟨p, rr, recN, M, N, hle.pats hp, hpe⟩⟩)
    trivial (fun _ _ _ _ _ _ _ _ => trivial) H

/-- **The constructor of every rule of a compiled block** is a constructor of the block or the
constructor of a ι rule already registered in the compilation environment (the container's). -/
theorem CompiledInductive.rule_ctor_cases {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (H : CompiledInductive env source block)
    (hrecs : source.RecsOf block) {r : VRecursor} {ru : VRecRule} (hr : r ∈ source.recs)
    (hru : ru ∈ r.rules) :
    (∃ ctor ∈ source.constructorConstants, ru.ctor = ctor.name) ∨ VEnv.IsPatCtor env ru.ctor := by
  obtain ⟨df, hdf, hof⟩ := hrecs.rules r hr ru hru
  obtain ⟨name, hm, hcases⟩ := H.equation_major_cases df hdf
  rw [hm.ofEquation hof]
  exact hcases

end Lean4Lean
