import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Inductive.CompilationNames

/-! Deterministic constructor selection for generated abstract case rules. -/

namespace Lean4Lean.InductiveSignature

/-- The name restoration gives a head constant: the target of an auxiliary head, otherwise the
renamed recursor name (`recursorName`). This records only the name;
the level and parameter substitutions are still computed by restoration. -/
def Restoration.headName (r : Restoration) (name : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == name) with
  | some h => h.target
  | none => r.recursorName name

theorem Restoration.const_spine {r : Restoration} {output : VExpr}
    (h : Restoration.expr.go r (.const name levels) args = some output) :
    ∃ levels' args', output = VExpr.mkApps (.const (r.headName name) levels') args' := by
  unfold Restoration.expr.go at h
  unfold headName
  split at h
  · rename_i spec hspec
    rw [hspec]
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · cases h
      exact ⟨_, _, rfl⟩
  · rename_i hspec
    rw [hspec]
    cases h
    exact ⟨_, _, rfl⟩

theorem Restoration.const_mkApps {r : Restoration} {output : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) args) = some output) :
    ∃ levels' args', output = VExpr.mkApps (.const (r.headName name) levels') args' := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) args) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨args', _, h⟩ := h
  exact r.const_spine h

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
    exact (H.source_head_disjoint hname (List.mem_map.mpr ⟨found, hm, hn⟩)).elim
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

theorem CaseCompilationData.headName_source
    {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (hdisj : RecursorNamesFresh env source expanded auxiliaries)
    (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).headName name = name := by
  unfold Restoration.headName
  cases hf : (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == name) with
  | some found =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : found.auxiliary = name := by simpa using List.find?_some hf
    exact (H.source_head_disjoint hname (List.mem_map.mpr ⟨found, hm, hn⟩)).elim
  | none =>
    unfold Restoration.recursorName
    cases hr : (compilationRestoration source auxiliaries).recursors.find?
        (fun p => p.1 == name) with
    | none => rfl
    | some pair =>
      have hm := List.mem_of_find?_eq_some hr
      have hn : pair.1 = name := by simpa using List.find?_some hr
      have hs : pair.1 ∈ source.sourceNames := by
        rw [hn]
        have := (familyNames_perm source.types).mem_iff.mp hname
        simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
          VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
          using this
      exact ((hdisj _ (List.mem_map.mpr ⟨pair, hm, rfl⟩)).2.1 hs).elim

theorem CaseCompilationData.headName_auxiliary_constructor
    {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (ha : a ∈ auxiliaries) (hc : ctor ∈ a.source.ctors) :
    (compilationRestoration source auxiliaries).headName (a.constructorName ctor) = ctor.name := by
  apply Restoration.headName_of_mem H.restorationScoped (spec := {
    auxiliary := a.constructorName ctor, uvars := source.uvars, nparams := source.nparams,
    target := ctor.name, levels := a.levels, arguments := a.arguments })
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, List.mem_cons_of_mem _ ?_⟩
  exact List.mem_map.mpr ⟨ctor, hc, rfl⟩

open CaseSchema in
/-- The parser's constructor tag is the restored name of the constructor
selected by the generator. It cannot be chosen independently by a match. -/
theorem Instance.parsed_constructor {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size) {r : Restoration} {equation : VDefEq}
    {rule : AppliedRule}
    (hrestore : r.equation (g.equation index (.elim block firstOwner)) = some equation)
    (hparse : AppliedRule.extract key owner equation = some rule) :
    rule.application.ctorName = r.headName s.constructors[index].name := by
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨domains', lhs', rhs', type', hl', _, _, hel, her, het, _⟩ :=
    restored_common_telescope hl hr ht
  let ctor := s.constructors[index]
  let extra := s.families.size + s.constructors.size
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra ctor.fields.length
  let preArgs := vars (s.params.length + extra) ctor.fields.length ++ indices
  let head := g.recursorHead (.elim block firstOwner) ctor.owner
  change r.expr (VExpr.mkApps head (preArgs ++ [g.constructorApp ctor extra 0])) = some lhs' at hl'
  simp only [VExpr.mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil] at hl'
  change (do let major' ← r.expr (g.constructorApp ctor extra 0)
             Restoration.expr.go r (VExpr.mkApps head preArgs) [major']) = some lhs' at hl'
  simp only [bind, Option.bind_eq_some_iff] at hl'
  obtain ⟨major', hmajor, hfn⟩ := hl'
  obtain ⟨ctorLevels, ctorArgs, rfl⟩ := r.const_mkApps hmajor
  rw [restoration_mkApps] at hfn
  simp only [bind, Option.bind_eq_some_iff] at hfn
  obtain ⟨args, _, hout⟩ := hfn
  have hlhs : lhs' = .app (VExpr.mkApps head args)
      (VExpr.mkApps (.const (r.headName ctor.name) ctorLevels) ctorArgs) := by
    simpa [head, Instance.recursorHead, Restoration.expr.go, VExpr.mkApps,
      List.foldl_append] using hout.symm
  have hhead : lhs'.getAppFnArgs.1 =
      .elim block (firstOwner + ctor.owner.val) (g.targetLevel :: g.levels) := by
    rw [hlhs, VExpr.getAppFnArgs_app, spine_mkApps_exact _ _ (by rfl)]
    rfl
  have hbody := extract_wrap (rhs := rhs') (type := type') hhead domains'
  rw [← hel, ← her, ← het] at hbody
  have hspec := AppliedRule.extract_spec hparse
  have heq := Option.some.inj (hspec.2.1.symm.trans hbody)
  have happ := hspec.2.2.1
  rw [heq] at happ
  simp only at happ
  rw [hlhs] at happ
  simp only [Application.extract,
    spine_mkApps_exact (.elim block (firstOwner + ctor.owner.val) (g.targetLevel :: g.levels)) args rfl,
    spine_mkApps_exact (.const (r.headName ctor.name) ctorLevels) ctorArgs rfl,
    head, Instance.recursorHead, Option.some.injEq] at happ
  exact congrArg (fun a : Application => a.ctorName) happ.symm

namespace CaseSchema

theorem directFamily_restored_constructor_names
    {s : InductiveSignature}
    {params : List VExpr}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (ha : a ∈ auxiliaries) (hd : a.specializedFamily U params = some direct) :
    direct.ctors.map (fun ctor => (compilationRestoration source auxiliaries).headName ctor.name) =
      a.source.ctors.map (·.name) := by
  have hnames := a.directFamily_heads hd
  simp only [ContainerSpecialization.heads, List.map_cons, List.cons.injEq,
    List.map_map, Function.comp_def] at hnames
  change List.map ((compilationRestoration source auxiliaries).headName ∘ VConstVal.name) _ = _
  rw [← List.map_map, ← hnames.2, List.map_map]
  apply List.map_congr_left
  intro ctor hc
  exact H.headName_auxiliary_constructor ha hc

private theorem family_ctorNames_nodup {decl : VInductDecl}
    (H : decl.sourceNames.Nodup) (hf : family ∈ decl.types) :
    (family.ctors.map (·.name)).Nodup := by
  have hnd := familyNames_nodup H
  have hfamily := (List.pairwise_flatMap.mp hnd).1 family hf
  exact (List.nodup_cons.mp hfamily).2

end CaseSchema

end Lean4Lean.InductiveSignature

namespace Lean4Lean

theorem ContainersInstalled.container_names (H : ContainersInstalled env auxiliaries) :
    ∀ a ∈ auxiliaries, a.container.sourceNames.Nodup := by
  exact ContainersInstalled.rec
    (motive_1 := fun _ source _ _ => source.sourceNames.Nodup)
    (motive_2 := fun _ auxiliaries _ => ∀ a ∈ auxiliaries, a.container.sourceNames.Nodup)
    (fun data _ _ => data.sourceWF.2.1)
    (fun _ _ _ ih => ih)
    (by simp)
    (fun _ _ _ _ _ hc hr => by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hc
      · exact hr a ha)
    H

end Lean4Lean

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- Every certified family has a duplicate-free list of restored constructor
names. Auxiliary names are restored to constructors of their certified prior
container; source constructor names are unchanged. -/
theorem Certified.constructor_names_nodup {schema : CaseSchema}
    (H : schema.Certified base source block)
    (owner : Fin schema.signature.families.size) :
    ((schema.view owner).constructors.toList.map
      (fun ctor => schema.restoration.headName ctor.name)).Nodup := by
  obtain ⟨expanded, auxiliaries, hdata, hprior, hr, _, hdisj⟩ := H
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := hdata.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
    (schema.signature.declarationFamily_mem owner)
  have hnames := ctorNames_eq_of_forall₂ hrel.constructors (fun _ _ h => h.1)
  change (List.map (schema.restoration.headName ∘ fun c => c.name)
    (schema.view owner).constructors.toList).Nodup
  rw [← List.map_map, view_constructor_names, hnames, hr, List.map_map]
  simp only [Function.comp_def]
  rcases List.mem_append.mp hfamily with hfamily | hfamily
  · have heq : family.ctors.map (fun ctor =>
        (compilationRestoration source auxiliaries).headName ctor.name) =
        family.ctors.map (·.name) := by
      apply List.map_congr_left
      intro ctor hc
      apply hdata.headName_source hdisj
      exact List.mem_flatMap.mpr ⟨family, hfamily, List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨ctor, hc, rfl⟩)⟩
    rw [heq]
    exact family_ctorNames_nodup hdata.sourceWF.2.1 hfamily
  · obtain ⟨a, ha, hfamily⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) _ hfamily
    rw [directFamily_restored_constructor_names hdata ha hfamily]
    exact family_ctorNames_nodup (hprior.container_names a ha)
      (List.getElem_mem a.family.isLt)

/-- Once restored constructor names are distinct, a constructor name
selects exactly one generated case rule. `Certified.generated_unique` below
establishes the distinctness from the case certificate. -/
theorem Generates.unique_of_names {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {left right : AppliedRule}
    (hnames : ((schema.view owner).constructors.toList.map
      (fun ctor => schema.restoration.headName ctor.name)).Nodup)
    (hleft : schema.Generates block owner left)
    (hright : schema.Generates block owner right)
    (hctor : left.application.ctorName = right.application.ctorName) : left = right := by
  obtain ⟨leftRules, hleftRules, hleftMem, hleftParse⟩ := hleft
  obtain ⟨rightRules, hrightRules, hrightMem, hrightParse⟩ := hright
  obtain ⟨i, hi⟩ := equation_of_mem hleftRules hleftMem
  obtain ⟨j, hj⟩ := equation_of_mem hrightRules hrightMem
  have hnameLeft := Instance.parsed_constructor _ i hi hleftParse
  have hnameRight := Instance.parsed_constructor _ j hj hrightParse
  have heq : i = j := by
    apply Fin.ext
    apply (List.getElem_inj (h₀ := by simpa only [List.length_map, Array.length_toList] using i.isLt)
      (h₁ := by simpa only [List.length_map, Array.length_toList] using j.isLt) hnames).mp
    simpa only [List.getElem_map, Array.getElem_toList, Fin.getElem_fin] using
      hnameLeft.symm.trans (hctor.trans hnameRight)
  cases heq
  have heq : left.equation = right.equation := Option.some.inj (hi.symm.trans hj)
  rw [heq] at hleftParse
  exact Option.some.inj (hleftParse.symm.trans hrightParse)

/-- The case certificate makes constructor selection deterministic without
assuming any matching or confluence property from a caller. -/
theorem Certified.generated_unique {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {left right : AppliedRule}
    (H : schema.Certified base source sourceBlock)
    (hleft : schema.Generates block owner left)
    (hright : schema.Generates block owner right)
    (hctor : left.application.ctorName = right.application.ctorName) : left = right :=
  hleft.unique_of_names (H.constructor_names_nodup owner) hright hctor

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean

theorem VEnv.WF.case_rule_unique {env : VEnv} (H : env.WF)
    (hregistered : env.eliminators block schema)
    {owner : Fin schema.signature.families.size}
    (hleft : schema.Generates block owner left)
    (hright : schema.Generates block owner right)
    (hctor : left.application.ctorName = right.application.ctorName) : left = right := by
  obtain ⟨_, _, _, _, _, hformed, _, _⟩ := H.eliminator_installed hregistered
  exact hformed.generated_unique hleft hright hctor

end Lean4Lean
