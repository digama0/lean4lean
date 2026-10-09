import Lean4Lean.Theory.Typing.EnvTables.Majors

/-!
# Majors of generic eliminator-schema equations

The schema's own view of a family can disagree with the recorded one (see the counterexample in
`EnvTables/OfWF.lean`), so for schema equations the constructor data are given in the schema's own
view; the table agrees with it unless the family was recorded first with a different
parameter count or without the constructor.
-/

namespace Lean4Lean.EnvTables
open _root_.Lean4Lean.EnvTables.VEnv InductiveSignature

/-- Restoration of the constructor application of a signature constructor. -/
theorem CaseCompilationData.ctorApp_cases {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CaseCompilationData base src exp s aux block)
    (hrfresh : RecursorNamesFresh base src exp aux)
    (j : Fin s.constructors.size) {lv : List VLevel} {e : Nat} {major : VExpr}
    (hr : (compilationRestoration src aux).expr (VExpr.mkApps (.const s.constructors[j].name lv)
      (vars s.params.length (e + s.constructors[j].fields.length) ++
        vars s.constructors[j].fields.length 0)) = some major) :
    (∃ F ∈ src.types, src.types[s.constructors[j].owner.val]? = some F ∧
        ∃ c ∈ F.ctors, c.name = s.constructors[j].name ∧
        major = VExpr.mkApps (.const c.name lv)
          (vars s.params.length (e + s.constructors[j].fields.length) ++
            vars s.constructors[j].fields.length 0)) ∨
    (∃ a ∈ aux, src.types.length ≤ s.constructors[j].owner.val ∧
        aux[s.constructors[j].owner.val - src.types.length]? = some a ∧
        ∃ c ∈ a.source.ctors, s.constructors[j].name = a.constructorName c ∧
        major = VExpr.mkApps (.const c.name (a.levels.map (·.inst lv)))
          (a.arguments.map (fun arg => instantiateParams (arg.instL lv)
            (vars s.params.length (e + s.constructors[j].fields.length))) ++
            vars s.constructors[j].fields.length 0)) := by
  have hparams : ∀ h ∈ (compilationRestoration src aux).heads, h.nparams = s.params.length := by
    intro h hh
    rw [compilationRestoration_nparams h hh, ← hdata.nparams, ← hdata.model.nparams]
  have hmaj := restored_ctorApp hparams hr
  by_cases ho : s.constructors[j].owner.val < src.types.length
  · obtain ⟨_, _, hctors⟩ := CaseCompilationData.source_slot hdata _ ho
    obtain ⟨c, hc, hcn⟩ := hctors j rfl
    have hF := List.getElem_mem (l := src.types) ho
    have hcn' : c.name ∈ familyNames src.types :=
      List.mem_flatMap.mpr ⟨_, hF, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
    left
    refine ⟨_, hF, List.getElem?_eq_getElem ho, c, hc, hcn, ?_⟩
    rcases hmaj with ⟨hnone, rfl⟩ | ⟨spec, hspec, hsome, _, _⟩
    · have hhn := hdata.headName_source hrfresh hcn'
      unfold Restoration.headName at hhn
      rw [hcn, hnone] at hhn
      simp only at hhn
      rw [hhn, hcn]
    · exfalso
      have : spec.auxiliary = c.name := by
        rw [hcn]; simpa using List.find?_some hsome
      exact hdata.source_head_disjoint hcn' (List.mem_map.mpr ⟨spec, hspec, this⟩)
  · right
    obtain ⟨envTypes, direct, _, hdirect, hlt, hrel⟩ :=
      CaseCompilationData.family_slot hdata s.constructors[j].owner
    have ho' : src.types.length ≤ s.constructors[j].owner.val := by omega
    have hlt2 : s.constructors[j].owner.val < src.types.length + direct.length := by
      simpa using hlt
    rw [List.getElem_append_right ho'] at hrel
    have hrel' := List.mapM_eq_some.mp hdirect
    have hlen := Lean4Lean.List.Forall₂.length_eq hrel'
    have hjb : s.constructors[j].owner.val - src.types.length < aux.length := by omega
    obtain ⟨_, hdf⟩ := List.forall₂_getElem_exists hrel' (s.constructors[j].owner.val - src.types.length) hjb
    have ha := List.getElem_mem hjb
    obtain ⟨dc, hdc, hdcn, _⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
      (s.declarationCtor_family j)
    obtain ⟨c, hc, t, _, hdcname, _⟩ := directFamily_ctor hdf hdc
    have hjn : s.constructors[j].name = _ := hdcn.trans hdcname
    refine ⟨_, ha, ho', List.getElem?_eq_getElem hjb, c, hc, hjn, ?_⟩
    have hhead := auxCtor_head_mem (src := src) ha hc
    rcases hmaj with ⟨hnone, _⟩ | ⟨spec, hspec, hsome, _, rfl⟩
    · exfalso
      have := List.find?_eq_none.mp hnone _ hhead
      simp at this
      exact this hjn.symm
    · have hsa : spec.auxiliary =
          aux[s.constructors[j].owner.val - src.types.length].constructorName c := by
        rw [← hjn]; simpa using List.find?_some hsome
      have := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1 hspec hhead hsa
      subst this
      rfl

/-- The major of a generic case equation. -/
theorem generic_major
    {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (hgen : schema.genericEquations key owner = some rules) (hdf : df ∈ rules)
    (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ∃ j : Fin schema.signature.constructors.size, schema.signature.constructors[j].owner = owner ∧
      ∃ e, 1 ≤ e ∧ schema.restoration.expr (VExpr.mkApps
        (.const schema.signature.constructors[j].name schema.genericLevels)
        (vars schema.signature.params.length (e + schema.signature.constructors[j].fields.length) ++
          vars schema.signature.constructors[j].fields.length 0)) =
        some (VExpr.mkApps (.const c ls) args) := by
  obtain ⟨index, hrestore⟩ := CaseSchema.equation_of_mem hgen hdf
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨ds', lhs', _, _, hl', _, _, hel, _, _, _⟩ := restored_common_telescope hl hr ht
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let nf := ctor.fields.length
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let np := (schema.view owner).params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  change schema.restoration.expr (VExpr.mkApps _ (vars np nf ++ indices ++
    [g.constructorApp ctor extra 0])) = some lhs' at hl'
  change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hl'
  rw [restoration_mkApps] at hl'
  simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, List.mapM_cons, List.mapM_nil, bind,
    Option.bind_eq_some_iff, pure, Option.some.injEq] at hl'
  obtain ⟨_, ⟨_, ⟨_, rfl, idx', _, rfl⟩, _, ⟨major', hmajor, _, rfl, rfl⟩, rfl⟩, hout⟩ := hl'
  simp only [List.append_nil, Instance.recursorHead, Restoration.expr.go,
    Option.some.injEq] at hout
  rw [hel, VExpr.stripLams_wrapLams, ← hout, VExpr.mkApps_snoc] at hm
  have hmaj : major' = VExpr.mkApps (.const c ls) args := (VExpr.app.inj hm).2
  obtain ⟨sc, hsc, hown, hview⟩ := CaseSchema.view_constructor_eq_caseConstructor index
  obtain ⟨jn, hjn, hjget⟩ := List.mem_iff_getElem.mp hsc
  let j : Fin schema.signature.constructors.size := ⟨jn, by simpa using hjn⟩
  have hj : schema.signature.constructors[j] = sc := by simpa [j] using hjget
  refine ⟨j, by rw [hj, hown], extra, by simp [extra], ?_⟩
  rw [← hmaj, ← hmajor]
  change _ = schema.restoration.expr (VExpr.mkApps (.const ctor.name g.levels)
    (vars (schema.view owner).params.length (extra + ctor.fields.length + 0) ++
      vars ctor.fields.length 0))
  have hc : ctor = schema.caseConstructor sc := hview
  rw [hc, hj]
  simp [CaseSchema.caseConstructor, fieldTypes, CaseSchema.view, g, CaseSchema.specialize]

end Lean4Lean.EnvTables
