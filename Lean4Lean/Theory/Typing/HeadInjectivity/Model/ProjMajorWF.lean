import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CtorArity

/-! # Static facts about the majors of rules on projection-registered families

* `WF.isCtor_const`: a constructor of a rule is a declared constant.
* `WF.container_entry`: the projection entry of a projection-registered container family of a
  nested compilation is the container declaration's own entry (its family has the single
  constructor of the major): every constructor of the container family is an installed constructor
  of the well-formed environment, and a projection-registered family has only its registered
  constructor among them (`WF.ctor_of_projFamily`). -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

variable {env : VEnv}

theorem WF.installedCtor_const (H : env.WF) (h : Model.IsInstalledCtor env c) :
    ∃ ci, env.constants c = some ci := by
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp (H.ctorOf_of_installedCtor h)
  obtain ⟨ci, -, -, hci, -⟩ := EnvTables.ctorOf_shape H hk
  exact ⟨ci, hci⟩

theorem WF.caseCtor_const (H : env.WF) (h : Model.IsCaseCtor env c) :
    ∃ ci, env.constants c = some ci := by
  obtain ⟨key, schema, owner, rule, hreg, hgen, rfl⟩ := h
  obtain ⟨fn, ls, args, hm⟩ := Model.generates_major hgen
  obtain ⟨rules, hrules, hmem, -⟩ := hgen
  obtain ⟨base, source, block, _, hle, hcert, _, hconsts⟩ := H.eliminator_installed hreg
  have hcert' := hcert
  obtain ⟨expanded, aux, hdata, hprior, hr, -, hfresh⟩ := hcert'
  obtain ⟨j, -, e, _, hrestore⟩ := EnvTables.generic_major hrules hmem hm
  rw [hr] at hrestore
  rcases EnvTables.CaseCompilationData.ctorApp_cases hdata hfresh j hrestore with
    ⟨F, hF, _, c', hc', _, hmaj⟩ | ⟨a, ha, _, _, c', hc', _, hmaj⟩
  · obtain ⟨h1, -, -⟩ := EnvTables.mkApps_const_inj hmaj.symm
    rw [← h1]
    exact ⟨_, hconsts c' (List.mem_append_right _ (by
      rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))⟩
  · obtain ⟨h1, -, -⟩ := EnvTables.mkApps_const_inj hmaj.symm
    rw [← h1]
    exact ⟨_, hle.constants (hprior.container_ctor a ha c' hc').1⟩

/-- **A constructor of a rule is a declared constant.** -/
theorem WF.isCtor_const (H : env.WF) (h : Model.IsCtor env c) : ∃ ci, env.constants c = some ci :=
  h.elim H.installedCtor_const H.caseCtor_const

theorem list_eq_single_of_names {l : List VConstVal} {c : VConstVal} {k : Name}
    (hnd : (l.map (·.name)).Nodup) (hall : ∀ x ∈ l, x.name = k) (hc : c ∈ l) : l = [c] := by
  match l, hnd, hall, hc with
  | [x], _, _, hc => rw [List.mem_singleton.1 hc]
  | x :: y :: l, hnd, hall, _ =>
    exfalso
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
    exact hnd.1.1 ((hall x (by simp)).trans (hall y (by simp)).symm)

/-- Every constructor of a certified container family is an installed constructor of a later
environment. -/
theorem container_ctor_installed {base : VEnv} {aux : List ContainerSpecialization}
    (hprior : ContainersInstalled base aux) (hle : base ≤ env)
    {a : ContainerSpecialization} (ha : a ∈ aux) {c : VConstVal} (hc : c ∈ a.source.ctors) :
    Model.IsInstalledCtor env c.name := by
  obtain ⟨base', block', inst', hcomp', hinst', hle'⟩ :=
    EnvTables.ContainersInstalled.member hprior ha
  obtain ⟨b'', exp', s', g', aux', hb'', hdata', hprior'⟩ := hcomp'.exists_compilation
  have hfam_lt : a.family.val < s'.families.size :=
    Nat.lt_of_lt_of_le a.family.isLt (EnvTables.CaseCompilationData.families_size_ge hdata'.toCaseCompilationData)
  let o' : Fin s'.families.size := ⟨a.family.val, hfam_lt⟩
  have hsrc : a.container.types[o'.val] = a.source := rfl
  have hc' : c ∈ a.container.types[o'.val].ctors := by rw [hsrc]; exact hc
  obtain ⟨j, hjown, hjname⟩ :=
    (EnvTables.CaseCompilationData.source_slot hdata'.toCaseCompilationData o' a.family.isLt).2.1 c hc'
  have hjlt : s'.constructors[j].owner.val < a.container.types.length := by
    rw [hjown]; exact a.family.isLt
  obtain ⟨ρ, hρmem, hρ⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata'.equations) (g'.equation j)
    (List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩)
  have hρenv : env.defeqs ρ :=
    (hle'.trans hle).defeqs (VInductBlock.install_rule hinst' hρmem)
  have hsrc' : a.container.types[s'.constructors[j].owner.val] = a.source := by
    simp only [hjown]; rfl
  have hcj : c ∈ a.container.types[s'.constructors[j].owner.val].ctors := by
    rw [hsrc']; exact hc
  obtain ⟨Ds, idx, hρlhs⟩ := EnvTables.CompilationData.source_rule hdata' j hjlt hcj hjname.symm hρ
  exact ⟨ρ, hρenv, _, _, _, by rw [hρlhs, EnvTables.ruleBody_stripLams]⟩

/-- **The entry of a projection-registered container family** is the container declaration's
own entry, and the family has the single constructor of the major. -/
theorem WF.container_entry {base : VEnv} {aux : List ContainerSpecialization} (henv : env.WF)
    (hprior : ContainersInstalled base aux) (hle : base ≤ env)
    {a : ContainerSpecialization} (ha : a ∈ aux) {c : VConstVal} (hc : c ∈ a.source.ctors)
    {info : VProjectionInfo} (hp : env.projections a.source.name info) :
    a.source.ctors = [c] ∧
      info = ⟨a.container.uvars, a.container.nparams, a.source.numIndices,
        a.source.resultLevel, c.name, c.type⟩ := by
  have hall : ∀ c' ∈ a.source.ctors, c'.name = info.ctorName := by
    intro c' hc'
    obtain ⟨h1, ls, h2⟩ := hprior.container_ctor a ha c' hc'
    exact henv.ctor_of_projFamily hp (.inl (container_ctor_installed hprior hle ha hc'))
      ⟨_, ls, hle.constants h1, h2⟩
  obtain ⟨base', block', inst', hcomp', hinst', hle'⟩ :=
    EnvTables.ContainersInstalled.member hprior ha
  obtain ⟨b'', exp', s', g', aux', hb'', hdata', hprior'⟩ := hcomp'.exists_compilation
  have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
  have hnd := EnvTables.sourceNames_ctors_nodup hdata'.sourceWF.2.1 hsrc
  have hone := list_eq_single_of_names hnd hall hc
  refine ⟨hone, ?_⟩
  have hmem := VInductDecl.mem_projectionEntries hsrc hone
  have hin : inst'.projections a.source.name ⟨a.container.uvars, a.container.nparams,
      a.source.numIndices, a.source.resultLevel, c.name, c.type⟩ :=
    (EnvTables.install_projections hinst').2 (.inl ⟨_, by rw [hdata'.projections]; exact hmem,
      rfl, rfl⟩)
  exact henv.ordered.projections_unique hp ((hle'.trans hle).projections hin)

/-- The major of a generic case equation, at the view constructor `index` of its registered schema: the
restoration of the case form of a signature constructor. (`EnvTables.generic_major` at
a given equation index.) -/
theorem generic_major_at {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {index : Fin (schema.view owner).constructors.size} {key : Name} {df : VDefEq}
    {fn major : VExpr}
    (hrestore : schema.restoration.equation ((schema.specialize owner schema.genericUvars
      schema.genericLevels (.param 0)).equation index (.elim key owner.val)) = some df)
    (hm : df.lhs.stripLams = .app fn major) :
    ∃ j : Fin schema.signature.constructors.size, schema.signature.constructors[j].owner = owner ∧
      (schema.view owner).constructors[index] = schema.caseConstructor schema.signature.constructors[j] ∧
      ∃ e, 1 ≤ e ∧ schema.restoration.expr (VExpr.mkApps
        (.const schema.signature.constructors[j].name schema.genericLevels)
        (vars schema.signature.params.length (e + schema.signature.constructors[j].fields.length) ++
          vars schema.signature.constructors[j].fields.length 0)) = some major := by
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
  have hmaj : major' = major := (VExpr.app.inj hm).2
  obtain ⟨sc, hsc, hown, hview⟩ := CaseSchema.view_constructor_eq_caseConstructor index
  obtain ⟨jn, hjn, hjget⟩ := List.mem_iff_getElem.mp hsc
  let j : Fin schema.signature.constructors.size := ⟨jn, by simpa using hjn⟩
  have hj : schema.signature.constructors[j] = sc := by simpa [j] using hjget
  refine ⟨j, by rw [hj, hown], by rw [hj]; exact hview, extra, by simp [extra], ?_⟩
  rw [← hmaj, ← hmajor]
  change _ = schema.restoration.expr (VExpr.mkApps (.const ctor.name g.levels)
    (vars (schema.view owner).params.length (extra + ctor.fields.length + 0) ++
      vars ctor.fields.length 0))
  have hc : ctor = schema.caseConstructor sc := hview
  rw [hc, hj]
  simp [CaseSchema.caseConstructor, fieldTypes, CaseSchema.view, g, CaseSchema.specialize]

end VEnv
end Lean4Lean
