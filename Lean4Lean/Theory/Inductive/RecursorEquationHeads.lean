import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.StoredRuleHeads

/-! Constructor heads of restored iota equations: each is the restored name of a constructor of
the source declaration or of a container. -/

namespace Lean4Lean.InductiveSignature

private theorem stripLams_wrap (domains : List VExpr) (e : VExpr) :
    (VExpr.wrapLams domains e).stripLams = e.stripLams := by
  induction domains with
  | nil => rfl
  | cons d ds ih => exact ih

/-- Restoration preserves the final major argument of a generated
recursor equation; its head is the restored constructor name (`headName`). -/
theorem Instance.restored_equation_major {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {equation : VDefEq}
    (hrestore : (compilationRestoration source auxiliaries).equation
      (g.equation index) = some equation) :
    ∃ fn levels args, equation.lhs.stripLams = .app fn
      (VExpr.mkApps (.const ((compilationRestoration source auxiliaries).headName
        s.constructors[index].name) levels) args) := by
  let r := compilationRestoration source auxiliaries
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨domains', lhs', rhs', type', hl', _, _, hel, _, _, _⟩ :=
    restored_common_telescope hl hr ht
  let ctor := s.constructors[index]
  let extra := s.families.size + s.constructors.size
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra ctor.fields.length
  let preArgs := vars (s.params.length + extra) ctor.fields.length ++ indices
  let head := g.recursorHead .recursor ctor.owner
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
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using H.heads_not_recursors ctor.owner spec hs
  have hlhs : lhs' = .app
      (VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner)) (VLevel.params g.uvars)) args)
      (VExpr.mkApps (.const (r.headName ctor.name) ctorLevels) ctorArgs) := by
    simpa [head, Instance.recursorHead, Restoration.expr.go, hnone, VExpr.mkApps,
      List.foldl_append] using hout.symm
  refine ⟨VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner)) (VLevel.params g.uvars)) args, ctorLevels, ctorArgs, ?_⟩
  rw [hel, hlhs]
  rw [stripLams_wrap]
  rfl

/-- A restored constructor belongs either to the source declaration or to
one of the earlier containers selected by the specialization list. -/
theorem CaseCompilationData.constructor_name_cases {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block)
    (hdisj : RecursorNamesFresh env source expanded auxiliaries)
    (index : Fin s.constructors.size) :
    (∃ ctor ∈ source.constructorConstants,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name = ctor.name) ∨
    (∃ a ∈ auxiliaries, ∃ ctor ∈ a.source.ctors,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name = ctor.name) := by
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
    apply H.headName_source hdisj
    exact List.mem_flatMap.mpr ⟨family, hfamily, List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) _ hfamily
    have hm : (compilationRestoration source auxiliaries).headName ctor.name ∈
        a.source.ctors.map (·.name) := by
      rw [← CaseSchema.directFamily_restored_constructor_names H ha hdf]
      exact List.mem_map.mpr ⟨ctor, hctor, rfl⟩
    obtain ⟨original, horiginal, hrestored⟩ := List.mem_map.mp hm
    exact ⟨a, ha, original, horiginal, by rw [hname]; exact hrestored.symm⟩

theorem CompilationData.constructor_name_cases {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) :
    (∃ ctor ∈ source.constructorConstants,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name = ctor.name) ∨
    (∃ a ∈ auxiliaries, ∃ ctor ∈ a.source.ctors,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name = ctor.name) :=
  H.toCaseCompilationData.constructor_name_cases H.recursorNamesFresh index

end Lean4Lean.InductiveSignature
