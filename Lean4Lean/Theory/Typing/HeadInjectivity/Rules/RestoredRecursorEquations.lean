import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.RecursorEquations
import Lean4Lean.Theory.Inductive.RestorationHead

/-! # Syntax of restored recursor equations (nested compilations)

For a finite compilation with container specializations the installed equations and
recursors are restorations of the generated ones. Restoration acts on bound variables and
sorts as the identity, renames recursor heads, and replaces auxiliary family and constructor
heads (applied to at least the common parameters) by the specialized container heads. This
file computes the shape of a restored equation (`Instance.restored_equation`) and of a
restored recursor type (`CompilationData.restored_recursor`). -/

namespace Lean4Lean
namespace InductiveSignature

theorem Restoration.expr_forall_parts {r : Restoration} {domain body restored : VExpr}
    (h : r.expr (.forallE domain body) = some restored) :
    ∃ domain' body', r.expr domain = some domain' ∧ r.expr body = some body' ∧
      restored = .forallE domain' body' := by
  change (do
    let domain' ← r.expr domain
    let body' ← r.expr body
    pure (.forallE domain' body')) = some restored at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨domain', hd, body', hb, h⟩ := h
  exact ⟨domain', body', hd, hb, Option.some.inj h.symm⟩

theorem Restoration.expr_wrapLams_parts {r : Restoration} : ∀ {ds : List VExpr} {b out : VExpr},
    r.expr (.wrapLams ds b) = some out →
    ∃ ds' b', ds.mapM r.expr = some ds' ∧ r.expr b = some b' ∧ out = .wrapLams ds' b'
  | [], b, out, h => ⟨[], out, rfl, h, rfl⟩
  | d :: ds, b, out, h => by
    obtain ⟨d', body', hd, hb, rfl⟩ := Restoration.expr_lam_parts h
    obtain ⟨ds', b', hds, hb', rfl⟩ := Restoration.expr_wrapLams_parts hb
    exact ⟨d' :: ds', b', by simp [List.mapM_cons, hd, hds], hb', rfl⟩

theorem Restoration.expr_wrapForalls_parts {r : Restoration} : ∀ {ds : List VExpr} {b out : VExpr},
    r.expr (.wrapForalls ds b) = some out →
    ∃ ds' b', ds.mapM r.expr = some ds' ∧ r.expr b = some b' ∧ out = .wrapForalls ds' b'
  | [], b, out, h => ⟨[], out, rfl, h, rfl⟩
  | d :: ds, b, out, h => by
    obtain ⟨d', body', hd, hb, rfl⟩ := Restoration.expr_forall_parts h
    obtain ⟨ds', b', hds, hb', rfl⟩ := Restoration.expr_wrapForalls_parts hb
    exact ⟨d' :: ds', b', by simp [List.mapM_cons, hd, hds], hb', rfl⟩

theorem mapM_length {f : VExpr → Option VExpr} : ∀ {l l' : List VExpr},
    l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', -, l'', hl, rfl⟩ := h
    simp [mapM_length hl]

theorem mapM_getElem? {f : VExpr → Option VExpr} : ∀ {l l' : List VExpr} {i : Nat} {a : VExpr},
    l.mapM f = some l' → l[i]? = some a → ∃ a', f a = some a' ∧ l'[i]? = some a'
  | [], _, _, _, _, h => by simp at h
  | b :: l, l', i, a, hm, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
    obtain ⟨b', hb, l'', hl, rfl⟩ := hm
    cases i with
    | zero => simp at h; subst h; exact ⟨b', hb, rfl⟩
    | succ i =>
      simp at h
      obtain ⟨a', h1, h2⟩ := mapM_getElem? hl h
      exact ⟨a', h1, by simpa using h2⟩

theorem Restoration.go_const_none {r : Restoration} {name : Name} {levels : List VLevel}
    {args : List VExpr} (h : ∀ spec ∈ r.heads, spec.auxiliary ≠ name) :
    Restoration.expr.go r (.const name levels) args =
      some (.mkApps (.const (r.recursorName name) levels) args) := by
  have hnone : r.heads.find? (fun spec => spec.auxiliary == name) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using h spec hs
  simp [Restoration.expr.go, hnone]

/-- Restoration of a constructor application with its field variables: the head is the
restored constructor name and the field variables are kept. -/
theorem Restoration.ctorApp {r : Restoration} (hparams : ∀ h ∈ r.heads, h.nparams ≤ np)
    {output : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) (vars np offset ++ vars nf 0)) = some output) :
    ∃ levels' ms, output = VExpr.mkApps (.const (r.headName name) levels') (ms ++ vars nf 0) := by
  obtain ⟨n1, l1, ms, e1⟩ := Restoration.ctorApp_fields hparams h
  obtain ⟨l2, a2, e2⟩ := Restoration.const_mkApps h
  have := congrArg (fun e : VExpr => e.getAppFnArgs.1) (e1.symm.trans e2)
  simp only [VExpr.getAppFnArgs_mkApps_const] at this
  cases this
  exact ⟨l1, ms, e1⟩

namespace Instance
variable {s : InductiveSignature} (g : Instance s) (index : Fin s.constructors.size)

/-- **Shape of a restored generated equation.** -/
theorem restored_equation {r : Restoration} {df : VDefEq}
    (hparams : ∀ h ∈ r.heads, h.nparams ≤ s.params.length)
    (hhead : ∀ h ∈ r.heads, h.auxiliary ≠ g.recursorName s.constructors[index].owner)
    (he : r.equation (g.equation index) = some df) :
    ∃ ds' idx' lsC' ms' body' T',
      (g.eqDoms index).mapM r.expr = some ds' ∧
      (g.eqIndices index).mapM r.expr = some idx' ∧
      df.lhs = .wrapLams ds' (.mkApps (.const (r.recursorName
          (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars))
        ((vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[index].fields.length ++ idx') ++
          [.mkApps (.const (r.headName s.constructors[index].name) lsC')
            (ms' ++ (eqFs index).map .bvar)])) ∧
      df.rhs = .wrapLams ds' body' ∧
      df.type = .wrapForalls ds' T' ∧
      r.expr (.mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)))
        (g.eqIndices index ++ [g.constructorApp s.constructors[index]
          (s.families.size + s.constructors.size) 0])) = some T' ∧
      df.uvars = g.uvars := by
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts he
  have huv : df.uvars = g.uvars := by
    simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at he
    obtain ⟨_, _, _, _, _, _, h⟩ := he
    cases h; rfl
  obtain ⟨ds', l, hds, hl', el⟩ := Restoration.expr_wrapLams_parts (ds := g.eqDoms index) hl
  obtain ⟨ds2, body', hds2, -, er⟩ := Restoration.expr_wrapLams_parts (ds := g.eqDoms index) hr
  obtain ⟨ds3, T', hds3, hT', et⟩ := Restoration.expr_wrapForalls_parts (ds := g.eqDoms index) ht
  cases hds.symm.trans hds2
  cases hds.symm.trans hds3
  -- the left-hand side body
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hl'
  rw [restoration_mkApps] at hl'
  simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, bind, Option.bind_eq_some_iff,
    List.append_nil] at hl'
  obtain ⟨a, ⟨a1, ⟨_, h1, idx', hi, h2⟩, a3, hm, h3⟩, hout⟩ := hl'
  cases Option.some.inj h1
  cases Option.some.inj h2
  cases Option.some.inj h3
  simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hm
  obtain ⟨major', hmajor, _, rfl, rfl⟩ := hm
  simp only [recursorHead] at hout
  rw [Restoration.go_const_none hhead, Option.some.injEq] at hout
  obtain ⟨lsC', ms', rfl⟩ := Restoration.ctorApp hparams hmajor
  refine ⟨ds', idx', lsC', ms', body', T', hds, hi, ?_, er, et, ?_, huv⟩
  · rw [el, ← hout, InductiveSignature.vars_zero]; rfl
  · exact hT'

/-- **Shape of a restored generated equation in abstract mode** (generic case equations). -/
theorem restored_equation_abstract {r : Restoration} {df : VDefEq} (blk : Name) (first : Nat)
    (hparams : ∀ h ∈ r.heads, h.nparams ≤ s.params.length)
    (he : r.equation (g.equation index (.elim blk first)) = some df) :
    ∃ ds' idx' lsC' ms' body' T',
      (g.eqDoms index).mapM r.expr = some ds' ∧
      (g.eqIndices index).mapM r.expr = some idx' ∧
      df.lhs = .wrapLams ds' (.mkApps (.elim blk (first + s.constructors[index].owner.val)
          (g.targetLevel :: g.levels))
        ((vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[index].fields.length ++ idx') ++
          [.mkApps (.const (r.headName s.constructors[index].name) lsC')
            (ms' ++ (eqFs index).map .bvar)])) ∧
      df.rhs = .wrapLams ds' body' ∧
      df.type = .wrapForalls ds' T' ∧
      r.expr (.mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)))
        (g.eqIndices index ++ [g.constructorApp s.constructors[index]
          (s.families.size + s.constructors.size) 0])) = some T' ∧
      df.uvars = g.uvars := by
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts he
  have huv : df.uvars = g.uvars := by
    simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at he
    obtain ⟨_, _, _, _, _, _, h⟩ := he
    cases h; rfl
  obtain ⟨ds', l, hds, hl', el⟩ := Restoration.expr_wrapLams_parts (ds := g.eqDoms index) hl
  obtain ⟨ds2, body', hds2, -, er⟩ := Restoration.expr_wrapLams_parts (ds := g.eqDoms index) hr
  obtain ⟨ds3, T', hds3, hT', et⟩ := Restoration.expr_wrapForalls_parts (ds := g.eqDoms index) ht
  cases hds.symm.trans hds2
  cases hds.symm.trans hds3
  -- the left-hand side body
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hl'
  rw [restoration_mkApps] at hl'
  simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, bind, Option.bind_eq_some_iff,
    List.append_nil] at hl'
  obtain ⟨a, ⟨a1, ⟨_, h1, idx', hi, h2⟩, a3, hm, h3⟩, hout⟩ := hl'
  cases Option.some.inj h1
  cases Option.some.inj h2
  cases Option.some.inj h3
  simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hm
  obtain ⟨major', hmajor, _, rfl, rfl⟩ := hm
  simp only [recursorHead, Restoration.expr.go, Option.some.injEq] at hout
  obtain ⟨lsC', ms', rfl⟩ := Restoration.ctorApp hparams hmajor
  refine ⟨ds', idx', lsC', ms', body', T', hds, hi, ?_, er, et, ?_, huv⟩
  · rw [el, ← hout, InductiveSignature.vars_zero]; rfl
  · exact hT'

end Instance

/-- The restored constructor of a generated equation returns the restored family of its
owner: either it is a source constructor, installed with the block, or a constructor of a
certified container, installed in the base environment. -/
theorem CaseCompilationData.ctor_cases {s : InductiveSignature}
    (H : CaseCompilationData base source expanded s aux block)
    (hfresh : RecursorNamesFresh base source expanded aux)
    (hprior : ContainersInstalled base aux) (index : Fin s.constructors.size) :
    (∃ fc ∈ source.constructorConstants,
      fc.name = (compilationRestoration source aux).headName s.constructors[index].name ∧
      ∃ ls, fc.type.forallResult.getAppFnArgs.1 = .const ((compilationRestoration source aux).headName
        s.families[s.constructors[index].owner].name) ls) ∨
    (∃ cc : VConstVal, base.constants ((compilationRestoration source aux).headName
        s.constructors[index].name) = some cc.toVConstant ∧
      ∃ ls, cc.type.forallResult.getAppFnArgs.1 = .const ((compilationRestoration source aux).headName
        s.families[s.constructors[index].owner].name) ls) := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[index].owner)
  have hname : s.families[s.constructors[index].owner].name = family.name := hrel.name
  obtain ⟨fc, hfc, hrelctor⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
    (s.declarationCtor_family index)
  have hcname : s.constructors[index].name = fc.name := hrelctor.1
  rw [hname, hcname]
  rcases List.mem_append.mp hfamily with hsrc | hdir
  · left
    have hfn : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_self⟩
    have hcn : fc.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨fc, hfc, rfl⟩)⟩
    rw [H.headName_source hfresh hfn, H.headName_source hfresh hcn]
    obtain ⟨_, _, _, _, _, hraw⟩ := H.sourceParameters
    obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw family hsrc fc hfc
    refine ⟨fc, List.mem_flatMap.mpr ⟨family, hsrc, hfc⟩, rfl, ?_⟩
    have h2 := hhead
    rw [← VExpr.forallResult_of_head hhead, ← VExpr.forallResult_wrapForalls doms, ← heq] at h2
    exact ⟨_, h2⟩
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) family hdir
    obtain ⟨spec, hspec, hsa, hst⟩ : ∃ spec ∈ (compilationRestoration source aux).heads,
        spec.auxiliary = a.auxiliary ∧ spec.target = a.source.name :=
      ⟨_, List.mem_flatMap.mpr ⟨a, ha, by
        unfold ContainerSpecialization.heads; exact List.mem_cons_self⟩, rfl, rfl⟩
    have hhead : (compilationRestoration source aux).headName family.name = a.source.name := by
      rw [ContainerSpecialization.directFamily_name hdf, ← hsa, ← hst]
      exact Restoration.headName_of_mem H.restorationScoped hspec
    rw [hhead]
    have hnames := CaseSchema.directFamily_restored_constructor_names H ha hdf
    have hm : (compilationRestoration source aux).headName fc.name ∈ a.source.ctors.map (·.name) := by
      rw [← hnames]
      exact List.mem_map.mpr ⟨fc, hfc, rfl⟩
    obtain ⟨cctor, hcctor, hcn⟩ := List.mem_map.mp hm
    obtain ⟨hconst, hres⟩ := hprior.container_ctor a ha cctor hcctor
    exact ⟨cctor, by rw [← hcn]; exact hconst, hres⟩

/-- `CaseCompilationData.ctor_cases` for a full compilation. -/
theorem CompilationData.ctor_cases {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) (index : Fin s.constructors.size) :
    (∃ fc ∈ source.constructorConstants,
      fc.name = (compilationRestoration source aux).headName s.constructors[index].name ∧
      ∃ ls, fc.type.forallResult.getAppFnArgs.1 = .const ((compilationRestoration source aux).headName
        s.families[s.constructors[index].owner].name) ls) ∨
    (∃ cc : VConstVal, base.constants ((compilationRestoration source aux).headName
        s.constructors[index].name) = some cc.toVConstant ∧
      ∃ ls, cc.type.forallResult.getAppFnArgs.1 = .const ((compilationRestoration source aux).headName
        s.families[s.constructors[index].owner].name) ls) :=
  H.toCaseCompilationData.ctor_cases H.recursorNamesFresh hprior index

theorem Restoration.recursor_parts {r : Restoration} {value value' : VConstVal}
    (h : r.recursor value = some value') :
    value'.name = r.recursorName value.name ∧ value'.uvars = value.uvars ∧
      r.expr value.type = some value'.type := by
  simp only [Restoration.recursor, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨rfl, rfl, ht⟩

/-- The restored recursor of an owner, its type a restored telescope. -/
theorem CompilationData.restored_recursor {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block) (o : Fin s.families.size) :
    ∃ rec' ∈ block.recursors, rec'.name =
        (compilationRestoration source aux).recursorName (g.recursorName o) ∧
      rec'.uvars = g.uvars ∧
      ∃ dsH' RH', rec'.type = .wrapForalls dsH' RH' ∧
        (g.recDoms o).mapM (compilationRestoration source aux).expr = some dsH' := by
  have hrs := List.mapM_eq_some.mp H.recursors
  obtain ⟨rec', hrec', hr⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrs (g.recursor o)
    (List.mem_map.2 ⟨o, List.mem_finRange _, rfl⟩)
  obtain ⟨hn, hu, ht⟩ := Restoration.recursor_parts hr
  obtain ⟨RH, eH⟩ := g.recursorType_eq_hi o
  rw [eH] at ht
  obtain ⟨dsH', RH', hds, -, et⟩ := Restoration.expr_wrapForalls_parts ht
  exact ⟨rec', hrec', hn, hu, dsH', RH', et, hds⟩

/-- Restored recursor names are distinct across owners. -/
theorem CompilationData.restored_recursorName_inj {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block) {o o' : Fin s.families.size}
    (h : (compilationRestoration source aux).recursorName (g.recursorName o) =
      (compilationRestoration source aux).recursorName (g.recursorName o')) : o = o' := by
  have hrs := List.mapM_eq_some.mp H.recursors
  have hmap : block.recursors.map (·.name) =
      g.recursors.map fun v => (compilationRestoration source aux).recursorName v.name := by
    clear h
    generalize g.recursors = gr at hrs ⊢
    generalize block.recursors = br at hrs ⊢
    induction hrs with
    | nil => rfl
    | cons hxy _ ih => simp only [List.map_cons, ih, (Restoration.recursor_parts hxy).1]
  have hnd := H.names
  rw [List.map_append] at hnd
  have hnd := (List.nodup_append.1 hnd).2.1
  rw [hmap] at hnd
  simp only [Instance.recursors, List.map_map] at hnd
  exact VEnv.inj_on_of_nodup_map hnd (List.mem_finRange _) (List.mem_finRange _) h

/-- Restored constructor names are distinct within an owner. -/
theorem CompilationData.restored_ctor_inj {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) {i j : Fin s.constructors.size}
    (ho : s.constructors[i].owner = s.constructors[j].owner)
    (hn : (compilationRestoration source aux).headName s.constructors[i].name =
      (compilationRestoration source aux).headName s.constructors[j].name) : i = j := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[i].owner)
  have hnames := ctorNames_eq_of_forall₂ hrel.constructors (fun _ _ h => h.1)
  have hnd : ((s.declarationFamily s.constructors[i].owner).ctors.map
      (fun c => (compilationRestoration source aux).headName c.name)).Nodup := by
    change (List.map ((compilationRestoration source aux).headName ∘ VConstVal.name) _).Nodup
    rw [← List.map_map, hnames, List.map_map]
    rcases List.mem_append.mp hfamily with hsrc | hdir
    · have heq : family.ctors.map ((compilationRestoration source aux).headName ∘ (·.name)) =
          family.ctors.map (·.name) := by
        apply List.map_congr_left
        intro ctor hc
        apply H.headName_source
        exact List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hc, rfl⟩)⟩
      rw [heq]
      have hfam := (List.pairwise_flatMap.mp (familyNames_nodup H.sourceWF.2.1)).1 family hsrc
      exact (List.nodup_cons.mp hfam).2
    · obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
        (List.mapM_eq_some.mp hdirect) _ hdir
      have := CaseSchema.directFamily_restored_constructor_names H.toCaseCompilationData ha hdf
      change List.map ((compilationRestoration source aux).headName ∘ VConstVal.name) _ = _ at this
      rw [this]
      have hfam := (List.pairwise_flatMap.mp (familyNames_nodup
        (hprior.container_names a ha))).1 a.source (List.getElem_mem a.family.isLt)
      exact (List.nodup_cons.mp hfam).2
  simp only [declarationFamily, List.map_filterMap] at hnd
  apply Fin.ext
  refine filterMap_idx_inj (h := id) (b := (compilationRestoration source aux).headName
    s.constructors[i].name) (b' := (compilationRestoration source aux).headName
    s.constructors[j].name) (by simpa using hnd)
    (by exact i.isLt) (by exact j.isLt) ?_ ?_ hn
  · simp
  · have := congrArg Fin.val ho
    simp only [Fin.getElem_fin] at this
    simp [this]

theorem ContainerSpecialization.directFamily_resultLevel_nested {a : ContainerSpecialization}
    {params : List VExpr} (H : a.specializedFamily U params = some direct) :
    direct.resultLevel = a.source.resultLevel.inst a.levels := by
  simp only [ContainerSpecialization.specializedFamily, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at H
  obtain ⟨_, _, _, _, rfl⟩ := H
  rfl

/-- The restored head of a family: a source family (with its correspondence), or the
container family of a specialization. -/
theorem CaseCompilationData.family_cases {s : InductiveSignature}
    (H : CaseCompilationData base source expanded s aux block)
    (hfresh : RecursorNamesFresh base source expanded aux) (o : Fin s.families.size) :
    (∃ envTypes family, base.addConstVals source.typeConstants = some envTypes ∧
      family ∈ source.types ∧
      RestoresFamily (compilationRestoration source aux) envTypes source.uvars
        (s.declarationFamily o) family ∧
      (compilationRestoration source aux).headName s.families[o].name = family.name ∧
      ∀ lv, (compilationRestoration source aux).headLevels s.families[o].name lv = lv) ∨
    (∃ a ∈ aux, (compilationRestoration source aux).headName s.families[o].name = a.source.name ∧
      (∀ lv, (compilationRestoration source aux).headLevels s.families[o].name lv =
        a.levels.map (·.inst lv)) ∧
      s.families[o].resultLevel ≈ a.source.resultLevel.inst a.levels) := by
  obtain ⟨envTypes, direct, htypes, hdirect, _, hfamilies⟩ := H.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem o)
  have hname : s.families[o].name = family.name := hrel.name
  rcases List.mem_append.mp hfamily with hsrc | hdir
  · left
    have hfn : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_self⟩
    refine ⟨envTypes, family, htypes, hsrc, hrel, ?_, fun lv => ?_⟩
    · rw [hname]; exact H.headName_source hfresh hfn
    · rw [hname]; exact H.headLevels_source hfn
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) family hdir
    obtain ⟨spec, hspec, hsa, hst, hsl⟩ : ∃ spec ∈ (compilationRestoration source aux).heads,
        spec.auxiliary = a.auxiliary ∧ spec.target = a.source.name ∧ spec.levels = a.levels :=
      ⟨_, List.mem_flatMap.mpr ⟨a, ha, by
        unfold ContainerSpecialization.heads; exact List.mem_cons_self⟩, rfl, rfl, rfl⟩
    have hfa : s.families[o].name = a.auxiliary := hname.trans
      (ContainerSpecialization.directFamily_name hdf)
    refine ⟨a, ha, ?_, fun lv => ?_, ?_⟩
    · rw [hfa, ← hsa, ← hst]; exact Restoration.headName_of_mem H.restorationScoped hspec
    · rw [hfa, ← hsa, ← hsl]; exact Restoration.headLevels_of_mem H.restorationScoped hspec
    · have := hrel.resultLevel
      rw [ContainerSpecialization.directFamily_resultLevel_nested hdf] at this
      exact this

/-- `CaseCompilationData.family_cases` for a full compilation. -/
theorem CompilationData.family_cases {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block) (o : Fin s.families.size) :
    (∃ envTypes family, base.addConstVals source.typeConstants = some envTypes ∧
      family ∈ source.types ∧
      RestoresFamily (compilationRestoration source aux) envTypes source.uvars
        (s.declarationFamily o) family ∧
      (compilationRestoration source aux).headName s.families[o].name = family.name ∧
      ∀ lv, (compilationRestoration source aux).headLevels s.families[o].name lv = lv) ∨
    (∃ a ∈ aux, (compilationRestoration source aux).headName s.families[o].name = a.source.name ∧
      (∀ lv, (compilationRestoration source aux).headLevels s.families[o].name lv =
        a.levels.map (·.inst lv)) ∧
      s.families[o].resultLevel ≈ a.source.resultLevel.inst a.levels) :=
  H.toCaseCompilationData.family_cases H.recursorNamesFresh o

/-- A compilation with container specializations has at least two families. -/
theorem CompilationData.nested_families {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g aux block) (haux : aux ≠ []) :
    2 ≤ s.families.size := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have h1 := Lean4Lean.List.Forall₂.length_eq hfamilies
  have h2 := mapM_length (List.mapM_eq_some.mp hdirect)
  have h3 : source.types ≠ [] := H.sourceWF.1
  simp only [declaration, List.length_map, List.length_zipIdx, Array.length_toList,
    List.length_append] at h1
  have := List.length_pos_iff.2 h3
  have := List.length_pos_iff.2 haux
  omega
where
  mapM_length {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
      (h : List.Forall₂ R l l') : l'.length = l.length :=
    (Lean4Lean.List.Forall₂.length_eq h).symm

end InductiveSignature

theorem ContainersInstalled.mem {env : VEnv}
    {aux : List InductiveSignature.ContainerSpecialization}
    (H : ContainersInstalled env aux) :
    ∀ a ∈ aux, ∃ base block installed, CompiledInductive base a.container block ∧
      block.WF base ∧ VInductBlock.install base block = some installed ∧ installed ≤ env := by
  exact ContainersInstalled.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun env aux _ => ∀ a ∈ aux, ∃ base block installed,
      CompiledInductive base a.container block ∧ block.WF base ∧
      VInductBlock.install base block = some installed ∧ installed ≤ env)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (by simp)
    (fun hcompile hw hinstall hle _ _ ih => by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨_, _, _, hcompile, hw, hinstall, hle⟩
      · exact ih a ha)
    H

end Lean4Lean
