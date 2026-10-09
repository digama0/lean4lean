import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas

/-! Name separation inherited from the source and expanded declarations: the source family
names, the auxiliary families of the restoration and the generated recursor names of a
compilation are pairwise disjoint. -/

namespace Lean4Lean.InductiveSignature

theorem familyNames_perm (types : List VInductiveType) :
    (familyNames types).Perm
      (types.map (·.name) ++ types.flatMap (fun t => t.ctors.map (·.name))) := by
  induction types with
  | nil => exact .refl _
  | cons t ts ih =>
    change (t.name :: (t.ctors.map (·.name) ++ familyNames ts)).Perm
      (t.name :: (ts.map (·.name) ++ (t.ctors.map (·.name) ++ ts.flatMap (fun t => t.ctors.map (·.name)))))
    exact ((ih.append_left _).trans (List.perm_append_comm_assoc ..)).cons _

theorem familyNames_nodup {decl : VInductDecl} (H : decl.sourceNames.Nodup) :
    (familyNames decl.types).Nodup := by
  apply (familyNames_perm decl.types).nodup_iff.mpr
  simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
    VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def] using H

theorem Models.familyNames {s : InductiveSignature} (H : s.Models env decl) :
    familyNames s.declaration.types = familyNames decl.types :=
  familyNames_eq_of_forall₂ (Lean4Lean.List.Forall₂.imp (fun _ _ h =>
    ⟨h.1, h.2.2.2.2⟩) H.families)

theorem RestoresFamily.familyNames
    (H : List.Forall₂ (RestoresFamily r env U) left right) :
    familyNames left = familyNames right :=
  familyNames_eq_of_forall₂ (Lean4Lean.List.Forall₂.imp (fun _ _ h =>
    ⟨h.name, ctorNames_eq_of_forall₂ h.constructors (fun _ _ h => h.1)⟩) H)

theorem compilationRestoration_heads_names
    {params : List VExpr} {source : VInductDecl}
    {auxiliaries : List ContainerSpecialization}
    (hparams : params.length = source.nparams)
    (H : auxiliaries.mapM (fun a => a.specializedFamily source.uvars params) = some direct) :
    ((compilationRestoration source auxiliaries).heads.map (·.auxiliary)) = familyNames direct := by
  have hrel := List.mapM_eq_some.mp H
  clear H
  change (auxiliaries.flatMap (fun a => a.heads source.uvars source.nparams)).map
    (·.auxiliary) = familyNames direct
  induction hrel with
  | nil => rfl
  | @cons a d auxiliaries rest ha _ ih =>
    simp only [List.flatMap_cons, List.map_append]
    change (a.heads source.uvars source.nparams).map (·.auxiliary) ++ _ =
      (d.name :: d.ctors.map (·.name)) ++ familyNames rest
    have hh := a.directFamily_heads ha
    rw [hparams] at hh
    rw [hh, ih]

/-- Source family names and auxiliary family names are disjoint. This is a
consequence of expanded declaration freshness and the ordered correspondence. -/
theorem CaseCompilationData.source_head_disjoint
    {s : InductiveSignature}
    (H : CaseCompilationData env source expanded s auxiliaries block) :
    List.Disjoint (familyNames source.types)
      ((compilationRestoration source auxiliaries).heads.map (·.auxiliary)) := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have hnames := RestoresFamily.familyNames hfamilies
  have hnd := familyNames_nodup H.expandedWF.2.1
  rw [← H.model.familyNames, hnames] at hnd
  rw [compilationRestoration_heads_names (H.model.nparams.trans H.nparams) hdirect]
  have hdis := (List.nodup_append.mp
    (by simpa only [familyNames, List.flatMap_append] using hnd)).2.2
  intro name hsource hdirect
  exact hdis name hsource name hdirect rfl

theorem ContainerSpecialization.directFamily_name
    {a : ContainerSpecialization} {params : List VExpr}
    (H : a.specializedFamily U params = some direct) : direct.name = a.auxiliary := by
  have h := a.directFamily_heads H
  simp only [ContainerSpecialization.heads, List.map_cons, List.cons.injEq] at h
  exact h.1.symm

theorem familyHeaderNames_eq {R : VInductiveType → VInductiveType → Prop}
    (H : List.Forall₂ R left right) (hn : ∀ a b, R a b → a.name = b.name) :
    left.map (·.name) = right.map (·.name) := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp [hn _ _ h, ih]

theorem declaration_familyNames (s : InductiveSignature) :
    s.declaration.types.map (·.name) = s.families.toList.map (·.name) := by
  simp only [declaration, List.map_map, Function.comp_def]
  change List.map ((fun f : Family => f.name) ∘ Prod.fst) _ = _
  rw [← List.map_map (f := Prod.fst) (g := fun f : Family => f.name), List.zipIdx_map_fst]

/-- The recursor-renaming table contains only the generated recursor
names of auxiliary families, never names of constructors or other constants. -/
theorem CompilationData.recursor_source_mem
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (hpair : pair ∈ (compilationRestoration source auxiliaries).recursors) :
    pair.1 ∈ g.recursors.map (·.name) := by
  obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hpair
  have ha := List.fst_mem_of_mem_zipIdx hitem
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  obtain ⟨d, hd, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdirect) _ ha
  have hheaders := familyHeaderNames_eq hfamilies (fun _ _ h => h.name)
  have hm : d.name ∈ s.families.toList.map (·.name) := by
    rw [← declaration_familyNames, hheaders]
    exact List.mem_map.mpr ⟨d, List.mem_append_right _ hd, rfl⟩
  obtain ⟨family, hfamily, hname⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, hindex⟩ := List.mem_iff_getElem.mp hfamily
  have hi' : i < s.families.size := by simpa only [Array.length_toList] using hi
  let owner : Fin s.families.size := ⟨i, hi'⟩
  have howner : s.families[owner].name = item.1.auxiliary := by
    exact (congrArg (fun f : Family => f.name) hindex).trans
      (hname.trans (ContainerSpecialization.directFamily_name hdf))
  exact List.mem_map.mpr ⟨g.recursor owner,
    List.mem_map.mpr ⟨owner, List.mem_finRange owner, rfl⟩, by
      change g.recursorName owner = item.1.auxiliary.str "rec"
      rw [H.recursorNames, howner]⟩

/-- None of the expanded source names is a generated recursor name. -/
theorem CompilationData.source_recursors_disjoint
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block) :
    List.Disjoint (familyNames source.types) (g.recursors.map (·.name)) := by
  obtain ⟨envTypes, direct, _, _, _, hfamilies⟩ := H.correspondence
  have hnames := RestoresFamily.familyNames hfamilies
  have hnd : (expanded.sourceNames ++ g.recursors.map (·.name)).Nodup := by
    simpa only [VInductDecl.sourceNames, List.map_append, List.append_assoc] using H.generatedNames
  intro name hs hr
  have he : name ∈ familyNames expanded.types := by
    rw [← H.model.familyNames, hnames]
    simpa only [familyNames, List.flatMap_append] using List.mem_append_left (familyNames direct) hs
  have he' : name ∈ expanded.sourceNames := by
    have := (familyNames_perm expanded.types).mem_iff.mp he
    simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def] using this
  exact (List.nodup_append.mp hnd).2.2 name he' name hr rfl

/-- The auxiliary recursor names of a compilation are fresh and distinct from the declaration's
names. -/
theorem CompilationData.recursorNamesFresh {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block) :
    RecursorNamesFresh env source expanded auxiliaries := by
  intro name hr
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hr
  have hm := H.recursor_source_mem hpair
  obtain ⟨rec, hrec, hname⟩ := List.mem_map.mp hm
  refine ⟨hname ▸ H.recursorsFresh rec hrec, fun hs => ?_, fun he => ?_⟩
  · apply H.source_recursors_disjoint _ hm
    apply (familyNames_perm source.types).mem_iff.mpr
    simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
      using hs
  · have hnd := H.generatedNames
    rw [List.map_append, List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ (by
      simpa only [VInductDecl.sourceNames, List.map_append] using he) _ hm rfl

end Lean4Lean.InductiveSignature
