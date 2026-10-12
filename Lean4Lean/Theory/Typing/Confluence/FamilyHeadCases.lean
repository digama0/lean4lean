import Lean4Lean.Theory.Typing.FamilyHeadType
import Lean4Lean.Theory.Typing.Confluence.PatternConstructorRigidity

/-! # The family head of a recursor's owner

The family head of a constructor's owner, in a compiled declaration, is the result type former
of a constructor registered as a pattern constructor: a constructor of the declaration itself,
or a constructor of a certified container (whose own rules are registered earlier). Through
`WF.patCtor_resultRigid` this makes every major family of a registered recursor a present
rigid constant (`RecursorRegistered.family_head_rigid`,
`Theory/Typing/RecursorMajorFamily.lean`). -/

namespace Lean4Lean
open InductiveSignature

/-- Every source constructor of a compiled declaration returns an application
of one of the declaration's own families. -/
theorem CompiledInductive.ctor_result {env : VEnv} {source : VInductDecl} {block : VInductBlock}
    (H : CompiledInductive env source block) :
    ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, ∃ ls,
      ctor.type.forallResult.getAppFnArgs.1 = .const type.name ls := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source _ _ => ∀ type ∈ source.types, ∀ ctor ∈ type.ctors,
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 = .const type.name ls)
    (motive_2 := fun _ _ _ => True)
    (fun hdata _ _ type htype ctor hc => by
      obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
      exact ⟨_, (hraw type htype ctor hc).forallResult_head⟩)
    (fun _ _ _ ih => ih) trivial (fun _ _ _ _ _ _ _ _ => trivial) H

/-- Every source constructor of a compiled and installed declaration is a pattern constructor
of the environment: its recursor has a rule on it (`CompiledInductive.constructor_equation`),
registered by `VEnv.addInduct`. -/
theorem CompiledInductive.constructor_isPatCtor {base installBase installed env : VEnv}
    {source : VInductDecl} {block : VInductBlock}
    (H : CompiledInductive base source block) (hrecs : source.RecsOf block)
    (hinstall : installBase.addInduct source = some installed) (hle : installed ≤ env)
    {ctor : VConstVal} (hctor : ctor ∈ source.constructorConstants) :
    VEnv.IsPatCtor env ctor.name := by
  obtain ⟨df, hdf, hmajor⟩ := H.constructor_equation ctor hctor
  obtain ⟨r, hr, ru, hru, hof⟩ := hrecs.rules_total df hdf
  have hname := hmajor.ofEquation hof
  obtain ⟨hc, hp⟩ := VEnv.addInduct_pats_of_rule hinstall hr hru
  refine ⟨_, _, r.name, r.getMajorIdx, ru.ctorParams + ru.nfields, hle.pats hp, ?_⟩
  rw [hname]

/-- Constructors of certified containers are installed with their exact
declared types, which return applications of their own container family. -/
theorem ContainersInstalled.container_ctor {env : VEnv}
    {auxiliaries : List ContainerSpecialization} (H : ContainersInstalled env auxiliaries) :
    ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      env.constants ctor.name = some ctor.toVConstant ∧
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 = .const a.source.name ls := by
  induction auxiliaries generalizing env with
  | nil => intro a ha; cases ha
  | cons a' rest ih =>
    cases H with
    | @cons _ _ _ base block installed hcompile _ hrecs hinstall hle hrest =>
    intro a ha ctor hctor
    rcases List.mem_cons.mp ha with rfl | ha
    · have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
      exact ⟨hle.constants (VEnv.addInduct_ctor_find hinstall hsrc hctor),
        hcompile.ctor_result a.source hsrc ctor hctor⟩
    · exact ih hrest a ha ctor hctor

/-- The family head of a constructor's owner is the result type former of a pattern constructor
present in the environment: a constructor of the declaration itself, or of a certified
container. -/
theorem InductiveSignature.CompilationData.family_head_cases
    {base installBase installed env : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {auxiliaries : List ContainerSpecialization}
    {block : VInductBlock}
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : ContainersInstalled base auxiliaries) (hbase : base ≤ installBase)
    (hrecs : source.RecsOf block) (hinstall : installBase.addInduct source = some installed)
    (he : installed ≤ env) (index : Fin s.constructors.size) :
    ∃ (ctor : VConstVal) (ls : List VLevel), VEnv.IsPatCtor env ctor.name ∧
      env.constants ctor.name = some ctor.toVConstant ∧
      ctor.type.forallResult.getAppFnArgs.1 =
        .const ((compilationRestoration source auxiliaries).headName
          s.families[s.constructors[index].owner].name) ls := by
  have hcomp : CompiledInductive base source block := .intro hdata hprior
  have hle : base ≤ env := hbase.trans ((VEnv.addInduct_le hinstall).trans he)
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := hdata.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[index].owner)
  have hname : s.families[s.constructors[index].owner].name = family.name := hrel.name
  have hdc := s.declarationCtor_family index
  obtain ⟨fc, hfc, hrelctor⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _ hdc
  rw [hname]
  rcases List.mem_append.mp hfamily with hsrc | hdir
  · have hfn : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_self⟩
    rw [hdata.headName_source hfn]
    have hfcc : fc ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨family, hsrc, hfc⟩
    obtain ⟨ls, hres⟩ := hcomp.ctor_result family hsrc fc hfc
    exact ⟨fc, ls, hcomp.constructor_isPatCtor hrecs hinstall he hfcc,
      he.constants (VEnv.addInduct_ctor_find hinstall hsrc hfc), hres⟩
  · obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) family hdir
    obtain ⟨spec, hspec, hsa, hst⟩ : ∃ spec ∈ (compilationRestoration source auxiliaries).heads,
        spec.auxiliary = a.auxiliary ∧ spec.target = a.source.name :=
      ⟨_, List.mem_flatMap.mpr ⟨a, ha, by
        unfold ContainerSpecialization.heads; exact List.mem_cons_self⟩, rfl, rfl⟩
    have hhead : (compilationRestoration source auxiliaries).headName family.name =
        a.source.name := by
      rw [ContainerSpecialization.directFamily_name hdf, ← hsa, ← hst]
      exact Restoration.headName_of_mem hdata.restorationScoped hspec
    rw [hhead]
    have hpos : 0 < family.ctors.length := List.length_pos_of_mem hfc
    have hnames' := CaseCompilationData.directFamily_restored_constructor_names hdata.toCaseCompilationData ha hdf
    have hpos' : 0 < a.source.ctors.length := by
      have := congrArg List.length hnames'
      simp only [List.length_map] at this
      omega
    obtain ⟨cctor, hcctor⟩ := List.exists_mem_of_length_pos hpos'
    obtain ⟨hconst, ls, hres⟩ := hprior.container_ctor a ha cctor hcctor
    obtain ⟨p, rr, recN, M, N, hp, hpe⟩ := hprior.constructor_isPatCtor ha hcctor
    exact ⟨cctor, ls, ⟨p, rr, recN, M, N, hle.pats hp, hpe⟩, hle.constants hconst, hres⟩

end Lean4Lean
