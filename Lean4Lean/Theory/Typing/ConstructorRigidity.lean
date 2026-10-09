import Lean4Lean.Theory.Inductive.RecursorEquationCoverage
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! Declaration-history invariants for constructors of stored rules and of case rules: they
and their result families stay rigid (no stored rule is headed by them) in every later
environment. -/

namespace Lean4Lean

/-- The final major argument of an installed equation is headed by the constant `name`. -/
def VDefEq.HasConstructorMajor (equation : VDefEq) (name : Name) : Prop :=
  ∃ fn levels args, equation.lhs.stripLams = .app fn (VExpr.mkApps (.const name levels) args)

theorem InductiveSignature.CompilationData.equation_major_cases
    {s : InductiveSignature} {g : s.Instance}
    (H : InductiveSignature.CompilationData env source expanded s g auxiliaries block)
    (hprior : ContainersInstalled env auxiliaries) (hdf : df ∈ block.rules) :
    ∃ name, df.HasConstructorMajor name ∧
      ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨
        ∃ prior, env.defeqs prior ∧ prior.HasConstructorMajor name) := by
  obtain ⟨generated, hgenerated, hrestored⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (List.mapM_eq_some.mp H.equations) _ hdf
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hgenerated
  refine ⟨_, InductiveSignature.Instance.restored_equation_major H index hrestored, ?_⟩
  rcases H.constructor_name_cases index with ho | ⟨a, ha, ctor, hc, he⟩
  · exact Or.inl ho
  · right
    rw [he]
    exact hprior.constructor_equation a ha ctor hc

theorem CompiledInductive.equation_major_cases (H : CompiledInductive env source block) :
    ∀ df ∈ block.rules, ∃ name, df.HasConstructorMajor name ∧
      ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨
        ∃ prior, env.defeqs prior ∧ prior.HasConstructorMajor name) := by
  exact CompiledInductive.rec
    (motive_1 := fun env source block _ =>
      ∀ df ∈ block.rules, ∃ name, df.HasConstructorMajor name ∧
        ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨
          ∃ prior, env.defeqs prior ∧ prior.HasConstructorMajor name))
    (motive_2 := fun _ _ _ => True)
    (fun hdata hprior _ df hdf => hdata.equation_major_cases hprior hdf)
    (fun _ hle _ ih df hdf => by
      obtain ⟨name, hm, ho | ⟨prior, hp, hpm⟩⟩ := ih df hdf
      · exact ⟨name, hm, Or.inl ho⟩
      · exact ⟨name, hm, Or.inr ⟨prior, hle.defeqs hp, hpm⟩⟩)
    trivial (fun _ _ _ _ _ _ _ => trivial) H

private theorem VDefEq.HasConstructorMajor.unique {df : VDefEq}
    (hleft : df.HasConstructorMajor left) (hright : df.HasConstructorMajor right) :
    left = right := by
  obtain ⟨fl, ll, al, hl⟩ := hleft
  obtain ⟨fr, lr, ar, hr⟩ := hright
  have he := (VExpr.app.inj (hl.symm.trans hr)).2
  have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
  simp only [VExpr.getAppFnArgs_mkApps_head] at hh
  exact (VExpr.const.inj hh).1

/-- The codomain of a syntactic forall telescope. -/
def VExpr.forallResult : VExpr → VExpr
  | .forallE _ body => body.forallResult
  | e => e

theorem VExpr.forallResult_wrapForalls (doms : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls doms body).forallResult = body.forallResult := by
  induction doms with
  | nil => rfl
  | cons d ds ih => exact ih

theorem VExpr.forallResult_of_head {e : VExpr} (h : e.getAppFnArgs.1 = .const c ls) :
    e.forallResult = e := by
  cases e with
  | forallE => simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at h
  | _ => rfl

/-- Every source constructor of a compiled declaration returns an application
of one of the declaration's own families. -/
theorem CompiledInductive.ctor_result (H : CompiledInductive env source block) :
    ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, ∃ ls,
      ctor.type.forallResult.getAppFnArgs.1 = .const type.name ls := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source _ _ => ∀ type ∈ source.types, ∀ ctor ∈ type.ctors,
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 = .const type.name ls)
    (motive_2 := fun _ _ _ => True)
    (fun hdata _ _ type htype ctor hc => by
      obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
      obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw type htype ctor hc
      have h2 := hhead
      rw [← VExpr.forallResult_of_head hhead, ← VExpr.forallResult_wrapForalls doms, ← heq] at h2
      exact ⟨_, h2⟩)
    (fun _ _ _ ih => ih) trivial (fun _ _ _ _ _ _ _ => trivial) H

theorem VInductBlock.install_ctor_lookup (H : VInductBlock.install base block = some installed)
    (hvalue : value ∈ block.ctors) : installed.constants value.name = some value.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact (VEnv.addEliminators_addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le).constants (VEnv.addConstVals_get hc hvalue)

/-- Constructors of certified containers are installed with their exact
declared types, which return applications of their own container family. -/
theorem ContainersInstalled.container_ctor (H : ContainersInstalled env auxiliaries) :
    ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      env.constants ctor.name = some ctor.toVConstant ∧
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 = .const a.source.name ls := by
  exact ContainersInstalled.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun env auxiliaries _ => ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      env.constants ctor.name = some ctor.toVConstant ∧
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 = .const a.source.name ls)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (by simp)
    (fun hcompile _ hinstall hle _ _ ih => by
      intro a ha ctor hctor
      rcases List.mem_cons.mp ha with rfl | ha
      · have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
        have hc : ctor ∈ a.container.constructorConstants :=
          List.mem_flatMap.mpr ⟨a.source, hsrc, hctor⟩
        refine ⟨hle.constants (VInductBlock.install_ctor_lookup hinstall ?_),
          hcompile.ctor_result a.source hsrc ctor hctor⟩
        rw [hcompile.ctors_eq]; exact hc
      · exact ih a ha ctor hctor)
    H

/-- The family head of a constructor's owner is either a source family,
which then contains the restored constructor, or the family of a certified
container constructor whose recursor equation is already installed in the
base environment. -/
theorem InductiveSignature.CaseCompilationData.family_head_cases
    {s : InductiveSignature}
    (hdata : InductiveSignature.CaseCompilationData base source expanded s auxiliaries block)
    (hdisj : InductiveSignature.RecursorNamesFresh base source expanded auxiliaries)
    (hprior : ContainersInstalled base auxiliaries) (index : Fin s.constructors.size) :
    (∃ family ∈ source.types, s.families[s.constructors[index].owner].name = family.name ∧
      (InductiveSignature.compilationRestoration source auxiliaries).headName family.name =
        family.name ∧
      ∃ fc ∈ family.ctors, (InductiveSignature.compilationRestoration source auxiliaries).headName
        s.constructors[index].name = fc.name) ∨
    ∃ (ctor : VConstVal) (equation : VDefEq), base.defeqs equation ∧
      equation.HasConstructorMajor ctor.name ∧
      base.constants ctor.name = some ctor.toVConstant ∧
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 =
        .const ((InductiveSignature.compilationRestoration source auxiliaries).headName
          s.families[s.constructors[index].owner].name) ls := by
  open InductiveSignature in
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := hdata.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[index].owner)
  have hname : s.families[s.constructors[index].owner].name = family.name := hrel.name
  have hdc := s.declarationCtor_family index
  obtain ⟨fc, hfc, hrelctor⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _ hdc
  rcases List.mem_append.mp hfamily with hsrc | hdir
  · left
    have hfn : family.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_self⟩
    have hcn : fc.name ∈ familyNames source.types :=
      List.mem_flatMap.mpr ⟨family, hsrc, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨fc, hfc, rfl⟩)⟩
    have hcname : s.constructors[index].name = fc.name := hrelctor.1
    refine ⟨family, hsrc, hname, hdata.headName_source hdisj hfn, fc, hfc, ?_⟩
    rw [hcname]; exact hdata.headName_source hdisj hcn
  · right
    rw [hname]
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
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
    have hnames' := CaseSchema.directFamily_restored_constructor_names hdata ha hdf
    have hpos' : 0 < a.source.ctors.length := by
      have := congrArg List.length hnames'
      simp only [List.length_map] at this
      omega
    obtain ⟨cctor, hcctor⟩ := List.exists_mem_of_length_pos hpos'
    obtain ⟨equation, hdefeq, fn, levels, args, hmaj⟩ :=
      hprior.constructor_equation a ha cctor hcctor
    obtain ⟨hconst, hres⟩ := hprior.container_ctor a ha cctor hcctor
    exact ⟨cctor, equation, hdefeq, ⟨fn, levels, args, hmaj⟩, hconst, hres⟩

/-- The family head selected by a generated case rule is either a source
family or the family of a certified container constructor whose recursor
equation is already installed in the base environment. -/
theorem InductiveSignature.CaseSchema.Certified.family_head_cases
    {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : InductiveSignature.CaseSchema.AppliedRule}
    (H : schema.Certified base source sourceBlock) (hgen : schema.Generates key owner rule) :
    schema.restoration.headName schema.signature.families[owner].name ∈ schema.sourceFamilies ∨
    ∃ (ctor : VConstVal) (equation : VDefEq), base.defeqs equation ∧
      equation.HasConstructorMajor ctor.name ∧
      base.constants ctor.name = some ctor.toVConstant ∧
      ∃ ls, ctor.type.forallResult.getAppFnArgs.1 =
        .const (schema.restoration.headName schema.signature.families[owner].name) ls := by
  obtain ⟨expanded, auxiliaries, hdata, hprior, hr, hnames, hdisj⟩ := H
  obtain ⟨rules, hrules, hmem, _⟩ := hgen
  obtain ⟨index, _⟩ := equation_of_mem hrules hmem
  obtain ⟨ctor, hctor, hown, _⟩ := view_constructor_eq_caseConstructor index
  obtain ⟨position, hposition, hget⟩ := List.mem_iff_getElem.mp hctor
  let original : Fin schema.signature.constructors.size := ⟨position, by simpa using hposition⟩
  have hoeq : schema.signature.constructors[original] = ctor := by
    simpa only [original, Fin.getElem_fin, Array.getElem_toList] using hget
  have hown' : schema.signature.constructors[original].owner = owner := by rw [hoeq]; exact hown
  rw [hr, ← hown']
  rcases hdata.family_head_cases hdisj hprior original with
    ⟨family, hsrc, hfn, hhn, _⟩ | h
  · left
    rw [hfn, hhn, hnames]
    exact List.mem_map.mpr ⟨family, hsrc, rfl⟩
  · exact .inr h

namespace VEnv

/-- `name` is a constant whose type returns an application of a declared constant `F` at which
no stored equation computes. This holds for the majors of stored equations. -/
def CtorResultRigid (env : VEnv) (name : Name) : Prop :=
  ∃ ci, env.constants name = some ci ∧ ∃ F ls, ci.type.forallResult.getAppFnArgs.1 = .const F ls ∧
    (∃ ciF, env.constants F = some ciF) ∧ env.Rigid F

private def ConstructorHeadsRigid (env : VEnv) : Prop :=
  (∀ equation, env.defeqs equation → ∀ name, equation.HasConstructorMajor name →
    (∃ ci, env.constants name = some ci) ∧ env.Rigid name ∧ env.CtorResultRigid name) ∧
  (∀ key schema, env.eliminators key schema →
    ∀ (owner : Fin schema.signature.families.size) rule, schema.Generates key owner rule →
    (∃ ci, env.constants rule.application.ctorName = some ci) ∧ env.Rigid rule.application.ctorName) ∧
  (∀ key schema, env.eliminators key schema → ∀ name ∈ schema.sourceFamilies,
    (∃ ci, env.constants name = some ci) ∧ env.Rigid name) ∧
  (∀ key schema, env.eliminators key schema →
    ∀ (owner : Fin schema.signature.families.size) rule, schema.Generates key owner rule →
    (∃ ci, env.constants (schema.restoration.headName schema.signature.families[owner].name) =
      some ci) ∧
    env.Rigid (schema.restoration.headName schema.signature.families[owner].name))

private theorem CtorResultRigid.mono {env env' : VEnv} (H : env.CtorResultRigid name)
    (hle : env ≤ env')
    (hr : ∀ {n}, (∃ ci, env.constants n = some ci) → env.Rigid n → env'.Rigid n) :
    env'.CtorResultRigid name := by
  obtain ⟨ci, hci, F, ls, hF, ⟨ciF, hciF⟩, hrF⟩ := H
  exact ⟨ci, hle.constants hci, F, ls, hF, ⟨ciF, hle.constants hciF⟩, hr ⟨ciF, hciF⟩ hrF⟩

private theorem ConstructorHeadsRigid.transport {env env' : VEnv}
    (H : ConstructorHeadsRigid env) (hle : env ≤ env')
    (hdf : env'.defeqs = env.defeqs) (helim : env'.eliminators = env.eliminators) :
    ConstructorHeadsRigid env' := by
  have move {name} : ((∃ ci, env.constants name = some ci) ∧ env.Rigid name) →
      ((∃ ci, env'.constants name = some ci) ∧ env'.Rigid name) := by
    rintro ⟨⟨ci, hci⟩, hr⟩
    exact ⟨⟨ci, hle.1 hci⟩, by simpa only [Rigid, hdf] using hr⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equation he name hn
    rw [hdf] at he
    obtain ⟨h1, h2, h3⟩ := H.1 equation he name hn
    exact ⟨(move ⟨h1, h2⟩).1, (move ⟨h1, h2⟩).2,
      h3.mono hle fun hc hr => (move ⟨hc, hr⟩).2⟩
  · intro key schema hs owner rule hr
    rw [helim] at hs
    exact move (H.2.1 key schema hs owner rule hr)
  · intro key schema hs name hn
    rw [helim] at hs
    exact move (H.2.2.1 key schema hs name hn)
  · intro key schema hs owner rule hr
    rw [helim] at hs
    exact move (H.2.2.2 key schema hs owner rule hr)

private theorem ConstructorHeadsRigid.addConst {env env' : VEnv}
    (H : ConstructorHeadsRigid env) (hadd : env.addConst name ci = some env') :
    ConstructorHeadsRigid env' :=
  H.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
    (VEnv.addConst_eliminators hadd)

private theorem ConstructorHeadsRigid.addConstVals {env env' : VEnv}
    (H : ConstructorHeadsRigid env) (hadd : env.addConstVals values = some env') :
    ConstructorHeadsRigid env' :=
  H.transport (VEnv.addConstVals_le hadd) (VEnv.addConstVals_defeqs hadd)
    (VEnv.addConstVals_eliminators hadd)

/-- Fresh recursor heads preserve constructors known before the recursor
constants and equations were added. -/
private theorem ConstructorHeadsRigid.addRules {pre env : VEnv} {rules : List VDefEq}
    (H : ConstructorHeadsRigid pre) (hle : pre ≤ env)
    (hdf : env.defeqs = pre.defeqs) (helim : env.eliminators = pre.eliminators)
    (hhead : ∀ df ∈ rules, ∀ name levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const name levels → pre.constants name = none)
    (hmajor : ∀ df ∈ rules, ∀ name, df.HasConstructorMajor name →
      (∃ ci, pre.constants name = some ci) ∧ pre.Rigid name ∧ pre.CtorResultRigid name) :
    ConstructorHeadsRigid (env.addDefEqRules rules) := by
  have hconstants : (env.addDefEqRules rules).constants = env.constants :=
    VEnv.addDefEqRules_constants _ _
  have heliminators : (env.addDefEqRules rules).eliminators = pre.eliminators :=
    (VEnv.addDefEqRules_eliminators _ _).trans helim
  have move {name} : ((∃ ci, pre.constants name = some ci) ∧ pre.Rigid name) →
      ((∃ ci, (env.addDefEqRules rules).constants name = some ci) ∧
        (env.addDefEqRules rules).Rigid name) := by
    rintro ⟨⟨ci, hci⟩, hr⟩
    refine ⟨⟨ci, by rw [hconstants]; exact hle.1 hci⟩, ?_⟩
    intro df hd levels hh
    rcases VEnv.addDefEqRules_defeqs_iff_mem_or.mp hd with hm | ho
    · have hn := hhead df hm name levels hh
      rw [hci] at hn
      contradiction
    · rw [hdf] at ho
      exact hr df ho levels hh
  have hle' : pre ≤ env.addDefEqRules rules := hle.trans VEnv.addDefEqRules_le
  have moveT {name} (h : (∃ ci, pre.constants name = some ci) ∧ pre.Rigid name ∧
      pre.CtorResultRigid name) :
      (∃ ci, (env.addDefEqRules rules).constants name = some ci) ∧
        (env.addDefEqRules rules).Rigid name ∧ (env.addDefEqRules rules).CtorResultRigid name :=
    ⟨(move ⟨h.1, h.2.1⟩).1, (move ⟨h.1, h.2.1⟩).2,
      h.2.2.mono hle' fun hc hr => (move ⟨hc, hr⟩).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro df hd name hn
    rcases VEnv.addDefEqRules_defeqs_iff_mem_or.mp hd with hm | ho
    · exact moveT (hmajor df hm name hn)
    · rw [hdf] at ho
      exact moveT (H.1 df ho name hn)
  · intro key schema hs owner rule hr
    rw [heliminators] at hs
    exact move (H.2.1 key schema hs owner rule hr)
  · intro key schema hs name hn
    rw [heliminators] at hs
    exact move (H.2.2.1 key schema hs name hn)
  · intro key schema hs owner rule hr
    rw [heliminators] at hs
    exact move (H.2.2.2 key schema hs owner rule hr)

private theorem ConstructorHeadsRigid.compileRules {pre env : VEnv}
    {recursors : List VConstVal} {rules : List VDefEq}
    (H : ConstructorHeadsRigid pre) (hrecs : pre.addConstVals recursors = some env)
    (hheads : ∀ df ∈ rules, ∃ recursor ∈ recursors, ∃ levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const recursor.name levels)
    (hmajor : ∀ df ∈ rules, ∀ name, df.HasConstructorMajor name →
      (∃ ci, pre.constants name = some ci) ∧ pre.Rigid name ∧ pre.CtorResultRigid name) :
    ConstructorHeadsRigid (env.addDefEqRules rules) := by
  apply H.addRules (VEnv.addConstVals_le hrecs) (VEnv.addConstVals_defeqs hrecs)
    (VEnv.addConstVals_eliminators hrecs) _ hmajor
  intro df hdf name levels hhead
  obtain ⟨recursor, hrecursor, ls, hr⟩ := hheads df hdf
  have hn : recursor.name = name := (VExpr.const.inj (hr.symm.trans hhead)).1
  rw [← hn]
  exact VEnv.addConstVals_names_fresh hrecs recursor hrecursor

private theorem ConstructorHeadsRigid.addProjections
    (H : ConstructorHeadsRigid env) : ConstructorHeadsRigid (env.addProjections entries) :=
  H.transport VEnv.addProjections_le (VEnv.addProjections_defeqs _ _)
    (VEnv.addProjections_eliminators _ _)

private theorem ConstructorHeadsRigid.addDefinitions {env env' : VEnv}
    (H : ConstructorHeadsRigid env) (hadd : env.addConsts cis = some env') :
    ConstructorHeadsRigid (env'.addDefEqs cis) := by
  rw [VEnv.addDefEqs_eq_addDefEqRules]
  apply H.compileRules (recursors := cis.map (·.toVConstVal))
    (by rwa [← VEnv.addConsts_eq_addConstVals])
  · intro df hdf
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hdf
    exact ⟨ci.toVConstVal, List.mem_map.mpr ⟨ci, hci, rfl⟩,
      VLevel.params ci.uvars, rfl⟩
  · intro df hdf name hn
    obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hdf
    obtain ⟨fn, levels, args, hm⟩ := hn
    cases hm

private theorem rigid_of_defeqs_eq {base env : VEnv} (h : env.defeqs = base.defeqs)
    (hr : base.Rigid name) : env.Rigid name := by
  simpa only [Rigid, h] using hr

private theorem ConstructorHeadsRigid.addQuot {env env' : VEnv}
    (H : ConstructorHeadsRigid env) (hordered : env.Ordered)
    (hadd : env.addQuot = some env') : ConstructorHeadsRigid env' := by
  simp [VEnv.addQuot] at hadd
  obtain ⟨e1, h1, e2, h2, e3, h3, pre, h4, rfl⟩ := hadd
  let recursors : List VConstVal := [
    { name := ``Quot.lift, toVConstant := quotLiftConst },
    { name := ``Quot.ind, toVConstant := quotIndConst }]
  have hrecs : e2.addConstVals recursors = some pre := by
    simp [recursors, VEnv.addConstVals, h3, h4]
  apply ((H.addConst h1).addConst h2).compileRules (rules := [quotDefEq]) hrecs
  · intro df hdf
    obtain rfl := List.mem_singleton.mp hdf
    exact ⟨{ name := ``Quot.lift, toVConstant := quotLiftConst }, by simp [recursors],
      [.param 0, .param 1], rfl⟩
  · intro df hdf name hm
    obtain rfl := List.mem_singleton.mp hdf
    have hmk : quotDefEq.HasConstructorMajor ``Quot.mk := ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
    have hn := hm.unique hmk
    subst name
    have hrigid := hordered.rigid_of_absent
      (VEnv.LE.constants_eq_none_left (VEnv.addConst_le h1) (VEnv.addConst_fresh h2))
    have hquot := hordered.rigid_of_absent (VEnv.addConst_fresh h1)
    have hdf2 := (VEnv.addConst_defeqs h2).trans (VEnv.addConst_defeqs h1)
    exact ⟨⟨quotMkConst, VEnv.addConst_self h2⟩, rigid_of_defeqs_eq hdf2 hrigid,
      quotMkConst, VEnv.addConst_self h2, ``Quot, _, rfl,
      ⟨quotConst, (VEnv.addConst_le h2).constants (VEnv.addConst_self h1)⟩,
      rigid_of_defeqs_eq hdf2 hquot⟩

private theorem ConstructorHeadsRigid.register {base env : VEnv}
    {schema : InductiveSignature.CaseSchema}
    (Hbase : ConstructorHeadsRigid base) (Henv : ConstructorHeadsRigid env)
    (hbase : base.Ordered) (hle : base ≤ env)
    (hcert : schema.Certified base source block)
    (hconstants : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hdf : env.defeqs = base.defeqs) :
    ConstructorHeadsRigid (env.addEliminator key schema) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Henv.1
  · intro k s hs owner rule hr
    rcases hs with ⟨rfl, rfl⟩ | hs
    · rcases hcert.case_constructor_cases hr with ⟨ctor, hc, hn⟩ | ⟨prior, hp, hpm⟩
      · obtain ⟨expanded, auxiliaries, hdata, _⟩ := hcert
        obtain ⟨types, ctors, ht, hct, _⟩ := hdata.sourceWF.2.2.2.2
        have hfresh := VEnv.LE.constants_eq_none_left (VEnv.addConstVals_le ht)
          (VEnv.addConstVals_names_fresh hct ctor hc)
        rw [hn]
        refine ⟨⟨ctor.toVConstant, ?_⟩, ?_⟩
        · exact hconstants ctor (List.mem_append_right _ (by rwa [hdata.ctors]))
        · exact rigid_of_defeqs_eq hdf (hbase.rigid_of_absent hfresh)
      · obtain ⟨⟨ci, hci⟩, hrigid, -⟩ := Hbase.1 prior hp _ hpm
        exact ⟨⟨ci, hle.constants hci⟩, rigid_of_defeqs_eq hdf hrigid⟩
    · exact Henv.2.1 k s hs owner rule hr
  · intro k s hs name hn
    rcases hs with ⟨rfl, rfl⟩ | hs
    · obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, hdisj⟩ := hcert
      rw [hnames] at hn
      obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hn
      obtain ⟨types, ctors, ht, _⟩ := hdata.sourceWF.2.2.2.2
      have hfresh := VEnv.addConstVals_names_fresh ht family.toVConstVal
        (List.mem_map.mpr ⟨family, hfamily, rfl⟩)
      refine ⟨⟨family.toVConstant, hconstants family.toVConstVal ?_⟩,
        rigid_of_defeqs_eq hdf (hbase.rigid_of_absent hfresh)⟩
      apply List.mem_append_left
      rw [hdata.types]
      exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
    · exact Henv.2.2.1 k s hs name hn
  · intro k s hs owner rule hr
    rcases hs with ⟨rfl, rfl⟩ | hs
    · rcases hcert.family_head_cases hr with horig | ⟨cctor, equation, hdefeq, hmaj, hconst, ls, hres⟩
      · obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, hdisj⟩ := hcert
        rw [hnames] at horig
        obtain ⟨family, hfamily, hfn⟩ := List.mem_map.mp horig
        rw [← hfn]
        obtain ⟨types, ctors, ht, _⟩ := hdata.sourceWF.2.2.2.2
        have hfresh := VEnv.addConstVals_names_fresh ht family.toVConstVal
          (List.mem_map.mpr ⟨family, hfamily, rfl⟩)
        refine ⟨⟨family.toVConstant, hconstants family.toVConstVal ?_⟩,
          rigid_of_defeqs_eq hdf (hbase.rigid_of_absent hfresh)⟩
        apply List.mem_append_left
        rw [hdata.types]
        exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
      · obtain ⟨-, -, ci, hci, F, ls', hF, ⟨ciF, hciF⟩, hFr⟩ := Hbase.1 equation hdefeq _ hmaj
        rw [hconst] at hci
        cases hci
        obtain rfl := (VExpr.const.inj (hF.symm.trans hres)).1
        exact ⟨⟨ciF, hle.constants hciF⟩, rigid_of_defeqs_eq hdf hFr⟩
    · exact Henv.2.2.2 k s hs owner rule hr

private theorem ConstructorHeadsRigid.addInduct
    (H : ConstructorHeadsRigid env) (hordered : env.Ordered)
    (hadd : env.AddInduct decl env') : ConstructorHeadsRigid env' := by
  cases hadd with
  | @intro block installed hdecl hcompile hblock helim hinstall =>
    obtain ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, _⟩ := hblock
    obtain ⟨eT, eC, hT', hC', helim⟩ := helim
    cases htypes.symm.trans hT'
    cases hctors.symm.trans hC'
    have hcanonical : VInductBlock.install env block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecs]
    have he : env' = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (hinstall.symm.trans hcanonical)
    subst env'
    have hdf0 : envCtors.defeqs = env.defeqs :=
      (VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)
    have hpre := (show ConstructorHeadsRigid (envCtors.addEliminators block.eliminators) by
      rcases helim with ⟨-, hE⟩ | ⟨key, schema, hE, ⟨hcert, hkey, -⟩, hprojs⟩
      · rw [hE]; exact (H.addConstVals htypes).addConstVals hctors
      · rw [hE]
        exact H.register ((H.addConstVals htypes).addConstVals hctors) hordered
          ((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)) hcert
          (fun value hv => by
            rcases List.mem_append.mp hv with hv | hv
            · exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hv)
            · exact VEnv.addConstVals_get hctors hv) hdf0 (key := key)).addProjections
      (entries := block.projections)
    have hle : env ≤ (envCtors.addEliminators block.eliminators).addProjections block.projections :=
      (VEnv.addConstVals_le htypes).trans <|
        (VEnv.addConstVals_le hctors).trans VEnv.addEliminators_addProjections_le
    have hdf : ((envCtors.addEliminators block.eliminators).addProjections
        block.projections).defeqs = env.defeqs := by
      simp only [VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs, hdf0]
    apply hpre.compileRules hrecs hcompile.equation_head_owned
    intro df hdfMem name hmajor
    obtain ⟨originName, horigin, hctor | ⟨prior, hprior, hpriorMajor⟩⟩ :=
      hcompile.equation_major_cases df hdfMem
    · have heq := hmajor.unique horigin
      obtain ⟨ctor, hctor, hname⟩ := hctor
      have hn : name = ctor.name := heq.trans hname
      rw [hn]
      have hc : ctor ∈ block.ctors := by rw [hcompile.ctors]; exact hctor
      have hfresh := VEnv.addConstVals_names_fresh hctors ctor hc
      have hr := hordered.rigid_of_absent
        (VEnv.LE.constants_eq_none_left (VEnv.addConstVals_le htypes) hfresh)
      have hci : ((envCtors.addEliminators block.eliminators).addProjections
          block.projections).constants ctor.name =
          some ctor.toVConstant := by
        simpa only [VEnv.addEliminators_constants, VEnv.addProjections_constants] using VEnv.addConstVals_get hctors hc
      obtain ⟨type, htype, hct⟩ := List.mem_flatMap.mp hctor
      obtain ⟨ls, hres⟩ := hcompile.ctor_result type htype ctor hct
      have ht : type.toVConstVal ∈ block.types := by
        rw [hcompile.types_eq]; exact List.mem_map.mpr ⟨type, htype, rfl⟩
      have hTfresh := VEnv.addConstVals_names_fresh htypes _ ht
      have hTr := hordered.rigid_of_absent hTfresh
      have hTc : ((envCtors.addEliminators block.eliminators).addProjections
          block.projections).constants type.name =
          some type.toVConstVal.toVConstant := by
        have := VEnv.addConstVals_get htypes ht
        simpa only [VEnv.addEliminators_constants, VEnv.addProjections_constants] using (VEnv.addConstVals_le hctors).constants this
      exact ⟨⟨ctor.toVConstant, hci⟩, rigid_of_defeqs_eq hdf hr,
        ctor.toVConstant, hci, type.name, ls, hres, ⟨_, hTc⟩, rigid_of_defeqs_eq hdf hTr⟩
    · have heq := hmajor.unique horigin
      rw [← heq] at hpriorMajor
      obtain ⟨⟨ci, hci⟩, hr, hres⟩ := H.1 prior hprior name hpriorMajor
      exact ⟨⟨ci, hle.constants hci⟩, rigid_of_defeqs_eq hdf hr,
        hres.mono hle fun _ hr => rigid_of_defeqs_eq hdf hr⟩

private theorem WF.constructorHeadsRigid {env : VEnv} (H : env.WF) : ConstructorHeadsRigid env := by
  suffices h : ∀ {ds env}, VEnv.WF' ds env → ConstructorHeadsRigid env from h H.choose_spec
  intro ds env H
  induction H with
  | empty =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro _ _ h; cases h
    · intro _ _ h; cases h
    · intro _ _ h; cases h
  | @decl d env' ds env hdecl hbase ih =>
    have hordered := (show env.WF from ⟨ds, hbase⟩).ordered
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd => exact ih.addConst hadd
    | «example» => exact ih
    | @«def» _ _ ci _ hadd =>
      exact ih.addDefinitions (cis := [ci]) (by simpa [VEnv.addConsts] using hadd)
    | mutualDef _ hadd _ => exact ih.addDefinitions hadd
    | quot _ hadd => exact ih.addQuot hordered hadd
    | induct hadd => exact ih.addInduct hordered hadd
  | inductEliminators hbase henv hle hreg hconstants hdefeqs _ _ _ _ ihBase ihEnv =>
    exact ihBase.register ihEnv (show VEnv.WF _ from ⟨_, hbase⟩).ordered
      hle hreg.certified hconstants hdefeqs
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    exact ihCtors.addProjections

/-- Every generated case constructor is rigid: no stored equation computes at it.
The proof uses the finite source compilation and declaration history, independently
of confluence, typing uniqueness, or constructor injectivity. -/
theorem WF.case_constructor_rigid {env : VEnv} (H : env.WF)
    (hregistered : env.eliminators block schema)
    {owner : Fin schema.signature.families.size}
    (hgenerated : schema.Generates block owner rule) :
    env.Rigid rule.application.ctorName :=
  (H.constructorHeadsRigid.2.1 _ _ hregistered _ _ hgenerated).2

/-- The source family behind a registered projection or case program is
rigid throughout declaration extension. This uses the registration certificate,
not a primitive projection entry or a general monotonicity assumption. -/
theorem WF.case_source_family_rigid {env : VEnv} (H : env.WF)
    (hregistered : env.eliminators key schema)
    (hfamily : name ∈ schema.sourceFamilies) : env.Rigid name :=
  (H.constructorHeadsRigid.2.2.1 _ _ hregistered _ hfamily).2

/-- The family head of every registered case owner that generates a rule is
a rigid constant. -/
theorem WF.case_family_head_rigid {env : VEnv} (H : env.WF)
    (hregistered : env.eliminators block schema)
    {owner : Fin schema.signature.families.size}
    (hgenerated : schema.Generates block owner rule) :
    env.Rigid (schema.restoration.headName schema.signature.families[owner].name) :=
  (H.constructorHeadsRigid.2.2.2 _ _ hregistered _ _ hgenerated).2

/-- The major constructor of every installed iota equation remains
rigid throughout all subsequent declarations. -/
theorem WF.installed_constructor_rigid {env : VEnv} (H : env.WF)
    (hinstalled : env.defeqs equation) (hmajor : equation.HasConstructorMajor name) :
    env.Rigid name :=
  (H.constructorHeadsRigid.1 _ hinstalled _ hmajor).2.1

/-- The constructor major of every installed equation returns an application
of a rigid family constant. -/
theorem WF.installed_constructor_result_rigid {env : VEnv} (H : env.WF)
    (hinstalled : env.defeqs equation) (hmajor : equation.HasConstructorMajor name) :
    env.CtorResultRigid name :=
  (H.constructorHeadsRigid.1 _ hinstalled _ hmajor).2.2

end VEnv
end Lean4Lean
