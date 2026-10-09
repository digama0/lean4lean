import Lean4Lean.Theory.Typing.Confluence.StructureConstructorHistory
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Inductive.RecursorEquationCoverage
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Inductive.CompilationNames

/-! A recursor rule at a structure constructor captures only the structure's
fields.

The restored major of a recursor equation is the constructor applied to its
constructor parameters followed by exactly the signature constructor's field
variables. The constructor parameter prefix is the declaration's own common
parameters for an original constructor, and the certified container
arguments for a nested auxiliary constructor. In either case, the installed
projection metadata of the constructor's family is the very declaration's
entry, whose parameter count is that prefix length. -/

namespace Lean4Lean
open VExpr

theorem VExpr.getAppFnArgs_go_snd (e : VExpr) (args : List VExpr) :
    (VExpr.getAppFnArgs.go e args).2 = (VExpr.getAppFnArgs.go e []).2 ++ args := by
  induction e generalizing args with
  | app f x ihf _ =>
    change (VExpr.getAppFnArgs.go f (x :: args)).2 = (VExpr.getAppFnArgs.go f [x]).2 ++ args
    rw [ihf, ihf (args := [x])]
    simp
  | _ => rfl

theorem List.eq_singleton_of_nodup_map {f : α → β} {l : List α} (hnodup : (l.map f).Nodup)
    (hx : x ∈ l) (hall : ∀ y ∈ l, f y = f x) : l = [x] := by
  have heq : ∀ y ∈ l, y = x := fun y hy =>
    List.eq_of_mem_of_nodup_map hnodup hy hx (hall y hy)
  cases l with
  | nil => cases hx
  | cons a t =>
    have ha := heq a (List.mem_cons_self ..)
    subst ha
    cases t with
    | nil => rfl
    | cons b t =>
      have hb := heq b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      subst hb
      simp at hnodup

theorem List.sublist_flatMap_of_mem' {f : α → List β} {l : List α} (h : a ∈ l) :
    List.Sublist (f a) (l.flatMap f) := by
  induction l with
  | nil => cases h
  | cons b t ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

namespace InductiveSignature

theorem RecursorData.ruleMajorArguments_of_stripLams {equation : VDefEq}
    (h : equation.lhs.stripLams = .app fn major) :
    RecursorData.ruleMajorArguments equation = major.getAppFnArgs.2 := by
  unfold RecursorData.ruleMajorArguments
  rw [h]
  change ((VExpr.getAppFnArgs.go fn [major]).2.getLast?.getD _).getAppFnArgs.2 = _
  rw [VExpr.getAppFnArgs_go_snd]
  simp

private theorem stripLams_wrap' (domains : List VExpr) (e : VExpr) :
    (VExpr.wrapLams domains e).stripLams = e.stripLams := by
  induction domains with
  | nil => rfl
  | cons d ds ih => exact ih

/-- The restored recursor equation's major is the restoration of the
generated constructor application. -/
theorem Instance.restored_equation_major_exact {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {equation : VDefEq}
    (hrestore : (compilationRestoration source auxiliaries).equation
      (g.equation index) = some equation) :
    ∃ fn major, equation.lhs.stripLams = .app fn major ∧
      (compilationRestoration source auxiliaries).expr
        (g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0) =
          some major := by
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
  rw [restoration_mkApps] at hfn
  simp only [bind, Option.bind_eq_some_iff] at hfn
  obtain ⟨args, _, hout⟩ := hfn
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using H.heads_not_recursors ctor.owner spec hs
  have hlhs : lhs' = .app
      (VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner)) (VLevel.params g.uvars)) args)
      major' := by
    simpa [head, Instance.recursorHead, Restoration.expr.go, hnone, VExpr.mkApps,
      List.foldl_append] using hout.symm
  refine ⟨VExpr.mkApps (.const (r.recursorName (g.recursorName ctor.owner)) (VLevel.params g.uvars)) args,
    major', ?_, hmajor⟩
  rw [hel, hlhs, stripLams_wrap']
  rfl

private theorem vars_restore (r : Restoration) (count below : Nat) :
    (vars count below).mapM r.expr = some (vars count below) := by
  unfold vars
  generalize (List.range count).reverse = is
  induction is with
  | nil => rfl
  | cons i is ih => simpa [List.mapM_cons, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using ih

/-- Restoring a generated constructor application keeps all field variables
and replaces at most the constructor parameter prefix. -/
theorem restored_ctorApp_count {r : Restoration} {np nf off : Nat}
    (hparams : ∀ h ∈ r.heads, h.nparams ≤ np) {output : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) (vars np off ++ vars nf 0)) = some output) :
    (r.heads.find? (fun h => h.auxiliary == name) = none ∧ output.getAppFnArgs.2.length = np + nf) ∨
    ∃ spec, r.heads.find? (fun h => h.auxiliary == name) = some spec ∧
      output.getAppFnArgs.2.length = spec.arguments.length + (np - spec.nparams) + nf := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) _) [] = _ at h
  rw [restoration_mkApps] at h
  simp [List.mapM_append, vars_restore] at h
  simp only [Restoration.expr.go] at h
  split at h
  · rename_i spec hspec
    have hle := hparams spec (List.mem_of_find?_eq_some hspec)
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · cases h
      refine .inr ⟨spec, hspec, ?_⟩
      rw [spine_mkApps_exact _ _ rfl]
      simp [vars]
      omega
  · rename_i hspec
    cases h
    refine .inl ⟨hspec, ?_⟩
    rw [spine_mkApps_exact _ _ rfl]
    simp [vars]

theorem Restoration.find_of_mem {r : Restoration} (hr : r.Scoped) (hmem : spec ∈ r.heads) :
    r.heads.find? (fun h => h.auxiliary == spec.auxiliary) = some spec := by
  cases hf : r.heads.find? (fun h => h.auxiliary == spec.auxiliary) with
  | none =>
    have hfalse := List.find?_eq_none.mp hf spec hmem
    simp at hfalse
  | some found =>
    have hfound := List.mem_of_find?_eq_some hf
    have hname : found.auxiliary = spec.auxiliary := by
      simpa using List.find?_some hf
    rw [List.eq_of_mem_of_nodup_map hr.1 hfound hmem hname]

theorem CompilationData.heads_nparams {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block) :
    ∀ h ∈ (compilationRestoration source auxiliaries).heads, h.nparams = s.params.length := by
  have hn := H.model.nparams.trans H.nparams
  intro head hhead
  obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
  change head ∈ _ :: _ at hhead
  rcases List.mem_cons.mp hhead with rfl | hhead
  · exact hn.symm
  · obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hhead
    exact hn.symm

/-- The origin of a signature constructor: an original constructor, or a
constructor of a certified container through its auxiliary name. -/
theorem CaseCompilationData.constructor_origin {s : InductiveSignature} (H : CaseCompilationData env source expanded s auxiliaries block)
    (index : Fin s.constructors.size) :
    (∃ type ∈ source.types, ∃ ctor ∈ type.ctors, s.constructors[index].name = ctor.name) ∨
    (∃ a ∈ auxiliaries, ∃ ctor ∈ a.source.ctors,
      s.constructors[index].name = a.constructorName ctor) := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
    (s.declarationFamily_mem s.constructors[index].owner)
  obtain ⟨ctor, hctor, hrelctor⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
    (s.declarationCtor_family index)
  have hname : s.constructors[index].name = ctor.name := hrelctor.1
  rcases List.mem_append.mp hfamily with hfamily | hfamily
  · exact .inl ⟨family, hfamily, ctor, hctor, hname⟩
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) _ hfamily
    have hnames := a.directFamily_heads hdf
    simp only [ContainerSpecialization.heads, List.map_cons, List.cons.injEq,
      List.map_map, Function.comp_def] at hnames
    have hm : ctor.name ∈ a.source.ctors.map (fun c => a.constructorName c) := by
      rw [hnames.2]
      exact List.mem_map.mpr ⟨ctor, hctor, rfl⟩
    obtain ⟨original, horiginal, hrestored⟩ := List.mem_map.mp hm
    exact ⟨a, ha, original, horiginal, hname.trans hrestored.symm⟩

end InductiveSignature

namespace CompiledInductive
open InductiveSignature

theorem ctor_names_nodup (H : CompiledInductive env source block) :
    (source.constructorConstants.map VConstVal.name).Nodup := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source block _ => (source.constructorConstants.map VConstVal.name).Nodup)
    (motive_2 := fun _ _ _ => True)
    (fun hdata _ _ => by
      have h := hdata.names
      rw [hdata.ctors] at h
      simp only [List.map_append] at h
      exact (List.nodup_append.mp (List.nodup_append.mp h).1).2.1)
    (fun _ _ _ ih => ih)
    trivial (fun _ _ _ _ _ _ _ => trivial) H

end CompiledInductive

namespace VEnv
open InductiveSignature
variable {env : VEnv}

theorem VInductBlock.install_le' (H : VInductBlock.install base block = some installed) :
    base ≤ installed := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact (((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
    (VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le hr))).trans VEnv.addDefEqRules_le

theorem VInductBlock.install_projection (H : VInductBlock.install base block = some installed)
    (hentry : entry ∈ block.projections) : installed.projections entry.typeName entry.info := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  simp only [VEnv.addDefEqRules_projections]
  rw [VEnv.addConstVals_projections hr, VEnv.addProjections_iff]
  exact .inl ⟨entry, hentry, rfl, rfl⟩

theorem ContainersInstalled.container_installed
    (H : ContainersInstalled env auxiliaries) (ha : a ∈ auxiliaries) :
    ∃ base block installed, CompiledInductive base a.container block ∧
      VInductBlock.install base block = some installed ∧ installed ≤ env := by
  revert H ha
  induction auxiliaries with
  | nil => intro _ ha; cases ha
  | cons b rest ih =>
    intro H ha
    cases H with
    | cons hc _ hi hle hrest =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨_, _, _, hc, hi, hle⟩
      · exact ih hrest ha

theorem ResultFamily.unique (H : env.ResultFamily c F) (H' : env.ResultFamily c F') : F = F' := by
  obtain ⟨ci, ls, hc, hh⟩ := H
  obtain ⟨ci', ls', hc', hh'⟩ := H'
  rw [hc] at hc'
  cases hc'
  exact (VExpr.const.inj (hh.symm.trans hh')).1

/-- The projection constructor of a registered structure returns that structure. -/
theorem Ordered.projection_resultFamily (henv : env.Ordered) (hp : env.projections family info) :
    env.ResultFamily info.ctorName family := by
  obtain ⟨decl, type, ctor, _, _, hname, _, _, _, _, _, _, hctorType, _, _, _, hraw, _⟩ :=
    henv.projectionShape hp
  obtain ⟨doms, result, heq, _, _, hhead, _⟩ := hraw.forallArity
  refine ⟨_, VLevel.params decl.uvars, henv.projectionConstructor hp, ?_⟩
  change info.ctorType.forallResult.getAppFnArgs.1 = _
  rw [← hctorType, heq, VExpr.forallResult_wrapForalls]
  have hres : result.forallResult = result := by
    cases result <;> first | rfl | cases hhead
  rw [hres, hhead, hname]

/-- A registered structure family installed by a compiled declaration has
exactly the projection metadata of that declaration: in particular its
constructor and parameter count. -/
theorem CompiledInductive.family_projection (henv : env.WF)
    (hc : CompiledInductive b source block) (hi : VInductBlock.install b' block = some installed)
    (hle : installed ≤ env) (htype : type ∈ source.types) (hctor : ctor ∈ type.ctors)
    (hp : env.projections type.name info) :
    type.ctors = [ctor] ∧ info.ctorName = ctor.name ∧ info.nparams = source.nparams := by
  have hK := henv.structureCtorCoherent
  have hall : ∀ c2 ∈ type.ctors, c2.name = info.ctorName := by
    intro c2 hc2
    have hmem : c2 ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨type, htype, hc2⟩
    obtain ⟨eq, heq, fn, lv, args, hs⟩ := hc.constructor_equation c2 hmem
    have hd : env.defeqs eq := hle.defeqs (VInductBlock.install_rule hi heq)
    obtain ⟨ls, hres⟩ := hc.ctor_result type htype c2 hc2
    have hlookup : env.constants c2.name = some c2.toVConstant :=
      hle.constants (VInductBlock.install_ctor_lookup hi (by rw [hc.ctors_eq]; exact hmem))
    exact hK type.name info hp eq c2.name hd ⟨fn, lv, args, hs⟩ ⟨_, ls, hlookup, hres⟩
  have hnodup : (type.ctors.map VConstVal.name).Nodup := by
    have h := hc.ctor_names_nodup
    unfold VInductDecl.constructorConstants at h
    rw [List.map_flatMap] at h
    exact List.Nodup.sublist (List.sublist_flatMap_of_mem' (f := fun t => t.ctors.map VConstVal.name) htype) h
  have hsingle : type.ctors = [ctor] := List.eq_singleton_of_nodup_map hnodup hctor
    (fun y hy => (hall y hy).trans (hall ctor hctor).symm)
  have hentry : (⟨type.name, ⟨source.uvars, source.nparams, type.numIndices, type.resultLevel,
      ctor.name, ctor.type⟩⟩ : VProjectionEntry) ∈ source.projectionEntries :=
    List.mem_filterMap.mpr ⟨type, htype, by rw [hsingle]⟩
  have hp' := hle.projections (VInductBlock.install_projection hi (by rw [hc.projections_eq]; exact hentry))
  have := henv.ordered.projections_unique hp hp'
  subst this
  exact ⟨hsingle, rfl, rfl⟩

/-- A recursor rule whose major constructor is a registered structure's
constructor has at least the structure's parameters before the captured
fields of its major. -/
theorem RecursorRegistered.rule_param_count (henv : env.WF)
    (hr : RecursorRegistered env data) {index : Fin data.schema.signature.constructors.size}
    {equation : VDefEq} (hg : data.equation index = some equation)
    (hp : env.projections family info) (hcc : data.ruleConstructor index = info.ctorName) :
    info.nparams + data.schema.signature.constructors[index].fields.length ≤
      (RecursorData.ruleMajorArguments equation).length := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hres, _, hu, hlv, ht, hi, he⟩ := hr
  have hinstance : data.recursorInstance = g := by
    cases g
    simp only [RecursorData.recursorInstance, Instance.mk.injEq]
    exact ⟨hu, hlv, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  subst hinstance
  have hrestore : (compilationRestoration source auxiliaries).equation
      (data.recursorInstance.equation index) = some equation := by
    simpa only [RecursorData.equation, hres] using hg
  obtain ⟨fn, major, hs, hmajor⟩ := Instance.restored_equation_major_exact hdata index hrestore
  rw [RecursorData.ruleMajorArguments_of_stripLams hs]
  have hnp := hdata.model.nparams.trans hdata.nparams
  have hbaseEnv : base ≤ env := hbase.trans ((VInductBlock.install_le' hi).trans he)
  have hcompiled : CompiledInductive base source block := .intro hdata hprior
  have hcn : (compilationRestoration source auxiliaries).headName
      data.schema.signature.constructors[index].name = info.ctorName := by
    rw [← hcc]; unfold RecursorData.ruleConstructor; rw [hres]
  have hfamily : ∀ (ctor : VConstVal) F, env.ResultFamily ctor.name F → ctor.name = info.ctorName → family = F :=
    fun ctor F h hn => ((henv.ordered.projection_resultFamily hp).unique (hn ▸ h))
  have hheads : ∀ h ∈ (compilationRestoration source auxiliaries).heads,
      h.nparams ≤ data.schema.signature.params.length :=
    fun h hh => Nat.le_of_eq (hdata.heads_nparams h hh)
  unfold Instance.constructorApp at hmajor
  obtain ⟨envTypes, direct, _, _, hwf, _⟩ := hdata.correspondence
  have hcontainer : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors, ctor.name = info.ctorName →
      info.nparams = a.arguments.length := by
    intro a ha ctor hctor hname
    obtain ⟨b0, cblock, inst0, hc0, hi0, hle0⟩ := VEnv.ContainersInstalled.container_installed hprior ha
    have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
    have hmem : ctor ∈ a.container.constructorConstants := List.mem_flatMap.mpr ⟨a.source, hsrc, hctor⟩
    obtain ⟨ls, hres'⟩ := hc0.ctor_result a.source hsrc ctor hctor
    have hlookup : env.constants ctor.name = some ctor.toVConstant :=
      (hle0.trans hbaseEnv).constants (VInductBlock.install_ctor_lookup hi0 (by rw [hc0.ctors_eq]; exact hmem))
    have hF := hfamily ctor a.source.name ⟨_, ls, hlookup, hres'⟩ hname
    subst hF
    obtain ⟨_, _, hnparams⟩ := CompiledInductive.family_projection henv hc0 hi0 (hle0.trans hbaseEnv)
      hsrc hctor hp
    rw [hnparams, (hwf a ha).1]
  rcases restored_ctorApp_count hheads hmajor with ⟨hfind, hlen⟩ | ⟨spec, hfind, hlen⟩
  · rw [hlen]
    rcases hdata.constructor_origin index with ⟨type, htype, ctor, hctor, hn⟩ | ⟨a, ha, ctor, hctor, hn⟩
    · have hsourceName : data.schema.signature.constructors[index].name ∈ familyNames source.types := by
        rw [hn]
        exact List.mem_flatMap.mpr ⟨type, htype, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      rw [hdata.headName_source hsourceName, hn] at hcn
      have hmem : ctor ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨type, htype, hctor⟩
      obtain ⟨ls, hres'⟩ := hcompiled.ctor_result type htype ctor hctor
      have hlookup : env.constants ctor.name = some ctor.toVConstant :=
        he.constants (VInductBlock.install_ctor_lookup hi (by rw [hdata.ctors]; exact hmem))
      have hF := hfamily ctor type.name ⟨_, ls, hlookup, hres'⟩ hcn
      subst hF
      obtain ⟨_, _, hnparams⟩ := CompiledInductive.family_projection henv hcompiled hi he htype hctor hp
      omega
    · have hmem : (⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels, a.arguments⟩ :
          HeadSpecialization) ∈
          (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hf := Restoration.find_of_mem hdata.restorationScoped hmem
      rw [← hn, hfind] at hf
      cases hf
  · rw [hlen]
    rcases hdata.constructor_origin index with ⟨type, htype, ctor, hctor, hn⟩ | ⟨a, ha, ctor, hctor, hn⟩
    · have hsourceName : data.schema.signature.constructors[index].name ∈ familyNames source.types := by
        rw [hn]
        exact List.mem_flatMap.mpr ⟨type, htype, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hm := List.mem_of_find?_eq_some hfind
      have hname : spec.auxiliary = data.schema.signature.constructors[index].name := by
        simpa using List.find?_some hfind
      exact (hdata.source_head_disjoint hsourceName (List.mem_map.mpr ⟨spec, hm, hname⟩)).elim
    · have hmem : (⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels, a.arguments⟩ :
          HeadSpecialization) ∈
          (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hf := Restoration.find_of_mem hdata.restorationScoped hmem
      rw [← hn, hfind] at hf
      cases hf
      rw [hn, hdata.headName_auxiliary_constructor ha hctor] at hcn
      have := hcontainer a ha ctor hctor hcn
      simp only
      omega

end VEnv
end Lean4Lean
