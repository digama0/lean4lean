import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyKernel
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerConstructorShape

/-! # The constructors of the restored rules

The facts `NestedRun.assemblyRecursors` (`AssemblyRecursors.lean`) reads about the constructor
of every restored recursor rule: its kernel `ctorInfo` and parameter count, its constructor
shape in the source constructor stage, the source-or-container alternative, and their
distinctness within one family. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### The constructors of one family of a compiled signature -/

theorem list_filter_map_eq_filterMap {α β : Type _} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter p).map f = l.filterMap fun x => if p x then some (f x) else none
  | [] => rfl
  | x :: l => by
    by_cases h : p x <;> simp [List.filter_cons, h, list_filter_map_eq_filterMap p f l]

/-- The names of the constructors a family owns, in generation order, are those of its family
in the signature's declaration. -/
theorem ownedConstructors_names (s : InductiveSignature) (owner : Fin s.families.size) :
    (s.ownedConstructors owner).map (fun index => s.constructors[index].name) =
      (s.declarationFamily owner).ctors.map (·.name) := by
  unfold InductiveSignature.ownedConstructors InductiveSignature.declarationFamily
  rw [list_filter_map_eq_filterMap, List.map_filterMap]
  have hlist : s.constructors.toList = (List.finRange s.constructors.size).map
      (fun i => s.constructors[i]) := by
    apply List.ext_getElem <;> simp
  rw [hlist, List.filterMap_map]
  congr 1
  funext i
  simp only [Function.comp_def, beq_iff_eq, Fin.ext_iff]
  split <;> simp

/-- The restored head name of a name that is not an auxiliary head is the name itself. -/
theorem Restoration.restoredHeadName_of_not_head {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) : r.restoredHeadName name = name := by
  simp only [Restoration.restoredHeadName, Restoration.heads_find?_eq_none h]

/-- The restored head name of an auxiliary head is its target. -/
theorem Restoration.restoredHeadName_of_mem {r : Restoration} (hr : r.Scoped)
    {spec : HeadSpecialization} (hmem : spec ∈ r.heads) :
    r.restoredHeadName spec.auxiliary = spec.target := by
  simp only [Restoration.restoredHeadName, Restoration.find?_of_nodup hr.1 hmem]

/-- The two kinds of family of a compiled signature: a source family, whose constructors are the
source family's (their restored names are themselves), or the family of a container
specialization, whose constructors are the renamed container constructors (restored to the
container constructors). -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.familyCases {env : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {auxiliaries : List ContainerSpecialization}
    {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) :
    (∃ hsrc : owner.val < source.types.length,
      s.families[owner].name = (source.types[owner.val]'hsrc).name ∧
      (s.declarationFamily owner).ctors.map (·.name) =
        (source.types[owner.val]'hsrc).ctors.map (·.name)) ∨
    (∃ _hge : source.types.length ≤ owner.val, ∃ hidx : owner.val - source.types.length <
        auxiliaries.length,
      s.families[owner].name = (auxiliaries[owner.val - source.types.length]'hidx).auxiliary ∧
      (s.declarationFamily owner).ctors.map (·.name) =
        (auxiliaries[owner.val - source.types.length]'hidx).source.ctors.map
          (auxiliaries[owner.val - source.types.length]'hidx).constructorName) := by
  obtain ⟨envTypes', direct, -, hdirect, -, Hfam⟩ := Hd.correspondence
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have howner : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have howner' : owner.val < (source.types ++ direct).length := hlen ▸ howner
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val howner howner'
  have hdf : s.declaration.types[owner.val]'howner = s.declarationFamily owner := by
    simp [InductiveSignature.declaration, InductiveSignature.declarationFamily]
  rw [hdf] at Hat
  have hnames : (s.declarationFamily owner).ctors.map (·.name) =
      ((source.types ++ direct)[owner.val]'howner').ctors.map (·.name) :=
    List.Forall₂.map_eq (fun _ _ h => h.1) Hat.constructors
  have hfam : s.families[owner].name = ((source.types ++ direct)[owner.val]'howner').name :=
    Hat.name
  by_cases hsrc : owner.val < source.types.length
  · left
    refine ⟨hsrc, ?_, ?_⟩
    · rw [hfam, List.getElem_append_left hsrc]
    · rw [hnames, List.getElem_append_left hsrc]
  · right
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := howner'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length :=
      (Lean4Lean.List.Forall₂.length_eq hFdirect) ▸ hidx
    have hd := Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hheads := ContainerSpecialization.directFamily_heads hd
    simp only [ContainerSpecialization.heads, List.map_cons, List.map_map, List.cons.injEq,
      Function.comp_def] at hheads
    refine ⟨hge, hidx', ?_, ?_⟩
    · rw [hfam, List.getElem_append_right hge]; exact hheads.1.symm
    · rw [hnames, List.getElem_append_right hge, ← hheads.2]

/-- The constructor names of a family of a declaration with distinct names are distinct. -/
theorem familyCtorNames_nodup {decl : VInductDecl} (hnd : decl.sourceNames.Nodup)
    {family : VInductiveType} (hfamily : family ∈ decl.types) :
    (family.ctors.map (·.name)).Nodup := by
  have h := (List.nodup_append.mp hnd).2.1
  simp only [VInductDecl.constructorConstants, List.flatMap, List.map_flatten,
    List.map_map] at h
  exact h.sublist (List.sublist_flatten_of_mem
    (List.mem_map_of_mem (f := List.map VConstVal.name ∘ VInductiveType.ctors) hfamily))

theorem list_nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => .nil
  | x :: l, H, hnd => by
    rw [List.nodup_cons] at hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_, list_nodup_map_on
      (fun a ha b hb => H a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) hnd.2⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    exact hnd.1 (H x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hxy.symm ▸ hy)

/-- The constructor names of a family of a compiled signature are distinct. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.declarationFamily_names_nodup {env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) :
    ((s.declarationFamily owner).ctors.map (·.name)).Nodup := by
  obtain ⟨family, hfamily, -, -, -, -, hnames⟩ := Hd.model.family owner
  rw [hnames]
  exact familyCtorNames_nodup Hd.expandedWF.2.1 hfamily

/-- The restored constructor head of a constructor name of a source family is itself. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.restoredHeadName_source {env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {name : Name} (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).restoredHeadName name = name :=
  Restoration.restoredHeadName_of_not_head
    (Hd.toCaseCompilationData.source_head_disjoint hname)

/-- The restored constructor head of a renamed container constructor is the container
constructor. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.restoredHeadName_auxiliary {env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries) {c : VConstVal}
    (hc : c ∈ a.source.ctors) :
    (compilationRestoration source auxiliaries).restoredHeadName (a.constructorName c) =
      c.name := by
  have hmem : HeadSpecialization.mk (a.constructorName c) source.uvars source.nparams c.name
      a.levels a.arguments ∈ (compilationRestoration source auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  exact Restoration.restoredHeadName_of_mem Hd.restorationScoped hmem

/-- The restored family head of a source family: the family itself, at the instance's levels
and the parameter variables. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.restoredFamilyHead_source
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) (hsrc : owner.val < source.types.length)
    (hname : s.families[owner].name = (source.types[owner.val]'hsrc).name) :
    g.restoredFamilyHead (compilationRestoration source auxiliaries) owner =
      some ⟨s.families[owner].name, g.levels, vars s.params.length 0⟩ := by
  have hmemF : s.families[owner].name ∈ familyNames source.types :=
    mem_familyNames.mpr ⟨_, List.getElem_mem hsrc, .inl hname⟩
  have hfind : (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == s.families[owner].name) = none :=
    Restoration.heads_find?_eq_none (Hd.toCaseCompilationData.source_head_disjoint hmemF)
  have hrecName : (compilationRestoration source auxiliaries).recursorName
      s.families[owner].name = s.families[owner].name := by
    unfold Restoration.recursorName
    cases hr : (compilationRestoration source auxiliaries).recursors.find?
        (fun p => p.1 == s.families[owner].name) with
    | none => rfl
    | some pair =>
      have hm := List.mem_of_find?_eq_some hr
      have hn : pair.1 = s.families[owner].name := by simpa using List.find?_some hr
      have hrec := Hd.recursor_source_mem hm
      rw [hn] at hrec
      exact (Hd.source_recursors_disjoint hmemF hrec).elim
  simp only [Instance.restoredFamilyHead, Instance.familyApp,
    InductiveSignature.familyApp, List.append_nil]
  rw [(compilationRestoration source auxiliaries).expr_mkApps,
    (compilationRestoration source auxiliaries).mapM_expr_vars]
  simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
  simp only [Option.bind_eq_bind, Option.bind_some,
    VerifyInductive.VExpr.getAppFnArgs_mkApps]
  rfl

/-- The restored family head of an auxiliary family: the container family applied to the
specialization arguments. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.restoredFamilyHead_auxiliary
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) {a : ContainerSpecialization} (ha : a ∈ auxiliaries)
    (hname : s.families[owner].name = a.auxiliary) :
    g.restoredFamilyHead (compilationRestoration source auxiliaries) owner =
      some ⟨a.source.name, a.levels.map (·.inst g.levels),
        a.arguments.map (fun arg => arg.instL g.levels)⟩ := by
  obtain ⟨envTypes', direct, -, -, hwellFormed, -⟩ := Hd.correspondence
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  let h : HeadSpecialization :=
    ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
  have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have hfind : (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == s.families[owner].name) = some h := by
    rw [hname]
    exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
  obtain ⟨-, hargsClosed, -, -, -⟩ := hwellFormed a ha
  have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
    intro arg harg
    rw [hnp]
    exact (hargsClosed arg harg).instL
  have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
      (vars source.nparams k)) =
        a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
    intro k
    apply List.map_congr_left
    intro arg harg
    rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
  simp only [Instance.restoredFamilyHead, Instance.familyApp,
    InductiveSignature.familyApp, List.append_nil]
  rw [(compilationRestoration source auxiliaries).expr_mkApps,
    (compilationRestoration source auxiliaries).mapM_expr_vars]
  simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
    hlevelsLen, h, bne_self_eq_false, Bool.false_or, length_vars, hnp]
  rw [if_neg (by simp), List.take_of_length_le (by simp),
    List.drop_of_length_le (by simp), hinst 0]
  simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
  rfl

end VerifyInductive

namespace VerifyInductive

/-- A raw constructor shape ends in a constant-headed codomain. -/
theorem _root_.Lean4Lean.VInductDecl.RawCtorShape.ctorHeaded {decl : VInductDecl}
    {t : VInductiveType} {ctor : VConstVal} (H : decl.RawCtorShape t ctor) :
    ctor.type.CtorHeaded := by
  obtain ⟨doms, result, htype, -, -, hhead⟩ := H
  refine ⟨t.name, VLevel.params decl.uvars, ?_⟩
  have hr : result = VExpr.mkApps (.const t.name (VLevel.params decl.uvars))
      result.getAppFnArgs.2 := by
    rw [← hhead]; exact (VExpr.mkApps_getAppFnArgs_eq result).symm
  have hfn : result.getAppFn = .const t.name (VLevel.params decl.uvars) := by
    rw [hr]; simp [VExpr.getAppFn]
  have hbody : result.piBody = result := by
    clear hr htype hhead; cases result <;> simp_all [VExpr.piBody, VExpr.getAppFn]
  have hpb : ∀ ds : List VExpr, (VExpr.wrapForalls ds result).piBody = result.piBody := by
    intro ds; induction ds with
    | nil => rfl
    | cons d ds ih => exact ih
  rw [htype, hpb, hbody, hfn]

/-- The container application recorded for an auxiliary family by lowering is a kernel
inductive family applied to exactly its parameters (`NestedLoweringOutputClosed.nested_app`, from
the syntactic source checks). -/
theorem NestedRun.auxiliaryNestedApp
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {venv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment} {ves : VEnvs}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes venv sourceDecl lparams nparams isUnsafe
      safety outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {n : Name} {nested : Expr} (hfind : result.aux2nested.find? n = some nested) :
    ∃ (I : Name) (ls : List Level) (info : InductiveVal) (args : Array Expr),
      nested = mkAppN (.const I ls) args ∧ sourceProdEnv.find? I = some (.inductInfo info) ∧
      args.size = info.numParams := by
  obtain ⟨finalState, Hrun, -, -⟩ := E.lowering
  obtain ⟨C⟩ := Hrun.cachedAuxiliaryFamilyOfLookup (VEnvs.WF.environmentTypesClosed wf)
    wf.inductivesClosed Hsources rfl (by rfl) hfind
  obtain ⟨args', hsize, heq⟩ := Expr.closure_mkAppRange_const C.origin.generated.sourceName
    C.origin.generated.levels C.origin.generated.nestedNParams C.origin.generated.args
    C.origin.generated.argsArity C.origin.generated.selection.fvars result.params
  refine ⟨C.origin.generated.sourceName, C.origin.generated.levels, _, args', ?_,
    C.origin.generated.built.lookup, hsize.trans C.origin.generated.sourceNumParams⟩
  refine C.nested_eq.symm.trans ?_
  rw [C.origin.generated.built.nested, C.origin.generated.selection.expressions]
  exact heq

/-- The kernel family of a specialization's container: the container family is a kernel
inductive family whose parameter count is the number of specialization arguments. -/
theorem NestedRun.containerFamilyKernel
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries) :
    ∃ info : InductiveVal, sourceProdEnv.find? a.source.name = some (.inductInfo info) ∧
      info.numParams = a.arguments.length := by
  obtain ⟨nested, hn⟩ := D.familyLookup a ha
  obtain ⟨b, hb, hba, envS, domains, lvls, Ys, -, hab, -, hYs⟩ := D.familyKey _ nested hn
  -- the recorded application is that of `a`
  have key : ∀ l : List ContainerSpecialization,
      (l.flatMap (·.headNames)).Nodup → (l.map (·.auxiliary)).Nodup := by
    intro l h
    induction l with
    | nil => exact .nil
    | cons x xs ih =>
      simp only [List.flatMap_cons, InductiveSignature.ContainerSpecialization.headNames,
        List.cons_append] at h
      obtain ⟨h1, h2⟩ := List.nodup_cons.mp h
      have h3 := (List.nodup_append.mp h2).2.1
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih h3⟩
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
      exact h1 (List.mem_append_right _ (List.mem_flatMap.mpr ⟨y, hy, by
        simp only [hyx]
        exact List.mem_cons_self⟩))
  have hauxNodup : (auxiliaries.map (·.auxiliary)).Nodup := key _ D.headNodup
  have hba' : b = a := List.eq_of_mem_of_nodup_map hauxNodup hb ha hba
  subst hba'
  obtain ⟨I, ls, info, args, rfl, hI, hsize⟩ := E.auxiliaryNestedApp wf Hsources hn
  obtain ⟨xs, hxs⟩ := D.paramsFVars
  rw [hxs, Expr.abstractN_eq, Expr.abstractN_mkAppN, Expr.mkAppN_eq_mkAppList] at hab
  have hfn := congrArg Expr.getAppFn hab
  have hargs := congrArg Expr.getAppArgsList hab
  simp only [Expr.abstractN, Expr.getAppFn_mkAppList_const] at hfn
  simp only [Expr.abstractN, Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_const,
    List.nil_append] at hargs
  cases hfn
  refine ⟨info, hI, ?_⟩
  rw [← hsize, ← Lean4Lean.List.Forall₂.length_eq hYs, ← hargs]
  simp

/-- The constructors of a specialization's container are the constructors listed by the kernel
family of the container, given the kernel families of the specialization list (`Hkernel`, which
`NestedRun.restorationTablesRestoringAll` provides for the run's own list: the abstract installed
container does not determine them). -/
theorem NestedRun.containerConstructorListed
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hkernel : ∀ a ∈ auxiliaries, ∃ info,
      sourceProdEnv.find? a.source.name = some (.inductInfo info) ∧
        info.ctors = a.source.ctors.map (·.name))
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries)
    {c : VConstVal} (hc : c ∈ a.source.ctors) {info : InductiveVal}
    (hI : sourceProdEnv.find? a.source.name = some (.inductInfo info)) :
    c.name ∈ info.ctors := by
  have := E; have := wf; have := Hsources; have := D
  obtain ⟨info', h', hctors⟩ := Hkernel a ha
  rw [hI] at h'
  cases h'
  rw [hctors]
  exact List.mem_map_of_mem hc

/-- The kernel constructor of a container constructor: a constructor `c` of the container family
of a specialization `a` is a kernel constructor of the output whose parameter count is the number
of specialization arguments. The kernel family is the one lowering recorded for `a`
(`NestedRun.containerFamilyKernel`), its constructors carry its parameter count
(`ConstructorParameterAlignment` of the source environment), and the output extends the source
environment. -/
theorem NestedRun.containerConstructorKernel
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hkernel : ∀ a ∈ auxiliaries, ∃ info,
      sourceProdEnv.find? a.source.name = some (.inductInfo info) ∧
        info.ctors = a.source.ctors.map (·.name))
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries)
    {c : VConstVal} (hc : c ∈ a.source.ctors) :
    ∃ cval : ConstructorVal, outEnv.constants.find? c.name = some (.ctorInfo cval) ∧
      cval.numParams = a.arguments.length := by
  obtain ⟨info, hI, hnp⟩ := E.containerFamilyKernel wf Hsources D ha
  have hmem := E.containerConstructorListed wf Hsources D Hkernel ha hc hI
  obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨Al⟩ := wf.constructorParameterAlignment (safety := .unsafe) _ info hI
    (by split <;> decide) i hi
  have hsourceWF : sourceProdEnv.constants.WF := by
    have h := E.contextWF.checking.tr.map_wf
    rwa [E.context_env] at h
  obtain ⟨_, Hfresh⟩ := E.restoration.freshExtension hsourceWF
  have houtWF : outEnv.constants.WF := Hfresh.targetWF hsourceWF
  have hlookup := Hfresh.preservesSourceFind hsourceWF Al.lookup
  rw [hci, Kernel.Environment.find?_eq_constants houtWF] at hlookup
  exact ⟨Al.info, hlookup, Al.numParams.trans hnp⟩

/-- **The constructor of every restored rule**: the restored constructor of a generated
constructor `index` of family `owner` is a kernel constructor of the output whose parameter
count is the restored family head's argument count (the source family's parameters, or the
container's specialization arguments), a constructor of the source constructor stage with the
constructor shape at that count plus the field count, and either one of the source
declaration's constructors at its parameter count or a constructor of a container installed
below at the container's.

For a source owner `restoredHeadName` is the identity on its constructors, the constructor's
kernel `ctorInfo` is read off the output's family lookups (`NestedRun.inductInfosFromDeclOfArity`,
`NestedRun.coverOfArity`), and its shape off the lowered constructor
(`NestedRun.loweredConstructorShape`) through the constructor arities `Harity`. For an auxiliary
owner the restored constructor is a constructor `c` of the container (`NestedRun.containerConstructorKernel`,
`NestedRun.containerConstructorShape`). -/
theorem NestedRun.restoredRuleConstructors
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hcert : ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries)
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (Harity : sourceDecl.ConstructorArityPrefix E.lowered.loweredDecl)
    {envTypes : VEnv} {ctx : List VExpr} {generated : List VInductiveType}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes ctx sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (Hkernel : ∀ a ∈ auxiliaries, ∃ info,
      sourceProdEnv.find? a.source.name = some (.inductInfo info) ∧
        info.ctors = a.source.ctors.map (·.name))
    (owner : Fin E.lowered.signature.families.size) {head : RestoredFamilyHead}
    (hhead : E.lowered.generatedInstance.restoredFamilyHead
      (compilationRestoration sourceDecl auxiliaries) owner = some head)
    (index : Fin E.lowered.signature.constructors.size)
    (hown : E.lowered.signature.constructors[index].owner = owner) :
    (∃ cval : ConstructorVal, outEnv.constants.find?
        ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name) = some (.ctorInfo cval) ∧
      cval.numParams = head.arguments.length) ∧
    (∃ ci, E.sourceCore.envCtors.constants
        ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name) = some ci ∧
      ci.type.CtorShape (head.arguments.length +
        E.lowered.signature.constructors[index].fields.length)) ∧
    ((∃ c ∈ sourceDecl.constructorConstants,
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name = c.name ∧
        head.arguments.length = sourceDecl.nparams) ∨
      (∃ Dc, VEnv.InstalledBelow (ves.venv (if isUnsafe then .unsafe else .safe)) Dc ∧
        ∃ c ∈ Dc.constructorConstants,
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            E.lowered.signature.constructors[index].name = c.name ∧
          head.arguments.length = Dc.nparams)) := by
  have := Hcert
  have hnp : E.lowered.signature.params.length = sourceDecl.nparams := Hdata.model.nparams.trans Hdata.nparams
  have hx : E.lowered.signature.constructors[index].name ∈ (E.lowered.signature.declarationFamily owner).ctors.map (·.name) := by
    have h := E.lowered.signature.declarationCtor_family index
    rw [hown] at h
    exact List.mem_map_of_mem h
  rcases Hdata.familyCases owner with ⟨hsrc, hfamName, hnames⟩ |
      ⟨hge, hidx, hfamName, hnames⟩
  · -- a source family
    have hh := Hdata.restoredFamilyHead_source owner hsrc hfamName
    rw [hhead] at hh
    cases hh
    rw [hnames] at hx
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    simp only [List.getElem_map, List.length_map] at hj hjx
    let sc := (sourceDecl.types[owner.val]'hsrc).ctors[j]'hj
    have hscMem : sc ∈ sourceDecl.constructorConstants :=
      List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, List.getElem_mem hj⟩
    have hrestored : (compilationRestoration sourceDecl auxiliaries).restoredHeadName E.lowered.signature.constructors[index].name = sc.name := by
      rw [← hjx]
      exact Hdata.restoredHeadName_source (mem_familyNames.mpr
        ⟨_, List.getElem_mem hsrc, .inr ⟨sc, List.getElem_mem hj, rfl⟩⟩)
    have hargs : (vars E.lowered.signature.params.length 0).length = sourceDecl.nparams := by
      rw [length_vars, hnp]
    simp only [hrestored, hargs]
    -- the kernel constructor
    have hsourceWF : sourceProdEnv.constants.WF := by
      have h := E.contextWF.checking.tr.map_wf
      rwa [E.context_env] at h
    obtain ⟨_, Hfresh⟩ := E.restoration.freshExtension hsourceWF
    have houtWF : outEnv.constants.WF := Hfresh.targetWF hsourceWF
    have horig := E.inductInfosFromDeclOfArity Harity Hsources wf.constructorOwners
    obtain ⟨v, hv, hnone⟩ := E.coverOfArity Harity Hsources wf.constructorOwners
      _ (List.getElem_mem hsrc)
    rw [Kernel.Environment.find?_eq_constants houtWF] at hv
    rw [Kernel.Environment.find?_eq_constants hsourceWF] at hnone
    have hA : Nonempty (InductInfoAlignment outEnv.constants sourceDecl owner.val v) := by
      rcases horig _ v hv with hold | ⟨fi, hfn, ⟨A⟩⟩
      · rw [hnone] at hold; cases hold
      · have htypesNodup : (sourceDecl.types.map (·.name)).Nodup := by
          have h := (List.nodup_append.mp Hdata.sourceWF.2.1).1
          simpa [VInductDecl.typeConstants, List.map_map, Function.comp_def] using h
        have hfi : fi = owner.val := by
          have hn : (sourceDecl.types[fi]'A.familyIdx_lt).name =
              (sourceDecl.types[owner.val]'hsrc).name := A.name.symm.trans hfn.symm
          have hfi' : fi < (sourceDecl.types.map (·.name)).length := by
            simpa using A.familyIdx_lt
          have how' : owner.val < (sourceDecl.types.map (·.name)).length := by
            simpa using hsrc
          exact (List.getElem_inj (h₀ := hfi') (h₁ := how') htypesNodup).mp (by simpa using hn)
        subst hfi
        exact ⟨A⟩
    obtain ⟨A⟩ := hA
    obtain ⟨C⟩ := A.constructor j hj
    have hCname : v.ctors[j]'C.familyInfo_ctorIdx_lt = sc.name := C.name
    refine ⟨⟨C.info, by rw [← hCname]; exact C.lookup, C.numParams⟩, ?_, .inl ⟨sc, hscMem, rfl, by simp [hnp]⟩⟩
    -- the constructor shape
    have Hcore := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at Hcore
    refine ⟨sc.toVConstant, VEnv.addConstVals_get Hcore.ctorsAdded hscMem, ?_, ?_⟩
    · -- the lowered constructor at the same position
      have Hfam := Lean4Lean.List.forall₂_getElem Hdata.model.families owner.val
        (by simp [InductiveSignature.declaration])
        (by rw [← Lean4Lean.List.Forall₂.length_eq Hdata.model.families]
            simp [InductiveSignature.declaration])
      have hdf : E.lowered.signature.declaration.types[owner.val]'(by simp [InductiveSignature.declaration]) =
          E.lowered.signature.declarationFamily owner := by
        simp [InductiveSignature.declaration, InductiveSignature.declarationFamily]
      have hlnames := Hfam.2.2.2.2
      rw [hdf, hnames] at hlnames
      have hlen := congrArg List.length hlnames
      simp only [List.length_map] at hlen
      have hiL : owner.val < E.lowered.loweredDecl.types.length := by
        rw [← Lean4Lean.List.Forall₂.length_eq Hdata.model.families]
        simp [InductiveSignature.declaration]
      have hjL : j < (E.lowered.loweredDecl.types[owner.val]'hiL).ctors.length := by
        rw [← hlen]; exact hj
      have hlcName : ((E.lowered.loweredDecl.types[owner.val]'hiL).ctors[j]'hjL).name =
          sc.name := by
        have := congrArg (fun l => l[j]?) hlnames
        simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
          List.getElem?_eq_getElem hjL, Option.map_some, Option.some.injEq] at this
        exact this.symm
      have hlcMem : (E.lowered.loweredDecl.types[owner.val]'hiL).ctors[j]'hjL ∈
          E.lowered.loweredDecl.constructorConstants :=
        List.mem_flatMap.mpr ⟨_, List.getElem_mem hiL, List.getElem_mem hjL⟩
      have hlcGet := VEnv.addConstVals_get E.lowered.constructors.core.ctorsAdded hlcMem
      obtain ⟨ci, hci, hshape⟩ := E.loweredConstructorShape index
      rw [← hjx, ← hlcName, hlcGet] at hci
      cases hci
      have hAr := Harity owner.val hsrc hiL j hj hjL
      change sc.type.piArity = _
      rw [VExpr.piArity_eq_forallArity, hAr, ← VExpr.piArity_eq_forallArity, hshape.1,
        Hdata.nparams]
    · obtain ⟨-, -, -, -, -, hraw⟩ := Hdata.sourceParameters
      exact (hraw _ (List.getElem_mem hsrc) sc (List.getElem_mem hj)).ctorHeaded
  · -- an auxiliary family
    have ha := List.getElem_mem hidx
    have hh := Hdata.restoredFamilyHead_auxiliary owner ha hfamName
    rw [hhead] at hh
    cases hh
    rw [hnames] at hx
    obtain ⟨c, hc, hcx⟩ := List.mem_map.mp hx
    have hrestored : (compilationRestoration sourceDecl auxiliaries).restoredHeadName E.lowered.signature.constructors[index].name = c.name := by
      rw [← hcx]; exact Hdata.restoredHeadName_auxiliary ha hc
    simp only [hrestored, List.length_map]
    obtain ⟨g', hg', HG⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux _ ha
    refine ⟨E.containerConstructorKernel wf Hsources D Hkernel ha hc, ?_, .inr ⟨_, HG.installed, c,
      List.mem_flatMap.mpr ⟨_, List.getElem_mem _, hc⟩, rfl, HG.argumentsLength⟩⟩
    have hown' : E.lowered.signature.constructors[index].owner.val = owner.val := by rw [hown]
    have hidx' : E.lowered.signature.constructors[index].owner.val - sourceDecl.types.length <
        auxiliaries.length := by rw [hown']; exact hidx
    have := E.containerConstructorShape Haux Hexpansion Hdata index (by rw [hown']; exact hge)
      hidx' (c := c) (by simp only [hown']; exact hc) (by simp only [hown']; exact hcx.symm)
    simp only [hown'] at this
    exact this

/-- The restored constructors of one family are distinct: the identity on a
source family's constructors, and on an auxiliary family's the constructors of its container's
family (`CaseCompilationData.directFamily_restored_constructor_names`), whose names are distinct
in the installed container. -/
theorem NestedRun.restoredRuleConstructors_nodup
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hcert : ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries)
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (owner : Fin E.lowered.signature.families.size) :
    ((E.lowered.signature.ownedConstructors owner).map fun index =>
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.lowered.signature.constructors[index].name).Nodup := by
  have := Hcert
  have hmap : (E.lowered.signature.ownedConstructors owner).map (fun index =>
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.lowered.signature.constructors[index].name) =
      ((E.lowered.signature.declarationFamily owner).ctors.map (·.name)).map
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName := by
    rw [← ownedConstructors_names, List.map_map]; rfl
  rw [hmap]
  refine list_nodup_map_on ?_ (Hdata.declarationFamily_names_nodup owner)
  rcases Hdata.familyCases owner with ⟨hsrc, -, hnames⟩ | ⟨-, hidx, -, hnames⟩
  · intro x hx y hy hxy
    rw [hnames] at hx hy
    have hmem : ∀ z ∈ (sourceDecl.types[owner.val]'hsrc).ctors.map (·.name),
        z ∈ familyNames sourceDecl.types := fun z hz =>
      mem_familyNames.mpr ⟨_, List.getElem_mem hsrc, .inr (by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz; exact ⟨c, hc, rfl⟩)⟩
    rwa [Hdata.restoredHeadName_source (hmem x hx),
      Hdata.restoredHeadName_source (hmem y hy)] at hxy
  · intro x hx y hy hxy
    rw [hnames] at hx hy
    have ha := List.getElem_mem hidx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hy
    rw [Hdata.restoredHeadName_auxiliary ha hc, Hdata.restoredHeadName_auxiliary ha hc'] at hxy
    simp only [ContainerSpecialization.constructorName, hxy]


end VerifyInductive
end Lean4Lean
