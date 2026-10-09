import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Verify.Inductive.Nested.Restoration.TrRestoredRecursorVal
import Lean4Lean.Verify.Inductive.Rules.Alignment
import Lean4Lean.Verify.Inductive.Nested.Install.RunView
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliarySources

/-! Container specialisations of a nested declaration.

`CompilationData` fixes nested restoration by an ordered list of
`ContainerSpecialization`s, one per generated auxiliary family, in the order
of the lowered family suffix (the order also used by `mkAuxRecNameMap`).
This module proves the generic properties of `compilationRestoration`
(scoping, recursor and head renaming, the direct families) and connects the
recursor renaming with the executable `mkAuxRecNameMap`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace InductiveSignature

theorem compilationRestoration_recursors_fst (source : VInductDecl)
    (auxiliaries : List ContainerSpecialization) :
    (compilationRestoration source auxiliaries).recursors.map Prod.fst =
      auxiliaries.map (fun a => a.auxiliary.str "rec") := by
  simp only [compilationRestoration, List.map_map]
  conv => rhs; rw [← List.zipIdx_map_fst 0 auxiliaries, List.map_map]
  rfl

/-- The renaming target of every auxiliary recursor. -/
def compilationRecursorTarget (source : VInductDecl) (i : Nat) : Name :=
  (((source.types.head?).map (fun t : VInductiveType => t.name)).getD
    (default : Name)).str "rec" |>.appendIndexAfter (i + 1)

theorem compilationRestoration_recursors (source : VInductDecl)
    (auxiliaries : List ContainerSpecialization) :
    (compilationRestoration source auxiliaries).recursors =
      auxiliaries.zipIdx.map fun (a, i) =>
        (a.auxiliary.str "rec", compilationRecursorTarget source i) := rfl

private theorem find?_zipIdx_map_of_nodup
    (f : α → Name) (g : Nat → Name) (l : List α) (k : Nat)
    (hnodup : (l.map f).Nodup) (i : Nat) (hi : i < l.length) :
    ((l.zipIdx k).map fun (a, j) => (f a, g j)).find?
        (fun pair => pair.1 == f l[i]) = some (f l[i], g (k + i)) := by
  induction l generalizing k i with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < l.length := by simpa using hi
      have hne : f a ≠ f l[i] := by
        intro h
        exact hnodup.1 ⟨l[i], List.getElem_mem _, h.symm⟩
      simp only [List.zipIdx_cons, List.map_cons, List.find?_cons,
        List.getElem_cons_succ]
      have hbeq : (f a == f l[i]) = false := by simpa using hne
      rw [hbeq]
      simp only
      rw [ih (k + 1) hnodup.2 i hi', show k + 1 + i = k + (i + 1) by omega]

theorem compilationRestoration_recursorName_auxiliary
    (source : VInductDecl) (auxiliaries : List ContainerSpecialization)
    (hnodup : (auxiliaries.map (·.auxiliary)).Nodup)
    (i : Nat) (hi : i < auxiliaries.length) :
    (compilationRestoration source auxiliaries).recursorName
        (auxiliaries[i].auxiliary.str "rec") =
      compilationRecursorTarget source i := by
  have hnodup' : (auxiliaries.map (fun a => a.auxiliary.str "rec")).Nodup := by
    have h : List.Pairwise (fun x y : Name => x.str "rec" ≠ y.str "rec")
        (auxiliaries.map (·.auxiliary)) :=
      List.Pairwise.imp (fun hne h => hne (Name.str.inj h).1) hnodup
    simpa [List.Nodup, List.pairwise_map] using h
  unfold Restoration.recursorName
  rw [compilationRestoration_recursors,
    find?_zipIdx_map_of_nodup (fun a => a.auxiliary.str "rec")
      (compilationRecursorTarget source) auxiliaries 0 hnodup' i hi]
  simp

theorem compilationRestoration_recursorName_of_not_mem
    (source : VInductDecl) (auxiliaries : List ContainerSpecialization)
    (hname : name ∉ auxiliaries.map (fun a => a.auxiliary.str "rec")) :
    (compilationRestoration source auxiliaries).recursorName name = name := by
  unfold Restoration.recursorName
  rw [← compilationRestoration_recursors_fst source auxiliaries] at hname
  split
  · rename_i pair hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have heq := List.find?_some hfind
    simp only [beq_iff_eq] at heq
    exact absurd (List.mem_map.mpr ⟨pair, hmem, heq⟩) hname
  · rfl


theorem ContainerSpecialization.heads_map_auxiliary (a : ContainerSpecialization)
    (uvars nparams : Nat) :
    (a.heads uvars nparams).map (·.auxiliary) = a.headNames := by
  simp [ContainerSpecialization.heads, ContainerSpecialization.headNames,
    Function.comp_def]

theorem compilationRestoration_heads_auxiliary (source : VInductDecl)
    (auxiliaries : List ContainerSpecialization) :
    (compilationRestoration source auxiliaries).heads.map (·.auxiliary) =
      auxiliaries.flatMap (·.headNames) := by
  simp only [compilationRestoration, List.map_flatMap,
    ContainerSpecialization.heads_map_auxiliary]

theorem ContainerSpecialization.mem_heads {a : ContainerSpecialization}
    {head : HeadSpecialization} {uvars nparams : Nat}
    (h : head ∈ a.heads uvars nparams) :
    head.uvars = uvars ∧ head.nparams = nparams ∧ head.levels = a.levels ∧
      head.arguments = a.arguments := by
  simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨_, _, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `compilationRestoration` is scoped once its head and recursor names are
jointly distinct and every specialisation argument is in scope. -/
theorem compilationRestoration_scoped (source : VInductDecl)
    (auxiliaries : List ContainerSpecialization)
    (hnames : (auxiliaries.flatMap (·.headNames) ++
      auxiliaries.map (fun a => a.auxiliary.str "rec")).Nodup)
    (hlevels : ∀ a ∈ auxiliaries, ∀ level ∈ a.levels, level.WF source.uvars)
    (harguments : ∀ a ∈ auxiliaries, ∀ arg ∈ a.arguments,
      arg.ClosedN source.nparams) :
    (compilationRestoration source auxiliaries).Scoped := by
  have hsplit := List.nodup_append.mp hnames
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [compilationRestoration_heads_auxiliary]
    exact hsplit.1
  · rw [compilationRestoration_recursors_fst]
    exact hsplit.2.1
  · intro head hhead
    change head ∈ auxiliaries.flatMap _ at hhead
    rcases List.mem_flatMap.mp hhead with ⟨a, ha, hmem⟩
    rcases ContainerSpecialization.mem_heads hmem with ⟨huvars, hnparams, hl, hargs⟩
    exact ⟨by rw [hl, huvars]; exact hlevels a ha,
      by rw [hargs, hnparams]; exact harguments a ha⟩
  · intro head hhead hrec
    rw [compilationRestoration_recursors_fst] at hrec
    have hmem : head.auxiliary ∈
        (compilationRestoration source auxiliaries).heads.map (·.auxiliary) :=
      List.mem_map.mpr ⟨head, hhead, rfl⟩
    rw [compilationRestoration_heads_auxiliary] at hmem
    exact hsplit.2.2 _ hmem _ hrec rfl

theorem compilationRestoration_restoredHeadName_of_mem
    {source : VInductDecl} {auxiliaries : List ContainerSpecialization}
    (hnodup : (auxiliaries.flatMap (·.headNames)).Nodup)
    {head : HeadSpecialization}
    (hhead : head ∈ (compilationRestoration source auxiliaries).heads) :
    (compilationRestoration source auxiliaries).restoredHeadName head.auxiliary =
      head.target := by
  rw [← compilationRestoration_heads_auxiliary source auxiliaries] at hnodup
  unfold Restoration.restoredHeadName
  rw [Lean4Lean.EnvTables.find?_name_of_mem (f := (·.auxiliary)) hnodup hhead]

/-- An auxiliary constructor name restores to its container constructor. -/
theorem compilationRestoration_restoredHeadName_constructor
    {source : VInductDecl} {auxiliaries : List ContainerSpecialization}
    (hnodup : (auxiliaries.flatMap (·.headNames)).Nodup)
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries)
    {ctor : VConstVal} (hctor : ctor ∈ a.source.ctors) :
    (compilationRestoration source auxiliaries).restoredHeadName
        (a.constructorName ctor) = ctor.name := by
  have hhead : HeadSpecialization.mk (a.constructorName ctor) source.uvars
      source.nparams ctor.name a.levels a.arguments ∈
      (compilationRestoration source auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
  exact compilationRestoration_restoredHeadName_of_mem hnodup hhead

/-- A syntactic forall telescope covering at least `n` binders. -/
def HasForallPrefix (type : VExpr) (n : Nat) : Prop :=
  ∃ domains body, type = VExpr.wrapForalls domains body ∧ n ≤ domains.length

theorem HasForallPrefix.instL {type : VExpr} {n : Nat}
    (H : HasForallPrefix type n) (levels : List VLevel) :
    HasForallPrefix (type.instL levels) n := by
  rcases H with ⟨domains, body, rfl, hn⟩
  refine ⟨domains.map (·.instL levels), body.instL levels, ?_, by simpa using hn⟩
  clear hn
  induction domains with
  | nil => rfl
  | cons d ds ih => simp [VExpr.wrapForalls, VExpr.instL] at ih ⊢; exact ih

theorem specializeType_isSome {type : VExpr} {args : List VExpr}
    (H : HasForallPrefix type args.length) :
    ∃ specialized, specializeType type args = some specialized := by
  rcases H with ⟨domains, body, rfl, hn⟩
  obtain ⟨pre, suff, rfl, hpre⟩ : ∃ pre suff, domains = pre ++ suff ∧
      pre.length = args.length :=
    ⟨domains.take args.length, domains.drop args.length,
      (List.take_append_drop _ _).symm, by simp [Nat.min_eq_left hn]⟩
  unfold specializeType
  rw [← hpre, VExpr.takeForalls_wrapForalls_append]
  exact ⟨_, rfl⟩

/-- Metadata of a direct auxiliary family that does not depend on the
specialised types. -/
structure DirectFamilyShape (U : Nat) (a : ContainerSpecialization)
    (direct : VInductiveType) : Prop where
  name : direct.name = a.auxiliary
  uvars : direct.uvars = U
  numIndices : direct.numIndices = a.source.numIndices
  resultLevel : direct.resultLevel = a.source.resultLevel.inst a.levels
  ctorNames : direct.ctors.map (·.name) = a.source.ctors.map a.constructorName
  ctorUvars : ∀ ctor ∈ direct.ctors, ctor.uvars = U

/-- `specializedFamily` succeeds as soon as the selected family and all of its
constructors carry a syntactic parameter telescope. -/
theorem ContainerSpecialization.directFamily_isSome
    (a : ContainerSpecialization) (uvars : Nat) (params : List VExpr)
    (hfamily : HasForallPrefix a.source.type a.arguments.length)
    (hctors : ∀ ctor ∈ a.source.ctors,
      HasForallPrefix ctor.type a.arguments.length) :
    ∃ direct, a.specializedFamily uvars params = some direct ∧
      DirectFamilyShape uvars a direct := by
  rcases specializeType_isSome (hfamily.instL a.levels) with ⟨type, htype⟩
  let ctorFn := fun ctor : VConstVal => (do
    let type ← specializeType (ctor.type.instL a.levels) a.arguments
    return ({
      name := a.constructorName ctor
      uvars := uvars
      type := VExpr.wrapForalls params type } : VConstVal) : Option VConstVal)
  have hctorFn : ∀ ctor ∈ a.source.ctors, ∃ c, ctorFn ctor = some c ∧
      c.name = a.constructorName ctor ∧ c.uvars = uvars := by
    intro ctor hctor
    rcases specializeType_isSome ((hctors ctor hctor).instL a.levels) with
      ⟨t, ht⟩
    exact ⟨{
      name := a.constructorName ctor
      uvars := uvars
      type := VExpr.wrapForalls params t }, by simp [ctorFn, ht], rfl, rfl⟩
  have hmapM : ∀ (ctors : List VConstVal), (∀ ctor ∈ ctors, ∃ c, ctorFn ctor = some c ∧
      c.name = a.constructorName ctor ∧ c.uvars = uvars) →
      ∃ cs, ctors.mapM ctorFn = some cs ∧
        cs.map (·.name) = ctors.map a.constructorName ∧
        ∀ c ∈ cs, c.uvars = uvars := by
    intro ctors H
    induction ctors with
    | nil => exact ⟨[], rfl, rfl, by simp⟩
    | cons ctor ctors ih =>
      rcases H ctor List.mem_cons_self with ⟨c, hc, hname, huvars⟩
      rcases ih (fun x hx => H x (List.mem_cons_of_mem _ hx)) with
        ⟨cs, hcs, hnames, hcsUvars⟩
      refine ⟨c :: cs, ?_, ?_, ?_⟩
      · simp [List.mapM_cons, hc, hcs]
      · simp [hname, hnames]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact huvars
        · exact hcsUvars x hx
  rcases hmapM a.source.ctors hctorFn with ⟨cs, hcs, hnames, hcsUvars⟩
  refine ⟨{
    name := a.auxiliary
    uvars := uvars
    type := VExpr.wrapForalls params type
    numIndices := a.source.numIndices
    resultLevel := a.source.resultLevel.inst a.levels
    ctors := cs }, ?_, ⟨rfl, rfl, rfl, rfl, hnames, hcsUvars⟩⟩
  simp only [ContainerSpecialization.specializedFamily, htype]
  change (do
    let ctors ← a.source.ctors.mapM ctorFn
    pure _) = _
  rw [hcs]
  rfl

theorem directFamilies_isSome (auxiliaries : List ContainerSpecialization)
    (uvars : Nat) (params : List VExpr)
    (H : ∀ a ∈ auxiliaries,
      HasForallPrefix a.source.type a.arguments.length ∧
      ∀ ctor ∈ a.source.ctors, HasForallPrefix ctor.type a.arguments.length) :
    ∃ direct, auxiliaries.mapM (fun a => a.specializedFamily uvars params) = some direct ∧
      List.Forall₂ (DirectFamilyShape uvars) auxiliaries direct := by
  induction auxiliaries with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons a rest ih =>
    rcases H a List.mem_cons_self with ⟨hfamily, hctors⟩
    rcases a.directFamily_isSome uvars params hfamily hctors with ⟨d, hd, hshape⟩
    rcases ih (fun b hb => H b (List.mem_cons_of_mem _ hb)) with
      ⟨direct, hdirect, hshapes⟩
    exact ⟨d :: direct, by simp [List.mapM_cons, hd, hdirect], .cons hshape hshapes⟩

end InductiveSignature

/-- `ContainersInstalled` for every selected container, from installed-container
certificates in the same ambient environment. -/
theorem ContainersInstalled.of_installed {env : VEnv} :
    ∀ {auxiliaries : List InductiveSignature.ContainerSpecialization},
      (∀ a ∈ auxiliaries, VEnv.InstalledBelow env a.container) →
      ContainersInstalled env auxiliaries
  | [], _ => .nil
  | a :: rest, H => by
    cases H a List.mem_cons_self with
    | intro _ _ hcompile hblock hinstall hle =>
      exact .cons hcompile hblock hinstall hle
        (ContainersInstalled.of_installed fun b hb =>
          H b (List.mem_cons_of_mem _ hb))

/-- Every installed container retains its source parameter formation. -/
theorem VEnv.InstalledBelow.sourceParameterWF
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl) :
    ∃ base, VInductDecl.SourceParameterWF base decl := by
  cases H with
  | intro _ hformation _ _ _ _ =>
    cases hformation with
    | ordinary hwf => exact ⟨_, hwf.sourceParameterWF⟩
    | nested hnested _ =>
      cases hnested with
      | intro _ _ hparams _ _ _ _ => exact ⟨_, hparams⟩

/-- Constructors of an installed container carry a syntactic parameter
telescope. -/
theorem VEnv.InstalledBelow.ctorForallPrefix
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledBelow env decl)
    {type : VInductiveType} (htype : type ∈ decl.types)
    {ctor : VConstVal} (hctor : ctor ∈ type.ctors) :
    InductiveSignature.HasForallPrefix ctor.type decl.nparams := by
  rcases H.sourceParameterWF with ⟨_, hparams⟩
  rcases hparams.rawCtorShape type htype ctor hctor with
    ⟨domains, result, hctorType, hn, _, _⟩
  exact ⟨domains, result, hctorType, hn⟩

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive

private theorem auxRecFold_find_of_not_mem
    (names : List Name) (acc : Array Name × NameMap Name × Nat)
    (mainName query : Name)
    (hnot : query ∉ names.map Lean.mkRecName) :
    (names.foldl (fun b name =>
      (b.1.push (Lean.mkRecName name),
        b.2.1.insert (Lean.mkRecName name)
          ((Lean.mkRecName mainName).appendIndexAfter b.2.2),
        b.2.2 + 1)) acc).2.1.find? query = acc.2.1.find? query := by
  induction names generalizing acc with
  | nil => rfl
  | cons name names ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    rw [List.foldl_cons, ih _ hnot.2]
    change (Std.TreeMap.insert
      (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)
      (Lean.mkRecName name)
      ((Lean.mkRecName mainName).appendIndexAfter acc.2.2))[query]? =
      (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)[query]?
    rw [Std.TreeMap.getElem?_insert]
    split
    · rename_i heq
      have : Lean.mkRecName name = query := by simpa using heq
      exact False.elim (hnot.1 this.symm)
    · rfl

private theorem auxRecFold_find
    (names : List Name) (acc : Array Name × NameMap Name × Nat)
    (mainName : Name) (hnodup : (names.map Lean.mkRecName).Nodup)
    (i : Nat) (hi : i < names.length) :
    (names.foldl (fun b name =>
      (b.1.push (Lean.mkRecName name),
        b.2.1.insert (Lean.mkRecName name)
          ((Lean.mkRecName mainName).appendIndexAfter b.2.2),
        b.2.2 + 1)) acc).2.1.find? (Lean.mkRecName names[i]) =
      some ((Lean.mkRecName mainName).appendIndexAfter (acc.2.2 + i)) := by
  induction names generalizing acc i with
  | nil => simp at hi
  | cons name names ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rw [List.foldl_cons]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [auxRecFold_find_of_not_mem _ _ _ _ hnodup.1]
      change (Std.TreeMap.insert
        (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)
        (Lean.mkRecName name)
        ((Lean.mkRecName mainName).appendIndexAfter acc.2.2))[Lean.mkRecName name]? = _
      rw [Std.TreeMap.getElem?_insert_self]
      rfl
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [ih _ hnodup.2 i (by simpa using hi)]
      congr 2
      simp only
      omega

/-- The executable auxiliary-recursor map sends the recursor of the `i`-th
extra family to `main.rec_(i+1)`. -/
theorem mkAuxRecNameMap_find_auxiliary
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hnodup : ((info.all.drop (main :: rest).length).map Lean.mkRecName).Nodup)
    (i : Nat) (hi : i < (info.all.drop (main :: rest).length).length) :
    (Lean4Lean.mkAuxRecNameMap env (main :: rest)).2.find?
        (Lean.mkRecName (info.all.drop (main :: rest).length)[i]) =
      some ((Lean.mkRecName main.name).appendIndexAfter (i + 1)) := by
  have hlength' : rest.length + 1 < info.all.length := by
    simp at hi; omega
  have h := auxRecFold_find (info.all.drop (rest.length + 1)) (#[], {}, 1)
    main.name (by simpa using hnodup) i (by simpa using hi)
  simp only [Nat.add_comm 1 i] at h
  simpa [Lean4Lean.mkAuxRecNameMap, hfind, hlength'] using h


open _root_.Lean4Lean.InductiveSignature in
/-- The abstract auxiliary-recursor renaming of `compilationRestoration`
agrees with the executable `mkAuxRecNameMap` on every name, provided the
specialisations are listed in the order of the lowered family suffix
recorded by the main family's `all` metadata. -/
theorem compilationRestoration_recursorName_eq_mkAuxRecNameMap
    (decl : VInductDecl) (auxiliaries : List ContainerSpecialization)
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hfirst : decl.types.head?.map (·.name) = some main.name)
    (hnames : auxiliaries.map (·.auxiliary) = info.all.drop (main :: rest).length)
    (hnodup : (auxiliaries.map (·.auxiliary)).Nodup) (name : Name) :
    (compilationRestoration decl auxiliaries).recursorName name =
      ((Lean4Lean.mkAuxRecNameMap env (main :: rest)).2.find? name).getD name := by
  have hrecNames : auxiliaries.map (fun a => a.auxiliary.str "rec") =
      (info.all.drop (main :: rest).length).map Lean.mkRecName := by
    rw [← hnames, List.map_map]
    rfl
  by_cases hmem : name ∈ auxiliaries.map (fun a => a.auxiliary.str "rec")
  · rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hname⟩
    have hi' : i < auxiliaries.length := by simpa using hi
    have hname' : name = auxiliaries[i].auxiliary.str "rec" := by
      rw [← hname, List.getElem_map]
    have hnodupRec : ((info.all.drop (main :: rest).length).map
        Lean.mkRecName).Nodup := by
      rw [← hrecNames]
      have h : List.Pairwise (fun x y : Name => x.str "rec" ≠ y.str "rec")
          (auxiliaries.map (·.auxiliary)) :=
        List.Pairwise.imp (fun hne h => hne (Name.str.inj h).1) hnodup
      simpa [List.Nodup, List.pairwise_map] using h
    have hiDrop : i < (info.all.drop (main :: rest).length).length := by
      rw [← hnames]; simpa using hi'
    have hauxName : auxiliaries[i].auxiliary =
        (info.all.drop (main :: rest).length)[i] := by
      have := congrArg (fun l => l[i]?) hnames
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi',
        List.getElem?_eq_getElem hiDrop, Option.map_some, Option.some.injEq] at this
      exact this
    rw [hname', compilationRestoration_recursorName_auxiliary decl auxiliaries hnodup i hi']
    have hfindAux := mkAuxRecNameMap_find_auxiliary main rest env info hfind
      hnodupRec i hiDrop
    rw [← hauxName] at hfindAux
    change _ = ((Lean4Lean.mkAuxRecNameMap env (main :: rest)).2.find?
      (Lean.mkRecName auxiliaries[i].auxiliary)).getD _
    rw [hfindAux]
    simp [compilationRecursorTarget, hfirst, Lean.mkRecName]
  · rw [compilationRestoration_recursorName_of_not_mem decl auxiliaries hmem]
    rw [hrecNames] at hmem
    rw [mkAuxRecNameMap_recMap_find_none main rest env info hfind hmem]
    rfl


open _root_.Lean4Lean.InductiveSignature

/-- One container specialisation describes one generated (pre-lowering)
auxiliary family. `sourceEnv` is the environment the declaration is checked
in; `envTypes` adds the source family headers. -/
structure SpecializationGenerates (sourceEnv envTypes : VEnv)
    (paramCtx : List VExpr)
    (decl : VInductDecl) (a : ContainerSpecialization)
    (generated : VInductiveType) : Prop where
  installed : VEnv.InstalledBelow sourceEnv a.container
  auxiliary : a.auxiliary = generated.name
  generatedUvars : generated.uvars = decl.uvars
  argumentsLength : a.arguments.length = a.container.nparams
  argumentsClosed : ∀ arg ∈ a.arguments, arg.ClosedN decl.nparams
  levelsLength : a.levels.length = a.container.uvars
  levelsWF : ∀ level ∈ a.levels, level.WF decl.uvars
  safety : decl.isUnsafe = true ∨ a.container.isUnsafe = false
  familyForallPrefix : HasForallPrefix a.source.type a.arguments.length
  application : ∃ sourceParams : List VExpr,
    sourceParams.length = decl.nparams ∧
    VEnv.IsDefEqCtx envTypes decl.uvars [] sourceParams.reverse paramCtx ∧
    OnCtx sourceParams.reverse (envTypes.IsType decl.uvars) ∧
    envTypes.HasType decl.uvars sourceParams.reverse
      (VExpr.mkApps (.const a.source.name a.levels) a.arguments)
      (VExpr.instantiateForallPrefix (a.source.type.instL a.levels)
        a.arguments) ∧
    envTypes.IsDefEqU decl.uvars [] generated.type
      (VExpr.wrapForalls sourceParams
        (VExpr.instantiateForallPrefix (a.source.type.instL a.levels)
          a.arguments)) ∧
    List.Forall₂
      (VInductDecl.SpecializedAuxConstructor envTypes decl.uvars sourceParams
        a.arguments a.levels a.source generated)
      a.source.ctors generated.ctors
  /-- Each generated constructor type is syntactically the parameter closure
  of the container constructor type instantiated at the specialization
  arguments, up to level equivalence. -/
  constructorShapes : ∃ sourceParams : List VExpr,
    sourceParams.length = decl.nparams ∧
    List.Forall₂
      (fun ctor target => ∃ instCtorType : VExpr,
        VExpr.LEquiv decl.uvars instCtorType (ctor.type.instL a.levels) ∧
        target.type = VExpr.wrapForalls sourceParams
          (VExpr.instantiateForallPrefix instCtorType a.arguments))
      a.source.ctors generated.ctors

private theorem directAuxConstructors_names
    {sourceCtors targetCtors : List VConstVal}
    (H : List.Forall₂ (VInductDecl.SpecializedAuxConstructor env U sourceParams
      baseArgs levels containerFamily auxiliaryFamily) sourceCtors targetCtors) :
    targetCtors.map (·.name) = sourceCtors.map
      (fun ctor => ctor.name.replacePrefix containerFamily.name
        auxiliaryFamily.name) := by
  induction H with
  | nil => rfl
  | cons hhead _ ih => simp only [List.map_cons, ih, hhead.name]

theorem nestedConstructorExpansions_names
    {sourceCtors targetCtors : List VConstVal}
    (H : List.Forall₂ (VInductDecl.NestedConstructorExpansion leaf nparams)
      sourceCtors targetCtors) :
    targetCtors.map (·.name) = sourceCtors.map (·.name) := by
  induction H with
  | nil => rfl
  | cons hhead _ ih => simp only [List.map_cons, ih, hhead.name]

theorem SpecializationGenerates.generatedCtorNames
    (H : SpecializationGenerates sourceEnv envTypes paramCtx decl a generated) :
    generated.ctors.map (·.name) = a.source.ctors.map a.constructorName := by
  rcases H.application with ⟨_, _, _, _, _, _, hctors⟩
  rw [directAuxConstructors_names hctors, ← H.auxiliary]
  rfl

/-- Typing of the actual container application, in any parameter context
definitionally equal to the common one. -/
theorem SpecializationGenerates.wellFormed
    (H : SpecializationGenerates sourceEnv envTypes paramCtx decl a generated)
    (henv : envTypes.WF) (params : List VExpr)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx) :
    a.WellFormed envTypes decl params := by
  rcases H.application with
    ⟨sourceParams, _, hsourceCtx, _, htyping, _, _⟩
  exact ⟨H.argumentsLength, H.argumentsClosed, H.levelsLength, H.levelsWF,
    H.safety, _, (htyping.defeqDFC henv.ordered hsourceCtx).defeqDFC henv.ordered
      (hparams.symm henv.ordered)⟩

/-- The selected container constructors carry a syntactic parameter
telescope covering the specialisation arguments. -/
theorem SpecializationGenerates.ctorForallPrefix
    (H : SpecializationGenerates sourceEnv envTypes paramCtx decl a generated)
    {ctor : VConstVal} (hctor : ctor ∈ a.source.ctors) :
    HasForallPrefix ctor.type a.arguments.length := by
  rw [H.argumentsLength]
  exact H.installed.ctorForallPrefix (List.getElem_mem a.family.isLt) hctor

section Lists

variable {sourceEnv envTypes : VEnv} {paramCtx : List VExpr} {decl : VInductDecl}
  {auxiliaries : List ContainerSpecialization}
  {generated targets : List VInductiveType}
  {leaf : Nat → VExpr → VExpr → Prop}

theorem auxiliarySpecializations_certified
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated) :
    ContainersInstalled sourceEnv auxiliaries := by
  apply ContainersInstalled.of_installed
  intro a ha
  rcases Lean4Lean.List.Forall₂.forall_exists_l H a ha with ⟨_, _, h⟩
  exact h.installed

theorem auxiliarySpecializations_wellFormed
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (henv : envTypes.WF) (params : List VExpr)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx) :
    ∀ a ∈ auxiliaries, a.WellFormed envTypes decl params := by
  intro a ha
  rcases Lean4Lean.List.Forall₂.forall_exists_l H a ha with ⟨_, _, h⟩
  exact h.wellFormed henv params hparams

theorem auxiliarySpecializations_names
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion env decl leaf)
      generated targets) :
    auxiliaries.map (·.auxiliary) = targets.map (·.name) := by
  induction H generalizing targets with
  | nil => cases Hexpansion; rfl
  | cons h _ ih =>
    cases Hexpansion with
    | cons hexp htail =>
      simp only [List.map_cons, ih htail, h.auxiliary, hexp.name]

/-- The restoration heads claim exactly the names of the lowered auxiliary
families and their constructors. -/
theorem auxiliarySpecializations_headNames
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion env decl leaf)
      generated targets) :
    auxiliaries.flatMap (·.headNames) = familyNames targets := by
  induction H generalizing targets with
  | nil => cases Hexpansion; rfl
  | @cons a family _ _ h _ ih =>
    cases Hexpansion with
    | @cons _ target _ _ hexp htail =>
      have hctors : target.ctors.map (·.name) = family.ctors.map (·.name) :=
        nestedConstructorExpansions_names hexp.constructors
      simp only [List.flatMap_cons, familyNames] at ih ⊢
      rw [ih htail]
      simp only [ContainerSpecialization.headNames, hctors,
        h.generatedCtorNames, h.auxiliary, hexp.name, List.cons_append]

/-- Every direct family is computed. -/
theorem auxiliarySpecializations_directFamilies
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (uvars : Nat) (params : List VExpr) :
    ∃ direct, auxiliaries.mapM (fun a => a.specializedFamily uvars params) =
        some direct ∧
      List.Forall₂ (DirectFamilyShape uvars) auxiliaries direct := by
  apply directFamilies_isSome
  intro a ha
  rcases Lean4Lean.List.Forall₂.forall_exists_l H a ha with ⟨_, _, h⟩
  exact ⟨h.familyForallPrefix, fun _ hctor => h.ctorForallPrefix hctor⟩

/-- Scoping of the restoration table from the name separation of the lowered
auxiliary families and their generated recursors. -/
theorem auxiliarySpecializations_scoped
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion env decl leaf)
      generated targets)
    (hnodup : (familyNames targets ++
      targets.map (fun t => t.name.str "rec")).Nodup) :
    (compilationRestoration decl auxiliaries).Scoped := by
  apply compilationRestoration_scoped
  · rw [auxiliarySpecializations_headNames H Hexpansion]
    have hrec : auxiliaries.map (fun a => a.auxiliary.str "rec") =
        targets.map (fun t => t.name.str "rec") := by
      have h := congrArg (List.map (fun n : Name => n.str "rec"))
        (auxiliarySpecializations_names H Hexpansion)
      simpa only [List.map_map, Function.comp_def] using h
    rw [hrec]
    exact hnodup
  · intro a ha
    rcases Lean4Lean.List.Forall₂.forall_exists_l H a ha with ⟨_, _, h⟩
    exact h.levelsWF
  · intro a ha
    rcases Lean4Lean.List.Forall₂.forall_exists_l H a ha with ⟨_, _, h⟩
    exact h.argumentsClosed

end Lists

/-! ### The specialisations of a validated nested run -/

private theorem inductInfo_safety_of_visible {info : InductiveVal} {isUnsafe : Bool}
    (h : (if isUnsafe then DefinitionSafety.unsafe else .safe) ≤
      (ConstantInfo.inductInfo info).safety) :
    isUnsafe = true ∨ info.isUnsafe = false := by
  cases isUnsafe
  · right
    cases hi : info.isUnsafe
    · rfl
    · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hi] at h
      exact absurd h (by decide)
  · left; rfl

theorem sameTelescopeArity_hasForallPrefix
    (H : SameTelescopeArity arity type type') :
    HasForallPrefix type arity := by
  induction H with
  | zero left _ => exact ⟨[], left, rfl, Nat.le_refl _⟩
  | succ leftDomain _ _ _ _ ih =>
    rcases ih with ⟨domains, body, rfl, hn⟩
    exact ⟨leftDomain :: domains, body, rfl, Nat.succ_le_succ hn⟩

theorem AuxiliaryFamilySource.auxiliarySpecialization
    {ves : VEnvs} {isUnsafe : Bool} {prodEnv : Environment}
    {params : Array Expr} {nparams : Nat}
    {finalState : Lean4Lean.ElimNestedInductive.State}
    {targetConcrete : InductiveType}
    {H : LoweredAuxiliaryFamily prodEnv params nparams finalState
      targetConcrete}
    {sourceTypesVEnv : VEnv} {lparams : List Name} {target : VInductiveType}
    {baseVEnv : VEnv}
    (N : AuxiliaryFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (hbase : baseVEnv = ves.venv (if isUnsafe then .unsafe else .safe))
    (wf : ves.WF prodEnv) (decl : VInductDecl)
    (huvars : decl.uvars = lparams.length) (hnparams : decl.nparams = nparams)
    (hunsafe : decl.isUnsafe = isUnsafe)
    (hle : baseVEnv ≤ sourceTypesVEnv) {paramCtx : List VExpr}
    (hctx : VEnv.IsDefEqCtx baseVEnv lparams.length [] N.sourceParams.reverse
      paramCtx) :
    ∃ a : ContainerSpecialization,
      SpecializationGenerates
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceTypesVEnv paramCtx
        decl a N.source ∧
      a.auxiliary = N.source.name ∧ a.source = N.containerFamily := by
  subst hbase
  rcases List.mem_iff_getElem.mp N.familyMember with ⟨idx, hidx, hfamily⟩
  let a : ContainerSpecialization := {
    container := N.container
    family := ⟨idx, hidx⟩
    auxiliary := N.source.name
    levels := N.levels
    arguments := N.baseArgs }
  have hsource : a.source = N.containerFamily := hfamily
  have habstract : (ves.venv (if isUnsafe then .unsafe else .safe)).constants
      H.generated.sourceName = some N.container.types[idx].toVConstant := by
    rw [← N.containerName, ← hfamily]
    exact N.installedBase.familyConstant idx hidx
  have htrConst := ((wf.tr (safety := if isUnsafe then .unsafe else .safe)).find?_uniq
    H.generated.built.lookup habstract).2
  have hvisible := htrConst.1
  have hfamilyPrefix : HasForallPrefix a.source.type a.arguments.length := by
    rcases H.generated.built.opening with ⟨_, Htelescope, _⟩
    rcases Htelescope.reflect_instantiateLevelParams with ⟨_, Hsource, _⟩
    have Hshape := TrExprS.targetArityOfForallTelescope htrConst.2.2 Hsource
    have hlength : a.arguments.length = H.generated.nestedNParams := by
      have h := Lean4Lean.List.Forall₂.length_eq N.baseTranslations
      simp only [List.length_map, List.length_take, Array.length_toList] at h
      change N.baseArgs.length = _
      rw [← h]
      exact Nat.min_eq_left H.generated.argsArity
    rw [hlength, hsource, ← hfamily]
    exact sameTelescopeArity_hasForallPrefix Hshape
  have hsafety : decl.isUnsafe = true ∨ N.container.isUnsafe = false := by
    rw [hunsafe, ← N.containerUnsafe]
    exact inductInfo_safety_of_visible hvisible
  refine ⟨a, ?_, rfl, hsource⟩
  refine {
    installed := N.installedBase
    auxiliary := rfl
    generatedUvars := N.sourceUvars.trans huvars.symm
    argumentsLength := N.baseArgsLength
    argumentsClosed := ?_
    levelsLength := N.levelsLength
    levelsWF := by rw [huvars]; exact N.levelsWF
    safety := hsafety
    familyForallPrefix := hfamilyPrefix
    application := ?_
    constructorShapes := ?_ }
  · intro arg harg
    rw [hnparams, ← N.sourceParamsLength]
    exact N.baseArgsClosed arg harg
  · refine ⟨N.sourceParams, N.sourceParamsLength.trans hnparams.symm,
      by rw [huvars]; exact VEnv.IsDefEqCtx.mono hle hctx,
      by rw [huvars]; exact N.sourceParamsWF, ?_, ?_, ?_⟩
    · rw [hsource, huvars]
      simpa only [abstractForallContext_toCtx, VLCtx.toCtx, List.append_nil]
        using N.familyApplicationTyping
    · rw [hsource, huvars]
      exact N.familyType
    · rw [hsource, huvars]
      exact N.constructors
  · refine ⟨N.sourceParams, N.sourceParamsLength.trans hnparams.symm, ?_⟩
    rw [hsource, huvars]
    exact N.constructorShapes


theorem exists_forall₂_of_forall {R : α → β → Prop} :
    ∀ {l : List β}, (∀ y ∈ l, ∃ x, R x y) → ∃ xs, List.Forall₂ R xs l
  | [], _ => ⟨[], .nil⟩
  | y :: l, H => by
    rcases H y List.mem_cons_self with ⟨x, hx⟩
    rcases exists_forall₂_of_forall (fun z hz => H z (List.mem_cons_of_mem _ hz)) with
      ⟨xs, hxs⟩
    exact ⟨x :: xs, .cons hx hxs⟩

theorem forall₂_trInductiveType_names
    (H : List.Forall₂ (TrInductiveType env envTypes lparams) types decl) :
    decl.map (·.name) = types.map (·.name) := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih, ← h.header.name]

theorem familyNames_drop_sublist (types : List VInductiveType) (n : Nat) :
    (familyNames (types.drop n)).Sublist (familyNames types) := by
  conv => rhs; rw [← List.take_append_drop n types]
  simp only [familyNames, List.flatMap_append]
  exact List.sublist_append_right _ _

/-! ### Executable constructor-name restoration -/

/-- `P` is a (non-strict) prefix of a hierarchical name. -/
inductive NamePrefix (P : Name) : Name → Prop
  | refl : NamePrefix P P
  | str {p : Name} (s : String) : NamePrefix P p → NamePrefix P (.str p s)
  | num {p : Name} (n : Nat) : NamePrefix P p → NamePrefix P (.num p n)

private def nameDepth : Name → Nat
  | .anonymous => 0
  | .str p _ => nameDepth p + 1
  | .num p _ => nameDepth p + 1

theorem Name.replacePrefix_self (A P : Name) : A.replacePrefix A P = P := by
  cases A <;> simp [Name.replacePrefix]

private theorem NamePrefix.depth_le (H : NamePrefix P x) : nameDepth P ≤ nameDepth x := by
  induction H with
  | refl => exact Nat.le_refl _
  | str _ _ ih => simp only [nameDepth]; omega
  | num _ _ ih => simp only [nameDepth]; omega

theorem NamePrefix.replacePrefix_nameDepth (H : NamePrefix P x) (A : Name) :
    nameDepth A ≤ nameDepth (x.replacePrefix P A) ∧
      (x ≠ P → nameDepth A < nameDepth (x.replacePrefix P A)) := by
  induction H with
  | refl => simp [Name.replacePrefix_self]
  | @str p s H ih =>
    have hne : Name.str p s ≠ P := by
      intro h; have := H.depth_le; rw [← h] at this; simp [nameDepth] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkStr, nameDepth]
    constructor <;> omega
  | @num p n H ih =>
    have hne : Name.num p n ≠ P := by
      intro h; have := H.depth_le; rw [← h] at this; simp [nameDepth] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkNum, nameDepth]
    constructor <;> omega

theorem NamePrefix.replacePrefix_replacePrefix (H : NamePrefix P x) (A : Name) :
    (x.replacePrefix P A).replacePrefix A P = x := by
  induction H with
  | refl => simp [Name.replacePrefix_self]
  | @str p s H ih =>
    have hne : Name.str p s ≠ P := by
      intro h; have := H.depth_le; rw [← h] at this; simp [nameDepth] at this; omega
    have hnameDepth := (H.replacePrefix_nameDepth A).1
    have hne' : Name.str (p.replacePrefix P A) s ≠ A := by
      intro h; have := congrArg nameDepth h; simp [nameDepth] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkStr, hne', ih]
  | @num p n H ih =>
    have hne : Name.num p n ≠ P := by
      intro h; have := H.depth_le; rw [← h] at this; simp [nameDepth] at this; omega
    have hnameDepth := (H.replacePrefix_nameDepth A).1
    have hne' : Name.num (p.replacePrefix P A) n ≠ A := by
      intro h; have := congrArg nameDepth h; simp [nameDepth] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkNum, hne', ih]

theorem namePrefix_of_replacePrefix_ne {x P A : Name}
    (h : x.replacePrefix P A ≠ x) : NamePrefix P x := by
  induction x with
  | anonymous =>
    cases P with
    | anonymous => exact .refl
    | str => simp [Name.replacePrefix] at h
    | num => simp [Name.replacePrefix] at h
  | str p s ih =>
    by_cases hP : Name.str p s = P
    · subst hP; exact .refl
    · simp only [Name.replacePrefix, beq_iff_eq, hP, if_false, Name.mkStr] at h
      exact .str s (ih fun h' => h (by rw [h']))
  | num p n ih =>
    by_cases hP : Name.num p n = P
    · subst hP; exact .refl
    · simp only [Name.replacePrefix, beq_iff_eq, hP, if_false, Name.mkNum] at h
      exact .num n (ih fun h' => h (by rw [h']))

/-- Executable and abstract constructor restoration agree on every
auxiliary constructor: the executable renames the lowered constructor
`a.constructorName ctor` back along the auxiliary/container prefix recorded by
lowering, and the abstract table maps it to the container constructor.  The
only side condition is that lowering actually renamed the constructor (which
is the case whenever the lowered constructor name is fresh). -/
theorem restoreCtorName_eq_restoredHeadName
    {decl : VInductDecl} {auxiliaries : List ContainerSpecialization}
    (hnodup : (auxiliaries.flatMap (·.headNames)).Nodup)
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries)
    {ctor : VConstVal} (hctor : ctor ∈ a.source.ctors)
    (hrenamed : a.constructorName ctor ≠ ctor.name)
    (r : Lean4Lean.ElimNestedInductive.Result) (env' : Environment)
    {e : Expr} {ls : List Level}
    (hget : r.getNestedIfAuxCtor env' (a.constructorName ctor) =
      some (e, a.auxiliary))
    (hhead : e.getAppFn = .const a.source.name ls) :
    r.restoreCtorName env' (a.constructorName ctor) =
      (compilationRestoration decl auxiliaries).restoredHeadName
        (a.constructorName ctor) := by
  rw [restoreCtorName_eq r env' _ _ _ e ls hget hhead,
    compilationRestoration_restoredHeadName_constructor hnodup ha hctor]
  exact (namePrefix_of_replacePrefix_ne hrenamed).replacePrefix_replacePrefix _

theorem Expr.getAppFn_abstractN_const {e : Expr} {xs : List FVarId} {k : Nat}
    {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.abstractN xs k).getAppFn = .const n ls := by
  induction e generalizing k with
  | app f a ihf _ =>
    simp only [Expr.abstractN, Expr.getAppFn] at H ⊢
    exact ihf H
  | const => simpa [Expr.abstractN] using H
  | _ => simp [Expr.getAppFn] at H

theorem Expr.getAppFn_instantiate1'_of_const {e s : Expr} {d : Nat}
    {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.instantiate1' s d).getAppFn = .const n ls := by
  induction e generalizing d with
  | app f a ihf _ =>
    simp only [Expr.instantiate1', Expr.getAppFn] at H ⊢
    exact ihf H
  | const => simpa [Expr.instantiate1'] using H
  | _ => simp [Expr.getAppFn] at H

theorem Expr.getAppFn_instantiateList_of_const {e : Expr} {subst : List Expr}
    {k : Nat} {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.instantiateList subst k).getAppFn = .const n ls := by
  induction subst generalizing e with
  | nil => simpa [Expr.instantiateList] using H
  | cons s subst ih =>
    simp only [Expr.instantiateList]
    exact ih (Expr.getAppFn_instantiate1'_of_const H)

theorem AuxiliaryFamilySpec.nested_getAppFn
    {env : Environment} {lctx : LocalContext} {params As : Array Expr}
    {levels : List Level} {nparams : Nat} {args : Array Expr}
    {sourceName auxName : Name} {sourceInfo : InductiveVal}
    {data : Lean4Lean.ElimNestedInductive.AuxiliaryData}
    (H : AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (sel : CDeclArray lctx As) (harity : nparams ≤ args.size) :
    data.nested.getAppFn = .const sourceName levels := by
  rw [H.nested, sel.expressions, Expr.instantiateRev_eq, Expr.instantiate_eq]
  apply Expr.getAppFn_instantiateList_of_const
  have h := Expr.abstractN_eq (mkAppRange (.const sourceName levels) 0 nparams args) sel.fvars
  simp only [List.toArray] at h ⊢
  rw [h]
  apply Expr.getAppFn_abstractN_const
  rw [Expr.mkAppRange_from_zero _ _ _ harity, Expr.getAppFn_mkAppList]
  rfl
private theorem constructorListEntries_findInduct
    {stats : AddInductive.InductiveStats} {lparams : List Name}
    {isUnsafe : Bool} {owner : InductiveType} {ctors : List Constructor}
    {entries : List (ConstantInfo × VConstVal)} {ctor : Constructor}
    {initial : Nat}
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      initial ctors entries)
    (hctor : ctor ∈ ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.induct = owner.name := by
  induction H with
  | nil => simp at hctor
  | @cons start head tail tailEntries value Htail ih =>
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact ⟨AddInductive.constructorInfo stats lparams isUnsafe owner
        start ctor, value, by simp,
        by simp [AddInductive.constructorInfo],
        by simp [AddInductive.constructorInfo]⟩
    · rcases ih htail with ⟨info, value', hmem, hname, hinduct⟩
      exact ⟨info, value', by simp [hmem], hname, hinduct⟩

theorem ConstructorTypeEntries.findInduct
    {stats : AddInductive.InductiveStats} {lparams : List Name}
    {isUnsafe : Bool} {types : List InductiveType} {owner : InductiveType}
    {entries : List (ConstantInfo × VConstVal)} {ctor : Constructor}
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (howner : owner ∈ types) (hctor : ctor ∈ owner.ctors) :
    ∃ info : ConstructorVal, ∃ value : VConstVal,
      (.ctorInfo info, value) ∈ entries ∧
      info.name = ctor.name ∧ info.induct = owner.name := by
  induction H generalizing owner with
  | nil => simp at howner
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at howner
    rcases howner with rfl | htailOwner
    · rcases constructorListEntries_findInduct Hhead hctor with
        ⟨info, value, hmem, hname, hinduct⟩
      exact ⟨info, value, List.mem_append_left _ hmem, hname, hinduct⟩
    · rcases ih htailOwner hctor with ⟨info, value, hmem, hname, hinduct⟩
      exact ⟨info, value, List.mem_append_right _ hmem, hname, hinduct⟩

/-- Every lowered constructor is installed in the lowered kernel
environment as a constructor of its own lowered family, and its name was
fresh in the abstract source environment. -/
private theorem loweredConstructor_facts
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {types : List InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv)
    {t : VInductiveType} (ht : t ∈ decl.types)
    {ctor : VConstVal} (hctor : ctor ∈ t.ctors) :
    (∃ info : ConstructorVal, outEnv.find? ctor.name = some (.ctorInfo info) ∧
      info.induct = t.name) ∧
    sourceEnv.constants ctor.name = none := by
  constructor
  · rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types t ht with
      ⟨T, hT, htrT⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r htrT.ctors ctor hctor with
      ⟨C, hC, htrC⟩
    rcases ConstructorTypeEntries.findInduct R.declared.sourceAligned
        (by simpa using hT) hC with ⟨info, value, hmem, hname, hinduct⟩
    refine ⟨info, ?_, ?_⟩
    · rw [htrC.name, ← hname]
      exact H.findConstructorOfMem hmem
    · rw [hinduct, ← htrT.header.name]
  · have hmem : ctor ∈ decl.constructorConstants := by
      simp only [VInductDecl.constructorConstants, List.mem_flatMap]
      exact ⟨t, ht, hctor⟩
    have hfresh := (VEnv.addConstVals_names_fresh R.core.ctorsAdded).2 ctor hmem
    cases hsource : sourceEnv.constants ctor.name with
    | none => rfl
    | some ci =>
      have := (VEnv.addConstVals_le R.core.typesAdded).constants hsource
      rw [hfresh] at this
      cases this

/-- Lowered type, constructor and recursor names are jointly distinct: each
is looked up in the lowered kernel environment as an inductive,
constructor and recursor respectively. -/
private theorem loweredNames_nodup
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {types : List InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hc : ContextWF c) (H : RecursorCheck R.toConstructorCheck outEnv) :
    (familyNames decl.types ++
      decl.types.map (fun t => t.name.str "rec")).Nodup := by
  have hsource := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  have htypes : (decl.types.map (·.name)).Nodup := by
    have h := (List.nodup_append.mp hsource).1
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using h
  refine List.nodup_append.mpr ⟨familyNames_nodup hsource, ?_, ?_⟩
  · have h : List.Pairwise (fun x y : Name => x.str "rec" ≠ y.str "rec")
        (decl.types.map (·.name)) :=
      List.Pairwise.imp (fun hne h => hne (Name.str.inj h).1) htypes
    simpa [List.Nodup, List.pairwise_map] using h
  · intro x hx y hy hxy
    subst hxy
    rcases List.mem_map.mp hy with ⟨t, ht, hrec⟩
    rcases List.mem_iff_getElem.mp ht with ⟨k, hk, rfl⟩
    have hkTypes : k < types.length := by
      rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]; exact hk
    have htr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core k hkTypes hk
    rcases H.findSourceRecursor k (by simpa using hkTypes) with
      ⟨recInfo, hrecFind, _⟩
    have hget : types.toArray[k]! = types[k] := by
      simp [hkTypes]
    rw [hget, show Lean.mkRecName types[k].name = x by
      rw [← hrec, ← htr.header.name]; rfl] at hrecFind
    rcases List.mem_flatMap.mp hx with ⟨t', ht', hx'⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r R.core.types t' ht' with
      ⟨T, hT, htrT⟩
    rcases List.mem_cons.mp hx' with hname | hctor
    · rcases H.findSourceHeader Hc (owner := T) (by simpa using hT) with
        ⟨info, hfind, _, _⟩
      rw [show T.name = x by rw [hname, ← htrT.header.name]] at hfind
      rw [hfind] at hrecFind
      cases hrecFind
    · rcases List.mem_map.mp hctor with ⟨c', hc', hcname⟩
      rcases Lean4Lean.List.Forall₂.forall_exists_r htrT.ctors c' hc' with
        ⟨C, hC, htrC⟩
      rcases H.findSourceConstructor (by simpa using hT) hC with
        ⟨info, hfind, _⟩
      rw [show C.name = x by rw [← hcname, ← htrC.name]] at hfind
      rw [hfind] at hrecFind
      cases hrecFind

/-- The container specialisations of a validated nested run, one per
generated auxiliary family in lowered order, together with their installed
container certificates at the source environment, the lowering
expansion of each generated family into the lowered suffix, and agreement of
the abstract recursor renaming with the executable `mkAuxRecNameMap`. -/
theorem NestedRun.containerSpecializations
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (generated : List VInductiveType)
        (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      List.Forall₂ (SpecializationGenerates
        (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
        E.lowered.headers.commonParameterContext sourceDecl)
        auxiliaries generated ∧
      List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          (VInductDecl.NestedOccurrenceReplacementAbs
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
        generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length) ∧
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup ∧
      (∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
        result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            (a.constructorName ctor)) ∧
      (∀ name, (compilationRestoration sourceDecl auxiliaries).recursorName name =
        ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.find? name).getD
          name) := by
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : P.nparams = nparams := E.lowered_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  let initialState := E.initialState
  have Hlower : NestedLoweringOutputClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hpack := E.phases
  let R := Hpack.constructors
  let Hprod := Hpack.recursors
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.sourceCoreDecl_eq] using E.sourceCore.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hpack.headers.context.venv
        R.declared.venvCtors := by
    exact R.core
  have Hmetadata : SourcePrefixOfLowered sourceDecl P.loweredDecl := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.checked
  have wfP : ves.WF P.c.env := by
    simpa only [henv] using wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.sourceCore.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    simpa only [hinitial, safety] using E.sourceCore.sourceAdded
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource
      (by simpa only [hinitial, safety] using
        (wf.tr (safety := safety)).wf)
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := by
    rfl
  rcases Hrun.auxiliaryFamilySources Hcache Hparams wfP
      hinitial HcP Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, hNctx⟩
  have hctxEq : N.parameterContext = P.headers.commonParameterContext := by
    exact hNctx.trans E.phases_commonParameterContext
  have Htypes := Hrun.allExpansionsOfSources Hcache Hparams Hsource
    Htarget Hmetadata Hsources
      (VEnvs.WF.environmentTypesClosed wfP) wfP.inductivesClosed
      (by simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf)
      hempty N E.auxiliarySelection
  have hsourceLength : sourceTypes.length = sourceDecl.types.length :=
    TrInductDeclCore.types_length Hsource
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  have hgeneratedLength := N.length
  have hvals : sourceDecl.typeConstants =
      (P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal := by
    have h := E.sourceCore.sourceTypeValues
    rw [E.sourceCoreDecl_eq] at h
    exact h
  have hadded : (ves.venv safety).addConstVals sourceDecl.typeConstants =
      some E.sourceCore.envTypes := by
    have h := HsourceAdded
    rw [hinitial, ← hvals] at h
    exact h
  have hprefixLength : sourceDecl.types.length =
      (P.loweredDecl.types.take sourceDecl.types.length).length := by
    simp only [List.length_take]
    omega
  have Hparts := (Lean4Lean.List.Forall₂.append_of_left hprefixLength).mp
    (by rw [List.take_append_drop]; exact Htypes)
  have hbaseLE : P.initialEnv ≤ E.sourceCore.envTypes :=
    VEnv.addConstVals_le HsourceAdded
  have Hmap : NestedAuxMapModels result finalState :=
    Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have Hpoint : ∀ family ∈ N.generated, ∃ a,
      SpecializationGenerates (ves.venv safety) E.sourceCore.envTypes
        N.parameterContext sourceDecl a family ∧
      ∃ nested levels, result.aux2nested.find? a.auxiliary = some nested ∧
        nested.getAppFn = .const a.source.name levels := by
    intro family hfamily
    rcases List.mem_iff_getElem.mp hfamily with ⟨i, hi, rfl⟩
    have hresult : sourceTypes.length + i < result.types.length := by omega
    have hlowered : sourceTypes.length + i < P.loweredDecl.types.length := by
      omega
    rcases N.parametersAt i hi hresult hlowered with ⟨Horigin, NN, hNN, hctx⟩
    rw [← hNN]
    rcases NN.auxiliarySpecialization hinitial wfP sourceDecl Hsource.uvars
      Hsource.nparams (Hsource.isUnsafe.trans hisUnsafe) hbaseLE hctx with
      ⟨a, hev, haux, hsrc⟩
    refine ⟨a, hev, Horigin.generated.data.nested, Horigin.generated.levels,
      ?_, ?_⟩
    · rw [haux, NN.sourceName]
      exact Hmap _ _ Horigin.generated.cached
    · rw [hsrc, NN.containerName]
      exact Horigin.generated.built.nested_getAppFn Horigin.generated.selection
        Horigin.generated.argsArity
  rcases exists_forall₂_of_forall Hpoint with ⟨auxiliaries, Haux'⟩
  have Haux := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) Haux'
  have Hexpansion := Hparts.2
  have hauxNames := auxiliarySpecializations_names Haux Hexpansion
  rw [hctxEq] at Haux Haux'
  generalize N.generated = generated at Haux Haux' Hexpansion
  rw [hinitial] at Hexpansion
  refine ⟨E.sourceCore.envTypes, generated, auxiliaries, hadded,
    HsourceTypesWF, Haux, Hexpansion, loweredNames_nodup HcP Hprod, ?_, ?_⟩
  · -- executable constructor-name restoration
    have hheadsNodup : (auxiliaries.flatMap (·.headNames)).Nodup := by
      rw [auxiliarySpecializations_headNames Haux Hexpansion]
      have h := (List.nodup_append.mp (loweredNames_nodup HcP Hprod)).1
      exact h.sublist (familyNames_drop_sublist _ _)
    intro a ha ctor hctor
    rcases Lean4Lean.List.Forall₂.forall_exists_l Haux' a ha with
      ⟨g, hg, hev, nested, levels, hfindAux, hhead⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hexpansion g hg with
      ⟨t, ht, hexp⟩
    have htLowered : t ∈ P.loweredDecl.types := List.mem_of_mem_drop ht
    have hnames : t.ctors.map (·.name) = a.source.ctors.map a.constructorName :=
      (nestedConstructorExpansions_names hexp.constructors).trans
        hev.generatedCtorNames
    have hcmem : a.constructorName ctor ∈ t.ctors.map (·.name) := by
      rw [hnames]; exact List.mem_map_of_mem hctor
    rcases List.mem_map.mp hcmem with ⟨c', hc', hc'name⟩
    rcases loweredConstructor_facts Hprod htLowered hc' with
      ⟨⟨info, hfind, hinduct⟩, hfresh⟩
    rw [hc'name] at hfind hfresh
    have hinduct' : info.induct = a.auxiliary := by
      rw [hinduct, hexp.name, hev.auxiliary]
    have hget : result.getNestedIfAuxCtor E.loweredEnv (a.constructorName ctor) =
        some (nested, a.auxiliary) := by
      simp [Lean4Lean.ElimNestedInductive.Result.getNestedIfAuxCtor, hfind,
        hinduct', hfindAux]
    have hrenamed : a.constructorName ctor ≠ ctor.name := by
      intro heq
      rcases List.mem_iff_getElem.mp hctor with ⟨k, hk, hkEq⟩
      have hlookup := hev.installed.constructorConstant a.family k a.family.isLt hk
      have hsome : (ves.venv safety).constants ctor.name ≠ none := by
        rw [← hkEq]
        change (ves.venv safety).constants
          ((a.container.types[(a.family : Nat)]'a.family.isLt).ctors[k]'hk).name
            ≠ none
        rw [hlookup]
        simp
      rw [← hinitial, ← heq, hfresh] at hsome
      exact hsome rfl
    exact restoreCtorName_eq_restoredHeadName hheadsNodup ha hctor hrenamed
      result E.loweredEnv hget hhead
  rcases Hrun.source with
    ⟨main, rest, _tail, _paramsState, _lctx, _params, hsourceTypes, _⟩
  have hmainMem : main ∈ sourceTypes := by rw [hsourceTypes]; simp
  rcases Hrun.preservesInitialTypeName ⟨main, by simpa using hmainMem, rfl⟩ with
    ⟨loweredMain, hloweredMain, hloweredName⟩
  rcases Hprod.findSourceHeader HcP (by simpa using hloweredMain) with
    ⟨info, hfind, _hctors, hall⟩
  rw [hloweredName] at hfind
  generalize E.loweredEnv = loweredEnv at hfind ⊢
  rw [hsourceTypes]
  have hsourceNames := forall₂_trInductiveType_names Hsource.types
  have hloweredNames := forall₂_trInductiveType_names Htarget.types
  have hfirst : sourceDecl.types.head?.map (·.name) = some main.name := by
    have h := congrArg List.head? hsourceNames
    rw [hsourceTypes] at h
    simpa [List.head?_map] using h
  have hnames : auxiliaries.map (·.auxiliary) =
      info.all.drop (main :: rest).length := by
    rw [hauxNames, hall, List.map_drop, hloweredNames, ← hsourceLength,
      hsourceTypes]
  have hnodup : (auxiliaries.map (·.auxiliary)).Nodup := by
    have h := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)).1
    have htypes : (P.loweredDecl.types.map (·.name)).Nodup := by
      simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
        Function.comp_def] using h
    rw [hauxNames, List.map_drop]
    exact htypes.sublist (List.drop_sublist _ _)
  exact compilationRestoration_recursorName_eq_mkAuxRecNameMap sourceDecl
    auxiliaries main rest loweredEnv info hfind hfirst hnames hnodup


/-- The common header parameter context of the lowered run is a
well-formed context of the source environment, at the declaration's
universe arity. -/
theorem NestedRun.commonParameterContext_refl
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) :
    VEnv.IsDefEqCtx (ves.venv (if isUnsafe then .unsafe else .safe))
      sourceDecl.uvars [] E.lowered.headers.commonParameterContext
      E.lowered.headers.commonParameterContext := by
  have hctx := E.lowered.headers.sourceStatsWF.paramsContext
  change VEnv.IsDefEqCtx _ _ [] _ E.lowered.headers.commonParameterContext at hctx
  generalize E.lowered.headers.commonParameterContext = L₂ at hctx ⊢
  generalize E.lowered.headers.sourceStatsWF.headers.params.reverse = L₁
    at hctx
  rw [E.lowered.headers.sourceContextVEnv, E.lowered_initialEnv] at hctx
  have henv : (ves.venv (if isUnsafe then .unsafe else .safe)).WF :=
    (wf.tr (safety := if isUnsafe then .unsafe else .safe)).wf
  have huvars : sourceDecl.uvars = E.lowered.c.lparams.length := by
    have h := E.sourceCore.core.uvars
    rw [E.sourceCoreDecl_eq] at h
    rw [h, E.lowered_c, E.context_lparams]
  rw [huvars]
  exact VEnv.IsDefEqCtx.refl (hctx.symm henv.ordered).isType

end VerifyInductive
end Lean4Lean
