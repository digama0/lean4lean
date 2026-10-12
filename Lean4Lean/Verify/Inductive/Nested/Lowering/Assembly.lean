import Lean4Lean.Verify.Inductive.Nested.Lowering.Ordinary
import Lean4Lean.Verify.Inductive.Nested.Lowering.Counts

/-! # The fields of `NestedLoweringOutput`

Each field of the lowering interface (`Verify/Inductive/Lowering.lean`), proved from the run
relation `NestedLoweringOutputClosed` that `ElimNestedInductive.run'.translationClosed` gives for
a successful run from the executable's initial state. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The executable's initial lowering state. -/
abbrev loweringInitialState (lparams : List Name) (types : List InductiveType) :
    ElimNestedInductive.State :=
  { lvls := lparams.map .param, newTypes := types.toArray }

/-- A successful lowering run from the executable's initial state is a closed lowering. -/
theorem loweringRun.closedOfRun {env : Environment} {ves : VEnvs} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ())
    (h : (ElimNestedInductive.run fuel nparams types env).run'
      (loweringInitialState lparams types) = .ok res) :
    NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types) res :=
  ElimNestedInductive.run'.translationClosed fuel nparams types env _ wf.inductivesClosed
    (VEnvs.WF.environmentTypesClosed wf) (checkInductiveSources_refines env types _ hsources)
    rfl rfl _ h

section
variable {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

theorem NestedLoweringOutputClosed.nparams_eq
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : res.nparams = nparams := by
  obtain ⟨_, Hrun, -, -⟩ := H
  exact Hrun.resultNParams

theorem NestedLoweringOutputClosed.params_size
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : res.params.size = nparams := by
  obtain ⟨_, Hrun, -, -⟩ := H
  exact Hrun.resultParamsSize

theorem NestedLoweringOutputClosed.source_nonempty
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : types ≠ [] := by
  obtain ⟨_, Hrun, -, -⟩ := H
  obtain ⟨first, rest, -, -, -, -, htypes, -⟩ := Hrun.source
  rw [htypes]; simp

theorem NestedLoweringOutputClosed.lctx_params
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    res.params.toList.reverse.map (·.fvarId!) = res.lctx.fvars ∧
      ∀ p ∈ res.params.toList, p.isFVar := by
  obtain ⟨_, Hrun, -, fvars, hparams, -⟩ := H
  have hrev := Hrun.resultParams_reverse_fvars
  refine ⟨?_, ?_⟩
  · rw [hrev, List.map_map]
    exact List.map_id'' (fun _ => rfl) _
  · intro p hp
    rw [hparams] at hp
    simp at hp
    obtain ⟨fv, -, rfl⟩ := hp
    rfl

theorem NestedLoweringOutputClosed.params_opening
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    ∃ first rest tail, types = first :: rest ∧
      LoweringParamOpening {} #[] first.type nparams res.lctx tail res.params ∧
      res.lctx.WF ∧ (∀ fv ∈ res.lctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv) ∧
      ∃ fvars : List FVarId, res.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup := by
  obtain ⟨_, Hrun, -, Hnodup⟩ := H
  have hfresh := Hrun.resultContextKernelFresh rfl
  have hwf := Hrun.resultContextWF
  obtain ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening, -, -, -, -, -, -,
    Hqueue⟩ := Hrun.source
  obtain ⟨hlctx, hparams⟩ := Hqueue.resultContext
  refine ⟨first, rest, tail, htypes, ?_, hwf, hfresh, Hnodup⟩
  rw [hlctx, hparams]
  exact Hopening

theorem NestedLoweringOutputClosed.types_length
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : res.types.length = types.length + res.aux2nested.size := by
  obtain ⟨finalState, Hrun, -, -⟩ := H
  have hnodup := Hrun.resultNamesNodupOfEmpty (by rfl)
  obtain ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening, hnewTypes, hnestedAux,
    -, -, -, -, Hqueue⟩ := Hrun.source
  have Hbal : SizeBalanced types.length finalState := by
    apply Hqueue.sizeBalanced
    unfold SizeBalanced
    rw [hnewTypes, hnestedAux]
    show types.toArray.size = types.length + (#[] : Array (Expr × Name)).size
    simp
  have hmap := Hrun.resultAuxMap
  have hsize : res.aux2nested.size = finalState.nestedAux.size := by
    rw [hmap]
    change (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp) (entry : Expr × Name) =>
        map.insert entry.2 entry.1) {}).size = _
    rw [← Array.foldl_toList, nestedAuxFold_size _ _ hnodup (by simp)]
    simp
  rw [hsize, Hqueue.resultTypes]
  simpa [SizeBalanced] using Hbal

theorem NestedLoweringOutputClosed.ordinary
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res)
    (hsources : checkInductiveSources env types = .ok ()) (hclosed : SourceBVarClosed types)
    (haux : res.aux2nested.size = 0) : res.types = types :=
  NestedLoweringRun.types_eq_source_of_aux2nested_size_eq_zero
    (initialState := loweringInitialState lparams types) H.toResult
    (checkInductiveSources_refines env types _ hsources) hclosed rfl haux

end

theorem ConstructorLowerings.Resolved.forall₂
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources state out) :
    List.Forall₂ (fun target source => ∃ before after,
      ConstructorLowering.Resolved env params nparams finalResult source before (target, after))
      out.1 sources := by
  induction H with
  | nil => exact .nil
  | cons Hhead _ ih => exact .cons ⟨_, _, Hhead⟩ ih

theorem ConstructorLowerings.Resolved.names
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources state out) :
    out.1.map (·.name) = sources.map (·.name) := by
  induction H with
  | nil => rfl
  | cons Hhead _ ih => simp only [List.map_cons, ih, Hhead.name]

theorem forall₂_imp_mem {R S : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b →
      (∀ x ∈ a, ∀ y ∈ b, R x y → S x y) → List.Forall₂ S a b
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, H =>
    .cons (H _ (by simp) _ (by simp) h)
      (forall₂_imp_mem t fun x hx y hy => H x (by simp [hx]) y (by simp [hy]))

/-- A positional relation on the first `types.length` families of a list that extends it. -/
theorem forall₂_take_of_getElem? {R : InductiveType → InductiveType → Prop}
    {lowered types : List InductiveType} (hlen : types.length ≤ lowered.length)
    (H : ∀ j (hj : j < types.length), ∃ target, lowered[j]? = some target ∧ R target types[j]) :
    List.Forall₂ R (lowered.take types.length) types := by
  refine List.forall₂_of_getElem (by simp [hlen]) fun j hj hj' => ?_
  obtain ⟨target, htarget, hR⟩ := H j hj'
  have : (lowered.take types.length)[j] = target := by
    rw [List.getElem_take]
    exact (List.getElem?_eq_some_iff.mp htarget).2
  rw [this]
  exact hR

section
variable {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

/-- The lowering of the `j`-th source family, against the final result. -/
theorem NestedLoweringOutputClosed.sourceMapping
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (hj : j < types.length) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      res.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup ∧ res.params.size = nparams ∧
      FamilyLowering.Resolved env res.params nparams res types[j] stepState
        (target, loweredState) ∧
      res.types[j]? = some target :=
  NestedLoweringOutputClosed.sourceResolvedMappingAtFreshAligned
    (initialState := loweringInitialState lparams types) H (by rfl) hj

theorem NestedLoweringOutputClosed.source_headers
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    List.Forall₂ (fun lowered source => lowered.name = source.name ∧
        lowered.type = source.type ∧ lowered.ctors.map (·.name) = source.ctors.map (·.name))
      (res.types.take types.length) types := by
  refine forall₂_take_of_getElem? ?_ fun j hj => ?_
  · rw [H.types_length]; exact Nat.le_add_right _ _
  obtain ⟨_, _, target, _, -, -, -, Hfam, htarget⟩ := H.sourceMapping hj
  exact ⟨target, htarget, Hfam.name, Hfam.type, Hfam.constructors.names⟩

theorem NestedLoweringOutputClosed.restore_source
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res)
    (hsources : checkInductiveSources env types = .ok ()) (hclosed : SourceBVarClosed types)
    (loweredEnv : Environment) :
    List.Forall₂ (fun lowered source => List.Forall₂
        (fun (lc sc : Constructor) => RestoreSourceDisjoint res loweredEnv sc.type →
          (res.restoreNested loweredEnv lc.type == sc.type) = true)
        lowered.ctors source.ctors)
      (res.types.take types.length) types := by
  have Hchecked := checkInductiveSources_refines env types _ hsources
  have Hrestorable : ∀ type ∈ res.types, RestorableInductiveType nparams type := by
    obtain ⟨_, Hrun, -, -⟩ := H
    exact Hrun.resultRestorable
  refine forall₂_take_of_getElem? ?_ fun j hj => ?_
  · rw [H.types_length]; exact Nat.le_add_right _ _
  obtain ⟨fvars, _, target, _, hparams, hnodup, hsize, Hfam, htarget⟩ := H.sourceMapping hj
  refine ⟨target, htarget, ?_⟩
  have hmem : types[j] ∈ types := List.getElem_mem hj
  have htargetMem : target ∈ res.types := List.mem_of_getElem? htarget
  refine forall₂_imp_mem Hfam.constructors.forall₂ fun lc hlcMem sc hscMem hpair hdisjoint => ?_
  obtain ⟨before, after, Hctor⟩ := hpair
  have Htelescope : RestoreTelescope lc.type res.nparams := by
    rw [H.nparams_eq]
    exact Hrestorable target htargetMem lc hlcMem
  obtain ⟨Hinverse⟩ := Hctor.nestedRestoration_inverse rfl fvars hparams hnodup
    ((Hchecked.constructorsClosed hmem) sc hscMem) ((hclosed _ hmem).2 sc hscMem) hsize
    loweredEnv hdisjoint H.nparams_eq
    (restoreNested_refines res loweredEnv {} lc.type Htelescope)
  exact Hinverse.restoredType_eqv_source

end

theorem Expr.abstractN_mkAppList (xs : List FVarId) (k : Nat) :
    ∀ (l : List Expr) (f : Expr),
      (Expr.mkAppList f l).abstractN xs k =
        Expr.mkAppList (f.abstractN xs k) (l.map (·.abstractN xs k))
  | [], _ => rfl
  | a :: l, f => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [Expr.abstractN_mkAppList xs k l]
    rfl

theorem Expr.instantiateList_mkAppList (as : List Expr) (k : Nat) :
    ∀ (l : List Expr) (f : Expr),
      (Expr.mkAppList f l).instantiateList as k =
        Expr.mkAppList (f.instantiateList as k) (l.map (·.instantiateList as k))
  | [], _ => rfl
  | a :: l, f => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [Expr.instantiateList_mkAppList as k l, Expr.instantiateList_app]

theorem Expr.instantiateList_const (as : List Expr) (k : Nat) (c : Name) (ls : List Level) :
    (Expr.const c ls).instantiateList as k = .const c ls := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [Expr.instantiate1'] using ih

/-- Closing a constant application over parameters keeps its head and its argument count. -/
theorem Expr.closure_mkAppRange_const (c : Name) (ls : List Level) (n : Nat)
    (args : Array Expr) (hn : n ≤ args.size) (fvs : List FVarId) (ps : Array Expr) :
    ∃ args' : Array Expr, args'.size = n ∧
      ((mkAppRange (.const c ls) 0 n args).abstract (fvs.map Expr.fvar).toArray).instantiateRev
          ps = mkAppN (.const c ls) args' := by
  have hrange : mkAppRange (.const c ls) 0 n args =
      Expr.mkAppList (.const c ls) (args.toList.take n) :=
    Expr.mkAppRange_eq (l₁ := []) (l₃ := args.toList.drop n) (by simp) rfl
      (by simp; omega)
  refine ⟨((args.toList.take n).map fun a =>
      ((a.abstractN fvs 0).instantiateList ps.reverse.toList 0)).toArray, by simp; omega, ?_⟩
  rw [hrange, Expr.mkAppN_eq_mkAppList]
  have habs : (Expr.mkAppList (.const c ls) (args.toList.take n)).abstract
      (fvs.map Expr.fvar).toArray =
      (Expr.mkAppList (.const c ls) (args.toList.take n)).abstractN fvs := by
    rw [← Expr.abstractN_eq]
  rw [habs, Expr.instantiateRev_eq, Expr.instantiate_eq, Expr.abstractN_mkAppList,
    Expr.instantiateList_mkAppList]
  simp [Expr.abstractN, Expr.instantiateList_const, List.map_map, Function.comp_def]

theorem AuxiliaryConstructorSpecs.mem_name
    (H : AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily auxFamily
      sourceNames targets) :
    ∀ d ∈ targets, ∃ s ∈ sourceNames, d.name = s.replacePrefix sourceFamily auxFamily := by
  induction H with
  | nil => simp
  | cons Hhead _ ih =>
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · obtain ⟨_, _, _, _, hname, _⟩ := Hhead.source
      exact ⟨_, by simp, hname⟩
    · obtain ⟨s, hs, h⟩ := ih d hd
      exact ⟨s, by simp [hs], h⟩

theorem ConstructorLowerings.names
    (H : ConstructorLowerings env params nparams sources state out) :
    out.1.map (·.name) = sources.map (·.name) := by
  induction H with
  | nil => rfl
  | cons Hhead _ ih => simp only [List.map_cons, ih, Hhead.name]

section
variable {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

/-- Every family after the source block is a lowered auxiliary family. -/
theorem NestedLoweringOutputClosed.auxFamily {ves : VEnvs}
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ())
    {t : InductiveType} (ht : t ∈ res.types.drop types.length) :
    ∃ finalState, NestedLowering env fuel nparams types (loweringInitialState lparams types)
      (res, finalState) ∧
      Nonempty (LoweredAuxiliaryFamily env res.params nparams finalState t) := by
  obtain ⟨finalState, Hrun, -, -⟩ := H
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
  simp only [List.getElem_drop] at hk ⊢
  have hj : types.length + k < res.types.length := by
    simp at hk; omega
  exact ⟨finalState, Hrun, Hrun.resolvedAuxiliaryFamilyAt (VEnvs.WF.environmentTypesClosed wf)
    wf.inductivesClosed (checkInductiveSources_refines env types _ hsources) rfl
    (by simp) hj⟩

theorem LoweredAuxiliaryFamily.name_eq
    (O : LoweredAuxiliaryFamily env params nparams finalState t) :
    t.name = O.generated.auxName :=
  O.lowered.name.trans ((congrArg InductiveType.name O.generated.family_eq).trans
    O.generated.built.name)

theorem NestedLoweringOutputClosed.aux_cached {ves : VEnvs}
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ()) :
    ∀ t ∈ res.types.drop types.length, ∃ nested, res.aux2nested.find? t.name = some nested := by
  intro t ht
  obtain ⟨finalState, Hrun, ⟨O⟩⟩ := H.auxFamily wf hsources ht
  refine ⟨O.generated.data.nested, ?_⟩
  rw [O.name_eq]
  exact Hrun.resultAuxLookup (Hrun.resultNamesNodupOfEmpty (by rfl)) O.generated.cached

theorem NestedLoweringOutputClosed.cached_aux
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    ∀ n nested, res.aux2nested.find? n = some nested →
      n ∈ (res.types.drop types.length).map (·.name) := by
  intro n nested hfind
  obtain ⟨finalState, Hrun, -, -⟩ := H
  have hentry := Hrun.resolvedCacheEntryOfResultLookup hfind
  obtain ⟨j, hj, hinitial, hname⟩ :=
    (Hrun.resolvedAuxFamilyPosition (by rfl)).position nested n hentry
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, Hqueue⟩ := Hrun.source
  have htypes := Hqueue.resultTypes
  simp only [List.mem_map]
  have hinitial' : types.length ≤ j := by simpa using hinitial
  have hjr : j < res.types.length := by rw [htypes]; simpa using hj
  refine ⟨res.types[j], ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨j - types.length, by simp; omega, ?_⟩
    simp only [List.getElem_drop]
    congr 1; omega
  · have : res.types[j] = finalState.newTypes[j] := by
      rw [List.getElem_of_eq htypes]; exact Array.getElem_toList _
    rw [this]
    exact hname

theorem NestedLoweringOutputClosed.aux_fresh {ves : VEnvs}
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ()) :
    ∀ t ∈ res.types.drop types.length,
      env.find? t.name = none ∧ ∃ i : Nat, t.name = .num `_nested i := by
  intro t ht
  obtain ⟨finalState, Hrun, ⟨O⟩⟩ := H.auxFamily wf hsources ht
  rw [O.name_eq]
  have Hfresh := Hrun.resultNamesFresh (NestedAuxNamesFresh.empty env _ (by rfl))
  have Hwf := Hrun.resultNamesWF (NestedAuxNamesWF.empty _ (by rfl))
  obtain ⟨i, hi, -⟩ := Hwf.indexed _ _ O.generated.cached
  exact ⟨find?_none_of_contains_false (wf.tr (safety := .safe)).map_wf
    (Hfresh _ _ O.generated.cached), i, hi⟩

theorem NestedLoweringOutputClosed.aux_ctor_names {ves : VEnvs}
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ()) :
    ∀ t ∈ res.types.drop types.length, ∀ c ∈ t.ctors,
      ∃ (J : Name) (info : InductiveVal), env.find? J = some (.inductInfo info) ∧
        ∃ cJ ∈ info.ctors, c.name = cJ.replacePrefix J t.name := by
  intro t ht c hc
  obtain ⟨finalState, Hrun, ⟨O⟩⟩ := H.auxFamily wf hsources ht
  have G := O.generated
  have hnames := O.lowered.constructors.names
  have hcName : c.name ∈ O.source.ctors.map (·.name) := by
    rw [← hnames]; exact List.mem_map_of_mem hc
  obtain ⟨d, hd, hdName⟩ := List.mem_map.mp hcName
  rw [O.generated.family_eq] at hd
  obtain ⟨s, hs, hsName⟩ := O.generated.built.constructors.mem_name d hd
  refine ⟨_, _, O.generated.built.lookup, s, hs, ?_⟩
  rw [← hdName, hsName, O.name_eq]

theorem NestedLoweringOutputClosed.nested_app {ves : VEnvs}
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ()) :
    ∀ n nested, res.aux2nested.find? n = some nested →
      ∃ (I : Name) (ls : List Level) (info : InductiveVal) (args : Array Expr),
        nested = mkAppN (.const I ls) args ∧ env.find? I = some (.inductInfo info) ∧
        args.size = info.numParams ∧
        nested.FVarsIn (fun fv => Expr.fvar fv ∈ res.params.toList) := by
  intro n nested hfind
  have Hlctx := H.lctx_params.1
  have HisFVar := H.lctx_params.2
  obtain ⟨finalState, Hrun, Hcache, -⟩ := H
  obtain ⟨C⟩ := Hrun.cachedAuxiliaryFamilyOfLookup (VEnvs.WF.environmentTypesClosed wf)
    wf.inductivesClosed (checkInductiveSources_refines env types _ hsources) rfl (by rfl) hfind
  have G := C.origin.generated
  have hentry := Hrun.resolvedCacheEntryOfResultLookup hfind
  obtain ⟨args', hsize, heq⟩ := Expr.closure_mkAppRange_const C.origin.generated.sourceName
    C.origin.generated.levels C.origin.generated.nestedNParams C.origin.generated.args
    C.origin.generated.argsArity C.origin.generated.selection.fvars res.params
  refine ⟨C.origin.generated.sourceName, C.origin.generated.levels, _, args', ?_,
    C.origin.generated.built.lookup,
    hsize.trans C.origin.generated.sourceNumParams, ?_⟩
  · refine C.nested_eq.symm.trans ?_
    rw [C.origin.generated.built.nested, C.origin.generated.selection.expressions]
    exact heq
  · refine (Hcache nested n hentry).mono fun fv hfv => ?_
    rw [← Hlctx] at hfv
    simp only [List.mem_map, List.mem_reverse] at hfv
    obtain ⟨p, hp, rfl⟩ := hfv
    have hpf := HisFVar p hp
    have hp' : Expr.fvar p.fvarId! = p := by
      cases p <;> simp_all [Expr.isFVar, Expr.fvarId!]
    rw [hp']
    exact hp

end

end VerifyInductive
end Lean4Lean
