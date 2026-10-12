import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyBase
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredLookups
import Lean4Lean.Verify.Inductive.Nested.Restoration.Lookups
import Lean4Lean.Verify.Inductive.Constructor.Install
import Lean4Lean.Verify.Inductive.Nested.Restoration.Lookups
import Lean4Lean.Verify.Inductive.Nested.Install.DependencyOrder

/-! # The types and kernel half of the nested assembly

The restored headers and constructors of a nested run (`NestedRestorationFolds.ivals`)
translate to the source declaration's families (`NestedRun.trTypes`), and every restored
constant carries the declaration's safety flag (`NestedRun.newUnsafe`).

The restoration folds are read off the lowered run: a restored header is the lowered header
with its mutual-family list replaced, a restored constructor is the lowered constructor with its
type restored (`restoredCtor`). The headers' translation is the lowered header's
(`HeaderRestorationStep.translated`), the constructors' translations are those of the restored
block (`RestoredBlockBase.sourceTranslations`), and their arity is the lowered constructors',
which the expansion keeps (`NestedExpansionData.constructorArityPrefix`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
  {auxRec : NameMap Name} {allIndNames : List Name}

/-- A restored constructor: the lowered constructor with its type restored. -/
def restoredCtor (result : Lean4Lean.ElimNestedInductive.Result) (loweredEnv : Environment)
    (cv : ConstructorVal) : ConstructorVal :=
  { cv with type := result.restoreNested loweredEnv cv.type }

theorem RestoredConstructorStep.newInfo_eq_of_lookup {n : Name} {s t : Environment}
    (H : RestoredConstructorStep result loweredEnv n s t) {cv : ConstructorVal}
    (h : loweredEnv.find? n = some (.ctorInfo cv)) :
    H.restored.newInfo = restoredCtor result loweredEnv cv := by
  have : H.oldInfo = cv := ConstantInfo.ctorInfo.inj (Option.some.inj (H.lookup.symm.trans h))
  rw [H.restored.newInfo_eq, this]; rfl

/-- A restored constructor fold over lowered constructors restores exactly those. -/
theorem FoldSteps.ctorInfos_eq {names : List Name} {s t : Environment}
    (F : FoldSteps (RestoredConstructorStep result loweredEnv) names s t) :
    ∀ {cvs : List ConstructorVal}, names = cvs.map (·.name) →
      (∀ cv ∈ cvs, loweredEnv.find? cv.name = some (.ctorInfo cv)) →
      F.ctorInfos = cvs.map (restoredCtor result loweredEnv) := by
  induction F with
  | nil => intro cvs h _; cases cvs with | nil => rfl | cons => simp at h
  | cons Hstep Htail ih =>
    intro cvs h hlook
    cases cvs with
    | nil => simp at h
    | cons cv cvs =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [FoldSteps.ctorInfos, List.map_cons]
      rw [Hstep.newInfo_eq_of_lookup (hlook cv List.mem_cons_self),
        ih h (fun c hc => hlook c (List.mem_cons_of_mem _ hc))]

/-- The constructor translations of a restored family, read along its constructor fold. -/
theorem RestoredConstructorTranslations.ctorInfos {lparams : List Name}
    {safety : DefinitionSafety} {canonicalEnv : VEnv} {names : List Name}
    {s t : Environment} {sources : List Constructor} {constructors : List VConstVal}
    (H : RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv names
      s t sources constructors) :
    ∀ {s' t' : Environment} (F : FoldSteps (RestoredConstructorStep result loweredEnv) names s' t'),
      List.Forall₂ (fun cval c => TrConstVal safety canonicalEnv (.ctorInfo cval) c)
        F.ctorInfos constructors := by
  induction H with
  | nil => intro s' t' F; cases F; exact .nil
  | cons Hstep Hsemantic Hrest ih =>
    intro s' t' F
    cases F with
    | cons Hstep' Ftail =>
      refine .cons ?_ (ih Ftail)
      have h1 := Hstep.newInfo_eq_of_lookup Hstep.lookup
      have h2 := Hstep'.newInfo_eq_of_lookup Hstep.lookup
      have := Hsemantic.restoredTranslation
      rw [h1] at this
      rw [h2]; exact this

/-- **The restored families translate to the source families**, along the source translations
of a restored block: headers from the lowered headers, constructors from the block's
constructor translations, constructor arities from the lowered constructors. -/
theorem SourceFamilyTranslations.trIndTypes {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {types : List InductiveType} {s t : Environment}
    {F : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types s t}
    {owners : List VInductiveType} {recs : List VConstVal}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv envTypes envCtors F owners
      recs) :
    ∀ {ivs : List (InductiveVal × List ConstructorVal)} {lowereds : List VInductiveType}
      {envL : VEnv},
      List.Forall₂ (fun iv l => TrIndType safety sourceVEnv envL iv.1 iv.2 l) ivs lowereds →
      owners.map VInductiveType.toVConstVal = lowereds.map VInductiveType.toVConstVal →
      List.Forall₂ (fun (o l : VInductiveType) => ∀ j (h₁ : j < o.ctors.length)
        (h₂ : j < l.ctors.length), o.ctors[j].type.piArity = l.ctors[j].type.piArity)
        owners lowereds →
      (∀ iv ∈ ivs, loweredEnv.find? iv.1.name = some (.inductInfo iv.1) ∧
        ∀ cv ∈ iv.2, loweredEnv.find? cv.name = some (.ctorInfo cv)) →
      List.Forall₂ (fun iv o => TrIndType safety sourceVEnv envTypes iv.1 iv.2 o)
        F.inductiveInfos owners := by
  induction H with
  | nil => intro ivs lowereds envL h1 h2; cases lowereds with
    | nil => cases h1; intros; exact .nil
    | cons => simp at h2
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    intro ivs lowereds envL h1 h2 h3 hlook
    cases h1 with
    | nil => simp at h2
    | @cons iv l ivs' ls h1h h1t =>
    cases h3 with
    | cons h3h h3t =>
    simp only [List.map_cons, List.cons.injEq] at h2
    have hname := Hheader.name.symm.trans ((congrArg VConstVal.name h2.1).trans h1h.tr.2.symm)
    obtain ⟨hivLook, hcvLook⟩ := hlook iv List.mem_cons_self
    have holdInfo : Hstep.oldInfo = iv.1 := ConstantInfo.inductInfo.inj
      (Option.some.inj (Hstep.lookup.symm.trans (hname ▸ hivLook)))
    have hctorNames : Hstep.oldInfo.ctors = iv.2.map (·.name) := by
      rw [holdInfo]; exact h1h.ctor_names
    have hctorInfos := Hstep.restored.constructors.ctorInfos_eq hctorNames hcvLook
    have Htr := Hconstructors.ctorInfos Hstep.restored.constructors
    rw [hctorInfos] at Htr
    refine .cons ?_ (ih h1t h2.2 h3t (fun iv hiv => hlook iv (List.mem_cons_of_mem _ hiv)))
    dsimp only
    rw [hctorInfos]
    have hlenO := (Lean4Lean.List.Forall₂.length_eq Htr).symm
    simp only [List.length_map] at hlenO
    have hlenL : iv.2.length = l.ctors.length := Lean4Lean.List.Forall₂.length_eq h1h.ctors
    refine ⟨?_, ?_, ?_⟩
    · apply Hstep.restored.header.translated
      rw [holdInfo, h2.1]; exact h1h.tr
    · rw [Hstep.restored.header.restored, holdInfo, h1h.ctor_names, List.map_map]; rfl
    · refine List.forall₂_of_getElem (by simpa using hlenO.symm) fun j hj hj' => ⟨?_, ?_⟩
      · exact List.forall₂_getElem Htr j hj hj'
      · have hjl : j < l.ctors.length := by rw [← hlenL]; simpa using hj
        have hjv : j < iv.2.length := by simpa using hj
        have harity := (List.forall₂_getElem h1h.ctors j hjv hjl).2
        simp only [List.getElem_map, restoredCtor]
        rw [harity, h3h j hj' hjl]

/-- The lowered headers with their constructors are the lowered environment's. -/
theorem NestedRun.ivals_lookup
    {res : Lean4Lean.ElimNestedInductive.Result} {sourceProdEnv : Environment}
    {sourceTypes : List InductiveType} {venv : VEnv} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes venv decl lparams nparams isUnsafe safety
      outEnv L) :
    ∀ iv ∈ E.lowered.constructors.ivals,
      E.loweredEnv.find? iv.1.name = some (.inductInfo iv.1) ∧
      ∀ cv ∈ iv.2, E.loweredEnv.find? cv.name = some (.ctorInfo cv) := by
  intro iv hiv
  refine ⟨E.lowered.recursors.findHeaderOfMem ?_, fun cv hcv =>
    E.lowered.recursors.findConstructorOfMem hiv hcv⟩
  have hiv' := hiv
  rw [E.lowered.constructors.ivals_eq] at hiv'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hiv'
  exact (List.of_mem_zip hp).1

/-- **The restored families translate to the source declaration's families**, with their
constructors in the source header environment. -/
theorem NestedRun.trTypes
    {res : Lean4Lean.ElimNestedInductive.Result} {sourceProdEnv : Environment}
    {sourceTypes : List InductiveType} {venv : VEnv} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes venv decl lparams nparams isUnsafe safety
      outEnv L)
    (B : RestoredBlockBase E.restoration venv decl lparams nparams isUnsafe safety)
    (hB : B.loweredDecl = E.lowered.loweredDecl) :
    List.Forall₂ (fun iv t => TrIndType safety venv E.sourceCore.envTypes iv.1 iv.2 t)
      E.restoration.ivals decl.types := by
  let n := sourceTypes.length
  have hsourceDecl := E.sourceCoreDecl_eq
  have hvalues := E.sourceCore.sourceTypeValues
  rw [hsourceDecl] at hvalues
  have hcore := E.sourceCore.core
  rw [hsourceDecl] at hcore
  have hn : n = decl.types.length := TrInductDeclCore.types_length hcore
  -- the lowered headers, in the source environment
  have h1 : List.Forall₂ (fun iv l => TrIndType safety venv
      E.lowered.constructors.headers.context.venv iv.1 iv.2 l)
      (E.lowered.constructors.ivals.take n) (E.lowered.loweredDecl.types.take n) := by
    have h := List.forall₂_take E.lowered.constructors.trTypes n
    have hs : E.lowered.c.safety = safety := by rw [E.lowered_c, E.context_safety]
    have hi : E.lowered.Hc'.venv = venv := E.lowered_initialEnv
    generalize E.lowered.constructors.headers.context.venv = envL at h ⊢
    generalize E.lowered.constructors.ivals.take n = ivs at h ⊢
    generalize E.lowered.loweredDecl.types.take n = ls at h ⊢
    rw [hs, hi] at h
    exact h
  have h2 : decl.types.map VInductiveType.toVConstVal =
      (E.lowered.loweredDecl.types.take n).map VInductiveType.toVConstVal := by
    rw [← hvalues]; rfl
  have hlen : (E.lowered.loweredDecl.types.take n).length = decl.types.length := by
    simpa using (congrArg List.length h2).symm
  have h3 : List.Forall₂ (fun (o l : VInductiveType) => ∀ j (h₁ : j < o.ctors.length)
      (h₂ : j < l.ctors.length), o.ctors[j].type.piArity = l.ctors[j].type.piArity)
      decl.types (E.lowered.loweredDecl.types.take n) := by
    have Harity := B.formationAssembly.constructorArityPrefix
    rw [B.formationExpanded, hB] at Harity
    refine List.forall₂_of_getElem hlen.symm fun i hi hi' j hj hj' => ?_
    have hiL : i < E.lowered.loweredDecl.types.length :=
      by have := hi'; simp only [List.length_take] at this; omega
    have hget : (E.lowered.loweredDecl.types.take n)[i] = E.lowered.loweredDecl.types[i] :=
      List.getElem_take ..
    rw [VExpr.piArity_eq_forallArity, VExpr.piArity_eq_forallArity]
    have hj'' : j < E.lowered.loweredDecl.types[i].ctors.length := by rw [← hget]; exact hj'
    have := Harity i hi hiL j hj hj''
    rw [this]
    simp only [List.getElem_take]
  have h4 : ∀ iv ∈ E.lowered.constructors.ivals.take n,
      E.loweredEnv.find? iv.1.name = some (.inductInfo iv.1) ∧
      ∀ cv ∈ iv.2, E.loweredEnv.find? cv.name = some (.ctorInfo cv) :=
    fun iv hiv => E.ivals_lookup iv (List.mem_of_mem_take hiv)
  have H := B.sourceTranslations
  rw [← B.typesSource] at H
  have hres := H.trIndTypes h1 h2 h3 h4
  have htypes : B.install.venvTypes = E.sourceCore.envTypes := by
    have h₁ := B.typesAdded
    have h₂ := hcore.typesAdded
    exact Option.some.inj (h₁.symm.trans h₂)
  rw [htypes] at hres
  exact hres

/-! ### Safety flags of the restored constants -/

/-- A restored recursor fold whose steps restore recursors of flag `b` restores only such. -/
theorem FoldSteps.recursorInfos_isUnsafe {names : List Name} {s t : Environment}
    (F : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names s t)
    {b : Bool}
    (h : ∀ n ∈ names, ∀ {s t : Environment}
      (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
      Hs.restored.newInfo.isUnsafe = b) :
    ∀ r ∈ F.recursorInfos, r.isUnsafe = b := by
  induction F with
  | nil => simp [FoldSteps.recursorInfos]
  | cons Hstep Htail ih =>
    intro r hr
    simp only [FoldSteps.recursorInfos, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h _ List.mem_cons_self Hstep
    · exact ih (fun n hn _ _ Hs => h n (List.mem_cons_of_mem _ hn) Hs) r hr

/-- The restored headers, constructors and recursors of a family fold carry the flag `b` when
the lowered ones do. -/
theorem FoldSteps.inductive_isUnsafe {types : List InductiveType} {s t : Environment}
    (F : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types s t)
    {b : Bool}
    (hfam : ∀ indType ∈ types, ∃ iv : InductiveVal × List ConstructorVal,
      loweredEnv.find? indType.name = some (.inductInfo iv.1) ∧
      iv.1.ctors = iv.2.map (·.name) ∧
      (∀ cv ∈ iv.2, loweredEnv.find? cv.name = some (.ctorInfo cv)) ∧
      iv.1.isUnsafe = b ∧ ∀ cv ∈ iv.2, cv.isUnsafe = b)
    (hrec : ∀ indType ∈ types, ∀ {s t : Environment}
      (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames
        (Lean.mkRecName indType.name) s t),
      Hs.restored.newInfo.isUnsafe = b) :
    (∀ iv ∈ F.inductiveInfos, iv.1.isUnsafe = b ∧ ∀ cv ∈ iv.2, cv.isUnsafe = b) ∧
      ∀ r ∈ F.inductiveRecs, r.isUnsafe = b := by
  induction F with
  | nil => simp [FoldSteps.inductiveInfos, FoldSteps.inductiveRecs]
  | @cons indType _ _ _ _ Hstep Htail ih =>
    obtain ⟨ihI, ihR⟩ := ih (fun i hi => hfam i (List.mem_cons_of_mem _ hi))
      (fun i hi _ _ Hs => hrec i (List.mem_cons_of_mem _ hi) Hs)
    obtain ⟨iv, hlook, hctors, hcvLook, hivU, hcvU⟩ := hfam indType List.mem_cons_self
    have holdInfo : Hstep.oldInfo = iv.1 :=
      ConstantInfo.inductInfo.inj (Option.some.inj (Hstep.lookup.symm.trans hlook))
    refine ⟨fun x hx => ?_, fun r hr => ?_⟩
    · simp only [FoldSteps.inductiveInfos, List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨?_, ?_⟩
        · show Hstep.restored.header.newInfo.isUnsafe = b
          rw [Hstep.restored.header.restored]
          show Hstep.oldInfo.isUnsafe = b
          rw [holdInfo]; exact hivU
        · rw [Hstep.restored.constructors.ctorInfos_eq (by rw [holdInfo]; exact hctors)
            hcvLook]
          intro cv hcv
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcv
          exact hcvU c hc
      · exact ihI x hx
    · simp only [FoldSteps.inductiveRecs, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hrec indType List.mem_cons_self Hstep.restored.recursor
      · exact ihR r hr

/-- A restored recursor of a generated recursor carries the lowered declaration's flag. -/
theorem RestoredRecursorStep.isUnsafe_of_generated
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceVEnv indTypes ctorEnv}
    (Hprod : RecursorInstallation R loweredEnv) {oldRecName : Name} {s t : Environment}
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s t)
    (hgenerated : oldRecName ∈ (Hprod.entries.map Prod.snd).map (·.name)) :
    Hstep.restored.newInfo.isUnsafe = isUnsafe := by
  rcases List.mem_map.mp hgenerated with ⟨value, hvalue, hvalueName⟩
  rcases AddConstants.existsEntryOfValue hvalue with ⟨info, hentry⟩
  have hlookup := Hprod.findRecursorOfMem hentry
  have hentryName := Hprod.installed.entryNames hentry
  have holdInfo : info = .recInfo Hstep.oldInfo := by
    have hlookup' : loweredEnv.find? info.name = some (.recInfo Hstep.oldInfo) := by
      rw [hentryName, hvalueName]
      exact Hstep.lookup
    exact Option.some.inj (hlookup.symm.trans hlookup')
  rcases List.mem_iff_getElem.mp hentry with ⟨i, hi, hentryEq⟩
  have hsource : Hprod.entries[i].1 = .recInfo (Hprod.generated.entry i hi).info :=
    (Hprod.generated.entry i hi).source_eq
  have hinfo : Hstep.oldInfo = (Hprod.generated.entry i hi).info := by
    have : info = .recInfo (Hprod.generated.entry i hi).info :=
      (congrArg Prod.fst hentryEq).symm.trans hsource
    rw [holdInfo] at this
    exact ConstantInfo.recInfo.inj this
  rw [Hstep.restored.restoration.isUnsafe, hinfo, Hprod.generated_isUnsafe, R.core.isUnsafe]

/-- **Every restored constant carries the declaration's safety flag.** -/
theorem NestedRun.newUnsafe
    {res : Lean4Lean.ElimNestedInductive.Result} {sourceProdEnv : Environment}
    {sourceTypes : List InductiveType} {venv : VEnv} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes venv decl lparams nparams isUnsafe safety
      outEnv L) :
    ∀ ci ∈ AddInduct.consts E.restoration.ivals E.restoration.rvals, ci.isUnsafe = isUnsafe := by
  have Hlower := E.loweringAtContext
  have hempty : E.initialState.nestedAux = #[] := rfl
  have hne : sourceTypes ≠ [] := Hlower.toResult.sourceNonempty
  let R := E.lowered.constructors
  let Hprod := E.lowered.recursors
  have hRU : E.lowered.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF E.lowered.c := E.loweredContextWF
  -- the source families are lowered families
  have hsrc : ∀ indType ∈ sourceTypes, ∃ j, ∃ hj : j < res.types.toArray.size,
      res.types.toArray[j].name = indType.name := by
    intro indType hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
    rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hj with
      ⟨_, _, target, _, _, _, _, Hmapping, htarget⟩
    obtain ⟨hres, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
    exact ⟨j, by simpa using hres, by simpa [htargetEq] using Hmapping.name⟩
  have hrecords : Hprod.recInfos.size = res.types.toArray.size := by
    rw [Hprod.cardinality.records, ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
      R.core]
    simp
  have hfam : ∀ indType ∈ sourceTypes, ∃ iv : InductiveVal × List ConstructorVal,
      E.loweredEnv.find? indType.name = some (.inductInfo iv.1) ∧
      iv.1.ctors = iv.2.map (·.name) ∧
      (∀ cv ∈ iv.2, E.loweredEnv.find? cv.name = some (.ctorInfo cv)) ∧
      iv.1.isUnsafe = isUnsafe ∧ ∀ cv ∈ iv.2, cv.isUnsafe = isUnsafe := by
    intro indType hmem
    obtain ⟨j, hj, hname⟩ := hsrc indType hmem
    have hmemT : res.types.toArray[j] ∈ res.types.toArray.toList := by simp
    obtain ⟨iv, hiv, hinfo, hivName, hivCtors, -, -, hivU, hiv2⟩ := R.family_of_mem hmemT
    refine ⟨iv, ?_, ?_, fun cv hcv => Hprod.findConstructorOfMem hiv hcv, ?_,
      fun cv hcv => (R.ctor_isUnsafe hiv hcv).trans hRU⟩
    · rw [← hname, ← hivName]; exact Hprod.findHeaderOfMem hinfo
    · rw [hivCtors, hiv2, familyCtorInfos, ctorInfosFrom_names]
    · exact hivU.trans hRU
  have hrec : ∀ indType ∈ sourceTypes, ∀ {s t : Environment}
      (Hs : RestoredRecursorStep res E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) (Lean.mkRecName indType.name) s t),
      Hs.restored.newInfo.isUnsafe = isUnsafe := by
    intro indType hmem s t Hs
    obtain ⟨j, hj, hname⟩ := hsrc indType hmem
    have hgen := Hprod.generated.recursorName_mem hrecords j hj
    rw [getElem!_pos res.types.toArray j hj, hname] at hgen
    exact (Hs.isUnsafe_of_generated Hprod hgen).trans hRU
  obtain ⟨main, rest, rfl⟩ : ∃ main rest, sourceTypes = main :: rest := by
    cases sourceTypes with
    | nil => exact absurd rfl hne
    | cons main rest => exact ⟨main, rest, rfl⟩
  have haux : ∀ n ∈ (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).1,
      ∀ {s t : Environment}
      (Hs : RestoredRecursorStep res E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv (main :: rest)).2
        ((main :: rest).map (·.name)) n s t),
      Hs.restored.newInfo.isUnsafe = isUnsafe := by
    intro n hn s t Hs
    have hgen := Hlower.auxRecNameGeneratedAtFresh HcP Hprod hempty hn
    exact (Hs.isUnsafe_of_generated Hprod hgen).trans hRU
  obtain ⟨hI, hR⟩ := E.restoration.inductives.inductive_isUnsafe hfam hrec
  have hA := E.restoration.auxiliaries.recursorInfos_isUnsafe haux
  intro ci hci
  simp only [AddInduct.consts, List.mem_append, List.mem_map, List.mem_flatMap] at hci
  rcases hci with ((⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cv, hcv, rfl⟩) | ⟨r, hr, rfl⟩)
  · exact (hI iv hiv).1
  · exact (hI iv hiv).2 cv hcv
  · rcases hr with hr | hr
    · exact hR r hr
    · exact hA r hr

end VerifyInductive
end Lean4Lean
