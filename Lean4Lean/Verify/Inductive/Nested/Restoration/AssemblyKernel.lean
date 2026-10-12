import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyTypes
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorAlignment
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorCoherence
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ParameterScopes
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledFamilyLookups

/-! # The kernel half of the nested assembly

The kernel facts of a validated nested run, over `E : NestedRun`, its rule-free block
`B : RestoredBlockBase E.restoration …` and `hB : B.loweredDecl = E.lowered.loweredDecl`: the kernel family
lookups (`NestedRun.inductInfosFromDecl`), the cover of the declaration's families
(`NestedRun.cover`), the constructor owners (`NestedRun.constructorOwnersPresent`), the major
inductives of the restored recursors (`NestedRun.recMajor`) and the constructor parameter
alignment (`NestedRun.constructorParameterAlignment`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
  {auxRec : NameMap Name} {allIndNames : List Name}

/-! ### The restored recursors are those of the steps -/

theorem FoldSteps.recursorInfos_mem {names : List Name} {s t : Environment}
    (F : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names s t)
    {r : RecursorVal} (hr : r ∈ F.recursorInfos) :
    ∃ n ∈ names, ∃ (s' t' : Environment)
      (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s' t'),
      r = Hs.restored.newInfo := by
  induction F with
  | nil => simp [FoldSteps.recursorInfos] at hr
  | cons Hstep Htail ih =>
    simp only [FoldSteps.recursorInfos, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨_, List.mem_cons_self, _, _, Hstep, rfl⟩
    · obtain ⟨n, hn, s', t', Hs, h⟩ := ih hr
      exact ⟨n, List.mem_cons_of_mem _ hn, s', t', Hs, h⟩

theorem FoldSteps.inductiveRecs_mem {types : List InductiveType} {s t : Environment}
    (F : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types s t)
    {r : RecursorVal} (hr : r ∈ F.inductiveRecs) :
    ∃ indType ∈ types, ∃ (s' t' : Environment)
      (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames
        (Lean.mkRecName indType.name) s' t'),
      r = Hs.restored.newInfo := by
  induction F with
  | nil => simp [FoldSteps.inductiveRecs] at hr
  | cons Hstep Htail ih =>
    simp only [FoldSteps.inductiveRecs, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨_, List.mem_cons_self, _, _, Hstep.restored.recursor, rfl⟩
    · obtain ⟨i, hi, s', t', Hs, h⟩ := ih hr
      exact ⟨i, List.mem_cons_of_mem _ hi, s', t', Hs, h⟩

/-- Every generated recursor name is the canonical recursor name of an owner. -/
theorem NestedRun.recursorOwnerOfName
    {res : Lean4Lean.ElimNestedInductive.Result} {sourceProdEnv : Environment}
    {sourceTypes : List InductiveType} {venv : VEnv} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes venv decl lparams nparams isUnsafe safety
      outEnv L)
    {n : Name} (hn : n ∈ (E.lowered.recursors.entries.map Prod.snd).map (·.name)) :
    ∃ owner : Fin E.lowered.recursors.generationSignature.families.size,
      E.lowered.recursors.canonicalGeneration.recursorName owner = n := by
  obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hn
  obtain ⟨info, hentry⟩ := AddConstants.existsEntryOfValue hvalue
  obtain ⟨i, hi, hentryEq⟩ := List.mem_iff_getElem.mp hentry
  obtain ⟨owner, -, howner⟩ := E.recursorOwnerOfEntry hi
  refine ⟨owner, ?_⟩
  rw [← howner]
  let G := E.lowered.recursors.generated.entry i hi
  have h1 : G.info.name = E.lowered.recursors.entries[i].2.name := G.translated.2
  rw [← G.name, h1, hentryEq]

/-! ### The kernel facts of the run -/

section

variable {res : Lean4Lean.ElimNestedInductive.Result} {sourceProdEnv : Environment}
  {sourceTypes : List InductiveType} {venv : VEnv} {decl : VInductDecl}
  {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
  {outEnv : Environment}
  {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes venv decl lparams nparams isUnsafe safety
    outEnv L)
include E

/-- The source core of the run at the lowered context's indices. -/
theorem NestedRun.sourceCoreAtLowered :
    TrInductDeclCore E.lowered.Hc'.venv E.lowered.c.lparams nparams sourceTypes
      E.lowered.isUnsafe decl E.sourceCore.envTypes E.sourceCore.envCtors := by
  have h := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at h
  rw [E.lowered_initialEnv, E.lowered_lparams, E.lowered_isUnsafe_source]
  exact h

/-- The restoration folds at the lowered context. -/
def NestedRun.restorationAtLowered :
    NestedRestorationFolds res E.loweredEnv E.lowered.c.env
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 (sourceTypes.map (·.name))
      sourceTypes (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 ((), outEnv) := by
  rw [E.lowered_env]; exact E.restoration

/-- The constructor arities of the source declaration are those of the lowered one. -/
theorem NestedRun.constructorArityPrefix
    (B : RestoredBlockBase E.restoration venv decl lparams nparams isUnsafe safety)
    (hB : B.loweredDecl = E.lowered.loweredDecl) : decl.ConstructorArityPrefix E.lowered.loweredDecl := by
  have h := B.formationAssembly.constructorArityPrefix
  rw [B.formationExpanded, hB] at h
  exact h

/-- The kernel family lookups, from the constructor arities of the lowered declaration. -/
theorem NestedRun.inductInfosFromDeclOfArity
    (Harity : decl.ConstructorArityPrefix E.lowered.loweredDecl)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv) :
    InductInfosFromDecl sourceProdEnv.constants outEnv.constants decl := by
  have h := NestedRestorationFolds.inductInfosFromDecl E.loweringAtContext E.loweredContextWF
    E.lowered.recursors E.sourceCoreAtLowered
    (by simpa only [E.sourceCoreDecl_eq] using E.sourceCore.checked) Hsources
    Harity (by rw [E.lowered_env]; exact Howners) rfl
    E.restorationAtLowered
  rwa [E.lowered_env] at h

/-- **The kernel family lookups**: every inductive header of the output is a base header or an
aligned family of the declaration. -/
theorem NestedRun.inductInfosFromDecl
    (B : RestoredBlockBase E.restoration venv decl lparams nparams isUnsafe safety)
    (hB : B.loweredDecl = E.lowered.loweredDecl) (Hsources : SourceSyntaxChecked sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv) :
    InductInfosFromDecl sourceProdEnv.constants outEnv.constants decl :=
  E.inductInfosFromDeclOfArity (E.constructorArityPrefix B hB) Hsources Howners

/-- The declaration's families are new headers of the output, from the constructor arities of
the lowered declaration. -/
theorem NestedRun.coverOfArity
    (Harity : decl.ConstructorArityPrefix E.lowered.loweredDecl)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv) :
    ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      sourceProdEnv.find? T.name = none := by
  have h := NestedRestorationFolds.cover E.loweringAtContext E.loweredContextWF
    E.lowered.recursors E.sourceCoreAtLowered
    (by simpa only [E.sourceCoreDecl_eq] using E.sourceCore.checked) Hsources
    Harity (by rw [E.lowered_env]; exact Howners) rfl
    E.restorationAtLowered
  rwa [E.lowered_env] at h

/-- **The declaration's families are new headers of the output.** -/
theorem NestedRun.cover
    (B : RestoredBlockBase E.restoration venv decl lparams nparams isUnsafe safety)
    (hB : B.loweredDecl = E.lowered.loweredDecl) (Hsources : SourceSyntaxChecked sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv) :
    ∀ T ∈ decl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      sourceProdEnv.find? T.name = none :=
  E.coverOfArity (E.constructorArityPrefix B hB) Hsources Howners

/-- **Every constructor's owner is present in the output.** -/
theorem NestedRun.constructorOwnersPresent
    (Howners : ConstructorOwnersPresent sourceProdEnv) : ConstructorOwnersPresent outEnv :=
  NestedRestorationFolds.constructorOwnersPresent E.loweringAtContext E.loweredContextWF
    E.lowered.recursors rfl E.restorationAtLowered (by rw [E.lowered_env]; exact Howners)

end

/-- **The major inductive of every restored recursor is an inductive type of the output.** -/
theorem NestedRun.recMajor
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ rval ∈ E.restoration.rvals,
      ∃ info, outEnv.find? rval.getMajorInduct = some (.inductInfo info) := by
  obtain ⟨envTypes, generated, auxiliaries, -, -, Haux, Hexpansion, hparamsSize, D, -, -⟩ :=
    E.restorationTablesRestoringAll wf Hsources
  have hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := E.containerSpecializations wf Hsources
    exact h
  have hsourceWF : sourceProdEnv.constants.WF := by
    have h := E.contextWF.checking.tr.map_wf
    rwa [E.context_env] at h
  obtain ⟨_, Hfresh⟩ := E.restoration.freshExtension hsourceWF
  have houtWF : outEnv.constants.WF := Hfresh.targetWF hsourceWF
  have Hlower := E.loweringAtContext
  have hempty : E.initialState.nestedAux = #[] := rfl
  let Hprod := E.lowered.recursors
  -- the names restored are generated recursor names
  have hgen : ∀ (n : Name) {s t : Environment}
      (Hs : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 (sourceTypes.map (·.name)) n s t),
      n ∈ (E.lowered.recursors.entries.map Prod.snd).map (·.name) →
      ∃ info, outEnv.find? Hs.restored.newInfo.getMajorInduct = some (.inductInfo info) := by
    intro n s t Hs hn
    obtain ⟨owner, howner⟩ := E.recursorOwnerOfName hn
    subst howner
    obtain ⟨info, hinfo⟩ := E.restoredMajorFound wf Hsources Haux Hexpansion hnodup hparamsSize D
      owner Hs
    exact ⟨info, by rw [Kernel.Environment.find?_eq_constants houtWF]; exact hinfo⟩
  have hentries : E.lowered.recursors.entries = E.lowered.recursors.entries :=
    rfl
  intro rval hrval
  rcases List.mem_append.mp hrval with hr | hr
  · obtain ⟨indType, hmem, s, t, Hs, rfl⟩ := E.restoration.inductives.inductiveRecs_mem hr
    refine hgen _ Hs ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
    rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hj with
      ⟨_, _, target, _, _, _, _, Hmapping, htarget⟩
    obtain ⟨hres, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
    have hj' : j < result.types.toArray.size := by simpa using hres
    have hrecords : Hprod.recInfos.size = result.types.toArray.size := by
      rw [Hprod.cardinality.records,
        ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length E.lowered.constructors.core]
      simp
    have h := Hprod.generated.recursorName_mem hrecords j hj'
    rw [hentries] at h
    have hname : result.types.toArray[j]!.name = sourceTypes[j].name := by
      rw [getElem!_pos result.types.toArray j hj']
      simpa [htargetEq] using Hmapping.name
    rwa [hname] at h
  · obtain ⟨n, hn, s, t, Hs, rfl⟩ := E.restoration.auxiliaries.recursorInfos_mem hr
    refine hgen _ Hs ?_
    have hne : sourceTypes ≠ [] := Hlower.toResult.sourceNonempty
    obtain ⟨main, rest, hsplit⟩ : ∃ main rest, sourceTypes = main :: rest := by
      cases sourceTypes with
      | nil => exact absurd rfl hne
      | cons main rest => exact ⟨main, rest, rfl⟩
    clear hgen hnodup Haux Hexpansion D hparamsSize
    subst hsplit
    have h := Hlower.auxRecNameGeneratedAtFresh E.loweredContextWF Hprod hempty hn
    rwa [hentries] at h

/-- **The constructor parameter alignment of the output**, at any extension of the restored
block's recursor stage. -/
theorem NestedRun.constructorParameterAlignment
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {decl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes (ves.venv safety) decl lparams
      nparams isUnsafe safety outEnv L)
    (B : RestoredBlockBase E.restoration (ves.venv safety) decl lparams nparams isUnsafe safety)
    (hB : B.loweredDecl = E.lowered.loweredDecl)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {installedVEnv : VEnv} (hinstalled : B.recursorVEnv ≤ installedVEnv) :
    ConstructorParameterAlignment safety outEnv installedVEnv := by
  let I : NestedInstalledRun result sourceProdEnv sourceTypes (ves.venv safety) decl lparams
      nparams isUnsafe safety outEnv L := { toNestedRun := E, assembly := B, lowered_eq := hB }
  have Hlower : NestedLoweringOutputClosed I.context.env E.validationFuel.inductiveFuel nparams
      sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } : Lean4Lean.ElimNestedInductive.State)
        with newTypes := sourceTypes.toArray } result := by
    show NestedLoweringOutputClosed E.context.env _ _ _ _ _
    rw [E.context_env]; exact E.lowering
  have Hscopes := I.restoredFamilyParameterScopes Hlower rfl
  have Hparams : NestedConstructorParameterDomainsDefEq B :=
    I.constructorParameterDomainsDefEqOfSource Hscopes
  exact B.constructorTypingOfParameterDomains wf
    (E.inductInfosFromDecl B hB Hsources wf.constructorOwners) Hparams hinstalled

end VerifyInductive
end Lean4Lean
