import Lean4Lean.Verify.Inductive.Install.Ordinary
import Lean4Lean.Verify.Inductive.Prelude.EqReady
import Lean4Lean.Verify.Inductive.Install.Result
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations

/-! The ordinary path of section 3.1 of the design notes: a successful
ordinary run extends the safety-indexed environment model, and a lowering
result without auxiliary families leaves the source declaration literally
unchanged, so the ordinary branch of `addInductiveAfterLowering` yields an
`InductiveExtension` for the submitted declaration. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

private theorem inductiveTypeInfo_isUnsafe
    (hinfo : info ∈ (AddInductive.inductiveTypeInfos stats nparams
      indTypes numNested isUnsafe lparams).toList) :
    info.isUnsafe = isUnsafe := by
  simp only [AddInductive.inductiveTypeInfos, Array.toList_zipWith,
    Array.toList_map] at hinfo
  apply List.property_of_mem_zipWith
    (f := fun (indType : InductiveType) (numIndices : Nat) =>
      show InductiveVal from {
        name := indType.name
        levelParams := lparams
        type := indType.type
        numParams := nparams
        numIndices := numIndices
        all := indTypes.toList.map (fun x => x.name)
        ctors := indType.ctors.map (fun x => x.name)
        numNested := numNested
        isRec := AddInductive.isRec indTypes stats.indConsts
        isUnsafe := isUnsafe
        isReflexive := AddInductive.isReflexive indTypes stats.indConsts })
    (P := fun candidate => candidate.isUnsafe = isUnsafe)
    (by intros; rfl) hinfo

private theorem InductiveHeaderEntries.entrySafety_eq_unsafe
    (H : InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe lparams).toList entries)
    (hunsafe : isUnsafe = true) (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  rcases H.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
  rw [hentryInfo]
  have hinfoUnsafe := inductiveTypeInfo_isUnsafe hinfo
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hinfoUnsafe, hunsafe]

private theorem ConstructorListEntries.entrySafety_eq_unsafe
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      start ctors entries)
    (hunsafe : isUnsafe = true) (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  induction H with
  | nil => simp at hentry
  | cons Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · simp [AddInductive.constructorInfo, ConstantInfo.safety,
        ConstantInfo.isUnsafe, hunsafe]
    · exact ih htail

private theorem ConstructorTypeEntries.entrySafety_eq_unsafe
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (hunsafe : isUnsafe = true) (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  induction H with
  | nil => simp at hentry
  | cons Hhead Htail ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · exact Hhead.entrySafety_eq_unsafe hunsafe hhead
    · exact ih htail

private theorem GeneratedRecursors.entrySafety_eq_unsafe
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (hsafety : c.safety = .unsafe)
    {entry : ConstantInfo × VConstVal} (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  rcases List.mem_iff_getElem.mp hentry with ⟨i, hi, heq⟩
  have hi' : i < entries.length := by simpa using hi
  let E := H.entry i hi'
  have hsource : entries[i].1 = .recInfo E.info := E.source_eq
  have hinfoUnsafe : E.info.isUnsafe = true := by
    exact E.isUnsafe.trans (by rw [hsafety]; decide)
  rw [← heq, hsource]
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hinfoUnsafe]

/-- A successful safe ordinary run extends the complete safety-indexed model.
The result depends only on the successful run and the source environment
model; whether the prelude `Eq` is present is irrelevant to inductive soundness. -/
theorem OrdinaryInstallation.extendSafeExact
    {ves : VEnvs}
    (Hrun : OrdinaryInstallation c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ∃ decl : VInductDecl, ∃ envTypes envCtors : VEnv,
      ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      TrInductDeclCore (ves.venv .safe) c.lparams nparams indTypes.toList
        isUnsafe decl envTypes envCtors ∧
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.generatedRuleTranslation with ⟨T⟩
  let B0 := Hrecursors.blockCertificate T.rules T.rulesWF
  let B := B0.sf_mono (safety := .safe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) B.block :=
    by simpa [B, B0, BlockCertificate.sf_mono, BlockInstallation.sf_mono,
      BlockCertificate.block] using
      (show OrdinaryCompilationCertificate _ decl B0.block from
        T.compilation hnonempty).compilesTo
  have hconstructors :
      ConstructorParameterAlignment .safe outEnv
        (Hrecursors.outVEnv.addDefEqRules T.rules) := by
    exact Hrecursors.constructorTyping
      (wf.constructorParameterAlignment (safety := .safe)) T.rules
  have horigins :
      InductInfosFromDecl c.env.constants outEnv.constants decl :=
    Hrecursors.inductInfosFromDecl
  have howners : ConstructorOwnersPresent outEnv :=
    Hrecursors.constructorOwnersPresent wf.constructorOwners
  have htypes : (ves.venv .safe).addConstVals (Hheaders.entries.map Prod.snd) =
      some Hheaders.context.venv := by
    rw [Hheaders.values]; exact Hheaders.translation.typesAdded
  rcases B.extendSafeExact wf hdecl hcompile horigins T.newRecursorsAligned
      Hrecursors.closed howners hconstructors
      (fun safety => Hrecursors.blockEliminatorsReplay T.rules T.rulesWF
        (wf.mono (DefinitionSafety.le_safe (a := safety))))
      Hrecursors.cover (fun hfind => Hrecursors.ctorOrigin hfind) (B.typesLe htypes) with
    ⟨ves', wf', hle, hadd, -⟩
  exact ⟨ves', decl, Hheaders.context.venv, R.declared.venvCtors,
    wf', hle, R.core, hadd⟩

/-- A successful unsafe ordinary run extends the unsafe model and is hidden
from the partial and safe observers. Uniform entry safety is obtained from
the block installation rather than assumed separately. -/
theorem OrdinaryInstallation.extendUnsafeExact
    {ves : VEnvs}
    (Hrun : OrdinaryInstallation c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .unsafe)
    (hsource : sourceEnv = ves.venv .unsafe)
    (hproduction : isUnsafe = (c.safety != .safe))
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ∃ decl : VInductDecl, ∃ envTypes envCtors : VEnv,
      ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      TrInductDeclCore (ves.venv .unsafe) c.lparams nparams indTypes.toList
        isUnsafe decl envTypes envCtors ∧
      VEnv.AddInduct (ves.venv .unsafe) decl (ves'.venv .unsafe) := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.generatedRuleTranslation with ⟨T⟩
  let B0 := Hrecursors.blockCertificate T.rules T.rulesWF
  let B := B0.sf_mono (safety := .unsafe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .unsafe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .unsafe) B.block :=
    by simpa [B, B0, BlockCertificate.sf_mono, BlockInstallation.sf_mono,
      BlockCertificate.block] using
      (show OrdinaryCompilationCertificate _ decl B0.block from
        T.compilation hnonempty).compilesTo
  have hisUnsafe : isUnsafe = true := by
    exact hproduction.trans (by rw [hsafety]; decide)
  have hconstructors :
      ConstructorParameterAlignment .unsafe outEnv
        (Hrecursors.outVEnv.addDefEqRules T.rules) := by
    exact Hrecursors.constructorTyping
      (wf.constructorParameterAlignment (safety := .unsafe)) T.rules
  have horigins :
      InductInfosFromDecl c.env.constants outEnv.constants decl :=
    Hrecursors.inductInfosFromDecl
  have howners : ConstructorOwnersPresent outEnv :=
    Hrecursors.constructorOwnersPresent wf.constructorOwners
  have hentries : ∀ entry ∈
      Hheaders.entries ++ R.declared.entries ++ Hrecursors.entries,
      entry.1.safety = .unsafe := by
    have hlocalSafety : Hrecursors.localContext.safety = .unsafe :=
      Hrecursors.localExtends.safety_eq.trans hsafety
    intro entry hentry
    rcases List.mem_append.mp hentry with hprefix | hrecursors
    · rcases List.mem_append.mp hprefix with hheaders | hconstructors
      · rcases Hheaders.sourceAligned with ⟨numNested, Haligned⟩
        exact Haligned.entrySafety_eq_unsafe hisUnsafe hheaders
      · exact R.declared.sourceAligned.entrySafety_eq_unsafe
          hisUnsafe hconstructors
    · exact Hrecursors.generated.entrySafety_eq_unsafe
        hlocalSafety hrecursors
  have htypes : (ves.venv .unsafe).addConstVals (Hheaders.entries.map Prod.snd) =
      some Hheaders.context.venv := by
    rw [Hheaders.values]; exact Hheaders.translation.typesAdded
  rcases B.extendUnsafeOfHiddenExact wf hdecl hcompile
      horigins T.newRecursorsAligned hentries Hrecursors.closed howners hconstructors
      (Hrecursors.blockEliminatorsWF T.rules T.rulesWF)
      Hrecursors.cover (fun hfind => Hrecursors.ctorOrigin hfind) (B.typesLe htypes) with
    ⟨ves', wf', hle, hadd, -⟩
  exact ⟨ves', decl, Hheaders.context.venv, R.declared.venvCtors,
    wf', hle, R.core, hadd⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A source-aligned ordinary checker result extends the complete
safety-indexed abstract environment. The result is independent of whether
the source environment has canonical `Eq`. -/
theorem OrdinaryRunResult.extendWithSpecification
    {ves : VEnvs}
    (Hrun : OrdinaryRunResult source sourceEnv
      nparams types outEnv)
    (wf : ves.WF source.env)
    (hsource : sourceEnv = ves.venv source.safety)
    (hnotPartial : source.safety ≠ .partial)
    (hnonempty : types ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct sourceEnv source.lparams nparams types
        (source.safety != .safe)
        (ves'.venv (if source.safety != .safe then .unsafe else .safe))) := by
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hphases⟩
  have wf' : ves.WF c'.env := by
    rw [henv]
    exact wf
  have hnonempty' : types.toArray.toList ≠ [] := by
    simpa using hnonempty
  cases hs : source.safety with
  | «unsafe» =>
      have hcSafety : c'.safety = .unsafe := hsafety.trans hs
      have hcVEnv : Hc'.venv = ves.venv .unsafe := by
        exact hvenv.trans (hsource.trans (congrArg ves.venv hs))
      have hproduction :
          (source.safety != .safe) = (c'.safety != .safe) :=
        congrArg (fun safety => safety != .safe) hsafety.symm
      rcases OrdinaryInstallation.extendUnsafeExact Hphases wf'
          hcSafety hcVEnv hproduction hnonempty' with
        ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd⟩
      refine ⟨ves', wf'', hle, ?_⟩
      have hspec : SourceAddInduct (ves.venv .unsafe)
          c'.lparams nparams types (source.safety != .safe)
          (ves'.venv .unsafe) := {
        decl := decl
        envTypes := envTypes
        envCtors := envCtors
        source := by simpa using hcore
        extension := hadd
      }
      exact ⟨by simpa [hs, hlparams, hsource] using hspec⟩
  | safe =>
      have hcSafety : c'.safety = .safe := hsafety.trans hs
      have hcVEnv : Hc'.venv = ves.venv .safe := by
        exact hvenv.trans (hsource.trans (congrArg ves.venv hs))
      rcases OrdinaryInstallation.extendSafeExact Hphases wf'
          hcSafety hcVEnv hnonempty' with
        ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd⟩
      refine ⟨ves', wf'', hle, ?_⟩
      have hspec : SourceAddInduct (ves.venv .safe)
          c'.lparams nparams types (source.safety != .safe)
          (ves'.venv .safe) := {
        decl := decl
        envTypes := envTypes
        envCtors := envCtors
        source := by simpa using hcore
        extension := hadd
      }
      exact ⟨by simpa [hs, hlparams, hsource] using hspec⟩
  | «partial» =>
      exact (hnotPartial hs).elim

/-- Complete ordinary refinement retaining the independent source judgment,
without any premise about the prelude `Eq`. -/
theorem AddInductive.run.extensionModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv c.safety)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : types ≠ [])
    (HnotPartial : c.safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.CheckedHeaders
          Hc'.venv c'.lparams nparams commonParams commonLevel
            types.toArray.toList) →
      PrimitiveNamesFresh c' stats nparams depth numNested
        types.toArray (c.safety != .safe) Hc') :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (OrdinarySourceAddInduct Hc.venv c.lparams
          nparams types (c.safety != .safe)
          (ves'.venv (if c.safety != .safe then .unsafe else .safe))) := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp
  exact (AddInductive.run.sourceAlignedWF nparams numNested Hc
    Hclosed wf.envGhostFree wf.listedConstructorsPresent hctx hsize HnotPartial Hinputs).mono fun _ Hrun => by
      exact Hrun.extendWithSpecification wf hsource HnotPartial hnonempty

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

private theorem Constructor.eq_of_name_type {left right : Constructor}
    (hname : left.name = right.name) (htype : left.type = right.type) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem InductiveType.eq_of_fields {left right : InductiveType}
    (hname : left.name = right.name) (htype : left.type = right.type)
    (hctors : left.ctors = right.ctors) : left = right := by
  cases left
  cases right
  simp_all

/-- A zero-sized restoration map has no successful lookup, so on the ordinary
branch no lowering step replaces a nested occurrence. -/
theorem ElimNestedInductive.Result.auxFind?_eq_none_of_size_eq_zero
    {result : ElimNestedInductive.Result}
    (hsize : result.aux2nested.size = 0) (name : Name) :
    (show Std.TreeMap Name Expr Name.quickCmp from
      result.aux2nested)[name]? = none := by
  let map : Std.TreeMap Name Expr Name.quickCmp := result.aux2nested
  have hempty : map.isEmpty = true := by
    rw [Std.TreeMap.isEmpty_eq_size_eq_zero, hsize]
    rfl
  apply Std.TreeMap.getElem?_eq_none_of_contains_eq_false
  exact Std.TreeMap.contains_of_isEmpty hempty

/-- If the restoration map of the lowering result is empty, the
expression-lowering derivation contains no nested occurrence.  Every
remaining constructor is a structural identity and does not change the
lowering state. -/
theorem ExprLowering.Resolved.eq_of_aux2nested_size_eq_zero
    (H : ExprLowering.Resolved env lctx params As result input state out)
    (hsize : result.aux2nested.size = 0) :
    out = (input, state) := by
  induction H with
  | occurrence Hhit =>
      rcases Hhit.mapping with
        ⟨_value, _targetName, _levels, auxName, _auxLevels, nested,
          _Hcandidate, _hauxLevels, _hhead, _hlowered, _hnested, hlookup⟩
      change (show Std.TreeMap Name Expr Name.quickCmp from
        result.aux2nested)[auxName]? = some nested at hlookup
      rw [ElimNestedInductive.Result.auxFind?_eq_none_of_size_eq_zero
        hsize auxName] at hlookup
      contradiction
  | bvar | fvar | mvar | sort | const | lit => rfl
  | app _ _ _ ihFn ihArg =>
      cases ihFn
      cases ihArg
      rfl
  | lam _ _ _ ihDom ihBody =>
      cases ihDom
      cases ihBody
      rfl
  | forallE _ _ _ ihDom ihBody =>
      cases ihDom
      cases ihBody
      rfl
  | letE _ _ _ _ ihType ihValue ihBody =>
      cases ihType
      cases ihValue
      cases ihBody
      rfl
  | mdata _ _ ihBody =>
      cases ihBody
      rfl
  | proj _ _ ihBody =>
      cases ihBody
      rfl

/-- With no final auxiliary family to interpret, constructor lowering only
opens and recloses the source parameter telescope.  Closed source syntax
makes that round trip literal, not merely alpha-equivalent. -/
theorem ConstructorLowering.Resolved.eq_of_aux2nested_size_eq_zero
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hsize : result.aux2nested.size = 0)
    (hclosed : source.type.FVarsIn fun _ => False)
    (hbclosed : Closed source.type) :
    out.1 = source ∧ out.2.newTypes = state.newTypes := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, _Hselection,
      _hnodup, hopenedTypes, _hopenedAux, _hopenedNext, _hparams,
      Hmapping, htargetType⟩
  have hmapped := Hmapping.eq_of_aux2nested_size_eq_zero hsize
  have hlowered : lowered = tail := congrArg Prod.fst hmapped
  have houtState : out.2 = openedState := congrArg Prod.snd hmapped
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  have hsourceType : lctx.mkForall As tail = source.type :=
    Hopening.toParamOpening.root_mkForall_tail hlctxWF Htelescope
      (FVarsIn_to_FVarIdsIn hclosed) hbclosed
  have houtType : out.1.type = source.type := by
    rw [htargetType, hlowered, hsourceType]
  have houtName : out.1.name = source.name := H.name
  have houtCtor : out.1 = source :=
    Constructor.eq_of_name_type houtName houtType
  exact ⟨houtCtor, by rw [houtState, hopenedTypes]⟩

/-- Pointwise constructor identity composes through the state-threaded
constructor list.  Only the dynamic family array is retained here; changes
to the private fresh-name generator are intentionally irrelevant. -/
theorem ConstructorLowerings.Resolved.eq_of_aux2nested_size_eq_zero
    (H : ConstructorLowerings.Resolved env params nparams result sources state out)
    (hsize : result.aux2nested.size = 0)
    (hclosed : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (hbclosed : ∀ source ∈ sources, Closed source.type) :
    out.1 = sources ∧ out.2.newTypes = state.newTypes := by
  induction H with
  | nil => exact ⟨rfl, rfl⟩
  | @cons source state step sources out Hhead Htail ih =>
      have hheadClosed : source.type.FVarsIn fun _ => False :=
        hclosed source (List.mem_cons_self)
      rcases Hhead.eq_of_aux2nested_size_eq_zero hsize hheadClosed
          (hbclosed source List.mem_cons_self) with
        ⟨htarget, hheadTypes⟩
      have htailClosed : ∀ (ctor : Constructor), ctor ∈ sources →
          ctor.type.FVarsIn fun _ => False := by
        intro ctor hctor
        exact hclosed ctor (List.mem_cons_of_mem _ hctor)
      have htailBClosed : ∀ (ctor : Constructor), ctor ∈ sources →
          Closed ctor.type := by
        intro ctor hctor
        exact hbclosed ctor (List.mem_cons_of_mem _ hctor)
      rcases ih htailClosed htailBClosed with
        ⟨htail, htailTypes⟩
      exact ⟨by simp [htarget, htail], htailTypes.trans hheadTypes⟩

/-- Hence an entire source family is unchanged whenever the final lowering
map is empty. -/
theorem FamilyLowering.Resolved.eq_of_aux2nested_size_eq_zero
    (H : FamilyLowering.Resolved env params nparams result source state out)
    (hsize : result.aux2nested.size = 0)
    (hclosed : InductiveConstructorsClosed source)
    (hbclosed : InductiveConstructorsBVarClosed source) :
    out.1 = source ∧ out.2.newTypes = state.newTypes := by
  rcases H.constructors.eq_of_aux2nested_size_eq_zero hsize hclosed hbclosed with
    ⟨hctors, houtTypes⟩
  have hname : out.1.name = source.name := H.name
  have htype : out.1.type = source.type := H.type
  have hout : out.1 = source :=
    InductiveType.eq_of_fields hname htype hctors
  exact ⟨hout, houtTypes⟩

/-- Once the final map is empty, every dynamic queue step rewrites its
selected slot with the very family already stored there and appends no new
family.  Thus exhausting the queue returns exactly its starting family
array. -/
theorem LoweringQueue.types_eq_of_aux2nested_size_eq_zero
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hpending : PendingNewTypesClosed i state)
    (HpendingB : PendingNewTypesBVarClosed i state)
    (Hmap : NestedAuxMapModels out.1 out.2)
    (hsize : out.1.aux2nested.size = 0) :
    out.1.types = state.newTypes.toList := by
  induction H with
  | done => rfl
  | step Hnext Htail ih =>
      cases Hnext with
      | step hidx Hlowered =>
          rename_i iStep stateStep fuelStep outStep target loweredState
          have Hmapping := Hlowered.resolvedMapping
            Htail.resultNestedAuxLE Hmap
          have hclosed :
              InductiveConstructorsClosed stateStep.newTypes[iStep] :=
            Hpending iStep (Nat.le_refl _) hidx
          have hbclosed :
              InductiveConstructorsBVarClosed stateStep.newTypes[iStep] :=
            HpendingB iStep (Nat.le_refl _) hidx
          rcases Hmapping.eq_of_aux2nested_size_eq_zero hsize hclosed hbclosed with
            ⟨htarget, hloweredTypes⟩
          change target = stateStep.newTypes[iStep] at htarget
          change loweredState.newTypes = stateStep.newTypes at hloweredTypes
          have hnextTypes :
              ({ loweredState with
                newTypes := loweredState.newTypes.set! iStep target } :
                ElimNestedInductive.State).newTypes = stateStep.newTypes := by
            simp only
            rw [htarget, hloweredTypes]
            rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds,
              dif_pos hidx, Array.set_getElem_self hidx]
          have HpendingNext : PendingNewTypesClosed (iStep + 1)
              ({ loweredState with
                newTypes := loweredState.newTypes.set! iStep target } :
                ElimNestedInductive.State) := by
            intro j hjCursor hj
            have harray : loweredState.newTypes.set! iStep target =
                stateStep.newTypes := by simpa only using hnextTypes
            have hjState : j < stateStep.newTypes.size := by
              simpa only [harray] using hj
            simpa only [harray] using
              Hpending j (by omega) hjState
          have HpendingBNext : PendingNewTypesBVarClosed (iStep + 1)
              ({ loweredState with
                newTypes := loweredState.newTypes.set! iStep target } :
                ElimNestedInductive.State) := by
            intro j hjCursor hj
            have harray : loweredState.newTypes.set! iStep target =
                stateStep.newTypes := by simpa only using hnextTypes
            have hjState : j < stateStep.newTypes.size := by
              simpa only [harray] using hj
            simpa only [harray] using
              HpendingB j (by omega) hjState
          rw [ih HpendingNext HpendingBNext Hmap hsize, hnextTypes]

/-- Source syntax checked before lowering is therefore preserved literally
by every successful ordinary (zero-auxiliary) lowering result. -/
theorem NestedLoweringOutput.types_eq_source_of_aux2nested_size_eq_zero
    {initialState : ElimNestedInductive.State}
    (H : NestedLoweringOutput env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (hsize : result.aux2nested.size = 0) :
    result.types = sourceTypes := by
  rcases H with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨first, rest, tail, paramsState, lctx, params, hsourceTypes, _Hopening,
      hinitialTypes, _hinitialAux, _hinitialNext, _Hprefix, _Hctx,
      _Hselection, Hqueue⟩
  have Hpending : PendingNewTypesClosed 0 paramsState := by
    intro j _hjCursor hj
    have hjSource : j < sourceTypes.length := by
      simpa [hinitialTypes] using hj
    have hvalue : paramsState.newTypes[j] = sourceTypes[j] := by
      have heq := congrArg (fun xs : Array InductiveType => xs[j]!)
        hinitialTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjSource] using heq
    rw [hvalue]
    exact Hsources.constructorsClosed (List.getElem_mem hjSource)
  have HpendingB : PendingNewTypesBVarClosed 0 paramsState := by
    intro j _hjCursor hj
    have hjSource : j < sourceTypes.length := by
      simpa [hinitialTypes] using hj
    have hvalue : paramsState.newTypes[j] = sourceTypes[j] := by
      have heq := congrArg (fun xs : Array InductiveType => xs[j]!)
        hinitialTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjSource] using heq
    rw [hvalue]
    exact HsourcesB.constructorsClosed (List.getElem_mem hjSource)
  have Hmap : NestedAuxMapModels result finalState :=
    Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have hresult := Hqueue.types_eq_of_aux2nested_size_eq_zero
    Hpending HpendingB Hmap hsize
  rw [hresult, hinitialTypes]

/-- The executable starts lowering from this exact fresh state.  This
specialization removes the generic cache premise from the declaration-facing
ordinary branch. -/
theorem NestedLoweringOutput.ordinary_types_eq_source
    (H : NestedLoweringOutput env fuel nparams sourceTypes
      { lvls := levels, newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (hsize : result.aux2nested.size = 0) :
    result.types = sourceTypes := by
  apply NestedLoweringOutput.types_eq_source_of_aux2nested_size_eq_zero
    (initialState := { lvls := levels, newTypes := sourceTypes.toArray })
    H Hsources HsourcesB
  · rfl
  · exact hsize

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The ordinary branch of the executable cannot request a reserved primitive
name.  Consequently all three primitive-name side conditions are vacuous; the
only remaining run inputs are facts retained by the shared header and
constructor pipeline. -/
theorem PrimitiveNamesFresh.ofAllowPrimitiveFalse
    (hallow : c.allowPrimitive = false) :
    PrimitiveNamesFresh c stats nparams depth numNested indTypes
      isUnsafe Hc where
  freshTypes htrue := by simp_all
  freshConstructors htrue := by simp_all
  freshRecursors htrue := by simp_all

/-- A successful lowering run can only have started from a nonempty source
mutual block: the executable checks nonemptiness before lowering. -/
theorem NestedLoweringOutput.sourceTypes_nonempty
    (H : NestedLoweringOutput env fuel nparams sourceTypes initialState result) :
    sourceTypes ≠ [] := by
  rcases H with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨first, rest, tail, paramsState, lctx, params, htypes, _⟩
  simp [htypes]

/-- Lowering retains every source family, so a successful lowering result
is itself nonempty. -/
theorem NestedLoweringOutput.resultTypes_nonempty
    (initialState : ElimNestedInductive.State)
    (H : NestedLoweringOutput env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    result.types ≠ [] := by
  have hsource : 0 < sourceTypes.length := by
    cases htypes : sourceTypes with
    | nil => exact (H.sourceTypes_nonempty htypes).elim
    | cons _ _ => simp
  exact List.ne_nil_of_length_pos
    (Nat.lt_of_lt_of_le hsource H.sourceTypes_length_le)

/-- Well-formedness of the ordinary (zero-auxiliary) branch alone.  Unlike the
specification-facing endpoints below, this needs no closedness of the source
syntax: the checked block is whatever lowering produced. -/
theorem Environment.addInductiveAfterLowering.ordinaryInstalledModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hlower : NestedLoweringOutput env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel (hmode _)
  have hsource : Hc.venv = ves.venv c.safety := by
    rfl
  have hctx : Hc.mlctx.vlctx = [] := by
    rfl
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have hnonempty : res.types ≠ [] :=
    Hlower.resultTypes_nonempty
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray }
  have Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.CheckedHeaders
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      PrimitiveNamesFresh c' stats nparams depth 0
        res.types.toArray (c.safety != .safe) Hc' := by
    intro c' stats depth commonParams commonLevel Hc' hallow _hfuel _Hsemantic
    exact PrimitiveNamesFresh.ofAllowPrimitiveFalse
      (by simpa [c, initialContext] using hallow)
  have Hrun := AddInductive.run.extensionModelWF
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hsource
    wf.inductivesClosed hctx hnonempty hnotPartial Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  rcases Hrun outEnv hout' with ⟨ves', wf', hle, _⟩
  exact ⟨ves', wf', hle⟩

/-- Source-facing ordinary refinement of `addInductiveAfterLowering`.  The
successful source precheck and zero-auxiliary lowering run prove that the
block checked by `AddInductive.run` is literally the source declaration;
the installed model and independent source judgment therefore come from the same
execution. -/
theorem Environment.addInductiveAfterLowering.ordinaryExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (Hlower : NestedLoweringOutput env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct
            (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
            sourceTypes isUnsafe
            (ves'.venv (if isUnsafe then .unsafe else .safe))) := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel (hmode _)
  have hsource : Hc.venv = ves.venv c.safety := by
    rfl
  have hctx : Hc.mlctx.vlctx = [] := by
    rfl
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have hnonempty : res.types ≠ [] :=
    Hlower.resultTypes_nonempty
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray }
  have htypes : res.types = sourceTypes :=
    Hlower.ordinary_types_eq_source Hsources HsourcesB haux
  have Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.CheckedHeaders
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      PrimitiveNamesFresh c' stats nparams depth 0
        res.types.toArray (c.safety != .safe) Hc' := by
    intro c' stats depth commonParams commonLevel Hc' hallow _hfuel _Hsemantic
    exact PrimitiveNamesFresh.ofAllowPrimitiveFalse
      (by simpa [c, initialContext] using hallow)
  have Hrun := AddInductive.run.extensionModelWF
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf hsource
    wf.inductivesClosed hctx hnonempty hnotPartial Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  rcases Hrun outEnv hout' with ⟨ves', wf', hle, ⟨S⟩⟩
  refine ⟨ves', wf', hle, ⟨?_⟩⟩
  rw [htypes, hsource] at S
  have hisUnsafe : (c.safety != .safe) = isUnsafe := by
    cases isUnsafe <;> rfl
  rw [hisUnsafe] at S
  simpa [c, safety, initialContext] using S

end VerifyInductive
end Lean4Lean
