import Lean4Lean.Verify.Inductive.Install.Formation
import Lean4Lean.Verify.Inductive.Install.Lookups
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint
import Lean4Lean.Verify.Inductive.Recursor.Context.Unannotated

/-! The complete ordinary checker (`AddInductive.runWithStats`, `AddInductive.run`)
refines a skeleton-free result (`OrdinaryInstallation`, `OrdinaryRunResult`):
the declaration is the one synthesized by the successful header and
constructor traversals, and the same declaration is carried through the
recursor check and the rules. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Complete post-analysis result when the declaration is synthesized by the
successful header and constructor traversals rather than fixed before
execution. -/
def OrdinaryInstallation
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (sourceEnv : VEnv) (outEnv : Environment) : Prop :=
  ∃ decl headerEnv ctorEnv,
    ∃ Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv,
    ∃ R : OrdinaryConstructorCheck Hheaders ctorEnv,
      Nonempty (RecursorCheck R.toConstructorCheck outEnv)

/-- Complete ordinary `runWithStats` refinement from skeleton-free formation.
The existential declaration selected by constructor checking remains the
same declaration through recursor generation and equation reconstruction. -/
theorem AddInductive.runWithStats.typingWF
    (stats : AddInductive.InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (c : AddInductive.Context) (depth : Nat) (sourceEnv : VEnv)
    (Hformation :
      (AddInductive.constructorPhase stats nparams indTypes numNested isUnsafe c).WF
        fun out => ∃ decl headerEnv,
          ∃ Hheaders : HeaderEnvironment c stats decl nparams isUnsafe
            depth sourceEnv indTypes headerEnv,
          ∃ R : OrdinaryConstructorCheck Hheaders out.1,
            R.classes = out.2 ∧ MutualInductivesClosed out.1)
    (hlparams : c.lparams.Nodup)
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      (OrdinaryInstallation c stats nparams depth indTypes isUnsafe
        sourceEnv) := by
  unfold AddInductive.runWithStats
  refine Hformation.bind fun out Hresult => ?_
  obtain ⟨ctorEnv, positivity⟩ := out
  rcases Hresult with ⟨decl, headerEnv, Hheaders, R, hclasses, hclosed⟩
  have hlitHeaders := Hheaders.checkedAvailableLiteralDisjoint
  have hlitCtors :=
    R.declared.installed.availableLiteralDisjoint hlitHeaders
  have hlit : checkPositivityStep.AvailableLiteralDisjoint
      R.declared.context.venv stats.indConsts := by
    rw [R.declared.contextVEnv]
    exact (hlitCtors.addEliminators _).addProjections _
  exact (R.toConstructorCheck.recursorPhasesWF (hsourceSafety := hsourceSafety) hclosed hlparams
    hlit hnotPartial hnprim hclasses.symm).mono
      fun outEnv Hrecursors =>
        show OrdinaryInstallation c stats nparams depth indTypes
          isUnsafe sourceEnv outEnv
        from ⟨decl, headerEnv, ctorEnv, Hheaders, R, Hrecursors⟩

/-- One successful semantic header accumulation closes the complete ordinary
post-analysis checker without any declaration, skeleton, or constructor
target supplied by the caller. -/
theorem AddInductive.runWithStats.closedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (Hclosed : MutualInductivesClosed c.env)
    (HenvGF : TypeChecker.EnvGhostFree (fun _ => True) c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprimTypes : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hnprimCtors : c.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hlparams : c.lparams.Nodup)
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
    (hnotPartial : c.safety ≠ .partial)
    (hnprimRecursors : c.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName indTypes[owner]!.name)) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      (OrdinaryInstallation c stats nparams depth indTypes isUnsafe
        Hc.venv) := by
  apply AddInductive.runWithStats.typingWF (hsourceSafety := hsourceSafety) stats nparams indTypes numNested
    isUnsafe c depth Hc.venv
  · exact AddInductive.formationCoreClosedWF Hsemantic hlevels
      hlevelParams hindicesSize hindices hconsts hparams hcommonParams
      Hcache Hsuffix Hambient hcommon hnotzero Hclosed hvisible hnprimTypes
      Lean4Lean.consumeTypeAnnotationsCompat hnprimCtors hlparams HenvGF Hpresent
  · exact hlparams
  · exact hnotPartial
  · exact hnprimRecursors

/-- Remaining environment-wide contracts at the post-header boundary.  The
declaration, its constructor targets, literal disjointness, formation, and
all equation data are deliberately absent: successful execution produces
them. -/
structure PrimitiveNamesFresh
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth numNested : Nat) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (Hc : ContextWF c) : Prop where
  freshTypes : c.allowPrimitive = true → ∀ info ∈
    (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
      isUnsafe c.lparams).toList,
    ¬ Kernel.Environment.primitives.contains info.name
  freshConstructors : c.allowPrimitive = true →
    ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
    ¬ Kernel.Environment.primitives.contains ctor.name
  freshRecursors : c.allowPrimitive = true →
    ∀ owner (_howner : owner < indTypes.size),
    ¬ Kernel.Environment.primitives.contains
      (Lean.mkRecName indTypes[owner]!.name)

/-- Source-aligned declaration-facing result of the complete ordinary
checker.  In addition to the semantic certificate, this retains the exact
verification environment from which header checking began. -/
def OrdinaryRunResult
    (source : AddInductive.Context) (sourceEnv : VEnv) (nparams : Nat)
    (types : List InductiveType)
    (outEnv : Environment) : Prop :=
  ∃ c' stats depth commonParams commonLevel,
    ∃ Hc' : ContextWF c',
    c'.env = source.env ∧
    c'.safety = source.safety ∧
    c'.lparams = source.lparams ∧
    c'.allowPrimitive = source.allowPrimitive ∧
    c'.fuel = source.fuel ∧
    Hc'.venv = sourceEnv ∧
    ∃ _Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc'.venv c'.lparams nparams commonParams commonLevel
          types.toArray.toList,
      OrdinaryInstallation c' stats nparams depth
        types.toArray (source.safety != .safe) Hc'.venv outEnv

/-- The complete executable ordinary checker refines a skeleton-free
semantic result.  This replaces `run.withMetadata`'s caller-supplied abstract
skeleton with the declaration constructed from successful header and
constructor executions. -/
theorem AddInductive.run.sourceAlignedWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (HenvGF : TypeChecker.EnvGhostFree (fun _ => True) c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
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
    (AddInductive.run nparams types numNested c).WF
      (OrdinaryRunResult c Hc.venv nparams
        types) := by
  have Hduplicates :
      (Kernel.Environment.checkDuplicatedUnivParams c.lparams).WF
        fun _ => c.lparams.Nodup :=
    Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams
  have Hcombined := Hduplicates.bind fun _ hnodup => by
    apply checkInductiveTypes.loopInd.checkInductiveTypes.accumulatesHeadersSourceAligned
      (fun stats => AddInductive.runWithStats stats nparams
        types.toArray numNested (c.safety != .safe))
      (OrdinaryRunResult c Hc.venv nparams
        types)
      Hc hctx hnonempty Lean4Lean.consumeTypeAnnotationsCompat
    intro c' stats depth commonParams commonLevel Hc' henv hsafety
      hlparams hallowPrimitive hfuel hvenv Hsemantic
      hlevels hlevelParams hindicesSize hindices _hconstsSize hconsts
      _hnonempty hparams hcommonParams Hcache Hsuffix Hambient hcommon hnotzero
    let I := Hinputs (stats := stats) (depth := depth) Hc'
      hallowPrimitive hfuel Hsemantic
    have Hclosed' : MutualInductivesClosed c'.env := by
      rw [henv]
      exact Hclosed
    have HenvGF' : TypeChecker.EnvGhostFree (fun _ => True) c'.env := by
      rw [henv]
      exact HenvGF
    have Hpresent' : ListedConstructorsPresent c'.env := by
      rw [henv]
      exact Hpresent
    have hvisible : c'.safety ≤
        (if c.safety != .safe then DefinitionSafety.unsafe else .safe) := by
      rw [hsafety]
      cases h : c.safety with
      | «unsafe» => simp
      | safe => simp
      | «partial» => exact (HnotPartial h).elim
    have hlparamsNodup : c'.lparams.Nodup := by
      rw [hlparams]
      exact hnodup
    have hnotPartial : c'.safety ≠ .partial := by
      simpa [hsafety] using HnotPartial
    exact (AddInductive.runWithStats.closedWF
      (hsourceSafety := by rw [hsafety]) Hsemantic hlevels
      hlevelParams hindicesSize hindices hconsts hparams hcommonParams
      Hcache Hsuffix Hambient hcommon hnotzero Hclosed' HenvGF' Hpresent' hvisible I.freshTypes
      I.freshConstructors hlparamsNodup hnotPartial
      I.freshRecursors).mono fun outEnv Hrun =>
        ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
          hlparams, hallowPrimitive, hfuel, hvenv, Hsemantic, Hrun⟩
  simpa [AddInductive.run] using Hcombined

end VerifyInductive
end Lean4Lean
