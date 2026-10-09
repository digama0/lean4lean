import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations
import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshExtensions
import Lean4Lean.Verify.Environment.Lemmas

/-! Lookups of inductive families and constructors in the kernel environment after nested
restoration: every visible family is a base constant or one of the source declaration's
families (`NestedRestorationFolds.inductInfosFromDecl`), and every constructor's owner
is present (`NestedRestorationFolds.constructorOwnersPresent`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem Expr.constructorArity_mkAppList_of_zero
    (h : AddInductive.constructorArity e = 0) :
    AddInductive.constructorArity (e.mkAppList args) = 0 := by
  induction args generalizing e with
  | nil => exact h
  | cons arg args ih =>
      exact ih (e := .app e arg) rfl

private theorem NodeReplacementResolved.output_constructorArity_eq_zero
    (H : NodeReplacementResolved env lctx params As input state output
      nextState result finalState) :
    AddInductive.constructorArity output = 0 := by
  rcases H.mapping with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, _hauxLevels, _hhead, houtput, _hnested, _hlookup⟩
  rw [houtput]
  rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
  rw [Expr.mkAppN_eq_mkAppList]
  apply Expr.constructorArity_mkAppList_of_zero
  apply Expr.constructorArity_mkAppList_of_zero
  rfl

private theorem NodeReplacementResolved.input_constructorArity_eq_zero
    (H : NodeReplacementResolved env lctx params As input state output
      nextState result finalState) :
    AddInductive.constructorArity input = 0 := by
  rcases H with
    ⟨value, targetName, levels, Hcandidate, hhead, Hrecognized, Hlater, Hmap⟩
  cases input <;>
    simp_all [AddInductive.constructorArity, Expr.getAppFn]

private theorem ExprLowering.Resolved.constructorArity_eq
    (H : ExprLowering.Resolved env lctx params As result input state output) :
    AddInductive.constructorArity output.1 =
      AddInductive.constructorArity input := by
  induction H with
  | occurrence Hnode =>
      exact Hnode.output_constructorArity_eq_zero.trans
        Hnode.input_constructorArity_eq_zero.symm
  | bvar | fvar | mvar | sort | const | lit => rfl
  | app Hnode Hfn Harg ihFn ihArg =>
      simp [AddInductive.constructorArity, Expr.updateApp!]
  | lam Hnode Hdom Hbody ihDom ihBody =>
      simp [AddInductive.constructorArity, Expr.updateLambdaE!]
  | forallE Hnode Hdom Hbody ihDom ihBody =>
      simp [AddInductive.constructorArity, Expr.updateForallE!, ihBody]
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
      simp [AddInductive.constructorArity, Expr.updateLet!]
  | mdata Hnode Hbody ihBody =>
      simp [AddInductive.constructorArity, Expr.updateMData!]
  | proj Hnode Hbody ihBody =>
      simp [AddInductive.constructorArity, Expr.updateProj!]

private theorem Expr.constructorArity_abstractN
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    AddInductive.constructorArity (e.abstractN fvars k) =
      AddInductive.constructorArity e := by
  induction e generalizing k <;>
    simp [Expr.abstractN, AddInductive.constructorArity, *]
  all_goals split <;> simp [AddInductive.constructorArity]

private theorem Expr.ForallTelescope.constructorArity_eq
    (H : Expr.ForallTelescope input arity residual) :
    AddInductive.constructorArity input =
      arity + AddInductive.constructorArity residual := by
  induction H with
  | nil => simp
  | cons Htail ih =>
      simp [AddInductive.constructorArity, ih]
      omega

private theorem ConstructorLowering.Resolved.constructorArity_eq
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (Hsource : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type) :
    AddInductive.constructorArity out.1.type =
      AddInductive.constructorArity source.type := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodup, htypes, haux, hnext, harity, Hmapping, htype⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  have hsource : lctx.mkForall As tail = source.type :=
    Hopening.toParamOpening.root_mkForall_tail hlctxWF Htelescope
      (FVarsIn_to_FVarIdsIn Hsource) hsourceBVar
  have HtailTelescope := Hselection.forallTelescope tail
  have HloweredTelescope := Hselection.forallTelescope lowered
  have htailArity := HtailTelescope.constructorArity_eq
  have hloweredArity := HloweredTelescope.constructorArity_eq
  rw [htype, ← hsource, hloweredArity, htailArity,
    Expr.constructorArity_abstractN,
    Expr.constructorArity_abstractN, Hmapping.constructorArity_eq]

/-- Lookup classification for one checked addition to the kernel environment. -/
theorem Environment.find?_freshAdd_cases
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hfind : (env.add ci).find? name = some found) :
    (name = ci.name ∧ found = ci) ∨ env.find? name = some found := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change SMap.find?' (env.constants.insert ci.name ci) name = some found at hfind
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?,
    hwf.find?_insert] at hfind
  split at hfind
  · left
    exact ⟨(LawfulBEq.eq_of_beq (by assumption)).symm,
      (Option.some.inj hfind).symm⟩
  · right
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    exact hfind

/-- An old lookup is preserved by one checked addition. -/
theorem Environment.find?_freshAdd_preserves
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hfind : env.find? name = some found) :
    (env.add ci).find? name = some found := by
  have hne : ci.name ≠ name := by
    intro heq
    subst name
    rw [hfind] at hfresh
    contradiction
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh hfind
  change SMap.find?' (env.constants.insert ci.name ci) name = some found
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?,
    hwf.find?_insert, if_neg (by simpa using hne)]
  exact hfind

/-- The keyed value is visible immediately after its checked addition. -/
theorem Environment.find?_freshAdd_self
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none) :
    (env.add ci).find? ci.name = some ci := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change SMap.find?' (env.constants.insert ci.name ci) ci.name = some ci
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?, hwf.find?_insert]
  simp

theorem Environment.mapFind_of_find
    {env : Environment} (hwf : env.constants.WF)
    (hfind : env.find? name = some found) :
    env.constants.find? name = some found := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfind
  exact hfind

/-- Adding one fresh non-inductive declaration preserves `InductInfosFromDecl`.
Existing family and constructor lookups are rebased through the one-step
extension. -/
theorem InductInfosFromDecl.addNoninductive
    {source env : Environment} {ci : ConstantInfo}
    (H : InductInfosFromDecl source.constants env.constants decl)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnind : ∀ info, ci ≠ .inductInfo info) :
    InductInfosFromDecl source.constants (env.add ci).constants decl := by
  intro familyName familyInfo hfamily
  have htargetWF := constantsWF_add_checked hwf hfresh
  have hfamilyEnv : (env.add ci).find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?]
    exact hfamily
  rcases Environment.find?_freshAdd_cases hwf ci hfresh hfamilyEnv with
      hnew | hold
  · rcases hnew with ⟨hname, hinfo⟩
    subst familyName
    exact False.elim (hnind familyInfo hinfo.symm)
  · have holdMap : env.constants.find? familyName =
        some (.inductInfo familyInfo) := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hold
    rcases H familyName familyInfo holdMap with hsource | hcurrent
    · exact .inl hsource
    · rcases hcurrent with ⟨familyIdx, hname, ⟨A⟩⟩
      exact .inr ⟨familyIdx, hname, ⟨A.rebase
        (by simpa [← hname] using hfamily)
        (fun {name found} hfind => by
          have hfindEnv : env.find? name = some found := by
            rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
          have hpreserved := Environment.find?_freshAdd_preserves hwf ci
            hfresh hfindEnv
          rwa [Lean.Kernel.Environment.find?,
            htargetWF.find?'_eq_find?] at hpreserved)⟩⟩

/-- The auxiliary restoration fold installs recursors only, so it adds no
inductive family. -/
theorem FoldSteps.recursorPreservesInductInfosFromDecl
    {sourceEnv targetEnv base : Environment}
    (Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF)
    (Horigins : InductInfosFromDecl base.constants
      sourceEnv.constants decl) :
    InductInfosFromDecl base.constants targetEnv.constants decl := by
  induction Htrace with
  | nil => exact Horigins
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
      have hfresh : stepSource.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middle = stepSource.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middle.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      apply ih hmiddleWF
      rw [hmiddle]
      exact InductInfosFromDecl.addNoninductive Horigins hsourceWF
        hfresh (by simp [ci])

/-- Constructor restoration cannot create an inductive-family lookup. -/
theorem FoldSteps.constructorInductiveFindSource
    (Htrace : FoldSteps
      (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF)
    (hfind : targetEnv.find? familyName =
      some (.inductInfo familyInfo)) :
    sourceEnv.find? familyName = some (.inductInfo familyInfo) := by
  induction Htrace with
  | nil => exact hfind
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
      have hfresh : stepSource.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middle = stepSource.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middle.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      have hmiddleFind := ih hmiddleWF hfind
      rw [hmiddle] at hmiddleFind
      rcases Environment.find?_freshAdd_cases hsourceWF ci hfresh
          hmiddleFind with hnew | hold
      · rcases hnew with ⟨_hname, hinfo⟩
        simp [ci] at hinfo
      · exact hold

/-- The kernel lookup of one restored source constructor, by position: the
lowered lookup and restoration metadata of its step, and the restored
constructor lookup in the target environment of the constructor fold. -/
theorem FoldSteps.constructorKernelOriginAt
    (H : FoldSteps (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF)
    (ctorIdx : Nat) (hname : ctorIdx < names.length) :
    ∃ stepSource stepTarget oldInfo newInfo,
      ∃ Hstep : RestoredConstructorStep result loweredEnv names[ctorIdx]
        stepSource stepTarget,
        Hstep.oldInfo = oldInfo ∧
        Hstep.restored.newInfo = newInfo ∧
        ConstructorRestoration result loweredEnv oldInfo newInfo ∧
        targetEnv.find? newInfo.name =
          some (.ctorInfo newInfo) := by
  induction H generalizing ctorIdx with
  | nil => simp at hname
  | @cons head stepSource middle tail target Hstep Htail ih =>
      cases ctorIdx with
      | zero =>
          let newInfo := Hstep.restored.newInfo
          let ci : ConstantInfo := .ctorInfo newInfo
          have hfresh : stepSource.find?
              ci.name = none :=
            find?_none_of_contains_false hsourceWF Hstep.restored.fresh
          have hmiddle : middle = stepSource.add
              ci :=
            congrArg Prod.snd Hstep.restored.output
          have hmiddleWF : middle.constants.WF :=
            hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
          have hmiddleFind : middle.find? newInfo.name =
              some (.ctorInfo newInfo) := by
            rw [hmiddle]
            exact Environment.find?_freshAdd_self hsourceWF ci hfresh
          have htargetFind : target.find? newInfo.name =
              some (.ctorInfo newInfo) := by
            obtain ⟨entries, Hfresh⟩ :=
              Htail.constructorFreshExtension hmiddleWF
            exact Hfresh.preservesSourceFind hmiddleWF hmiddleFind
          exact ⟨stepSource, middle, Hstep.oldInfo,
            newInfo, by simpa using Hstep, rfl, rfl,
            Hstep.restored.restoration, htargetFind⟩
      | succ ctorIdx =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hname
          let newInfo := Hstep.restored.newInfo
          let ci : ConstantInfo := .ctorInfo newInfo
          have hfresh : stepSource.find?
              ci.name = none :=
            find?_none_of_contains_false hsourceWF Hstep.restored.fresh
          have hmiddle : middle = stepSource.add
              ci :=
            congrArg Prod.snd Hstep.restored.output
          have hmiddleWF : middle.constants.WF :=
            hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
          rcases ih hmiddleWF ctorIdx hname with
            ⟨laterSource, laterTarget, oldInfo, newInfo, Hlater, hold,
              hnew, Hrestore, htarget⟩
          exact ⟨laterSource, laterTarget, oldInfo, newInfo,
            by simpa using Hlater, hold, hnew, Hrestore, htarget⟩

/-- A constructor visible after a constructor-restoration fold either came from
the source environment or is the result of one positional restoration step. -/
theorem FoldSteps.constructorFindCases
    (H : FoldSteps (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF)
    (hfind : targetEnv.find? name = some (.ctorInfo found)) :
    sourceEnv.find? name = some (.ctorInfo found) ∨
      ∃ ctorIdx, ∃ hidx : ctorIdx < names.length,
        ∃ stepSource stepTarget,
        ∃ Hstep : RestoredConstructorStep result loweredEnv names[ctorIdx]
            stepSource stepTarget,
          name = Hstep.restored.newInfo.name ∧
          found = Hstep.restored.newInfo := by
  induction H with
  | nil => exact .inl hfind
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
      have hfresh : stepSource.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middle = stepSource.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middle.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      rcases ih hmiddleWF hfind with hold | hnew
      · rw [hmiddle] at hold
        rcases Environment.find?_freshAdd_cases hsourceWF ci hfresh hold with
          hhead | hsource
        · rcases hhead with ⟨hname, hfound⟩
          right
          refine ⟨0, by simp, stepSource, middle, ?_, ?_, ?_⟩
          · simpa using Hstep
          · simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal]
              using hname
          · exact ConstantInfo.ctorInfo.inj hfound
        · exact .inl hsource
      · rcases hnew with
          ⟨ctorIdx, hidx, laterSource, laterTarget, Hlater, hname, hfound⟩
        right
        exact ⟨ctorIdx + 1, by simpa, laterSource, laterTarget,
          by simpa using Hlater, hname, hfound⟩

/-- One complete restored source-family installation exposes either its
newly restored header or an unchanged lookup from the preceding environment.
The constructor and recursor sub-phases are proved non-inductive from their
concrete `ConstantInfo` constructors. -/
theorem SourceFamilyRestoration.inductiveFindCases
    (H : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hsourceWF : sourceEnv.constants.WF)
    (hfind : targetEnv.find? familyName = some (.inductInfo familyInfo)) :
    (familyName = H.header.newInfo.name ∧
      familyInfo = H.header.newInfo) ∨
      sourceEnv.find? familyName = some (.inductInfo familyInfo) := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hsourceWF H.header.fresh
  have hheaderWF : H.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hsourceWF hheaderFresh
  obtain ⟨ctorEntries, HctorFresh⟩ :=
    H.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF : H.constructorEnv.constants.WF :=
    HctorFresh.targetWF hheaderWF
  have hctorFind : H.headerEnv.find? familyName =
      some (.inductInfo familyInfo) := by
    let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
    have hrecFresh : H.constructorEnv.find? recursor.name = none := by
      exact find?_none_of_contains_false hconstructorWF
        H.recursor.restored.fresh
    have htarget : targetEnv = H.constructorEnv.add recursor :=
      congrArg Prod.snd H.recursor.restored.output
    rw [htarget] at hfind
    rcases Environment.find?_freshAdd_cases
        hconstructorWF recursor hrecFresh hfind with hnew | hold
    · rcases hnew with ⟨_hname, hinfo⟩
      simp [recursor] at hinfo
    · exact H.constructors.constructorInductiveFindSource hheaderWF hold
  rw [hheaderEnv] at hctorFind
  rcases Environment.find?_freshAdd_cases hsourceWF header hheaderFresh
      hctorFind with hnew | hold
  · left
    simpa [header, ConstantInfo.name, ConstantInfo.toConstantVal] using hnew
  · exact .inr hold

/-- The restored family header remains visible after its constructor fold and
source recursor addition. -/
theorem SourceFamilyRestoration.headerFind
    (H : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hsourceWF : sourceEnv.constants.WF) :
    targetEnv.find? H.header.newInfo.name =
      some (.inductInfo H.header.newInfo) := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hsourceWF H.header.fresh
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderWF : H.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hsourceWF hheaderFresh
  have hheaderFind' : H.headerEnv.find? header.name = some header := by
    rw [hheaderEnv]
    exact Environment.find?_freshAdd_self hsourceWF header hheaderFresh
  have hheaderFind : H.headerEnv.find? H.header.newInfo.name =
      some (.inductInfo H.header.newInfo) := by
    simpa [header, ConstantInfo.name, ConstantInfo.toConstantVal] using
      hheaderFind'
  obtain ⟨ctorEntries, HctorFresh⟩ :=
    H.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF := HctorFresh.targetWF hheaderWF
  have hconstructorFind :=
    HctorFresh.preservesSourceFind hheaderWF hheaderFind
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hconstructorWF H.recursor.restored.fresh
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have htargetFind : targetEnv.find? header.name = some header := by
    rw [htarget]
    exact Environment.find?_freshAdd_preserves hconstructorWF recursor
      hrecFresh (by
        simpa [header, ConstantInfo.name, ConstantInfo.toConstantVal] using
          hconstructorFind)
  simpa [header, ConstantInfo.name, ConstantInfo.toConstantVal] using
    htargetFind

/-- Extension of `InductInfosFromDecl` by one restored source family. The
alignment premise is indexed by the restored header in the target environment;
the classification of lookups and the rebasing of earlier alignments are
derived from the restoration fold. -/
theorem SourceFamilyRestoration.extendInductInfosFromDecl
    {base : Environment}
    (H : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hsourceWF : sourceEnv.constants.WF)
    (Horigins : InductInfosFromDecl base.constants
      sourceEnv.constants decl)
    (Hnew : InductInfoAlignment targetEnv.constants decl familyIdx
      H.header.newInfo) :
    InductInfosFromDecl base.constants targetEnv.constants decl := by
  intro familyName familyInfo hfind
  have htargetWF := H.freshExtension hsourceWF
  rcases htargetWF with ⟨entries, Hfresh⟩
  have hfindEnv : targetEnv.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?,
      (Hfresh.targetWF hsourceWF).find?'_eq_find?]
    exact hfind
  rcases H.inductiveFindCases hsourceWF hfindEnv with hnew | hold
  · rcases hnew with ⟨hname, rfl⟩
    exact .inr ⟨familyIdx, hname, ⟨Hnew⟩⟩
  · have holdMap : sourceEnv.constants.find? familyName =
        some (.inductInfo familyInfo) := by
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?] at hold
    rcases Horigins familyName familyInfo holdMap with hbase | hcurrent
    · exact .inl hbase
    · rcases hcurrent with ⟨currentIdx, hname, ⟨A⟩⟩
      exact .inr ⟨currentIdx, hname, ⟨A.rebase
        (by simpa [← hname] using hfind)
        (fun {name found} hsource =>
          Hfresh.preservesSourceMapFind hsourceWF hsource)⟩⟩

/-- Positional form of the family-header lookup after the lowered run, with
all metadata later preserved by nested restoration. -/
theorem RecursorCheck.findSourceHeaderAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size) :
    ∃ info : InductiveVal,
      outEnv.find? indTypes[familyIdx].name = some (.inductInfo info) ∧
      info.name = indTypes[familyIdx].name ∧
      info.type = indTypes[familyIdx].type ∧
      info.ctors = indTypes[familyIdx].ctors.map (fun ctor => ctor.name) ∧
      info.all = indTypes.toList.map (fun type => type.name) ∧
      info.levelParams = c.lparams ∧
      info.numParams = nparams ∧
      info.isUnsafe = isUnsafe := by
  rcases Hheaders.sourceAligned with ⟨numNested, Haligned⟩
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, Hheaders.statsWF.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have hinfosSize : infos.size = indTypes.size := by
    simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hinfoIdx : familyIdx < infos.size := by
    simpa [hinfosSize] using hfamily
  let info := infos[familyIdx]
  have hinfoMem : info ∈ infos.toList := by
    apply Array.mem_toList_iff.mpr
    simp [info]
  rcases Haligned.findInfo hinfoMem with ⟨familyValue, hfamilyEntry⟩
  have hheader : headerEnv.find? info.name = some (.inductInfo info) :=
    Hheaders.installed.findEntry
      Hheaders.sourceContext.checking.tr.map_wf hfamilyEntry
  have hout : outEnv.find? info.name = some (.inductInfo info) := by
    apply H.installed.preservesFind
    · rw [H.localExtends.env_eq]
      exact R.declared.context.checking.tr.map_wf
    · rw [H.localExtends.env_eq]
      exact R.declared.installed.preservesSourceFind
        Hheaders.context.checking.tr.map_wf hheader
  refine ⟨info, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [info, infos, AddInductive.inductiveTypeInfos] at hout ⊢
  exact hout

/-- The source-position header lookup also gives the executable index count.
It is stated separately from `findSourceHeaderAt`, whose metadata tuple it
extends. -/
theorem RecursorCheck.findSourceHeaderNumIndicesAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (hstats : familyIdx < stats.nindices.size)
    (info : InductiveVal)
    (hlookup : outEnv.find? indTypes[familyIdx].name =
      some (.inductInfo info)) :
    info.numIndices = stats.nindices[familyIdx] := by
  rcases Hheaders.sourceAligned with ⟨numNested, Haligned⟩
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, Hheaders.statsWF.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have hinfosSize : infos.size = indTypes.size := by
    simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hinfoIdx : familyIdx < infos.size := by
    simpa [hinfosSize] using hfamily
  let expected := infos[familyIdx]
  have hexpectedMem : expected ∈ infos.toList := by
    apply Array.mem_toList_iff.mpr
    simp [expected]
  rcases Haligned.findInfo hexpectedMem with ⟨_familyValue, hfamilyEntry⟩
  have hheader : headerEnv.find? expected.name =
      some (.inductInfo expected) :=
    Hheaders.installed.findEntry
      Hheaders.sourceContext.checking.tr.map_wf hfamilyEntry
  have hout : outEnv.find? expected.name = some (.inductInfo expected) := by
    apply H.installed.preservesFind
    · rw [H.localExtends.env_eq]
      exact R.declared.context.checking.tr.map_wf
    · rw [H.localExtends.env_eq]
      exact R.declared.installed.preservesSourceFind
        Hheaders.context.checking.tr.map_wf hheader
  have hexpectedName : expected.name = indTypes[familyIdx].name := by
    simp [expected, infos, AddInductive.inductiveTypeInfos]
  have hout' : outEnv.find? indTypes[familyIdx].name =
      some (.inductInfo expected) := by
    simpa [hexpectedName] using hout
  have hinfoEq : info = expected :=
    ConstantInfo.inductInfo.inj (Option.some.inj (hlookup.symm.trans hout'))
  subst info
  simp [expected, infos, AddInductive.inductiveTypeInfos]

/-- A restored-constructor step records the restored family header as owner, with the
header's `isUnsafe`, under the name the header lists. This follows from the installed
constructor metadata of the lowered run and the restoration equation, rather than from the
weaker translated-constant relation. -/
theorem RestoredInductiveStep.restoredConstructorOwnerUnsafeAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      stepSource stepTarget)
    (ctorIdx : Nat) (hctor : ctorIdx < Hstep.oldInfo.ctors.length)
    {ctorSource ctorTarget : Environment}
    (Hctor : RestoredConstructorStep result loweredEnv
      Hstep.oldInfo.ctors[ctorIdx] ctorSource ctorTarget) :
    Hctor.restored.newInfo.induct = Hstep.restored.header.newInfo.name ∧
      Hctor.restored.newInfo.isUnsafe = Hstep.restored.header.newInfo.isUnsafe ∧
      Hctor.restored.newInfo.name = Hstep.oldInfo.ctors[ctorIdx] := by
  rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _mappingState, target, _loweredState, _hparams, _hnodup,
      _hparamsSize, Hmapping, htarget⟩
  obtain ⟨hresultFamily, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hresultArray : familyIdx < result.types.toArray.size := by
    simpa using hresultFamily
  have htargetArrayEq : result.types.toArray[familyIdx] = target := by
    simpa using htargetEq
  rcases Hprod.findSourceHeaderAt familyIdx hresultArray with
    ⟨installedInfo, hinstalledLookup, hinstalledName, _hinstalledType,
      hinstalledCtors, _hinstalledAll, _hinstalledLevels,
      _hinstalledParams, _hinstalledUnsafe⟩
  have hinstalledLookup' : loweredEnv.find? target.name =
      some (.inductInfo installedInfo) := by
    simpa [htargetArrayEq] using hinstalledLookup
  have hinstalledName' : installedInfo.name = target.name := by
    simpa [htargetArrayEq] using hinstalledName
  have hinstalledCtors' : installedInfo.ctors =
      target.ctors.map (fun ctor => ctor.name) := by
    simpa [htargetArrayEq] using hinstalledCtors
  have hstepLookup : loweredEnv.find? target.name =
      some (.inductInfo Hstep.oldInfo) := by
    rw [Hmapping.name]
    exact Hstep.lookup
  have holdInfo : Hstep.oldInfo = installedInfo :=
    ConstantInfo.inductInfo.inj
      (Option.some.inj (hstepLookup.symm.trans hinstalledLookup'))
  have hfamilyCtor : ctorIdx < installedInfo.ctors.length := by
    simpa [holdInfo] using hctor
  have htargetCtor : ctorIdx < target.ctors.length := by
    rw [hinstalledCtors', List.length_map] at hfamilyCtor
    exact hfamilyCtor
  rcases R.installedConstructorCoherenceAt familyIdx hresultArray
      ctorIdx (by simpa [htargetArrayEq] using htargetCtor) with
    ⟨producerFamily, _hproducerCtor, hproducerName, _hproducerCtors,
      hproducerLookup, ⟨C⟩⟩
  have hproducerLookup' : loweredEnv.find? producerFamily.name =
      some (.inductInfo producerFamily) := by
    apply Hprod.installed.preservesFind
    · rw [Hprod.localExtends.env_eq]
      exact R.declared.context.checking.tr.map_wf
    · rw [Hprod.localExtends.env_eq]
      exact hproducerLookup
  have hproducerName' : producerFamily.name = target.name := by
    simpa [htargetArrayEq] using hproducerName
  have hproducerFamilyEq : producerFamily = installedInfo := by
    rw [hproducerName', hinstalledLookup'] at hproducerLookup'
    exact ConstantInfo.inductInfo.inj
      (Option.some.inj hproducerLookup').symm
  subst producerFamily
  have hClookup : loweredEnv.find? installedInfo.ctors[ctorIdx] =
      some (.ctorInfo C.info) := by
    apply Hprod.installed.preservesFind
    · rw [Hprod.localExtends.env_eq]
      exact R.declared.context.checking.tr.map_wf
    · rw [Hprod.localExtends.env_eq]
      exact C.lookup
  have hfoldName : Hstep.oldInfo.ctors[ctorIdx] =
      installedInfo.ctors[ctorIdx] := by
    have hget := congrArg
      (fun info : InductiveVal => info.ctors[ctorIdx]?) holdInfo
    simpa [hctor, hfamilyCtor] using hget
  have holdCtorInfo : Hctor.oldInfo = C.info := by
    have hoperational : loweredEnv.find? installedInfo.ctors[ctorIdx] =
        some (.ctorInfo Hctor.oldInfo) := by
      exact (congrArg (fun name => loweredEnv.find? name)
        hfoldName.symm).trans Hctor.lookup
    exact ConstantInfo.ctorInfo.inj
      (Option.some.inj (hoperational.symm.trans hClookup))
  have hCname : C.info.name = installedInfo.ctors[ctorIdx] := by
    have habstract : R.declared.context.venv.constants installedInfo.ctors[ctorIdx] =
        some C.constructorTarget := by
      rw [R.declared.contextVEnv, VEnv.addProjections_constants,
        VEnv.addEliminators_constants]
      exact C.constructorLookup
    exact (R.declared.context.checking.tr.find?_uniq C.lookup habstract).1
  refine ⟨?_, ?_, ?_⟩
  · calc
      Hctor.restored.newInfo.induct = Hctor.oldInfo.induct :=
        Hctor.restored.restoration.induct
      _ = C.info.induct := by rw [holdCtorInfo]
      _ = installedInfo.name := C.induct
      _ = Hstep.oldInfo.name := by rw [holdInfo]
      _ = Hstep.restored.header.newInfo.name := by
        simp [Hstep.restored.header.restored]
  · calc
      Hctor.restored.newInfo.isUnsafe = Hctor.oldInfo.isUnsafe :=
        Hctor.restored.restoration.isUnsafe
      _ = C.info.isUnsafe := by rw [holdCtorInfo]
      _ = installedInfo.isUnsafe := C.isUnsafe
      _ = Hstep.oldInfo.isUnsafe := by rw [holdInfo]
      _ = Hstep.restored.header.newInfo.isUnsafe := by
        simp [Hstep.restored.header.restored]
  · calc
      Hctor.restored.newInfo.name = Hctor.oldInfo.name :=
        Hctor.restored.restoration.name
      _ = C.info.name := by rw [holdCtorInfo]
      _ = installedInfo.ctors[ctorIdx] := hCname
      _ = Hstep.oldInfo.ctors[ctorIdx] := hfoldName.symm

/-- The owner half of `restoredConstructorOwnerUnsafeAt`. -/
theorem RestoredInductiveStep.restoredConstructorOwnerAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      stepSource stepTarget)
    (ctorIdx : Nat) (hctor : ctorIdx < Hstep.oldInfo.ctors.length)
    {ctorSource ctorTarget : Environment}
    (Hctor : RestoredConstructorStep result loweredEnv
      Hstep.oldInfo.ctors[ctorIdx] ctorSource ctorTarget) :
    Hctor.restored.newInfo.induct = Hstep.restored.header.newInfo.name :=
  (Hstep.restoredConstructorOwnerUnsafeAt Hlower Hprod hempty familyIdx hfamily
    ctorIdx hctor Hctor).1

/-- Restoring one source family preserves constructor-owner presence.  Old
constructors retain their source owners, while every newly restored
constructor is tied to its lowered constructor by
`restoredConstructorOwnerAt`. -/
theorem RestoredInductiveStep.constructorOwnersPresent
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      stepSource stepTarget)
    (hsourceWF : stepSource.constants.WF)
    (Howners : ConstructorOwnersPresent stepSource) :
    ConstructorOwnersPresent stepTarget := by
  intro name info hfind
  let header : ConstantInfo := .inductInfo Hstep.restored.header.newInfo
  have hheaderFresh : stepSource.find? header.name = none :=
    find?_none_of_contains_false hsourceWF Hstep.restored.header.fresh
  have hheaderEnv : Hstep.restored.headerEnv = stepSource.add header :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hsourceWF hheaderFresh
  obtain ⟨ctorEntries, HctorFresh⟩ :=
    Hstep.restored.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
    HctorFresh.targetWF hheaderWF
  let recursor : ConstantInfo :=
    .recInfo Hstep.restored.recursor.restored.newInfo
  have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hconstructorWF
      Hstep.restored.recursor.restored.fresh
  have htarget : stepTarget = Hstep.restored.constructorEnv.add recursor :=
    congrArg Prod.snd Hstep.restored.recursor.restored.output
  rw [htarget] at hfind
  rcases Environment.find?_freshAdd_cases hconstructorWF recursor hrecFresh
      hfind with hrec | hconstructor
  · rcases hrec with ⟨_name, hinfo⟩
    simp [recursor] at hinfo
  · rcases Hstep.restored.constructors.constructorFindCases hheaderWF
        hconstructor with hbefore | hrestored
    · rw [hheaderEnv] at hbefore
      rcases Environment.find?_freshAdd_cases hsourceWF header hheaderFresh
          hbefore with hnewHeader | hsource
      · rcases hnewHeader with ⟨_name, hinfo⟩
        simp [header] at hinfo
      · rcases Howners name info hsource with ⟨owner, howner, hrest⟩
        obtain ⟨entries, Hfresh⟩ := Hstep.restored.freshExtension hsourceWF
        exact ⟨owner, Hfresh.preservesSourceFind hsourceWF howner, hrest⟩
    · rcases hrestored with
        ⟨ctorIdx, hidx, ctorSource, ctorTarget, Hctor, hname, hinfo⟩
      subst info
      have ⟨howner, hunsafe, hctorName⟩ := Hstep.restoredConstructorOwnerUnsafeAt Hlower
        Hprod hempty familyIdx hfamily ctorIdx hidx Hctor
      refine ⟨Hstep.restored.header.newInfo, ?_, ?_, hunsafe⟩
      · rw [howner]
        exact Hstep.restored.headerFind hsourceWF
      · rw [hname, hctorName, Hstep.restored.header.restored]
        exact List.getElem_mem hidx

/-- Alignment of one restored source family with the source declaration
(`InductInfoAlignment`). -/
theorem RestoredInductiveStep.inductInfoAlignmentAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv auxRec
      (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
      stepSource stepTarget)
    (hstepWF : stepSource.constants.WF) :
    InductInfoAlignment stepTarget.constants sourceDecl familyIdx
      Hstep.restored.header.newInfo := by
  rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨fvars, _mappingState, target, _loweredState, hparams, hnodup,
      hparamsSize, Hmapping, htarget⟩
  obtain ⟨hresultFamily, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hresultArray : familyIdx < result.types.toArray.size := by
    simpa using hresultFamily
  have htargetArrayEq : result.types.toArray[familyIdx] = target := by
    simpa using htargetEq
  have htargetMem : target ∈ result.types.toArray.toList := by
    rw [← htargetArrayEq]
    simp
  rcases Hprod.findSourceHeaderAt familyIdx hresultArray with
    ⟨installedInfo, hinstalledLookup, hinstalledName, hinstalledType,
      hinstalledCtors, hinstalledAll, hinstalledLevels, hinstalledParams,
      hinstalledUnsafe⟩
  have hinstalledLookup' : loweredEnv.find? target.name =
      some (.inductInfo installedInfo) := by
    simpa [htargetArrayEq] using hinstalledLookup
  have hinstalledName' : installedInfo.name = target.name := by
    simpa [htargetArrayEq] using hinstalledName
  have hinstalledCtors' : installedInfo.ctors =
      target.ctors.map (fun ctor => ctor.name) := by
    simpa [htargetArrayEq] using hinstalledCtors
  have hstepLookup : loweredEnv.find? target.name =
      some (.inductInfo Hstep.oldInfo) := by
    rw [Hmapping.name]
    exact Hstep.lookup
  have holdInfo : Hstep.oldInfo = installedInfo :=
    ConstantInfo.inductInfo.inj
      (Option.some.inj (hstepLookup.symm.trans hinstalledLookup'))
  have hsourceDecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have HsourceType :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource familyIdx
      hfamily hsourceDecl
  have hloweredDecl : familyIdx < loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    exact hresultFamily
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := Hlower.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases Hlower with ⟨finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors :
      RestoreAuxConstructorsFresh result loweredEnv envTypes :=
    Hlower.restoreAuxConstructorsFreshAtTypes Hc Hprod Hsource Howners hempty
  have hresultNParams : result.nparams = nparams :=
    Hlower.resultParamsSize.symm.trans hparamsSize
  have hstatsParams : stats.params.size = nparams := by
    have hlength := Lean4Lean.List.Forall₂.length_eq
      Hheaders.statsWF.params
    simpa [VInductDecl.paramVars, R.core.nparams] using hlength
  have hheaderFresh : stepSource.find?
      (ConstantInfo.inductInfo Hstep.restored.header.newInfo).name = none :=
    find?_none_of_contains_false hstepWF Hstep.restored.header.fresh
  have hheaderEnv : Hstep.restored.headerEnv = stepSource.add
      (.inductInfo Hstep.restored.header.newInfo) :=
    congrArg Prod.snd Hstep.restored.header.output
  have hheaderWF : Hstep.restored.headerEnv.constants.WF :=
    hheaderEnv.symm ▸ constantsWF_add_checked hstepWF hheaderFresh
  obtain ⟨ctorEntries, HctorFresh⟩ :=
    Hstep.restored.constructors.constructorFreshExtension hheaderWF
  have hconstructorWF : Hstep.restored.constructorEnv.constants.WF :=
    HctorFresh.targetWF hheaderWF
  obtain ⟨stepEntries, HstepFresh⟩ := Hstep.restored.freshExtension hstepWF
  have hstepTargetWF := HstepFresh.targetWF hstepWF
  have hheaderMap : stepTarget.constants.find?
      Hstep.restored.header.newInfo.name =
      some (.inductInfo Hstep.restored.header.newInfo) :=
    Environment.mapFind_of_find hstepTargetWF
      (Hstep.restored.headerFind hstepWF)
  have hstats : familyIdx < stats.nindices.size := by
    rw [Array.size_eq_length_toList,
      Hheaders.statsWF.indices, List.length_map]
    exact hloweredDecl
  refine {
    familyIdx_lt := hsourceDecl
    name := ?_
    lookup := hheaderMap
    all := ?_
    levelParams := ?_
    numParams := ?_
    numIndices := ?_
    constructors := ?_
    isUnsafe := ?_
    constructor := ?_ }
  · calc
      Hstep.restored.header.newInfo.name = Hstep.oldInfo.name := by
        simp [Hstep.restored.header.restored]
      _ = installedInfo.name :=
        congrArg (fun info : InductiveVal => info.name) holdInfo
      _ = target.name := hinstalledName'
      _ = sourceTypes[familyIdx].name := Hmapping.name
      _ = sourceDecl.types[familyIdx].name := HsourceType.header.name.symm
  · calc
      Hstep.restored.header.newInfo.all =
          sourceTypes.map (fun type => type.name) := by
        simp [Hstep.restored.header.restored]
      _ = sourceDecl.types.map (fun type => type.name) := by
        apply List.ext_getElem
        · simpa using
            Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource
        · intro i hiSource hiDecl
          simp only [List.getElem_map]
          exact (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource i
            (by simpa using hiSource) (by simpa using hiDecl)).header.name.symm
  · calc
      Hstep.restored.header.newInfo.levelParams.length =
          Hstep.oldInfo.levelParams.length := by
        simp [Hstep.restored.header.restored]
      _ = installedInfo.levelParams.length := by rw [holdInfo]
      _ = c.lparams.length := congrArg List.length hinstalledLevels
      _ = sourceDecl.uvars := Hsource.uvars.symm
  · calc
      Hstep.restored.header.newInfo.numParams = Hstep.oldInfo.numParams := by
        simp [Hstep.restored.header.restored]
      _ = installedInfo.numParams := by rw [holdInfo]
      _ = nparams := hinstalledParams
      _ = sourceDecl.nparams := Hsource.nparams.symm
  · calc
      Hstep.restored.header.newInfo.numIndices =
          Hstep.oldInfo.numIndices := by
        simp [Hstep.restored.header.restored]
      _ = installedInfo.numIndices := by rw [holdInfo]
      _ = stats.nindices[familyIdx] :=
        Hprod.findSourceHeaderNumIndicesAt familyIdx hresultArray hstats
          installedInfo (by simpa [htargetArrayEq] using hinstalledLookup)
      _ = loweredDecl.types[familyIdx].numIndices := by
        have hindex : stats.nindices[familyIdx]? =
            some loweredDecl.types[familyIdx].numIndices := by
          rw [← Array.getElem?_toList,
            Hheaders.statsWF.indices]
          simp [hloweredDecl]
        simpa [Array.getElem?_eq_getElem hstats] using hindex
      _ = sourceDecl.types[familyIdx].numIndices :=
        (Hmetadata.numIndices hdeclLength familyIdx hsourceDecl
          hloweredDecl).symm
  · calc
      Hstep.restored.header.newInfo.ctors.length =
          Hstep.oldInfo.ctors.length := by
        simp [Hstep.restored.header.restored]
      _ = installedInfo.ctors.length := by rw [holdInfo]
      _ = target.ctors.length := by simp [hinstalledCtors']
      _ = sourceTypes[familyIdx].ctors.length := Hmapping.constructors.length
      _ = sourceDecl.types[familyIdx].ctors.length :=
        Lean4Lean.VerifyInductive.TrInductiveType.ctors_length HsourceType
  · calc
      Hstep.restored.header.newInfo.isUnsafe = Hstep.oldInfo.isUnsafe := by
        simp [Hstep.restored.header.restored]
      _ = installedInfo.isUnsafe := by rw [holdInfo]
      _ = isUnsafe := hinstalledUnsafe
      _ = sourceDecl.isUnsafe := Hsource.isUnsafe.symm
  · intro ctorIdx hsourceCtorDecl
    have hsourceCtor : ctorIdx < sourceTypes[familyIdx].ctors.length := by
      rw [Lean4Lean.VerifyInductive.TrInductiveType.ctors_length HsourceType]
      exact hsourceCtorDecl
    have htargetCtor : ctorIdx < target.ctors.length := by
      rw [Hmapping.constructors.length]
      exact hsourceCtor
    rcases Hmapping.constructors.mappingAt ctorIdx hsourceCtor with
      ⟨sourceCtor, targetCtor, _before, _after, hsourceCtorEq,
        htargetCtorEq, HctorMapping⟩
    obtain ⟨_, hsourceCtorVal⟩ :=
      _root_.getElem?_eq_some_iff.mp hsourceCtorEq
    obtain ⟨_, htargetCtorVal⟩ :=
      _root_.getElem?_eq_some_iff.mp htargetCtorEq
    have hctorNames : Hstep.oldInfo.ctors =
        target.ctors.map (fun ctor => ctor.name) := by
      calc
        Hstep.oldInfo.ctors = installedInfo.ctors :=
          congrArg InductiveVal.ctors holdInfo
        _ = target.ctors.map (fun ctor => ctor.name) := hinstalledCtors'
    have htraceName : ctorIdx < Hstep.oldInfo.ctors.length := by
      rw [hctorNames, List.length_map]
      exact htargetCtor
    rcases Hstep.restored.constructors.constructorKernelOriginAt
        hheaderWF ctorIdx htraceName with
      ⟨ctorSource, ctorTarget, oldCtorInfo, newCtorInfo, HctorStep,
        holdCtor, hnewCtor, HctorRestore, hctorFind⟩
    have hfamilyCtor : ctorIdx < installedInfo.ctors.length := by
      rw [hinstalledCtors', List.length_map]
      exact htargetCtor
    rcases R.installedConstructorCoherenceAt familyIdx hresultArray
        ctorIdx (by simpa [htargetArrayEq] using htargetCtor) with
      ⟨producerFamily, hproducerCtor, hproducerName, hproducerCtors,
        hproducerLookup, ⟨C⟩⟩
    have hproducerLookup' : loweredEnv.find? producerFamily.name =
        some (.inductInfo producerFamily) := by
      apply Hprod.installed.preservesFind
      · rw [Hprod.localExtends.env_eq]
        exact R.declared.context.checking.tr.map_wf
      · rw [Hprod.localExtends.env_eq]
        exact hproducerLookup
    have hproducerName' : producerFamily.name = target.name := by
      simpa [htargetArrayEq] using hproducerName
    have hproducerFamilyEq : producerFamily = installedInfo := by
      rw [hproducerName', hinstalledLookup'] at hproducerLookup'
      exact ConstantInfo.inductInfo.inj
        (Option.some.inj hproducerLookup').symm
    subst producerFamily
    have hClookup : loweredEnv.find? installedInfo.ctors[ctorIdx] =
        some (.ctorInfo C.info) := by
      apply Hprod.installed.preservesFind
      · rw [Hprod.localExtends.env_eq]
        exact R.declared.context.checking.tr.map_wf
      · rw [Hprod.localExtends.env_eq]
        exact C.lookup
    have hfoldName : Hstep.oldInfo.ctors[ctorIdx] =
        installedInfo.ctors[ctorIdx] := by
      have hget := congrArg
        (fun info : InductiveVal => info.ctors[ctorIdx]?) holdInfo
      simpa [htraceName, hfamilyCtor] using hget
    have holdCtorInfo : oldCtorInfo = C.info := by
      have hoperational := HctorStep.lookup
      rw [holdCtor, hfoldName] at hoperational
      exact ConstantInfo.ctorInfo.inj
        (Option.some.inj (hoperational.symm.trans hClookup))
    have hmetadata := HctorStep.metadataOfInstalled Hprod htargetMem
      (by simpa [htargetCtorVal] using List.getElem_mem htargetCtor)
      (by simp [hctorNames, htargetCtorVal])
    have hnewName : newCtorInfo.name = targetCtor.name := by
      calc
        newCtorInfo.name = oldCtorInfo.name := HctorRestore.name
        _ = HctorStep.oldInfo.name := by rw [holdCtor]
        _ = targetCtor.name := hmetadata.2.2.1
    have HsourceCtor :=
      Lean4Lean.VerifyInductive.TrInductiveType.ctorAt HsourceType ctorIdx
        hsourceCtor hsourceCtorDecl
    have HsourceSyntax : SourceConstructorSyntax sourceCtor := by
      have HsourceSyntaxAt :=
        (Hsources.getElem familyIdx hfamily).constructors.getElem ctorIdx
          hsourceCtor
      simpa [hsourceCtorVal] using HsourceSyntaxAt
    have HsourceClosed : sourceCtor.type.FVarsIn fun _ => False :=
      HsourceSyntax.closed
    have HsourceBVar : Closed sourceCtor.type := by
      have h := HsourceCtor.type.closed
      simpa [VLCtx.bvars, hsourceCtorVal] using h
    have HsourceDisjoint :
        RestoreSourceDisjoint result loweredEnv sourceCtor.type :=
      HsourceSyntax.noNestedAux.restoreSourceDisjointOfFresh
        (by simpa [hsourceCtorVal] using HsourceCtor.type.constantsDefined)
        Hfamilies Hconstructors
    have holdType : oldCtorInfo.type = targetCtor.type := by
      simpa [holdCtor] using HctorStep.oldType_eq_ofInstalled Hprod htargetMem
        (by simpa [htargetCtorVal] using List.getElem_mem htargetCtor) (by
          simp [hctorNames, htargetCtorVal])
    rcases HctorMapping.constructorRestoration_inverse rfl fvars hparams
        hnodup HsourceClosed HsourceBVar hparamsSize loweredEnv HsourceDisjoint
        hresultNParams HctorRestore holdType with ⟨Hinverse⟩
    have hrestoredArity :
        AddInductive.constructorArity newCtorInfo.type =
          AddInductive.constructorArity sourceCtor.type :=
      Lean4Lean.AddInductive.constructorArity_eqv Hinverse.restoredType_eqv_source
    have harityMapping :
        AddInductive.constructorArity targetCtor.type =
          AddInductive.constructorArity sourceCtor.type :=
      HctorMapping.constructorArity_eq HsourceClosed HsourceBVar
    have habstractName : newCtorInfo.name =
        sourceDecl.types[familyIdx].ctors[ctorIdx].name := by
      calc
        newCtorInfo.name = targetCtor.name := hnewName
        _ = sourceCtor.name := HctorMapping.name
        _ = sourceTypes[familyIdx].ctors[ctorIdx].name := by
          rw [hsourceCtorVal]
        _ = sourceDecl.types[familyIdx].ctors[ctorIdx].name :=
          HsourceCtor.name.symm
    let recursor : ConstantInfo :=
      .recInfo Hstep.restored.recursor.restored.newInfo
    have hrecFresh : Hstep.restored.constructorEnv.find? recursor.name =
        none := find?_none_of_contains_false hconstructorWF
          Hstep.restored.recursor.restored.fresh
    have htargetEnv : stepTarget =
        Hstep.restored.constructorEnv.add recursor :=
      congrArg Prod.snd Hstep.restored.recursor.restored.output
    have hctorFinalFind : stepTarget.find? newCtorInfo.name =
        some (.ctorInfo newCtorInfo) := by
      rw [htargetEnv]
      exact Environment.find?_freshAdd_preserves hconstructorWF recursor
        hrecFresh hctorFind
    have hnewFamilyCtors : Hstep.restored.header.newInfo.ctors =
        target.ctors.map (fun ctor => ctor.name) := by
      calc
        Hstep.restored.header.newInfo.ctors = Hstep.oldInfo.ctors := by
          simp [Hstep.restored.header.restored]
        _ = target.ctors.map (fun ctor => ctor.name) := hctorNames
    have hnewFamilyCtor : ctorIdx <
        Hstep.restored.header.newInfo.ctors.length := by
      simpa [Hstep.restored.header.restored] using htraceName
    have hnewCtorKey : Hstep.restored.header.newInfo.ctors[ctorIdx] =
        targetCtor.name := by
      have hget := congrArg (fun names : List Name => names[ctorIdx]?)
        hnewFamilyCtors
      simpa [hnewFamilyCtor, htargetCtor, htargetCtorVal] using hget
    let expectedInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
      target ctorIdx targetCtor
    rcases R.declared.sourceAligned.findAt htargetMem ctorIdx htargetCtor with
      ⟨expectedValue, hexpectedEntry⟩
    have hexpectedLookup : loweredEnv.find? expectedInfo.name =
        some (.ctorInfo expectedInfo) := by
      simpa [expectedInfo, htargetCtorVal, ConstantInfo.name,
        ConstantInfo.toConstantVal] using
        Hprod.findConstructorOfMem hexpectedEntry
    have hinstalledCtorKey : installedInfo.ctors[ctorIdx] = targetCtor.name := by
      have hget := congrArg (fun names : List Name => names[ctorIdx]?)
        hinstalledCtors'
      simpa [hfamilyCtor, htargetCtor, htargetCtorVal] using hget
    have hCExpected : C.info = expectedInfo := by
      have hexpectedLookup' : loweredEnv.find? installedInfo.ctors[ctorIdx] =
          some (.ctorInfo expectedInfo) := by
        simpa [expectedInfo, AddInductive.constructorInfo,
          hinstalledCtorKey] using hexpectedLookup
      exact ConstantInfo.ctorInfo.inj
        (Option.some.inj (hClookup.symm.trans hexpectedLookup'))
    refine ⟨{
      familyIdx_lt := hsourceDecl
      ctorIdx_lt := hsourceCtorDecl
      familyInfo_ctorIdx_lt := ?_
      info := newCtorInfo
      name := ?_
      lookup := ?_
      induct := ?_
      cidx := ?_
      numParams := ?_
      numFields := ?_
      numFields_forallArity := ?_
      levelParamsExact := ?_
      levelParams := ?_
      isUnsafe := ?_ }⟩
    · exact hnewFamilyCtor
    · calc
        Hstep.restored.header.newInfo.ctors[ctorIdx] = targetCtor.name :=
          hnewCtorKey
        _ = newCtorInfo.name := hnewName.symm
        _ = sourceDecl.types[familyIdx].ctors[ctorIdx].name := habstractName
    · rw [hnewCtorKey, ← hnewName]
      exact Environment.mapFind_of_find hstepTargetWF hctorFinalFind
    · calc
        newCtorInfo.induct = oldCtorInfo.induct := HctorRestore.induct
        _ = C.info.induct := by rw [holdCtorInfo]
        _ = installedInfo.name := C.induct
        _ = Hstep.oldInfo.name := by rw [holdInfo]
        _ = Hstep.restored.header.newInfo.name := by
          simp [Hstep.restored.header.restored]
    · exact HctorRestore.cidx.trans (holdCtorInfo ▸ C.cidx)
    · calc
        newCtorInfo.numParams = oldCtorInfo.numParams := HctorRestore.numParams
        _ = C.info.numParams := by rw [holdCtorInfo]
        _ = installedInfo.numParams := C.numParams
        _ = nparams := hinstalledParams
        _ = sourceDecl.nparams := Hsource.nparams.symm
    · calc
        newCtorInfo.numFields = oldCtorInfo.numFields := HctorRestore.numFields
        _ = C.info.numFields := by rw [holdCtorInfo]
        _ = expectedInfo.numFields := congrArg ConstructorVal.numFields hCExpected
        _ = AddInductive.constructorArity targetCtor.type -
              stats.params.size := by
          exact AddInductive.constructorInfo_numFields stats c.lparams
            isUnsafe target ctorIdx targetCtor
        _ = AddInductive.constructorArity sourceCtor.type - nparams := by
          rw [harityMapping, hstatsParams]
        _ = AddInductive.constructorArity newCtorInfo.type -
              sourceDecl.nparams := by
          rw [hrestoredArity, Hsource.nparams]
    · have hspineAt := R.parameterPrefixes.spines familyIdx hresultArray ctorIdx
      have HloweredType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
        R.core familyIdx (by simpa using hresultArray) hloweredDecl
      have hnumFields : newCtorInfo.numFields =
          AddInductive.constructorArity targetCtor.type - stats.params.size := by
        calc
          newCtorInfo.numFields = oldCtorInfo.numFields := HctorRestore.numFields
          _ = C.info.numFields := by rw [holdCtorInfo]
          _ = expectedInfo.numFields :=
            congrArg ConstructorVal.numFields hCExpected
          _ = AddInductive.constructorArity targetCtor.type -
                stats.params.size :=
            AddInductive.constructorInfo_numFields stats c.lparams
              isUnsafe target ctorIdx targetCtor
      rw [hnumFields, hstatsParams, ← Hsource.nparams]
      clear hnumFields
      subst htargetArrayEq
      rcases hspineAt htargetCtor with ⟨k, hspine⟩
      have hloweredCtor : ctorIdx < loweredDecl.types[familyIdx].ctors.length := by
        rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length HloweredType]
        simpa using htargetCtor
      have HloweredCtor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt
        HloweredType ctorIdx (by simpa using htargetCtor) hloweredCtor
      have HloweredCtorType : TrExprS Hheaders.context.venv c.lparams []
          (result.types.toArray[familyIdx].ctors[ctorIdx]).type
          (loweredDecl.types[familyIdx].ctors[ctorIdx]).type := by
        simpa using HloweredCtor.type
      have hloweredArity :
          (loweredDecl.types[familyIdx].ctors[ctorIdx]).type.forallArity = k :=
        checkPositivityStep.TrExprS.forallArity_of_spine hspine HloweredCtorType
      have htargetArity : AddInductive.constructorArity targetCtor.type = k := by
        rw [← htargetCtorVal]
        exact hspine.constructorArity
      rw [htargetArity, Harity familyIdx hsourceDecl hloweredDecl ctorIdx
        hsourceCtorDecl hloweredCtor, hloweredArity]
    · calc
        newCtorInfo.levelParams = oldCtorInfo.levelParams :=
          HctorRestore.levelParams
        _ = C.info.levelParams := by rw [holdCtorInfo]
        _ = installedInfo.levelParams := C.levelParams
        _ = Hstep.oldInfo.levelParams := by rw [holdInfo]
        _ = Hstep.restored.header.newInfo.levelParams := by
          simp [Hstep.restored.header.restored]
    · calc
        newCtorInfo.levelParams.length = oldCtorInfo.levelParams.length :=
          congrArg List.length HctorRestore.levelParams
        _ = C.info.levelParams.length := by rw [holdCtorInfo]
        _ = installedInfo.levelParams.length :=
          congrArg List.length C.levelParams
        _ = c.lparams.length := congrArg List.length hinstalledLevels
        _ = sourceDecl.uvars := Hsource.uvars.symm
    · calc
        newCtorInfo.isUnsafe = oldCtorInfo.isUnsafe := HctorRestore.isUnsafe
        _ = C.info.isUnsafe := by rw [holdCtorInfo]
        _ = installedInfo.isUnsafe := C.isUnsafe
        _ = isUnsafe := hinstalledUnsafe
        _ = sourceDecl.isUnsafe := Hsource.isUnsafe.symm

/-- Auxiliary recursor restoration adds no constructors and therefore
preserves constructor-owner presence. -/
theorem FoldSteps.recursorConstructorOwnersPresent
    (Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceEnv) :
    ConstructorOwnersPresent targetEnv := by
  induction Htrace with
  | nil => exact Howners
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
      have hfresh : stepSource.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have hmiddle : middle = stepSource.add ci :=
        congrArg Prod.snd Hstep.restored.output
      have hmiddleWF : middle.constants.WF :=
        hmiddle.symm ▸ constantsWF_add_checked hsourceWF hfresh
      apply ih hmiddleWF
      rw [hmiddle]
      exact Howners.addNonConstructor hsourceWF hfresh (by
        intro info hinfo
        simp [ci] at hinfo)

/-- Indexed fold of per-family owner preservation over a suffix of the
source mutual family list. -/
theorem FoldSteps.sourceFamiliesConstructorOwnersPresent
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      remaining sourceEnv targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hsourceWF : sourceEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceEnv) :
    ConstructorOwnersPresent targetEnv := by
  induction Htrace generalizing processed with
  | nil => exact Howners
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let familyIdx := processed.length
      have hfamily : familyIdx < sourceTypes.length := by
        simp [familyIdx, hsplit]
      have hfamilyEq : sourceTypes[familyIdx] = head := by
        simp [familyIdx, hsplit]
      have Hstep' : RestoredInductiveStep result loweredEnv auxRec
          (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
          stepSource middle := by
        simpa [hfamilyEq] using Hstep
      have Hnext := Hstep'.constructorOwnersPresent Hlower Hprod hempty
        familyIdx hfamily hsourceWF Howners
      obtain ⟨entries, Hfresh⟩ := Hstep'.restored.freshExtension hsourceWF
      have hmiddleWF : middle.constants.WF := Hfresh.targetWF hsourceWF
      apply ih (processed := processed ++ [head])
        (hsplit := by simpa [List.append_assoc] using hsplit)
        hmiddleWF Hnext

/-- Nested restoration preserves constructor-owner presence through the source
family fold and the auxiliary recursor fold. -/
theorem NestedRestorationFolds.constructorOwnersPresent
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      out)
    (Howners : ConstructorOwnersPresent c.env) :
    ConstructorOwnersPresent out.2 := by
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have Hprimary : ConstructorOwnersPresent Hrestored.sourceFamiliesEnv := by
    apply Hrestored.inductives.sourceFamiliesConstructorOwnersPresent
      Hlower Hprod hempty [] (by simp) hsourceWF Howners
  obtain ⟨primaryEntries, HprimaryFresh⟩ :=
    Hrestored.inductives.inductiveFreshExtension hsourceWF
  have hprimaryWF : Hrestored.sourceFamiliesEnv.constants.WF :=
    HprimaryFresh.targetWF hsourceWF
  exact Hrestored.auxiliaries.recursorConstructorOwnersPresent
    hprimaryWF Hprimary

/-- Indexed fold of the pointwise source-family alignment over an exact
suffix of the source mutual family list. -/
theorem FoldSteps.sourceFamiliesInductInfosFromDecl
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      remaining sourceEnv targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hsourceWF : sourceEnv.constants.WF)
    (Horigins : InductInfosFromDecl c.env.constants
      sourceEnv.constants sourceDecl) :
    InductInfosFromDecl c.env.constants targetEnv.constants
      sourceDecl := by
  induction Htrace generalizing processed with
  | nil => exact Horigins
  | @cons head stepSource middle tail target Hstep Htail ih =>
      let familyIdx := processed.length
      have hfamily : familyIdx < sourceTypes.length := by
        simp [familyIdx, hsplit]
      have hfamilyEq : sourceTypes[familyIdx] = head := by
        simp [familyIdx, hsplit]
      have Hstep' : RestoredInductiveStep result loweredEnv auxRec
          (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
          stepSource middle := by
        simpa [hfamilyEq] using Hstep
      have Halign := Hstep'.inductInfoAlignmentAt Hlower Hc Hprod
        Hsource Hmetadata Hsources Harity Howners hempty familyIdx hfamily
        hsourceWF
      have Hnext := Hstep'.restored.extendInductInfosFromDecl
        hsourceWF Horigins Halign
      obtain ⟨entries, Hfresh⟩ := Hstep'.restored.freshExtension hsourceWF
      have hmiddleWF : middle.constants.WF := Hfresh.targetWF hsourceWF
      apply ih (processed := processed ++ [head])
        (hsplit := by simpa [List.append_assoc] using hsplit)
        hmiddleWF Hnext

/-- Every family of the source declaration is a restored kernel header, fresh in the
environment the restoration starts from: the positional cover of the source-family fold. -/
theorem FoldSteps.sourceFamiliesCover
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)))
      remaining sourceEnv targetEnv)
    (processed : List InductiveType)
    (hsplit : sourceTypes = processed ++ remaining)
    (hsourceWF : sourceEnv.constants.WF)
    (hbase : ∀ {n ci}, c.env.find? n = some ci → sourceEnv.find? n = some ci)
    (Hdone : ∀ i (hi : i < sourceDecl.types.length), i < processed.length →
      ∃ v, sourceEnv.find? sourceDecl.types[i].name = some (.inductInfo v) ∧
        c.env.find? sourceDecl.types[i].name = none) :
    ∀ i (hi : i < sourceDecl.types.length),
      ∃ v, targetEnv.find? sourceDecl.types[i].name = some (.inductInfo v) ∧
        c.env.find? sourceDecl.types[i].name = none := by
  induction Htrace generalizing processed with
  | nil =>
    intro i hi
    apply Hdone i hi
    have := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource
    rw [hsplit, List.append_nil] at this
    omega
  | @cons head stepSource middle tail target Hstep Htail ih =>
    let familyIdx := processed.length
    have hfamily : familyIdx < sourceTypes.length := by
      simp [familyIdx, hsplit]
    have hfamilyEq : sourceTypes[familyIdx] = head := by
      simp [familyIdx, hsplit]
    have Hstep' : RestoredInductiveStep result loweredEnv auxRec
        (sourceTypes.map (fun type => type.name)) sourceTypes[familyIdx]
        stepSource middle := by
      simpa [hfamilyEq] using Hstep
    have Halign := Hstep'.inductInfoAlignmentAt Hlower Hc Hprod
      Hsource Hmetadata Hsources Harity Howners hempty familyIdx hfamily
      hsourceWF
    obtain ⟨entries, Hfresh⟩ := Hstep'.restored.freshExtension hsourceWF
    have hmiddleWF : middle.constants.WF := Hfresh.targetWF hsourceWF
    have hheaderFresh : stepSource.find? Hstep'.restored.header.newInfo.name = none :=
      find?_none_of_contains_false hsourceWF Hstep'.restored.header.fresh
    have hheaderFind := Hstep'.restored.headerFind hsourceWF
    apply ih (processed := processed ++ [head])
      (hsplit := by simpa [List.append_assoc] using hsplit) hmiddleWF
      (fun h => Hfresh.preservesSourceFind hsourceWF (hbase h))
    intro i hi hlt
    rw [List.length_append, List.length_singleton] at hlt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
    · obtain ⟨v, hv, hnone⟩ := Hdone i hi hlt
      exact ⟨v, Hfresh.preservesSourceFind hsourceWF hv, hnone⟩
    · subst heq
      have hname : Hstep'.restored.header.newInfo.name =
          sourceDecl.types[processed.length].name := Halign.name
      refine ⟨Hstep'.restored.header.newInfo, by rw [← hname]; exact hheaderFind, ?_⟩
      cases h : c.env.find? sourceDecl.types[processed.length].name with
      | none => rfl
      | some ci =>
        have := hbase h
        rw [← hname, hheaderFresh] at this
        cases this

/-- Every family of the source declaration is a restored kernel header of the environment
the restoration folds produce, fresh in the environment they start from. -/
theorem NestedRestorationFolds.cover
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      ((), outEnv)) :
    ∀ T ∈ sourceDecl.types, ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧
      c.env.find? T.name = none := by
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have Hprimary := FoldSteps.sourceFamiliesCover Hlower Hc Hprod Hsource Hmetadata
    Hsources Harity Howners hempty Hrestored.inductives [] (by simp) hsourceWF id
    (fun _ _ h => by simp at h)
  obtain ⟨primaryEntries, HprimaryFresh⟩ :=
    Hrestored.inductives.inductiveFreshExtension hsourceWF
  have hprimaryWF := HprimaryFresh.targetWF hsourceWF
  obtain ⟨auxiliaryEntries, HauxiliaryFresh⟩ :=
    Hrestored.auxiliaries.recursorFreshExtension hprimaryWF
  intro T hT
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
  obtain ⟨v, hv, hnone⟩ := Hprimary i hi
  exact ⟨v, HauxiliaryFresh.preservesSourceFind hprimaryWF hv, hnone⟩

/-- After the nested restoration folds, every visible inductive family is a base
constant or a family of the source declaration (`InductInfosFromDecl`). Source
families are installed positionally; auxiliary restoration adds recursors only. -/
theorem NestedRestorationFolds.inductInfosFromDecl
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat}
    {isUnsafe : Bool} {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv c.env
      auxRec (sourceTypes.map (fun type => type.name)) sourceTypes auxRecNames
      out) :
    InductInfosFromDecl c.env.constants out.2.constants sourceDecl := by
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have Hinitial : InductInfosFromDecl c.env.constants c.env.constants
      sourceDecl := by
    intro familyName familyInfo hfind
    exact .inl hfind
  have Hprimary : InductInfosFromDecl c.env.constants
      Hrestored.sourceFamiliesEnv.constants sourceDecl := by
    apply Hrestored.inductives.sourceFamiliesInductInfosFromDecl
      Hlower Hc Hprod Hsource Hmetadata Hsources Harity Howners hempty []
        (by simp) hsourceWF Hinitial
  obtain ⟨entries, Hfresh⟩ :=
    Hrestored.inductives.inductiveFreshExtension hsourceWF
  exact Hrestored.auxiliaries.recursorPreservesInductInfosFromDecl
    (Hfresh.targetWF hsourceWF) Hprimary

end VerifyInductive
end Lean4Lean
