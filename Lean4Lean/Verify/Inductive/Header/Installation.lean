import Lean4Lean.Verify.Inductive.Header.Check
import Lean4Lean.Verify.Inductive.Recursor.Entries.AddConstants

/-!
# Installation of the headers

Verifies `AddInductive.declareInductiveTypes`, which adds the family constants: the
executable environment is related by `AddConstants` to the abstract header environment
`addConstVals (headerDecl isUnsafe).typeConstants`, with freshness read off the executable's
`checkName` (`InstalledHeaders`, `declareInductiveTypes.headersWF`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Existential form of the atomic mutual-header installer.  Freshness is
recovered from each successful executable `checkName`, so the abstract
`addConstVals` equation is an output rather than a premise. -/
theorem AddConstants.ofDeclareInductiveTypeInfosExists
    (Hvalid : CheckingEnv safety env venv)
    (Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal safety sourceEnv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF sourceEnv)
      infos values)
    (hle : sourceEnv ≤ venv)
    (hnprim : allowPrimitive = true → ∀ info ∈ infos,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypeInfos allowPrimitive infos env).WF
      fun outEnv => ∃ outVEnv,
        AddConstants safety env venv
          (List.zip (infos.map (fun info => .inductInfo info)) values)
          outEnv outVEnv := by
  induction Hentries generalizing env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, .nil⟩
  | @cons info ci' infos values Hentry _ ih =>
    rw [AddInductive.declareInductiveTypeInfos]
    exact (checkName.WF Hvalid.map_wf info.name allowPrimitive).bind
      fun _ hchecked => by
        have hnprimHead :
            ¬ Kernel.Environment.primitives.contains info.name := by
          intro hp
          have hallowed := hchecked.2 hp
          cases hallow : allowPrimitive with
          | false => simp [hallow] at hallowed
          | true => exact hnprim hallow info (by simp) hp
        have hnprimTail : allowPrimitive = true → ∀ info ∈ infos,
            ¬ Kernel.Environment.primitives.contains info.name := by
          intro hallow info hinfo
          exact hnprim hallow info (by simp [hinfo])
        have hn : env.find? info.name = none := hchecked.1
        rcases CheckingEnv.exists_addConst Hvalid hn
            ci'.toVConstant with ⟨nextVEnv, haddRaw⟩
        have htr : TrConstVal safety venv (.inductInfo info) ci' :=
          Hentry.1.mono hle
        have hwf : ci'.toVConstant.WF venv := Hentry.2.mono hle
        have hname : info.name = ci'.name := Hentry.1.2
        have hadd : venv.addConst info.name ci'.toVConstant =
            some nextVEnv := by
          simpa [hname] using haddRaw
        have HnextValid : CheckingEnv safety
            (env.add (.inductInfo info)) nextVEnv :=
          Hvalid.add (ci := .inductInfo info) hn htr.1 hwf hadd rfl
        have hnextLe : sourceEnv ≤ nextVEnv :=
          hle.trans (VEnv.addConst_le hadd)
        exact (ih HnextValid hnextLe hnprimTail).mono
          fun outEnv Hrest => by
            rcases Hrest with ⟨outVEnv, Htail⟩
            exact ⟨outVEnv, by
              simpa using AddConstants.cons (ci := .inductInfo info)
                (ci' := ci') hn hnprimHead htr hwf hadd rfl Htail⟩

/-- The constructor names of a declaration are absent from an environment. -/
def ConstructorNamesAbsent (indTypes : Array InductiveType) (env : Environment) : Prop :=
  ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors, env.find? ctor.name = none

/-- The constructor fold of `declareConstructors` succeeds only on names absent from every
environment it extends. -/
theorem AddInductive.declareConstructors.ctorFoldAbsent
    (allowPrimitive : Bool) (mk : Nat → Constructor → ConstantInfo)
    (hmk : ∀ i ctor, (mk i ctor).name = ctor.name) (base : Environment) :
    ∀ (ctors : List Constructor) (cidx : Nat) (env : Environment), env.constants.WF →
      (∀ {n x}, base.find? n = some x → env.find? n = some x) →
      (ctors.foldlM (init := (cidx, env)) fun (state : Nat × Environment)
          (ctor : Constructor) => do
        let (cidx, env) := state
        env.checkName ctor.name allowPrimitive
        pure (cidx + 1, env.add (mk cidx ctor))).WF fun r =>
        r.2.constants.WF ∧ (∀ {n x}, base.find? n = some x → r.2.find? n = some x) ∧
        ∀ ctor ∈ ctors, base.find? ctor.name = none
  | [], _, _, hwf, hsub => Except.WF.pure ⟨hwf, hsub, by simp⟩
  | ctor :: ctors, cidx, env, hwf, hsub => by
    rw [List.foldlM_cons]
    refine Except.WF.bind (Q := fun r => r.2.constants.WF ∧
        (∀ {n x}, base.find? n = some x → r.2.find? n = some x) ∧
        base.find? ctor.name = none) ?_ fun r ⟨hwf', hsub', habs⟩ => ?_
    · refine (checkName.WF hwf ctor.name allowPrimitive).bind fun _ ⟨hn, _⟩ => ?_
      have hn' : env.find? (mk cidx ctor).name = none := by rw [hmk]; exact hn
      have hnMap : env.constants.find? (mk cidx ctor).name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn'
      refine Except.WF.pure ⟨?_, ?_, ?_⟩
      · change (env.constants.insert (mk cidx ctor).name (mk cidx ctor)).WF
        exact hwf.insert _ _ hnMap
      · intro n x h
        exact findAddFresh_of_find hwf _ hn' (hsub h)
      · cases hb : base.find? ctor.name with
        | none => rfl
        | some x => rw [hsub hb] at hn; cases hn
    · exact (ctorFoldAbsent allowPrimitive mk hmk base ctors r.1 r.2 hwf' hsub').mono
        fun r' ⟨h1, h2, h3⟩ => ⟨h1, h2, by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact habs
          · exact h3 c hc⟩

/-- `declareConstructors` succeeds only when every constructor name is absent from the
environment it starts from. -/
theorem AddInductive.declareConstructors.namesAbsent
    {c : AddInductive.Context} (hwf : c.env.constants.WF) :
    (AddInductive.declareConstructors stats indTypes isUnsafe c).WF fun _ =>
      ConstructorNamesAbsent indTypes c.env := by
  let mk := fun (owner : InductiveType) (cidx : Nat) (ctor : Constructor) =>
    ConstantInfo.ctorInfo (AddInductive.constructorInfo stats c.lparams isUnsafe owner cidx ctor)
  have outer : ∀ (owners : List InductiveType) (env : Environment), env.constants.WF →
      (∀ {n x}, c.env.find? n = some x → env.find? n = some x) →
      (owners.foldlM (init := env) fun (env : Environment) (owner : InductiveType) => do
        let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
            (state : Nat × Environment) (ctor : Constructor) => do
          let (cidx, env) := state
          env.checkName ctor.name c.allowPrimitive
          pure (cidx + 1, env.add (mk owner cidx ctor))
        pure env).WF fun _ =>
        ∀ owner ∈ owners, ∀ ctor ∈ owner.ctors, c.env.find? ctor.name = none := by
    intro owners
    induction owners with
    | nil => intro _ _ _; exact Except.WF.pure (by simp)
    | cons owner owners ih =>
      intro env hwf hsub
      rw [List.foldlM_cons]
      refine Except.WF.bind (Q := fun env' : Environment => env'.constants.WF ∧
            (∀ {n x}, c.env.find? n = some x → env'.find? n = some x) ∧
            ∀ ctor ∈ owner.ctors, c.env.find? ctor.name = none) ?_ fun env' h => ?_
      · exact Except.WF.bind (AddInductive.declareConstructors.ctorFoldAbsent
          c.allowPrimitive (mk owner) (by intros; rfl) c.env owner.ctors 0 env hwf hsub)
          fun ⟨_, _⟩ h => Except.WF.pure h
      · rcases h with ⟨hwf', hsub', habs⟩
        exact (ih env' hwf' hsub').mono fun _ h o ho ctor hctor => by
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact habs ctor hctor
          · exact h o ho ctor hctor
  rw [AddInductive.declareConstructors, ← Array.foldlM_toList]
  exact outer indTypes.toList c.env hwf id

/-- The executable's mutual-header metadata (`inductiveTypeInfos`) translates
directly to the exact
constants recovered by the skeleton-free header traversal. -/
theorem AddInductive.inductiveTypeInfos.translatedCheckedHeaders
    (Hheaders : HeaderTranslations env lparams
      indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    List.Forall₂
      (fun info ci' =>
        TrConstVal safety env (.inductInfo info) ci' ∧
          ci'.toVConstant.WF env)
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).toList
      Hheaders.targets := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe lparams
  have hsourceLength : indTypes.toList.length = Hheaders.targets.length :=
    List.Forall₂.length_eq
      Hheaders.translations
  have hinfosLength : infos.toList.length = Hheaders.targets.length := by
    calc
      infos.toList.length = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindices]
      _ = indTypes.toList.length := by simp
      _ = Hheaders.targets.length := hsourceLength
  apply List.forall₂_of_getElem hinfosLength
  intro i hiInfo hiTarget
  have hiSource : i < indTypes.toList.length := by
    simpa [hsourceLength] using hiTarget
  have Htarget := List.forall₂_getElem
    Hheaders.translations i hiSource hiTarget
  constructor
  · apply TrSourceConst.inductInfo Htarget
    · simp [infos, AddInductive.inductiveTypeInfos]
    · simp [infos, AddInductive.inductiveTypeInfos]
    · simp [infos, AddInductive.inductiveTypeInfos]
    · simpa [infos, AddInductive.inductiveTypeInfos, hindices] using
        hvisible
  · exact Htarget.wf

/-- The executable header declaration (`declareInductiveTypes`) installs the skeleton-free abstract
header constants in exact source order.  In particular the abstract
`addConstVals` equation is obtained from execution and is not supplied by a
caller skeleton. -/
theorem AddInductive.declareInductiveTypes.installsCheckedHeadersWF
    (Hc : ContextWF c)
    (Hheaders : HeaderTranslations Hc.venv c.lparams
      indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv => ∃ outVEnv,
        Hc.venv.addConstVals Hheaders.targets = some outVEnv ∧
        AddConstants c.safety c.env Hc.venv
          (List.zip
            ((AddInductive.inductiveTypeInfos stats numParams indTypes
              numNested isUnsafe c.lparams).toList.map
                (fun info => .inductInfo info))
            Hheaders.targets)
          outEnv outVEnv := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Hentries := AddInductive.inductiveTypeInfos.translatedCheckedHeaders
    (stats := stats) (numParams := numParams) (numNested := numNested)
    Hheaders hindices hvisible
  have Hinstall := AddConstants.ofDeclareInductiveTypeInfosExists
    (allowPrimitive := c.allowPrimitive) Hc.checking.tr Hentries VEnv.LE.rfl
      (by simpa [infos] using hnprim)
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    rcases Hinstalled with ⟨outVEnv, Hinstalled⟩
    refine ⟨outVEnv, ?_, ?_⟩
    · have habstract := Hinstalled.abstract
      have hvalues :
          (List.zip
            (infos.toList.map (fun info => ConstantInfo.inductInfo info))
            Hheaders.targets).map Prod.snd = Hheaders.targets := by
        apply List.map_snd_zip
        have hlength :=
          List.Forall₂.length_eq Hentries
        rw [List.length_map]
        exact Nat.le_of_eq hlength.symm
      rw [hvalues] at habstract
      exact habstract
    · simpa [infos] using Hinstalled

/-- The header environment, skeleton-free: the state after all mutual family
constants have been installed and before any constructor is checked. -/
structure InstalledHeaders
    (c : AddInductive.Context) (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats)
    (nparams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (commonParams : List VExpr) (commonLevel : VLevel)
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (outEnv : Environment) where
  envTypes : VEnv
  context : ContextWF { c with env := outEnv }
  contextVEnv : context.venv = envTypes
  contextMLCtx : context.mlctx = Hc.mlctx
  installed : AddConstants c.safety c.env Hc.venv
    (List.zip
      ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList.map (fun info => .inductInfo info))
      Hsemantic.headers.targets)
    outEnv envTypes
  values : (List.zip
    ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
      isUnsafe c.lparams).toList.map (fun info => ConstantInfo.inductInfo info))
    Hsemantic.headers.targets).map Prod.snd = Hsemantic.headers.targets
  typesAdded : Hc.venv.addConstVals
    (Hsemantic.headerDecl isUnsafe).typeConstants = some envTypes
  headers : HeaderCertificate Hc.venv (Hsemantic.headerDecl isUnsafe)
  /-- Every constructor a header of the source environment lists is present there. -/
  sourcePresent : ListedConstructorsPresent c.env

/-- Package exact abstract installation, the valid installed checking
context, and the header certificate while retaining every semantic payload
and normalized source telescope. -/
theorem AddInductive.declareInductiveTypes.headersWF
    (Hc : ContextWF c)
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams numParams commonParams commonLevel indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hpresent : ListedConstructorsPresent c.env) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv => outEnv.constants.WF ∧
        (ConstructorNamesAbsent indTypes outEnv →
        Nonempty (InstalledHeaders c Hc stats numParams indTypes
          numNested isUnsafe commonParams commonLevel Hsemantic outEnv)) := by
  have Hinstall :=
    AddInductive.declareInductiveTypes.installsCheckedHeadersWF
      Hc Hsemantic.headers hindices hvisible hnprim
  exact Hinstall.mono fun outEnv Hresult => by
    rcases Hresult with ⟨envTypes, htypes, Hinstalled⟩
    refine ⟨Hinstalled.targetMapWF Hc.checking.tr.map_wf, fun habsent => ?_⟩
    have habsentInfos : ∀ info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes
        numNested isUnsafe c.lparams).toList, ∀ name ∈ info.ctors, outEnv.find? name = none := by
      intro info hinfo name hname
      rcases inductiveTypeInfos_ctors stats numParams indTypes numNested isUnsafe c.lparams
        hinfo with ⟨owner, howner, -, hctors, -⟩
      rw [hctors] at hname
      obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hname
      exact habsent owner howner ctor hctor
    exact ⟨{
      envTypes := envTypes
      context := Hc.withEnv (Hinstalled.validHeaders Hc.checking hpresent habsentInfos)
        Hinstalled.le
      contextVEnv := rfl
      contextMLCtx := rfl
      installed := Hinstalled
      values := by
        apply List.map_snd_zip
        have hlength := List.Forall₂.length_eq
          Hsemantic.headers.translations
        have hinfos :
            (AddInductive.inductiveTypeInfos stats numParams indTypes
              numNested isUnsafe c.lparams).toList.length = indTypes.size := by
          simp [AddInductive.inductiveTypeInfos, hindices]
        simpa [hinfos] using Nat.le_of_eq hlength.symm
      typesAdded := by
        rw [Hsemantic.headerDecl_typeConstants]
        exact htypes
      headers := Hsemantic.headerCertificate isUnsafe
      sourcePresent := hpresent }⟩

end VerifyInductive
end Lean4Lean
