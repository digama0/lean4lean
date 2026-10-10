import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Install.Result
import Lean4Lean.Verify.Inductive.Install.Rebase
import Lean4Lean.Verify.Inductive.Install.RecursorShapes

/-! # The block certificate and its installation into the environment model

`BlockCertificate` is what a complete run of the ordinary pipeline certifies at the checked
safety level: the installed declaration is well formed (`VInductDecl.WF`), PR #43's `AddInduct`
relates the source and output environments (so `TrEnv'.induct` applies), and the facts
`InstalledBlocks.addInduct` (wave 1B) reads of the output. `RecursorCheck.blockCertificate`
assembles it from the recursor and rule phases; `BlockCertificate.extendSafeExact` and
`extendUnsafeExact` install it into the safety-indexed model `VEnvs` ("Assembly" in section 3.2
of the design notes).

Wave 2 scaffold: owned by the `Install/`+`Primitive/`+`Prelude/` agent (source branch:
`Install/{BlockCertificate,Environments,Lookups,Metadata,LiteralNames}.lean`, rewritten against
`AddInduct`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The certificate of an installed block at the checked safety level `safety`. -/
structure BlockCertificate (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (decl : VInductDecl) (outEnv : Environment) (outVEnv : VEnv) where
  wf : decl.WF venv
  add : AddInduct safety env.constants venv decl outEnv.constants outVEnv
  quotInit_eq : outEnv.quotInit = env.quotInit
  checking : CheckingEnv.Valid safety outEnv outVEnv
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl env.constants outEnv.constants decl
  cover : ∀ T ∈ decl.types,
    ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment safety env venv →
    ConstructorParameterAlignment safety outEnv outVEnv
  recK : ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
    KLikeRecursor outEnv.constants outVEnv r
  /-- A well-formed compiled block of the declaration: its equations' typing (`block.WF`) is
  what replays `recsCompiled` in the models of the other safety levels (`rebase`). -/
  compiled : ∃ block, decl.CompilesTo venv block ∧ decl.RecsOf block ∧ block.WF venv
  /-- Every inserted constant carries the declaration's `isUnsafe`: an unsafe block is hidden
  from the partial and safe observers (`extendUnsafeExact`), a safe one is visible to all. -/
  newUnsafe : ∀ ci ∈ AddInduct.consts add.ivals add.rvals, ci.isUnsafe = decl.isUnsafe
  /-- The recursor and constructor telescopes of every new recursor (`RecursorShapes`, read by
  recursor reduction), recorded in the new block's descriptor. -/
  recShapes : ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
    RecursorShapesAt outEnv.constants outVEnv r

namespace BlockCertificate

variable {safety : DefinitionSafety} {env outEnv : Environment} {venv outVEnv : VEnv}
  {decl : VInductDecl}

theorem installed (H : BlockCertificate safety env venv decl outEnv outVEnv) :
    venv.addInduct decl = some outVEnv := H.add.env_eq

theorem le (H : BlockCertificate safety env venv decl outEnv outVEnv) : venv ≤ outVEnv :=
  H.add.le

theorem inductInstalled (H : BlockCertificate safety env venv decl outEnv outVEnv) :
    outVEnv.InductInstalled decl :=
  VEnv.InductInstalled.of_addInduct H.wf H.installed H.compiled -- WAVE 3 COMPAT (lowering)

/-- Every constant of the source environment is a constant of the output, to the same value:
every name the block inserts is fresh. -/
theorem find?_mono (H : BlockCertificate safety env venv decl outEnv outVEnv)
    (hwf : env.constants.WF) {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) :
    outEnv.find? n = some ci := by
  have houtWF : outEnv.constants.WF := H.checking.tr.map_wf
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
  exact H.add.find?_mono hwf h

/-- The output of a certified block is a valid checking environment with the installed blocks of
the source and the new one: wave 1B's `InstalledBlocks.addInduct`. -/
theorem installedBlocks (H : BlockCertificate safety env venv decl outEnv outVEnv)
    (hblocks : InstalledBlocks safety env venv .complete) (hwf : env.constants.WF)
    (hvisible : safety ≤ (if decl.isUnsafe then DefinitionSafety.unsafe else .safe))
    (hparams : ConstructorParameterAlignment safety env venv) :
    InstalledBlocks safety outEnv outVEnv .complete := by
  refine InstalledBlocks.addInduct hblocks hwf H.checking.tr ?_ H.le H.inductInfosFromDecl
    H.cover H.closed H.constructorOwners (fun h1 h2 => H.recMajor h1 h2)
    (fun _ => ⟨H.wf, H.installed, H.compiled⟩) -- WAVE 3 COMPAT (lowering)
    (fun h => absurd hvisible h)
    (fun _ => H.constructorParameterAlignment hparams) (fun h1 h2 _ => H.recK h1 h2)
    (fun h1 h2 _ => H.recShapes h1 h2)
  exact H.find?_mono hwf

/-- The constructor parameter alignment of the output at any observer: the families of the
source come from the source alignment at that observer, the new families (safe, since the block
is) from the certificate's alignment at `.safe`. -/
theorem parameterAlignment (H : BlockCertificate .safe env venv decl outEnv outVEnv)
    (hwf : env.constants.WF) (hsafe : decl.isUnsafe = false) {venv' outVEnv' : VEnv}
    (hsrc : ConstructorParameterAlignment safety env venv')
    (hsrcSafe : ConstructorParameterAlignment .safe env venv)
    (hle' : venv' ≤ outVEnv') (hout : outVEnv ≤ outVEnv') :
    ConstructorParameterAlignment safety outEnv outVEnv' := by
  intro familyName familyInfo hfamily hvisible i hi
  have houtWF : outEnv.constants.WF := H.checking.tr.map_wf
  have hfamily' := hfamily
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hfamily'
  rcases H.add.find? hwf hfamily' with hold | ⟨hnew, -⟩
  · have hold' : env.find? familyName = some (.inductInfo familyInfo) := by
      rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]; exact hold
    obtain ⟨C⟩ := hsrc familyName familyInfo hold' hvisible i hi
    exact ⟨C.rebaseKernel (H.find?_mono hwf C.lookup) hle'⟩
  · have hu : familyInfo.isUnsafe = false := by
      have := H.newUnsafe _ hnew; rw [hsafe] at this; exact this
    have hvis : DefinitionSafety.safe ≤
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe else .safe) := by
      simp [hu]
    obtain ⟨C⟩ := H.constructorParameterAlignment hsrcSafe familyName familyInfo hfamily hvis i hi
    exact ⟨C.mono hout⟩

/-- Replay a certified safe block in the model of another safety level: the names are fresh
there too (the model is aligned with the same constant map), the stages replay above the
original ones (`AddInduct.rebase`), the declaration and its compiled block stay well formed
(`VInductDecl.WF.rebase`), and the output is a valid checking environment with the new block
installed (`InstalledBlocks.addInduct`). -/
theorem rebase {ves : VEnvs} (H : BlockCertificate .safe env (ves.venv .safe) decl outEnv outVEnv)
    (wf : ves.WF env) (hsafe : decl.isUnsafe = false) (safety : DefinitionSafety) :
    ∃ outVEnv', Nonempty (BlockCertificate safety env (ves.venv safety) decl outEnv outVEnv') ∧
      outVEnv ≤ outVEnv' := by
  have hle : ves.venv .safe ≤ ves.venv safety := wf.mono DefinitionSafety.le_safe
  have htr : TrEnv safety env (ves.venv safety) := wf.tr
  have hwf : env.constants.WF := htr.map_wf
  obtain ⟨out', add', hivals, hrvals, hout⟩ :=
    H.add.rebase (safety := safety) DefinitionSafety.le_safe hle (H.add.fresh_of_aligned htr.aligned)
  obtain ⟨block, hcomp, hrecs, hblock⟩ := H.compiled
  obtain ⟨wf', hblock'⟩ := H.wf.rebase hcomp hrecs hblock hle H.add.stT H.add.stC H.add.stR
    add'.stT add'.stC add'.stR
  have installed' : (ves.venv safety).addInduct decl = some out' := add'.env_eq
  have htrOut : TrEnv safety outEnv out' := by
    unfold TrEnv; rw [H.quotInit_eq]; exact .induct wf' add' htr
  have hprims' : out'.HasPrimitives :=
    VEnv.HasPrimitives.addInduct_rebase wf.hasPrimitives H.checking.hasPrimitives H.installed
      installed' hout
  have hvis : safety ≤ (if decl.isUnsafe then DefinitionSafety.unsafe else .safe) := by
    rw [hsafe]; exact DefinitionSafety.le_safe
  have hparams' : ConstructorParameterAlignment safety outEnv out' :=
    H.parameterAlignment hwf hsafe wf.constructorParameterAlignment
      wf.constructorParameterAlignment add'.le hout
  have hrecK' : ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
      KLikeRecursor outEnv.constants out' r :=
    fun h1 h2 => (H.recK h1 h2).mono hout id
  have hblocks' : InstalledBlocks safety outEnv out' .complete :=
    InstalledBlocks.addInduct wf.blocks hwf htrOut.toChecking (H.find?_mono hwf) add'.le
      H.inductInfosFromDecl H.cover H.closed H.constructorOwners (fun h1 h2 => H.recMajor h1 h2)
      -- WAVE 3 COMPAT (lowering): the compiled block, replayed
      (fun _ => ⟨wf', installed', block, hcomp.mono hle hblock', hrecs, hblock'⟩)
      (fun h => absurd hvis h) (fun _ => hparams')
      (fun h1 h2 _ => hrecK' h1 h2) (fun h1 h2 _ => (H.recShapes h1 h2).extend hout id)
  refine ⟨out', ⟨{
    wf := wf'
    add := add'
    quotInit_eq := H.quotInit_eq
    checking := htrOut.toCheckingValid hprims' H.checking.safePrimitives hblocks'
    closed := H.closed
    constructorOwners := H.constructorOwners
    inductInfosFromDecl := H.inductInfosFromDecl
    cover := H.cover
    recMajor := H.recMajor
    constructorParameterAlignment := fun _ => hparams'
    recK := hrecK'
    compiled := ⟨block, hcomp.mono hle hblock', hrecs, hblock'⟩
    newUnsafe := by rw [hivals, hrvals]; exact H.newUnsafe
    recShapes := fun h1 h2 => (H.recShapes h1 h2).extend hout id }⟩, hout⟩

/-- A certified safe block extends the whole safety-indexed model: the block is replayed at
every safety level (`rebase`) and `VEnvs.WF.extendInductExact` assembles the models. -/
theorem extendSafeExact {ves : VEnvs}
    (H : BlockCertificate .safe env (ves.venv .safe) decl outEnv outVEnv)
    (wf : ves.WF env) (hsafe : decl.isUnsafe = false) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      ves'.venv .safe = outVEnv := by
  have hR : ∀ safety, ∃ out', Nonempty (BlockCertificate safety env (ves.venv safety) decl outEnv
      out') ∧ (safety = .safe → out' = outVEnv) := by
    intro safety
    cases safety with
    | safe => exact ⟨outVEnv, ⟨H⟩, fun _ => rfl⟩
    | «partial» =>
      obtain ⟨out', B, -⟩ := H.rebase wf hsafe .partial
      exact ⟨out', B, fun h => nomatch h⟩
    | «unsafe» =>
      obtain ⟨out', B, -⟩ := H.rebase wf hsafe .unsafe
      exact ⟨out', B, fun h => nomatch h⟩
  obtain ⟨next, hnext⟩ := VEnvs.axiom_of_choice hR
  have B : ∀ safety, BlockCertificate safety env (ves.venv safety) decl outEnv (next.venv safety) :=
    fun safety => Classical.choice (hnext safety).1
  have hwf : env.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hvis : ∀ safety : DefinitionSafety,
      safety ≤ (if decl.isUnsafe then DefinitionSafety.unsafe else .safe) := by
    intro safety; rw [hsafe]; exact DefinitionSafety.le_safe
  obtain ⟨ves', wf', hle, heq⟩ := wf.extendInductExact decl next.venv (fun s => (B s).wf)
    (fun s => (B s).add) H.quotInit_eq (fun s => (B s).checking.hasPrimitives)
    H.checking.safePrimitives
    (fun s => (B s).installedBlocks wf.blocks hwf (hvis s) wf.constructorParameterAlignment)
    (fun h => VEnv.addInduct_mono (wf.mono h) (B _).installed (B _).installed)
  exact ⟨ves', wf', hle, (heq .safe).trans ((hnext .safe).2 rfl)⟩

/-- A certified unsafe block extends the unsafe model and is hidden from the partial and safe
observers (`VEnvs.WF.extendUnsafeExact`): every inserted constant is unsafe, so the other two
translations are extended by `TrEnv'.ignore`. -/
theorem extendUnsafeExact {ves : VEnvs}
    (H : BlockCertificate .unsafe env (ves.venv .unsafe) decl outEnv outVEnv)
    (wf : ves.WF env) (hunsafe : decl.isUnsafe = true) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      ves'.venv .unsafe = outVEnv := by
  have hwf : env.constants.WF := (wf.tr (safety := .unsafe)).map_wf
  have hhidden : ∀ {safety : DefinitionSafety}, safety ≠ .unsafe →
      ∀ ci ∈ H.add.order, ¬ safety ≤ ci.safety := fun hs ci hci =>
    ConstantInfo.not_le_safety_of_isUnsafe
      ((H.newUnsafe ci (H.add.order_perm.mem_iff.1 hci)).trans hunsafe) hs
  have htrHidden : ∀ {safety : DefinitionSafety}, safety ≠ .unsafe →
      TrEnv' safety outEnv.constants outEnv.quotInit (ves.venv safety) := by
    intro safety hs
    rw [H.quotInit_eq, H.add.map_eq]
    exact TrEnv'.ignoreConsts (hhidden hs) H.add.order_fresh H.add.order_nodup wf.tr
  have hdeclHidden : ∀ {safety : DefinitionSafety}, safety ≠ .unsafe →
      ¬ safety ≤ (if decl.isUnsafe then DefinitionSafety.unsafe else .safe) := by
    intro safety hs h
    rw [hunsafe] at h
    exact hs (DefinitionSafety.le_antisymm h DefinitionSafety.unsafe_le)
  have hrecHidden : ∀ {safety : DefinitionSafety}, safety ≠ .unsafe →
      ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
      ¬ safety ≤ (ConstantInfo.recInfo r).safety := by
    intro safety hs n r h1 h2
    have houtWF : outEnv.constants.WF := H.checking.tr.map_wf
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at h1
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h2
    rcases H.add.find? hwf h1 with hold | ⟨hnew, -⟩
    · rw [h2] at hold; cases hold
    · exact ConstantInfo.not_le_safety_of_isUnsafe ((H.newUnsafe _ hnew).trans hunsafe) hs
  have hidden : ∀ {safety : DefinitionSafety}, safety ≠ .unsafe →
      InstalledBlocks safety outEnv (ves.venv safety) .complete := by
    intro safety hs
    exact InstalledBlocks.addInduct wf.blocks hwf
      (show TrEnv safety outEnv (ves.venv safety) from htrHidden hs).toChecking
      (H.find?_mono hwf) VEnv.LE.rfl H.inductInfosFromDecl H.cover H.closed
      H.constructorOwners (fun h1 h2 => H.recMajor h1 h2) (fun h => absurd h (hdeclHidden hs))
      (fun _ => rfl) (fun h => absurd h (hdeclHidden hs))
      (fun h1 h2 h => absurd h (hrecHidden hs h1 h2))
      (fun h1 h2 h => absurd h (hrecHidden hs h1 h2))
  have hvisU : DefinitionSafety.unsafe ≤
      (if decl.isUnsafe then DefinitionSafety.unsafe else .safe) := DefinitionSafety.unsafe_le
  refine wf.extendUnsafeExact outVEnv ?_ (htrHidden (by decide)) (htrHidden (by decide))
    H.checking.hasPrimitives H.checking.safePrimitives ?_ H.le
  · rw [H.quotInit_eq]; exact .induct H.wf H.add wf.tr
  · intro safety
    cases safety with
    | «unsafe» =>
      exact H.installedBlocks wf.blocks hwf hvisU wf.constructorParameterAlignment
    | «partial» => exact hidden (by decide)
    | safe => exact hidden (by decide)

end BlockCertificate

/-- The environment after the rules are registered: the output of `addInduct` for the
recursor check's declaration (`RecursorCheck.decl'`), given that `addRules` succeeds
(`rules_closed`). -/
def RecursorCheck.outVEnv'
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT
    (H : RecursorCheck R outEnv) : VEnv :=
  ((decl.withRecs H.recs).addRules H.outVEnv).getD H.outVEnv

/-- The source branch's `OrdinaryInstallation.extend*Exact` read the block certificate off the
recursor check and the rule translations: this is that assembly. The installed declaration is
`H.decl'` (the constructor phase's declaration with the generated recursors). -/
theorem RecursorCheck.blockCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT
    (H : RecursorCheck R outEnv) (T : RuleTranslations H)
    (hnonempty : indTypes.toList ≠ []) :
    Nonempty (BlockCertificate c.safety c.env sourceEnv H.decl' outEnv H.outVEnv') := by
  have hwf : c.env.constants.WF := R.headers.sourceContext.map_wf
  have hsrcWF : sourceEnv.WF := R.headers.sourceContextVEnv ▸ R.headers.sourceContext.wf
  have hhdrWF : R.headerEnv.constants.WF := R.headers.context.map_wf
  have hctorWF : ctorEnv.constants.WF := R.context.map_wf
  have toMap : ∀ {E : Environment} (_ : E.constants.WF) {n ci}, E.find? n = some ci →
      E.constants.find? n = some ci := by
    intro E hE n ci h; rwa [Lean.Kernel.Environment.find?, hE.find?'_eq_find?] at h
  have toMapNone : ∀ {E : Environment} (_ : E.constants.WF) {n}, E.find? n = none →
      E.constants.find? n = none := by
    intro E hE n h; rwa [Lean.Kernel.Environment.find?, hE.find?'_eq_find?] at h
  have hinfos : R.headers.infos = R.ivals.map (·.1) := R.ivals_infos.symm
  -- the kernel side: headers over the source, constructors over the headers, recursors over
  -- the constructors
  have freshHdr : ∀ ci ∈ R.headers.infos.map ConstantInfo.inductInfo,
      c.env.constants.find? ci.name = none := by
    intro ci hci
    obtain ⟨info, hinfo, rfl⟩ := List.mem_map.1 hci
    exact toMapNone hwf (R.headers.fresh info hinfo)
  have subHdr : ∀ {n x}, c.env.constants.find? n = some x → R.headerEnv.constants.find? n = some x :=
    fun h => by rw [R.headers.map_eq]; exact insertConsts_find?_mono_of_fresh hwf.map₂ freshHdr h
  have freshCtor : ∀ ci ∈ R.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo),
      R.headerEnv.constants.find? ci.name = none := by
    intro ci hci
    obtain ⟨iv, hiv, hci⟩ := List.mem_flatMap.1 hci
    obtain ⟨cval, hcval, rfl⟩ := List.mem_map.1 hci
    exact toMapNone hhdrWF (R.fresh iv hiv cval hcval)
  have subCtor : ∀ {n x}, R.headerEnv.constants.find? n = some x → ctorEnv.constants.find? n = some x :=
    fun h => by rw [R.map_eq]; exact insertConsts_find?_mono_of_fresh hhdrWF.map₂ freshCtor h
  have noneOf : ∀ {C C' : ConstMap} (_ : ∀ {n x}, C.find? n = some x → C'.find? n = some x)
      {n}, C'.find? n = none → C.find? n = none := by
    intro C C' hsub n h
    cases hc : C.find? n with
    | none => rfl
    | some x => rw [hsub hc] at h; cases h
  -- the stages
  obtain ⟨outR, hP⟩ := VEnv.addRules_exists (decl := H.decl') H.outVEnv H.rules_closed
  have hout' : H.outVEnv' = outR := by simp [RecursorCheck.outVEnv', hP]
  rw [hout']
  have stT : H.decl'.addTypes sourceEnv = some R.headerVEnv := by
    rw [VInductDecl.addTypes_eq_addConstVals]; exact R.core.typesAdded
  have stC : H.decl'.addCtors R.headerVEnv = some R.ctorVEnv := by
    rw [VInductDecl.addCtors_eq_addConstVals]; exact R.core.ctorsAdded
  have stR : H.decl'.addRecs (H.decl'.addProjs R.ctorVEnv) = some H.outVEnv := H.recsAdded
  let add : AddInduct c.safety c.env.constants sourceEnv H.decl' outEnv.constants outR := {
    ivals := R.ivals
    rvals := H.rvals
    envT := R.headerVEnv
    envC := R.ctorVEnv
    envR := H.outVEnv
    stT := stT
    stC := stC
    stR := stR
    stP := hP
    types := R.trTypes
    recs := H.trRecs
    order := AddInduct.consts R.ivals H.rvals
    order_perm := List.Perm.refl _
    fresh := by
      intro ci hci
      rcases AddInduct.mem_consts.1 hci with ⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cval, hcval, rfl⟩ |
          ⟨rval, hrval, rfl⟩
      · exact freshHdr _ (List.mem_map_of_mem (by rw [hinfos]; exact List.mem_map_of_mem hiv))
      · exact noneOf subHdr (toMapNone hhdrWF (R.fresh iv hiv cval hcval))
      · exact noneOf (fun h => subCtor (subHdr h)) (toMapNone hctorWF (H.fresh rval hrval))
    map_eq := by
      rw [H.map_eq, R.map_eq, R.headers.map_eq, hinfos]
      simp [AddInduct.consts, insertConsts, List.foldl_append, List.map_map, Function.comp_def] }
  have hle' : H.outVEnv ≤ outR := VEnv.addRules_le hP
  have hleR : sourceEnv ≤ H.outVEnv :=
    (VEnv.addTypes_le stT).trans ((VEnv.addCtors_le stC).trans
      (VEnv.addProjs_le.trans (VEnv.addRecs_le stR)))
  have wf' : H.decl'.WF sourceEnv :=
    (R.formation.withRecs H.recs).wf
      (VInductDecl.SourceWF.withRecs (TrInductDeclCore.sourceWF_ofNonempty R.core
        (TrInductDeclCore.nonempty R.core hnonempty)) H.recs) (T.recursorsWF hnonempty)
  have installed : sourceEnv.addInduct H.decl' = some outR := add.env_eq
  have houtWF : outEnv.constants.WF := H.checking.tr.map_wf
  -- every new recursor is one of the block's
  have newRec : ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
      r ∈ H.rvals := by
    intro n r h1 h2
    rcases add.find? hwf (toMap houtWF h1) with hold | ⟨hmem, -⟩
    · rw [toMapNone hwf h2] at hold; cases hold
    · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨rval, hrval, h⟩
      · cases h
      · cases h
      · cases h; exact hrval
  have hnpCtor : ∀ {n cval}, outEnv.constants.find? n = some (.ctorInfo cval) →
      (∃ src ∈ decl.constructorConstants, src.name = n) → cval.numParams = decl.nparams := by
    intro n cval h ⟨src, hsrc, hname⟩
    subst hname
    rcases add.find? hwf h with hold | ⟨hmem, -⟩
    · have hin : src.name ∈ (AddInduct.consts add.ivals add.rvals).map (·.name) := by
        rw [add.consts_names]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hsrc))
      obtain ⟨ci, hci, hcn⟩ := List.mem_map.1 hin
      have := add.fresh ci hci
      rw [hcn, hold] at this; cases this
    · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨iv, hiv, cval', hcval', h⟩ | ⟨_, _, h⟩
      · cases h
      · cases h; exact R.ctor_numParams iv hiv cval hcval'
      · cases h
  have checking : CheckingEnv.Valid c.safety outEnv outR := by
    obtain ⟨ds, hds⟩ := hsrcWF
    refine H.checking.addRules hP ⟨_, .decl (.induct wf' installed) hds⟩ ?_
    intro p r hp
    rcases VEnv.addInduct_pats_origin installed hp with hold | ⟨rec, hrec, ru, -, rfl⟩
    · exact .inl (hleR.pats hold)
    · refine .inr ?_
      rw [SimplePattern.iota_headConst]
      obtain ⟨rval, hrval, htr⟩ := List.Forall₂.forall_exists_r H.trRecs rec hrec
      have := add.find?_self hwf (ci := .recInfo rval)
        (AddInduct.mem_consts.2 (.inr (.inr ⟨rval, hrval, rfl⟩)))
      exact ⟨rval, htr.tr.2 ▸ this⟩
  refine ⟨{
    wf := wf'
    add := add
    quotInit_eq := H.quotInit_eq.trans (R.quotInit_eq.trans R.headers.quotInit_eq)
    checking := checking
    closed := H.closed
    constructorOwners := H.checking.constructorOwners
    inductInfosFromDecl := H.inductInfosFromDecl.withRecs H.recs
    cover := ?_
    recMajor := ?_
    constructorParameterAlignment := fun h => (H.constructorParameterAlignment h).mono hle'
    recK := fun h1 h2 => (H.kLike _ (newRec h1 h2)).mono hle' id
    compiled := ⟨T.block, T.compilesTo hnonempty, T.recsOf, T.blockWF⟩
    newUnsafe := ?_
    recShapes := fun h1 h2 => (H.recursorShapes T hnpCtor _ (newRec h1 h2)).extend hle' id }⟩
  · intro t ht
    obtain ⟨info, hinfo, htr⟩ := List.Forall₂.forall_exists_r R.headers.trHeaders t ht
    have hname : info.name = t.name := htr.1.2
    have hmem : ConstantInfo.inductInfo info ∈ AddInduct.consts R.ivals H.rvals := by
      rw [hinfos] at hinfo
      obtain ⟨iv, hiv, rfl⟩ := List.mem_map.1 hinfo
      exact AddInduct.mem_consts.2 (.inl ⟨iv, hiv, rfl⟩)
    refine ⟨info, ?_, hname ▸ R.headers.fresh info hinfo⟩
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, ← hname]
    exact add.find?_self hwf hmem
  · intro n r h1 h2
    have hr := newRec h1 h2
    obtain ⟨rec, -, htr⟩ := List.Forall₂.forall_exists_l H.trRecs r hr
    obtain ⟨info, hinfo⟩ := H.checking.recursors.majors (toMap houtWF h1) htr.tr.1.1
    exact ⟨info, by rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]; exact hinfo⟩
  · have hdecl : H.decl'.isUnsafe = decl.isUnsafe := rfl
    have hfam : ∀ iv ∈ R.ivals, iv.1.isUnsafe = decl.isUnsafe := by
      intro iv hiv
      have hmem : ConstantInfo.inductInfo iv.1 ∈ AddInduct.consts R.ivals H.rvals :=
        AddInduct.mem_consts.2 (.inl ⟨iv, hiv, rfl⟩)
      have hf := add.find?_self hwf hmem
      have hf' : outEnv.find? iv.1.name = some (.inductInfo iv.1) := by
        rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]; exact hf
      rcases H.inductInfosFromDecl _ _ (toMap houtWF hf') with hold | ⟨_, -, ⟨A⟩⟩
      · have : c.env.constants.find? iv.1.name = none := add.fresh _ hmem
        rw [this] at hold; cases hold
      · exact A.isUnsafe
    intro ci hci
    rw [hdecl]
    rcases AddInduct.mem_consts.1 hci with ⟨iv, hiv, rfl⟩ | ⟨iv, hiv, cval, hcval, rfl⟩ |
        ⟨rval, hrval, rfl⟩
    · exact hfam iv hiv
    · obtain ⟨t, -, ht⟩ := List.Forall₂.forall_exists_l R.trTypes iv hiv
      have hlisted : cval.name ∈ iv.1.ctors := by
        rw [ht.ctor_names]; exact List.mem_map_of_mem hcval
      have hfind : ∀ ci ∈ AddInduct.consts R.ivals H.rvals, outEnv.find? ci.name = some ci := by
        intro ci hci
        rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]; exact add.find?_self hwf hci
      obtain ⟨info, hinfo, -, hu⟩ := H.checking.listedConstructors iv.1.name iv.1
        (hfind _ (AddInduct.mem_consts.2 (.inl ⟨iv, hiv, rfl⟩))) cval.name hlisted _
        (hfind _ hci)
      cases hinfo
      exact hu.trans (hfam iv hiv)
    · obtain ⟨owner, -, hm⟩ := List.Forall₂.forall_exists_r H.metadata rval hrval
      exact hm.isUnsafe.trans H.models.safety

end VerifyInductive
end Lean4Lean
