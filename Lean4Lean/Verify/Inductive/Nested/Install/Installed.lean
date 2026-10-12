import Lean4Lean.Verify.Inductive.Nested.Equations.Rules
import Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledFamilyLookups
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorCoherence

/-! # The environment-side facts of a restored block and its block certificate

`RestoredBlock.Installed` collects what `InstalledBlocks.addInduct` and `BlockCertificate` read
of the output environment beyond the restored block's own data: the checking invariant of the
output over the output model, closure, constructor owners, the origin of every new header
(`InductInfosFromDecl`), the cover of the declaration's families, the majors of the new
recursors and the constructor parameter alignment. `RestoredBlock.installedFacts` produces it;
`RestoredBlock.blockCertificate` assembles PR #43's `BlockCertificate` from it, the restored
block and the typing of the restored rules (`Nested/Equations/`), after which the ordinary
path's `BlockCertificate.extendSafeExact`/`extendUnsafeExact` install the block. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- A name new in the target of a nonprimitive fresh extension is not primitive. -/
theorem FreshNonprimitiveExtension.new_nonprimitive {source target : Environment}
    {entries : List ConstantInfo} (H : FreshNonprimitiveExtension false source entries target)
    (hwf : source.constants.WF) {n : Name} {ci : ConstantInfo}
    (ht : target.find? n = some ci) (hs : source.find? n = none) :
    ¬ Kernel.Environment.primitives.contains n := by
  induction H with
  | nil => rw [hs] at ht; cases ht
  | cons hfresh hnprim Htail ih =>
    rename_i cis out env ci0
    have hnextWF : (env.add ci0).constants.WF := constantsWF_add_checked hwf hfresh
    by_cases hn : ci0.name = n
    · subst hn; simp [hnprim rfl]
    · apply ih hnextWF ht
      have hfreshMap : env.constants.find? ci0.name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
      rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hs
      change (env.constants.insert ci0.name ci0).find?' n = none
      rw [(hwf.insert ci0.name ci0 hfreshMap).find?'_eq_find?, hwf.find?_insert]
      split
      · rename_i heq; exact absurd (by simpa using heq) hn
      · exact hs

/-- The primitive safety of the target of a nonprimitive fresh extension. -/
theorem FreshNonprimitiveExtension.safePrimitives {source target : Environment}
    {entries : List ConstantInfo} (H : FreshNonprimitiveExtension false source entries target)
    (hwf : source.constants.WF)
    (hsafe : ∀ {n ci}, source.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []) :
    ∀ {n ci}, target.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [] := by
  intro n ci ht hp
  cases hs : source.find? n with
  | none => exact absurd hp (H.new_nonprimitive hwf ht hs)
  | some ci0 =>
    have := H.fresh.preservesSourceFind hwf hs
    rw [ht] at this
    cases this
    exact hsafe hs hp

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- The environment-side facts of a restored block (see the module documentation). -/
structure Installed (B : RestoredBlock L sourceTypes isUnsafe outEnv) : Prop where
  checking : CheckingEnv.Valid c.safety outEnv B.outVEnv
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants B.decl
  cover : ∀ T ∈ B.decl.types,
    ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ c.env.find? T.name = none
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment c.safety c.env Hc.venv →
    ConstructorParameterAlignment c.safety outEnv B.outVEnv

/-- The kernel-level facts of the restored output: what the restoration folds certify about
the inserted `inductInfo`/`ctorInfo`/`recInfo` metadata (the `all` lists, constructor owners,
the families' alignment with the declaration, the recursors' majors, the constructor
parameter domains) and the primitive names. -/
structure KernelFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv) : Prop where
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants B.decl
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment c.safety c.env Hc.venv →
    ConstructorParameterAlignment c.safety outEnv B.outVEnv
  hasPrimitives : B.outVEnv.HasPrimitives
  safePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
    Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []

/-- The declaration's `isUnsafe` is the lowered run's. -/
theorem isUnsafe_lowered (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    isUnsafe = (c.safety != .safe) :=
  B.run.lowered_isUnsafe_source.symm

/-- The run's lowering certificate, at the lowered run's context. -/
theorem runLowering (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    NestedLoweringOutputClosed L.c.env B.run.validationFuel.inductiveFuel nparams sourceTypes
      { ({ lvls := L.c.lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with newTypes := sourceTypes.toArray } res := by
  rw [L.env_eq, L.lparams_eq]
  exact B.run.lowering

/-- The run's restoration folds, over the lowered environment and the lowered run's context. -/
def runRestoration (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    NestedRestorationFolds res loweredEnv L.c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv) := by
  have h := B.run.restoration
  rw [L.env_eq]
  exact h

/-- Every constructor of the output is listed by its present owner. -/
theorem constructorOwnersPresent (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ConstructorOwnersPresent outEnv := by
  have Howners : ConstructorOwnersPresent L.c.env := by
    rw [L.env_eq]; exact Hc.checking.constructorOwners
  exact NestedRestorationFolds.constructorOwnersPresent (R := L.constructors) B.runLowering L.Hc'
    L.recursors rfl B.runRestoration Howners

/-- The run's source-side certificates for its recursor-free declaration `runDecl`. -/
theorem runSource (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    TrInductDeclCore L.Hc'.venv L.c.lparams nparams sourceTypes (c.safety != .safe) B.runDecl
      B.envTypes B.envCtors ∧
    SourcePrefixOfLowered B.runDecl L.loweredDecl ∧
    B.runDecl.ConstructorArityPrefix L.loweredDecl := by
  have hdecl := B.run_decl
  have Hsource0 := B.source
  rw [hdecl] at Hsource0
  refine ⟨?_, ?_, ?_⟩
  · simp only [L.lparams_eq, L.venv_eq, ← B.isUnsafe_lowered]
    exact ⟨Hsource0.uvars, Hsource0.nparams, Hsource0.isUnsafe, Hsource0.typesAdded,
      Hsource0.ctorsAdded, Hsource0.types⟩
  · have h := B.run.sourceCore.checked
    rw [B.run.sourceCoreDecl_eq] at h
    exact h
  · have Harity0 := B.constructorArityPrefix
    rw [hdecl] at Harity0
    exact Harity0

/-- The origin of every inductive header of the output, for the run's declaration. -/
theorem inductInfosFromRunDecl (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants B.runDecl := by
  have Howners : ConstructorOwnersPresent L.c.env := by
    rw [L.env_eq]; exact Hc.checking.constructorOwners
  obtain ⟨Hsource, Hmetadata, Harity⟩ := B.runSource
  have H := NestedRestorationFolds.inductInfosFromDecl (R := L.constructors) B.runLowering L.Hc'
    L.recursors Hsource Hmetadata B.sourceSyntaxChecked Harity
    Howners rfl B.runRestoration
  rw [L.env_eq] at H
  exact H

/-- The origin of every inductive header of the output, carried to `B.decl` along `run_decl`
(only the families are read). -/
theorem inductInfosFromDecl (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants B.decl := by
  rw [B.run_decl]
  exact B.inductInfosFromRunDecl.withRecs _

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- The installed mutual blocks of the output are closed, given those of the base: the
restored source families are the output's members of the declaration's block
(`FoldSteps.restoredSourceMemberInfos`), and every other header is the base's
(`InductInfosFromDecl.mutualInductivesClosed`). -/
theorem mutualInductivesClosed (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (hsourceClosed : MutualInductivesClosed c.env) : MutualInductivesClosed outEnv := by
  have Howners : ConstructorOwnersPresent L.c.env := by
    rw [L.env_eq]; exact Hc.checking.constructorOwners
  obtain ⟨Hsource, Hmetadata, Harity⟩ := B.runSource
  have Hrestored := B.runRestoration
  have hsourceWF : L.c.env.constants.WF := L.Hc'.checking.tr.map_wf
  obtain ⟨HprimaryMembers, HprimaryParams⟩ :=
    Hrestored.inductives.restoredSourceMemberInfos B.runLowering L.Hc'
      L.recursors Hsource Hmetadata B.sourceSyntaxChecked Harity Howners rfl
      [] (by simp) hsourceWF
  obtain ⟨primaryEntries, HprimaryFresh⟩ :=
    Hrestored.inductives.inductiveFreshExtension hsourceWF
  obtain ⟨auxEntries, HauxFresh⟩ :=
    Hrestored.auxiliaries.recursorFreshExtension (HprimaryFresh.targetWF hsourceWF)
  have hnames : sourceTypes.map (fun type => type.name) =
      B.runDecl.types.map (fun type => type.name) := sourceTypeNames Hsource.types
  have Hmembers : InductiveMemberInfos outEnv
      (B.runDecl.types.map (fun type => type.name)) := by
    rw [← hnames]
    exact HprimaryMembers.mono
      (HauxFresh.preservesSourceFind (HprimaryFresh.targetWF hsourceWF))
  have HmemberParams : ∀ member info,
      member ∈ B.runDecl.types.map (fun type => type.name) →
      outEnv.find? member = some (.inductInfo info) →
      info.numParams = B.runDecl.nparams := by
    intro member info hmember hlookup
    have hmemberSource : member ∈ sourceTypes.map (fun type => type.name) := by
      rwa [hnames]
    rcases HprimaryMembers.find hmemberSource with ⟨primaryInfo, hprimaryLookup⟩
    have houtLookup := HauxFresh.preservesSourceFind
      (HprimaryFresh.targetWF hsourceWF) hprimaryLookup
    rw [hlookup] at houtLookup
    have hinfo : info = primaryInfo :=
      ConstantInfo.inductInfo.inj (Option.some.inj houtLookup)
    subst info
    exact HprimaryParams member primaryInfo hmemberSource hprimaryLookup
  have htypeNames : (B.runDecl.types.map (fun type => type.name)).Nodup := by
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using VEnv.addConstVals_names_nodup Hsource.typesAdded
  have Hfresh := HprimaryFresh.append HauxFresh
  have hcl : MutualInductivesClosed L.c.env := by rw [L.env_eq]; exact hsourceClosed
  have Horigins := B.inductInfosFromRunDecl
  rw [← L.env_eq] at Horigins
  exact InductInfosFromDecl.mutualInductivesClosed Horigins hsourceWF
    (Hfresh.targetWF hsourceWF) hcl
    (fun hfind => Hfresh.preservesSourceFind hsourceWF hfind) Hmembers HmemberParams htypeNames

/-- A new recursor of the output is one of the block's. -/
theorem newRec' (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    {n : Name} {r : RecursorVal} (h1 : outEnv.find? n = some (.recInfo r))
    (h2 : c.env.find? n = none) : r ∈ B.rvals := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at h1
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h2
  rcases B.addInduct.find? hwf h1 with hold | ⟨hmem, -⟩
  · rw [h2] at hold; cases hold
  · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨rval, hrval, h⟩
    · cases h
    · cases h
    · cases h; exact hrval

/-- The major family of every new recursor is present (`RestoredBlock.recMajor`). -/
theorem recMajor' (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
      ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info) :=
  fun h1 h2 => B.recMajor _ (B.newRec' h1 h2)

/-- The primitive names of the output: the restored constants are nonprimitive
(`NestedRun.primitiveSafe`), so the base's primitive invariants persist. -/
theorem primitives (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    B.outVEnv.HasPrimitives ∧ ∀ {n ci}, outEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [] := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
  obtain ⟨entries, H⟩ := B.run.primitiveSafe
  refine ⟨?_, H.safePrimitives hwf Hc.checking.safePrimitives⟩
  intro p hp
  have hnot : ∀ b ∈ B.decl.consts, b.1 ≠ p.1 := by
    intro b hb hbn
    have hname : b.1 ∈ (AddInduct.consts B.ivals B.rvals).map (·.name) := by
      show b.1 ∈ (AddInduct.consts B.addInduct.ivals B.addInduct.rvals).map (·.name)
      rw [B.addInduct.consts_names]
      simp only [VInductDecl.consts, List.mem_append, List.mem_map] at hb
      simp only [List.mem_append, List.mem_map]
      rcases hb with (⟨t, ht, rfl⟩ | ⟨ct, hct, rfl⟩) | ⟨r, hr, rfl⟩
      · exact .inl (.inl ⟨t, ht, rfl⟩)
      · exact .inl (.inr ⟨ct, hct, rfl⟩)
      · exact .inr ⟨r, hr, rfl⟩
    obtain ⟨ci, hci, hcn⟩ := List.mem_map.1 hname
    have ht : outEnv.find? b.1 = some ci := by
      rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, ← hcn]
      exact B.addInduct.find?_self hwf hci
    have hs : c.env.find? b.1 = none := by
      rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, ← hcn]
      exact B.fresh ci hci
    exact H.new_nonprimitive hwf ht hs (hbn ▸ mem_primSpecs_contains hp)
  exact (Hc.checking.hasPrimitives p hp).extend (VEnv.addInduct_le B.installed)
    (VEnv.addInduct_constants_of_not_mem B.installed hnot)

/-- The kernel-level facts of a restored block. -/
theorem kernelFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (_hsource : sourceTypes ≠ []) (hclosed : MutualInductivesClosed c.env) : B.KernelFacts where
  closed := B.mutualInductivesClosed hclosed
  constructorOwners := B.constructorOwnersPresent
  inductInfosFromDecl := B.inductInfosFromDecl
  recMajor := B.recMajor'
  constructorParameterAlignment := fun _ => B.constructorParameterAlignment
  hasPrimitives := B.primitives.1
  safePrimitives := B.primitives.2

/-- The families of the declaration are new `inductInfo`s of the output. -/
theorem cover (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∀ T ∈ B.decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ c.env.find? T.name = none := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
  intro T hT
  obtain ⟨iv, hiv, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_r B.trTypes T hT
  have hname : iv.1.name = T.name := htr.tr.2
  have hmem : ConstantInfo.inductInfo iv.1 ∈ AddInduct.consts B.ivals B.rvals :=
    AddInduct.mem_consts.2 (.inl ⟨iv, hiv, rfl⟩)
  refine ⟨iv.1, ?_, ?_⟩
  · rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, ← hname]
    exact B.addInduct.find?_self hwf hmem
  · have h := B.fresh _ hmem
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, ← hname]
    exact h

/-- **The installation boundary theorem**: the output of a nested restoration is a valid
checking environment with the environment-side facts of the restored block. The checking
invariant is the base translation extended by the restored declaration (`TrEnv'.induct`, the
declaration's `VInductDecl.WF` being `RestoredBlock.wf'`), its installed blocks the base's
complete ones extended by the new block (`InstalledBlocks.addInduct`, whose `hrecShapes` is
`RestoredBlock.recShapes`, auxiliary recursors included, and `hrecK` is `RestoredBlock.recK`).
It takes the base translation, its complete installed blocks and its
constructor parameter alignment (the caller has them from `VEnvs.WF`); `ContextWF` records the
checking invariant at the `.headers` stage only, which `InstalledBlocks.addInduct` cannot
extend. -/
theorem installedFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (hsource : sourceTypes ≠ [])
    (hvisible : c.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (htr : TrEnv c.safety c.env Hc.venv)
    (hblocks : InstalledBlocks c.safety c.env Hc.venv .complete)
    (hparams : ConstructorParameterAlignment c.safety c.env Hc.venv) :
    B.Installed := by
  have K := B.kernelFacts hsource (hblocks.mutualInductivesClosed (by decide))
  have hwf : c.env.constants.WF := Hc.map_wf
  have wf' := B.wf' hsource
  have htrOut : TrEnv c.safety outEnv B.outVEnv := by
    unfold TrEnv; rw [B.quotInit_eq]; exact .induct wf' B.addInduct htr
  have hpres : ∀ {n ci}, c.env.find? n = some ci → outEnv.find? n = some ci := by
    intro n ci h
    have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
    exact B.addInduct.find?_mono hwf h
  have hvis : c.safety ≤ (if B.decl.isUnsafe then DefinitionSafety.unsafe else .safe) := by
    rw [B.isUnsafe_eq]; exact hvisible
  have hblocks' : InstalledBlocks c.safety outEnv B.outVEnv .complete :=
    InstalledBlocks.addInduct hblocks hwf htrOut.toChecking hpres B.le K.inductInfosFromDecl
      B.cover K.closed K.constructorOwners (fun h1 h2 => K.recMajor h1 h2)
      (fun _ => ⟨wf', B.installed, B.compiledWF⟩)
      (fun h => absurd hvis h)
      (fun _ => K.constructorParameterAlignment hparams)
      (fun h1 h2 _ => B.recK _ (B.newRec' h1 h2))
      (fun h1 h2 _ => B.recShapes _ (B.newRec' h1 h2))
  exact {
    checking := htrOut.toCheckingValid K.hasPrimitives K.safePrimitives hblocks'
    closed := K.closed
    constructorOwners := K.constructorOwners
    inductInfosFromDecl := K.inductInfosFromDecl
    cover := B.cover
    recMajor := K.recMajor
    constructorParameterAlignment := K.constructorParameterAlignment }

/-- A new constant of the output is one of the block's (`B.addInduct.find?`). -/
theorem newRec (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    {n : Name} {r : RecursorVal} (h1 : outEnv.find? n = some (.recInfo r))
    (h2 : c.env.find? n = none) : r ∈ B.rvals := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := I.checking.tr.map_wf
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at h1
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h2
  rcases B.addInduct.find? hwf h1 with hold | ⟨hmem, -⟩
  · rw [h2] at hold; cases hold
  · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨rval, hrval, h⟩
    · cases h
    · cases h
    · cases h; exact hrval

/-- **The block certificate of a restored block.** -/
def blockCertificate (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    (hsource : sourceTypes ≠ []) :
    BlockCertificate c.safety c.env Hc.venv B.decl outEnv B.outVEnv where
  wf := B.wf' hsource
  add := B.addInduct
  quotInit_eq := B.quotInit_eq
  checking := I.checking
  closed := I.closed
  constructorOwners := I.constructorOwners
  inductInfosFromDecl := I.inductInfosFromDecl
  cover := I.cover
  recMajor := I.recMajor
  constructorParameterAlignment := I.constructorParameterAlignment
  recK h1 h2 := B.recK _ (B.newRec I h1 h2)
  compiled := B.compiledWF
  newUnsafe ci hci := by rw [B.isUnsafe_eq]; exact B.newUnsafe ci hci
  recShapes h1 h2 := B.recShapes _ (B.newRec I h1 h2)

end RestoredBlock
end VerifyInductive
end Lean4Lean
