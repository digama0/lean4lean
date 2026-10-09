import Lean4Lean.Verify.Inductive.Install.BlockCertificate

/-!
# Constructor installation on the primitive path

The executable constructor fold on a primitive declaration completes the atomic batch of
`Bool` or `Nat` constants; only then is the ordinary `ContextWF` restored
(`declareConstructors.primitiveWF`). The constructor types `Bool`, `Nat` and `Nat → Nat` are
certified directly (`SourceCtorsCertified.ofPrimitiveShape`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem List.Forall₂.leftPair
    (H : List.Forall₂ R [a₁, a₂] bs) :
    ∃ b₁ b₂, bs = [b₁, b₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  cases H with
  | cons ha₁ Htail =>
    cases Htail with
    | cons ha₂ Hnil =>
      cases Hnil
      exact ⟨_, _, rfl, ha₁, ha₂⟩

private theorem VConstVal.eq_of_fields {a b : VConstVal}
    (hname : a.name = b.name) (huvars : a.uvars = b.uvars)
    (htype : a.type = b.type) : a = b := by
  cases a with
  | mk ac aname =>
    cases b with
    | mk bc bname =>
      cases ac with
      | mk auvars atype =>
        cases bc with
        | mk buvars btype => simp_all

theorem VConstant.eq_of_fields {a b : VConstant}
    (huvars : a.uvars = b.uvars) (htype : a.type = b.type) : a = b := by
  cases a
  cases b
  simp_all

private theorem ConstructorListEntries.primitiveMetadata
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      start ctors entries)
    (hentry : entry ∈ entries) :
    entry.1.safety =
        (if isUnsafe then DefinitionSafety.unsafe else .safe) ∧
      entry.1.levelParams = lparams := by
  induction H with
  | nil => simp at hentry
  | cons Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · simp [AddInductive.constructorInfo, ConstantInfo.safety,
        ConstantInfo.isUnsafe, ConstantInfo.isPartial,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal]
    · exact ih htail

private theorem ConstructorTypeEntries.primitiveMetadata
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (hentry : entry ∈ entries) :
    entry.1.safety =
        (if isUnsafe then DefinitionSafety.unsafe else .safe) ∧
      entry.1.levelParams = lparams := by
  induction H with
  | nil => simp at hentry
  | cons Hhead Htail ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · exact Hhead.primitiveMetadata hhead
    · exact ih htail

private theorem AddInductive.inductiveTypeInfos.primitiveMetadata
    (hinfo : info ∈ (AddInductive.inductiveTypeInfos stats nparams
      indTypes numNested isUnsafe lparams).toList) :
    (ConstantInfo.inductInfo info).safety =
        (if isUnsafe then DefinitionSafety.unsafe else .safe) ∧
      (ConstantInfo.inductInfo info).levelParams = lparams := by
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
    (P := fun candidate =>
      (ConstantInfo.inductInfo candidate).safety =
          (if isUnsafe then DefinitionSafety.unsafe else .safe) ∧
        (ConstantInfo.inductInfo candidate).levelParams = lparams)
    (by
      intro indType numIndices
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial, ConstantInfo.levelParams,
        ConstantInfo.toConstantVal])
    hinfo

/-- Canonical primitive declarations have no cached common parameters. -/
theorem PrimitiveHeaderEnvironment.params_size_eq_zero
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    stats.params.size = 0 := by
  have hparams : stats.params.size = decl.nparams := by
    have hlength := List.Forall₂.length_eq
      H.statsWF.params
    simpa [VInductDecl.paramVars] using hlength
  rw [hparams, H.translation.nparams]
  exact Hshape.2.1

/-- The independently retained parameter scope is empty on the canonical
primitive branch. -/
theorem PrimitiveHeaderEnvironment.parameterScope_eq_nil
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    H.statsWF.parameterScope = [] := by
  have hlength := List.Forall₂.length_eq
    H.statsWF.cachedScope
  have hzero := H.params_size_eq_zero Hshape
  apply List.eq_nil_of_length_eq_zero
  simpa [hzero] using hlength.symm

/-- A raw header translation of a canonical primitive declaration fixes its
complete abstract payload.  Stating the finite fact on the translation lets
it remain available after the primitive constructor check has been turned
into the shared checked formation. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.primitiveAbstractConstants
    (H : TrInductDeclHeaders env lparams nparams types isUnsafe decl envTypes)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    decl.typeConstants ++ decl.constructorConstants =
        primitiveBoolConstants ∨
      decl.typeConstants ++ decl.constructorConstants =
        primitiveNatConstants := by
  rcases Hshape with ⟨hlparams, _hnparams, _hunsafe, htypes⟩
  rcases htypes with hbool | ⟨binderName, binderInfo, hnat⟩
  · have Htypes := H.types
    rw [hbool] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    rcases List.Forall₂.leftPair Htarget.ctors with
      ⟨falseVal, trueVal, htargetCtors, Hfalse, Htrue⟩
    simp only [VInductDecl.typeConstants,
      VInductDecl.constructorConstants]
    rw [hdeclTypes]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [htargetCtors]
    have htargetType : TrExprS env lparams []
        (.sort (.succ .zero)) (.sort (.succ .zero)) :=
      TrExprS.sort (by rw [hlparams]; rfl)
    have htypeEq := TrExprS.unique
      Htarget.header.type htargetType
    have htargetLookup : envTypes.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get H.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hfalseCanonical : TrExprS envTypes lparams []
        (.const ``Bool []) .bool := by
      apply TrExprS.const
      · simpa [Htarget.header.name] using htargetLookup
      · simp [hlparams]
      · simp [Htarget.header.uvars, hlparams]
    have hfalseType := TrExprS.unique
      Hfalse.type hfalseCanonical
    have htrueType := TrExprS.unique
      Htrue.type hfalseCanonical
    left
    simp [primitiveBoolConstants, primitiveBoolType,
      primitiveBoolFalse, primitiveBoolTrue]
    constructor
    · apply VConstVal.eq_of_fields
      · exact Htarget.header.name
      · simpa [hlparams] using Htarget.header.uvars
      · exact htypeEq
    · constructor
      · apply VConstVal.eq_of_fields
        · exact Hfalse.name
        · simpa [hlparams] using Hfalse.uvars
        · exact hfalseType
      · apply VConstVal.eq_of_fields
        · exact Htrue.name
        · simpa [hlparams] using Htrue.uvars
        · exact htrueType
  · have Htypes := H.types
    rw [hnat] at Htypes
    rcases List.Forall₂.leftSingleton Htypes with
      ⟨target, hdeclTypes, Htarget⟩
    rcases List.Forall₂.leftPair Htarget.ctors with
      ⟨zeroVal, succVal, htargetCtors, Hzero, Hsucc⟩
    simp only [VInductDecl.typeConstants,
      VInductDecl.constructorConstants]
    rw [hdeclTypes]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [htargetCtors]
    have htargetType : TrExprS env lparams []
        (.sort (.succ .zero)) (.sort (.succ .zero)) :=
      TrExprS.sort (by rw [hlparams]; rfl)
    have htypeEq := TrExprS.unique
      Htarget.header.type htargetType
    have htargetLookup : envTypes.constants target.name =
        some target.toVConstant := by
      apply VEnv.addConstVals_get H.typesAdded
      simp [VInductDecl.typeConstants, hdeclTypes]
    have hnatCanonical : TrExprS envTypes lparams []
        (.const ``Nat []) .nat := by
      apply TrExprS.const
      · simpa [Htarget.header.name] using htargetLookup
      · simp [hlparams]
      · simp [Htarget.header.uvars, hlparams]
    have hzeroType := TrExprS.unique
      Hzero.type hnatCanonical
    have htargetConstant : target.toVConstant =
        ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) := by
      apply VConstant.eq_of_fields
      · simpa [hlparams] using Htarget.header.uvars
      · exact htypeEq
    have htargetName : target.name = ``Nat := Htarget.header.name
    have hnatLookup : envTypes.constants ``Nat = some
        ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) := by
      rw [← htargetName, ← htargetConstant]
      exact htargetLookup
    have hsuccCanonical : TrExprS envTypes lparams []
        (.forallE binderName (.const ``Nat []) (.const ``Nat [])
          binderInfo) (.forallE .nat .nat) := by
      apply TrExprS.forallE
      · refine ⟨.succ .zero, ?_⟩
        exact VEnv.HasType.const (ls := []) hnatLookup (by simp) rfl
      · refine ⟨.succ .zero, ?_⟩
        exact VEnv.HasType.const (ls := []) hnatLookup (by simp) rfl
      · exact hnatCanonical
      · apply TrExprS.const
        · simpa [Htarget.header.name] using htargetLookup
        · simp [hlparams]
        · simp [Htarget.header.uvars, hlparams]
    have hsuccType := TrExprS.unique
      Hsucc.type hsuccCanonical
    right
    simp [primitiveNatConstants, primitiveNatType,
      primitiveNatZero, primitiveNatSucc]
    constructor
    · apply VConstVal.eq_of_fields
      · exact Htarget.header.name
      · simpa [hlparams] using Htarget.header.uvars
      · exact htypeEq
    · constructor
      · apply VConstVal.eq_of_fields
        · exact Hzero.name
        · simpa [hlparams] using Hzero.uvars
        · exact hzeroType
      · apply VConstVal.eq_of_fields
        · exact Hsucc.name
        · simpa [hlparams] using Hsucc.uvars
        · exact hsuccType

/-- The primitive constructor types are `Bool`, `Nat` and `Nat → Nat`: certified directly. -/
theorem SourceCtorsCertified.ofPrimitiveShape {targets : List VInductiveType}
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (Htranslated : List.Forall₂ (fun source target => List.Forall₂
        (fun ctor ctor' => TrSourceConst venv lparams ctor.name ctor.type ctor')
        source.ctors target.ctors) types targets) :
    SourceCtorsCertified venv lparams types := by
  refine SourceCtorsCertified.ofTranslated Htranslated ?_
  intro owner howner ctor hctor T hT
  rcases Hshape with ⟨-, -, -, hbool | ⟨_, _, hnat⟩⟩
  · rw [hbool] at howner
    simp only [List.mem_singleton] at howner
    subst howner
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hctor
    rcases hctor with rfl | rfl <;> exact ⟨_, TelTrN.const hT⟩
  · rw [hnat] at howner
    simp only [List.mem_singleton] at howner
    subst howner
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hctor
    rcases hctor with rfl | rfl
    · exact ⟨_, TelTrN.const hT⟩
    · exact ⟨_, TelTrN.constArrow hT⟩

/-- The executable constructor declaration fold is verified atomically on a
canonical primitive branch.  Validity is restored only after the family
header and all constructors have been identified as one complete batch of
Bool or Nat constants. -/
theorem AddInductive.declareConstructors.primitiveWF
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (Hchecked : CheckedConstructorCertificate sourceEnv decl H.context.venv
      H.headers.params)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareConstructors stats indTypes isUnsafe
      { c with env := headerEnv }).WF fun outEnv =>
        ∃ _ : PrimitiveConstructorEnvironment H outEnv, True := by
  let mkInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
  have Htranslated := Hchecked.translated H.translation
  have hctors : SourceCtorsCertified H.context.venv c.lparams indTypes.toList :=
    SourceCtorsCertified.ofPrimitiveShape Hshape Htranslated
  have Hfold := AtomicAddConstants.ofConstructorTypes
    (allowPrimitive := c.allowPrimitive) mkInfo H.context.checking
    Htranslated VEnv.LE.rfl
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by
      intro owner i ctor
      simpa [mkInfo, AddInductive.constructorInfo] using hvisible)
  rw [AddInductive.declareConstructors, ← Array.foldlM_toList]
  change (indTypes.toList.foldlM (init := headerEnv) fun
      (env : Environment) (owner : InductiveType) => do
    let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
        (state : Nat × Environment) (ctor : Constructor) => do
      let (cidx, env) := state
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add (.ctorInfo (mkInfo owner cidx ctor)))
    pure env).WF _
  exact Hfold.mono fun outEnv Hout => by
    rcases Hout with
      ⟨venvCtors, entries, hvalues, Hinstalled, Haligned, hproduction,
        hnind⟩
    have hctorValues : entries.map Prod.snd =
        decl.constructorConstants := by
      simpa [VInductDecl.constructorConstants] using hvalues
    have Hcombined := H.installed.append Hinstalled
    have hcombinedValues : (H.entries ++ entries).map Prod.snd =
        decl.typeConstants ++ decl.constructorConstants := by
      simp [H.values, hctorValues]
    let Hbootstrap := Hcombined.toConstantsInstallation hcombinedValues
    have hsourcePrimitives : sourceEnv.HasPrimitives := by
      rw [← H.sourceContextVEnv]
      exact H.sourceContext.checking.hasPrimitives
    have hprimitives : venvCtors.HasPrimitives := by
      rcases H.translation.primitiveAbstractConstants Hshape with hbool | hnat
      · have Hb : PrimitiveConstantsInstallation sourceEnv venvCtors
            primitiveBoolConstants := by
          rw [← hbool]
          exact Hbootstrap
        exact Hb.boolHasPrimitives hsourcePrimitives
      · have Hn : PrimitiveConstantsInstallation sourceEnv venvCtors
            primitiveNatConstants := by
          rw [← hnat]
          exact Hbootstrap
        exact Hn.natHasPrimitives hsourcePrimitives
    have hsafeEntries : ∀ entry ∈ H.entries ++ entries,
        Kernel.Environment.primitives.contains entry.1.name →
        entry.1.safety = .safe ∧ entry.1.levelParams = [] := by
      intro entry hentry _hprimitive
      rcases List.mem_append.mp hentry with hheader | hctor
      · rcases H.infos with ⟨numNested, hproductionHeaders⟩
        have hmember : entry.1 ∈ H.entries.map Prod.fst :=
          List.mem_map.mpr ⟨entry, hheader, rfl⟩
        rw [hproductionHeaders] at hmember
        rcases List.mem_map.mp hmember with ⟨info, hinfo, heq⟩
        rw [← heq]
        have hmetadata :=
          AddInductive.inductiveTypeInfos.primitiveMetadata hinfo
        rcases Hshape with ⟨hlparams, _hnparams, hunsafe, _htypes⟩
        simpa [hlparams, hunsafe] using hmetadata
      · rcases hproduction entry hctor with ⟨info, heq⟩
        have hmetadata := Haligned.primitiveMetadata hctor
        rcases Hshape with ⟨hlparams, _hnparams, hunsafe, _htypes⟩
        simpa [hlparams, hunsafe] using hmetadata
    have hsafe : ∀ {n ci}, outEnv.find? n = some ci →
        Kernel.Environment.primitives.contains n →
        ci.safety = .safe ∧ ci.levelParams = [] :=
      Hcombined.safePrimitives
        H.sourceContext.checking.tr.map_wf
        H.sourceContext.checking.safePrimitives hsafeEntries
    have hsourceMapWF := H.sourceContext.checking.tr.map_wf
    have houtWF : outEnv.constants.WF := Hcombined.targetMapWF hsourceMapWF
    have hindicesSize : stats.nindices.size = indTypes.size := by
      calc
        stats.nindices.size = decl.types.length := by
          rw [Array.size_eq_length_toList, H.statsWF.indices,
            List.length_map]
        _ = indTypes.toList.length :=
          (List.Forall₂.length_eq H.translation.types).symm
        _ = indTypes.size := by simp
    rcases H.sourceAligned with ⟨numNested, Hheaders⟩
    have hheaderNotCtor : ∀ entry ∈ H.entries, ∀ info : ConstructorVal,
        entry.1 ≠ .ctorInfo info := by
      intro entry hentry info heq
      rcases Hheaders.originInfo hentry with ⟨_, _, hentryInfo⟩
      rw [hentryInfo] at heq
      cases heq
    have howners : ConstructorOwnersPresent outEnv := by
      apply Hcombined.constructorOwnersPresent hsourceMapWF
        H.sourceContext.checking.constructorOwners
      intro entry hentry info hinfo
      rcases List.mem_append.mp hentry with hheader | hctor
      · exact absurd hinfo (hheaderNotCtor entry hheader info)
      rcases Haligned.ownerOfEntry hctor with
        ⟨owner, howner, installedInfo, hentryInfo, hownerName, hmem, hunsafe⟩
      have hinfoEq : info = installedInfo := by
        rw [hentryInfo] at hinfo
        exact (ConstantInfo.ctorInfo.inj hinfo).symm
      subst info
      rcases inductiveTypeInfos_owner stats nparams indTypes numNested isUnsafe
          c.lparams hindicesSize howner with
        ⟨ownerInfo, hownerInfo, hname, hctors, hownerUnsafe⟩
      rcases Hheaders.findInfo hownerInfo with ⟨value, hheaderEntry⟩
      refine ⟨ownerInfo, ?_, by rw [hctors]; exact hmem, hunsafe.trans hownerUnsafe.symm⟩
      rw [hownerName, ← hname]
      exact Hcombined.findEntry hsourceMapWF
        (List.mem_append_left _ hheaderEntry)
    have hrecursors : RecursorEnvCoherent c.safety outEnv.constants venvCtors := by
      apply Hcombined.recursorEnvCoherent hsourceMapWF
      · intro entry hentry rec heq
        rcases List.mem_append.mp hentry with hheader | hctor
        · rcases Hheaders.originInfo hheader with ⟨_, _, hentryInfo⟩
          rw [hentryInfo] at heq
          cases heq
        · rcases hproduction entry hctor with ⟨cinfo, hcinfo⟩
          rw [hcinfo] at heq
          cases heq
      · have h := H.sourceContext.checking.recursors
        rwa [H.sourceContextVEnv] at h
    have hquot : outEnv.quotInit = true →
        QuotEnvCoherent outEnv.constants venvCtors := by
      apply Hcombined.quotEnvCoherent hsourceMapWF hrecursors.heads
      have h := H.sourceContext.checking.quot
      rwa [H.sourceContextVEnv] at h
    let Hcontext := H.context.withEnv (Hinstalled.checking H.context.checking) Hinstalled.le
      (Hinstalled.ctorTelescopes H.context.checking H.context.ctorTelescopes (Haligned.ctorTelescopeSteps hctors))
    have hctorsAdded : H.context.venv.addConstVals
        decl.constructorConstants = some venvCtors := by
      rw [← hctorValues]
      exact Hinstalled.abstract
    let Htranslation : TrInductDeclConstructors H.context.venv c.lparams
        indTypes.toList decl venvCtors := {
      ctorsAdded := hctorsAdded
      types := Htranslated }
    refine ⟨{
      venvCtors := venvCtors
      entries := entries
      values := hctorValues
      installed := Hinstalled
      sourceAligned := by simpa [mkInfo] using Haligned
      infos := hproduction
      nonInductive := hnind
      translation := Htranslation
      primitiveConstants := H.translation.primitiveAbstractConstants Hshape
      safeEntries := hsafeEntries
      context := Hcontext
      contextVEnv := rfl
      contextMLCtx := rfl
      validCore := ⟨Hcombined.checking (H.sourceContextVEnv ▸ H.sourceContext.checking.tr),
        hprimitives, hsafe⟩
      owners := howners
      equationHeads := hrecursors.heads
      quot := hquot }, trivial⟩

end VerifyInductive
end Lean4Lean
