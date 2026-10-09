import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension
import Lean4Lean.Verify.Inductive.Install.Result
import Lean4Lean.Verify.Inductive.Prelude.EqSyntax

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! # Checking the prelude's `Eq` declaration

`Init.Prelude` declares `Eq` as an ordinary inductive, before any quotient. This file follows
that one declaration (`PreludeEqShape`) through the executable: the primitive Bool/Nat
recognizer rejects it, lowering leaves it unchanged, and the ordinary path of section 3.1 of
the design notes installs it. From the header translation and the block
installation it derives that every safety-indexed model of the output contains abstract `Eq`
with the prelude's type (`QuotReadyEnvs`), assuming only that `Eq` was absent before.
`addInductiveDeclaration.preludeEqExtensionWF` is the resulting `addDecl` statement. -/

namespace VerifyInductive

private theorem vconstant_eq_of_fields {a b : VConstant}
    (huvars : a.uvars = b.uvars) (htype : a.type = b.type) : a = b := by
  cases a
  cases b
  simp_all

/-- The exact syntax of the prelude's ordinary (non-primitive) `Eq`
declaration, modulo binder and universe-parameter names.  As
submitted by `Init.Prelude`, `Eq` has two parameters (`α` and the left
endpoint `a`) and one index (the right endpoint), so `nparams = 2`. -/
def PreludeEqShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  ∃ u alphaName lhsName rhsName reflAlphaName reflValueName,
    lparams = [u] ∧ nparams = 2 ∧ isUnsafe = false ∧
    types = [{
      name := ``Eq
      type := preludeEqType u alphaName lhsName rhsName
      ctors := [{
        name := ``Eq.refl
        type := preludeEqReflType u reflAlphaName reflValueName }] }]

/-- The concrete `Eq` family arity has the canonical abstract type stored in
`eqConst`. This proof is environment-independent: the arity contains only
sorts and bound variables. -/
theorem preludeEqType_translation
    (env : VEnv) (u alphaName lhsName rhsName : Name) :
    TrExprS env [u] [] (preludeEqType u alphaName lhsName rhsName)
      eqConst.type := by
  unfold preludeEqType eqConst
  change TrExprS env [u] []
    (.forallE alphaName (.sort (.param u))
      (.forallE lhsName (.bvar 0)
        (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default)
      .implicit)
    (.forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
  apply TrExprS.forallE
  · refine ⟨_, VEnv.HasType.sort ?_⟩
    change VLevel.WF 1 (.param 0)
    trivial
  · apply VEnv.IsType.forallE
    · refine ⟨.param 0, ?_⟩
      type_tac
    · apply VEnv.IsType.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
  · exact .sort (by simp [VLevel.ofLevel])
  · apply TrExprS.forallE
    · refine ⟨.param 0, ?_⟩
      type_tac
    · apply VEnv.IsType.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
    · exact .bvar rfl
    · apply TrExprS.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
      · exact .bvar rfl
      · exact .sort rfl

/-- Header translation of the exact prelude `Eq` declaration determines
the abstract family constant uniquely. -/
theorem TrInductDeclHeaders.preludeEqConstant
    (H : TrInductDeclHeaders env lparams nparams types isUnsafe decl envTypes)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    ∃ target : VInductiveType,
      decl.types = [target] ∧ target.name = ``Eq ∧
      target.toVConstant = eqConst := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      hlparams, _hnparams, _hunsafe, htypes⟩
  subst lparams
  subst types
  rcases List.Forall₂.leftSingleton H.types with ⟨target, hdecl, Htarget⟩
  refine ⟨target, hdecl, Htarget.header.name, ?_⟩
  apply vconstant_eq_of_fields
  · simpa [eqConst] using Htarget.header.uvars
  · apply TrExprS.unique Htarget.header.type
    exact preludeEqType_translation env u alphaName lhsName rhsName

/-- The header environment of the exact prelude `Eq` declaration contains one installed
`Eq` entry, whose abstract value is the canonical `eqConst`. -/
theorem HeaderEnvironment.preludeEqEntry
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (Hshape : PreludeEqShape c.lparams nparams indTypes.toList isUnsafe) :
    ∃ (info : InductiveVal) (target : VInductiveType),
      (.inductInfo info, target.toVConstVal) ∈ H.entries ∧
      info.name = ``Eq ∧ target.name = ``Eq ∧
      target.toVConstant = eqConst := by
  rcases TrInductDeclHeaders.preludeEqConstant H.translation Hshape with
    ⟨target, htypes, htargetName, htargetConstant⟩
  have htargetMem : target.toVConstVal ∈ H.entries.map Prod.snd := by
    rw [H.values, VInductDecl.typeConstants, htypes]
    simp
  rcases List.mem_map.mp htargetMem with
    ⟨entry, hentry, hentryValue⟩
  rcases H.sourceAligned with ⟨_numNested, Haligned⟩
  rcases Haligned.originInfo hentry with
    ⟨info, _hinfo, hentryInfo⟩
  have hnames := H.installed.entryNames hentry
  have hinfoName : info.name = ``Eq := by
    rw [hentryInfo] at hnames
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hentryValue,
      htargetName] using hnames
  have hentryEq : entry = (.inductInfo info, target.toVConstVal) := by
    apply Prod.ext
    · exact hentryInfo
    · exact hentryValue
  exact ⟨info, target, hentryEq ▸ hentry, hinfoName,
    htargetName, htargetConstant⟩

/-- The source translation of the exact prelude `Eq` declaration fixes the
abstract declaration: one family `Eq` with the stored type of `Eq`, one
constructor `Eq.refl` with the stored type of `Eq.refl`, two parameters. -/
theorem TrInductDeclCore.preludeEqDecl
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    ∃ family refl, decl.types = [family] ∧ family.name = ``Eq ∧
      family.toVConstant = ⟨1, canonicalEqType⟩ ∧ family.ctors = [refl] ∧
      refl.name = ``Eq.refl ∧ refl.toVConstant = ⟨1, canonicalEqReflType⟩ ∧
      decl.nparams = 2 := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  rcases List.Forall₂.leftSingleton H.types with ⟨family, hdecl, Hfamily⟩
  rcases List.Forall₂.leftSingleton Hfamily.ctors with ⟨refl, hctors, Hrefl⟩
  refine ⟨family, refl, hdecl, Hfamily.header.name, ?_, hctors, Hrefl.name, ?_,
    H.nparams⟩
  · apply vconstant_eq_of_fields
    · simpa using Hfamily.header.uvars
    · exact TrExprS.eq_canonicalEqType Hfamily.header.type
  · apply vconstant_eq_of_fields
    · simpa using Hrefl.uvars
    · exact TrExprS.eq_canonicalEqReflType Hrefl.type

/-- Installation of a block exposes each of its recursors at its exact value. -/
theorem VInductBlock.install_recursorConstant {base env' : VEnv} {block : VInductBlock}
    (H : block.install base = some env') {recursor : VConstVal}
    (hrecursor : recursor ∈ block.recursors) :
    env'.constants recursor.name = some recursor.toVConstant := by
  unfold VInductBlock.install at H
  cases htypes : base.addConstVals block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConstVals block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : ((envCtors.addEliminators block.eliminators).addProjections
          block.projections).addConstVals block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        simpa using VEnv.addConstVals_get hrecursors hrecursor

/-- Installation of a block stores each of its rules. -/
theorem VInductBlock.install_rule {base env' : VEnv} {block : VInductBlock}
    (H : block.install base = some env') {rule : VDefEq} (hrule : rule ∈ block.rules) :
    env'.defeqs rule := by
  unfold VInductBlock.install at H
  cases htypes : base.addConstVals block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConstVals block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : ((envCtors.addEliminators block.eliminators).addProjections
          block.projections).addConstVals block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        exact VEnv.addDefEqRules_defeqs_iff.mpr (.inr hrule)

/-- The safe ordinary installation of the prelude's `Eq` declaration yields models
that contain canonical `Eq` at every safety level (`QuotReadyEnvs`).
Canonical equality follows from the header translation and the certified block
installation. -/
theorem OrdinaryInstallation.extendSafePreludeEq
    {ves : VEnvs}
    (Hrun : OrdinaryInstallation c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (Hshape : PreludeEqShape c.lparams nparams indTypes.toList isUnsafe) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyEnvs ves' ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct (ves.venv .safe) c.lparams
        nparams indTypes.toList isUnsafe (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.generatedRuleTranslation with ⟨T⟩
  let B0 := Hrecursors.blockCertificate T.rules T.rulesWF
  let B := B0.sf_mono (safety := .safe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  rcases Hheaders.preludeEqEntry Hshape with
    ⟨eqInfo, target, hentry, hinfoName, htargetName, htargetConstant⟩
  have hnonempty : indTypes.toList ≠ [] := by
    intro hempty
    rcases Hshape with ⟨u, alphaName, lhsName, rhsName,
      reflAlphaName, reflValueName, _hlparams, _hnparams, _hunsafe, htypes⟩
    rw [hempty] at htypes
    contradiction
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
  have htypeValue : target.toVConstVal ∈ Hheaders.entries.map Prod.snd :=
    List.mem_map.mpr ⟨(.inductInfo eqInfo, target.toVConstVal), hentry, rfl⟩
  have htypesEq : B.installation.venvTypes.constants ``Eq = some eqConst := by
    have hlookup := VEnv.addConstVals_get B.installation.abstract_types htypeValue
    simpa [htargetName, htargetConstant] using hlookup
  have houtEq :
      (Hrecursors.outVEnv.addDefEqRules T.rules).constants ``Eq = some eqConst := by
    apply VEnv.addDefEqRules_le.constants
    apply (VEnv.addConstVals_le B.installation.abstract_recursors).constants
    apply VEnv.addEliminators_addProjections_le.constants
    apply (VEnv.addConstVals_le B.installation.abstract_ctors).constants
    exact htypesEq
  have htypesH : (ves.venv .safe).addConstVals (Hheaders.entries.map Prod.snd) =
      some Hheaders.context.venv := by
    rw [Hheaders.values]; exact Hheaders.translation.typesAdded
  rcases B.extendSafeExact wf hdecl hcompile horigins T.newRecursorsAligned Hrecursors.closed
      (Hrecursors.constructorOwnersPresent wf.constructorOwners)
      hconstructors
      (fun safety => Hrecursors.blockEliminatorsReplay T.rules T.rulesWF
        (wf.mono (DefinitionSafety.le_safe (a := safety))))
      Hrecursors.cover (fun hfind => Hrecursors.ctorOrigin hfind) (B.typesLe htypesH) with
      ⟨ves', wf', hle, hadd, hsafeReplay⟩
  have hsafeEq : (ves'.venv .safe).constants ``Eq = some eqConst :=
    hsafeReplay.constants houtEq
  have hcanonical : QuotReadyEnvs ves' := by
    intro safety
    exact (wf'.mono DefinitionSafety.le_safe).constants hsafeEq
  have hHasCanonical : ∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
      ∀ safety, (ves'.venv safety).HasCanonicalEq := by
    intro ci hfind ⟨hciSafe, u, v, names, huv, hlps, htype⟩ safety
    refine VEnv.HasCanonicalEq.mono (wf'.mono DefinitionSafety.le_safe) ?_
    -- `Eq.rec`: the prelude type translates to the stored type.
    rcases (wf'.tr (safety := .safe)).find? hfind
        (by rw [hciSafe]; exact DefinitionSafety.le_rfl) with
      ⟨recConst, hrecConst, -, hrecUvars, hrecType⟩
    rw [hlps, htype] at hrecType
    have hrecEq : (ves'.venv .safe).constants ``Eq.rec = some ⟨2, canonicalEqRecType⟩ := by
      rw [hrecConst]
      congr 1
      apply vconstant_eq_of_fields
      · simpa [hlps] using hrecUvars.symm
      · exact TrExprS.eq_canonicalEqRecType huv hrecType
    -- The abstract declaration is the canonical one.
    rcases VerifyInductive.TrInductDeclCore.preludeEqDecl R.core Hshape with
      ⟨family, refl, hdeclTypes, hfamilyName, hfamilyConst, hfamilyCtors, hreflName,
        hreflConst, hdeclParams⟩
    -- The generated rule is the stored rule.
    have hinstall : B.block.install (ves.venv .safe) = some (Hrecursors.outVEnv.addDefEqRules T.rules) := B.install
    have hrules : B.block.rules = [canonicalEqRecRule] := by
      have Hcompiles : InductiveSignature.Compiles (ves.venv .safe) decl B.block := by
        simpa [B, B0, BlockCertificate.sf_mono, BlockInstallation.sf_mono,
      BlockCertificate.block] using
          (show OrdinaryCompilationCertificate _ decl B0.block from
            T.compilation hnonempty).canonical
      refine Hcompiles.eqRecRules hdeclTypes hfamilyName (by simp [hfamilyCtors])
        hdeclParams ?_
      intro recursor hrecursor hname
      have hinstalled := hsafeReplay.constants
        (VInductBlock.install_recursorConstant hinstall hrecursor)
      rw [hname, hrecEq] at hinstalled
      have h := Option.some.inj hinstalled
      exact ⟨(congrArg VConstant.uvars h).symm, (congrArg VConstant.type h).symm⟩
    have hrule : (ves'.venv .safe).defeqs canonicalEqRecRule :=
      hsafeReplay.defeqs (VInductBlock.install_rule hinstall (by simp [hrules]))
    -- `Eq.refl` is installed with the translated constructor type.
    have hcert : VEnv.InstalledBelow (ves'.venv .safe) decl := by
      cases hadd with
      | intro hdecl' hcompile' hblock' _helim' hinstall' =>
        exact .intro hdecl'.1 hdecl'.2 hcompile' hblock' hinstall' VEnv.LE.rfl
    have hreflEq : (ves'.venv .safe).constants ``Eq.refl =
        some ⟨1, canonicalEqReflType⟩ := by
      have hfamily : 0 < decl.types.length := by simp [hdeclTypes]
      have hctor : 0 < decl.types[0].ctors.length := by
        simp [hdeclTypes, hfamilyCtors]
      have := hcert.constructorConstant 0 0 hfamily hctor
      simp only [hdeclTypes, hfamilyCtors, List.getElem_cons_zero] at this
      rw [hreflName, hreflConst] at this
      exact this
    exact ⟨hsafeEq, hreflEq, hrecEq, hrule⟩
  exact ⟨ves', wf', hcanonical, hle, ⟨{
    decl := decl
    envTypes := Hheaders.context.venv
    envCtors := R.declared.venvCtors
    source := R.core
    extension := hadd
  }⟩, hHasCanonical⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

set_option linter.unusedSimpArgs false in
/-- Nested-inductive lowering is a literal no-op for the prelude `Eq`
syntax: its recursive constructor occurrence is the family currently being
defined, not a nested occurrence through another inductive. -/
theorem ElimNestedInductive.run'.preludeEqNoop
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (res : ElimNestedInductive.Result)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe)
    (hAbsent : env.find? ``Eq = none)
    (hout : ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }) = .ok res) :
    res.types = types ∧ res.aux2nested.size = 0 := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  have hheaderInstantiate (fv : FVarId) :
      (Expr.forallE lhsName (.bvar 0)
        (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default).instantiate1'
          (.fvar fv) =
        Expr.forallE lhsName (.fvar fv)
          (.forallE rhsName (.fvar fv) (.sort .zero) .default) .default := by
    rfl
  have hctorInstantiate (fv : FVarId) :
      (Expr.forallE reflValueName (.bvar 0)
        (.app (.app (.app (.const ``Eq [.param u]) (.bvar 1)) (.bvar 0))
          (.bvar 0)) .default).instantiate1' (.fvar fv) =
        Expr.forallE reflValueName (.fvar fv)
          (.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.bvar 0))
            (.bvar 0)) .default := by
    rfl
  have hctorBodyInstantiate (fv fv' : FVarId) :
      (Expr.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.bvar 0))
          (.bvar 0)).instantiate1' (.fvar fv') =
        Expr.app (.app (.app (.const ``Eq [.param u]) (.fvar fv)) (.fvar fv'))
          (.fvar fv') := by
    rfl
  have hclose (id id' : FVarId) (hne : id ≠ id') :
      ((({} : LocalContext).mkLocalDecl id reflAlphaName
          (.sort (.param u)) .implicit).mkLocalDecl id' reflValueName
          (.fvar id) .default).mkForall #[.fvar id, .fvar id']
          (.app (.app (.app (.const ``Eq [.param u]) (.fvar id)) (.fvar id'))
            (.fvar id')) =
        preludeEqReflType u reflAlphaName reflValueName := by
    let lctx0 := ({} : LocalContext).mkLocalDecl id reflAlphaName
      (.sort (.param u)) .implicit
    let lctx := lctx0.mkLocalDecl id' reflValueName (.fvar id) .default
    have hmapWF : ({} : PersistentHashMap FVarId LocalDecl).WF := .empty
    have hid : lctx.find? id = some (.cdecl 0 id reflAlphaName
        (.sort (.param u)) .implicit .default) := by
      simp only [lctx, lctx0, LocalContext.mkLocalDecl, LocalContext.find?]
      rw [hmapWF.insert.find?_insert, hmapWF.find?_insert]
      simp [Ne.symm hne]
    have hid' : lctx.find? id' = some (.cdecl 1 id' reflValueName
        (.fvar id) .default .default) := by
      simp only [lctx, lctx0, LocalContext.mkLocalDecl, LocalContext.find?]
      rw [hmapWF.insert.find?_insert]
      simp
    have hfind : ∀ x ∈ [id, id'], ∃ decl, lctx.find? x = some decl := by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, hid⟩
      · exact ⟨_, hid'⟩
    have hnd : [id, id'].Nodup := by simp [hne]
    rw [LocalContext.mkForall]
    change LocalContext.mkBinding false _
      ⟨[id, id'].map Expr.fvar⟩ _ = _
    rw [LocalContext.mkBinding_eq' hfind hnd (by simp [Lean4Lean.Closed])
      (fun x hx d hd => by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl
        · rw [hid] at hd
          cases hd
          trivial
        · rw [hid'] at hd
          cases hd
          trivial)]
    rw [LocalContext.mkBindingList_eq_fold hfind hnd]
    simp [LocalContext.mkBindingList1, hid, hid', Expr.abstract1,
      preludeEqReflType, Ne.symm hne, hne]
  cases fuel with
  | zero =>
    simp [preludeEqType, preludeEqReflType, hheaderInstantiate, hAbsent, Lean.mkFreshId,
      getNGen, setNGen, StateT.run', ElimNestedInductive.run,
      ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
      ElimNestedInductive.run.loop, MonadExcept.throw,
      instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
      StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
      MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
      ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
      ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
      StateT.get, StateT.set, StateT.modifyGet, getThe, modifyGetThe,
      MonadState.get, MonadState.set, MonadState.modifyGet,
      MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet,
      instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
      instMonadStateOfStateTOfMonad, _root_.modify,
      Bind.bind, Monad.toBind, ReaderT.instMonad, StateT.instMonad,
      Except.instMonad, Pure.pure, Applicative.toPure,
      Applicative.toFunctor, Monad.toApplicative,
      Functor.map, StateT.map, Except.bind, Except.pure, Except.map] at hout
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [preludeEqType, preludeEqReflType, hheaderInstantiate, hctorInstantiate,
        hctorBodyInstantiate, hAbsent, Lean.mkFreshId,
        getNGen, setNGen, StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.run.loop, ElimNestedInductive.withParams,
        ElimNestedInductive.withParams.loop,
        ElimNestedInductive.lowerNext, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
        StateT.get, StateT.modifyGet, getThe, modifyGetThe,
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, instMonadStateOfMonadStateOf,
        instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
        _root_.modify, Bind.bind, Monad.toBind, ReaderT.instMonad,
        StateT.instMonad, Except.instMonad, Pure.pure,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        Except.bind, Except.pure, Except.map, Functor.map,
        ElimNestedInductive.lowerInductive,
        ElimNestedInductive.lowerConstructor,
        ElimNestedInductive.replaceAllNested,
        ElimNestedInductive.replaceIfNested,
        ElimNestedInductive.isNestedInductiveApp?,
        ElimNestedInductive.isNestedInductiveAppConst?, Expr.replaceM,
        Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
        Expr.getAppArgs] at hout
    | succ fuel =>
      simp [preludeEqType, preludeEqReflType, hheaderInstantiate, hctorInstantiate,
        hctorBodyInstantiate, hAbsent, Lean.mkFreshId,
        getNGen, setNGen, StateT.run', ElimNestedInductive.run,
        ElimNestedInductive.run.loop, ElimNestedInductive.withParams,
        ElimNestedInductive.withParams.loop,
        ElimNestedInductive.lowerNext, MonadExcept.throw,
        instMonadExceptOfMonadExceptOf, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept, throwThe,
        MonadExceptOf.throw, liftM, monadLift, MonadLiftT.monadLift,
        MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        ReaderT.pure, ReaderT.bind, StateT.pure, StateT.bind,
        StateT.get, StateT.modifyGet, StateT.map, getThe, modifyGetThe,
        MonadState.get, MonadState.modifyGet, MonadStateOf.get,
        MonadStateOf.modifyGet, instMonadStateOfMonadStateOf,
        instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
        _root_.modify, Bind.bind, Monad.toBind, ReaderT.instMonad,
        StateT.instMonad, Except.instMonad, Pure.pure,
        Applicative.toPure, Applicative.toFunctor, Monad.toApplicative,
        Except.bind, Except.pure, Except.map, Functor.map,
        ElimNestedInductive.lowerInductive,
        ElimNestedInductive.lowerConstructor,
        ElimNestedInductive.replaceAllNested,
        ElimNestedInductive.replaceIfNested,
        ElimNestedInductive.isNestedInductiveApp?,
        ElimNestedInductive.isNestedInductiveAppConst?, Expr.replaceM,
        Expr.replaceNoCacheT, Expr.isApp, Expr.getAppFn,
        Expr.getAppArgs] at hout
      subst res
      have habstract (e : Expr) : e.abstract #[] = e := by
        simpa [Expr.abstractN_nil] using Expr.abstractN_eq e []
      simp [preludeEqType, preludeEqReflType, habstract]
      constructor
      · exact hclose _ _ (by simp [NameGenerator.curr, NameGenerator.next])
      · rfl

/-- Predicate-transformer form of the exact `Eq` lowering no-op. -/
theorem ElimNestedInductive.run'.preludeEqNoopWF
    (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe)
    (hAbsent : env.find? ``Eq = none) :
    ((ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray }).WF fun res =>
        res.types = types ∧ res.aux2nested.size = 0 :=
  fun res hout => preludeEqNoop env fuel lparams nparams types isUnsafe res
    Hshape hAbsent hout

/-- The exact prelude `Eq` syntax is necessarily dispatched through the
ordinary branch: it has one universe parameter and two inductive parameters
(`α` and the left endpoint), whereas primitive Bool/Nat recognition requires
both lists to be empty. -/
theorem checkPrimitiveInductive_eq_false_of_preludeEqShape
    (env : Environment)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    Primitive.checkInductive env lparams nparams types isUnsafe =
      .ok false := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  simp [Primitive.checkInductive]
  rfl

/-- The ordinary run of the exact safe prelude `Eq` declaration yields models with
canonical `Eq` at every safety level, extending the source models, together with the
source `AddInduct`. -/
theorem OrdinaryRunResult.extendPreludeEq
    {ves : VEnvs}
    (Hrun : OrdinaryRunResult source sourceEnv
      nparams types outEnv)
    (wf : ves.WF source.env)
    (hsafety : source.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (Hshape : PreludeEqShape source.lparams nparams types
      (source.safety != .safe)) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyEnvs ves' ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct sourceEnv source.lparams
        nparams types (source.safety != .safe) (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  have hnonempty : types ≠ [] := by
    rcases Hshape with
      ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
        _hlparams, _hnparams, _hunsafe, htypes⟩
    rw [htypes]
    simp
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hcSafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hphases⟩
  have wf' : ves.WF c'.env := by
    rw [henv]
    exact wf
  have hcSafety' : c'.safety = .safe := hcSafety.trans hsafety
  have hcVEnv : Hc'.venv = ves.venv .safe := hvenv.trans hsource
  have Hshape' : PreludeEqShape c'.lparams nparams
      types.toArray.toList (source.safety != .safe) := by
    simpa [hlparams] using Hshape
  rcases Hphases.extendSafePreludeEq wf' hcSafety' hcVEnv
      Hshape' with ⟨ves', wf', hEq', hle, Hspec, hcanonical⟩
  refine ⟨ves', wf', hEq', hle, ?_, hcanonical⟩
  simpa only [hlparams, hsource] using Hspec

/-- Complete `AddInductive.run` refinement for the exact prelude `Eq`
declaration, without assuming canonical equality in the source model. -/
theorem AddInductive.run.preludeEqInstalledWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .safe)
    (hsource : Hc.venv = ves.venv .safe)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (Hshape : PreludeEqShape c.lparams nparams types
      (c.safety != .safe))
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
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyEnvs ves' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (SourceAddInduct Hc.venv c.lparams
          nparams types (c.safety != .safe) (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  have hsize : 0 < types.toArray.size := by
    rcases Hshape with
      ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
        _hlparams, _hnparams, _hunsafe, htypes⟩
    rw [htypes]
    change 0 < 1
    decide
  exact (AddInductive.run.sourceAlignedWF nparams numNested Hc
    Hclosed wf.envGhostFree wf.listedConstructorsPresent hctx hsize (by simp [hsafety]) Hinputs).mono fun _ Hrun =>
      Hrun.extendPreludeEq wf hsafety hsource Hshape

/-- `addInductiveAfterLowering` on the exact prelude `Eq` declaration, after a lowering
that produced no auxiliary families, yields well-formed models of the output that extend
the source models and satisfy `QuotReadyOrEqAbsent`, with the source `AddInduct`, and in which
`Eq` is canonical (`HasCanonicalEq`) whenever the installed `Eq.rec` is the prelude's. -/
theorem Environment.addInductiveAfterLowering.preludeEqExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hshape : PreludeEqShape lparams nparams types isUnsafe)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      false fuel res).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyOrEqAbsent outEnv ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
            nparams types false (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  have hisUnsafe : isUnsafe = false := by
    rcases Hshape with
      ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
        _hlparams, _hnparams, hunsafe, _htypes⟩
    exact hunsafe
  subst isUnsafe
  let c := initialContext env lparams .safe false fuel
  let Hc : ContextWF c := by
    simpa [c, initialContext] using
      ContextWF.initial wf .safe lparams false fuel (hmode _)
  have hsource : Hc.venv = ves.venv .safe := rfl
  have Hshape' : PreludeEqShape c.lparams nparams res.types
      (c.safety != .safe) := by
    simpa [c, initialContext, htypes] using Hshape
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
  have Hrun := AddInductive.run.preludeEqInstalledWF
    (c := c) (types := res.types) (ves := ves) nparams 0 Hc wf
    (by rfl) hsource wf.inductivesClosed (by rfl) Hshape' Hinputs
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  simpa [c, initialContext] using Hrun.mono fun _ h => by
    rcases h with ⟨ves', wf', hEq', hle, Hspec, hcanonical⟩
    have Hspec' : Nonempty (SourceAddInduct
        (ves.venv .safe) lparams nparams types false (ves'.venv .safe)) := by
      rw [hsource] at Hspec
      simpa [c, initialContext, htypes] using Hspec
    exact ⟨ves', wf', QuotReadyOrEqAbsent.ofCanonical hEq', hle, Hspec', hcanonical⟩

/-- `addInductive` on the prelude `Eq` declaration yields the conclusion of
`Environment.addInductiveAfterLowering.preludeEqExtensionWF`.  The source checks and the lowering no-op are composed
with the ordinary run that installs canonical abstract equality. -/
theorem Environment.addInductive.preludeEqExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (hAbsent : env.constants.find? ``Eq = none)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe false fuel).WF
      fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyOrEqAbsent outEnv ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
            nparams types false (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  have hAbsentFind : env.find? ``Eq = none := by
    rw [Lean.Kernel.Environment.find?,
      (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hAbsent
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.preludeEqNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape hAbsentFind
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.preludeEqExtensionWF env
        lparams nparams types isUnsafe fuel res ves wf hmode Hshape
        Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Checked `addDecl` on the exact non-primitive prelude `Eq`
declaration.  The primitive recognizer is proved to return `false`, so
the theorem follows the ordinary branch rather than assuming it. -/
theorem addInductiveDeclaration.preludeEqExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (hAbsent : env.constants.find? ``Eq = none)
    (Hshape : PreludeEqShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ QuotReadyOrEqAbsent outEnv ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
            nparams types false (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  have Hrun := Environment.addInductive.preludeEqExtensionWF env
    lparams nparams types isUnsafe fuel ves wf hmode hAbsent Hshape
  have hcheck := checkPrimitiveInductive_eq_false_of_preludeEqShape env Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
