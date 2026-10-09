import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorFields
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Recursor.Signature.Constructors

/-! Inversion of the executable's pre-installation recursor type check.

`RecursorConstruction.recursorTypes` records the translation of every closed generated
recursor type checked by `checkRecursorTypes`. Decomposing that translation along the five
executable binder groups gives translations of each parameter, motive, minor, index and major
domain in the abstract contexts used by the generator. Translations are syntactically unique
(`TrExprS.uniqueS`), so the parameter and motive groups coincide with the parameter scope and
the generated motives chosen earlier. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The executable's recursor type of each family translates, in the recursor-checking
environment at the recursor's universe parameters, to a closed type (from the executable's
check of the recursor type). -/
theorem RecursorConstruction.recursorTypeTranslation
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < indTypes.size) :
    ∃ type : VExpr,
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
        type ∧
      R.context.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        type := by
  have h := H.recursorTypes.typeAt owner howner
  rwa [H.localExtends.lparams_eq] at h

/-- Five-group decomposition of the checked recursor type, obtained only by inverting its
translation along the binder groups of `declareRecursors`. -/
theorem RecursorConstruction.recursorTelescope
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ target : VExpr,
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
        target ∧
      Nonempty (RecursorTypeTelescope R.context.venv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
        target stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨target, Htr, Htype⟩ := H.recursorTypeTranslation owner hsourceOwner
  let Hsel := H.bindings.toRecursorBinderGroups H.localWF H.params owner howner
  have hnoalias := H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner
  have Htel := Hsel.forallTelescope
    (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  rw [Hsel.residual_eq_concreteRecursorResult howner hnoalias] at Htel
  have Htel' : Expr.ForallTelescope
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (stats.params.size + (H.recInfos.map (·.motive)).size +
        (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size + 1)
      (concreteRecursorResult (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) := Htel
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel' Htr Htype
  rcases TrExprS.forallTelescope_shape_with_context Htel' Htr with
    ⟨domains, result, hlen, htarget, Hresult⟩
  rcases List.exists_append_five_of_length_eq domains stats.params.size
      (H.recInfos.map (·.motive)).size (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size 1 hlen with
    ⟨params, motives, minors, indices, major, hdomains, hp, hm, hmi, hi, hma⟩
  refine ⟨target, Htr, ⟨⟨params, motives, minors, indices, major, result, ?_, hp, hm, hmi, hi,
    hma, Htyped, ?_⟩⟩⟩
  · simpa [hdomains] using htarget
  · simpa [hdomains] using Hresult

/-- The parameter group of the checked recursor type is the recursor parameter context: both
translate the same closed parameter prefix. -/
theorem RecursorConstruction.recursorTelescope_params
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) :
    T.params = H.parameterSuffix.parameterDecls.toCtx.reverse := by
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have Htr := T.typed.translation
  rw [T.target_eq, VExpr.wrapForalls_append, VExpr.wrapForalls_append, VExpr.wrapForalls_append,
    VExpr.wrapForalls_append] at Htr
  have Htel := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
      H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
      H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
      H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
          H.recInfos[owner]!.major))
  have Hdomains := (TrExprS.forallDomainsOnly Htel T.params_length Htr).1
  rw [H.params.forallDomainsOnly H.localWF hparams] at Hdomains
  have Hcached := H.sourceParameterTranslation
  rw [← H.parameterDomains] at Hcached
  have heq := Hdomains.uniqueS Hcached
  exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) T.params_length
    (by simp [H.parameterDomains, H.sourceParameterCount])
    (by simpa using heq)

/-- The motive group of the checked recursor type is the generator's motive
list: both translate the same parameter-closed motive telescope. -/
theorem RecursorConstruction.recursorTelescope_motives
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (g : InductiveSignature.Instance s)
    (hp : s.params = R.parameterScope.toCtx.reverse)
    (hf : s.families = H.families)
    (hl : g.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some g.targetLevel) :
    T.motives = g.motives := by
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have hmotives : H.bindings.motives.fvars.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp houter).1).2.1
  have Htr := T.typed.translation
  rw [T.target_eq, VExpr.wrapForalls_append, VExpr.wrapForalls_append, VExpr.wrapForalls_append,
    VExpr.wrapForalls_append] at Htr
  let inner := H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
        H.recInfos[owner]!.major)
  have Htel := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) inner)
  have Hres := TrExprS.forallTelescope_residual Htel T.params_length Htr
  have HtelM := (H.bindings.motives.mkForall_forallTelescope H.localWF inner).abstractN
    H.params.fvars
  have Hdom := (TrExprS.forallDomainsOnly HtelM (by simpa using T.motives_length) Hres).1
  rw [Expr.forallDomainsOnly_abstractN, H.bindings.motives.forallDomainsOnly H.localWF hmotives]
    at Hdom
  have hmotivesClosed : Closed (H.localContext.lctx.mkForall (H.recInfos.map (·.motive))
      (.sort .zero)) :=
    H.bindings.motives.mkForall_closed H.localWF hmotives H.recursorWF.lctxClosed trivial
  rw [Expr.abstractN_eq_abstractList_of_closed hparams hmotivesClosed] at Hdom
  have Hgen := (H.generatedMotivesTranslation g hp hf hl hu).1
  have hp' : g.params = H.parameterSuffix.parameterDecls.toCtx.reverse := by
    rw [InductiveSignature.Instance.params, hp, hl, H.parameterDomains]
  rw [H.recursorEnv, hp', ← H.recursorTelescope_params T] at Hgen
  have heq := Hdom.uniqueS Hgen
  exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) T.motives_length
    (by simp [InductiveSignature.Instance.motives, hf]) (by simpa using heq)

/-- `RecursorBinderGroups.minorBinderAt` before `inferImplicit`: the flat minor slot of the
recursor type is the minor's declared type closed over parameters, motives and the strictly
earlier minors. -/
theorem RecursorBinderGroups.minorBinderAtRaw
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : FVarDeclAt c (recInfos.flatMap (·.minors)) minorIdx) :
    Expr.ForallBinderAt
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive recInfos[ownerIdx]!.indices)
           recInfos[ownerIdx]!.major))
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractN
        (H.params.fvars ++ H.motives.fvars ++ H.minors.fvars.take minorIdx)) := by
  let minorBody :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) minorBody
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have hminorFVars : minorIdx < H.minors.fvars.length := by
    rw [← H.minors.size]
    exact D.inBounds
  have Hminor : Expr.ForallBinderAt minorSource minorIdx
      (D.type.abstractN (H.minors.fvars.take minorIdx)) := by
    exact H.minors.forallBinderAt parts.minors D (body := minorBody)
  have HminorMotives := Hminor.abstractN H.motives.fvars 0
  have hdomainMotives :
      (D.type.abstractN (H.minors.fvars.take minorIdx)).abstractN
          H.motives.fvars minorIdx =
        D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.motives.fvars)
      (inner := H.minors.fvars.take minorIdx) (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars)] using Hclose
  have Hmotives := H.motives.forallTelescope minorSource
  have HthroughMotives := Hmotives.prependBinderAt (by
    simpa [Nat.zero_add, hdomainMotives] using HminorMotives)
  have HthroughParams := HthroughMotives.abstractN H.params.fvars 0
  have hdomainParams :
      (D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractN
          H.params.fvars (H.motives.fvars.length + minorIdx) =
        D.type.abstractN
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars ++ H.minors.fvars.take minorIdx)
      (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars), List.append_assoc]
      using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  have hmotivesLength : H.motives.fvars.length =
      (recInfos.map (·.motive)).size := by
    rw [← H.motives.size]
  have hmotivesLength' : H.motives.fvars.length = recInfos.size := by
    simpa using hmotivesLength
  have HrawBase := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, Nat.add_assoc] using HthroughParams)
  have hdomainParamsStats :
      (D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractN
          H.params.fvars (recInfos.size + minorIdx) =
        D.type.abstractN
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    rw [← hmotivesLength']
    exact hdomainParams
  rw [hdomainParamsStats] at HrawBase
  have Hraw : Expr.ForallBinderAt
      (c.lctx.mkForall stats.params motiveSource)
      (H.params.fvars.length + (H.motives.fvars.length + minorIdx))
      (D.type.abstractN
        (H.params.fvars ++ (H.motives.fvars ++
          H.minors.fvars.take minorIdx))) := by
    simpa [hparamsLength, hmotivesLength, Nat.add_assoc] using
      HrawBase
  simpa [motiveSource, minorSource, minorBody, hparamsLength,
    hmotivesLength, Nat.add_assoc] using Hraw

/-- Sequential-model form of `minorBinderAtRaw` for a locally closed context. -/
theorem RecursorBinderGroups.minorBinderAtRawList
    (H : RecursorBinderGroups c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias) (hl : LocalContext.LctxClosed c.lctx)
    (D : FVarDeclAt c (recInfos.flatMap (·.minors)) minorIdx) :
    Expr.ForallBinderAt
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive recInfos[ownerIdx]!.indices)
           recInfos[ownerIdx]!.major))
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars ++ H.minors.fvars.take minorIdx)) := by
  have h := H.minorBinderAtRaw hnoalias D
  have hall : (H.params.fvars ++ (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))).Nodup := hnoalias
  have hnodup : (H.params.fvars ++ H.motives.fvars ++
      H.minors.fvars.take minorIdx).Nodup := by
    rw [List.append_assoc]
    exact List.Nodup.sublist (List.Sublist.append (List.Sublist.refl _)
      (List.Sublist.append (List.Sublist.refl _)
        ((List.take_sublist _ _).trans (List.sublist_append_left _ _)))) hall
  rwa [Expr.abstractN_eq_abstractList_of_closed hnodup (D.closed hl)] at h

theorem RecursorTypeTelescope.take_minorPrefix
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (h : minorIdx ≤ T.minors.length) :
    (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).take
        (numParams + numMotives + minorIdx) =
      T.params ++ T.motives ++ T.minors.take minorIdx := by
  have hp := T.params_length
  have hm := T.motives_length
  simp only [List.append_assoc]
  rw [List.take_append, List.take_of_length_le (by omega),
    List.take_append, List.take_of_length_le (by omega),
    List.take_append_of_le_length (by omega),
    show numParams + numMotives + minorIdx - T.params.length - T.motives.length = minorIdx by omega]

theorem RecursorTypeTelescope.getElem_minor
    (T : RecursorTypeTelescope env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (h : minorIdx < T.minors.length)
    (hi : numParams + numMotives + minorIdx <
      (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).length) :
    (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major)[numParams + numMotives + minorIdx] =
      T.minors[minorIdx] := by
  have hp := T.params_length
  have hm := T.motives_length
  simp only [List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
    List.getElem_append_left (by omega)]
  congr 1
  omega

/-- The flat minor slot of the checked recursor type translates the minor's declared type,
closed over parameters, motives and earlier minors, in the generator's abstract context for
that slot. -/
theorem RecursorConstruction.recursorTelescope_minor
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx) :
    TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx) [])
      (D.type.abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take minorIdx))
      (T.minors[minorIdx]'(by rw [T.minors_length]; exact D.inBounds)) := by
  let Hsel := H.bindings.toRecursorBinderGroups H.localWF H.params owner howner
  have hnoalias := H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner
  have Hb := Hsel.minorBinderAtRawList hnoalias H.recursorWF.lctxClosed D
  have Htr := T.typed.translation
  rw [T.target_eq] at Htr
  have hminor : minorIdx < T.minors.length := by rw [T.minors_length]; exact D.inBounds
  have hi : stats.params.size + (H.recInfos.map (·.motive)).size + minorIdx <
      (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).length := by
    have hmin := T.minors_length
    simp only [List.length_append, T.params_length, T.motives_length, T.minors_length,
      T.indices_length, T.major_length]
    omega
  have Ht := Hb.translation Htr hi
  rw [T.take_minorPrefix minorIdx (Nat.le_of_lt hminor), T.getElem_minor minorIdx hminor hi] at Ht
  exact Ht

/-- The field domains of a flat minor slot of the checked recursor type are the
`insertBinders` lift of the minor's field domains (`declFieldDomains`); the residual
is the translation of the hypothesis telescope and motive application closed
over the fields. -/
theorem RecursorConstruction.recursorTelescope_minorFields
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ residual : VExpr,
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D.inBounds) =
        VExpr.wrapForalls fields residual ∧
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields) [])
        (((S.sourceContext.mkForall S.hypotheses S.motiveApp).abstractN
          S.fields_bound.fvars).abstractList ys S.fields.size)
        residual := by
  intro S fields ys
  have Hminor := H.recursorTelescope_minor howner T minorIdx D
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨horigin, _, _, _, _, _, _, _, _, _, _, _, _, _, hsourceLE⟩ :=
    H.minorSources.rows mowner hmowner hsourceOwner localIndex hlocal
  let HS := H.sourceMinorTyping mowner hmowner localIndex hlocal
  have hsource : D.type = S.sourceType := by
    rw [hD, ← horigin, ← S.unannotated_eq, HS.semantic.sourceType_consumeTypeAnnotations_eq_self]
  rw [hsource] at Hminor
  have hminor : minorIdx < (H.recInfos.flatMap (·.minors)).size := D.inBounds
  have Htel := (S.fieldTelescope (S.sourceContext.mkForall S.hypotheses S.motiveApp)).abstractList ys
  rw [← S.sourceType_eq, Nat.zero_add] at Htel
  obtain ⟨F, residual, hF, heq, Hres⟩ := TrExprS.forallTelescope_shape_with_context Htel Hminor
  have Hdom := (TrExprS.forallDomainsOnly Htel hF (heq ▸ Hminor)).1
  have hsort : S.sourceContext.mkForall S.fields (.sort .zero) =
      H.localContext.lctx.mkForall S.fields (.sort .zero) := by
    rw [← S.sourceContext_eq]
    exact (S.fields_bound.mkForall_mono hsourceLE (.sort .zero)).symm
  rw [Expr.forallDomainsOnly_abstractList, S.sourceType_eq, ← S.sourceContext_eq,
    S.fields_bound.forallDomainsOnly S.sourceFullWF S.fields_nodup, S.sourceContext_eq, hsort]
    at Hdom
  have hmotivesLen : H.bindings.motives.fvars.length = T.motives.length := by
    rw [H.bindings.motives.length_fvars, T.motives_length]
  have hminorsLen : (H.bindings.flatMinors.fvars.take minorIdx).length =
      (T.minors.take minorIdx).length := by
    rw [List.length_take, List.length_take, H.bindings.flatMinors.length_fvars, T.minors_length]
  have Htemplate := H.minorFieldsTemplate mowner hmowner localIndex hlocal
    (T.motives ++ T.minors.take minorIdx)
    (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx)
    (by simp only [List.length_append, hmotivesLen, hminorsLen])
  have hinserted : (T.motives ++ T.minors.take minorIdx).length =
      (H.recInfos.map (·.motive)).size + minorIdx := by
    simp only [List.length_append, T.motives_length, List.length_take, T.minors_length]
    omega
  rw [H.recursorEnv, ← H.recursorTelescope_params T, hinserted, ← List.append_assoc,
    ← List.append_assoc] at Htemplate
  have hF' : F = fields :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := []) hF (by
      simp only [fields, InductiveSignature.insertBinders, List.length_map, List.length_zipIdx,
        H.sourceFields_length]
      exact hF.symm ▸ rfl) (by simpa [ys, fields, List.append_assoc] using Hdom.uniqueS Htemplate)
  refine ⟨residual, by rw [heq, hF'], ?_⟩
  rw [← hF']
  simpa [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc] using Hres

/-- The executable's universe arguments translate to the recursor's abstract level list, for
any checked header statistics (`HeaderStatsWF`) over the same universe parameter names. -/
theorem checkInductiveTypes.loopInd.HeaderStatsWF.recursorLevelTranslation_general
    {env : VEnv} {Us : List Name} {Δ : VLCtx} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat}
    (H : checkInductiveTypes.loopInd.HeaderStatsWF env Us Δ stats decl depth)
    (hlparams : Us.Nodup) {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel Us elimLevel) :
    stats.levels.mapM (VLevel.ofLevel (AddInductive.getRecLevelParams elimLevel Us)) =
      some (recursorDeclarationAbstractLevels Us Helim) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using H.levelTranslation
  | param fresh =>
    have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim H.levelTranslation
    simpa [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using hshifted
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem RecursorConstruction.statsLevelsTranslation
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) :
    stats.levels.mapM (VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)) =
      some (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) :=
  R.statsWF.recursorLevelTranslation_general H.lparamsNodup H.elimLevelAdmissible

/-- The motive application of a minor: the motive of the minor's family applied to the indices
of the traversal's terminal family application, then to the constructor applied to the
parameters and fields. -/
theorem RecursorConstruction.minorMotiveAppForm
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let HS := H.sourceMinorTyping mowner hmowner localIndex hlocal
    S.motiveApp = Expr.app
      (mkAppN H.recInfos[mowner]!.motive
        (AddInductive.getIIndices stats HS.semantic.traversal.terminal).2)
      (mkAppN (mkAppN (.const S.constructor.name stats.levels) stats.params) S.fields) := by
  intro S HS
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, _, _, hmotiveApp, _, _, _⟩ :=
    H.minorSources.rows mowner hmowner hsourceOwner localIndex hlocal
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  subst heq
  have hfst := checkPositivityStep.getIIndices.fst_eq_of_valid (H.constructorTerminalOwner mowner hmowner localIndex hlocal HS)
  rw [hmotiveApp]
  rcases hindices : AddInductive.getIIndices stats HS.semantic.traversal.terminal with
    ⟨motiveOwner, indices⟩
  have : motiveOwner = mowner := by simpa [hindices] using hfst
  subst this
  rfl

/-- Closing a list of distinct free variables over itself yields the descending de Bruijn spine
above the abstraction depth. -/
theorem Expr.abstractList_fvar_spine (fvs : List FVarId) (hnd : fvs.Nodup) (k : Nat) :
    (fvs.map Expr.fvar).map (fun e => e.abstractList fvs k) =
      List.ofFn fun j : Fin fvs.length => Expr.bvar (k + (fvs.length - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < fvs.length := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i hi

/-- Closing a prefix of distinct free variables over a longer distinct list
places each at its descending position above the trailing variables. -/
theorem Expr.abstractList_fvar_prefix_spine (fvs rest : List FVarId)
    (hnd : (fvs ++ rest).Nodup) (k : Nat) :
    (fvs.map Expr.fvar).map (fun e => e.abstractList (fvs ++ rest) k) =
      List.ofFn fun j : Fin fvs.length => Expr.bvar ((k + rest.length) + (fvs.length - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < fvs.length := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    have h := Expr.abstractList_fvar_getElem hnd (fvs := fvs ++ rest) i (by simp; omega) (k := k)
    rw [List.getElem_append_left hi] at h
    rw [h]
    congr 1
    simp only [List.length_append]
    omega

/-- Bound variables below the abstraction depth are untouched. -/
theorem Expr.abstractList_bvar_spine (n below : Nat) (fvs : List FVarId) (k : Nat)
    (h : below + n ≤ k) :
    (List.ofFn fun j : Fin n => Expr.bvar (below + (n - 1 - j))).map
        (fun e => e.abstractList fvs k) =
      List.ofFn fun j : Fin n => Expr.bvar (below + (n - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_bvar_lt fvs (by omega)

/-- The motive application of a minor after closing hypotheses, fields, and
the outer parameter, motive and earlier-minor binders: the motive is the bound variable of the
family's motive, the constructor is applied to the bvar spine of parameters and fields, and the
indices are closed pointwise. -/
theorem RecursorConstruction.minorResidualSource
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (minorIdx : Nat) (hminor : minorIdx < (H.recInfos.flatMap (·.minors)).size)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let HS := H.sourceMinorTyping mowner hmowner localIndex hlocal
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ((S.motiveApp.abstractN S.hypotheses_bound.fvars).abstractN S.fields_bound.fvars
        S.hypotheses.size).abstractList ys (S.fields.size + S.hypotheses.size) =
      Expr.app
        (Expr.mkAppList
          (.bvar (S.fields.size + S.hypotheses.size + minorIdx +
            ((H.recInfos.map (·.motive)).size - 1 - mowner)))
          ((AddInductive.getIIndices stats HS.semantic.traversal.terminal).2.toList.map fun arg =>
            (arg.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
              (S.fields.size + S.hypotheses.size)))
        (Expr.mkAppList (.const S.constructor.name stats.levels)
          ((List.ofFn fun k : Fin stats.params.size =>
              Expr.bvar (((H.recInfos.map (·.motive)).size + minorIdx + S.fields.size +
                S.hypotheses.size) + (stats.params.size - 1 - k))) ++
            (List.ofFn fun j : Fin S.fields.size =>
              Expr.bvar (S.hypotheses.size + (S.fields.size - 1 - j))))) := by
  intro S HS ys
  have hclosed : Closed S.motiveApp 0 := by
    have h := HS.semantic.motivePreTranslation.closed
    rw [HS.semantic.terminalWF.mlctx.noBV] at h
    simpa using h
  rw [Expr.abstractN_eq_abstractList_of_closed S.hypotheses_nodup hclosed,
    HS.semantic.abstractHypotheses_motiveApp,
    Expr.abstractN_eq_abstractList S.fields_nodup _ _
      (by rw [hclosed.looseBVarRange_zero]; exact Nat.zero_le _),
    H.minorMotiveAppForm mowner hmowner localIndex hlocal]
  -- Freshness of the fields relative to the traversal root.
  have hfieldsFvars : HS.semantic.fieldsRecent.fvars = S.fields_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq
      HS.semantic.fieldsRecent.toFVarArrayAfter.toFVarArrayIn S.fields_bound rfl
  have hrootFresh : ∀ fv, fv ∈ HS.semantic.rootWF.mlctx.vlctx.fvars →
      fv ∉ S.fields_bound.fvars := by
    intro fv hroot hfield
    rw [← hfieldsFvars] at hfield
    apply HS.semantic.fieldsRecent.fresh fv hfield
    rw [← HS.semantic.rootWF.lctx_eq, HS.semantic.rootWF.mlctx_wf.tr.fvars_eq]
    exact hroot
  -- The motive is a root free variable.
  obtain ⟨mfv, hhead, hmroot⟩ := HS.semantic.motiveHeadRoot
  have hmotiveForm := H.minorMotiveAppForm mowner hmowner localIndex hlocal
  have hmotiveLt : mowner < (H.recInfos.map (·.motive)).size := by simpa using hmowner
  obtain ⟨hmfvLt, hmotiveGet⟩ := H.bindings.motives.getElem_eq_fvar mowner hmotiveLt
  have hmotive : H.recInfos[mowner]!.motive = .fvar (H.bindings.motives.fvars[mowner]'hmfvLt) := by
    have h := hmotiveGet
    simpa [Array.getElem_map, getElem!_pos H.recInfos mowner hmowner] using h
  have hmfv : mfv = H.bindings.motives.fvars[mowner]'hmfvLt := by
    have h := hhead
    rw [hmotiveForm, hmotive] at h
    simp only [Expr.getAppFn, Expr.getAppFn_mkAppN] at h
    exact (Expr.fvar.inj h).symm
  -- Parameters are root free variables.
  have hstats : HS.semantic.traversal.stats = stats := by
    have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
    obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, hst, _, _, _, _, _⟩ :=
      H.minorSources.rows mowner hmowner hsourceOwner localIndex hlocal
    have heq : traversal = HS.semantic.traversal :=
      Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
    rw [← heq]
    exact hst
  have hparamsList : stats.params.toList = H.params.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList H.params.expressions
  have hparamsRoot : ∀ fv ∈ H.params.fvars, fv ∈ HS.semantic.rootWF.mlctx.vlctx.fvars := by
    intro fv hfv
    have hids : ExprArrayFVarIds HS.semantic.traversal.stats.params = H.params.fvars := by
      rw [hstats]
      simp only [ExprArrayFVarIds, hparamsList, List.map_map]
      simp [Function.comp_def, recursorFVarId]
    have hmem : fv ∈ (HS.semantic.parameterSuffix.ambientDecls ++
        HS.semantic.parameterSuffix.parameterDecls).fvars := by
      rw [VLCtx.fvars_append, HS.semantic.parameterSuffix.parameterDecls_fvars, hids]
      apply List.mem_append_right
      rwa [List.mem_reverse]
    rwa [← HS.semantic.parameterSuffix.context] at hmem
  -- Lengths and distinctness of the outer binders.
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hys : ys.Nodup := by
    apply List.Nodup.sublist _ houter
    exact List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _)
  have hparamsLen : H.params.fvars.length = stats.params.size := H.params.length_fvars
  have hmotivesLen : H.bindings.motives.fvars.length = (H.recInfos.map (·.motive)).size :=
    H.bindings.motives.length_fvars
  have hminorsLen : (H.bindings.flatMinors.fvars.take minorIdx).length = minorIdx := by
    rw [List.length_take, H.bindings.flatMinors.length_fvars]
    omega
  -- Component computations.
  have hconst : ∀ (fvs : List FVarId) (k : Nat),
      (Expr.const S.constructor.name stats.levels).abstractList fvs k =
        .const S.constructor.name stats.levels :=
    fun fvs k => Expr.abstractList_eq_self_of_abstract1 _ (fun _ _ => rfl) fvs k
  have hfvarField : ∀ fv, fv ∉ S.fields_bound.fvars → ∀ k,
      (Expr.fvar fv).abstractList S.fields_bound.fvars k = .fvar fv := by
    intro fv hfv k
    exact FVarsIn.abstractList_eq_self (e := .fvar fv) (by simpa [FVarsIn] using hfv) (by simp [Closed])
  have hmotiveAbs : ((H.recInfos[mowner]!.motive.abstractList S.fields_bound.fvars
      S.hypotheses.size).abstractList ys (S.fields.size + S.hypotheses.size)) =
      .bvar (S.fields.size + S.hypotheses.size + minorIdx +
        ((H.recInfos.map (·.motive)).size - 1 - mowner)) := by
    rw [hmotive, hfvarField _ (hmfv ▸ hrootFresh mfv hmroot)]
    have hpos : H.params.fvars.length + mowner < ys.length := by
      simp only [ys, List.length_append]
      omega
    have hget : ys[H.params.fvars.length + mowner]'hpos =
        H.bindings.motives.fvars[mowner]'hmfvLt := by
      simp only [ys]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
      congr 1
      omega
    rw [← hget, Expr.abstractList_fvar_getElem hys _ hpos]
    congr 1
    simp only [ys, List.length_append, hparamsLen, hmotivesLen, hminorsLen]
    omega
  have hparamsAbs : (stats.params.toList.map fun e =>
      (e.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
        (S.fields.size + S.hypotheses.size)) =
      List.ofFn fun k : Fin stats.params.size =>
        Expr.bvar (((H.recInfos.map (·.motive)).size + minorIdx + S.fields.size +
          S.hypotheses.size) + (stats.params.size - 1 - k)) := by
    have hinner : stats.params.toList.map (fun e =>
        (e.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
          (S.fields.size + S.hypotheses.size)) =
        (H.params.fvars.map Expr.fvar).map (fun e => e.abstractList ys
          (S.fields.size + S.hypotheses.size)) := by
      rw [hparamsList]
      apply List.map_congr_left
      intro e he
      obtain ⟨fv, hfv, rfl⟩ := List.mem_map.mp he
      rw [hfvarField fv (hrootFresh fv (hparamsRoot fv hfv))]
    rw [hinner]
    have hspine := Expr.abstractList_fvar_prefix_spine H.params.fvars
      (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx)
      (by simpa [ys, List.append_assoc] using hys) (S.fields.size + S.hypotheses.size)
    simp only [ys, List.append_assoc]
    rw [hspine]
    apply List.ext_getElem
    · simp [hparamsLen]
    · intro i hleft hright
      simp only [List.getElem_ofFn, List.length_append, hmotivesLen, hminorsLen, hparamsLen]
      congr 1
      omega
  have hfieldsAbs : (S.fields.toList.map fun e =>
      (e.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
        (S.fields.size + S.hypotheses.size)) =
      List.ofFn fun j : Fin S.fields.size =>
        Expr.bvar (S.hypotheses.size + (S.fields.size - 1 - j)) := by
    have hlen : S.fields_bound.fvars.length = S.fields.size := S.fields_bound.length_fvars
    have hinner : S.fields.toList.map (fun e =>
        (e.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
          (S.fields.size + S.hypotheses.size)) =
        ((S.fields_bound.fvars.map Expr.fvar).map
          (fun e => e.abstractList S.fields_bound.fvars S.hypotheses.size)).map
            (fun e => e.abstractList ys (S.fields.size + S.hypotheses.size)) := by
      have hflist : S.fields.toList = S.fields_bound.fvars.map Expr.fvar := by
        simpa using congrArg Array.toList S.fields_bound.expressions
      rw [hflist]
      simp [List.map_map, Function.comp_def]
    rw [hinner, Expr.abstractList_fvar_spine _ S.fields_nodup, hlen,
      Expr.abstractList_bvar_spine _ _ _ _ (by omega)]
  have hS : H.origins.minorShapes mowner hmowner localIndex hlocal = S := rfl
  have hHS : H.sourceMinorTyping mowner hmowner localIndex hlocal = HS := rfl
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  simp only [hS, hHS, Expr.mkAppN_eq_mkAppList, Array.toList_map, List.map_map,
    Function.comp_def, hconst, hmotiveAbs, hparamsAbs, hfieldsAbs]
  rw [Expr.mkAppList_append]

/-- Shape of a flat minor slot of the checked recursor type: the field
domains are the lifted field domains of the minor, followed by one domain per
hypothesis and the motive application, whose head is the owner's motive
variable, whose last argument is the constructor applied to the bvar spine, and whose
index arguments translate the closed terminal indices. -/
theorem RecursorConstruction.recursorTelescope_minorResidual
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let HS := H.sourceMinorTyping mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ hyps idx : List VExpr,
      hyps.length = S.hypotheses.size ∧
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps
          (.app
            (VExpr.mkApps (.bvar (S.fields.size + S.hypotheses.size + minorIdx +
              ((H.recInfos.map (·.motive)).size - 1 - mowner))) idx)
            (VExpr.mkApps
              (.const S.constructor.name
                (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
              (InductiveSignature.vars stats.params.size
                ((H.recInfos.map (·.motive)).size + minorIdx + S.fields.size +
                  S.hypotheses.size) ++
                InductiveSignature.vars S.fields.size S.hypotheses.size)))) ∧
      List.Forall₂
        (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps) []))
        ((AddInductive.getIIndices stats HS.semantic.traversal.terminal).2.toList.map fun arg =>
          (arg.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
            (S.fields.size + S.hypotheses.size))
        idx := by
  intro S HS fields ys
  obtain ⟨residual, heq, Hres⟩ :=
    H.recursorTelescope_minorFields howner T minorIdx D mowner hmowner localIndex hlocal hD
  have Htel := ((S.hypothesisTelescope).abstractN S.fields_bound.fvars).abstractList ys
    S.fields.size
  rw [Nat.zero_add] at Htel
  obtain ⟨hyps, res, hhyps, hresEq, Hr⟩ := TrExprS.forallTelescope_shape_with_context Htel Hres
  have hctx : abstractForallContext hyps
      (abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields) []) =
      abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps)
        [] := by
    simp [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc]
  rw [hctx, H.minorResidualSource minorIdx D.inBounds mowner hmowner localIndex hlocal] at Hr
  have hminor : minorIdx < T.minors.length := by rw [T.minors_length]; exact D.inBounds
  have hmotiveLt : mowner < (H.recInfos.map (·.motive)).size := by simpa using hmowner
  have hfs : (H.origins.minorShapes mowner hmowner localIndex hlocal).fields.size =
    S.fields.size := rfl
  have hhs : (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size =
    S.hypotheses.size := rfl
  have hfieldsLen : fields.length = S.fields.size := by
    simp only [fields, InductiveSignature.insertBinders, List.length_map, List.length_zipIdx]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  have hlenCtx : (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps).length =
      stats.params.size + ((H.recInfos.map (·.motive)).size + minorIdx) + S.fields.size +
        S.hypotheses.size := by
    simp only [List.length_append, T.params_length, T.motives_length, List.length_take,
      hfieldsLen, hhyps]
    omega
  cases Hr with
  | app _ _ Hf Ha =>
    obtain ⟨m', idx, Hm, Hidx, hf'⟩ := checkPositivityStep.TrExprS.mkAppList_inv Hf
    have hm' := TrExprS.bvar_eq_of_abstractForallContext Hm (by rw [hlenCtx]; omega)
    obtain ⟨c', P', F', Hc, HP, HF, ha'⟩ := checkPositivityStep.TrExprS.mkAppList_append_inv Ha
    have hP := TrExprS.shiftedBvarSpine_eq HP (by rw [hlenCtx]; omega)
    have hF := TrExprS.shiftedBvarSpine_eq HF (by rw [hlenCtx]; omega)
    cases Hc with
    | const _ hlevels _ =>
      have hus := Option.some.inj (hlevels.symm.trans H.statsLevelsTranslation)
      refine ⟨hyps, idx, hhyps, ?_, Hidx⟩
      rw [heq, hresEq, hf', ha', hm', hP, hF, hus, VExpr.mkApps_append]

theorem Expr.abstractList_mkAppList_depth (head : Expr) (args : List Expr)
    (fvars : List FVarId) (depth : Nat) :
    (Expr.mkAppList head args).abstractList fvars depth =
      Expr.mkAppList (head.abstractList fvars depth)
        (args.map fun arg => arg.abstractList fvars depth) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    simpa only [Expr.mkAppList, List.map_cons, Expr.abstractList_app] using ih (.app head arg)

theorem Expr.liftLooseBVars'_mkAppList (head : Expr) (args : List Expr) (start amount : Nat) :
    (Expr.mkAppList head args).liftLooseBVars' start amount =
      Expr.mkAppList (head.liftLooseBVars' start amount)
        (args.map fun arg => arg.liftLooseBVars' start amount) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    simpa only [Expr.mkAppList, List.map_cons, Expr.liftLooseBVars'] using ih (.app head arg)

/-- Application spines of equal length are injective in head and arguments. -/
theorem VExpr.mkApps_inj {f g : VExpr} {l₁ l₂ : List VExpr} (hlen : l₁.length = l₂.length)
    (h : VExpr.mkApps f l₁ = VExpr.mkApps g l₂) : f = g ∧ l₁ = l₂ := by
  induction l₁ generalizing f g l₂ with
  | nil =>
    cases l₂ with
    | nil => exact ⟨h, rfl⟩
    | cons _ _ => simp at hlen
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b l₂ =>
      have h' : VExpr.mkApps (.app f a) l₁ = VExpr.mkApps (.app g b) l₂ := h
      obtain ⟨hfg, hl⟩ := ih (by simpa using hlen) h'
      cases hfg
      exact ⟨rfl, by rw [hl]⟩

theorem getIIndices_snd_toList (stats : AddInductive.InductiveStats) (e : Expr) :
    (AddInductive.getIIndices stats e).2.toList = e.getAppArgsList.drop stats.params.size := by
  rw [← Expr.getAppArgs_toList]
  simp only [AddInductive.getIIndices]
  let suffix := e.getAppArgs.toSubarray stats.params.size
  calc
    (Std.Slice.toArray suffix).toList = suffix.toList := by
      exact (congrArg Array.toList
        (Subarray.toArray_eq_sliceToArray (s := suffix)).symm).trans
          Subarray.toList_toArray
    _ = e.getAppArgs.toList.drop stats.params.size := by
      rw [List.drop_eq_drop_min]
      simp only [suffix, Subarray.toList_eq, Array.array_toSubarray,
        Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
        Array.toList_extract, List.extract_eq_take_drop,
        Array.length_toList]
      apply List.take_of_length_le
      simp

/-- Pointwise syntactic uniqueness of translation lists. -/
theorem TrExprS.forall₂_uniqueS {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {srcs : List Expr} {l₁ l₂ : List VExpr}
    (H₁ : List.Forall₂ (TrExprS env Us Δ) srcs l₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ) srcs l₂) : l₁ = l₂ := by
  induction H₁ generalizing l₂ with
  | nil => cases H₂; rfl
  | cons h₁ _ ih =>
    cases H₂ with
    | cons h₂ H₂ => rw [h₁.uniqueS h₂, ih H₂]

/-- Abstraction removes the abstracted variable from the free-variable scope. -/
theorem _root_.Lean4Lean.FVarsIn.abstract1_not {P : FVarId → Prop} {e : Expr} {v : FVarId} {k : Nat}
    (h : FVarsIn P e) : FVarsIn (fun fv => P fv ∧ fv ≠ v) (e.abstract1 v k) := by
  induction e generalizing k with
  | fvar v' =>
    simp only [FVarsIn] at h
    by_cases hv : v = v'
    · subst hv; simp [Expr.abstract1, FVarsIn]
    · simp [Expr.abstract1, hv, FVarsIn, h, Ne.symm hv]
  | _ => simp_all [FVarsIn, Expr.abstract1]

theorem _root_.Lean4Lean.FVarsIn.abstractList_not {P : FVarId → Prop} {e : Expr} {xs : List FVarId} {k : Nat}
    (h : FVarsIn P e) : FVarsIn (fun fv => P fv ∧ fv ∉ xs) (e.abstractList xs k) := by
  induction xs generalizing P e with
  | nil => simpa using h
  | cons a as ih =>
    simp only [Expr.abstractList]
    have h' := ih (P := fun fv => P fv ∧ fv ≠ a) (h.abstract1_not (v := a) (k := k))
    apply h'.mono
    intro fv hfv
    simp only [List.mem_cons, not_or]
    exact ⟨hfv.1.1, hfv.1.2, hfv.2⟩

/-- Closing a parameter-and-field term over hypotheses, fields, and the outer
binders in the generator's order equals closing it over fields and
parameters first and then lifting. -/
theorem Expr.closeIndexSource (e : Expr) (fields params rest : List FVarId) (nf nh : Nat)
    (hclosed : Closed e 0) (hfields : fields.Nodup) (hnodup : (params ++ rest).Nodup)
    (hscope : e.FVarsIn fun fv => fv ∈ params ∨ fv ∈ fields) :
    (e.abstractList fields nh).abstractList (params ++ rest) (nf + nh) =
      (((e.abstractList fields).abstractList params nf).liftLooseBVars' nf rest.length).liftLooseBVars'
        0 nh := by
  have h1 : e.abstractList fields nh = (e.abstractList fields).liftLooseBVars' 0 nh := by
    simpa using Expr.abstractList_add_eq_liftLooseBVars (e := e) (fvars := fields)
      (depth := 0) (extra := nh) hclosed hfields
  rw [h1, Expr.liftLooseBVars'_abstractList_add _ _ 0 nf nh (Nat.zero_le _) hnodup,
    Expr.abstractList_append]
  congr 1
  apply FVarsIn.abstractList_eq_liftLooseBVars
  have h2 := (hscope.abstractList_not (xs := fields) (k := 0)).abstractList_not (xs := params)
    (k := nf)
  apply h2.mono
  intro fv hfv hrest
  rcases hfv with ⟨⟨hpf, hnotf⟩, hnotp⟩
  rcases hpf with hp | hf
  · exact hnotp hp
  · exact hnotf hf

/-- The index translations of a flat minor slot are the minor's result indices
(`declConstructorIndices`), instantiated at the recursor universes and lifted
beneath the motives, earlier minors, fields and hypotheses. -/
theorem RecursorConstruction.recursorTelescope_minorIndices
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat}
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat) (hminor : minorIdx < (H.recInfos.flatMap (·.minors)).size)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let HS := H.sourceMinorTyping mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ (hyps idx : List VExpr), hyps.length = S.hypotheses.size →
      List.Forall₂
        (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps) []))
        ((AddInductive.getIIndices stats HS.semantic.traversal.terminal).2.toList.map fun arg =>
          (arg.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
            (S.fields.size + S.hypotheses.size))
        idx →
      idx = (H.declConstructorIndices mowner hmowner localIndex hlocal).map fun e =>
        ((e.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)).liftN
          ((H.recInfos.map (·.motive)).size + minorIdx) S.fields.size).liftN S.hypotheses.size 0 := by
  intro S HS fields ys hyps idx hhyps Hidx
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, hst, _, _, _, _, hsourceLE⟩ :=
    H.minorSources.rows mowner hmowner hsourceOwner localIndex hlocal
  have heqT : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  subst heqT
  -- The translations of the field telescope and its indices in the header environment.
  obtain ⟨Hsrc, _, Hindices⟩ := H.sourceConstructorIndices_replay mowner hmowner localIndex hlocal
  have Hle := R.installation.constructorLE.trans R.ctorLE
  have Hlift := H.liftDeclUnivType (Hsrc.mono Hle)
  rw [VExpr.instL_wrapForalls] at Hlift
  -- Peel the field telescope.
  have hfv : (S.fields_bound.mono hsourceLE).fvars = S.fields_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq _ _ rfl
  have Htel := ((S.fields_bound.mono hsourceLE).mkForall_forallTelescope H.localWF
    HS.semantic.traversal.terminal).abstractList H.params.fvars
  rw [hfv, Nat.zero_add] at Htel
  have hdomLen : ((H.declFieldDomains mowner hmowner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))).length =
      S.fields.size := by
    simp only [List.length_map]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  have Hres := TrExprS.forallTelescope_residual Htel hdomLen Hlift
  have hctx₁ : abstractForallContext ((H.declFieldDomains mowner hmowner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) =
      abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
        (H.declFieldDomains mowner hmowner localIndex hlocal).map
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))) [] := by
    simp [abstractForallContext, List.reverse_append, List.map_append]
  rw [hctx₁] at Hres
  -- Insert the motives and earlier minors, then the hypotheses.
  have Hins := TrExprS.insertBeforeInner H.recursorWF.checking.tr.wf.ordered Hres
    (T.motives ++ T.minors.take minorIdx)
  have Hhyp := Hins.weakBV H.recursorWF.checking.tr.wf.ordered
    (abstractForallContext.bvLift hyps _)
  have hminorT : minorIdx < T.minors.length := by rw [T.minors_length]; exact hminor
  have hinserted : (T.motives ++ T.minors.take minorIdx).length =
      (H.recInfos.map (·.motive)).size + minorIdx := by
    simp only [List.length_append, T.motives_length, List.length_take, T.minors_length]
    omega
  have hctx₂ : abstractForallContext hyps
      (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++
        (T.motives ++ T.minors.take minorIdx) ++
        (liftContextPrefix (T.motives ++ T.minors.take minorIdx).length
          ((H.declFieldDomains mowner hmowner localIndex hlocal).map
            (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))).reverse).reverse)
        []) =
      abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps) [] := by
    rw [← H.recursorTelescope_params T, hinserted]
    simp only [fields, insertBinders_eq_prefix, liftContextPrefix]
    simp [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc]
  rw [H.recursorEnv, hctx₂, hinserted] at Hhyp
  -- Decompose the lifted terminal application on both sides.
  obtain ⟨hhead, hparamsTake⟩ := H.constructorTerminalSpine mowner hmowner localIndex hlocal HS
  have hterminal : HS.semantic.traversal.terminal =
      Expr.mkAppList (.const (decl.types[mowner]'(by rw [← H.cardinality.records]; exact hmowner)).name
        stats.levels)
        (stats.params.toList ++ HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size) := by
    conv => lhs; rw [← Expr.mkAppList_getAppArgsList HS.semantic.traversal.terminal]
    rw [hhead, ← hparamsTake, List.take_append_drop]
  have hclosedT : Closed HS.semantic.traversal.terminal 0 := by
    have h := HS.semantic.terminalTranslation.closed
    rw [HS.semantic.terminalWF.mlctx.noBV] at h
    simpa using h
  have hparamsList : stats.params.toList = H.params.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList H.params.expressions
  have hids : ExprArrayFVarIds HS.semantic.traversal.stats.params = H.params.fvars := by
    rw [hst]
    simp only [ExprArrayFVarIds, hparamsList, List.map_map]
    simp [Function.comp_def, recursorFVarId]
  have hscopeT : HS.semantic.traversal.terminal.FVarsIn
      (fun fv => fv ∈ H.params.fvars ∨ fv ∈ S.fields_bound.fvars) := by
    have h := HS.semantic.fieldOpening.currentFVarsIn HS.semantic.parameterScope
    apply h.mono
    intro fv hfv
    rcases hfv with hfield | hparam
    · right
      rwa [HS.semantic.fieldOpening.fvars_eq_bound S.fields_bound] at hfield
    · left
      rwa [HS.semantic.parameterSuffix.parameterDecls_fvars, hids, List.mem_reverse] at hparam
  have hclosedApp : Closed (Expr.mkAppList
      (.const (decl.types[mowner]'(by rw [← H.cardinality.records]; exact hmowner)).name stats.levels)
      (stats.params.toList ++ HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size))
      0 := by
    rw [← hterminal]; exact hclosedT
  rw [hterminal, Expr.abstractN_eq_abstractList_of_closed S.fields_nodup hclosedApp] at Hhyp
  simp only [Expr.abstractList_mkAppList_depth, Expr.liftLooseBVars'_mkAppList, List.map_append,
    List.map_map] at Hhyp
  obtain ⟨fn', left', right', _, Hleft, Hright, hout⟩ :=
    checkPositivityStep.TrExprS.mkAppList_append_inv Hhyp
  simp only [VExpr.instL_mkApps, VExpr.liftN_mkApps, List.map_append, List.map_map] at hout
  simp only [Function.comp_def, hhyps, hdomLen] at Hright
  have hleftLen : left'.length = stats.params.size := by
    rw [← Lean4Lean.List.Forall₂.length_eq Hleft]
    simp [hparamsList, H.params.length_fvars]
  have hindicesLen := Lean4Lean.List.Forall₂.length_eq Hindices
  have hrightLen : right'.length = (H.declConstructorIndices mowner hmowner localIndex hlocal).length := by
    rw [← Lean4Lean.List.Forall₂.length_eq Hright]
    simpa using hindicesLen
  obtain ⟨_, hargs⟩ := VExpr.mkApps_inj (by
    simp only [List.length_append, List.length_map, hleftLen, hrightLen, InductiveSignature.vars]
    simp) hout
  have hright := List.append_inj_right hargs (by simp [hleftLen, InductiveSignature.vars])
  -- The two index source lists coincide.
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hys : (H.params.fvars ++ (H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx)).Nodup := by
    rw [← List.append_assoc]
    apply List.Nodup.sublist _ houter
    exact List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _)
  have hrestLen : (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx).length =
      (H.recInfos.map (·.motive)).size + minorIdx := by
    rw [List.length_append, H.bindings.motives.length_fvars, List.length_take,
      H.bindings.flatMinors.length_fvars]
    omega
  have hsrcEq : (AddInductive.getIIndices stats HS.semantic.traversal.terminal).2.toList.map
      (fun arg => (arg.abstractList S.fields_bound.fvars S.hypotheses.size).abstractList ys
        (S.fields.size + S.hypotheses.size)) =
      (HS.semantic.traversal.terminal.getAppArgsList.drop stats.params.size).map
        (fun arg => (((arg.abstractList S.fields_bound.fvars).abstractList H.params.fvars
          S.fields.size).liftLooseBVars' S.fields.size
            ((H.recInfos.map (·.motive)).size + minorIdx)).liftLooseBVars' 0 S.hypotheses.size) := by
    rw [getIIndices_snd_toList]
    apply List.map_congr_left
    intro arg harg
    have hmem := List.mem_of_mem_drop harg
    have hc := hclosedT.getAppArgsList_at hmem
    have hs := hscopeT.of_mem_getAppArgsList hmem
    rw [← hrestLen]
    simpa [ys, List.append_assoc] using
      Expr.closeIndexSource arg S.fields_bound.fvars H.params.fvars
        (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx)
        S.fields.size S.hypotheses.size hc S.fields_nodup hys hs
  rw [hsrcEq] at Hidx
  rw [TrExprS.forall₂_uniqueS Hidx Hright]
  simp only [Function.comp_def, hhyps, hdomLen] at hright
  simpa using hright.symm

/-- The `j`-th hypothesis domain of a flat minor slot translates the hypothesis's declared
type, closed over the earlier hypotheses, the fields,
and the outer binders, in the generator context of that hypothesis. -/
theorem RecursorConstruction.recursorTelescope_hypothesisSlot
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat) (D : FVarDeclAt S.sourceFullContext S.hypotheses j),
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext
          (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j) [])
        (((D.type.abstractList (S.hypotheses_bound.fvars.take j)).abstractList
          S.fields_bound.fvars j).abstractList ys (S.fields.size + j))
        (hyps[j]'(by rw [hhyps]; exact D.inBounds)) := by
  intro S fields ys hyps res hhyps hminorEq j D
  have Hminor := H.recursorTelescope_minor howner T minorIdx D₀
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨horigin, _, _, _, _, _, _, _, _, _, _, _, _, _, hsourceLE⟩ :=
    H.minorSources.rows mowner hmowner hsourceOwner localIndex hlocal
  have hsource : D₀.type = S.origin := hD.trans horigin.symm
  rw [hsource, hminorEq, ← VExpr.wrapForalls_append] at Hminor
  have hclosedD : Closed D.type := by
    apply H.recursorWF.lctxClosed.cdecl
    rw [hsourceLE.declarations D.fvar D.member]
    exact D.declaration
  have Hb := (S.hypothesisBinderAtList D hclosedD).abstractList ys
  rw [Nat.zero_add] at Hb
  have hfieldsLen : fields.length = S.fields.size := by
    simp only [fields, InductiveSignature.insertBinders, List.length_map, List.length_zipIdx]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  have hj : j < S.hypotheses.size := D.inBounds
  have hi : S.fields.size + j < (fields ++ hyps).length := by
    simp only [List.length_append, hfieldsLen, hhyps]
    omega
  have Ht := Hb.translation Hminor hi
  have htake : (fields ++ hyps).take (S.fields.size + j) = fields ++ hyps.take j := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    congr 2
    omega
  have hget : (fields ++ hyps)[S.fields.size + j]'hi = hyps[j]'(by rw [hhyps]; exact hj) := by
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega
  rw [htake, hget] at Ht
  simpa [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc] using Ht

/-- The closed source of a hypothesis's motive application: after closing the
higher-order arguments, the earlier hypotheses, the fields and the outer binders, the motive
is the bound variable of the target family's motive, the recursive field is its field's bound
variable applied to the bvar spine of the arguments, and the indices are closed pointwise. -/
theorem RecursorConstruction.hypothesisResidualSource
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (minorIdx : Nat) (hminor : minorIdx < (H.recInfos.flatMap (·.minors)).size)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ (j : Nat)
      (origins : MinorInductionHypothesisTypes S.sourceFullContext S.recursiveFields
        S.hypotheses)
      (_hmotives : origins.recInfos.map (·.motive) = H.recInfos.map (·.motive))
      {root : AddInductive.Context} {sourceType : Expr}
      (O : InductionHypothesisType origins.stats origins.recInfos root
        (S.recursiveFields[j]!) sourceType)
      (_howner : O.ownerIdx < H.recInfos.size)
      (pos : Nat) (hpos : pos < S.fields_bound.fvars.length)
      (_hfield : S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos)),
      ((((Expr.app
          (mkAppN origins.recInfos[O.ownerIdx]!.motive
            (O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr))
          (mkAppN (S.recursiveFields[j]!) O.args)).abstractN O.arguments_bound.fvars).abstractList
            (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
              (j + O.args.size)).abstractList ys (S.fields.size + j + O.args.size) =
        Expr.app
          (Expr.mkAppList
            (.bvar (S.fields.size + j + O.args.size + minorIdx +
              ((H.recInfos.map (·.motive)).size - 1 - O.ownerIdx)))
            ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map fun e =>
              (((e.abstractN O.arguments_bound.fvars).abstractList
                (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
                  (j + O.args.size)).abstractList ys (S.fields.size + j + O.args.size)))
          (Expr.mkAppList (.bvar (j + O.args.size + (S.fields.size - 1 - pos)))
            (List.ofFn fun l : Fin O.args.size => Expr.bvar (O.args.size - 1 - l))) := by
  intro S ys j origins hmotives root sourceType O howner pos hpos hfield
  obtain ⟨mfv, hmotive, hmroot⟩ := O.motive_is_fvar
  obtain ⟨ffv, hfieldEq, hfroot⟩ := O.field_fvar
  have hffv : ffv = S.fields_bound.fvars[pos]'hpos := Expr.fvar.inj (hfieldEq.symm.trans hfield)
  have hna : O.arguments_bound.fvars.length = O.args.size := O.arguments_bound.length_fvars
  have hnf : S.fields_bound.fvars.length = S.fields.size := S.fields_bound.length_fvars
  have hmotiveLt : O.ownerIdx < (H.recInfos.map (·.motive)).size := by simpa using howner
  have hoLt : O.ownerIdx < origins.recInfos.size := by
    have h := congrArg Array.size hmotives
    simp only [Array.size_map] at h
    omega
  -- The motive variable is the owner's motive binder.
  obtain ⟨hmfvLt, hmotiveGet⟩ := H.bindings.motives.getElem_eq_fvar O.ownerIdx hmotiveLt
  have hmfv : mfv = H.bindings.motives.fvars[O.ownerIdx]'hmfvLt := by
    have h1 : (origins.recInfos.map (·.motive))[O.ownerIdx]'(by simpa using hoLt) =
        (H.recInfos.map (·.motive))[O.ownerIdx]'hmotiveLt := by
      simp only [hmotives]
    rw [hmotiveGet, Array.getElem_map] at h1
    have hm := hmotive
    rw [getElem!_pos origins.recInfos O.ownerIdx hoLt] at hm
    exact Expr.fvar.inj (hm.symm.trans h1)
  -- Freshness of the arguments relative to the root.
  have hargsFresh : ∀ fv, fv ∈ root.lctx.fvars → fv ∉ O.arguments_bound.fvars := by
    intro fv hroot hmem
    exact O.arguments_bound.fresh fv hmem hroot
  have hmNotArgs : mfv ∉ O.arguments_bound.fvars := hargsFresh mfv hmroot
  have hfNotArgs : ffv ∉ O.arguments_bound.fvars := hargsFresh ffv hfroot
  -- The motive is not a hypothesis or a field.
  have hmInMotives : mfv ∈ ExprArrayFVarIds (origins.recInfos.map (·.motive)) := by
    simp only [ExprArrayFVarIds, List.mem_map, Array.mem_toList_iff]
    refine ⟨.fvar mfv, ?_, rfl⟩
    rw [← hmotive, getElem!_pos origins.recInfos O.ownerIdx hoLt,
      ← Array.getElem_map (f := fun x : AddInductive.RecInfo => x.motive)]
    exact Array.getElem_mem (by simpa using hoLt)
  have hmNotHyps : mfv ∉ S.hypotheses_bound.fvars.take j := by
    intro hmem
    have h := origins.hypotheses_outer_fresh mfv (List.mem_append_right _ hmInMotives)
    rw [S.hypotheses_bound.exprArrayFVarIds] at h
    exact h (List.mem_of_mem_take hmem)
  have hmNotFields : mfv ∉ S.fields_bound.fvars := by
    intro hmem
    have h := H.templates.fields_outer_fresh mowner hmowner localIndex hlocal mfv hmem
    apply h
    apply List.mem_append_left
    apply List.mem_append_right
    rwa [← hmotives]
  have hfNotHyps : ffv ∉ S.hypotheses_bound.fvars.take j := by
    intro hmem
    exact S.hypotheses_fields_fresh ffv (List.mem_of_mem_take hmem) (hffv ▸ List.getElem_mem hpos)
  -- Distinctness and lengths of the outer binders.
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hys : ys.Nodup := by
    apply List.Nodup.sublist _ houter
    exact List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _)
  have hparamsLen : H.params.fvars.length = stats.params.size := H.params.length_fvars
  have hmotivesLen : H.bindings.motives.fvars.length = (H.recInfos.map (·.motive)).size :=
    H.bindings.motives.length_fvars
  have hminorsLen : (H.bindings.flatMinors.fvars.take minorIdx).length = minorIdx := by
    rw [List.length_take, H.bindings.flatMinors.length_fvars]
    omega
  -- Component computations.
  have hfvarKeep : ∀ (fv : FVarId) (xs : List FVarId), fv ∉ xs → ∀ k,
      (Expr.fvar fv).abstractList xs k = .fvar fv := by
    intro fv xs hfv k
    exact FVarsIn.abstractList_eq_self (e := .fvar fv) (by simpa [FVarsIn] using hfv) (by simp [Closed])
  have hmotiveAbs : ((((origins.recInfos[O.ownerIdx]!.motive.abstractN O.arguments_bound.fvars).abstractList
      (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
        (j + O.args.size)).abstractList ys (S.fields.size + j + O.args.size)) =
      .bvar (S.fields.size + j + O.args.size + minorIdx +
        ((H.recInfos.map (·.motive)).size - 1 - O.ownerIdx)) := by
    rw [hmotive, Expr.abstractN_fvar_of_not_mem hmNotArgs, hfvarKeep _ _ hmNotHyps,
      hfvarKeep _ _ hmNotFields]
    have hposY : H.params.fvars.length + O.ownerIdx < ys.length := by
      simp only [ys, List.length_append]
      omega
    have hget : ys[H.params.fvars.length + O.ownerIdx]'hposY =
        H.bindings.motives.fvars[O.ownerIdx]'hmfvLt := by
      simp only [ys]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
      congr 1
      omega
    rw [hmfv, ← hget, Expr.abstractList_fvar_getElem hys _ hposY]
    congr 1
    simp only [ys, List.length_append, hparamsLen, hmotivesLen, hminorsLen]
    omega
  have hfieldAbs : ((((Expr.fvar ffv).abstractN O.arguments_bound.fvars).abstractList
      (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
        (j + O.args.size)).abstractList ys (S.fields.size + j + O.args.size) =
      .bvar (j + O.args.size + (S.fields.size - 1 - pos)) := by
    rw [Expr.abstractN_fvar_of_not_mem hfNotArgs, hfvarKeep _ _ hfNotHyps, hffv,
      Expr.abstractList_fvar_getElem S.fields_nodup pos hpos, hnf,
      Expr.abstractList_bvar_lt _ (by omega)]
  have hargsAbs : (O.args.toList.map fun e =>
      (((e.abstractN O.arguments_bound.fvars).abstractList (S.hypotheses_bound.fvars.take j)
        O.args.size).abstractList S.fields_bound.fvars (j + O.args.size)).abstractList ys
          (S.fields.size + j + O.args.size)) =
      List.ofFn fun l : Fin O.args.size => Expr.bvar (O.args.size - 1 - l) := by
    have hlist : O.args.toList = O.arguments_bound.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList O.arguments_bound.expressions
    rw [hlist]
    apply List.ext_getElem
    · simp [hna]
    · intro i hleft hright
      have hi : i < O.arguments_bound.fvars.length := by simpa using hleft
      simp only [List.getElem_map, List.getElem_ofFn]
      rw [Expr.abstractN_fvar_getElem O.arguments_bound.nodup i hi, hna, Nat.zero_add,
        Expr.abstractList_bvar_lt _ (by omega), Expr.abstractList_bvar_lt _ (by omega),
        Expr.abstractList_bvar_lt _ (by omega)]
  simp only [hfieldEq, Expr.abstractN_app, Expr.abstractN_mkAppN]
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hmotiveAbs, hfieldAbs]
  simp only [Expr.mkAppN_eq_mkAppList, Array.toList_map, List.map_map, Function.comp_def]
  rw [← hargsAbs]

/-- Shape of the `j`-th hypothesis domain of a flat minor slot: a telescope
of one domain per higher-order argument, then the owner's motive variable
applied to translations of the closed exposed indices and to the recursive
field variable applied to the bvar spine of the arguments. -/
theorem RecursorConstruction.recursorTelescope_hypothesisShape
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat)
        (origins : MinorInductionHypothesisTypes S.sourceFullContext S.recursiveFields
          S.hypotheses)
        (_hmotives : origins.recInfos.map (·.motive) = H.recInfos.map (·.motive))
        {root : AddInductive.Context} {sourceType : Expr}
        (O : InductionHypothesisType origins.stats origins.recInfos root
          (S.recursiveFields[j]!) sourceType)
        (D : FVarDeclAt S.sourceFullContext S.hypotheses j)
        (_hDtype : D.type = (sourceType.consumeTypeAnnotationsVerified S.sourceFullContext.env.isTypeAnnotationWrapper))
        (_howner' : O.ownerIdx < H.recInfos.size)
        (pos : Nat) (hpos : pos < S.fields_bound.fvars.length)
        (_hfield : S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos)),
      ∃ A I : List VExpr, A.length = O.args.size ∧
        hyps[j]'(by rw [hhyps]; exact D.inBounds) =
          VExpr.wrapForalls A
            (.app
              (VExpr.mkApps (.bvar (S.fields.size + j + O.args.size + minorIdx +
                ((H.recInfos.map (·.motive)).size - 1 - O.ownerIdx))) I)
              (VExpr.mkApps (.bvar (j + O.args.size + (S.fields.size - 1 - pos)))
                (InductiveSignature.vars O.args.size 0))) ∧
        List.Forall₂
          (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++ A) []))
          ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map fun e =>
            (((e.abstractN O.arguments_bound.fvars).abstractList
              (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
                (j + O.args.size)).abstractList ys (S.fields.size + j + O.args.size))
          I := by
  intro S fields ys hyps res hhyps hminorEq j origins hmotives root sourceType O D hDtype howner'
    pos hpos hfield
  have Hslot := H.recursorTelescope_hypothesisSlot howner T minorIdx D₀ mowner hmowner localIndex
    hlocal hD hyps res hhyps hminorEq j D
  have htype : D.type = sourceType := hDtype.trans O.consumeTypeAnnotationsVerified_eq_self
  rw [htype] at Hslot
  have Htel := (((O.sourceTelescope).abstractList (S.hypotheses_bound.fvars.take j)).abstractList
    S.fields_bound.fvars j).abstractList ys (S.fields.size + j)
  simp only [Nat.zero_add] at Htel
  obtain ⟨A, res', hA, hEq, Hr⟩ := TrExprS.forallTelescope_shape_with_context Htel Hslot
  rw [H.hypothesisResidualSource minorIdx D₀.inBounds mowner hmowner localIndex hlocal j origins
    hmotives O howner' pos hpos hfield] at Hr
  have hctx : abstractForallContext A
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j) []) =
      abstractForallContext
        (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++ A) [] := by
    simp [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc]
  rw [hctx] at Hr
  have hmotiveLt : O.ownerIdx < (H.recInfos.map (·.motive)).size := by simpa using howner'
  have hnf : S.fields_bound.fvars.length = S.fields.size := S.fields_bound.length_fvars
  have hfs : (H.origins.minorShapes mowner hmowner localIndex hlocal).fields.size =
    S.fields.size := rfl
  have hhs : (H.origins.minorShapes mowner hmowner localIndex hlocal).hypotheses.size =
    S.hypotheses.size := rfl
  have hposf : pos < S.fields.size := by omega
  have hfieldsLen : fields.length = S.fields.size := by
    simp only [fields, InductiveSignature.insertBinders, List.length_map, List.length_zipIdx]
    exact H.sourceFields_length mowner hmowner localIndex hlocal
  have hj : j < S.hypotheses.size := D.inBounds
  have hlenCtx : (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++
      A).length = stats.params.size + ((H.recInfos.map (·.motive)).size + minorIdx) +
        S.fields.size + j + O.args.size := by
    have hminorT : minorIdx < T.minors.length := by rw [T.minors_length]; exact D₀.inBounds
    simp only [List.length_append, T.params_length, T.motives_length, List.length_take,
      hfieldsLen, hhyps, hA]
    omega
  cases Hr with
  | app _ _ Hf Ha =>
    obtain ⟨m', I, Hm, HI, hf'⟩ := checkPositivityStep.TrExprS.mkAppList_inv Hf
    have hm' := TrExprS.bvar_eq_of_abstractForallContext Hm (by rw [hlenCtx]; omega)
    obtain ⟨f', args', Hfv, Hargs, ha'⟩ := checkPositivityStep.TrExprS.mkAppList_inv Ha
    have hf'' := TrExprS.bvar_eq_of_abstractForallContext Hfv (by rw [hlenCtx]; omega)
    have hspine : (List.ofFn fun l : Fin O.args.size => Expr.bvar (O.args.size - 1 - l)) =
        List.ofFn fun l : Fin O.args.size => Expr.bvar (0 + (O.args.size - 1 - l)) := by
      simp
    rw [hspine] at Hargs
    have hargs' := TrExprS.shiftedBvarSpine_eq Hargs (by rw [hlenCtx]; omega)
    refine ⟨A, I, hA, ?_, HI⟩
    rw [hEq, hf', ha', hm', hf'', hargs']

/-- Closing a concatenated selection of distinct declarations closes the
suffix first. -/
theorem FVarArrayIn.mkForall_append_eq
    (H₁ : FVarArrayIn c xs) (H₂ : FVarArrayIn c ys) (Hc : BindingContextWF c)
    (hnodup : (H₁.fvars ++ H₂.fvars).Nodup) (body : Expr) :
    c.lctx.mkForall (xs ++ ys) body = c.lctx.mkForall xs (c.lctx.mkForall ys body) := by
  have hdecl : ∀ fv ∈ H₁.fvars ++ H₂.fvars, ∃ d, c.lctx.find? fv = some d := by
    intro fv hfv
    rcases List.mem_append.mp hfv with h | h
    · obtain ⟨_, _, _, _, _, hd⟩ := Hc.findCDecl fv (H₁.members fv h)
      exact ⟨_, hd⟩
    · obtain ⟨_, _, _, _, _, hd⟩ := Hc.findCDecl fv (H₂.members fv h)
      exact ⟨_, hd⟩
  rcases H₁ with ⟨fvars₁, rfl, members₁⟩
  rcases H₂ with ⟨fvars₂, rfl, members₂⟩
  dsimp only at hnodup hdecl
  have hxy : (fvars₁.map Expr.fvar).toArray ++ (fvars₂.map Expr.fvar).toArray =
      ((fvars₁ ++ fvars₂).map Expr.fvar).toArray := by simp
  rw [hxy, LocalContext.mkForall, LocalContext.mkBinding_eqN, LocalContext.mkForall,
    LocalContext.mkBinding_eqN, LocalContext.mkForall, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_append hdecl hnodup

theorem _root_.Lean4Lean.FVarsIn.forallDomainsOnly {P : FVarId → Prop} {e : Expr}
    (h : FVarsIn P e) (n : Nat) : FVarsIn P (Expr.forallDomainsOnly n e) := by
  induction n generalizing e with
  | zero => simp [Expr.forallDomainsOnly, FVarsIn, Level.hasMVar']
  | succ n ih =>
    cases e with
    | forallE name d b bi =>
      simp only [Expr.forallDomainsOnly, FVarsIn] at h ⊢
      exact ⟨h.1, ih h.2⟩
    | _ => simp [Expr.forallDomainsOnly, FVarsIn, Level.hasMVar']

/-- The owner's index and major groups of the checked recursor type are the owner's motive
telescope (its index domains and the major domain, the family applied to the bvar spine)
lifted beneath the motives and all minors. -/
theorem RecursorConstruction.recursorTelescope_indicesMajor
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    {level : VLevel}
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams) H.elimLevel =
      some level) :
    T.indices ++ T.major = InductiveSignature.insertBinders
      ((H.declIndexDomains ⟨owner, howner⟩).map
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) ++
        [VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
          (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size))])
      ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size) := by
  obtain ⟨Sseed, _⟩ := H.motiveTelescopes.motiveDecls owner howner
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have hmotives : H.bindings.motives.fvars.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp houter).1).2.1
  have hminors : H.bindings.flatMinors.fvars.Nodup := (List.nodup_append.mp houter).2.1
  have hnoalias := H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner
  have hIM : (Sseed.indicesBound.fvars ++ Sseed.majorBound.fvars).Nodup := by
    have h1 : Sseed.indicesBound.fvars = (H.bindings.indices owner howner).fvars :=
      FVarArrayIn.fvars_eq_of_array_eq _ _ rfl
    have h2 : Sseed.majorBound.fvars = (H.bindings.major owner howner).fvars :=
      FVarArrayIn.fvars_eq_of_array_eq _ _ rfl
    rw [h1, h2]
    have hall : (H.params.fvars ++ (H.bindings.motives.fvars ++
        (H.bindings.flatMinors.fvars ++ ((H.bindings.indices owner howner).fvars ++
          (H.bindings.major owner howner).fvars)))).Nodup := hnoalias
    exact (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hall).2.1).2.1).2.1
  let IM := Sseed.indicesBound.append Sseed.majorBound
  have hIMfvars : IM.fvars = Sseed.indicesBound.fvars ++ Sseed.majorBound.fvars := rfl
  have hIMnodup : IM.fvars.Nodup := by rw [hIMfvars]; exact hIM
  have hsplit : ∀ body, H.localContext.lctx.mkForall
      (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major]) body =
      H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] body) :=
    fun body => Sseed.indicesBound.mkForall_append_eq Sseed.majorBound H.localWF hIM body
  have hnidx : (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major]).size =
      H.recInfos[owner]!.indices.size + 1 := by simp
  have hsort : ∀ (fvars : List FVarId) (k : Nat) (u : Level),
      (Expr.sort u).abstractList fvars k = .sort u :=
    fun fvars k u => Expr.abstractList_eq_self_of_abstract1 _ (by intro fv depth; simp [Expr.abstract1]) fvars k
  have hsortN : ∀ (fvars : List FVarId) (k : Nat) (u : Level),
      (Expr.sort u).abstractN fvars k = .sort u := fun _ _ _ => rfl
  -- The closed domains-only telescope.
  let X := H.localContext.lctx.mkForall (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major])
    (.sort .zero)
  have hXclosed : Closed X := IM.mkForall_closed H.localWF hIMnodup H.recursorWF.lctxClosed trivial
  have hXfv : X.FVarsIn (· ∈ H.params.fvars) := by
    have h := (H.motiveSource_support owner howner).1
    have h' := h.forallDomainsOnly (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major]).size
    rwa [← hsplit, IM.forallDomainsOnly H.localWF hIMnodup] at h'
  -- Forward: the owner's motive telescope, lifted.
  have Hmot := (H.sourceIndices_motive ⟨owner, howner⟩ hu).1
  have Hmot' : TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major])
        (.sort H.elimLevel)).abstractList H.params.fvars)
      (VExpr.wrapForalls
        ((H.declIndexDomains ⟨owner, howner⟩).map
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) ++
          [VExpr.mkApps
            (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
              (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
            (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size))])
        (.sort level)) := by
    rw [hsplit]
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls] using Hmot
  have HtelF := (IM.mkForall_forallTelescope H.localWF (.sort H.elimLevel)).abstractList
    H.params.fvars
  simp only [hsortN, hsort] at HtelF
  have hlenF : ((H.declIndexDomains ⟨owner, howner⟩).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) ++
      [VExpr.mkApps
        (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
          (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
        (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size))]).length =
      (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major]).size := by
    simp [H.sourceIndices_length]
  have HdomF := (TrExprS.forallDomainsOnly HtelF hlenF Hmot').1
  rw [Expr.forallDomainsOnly_abstractList, IM.forallDomainsOnly H.localWF hIMnodup] at HdomF
  have Hw := HdomF.weakBV H.recursorWF.checking.tr.wf.ordered
    (abstractForallContext.bvLift (T.motives ++ T.minors)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []))
  -- Checked side: peel parameters, motives and minors.
  have Htr := T.typed.translation
  rw [T.target_eq, VExpr.wrapForalls_append, VExpr.wrapForalls_append, VExpr.wrapForalls_append,
    VExpr.wrapForalls_append] at Htr
  let body₃ := H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have Htel1 := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive))
      (H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) body₃))
  have Hres1 := TrExprS.forallTelescope_residual Htel1 T.params_length Htr
  have Htel2 := (H.bindings.motives.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) body₃)).abstractN H.params.fvars
  have Hres2 := TrExprS.forallTelescope_residual Htel2 (by simpa using T.motives_length) Hres1
  simp only [Nat.zero_add] at Hres2
  have Htel3 := ((H.bindings.flatMinors.mkForall_forallTelescope H.localWF body₃).abstractN
    H.bindings.motives.fvars).abstractN H.params.fvars (H.recInfos.map (·.motive)).size
  have Hres3 := TrExprS.forallTelescope_residual Htel3 T.minors_length Hres2
  have HtelT := (((IM.mkForall_forallTelescope H.localWF
    (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
      H.recInfos[owner]!.major)).abstractN H.bindings.flatMinors.fvars).abstractN
        H.bindings.motives.fvars (H.recInfos.flatMap (·.minors)).size).abstractN H.params.fvars
          ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size)
  rw [hsplit] at HtelT
  have hlenT : (T.indices ++ T.major).length =
      (H.recInfos[owner]!.indices ++ #[H.recInfos[owner]!.major]).size := by
    simp [T.indices_length, T.major_length]
  simp only [Nat.zero_add] at Hres3 HtelT
  rw [← VExpr.wrapForalls_append] at Hres3
  have HdomT := (TrExprS.forallDomainsOnly HtelT hlenT Hres3).1
  rw [Expr.forallDomainsOnly_abstractN, Expr.forallDomainsOnly_abstractN,
    Expr.forallDomainsOnly_abstractN, ← hsplit, IM.forallDomainsOnly H.localWF hIMnodup] at HdomT
  -- The checked source is the lifted forward source.
  have hparamsMinors : ∀ fv ∈ H.params.fvars, fv ∉ H.bindings.flatMinors.fvars := by
    intro fv hfv hmem
    exact (List.nodup_append.mp houter).2.2 fv (List.mem_append_left _ hfv) fv hmem rfl
  have hparamsMotives : ∀ fv ∈ H.params.fvars, fv ∉ H.bindings.motives.fvars := by
    intro fv hfv hmem
    exact (List.nodup_append.mp (List.nodup_append.mp houter).1).2.2 fv hfv fv hmem rfl
  have hX1 : X.abstractN H.bindings.flatMinors.fvars = X := by
    rw [Expr.abstractN_eq_abstractList_of_closed hminors hXclosed]
    exact (hXfv.mono fun fv hfv => hparamsMinors fv hfv).abstractList_eq_self hXclosed
  have hX2 : X.abstractN H.bindings.motives.fvars (H.recInfos.flatMap (·.minors)).size = X := by
    rw [Expr.abstractN_eq_abstractList hmotives _ _
      (by rw [hXclosed.looseBVarRange_zero]; exact Nat.zero_le _)]
    exact (hXfv.mono fun fv hfv => hparamsMotives fv hfv).abstractList_eq_self
      (hXclosed.mono (Nat.zero_le _))
  have hX3 : X.abstractN H.params.fvars
      ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size) =
      (X.abstractList H.params.fvars).liftLooseBVars' 0
        ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size) := by
    rw [Expr.abstractN_eq_abstractList hparams _ _
      (by rw [hXclosed.looseBVarRange_zero]; exact Nat.zero_le _)]
    simpa using Expr.abstractList_add_eq_liftLooseBVars (e := X) (fvars := H.params.fvars)
      (depth := 0) (extra := (H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size)
      hXclosed hparams
  rw [hX1, hX2, hX3] at HdomT
  have hn : (T.motives ++ T.minors).length =
      (H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size := by
    simp [T.motives_length, T.minors_length]
  rw [H.recursorEnv, ← H.recursorTelescope_params T, hn, VExpr.liftN_wrapForalls] at Hw
  have hctx : abstractForallContext (T.motives ++ T.minors) (abstractForallContext T.params []) =
      abstractForallContext T.minors (abstractForallContext T.motives
        (abstractForallContext T.params [])) := by
    simp [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc]
  rw [hctx] at Hw
  have heq := HdomT.uniqueS Hw
  rw [insertBinders_eq_prefix]
  exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) hlenT
    (by simp [H.sourceIndices_length]) (by simpa [VExpr.liftN] using heq)

theorem insertBinders_append_singleton (domains : List VExpr) (x : VExpr) (n : Nat) :
    InductiveSignature.insertBinders (domains ++ [x]) n =
      InductiveSignature.insertBinders domains n ++ [x.liftN n domains.length] := by
  rw [insertBinders_eq_prefix, insertBinders_eq_prefix, List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  simp [liftContextPrefixAt]

/-- The major domain (the family applied to the bvar spine) lifted beneath `extra` binders
above the indices is the generator's family application. -/
theorem majorDomain_lift (name : Name) (levels : List VLevel) (nparams nidx extra : Nat) :
    (VExpr.mkApps (.const name levels) (bvarSpine (nparams + nidx))).liftN extra nidx =
      VExpr.mkApps (.const name levels)
        (InductiveSignature.vars nparams (extra + nidx) ++ InductiveSignature.vars nidx 0) := by
  simp only [VExpr.liftN_mkApps, VExpr.liftN]
  rw [bvarSpine_add, List.map_append, List.map_map, ← vars_eq_bvarSpine,
    ← vars_eq_bvarSpine]
  congr 1
  congr 1
  · have h : (InductiveSignature.vars nparams 0).map
        ((fun arg => arg.liftN extra nidx) ∘ fun arg => arg.liftN nidx 0) =
        ((InductiveSignature.vars nparams 0).map (fun arg => arg.liftN nidx 0)).map
          (fun arg => arg.liftN extra nidx) := by simp [List.map_map]
    rw [h, vars_lift, Nat.add_zero, vars_lift_below]
  · exact vars_lift_above nidx extra

/-- The checked recursor type is the generator's recursor type as soon as
the minor groups agree: parameters, motives, indices, major and result are
already identified. -/
theorem RecursorConstruction.recursorTarget_eq_of_minors
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (g : InductiveSignature.Instance s)
    (hp : s.params = R.parameterScope.toCtx.reverse)
    (hf : s.families = H.families)
    (hl : g.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some g.targetLevel)
    (hctors : s.constructors.size = (H.recInfos.flatMap (·.minors)).size)
    (hminors : T.minors = g.minors) :
    target = g.recursorType ⟨owner, by rw [hf]; simpa using howner⟩ := by
  have hfam : s.families.size = (H.recInfos.map (·.motive)).size := by
    rw [hf]; simp
  have hmotivesLt : owner < (H.recInfos.map (·.motive)).size := by simpa using howner
  have hp' : g.params = T.params := by
    rw [InductiveSignature.Instance.params, hp, hl, ← H.parameterDomains,
      H.recursorTelescope_params T]
  have hm' : T.motives = g.motives := H.recursorTelescope_motives T g hp hf hl hu
  have him := H.recursorTelescope_indicesMajor howner T hu
  have hres := T.resultShape hmotivesLt
  have hfin : owner < s.families.size := by rw [hf]; simpa using howner
  have hfam' : s.families[(⟨owner, hfin⟩ : Fin s.families.size)] =
      H.families[owner]'(by simpa using howner) := by
    simp [hf]
  have hidxLen : (InductiveSignature.insertBinders
      ((H.declIndexDomains ⟨owner, howner⟩).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size)).length =
      H.recInfos[owner]!.indices.size := by
    simp [InductiveSignature.insertBinders, H.sourceIndices_length]
  have hsplit : InductiveSignature.insertBinders
      ((H.declIndexDomains ⟨owner, howner⟩).map
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) ++
        [VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
            (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
          (bvarSpine (stats.params.size + H.recInfos[owner]!.indices.size))])
      ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size) =
      InductiveSignature.insertBinders
        ((H.declIndexDomains ⟨owner, howner⟩).map
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
        ((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size) ++
      [VExpr.mkApps
        (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
          (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
        (InductiveSignature.vars stats.params.size
          (((H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size) +
            H.recInfos[owner]!.indices.size) ++
          InductiveSignature.vars H.recInfos[owner]!.indices.size 0)] := by
    rw [insertBinders_append_singleton, List.length_map, H.sourceIndices_length, majorDomain_lift]
  rw [hsplit] at him
  have hvars : InductiveSignature.vars H.recInfos[owner]!.indices.size 1 =
      (List.range H.recInfos[owner]!.indices.size).reverse.map fun index => VExpr.bvar (index + 1) := by
    simp [InductiveSignature.vars, Nat.add_comm]
  have hplen : s.params.length = stats.params.size := by
    rw [hp]
    simp [H.sourceParameterCount]
  have him' : T.indices ++ T.major =
      InductiveSignature.insertBinders
        ((H.declIndexDomains ⟨owner, howner⟩).map
          (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
        (s.families.size + s.constructors.size) ++
      [VExpr.mkApps
        (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
          (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
        (InductiveSignature.vars stats.params.size
          ((s.families.size + s.constructors.size) + H.recInfos[owner]!.indices.size) ++
          InductiveSignature.vars H.recInfos[owner]!.indices.size 0)] := by
    rw [him]
    simp only [← hfam, ← hctors]
  have hres' : T.result = VExpr.mkApps
      (.bvar (1 + H.recInfos[owner]!.indices.size + s.constructors.size +
        (s.families.size - 1 - owner)))
      (((List.range H.recInfos[owner]!.indices.size).reverse.map fun index =>
          .bvar (index + 1)) ++ [.bvar 0]) := by
    rw [hres]
    simp only [← hfam, ← hctors]
  have hidxLen' : (InductiveSignature.insertBinders
      ((H.declIndexDomains ⟨owner, howner⟩).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      (s.families.size + s.constructors.size)).length = H.recInfos[owner]!.indices.size := by
    simp [InductiveSignature.insertBinders, H.sourceIndices_length]
  rw [T.target_eq, InductiveSignature.Instance.recursorType]
  simp only [InductiveSignature.Instance.familyApp, InductiveSignature.familyApp]
  rw [hp', ← hm', ← hminors, hfam', H.families_indices ⟨owner, howner⟩,
    H.families_name ⟨owner, howner⟩, hl, hidxLen', hplen, hres', hvars,
    List.append_assoc (T.params ++ T.motives ++ T.minors) T.indices T.major, him',
    ← List.append_assoc]
  congr 3
  omega

/-- The first `n` binder domains of a forall telescope, exactly as they sit in
the expression: the `i`-th domain still carries loose bound variables
`0, …, i - 1` for the `i` binders before it. -/
def Expr.forallDomainList : Nat → Expr → List Expr
  | 0, _ => []
  | n + 1, .forallE _ domain body _ => domain :: forallDomainList n body
  | _, _ => []

theorem Expr.ForallTelescope.forallDomainList_length
    (H : Expr.ForallTelescope source n residual) :
    (Expr.forallDomainList n source).length = n := by
  induction H with
  | nil => simp [Expr.forallDomainList]
  | cons _ ih => simp [Expr.forallDomainList, ih]

/-- Abstracting free variables of a forall telescope abstracts its `i`-th
literal domain at cutoff advanced by the `i` binders before it. -/
theorem Expr.ForallTelescope.forallDomainList_abstractList
    (H : Expr.ForallTelescope source n residual) (fvs : List FVarId) (k : Nat)
    {i : Nat} (hi : i < n) :
    (Expr.forallDomainList n (source.abstractList fvs k))[i]! =
      (Expr.forallDomainList n source)[i]!.abstractList fvs (k + i) := by
  induction H generalizing k i with
  | nil => omega
  | cons _ ih =>
    rw [Expr.abstractList_forallE]
    cases i with
    | zero => simp [Expr.forallDomainList]
    | succ i =>
      simp only [Expr.forallDomainList, List.getElem!_cons_succ]
      rw [ih (k + 1) (by omega)]
      congr 1
      omega

/-- Telescope inversion recording each translated domain: the `i`-th
abstract domain is the translation of the `i`-th literal source domain in the
context extended by the earlier abstract domains. -/
theorem TrExprS.forallTelescope_domains
    (Htel : Expr.ForallTelescope source n residual)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (hlen : domains.length = n) :
    ∀ (i : Nat) (hi : i < domains.length),
      TrExprS env Us (abstractForallContext (domains.take i) Δ)
        (Expr.forallDomainList n source)[i]! (domains[i]'hi) := by
  induction Htel generalizing Δ domains with
  | nil =>
    intro i hi
    simp only [List.length_eq_zero_iff] at hlen
    subst hlen
    simp at hi
  | cons Htel ih =>
    cases domains with
    | nil => simp at hlen
    | cons d ds =>
      simp only [VExpr.wrapForalls, List.foldr_cons] at Htr
      cases Htr with
      | forallE _ _ Hdom Hbody =>
        intro i hi
        cases i with
        | zero => simpa [Expr.forallDomainList, abstractForallContext] using Hdom
        | succ i =>
          have Hi := ih (domains := ds) Hbody (by simpa using hlen) i (by simpa using hi)
          simpa [Expr.forallDomainList, abstractForallContext, List.map_append,
            List.append_assoc] using Hi

/-- The binder domains of a minor hypothesis's higher-order argument
telescope, in order, exactly as they sit in the hypothesis type
`current.lctx.mkForall args motiveApp` (which is also the installed declaration
type, since `(type.consumeTypeAnnotationsVerified annOk) = type`).  The `i`-th domain
is therefore already closed over the arguments before it: its loose bound
variables `0, …, i - 1` refer to those arguments. -/
def InductionHypothesisType.argDomains
    (_O : InductionHypothesisType stats recInfos root field type) : List Expr :=
  Expr.forallDomainList _O.args.size type

theorem InductionHypothesisType.argDomains_length
    (O : InductionHypothesisType stats recInfos root field type) :
    O.argDomains.length = O.args.size :=
  O.sourceTelescope.forallDomainList_length

/-- `recursorTelescope_hypothesisShape` together with the identity of each
higher-order argument domain `A[i]`: it is the translation of the `i`-th
literal domain `O.argDomains[i]!` of the hypothesis type (already closed over
the earlier arguments), closed over the earlier hypotheses at depth `i`, the
fields at depth `j + i` and the outer binders at depth `S.fields.size + j + i`,
in the context extended by `A.take i`. -/
theorem RecursorConstruction.recursorTelescope_hypothesisDomains
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D₀ : FVarDeclAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D₀.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.declFieldDomains mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ (hyps : List VExpr) (res : VExpr) (hhyps : hyps.length = S.hypotheses.size),
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D₀.inBounds) =
        VExpr.wrapForalls fields (VExpr.wrapForalls hyps res) →
      ∀ (j : Nat)
        (origins : MinorInductionHypothesisTypes S.sourceFullContext S.recursiveFields
          S.hypotheses)
        (_hmotives : origins.recInfos.map (·.motive) = H.recInfos.map (·.motive))
        {root : AddInductive.Context} {sourceType : Expr}
        (O : InductionHypothesisType origins.stats origins.recInfos root
          (S.recursiveFields[j]!) sourceType)
        (D : FVarDeclAt S.sourceFullContext S.hypotheses j)
        (_hDtype : D.type = (sourceType.consumeTypeAnnotationsVerified S.sourceFullContext.env.isTypeAnnotationWrapper))
        (_howner' : O.ownerIdx < H.recInfos.size)
        (pos : Nat) (hpos : pos < S.fields_bound.fvars.length)
        (_hfield : S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos)),
      ∃ A I : List VExpr, A.length = O.args.size ∧
        hyps[j]'(by rw [hhyps]; exact D.inBounds) =
          VExpr.wrapForalls A
            (.app
              (VExpr.mkApps (.bvar (S.fields.size + j + O.args.size + minorIdx +
                ((H.recInfos.map (·.motive)).size - 1 - O.ownerIdx))) I)
              (VExpr.mkApps (.bvar (j + O.args.size + (S.fields.size - 1 - pos)))
                (InductiveSignature.vars O.args.size 0))) ∧
        List.Forall₂
          (TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++ A) []))
          ((O.exposedType.getAppArgs[origins.stats.params.size:] : Array Expr).toList.map fun e =>
            (((e.abstractN O.arguments_bound.fvars).abstractList
              (S.hypotheses_bound.fvars.take j) O.args.size).abstractList S.fields_bound.fvars
                (j + O.args.size)).abstractList ys (S.fields.size + j + O.args.size))
          I ∧
        ∀ (i : Nat) (hi : i < A.length),
          TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++
                A.take i) [])
            (((O.argDomains[i]!.abstractList (S.hypotheses_bound.fvars.take j) i).abstractList
              S.fields_bound.fvars (j + i)).abstractList ys (S.fields.size + j + i))
            (A[i]'hi) := by
  intro S fields ys hyps res hhyps hminorEq j origins hmotives root sourceType O D hDtype howner'
    pos hpos hfield
  obtain ⟨A, I, hA, hEq, HI⟩ := H.recursorTelescope_hypothesisShape howner T minorIdx D₀ mowner
    hmowner localIndex hlocal hD hyps res hhyps hminorEq j origins hmotives O D hDtype howner'
    pos hpos hfield
  refine ⟨A, I, hA, hEq, HI, ?_⟩
  intro i hi
  have Hslot := H.recursorTelescope_hypothesisSlot howner T minorIdx D₀ mowner hmowner localIndex
    hlocal hD hyps res hhyps hminorEq j D
  have htype : D.type = sourceType := hDtype.trans O.consumeTypeAnnotationsVerified_eq_self
  rw [htype, hEq] at Hslot
  have Htel₀ := O.sourceTelescope
  have Htel₁ := Htel₀.abstractList (S.hypotheses_bound.fvars.take j)
  have Htel₂ := Htel₁.abstractList S.fields_bound.fvars j
  have Htel₃ := Htel₂.abstractList ys (S.fields.size + j)
  have Hd := TrExprS.forallTelescope_domains Htel₃ Hslot hA i hi
  have hi' : i < O.args.size := hA ▸ hi
  rw [Htel₂.forallDomainList_abstractList _ _ hi', Htel₁.forallDomainList_abstractList _ _ hi',
    Htel₀.forallDomainList_abstractList _ _ hi', Nat.zero_add] at Hd
  have hctx : abstractForallContext (A.take i)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j) []) =
      abstractForallContext
        (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields ++ hyps.take j ++
          A.take i) [] := by
    simp only [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc,
      List.append_nil]
  rw [hctx] at Hd
  exact Hd

end Lean4Lean.VerifyInductive
