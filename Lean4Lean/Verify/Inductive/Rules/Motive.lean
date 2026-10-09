import Lean4Lean.Verify.Inductive.Rules.MinorPremise

/-! The owner motive of a rule. The generated index/major suffix of a recursor is the owner
motive's domain telescope (`RecursorCheck.ownerSuffix_eq_expected`); this alignment is carried
under the constructor fields and transported to the cached parameter context. Every recursor
is well typed in the recursor environment at its identity universe instantiation
(`RecursorCheck.recursorTypingAt`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The generated owner-motive domain is itself an exactly sized typed
index/major telescope.  This follows from the retained executable local
declarations, not by inspecting the translated target: the source closes the
owner indices and major, and abstraction over the preceding recursor binders
preserves that telescope. -/
theorem
    RecursorCheck.installedOwnerMotiveTelescopeShapeAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        ∃ motiveDomains resultLevel,
          motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
          motiveDomains.length = (T.indices ++ T.major).length ∧
          T.motives[owner]! =
            VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
          resultLevel.WF Us.length := by
  dsimp only
  rcases H.installedOwnerMotiveFrameAt owner howner with
    ⟨T, S, hparameters, D, _hdeclarationOrigin, hdeclarationShape,
      suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      _Hsource, _hsource, hsourceDomain, Hdomain, HdomainType⟩
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hsortAbstract (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractList fvars k =
        .sort H.elimLevel := by
    exact Expr.abstractList_eq_self_of_abstract1 (.sort H.elimLevel)
      (by intro fv depth; rfl) fvars k
  have hsortN (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractN fvars k = .sort H.elimLevel := rfl
  have HmajorRaw : Expr.ForallTelescope
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)) 1 (.sort H.elimLevel) := by
    simpa [hsortN] using
      selections.major.forallTelescope (.sort H.elimLevel)
  have Hmajor : Expr.ForallTelescope
      ((H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)).abstractN selections.indices.fvars)
      1 (.sort H.elimLevel) := by
    have HmajorClosed := HmajorRaw.abstractN selections.indices.fvars 0
    simpa only [hsortN] using HmajorClosed
  have Hindices : Expr.ForallTelescope
      (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
          (.sort H.elimLevel)))
      (H.recInfos[owner]!.indices.size + 1) (.sort H.elimLevel) := by
    exact (selections.indices.forallTelescope
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel))).trans Hmajor
  have HsourceTelescope : Expr.ForallTelescope sourceDomain
      (H.recInfos[owner]!.indices.size + 1) (.sort H.elimLevel) := by
    rw [hsourceDomain, hdeclarationShape]
    have Habstract := Hindices.abstractList
      (H.params.fvars ++ H.bindings.motives.fvars.take owner) 0
    simpa only [hsortAbstract] using Habstract
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    HsourceTelescope Hdomain HdomainType
  rcases Htyped.toWrapForalls with
    ⟨motiveDomains, sourceResidual, motiveResult, hlength,
      _HsourceResidual, htarget, Hresult, _HresultType⟩
  have hsourceResidual : sourceResidual = .sort H.elimLevel :=
    _HsourceResidual.residual_eq HsourceTelescope
  subst sourceResidual
  cases Hresult with
  | sort hlevel =>
    have hsuffixLength : motiveDomains.length =
        (T.indices ++ T.major).length := by
      simp only [List.length_append, T.indices_length, T.major_length,
        hlength]
    exact ⟨T, S, hparameters, motiveDomains, _, hlength, hsuffixLength,
      htarget, VLevel.WF.of_ofLevel hlevel⟩

/-- Arbitrary-witness form of `installedOwnerMotiveTelescopeShapeAt`.  Structural
uniqueness transports the semantic shape to the exact `T` already selected
by an equation frame. -/
theorem
    RecursorCheck.installedOwnerMotiveTelescopeShapeForAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : MotiveDecl H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
        motiveDomains.length = (T.indices ++ T.major).length ∧
        T.motives[owner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        resultLevel.WF Us.length := by
  dsimp only
  rcases H.installedOwnerMotiveTelescopeShapeAt owner howner with
    ⟨T₀, S, hparameters, motiveDomains, resultLevel,
      hdomainLength, hsuffixLength, hmotive, hresultLevel⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams, hmotives, _hminors, hindices, hmajor, _hresult⟩
  rw [hparams] at hparameters
  rw [hmotives] at hmotive
  rw [hindices, hmajor] at hsuffixLength
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hsuffixLength, hmotive, hresultLevel⟩

/-- Inserting binders twice at the same cut inserts their sum. -/
theorem _root_.Lean4Lean.InductiveSignature.insertBinders_insertBinders
    (l : List VExpr) (a b : Nat) :
    InductiveSignature.insertBinders (InductiveSignature.insertBinders l a) b =
      InductiveSignature.insertBinders l (a + b) := by
  apply List.ext_getElem
  · simp [InductiveSignature.insertBinders]
  · intro i h₁ h₂
    simp [InductiveSignature.insertBinders, List.getElem_zipIdx,
      VExpr.liftN'_liftN_hi]

/-- Two retained recursor telescopes with the same translated target have
the same motive group and the same index/major suffix, whatever their
environments and sources. -/
theorem RecursorTypeTelescope.motivesSuffix_eq_of_target
    {env₁ env₂ : VEnv} {Us₁ Us₂ : List Name} {source₁ source₂ : Expr}
    {target₁ target₂ : VExpr}
    {numParams numMotives numMinors numIndices ownerIdx : Nat}
    (T₁ : RecursorTypeTelescope env₁ Us₁ source₁ target₁
      numParams numMotives numMinors numIndices ownerIdx)
    (T₂ : RecursorTypeTelescope env₂ Us₂ source₂ target₂
      numParams numMotives numMinors numIndices ownerIdx)
    (htarget : target₁ = target₂) :
    T₁.motives = T₂.motives ∧ T₁.indices ++ T₁.major = T₂.indices ++ T₂.major := by
  let domains₁ :=
    T₁.params ++ T₁.motives ++ T₁.minors ++ T₁.indices ++ T₁.major
  let domains₂ :=
    T₂.params ++ T₂.motives ++ T₂.minors ++ T₂.indices ++ T₂.major
  have hlength₁ : domains₁.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains₁, List.length_append, T₁.params_length,
      T₁.motives_length, T₁.minors_length, T₁.indices_length,
      T₁.major_length]
  have hlength₂ : domains₂.length =
      numParams + numMotives + numMinors + numIndices + 1 := by
    simp only [domains₂, List.length_append, T₂.params_length,
      T₂.motives_length, T₂.minors_length, T₂.indices_length,
      T₂.major_length]
  have hwrapped : VExpr.wrapForalls domains₁ T₁.result =
      VExpr.wrapForalls domains₂ T₂.result := by
    rw [← T₁.target_eq, ← T₂.target_eq, htarget]
  have hdomains : domains₁ = domains₂ :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := [])
      hlength₁ hlength₂ (by simpa using hwrapped)
  have H₀ : T₁.params ++
        (T₁.motives ++ (T₁.minors ++ (T₁.indices ++ T₁.major))) =
      T₂.params ++
        (T₂.motives ++ (T₂.minors ++ (T₂.indices ++ T₂.major))) := by
    simpa [domains₁, domains₂, List.append_assoc] using hdomains
  have H₁ := List.append_inj_right H₀ (by rw [T₁.params_length, T₂.params_length])
  have hmotives := List.append_inj_left H₁
    (by rw [T₁.motives_length, T₂.motives_length])
  have H₂ := List.append_inj_right H₁ (by rw [T₁.motives_length, T₂.motives_length])
  have H₃ := List.append_inj_right H₂ (by rw [T₁.minors_length, T₂.minors_length])
  exact ⟨hmotives, H₃⟩

/-- The checked recursor telescope decomposes the canonical generated
recursor type itself. -/
theorem RecursorConstruction.recursorTelescopeGenerated
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat)
    (howner : owner < H.recInfos.size) :
    Nonempty (RecursorTypeTelescope R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos
        H.localContext.lctx owner)
      (H.recursorTarget owner).type stats.params.size
      (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size
      owner) := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  have henv : R.context.venv.WF := by
    rw [← H.recursorEnv]
    exact H.recursorWF.checking.tr.wf
  obtain ⟨target, Htr₀, Htype₀⟩ := H.recursorTypeTranslation owner hsourceOwner
  have Htr := H.typeTranslations owner hsourceOwner
  have Heq := Htr.uniq henv .nil Htr₀
  have Htype : R.context.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (H.recursorTarget owner).type :=
    Htype₀.defeqU_l henv (by trivial) Heq.symm
  let Hsel := H.bindings.toRecursorBinderGroups H.localWF H.params owner howner
  have hnoalias := H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner
  have Htel := Hsel.forallTelescope
    (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
      H.recInfos[owner]!.major)
  rw [Hsel.residual_eq_concreteRecursorResult howner hnoalias] at Htel
  have Htel' : Expr.ForallTelescope
      (AddInductive.declareRecursors.recursorType stats H.recInfos
        H.localContext.lctx owner)
      (stats.params.size + (H.recInfos.map (·.motive)).size +
        (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size + 1)
      (concreteRecursorResult (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size
        owner) := Htel
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel' Htr Htype
  rcases TrExprS.forallTelescope_shape_with_context Htel' Htr with
    ⟨domains, result, hlen, htarget, Hresult⟩
  rcases List.exists_append_five_of_length_eq domains stats.params.size
      (H.recInfos.map (·.motive)).size (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size 1 hlen with
    ⟨params, motives, minors, indices, major, hdomains, hp, hm, hmi, hi, hma⟩
  refine ⟨⟨params, motives, minors, indices, major, result, ?_, hp, hm, hmi, hi,
    hma, Htyped, ?_⟩⟩
  · simpa [hdomains] using htarget
  · simpa [hdomains] using Hresult

/-- The generated index/major suffix of a recursor is literally the owner
motive's domain telescope, lifted beneath the later motives and all minors.
Both are produced by the same generator from the owner family's indices. -/
theorem RecursorCheck.ownerSuffix_eq_expected
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (motiveDomains : List VExpr) (resultLevel : VLevel)
    (hmotive : T.motives[owner]! =
      VExpr.wrapForalls motiveDomains (.sort resultLevel))
    (hlength : motiveDomains.length = H.recInfos[owner]!.indices.size + 1) :
    let later := T.motives.drop (owner + 1) ++ T.minors
    T.indices ++ T.major =
      (liftContextPrefixAt (later.length + 1) 0 motiveDomains.reverse).reverse := by
  dsimp only
  have hrec : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  obtain ⟨T₀⟩ := H.recursorTelescopeGenerated owner hrec
  have htgt : H.entries[owner].2.type = (H.recursorTarget owner).type := by
    rw [H.targets owner howner]
  obtain ⟨hmot, hidx⟩ := T.motivesSuffix_eq_of_target T₀ htgt
  let g := H.generatedInstance H.familySignature
  have hm := H.recursorTelescope_motives T₀ g rfl rfl rfl
    (H.generatedInstance_target _)
  have him := H.recursorTelescope_indicesMajor hrec T₀
    (H.generatedInstance_target H.familySignature)
  have hfam : owner < H.families.size := by simpa using hrec
  have hgm : g.motives[owner]! = g.motive (H.families[owner]'hfam) owner := by
    have hlt : owner < g.motives.length := by
      simp [InductiveSignature.Instance.motives,
        RecursorConstruction.familySignature, hrec]
    rw [getElem!_pos g.motives owner hlt]
    simp [InductiveSignature.Instance.motives,
      RecursorConstruction.familySignature, List.getElem_zipIdx]
  have hTm : T.motives[owner]! = g.motives[owner]! := by rw [hmot, hm]
  rw [hTm, hgm] at hmotive
  have hidxs := H.families_indices ⟨owner, hrec⟩
  have hname := H.families_name ⟨owner, hrec⟩
  simp only [InductiveSignature.Instance.motive] at hmotive
  rw [hidxs, hname] at hmotive
  have hsrcLen := H.sourceIndices_length ⟨owner, hrec⟩
  have hplen : H.familySignature.params.length = stats.params.size := by
    simp [RecursorConstruction.familySignature, H.sourceParameterCount]
  rw [hplen] at hmotive
  let A₀ := (H.declIndexDomains ⟨owner, hrec⟩).map
    (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
  have hA₀len : A₀.length = H.recInfos[owner]!.indices.size := by
    simp [A₀, hsrcLen]
  have hdomains : motiveDomains =
      InductiveSignature.insertBinders A₀ owner ++
        [VExpr.mkApps
          (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact hrec)).name
            (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
          (InductiveSignature.vars stats.params.size
              (owner + (InductiveSignature.insertBinders A₀ owner).length) ++
            InductiveSignature.vars (InductiveSignature.insertBinders A₀ owner).length 0)] := by
    apply VExpr.wrapForalls_prefix_domains_eq (suffix := []) hlength
      (by simp [InductiveSignature.insertBinders, hA₀len])
    rw [List.append_nil]
    exact hmotive.symm
  rw [hidx, him, ← insertBinders_eq_prefix, hdomains,
    insertBinders_append_singleton, insertBinders_append_singleton,
    InductiveSignature.insertBinders_insertBinders]
  have hinsLen : (InductiveSignature.insertBinders A₀ owner).length =
      H.recInfos[owner]!.indices.size := by
    simp [InductiveSignature.insertBinders, hA₀len]
  have hlater : owner + ((T.motives.drop (owner + 1) ++ T.minors).length + 1) =
      (H.recInfos.map (·.motive)).size + (H.recInfos.flatMap (·.minors)).size := by
    simp only [List.length_append, List.length_drop, T.motives_length,
      T.minors_length]
    have : owner < (H.recInfos.map (·.motive)).size := by simpa using hrec
    omega
  rw [hlater, hinsLen]
  congr 2
  rw [← majorDomain_lift, VExpr.liftN'_liftN_hi, hlater]
  simp [hsrcLen]

/-- Complete dependent alignment of the generated owner index/major suffix
with the owner motive's declared domains: the two telescopes coincide. -/
theorem RecursorCheck.ownerMotiveSuffixContextFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (motiveDomains : List VExpr) (resultLevel : VLevel)
    (hmotive : T.motives[owner]! =
      VExpr.wrapForalls motiveDomains (.sort resultLevel))
    (hlength : motiveDomains.length = H.recInfos[owner]!.indices.size + 1) :
    let outer := T.params ++ T.motives ++ T.minors
    let suffix := T.indices ++ T.major
    let later := T.motives.drop (owner + 1) ++ T.minors
    let expected :=
      (liftContextPrefixAt (later.length + 1) 0 motiveDomains.reverse).reverse
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (suffix.reverse ++ outer.reverse)
      (expected.reverse ++ outer.reverse) := by
  dsimp only
  have heq := H.ownerSuffix_eq_expected owner howner T motiveDomains
    resultLevel hmotive hlength
  dsimp only at heq
  rw [← heq]
  have Hfull := T.fullContextResultType H.outVEnvWF.ordered
  apply VEnv.IsDefEqCtx.refl
  simpa [List.reverse_append, List.append_assoc] using Hfull.1

/-- Arbitrary-witness specialization of the complete suffix alignment, for
direct use with the telescope retained by the canonical equation frame. -/
theorem
    RecursorCheck.RuleAlignment.installedOwnerMotiveSuffixContextAlignmentFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : MotiveDecl H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
        T.motives[owner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        let outer := T.params ++ T.motives ++ T.minors
        let suffix := T.indices ++ T.major
        let later := T.motives.drop (owner + 1) ++ T.minors
        let expected :=
          (liftContextPrefixAt (later.length + 1) 0
            motiveDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (suffix.reverse ++ outer.reverse)
          (expected.reverse ++ outer.reverse) := by
  dsimp only
  rcases H.installedOwnerMotiveTelescopeShapeForAt owner howner T with
    ⟨S, hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have Hsuffix := H.ownerMotiveSuffixContextFor owner howner T
    motiveDomains resultLevel hmotive hdomainLength
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Hsuffix⟩

/-- Insert an exact constructor-field telescope beneath both sides of the
owner index/major alignment.  This is the context conversion needed by the
equation LHS: the generated recursor suffix and the independent motive
domains are weakened through precisely the same locally bound fields. -/
theorem
    RecursorCheck.RuleAlignment.installedOwnerMotiveSuffixAlignmentUnderFields
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : MotiveDecl H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
        T.motives[owner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        let outer := T.params ++ T.motives ++ T.minors
        let suffix := T.indices ++ T.major
        let later := T.motives.drop (owner + 1) ++ T.minors
        let expected :=
          (liftContextPrefixAt (later.length + 1) 0
            motiveDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (liftContextPrefix fieldDomains.length suffix.reverse ++
            fieldDomains.reverse ++ outer.reverse)
          (liftContextPrefix fieldDomains.length expected.reverse ++
            fieldDomains.reverse ++ outer.reverse) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases RecursorCheck.RuleAlignment.installedOwnerMotiveSuffixContextAlignmentFor (H := H) T with
    ⟨S, hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Hsuffix⟩
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have hsuffixLength : suffix.reverse.length = expected.reverse.length := by
    have htotal := Hsuffix.length_eq
    simp [suffix, later, expected] at htotal ⊢
    omega
  have hfieldCtx : OnCtx (fieldDomains.reverse ++ outer.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [outer, List.reverse_append, List.append_assoc] using hctx
  have Haligned := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered suffix.reverse expected.reverse
      fieldDomains.reverse outer.reverse Hsuffix hsuffixLength hfieldCtx
  have Haligned' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftContextPrefix fieldDomains.length suffix.reverse ++
        fieldDomains.reverse ++ outer.reverse)
      (liftContextPrefix fieldDomains.length expected.reverse ++
        fieldDomains.reverse ++ outer.reverse) := by
    simpa [List.length_reverse] using Haligned
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Haligned'⟩

/-- Re-close the field-lifted suffix conversion as equality of function
types in the canonical equation context.  The common residual is the
generated owner-motive application `T.result`; only the dependent domains
differ, and `closeWrapForalls` discharges exactly that distinction. -/
theorem
    RecursorCheck.RuleAlignment.installedOwnerMotiveSuffixTypeAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := T.params ++ T.motives ++ T.minors
      let suffix := T.indices ++ T.major
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.IsDefEqU Us.length
        (fieldDomains.reverse ++ outer.reverse)
        ((VExpr.wrapForalls suffix T.result).liftN
          fieldDomains.length 0)
        (VExpr.wrapForalls
          ((liftContextPrefix fieldDomains.length expected.reverse).reverse)
          (T.result.liftN fieldDomains.length suffix.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases RecursorCheck.RuleAlignment.installedOwnerMotiveSuffixAlignmentUnderFields
    (H := H) (owner := owner) (howner := howner) T fieldDomains hctx with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Haligned⟩
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let actualRecent := liftContextPrefix fieldDomains.length suffix.reverse
  let expectedRecent :=
    liftContextPrefix fieldDomains.length expected.reverse
  let base := fieldDomains.reverse ++ outer.reverse
  have Haligned' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (actualRecent ++ base) (expectedRecent ++ base) := by
    simpa [Us, actualRecent, expectedRecent, base, outer, suffix, later,
      expected] using Haligned
  have HprefixType := Hprefix.isType H.outVEnvWF hctx
  rw [VExpr.liftN_wrapForalls] at HprefixType
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    (ctx := base) (domains := actualRecent.reverse)
    (result := T.result.liftN fieldDomains.length suffix.length)
    (by simpa [base, outer] using hctx) (by
      simpa [actualRecent, suffix, base, outer, liftContextPrefix,
        Nat.add_comm] using
        HprefixType)
  rcases Hopened.2 with ⟨bodyLevel, Hbody⟩
  have Hbody' : H.outVEnv.HasType Us.length
      (liftContextPrefix fieldDomains.length suffix.reverse ++
        fieldDomains.reverse ++ outer.reverse)
      (T.result.liftN fieldDomains.length suffix.length)
      (.sort bodyLevel) := by
    simpa [actualRecent, base] using Hbody
  have Hbody'' : H.outVEnv.HasType Us.length (actualRecent ++ base)
      (T.result.liftN fieldDomains.length suffix.length)
      (.sort bodyLevel) := by
    simpa [actualRecent, base, outer, suffix] using Hbody'
  have hrecentLength : expectedRecent.length = actualRecent.length := by
    have hlength := Haligned'.length_eq
    simp only [List.length_append] at hlength
    omega
  have Hclosed := VEnv.IsDefEqCtx.closeHeads Haligned'
    actualRecent.length (by simp [actualRecent, suffix]) Hbody''
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  have Hclosed' : H.outVEnv.IsDefEq Us.length base
      (VExpr.wrapForalls actualRecent.reverse
        (T.result.liftN fieldDomains.length suffix.length))
      (VExpr.wrapForalls expectedRecent.reverse
        (T.result.liftN fieldDomains.length suffix.length))
      (.sort closedLevel) := by
    have hrightTake : (expectedRecent ++ base).take actualRecent.length =
        expectedRecent := by
      rw [← hrecentLength]
      simp
    rw [List.drop_left, List.take_left, hrightTake] at Hclosed
    exact Hclosed
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_⟩
  refine ⟨.sort closedLevel, ?_⟩
  change H.outVEnv.IsDefEq Us.length base
    ((VExpr.wrapForalls suffix T.result).liftN fieldDomains.length 0)
    (VExpr.wrapForalls expectedRecent.reverse
      (T.result.liftN fieldDomains.length suffix.length))
    (.sort closedLevel)
  rw [VExpr.liftN_wrapForalls]
  simpa [actualRecent, base, outer, suffix,
    liftContextPrefix, Nat.add_comm] using Hclosed'

/-- The owner-motive local itself is the comparison function for concrete
suffix application.  After weakening beneath constructor fields, its type
has exactly the independent domains appearing on the right side of
`installedOwnerMotiveSuffixTypeAlignment`, but ends in the elimination sort
rather than the generated recursor result. -/
theorem
    RecursorCheck.RuleAlignment.installedOwnerMotiveFieldWitnessTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := T.params ++ T.motives ++ T.minors
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length
        (fieldDomains.reverse ++ outer.reverse)
        (.bvar (fieldDomains.length + later.length))
        (VExpr.wrapForalls
          ((liftContextPrefix fieldDomains.length expected.reverse).reverse)
          (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases H.installedOwnerMotiveTelescopeShapeForAt owner howner T with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hownerRecInfo
  let outer := T.params ++ T.motives ++ T.minors
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have Hmotive := T.ownerMotiveOuterBvarTyping hownerMotive
  have W : Ctx.LiftN fieldDomains.length 0 outer.reverse
      (fieldDomains.reverse ++ outer.reverse) := by
    exact .zero fieldDomains.reverse (by simp)
  have Hweak := Hmotive.weakN H.outVEnvWF.ordered W
  rw [show T.motives[owner]'hownerMotive = T.motives[owner]! by
    exact (getElem!_pos T.motives owner hownerMotive).symm,
    hmotive] at Hweak
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive, by
    simpa [outer, later, expected, VExpr.liftN_wrapForalls,
      liftContextPrefix, VExpr.liftN_liftN, VExpr.liftN, liftVar_base,
      Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using Hweak⟩

/-- Transport the field-weakened owner-motive witness from the generated
parameter domains to the cached constructor-checking parameter context.  The
owner variable and its complete dependent function type are unchanged; only
the outer parameter domains are converted. -/
theorem
    RecursorCheck.RuleAlignment.installedCachedOwnerMotiveWitnessTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (Hctx :
      let parameterDecls :=
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let canonicalDomains :=
        (T.params ++ T.motives ++ T.minors) ++ fieldDomains
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        canonicalDomains.reverse cachedDomains.reverse) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    let cachedDomains :=
      (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
        fieldDomains
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length cachedDomains.reverse
        (.bvar (fieldDomains.length + later.length))
        (VExpr.wrapForalls
          ((liftContextPrefix fieldDomains.length expected.reverse).reverse)
          (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  rcases RecursorCheck.RuleAlignment.installedOwnerMotiveFieldWitnessTyping
    (H := H) T fieldDomains with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Hmotive⟩
  have HmotiveCanonical : H.outVEnv.HasType Us.length
      canonicalDomains.reverse
      (.bvar
        (fieldDomains.length +
          (T.motives.drop (owner + 1) ++ T.minors).length))
      (VExpr.wrapForalls
        ((liftContextPrefix fieldDomains.length
          ((liftContextPrefixAt
            ((T.motives.drop (owner + 1) ++ T.minors).length + 1) 0
            motiveDomains.reverse).reverse).reverse).reverse)
        (.sort resultLevel)) := by
    simpa [canonicalDomains, List.reverse_append, List.append_assoc] using
      Hmotive
  have HmotiveCached :=
    HmotiveCanonical.defeqDFC H.outVEnvWF.ordered Hctx
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive, by
    simpa [cachedDomains] using HmotiveCached⟩

/-- In the cached equation context, the recursor prefix and the owner motive
are typed by forall telescopes with literally the same dependent domains.
Their residuals deliberately differ: the prefix returns the generated
recursor result, while the motive application returns an elimination sort.
This is the form in which `SameTelescopeDomains` compares the two applications. -/
theorem
    RecursorCheck.RuleAlignment.installedCachedPrefixOwnerTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (prefixTarget : VExpr)
    (Hfull :
      let parameterDecls :=
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let canonicalDomains :=
        (T.params ++ T.motives ++ T.minors) ++ fieldDomains
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        canonicalDomains.reverse cachedDomains.reverse)
    (HcachedCtx :
      let parameterDecls :=
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      OnCtx cachedDomains.reverse
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (HprefixCached :
      let parameterDecls :=
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      H.outVEnv.HasType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        cachedDomains.reverse prefixTarget
        ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
          fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    let cachedDomains :=
      (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
        fieldDomains
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := T.indices ++ T.major
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix fieldDomains.length expected.reverse).reverse
      H.outVEnv.HasType Us.length cachedDomains.reverse prefixTarget
          (VExpr.wrapForalls expectedDomains
            (T.result.liftN fieldDomains.length suffix.length)) ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse
          (.bvar (fieldDomains.length + later.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) ∧
        SameTelescopeDomains expectedDomains.length
          (VExpr.wrapForalls expectedDomains
            (T.result.liftN fieldDomains.length suffix.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  have HcanonicalCtx : OnCtx canonicalDomains.reverse
      (H.outVEnv.IsType Us.length) :=
    Hfull.isType
  have HprefixCanonical : H.outVEnv.HasType Us.length
      canonicalDomains.reverse prefixTarget
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0) :=
    HprefixCached.defeqDFC H.outVEnvWF.ordered
      (Hfull.symm H.outVEnvWF.ordered)
  rcases RecursorCheck.RuleAlignment.installedOwnerMotiveSuffixTypeAlignment
    (H := H) T fieldDomains prefixTarget
      (by simpa [canonicalDomains] using HcanonicalCtx)
      (by simpa [canonicalDomains] using HprefixCanonical) with
    ⟨alignedDomains, alignedLevel, halignedLength, halignedMotive,
      Haligned⟩
  rcases RecursorCheck.RuleAlignment.installedCachedOwnerMotiveWitnessTyping
    (H := H) (owner := owner) (howner := howner) T fieldDomains Hfull with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Hmotive⟩
  have hdomains : motiveDomains = alignedDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq hdomainLength halignedLength
      (suffix := [])
    simpa using hmotive.symm.trans halignedMotive
  subst alignedDomains
  have hresultLevel : resultLevel = alignedLevel := by
    have hsort : VExpr.sort resultLevel = VExpr.sort alignedLevel := by
      apply VExpr.wrapForalls_left_cancel motiveDomains
      exact hmotive.symm.trans halignedMotive
    exact VExpr.sort.inj hsort
  subst alignedLevel
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix fieldDomains.length expected.reverse).reverse
  have HalignedCanonical : H.outVEnv.IsDefEqU Us.length
      canonicalDomains.reverse
      ((VExpr.wrapForalls suffix T.result).liftN fieldDomains.length 0)
      (VExpr.wrapForalls expectedDomains
        (T.result.liftN fieldDomains.length suffix.length)) := by
    simpa [canonicalDomains, suffix, later, expected, expectedDomains,
      List.reverse_append] using Haligned
  have HalignedCached :=
    HalignedCanonical.defeqDFC H.outVEnvWF.ordered Hfull
  have HprefixExpected : H.outVEnv.HasType Us.length cachedDomains.reverse
      prefixTarget
      (VExpr.wrapForalls expectedDomains
        (T.result.liftN fieldDomains.length suffix.length)) := by
    exact HprefixCached.defeqU_r H.outVEnvWF HcachedCtx HalignedCached
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
    HprefixExpected, ?_, ?_⟩
  · simpa [cachedDomains, suffix, later, expected, expectedDomains] using
      Hmotive
  · exact SameTelescopeDomains.wrapForalls expectedDomains _ _

/-- The generated owner-motive domain and the retained first-pass motive are
the same concrete declaration viewed at the two contexts that still have to
be related.  The retained closed scope is now decomposed explicitly into its
interleaved executable ambient prefix and the very parameter scope aligned
with the generated telescope.  No index, major, or current-motive weakening
remains hidden in this frame. -/
theorem
    RecursorCheck.installedOwnerClosedMotiveFrameAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.motiveParameterScope.toCtx ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.motiveSourceScope.toCtx ∧
        VLCtx.FVLift' S.motiveSourceScope S.motiveSourceExpanded
            0 S.motiveSourceShift 0 ∧
        VLCtx.IsDefEq H.outVEnv Us.length S.motiveSourceExpanded
            S.motiveClosedScope ∧
        S.motiveClosedScope =
            S.motiveClosedAmbient ++ S.motiveParameterScope ∧
        TrExprS H.outVEnv Us S.motiveClosedScope
          (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel)))
          S.motiveClosedTarget ∧
        H.outVEnv.IsType Us.length S.motiveClosedScope.toCtx
          S.motiveClosedTarget ∧
        H.outVEnv.IsDefEqU Us.length S.motiveClosedScope.toCtx
          S.motiveClosedTarget S.motiveClosedCanonicalTarget ∧
        S.motiveType = S.motiveReopenedCanonicalTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives.take owner) [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel))).abstractList
                (H.params.fvars ++ H.bindings.motives.fvars.take owner))
          T.motives[owner]! := by
  dsimp only
  rcases H.installedOwnerMotiveDomainTranslationAt owner howner with
    ⟨T, S, hparameters, Hgenerated, _HgeneratedType⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hparameterScope := S.motiveParameterAlignment.mono hbase
  have hparameters' :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      hparameters hparameterScope
  have hsourceScope := S.motiveSourceAlignment.mono hbase
  have hsource :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      hparameters hsourceScope
  exact ⟨T, S, hparameters', hsource, S.motiveSourceLift,
    S.motiveSourceContext.mono hbase, S.motiveClosedContext,
    S.motiveClosedTr.mono hbase, S.motiveClosedType.mono hbase,
    S.motiveClosedCanonicalDefEq.mono hbase, S.motiveTypeCanonicalEq,
    Hgenerated⟩

/-- The executable motive translated in the canonical parameter scope, as
replayed in the checker context of the first pass. -/
theorem
    RecursorCheck.installedOwnerScopedMotiveTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        ∃ narrowTarget,
          VEnv.IsDefEqCtx H.outVEnv Us.length []
              T.params.reverse S.motiveSourceScope.toCtx ∧
          TrExprS H.outVEnv Us S.motiveSourceScope
            (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
              (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
                (.sort H.elimLevel)))
            narrowTarget ∧
          H.outVEnv.IsDefEqU Us.length S.motiveSourceScope.toCtx
            narrowTarget S.canonical.motiveType ∧
          TrExprS H.outVEnv Us
            (abstractForallContext
              (T.params ++ T.motives.take owner) [])
            ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
              (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
                (.sort H.elimLevel))).abstractList
                  (H.params.fvars ++ H.bindings.motives.fvars.take owner))
            T.motives[owner]! := by
  dsimp only
  rcases H.installedOwnerClosedMotiveFrameAt owner howner with
    ⟨T, S, _hparameters, hsource, _W, _Hcontext, _hdecomposition,
      _HclosedTr, _HclosedType, _HclosedCanonical, _hmotiveType,
      Hgenerated⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  exact ⟨T, S, S.motiveSourceTarget, hsource, S.motiveSourceTr.mono hbase,
    S.motiveSourceCanonical.mono hbase, Hgenerated⟩

/-- Abstract the exact cached parameter suffix of the dependency-selected executable
motive, then transport it to the generated parameter telescope.  Earlier
mutual motives are absent from the concrete source, so adding their abstract
binders is precisely ordinary bound-variable weakening. -/
theorem
    RecursorCheck.installedOwnerMotiveDomainAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MotiveDecl H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.motiveSourceScope.toCtx ∧
        H.outVEnv.IsDefEqU Us.length
          (abstractForallContext
            (T.params ++ T.motives.take owner) []).toCtx
          T.motives[owner]!
          (S.canonical.motiveType.liftN
            (T.motives.take owner).length 0) := by
  dsimp only
  rcases H.installedOwnerScopedMotiveTranslationAt owner howner with
    ⟨T, S, narrowTarget, hparams, Hnarrow, Hcanonical, Hgenerated⟩
  let source := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel))
  have HnarrowParameters : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      S.motiveParameterScope source narrowTarget := by
    simpa [source, S.motiveSourceParameterScope] using Hnarrow
  rcases cachedParameterDecls_fvars S.motiveParameterDecls with
    ⟨parameterFVars, hparameterExprs, hparameterScopeFVars⟩
  have hstatsParams : stats.params.toList.reverse =
      H.params.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList H.params.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have hparameterFVars : parameterFVars = H.params.fvars.reverse := by
    apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
    exact hparameterExprs.symm.trans hstatsParams
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      H.params.fvars.reverse S.motiveParameterScope := by
    have Hcached := S.motiveParameterDecls
    rw [hparameterExprs] at Hcached
    rw [List.forall₂_map_left_iff] at Hcached
    have Hdecls' : List.Forall₂
        (fun fv entry => ∃ deps type,
          entry = (some (fv, deps), .vlam type))
        parameterFVars S.motiveParameterScope :=
      Lean4Lean.List.Forall₂.imp
      (fun fv entry hentry => by
        rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
        cases Expr.fvar.inj hparam
        exact ⟨deps, type, hentry⟩) Hcached
    simpa [hparameterFVars] using Hdecls'
  have houterNodup := H.bindings.outerNodup H.params H.noAlias
  have hparamsMotivesNodup :
      (H.params.fvars ++ H.bindings.motives.fvars).Nodup :=
    (List.nodup_append.mp houterNodup).1
  have hparamsNodup : H.params.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr
      (List.nodup_append.mp hparamsMotivesNodup).1
  have HparameterAbstract :=
    Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
      (domains := []) Hdecls hparamsNodup (by
        simpa [abstractForallContext] using HnarrowParameters)
  simp only [List.reverse_reverse] at HparameterAbstract
  have HparameterAbstract' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext S.motiveParameterScope.toCtx.reverse [])
      (source.abstractList H.params.fvars) narrowTarget := by
    simpa using HparameterAbstract
  have HparameterContext : VLCtx.IsDefEq H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext T.params [])
      (abstractForallContext
        S.motiveParameterScope.toCtx.reverse []) := by
    have hparams' := hparams
    rw [S.motiveSourceParameterScope] at hparams'
    exact abstractForallContext.isDefEq (by simpa using hparams')
  rcases HparameterAbstract'.defeqDFC H.outVEnvWF
      (HparameterContext.symm H.outVEnvWF.ordered) with
    ⟨parameterTarget, HparameterTarget⟩
  have HparameterTargets := HparameterAbstract'.uniq H.outVEnvWF
    (HparameterContext.symm H.outVEnvWF.ordered) HparameterTarget
  have HcanonicalParameters : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        S.motiveParameterScope.toCtx.reverse []).toCtx
      narrowTarget S.canonical.motiveType := by
    have hctx :
        (abstractForallContext
          S.motiveParameterScope.toCtx.reverse []).toCtx =
          S.motiveParameterScope.toCtx := by
      simp [abstractForallContext]
    rw [hctx, ← S.motiveSourceParameterScope]
    exact Hcanonical
  have HparameterCanonicalAtSource : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        S.motiveParameterScope.toCtx.reverse []).toCtx
      parameterTarget S.canonical.motiveType :=
    HparameterTargets.symm.trans H.outVEnvWF
      (HparameterContext.symm H.outVEnvWF.ordered).wf.toCtx
      HcanonicalParameters
  have HparameterCanonical := HparameterCanonicalAtSource.defeqDFC
    H.outVEnvWF.ordered
    (HparameterContext.symm H.outVEnvWF.ordered).defeqCtx
  let earlierFVars := H.bindings.motives.fvars.take owner
  have hsourceParameters : source.FVarsIn
      (· ∈ H.params.fvars) := by
    have Hfv := Hnarrow.fvarsIn
    rw [S.motiveSourceParameterScope, hparameterScopeFVars,
      hparameterFVars] at Hfv
    exact Hfv.mono fun fv hfv => by simpa using hfv
  have hsourceClosed : Closed source 0 := by
    have hclosed := Hnarrow.closed
    rw [S.motiveSourceNoBV] at hclosed
    exact hclosed
  have hsourceAvoidsEarlier : source.FVarsIn (· ∉ earlierFVars) := by
    exact hsourceParameters.mono fun fv hfv hearlier => by
      have hdisjoint := (List.nodup_append.mp hparamsMotivesNodup).2.2
      exact hdisjoint fv hfv fv (List.mem_of_mem_take hearlier) rfl
  have hearlierAbstract : source.abstractList earlierFVars = source :=
    hsourceAvoidsEarlier.abstractList_eq_self hsourceClosed
  have hearlierNodup : earlierFVars.Nodup := by
    exact (List.nodup_append.mp hparamsMotivesNodup).2.1.sublist
      (List.take_sublist owner H.bindings.motives.fvars)
  have hparamsNodup' : H.params.fvars.Nodup :=
    List.nodup_reverse.mp hparamsNodup
  have hparamsEarlierNodup :
      (H.params.fvars ++ earlierFVars).Nodup := by
    exact hparamsMotivesNodup.sublist
      ((List.Sublist.refl H.params.fvars).append
        (List.take_sublist owner H.bindings.motives.fvars))
  have habstractShape :
      (source.abstractList H.params.fvars).liftLooseBVars'
          0 earlierFVars.length =
        source.abstractList (H.params.fvars ++ earlierFVars) := by
    have hshift := Expr.abstractList_add_eq_liftLooseBVars
      (e := source) (fvars := H.params.fvars) (depth := 0)
      (extra := earlierFVars.length) hsourceClosed hparamsNodup'
    have happend := Expr.abstractList_after_inner
      (e := source) (outer := H.params.fvars)
      (inner := earlierFVars) (k := 0) hparamsEarlierNodup
    rw [hearlierAbstract] at happend
    exact hshift.symm.trans happend
  have W := abstractForallContext.bvLift (T.motives.take owner)
    (abstractForallContext T.params [])
  have HparameterWeak := HparameterTarget.weakBV
    H.outVEnvWF.ordered W
  have HparameterWeak' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives.take owner) [])
      (source.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars.take owner))
      (parameterTarget.liftN (T.motives.take owner).length 0) := by
    have hrecInfo : owner < H.recInfos.size := by
      simpa [H.generated.length] using howner
    have hownerMotive : owner < T.motives.length := by
      rw [T.motives_length]
      simpa using hrecInfo
    have hownerBinding : owner < H.bindings.motives.fvars.length := by
      have hlength : H.bindings.motives.fvars.length = H.recInfos.size := by
        have h := congrArg Array.size H.bindings.motives.expressions
        simpa using h.symm
      rw [hlength]
      exact hrecInfo
    have htakeT : (T.motives.take owner).length = owner := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hownerMotive)]
    have htakeSource : earlierFVars.length = owner := by
      simp [earlierFVars, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hownerBinding)]
    have hweakContext :
        abstractForallContext (T.motives.take owner)
            (abstractForallContext T.params []) =
          abstractForallContext
            (T.params ++ T.motives.take owner) [] := by
      simp [abstractForallContext, List.reverse_append, List.map_append,
        List.map_take]
    rw [htakeT] at HparameterWeak
    rw [← habstractShape, htakeT, htakeSource, ← hweakContext]
    exact HparameterWeak
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have anonymousWF : ∀ types : List VExpr,
      OnCtx types (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) →
      VLCtx.WF H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        (types.map fun type =>
          ((none, .vlam type) :
            Option (FVarId × List FVarId) × VLocalDecl)) := by
    intro types Htypes
    induction types with
    | nil => trivial
    | cons type types ih =>
      have Htype : H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          (VLCtx.toCtx (types.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl))) type := by
        rw [htoCtx]
        exact Htypes.2
      exact ⟨ih Htypes.1, nofun, Htype⟩
  have HearlierCtx : OnCtx
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
    have HprefixCtx := T.prefixContext H.outVEnvWF.ordered
    have hmotivesReverse : T.motives.reverse =
        (T.motives.drop owner).reverse ++
          (T.motives.take owner).reverse := by
      simp
    have hsplit : (T.params ++ T.motives ++ T.minors).reverse =
        (T.minors.reverse ++ (T.motives.drop owner).reverse) ++
          (T.params ++ T.motives.take owner).reverse := by
      rw [List.reverse_append, List.reverse_append, hmotivesReverse,
        List.reverse_append]
      simp [List.append_assoc]
    rw [hsplit] at HprefixCtx
    have Hsuffix := OnCtx.of_append HprefixCtx
    have hearlierToCtx :
        (abstractForallContext
          (T.params ++ T.motives.take owner) []).toCtx =
          (T.params ++ T.motives.take owner).reverse := by
      simpa [abstractForallContext] using
        htoCtx ((T.params ++ T.motives.take owner).reverse)
    rw [hearlierToCtx]
    exact Hsuffix
  have HearlierVLCtx : VLCtx.WF H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (T.params ++ T.motives.take owner) []) := by
    have Hwf := anonymousWF
      ((T.params ++ T.motives.take owner).reverse)
      (by
        have hearlierToCtx :
            (abstractForallContext
              (T.params ++ T.motives.take owner) []).toCtx =
              (T.params ++ T.motives.take owner).reverse := by
          simpa [abstractForallContext] using
            htoCtx ((T.params ++ T.motives.take owner).reverse)
        rwa [hearlierToCtx] at HearlierCtx)
    simpa [abstractForallContext] using Hwf
  have Htargets := Hgenerated.uniq H.outVEnvWF
    (.refl H.outVEnvWF HearlierVLCtx)
    HparameterWeak'
  have HcanonicalWeak := HparameterCanonical.weakN
    H.outVEnvWF.ordered W.toCtx
  have HcanonicalWeak' : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      (parameterTarget.liftN (T.motives.take owner).length 0)
      (S.canonical.motiveType.liftN
        (T.motives.take owner).length 0) := by
    simpa [abstractForallContext, List.reverse_append, List.map_append,
      List.map_take, List.append_assoc] using HcanonicalWeak
  have Hresult := Htargets.trans H.outVEnvWF
    HearlierCtx
    HcanonicalWeak'
  exact ⟨T, S, hparams, by simpa [source] using Hresult⟩

/-- The aligned recursor is present and well typed in the recursor environment
at its identity universe instantiation.  Rule typing can therefore consume
the independently recovered telescope without appealing to the equation
being constructed. -/
theorem RecursorCheck.recursorTypingAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let recursor := H.entries[owner].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type := by
  let recursor := H.entries[owner].2
  have hmem : recursor ∈ H.entries.map Prod.snd := by
    exact List.mem_map.mpr
      ⟨H.entries[owner], List.getElem_mem howner, rfl⟩
  have hlookup : H.outVEnv.constants recursor.name =
      some recursor.toVConstant := by
    apply VEnv.addConstVals_get H.installed.abstract
    exact hmem
  have hwfBase : recursor.toVConstant.WF
      R.context.venv :=
    H.generated.recursorsWF H.localWF H.bindings H.params recursor hmem
  have hwf : recursor.toVConstant.WF H.outVEnv :=
    hwfBase.mono H.installed.le
  exact VEnv.HasType.const0 hlookup hwf

theorem RecursorCheck.RuleAlignment.recursorTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.RuleAlignment owner howner i hctor) :
    let recursor := H.entries[owner].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type := by
  exact H.recursorTypingAt owner howner

end VerifyInductive
end Lean4Lean
