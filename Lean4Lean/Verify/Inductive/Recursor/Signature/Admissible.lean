import Lean4Lean.Verify.Inductive.Recursor.Signature.FieldDomainsDefEq
import Lean4Lean.Verify.Inductive.Recursor.Signature.Constructors
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorSpine
import Lean4Lean.Verify.Inductive.Recursor.Signature.Families
import Lean4Lean.Verify.Inductive.Recursor.Elimination.Singleton
import Lean4Lean.Verify.Inductive.Constructor.ParameterSyntacticTranslation
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorFields

/-! Admissibility (`Instance.Admissible`) of the universe instance of the recursor
construction's signature.

The universe levels, elimination level and recursor names are fixed by the construction alone.
The singleton case is read off the executable's large-elimination check against the
checked-formation constructor telescope, and moved to the construction's field domains, which
are definitionally equal field by field and have syntactically the same result indices. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Translations of a telescope and of its unannotated form, in contexts that differ only in
binder types, have syntactically equal bodies once the same number of binders is opened,
provided removing annotations leaves the residual unchanged. -/
theorem TrExprS.unannotatedTelescope_body_eq {venv : VEnv} {Us : List Name}
    (Htel : Expr.ForallTelescope raw n residual) :
    Lean4Lean.Expr.consumeForallTypes annOk residual = residual →
    ∀ {Δ₁ Δ₂ : VLCtx} {As Cs : List VExpr} {B D : VExpr},
      TrExprS.IsUniqueCtx Δ₁ Δ₂ →
      TrExprS venv Us Δ₁ raw (VExpr.wrapForalls As B) →
      TrExprS venv Us Δ₂ (Lean4Lean.Expr.consumeForallTypes annOk raw) (VExpr.wrapForalls Cs D) →
      As.length = n → Cs.length = n → B = D := by
  induction Htel with
  | nil body =>
    intro hres Δ₁ Δ₂ As Cs B D hΔ H1 H2 hA hC
    cases As with
    | cons => simp at hA
    | nil =>
    cases Cs with
    | cons => simp at hC
    | nil =>
    rw [hres] at H2
    simpa [VExpr.wrapForalls] using TrExprS.uniqueCtx hΔ H1 H2
  | cons _ ih =>
    intro hres Δ₁ Δ₂ As Cs B D hΔ H1 H2 hA hC
    cases As with
    | nil => simp at hA
    | cons A As =>
    cases Cs with
    | nil => simp at hC
    | cons C Cs =>
    simp only [VExpr.wrapForalls, List.foldr_cons, Lean4Lean.Expr.consumeForallTypes] at H1 H2
    cases H1 with
    | forallE _ _ _ Hbody =>
    cases H2 with
    | forallE _ _ _ Hcbody =>
    exact ih hres (hΔ.cons .vlam) Hbody Hcbody (by simpa using hA) (by simpa using hC)

/-- Removing type annotations changes only binder domains: the result indices of a minor's
constructor (`declConstructorIndices`) are syntactically those of the matching checked-formation
signature constructor. -/
theorem RecursorConstruction.sourceConstructorIndices_eq_header
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    H.declConstructorIndices owner howner localIndex hlocal =
      (R.sourceSignatureConstructor
        ⟨recursorMinorOffset indTypes owner + localIndex,
          H.sourceMinorOffsetBound owner howner localIndex hlocal⟩).indices := by
  have Hraw := H.constructorRawSourceReplay owner howner localIndex hlocal
    (H.sourceMinorTyping owner howner localIndex hlocal)
  have Hcons := (H.sourceConstructorIndices_replay owner howner localIndex hlocal).1
  rw [H.constructorUnannotatedSource owner howner localIndex hlocal
    (H.sourceMinorTyping owner howner localIndex hlocal)] at Hcons
  have Htel := (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fieldTelescope.abstractList
    H.params.fvars
  have hres := (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fieldResidual_not_forall
  have hcons : Lean4Lean.Expr.consumeForallTypes ctorEnv.isTypeAnnotationWrapper
      (((H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fieldResidual).abstractList
        H.params.fvars (0 + (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fields.size)) =
      ((H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fieldResidual).abstractList
        H.params.fvars (0 + (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fields.size) := by
    rw [← Lean4Lean.Expr.abstractList_consumeForallTypes _ _ (0 + _)]
    congr 1
    revert hres
    cases (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal.fieldResidual <;>
      simp [Lean4Lean.Expr.consumeForallTypes, Lean.Expr.isForall]
  obtain ⟨hlen, -⟩ := H.sourceFields_defeq_header owner howner localIndex hlocal
  have hconsLen := H.sourceFields_length owner howner localIndex hlocal
  have hfields := (H.sourceMinorTyping owner howner localIndex hlocal).semantic.traversal_fields
  have hbody := TrExprS.unannotatedTelescope_body_eq Htel hcons .base Hraw Hcons
    (by rw [hfields]; omega) (by rw [hfields]; exact hconsLen)
  have hargs := congrArg (fun e => e.getAppFnArgs.2) hbody
  simp only [InductiveSignature.familyApp, VExpr.getAppFnArgs_mkApps_const] at hargs
  have hstats : stats.params.size = decl.nparams := by
    have hlength := List.Forall₂.length_eq R.statsWF.params
    simpa [VInductDecl.paramVars] using hlength
  have hsig : R.sourceSignature.params.length = decl.nparams := R.sourceSignature_models.nparams
  have hvars := (List.append_inj hargs (by simp [InductiveSignature.vars, hstats, hsig])).2
  exact hvars.symm

open InductiveSignature in
/-- If the executable's large-elimination check accepts a source constructor, then each field of
the matching signature constructor is a proof (its type has sort `Prop`) or occurs as a result
index, over the parameter scope. -/
private theorem SourceConstructorTelescope.singletonFieldsInScope
    (H : SourceConstructorTelescope env Us scope stats decl family source sourceCtor s ctor)
    (Hc : ContextWF c) (hchk : Hc.chk.vlctx = []) (hus : Us = c.lparams)
    (hle : env ≤ Hc.venv) (henv : env.WF)
    (hscope : scope.WF env Us.length)
    (hu : decl.uvars = Us.length)
    (Htrace : LargeEliminationCheck stats c source.type 0 #[])
    (Hspine : Expr.ForallSpine source.type arity) :
    ∀ i (hi : i < (s.fieldTypes ctor).length),
      env.HasType Us.length (((s.fieldTypes ctor).take i).reverse ++ scope.toCtx)
        (s.fieldTypes ctor)[i] (.sort .zero) ∨
      .bvar (ctor.fields.length - 1 - i) ∈ ctor.indices := by
  subst Us
  obtain ⟨tail, tailTarget, sourceDomains, hraw, hprefix, hchecked,
    htail, hcert, hsynthesis, hgenerator⟩ := H
  obtain ⟨rawScope, domains, residual, hrawType, hlength, hrawCtx,
    hcontexts, hshapeCtx, hresidual⟩ := hchecked.rawTranslation henv hscope hraw.type
  have Hclosed := Htrace.singletonClosed Hc hchk Hspine (hraw.type.mono hle)
  rw [hrawType] at Hclosed
  have HrawTail := Hclosed.dropParams
  simp only [List.append_nil, Nat.zero_add, hlength, ← hrawCtx] at HrawTail
  have HrawTail' := HrawTail.of_defeq Hc.checking.tr.wf
    ((hcontexts.wf.toCtx).mono (VEnv.IsType.mono hle))
    ((hresidual.uniq henv hcontexts htail).mono hle)
    (TrExprS.rawShape hshapeCtx.rawShape hresidual htail)
  have Htail' := HrawTail'.defeqCtx Hc.checking.tr.wf.ordered
    (hcontexts.defeqCtx.mono hle)
  have HtailSmall := Htail'.of_mono hle henv Hc.checking.tr.wf hscope.toCtx
    (by simpa [hu] using hcert.choose_spec.isType)
  rw [sourceConstructor_tail_eq hgenerator] at HtailSmall
  intro i hi
  have hlengthFields : (s.fieldTypes ctor).length = ctor.fields.length := by
    simp [fieldTypes]
  have hresult : (s.familyApp ctor.owner (VLevel.params s.uvars)
      (vars s.params.length ctor.fields.length) ctor.indices).forallArity = 0 :=
    VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)
  have Hfield := HtailSmall.fieldAt (Nat.le_refl _) hresult i hi
  rcases Hfield with hp | hx
  · exact .inl hp
  · apply Or.inr
    simp only [familyApp, VExpr.getAppFnArgs_mkApps_const, hlengthFields] at hx
    rcases List.mem_append.mp hx with hparam | hindex
    · simp only [vars, List.mem_map] at hparam
      obtain ⟨j, hj, heq⟩ := hparam
      have heq := VExpr.bvar.inj heq
      omega
    · exact hindex

/-- Field-by-field definitional equality of two telescopes over a common
base yields definitional equality of every prefix context. -/
theorem IsDefEqCtx.ofFieldPrefixes {env : VEnv} {U : Nat} {P xs ys : List VExpr}
    (henv : env.WF) (hP : OnCtx P (env.IsType U)) (hlen : xs.length = ys.length)
    (H : ∀ j (hj : j < xs.length) (hj' : j < ys.length),
      env.IsDefEqU U ((xs.take j).reverse ++ P) xs[j] ys[j] ∧
      env.IsType U ((xs.take j).reverse ++ P) xs[j]) :
    ∀ i, i ≤ xs.length →
      env.IsDefEqCtx U P ((xs.take i).reverse ++ P) ((ys.take i).reverse ++ P) := by
  intro i
  induction i with
  | zero => intro _; simpa using VEnv.IsDefEqCtx.zero
  | succ i ih =>
    intro hi
    have W := ih (by omega)
    obtain ⟨hdefeq, u, htype⟩ := H i (by omega) (by omega)
    have hΓ := W.isType' hP
    rw [List.take_succ_eq_append_getElem (by omega), List.take_succ_eq_append_getElem (by omega)]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    exact .succ W (hdefeq.of_l henv hΓ htype)

/-- The universe instance of the recursor construction for a signature `s`: the recursor's
universe parameters and levels, the elimination level as target, and recursor names `T.rec`.
Only the recursor names depend on `s`. -/
noncomputable def RecursorConstruction.generatedInstance
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (s : InductiveSignature) :
    InductiveSignature.Instance s where
  uvars := (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
  levels := recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  targetLevel := Classical.choose H.elimLevelAdmissible.ofLevel
  recursorName owner := s.families[owner].name.str "rec"

theorem RecursorConstruction.generatedInstance_target
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (s : InductiveSignature) :
    VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some (H.generatedInstance s).targetLevel :=
  Classical.choose_spec H.elimLevelAdmissible.ofLevel

/-- The elimination level of the construction is justified: every source family is never
zero, or the target is `Prop`, or the block has one family with at most one constructor,
accepted by the executable's large-elimination check. -/
theorem RecursorConstruction.elimLevelDecision
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) :
    (∀ family ∈ decl.types, family.resultLevel.IsNeverZero) ∨
    H.elimLevel = .zero ∨
    ∃ ind, indTypes = #[ind] ∧
      (ind.ctors = [] ∨ ∃ ctor, ind.ctors = [ctor] ∧
        LargeEliminationCheck stats
          { c with env := ctorEnv, checkLCtx := {} } ctor.type 0 #[]) := by
  by_cases hzero : H.elimLevel = .zero
  · exact .inr (.inl hzero)
  rcases AddInductive.isLargeEliminator.shape_of_checked
      (AddInductive.getElimLevel.large_of_checked H.elimLevelChecked hzero) with
    hnotzero | ⟨ind, hind, hctors⟩
  · exact .inl fun _ hfamily =>
      R.sourceStatsWF.familyNeverZero hnotzero hfamily
  · refine .inr (.inr ⟨ind, hind, ?_⟩)
    rcases hctors with hnil | ⟨ctor, hctor, hchecked⟩
    · exact .inl hnil
    · exact .inr ⟨ctor, hctor,
        AddInductive.isLargeEliminator.loop.trace hchecked⟩

/-- A singleton source block accepted by the executable's large-elimination check satisfies
the generator's singleton condition (`SingletonElimination`) for any signature with the
construction's parameters, families, field domains and result indices, at every universe
instance. -/
theorem RecursorConstruction.unannotatedSingletonElimination
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {s : InductiveSignature}
    (hparams : s.params = R.parameterScope.toCtx.reverse)
    (hfam : s.families = H.families)
    (hsize : s.constructors.size = decl.ownedConstructors.length)
    (hfields : ∀ owner (howner : owner < H.recInfos.size) localIndex
      (hlocal : localIndex < H.origins.minorTypes[owner]!.size),
      let k := recursorMinorOffset indTypes owner + localIndex
      ∃ hk : k < s.constructors.size,
        s.constructors[k].owner.val = owner ∧
        s.fieldTypes s.constructors[k] = H.declFieldDomains owner howner localIndex hlocal ∧
        s.constructors[k].indices = H.declConstructorIndices owner howner localIndex hlocal)
    (hls : ∀ level ∈ levels, level.WF U)
    (Hsingleton : ∃ ind, indTypes = #[ind] ∧
      (ind.ctors = [] ∨ ∃ ctor, ind.ctors = [ctor] ∧
        LargeEliminationCheck stats { c with env := ctorEnv, checkLCtx := {} }
          ctor.type 0 #[])) :
    s.SingletonElimination R.headerVEnv U levels := by
  obtain ⟨ind, hind, hctors⟩ := Hsingleton
  have hsourceCtorCount := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length R.core
  have hctorCount : decl.ownedConstructors.length = ind.ctors.length := by
    simpa [hind, ownedConstructors] using hsourceCtorCount.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hfam, H.families_size, H.sourceFamilyCount, hind]; rfl
  · rw [hsize, hctorCount]
    rcases hctors with hnil | ⟨ctor, hctor, _⟩ <;> simp_all
  intro ctor hctor i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
  rcases hctors with hnil | ⟨source, hsource, htrace⟩
  · simp [hsize, hctorCount, hnil] at hj
  have hj0 : j = 0 := by
    simp [hsize, hctorCount, hsource] at hj
    exact hj
  subst hj0
  have h0 : 0 < H.recInfos.size := by rw [H.sourceFamilyCount, hind]; simp
  have hl0 : 0 < H.origins.minorTypes[0]!.size := by
    have hsz := (H.origins.minors 0 h0).size_eq
    have hcounts := H.minorCounts 0 h0
    simp [hind, hsource] at hcounts
    omega
  obtain ⟨hk, -, hft0, hidx0⟩ := hfields 0 h0 0 hl0
  have hoff : recursorMinorOffset indTypes 0 + 0 = 0 := by simp [recursorMinorOffset]
  have hc : s.constructors[recursorMinorOffset indTypes 0 + 0]'hk = s.constructors.toList[0]'hj := by
    simp [hoff]
  have hft : s.fieldTypes (s.constructors.toList[0]'hj) = H.declFieldDomains 0 h0 0 hl0 := by
    rw [← hc]; exact hft0
  have hidx : (s.constructors.toList[0]'hj).indices = H.declConstructorIndices 0 h0 0 hl0 := by
    rw [← hc]; exact hidx0
  clear hft0 hidx0 hc hctor
  generalize s.constructors.toList[0]'hj = ctor at hft hidx hi ⊢
  -- The header constructor at the same flattened offset and its singleton fields.
  have hbound := H.sourceMinorOffsetBound 0 h0 0 hl0
  obtain ⟨production, hproduction, hreplay⟩ := R.sourceSignatureConstructor_replay
    ⟨recursorMinorOffset indTypes 0 + 0, hbound⟩
  simp [hind] at hproduction
  have hprod : production = source := by simpa [hsource] using hproduction
  subst production
  have henvSource : sourceEnv.WF := by
    simpa only [R.sourceContextVEnv] using R.sourceContext.checking.tr.wf
  have hheader := Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core henvSource
  have hscope : R.parameterScope.WF R.headerVEnv c.lparams.length := by
    rw [← R.checkedParameterScope]
    exact R.statsWF.parameterEmbedding.scopeWF hheader
  have hspine := R.parameterPrefixes.spines 0 (by simp [hind]) 0 (by simp [hind, hsource])
  simp only [hind, Array.getElem_singleton, hsource, List.getElem_cons_zero] at hspine
  obtain ⟨arity, hspine⟩ := hspine
  have Hheader := SourceConstructorTelescope.singletonFieldsInScope hreplay
    (R.context.withCheckLCtx {} R.context.baseNil) rfl rfl
    (R.installation.constructorLE.trans R.ctorLE) hheader hscope
    R.core.uvars htrace hspine
  -- Field-by-field comparison of the unannotated and header telescopes.
  obtain ⟨hlen, hdef⟩ := H.sourceFields_defeq_header 0 h0 0 hl0
  have hidx' := hidx.trans (H.sourceConstructorIndices_eq_header 0 h0 0 hl0)
  have henv := R.headerCheckingAnnotations.1.wf
  have hP : OnCtx R.parameterScope.toCtx (R.headerVEnv.IsType c.lparams.length) := by
    have h := R.headerAnonymousParameterWF.toCtx
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using h
  have hlenFields : (s.fieldTypes ctor).length =
      ctor.fields.length := by
    simp [InductiveSignature.fieldTypes]
  have hiC : i < (H.declFieldDomains 0 h0 0 hl0).length := by rw [← hft, hlenFields]; exact hi
  have hiH : i < (R.sourceSignature.fieldTypes (R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes 0 + 0, hbound⟩)).length := by omega
  have hfieldEq : s.fieldType i ctor.fields[i] =
      (H.declFieldDomains 0 h0 0 hl0)[i]'hiC := by
    have h : (s.fieldTypes ctor)[i]'(by rw [hlenFields]; exact hi) =
        s.fieldType i ctor.fields[i] := by
      simp [InductiveSignature.fieldTypes]
    rw [← h]
    simp only [hft]
  rcases Hheader i hiH with hp | hx
  · left
    have W := IsDefEqCtx.ofFieldPrefixes henv hP hlen
      (fun j hj hj' => ⟨(hdef j hj hj').1, (hdef j hj hj').2.2⟩) i (by omega)
    have hp' := hp.defeqDFC henv.ordered (W.symm henv.ordered)
    have hc' := VEnv.HasType.defeqU_l henv (W.isType' hP) (hdef i hiC hiH).1.symm hp'
    have hinst := hc'.instL hls
    rw [hfieldEq, hft, hparams]
    simpa only [List.map_append, List.map_reverse, List.reverse_reverse, VExpr.instL,
      VLevel.inst] using hinst
  · right
    rw [hidx']
    have hcount : ctor.fields.length =
        (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes 0 + 0, hbound⟩).fields.length := by
      have h1 : (R.sourceSignature.fieldTypes (R.sourceSignatureConstructor
          ⟨recursorMinorOffset indTypes 0 + 0, hbound⟩)).length =
          (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes 0 + 0, hbound⟩).fields.length := by
        exact (List.length_map _).trans List.length_zipIdx
      rw [← hlenFields, hft]
      omega
    rw [hcount]
    exact hx

/-- The construction's universe instance is admissible, in the header environment, for any
signature with the source universe count, parameters, the construction's families, constructor
count and per-minor field domains and result indices. -/
theorem RecursorConstruction.generatedInstance_admissible
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    {s : InductiveSignature} (huvars : s.uvars = decl.uvars)
    (hparams : s.params = R.parameterScope.toCtx.reverse)
    (hfam : s.families = H.families)
    (hsize : s.constructors.size = decl.ownedConstructors.length)
    (hfields : ∀ owner (howner : owner < H.recInfos.size) localIndex
      (hlocal : localIndex < H.origins.minorTypes[owner]!.size),
      let k := recursorMinorOffset indTypes owner + localIndex
      ∃ hk : k < s.constructors.size,
        s.constructors[k].owner.val = owner ∧
        s.fieldTypes s.constructors[k] = H.declFieldDomains owner howner localIndex hlocal ∧
        s.constructors[k].indices = H.declConstructorIndices owner howner localIndex hlocal) :
    (H.generatedInstance s).Admissible R.headerVEnv := by
  refine {
    levels_length := ?_
    levels_wf := recursorDeclarationAbstractLevels_wf H.elimLevelAdmissible
    target_wf := .of_ofLevel (H.generatedInstance_target s)
    elimination := ?_ }
  · change (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible).length = s.uvars
    rw [recursorDeclarationAbstractLevels_length, huvars, R.core.uvars]
  · rcases H.elimLevelDecision with hnonzero | hsmall | hsingleton
    · left
      intro family hfamily
      rw [hfam] at hfamily
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hfamily
      have hi' : i < H.recInfos.size := by simpa using hi
      have hlevel := H.families_level ⟨i, hi'⟩
      simp only [Array.getElem_toList] at hlevel ⊢
      rw [hlevel]
      exact (hnonzero _ (List.getElem_mem _)).inst
    · apply Or.inr; apply Or.inl
      have ht := H.generatedInstance_target s
      rw [hsmall] at ht
      have : (H.generatedInstance s).targetLevel = .zero := Option.some.inj ht.symm
      rw [this]
      rfl
    · by_cases hz : H.elimLevel = .zero
      · apply Or.inr; apply Or.inl
        have ht := H.generatedInstance_target s
        rw [hz] at ht
        have : (H.generatedInstance s).targetLevel = .zero := Option.some.inj ht.symm
        rw [this]
        rfl
      · obtain ⟨htarget, hfree⟩ := recursorDeclarationAbstractLevels_freeTarget
          H.elimLevelAdmissible hz (H.generatedInstance_target s)
        exact .inr (.inr ⟨H.unannotatedSingletonElimination hparams hfam hsize hfields
          (recursorDeclarationAbstractLevels_wf H.elimLevelAdmissible) hsingleton,
          0, htarget, hfree⟩)

end Lean4Lean.VerifyInductive
