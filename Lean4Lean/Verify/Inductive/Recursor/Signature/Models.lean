import Lean4Lean.Verify.Inductive.Recursor.Signature.FieldDomainsDefEq
import Lean4Lean.Verify.Inductive.Recursor.Signature.Constructors
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorSpine
import Lean4Lean.Verify.Inductive.Recursor.Signature.Families
import Lean4Lean.Verify.Inductive.Recursor.Signature.MotiveGroup
import Lean4Lean.Verify.Inductive.Constructor.SourceSignature

/-! Source models for signatures built from the data of the recursor construction: a signature
with the construction's parameters, families, field domains and result indices
(`RecursorConstruction.SignatureSpec`) models the source declaration (`Models`). -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Changing only the domains of a closed telescope along a context
conversion preserves the telescope up to definitional equality. -/
theorem VExpr.wrapForalls_domains_defeqCtx {env : VEnv} {U : Nat} (henv : env.WF) :
    ∀ {P Q : List VExpr} {Y : VExpr},
      VEnv.IsDefEqCtx env U [] P.reverse Q.reverse →
      env.IsType U Q.reverse Y →
      env.IsDefEqU U [] (VExpr.wrapForalls P Y) (VExpr.wrapForalls Q Y) := by
  suffices H : ∀ L : List VExpr, ∀ {P Q : List VExpr} {Y : VExpr}, P.reverse = L →
      VEnv.IsDefEqCtx env U [] P.reverse Q.reverse →
      env.IsType U Q.reverse Y →
      env.IsDefEqU U [] (VExpr.wrapForalls P Y) (VExpr.wrapForalls Q Y) from
    fun {P Q Y} hPQ hY => H P.reverse (P := P) (Q := Q) (Y := Y) rfl hPQ hY
  intro L
  induction L with
  | nil =>
    intro P Q Y hP hPQ hY
    have hP' : P = [] := by simpa using hP
    subst hP'
    have hlen := hPQ.length_eq
    have hQ : Q = [] := by simpa using hlen.symm
    subst hQ
    obtain ⟨u, h⟩ := hY
    exact ⟨_, h⟩
  | cons A L' ih =>
    intro P Q Y hP hPQ hY
    have hP' : P = L'.reverse ++ [A] := by
      rw [← List.reverse_reverse P, hP]; simp
    subst hP'
    rcases List.eq_nil_or_concat Q with hQ | ⟨Q', B, hQ⟩
    · subst hQ
      have hlen := hPQ.length_eq
      simp at hlen
    rw [List.concat_eq_append] at hQ
    subst hQ
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.reverse_reverse] at hPQ hY
    cases hPQ with
    | succ hctx hAB =>
    have hAB' := hAB.defeqDFC henv.ordered hctx
    have hQctx : OnCtx Q'.reverse (env.IsType U) := (hctx.symm henv.ordered).isType
    obtain ⟨v, hYB⟩ := hY
    have hYA : env.HasType U (A :: Q'.reverse) Y (.sort v) :=
      hYB.defeqDFC henv.ordered (.succ .zero hAB'.symm)
    have hforallA : env.IsType U Q'.reverse (.forallE A Y) :=
      ⟨_, .forallEDF hAB'.hasType.1 hYA⟩
    have hfirst := ih (P := L'.reverse) (by simp) (by simpa using hctx) hforallA
    obtain ⟨level, hsecond⟩ := VExpr.wrapForalls_defeq (domains := Q') (Γ := [])
      (by simpa using hQctx)
      (by simpa using (VEnv.IsDefEq.forallEDF hAB' hYA))
    simp only [VExpr.wrapForalls_append]
    exact hfirst.trans henv trivial ⟨_, by simpa [VExpr.wrapForalls] using hsecond⟩

/-- Closing definitionally equal bodies over definitionally equal telescopes gives
definitionally equal types. -/
theorem VExpr.wrapForalls_defeqCtx {env : VEnv} {U : Nat} (henv : env.WF)
    {P Q : List VExpr} {X Y : VExpr}
    (hPQ : VEnv.IsDefEqCtx env U [] P.reverse Q.reverse)
    (hY : env.IsType U Q.reverse Y)
    (hXY : env.IsDefEqU U Q.reverse X Y) :
    env.IsDefEqU U [] (VExpr.wrapForalls P X) (VExpr.wrapForalls Q Y) := by
  have hQP := hPQ.symm henv.ordered
  have hXY' := hXY.defeqDFC henv.ordered hQP
  have hY' := hY.defeqDFC henv.ordered hQP
  obtain ⟨u, hYty⟩ := hY'
  have hXYsort := hXY'.of_r henv hPQ.isType hYty
  obtain ⟨level, hbody⟩ := VExpr.wrapForalls_defeq (domains := P) (Γ := [])
    (by simpa using hPQ.isType) (by simpa using hXYsort)
  exact VEnv.IsDefEqU.trans henv trivial ⟨_, hbody⟩
    (VExpr.wrapForalls_domains_defeqCtx henv hPQ hY)

/-- Field-by-field definitional equalities, each stated in the right-hand prefix scope, extend
a context conversion of the base to every prefix. -/
theorem VEnv.IsDefEqCtx.prefixes {env : VEnv} {U : Nat} (henv : env.WF)
    {A C Γ₁ Γ₂ : List VExpr} (hlen : C.length = A.length)
    (hbase : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂)
    (hfield : ∀ j (hj : j < C.length) (hj' : j < A.length),
      env.IsDefEqU U ((C.take j).reverse ++ Γ₂) C[j] A[j] ∧
      env.IsType U ((C.take j).reverse ++ Γ₂) C[j]) :
    ∀ i, i ≤ C.length →
      VEnv.IsDefEqCtx env U [] ((A.take i).reverse ++ Γ₁) ((C.take i).reverse ++ Γ₂) := by
  intro i
  induction i with
  | zero => intro _; simpa using hbase
  | succ i ih =>
    intro hi
    have IH := ih (by omega)
    have hiC : i < C.length := by omega
    have hiA : i < A.length := by omega
    obtain ⟨hdefeq, u, hC⟩ := hfield i hiC hiA
    have hrev := IH.symm henv.ordered
    have hCA := hdefeq.of_l henv hrev.isType hC
    have hAC := hCA.symm.defeqDFC henv.ordered hrev
    have eA : A.take (i + 1) = A.take i ++ [A[i]] := (List.take_append_getElem hiA).symm
    have eC : C.take (i + 1) = C.take i ++ [C[i]] := (List.take_append_getElem hiC).symm
    rw [eA, eC]
    simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons_append] using VEnv.IsDefEqCtx.succ IH hAC

theorem InductiveSignature.fieldTypes_getElem (s : InductiveSignature)
    (ctor : InductiveSignature.Constructor s.families.size) (i : Nat)
    (hi : i < (s.fieldTypes ctor).length) (hi' : i < ctor.fields.length) :
    (s.fieldTypes ctor)[i] = s.fieldType i ctor.fields[i] := by
  simp [InductiveSignature.fieldTypes]

theorem InductiveSignature.fieldTypes_length (s : InductiveSignature)
    (ctor : InductiveSignature.Constructor s.families.size) :
    (s.fieldTypes ctor).length = ctor.fields.length := by
  simp [InductiveSignature.fieldTypes]

theorem recursorMinorOffset_size (indTypes : Array InductiveType) :
    recursorMinorOffset indTypes indTypes.size =
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
  unfold recursorMinorOffset
  rw [List.take_of_length_le (by simp)]

/-- Every position below a prefix offset lies in exactly one earlier row. -/
theorem recursorMinorOffset_decompose (indTypes : Array InductiveType) :
    ∀ n, n ≤ indTypes.size → ∀ k, k < recursorMinorOffset indTypes n →
      ∃ owner, owner < n ∧ ∃ localIndex, localIndex < indTypes[owner]!.ctors.length ∧
        k = recursorMinorOffset indTypes owner + localIndex := by
  intro n
  induction n with
  | zero => intro _ k hk; simp [recursorMinorOffset] at hk
  | succ n ih =>
    intro hn k hk
    rw [recursorMinorOffset_step indTypes n (by omega)] at hk
    by_cases hlt : k < recursorMinorOffset indTypes n
    · obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ := ih (by omega) k hlt
      exact ⟨owner, by omega, localIndex, hlocal, rfl⟩
    · exact ⟨n, by omega, k - recursorMinorOffset indTypes n, by omega, by omega⟩

theorem recursorMinorOffset_unique (indTypes : Array InductiveType)
    {owner owner' localIndex localIndex' : Nat}
    (howner : owner < indTypes.size) (howner' : owner' < indTypes.size)
    (hlocal : localIndex < indTypes[owner]!.ctors.length)
    (hlocal' : localIndex' < indTypes[owner']!.ctors.length)
    (heq : recursorMinorOffset indTypes owner + localIndex =
      recursorMinorOffset indTypes owner' + localIndex') :
    owner = owner' ∧ localIndex = localIndex' := by
  have key : ∀ a b, a < b → b < indTypes.size → ∀ i, i < indTypes[a]!.ctors.length →
      recursorMinorOffset indTypes a + i < recursorMinorOffset indTypes b := by
    intro a b hab hb i hi
    have hstep := recursorMinorOffset_step indTypes a (by omega)
    have hmono := recursorMinorOffset_mono indTypes (a + 1) b hab (by omega)
    omega
  rcases Nat.lt_trichotomy owner owner' with h | h | h
  · have := key owner owner' h howner' localIndex hlocal
    omega
  · subst h
    exact ⟨rfl, by omega⟩
  · have := key owner' owner h howner localIndex' hlocal'
    omega

/-- Each family has as many minors as constructors. -/
theorem RecursorConstruction.minorTypes_size
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    H.origins.minorTypes[owner]!.size = indTypes[owner]!.ctors.length := by
  have hsize := (H.origins.minors owner howner).size_eq
  have hcounts := H.minorCounts owner howner
  omega

/-- The total number of owned constructors is the executable's minor offset after the last
family. -/
theorem RecursorConstruction.ownedConstructors_length_offset
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (_H : RecursorConstruction R) :
    decl.ownedConstructors.length = recursorMinorOffset indTypes indTypes.size := by
  have htotal := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length R.core
  rw [recursorMinorOffset_size]
  simp only [ownedConstructors, List.length_flatMap, List.length_map] at htotal
  rw [List.length_flatMap]
  omega

/-- Every flattened constructor position is the minor offset of some family plus a local index
among that family's minors (unique by `flatMinorIndex_unique`). -/
theorem RecursorConstruction.flatMinorIndex
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (k : Nat) (hk : k < decl.ownedConstructors.length) :
    ∃ owner, ∃ _howner : owner < H.recInfos.size,
      ∃ localIndex, ∃ _hlocal : localIndex < H.origins.minorTypes[owner]!.size,
        k = recursorMinorOffset indTypes owner + localIndex := by
  rw [H.ownedConstructors_length_offset] at hk
  obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ :=
    recursorMinorOffset_decompose indTypes indTypes.size (Nat.le_refl _) k hk
  have howner' : owner < H.recInfos.size := by rw [H.sourceFamilyCount]; exact howner
  exact ⟨owner, howner', localIndex, by rw [H.minorTypes_size owner howner']; exact hlocal, rfl⟩

theorem RecursorConstruction.flatMinorIndex_unique
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    {owner owner' localIndex localIndex' : Nat}
    (howner : owner < H.recInfos.size) (howner' : owner' < H.recInfos.size)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hlocal' : localIndex' < H.origins.minorTypes[owner']!.size)
    (heq : recursorMinorOffset indTypes owner + localIndex =
      recursorMinorOffset indTypes owner' + localIndex') :
    owner = owner' ∧ localIndex = localIndex' :=
  recursorMinorOffset_unique indTypes (by rw [← H.sourceFamilyCount]; exact howner)
    (by rw [← H.sourceFamilyCount]; exact howner')
    (by rw [← H.minorTypes_size owner howner]; exact hlocal)
    (by rw [← H.minorTypes_size owner' howner']; exact hlocal') heq

/-- `sourceModelsOfTables` with the per-field obligation reduced to the classified
positivity clause of `Models`. -/
theorem sourceModelsOfTablesPositive {s : InductiveSignature} {decl : VInductDecl}
    (Hsource : decl.SourceWF env)
    (hadd : env.addConstVals decl.typeConstants = some envTypes)
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (Hfamilies : List.Forall₂ (fun f src =>
      f.name = src.name ∧ f.indices.length = src.numIndices ∧
      f.resultLevel = src.resultLevel)
      s.families.toList decl.types)
    (Hctors : List.Forall₂ (fun ctor pair =>
      s.families[ctor.owner].name = pair.1.name ∧ ctor.name = pair.2.name ∧
      envTypes.IsDefEqU decl.uvars [] (s.constructorType ctor) pair.2.type)
      s.constructors.toList decl.ownedConstructors)
    (Hpositive : s.isUnsafe = true ∨
      ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
        ∃ normalized,
          envTypes.IsDefEqU decl.uvars (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
            (s.fieldType i ctor.fields[i]) normalized ∧
          decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) i ctor.fields[i].isRecursive
            normalized)
    (Harity : ∀ ctor ∈ s.constructors.toList,
      ctor.indices.length = s.families[ctor.owner].indices.length) :
    s.Models env decl := by
  have hnames : s.families.toList.map (·.name) = decl.types.map (·.name) := by
    have hr := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) Hfamilies
    clear Hfamilies Hctors Hpositive Hsource
    generalize s.families.toList = left at hr ⊢
    generalize decl.types = right at hr ⊢
    induction hr with
    | nil => rfl
    | cons h _ ih => simp [h, ih]
  have hfamilyNames := decl.typeNames_nodup Hsource.2.1
  let C : VConstVal → VConstVal → Prop := fun normalized source =>
    normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
      envTypes.IsDefEqU decl.uvars [] normalized.type source.type
  have hctorFamilies (owner : Fin s.families.size) {family : VInductiveType}
      (hf : family ∈ decl.types) (hn : s.families[owner].name = family.name) :
      List.Forall₂ C (s.declarationFamily owner).ctors family.ctors := by
    apply Lean4Lean.List.Forall₂.imp (fun normalized source hc => ?_)
      (Lean4Lean.List.Forall₂.and_mem
        (InductiveSignature.constructor_model_in_family (R := fun ctor source => ctor.name = source.name ∧
          envTypes.IsDefEqU decl.uvars [] (s.constructorType ctor) source.type)
          hnames hfamilyNames Hctors owner hf hn))
    obtain ⟨⟨ctor, rfl, hname, htype⟩, _, hsourceMem⟩ := hc
    exact ⟨hname, huvars.trans (Hsource.2.2.2.1 source
      (List.mem_flatMap.mpr ⟨family, hf, hsourceMem⟩)).symm, htype⟩
  have hfull : List.Forall₂ (fun normalized source : VInductiveType =>
      normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
      normalized.numIndices = source.numIndices ∧
      normalized.resultLevel ≈ source.resultLevel ∧
      List.Forall₂ C normalized.ctors source.ctors) s.declaration.types decl.types := by
    apply List.forall₂_of_getElem (by
      simpa [InductiveSignature.declaration] using Lean4Lean.List.Forall₂.length_eq Hfamilies)
    intro i hi hi'
    have hsize : i < s.families.size := by simpa [InductiveSignature.declaration] using hi
    let owner : Fin s.families.size := ⟨i, hsize⟩
    have hget := List.forall₂_getElem Hfamilies i (by simpa using hsize) hi'
    have he : s.declaration.types[i] = s.declarationFamily owner := by
      simp [InductiveSignature.declaration, InductiveSignature.declarationFamily, owner]
    rw [he]
    refine ⟨hget.1, huvars.trans (Hsource.2.2.1 _ (List.getElem_mem hi')).symm,
      hget.2.1, ?_, hctorFamilies owner (List.getElem_mem hi') hget.1⟩
    exact hget.2.2 ▸ rfl
  refine ⟨huvars, hparams, hsafety, ?_, ⟨envTypes, hadd, ?_⟩, ?_, Harity⟩
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        InductiveSignature.ctorNames_eq_of_forall₂ h.2.2.2.2 (fun _ _ hc => hc.1)⟩) hfull
  · change List.Forall₂ C (s.declaration.types.flatMap (·.ctors)) (decl.types.flatMap (·.ctors))
    clear Hfamilies Hctors Hpositive hnames hfamilyNames hctorFamilies Hsource
    generalize s.declaration.types = left at hfull ⊢
    generalize decl.types = right at hfull ⊢
    induction hfull with
    | nil => exact .nil
    | cons h _ ih => exact h.2.2.2.2.append' ih
  · rcases Hpositive with hunsafe | Hpositive
    · exact Or.inl hunsafe
    · exact Or.inr ⟨envTypes, hadd, Hpositive⟩

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- A signature over the data of the recursor construction: the source universes, parameter
scope and safety, the construction's families, and one constructor per minor whose field types
are the minor's field domains (`declFieldDomains`) and whose indices are its result indices
(`declConstructorIndices`). The classification of its fields is unconstrained here. -/
structure RecursorConstruction.SignatureSpec
    (H : RecursorConstruction R) (s : InductiveSignature) : Prop where
  uvars : s.uvars = decl.uvars
  params : s.params = R.parameterScope.toCtx.reverse
  families : s.families = H.families
  safety : s.isUnsafe = decl.isUnsafe
  size : s.constructors.size = decl.ownedConstructors.length
  constructor : ∀ owner (howner : owner < H.recInfos.size) localIndex
      (hlocal : localIndex < H.origins.minorTypes[owner]!.size),
    let k := recursorMinorOffset indTypes owner + localIndex
    ∃ hk : k < s.constructors.size,
      s.constructors[k].name = (H.origins.minorShapes owner howner localIndex hlocal).constructor.name ∧
      s.constructors[k].owner.val = owner ∧
      s.fieldTypes s.constructors[k] = H.declFieldDomains owner howner localIndex hlocal ∧
      s.constructors[k].indices = H.declConstructorIndices owner howner localIndex hlocal
  /-- For a safe declaration, the fields marked recursive are those the constructor phase's
  positivity check classified as recursive. -/
  classified : decl.isUnsafe ≠ true → ∀ owner (_howner : owner < H.recInfos.size) localIndex
      (_hlocal : localIndex < H.origins.minorTypes[owner]!.size)
      (hk : recursorMinorOffset indTypes owner + localIndex < s.constructors.size),
    s.constructors[recursorMinorOffset indTypes owner + localIndex].fields.map
      InductiveSignature.Field.isRecursive = R.classes[owner]![localIndex]!

theorem RecursorConstruction.SignatureSpec.family_getElem
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s) (i : Nat) (hi : i < s.families.size) :
    s.families[i] = H.families[i]'(by rw [← D.families]; exact hi) := by
  simp only [D.families]

theorem RecursorConstruction.SignatureSpec.family_name
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s) (i : Fin s.families.size) (owner : Nat)
    (howner : owner < H.recInfos.size) (heq : i.val = owner) :
    s.families[i].name = (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name := by
  subst heq
  rw [Fin.getElem_fin, D.family_getElem]
  exact H.families_name ⟨i.val, howner⟩

theorem RecursorConstruction.SignatureSpec.family_indices
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s) (i : Fin s.families.size) (owner : Nat)
    (howner : owner < H.recInfos.size) (heq : i.val = owner) :
    s.families[i].indices = H.declIndexDomains ⟨owner, howner⟩ := by
  subst heq
  rw [Fin.getElem_fin, D.family_getElem]
  exact H.families_indices ⟨i.val, howner⟩

/-- The closed type of each constructor of such a signature is definitionally equal, in the
header environment, to the type of the source constructor at the same flattened position. -/
theorem RecursorConstruction.SignatureSpec.constructorType_defeq
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hk : recursorMinorOffset indTypes owner + localIndex < s.constructors.size) :
    R.headerVEnv.IsDefEqU decl.uvars []
      (s.constructorType s.constructors[recursorMinorOffset indTypes owner + localIndex])
      (decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex]'(
        H.sourceMinorOffsetBound owner howner localIndex hlocal)).2.type := by
  obtain ⟨_, _, hown, hfields, hidx⟩ := D.constructor owner howner localIndex hlocal
  have bound := H.sourceMinorOffsetBound owner howner localIndex hlocal
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem bound))
  have hhdrType : R.headerVEnv.IsDefEqU decl.uvars []
      (R.sourceSignature.constructorType (R.sourceSignatureConstructor
        ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩))
      (decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex]'bound).2.type := by
    have ht : R.headerVEnv.IsDefEqU decl.uvars []
        (R.sourceSignatureHeader.constructorType (R.sourceSignatureConstructor
          ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩))
        (decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex]'bound).2.type :=
      hmodel.2.2.1
    simpa only [RecursorInput.sourceSignature_constructorType] using ht
  have hdefeq := H.sourceConstructorDefEq owner howner localIndex hlocal
  have hreplay := (H.sourceConstructorIndices_replay owner howner localIndex hlocal).2.1
  have henv := R.headerCheckingAnnotations.1.wf
  have hctx : R.headerVEnv.IsDefEqCtx c.lparams.length [] R.params.reverse R.parameterScope.toCtx := by
    have h := (R.sourceParameterContext).mono (VEnv.addConstVals_le R.core.typesAdded)
    rwa [R.core.uvars] at h
  have hmain := VExpr.wrapForalls_defeqCtx henv (P := R.params)
    (Q := R.parameterScope.toCtx.reverse)
    (by simpa using hctx) (by simpa using hreplay) (by simpa using hdefeq)
  have hlhs : s.constructorType s.constructors[recursorMinorOffset indTypes owner + localIndex] =
      VExpr.wrapForalls R.parameterScope.toCtx.reverse
        (VExpr.wrapForalls (H.declFieldDomains owner howner localIndex hlocal)
          (VExpr.mkApps
            (.const (decl.types[owner]'(by rw [← H.cardinality.records]; exact howner)).name
              (VLevel.params decl.uvars))
            (InductiveSignature.vars stats.params.size
                (H.origins.minorShapes owner howner localIndex hlocal).fields.size ++
              H.declConstructorIndices owner howner localIndex hlocal))) := by
    have hlen : s.constructors[recursorMinorOffset indTypes owner + localIndex].fields.length =
        (H.origins.minorShapes owner howner localIndex hlocal).fields.size := by
      rw [← InductiveSignature.fieldTypes_length, hfields, H.sourceFields_length]
    unfold InductiveSignature.constructorType InductiveSignature.familyApp
    rw [VExpr.wrapForalls_append, D.params, hfields, hidx, D.uvars, hlen,
      D.family_name _ owner howner hown, List.length_reverse, H.sourceParameterCount]
  have hrhs : R.sourceSignature.constructorType (R.sourceSignatureConstructor
        ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩) =
      VExpr.wrapForalls R.params
        (VExpr.wrapForalls (R.sourceSignature.fieldTypes (R.sourceSignatureConstructor
          ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩))
        (R.sourceSignature.familyApp (R.sourceSignatureConstructor
          ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩).owner
          (VLevel.params R.sourceSignature.uvars)
          (InductiveSignature.vars R.sourceSignature.params.length
            (R.sourceSignatureConstructor
              ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩).fields.length)
          (R.sourceSignatureConstructor
              ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩).indices)) := by
    unfold InductiveSignature.constructorType
    rw [VExpr.wrapForalls_append]
    congr 1
    exact R.sourceSignatureHeader_params
  rw [hlhs]
  rw [hrhs] at hhdrType
  rw [← R.core.uvars] at hmain
  exact hmain.symm.trans henv trivial hhdrType

/-- For a safe declaration, the source signature classifies the fields of each constructor as
the positivity check did. -/
theorem RecursorConstruction.sourceClasses
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hsafe : decl.isUnsafe ≠ true) :
    (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex,
        H.sourceMinorOffsetBound owner howner localIndex hlocal⟩).fields.map
      InductiveSignature.Field.isRecursive = R.classes[owner]![localIndex]! := by
  have bound := H.sourceMinorOffsetBound owner howner localIndex hlocal
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem bound))
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  have habstractOwner : owner < decl.types.length := by
    rw [← H.cardinality.records]; exact howner
  have hctor : localIndex < indTypes[owner]!.ctors.length := by
    rw [← H.minorTypes_size owner howner]; exact hlocal
  have habstractCtor : localIndex < (decl.types[owner]'habstractOwner).ctors.length := by
    have hownerTr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
      owner (by simpa using hsourceOwner) habstractOwner
    simp only [Array.getElem_toList] at hownerTr
    have hlength := Lean4Lean.List.Forall₂.length_eq hownerTr.ctors
    have hbang : indTypes[owner]! = indTypes[owner] := by simp [hsourceOwner]
    rw [hbang] at hctor
    omega
  have hpair := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructorAtMinorOffset
    R.core owner localIndex hsourceOwner hctor habstractOwner habstractCtor bound
  exact (hmodel.2.2.2.1 owner habstractOwner localIndex habstractCtor hpair).resolve_left
    hsafe

/-- For a safe declaration, every field of such a signature is, in its own prefix scope,
definitionally equal to a strictly positive normal form: the checked formation's normal form
for the same field, in the branch its classification names. -/
theorem RecursorConstruction.SignatureSpec.fieldPositive
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hk : recursorMinorOffset indTypes owner + localIndex < s.constructors.size)
    (hsafe : decl.isUnsafe ≠ true)
    (i : Nat) (hi : i < (s.constructors[recursorMinorOffset indTypes owner + localIndex]).fields.length) :
    ∃ normalized,
      R.headerVEnv.IsDefEqU decl.uvars
        (((s.fieldTypes s.constructors[recursorMinorOffset indTypes owner + localIndex]).take i).reverse ++
          s.params.reverse)
        (s.fieldType i (s.constructors[recursorMinorOffset indTypes owner + localIndex]).fields[i])
        normalized ∧
      decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) i
        (s.constructors[recursorMinorOffset indTypes owner + localIndex]).fields[i].isRecursive
        normalized := by
  have hgenClasses := D.classified hsafe owner howner localIndex hlocal hk
  have hsrcClasses := H.sourceClasses owner howner localIndex hlocal hsafe
  obtain ⟨_, _, _, hfields, _⟩ := D.constructor owner howner localIndex hlocal
  have bound := H.sourceMinorOffsetBound owner howner localIndex hlocal
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem bound))
  have HD := H.sourceFields_defeq_header owner howner localIndex hlocal
  simp only at HD
  generalize hhdr : R.sourceSignatureConstructor
    ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩ = hdr at HD
  have hfm : ∀ k (hk : k < hdr.fields.length),
      SignatureFieldModel R.headerVEnv decl R.sourceSignatureHeader
        (((R.sourceSignatureHeader.fieldTypes hdr).take k).reverse ++
          R.sourceSignatureHeader.params.reverse) k hdr.fields[k] := by
    rw [← hhdr]
    exact hmodel.2.2.2.2.1
  have hconsLen : (H.declFieldDomains owner howner localIndex hlocal).length =
      (s.constructors[recursorMinorOffset indTypes owner + localIndex]).fields.length := by
    rw [← hfields, InductiveSignature.fieldTypes_length]
  have hhdrLen : (R.sourceSignature.fieldTypes hdr).length = hdr.fields.length :=
    InductiveSignature.fieldTypes_length _ _
  have hiC : i < (H.declFieldDomains owner howner localIndex hlocal).length := by omega
  have hiA : i < (R.sourceSignature.fieldTypes hdr).length := by omega
  have hiF : i < hdr.fields.length := by omega
  obtain ⟨normalized, hN, hshape⟩ := (hfm i hiF).2.resolve_left (by
    change decl.isUnsafe ≠ true
    exact hsafe)
  have hfieldEq : R.sourceSignatureHeader.fieldType i hdr.fields[i] =
      (R.sourceSignature.fieldTypes hdr)[i] := by
    rw [InductiveSignature.fieldTypes_getElem _ _ i hiA hiF]
    exact (R.sourceSignature_fieldType _).symm
  have hhdrFT : R.sourceSignatureHeader.fieldTypes hdr = R.sourceSignature.fieldTypes hdr :=
    (R.sourceSignature_fieldTypes hdr).symm
  rw [hfieldEq, hhdrFT, R.sourceSignatureHeader_params] at hN
  have henv := R.headerCheckingAnnotations.1.wf
  have hctx : R.headerVEnv.IsDefEqCtx c.lparams.length [] R.params.reverse R.parameterScope.toCtx := by
    have h := (R.sourceParameterContext).mono (VEnv.addConstVals_le R.core.typesAdded)
    rwa [R.core.uvars] at h
  have hctxI := VEnv.IsDefEqCtx.prefixes henv HD.1 hctx
    (fun j hj hj' => ⟨(HD.2 j hj hj').1, (HD.2 j hj hj').2.2⟩) i (by omega)
  rw [R.core.uvars] at hN
  have hN' := hN.defeqDFC henv.ordered hctxI
  have hcd := (HD.2 i hiC hiA).1
  have hres := hcd.trans henv (hctxI.symm henv.ordered).isType hN'
  have hclass : hdr.fields[i].isRecursive =
      (s.constructors[recursorMinorOffset indTypes owner + localIndex]).fields[i].isRecursive := by
    rw [hhdr] at hsrcClasses
    have h1 := congrArg (fun l : List Bool => l[i]?) (hsrcClasses.trans hgenClasses.symm)
    simpa [List.getElem?_map, hiF, hi] using h1
  rw [hclass] at hshape
  refine ⟨normalized, ?_, hshape⟩
  have hget : s.fieldType i (s.constructors[recursorMinorOffset indTypes owner + localIndex]).fields[i] =
      (H.declFieldDomains owner howner localIndex hlocal)[i] := by
    rw [← InductiveSignature.fieldTypes_getElem _ _ i
      (by rw [InductiveSignature.fieldTypes_length]; exact hi) hi]
    simp only [hfields]
  rw [hget, hfields, D.params, List.reverse_reverse, R.core.uvars]
  exact hres

/-- The constructor of such a signature at a flattened position has the family name and
constructor name of the source constructor at that position. -/
theorem RecursorConstruction.SignatureSpec.constructorNames
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hk : recursorMinorOffset indTypes owner + localIndex < s.constructors.size) :
    s.families[(s.constructors[recursorMinorOffset indTypes owner + localIndex]).owner].name =
        (decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex]'(
          H.sourceMinorOffsetBound owner howner localIndex hlocal)).1.name ∧
      (s.constructors[recursorMinorOffset indTypes owner + localIndex]).name =
        (decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex]'(
          H.sourceMinorOffsetBound owner howner localIndex hlocal)).2.name := by
  obtain ⟨_, hname, hown, _, _⟩ := D.constructor owner howner localIndex hlocal
  have bound := H.sourceMinorOffsetBound owner howner localIndex hlocal
  have hmodel := Classical.choose_spec
    (R.sourceSignatureHeader_ownedConstructor _ (List.getElem_mem bound))
  obtain ⟨_, _, hhdrOwner, hhdrName, _⟩ := H.minorSourceReplay owner howner
    (by rwa [← H.sourceFamilyCount]) localIndex hlocal bound
  have hdeclOwner : owner < decl.types.length := by rw [← H.cardinality.records]; exact howner
  refine ⟨?_, ?_⟩
  · rw [D.family_name _ owner howner hown]
    let hdr := R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, bound⟩
    have hm : R.sourceSignatureHeader.families[hdr.owner].name =
        (decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex]'bound).1.name :=
      hmodel.1
    have hheader : owner < R.sourceSignatureHeader.families.size := by
      have := hdr.owner.isLt
      have h' : hdr.owner.val = owner := hhdrOwner
      omega
    have hfamily := List.forall₂_getElem R.sourceSignatureHeader_families owner
      (by simpa using hheader) hdeclOwner
    have hfin : hdr.owner = ⟨owner, hheader⟩ := Fin.ext hhdrOwner
    have hm' := (congrArg (fun j : Fin R.sourceSignatureHeader.families.size =>
      R.sourceSignatureHeader.families[j].name) hfin).symm.trans hm
    have hf1 : R.sourceSignatureHeader.families[owner].name =
        (decl.types[owner]'hdeclOwner).name := by
      simpa only [Array.getElem_toList] using hfamily.1
    exact hf1.symm.trans (by simpa only [Fin.getElem_fin] using hm')
  · exact hname.trans (hhdrName.symm.trans (R.sourceSignatureConstructor_name _))

/-- A signature over the data of the recursor construction models the source declaration. -/
theorem RecursorConstruction.SignatureSpec.models
    {H : RecursorConstruction R} {s : InductiveSignature}
    (D : H.SignatureSpec s) :
    s.Models sourceEnv decl := by
  have hparams : s.params.length = decl.nparams := by
    rw [D.params, List.length_reverse, H.sourceParameterCount, H.cardinality.params]
  have hfamSize : s.families.size = H.recInfos.size := by
    rw [D.families, H.families_size]
  have Harity : ∀ ctor ∈ s.constructors.toList,
      ctor.indices.length = s.families[ctor.owner].indices.length := by
    intro ctor hctor
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hk' : k < decl.ownedConstructors.length := by rw [← D.size]; simpa using hk
    obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ := H.flatMinorIndex k hk'
    obtain ⟨hk2, _, hown, _, hidx⟩ := D.constructor owner howner localIndex hlocal
    simp only [Array.getElem_toList]
    rw [hidx, H.sourceConstructorIndices_length, D.family_indices _ owner howner hown]
  have Hctors : List.Forall₂ (fun ctor pair =>
      s.families[ctor.owner].name = pair.1.name ∧ ctor.name = pair.2.name ∧
      R.headerVEnv.IsDefEqU decl.uvars [] (s.constructorType ctor) pair.2.type)
      s.constructors.toList decl.ownedConstructors := by
    apply List.forall₂_of_getElem (by simpa using D.size)
    intro k hk hk'
    obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ := H.flatMinorIndex k hk'
    have hk2 : recursorMinorOffset indTypes owner + localIndex < s.constructors.size := by
      simpa using hk
    simp only [Array.getElem_toList]
    obtain ⟨h1, h2⟩ := D.constructorNames owner howner localIndex hlocal hk2
    exact ⟨h1, h2, D.constructorType_defeq owner howner localIndex hlocal hk2⟩
  have Hpositive : s.isUnsafe = true ∨
      ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
        ∃ normalized,
          R.headerVEnv.IsDefEqU decl.uvars (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
            (s.fieldType i ctor.fields[i]) normalized ∧
          decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) i ctor.fields[i].isRecursive
            normalized := by
    by_cases hunsafe : decl.isUnsafe = true
    · exact Or.inl (D.safety.trans hunsafe)
    refine Or.inr fun ctor hctor i hi => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hk' : k < decl.ownedConstructors.length := by rw [← D.size]; simpa using hk
    obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ := H.flatMinorIndex k hk'
    have hk2 : recursorMinorOffset indTypes owner + localIndex < s.constructors.size := by
      simpa using hk
    simp only [Array.getElem_toList] at hi ⊢
    exact D.fieldPositive owner howner localIndex hlocal hk2 hunsafe i hi
  by_cases hempty : decl.types = []
  · have hfamilies : s.families = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      rw [hfamSize, H.cardinality.records, hempty]
      rfl
    have hctors : s.constructors.size = 0 := by
      rw [D.size]
      simp [VInductDecl.ownedConstructors, hempty]
    have hctorsList : s.constructors.toList = [] := by
      simpa using hctors
    refine ⟨D.uvars, hparams, D.safety, ?_, ⟨R.headerVEnv, R.core.typesAdded, ?_⟩,
      ?_, Harity⟩
    · simp [InductiveSignature.declaration, hfamilies, hempty]
    · simp [InductiveSignature.declaration, hfamilies, hctorsList,
        VInductDecl.constructorConstants, hempty]
    · rcases Hpositive with h | h
      · exact Or.inl h
      · exact Or.inr ⟨R.headerVEnv, R.core.typesAdded, h⟩
  apply sourceModelsOfTablesPositive
    (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core hempty
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core))
    R.core.typesAdded D.uvars hparams D.safety ?_ Hctors Hpositive Harity
  apply List.forall₂_of_getElem (by
    simp [hfamSize, H.cardinality.records])
  intro i hi hi'
  have howner : i < H.recInfos.size := by rw [H.cardinality.records]; exact hi'
  have hget : s.families.toList[i] = H.families[i]'(by simpa using howner) := by
    simp only [Array.getElem_toList]
    exact D.family_getElem i (by simpa using hi)
  rw [hget, H.families_name ⟨i, howner⟩, H.families_indices ⟨i, howner⟩,
    H.families_level ⟨i, howner⟩]
  refine ⟨rfl, ?_, rfl⟩
  rw [H.sourceIndices_length, H.cardinality.indices i howner]

end Lean4Lean.VerifyInductive
