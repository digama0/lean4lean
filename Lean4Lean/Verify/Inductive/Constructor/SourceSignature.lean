import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Header.Block
import Lean4Lean.Theory.Inductive.Normalization
import Lean4Lean.Theory.Inductive.SourceModelNames

/-! The normalized source signature read off the checked headers and constructor
tails: the classification of each field as external or recursive and the
shared family and parameter choices, with the proof that the signature models
the source declaration. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive
open InductiveSignature

/-- Close two definitionally equal dependent contexts around equally typed
bodies. This changes the chosen binder domains by typed equality. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqCtx.closeForalls
    (H : VEnv.IsDefEqCtx env U [] left right)
    (Hbody : env.IsDefEq U left body body' (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U []
      (VExpr.wrapForalls left.reverse body)
      (VExpr.wrapForalls right.reverse body') (.sort resultLevel) := by
  induction H generalizing body body' bodyLevel with
  | zero => exact ⟨bodyLevel, Hbody⟩
  | succ hctx hdom ih =>
    rcases ih (.forallEDF hdom Hbody) with ⟨level, hclosed⟩
    exact ⟨level, by simpa [List.reverse_cons, VExpr.wrapForalls_append, VExpr.wrapForalls] using hclosed⟩

/-- Replace an independently checked parameter prefix by the one shared
source prefix while preserving the selected index domains exactly. -/
theorem canonicalFamilyOfTelescope
    {env : VEnv} {U : Nat} {params ownParams indices : List VExpr}
    {source result exprType : VExpr} {resultLevel : VLevel}
    (henv : env.WF) (htype : env.IsType U [] source)
    (hnormalized : env.IsDefEq U [] source
      (VExpr.wrapForalls (ownParams ++ indices) result) exprType)
    (hparams : env.IsDefEqCtx U [] params.reverse ownParams.reverse)
    (hresult : env.IsDefEq U (indices.reverse ++ ownParams.reverse)
      result (.sort resultLevel) (.sort (.succ resultLevel))) :
    env.IsDefEqU U [] source
      (VExpr.wrapForalls (params ++ indices) (.sort resultLevel)) := by
  have hnormalizedType := htype.defeqU_l henv trivial ⟨_, hnormalized⟩
  have htelescope := VEnv.IsType.wrapForalls_inv henv trivial hnormalizedType
  obtain ⟨sortLevel, hwrapped⟩ := VExpr.wrapForalls_defeq
    (domains := ownParams ++ indices) (Γ := [])
    (by simpa using htelescope.1)
    (by simpa [List.reverse_append] using hresult)
  have hownType : env.IsType U []
      (VExpr.wrapForalls ownParams (VExpr.wrapForalls indices (.sort resultLevel))) := by
    simpa [VExpr.wrapForalls_append] using
      (show env.IsType U []
        (VExpr.wrapForalls (ownParams ++ indices) (.sort resultLevel)) from
        ⟨sortLevel, hwrapped.hasType.2⟩)
  obtain ⟨_, bodyLevel, hbody⟩ := VEnv.IsType.wrapForalls_inv henv trivial hownType
  have hbody' : env.HasType U ownParams.reverse
      (VExpr.wrapForalls indices (.sort resultLevel)) (.sort bodyLevel) := by
    simpa using hbody
  obtain ⟨canonicalLevel, hcanonical⟩ :=
    (hparams.symm henv.ordered).closeForalls hbody'
  refine VEnv.IsDefEqU.trans henv trivial
    (VEnv.IsDefEqU.trans henv trivial ⟨_, hnormalized⟩ ⟨_, hwrapped⟩) ?_
  simpa [List.reverse_reverse, VExpr.wrapForalls_append] using
    (show env.IsDefEqU U []
      (VExpr.wrapForalls ownParams.reverse.reverse
        (VExpr.wrapForalls indices (.sort resultLevel)))
      (VExpr.wrapForalls params.reverse.reverse
        (VExpr.wrapForalls indices (.sort resultLevel))) from
        ⟨.sort canonicalLevel, hcanonical⟩)

/-- A retained recursive normal form determines exactly the recursive shape expected by
the independent generator, using the shared family table. -/
theorem _root_.Lean4Lean.VInductDecl.RecursiveNormalForm.recursiveShape
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (H : decl.RecursiveNormalForm (VLevel.params decl.uvars) depth normalized) :
    ∃ r : Recursive s.families.size,
      normalized = s.recursiveType depth r ∧
      (∀ domain ∈ r.binders, domain.SourceConstFree (s.families.toList.map (·.name))) ∧
      (∀ index ∈ r.indices, index.SourceConstFree (s.families.toList.map (·.name))) := by
  rcases H with ⟨domains, result, rfl, hdomains, hresult, sourceHead, hsourceHead, hhead⟩
  rcases hresult with ⟨source, hsource, _, levels, hfn, hlevels, hargs, hparamsAt, hindices⟩
  have hlevelsEq : levels = VLevel.params decl.uvars :=
    (VExpr.const.inj (hfn.symm.trans hhead)).2
  subst levels
  change result.getAppFnArgs.1 = .const source.name (VLevel.params decl.uvars) at hfn
  change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (depth + domains.length) at hparamsAt
  have hsourceName : source.name ∈ s.families.toList.map (·.name) := by
    rw [hnames]
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  rcases List.mem_map.mp hsourceName with ⟨family, hfamily, hname⟩
  rcases List.mem_iff_getElem.mp hfamily with ⟨owner, howner, rfl⟩
  let r : Recursive s.families.size := {
    binders := domains
    target := ⟨owner, by simpa using howner⟩
    indices := result.getAppFnArgs.2.drop decl.nparams }
  refine ⟨r, ?_, ?_, ?_⟩
  · unfold InductiveSignature.recursiveType InductiveSignature.familyApp
    dsimp only [r]
    have hname' : s.families[r.target].name = source.name := by simpa [r] using hname
    rw [huvars, hname']
    congr 1
    have hrebuild := VerifyInductive.VExpr.mkApps_getAppFnArgs result
    change VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 = result at hrebuild
    rw [hfn] at hrebuild
    have hparamVars : vars s.params.length (depth + domains.length) =
        decl.paramVars (depth + domains.length) := by
      simp [vars, VInductDecl.paramVars, hparams]
    rw [hparamVars, ← hparamsAt, List.take_append_drop]
    exact hrebuild.symm
  · intro domain hdomain
    simpa [hnames] using hdomains domain hdomain
  · intro index hindex
    simpa [hnames] using hindices index hindex

/-- A retained uniform positive normal form is either family-free or determines the
recursive shape expected by the independent generator (`RecursiveNormalForm.recursiveShape`). -/
theorem _root_.Lean4Lean.VInductDecl.UniformFieldNormalForm.recursiveShape
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (H : decl.UniformFieldNormalForm (VLevel.params decl.uvars) depth normalized) :
    normalized.SourceConstFree (s.families.toList.map (·.name)) ∨
      ∃ r : Recursive s.families.size,
        normalized = s.recursiveType depth r ∧
        (∀ domain ∈ r.binders, domain.SourceConstFree (s.families.toList.map (·.name))) ∧
        (∀ index ∈ r.indices, index.SourceConstFree (s.families.toList.map (·.name))) := by
  rcases H with hfree | H
  · exact .inl (by simpa [hnames] using hfree)
  · exact .inr (VInductDecl.RecursiveNormalForm.recursiveShape huvars hparams hnames H)

/-- Classification part of the per-field source signature model: an external
field normalizes to a source-free type, and a recursive field is
definitionally its generated recursive type with source-free binders and
indices. -/
def SignatureFieldClass (env : VEnv) (U : Nat) (s : InductiveSignature)
    (ctx : List VExpr) (depth : Nat) : Field s.families.size → Prop
  | .external type => s.isUnsafe = true ∨ ∃ normalized,
      env.IsDefEqU U ctx type normalized ∧
      normalized.SourceConstFree (s.families.toList.map (·.name))
  | .recursive type r =>
      env.IsDefEqU U ctx type (s.recursiveType depth r) ∧
      (s.isUnsafe = true ∨
        (∀ domain ∈ r.binders, domain.SourceConstFree (s.families.toList.map (·.name))) ∧
        (∀ index ∈ r.indices, index.SourceConstFree (s.families.toList.map (·.name))))

/-- Per-field part of the source signature model, indexed by the real prefix
context. Stored field domains remain exactly the source domains. Besides the
classification, every field's domain is definitionally a uniform positive
normal form at the source universes, in the branch its classification names
(`ClassifiedFieldNormalForm`). -/
def SignatureFieldModel (env : VEnv) (decl : VInductDecl) (s : InductiveSignature)
    (ctx : List VExpr) (depth : Nat) (field : Field s.families.size) : Prop :=
  SignatureFieldClass env decl.uvars s ctx depth field ∧
  (s.isUnsafe = true ∨ ∃ normalized,
    env.IsDefEqU decl.uvars ctx (s.fieldType depth field) normalized ∧
    decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) depth field.isRecursive
      normalized)

/-- Select the independent field classification from the successful source
check, retaining the exact domain in both external and recursive cases. The
classification is the one the positivity check returned. -/
theorem signatureFieldOfUniform
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (H : decl.isUnsafe = true ∨ ∃ normalized,
      env.IsDefEqU decl.uvars ctx domain normalized ∧
      decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) depth recursive normalized) :
    ∃ field : Field s.families.size, s.fieldType depth field = domain ∧
      (s.isUnsafe = true ∨ field.isRecursive = recursive) ∧
      SignatureFieldModel env decl s ctx depth field := by
  rcases H with hunsafe | ⟨normalized, hnormal, hshape⟩
  · exact ⟨.external domain, rfl, .inl (hsafety.trans hunsafe),
      .inl (hsafety.trans hunsafe), .inl (hsafety.trans hunsafe)⟩
  cases recursive with
  | false =>
    have hfree : normalized.SourceConstFree (decl.types.map (·.name)) := hshape
    exact ⟨.external domain, rfl, .inr rfl,
      .inr ⟨normalized, hnormal, by simpa [hnames] using hfree⟩,
      .inr ⟨normalized, hnormal, hshape⟩⟩
  | true =>
    obtain ⟨r, hr, hdomains, hindices⟩ :=
      VInductDecl.RecursiveNormalForm.recursiveShape huvars hparams hnames hshape
    have hpos : s.isUnsafe = true ∨ ∃ normalized,
        env.IsDefEqU decl.uvars ctx (s.fieldType depth (.recursive domain r)) normalized ∧
        decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) depth
          (Field.recursive domain r).isRecursive normalized :=
      .inr ⟨normalized, hnormal, hshape⟩
    rw [hr] at hnormal
    exact ⟨.recursive domain r, rfl, .inr rfl,
      ⟨hnormal, .inr ⟨hdomains, hindices⟩⟩, hpos⟩

/-- Fold the source telescope in binder order. Classification does not
replace a domain, so every later field keeps exactly its source context. -/
theorem signatureFieldsOfUniform
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    {domains : List VExpr} {classes : List Bool}
    (hlength : classes.length = domains.length)
    (H : ∀ i (hi : i < domains.length) (hc : i < classes.length),
      decl.isUnsafe = true ∨ ∃ normalized,
        env.IsDefEqU decl.uvars ((domains.take i).reverse ++ ctx) domains[i] normalized ∧
        decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) (depth + i) classes[i]
          normalized) :
    ∃ fields : List (Field s.families.size),
      fields.map (s.fieldType 0) = domains ∧
      (s.isUnsafe = true ∨ fields.map Field.isRecursive = classes) ∧
      ∀ i (hi : i < fields.length),
        SignatureFieldModel env decl s ((domains.take i).reverse ++ ctx)
          (depth + i) fields[i] := by
  induction domains generalizing ctx depth classes with
  | nil =>
    have : classes = [] := List.eq_nil_of_length_eq_zero (by simpa using hlength)
    subst this
    exact ⟨[], rfl, .inr rfl, by intro i hi; simp at hi⟩
  | cons domain domains ih =>
    obtain ⟨recursive, classes, rfl⟩ : ∃ recursive rest, classes = recursive :: rest := by
      cases classes with
      | nil => simp at hlength
      | cons recursive rest => exact ⟨recursive, rest, rfl⟩
    have hhead := H 0 (by simp) (by simp)
    simp only [List.take_zero, List.reverse_nil, List.nil_append, List.getElem_cons_zero,
      Nat.add_zero] at hhead
    obtain ⟨field, hfield, hclass, hmodel⟩ :=
      signatureFieldOfUniform huvars hparams hnames hsafety hhead
    have htail : ∀ i (hi : i < domains.length) (hc : i < classes.length),
        decl.isUnsafe = true ∨ ∃ normalized,
          env.IsDefEqU decl.uvars ((domains.take i).reverse ++ (domain :: ctx)) domains[i]
            normalized ∧
          decl.ClassifiedFieldNormalForm (VLevel.params decl.uvars) (depth + 1 + i)
            classes[i] normalized := by
      intro i hi hc
      have hnext := H (Nat.succ i) (by simpa using hi) (by simpa using hc)
      simp only [List.getElem_cons_succ] at hnext
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
    obtain ⟨fields, hfields, hclasses, hmodels⟩ := ih (by simpa using hlength) htail
    refine ⟨field :: fields, ?_, ?_, ?_⟩
    · simp only [List.map_cons, hfields]
      change s.fieldType depth field :: domains = domain :: domains
      rw [hfield]
    · rcases hclass with hunsafe | hclass
      · exact .inl hunsafe
      rcases hclasses with hunsafe | hclasses
      · exact .inl hunsafe
      exact .inr (by simp [hclass, hclasses])
    · intro i hi
      cases i with
      | zero => simpa using hmodel
      | succ i =>
        have hi' : i < fields.length := by simpa using hi
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmodels i hi'

theorem _root_.Lean4Lean.VInductDecl.UniformCtorTail.defeqCtx
    (H : VInductDecl.UniformCtorTail env decl target levels ctx₁ depth tail classes)
    (henv : env.Ordered) (hctx : env.IsDefEqCtx decl.uvars base ctx₁ ctx₂) :
    decl.UniformCtorTail env target levels ctx₂ depth tail classes := by
  induction H generalizing ctx₂ with
  | result hresult hhead => exact .result hresult hhead
  | field htype hfield _ ih =>
    obtain ⟨u, hu⟩ := htype
    refine .field ⟨u, hu.defeqDFC henv hctx⟩ ?_ (ih (.succ hctx hu))
    rcases hfield with hunsafe | ⟨normalized, hnormal, hshape⟩
    · exact .inl hunsafe
    · exact .inr ⟨normalized, hnormal.defeqDFC henv hctx, hshape⟩

theorem signatureFieldTypes_eq_map (s : InductiveSignature)
    (ctor : Constructor s.families.size) :
    s.fieldTypes ctor = ctor.fields.map (s.fieldType 0) := by
  change ctor.fields.zipIdx.map ((s.fieldType 0) ∘ Prod.fst) = _
  rw [← List.map_map]
  simp

/-- Build a constructor's generator data from the retained literal source
telescope. Field selection preserves every domain, and its semantic model
uses exactly the preceding domains in that same telescope. -/
theorem signatureConstructorOfUniform
    {decl : VInductDecl} {s : InductiveSignature} {target : VInductiveType}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (owner : Fin s.families.size) (howner : s.families[owner].name = target.name)
    (ctorName : Name)
    (H : decl.UniformCtorTail env target (VLevel.params decl.uvars)
      s.params.reverse 0 tail classes) :
    ∃ ctor : Constructor s.families.size,
      ctor.name = ctorName ∧ ctor.owner = owner ∧
      VExpr.wrapForalls s.params tail = s.constructorType ctor ∧
      (s.isUnsafe = true ∨ ctor.fields.map Field.isRecursive = classes) ∧
      ∀ i (hi : i < ctor.fields.length),
        SignatureFieldModel env decl s
          (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse) i ctor.fields[i] := by
  obtain ⟨domains, result, rfl, hclassesLength, hresult, hhead, hfields⟩ := H.telescope
  obtain ⟨fields, hfieldsEq, hclasses, hmodels⟩ := signatureFieldsOfUniform
    huvars hparams hnames hsafety hclassesLength (fun i hi hc => (hfields i hi hc).2)
  have hlength : fields.length = domains.length := by
    simpa using congrArg List.length hfieldsEq
  let ctor : Constructor s.families.size := {
    name := ctorName
    owner := owner
    fields := fields
    indices := result.getAppFnArgs.2.drop decl.nparams }
  have hfieldTypes : s.fieldTypes ctor = domains := by
    rw [signatureFieldTypes_eq_map]
    exact hfieldsEq
  refine ⟨ctor, rfl, rfl, ?_, hclasses, ?_⟩
  · unfold InductiveSignature.constructorType
    rw [VExpr.wrapForalls_append, hfieldTypes]
    congr 2
    rcases hresult with ⟨family, hfamily, htarget, levels, hfn, hlevels, hargs, hparamAt, hindices⟩
    change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (0 + domains.length) at hparamAt
    simp only [Nat.zero_add] at hparamAt
    have hrebuild := VExpr.mkApps_getAppFnArgs result
    change VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 = result at hrebuild
    rw [hhead] at hrebuild
    unfold InductiveSignature.familyApp
    dsimp only [ctor]
    rw [howner, huvars, hlength]
    have hparamVars : vars s.params.length domains.length = decl.paramVars domains.length := by
      simp [vars, VInductDecl.paramVars, hparams]
    rw [hparamVars, ← hparamAt, List.take_append_drop]
    exact hrebuild.symm
  · intro i hi
    rw [hfieldTypes]
    simpa only [Nat.zero_add] using hmodels i hi

namespace checkInductiveTypes.loopInd

/-- Select one normalized source header per family, before adding the fresh
recursor universe. The family table and later generation share this choice. -/
noncomputable def HeaderStatsWF.signatureFamily
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (i : Nat) (hi : i < decl.types.length) : InductiveSignature.Family :=
  let source := Classical.choose (H.normalizedShapes i hi)
  { name := decl.types[i].name
    indices := source.indices
    resultLevel := decl.types[i].resultLevel }

noncomputable def HeaderStatsWF.signatureFamilies
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    Array InductiveSignature.Family :=
  Array.ofFn fun i : Fin decl.types.length => H.signatureFamily i.val i.isLt

@[simp] theorem HeaderStatsWF.signatureFamilies_size
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    H.signatureFamilies.size = decl.types.length := by
  simp [signatureFamilies]

/-- The chosen index domains are those of the same retained normalized source
header that proves this family's model; their universe context is unchanged. -/
theorem HeaderStatsWF.signatureFamily_model
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (henv : env.WF)
    (i : Nat) (hi : i < decl.types.length)
    (htype : env.IsType decl.uvars [] decl.types[i].type) :
    (H.signatureFamily i hi).name = decl.types[i].name ∧
    (H.signatureFamily i hi).indices.length = decl.types[i].numIndices ∧
    (H.signatureFamily i hi).resultLevel = decl.types[i].resultLevel ∧
    env.IsDefEqU decl.uvars [] decl.types[i].type
      (VExpr.wrapForalls (H.headers.params ++ (H.signatureFamily i hi).indices)
        (.sort (H.signatureFamily i hi).resultLevel)) := by
  let source := Classical.choose (H.normalizedShapes i hi)
  obtain ⟨result, exprType, hnormalized, hresult⟩ :=
    Classical.choose_spec (H.normalizedShapes i hi)
  refine ⟨rfl, source.indexCount, rfl, ?_⟩
  have hcanonical := canonicalFamilyOfTelescope henv
    (by simpa [H.uvars] using htype) hnormalized source.parameters hresult
  simpa [signatureFamily, source, H.uvars] using hcanonical

theorem HeaderStatsWF.signatureFamilies_names
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    H.signatureFamilies.toList.map (·.name) = decl.types.map (·.name) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < decl.types.length := by simpa using hright
    simp [signatureFamilies, signatureFamily]

/-- The common source parameter list has exactly the arity checked by the
executable parameter cache. -/
theorem HeaderStatsWF.signatureParams_length
    (H : HeaderStatsWF env Us Δ stats decl depth) :
    H.headers.params.length = decl.nparams := by
  have hcontext := H.paramsContext.length_eq
  have hcached := checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length H.cachedScope
  have hscope := List.Forall₂.length_eq H.cachedScope
  have htranslated := List.Forall₂.length_eq H.params
  simp only [List.length_reverse, Array.length_toList,
    VInductDecl.paramVars, List.length_map, List.length_reverse, List.length_range] at *
  omega

/-- Shared source-universe family and parameter choices. Constructor fields
are filled from the checked source-tail certificates over this same table. -/
noncomputable def HeaderStatsWF.signatureHeader
    (H : HeaderStatsWF env Us Δ stats decl depth) : InductiveSignature where
  uvars := decl.uvars
  params := H.headers.params
  families := H.signatureFamilies
  constructors := #[]
  isUnsafe := decl.isUnsafe

end checkInductiveTypes.loopInd

end VerifyInductive
end Lean4Lean

/-! Assemble one source model from the shared source selections. -/

namespace Lean4Lean.VerifyInductive
open InductiveSignature

/-- The ordered source family and constructor tables, together with each
field's actual checked classification, determine a full normalized model. -/
theorem sourceModelsOfTables {s : InductiveSignature} {decl : VInductDecl}
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
    (Hfields : ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
      SignatureFieldModel envTypes decl s
        (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse) i ctor.fields[i])
    (Harity : ∀ ctor ∈ s.constructors.toList,
      ctor.indices.length = s.families[ctor.owner].indices.length) :
    s.Models env decl := by
  have hnames : s.families.toList.map (·.name) = decl.types.map (·.name) := by
    have hr := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) Hfamilies
    clear Hfamilies Hctors Hfields Hsource
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
        (constructor_model_in_family (R := fun ctor source => ctor.name = source.name ∧
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
    apply List.forall₂_of_getElem (by simpa [declaration] using Lean4Lean.List.Forall₂.length_eq Hfamilies)
    intro i hi hi'
    have hsize : i < s.families.size := by simpa [declaration] using hi
    let owner : Fin s.families.size := ⟨i, hsize⟩
    have hget := List.forall₂_getElem Hfamilies i (by simpa using hsize) hi'
    have he : s.declaration.types[i] = s.declarationFamily owner := by
      simp [declaration, declarationFamily, owner]
    rw [he]
    refine ⟨hget.1, huvars.trans (Hsource.2.2.1 _ (List.getElem_mem hi')).symm,
      hget.2.1, ?_, hctorFamilies owner (List.getElem_mem hi') hget.1⟩
    exact hget.2.2 ▸ rfl
  refine ⟨huvars, hparams, hsafety, ?_, ⟨envTypes, hadd, ?_⟩, ?_, Harity⟩
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        ctorNames_eq_of_forall₂ h.2.2.2.2 (fun _ _ hc => hc.1)⟩) hfull
  · change List.Forall₂ C (s.declaration.types.flatMap (·.ctors)) (decl.types.flatMap (·.ctors))
    clear Hfamilies Hctors Hfields hnames hfamilyNames hctorFamilies Hsource
    generalize s.declaration.types = left at hfull ⊢
    generalize decl.types = right at hfull ⊢
    induction hfull with
    | nil => exact .nil
    | cons h _ ih => exact h.2.2.2.2.append' ih
  · by_cases hunsafe : s.isUnsafe = true
    · exact Or.inl hunsafe
    · refine Or.inr ⟨envTypes, hadd, ?_⟩
      intro ctor hc i hi
      exact (Hfields ctor hc i hi).2.resolve_left hunsafe

end Lean4Lean.VerifyInductive
