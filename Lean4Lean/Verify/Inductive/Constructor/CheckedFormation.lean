import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Constructor.SourceSignature

/-! # The checked formation

`CheckedFormation` is the data available once every constructor of a declaration is checked
(`AddInductive.checkConstructors`) and before the constructors are declared: the header
environment, the translated declaration (`TrInductDeclCore`), the formation certificate and the
field classification the executable returns. From it the constructor phase delivers a source
signature of the declaration (`CheckedFormation.signature`), which the recursor phase's generator
instantiates (section 3.2 of the design notes).

Ported from the source branch's `Constructor/CheckedFormation.lean`: the signature's family
table is read off the header certificate (`HeaderCertificate.familyTelescope`) and its
constructors off the checked tails (`tails`, an added field: the abstract half of the source
branch's `ConstructorTails`). The case eliminators of the source branch are gone. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The checked tail of one constructor `ctor` of `target`: its type is definitionally a
telescope over a parameter list `ps` (definitionally the common parameters `params`) ending in
a constructor tail certified by the executable check, with the field classification `classes`
the positivity check returned. -/
def CheckedCtorTail (env : VEnv) (decl : VInductDecl) (params : List VExpr)
    (target : VInductiveType) (ctor : VConstVal) (classes : List Bool) : Prop :=
  ∃ ps tail, env.IsDefEqCtx decl.uvars [] params.reverse ps.reverse ∧
    env.IsDefEqU decl.uvars [] ctor.type (VExpr.wrapForalls ps tail) ∧
    ConstructorTailCertificate env decl target ps.reverse 0 tail classes

theorem _root_.Lean4Lean.VInductDecl.UniformCtorTail.mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.UniformCtorTail env decl target levels ctx depth tail classes) :
    VInductDecl.UniformCtorTail env' decl target levels ctx depth tail classes := by
  induction H with
  | result h1 h2 => exact .result h1 h2
  | field htype' hfield _ ih =>
    obtain ⟨u, hu⟩ := htype'
    refine .field ⟨u, hu.mono henv⟩ ?_ ih
    rcases hfield with h | ⟨n, ⟨_, hn⟩, hs⟩
    · exact .inl h
    · exact .inr ⟨n, ⟨_, hn.mono henv⟩, hs⟩

theorem ConstructorTailCertificate.mono {env env' : VEnv} (henv : env ≤ env')
    (H : ConstructorTailCertificate env decl target ctx depth tail classes) :
    ConstructorTailCertificate env' decl target ctx depth tail classes := by
  obtain ⟨hshape, ⟨_, hty⟩, hraw, huniform⟩ := H
  exact ⟨hshape.mono henv, ⟨_, hty.mono henv⟩, hraw, huniform.mono henv⟩

theorem CheckedCtorTail.mono {env env' : VEnv} (henv : env ≤ env')
    (H : CheckedCtorTail env decl params target ctor classes) :
    CheckedCtorTail env' decl params target ctor classes := by
  obtain ⟨ps, tail, hctx, ⟨_, htype⟩, cert⟩ := H
  exact ⟨ps, tail, hctx.mono henv, ⟨_, htype.mono henv⟩, cert.mono henv⟩

/-- The checked formation of a declaration: its header environment and, in it, the checked
constructor types, their translation and the formation certificate. -/
structure CheckedFormation (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) where
  headerEnv : Environment
  headers : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv
  /-- The abstract constructor environment. -/
  ctorVEnv : VEnv
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
    headers.context.venv ctorVEnv
  formation : FormationCertificate sourceEnv decl
  params_eq : formation.headers.params = headers.headers.params
  checked : CheckedConstructorCertificate sourceEnv decl headers.context.venv
    formation.headers.params
  /-- The field classifications returned by the executable constructor check, family by
  family and constructor by constructor. -/
  classes : List (List (List Bool))
  classes_length : classes.length = indTypes.size
  /-- (Added by the constructor agent.) The checked tail of every constructor, with the
  classification the executable returned for it. -/
  tails : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
    CheckedCtorTail headers.context.venv decl formation.headers.params decl.types[i]
      decl.types[i].ctors[j] (classes[i]![j]!)

namespace CheckedFormation

open InductiveSignature

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}

/-- The abstract header environment. -/
abbrev headerVEnv (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    VEnv := B.headers.context.venv

theorem headerVEnv_wf (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    B.headerVEnv.WF := B.headers.context.wf

theorem sourceEnv_wf (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    sourceEnv.WF := by
  rw [← B.headers.sourceContextVEnv]; exact B.headers.sourceContext.wf

theorem sourceLE (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    sourceEnv ≤ B.headerVEnv := VEnv.addConstVals_le B.core.typesAdded

theorem typeNames_nodup
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    (decl.types.map (·.name)).Nodup := by
  simpa only [VInductDecl.typeConstants, List.map_map, Function.comp_def] using
    VEnv.addConstVals_names_nodup B.core.typesAdded

/-- The header type of every family is a well-formed type of the source environment. -/
theorem familyIsType (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    {type : VInductiveType} (htype : type ∈ decl.types) :
    sourceEnv.IsType decl.uvars [] type.type := by
  obtain ⟨_, _, htr⟩ := List.Forall₂.forall_exists_r B.core.types type htype
  have hu : type.uvars = decl.uvars := htr.header.uvars.trans B.core.uvars.symm
  have := htr.header.wf
  simpa only [VConstant.WF, VConstVal.toVConstant, hu] using this

theorem familyTelescope_exists
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Fin decl.types.length) :
    ∃ indices : List VExpr, indices.length = decl.types[i].numIndices ∧
      sourceEnv.IsDefEqU decl.uvars [] decl.types[i].type
        (VExpr.wrapForalls (B.formation.headers.params ++ indices)
          (.sort decl.types[i].resultLevel)) :=
  B.formation.headers.familyTelescope B.sourceEnv_wf (List.getElem_mem i.isLt)
    (B.familyIsType (List.getElem_mem i.isLt))

/-- The family of the source signature at position `i`: the family's name, result level and
the index telescope of its type shape. -/
noncomputable def family
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Fin decl.types.length) : Family where
  name := decl.types[i].name
  indices := Classical.choose (B.familyTelescope_exists i)
  resultLevel := decl.types[i].resultLevel

theorem family_spec
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Fin decl.types.length) :
    (B.family i).indices.length = decl.types[i].numIndices ∧
      sourceEnv.IsDefEqU decl.uvars [] decl.types[i].type
        (VExpr.wrapForalls (B.formation.headers.params ++ (B.family i).indices)
          (.sort (B.family i).resultLevel)) :=
  Classical.choose_spec (B.familyTelescope_exists i)

/-- The shared source-universe parameters and family choices, before any constructor. -/
noncomputable def signatureHeader
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    InductiveSignature where
  uvars := decl.uvars
  params := B.formation.headers.params
  families := Array.ofFn B.family
  constructors := #[]
  isUnsafe := decl.isUnsafe

@[simp] theorem signatureHeader_families_size
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    B.signatureHeader.families.size = decl.types.length := by
  simp [signatureHeader]

theorem signatureHeader_family
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Nat) (hi : i < B.signatureHeader.families.size) :
    B.signatureHeader.families[i] = B.family ⟨i, by simpa using hi⟩ := by
  simp [signatureHeader]

theorem signatureHeader_names
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    B.signatureHeader.families.toList.map (·.name) = decl.types.map (·.name) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [signatureHeader, family]

theorem signatureHeader_params_length
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hne : decl.types ≠ []) :
    B.signatureHeader.params.length = decl.nparams := by
  obtain ⟨type, htype⟩ := List.exists_mem_of_ne_nil _ hne
  exact B.formation.headers.params_length htype

/-- The family table, in the form of `sourceModelsOfTables`. -/
theorem signatureHeader_families
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    List.Forall₂ (fun f src =>
      f.name = src.name ∧ f.indices.length = src.numIndices ∧
      f.resultLevel = src.resultLevel ∧
      sourceEnv.IsDefEqU decl.uvars []
        (VExpr.wrapForalls (B.signatureHeader.params ++ f.indices) (.sort f.resultLevel))
        src.type)
      B.signatureHeader.families.toList decl.types := by
  apply List.forall₂_of_getElem (by simp)
  intro i hi hi'
  obtain ⟨hlen, hdef⟩ := B.family_spec ⟨i, hi'⟩
  simp only [Array.getElem_toList, B.signatureHeader_family i (by simpa using hi)]
  exact ⟨rfl, hlen, rfl, hdef.symm⟩

/-- A fixed parameter prefix is injective in its residual expression. -/
private theorem wrapForalls_body_eq {params : List VExpr} {left right : VExpr}
    (H : VExpr.wrapForalls params left = VExpr.wrapForalls params right) : left = right := by
  induction params with
  | nil => exact H
  | cons param params ih => exact ih (VExpr.forallE.inj H).2

/-- Each checked constructor supplies one constructor over the shared family table. -/
theorem signatureHeader_constructor
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Nat) (hi : i < decl.types.length)
    (j : Nat) (hj : j < decl.types[i].ctors.length) :
    ∃ ctor : InductiveSignature.Constructor B.signatureHeader.families.size,
      B.signatureHeader.families[ctor.owner].name = decl.types[i].name ∧
      ctor.name = decl.types[i].ctors[j].name ∧
      B.headerVEnv.IsDefEqU decl.uvars []
        (B.signatureHeader.constructorType ctor) decl.types[i].ctors[j].type ∧
      (B.signatureHeader.isUnsafe = true ∨
        ctor.fields.map Field.isRecursive = B.classes[i]![j]!) ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel B.headerVEnv decl B.signatureHeader
          (((B.signatureHeader.fieldTypes ctor).take k).reverse ++
            B.signatureHeader.params.reverse) k ctor.fields[k]) ∧
      ctor.indices.length = B.signatureHeader.families[ctor.owner].indices.length := by
  have henv := B.headerVEnv_wf
  have hne : decl.types ≠ [] := List.ne_nil_of_mem (List.getElem_mem hi)
  obtain ⟨ps, tail, hctx, htype, cert⟩ := B.tails i hi j hj
  have huniform := cert.uniform.defeqCtx henv.ordered (hctx.symm henv.ordered)
  let owner : Fin B.signatureHeader.families.size := ⟨i, by simpa using hi⟩
  have howner : B.signatureHeader.families[owner].name = decl.types[i].name := by
    simp [owner, signatureHeader, family]
  obtain ⟨ctor, hname, hctorOwner, hliteral, hclasses, hfields⟩ :=
    signatureConstructorOfUniform (s := B.signatureHeader) rfl
      (B.signatureHeader_params_length hne) B.signatureHeader_names rfl owner howner
      decl.types[i].ctors[j].name huniform
  obtain ⟨level, htailType⟩ := cert.isType
  obtain ⟨closedLevel, hclosed⟩ := (hctx.symm henv.ordered).closeForalls htailType
  have hclosed' : B.headerVEnv.IsDefEqU decl.uvars []
      (VExpr.wrapForalls ps tail) (VExpr.wrapForalls B.signatureHeader.params tail) := by
    have h : B.headerVEnv.IsDefEqU decl.uvars []
        (VExpr.wrapForalls ps.reverse.reverse tail)
        (VExpr.wrapForalls B.formation.headers.params.reverse.reverse tail) := ⟨_, hclosed⟩
    simp only [List.reverse_reverse] at h
    exact h
  refine ⟨ctor, by simp only [hctorOwner]; exact howner, hname, ?_, hclasses, hfields, ?_⟩
  · rw [← hliteral]
    exact (htype.trans henv trivial hclosed').symm
  · have hliteral' : tail = VExpr.wrapForalls (B.signatureHeader.fieldTypes ctor)
        (B.signatureHeader.familyApp ctor.owner (VLevel.params B.signatureHeader.uvars)
          (vars B.signatureHeader.params.length ctor.fields.length) ctor.indices) := by
      apply wrapForalls_body_eq (params := B.signatureHeader.params)
      simpa only [constructorType, VExpr.wrapForalls_append] using hliteral
    obtain ⟨domains, result, same, application, head⟩ := cert.raw
    have hfam : B.signatureHeader.families[ctor.owner].indices.length =
        decl.types[i].numIndices := by
      simp only [hctorOwner]
      simpa [owner, signatureHeader] using (B.family_spec ⟨i, hi⟩).1
    exact constructor_indices_length_of_rawTail B.typeNames_nodup (List.getElem_mem hi)
      (B.signatureHeader_params_length hne) hfam
      ⟨domains, result, same, application.raw, head⟩ hliteral'

/-- An owned constructor determines its family and local positions: family and
constructor names are distinct. -/
theorem ownedConstructor_index_unique
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    {i i' j j' : Nat} (hi : i < decl.types.length) (hi' : i' < decl.types.length)
    (hj : j < decl.types[i].ctors.length) (hj' : j' < decl.types[i'].ctors.length)
    (hfamily : decl.types[i] = decl.types[i'])
    (hctor : decl.types[i].ctors[j] = decl.types[i'].ctors[j']) :
    i = i' ∧ j = j' := by
  have hii : i = i' := (List.getElem_inj (h₀ := by simpa using hi)
    (h₁ := by simpa using hi') B.typeNames_nodup).mp (by simp [hfamily])
  subst hii
  refine ⟨rfl, ?_⟩
  have hctorNames : (decl.constructorConstants.map VConstVal.name).Nodup :=
    VEnv.addConstVals_names_nodup B.core.ctorsAdded
  have hsub : (decl.types[i].ctors.map VConstVal.name).Sublist
      (decl.constructorConstants.map VConstVal.name) := by
    apply List.Sublist.map
    rw [VInductDecl.constructorConstants, List.flatMap_def]
    exact List.sublist_flatten_of_mem (List.mem_map_of_mem (List.getElem_mem hi))
  exact (List.getElem_inj (h₀ := by simpa using hj) (h₁ := by simpa using hj')
    (hsub.nodup hctorNames)).mp (by simp [hctor])

theorem signatureHeader_ownedConstructor
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (pair : VInductiveType × VConstVal) (hpair : pair ∈ decl.ownedConstructors) :
    ∃ ctor : InductiveSignature.Constructor B.signatureHeader.families.size,
      B.signatureHeader.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name ∧
      B.headerVEnv.IsDefEqU decl.uvars []
        (B.signatureHeader.constructorType ctor) pair.2.type ∧
      (∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
        pair = (decl.types[i], decl.types[i].ctors[j]) →
        B.signatureHeader.isUnsafe = true ∨
          ctor.fields.map Field.isRecursive = B.classes[i]![j]!) ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel B.headerVEnv decl B.signatureHeader
          (((B.signatureHeader.fieldTypes ctor).take k).reverse ++
            B.signatureHeader.params.reverse) k ctor.fields[k]) ∧
      ctor.indices.length = B.signatureHeader.families[ctor.owner].indices.length := by
  obtain ⟨family, hfamily, hmapped⟩ := List.mem_flatMap.mp hpair
  obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hmapped
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hfamily
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
  obtain ⟨sig, hfamilyName, hname, htype, hclasses, hfields, harity⟩ :=
    B.signatureHeader_constructor i hi j hj
  refine ⟨sig, hfamilyName, hname, htype, ?_, hfields, harity⟩
  intro i' hi' j' hj' hpair'
  obtain ⟨hfam, hctor'⟩ := Prod.mk.inj hpair'
  obtain ⟨rfl, rfl⟩ := B.ownedConstructor_index_unique hi hi' hj hj' hfam hctor'
  exact hclasses

/-- Choose each constructor once, in the declaration's exact flattened order. -/
noncomputable def signatureConstructor
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Fin decl.ownedConstructors.length) :
    InductiveSignature.Constructor B.signatureHeader.families.size :=
  Classical.choose (B.signatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))

theorem signatureConstructor_spec
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Fin decl.ownedConstructors.length) :
    let ctor := B.signatureConstructor i
    let pair := decl.ownedConstructors[i]
    B.signatureHeader.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name ∧
      B.headerVEnv.IsDefEqU decl.uvars []
        (B.signatureHeader.constructorType ctor) pair.2.type ∧
      (∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
        pair = (decl.types[i], decl.types[i].ctors[j]) →
        B.signatureHeader.isUnsafe = true ∨
          ctor.fields.map Field.isRecursive = B.classes[i]![j]!) ∧
      (∀ k (hk : k < ctor.fields.length),
        SignatureFieldModel B.headerVEnv decl B.signatureHeader
          (((B.signatureHeader.fieldTypes ctor).take k).reverse ++
            B.signatureHeader.params.reverse) k ctor.fields[k]) ∧
      ctor.indices.length = B.signatureHeader.families[ctor.owner].indices.length :=
  Classical.choose_spec (B.signatureHeader_ownedConstructor _ (List.getElem_mem i.isLt))

/-- The source signature of a nonempty checked formation. -/
noncomputable def sourceSignature
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    InductiveSignature :=
  { B.signatureHeader with constructors := Array.ofFn B.signatureConstructor }

theorem sourceSignature_fieldType
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (field : Field B.signatureHeader.families.size) :
    B.sourceSignature.fieldType k field = B.signatureHeader.fieldType k field := by
  cases field <;> rfl

theorem sourceSignature_fieldTypes
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (ctor : InductiveSignature.Constructor B.signatureHeader.families.size) :
    B.sourceSignature.fieldTypes ctor = B.signatureHeader.fieldTypes ctor := by
  unfold fieldTypes
  apply List.map_congr_left
  intro field _
  exact B.sourceSignature_fieldType field.1

theorem sourceSignature_constructorType
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (ctor : InductiveSignature.Constructor B.signatureHeader.families.size) :
    B.sourceSignature.constructorType ctor = B.signatureHeader.constructorType ctor := by
  simp only [constructorType, sourceSignature_fieldTypes]
  rfl

theorem sourceSignature_fieldModel
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (field : Field B.signatureHeader.families.size) :
    SignatureFieldModel env decl' B.sourceSignature ctx k field ↔
      SignatureFieldModel env decl' B.signatureHeader ctx k field := by
  cases field <;> rfl

theorem sourceSignature_get
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (i : Nat) (hi : i < B.sourceSignature.constructors.toList.length)
    (hi' : i < decl.ownedConstructors.length) :
    B.sourceSignature.constructors.toList[i] = B.signatureConstructor ⟨i, hi'⟩ := by
  simp only [sourceSignature, Array.getElem_toList, Array.getElem_ofFn]

/-- The source signature of a nonempty checked formation models the declaration. -/
theorem sourceSignature_models
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes)
    (hne : decl.types ≠ []) : B.sourceSignature.Models sourceEnv decl := by
  apply sourceModelsOfTables (s := B.sourceSignature)
    (TrInductDeclCore.sourceWF B.core hne (TrInductDeclCore.sourceNames_nodup B.core))
    B.core.typesAdded rfl (B.signatureHeader_params_length hne) rfl
  · exact List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) B.signatureHeader_families
  · apply List.forall₂_of_getElem (by simp [sourceSignature])
    intro i hi hi'
    have hmodel := B.signatureConstructor_spec ⟨i, hi'⟩
    rw [B.sourceSignature_get i hi hi']
    refine ⟨hmodel.1, hmodel.2.1, ?_⟩
    simpa only [sourceSignature_constructorType, Fin.getElem_fin] using hmodel.2.2.1
  · intro ctor hctor k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hi' : i < decl.ownedConstructors.length := by simpa [sourceSignature] using hi
    have hmodel := B.signatureConstructor_spec ⟨i, hi'⟩
    simp only [B.sourceSignature_get i hi hi'] at hk ⊢
    apply (B.sourceSignature_fieldModel _).2
    rw [sourceSignature_fieldTypes]
    exact hmodel.2.2.2.2.1 k hk
  · intro ctor hctor
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hi' : i < decl.ownedConstructors.length := by simpa [sourceSignature] using hi
    rw [B.sourceSignature_get i hi hi']
    exact (B.signatureConstructor_spec ⟨i, hi'⟩).2.2.2.2.2

/-- The family applications of the source signature are typed in the header environment. -/
theorem sourceSignature_familyTypesWF
    (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    B.sourceSignature.FamilyTypesWF B.headerVEnv decl.uvars := by
  intro owner
  have henv := B.headerVEnv_wf
  have hheader : owner.val < B.signatureHeader.families.size := owner.isLt
  have hdecl : owner.val < decl.types.length := by simpa using hheader
  have hfam := List.forall₂_getElem B.signatureHeader_families owner.val
    (by simpa using hheader) hdecl
  simp only [Array.getElem_toList] at hfam
  obtain ⟨hname, _, _, hdefeq⟩ := hfam
  have hmem : decl.types[owner.val] ∈ decl.types := List.getElem_mem hdecl
  have hsourceWF := TrInductDeclCore.sourceWF B.core
    (List.ne_nil_of_mem hmem) (TrInductDeclCore.sourceNames_nodup B.core)
  have huvars : decl.types[owner.val].uvars = decl.uvars := hsourceWF.2.2.1 _ hmem
  have hlookup : B.headerVEnv.constants decl.types[owner.val].name =
      some decl.types[owner.val].toVConstant :=
    VEnv.addConstVals_get B.core.typesAdded (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have hconst := VEnv.HasType.const0 hlookup (henv.ordered.constWF hlookup)
  change B.headerVEnv.HasType decl.types[owner.val].uvars [] (.const decl.types[owner.val].name
      (VLevel.params decl.types[owner.val].uvars)) decl.types[owner.val].type at hconst
  rw [huvars, ← hname] at hconst
  have hW := hconst.defeqU_r henv trivial (hdefeq.symm.mono B.sourceLE)
  have hWT := hW.isType henv.ordered trivial
  have hctx := (VEnv.IsType.wrapForalls_inv henv.ordered (ctx := []) trivial hWT).1
  simp only [List.append_nil] at hctx
  have happ := VEnv.HasType.mkApps_bvarRange henv hW hctx trivial
  have hctx' : OnCtx (B.signatureHeader.families[owner.val].indices.reverse ++
      B.signatureHeader.params.reverse) (B.headerVEnv.IsType decl.uvars) := by
    simpa [List.reverse_append] using hctx
  refine ⟨hctx', ?_⟩
  change B.headerVEnv.HasType decl.uvars
    (B.signatureHeader.families[owner.val].indices.reverse ++
      B.signatureHeader.params.reverse)
    (VExpr.mkApps (.const B.signatureHeader.families[owner.val].name
      (VLevel.params decl.uvars))
      (InductiveSignature.vars B.signatureHeader.params.length
          B.signatureHeader.families[owner.val].indices.length ++
        InductiveSignature.vars B.signatureHeader.families[owner.val].indices.length 0))
    (.sort B.signatureHeader.families[owner.val].resultLevel)
  rw [vars_append_eq_bvarRange, ← List.length_append]
  simpa [List.reverse_append] using happ

/-- The source signature of the checked formation: a signature modelling the declaration
(`InductiveSignature.Models`), whose family applications are typed in the header environment.
This is the signature the recursor generator instantiates. -/
theorem signature (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ∃ s : InductiveSignature, s.Models sourceEnv decl ∧
      s.FamilyTypesWF B.headerVEnv decl.uvars := by
  by_cases hne : decl.types = []
  · -- The empty declaration: no family, no constructor.
    let s : InductiveSignature :=
      { uvars := decl.uvars
        params := List.replicate decl.nparams (VExpr.sort VLevel.zero)
        families := #[]
        constructors := #[]
        isUnsafe := decl.isUnsafe }
    refine ⟨s, ?_, ?_⟩
    · refine ⟨rfl, by simp [s], rfl, ?_, ⟨B.headerVEnv, B.core.typesAdded, ?_⟩,
        .inr ⟨B.headerVEnv, B.core.typesAdded, ?_⟩, ?_⟩
      all_goals simp [s, declaration, VInductDecl.constructorConstants, hne]
    · intro owner; exact absurd owner.isLt (by simp [s])
  · exact ⟨B.sourceSignature, B.sourceSignature_models hne, B.sourceSignature_familyTypesWF⟩

end CheckedFormation

end VerifyInductive
end Lean4Lean
