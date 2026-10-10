import Lean4Lean.Verify.Inductive.Recursor.Installation
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal

/-! Recursor metadata of a recursor check.

`InductiveSignature.RecursorMetadata` (defined in `Entries/TrRecursorVal.lean`, as the
base that `TrRecursorVal` extends with rule coverage) is established for each installed
recursor entry of a `RecursorInstallation`, against the one instance of the construction's signature
(`RecursorInstallation.canonicalGeneration`). Together with the rule translations of `Rules/` this
shows that the executable's recursors are the translations of the generated ones (section 3.2
of the design notes).
-/

namespace Lean4Lean
namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- `getMajorInduct` reads the head constant of the domain at the major
position of the recursor type. -/
theorem RecursorVal.getMajorInduct_of_binderAt (rec : Lean.RecursorVal)
    (H : Expr.ForallBinderAt rec.type rec.getMajorIdx domain) :
    rec.getMajorInduct = domain.getAppFn.constName! := by
  unfold Lean.RecursorVal.getMajorInduct
  generalize rec.getMajorIdx = n at H ⊢
  generalize rec.type = e at H ⊢
  induction H with
  | here => rfl
  | there _ ih => exact ih

/-- The executable arity counts every binder of a concrete forall telescope. -/
theorem Expr.ForallTelescope.constructorArity
    (H : Expr.ForallTelescope source n result) :
    AddInductive.constructorArity source = n + AddInductive.constructorArity result := by
  induction H with
  | nil => simp
  | cons _ ih => simp [AddInductive.constructorArity, ih]; omega

/-- Installed recursor entries are indexed by the families of the construction's
signature. -/
theorem RecursorInstallation.entries_length_eq
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) :
    H.entries.length = H.generationSignature.families.size := by
  rw [H.generated.length]
  change _ = H.generator.signature.families.size
  rw [H.generator.families, H.families_size]

/-- The head constant of the generated major premise is the owner family. -/
theorem RecursorInstallation.generated_getMajorInduct
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    (H.generated.entry owner howner).info.getMajorInduct =
      (decl.types[owner]'(by
        rw [← H.cardinality.records, ← H.generated.length]; exact howner)).name := by
  have hrecInfo : owner < H.recInfos.size := by
    rw [← H.generated.length]; exact howner
  let E := H.generated.entry owner howner
  let S := H.bindings.toRecursorBinderGroups H.localWF H.params owner hrecInfo
  have hnoalias : S.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  obtain ⟨D⟩ := (H.bindings.major owner hrecInfo).declarationAt H.localWF 0 (by simp)
  have Hbinder := S.majorBinderAt hnoalias D
  dsimp only at Hbinder
  rw [← E.type] at Hbinder
  have hidx : E.info.getMajorIdx = stats.params.size + (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size := by
    simp only [Lean.RecursorVal.getMajorIdx, E.numParams, E.numMotives, E.numMinors,
      E.numIndices, H.arities owner hrecInfo]
  rw [← hidx] at Hbinder
  rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, H.majorSourceType owner hrecInfo D]
  simp [Expr.abstractN_mkAppN, Expr.getAppFn_mkAppN, Expr.abstractN, Expr.getAppFn,
    Expr.constName!]

/-- A successful K check pins down the construction's signature: one family, one
constructor without fields beyond the parameters, in `Prop`. -/
theorem RecursorInstallation.kShape
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) (hk : H.kTarget = true) :
    H.generationSignature.families.size = 1 ∧
    H.generationSignature.constructors.size = 1 ∧
    (∀ owner : Fin H.generationSignature.families.size,
      H.generationSignature.families[owner].resultLevel ≈ .zero) ∧
    ∀ ctor ∈ H.generationSignature.constructors.toList, ctor.fields = [] := by
  have HK : KEligible stats indTypes true := hk ▸ H.kTargetChecked
  obtain ⟨ind, ctor, hind, hzero, hctors, harity⟩ :=
    HK.true_shape stats indTypes H.localContext
  have hfamCons : H.generationSignature.families = H.families :=
    H.generator.families
  have hsize1 : indTypes.size = 1 := by simp [hind]
  have hfam1 : H.generationSignature.families.size = 1 :=
    H.generator.familyCount.trans hsize1
  have hrec1 : H.recInfos.size = 1 := by
    rw [← H.families_size, ← hfamCons]; exact hfam1
  have h0 : 0 < H.recInfos.size := by omega
  have hminors0 : H.recInfos[0]!.minors.size = 1 := by
    rw [H.minorCounts 0 h0]; simp [hind, hctors]
  have hflat : (H.recInfos.flatMap (·.minors)).size = 1 := by
    have : ∃ r, H.recInfos = #[r] := by
      match hr : H.recInfos, hrec1 with
      | ⟨[r]⟩, _ => exact ⟨r, rfl⟩
    obtain ⟨r, hr⟩ := this
    rw [hr] at hminors0 ⊢
    simpa using hminors0
  have hctor1 : H.generationSignature.constructors.size = 1 :=
    H.generator.constructorCount.trans (H.cardinality.minors.symm.trans hflat)
  refine ⟨hfam1, hctor1, ?_, ?_⟩
  · intro owner
    have howner : owner.val < H.recInfos.size := by
      rw [← H.families_size, ← hfamCons]; exact owner.isLt
    have hlevel : H.generationSignature.families[owner].resultLevel =
        (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact howner)).resultLevel := by
      rw [← H.families_level ⟨owner.val, howner⟩]
      simp only [Fin.getElem_fin, hfamCons]
    rw [hlevel]
    exact (VLevel.equiv_congr_left
      (R.statsWF.headers.commonLevels _ (List.getElem_mem _))).2
      (ofLevel_isAlwaysZero R.statsWF.commonLevel hzero)
  · intro ct hct
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hct
    have hk0 : k = 0 := by simp only [Array.length_toList] at hk; omega
    subst hk0
    have hlocal : 0 < H.origins.minorTypes[0]!.size := by
      rw [(H.origins.minors 0 h0).size_eq, hminors0]; omega
    obtain ⟨index, -, -, -, -, ⟨O⟩⟩ := H.generator.sourceOrigins 0 h0 0 hlocal
    have hindex0 : index.val = 0 := by
      have := index.isLt
      change _ < H.generationSignature.constructors.size at this
      omega
    have hget : H.generationSignature.constructors.toList[0] =
        H.generator.signature.constructors[index] := by
      simp only [Array.getElem_toList, Fin.getElem_fin, hindex0]
      rfl
    rw [hget]
    obtain ⟨-, hlocalIdx, hsrcCtors, -, traversal, htrav, hcons, -, -, hstats, -⟩ :=
      H.minorSources.rows 0 h0 (by omega) 0 hlocal
    have htravEq : traversal = O.traversal :=
      Option.some.inj (htrav.symm.trans O.traversal_eq)
    have hSctor : (H.origins.minorShapes 0 h0 0 hlocal).constructor = ctor := by
      have hsc := (H.origins.minorShapes 0 h0 0 hlocal).sourceConstructor
      rw [hlocalIdx, hsrcCtors] at hsc
      simpa [hind, hctors] using hsc.symm
    have hA := traversal.parameterPrefix.constructorArity
      (hstats ▸ R.statsWF.paramFVars)
    have hB := traversal.fieldTelescope.constructorArity
    rw [hcons, hSctor, hstats] at hA
    have hfields0 : traversal.fields.size = 0 := by omega
    have hlen := O.fields
    rw [← htravEq, hfields0] at hlen
    exact List.eq_nil_of_length_eq_zero hlen

/-- Every installed recursor translates all non-rule metadata of the generated recursor
for its owner. -/
theorem RecursorInstallation.trMetadata
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (owner : Fin H.generationSignature.families.size) :
    ∃ rec : Lean.RecursorVal,
      (H.entries[owner.val]'(by rw [H.entries_length_eq]; exact owner.isLt)).1 = .recInfo rec ∧
      (H.entries[owner.val]'(by rw [H.entries_length_eq]; exact owner.isLt)).2 =
        H.canonicalGeneration.recursor owner ∧
      InductiveSignature.RecursorMetadata H.canonicalGeneration H.outVEnv owner rec := by
  have hi : owner.val < H.entries.length := by rw [H.entries_length_eq]; exact owner.isLt
  have hrecInfo : owner.val < H.recInfos.size := by rw [← H.generated.length]; exact hi
  have hfamCons : H.generationSignature.families = H.families :=
    H.generator.families
  let E := H.generated.entry owner.val hi
  have htarget : H.entries[owner.val].2 = H.canonicalGeneration.recursor owner := by
    rw [H.targets owner.val hi]
    unfold RecursorConstruction.recursorTarget
    rw [dif_pos owner.isLt]
    rfl
  have Htr := E.translated
  rw [htarget] at Htr
  obtain ⟨⟨_, huvars, htype⟩, hname⟩ := Htr
  refine ⟨E.info, E.source_eq, htarget, ?_⟩
  have hfamily : ∀ k (hk : k < H.generationSignature.families.size),
      H.generationSignature.families[k] =
        H.families[k]'(by rw [← hfamCons]; exact hk) := by
    intro k hk
    simp only [hfamCons]
  have hdecl : owner.val < decl.types.length := by
    rw [← H.cardinality.records]; exact hrecInfo
  refine {
    name := hname
    uvars := huvars
    type := htype.mono H.installed.le
    numParams := E.numParams.trans
      (H.cardinality.params.trans H.generator.models.nparams.symm)
    numIndices := ?_
    numMotives := ?_
    numMinors := E.numMinors.trans
      (H.cardinality.minors.trans H.generator.constructorCount.symm)
    major := ?_
    all := ?_
    isUnsafe := (H.generated_isUnsafe owner.val hi).trans
      H.generator.models.safety.symm
    k := ?_ }
  · rw [E.numIndices, ← H.arities _ hrecInfo,
      ← H.sourceIndices_length ⟨owner.val, hrecInfo⟩,
      ← H.families_indices ⟨owner.val, hrecInfo⟩, Fin.getElem_fin,
      hfamily owner.val owner.isLt]
  · rw [E.numMotives, Array.size_map, ← H.families_size, ← hfamCons]
  · rw [H.generated_getMajorInduct owner.val hi, Fin.getElem_fin,
      hfamily owner.val owner.isLt, H.families_name ⟨owner.val, hrecInfo⟩]
  · rw [E.all]
    apply List.ext_getElem
    · simp only [List.length_map, Array.length_toList, Array.size_map]
      exact H.generator.familyCount.symm
    · intro k hk₁ hk₂
      have hk : k < H.generationSignature.families.size := by simpa using hk₂
      simp only [Array.toList_map, List.getElem_map, Array.getElem_toList]
      have hk' : k < indTypes.size := by
        rw [← H.generator.familyCount]; exact hk
      have h := H.generator.familyName k hk
      rw [getElem!_pos indTypes k hk'] at h
      exact h.symm
  · intro hk
    rw [H.generated_k owner.val hi] at hk
    obtain ⟨h1, h2, h3, h4⟩ := H.kShape hk
    exact ⟨h1, h2, h3 owner, h4⟩

end VerifyInductive
end Lean4Lean
