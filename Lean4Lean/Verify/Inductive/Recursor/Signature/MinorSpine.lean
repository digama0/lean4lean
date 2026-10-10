import Lean4Lean.Verify.Inductive.Recursor.Signature.SourceReplay
import Lean4Lean.Verify.Inductive.Recursor.Construction
import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation

/-! Source telescopes of the constructor traversals recorded for each minor premise during the
minor pass of the recursor construction: each traversal's parameter tail translates to the
generator's field and result-index telescope of the matching signature constructor. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel InductiveSignature

private theorem forallSpine_of_telescope
    (H : Expr.ForallTelescope input arity residual)
    (hhead : residual.getAppFn = .const name levels) :
    Expr.ForallSpine input arity := by
  induction H with
  | nil => exact .codomain hhead
  | cons _ ih => exact .step (ih hhead)

/-- A constructor traversal ends at an application of a block family, so its field array
covers the whole forall prefix of its parameter tail. -/
theorem ConstructorFieldTraversal.sourceSpine
    (T : ConstructorFieldTraversal)
    (hconsts : checkPositivityStep.IndConstArray T.stats.levels T.stats.indConsts names)
    (hvalid : AddInductive.isValidIndApp? T.stats T.terminal = some owner) :
    Expr.ForallSpine T.parameterTail T.fields.size := by
  obtain ⟨howner, hvalid⟩ := checkPositivityStep.isValidIndApp?_some hvalid
  have howner' : owner < names.length := by
    simpa [hconsts.exact] using howner
  have hconst : T.stats.indConsts[owner]? = some (.const names[owner] T.stats.levels) := by
    simp [hconsts.exact, howner']
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead hvalid hconst
  apply forallSpine_of_telescope (name := names[owner]) (levels := T.stats.levels) T.fieldTelescope
  rw [← T.fieldClosed, Expr.getAppFn_abstractList, hhead]
  induction T.fieldFVars <;> simp_all [Expr.abstractList, Expr.abstract1]

/-- The minor at position `localIndex` of family `owner` was built from the signature
constructor at flattened offset `recursorMinorOffset indTypes owner + localIndex`: its recorded
traversal has the same owner, name and number of fields, and its parameter tail translates, in
the header environment over the parameter scope, to the constructor's field types followed by
its family application. -/
theorem RecursorConstruction.minorSourceReplay
    {isUnsafe : Bool}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (hsourceOwner : owner < indTypes.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hindex : recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let ctor := R.sourceSignatureConstructor
      ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩
    ∃ traversal, S.traversal = some traversal ∧
      ctor.owner.val = owner ∧ ctor.name = S.constructor.name ∧
      traversal.fields.size = ctor.fields.length ∧
      TrExprS R.headerVEnv c.lparams R.parameterScope traversal.parameterTail
        (VExpr.wrapForalls (R.sourceSignature.fieldTypes ctor)
          (R.sourceSignature.familyApp ctor.owner (VLevel.params R.sourceSignature.uvars)
            (vars R.sourceSignature.params.length ctor.fields.length) ctor.indices)) := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  obtain ⟨_, hlocalIndex, hsource, _, traversal, htraversal,
    hconstructor, _, _, hstats, hvalid, _⟩ :=
    H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hselected := S.sourceConstructor
  change S.localIndex = localIndex at hlocalIndex
  change S.sourceConstructors = indTypes[owner]!.ctors at hsource
  rw [hlocalIndex, hsource] at hselected
  obtain ⟨hctor, hctorEq⟩ := List.getElem?_eq_some_iff.mp hselected
  have hsourceBang : indTypes[owner]! = indTypes[owner] := by
    simp [hsourceOwner]
  have hctor' : localIndex < indTypes[owner].ctors.length := by
    simpa only [hsourceBang] using hctor
  have habstractOwner : owner < decl.types.length := by
    have hlength := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
    simp only [Array.length_toList] at hlength
    omega
  have hownerTr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    owner (by simpa using hsourceOwner) habstractOwner
  simp only [Array.getElem_toList] at hownerTr
  have habstractCtor : localIndex < decl.types[owner].ctors.length := by
    have hlength := Lean4Lean.List.Forall₂.length_eq hownerTr.ctors
    omega
  have hctorTr := List.forall₂_getElem hownerTr.ctors localIndex hctor' habstractCtor
  have hpair := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructorAtMinorOffset
    R.core owner localIndex hsourceOwner hctor habstractOwner habstractCtor hindex
  have hctorEq' : indTypes[owner].ctors[localIndex] = S.constructor := by
    simpa only [hsourceBang] using hctorEq
  have hmem : S.constructor ∈ indTypes.toList.flatMap (·.ctors) := by
    rw [← hctorEq']
    exact List.mem_flatMap.mpr ⟨indTypes[owner], by simp,
      List.getElem_mem hctor'⟩
  have hname : S.constructor.name =
      decl.ownedConstructors[recursorMinorOffset indTypes owner + localIndex].2.name := by
    rw [hpair, ← hctorEq']
    exact hctorTr.name.symm
  have hreplay := R.sourceSignature_replay_of_source
    ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩ S.constructor hmem hname
  have htranslation := hreplay.tailTranslation (residual := traversal.parameterTail) (by
    have hprefix := traversal.parameterPrefix
    simpa only [hstats, hconstructor] using hprefix)
  refine ⟨traversal, htraversal, ?_, ?_, ?_, htranslation⟩
  · exact R.sourceSignatureConstructor_owner _ owner habstractOwner (congrArg Prod.fst hpair)
  · exact (R.sourceSignatureConstructor_name _).trans hname.symm
  have hspine := traversal.sourceSpine
    (by simpa only [hstats] using H.validStats.consts)
    (by simpa only [hstats] using hvalid)
  have harity := TrExprS.forallArity_of_spine hspine htranslation
  have hresult : (R.sourceSignature.familyApp
      (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩).owner
      (VLevel.params R.sourceSignature.uvars)
      (vars R.sourceSignature.params.length
        (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩).fields.length)
      (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩).indices).forallArity = 0 := by
    apply VExpr.forallArity_eq_zero_of_getAppFnArgs
    exact VExpr.getAppFnArgs_mkApps _ _
  rw [VExpr.forallArity_wrapForalls] at harity
  change (R.sourceSignature.fieldTypes
      (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩)).length +
    (R.sourceSignature.familyApp
      (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩).owner
      (VLevel.params R.sourceSignature.uvars)
      (vars R.sourceSignature.params.length
        (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩).fields.length)
      (R.sourceSignatureConstructor ⟨recursorMinorOffset indTypes owner + localIndex, hindex⟩).indices).forallArity =
    traversal.fields.size at harity
  rw [hresult, Nat.add_zero] at harity
  exact harity.symm.trans ((List.length_map _).trans List.length_zipIdx)

end Lean4Lean.VerifyInductive
