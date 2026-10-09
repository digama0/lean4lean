import Lean4Lean.Verify.Inductive.Recursor.Context.RecInfoTraversal

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-- Per-family minor counts give the flattened minor count of the block, as used by the
executable's recursor types. -/
theorem mkRecInfos.flatMinors_size
    {recInfos : Array AddInductive.RecInfo}
    {indTypes : Array InductiveType}
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  rw [Array.size_flatMap, Array.size_flatMap]
  congr 1
  apply Array.ext
  · simp [hsize]
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    have hiRec : i < recInfos.size := by simpa using hiLeft
    have hiInd : i < indTypes.size := by omega
    have hc := hcounts i hiRec
    simpa [Array.getElem!_eq_getD, Array.getD, hiRec, hiInd] using hc

theorem ownedConstructors_length_eq_flattened_size
    (indTypes : Array InductiveType) :
    (ownedConstructors indTypes.toList).length =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  simp only [ownedConstructors, List.length_flatMap, List.length_map,
    Array.size_flatMap]
  rw [← Array.sum_toList, Array.toList_map]
  simp

/-- Number of constructors belonging to mutual families strictly before
`dIdx`. This is also the shared minor/rule state at the corresponding
iteration of `declareRecursors.loop`. -/
def recursorMinorOffset (indTypes : Array InductiveType) (dIdx : Nat) : Nat :=
  ((indTypes.toList.take dIdx).flatMap (fun type => type.ctors)).length

/-- The element of a flattening at offset (length of the first `owner` rows) `+ i` is element
`i` of row `owner`. This is the list arithmetic shared by the executable and abstract
owned-constructor enumerations. -/
theorem List.flatMap_getElem_prefix
    (rows : List α) (entries : α → List β)
    (owner i : Nat) (howner : owner < rows.length)
    (hi : i < (entries rows[owner]).length)
    (hindex : ((rows.take owner).flatMap entries).length + i <
      (rows.flatMap entries).length) :
    (rows.flatMap entries)[((rows.take owner).flatMap entries).length + i]'hindex =
      (entries rows[owner])[i]'hi := by
  have hsplit : rows = rows.take owner ++ rows[owner] ::
      rows.drop (owner + 1) := by
    calc
      rows = rows.take (owner + 1) ++ rows.drop (owner + 1) :=
        (List.take_append_drop (owner + 1) rows).symm
      _ = (rows.take owner ++ [rows[owner]]) ++
          rows.drop (owner + 1) := by
        rw [List.take_append_getElem howner]
      _ = rows.take owner ++ rows[owner] :: rows.drop (owner + 1) := by
        simp
  have hrow : entries rows[owner] =
      (entries rows[owner]).take i ++
        (entries rows[owner])[i] ::
          (entries rows[owner]).drop (i + 1) := by
    calc
      entries rows[owner] =
          (entries rows[owner]).take (i + 1) ++
            (entries rows[owner]).drop (i + 1) :=
        (List.take_append_drop (i + 1) (entries rows[owner])).symm
      _ = ((entries rows[owner]).take i ++
            [(entries rows[owner])[i]]) ++
          (entries rows[owner]).drop (i + 1) := by
        rw [List.take_append_getElem hi]
      _ = (entries rows[owner]).take i ++
          (entries rows[owner])[i] ::
            (entries rows[owner]).drop (i + 1) := by
        simp
  have houter : rows.flatMap entries =
      (rows.take owner).flatMap entries ++ entries rows[owner] ++
        (rows.drop (owner + 1)).flatMap entries := by
    simpa only [List.flatMap_append, List.flatMap_cons,
      List.append_assoc] using congrArg (List.flatMap entries) hsplit
  have hflat : rows.flatMap entries =
      ((rows.take owner).flatMap entries ++
        (entries rows[owner]).take i) ++
      (entries rows[owner])[i] ::
        ((entries rows[owner]).drop (i + 1) ++
          (rows.drop (owner + 1)).flatMap entries) := by
    calc
      rows.flatMap entries =
          (rows.take owner).flatMap entries ++ entries rows[owner] ++
            (rows.drop (owner + 1)).flatMap entries := houter
      _ = (rows.take owner).flatMap entries ++
          ((entries rows[owner]).take i ++
            (entries rows[owner])[i] ::
              (entries rows[owner]).drop (i + 1)) ++
          (rows.drop (owner + 1)).flatMap entries :=
        congrArg
          (fun xs => (rows.take owner).flatMap entries ++ xs ++
            (rows.drop (owner + 1)).flatMap entries) hrow
      _ = ((rows.take owner).flatMap entries ++
            (entries rows[owner]).take i) ++
          (entries rows[owner])[i] ::
            ((entries rows[owner]).drop (i + 1) ++
              (rows.drop (owner + 1)).flatMap entries) := by
        simp only [List.append_assoc, List.cons_append]
  exact List.getElem_of_append hflat (by
    simp [Nat.min_eq_left (Nat.le_of_lt hi)])

/-- The abstract owned-constructor enumeration uses the same owner-major,
constructor-minor order as its defining nested flattening. -/
theorem VInductDecl.ownedConstructors_getElem_prefix
    (decl : VInductDecl) (owner i : Nat)
    (howner : owner < decl.types.length)
    (hi : i < (decl.types[owner]).ctors.length)
    (hindex : ((decl.types.take owner).flatMap
      (fun type => type.ctors)).length + i < decl.ownedConstructors.length) :
    decl.ownedConstructors[
        ((decl.types.take owner).flatMap
          (fun type => type.ctors)).length + i]'hindex =
      (decl.types[owner], (decl.types[owner]).ctors[i]) := by
  have hiMapped : i <
      ((decl.types[owner]).ctors.map (decl.types[owner], ·)).length := by
    simpa using hi
  have hindexMapped :
      ((decl.types.take owner).flatMap
          (fun type => type.ctors.map (type, ·))).length + i <
        (decl.types.flatMap
          (fun type => type.ctors.map (type, ·))).length := by
    simpa [VInductDecl.ownedConstructors, List.length_flatMap] using hindex
  simpa [VInductDecl.ownedConstructors, List.length_flatMap] using
    List.flatMap_getElem_prefix decl.types
      (fun type => type.ctors.map (type, ·)) owner i howner hiMapped
      hindexMapped

/-- Translation preserves the number of constructors in every mutual-family prefix, so the
executable's running minor offset is the abstract flattening offset for the same owner. -/
theorem TrInductDeclCore.recursorMinorOffset_eq_abstract
    (H : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe decl
      envTypes envCtors)
    (owner : Nat) (howner : owner ≤ indTypes.size) :
    recursorMinorOffset indTypes owner =
      ((decl.types.take owner).flatMap
        (fun type => type.ctors)).length := by
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
    have hsourceOwner : owner < indTypes.size := by omega
    have htypes : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length H
    have habstractOwner : owner < decl.types.length := by omega
    have hsourceList : owner < indTypes.toList.length := by
      simpa only [Array.length_toList] using hsourceOwner
    have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt H owner
      hsourceList habstractOwner
    unfold recursorMinorOffset at ih ⊢
    rw [← List.take_append_getElem hsourceList]
    rw [← List.take_append_getElem habstractOwner]
    simp only [List.flatMap_append, List.flatMap_singleton, List.length_append]
    rw [ih (by omega)]
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using
      Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Howner

/-- The abstract owned constructor at the executable's minor offset of family `owner` plus `i`
is constructor `i` of family `owner`. This identifies the translations of the generated
equations with the specification's iota rules pointwise. -/
theorem TrInductDeclCore.ownedConstructorAtMinorOffset
    (H : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe decl
      envTypes envCtors)
    (owner i : Nat) (howner : owner < indTypes.size)
    (hi : i < indTypes[owner]!.ctors.length)
    (habstractOwner : owner < decl.types.length)
    (habstractCtor : i < (decl.types[owner]'habstractOwner).ctors.length)
    (hindex : recursorMinorOffset indTypes owner + i <
      decl.ownedConstructors.length) :
    decl.ownedConstructors[recursorMinorOffset indTypes owner + i]'hindex =
      (decl.types[owner]'habstractOwner,
        (decl.types[owner]'habstractOwner).ctors[i]'habstractCtor) := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length H
  let Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt H owner
    (by simpa using howner) habstractOwner
  have habstractCtor' : i < (decl.types[owner]).ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Howner]
    simpa [Array.getElem!_eq_getD, Array.getD, howner] using hi
  have hoffset :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.recursorMinorOffset_eq_abstract
      H owner (Nat.le_of_lt howner)
  have habstractIndex :
      ((decl.types.take owner).flatMap
        (fun type => type.ctors)).length + i <
        decl.ownedConstructors.length := by
    simpa [hoffset] using hindex
  simpa [hoffset] using
    Lean4Lean.VerifyInductive.VInductDecl.ownedConstructors_getElem_prefix
      decl owner i habstractOwner habstractCtor' habstractIndex

theorem recursorMinorOffset_step
    (indTypes : Array InductiveType) (dIdx : Nat)
    (hidx : dIdx < indTypes.size) :
    recursorMinorOffset indTypes (dIdx + 1) =
      recursorMinorOffset indTypes dIdx + indTypes[dIdx]!.ctors.length := by
  simp [recursorMinorOffset, List.take_add_one, hidx,
    List.length_flatMap]

theorem recursorMinorOffset_mono
    (indTypes : Array InductiveType) (a b : Nat)
    (hab : a ≤ b) (hb : b ≤ indTypes.size) :
    recursorMinorOffset indTypes a ≤
      recursorMinorOffset indTypes b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases heq : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a ≤ b := by omega
        have hb' : b ≤ indTypes.size := by omega
        have hidx : b < indTypes.size := by omega
        calc
          recursorMinorOffset indTypes a ≤
              recursorMinorOffset indTypes b := ih a hab' hb'
          _ ≤ recursorMinorOffset indTypes (b + 1) := by
            rw [recursorMinorOffset_step indTypes b hidx]
            omega

theorem recursorMinorOffset_le_total
    (indTypes : Array InductiveType) (dIdx : Nat) :
    recursorMinorOffset indTypes dIdx ≤
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
  let pre := (indTypes.toList.take dIdx).flatMap (fun type => type.ctors)
  let suffix := (indTypes.toList.drop dIdx).flatMap (fun type => type.ctors)
  have hsplit : pre ++ suffix =
      indTypes.toList.flatMap (fun type => type.ctors) := by
    simp only [pre, suffix, ← List.flatMap_append,
      List.take_append_drop]
  change pre.length ≤ _
  rw [← hsplit, List.length_append]
  omega

theorem recursorMinorOffset_room
    (indTypes : Array InductiveType) (dIdx : Nat)
    (hidx : dIdx < indTypes.size) :
    recursorMinorOffset indTypes dIdx + indTypes[dIdx]!.ctors.length ≤
      (indTypes.toList.flatMap (fun type => type.ctors)).length := by
  rw [← recursorMinorOffset_step indTypes dIdx hidx]
  exact recursorMinorOffset_le_total indTypes (dIdx + 1)

theorem mkRecInfos.motives_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (hsize : recInfos.size = indTypes.size) :
    (recInfos.map (·.motive)).size = decl.types.length := by
  simp only [Array.size_map]
  rw [hsize]
  simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl

theorem mkRecInfos.flatMinors_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size = decl.ownedConstructors.length := by
  rw [mkRecInfos.flatMinors_size hsize hcounts,
    ← ownedConstructors_length_eq_flattened_size]
  exact Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl

/-- The counts of the recursor construction: numbers of families, parameters, motives, minors
and indices agree with the abstract declaration. They are established before the generated
telescope is translated. -/
structure RecursorCounts
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (decl : VInductDecl) : Prop where
  records : recInfos.size = decl.types.length
  families : stats.indConsts.size = decl.types.length
  params : stats.params.size = decl.nparams
  motives : (recInfos.map (·.motive)).size = decl.types.length
  minors : (recInfos.flatMap (·.minors)).size =
    decl.ownedConstructors.length
  indices : ∀ i (hi : i < recInfos.size),
    recInfos[i]!.indices.size =
      (decl.types[i]'(by simpa [records] using hi)).numIndices

theorem RecursorCounts.ofResult
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.HeaderStatsWF
        headerEnv lparams Δ stats decl depth)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (harities : ∀ i, i < recInfos.size →
      recInfos[i]!.indices.size = stats.nindices[i]!) :
    RecursorCounts stats recInfos decl where
  records := hsize.trans (by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl)
  families := by
    exact
      (checkPositivityStep.ValidAppStatsWF.ofHeaderStats
        Hmaterialized).types_size
  params := by
    have hlen := List.Forall₂.length_eq
      Hmaterialized.suffixParams
    simpa [VInductDecl.paramVars] using hlen
  motives := mkRecInfos.motives_size_of_translation Hdecl hsize
  minors := mkRecInfos.flatMinors_size_of_translation Hdecl hsize hcounts
  indices := by
    let Hstats :=
      checkPositivityStep.ValidAppStatsWF.ofHeaderStats Hmaterialized
    intro i hi
    have hiDecl : i < decl.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl]
      simpa [hsize] using hi
    have hn := Hstats.nindicesAt hiDecl
    have hstats : stats.nindices[i]! = decl.types[i].numIndices := by
      obtain ⟨hstatsBound, hnget⟩ := Array.getElem?_eq_some_iff.mp hn
      simpa [Array.getElem!_eq_getD, Array.getD, hstatsBound] using hnget
    exact (harities i hi).trans hstats

end VerifyInductive
end Lean4Lean
