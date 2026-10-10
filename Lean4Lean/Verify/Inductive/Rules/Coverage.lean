import Lean4Lean.Verify.Inductive.Rules.EquationWF
import Lean4Lean.Verify.Inductive.Rules.LhsTranslation
import Lean4Lean.Verify.Inductive.Recursor.Metadata
import Lean4Lean.Verify.Inductive.Rules.Translation

/-! # Rule coverage and equation well-formedness of the recursor installation

Assembly of the rule translations over the recursor installation (source branch:
`Rules/RuleTranslations.lean`). Given the translation of each installed rule's closed
right-hand side to the generator's equation right-hand side (`RuleRhsTranslations`, supplied by
`RecursorInstallation.ruleRhsTranslations` of `Rules/Translation.lean`):

* every installed recursor's rules are, in order, the generated equations of the constructors
  its owner owns (`RecursorInstallation.rulesCovered`), which the recursor phase uses to build
  the `TrRecursor`s of `RecursorCheck`;
* the generated equations are well formed in the recursor stage
  (`RecursorInstallation.equationsWF'`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! ### List arithmetic -/

theorem RuleAssembly.filter_range_interval (a b : Nat) :
    ∀ n, (List.range n).filter (fun k => decide (a ≤ k ∧ k < b)) =
      List.range' a (min b n - a) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : a ≤ n ∧ n < b
    · have h1 : min b n = n := by omega
      have h2 : min b (n + 1) - a = (n - a) + 1 := by omega
      rw [h1, h2, List.range'_concat]
      simp [h]
    · have h2 : min b (n + 1) - a = min b n - a := by omega
      rw [h2]
      simp [h]

theorem RuleAssembly.filter_finRange_map_val {n : Nat} (p : Fin n → Bool) (a b : Nat)
    (hp : ∀ k : Fin n, p k = true ↔ a ≤ k.val ∧ k.val < b) :
    ((List.finRange n).filter p).map Fin.val =
      (List.range n).filter (fun k => decide (a ≤ k ∧ k < b)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.filter_append, List.map_append, List.range_succ,
      List.filter_append]
    have hcast : ((List.map Fin.castSucc (List.finRange n)).filter p).map Fin.val =
        ((List.finRange n).filter (p ∘ Fin.castSucc)).map Fin.val := by
      rw [List.filter_map, List.map_map]
      rfl
    rw [hcast, ih (p ∘ Fin.castSucc) (fun k => by simpa using hp k.castSucc)]
    congr 1
    have hl := hp (Fin.last n)
    simp only [Fin.val_last] at hl
    by_cases h : a ≤ n ∧ n < b
    · simp [h, hl.mpr h]
    · have : p (Fin.last n) = false := by
        cases hpl : p (Fin.last n)
        · rfl
        · exact absurd (hl.mp hpl) h
      simp [h, this]

theorem RuleAssembly.getElem_of_map_val_eq {n : Nat} {l : List (Fin n)} {a m : Nat}
    (h : l.map Fin.val = List.range' a m) (j : Nat) (hj : j < l.length) :
    (l[j]).val = a + j := by
  have hj' : j < (l.map Fin.val).length := by simpa using hj
  have := List.getElem_of_eq h hj'
  simpa using this

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The input of `ruleTranslation_of`: every installed rule's closed right-hand side
translates to the generator's equation right-hand side at its flattened
constructor position. -/
def RecursorInstallation.RuleRhsTranslations
    (H : RecursorInstallation R outEnv) : Prop :=
  ∀ owner (howner : owner < H.entries.length) (i : Nat)
    (hi : i < (H.generated.entry owner howner).info.rules.length)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size),
    TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      ((H.generated.entry owner howner).info.rules[i]).rhs
      (H.canonicalGeneration.equation ⟨recursorMinorOffset indTypes owner + i, hk⟩).rhs

/-- The generator body translations follow from the closed RHS translations. -/
theorem RecursorInstallation.equationBodyTranslations_of
    (H : RecursorInstallation R outEnv) (Hrhs : H.RuleRhsTranslations) :
    H.EquationBodyTranslations := by
  intro owner howner i hctor hk
  rcases H.ruleAlignment owner howner i hctor with ⟨A⟩
  exact ⟨A, A.equationBodyTranslationsOfClosedRhs hk
    (Hrhs owner howner i A.sourceRule_lt hk)⟩

theorem RecursorInstallation.recInfos_size_eq_source
    (H : RecursorInstallation R outEnv) :
    H.recInfos.size = indTypes.size := H.sourceFamilyCount

theorem RecursorInstallation.constructors_size_offset
    (H : RecursorInstallation R outEnv) :
    H.generationSignature.constructors.size = recursorMinorOffset indTypes indTypes.size := by
  change H.generator.signature.constructors.size = _
  rw [H.generator.constructorCount]
  exact H.toRecursorConstruction.ownedConstructors_length_offset

/-- The generated constructor at a flattened source position is owned by that
position's family. -/
theorem RecursorInstallation.generatedConstructor_owner
    (H : RecursorInstallation R outEnv)
    (owner : Nat) (howner : owner < indTypes.size)
    (l : Nat) (hl : l < indTypes[owner]!.ctors.length)
    (hk : recursorMinorOffset indTypes owner + l < H.generationSignature.constructors.size) :
    (H.generationSignature.constructors[recursorMinorOffset indTypes owner + l]).owner.val =
      owner := by
  have hrec : owner < H.recInfos.size := by rw [H.recInfos_size_eq_source]; exact howner
  have hlocal : l < H.origins.minorTypes[owner]!.size := by
    rw [H.toRecursorConstruction.minorTypes_size owner hrec]; exact hl
  obtain ⟨index, hindex, hown, -, -, -⟩ := H.generator.sourceOrigins owner hrec l hlocal
  have : H.generationSignature.constructors[recursorMinorOffset indTypes owner + l] =
      H.generator.signature.constructors[index] := by
    simp only [Fin.getElem_fin, hindex]; rfl
  rw [this]; exact hown

theorem RecursorInstallation.ownedConstructors_length_eq
    (H : RecursorInstallation R outEnv) :
    decl.ownedConstructors.length = H.generationSignature.constructors.size := by
  change _ = H.generator.signature.constructors.size
  rw [H.generator.constructorCount]

/-- The installed rule names the generated constructor at its flattened
position. -/
theorem RecursorInstallation.RuleAlignment.ruleCtor_eq
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size) :
    ((H.generated.entry owner howner).info.rules[i]'A.sourceRule_lt).ctor =
      (H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).name := by
  have hindex : recursorMinorOffset indTypes owner + i < decl.ownedConstructors.length := by
    rw [H.ownedConstructors_length_eq]; exact hk
  have hpair := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructorAtMinorOffset R.core
    owner i A.sourceOwner_lt hctor A.abstractOwner_lt A.abstractCtor_lt hindex
  have horder := List.forall₂_getElem H.generator.constructorOrder
    (recursorMinorOffset indTypes owner + i) (by rw [Array.length_toList]; exact hk) hindex
  rw [hpair] at horder
  have hname := horder.2
  simp only [Array.getElem_toList] at hname
  rw [A.rule.ctor_eq]
  have hsource : indTypes[owner]!.ctors[i].name =
      ((decl.types[owner]'A.abstractOwner_lt).ctors[i]'A.abstractCtor_lt).name := by
    simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using
      A.ctorTranslation.name.symm
  exact hsource.trans hname.symm

/-- The installed rule's field count is the generated constructor's. -/
theorem RecursorInstallation.RuleAlignment.ruleNFields_eq
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (hk : recursorMinorOffset indTypes owner + i < H.generationSignature.constructors.size) :
    ((H.generated.entry owner howner).info.rules[i]'A.sourceRule_lt).nfields =
      (H.generationSignature.constructors[recursorMinorOffset indTypes owner + i]).fields.length := by
  obtain ⟨_, -, hnf⟩ := A.generatedConstructor
  rw [A.rule.fields_eq, hnf]

/-- The generated constructors owned by a family form the contiguous block of
its source constructors. -/
theorem RecursorInstallation.ownedConstructors_map_val
    (H : RecursorInstallation R outEnv)
    (o : Fin H.generationSignature.families.size) (howner : o.val < H.entries.length) :
    (H.generationSignature.ownedConstructors o).map Fin.val =
      List.range' (recursorMinorOffset indTypes o.val)
        (H.generated.entry o.val howner).info.rules.length := by
  have hrec : o.val < H.recInfos.size := by rw [← H.generated.length]; exact howner
  have hsrc : o.val < indTypes.size := by rw [← H.recInfos_size_eq_source]; exact hrec
  have hcnt : (H.generated.entry o.val howner).info.rules.length =
      indTypes[o.val]!.ctors.length := (H.generated.entry o.val howner).rules.length
  have htotal : recursorMinorOffset indTypes o.val + indTypes[o.val]!.ctors.length ≤
      H.generationSignature.constructors.size := by
    rw [H.constructors_size_offset, ← recursorMinorOffset_step indTypes o.val hsrc]
    exact recursorMinorOffset_mono indTypes _ _ (by omega) (Nat.le_refl _)
  unfold InductiveSignature.ownedConstructors
  rw [RuleAssembly.filter_finRange_map_val _ (recursorMinorOffset indTypes o.val)
      (recursorMinorOffset indTypes o.val + indTypes[o.val]!.ctors.length),
    RuleAssembly.filter_range_interval, hcnt]
  · congr 1; omega
  intro k
  have hk' : k.val < decl.ownedConstructors.length := by
    rw [H.ownedConstructors_length_eq]; exact k.isLt
  obtain ⟨o', hrec', l', hlocal', hkEq⟩ :=
    H.toRecursorConstruction.flatMinorIndex k.val hk'
  have hsrc' : o' < indTypes.size := by rw [← H.recInfos_size_eq_source]; exact hrec'
  have hl' : l' < indTypes[o']!.ctors.length := by
    rw [← H.toRecursorConstruction.minorTypes_size o' hrec']; exact hlocal'
  have hk2 : recursorMinorOffset indTypes o' + l' < H.generationSignature.constructors.size :=
    hkEq ▸ k.isLt
  have hown := H.generatedConstructor_owner o' hsrc' l' hl' hk2
  have hown' : (H.generationSignature.constructors[k]).owner.val = o' := by
    have : H.generationSignature.constructors[k] =
        H.generationSignature.constructors[recursorMinorOffset indTypes o' + l'] := by
      simp only [Fin.getElem_fin, hkEq]
    rw [this]; exact hown
  rw [beq_iff_eq, Fin.ext_iff, hown']
  constructor
  · rintro rfl
    omega
  · rintro ⟨h1, h2⟩
    have hu := recursorMinorOffset_unique indTypes hsrc' hsrc hl'
      (show k.val - recursorMinorOffset indTypes o.val < indTypes[o.val]!.ctors.length by omega)
      (by omega)
    exact hu.1

/-- Rule coverage of one installed recursor against the canonical generation. -/
theorem RecursorInstallation.trRules
    (H : RecursorInstallation R outEnv) (Hrhs : H.RuleRhsTranslations)
    (o : Fin H.generationSignature.families.size) (howner : o.val < H.entries.length) :
    List.Forall₂ (InductiveSignature.TrRecursorRule H.canonicalGeneration H.outVEnv
        (H.generated.entry o.val howner).info.levelParams)
      (H.generationSignature.ownedConstructors o) (H.generated.entry o.val howner).info.rules := by
  have hmap := H.ownedConstructors_map_val o howner
  have hlen : (H.generationSignature.ownedConstructors o).length =
      (H.generated.entry o.val howner).info.rules.length := by
    have := congrArg List.length hmap
    simpa using this
  apply List.forall₂_of_getElem hlen
  intro j hj hj'
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  have hctor : j < indTypes[o.val]!.ctors.length := by
    rw [← (H.generated.entry o.val howner).rules.length]; exact hj'
  rcases H.ruleAlignment o.val howner j hctor with ⟨A⟩
  have hk : recursorMinorOffset indTypes o.val + j < H.generationSignature.constructors.size :=
    hval ▸ (H.generationSignature.ownedConstructors o)[j].isLt
  have hfin : (H.generationSignature.ownedConstructors o)[j] =
      ⟨recursorMinorOffset indTypes o.val + j, hk⟩ := Fin.ext hval
  rw [hfin]
  have hlevels : (H.generated.entry o.val howner).info.levelParams =
      AddInductive.getRecLevelParams H.elimLevel c.lparams := by
    rw [(H.generated.entry o.val howner).levels, H.localExtends.lparams_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact A.ruleCtor_eq hk
  · exact A.ruleNFields_eq hk
  · rw [hlevels]
    exact Hrhs o.val howner j hj' hk

/-- The rule coverage of the installation: each installed kernel recursor's rules are, in
order, the generated equations of the constructors its owner owns. -/
theorem RecursorInstallation.rulesCovered (H : RecursorInstallation R outEnv) :
    List.Forall₂ (fun (owner : Fin H.generationSignature.families.size)
        (e : ConstantInfo × VConstVal) =>
      ∃ rval, e.1 = .recInfo rval ∧
        List.Forall₂ (InductiveSignature.TrRecursorRule H.generationInstance H.outVEnv
          rval.levelParams) (H.generationSignature.ownedConstructors owner) rval.rules)
      (List.finRange H.generationSignature.families.size) H.entries := by
  apply List.forall₂_of_getElem (by simp [H.entries_length_eq])
  intro j hj hj'
  have hjf : j < H.generationSignature.families.size := by simpa using hj
  have hfin : (List.finRange H.generationSignature.families.size)[j] = ⟨j, hjf⟩ := by simp
  rw [hfin]
  exact ⟨_, (H.generated.entry j hj').source_eq,
    H.trRules H.ruleRhsTranslations ⟨j, hjf⟩ hj'⟩

/-- The generated equations are well formed in the recursor stage. -/
theorem RecursorInstallation.equationsWF' (H : RecursorInstallation R outEnv) :
    ∀ df ∈ H.generationInstance.equations, df.WF H.outVEnv :=
  H.equationsWF (H.equationBodyTranslations_of H.ruleRhsTranslations)

end
end VerifyInductive
end Lean4Lean
