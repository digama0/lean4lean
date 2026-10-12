import Lean4Lean.Verify.Inductive.Nested.Lowering.AuxiliaryFamilyPositions

/-! # One queued family per cache entry

Every auxiliary generation step pushes one family onto the queue and one entry onto the cache,
and nothing else changes either array's size, so the queue is the source block followed by one
family per cache entry (`NestedLowering.resultTypes_length`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The queue holds `initialSize` families plus one per cache entry. -/
def SizeBalanced (initialSize : Nat) (state : ElimNestedInductive.State) : Prop :=
  state.newTypes.size = initialSize + state.nestedAux.size

theorem AuxiliaryGenerationStep.sizeBalanced
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  unfold SizeBalanced at *
  rw [hstate]
  simp only [Array.size_push]
  omega

theorem AuxiliaryGenerationBatch.sizeBalanced
    (H : AuxiliaryGenerationBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  induction H with
  | nil => exact Hs
  | cons Hstep _ ih => exact ih (Hstep.sizeBalanced Hs)

theorem OccurrenceReplacement.sizeBalanced
    (H : OccurrenceReplacement env lctx params As targetName levels args
      value state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  cases H with
  | cached => exact Hs
  | generated _ Hbatch => exact Hbatch.sizeBalanced Hs

theorem NodeReplacement.sizeBalanced
    (H : NodeReplacement env lctx params As input state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  cases H with
  | unrecognized => exact Hs
  | recognized _ _ Hrecognized => exact Hrecognized.sizeBalanced Hs

theorem ExprLowering.sizeBalanced
    (H : ExprLowering env lctx params As input state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  induction H with
  | occurrence Hnode => exact Hnode.sizeBalanced Hs
  | bvar | fvar | mvar | sort | const | lit => exact Hs
  | app Hnode _ _ ihFn ihArg => exact ihArg (ihFn (Hnode.sizeBalanced Hs))
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact ihBody (ihDom (Hnode.sizeBalanced Hs))
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.sizeBalanced Hs)))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody => exact ihBody (Hnode.sizeBalanced Hs)

theorem ConstructorLowering.sizeBalanced
    (H : ConstructorLowering env params nparams source state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, hopenedTypes, hopenedAux, _, _,
      Hreplace, _⟩
  apply Hreplace.sizeBalanced
  unfold SizeBalanced at *
  rw [hopenedTypes, hopenedAux]
  exact Hs

theorem ConstructorLowerings.sizeBalanced
    (H : ConstructorLowerings env params nparams sources state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  induction H with
  | nil => exact Hs
  | cons Hhead _ ih => exact ih (Hhead.sizeBalanced Hs)

theorem LowerNextStep.sizeBalanced
    (H : LowerNextStep env params nparams i state (some source, nextState))
    (Hs : SizeBalanced k state) : SizeBalanced k nextState := by
  cases H with
  | step hi Hlowered =>
    have H' := Hlowered.constructors.sizeBalanced Hs
    unfold SizeBalanced at *
    simpa [Array.size_set!] using H'

theorem LoweringQueue.sizeBalanced
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hs : SizeBalanced k state) : SizeBalanced k out.2 := by
  induction H with
  | done => exact Hs
  | step Hnext _ ih => exact ih (Hnext.sizeBalanced Hs)

/-- Inserting distinct keys into an empty tree map gives one entry per key. -/
theorem nestedAuxFold_size (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnodup : (entries.map Prod.snd).Nodup)
    (hfresh : ∀ entry ∈ entries, entry.2 ∉ map) :
    (entries.foldl (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) map).size =
      map.size + entries.length := by
  induction entries generalizing map with
  | nil => simp
  | cons entry entries ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.foldl_cons, List.length_cons]
    rw [ih _ hnodup.2]
    · have hnot : map.contains entry.2 = false := by
        exact Bool.eq_false_iff.mpr fun h =>
          hfresh entry (by simp) (Std.TreeMap.contains_iff_mem.mp h)
      rw [Std.TreeMap.size_insert, hnot]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · intro e he hmem
      rw [Std.TreeMap.mem_insert] at hmem
      rcases hmem with heq | hmem
      · apply hnodup.1
        have : entry.2 = e.2 := Std.LawfulEqCmp.eq_of_compare heq
        rw [this]
        exact List.mem_map.mpr ⟨e, he, rfl⟩
      · exact hfresh e (by simp [he]) hmem

end VerifyInductive
end Lean4Lean
