import Lean4Lean.Verify.LevelStd

open Lean

private def p : Level := .param `p
private def q : Level := .param `q
private def m : Level := .mvar ⟨`m⟩
private def n : Level := .mvar ⟨`n⟩

private def atoms : Array Level := #[.zero, p, q, m, n]

private def levels : Nat → Array Level
  | 0 => atoms
  | n + 1 =>
    let xs := levels n
    xs ++ xs.map .succ ++ xs.flatMap fun a =>
      xs.flatMap fun b => #[.max a b, .imax a b]

private def sampleEvery (step : Nat) : Nat → List Level → List Level
  | _, [] => []
  | i, u :: us =>
    if i % step == 0 then u :: sampleEvery step (i + 1) us
    else sampleEvery step (i + 1) us

private def generatedSamples : Array Level :=
  (sampleEvery 12 0 (levels 2).toList).toArray

-- Exercise the offset boundaries used when normalization drops explicit levels
-- or deduplicates levels with the same base.
private def trickySamples : Array Level := #[
  .max (.succ .zero) (.succ p),
  .max (.succ (.succ .zero)) (.succ p),
  .max (.succ (.succ .zero)) (.succ (.succ p)),
  .max (.succ (.succ (.succ .zero))) (.succ (.succ p)),
  .max (.succ p) (.succ (.succ p)),
  .max (.succ (.succ p)) (.succ p),
  .max (.max (.succ (.succ .zero)) (.succ q)) (.succ (.succ p)),
  .succ (.max (.succ (.succ .zero)) (.imax p (.succ q))),
  .imax (.succ (.succ p)) (.max (.succ (.succ .zero)) q)]

private def samples := generatedSamples ++ trickySamples

private def valuations : Array (Nat × Nat × Nat × Nat) := #[
  (0, 0, 0, 0), (0, 1, 0, 1), (1, 0, 1, 0),
  (1, 1, 1, 1), (2, 5, 3, 7), (5, 2, 7, 3)]

private def paramVal (v : Nat × Nat × Nat × Nat) : Name → Nat
  | `p => v.1
  | `q => v.2.1
  | _ => 0

private def mvarVal (v : Nat × Nat × Nat × Nat) : LMVarId → Nat
  | ⟨`m⟩ => v.2.2.1
  | ⟨`n⟩ => v.2.2.2
  | _ => 0

-- Finite regression coverage for `Level.Semantics.eval_normalize`.
#guard samples.all fun u => valuations.all fun v =>
  Level.eval (paramVal v) (mvarVal v) u.normalize ==
    Level.eval (paramVal v) (mvarVal v) u

-- Finite regression coverage for `Level.normalize_eq`: exhaustive over the 7320 levels of depth
-- at most 2 over `atoms`, plus 28920 depth-3 levels built from a sample of them.
private def deeperSamples : Array Level :=
  let sample := (levels 2).zipIdx.filterMap fun (u, i) => if i % 61 == 0 then some u else none
  sample.map .succ ++ sample.flatMap fun a =>
    (levels 1).flatMap fun b => #[.max a b, .imax a b, .max b a, .imax b a]

#guard (levels 2).all fun u => u.normalize == Level.Total.normalize u
#guard deeperSamples.all fun u => u.normalize == Level.Total.normalize u

/--
info: 'Lean.Level.isEquiv_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq]
-/
#guard_msgs in #print axioms Level.isEquiv_wf

/--
info: 'Lean.Level.geq_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq]
-/
#guard_msgs in #print axioms Level.geq_wf
