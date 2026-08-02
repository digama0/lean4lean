import Lean4Lean.Verify.Level.Std

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

-- Finite regression coverage for the semantic assumption on opaque `Level.normalize`.
#guard samples.all fun u => valuations.all fun v =>
  Level.Semantics.eval (paramVal v) (mvarVal v) u.normalize ==
    Level.Semantics.eval (paramVal v) (mvarVal v) u

/--
info: 'Lean.Level.Semantics.isEquiv_wf' depends on axioms: [propext,
 Quot.sound,
 Level.instLawfulBEqLevel,
 Level.Semantics.eval_normalize]
-/
#guard_msgs in
#print axioms Level.Semantics.isEquiv_wf

/--
info: 'Lean.Level.Semantics.geq_wf' depends on axioms: [propext,
 Quot.sound,
 Level.instLawfulBEqLevel,
 Level.Semantics.eval_normalize]
-/
#guard_msgs in
#print axioms Level.Semantics.geq_wf
