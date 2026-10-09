import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.RecursorEquationCoverage

/-! Recursor metadata (`RecursorData`, used by singleton reconstruction) comes from an actual
finite compilation whose whole generated block is installed below the current environment
(`RecursorRegistered`). Compilation may precede installation (`CompiledInductive.mono`).
Abstract case metadata is independent of this. -/

namespace Lean4Lean
open InductiveSignature

/-- A compiled inductive retains the actual compilation at its own base. It
never asserts that lowering-only names remain fresh at the installation base. -/
theorem CompiledInductive.exists_compilation
    (compiled : CompiledInductive installBase source block) :
    ∃ (base : VEnv) (expanded : VInductDecl) (signature : InductiveSignature)
      (generated : Instance signature) (auxiliaries : List ContainerSpecialization),
      base ≤ installBase ∧
      CompilationData base source expanded signature generated auxiliaries block ∧
      ContainersInstalled base auxiliaries := by
  exact CompiledInductive.rec
    (motive_1 := fun installBase source block _ =>
      ∃ (base : VEnv) (expanded : VInductDecl) (signature : InductiveSignature)
        (generated : Instance signature) (auxiliaries : List ContainerSpecialization),
        base ≤ installBase ∧
        CompilationData base source expanded signature generated auxiliaries block ∧
        ContainersInstalled base auxiliaries)
    (motive_2 := fun _ _ _ => True)
    (fun compilation specializations _ => ⟨_, _, _, _, _, .rfl, compilation, specializations⟩)
    (fun _ below _ ih => by
      obtain ⟨base, expanded, signature, generated, auxiliaries, earlier, compilation, specializations⟩ := ih
      exact ⟨base, expanded, signature, generated, auxiliaries, earlier.trans below,
        compilation, specializations⟩)
    trivial (fun _ _ _ _ _ _ _ => trivial) compiled

end Lean4Lean

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The recursor metadata `data` is that of an actual finite compilation whose whole generated
block is installed below `env`. -/
def RecursorRegistered (env : VEnv) (data : RecursorData) : Prop :=
  ∃ base installBase source expanded, ∃ (g : Instance data.schema.signature), ∃ auxiliaries block installed,
    CompilationData base source expanded data.schema.signature g auxiliaries block ∧
    ContainersInstalled base auxiliaries ∧
    base ≤ installBase ∧
    data.schema.restoration = compilationRestoration source auxiliaries ∧
    data.schema.sourceFamilies = source.types.map (·.name) ∧
    data.uvars = g.uvars ∧ data.levels = g.levels ∧ data.target = g.targetLevel ∧
    block.install installBase = some installed ∧ installed ≤ env

/-- The singleton replay equation is taken from the actual installed finite
block, with the compilation instance's universe packing and generated names. -/
theorem RecursorRegistered.singletonEquation
    (H : RecursorRegistered env data)
    (hgen : data.singletonEquation = some equation) : env.defeqs equation := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinstance : data.recursorInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [RecursorData.recursorInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  have every (index : Fin data.schema.signature.constructors.size)
      (hg : (compilationRestoration source auxiliaries).equation (g.equation index) = some equation) :
      env.defeqs equation := by
    have hgenerated : g.equation index ∈ g.equations :=
      List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
    obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      (List.mapM_eq_some.mp hdata.equations) _ hgenerated
    have heq : actual = equation := Option.some.inj (hrestore.symm.trans hg)
    rw [← heq]
    exact he.defeqs (VInductBlock.install_rule hi hmem)
  unfold RecursorData.singletonEquation at hgen
  dsimp only at hgen
  split at hgen <;> try contradiction
  rw [hinstance, hr] at hgen
  exact every _ hgen

/-- The recursor type computed from the metadata is exactly the type of its
installed recursor, selected from the same finite compilation instance. -/
theorem RecursorRegistered.recursorType
    (H : RecursorRegistered env data)
    (hgen : data.recursorType = some type) :
    env.constants data.name = some { uvars := data.uvars, type := type } := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinstance : data.recursorInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [RecursorData.recursorInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  have hgenerated : g.recursor data.owner ∈ g.recursors :=
    List.mem_map.mpr ⟨data.owner, List.mem_finRange _, rfl⟩
  obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.recursors) _ hgenerated
  have htarget : (compilationRestoration source auxiliaries).expr
      (g.recursorType data.owner) = some type := by
    simpa only [RecursorData.recursorType, hinstance, hr] using hgen
  have hexact : actual = { name := data.name, uvars := data.uvars, type := type } := by
    simp only [Restoration.recursor, Instance.recursor, htarget] at hrestore
    have heq := Option.some.inj hrestore
    rw [← heq]
    simp only [RecursorData.name, hr, hdata.recursorNames, hu]
  rw [hexact] at hmem
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hi
  obtain ⟨types, _, ctors, _, recursors, hrecursors, rfl⟩ := hi
  exact he.constants ((VEnv.addDefEqRules_le).constants
    (VEnv.addConstVals_get hrecursors hmem))

/-- Scope comes from the actual installed recursor's well-formed type. -/
theorem RecursorRegistered.recursorType_closed (henv : env.WF)
    (H : RecursorRegistered env data) (hgen : data.recursorType = some type) :
    type.Closed := by
  obtain ⟨_, htype⟩ := henv.ordered.constWF (H.recursorType hgen)
  exact VExpr.WF.closedN henv.ordered ⟨_, htype⟩ (by trivial)

end Lean4Lean.VEnv

namespace Lean4Lean.VLevel

/-- At well-scoped universes, evaluation at positive parameters detects
whether a level is identically zero. -/
theorem zero_of_eval_ones {level : VLevel} (hw : level.WF count)
    (hzero : level.eval (List.replicate count 1) = 0) : level ≈ .zero := by
  induction level with
  | zero => rfl
  | succ l ih => simp [eval] at hzero
  | param i =>
    have hi : i < count := hw
    simp [eval, List.getD_eq_getElem?_getD, hi] at hzero
  | max a b iha ihb =>
    have hz : a.eval (List.replicate count 1) = 0 ∧ b.eval (List.replicate count 1) = 0 := by
      exact ⟨Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left ..) (Nat.le_of_eq hzero)),
        Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right ..) (Nat.le_of_eq hzero))⟩
    exact (max_congr (iha hw.1 hz.1) (ihb hw.2 hz.2)).trans (by rfl)
  | imax a b iha ihb =>
    have hz : b.eval (List.replicate count 1) = 0 := by
      simp only [eval, Lean.Nat.imax] at hzero
      split at hzero
      · assumption
      · exact Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right ..) (Nat.le_of_eq hzero))
    exact imax_eq_zero.mpr (ihb hw.2 hz)

end Lean4Lean.VLevel

namespace Lean4Lean.VEnv
open InductiveSignature

theorem RecursorRegistered.small_target
    (H : RecursorRegistered env data) (hsmall : data.largeTarget = false) :
    data.target ≈ .zero := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hi, he⟩ := H
  have hw : data.target.WF data.uvars := by
    rw [hu, ht]
    obtain ⟨_, _, hadmissible⟩ := hdata.admissible
    exact hadmissible.target_wf
  apply VLevel.zero_of_eval_ones hw
  simpa only [RecursorData.largeTarget, bne_eq_false_iff_eq] using hsmall

end Lean4Lean.VEnv
