import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! Recursor metadata (`RecursorData`, used by singleton reconstruction) comes from an actual
finite compilation of a declaration added below the current environment
(`RecursorRegistered`): the declaration is well formed and `VEnv.addInduct` installs it, its
recursors and rules being read off the compiled block (`VInductDecl.RecsOf`). The generated
equations are not stored: each is registered as the ι pattern of its recursor rule
(`VEnv.addRecRule`), which `RecursorRegistered.singletonEquation` recovers. Compilation may
precede installation (`CompiledInductive.mono`). -/

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
    trivial (fun _ _ _ _ _ _ _ _ => trivial) compiled

end Lean4Lean

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The recursor metadata `data` is that of an actual finite compilation of a declaration
`source` that `VEnv.addInduct` installs below `env`, its recursors and rules read off the
compiled `block` (`VInductDecl.RecsOf`). It records the block's typing `block.WF installBase`,
which confluence reads through `IsDefEq.uniq`. -/
def RecursorRegistered (env : VEnv) (data : RecursorData) : Prop :=
  ∃ base installBase source expanded, ∃ (g : Instance data.schema.signature), ∃ auxiliaries block installed,
    CompilationData base source expanded data.schema.signature g auxiliaries block ∧
    ContainersInstalled base auxiliaries ∧
    base ≤ installBase ∧
    data.schema.restoration = compilationRestoration source auxiliaries ∧
    data.schema.sourceFamilies = source.types.map (·.name) ∧
    data.uvars = g.uvars ∧ data.levels = g.levels ∧ data.target = g.targetLevel ∧
    source.WF installBase ∧ installBase.addInduct source = some installed ∧
    source.RecsOf block ∧ installed ≤ env ∧ block.WF installBase

/-- `RecursorRegistered` with its installation fixed: the declaration `source`, installed at
`installBase` into `installed`. -/
def RecursorRegisteredAt (env : VEnv) (data : RecursorData) (source : VInductDecl)
    (installBase installed : VEnv) : Prop :=
  ∃ base expanded, ∃ (g : Instance data.schema.signature), ∃ auxiliaries block,
    CompilationData base source expanded data.schema.signature g auxiliaries block ∧
    ContainersInstalled base auxiliaries ∧
    base ≤ installBase ∧
    data.schema.restoration = compilationRestoration source auxiliaries ∧
    data.schema.sourceFamilies = source.types.map (·.name) ∧
    data.uvars = g.uvars ∧ data.levels = g.levels ∧ data.target = g.targetLevel ∧
    source.WF installBase ∧ installBase.addInduct source = some installed ∧
    source.RecsOf block ∧ installed ≤ env ∧ block.WF installBase

theorem RecursorRegisteredAt.registered {data : RecursorData} {source : VInductDecl}
    {installBase installed : VEnv}
    (H : RecursorRegisteredAt env data source installBase installed) : RecursorRegistered env data :=
  let ⟨base, expanded, g, auxiliaries, block, h⟩ := H
  ⟨base, installBase, source, expanded, g, auxiliaries, block, installed, h⟩

/-- A fold that succeeds passes through every element: the step at `a ∈ l` succeeds from some
intermediate environment, and its result is below the final one. -/
theorem foldlM_step_le {α} {f : VEnv → α → Option VEnv} (hf : ∀ {e a e'}, f e a = some e' → e ≤ e') :
    ∀ {l : List α} {init final : VEnv}, l.foldlM f init = some final → ∀ a ∈ l,
      ∃ e e', f e a = some e' ∧ e' ≤ final
  | [], _, _, _, _, h => by cases h
  | b :: l, init, final, h, a, ha => by
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    obtain ⟨e₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨init, e₁, h1, foldlM_le hf h2⟩
    · exact foldlM_step_le hf h2 a ha

/-- Every recursor rule of an installed declaration is registered as an ι pattern. -/
theorem addInduct_pats_of_rule {env env' : VEnv} {decl : VInductDecl}
    (h : env.addInduct decl = some env') {r : VRecursor} (hr : r ∈ decl.recs)
    {ru : VRecRule} (hru : ru ∈ r.rules) :
    ∃ hc : ru.rhs.Closed,
      env'.pats
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor
          r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
          .true) := by
  obtain ⟨env1, env2, env3, -, -, -, s4⟩ := addInduct_stages h
  unfold VInductDecl.addRules at s4
  obtain ⟨e, e', hstep, hle⟩ := foldlM_step_le
    (fun hh => foldlM_le (fun hh' => addRecRule_le hh') hh) s4 r hr
  obtain ⟨e₀, e₀', hstep', hle'⟩ := foldlM_step_le (fun hh => addRecRule_le hh) hstep ru hru
  have hc : ru.rhs.Closed := by
    unfold addRecRule at hstep'
    split at hstep'
    · assumption
    · cases hstep'
  exact ⟨hc, hle.pats (hle'.pats (addRecRule_pats hc hstep'))⟩

/-- The compilation instance of a registered recursor is the one its data records. -/
theorem RecursorRegistered.recursorInstance_eq {data : RecursorData}
    {base source expanded : _} {g : Instance data.schema.signature} {auxiliaries block}
    (hdata : CompilationData base source expanded data.schema.signature g auxiliaries block)
    (hu : data.uvars = g.uvars) (hl : data.levels = g.levels) (ht : data.target = g.targetLevel) :
    data.recursorInstance = g := by
  cases g with
  | mk U levels target recNames =>
    simp only [RecursorData.recursorInstance, Instance.mk.injEq]
    exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩

/-- A restored equation of the compilation instance is one of the block's rules. -/
theorem RecursorRegistered.equation_mem_rules {data : RecursorData}
    {base source expanded : _} {g : Instance data.schema.signature} {auxiliaries block}
    (hdata : CompilationData base source expanded data.schema.signature g auxiliaries block)
    (index : Fin data.schema.signature.constructors.size) {equation : VDefEq}
    (hg : (compilationRestoration source auxiliaries).equation (g.equation index) = some equation) :
    equation ∈ block.rules := by
  have hgenerated : g.equation index ∈ g.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hgenerated
  have heq : actual = equation := Option.some.inj (hrestore.symm.trans hg)
  rw [← heq]
  exact hmem

/-- The ι pattern of a generated equation of a registered recursor is registered: the
equation is a rule of the compiled block, hence (`VInductDecl.RecsOf`) the generated equation
of a recursor rule `ru` of a recursor `r` of the installed declaration, whose ι pattern
`VEnv.addRecRule` registered. -/
theorem RecursorRegistered.restoredEquation_pat
    (H : RecursorRegistered env data) (index : Fin data.schema.signature.constructors.size)
    {equation : VDefEq}
    (hgen : data.schema.restoration.equation (data.recursorInstance.equation index) =
      some equation) :
    ∃ (r : VRecursor) (ru : VRecRule) (hc : ru.rhs.Closed), VRecRule.OfEquation r ru equation ∧
      env.pats
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor
          r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
          .true) := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hwf, hadd, hrecs, he, -⟩ := H
  have hinstance : data.recursorInstance = g :=
    RecursorRegistered.recursorInstance_eq hdata hu hl ht
  rw [hinstance, hr] at hgen
  have hmem := RecursorRegistered.equation_mem_rules hdata index hgen
  obtain ⟨r, hr', ru, hru, hof⟩ := hrecs.rules_total equation hmem
  obtain ⟨hc, hp⟩ := addInduct_pats_of_rule hadd hr' hru
  exact ⟨r, ru, hc, hof, he.pats hp⟩

/-- The singleton equation is a generated equation of the compilation instance. -/
theorem RecursorData.singletonEquation_eq {data : RecursorData} {equation : VDefEq}
    (hgen : data.singletonEquation = some equation) :
    ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner ∧
      data.schema.restoration.equation (data.recursorInstance.equation index) = some equation := by
  unfold RecursorData.singletonEquation at hgen
  dsimp only at hgen
  split at hgen <;> try contradiction
  rename_i index hfilter
  refine ⟨index, ?_, hgen⟩
  have := List.mem_filter.1 (hfilter ▸ List.mem_singleton_self index)
  simpa using this.2

/-- The singleton equation's ι pattern is registered (the stored equation of the source
branch, as a pattern). -/
theorem RecursorRegistered.singletonEquation
    (H : RecursorRegistered env data)
    (hgen : data.singletonEquation = some equation) :
    ∃ (r : VRecursor) (ru : VRecRule) (hc : ru.rhs.Closed), VRecRule.OfEquation r ru equation ∧
      env.pats
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor
          r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
          .true) := by
  obtain ⟨index, -, hgen'⟩ := RecursorData.singletonEquation_eq hgen
  exact H.restoredEquation_pat index hgen'

/-- The recursor type computed from the metadata is exactly the type of its
installed recursor, selected from the same finite compilation instance. -/
theorem RecursorRegistered.recursorType
    (H : RecursorRegistered env data)
    (hgen : data.recursorType = some type) :
    env.constants data.name = some { uvars := data.uvars, type := type } := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hwf, hadd, hrecs, he, -⟩ := H
  have hinstance : data.recursorInstance = g :=
    RecursorRegistered.recursorInstance_eq hdata hu hl ht
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
  rw [← hrecs.recursors] at hmem
  obtain ⟨rec, hrec, hval⟩ := List.mem_map.1 hmem
  have hfind := addInduct_rec_find hadd hrec
  rw [hval] at hfind
  exact he.constants hfind

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
