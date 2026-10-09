import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ProjectionRigidity
import Lean4Lean.Theory.Inductive.RecursorEquationHeads
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.RecursorEquationCoverage
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Typing.EnvTables.CtorFamily
import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.ProjectionLemmas

namespace Lean4Lean
def Pattern.RHS.applyArgs {p : Pattern} (head : p.RHS) (args : List p.RHS) : p.RHS := args.foldl .app head
theorem Pattern.RHS.applyArgs_apply {p : Pattern} (head : p.RHS) (args : List p.RHS) {values : p.Path → VExpr} :
    (head.applyArgs args).apply levels values =
      VExpr.mkApps (head.apply levels values) (args.map fun rhs => rhs.apply levels values) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih => simpa [applyArgs, VExpr.mkApps, Pattern.RHS.apply] using ih (.app head arg)
end Lean4Lean

namespace Lean4Lean
namespace VInductBlock
open InductiveSignature
/-- The projection stage of a certified block is well formed. -/
theorem EliminatorsWF.projectionsWF {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsWF base decl block) (hbase : base.WF)
    (hdecl : decl.WF base) (hcompile : decl.CompilesTo base block)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    ((envCtors.addEliminators block.eliminators).addProjections block.projections).WF := by
  have ht' : base.addConstVals decl.typeConstants = some envTypes := by
    simpa only [hcompile.types] using htypes
  have helimWF := H.elimWF hbase hdecl.1 hcompile.types hcompile.ctors htypes hctors
  obtain ⟨_, _, _, _, H⟩ := H
  rcases H with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, -⟩
  · rw [hcompile.projections, VInductDecl.projectionEntries_eq_nil hT]; exact helimWF
  have parameters := hdecl.sourceParameterWF ht'
  exact VEnv.WF.inductProjections hbase helimWF ⟨key, schema, hE, hreg⟩
    hcompile.sourceNames hdecl.1.sourceTypes hdecl.1.2.2.2.1 (hdecl.1.constructorsWF_at ht')
    parameters parameters.rawCtorShape hcompile.types hcompile.ctors
    hcompile.projections htypes hctors
end VInductBlock
end Lean4Lean

namespace Lean4Lean
namespace VEnv
variable {env : VEnv} {U : Nat}
open private WF.projectionRigid_both from Lean4Lean.Theory.Typing.ProjectionRigidity
/-- The constructor of a registered structure is rigid: no installed equation
computes at its head. -/
theorem WF.projectionCtorRigid {env : VEnv} (H : env.WF)
    {name : Name} {info : VProjectionInfo} (hinfo : env.projections name info) :
    env.Rigid info.ctorName := (WF.projectionRigid_both H name info hinfo).2
end VEnv
end Lean4Lean

namespace Lean4Lean
/-- Finite compilation retains concrete recursor equation coverage for every
source constructor, including when the original derivation is replayed. -/
theorem CompiledInductive.constructor_equation
    (H : CompiledInductive env source block) :
    ∀ ctor ∈ source.constructorConstants, ∃ equation ∈ block.rules, ∃ fn levels args,
      equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args) := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source block _ =>
      ∀ ctor ∈ source.constructorConstants, ∃ equation ∈ block.rules, ∃ fn levels args,
        equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args))
    (motive_2 := fun _ _ _ => True)
    (fun data _ _ ctor hctor => data.constructor_equation hctor)
    (fun _ _ _ ih => ih)
    trivial
    (fun _ _ _ _ _ _ _ => trivial)
    H
end Lean4Lean

namespace Lean4Lean
theorem InductiveSignature.CaseCompilationData.ctor_result
    (hdata : InductiveSignature.CaseCompilationData env source expanded s auxiliaries block) :
    ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, ∃ ls,
      ctor.type.forallResult.getAppFnArgs.1 = .const type.name ls := by
  intro type htype ctor hc
  obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
  obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw type htype ctor hc
  have h2 := hhead
  rw [← VExpr.forallResult_of_head hhead, ← VExpr.forallResult_wrapForalls doms, ← heq] at h2
  exact ⟨_, h2⟩
end Lean4Lean

namespace Lean4Lean.VEnv
open InductiveSignature RecursorData
variable {block : VInductBlock} {name : Name}
/-- Every generated family descriptor has concrete whole-block provenance. -/
theorem RecursorRegistered.ofCompilation
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : ContainersInstalled base auxiliaries)
    (hbase : base ≤ installBase)
    (hinstall : block.install installBase = some installed) (hle : installed ≤ env)
    (owner : Fin s.families.size) :
    RecursorRegistered env
      (ofInstance key (CaseSchema.ofCompilation source s auxiliaries) g owner) :=
  ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, rfl, rfl, rfl, rfl, rfl, hinstall, hle⟩
theorem RecursorRegistered.compilationEntries
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : ContainersInstalled base auxiliaries)
    (hbase : base ≤ installBase)
    (hinstall : block.install installBase = some installed) (hle : installed ≤ env)
    (hentry : data ∈ compilationEntries key source s auxiliaries g) :
    RecursorRegistered env data := by
  obtain ⟨owner, _, rfl⟩ := List.mem_map.mp hentry
  exact .ofCompilation hdata hprior hbase hinstall hle owner
/-- Installing a new block cannot replace metadata of an earlier
registered recursor: its concrete constant name is already occupied. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_preserves
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hinstall : block.install installBase = some installed)
    (hregistered : RecursorRegistered installBase previous)
    (hold : old previous.name = some previous) :
    RecursorData.installEntries old (compilationEntries key source s auxiliaries g)
      previous.name = some previous := by
  unfold RecursorData.installEntries
  cases hf : (compilationEntries key source s auxiliaries g).find?
      (fun data => data.name == previous.name) with
  | none => exact hold
  | some fresh =>
    have hname : fresh.name = previous.name := by simpa using List.find?_some hf
    have hnone := hdata.recursorEntries_fresh hinstall (List.mem_of_find?_eq_some hf)
    obtain ⟨value, hsome⟩ := hregistered.constant_exists
    rw [hname, hsome] at hnone
    contradiction
end Lean4Lean.VEnv

namespace Lean4Lean.InductiveSignature.RecursorData
/-- Only constructors of the selected recursor owner are enumerated. -/
def constructorIndices (data : RecursorData) :
    List (Fin data.schema.signature.constructors.size) :=
  (List.finRange data.schema.signature.constructors.size).filter
    (fun i => data.schema.signature.constructors[i].owner == data.owner)
theorem mem_constructorIndices {data : RecursorData}
    {index : Fin data.schema.signature.constructors.size} :
    index ∈ data.constructorIndices ↔ data.schema.signature.constructors[index].owner = data.owner := by
  simp [constructorIndices]
end Lean4Lean.InductiveSignature.RecursorData
namespace Lean4Lean.VEnv
open InductiveSignature
open private registeredInstance from Lean4Lean.Theory.Typing.RecursorRuleRegistration
variable {data : RecursorData} {equation : VDefEq}
  {index : Fin data.schema.signature.constructors.size}
/-- Successful compilation restores every generated rule, including every
rule of a nonsingleton recursor. -/
theorem RecursorRegistered.equation_exists (H : RecursorRegistered env data)
    (index : Fin data.schema.signature.constructors.size) :
    ∃ equation, data.equation index = some equation := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _⟩ :=
    registeredInstance H
  have hm : data.recursorInstance.equation index ∈ data.recursorInstance.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨equation, _, he⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hm
  exact ⟨equation, by simpa only [RecursorData.equation, hr] using he⟩
/-- Rule presence follows from the actual installation, not from pattern
soundness or a guessed recursor name. -/
theorem RecursorRegistered.equation_present (H : RecursorRegistered env data)
    (hgen : data.equation index = some equation) : env.defeqs equation := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, hi, he⟩ :=
    registeredInstance H
  have hm : data.recursorInstance.equation index ∈ data.recursorInstance.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hm
  have hg : (compilationRestoration source auxiliaries).equation
      (data.recursorInstance.equation index) = some equation := by
    simpa only [RecursorData.equation, hr] using hgen
  cases Option.some.inj (hrestore.symm.trans hg)
  exact he.defeqs (VInductBlock.install_rule hi hmem)
theorem RecursorRegistered.equation_uvars (_H : RecursorRegistered env data)
    (hgen : data.equation index = some equation) : equation.uvars = data.uvars := by
  unfold RecursorData.equation Restoration.equation at hgen
  simp only [bind, Option.bind_eq_some_iff] at hgen
  obtain ⟨_, _, _, _, _, _, he⟩ := hgen
  cases he
  rfl
/-- Constructor specialization computes the recursor major's actual name. -/
theorem RecursorRegistered.equation_major (H : RecursorRegistered env data)
    (hgen : data.equation index = some equation) :
    ∃ fn levels args, equation.lhs.stripLams = .app fn
      (VExpr.mkApps (.const (data.schema.restoration.headName
        data.schema.signature.constructors[index].name) levels) args) := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _⟩ :=
    registeredInstance H
  have hg : (compilationRestoration source auxiliaries).equation
      (data.recursorInstance.equation index) = some equation := by
    simpa only [RecursorData.equation, hr] using hgen
  simpa only [← hr] using Instance.restored_equation_major hdata index hg
/-- All syntax stored in the actual equation has the scope needed by fixed
pattern right-hand sides. -/
theorem RecursorRegistered.equation_closed (henv : env.WF)
    (H : RecursorRegistered env data) (hgen : data.equation index = some equation) :
    equation.lhs.Closed ∧ equation.rhs.Closed ∧ equation.type.Closed := by
  have hw := henv.ordered.defEqWF (H.equation_present hgen)
  obtain ⟨u, ht⟩ := hw.1.isType henv.ordered (by trivial)
  exact ⟨VExpr.WF.closedN henv.ordered ⟨_, hw.1⟩ (by trivial),
    VExpr.WF.closedN henv.ordered ⟨_, hw.2⟩ (by trivial),
    VExpr.WF.closedN henv.ordered (show VExpr.WF env equation.uvars [] equation.type from ⟨_, ht⟩) (by trivial)⟩
end Lean4Lean.VEnv

namespace Lean4Lean.InductiveSignature.CaseSchema
theorem Certified.constructor_index_unique {schema : CaseSchema}
    (H : schema.Certified base source block)
    {owner : Fin schema.signature.families.size}
    {i j : Fin schema.signature.constructors.size}
    (hi : schema.signature.constructors[i].owner = owner)
    (hj : schema.signature.constructors[j].owner = owner)
    (hn : schema.restoration.headName schema.signature.constructors[i].name =
      schema.restoration.headName schema.signature.constructors[j].name) : i = j := by
  have hp := H.constructor_names_nodup owner
  simp only [view, List.toList_toArray, List.map_filterMap] at hp
  have hp := List.pairwise_filterMap.mp hp
  have hp := List.pairwise_iff_getElem.mp hp
  have hneq (a b : Fin schema.signature.constructors.size) (hab : a.val < b.val)
      (ha : schema.signature.constructors[a].owner = owner)
      (hb : schema.signature.constructors[b].owner = owner) :
      schema.restoration.headName schema.signature.constructors[a].name ≠
        schema.restoration.headName schema.signature.constructors[b].name := by
    have h := hp a.val b.val (by simp) (by simp) hab
    simp only [Array.getElem_toList] at h
    simp only [Fin.getElem_fin] at ha hb ⊢
    exact h _ (by simp [ha, caseConstructor]) _ (by simp [hb, caseConstructor])
  apply Fin.ext
  by_cases h : i.val = j.val
  · exact h
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact (hneq i j h hi hj hn).elim
    · exact (hneq j i h hj hi hn.symm).elim
end Lean4Lean.InductiveSignature.CaseSchema
namespace Lean4Lean.VEnv
open InductiveSignature
/-- The same registered recursor owner has one constructor index for each
restored constructor name, including specialized container constructors. -/
theorem RecursorRegistered.constructor_index_unique
    (H : RecursorRegistered env data)
    {i j : Fin data.schema.signature.constructors.size}
    (hi : data.schema.signature.constructors[i].owner = data.owner)
    (hj : data.schema.signature.constructors[j].owner = data.owner)
    (hn : data.schema.restoration.headName data.schema.signature.constructors[i].name =
      data.schema.restoration.headName data.schema.signature.constructors[j].name) : i = j := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, _, hr, hf, _⟩ := H
  have hc : data.schema.Certified base source block :=
    ⟨expanded, auxiliaries, hdata.toCaseCompilationData, hprior, hr, hf, hdata.recursorNamesFresh⟩
  exact hc.constructor_index_unique hi hj hn
end Lean4Lean.VEnv

namespace Lean4Lean
namespace VExpr
theorem Subst.ofList_ge (args : List VExpr) (h : args.length ≤ k) :
    Subst.ofList args k = .bvar (k - args.length) := dif_neg (Nat.not_lt.2 h)
/-- Lifting an instantiation lifts the arguments. -/
theorem liftN_instOuter (X : VExpr) (args : List VExpr) (hX : X.ClosedN args.length) (n : Nat) :
    (X.instOuter args).liftN n = X.instOuter (args.map (·.liftN n)) := by
  simp only [instOuter_eq_subst, liftN_eq_subst]
  rw [subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (args.map _) (by simpa using hi), List.getElem_map]
end VExpr
end Lean4Lean
