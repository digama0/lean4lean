import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.RecursorRuleRegistration

/-! Recursor metadata is installed from the same finite instance and abstract
schema as the actual recursor block. Registry lookup adds no semantic data. -/

namespace Lean4Lean.InductiveSignature.RecursorData

/-- One recursor metadata entry for each family of the shared compilation instance. -/
def compilationEntries (key : Name) (source : VInductDecl) (s : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) (g : Instance s) : List RecursorData :=
  (List.finRange s.families.size).map fun owner =>
    ofInstance key (CaseSchema.ofCompilation source s auxiliaries) g owner

/-- Extend the metadata table with the entries of one installed block. -/
def installEntries (old : Name → Option RecursorData) (entries : List RecursorData)
    (name : Name) : Option RecursorData :=
  (entries.find? (fun data => data.name == name)).orElse (fun _ => old name)

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open InductiveSignature RecursorData
variable {block : VInductBlock} {name : Name}

/-- The metadata table has exactly the names of the restored installed
recursors, in the same family order. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_names
    (hdata : CompilationData base source expanded s g auxiliaries block) :
    (compilationEntries key source s auxiliaries g).map (·.name) =
      block.recursors.map (·.name) := by
  have hrestored := List.mapM_eq_some.mp hdata.recursors
  have hn : g.recursors.map (fun rec =>
      (compilationRestoration source auxiliaries).recursorName rec.name) =
      block.recursors.map (·.name) := by
    generalize g.recursors = originals at hrestored ⊢
    generalize block.recursors = actuals at hrestored ⊢
    induction hrestored with
    | nil => rfl
    | cons h hs ih =>
      simp only [Restoration.recursor, bind, Option.bind_eq_some_iff] at h
      obtain ⟨type, _, he⟩ := h
      cases he
      exact congrArg (List.cons _) ih
  rw [← hn]
  simp only [compilationEntries, List.map_map, Function.comp_def, ofInstance, name,
    CaseSchema.ofCompilation, Instance.recursors, Instance.recursor]
  simp only [hdata.recursorNames]

/-- Successful whole-block installation makes every new metadata name
fresh in the previous environment. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_fresh
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hinstall : block.install installBase = some installed)
    (hentry : data ∈ compilationEntries key source s auxiliaries g) :
    installBase.constants data.name = none := by
  have hname : data.name ∈ block.recursors.map (·.name) := by
    rw [← hdata.recursorEntries_names (key := key)]
    exact List.mem_map.mpr ⟨data, hentry, rfl⟩
  obtain ⟨rec, hrec, heq⟩ := List.mem_map.mp hname
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hinstall
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinstall
  have hf := VEnv.addConstVals_names_fresh hr rec hrec
  have hle : installBase ≤ (ctors.addEliminators block.eliminators).addProjections block.projections :=
    ((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
    VEnv.addEliminators_addProjections_le
  cases hv : installBase.constants data.name with
  | none => rfl
  | some value =>
    have hsome := hle.constants hv
    rw [← heq] at hsome
    rw [hf] at hsome
    contradiction


/-- Restoration succeeds for every selected family because the
entire restored recursor list was actually installed. -/
theorem RecursorRegistered.recursorType_exists
    (H : RecursorRegistered env data) : ∃ type, data.recursorType = some type := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinstance : data.recursorInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [recursorInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  have hgenerated : g.recursor data.owner ∈ g.recursors :=
    List.mem_map.mpr ⟨data.owner, List.mem_finRange _, rfl⟩
  obtain ⟨actual, _, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.recursors) _ hgenerated
  simp only [Restoration.recursor, Instance.recursor, bind, Option.bind_eq_some_iff] at hrestore
  obtain ⟨type, htype, _⟩ := hrestore
  exact ⟨type, by simpa only [RecursorData.recursorType, hinstance, hr] using htype⟩

theorem RecursorRegistered.constant_exists
    (H : RecursorRegistered env data) :
    ∃ value, env.constants data.name = some value := by
  obtain ⟨type, htype⟩ := H.recursorType_exists
  exact ⟨_, H.recursorType htype⟩

theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_nodup
    (hdata : CompilationData base source expanded s g auxiliaries block) :
    ((compilationEntries key source s auxiliaries g).map (·.name)).Nodup := by
  rw [hdata.recursorEntries_names]
  have hh := hdata.names
  simp only [List.map_append, List.nodup_append] at hh
  exact hh.2.1

private theorem recursorEntries_find (entries : List RecursorData)
    (hnodup : (entries.map (·.name)).Nodup) (hmem : data ∈ entries) :
    entries.find? (fun value => value.name == data.name) = some data := by
  induction entries with
  | nil => cases hmem
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with he | hm
    · subst head
      simp
    · have hne : head.name ≠ data.name := by
        intro he
        apply hnodup.1
        exact List.mem_map.mpr ⟨data, hm, he.symm⟩
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hne]
      exact ih hnodup.2 hm

/-- Every newly installed family remains individually addressable by its
actual restored name. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_lookup
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hmem : data ∈ compilationEntries key source s auxiliaries g) :
    RecursorData.installEntries old (compilationEntries key source s auxiliaries g)
      data.name = some data := by
  unfold RecursorData.installEntries
  rw [recursorEntries_find _ hdata.recursorEntries_nodup hmem]
  rfl

end Lean4Lean.VEnv

/-! A recursor metadata table is extracted from the finite compilation retained by an
actual inductive installation. Abstract eliminator metadata is not needed.
The compilation base is preserved by `CompiledInductive.mono`.
-/
namespace Lean4Lean
open InductiveSignature InductiveSignature.RecursorData VEnv
set_option Elab.async false
set_option maxRecDepth 2048
variable {base installBase extended env : VEnv} {source expanded : VInductDecl}
  {block : VInductBlock} {equation : VDefEq}

/-- Every restored constructor equation belongs to the descriptor for its
actual owner. Both the descriptor and equation are computed from one instance. -/
theorem InductiveSignature.CompilationData.recursorEntries_equation
    (compilation : CompilationData base source expanded signature generated auxiliaries block)
    (member : equation ∈ block.rules) (key : Name) :
    ∃ data ∈ compilationEntries key source signature auxiliaries generated,
      ∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner ∧
        data.equation index = some equation := by
  obtain ⟨original, originalMember, restored⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (List.mapM_eq_some.mp compilation.equations) _ member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp originalMember
  let data := ofInstance key (CaseSchema.ofCompilation source signature auxiliaries)
    generated signature.constructors[index].owner
  have instanceEq : data.recursorInstance = generated := by
    cases generated with
    | mk U levels target names =>
      change Instance.mk U levels target (fun owner => signature.families[owner].name.str "rec") =
        Instance.mk U levels target names
      congr 1
      exact funext fun owner => (compilation.recursorNames owner).symm
  refine ⟨data, List.mem_map.mpr ⟨signature.constructors[index].owner,
    List.mem_finRange _, rfl⟩, index, rfl, ?_⟩
  change (compilationRestoration source auxiliaries).equation (data.recursorInstance.equation index) = _
  rw [instanceEq]
  exact restored

end Lean4Lean
