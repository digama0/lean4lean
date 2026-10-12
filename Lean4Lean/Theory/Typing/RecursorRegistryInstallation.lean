import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.RecursorRuleRegistration

/-! Recursor metadata is installed from the same finite instance and schema as the actual
recursor block. Registry lookup adds no semantic data. -/

namespace Lean4Lean.InductiveSignature.RecursorData

/-- One recursor metadata entry for each family of the shared compilation instance. -/
def compilationEntries (key : Name) (source : VInductDecl) (s : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) (g : Instance s) : List RecursorData :=
  (List.finRange s.families.size).map fun owner =>
    ofInstance key (RecursorSchema.ofCompilation source s auxiliaries) g owner

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
    RecursorSchema.ofCompilation, Instance.recursors, Instance.recursor]
  simp only [hdata.recursorNames]

/-- Successful installation of the declaration makes every new metadata name fresh in the
previous environment: the metadata names are the block's recursor names, the declaration's
recursors (`VInductDecl.RecsOf`), fresh when `VEnv.addInduct` adds them. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_fresh
    {installBase installed : VEnv}
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hrecs : source.RecsOf block)
    (hinstall : installBase.addInduct source = some installed)
    (hentry : data ∈ compilationEntries key source s auxiliaries g) :
    installBase.constants data.name = none := by
  have hname : data.name ∈ block.recursors.map (·.name) := by
    rw [← hdata.recursorEntries_names (key := key)]
    exact List.mem_map.mpr ⟨data, hentry, rfl⟩
  rw [← hrecs.recursors, List.map_map] at hname
  obtain ⟨rec, hrec, heq⟩ := List.mem_map.mp hname
  rw [← heq]
  exact addInduct_rec_fresh hinstall hrec

/-- Restoration succeeds for every selected family because the
entire restored recursor list was actually installed. -/
theorem RecursorRegistered.recursorType_exists
    (H : RecursorRegistered env data) : ∃ type, data.recursorType = some type := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, _, _, _, he, -⟩ := H
  have hinstance : data.recursorInstance = g :=
    RecursorRegistered.recursorInstance_eq hdata hu hl ht
  have hgenerated : g.recursor data.owner ∈ g.recursors :=
    List.mem_map.mpr ⟨data.owner, List.mem_finRange _, rfl⟩
  obtain ⟨actual, _, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.recursors) _ hgenerated
  simp only [Restoration.recursor, Instance.recursor, bind, Option.bind_eq_some_iff] at hrestore
  obtain ⟨type, htype, _⟩ := hrestore
  exact ⟨type, by simpa only [RecursorData.recursorType, hinstance, hr] using htype⟩

theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursorEntries_nodup
    (hdata : CompilationData base source expanded s g auxiliaries block) :
    ((compilationEntries key source s auxiliaries g).map (·.name)).Nodup := by
  rw [hdata.recursorEntries_names]
  have hh := hdata.names
  simp only [List.map_append, List.nodup_append] at hh
  exact hh.2.1

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
  let data := ofInstance key (RecursorSchema.ofCompilation source signature auxiliaries)
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
