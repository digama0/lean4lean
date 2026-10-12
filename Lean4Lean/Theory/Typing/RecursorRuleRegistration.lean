import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.CompilationMajors

/-! Every recursor rule is selected from the same finite compilation instance
as its recursor. Restoration, equation presence and head ownership are
retained before constructing the corresponding first-order pattern. -/

namespace Lean4Lean.InductiveSignature.RecursorData

/-- The exact restored recursor equation at a signature constructor index. -/
def equation (data : RecursorData)
    (index : Fin data.schema.signature.constructors.size) : Option VDefEq :=
  data.schema.restoration.equation (data.recursorInstance.equation index)

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open InductiveSignature
variable {data : RecursorData} {equation : VDefEq}
  {index : Fin data.schema.signature.constructors.size}

private theorem registeredInstance (H : RecursorRegistered env data) :
    ∃ base installBase source expanded auxiliaries block installed,
      CompilationData base source expanded data.schema.signature data.recursorInstance auxiliaries block ∧
      ContainersInstalled base auxiliaries ∧
      data.schema.restoration = compilationRestoration source auxiliaries ∧
      source.WF installBase ∧ installBase.addInduct source = some installed ∧
      source.RecsOf block ∧ installed ≤ env := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, _, hr, _, hu, hl, ht, hwf, hadd, hrecs, he, -⟩ := H
  have hg : data.recursorInstance = g := RecursorRegistered.recursorInstance_eq hdata hu hl ht
  exact ⟨base, installBase, source, expanded, auxiliaries, block, installed, hg ▸ hdata, hprior, hr,
    hwf, hadd, hrecs, he⟩

/-- The restored equation is headed by precisely this recursor. -/
theorem RecursorRegistered.equation_head (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) :
    equation.lhs.stripLams.getAppFnArgs.1 = .const data.name (VLevel.params data.uvars) := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _, _, _⟩ :=
    registeredInstance H
  have hleft := (Restoration.equation_parts hgen).1
  have hn := hdata.heads_not_recursors data.schema.signature.constructors[index].owner
  rw [← hr] at hn
  have he := Restoration.wrapLams_head_const hn
    (VExpr.getAppFnArgs_mkApps_head _ _) hleft
  simpa only [RecursorData.recursorInstance, RecursorData.name,
    Instance.recursorName, howner] using he

/-- Every extracted recursor equation body has an actual constant head. -/
theorem RecursorRegistered.equation_body_head
    (H : RecursorRegistered env data) (hgen : data.equation index = some equation)
    (hbody : RecursorSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body) :
    ∃ name levels args, body.lhs = VExpr.mkApps (.const name levels) args := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, _, hr, _, _, _, _⟩ :=
    registeredInstance H
  have hleft := (Restoration.equation_parts hgen).1
  have hn := hdata.heads_not_recursors data.schema.signature.constructors[index].owner
  rw [← hr] at hn
  have he := Restoration.wrapLams_head_const hn
    (VExpr.getAppFnArgs_mkApps_head _ _) hleft
  rw [← (RecursorSchema.EquationBody.extract_sound hbody).1, VExpr.stripLams_wrapLams, RecursorSchema.EquationBody.extracted_lhs_stripLams hbody] at he
  exact ⟨_, _, body.lhs.getAppFnArgs.2, by
    rw [← he]
    exact (VExpr.rebuild_spine body.lhs).symm⟩

theorem RecursorRegistered.singletonEquation_body_head
    (H : RecursorRegistered env data) (hgen : data.singletonEquation = some equation)
    (hbody : RecursorSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body) :
    ∃ name levels args, body.lhs = VExpr.mkApps (.const name levels) args := by
  unfold RecursorData.singletonEquation at hgen
  dsimp only at hgen
  split at hgen <;> try contradiction
  exact H.equation_body_head hgen hbody

end Lean4Lean.VEnv
