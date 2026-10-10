import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.RecursiveShapeCorrespondence

/-! Shapes of the generated recursors.

The recursor telescope used by recursor reduction (`VRecursorShape`) follows from the
generator's syntax: the last domain of a generated recursor type is the family applied to the
parameters and the indices. -/

namespace Lean4Lean
namespace InductiveSignature

/-- A generated recursor installed with its generated type has the shape expected by recursor
reduction (`VRecursorShape`): its last domain is the family applied to the parameters and the
indices, and constructors take the recursor's parameters. -/
theorem Instance.recursor_shape {s : InductiveSignature} (g : Instance s)
    (owner : Fin s.families.size) {env : VEnv}
    (hlookup : env.constants (g.recursorName owner) = some (g.recursor owner).toVConstant) :
    Nonempty (VRecursorShape env (g.recursorName owner) g.uvars s.params.length
      s.params.length s.families.size s.constructors.size s.families[owner].indices.length
      s.families[owner].name g.levels) := by
  let extra := s.families.size + s.constructors.size
  let indices := insertBinders (s.families[owner].indices.map (·.instL g.levels)) extra
  let major := g.familyApp owner
    (vars s.params.length (extra + indices.length)) (vars indices.length 0)
  let pre := g.params ++ g.motives ++ g.minors ++ indices
  have hindices : indices.length = s.families[owner].indices.length := by
    simp [indices, insertBinders]
  have hpre : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    simp [pre, Instance.params, Instance.motives, Instance.minors, hindices, Nat.add_assoc]
  refine ⟨{
    ctorParams_length := by simp
    ctorParams_closed := ?_
    type := g.recursorType owner
    const := hlookup
    doms := pre ++ [major]
    result := VExpr.mkApps
      (.bvar (indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val)))
      (vars indices.length 1 ++ [.bvar 0])
    type_eq := rfl
    doms_length := by simp [hpre]
    major_eq := ?_ }⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
    simp only [List.mem_range] at hi
    change s.params.length - 1 - i < s.params.length
    omega
  · rw [← hpre]
    simp only [List.getElem?_concat_length]
    congr 1
    simp only [major, Instance.familyApp, InductiveSignature.familyApp,
      vars_eq_bvarRange]
    rw [VExpr.bvarRange_map_liftN _ _ _ (Nat.le_refl _)]
    congr 2 <;> simp [extra, hindices, Nat.add_assoc] <;> congr 1 <;> omega

end InductiveSignature
end Lean4Lean
