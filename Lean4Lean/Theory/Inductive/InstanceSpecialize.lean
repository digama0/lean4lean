import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! # Universe specialization of generated recursor types

Instantiating the universe parameters of a generated recursor type is generating the
recursor type of the specialized instance: the instance's source universes and elimination
universe are instantiated, and nothing else changes. -/

namespace Lean4Lean.InductiveSignature
open VExpr

namespace Instance
variable {s : InductiveSignature}

/-- The instance at instantiated universe levels. -/
def specialize (g : Instance s) (U : Nat) (ls : List VLevel) : Instance s where
  uvars := U
  levels := g.levels.map (·.inst ls)
  targetLevel := g.targetLevel.inst ls
  recursorName := g.recursorName

theorem instL_vars (count below : Nat) (ls : List VLevel) :
    (vars count below).map (·.instL ls) = vars count below := by
  simp [vars, VExpr.instL]

theorem instL_insertBinders (domains : List VExpr) (count : Nat) (ls : List VLevel) :
    (insertBinders domains count).map (·.instL ls) =
      insertBinders (domains.map (·.instL ls)) count := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i hi hj
    simp [insertBinders]

theorem params_specialize (g : Instance s) (U ls) :
    g.params.map (·.instL ls) = (g.specialize U ls).params := by
  simp [params, specialize, Function.comp_def, VExpr.instL_instL]

theorem motive_specialize (g : Instance s) (U ls) (family : Family) (prior : Nat) :
    (g.motive family prior).instL ls = (g.specialize U ls).motive family prior := by
  simp [motive, specialize, insertBinders, VExpr.instL_instL, VExpr.instL, instL_vars, List.zipIdx_map,
    Function.comp_def]

theorem motives_specialize (g : Instance s) (U ls) :
    g.motives.map (·.instL ls) = (g.specialize U ls).motives := by
  simp only [motives, List.map_map, Function.comp_def, motive_specialize g U ls]

theorem hypothesis_specialize (g : Instance s) (U ls) (ctor : Constructor s.families.size)
    (priorMinors priorIHs field : Nat) (r : Recursive s.families.size) :
    (g.hypothesis ctor priorMinors priorIHs field r).instL ls =
      (g.specialize U ls).hypothesis ctor priorMinors priorIHs field r := by
  simp [hypothesis, specialize, underFields, VExpr.instL_instL, VExpr.instL, instL_vars,
    Function.comp_def]

theorem constructorApp_specialize (g : Instance s) (U ls) (ctor : Constructor s.families.size)
    (extra below : Nat) :
    (g.constructorApp ctor extra below).instL ls =
      (g.specialize U ls).constructorApp ctor extra below := by
  simp [constructorApp, specialize, VExpr.instL, instL_vars]

theorem minor_specialize (g : Instance s) (U ls) (ctor : Constructor s.families.size)
    (prior : Nat) :
    (g.minor ctor prior).instL ls = (g.specialize U ls).minor ctor prior := by
  simp [minor, insertBinders, VExpr.instL_instL, hypothesis_specialize g U ls, List.zipIdx_map,
    constructorApp_specialize g U ls, Function.comp_def, specialize, VExpr.instL]

theorem minors_specialize (g : Instance s) (U ls) :
    g.minors.map (·.instL ls) = (g.specialize U ls).minors := by
  simp only [minors, List.map_map, Function.comp_def, minor_specialize g U ls]

theorem recursorType_specialize (g : Instance s) (U ls) (owner : Fin s.families.size) :
    (g.recursorType owner).instL ls = (g.specialize U ls).recursorType owner := by
  simp only [recursorType, VExpr.instL_wrapForalls, List.map_append, params_specialize g U ls,
    motives_specialize g U ls, minors_specialize g U ls]
  simp [insertBinders, VExpr.instL_instL, familyApp, InductiveSignature.familyApp, List.zipIdx_map,
    Function.comp_def, specialize, VExpr.instL, instL_vars]

end Instance
end Lean4Lean.InductiveSignature
