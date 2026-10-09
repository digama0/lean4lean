import Lean4Lean.Verify.Inductive.Recursor.Signature.GeneratorShapes
import Lean4Lean.Verify.Inductive.Nested.Restoration.TrRestoredRecursorVal
import Lean4Lean.Verify.Environment.RecursorAlignment
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas

namespace Lean4Lean
namespace InductiveSignature

/-! The restored major domain, in the source and auxiliary cases. -/




/-! The recursor shape contract for a restored recursor. -/

/-- Exactly the facts about a restored recursor that fix its `VRecursorShape`:
its stored abstract constant is the restored generated type, its counts are the
expanded signature's, it is not K-like, and its major family application is the
restored owner family at the parameter and index variables
(`TrRestoredRecursorVal.specialization`). Rules are not involved. -/
structure RestoredRecursorShape {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (venv : VEnv) (owner : Fin s.families.size)
    (rec : Lean.RecursorVal) : Prop where
  type : ∃ type, r.expr (g.recursorType owner) = some type ∧
    venv.constants rec.name = some ⟨rec.levelParams.length, type⟩
  numParams : rec.numParams = s.params.length
  numIndices : rec.numIndices = s.families[owner].indices.length
  numMotives : rec.numMotives = s.families.size
  numMinors : rec.numMinors = s.constructors.size
  k : rec.k = false
  specialization : ∃ head : RestoredFamilyHead,
    rec.getMajorInduct = head.name ∧
    (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
    r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0))

/-- The abstract constant installed for a restored recursor entry is the
restored generated type at the concrete recursor's name and universe arity. -/
theorem restoredRecursor_constant {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} {value : VConstVal}
    (hvalue : r.recursor (g.recursor owner) = some value)
    (hconst : venv.constants value.name = some value.toVConstant)
    (hname : rec.name = r.recursorName (g.recursorName owner))
    (huvars : rec.levelParams.length = g.uvars) :
    ∃ type, r.expr (g.recursorType owner) = some type ∧
      venv.constants rec.name = some ⟨rec.levelParams.length, type⟩ := by
  simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hvalue
  cases ht : r.expr (g.recursor owner).type with
  | none => simp [ht] at hvalue
  | some type =>
    simp only [ht, Option.bind_some, Option.some.injEq] at hvalue
    subst hvalue
    refine ⟨type, ht, ?_⟩
    rw [hname, huvars]
    exact hconst

/-- A recursor of a block with more than one family is not K-like. -/
theorem TrRestoredRecursorVal.k_eq_false {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {sourceNames : List Name} {venv : VEnv}
    {owner : Fin s.families.size} {rec : Lean.RecursorVal}
    (H : TrRestoredRecursorVal g r sourceNames venv owner rec)
    (hfamilies : 1 < s.families.size) : rec.k = false := by
  cases hk : rec.k with
  | false => rfl
  | true => have := (H.k hk).1; omega

/-- The restored recursor's stored type has the recursor shape, with the
restored family head's arguments as constructor parameters. -/
theorem RestoredRecursorShape.shape {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShape g r venv owner rec) :
    ∃ head : RestoredFamilyHead, rec.getMajorInduct = head.name ∧
      Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams
        head.arguments.length rec.numMotives rec.numMinors rec.numIndices
        rec.getMajorInduct head.levels head.arguments) := by
  rcases H.type with ⟨type, htype, hconst⟩
  rcases H.specialization with ⟨head, hmajor, hargs, happ⟩
  rcases r.expr_recursorType_eq_some htype with ⟨pre, major, hpre, hm, rfl⟩
  have hprelen : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    rw [← g.recursorPrefix_length owner]
    exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
  have hmaj : major = VExpr.mkApps (.const head.name head.levels)
      (head.arguments.map (fun arg => arg.liftN
        (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
        vars s.families[owner].indices.length 0) := by
    have := hm.symm.trans happ
    exact Option.some.inj this
  refine ⟨head, hmajor, ⟨{
    ctorParams_length := rfl
    ctorParams_closed := by rw [H.numParams]; exact hargs
    type := _
    const := hconst
    doms := pre ++ [major]
    result := g.recursorBody owner
    type_eq := rfl
    doms_length := by
      simp [hprelen, H.numParams, H.numMotives, H.numMinors, H.numIndices]
    major_eq := ?_ }⟩⟩
  rw [H.numParams, H.numMotives, H.numMinors, H.numIndices, ← hprelen,
    List.getElem?_concat_length, hmaj, ← hmajor, vars_eq_bvarRange, Nat.add_zero]

/-- The rule-free copy of a restored recursor is aligned. -/
theorem RestoredRecursorShape.alignmentCore {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShape g r venv owner rec) :
    RecursorAlignmentCore venv { rec with rules := [] } := by
  rcases H.shape with ⟨head, _, hshape⟩
  exact ⟨head.arguments.length, head.levels, head.arguments, hshape, by simp⟩

/-- The rule-free copy of a restored recursor is not K-like. -/
theorem RestoredRecursorShape.kLike {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal} (H : RestoredRecursorShape g r venv owner rec)
    (C : Lean.ConstMap) : KLikeRecursor C venv { rec with rules := [] } := by
  intro hk
  have : rec.k = true := hk
  rw [H.k] at this
  cases this
