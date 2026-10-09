import Lean4Lean.Primitive
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

/-!
# The primitive declaration shapes

Primitive declarations are `Bool` and `Nat`, recognized by `Primitive.checkInductive`
(section 3.1 of the design notes). `PrimitiveInductiveShape` is the dispatch
predicate: a successful recognition has exactly the canonical `Bool` or `Nat` syntax
(`checkPrimitiveInductive_eq_true_iff`), so the primitive path is verified for two finite
declarations. The file also proves the literal-disjointness and recursor-name facts that the
primitive path needs.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two declaration shapes for which the executable kernel checker enables
the primitive-name exception.  This is an operational dispatch predicate, not
the abstract inductive well-formedness specification. -/
def PrimitiveInductiveShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  lparams = [] ∧ nparams = 0 ∧ isUnsafe = false ∧
    (types = [{
        name := ``Bool
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Bool.false, type := .const ``Bool [] },
          { name := ``Bool.true, type := .const ``Bool [] }] }] ∨
      ∃ binderName binderInfo,
        types = [{
          name := ``Nat
          type := .sort (.succ .zero)
          ctors := [
            { name := ``Nat.zero, type := .const ``Nat [] },
            { name := ``Nat.succ,
              type := .forallE binderName (.const ``Nat [])
                (.const ``Nat []) binderInfo }] }])

/-- Successful primitive recognition has exactly the canonical `Bool` or
`Nat` syntax.  In particular the `true` branch is finite and can be verified
separately from the ordinary fresh-name pipeline. -/
theorem checkPrimitiveInductive_eq_true_iff
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) :
    Primitive.checkInductive env lparams nparams types isUnsafe =
        .ok true ↔
      PrimitiveInductiveShape lparams nparams types isUnsafe := by
  unfold Primitive.checkInductive PrimitiveInductiveShape
  constructor
  · intro h
    split at h
    · rename_i hpre
      have hpre' : (!isUnsafe && lparams.isEmpty && nparams == 0) = true :=
        hpre
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hpre'
      obtain ⟨⟨hisUnsafe, hlparams⟩, hnparams⟩ := hpre'
      have hisUnsafe' : isUnsafe = false := by
        cases isUnsafe <;> simp_all
      subst isUnsafe
      subst lparams
      subst nparams
      cases types with
      | nil =>
        simp only at h
        cases h
      | cons type tail =>
        cases tail with
        | cons other rest =>
          simp only at h
          cases h
        | nil =>
          simp only at h
          by_cases htype : (type.type == .sort (.succ .zero)) = true
          · rw [if_pos htype] at h
            by_cases hbool : type.name = ``Bool
            · simp only [hbool] at h
              split at h
              · rename_i _ hctors
                refine ⟨rfl, rfl, rfl, Or.inl ?_⟩
                congr 1
                have htypeEq : type.type = .sort (.succ .zero) :=
                  Expr.eqv_sort.mp htype
                cases type
                simp_all
              · change Except.error _ = Except.ok true at h
                cases h
            · by_cases hnat : type.name = ``Nat
              · simp only [hnat] at h
                split at h
                · rename_i _ binderName binderInfo hctors
                  refine ⟨rfl, rfl, rfl, Or.inr
                    ⟨binderName, binderInfo, ?_⟩⟩
                  congr 1
                  have htypeEq : type.type = .sort (.succ .zero) :=
                    Expr.eqv_sort.mp htype
                  cases type
                  simp_all
                · change Except.error _ = Except.ok true at h
                  cases h
              · simp only at h
                change Except.ok false = Except.ok true at h
                cases h
          · rw [if_neg htype] at h
            change Except.ok false = Except.ok true at h
            cases h
    · change Except.ok false = Except.ok true at h
      cases h
  · rintro ⟨rfl, rfl, rfl, hshape⟩
    rcases hshape with hbool | ⟨binderName, binderInfo, hnat⟩
    · subst types
      simp
      change Except.ok true = Except.ok true
      rfl
    · subst types
      simp
      change Except.ok true = Except.ok true
      rfl

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Literal expansion never mentions the `Bool` family header.  This is the
literal-side positivity premise needed by the finite primitive `Bool` branch. -/
theorem primitiveBoolLiteralDisjoint :
    checkPositivityStep.LiteralDisjoint #[.const ``Bool []] := by
  exact (checkPositivityStep.IndConstArray.ofExact (names := [``Bool])
    rfl).literalDisjoint (by
      simp [checkPositivityStep.LiteralConstructorNamesDisjoint,
        checkPositivityStep.literalConstructorNames])

/-- Literal expansion uses `Nat.zero` and `Nat.succ`, not the `Nat` family
header itself.  Consequently the primitive `Nat` declaration also satisfies
the literal-side positivity premise. -/
theorem primitiveNatLiteralDisjoint :
    checkPositivityStep.LiteralDisjoint #[.const ``Nat []] := by
  exact (checkPositivityStep.IndConstArray.ofExact (names := [``Nat])
    rfl).literalDisjoint (by
      simp [checkPositivityStep.LiteralConstructorNamesDisjoint,
        checkPositivityStep.literalConstructorNames])

/-- Header translation preserves the ordered concrete family names. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.typeNames
    (H : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes) :
    decl.types.map (·.name) = types.map (·.name) := by
  have go : ∀ {sources targets},
      List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
          sources targets →
        targets.map (·.name) = sources.map (·.name) := by
    intro sources targets htypes
    induction htypes with
    | nil => rfl
    | cons h _ ih => simp [h.header.name, ih]
  exact go H.types

/-- Once the primitive dispatch shape has been established, its concrete
inductive-constant array satisfies literal disjointness automatically. -/
theorem PrimitiveInductiveShape.checkedLiteralDisjoint
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (Hdecl : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (Hmaterialized : checkInductiveTypes.loopInd.HeaderStatsWF
      env lparams Delta stats decl depth) :
    checkPositivityStep.LiteralDisjoint stats.indConsts := by
  rcases Hshape with ⟨rfl, rfl, rfl, htypes | htypes⟩
  · have hconsts :
        (decl.types.map fun type => Expr.const type.name stats.levels).toArray =
          (types.map fun type => Expr.const type.name stats.levels).toArray := by
      simpa [List.map_map, Function.comp_def] using congrArg
        (fun names =>
          (names.map fun name => Expr.const name stats.levels).toArray)
        Hdecl.typeNames
    rw [Hmaterialized.consts, hconsts, Hmaterialized.levelParams, htypes]
    exact primitiveBoolLiteralDisjoint
  · rcases htypes with ⟨binderName, binderInfo, htypes⟩
    have hconsts :
        (decl.types.map fun type => Expr.const type.name stats.levels).toArray =
          (types.map fun type => Expr.const type.name stats.levels).toArray := by
      simpa [List.map_map, Function.comp_def] using congrArg
        (fun names =>
          (names.map fun name => Expr.const name stats.levels).toArray)
        Hdecl.typeNames
    rw [Hmaterialized.consts, hconsts, Hmaterialized.levelParams, htypes]
    exact primitiveNatLiteralDisjoint

/-- The generated recursor names are not themselves primitive-reserved, even
on the finite `Bool`/`Nat` branch. -/
theorem PrimitiveInductiveShape.recursorsNonprimitive
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    ∀ owner (_howner : owner < types.toArray.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName types.toArray[owner]!.name) := by
  rcases Hshape with ⟨rfl, rfl, rfl, htypes | htypes⟩
  · subst types
    intro owner howner
    have : owner = 0 := by simpa using howner
    subst owner
    simp
    simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList,
      Lean.mkRecName]
  · rcases htypes with ⟨binderName, binderInfo, htypes⟩
    subst types
    intro owner howner
    have : owner = 0 := by simpa using howner
    subst owner
    simp
    simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList,
      Lean.mkRecName]

end VerifyInductive
end Lean4Lean
