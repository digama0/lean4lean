import Lean4Lean.Verify.Inductive.Constructor.Positivity

/-! The literal branch of the positivity check: literal expansion exposes only a
fixed finite set of constants (`literalConstructorNames`), so it cannot
mention a family of a block whose names avoid that set. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkPositivityStep

/-- The complete finite set of constant names exposed by constructor
expansion of natural-number and string literals. -/
def literalConstructorNames : List Name :=
  [``Nat.zero, ``Nat.succ, ``String.ofList, ``Char, ``List.nil,
    ``List.cons, ``Char.ofNat]

/-- None of the mutually defined family names is one of the constants that
literal expansion can expose to the positivity checker. -/
def LiteralConstructorNamesDisjoint (names : List Name) : Prop :=
  ∀ name ∈ literalConstructorNames, names.contains name = false

/-- The exact inductive-constant array and finite name disjointness together
discharge the literal branch of positivity.  This makes the executable
premise depend only on the source family names, not on mutable checker state. -/
theorem IndConstArray.literalDisjoint
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (H : IndConstArray levels indConsts names)
    (hdisjoint : LiteralConstructorNamesDisjoint names) :
    LiteralDisjoint indConsts := by
  have hNatZero : ``Nat.zero ∉ names := by
    simpa using hdisjoint ``Nat.zero (by simp [literalConstructorNames])
  have hNatSucc : ``Nat.succ ∉ names := by
    simpa using hdisjoint ``Nat.succ (by simp [literalConstructorNames])
  have hStringOfList : ``String.ofList ∉ names := by
    simpa using hdisjoint ``String.ofList (by simp [literalConstructorNames])
  have hChar : ``Char ∉ names := by
    simpa using hdisjoint ``Char (by simp [literalConstructorNames])
  have hListNil : ``List.nil ∉ names := by
    simpa using hdisjoint ``List.nil (by simp [literalConstructorNames])
  have hListCons : ``List.cons ∉ names := by
    simpa using hdisjoint ``List.cons (by simp [literalConstructorNames])
  have hCharOfNat : ``Char.ofNat ∉ names := by
    simpa using hdisjoint ``Char.ofNat (by simp [literalConstructorNames])
  intro literal
  rw [hasIndOcc_eq_findAny]
  let p : Expr → Bool := fun x => match x with
    | Expr.const name _ => indConsts.any fun I => I.constName! == name
    | _ => false
  let q : Expr → Bool := fun x => match x with
    | Expr.const name _ => names.contains name
    | _ => false
  change Expr.findAny p literal.toConstructor = false
  have hpred : p = q := by
    funext x
    cases x <;> try rfl
    exact H.names _
  rw [hpred]
  change Expr.findAny
      (fun x : Expr => match x with
        | Expr.const name _ => names.contains name
        | _ => false) literal.toConstructor = false
  cases literal with
  | natVal n =>
      cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor,
        Expr.natZero, Expr.natSucc, Expr.findAny, hNatZero,
        hNatSucc]
  | strVal s =>
      simp [Literal.toConstructor, Expr.strLitToConstructor, Expr.findAny,
        hStringOfList]
      induction s.toList <;> simp_all [Expr.findAny]

/-- Natural-number literal expansion only exposes the two reserved natural
constructors.  This local form remains usable while the prelude is declared
and string-literal support is not yet available. -/
theorem IndConstArray.natLiteralDisjoint
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (H : IndConstArray levels indConsts names)
    (hzero : ``Nat.zero ∉ names) (hsucc : ``Nat.succ ∉ names)
    (n : Nat) :
    AddInductive.hasIndOcc indConsts (Literal.natVal n).toConstructor = false := by
  rw [hasIndOcc_eq_findAny]
  let p : Expr → Bool := fun x => match x with
    | Expr.const name _ => indConsts.any fun I => I.constName! == name
    | _ => false
  let q : Expr → Bool := fun x => match x with
    | Expr.const name _ => names.contains name
    | _ => false
  change Expr.findAny p (Literal.natVal n).toConstructor = false
  have hpred : p = q := by
    funext x
    cases x <;> try rfl
    exact H.names _
  rw [hpred]
  cases n <;> simp [q, Literal.toConstructor, Expr.natLitToConstructor,
    Expr.natZero, Expr.natSucc, Expr.findAny, hzero, hsucc]

end checkPositivityStep

/-- The header checks expose the exact family-name array, so the finite
source-name condition is sufficient at every downstream positivity call. -/
theorem checkInductiveTypes.loopInd.HeaderStatsWF.literalDisjoint
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      env Us Delta stats decl depth)
    (hdisjoint : checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name))) :
    checkPositivityStep.LiteralDisjoint stats.indConsts := by
  have hconsts : stats.indConsts =
      ((decl.types.map (·.name)).map fun name =>
        Expr.const name stats.levels).toArray := by
    simpa [List.map_map, Function.comp_def] using H.consts
  have Harray : checkPositivityStep.IndConstArray stats.levels
      stats.indConsts (decl.types.map (·.name)) :=
    checkPositivityStep.IndConstArray.ofExact hconsts
  exact Harray.literalDisjoint hdisjoint

/-- Checked family constants cannot occur in a natural-number literal
when neither reserved natural constructor is a family name. -/
theorem checkInductiveTypes.loopInd.HeaderStatsWF.natLiteralDisjoint
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      env Us Delta stats decl depth)
    (hzero : ``Nat.zero ∉ decl.types.map (·.name))
    (hsucc : ``Nat.succ ∉ decl.types.map (·.name))
    (n : Nat) :
    AddInductive.hasIndOcc stats.indConsts
      (Literal.natVal n).toConstructor = false := by
  have hconsts : stats.indConsts =
      ((decl.types.map (·.name)).map fun name =>
        Expr.const name stats.levels).toArray := by
    simpa [List.map_map, Function.comp_def] using H.consts
  exact (checkPositivityStep.IndConstArray.ofExact hconsts).natLiteralDisjoint
    hzero hsucc n

end VerifyInductive
end Lean4Lean
