import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

/-! Literal-name side conditions of the positivity check, in the header environment: no
family is a kernel-reserved primitive name, and the three literal expansion names that the
kernel does not reserve are excluded once string-literal support is present. Ported from the
source branch's `Install/LiteralNames.lean`, stated over the header interface. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {outEnv : Environment} {name : Name}

/-- Literal expansion names which are not reserved by
`Kernel.Environment.primitives`.  Unlike the other four literal names, these
cannot be excluded solely from a successful ordinary `checkName`. -/
def checkPositivityStep.unreservedLiteralConstructorNames : List Name :=
  [``Char, ``List.nil, ``List.cons]

/-- The exact residual literal-name condition left after successful ordinary
header installation has excluded every primitive-reserved name. -/
def checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
    (names : List Name) : Prop :=
  ∀ name ∈ unreservedLiteralConstructorNames, names.contains name = false

/-- Once string-literal support is present, `HasPrimitives` and orderedness
recover all three non-reserved constants used by literal expansion. -/
theorem unreservedLiteralConstructorsOfStringOfList
    {env : VEnv}
    (H : env.HasPrimitives) (hwf : env.OrderedStrong)
    (hstring : env.contains ``String.ofList) :
    ∀ name ∈ checkPositivityStep.unreservedLiteralConstructorNames,
      env.contains name := by
  intro name hname
  simp only [checkPositivityStep.unreservedLiteralConstructorNames,
    List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl
  · have HlistChar :=
      (TrExprS.listChar hwf H hstring (Us := []) (Δ := [])).1
    let .app _ _ _ Hchar := HlistChar
    let .const hlookup _ _ := Hchar
    exact ⟨_, hlookup⟩
  · have Hnil :=
      (TrExprS.listCharNil hwf H hstring (Us := []) (Δ := [])).1
    let .app _ _ HnilConst _ := Hnil
    let .const hlookup _ _ := HnilConst
    exact ⟨_, hlookup⟩
  · have Hcons :=
      (TrExprS.listCharCons hwf H hstring (Us := []) (Δ := [])).1
    let .app _ _ HconsConst _ := Hcons
    let .const hlookup _ _ := HconsConst
    exact ⟨_, hlookup⟩

/-- Primitive support visible in the header environment was already present in the source
environment: the family names are not primitive. -/
theorem HeaderEnvironment.sourceContainsOfTargetContainsPrimitive
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv)
    (hnprim : ∀ T ∈ decl.types, ¬ Kernel.Environment.primitives.contains T.name)
    (hprimitive : Kernel.Environment.primitives.contains name)
    (htarget : H.context.venv.contains name) : sourceEnv.contains name := by
  obtain ⟨ci, hci⟩ := htarget
  rcases VEnv.addConstVals_lookup_cases H.typesAdded hci with h | ⟨v, hv, hn, -⟩
  · exact ⟨ci, h⟩
  · exfalso
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hv
    exact hnprim T hT (hn ▸ hprimitive)

/-- The family names avoid every name present in the source environment. -/
theorem HeaderEnvironment.familyNamesFresh
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv)
    (hpresent : sourceEnv.contains name) : name ∉ decl.types.map (·.name) := by
  intro hmem
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hmem
  have := (VEnv.addConstVals_names_fresh H.typesAdded).2 T.toVConstVal
    (List.mem_map_of_mem hT)
  obtain ⟨ci, hci⟩ := hpresent
  rw [this] at hci; cases hci

/-- The header environment supplies positivity's environment-indexed literal side
condition. -/
theorem HeaderEnvironment.checkedAvailableLiteralDisjoint
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv)
    (hnprim : ∀ T ∈ decl.types, ¬ Kernel.Environment.primitives.contains T.name) :
    checkPositivityStep.AvailableLiteralDisjoint H.context.venv stats.indConsts := by
  have hexcl : ∀ {name}, Kernel.Environment.primitives.contains name →
      name ∉ decl.types.map (·.name) := by
    intro name hp hmem
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hmem
    exact hnprim T hT hp
  intro literal havailable
  cases literal with
  | natVal n =>
    exact H.statsWF.natLiteralDisjoint
      (hexcl (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]))
      (hexcl (by simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])) n
  | strVal s =>
    have hsourceString : sourceEnv.contains ``String.ofList :=
      H.sourceContainsOfTargetContainsPrimitive hnprim (by
        simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]) havailable.2
    have hsrcWF : sourceEnv.WF := by rw [← H.sourceContextVEnv]; exact H.sourceContext.wf
    have hsrcPrim : sourceEnv.HasPrimitives := by
      rw [← H.sourceContextVEnv]; exact H.sourceContext.checking.hasPrimitives
    have hunreserved := unreservedLiteralConstructorsOfStringOfList hsrcPrim
      hsrcWF.orderedStrong hsourceString
    have hliteral : checkPositivityStep.LiteralConstructorNamesDisjoint
        (decl.types.map (·.name)) := by
      intro name hname
      simp only [checkPositivityStep.literalConstructorNames,
        List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using hexcl (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
      · simpa using hexcl (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
      · simpa using hexcl (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
      · simpa using H.familyNamesFresh (hunreserved ``Char (by
          simp [checkPositivityStep.unreservedLiteralConstructorNames]))
      · simpa using H.familyNamesFresh (hunreserved ``List.nil (by
          simp [checkPositivityStep.unreservedLiteralConstructorNames]))
      · simpa using H.familyNamesFresh (hunreserved ``List.cons (by
          simp [checkPositivityStep.unreservedLiteralConstructorNames]))
      · simpa using hexcl (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
    exact H.statsWF.literalDisjoint hliteral (.strVal s)

end VerifyInductive
end Lean4Lean
