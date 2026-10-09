import Lean4Lean.Verify.Inductive.Install.Environments
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

/-! Literal-name side conditions of the positivity check.  A successful ordinary
header installation excludes every kernel-reserved primitive name; the three
literal expansion names that the kernel does not reserve are excluded once
string-literal support is present. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

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
    (H : env.HasPrimitives) (hwf : env.Ordered)
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

/-- An ordinary installed family cannot use a kernel-reserved primitive
name.  This is the exact reusable consequence of successful `checkName` for
the header family-name list. -/
theorem HeaderEnvironment.familyNamesExcludePrimitive
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hprimitive : Kernel.Environment.primitives.contains name) :
    name ∉ decl.types.map (·.name) := by
  intro hmem
  have hvalue : name ∈
      (H.entries.map Prod.snd).map VConstVal.name := by
    rw [H.values]
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using hmem
  exact H.installed.valueNamesNonprimitive name hvalue hprimitive

/-- Successful ordinary header installation excludes every literal expansion
name except the three names not reserved by the kernel. -/
theorem HeaderEnvironment.literalNamesDisjointOfUnreserved
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hunreserved :
      checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
        (decl.types.map (·.name))) :
    checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  intro name hliteral
  simp only [checkPositivityStep.literalConstructorNames, List.mem_cons,
    List.not_mem_nil, or_false] at hliteral
  rcases hliteral with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact excludePrimitive (by
      simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
  · exact excludePrimitive (by
      simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
  · exact excludePrimitive (by
      simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
  · exact hunreserved ``Char (by
      simp [checkPositivityStep.unreservedLiteralConstructorNames])
  · exact hunreserved ``List.nil (by
      simp [checkPositivityStep.unreservedLiteralConstructorNames])
  · exact hunreserved ``List.cons (by
      simp [checkPositivityStep.unreservedLiteralConstructorNames])
  · exact excludePrimitive (by
      simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
  where
    excludePrimitive {name : Name}
        (hprimitive : Kernel.Environment.primitives.contains name) :
        (decl.types.map (·.name)).contains name = false := by
      simpa using H.familyNamesExcludePrimitive hprimitive

/-- If the three unreserved expansion names already exist in the abstract
source environment, successful fresh header installation discharges the
residual condition too. -/
theorem HeaderEnvironment.unreservedLiteralNamesDisjointOfSourceContains
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hpresent : ∀ name ∈
      checkPositivityStep.unreservedLiteralConstructorNames,
      sourceEnv.contains name) :
    checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  have hfresh := (VEnv.addConstVals_names_fresh H.installed.abstract).2
  intro name hname
  have hnotMem : name ∉ decl.types.map (·.name) := by
    intro hmem
    rcases hpresent name hname with ⟨ci, hlookup⟩
    have hconstant : ∃ value ∈ decl.typeConstants,
        value.name = name := by
      rcases List.mem_map.mp hmem with ⟨type, htype, htypeName⟩
      refine ⟨type.toVConstVal, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨type, htype, rfl⟩
      · simpa using htypeName
    rcases hconstant with ⟨value, hvalue, hvalueName⟩
    have hentryValue : value ∈ H.entries.map Prod.snd := by
      rw [H.values]
      exact hvalue
    have habsent := hfresh value hentryValue
    rw [hvalueName, hlookup] at habsent
    contradiction
  simpa using hnotMem

/-- In an environment where the unreserved literal constants are already
present, ordinary header installation supplies the global condition
without any caller premise. -/
theorem HeaderEnvironment.literalNamesDisjointOfSourceContains
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hpresent : ∀ name ∈
      checkPositivityStep.unreservedLiteralConstructorNames,
      sourceEnv.contains name) :
    checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) :=
  H.literalNamesDisjointOfUnreserved
    (H.unreservedLiteralNamesDisjointOfSourceContains hpresent)

/-- After string-literal support has been installed, the existing checking
context supplies the residual source-presence condition automatically. -/
theorem HeaderEnvironment.literalNamesDisjointOfStringOfList
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hstring : sourceEnv.contains ``String.ofList) :
    checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  apply H.literalNamesDisjointOfSourceContains
  rw [← H.sourceContextVEnv] at hstring ⊢
  exact unreservedLiteralConstructorsOfStringOfList
    H.sourceContext.checking.hasPrimitives
    H.sourceContext.checking.tr.wf hstring

/-- A primitive lookup visible after ordinary header installation was already
present in the source environment: all newly installed header values have
non-primitive names. -/
theorem HeaderEnvironment.sourceContainsOfTargetContainsPrimitive
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hprimitive : Kernel.Environment.primitives.contains name)
    (htarget : H.context.venv.contains name) :
    sourceEnv.contains name := by
  rcases htarget with ⟨ci, hlookup⟩
  refine ⟨ci, ?_⟩
  rw [VEnv.addConstVals_constants_of_forall_ne H.installed.abstract ?_] at hlookup
  · exact hlookup
  · intro value hvalue hname
    apply H.installed.valueNamesNonprimitive value.name
      (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
    simpa [hname] using hprimitive

/-- The actual literal premise needed by positivity is automatic for every
ordinary declaration, including the prelude's declaration of `Char`.  Natural
literals only expose reserved natural constructors.  A supported string
literal implies that the reserved `String.ofList` lookup predates this
ordinary header batch; `HasPrimitives`, orderedness, and source freshness then
exclude the remaining `Char`/`List` expansion names. -/
theorem HeaderEnvironment.checkedAvailableLiteralDisjoint
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv) :
    checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts := by
  intro literal havailable
  cases literal with
  | natVal n =>
      exact H.statsWF.natLiteralDisjoint
        (H.familyNamesExcludePrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]))
        (H.familyNamesExcludePrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])) n
  | strVal s =>
      have hsourceString : sourceEnv.contains ``String.ofList :=
        H.sourceContainsOfTargetContainsPrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
          havailable.2
      exact H.statsWF.literalDisjoint
        (H.literalNamesDisjointOfStringOfList hsourceString) (.strVal s)

end VerifyInductive
end Lean4Lean
