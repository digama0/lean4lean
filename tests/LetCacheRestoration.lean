import Lean4Lean.Verify.TypeChecker.Basic
import Lean.Util.CollectAxioms

/-! Erase a local definition over a nonempty dependent context. Retained native
lambdas and lets keep their original model expressions; cache dependency scopes
survive restoration. No arbitrary semantic binder is removed. -/
namespace LetCacheRestorationTest
open Lean Lean4Lean Lean4Lean.TypeChecker

abbrev propositionId : FVarId := ⟨`proposition⟩
abbrev proofId : FVarId := ⟨`proof⟩
abbrev removedId : FVarId := ⟨`removed⟩
abbrev base : VLCtx := [
  (some (proofId, [propositionId]), .vlam (.bvar 0)),
  (some (propositionId, []), .vlam (.sort .zero))]
abbrev extended : VLCtx :=
  (some (removedId, [proofId, propositionId]), .vlet (.bvar 1) (.bvar 0)) :: base

theorem extendedWF : VLCtx.WF VEnv.empty 0 extended := by
  have first : VLCtx.WF VEnv.empty 0
      [(some (propositionId, []), .vlam (.sort .zero))] := by
    refine ⟨trivial, ?_, _, .sort trivial⟩
    intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars]
  have second : VLCtx.WF VEnv.empty 0 base := by
    refine ⟨first, ?_, _, .bvar .zero⟩
    intro fv deps equal
    cases Option.some.inj equal
    simp [VLCtx.fvars, propositionId, proofId]
  refine ⟨second, ?_, .bvar .zero⟩
  intro fv deps equal
  cases Option.some.inj equal
  simp [VLCtx.fvars, base, removedId, propositionId, proofId]

abbrev nested : Expr := .lam `x (.fvar propositionId)
  (.letE `y (.fvar propositionId) (.bvar 0) (.bvar 0) false) .default

theorem nestedTranslation :
    TrExprS VEnv.empty [] extended nested (.lam (.bvar 1) (.bvar 0)) :=
  .lam ⟨_, .bvar (.succ .zero)⟩ (.fvar rfl)
    (.letE (.bvar .zero) (.fvar rfl) (.bvar rfl) (.bvar rfl))

theorem eraseBeneathNativeBinders :
    TrExprS VEnv.empty [] base nested (.lam (.bvar 1) (.bvar 0)) := by
  exact nestedTranslation.eraseLet .zero
    ⟨by simp [FVarsIn, propositionId, removedId],
      by simp [FVarsIn, propositionId, removedId]⟩

theorem restoredSyntax (reserved : ngen.Reserves propositionId) :
    ConditionallyTyped ngen VEnv.empty [] base nested := by
  have cached : ConditionallyTyped ngen VEnv.empty [] extended nested :=
    .mk rfl ⟨reserved, reserved, trivial, trivial⟩ nestedTranslation
  exact cached.weakLet_inv extendedWF

-- The inferred type mentions a distinct variable reached through the proof's
-- dependency list, exercising the up-set argument in cache restoration.
theorem typeBelow : FVarsBelow extended (.fvar proofId) (.fvar propositionId) := by
  intro P up source
  exact up.1.2 source _ (by simp)

theorem restoredType (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    ConditionallyHasType ngen VEnv.empty [] base (.fvar proofId) (.fvar propositionId) := by
  have cached : ConditionallyHasType ngen VEnv.empty [] extended
      (.fvar proofId) (.fvar propositionId) :=
    .mk rfl ⟨typeBelow, .fvar rfl, .fvar rfl, .bvar .zero⟩
      proofReserved propositionReserved
  exact cached.weakLet_inv extendedWF

theorem restoredWHNF (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    ConditionallyWHNF ngen VEnv.empty [] base
      (.letE `alias (.fvar propositionId) (.fvar proofId) (.bvar 0) false) (.fvar proofId) := by
  have below : FVarsBelow extended
      (.letE `alias (.fvar propositionId) (.fvar proofId) (.bvar 0) false) (.fvar proofId) :=
    fun _ _ source => source.2.1
  have source : TrExprS VEnv.empty [] extended
      (.letE `alias (.fvar propositionId) (.fvar proofId) (.bvar 0) false) (.bvar 0) :=
    .letE (.bvar .zero) (.fvar rfl) (.fvar rfl) (.bvar rfl)
  have refl : TrExpr VEnv.empty [] extended (.fvar proofId) (.bvar 0) :=
    ⟨_, .fvar rfl, _, .bvar .zero⟩
  have cached : ConditionallyWHNF ngen VEnv.empty [] extended
      (.letE `alias (.fvar propositionId) (.fvar proofId) (.bvar 0) false) (.fvar proofId) :=
    .mk rfl below source refl ⟨propositionReserved, proofReserved, trivial⟩ proofReserved
  exact cached.weakLet_inv extendedWF

theorem reinsertBeneathNativeBinders :
    TrExprS VEnv.empty [] extended nested (.lam (.bvar 1) (.bvar 0)) := by
  exact eraseBeneathNativeBinders.insertLet .zero
    ⟨by simp [FVarsIn, propositionId, removedId],
      by simp [FVarsIn, propositionId, removedId]⟩

abbrev freshContext (ngen : NameGenerator) : VLCtx :=
  (some (⟨ngen.curr⟩, [proofId, propositionId]), .vlet (.bvar 1) (.bvar 0)) :: base

theorem freshContextWF (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    VLCtx.WF VEnv.empty 0 (freshContext ngen) := by
  refine ⟨extendedWF.1, ?_, .bvar .zero⟩
  intro fv dependencies equal
  cases Option.some.inj equal
  constructor
  · intro member
    simp only [base, VLCtx.fvars_cons_some, VLCtx.fvars_nil, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with equal | equal
    · exact ngen.not_reserves_self (by simpa only [equal] using proofReserved)
    · exact ngen.not_reserves_self (by simpa only [equal] using propositionReserved)
  · simp [VLCtx.fvars, base]

theorem enteredSyntax (reserved : ngen.Reserves propositionId) :
    ConditionallyTyped ngen VEnv.empty [] (freshContext ngen) nested :=
  (restoredSyntax reserved).freshLet

theorem enteredType (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    ConditionallyHasType ngen VEnv.empty [] (freshContext ngen)
      (.fvar proofId) (.fvar propositionId) :=
  (restoredType proofReserved propositionReserved).freshLet

theorem enteredWHNF (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    ConditionallyWHNF ngen VEnv.empty [] (freshContext ngen)
      (.letE `alias (.fvar propositionId) (.fvar proofId) (.bvar 0) false) (.fvar proofId) :=
  (restoredWHNF proofReserved propositionReserved).freshLet

theorem typeRoundTrip (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    ConditionallyHasType ngen VEnv.empty [] base (.fvar proofId) (.fvar propositionId) :=
  (enteredType proofReserved propositionReserved).weakLet_inv
    (freshContextWF proofReserved propositionReserved)

theorem whnfRoundTrip (proofReserved : ngen.Reserves proofId)
    (propositionReserved : ngen.Reserves propositionId) :
    ConditionallyWHNF ngen VEnv.empty [] base
      (.letE `alias (.fvar propositionId) (.fvar proofId) (.bvar 0) false) (.fvar proofId) :=
  (enteredWHNF proofReserved propositionReserved).weakLet_inv
    (freshContextWF proofReserved propositionReserved)

-- Reflexive nodes may mention the fresh identifier. Only the typed leaves
-- require transport, so insertion must not require the whole expression to omit it.
theorem mixedEquivalence : EquivManager.IsDefEqE VEnv.empty [] extended
    (.app (.fvar removedId) (.fvar proofId))
    (.app (.fvar removedId) (.mdata {} (.fvar proofId))) := by
  have typed : EquivManager.IsDefEqE VEnv.empty [] base
      (.fvar proofId) (.mdata {} (.fvar proofId)) :=
    .defeq (.fvar rfl) ⟨_, .mdata (.fvar rfl), _, .bvar .zero⟩
  exact (EquivManager.IsDefEqE.app .rfl typed).insertLet
    (by simp [VLCtx.fvars, base, removedId, proofId, propositionId])

run_meta
  let environment ← getEnv
  let roots := #[``VLCtx.EraseLet.toCtx_eq, ``VLCtx.EraseLet.find?_eq,
    ``TrExprS.eraseLet, ``TrExpr.eraseLet, ``ConditionallyTyped.weakLet_inv,
    ``ConditionallyHasType.weakLet_inv, ``ConditionallyWHNF.weakLet_inv,
    ``extendedWF, ``nestedTranslation, ``eraseBeneathNativeBinders, ``restoredSyntax,
    ``typeBelow, ``restoredType, ``restoredWHNF,
    ``FVarsIn.not_curr, ``TrExprS.insertLet, ``TrExpr.insertLet,
    ``ConditionallyTyped.freshLet, ``ConditionallyHasType.freshLet,
    ``ConditionallyWHNF.freshLet, ``EquivManager.IsDefEqE.insertLet,
    ``EquivManager.WF.insertLet, ``reinsertBeneathNativeBinders, ``freshContextWF,
    ``enteredSyntax, ``enteredType, ``enteredWHNF, ``typeRoundTrip, ``whnfRoundTrip,
    ``mixedEquivalence]
  let forbidden := [``TrProj.weak', ``TrExprS.weakFV, ``TrExprS.weakFV',
    ``ConditionallyTyped.fresh, ``ConditionallyHasType.fresh, ``ConditionallyWHNF.fresh,
    ``EquivManager.IsDefEqE.weak', ``EquivManager.WF.weak', ``TrExprS.weakFV_inv, ``TrExprS.weakFV'_inv,
    ``ConditionallyTyped.weakN_inv, ``ConditionallyHasType.weakN_inv,
    ``ConditionallyWHNF.weakN_inv, ``TrExprS.uniq,
    ``VEnv.IsDefEqU.weakN_iff, ``VEnv.IsDefEq.weakN_iff, ``VEnv.HasType.weakN_iff,
    `Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS, `Lean4Lean.VEnv.IsDefEq.church_rosser,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj]
  for name in roots do
    let info ← getConstInfo name
    if info matches .axiomInfo _ then throwError "new let erasure axiom {name}"
    let some value := info.value? (allowOpaque := true) | throwError "missing proof {name}"
    if value.hasSorry then throwError "direct let erasure admission {name}"
    let expected := if name == ``FVarsIn.not_curr then []
      else if name == ``VLCtx.EraseLet.toCtx_eq || name == ``typeBelow then
        [``propext]
      else if name == ``VLCtx.EraseLet.find?_eq then [``propext, ``Quot.sound]
      else if name == ``extendedWF || name == ``freshContextWF then [``propext, ``Quot.sound, ``Classical.choice]
      else [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
    let axioms ← collectAxioms name
    unless expected.length == axioms.size && expected.all axioms.contains do
      throwError "let erasure axiom manifest changed for {name}: {repr axioms}"
    for dependency in axioms do
      unless expected.contains dependency do
        throwError "unexpected let erasure axiom {dependency} in {name}"
    logInfo m!"{name}: {repr (← collectAxioms name)}"
  let inherited := [``TrProj]
  let mut pending := roots
  let mut visited : NameSet := {}
  let mut admissions : Array Name := #[]
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "forbidden let erasure dependency {name}"
    if let some info := environment.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        if value.hasSorry then
          unless inherited.contains name do throwError "unapproved let erasure admission {name}"
          admissions := admissions.push name
        pending := pending ++ value.getUsedConstants
  unless pending.isEmpty do throwError "let erasure traversal exceeded bound"
  unless inherited.all admissions.contains && admissions.size == inherited.length do
    throwError "let erasure admission manifest changed: {repr admissions}"
  logInfo m!"{visited.size} let erasure dependencies; exact inherited admissions {repr admissions}"
  let restorationConsumers := [``RecM.WF.withLetDecl]
  let insertionConsumers : List Name := []
  for consumer in restorationConsumers ++ insertionConsumers do
    let some value := (← getConstInfo consumer).value? (allowOpaque := true)
      | throwError "missing actual let restoration {consumer}"
    if value.hasSorry then throwError "direct actual let restoration admission {consumer}"
    let direct := value.getUsedConstants
    let required := if insertionConsumers.contains consumer then
        [``ConditionallyHasType.freshLet, ``ConditionallyWHNF.freshLet, ``EquivManager.WF.insertLet]
      else [``ConditionallyHasType.weakLet_inv, ``ConditionallyWHNF.weakLet_inv]
    let required := if consumer == ``RecM.WF.withLetDecl then
        required ++ [``ConditionallyHasType.freshLet, ``ConditionallyWHNF.freshLet,
          ``EquivManager.WF.insertLet]
      else required
    for helper in required do
      unless direct.contains helper do throwError "actual let restoration {consumer} lost {helper}"
    for name in forbidden do
      if direct.contains name then throwError "actual let restoration {consumer} directly uses {name}"
    let consumerInherited := [``TrProj, ``VEnv.addInduct_WF,
      ``VEnv.addInduct, ``VInductDecl.WF]
    let expectedAxioms := [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx,
      ``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
      ``Lean.PersistentHashMap.WF.toList'_insert]
    let actualAxioms ← collectAxioms consumer
    unless expectedAxioms.length == actualAxioms.size && expectedAxioms.all actualAxioms.contains do
      throwError "actual let restoration axiom manifest changed: {repr actualAxioms}"
    let mut consumerPending := #[consumer]
    let mut consumerVisited : NameSet := {}
    let mut consumerAdmissions : Array Name := #[]
    for _ in [:1000000] do
      if consumerPending.isEmpty then break
      let name := consumerPending.back!
      consumerPending := consumerPending.pop
      if consumerVisited.contains name then continue
      consumerVisited := consumerVisited.insert name
      if forbidden.contains name then throwError "forbidden actual let restoration dependency {name}"
      if let some info := environment.find? name then
        consumerPending := consumerPending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          if value.hasSorry then
            unless consumerInherited.contains name do
              throwError "unapproved actual let restoration admission {name}"
            consumerAdmissions := consumerAdmissions.push name
          consumerPending := consumerPending ++ value.getUsedConstants
    unless consumerPending.isEmpty do throwError "actual let restoration traversal exceeded bound"
    unless consumerInherited.all consumerAdmissions.contains && consumerAdmissions.size == consumerInherited.length do
      throwError "actual let restoration admission manifest changed: {repr consumerAdmissions}"
    logInfo m!"{consumer}: {consumerVisited.size} dependencies; exact inherited admissions {repr consumerAdmissions}"

end LetCacheRestorationTest
