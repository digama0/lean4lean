import Lean4Lean.Verify.InductiveEliminationLevel
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveEliminationLevelTest

example (names : List Name) : freshElimName names ∉ names :=
  freshElimName.not_mem names

example (names : List Name) (index : Nat) :
    ∃ selected, index ≤ selected ∧ freshElimName.loop names index = freshElimName.candidate selected ∧
      freshElimName.candidate selected ∉ names ∧
      ∀ earlier, index ≤ earlier → earlier < selected → freshElimName.candidate earlier ∈ names :=
  freshElimName.loop.spec names index

example (stats : InductiveStats) (types : Array InductiveType) (reader : Context)
    (distinct : reader.lparams.Nodup) :
    (getElimLevel stats types reader).WF fun level =>
      (getRecLevelParams level reader.lparams).Nodup ∧
      VLevel.ofLevel (getRecLevelParams level reader.lparams) level =
        some (if level.isParam then .param 0 else .zero) :=
  getElimLevel.recLevelParams stats types reader distinct

private def legacyLoop (names : List Name) (current : Name) (index : Nat) : Nat → Option Name
  | 0 => none
  | fuel + 1 =>
    if names.contains current then
      legacyLoop names ((`u).appendIndexAfter index) (index + 1) fuel
    else
      some current

private def checkNames (names : List Name) (expected : Name) : MetaM Unit := do
  let actual := freshElimName names
  unless actual == expected && !names.contains actual do
    throwError "fresh elimination name changed its first-unused result"
  unless legacyLoop names `u 1 (names.length + 2) == some actual do
    throwError "total name search disagrees with the original appendIndexAfter loop"

private def nameControls : MetaM Unit := do
  let noise := [Name.anonymous, .num .anonymous 37, `u_0, `u_01, `u_001,
    `Other.u, `Other.u_1, `u.u_2, `unrelated, .str .anonymous "u_λ"]
  checkNames noise `u
  checkNames [`u_1, `u_2, `u_3] `u
  let mut checked : Nat := 2
  for blocked in [:65] do
    let blockedNames := `u :: (List.range blocked).map (fun index => (`u).appendIndexAfter (index + 1))
    let expected := (`u).appendIndexAfter (blocked + 1)
    for names in [blockedNames, blockedNames.reverse ++ noise, noise ++ blockedNames ++ blockedNames] do
      checkNames names expected
      checked := checked + 1
    for hole in [1:blocked + 1] do
      let names := blockedNames.filter (· != (`u).appendIndexAfter hole)
      checkNames (noise ++ names.reverse ++ noise) ((`u).appendIndexAfter hole)
      checked := checked + 1
  for blocked in [99, 100, 999, 1000, 2048] do
    let names := `u :: (List.range blocked).map (fun index => (`u).appendIndexAfter (index + 1))
    checkNames names ((`u).appendIndexAfter (blocked + 1))
    checked := checked + 1
  for index in [:2049] do
    unless freshElimName.candidate index == (`u).appendIndexAfter index do
      throwError "verified string append disagrees with native indexed-name rendering"
  for digits in [1:33] do
    for index in [10 ^ digits - 1, 10 ^ digits, 10 ^ digits + 1] do
      unless freshElimName.candidate index == (`u).appendIndexAfter index do
        throwError "large decimal indexed-name rendering changed"
      checkNames [freshElimName.candidate index, `u] `u_1
      checked := checked + 1
  logInfo m!"{checked} first-unused collision/order/duplicate/noise controls pass; candidate rendering agrees with the former opaque native helper at 2049 consecutive indices and 96 large decimal boundaries; search adds no fuel rejection"

private def checkLevel (reader : Context) (stats : InductiveStats) (types : Array InductiveType)
    (large : Bool) : MetaM Unit := do
  let .ok accepted := isLargeEliminator stats types reader
    | throwError "large-elimination classifier unexpectedly failed"
  unless accepted == large do throwError "large-elimination classifier changed"
  let expected := if large then Level.param (freshElimName reader.lparams) else .zero
  let .ok level := getElimLevel stats types reader
    | throwError "total elimination-level selection unexpectedly failed"
  unless level == expected do throwError "elimination-level selection changed"
  let params := getRecLevelParams level reader.lparams
  unless params == (if large then freshElimName reader.lparams :: reader.lparams else reader.lparams) do
    throwError "recursor universe parameter order changed"

private def checkFrontend (reader : Context) (declaration : InductiveType) (large : Bool) : MetaM Unit := do
  let .ok extended := run 0 [declaration] 0 reader
    | throwError "actual declaration frontend rejects elimination-level control {declaration.name}"
  let some (.recInfo recursor) := extended.find? (mkRecName declaration.name)
    | throwError "actual frontend lost generated recursor"
  let expected := if large then freshElimName reader.lparams :: reader.lparams else reader.lparams
  unless recursor.levelParams == expected do
    throwError "actual generated recursor changed elimination universes"

private def frontendControls : MetaM Unit := do
  let host ← getEnv
  let mut checked : Nat := 0
  for safety in [DefinitionSafety.safe, .unsafe] do
    for allowPrimitive in [false, true] do
      for names in [[], [`u], [`u, `u_1, `u_3], [`u_1, `u_2], [`u, `u_1, `u_2, `u_3]] do
        let reader : Context := { env := host.toKernelEnv, lparams := names, safety, allowPrimitive }
        let stats : InductiveStats := {
          levels := names.map Level.param, resultLevel := .zero,
          indConsts := #[], params := #[], isNotZero := false }
        let empty : InductiveType := { name := `ElimEmpty, type := .sort .zero, ctors := [] }
        checkLevel reader stats #[] false
        checkLevel reader stats #[empty] true
        checkLevel reader stats #[empty, { empty with name := `ElimOther }] false
        checkLevel { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
          { stats with isNotZero := true } #[] true
        let ctor : Constructor := { name := `ElimEmpty.intro, type := .const empty.name stats.levels }
        checkLevel reader stats #[{ empty with ctors := [ctor] }] true
        checkLevel reader stats #[{ empty with ctors := [ctor, { ctor with name := `ElimEmpty.other }] }] false
        let exhausted := { reader with fuel := { reader.fuel with inductiveFuel := 0 } }
        match getElimLevel stats #[{ empty with ctors := [ctor] }] exhausted with
        | .error .deepRecursion => pure ()
        | _ => throwError "classifier recursion failure no longer propagates unchanged"
        checkFrontend reader empty true
        let unit : InductiveType := {
          name := `ElimUnit, type := .sort .zero,
          ctors := [{ name := `ElimUnit.intro, type := .const `ElimUnit stats.levels }] }
        checkFrontend reader unit true
        let data : InductiveType := {
          name := `ElimData, type := .sort .zero,
          ctors := [{
            name := `ElimData.intro
            type := .forallE `value (.const ``Nat []) (.const `ElimData stats.levels) .default }] }
        checkFrontend reader data false
        let proof : InductiveType := {
          name := `ElimProof, type := .sort .zero,
          ctors := [{
            name := `ElimProof.intro
            type := .forallE `value (.const ``True []) (.const `ElimProof stats.levels) .default }] }
        checkFrontend reader proof true
        let indexed : InductiveType := {
          name := `ElimIndexed, type := .forallE `index (.const ``Nat []) (.sort .zero) .default,
          ctors := [{
            name := `ElimIndexed.intro
            type := .forallE `value (.const ``Nat [])
              (.app (.const `ElimIndexed stats.levels) (.bvar 0)) .default }] }
        checkFrontend reader indexed true
        checked := checked + 1
  logInfo m!"{checked * 5} actual empty/unit/data/proof/indexed frontend recursors and {checked * 6} classifier/selection controls retain fresh leading universes, small/mutual elimination, safe/unsafe modes, primitive flags and classifier fuel failures"

run_meta
  let environment ← getEnv
  let mut owned : Nat := 0
  for moduleName in [`Lean4Lean.Inductive.ElimName, `Lean4Lean.Verify.InductiveEliminationLevel] do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwError "elimination-level module absent"
    for (name, information) in environment.constants do
      if environment.getModuleIdxFor? name == some moduleIndex then
        if information matches .axiomInfo _ then throwError "new elimination-level axiom {name}"
        for dependency in (← collectAxioms name) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
            throwError "unexpected elimination-level dependency {dependency} in {name}"
        owned := owned + 1
  for name in [``getElimLevel, ``freshElimName, ``freshElimName.loop] do
    let some information := environment.find? name | throwError "actual selector absent"
    if information matches .opaqueInfo _ then throwError "actual selector remains partial/opaque: {name}"
    for dependency in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "actual selector gained an unverified dependency {dependency}"
  logInfo m!"{owned} owned public/private/generated elimination-name and level proof values have only propext/Classical.choice/Quot.sound dependencies, with no admission or new interface axiom; actual getElimLevel is total and has an equation theorem"
  nameControls
  frontendControls

end InductiveEliminationLevelTest
