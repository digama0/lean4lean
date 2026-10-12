import Lean4Lean.Verify.Inductive.Header.Check

/-! # The header fold: `declareInductiveTypeInfos`

`AddInductive.declareInductiveTypes` adds the kernel headers (`inductiveTypeInfos`) one at a
time, each after a successful `checkName`. This file verifies that fold: unconditionally its
structural effect on the constant map (`declareInfos_structural`), and, when the constructor
names the new headers list are absent and distinct from the header names, that every
intermediate environment is a checking environment for the abstract environment with the
translated headers added (`declareInfos_valid`: `CheckingEnv.Valid`, `RecursorShapesCoherent`,
`IotaRulesRegistered`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
namespace HeaderInstallation

/-- The constructor names the headers of a block list. -/
def listedNames (indTypes : Array InductiveType) : List Name :=
  indTypes.toList.flatMap fun owner => owner.ctors.map (·.name)

theorem mem_listedNames {indTypes : Array InductiveType} {n : Name} :
    n ∈ listedNames indTypes ↔ ∃ owner ∈ indTypes.toList, ∃ ctor ∈ owner.ctors, ctor.name = n := by
  simp [listedNames]

/-- A lookup in the constant map of a fresh extension. -/
theorem constFind_add_cases {env : Environment} (hwf : env.constants.WF)
    {ci : ConstantInfo} (hn : env.find? ci.name = none) {n : Name} {found : ConstantInfo}
    (h : (env.add ci).constants.find? n = some found) :
    (n = ci.name ∧ found = ci) ∨ env.constants.find? n = some found := by
  have hnMap : env.constants.find? ci.name = none := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
  change (env.constants.insert ci.name ci).find? n = some found at h
  rw [hwf.find?_insert] at h
  split at h
  · exact .inl ⟨(LawfulBEq.eq_of_beq (by assumption)).symm, (Option.some.inj h).symm⟩
  · exact .inr h

/-- The self lookup of a fresh extension. -/
theorem find_add_self {env : Environment} (hwf : env.constants.WF)
    {ci : ConstantInfo} (hn : env.find? ci.name = none) :
    (env.add ci).find? ci.name = some ci := by
  have hnMap : env.constants.find? ci.name = none := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
  change (env.constants.insert ci.name ci).find?' ci.name = some ci
  rw [(hwf.insert ci.name ci hnMap).find?'_eq_find?, hwf.find?_insert]
  simp

theorem RecursorShapes.mono {C C' : ConstMap} {venv venv' : VEnv} {rec : RecursorVal}
    (hle : venv ≤ venv')
    (hctor : ∀ {n cval}, C'.find? n = some (.ctorInfo cval) → C.find? n = some (.ctorInfo cval))
    (H : RecursorShapes C venv rec) : RecursorShapes C' venv' rec := by
  obtain ⟨cnparams, indLevels, ctorParams, ⟨S⟩, hrules⟩ := H
  refine ⟨cnparams, indLevels, ctorParams, ⟨{ S with const := hle.constants S.const }⟩, ?_⟩
  intro rule hrule
  obtain ⟨ctorUvars, hlen, ⟨T⟩, hc⟩ := hrules rule hrule
  exact ⟨ctorUvars, hlen, ⟨{ T with const := hle.constants T.const }⟩,
    fun cval h => hc cval (hctor h)⟩

/-- Recursor shapes survive a fresh constant that is neither a constructor nor a recursor. -/
theorem shapes_add {safety : DefinitionSafety} {env : Environment} {venv venv' : VEnv}
    (H : RecursorShapesCoherent safety env.constants venv) (hwf : env.constants.WF)
    {ci : ConstantInfo} (hn : env.find? ci.name = none)
    (hnctor : ∀ v, ci ≠ .ctorInfo v) (hnrec : ∀ v, ci ≠ .recInfo v) (hle : venv ≤ venv') :
    RecursorShapesCoherent safety (env.add ci).constants venv' := by
  intro name rec hfind hsafe
  rcases constFind_add_cases hwf hn hfind with ⟨-, h⟩ | hold
  · exact absurd h.symm (hnrec rec)
  · refine RecursorShapes.mono hle ?_ (H hold hsafe)
    intro n cval h
    rcases constFind_add_cases hwf hn h with ⟨-, h'⟩ | h'
    · exact absurd h'.symm (hnctor cval)
    · exact h'

/-- Registered ι rules survive a fresh constant that is not a recursor. -/
theorem iota_add {safety : DefinitionSafety} {env : Environment} {venv venv' : VEnv}
    (H : IotaRulesRegistered safety env venv) (hwf : env.constants.WF)
    {ci : ConstantInfo} (hn : env.find? ci.name = none)
    (hnrec : ∀ v, ci ≠ .recInfo v) (hle : venv ≤ venv') :
    IotaRulesRegistered safety (env.add ci) venv' := by
  intro recName cName rval rule hrec hrule hsafe
  rcases findAddFresh_cases hwf ci hn hrec with ⟨-, h⟩ | hold
  · exact absurd h.symm (hnrec rval)
  · obtain ⟨cval, rhs, hc, hcval, htr, hpat⟩ := H hold hrule hsafe
    exact ⟨cval, rhs, hc, findAddFresh_of_find hwf ci hn hcval, htr.mono hle, hle.pats hpat⟩

/-- The structural effect of the header fold. -/
theorem declareInfos_structural (allow : Bool) :
    ∀ (infos : List InductiveVal) (env : Environment), env.constants.WF →
    (AddInductive.declareInductiveTypeInfos allow infos env).WF fun out =>
      out.constants.WF ∧
      out.constants = insertConsts env.constants (infos.map .inductInfo) ∧
      out.quotInit = env.quotInit ∧
      (∀ info ∈ infos, env.find? info.name = none) ∧
      (∀ {n c}, env.find? n = some c → out.find? n = some c) ∧
      (∀ info ∈ infos, out.find? info.name = some (.inductInfo info)) ∧
      (∀ info ∈ infos, Kernel.Environment.primitives.contains info.name → allow = true)
  | [], env, hwf => Except.WF.pure ⟨hwf, rfl, rfl, by simp, id, by simp, by simp⟩
  | info :: infos, env, hwf => by
    rw [AddInductive.declareInductiveTypeInfos]
    refine (checkName.WF hwf info.name allow).bind fun _ ⟨hn, hprim⟩ => ?_
    have hn' : env.find? (ConstantInfo.inductInfo info).name = none := hn
    have hnMap : env.constants.find? info.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hwf' : (env.add (.inductInfo info)).constants.WF := hwf.insert _ _ hnMap
    refine (declareInfos_structural allow infos (env.add (.inductInfo info)) hwf').mono
      fun out ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_
    refine ⟨h1, h2, h3, ?_, fun h => h5 (findAddFresh_of_find hwf _ hn' h), ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hn
      · have := h4 i hi
        cases h : env.find? i.name with
        | none => rfl
        | some c => rw [findAddFresh_of_find hwf _ hn' h] at this; cases this
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact h5 (find_add_self hwf hn')
      · exact h6 i hi
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hprim
      · exact h7 i hi

/-- The header fold keeps a checking environment, with the translated headers added to the
abstract environment, while the names the headers list are absent and distinct from the
header names. -/
theorem declareInfos_valid {safety : DefinitionSafety} (allow : Bool) (L : List Name)
    (sourceEnv : VEnv) :
    ∀ (infos : List InductiveVal) (values : List VConstVal) (env : Environment) (venv : VEnv),
    List.Forall₂ (fun info v =>
      TrConstVal safety sourceEnv (.inductInfo info) v ∧ v.toVConstant.WF sourceEnv)
      infos values →
    sourceEnv ≤ venv →
    CheckingEnv.Valid safety env venv →
    RecursorShapesCoherent safety env.constants venv →
    IotaRulesRegistered safety env venv →
    (∀ n ∈ L, env.find? n = none) →
    (∀ info ∈ infos, info.name ∉ L) →
    (∀ info ∈ infos, ∀ n ∈ info.ctors, n ∈ L) →
    (∀ fn fi, env.find? fn = some (.inductInfo fi) → ∀ n ∈ fi.ctors,
      (∃ c, env.find? n = some c) ∨ n ∈ L) →
    (allow = true → ∀ info ∈ infos, ¬ Kernel.Environment.primitives.contains info.name) →
    (AddInductive.declareInductiveTypeInfos allow infos env).WF fun out =>
      ∃ outVEnv, venv.addConstVals values = some outVEnv ∧ venv ≤ outVEnv ∧
        CheckingEnv.Valid safety out outVEnv ∧
        RecursorShapesCoherent safety out.constants outVEnv ∧
        IotaRulesRegistered safety out outVEnv
  | [], [], env, venv, .nil, _, hV, hS, hI, _, _, _, _, _ =>
    Except.WF.pure ⟨venv, rfl, VEnv.LE.rfl, hV, @hS, @hI⟩
  | info :: infos, v :: values, env, venv, .cons hentry hrest, hle, hV, hS, hI, hL, hnotL,
      hsub, hinv, hnprim => by
    rw [AddInductive.declareInductiveTypeInfos]
    have hwf := hV.tr.map_wf
    refine (checkName.WF hwf info.name allow).bind fun _ ⟨hn, hprim⟩ => ?_
    have hn' : env.find? (ConstantInfo.inductInfo info).name = none := hn
    have hnprimHead : ¬ Kernel.Environment.primitives.contains info.name := by
      intro hp
      exact hnprim (hprim hp) info (by simp) hp
    have hname : info.name = v.name := hentry.1.2
    have hvnone : venv.constants info.name = none := by
      cases h : venv.constants info.name with
      | none => rfl
      | some ci =>
        obtain ⟨c, hc, -⟩ := hV.tr.find?_iff.2 ⟨ci, h⟩
        rw [hn] at hc; cases hc
    obtain ⟨venv', hadd⟩ : ∃ venv', venv.addConst info.name v.toVConstant = some venv' := by
      simp [VEnv.addConst, hvnone]
    have hle' : venv ≤ venv' := VEnv.addConst_le hadd
    have hnotL₀ : info.name ∉ L := hnotL info (by simp)
    have hL' : ∀ n ∈ L, (env.add (.inductInfo info)).find? n = none := by
      intro n hnL
      cases h : (env.add (.inductInfo info)).find? n with
      | none => rfl
      | some c =>
        rcases findAddFresh_cases hwf _ hn' h with ⟨rfl, -⟩ | hold
        · exact absurd hnL hnotL₀
        · rw [hL n hnL] at hold; cases hold
    have hinv' : ∀ fn fi, (env.add (.inductInfo info)).find? fn = some (.inductInfo fi) →
        ∀ n ∈ fi.ctors, (∃ c, (env.add (.inductInfo info)).find? n = some c) ∨ n ∈ L := by
      intro fn fi hfi n hnmem
      rcases findAddFresh_cases hwf _ hn' hfi with ⟨-, hfiEq⟩ | hold
      · cases hfiEq
        exact .inr (hsub info (by simp) n hnmem)
      · rcases hinv fn fi hold n hnmem with ⟨c, hc⟩ | hnL
        · exact .inl ⟨c, findAddFresh_of_find hwf _ hn' hc⟩
        · exact .inr hnL
    have hlisted : ListedConstructorsCoherent (env.add (.inductInfo info)) := by
      intro fn fi hfi n hnmem c hc
      rcases findAddFresh_cases hwf _ hn' hfi with ⟨-, hfiEq⟩ | hold
      · cases hfiEq
        rw [hL' n (hsub info (by simp) n hnmem)] at hc; cases hc
      · rcases hinv fn fi hold n hnmem with ⟨c₀, hc₀⟩ | hnL
        · have := findAddFresh_of_find hwf _ hn' hc₀
          rw [hc] at this
          cases this
          exact hV.listedConstructors fn fi hold n hnmem c hc₀
        · rw [hL' n hnL] at hc; cases hc
    have hV' := hV.add (ci := .inductInfo info) hn' hnprimHead (hentry.1.1.mono hle)
      (hentry.2.mono hle) hadd rfl (fun _ h => by cases h) (fun _ h => by cases h) hlisted
    have hS' : RecursorShapesCoherent safety (env.add (.inductInfo info)).constants venv' :=
      shapes_add @hS hwf hn' (fun _ h => by cases h) (fun _ h => by cases h) hle'
    have hI' : IotaRulesRegistered safety (env.add (.inductInfo info)) venv' :=
      iota_add @hI hwf hn' (fun _ h => by cases h) hle'
    refine (declareInfos_valid allow L sourceEnv infos values (env.add (.inductInfo info)) venv'
      hrest (hle.trans hle') hV' @hS' @hI' hL'
      (fun i hi => hnotL i (by simp [hi])) (fun i hi => hsub i (by simp [hi])) hinv'
      (fun hallow i hi => hnprim hallow i (by simp [hi]))).mono
      fun out ⟨outVEnv, hvals, hle'', h1, h2, h3⟩ => ⟨outVEnv, ?_, hle'.trans hle'', h1, h2, h3⟩
    simp only [VEnv.addConstVals, ← hname, hadd, Option.bind_eq_bind, Option.bind_some]
    exact hvals

end HeaderInstallation
end VerifyInductive
end Lean4Lean
