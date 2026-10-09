import Lean4Lean.Verify.Environment

/-! # Realizability of canonical equality

`VEnv.HasCanonicalEq` stores explicit abstract terms for `Eq`, `Eq.refl`,
`Eq.rec` and the iota rule of `Eq.rec`.  This file connects them to the
declaration `Init.Prelude` submits.

* `Lean4Lean/Verify/Inductive/Prelude/EqSyntax.lean` states the prelude's
  expressions literally (`preludeEqType`, `preludeEqReflType`,
  `eqRecTypeExpr`, `eqRecRuleRhsExpr`, `eqRecRuleLhsExpr`, `eqRecRuleTypeExpr`,
  generic only in binder and universe-parameter names) and proves that every
  `TrExprS` translation of each of the three types is the corresponding stored
  term (`TrExprS.eq_canonicalEq*`).
* `InductiveSignature.Compiles.eqRecRules`
  (`Lean4Lean/Theory/Inductive/CanonicalEqSignature.lean`): an ordinary
  compilation of the declaration generates exactly the stored iota rule once its
  recursor has the stored type.
* `addDecl.preludeEq_hasCanonicalEq` (below): checked addition of the prelude's `Eq`
  declaration (`PreludeEqShape`) produces abstract environments satisfying
  `HasCanonicalEq`, provided the executable installs `Eq.rec` with the
  prelude's type (`IsPreludeEqRec`).  The executable recursor construction
  is not modelled syntactically, so this is a hypothesis on the output;
  `Lean4Lean/Tests/PreludeEq.lean` checks it for the declaration of
  `Init.Prelude`.
* `VEnvs.WF.canonicalEq_constants` (below): in any well-formed model of an
  environment whose `Eq`, `Eq.refl` and `Eq.rec` have the prelude's
  types, the three constant clauses of `HasCanonicalEq` hold at every safety.
  `VEnvs.WF.quotReady_of_eqType` needs only `Eq` and concludes `QuotReady`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

private theorem vconstant_ext {a b : VConstant} (huvars : a.uvars = b.uvars)
    (htype : a.type = b.type) : a = b := by
  cases a; cases b; simp_all

/-- The translated constant of a safe kernel constant whose type
translates uniquely. -/
private theorem VEnvs.WF.constant_of_kernel {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {name : Name} {ci : ConstantInfo} {uvars : Nat} {type : VExpr}
    (hfind : env.find? name = some ci) (hsafe : ci.safety = .safe)
    (huvars : ci.levelParams.length = uvars)
    (htype : ∀ {venv e}, TrExprS venv ci.levelParams [] ci.type e → e = type)
    (safety : DefinitionSafety) :
    (ves.venv safety).constants name = some ⟨uvars, type⟩ := by
  rcases (wf.tr (safety := safety)).find? hfind
      (by rw [hsafe]; exact DefinitionSafety.le_safe) with
    ⟨ci', hci', -, hciUvars, hciType⟩
  rw [hci']
  exact congrArg some (vconstant_ext (hciUvars.symm.trans huvars) (htype hciType))

/-- The constant clauses of `HasCanonicalEq` hold in every well-formed model of
an environment containing the prelude's `Eq`, `Eq.refl` and `Eq.rec`. -/
theorem VEnvs.WF.canonicalEq_constants {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {eqInfo reflInfo recInfo : ConstantInfo}
    (hEq : env.find? ``Eq = some eqInfo) (hEqProd : IsPreludeEq eqInfo)
    (hRefl : env.find? ``Eq.refl = some reflInfo) (hReflProd : IsPreludeEqRefl reflInfo)
    (hRec : env.find? ``Eq.rec = some recInfo) (hRecProd : IsPreludeEqRec recInfo)
    (safety : DefinitionSafety) :
    (ves.venv safety).constants ``Eq = some ⟨1, canonicalEqType⟩ ∧
    (ves.venv safety).constants ``Eq.refl = some ⟨1, canonicalEqReflType⟩ ∧
    (ves.venv safety).constants ``Eq.rec = some ⟨2, canonicalEqRecType⟩ := by
  rcases hEqProd with ⟨hEqSafe, u, a, b, c, hEqLps, hEqType⟩
  rcases hReflProd with ⟨hReflSafe, u', a', b', hReflLps, hReflType⟩
  rcases hRecProd with ⟨hRecSafe, v, w, n, hvw, hRecLps, hRecType⟩
  refine ⟨wf.constant_of_kernel hEq hEqSafe (by simp [hEqLps]) ?_ safety,
    wf.constant_of_kernel hRefl hReflSafe (by simp [hReflLps]) ?_ safety,
    wf.constant_of_kernel hRec hRecSafe (by simp [hRecLps]) ?_ safety⟩
  · intro _ _ H
    rw [hEqLps, hEqType] at H
    exact TrExprS.eq_canonicalEqType H
  · intro _ _ H
    rw [hReflLps, hReflType] at H
    exact TrExprS.eq_canonicalEqReflType H
  · intro _ _ H
    rw [hRecLps, hRecType] at H
    exact TrExprS.eq_canonicalEqRecType hvw H

/-- Quotient readiness holds in every well-formed model of an environment whose `Eq` is a safe
constant with one universe parameter and whose type translates only to the canonical type of
`Eq`. This is the part of `canonicalEq_constants` that quotient initialization consumes. -/
theorem VEnvs.WF.quotReady_of_eqType {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {eqInfo : ConstantInfo} (hEq : env.find? ``Eq = some eqInfo)
    (hsafe : eqInfo.safety = .safe) {u : Name} (hlps : eqInfo.levelParams = [u])
    (htype : ∀ {venv e}, TrExprS venv [u] [] eqInfo.type e → e = canonicalEqType)
    (safety : DefinitionSafety) : (ves.venv safety).QuotReady :=
  wf.constant_of_kernel hEq hsafe (by simp [hlps]) (fun H => htype (hlps ▸ H)) safety

/-- Checked addition of the prelude's `Eq` declaration realizes canonical
equality: the output environment has well-formed abstract models extending the
input ones, and these satisfy `HasCanonicalEq` (including the iota rule of
`Eq.rec`) as soon as the executable has installed `Eq.rec` with the prelude's
type.  Only the absence of `Eq` is assumed of the input. -/
theorem addDecl.preludeEq_hasCanonicalEq {env : Environment} {ves : VEnvs}
    (wf : ves.WF env)
    (hAbsent : env.constants.find? ``Eq = none)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType} {isUnsafe : Bool}
    (Hshape : VerifyInductive.PreludeEqShape lparams nparams types isUnsafe)
    (fuel : FuelConfig := {})
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety) := by intro; trivial) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe) (check := true)
      (fuel := fuel)).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        ∀ ci, outEnv.find? ``Eq.rec = some ci → IsPreludeEqRec ci →
          ves'.HasCanonicalEq :=
  (VerifyInductive.addInductiveDeclaration.preludeEqExtensionWF env lparams
      nparams types isUnsafe fuel ves wf hmode hAbsent Hshape).mono
    fun _ ⟨ves', wf', _, hle, _, hcanonical⟩ => ⟨ves', wf', hle, hcanonical⟩

end Lean4Lean
