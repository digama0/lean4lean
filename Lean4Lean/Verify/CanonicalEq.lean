import Lean4Lean.Verify.Inductive.Prelude.Eq
import Lean4Lean.Verify.TypeChecker.CheckerEnv

/-! # Realizability of canonical equality

`VEnv.HasCanonicalEq` states the types of `Eq`, `Eq.refl` and `Eq.rec` and the registered ι rule
of `Eq.rec`. This file connects them to the declaration `Init.Prelude` submits.

* `Lean4Lean/Verify/Inductive/Prelude/EqSyntax.lean` states the prelude's expressions literally
  (`preludeEqType`, `preludeEqReflType`, `eqRecTypeExpr`, `eqRecRuleRhsExpr`, generic only in
  binder and universe-parameter names) and proves that every `TrExprS` translation of each of
  the three types is the corresponding stored term (`TrExprS.eq_canonicalEq*`).
* `VEnvs.WF.canonicalEq_constants`: in any well-formed model of an environment whose `Eq`,
  `Eq.refl` and `Eq.rec` have the prelude's types, the three constant clauses hold at every
  safety. `VEnvs.WF.quotReady_of_eqType` needs only `Eq` and concludes `QuotReady`.
* `VEnvs.WF.hasCanonicalEq`: the ι rule clause, read off the kernel recursor `Eq.rec` through
  the translation invariant (`TrEnv.iotaRulesRegistered`): a recursor of the kernel environment
  has its rules registered as patterns of the model. The kernel recursor's metadata (the
  parameter, motive, minor and index counts and the single rule on `Eq.refl` with no fields and
  right-hand side `eqRecRuleRhsExpr`) is a hypothesis on the output (`IsPreludeEqRecVal`),
  as its type is (`IsPreludeEqRec`): the executable recursor construction is not modelled
  syntactically. `Lean4Lean/Tests/PreludeEq.lean` checks both for the declaration of
  `Init.Prelude`.
* `addDecl.preludeEq_hasCanonicalEq`: checked addition of the prelude's `Eq` declaration
  (`PreludeEqShape`) produces abstract environments satisfying `HasCanonicalEq`, provided the
  executable installs `Eq.refl` and `Eq.rec` with the prelude's data.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

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
  exact congrArg some (VConstant.eq_of_fields (hciUvars.symm.trans huvars) (htype hciType))

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

/-- The kernel constructor `Eq.refl` as `Init.Prelude` declares it: the prelude's type and two
parameters. -/
def IsPreludeEqReflVal (cval : ConstructorVal) : Prop :=
  IsPreludeEqRefl (.ctorInfo cval) ∧ cval.numParams = 2

/-- The kernel recursor `Eq.rec` as the kernel generates it for the prelude's `Eq`: its type, two
parameters, one motive, one minor premise, one index, and the single rule on `Eq.refl`, with no
field and the right-hand side `fun α a motive refl => refl`. -/
def IsPreludeEqRecVal (rval : RecursorVal) : Prop :=
  IsPreludeEqRec (.recInfo rval) ∧ rval.numParams = 2 ∧ rval.numMotives = 1 ∧
    rval.numMinors = 1 ∧ rval.numIndices = 1 ∧
    ∃ (u v : Name) (n : EqRecBinderNames) (rule : RecursorRule), rval.levelParams = [u, v] ∧
      rval.rules = [rule] ∧ rule.ctor = ``Eq.refl ∧ rule.nfields = 0 ∧
      rule.rhs = eqRecRuleRhsExpr u v n

/-- Every translation of the right-hand side of the rule of `Eq.rec` is a four-binder
λ-template returning its last binder. -/
theorem TrSyn.eqRecRuleRhs {u v : Name} {n : EqRecBinderNames} {e : VExpr}
    (H : TrSyn [u, v] [] (eqRecRuleRhsExpr u v n) e) :
    ∃ d1 d2 d3 d4, e = .lam d1 (.lam d2 (.lam d3 (.lam d4 (.bvar 0)))) := by
  unfold eqRecRuleRhsExpr at H
  cases H with | lam _ H =>
  cases H with | lam _ H =>
  cases H with | lam _ H =>
  cases H with | lam _ H =>
  cases H with | bvar h =>
  simp [VLCtx.find?] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨_, _, _, _, rfl⟩

/-- **Canonical equality in a well-formed model** of an environment whose `Eq`, `Eq.refl` and
`Eq.rec` are the prelude's. -/
theorem VEnvs.WF.hasCanonicalEq {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {cval : ConstructorVal} {rval : RecursorVal} {safety : DefinitionSafety}
    (hready : (ves.venv safety).QuotReady)
    (hRefl : env.find? ``Eq.refl = some (.ctorInfo cval)) (hReflProd : IsPreludeEqReflVal cval)
    (hRec : env.find? ``Eq.rec = some (.recInfo rval)) (hRecProd : IsPreludeEqRecVal rval) :
    (ves.venv safety).HasCanonicalEq := by
  have h2 : (ves.venv safety).constants ``Eq.refl = some ⟨1, canonicalEqReflType⟩ := by
    rcases hReflProd.1 with ⟨hReflSafe, u', a', b', hReflLps, hReflType⟩
    exact wf.constant_of_kernel hRefl hReflSafe (by simp [hReflLps]) (fun H => by
      rw [hReflLps, hReflType] at H; exact TrExprS.eq_canonicalEqReflType H) safety
  have h3 : (ves.venv safety).constants ``Eq.rec = some ⟨2, canonicalEqRecType⟩ := by
    rcases hRecProd.1 with ⟨hRecSafe, u, v, n, hvw, hRecLps, hRecType⟩
    exact wf.constant_of_kernel hRec hRecSafe (by simp [hRecLps]) (fun H => by
      rw [hRecLps, hRecType] at H; exact TrExprS.eq_canonicalEqRecType hvw H) safety
  refine ⟨hready, h2, h3, ?_⟩
  obtain ⟨⟨hsafe, -⟩, hnp, hnm, hnmin, hnind, u, v, n, rule, hlps, hrules, hctor, hnf, hrhs⟩ :=
    hRecProd
  have hfind : rval.rules.find? (·.ctor == ``Eq.refl) = some rule := by
    rw [hrules]; simp [hctor]
  obtain ⟨cval', rhs, hc, hfind', htr, hpat⟩ :=
    (wf.tr (safety := safety)).iotaRulesRegistered hRec hfind
      (by show safety ≤ (ConstantInfo.recInfo rval).safety; rw [hsafe]
          exact DefinitionSafety.le_safe)
  rw [hRefl] at hfind'
  cases Option.some.inj hfind'
  rw [hlps, hrhs] at htr
  obtain ⟨d1, d2, d3, d4, rfl⟩ := TrSyn.eqRecRuleRhs htr.toTrSyn
  rw [hnp, hnm, hnmin, hnind, hReflProd.2, hnf] at hpat
  exact ⟨[d1, d2, d3, d4], hc, rfl, hpat⟩

/-- Checked addition of the prelude's `Eq` declaration realizes canonical equality: the output
environment has well-formed abstract models extending the input ones, and these satisfy
`HasCanonicalEq` as soon as the executable has installed `Eq.refl` and `Eq.rec` with the
prelude's data. Only the absence of `Eq` is assumed of the input. -/
theorem addDecl.preludeEq_hasCanonicalEq {env : Environment} {ves : VEnvs}
    (wf : ves.WF env)
    (hAbsent : env.constants.find? ``Eq = none)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType} {isUnsafe : Bool}
    (Hshape : VerifyInductive.PreludeEqShape lparams nparams types isUnsafe)
    (fuel : FuelConfig := {}) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe) (check := true)
      (fuel := fuel)).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        ∀ {cval : ConstructorVal} {rval : RecursorVal},
          outEnv.find? ``Eq.refl = some (.ctorInfo cval) → IsPreludeEqReflVal cval →
          outEnv.find? ``Eq.rec = some (.recInfo rval) → IsPreludeEqRecVal rval →
          ∀ safety, (ves'.venv safety).HasCanonicalEq := by
  have Hrun := VerifyInductive.Environment.addInductive.preludeEqExtensionWF env
    lparams nparams types isUnsafe fuel ves wf hAbsent Hshape
  have hcheck := VerifyInductive.checkPrimitiveInductive_eq_false_of_preludeEqShape env Hshape
  have Hrun' : (addDecl env (.inductDecl lparams nparams types isUnsafe) (check := true)
      (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ VerifyInductive.QuotReadyEnvs ves' ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (VerifyInductive.SourceAddInduct (ves.venv .safe) lparams
            nparams types false (ves'.venv .safe)) := by
    simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun
  refine Hrun'.mono fun outEnv ⟨ves', wf', hready, hle, _⟩ => ⟨ves', wf', hle, ?_⟩
  intro cval rval hRefl hReflProd hRec hRecProd safety
  exact wf'.hasCanonicalEq (hready safety) hRefl hReflProd hRec hRecProd

end Lean4Lean
