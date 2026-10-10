import Lean4Lean.Verify.Environment.Blocks
import Lean4Lean.Verify.Environment.QuotCoherence

/-!
# What the checker reads of its environment

The verification of the type checker (`Verify/TypeChecker/**`) runs against an abstract
environment `venv` and reads a fixed list of facts relating it to the executable environment
`env`. Most of them are the checking invariant `CheckingEnv.Valid` of the environment model
(`Verify/Environment/Blocks.lean`): the constant translation, the constructor and projection
metadata of the installed inductive blocks, the K clause of the visible recursors, the heads of
the reduction rules and the quotient constants. Recursor reduction reads two more facts about
each visible recursor, collected here:

* `RecursorShapes`: the recursor's type is a recursor telescope over its major family, and the
  constructor of each rule has the constructor telescope at its own parameter count. This is
  what shows the constructor application of a well-typed redex saturated.
* `IotaRulesRegistered`: the ι rule of each rule is registered, in the form of PR #43's
  `TrEnv.pats_iota'`.

`CheckerEnv` is `CheckingEnv.Valid` with these two facts.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

-- WAVE 2 install COMPAT: `RecursorShapes` moved to `Verify/Environment/Blocks.lean` (the
-- installed-block descriptor records it).

/-- Every visible recursor of the constant map has its shapes. -/
def RecursorShapesCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) →
    safety ≤ (ConstantInfo.recInfo rec).safety → RecursorShapes C venv rec

/-- WAVE 2 install COMPAT: the shapes of every visible recursor are read off its installed-block
descriptor (`InstalledBlock.WF.shapes`). -/
theorem InstalledBlocks.recursorShapesCoherent {safety : DefinitionSafety} {env : Environment}
    {venv : VEnv} {st : InstallStage} (H : InstalledBlocks safety env venv st)
    (hwf : env.constants.WF) : RecursorShapesCoherent safety env.constants venv := by
  intro name rec hfind hsafe
  have hf : env.find? name = some (.recInfo rec) := by
    rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  obtain ⟨-, B, -, hB, hmem⟩ := H.recursor hf
  exact (hB.shapes rec hmem hsafe).1

/-- What recursor reduction reads of a visible recursor: its shapes, the rigidity of its major
family, and the K clause. -/
def RecursorsCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) →
    safety ≤ (ConstantInfo.recInfo rec).safety →
    (∃ cnparams indLevels ctorParams,
      Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams cnparams
        rec.numMotives rec.numMinors rec.numIndices rec.getMajorInduct indLevels ctorParams) ∧
      venv.Rigid rec.getMajorInduct ∧
      ∀ rule ∈ rec.rules, ∃ ctorUvars, indLevels.length = ctorUvars ∧
        Nonempty (VConstructorShape venv rule.ctor ctorUvars cnparams rule.nfields rec.numIndices
          rec.getMajorInduct) ∧
        ∀ cval, C.find? rule.ctor = some (.ctorInfo cval) → cval.numParams = cnparams) ∧
    KLikeRecursor C venv rec

/-- The ι rule of every rule of a visible recursor is registered: PR #43's `TrEnv.pats_iota'`. -/
def IotaRulesRegistered (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  ∀ {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule},
    env.find? recName = some (.recInfo rval) →
    rval.rules.find? (·.ctor == cName) = some rule →
    safety ≤ (Lean.ConstantInfo.recInfo rval).safety →
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      env.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true)

theorem TrEnv.iotaRulesRegistered (H : TrEnv safety env venv) :
    IotaRulesRegistered safety env venv := fun hrec hrule hsafe => H.pats_iota' hrec hrule hsafe

/-- Everything the checker verification reads of its environment: the checking invariant and
the two recursor facts. -/
structure CheckerEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop
    extends CheckingEnv.Valid safety env venv where
  /-- The shapes of the visible recursors. -/
  shapes : RecursorShapesCoherent safety env.constants venv
  /-- The ι rules of the visible recursors. -/
  iota : IotaRulesRegistered safety env venv

namespace CheckerEnv
variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv}

theorem wf (H : CheckerEnv safety env venv) : venv.WF := H.tr.wf
theorem map_wf (H : CheckerEnv safety env venv) : env.constants.WF := H.tr.map_wf

theorem find?_iff (H : CheckerEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci := H.tr.find?_iff

theorem find? (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := H.tr.find? h hs

theorem find?_uniq (H : CheckerEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := H.tr.find?_uniq h hs

theorem of_value (H : CheckerEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.tr.of_value h hs hv

/-- What recursor reduction reads of a visible recursor. -/
theorem recursors (H : CheckerEnv safety env venv) :
    RecursorsCoherent safety env.constants venv := by
  intro name rec hrec hsafe
  obtain ⟨cnparams, indLevels, ctorParams, hrec', hrules⟩ := H.shapes hrec hsafe
  obtain ⟨info, hmajor⟩ := H.toValid.recursors.majors hrec hsafe
  exact ⟨⟨cnparams, indLevels, ctorParams, hrec', H.equationHeads.rigid hmajor, hrules⟩,
    H.toValid.recursors.rules hrec hsafe⟩

/-- The major family of every present recursor is a header whose constructors are present. -/
theorem recursorMajorCtors (H : CheckerEnv safety env venv)
    (hrec : env.find? name = some (.recInfo r)) :
    ∃ info, env.find? r.getMajorInduct = some (.inductInfo info) ∧
      ∀ n ∈ info.ctors, ∃ ci, env.find? n = some ci :=
  H.blocks.recursorMajorCtors hrec

end CheckerEnv

end Lean4Lean
