import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaOverlap
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Confluence.QuotPatterns
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! Generated iota patterns are generated from the actual restored equation.
Their RHS applies that equation's closed lambda telescope to captured
parameters, motives, minors and constructor fields. The source guard is
fixed by the registered recursor elimination instance. -/

namespace Lean4Lean.InductiveSignature.RecursorData

/-- Actual restored constructor arguments, including specialized parameters. -/
def ruleMajorArguments (equation : VDefEq) : List VExpr :=
  (equation.lhs.stripLams.getAppFnArgs.2.getLast?.getD (.bvar 0)).getAppFnArgs.2

def ruleConstructor (data : RecursorData)
    (index : Fin data.schema.signature.constructors.size) : Name :=
  data.schema.restoration.headName data.schema.signature.constructors[index].name

def rulePattern (data : RecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) : Pattern :=
  (SimplePattern.iota data.name data.majorOffset (data.ruleConstructor index)
    (ruleMajorArguments equation).length).toPattern

def ruleCaptures (data : RecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) :
    List (data.rulePattern index equation).RHS :=
  let pre := ((Pattern.const data.name).argumentRHS data.majorOffset).take data.indexOffset
  let ctor := (Pattern.const (data.ruleConstructor index)).argumentRHS
    (ruleMajorArguments equation).length
  pre.map (Pattern.RHS.mapPaths Sum.inl) ++
    (ctor.drop ((ruleMajorArguments equation).length -
      data.schema.signature.constructors[index].fields.length)).map (Pattern.RHS.mapPaths Sum.inr)

def ruleRHS (data : RecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq)
    (hclosed : equation.rhs.Closed) : (data.rulePattern index equation).RHS :=
  (Pattern.RHS.fixed equation.rhs hclosed).applyArgs (data.ruleCaptures index equation)

def ruleCheck (data : RecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) :
    (data.rulePattern index equation).Check :=
  if data.largeTarget then .nonzero (data.schema.sourceLevel data.owner data.levels) .true else .true

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open InductiveSignature

inductive GeneratedIotaPattern (env : VEnv) (registry : Name → Option RecursorData) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | intro {data : RecursorData} {index : Fin data.schema.signature.constructors.size}
      {equation : VDefEq} (henv : env.WF)
      (hregistered : RecursorRegistered env data)
      (hlookup : registry data.name = some data)
      (howner : data.schema.signature.constructors[index].owner = data.owner)
      (hgen : data.equation index = some equation) :
      GeneratedIotaPattern env registry (data.rulePattern index equation)
        (data.ruleRHS index equation (hregistered.equation_closed henv hgen).2.1,
          data.ruleCheck index equation)

private theorem constHead_varN (p : Pattern) (n : Nat) :
    (p.varN n).constHead = p.constHead := by induction n <;> simp [Pattern.varN, Pattern.constHead, *]

namespace GeneratedIotaPattern

theorem simple (H : GeneratedIotaPattern env registry p rhs) :
    ∃ shape : SimplePattern, p = shape.toPattern := by
  cases H
  exact ⟨.iota _ _ _ _, rfl⟩

theorem origin (H : GeneratedIotaPattern env registry p rhs) : PatternHeadsStoredRule env p := by
  cases H with
  | intro henv hr hl ho hg =>
    exact ⟨_, _, _, hr.equation_present hg,
      by simp only [RecursorData.rulePattern, SimplePattern.toPattern,
        Pattern.constHead, constHead_varN],
      (VExpr.equationHead_eq _).trans (hr.equation_head ho hg)⟩

theorem generated (H : GeneratedIotaPattern env registry p rhs) :
    ∃ data : RecursorData, ∃ index : Fin data.schema.signature.constructors.size,
      ∃ (equation : VDefEq) (hclosed : equation.rhs.Closed), RecursorRegistered env data ∧ registry data.name = some data ∧
      data.schema.signature.constructors[index].owner = data.owner ∧
      data.equation index = some equation ∧ p = data.rulePattern index equation ∧
      rhs ≍ (data.ruleRHS index equation hclosed, data.ruleCheck index equation) := by
  cases H with
  | @intro data index equation henv hr hl ho hg => exact ⟨data, index, equation, _, hr, hl, ho, hg, rfl, HEq.rfl⟩

/-- The iota pattern retains the exact recursor metadata required by the core
reduction guard; primitive quotient metadata remain a separate alternative. -/
theorem registered (H : GeneratedIotaPattern env registry
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) :
    ∃ data, RecursorRegistered env data ∧ data.name = recursor ∧
      data.majorOffset = major ∧ registry recursor = some data ∧
      (data.largeTarget = true → ∃ rest,
        rhs.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest) := by
  obtain ⟨data, index, equation, hclosed, hr, hl, ho, hg, he, hrhs⟩ := H.generated
  have hi : (SimplePattern.iota recursor major ctor fields).toPattern.inter
      (data.rulePattern index equation) = some (data.rulePattern index equation) := by
    rw [he]; exact Pattern.inter_self _
  simp only [RecursorData.rulePattern, SimplePattern.toPattern, Pattern.inter,
    bind, Option.bind_eq_some_iff] at hi
  obtain ⟨left, hleft, right, hright, _⟩ := hi
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hleft
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hright
  refine ⟨data, hr, rfl, rfl, hl, ?_⟩
  intro hlarge
  have hc := congrArg Prod.snd (eq_of_heq hrhs)
  exact ⟨.true, hc.trans (by simp only [RecursorData.ruleCheck, hlarge, ↓reduceIte]; rfl)⟩

theorem app_l (H : GeneratedIotaPattern env registry p rhs)
    (hs : Subpattern (.app fn arg) p) : ¬Subpattern (.app left right) fn := by
  cases H
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  exact Subpattern.constVarN_noapp

theorem app_l_uniq (H : GeneratedIotaPattern env registry p rhs)
    (H' : GeneratedIotaPattern env registry p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  cases H with
  | @intro data index equation henv hr hl ho hg =>
    cases H' with
    | @intro data' index' equation' henv' hr' hl' ho' hg' =>
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      apply SimplePattern.iota_app_l_uniq ?_ hb
      intro hn
      rw [hn] at hl
      cases Option.some.inj (hl.symm.trans hl')
      rfl

theorem app_uniq (H : GeneratedIotaPattern env registry p rhs)
    (H' : GeneratedIotaPattern env registry p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hright : Subpattern right arg') : left.inter right = none := by
  cases H with
  | @intro data index equation henv hr hlookup ho hg =>
    cases H' with
    | @intro data' index' equation' henv' hr' hlookup' ho' hg' =>
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      apply SimplePattern.iota_app_uniq ?_ hl hright
      intro hn
      have hrigid := henv.installed_constructor_rigid (hr'.equation_present hg') (hr'.equation_major hg')
      apply hrigid equation (hr.equation_present hg) (VLevel.params data.uvars)
      exact (hr.equation_head ho hg).trans (by rw [hn]; rfl)

end GeneratedIotaPattern
end Lean4Lean.VEnv

namespace Lean4Lean.VEnv
open InductiveSignature
set_option maxHeartbeats 1000000 in
theorem VInductBlock.install_type_lookup' (H : VInductBlock.install base block = some installed)
    (hvalue : value ∈ block.types) : installed.constants value.name = some value.toVConstant := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact ((VEnv.addConstVals_le hc).trans <| VEnv.addEliminators_addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le).constants (VEnv.addConstVals_get ht hvalue)
end Lean4Lean.VEnv
