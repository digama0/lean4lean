import Lean4Lean.Theory.Typing.Confluence.RegistryOfWF
import Lean4Lean.Theory.Typing.Confluence.QuotPatterns
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaOverlap
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.RecursorMajorFamily
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.EnvTables.Arity
import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance

/-! The concrete pattern table of a well-formed environment: definition
unfoldings and generated iota rules from the head registry, and the primitive
quotient rule when the quotient declaration is present. This file proves the
syntactic non-overlap facts of the table. -/

namespace Lean4Lean.VEnv
open InductiveSignature HeadRegistry
set_option linter.unusedSectionVars false

/-- A recursor never carries the primitive quotient lift's name: its
type returns a motive application, the quotient lift's type a bare variable. -/
theorem QuotRegistered.recursor_name_ne (hq : QuotRegistered env)
    (H : RecursorRegistered env data) : data.name ≠ ``Quot.lift := by
  intro hn
  obtain ⟨type, htype⟩ := H.recursorType_exists
  have hc := H.recursorType htype
  rw [hn, hq.lift] at hc
  obtain ⟨domains, _, hshape, _⟩ := RecursorData.recursorType_shape htype
  have ht := congrArg (fun c : VConstant => c.type.forallResult) (Option.some.inj hc)
  simp only [hshape, VExpr.forallResult_wrapForalls] at ht
  rw [← List.singleton_append, ← List.append_assoc, VExpr.mkApps_append] at ht
  simp [VExpr.mkApps, quotLiftConst, VExpr.forallResult] at ht

theorem QuotRegistered.quotMk_rigid (henv : env.WF) (hq : QuotRegistered env) :
    env.Rigid ``Quot.mk :=
  henv.installed_constructor_rigid hq.equation ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩

theorem QuotRegistered.lift_head (hq : QuotRegistered env) :
    ∃ equation levels, env.defeqs equation ∧
      equation.lhs.equationHead = .const ``Quot.lift levels :=
  ⟨quotDefEq, [.param 0, .param 1], hq.equation, rfl⟩

/-- A recursor has an installed equation headed by its name, so it is
never a rigid head. -/
theorem RecursorRegistered.not_rigid_of_lookup
    (H : RecursorRegistered env data)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) : ¬env.Rigid data.name := fun h =>
  h equation (H.equation_present hgen) _ (H.equation_head howner hgen)

theorem _root_.Lean4Lean.SimplePattern.iota_toPattern_inj
    (H : (SimplePattern.iota a b c d).toPattern = (SimplePattern.iota a' b' c' d').toPattern) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hi := Pattern.inter_self (SimplePattern.iota a b c d).toPattern
  conv at hi => rhs; rw [H]
  conv at hi => lhs; arg 2; rw [H]
  simp only [SimplePattern.toPattern, Pattern.inter, bind, Option.bind_eq_some_iff] at hi
  obtain ⟨_, h1, _, h2, _⟩ := hi
  obtain ⟨e1, e2⟩ := Pattern.constVarN_inter h1
  obtain ⟨e3, e4⟩ := Pattern.constVarN_inter h2
  exact ⟨e1, e2, e3, e4⟩

namespace GeneratedIotaPattern

theorem unique (H : GeneratedIotaPattern env registry p rhs)
    (H' : GeneratedIotaPattern env registry q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  cases H with
  | @intro data index equation henv hr hl ho hg =>
    cases H' with
    | @intro data' index' equation' henv' hr' hl' ho' hg' =>
      have hrigid := henv.installed_constructor_rigid (hr.equation_present hg) (hr.equation_major hg)
      have hmajor : data'.name = data.name → data'.majorOffset = data.majorOffset := by
        intro hn
        rw [hn] at hl'
        cases Option.some.inj (hl.symm.trans hl')
        rfl
      have hctor : data'.name ≠ data.ruleConstructor index := by
        intro hn
        exact hr'.not_rigid_of_lookup ho' hg' (hn ▸ hrigid)
      obtain ⟨hsub, hn, _, hc, _⟩ := SimplePattern.iota_overlap hmajor hctor hs hi
      rw [hn] at hl'
      cases Option.some.inj (hl.symm.trans hl')
      cases hr.constructor_index_unique ho ho' hc.symm
      cases Option.some.inj (hg.symm.trans hg')
      exact ⟨rfl, hsub.symm, HEq.rfl⟩

end GeneratedIotaPattern

/-- The concrete pattern table. -/
def ConcretePattern (registry : Registry) (env : VEnv) (p : Pattern) (rhs : p.RHS × p.Check) :
    Prop :=
  DefinitionPattern registry.definitions p rhs ∨
    (registry.quotient = true ∧ QuotPattern env p rhs) ∨
    GeneratedIotaPattern env registry.recursors p rhs

section
variable {registry : Registry} {declarations : List VDecl}
  (henv : env.WF) (contract : registry.EnvironmentContract env declarations)
include henv contract

theorem ConcretePattern.simple (H : ConcretePattern registry env p rhs) :
    ∃ s : SimplePattern, p = s.toPattern := by
  rcases H with H | ⟨_, H⟩ | H
  · exact H.simple
  · exact H.simple
  · exact H.simple

theorem ConcretePattern.origin (H : ConcretePattern registry env p rhs) :
    PatternHeadsStoredRule env p := by
  rcases H with H | ⟨_, H⟩ | H
  · exact H.origin fun _ _ h => (contract.definitions _ _ h).1
  · exact H.origin
  · exact H.origin

/-- A recursor lookup is never the registered quotient lift. -/
theorem ConcretePattern.recursor_quot (hq : QuotRegistered env) :
    registry.recursors ``Quot.lift = none := by
  cases h : registry.recursors ``Quot.lift with
  | none => rfl
  | some data =>
    obtain ⟨hr, hn, _⟩ := contract.recursors _ _ h
    exact (hq.recursor_name_ne hr hn).elim

theorem ConcretePattern.recursor {recursor ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    (H : ConcretePattern registry env (SimplePattern.iota recursor major ctor fields).toPattern r) :
    (∃ data, RecursorRegistered env data ∧ data.name = recursor ∧
      data.majorOffset = major ∧ registry.recursors recursor = some data ∧
      (∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner) ∧
      (data.largeTarget = true → ∃ rest,
        r.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest)) ∨
    (QuotRegistered env ∧ recursor = ``Quot.lift ∧ major = 5 ∧ ctor = ``Quot.mk ∧ fields = 3 ∧
      ∃ rest, r.2 = .nonzero (.param 0) rest) := by
  rcases H with H | ⟨_, H⟩ | H
  · exact H.not_iota.elim
  · exact .inr H.registered
  · obtain ⟨data, hr, hn, hm, hl, hg⟩ := H.registered
    obtain ⟨data', index, eqn, _, _, hl', ho, _, he, _⟩ := H.generated
    have hi : (SimplePattern.iota recursor major ctor fields).toPattern.inter
        (data'.rulePattern index eqn) = some (data'.rulePattern index eqn) := by
      rw [← he]; exact Pattern.inter_self _
    simp only [RecursorData.rulePattern, SimplePattern.toPattern, Pattern.inter,
      bind, Option.bind_eq_some_iff] at hi
    obtain ⟨_, hleft, _, _, _⟩ := hi
    obtain ⟨rfl, -⟩ := Pattern.constVarN_inter hleft
    rw [hl'] at hl
    cases hl
    exact .inl ⟨_, hr, hn, hm, hl', ⟨index, ho⟩, hg⟩

/-- Definition heads are neither recursors nor constructors of recursor
equations. -/
theorem ConcretePattern.definition_iota (hd : DefinitionPattern registry.definitions (.const c) rd)
    (hn : GeneratedIotaPattern env registry.recursors p rn) (hs : Subpattern (.const c) p) : False := by
  cases hd with
  | @intro value hl _ =>
    obtain ⟨hvr, hvn⟩ := contract.definitions _ _ hl
    cases hn with
    | @intro data index equation _ hr hlk ho hg =>
      rcases hs.iota_const with h | h
      · rw [h] at hl
        rw [contract.recursorNotDefinition _ _ hlk] at hl
        cases hl
      · have hrigid := henv.installed_constructor_rigid (hr.equation_present hg) (hr.equation_major hg)
        apply hrigid value.toDefEq hvr.2 (VLevel.params value.uvars)
        change VExpr.const value.name _ = VExpr.const _ _
        rw [h]; rfl

theorem ConcretePattern.app_l (H : ConcretePattern registry env p rhs)
    (hs : Subpattern (.app fn arg) p) : ¬Subpattern (.app left right) fn := by
  rcases H with H | ⟨_, H⟩ | H
  · exact (H.no_app_subpattern hs).elim
  · exact H.app_l hs
  · exact H.app_l hs

/-- A generated iota pattern's recursor is not the registered quotient lift, and
its constructor is neither the quotient lift nor the quotient constructor. -/
theorem ConcretePattern.recursor_quot_names (hq : QuotRegistered env)
    (H : GeneratedIotaPattern env registry.recursors p rhs) :
    ∃ rc mr cc kc, p = (SimplePattern.iota rc mr cc kc).toPattern ∧
      rc ≠ ``Quot.lift ∧ rc ≠ ``Quot.mk ∧ cc ≠ ``Quot.lift ∧ env.Rigid cc ∧
      ¬env.Rigid rc := by
  cases H with
  | @intro data index equation _ hr hl ho hg =>
    have hrigid := henv.installed_constructor_rigid (hr.equation_present hg) (hr.equation_major hg)
    have hnr := hr.not_rigid_of_lookup ho hg
    refine ⟨_, _, _, _, rfl, hq.recursor_name_ne hr, ?_, ?_, hrigid, hnr⟩
    · intro h; exact hnr (h ▸ hq.quotMk_rigid henv)
    · intro h
      obtain ⟨eq, lv, he, hh⟩ := hq.lift_head
      exact hrigid eq he lv
        (by rw [← VExpr.equationHead_eq, hh]; exact congrArg (VExpr.const · lv) h.symm)

theorem ConcretePattern.uniq (H : ConcretePattern registry env p rhs)
    (H' : ConcretePattern registry env q rhs')
    (hs : Subpattern sub p) (hi : q.inter sub = some intersection) :
    p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  have hdq : ∀ {p r}, DefinitionPattern registry.definitions p r ∨
      (registry.quotient = true ∧ QuotPattern env p r) →
      DefinitionQuotPattern env registry.definitions p r := fun h =>
    h.elim .inl fun h => .inr h.2
  rcases H with H | H | H <;> rcases H' with H' | H' | H'
  · exact (hdq (.inl H)).unique henv (fun _ _ h => (contract.definitions _ _ h).1)
      (hdq (.inl H')) hs hi
  · exact (hdq (.inl H)).unique henv (fun _ _ h => (contract.definitions _ _ h).1)
      (hdq (.inr H')) hs hi
  · cases H
    cases hs
    cases H'
    simp [RecursorData.rulePattern, SimplePattern.toPattern, Pattern.inter] at hi
  · exact (hdq (.inr H)).unique henv (fun _ _ h => (contract.definitions _ _ h).1)
      (hdq (.inl H')) hs hi
  · exact (hdq (.inr H)).unique henv (fun _ _ h => (contract.definitions _ _ h).1)
      (hdq (.inr H')) hs hi
  · obtain ⟨hen, H⟩ := H
    have hq := contract.quotientRegistered hen
    obtain ⟨rc, mr, cc, kc, rfl, hrc, hrm, _, _, _⟩ :=
      ConcretePattern.recursor_quot_names henv contract hq H'
    cases H
    obtain ⟨_, he, _⟩ := SimplePattern.iota_overlap (fun h => (hrc h).elim) hrm hs hi
    exact (hrc he).elim
  · have H'' := H'
    cases H' with
    | @intro value _ _ =>
      cases sub <;> simp only [Pattern.inter, reduceCtorEq, Option.ite_none_right_eq_some] at hi
      obtain ⟨rfl, -⟩ := hi
      exact (ConcretePattern.definition_iota henv contract H'' H hs).elim
  · obtain ⟨hen, H'⟩ := H'
    have hq := contract.quotientRegistered hen
    obtain ⟨rc, mr, cc, kc, rfl, hrc, _, hcq, _, _⟩ :=
      ConcretePattern.recursor_quot_names henv contract hq H
    cases H'
    obtain ⟨_, he, _⟩ := SimplePattern.iota_overlap (fun h => (hrc h.symm).elim)
      (fun h => hcq h.symm) hs hi
    exact (hrc he.symm).elim
  · exact H.unique H' hs hi

theorem ConcretePattern.app_l_uniq (H : ConcretePattern registry env p rhs)
    (H' : ConcretePattern registry env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  rcases H with H | ⟨hen, H⟩ | H
  · exact (H.no_app_subpattern hs).elim
  · rcases H' with H' | ⟨_, H'⟩ | H'
    · exact (H'.no_app_subpattern hs').elim
    · exact H.app_l_uniq H' hs hs' hb
    · have hq := contract.quotientRegistered hen
      cases H
      cases H' with
      | @intro data index equation _ hr hl ho hg =>
        obtain ⟨rfl, rfl⟩ := hs.iota_app
        obtain ⟨rfl, rfl⟩ := hs'.iota_app
        exact SimplePattern.iota_app_l_uniq (fun h => (hq.recursor_name_ne hr h.symm).elim) hb
  · rcases H' with H' | ⟨hen, H'⟩ | H'
    · exact (H'.no_app_subpattern hs').elim
    · have hq := contract.quotientRegistered hen
      cases H'
      cases H with
      | @intro data index equation _ hr hl ho hg =>
        obtain ⟨rfl, rfl⟩ := hs.iota_app
        obtain ⟨rfl, rfl⟩ := hs'.iota_app
        exact SimplePattern.iota_app_l_uniq (fun h => (hq.recursor_name_ne hr h).elim) hb
    · exact H.app_l_uniq H' hs hs' hb

theorem ConcretePattern.app_uniq (H : ConcretePattern registry env p rhs)
    (H' : ConcretePattern registry env p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hr : Subpattern right arg') : left.inter right = none := by
  rcases H with H | ⟨hen, H⟩ | H
  · exact (H.no_app_subpattern hs).elim
  · rcases H' with H' | ⟨_, H'⟩ | H'
    · exact (H'.no_app_subpattern hs').elim
    · exact H.app_uniq H' hs hs' hl hr
    · have hq := contract.quotientRegistered hen
      cases H
      cases H' with
      | @intro data index equation _ hrd hlk ho hg =>
        obtain ⟨rfl, rfl⟩ := hs.iota_app
        obtain ⟨rfl, rfl⟩ := hs'.iota_app
        have hrigid := henv.installed_constructor_rigid (hrd.equation_present hg)
          (hrd.equation_major hg)
        apply SimplePattern.iota_app_uniq ?_ hl hr
        intro h
        obtain ⟨eq, lv, he, hh⟩ := hq.lift_head
        exact hrigid eq he lv (by rw [← VExpr.equationHead_eq, hh, h]; rfl)
  · rcases H' with H' | ⟨hen, H'⟩ | H'
    · exact (H'.no_app_subpattern hs').elim
    · have hq := contract.quotientRegistered hen
      cases H'
      cases H with
      | @intro data index equation _ hrd hlk ho hg =>
        obtain ⟨rfl, rfl⟩ := hs.iota_app
        obtain ⟨rfl, rfl⟩ := hs'.iota_app
        apply SimplePattern.iota_app_uniq ?_ hl hr
        intro h
        exact hrd.not_rigid_of_lookup ho hg (h ▸ hq.quotMk_rigid henv)
    · exact H.app_uniq H' hs hs' hl hr

theorem ConcretePattern.const_not_unfolding (H : ConcretePattern registry env (.const c) rhs) :
    registry.recursors c = none ∧ (QuotRegistered env → c ≠ ``Quot.lift) := by
  rcases H with H | ⟨_, H⟩ | H
  · cases H with
    | @intro value hl _ =>
      refine ⟨?_, fun hq => (hq.definition_names henv (contract.definitions _ _ hl).1).1⟩
      cases h : registry.recursors value.name with
      | none => rfl
      | some data => rw [contract.recursorNotDefinition _ _ h] at hl; cases hl
  · cases H
  · cases H

theorem ConcretePattern.ctor_rigid_aux {P : Pattern} {r : P.RHS × P.Check}
    (H : ConcretePattern registry env P r) (hp : (SimplePattern.iota rc mr cc kc).toPattern = P) :
    env.Rigid cc := by
  rcases H with H | ⟨hen, H⟩ | H
  · cases H; cases hp
  · cases H
    obtain ⟨-, -, rfl, -⟩ := SimplePattern.iota_toPattern_inj hp
    exact (contract.quotientRegistered hen).quotMk_rigid henv
  · cases H with
    | @intro data index equation _ hrd hlk ho hg =>
      have hrigid := henv.installed_constructor_rigid (hrd.equation_present hg) (hrd.equation_major hg)
      obtain ⟨-, -, rfl, -⟩ := SimplePattern.iota_toPattern_inj hp
      exact hrigid

theorem ConcretePattern.ctor_rigid
    (H : ConcretePattern registry env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r) :
    env.Rigid cc := by
  have key : ∀ {P r}, ConcretePattern registry env P r →
      P = (SimplePattern.iota rc mr cc kc).toPattern → env.Rigid cc := by
    intro P r H hp
    exact ConcretePattern.ctor_rigid_aux henv contract H hp.symm
  exact key H rfl

end

end Lean4Lean.VEnv
