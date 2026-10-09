import Lean4Lean.Theory.Typing.Confluence.StructureParams
import Lean4Lean.Theory.Typing.Confluence.Patterns
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Typing.Confluence.QuotPatterns
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Typing.Confluence.RegistryOfWF
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaSoundness
import Lean4Lean.Theory.Typing.Confluence.StructureConstructorHistory
import Lean4Lean.Theory.Inductive.SourceShape
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.ProjectionRigidity
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.CaseFormation
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Confluence.QuotPrefixTyping
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.CaseSchemaLemmas
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseCapture
import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Inductive.RecursorEquationCoverage
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Typing.EliminatorCoherence
import Lean4Lean.Theory.Typing.StoredRuleHeads
import Lean4Lean.Theory.Typing.EnvTables.CaseMajors
import Lean4Lean.Std.Basic

/-! The structure-major facts of the concrete pattern table.

A recursor or quotient iota major of structure type is a saturated application
of the structure's constructor, and recursor computation at a structure
constructor reads only its fields. Both are consequences of declaration
provenance: the major constructor of every installed equation is the
projection constructor of its registered result family
(`WF.structureCtorCoherent`), a registered structure is never the primitive
quotient type, and a recursor rule's constructor parameter prefix is the
parameter telescope recorded by that family's projection metadata. -/

namespace Lean4Lean.VEnv
open InductiveSignature VExpr HeadRegistry
open private declaration_le from Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
set_option linter.unusedSectionVars false

variable {env : VEnv}

theorem _root_.Lean4Lean.VExpr.forallResult_telescope (e : VExpr) :
    ∃ doms, e = VExpr.wrapForalls doms e.forallResult ∧ doms.length = e.forallArity := by
  induction e with
  | forallE d b _ ih =>
    obtain ⟨doms, he, hl⟩ := ih
    exact ⟨d :: doms, by
      change VExpr.forallE d b = VExpr.forallE d (VExpr.wrapForalls doms b.forallResult)
      rw [← he], by simp [VExpr.forallArity, hl]⟩
  | _ => exact ⟨[], rfl, rfl⟩

private theorem instL_wrapForalls' (ds : List VExpr) (body : VExpr) (packed : List VLevel) :
    (VExpr.wrapForalls ds body).instL packed =
      VExpr.wrapForalls (ds.map (·.instL packed)) (body.instL packed) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [VExpr.wrapForalls, List.foldr_cons, List.map_cons, VExpr.instL] at ih ⊢; rw [ih]

/-- A saturated application whose head returns a rigid family and whose own
type is an application of a rigid family supplies the whole telescope, and the
two families agree. -/
theorem HasType.mkApps_rigid_family (henv : VEnv.WF env)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hF : env.Rigid F) (hG : env.Rigid G)
    {f : VExpr} {domains args xs ys : List VExpr} {ls levels : List VLevel}
    (hf : env.HasType U Γ f (VExpr.wrapForalls domains (VExpr.mkApps (.const F ls) xs)))
    (ht : env.HasType U Γ (VExpr.mkApps f args) (VExpr.mkApps (.const G levels) ys)) :
    args.length = domains.length ∧ F = G := by
  induction args generalizing f domains xs with
  | nil =>
    cases domains with
    | nil =>
      have ⟨_, hT⟩ := hf.isType henv.ordered hΓ
      exact ⟨rfl, Classical.byContradiction fun hne =>
        IsDefEqU.rigidApp_ne henv hΓ hF hG hne hT (hf.uniqU henv hΓ ht)⟩
    | cons domain domains =>
      have ⟨_, hT⟩ := ht.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hG hT
        (hf.uniqU henv hΓ ht).symm).elim
  | cons arg args ih =>
    have hfa : VExpr.WF env U Γ (.app f arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.ordered hΓ with ⟨A, B, hfun, harg⟩
    cases domains with
    | nil =>
      have ⟨_, hT⟩ := hf.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hF hT
        (hf.uniqU henv hΓ hfun)).elim
    | cons domain domains =>
      rcases (hf.uniqU henv hΓ hfun).forallE_inv henv hΓ with ⟨⟨_, hd⟩, _⟩
      have ha := harg.defeqU_r henv hΓ ⟨_, hd.symm⟩
      have hfa' := hf.app ha
      change env.HasType U Γ (.app f arg)
        ((VExpr.wrapForalls domains (VExpr.mkApps (.const F ls) xs)).inst arg) at hfa'
      rw [VExpr.wrapForalls_inst, VExpr.inst_mkApps] at hfa'
      obtain ⟨hlen, heq⟩ := ih hfa' ht
      exact ⟨by simpa [VExpr.instDomains] using hlen, heq⟩

/-- The major constructor of an installed equation, applied at a registered
structure type, is that structure's constructor applied to all its parameters
and fields. -/
theorem WF.installed_major_struct (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hdf : env.defeqs equation) (hm : equation.HasConstructorMajor cc)
    (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps)) :
    cc = info.ctorName ∧ fs.length = info.nparams + info.numFields := by
  obtain ⟨ci, hci, F, lsF, hres, _, hrigidF⟩ := henv.installed_constructor_result_rigid hdf hm
  have hhead : VExpr.WF env U Γ (.const cc lsc) := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hs⟩
  obtain ⟨ci', hci', hlw, hlen⟩ := hhead.const_inv henv.ordered hΓ
  rw [hci] at hci'
  cases hci'
  have hc := HasType.const (Γ := Γ) hci hlw hlen
  obtain ⟨doms, hdoms, hdomsLen⟩ := VExpr.forallResult_telescope ci.type
  have hresEq : ci.type.forallResult =
      VExpr.mkApps (.const F lsF) ci.type.forallResult.getAppFnArgs.2 := by
    have h := VExpr.mkApps_getAppFnArgs_eq ci.type.forallResult
    change VExpr.mkApps ci.type.forallResult.getAppFnArgs.1 ci.type.forallResult.getAppFnArgs.2 = _ at h
    rw [hres] at h
    exact h.symm
  rw [hdoms, hresEq, instL_wrapForalls', VExpr.instL_mkApps] at hc
  obtain ⟨hfs, hFfam⟩ := HasType.mkApps_rigid_family henv hΓ hrigidF (henv.projectionRigid hl) hc hs
  subst hFfam
  have hcc := henv.structureCtorCoherent F info hl equation cc hdf hm ⟨ci, lsF, hci, hres⟩
  subst hcc
  refine ⟨rfl, ?_⟩
  have hctor := henv.ordered.projectionConstructor hl
  rw [hci] at hctor
  cases hctor
  obtain ⟨decl, type, ctor, _, _, _, _, _, hnparams, _, _, _, hctorType, _, _, _, hraw, _⟩ :=
    henv.ordered.projectionShape hl
  obtain ⟨doms', result, _, hle, _, _, harity⟩ := hraw.forallArity
  rw [hctorType] at harity
  simp only [List.length_map] at hfs
  change fs.length = info.nparams + (info.ctorType.forallArity - info.nparams)
  change doms.length = info.ctorType.forallArity at hdomsLen
  omega

/-- After the primitive quotient declaration, no structure is registered for
`Quot`. -/
theorem WF'.quot_no_projection (H : VEnv.WF' ds env) :
    VDecl.quot ∈ ds → QuotRegistered env ∧ ∀ info, ¬env.projections ``Quot info := by
  induction H with
  | empty => intro h; cases h
  | @decl d env' ds env hdecl hbase ih =>
    have henv := (show env.WF from ⟨ds, hbase⟩).ordered
    intro hmem
    have hle := declaration_le hdecl
    have hproj : ∀ F info, env'.projections F info → env.projections F info ∨
        env.constants F = none := by
      intro F info hp
      cases hdecl with
      | «axiom» _ hadd | «opaque» _ hadd => rw [VEnv.addConst_projections hadd] at hp; exact .inl hp
      | «example» => exact .inl hp
      | «def» _ hadd =>
        have h := VEnv.addConst_projections hadd
        exact .inl (h ▸ hp)
      | mutualDef _ hadd _ =>
        rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_projections,
          VEnv.addConstVals_projections (VEnv.addConsts_eq_addConstVals ▸ hadd)] at hp
        exact .inl hp
      | quot _ hadd =>
        simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hadd
        obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hadd
        have h : (d.addDefEq quotDefEq).projections = env.projections :=
          (VEnv.addConst_projections hd).trans <| (VEnv.addConst_projections hc).trans <|
            (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)
        exact .inl (h ▸ hp)
      | induct hadd =>
        cases hadd with
        | intro _ hcompile _ _ hinstall =>
          simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at hinstall
          obtain ⟨envTypes, htypes, envCtors, hctors, envRecs, hrecs, rfl⟩ := hinstall
          rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hrecs,
            VEnv.addProjections_iff, VEnv.addEliminators_projections,
            VEnv.addConstVals_projections hctors,
            VEnv.addConstVals_projections htypes] at hp
          rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hp
          · rw [hcompile.projections] at hentry
            obtain ⟨type, htype, ctor, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
            exact .inr (VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
              rw [hcompile.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩))
          · exact .inl hp
    rcases List.mem_cons.mp hmem with rfl | hold
    · cases hdecl with
      | quot _ hadd =>
        refine ⟨.of_addQuot hadd, fun info hp => ?_⟩
        simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hadd
        obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hadd
        have h : (d.addDefEq quotDefEq).projections = env.projections :=
          (VEnv.addConst_projections hd).trans <| (VEnv.addConst_projections hc).trans <|
            (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)
        obtain ⟨_, hq⟩ := henv.projectionConstant (h ▸ hp)
        unfold VEnv.addConst at ha
        split at ha
        · cases ha
        · rename_i hnone; rw [hnone] at hq; cases hq
    · obtain ⟨hq, hno⟩ := ih hold
      refine ⟨hq.mono hle, fun info hp => ?_⟩
      rcases hproj _ info hp with hp | hfresh
      · exact hno info hp
      · rw [hq.quotient] at hfresh; cases hfresh
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hmem
    obtain ⟨hq, hno⟩ := ih hmem
    exact ⟨hq.mono VEnv.addEliminator_le, fun info hp => hno info hp⟩
  | @inductProjections baseDecls ds base envTypes envCtors decl block
      hbase _ _ _ _ _ _ _ _ htypesSource _ hprojections htypes hctors _ ihCtors =>
    intro hmem
    obtain ⟨hq, hno⟩ := ihCtors hmem
    have hbaseOrdered := (show base.WF from ⟨baseDecls, hbase⟩).ordered
    have hleCtors : base ≤ envCtors.addEliminators block.eliminators :=
      (VEnv.addConstVals_le htypes).trans ((VEnv.addConstVals_le hctors).trans
        VEnv.addEliminators_le)
    refine ⟨hq.mono VEnv.addProjections_le, fun info hp => ?_⟩
    rw [VEnv.addProjections_iff] at hp
    rcases hp with ⟨entry, hentry, hname, rfl⟩ | hp
    · have hdf : (envCtors.addEliminators block.eliminators).defeqs = base.defeqs :=
        VEnv.addEliminators_defeqs.trans <|
        (VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)
      have hqd : base.defeqs quotDefEq := hdf ▸ hq.equation
      have hmk : quotDefEq.HasConstructorMajor ``Quot.mk :=
        ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
      obtain ⟨ci, hci⟩ := hbaseOrdered.constructorMajor_declared hqd hmk
      have hci' := hleCtors.constants hci
      rw [hq.constructor] at hci'
      cases hci'
      have hrf : base.ResultFamily ``Quot.mk ``Quot := ⟨_, [.param 0], hci, by rfl⟩
      obtain ⟨cF, hcF⟩ := hbaseOrdered.resultFamily_declared hrf
      rw [hprojections] at hentry
      obtain ⟨type, htype, ctor, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
      have hfresh := VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
        rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      change base.constants type.name = none at hfresh
      have hname' : type.name = ``Quot := hname.symm
      rw [hname', hcF] at hfresh
      cases hfresh
    · exact hno info hp

theorem _root_.List.drop_append_ge {l1 l2 : List α} (h : l1.length ≤ n) :
    (l1 ++ l2).drop n = l2.drop (n - l1.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem Pattern.argumentRHS_var (p : Pattern) (n : Nat) :
    ∀ x ∈ p.argumentRHS n, ∃ path, x = .var path := by
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
    intro x hx
    simp only [Pattern.argumentRHS, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl
    · obtain ⟨path, rfl⟩ := ih y hy
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem Pattern.Matches.const_arguments_eq
    (H : ((Pattern.const name).varN n).Matches (VExpr.mkApps (.const name levels) args) levels values)
    (levels' : List VLevel) :
    ((Pattern.const name).argumentRHS n).map (fun rhs => rhs.apply levels' values) = args := by
  have h := congrArg VExpr.getAppFnArgs H.const_arguments
  rw [spine_mkApps_exact _ _ rfl, spine_mkApps_exact _ _ rfl] at h
  have h2 := (Prod.mk.inj h).2
  rw [h2]
  apply List.map_congr_left
  intro x hx
  obtain ⟨path, rfl⟩ := Pattern.argumentRHS_var _ _ x hx
  rfl

section
variable {registry : Registry} {declarations : List VDecl}

/-- A recursor or quotient iota major of structure type is a saturated
application of the structure's constructor. -/
theorem ConcretePattern.struct_major (henv : env.WF)
    (H : ConcretePattern registry env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hΓ : OnCtx Γ (env.IsType U)) (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps))
    (hlen : fs.length = kc) : cc = info.ctorName ∧ kc = info.nparams + info.numFields := by
  have hmajor : ∃ equation, env.defeqs equation ∧ equation.HasConstructorMajor cc := by
    rcases H with H | ⟨_, H⟩ | H
    · exact (DefinitionPattern.not_iota (recursor := rc) (major := mr) (ctor := cc) (fields := kc) H).elim
    · obtain ⟨hq, -, -, hccq, -⟩ := QuotPattern.registered (recursor := rc) (major := mr)
        (ctor := cc) (fields := kc) H
      subst hccq
      exact ⟨quotDefEq, hq.equation, ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩⟩
    · obtain ⟨data, index, equation, _, hr, _, _, hg, he, _⟩ := H.generated
      obtain ⟨-, -, hccd, -⟩ := SimplePattern.iota_toPattern_inj (a := rc) (b := mr) (c := cc)
        (d := kc) he
      subst hccd
      exact ⟨equation, hr.equation_present hg, hr.equation_major hg⟩
  obtain ⟨equation, hdf, hm⟩ := hmajor
  obtain ⟨hcc, hfs⟩ := henv.installed_major_struct hΓ hdf hm hl hs
  exact ⟨hcc, hlen ▸ hfs⟩

/-- Generated iota computation at a structure constructor reads only its
fields, not its parameters. -/
theorem ConcretePattern.iota_params (henv : env.WF)
    (contract : registry.EnvironmentContract env declarations)
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (H : ConcretePattern registry env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hl : env.projections family info) (hcc : cc = info.ctorName)
    (hm : ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc) (ps ++ fields)) lsc g)
    (hm' : ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc') (ps' ++ fields)) lsc' g')
    (hps : ps.length = info.nparams) (hps' : ps'.length = info.nparams) :
    (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr),
      Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          m1 (Sum.elim g1 g) r.1 =
        Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          m1 (Sum.elim g1 g') r.1) ∧
    (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr)
      (df : VExpr → VExpr → Prop),
      Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          df m1 (Sum.elim g1 g) r.2 →
        Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          df m1 (Sum.elim g1 g') r.2) := by
  rcases H with H | ⟨hen, H⟩ | H
  · exact (DefinitionPattern.not_iota (recursor := rc) (major := mr) (ctor := cc) (fields := kc) H).elim
  · obtain ⟨hq, -, -, hccq, -⟩ := QuotPattern.registered (recursor := rc) (major := mr)
      (ctor := cc) (fields := kc) H
    exfalso
    have hrf := henv.ordered.projection_resultFamily hl
    rw [← hcc, hccq] at hrf
    have hF := hrf.unique (⟨_, [.param 0], hq.constructor, by rfl⟩ : env.ResultFamily ``Quot.mk ``Quot)
    subst hF
    exact (WF'.quot_no_projection contract.history (contract.quotient.mp hen)).2 info hl
  · obtain ⟨data, index, equation, hclosed, hr, _, _, hg, he, hrhs⟩ := H.generated
    obtain ⟨hrc, hmr, hccd, hkc⟩ := SimplePattern.iota_toPattern_inj (a := rc) (b := mr) (c := cc)
      (d := kc) he
    subst hrc hmr hccd hkc
    obtain rfl := eq_of_heq hrhs
    have hcount := hr.rule_param_count henv hg hl hcc
    have hargs := Pattern.Matches.const_arguments_eq hm
    have hargs' := Pattern.Matches.const_arguments_eq hm'
    refine ⟨fun m1 g1 => ?_, fun m1 g1 df h => ?_⟩
    · dsimp only
      rw [RecursorData.ruleRHS]
      refine (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).trans
        (Eq.trans ?_ (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).symm)
      rw [RecursorData.ruleCaptures]
      simp only [List.map_append, List.map_map]
      have hpre : ∀ (L : List ((Pattern.const data.name).varN data.majorOffset).RHS),
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g) rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inl) L =
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g') rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inl) L := by
        intro L
        apply List.map_congr_left
        intro x _
        exact (Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) (levels := m1)
          (values := Sum.elim g1 g) Sum.inl x).trans
          (Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) (levels := m1)
            (values := Sum.elim g1 g') Sum.inl x).symm
      have hpost : ∀ (L : List ((Pattern.const (data.ruleConstructor index)).varN
          (RecursorData.ruleMajorArguments equation).length).RHS),
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g) rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inr) L =
          List.map (fun rhs => rhs.apply m1 g) L := by
        intro L
        apply List.map_congr_left
        intro x _
        exact Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inr x
      have hpost' : ∀ (L : List ((Pattern.const (data.ruleConstructor index)).varN
          (RecursorData.ruleMajorArguments equation).length).RHS),
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g') rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inr) L =
          List.map (fun rhs => rhs.apply m1 g') L := by
        intro L
        apply List.map_congr_left
        intro x _
        exact Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inr x
      rw [hpre, hpost, hpost', List.map_drop, List.map_drop, hargs m1, hargs' m1]
      have hd : ps.length ≤ (RecursorData.ruleMajorArguments equation).length -
          data.schema.signature.constructors[index].fields.length := by omega
      have hd' : ps'.length ≤ (RecursorData.ruleMajorArguments equation).length -
          data.schema.signature.constructors[index].fields.length := by omega
      rw [List.drop_append_ge hd, List.drop_append_ge hd', hps, hps']
      rfl
    · revert h
      unfold RecursorData.ruleCheck
      split <;> simp [Pattern.Check.OK]

end

end Lean4Lean.VEnv

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr
open private reduction_head_app reduction_head_mkApps restoration_vars view_constructor_external
  from Lean4Lean.Theory.Inductive.CaseReductionLemmas
/-- The constructor major of a generated case rule is the restored generated
constructor application: its head is the restored constructor name, it ends
with exactly the rule's captured field variables, and its parameter prefix is
the common parameters or the certified container arguments. -/
theorem Generates.ctor_shape {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length)
    (hgen : schema.Generates block owner rule) :
    ∃ index : Fin (schema.view owner).constructors.size,
      rule.application.ctorName =
        schema.restoration.headName (schema.view owner).constructors[index].name ∧
      ((schema.restoration.heads.find? (fun h => h.auxiliary ==
          (schema.view owner).constructors[index].name) = none ∧
        rule.application.ctorArguments.length = schema.signature.params.length + rule.numFields) ∨
      ∃ spec, schema.restoration.heads.find? (fun h => h.auxiliary ==
          (schema.view owner).constructors[index].name) = some spec ∧
        rule.application.ctorArguments.length = spec.arguments.length +
          (schema.signature.params.length - spec.nparams) + rule.numFields) := by
  obtain ⟨rules, hg, hm, he⟩ := hgen
  obtain ⟨index, hrestore⟩ := equation_of_mem hg hm
  have ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  let nf := ctor.fields.length
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let np := (schema.view owner).params.length + extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let major := g.constructorApp ctor extra 0
  have hnoRec := view_constructor_external (schema := schema) (owner := owner) index
  obtain ⟨ds', lhs', rhs', type', hl', hr', _, hel, her, het, _⟩ :=
    restored_common_telescope hl hr ht
  have hrhs : rhs' = VExpr.mkApps (.bvar (nf + (schema.view owner).constructors.size - 1 - index.val))
      (vars nf 0) := by
    change schema.restoration.expr (VExpr.mkApps _ _) = some rhs' at hr'
    simp only [hnoRec, List.map_nil, List.append_nil] at hr'
    change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hr'
    rw [restoration_mkApps] at hr'
    simp [restoration_vars, Restoration.expr.go] at hr'
    exact hr'.symm
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [view_familyCount] at this
    omega
  have hlhs0 : schema.restoration.expr
      (VExpr.mkApps (.elim block owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices ++ [major])) = some lhs' := by
    simpa only [Instance.recursorHead, hzero, Nat.add_zero] using hl'
  change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at hlhs0
  rw [restoration_mkApps] at hlhs0
  simp [List.mapM_append, restoration_vars, List.mapM_cons, Restoration.expr.go] at hlhs0
  obtain ⟨allArgs, ⟨restArgs, ⟨indices', hi, majorArgs, ⟨major', hmajor, rfl⟩, rfl⟩, rfl⟩, hout⟩ := hlhs0
  have hlhs : lhs' = .app
      (VExpr.mkApps (.elim block owner.val (g.targetLevel :: g.levels))
        (vars np nf ++ indices')) major' := by
    simpa [VExpr.mkApps, List.foldl_append] using hout.symm
  have hmParams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ (schema.view owner).params.length :=
    hparams
  obtain ⟨cl, cargs, hmajEq⟩ := Restoration.const_mkApps hmajor
  have hcount := restored_ctorApp_count hmParams hmajor
  have ha : Application.extract lhs' = some
      ⟨block, owner.val, g.targetLevel :: g.levels, vars np nf ++ indices',
        schema.restoration.headName ctor.name, cl, cargs⟩ := by
    rw [hlhs, hmajEq]
    simp only [Application.extract,
      spine_mkApps_exact (.elim block owner.val (g.targetLevel :: g.levels)) _ rfl,
      spine_mkApps_exact (.const (schema.restoration.headName ctor.name) cl) _ rfl]
  have hhead : lhs'.getAppFnArgs.1 = .elim block owner.val (g.targetLevel :: g.levels) := by
    rw [hlhs, reduction_head_app]
    exact reduction_head_mkApps _ _
  have hb := extract_wrap (rhs := rhs') (type := type') hhead ds'
  rw [← hel, ← her, ← het] at hb
  simp [AppliedRule.extract, hb, ha] at he
  have hnf : rule.numFields = nf := by
    rw [← he]
    simp only [AppliedRule.numFields]
    rw [hrhs, spine_mkApps_exact _ _ rfl]
    simp [vars]
  have hargsEq : rule.application.ctorArguments = cargs := by rw [← he]
  have hcargs : major'.getAppFnArgs.2 = cargs := by rw [hmajEq, spine_mkApps_exact _ _ rfl]
  refine ⟨index, by rw [← he], ?_⟩
  rw [hargsEq, hnf, ← hcargs]
  exact hcount
end Lean4Lean.InductiveSignature.CaseSchema
namespace Lean4Lean.VEnv
open InductiveSignature CaseSchema VExpr
set_option linter.unusedSectionVars false
variable {env : VEnv}
theorem CaseStep.generated (H : CaseStep env U Γ rule levels arguments) :
    ∃ block schema owner, env.eliminators block schema ∧ schema.Generates block owner rule := by
  cases H with
  | iota hl hg => exact ⟨_, _, _, hl, hg⟩
private theorem instL_wrapForalls'' (ds : List VExpr) (body : VExpr) (packed : List VLevel) :
    (VExpr.wrapForalls ds body).instL packed =
      VExpr.wrapForalls (ds.map (·.instL packed)) (body.instL packed) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [VExpr.wrapForalls, List.foldr_cons, List.map_cons, VExpr.instL] at ih ⊢; rw [ih]
/-- A saturated constant application at a rigid family type supplies the
constant's whole telescope, and its declared result family is that family. -/
theorem HasType.const_spine_family (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hci : env.constants c = some ci) (hres : ci.type.forallResult.getAppFnArgs.1 = .const F lsF)
    (hF : env.Rigid F) (hG : env.Rigid G)
    (hs : env.HasType U Γ (VExpr.mkApps (.const c lsc) fs) (VExpr.mkApps (.const G ls) ps)) :
    fs.length = ci.type.forallArity ∧ F = G := by
  have hhead : VExpr.WF env U Γ (.const c lsc) := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hs⟩
  obtain ⟨ci', hci', hlw, hlen⟩ := hhead.const_inv henv.ordered hΓ
  rw [hci] at hci'
  cases hci'
  have hc := HasType.const (Γ := Γ) hci hlw hlen
  obtain ⟨doms, hdoms, hdomsLen⟩ := VExpr.forallResult_telescope ci.type
  have hresEq : ci.type.forallResult =
      VExpr.mkApps (.const F lsF) ci.type.forallResult.getAppFnArgs.2 := by
    have h := VExpr.mkApps_getAppFnArgs_eq ci.type.forallResult
    change VExpr.mkApps ci.type.forallResult.getAppFnArgs.1 ci.type.forallResult.getAppFnArgs.2 = _ at h
    rw [hres] at h
    exact h.symm
  rw [hdoms, hresEq, instL_wrapForalls'', VExpr.instL_mkApps] at hc
  obtain ⟨hfs, hFG⟩ := HasType.mkApps_rigid_family henv hΓ hF hG hc hs
  simp only [List.length_map] at hfs
  exact ⟨hfs.trans hdomsLen, hFG⟩
/-- A case major of structure type is a saturated application of the
structure's constructor, and the case rule captures only its fields. This
needs `EliminatorsCoherent`, which is not a consequence of `env.WF`. -/
theorem CaseRedex.struct_major (henv : env.WF) (hcoh : env.EliminatorsCoherent)
    (hm : CaseRedex env U Γ rule actual) (hΓ : OnCtx Γ (env.IsType U))
    (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
      (VExpr.mkApps (.const family ls) ps)) :
    actual.ctorName = info.ctorName ∧
      actual.ctorArguments.length = info.nparams + info.numFields ∧
      rule.numFields ≤ info.numFields := by
  obtain ⟨block, schema, owner, hlookup, hgen⟩ := hm.source.generated
  obtain ⟨base, source, sblock, hbaseLe, hcert, hconst, hproj⟩ := hcoh block schema hlookup
  have hcert' := hcert
  obtain ⟨expanded, aux, hdata, hprior, hres, hfam, hdisj⟩ := hcert
  have hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length :=
    fun h hh => Nat.le_of_eq (hcert'.restoration_nparams h hh)
  obtain ⟨index, hname, hcount⟩ := hgen.ctor_shape hparams
  obtain ⟨sctor, hsctor, _, hvc⟩ := view_constructor_eq_caseConstructor index
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hsctor
  have hi' : i < schema.signature.constructors.size := by simpa using hi
  let sidx : Fin schema.signature.constructors.size := ⟨i, hi'⟩
  have hsidx : schema.signature.constructors[sidx] = sctor := by
    simpa only [sidx, Fin.getElem_fin, Array.getElem_toList] using hget
  have hvname : (schema.view owner).constructors[index].name =
      schema.signature.constructors[sidx].name := by
    rw [hvc, hsidx]; rfl
  rw [hvname, hres] at hname hcount
  have hctorEq : actual.ctorName = (compilationRestoration source aux).headName
      schema.signature.constructors[sidx].name := hm.ctor_eq.trans hname
  have hlenEq : actual.ctorArguments.length = rule.application.ctorArguments.length :=
    hm.ctorArguments_length
  have hnp := hdata.model.nparams.trans hdata.nparams
  obtain ⟨envTypes, direct, _, _, hwf, _⟩ := hdata.correspondence
  rcases hdata.constructor_origin sidx with ⟨type, htype, ctor, hctor, hn⟩ | ⟨a, ha, actor, hactor, hn⟩
  · have hsourceName : schema.signature.constructors[sidx].name ∈ familyNames source.types := by
      rw [hn]
      exact List.mem_flatMap.mpr ⟨type, htype, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
    rcases hcount with ⟨_, hlen⟩ | ⟨spec, hfind, _⟩
    · rw [hdata.headName_source hdisj hsourceName, hn] at hctorEq
      have hmem : ctor ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨type, htype, hctor⟩
      have hlookup' : env.constants ctor.name = some ctor.toVConstant :=
        hconst ctor (List.mem_append_right _ (by rw [hdata.ctors]; exact hmem))
      obtain ⟨lsF, hresF⟩ := hdata.ctor_result type htype ctor hctor
      have hrigid : env.Rigid type.name :=
        henv.case_source_family_rigid hlookup (by rw [hfam]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      rw [hctorEq] at hs
      obtain ⟨harity, hF⟩ := HasType.const_spine_family henv hΓ hlookup' hresF hrigid
        (henv.projectionRigid hl) hs
      subst hF
      have hentry := hproj type htype info hl
      obtain ⟨type', htype', c', hct', heq⟩ := VInductDecl.projectionEntries_origin hentry
      simp only [VProjectionEntry.mk.injEq] at heq
      obtain ⟨htn, rfl⟩ := heq
      have htt : type = type' :=
        VInductDecl.type_eq_of_mem_name hdata.sourceWF.2.1 htype htype' htn
      subst htt
      rw [hct'] at hctor
      obtain rfl := List.mem_singleton.mp hctor
      refine ⟨hctorEq, ?_, ?_⟩
      · simp only [VProjectionInfo.numFields]
        change actual.ctorArguments.length = ctor.type.forallArity at harity
        omega
      · simp only [VProjectionInfo.numFields]
        change actual.ctorArguments.length = ctor.type.forallArity at harity
        omega
    · have hm' := List.mem_of_find?_eq_some hfind
      have hsn : spec.auxiliary = schema.signature.constructors[sidx].name := by
        simpa using List.find?_some hfind
      exact (hdata.source_head_disjoint hsourceName (List.mem_map.mpr ⟨spec, hm', hsn⟩)).elim
  · have hmem : (⟨a.constructorName actor, source.uvars, source.nparams, actor.name, a.levels,
        a.arguments⟩ : HeadSpecialization) ∈ (compilationRestoration source aux).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨actor, hactor, rfl⟩)⟩
    have hf := Restoration.find_of_mem hdata.restorationScoped hmem
    rcases hcount with ⟨hfind, _⟩ | ⟨spec, hfind, hlen⟩
    · rw [← hn, hfind] at hf; cases hf
    rw [← hn, hfind] at hf
    cases hf
    rw [hn, hdata.headName_auxiliary_constructor ha hactor] at hctorEq
    obtain ⟨b0, cblock, inst0, hc0, hi0, hle0⟩ :=
      VEnv.ContainersInstalled.container_installed hprior ha
    have hle : inst0 ≤ env := hle0.trans hbaseLe
    have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
    have hcmem : actor ∈ a.container.constructorConstants :=
      List.mem_flatMap.mpr ⟨a.source, hsrc, hactor⟩
    obtain ⟨eq, heq, fn, lv, args, hmaj⟩ := hc0.constructor_equation actor hcmem
    have hdf : env.defeqs eq := hle.defeqs (VInductBlock.install_rule hi0 heq)
    rw [hctorEq] at hs
    obtain ⟨hcn, hlenStruct⟩ := henv.installed_major_struct hΓ hdf ⟨fn, lv, args, hmaj⟩ hl hs
    obtain ⟨lsF, hresF⟩ := hc0.ctor_result a.source hsrc actor hactor
    have hlookup' : env.constants actor.name = some actor.toVConstant :=
      hle.constants (VInductBlock.install_ctor_lookup hi0 (by rw [hc0.ctors_eq]; exact hcmem))
    have hF := (henv.ordered.projection_resultFamily hl).unique
      (hcn ▸ (⟨_, lsF, hlookup', hresF⟩ : env.ResultFamily actor.name a.source.name))
    subst hF
    obtain ⟨_, _, hnparams⟩ := CompiledInductive.family_projection henv hc0 hi0 hle hsrc hactor hl
    have hwfa := (hwf a ha).1
    refine ⟨hctorEq.trans hcn, hlenStruct, ?_⟩
    simp only at hlen
    omega
end Lean4Lean.VEnv
