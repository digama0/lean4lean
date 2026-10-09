import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong

/-! Rigidity of registered structure heads from declaration history.

This proof uses the ownership of stored equations by their declarations and freshness. It
requires no injectivity, uniqueness, or confluence theorem.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- A constant at the head of a typed expression, after leading lambdas are
removed, must be declared in the environment. -/
theorem HasType.head_const_lookup (henv : env.Ordered)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {e type : VExpr} (H : env.HasType U Γ e type)
    (hhead : e.stripLams.getAppFnArgs.1 = .const name levels) :
    ∃ ci, env.constants name = some ci := by
  induction e generalizing Γ type with
  | const n ls =>
    have heq : n = name ∧ ls = levels := by simpa [VExpr.stripLams] using hhead
    rcases heq with ⟨hn, hls⟩
    subst n
    rcases H.const_inv henv hΓ with ⟨ci, hci, _⟩
    exact ⟨ci, hci⟩
  | app fn arg ihfn _ =>
    rcases H.app_inv henv hΓ with ⟨A, B, hf, _⟩
    have hh : fn.getAppFnArgs.1 = .const name levels := by
      simpa [VExpr.stripLams] using hhead
    exact ihfn hΓ hf (by rw [VExpr.stripLams_of_head_const hh]; exact hh)
  | lam domain body _ ihbody =>
    rcases H.lam_inv henv hΓ with ⟨hdomain, type', hbody⟩
    exact ihbody (Γ := domain :: Γ) ⟨hΓ, hdomain⟩ hbody hhead
  | bvar | sort | elim | proj | forallE => cases hhead

/-- Well-formed equations cannot mention an undeclared constant at their
left-hand head. -/
theorem Ordered.rigid_of_absent (henv : env.Ordered)
    (habsent : env.constants name = none) : env.Rigid name := by
  intro df hdf levels hhead
  rcases (henv.defEqWF hdf).1.head_const_lookup henv (Γ := []) ⟨⟩ hhead with ⟨ci, hci⟩
  rw [habsent] at hci
  contradiction

private def ProjectionRigid (env : VEnv) : Prop :=
  ∀ name info, env.projections name info → env.Rigid name ∧ env.Rigid info.ctorName

private theorem ProjectionRigid.addConstVals {env env' : VEnv} {cis : List VConstVal}
    (H : ProjectionRigid env) (hadd : env.addConstVals cis = some env') :
    ProjectionRigid env' := by
  intro name info hinfo
  rw [VEnv.addConstVals_projections hadd] at hinfo
  simpa only [VEnv.Rigid, VEnv.addConstVals_defeqs hadd] using H name info hinfo

private theorem ProjectionRigid.addConst {env env' : VEnv}
    (H : ProjectionRigid env) (hadd : env.addConst name ci = some env') :
    ProjectionRigid env' := by
  intro name info hinfo
  rw [VEnv.addConst_projections hadd] at hinfo
  simpa only [VEnv.Rigid, VEnv.addConst_defeqs hadd] using H name info hinfo

private theorem ProjectionRigid.register
    {base envTypes envCtors : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (hbase : base.Ordered) (hctors : ProjectionRigid envCtors)
    (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctorsAdded : envTypes.addConstVals block.ctors = some envCtors)
    {es : List (Name × InductiveSignature.CaseSchema)} :
    ProjectionRigid ((envCtors.addEliminators es).addProjections block.projections) := by
  intro name info hinfo
  rw [VEnv.addProjections_iff, VEnv.addEliminators_projections] at hinfo
  rcases hinfo with ⟨entry, hentry, rfl, rfl⟩ | hold
  · rw [hprojections] at hentry
    rcases VInductDecl.projectionEntries_origin hentry with
      ⟨type, htype, ctor, hctor, rfl⟩
    have hfresh := VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
      rw [htypesSource]
      exact List.mem_map.mpr ⟨type, htype, rfl⟩)
    have hrigid := hbase.rigid_of_absent hfresh
    have hc : ctor ∈ block.ctors := by
      rw [hctorsSource]
      exact List.mem_flatMap.mpr ⟨type, htype, by rw [hctor]; exact List.mem_singleton_self _⟩
    have hfreshC := VEnv.addConstVals_names_fresh hctorsAdded ctor hc
    have habsent : base.constants ctor.name = none := by
      cases h : base.constants ctor.name with
      | none => rfl
      | some c => rw [(VEnv.addConstVals_le htypes).constants h] at hfreshC; cases hfreshC
    have hrigidC := hbase.rigid_of_absent habsent
    simp only [VEnv.Rigid, VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs,
      VEnv.addConstVals_defeqs hctorsAdded, VEnv.addConstVals_defeqs htypes]
    exact ⟨hrigid, hrigidC⟩
  · simpa only [VEnv.Rigid, VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using hctors name info hold

private theorem ProjectionRigid.addRules {env : VEnv} {rules : List VDefEq}
    (H : ProjectionRigid env)
    (hnew : ∀ rule ∈ rules, ∀ name info, env.projections name info →
      ∀ levels, rule.lhs.stripLams.getAppFnArgs.1 ≠ .const name levels ∧
        rule.lhs.stripLams.getAppFnArgs.1 ≠ .const info.ctorName levels) :
    ProjectionRigid (env.addDefEqRules rules) := by
  induction rules generalizing env with
  | nil => exact H
  | cons rule rules ih =>
    apply ih (env := env.addDefEq rule)
    · intro name info hinfo
      refine ⟨fun df hdf levels => ?_, fun df hdf levels => ?_⟩
      · rcases hdf with rfl | hdf
        · exact (hnew df (by simp) name info hinfo levels).1
        · exact (H name info hinfo).1 df hdf levels
      · rcases hdf with rfl | hdf
        · exact (hnew df (by simp) name info hinfo levels).2
        · exact (H name info hinfo).2 df hdf levels
    · intro df hdf name info hinfo levels
      exact hnew df (by simp [hdf]) name info hinfo levels

private theorem ProjectionRigid.compileRules {pre recEnv : VEnv} {block : VInductBlock}
    (H : ProjectionRigid pre) (hordered : pre.Ordered)
    (hrecs : pre.addConstVals block.recursors = some recEnv)
    (hheads : ∀ df ∈ block.rules, ∃ recursor ∈ block.recursors, ∃ levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const recursor.name levels) :
    ProjectionRigid (recEnv.addDefEqRules block.rules) := by
  apply (H.addConstVals hrecs).addRules
  intro df hdf name info hinfo levels
  rw [VEnv.addConstVals_projections hrecs] at hinfo
  rcases hheads df hdf with ⟨recursor, hrecursor, ls, hrecHead⟩
  have hfresh := VEnv.addConstVals_names_fresh hrecs recursor hrecursor
  constructor
  · intro hhead
    rcases hordered.projectionConstant hinfo with ⟨ci, hci⟩
    have hn : recursor.name = name := (VExpr.const.inj (hrecHead.symm.trans hhead)).1
    rw [hn, hci] at hfresh
    contradiction
  · intro hhead
    have hci := hordered.projectionConstructor hinfo
    have hn : recursor.name = info.ctorName := (VExpr.const.inj (hrecHead.symm.trans hhead)).1
    rw [hn, hci] at hfresh
    contradiction

private theorem ProjectionRigid.addInduct {base env' : VEnv} {decl : VInductDecl}
    (H : ProjectionRigid base) (hbase : base.Ordered)
    (hdecl : decl.WF base) (hadd : VEnv.AddInduct base decl env') :
    ProjectionRigid env' := by
  cases hadd with
  | @intro block _ _ hcompile hblock _ hinstall =>
    rcases hblock with ⟨envTypes, envCtors, envRecs, htypes, hctors, hrecs,
      htypesWF, hctorsWF, hrecsWF, hrulesWF⟩
    have henvTypes := hbase.addConstVals htypesWF htypes
    have henvCtors := henvTypes.addConstVals hctorsWF hctors
    have hparams := hdecl.sourceParameterWF (by rwa [hcompile.types] at htypes)
    have hpreOrdered := Ordered.inductProjections (es := block.eliminators) hbase henvCtors hcompile.sourceNames hdecl.1.sourceTypes
      hdecl.1.2.2.2.1 (hdecl.1.constructorsWF_at (by rwa [hcompile.types] at htypes))
      hparams hparams.rawCtorShape hcompile.types hcompile.ctors hcompile.projections htypes hctors
    have hpreRigid := (H.addConstVals htypes).addConstVals hctors
    have hpreRegistered := hpreRigid.register (es := block.eliminators) hbase hcompile.types hcompile.ctors hcompile.projections htypes hctors
    have hresult := hpreRegistered.compileRules hpreOrdered hrecs hcompile.equation_head_owned
    simp [VInductBlock.install, htypes, hctors, hrecs] at hinstall
    cases hinstall
    exact hresult

private theorem ProjectionRigid.addDefinitions {env env' : VEnv} {cis : List VDefVal}
    (H : ProjectionRigid env) (hordered : env.Ordered)
    (hadd : env.addConsts cis = some env') : ProjectionRigid (env'.addDefEqs cis) := by
  rw [VEnv.addDefEqs_eq_addDefEqRules]
  apply H.compileRules (block := {
    types := [], ctors := [], projections := []
    recursors := cis.map (·.toVConstVal), rules := cis.map (·.toDefEq) }) hordered
  · rwa [← VEnv.addConsts_eq_addConstVals]
  · intro df hdf
    rcases List.mem_map.mp hdf with ⟨ci, hci, rfl⟩
    exact ⟨ci.toVConstVal, List.mem_map.mpr ⟨ci, hci, rfl⟩,
      VLevel.params ci.uvars, rfl⟩

private theorem ProjectionRigid.addQuot {env env' : VEnv}
    (H : ProjectionRigid env) (hordered : env.Ordered)
    (hadd : env.addQuot = some env') : ProjectionRigid env' := by
  let constants : List VConstVal := [
    { name := ``Quot, toVConstant := quotConst },
    { name := ``Quot.mk, toVConstant := quotMkConst },
    { name := ``Quot.lift, toVConstant := quotLiftConst },
    { name := ``Quot.ind, toVConstant := quotIndConst }]
  simp [VEnv.addQuot] at hadd
  rcases hadd with ⟨e1, h1, e2, h2, e3, h3, pre, h4, rfl⟩
  have hpre : env.addConstVals constants = some pre := by
    simp [constants, VEnv.addConstVals, h1, h2, h3, h4]
  apply H.compileRules (block := {
    types := [], ctors := [], projections := []
    recursors := constants, rules := [quotDefEq] }) hordered hpre
  intro df hdf
  rcases List.mem_singleton.mp hdf with rfl
  refine ⟨{ name := ``Quot.lift, toVConstant := quotLiftConst }, by simp [constants], [.param 0, .param 1], ?_⟩
  rfl

/-- Registered structure heads and their constructors remain rigid through
every declaration extension. Canonical recursor ownership excludes new
inductive equations; constant freshness excludes definitions and the quotient
equation. -/
private theorem WF.projectionRigid_both {env : VEnv} (H : env.WF) : ProjectionRigid env := by
  suffices h : ∀ {ds env}, VEnv.WF' ds env → ProjectionRigid env from h H.choose_spec
  intro ds env H
  induction H with
  | empty => intro _ _ hinfo; cases hinfo
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | @decl d env' ds env hdecl hbase ih =>
    have hordered := (show env.WF from ⟨ds, hbase⟩).ordered
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd => exact ih.addConst hadd
    | «example» => exact ih
    | @«def» _ _ ci _ hadd =>
      exact ih.addDefinitions (cis := [ci]) hordered (by
        simpa [VEnv.addConsts] using hadd)
    | mutualDef _ hadd _ => exact ih.addDefinitions hordered hadd
    | quot _ hadd => exact ih.addQuot hordered hadd
    | induct hadd => exact ih.addInduct hordered hadd.sourceWF hadd
  | @inductProjections baseDecls ds base envTypes envCtors decl block
      hbase hctorsWF _ hsource htypesWF hconstructorUvars hctorsTyped hparams hshape htypesSource
      hctorsSource hprojections htypes hctors ihBase ihCtors =>
    have hrigid : ProjectionRigid envCtors := by
      intro name info hinfo
      have := ihCtors name info (by simpa using hinfo)
      simpa only [VEnv.Rigid, VEnv.addEliminators_defeqs] using this
    exact hrigid.register (show base.WF from ⟨baseDecls, hbase⟩).ordered
      htypesSource hctorsSource hprojections htypes hctors

/-- Registered structure heads remain rigid through every declaration
extension. -/
theorem WF.projectionRigid {env : VEnv} (H : env.WF)
    {name : Name} {info : VProjectionInfo} (hinfo : env.projections name info) :
    env.Rigid name := (H.projectionRigid_both name info hinfo).1

end VEnv
end Lean4Lean
