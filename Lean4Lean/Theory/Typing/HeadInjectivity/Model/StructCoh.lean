import Lean4Lean.Theory.Typing.HeadInjectivity.Model.WFFacts

/-! # The constructor of a registered structure, for the model

A pattern constructor whose type returns a registered structure is that structure's constructor
(`WF.structCoh`, along the history), so the projection entry of a family of an installed
declaration whose constructors are pattern constructors is the declaration's own entry
(`projMajor_decl`, `Model/IotaStage.lean`). These are the facts of
`Confluence/StructureMajor.lean` (`WF'.structureCtorCoherent`, `WF.installed_projection`),
restated here because the confluence files import the model, so the model cannot import them
(import cycle). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv}

/-- The type of the constant `c` returns an application of `F`. -/
def RetFam (env : VEnv) (c F : Name) : Prop :=
  ∃ ci ls, env.constants c = some ci ∧ ci.type.forallResult.getAppFnArgs.1 = .const F ls

theorem RetFam.unique {c F F' : Name} (H : RetFam env c F) (H' : RetFam env c F') : F = F' := by
  obtain ⟨ci, ls, hc, hh⟩ := H
  obtain ⟨ci', ls', hc', hh'⟩ := H'
  rw [hc] at hc'
  cases hc'
  exact (VExpr.const.inj (hh.symm.trans hh')).1

theorem RetFam.of_le {env' : VEnv} {c F : Name} {ci : VConstant} (hle : env ≤ env')
    (hc : env.constants c = some ci) (H : RetFam env' c F) : RetFam env c F := by
  obtain ⟨ci', ls, h', hh⟩ := H
  rw [hle.constants hc] at h'
  cases h'
  exact ⟨ci, ls, hc, hh⟩

/-- The result head of a well-formed type is a declared constant. -/
theorem retFam_head_declared (henv : env.OrderedStrong) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {type : VExpr} (H : env.IsType U Γ type) {F : Name}
    {ls : List VLevel} (hh : type.forallResult.getAppFnArgs.1 = .const F ls) :
    ∃ cF, env.constants F = some cF := by
  induction type generalizing Γ with
  | forallE domain body _ ih =>
    obtain ⟨_, h⟩ := H
    obtain ⟨⟨_, hd⟩, _, hb⟩ := h.forallE_inv henv.ordered
    exact ih (Γ := domain :: Γ) ⟨hΓ, _, hd⟩ ⟨_, hb⟩ hh
  | lam => cases hh
  | _ =>
    obtain ⟨_, h⟩ := H
    exact h.head_const_lookup henv hΓ (by simpa only [VExpr.forallResult, VExpr.stripLams] using hh)

theorem _root_.Lean4Lean.VEnv.WF.retFam_declared (henv : env.WF) {c F : Name}
    (H : RetFam env c F) : ∃ cF, env.constants F = some cF := by
  obtain ⟨ci, ls, hc, hh⟩ := H
  exact retFam_head_declared henv.orderedStrong (Γ := []) ⟨⟩ (henv.ordered.constWF hc) hh

theorem forallResult_of_const_head' {e : VExpr} {c : Name} {ls : List VLevel}
    (h : e.getAppFnArgs.1 = .const c ls) : e.forallResult = e := by
  cases e with
  | forallE A B => simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at h
  | _ => rfl

/-- The constructor of a registered structure returns that structure. -/
theorem projection_retFam (henv : env.Ordered) {family : Name} {info : VProjectionInfo}
    (hp : env.projections family info) : RetFam env info.ctorName family := by
  obtain ⟨decl, type, ctor, _, _, hname, _, _, _, _, _, _, hctorType, _, _, _, hraw, _⟩ :=
    henv.projectionShape hp
  obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw
  refine ⟨_, VLevel.params decl.uvars, henv.projectionConstructor hp, ?_⟩
  change info.ctorType.forallResult.getAppFnArgs.1 = _
  rw [← hctorType, heq, VExpr.forallResult_wrapForalls, forallResult_of_const_head' hhead, hhead,
    hname]

/-- A constructor of an installed declaration returns its own type former. -/
theorem addInduct_ctor_retFam {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hdecl : decl.WF env₀) (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    {type : VInductiveType} (htype : type ∈ decl.types) {ctor : VConstVal}
    (hctor : ctor ∈ type.ctors) : RetFam env ctor.name type.name := by
  obtain ⟨envT, -, -, hT, -, -, -⟩ := addInduct_stages hadd
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  obtain ⟨_, _, _, _, _, hraw⟩ := hdecl.sourceParameterWF hT
  obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw type htype ctor hctor
  refine ⟨ctor.toVConstant, VLevel.params decl.uvars,
    hle.constants (addInduct_ctor_find hadd htype hctor), ?_⟩
  change ctor.type.forallResult.getAppFnArgs.1 = _
  rw [heq, VExpr.forallResult_wrapForalls, forallResult_of_const_head' hhead, hhead]

/-- A pattern constructor whose type returns a registered structure is that structure's
constructor. -/
def StructCoh (env : VEnv) : Prop :=
  ∀ F info, env.projections F info → ∀ c, IsPatCtor env c → RetFam env c F → c = info.ctorName

/-- A pattern constructor is a declared constant. -/
theorem _root_.Lean4Lean.VEnv.WF.patCtor_declared' (henv : env.WF) {c : Name}
    (h : IsPatCtor env c) : ∃ ci, env.constants c = some ci := by
  obtain ⟨p, r, recN, M, N, hp, rfl⟩ := h
  obtain ⟨ci, hci, -⟩ := henv.patsIota.ctor_shape hp
  exact ⟨ci, hci⟩

private theorem structCoh_projections {base envTypes envCtors : VEnv}
    {decl : VInductDecl} {block : VInductBlock} (hW : base.WF)
    (htypesEq : block.types = decl.typeConstants)
    (hprojs : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctorsAdd : envTypes.addConstVals block.ctors = some envCtors)
    (ihCtors : StructCoh envCtors) :
    StructCoh (envCtors.addProjections block.projections) := by
  have hle : base ≤ envCtors := (addConstVals_le htypes).trans (addConstVals_le hctorsAdd)
  have hpats : envCtors.pats = base.pats := by
    rw [addConstVals_pats hctorsAdd, addConstVals_pats htypes]
  intro F info hp c hc hres
  have hcBase : IsPatCtor base c := by
    obtain ⟨_, r, recN, M, N, hpp, rfl⟩ := hc
    refine ⟨_, r, recN, M, N, ?_, rfl⟩
    rw [← hpats]; simpa using hpp
  obtain ⟨ci, hci⟩ := hW.patCtor_declared' hcBase
  have hresBase : RetFam base c F :=
    RetFam.of_le (hle.trans addProjections_le) hci hres
  rcases VEnv.addProjections_iff.mp hp with ⟨entry, hentry, rfl, rfl⟩ | hold
  · exfalso
    rw [hprojs] at hentry
    obtain ⟨type, htype, ctor, -, rfl⟩ := VInductDecl.projectionEntries_origin hentry
    obtain ⟨cF, hcF⟩ := hW.retFam_declared hresBase
    have hfresh := addConstVals_names_fresh htypes type.toVConstVal (by
      rw [htypesEq]; exact List.mem_map_of_mem htype)
    change base.constants type.name = none at hfresh
    rw [hfresh] at hcF; cases hcF
  · refine ihCtors F info hold c ?_ (RetFam.of_le addProjections_le
      (hle.constants hci) hres)
    obtain ⟨_, r, recN, M, N, hpp, rfl⟩ := hc
    exact ⟨_, r, recN, M, N, by simpa using hpp, rfl⟩

theorem _root_.Lean4Lean.VEnv.WF'.structCoh {ds : List VDecl} (H : env.WF' ds) :
    StructCoh env := by
  induction H with
  | empty => intro F info hp; cases hp
  | inductProjections hbase _ _ _ _ _ _ _ htypesEq _ hprojs htypes hctorsAdd _ ihCtors =>
    exact structCoh_projections ⟨_, hbase⟩ htypesEq hprojs htypes hctorsAdd ihCtors
  | @decl d env' ds env hd H ih =>
    have hW : env.WF := ⟨ds, H⟩
    have hle := hd.le
    intro F info hp c hc hres
    have old : IsPatCtor env c → env.projections F info → c = info.ctorName := by
      intro hc0 hp0
      obtain ⟨ci, hci⟩ := hW.patCtor_declared' hc0
      exact ih F info hp0 c hc0 (RetFam.of_le hle hci hres)
    have inductCase : ∀ decl : VInductDecl, decl.WF env → env.addInduct decl = some env' →
        c = info.ctorName := by
      intro decl hdecl hadd
      have hcases : IsPatCtor env c ∨
          ∃ type ∈ decl.types, ∃ ctor ∈ type.ctors, ctor.name = c := by
        obtain ⟨p, r, recN, M, N, hpp, rfl⟩ := hc
        rcases addInduct_pats_origin hadd hpp with hold | ⟨rec, hrec, ru, hru, e⟩
        · exact .inl ⟨_, r, recN, M, N, hold, rfl⟩
        · obtain ⟨-, -, rfl, -⟩ := iota_toPattern_inj e
          obtain ⟨block, hcomp, hrecs, -⟩ := hdecl.recsCompiled
          rcases hcomp.rule_ctor_cases hrecs hrec hru with ⟨ctor, hctor, hn⟩ | hpc
          · obtain ⟨type, htype, hctor'⟩ := List.mem_flatMap.1 hctor
            exact .inr ⟨type, htype, ctor, hctor', hn.symm⟩
          · exact .inl hpc
      rcases (addInduct_projections_iff hadd).mp hp with ⟨entry, hentry, rfl, rfl⟩ | hold
      · obtain ⟨type, htype, ctor, hctors, rfl⟩ := VInductDecl.projectionEntries_origin hentry
        rcases hcases with hc0 | ⟨type', htype', ctor', hctor', rfl⟩
        · exfalso
          obtain ⟨ci, hci⟩ := hW.patCtor_declared' hc0
          obtain ⟨cF, hcF⟩ := hW.retFam_declared (RetFam.of_le hle hci hres)
          rw [addInduct_type_fresh hadd htype] at hcF; cases hcF
        · have hF := (addInduct_ctor_retFam hdecl hadd VEnv.LE.rfl htype' hctor').unique hres
          obtain ⟨envT, -, -, hT, -, -, -⟩ := addInduct_stages hadd
          have hT' := addTypes_nodup hT
          have htt : type' = type :=
            VEnv.inj_on_of_nodup_map hT' htype' htype hF
          subst htt
          rw [hctors, List.mem_singleton] at hctor'
          subst hctor'
          rfl
      · rcases hcases with hc0 | ⟨type', htype', ctor', hctor', rfl⟩
        · exact old hc0 hold
        · exfalso
          have hF := (addInduct_ctor_retFam hdecl hadd VEnv.LE.rfl htype' hctor').unique hres
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, _⟩ :=
            hW.ordered.projectionShape hold
          rw [← hF, addInduct_type_fresh hadd htype'] at hlookup; cases hlookup
    rcases hd.projections_eq_or_induct with hprojs | ⟨decl, hdecl, hadd⟩
    · rcases hd.pats_eq_or_induct with hpats | ⟨decl, hdecl, hadd⟩
      · have hc0 : IsPatCtor env c := by
          obtain ⟨_, r, recN, M, N, hpp, rfl⟩ := hc
          exact ⟨_, r, recN, M, N, hpats ▸ hpp, rfl⟩
        exact old hc0 (hprojs ▸ hp)
      · exact inductCase decl hdecl hadd
    · exact inductCase decl hdecl hadd

theorem _root_.Lean4Lean.VEnv.WF.structCoh (henv : env.WF) : StructCoh env :=
  let ⟨_, H⟩ := henv; H.structCoh

end Model
end VEnv
end Lean4Lean
