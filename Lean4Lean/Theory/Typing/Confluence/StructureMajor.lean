import Lean4Lean.Theory.Typing.Confluence.Patterns
import Lean4Lean.Theory.Typing.Confluence.FamilyHeadCases
import Lean4Lean.Theory.Typing.PatternCaptures

/-! # Registered ι rules at structure constructors

The two structure fields of the confluence engine's `Params` for the pattern table of a
well-formed environment: the major of an ι rule typed at a registered structure is that
structure's constructor applied to all its parameters and fields
(`ConcretePattern.struct_major`), and an ι rule at a structure constructor reads only its fields
(`ConcretePattern.iota_params`).

Both rest on one fact proved along the history (`WF'.structureCtorCoherent`): a pattern
constructor whose type returns a registered structure is that structure's constructor. A
registered structure is a type former with a single constructor, so the declaration installing a
pattern constructor's family registers exactly that projection entry
(`WF.installed_projection`), whose parameter count is the rule's
(`VInductDecl.WF.rules_ctorParams`). -/

namespace Lean4Lean.VEnv
open InductiveSignature

variable {env : VEnv}

/-! ## Result families -/

/-- The type of the constant `c` returns an application of `F`. -/
def ResultFamily (env : VEnv) (c F : Name) : Prop :=
  ∃ ci ls, env.constants c = some ci ∧ ci.type.forallResult.getAppFnArgs.1 = .const F ls

theorem ResultFamily.unique (H : env.ResultFamily c F) (H' : env.ResultFamily c F') : F = F' := by
  obtain ⟨ci, ls, hc, hh⟩ := H
  obtain ⟨ci', ls', hc', hh'⟩ := H'
  rw [hc] at hc'
  cases hc'
  exact (VExpr.const.inj (hh.symm.trans hh')).1

theorem ResultFamily.of_le {env' : VEnv} {ci : VConstant} (hle : env ≤ env')
    (hc : env.constants c = some ci) (H : env'.ResultFamily c F) : env.ResultFamily c F := by
  obtain ⟨ci', ls, h', hh⟩ := H
  rw [hle.constants hc] at h'
  cases h'
  exact ⟨ci, ls, hc, hh⟩

/-- The result head of a well-formed type is a declared constant. -/
theorem IsType.forallResult_head_declared (henv : env.OrderedStrong) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {type : VExpr} (H : env.IsType U Γ type)
    (hh : type.forallResult.getAppFnArgs.1 = .const F ls) :
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

theorem WF.resultFamily_declared (henv : env.WF) (H : env.ResultFamily c F) :
    ∃ cF, env.constants F = some cF := by
  obtain ⟨ci, ls, hc, hh⟩ := H
  exact IsType.forallResult_head_declared henv.orderedStrong (Γ := []) ⟨⟩
    (henv.ordered.constWF hc) hh

/-- The projection constructor of a registered structure returns that structure. -/
theorem Ordered.projection_resultFamily (henv : env.Ordered) (hp : env.projections family info) :
    env.ResultFamily info.ctorName family := by
  obtain ⟨decl, type, ctor, _, _, hname, _, _, _, _, _, _, hctorType, _, _, _, hraw, _⟩ :=
    henv.projectionShape hp
  obtain ⟨doms, result, heq, _, _, hhead, _⟩ := hraw.forallArity
  refine ⟨_, VLevel.params decl.uvars, henv.projectionConstructor hp, ?_⟩
  change info.ctorType.forallResult.getAppFnArgs.1 = _
  rw [← hctorType, heq, VExpr.forallResult_wrapForalls]
  have hres : result.forallResult = result := by
    cases result <;> first | rfl | cases hhead
  rw [hres, hhead, hname]

/-- A constructor of an installed declaration returns its own type former. -/
theorem addInduct_ctor_resultFamily {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hdecl : decl.WF env₀) (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    {type : VInductiveType} (htype : type ∈ decl.types) {ctor : VConstVal}
    (hctor : ctor ∈ type.ctors) : env.ResultFamily ctor.name type.name := by
  obtain ⟨block, hcomp, -, -⟩ := hdecl.recsCompiled
  obtain ⟨ls, hres⟩ := hcomp.ctor_result type htype ctor hctor
  exact ⟨_, ls, hle.constants (addInduct_ctor_find hadd htype hctor), hres⟩

/-- A projection entry of a declaration: a type former with one constructor. -/
theorem VInductDecl.mem_projectionEntries {decl : VInductDecl} {entry : VProjectionEntry}
    (h : entry ∈ decl.projectionEntries) :
    ∃ type ∈ decl.types, ∃ ctor, type.ctors = [ctor] ∧ entry.typeName = type.name ∧
      entry.info.ctorName = ctor.name ∧ entry.info.nparams = decl.nparams := by
  obtain ⟨type, htype, hentry⟩ := List.mem_filterMap.mp h
  split at hentry
  · rename_i ctor hctors
    cases hentry
    exact ⟨type, htype, ctor, hctors, rfl, rfl, rfl⟩
  · cases hentry

/-! ## Pattern constructors of registered structures -/

/-- A pattern constructor whose type returns a registered structure is that structure's
constructor. -/
def StructureCtorCoherent (env : VEnv) : Prop :=
  ∀ F info, env.projections F info → ∀ c, IsPatCtor env c → env.ResultFamily c F →
    c = info.ctorName

/-- A pattern constructor is a declared constant. -/
theorem WF.patCtor_declared (henv : env.WF) {c : Name} (h : IsPatCtor env c) :
    ∃ ci, env.constants c = some ci := by
  obtain ⟨p, r, recN, M, N, hp, rfl⟩ := h
  obtain ⟨ci, hci, -⟩ := henv.patsIota.ctor_shape hp
  exact ⟨ci, hci⟩

private theorem structureCtorCoherent_projections {base envTypes envCtors : VEnv}
    {decl : VInductDecl} {block : VInductBlock} (hW : base.WF)
    (htypesEq : block.types = decl.typeConstants)
    (hprojs : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctorsAdd : envTypes.addConstVals block.ctors = some envCtors)
    (ihCtors : StructureCtorCoherent envCtors) :
    StructureCtorCoherent (envCtors.addProjections block.projections) := by
  have hle : base ≤ envCtors := (addConstVals_le htypes).trans (addConstVals_le hctorsAdd)
  have hpats : envCtors.pats = base.pats := by
    rw [addConstVals_pats hctorsAdd, addConstVals_pats htypes]
  intro F info hp c hc hres
  have hcBase : IsPatCtor base c := by
    obtain ⟨_, r, recN, M, N, hpp, rfl⟩ := hc
    refine ⟨_, r, recN, M, N, ?_, rfl⟩
    rw [← hpats]; simpa using hpp
  obtain ⟨ci, hci⟩ := hW.patCtor_declared hcBase
  have hresBase : base.ResultFamily c F :=
    ResultFamily.of_le (hle.trans addProjections_le) hci hres
  rcases VEnv.addProjections_iff.mp hp with ⟨entry, hentry, rfl, rfl⟩ | hold
  · exfalso
    rw [hprojs] at hentry
    obtain ⟨type, htype, ctor, -, hname, -, -⟩ := VInductDecl.mem_projectionEntries hentry
    obtain ⟨cF, hcF⟩ := hW.resultFamily_declared hresBase
    have hfresh := addConstVals_names_fresh htypes type.toVConstVal (by
      rw [htypesEq]; exact List.mem_map_of_mem htype)
    rw [hname] at hcF
    change base.constants type.name = none at hfresh
    rw [hfresh] at hcF; cases hcF
  · refine ihCtors F info hold c ?_ (ResultFamily.of_le addProjections_le
      (hle.constants hci) hres)
    obtain ⟨_, r, recN, M, N, hpp, rfl⟩ := hc
    exact ⟨_, r, recN, M, N, by simpa using hpp, rfl⟩

theorem WF'.structureCtorCoherent {ds : List VDecl} (H : env.WF' ds) :
    StructureCtorCoherent env := by
  induction H with
  | empty => intro F info hp; cases hp
  | inductProjections hbase _ _ _ _ _ _ _ htypesEq _ hprojs htypes hctorsAdd _ ihCtors =>
    exact structureCtorCoherent_projections ⟨_, hbase⟩ htypesEq hprojs htypes hctorsAdd ihCtors
  | @decl d env' ds env hd H ih =>
    have hW : env.WF := ⟨ds, H⟩
    have hle := hd.le
    intro F info hp c hc hres
    -- an old pattern constructor with an old projection: the induction hypothesis
    have old : IsPatCtor env c → env.projections F info → c = info.ctorName := by
      intro hc0 hp0
      obtain ⟨ci, hci⟩ := hW.patCtor_declared hc0
      exact ih F info hp0 c hc0 (ResultFamily.of_le hle hci hres)
    have inductCase : ∀ decl : VInductDecl, decl.WF env → env.addInduct decl = some env' →
        c = info.ctorName := by
      intro decl hdecl hadd
      have hcases : IsPatCtor env c ∨ ∃ type ∈ decl.types, ∃ ctor ∈ type.ctors, ctor.name = c := by
        obtain ⟨p, r, recN, M, N, hpp, rfl⟩ := hc
        rcases addInduct_pats_origin hadd hpp with hold | ⟨rec, hrec, ru, hru, e⟩
        · exact .inl ⟨_, r, recN, M, N, hold, rfl⟩
        · obtain ⟨-, -, rfl, -⟩ := SimplePattern.iota_toPattern_inj e
          obtain ⟨block, hcomp, hrecs, -⟩ := hdecl.recsCompiled
          rcases hcomp.rule_ctor_cases hrecs hrec hru with ⟨ctor, hctor, hn⟩ | hpc
          · obtain ⟨type, htype, hctor'⟩ := List.mem_flatMap.1 hctor
            exact .inr ⟨type, htype, ctor, hctor', hn.symm⟩
          · exact .inl hpc
      rcases (addInduct_projections_iff hadd).mp hp with ⟨entry, hentry, rfl, rfl⟩ | hold
      · obtain ⟨type, htype, ctor, hctors, hname, hctorName, -⟩ :=
          VInductDecl.mem_projectionEntries hentry
        rcases hcases with hc0 | ⟨type', htype', ctor', hctor', rfl⟩
        · exfalso
          obtain ⟨ci, hci⟩ := hW.patCtor_declared hc0
          obtain ⟨cF, hcF⟩ := hW.resultFamily_declared (ResultFamily.of_le hle hci hres)
          rw [hname, addInduct_type_fresh hadd htype] at hcF; cases hcF
        · have hF := (addInduct_ctor_resultFamily hdecl hadd VEnv.LE.rfl htype' hctor').unique hres
          rw [hname] at hF
          obtain ⟨envT, -, -, hT, -, -, -⟩ := addInduct_stages hadd
          have hT' := addTypes_nodup hT
          have htt : type' = type :=
            nodup_map_inj_on hT' type' htype' type htype hF
          subst htt
          rw [hctors, List.mem_singleton] at hctor'
          subst hctor'
          exact hctorName.symm
      · rcases hcases with hc0 | ⟨type', htype', ctor', hctor', rfl⟩
        · exact old hc0 hold
        · exfalso
          have hF := (addInduct_ctor_resultFamily hdecl hadd VEnv.LE.rfl htype' hctor').unique hres
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

theorem WF.structureCtorCoherent (henv : env.WF) : StructureCtorCoherent env :=
  let ⟨_, H⟩ := henv; H.structureCtorCoherent

theorem _root_.List.sublist_flatMap_of_mem' {f : α → List β} {l : List α} (h : a ∈ l) :
    List.Sublist (f a) (l.flatMap f) := by
  induction l with
  | nil => cases h
  | cons b t ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

theorem _root_.List.eq_singleton_of_nodup_map' {f : α → β} {l : List α}
    (hnodup : (l.map f).Nodup) (ha : a ∈ l) (hsame : ∀ y ∈ l, f y = f a) : l = [a] := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hx : x = a := by
      rcases List.mem_cons.mp ha with rfl | hxs
      · rfl
      · exact absurd (hsame x (.head _) ▸ List.mem_map_of_mem hxs) hnodup.1
    subst hx
    cases xs with
    | nil => rfl
    | cons y ys =>
      exact absurd ((hsame y (.tail _ (.head _))) ▸ List.mem_map_of_mem (.head _)) hnodup.1

/-- **The projection entry of an installed structure.** A type former of an installed compiled
declaration that is a registered structure has a single constructor, and its projection entry is
the declaration's. -/
theorem WF.installed_projection (henv : env.WF) {base installBase installed : VEnv}
    {decl : VInductDecl} {block : VInductBlock}
    (hcomp : CompiledInductive base decl block) (hrecs : decl.RecsOf block)
    (hadd : installBase.addInduct decl = some installed) (hle : installed ≤ env)
    {type : VInductiveType} (htype : type ∈ decl.types) {ctor : VConstVal}
    (hctor : ctor ∈ type.ctors) {info : VProjectionInfo}
    (hp : env.projections type.name info) :
    type.ctors = [ctor] ∧ info.ctorName = ctor.name ∧ info.nparams = decl.nparams := by
  have hall : ∀ c2 ∈ type.ctors, c2.name = info.ctorName := by
    intro c2 hc2
    have hmem : c2 ∈ decl.constructorConstants := List.mem_flatMap.mpr ⟨type, htype, hc2⟩
    have hpc := hcomp.constructor_isPatCtor hrecs hadd hle hmem
    obtain ⟨ls, hres⟩ := hcomp.ctor_result type htype c2 hc2
    exact henv.structureCtorCoherent type.name info hp c2.name hpc
      ⟨_, ls, hle.constants (addInduct_ctor_find hadd htype hc2), hres⟩
  have hnodup : (type.ctors.map (·.name)).Nodup := by
    obtain ⟨e1, e2, e3, s1, s2, s3, s4⟩ := addInduct_stages hadd
    have h := addCtors_nodup s2
    rw [List.map_flatMap] at h
    exact List.Nodup.sublist (List.sublist_flatMap_of_mem' (f := fun t => t.ctors.map (·.name)) htype) h
  have hsingle : type.ctors = [ctor] := List.eq_singleton_of_nodup_map' hnodup hctor
    (fun y hy => (hall y hy).trans (hall ctor hctor).symm)
  have hentry : (⟨type.name, ⟨decl.uvars, decl.nparams, type.numIndices, type.resultLevel,
      ctor.name, ctor.type⟩⟩ : VProjectionEntry) ∈ decl.projectionEntries :=
    List.mem_filterMap.mpr ⟨type, htype, by rw [hsingle]⟩
  have hp' := hle.projections ((addInduct_projections_iff hadd).mpr (.inl ⟨_, hentry, rfl, rfl⟩))
  have := henv.ordered.projections_unique hp hp'
  subst this
  exact ⟨hsingle, rfl, rfl⟩

/-- A saturated application whose head returns a rigid family and whose own type is an
application of a rigid family supplies the whole telescope, and the two families agree. -/
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
      VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.orderedStrong hΓ with ⟨A, B, hfun, harg⟩
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

theorem _root_.Lean4Lean.VExpr.forallResult_telescope (e : VExpr) :
    ∃ doms, e = VExpr.wrapForalls doms e.forallResult ∧ doms.length = e.forallArity := by
  induction e with
  | forallE d b _ ih =>
    obtain ⟨doms, he, hl⟩ := ih
    exact ⟨d :: doms, by
      change VExpr.forallE d b = VExpr.forallE d (VExpr.wrapForalls doms b.forallResult)
      rw [← he], by simp [VExpr.forallArity, hl]⟩
  | _ => exact ⟨[], rfl, rfl⟩

/-- A saturated application of a constant whose type returns a rigid family, typed at a
registered structure, is an application of that structure's constructor to all its
parameters and fields, provided the constant's result family is coherent with the structure. -/
theorem WF.ctorResult_struct (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {cc : Name} (hrigid : env.CtorResultRigid cc)
    (hcoh : env.ResultFamily cc family → cc = info.ctorName)
    (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps)) :
    cc = info.ctorName ∧ fs.length = info.nparams + info.numFields := by
  obtain ⟨ci, hci, F, lsF, hres, _, hrigidF⟩ := hrigid
  have hhead : VExpr.WF env U Γ (.const cc lsc) := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, hs⟩
  obtain ⟨ci', hci', hlw, hlen⟩ := hhead.const_inv henv.orderedStrong hΓ
  rw [hci] at hci'
  cases hci'
  have hc := HasType.const (Γ := Γ) hci hlw hlen
  obtain ⟨doms, hdoms, hdomsLen⟩ := VExpr.forallResult_telescope ci.type
  have hresEq : ci.type.forallResult =
      VExpr.mkApps (.const F lsF) ci.type.forallResult.getAppFnArgs.2 := by
    have h := VExpr.rebuild_spine ci.type.forallResult
    rw [hres] at h
    exact h.symm
  rw [hdoms, hresEq, VExpr.instL_wrapForalls, VExpr.instL_mkApps] at hc
  obtain ⟨hfs, hFfam⟩ := HasType.mkApps_rigid_family henv hΓ hrigidF (henv.projectionRigid hl) hc hs
  subst hFfam
  have hcc := hcoh ⟨ci, lsF, hci, hres⟩
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

/-- A registered quotient is not a registered structure, and its constructor returns `Quot`. -/
theorem QuotRegistered.not_struct (henv : env.WF) (hq : QuotRegistered env)
    (hl : env.projections family info) (hcc : ``Quot.mk = info.ctorName) : False := by
  have hrf := henv.ordered.projection_resultFamily hl
  rw [← hcc] at hrf
  have hF := hrf.unique (⟨_, [.param 0], hq.constructor, rfl⟩ : env.ResultFamily ``Quot.mk ``Quot)
  subst hF
  exact (henv.quot_not_projection hq.equation).1 info hl

/-- **A recursor or quotient iota major of structure type is a saturated application of the
structure's constructor.** -/
theorem ConcretePattern.struct_major (henv : env.WF)
    (H : ConcretePattern env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hΓ : OnCtx Γ (env.IsType U)) (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps))
    (hlen : fs.length = kc) : cc = info.ctorName ∧ kc = info.nparams + info.numFields := by
  have key : ∀ {P r}, ConcretePattern env P r →
      P = (SimplePattern.iota rc mr cc kc).toPattern →
      cc = info.ctorName ∧ kc = info.nparams + info.numFields := by
    intro P r H hP
    rcases H with H | H | H
    · cases H; cases hP
    · cases H with
      | intro hq =>
        obtain ⟨-, -, rfl, -⟩ := SimplePattern.iota_toPattern_inj hP.symm
        have hrigid : env.CtorResultRigid ``Quot.mk :=
          ⟨_, hq.constructor, ``Quot, [.param 0], rfl, ⟨_, hq.quotient⟩,
            henv.quot_rigid hq.equation⟩
        have hcoh : env.ResultFamily ``Quot.mk family → ``Quot.mk = info.ctorName := fun h => by
          have hF := h.unique (⟨_, [.param 0], hq.constructor, rfl⟩ :
            env.ResultFamily ``Quot.mk ``Quot)
          subst hF
          exact ((henv.quot_not_projection hq.equation).1 info hl).elim
        obtain ⟨hcc, -⟩ := henv.ctorResult_struct hΓ hrigid hcoh hl hs
        exact (QuotRegistered.not_struct henv hq hl hcc).elim
    · subst hP
      have hpc : IsPatCtor env cc := ⟨_, _, rc, mr, kc, H.pats, rfl⟩
      obtain ⟨hcc, hfs⟩ := henv.ctorResult_struct hΓ (henv.patCtor_resultRigid hpc)
        (henv.structureCtorCoherent family info hl cc hpc) hl hs
      exact ⟨hcc, hlen ▸ hfs⟩
  exact key H rfl

theorem GuardedIotaPattern.check_eq {p : Pattern} {r : p.RHS × p.Check}
    (H : GuardedIotaPattern env p r) : ∃ data : RecursorData, r.2 = data.guard p := by
  cases H with | intro _ _ => exact ⟨_, rfl⟩

/-- **The parameter count of a registered ι rule at a structure constructor is the
structure's.** The rule's constructor is a constructor of the declaration or of a certified
container (`VInductDecl.WF.rules_ctorParams`), whose projection entry for the structure is the
registered one (`WF.installed_projection`). -/
theorem WF.pat_struct_params (henv : env.WF) {p : Pattern} {r : p.RHS × p.Check}
    (hp : env.pats p r) (hl : env.projections family info) :
    ∃ (rec : VRecursor) (ru : VRecRule) (hc : ru.rhs.Closed)
      (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
        (ru.ctorParams + ru.nfields)).toPattern),
      e ▸ r = (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
        rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) ∧
      (ru.ctor = info.ctorName → ru.ctorParams = info.nparams) := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨decl, ds₀, env₀, env₁, -, -, hdecl, hadd, hle, rec, hrec, ru, hru, hc, e, hr⟩ :=
    H.pats_origin hp
  have henv : env.WF := ⟨ds, H⟩
  refine ⟨rec, ru, hc, e, hr, fun hcc => ?_⟩
  have hfam : ∀ {c T : Name}, env.ResultFamily c T → c = info.ctorName → T = family :=
    fun h hn => h.unique (hn ▸ henv.ordered.projection_resultFamily hl)
  obtain ⟨block, hcomp, hrecs, -⟩ := hdecl.recsCompiled
  rcases hdecl.rules_ctorParams rec hrec ru hru with
    ⟨c, hcm, hcn, hcp⟩ | ⟨D, hD, c, hcm, hcn, hcp⟩
  · obtain ⟨type, htype, hctor⟩ := List.mem_flatMap.1 hcm
    have hT := hfam (addInduct_ctor_resultFamily hdecl hadd hle htype hctor) (hcn ▸ hcc)
    subst hT
    obtain ⟨-, -, hnp⟩ := henv.installed_projection hcomp hrecs hadd hle htype hctor hl
    rw [hcp, hnp]
  · cases hD with
    | intro _ _ hcomp' _ hrecs' hadd' hle' =>
      obtain ⟨type, htype, hctor⟩ := List.mem_flatMap.1 hcm
      have hle'' := hle'.trans ((addInduct_le hadd).trans hle)
      obtain ⟨ls, hres⟩ := hcomp'.ctor_result type htype c hctor
      have hT := hfam ⟨_, ls, hle''.constants (addInduct_ctor_find hadd' htype hctor), hres⟩
        (hcn ▸ hcc)
      subst hT
      obtain ⟨-, -, hnp⟩ := henv.installed_projection hcomp' hrecs' hadd' hle'' htype hctor hl
      rw [hcp, hnp]

/-- **An ι rule at a structure constructor reads only its fields**, not its parameters, and its
universe guard reads only the levels. -/
theorem ConcretePattern.iota_params (henv : env.WF)
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (H : ConcretePattern env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
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
  rcases H with H | H | H
  · cases H
  · obtain ⟨hq, -, -, hccq, -⟩ := QuotPattern.registered (recursor := rc) (major := mr)
      (ctor := cc) (fields := kc) H
    exact (QuotRegistered.not_struct henv hq hl (hccq ▸ hcc)).elim
  · obtain ⟨rhs, ck⟩ := r
    obtain ⟨data, rfl⟩ := H.check_eq
    have hpats := H.pats
    refine ⟨fun m1 g1 => ?_, fun m1 g1 df h => ?_⟩
    · obtain ⟨rec, ru, hc, e, hr, hcp⟩ := henv.pat_struct_params hpats hl
      obtain ⟨rfl, rfl, rfl, rfl⟩ := SimplePattern.iota_toPattern_inj e
      cases e
      have hr1 := congrArg Prod.fst hr
      simp only at hr1
      subst hr1
      have hcp := hcp hcc
      have hlen : (ps ++ fields).length = ru.ctorParams + ru.nfields := by
        obtain ⟨-, -, h⟩ := VExpr.mkApps_const_inj hm.const_arguments
        rw [h]; simp [Pattern.argumentRHS_length]
      have hlen' : (ps' ++ fields).length = ru.ctorParams + ru.nfields := by
        obtain ⟨-, -, h⟩ := VExpr.mkApps_const_inj hm'.const_arguments
        rw [h]; simp [Pattern.argumentRHS_length]
      obtain ⟨g0, hm0, hg0⟩ := Pattern.matches_varN_const (c := ru.ctor) (ls := lsc) _ _ hlen
      obtain ⟨g0', hm0', hg0'⟩ := Pattern.matches_varN_const (c := ru.ctor) (ls := lsc') _ _ hlen'
      obtain ⟨-, rfl⟩ := hm.uniq hm0
      obtain ⟨-, rfl⟩ := hm'.uniq hm0'
      let k := rec.numParams + rec.numMotives + rec.numMinors
      let recArgs := (List.finRange (k + rec.numIndices)).map fun i =>
        g1 (Pattern.varN_pathOf (k + rec.numIndices) i.1 i.2)
      have hrl : recArgs.length = k + rec.numIndices := by simp [recArgs]
      have hg1 : ∀ i (hi : i < k + rec.numIndices),
          g1 (Pattern.varN_pathOf (k + rec.numIndices) i hi) = recArgs[i]'(hrl ▸ hi) := by
        intro i hi; simp [recArgs]
      have a1 := SimplePattern.iotaRHS'_apply rec.name ru.ctor k rec.numIndices ru.ctorParams
        ru.nfields ru.rhs hc m1 (Sum.elim g1 g) hrl hlen hg1 hg0
      have a2 := SimplePattern.iotaRHS'_apply rec.name ru.ctor k rec.numIndices ru.ctorParams
        ru.nfields ru.rhs hc m1 (Sum.elim g1 g') hrl hlen' hg1 hg0'
      refine a1.trans (Eq.trans ?_ a2.symm)
      rw [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
        List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    · revert h
      unfold RecursorData.guard
      split <;> simp [Pattern.Check.OK]

end Lean4Lean.VEnv
