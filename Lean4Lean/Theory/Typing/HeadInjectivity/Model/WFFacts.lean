import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound
import Lean4Lean.Theory.Inductive.CompilationMajors

/-! # Facts about well-formed environments used by the history induction

The static facts about a well-formed environment that `Model/EnvValid.lean` feeds to the
rule and projection cases of soundness: the classification of its definitional axioms (delta
rules of definitions and the quotient rule, `WF'.defeqs_cases`), the quotient constants
(`Quot`, `Quot.mk` rigid and never projection-registered, `WF.quot_not_projection`), the
projection families (never constructors, `WF.projStatic`) and the rigidity of constructors
(`WF.isCtor_rigid`). All are proved along the declaration history; the rigidity of the
constructor of a registered ι pattern (`WF.patCtor_rigid`) reads the constructor off the
compilation of its block (`VInductDecl.RecsCompiled`, `CompiledInductive.rule_ctor_cases`). -/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv}

/-! ## Definitional axioms -/

/-- Every definitional axiom of a well-formed environment is the delta rule of a definition
(a bare constant on the left) or the quotient rule. -/
theorem WF'.defeqs_cases {ds : List VDecl} (H : env.WF' ds) {df : VDefEq} (hdf : env.defeqs df) :
    (∃ n ls, df.lhs = .const n ls) ∨ df = quotDefEq := by
  induction H with
  | empty => cases hdf
  | decl hd _ ih =>
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 => rw [addConst_defeqs h2] at hdf; exact ih hdf
    | «example» _ => exact ih hdf
    | «def» _ h2 =>
      rcases hdf with rfl | hdf
      · exact .inl ⟨_, _, rfl⟩
      · rw [addConst_defeqs h2] at hdf; exact ih hdf
    | mutualDef _ h2 _ =>
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hdf
      rcases hdf with hm | hdf
      · obtain ⟨ci, -, rfl⟩ := List.mem_map.1 hm
        exact .inl ⟨_, _, rfl⟩
      · rw [addConsts_defeqs h2] at hdf; exact ih hdf
    | quot h1 h2 =>
      obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
      rcases hdf with rfl | hdf
      · exact .inr rfl
      · rw [addConst_defeqs a4, addConst_defeqs a3, addConst_defeqs a2, addConst_defeqs a1] at hdf
        exact ih hdf
    | induct _ h2 => rw [addInduct_defeqs h2] at hdf; exact ih hdf
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih (by simpa using hdf)

/-- The constructor major of a λ-wrapped definitional axiom is unique. -/
theorem _root_.Lean4Lean.VDefEq.HasConstructorMajor.unique {df : VDefEq} {a b : Name}
    (ha : df.HasConstructorMajor a) (hb : df.HasConstructorMajor b) : a = b := by
  obtain ⟨fa, la, aa, ea⟩ := ha
  obtain ⟨fb, lb, ab, eb⟩ := hb
  have he := (VExpr.app.inj (ea.symm.trans eb)).2
  have := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
  simp only [VExpr.getAppFnArgs_mkApps_const] at this
  exact (VExpr.const.inj this).1

/-- A constructor major of a definitional axiom of a well-formed environment is `Quot.mk`,
and the axiom is the quotient rule. -/
theorem WF.installedCtor_eq (henv : env.WF) {c : Name} (h : Model.IsInstalledCtor env c) :
    c = ``Quot.mk ∧ env.defeqs quotDefEq := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨df, hdf, hm⟩ := h
  rcases H.defeqs_cases hdf with ⟨n, ls, hl⟩ | rfl
  · obtain ⟨fn, levels, args, e⟩ := hm
    rw [hl] at e; cases e
  · exact ⟨hm.unique Model.quotDefEq_ctorMajor, hdf⟩

/-! ## The quotient constants -/

/-- Once the quotient rule is installed: the quotient constants are declared, `Quot` and
`Quot.mk` are rigid, and no projection entry names them. -/
private def QuotFacts (env : VEnv) : Prop :=
  env.defeqs quotDefEq →
    env.constants ``Quot = some quotConst ∧ env.constants ``Quot.mk = some quotMkConst ∧
    env.constants ``Quot.lift = some quotLiftConst ∧
    env.Rigid ``Quot ∧ env.Rigid ``Quot.mk ∧
    ∀ S info, env.projections S info →
      S ≠ ``Quot ∧ S ≠ ``Quot.mk ∧ info.ctorName ≠ ``Quot ∧ info.ctorName ≠ ``Quot.mk

private theorem quotDefEq_ne_toDefEq (v : VDefVal) : quotDefEq ≠ v.toDefEq := by
  intro h
  have := congrArg VDefEq.lhs h
  simp [VDefVal.toDefEq] at this
  cases this

private theorem ne_of_some_none {n m : Name} {ci : VConstant}
    (h1 : env.constants n = some ci) (h2 : env.constants m = none) : n ≠ m := by
  rintro rfl; rw [h1] at h2; cases h2

private theorem WF'.quotFacts {ds : List VDecl} (H : env.WF' ds) : QuotFacts env := by
  induction H with
  | empty => intro h; cases h
  | @decl d env' ds env0 hd hW ih =>
    intro hq
    have hWF : env0.WF := ⟨ds, hW⟩
    by_cases hq0 : env0.defeqs quotDefEq
    · obtain ⟨c1, c2, c3, r1, r2, hp⟩ := ih hq0
      refine ⟨hd.le.constants c1, hd.le.constants c2, hd.le.constants c3, r1.step c1 hd,
        r2.step c2 hd, fun S info hS => ?_⟩
      rcases hd.projections_eq_or_induct with heq | ⟨decl, -, hadd⟩
      · rw [heq] at hS; exact hp S info hS
      · rcases (addInduct_projections_iff hadd).1 hS with ⟨entry, hentry, rfl, rfl⟩ | hold
        · obtain ⟨type, htype, ctor, hctors, rfl⟩ := VInductDecl.projectionEntries_origin hentry
          have hT := addInduct_type_fresh hadd htype
          have hC := addInduct_ctor_fresh hadd htype (by rw [hctors]; exact List.mem_singleton_self _)
          exact ⟨(ne_of_some_none c1 hT).symm, (ne_of_some_none c2 hT).symm,
            (ne_of_some_none c1 hC).symm, (ne_of_some_none c2 hC).symm⟩
        · exact hp S info hold
    · -- the step installed the quotient rule, so it is the `quot` step
      cases hd with
      | «axiom» _ h2 | «opaque» _ h2 => rw [addConst_defeqs h2] at hq; exact absurd hq hq0
      | «example» _ => exact absurd hq hq0
      | «def» _ h2 =>
        rcases hq with h | hq
        · exact absurd h (quotDefEq_ne_toDefEq _)
        · rw [addConst_defeqs h2] at hq; exact absurd hq hq0
      | mutualDef _ h2 _ =>
        rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hq
        rcases hq with hm | hq
        · obtain ⟨ci, -, h⟩ := List.mem_map.1 hm
          exact absurd h.symm (quotDefEq_ne_toDefEq _)
        · rw [addConsts_defeqs h2] at hq; exact absurd hq hq0
      | induct _ h2 => rw [addInduct_defeqs h2] at hq; exact absurd hq hq0
      | quot h1 h2 =>
        obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
        have hQ0 : env0.constants ``Quot = none := addConst_fresh a1
        have hM0 : env0.constants ``Quot.mk = none :=
          (addConst_le a1).constants_eq_none_left (addConst_fresh a2)
        have hdefeqs : ∀ df, (e4.addDefEq quotDefEq).defeqs df → df = quotDefEq ∨ env0.defeqs df :=
          fun df h => by
            rwa [defeqs_addDefEq, List.mem_singleton, addConst_defeqs a4, addConst_defeqs a3,
              addConst_defeqs a2, addConst_defeqs a1] at h
        have hpats : (e4.addDefEq quotDefEq).pats = env0.pats := by
          rw [addDefEq_pats, addConst_pats a4, addConst_pats a3, addConst_pats a2, addConst_pats a1]
        have hprojs : (e4.addDefEq quotDefEq).projections = env0.projections := by
          rw [addDefEq_projections, addConst_projections a4, addConst_projections a3,
            addConst_projections a2, addConst_projections a1]
        have hhead : quotDefEq.lhs.stripLams.getAppFnArgs.1 =
            .const ``Quot.lift [.param 0, .param 1] := rfl
        have rigid : ∀ n, env0.constants n = none → n ≠ ``Quot.lift →
            (e4.addDefEq quotDefEq).Rigid n := fun n hn hne => by
          refine ⟨fun df hdf ls h => ?_, fun p r hp => ?_⟩
          · rcases hdefeqs df hdf with rfl | hdf
            · rw [hhead] at h; exact hne (VExpr.const.inj h).1.symm
            · exact (hWF.rigid_of_absent hn).defeqs df hdf ls h
          · rw [hpats] at hp; exact (hWF.rigid_of_absent hn).pats p r hp
        refine ⟨addDefEq_le.constants ((addConst_le a4).constants ((addConst_le a3).constants
            ((addConst_le a2).constants (addConst_self a1)))),
          addDefEq_le.constants ((addConst_le a4).constants ((addConst_le a3).constants
            (addConst_self a2))),
          addDefEq_le.constants ((addConst_le a4).constants (addConst_self a3)),
          rigid _ hQ0 (by decide), rigid _ hM0 (by decide), fun S info hS => ?_⟩
        rw [hprojs] at hS
        obtain ⟨cS, hcS⟩ := hWF.ordered.projectionConstant hS
        have hcC := hWF.ordered.projectionConstructor hS
        exact ⟨ne_of_some_none hcS hQ0, ne_of_some_none hcS hM0, ne_of_some_none hcC hQ0,
          ne_of_some_none hcC hM0⟩
  | @inductProjections _ ds base envTypes envCtors decl block hbase hctorsW hsource htypesWF
      hconstructorUvars hctorsWF' hspw hshape htypesSource hctorsSource hprojections htypes
      hctors ihBase ihCtors =>
    intro hq
    have hqC : envCtors.defeqs quotDefEq := by simpa using hq
    have hqB : base.defeqs quotDefEq := by
      rwa [addConstVals_defeqs hctors, addConstVals_defeqs htypes] at hqC
    obtain ⟨c1, c2, c3, r1, r2, hp⟩ := ihCtors hqC
    obtain ⟨b1, b2, -, -, -, -⟩ := ihBase hqB
    refine ⟨by simpa using c1, by simpa using c2, by simpa using c3, r1.addProjections,
      r2.addProjections, fun S info hS => ?_⟩
    rw [addProjections_iff] at hS
    rcases hS with ⟨entry, hentry, rfl, rfl⟩ | hold
    · rw [hprojections] at hentry
      obtain ⟨type, htype, ctor, hctors', rfl⟩ := VInductDecl.projectionEntries_origin hentry
      have htypes' := htypes; rw [htypesSource] at htypes'
      have hctorsC := hctors; rw [hctorsSource] at hctorsC
      have hT : base.constants type.name = none :=
        addConstVals_names_fresh htypes' type.toVConstVal (List.mem_map_of_mem htype)
      have hC : base.constants ctor.name = none :=
        (addConstVals_le htypes).constants_eq_none_left
          (addConstVals_names_fresh hctorsC ctor
            (List.mem_flatMap.2 ⟨type, htype, by rw [hctors']; exact List.mem_singleton_self _⟩))
      exact ⟨(ne_of_some_none b1 hT).symm, (ne_of_some_none b2 hT).symm,
        (ne_of_some_none b1 hC).symm, (ne_of_some_none b2 hC).symm⟩
    · exact hp S info hold

/-- The quotient constants of a well-formed environment containing the quotient rule. -/
theorem WF.quotConsts (henv : env.WF) (hq : env.defeqs quotDefEq) : Model.QuotConsts env := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨c1, c2, c3, -, -, -⟩ := H.quotFacts hq
  exact ⟨c1, c2, c3⟩

/-- `Quot` is rigid in a well-formed environment containing the quotient rule. -/
theorem WF.quot_rigid (henv : env.WF) (hq : env.defeqs quotDefEq) : env.Rigid ``Quot := by
  obtain ⟨ds, H⟩ := henv; exact (H.quotFacts hq).2.2.2.1

/-- `Quot.mk` is rigid in a well-formed environment containing the quotient rule. -/
theorem WF.quotMk_rigid (henv : env.WF) (hq : env.defeqs quotDefEq) : env.Rigid ``Quot.mk := by
  obtain ⟨ds, H⟩ := henv; exact (H.quotFacts hq).2.2.2.2.1

/-- **The quotient is not projection-registered.** -/
theorem WF.quot_not_projection (henv : env.WF) (hq : env.defeqs quotDefEq) :
    (∀ info, ¬ env.projections ``Quot info) ∧ ¬ Model.IsProjCtor env ``Quot.mk := by
  obtain ⟨ds, H⟩ := henv
  have h := (H.quotFacts hq).2.2.2.2.2
  exact ⟨fun info hp => (h _ info hp).1 rfl, fun ⟨S, info, hp, hn⟩ => (h S info hp).2.2.2 hn⟩

/-! ## Projection families -/

/-- A type former of a declaration is not one of its constructors. -/
theorem _root_.Lean4Lean.VInductDecl.typeName_ne_ctorName {decl : VInductDecl}
    (H : decl.sourceNames.Nodup) {type type' : VInductiveType} {ctor : VConstVal}
    (ht : type ∈ decl.types) (ht' : type' ∈ decl.types) (hc : ctor ∈ type'.ctors) :
    type.name ≠ ctor.name := by
  intro e
  have hd := (List.nodup_append.1 H).2.2
  exact hd type.name (List.mem_map.2 ⟨type.toVConstVal, List.mem_map_of_mem ht, rfl⟩)
    ctor.name (List.mem_map.2 ⟨ctor, List.mem_flatMap.2 ⟨type', ht', hc⟩, rfl⟩) e

/-- A registered structure is never the constructor of a registered structure. -/
private def ProjNames (env : VEnv) : Prop :=
  ∀ S info, env.projections S info → ∀ S' info', env.projections S' info' → S ≠ info'.ctorName

private theorem WF'.projNames {ds : List VDecl} (H : env.WF' ds) : ProjNames env := by
  induction H with
  | empty => intro _ _ h; cases h
  | @decl d env' ds env0 hd hW ih =>
    have hWF : env0.WF := ⟨ds, hW⟩
    intro S info hS S' info' hS'
    rcases hd.projections_eq_or_induct with heq | ⟨decl, hdecl, hadd⟩
    · rw [heq] at hS hS'; exact ih S info hS S' info' hS'
    · have hnd : decl.sourceNames.Nodup := hdecl.source.2.1
      rcases (addInduct_projections_iff hadd).1 hS with ⟨e, he, rfl, rfl⟩ | hold <;>
        rcases (addInduct_projections_iff hadd).1 hS' with ⟨e', he', rfl, rfl⟩ | hold'
      · obtain ⟨t, ht, c, hc, rfl⟩ := VInductDecl.projectionEntries_origin he
        obtain ⟨t', ht', c', hc', rfl⟩ := VInductDecl.projectionEntries_origin he'
        exact VInductDecl.typeName_ne_ctorName hnd ht ht' (by rw [hc']; exact List.mem_singleton_self _)
      · obtain ⟨t, ht, c, hc, rfl⟩ := VInductDecl.projectionEntries_origin he
        exact (ne_of_some_none (hWF.ordered.projectionConstructor hold') (addInduct_type_fresh hadd ht)).symm
      · obtain ⟨t', ht', c', hc', rfl⟩ := VInductDecl.projectionEntries_origin he'
        obtain ⟨cS, hcS⟩ := hWF.ordered.projectionConstant hold
        exact ne_of_some_none hcS
          (addInduct_ctor_fresh hadd ht' (by rw [hc']; exact List.mem_singleton_self _))
      · exact ih S info hold S' info' hold'
  | @inductProjections _ ds base envTypes envCtors decl block hbase hctorsW hsource htypesWF
      hconstructorUvars hctorsWF' hspw hshape htypesSource hctorsSource hprojections htypes
      hctors ihBase ihCtors =>
    have hbW : base.WF := ⟨_, hbase⟩
    have htypes' := htypes; rw [htypesSource] at htypes'
    have hctorsC := hctors; rw [hctorsSource] at hctorsC
    have freshT : ∀ t ∈ decl.types, base.constants t.name = none := fun t ht =>
      addConstVals_names_fresh htypes' t.toVConstVal (List.mem_map_of_mem ht)
    have freshC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, base.constants c.name = none := fun t ht c hc =>
      (addConstVals_le htypes).constants_eq_none_left
        (addConstVals_names_fresh hctorsC c (List.mem_flatMap.2 ⟨t, ht, hc⟩))
    have hprB : ∀ S info, envCtors.projections S info ↔ base.projections S info := fun S info => by
      rw [addConstVals_projections hctors, addConstVals_projections htypes]
    intro S info hS S' info' hS'
    rw [addProjections_iff, hprojections] at hS hS'
    rcases hS with ⟨e, he, rfl, rfl⟩ | hold <;> rcases hS' with ⟨e', he', rfl, rfl⟩ | hold'
    · obtain ⟨t, ht, c, hc, rfl⟩ := VInductDecl.projectionEntries_origin he
      obtain ⟨t', ht', c', hc', rfl⟩ := VInductDecl.projectionEntries_origin he'
      exact VInductDecl.typeName_ne_ctorName hsource ht ht' (by rw [hc']; exact List.mem_singleton_self _)
    · obtain ⟨t, ht, c, hc, rfl⟩ := VInductDecl.projectionEntries_origin he
      exact (ne_of_some_none (hbW.ordered.projectionConstructor ((hprB _ _).1 hold'))
        (freshT t ht)).symm
    · obtain ⟨t', ht', c', hc', rfl⟩ := VInductDecl.projectionEntries_origin he'
      obtain ⟨cS, hcS⟩ := hbW.ordered.projectionConstant ((hprB _ _).1 hold)
      exact ne_of_some_none hcS (freshC t' ht' c' (by rw [hc']; exact List.mem_singleton_self _))
    · exact ihCtors S info hold S' info' hold'

/-- **The constructor of a registered structure is rigid.** -/
theorem WF.projCtor_rigid (henv : env.WF) {c : Name} (h : Model.IsProjCtor env c) :
    env.Rigid c := by
  obtain ⟨fam, info, hp, rfl⟩ := h
  exact henv.projectionCtorRigid hp

/-- **Static facts of a projection entry** (`Model.ProjStatic`) of a well-formed environment. -/
theorem WF.projStatic (henv : env.WF) {S : Name} {info : VProjectionInfo}
    (hp : env.projections S info) : Model.ProjStatic env S info where
  famRigid := henv.projectionRigid hp
  ctorRigid := henv.projectionCtorRigid hp
  famNotInstalledCtor h := by
    obtain ⟨rfl, hq⟩ := henv.installedCtor_eq h
    obtain ⟨ds, H⟩ := henv
    exact ((H.quotFacts hq).2.2.2.2.2 _ _ hp).2.1 rfl
  famNotProjCtor := fun ⟨fam, info', hp', hn⟩ => by
    obtain ⟨ds, H⟩ := henv; exact H.projNames S info hp fam info' hp' hn.symm
  ctorClosed := henv.ordered.closedC (henv.ordered.projectionConstructor hp)

/-! ## Constructors -/

/-- Along the history: the constructor of a registered ι pattern is rigid. A pattern of a step
is an old pattern (its constructor is a declared constant, rigid by the induction hypothesis and
`Rigid.step`) or a rule of the step's block, whose constructor is a constructor of the block
(`WF'.inductCtorRigid`) or the constructor of a pattern already registered in the environment
the block was compiled in (`CompiledInductive.rule_ctor_cases`; the induction hypothesis
again). -/
private theorem WF'.patCtor_rigid_aux {ds : List VDecl} (H : env.WF' ds) :
    ∀ c, IsPatCtor env c → env.Rigid c := by
  induction H with
  | empty => rintro c ⟨p, r, _, _, _, hp, _⟩; exact (hp : False).elim
  | @decl d env' ds env0 hd H ih =>
    intro c hc
    have hW : env0.WF := ⟨ds, H⟩
    have step : IsPatCtor env0 c → env'.Rigid c := fun h0 => by
      obtain ⟨p, r, recN, M, N, hp, rfl⟩ := h0
      obtain ⟨ci, hci, -⟩ := hW.patsIota.ctor_shape hp
      exact (ih _ ⟨_, r, recN, M, N, hp, rfl⟩).step hci hd
    obtain ⟨p, r, recN, M, N, hp, rfl⟩ := hc
    rcases hd.pats_eq_or_induct' with heq | ⟨decl, rfl, hdecl, hadd⟩
    · exact step ⟨_, r, recN, M, N, heq ▸ hp, rfl⟩
    · rcases addInduct_pats_origin hadd hp with hold | ⟨rec, hrec, ru, hru, e⟩
      · exact step ⟨_, r, recN, M, N, hold, rfl⟩
      · obtain ⟨-, -, rfl, -⟩ := iota_toPattern_inj e
        obtain ⟨block, hcomp, hrecsOf, -⟩ := hdecl.recsCompiled
        rcases hcomp.rule_ctor_cases hrecsOf hrec hru with ⟨ctor, hctor, hc'⟩ | hpc
        · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hctor
          rw [hc']
          exact (VEnv.WF'.decl hd H).inductCtorRigid (List.mem_cons_self ..) ht hc
        · exact step hpc
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    rintro c ⟨p, r, recN, M, N, hp, rfl⟩
    exact (ihCtors _ ⟨_, r, recN, M, N, by simpa using hp, rfl⟩).addProjections

/-- **The constructor of a registered ι pattern is rigid**: it is a constructor of the block that
registered the pattern or of a container block declared earlier (the auxiliary recursors of a
nested block fire on the container's constructors, `CompiledInductive.rule_ctor_cases`), and
constructors of a well-formed history are rigid (`VEnv.WF'.inductCtorRigid`). -/
theorem WF.patCtor_rigid (henv : env.WF) {c : Name} (h : IsPatCtor env c) :
    env.Rigid c :=
  let ⟨_, H⟩ := henv; H.patCtor_rigid_aux c h

/-- **Constructors are rigid**: the constructor major of a definitional axiom (`Quot.mk`) and
the constructor of a registered ι pattern. -/
theorem WF.isCtor_rigid (henv : env.WF) {c : Name} (h : Model.IsCtor env c) : env.Rigid c := by
  rcases h with h | h
  · obtain ⟨rfl, hq⟩ := henv.installedCtor_eq h
    exact henv.quotMk_rigid hq
  · exact henv.patCtor_rigid h

/-- The constructor major of a definitional axiom (`Quot.mk`) returns an application of a rigid
constant (`Quot`). -/
theorem WF.installedCtor_resultRigid (henv : env.WF) {c : Name}
    (h : Model.IsInstalledCtor env c) : env.CtorResultRigid c := by
  obtain ⟨rfl, hq⟩ := henv.installedCtor_eq h
  obtain ⟨ds, H⟩ := henv
  obtain ⟨c1, c2, -, r1, -, -⟩ := H.quotFacts hq
  exact ⟨quotMkConst, c2, ``Quot, [.param 0], rfl, ⟨_, c1⟩, r1⟩

end VEnv
end Lean4Lean
