import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.WFFacts
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.PatSound

/-! # Environment validity along the declaration history

`VEnv.WF'.envValid` (history induction, section 4.1 of the design notes): every environment in
the declaration history of a well-formed environment `envF` is valid in the model of `envF`
(`Model.EnvValid`): its definitional axioms, its projection entries and its registered ι
patterns. The proof is by induction on the history. A delta rule is valid by `DeltaRules`
(`RuleValid.delta`); the quotient rule by `RuleValid.quot`, whose uniqueness hypotheses come
from `HeadsClosed` and `PatsClosed`: along the history, no later declaration adds a
definitional axiom or a pattern headed by an existing constant, so the rules headed by
`Quot.lift` are exactly the quotient rule. A projection entry is valid from the header
environment of its declaration (`ProjDeclAt.ofEntry`, `ProjValid.of_origin`), which is valid
by the induction hypothesis. A registered ι pattern is valid by `Model.PatValid.iota`.

`VEnv.WF.soundEnv`: soundness of the model for every well-formed environment, the hypothesis
of the extraction (`Model/Extract.lean`) and of separation (`Model/Separation.lean`). -/

namespace Lean4Lean
namespace VEnv

/-! ## Rules along the history -/

/-- The definitional axioms of `envF` whose head constant is a constant of `env` are axioms of
`env`: no later declaration adds an axiom headed by an existing constant. -/
def HeadsClosed (envF env : VEnv) : Prop :=
  ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
    (∃ ci, env.constants n = some ci) → env.defeqs df

/-- The patterns of `envF` whose head constant is a constant of `env` are patterns of `env`: no
later declaration registers a pattern headed by an existing constant. -/
def PatsClosed (envF env : VEnv) : Prop :=
  ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r →
    (∃ ci, env.constants p.headConst = some ci) → env.pats p r

/-- Every definitional axiom of `env` headed by `n` belongs to `rs`. -/
def HeadExcl (env : VEnv) (n : Name) (rs : List VDefEq) : Prop :=
  ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' ∈ rs

theorem HeadsClosed.down {envF env0 env' : VEnv} {new : List VDefEq} (H : HeadsClosed envF env')
    (hle : env0 ≤ env') (hdefeqs : ∀ df, env'.defeqs df → df ∈ new ∨ env0.defeqs df)
    (hfresh : ∀ df ∈ new, ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      env0.constants n = none) : HeadsClosed envF env0 := by
  intro df hdf n ls h ⟨ci, hci⟩
  rcases hdefeqs df (H df hdf n ls h ⟨ci, hle.constants hci⟩) with hm | ho
  · rw [hfresh df hm n ls h] at hci; cases hci
  · exact ho

theorem HeadsClosed.excl {envF env0 env' : VEnv} {new : List VDefEq} {n : Name}
    (H : HeadsClosed envF env') (hord0 : env0.OrderedStrong)
    (hdefeqs : ∀ df, env'.defeqs df → df ∈ new ∨ env0.defeqs df)
    (hn : ∃ ci, env'.constants n = some ci) (hfresh : env0.constants n = none) :
    HeadExcl envF n new := fun df' hdf' ls' h' => by
  rcases hdefeqs df' (H df' hdf' n ls' h' hn) with hm | ho
  · exact hm
  · obtain ⟨_, hc⟩ := (hord0.ordered.defEqWF ho).1.head_const_lookup hord0 (Γ := []) ⟨⟩ h'
    rw [hfresh] at hc; cases hc

theorem HeadsClosed.of_decl {envF env0 env' : VEnv} {d : VDecl} (hdecl : VDecl.WF env0 d env')
    (hcl : HeadsClosed envF env') : HeadsClosed envF env0 := by
  have h0le := hdecl.le
  cases hdecl with
  | «axiom» _ hadd | «opaque» _ hadd =>
    exact hcl.down (new := []) h0le
      (fun df h => .inr (by rwa [addConst_defeqs hadd] at h)) nofun
  | «example» => exact hcl
  | @«def» env₁ _ ci _ hadd =>
    have hnone : env0.constants ci.name = none := addConst_fresh hadd
    exact hcl.down (new := [ci.toDefEq]) h0le
      (fun df h => by rwa [defeqs_addDefEq, addConst_defeqs hadd] at h)
      (fun df hm n ls h => by
        simp only [List.mem_singleton] at hm; subst hm; cases h; exact hnone)
  | mutualDef _ hadd _ =>
    rw [addConsts_eq_addConstVals] at hadd
    exact hcl.down (new := _) h0le
      (fun df h => by
        rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or,
          addConstVals_defeqs hadd] at h; exact h)
      (fun df hm n ls h => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
        cases h
        exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci))
  | quot h1 h2 =>
    obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
    have hnone : env0.constants ``Quot.lift = none :=
      ((addConst_le a1).trans (addConst_le a2)).constants_eq_none_left (addConst_fresh a3)
    exact hcl.down h0le (new := [quotDefEq]) (fun df h => by
        rwa [defeqs_addDefEq, addConst_defeqs a4, addConst_defeqs a3,
          addConst_defeqs a2, addConst_defeqs a1] at h) (fun df hm n ls h => by
      simp only [List.mem_singleton] at hm; subst hm
      have hn : n = ``Quot.lift := by cases h; rfl
      subst hn; exact hnone)
  | induct _ hadd =>
    exact hcl.down (new := []) h0le
      (fun df h => .inr (by rwa [addInduct_defeqs hadd] at h)) nofun

theorem PatsClosed.of_decl {envF env0 env' : VEnv} {d : VDecl}
    (hdecl : VDecl.WF env0 d env') (hcl : PatsClosed envF env') : PatsClosed envF env0 := by
  intro p r hp ⟨ci, hci⟩
  have hp' := hcl p r hp ⟨ci, hdecl.le.constants hci⟩
  rcases hdecl.pats_eq_or_induct with heq | ⟨decl, -, hadd⟩
  · rwa [heq] at hp'
  · rcases addInduct_pats_origin hadd hp' with hold | ⟨rec, hrec, ru, hru, rfl⟩
    · exact hold
    · exfalso
      rw [SimplePattern.iota_headConst] at hci
      have := addInduct_rec_fresh hadd hrec
      rw [this] at hci; cases hci

/-- No pattern of `envF` is headed by a constant that a step declares when the step registers
no pattern. -/
theorem PatsClosed.not_head {envF env0 env' : VEnv} {n : Name} {ci : VConstant}
    (hcl : PatsClosed envF env') (hW : env0.WF) (hpats : env'.pats = env0.pats)
    (hdecl : env'.constants n = some ci) (hfresh : env0.constants n = none) :
    ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r → p.headConst ≠ n := by
  intro p r hp e
  have hp' := hcl p r hp ⟨ci, e ▸ hdecl⟩
  rw [hpats] at hp'
  obtain ⟨c, hc⟩ := hW.pat_head_declared hp'
  rw [e, hfresh] at hc; cases hc

/-! ## Projection entries along the history -/

/-- The entries of a declaration step: entries of the environment before it, or new entries
whose constructor is fresh before it. -/
theorem projections_of_decl {env0 env' : VEnv} {d : VDecl} (hdecl : VDecl.WF env0 d env') :
    ∀ S info, env'.projections S info →
      env0.projections S info ∨ env0.constants info.ctorName = none := by
  intro S info hp
  rcases hdecl.projections_eq_or_induct with heq | ⟨decl, -, hadd⟩
  · rw [heq] at hp; exact .inl hp
  · rcases (addInduct_projections_iff hadd).1 hp with ⟨entry, hentry, rfl, rfl⟩ | hold
    · obtain ⟨type, htype, ctor, hctors, rfl⟩ := VInductDecl.projectionEntries_origin hentry
      exact .inr (addInduct_ctor_fresh hadd htype (by rw [hctors]; exact List.mem_singleton_self _))
    · exact .inl hold

/-- The declaration of a projection entry (`VEnv.ProjDeclAt`) at the given header
environment. -/
theorem ProjDeclAt.ofEntry {base envTypes env : VEnv} {dsb : List VDecl}
    {decl : VInductDecl} (hbase : base.WF' dsb)
    (htypes : base.addConstVals decl.typeConstants = some envTypes) (hle : envTypes ≤ env)
    (htypesWF : ∀ type ∈ decl.types, type.toVConstant.WF base)
    (hctorsWF : ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes)
    (huvars : ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (hshape : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (hnodup : decl.sourceNames.Nodup) (hspw : decl.SourceParameterWF base)
    {entry : VProjectionEntry} (hentry : entry ∈ decl.projectionEntries) :
    env.ProjDeclAt envTypes entry.typeName entry.info := by
  obtain ⟨type, htype, ctor, hctors, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  have hmem : ctor ∈ type.ctors := by rw [hctors]; simp
  have hcc : ctor ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants, List.mem_flatMap]
    exact ⟨type, htype, hmem⟩
  have hwf := hctorsWF ctor hcc
  have hu := huvars ctor hcc
  change envTypes.IsType ctor.uvars [] ctor.type at hwf
  rw [hu] at hwf
  have hW : envTypes.WF :=
    (show base.WF from ⟨dsb, hbase⟩).addConstVals (fun ci hci => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hci; exact htypesWF t ht) htypes
  exact ⟨base, dsb, decl, type, ctor, hbase, htypes, hle, hW, htype, hctors, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, hu, hwf, hshape type htype ctor hmem, hnodup, hspw⟩

/-- Validity of a projection entry from its declaration (`ProjDeclAt`) at a header environment
that is valid. -/
theorem Model.ProjValid.of_origin {envF envTypes : VEnv} {S : Name} {info : VProjectionInfo}
    (hF : envF.WF) (hp : envF.projections S info) (hO : envF.ProjDeclAt envTypes S info)
    (V : Model.EnvValid envF envTypes) : Model.ProjValid envF S info := by
  have hTF : envTypes ≤ envF := let ⟨_, _, _, _, _, _, _, h, _⟩ := hO; h
  exact ⟨hF.projStatic hp, envTypes, hO, fun U Δ hΔ => V.soundAtH hF.orderedStrong hTF U Δ hΔ⟩

theorem Model.EnvValid.addConstVals {envF E E' : VEnv} {cis : List VConstVal}
    (V : Model.EnvValid envF E) (h : E.addConstVals cis = some E') : Model.EnvValid envF E' :=
  V.of_sub (fun df hd => by rwa [addConstVals_defeqs h] at hd)
    (fun n p hp => by rwa [addConstVals_projections h] at hp)
    (fun p r hp => by rwa [addConstVals_pats h] at hp)

/-- The entries of a declaration step are valid, given validity of the environment before it. -/
theorem projValid_of_decl {envF env0 env' : VEnv} {d : VDecl} {ds : List VDecl} (hF : envF.WF)
    (hdecl : VDecl.WF env0 d env') (hbase : env0.WF' ds) (hle : env' ≤ envF)
    (V0 : Model.EnvValid envF env0) :
    ∀ S info, env'.projections S info → Model.ProjValid envF S info := by
  intro S info hp
  have hpF := hle.projections hp
  rcases hdecl.projections_eq_or_induct with heq | ⟨decl, hdeclWF, hadd⟩
  · rw [heq] at hp; exact V0.proj _ _ hp
  rcases (addInduct_projections_iff hadd).1 hp with ⟨entry, hentry, rfl, rfl⟩ | hold
  · obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := addInduct_stages hadd
    have htypes' : env0.addConstVals decl.typeConstants = some envT := by
      rwa [VInductDecl.addTypes_eq_addConstVals] at hT
    have hTF : envT ≤ envF := (addCtors_le hC).trans <| addProjs_le.trans <|
      (addRecs_le hR).trans <| (addRules_le hP).trans hle
    have hparams := hdeclWF.sourceParameterWF htypes'
    exact Model.ProjValid.of_origin hF hpF (ProjDeclAt.ofEntry hbase htypes' hTF
      hdeclWF.types_wf (hdeclWF.source.constructorsWF_at htypes') hdeclWF.source.2.2.2.1
      hparams.rawCtorShape hdeclWF.source.2.1 hparams hentry) (V0.addConstVals htypes')
  · exact V0.proj _ _ hold

/-! ## The history induction -/

/-- **Environment validity**: every environment in the declaration history of a well-formed
`envF` is valid in the model of `envF`: its definitional axioms, its projection entries and its
registered ι patterns. -/
theorem WF'.envValid {envF : VEnv} (hF : envF.WF) :
    ∀ {ds env}, env.WF' ds → env ≤ envF → HeadsClosed envF env → PatsClosed envF env →
      Model.EnvValid envF env := by
  have henvF := hF.orderedStrong
  have hdr := hF.deltaRules
  have hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c := fun _ h => hF.isCtor_rigid h
  have hcres : ∀ c, Model.IsInstalledCtor envF c → envF.CtorResultRigid c :=
    fun _ h => hF.installedCtor_resultRigid h
  have hpctor : ∀ c, Model.IsProjCtor envF c → envF.Rigid c := fun _ h => hF.projCtor_rigid h
  intro ds env H
  induction H with
  | empty =>
    intro _ _ _
    exact ⟨fun df h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  | @decl d env' ds env0 hdecl hbase ih =>
    intro hle hcl hpc
    have h0le := hdecl.le
    have h0W : env0.WF := ⟨ds, hbase⟩
    have hcl0 := HeadsClosed.of_decl hdecl hcl
    have hpc0 := PatsClosed.of_decl hdecl hpc
    have V0 : Model.EnvValid envF env0 := ih (h0le.trans hle) hcl0 hpc0
    have hprojV := projValid_of_decl hF hdecl hbase hle V0
    refine ⟨fun df hdf => ?_, hprojV, fun p r hp => Model.PatValid.iota hF (hle.pats hp)⟩
    have hdfF := hle.defeqs hdf
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      exact V0.rule df (by rwa [addConst_defeqs hadd] at hdf)
    | «example» => exact V0.rule df hdf
    | «def» _ hadd =>
      rcases hdf with rfl | hdf
      · exact Model.RuleValid.delta henvF hdr hctor hpctor hdfF rfl
      · exact V0.rule df (by rwa [addConst_defeqs hadd] at hdf)
    | mutualDef _ hadd _ =>
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hdf
      rcases hdf with member | hdf
      · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp member
        exact Model.RuleValid.delta henvF hdr hctor hpctor hdfF rfl
      · exact V0.rule df (by rwa [addConsts_defeqs hadd] at hdf)
    | quot h1 h2 =>
      obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
      have hdefeqs : ∀ df, (e4.addDefEq quotDefEq).defeqs df →
          df ∈ [quotDefEq] ∨ env0.defeqs df := fun df h => by
        rwa [defeqs_addDefEq, addConst_defeqs a4, addConst_defeqs a3, addConst_defeqs a2,
          addConst_defeqs a1] at h
      rcases hdefeqs df hdf with hm | hdf
      · simp only [List.mem_singleton] at hm; subst hm
        have hlift : (e4.addDefEq quotDefEq).constants ``Quot.lift = some quotLiftConst :=
          addDefEq_le.constants ((addConst_le a4).constants (addConst_self a3))
        have hnone : env0.constants ``Quot.lift = none :=
          ((addConst_le a1).trans (addConst_le a2)).constants_eq_none_left (addConst_fresh a3)
        have hex := hcl.excl h0W.orderedStrong hdefeqs ⟨_, hlift⟩ hnone
        have hqu : ∀ df' ls', envF.defeqs df' →
            df'.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift ls' → df' = quotDefEq :=
          fun df' ls' hdf' h' => List.mem_singleton.1 (hex df' hdf' ls' h')
        have hpats : (e4.addDefEq quotDefEq).pats = env0.pats := by
          rw [addDefEq_pats, addConst_pats a4, addConst_pats a3, addConst_pats a2,
            addConst_pats a1]
        have hqpat := hpc.not_head h0W hpats hlift hnone
        have hQ := hF.quot_not_projection hdfF
        exact Model.RuleValid.quot henvF (hF.quotConsts hdfF) hqu hdr hctor hcres hpctor hqpat
          hQ.1 hQ.2 hdfF
      · exact V0.rule df hdf
    | induct _ hadd => exact V0.rule df (by rwa [addInduct_defeqs hadd] at hdf)
  | @inductProjections _ ds base envTypes envCtors decl block hbase hctorsW hsource htypesWF
      hconstructorUvars hctorsWF' hspw hshape htypesSource hctorsSource hprojections htypes
      hctors ihBase ihCtors =>
    intro hle hcl hpc
    have hCF : envCtors ≤ envF := addProjections_le.trans hle
    have hBC : base ≤ envCtors := (addConstVals_le htypes).trans (addConstVals_le hctors)
    have hclC : HeadsClosed envF envCtors := fun df h n ls h' ⟨ci, hci⟩ => by
      simpa using hcl df h n ls h' ⟨ci, by simpa using hci⟩
    have hpcC : PatsClosed envF envCtors := fun p r hp ⟨ci, hci⟩ => by
      simpa using hpc p r hp ⟨ci, by simpa using hci⟩
    have hclB : HeadsClosed envF base := fun df h n ls h' ⟨ci, hci⟩ => by
      have := hclC df h n ls h' ⟨ci, hBC.constants hci⟩
      rwa [addConstVals_defeqs hctors, addConstVals_defeqs htypes] at this
    have hpcB : PatsClosed envF base := fun p r hp ⟨ci, hci⟩ => by
      have := hpcC p r hp ⟨ci, hBC.constants hci⟩
      rwa [addConstVals_pats hctors, addConstVals_pats htypes] at this
    have VB := ihBase (hBC.trans hCF) hclB hpcB
    have VC := ihCtors hCF hclC hpcC
    refine ⟨fun df hdf => VC.rule df (by simpa using hdf), fun S info hp => ?_,
      fun p r hp => Model.PatValid.iota hF (hle.pats hp)⟩
    have hpF := hle.projections hp
    rw [addProjections_iff] at hp
    rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
    · rw [hprojections] at hentry
      have htypes' := htypes
      rw [htypesSource] at htypes'
      exact Model.ProjValid.of_origin hF hpF (ProjDeclAt.ofEntry hbase htypes'
        ((addConstVals_le hctors).trans hCF) htypesWF hctorsWF' hconstructorUvars hshape
        hsource hspw hentry) (VB.addConstVals htypes')
    · exact VC.proj _ _ hold

/-- **Soundness of the glued observation model** for every well-formed environment. -/
theorem WF.soundEnv {env : VEnv} (henv : env.WF) : Model.SoundEnv env := by
  obtain ⟨ds, H⟩ := henv
  have V := WF'.envValid ⟨ds, H⟩ H .rfl (fun _ h _ _ _ _ => h) (fun _ _ h _ => h)
  intro U Δ Γ t t' T hΔ H'
  exact V.soundAtH (VEnv.WF.orderedStrong ⟨ds, H⟩) .rfl U Δ hΔ H'

end VEnv
end Lean4Lean
