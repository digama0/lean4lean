import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjMajorRules

/-! # Environment validity along the declaration history

`VEnv.WF'.envValid` (history induction, section 4.1 of the design notes): every
environment in the declaration history of a well-formed environment `envF` is valid in the
model of `envF` (`Model.EnvValid`): its rules, its projection entries and its eliminator
rules. The proof is by induction on the history. The semantic fact needed by a recursor rule
of a data family (`FamSort`: the family's type observations end in its recorded result sort)
comes from the soundness, in the model of `envF`, of the definitional equality between the
family's declared type and a telescope ending in that sort, a derivation of the environment
before the rules of the family were installed, whose rules are valid by the induction
hypothesis. Projection entries are validated the same way from the environment in which
their family and constructor were checked (`projValid_of_decl`), and generic case equations
from the environment at their registration (`elimValid_of_registration`).

The proof-field fact needed by singleton eliminators (mode C) comes the same way from the
soundness of the field typings recorded by `SingletonElimination`, placed in the equation's
telescope (`Model/Singleton.lean`). Uniqueness of a recursor rule per head comes from
`HeadsClosed`: along the history, no later declaration adds a rule headed by an existing
constant, so the rules headed by a recursor are exactly its block's equations. `ProjsClosed`
plays the same role for projection entries. Restored equations of nested compilations take
`FamSort` of a source family from the block's own correspondence and of a container family
from the container's compilation (`Model/RestoredRecursorRule.lean`).

`VEnv.WF.soundEnv` and `VEnv.WF.chainHeadInjectivity`: soundness of the model and chain-level
head injectivity for every well-formed environment. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

/-- **The semantic sort of a source family**: its type observations end in its
recorded result sort, in the model of any later environment `envF` in which the rules of the
environment `env0` before the family are valid. -/
theorem Model.famSort_source {envF env0 installed base envTypes : VEnv} {source : VInductDecl}
    {block : VInductBlock} {r : Restoration} {u0 : Nat} {nf family : VInductiveType}
    (henvF : envF.Ordered) (h0 : env0.Ordered) (V : Model.EnvValid envF env0)
    (hwf : ∀ t ∈ source.types, t.toVConstant.WF base) (hb : base ≤ env0)
    (htypes : base.addConstVals source.typeConstants = some envTypes)
    (hbt : block.types = source.typeConstants)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (hfamily : family ∈ source.types) (hrel : RestoresFamily r envTypes u0 nf family) :
    Model.FamSort envF family.name nf.resultLevel := by
  obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
  obtain ⟨types', ht, hti⟩ := install_parts hinst
  rw [hbt] at ht
  have hE : types'.Ordered := h0.addConstVals (fun ci hci => by
    obtain ⟨t, htm, rfl⟩ := List.mem_map.1 hci
    exact (hwf t htm).mono hb) ht
  have hTE : envTypes ≤ types' := addConstVals_mono hb htypes ht
  have hEF : types' ≤ envF := hti.trans hle
  have hfc : envF.constants family.name = some family.toVConstant :=
    hEF.constants (addConstVals_get ht (List.mem_map_of_mem hfamily))
  exact Model.famSort_of henvF hE hEF (V.of_sub
    (fun df h => by rwa [VEnv.addConstVals_defeqs ht] at h)
    (fun n p h => by rwa [VEnv.addConstVals_projections ht] at h)
    (fun b s h => by rwa [VEnv.addConstVals_eliminators ht] at h)) hfc
    (h1.mono hTE) (h2.mono hTE) hlev

/-- `FamSort` for every family of an ordinary compilation. -/
theorem Model.famSort {envF env0 installed base : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {block : VInductBlock}
    (henvF : envF.Ordered) (h0 : env0.Ordered) (V : Model.EnvValid envF env0)
    (C : CompilationData base source expanded s g [] block) (hb : base ≤ env0)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (o : Fin s.families.size) : Model.FamSort envF s.families[o].name s.families[o].resultLevel := by
  obtain ⟨envTypes, direct, htypes, hdirect, -, hfamilies⟩ := C.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem o)
  rw [List.append_nil] at hfamily
  obtain ⟨-, -, -, -, _, _, _, _, hwf, _⟩ := C.sourceWF
  have hn : s.families[o].name = family.name := hrel.name
  rw [hn]
  exact Model.famSort_source henvF h0 V hwf hb htypes C.types hinst hle hfamily hrel

/-- The rules of `envF` whose head constant is a constant of `env` are rules of `env`: no later
declaration adds a rule headed by an existing constant. -/
def HeadsClosed (envF env : VEnv) : Prop :=
  ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
    (∃ ci, env.constants n = some ci) → env.defeqs df

theorem HeadsClosed.down {envF env0 env' : VEnv} {new : List VDefEq} (H : HeadsClosed envF env')
    (hle : env0 ≤ env') (hdefeqs : ∀ df, env'.defeqs df → df ∈ new ∨ env0.defeqs df)
    (hfresh : ∀ df ∈ new, ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      env0.constants n = none) : HeadsClosed envF env0 := by
  intro df hdf n ls h ⟨ci, hci⟩
  rcases hdefeqs df (H df hdf n ls h ⟨ci, hle.constants hci⟩) with hm | ho
  · rw [hfresh df hm n ls h] at hci; cases hci
  · exact ho

theorem HeadsClosed.excl {envF env0 env' : VEnv} {new : List VDefEq} {n : Name}
    (H : HeadsClosed envF env') (hord0 : env0.Ordered)
    (hdefeqs : ∀ df, env'.defeqs df → df ∈ new ∨ env0.defeqs df)
    (hn : ∃ ci, env'.constants n = some ci) (hfresh : env0.constants n = none) :
    Model.HeadExcl envF n new := fun df' hdf' ls' h' => by
  rcases hdefeqs df' (H df' hdf' n ls' h' hn) with hm | ho
  · exact hm
  · obtain ⟨_, hc⟩ := (hord0.defEqWF ho).1.head_const_lookup hord0 (Γ := []) ⟨⟩ h'
    rw [hfresh] at hc; cases hc

private theorem declaration_le (H : VDecl.WF env decl env') : env ≤ env' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_le h
  | «def» _ h => exact (VEnv.addConst_le h).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ h _ => exact (VEnv.addConsts_le h).trans (VEnv.addDefEqs_le ..)
  | quot _ h =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    exact (VEnv.addConst_le ha).trans <| (VEnv.addConst_le hb).trans <|
      (VEnv.addConst_le hc).trans <| (VEnv.addConst_le hd).trans VEnv.addDefEq_le
  | induct h =>
    cases h with
    | intro _ _ _ _ h =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := h
      exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
        VEnv.addEliminators_addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

theorem HeadsClosed.of_decl {envF env0 env' : VEnv} (hdecl : VDecl.WF env0 d env')
    (hcl : HeadsClosed envF env') : HeadsClosed envF env0 := by
  have h0le := declaration_le hdecl
  cases hdecl with
  | «axiom» _ hadd | «opaque» _ hadd =>
    exact hcl.down (new := []) h0le
      (fun df h => .inr (by rwa [VEnv.addConst_defeqs hadd] at h)) nofun
  | «example» => exact hcl
  | @«def» env₁ _ ci _ hadd =>
    have hnone : env0.constants ci.name = none := by
      unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
    exact hcl.down (new := [ci.toDefEq]) h0le
      (fun df h => by rwa [defeqs_addDefEq, VEnv.addConst_defeqs hadd] at h)
      (fun df hm n ls h => by
        simp only [List.mem_singleton] at hm; subst hm; cases h; exact hnone)
  | mutualDef _ hadd _ =>
    rw [VEnv.addConsts_eq_addConstVals] at hadd
    exact hcl.down (new := _) h0le
      (fun df h => by
        rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hadd] at h; exact h)
      (fun df hm n ls h => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
        cases h
        exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci))
  | quot _ installed =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at installed
    obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
    have hnone : env0.constants ``Quot.lift = none := by
      have hb' : b.constants ``Quot.lift = none := by
        unfold VEnv.addConst at hc; split at hc <;> cases hc; assumption
      cases h' : env0.constants ``Quot.lift with
      | none => rfl
      | some ci =>
        have := (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h'
        rw [this] at hb'; cases hb'
    exact hcl.down h0le (new := [quotDefEq]) (fun df h => by
        rwa [defeqs_addDefEq, VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
          VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at h) (fun df hm n ls h => by
      simp only [List.mem_singleton] at hm; subst hm
      have hn : n = ``Quot.lift := by cases h; rfl
      subst hn; exact hnone)
  | induct installed =>
    cases installed with
    | @intro block _ _ compiled _ _ hinst =>
      have howned := compiled.equation_head_owned
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hinst
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinst
      refine hcl.down h0le (new := block.rules) (fun df h => by
        rwa [VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h) fun df hm n ls h => ?_
      obtain ⟨recursor, hrec, ls', hhead⟩ := howned df hm
      have hn : recursor.name = n := (VExpr.const.inj (hhead.symm.trans h)).1
      subst hn
      have hfresh := addConstVals_names_fresh hr recursor hrec
      cases h' : env0.constants recursor.name with
      | none => rfl
      | some ci =>
        have := (addConstVals_le hc).constants ((addConstVals_le ht).constants h')
        simp only [VEnv.addProjections_constants, VEnv.addEliminators_constants] at hfresh
        rw [this] at hfresh; cases hfresh

/-- A family's derivations in the environment of its headers, placed in a later environment that
contains the headers. -/
theorem addConstVals_le_of : ∀ {cis : List VConstVal} {base E1 env : VEnv},
    base.addConstVals cis = some E1 → base ≤ env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) → E1 ≤ env
  | [], base, E1, env, h, hle, _ => by
    simp [VEnv.addConstVals] at h; subst h; exact hle
  | ci :: cis, base, E1, env, h, hle, hc => by
    cases hadd : base.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at h
    | some b1 =>
      simp [VEnv.addConstVals, hadd] at h
      refine addConstVals_le_of h ?_ fun c hc' => hc c (List.mem_cons_of_mem _ hc')
      unfold VEnv.addConst at hadd; split at hadd <;> cases hadd
      refine ⟨fun {n a} hn => ?_, hle.defeqs, hle.projections, hle.eliminators⟩
      simp only at hn
      split at hn
      · rename_i e; subst e; cases hn; exact hc ci List.mem_cons_self
      · exact hle.constants hn


/-! ## Projection entries along the history -/

/-- The entries of a declaration step: entries of the environment before it, or new entries whose
constructor is fresh before it. -/
theorem projections_of_decl {env0 env' : VEnv} (hdecl : VDecl.WF env0 d env') :
    ∀ S info, env'.projections S info →
      env0.projections S info ∨ env0.constants info.ctorName = none := by
  intro S info hp
  cases hdecl with
  | «axiom» _ hadd | «opaque» _ hadd => rw [VEnv.addConst_projections hadd] at hp; exact .inl hp
  | «def» _ hadd =>
    have : _ = env0.projections := VEnv.addConst_projections hadd
    exact .inl (by rw [← this]; exact hp)
  | «example» => exact .inl hp
  | mutualDef _ hadd _ =>
    rw [VEnv.addDefEqs_projections, VEnv.addConsts_projections hadd] at hp; exact .inl hp
  | quot _ hadd => rw [VEnv.addQuot_projections hadd] at hp; exact .inl hp
  | induct installed =>
    cases installed with
    | @intro block _ _ compiled _ _ hinst =>
      rcases (EnvTables.install_projections hinst).1 hp with ⟨entry, hentry, rfl, rfl⟩ | hp
      · obtain ⟨t, c, r, ht, hc, -, -⟩ := EnvTables.install_parts hinst
        exact .inr (entry_fresh compiled.types_eq compiled.ctors_eq
          compiled.projections ht hc hentry).2
      · exact .inl hp

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
  have hord : envTypes.Ordered :=
    (show base.WF from ⟨dsb, hbase⟩).ordered.addConstVals (fun ci hci => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hci; exact htypesWF t ht) htypes
  exact ⟨base, dsb, decl, type, ctor, hbase, htypes, hle, hord, htype, hctors, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, hu, hwf, hshape type htype ctor hmem, hnodup, hspw⟩

/-- Validity of a projection entry from its declaration (`ProjDeclAt`) at a header environment
that is valid. -/
theorem Model.ProjValid.of_origin {envF envTypes : VEnv} {S : Name} {info : VProjectionInfo}
    (hF : envF.WF) (hp : envF.projections S info) (hO : envF.ProjDeclAt envTypes S info)
    (V : Model.EnvValid envF envTypes) : Model.ProjValid envF S info := by
  have hTF : envTypes ≤ envF := let ⟨_, _, _, _, _, _, _, h, _⟩ := hO; h
  exact ⟨hF.projStatic hp, envTypes, hO, fun U Δ hΔ => V.soundAtH hF.ordered hTF U Δ hΔ⟩

theorem Model.EnvValid.addConstVals {envF E E' : VEnv} {cis : List VConstVal}
    (V : Model.EnvValid envF E) (h : E.addConstVals cis = some E') : Model.EnvValid envF E' :=
  V.of_sub (fun df hd => by rwa [VEnv.addConstVals_defeqs h] at hd)
    (fun n p hp => by rwa [VEnv.addConstVals_projections h] at hp)
    (fun b s he => by rwa [VEnv.addConstVals_eliminators h] at he)

/-- The entries of a declaration step are valid, given validity of the environment before it. -/
theorem projValid_of_decl {envF env0 env' : VEnv} {ds : List VDecl} (hF : envF.WF)
    (hdecl : VDecl.WF env0 d env') (hbase : env0.WF' ds) (hle : env' ≤ envF)
    (V0 : Model.EnvValid envF env0) :
    ∀ S info, env'.projections S info → Model.ProjValid envF S info := by
  intro S info hp
  have hpF := hle.projections hp
  cases hdecl with
  | «axiom» _ hadd | «opaque» _ hadd =>
    rw [VEnv.addConst_projections hadd] at hp; exact V0.proj _ _ hp
  | «def» _ hadd =>
    have : _ = env0.projections := VEnv.addConst_projections hadd
    exact V0.proj _ _ (by rw [← this]; exact hp)
  | «example» => exact V0.proj _ _ hp
  | mutualDef _ hadd _ =>
    rw [VEnv.addDefEqs_projections, VEnv.addConsts_projections hadd] at hp; exact V0.proj _ _ hp
  | quot _ hadd => rw [VEnv.addQuot_projections hadd] at hp; exact V0.proj _ _ hp
  | induct hadd =>
    cases hadd with
    | intro hdeclWF hcompile hblock _ hinstall =>
      obtain ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, -, -, -, -⟩ := hblock
      have hinst := hinstall
      simp only [VInductBlock.install, htypes, hctors, hrecs, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def, Option.some.injEq] at hinst
      subst hinst
      rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hrecs,
        VEnv.addProjections_iff] at hp
      rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
      · rw [hcompile.projections] at hentry
        have htypes' := htypes
        rw [hcompile.types] at htypes'
        have hparams := hdeclWF.sourceParameterWF htypes'
        have hTF : envTypes ≤ envF := (VEnv.addConstVals_le hctors).trans <|
          VEnv.addEliminators_addProjections_le.trans <| (VEnv.addConstVals_le hrecs).trans <|
            VEnv.addDefEqRules_le.trans hle
        exact Model.ProjValid.of_origin hF hpF (ProjDeclAt.ofEntry hbase htypes' hTF
          hdeclWF.1.sourceTypes (hdeclWF.1.constructorsWF_at htypes') hdeclWF.1.2.2.2.1
          hparams.rawCtorShape hcompile.sourceNames hparams hentry) (V0.addConstVals htypes')
      · rw [VEnv.addEliminators_projections, VEnv.addConstVals_projections hctors,
          VEnv.addConstVals_projections htypes] at hold
        exact V0.proj _ _ hold

theorem headName_nil {source : VInductDecl} (n : Name) :
    (compilationRestoration source []).headName n = n := by
  simp [Restoration.headName, compilationRestoration, Restoration.recursorName]

/-- The family of the major of a restored recursor equation is rigid. -/
theorem restored_family_rigid {envF base installed env0 : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} {df : VDefEq} (hF : envF.WF)
    (C : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) (hbF : base ≤ envF)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (index : Fin s.constructors.size) (hdf : envF.defeqs df)
    (hm : df.HasConstructorMajor ((compilationRestoration source aux).headName
      s.constructors[index].name)) :
    envF.Rigid ((compilationRestoration source aux).headName
      s.families[s.constructors[index].owner].name) := by
  obtain ⟨ci, hci', F, lsF, hF', -, hrigF⟩ := hF.installed_constructor_result_rigid hdf hm
  rcases C.ctor_cases hprior index with ⟨fc, hfc, hfcn, lsc, hfch⟩ | ⟨cc, hcc, lsc, hcch⟩
  · have hfc' := hle.constants (VInductBlock.install_ctor_lookup hinst
      (by rw [C.ctors]; exact hfc))
    rw [hfcn, hci'] at hfc'
    cases hfc'
    rw [hfch] at hF'
    cases hF'; exact hrigF
  · have hcc' := hbF.constants hcc
    rw [hci'] at hcc'
    cases hcc'
    rw [hcch] at hF'
    cases hF'; exact hrigF

theorem ordinary_owner_lt {base : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {block : VInductBlock}
    (C : CompilationData base source expanded s g [] block) (o : Fin s.families.size) :
    o.val < source.types.length := by
  obtain ⟨_, direct, _, hdirect, hlt, -⟩ :=
    EnvTables.CaseCompilationData.family_slot C.toCaseCompilationData o
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  simpa using hlt

theorem types_constants {base env0 types : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (C : CompilationData base source expanded s g aux block)
    (ht : env0.addConstVals block.types = some types) :
    ∀ t ∈ source.types, types.constants t.name = some t.toVConstant :=
  fun t htt => addConstVals_get ht (by rw [C.types]; exact List.mem_map_of_mem htt)

/-- The environment of an installation after its projection entries is ordered. -/
theorem ordered_addProjections {env0 types ctors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (h0 : env0.Ordered) (hdw : decl.WF env0)
    (hcomp : VInductDecl.CompilesTo env0 decl block)
    (ht : env0.addConstVals block.types = some types)
    (hc : types.addConstVals block.ctors = some ctors)
    (htwf : ∀ ci ∈ block.types, ci.toVConstant.WF env0)
    (hcwf : ∀ ci ∈ block.ctors, ci.toVConstant.WF types) :
    ((ctors.addEliminators block.eliminators).addProjections block.projections).Ordered := by
  have ht' := ht
  rw [hcomp.types] at ht'
  have hparams := hdw.sourceParameterWF ht'
  exact .inductProjections h0 ((h0.addConstVals htwf ht).addConstVals hcwf hc) hcomp.sourceNames
    hdw.1.sourceTypes hdw.1.2.2.2.1 (hdw.1.constructorsWF_at ht') hparams hparams.rawCtorShape
    hcomp.types hcomp.ctors hcomp.projections ht hc

/-- **Validity of the generic equations of a registered case eliminator**, from validity of
the environment `env` at the registration. `hsrc`: a projection entry of `envF` for a family of
the certified declaration whose constructor is a case constructor of the registration is one of
the declaration's own entries, and valid. -/
theorem elimValid_of_registration {envF env base : VEnv} {key : Name} {schema : CaseSchema}
    {source : VInductDecl} {block : VInductBlock} (hF : envF.WF)
    (hEu : ∀ b s s', envF.eliminators b s → envF.eliminators b s' → s = s')
    (hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c)
    (h0 : env.Ordered) (hle : env.addEliminator key schema ≤ envF) (hble : base ≤ env)
    (hcert : schema.Certified base source block)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hpc0 : ProjsClosed envF env) (IH : Model.EnvValid envF env)
    (hsrc : ∀ F ∈ source.types, ∀ info, envF.projections F.name info →
      Model.IsCaseCtor (env.addEliminator key schema) info.ctorName →
      (⟨F.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries ∧
        Model.ProjValid envF F.name info)
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {df : VDefEq}
    (hr : schema.genericEquations key owner = some rules) (hm : df ∈ rules) :
    Model.ElimValid envF owner df := by
  have henvF := hF.ordered
  have hle0 : env ≤ envF :=
    (show env ≤ env.addEliminator key schema from ⟨id, id, id, fun h => .inr h⟩).trans hle
  have hbF : envF.eliminators key schema := hle.eliminators (.inl ⟨rfl, rfl⟩)
  have hctorsIn : ∀ value ∈ block.ctors, envF.constants value.name = some value.toVConstant :=
    fun v hv => hle0.constants (hconsts v (List.mem_append_right _ hv))
  have hbase : base ≤ envF := hble.trans hle0
  obtain ⟨rule, hgen, -⟩ := CaseSchema.generates_of_genericEquation hr hm
  have hIrig := hF.case_family_head_rigid hbF hgen
  have hcert' := hcert
  obtain ⟨expanded, aux, C, hprior, hrr, -, hfresh⟩ := hcert'
  have hpm := Model.projMajor_generic hF h0 hle C hfresh hprior hrr hble hpc0 IH hsrc hconsts
    hr hm hIrig
  rcases C.family_cases hfresh owner with
    ⟨envTypes, family, htypes, hfamily, hrel, hhn, hhl⟩ | ⟨a, ha, hhn, hhl, hlev⟩
  · obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
    have hTE : envTypes ≤ env := addConstVals_le_of htypes hble fun v hv =>
      hconsts v (List.mem_append_left _ (by rw [C.types]; exact hv))
    have hfc : envF.constants family.name = some family.toVConstant :=
      hle0.constants (hconsts _ (List.mem_append_left _ (by
        rw [C.types]; exact List.mem_map_of_mem hfamily)))
    have hfs := Model.famSort_of henvF h0 hle0 IH hfc (h1.mono hTE) (h2.mono hTE) hlev
    rw [← hhn, ← hrr] at hfs
    refine Model.ElimValid.of_certified henvF hEu hctor hcert hbF hr hm hctorsIn hbase hIrig hfs
      hpm fun levels target hlen hnz => ?_
    rw [hrr, hhl, VLevel.inst_inst, InductiveSignature.CaseSchema.genericLevels_inst hlen]
    exact hnz
  · have hfs := Model.famSort_container henvF h0 hle0 IH hprior hble ha
    rw [← hhn, ← hrr] at hfs
    refine Model.ElimValid.of_certified henvF hEu hctor hcert hbF hr hm hctorsIn hbase hIrig hfs
      hpm fun levels target hlen hnz => ?_
    rw [hrr, hhl, VLevel.inst_inst, List.map_map]
    have e : (VLevel.inst (target :: levels) ∘ VLevel.inst schema.genericLevels) =
        VLevel.inst levels := by
      funext x
      simp only [Function.comp_apply, VLevel.inst_inst, InductiveSignature.CaseSchema.genericLevels_inst hlen]
    rw [e, ← VLevel.inst_inst]
    exact hnz.of_equiv (VLevel.inst_congr_l hlev)

/-- The eliminators of a declaration step are valid, given validity of the environment before
it: an inductive declaration registers its certified case eliminator at its constructor
boundary (`VEnv.InductRegistration`). -/
theorem elimsValid_of_decl {envF env0 env' : VEnv} {ds : List VDecl} (hF : envF.WF)
    (hEu : ∀ b s s', envF.eliminators b s → envF.eliminators b s' → s = s')
    (hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c)
    (hdecl : VDecl.WF env0 d env') (hbase : env0.WF' ds) (hle : env' ≤ envF)
    (hpc : ProjsClosed envF env') (hpc0 : ProjsClosed envF env0) (V0 : Model.EnvValid envF env0)
    (hprojV : ∀ S info, env'.projections S info → Model.ProjValid envF S info) :
    Model.ElimsValid envF env' := by
  refine ⟨hEu, fun b schema owner rules df hb hr hm => ?_⟩
  rcases (VDecl.WF.eliminators_iff hdecl).1 hb with ⟨source, -, hreg⟩ | hb
  · obtain ⟨block, envTypes, envCtors, -, hcomp, hbwf, hinst, ht, hc, hE, ⟨hcert, -, -⟩, -⟩ := hreg
    have h0 : env0.Ordered := (show env0.WF from ⟨ds, hbase⟩).ordered
    obtain ⟨tE, cE, rE, htE, hcE, -, htwf, hcwf, -, -⟩ := hbwf
    cases ht.symm.trans htE
    cases hc.symm.trans hcE
    have hCO : envCtors.Ordered := (h0.addConstVals htwf ht).addConstVals hcwf hc
    obtain ⟨_, _, recursors, ht', hc', hrec, hrfl⟩ := VInductBlock.install_stages hinst
    cases ht.symm.trans ht'
    cases hc.symm.trans hc'
    have hES : envCtors.addEliminators block.eliminators = envCtors.addEliminator b schema := by
      rw [hE]; rfl
    have hCE : envCtors.addEliminator b schema ≤ env' := by
      rw [← hES, hrfl]
      exact VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hrec).trans
        VEnv.addDefEqRules_le
    have hble : env0 ≤ envCtors := (VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)
    have hconsts : ∀ value ∈ block.types ++ block.ctors,
        envCtors.constants value.name = some value.toVConstant := fun v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact (VEnv.addConstVals_le hc).constants (addConstVals_get ht hv)
      · exact addConstVals_get hc hv
    have hpcC : ProjsClosed envF envCtors := fun S info hp hcc => by
      have h := hpc0 S info hp (hcc.mono
        (fun df h => by rwa [VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h)
        (fun b s h => by
          rwa [VEnv.addConstVals_eliminators hc, VEnv.addConstVals_eliminators ht] at h))
      rwa [VEnv.addConstVals_projections hc, VEnv.addConstVals_projections ht]
    have VC : Model.EnvValid envF envCtors := (V0.addConstVals ht).addConstVals hc
    refine elimValid_of_registration hF hEu hctor hCO (hCE.trans hle) hble hcert hconsts hpcC VC
      (fun F hF' info hp hcc => ?_) hr hm
    have hcF : Model.IsCtor env' info.ctorName :=
      .inr (let ⟨b', s', o, r, h, hg, he⟩ := hcc; ⟨b', s', o, r, hCE.eliminators h, hg, he⟩)
    have hp' := hpc _ _ hp hcF
    refine ⟨?_, hprojV _ _ hp'⟩
    rcases (EnvTables.install_projections hinst).1 hp' with ⟨entry, hentry, hS, hinfo⟩ | hold
    · rw [hcomp.projections] at hentry
      rw [hS, hinfo]; exact hentry
    · exfalso
      obtain ⟨_, hci⟩ := h0.projectionConstant hold
      have ht2 := ht
      rw [hcomp.types] at ht2
      have := addConstVals_names_fresh ht2 _ (List.mem_map_of_mem hF')
      rw [this] at hci; cases hci
  · exact V0.elim.valid b schema owner rules df hb hr hm

/-- **Environment validity**: every environment in the declaration history of a
well-formed `envF` is valid in the model of `envF`: its rules, its projection entries and its
eliminator rules. -/
theorem WF'.envValid {envF : VEnv} (hF : envF.WF) :
    ∀ {ds env}, env.WF' ds → env ≤ envF → HeadsClosed envF env → ProjsClosed envF env →
      Model.EnvValid envF env := by
  have henvF := hF.ordered
  have hEu : ∀ b s s', envF.eliminators b s → envF.eliminators b s' → s = s' :=
    fun _ _ _ h1 h2 => hF.eliminators_unique h1 h2
  have hdr := hF.deltaRules
  have hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c := by
    rintro _ (⟨_, hdf, hm⟩ | ⟨_, _, _, _, hb, hgen, rfl⟩)
    · exact hF.installed_constructor_rigid hdf hm
    · exact hF.case_constructor_rigid hb hgen
  have hcres : ∀ c, Model.IsInstalledCtor envF c → envF.CtorResultRigid c :=
    fun _ ⟨_, hdf, hm⟩ => hF.installed_constructor_result_rigid hdf hm
  have hpctor : ∀ c, Model.IsProjCtor envF c → envF.Rigid c := fun _ h => hF.projCtor_rigid h
  intro ds env H
  induction H with
  | empty =>
    intro _ _ _
    exact ⟨fun df h => (by cases h), fun _ _ h => (by cases h),
      ⟨hEu, fun _ _ _ _ _ h => (by cases h)⟩⟩
  | @decl d env' ds env0 hdecl hbase ih =>
    intro hle hcl hpc
    have h0le := declaration_le hdecl
    have h0W : env0.WF := ⟨ds, hbase⟩
    have hpc0 : ProjsClosed envF env0 := hpc.down h0W (fun _ => h0le.defeqs)
      (fun _ _ => h0le.eliminators) (projections_of_decl hdecl)
    have V0 : Model.EnvValid envF env0 :=
      ih (h0le.trans hle) (HeadsClosed.of_decl hdecl hcl) hpc0
    have hprojV := projValid_of_decl hF hdecl hbase hle V0
    have hElimV := elimsValid_of_decl hF hEu hctor hdecl hbase hle hpc hpc0 V0 hprojV
    refine ⟨fun df hdf => ?_, hprojV, hElimV⟩
    have h0 : env0.Ordered := h0W.ordered
    have ih' : HeadsClosed envF env0 → ∀ df, env0.defeqs df → Model.RuleValid envF df :=
      fun _ => V0.rule
    have hdfF := hle.defeqs hdf
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      have hcl0 := hcl.down (new := []) h0le
        (fun df h => .inr (by rwa [VEnv.addConst_defeqs hadd] at h)) nofun
      exact @ih' hcl0 df (by rwa [VEnv.addConst_defeqs hadd] at hdf)
    | «example» => exact @ih' hcl df hdf
    | @«def» env₁ _ ci _ hadd =>
      have hnone : env0.constants ci.name = none := by
        unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
      have hcl0 := hcl.down (new := [ci.toDefEq]) h0le
        (fun df h => by rwa [defeqs_addDefEq, VEnv.addConst_defeqs hadd] at h)
        (fun df hm n ls h => by
          simp only [List.mem_singleton] at hm; subst hm; cases h; exact hnone)
      rcases hdf with rfl | hdf
      · exact Model.RuleValid.delta henvF hdr hctor hpctor hdfF rfl
      · exact @ih' hcl0 df (by rwa [VEnv.addConst_defeqs hadd] at hdf)
    | mutualDef _ hadd _ =>
      rw [VEnv.addConsts_eq_addConstVals] at hadd
      have hcl0 := hcl.down (new := _) h0le
        (fun df h => by
          rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hadd] at h; exact h)
        (fun df hm n ls h => by
          obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
          cases h
          exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci))
      rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or] at hdf
      rcases hdf with member | hdf
      · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp member
        exact Model.RuleValid.delta henvF hdr hctor hpctor hdfF rfl
      · exact @ih' hcl0 df (by rwa [VEnv.addConstVals_defeqs hadd] at hdf)
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
      have hnone : env0.constants ``Quot.lift = none := by
        have hb' : b.constants ``Quot.lift = none := by
          unfold VEnv.addConst at hc; split at hc <;> cases hc; assumption
        cases h' : env0.constants ``Quot.lift with
        | none => rfl
        | some ci =>
          have := (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h'
          rw [this] at hb'; cases hb'
      have hdefeqs : ∀ df, (e.addDefEq quotDefEq).defeqs df → df ∈ [quotDefEq] ∨ env0.defeqs df :=
        fun df h => by
          rwa [defeqs_addDefEq, VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at h
      have hcl0 := hcl.down h0le hdefeqs (fun df hm n ls h => by
        simp only [List.mem_singleton] at hm; subst hm
        have hn : n = ``Quot.lift := by cases h; rfl
        subst hn; exact hnone)
      have hle' : e.addDefEq quotDefEq ≤ envF := hle
      have hlift : (e.addDefEq quotDefEq).constants ``Quot.lift = some quotLiftConst :=
        VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants (VEnv.addConst_self hc))
      rcases (hdefeqs df hdf) with hm | hdf
      · simp only [List.mem_singleton] at hm; subst hm
        have hq : Model.QuotConsts envF := by
          refine ⟨?_, ?_, hle'.constants hlift⟩
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              ((VEnv.addConst_le hc).constants ((VEnv.addConst_le hb).constants
                (VEnv.addConst_self ha)))))
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              ((VEnv.addConst_le hc).constants (VEnv.addConst_self hb))))
        have hex := hcl.excl h0 hdefeqs ⟨_, hlift⟩ hnone
        have hQ := hF.quot_not_projection hdfF (hle'.constants hlift)
        exact Model.RuleValid.quot henvF hq (fun df' ls' hdf' h' => List.mem_singleton.1
          (hex df' hdf' ls' h')) hdr hctor hcres hpctor hQ.1 hQ.2 hdfF
      · exact @ih' hcl0 df hdf
    | induct installed =>
      cases installed with
      | @intro block _ hdw compiled hbwf _ hinst =>
        obtain ⟨base, expanded, s, g, aux, hbase', C, hprior⟩ :=
          compiled.exists_compilation
        have howned := compiled.equation_head_owned
        have hinst' := hinst
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hinst'
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinst'
        have hdefeqs : ∀ df, (recursors.addDefEqRules block.rules).defeqs df →
            df ∈ block.rules ∨ env0.defeqs df := fun df h => by
          rwa [VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
            VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h
        have hrecFresh : ∀ recursor ∈ block.recursors, env0.constants recursor.name = none :=
          fun recursor hrec => by
            have hfresh := addConstVals_names_fresh hr recursor hrec
            cases h' : env0.constants recursor.name with
            | none => rfl
            | some ci =>
              have := (addConstVals_le hc).constants ((addConstVals_le ht).constants h')
              simp only [VEnv.addProjections_constants, VEnv.addEliminators_constants] at hfresh
              rw [this] at hfresh; cases hfresh
        have hcl0 := hcl.down h0le hdefeqs (fun df hm n ls h => by
          obtain ⟨recursor, hrec, ls', hhead⟩ := howned df hm
          have hn : recursor.name = n := (VExpr.const.inj (hhead.symm.trans h)).1
          subst hn; exact hrecFresh recursor hrec)
        -- the environments of the installation
        obtain ⟨tE, cE, rE, htE, hcE, hrE, htwf, hcwf, hrwf, hdfwf⟩ := hbwf
        cases ht.symm.trans htE
        cases hc.symm.trans hcE
        cases hr.symm.trans hrE
        have hTO : types.Ordered := h0.addConstVals htwf ht
        have hTF : types ≤ envF := (VEnv.addConstVals_le hc).trans <| VEnv.addEliminators_addProjections_le.trans <|
          (VEnv.addConstVals_le hr).trans <| VEnv.addDefEqRules_le.trans hle
        have VT : Model.EnvValid envF types := V0.addConstVals ht
        have hsndT := VT.soundAtH henvF hTF
        have hbT : base ≤ types := hbase'.trans (VEnv.addConstVals_le ht)
        have htypesT := types_constants C ht
        have hbF : base ≤ envF := hbase'.trans (h0le.trans hle)
        rcases hdefeqs df hdf with member | hdf
        rcases (Classical.em (aux = [])).symm with haux | haux
        · -- nested compilations
          obtain ⟨src, hsrc, hres⟩ := Lean4Lean.List.Forall₂.forall_exists_r
            (List.mapM_eq_some.mp C.equations) _ member
          obtain ⟨index, -, rfl⟩ := List.mem_map.1 hsrc
          obtain ⟨rec', hrec', hn, -⟩ := C.restored_recursor s.constructors[index].owner
          have hc1 := VInductBlock.install_recursor_lookup hinst hrec'
          have hc2 := hrecFresh _ hrec'
          rw [hn] at hc1 hc2
          have hex := hcl.excl h0 hdefeqs ⟨_, hc1⟩ hc2
          have hmemF : s.families[s.constructors[index].owner] ∈ s.families.toList :=
            Array.mem_toList_iff.2 (Array.getElem_mem s.constructors[index].owner.isLt)
          obtain ⟨_, _, _, _, _, _, -, -, hl, -⟩ := g.restored_equation index
            (fun h hh => Nat.le_of_eq (C.restoration_nparams h hh)) (C.heads_not_recursors _) hres
          have hrigF := restored_family_rigid hF C hprior hbF hinst hle index hdfF
            ⟨_, _, _, by rw [hl, VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]; rfl⟩
          have hpm := Model.projMajor_restored hF C hprior h0 hinst hle hpc hprojV hbase'
            (h0le.trans hle) hpc0 V0.proj hTO hTF hsndT hbT htypesT index hres hrigF
          rcases C.family_cases s.constructors[index].owner with
            ⟨envTypes, family, htypes, hfamily, hrel, hhn, hhl⟩ | ⟨a, ha, hhn, hhl, hlev⟩
          · obtain ⟨-, -, -, -, _, _, _, _, hwf, _⟩ := C.sourceWF
            have hfs := Model.famSort_source henvF h0 V0 hwf hbase' htypes C.types
              hinst hle hfamily hrel
            exact Model.RuleValid.nested henvF hdr hctor hcres hpctor C hprior haux hbF hinst hle
              index hres hdfF hpm hex
              (L := s.families[s.constructors[index].owner].resultLevel)
              (by rw [hhn]; exact hfs) (fun hnz => by rw [hhl]; exact hnz _ hmemF)
          · have hfs := Model.famSort_container henvF h0 (h0le.trans hle) V0 hprior hbase' ha
            exact Model.RuleValid.nested henvF hdr hctor hcres hpctor C hprior haux hbF hinst hle
              index hres hdfF hpm hex (L := a.source.resultLevel) (by rw [hhn]; exact hfs)
              (fun hnz => by
                rw [hhl, ← VLevel.inst_inst]
                exact (hnz _ hmemF).of_equiv (VLevel.inst_congr_l hlev))
        · subst haux
          rw [C.ordinary_rules] at member
          obtain ⟨index, -, rfl⟩ := List.mem_map.1 member
          have hrec : g.recursor s.constructors[index].owner ∈ block.recursors := by
            rw [C.ordinary_recursors]; exact List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩
          have hex := hcl.excl h0 hdefeqs
            ⟨_, VInductBlock.install_recursor_lookup hinst hrec⟩ (hrecFresh _ hrec)
          have hER : recursors.Ordered :=
            (ordered_addProjections h0 hdw compiled ht hc htwf hcwf).addConstVals hrwf hr
          have hERF : recursors ≤ envF := VEnv.addDefEqRules_le.trans hle
          have VR : Model.EnvValid envF recursors :=
            ⟨fun df h => V0.rule df (by
              rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
                VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h),
            fun n p h => hprojV n p (VEnv.addDefEqRules_le.projections h),
            hElimV.mono VEnv.addDefEqRules_le⟩
          have hmem : g.equation index ∈ block.rules := by
            rw [C.ordinary_rules]; exact List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩
          have hdoms : OnCtx (g.eqDoms index).reverse (recursors.IsType g.uvars) := by
            have hty := IsDefEq.isType hER (show OnCtx [] (recursors.IsType g.uvars) from trivial)
              (hdfwf _ hmem).1
            rw [g.equation_type_eq] at hty
            simpa using onCtx_wrapForalls hER (show OnCtx [] (recursors.IsType g.uvars) from trivial)
              hty
          -- the projection facts of the major
          have hrigF := restored_family_rigid hF C hprior hbF hinst hle index hdfF
            ⟨_, _, _, by rw [headName_nil, g.equation_lhs_eq, VExpr.stripLams_wrapLams,
              VExpr.mkApps_snoc]; rfl⟩
          have hpm := Model.projMajor_source hF C hprior h0 hinst hle hpc hprojV hTO hTF hsndT
            hbT htypesT index (ordinary_owner_lt C _) hrigF
          rw [headName_nil, headName_nil] at hpm
          exact Model.RuleValid.recursor henvF hdr hctor hcres hpctor C hinst hle index hdfF hpm hex
            (Model.famSort henvF h0 V0 C hbase' hinst hle _)
            (fun envE hE hsing U Δ Γ ls hΔ hlw _ i hi hidx => by
              have hEE : envE ≤ recursors := by
                rw [C.ordinary_expanded_types, ← C.types] at hE
                exact (addConstVals_mono hbase' hE ht).trans
                  ((VEnv.addConstVals_le hc).trans
                    (VEnv.addEliminators_addProjections_le.trans (VEnv.addConstVals_le hr)))
              exact Model.proofBinder_of henvF hER hERF VR hdoms
                (singleton_field_typing hER hEE hsing index hi hidx) hΔ hlw)
        · exact @ih' hcl0 df hdf
  | @inductEliminators _ _ key base env source block schema _ hW hble hreg hconsts _ _ hcoherent _
      hsc _ ih =>
    intro hle hcl hpc
    have hle0 : env ≤ envF :=
      (show env ≤ env.addEliminator key schema from ⟨id, id, id, fun h => .inr h⟩).trans hle
    have hpc0 : ProjsClosed envF env := fun S info hp hc =>
      hpc S info hp (Model.IsCtor.mono (env := env) (env' := env.addEliminator key schema)
        (fun _ h => h) (fun _ _ h => .inr h) hc)
    have IH := ih hle0 (fun df h n ls hh hc => hcl df h n ls hh hc) hpc0
    have h0 : env.Ordered := (show env.WF from ⟨_, hW⟩).ordered
    refine ⟨fun df hdf => IH.rule df hdf, fun S info hp => IH.proj S info hp,
      ⟨hEu, fun b schema' owner rules df hb hr hm => ?_⟩⟩
    rcases hb with ⟨rfl, rfl⟩ | hb
    rotate_left
    · exact IH.elim.valid _ _ _ _ _ hb hr hm
    exact elimValid_of_registration hF hEu hctor h0 hle hble hreg.certified hconsts hpc0 IH
      (fun F hF' info hp hc => by
        have hp0 := hpc _ _ hp (.inr hc)
        exact ⟨hcoherent _ hF' info hp0, IH.proj _ _ hp0⟩) hr hm
  | @inductProjections _ ds base envTypes envCtors decl block hbase _ helimE hsource htypesWF
      hconstructorUvars hctorsWF' hspw hshape htypesSource hctorsSource hprojections htypes hctors
      ihBase _ =>
    -- The intermediate environment `envCtors.addEliminators block.eliminators` registers the
    -- block's certified case eliminator before its projection entries, so a constructor of a
    -- block structure is a case constructor there without its entry: its validity is not that
    -- of an earlier environment.
    -- The block's rules and entries come from `base`, and its eliminator is validated directly.
    intro hle hcl hpc
    obtain ⟨key, schema, hE, ⟨hcert, -, -⟩⟩ := helimE
    have hES : envCtors.addEliminators block.eliminators = envCtors.addEliminator key schema := by
      rw [hE]; rfl
    have hEF : envCtors.addEliminator key schema ≤ envF := by
      rw [← hES]; exact VEnv.addProjections_le.trans hle
    have hCF : envCtors ≤ envF :=
      (show envCtors ≤ envCtors.addEliminator key schema from
        ⟨id, id, id, fun h => .inr h⟩).trans hEF
    have hBC : base ≤ envCtors := (VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)
    have hdfBC : ∀ df, envCtors.defeqs df ↔ base.defeqs df := fun df => by
      rw [VEnv.addConstVals_defeqs hctors, VEnv.addConstVals_defeqs htypes]
    have helBC : ∀ b s, envCtors.eliminators b s ↔ base.eliminators b s := fun b s => by
      rw [VEnv.addConstVals_eliminators hctors, VEnv.addConstVals_eliminators htypes]
    have hprBC : ∀ S info, envCtors.projections S info ↔ base.projections S info := fun S info => by
      rw [VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes]
    have hbW : base.WF := ⟨_, hbase⟩
    have hclB : HeadsClosed envF base := fun df' h n ls h' ⟨ci, hci⟩ => by
      have := hcl df' h n ls h' ⟨ci, by simpa using hBC.constants hci⟩
      exact (hdfBC df').1 (by simpa using this)
    have hpcB : ProjsClosed envF base := by
      intro S info hp hc
      have hcF0 : Model.IsCtor ((envCtors.addEliminators block.eliminators).addProjections
          block.projections) info.ctorName :=
        hc.mono (fun df h => by simpa using (hdfBC df).2 h) (fun b s h => by
          rw [VEnv.addProjections_eliminators, VEnv.addEliminators_iff]
          exact .inr ((helBC b s).2 h))
      rcases (VEnv.addProjections_iff).1 (hpc S info hp hcF0) with
        ⟨entry, hentry, rfl, rfl⟩ | hold
      · exfalso
        obtain ⟨ci, hci⟩ := hbW.isCtor_const hc
        rw [(entry_fresh htypesSource hctorsSource hprojections htypes hctors hentry).2] at hci
        cases hci
      · rw [VEnv.addEliminators_projections] at hold
        exact (hprBC S info).1 hold
    have VB := ihBase (hBC.trans hCF) hclB hpcB
    have VC : Model.EnvValid envF envCtors := (VB.addConstVals htypes).addConstVals hctors
    have hpcC : ProjsClosed envF envCtors := fun S info hp hc =>
      (hprBC S info).2 (hpcB S info hp (hc.mono (fun df h => (hdfBC df).1 h)
        (fun b s h => (helBC b s).1 h)))
    have hprojV : ∀ S info, ((envCtors.addEliminators block.eliminators).addProjections
        block.projections).projections S info → Model.ProjValid envF S info := by
      intro S info hp
      have hpF := hle.projections hp
      rw [VEnv.addProjections_iff] at hp
      rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
      · rw [hprojections] at hentry
        have htypes' := htypes
        rw [htypesSource] at htypes'
        exact Model.ProjValid.of_origin hF hpF (ProjDeclAt.ofEntry hbase htypes'
          ((VEnv.addConstVals_le hctors).trans hCF) htypesWF hctorsWF' hconstructorUvars hshape
          hsource hspw hentry) (VB.addConstVals htypes')
      · rw [VEnv.addEliminators_projections] at hold
        exact VC.proj _ _ hold
    have hCO : envCtors.Ordered :=
      (hbW.ordered.addConstVals (fun ci hci => by
        rw [htypesSource] at hci
        obtain ⟨t, htm, rfl⟩ := List.mem_map.1 hci
        exact htypesWF t htm) htypes).addConstVals
        (fun ci hci => hctorsWF' ci (by rw [← hctorsSource]; exact hci)) hctors
    have hconsts : ∀ value ∈ block.types ++ block.ctors,
        envCtors.constants value.name = some value.toVConstant := fun v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact (VEnv.addConstVals_le hctors).constants (addConstVals_get htypes hv)
      · exact addConstVals_get hctors hv
    refine ⟨fun df hdf => VB.rule df ((hdfBC df).1 (by simpa using hdf)), hprojV,
      ⟨hEu, fun b schema' owner rules df hb hr hm => ?_⟩⟩
    rw [VEnv.addProjections_eliminators, VEnv.addEliminators_iff, hE] at hb
    rcases hb with hb | hb
    · simp only [List.mem_singleton, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine elimValid_of_registration hF hEu hctor hCO hEF hBC hcert hconsts hpcC VC
        (fun F hF' info hp hcc => ?_) hr hm
      have hcF0 : Model.IsCtor ((envCtors.addEliminators block.eliminators).addProjections
          block.projections) info.ctorName :=
        .inr (let ⟨b', s', o, r, h, hg, he⟩ := hcc
          ⟨b', s', o, r, by rw [VEnv.addProjections_eliminators, hES]; exact h, hg, he⟩)
      have hp0 := hpc _ _ hp hcF0
      refine ⟨?_, hprojV _ _ hp0⟩
      rcases (VEnv.addProjections_iff).1 hp0 with ⟨entry, hentry, hS, hinfo⟩ | hold
      · rw [hprojections] at hentry
        rw [hS, hinfo]; exact hentry
      · exfalso
        rw [VEnv.addEliminators_projections, hprBC] at hold
        obtain ⟨_, hci⟩ := hbW.ordered.projectionConstant hold
        have ht2 := htypes
        rw [htypesSource] at ht2
        have := addConstVals_names_fresh ht2 _ (List.mem_map_of_mem hF')
        rw [this] at hci; cases hci
    · exact VC.elim.valid _ _ _ _ _ hb hr hm

/-- **Soundness of the glued observation model** for every well-formed environment. -/
theorem WF.soundEnv {env : VEnv} (henv : env.WF) : Model.SoundEnv env := by
  obtain ⟨ds, H⟩ := henv
  have V := WF'.envValid ⟨ds, H⟩ H .rfl (fun _ h _ _ _ _ => h) (fun _ _ h _ => h)
  intro U Δ Γ t t' T hΔ H'
  exact V.soundAtH (VEnv.WF.ordered ⟨ds, H⟩) .rfl U Δ hΔ H'

/-- **Chain-level head injectivity** for every well-formed environment. -/
theorem WF.chainHeadInjectivity {env : VEnv} (henv : env.WF) : env.ChainHeadInjectivity :=
  WF.chainHeadInjectivity_of_sound henv henv.soundEnv

end VEnv
end Lean4Lean
