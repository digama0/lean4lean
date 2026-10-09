import Lean4Lean.Theory.Typing.EnvTables.Registration

/-!
# Environment tables built along a declaration history

`Tables.OfHistory env T`: the tables `T` are those built step by step along a `VEnv.WF'` history of
`env` (one constructor per step, with the step's premises and the explicit table update). Every
such `T` satisfies the history invariant `Tables.Inv env` (`Tables.OfHistory.inv`), and every
well-formed environment has such tables (`VEnv.WF'.tablesOfHistory`).

The environment tables (`envTables`, `EnvTables/OfWF.lean`) are chosen among these:
the validity of the computation rules is proved by induction along the history
that built the tables, so that every table entry is justified by derivations in an earlier
environment of the same history, where soundness is already established.
-/

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

/-- Tables built along a well-formed history. -/
inductive Tables.OfHistory : VEnv → Tables → Prop
  | empty : Tables.OfHistory .empty Tables.empty
  | «axiom» {env env' : VEnv} {T : Tables} {ci : VConstVal} :
    Tables.OfHistory env T → env.WF → ci.WF env → env.addConst ci.name ci.toVConstant = some env' →
    Tables.OfHistory env' T
  | «opaque» {env env' : VEnv} {T : Tables} {ci : VDefVal} :
    Tables.OfHistory env T → env.WF → ci.WF env → env.addConst ci.name ci.toVConstant = some env' →
    Tables.OfHistory env' T
  | «def» {env env' : VEnv} {T : Tables} {ci : VDefVal} :
    Tables.OfHistory env T → env.WF → ci.WF env → env.addConst ci.name ci.toVConstant = some env' →
    Tables.OfHistory (env'.addDefEq ci.toDefEq) (T.addDefs [ci])
  | mutualDef {env env' : VEnv} {T : Tables} {cis : List VDefVal} :
    Tables.OfHistory env T → env.WF → (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' → (∀ ci ∈ cis, ci.WF env') →
    Tables.OfHistory (env'.addDefEqs cis) (T.addDefs cis)
  | quot {env env' : VEnv} {T : Tables} :
    Tables.OfHistory env T → env.WF → env.QuotReady → env.addQuot = some env' →
    Tables.OfHistory env' T.addQuot
  | induct {env env' cbase : VEnv} {T : Tables} {decl expanded : VInductDecl}
      {block : VInductBlock} {s : InductiveSignature} {g : Instance s}
      {aux : List ContainerSpecialization} :
    Tables.OfHistory env T → env.WF → decl.WF env → decl.CompilesTo env block →
    VInductBlock.WF env block → VInductBlock.EliminatorsWF env decl block →
    block.eliminators = [] → block.install env = some env' →
    cbase ≤ env → CompilationData cbase decl expanded s g aux block →
    ContainersInstalled cbase aux →
    Tables.OfHistory env' (T.addRecursor decl (RecursorData.compilationEntries default decl s aux g))
  /-- A block installation that also installs the certified case eliminator of its
  declaration: the views of the installation, then the views of the remaining families of the
  schema. -/
  | inductCases {env env' cbase : VEnv} {T : Tables} {decl expanded : VInductDecl}
      {block : VInductBlock} {s : InductiveSignature} {g : Instance s}
      {aux : List ContainerSpecialization} {key : Name} {schema : CaseSchema} :
    Tables.OfHistory env T → env.WF → decl.WF env → decl.CompilesTo env block →
    VInductBlock.WF env block → VInductBlock.EliminatorsWF env decl block →
    block.eliminators = [(key, schema)] → block.install env = some env' →
    cbase ≤ env → CompilationData cbase decl expanded s g aux block →
    ContainersInstalled cbase aux →
    Tables.OfHistory env'
      ((T.addRecursor decl (RecursorData.compilationEntries default decl s aux g)).addSchema
        env' decl)
  | elim {base env : VEnv} {T : Tables} {source : VInductDecl} {block : VInductBlock}
      {schema : CaseSchema} {key : Name} :
    Tables.OfHistory env T → base.WF → env.WF → base ≤ env →
    schema.RegistrationCertificate base source block key →
    (∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant) → env.defeqs = base.defeqs →
    schema.ProjNamesRegistered env key → source.ProjectionsCoherent env →
    schema.Fresh env key → schema.StructCompat env →
    Tables.OfHistory (env.addEliminator key schema) (T.addSchema env source)
  /-- Projection registration after the certified case eliminator of the same declaration
  (`VEnv.WF'.inductProjections`), over the tables of the base: the schema records the views of
  every family of the declaration, structures included. -/
  | proj {base envTypes envCtors : VEnv} {T : Tables} {decl : VInductDecl}
      {block : VInductBlock} {key : Name} {schema : CaseSchema} :
    Tables.OfHistory base T → base.WF → (envCtors.addEliminators block.eliminators).WF →
    block.eliminators = [(key, schema)] → schema.RegistrationCertificate base decl block key →
    decl.sourceNames.Nodup →
    (∀ type ∈ decl.types, type.toVConstant.WF base) →
    (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) →
    (∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes) →
    decl.SourceParameterWF base →
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor) →
    block.types = decl.typeConstants →
    block.ctors = decl.constructorConstants →
    block.projections = decl.projectionEntries →
    base.addConstVals block.types = some envTypes →
    envTypes.addConstVals block.ctors = some envCtors →
    Tables.OfHistory ((envCtors.addEliminators block.eliminators).addProjections block.projections)
      (T.addSchema envCtors decl)

variable {env env' : VEnv} {T : Tables}

/-- The tables of a block installation that also installs the certified case eliminator of
its declaration. -/
theorem Tables.Inv.inductCases {decl : VInductDecl} {block : VInductBlock} {key : Name}
    {schema : CaseSchema} (H : T.Inv env) (henv : env.WF) (henv' : env'.WF)
    (hcomp : decl.CompilesTo env block) (hblock : VInductBlock.WF env block)
    (helim : VInductBlock.EliminatorsWF env decl block)
    (hE : block.eliminators = [(key, schema)])
    (hinstall : block.install env = some env')
    {cbase : VEnv} {expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization} (hcle : cbase ≤ env)
    (hdata : CompilationData cbase decl expanded s g aux block)
    (hprior : ContainersInstalled cbase aux) :
    T.Extends ((T.addRecursor decl (RecursorData.compilationEntries default decl s aux g)).addSchema
        env' decl) ∧
      ((T.addRecursor decl (RecursorData.compilationEntries default decl s aux g)).addSchema
        env' decl).Inv env' := by
  classical
  obtain ⟨hext, hinv⟩ := H.install henv hcomp hblock hinstall hcle hdata hprior
  obtain ⟨_, _, _, _, hcase⟩ := helim
  rcases hcase with ⟨-, hE'⟩ | ⟨key', schema', hE', hreg', -⟩
  · rw [hE] at hE'; cases hE'
  rw [hE] at hE'
  obtain ⟨-, hs'⟩ := Prod.mk.inj (List.cons.inj hE').1.symm
  have hcert := hreg'.certified
  rw [hs'] at hcert
  have hreg : env'.eliminators key schema :=
    (install_eliminators hinstall).mpr (.inl (by rw [hE]; exact List.mem_singleton_self _))
  obtain ⟨envTypes, envCtors, envRecs, htypes, hctors, hrecs, hinstEq⟩ := install_parts hinstall
  have hle := VInductBlock.install_base_le hinstall
  have hconsts : ∀ value ∈ block.types ++ block.ctors,
      env'.constants value.name = some value.toVConstant := by
    intro value hvalue
    rcases List.mem_append.mp hvalue with hvalue | hvalue
    · rw [hinstEq]
      simp only [VEnv.addDefEqRules_constants]
      exact (VEnv.addConstVals_le hrecs).constants (VEnv.addEliminators_addProjections_le.constants
        ((VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hvalue)))
    · exact VInductBlock.install_ctor_lookup hinstall hvalue
  refine (fun h => ⟨hext.trans h.1, h.2⟩) (hinv.addSchema_registered hle hcert hreg hconsts ?_)
  intro t ht hs
  obtain ⟨_, _, _, _, _, hnames, _⟩ := hcert
  refine ⟨VEnv.WF.case_source_family_rigid henv' hreg
    (by rw [hnames]; exact List.mem_map.mpr ⟨t, ht, rfl⟩), fun c hc => ?_⟩
  exfalso
  have hsel : selCtors t = true := selCtors_iff.mpr (List.ne_nil_of_mem hc)
  have hfree := selFree_of_selFreeIn hs
  simp only [unrecorded, decide_eq_true_eq] at hfree
  have hnone := (hfree.2.2 c hc).2
  obtain ⟨p, hp⟩ := find?_exists (f := fun p : VInductiveType × VConstVal => p.2.name)
    (x := (t, c)) (mem_viewPairs.mpr ⟨ht, hsel, hc⟩) rfl
  have hsome : viewCtors decl selCtors c.name ≠ none := by
    simp [viewCtors, hp]
  exact hsome (addView_none.mp hnone).2

/-- Tables built along a history satisfy the history invariant, in a well-formed environment. -/
theorem Tables.OfHistory.inv (H : Tables.OfHistory env T) : T.Inv env ∧ env.WF := by
  induction H with
  | empty => exact ⟨Tables.empty_inv, ⟨[], .empty⟩⟩
  | «axiom» _ henv hci hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
      (VEnv.addConst_projections hadd), ⟨_, .decl (.axiom hci hadd) hds⟩⟩
  | «opaque» _ henv hci hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
      (VEnv.addConst_projections hadd), ⟨_, .decl (.opaque hci hadd) hds⟩⟩
  | @«def» env env' T ci _ henv hci hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.addDefinitions (cis := [ci]) (by simpa [VEnv.addConsts] using hadd),
      ⟨_, .decl (.def hci hadd) hds⟩⟩
  | mutualDef _ henv h1 hadd h2 ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.addDefinitions hadd, ⟨_, .decl (.mutualDef h1 hadd h2) hds⟩⟩
  | quot _ henv hready hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    have henv' : VEnv.WF _ := ⟨_, .decl (.quot hready hadd) hds⟩
    exact ⟨ih.1.addQuot ⟨ds, hds⟩ henv' hadd, henv'⟩
  | induct _ henv hdecl hcomp hblock helim _ hinstall hcle hdata hprior ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨(ih.1.install ⟨ds, hds⟩ hcomp hblock hinstall hcle hdata hprior).2,
      ⟨_, .decl (.induct (.intro hdecl hcomp hblock helim hinstall)) hds⟩⟩
  | inductCases _ henv hdecl hcomp hblock helim hE hinstall hcle hdata hprior ih =>
    have henv' : VEnv.WF _ :=
      ⟨_, .decl (.induct (.intro hdecl hcomp hblock helim hinstall)) henv.choose_spec⟩
    exact ⟨(Tables.Inv.inductCases ih.1 henv henv' hcomp hblock helim hE hinstall hcle hdata
      hprior).2, henv'⟩
  | elim _ hbase henv hle hreg hconsts hdefeqs hprojs hcoherent hfresh hcompat ih =>
    exact ⟨(ih.1.eliminator hbase hle hreg.certified hconsts hdefeqs).2,
      VEnv.WF.inductEliminators hbase henv hle hreg hconsts hdefeqs hprojs hcoherent hfresh
        hcompat⟩
  | proj _ hbase hctorsWF hE hreg hsource htypesWF hconstructorUvars hctorsWF'
      hparams hshape htypesSource hctorsSource hprojections htypes hctors ih =>
    have henv' := VEnv.WF.inductProjections hbase hctorsWF ⟨_, _, hE, hreg⟩
      hsource htypesWF hconstructorUvars hctorsWF' hparams hshape htypesSource hctorsSource
      hprojections htypes hctors
    exact ⟨(ih.1.registerCasesProjections hbase hE hreg.certified htypes hctors).2, henv'⟩

/-- Every well-formed history builds tables. -/
theorem VEnv.WF'.tablesOfHistory {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    ∃ T : Tables, Tables.OfHistory env T := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | @decl d env' ds env hdecl hprev ih =>
    obtain ⟨T, hT⟩ := ih
    have henv : env.WF := ⟨ds, hprev⟩
    cases hdecl with
    | «axiom» hci hadd => exact ⟨T, .axiom hT henv hci hadd⟩
    | «opaque» hci hadd => exact ⟨T, .opaque hT henv hci hadd⟩
    | «example» => exact ⟨T, hT⟩
    | «def» hci hadd => exact ⟨_, .def hT henv hci hadd⟩
    | mutualDef h1 hadd h2 => exact ⟨_, .mutualDef hT henv h1 hadd h2⟩
    | quot hready hadd => exact ⟨_, .quot hT henv hready hadd⟩
    | induct hadd =>
      cases hadd with
      | intro hdecl hcompile hblock helim hinstall =>
        obtain ⟨cbase, expanded, s, g, aux, hcle, hdata, hprior⟩ :=
          hcompile.exists_compilation
        have helim' := helim
        obtain ⟨_, _, _, _, hcase⟩ := helim'
        rcases hcase with ⟨-, hE⟩ | ⟨key, schema, hE, -⟩
        · exact ⟨_, .induct hT henv hdecl hcompile hblock helim hE hinstall hcle hdata hprior⟩
        · exact ⟨_, .inductCases hT henv hdecl hcompile hblock helim hE hinstall hcle hdata
            hprior⟩
  | inductEliminators hbase hprev hle hreg hconsts hdefeqs hprojs hcoherent hfresh hcompat _ ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, .elim hT ⟨_, hbase⟩ ⟨_, hprev⟩ hle hreg hconsts hdefeqs hprojs hcoherent hfresh
      hcompat⟩
  | inductProjections hbase hctorsWF hcovered hsource htypesWF hconstructorUvars hctorsWF'
      hparams hshape htypesSource hctorsSource hprojections htypes hctors ihBase _ =>
    obtain ⟨T, hT⟩ := ihBase
    obtain ⟨key, schema, hE, hreg⟩ := hcovered
    exact ⟨_, .proj hT ⟨_, hbase⟩ ⟨_, hctorsWF⟩ hE hreg hsource htypesWF
      hconstructorUvars hctorsWF' hparams hshape htypesSource hctorsSource hprojections htypes
      hctors⟩

end Lean4Lean.EnvTables
