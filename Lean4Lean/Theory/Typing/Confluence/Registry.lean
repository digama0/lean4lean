import Lean4Lean.Theory.Typing.Confluence.HeadSeparation
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.RecursorMajorFamily
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.PatsIota
import Lean4Lean.Theory.Typing.Confluence.History

/-! # The head registries of a well-formed environment

The data the confluence engine (`Params`, `Theory/Typing/ChurchRosser.lean`) reads off an
environment: for each name, the metadata of a registered recursor of that name with a
constructor of its owner (`recursorRegistry`), and the stored definition of that name
(`definitionRegistry`). Both are chosen classically among the actual installations; the facts
below make every choice agree with the registered rules:

* every registered ι pattern has a registry entry for its recursor (`WF.pat_recursorEntry`),
  and the entry's major offset is the pattern's (`WF.recursorEntry_majorOffset`): the
  recursor's constant determines it;
* every stored equation is the quotient rule or the δ rule of a registered definition
  (`WF.defeqs_origin`), which is the registry's (`WF.definitionRegistry_of_defeq`).

With the ι rules registered as patterns (`VEnv.pats`, provenance `WF'.pats_origin`), these
tables are read off the environment directly. -/

namespace Lean4Lean

theorem VExpr.stripLams_eq_lamBody : ∀ e : VExpr, e.stripLams = e.lamBody
  | .lam _ b => stripLams_eq_lamBody b
  | .bvar _ | .sort _ | .const .. | .app .. | .forallE .. | .proj .. => rfl

theorem VExpr.piArity_mkApps_bvar (k : Nat) (args : List VExpr) :
    (VExpr.mkApps (.bvar k) args).piArity = 0 := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append, VExpr.mkApps_append]; rfl

end Lean4Lean

namespace Lean4Lean.VEnv
open InductiveSignature

variable {env : VEnv}

/-! ## Recursors -/

/-- The registered pattern `(p, r)` is the ι rule of a rule of the recursor `rec`, as
`VEnv.addRecRule` registers it. -/
def RuleOf (rec : VRecursor) (p : Pattern) (r : p.RHS × p.Check) : Prop :=
  ∃ ru ∈ rec.rules, ∃ (hc : ru.rhs.Closed)
    (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern),
    e ▸ r = (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true)

/-- All registered patterns headed by `name` are rules of one recursor of one installed
declaration. -/
def OneRecursor (env : VEnv) (hs : List VEnv) (name : Name) : Prop :=
  ∃ (decl : VInductDecl) (env₀ env₁ : VEnv) (rec : VRecursor),
    decl.WF env₀ ∧ env₀.addInduct decl = some env₁ ∧ env₁ ≤ env ∧ env₀ ∈ hs ∧ rec ∈ decl.recs ∧
    rec.name = name ∧
    ∀ (p : Pattern) (r : p.RHS × p.Check), env.pats p r → p.headConst = name → RuleOf rec p r

theorem OneRecursor.mono {env' : VEnv} {hs hs' : List VEnv} (H : OneRecursor env hs name)
    (hle : env ≤ env') (hhs : ∀ e ∈ hs, e ∈ hs')
    (hpats : ∀ (p : Pattern) (r : p.RHS × p.Check), env'.pats p r → p.headConst = name →
      env.pats p r) : OneRecursor env' hs' name :=
  let ⟨decl, env₀, env₁, rec, hd, ha, hl, hm, hr, hn, hall⟩ := H
  ⟨decl, env₀, env₁, rec, hd, ha, hl.trans hle, hhs _ hm, hr, hn,
    fun p r hp hh => hall p r (hpats p r hp hh) hh⟩

/-- **The patterns of one head are the rules of one recursor**, along the history: the heads of
an `induct` step's patterns are its recursors' names, fresh at that step. -/
theorem WFH.oneRecursor {ds : List VDecl} {hs : List VEnv} (H : env.WFH ds hs) {name : Name}
    (hex : ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = name) :
    OneRecursor env hs name := by
  induction H with
  | empty => obtain ⟨p, r, hp, -⟩ := hex; cases hp
  | projs _ _ ihCtors =>
    obtain ⟨p, r, hp, hh⟩ := hex
    exact (ihCtors ⟨p, r, by simpa using hp, hh⟩).mono addProjections_le (fun _ h => h)
      (fun p r hp _ => by simpa using hp)
  | @decl env env' d ds hs hd H _ ih =>
    have hW : env.WF := ⟨ds, H⟩
    rcases hd.pats_eq_or_induct' with hpats | ⟨decl, rfl, hdecl, hadd⟩
    · obtain ⟨p, r, hp, hh⟩ := hex
      exact (ih ⟨p, r, hpats ▸ hp, hh⟩).mono hd.le (fun _ h => List.mem_cons_of_mem _ h)
        (fun p r hp _ => hpats ▸ hp)
    · by_cases hold : ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = name
      · -- an old head: no new pattern has it
        refine (ih hold).mono (addInduct_le hadd) (fun _ h => List.mem_cons_of_mem _ h)
          (fun p r hp hh => ?_)
        rcases addInduct_pats_origin hadd hp with h | ⟨rec, hrec, ru, hru, rfl⟩
        · exact h
        · exfalso
          obtain ⟨p₀, r₀, hp₀, hh₀⟩ := hold
          obtain ⟨c, hc⟩ := hW.pat_head_declared hp₀
          rw [hh₀, ← hh, SimplePattern.iota_headConst, addInduct_rec_fresh hadd hrec] at hc
          cases hc
      · -- a new head: the name of one recursor of the declaration
        obtain ⟨p, r, hp, hh⟩ := hex
        rcases addInduct_pats_origin' hadd hp with h | ⟨rec, hrec, ru, hru, hc, e, he⟩
        · exact (hold ⟨p, r, h, hh⟩).elim
        · subst e
          refine ⟨decl, env, _, rec, hdecl, hadd, VEnv.LE.rfl, List.mem_cons_self, hrec,
            by rw [← hh, SimplePattern.iota_headConst], fun p' r' hp' hh' => ?_⟩
          rcases addInduct_pats_origin' hadd hp' with h' | ⟨rec', hrec', ru', hru', hc', e', he'⟩
          · exact (hold ⟨p', r', h', hh'⟩).elim
          · have hn : rec'.name = rec.name := by
              rw [← SimplePattern.iota_headConst rec'.name rec'.getMajorIdx ru'.ctor
                (ru'.ctorParams + ru'.nfields), ← e', hh', ← hh, SimplePattern.iota_headConst]
            cases addInduct_recs_name_inj hadd hrec' hrec hn
            exact ⟨ru', hru', hc', e', he'⟩

/-- A registry entry for the name `name`: the metadata of the recursor `rec` named `name` of an
installed declaration, read off that declaration's compilation, whose owner has a constructor, and
whose generated equations are the registered patterns headed by `name` (`covers`): every such
pattern is the ι rule of a rule of `rec` read off one of the entry's equations. -/
def RecursorEntry (env : VEnv) (name : Name) (data : RecursorData) : Prop :=
  ∃ (decl : VInductDecl) (env₀ env₁ : VEnv) (rec : VRecursor),
    RecursorRegisteredAt env data decl env₀ env₁ ∧ env₀ ∈ env.stages ∧ rec ∈ decl.recs ∧
    rec.name = name ∧ data.name = name ∧
    (∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner) ∧
    ∀ (p : Pattern) (r : p.RHS × p.Check), env.pats p r → p.headConst = name →
      ∃ (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) (ru : VRecRule),
        data.schema.signature.constructors[index].owner = data.owner ∧
        data.equation index = some equation ∧ ru ∈ rec.rules ∧
        VRecRule.OfEquation rec ru equation ∧
        ∃ (hc : ru.rhs.Closed) (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
          (ru.ctorParams + ru.nfields)).toPattern),
          e ▸ r = (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives
            rec.numMinors rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true)

theorem RecursorEntry.registered {name : Name} {data : RecursorData}
    (H : RecursorEntry env name data) : RecursorRegistered env data :=
  let ⟨_, _, _, _, h, _⟩ := H; h.registered

theorem RecursorEntry.name_eq {name : Name} {data : RecursorData}
    (H : RecursorEntry env name data) : data.name = name :=
  let ⟨_, _, _, _, _, _, _, _, h, _⟩ := H; h

theorem RecursorEntry.index {name : Name} {data : RecursorData}
    (H : RecursorEntry env name data) : ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner :=
  let ⟨_, _, _, _, _, _, _, _, _, h, _⟩ := H; h

open Classical in
/-- The recursor registry of an environment: some registry entry of each name. -/
noncomputable def recursorRegistry (env : VEnv) (name : Name) : Option RecursorData :=
  if h : ∃ data, RecursorEntry env name data then some (Classical.choose h) else none

theorem recursorRegistry_entry {name : Name} {data : RecursorData}
    (h : env.recursorRegistry name = some data) : RecursorEntry env name data := by
  unfold recursorRegistry at h
  split at h
  · cases h; exact Classical.choose_spec ‹∃ data, RecursorEntry env name data›
  · cases h

theorem recursorRegistry_of_entry {name : Name} {data : RecursorData}
    (h : RecursorEntry env name data) : ∃ data', env.recursorRegistry name = some data' := by
  unfold recursorRegistry
  rw [dif_pos ⟨data, h⟩]
  exact ⟨_, rfl⟩

theorem recursorRegistry_none {name : Name}
    (h : ∀ data, ¬RecursorEntry env name data) : env.recursorRegistry name = none := by
  unfold recursorRegistry
  rw [dif_neg fun ⟨d, hd⟩ => h d hd]

/-- A registered recursor of the environment is a constant whose type has `majorOffset + 1`
binders. -/
theorem RecursorRegistered.constant_piArity {data : RecursorData}
    (H : RecursorRegistered env data) :
    ∃ c, env.constants data.name = some c ∧ c.type.piArity = data.majorOffset + 1 := by
  obtain ⟨type, htype⟩ := H.recursorType_exists
  obtain ⟨domains, _, rfl, hlen, -⟩ := RecursorData.recursorType_shape htype
  refine ⟨_, H.recursorType htype, ?_⟩
  simp [VExpr.piArity_wrapForalls, VExpr.piArity_mkApps_bvar, hlen]

/-- The compilation data of the recursor `rec` of an installed declaration, whose rules are the
registered patterns of its name, is a registry entry. -/
theorem WF'.recursorEntry_of_oneRecursor {name : Name}
    (H1 : OneRecursor env env.stages name)
    (hex : ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = name) :
    ∃ data, RecursorEntry env name data := by
  obtain ⟨decl, env₀, env₁, rec, hdecl, hadd, hle, hstage, hrec, hname, hall⟩ := H1
  obtain ⟨p₀, r₀, hp₀, hh₀⟩ := hex
  obtain ⟨ru₀, hru₀, -⟩ := hall p₀ r₀ hp₀ hh₀
  obtain ⟨block, hcomp, hrecs, hbwf⟩ := hdecl.recsCompiled
  obtain ⟨base, expanded, s, g, auxiliaries, hbase, hdata, hprior⟩ := hcomp.exists_compilation
  have hregAt : ∀ owner, RecursorRegisteredAt env
      (RecursorData.ofInstance .anonymous (RecursorSchema.ofCompilation decl s auxiliaries) g
        owner) decl env₀ env₁ := fun owner =>
    ⟨base, expanded, g, auxiliaries, block, hdata, hprior, hbase, rfl, rfl,
      rfl, rfl, rfl, hdecl, hadd, hrecs, hle, hbwf⟩
  have hreg := fun owner => (hregAt owner).registered
  -- the entry of a rule of `rec`: the compilation entry of its equation
  have hentry : ∀ ru ∈ rec.rules, ∃ (owner : Fin s.families.size) (index : Fin s.constructors.size)
      (equation : VDefEq),
      s.constructors[index].owner = owner ∧
      (RecursorData.ofInstance .anonymous (RecursorSchema.ofCompilation decl s auxiliaries) g
        owner).equation index = some equation ∧
      (RecursorData.ofInstance .anonymous (RecursorSchema.ofCompilation decl s auxiliaries) g
        owner).name = name ∧ VRecRule.OfEquation rec ru equation := by
    intro ru hru
    obtain ⟨df, hdf, hof⟩ := hrecs.rules rec hrec ru hru
    obtain ⟨data, hmem, index, howner, hgen⟩ := hdata.recursorEntries_equation hdf .anonymous
    obtain ⟨owner, -, rfl⟩ := List.mem_map.mp hmem
    refine ⟨owner, index, df, howner, hgen, ?_, hof⟩
    have hhead := (hreg owner).equation_head howner hgen
    rw [VExpr.stripLams_eq_lamBody, ← VExpr.getAppFn_eq_fst] at hhead
    have h := hof.2.1
    rw [VExpr.headConst?_eq_some, hhead] at h
    obtain ⟨_, h⟩ := h
    exact (VExpr.const.inj h).1.trans hname
  obtain ⟨owner, index₀, eq₀, howner₀, hgen₀, hname₀, -⟩ := hentry ru₀ hru₀
  refine ⟨_, decl, env₀, env₁, rec, hregAt owner, hstage, hrec, hname, hname₀, ⟨index₀, howner₀⟩,
    fun p r hp hh => ?_⟩
  obtain ⟨ru, hru, hc, e, he⟩ := hall p r hp hh
  obtain ⟨owner', index, equation, howner, hgen, hname', hof⟩ := hentry ru hru
  -- both entries are compilation entries of the same name, hence the same entry
  have hsame : owner' = owner := by
    have hnodup := hdata.recursorEntries_nodup (key := .anonymous)
    have hm : ∀ o, RecursorData.ofInstance .anonymous (RecursorSchema.ofCompilation decl s auxiliaries)
        g o ∈ RecursorData.compilationEntries .anonymous decl s auxiliaries g :=
      fun o => List.mem_map.mpr ⟨o, List.mem_finRange _, rfl⟩
    have := nodup_map_inj_on hnodup _ (hm owner') _ (hm owner) (hname'.trans hname₀.symm)
    exact Fin.ext (congrArg (fun d : RecursorData => (d.owner : Nat)) this)
  subst hsame
  exact ⟨index, equation, ru, howner, hgen, hru, hof, hc, e, he⟩

/-- **Every registered ι pattern has a recursor registry entry.** -/
theorem WF.pat_recursorEntry (henv : env.WF) {recN ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recN major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recN major ctor fields).toPattern.Check}
    (hp : env.pats (SimplePattern.iota recN major ctor fields).toPattern r) :
    ∃ data, RecursorEntry env recN data := by
  obtain ⟨ds, H⟩ := henv.stagesH
  have hex : ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = recN :=
    ⟨_, r, hp, SimplePattern.iota_headConst _ _ _ _⟩
  exact WF'.recursorEntry_of_oneRecursor (H.oneRecursor hex) hex

/-- **The registry's major offset is the pattern's**: both are read off the recursor's
constant. -/
theorem WF.recursorEntry_majorOffset (henv : env.WF) {recN ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recN major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recN major ctor fields).toPattern.Check}
    (hp : env.pats (SimplePattern.iota recN major ctor fields).toPattern r)
    {data : RecursorData} (hentry : RecursorEntry env recN data) :
    data.majorOffset = major := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨decl, ds₀, env₀, env₁, -, -, hdecl, hadd, hle, rec, hrec, ru, hru, -, hpe, -⟩ :=
    H.pats_origin hp
  obtain ⟨rfl, rfl, -, -⟩ := SimplePattern.iota_toPattern_inj hpe
  have hreg := hentry.registered
  have hname := hentry.name_eq
  obtain ⟨c, hc, harity⟩ := hreg.constant_piArity
  have hrc := hle.constants (addInduct_rec_find hadd hrec)
  rw [hname, hrc] at hc
  cases Option.some.inj hc
  have hshape := (hdecl.rec_shape rec hrec).1
  change rec.type.piArity = _ at harity
  simp only [VRecursor.getMajorIdx]
  omega

/-- The registry entry of the recursor of a registered ι pattern. -/
theorem WF.pat_recursorRegistry (henv : env.WF) {recN ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recN major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recN major ctor fields).toPattern.Check}
    (hp : env.pats (SimplePattern.iota recN major ctor fields).toPattern r) :
    ∃ data, env.recursorRegistry recN = some data ∧ RecursorEntry env recN data ∧
      data.majorOffset = major := by
  obtain ⟨data, hentry⟩ := henv.pat_recursorEntry hp
  obtain ⟨data', hlookup⟩ := recursorRegistry_of_entry hentry
  have hentry' := recursorRegistry_entry hlookup
  exact ⟨data', hlookup, hentry', henv.recursorEntry_majorOffset hp hentry'⟩

/-- Every constructor of a registered recursor's signature has a restored equation. -/
theorem RecursorRegistered.equation_exists' {data : RecursorData}
    (H : RecursorRegistered env data) (index : Fin data.schema.signature.constructors.size) :
    ∃ equation, data.equation index = some equation := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, -⟩ := H
  have hinstance := RecursorRegistered.recursorInstance_eq hdata hu hl ht
  have hm : g.equation index ∈ g.equations := List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨equation, _, he⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hm
  exact ⟨equation, by simpa only [RecursorData.equation, hinstance, hr] using he⟩

/-- A registry entry's recursor heads a registered ι pattern: the generated equation of its
constructor is the rule of one of the recursor's rules (`RecursorRegistered.restoredEquation_pat`). -/
theorem RecursorEntry.pat {name : Name} {data : RecursorData} (H : RecursorEntry env name data) :
    ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = name := by
  have hreg := H.registered
  have hname := H.name_eq
  obtain ⟨index, howner⟩ := H.index
  obtain ⟨equation, hgen⟩ := hreg.equation_exists' index
  obtain ⟨rec, ru, hc, hof, hp⟩ := hreg.restoredEquation_pat index hgen
  refine ⟨_, _, hp, ?_⟩
  rw [SimplePattern.iota_headConst, ← hname]
  have hhead := hreg.equation_head howner hgen
  rw [VExpr.stripLams_eq_lamBody, ← VExpr.getAppFn_eq_fst] at hhead
  have h := hof.2.1
  rw [VExpr.headConst?_eq_some, hhead] at h
  obtain ⟨_, h⟩ := h
  exact (VExpr.const.inj h).1.symm

/-- The head of a registry entry is not rigid. -/
theorem RecursorEntry.not_rigid {name : Name} {data : RecursorData}
    (H : RecursorEntry env name data) : ¬env.Rigid name := fun hr =>
  let ⟨_, _, hp, hh⟩ := H.pat; hr.pats _ _ hp hh

/-! ## Definitions -/

open Classical in
/-- The definition registry of an environment: some registered definition of each name. -/
noncomputable def definitionRegistry (env : VEnv) (name : Name) : Option VDefVal :=
  if h : ∃ value : VDefVal, DefinitionRegistered env value ∧ value.name = name then
    some (Classical.choose h) else none

theorem definitionRegistry_registered {name : Name} {value : VDefVal}
    (h : env.definitionRegistry name = some value) :
    DefinitionRegistered env value ∧ value.name = name := by
  unfold definitionRegistry at h
  split at h
  · cases h
    exact Classical.choose_spec ‹∃ value : VDefVal, DefinitionRegistered env value ∧ value.name = name›
  · cases h

/-- A registered definition's value is closed. -/
theorem DefinitionRegistered.closed (henv : env.WF) {value : VDefVal}
    (H : DefinitionRegistered env value) : value.value.Closed := by
  have hw := (henv.ordered.defEqWF H.2).2
  exact VExpr.WF.closedN henv.ordered ⟨_, hw⟩ (by trivial)

theorem DefinitionRegistered.mono {env' : VEnv} {value : VDefVal}
    (H : DefinitionRegistered env value) (hle : env ≤ env') : DefinitionRegistered env' value :=
  ⟨hle.constants H.1, hle.defeqs H.2⟩

theorem addDefEqs_constants' : ∀ {cis : List VDefVal} {e : VEnv},
    (e.addDefEqs cis).constants = e.constants
  | [], _ => rfl
  | ci :: cis, e => (addDefEqs_constants' (cis := cis) (e := e.addDefEq ci.toDefEq) :)

/-- **Every stored equation is the quotient rule or the δ rule of a registered definition.** -/
theorem WF'.defeqs_origin {ds : List VDecl} (H : env.WF' ds) {df : VDefEq}
    (hdf : env.defeqs df) :
    df = quotDefEq ∨ ∃ value, DefinitionRegistered env value ∧ df = value.toDefEq := by
  induction H generalizing df with
  | empty => cases hdf
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    rcases ihCtors (by simpa using hdf) with h | ⟨value, hv, h⟩
    · exact .inl h
    · exact .inr ⟨value, hv.mono addProjections_le, h⟩
  | @decl d env' ds env hd H ih =>
    have old : env.defeqs df → env ≤ env' →
        df = quotDefEq ∨ ∃ value, DefinitionRegistered env' value ∧ df = value.toDefEq :=
      fun h hle => (ih h).imp id fun ⟨value, hv, h⟩ => ⟨value, hv.mono hle, h⟩
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 =>
      rw [addConst_defeqs h2] at hdf; exact old hdf (addConst_le h2)
    | «example» _ => exact ih hdf
    | @«def» _ _ ci _ h2 =>
      rcases hdf with rfl | hdf
      · exact .inr ⟨ci, ⟨(addConst_self h2 : _), .inl rfl⟩, rfl⟩
      · rw [addConst_defeqs h2] at hdf
        exact old hdf ((addConst_le h2).trans addDefEq_le)
    | mutualDef _ h2 _ =>
      have hdf' := hdf
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hdf'
      rcases hdf' with hm | hdf'
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
        refine .inr ⟨ci, ⟨?_, hdf⟩, rfl⟩
        rw [addDefEqs_constants']
        exact addConsts_constants h2 ci hci
      · rw [addConsts_defeqs h2] at hdf'; exact old hdf' ((addConsts_le h2).trans addDefEqs_le)
    | quot h1 h2 =>
      obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
      rcases hdf with rfl | hdf
      · exact .inl rfl
      · rw [addConst_defeqs a4, addConst_defeqs a3, addConst_defeqs a2,
          addConst_defeqs a1] at hdf
        exact old hdf ((addConst_le a1).trans ((addConst_le a2).trans ((addConst_le a3).trans
          ((addConst_le a4).trans addDefEq_le))))
    | induct _ h2 => rw [addInduct_defeqs h2] at hdf; exact old hdf (addInduct_le h2)

/-- The registry's definition of the head of a stored δ rule is that rule's definition. -/
theorem WF.definitionRegistry_of_defeq (henv : env.WF) {value : VDefVal}
    (hv : DefinitionRegistered env value) :
    env.definitionRegistry value.name = some value := by
  have hex : ∃ v : VDefVal, DefinitionRegistered env v ∧ v.name = value.name := ⟨value, hv, rfl⟩
  unfold definitionRegistry
  rw [dif_pos hex]
  congr 1
  obtain ⟨hv', hn⟩ := Classical.choose_spec hex
  generalize Classical.choose hex = v at hv' hn ⊢
  obtain ⟨ds, H⟩ := henv
  have heq := H.defeqs_const_uniq hv'.2 hv.2 (c := value.name)
    (us := VLevel.params v.uvars) (us' := VLevel.params value.uvars)
    (by simp [VDefVal.toDefEq, hn]) (by simp [VDefVal.toDefEq])
  rcases v with ⟨⟨⟨u1, t1⟩, n1⟩, v1⟩
  rcases value with ⟨⟨⟨u2, t2⟩, n2⟩, v2⟩
  simp only [VDefVal.toDefEq, VDefEq.mk.injEq] at heq hn
  obtain ⟨rfl, -, rfl, rfl⟩ := heq
  subst hn
  rfl

end Lean4Lean.VEnv
