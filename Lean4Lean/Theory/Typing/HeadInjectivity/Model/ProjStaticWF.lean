import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjValid
import Lean4Lean.Theory.Typing.EnvTables.CtorFamily
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.RestoredRecursorEquations
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.ConstructorRigidity

/-! # Static facts about projection entries of well-formed environments

The constructor and family tables (`EnvTables.ctorOf`, `EnvTables.famOf`,
`Theory/Typing/EnvTables/OfWF.lean`) record every registered structure with its
constructor, every constructor major of a stored rule, and every generic case major of a registered
schema whose view is the recorded one. A family is never a constructor of the tables, and table
entries are rigid. -/

/-!
# Restoration of Pi telescopes

`restoration_wrapForalls_forall₂`: restoring a Pi telescope restores each domain and the body
separately and gives a Pi telescope of the same length.
-/

namespace Lean4Lean.EnvTables
open Lean4Lean InductiveSignature

theorem restoration_wrapForalls_forall₂ {r : Restoration} :
    ∀ {domains : List VExpr} {body output : VExpr},
      r.expr (VExpr.wrapForalls domains body) = some output →
      ∃ domains' body', output = VExpr.wrapForalls domains' body' ∧
        List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧ r.expr body = some body'
  | [], _, output, H => ⟨[], output, rfl, .nil, H⟩
  | d :: ds, body, output, H => by
    change (do let d' ← r.expr d; let t' ← r.expr (VExpr.wrapForalls ds body)
               pure (.forallE d' t')) = some output at H
    simp only [bind, Option.bind_eq_some_iff] at H
    obtain ⟨d', hd, out, hout, H⟩ := H
    cases H
    obtain ⟨ds', body', rfl, hrel, hb⟩ := restoration_wrapForalls_forall₂ (domains := ds) hout
    exact ⟨d' :: ds', body', rfl, .cons hd hrel, hb⟩

end Lean4Lean.EnvTables


namespace Lean4Lean
namespace VEnv
open InductiveSignature

variable {env : VEnv}

/-- The major of a generic case rule of a registered schema is literally its constructor. -/
theorem Model.generates_major {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {rule : CaseSchema.AppliedRule} (hgen : schema.Generates key owner rule) :
    ∃ fn ls args, rule.equation.lhs.stripLams =
      .app fn (VExpr.mkApps (.const rule.application.ctorName ls) args) := by
  obtain ⟨_, _, _, hextract⟩ := hgen
  have hb := (CaseSchema.Generates.body_exact ⟨_, ‹_›, ‹_›, hextract⟩).1
  have ha := CaseSchema.Application.extract_sound
    (CaseSchema.AppliedRule.extract_spec hextract).2.2.1
  refine ⟨VExpr.mkApps (.elim rule.application.block rule.application.owner
    rule.application.levels) rule.application.arguments, rule.application.ctorLevels,
    rule.application.ctorArguments, ?_⟩
  rw [← hb, VExpr.stripLams_wrapLams, ← ha]
  rfl

/-- An installed constructor (the major of a stored rule) is a constructor of the table. -/
theorem WF.ctorOf_of_installedCtor (henv : env.WF) (h : Model.IsInstalledCtor env c) :
    EnvTables.ctorOf env c ≠ none := by
  obtain ⟨df, hdf, fn, ls, args, hm⟩ := h
  obtain ⟨k, _, _, hk, _⟩ := EnvTables.defeq_major henv hdf hm
  simp [hk]

/-- A case constructor is a constructor of the table, or a constructor, in the schema's view, of
a source family of the schema which is its syntactic family. -/
theorem WF.caseCtor_cases (henv : env.WF) (h : Model.IsCaseCtor env c) :
    EnvTables.ctorOf env c ≠ none ∨ ∃ (key : Name) (schema : CaseSchema)
      (owner : Fin schema.signature.families.size), env.eliminators key schema ∧
      schema.sourceFamilies[owner.val]? = EnvTables.ctorFamily env c ∧
      c ∈ (schema.view owner).constructors.toList.map (·.name) := by
  obtain ⟨key, schema, owner, rule, hreg, hgen, rfl⟩ := h
  obtain ⟨fn, ls, args, hm⟩ := Model.generates_major hgen
  obtain ⟨rules, hrules, hmem, -⟩ := hgen
  rcases EnvTables.generic_major_cases henv hreg hrules hmem hm with h | ⟨ho, hc⟩
  · exact .inl h
  · exact .inr ⟨key, schema, owner, hreg, ho, hc⟩

theorem Model.ctorFamily_of_ctorFam (h : Model.CtorFam env c I) :
    EnvTables.ctorFamily env c = some I := by
  obtain ⟨ci, ls, hci, hres⟩ := h
  simp [EnvTables.ctorFamily, hci, EnvTables.familyOfType, hres]

/-- **The constructor of a registered structure is rigid.** -/
theorem WF.projCtor_rigid (henv : env.WF) : Model.IsProjCtor env c → env.Rigid c := by
  rintro ⟨fam, info, hp, rfl⟩
  exact (EnvTables.ctorOf_rigid henv (EnvTables.ctorOf_projection henv hp)).1

/-- A registered structure is not the constructor of a registered structure. -/
theorem WF.projFamily_not_projCtor (henv : env.WF) (hp : env.projections S info) :
    ¬ Model.IsProjCtor env S := by
  rintro ⟨fam, info', hp', hn⟩
  have h1 := (EnvTables.ctorOf_rigid henv (EnvTables.ctorOf_projection henv hp)).2.2
  rw [← hn, EnvTables.ctorOf_projection henv hp'] at h1
  cases h1

/-- A registered structure is not an installed constructor. -/
theorem WF.projFamily_not_installedCtor (henv : env.WF) (hp : env.projections S info) :
    ¬ Model.IsInstalledCtor env S := fun h => henv.ctorOf_of_installedCtor h
  (EnvTables.ctorOf_rigid henv (EnvTables.ctorOf_projection henv hp)).2.2

/-- **Static facts of a projection entry** (`Model.ProjStatic`) of a well-formed environment. -/
theorem WF.projStatic (henv : env.WF) (hp : env.projections S info) :
    Model.ProjStatic env S info := by
  have hk := EnvTables.ctorOf_projection henv hp
  have hr := EnvTables.ctorOf_rigid henv hk
  exact ⟨hr.2.1, hr.1, henv.projFamily_not_installedCtor hp, henv.projFamily_not_projCtor hp,
    henv.ordered.closedC (henv.ordered.projectionConstructor hp)⟩

/-- **A constructor of a registered structure belongs to that structure.** -/
theorem WF.projCtor_family (henv : env.WF) (hpc : Model.IsProjCtor env c)
    (hcf : Model.CtorFam env c I) : ∃ info, env.projections I info ∧ info.ctorName = c := by
  obtain ⟨fam, info, hp, rfl⟩ := hpc
  have h1 := (EnvTables.ctorOf_ctorShape henv (EnvTables.ctorOf_projection henv hp)).family
  rw [Model.ctorFamily_of_ctorFam hcf] at h1
  cases h1
  exact ⟨info, hp, rfl⟩

/-- **A registered structure has exactly its registered constructor** among the constructors
(installed or case) whose type returns it. -/
theorem WF.ctor_of_projFamily (henv : env.WF) (hp : env.projections I info)
    (hc : Model.IsCtor env c) (hcf : Model.CtorFam env c I) : c = info.ctorName := by
  have hf := Model.ctorFamily_of_ctorFam hcf
  have fromTable : EnvTables.ctorOf env c ≠ none → c = info.ctorName := by
    intro h
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
    have hfam := (EnvTables.ctorOf_ctorShape henv hk).family
    rw [hf] at hfam
    cases hfam
    have hmem := (EnvTables.famOf_mem_ctors henv (EnvTables.famOf_projection henv hp)).mpr
      ⟨k, hk, rfl⟩
    simpa using hmem
  rcases hc with h | h
  · exact fromTable (henv.ctorOf_of_installedCtor h)
  · rcases henv.caseCtor_cases h with h | ⟨key, schema, owner, hreg, ho, hmem⟩
    · exact fromTable h
    · rw [hf] at ho
      rw [henv.schemaStructCompat hreg hp owner ho] at hmem
      simpa using hmem

end VEnv
end Lean4Lean

/-! ## The quotient is not projection-registered -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

variable {env : VEnv}

theorem _root_.Lean4Lean.VExpr.mkApps_ne_nil_app : ∀ {args : List VExpr} (hd : VExpr),
    args ≠ [] → ∃ f a, VExpr.mkApps hd args = .app f a
  | [], _, h => absurd rfl h
  | [a], hd, _ => ⟨hd, a, rfl⟩
  | a :: b :: l, hd, _ => VExpr.mkApps_ne_nil_app (args := b :: l) (.app hd a) (by simp)

/-- The type of a recursor of a finite compilation returns an application (of a motive). -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.recursor_forallResult_app {s : InductiveSignature} {g : Instance s}
    (C : CompilationData base source expanded s g aux block) {recr : VConstVal} (hrec : recr ∈ block.recursors) :
    ∃ f a, recr.type.forallResult = .app f a := by
  have hrs := List.mapM_eq_some.mp C.recursors
  obtain ⟨a, ha, hr⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrs _ hrec
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 ha
  obtain ⟨-, -, ht⟩ := Restoration.recursor_parts hr
  change Restoration.expr _ (g.recursorType o) = _ at ht
  unfold Instance.recursorType at ht
  obtain ⟨D', B', heq, -, hb⟩ := EnvTables.restoration_wrapForalls_forall₂ ht
  obtain ⟨args', hargs, rfl⟩ := InductiveSignature.Restoration.expr_bvar_mkApps hb
  rw [heq, VExpr.forallResult_wrapForalls]
  have hlen := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hargs)
  obtain ⟨f, x, e⟩ := VExpr.mkApps_ne_nil_app (args := args') (.bvar _) (by
    intro h; rw [h] at hlen; simp at hlen)
  rw [e]
  exact ⟨f, x, rfl⟩

theorem quotLiftConst_forallResult_not_app : ∀ f a, quotLiftConst.type.forallResult ≠ .app f a := by
  intro f a h
  simp [quotLiftConst, VExpr.forallResult] at h

private theorem quotDefEq_ne_toDefEq (v : VDefVal) : quotDefEq ≠ v.toDefEq := by
  intro h
  have := congrArg VDefEq.lhs h
  simp [VDefVal.toDefEq] at this
  cases this

private theorem quotDefEq_head :
    quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift [.param 0, .param 1] := rfl

/-- In an ordered environment containing the quotient rule, `Quot.lift` is declared. -/
private theorem quotLift_declared (henv : env.Ordered) (hq : env.defeqs quotDefEq) :
    ∃ ci, env.constants ``Quot.lift = some ci :=
  (henv.defEqWF hq).1.head_const_lookup henv (Γ := []) ⟨⟩ quotDefEq_head

/-- A fresh entry of a declaration names a family and a constructor fresh in the base. -/
theorem entry_fresh {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    {entry : VProjectionEntry} (hentry : entry ∈ block.projections) :
    base.constants entry.typeName = none ∧ base.constants entry.info.ctorName = none := by
  rw [hprojections] at hentry
  obtain ⟨type, htype, ctor, hcs, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  refine ⟨VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
    rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩), ?_⟩
  have hf := VEnv.addConstVals_names_fresh hctors ctor (by
    rw [hctorsSource, VInductDecl.constructorConstants]
    exact List.mem_flatMap.mpr ⟨type, htype, by simp [hcs]⟩)
  change base.constants ctor.name = none
  cases h : base.constants ctor.name with
  | none => rfl
  | some ci => rw [(VEnv.addConstVals_le htypes).constants h] at hf; cases hf


/-- The quotient facts along the declaration history: an environment containing the quotient
rule, with `Quot.lift` at its primitive type, declares `Quot` and `Quot.mk`, and no projection
entry names `Quot` or has constructor `Quot.mk` (every entry names a family and a constructor
fresh at its registration). -/
theorem WF'.quot_projections : ∀ {ds env}, VEnv.WF' ds env → env.defeqs quotDefEq →
    env.constants ``Quot.lift = some quotLiftConst →
    (∃ c, env.constants ``Quot = some c) ∧ (∃ c, env.constants ``Quot.mk = some c) ∧
      ∀ S info, env.projections S info → S ≠ ``Quot ∧ info.ctorName ≠ ``Quot.mk := by
  intro ds env H
  induction H with
  | empty => intro h; cases h
  | @decl d env' ds env0 hdecl hbase ih =>
    intro hq hlift
    have hord0 : env0.Ordered := (show env0.WF from ⟨ds, hbase⟩).ordered
    have ih0 : env0 ≤ env' → env0.defeqs quotDefEq →
        (∃ c, env'.constants ``Quot = some c) ∧ (∃ c, env'.constants ``Quot.mk = some c) ∧
        ∀ S info, env0.projections S info → S ≠ ``Quot ∧ info.ctorName ≠ ``Quot.mk := by
      intro hle h0
      obtain ⟨ci, hci⟩ := quotLift_declared hord0 h0
      have h1 := hle.constants hci
      rw [hlift] at h1
      cases h1
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hc⟩ := ih h0 hci
      exact ⟨⟨a, hle.constants ha⟩, ⟨b, hle.constants hb⟩, hc⟩
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      rw [VEnv.addConst_defeqs hadd] at hq
      obtain ⟨h1, h2, h3⟩ := ih0 (VEnv.addConst_le hadd) hq
      exact ⟨h1, h2, fun S info hp => h3 S info (by rwa [VEnv.addConst_projections hadd] at hp)⟩
    | «example» => exact ih hq hlift
    | «def» _ hadd =>
      rcases defeqs_addDefEq.1 hq with hm | hq
      · exact absurd (List.mem_singleton.1 hm) (quotDefEq_ne_toDefEq _)
      rw [VEnv.addConst_defeqs hadd] at hq
      obtain ⟨h1, h2, h3⟩ := ih0 ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le) hq
      refine ⟨h1, h2, fun S info hp => h3 S info ?_⟩
      have : _ = env0.projections := VEnv.addConst_projections hadd
      rw [← this]; exact hp
    | mutualDef _ hadd _ =>
      rename_i cis E _ _
      have hle : env0 ≤ E.addDefEqs cis := (VEnv.addConsts_le hadd).trans (VEnv.addDefEqs_le)
      have hproj := VEnv.addConsts_projections hadd
      rw [VEnv.addConsts_eq_addConstVals] at hadd
      rw [VEnv.addDefEqs_eq_addDefEqRules, VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hadd] at hq
      rcases hq with hm | hq
      · obtain ⟨ci, -, e⟩ := List.mem_map.1 hm
        exact absurd e.symm (quotDefEq_ne_toDefEq _)
      obtain ⟨h1, h2, h3⟩ := ih0 hle hq
      refine ⟨h1, h2, fun S info hp => h3 S info ?_⟩
      rw [VEnv.addDefEqs_projections, hproj] at hp
      exact hp
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
      have hfQ : env0.constants ``Quot = none := by
        unfold VEnv.addConst at ha; split at ha <;> cases ha; assumption
      have hfM : env0.constants ``Quot.mk = none := by
        have hb' : a.constants ``Quot.mk = none := by
          unfold VEnv.addConst at hb; split at hb <;> cases hb; assumption
        cases h' : env0.constants ``Quot.mk with
        | none => rfl
        | some ci => rw [(VEnv.addConst_le ha).constants h'] at hb'; cases hb'
      refine ⟨⟨_, VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
          ((VEnv.addConst_le hc).constants ((VEnv.addConst_le hb).constants
            (VEnv.addConst_self ha))))⟩,
        ⟨_, VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
          ((VEnv.addConst_le hc).constants (VEnv.addConst_self hb)))⟩, fun S info hp => ?_⟩
      have hp0 : env0.projections S info := by
        have h : (e.addDefEq quotDefEq).projections = env0.projections :=
          (VEnv.addConst_projections he).trans <| (VEnv.addConst_projections hc).trans <|
            (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)
        exact h ▸ hp
      obtain ⟨_, hS⟩ := hord0.projectionConstant hp0
      have hC := hord0.projectionConstructor hp0
      refine ⟨fun h => ?_, fun h => ?_⟩
      · subst h; rw [hfQ] at hS; cases hS
      · rw [h, hfM] at hC; cases hC
    | induct installed =>
      cases installed with
      | @intro block _ _ compiled _ _ hinst =>
        have hinst' := hinst
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hinst'
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinst'
        have hle : env0 ≤ recursors.addDefEqRules block.rules :=
          (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
            VEnv.addEliminators_addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le
        rw [VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hq
        rcases hq with hm | hq
        · exfalso
          obtain ⟨recursor, hrec, ls, hhead⟩ := compiled.equation_head_owned _ hm
          rw [quotDefEq_head] at hhead
          have hn := (VExpr.const.inj hhead).1
          have hlook := VInductBlock.install_recursor_lookup hinst hrec
          rw [← hn, hlift] at hlook
          obtain ⟨_, _, _, _, _, _, C, _⟩ := compiled.exists_compilation
          obtain ⟨f, x, hfx⟩ := InductiveSignature.CompilationData.recursor_forallResult_app C hrec
          have := congrArg VConstant.type (Option.some.inj hlook)
          exact quotLiftConst_forallResult_not_app f x (by rw [this]; exact hfx)
        obtain ⟨h1, h2, h3⟩ := ih0 hle hq
        refine ⟨h1, h2, fun S info hp => ?_⟩
        rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hr,
          VEnv.addProjections_iff, VEnv.addEliminators_projections, VEnv.addConstVals_projections hc,
          VEnv.addConstVals_projections ht] at hp
        rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hp
        · obtain ⟨hfS, hfC⟩ := entry_fresh compiled.types_eq compiled.ctors_eq
            compiled.projections ht hc hentry
          obtain ⟨hQ, hM, -⟩ := ih hq (by
            obtain ⟨ci, hci⟩ := quotLift_declared hord0 hq
            have h1 := hle.constants hci
            rw [hlift] at h1
            cases h1; exact hci)
          obtain ⟨_, hQ⟩ := hQ
          obtain ⟨_, hM⟩ := hM
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [h, hQ] at hfS; cases hfS
          · rw [h, hM] at hfC; cases hfC
        · exact h3 S info hp
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hq hlift
    obtain ⟨h1, h2, h3⟩ := ih hq hlift
    exact ⟨h1, h2, fun S info hp => h3 S info hp⟩
  | @inductProjections _ _ base envTypes envCtors decl block hbase _ _ _ _ _ _ _ _ htypesSource
      hctorsSource hprojections htypes hctors ihBase ihCtors =>
    intro hq hlift
    simp only [VEnv.addProjections_defeqs, VEnv.addProjections_constants] at hq hlift
    obtain ⟨h1, h2, h3⟩ := ihCtors hq hlift
    simp only [VEnv.addEliminators_defeqs, VEnv.addEliminators_constants] at hq hlift
    refine ⟨by simpa using h1, by simpa using h2, fun S info hp => ?_⟩
    rw [VEnv.addProjections_iff] at hp
    rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hp
    · have hord : base.Ordered := (show base.WF from ⟨_, hbase⟩).ordered
      have hble : base ≤ envCtors := (VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)
      have hqb : base.defeqs quotDefEq := by
        rwa [VEnv.addConstVals_defeqs hctors, VEnv.addConstVals_defeqs htypes] at hq
      obtain ⟨ci, hci⟩ := quotLift_declared hord hqb
      have hl := hble.constants hci
      rw [hlift] at hl
      cases hl
      obtain ⟨⟨_, hQ⟩, ⟨_, hM⟩, -⟩ := ihBase hqb hci
      obtain ⟨hfS, hfC⟩ := entry_fresh htypesSource hctorsSource hprojections htypes hctors hentry
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [h, hQ] at hfS; cases hfS
      · rw [h, hM] at hfC; cases hfC
    · exact h3 S info hp

/-- **The quotient is not projection-registered.** -/
theorem WF.quot_not_projection (henv : env.WF) (hq : env.defeqs quotDefEq)
    (hlift : env.constants ``Quot.lift = some quotLiftConst) :
    (∀ info, ¬ env.projections ``Quot info) ∧ ¬ Model.IsProjCtor env ``Quot.mk := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨-, -, h⟩ := H.quot_projections hq hlift
  exact ⟨fun info hp => (h _ info hp).1 rfl, fun ⟨S, info, hp, hn⟩ => (h S info hp).2 hn⟩

/-! ## Recursor rules whose owner family is projection-registered -/

end VEnv
end Lean4Lean
