import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Coverage

/-! # Delta rules of a well-formed environment

`VEnv.WF.deltaRules`: every installed rule whose left-hand side is a bare constant is the
delta rule of a definition: its levels are the rule's level parameters, the constant is
declared with the rule's level count and type, and no other rule (of any shape) is headed
by that constant. Proved by induction on the declaration history: every new rule is headed
by a constant installed by the same declaration, hence absent before
(`HasType.head_const_lookup` places the heads of old rules among old constants), and
restored recursor equations are never bare constants
(`CompilationData.equation_not_const`). -/

namespace Lean4Lean
open InductiveSignature

namespace VEnv

/-- The delta rules of an environment: rules with a bare-constant left-hand side. -/
structure DeltaRules (env : VEnv) : Prop where
  const : ∀ df, env.defeqs df → ∀ n ls, df.lhs = .const n ls →
    ls = VLevel.params df.uvars ∧ env.constants n = some ⟨df.uvars, df.type⟩
  excl : ∀ df df', env.defeqs df → env.defeqs df' → ∀ n ls ls', df.lhs = .const n ls →
    df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df

theorem DeltaRules.extend {env env' : VEnv} {new : List VDefEq} (H : env.DeltaRules)
    (hord : env.Ordered)
    (hle : ∀ n ci, env.constants n = some ci → env'.constants n = some ci)
    (hdefeqs : ∀ df, env'.defeqs df ↔ df ∈ new ∨ env.defeqs df)
    (hfresh : ∀ df ∈ new, ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      env.constants n = none)
    (hconst : ∀ df ∈ new, ∀ n ls, df.lhs = .const n ls →
      ls = VLevel.params df.uvars ∧ env'.constants n = some ⟨df.uvars, df.type⟩)
    (hexcl : ∀ df ∈ new, ∀ df' ∈ new, ∀ n ls ls', df.lhs = .const n ls →
      df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df) :
    env'.DeltaRules := by
  have oldHead : ∀ df, env.defeqs df → ∀ n ls,
      df.lhs.stripLams.getAppFnArgs.1 = .const n ls → ∃ ci, env.constants n = some ci :=
    fun df hdf n ls h => (hord.defEqWF hdf).1.head_const_lookup hord (Γ := []) ⟨⟩ h
  have headOf : ∀ (df : VDefEq) n ls, df.lhs = .const n ls →
      df.lhs.stripLams.getAppFnArgs.1 = .const n ls := fun df n ls h => by rw [h]; rfl
  refine ⟨fun df hdf n ls h => ?_, fun df df' hdf hdf' n ls ls' h h' => ?_⟩
  · rcases (hdefeqs df).1 hdf with hm | ho
    · exact hconst df hm n ls h
    · have ⟨h1, h2⟩ := H.const df ho n ls h
      exact ⟨h1, hle _ _ h2⟩
  · rcases (hdefeqs df).1 hdf with hm | ho <;> rcases (hdefeqs df').1 hdf' with hm' | ho'
    · exact hexcl df hm df' hm' n ls ls' h h'
    · obtain ⟨_, hc⟩ := oldHead df' ho' n ls' h'
      rw [hfresh df hm n ls (headOf df n ls h)] at hc; cases hc
    · have hc := (H.const df ho n ls h).2
      rw [hfresh df' hm' n ls' h'] at hc; cases hc
    · exact H.excl df df' ho ho' n ls ls' h h'

theorem inj_on_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: l, hnd, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (e ▸ List.mem_map_of_mem hb) hnd.1
    · exact absurd (e.symm ▸ List.mem_map_of_mem ha) hnd.1
    · exact inj_on_of_nodup_map hnd.2 ha hb e

theorem quotDefEq_lhs_ne_const : quotDefEq.lhs ≠ .const n ls := by
  intro h; cases h

theorem defeqs_addDefEq {env : VEnv} : (env.addDefEq d).defeqs df ↔ df ∈ [d] ∨ env.defeqs df := by
  simp [VEnv.addDefEq]

theorem WF'.deltaRules {env : VEnv} (H : env.WF' ds) : env.DeltaRules := by
  induction H with
  | empty => exact ⟨nofun, nofun⟩
  | @decl d env' ds env hdecl hbase ih =>
    have hord := (show env.WF from ⟨ds, hbase⟩).ordered
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      refine ih.extend hord (new := []) (fun _ _ h => (VEnv.addConst_le hadd).constants h)
        (fun df => by rw [VEnv.addConst_defeqs hadd]; simp) nofun nofun nofun
    | «example» => exact ih
    | @«def» env₁ _ ci _ hadd =>
      have hnone : env.constants ci.name = none := by
        unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
      refine ih.extend hord (new := [ci.toDefEq])
        (fun _ _ h => (VEnv.addConst_le hadd).constants h)
        (fun df => by rw [defeqs_addDefEq, VEnv.addConst_defeqs hadd]) ?_ ?_ ?_
      · intro df hm n ls h
        simp only [List.mem_singleton] at hm; subst hm
        cases h; exact hnone
      · intro df hm n ls h
        simp only [List.mem_singleton] at hm; subst hm
        cases h
        refine ⟨rfl, ?_⟩
        show env₁.constants ci.name = some ⟨ci.uvars, ci.type⟩
        exact VEnv.addConst_self hadd
      · intro df hm df' hm' _ _ _ _ _
        simp only [List.mem_singleton] at hm hm'; subst hm hm'; rfl
    | @mutualDef cis env₁ _ _ hadd _ =>
      rw [VEnv.addConsts_eq_addConstVals] at hadd
      rw [VEnv.addDefEqs_eq_addDefEqRules]
      refine ih.extend hord (new := cis.map (·.toDefEq))
        (fun _ _ h => by
          rw [VEnv.addDefEqRules_constants]; exact (addConstVals_le hadd).constants h)
        (fun df => by rw [VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hadd]) ?_ ?_ ?_
      · intro df hm n ls h
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
        cases h
        exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci)
      · intro df hm n ls h
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
        cases h
        refine ⟨rfl, ?_⟩
        rw [VEnv.addDefEqRules_constants]
        exact addConstVals_get hadd (ci := ci.toVConstVal) (List.mem_map_of_mem hci)
      · intro df hm df' hm' n ls ls' h h'
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
        obtain ⟨cj, hcj, rfl⟩ := List.mem_map.mp hm'
        have e1 : ci.name = n := (VExpr.const.inj h).1
        have e2 : cj.name = n := (VExpr.const.inj (show VExpr.const cj.name _ = _ from h')).1
        have hnd := addConstVals_names_nodup hadd
        rw [List.map_map] at hnd
        have : cj = ci := inj_on_of_nodup_map hnd hcj hci (e2.trans e1.symm)
        subst this; rfl
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
      have hle : ∀ n ci, env.constants n = some ci → e.constants n = some ci := fun _ _ h =>
        (VEnv.addConst_le he).constants <| (VEnv.addConst_le hc).constants <|
          (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h
      refine ih.extend hord (new := [quotDefEq]) hle
        (fun df => by
          rw [defeqs_addDefEq, VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha]) ?_ ?_ ?_
      · intro df hm n ls h
        simp only [List.mem_singleton] at hm; subst hm
        have hn : n = ``Quot.lift := by cases h; rfl
        subst hn
        have hnone : b.constants ``Quot.lift = none := by
          unfold VEnv.addConst at hc; split at hc <;> cases hc; assumption
        cases h' : env.constants ``Quot.lift with
        | none => rfl
        | some ci =>
          have := (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h'
          rw [this] at hnone; cases hnone
      · intro df hm n ls h
        simp only [List.mem_singleton] at hm; subst hm
        exact absurd h quotDefEq_lhs_ne_const
      · intro df hm _ _ n ls _ h
        simp only [List.mem_singleton] at hm; subst hm
        exact absurd h quotDefEq_lhs_ne_const
    | induct installed =>
      cases installed with
      | @intro block _ _ compiled _ _ installed =>
        obtain ⟨base, expanded, signature, generated, auxiliaries, _, compilation, _⟩ :=
          compiled.exists_compilation
        have hrules := compilation.equations
        have howned := compiled.equation_head_owned
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at installed
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := installed
        have notConst : ∀ df ∈ block.rules, ∀ n ls, df.lhs ≠ .const n ls := by
          intro df member
          obtain ⟨source, hsource, hrestore⟩ :=
            Lean4Lean.List.Forall₂.forall_exists_r (List.mapM_eq_some.mp hrules) _ member
          obtain ⟨index, _, rfl⟩ := List.mem_map.mp hsource
          exact compilation.equation_not_const index hrestore
        refine ih.extend hord (new := block.rules)
          (fun _ _ h => by
            rw [VEnv.addDefEqRules_constants]
            exact (addConstVals_le hr).constants (by
              rw [VEnv.addProjections_constants, VEnv.addEliminators_constants]
              exact (addConstVals_le hc).constants ((addConstVals_le ht).constants h)))
          (fun df => by
            rw [VEnv.addDefEqRules_defeqs_iff_mem_or, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs, VEnv.addEliminators_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht]) ?_
          (fun df hm n ls h => absurd h (notConst df hm n ls))
          (fun df hm _ _ n ls _ h => absurd h (notConst df hm n ls))
        intro df hm n ls h
        obtain ⟨recursor, hrec, ls', hhead⟩ := howned df hm
        have hn : recursor.name = n := (VExpr.const.inj (hhead.symm.trans h)).1
        subst hn
        have hfresh := addConstVals_names_fresh hr recursor hrec
        cases h' : env.constants recursor.name with
        | none => rfl
        | some ci =>
          have := (addConstVals_le hc).constants ((addConstVals_le ht).constants h')
          simp only [VEnv.addProjections_constants, VEnv.addEliminators_constants] at hfresh
          rw [this] at hfresh; cases hfresh
  | inductEliminators _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨fun df hdf n ls h => ih.const df hdf n ls h,
      fun df df' hdf hdf' => ih.excl df df' hdf hdf'⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨fun df hdf n ls h => by simpa using ih.const df (by simpa using hdf) n ls h,
      fun df df' hdf hdf' => ih.excl df df' (by simpa using hdf) (by simpa using hdf')⟩

theorem WF.deltaRules {env : VEnv} (H : env.WF) : env.DeltaRules :=
  let ⟨_, H⟩ := H; H.deltaRules

end VEnv
end Lean4Lean
