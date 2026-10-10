import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.PatShape
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! # Delta rules of a well-formed environment

`VEnv.WF.deltaRules`: every installed rule whose left-hand side is a bare constant is the
delta rule of a definition: its levels are the rule's level parameters, the constant is
declared with the rule's level count and type, and no other rule (of any shape) is headed
by that constant. Proved by induction on the declaration history: every new rule is headed
by a constant installed by the same declaration, hence absent before
(`HasType.head_const_lookup` places the heads of old rules among old constants); on the ι
pattern calculus an inductive declaration adds no definitional axiom at all
(`VEnv.addInduct_defeqs`), its recursor rules being registered patterns. -/

namespace Lean4Lean

namespace VEnv

/-- The delta rules of an environment: rules with a bare-constant left-hand side. -/
structure DeltaRules (env : VEnv) : Prop where
  const : ∀ df, env.defeqs df → ∀ n ls, df.lhs = .const n ls →
    ls = VLevel.params df.uvars ∧ env.constants n = some ⟨df.uvars, df.type⟩
  excl : ∀ df df', env.defeqs df → env.defeqs df' → ∀ n ls ls', df.lhs = .const n ls →
    df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df
  /-- No registered pattern is headed by a defined constant: a pattern's head is a recursor,
  fresh when its block is declared, and a definition's constant is fresh when it is declared. -/
  pats : ∀ df, env.defeqs df → ∀ n ls, df.lhs = .const n ls →
    ∀ (p : Pattern) (r : p.RHS × p.Check), env.pats p r → p.headConst ≠ n

theorem DeltaRules.extend {env env' : VEnv} {new : List VDefEq} (H : env.DeltaRules)
    (hord : env.OrderedStrong)
    (hle : ∀ n ci, env.constants n = some ci → env'.constants n = some ci)
    (hdefeqs : ∀ df, env'.defeqs df ↔ df ∈ new ∨ env.defeqs df)
    (hfresh : ∀ df ∈ new, ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      env.constants n = none)
    (hconst : ∀ df ∈ new, ∀ n ls, df.lhs = .const n ls →
      ls = VLevel.params df.uvars ∧ env'.constants n = some ⟨df.uvars, df.type⟩)
    (hexcl : ∀ df ∈ new, ∀ df' ∈ new, ∀ n ls ls', df.lhs = .const n ls →
      df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' → df' = df)
    (hpatsOld : ∀ (p : Pattern) (r : p.RHS × p.Check), env'.pats p r →
      env.pats p r ∨ env.constants p.headConst = none)
    (hpatsNew : ∀ df ∈ new, ∀ n ls, df.lhs = .const n ls →
      ∀ (p : Pattern) (r : p.RHS × p.Check), env'.pats p r → p.headConst ≠ n) :
    env'.DeltaRules := by
  have oldHead : ∀ df, env.defeqs df → ∀ n ls,
      df.lhs.stripLams.getAppFnArgs.1 = .const n ls → ∃ ci, env.constants n = some ci :=
    fun df hdf n ls h => (hord.ordered.defEqWF hdf).1.head_const_lookup hord (Γ := []) ⟨⟩ h
  have headOf : ∀ (df : VDefEq) n ls, df.lhs = .const n ls →
      df.lhs.stripLams.getAppFnArgs.1 = .const n ls := fun df n ls h => by rw [h]; rfl
  refine ⟨fun df hdf n ls h => ?_, fun df df' hdf hdf' n ls ls' h h' => ?_,
    fun df hdf n ls h p r hp hn => ?_⟩
  · rcases (hdefeqs df).1 hdf with hm | ho
    · exact hconst df hm n ls h
    · have ⟨h1, h2⟩ := H.const df ho n ls h
      exact ⟨h1, hle _ _ h2⟩
  rotate_left
  · rcases (hdefeqs df).1 hdf with hm | ho
    · exact hpatsNew df hm n ls h p r hp hn
    · rcases hpatsOld p r hp with hp' | hnone
      · exact H.pats df ho n ls h p r hp' hn
      · have := (H.const df ho n ls h).2
        rw [hn, this] at hnone; cases hnone
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
  | empty => exact ⟨nofun, nofun, nofun⟩
  | @decl d env' ds env hdecl hbase ih =>
    have hW : env.WF := ⟨ds, hbase⟩
    have hord := hW.orderedStrong
    -- a pattern of the environment is headed by a declared constant
    have hdecl' : ∀ (p : Pattern) (r : p.RHS × p.Check), env.pats p r →
        ∀ n, env.constants n = none → p.headConst ≠ n := fun p r hp n hn e => by
      obtain ⟨c, hc⟩ := hW.pat_head_declared hp
      rw [e, hn] at hc; cases hc
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      refine ih.extend hord (new := []) (fun _ _ h => (VEnv.addConst_le hadd).constants h)
        (fun df => by rw [VEnv.addConst_defeqs hadd]; simp) nofun nofun nofun
        (fun p r hp => .inl (by rwa [VEnv.addConst_pats hadd] at hp)) nofun
    | «example» => exact ih
    | @«def» env₁ _ ci _ hadd =>
      have hnone : env.constants ci.name = none := by
        unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
      refine ih.extend hord (new := [ci.toDefEq])
        (fun _ _ h => (VEnv.addConst_le hadd).constants h)
        (fun df => by rw [defeqs_addDefEq, VEnv.addConst_defeqs hadd]) ?_ ?_ ?_
        (fun p r hp => .inl (by rwa [VEnv.addDefEq_pats, VEnv.addConst_pats hadd] at hp))
        (fun df hm n ls h p r hp => by
          simp only [List.mem_singleton] at hm; subst hm
          cases h
          rw [VEnv.addDefEq_pats, VEnv.addConst_pats hadd] at hp
          exact hdecl' p r hp _ hnone)
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
        (fun p r hp => .inl (by
          rwa [VEnv.addDefEqRules_pats, VEnv.addConstVals_pats hadd] at hp))
        (fun df hm n ls h p r hp => by
          obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
          cases h
          rw [VEnv.addDefEqRules_pats, VEnv.addConstVals_pats hadd] at hp
          exact hdecl' p r hp _
            (addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci)))
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
        (fun p r hp => .inl (by
          rwa [VEnv.addDefEq_pats, VEnv.addConst_pats he, VEnv.addConst_pats hc,
            VEnv.addConst_pats hb, VEnv.addConst_pats ha] at hp))
        (fun df hm n ls h => by
          simp only [List.mem_singleton] at hm; subst hm
          exact absurd h quotDefEq_lhs_ne_const)
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
    | induct _ hadd =>
      refine ih.extend hord (new := []) (fun _ _ h => (VEnv.addInduct_le hadd).constants h)
        (fun df => by rw [VEnv.addInduct_defeqs hadd]; simp) nofun nofun nofun
        (fun p r hp => ?_) nofun
      rcases VEnv.addInduct_pats_origin hadd hp with hold | ⟨rec, hrec, ru, hru, rfl⟩
      · exact .inl hold
      · exact .inr (by rw [SimplePattern.iota_headConst]; exact VEnv.addInduct_rec_fresh hadd hrec)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨fun df hdf n ls h => by simpa using ih.const df (by simpa using hdf) n ls h,
      fun df df' hdf hdf' => ih.excl df df' (by simpa using hdf) (by simpa using hdf'),
      fun df hdf n ls h p r hp => ih.pats df (by simpa using hdf) n ls h p r (by simpa using hp)⟩

theorem WF.deltaRules {env : VEnv} (H : env.WF) : env.DeltaRules :=
  let ⟨_, H⟩ := H; H.deltaRules

end VEnv
end Lean4Lean
