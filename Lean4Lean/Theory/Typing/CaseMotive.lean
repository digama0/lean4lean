import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.SignatureArity

/-! The result universe of a declaration-generated case equation is fixed
by its actual motive binder, including after restoration. -/

namespace Lean4Lean.InductiveSignature

private theorem restoration_telescope_trace {r : Restoration} {domains : List VExpr}
    {lhs rhs type lhs' rhs' type' : VExpr}
    (hl : r.expr (VExpr.wrapLams domains lhs) = some lhs')
    (hr : r.expr (VExpr.wrapLams domains rhs) = some rhs')
    (ht : r.expr (VExpr.wrapForalls domains type) = some type') :
    ∃ domains' l r' t,
      List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧
      r.expr lhs = some l ∧ r.expr rhs = some r' ∧ r.expr type = some t ∧
      lhs' = VExpr.wrapLams domains' l ∧ rhs' = VExpr.wrapLams domains' r' ∧
      type' = VExpr.wrapForalls domains' t := by
  induction domains generalizing lhs' rhs' type' with
  | nil => exact ⟨[], lhs', rhs', type', .nil, hl, hr, ht, rfl, rfl, rfl⟩
  | cons d ds ih =>
    obtain ⟨dl, l, hdl, hlBody, rfl⟩ := Restoration.expr_lam_parts hl
    obtain ⟨dr, rr, hdr, hrBody, rfl⟩ := Restoration.expr_lam_parts hr
    have hd : dr = dl := Option.some.inj (hdr.symm.trans hdl)
    subst dr
    change (do let d' ← r.expr d; let t' ← r.expr (VExpr.wrapForalls ds type)
               pure (.forallE d' t')) = some type' at ht
    simp only [bind, Option.bind_eq_some_iff] at ht
    obtain ⟨dt, hdt, t, ht, heq⟩ := ht
    have hd : dt = dl := Option.some.inj (hdt.symm.trans hdl)
    subst dt
    cases heq
    obtain ⟨ds', l', r', t', hds, hl', hr', ht', rfl, rfl, rfl⟩ := ih hlBody hrBody ht
    exact ⟨dl :: ds', l', r', t', .cons hdl hds, hl', hr', ht', rfl, rfl, rfl⟩

theorem Restoration.forall_sort_shape {r : Restoration} {domains : List VExpr}
    (h : r.expr (VExpr.wrapForalls domains (.sort level)) = some output) :
    ∃ domains', output = VExpr.wrapForalls domains' (.sort level) := by
  induction domains generalizing output with
  | nil =>
    have he : output = .sort level := by simpa [VExpr.wrapForalls, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using h.symm
    exact ⟨[], he⟩
  | cons d ds ih =>
    change (do let d' ← r.expr d; let t' ← r.expr (VExpr.wrapForalls ds (.sort level))
               pure (.forallE d' t')) = some output at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨d', hd, t', ht, he⟩ := h
    obtain ⟨ds', rfl⟩ := ih ht
    exact ⟨d' :: ds', Option.some.inj he.symm⟩

namespace CaseSchema

/-- The type of a generated case equation applies the motive stored in its
own binder telescope; that motive ends in the generic target universe. -/
theorem Generates.motive_shape {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule}
    (H : schema.Generates block owner rule) :
    ∃ (position : Nat) (hposition : position < rule.body.domains.length)
      (motiveDomains typeArguments : List VExpr),
      rule.body.domains[position] = VExpr.wrapForalls motiveDomains (.sort (.param 0)) ∧
      rule.body.type = VExpr.mkApps
        (.bvar (rule.body.domains.length - 1 - position)) typeArguments := by
  obtain ⟨rules, hg, hm, he⟩ := H
  obtain ⟨index, hrestore⟩ := equation_of_mem hg hm
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨ds, lhs, rhs, type, hds, hl', hr', ht', hel, her, het⟩ :=
    restoration_telescope_trace hl hr ht
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let ctor := (schema.view owner).constructors[index]
  have htype : ∃ args, type = VExpr.mkApps
      (.bvar (ctor.fields.length + (schema.view owner).constructors.size)) args := by
    change schema.restoration.expr (VExpr.mkApps _ _) = some type at ht'
    change Restoration.expr.go schema.restoration (VExpr.mkApps _ _) [] = _ at ht'
    rw [restoration_mkApps] at ht'
    simp only [bind, Option.bind_eq_some_iff] at ht'
    obtain ⟨args, _, heq⟩ := ht'
    refine ⟨args, ?_⟩
    simp only [Restoration.expr.go, List.append_nil, Option.some.injEq,
      view_familyCount, Nat.sub_self, Nat.zero_sub, Nat.add_zero] at heq
    exact heq.symm
  have hhead := Restoration.go_head_elim
    (hhead := VExpr.getAppFnArgs_mkApps_head _ _) hl'
  have hb := extract_wrap (rhs := rhs) (type := type) hhead ds
  rw [← hel, ← her, ← het] at hb
  have hbody := Option.some.inj (hb.symm.trans (AppliedRule.extract_spec he).2.1)
  rw [← hbody]
  simp only
  have hlen : ds.length = schema.signature.params.length + 1 +
      (schema.view owner).constructors.size + ctor.fields.length := by
    have hh := (Lean4Lean.List.Forall₂.length_eq hds).symm
    simp only [Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList] at hh
    exact hh
  have hp : schema.signature.params.length < ds.length := by omega
  have hp' : schema.signature.params.length <
      (g.params ++ g.motives ++ g.minors ++ insertBinders
        (((schema.view owner).fieldTypes ctor).map (·.instL g.levels))
        ((schema.view owner).families.size + (schema.view owner).constructors.size)).length := by
    rw [Lean4Lean.List.Forall₂.length_eq hds]
    exact hp
  have hmotive := VEnv.case_forall₂_get (i := schema.signature.params.length) hds hp' hp
  have hsource : (g.params ++ g.motives ++ g.minors ++ insertBinders
        (((schema.view owner).fieldTypes ctor).map (·.instL g.levels))
        ((schema.view owner).families.size + (schema.view owner).constructors.size))[schema.signature.params.length] =
      g.motive schema.signature.families[owner] 0 := by
    simp [g, Instance.params, Instance.motives, CaseSchema.view]
  rw [hsource] at hmotive
  obtain ⟨motiveDomains, hmotive⟩ := Restoration.forall_sort_shape hmotive
  obtain ⟨args, hargs⟩ := htype
  refine ⟨schema.signature.params.length, hp, motiveDomains, args, hmotive, ?_⟩
  rw [hargs]
  congr 2
  omega

end CaseSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema

/-- The specialized type of a case equation has exactly its permitted target
universe. This is recovered from the generated motive binder, not assumed as
an additional schema certificate. -/
theorem CaseStep.result_sort (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule (target :: levels) arguments) :
    env.HasType U Γ (rule.type (target :: levels) arguments) (.sort target) := by
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    obtain ⟨position, hposition, motiveDomains, typeArguments, hmotive, hresult⟩ := hg.motive_shape
    obtain ⟨hlbody, hrbody, htype⟩ := hg.body_exact
    have htypeWF := hleft.isType henv.ordered hΓ
    rw [← htype, instL_wrapForalls] at htypeWF
    obtain ⟨hctx, resultLevel, hresultWF⟩ := IsType.wrapForalls_inv henv hΓ htypeWF
    let domains := rule.body.domains.map (instL (target :: levels))
    have hposition' : position < domains.length := by simpa [domains] using hposition
    have hvar : env.HasType U (domains.reverse ++ Γ)
        (.bvar (domains.length - 1 - position))
        (domains[position].liftN (domains.length - position)) :=
      .bvar (Lookup.reverse_append domains Γ position hposition')
    have hd : domains[position] =
        VExpr.wrapForalls (motiveDomains.map (instL (target :: levels))) (.sort target) := by
      simp only [domains, List.getElem_map, hmotive, instL_wrapForalls]
      rfl
    rw [hd] at hvar
    obtain ⟨motiveDomains', hmotive'⟩ := VExpr.liftN_wrapForalls_sort
      (motiveDomains.map (instL (target :: levels))) target (domains.length - position) 0
    rw [hmotive'] at hvar
    have hresultWF' : env.HasType U (domains.reverse ++ Γ)
        (VExpr.mkApps (.bvar (domains.length - 1 - position))
          (typeArguments.map (instL (target :: levels)))) (.sort resultLevel) := by
      simpa only [domains, List.length_map, hresult, instL_mkApps, instL] using hresultWF
    have hlength := HasType.mkApps_sort_arity henv hctx hvar hresultWF'
    have hsort := (HasType.mkApps_wrapForalls henv hctx hvar ⟨_, hresultWF'⟩ hlength).2
    have hsort' : env.HasType U (domains.reverse ++ Γ)
        (rule.body.type.instL (target :: levels)) (.sort target) := by
      simpa only [domains, List.length_map, hresult, instL_mkApps, instL, instOuter_sort] using hsort
    have hargs : ∀ i (hi : i < arguments.length) (hd : i < domains.length),
        env.HasType U Γ arguments[i] (domains[i].instOuter (arguments.take i)) := by
      intro i hi hd
      simp only [domains, List.getElem_map]
      simpa only [instantiateParams_eq_instOuter] using ha.2 i hi (by simpa [domains] using hd)
    have hfinal := IsDefEq.instOuter_telescope henv hsort'
      (by simpa [domains] using ha.1) hargs
    simpa only [AppliedRule.type, instantiateParams_eq_instOuter, instOuter_sort, HasType] using hfinal

/-- Both applied endpoints have the exact specialized generated type. -/
theorem CaseStep.endpoints_typed (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : CaseStep env U Γ rule levels arguments) :
    env.HasType U Γ (rule.lhs levels arguments) (rule.type levels arguments) ∧
      env.HasType U Γ (rule.rhs levels arguments) (rule.type levels arguments) := by
  cases H with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    obtain ⟨hlbody, hrbody, htype⟩ := hg.body_exact
    rw [← hlbody, ← htype, instL_wrapLams, instL_wrapForalls] at hleft
    rw [← hrbody, ← htype, instL_wrapLams, instL_wrapForalls] at hright
    let domains := rule.body.domains.map (instL (target :: levels))
    have hlength : arguments.length = domains.length := by simpa [domains] using ha.1
    have hargs : ∀ i (hi : i < arguments.length) (hd : i < domains.length),
        env.HasType U Γ arguments[i] (domains[i].instOuter (arguments.take i)) := by
      intro i hi hd
      simp only [domains, List.getElem_map]
      simpa only [instantiateParams_eq_instOuter] using ha.2 i hi (by simpa [domains] using hd)
    have hl := (IsDefEq.mkApps_wrapLams henv hΓ hleft hlength hargs).hasType.2
    have hr := (IsDefEq.mkApps_wrapLams henv hΓ hright hlength hargs).hasType.2
    simpa only [AppliedRule.lhs, AppliedRule.rhs, AppliedRule.type,
      instantiateParams_eq_instOuter] using And.intro hl hr

/-- A case occurrence eliminating into Prop has a proposition as its actual
result type, even when the matched left template is checked by conversion. -/
theorem CaseRedex.result_prop_of_target_zero (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : CaseRedex env U Γ rule actual)
    (htarget : actual.levels.head?.getD .zero ≈ .zero) :
    ∃ resultType, env.HasType U Γ resultType (.sort .zero) ∧
      env.HasType U Γ actual.expr resultType := by
  have Hsaved := H
  have hsource := H.source
  generalize hpacked : actual.levels = packed at hsource
  cases hsource with
  | @iota block levels target arguments schema owner rule hl hg hc hp hleft hright ha =>
    have Hsource : CaseStep env U Γ rule (target :: levels) (rule.capture actual) := by
      simpa only [hpacked] using Hsaved.source
    have hsort := Hsource.result_sort henv hΓ
    have hendpoint := Hsource.endpoints_typed henv hΓ
    have heq : target ≈ .zero := by simpa only [hpacked, List.head?_cons, Option.getD_some] using htarget
    refine ⟨rule.type (target :: levels) (rule.capture actual),
      (IsDefEq.sortDF hp.target_wf (by trivial) heq).defeq hsort, ?_⟩
    apply hendpoint.1.defeqU_l henv hΓ
    simpa only [hpacked] using Hsaved.guard.symm

end Lean4Lean.VEnv

/-! Recover the target universe from the motive supplied to a generated case
application. Only motive binders actually used by the application matter. -/

set_option maxHeartbeats 1000000

namespace Lean4Lean.InductiveSignature

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
variable {env : VEnv} {U : Nat}
open VExpr InductiveSignature InductiveSignature.CaseSchema

/-- Equal telescope types ending in sorts have the same final universe,
even when their domain lists have not been identified in advance. -/
theorem IsDefEqU.wrapForalls_sort_level (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (wrapForalls ds₁ (.sort u)) (wrapForalls ds₂ (.sort v))) :
    u ≈ v := by
  induction ds₁ generalizing Γ ds₂ with
  | nil =>
    cases ds₂ with
    | nil => exact H.sort_inv henv hΓ
    | cons d ds => exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ H)
  | cons d ds ih =>
    cases ds₂ with
    | nil => exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ H.symm)
    | cons d' ds' =>
      obtain ⟨⟨_, hd⟩, _, hb⟩ := H.forallE_inv henv hΓ
      have hctx : OnCtx (d :: Γ) (env.IsType U) := ⟨hΓ, _, hd.hasType.1⟩
      exact ih hctx ⟨_, hb⟩

end Lean4Lean.VEnv
