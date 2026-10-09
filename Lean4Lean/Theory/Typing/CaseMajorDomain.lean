import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Inductive.RestorationHead

/-! The major premise of a typed abstract case application has the restored
family type, headed by the installed family constant, determined by its generated eliminator
telescope. -/

set_option maxHeartbeats 1000000

namespace Lean4Lean.InductiveSignature

private theorem restoration_forall_prefix {r : Restoration} {domains : List VExpr}
    (h : r.expr (VExpr.wrapForalls domains body) = some output) :
    ∃ domains' body', domains'.length = domains.length ∧
      r.expr body = some body' ∧ output = VExpr.wrapForalls domains' body' := by
  induction domains generalizing output with
  | nil => exact ⟨[], output, rfl, h, rfl⟩
  | cons d ds ih =>
    change (do let d' ← r.expr d; let b' ← r.expr (VExpr.wrapForalls ds body)
               pure (.forallE d' b')) = some output at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨d', hd, b', hb, heq⟩ := h
    obtain ⟨ds', body', hlen, hb', rfl⟩ := ih hb
    exact ⟨d' :: ds', body', by simp [hlen], hb', Option.some.inj heq.symm⟩

namespace CaseSchema

/-- The last binder of the generated case telescope is exactly its restored
family application. The preceding arity is fixed by the declaration. -/
theorem genericType_major {type : VExpr} {schema : CaseSchema}
    {owner : Fin schema.signature.families.size}
    (H : schema.genericType owner = some type) :
    ∃ (domains familyArgs : List VExpr) (body : VExpr),
      domains.length = schema.signature.params.length + 1 +
        (schema.view owner).constructors.size + schema.signature.families[owner].indices.length ∧
      type = VExpr.wrapForalls (domains ++ [VExpr.mkApps
        (.const (schema.restoration.headName schema.signature.families[owner].name)
          (schema.restoration.headLevels schema.signature.families[owner].name schema.genericLevels))
        familyArgs]) body := by
  let g := schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)
  let family := (schema.view owner).families[schema.viewOwner owner]
  let extra := (schema.view owner).families.size + (schema.view owner).constructors.size
  let indices := insertBinders (family.indices.map (·.instL g.levels)) extra
  let major := g.familyApp (schema.viewOwner owner)
    (vars (schema.view owner).params.length (extra + indices.length)) (vars indices.length 0)
  let motive := VExpr.bvar
    (indices.length + 1 + (schema.view owner).constructors.size +
      ((schema.view owner).families.size - 1 - (schema.viewOwner owner).val))
  let rawDomains := g.params ++ g.motives ++ g.minors ++ indices
  change schema.restoration.expr (VExpr.wrapForalls (rawDomains ++ [major])
    (VExpr.mkApps motive (vars indices.length 1 ++ [.bvar 0]))) = some type at H
  rw [VExpr.wrapForalls_append] at H
  obtain ⟨domains, tailType, hlen, htail, htype⟩ := restoration_forall_prefix H
  change (do let major' ← schema.restoration.expr major
             let body' ← schema.restoration.expr (VExpr.mkApps motive (vars indices.length 1 ++ [.bvar 0]))
             pure (.forallE major' body')) = some tailType at htail
  simp only [bind, Option.bind_eq_some_iff] at htail
  obtain ⟨major', hmajor, body', hbody, heq⟩ := htail
  have hmajorShape : ∃ args, major' = VExpr.mkApps
      (.const (schema.restoration.headName schema.signature.families[owner].name)
        (schema.restoration.headLevels schema.signature.families[owner].name schema.genericLevels)) args := by
    exact schema.restoration.const_mkApps_exact hmajor
  obtain ⟨familyArgs, rfl⟩ := hmajorShape
  refine ⟨domains, familyArgs, body', ?_, ?_⟩
  · rw [hlen]
    simp [rawDomains, g, Instance.params, Instance.motives, Instance.minors,
      indices, insertBinders, family, viewOwner, view]
    omega
  · rw [htype, ← Option.some.inj heq, VExpr.wrapForalls_append]
    rfl

end CaseSchema
end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
open Lean4Lean
variable {env : VEnv} {U : Nat}
open VExpr InductiveSignature InductiveSignature.CaseSchema

private theorem caseMajor_head_typed {type : VExpr} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (VExpr.mkApps fn args) type) :
    ∃ headType, env.HasType U Γ fn headType := by
  induction args generalizing fn with
  | nil => exact ⟨_, H⟩
  | cons a args ih =>
    obtain ⟨_, h⟩ := ih H
    obtain ⟨_, _, hf, _⟩ := h.app_inv henv hΓ
    exact ⟨_, hf⟩

/-- Typing a saturated abstract eliminator application fixes the major
premise's installed family head and its restored universe specialization. -/
theorem HasType.caseMajor_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {packed : List VLevel} {args : List VExpr} {major : VExpr}
    (hlookup : env.eliminators block schema)
    (hlen : args.length = caseMajorArity schema owner)
    (H : VExpr.WF env U Γ (VExpr.mkApps (.elim block owner.val packed) (args ++ [major]))) :
    ∃ familyArgs, env.HasType U Γ major (VExpr.mkApps
      (.const (schema.restoration.headName schema.signature.families[owner].name)
        ((schema.restoration.headLevels schema.signature.families[owner].name schema.genericLevels).map
          (·.inst packed))) familyArgs) := by
  obtain ⟨_, ht⟩ := H
  obtain ⟨_, hhead⟩ := caseMajor_head_typed henv hΓ ht
  obtain ⟨schema', owner', type, target, levels, typeLevel, hslot, hpacked,
    hlookup', htype, hclosed, hpermission, hsortWF, hsort⟩ := hhead.elim_inv henv.ordered hΓ
  cases henv.eliminators_unique hlookup hlookup'
  have howner : owner = owner' := Fin.ext hslot
  cases howner
  cases hpacked
  simp only [caseMajorArity] at hlen
  have hcanonical : env.HasType U Γ (.elim block owner.val (target :: levels))
      (type.instL (target :: levels)) :=
    .elimDF hlookup htype hclosed hpermission hpermission.packedWF
      (by
        suffices ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls from this _
        intro ls
        induction ls with
        | nil => exact .nil
        | cons l ls ih => exact .cons rfl ih) hsort
  obtain ⟨domains, familyArgs, body, hdomains, hshape⟩ := CaseSchema.genericType_major htype
  rw [hshape, VExpr.instL_wrapForalls] at hcanonical
  have hargs := (HasType.mkApps_wrapForalls henv hΓ hcanonical ⟨_, ht⟩
    (by simp only [List.length_map, List.length_append, List.length_singleton];
        omega)).1
  have hmajor := hargs args.length (by simp) (by
    simp only [List.length_map, List.length_append, List.length_singleton]
    omega)
  have hd : args.length = domains.length := by
    omega
  rw [List.getElem_append_right (Nat.le_refl _), List.take_left] at hmajor
  simp only [Nat.sub_self, List.getElem_singleton, List.getElem_map] at hmajor
  simp only [hd, List.getElem_append_right (Nat.le_refl _)] at hmajor
  simp only [Nat.sub_self, List.getElem_singleton, VExpr.instL_mkApps, VExpr.instL,
    VExpr.instOuter_mkApps, VExpr.instOuter_const] at hmajor
  exact ⟨_, hmajor⟩

end Lean4Lean.VEnv
