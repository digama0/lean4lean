import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CaseRuleSound
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RestoredRecursorRule
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjMajorWF

/-! # Validity of generic case equations

`ElimValid.of_certified`: a generic case equation of a registered certified schema is valid in
the model of a well-formed environment, given `FamSort` for the restored family of its owner.
It is an instance of `sound_pat_elim` (never-zero source sort: mode C is contradictory) or of
`sound_pat_elim_empty` (zero target: the right-hand side has no observations), with the
syntactic facts of the restored abstract equations of the owner's view. -/

namespace Lean4Lean
namespace InductiveSignature
namespace CaseSchema

/-- A constructor of the owner's view is the case form of a constructor of the owner. -/
theorem view_ctor (schema : CaseSchema) (owner : Fin schema.signature.families.size)
    (j : Fin (schema.view owner).constructors.size) :
    ∃ i : Fin schema.signature.constructors.size, schema.signature.constructors[i].owner = owner ∧
      (schema.view owner).constructors[j] = schema.caseConstructor schema.signature.constructors[i] := by
  have hj : (schema.view owner).constructors[j] ∈ (schema.view owner).constructors.toList :=
    Array.mem_toList_iff.2 (Array.getElem_mem j.isLt)
  simp only [view, List.toList_toArray] at hj
  obtain ⟨ctor, hctor, hc⟩ := List.mem_filterMap.1 hj
  split at hc
  · rename_i ho
    injection hc with hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hctor
    refine ⟨⟨i, by simpa using hi⟩, by simpa using ho, ?_⟩
    have : (schema.view owner).constructors[j] = schema.caseConstructor
        schema.signature.constructors.toList[i] := hc.symm
    simpa using this
  · cases hc

end CaseSchema
end InductiveSignature

namespace VEnv
namespace Model
open InductiveSignature
variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-- The schema data of an eliminator head of a semantically typed spine. -/
theorem HTS.elim_head : ∀ {Γ e T}, HTS env U Δ Γ e T → ∀ {b o ls args},
    e = .mkApps (.elim b o ls) args →
    ∃ (schema : CaseSchema) (owner : Fin schema.signature.families.size) (type : VExpr),
      env.eliminators b schema ∧ owner.val = o ∧ schema.genericType owner = some type := by
  intro Γ e T H
  induction H with
  | bvar => intro b o ls args he; exact absurd he.symm mkApps_elim_ne_bvar
  | other _ h' => intro b o ls args he; exact absurd he (h' _ _ _ _)
  | lam => intro b o ls args he; exact absurd he.symm mkApps_elim_ne_lam
  | forallE => intro b o ls args he; exact absurd he.symm mkApps_elim_ne_forallE
  | const | proj =>
    intro b o ls args he
    rcases mkApps_inv he with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | elim hb ht =>
    intro b o ls args he
    rcases mkApps_inv he with ⟨_, h⟩ | ⟨_, _, _, h⟩
    · cases h; exact ⟨_, _, _, hb, rfl, ht⟩
    · cases h
  | app _ _ _ _ _ _ ihf =>
    intro b o ls args he
    rcases mkApps_inv he with ⟨_, h⟩ | ⟨as, a, rfl, h⟩
    · cases h
    · injection h with hf; exact ihf hf
  | conv _ _ ih => intro b o ls args he; exact ih he

theorem HTS.wrapLams_hts : ∀ {ds : List VExpr} {Γ b P},
    HTS env U Δ Γ (.wrapLams ds b) P → ∃ B, HTS env U Δ (ds.reverse ++ Γ) b B
  | [], _, _, _, h => ⟨_, h⟩
  | A :: ds, Γ, b, P, H => by
    obtain ⟨B, -, -, -, -, hb, -⟩ := H.lam_inv rfl
    obtain ⟨B', h⟩ := HTS.wrapLams_hts hb
    exact ⟨B', by simpa [List.reverse_cons, List.append_assoc] using h⟩

theorem case_ctorFam {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {base : VEnv} {source expanded : VInductDecl} {block : VInductBlock}
    {aux : List ContainerSpecialization} {i : Fin schema.signature.constructors.size}
    (C : CaseCompilationData base source expanded schema.signature aux block)
    (hfresh : RecursorNamesFresh base source expanded aux)
    (hprior : ContainersInstalled base aux)
    (hrr : schema.restoration = compilationRestoration source aux)
    (hio : schema.signature.constructors[i].owner = owner)
    (hctorsIn : ∀ value ∈ block.ctors, env.constants value.name = some value.toVConstant)
    (hbF : base ≤ env) :
    CtorFam env (schema.restoration.headName schema.signature.constructors[i].name)
      (schema.restoration.headName schema.signature.families[owner].name) := by
  subst hio
  rw [hrr]
  rcases C.ctor_cases hfresh hprior i with ⟨fc, hfc, hfcn, lsc, hfch⟩ | ⟨cc, hcc, lsc, hcch⟩
  · refine ⟨_, _, ?_, hfch⟩
    rw [← hfcn]; exact hctorsIn fc (by rw [C.ctors]; exact hfc)
  · exact ⟨_, _, hbF.constants hcc, hcch⟩

set_option maxHeartbeats 1000000 in
/-- **Validity of a generic case equation** of a registered certified schema. -/
theorem ElimValid.of_certified {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {b : Name} {rules : List VDefEq} {df : VDefEq} {L : VLevel}
    {base : VEnv} {source : VInductDecl} {block : VInductBlock}
    (henv : env.Ordered)
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hcert : schema.Certified base source block) (hb : env.eliminators b schema)
    (hrules : schema.genericEquations b owner = some rules) (hmem : df ∈ rules)
    (hctorsIn : ∀ value ∈ block.ctors, env.constants value.name = some value.toVConstant)
    (hbF : base ≤ env)
    (hIrig : env.Rigid (schema.restoration.headName schema.signature.families[owner].name))
    (hfs : FamSort env (schema.restoration.headName schema.signature.families[owner].name) L)
    (hpm : ∀ (i : Fin schema.signature.constructors.size) (e : Nat) (c : Name) (lsC : List VLevel)
      (ms : List VExpr) (fn : VExpr), schema.signature.constructors[i].owner = owner → 1 ≤ e →
      df.lhs.stripLams = .app fn (VExpr.mkApps (.const c lsC)
        (ms ++ vars schema.signature.constructors[i].fields.length 0)) →
      schema.restoration.expr (VExpr.mkApps
        (.const schema.signature.constructors[i].name schema.genericLevels)
        (vars schema.signature.params.length (e + schema.signature.constructors[i].fields.length) ++
          vars schema.signature.constructors[i].fields.length 0)) =
        some (VExpr.mkApps (.const c lsC) (ms ++ vars schema.signature.constructors[i].fields.length 0)) →
      ∃ L', ProjMajor env (schema.restoration.headName schema.signature.families[owner].name) c
          ms.length schema.signature.constructors[i].fields.length L' ∧
        ∀ levels target, levels.length = schema.signature.uvars →
          (schema.sourceLevel owner levels).IsNeverZero →
          ((L'.inst lsC).inst (target :: levels)).IsNeverZero)
    (hnzL : ∀ levels target, levels.length = schema.signature.uvars →
      (schema.sourceLevel owner levels).IsNeverZero →
      ((L.inst (schema.restoration.headLevels schema.signature.families[owner].name
        schema.genericLevels)).inst (target :: levels)).IsNeverZero) :
    ElimValid env owner df := by
  intro U Δ Γ levels target tl hΔ hrc hperm _ ihT hLd ihL hRd ihR
  have hnodup := hcert.constructor_names_nodup owner
  obtain ⟨expanded, aux, C, hprior, hrr, -, hfresh⟩ := hcert
  obtain ⟨j, hres⟩ := CaseSchema.equation_of_mem hrules hmem
  have hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ (schema.view owner).params.length := by
    intro head hhead
    rw [hrr] at hhead
    obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
    have hn := C.model.nparams.trans C.nparams
    simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hhead
    rcases hhead with rfl | ⟨ctor, _, rfl⟩ <;> exact Nat.le_of_eq hn.symm
  obtain ⟨ds', idx', lsC', ms', body', T', hds, hidx, hl, hr, ht, hT', -⟩ :=
    Instance.restored_equation_abstract _ j b owner.val hparams hres
  have h0 : ((schema.view owner).constructors[j]).owner.val = 0 := by
    have := ((schema.view owner).constructors[j]).owner.isLt
    have h1 : (schema.view owner).families.size = 1 := CaseSchema.view_familyCount ..
    omega
  rw [h0, Nat.add_zero] at hl
  obtain ⟨leadE, hleadE⟩ : ∃ l, vars ((schema.view owner).params.length +
      ((schema.view owner).families.size + (schema.view owner).constructors.size))
      ((schema.view owner).constructors[j]).fields.length ++ idx' = l := ⟨_, rfl⟩
  obtain ⟨cE, hcE⟩ : ∃ c, schema.restoration.headName ((schema.view owner).constructors[j]).name =
    c := ⟨_, rfl⟩
  have hl0 := hl
  rw [hleadE, hcE] at hl
  obtain ⟨i, hio, hvc⟩ := schema.view_ctor owner j
  have hvn : ((schema.view owner).constructors[j]).name = schema.signature.constructors[i].name := by
    rw [hvc]; rfl
  have hvi : ((schema.view owner).constructors[j]).indices =
      schema.signature.constructors[i].indices := by rw [hvc]; rfl
  have hvf : ((schema.view owner).constructors[j]).fields.length =
      schema.signature.constructors[i].fields.length := by
    rw [hvc]; simp [CaseSchema.caseConstructor, fieldTypes]
  have harity := C.model.constructorArity schema.signature.constructors[i] (by simp)
  have he := congrArg (fun o : Fin schema.signature.families.size =>
    schema.signature.families[o].indices.length) hio

  have hlsP : (VLevel.param 0 :: schema.genericLevels).map (·.inst (target :: levels)) =
      target :: levels := by
    simp only [List.map_cons, InductiveSignature.CaseSchema.genericLevels_inst hperm.length]; rfl
  obtain ⟨eL, eR⟩ := pat_instL_elim hl hr hlsP
  -- the head type
  have hLH := ihL.2
  rw [eL] at hLH
  obtain ⟨Bl, hBl⟩ := HTS.wrapLams_hts hLH
  obtain ⟨schema', owner', type, hb', hown, htype⟩ := HTS.elim_head hBl rfl
  cases hEu _ _ _ hb hb'
  cases Fin.ext hown
  have htype' := htype
  simp only [CaseSchema.genericType, CaseSchema.type] at htype'
  obtain ⟨RH, eRH⟩ := (schema.specialize owner schema.genericUvars schema.genericLevels
    (.param 0)).recursorType_eq_hi (schema.viewOwner owner)
  change schema.restoration.expr ((schema.specialize owner schema.genericUvars
    schema.genericLevels (.param 0)).recursor (schema.viewOwner owner)).type = some type at htype'
  rw [eRH] at htype'
  obtain ⟨dsH', RH', hdsH, -, eT⟩ := Restoration.expr_wrapForalls_parts htype'
  have hN : (schema.view owner).families[schema.viewOwner owner] =
      schema.signature.families[owner] := rfl
  obtain ⟨d', hd', hget⟩ := mapM_getElem? hdsH
    ((schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0)).recDoms_major (schema.viewOwner owner))
  obtain ⟨iargs, rfl⟩ := Restoration.const_mkApps_exact hd'
  rw [hN] at hget
  have hidxl := mapM_length hidx
  have hdsHl := mapM_length hdsH
  have hlen1 : ((schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0)).eqIndices j).length = schema.signature.families[owner].indices.length := by
    simp only [Instance.eqIndices, List.length_map, hvi]
    rw [harity]; exact he
  have hlenH : dsH'.length = (vars ((schema.view owner).params.length +
      ((schema.view owner).families.size + (schema.view owner).constructors.size))
      ((schema.view owner).constructors[j]).fields.length ++ idx').length + 1 := by
    rw [hdsHl, Instance.recDoms_length, hN]
    simp only [List.length_append, InductiveSignature.length_vars, hidxl, hlen1]
  have hkH : dsH'[(vars ((schema.view owner).params.length +
      ((schema.view owner).families.size + (schema.view owner).constructors.size))
      ((schema.view owner).constructors[j]).fields.length ++ idx').length]? =
      some (VExpr.mkApps (.const (schema.restoration.headName schema.signature.families[owner].name)
        (schema.restoration.headLevels schema.signature.families[owner].name
          schema.genericLevels)) iargs) := by
    have hget2 : dsH'[(schema.view owner).params.length + ((schema.view owner).families.size +
        (schema.view owner).constructors.size) + schema.signature.families[owner].indices.length]? =
        some (VExpr.mkApps (.const (schema.restoration.headName
          schema.signature.families[owner].name) (schema.restoration.headLevels
            schema.signature.families[owner].name schema.genericLevels)) iargs) := hget
    rw [← hget2]
    congr 1
    simp only [List.length_append, InductiveSignature.length_vars, hidxl, hlen1]
  -- the constructor
  obtain ⟨rule, hgen, hreq⟩ := CaseSchema.generates_of_genericEquation hrules hmem
  have hgen' := hgen
  obtain ⟨_, -, -, hparse⟩ := hgen'
  rw [hreq] at hparse
  have hcn := Instance.parsed_constructor _ j hres hparse
  have hcis : IsCtor env (schema.restoration.headName ((schema.view owner).constructors[j]).name) :=
    .inr ⟨b, schema, owner, rule, hb, hgen, hcn⟩
  have hcrig := hctor _ hcis
  have hcf : CtorFam env (schema.restoration.headName ((schema.view owner).constructors[j]).name)
      (schema.restoration.headName schema.signature.families[owner].name) := by
    rw [hvn]; exact case_ctorFam C hfresh hprior hrr hio hctorsIn hbF
  -- uniqueness per head and constructor
  rw [hleadE] at hlenH hkH
  rw [hcE] at hcis hcf hcrig
  have huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      df' ∈ rules →
      df'.lhs = .wrapLams doms' (.mkApps (.elim b owner.val lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = leadE.length ∧ (ctor' = cE → df' = df) := by
    intro df' doms' lsP' lead' ctor' lsC'' ms'' fs' body'' hm' hl' _
    obtain ⟨j', hres'⟩ := CaseSchema.equation_of_mem hrules hm'
    obtain ⟨_, idxj, _, _, _, _, -, hidxj, hlj, -, -, -, -⟩ :=
      Instance.restored_equation_abstract _ j' b owner.val hparams hres'
    have h0' : ((schema.view owner).constructors[j']).owner.val = 0 := by
      have := ((schema.view owner).constructors[j']).owner.isLt
      have h1 : (schema.view owner).families.size = 1 := CaseSchema.view_familyCount ..
      omega
    rw [h0', Nat.add_zero] at hlj
    obtain ⟨-, -, l2, a2⟩ := wrapLams_pat_inj_elim (hl'.symm.trans hlj)
    obtain ⟨c2, -, -⟩ := VExpr.mkApps_const_inj a2
    obtain ⟨i', hio', hvc'⟩ := schema.view_ctor owner j'
    have hvi' : ((schema.view owner).constructors[j']).indices =
        schema.signature.constructors[i'].indices := by rw [hvc']; rfl
    have harity' := C.model.constructorArity schema.signature.constructors[i'] (by simp)
    have he' := congrArg (fun o : Fin schema.signature.families.size =>
      schema.signature.families[o].indices.length) hio'
    refine ⟨?_, fun hc => ?_⟩
    · rw [l2, ← hleadE]
      simp only [List.length_append, InductiveSignature.length_vars, hidxl, mapM_length hidxj, Instance.eqIndices,
        List.length_map, hvi, hvi']
      simp only [Fin.getElem_fin] at harity harity' he he' ⊢
      omega
    · have hj : j' = j := by
        have e := c2.symm.trans (hc.trans hcE.symm)
        apply Fin.ext
        refine (List.getElem_inj (i := j'.val) (j := j.val)
          (h₀ := by rw [List.length_map, Array.length_toList]; exact j'.isLt)
          (h₁ := by rw [List.length_map, Array.length_toList]; exact j.isLt) hnodup).1 ?_
        simp only [List.getElem_map, Array.getElem_toList]
        exact e
      subst hj
      exact Option.some.inj (hres'.symm.trans hres)
  -- the projection facts of the major
  obtain ⟨L', hpmL, hnzL'⟩ : ∃ L', ProjMajor env
      (schema.restoration.headName schema.signature.families[owner].name) cE
      ms'.length (eqFs j).length L' ∧
      ∀ levels target, levels.length = schema.signature.uvars →
        (schema.sourceLevel owner levels).IsNeverZero →
        ((L'.inst lsC').inst (target :: levels)).IsNeverZero := by
    have hm : df.lhs.stripLams = .app (VExpr.mkApps (.elim b owner.val
        ((schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).targetLevel ::
          (schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).levels))
        leadE) (VExpr.mkApps (.const cE lsC') (ms' ++ (eqFs j).map .bvar)) := by
      rw [hl, VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]; rfl
    obtain ⟨i', hown', hview', e, he, hR⟩ := generic_major_at hres hm
    have hF : (eqFs j).length = schema.signature.constructors[i'].fields.length := by
      simp only [eqFs, List.length_reverse, List.length_range, hview']
      simp [CaseSchema.caseConstructor, fieldTypes]
    have hfs' : (eqFs j).map VExpr.bvar = vars schema.signature.constructors[i'].fields.length 0 := by
      rw [← hF]; simp [eqFs, vars]
    rw [hfs'] at hR hm
    obtain ⟨L', h1, h2⟩ := hpm i' e cE lsC' ms' _ hown' he hm hR
    exact ⟨L', hF ▸ h1, h2⟩
  have hlw := hperm.packedWF
  have hcov : ∀ x < ds'.length, VExpr.bvar x ∈ leadE ∨ x ∈ eqFs j := by
    intro x hx
    rw [mapM_length hds, Instance.eqDoms_length] at hx
    rw [← hleadE]
    by_cases hxf : x < ((schema.view owner).constructors[j]).fields.length
    · exact .inr (by simpa [eqFs] using hxf)
    · exact .inl (List.mem_append_left _ (InductiveSignature.mem_vars (by omega) (by omega)))
  rcases hperm.admissible with hnz | hsmall
  · exact sound_pat_elim henv hΔ hEu hb hrules hmem hl hr hcov hlsP hrc.1 hrc.2.1 htype eT hlenH
      hkH hIrig hcf hcis (hpmL.majorFam (.inl (by
        rw [← VLevel.inst_inst]; exact hnzL' levels target hperm.length hnz))) hcrig huniq
      (fun keys hkl hobs => C_absurd_gen hΔ hlw eT hlenH hkH hIrig hfs
        (hnzL levels target hperm.length hnz) hkl hobs) ihL ihR
      (.elimIota hb hrules hmem hrc hperm hLd.defeq hRd.defeq)
  · obtain ⟨args', hargs, rfl⟩ := InductiveSignature.Restoration.expr_bvar_mkApps hT'
    obtain ⟨x, hx, hxget⟩ := mapM_reverse_getElem? hds (eqDoms_reverse_motive _ j)
    have hm := motive_eq (schema.specialize owner schema.genericUvars schema.genericLevels
      (.param 0))
    obtain ⟨ds0, e0, l0⟩ := hm _
    rw [e0] at hx
    obtain ⟨ds0', b', hds0, hb', rfl⟩ := Restoration.expr_wrapForalls_parts hx
    rw [InductiveSignature.Restoration.expr_sort, Option.some.injEq] at hb'
    subst hb'
    obtain ⟨mds, emds, lmds⟩ := binderTy_wrapForalls_sort hxget (target :: levels)
    refine sound_pat_elim_empty henv hΔ hEu hb hrules hl hr hlsP hrc.1 hrc.2.1 hcrig huniq
      htype eT hlenH hkH hpmL.weak ihL.1 ihR
      fun σ S W tv o => ?_
    refine rhs_empty_motive_ctx henv hΔ (doms := ds'.map (·.instL (target :: levels)))
      (by rw [ht, VExpr.instL_wrapForalls]) (by rw [hr, instL_wrapLams])
      ihT.2 (by simp only [VExpr.instL_mkApps, VExpr.instL]; rfl)
      (by have hxlt := (List.getElem?_eq_some_iff.1 hxget).1
          rw [List.length_reverse] at hxlt
          have := lookup_binderTy (Γ := []) (ls := target :: levels) hxlt
          rw [List.append_nil, emds] at this; exact this)
      (by have hfj : (schema.view owner).families[((schema.view owner).constructors[j]).owner] =
              schema.signature.families[owner] := by
            have : ((schema.view owner).constructors[j]).owner = ⟨0, by simp⟩ := Fin.ext h0
            exact (congrArg (fun o : Fin (schema.view owner).families.size =>
              (schema.view owner).families[o]) this).trans rfl
          rw [lmds, mapM_length hds0, l0, List.length_map, mapM_length hargs, hfj]
          simp only [List.length_append, List.length_singleton, hlen1])
      (funext fun v => by
        show (VLevel.param 0 |>.inst (target :: levels)).eval v = 0
        simp only [VLevel.inst, List.getD_cons_zero]
        exact (VLevel.equiv_def.1 hsmall _).trans rfl)
      ihR.1 W tv o

end Model
end VEnv
end Lean4Lean
