import Lean4Lean.Theory.Typing.EnvTables.Container

/-!
# Majors of installed equations
-/

namespace Lean4Lean.EnvTables
open _root_.Lean4Lean.EnvTables.VEnv InductiveSignature

/-- The major of a restored recursor equation is a source constructor applied to the parameter
variables, or a container constructor applied to the specialized container parameters; in both
cases followed by the field variables. -/
theorem CompilationData.major_cases {base : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (hdata : CompilationData base src exp s g aux block)
    (j : Fin s.constructors.size) {df : VDefEq}
    (hrestore : (compilationRestoration src aux).equation (g.equation j) = some df) :
    ∃ Ds idx major, df.lhs = VExpr.wrapLams Ds (VExpr.mkApps
        (.const ((compilationRestoration src aux).recursorName
          (g.recursorName s.constructors[j].owner)) (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[j].fields.length ++ idx ++ [major])) ∧
      idx.length = s.constructors[j].indices.length ∧
      ((∃ F ∈ src.types, src.types[s.constructors[j].owner.val]? = some F ∧
        ∃ c ∈ F.ctors, c.name = s.constructors[j].name ∧
        major = VExpr.mkApps (.const c.name g.levels)
          (vars s.params.length (s.families.size + s.constructors.size +
            s.constructors[j].fields.length) ++ vars s.constructors[j].fields.length 0)) ∨
      (∃ a ∈ aux, src.types.length ≤ s.constructors[j].owner.val ∧
        aux[s.constructors[j].owner.val - src.types.length]? = some a ∧
        ∃ c ∈ a.source.ctors, s.constructors[j].name = a.constructorName c ∧
        major = VExpr.mkApps (.const c.name (a.levels.map (·.inst g.levels)))
          (a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
            (vars s.params.length (s.families.size + s.constructors.size +
              s.constructors[j].fields.length))) ++ vars s.constructors[j].fields.length 0))) := by
  obtain ⟨Ds, idx, R, major, hlhs, _, _, hidx, _, hmaj⟩ :=
    CompilationData.rule_shape hdata j hrestore
  refine ⟨Ds, idx, major, hlhs, hidx, ?_⟩
  by_cases ho : s.constructors[j].owner.val < src.types.length
  · obtain ⟨_, _, hctors⟩ := CaseCompilationData.source_slot hdata.toCaseCompilationData _ ho
    obtain ⟨c, hc, hcn⟩ := hctors j rfl
    have hF := List.getElem_mem (l := src.types) ho
    have hcn' : c.name ∈ familyNames src.types :=
      List.mem_flatMap.mpr ⟨_, hF, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
    left
    refine ⟨_, hF, List.getElem?_eq_getElem ho, c, hc, hcn, ?_⟩
    rcases hmaj with ⟨hnone, rfl⟩ | ⟨spec, hspec, hsome, _, _⟩
    · have hhn := hdata.headName_source hcn'
      unfold Restoration.headName at hhn
      rw [hcn, hnone] at hhn
      simp only at hhn
      rw [hhn, hcn]
    · exfalso
      have : spec.auxiliary = c.name := by
        rw [hcn]; simpa using List.find?_some hsome
      exact hdata.source_head_disjoint hcn' (List.mem_map.mpr ⟨spec, hspec, this⟩)
  · right
    obtain ⟨envTypes, direct, _, hdirect, hlt, hrel⟩ :=
      CaseCompilationData.family_slot hdata.toCaseCompilationData s.constructors[j].owner
    have ho' : src.types.length ≤ s.constructors[j].owner.val := by omega
    have hlt2 : s.constructors[j].owner.val < src.types.length + direct.length := by
      simpa using hlt
    rw [List.getElem_append_right ho'] at hrel
    have hrel' := List.mapM_eq_some.mp hdirect
    have hlen := Lean4Lean.List.Forall₂.length_eq hrel'
    have hjb : s.constructors[j].owner.val - src.types.length < aux.length := by omega
    obtain ⟨_, hdf⟩ := List.forall₂_getElem_exists hrel' (s.constructors[j].owner.val - src.types.length) hjb
    have ha := List.getElem_mem hjb
    obtain ⟨dc, hdc, hdcn, _⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
      (s.declarationCtor_family j)
    obtain ⟨c, hc, t, _, hdcname, _⟩ := directFamily_ctor hdf hdc
    have hjn : s.constructors[j].name = _ := hdcn.trans hdcname
    refine ⟨_, ha, ho', List.getElem?_eq_getElem hjb, c, hc, hjn, ?_⟩
    let a := aux[s.constructors[j].owner.val - src.types.length]
    have hhead : HeadSpecialization.mk (a.constructorName c) src.uvars src.nparams c.name
        a.levels a.arguments ∈ (compilationRestoration src aux).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
    rcases hmaj with ⟨hnone, _⟩ | ⟨spec, hspec, hsome, _, rfl⟩
    · exfalso
      have := List.find?_eq_none.mp hnone _ hhead
      simp at this
      exact this hjn.symm
    · have hsa : spec.auxiliary = a.constructorName c := by
        rw [← hjn]; simpa using List.find?_some hsome
      have := List.eq_of_mem_of_nodup_map hdata.restorationScoped.1 hspec hhead hsa
      subst this
      rfl

theorem auxCtor_head_mem {src : VInductDecl} {aux : List ContainerSpecialization}
    {a : ContainerSpecialization} (ha : a ∈ aux) {c : VConstVal} (hc : c ∈ a.source.ctors) :
    HeadSpecialization.mk (a.constructorName c) src.uvars src.nparams c.name a.levels a.arguments ∈
      (compilationRestoration src aux).heads :=
  List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩

theorem install_type_lookup {base installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install base block = some installed) (hv : v ∈ block.types) :
    installed.constants v.name = some v.toVConstant := by
  obtain ⟨t, c, r, ht, hc, hr, rfl⟩ := install_parts H
  simp only [VEnv.addDefEqRules_constants]
  exact (VEnv.addConstVals_le hr).constants (VEnv.addEliminators_addProjections_le.constants
    ((VEnv.addConstVals_le hc).constants (VEnv.addConstVals_get ht hv)))

/-- The table entry of a constructor recorded with the view of a declaration. -/
theorem ctor_entry_of_fam {T : Tables} {env : VEnv} (HT : T.Inv env) {decl : VInductDecl}
    {F : VInductiveType} (hfam : T.fam F.name = some (famView decl F)) {c : VConstVal}
    (hc : c ∈ F.ctors) (hconst : env.constants c.name = some c.toVConstant) :
    ∃ k, T.ctor c.name = some k ∧ k.family = F.name ∧ k.uvars = decl.uvars ∧
      k.nparams = decl.nparams ∧ k.nparams + k.nfields = c.type.forallArity ∧
      decl.nparams ≤ c.type.forallArity := by
  obtain ⟨_, _, hks⟩ := HT.views.fam hfam
  obtain ⟨k, hk, hkfam, hkuv, hknp⟩ := hks c.name (List.mem_map.mpr ⟨c, hc, rfl⟩)
  obtain ⟨⟨ci, doms, indices, hci, _, htype, hlen⟩, _⟩ := HT.views.ctor hk
  rw [hconst] at hci
  cases hci
  have harity : c.type.forallArity = doms.length := by
    change c.toVConstant.type.forallArity = _
    rw [htype, VExpr.forallArity_wrapForalls,
      VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)]
    rfl
  simp only [famView] at hkuv hknp
  exact ⟨k, hk, hkfam, hkuv, hknp, by omega, by omega⟩

/-- Majors of stored equations: every constructor major of an installed equation (recursor iota
equations after restoration, and the quotient equation with `Quot.mk`) is a constructor of the
table; it is applied to `k.nparams` parameter arguments followed by the field variables
`vars nf 0` (the innermost binders of the equation, see `CompilationData.rule_shape`). That
`nf` is `k.nfields` needs the semantic arity comparison of `Model/CtorArity.lean`, since the
field count comes from the normalized signature, which is only definitionally equal to the
constructor type. -/
theorem defeq_major {env : VEnv} (H : env.WF) (hdf : env.defeqs df)
    (hm : df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    ∃ k ps nf, ctorOf env c = some k ∧ args = ps ++ vars nf 0 ∧ ps.length = k.nparams := by
  have HT := envTables_inv H
  rcases HT.equations hdf with ⟨v, _, rfl⟩ | ⟨hq, rfl⟩ | ⟨dX, hdX, iX, hiX, hgX⟩
  · cases hm
  · have h1 : quotDefEq.lhs.stripLams = .app _
        (VExpr.mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]) := rfl
    rw [h1] at hm
    obtain ⟨_, hm⟩ := VExpr.app.inj hm
    obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hm.symm
    refine ⟨quotCtor, [.bvar 5, .bvar 4], 1, (HT.quot hq).2.2.1, rfl, rfl⟩
  · obtain ⟨_, hevX⟩ := HT.recursors hdX
    obtain ⟨bX, ibX, srcX, expX, auxX, blockX, instX, hdataX, hpriorX, hbX, hrX, _, hinstX,
      hleX, _, _, hfamX⟩ := hevX
    have hgX' : (compilationRestoration srcX auxX).equation (dX.recursorInstance.equation iX) =
        some df := by
      simpa only [RecursorData.equation, hrX] using hgX
    have htypesE : ∀ t ∈ srcX.types, env.constants t.name = some t.toVConstant := fun t ht =>
      hleX.constants (install_type_lookup hinstX (by
        rw [hdataX.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
    have hbE : bX ≤ env := hbX.trans ((VInductBlock.install_base_le hinstX).trans hleX)
    have hnp : dX.schema.signature.params.length = srcX.nparams := by
      rw [hdataX.model.nparams, hdataX.nparams]
    obtain ⟨Ds, idx, major, hlhs, _, hcases⟩ := CompilationData.major_cases hdataX iX hgX'
    have hmaj : major = VExpr.mkApps (.const c ls) args := by
      rw [hlhs, ruleBody_stripLams] at hm
      exact (VExpr.app.inj hm).2
    rcases hcases with ⟨F, hF, _, c', hc', hcn, rfl⟩ | ⟨a, ha, _, _, c', hc', hcn, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj
      have hconst : env.constants c'.name = some c'.toVConstant :=
        hleX.constants (VInductBlock.install_ctor_lookup hinstX (by
          rw [hdataX.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hc'⟩))
      obtain ⟨k, hk, _, _, hknp, hkar, _⟩ :=
        ctor_entry_of_fam HT (hfamX F hF (List.ne_nil_of_mem hc')) hc' hconst
      exact ⟨k, _, _, hk, rfl, by rw [InductiveSignature.length_vars, hknp, hnp]⟩
    · obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hmaj
      have hk := container_ctor HT hpriorX hbE ha hc'
      obtain ⟨_, _, _, _, hwf, _⟩ := hdataX.correspondence
      have hargs : a.arguments.length = a.container.nparams := (hwf a ha).1
      exact ⟨_, _, _, hk, rfl, by simp [ctorView, hargs]⟩

end Lean4Lean.EnvTables
