import Lean4Lean.Theory.Typing.HeadInjectivity.Model.FamSort
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.RestoredRecursorEquations

/-! # Validity of restored recursor rules (nested compilations)

`RuleValid.nested`: a restored equation of a compilation with container specializations is
valid in the model of a well-formed environment, given uniqueness per head (`HeadExcl`) and
`FamSort` for the restored family head of the major. Singleton elimination does not occur
(a nested compilation has at least two families); never-zero families make mode C
contradictory (`C_absurd_gen`); elimination into `Prop` empties the right-hand side.

`Model.famSort_container`: `FamSort` for the family of a certified container, from its own
compilation's family correspondence, in the environment preceding the nested declaration. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

namespace Model

theorem FamSort.congr {I : Name} {l l' : VLevel} (H : FamSort env I l) (h : l ≈ l') :
    FamSort env I l' := by
  intro U Δ ci lsI ks z hΔ hci hls ho
  rw [H U Δ ci lsI ks z hΔ hci hls ho]
  exact VLevel.inst_congr_l h

/-- `FamSort` for the family of a certified container. -/
theorem famSort_container {envF env0 base : VEnv} {aux : List ContainerSpecialization}
    {a : ContainerSpecialization}
    (henvF : envF.Ordered) (h0 : env0.Ordered) (h0F : env0 ≤ envF)
    (V : EnvValid envF env0)
    (hprior : ContainersInstalled base aux) (hb : base ≤ env0) (ha : a ∈ aux) :
    FamSort envF a.source.name a.source.resultLevel := by
  obtain ⟨base', block', inst', hcomp, -, hinst', hle'⟩ := hprior.mem a ha
  obtain ⟨base'', expanded'', s'', g'', aux'', hb'', C'', -⟩ := hcomp.exists_compilation
  obtain ⟨envTypes'', direct'', htypes'', -, -, hfam''⟩ := C''.correspondence
  have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
  obtain ⟨nf, -, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hfam'' a.source
    (List.mem_append_left _ hsrc)
  obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
  obtain ⟨types', ht', hti'⟩ := install_parts hinst'
  rw [C''.types] at ht'
  have hTE : envTypes'' ≤ env0 :=
    (addConstVals_mono hb'' htypes'' ht').trans (hti'.trans (hle'.trans hb))
  have hc : envF.constants a.source.name = some a.source.toVConstant :=
    h0F.constants (hti'.trans (hle'.trans hb) |>.constants
      (addConstVals_get ht' (List.mem_map_of_mem hsrc)))
  exact (famSort_of henvF h0 h0F V hc (h1.mono hTE) (h2.mono hTE) hlev).congr
    hrel.resultLevel

end Model

theorem mapM_reverse_getElem? {f : VExpr → Option VExpr} {l l' : List VExpr} {i : Nat}
    {a : VExpr} (hm : l.mapM f = some l') (h : l.reverse[i]? = some a) :
    ∃ a', f a = some a' ∧ l'.reverse[i]? = some a' := by
  have hl := mapM_length hm
  have hi : i < l.length := by
    have := (List.getElem?_eq_some_iff.1 h).1; simpa using this
  rw [List.getElem?_reverse hi] at h
  obtain ⟨a', h1, h2⟩ := mapM_getElem? hm h
  refine ⟨a', h1, ?_⟩
  rw [List.getElem?_reverse (by omega), hl]
  exact h2

namespace Model
variable {env : VEnv}

set_option maxHeartbeats 400000 in
/-- **Validity of a restored recursor rule** of a nested compilation. -/
theorem RuleValid.nested {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {base' installed : VEnv} {df : VDefEq} {L : VLevel}
    (henv : env.Ordered) (hdr : env.DeltaRules)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hcres : ∀ c, IsInstalledCtor env c → env.CtorResultRigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (C : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) (haux : aux ≠ []) (hbF : base ≤ env)
    (hinst : block.install base' = some installed) (hle : installed ≤ env)
    (index : Fin s.constructors.size)
    (hres : (compilationRestoration source aux).equation (g.equation index) = some df)
    (hdf : env.defeqs df)
    (hpm : ∀ fn lsC' ms', df.lhs.stripLams = .app fn (.mkApps
        (.const ((compilationRestoration source aux).headName s.constructors[index].name) lsC')
        (ms' ++ (eqFs index).map .bvar)) →
      ∃ L', ProjMajor env ((compilationRestoration source aux).headName
          s.families[s.constructors[index].owner].name)
        ((compilationRestoration source aux).headName s.constructors[index].name)
        ms'.length (eqFs index).length L' ∧
        ((∀ fam ∈ s.families.toList, (fam.resultLevel.inst g.levels).IsNeverZero) →
          (L'.inst lsC').IsNeverZero))
    (hex : HeadExcl env ((compilationRestoration source aux).recursorName
      (g.recursorName s.constructors[index].owner)) block.rules)
    (hfs : FamSort env ((compilationRestoration source aux).headName
      s.families[s.constructors[index].owner].name) L)
    (hnzL : (∀ fam ∈ s.families.toList, (fam.resultLevel.inst g.levels).IsNeverZero) →
      (L.inst ((compilationRestoration source aux).headLevels
        s.families[s.constructors[index].owner].name g.levels)).IsNeverZero) :
    RuleValid env df := by
  intro U Δ Γ ls u hΔ hlw hlen _ ihT _ ihL _ ihR
  have hparams : ∀ h ∈ (compilationRestoration source aux).heads, h.nparams ≤ s.params.length :=
    fun h hh => Nat.le_of_eq (C.restoration_nparams h hh)
  obtain ⟨ds', idx', lsC', ms', body', T', hds, hidx, hl, hr, ht, hT', huv⟩ :=
    g.restored_equation index hparams (C.heads_not_recursors _) hres
  have hdsl := mapM_length hds
  have hidxl := mapM_length hidx
  have harity := C.model.constructorArity s.constructors[index] (by simp)
  simp only [Fin.getElem_fin] at harity
  have hlsP : (VLevel.params g.uvars).map (·.inst ls) = ls :=
    VLevel.inst_map_id (hlen.trans huv)
  have hcl := henv.closed.2 hdf
  have hcov : ∀ x < ds'.length, VExpr.bvar x ∈ vars (s.params.length +
      (s.families.size + s.constructors.size)) s.constructors[index].fields.length ++ idx' ∨
      x ∈ eqFs index := by
    intro x hx
    rw [hdsl, g.eqDoms_length] at hx
    by_cases hxf : x < s.constructors[index].fields.length
    · exact .inr (by simpa [eqFs] using hxf)
    · exact .inl (List.mem_append_left _ (InductiveSignature.mem_vars (by omega) (by omega)))
  -- the recursor
  obtain ⟨rec', hrec', hn, -, dsH', RH', eH, hdsH⟩ := C.restored_recursor s.constructors[index].owner
  have hci := hle.constants (VInductBlock.install_recursor_lookup hinst hrec')
  rw [hn] at hci
  have hlenH : dsH'.length = (vars (s.params.length + (s.families.size + s.constructors.size))
      s.constructors[index].fields.length ++ idx').length + 1 := by
    rw [mapM_length hdsH, g.recDoms_length]
    simp only [List.length_append, InductiveSignature.length_vars, hidxl, Instance.eqIndices, List.length_map]
    simp only [Fin.getElem_fin] at *
    omega
  obtain ⟨d', hd', hget⟩ := mapM_getElem? hdsH (g.recDoms_major s.constructors[index].owner)
  obtain ⟨iargs, rfl⟩ := Restoration.const_mkApps_exact hd'
  have hkH : dsH'[(vars (s.params.length + (s.families.size + s.constructors.size))
      s.constructors[index].fields.length ++ idx').length]? = some (VExpr.mkApps
        (.const ((compilationRestoration source aux).headName
          s.families[s.constructors[index].owner].name)
          ((compilationRestoration source aux).headLevels
            s.families[s.constructors[index].owner].name g.levels)) iargs) := by
    rw [← hget]
    congr 1
    simp only [List.length_append, InductiveSignature.length_vars, hidxl, Instance.eqIndices, List.length_map]
    simp only [Fin.getElem_fin] at *
    omega
  -- the constructor and its family
  have hcisN : IsInstalledCtor env
      ((compilationRestoration source aux).headName s.constructors[index].name) :=
    ⟨_, hdf, _, _, _, by rw [hl, VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]; rfl⟩
  have hcis : IsCtor env ((compilationRestoration source aux).headName s.constructors[index].name) :=
    .inl hcisN
  obtain ⟨ci, hci', F, lsF, hF, -, hrigF⟩ := hcres _ hcisN
  have hFam : F = (compilationRestoration source aux).headName
      s.families[s.constructors[index].owner].name := by
    rcases C.ctor_cases hprior index with ⟨fc, hfc, hfcn, lsc, hfch⟩ | ⟨cc, hcc, lsc, hcch⟩
    · have hfc' := hle.constants (VInductBlock.install_ctor_lookup hinst
        (by rw [C.ctors]; exact hfc))
      rw [hfcn, hci'] at hfc'
      cases hfc'
      rw [hfch] at hF
      cases hF; rfl
    · have hcc' := hbF.constants hcc
      rw [hci'] at hcc'
      cases hcc'
      rw [hcch] at hF
      cases hF; rfl
  subst hFam
  have hcf : CtorFam env ((compilationRestoration source aux).headName s.constructors[index].name)
      ((compilationRestoration source aux).headName
        s.families[s.constructors[index].owner].name) := ⟨_, _, hci', hF⟩
  -- uniqueness per head and constructor
  have huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const ((compilationRestoration source aux).recursorName
        (g.recursorName s.constructors[index].owner)) lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = (vars (s.params.length + (s.families.size + s.constructors.size))
        s.constructors[index].fields.length ++ idx').length ∧
      (ctor' = (compilationRestoration source aux).headName s.constructors[index].name →
        df' = df) := by
    intro df' doms' lsP' lead' ctor' lsC'' ms'' fs' body'' hdf' hl' _
    have hm := hex df' hdf' lsP' (by rw [hl']; exact VExpr.stripLams_wrapLams_mkApps_head)
    obtain ⟨src, hsrc, hrj⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp C.equations) _ hm
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hsrc
    obtain ⟨dsj, idxj, lsCj, msj, -, -, -, hidxj, hlj, -, -, -, -⟩ :=
      g.restored_equation j hparams (C.heads_not_recursors _) hrj
    obtain ⟨-, n2, -, l2, a2⟩ := wrapLams_pat_inj (hl'.symm.trans hlj)
    obtain ⟨c2, -, -⟩ := VExpr.mkApps_const_inj a2
    have ho := C.restored_recursorName_inj n2
    have harj := C.model.constructorArity s.constructors[j] (by simp)
    have he := congrArg (fun o : Fin s.families.size => s.families[o].indices.length) ho
    refine ⟨?_, fun hc => ?_⟩
    · rw [l2]
      simp only [List.length_append, InductiveSignature.length_vars, hidxl, mapM_length hidxj, Instance.eqIndices,
        List.length_map]
      simp only [Fin.getElem_fin] at harj he harity ⊢
      omega
    · have := C.restored_ctor_inj hprior ho.symm (c2.symm.trans hc)
      subst this
      exact Option.some.inj (hrj.symm.trans hres)
  obtain ⟨L', hpmL, hnzL'⟩ := hpm _ _ _ (by rw [hl, VExpr.stripLams_wrapLams, VExpr.mkApps_snoc]; rfl)
  obtain ⟨envE, hE, hadm⟩ := C.admissible
  rcases hadm.elimination with hnz | hsmall | hsing
  · -- data families: mode C is impossible
    exact sound_pat henv hΔ hdf hl hr hcov hlsP hcl.1.1 hcl.2.1 hci eH hlenH hkH
      hrigF hcf hcis (hpmL.majorFam (.inl (by rw [← VLevel.inst_inst]; exact (hnzL' hnz).inst)))
      (hctor _ hcis) hctor
      hpctor hdr huniq
      (fun keys hkl hobs => absurd hobs fun h =>
        C_absurd_gen hΔ hlw eH hlenH hkH hrigF hfs (hnzL hnz).inst hkl h)
      ihL ihR (.extra hdf hlw hlen)
  · -- small elimination: the right-hand side has no observations
    obtain ⟨args', hargs, rfl⟩ := InductiveSignature.Restoration.expr_bvar_mkApps hT'
    obtain ⟨x, hx, hxget⟩ := mapM_reverse_getElem? hds (eqDoms_reverse_motive g index)
    have hm := motive_eq g
    obtain ⟨ds0, e0, l0⟩ := hm _
    rw [e0] at hx
    obtain ⟨ds0', b', hds0, hb', rfl⟩ := Restoration.expr_wrapForalls_parts hx
    rw [InductiveSignature.Restoration.expr_sort, Option.some.injEq] at hb'
    subst hb'
    obtain ⟨mds, emds, lmds⟩ := binderTy_wrapForalls_sort hxget ls
    have hcl' : (df.type.instL ls).ClosedN := hcl.1.2.instL
    refine sound_pat_empty henv hΔ hdf hl hr hlsP hcl.1.1 hcl.2.1 (hctor _ hcis) hctor hpctor hdr
      huniq hci eH hlenH hkH hpmL.weak ihL.1 ihR fun σ S W tv o => ?_
    refine rhs_empty_motive henv hΔ (doms := ds'.map (·.instL ls))
      (by rw [ht, VExpr.instL_wrapForalls]) (by rw [hr, instL_wrapLams])
      hcl' ihT.2 (by simp only [VExpr.instL_mkApps, VExpr.instL]; rfl)
      (by have hxlt := (List.getElem?_eq_some_iff.1 hxget).1
          rw [List.length_reverse] at hxlt
          have := lookup_binderTy (Γ := []) (ls := ls) hxlt
          rw [List.append_nil, emds] at this; exact this)
      (by rw [lmds, mapM_length hds0, l0, List.length_map, mapM_length hargs]
          simp only [List.length_append, Instance.eqIndices, List.length_map,
            List.length_singleton, Fin.getElem_fin] at harity ⊢
          omega)
      (funext fun v => by
        rw [VLevel.eval_inst]; exact (VLevel.equiv_def.1 hsmall _).trans rfl)
      ihR.1 W tv o
  · -- singleton elimination does not occur for nested compilations
    exact absurd hsing.1.1 (by have := C.nested_families haux; omega)

end Model
end VEnv
end Lean4Lean
