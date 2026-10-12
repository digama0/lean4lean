import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NestedRel

/-! # Facts about the containers of a nested block

The facts the validity of a nested block's rules reads off the block's containers (certified by
`ContainersInstalled`, each installed by `VEnv.addInduct` below the block): the data of a
container's compilation (`containers_mem`), the rigidity of a container family (through the
provenance of pattern constructors, `patCtor_resultRigid`, the model's copy of the confluence
engine's `WF.patCtor_resultRigid`, which the model cannot import), the projection facts
(`projMajor_installed`) and the semantic sort (`famSort_container`) of a container family. -/

namespace Lean4Lean
namespace VEnv
namespace Model
namespace Nested
open InductiveSignature

/-- The result type former of a raw constructor shape. -/
theorem rawCtorShape_head {decl : VInductDecl} {type : VInductiveType} {ctor : VConstVal}
    (H : decl.RawCtorShape type ctor) :
    ctor.type.forallResult.getAppFnArgs.1 = .const type.name (VLevel.params decl.uvars) := by
  obtain ⟨doms, result, heq, -, -, hhead⟩ := H
  rw [heq, VExpr.forallResult_wrapForalls, ← hhead]
  congr 1
  cases result with
  | forallE A B => simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at hhead
  | _ => rfl

/-- **Direct provenance of a pattern constructor** along the history: a constructor of an
`induct` step, with its raw shape. -/
theorem patCtor_provenance : ∀ {ds : List VDecl} {env : VEnv}, env.WF' ds →
    ∀ {c : Name}, IsPatCtor env c →
    ∃ (decl : VInductDecl) (type : VInductiveType) (ctor : VConstVal) (env₀ env₁ : VEnv),
      VDecl.induct decl ∈ ds ∧ type ∈ decl.types ∧ ctor ∈ type.ctors ∧ ctor.name = c ∧
      decl.RawCtorShape type ctor ∧ env₀.addInduct decl = some env₁ ∧ env₁ ≤ env := by
  suffices ∀ n, ∀ {ds : List VDecl}, ds.length = n → ∀ {env : VEnv}, env.WF' ds →
      ∀ {c : Name}, IsPatCtor env c →
      ∃ (decl : VInductDecl) (type : VInductiveType) (ctor : VConstVal) (env₀ env₁ : VEnv),
        VDecl.induct decl ∈ ds ∧ type ∈ decl.types ∧ ctor ∈ type.ctors ∧ ctor.name = c ∧
        decl.RawCtorShape type ctor ∧ env₀.addInduct decl = some env₁ ∧ env₁ ≤ env from
    fun {ds env} H {c} hc => this ds.length rfl H hc
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ds hn env H c hc
  obtain ⟨p, rr, recN, M, N, hp, rfl⟩ := hc
  obtain ⟨decl, ds₀, env₀, env₁, hsuf, H₀, hdecl, hadd, hle, rec, hrec, ru, hru, -, hpe, -⟩ :=
    H.pats_origin hp
  obtain ⟨-, -, rfl, -⟩ := iota_toPattern_inj hpe
  have hmem : VDecl.induct decl ∈ ds := hsuf.subset (List.mem_cons_self ..)
  obtain ⟨block, hcomp, hrecs, -⟩ := hdecl.recsCompiled
  rcases hcomp.rule_ctor_cases hrecs hrec hru with ⟨ctor, hctor, hname⟩ | hpat
  · obtain ⟨type, htype, hctor'⟩ := List.mem_flatMap.1 hctor
    obtain ⟨base, expanded, s, g, auxiliaries, -, hdata, -⟩ := hcomp.data
    obtain ⟨-, -, -, -, -, hraw⟩ := hdata.sourceParameters
    exact ⟨decl, type, ctor, env₀, env₁, hmem, htype, hctor', hname.symm,
      hraw type htype ctor hctor', hadd, hle⟩
  · have hlt : ds₀.length < ds.length := by
      have := hsuf.length_le
      simp at this
      omega
    obtain ⟨decl', type, ctor, env₀', env₁', hmem', htype, hctor, hname, hraw, hadd', hle'⟩ :=
      ih ds₀.length (hn ▸ hlt) rfl H₀ hpat
    exact ⟨decl', type, ctor, env₀', env₁', ((List.suffix_cons _ _).trans hsuf).subset hmem',
      htype, hctor, hname, hraw, hadd', hle'.trans ((addInduct_le hadd).trans hle)⟩

/-- **The family of a pattern constructor is rigid.** -/
theorem patCtor_resultRigid {ds : List VDecl} {env : VEnv} (H : env.WF' ds) {c : Name}
    (hc : IsPatCtor env c) : env.CtorResultRigid c := by
  obtain ⟨decl, type, ctor, env₀, env₁, hmem, htype, hctor, rfl, hraw, hadd, hle⟩ :=
    patCtor_provenance H hc
  exact ⟨ctor.toVConstant, hle.constants (addInduct_ctor_find hadd htype hctor), type.name,
    VLevel.params decl.uvars, rawCtorShape_head hraw,
    ⟨_, hle.constants (addInduct_type_find hadd htype)⟩, H.inductTypeRigid hmem htype⟩

/-- The containers of an installed specialization list: each is a compiled declaration
installed by `VEnv.addInduct` below the environment. -/
theorem containers_mem {env : VEnv} {aux : List ContainerSpecialization}
    (H : ContainersInstalled env aux) {a : ContainerSpecialization} (ha : a ∈ aux) :
    ∃ (base0 installed base' : VEnv) (block : VInductBlock) (expanded : VInductDecl)
      (s : InductiveSignature) (g : Instance s) (aux' : List ContainerSpecialization),
      base' ≤ base0 ∧ CompilationData base' a.container expanded s g aux' block ∧
      a.container.RecsOf block ∧ base0.addInduct a.container = some installed ∧
      installed ≤ env := by
  induction aux generalizing env with
  | nil => cases ha
  | cons a' rest ih =>
    cases H with
    | @cons _ _ _ base block installed hcompile _ hrecs hinstall hle hrest =>
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨b, e, s, g, a2, hb, C, -⟩ := hcompile.data
      exact ⟨base, installed, b, block, e, s, g, a2, hb, C, hrecs, hinstall, hle⟩
    · exact ih hrest ha

/-- A constructor of an installed declaration returns its own type former (from its raw shape). -/
theorem addInduct_ctor_retFam' {env env₀ env₁ : VEnv} {decl : VInductDecl}
    (hraw : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, decl.RawCtorShape t c)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    {type : VInductiveType} (htype : type ∈ decl.types) {ctor : VConstVal}
    (hctor : ctor ∈ type.ctors) : RetFam env ctor.name type.name :=
  ⟨ctor.toVConstant, VLevel.params decl.uvars,
    hle.constants (addInduct_ctor_find hadd htype hctor), rawCtorShape_head (hraw type htype ctor hctor)⟩

/-- **The projection facts of a family of an installed declaration** (`projMajor_decl` for a
declaration known by its raw constructor shapes, such as a container). -/
theorem projMajor_installed {envF env₀ env₁ : VEnv} {decl : VInductDecl}
    (hF : envF.WF) (hraw : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, decl.RawCtorShape t c)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ envF)
    (hprojV : ∀ S info, env₁.projections S info → Model.ProjValid envF S info)
    {t : VInductiveType} (ht : t ∈ decl.types) {fc : VConstVal} (hfc : fc ∈ t.ctors)
    (hpat : ∀ c ∈ t.ctors, IsPatCtor envF c.name)
    {nf : Nat} (hshape : fc.type.forallArity = decl.nparams + nf) :
    Model.ProjMajor envF t.name fc.name decl.nparams nf t.resultLevel := by
  by_cases hex : ∃ info, envF.projections t.name info
  · obtain ⟨info, hp⟩ := hex
    have hall : ∀ c2 ∈ t.ctors, c2.name = info.ctorName := fun c2 hc2 =>
      hF.structCoh t.name info hp c2.name (hpat c2 hc2)
        (addInduct_ctor_retFam' hraw hadd hle ht hc2)
    have hnodup : (t.ctors.map (·.name)).Nodup := by
      obtain ⟨e1, e2, e3, s1, s2, s3, s4⟩ := addInduct_stages hadd
      have h := addCtors_nodup s2
      rw [List.map_flatMap] at h
      exact List.Nodup.sublist
        (Model.sublist_flatMap_of_mem_aux (f := fun t => t.ctors.map (·.name)) ht) h
    have hsingle : t.ctors = [fc] := Model.eq_singleton_of_nodup_map_aux hnodup hfc
      (fun y hy => (hall y hy).trans (hall fc hfc).symm)
    have hentry : (⟨t.name, ⟨decl.uvars, decl.nparams, t.numIndices, t.resultLevel,
        fc.name, fc.type⟩⟩ : VProjectionEntry) ∈ decl.projectionEntries :=
      List.mem_filterMap.mpr ⟨t, ht, by rw [hsingle]⟩
    have hp' := (addInduct_projections_iff hadd).mpr (.inl ⟨_, hentry, rfl, rfl⟩)
    have := hF.ordered.projections_unique hp (hle.projections hp')
    subst this
    refine .inr ⟨_, hp, hprojV _ _ hp', rfl, rfl, ?_, VLevel.equiv_def'.2 rfl⟩
    simp only [VProjectionInfo.numFields, hshape]
    omega
  · refine .inl ⟨fun info h => hex ⟨info, h⟩, fun ⟨S, info, hp, hcn⟩ => hex ⟨info, ?_⟩⟩
    have h1 := Model.projection_retFam hF.ordered hp
    rw [hcn] at h1
    have h2 := addInduct_ctor_retFam' hraw hadd hle ht hfc
    rw [← h1.unique h2]; exact hp

theorem famSort_congr {env : VEnv} {I : Name} {l l' : VLevel} (H : FamSort env I l)
    (h : l ≈ l') : FamSort env I l' := by
  intro U Δ ci lsI ks z hΔ hci hls ho
  rw [H U Δ ci lsI ks z hΔ hci hls ho]
  exact VLevel.inst_congr_l h

/-- **The semantic sort of a family of an installed compiled declaration** (a container), in the
model of `envF` in which the environment below the current block is valid. -/
theorem famSort_installed {envF env0 base0 installed base' : VEnv} {D expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} (henvF : envF.OrderedStrong) (h0s : env0.OrderedStrong)
    (h0F : env0 ≤ envF) (V0 : EnvValid envF env0) (hb : base' ≤ base0)
    (C : CompilationData base' D expanded s g aux block)
    (hadd : base0.addInduct D = some installed) (hle : installed ≤ env0)
    {t : VInductiveType} (ht : t ∈ D.types) : FamSort envF t.name t.resultLevel := by
  obtain ⟨envTypes, direct, htypes, -, -, hfam⟩ := C.correspondence
  obtain ⟨nt, -, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hfam t (List.mem_append_left _ ht)
  obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := addInduct_stages hadd
  have hT' := hT
  rw [VInductDecl.addTypes_eq_addConstVals] at hT'
  have hTE : envTypes ≤ env0 :=
    (addConstVals_mono hb htypes hT').trans ((addCtors_le hC).trans (addProjs_le.trans
      ((addRecs_le hR).trans ((addRules_le hP).trans hle))))
  have hc : envF.constants t.name = some t.toVConstant :=
    h0F.constants (hle.constants (addInduct_type_find hadd ht))
  exact famSort_congr (Model.famSort_of henvF h0s h0F V0 hc (h1.mono hTE) (h2.mono hTE) hlev)
    hrel.resultLevel

/-! ## The specialized and the restored constructor types -/

theorem takeForalls_wrapForalls_le {ds : List VExpr} {R : VExpr} {n : Nat} (hn : n ≤ ds.length) :
    (VExpr.wrapForalls ds R).takeForalls n = some (ds.take n, .wrapForalls (ds.drop n) R) := by
  have := VExpr.takeForalls_wrapForalls_append (ds.take n) (ds.drop n) R
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hn] at this
  exact this

theorem instantiateParams_eq_subst (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.subst (VExpr.argSubst args) := by
  unfold instantiateParams
  congr 1
  funext i
  rw [VExpr.argSubst, VExpr.foldl_cons_apply]
  rfl

/-- **The specialized type of a container constructor.** -/
theorem specializeType_shape {cdoms : List VExpr} {R0 : VExpr} {lv : List VLevel}
    {Ds0 : List VExpr} {T : VExpr} (hl : Ds0.length ≤ cdoms.length)
    (h : specializeType ((VExpr.wrapForalls cdoms R0).instL lv) Ds0 = some T) :
    T = .wrapForalls ((cdoms.drop Ds0.length).zipIdx.map fun ((d, j) : VExpr × Nat) =>
        (d.instL lv).subst ((VExpr.argSubst Ds0).liftN j))
      ((R0.instL lv).subst ((VExpr.argSubst Ds0).liftN (cdoms.length - Ds0.length))) := by
  unfold specializeType at h
  rw [VExpr.instL_wrapForalls, takeForalls_wrapForalls_le (by simpa using hl)] at h
  simp only [bind, Option.bind_some, pure, Option.some.injEq] at h
  subst h
  rw [instantiateParams_eq_subst,
    show VExpr.argSubst Ds0 = (VExpr.argSubst Ds0).liftN 0 from rfl, subst_wrapForalls_liftN]
  simp only [List.map_drop, Nat.zero_add, List.length_drop, List.length_map]
  rw [← List.map_drop, List.zipIdx_map, List.map_map]
  rfl

/-- **The restored normalized constructor type**: the restored parameters and fields, and the
restored family spine over the specialization arguments and the restored indices. -/
theorem restored_constructorType {s : InductiveSignature} {r : Restoration}
    (ctor : Constructor s.families.size) {I0 : Name} {lvf : List VLevel → List VLevel}
    {Ds0 : List VExpr}
    (hSF : Spec r s.families[ctor.owner].name s.params.length I0 lvf Ds0) {out : VExpr}
    (h : r.expr (s.constructorType ctor) = some out) :
    ∃ P0 Fn0 Idx0, s.params.mapM r.expr = some P0 ∧ (s.fieldTypes ctor).mapM r.expr = some Fn0 ∧
      ctor.indices.mapM r.expr = some Idx0 ∧
      out = .wrapForalls (P0 ++ Fn0) (.mkApps (.const I0 (lvf (VLevel.params s.uvars)))
        (Ds0.map (fun e => (e.instL (VLevel.params s.uvars)).liftN ctor.fields.length) ++ Idx0)) := by
  unfold constructorType at h
  obtain ⟨ds', b, hds, hb, rfl⟩ := expr_wrapForalls_parts h
  obtain ⟨P0, Fn0, h1, h2, rfl⟩ := mapM_append hds
  simp only [familyApp] at hb
  obtain ⟨Idx0, hIdx, rfl⟩ := hSF.spine _ _ _ _ hb
  exact ⟨P0, Fn0, Idx0, h1, h2, hIdx, rfl⟩

/-! ## The restored equation's type and motive -/

theorem eqDoms_motive {s : InductiveSignature} (g : Instance s) (index : Fin s.constructors.size) :
    (g.eqDoms index)[s.params.length + s.constructors[index].owner.val]? =
      some (g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val) := by
  have ho := s.constructors[index].owner.isLt
  simp only [Instance.eqDoms, List.append_assoc]
  rw [List.getElem?_append_right (by simp [Instance.params]),
    List.getElem?_append_left (by simp [Instance.params, Instance.motives])]
  simp [Instance.params, Instance.motives]

/-- The restored motive of an owner is a telescope of the owner's index count plus one ending in
the target sort. -/
theorem restored_motive {s : InductiveSignature} (g : Instance s) {r : Restoration}
    (family : Family) (prior : Nat) {out : VExpr} (h : r.expr (g.motive family prior) = some out) :
    ∃ mds, out = .wrapForalls mds (.sort g.targetLevel) ∧ mds.length = family.indices.length + 1 := by
  unfold Instance.motive at h
  obtain ⟨ds', b, hds, hb, rfl⟩ := expr_wrapForalls_parts h
  rw [Restoration.expr_sort] at hb
  cases hb
  refine ⟨ds', rfl, ?_⟩
  rw [mapM_length hds]
  simp [insertBinders]

/-- The type of a restored equation: a telescope over the restored binders whose body applies
the major's motive to the restored indices and constructor application. -/
theorem restored_equation_type {s : InductiveSignature} (g : Instance s) {r : Restoration}
    (index : Fin s.constructors.size) {df : VDefEq} {ds' : List VExpr}
    (hds : (g.eqDoms index).mapM r.expr = some ds') (h : r.equation (g.equation index) = some df) :
    ∃ targs, df.type = .wrapForalls ds' (.mkApps (.bvar (s.constructors[index].fields.length +
        s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val))) targs) ∧
      targs.length = s.constructors[index].indices.length + 1 := by
  obtain ⟨-, -, ht⟩ := Restoration.equation_parts h
  have hty : (g.equation index).type = .wrapForalls (g.eqDoms index)
      (.mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)))
        (g.eqIndices index ++ [g.constructorApp s.constructors[index]
          (s.families.size + s.constructors.size) 0])) := rfl
  rw [hty] at ht
  obtain ⟨ds2, b, hds2, hb, et⟩ := expr_wrapForalls_parts ht
  cases hds.symm.trans hds2
  rw [Restoration.expr_mkApps_bvar] at hb
  obtain ⟨targs, htargs, rfl⟩ := Option.map_eq_some_iff.1 hb
  refine ⟨targs, et, ?_⟩
  rw [mapM_length htargs]
  simp [Instance.eqIndices]

end Nested
end Model
end VEnv
end Lean4Lean
