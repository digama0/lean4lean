import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaOrdinary
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.FamSort
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.StructCoh

/-! # The stage environments of an inductive step in the model

For an inductive declaration `decl` added to `env0` inside a well-formed `envF` of which `env0`
is a prefix: the type-former stage `envT` and the recursor stage `envR` of `addInduct` satisfy
the hypotheses of the strong system (`stages_orderedStrong`) and are valid in the model of
`envF` (`stages_envValid`). From them: the projection facts of a family of the declaration
(`projMajor_decl`) and its semantic sort (`famSort_decl`). -/

namespace Lean4Lean
namespace VEnv

/-- Strong typing of the constants of the type-former stage and the recursor stage of
`addInduct` (the corresponding part of `addInduct_strong`). -/
theorem addInduct_stage_strong {env envT envC envR : VEnv} {decl : VInductDecl}
    (hord : Ordered env) (IH : OnTypes env (EnvStrong env)) (hdecl : decl.WF env)
    (hT : decl.addTypes env = some envT) (hC : decl.addCtors envT = some envC)
    (hR : decl.addRecs (decl.addProjs envC) = some envR) :
    OnTypes envT (EnvStrong envT) ∧ OnTypes envR (EnvStrong envR) := by
  have hTC : decl.addTypesCtors env = some envC := by
    unfold VInductDecl.addTypesCtors; rw [hT]; exact hC
  have hTCP : decl.addTypesCtorsProjs env = some (decl.addProjs envC) :=
    addTypesCtorsProjs_eq_some hTC
  have hordT := addTypes_ordered hord hdecl hT
  have hordC := addCtors_ordered hdecl hT hordT hC
  have hordP := addProjs_ordered hord hdecl hTC hordC
  have IHT : OnTypes envT (EnvStrong envT) := by
    unfold VInductDecl.addTypes at hT
    exact foldlM_addConst_strong hord IH hdecl.types_wf hT
  have IHC : OnTypes envC (EnvStrong envC) := by
    have hcw : ∀ c ∈ decl.types.flatMap (·.ctors), c.toVConstant.WF envT := fun c hc => by
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
      exact hdecl.ctors_wf envT hT t ht c hc
    unfold VInductDecl.addCtors at hC
    exact foldlM_addConst_strong hordT IHT hcw hC
  have IHP : OnTypes (decl.addProjs envC) (EnvStrong (decl.addProjs envC)) :=
    OnTypes.addProjections IHC
  have IHR : OnTypes envR (EnvStrong envR) := by
    have hrw := hdecl.recs_wf _ hTCP
    unfold VInductDecl.addRecs at hR
    exact foldlM_addConst_strong hordP IHP hrw hR
  exact ⟨IHT, IHR⟩

/-- **The stage environments of an inductive step are strong**: the type-former stage and the
recursor stage of `addInduct` over a well-formed environment. -/
theorem stages_orderedStrong {env0 envT envC envR : VEnv} {decl : VInductDecl}
    (h0 : env0.WF) (hdecl : decl.WF env0)
    (hT : decl.addTypes env0 = some envT) (hC : decl.addCtors envT = some envC)
    (hR : decl.addRecs (decl.addProjs envC) = some envR) :
    envT.OrderedStrong ∧ envR.OrderedStrong := by
  have hord := h0.ordered
  obtain ⟨IHT, IHR⟩ := addInduct_stage_strong hord h0.orderedStrong.strong hdecl hT hC hR
  have hTC : decl.addTypesCtors env0 = some envC := by
    unfold VInductDecl.addTypesCtors; rw [hT]; exact hC
  have hTCP : decl.addTypesCtorsProjs env0 = some (decl.addProjs envC) :=
    addTypesCtorsProjs_eq_some hTC
  have hordT := addTypes_ordered hord hdecl hT
  have hordR : Ordered envR :=
    addRecs_ordered hdecl hTCP (addTypesCtorsProjs_ordered hord hdecl hTCP) hR
  exact ⟨⟨hordT, IHT⟩, ⟨hordR, IHR⟩⟩

/-- **The stage environments of an inductive step are valid** in the model of `envF`, given
the validity of the step's base and of the step's projection entries. -/
theorem stages_envValid {envF env0 env' envT envC envR : VEnv} {decl : VInductDecl}
    (V0 : Model.EnvValid envF env0)
    (hprojV : ∀ S info, env'.projections S info → Model.ProjValid envF S info)
    (hT : decl.addTypes env0 = some envT) (hC : decl.addCtors envT = some envC)
    (hR : decl.addRecs (decl.addProjs envC) = some envR) (hP : decl.addRules envR = some env') :
    Model.EnvValid envF envT ∧ Model.EnvValid envF envR := by
  refine ⟨V0.of_sub (fun df h => by rwa [addTypes_defeqs hT] at h)
      (fun n p h => by rwa [addTypes_projections hT] at h)
      (fun p r h => by rwa [addTypes_pats hT] at h), ?_⟩
  exact ⟨fun df h => V0.rule df (by
      rwa [addRecs_defeqs hR, addProjs_defeqs, addCtors_defeqs hC, addTypes_defeqs hT] at h),
    fun n p h => hprojV n p ((addRules_le hP).projections h),
    fun p r h => V0.pat p r (by
      rwa [addRecs_pats hR, addProjs_pats, addCtors_pats hC, addTypes_pats hT] at h)⟩

theorem _root_.Lean4Lean.VExpr.piArity_eq_forallArity : ∀ e : VExpr, e.piArity = e.forallArity
  | .forallE _ B => by simp [VExpr.piArity, VExpr.forallArity, VExpr.piArity_eq_forallArity B]
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .proj _ _ _ => rfl

theorem Model.sublist_flatMap_of_mem_aux {α β : Type} {f : α → List β} {a : α} {l : List α}
    (h : a ∈ l) : List.Sublist (f a) (l.flatMap f) := by
  induction l with
  | nil => cases h
  | cons b t ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

theorem Model.eq_singleton_of_nodup_map_aux {α β : Type} {f : α → β} {a : α} {l : List α}
    (hnodup : (l.map f).Nodup) (ha : a ∈ l) (hsame : ∀ y ∈ l, f y = f a) : l = [a] := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hx : x = a := by
      rcases List.mem_cons.mp ha with rfl | hxs
      · rfl
      · exact absurd (hsame x (.head _) ▸ List.mem_map_of_mem hxs) hnodup.1
    subst hx
    cases xs with
    | nil => rfl
    | cons y ys =>
      exact absurd ((hsame y (.tail _ (.head _))) ▸ List.mem_map_of_mem (.head _)) hnodup.1

/-- **The projection facts of a family of an installed declaration**, given the validity of the
declaration's projection entries and that its constructors are pattern constructors: the family
is not a registered structure and its constructor is not a projection constructor, or its entry
is the declaration's, with the constructor `fc`, the declaration's parameters and the
constructor's fields. -/
theorem projMajor_decl {envF env0 env' : VEnv} {decl : VInductDecl}
    (hF : envF.WF) (hdecl : decl.WF env0) (hadd : env0.addInduct decl = some env')
    (hle : env' ≤ envF)
    (hprojV : ∀ S info, env'.projections S info → Model.ProjValid envF S info)
    {t : VInductiveType} (ht : t ∈ decl.types) {fc : VConstVal} (hfc : fc ∈ t.ctors)
    (hpat : ∀ c ∈ t.ctors, IsPatCtor envF c.name)
    {nf : Nat} (hshape : fc.type.forallArity = decl.nparams + nf) :
    Model.ProjMajor envF t.name fc.name decl.nparams nf t.resultLevel := by
  by_cases hex : ∃ info, envF.projections t.name info
  · obtain ⟨info, hp⟩ := hex
    have hall : ∀ c2 ∈ t.ctors, c2.name = info.ctorName := fun c2 hc2 =>
      hF.structCoh t.name info hp c2.name (hpat c2 hc2)
        (Model.addInduct_ctor_retFam hdecl hadd hle ht hc2)
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
    have h2 := Model.addInduct_ctor_retFam hdecl hadd hle ht hfc
    rw [← h1.unique h2]; exact hp

/-- **The semantic sort of a family of a declaration**, from the restoration relating it to its
normalized family, in the model of `envF` in which the declaration's type-former stage is
valid. -/
theorem famSort_decl {envF env0 envT base envTypes : VEnv} {decl : VInductDecl}
    {t nt : VInductiveType} {r : InductiveSignature.Restoration} {u0 : Nat}
    (hFs : envF.OrderedStrong) (hT : decl.addTypes env0 = some envT) (hTs : envT.OrderedStrong)
    (VT : Model.EnvValid envF envT) (hTF : envT ≤ envF) (hb : base ≤ env0)
    (htypes : base.addConstVals decl.typeConstants = some envTypes) (ht : t ∈ decl.types)
    (hrel : InductiveSignature.RestoresFamily r envTypes u0 nt t) : Model.FamSort envF t.name nt.resultLevel := by
  obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  have hTE : envTypes ≤ envT := addConstVals_mono hb htypes hT
  have hfc : envF.constants t.name = some t.toVConstant :=
    hTF.constants (addConstVals_get hT (List.mem_map_of_mem ht))
  exact Model.famSort_of hFs hTs hTF VT hfc (h1.mono hTE) (h2.mono hTE) hlev

end VEnv
end Lean4Lean
