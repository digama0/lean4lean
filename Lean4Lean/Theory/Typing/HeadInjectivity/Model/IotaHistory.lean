import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaStage

/-! # The ι rules of an ordinary block are valid

`PatValid.ordinary`: in the history induction (`Model/EnvValid.lean`), a rule registered by an
inductive declaration whose compilation is ordinary (no container specializations) is valid in
the model of the final environment, by `PatValid.of_rule` with the static data of its generated
equation (`Instance.iotaStatic`, `ordinary_rule_data`) and the relation of its instances'
arguments to the template (`iotaArgRel_of`). -/

namespace Lean4Lean

namespace InductiveSignature.Instance
variable {s : InductiveSignature} (g : Instance s) (index : Fin s.constructors.size)

theorem recDoms_param (owner : Fin s.families.size) {i : Nat} (hi : i < s.params.length) :
    (g.recDoms owner)[i]? = some ((s.params[i]).instL g.levels) := by
  have hl : i < g.params.length := by rw [params_length]; exact hi
  unfold recDoms
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
    List.getElem?_append_left (by simp only [List.length_append]; omega),
    List.getElem?_append_left (by simp only [List.length_append]; omega),
    List.getElem?_append_left hl]
  simp [Instance.params, hi]

theorem eqDoms_field {j : Nat} (hj : j < s.constructors[index].fields.length) :
    (g.eqDoms index)[s.params.length + (s.families.size + s.constructors.size) + j]? =
      some ((((s.fieldTypes s.constructors[index])[j]'(by simp [fieldTypes]; exact hj)).instL
        g.levels).liftN (s.families.size + s.constructors.size) j) := by
  have hl : (g.params ++ g.motives ++ g.minors).length =
      s.params.length + (s.families.size + s.constructors.size) := by
    simp only [List.length_append, params_length, motives_length, minors_length]; omega
  unfold eqDoms
  rw [List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left]
  simp [insertBinders, List.getElem?_map, List.getElem?_zipIdx, fieldTypes]
  exact ⟨_, List.getElem?_eq_getElem (by simpa using hj), rfl⟩

theorem eqLead_index {j : Nat} (hj : j < s.constructors[index].indices.length) :
    (g.eqLead index)[s.params.length + (s.families.size + s.constructors.size) + j]? =
      some (((s.constructors[index].indices[j]).instL g.levels).liftN
        (s.families.size + s.constructors.size) s.constructors[index].fields.length) := by
  unfold eqLead
  rw [List.getElem?_append_right (by simp [length_vars]), length_vars, Nat.add_sub_cancel_left]
  simp [eqIndices, List.getElem?_map]
  exact ⟨_, List.getElem?_eq_getElem (by simpa using hj), rfl⟩

end InductiveSignature.Instance

namespace VEnv
namespace Model

open InductiveSignature

/-- Two ι reducts equal along an equality of their patterns have the same counts. -/
theorem iotaCounts_of_eq {r : Name} {M : Nat} {c : Name} {N : Nat} {r2 : Name} {M2 : Nat} {c2 : Name} {N2 : Nat}
    (R : (SimplePattern.iota r M c N).toPattern.RHS)
    (R2 : (SimplePattern.iota r2 M2 c2 N2).toPattern.RHS)
    {ck : (SimplePattern.iota r M c N).toPattern.Check}
    {ck2 : (SimplePattern.iota r2 M2 c2 N2).toPattern.Check}
    (e : (SimplePattern.iota r M c N).toPattern = (SimplePattern.iota r2 M2 c2 N2).toPattern)
    (h : e ▸ (R, ck) = (R2, ck2)) : R.iotaCounts = R2.iotaCounts := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := iota_toPattern_inj e
  cases h; rfl

/-- **Uniqueness of the rules of a declaration** per head and constructor. -/
theorem patUniq_decl {envF env0 env' : VEnv} {decl : VInductDecl}
    (h0 : env0.WF) (hdecl : decl.WF env0) (hadd : env0.addInduct decl = some env')
    (hpats : ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r →
      (∃ ci, env'.constants p.headConst = some ci) → env'.pats p r)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules) :
    PatUniq envF rec.name ru.ctor (rec.numParams + rec.numMotives + rec.numMinors)
      rec.numIndices ru.ctorParams ru.nfields ru.rhs := by
  intro k' nind' ctor' cnp' nf' rhs' hc' hp2
  have hp3 := hpats _ _ hp2 ⟨_, by
    rw [SimplePattern.iota_headConst]; exact addInduct_rec_find hadd hrec⟩
  rcases addInduct_pats_origin' hadd hp3 with hold | ⟨rec2, hrec2, ru2, hru2, hc2, e, he⟩
  · obtain ⟨_, hc0⟩ := h0.pat_head_declared hold
    rw [SimplePattern.iota_headConst, addInduct_rec_fresh hadd hrec] at hc0; cases hc0
  obtain ⟨hn, hM, hct, hN⟩ := iota_toPattern_inj e
  have hrr := addInduct_recs_name_inj hadd hrec hrec2 hn
  subst hrr
  have hcnt := iotaCounts_of_eq _ _ e he
  rw [SimplePattern.iotaRHS'_iotaCounts] at hcnt
  erw [SimplePattern.iotaRHS_iotaCounts] at hcnt
  simp only [Option.some.injEq, Prod.mk.injEq] at hcnt
  obtain ⟨rfl, hk', hnf'⟩ := hcnt
  refine ⟨hM, fun hctor => ?_⟩
  have hru2 : ru2 = ru := VEnv.inj_on_of_nodup_map (hdecl.rules_nodup rec hrec) hru2 hru
    (hct.symm.trans hctor)
  subst hru2
  refine ⟨hk', ?_, ?_, hnf', rfl⟩
  · simp only [VRecursor.getMajorIdx] at hM; omega
  · omega

theorem forallResult_of_const_head {e : VExpr} {c : Name} {ls : List VLevel}
    (h : e.getAppFnArgs.1 = .const c ls) : e.forallResult = e := by
  cases e with
  | forallE A B => simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at h
  | _ => rfl

/-- **The source family and constructor of a generated equation** (ordinary compilations): the
family and constructor of the source declaration behind the normalized ones, the restoration
relating the families, the definitional equality of the normalized constructor type with the
source's, and the source constructor's raw shape. -/
theorem ordinary_ctor_data {base : VEnv} {decl expanded : VInductDecl} {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {block : VInductBlock}
    (C : InductiveSignature.CompilationData base decl expanded s g [] block)
    (index : Fin s.constructors.size) :
    ∃ envTypes, base.addConstVals decl.typeConstants = some envTypes ∧
    ∃ t ∈ decl.types, t.name = s.families[s.constructors[index].owner].name ∧
    (∃ r, InductiveSignature.RestoresFamily r envTypes decl.uvars
      (s.declarationFamily s.constructors[index].owner) t) ∧
    ∃ fc ∈ t.ctors, fc.name = s.constructors[index].name ∧
      envTypes.IsDefEqU decl.uvars [] (s.constructorType s.constructors[index]) fc.type ∧
      decl.RawCtorShape t fc := by
  obtain ⟨envTypes, direct, htypes, hdirect, -, hfamilies⟩ := C.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem s.constructors[index].owner)
  rw [List.append_nil] at hfamily
  obtain ⟨fc, hfc, hn, -, hrt⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _
    (s.declarationCtor_family index)
  obtain ⟨restored, hr, hdf⟩ := hrt
  rw [compilationRestoration_nil, Restoration.expr_empty] at hr
  cases hr
  obtain ⟨_, _, _, _, _, hraw⟩ := C.sourceParameters
  exact ⟨envTypes, htypes, family, hfamily, hrel.name.symm, ⟨_, hrel⟩, fc, hfc, hn.symm, hdf,
    hraw family hfamily fc hfc⟩

/-- The expanded declaration of an ordinary compilation has the source's type formers. -/
theorem ordinary_expanded_types {base : VEnv} {decl expanded : VInductDecl}
    {s : InductiveSignature} {g : InductiveSignature.Instance s} {block : VInductBlock}
    (C : InductiveSignature.CompilationData base decl expanded s g [] block) :
    expanded.typeConstants = decl.typeConstants := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := C.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  have h1 := Lean4Lean.List.Forall₂.length_eq hfamilies
  have h2 := Lean4Lean.List.Forall₂.length_eq C.model.families
  rw [C.headerPrefix, List.take_of_length_le]
  simp only [VInductDecl.typeConstants, List.length_map] at h1 h2 ⊢
  simp at h1
  omega

/-- The binder type of the motive of a generated equation is a telescope ending in the
target sort. -/
theorem motive_binderTy {s : InductiveSignature} (g : InductiveSignature.Instance s)
    (index : Fin s.constructors.size) (ls : List VLevel) :
    ∃ mds : List VExpr, binderTy (g.eqDoms index) ls
      (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)) =
      .wrapForalls mds (.sort (g.targetLevel.inst ls)) ∧
      mds.length = s.families[s.constructors[index].owner].indices.length + 1 := by
  have hlen := g.eqDoms_length index
  have ho := s.constructors[index].owner.isLt
  have e1 : (g.eqDoms index).reverse.getD (s.constructors[index].fields.length +
      s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val)) default =
      g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega)]
    rw [show (g.eqDoms index).length - 1 - (s.constructors[index].fields.length +
      s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val)) =
      s.params.length + s.constructors[index].owner.val by omega]
    simp only [Instance.eqDoms, List.append_assoc]
    rw [List.getElem?_append_right (by simp [Instance.params]),
      List.getElem?_append_left (by simp [Instance.params, Instance.motives])]
    simp [Instance.params, Instance.motives]
  obtain ⟨ds0, e0, l0⟩ : ∃ ds0 : List VExpr,
      g.motive s.families[s.constructors[index].owner] s.constructors[index].owner.val =
        .wrapForalls ds0 (.sort g.targetLevel) ∧
      ds0.length = s.families[s.constructors[index].owner].indices.length + 1 :=
    ⟨_, rfl, by simp [insertBinders]⟩
  unfold binderTy
  rw [e1, e0]
  obtain ⟨ds', h, l⟩ := liftN_wrapForalls_sort (w := g.targetLevel) ds0
    (s.constructors[index].fields.length + s.constructors.size +
      (s.families.size - 1 - s.constructors[index].owner.val) + 1) 0
  refine ⟨ds'.map (·.instL ls), ?_, by simp [l, l0]⟩
  rw [h, VExpr.instL_wrapForalls]
  rfl

/-- The reduct of a rule typed in an environment valid in the model of `envF`: its type is a
type and it is soundly typed at its type, at every instantiation of its levels. -/
theorem eq_rhs_sound {envF envR : VEnv} (hFs : envF.OrderedStrong) (hRs : envR.OrderedStrong)
    (hRF : envR ≤ envF) (VR : EnvValid envF envR) {df : VDefEq} (hwf : df.WF envR)
    {U : Nat} {Δ : List VExpr} (hΔ : OnCtx Δ (envF.IsType U)) {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF U) :
    (∃ u, HTS envF U Δ [] (df.type.instL m1) (.sort u)) ∧
    HTS envF U Δ [] (df.rhs.instL m1) (df.type.instL m1) ∧
    SoundAt envF U Δ [] (df.rhs.instL m1) (df.rhs.instL m1) (df.type.instL m1) := by
  have h : envR.HasType U [] (df.rhs.instL m1) (df.type.instL m1) := hwf.2.instL hm1
  have st := IsDefEq.strong hRs (Γ := []) trivial h
  obtain ⟨S, H, -⟩ := VR.soundAtH hFs hRF U Δ hΔ st
  obtain ⟨u, hu⟩ := h.isType hRs.ordered (show OnCtx [] (envR.IsType U) from trivial)
  obtain ⟨-, HT, -⟩ := VR.soundAtH hFs hRF U Δ hΔ (IsDefEq.strong hRs (Γ := []) trivial hu)
  exact ⟨⟨u, HT⟩, H, S⟩

theorem eq_bvar_of_liftN {e : VExpr} {n k x : Nat} (h : e.liftN n k = .bvar x) (hx : x < k) :
    e = .bvar x := by
  cases e with
  | bvar i =>
    simp only [VExpr.liftN, VExpr.bvar.injEq, liftVar] at h
    split at h <;> [exact congrArg _ h; omega]
  | _ => simp [VExpr.liftN] at h

theorem eq_bvar_of_instL {e : VExpr} {ls : List VLevel} {x : Nat} (h : e.instL ls = .bvar x) :
    e = .bvar x := by
  cases e <;> simp_all [VExpr.instL]

theorem vars_getElem? {count below i : Nat} (hi : i < count) :
    (vars count below)[i]? = some (.bvar (below + (count - 1 - i))) := by
  simp only [vars_unfold, List.getElem?_map]
  rw [List.getElem?_reverse (by simpa using hi)]
  simp only [List.length_range]
  rw [List.getElem?_range (by omega)]
  rfl

theorem forallArity_mkApps_const' (c : Name) (ls : List VLevel) : ∀ args : List VExpr,
    (VExpr.mkApps (.const c ls) args).forallArity = 0 := by
  intro args
  induction args using List.reverseRecOn with
  | nil => rfl
  | snoc args a _ => rw [VExpr.mkApps_snoc]; rfl

theorem eq_mkApps_of_getAppFnArgs {e f : VExpr} (h : e.getAppFnArgs.1 = f) :
    e = .mkApps f e.getAppFnArgs.2 := by
  have := VExpr.mkApps_getAppFnArgs_go e []
  rw [← h]; exact this.symm

set_option maxHeartbeats 4000000 in
/-- **The relation of the instances of an ordinary rule to its template** (`IotaArgRel`). -/
theorem ordinary_rel {envF env0 envT envR base envTypes : VEnv} {decl : VInductDecl}
    {s : InductiveSignature} {g : InductiveSignature.Instance s}
    (henvF : envF.OrderedStrong) (h0s : env0.OrderedStrong) (V0 : EnvValid envF env0)
    (h0F : env0 ≤ envF) (hTs : envT.OrderedStrong) (VT : EnvValid envF envT) (hTF : envT ≤ envF)
    (hRs : envR.OrderedStrong) (VR : EnvValid envF envR) (hRF : envR ≤ envF)
    (hbase : base ≤ env0) (hET : envTypes ≤ envT)
    (index : Fin s.constructors.size) {n ctor : Name}
    (hci : envF.constants n = some (g.recursor s.constructors[index].owner).toVConstant)
    {t : VInductiveType} (htn : t.name = s.families[s.constructors[index].owner].name)
    (hcI : envF.constants t.name = some t.toVConstant)
    {params : List VExpr} (hshapeT : decl.TypeShape base params t)
    (hnp : decl.nparams = s.params.length)
    (hnI : t.numIndices = s.families[s.constructors[index].owner].indices.length)
    (hIrig : envF.Rigid t.name)
    {fc : VConstVal} (hcc : envF.constants ctor = some fc.toVConstant)
    (hraw : decl.RawCtorShape t fc) (htuniq : ∀ t' ∈ decl.types, t'.name = t.name → t' = t)
    (hfcA : fc.type.forallArity = decl.nparams + s.constructors[index].fields.length)
    (hfcu : fc.uvars = decl.uvars)
    (hdfU : envTypes.IsDefEqU decl.uvars [] (s.constructorType s.constructors[index]) fc.type)
    (hdfWF : (g.equation index).WF envR)
    (harity : s.constructors[index].indices.length =
      s.families[s.constructors[index].owner].indices.length) :
    ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (envF.IsType U) →
      ∀ (Γ : List VExpr) (m1 lsC : List VLevel) (recArgs ctorArgs : List VExpr) (A : VExpr),
      recArgs.length = s.params.length + (s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length →
      ctorArgs.length = s.params.length + s.constructors[index].fields.length →
      HTS envF U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A →
      ∀ σ S, Ctx.SubstEq envF U Δ σ σ Γ → TV envF U Δ Γ σ S →
        IotaArgRel envF U Δ Γ n ctor m1 lsC s.params.length s.constructors[index].fields.length
          (g.eqDoms index) (g.eqLead index) recArgs ctorArgs
          (recArgs.take (s.params.length + (s.families.size + s.constructors.size)) ++
            ctorArgs.drop s.params.length) σ S ∧
        List.Forall₂ (· ≈ ·) lsC (g.levels.map (·.inst m1)) := by
  intro U Δ hΔ Γ m1 lsC recArgs ctorArgs A hrA hcA ihe σ S W tv
  -- the levels of the instance
  obtain ⟨ci1, hci1, hm1, hlen1⟩ := HTS.spine_levels ihe
  obtain ⟨Amaj, Bm, -, hmaj, -⟩ := HTS.spine_at _ rfl ihe recArgs.length (by simp)
  rw [List.getElem_append_right (by omega)] at hmaj
  simp only [Nat.sub_self, List.getElem_singleton] at hmaj
  obtain ⟨cc1, hcc1, hlsC, hlenC⟩ := HTS.spine_levels hmaj
  rw [hcc] at hcc1; cases hcc1
  have hlsI : ∀ l ∈ g.levels.map (·.inst m1), l.WF U := by
    intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hm1
  -- the family's telescope
  obtain ⟨N, ownP, afterP, idxs, res, X, hN, htf1, htf2, -, -⟩ := hshapeT
  obtain ⟨e1, l1⟩ := VExpr.takeForalls_eq_wrapForalls htf1
  obtain ⟨e2, l2⟩ := VExpr.takeForalls_eq_wrapForalls htf2
  subst e1 e2
  rw [← VExpr.wrapForalls_append] at hN
  have hNi : env0.IsDefEq U [] (t.type.instL (g.levels.map (·.inst m1)))
      ((VExpr.wrapForalls (ownP ++ idxs) res).instL (g.levels.map (·.inst m1)))
      (X.instL (g.levels.map (·.inst m1))) := IsDefEq.instL hlsI (hN.mono hbase)
  obtain ⟨SN, -, HN⟩ := V0.soundAtH henvF h0F U Δ hΔ (IsDefEq.strong h0s (Γ := []) trivial hNi)
  rw [VExpr.instL_wrapForalls] at SN HN
  -- the installed constructor
  obtain ⟨cdoms, result, hty, -, hvalid, hhead⟩ := hraw
  have hres := eq_mkApps_of_getAppFnArgs hhead
  have hcdl : cdoms.length = s.params.length + s.constructors[index].fields.length := by
    have := VExpr.forallArity_wrapForalls cdoms result
    rw [← hty, hfcA, hnp] at this
    rw [hres, forallArity_mkApps_const'] at this
    omega
  -- the installed constructor's own typing
  obtain ⟨cc2, -, hcc2, hlsC2, ⟨uC, hTc, hTcsd⟩, -, -, -, -, -⟩ :=
    hmaj.spine henvF hΔ rfl W tv (ctorArgs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  rw [hcc] at hcc2; cases hcc2
  have hlsC' : (VLevel.params decl.uvars).map (·.inst lsC) = lsC :=
    VLevel.inst_map_id (by rw [hlenC]; exact hfcu)
  have eC : fc.toVConstant.type.instL lsC = .wrapForalls (cdoms.map (·.instL lsC))
      (.mkApps (.const s.families[s.constructors[index].owner].name
        ((VLevel.params decl.uvars).map (·.inst lsC))) (result.getAppFnArgs.2.map (·.instL lsC))) := by
    show fc.type.instL lsC = _
    rw [hty, VExpr.instL_wrapForalls]; congr 1
    conv => lhs; rw [hres]
    rw [VExpr.instL_mkApps, htn]; rfl
  -- the template
  obtain ⟨⟨u, hTH⟩, -, -⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
  have hty' : (g.equation index).type = .wrapForalls (g.eqDoms index)
      (.mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)))
        (g.eqIndices index ++ [g.constructorApp s.constructors[index]
          (s.families.size + s.constructors.size) 0])) := rfl
  rw [hty', VExpr.instL_wrapForalls] at hTH
  have hdomsSD : DomsSD envF U Δ [] ((g.eqDoms index).map (·.instL m1)) := (HTS.piSD hTH).doms
  have eH : (g.recursor s.constructors[index].owner).toVConstant.type.instL m1 =
      .wrapForalls ((g.recDoms s.constructors[index].owner).map (·.instL m1))
        ((g.recBody s.constructors[index].owner).instL m1) := by
    show (g.recursor s.constructors[index].owner).type.instL m1 = _
    rw [g.recursorType_eq_recDoms, VExpr.instL_wrapForalls]
  have hlenH : ((g.recDoms s.constructors[index].owner).map (·.instL m1)).length =
      s.params.length + (s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length + 1 := by
    rw [List.length_map, g.recDoms_length]
  have hkH : ((g.recDoms s.constructors[index].owner).map (·.instL m1))[s.params.length +
      (s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length]? =
      some (.mkApps (.const s.families[s.constructors[index].owner].name
        (g.levels.map (·.inst m1)))
        (vars s.params.length ((s.families.size + s.constructors.size) +
          s.families[s.constructors[index].owner].indices.length) ++
          vars s.families[s.constructors[index].owner].indices.length 0)) := by
    rw [List.getElem?_map, g.recDoms_major]
    simp only [Option.map_some, VExpr.instL_mkApps, VExpr.instL, List.map_append, vars_instL]
  have hDK : ∀ i < s.params.length + (s.families.size + s.constructors.size),
      ((g.eqDoms index).map (·.instL m1))[i]? =
        ((g.recDoms s.constructors[index].owner).map (·.instL m1))[i]? := by
    intro i hi
    have hl : i < (g.params ++ g.motives ++ g.minors).length := by
      simp only [List.length_append, Instance.params_length, Instance.motives_length,
        Instance.minors_length]; omega
    rw [List.getElem?_map, List.getElem?_map]
    unfold Instance.eqDoms Instance.recDoms
    rw [List.append_assoc (g.params ++ g.motives ++ g.minors), List.getElem?_append_left hl,
      List.getElem?_append_left hl]
  have hleadK : ∀ i < s.params.length + (s.families.size + s.constructors.size),
      (g.eqLead index)[i]? = some (.bvar (s.params.length +
        (s.families.size + s.constructors.size) - 1 - i + s.constructors[index].fields.length)) := by
    intro i hi
    simp only [Instance.eqLead]
    rw [List.getElem?_append_left (by simp [length_vars]; omega), vars_getElem? hi]
    congr 2; omega
  have hleadl : (g.eqLead index).length = s.params.length +
      (s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length := by
    rw [g.eqLead_length, harity]
  -- the major's family
  have hFlip : List.Forall₂ (· ≈ ·) ((VLevel.params decl.uvars).map (·.inst lsC))
      (g.levels.map (·.inst m1)) → List.Forall₂ (· ≈ ·) (g.levels.map (·.inst m1)) lsC := by
    intro h; rw [hlsC'] at h; exact forall₂_equiv_symm h
  have hcI' : envF.constants s.families[s.constructors[index].owner].name = some t.toVConstant :=
    htn ▸ hcI
  have hIrig' : envF.Rigid s.families[s.constructors[index].owner].name := htn ▸ hIrig
  have hITW := (SN .id .id .empty .nil TV.empty TV.empty).1
  have hIpi := HTS.piSD HN
  have hDIl : s.params.length + s.families[s.constructors[index].owner].indices.length ≤
      ((ownP ++ idxs).map (·.instL (g.levels.map (·.inst m1)))).length := by
    simp only [List.length_map, List.length_append]; omega
  have hiargsP : ∀ i < s.params.length,
      (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length) ++
        vars s.families[s.constructors[index].owner].indices.length 0)[i]? =
      some (.bvar (s.params.length + (s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length - 1 - i)) := by
    intro i hi
    rw [List.getElem?_append_left (by simp [length_vars]; omega), vars_getElem? hi]
    congr 2; omega
  have hiargsI : ∀ j < s.families[s.constructors[index].owner].indices.length,
      (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length) ++
        vars s.families[s.constructors[index].owner].indices.length 0)[s.params.length + j]? =
      some (.bvar (s.families[s.constructors[index].owner].indices.length - 1 - j)) := by
    intro j hj
    rw [List.getElem?_append_right (by simp [length_vars]), length_vars, Nat.add_sub_cancel_left,
      vars_getElem? hj]
    congr 2; omega
  have hiargsl : (vars s.params.length ((s.families.size + s.constructors.size) +
        s.families[s.constructors[index].owner].indices.length) ++
        vars s.families[s.constructors[index].owner].indices.length 0).length =
      s.params.length + s.families[s.constructors[index].owner].indices.length := by
    simp [length_vars]
  by_cases hz : s.params.length + s.constructors[index].fields.length = 0
  · -- no binders: the installed constructor type is its own normal form
    have hcd0 : cdoms = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hcd0
    rcases hga : result.getAppFnArgs with ⟨fn, args⟩
    simp only [VInductDecl.RawIndAppAt, hga] at hvalid
    obtain ⟨type', htype', hor, lv, -, -, hal, -⟩ := hvalid
    have hal' : result.getAppFnArgs.2.length = decl.nparams + type'.numIndices := by
      rw [hga]; exact hal
    have htt : type' = t := htuniq type' htype' (by
      rcases hor with h | h
      · cases h
      · exact (Option.some.inj h).symm)
    rw [htt] at hal'
    have hTc' := hTc; rw [eC] at hTc'
    have hTcsd' := hTcsd; rw [eC] at hTcsd'
    have hCcl : (fc.toVConstant.type.instL lsC).ClosedN := (henvF.ordered.closedC hcc).instL
    rw [eC] at hCcl
    obtain ⟨h1, h2⟩ := iotaArgRel_of henvF hΔ hci eH hlenH hkH hiargsl hiargsP hiargsI hcI' hITW
      hIpi hDIl hIrig' hcc eC (by simp; omega) hCcl hTc' hTcsd'
      (by rw [eC]; exact hTcsd'.2) (by simp; omega)
      (by simp only [List.length_map]; rw [hal', hnp, hnI]) (fun i hi => by omega)
      (g.eqDoms_length index) (fun _ i hi => by omega) hDK (fun _ j hj => by omega) hleadK
      (fun j x _ hx => by omega) hleadl hdomsSD hrA hcA rfl ihe W tv
    exact ⟨h1, by rwa [hlsC'] at h2⟩
  · -- the normalized constructor type
    obtain ⟨uv, hdfU'⟩ := hdfU
    have hNc : envT.IsDefEq U [] (fc.type.instL lsC)
        ((s.constructorType s.constructors[index]).instL lsC) (uv.instL lsC) :=
      IsDefEq.instL hlsC (hdfU'.symm.mono hET)
    obtain ⟨SC, -, -⟩ := VT.soundAtH henvF hTF U Δ hΔ (IsDefEq.strong hTs (Γ := []) trivial hNc)
    have hNcl := (hNc.hasType.2.closedN' hTs.ordered.closed (Γ := []) ⟨⟩).1
    have hcT : (s.constructorType s.constructors[index]).instL lsC =
        .wrapForalls ((s.params ++ s.fieldTypes s.constructors[index]).map (·.instL lsC))
          (.mkApps (.const s.families[s.constructors[index].owner].name
            ((VLevel.params s.uvars).map (·.inst lsC)))
            (vars s.params.length s.constructors[index].fields.length ++
              s.constructors[index].indices.map (·.instL lsC))) := by
      simp only [constructorType, familyApp, VExpr.instL_wrapForalls, VExpr.instL_mkApps,
        VExpr.instL, List.map_append, vars_instL]
    have hTy2 := hNc.hasType.2
    rw [hcT] at hTy2 hNcl SC
    have hDl : ((s.params ++ s.fieldTypes s.constructors[index]).map (·.instL lsC)).length =
        s.params.length + s.constructors[index].fields.length := by simp [fieldTypes]
    obtain ⟨A0, ds0, hds0⟩ : ∃ A0 ds0,
        (s.params ++ s.fieldTypes s.constructors[index]).map (·.instL lsC) = A0 :: ds0 := by
      cases h : (s.params ++ s.fieldTypes s.constructors[index]).map (·.instL lsC) with
      | nil => rw [h, List.length_nil] at hDl; omega
      | cons A0 ds0 => exact ⟨A0, ds0, rfl⟩
    rw [hds0] at hTy2
    obtain ⟨⟨u1, hA⟩, ⟨v1, hB⟩⟩ := HasType.forallE_inv hTs.ordered hTy2
    have hsort : envT.HasType U [] (.wrapForalls (A0 :: ds0) (.mkApps
        (.const s.families[s.constructors[index].owner].name
          ((VLevel.params s.uvars).map (·.inst lsC)))
        (vars s.params.length s.constructors[index].fields.length ++
          s.constructors[index].indices.map (·.instL lsC)))) (.sort (.imax u1 v1)) :=
      .forallEDF hA hB
    rw [← hds0] at hsort
    have stN := IsDefEq.strong hTs (Γ := []) trivial hsort
    obtain ⟨SN2, HN2, -⟩ := VT.soundAtH henvF hTF U Δ hΔ stN
    obtain ⟨h1, h2⟩ := iotaArgRel_of henvF hΔ hci eH hlenH hkH hiargsl hiargsP hiargsI hcI' hITW
      hIpi hDIl hIrig' hcc eC (by simp; omega) hNcl HN2 ⟨stN.mono hTF, SN2⟩ SC hDl
      (by simp only [List.length_append, List.length_map, length_vars]; rw [harity])
      (fun i hi => by
        rw [List.getElem?_append_left (by simp [length_vars]; omega), vars_getElem? hi]
        congr 2; omega)
      (g.eqDoms_length index)
      (fun h i hi => by
        refine ⟨(s.params[i]).instL (g.levels.map (·.inst m1)), (s.params[i]).instL lsC,
          ?_, ?_, ?_⟩
        · rw [List.getElem?_map, g.recDoms_param _ hi]
          simp [VExpr.instL_instL]
        · rw [List.getElem?_map, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]; rfl
        · exact LvEq.instL _ hlsI hlsC (hFlip h))
      hDK
      (fun h j hj => by
        have hjF : j < (s.fieldTypes s.constructors[index]).length := by simpa [fieldTypes] using hj
        refine ⟨((s.fieldTypes s.constructors[index])[j].liftN
            (s.families.size + s.constructors.size) j).instL (g.levels.map (·.inst m1)),
          (s.fieldTypes s.constructors[index])[j].instL lsC, ?_, ?_, ?_⟩
        · rw [List.getElem?_map, g.eqDoms_field index hj]
          simp [VExpr.instL_instL]
        · rw [List.getElem?_map, List.getElem?_append_right (by omega),
            Nat.add_sub_cancel_left, List.getElem?_eq_getElem hjF]; rfl
        · rw [← VExpr.instL_liftN]
          exact LvEq.instL _ hlsI hlsC (hFlip h))
      hleadK
      (fun j x hx hxf => by
        have hj : j < s.constructors[index].indices.length := by
          refine Nat.lt_of_not_le fun hj' => ?_
          rw [List.getElem?_eq_none (by rw [g.eqLead_length]; omega)] at hx; cases hx
        rw [g.eqLead_index index hj] at hx
        have e1 := eq_bvar_of_instL (eq_bvar_of_liftN (Option.some.inj hx) hxf)
        rw [List.getElem?_append_right (by simp [length_vars]), length_vars, Nat.add_sub_cancel_left,
          List.getElem?_map, List.getElem?_eq_getElem hj, e1]; rfl)
      hleadl hdomsSD hrA hcA rfl ihe W tv
    exact ⟨h1, by rwa [hlsC'] at h2⟩

set_option maxHeartbeats 4000000 in
/-- **Validity of the ι rules of an ordinary block.** -/
theorem PatValid.ordinary {envF env0 env' : VEnv} {decl : VInductDecl}
    (hF : envF.WF) (h0 : env0.WF) (hdecl : decl.WF env0)
    (hadd : env0.addInduct decl = some env') (hle : env' ≤ envF)
    (V0 : EnvValid envF env0)
    (hprojV : ∀ S info, env'.projections S info → ProjValid envF S info)
    (hpats : ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r →
      (∃ ci, env'.constants p.headConst = some ci) → env'.pats p r)
    (hdefs : ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      (∃ ci, env'.constants n = some ci) → env'.defeqs df)
    (hrigT : ∀ t ∈ decl.types, envF.Rigid t.name)
    (hctor : ∀ c, IsCtor envF c → envF.Rigid c) (hpctor : ∀ c, IsProjCtor envF c → envF.Rigid c)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    (hc : ru.rhs.Closed)
    {block : VInductBlock} {base : VEnv} {expanded : VInductDecl} {s : InductiveSignature}
    {g : InductiveSignature.Instance s}
    (hcomp : CompiledInductive env0 decl block)
    (hrecsOf : decl.RecsOf block) (hbwf : block.WF env0) (hbase : base ≤ env0)
    (C : InductiveSignature.CompilationData base decl expanded s g [] block)
    {df : VDefEq} (hdf : df ∈ block.rules) (H : VRecRule.OfEquation rec ru df) :
    PatValid envF
      (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
        rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  have henvF := hF.orderedStrong
  have hp' := hle.pats (addInduct_pat hrec hru hc hadd)
  have hci' := hle.constants (addInduct_rec_find hadd hrec)
  obtain ⟨index, rfl, hrv, hctorN, hrhs, hk, hnI, hcp, hnf, harity⟩ :=
    ordinary_rule_data hdecl hrecsOf C hrec hru hdf H
  -- the rules registered at the recursor, when it has a single rule
  have hheadU : (∀ ru2 ∈ rec.rules, ru2 = ru) → ∀ (p' : Pattern) (r' : p'.RHS × p'.Check),
      envF.pats p' r' → p'.headConst = rec.name →
      ∃ h : p' = (SimplePattern.iota rec.name
        (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
        (ru.ctorParams + ru.nfields)).toPattern,
        h ▸ r' = (SimplePattern.iotaRHS' rec.name ru.ctor
          (rec.numParams + rec.numMotives + rec.numMinors) rec.numIndices ru.ctorParams
          ru.nfields ru.rhs hc, .true) := by
    intro hall p' r' hp2 hh
    have hp3 := hpats _ _ hp2 ⟨_, by rw [hh]; exact addInduct_rec_find hadd hrec⟩
    rcases addInduct_pats_origin' hadd hp3 with hold | ⟨rec2, hrec2, ru2, hru2, hc2, e, he⟩
    · obtain ⟨_, hc0⟩ := h0.pat_head_declared hold
      rw [hh, addInduct_rec_fresh hadd hrec] at hc0; cases hc0
    subst e
    rw [SimplePattern.iota_headConst] at hh
    have := addInduct_recs_name_inj hadd hrec2 hrec hh
    subst this
    have := hall ru2 hru2
    subst this
    exact ⟨rfl, he⟩
  -- the family and the constructor
  obtain ⟨envTypes, htypes, t, ht, htn, ⟨rr, hrelF⟩, fc, hfc, hfcn, hdfU, hraw⟩ :=
    ordinary_ctor_data C index
  have hnp : decl.nparams = s.params.length := (C.model.nparams.trans C.nparams).symm
  obtain ⟨envT, envC, envR, sT, sC, sR, sP⟩ := addInduct_stages hadd
  have hTC : decl.addTypesCtors env0 = some envC := by
    unfold VInductDecl.addTypesCtors; rw [sT]; exact sC
  have hfcA : fc.type.forallArity = decl.nparams + s.constructors[index].fields.length := by
    obtain ⟨cc, hcc, hsh, -⟩ := hdecl.rules_ctor envC hTC rec hrec ru hru
    rw [hctorN, ← hfcn, addCtors_find sC t ht fc hfc] at hcc
    cases hcc
    rw [← VExpr.piArity_eq_forallArity]
    change fc.type.piArity = _ at hsh
    rw [hsh, hcp, hnf, hnp]
  have hci : envF.constants rec.name =
      some (g.recursor s.constructors[index].owner).toVConstant := by
    rw [hci', show rec.toVConstVal.toVConstant = (g.recursor s.constructors[index].owner).toVConstant
      from congrArg (·.toVConstant) hrv]
  have hu := patUniq_decl h0 hdecl hadd hpats hrec hru (envF := envF)
  show PatValid envF (SimplePattern.iota rec.name
      (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern
    (SimplePattern.iotaRHS' rec.name ru.ctor (rec.numParams + rec.numMotives + rec.numMinors)
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true)
  change envF.pats (SimplePattern.iota rec.name
      (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern
    (SimplePattern.iotaRHS' rec.name ru.ctor (rec.numParams + rec.numMotives + rec.numMinors)
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) at hp'
  generalize rec.numParams + rec.numMotives + rec.numMinors = k at hk hp' hu hheadU ⊢
  generalize rec.numIndices = nind at hnI hp' hu hheadU ⊢
  generalize ru.ctorParams = cnp at hcp hp' hu hheadU ⊢
  generalize ru.nfields = nf at hnf hp' hu hheadU ⊢
  subst hk hnI hcp hnf
  have hr : ru.rhs = .wrapLams (g.eqDoms index) (g.eqBody index) := by
    rw [hrhs]; rfl
  have hstat := g.iotaStatic index harity (fun i h => C.ctor_index_inj h)
  rw [← hctorN] at hstat
  have hcis : IsCtor envF ru.ctor := .inr ⟨_, _, rec.name, _, _, hp', rfl⟩
  have hnodf : ∀ df', envF.defeqs df' → ∀ ls',
      df'.lhs.stripLams.getAppFnArgs.1 ≠ .const rec.name ls' := by
    intro df' hdf' ls' hh
    have h1 := hdefs df' hdf' _ _ hh ⟨_, addInduct_rec_find hadd hrec⟩
    rw [addInduct_defeqs hadd] at h1
    obtain ⟨_, hc0⟩ := (h0.ordered.defEqWF h1).1.head_const_lookup h0.orderedStrong (Γ := []) ⟨⟩ hh
    rw [addInduct_rec_fresh hadd hrec] at hc0; cases hc0
  have hIrig : envF.Rigid s.families[s.constructors[index].owner].name := htn ▸ hrigT t ht
  have hcf : CtorFam envF ru.ctor s.families[s.constructors[index].owner].name := by
    obtain ⟨doms, result, hty, -, -, hhead⟩ := hraw
    refine ⟨fc.toVConstant, VLevel.params decl.uvars, by
      rw [hctorN, ← hfcn]; exact addInduct_ctor_find hadd ht hfc |> hle.constants, ?_⟩
    show fc.type.forallResult.getAppFnArgs.1 = _
    rw [hty, VExpr.forallResult_wrapForalls, forallResult_of_const_head hhead, hhead, htn]
  -- the stage environments
  obtain ⟨hTs, hRs⟩ := stages_orderedStrong h0 hdecl sT sC sR
  obtain ⟨VT, VR⟩ := stages_envValid V0 hprojV sT sC sR sP
  have hRF : envR ≤ envF := (addRules_le sP).trans hle
  have hTF : envT ≤ envF :=
    (addCtors_le sC).trans (addProjs_le.trans ((addRecs_le sR).trans hRF))
  have hR' : decl.addTypesCtorsProjsRecs env0 = some envR := by
    unfold VInductDecl.addTypesCtorsProjsRecs; rw [addTypesCtorsProjs_eq_some hTC]; exact sR
  have hdfWF := VInductDecl.WF.block_rules_wf hcomp hrecsOf hbwf hR' _ hdf
  have hallpat : ∀ c2 ∈ t.ctors, IsPatCtor envF c2.name := by
    intro c2 hc2
    obtain ⟨df2, hdf2, hmaj⟩ := hcomp.constructor_equation c2 (List.mem_flatMap.2 ⟨t, ht, hc2⟩)
    obtain ⟨r2, hr2, ru2, hru2, hof⟩ := hrecsOf.rules_total df2 hdf2
    have hn := hmaj.ofEquation hof
    obtain ⟨index2, rfl, -, -, hrhs2, -⟩ := ordinary_rule_data hdecl hrecsOf C hr2 hru2 hdf2 hof
    have hc2' : ru2.rhs.Closed := by
      rw [hrhs2]
      exact ((VInductDecl.WF.block_rules_wf hcomp hrecsOf hbwf hR' _ hdf2).2.closedN'
        hRs.ordered.closed (Γ := []) ⟨⟩).1
    exact ⟨_, _, r2.name, r2.getMajorIdx, ru2.ctorParams + ru2.nfields,
      hle.pats (addInduct_pat hr2 hru2 hc2' hadd), by rw [hn]⟩
  have hpm := projMajor_decl hF hdecl hadd hle hprojV ht hfc hallpat hfcA
  rw [htn, hfcn, hnp, ← hctorN] at hpm
  have hfs : FamSort envF s.families[s.constructors[index].owner].name
      s.families[s.constructors[index].owner].resultLevel := by
    have := famSort_decl henvF sT hTs VT hTF hbase htypes ht hrelF
    rwa [htn] at this
  have hL : t.resultLevel ≈ s.families[s.constructors[index].owner].resultLevel :=
    Eq.symm hrelF.resultLevel
  have hT' := sT
  rw [VInductDecl.addTypes_eq_addConstVals] at hT'
  have hET : envTypes ≤ envT := addConstVals_mono hbase htypes hT'
  have hcIF : envF.constants t.name = some t.toVConstant :=
    hTF.constants (addConstVals_get hT' (List.mem_map_of_mem ht))
  obtain ⟨params, -, -, hshapes, -, -⟩ := C.sourceParameters
  have htuniq : ∀ t' ∈ decl.types, t'.name = t.name → t' = t := fun t' ht' e =>
    VEnv.inj_on_of_nodup_map (addTypes_nodup sT) ht' ht e
  have hfcu : fc.uvars = decl.uvars :=
    hdecl.source.2.2.2.1 fc (List.mem_flatMap.2 ⟨t, ht, hfc⟩)
  have hccF : envF.constants ru.ctor = some fc.toVConstant := by
    rw [hctorN, ← hfcn]; exact hle.constants (addInduct_ctor_find hadd ht hfc)
  have hrel := ordinary_rel henvF h0.orderedStrong V0 ((addTypes_le sT).trans hTF) hTs VT hTF
    hRs VR hRF hbase hET index hci htn hcIF (hshapes t ht) hnp hrelF.indices.symm (hrigT t ht)
    hccF hraw htuniq hfcA hfcu hdfU hdfWF harity
  have hpm' : ProjMajor envF s.families[s.constructors[index].owner].name ru.ctor
      (eqMs index).length (iotaFs s.constructors[index].fields.length).length t.resultLevel := by
    rw [Instance.eqMs_length, iotaFs_length]; exact hpm
  obtain ⟨envE, hE, hadm⟩ := C.admissible
  rcases hadm.elimination with hnz | hsmall | ⟨hsing, -⟩
  · -- families never in `Prop`: mode C is impossible
    have hnz' := hnz s.families[s.constructors[index].owner]
      (Array.mem_toList_iff.2 (Array.getElem_mem s.constructors[index].owner.isLt))
    refine PatValid.of_rule henvF hp' hr hci hstat hu (g.equation_cov index) hIrig hcf hcis
      (hctor _ hcis) hctor hpctor hnodf (ms := eqMs index) (Instance.eqMs_length index) ?_ hrel
    intro U Δ hΔ m1 hm1 hlen1
    obtain ⟨-, hRH, hRS⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
    refine ⟨hpm'.majorFam (.inl ?_), fun keys hkl hobs => ?_,
      (g.equation index).type.instL m1, by rw [hrhs]; exact hRH, by rw [hrhs]; exact hRS⟩
    · rw [← VLevel.inst_inst]
      exact (hnz'.of_equiv (VLevel.inst_congr_l (Eq.symm hL))).inst
    · exact (C_absurd_gen hΔ hm1 hstat.2.1 hstat.2.2.1 hstat.2.2.2.1 hIrig hfs
        hnz'.inst (by rw [hkl, hstat.lead_length]) hobs).elim
  · -- small elimination: the reduct has no observations
    refine PatValid.of_rule_empty henvF hp' hr hci hstat hu (hctor _ hcis) hctor hpctor hnodf
      hpm.weak ?_ hrel
    intro U Δ hΔ m1 hm1 hlen1
    obtain ⟨⟨u, hTH⟩, hRH, hRS⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
    refine ⟨⟨_, by rw [hrhs]; exact hRH, by rw [hrhs]; exact hRS⟩, fun o ho => ?_⟩
    obtain ⟨mds, emds, lmds⟩ := motive_binderTy g index m1
    have hcl : ((g.equation index).type.instL m1).ClosedN :=
      ((hdfWF.2.closedN' hRs.ordered.closed (Γ := []) ⟨⟩).2.2).instL
    have hlk := lookup_binderTy (Γ := []) (ls := m1) (doms := g.eqDoms index)
      (x := s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val))
      (by rw [g.eqDoms_length]; have := s.constructors[index].owner.isLt; omega)
    rw [List.append_nil, emds] at hlk
    rw [hrhs] at ho
    refine rhs_empty_motive henvF hΔ (doms := (g.eqDoms index).map (·.instL m1))
      (by show (VExpr.wrapForalls (g.eqDoms index) _).instL m1 = _
          rw [VExpr.instL_wrapForalls]) (by rw [g.equation_rhs_eq, VExpr.instL_wrapLams])
      hcl hTH (by simp only [VExpr.instL_mkApps, VExpr.instL]; rfl) hlk ?_
      (funext fun v => by
        rw [VLevel.eval_inst]; exact (VLevel.equiv_def.1 hsmall _).trans rfl)
      hRS Ctx.SubstEq.nil TV.empty o ho
    rw [lmds]
    simp only [List.length_append, List.length_map, List.length_singleton]
    omega
  · -- singleton elimination: the fields not bound by the lead are proofs
    have hall : ∀ ru2 ∈ rec.rules, ru2 = ru := by
      intro ru2 hru2
      obtain ⟨df2, hdf2, H2⟩ := hrecsOf.rules rec hrec ru2 hru2
      obtain ⟨index2, rfl, -, hctor2, -⟩ := ordinary_rule_data hdecl hrecsOf C hrec hru2 hdf2 H2
      have : index2 = index := Fin.ext (by
        have := index2.isLt; have := index.isLt; have := hsing.2.1; omega)
      subst this
      exact VEnv.inj_on_of_nodup_map (hdecl.rules_nodup rec hrec) hru2 hru (hctor2.trans hctorN.symm)
    have hEE : envE ≤ envR := by
      rw [ordinary_expanded_types C] at hE
      rw [VInductDecl.addTypes_eq_addConstVals] at sT
      exact (addConstVals_mono hbase hE sT).trans
        ((addCtors_le sC).trans (addProjs_le.trans (addRecs_le sR)))
    have hdoms : OnCtx (g.eqDoms index).reverse (envR.IsType g.uvars) := by
      have hty := hdfWF.2.isType hRs.ordered (show OnCtx [] (envR.IsType g.uvars) from trivial)
      simpa using onCtx_wrapForalls hRs.ordered
        (show OnCtx [] (envR.IsType g.uvars) from trivial) (ds := g.eqDoms index) hty
    have hpf : ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (envF.IsType U) → ∀ m1 : List VLevel,
        (∀ l ∈ m1, l.WF U) → ∀ x < (g.eqDoms index).length,
        (∀ i : Nat, (g.eqLead index)[i]? ≠ some (VExpr.bvar x)) →
        ProofBinder envF U Δ (g.eqDoms index) m1 x [] := by
      intro U Δ hΔ m1 hm1 x hx hnl
      have notLead : VExpr.bvar x ∉ g.eqLead index := fun hy => by
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem hy
        exact hnl i (List.getElem?_eq_some_iff.2 ⟨hi, e⟩)
      have hdl := g.eqDoms_length index
      have hxf : x < s.constructors[index].fields.length := by
        refine Nat.lt_of_not_le fun h => notLead
          (List.mem_append_left _ (InductiveSignature.mem_vars h ?_))
        omega
      have hidx : VExpr.bvar (s.constructors[index].fields.length - 1 -
          (s.constructors[index].fields.length - 1 - x)) ∉ s.constructors[index].indices := by
        rw [show s.constructors[index].fields.length - 1 -
          (s.constructors[index].fields.length - 1 - x) = x by omega]
        intro hm
        apply notLead
        refine List.mem_append_right _ (List.mem_map.2 ⟨_, hm, ?_⟩)
        have hxf' := hxf
        simp only [Fin.getElem_fin] at hxf'
        simp [VExpr.instL, VExpr.liftN, liftVar, hxf']
      have := proofBinder_of henvF hRs hRF VR hdoms
        (singleton_field_typing hRs.ordered hEE hsing index
          (i := s.constructors[index].fields.length - 1 - x) (by omega) hidx) (Γ := []) hΔ hm1
      rwa [show s.constructors[index].fields.length - 1 -
        (s.constructors[index].fields.length - 1 - x) = x by omega] at this
    refine PatValid.of_rule henvF hp' hr hci hstat hu (g.equation_cov index) hIrig hcf hcis
      (hctor _ hcis) hctor hpctor hnodf (ms := eqMs index) (Instance.eqMs_length index) ?_ hrel
    intro U Δ hΔ m1 hm1 hlen1
    obtain ⟨-, hRH, hRS⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
    refine ⟨hpm'.majorFam (.inr (hpf U Δ hΔ m1 hm1)), fun keys hkl hobs =>
      ⟨hheadU hall, hpf U Δ hΔ m1 hm1⟩,
      (g.equation index).type.instL m1, by rw [hrhs]; exact hRH, by rw [hrhs]; exact hRS⟩

end Model
end VEnv
end Lean4Lean
