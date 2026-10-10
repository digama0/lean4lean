import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjDF
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjValid
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CommonParams
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleWind

/-! # Field observations of constructor spines, and inversions

* `Model.ctor_field_obs`: a semantically typed constructor spine `mk ps fs` of a projection
  entry that is never zero at the constructor's levels has, for every observation `k` of the field
  `fs[j]`, a field observation `fieldOb S j L k`. The observation is built in the constructor's
  telescope (`spine_tele`, `tele_compact`, `tele_wind`); the field-domain and field-type
  observations of the codomain `S ls (params, idx)` are built in the family header's telescope,
  whose observations cover those of the family's declared type by the soundness of the recorded
  header conversion (`ProjValid`).
* Inversions: the observations of a projection-registered family spine end in `rigid`,
  `rigidArg`, `fieldTy` or `fieldDom` (`Obs.famSpine_inv`); the typed observations of a value of
  such a family are field observations (`typed_fam_fieldOb`); the field observations of a
  constructor spine come from its keys (`Obs.ctorSpine_fieldOb_inv`); `HTS.proj_inv`.
* Constructor spines typed at a family application have the constructor's arity, and the
  entry is never zero at the constructor's levels (`ctor_spine_fam`), through the codomain
  lemma `HTS.spineCod`. -/

/-! # Constructing field observations of constructor spines

`ctor_field_obs`: a constructor spine `mk ps fs` of a never-zero projection-registered family
has, for each observation `k` of the field `fs[j]` and finite demands on the earlier fields, a
field observation `fieldOb S j L k` whose context `L` contains the demands. The observation is
built in the constructor's telescope: typed finite keys at the anchors `args.subst σ`
(`tele_compact` over the valuation of `spine_tele`), field-type and field-domain observations
of the codomain from the spine lemma on the codomain (whose key classes are identified with the
constructor's parameter domains through the family's telescope), and `tele_wind`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem extS_apply : ∀ (K : List Key) (S : ObSets) (m : Nat),
    extS S K m = if h : m < K.length then listSet (K[K.length - 1 - m]).2.2 else S (m - K.length)
  | [], S, m => by simp [extS]
  | k :: K, S, m => by
    simp only [extS, List.foldl_cons] at *
    rw [show K.foldl (fun S k => S.cons (listSet k.2.2)) (S.cons (listSet k.2.2)) m =
      extS (S.cons (listSet k.2.2)) K m from rfl, extS_apply K]
    simp only [List.length_cons]
    by_cases hm : m < K.length
    · rw [dif_pos hm, dif_pos (by omega)]
      have e : K.length + 1 - 1 - m = (K.length - 1 - m) + 1 := by omega
      simp only [e, List.getElem_cons_succ]
    · rw [dif_neg hm]
      by_cases hm' : m = K.length
      · subst hm'; rw [dif_pos (by omega)]; simp [ObSets.cons]
      · rw [dif_neg (by omega)]
        obtain ⟨d, hd⟩ : ∃ d, m - K.length = d + 1 := ⟨m - K.length - 1, by omega⟩
        rw [hd, show m - (K.length + 1) = d by omega]; rfl

theorem keySets_eq_extS (K : List Key) : keySets K = extS .empty K := by
  funext m; rw [extS_apply]; simp only [keySets]; split <;> rfl

theorem keySets_congr {K K' : List Key}
    (H : List.Forall₂ (fun (k k' : Key) => ∀ y, y ∈ k.2.2 ↔ y ∈ k'.2.2) K K') :
    keySets K = keySets K' := by
  have hl := List.Forall₂.length_eq H
  funext m o
  simp only [keySets, hl]
  split
  · rename_i hm
    obtain ⟨_, h⟩ := List.forall₂_getElem_exists H (K'.length - 1 - m) (by omega)
    exact propext (h o)
  · rfl

/-- The data of a chain of typed keys from the identity: the anchors, the observation sets, and
for each key its domain class, its typed class containing the anchor, and its typed list. -/
theorem TeleKeys.data (h : TeleKeys env U Δ σ S ds keys σ' S') :
    ∃ ys : List VExpr, σ' = ys.foldl VExpr.Subst.cons σ ∧ S' = extS S keys ∧
      ys.length = ds.length ∧ keys.length = ds.length ∧
      ∀ i k y A, keys[i]? = some k → ys[i]? = some y → ds[i]? = some A →
        k.1 = TyCls env U Δ (A.subst ((ys.take i).foldl VExpr.Subst.cons σ)) ∧
        TypedElCls env U Δ (TyCls env U Δ (A.subst ((ys.take i).foldl VExpr.Subst.cons σ))) k.2.1 ∧
        k.2.1 y ∧
        (∀ x ∈ k.2.2, TypedAt env U Δ k.2.1 ((ys.take i).foldl VExpr.Subst.cons σ)
          (extS S (keys.take i)) A x) ∧
        Backed (listSet k.2.2) := by
  induction h with
  | nil => exact ⟨[], rfl, by simp [extS], rfl, rfl, fun i k y A h => by simp at h⟩
  | @cons c y K σ S A ds keys σ' S' hc hy hK hb _ ih =>
    obtain ⟨ys, e1, e2, hl1, hl2, hd⟩ := ih
    refine ⟨y :: ys, e1, by rw [e2]; rfl, by simp [hl1], by simp [hl2], fun i k y' A' hk hy' hA => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hy' hA
      subst hk hy' hA
      exact ⟨rfl, hc, hy, fun x hx => by simpa [extS] using hK x hx, hb⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hk hy' hA
      have := hd i k y' A' hk hy' hA
      simpa [List.take_succ_cons, List.foldl_cons, extS] using this

theorem forall₂_take {R : α → β → Prop} : ∀ (i : Nat) {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → List.Forall₂ R (l₁.take i) (l₂.take i)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, .nil => by simp
  | i + 1, _, _, .cons h H => by simpa using List.Forall₂.cons h (forall₂_take i H)

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

end

end Model
end VEnv
end Lean4Lean


namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-! ## Generic lemmas -/

/-- Winding up typed keys with a class-free innermost observation. -/
theorem tele_wind0 (h : TeleKeys env U Δ σ S ds keys σ' S') {R : VExpr} :
    ∀ {o : Ob} {τc : List Ob}, (∀ τ ∈ τc, Obs' σ' S' R τ) → (∀ cv, TypedOb env U Δ cv o τc) →
    ∃ τ₀, (∀ τ ∈ τ₀, Obs' σ S (.wrapForalls ds R) τ) ∧
      ∀ cv, TypedOb env U Δ cv (wrap keys o) τ₀ := by
  induction h with
  | nil => intro o τc hτc ho; exact ⟨τc, hτc, ho⟩
  | cons hc hy hK hb _ ih =>
    intro o τc hτc ho
    obtain ⟨τ₀, h1, h2⟩ := ih hτc ho
    obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK
    obtain ⟨τs, h3, h4⟩ := pi_list hc hy hτk hkk hb h1
    exact ⟨τs, h3, fun cv => h4 cv _ (h2 _)⟩

/-- A spine of keys around a non-`app` endpoint, split at a prefix of its keys. -/
theorem wrap_eq_wrap_notApp : ∀ {ks₀ ks : List Key} {o r : Ob}, r.NotApp →
    wrap ks₀ o = wrap ks r → ∃ ks', ks = ks₀ ++ ks' ∧ o = wrap ks' r
  | [], ks, o, r, _, h => ⟨ks, rfl, h⟩
  | k :: ks₀, [], o, r, hr, h => by simp only [wrap_cons, wrap_nil] at h; subst h; cases hr
  | k :: ks₀, k' :: ks, o, r, hr, h => by
    simp only [wrap_cons, Ob.app.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨ks', rfl, rfl⟩ := wrap_eq_wrap_notApp hr h4
    refine ⟨ks', ?_, rfl⟩
    obtain ⟨_, _, _⟩ := k; obtain ⟨_, _, _⟩ := k'; simp_all

/-- The end observations of a rigid family constant that is not a projection constructor. -/
def FamEnd (S : Name) (ls : List VLevel) (keys : List Key) (r : Ob) : Prop :=
  (∃ s, r = .rigid S (ls.map (·.eval)) keys.length s) ∨ (∃ i c, r = .rigidArg i c) ∨
  (∃ j FL x, r = .fieldTy S j FL x) ∨ (∃ j FL D, r = .fieldDom S j FL D) ∨
  CtorEnd S (ls.map (·.eval)) keys r

theorem FamEnd.notApp (h : FamEnd S ls keys r) : r.NotApp := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
    (rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> trivial

/-- Inversion of the observations of a rigid constant that is not a projection constructor. -/
theorem Obs.famConst_inv {S : Name} (hrig : env.Rigid S)
    (hnpc : ¬ IsProjCtor env S) (h : Obs' σ S0 (.const S ls) o) :
    ∃ keys r, o = wrap keys r ∧ FamEnd S ls keys r := by
  cases h with
  | const _ _ _ _ hr =>
    rcases hr with ⟨s, rfl⟩ | ⟨i, _, rfl⟩
    · exact ⟨_, _, rfl, .inl ⟨s, rfl⟩⟩
    · exact ⟨_, _, rfl, .inr (.inl ⟨i, _, rfl⟩)⟩
  | delta hdf hlhs => exact absurd (by rw [hlhs]; rfl) (hrig.defeqs _ hdf (VLevel.params _))
  | ctor _ _ _ _ _ hr => exact ⟨_, _, rfl, .inr (.inr (.inr (.inr hr)))⟩
  | projCtor hp hn => exact absurd ⟨_, _, hp, hn⟩ hnpc
  | rule hdf hlhs =>
    exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs _ hdf _)
  | pat hp => exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  | famTy => exact ⟨_, _, rfl, .inr (.inr (.inl ⟨_, _, _, rfl⟩))⟩
  | famDom => exact ⟨_, _, rfl, .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩

/-- Inversion of the observations of a spine of a rigid constant that is not a constructor:
they are end observations wrapped in keys. -/
theorem Obs.famSpine_inv {S : Name} (hrig : env.Rigid S)
    (hnpc : ¬ IsProjCtor env S) (h : Obs' σ S0 (.mkApps (.const S ls) args) o) :
    ∃ keys ks r, o = wrap ks r ∧ FamEnd S ls (keys ++ ks) r := by
  obtain ⟨keys, -, h'⟩ := wrap_of_obs_mkApps h
  obtain ⟨keys', r, e, hr⟩ := Obs.famConst_inv hrig hnpc h'
  obtain ⟨ks, rfl, rfl⟩ := wrap_eq_wrap_notApp hr.notApp e
  exact ⟨keys, ks, r, rfl, hr⟩

/-- A family spine has no observation of a non-`app` shape other than its end observations. -/
theorem Obs.famSpine_notApp {S : Name} (hrig : env.Rigid S)
    (hnpc : ¬ IsProjCtor env S) (h : Obs' σ S0 (.mkApps (.const S ls) args) o)
    (ho : o.NotApp) : ∃ keys, FamEnd S ls keys o := by
  obtain ⟨keys, ks, r, rfl, hr⟩ := Obs.famSpine_inv hrig hnpc h
  cases ks with
  | nil => exact ⟨_, hr⟩
  | cons => cases ho

theorem argSubst_inj : ∀ {as bs : List VExpr}, as.length = bs.length →
    VExpr.argSubst as = VExpr.argSubst bs → as = bs := by
  intro as bs hl h
  apply List.ext_getElem hl
  intro i h1 h2
  have e := congrFun h (as.length - 1 - i)
  rw [VExpr.argSubst_lt _ (by omega), VExpr.argSubst_lt _ (by omega)] at e
  simp only [show as.length - 1 - (as.length - 1 - i) = i by omega,
    show bs.length - 1 - (as.length - 1 - i) = i by omega] at e
  exact e

/-- A Pi telescope in a semantically typed derivation has a semantically typed body. -/
theorem HTS.wrapForalls_body : ∀ {ds : List VExpr} {Γ : List VExpr} {R : VExpr} {w : VLevel},
    HTS env U Δ Γ (.wrapForalls ds R) (.sort w) →
    ∃ v, HTS env U Δ (ds.reverse ++ Γ) R (.sort v)
  | [], _, _, w, H => ⟨w, H⟩
  | _ :: _, _, _, _, H => by
    obtain ⟨_, v, _, _, h3, _⟩ := H.forallE_inv rfl
    obtain ⟨v', h⟩ := HTS.wrapForalls_body h3
    exact ⟨v', by simpa [List.reverse_cons, List.append_assoc] using h⟩

/-- A substitution related along a prefix context is related along every shorter prefix. -/
theorem substEq_take {Ds : List VExpr} :
    ∀ (as bs : List VExpr), as.length = bs.length → as.length ≤ Ds.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst bs) (Ds.take as.length).reverse →
      ∀ m, m ≤ as.length →
        Ctx.SubstEq env U Δ (VExpr.argSubst (as.take m)) (VExpr.argSubst (bs.take m))
          (Ds.take m).reverse := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro bs hl _ W m hm
    cases bs with
    | nil => simp at hm; subst hm; simpa using W
    | cons => simp at hl
  | snoc as a ih =>
    intro bs hl hD W m hm
    obtain ⟨bs', b, rfl, hb⟩ : ∃ bs' b, bs = bs' ++ [b] ∧ bs'.length = as.length := by
      obtain ⟨bs', b, e, h⟩ := List.exists_snoc_of_length_succ (l := bs) (n := as.length) (by simp at hl; omega)
      exact ⟨bs', b, e, h⟩
    simp only [List.length_append, List.length_singleton] at hD hm W
    by_cases hm' : m = as.length + 1
    · subst hm'
      have e1 : (as ++ [a]).take (as.length + 1) = as ++ [a] := List.take_of_length_le (by simp)
      have e2 : (bs' ++ [b]).take (as.length + 1) = bs' ++ [b] :=
        List.take_of_length_le (by simp; omega)
      rw [e1, e2]; exact W
    · have W' : Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst bs')
          (Ds.take as.length).reverse := by
        rw [List.take_succ_eq_append_getElem (by omega), List.reverse_append,
          VExpr.argSubst_append_one, VExpr.argSubst_append_one] at W
        cases W with
        | cons W _ _ => simpa using W
      have := ih bs' hb.symm (by omega) W' m (by omega)
      rwa [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]

/-- Arguments related along a closed telescope are typed along it. -/
theorem ArgsTyped.of_substEq {D : List VExpr} {R0 : VExpr} :
    ∀ (as pre : List VExpr), pre.length + as.length ≤ D.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst (pre ++ as)) (VExpr.argSubst (pre ++ as))
        (D.take (pre ++ as).length).reverse →
      ArgsTyped env U Δ ((VExpr.wrapForalls (D.drop pre.length) R0).subst (VExpr.argSubst pre))
        as ((VExpr.wrapForalls (D.drop (pre ++ as).length) R0).subst
          (VExpr.argSubst (pre ++ as)))
  | [], pre, _, _ => by simpa using ArgsTyped.nil
  | a :: as, pre, hl, W => by
    simp only [List.length_cons] at hl
    have hk : pre.length < D.length := by omega
    rw [List.drop_eq_getElem_cons hk, VExpr.subst_wrapForalls_cons]
    have W1 := substEq_take (Ds := D) (pre ++ a :: as) (pre ++ a :: as) rfl (by simp; omega) W
      (pre.length + 1) (by simp)
    rw [show (pre ++ a :: as).take (pre.length + 1) = pre ++ [a] by
        rw [List.take_append]; simp [List.take_of_length_le],
      List.take_succ_eq_append_getElem hk, List.reverse_append, VExpr.argSubst_append_one] at W1
    cases W1 with
    | cons _ _ ha =>
    have ha' : env.IsDefEq U Δ a a (D[pre.length].subst (VExpr.argSubst pre)) := by
      simpa using ha
    refine .cons ha' ?_
    rw [VExpr.inst_lift_cons, ← VExpr.argSubst_append_one]
    have := ArgsTyped.of_substEq (D := D) (R0 := R0) as (pre ++ [a]) (by simp; omega)
      (by simpa using W)
    simpa using this

/-! ## The family header at a given declaration -/

/-- The family header data of a projection entry, at the header environment `envTypes` of its
declaration (`VEnv.ProjDeclAt`). -/
theorem _root_.Lean4Lean.VEnv.ProjDeclAt.familyTele_data {envTypes : VEnv} {S : Name}
    {info : VProjectionInfo} (h : env.ProjDeclAt envTypes S info) :
    ∃ (famType : VExpr) (params ownParams pdoms fdoms idoms idx : List VExpr)
      (result exprType : VExpr),
      envTypes.WF ∧ envTypes ≤ env ∧
      envTypes.constants S = some ⟨info.uvars, famType⟩ ∧
      info.ctorType = VExpr.wrapForalls (pdoms ++ fdoms)
        (VExpr.mkApps (.const S (VLevel.params info.uvars))
          ((List.range info.nparams).reverse.map
              (fun i => .bvar ((pdoms ++ fdoms).length - info.nparams + i)) ++ idx)) ∧
      pdoms.length = info.nparams ∧ ownParams.length = info.nparams ∧
      idoms.length = info.nindices ∧ idx.length = info.nindices ∧
      envTypes.IsDefEq info.uvars [] famType (VExpr.wrapForalls (ownParams ++ idoms) result)
        exprType ∧
      (∃ w, envTypes.IsDefEq info.uvars [] (VExpr.wrapForalls (ownParams ++ idoms) result)
        (VExpr.wrapForalls (ownParams ++ idoms) (.sort info.resultLevel)) (.sort w)) ∧
      envTypes.IsDefEqCtx info.uvars [] params.reverse ownParams.reverse ∧
      envTypes.IsDefEqCtx info.uvars [] params.reverse pdoms.reverse ∧
      envTypes.IsType info.uvars [] info.ctorType := by
  obtain ⟨doms, idx, hshape, hdl, hidx⟩ := h.origin.ctorType_shape
  obtain ⟨base, dsb, decl, type, ctor, hbase, htypes, hle, hord, htype, hctors, rfl,
    hu, hnp, hni, hrl, -, hct, -, hwf, -, -, hspw⟩ := h
  obtain ⟨params, envTypes0, htypes0, HT, HC, -⟩ := hspw
  cases htypes0.symm.trans htypes
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType, hT, hP, hI, hPD,
    hres⟩ := HT type htype
  obtain ⟨hn1, hn2⟩ := VExpr.takeForalls_eq_wrapForalls hP
  obtain ⟨ha1, ha2⟩ := VExpr.takeForalls_eq_wrapForalls hI
  obtain ⟨ctorParams, tail, htake, hCPD⟩ := HC type htype ctor (by rw [hctors]; simp)
  have hsplit : doms = doms.take info.nparams ++ doms.drop info.nparams :=
    (List.take_append_drop _ _).symm
  have hcp : ctorParams = doms.take info.nparams := by
    have hs := hshape
    generalize VExpr.mkApps _ _ = R at hs
    have h2 := VExpr.takeForalls_wrapForalls_append (doms.take info.nparams)
      (doms.drop info.nparams) R
    rw [List.take_append_drop, ← hs, hct, List.length_take, Nat.min_eq_left hdl, hnp,
      htake] at h2
    rw [hnp]; exact (Prod.mk.inj (Option.some.inj h2)).1
  have hconst : envTypes.constants type.name = some type.toVConstVal.toVConstant :=
    VEnv.addConstVals_get htypes (List.mem_map.mpr ⟨type, htype, rfl⟩)
  have huv : type.uvars = decl.uvars := by
    rw [← hct, hshape] at hwf
    have hctx := IsType.wrapForalls_ctx hord (Γ := []) trivial hwf doms.length (Nat.le_refl _)
    obtain ⟨_, hR⟩ := IsType.wrapForalls_body hord hwf
    simp only [List.append_nil, List.take_length] at hR hctx
    obtain ⟨_, hc⟩ := HasType.mkApps_fn hord hctx hR
    obtain ⟨ci, hci, -, hlen⟩ := HasType.const_inv hord hctx hc
    rw [hconst] at hci
    cases hci
    simpa [hu] using hlen.symm
  have hbt : base ≤ envTypes := VEnv.addConstVals_le htypes
  have hnorm : normalized = VExpr.wrapForalls (ownParams ++ indices) result := by
    rw [hn1, ha1]; simp [VExpr.wrapForalls]
  refine ⟨type.type, params, ownParams, doms.take info.nparams,
    doms.drop info.nparams, indices, idx, result, exprType, hord, hle, ?_, ?_, by simp; omega,
    by rw [hn2, hnp], by rw [ha2, hni], hidx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hconst, hu, ← huv]
  · rw [← hsplit]; exact hshape
  · rw [hu, ← hnorm]; exact hT.mono hbt
  · rw [hu, hrl]
    have hN := (hT.mono hbt).hasType.2
    rw [hnorm] at hN
    exact HasType.wrapForalls_congr_body hord hN
      (by simpa [List.reverse_append] using hres.mono hbt)
  · rw [hu]; exact hPD.mono hbt
  · rw [hu, ← hcp]; exact hCPD
  · rw [hu, hct]; exact hwf

/-! ## The data of a valid projection entry at universe levels -/

/-- The result type of a projection-registered constructor: the family at its universe
parameters applied to the parameter variables and the indices. -/
def ctorRes (S : Name) (info : VProjectionInfo) (n : Nat) (idx : List VExpr) : VExpr :=
  .mkApps (.const S (VLevel.params info.uvars))
    ((List.range info.nparams).reverse.map (fun i => .bvar (n - info.nparams + i)) ++ idx)

/-- The arguments of the constructor's result type at universe levels `ls`. -/
def famArgs (info : VProjectionInfo) (n : Nat) (idx : List VExpr) (ls : List VLevel) :
    List VExpr :=
  ((List.range info.nparams).reverse.map (fun i => VExpr.bvar (n - info.nparams + i)) ++ idx).map
    (·.instL ls)

theorem ctorRes_instL {ls : List VLevel} (hlen : ls.length = info.uvars) :
    (ctorRes S info n idx).instL ls = .mkApps (.const S ls) (famArgs info n idx ls) := by
  simp only [ctorRes, famArgs, VExpr.instL_mkApps, VExpr.instL, VLevel.inst_map_id hlen]

theorem famArgs_length : (famArgs info n idx ls).length = info.nparams + idx.length := by
  simp [famArgs]

theorem famArgs_param {i : Nat} (hi : i < info.nparams) (hn : info.nparams ≤ n) :
    (famArgs info n idx ls)[i]? = some (.bvar (n - 1 - i)) := by
  have hl : i < (famArgs info n idx ls).length := by rw [famArgs_length]; omega
  rw [List.getElem?_eq_getElem hl]
  congr 1
  have h1 : i < ((List.range info.nparams).reverse.map
      (fun i => VExpr.bvar (n - info.nparams + i))).length := by simpa using hi
  simp only [famArgs, List.getElem_map, List.getElem_append_left h1, List.getElem_reverse,
    List.getElem_range, List.length_range, VExpr.instL]
  congr 1; omega


theorem famArgs_subst_param {ys : List VExpr} (hyl : ys.length = n) (hn : info.nparams ≤ n)
    {i : Nat} (hi : i < info.nparams) :
    ((famArgs info n idx ls).map (·.subst (VExpr.argSubst ys)))[i]? = ys[i]? := by
  rw [List.getElem?_map, famArgs_param hi hn, Option.map_some,
    List.getElem?_eq_getElem (show i < ys.length by omega)]
  simp only [VExpr.subst]
  rw [VExpr.argSubst_lt _ (by omega)]
  congr 2; omega

theorem famArgs_subst_take {ys : List VExpr} (hyl : ys.length = n) (hn : info.nparams ≤ n)
    {m : Nat} (hm : m ≤ info.nparams) :
    ((famArgs info n idx ls).map (·.subst (VExpr.argSubst ys))).take m = ys.take m := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split
  · exact famArgs_subst_param hyl hn (by omega)
  · rfl

theorem argSets_get {σ : VExpr.Subst} {S : ObSets} {args : List VExpr} {i : Nat} {a : VExpr}
    (h : args[i]? = some a) {y : Ob} :
    argSets env U Δ σ S args (args.length - 1 - i) y ↔ Obs' σ S a y := by
  have hi : i < args.length := (List.getElem?_eq_some_iff.1 h).1
  have ea : args[i] = a := (List.getElem?_eq_some_iff.1 h).2
  simp only [argSets, show args.length - 1 - i < args.length by omega, dite_true,
    show args.length - 1 - (args.length - 1 - i) = i by omega, ea]

/-- The syntactic and semantic data of a valid projection entry at the universe levels `ls`:
the constructor telescope `doms` with indices `idx`, the family's declared type `famType`, and
the family header's domains `hdoms` (parameters, then indices), whose telescope ending in the
result sort has, soundly, the observations of the declared type. -/
structure ProjCtx (env : VEnv) (U : Nat) (Δ : List VExpr) (S : Name) (info : VProjectionInfo)
    (ls : List VLevel) (doms idx : List VExpr) (famType : VExpr) (hdoms : List VExpr) : Prop where
  shape : info.ctorType = .wrapForalls doms (ctorRes S info doms.length idx)
  np_le : info.nparams ≤ doms.length
  idx_len : idx.length = info.nindices
  wf : env.IsType info.uvars [] info.ctorType
  ctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩
  tele : ProjTele env U S info ls (doms.map (fun d : VExpr => d.instL ls))
    ((ctorRes S info doms.length idx).instL ls)
  piSD : PiSD env U Δ [] (doms.map (fun d : VExpr => d.instL ls)) ((ctorRes S info doms.length idx).instL ls)
  hts : ∃ v, HTS env U Δ (doms.map (fun d : VExpr => d.instL ls)).reverse
    ((ctorRes S info doms.length idx).instL ls) (.sort v)
  famConst : env.constants S = some ⟨info.uvars, famType⟩
  hdoms_len : hdoms.length = info.nparams + info.nindices
  famSub : Ob.Sub (Obs env U Δ .id .empty (famType.instL ls))
    (Obs env U Δ .id .empty
      (.wrapForalls (hdoms.map (fun d : VExpr => d.instL ls)) (.sort (info.resultLevel.inst ls))))
  famSub_symm : Ob.Sub (Obs env U Δ .id .empty
      (.wrapForalls (hdoms.map (fun d : VExpr => d.instL ls)) (.sort (info.resultLevel.inst ls))))
    (Obs env U Δ .id .empty (famType.instL ls))
  famPi : PiSD env U Δ [] (hdoms.map (fun d : VExpr => d.instL ls)) (.sort (info.resultLevel.inst ls))
  famClosed : ∀ i (hi : i < hdoms.length),
    ((hdoms.map (fun d : VExpr => d.instL ls))[i]'(by simpa using hi)).ClosedN i
  ctorClosed : ∀ i (hi : i < doms.length),
    ((doms.map (fun d : VExpr => d.instL ls))[i]'(by simpa using hi)).ClosedN i
  bridge : ∀ {as : List VExpr}, as.length ≤ info.nparams →
    Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst as)
      ((hdoms.map (fun d : VExpr => d.instL ls)).take as.length).reverse →
    Ctx.SubstEq env U Δ (VExpr.argSubst as) (VExpr.argSubst as)
      ((doms.map (fun d : VExpr => d.instL ls)).take as.length).reverse ∧
    ∀ i, i < as.length →
      TyCls env U Δ (((hdoms.map (fun d : VExpr => d.instL ls)).getD i (VExpr.sort .zero)).subst
        (VExpr.argSubst (as.take i))) =
      TyCls env U Δ (((doms.map (fun d : VExpr => d.instL ls)).getD i (VExpr.sort .zero)).subst
        (VExpr.argSubst (as.take i)))

theorem closed_doms_of_isType (henv : env.OrderedStrong) {D : List VExpr} {R : VExpr}
    (h : env.IsType U [] (.wrapForalls D R)) :
    ∀ i (hi : i < D.length), (D[i]).ClosedN i := by
  intro i hi
  obtain ⟨u, hu⟩ := IsType.wrapForalls_doms henv h i hi
  have hctx := IsType.wrapForalls_ctx henv (Γ := []) trivial h i (by omega)
  have := hu.closedN henv (CtxWF.closed henv hctx)
  simpa [Nat.min_eq_left (Nat.le_of_lt hi)] using this

theorem ProjValid.ctx (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U)) {S : Name}
    {info : VProjectionInfo} (hp : env.projections S info) (hPV : ProjValid env S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    ∃ doms idx famType hdoms, ProjCtx env U Δ S info ls doms idx famType hdoms := by
  obtain ⟨-, envTypes, ho, hsnd⟩ := hPV
  obtain ⟨famType, params, own, pdoms, fdoms, idoms, idx, result, exprType, hord, hle, hfc,
    hshape, hpl, hol, hil, hidx, hT, ⟨w, hconv⟩, hctx1, hctx2, hwfT⟩ := ho.familyTele_data
  have hsE : SoundTypedIn env envTypes U Δ := fun h => hsnd U Δ hΔ h
  have hsE' : SoundIn env envTypes U Δ := fun h => hsE.soundIn h
  have hwf : env.IsType info.uvars [] info.ctorType := hwfT.mono hle
  have hshape' : info.ctorType = .wrapForalls (pdoms ++ fdoms)
      (ctorRes S info (pdoms ++ fdoms).length idx) := hshape
  -- the constructor type at `ls`
  obtain ⟨wc, hct⟩ := IsType.instL hls hwfT
  simp only [List.map_nil] at hct
  have hctS := hsE (IsDefEq.strong hord (show OnCtx [] (envTypes.IsType U) from trivial) hct)
  rw [hshape', VExpr.instL_wrapForalls] at hct hctS
  -- the family header at `ls`
  have hsortL : ∀ l : VLevel, (VExpr.sort l).instL ls = .sort (l.inst ls) := fun _ => rfl
  have hT' := hT.instL hls
  have hconv' := hconv.instL hls
  simp only [List.map_nil, VExpr.instL_wrapForalls, List.map_append, hsortL] at hT' hconv'
  have sT := (hsE (IsDefEq.strong hord (show OnCtx [] (envTypes.IsType U) from trivial)
    hT')).1 .id .id .empty .nil TV.empty TV.empty
  have sC := (hsE (IsDefEq.strong hord (show OnCtx [] (envTypes.IsType U) from trivial)
    hconv')).1 .id .id .empty .nil TV.empty TV.empty
  have hfamTy : envTypes.HasType U [] (.wrapForalls ((own ++ idoms).map (·.instL ls))
      (.sort (info.resultLevel.inst ls))) (.sort (w.inst ls)) := by
    simpa only [List.map_append] using hconv'.hasType.2
  have hfamTy' : env.IsType U [] (.wrapForalls ((own ++ idoms).map (·.instL ls))
      (.sort (info.resultLevel.inst ls))) := ⟨_, hfamTy.mono hle⟩
  have T := ProjTele.of (S := S) henv hshape hwf hls
  refine ⟨pdoms ++ fdoms, idx, famType, own ++ idoms,
    { shape := hshape'
      np_le := by simp [hpl]
      idx_len := hidx
      wf := hwf
      ctor := henv.ordered.projectionConstructor hp
      tele := T
      piSD := piSD_of hord.orderedStrong hle hsE' trivial hct
      hts := ?_
      famConst := hle.constants hfc
      hdoms_len := by simp [hol, hil]
      famSub := ?_
      famSub_symm := ?_
      famPi := piSD_of hord.orderedStrong hle hsE' trivial hfamTy
      famClosed := fun i hi => closed_doms_of_isType henv hfamTy' i (by simpa using hi)
      ctorClosed := fun i hi => closed_doms_of_isType henv
        (by rw [← VExpr.instL_wrapForalls, ← hshape']; exact IsType.instL hls hwf) i
          (by simpa using hi)
      bridge := ?_ }⟩
  · obtain ⟨v, h⟩ := HTS.wrapForalls_body hctS.2.1
    exact ⟨v, by simpa using h⟩
  · simpa only [List.map_append] using sT.1.trans sC.1
  · simpa only [List.map_append] using sC.2.1.trans sT.2.1
  · intro as has W
    have hlo : as.length ≤ own.length := by omega
    have e1 : ((own ++ idoms).map (·.instL ls)).take as.length =
        (own.map (·.instL ls)).take as.length := by
      rw [List.map_append, List.take_append_of_le_length (by simp; omega)]
    have e2 : ((pdoms ++ fdoms).map (·.instL ls)).take as.length =
        (pdoms.map (·.instL ls)).take as.length := by
      rw [List.map_append, List.take_append_of_le_length (by simp; omega)]
    rw [e1] at W
    obtain ⟨WD, hcls⟩ := paramBridge henv hle hΔ hctx1 hctx2 hls hlo W
    refine ⟨by rw [e2]; exact WD, fun i hi => ?_⟩
    have := hcls i hi
    have hio : i < own.length := by omega
    have hip : i < pdoms.length := by omega
    simp only [List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa using hio : i < (own.map (·.instL ls)).length),
      List.getElem?_append_left (by simpa using hip : i < (pdoms.map (·.instL ls)).length),
      List.getElem?_map, List.getElem?_eq_getElem hio, List.getElem?_eq_getElem hip,
      Option.map_some, Option.getD_some]
    exact this

/-! ## Inversions -/

theorem FamEnd.not_sort : ¬ FamEnd S ls keys (.sort l) := by
  rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | (h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩)) <;>
    cases h

theorem FamEnd.not_piDom : ¬ FamEnd S ls keys (.piDom D) := by
  rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | (h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩)) <;>
    cases h

theorem FamEnd.rigid_eq (h : FamEnd S ls keys (.rigid I ℓs m z)) : I = S ∧ ℓs = ls.map (·.eval) := by
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | (h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
    cases h
  exact ⟨rfl, rfl⟩

theorem FamEnd.fieldDom_eq (h : FamEnd S ls keys (.fieldDom n j FL D)) : n = S := by
  rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | (h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
    cases h
  rfl

/-- Inversion of a semantic typing derivation of a projection, through `conv` nodes. -/
theorem HTS.proj_inv (H : HTS env U Δ Γ e T) {S : Name} {j : Nat} {e₀ : VExpr}
    (he : e = .proj S j e₀) :
    ∃ (info : VProjectionInfo) (ls : List VLevel) (ps idx : List VExpr) (F : VExpr)
      (fl : VLevel) (e' : VExpr),
      env.projections S info ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = info.uvars ∧
      ps.length = info.nparams ∧ idx.length = info.nindices ∧
      info.fieldType S ls ps j e' = some F ∧ SD env U Δ Γ F F (.sort fl) ∧
      HTS env U Δ Γ e₀ (.mkApps (.const S ls) (ps ++ idx)) ∧
      SD env U Δ Γ e' e₀ (.mkApps (.const S ls) (ps ++ idx)) ∧
      ((info.resultLevel.inst ls).IsNeverZero ∨ fl ≈ .zero) ∧
      ∀ σ S0, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S0 →
        Ob.Sub (Obs' σ S0 T) (Obs' σ S0 F) := by
  induction H with
  | proj h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases he
    exact ⟨_, _, _, _, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      fun _ _ _ _ => Ob.Sub.refl⟩
  | other _ _ _ _ h => exact absurd he (h _ _ _)
  | bvar | const | app | lam | forallE => cases he
  | conv _ hAB ih =>
    obtain ⟨info, ls, ps, idx, F, fl, e', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := ih he
    exact ⟨info, ls, ps, idx, F, fl, e', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      fun σ S0 W tv => ((hAB.2 σ σ S0 W tv tv).2.1).trans (h11 σ S0 W tv)⟩

section
variable (henv : env.OrderedStrong)
include henv

/-- **Typed observations at a projection-registered family are field observations**, of a field
that exists, and only when the entry is never zero at the family's levels. -/
theorem typed_fam_fieldOb {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hrig : env.Rigid S) (hnpc : ¬ IsProjCtor env S) {cv : VExpr → Prop} {o : Ob}
    {τs : List Ob} (H : TypedOb env U Δ cv o τs) {σ : VExpr.Subst} {S0 : ObSets}
    {ls : List VLevel} {args : List VExpr}
    (hτ : ∀ τ ∈ τs, Obs' σ S0 (.mkApps (.const S ls) args) τ) :
    ∃ j L k, o = .fieldOb S j L k ∧ j < info.numFields ∧
      (info.resultLevel.inst ls).IsNeverZero := by
  have fe : ∀ τ ∈ τs, τ.NotApp → ∃ keys, FamEnd S ls keys τ := fun τ hτ' hn =>
    Obs.famSpine_notApp hrig hnpc (hτ τ hτ') hn
  cases H with
  | sort h | piDom h | piDomOb h | piCod h | piCodOb h | rigid h | rigidArg h | rigidArgOb h
  | fieldTy h | fieldDom h =>
    obtain ⟨_, h⟩ := fe _ h trivial; exact absurd h FamEnd.not_sort
  | app h => obtain ⟨_, h⟩ := fe _ h trivial; exact absurd h FamEnd.not_piDom
  | ctorHead h | ctorArg h | ctorArgOb h =>
    obtain ⟨I, ℓs, m, z, h1, -, -, h4⟩ := h
    obtain ⟨_, h⟩ := fe _ h1 trivial
    obtain ⟨rfl, -⟩ := h.rigid_eq
    exact absurd hp (h4 info)
  | fieldOb hp' hj _ hD =>
    obtain ⟨_, h⟩ := fe _ hD trivial
    cases h.fieldDom_eq
    cases henv.ordered.projections_unique hp hp'
    obtain ⟨-, -, info', -, -, -, hp'', hnz, -⟩ := famDom_inv hrig (hτ _ hD)
    cases henv.ordered.projections_unique hp hp''
    exact ⟨_, _, _, rfl, hj, hnz⟩

/-- **The field observations of a constructor spine** of a projection entry come from the
projection-constructor clause: the spine is full, and the field's observation is covered by
an observation of the argument at the field. -/
theorem Obs.ctorSpine_fieldOb_inv {S : Name} {info : VProjectionInfo}
    (hp : env.projections S info) (hrig : env.Rigid info.ctorName) {σ : VExpr.Subst}
    {S0 : ObSets} {ls : List VLevel} {args : List VExpr} {j : Nat} {L : List (List Ob)} {k : Ob}
    (h : Obs' σ S0 (.mkApps (.const info.ctorName ls) args) (.fieldOb S j L k)) :
    args.length = info.nparams + info.numFields ∧ j < info.numFields ∧
      ∃ a, args[info.nparams + j]? = some a ∧ ∃ k', Obs' σ S0 a k' ∧ k' ≼ k := by
  obtain ⟨keys0, hk0, h'⟩ := wrap_of_obs_mkApps_le h
  generalize hw : wrap keys0 (Ob.fieldOb S j L k) = w at h'
  cases h' with
  | const _ _ _ _ hr =>
    obtain ⟨-, e⟩ := wrap_inj hw trivial hr.notApp
    rcases hr with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> cases e
  | delta hdf hlhs => exact absurd (by rw [hlhs]; rfl) (hrig.defeqs _ hdf (VLevel.params _))
  | ctor _ hnp => exact absurd ⟨_, _, hp, rfl⟩ hnp
  | rule hdf hlhs =>
    exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs _ hdf _)
  | pat hp => exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  | projCtor hp' hcn _ _ _ hlen hend =>
    obtain ⟨j', L', k', rfl, hj', -, -, kj, hkj, hkk⟩ := hend
    obtain ⟨rfl, e⟩ := wrap_inj hw trivial trivial
    cases e
    cases henv.ordered.projections_unique hp hp'
    have hl := List.Forall₂.length_eq hk0
    refine ⟨by omega, hj', ?_⟩
    have hia : info.nparams + j < args.length := by
      have := (List.getElem?_eq_some_iff.1 hkj).1; omega
    obtain ⟨-, hcov⟩ := forall₂_get? hk0 hkj (List.getElem?_eq_getElem hia)
    exact ⟨_, List.getElem?_eq_getElem hia, hcov k hkk⟩
  | famTy =>
    obtain ⟨-, e⟩ := wrap_inj hw trivial trivial
    cases e
  | famDom =>
    obtain ⟨-, e⟩ := wrap_inj hw trivial trivial
    cases e

end

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Codomain observations of a constant spine**: for a semantically typed constant spine and
keys whose classes contain the arguments and whose observations are covered by the arguments'
(`ChainArgs`), every codomain observation of the constant's type at the keys is covered by an
observation of the spine's type. -/
theorem HTS.spineCod (H : HTS env U Δ Γ e T) {c ls args} (he : e = .mkApps (.const c ls) args)
    {σ S} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
      ∀ keys, ChainArgs env U Δ σ S keys args → ∀ x,
        Obs' .id .empty (ci.type.instL ls) (piCodChain keys x) → ∃ x', Obs' σ S T x' ∧ x' ≼ x := by
  induction H generalizing args with
  | bvar => exact absurd he.symm mkApps_const_ne_bvar
  | other h => exact absurd he (h _ _ _)
  | lam => exact absurd he.symm mkApps_const_ne_lam
  | forallE => exact absurd he.symm VExpr.mkApps_const_ne_forallE
  | proj => rcases mkApps_inv he with ⟨_, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  | @const _ ci' _ _ _ hci hls hlen hT hsd =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨_, _, _, he'⟩
    · cases he'
      refine ⟨ci', hci, hls, hlen, fun keys hk x hx => ?_⟩
      cases hk
      exact ⟨x, (Obs.closed_iff_id (henv.ordered.closedC hci).instL).2 hx, .refl⟩
    · cases he'
  | @app Γ' A u B v f a hA hB _ hfty _ hsa ihf _ =>
    rcases mkApps_inv he with ⟨rfl, he'⟩ | ⟨as, a', rfl, he'⟩
    · cases he'
    injection he' with hf ha; subst ha
    obtain ⟨ci, hci, hls, hlen, ih⟩ := ihf hf W tv
    refine ⟨ci, hci, hls, hlen, fun keys hk x hx => ?_⟩
    unfold ChainArgs at hk
    obtain ⟨keys', k, rfl, hk', ⟨hka, hkK⟩⟩ := List.forall₂_snoc_right hk
    rw [piCodChain_append, piCodChain_cons, piCodChain_nil] at hx
    obtain ⟨x₁, hx₁, l₁⟩ := ih keys' hk' _ hx
    obtain ⟨K₀, y, rfl, hKK₀, ly⟩ := l₁.piCodOb_inv
    obtain ⟨hc, ⟨τk, hτk, hkk⟩, z, hz, hyB⟩ := Obs.piCodOb_mem hx₁
    have hb₀ := Obs.piCodOb_backed hx₁
    have haσ : env.HasType U Δ (a.subst σ) (A.subst σ) :=
      hsa.1.defeq.hasType.1.substDF henv W.wf hΔ W
    have hA' := hA.1.defeq.hasType.1
    have W' : Ctx.SubstEq env U Δ (σ.cons z) (σ.cons (a.subst σ)) (A :: Γ') :=
      .cons W hA' (hc.defeq henv hΔ hz hka)
    have hK₀ : ∀ k' ∈ K₀, TypedAt env U Δ k.2.1 σ S A k' := fun k' hk' => ⟨τk, hτk, hkk k' hk'⟩
    obtain ⟨x₂, hx₂, l₂⟩ := (hB.2 _ _ _ W' (tv.cons_cls henv hΔ hc hz hb₀ hK₀)
      (tv.cons_cls henv hΔ hc hka hb₀ hK₀)).1 y hyB
    obtain ⟨x₃, hx₃, l₃⟩ := hx₂.mono_le (S' := S.cons (Obs' σ S a)) fun i o h => by
      cases i with
      | zero =>
        obtain ⟨k', hk', l⟩ := hKK₀ o h
        obtain ⟨y₀, hy₀, l₀⟩ := hkK k' hk'
        exact ⟨y₀, hy₀, l₀.trans l⟩
      | succ i => exact ⟨o, h, .refl⟩
    exact ⟨x₃, Obs.inst_iff.2 hx₃, l₃.trans (l₂.trans ly)⟩
  | conv _ hAB ih =>
    obtain ⟨ci, hci, hls, hlen, ih⟩ := ih he W tv
    refine ⟨ci, hci, hls, hlen, fun keys hk x hx => ?_⟩
    obtain ⟨x₁, hx₁, l₁⟩ := ih keys hk x hx
    obtain ⟨x₂, hx₂, l₂⟩ := (SD.sub hAB W tv).1 x₁ hx₁
    exact ⟨x₂, hx₂, l₂.trans l₁⟩

/-! ## Typed keys at given anchors -/

/-- Typed keys along a closed telescope `D` at the anchors `ys`, with the observation sets `S'`
of their extension. -/
structure KeysAt (env : VEnv) (U : Nat) (Δ : List VExpr) (D ys : List VExpr) (keys : List Key)
    (S' : ObSets) : Prop where
  tele : TeleKeys env U Δ .id .empty D keys (VExpr.argSubst ys) S'
  len : keys.length = D.length
  ylen : ys.length = D.length
  sets : ∀ m k, keys[D.length - 1 - m]? = some k → m < D.length → ∀ o, S' m o ↔ o ∈ k.2.2
  cls : ∀ i k, keys[i]? = some k →
    k.1 = TyCls env U Δ ((D.getD i (.sort .zero)).subst (VExpr.argSubst (ys.take i))) ∧
    k.2.1 = ElCls env U Δ k.1 (ys.getD i (.sort .zero)) ∧ TypedElCls env U Δ k.1 k.2.1
  typed : ∀ i k, keys[i]? = some k → ∀ x ∈ k.2.2,
    TypedAt env U Δ k.2.1 (VExpr.argSubst (ys.take i)) (keySets (keys.take i))
      (D.getD i (.sort .zero)) x
  backed : KeysBacked keys

theorem KeysAt.of_tele {D ys : List VExpr} {keys : List Key} {S' : ObSets}
    (h : TeleKeys env U Δ .id .empty D keys (VExpr.argSubst ys) S') (hyl : ys.length = D.length)
    (hS : ∀ m k, keys[D.length - 1 - m]? = some k → m < D.length → ∀ o, S' m o ↔ o ∈ k.2.2) :
    KeysAt env U Δ D ys keys S' := by
  obtain ⟨ys', e1, -, hl1, hl2, hd⟩ := TeleKeys.data h
  have eys : ys' = ys := (argSubst_inj (by omega) e1.symm)
  subst eys
  refine ⟨h, hl2, hyl, hS, fun i k hk => ?_, fun i k hk x hx => ?_, fun k hk => ?_⟩
  · have hi : i < keys.length := (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨e, hc, hy, -, -⟩ := hd i k (ys'[i]'(by omega)) (D[i]'(by omega)) hk
      (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
    have eD : D.getD i (.sort .zero) = D[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < D.length by omega)]
    have eY : ys'.getD i (.sort .zero) = ys'[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ys'.length by omega)]
    rw [eD, eY]
    refine ⟨e, ?_, e ▸ hc⟩
    obtain ⟨_, _, _, e'⟩ := hc.mem henv hΔ hy
    rw [e]; exact e'
  · have hi : i < keys.length := (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨-, -, -, hK, -⟩ := hd i k (ys'[i]'(by omega)) (D[i]'(by omega)) hk
      (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
    have eD : D.getD i (.sort .zero) = D[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < D.length by omega)]
    rw [eD, keySets_eq_extS]; exact hK x hx
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
    obtain ⟨-, -, -, -, hb⟩ := hd i _ (ys'[i]'(by omega)) (D[i]'(by omega))
      (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem (by omega))
    exact hb

/-- **Typed keys of a constructor spine** along the constructor telescope, at the substituted
arguments, containing given finite demands and contained in the arguments' observations. -/
theorem ctor_keys {S : Name} {info : VProjectionInfo} {ls : List VLevel}
    {doms idx hdoms : List VExpr} {famType : VExpr}
    (C : ProjCtx env U Δ S info ls doms idx famType hdoms)
    {Γ : List VExpr} {σ : VExpr.Subst} {S0 : ObSets}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S0) {args : List VExpr} {T : VExpr}
    (H : HTS env U Δ Γ (.mkApps (.const info.ctorName ls) args) T)
    (hal : args.length = doms.length) (F : List (List Ob)) (hF : F.length = doms.length)
    (hFS : ∀ (i : Nat) (Fi : List Ob), F[i]? = some Fi → ∀ y ∈ Fi,
      ∃ a, args[i]? = some a ∧ Obs' σ S0 a y) :
    ∃ (keys : List Key) (S' : ObSets),
      KeysAt env U Δ (doms.map (·.instL ls)) (args.map (·.subst σ)) keys S' ∧
      ∀ (i : Nat) (k : Key), keys[i]? = some k →
        (∀ Fi : List Ob, F[i]? = some Fi → ∀ y ∈ Fi, y ∈ k.2.2) ∧
        ∀ y ∈ k.2.2, ∃ a, args[i]? = some a ∧ Obs' σ S0 a y := by
  have hTW : Ob.Sub (Obs' .id .empty ((⟨info.uvars, info.ctorType⟩ : VConstant).type.instL ls))
      (Obs' .id .empty (.wrapForalls (doms.map (·.instL ls))
        ((ctorRes S info doms.length idx).instL ls))) := by
    rw [show (⟨info.uvars, info.ctorType⟩ : VConstant).type = info.ctorType from rfl,
      C.tele.shape]
    exact Ob.Sub.refl
  obtain ⟨W1, tv1⟩ := spine_tele henv hΔ H W tv C.ctor hTW C.piSD (by simp [hal])
  have hDl : (doms.map (·.instL ls)).length = doms.length := by simp
  rw [show args.length = (doms.map (·.instL ls)).length by simp [hal], List.take_length] at W1 tv1
  obtain ⟨keys, S', hT, hkl, hS, hk⟩ := tele_compact (D := doms.map (·.instL ls))
    (as := args.map (·.subst σ)) (fun i hi => C.ctorClosed i (by simpa using hi))
    (by simp [hal]) W1 tv1 F (by simp [hF]) (fun i Fi hFi y hy => by
      obtain ⟨a, ha, hya⟩ := hFS i Fi hFi y hy
      rw [hDl, ← hal]; exact (argSets_get ha).2 hya)
  refine ⟨keys, S', KeysAt.of_tele henv hΔ hT (by simp [hal]) hS, fun i k hki => ?_⟩
  obtain ⟨h1, h2, -⟩ := hk i k hki
  refine ⟨h1, fun y hy => ?_⟩
  have hi : i < keys.length := (List.getElem?_eq_some_iff.1 hki).1
  have ha : args[i]? = some (args[i]'(by rw [hal]; simp at hkl; omega)) :=
    List.getElem?_eq_getElem _
  have := h2 y hy
  rw [hDl, ← hal] at this
  exact ⟨_, ha, (argSets_get ha).1 this⟩

/-- **Typed keys of the family application** `S ls (params, idx)` in the constructor's codomain,
along the family header, at the extension of the constructor telescope by typed keys `keysD`:
the parameter keys have the classes and the observations of the constructor's parameter keys. -/
theorem fam_keys {S : Name} {info : VProjectionInfo} {ls : List VLevel}
    {doms idx hdoms : List VExpr} {famType : VExpr}
    (C : ProjCtx env U Δ S info ls doms idx famType hdoms) (hlen : ls.length = info.uvars)
    {ys : List VExpr} {keysD : List Key} {S' : ObSets}
    (KD : KeysAt env U Δ (doms.map (·.instL ls)) ys keysD S') :
    ∃ (keysF : List Key) (S'' : ObSets),
      KeysAt env U Δ (hdoms.map (·.instL ls))
        ((famArgs info doms.length idx ls).map (·.subst (VExpr.argSubst ys))) keysF S'' ∧
      (∀ (i : Nat) (kf kd : Key), i < info.nparams → keysF[i]? = some kf → keysD[i]? = some kd →
        kf.2.1 = kd.2.1 ∧ ∀ y, y ∈ kf.2.2 ↔ y ∈ kd.2.2) ∧
      ∀ (i : Nat) (k : Key), keysF[i]? = some k → ∀ y ∈ k.2.2,
        ∃ a, (famArgs info doms.length idx ls)[i]? = some a ∧
          Obs' (VExpr.argSubst ys) S' a y := by
  have hn := C.np_le
  have hyl : ys.length = doms.length := by simpa using KD.ylen
  have hkl : keysD.length = doms.length := by simpa using KD.len
  have hAl : (famArgs info doms.length idx ls).length = (hdoms.map (·.instL ls)).length := by
    simp [famArgs_length, C.idx_len, C.hdoms_len]
  obtain ⟨v, hR⟩ := C.hts
  rw [ctorRes_instL hlen] at hR
  obtain ⟨W', tv'⟩ := TeleKeys.typed henv hΔ KD.tele C.piSD.doms .nil TV.empty
  simp only [List.append_nil] at W' tv'
  obtain ⟨W2, tv2⟩ := spine_tele henv hΔ hR W' tv' C.famConst C.famSub C.famPi (by omega)
  rw [hAl, List.take_length] at W2 tv2
  -- the demands: the parameter keys of the constructor
  let F : List (List Ob) := (keysD.take info.nparams).map (·.2.2) ++
    List.replicate info.nindices []
  have hF : F.length = (hdoms.map (·.instL ls)).length := by
    simp [F, C.hdoms_len]; omega
  have hFi : ∀ i Fi, F[i]? = some Fi → ∀ y ∈ Fi, ∃ kd : Key, i < info.nparams ∧
      keysD[i]? = some kd ∧ y ∈ kd.2.2 := by
    intro i Fi hFi y hy
    simp only [F, List.getElem?_append, List.length_map, List.length_take] at hFi
    split at hFi
    · rename_i hi
      rw [List.getElem?_map, List.getElem?_take] at hFi
      split at hFi
      · rename_i hi'
        rw [List.getElem?_eq_getElem (show i < keysD.length by omega)] at hFi
        cases hFi
        exact ⟨_, hi', List.getElem?_eq_getElem _, hy⟩
      · cases hFi
    · rw [List.getElem?_replicate] at hFi
      split at hFi <;> cases hFi
      cases hy
  have hbv : ∀ i (kd : Key), i < info.nparams → keysD[i]? = some kd → ∀ y,
      Obs' (VExpr.argSubst ys) S' (.bvar (doms.length - 1 - i)) y ↔ y ∈ kd.2.2 := by
    intro i kd hi hkd y
    rw [Obs.bvar_iff]
    refine KD.sets (doms.length - 1 - i) kd ?_ (by simp; omega) y
    simpa [show doms.length - 1 - (doms.length - 1 - i) = i by omega] using hkd
  have hSx : ∀ i (a : VExpr), (famArgs info doms.length idx ls)[i]? = some a → ∀ y,
      argSets env U Δ (VExpr.argSubst ys) S' (famArgs info doms.length idx ls)
        ((hdoms.map (·.instL ls)).length - 1 - i) y ↔ Obs' (VExpr.argSubst ys) S' a y := by
    intro i a ha y; rw [← hAl]; exact argSets_get ha
  obtain ⟨keysF, S'', hT, hkFl, hS, hk⟩ := tele_compact (D := hdoms.map (·.instL ls))
    (as := (famArgs info doms.length idx ls).map (·.subst (VExpr.argSubst ys)))
    (fun i hi => C.famClosed i (by simpa using hi)) (by simp [hAl]) W2 tv2 F hF
    (fun i Fi hF' y hy => by
      obtain ⟨kd, hi, hkd, hyk⟩ := hFi i Fi hF' y hy
      exact (hSx i _ (famArgs_param hi hn) y).2 ((hbv i kd hi hkd y).2 hyk))
  have KF := KeysAt.of_tele henv hΔ hT (by simp [hAl]) hS
  refine ⟨keysF, S'', KF, fun i kf kd hi hkf hkd => ?_, fun i k hki y hy => ?_⟩
  · obtain ⟨hdem, hsub, -⟩ := hk i kf hkf
    refine ⟨?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · obtain ⟨e1, e2, -⟩ := KF.cls i kf hkf
      obtain ⟨e3, e4, -⟩ := KD.cls i kd hkd
      rw [e2, e4, e1, e3]
      have hys : ((famArgs info doms.length idx ls).map
          (·.subst (VExpr.argSubst ys))).getD i (.sort .zero) = ys.getD i (.sort .zero) := by
        simp only [List.getD_eq_getElem?_getD, famArgs_subst_param hyl hn hi]
      have htk : ((famArgs info doms.length idx ls).map
          (·.subst (VExpr.argSubst ys))).take i = ys.take i :=
        famArgs_subst_take hyl hn (by omega)
      rw [hys, htk]
      congr 1
      -- the link between the header's and the constructor's parameter domains
      have W3 := substEq_take (Ds := hdoms.map (·.instL ls))
        ((famArgs info doms.length idx ls).map (·.subst (VExpr.argSubst ys)))
        ((famArgs info doms.length idx ls).map (·.subst (VExpr.argSubst ys))) rfl
        (by simp [hAl]) (by rw [List.length_map, hAl, List.take_length]; exact W2) info.nparams (by simp [famArgs_length])
      rw [famArgs_subst_take hyl hn (Nat.le_refl _)] at W3
      have hyn : (ys.take info.nparams).length = info.nparams := by simp; omega
      obtain ⟨-, hcls⟩ := C.bridge (as := ys.take info.nparams) (by omega) (by rw [hyn]; exact W3)
      have := hcls i (by omega)
      rwa [List.take_take, Nat.min_eq_left (by omega)] at this
    · have := hsub y hy
      rw [hSx i _ (famArgs_param hi hn)] at this
      exact (hbv i kd hi hkd y).1 this
    · refine hdem _ ?_ y hy
      simp only [F, List.getElem?_append_left (show i < ((keysD.take info.nparams).map
        (·.2.2)).length by simp; omega), List.getElem?_map, List.getElem?_take, hi, if_true, hkd,
        Option.map_some]
  · obtain ⟨-, hsub, -⟩ := hk i k hki
    have hil : i < (famArgs info doms.length idx ls).length := by
      have := (List.getElem?_eq_some_iff.1 hki).1; omega
    have ha := List.getElem?_eq_getElem hil
    exact ⟨_, ha, (hSx i _ ha y).1 (hsub y hy)⟩

/-- **The projection classes of a constructor spine at related anchors**: the projections onto
field `i` of the class of the constructor applied to anchors `ys` related along its telescope
form the class of the anchor of field `i`, at the type class of the field domain. -/
theorem ctor_field_cls {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hcl : info.ctorType.Closed) {ls : List VLevel} {doms idx hdoms : List VExpr}
    {famType : VExpr} (C : ProjCtx env U Δ S info ls doms idx famType hdoms)
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = info.uvars)
    (hnz : (info.resultLevel.inst ls).IsNeverZero) {ys : List VExpr}
    (hyl : ys.length = doms.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst ys) (VExpr.argSubst ys)
      (doms.map (·.instL ls)).reverse) :
    ∀ i, info.nparams + i < doms.length →
      projCls env U Δ S i (ElCls env U Δ (TyCls env U Δ
          (((ctorRes S info doms.length idx).instL ls).subst (VExpr.argSubst ys)))
          (.mkApps (.const info.ctorName ls) ys))
        (TyCls env U Δ (((doms.map (·.instL ls)).getD (info.nparams + i) (.sort .zero)).subst
          (VExpr.argSubst (ys.take (info.nparams + i))))) =
      ElCls env U Δ (TyCls env U Δ (((doms.map (·.instL ls)).getD (info.nparams + i)
          (.sort .zero)).subst (VExpr.argSubst (ys.take (info.nparams + i)))))
        (ys.getD (info.nparams + i) (.sort .zero)) := by
  intro i hi
  have T := C.tele
  have hn := C.np_le
  have hDl : (doms.map (·.instL ls)).length = doms.length := by simp
  have hnf : info.numFields = doms.length - info.nparams := by rw [T.numFields, hDl]
  -- parameters and fields
  have hys : ys = ys.take info.nparams ++ ys.drop info.nparams := (List.take_append_drop _ _).symm
  generalize hps : ys.take info.nparams = ps at hys
  generalize hfs : ys.drop info.nparams = fs at hys
  have hpl : ps.length = info.nparams := by rw [← hps]; simp; omega
  have hfl : fs.length = info.numFields := by rw [← hfs, hnf]; simp [hyl]
  subst hys
  have W' : Ctx.SubstEq env U Δ (VExpr.argSubst (ps ++ fs)) (VExpr.argSubst (ps ++ fs))
      ((doms.map (·.instL ls)).take (ps ++ fs).length).reverse := by
    rw [hyl, ← hDl, List.take_length]; exact W
  have hargs : ArgsTyped env U Δ (info.ctorType.instL ls) (ps ++ fs)
      ((VExpr.wrapForalls ((doms.map (·.instL ls)).drop ([] ++ (ps ++ fs)).length)
        ((ctorRes S info doms.length idx).instL ls)).subst
        (VExpr.argSubst ([] ++ (ps ++ fs)))) := by
    have := ArgsTyped.of_substEq (D := doms.map (·.instL ls))
      (R0 := (ctorRes S info doms.length idx).instL ls) (ps ++ fs) [] (by simp; omega)
      (by rw [List.nil_append]; exact W')
    rwa [List.length_nil, List.drop_zero,
      show VExpr.argSubst [] = VExpr.Subst.id from rfl, VExpr.subst_id, ← T.shape] at this
  have hall : (ps ++ fs).length = doms.length := hyl
  have hres := spine_result (S := S) (idx := idx) (doms := doms) hlen hpl hall
  have hctorRes : ((ctorRes S info doms.length idx).instL ls).subst (VExpr.argSubst (ps ++ fs)) =
      VExpr.mkApps (.const S ls) (ps ++ idx.map fun e =>
        (e.instL ls).subst (VExpr.argSubst (ps ++ fs))) := hres
  have CP := fun i (hi : i < fs.length) =>
    ctor_projCls henv hΔ hp hcl hls hlen hnz C.shape C.idx_len C.wf C.ctor hargs hpl hfl hi
  rw [hctorRes]
  -- the substitutions of the earlier projections and of the earlier fields are related
  have key : ∀ j, j ≤ fs.length →
      Ctx.SubstEq env U Δ
        (VExpr.argSubst (ps ++ projsOf S (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs)) j))
        (VExpr.argSubst (ps ++ fs.take j)) ((doms.map (·.instL ls)).take (info.nparams + j)).reverse := by
    intro j
    induction j with
    | zero =>
      intro _
      have := substEq_take (Ds := doms.map (·.instL ls)) (ps ++ fs) (ps ++ fs) rfl
        (by simp; omega) W' info.nparams (by simp; omega)
      simpa [projsOf, List.take_append_of_le_length, hpl] using this
    | succ j ih =>
      intro hj
      have Wj := ih (by omega)
      have hk : info.nparams + j < (doms.map (·.instL ls)).length := by simp; omega
      obtain ⟨u, hu⟩ := T.doms _ hk
      obtain ⟨-, F, hF, hdef, -⟩ := CP j (by omega)
      rw [T.fieldType hlen hpl _ hk, Option.some.injEq] at hF
      subst hF
      rw [projsOf_succ, ← List.append_assoc, List.take_succ_eq_append_getElem (by omega),
        ← List.append_assoc, show info.nparams + (j + 1) = (info.nparams + j) + 1 by omega,
        List.take_succ_eq_append_getElem hk, List.reverse_append, List.reverse_singleton,
        List.singleton_append, VExpr.argSubst_append_one, VExpr.argSubst_append_one]
      exact .cons (by rw [VExpr.Subst.cons_tail, VExpr.Subst.cons_tail]; exact Wj) hu
        (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_head, VExpr.Subst.cons_tail]; exact hdef)
  have hi' : i < fs.length := by omega
  obtain ⟨-, F, hF, -, hcls⟩ := CP i hi'
  have hk : info.nparams + i < (doms.map (·.instL ls)).length := by simp; omega
  rw [T.fieldType hlen hpl _ hk, Option.some.injEq] at hF
  subst hF
  obtain ⟨u, hu⟩ := T.doms _ hk
  have hconv := hu.substDF henv (T.ctx _ (by omega)) hΔ (key i (by omega))
  simp only [VExpr.subst] at hconv
  have eT := TyCls.eq_of_defeq hconv
  have e1 : (ps ++ fs).take (info.nparams + i) = ps ++ fs.take i := by
    rw [List.take_add, List.take_left' hpl, List.drop_left' hpl]
  have e2 : (doms.map (·.instL ls)).getD (info.nparams + i) (.sort .zero) =
      (doms.map (·.instL ls))[info.nparams + i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have e3 : (ps ++ fs).getD (info.nparams + i) (.sort .zero) = fs[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show ps.length ≤ info.nparams + i by omega), hpl,
      List.getElem?_eq_getElem hi']
  rw [e1, e2, e3, ← eT]
  exact hcls

/-- **Field-domain and field-type observations of the constructor's codomain.** At the
extension of the constructor telescope by typed keys `keysD` (anchors `ys`), the codomain
`S ls (params, idx)` of a never-zero entry has the field-domain observation of field `j` at the
earlier field keys of `keysD`, and a field-type observation for every observation of the field
domain at the keys. -/
theorem fam_field_obs {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hrig : env.Rigid S) {ls : List VLevel} {doms idx hdoms : List VExpr} {famType : VExpr}
    (C : ProjCtx env U Δ S info ls doms idx famType hdoms) (hlen : ls.length = info.uvars)
    (hnz : (info.resultLevel.inst ls).IsNeverZero) {ys : List VExpr} {keysD : List Key}
    {S' : ObSets} (KD : KeysAt env U Δ (doms.map (·.instL ls)) ys keysD S')
    {j : Nat} (hj : info.nparams + j < doms.length) :
    Obs' (VExpr.argSubst ys) S' ((ctorRes S info doms.length idx).instL ls)
      (.fieldDom S j ((keysD.drop info.nparams).take j)
        (TyCls env U Δ (((doms.map (·.instL ls)).getD (info.nparams + j) (.sort .zero)).subst
          (VExpr.argSubst (ys.take (info.nparams + j)))))) ∧
    ∀ x, Obs' (VExpr.argSubst (ys.take (info.nparams + j)))
        (keySets (keysD.take (info.nparams + j)))
        ((doms.map (·.instL ls)).getD (info.nparams + j) (.sort .zero)) x →
      Obs' (VExpr.argSubst ys) S' ((ctorRes S info doms.length idx).instL ls)
        (.fieldTy S j ((keysD.drop info.nparams).take j) x) := by
  have hn := C.np_le
  have hyl : ys.length = doms.length := by simpa using KD.ylen
  have hkl : keysD.length = doms.length := by simpa using KD.len
  have hDl : (doms.map (·.instL ls)).length = doms.length := by simp
  have hnf : info.numFields = doms.length - info.nparams := by rw [C.tele.numFields, hDl]
  obtain ⟨keysF, S'', KF, hpar, hobs⟩ := fam_keys henv hΔ C hlen KD
  have hkFl : keysF.length = info.nparams + info.nindices := by
    simpa [C.hdoms_len] using KF.len
  have hAl : (famArgs info doms.length idx ls).length = keysF.length := by
    simp [famArgs_length, C.idx_len, hkFl]
  rw [ctorRes_instL hlen]
  -- the keys of the family application
  have hargs : List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1
      (a.subst (VExpr.argSubst ys)) ∧ ∀ x ∈ k.2.2, Obs' (VExpr.argSubst ys) S' a x)
      keysF (famArgs info doms.length idx ls) := by
    refine List.forall₂_of_getElem (by omega) fun i h1 h2 => ⟨?_, fun x hx => ?_⟩
    · obtain ⟨-, e2, -⟩ := KF.cls i _ (List.getElem?_eq_getElem h1)
      rw [e2]; congr 1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    · obtain ⟨a, ha, hxa⟩ := hobs i _ (List.getElem?_eq_getElem h1) x hx
      rw [List.getElem?_eq_getElem h2, Option.some.injEq] at ha
      rw [ha]; exact hxa
  -- typing of the end observations of the family application
  have hwind : ∀ r, (∀ cv, TypedOb env U Δ cv r [.sort (info.resultLevel.inst ls).eval]) →
      ∃ τs, (∀ τ ∈ τs, Obs' .id .empty ((⟨info.uvars, famType⟩ : VConstant).type.instL ls) τ) ∧
        ∀ cv, TypedOb env U Δ cv (wrap keysF r) τs := by
    intro r hr
    obtain ⟨τ₀, h1, h2⟩ := tele_wind0 KF.tele (R := .sort (info.resultLevel.inst ls))
      (τc := [.sort (info.resultLevel.inst ls).eval])
      (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort) hr
    obtain ⟨τs, h3, h4⟩ := exists_list_cover (R := fun y x => y ≼ x)
      fun τ hτ => C.famSub_symm τ (h1 τ hτ)
    exact ⟨τs, h3, fun cv => (h2 cv).strengthen h4⟩
  have hnz' : ∀ ns, (info.resultLevel.inst ls).eval ns ≠ 0 := hnz
  -- the chain of keys for the field domain
  let FL := (keysD.drop info.nparams).take j
  have hFLl : FL.length = j := by simp [FL]; omega
  have hKl : (keysF.take info.nparams ++ FL).length = info.nparams + j := by
    simp [FL, hkFl]; omega
  have hK : ∀ i (hi : i < info.nparams + j), ∃ kd : Key, keysD[i]? = some kd ∧
      (keysF.take info.nparams ++ FL)[i]? = some (if hip : i < info.nparams then
        (keysF[i]'(by omega)) else kd) ∧
      (∀ hip : i < info.nparams, (keysF[i]'(by omega)).2.1 = kd.2.1 ∧
        ∀ y, y ∈ (keysF[i]'(by omega)).2.2 ↔ y ∈ kd.2.2) := by
    intro i hi
    refine ⟨keysD[i]'(by omega), List.getElem?_eq_getElem _, ?_, fun hip =>
      hpar i _ _ hip (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)⟩
    by_cases hip : i < info.nparams
    · rw [dif_pos hip, List.getElem?_append_left (by simp; omega), List.getElem?_take,
        if_pos hip, List.getElem?_eq_getElem]
    · rw [dif_neg hip, List.getElem?_append_right (by simp; omega)]
      simp only [FL, List.length_take, hkFl, show min info.nparams (info.nparams + info.nindices) =
        info.nparams by omega, List.getElem?_take, List.getElem?_drop,
        show i - info.nparams < j by omega, if_true,
        show info.nparams + (i - info.nparams) = i by omega,
        List.getElem?_eq_getElem (show i < keysD.length by omega)]
  have hFor : List.Forall₂ (fun (k k' : Key) => ∀ y, y ∈ k.2.2 ↔ y ∈ k'.2.2)
      (keysF.take info.nparams ++ FL) (keysD.take (info.nparams + j)) := by
    refine List.forall₂_of_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : i < info.nparams + j := by omega
    obtain ⟨kd, hkd, hKi, hpi⟩ := hK i hi
    rw [List.getElem?_eq_getElem h1, Option.some.injEq] at hKi
    have : (keysD.take (info.nparams + j))[i] = kd := by
      rw [List.getElem_take]; exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hkd)
    rw [hKi, this]
    split
    · exact (hpi ‹_›).2
    · exact fun _ => Iff.rfl
  have hsetsK : keySets (keysF.take info.nparams ++ FL) = keySets (keysD.take (info.nparams + j)) :=
    keySets_congr hFor
  have hchain : ChainOK env U Δ (doms.map (·.instL ls)) (ys.take (info.nparams + j))
      (keysF.take info.nparams ++ FL) := by
    refine ⟨by simp [hKl]; omega, fun i a k ha hk => ?_⟩
    have hi : i < info.nparams + j := by
      have := (List.getElem?_eq_some_iff.1 hk).1; omega
    obtain ⟨kd, hkd, hKi, hpi⟩ := hK i hi
    rw [hk, Option.some.injEq] at hKi
    rw [List.getElem?_take, if_pos hi] at ha
    rw [List.take_take, Nat.min_eq_left (by omega)]
    obtain ⟨e1, e2, hc⟩ := KD.cls i kd hkd
    have hya : ys.getD i (.sort .zero) = a := by
      simp [List.getD_eq_getElem?_getD, ha]
    have hcls : k.2.1 = kd.2.1 := by
      subst hKi; split
      · exact (hpi ‹_›).1
      · rfl
    rw [hcls, ← e1]
    exact ⟨hc, by rw [e2, hya]; exact ElCls.self⟩
  have hshape : info.ctorType.instL ls = .wrapForalls (doms.map (·.instL ls))
      ((ctorRes S info doms.length idx).instL ls) := C.tele.shape
  have hlt : info.nparams + j < (doms.map (·.instL ls)).length := by simp; omega
  have hjnf : j < info.numFields := by omega
  constructor
  · obtain ⟨τs, h1, h2⟩ := hwind (.fieldDom S j FL _) fun cv =>
      .fieldDom (List.mem_singleton_self _) hnz'
    refine obs_mkApps_of_wrap hargs (.famDom hrig C.famConst hp hnz h1 (h2 _)
      (by omega) hjnf hFLl hshape hlt hchain rfl)
  · intro x hx
    obtain ⟨τs, h1, h2⟩ := hwind (.fieldTy S j FL x) fun cv =>
      .fieldTy (List.mem_singleton_self _) hnz'
    -- the typing lists of the chain's keys
    have hτ : ∀ i, ∃ τi : List Ob,
        (∀ (k : Key) τ, (keysF.take info.nparams ++ FL)[i]? = some k → τ ∈ τi →
          Obs' (VExpr.argSubst ((ys.take (info.nparams + j)).take i))
            (keySets ((keysF.take info.nparams ++ FL).take i))
            ((doms.map (·.instL ls)).getD i (.sort .zero)) τ) ∧
        (∀ (k : Key) y, (keysF.take info.nparams ++ FL)[i]? = some k → y ∈ k.2.2 →
          TypedOb env U Δ k.2.1 y τi) := by
      intro i
      by_cases hi : i < info.nparams + j
      · obtain ⟨kd, hkd, hKi, hpi⟩ := hK i hi
        obtain ⟨τi, h3, h4⟩ := TypedAt.merge (KD.typed i kd hkd)
        refine ⟨τi, fun k τ hk hτ => ?_, fun k y hk hy => ?_⟩
        · have e : keySets ((keysF.take info.nparams ++ FL).take i) = keySets (keysD.take i) := by
            rw [keySets_congr (forall₂_take i hFor), List.take_take, Nat.min_eq_left (by omega)]
          rw [List.take_take, Nat.min_eq_left (by omega), e]
          exact h3 τ hτ
        · rw [hKi, Option.some.injEq] at hk
          subst hk
          by_cases hip : i < info.nparams
          · rw [dif_pos hip] at hy ⊢
            rw [(hpi hip).1]
            exact h4 y (((hpi hip).2 y).1 hy)
          · rw [dif_neg hip] at hy ⊢
            exact h4 y hy
      · exact ⟨[], fun k τ hk => by
          have := (List.getElem?_eq_some_iff.1 hk).1; omega, fun k y hk => by
          have := (List.getElem?_eq_some_iff.1 hk).1; omega⟩
    refine obs_mkApps_of_wrap hargs (.famTy hrig C.famConst hp hnz h1 (h2 _)
      (by omega) hjnf hFLl hshape hlt hchain ?_ (τk := fun i => (hτ i).choose)
      (fun i k τ hk hτ' => (hτ i).choose_spec.1 k τ hk hτ')
      (fun i k y hk hy => (hτ i).choose_spec.2 k y hk hy) ?_)
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · exact KF.backed k (List.mem_of_mem_take hk)
      · exact KD.backed k (List.mem_of_mem_drop (List.mem_of_mem_take hk))
    · rw [hsetsK]; exact hx

/-- The context of a field observation of a constructor spine: the observation lists of the
earlier field keys. -/
def fieldCtx (np : Nat) (keys : List Key) (j : Nat) : List (List Ob) :=
  ((keys.drop np).take j).map (·.2.2)

/-- The empty key. -/
def Key.none : Key := (fun _ => False, fun _ => False, [])

/-- **Field observations are typed at the constructor's codomain.** At the extension of the
constructor telescope of a never-zero entry by typed keys `keysD` (anchors `ys`), every field
observation of the field keys is typed, at the class of the constructor applied to the anchors,
at observations of the codomain `S ls (params, idx)`. -/
theorem field_typed {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hst : ProjStatic env S info) {ls : List VLevel} {doms idx hdoms : List VExpr}
    {famType : VExpr} (C : ProjCtx env U Δ S info ls doms idx famType hdoms)
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = info.uvars)
    (hnz : (info.resultLevel.inst ls).IsNeverZero) {ys : List VExpr} {keysD : List Key}
    {S' : ObSets} (KD : KeysAt env U Δ (doms.map (·.instL ls)) ys keysD S') :
    ∀ j, info.nparams + j < doms.length → ∀ kj, keysD[info.nparams + j]? = some kj →
      ∀ k ∈ kj.2.2,
      TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ
          (((ctorRes S info doms.length idx).instL ls).subst (VExpr.argSubst ys)))
          (.mkApps (.const info.ctorName ls) ys))
        (VExpr.argSubst ys) S' ((ctorRes S info doms.length idx).instL ls)
        (.fieldOb S j (fieldCtx info.nparams keysD j) k) := by
  have hn := C.np_le
  have hyl : ys.length = doms.length := by simpa using KD.ylen
  have hkl : keysD.length = doms.length := by simpa using KD.len
  have hDl : (doms.map (·.instL ls)).length = doms.length := by simp
  have hnf : info.numFields = doms.length - info.nparams := by rw [C.tele.numFields, hDl]
  obtain ⟨W, -⟩ := TeleKeys.typed henv hΔ KD.tele C.piSD.doms .nil TV.empty
  simp only [List.append_nil] at W
  have hcls := ctor_field_cls henv hΔ hp hst.ctorClosed C hls hlen hnz hyl W
  -- the class of a field key is the class of the projections
  have hkcls : ∀ i (k : Key), info.nparams + i < doms.length →
      keysD[info.nparams + i]? = some k →
      k.2.1 = projCls env U Δ S i (ElCls env U Δ (TyCls env U Δ
          (((ctorRes S info doms.length idx).instL ls).subst (VExpr.argSubst ys)))
          (.mkApps (.const info.ctorName ls) ys))
        (TyCls env U Δ (((doms.map (·.instL ls)).getD (info.nparams + i) (.sort .zero)).subst
          (VExpr.argSubst (ys.take (info.nparams + i))))) := by
    intro i k hi hk
    obtain ⟨e1, e2, -⟩ := KD.cls _ k hk
    rw [hcls i hi, e2, e1]
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
  intro hj kj hkj k hk
  have hjnf : j < info.numFields := by omega
  obtain ⟨hDom, hTy⟩ := fam_field_obs henv hΔ hp hst.famRigid C hlen hnz KD hj
  obtain ⟨τd, hτd, hkτ⟩ := KD.typed _ kj hkj k hk
  -- the recursive field observations of the context
  let Wl : List Ob := (List.range j).flatMap fun i =>
    ((keysD.getD (info.nparams + i) Key.none).2.2).map fun y =>
      .fieldOb S i (fieldCtx info.nparams keysD i) y
  have hWl : ∀ w ∈ Wl, TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ
        (((ctorRes S info doms.length idx).instL ls).subst (VExpr.argSubst ys)))
        (.mkApps (.const info.ctorName ls) ys))
      (VExpr.argSubst ys) S' ((ctorRes S info doms.length idx).instL ls) w := by
    intro w hw
    simp only [Wl, List.mem_flatMap, List.mem_range, List.mem_map] at hw
    obtain ⟨i, hi, y, hy, rfl⟩ := hw
    have hk' : keysD[info.nparams + i]? = some (keysD.getD (info.nparams + i) Key.none) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    exact ih i hi (by omega) _ hk' y hy
  obtain ⟨τrec, hτrec, hrec⟩ := TypedAt.merge hWl
  let FL := (keysD.drop info.nparams).take j
  refine ⟨.fieldDom S j FL (TyCls env U Δ (((doms.map (·.instL ls)).getD (info.nparams + j)
    (.sort .zero)).subst (VExpr.argSubst (ys.take (info.nparams + j))))) ::
      (τd.map (.fieldTy S j FL ·) ++ τrec), fun τ hτ => ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_append, List.mem_map] at hτ
    rcases hτ with rfl | ⟨x, hx, rfl⟩ | hτ
    · exact hDom
    · exact hTy x (hτd x hx)
    · exact hτrec τ hτ
  -- the compatibility of the context keys
  have hFL : FLCompat env U Δ S (ElCls env U Δ (TyCls env U Δ
        (((ctorRes S info doms.length idx).instL ls).subst (VExpr.argSubst ys)))
        (.mkApps (.const info.ctorName ls) ys))
      (fieldCtx info.nparams keysD j) FL := by
    refine ⟨by simp [fieldCtx, FL], fun i F Li hF hLi => ?_⟩
    have hij : i < j := by
      have := (List.getElem?_eq_some_iff.1 hF).1; simp [FL] at this; omega
    have hF' : keysD[info.nparams + i]? = some F := by
      simpa [FL, List.getElem?_take, hij, List.getElem?_drop] using hF
    have hLi' : Li = F.2.2 := by
      simp only [fieldCtx, List.getElem?_map] at hLi
      rw [show ((keysD.drop info.nparams).take j)[i]? = some F from hF] at hLi
      exact (Option.some.inj hLi).symm
    subst hLi'
    exact ⟨⟨_, hkcls i F (by omega) hF'⟩, fun y hy => ⟨y, hy, .refl⟩⟩
  refine .fieldOb hp hjnf (by simp [fieldCtx]; omega) (List.mem_cons_self ..) hFL
    (fun x hx => ⟨FL, List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hx)),
      hFL⟩) ?_ fun i Li hLi y hy => ?_
  · rw [← hkcls j kj hj hkj]; exact hkτ
  · have hij : i < j := by
      have := (List.getElem?_eq_some_iff.1 hLi).1; simp [fieldCtx] at this; omega
    have hLi' : Li = (keysD.getD (info.nparams + i) Key.none).2.2 := by
      simp only [fieldCtx, List.getElem?_map, List.getElem?_take, hij, if_true,
        List.getElem?_drop] at hLi
      rw [List.getElem?_eq_getElem (show info.nparams + i < keysD.length by omega)] at hLi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show info.nparams + i < keysD.length by omega)]
      exact (Option.some.inj hLi).symm
    have hctx : (fieldCtx info.nparams keysD j).take i = fieldCtx info.nparams keysD i :=
      take_map_take (Nat.le_of_lt hij)
    rw [hctx]
    refine (hrec _ ?_).mono fun τ hτ => List.mem_cons_of_mem _ (List.mem_append_right _ hτ)
    simp only [Wl, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨i, hij, y, hLi' ▸ hy, rfl⟩

/-- **Field observations of constructor spines.** A semantically typed constructor spine
`mk ps fs` of a projection entry that is never zero at the constructor's levels has, for every
observation `k` of the field `fs[j]`, a field observation `fieldOb S j L k`. -/
theorem ctor_field_obs {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hPV : ProjValid env S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = info.uvars)
    (hnz : (info.resultLevel.inst ls).IsNeverZero)
    {Γ : List VExpr} {σ : VExpr.Subst} {S0 : ObSets}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S0)
    {ps fs : List VExpr} {T : VExpr}
    (H : HTS env U Δ Γ (.mkApps (.const info.ctorName ls) (ps ++ fs)) T)
    (hpl : ps.length = info.nparams) (hfl : fs.length = info.numFields)
    {j : Nat} (hj : j < fs.length) {k : Ob} (hk : Obs env U Δ σ S0 fs[j] k) :
    ∃ L, Obs env U Δ σ S0 (.mkApps (.const info.ctorName ls) (ps ++ fs)) (.fieldOb S j L k) := by
  obtain ⟨doms, idx, famType, hdoms, C⟩ := ProjValid.ctx henv hΔ hp hPV hls
  have hn := C.np_le
  have hDl : (doms.map (·.instL ls)).length = doms.length := by simp
  have hnf : info.numFields = doms.length - info.nparams := by rw [C.tele.numFields, hDl]
  have hal : (ps ++ fs).length = doms.length := by simp; omega
  have hjD : info.nparams + j < doms.length := by omega
  -- typed keys of the spine, with the demand `k` at the field
  let F : List (List Ob) := (List.range doms.length).map fun i =>
    if i = info.nparams + j then [k] else []
  have hF : F.length = doms.length := by simp [F]
  have hfj : (ps ++ fs)[info.nparams + j]? = some fs[j] := by
    rw [List.getElem?_append_right (by omega)]; simp [hpl, List.getElem?_eq_getElem hj]
  obtain ⟨keysD, S', KD, hkd⟩ := ctor_keys henv hΔ C W tv H hal F hF (fun i Fi hFi y hy => by
    simp only [F, List.getElem?_map] at hFi
    rcases Nat.lt_or_ge i doms.length with hi | hi
    · rw [List.getElem?_range hi, Option.map_some, Option.some.injEq] at hFi
      subst hFi
      split at hy
      · rename_i hi
        rw [List.mem_singleton] at hy; subst hy; subst hi
        exact ⟨_, hfj, hk⟩
      · cases hy
    · rw [List.getElem?_eq_none (by simpa using hi)] at hFi; cases hFi)
  have hkl : keysD.length = doms.length := by simpa using KD.len
  have hkj : keysD[info.nparams + j]? = some (keysD[info.nparams + j]'(by omega)) :=
    List.getElem?_eq_getElem _
  have hkk : k ∈ (keysD[info.nparams + j]'(by omega)).2.2 := by
    refine (hkd _ _ hkj).1 [k] ?_ k (List.mem_singleton_self _)
    simp [F, List.getElem?_range hjD]
  have hty := field_typed henv hΔ hp hPV.1 C hls hlen hnz KD j hjD _ hkj k hkk
  -- winding up the constructor
  have hf : env.HasType U Δ (.const info.ctorName ls)
      ((VExpr.wrapForalls (doms.map (·.instL ls)) ((ctorRes S info doms.length idx).instL ls)).subst
        .id) := by
    rw [VExpr.subst_id, ← C.tele.shape]; exact .const C.ctor hls hlen
  obtain ⟨ys', e, hyl', -, -, hwind⟩ := tele_wind henv hΔ KD.tele _ hf
  have eys : ys' = (ps ++ fs).map (·.subst σ) :=
    argSubst_inj (by simp at hyl' ⊢; omega) e.symm
  subst eys
  obtain ⟨τc, hτc, htc⟩ := hty
  obtain ⟨τ₀, h1, h2⟩ := hwind _ τc hτc htc
  rw [VExpr.subst_id, ← C.tele.shape] at h2
  refine ⟨fieldCtx info.nparams keysD j, obs_mkApps_of_wrap ?_ (.projCtor hp rfl C.ctor
    (fun τ hτ => by rw [show (⟨info.uvars, info.ctorType⟩ : VConstant).type = info.ctorType
      from rfl, C.tele.shape]; exact h1 τ hτ) h2 (by omega)
    ⟨j, _, k, rfl, by omega, by simp [fieldCtx]; omega, fun i Li hLi => ?_, _, hkj, hkk⟩
    KD.backed)⟩
  · refine List.forall₂_of_getElem (by omega) fun i h1 h2 => ⟨?_, fun x hx => ?_⟩
    · obtain ⟨-, e2, -⟩ := KD.cls i _ (List.getElem?_eq_getElem h1)
      rw [e2]; congr 1
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h2]; rfl
    · obtain ⟨a, ha, hxa⟩ := (hkd i _ (List.getElem?_eq_getElem h1)).2 x hx
      rw [List.getElem?_eq_getElem h2, Option.some.injEq] at ha
      rw [ha]; exact hxa
  · have hij : i < j := by
      have := (List.getElem?_eq_some_iff.1 hLi).1; simp [fieldCtx] at this; omega
    simp only [fieldCtx, List.getElem?_map, List.getElem?_take, hij, if_true,
      List.getElem?_drop, List.getElem?_eq_getElem (show info.nparams + i < keysD.length by omega),
      Option.map_some, Option.some.injEq] at hLi
    exact ⟨_, List.getElem?_eq_getElem _, fun y hy => hLi ▸ hy⟩

omit henv hΔ in
/-- Typed keys at the substituted arguments, with observations from the arguments, are chain
keys of the arguments. -/
theorem KeysAt.chainArgs {D args : List VExpr} {keys : List Key} {S' : ObSets}
    {σ : VExpr.Subst} {S0 : ObSets}
    (K : KeysAt env U Δ D (args.map (·.subst σ)) keys S')
    (hobs : ∀ (i : Nat) (k : Key), keys[i]? = some k → ∀ y ∈ k.2.2,
      ∃ a, args[i]? = some a ∧ Obs' σ S0 a y) :
    ChainArgs env U Δ σ S0 keys args := by
  have hl : keys.length = args.length := by have := K.len; have := K.ylen; simp at *; omega
  refine List.forall₂_of_getElem hl fun i h1 h2 => ⟨?_, fun y hy => ?_⟩
  · obtain ⟨-, e2, -⟩ := K.cls i _ (List.getElem?_eq_getElem h1)
    rw [e2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h2]
    exact ElCls.self
  · obtain ⟨a, ha, hya⟩ := hobs i _ (List.getElem?_eq_getElem h1) y hy
    rw [List.getElem?_eq_getElem h2, Option.some.injEq] at ha
    exact ⟨y, ha ▸ hya, .refl⟩

/-- The rigid observation of the constructor's codomain `S ls (params, idx)`, at the extension
of the constructor telescope by typed keys. -/
theorem fam_rigid_obs {S : Name} {info : VProjectionInfo} (hrig : env.Rigid S)
    {ls : List VLevel} {doms idx hdoms : List VExpr} {famType : VExpr}
    (C : ProjCtx env U Δ S info ls doms idx famType hdoms) (hlen : ls.length = info.uvars)
    {ys : List VExpr} {keysD : List Key} {S' : ObSets}
    (KD : KeysAt env U Δ (doms.map (·.instL ls)) ys keysD S') :
    Obs' (VExpr.argSubst ys) S' ((ctorRes S info doms.length idx).instL ls)
      (.rigid S (ls.map (·.eval)) (info.nparams + info.nindices)
        (info.resultLevel.inst ls).eval) := by
  obtain ⟨keysF, S'', KF, -, hobs⟩ := fam_keys henv hΔ C hlen KD
  have hkFl : keysF.length = info.nparams + info.nindices := by
    simpa [C.hdoms_len] using KF.len
  have hAl : (famArgs info doms.length idx ls).length = keysF.length := by
    simp [famArgs_length, C.idx_len, hkFl]
  rw [ctorRes_instL hlen]
  have hargs : List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1
      (a.subst (VExpr.argSubst ys)) ∧ ∀ x ∈ k.2.2, Obs' (VExpr.argSubst ys) S' a x)
      keysF (famArgs info doms.length idx ls) := by
    refine List.forall₂_of_getElem (by omega) fun i h1 h2 => ⟨?_, fun x hx => ?_⟩
    · obtain ⟨-, e2, -⟩ := KF.cls i _ (List.getElem?_eq_getElem h1)
      rw [e2]; congr 1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    · obtain ⟨a, ha, hxa⟩ := hobs i _ (List.getElem?_eq_getElem h1) x hx
      rw [List.getElem?_eq_getElem h2, Option.some.injEq] at ha
      rw [ha]; exact hxa
  obtain ⟨τ₀, h1, h2⟩ := tele_wind0 KF.tele (R := .sort (info.resultLevel.inst ls))
    (o := .rigid S (ls.map (·.eval)) keysF.length (info.resultLevel.inst ls).eval)
    (τc := [.sort (info.resultLevel.inst ls).eval])
    (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort)
    (fun cv => .rigid (List.mem_singleton_self _))
  obtain ⟨τs, h3, h4⟩ := exists_list_cover (R := fun y x => y ≼ x)
    fun τ hτ => C.famSub_symm τ (h1 τ hτ)
  rw [← hkFl]
  exact obs_mkApps_of_wrap hargs (.const hrig C.famConst h3 ((h2 _).strengthen h4)
    (.inl ⟨_, rfl⟩))

/-- **Constructor spines typed at a family application.** A semantically typed constructor
spine of a projection entry, at the application of the family at levels where the entry is
never zero, has the constructor's arity, and the entry is never zero at the constructor's
levels. -/
theorem ctor_spine_fam {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hPV : ProjValid env S info) {Γ : List VExpr} {σ : VExpr.Subst} {S0 : ObSets}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S0)
    {lsm ls' : List VLevel} {args xs : List VExpr}
    (H : HTS env U Δ Γ (.mkApps (.const info.ctorName lsm) args) (.mkApps (.const S ls') xs))
    (hnz : (info.resultLevel.inst ls').IsNeverZero) :
    (∀ l ∈ lsm, l.WF U) ∧ lsm.length = info.uvars ∧
      args.length = info.nparams + info.numFields ∧
      (info.resultLevel.inst lsm).IsNeverZero := by
  have hst := hPV.1
  obtain ⟨ci, hci, hls, hlenci, hcod⟩ := HTS.spineCod henv hΔ H rfl W tv
  cases hci.symm.trans (henv.ordered.projectionConstructor hp)
  have hlen : lsm.length = info.uvars := hlenci
  obtain ⟨doms, idx, famType, hdoms, C⟩ := ProjValid.ctx henv hΔ hp hPV hls
  have hn := C.np_le
  have hDl : (doms.map (·.instL lsm)).length = doms.length := by simp
  have hnf : info.numFields = doms.length - info.nparams := by rw [C.tele.numFields, hDl]
  have hTh : (⟨info.uvars, info.ctorType⟩ : VConstant).type.instL lsm =
      .wrapForalls (doms.map (·.instL lsm)) ((ctorRes S info doms.length idx).instL lsm) :=
    C.tele.shape
  rw [hTh] at hcod
  have noPiDom : ∀ {σ' S1 ls1 xs1 D}, Obs' σ' S1 (.mkApps (.const S ls1) xs1) (.piDom D) →
      False := fun h => by
    obtain ⟨_, h⟩ := Obs.famSpine_notApp hst.famRigid hst.famNotProjCtor h trivial
    exact FamEnd.not_piDom h
  -- the arity is at most the constructor's
  have hle : args.length ≤ doms.length := by
    refine Nat.le_of_not_lt fun hlt => ?_
    obtain ⟨Th, As, hHT, -, hAl, hdom, -⟩ :=
      HTS.spineRev henv hΔ H rfl ⟨_, _, rfl⟩ W tv
    obtain ⟨c', ls1, ci', e, hci', -, rfl⟩ := hHT
    cases e
    cases hci'.symm.trans (henv.ordered.projectionConstructor hp)
    obtain ⟨-, ⟨keys, hk, hobs⟩, -⟩ := hdom doms.length (As[doms.length]'(by omega))
      (args[doms.length]'hlt) (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
    have hkl : keys.length = doms.length := by rw [hk.length]; simp; omega
    rw [hTh] at hobs
    obtain ⟨_, _, -, -, -, hz⟩ := tele_split (by rw [hkl, hDl]; exact Nat.le_refl _) hobs
    have e : (doms.map (·.instL lsm)).drop keys.length = [] := by
      rw [hkl, ← hDl, List.drop_length]
    rw [e] at hz
    have hz' : Obs' _ _ ((ctorRes S info doms.length idx).instL lsm) _ := hz
    rw [ctorRes_instL hlen] at hz'
    exact noPiDom hz'
  -- the arity is at least the constructor's
  have hge : doms.length ≤ args.length := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have hTW : Ob.Sub (Obs' .id .empty ((⟨info.uvars, info.ctorType⟩ : VConstant).type.instL lsm))
        (Obs' .id .empty (.wrapForalls (doms.map (·.instL lsm))
          ((ctorRes S info doms.length idx).instL lsm))) := by rw [hTh]; exact Ob.Sub.refl
    obtain ⟨W1, tv1⟩ := spine_tele henv hΔ H W tv (henv.ordered.projectionConstructor hp) hTW C.piSD
      (by simp; omega)
    obtain ⟨keys, S'', hT, hkl, hS, hk⟩ := tele_compact
      (D := (doms.map (·.instL lsm)).take args.length) (as := args.map (·.subst σ))
      (fun i hi => by
        rw [List.getElem_take]; exact C.ctorClosed i (by simp at hi; omega))
      (by simp; omega) (by simpa using W1) (by simpa using tv1)
      (List.replicate args.length []) (by simp; omega)
      (fun i Fi hFi y hy => by
        rw [List.getElem?_replicate] at hFi; split at hFi <;> cases hFi; cases hy)
    have KF := KeysAt.of_tele henv hΔ hT (by simp; omega) hS
    have hch := KF.chainArgs fun i k hki y hy => by
      obtain ⟨-, h2, -⟩ := hk i k hki
      have hi : i < args.length := by
        have := (List.getElem?_eq_some_iff.1 hki).1; simp at hkl; omega
      have := h2 y hy
      rw [show ((doms.map (·.instL lsm)).take args.length).length = args.length by simp; omega]
        at this
      exact ⟨_, List.getElem?_eq_getElem hi, (argSets_get (List.getElem?_eq_getElem hi)).1 this⟩
    have hdrop : (doms.map (fun d : VExpr => d.instL lsm)).drop args.length =
        (doms.map (fun d : VExpr => d.instL lsm))[args.length]'(by simp; omega) ::
          (doms.map (fun d : VExpr => d.instL lsm)).drop (args.length + 1) :=
      List.drop_eq_getElem_cons _
    have hx : Obs' (VExpr.argSubst (args.map (·.subst σ))) S''
        (.wrapForalls ((doms.map (fun d : VExpr => d.instL lsm)).drop args.length)
          ((ctorRes S info doms.length idx).instL lsm))
        (.piDom (TyCls env U Δ (((doms.map (fun d : VExpr => d.instL lsm))[args.length]'(by simp; omega)).subst
          (VExpr.argSubst (args.map (·.subst σ)))))) := by
      rw [hdrop]; exact .piDom
    have := tele_obs hT hx
    rw [← VExpr.wrapForalls_append, List.take_append_drop] at this
    obtain ⟨x', hx', l⟩ := hcod keys hch _ this
    cases l.piDom_inv
    exact noPiDom hx'
  have hal : args.length = doms.length := by omega
  refine ⟨hls, hlen, by omega, ?_⟩
  -- the levels agree up to evaluation, by the rigid observation of the codomain
  obtain ⟨keysD, S', KD, hkd⟩ := ctor_keys henv hΔ C W tv H hal (List.replicate doms.length [])
    (by simp) (fun i Fi hFi y hy => by
      rw [List.getElem?_replicate] at hFi; split at hFi <;> cases hFi; cases hy)
  have hrig := fam_rigid_obs henv hΔ hst.famRigid C hlen KD
  have := tele_obs KD.tele hrig
  obtain ⟨x', hx', l⟩ := hcod keysD (KD.chainArgs fun i k hki => (hkd i k hki).2) _ this
  cases l.rigid_inv
  obtain ⟨_, h⟩ := Obs.famSpine_notApp hst.famRigid hst.famNotProjCtor hx' trivial
  obtain ⟨-, heq⟩ := h.rigid_eq
  intro ns
  have h1 := hnz ns
  rw [show (info.resultLevel.inst lsm).eval ns = info.resultLevel.evalAt (lsm.map (·.eval)) ns
    from congrFun (VLevel.eval_inst_eq_evalAt _ _) ns, heq,
    ← congrFun (VLevel.eval_inst_eq_evalAt _ _) ns]
  exact h1

end

end Model
end VEnv
end Lean4Lean
