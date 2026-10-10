import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleWind
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjValid
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CtorFieldObs
import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.FamilyHeader

/-! # The eta binding of rule clauses on majors of projection-registered families

Constructor spines of projection-registered families have only field observations (clause
`projCtor`), so the rule clauses identify the rule of such a major from the head type
(`EtaHead`) and bind its fields from the field observations of the major key (the eta
alternative of `RuleBind`). This file collects the facts used by the soundness of pattern rules
(`RuleSound.lean`, `CaseRuleSound.lean`) in that case:

* `MajorFam`: the static facts about the family of a rule's major that select the binding modes;
* `projctor_spine_inv`: field observations of a constructor spine come from the `projCtor`
  clause, with the field observation covered by an observation of the field argument;
* `eta_anchor_defeq`: an eta-bound anchor is definitionally equal to the field of the actual
  major (by `projIota`), which is the left-to-right direction of the binding. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The family `I` of the major of a pattern rule, with the major constructor `ctor`, the major
arguments `ms ++ fs.map .bvar` at the constructor levels `lsC`, in the rule instance at the
levels `ls`: either `I` is not projection-registered and `ctor` is not a projection
constructor (the constructor binding modes), or `I` is projection-registered with the
constructor `ctor`, the major is a full constructor application whose variable fields not bound
by the leading arguments are proper fields, and either the entry is never zero at the major's
levels (the eta binding) or every such field is a proof (the proof binding). -/
def MajorFam (env : VEnv) (U : Nat) (Δ Γ : List VExpr) (I ctor : Name)
    (doms lead ms : List VExpr) (fs : List Nat) (ls lsC : List VLevel) : Prop :=
  ((∀ info, ¬ env.projections I info) ∧ ¬ IsProjCtor env ctor) ∨
  ∃ info, env.projections I info ∧ ProjValid env I info ∧ info.ctorName = ctor ∧
    ms.length + fs.length = info.nparams + info.numFields ∧
    (∀ x j, fs[j]? = some x → (∀ i : Nat, lead[i]? ≠ some (.bvar x)) →
      info.nparams ≤ ms.length + j) ∧
    ((info.resultLevel.inst (lsC.map (·.inst ls))).IsNeverZero ∨
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs env U Δ v vS (binderTy doms ls x) τ →
          ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])

/-- The part of `MajorFam` used by the left-to-right direction of a pattern rule: the family `I`
of the major is not projection-registered and `ctor` is not a projection constructor, or `I` is
projection-registered with the constructor `ctor`. -/
def MajorFamEntry (env : VEnv) (I ctor : Name) : Prop :=
  ((∀ info, ¬ env.projections I info) ∧ ¬ IsProjCtor env ctor) ∨
  ∃ info, env.projections I info ∧ info.ctorName = ctor

theorem MajorFam.weak {Γ : List VExpr} {I ctor : Name} {doms lead ms : List VExpr}
    {fs : List Nat} {ls lsC : List VLevel}
    (h : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC) : MajorFamEntry env I ctor := by
  rcases h with h | ⟨info, h1, -, h2, -⟩
  · exact .inl h
  · exact .inr ⟨info, h1, h2⟩

/-- Finitely many witnesses, one for each element of a list. -/
theorem exists_list_witness {α : Type} {Q : Ob → Prop} {P : α → Ob → Prop} :
    ∀ (L : List α), (∀ a ∈ L, ∃ o, Q o ∧ P a o) →
      ∃ K : List Ob, (∀ o ∈ K, Q o) ∧ ∀ a ∈ L, ∃ o ∈ K, P a o
  | [], _ => ⟨[], nofun, nofun⟩
  | a :: L, h => by
    obtain ⟨o, hQ, hP⟩ := h a (.head _)
    obtain ⟨K, hK1, hK2⟩ := exists_list_witness L fun b hb => h b (.tail _ hb)
    refine ⟨o :: K, fun o' ho' => ?_, fun b hb => ?_⟩
    · cases ho' with
      | head => exact hQ
      | tail _ h => exact hK1 o' h
    · cases hb with
      | head => exact ⟨o, .head _, hP⟩
      | tail _ hb => let ⟨o', h1, h2⟩ := hK2 b hb; exact ⟨o', .tail _ h1, h2⟩

/-- The head-type premise of a rule clause names the family of the head type's major domain. -/
theorem EtaHead.fam {T : VExpr} (h : EtaHead env I' ctor' T k)
    (eH : T = .wrapForalls dsH RH) (hlenH : dsH.length = k + 1)
    (hkH : dsH[k]? = some (.mkApps (.const I lsI) iargs)) :
    I' = I ∧ ∃ info : VProjectionInfo, env.projections I info ∧ info.ctorName = ctor' := by
  obtain ⟨info, dsH', RH', lsI', iargs', hp, hcn, eH', hlen', hk'⟩ := h
  obtain ⟨rfl, -⟩ := VExpr.wrapForalls_inj_of_length (by rw [hlenH, hlen']) (eH.symm.trans eH')
  rw [hkH] at hk'
  obtain ⟨rfl, -, -⟩ := VExpr.mkApps_const_inj (Option.some.inj hk')
  exact ⟨rfl, info, hp, hcn⟩

/-- Field observations of a spine of a rigid constructor come from the `projCtor` clause: the
constructor is the constructor of the family, and the field observation is covered by an
observation of the field argument. -/
theorem projctor_spine_inv {σ : VExpr.Subst} {S : ObSets} (hrig : env.Rigid c)
    (h : Obs' σ S (.mkApps (.const c lsc) margs) (.fieldOb I i L k)) :
    ∃ info : VProjectionInfo, env.projections I info ∧ info.ctorName = c ∧
      ∃ a, margs[info.nparams + i]? = some a ∧ ∃ k', Obs' σ S a k' ∧ k' ≼ k := by
  obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps_le h
  rcases Obs.const_iff.1 hw with ⟨_, _, keys', r', e, _, _, _, _, hr'⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r', e, _, _, _, _, _, hr', _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨fam, info, _, _, keys', r', e, hp, hcn, _, _, _, _, hend, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · obtain ⟨-, rfl⟩ := wrap_inj e trivial hr'.notApp
    rcases hr' with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf _)
  · have hrn : r'.NotApp := by
      rcases hr' with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨-, rfl⟩ := wrap_inj e trivial hrn
    rcases hr' with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf lsP)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  · obtain ⟨j, L', k₀, rfl, -, -, -, kj, hkj, hk₀⟩ := hend
    obtain ⟨rfl, e2⟩ := wrap_inj e trivial trivial
    cases e2
    have hil : info.nparams + i < keys.length := (List.getElem?_eq_some_iff.1 hkj).1
    obtain ⟨hil', _, hcov⟩ := List.forall₂_getElem_exists hk _ hil
    have hkj' : keys[info.nparams + i] = kj := (List.getElem?_eq_some_iff.1 hkj).2
    rw [hkj'] at hcov
    obtain ⟨k', hk', l⟩ := hcov k hk₀
    exact ⟨info, hp, hcn, _, List.getElem?_eq_getElem hil', k', hk', l⟩
  · obtain ⟨-, h⟩ := wrap_inj e trivial trivial; cases h
  · obtain ⟨-, h⟩ := wrap_inj e trivial trivial; cases h

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The eta anchor** (left to right): a member `z` of the class of the projections onto field
`i` of the major key's class `cm`, a typed class at `B`, is definitionally equal at `B` to the
field `a` of a constructor spine of the family in `cm`, when `a` has type `B` (by `projIota`). -/
theorem eta_anchor_defeq {I : Name} {info : VProjectionInfo} (hp : env.projections I info)
    {lsc : List VLevel} {margs : List VExpr} {B : VExpr} {cm : VExpr → Prop} {i : Nat}
    {z a : VExpr}
    (hTE : TypedElCls env U Δ (TyCls env U Δ B) (projCls env U Δ I i cm (TyCls env U Δ B)))
    (hz : projCls env U Δ I i cm (TyCls env U Δ B) z)
    (hM : cm (.mkApps (.const info.ctorName lsc) margs))
    (ha : margs[info.nparams + i]? = some a) (haT : env.HasType U Δ a B) :
    env.IsDefEq U Δ z a B := by
  have hpM : projCls env U Δ I i cm (TyCls env U Δ B)
      (.proj I i (.mkApps (.const info.ctorName lsc) margs)) := ⟨_, hM, ElCls.self⟩
  have h1 := hTE.defeq henv hΔ hz hpM
  have h2 := hTE.hasType henv hΔ hpM
  exact h1.trans (.projIota hp h2 ha haT)

end

/-! ## Classes along a constructor spine

The eta binding of the right-to-left direction needs the class of a field of the major to be
the class of the field type of the projection, and the class of the major key to be the class
of the constructor's result. Both come from the semantic typing of the major spine: the domain
and codomain classes of the spine's Pi types are observations (`piDom`, `piCod`) of the head
type, which the constructor's sound telescope reads at the arguments. -/

theorem HTS.app_const_inv {c : Name} {ls : List VLevel} {pre : List VExpr} {a : VExpr}
    (H : HTS env U Δ Γ e T) (he : e = .mkApps (.const c ls) (pre ++ [a])) :
    ∃ A B, HTS env U Δ Γ (.mkApps (.const c ls) pre) (.forallE A B) ∧ HTS env U Δ Γ a A ∧
      SD env U Δ Γ a a A ∧ (B.inst a = T ∨ env.TypeChain U Γ (B.inst a) T) := by
  rw [VExpr.mkApps_snoc] at he
  induction H with
  | app _ _ hf _ ha hsa => cases he; exact ⟨_, _, hf, ha, hsa, .inl rfl⟩
  | conv _ hAB ih =>
    obtain ⟨A, B, h1, h2, h3, h⟩ := ih he
    refine ⟨A, B, h1, h2, h3, .inr ?_⟩
    rcases h with rfl | h
    · exact .single hAB.1.defeq
    · exact h.tail hAB.1.defeq
  | other h =>
    exact absurd (he.trans (VExpr.mkApps_snoc _ _ _).symm) (h _ _ _)
  | bvar | const | lam | forallE | proj => cases he

/-- Every argument of a semantically typed constant spine is typed at the domain of the Pi type
of its prefix. -/
theorem HTS.spine_at {c : Name} {ls : List VLevel} : ∀ (n : Nat) {args : List VExpr} {T : VExpr},
    args.length = n → HTS env U Δ Γ (.mkApps (.const c ls) args) T →
    ∀ i (hi : i < args.length), ∃ A B,
      HTS env U Δ Γ (.mkApps (.const c ls) (args.take i)) (.forallE A B) ∧
      HTS env U Δ Γ args[i] A ∧ SD env U Δ Γ args[i] args[i] A
  | 0, args, _, hn, _, i, hi => by omega
  | n + 1, args, T, hn, H, i, hi => by
    rcases List.eq_nil_or_concat args with rfl | ⟨pre, a, h⟩
    · simp at hn
    rw [List.concat_eq_append] at h
    subst h
    obtain ⟨A, B, hf, ha, hsa, -⟩ := H.app_const_inv rfl
    simp only [List.length_append, List.length_singleton] at hi hn
    by_cases hip : i < pre.length
    · obtain ⟨A', B', h1, h2, h3⟩ := HTS.spine_at n (by omega) hf i hip
      refine ⟨A', B', ?_, ?_, ?_⟩
      · rwa [List.take_append_of_le_length (by omega)]
      · rwa [List.getElem_append_left hip]
      · rwa [List.getElem_append_left hip]
    · obtain rfl : i = pre.length := by omega
      refine ⟨A, B, ?_, ?_, ?_⟩
      · rw [List.take_left' rfl]; exact hf
      · simpa using ha
      · simpa using hsa

/-- The codomain of a sound Pi telescope after its first `i+1` binders is sound in their
context. -/
theorem PiSD.body_at : ∀ {Γ D : List VExpr} {R : VExpr}, PiSD env U Δ Γ D R →
    ∀ i (_hi : i < D.length), ∃ v, SD env U Δ ((D.take (i+1)).reverse ++ Γ)
      (.wrapForalls (D.drop (i+1)) R) (.wrapForalls (D.drop (i+1)) R) (.sort v)
  | _, [], _, _, i, hi => by simp at hi
  | _, A :: ds, R, .cons _ hB _, 0, _ => ⟨_, by simpa using hB⟩
  | Γ, A :: ds, R, .cons _ _ hP, i + 1, hi => by
    obtain ⟨v, h⟩ := PiSD.body_at hP i (by simp at hi; omega)
    exact ⟨v, by simpa [List.reverse_cons, List.append_assoc] using h⟩

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Splitting a head-type chain observation at the prefix of a spine, transported to a sound
telescope covering the head type (the `split` step of `spine_tele`). -/
theorem spine_split {ls : List VLevel} {ci : VConstant} {Dw : List VExpr}
    {Rw : VExpr}
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw) {pre : List VExpr} (hiD : pre.length < Dw.length)
    {σ : VExpr.Subst} {S : ObSets} {keys : List Key} {z : Ob}
    (hk : ChainArgs env U Δ σ S keys pre)
    (hz : Obs' .id .empty (ci.type.instL ls) (piCodChain keys z)) :
    ∃ ys z', ys.length = pre.length ∧ z' ≼ z ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst ys) (VExpr.argSubst (pre.map (·.subst σ)))
        (Dw.take pre.length).reverse ∧
      ∃ S', Obs' (VExpr.argSubst ys) S'
        (.forallE Dw[pre.length] (.wrapForalls (Dw.drop (pre.length + 1)) Rw)) z' := by
  obtain ⟨o', ho', l'⟩ := hTW _ hz
  obtain ⟨keys', z', rfl, hkk, hz'⟩ := Le.piCodChain_inv l'
  have hkl : keys'.length = pre.length := by
    rw [List.Forall₂.length_eq hkk, List.Forall₂.length_eq hk]
  obtain ⟨keys'', ys, hT, hk'', hky, hz''⟩ := tele_split (by omega) ho'
  have hyl : ys.length = pre.length := by rw [← List.Forall₂.length_eq hky, hkl]
  rw [hkl] at hT hz''
  rw [List.drop_eq_getElem_cons hiD] at hz''
  have hb : List.Forall₂ (fun (k : Key) b => k.2.1 b) keys'' (pre.map (·.subst σ)) :=
    forall₂_cls hk'' hkk hk
  obtain ⟨hdTake, -⟩ := DomsSD.take_getElem hpi.doms _ hiD
  have hdTake' : DomsSD env U Δ [] (Dw.take pre.length) := hdTake
  have WS := TeleKeys.substEq (v := .id) henv hΔ hT hdTake' .nil hb
  exact ⟨ys, z', hyl, hz', by simpa [VExpr.argSubst] using WS, _, hz''⟩

theorem spine_headTy {c : Name} {ls : List VLevel} {ci : VConstant} {args : List VExpr}
    {T : VExpr} {σ : VExpr.Subst} {S : ObSets}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) T) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hci : env.constants c = some ci) :
    ∀ y, Obs' σ S T y → ∃ keys y', ChainArgs env U Δ σ S keys args ∧
      Obs' .id .empty (ci.type.instL ls) (piCodChain keys y') ∧ y' ≼ y := by
  obtain ⟨Th, As, hTh, -, -, -, hlast⟩ := HTS.spineRev henv hΔ H rfl ⟨c, ls, rfl⟩ W tv
  have hThe : Th = ci.type.instL ls := by
    obtain ⟨c', ls', ci', he, hci', _, rfl⟩ := hTh
    cases he; cases hci.symm.trans hci'; rfl
  subst hThe
  exact hlast

/-- **The domain class at an argument of a constant spine** is the class of the telescope's
domain at the earlier arguments. -/
theorem spine_dom_cls {c : Name} {ls : List VLevel} {ci : VConstant} {Dw : List VExpr}
    {Rw : VExpr} (hci : env.constants c = some ci)
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw) {pre : List VExpr} (hiD : pre.length < Dw.length)
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S)
    {A B : VExpr} (H : HTS env U Δ Γ (.mkApps (.const c ls) pre) (.forallE A B)) :
    TyCls env U Δ (A.subst σ) =
      TyCls env U Δ (Dw[pre.length].subst (VExpr.argSubst (pre.map (·.subst σ)))) := by
  obtain ⟨keys, y', hk, hobs, ly⟩ := spine_headTy henv hΔ H W tv hci _
    (Obs.piDom : Obs' σ S (.forallE A B) _)
  cases ly.piDom_inv
  obtain ⟨ys, z', -, hz', WS, S', hzo⟩ := spine_split henv hΔ hTW hpi hiD hk hobs
  cases hz'.piDom_inv
  have hD := Obs.piDom_mem hzo
  obtain ⟨-, u, hDi⟩ := DomsSD.take_getElem hpi.doms _ hiD
  have hDiTy : env.HasType U (Dw.take pre.length).reverse Dw[pre.length] (.sort u) := by
    simpa using hDi.1.defeq.hasType.1
  exact hD.trans (TyCls.eq_of_defeq (hDiTy.substDF henv WS.wf hΔ WS))

/-- **The result class of a full constant spine** is the class of the telescope's codomain at
the arguments. -/
theorem spine_res_cls {c : Name} {ls : List VLevel} {ci : VConstant} {Dw : List VExpr}
    {Rw : VExpr} (hci : env.constants c = some ci)
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw) {args : List VExpr} (hn : args.length = Dw.length)
    (hne : args ≠ [])
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S)
    {T : VExpr} (H : HTS env U Δ Γ (.mkApps (.const c ls) args) T) :
    TyCls env U Δ (T.subst σ) =
      TyCls env U Δ (Rw.subst (VExpr.argSubst (args.map (·.subst σ)))) := by
  rcases List.eq_nil_or_concat args with rfl | ⟨pre, a, rfl⟩
  · exact absurd rfl hne
  rw [List.concat_eq_append] at H hn ⊢
  obtain ⟨A, B, hf, ha, hsa, hch⟩ := H.app_const_inv rfl
  simp only [List.length_append, List.length_singleton] at hn
  have hiD : pre.length < Dw.length := by omega
  have haσ : env.HasType U Δ (a.subst σ) (A.subst σ) :=
    hsa.1.defeq.hasType.1.substDF henv W.wf hΔ W
  obtain ⟨keys, y', hk, hobs, ly⟩ := spine_headTy henv hΔ hf W tv hci _
    (Obs.piCod (TypedElCls.of_hasType haσ) ElCls.self : Obs' σ S (.forallE A B) _)
  cases ly.piCod_inv
  obtain ⟨ys, z', -, hz', WS, S', hzo⟩ := spine_split henv hΔ hTW hpi hiD hk hobs
  cases hz'.piCod_inv
  obtain ⟨hcT, x, hx, hC⟩ := Obs.piCod_mem hzo
  have hxa := hcT.defeq henv hΔ hx ElCls.self
  obtain ⟨-, u, hDi⟩ := DomsSD.take_getElem hpi.doms _ hiD
  have hDiTy : env.HasType U (Dw.take pre.length).reverse Dw[pre.length] (.sort u) := by
    simpa using hDi.1.defeq.hasType.1
  have W2 : Ctx.SubstEq env U Δ ((VExpr.argSubst ys).cons x)
      ((VExpr.argSubst (pre.map (·.subst σ))).cons (a.subst σ))
      (Dw[pre.length] :: (Dw.take pre.length).reverse) :=
    .cons (by simpa using WS) hDiTy (by simpa using hxa)
  obtain ⟨v, hR⟩ := PiSD.body_at hpi _ hiD
  have hctx : (Dw.take (pre.length + 1)).reverse ++ [] =
      Dw[pre.length] :: (Dw.take pre.length).reverse := by
    rw [List.take_succ_eq_append_getElem hiD]; simp
  rw [hctx, show pre.length + 1 = Dw.length by omega, List.drop_length] at hR
  have hRty := hR.1.defeq.hasType.1
  have e1 := TyCls.eq_of_defeq (hRty.substDF henv W2.wf hΔ W2)
  rw [show pre.length + 1 = Dw.length by omega, List.drop_length] at hC
  simp only [VExpr.wrapForalls, List.foldr_nil] at e1 hC
  have e0 : TyCls env U Δ (T.subst σ) = TyCls env U Δ ((B.inst a).subst σ) := by
    rcases hch with rfl | hch
    · rfl
    · exact (TypeChain.tyCls_subst_of_ctx henv hΔ W hch).symm
  rw [e0, VExpr.inst_subst_cons, hC, e1, List.map_append, List.map_singleton,
    VExpr.argSubst_append_one]

end

/-- Arguments whose prefixes instantiate the prefixes of a telescope are typed along it. -/
theorem ArgsTyped.of_prefixes {D : List VExpr} {R0 : VExpr} {as : List VExpr}
    (hW : ∀ i ≤ as.length, Ctx.SubstEq env U Δ (VExpr.argSubst (as.take i))
      (VExpr.argSubst (as.take i)) (D.take i).reverse)
    (hn : as.length ≤ D.length) :
    ArgsTyped env U Δ (.wrapForalls D R0) as
      ((VExpr.wrapForalls (D.drop as.length) R0).subst (VExpr.argSubst as)) := by
  have aux : ∀ m k, k + m = as.length →
      ArgsTyped env U Δ ((VExpr.wrapForalls (D.drop k) R0).subst (VExpr.argSubst (as.take k)))
        (as.drop k) ((VExpr.wrapForalls (D.drop as.length) R0).subst (VExpr.argSubst as)) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [show k = as.length by omega, List.drop_length, List.take_of_length_le (Nat.le_refl _)]
      exact .nil
    | succ m ih =>
      intro k hk
      have hka : k < as.length := by omega
      have hkD : k < D.length := by omega
      rw [List.drop_eq_getElem_cons hka, List.drop_eq_getElem_cons hkD,
        VExpr.subst_wrapForalls_cons]
      have W := hW (k + 1) (by omega)
      rw [List.take_succ_eq_append_getElem hka, VExpr.argSubst_append_one,
        List.take_succ_eq_append_getElem hkD, List.reverse_append] at W
      cases W with
      | cons _ _ h =>
        refine .cons (by simp only [VExpr.Subst.cons_head, VExpr.Subst.cons_tail] at h; exact h) ?_
        rw [VExpr.inst_lift_cons, ← VExpr.argSubst_append_one,
          ← List.take_succ_eq_append_getElem hka]
        exact ih (k + 1) (by omega)
  have := aux as.length 0 (by omega)
  simpa [VExpr.argSubst] using this

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The field types of the projections of a constructor spine are the telescope's field domains
at the parameters and the earlier fields. -/
theorem proj_fieldTy_conv {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hcl : info.ctorType.Closed) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = info.uvars) (hnz : (info.resultLevel.inst ls).IsNeverZero)
    {doms idx : List VExpr}
    (hshape : info.ctorType = VExpr.wrapForalls doms
      (VExpr.mkApps (.const S (VLevel.params info.uvars))
        ((List.range info.nparams).reverse.map
            (fun i => VExpr.bvar (doms.length - info.nparams + i)) ++ idx)))
    (hidx : idx.length = info.nindices) (hwf : env.IsType info.uvars [] info.ctorType)
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    {ps fs : List VExpr} {R : VExpr}
    (hargs : ArgsTyped env U Δ (info.ctorType.instL ls) (ps ++ fs) R)
    (hpl : ps.length = info.nparams) (hfl : fs.length = info.numFields)
    (W0 : Ctx.SubstEq env U Δ (VExpr.argSubst ps) (VExpr.argSubst ps)
      ((doms.map (·.instL ls)).take info.nparams).reverse)
    {i : Nat} (hi : i < fs.length) {F : VExpr}
    (hF : info.fieldType S ls ps i (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs)) = some F) :
    ∃ d u, (doms.map (·.instL ls))[info.nparams + i]? = some d ∧
      env.IsDefEq U Δ F (d.subst (VExpr.argSubst (ps ++ fs.take i))) (.sort u) := by
  have T := ProjTele.of (S := S) henv hshape hwf hls
  have hnf := T.numFields
  obtain ⟨-, hall⟩ := proj_spine henv hΔ hp hcl hls hlen hnz hshape hidx hwf hctor hargs hpl hfl
  generalize hM : VExpr.mkApps (.const info.ctorName ls) (ps ++ fs) = M at hall hF
  generalize hD : doms.map (·.instL ls) = D at T W0 hnf ⊢
  have key : ∀ j, j ≤ fs.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst (ps ++ projsOf S M j))
        (VExpr.argSubst (ps ++ fs.take j)) (D.take (info.nparams + j)).reverse := by
    intro j
    induction j with
    | zero => intro _; simpa [projsOf] using W0
    | succ j ih =>
      intro hj
      have W := ih (by omega)
      have hk : info.nparams + j < D.length := by omega
      obtain ⟨u, hu⟩ := T.doms _ hk
      obtain ⟨Fj, hFj, -, hdef⟩ := hall j (by omega)
      rw [T.fieldType hlen hpl M hk, Option.some.injEq] at hFj
      subst hFj
      rw [projsOf_succ, ← List.append_assoc, List.take_succ_eq_append_getElem (by omega : j < fs.length),
        ← List.append_assoc, show info.nparams + (j + 1) = (info.nparams + j) + 1 by omega,
        List.take_succ_eq_append_getElem hk, List.reverse_append, List.reverse_singleton,
        List.singleton_append, VExpr.argSubst_append_one, VExpr.argSubst_append_one]
      exact .cons (by simpa using W) hu (by simpa using hdef)
  have hk : info.nparams + i < D.length := by omega
  obtain ⟨u, hu⟩ := T.doms _ hk
  rw [T.fieldType hlen hpl M hk, Option.some.injEq] at hF
  subst hF
  exact ⟨_, u, List.getElem?_eq_getElem hk, hu.substDF henv (T.ctx _ (by omega)) hΔ (key i (by omega))⟩

/-- The levels of a semantically typed constructor spine of a projection entry. -/
theorem ctor_spine_levels {I : Name} {info : VProjectionInfo} (hp : env.projections I info)
    {Γ' : List VExpr} {v : VExpr.Subst} (Wv : Ctx.SubstEq env U Δ v v Γ')
    {lsc : List VLevel} {margs : List VExpr} {Tm : VExpr}
    (hsd : SD env U Δ Γ' (.mkApps (.const info.ctorName lsc) margs)
      (.mkApps (.const info.ctorName lsc) margs) Tm) :
    (∀ l ∈ lsc, l.WF U) ∧ lsc.length = info.uvars := by
  have hMσ := hsd.1.defeq.hasType.1.substDF henv Wv.wf hΔ Wv
  rw [VExpr.subst_mkApps] at hMσ
  obtain ⟨_, hc⟩ := HasType.mkApps_fn henv hΔ hMσ
  obtain ⟨ci', hci', hls, hlsl⟩ := HasType.const_inv henv hΔ hc
  rw [henv.ordered.projectionConstructor hp] at hci'
  cases hci'
  exact ⟨hls, hlsl⟩

/-- **The eta binding class** (right to left): for a semantically typed full spine of the
constructor of a never-zero projection-registered family at a typed valuation, the class of the
projections onto a variable field of the class of the spine at its type is the class of the
variable at its type. -/
theorem eta_field_cls {I : Name} {info : VProjectionInfo} (hp : env.projections I info)
    (hPV : ProjValid env I info)
    {Γ' : List VExpr} {v : VExpr.Subst} {vS : ObSets} (Wv : Ctx.SubstEq env U Δ v v Γ')
    (tvv : TV env U Δ Γ' v vS) {lsc : List VLevel} {margs : List VExpr} {Tm : VExpr}
    (H : HTS env U Δ Γ' (.mkApps (.const info.ctorName lsc) margs) Tm)
    (hsd : SD env U Δ Γ' (.mkApps (.const info.ctorName lsc) margs)
      (.mkApps (.const info.ctorName lsc) margs) Tm)
    (hlen : margs.length = info.nparams + info.numFields)
    (hnz : (info.resultLevel.inst lsc).IsNeverZero)
    {q x : Nat} {A : VExpr} (hq : margs[q]? = some (.bvar x)) (hnq : info.nparams ≤ q)
    (hL : Lookup Γ' x A) :
    projCls env U Δ I (q - info.nparams)
        (ElCls env U Δ (TyCls env U Δ (Tm.subst v))
          ((VExpr.mkApps (.const info.ctorName lsc) margs).subst v))
        (TyCls env U Δ (A.subst v)) = ElCls env U Δ (TyCls env U Δ (A.subst v)) (v x) ∧
    env.HasType U Δ (v x) (A.subst v) := by
  have hvx : env.HasType U Δ (v x) (A.subst v) := (Wv.lookup hL).hasType.1
  refine ⟨?_, hvx⟩
  obtain ⟨hst, envTypes, hOrig, hsnd⟩ := hPV
  have hctor := henv.ordered.projectionConstructor hp
  obtain ⟨doms, idx, hshape, hnpD, hidx⟩ := hOrig.origin.ctorType_shape
  obtain ⟨base, dsb, decl, type, ctor, hbase, htypes, hle, hord, -, -, -, hu, -, -, -, -, hct,
    -, hwfE, -⟩ := hOrig
  have hwf : env.IsType info.uvars [] info.ctorType := by
    rw [hu, hct]; exact hwfE.mono hle
  -- the levels
  have hql : q < margs.length := (List.getElem?_eq_some_iff.1 hq).1
  have hMσ : env.HasType U Δ (VExpr.mkApps (.const info.ctorName lsc) (margs.map (·.subst v)))
      (Tm.subst v) := by
    have := hsd.1.defeq.hasType.1.substDF henv Wv.wf hΔ Wv
    rw [VExpr.subst_mkApps] at this; exact this
  obtain ⟨_, hc⟩ := HasType.mkApps_fn henv hΔ hMσ
  obtain ⟨ci', hci', hls, hlsl⟩ := HasType.const_inv henv hΔ hc
  rw [hctor] at hci'
  cases hci'
  -- the telescope
  generalize hRdef : VExpr.mkApps (.const I (VLevel.params info.uvars))
    ((List.range info.nparams).reverse.map
      (fun i => VExpr.bvar (doms.length - info.nparams + i)) ++ idx) = R at hshape
  have eT : info.ctorType.instL lsc =
      VExpr.wrapForalls (doms.map (·.instL lsc)) (R.instL lsc) := by
    rw [hshape, VExpr.instL_wrapForalls]
  have hTW : Ob.Sub (Obs' .id .empty ((⟨info.uvars, info.ctorType⟩ : VConstant).type.instL lsc))
      (Obs' .id .empty (.wrapForalls (doms.map (·.instL lsc)) (R.instL lsc))) :=
    fun o h => ⟨o, by rw [← eT]; exact h, .refl⟩
  have hpi : PiSD env U Δ [] (doms.map (·.instL lsc)) (R.instL lsc) := by
    obtain ⟨w, h⟩ := IsType.instL hls hwfE
    rw [← hct, hshape, VExpr.instL_wrapForalls] at h
    exact piSD_of hord.orderedStrong hle (SoundTypedIn.soundIn (hsnd U Δ hΔ)) trivial h
  have hnf := (ProjTele.of (S := I) henv (hRdef ▸ hshape) hwf hls).numFields
  simp only [List.length_map] at hnf
  have hDl : (doms.map (·.instL lsc)).length = margs.length := by simp; omega
  have hpre := spine_tele_prefix henv hΔ H Wv tvv hctor hTW hpi (by omega)
  -- the substituted arguments, typed along the constructor telescope
  generalize hmσ : margs.map (·.subst v) = mσ at hMσ
  have hmσl : mσ.length = margs.length := by rw [← hmσ]; simp
  have hpre' : ∀ i ≤ mσ.length, Ctx.SubstEq env U Δ (VExpr.argSubst (mσ.take i))
      (VExpr.argSubst (mσ.take i)) ((doms.map (·.instL lsc)).take i).reverse := by
    intro i hi
    have := (hpre i (by omega)).1
    rwa [List.map_take, hmσ] at this
  have hargs := ArgsTyped.of_prefixes (R0 := R.instL lsc) hpre' (by omega)
  rw [← eT, ← List.take_append_drop info.nparams mσ] at hargs
  have hpl : (mσ.take info.nparams).length = info.nparams := by simp; omega
  have hfl : (mσ.drop info.nparams).length = info.numFields := by simp; omega
  have hi : q - info.nparams < (mσ.drop info.nparams).length := by rw [hfl]; omega
  have hfx : (mσ.drop info.nparams)[q - info.nparams] = v x := by
    rw [List.getElem_drop]
    have : mσ[q]'(by omega) = v x := by
      subst hmσ; rw [List.getElem_map, (List.getElem?_eq_some_iff.1 hq).2]; rfl
    rw [← this]; congr 1; omega
  obtain ⟨hmk, F, hF, -, heq⟩ := ctor_projCls henv hΔ hp hst.ctorClosed hls hlsl hnz
    (hRdef ▸ hshape) hidx hwf hctor hargs hpl hfl hi
  -- the class of the major key is the class of the constructor's result
  have e5 : TyCls env U Δ (Tm.subst v) = TyCls env U Δ (VExpr.mkApps (.const I lsc)
      (mσ.take info.nparams ++ idx.map fun e =>
        (e.instL lsc).subst (VExpr.argSubst (mσ.take info.nparams ++ mσ.drop info.nparams)))) := by
    have := spine_res_cls henv hΔ hctor hTW hpi (by omega)
      (fun h => by simp [h] at hql) Wv tvv H
    rw [hmσ, ← List.take_append_drop info.nparams mσ, ← hRdef] at this
    rw [this, spine_result hlsl hpl (by simp; omega)]
  -- the class of the field is the class of the projection's field type
  obtain ⟨Aq, Bq, hfq, haq, -⟩ := HTS.spine_at _ rfl H q hql
  have hbq : margs[q] = .bvar x := (List.getElem?_eq_some_iff.1 hq).2
  rw [hbq] at haq
  obtain ⟨A₀, hL₀, hch⟩ := haq.bvar_chain rfl
  cases hL.uniq hL₀
  have e1 : TyCls env U Δ (A.subst v) = TyCls env U Δ (Aq.subst v) := by
    rcases hch with rfl | hch
    · rfl
    · exact TypeChain.tyCls_subst_of_ctx henv hΔ Wv hch
  have e2 := spine_dom_cls henv hΔ hctor hTW hpi (by simp; omega) Wv tvv hfq
  have W0 := hpre' info.nparams (by omega)
  obtain ⟨d, u, hd, hconv⟩ := proj_fieldTy_conv henv hΔ hp hst.ctorClosed hls hlsl hnz
    (hRdef ▸ hshape) hidx hwf hctor hargs hpl hfl W0 hi hF
  have e3 := TyCls.eq_of_defeq hconv
  have hd' : (doms.map (·.instL lsc))[(margs.take q).length]'(by simp; omega) = d := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, ← hd]
    congr 1; simp; omega
  have hmq : (margs.take q).map (·.subst v) =
      mσ.take info.nparams ++ (mσ.drop info.nparams).take (q - info.nparams) := by
    rw [List.map_take, hmσ, ← List.take_add, Nat.add_sub_cancel' hnq]
  have eA : TyCls env U Δ (A.subst v) = TyCls env U Δ F := by
    rw [e1, e2, hd', hmq, e3]
  rw [List.take_append_drop] at heq e5
  rw [e5, eA, VExpr.subst_mkApps, hmσ]
  simp only [VExpr.subst]
  rw [heq, hfx]

end

end Model
end VEnv
end Lean4Lean
