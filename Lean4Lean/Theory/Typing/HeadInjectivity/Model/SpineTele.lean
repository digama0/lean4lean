import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineRev
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleCompact
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleLemmas

/-! # The valuation of a constant spine over a syntactic telescope

`Model.spine_tele`: for a semantically typed constant spine `mkApps (.const c ls) args` at a
typed valuation `(σ, S)`, and a closed sound Pi telescope `wrapForalls Dw Rw` whose
observations cover those of the constant's type, the substituted arguments instantiate the
first `args.length` binders of `Dw` (a `Ctx.SubstEq`), and the observation sets of the
arguments (`argSets`) form a typed valuation of that prefix.

The proof follows the binders. `HTS.spineRev` gives, for the `i`-th argument, its domain type
`A` in the derivation and chain observations of the head type that end in the domain class of
`A` and in each observation of `A`. Transported to the telescope (`hTW`) and split at the
`i`-th binder (`tele_split`), they identify the domain classes of `A` and of `Dw[i]`, and map
the observations of `A` to observations of `Dw[i]` at the split's anchor, which is related to
the arguments' substitution (`TeleKeys.substEq`) so that soundness of `Dw[i]` moves them to it.
-/

namespace Lean4Lean
namespace VEnv
namespace Model
open VExpr

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The observation sets of a list of arguments, the last argument at index `0`. -/
def argSets (env : VEnv) (U : Nat) (Δ : List VExpr) (σ : VExpr.Subst) (S : ObSets)
    (args : List VExpr) : ObSets :=
  fun m => if h : m < args.length then Obs env U Δ σ S args[args.length - 1 - m] else fun _ => False

theorem argSets_snoc (σ : VExpr.Subst) (S : ObSets) (args : List VExpr) (a : VExpr) :
    argSets env U Δ σ S (args ++ [a]) = (argSets env U Δ σ S args).cons (Obs' σ S a) := by
  funext m
  cases m with
  | zero => simp [argSets, ObSets.cons]
  | succ m =>
    simp only [argSets, ObSets.cons, List.length_append, List.length_singleton]
    by_cases hm : m < args.length
    · rw [dif_pos (by omega), dif_pos hm, List.getElem_append_left (by omega)]
      congr 2; omega
    · rw [dif_neg (by omega), dif_neg hm]

/-- The observation sets of a list of keys, the last key at index `0`. -/
def extS (S : ObSets) (keys : List Key) : ObSets :=
  keys.foldl (fun S k => S.cons (listSet k.2.2)) S

theorem extS_snoc (S : ObSets) (keys : List Key) (k : Key) :
    extS S (keys ++ [k]) = (extS S keys).cons (listSet k.2.2) := by
  simp [extS, List.foldl_append]

theorem _root_.Lean4Lean.VExpr.argSubst_ge (as : List VExpr) {m : Nat} (h : as.length ≤ m) :
    VExpr.argSubst as m = VExpr.bvar (m - as.length) := by
  rw [VExpr.argSubst, VExpr.foldl_cons_apply, dif_neg (by omega)]; rfl

/-- Subsumption below a chain of codomain observations. -/
theorem Le.piCodChain_inv : ∀ {keys : List Key} {x o : Ob}, o ≼ piCodChain keys x →
    ∃ keys' x', o = piCodChain keys' x' ∧
      List.Forall₂ (fun (k' k : Key) => k'.1 = k.1 ∧ k'.2.1 = k.2.1 ∧ Covers k.2.2 k'.2.2)
        keys' keys ∧ x' ≼ x
  | [], x, o, h => ⟨[], o, rfl, .nil, h⟩
  | k :: keys, x, o, h => by
    rw [piCodChain_cons] at h
    obtain ⟨K₀, y, rfl, hK, hy⟩ := h.piCodOb_inv
    obtain ⟨keys', x', rfl, hk, hx⟩ := Le.piCodChain_inv hy
    exact ⟨(k.1, k.2.1, K₀) :: keys', x', rfl, .cons ⟨rfl, rfl, hK⟩ hk, hx⟩

/-- Splitting a codomain chain observation of a Pi telescope at its first binders. -/
theorem tele_split : ∀ {ds : List VExpr} {keys : List Key} {σ : VExpr.Subst} {S : ObSets}
    {R : VExpr} {z : Ob}, keys.length ≤ ds.length →
    Obs' σ S (.wrapForalls ds R) (piCodChain keys z) →
    ∃ keys' ys, TeleKeys env U Δ σ S (ds.take keys.length) keys' (ys.foldl VExpr.Subst.cons σ)
        (extS S keys) ∧
      List.Forall₂ (fun (k' k : Key) => k'.2 = k.2) keys' keys ∧
      List.Forall₂ (fun (k : Key) y => k.2.1 y) keys ys ∧
      Obs' (ys.foldl VExpr.Subst.cons σ) (extS S keys) (.wrapForalls (ds.drop keys.length) R) z
  | _, [], σ, S, R, z, _, h => ⟨[], [], .nil, .nil, .nil, by simpa [extS] using h⟩
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | A :: ds, k :: keys, σ, S, R, z, hl, h => by
    rw [piCodChain_cons] at h
    obtain ⟨hc, ⟨τs, h2, h3⟩, y, hy, h5⟩ := Obs.piCodOb_mem h
    have hb := Obs.piCodOb_backed h
    obtain ⟨keys', ys, hT, hk', hky, hz⟩ := tele_split (ds := ds) (keys := keys)
      (by simp at hl; omega) h5
    refine ⟨(TyCls env U Δ (A.subst σ), k.2) :: keys', y :: ys, ?_, .cons rfl hk',
      .cons hy hky, by simpa [extS] using hz⟩
    simp only [List.length_cons, List.take_succ_cons, List.foldl_cons]
    exact .cons hc hy (fun o ho => ⟨τs, h2, h3 o ho⟩) hb (by simpa [extS] using hT)

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The anchor of typed keys is related to any members of the key classes. -/
theorem TeleKeys.substEq {σ σ' v : VExpr.Subst} {S S' : ObSets} {ds : List VExpr}
    {keys : List Key} (h : TeleKeys env U Δ σ S ds keys σ' S') :
    ∀ {Γ' : List VExpr} {bs : List VExpr}, DomsSD env U Δ Γ' ds →
      Ctx.SubstEq env U Δ σ v Γ' → List.Forall₂ (fun (k : Key) b => k.2.1 b) keys bs →
      Ctx.SubstEq env U Δ σ' (bs.foldl VExpr.Subst.cons v) (ds.reverse ++ Γ') := by
  induction h generalizing v with
  | nil => intro Γ' bs _ W hb; cases hb; simpa using W
  | cons hc hy hK hb' _ ih =>
    intro Γ' bs hds W hbs
    cases hds with
    | cons hA hds =>
    cases hbs with
    | cons hbk hbs =>
    have := ih (v := VExpr.Subst.cons v _) hds
      (.cons (by simpa using W) hA.1.defeq.hasType.1 (by simpa using hc.defeq henv hΔ hy hbk)) hbs
    simpa [List.reverse_cons, List.append_assoc] using this

end

theorem DomsSD.take_getElem : ∀ {Γ ds : List VExpr}, DomsSD env U Δ Γ ds →
    ∀ i (hi : i < ds.length), DomsSD env U Δ Γ (ds.take i) ∧
      ∃ u, SD env U Δ ((ds.take i).reverse ++ Γ) ds[i] ds[i] (.sort u)
  | _, [], _, i, hi => by simp at hi
  | Γ, A :: ds, .cons hA hds, 0, _ => ⟨.nil, _, by simpa using hA⟩
  | Γ, A :: ds, .cons hA hds, i + 1, hi => by
    obtain ⟨h1, u, h2⟩ := DomsSD.take_getElem hds i (by simp at hi; omega)
    exact ⟨.cons hA h1, u, by simpa [List.reverse_cons, List.append_assoc] using h2⟩

theorem DomsSD.take : ∀ {Γ ds : List VExpr}, DomsSD env U Δ Γ ds →
    ∀ i, DomsSD env U Δ Γ (ds.take i)
  | _, [], _, i => by simpa using (DomsSD.nil : DomsSD env U Δ _ [])
  | _, _ :: _, _, 0 => by simpa using (DomsSD.nil : DomsSD env U Δ _ [])
  | _, A :: ds, .cons hA hds, i + 1 => .cons hA (DomsSD.take hds i)

/-- Extension of a typed valuation by a backed set of typed observations. -/
theorem TV.cons_set (h : TV env U Δ Γ σ S) {X : Ob → Prop} (hb : Backed X)
    (hX : ∀ k, X k → TypedAt env U Δ (ElCls env U Δ (TyCls env U Δ (A.subst σ)) x) σ S A k) :
    TV env U Δ (A :: Γ) (σ.cons x) (S.cons X) := by
  refine ⟨fun i => ?_, fun i B hL o ho => ?_⟩
  · cases i with
    | zero => exact hb
    | succ i => exact h.1 i
  · cases hL with
    | zero => rw [vcls_bvar_zero]; exact (hX o ho).lift_cons
    | succ hL => rw [vcls_bvar_succ]; exact (h.2 _ _ hL o ho).lift_cons

theorem forall₂_comp_cover {σ : VExpr.Subst} {S : ObSets} :
    ∀ {keys' keys : List Key} {as : List VExpr},
    List.Forall₂ (fun (k' k : Key) => k'.1 = k.1 ∧ k'.2.1 = k.2.1 ∧ Covers k.2.2 k'.2.2)
      keys' keys → ChainArgs env U Δ σ S keys as →
    List.Forall₂ (fun (k : Key) a => ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y) keys' as
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons ⟨_, _, hc⟩ h1, .cons ⟨_, h⟩ h2 =>
    .cons (fun y hy => by
      obtain ⟨y₁, hy₁, l₁⟩ := hc y hy
      obtain ⟨y₀, hy₀, l₀⟩ := h y₁ hy₁
      exact ⟨y₀, hy₀, l₀.trans l₁⟩) (forall₂_comp_cover h1 h2)

theorem List.reverseRecOn {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l a, motive l → motive (l ++ [a])) : ∀ l, motive l := by
  intro l
  induction h : l.length generalizing l with
  | zero => rw [List.length_eq_zero_iff.mp h]; exact nil
  | succ n ih =>
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · simp at h
    · rw [List.concat_eq_append]; exact snoc L b (ih L (by simp at h; omega))

theorem forall₂_snoc_inv {α β : Type} {R : α → β → Prop} {k : α} :
    ∀ {keys : List α} {as : List β}, List.Forall₂ R (keys ++ [k]) as →
      ∃ as' a, as = as' ++ [a] ∧ List.Forall₂ R keys as' ∧ R k a
  | [], _ :: _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _ :: _, .cons h t => by
    obtain ⟨as', a, rfl, h1, h2⟩ := forall₂_snoc_inv t
    exact ⟨_ :: as', a, rfl, .cons h h1, h2⟩

/-- Observations of the key lists are covered by observations of the arguments. -/
theorem extS_cover {σ : VExpr.Subst} {S : ObSets} :
    ∀ {keys : List Key} {as : List VExpr},
    List.Forall₂ (fun (k : Key) a => ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y) keys as →
    ∀ m o, extS .empty keys m o → ∃ o', argSets env U Δ σ S as m o' ∧ o' ≼ o := by
  intro keys
  induction keys using List.reverseRecOn with
  | nil => intro as h; cases h; intro m o h; exact absurd h (by simp [extS, ObSets.empty])
  | snoc keys k ih =>
    intro as h
    obtain ⟨as', a, rfl, h', hk⟩ : ∃ as' a, as = as' ++ [a] ∧
        List.Forall₂ (fun (k : Key) a => ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y) keys as' ∧
          ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y := by
      exact forall₂_snoc_inv h
    intro m o ho
    rw [extS_snoc] at ho
    rw [argSets_snoc]
    cases m with
    | zero => exact hk o ho
    | succ m => exact ih h' m o ho

theorem forall₂_cls {σ : VExpr.Subst} {S : ObSets} :
    ∀ {keys'' keys' keys : List Key} {as : List VExpr},
    List.Forall₂ (fun (k'' k' : Key) => k''.2 = k'.2) keys'' keys' →
    List.Forall₂ (fun (k' k : Key) => k'.1 = k.1 ∧ k'.2.1 = k.2.1 ∧ Covers k.2.2 k'.2.2)
      keys' keys → ChainArgs env U Δ σ S keys as →
    List.Forall₂ (fun (k : Key) b => k.2.1 b) keys'' (as.map (·.subst σ))
  | [], [], [], [], .nil, .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons ⟨_, h2, _⟩ t2, .cons ⟨h3, _⟩ t3 =>
    .cons (by rw [h1, h2]; exact h3) (forall₂_cls t1 t2 t3)

/-- The valuation of a constant spine over a syntactic telescope, at every prefix. -/
theorem spine_tele_prefix (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
    {Γ : List VExpr} {c : Name} {ls : List VLevel} {args : List VExpr} {T : VExpr}
    {σ : VExpr.Subst} {S : ObSets} {ci : VConstant}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) T) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hci : env.constants c = some ci) {Dw : List VExpr} {Rw : VExpr}
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw) (hn : args.length ≤ Dw.length) :
    ∀ i, i ≤ args.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((args.take i).map (·.subst σ)))
        (VExpr.argSubst ((args.take i).map (·.subst σ))) (Dw.take i).reverse ∧
      TV env U Δ (Dw.take i).reverse (VExpr.argSubst ((args.take i).map (·.subst σ)))
        (argSets env U Δ σ S (args.take i)) := by
  obtain ⟨Th, As, hTh, -, hlen, hdom, -⟩ :=
    HTS.spineRev henv hΔ H rfl ⟨c, ls, rfl⟩ W tv
  have hThe : Th = ci.type.instL ls := by
    obtain ⟨c', ls', ci', he, hci', _, rfl⟩ := hTh
    cases he; cases hci.symm.trans hci'; rfl
  subst hThe
  have hdoms := hpi.doms
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp only [List.take_zero, List.reverse_nil]; exact .nil,
      fun m => ?_, fun m B hL => by cases hL⟩
    simp only [List.take_zero]
    intro o h; simp [argSets] at h
  | succ i ih =>
    intro hi
    obtain ⟨Wi, tvi⟩ := ih (by omega)
    have hia : i < args.length := by omega
    have hiD : i < Dw.length := by omega
    have hiA : i < As.length := by omega
    obtain ⟨hsa, ⟨keys, hk, hobs⟩, hx⟩ :=
      hdom i As[i] args[i] (List.getElem?_eq_getElem hiA) (List.getElem?_eq_getElem hia)
    generalize hbs : (args.take i).map (·.subst σ) = bs at Wi tvi
    have hbl : bs.length = i := by rw [← hbs]; simp; omega
    obtain ⟨hdTake, u, hDi⟩ := DomsSD.take_getElem hdoms i hiD
    have hdTake' : DomsSD env U Δ [] (Dw.take i) := hdTake
    have hDiTy : env.HasType U (Dw.take i).reverse Dw[i] (.sort u) := by
      simpa using hDi.1.defeq.hasType.1
    -- the split of a transported chain observation at the `i`-th binder
    have split : ∀ (keys : List Key) (z : Ob), ChainArgs env U Δ σ S keys (args.take i) →
        Obs' .id .empty (ci.type.instL ls) (piCodChain keys z) →
        ∃ ys z', ys.length = i ∧ z' ≼ z ∧
          Ctx.SubstEq env U Δ (VExpr.argSubst ys) (VExpr.argSubst bs) (Dw.take i).reverse ∧
          (∃ keys', List.Forall₂ (fun (k : Key) a => ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y)
              keys' (args.take i) ∧
            Obs' (VExpr.argSubst ys) (extS .empty keys') (.forallE Dw[i]
              (.wrapForalls (Dw.drop (i + 1)) Rw)) z') := by
      intro keys z hk hz
      obtain ⟨o', ho', l'⟩ := hTW _ hz
      obtain ⟨keys', z', rfl, hkk, hz'⟩ := Le.piCodChain_inv l'
      have hkl : keys'.length = i := by
        rw [List.Forall₂.length_eq hkk, hk.length]; simp; omega
      obtain ⟨keys'', ys, hT, hk'', hky, hz''⟩ := tele_split (by omega) ho'
      have hyl : ys.length = i := by rw [← List.Forall₂.length_eq hky, hkl]
      rw [hkl] at hT hz''
      rw [List.drop_eq_getElem_cons hiD] at hz''
      have hb : List.Forall₂ (fun (k : Key) b => k.2.1 b) keys'' bs := by
        rw [← hbs]; exact forall₂_cls hk'' hkk hk
      have WS := TeleKeys.substEq (v := .id) henv hΔ hT hdTake' .nil hb
      exact ⟨ys, z', hyl, hz', by simpa [VExpr.argSubst] using WS, keys',
        forall₂_comp_cover hkk hk, hz''⟩
    -- the domain classes agree
    obtain ⟨ys, z', hyl, hz', WS, keys', -, hzo⟩ := split keys _ hk hobs
    cases hz'.piDom_inv
    have hD := Obs.piDom_mem hzo
    have hDD : TyCls env U Δ (Dw[i].subst (VExpr.argSubst ys)) =
        TyCls env U Δ (Dw[i].subst (VExpr.argSubst bs)) := by
      have := hDiTy.substDF henv WS.wf hΔ WS
      exact TyCls.eq_of_defeq this
    have hcls := hD.trans hDD
    have haσ : env.HasType U Δ (args[i].subst σ) (As[i].subst σ) :=
      hsa.1.defeq.hasType.1.substDF henv W.wf hΔ W
    have ha' : env.HasType U Δ (args[i].subst σ) (Dw[i].subst (VExpr.argSubst bs)) :=
      TyCls.defeq_rev henv hΔ (hcls ▸ TyCls.self) haσ
    -- reshape the goal
    rw [List.take_succ_eq_append_getElem hia, List.take_succ_eq_append_getElem hiD,
      List.map_append, hbs, List.reverse_append, argSets_snoc]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, VExpr.argSubst_append_one]
    refine ⟨.cons Wi hDiTy ha', TV.cons_set tvi (fun o h w hw => Obs.backed h tv.1 w hw)
      fun o ho => ?_⟩
    have IHa := hsa.2 σ σ S W tv tv
    have h1 := IHa.2.2.1 o ho
    refine (h1.congr_cls (by simp only [vcls]; rw [hcls])).mono_le ?_
    intro x hxo
    obtain ⟨keys2, x', hk2, hobs2, l1⟩ := hx x hxo
    obtain ⟨ys2, z2, hyl2, hz2, WS2, keys2', hcov, hzo2⟩ := split keys2 _ hk2 hobs2
    obtain ⟨x3, rfl, l3⟩ := hz2.piDomOb_inv
    have hx3 := Obs.piDomOb_mem hzo2
    obtain ⟨x4, hx4, l4⟩ := hx3.mono_le (extS_cover hcov)
    have tvys : TV env U Δ ((Dw.take i).reverse ++ []) (VExpr.argSubst ys2)
        (argSets env U Δ σ S (args.take i)) :=
      TV.transfer henv hΔ (L := (Dw.take i).reverse) (Γ := [])
        (by simpa using DomsSD.ctxSD (L := []) (by simpa using hdTake') .nil)
        (by simpa using WS2)
        (fun x hx => by
          simp only [List.length_reverse, List.length_take] at hx
          rw [VExpr.argSubst_ge _ (by omega), VExpr.argSubst_ge _ (by omega), hyl2, hbl])
        (by simpa using tvi)
    obtain ⟨x5, hx5, l5⟩ := (hDi.2 _ _ _ (by simpa using WS2) tvys (by simpa using tvi)).1 x4 hx4
    exact ⟨x5, hx5, l5.trans (l4.trans (l3.trans l1))⟩

/-- **The valuation of a constant spine over a syntactic telescope.** -/
theorem spine_tele (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
    {Γ : List VExpr} {c : Name} {ls : List VLevel} {args : List VExpr} {T : VExpr}
    {σ : VExpr.Subst} {S : ObSets} {ci : VConstant}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) T) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hci : env.constants c = some ci) {Dw : List VExpr} {Rw : VExpr}
    (hTW : Ob.Sub (Obs' .id .empty (ci.type.instL ls)) (Obs' .id .empty (.wrapForalls Dw Rw)))
    (hpi : PiSD env U Δ [] Dw Rw) (hn : args.length ≤ Dw.length) :
    Ctx.SubstEq env U Δ (VExpr.argSubst (args.map (·.subst σ)))
      (VExpr.argSubst (args.map (·.subst σ))) (Dw.take args.length).reverse ∧
    TV env U Δ (Dw.take args.length).reverse (VExpr.argSubst (args.map (·.subst σ)))
      (argSets env U Δ σ S args) := by
  have := spine_tele_prefix henv hΔ H W tv hci hTW hpi hn args.length (Nat.le_refl _)
  simpa using this

end Model
end VEnv
end Lean4Lean
