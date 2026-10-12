import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineVal

/-! # Congruence of constant spines

`spine_congr`: the observations of a spine `mkApps (const c ls) args` are subsumed by those
of `mkApps (const c ls) args'` whenever, argument by argument, the observations of `args[i]`
are subsumed by those of `args'[i]` and the two arguments are definitionally equal in the
target context at (the class of) the telescope domain of the constant's type at that position.
No typing of the spines in their context is needed: every observation of a constant head is
filtered by typing at the constant's type (`Obs.const_typed`), which pins the domain classes
of its keys (`tele_unwind`), so the key classes of the one spine are key classes of the other.
`LvEq.mkApps_const` changes the levels of the head. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem LvEq.mkApps_const {c : Name} {ls ls' : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hls' : ∀ l ∈ ls', l.WF U) (h : List.Forall₂ (· ≈ ·) ls ls') (args : List VExpr) :
    LvEq U (.mkApps (.const c ls) args) (.mkApps (.const c ls') args) := by
  induction args using List.reverseRecOn with
  | nil => exact .const hls hls' h
  | snoc as a ih => rw [VExpr.mkApps_snoc, VExpr.mkApps_snoc]; exact .app ih .refl

/-- The key classes of a spine contain the arguments. -/
theorem keys_cls_self {σ : VExpr.Subst} {S : ObSets} : ∀ {keys : List Key} {args : List VExpr},
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env U Δ k.1 (a.subst σ) ∧
      ∀ x ∈ k.2.2, ∃ x', Obs' σ S a x' ∧ x' ≼ x) keys args →
    List.Forall₂ (fun (k : Key) b => k.2.1 b) keys (args.map (·.subst σ))
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (by rw [h.1]; exact ElCls.self) (keys_cls_self t)

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Congruence of constant spines.** -/
theorem spine_congr {c : Name} {ls : List VLevel} {ci : VConstant} {Dw : List VExpr}
    {Rw : VExpr} {u : VLevel} (hci : env.constants c = some ci)
    (hTW : ci.type.instL ls = .wrapForalls Dw Rw)
    (hT : HTS env U Δ [] (ci.type.instL ls) (.sort u))
    {args args' : List VExpr} {σ : VExpr.Subst} {S : ObSets}
    (hlen : args.length = args'.length) (hn : args.length ≤ Dw.length)
    (hsub : ∀ i (hi : i < args.length) (hi' : i < args'.length),
      Ob.Sub (Obs' σ S args[i]) (Obs' σ S args'[i]))
    (hdef : ∀ i (hi : i < args.length) (hi' : i < args'.length) (hiD : i < Dw.length), ∃ X,
      TyCls env U Δ (Dw[i].subst (VExpr.argSubst ((args.take i).map (·.subst σ)))) X ∧
      env.IsDefEq U Δ (args[i].subst σ) (args'[i].subst σ) X) :
    Ob.Sub (Obs' σ S (.mkApps (.const c ls) args)) (Obs' σ S (.mkApps (.const c ls) args')) := by
  intro o ho
  obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps_le ho
  have hkl : keys.length = args.length := List.Forall₂.length_eq hk
  obtain ⟨τs, hτs, hty⟩ := Obs.const_typed hw hci
  have hsplit : ci.type.instL ls =
      .wrapForalls (Dw.take args.length) (.wrapForalls (Dw.drop args.length) Rw) := by
    rw [hTW, ← VExpr.wrapForalls_append, List.take_append_drop]
  rw [hsplit] at hτs hT
  have hds := hT.piSD
  have htl : (Dw.take args.length).length = args.length := by
    simp [List.length_take, Nat.min_eq_left hn]
  obtain ⟨σ', S', hTK, -⟩ := tele_unwind henv hΔ hds .nil TV.empty (by rw [hkl, htl]) hty hτs
  obtain ⟨ys, rfl, -, hyl, -, hd⟩ := hTK.data
  have hcls := keys_cls_self hk
  have W' := hTK.substEq henv hΔ (v := .id) hds.doms .nil hcls
  rw [List.append_nil] at W'
  have hyl' : ys.length = args.length := hyl.trans htl
  have W'' : Ctx.SubstEq env U Δ (VExpr.argSubst ys) (VExpr.argSubst (args.map (·.subst σ)))
      (Dw.take ys.length).reverse := by rw [hyl']; exact W'
  refine ⟨o, obs_mkApps_of_wrap_le ?_ hw, .refl⟩
  refine List.forall₂_of_getElem (by rw [hkl, hlen]) fun i hi hi' => ?_
  have hia : i < args.length := by omega
  have hiD : i < Dw.length := by omega
  obtain ⟨_, hki⟩ := List.forall₂_getElem_exists hk i hi
  have hiA : (Dw.take args.length)[i]? = some Dw[i] := by
    rw [List.getElem?_take_of_lt hia]; exact List.getElem?_eq_getElem hiD
  obtain ⟨hk1, -, -, -, -⟩ := hd i keys[i] (ys[i]'(by omega)) Dw[i]
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega)) hiA
  have Wi := substEq_take ys (args.map (·.subst σ)) (by simp [hyl']) (by rw [hyl']; exact hn)
    W'' i (by omega)
  obtain ⟨-, w, hDi⟩ := DomsSD.take_getElem hds.doms i (by omega)
  have hDiTy : env.HasType U (Dw.take i).reverse Dw[i] (.sort w) := by
    have := hDi.1.defeq.hasType.1
    simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hia), List.getElem_take] using this
  have eT : TyCls env U Δ (Dw[i].subst (VExpr.argSubst (ys.take i))) =
      TyCls env U Δ (Dw[i].subst (VExpr.argSubst ((args.take i).map (·.subst σ)))) := by
    rw [List.map_take]
    exact TyCls.eq_of_defeq (hDiTy.substDF henv Wi.wf hΔ Wi)
  obtain ⟨X, hX, hdf⟩ := hdef i hia hi' hiD
  have hXk : keys[i].1 X := by
    have e : keys[i].1 = TyCls env U Δ (Dw[i].subst (VExpr.argSubst (ys.take i))) := hk1
    rw [e, eT]; exact hX
  refine ⟨by rw [hki.1]; exact ElCls.eq_of_defeq hXk hdf, ?_⟩
  obtain ⟨K', h1, h2⟩ := exists_list_cover (P := Obs' σ S args'[i]) (R := fun y x => y ≼ x)
    (L := keys[i].2.2) fun x hx => by
      obtain ⟨y, hy, l⟩ := hki.2 x hx
      obtain ⟨y', hy', l'⟩ := hsub i hia hi' y hy
      exact ⟨y', hy', l'.trans l⟩
  exact ⟨K', h1, h2⟩

end

end Model
end VEnv
end Lean4Lean
