import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaDefs

/-! # Rules with an empty right-hand side

Observation-level lemmas for rules that eliminate into `Prop`, used at recursor equations whose
target is `≈ 0`:

* `motive_tele_empty`, `motive_tele_empty_ctx`: nothing is typed at the observations of a Pi
  telescope whose codomain applies a motive into `Prop`;
* `rhs_empty_motive`, `rhs_empty_motive_ctx`: hence the right-hand side of such a rule has no
  observations at typed valuations. -/

namespace Lean4Lean

theorem Lookup.append_left : ∀ {L : List VExpr} {i : Nat} {A : VExpr},
    Lookup L i A → Lookup (L ++ Γ) i A
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => .succ (Lookup.append_left h)

namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Small elimination**: nothing is typed at the observations of a closed Pi telescope whose
codomain applies a bound variable whose binder type is a telescope ending in a sort that is
identically zero (the motive of an eliminator into `Prop`). -/
theorem motive_tele_empty {doms args mds : List VExpr} {T X : VExpr} {m : Nat} {w : VLevel}
    {lk : List Key} {p : Ob} {τs : List Ob}
    (hT : HTS env U Δ [] (.wrapForalls doms T) X) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0) (hlk : lk.length = doms.length)
    (ho : TypedOb env U Δ cv (wrap lk p) τs)
    (hτs : ∀ τ ∈ τs, Obs' .id .empty (.wrapForalls doms T) τ) : False := by
  obtain ⟨σ', S', hk, τc, _, hτc, hp⟩ := tele_unwind henv hΔ hT.piSD .nil TV.empty hlk ho hτs
  obtain ⟨-, tv'⟩ := hk.typed henv hΔ hT.piSD.doms .nil TV.empty
  rw [List.append_nil] at tv'
  refine hp.not_prop fun τ hτ => ?_
  have h := hτc τ hτ
  rw [eT] at h
  obtain ⟨keys, hkeys, hb⟩ := wrap_of_obs_mkApps h
  obtain ⟨τs', h1, h2⟩ := tv'.2 m _ hm _ (Obs.bvar_iff.1 hb)
  obtain ⟨τc', _, h3, h4⟩ := chain_terminal_sort (env := env) (U := U) (Δ := Δ) (w := w)
    (by rw [hlen]; exact List.Forall₂.length_eq hkeys) h2 (fun τ hτ => ⟨_, _, h1 τ hτ⟩)
  refine ⟨_, h4.strengthen fun k hk => ⟨_, List.mem_singleton_self _, ?_⟩⟩
  rw [h3 k hk, hw]; exact .refl

/-- `motive_tele_empty` in a context with a typed valuation. -/
theorem motive_tele_empty_ctx {doms args mds : List VExpr} {T X : VExpr} {m : Nat} {w : VLevel}
    {lk : List Key} {p : Ob} {τs : List Ob} {σ : VExpr.Subst} {S : ObSets}
    (hT : HTS env U Δ Γ (.wrapForalls doms T) X) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0) (hlk : lk.length = doms.length)
    (ho : TypedOb env U Δ cv (wrap lk p) τs)
    (hτs : ∀ τ ∈ τs, Obs' σ S (.wrapForalls doms T) τ) : False := by
  obtain ⟨σ', S', hk, τc, _, hτc, hp⟩ := tele_unwind henv hΔ hT.piSD W tv hlk ho hτs
  obtain ⟨-, tv'⟩ := hk.typed henv hΔ hT.piSD.doms W tv
  refine hp.not_prop fun τ hτ => ?_
  have h := hτc τ hτ
  rw [eT] at h
  obtain ⟨keys, hkeys, hb⟩ := wrap_of_obs_mkApps h
  obtain ⟨τs', h1, h2⟩ := tv'.2 m _ (Lookup.append_left hm) _ (Obs.bvar_iff.1 hb)
  obtain ⟨τc', _, h3, h4⟩ := chain_terminal_sort (env := env) (U := U) (Δ := Δ) (w := w)
    (by rw [hlen]; exact List.Forall₂.length_eq hkeys) h2 (fun τ hτ => ⟨_, _, h1 τ hτ⟩)
  refine ⟨_, h4.strengthen fun k hk => ⟨_, List.mem_singleton_self _, ?_⟩⟩
  rw [h3 k hk, hw]; exact .refl

/-- The right-hand side of a rule whose type is a telescope over a motive into a
proposition, typed in the rule's context, has no observations at typed valuations. -/
theorem rhs_empty_motive_ctx {df : VDefEq} {ls : List VLevel} {doms args mds : List VExpr}
    {T body : VExpr} {m : Nat} {w : VLevel} {u : VLevel}
    (et : df.type.instL ls = .wrapForalls doms T) (er : df.rhs.instL ls = .wrapLams doms body)
    (hT : HTS env U Δ Γ (df.type.instL ls) (.sort u)) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0)
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) (o : Ob) :
    ¬ Obs' σ S (df.rhs.instL ls) o := by
  intro ho
  obtain ⟨τs, hτs, hty⟩ := (ihR σ σ S W tv tv).2.2.1 o ho
  rw [er] at ho
  obtain ⟨lk, _, _, p, hk, rfl, -⟩ := Obs.wrapLams_iff.1 ho
  rw [et] at hT
  exact motive_tele_empty_ctx henv hΔ hT W tv eT hm hlen hw hk.length hty
    (fun τ hτ => by have := hτs τ hτ; rw [et] at this; exact this)

/-- The right-hand side of a rule whose type is a closed telescope over a motive into a
proposition has no observations at typed valuations. -/
theorem rhs_empty_motive {df : VDefEq} {ls : List VLevel} {doms args mds : List VExpr}
    {T body : VExpr} {m : Nat} {w : VLevel} {u : VLevel}
    (et : df.type.instL ls = .wrapForalls doms T) (er : df.rhs.instL ls = .wrapLams doms body)
    (hcl : (df.type.instL ls).ClosedN)
    (hT : HTS env U Δ [] (df.type.instL ls) (.sort u)) (eT : T = .mkApps (.bvar m) args)
    (hm : Lookup doms.reverse m (.wrapForalls mds (.sort w))) (hlen : mds.length = args.length)
    (hw : w.eval = fun _ => 0)
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) (o : Ob) :
    ¬ Obs' σ S (df.rhs.instL ls) o := by
  intro ho
  obtain ⟨τs, hτs, hty⟩ := (ihR σ σ S W tv tv).2.2.1 o ho
  rw [er] at ho
  obtain ⟨lk, _, _, p, hk, rfl, -⟩ := Obs.wrapLams_iff.1 ho
  rw [et] at hT hcl
  exact motive_tele_empty henv hΔ hT eT hm hlen hw hk.length hty
    (fun τ hτ => by have := hτs τ hτ; rw [et] at this; exact (Obs.closed_iff_id hcl).1 this)

end

end Model
end VEnv
end Lean4Lean
