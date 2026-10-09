import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineTele
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjValid

/-! # Arity of rigid-ended Pi telescopes, from soundness of an earlier environment

Definitionally equal Pi telescopes ending in applications of rigid constants have the same number
of binders, provided the derivation is in an environment `E` whose derivations are sound in the
model of a later environment `envF` (`tele_arity`). Rigidity of the ends is needed: telescopes
ending in defined constants can be definitionally equal at different lengths. The proof: at the
target context of the domains of the left telescope, its innermost domain variables anchor a
codomain chain observation of depth the number of its binders (`deep_obs`); soundness carries it
to an observation of the right telescope, which has such chains only up to its own number of
binders (`chain_lt`), because a rigid spine has no codomain observation (`rigid_spine_not_pi`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- A spine of a rigid constant has no `sort`, `piDom`, `piCod` or `piCodOb` observation. -/
theorem rigid_spine_not_pi {σ : VExpr.Subst} {S : ObSets} {o : Ob}
    (hrig : env.Rigid c) (h : Obs' σ S (.mkApps (.const c ls) args) o)
    (ho : (∃ z, o = .sort z) ∨ (∃ D, o = .piDom D) ∨ (∃ c' C, o = .piCod c' C) ∨
      ∃ c' K p, o = .piCodOb c' K p) : False := by
  have hna : o.NotApp := by
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> trivial
  obtain ⟨keys, -, hw⟩ := wrap_of_obs_mkApps h
  rcases Obs.const_iff.1 hw with ⟨_, _, keys', r, e, _, _, _, _, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r, e, _, _, _, _, _, hr, _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, keys', r, e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · obtain ⟨-, rfl⟩ := wrap_inj e hna hr.notApp
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig df hdf _)
  · have hrn : r.NotApp := by
      rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨-, rfl⟩ := wrap_inj e hna hrn
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig df hdf lsP)
  all_goals
    obtain ⟨-, rfl⟩ := wrap_inj e hna trivial
    rcases ho with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h

/-- A codomain chain observation of a rigid-ended telescope is shorter than the telescope. -/
theorem chain_lt (hrig : env.Rigid c) :
    ∀ {ds : List VExpr} {keys : List Key} {σ : VExpr.Subst} {S : ObSets} {c' C},
      Obs' σ S (.wrapForalls ds (.mkApps (.const c ls) args)) (piCodChain keys (.piCod c' C)) →
      keys.length < ds.length
  | [], keys, σ, S, c', C, h => by
    exfalso
    refine rigid_spine_not_pi hrig h ?_
    cases keys with
    | nil => exact .inr (.inr (.inl ⟨_, _, rfl⟩))
    | cons k ks => exact .inr (.inr (.inr ⟨_, _, _, rfl⟩))
  | _ :: ds, [], _, _, _, _, _ => by simp
  | _ :: ds, k :: keys, σ, S, c', C, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, piCodChain_cons] at h
    obtain ⟨-, -, _, -, h⟩ := Obs.piCodOb_mem h
    have := chain_lt (ds := ds) (keys := keys) hrig h
    simp only [List.length_cons]; omega

/-- Anchors for the domains of a telescope at a valuation: a term of each domain, at the
valuation extended by the earlier anchors. -/
def Anch (env : VEnv) (U : Nat) (Δ : List VExpr) : VExpr.Subst → List VExpr → Prop
  | _, [] => True
  | σ, A :: ds => ∃ x, env.HasType U Δ x (A.subst σ) ∧ Anch env U Δ (σ.cons x) ds

/-- A deep codomain chain observation of an anchored telescope. -/
theorem deep_obs {R : VExpr} :
    ∀ {ds : List VExpr} {σ : VExpr.Subst} {S : ObSets}, ds ≠ [] → Anch env U Δ σ ds →
      ∃ keys c C, keys.length + 1 = ds.length ∧
        Obs' σ S (.wrapForalls ds R) (piCodChain keys (.piCod c C))
  | [], _, _, h, _ => absurd rfl h
  | [A], σ, S, _, ⟨x, hx, _⟩ => by
    refine ⟨[], ElCls env U Δ (TyCls env U Δ (A.subst σ)) x,
      TyCls env U Δ (R.subst (σ.cons x)), rfl, ?_⟩
    simp only [VExpr.wrapForalls, List.foldr_cons, List.foldr_nil, piCodChain_nil]
    exact .piCod (.of_hasType hx) ElCls.self
  | A :: B :: ds, σ, S, _, ⟨x, hx, ha⟩ => by
    obtain ⟨keys, c, C, hl, h⟩ := deep_obs (ds := B :: ds) (σ := σ.cons x)
      (S := S.cons (listSet [])) (by simp) ha
    refine ⟨(TyCls env U Δ (A.subst σ), ElCls env U Δ (TyCls env U Δ (A.subst σ)) x, []) :: keys,
      c, C, by simp [hl], ?_⟩
    simp only [piCodChain_cons]
    exact .piCodOb (τs := []) (.of_hasType hx) nofun nofun (fun _ h => nomatch h) ElCls.self h

/-- The shift substitution. -/
def shiftS (m : Nat) : VExpr.Subst := fun k => .bvar (k + m)

theorem subst_shiftS (e : VExpr) (m : Nat) : e.subst (shiftS m) = e.liftN m := by
  have h := VExpr.liftN_subst (n := m) (k := 0) (e := e) (σ := .id)
  rw [VExpr.subst_id] at h
  rw [h]
  congr 1
  funext k
  simp [shiftS, VExpr.Subst.lift_l, VExpr.Subst.id, Lift.consN, Lift.liftVar_skipN]

theorem shiftS_cons (m : Nat) : (shiftS (m + 1)).cons (.bvar m) = shiftS m := by
  funext k
  cases k with
  | zero => simp [VExpr.Subst.cons, shiftS]
  | succ k => simp [VExpr.Subst.cons, shiftS]; omega

/-- The domains of a telescope are anchored, at the shift valuation, by the variables of the
reversed telescope. -/
theorem anch_shift (env : VEnv) (U : Nat) {ds : List VExpr} :
    ∀ (pre suf : List VExpr), ds = pre ++ suf →
      Anch env U ds.reverse (shiftS suf.length) suf
  | _, [], _ => trivial
  | pre, A :: suf, e => by
    refine ⟨.bvar suf.length, ?_, ?_⟩
    · rw [subst_shiftS]
      have hl : suf.length < ds.reverse.length := by simp [e]
      have hL := lookup_append (Γ := []) ds.reverse suf.length hl
      rw [List.append_nil] at hL
      have hget : ds.reverse[suf.length] = A := by
        subst e
        simp [List.reverse_append]
      rw [hget] at hL
      exact .bvar hL
    · have := anch_shift env U (ds := ds) (pre ++ [A]) suf (by rw [e]; simp)
      simpa [shiftS_cons] using this

theorem onCtx_of_hasType_wrapForalls {E : VEnv} (hE : E.Ordered) :
    ∀ {ds Γ : List VExpr} {R T : VExpr}, OnCtx Γ (E.IsType U) →
      E.HasType U Γ (.wrapForalls ds R) T → ds ≠ [] → OnCtx (ds.reverse ++ Γ) (E.IsType U)
  | [], _, _, _, _, _, h => absurd rfl h
  | d :: ds, Γ, R, T, hΓ, h, _ => by
    obtain ⟨h1, h2⟩ := HasType.forallE_inv hE h
    have hΓ' : OnCtx (d :: Γ) (E.IsType U) := ⟨hΓ, h1⟩
    cases ds with
    | nil => simpa using hΓ'
    | cons d' ds =>
      obtain ⟨_, h2⟩ := h2
      have := onCtx_of_hasType_wrapForalls hE (ds := d' :: ds) hΓ' h2 (by simp)
      simpa [List.reverse_cons, List.append_assoc] using this

theorem onCtx_mono {E E' : VEnv} (hle : E ≤ E') :
    ∀ {Γ : List VExpr}, OnCtx Γ (E.IsType U) → OnCtx Γ (E'.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨onCtx_mono hle h1, h2.mono hle⟩

/-- One direction of `tele_arity`. -/
theorem tele_arity_le {envF E : VEnv} (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → SoundTypedIn envF E U Δ)
    {ds ds' : List VExpr} {c c' : Name} {ls ls' : List VLevel} {as as' : List VExpr}
    {T : VExpr} (hrig' : envF.Rigid c')
    (h : E.IsDefEq U [] (.wrapForalls ds (.mkApps (.const c ls) as))
      (.wrapForalls ds' (.mkApps (.const c' ls') as')) T) :
    ds.length ≤ ds'.length := by
  by_cases hne : ds = []
  · subst hne; simp
  have hΔE := onCtx_of_hasType_wrapForalls hE (Γ := []) trivial h.hasType.1 hne
  rw [List.append_nil] at hΔE
  have hΔ := onCtx_mono hEF hΔE
  have hs := IsDefEq.strong hE (show OnCtx [] (E.IsType U) from trivial) h
  have S := (hsnd U ds.reverse hΔ hs).1 (shiftS ds.length) (shiftS ds.length) .empty .nil
    TV.empty TV.empty
  have ha := anch_shift envF U [] ds rfl
  obtain ⟨keys, c0, C0, hl, ho⟩ := deep_obs (env := envF) (R := .mkApps (.const c ls) as)
    (S := .empty) hne ha
  obtain ⟨o', ho', l⟩ := S.1 _ ho
  obtain ⟨keys', x', rfl, hk, hx⟩ := Le.piCodChain_inv l
  rw [hx.piCod_inv] at ho'
  have := chain_lt hrig' ho'
  have := List.Forall₂.length_eq hk
  omega

/-- **Arity of rigid-ended telescopes**: in an environment whose derivations are sound in the
model of `envF`, definitionally equal Pi telescopes ending in spines of constants rigid in `envF`
have the same number of binders. -/
theorem tele_arity {envF E : VEnv} (hE : E.Ordered) (hEF : E ≤ envF)
    (hsnd : ∀ U Δ, OnCtx Δ (envF.IsType U) → SoundTypedIn envF E U Δ)
    {ds ds' : List VExpr} {c c' : Name} {ls ls' : List VLevel} {as as' : List VExpr}
    {T : VExpr} (hrig : envF.Rigid c) (hrig' : envF.Rigid c')
    (h : E.IsDefEq U [] (.wrapForalls ds (.mkApps (.const c ls) as))
      (.wrapForalls ds' (.mkApps (.const c' ls') as')) T) :
    ds.length = ds'.length :=
  Nat.le_antisymm (tele_arity_le hE hEF hsnd hrig' h) (tele_arity_le hE hEF hsnd hrig h.symm)

end Model
end VEnv
end Lean4Lean
