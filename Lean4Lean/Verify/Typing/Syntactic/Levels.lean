import Lean4Lean.Verify.Typing.Syntactic.Context
import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.ExprUniverses

/-!
# Syntactic infrastructure: universe levels

Translation of kernel levels (`VLevel.ofLevel`) through the kernel's level simplifications
(`mkLevelMax'`, `mkLevelIMax'`) and level-parameter substitution (`substParams_wf`), up to level
equivalence; the scoping of a translated level (`VLevel.ofLevel_paramsIn`); and contexts that are
equal up to level equivalence (`VLCtx.LEquiv`).
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean

theorem VLevel.ofLevel_paramsIn (H : VLevel.ofLevel Us level = some target) :
    level.paramsIn Us = true := by
  induction level generalizing target with simp [VLevel.ofLevel, bind] at H
  | zero => rfl
  | succ _ ih => obtain ⟨target, h, _⟩ := H; exact ih h
  | max _ _ ih₁ ih₂ | imax _ _ ih₁ ih₂ =>
    obtain ⟨_, h₁, _, h₂, _⟩ := H
    simp [Level.paramsIn, ih₁ h₁, ih₂ h₂]
  | param name =>
    simpa [Level.paramsIn] using List.idxOf_lt_length_iff.mp H.1

theorem ofLevel_mkLevelMax'
    (h1 : VLevel.ofLevel Us u = some u') (h2 : VLevel.ofLevel Us v = some v') :
    ∃ w, VLevel.ofLevel Us (mkLevelMax' u v) = some w ∧ w ≈ .max u' v' := by
  let subsumes (u v : Level) : Bool :=
    if v.isExplicit && u.getOffset ≥ v.getOffset then true
    else match u with
      | Level.max u₁ u₂ => v == u₁ || v == u₂
      | _ => false
  let mkLevelMaxCore (u v : Level) :=
    if u == v then u
    else if u.isZero then v
    else if v.isZero then u
    else if subsumes u v then u
    else if subsumes v u then v
    else if u.getLevelOffset == v.getLevelOffset then
      if u.getOffset ≥ v.getOffset then u else v
    else
      .max u v
  change ∃ w, VLevel.ofLevel Us (mkLevelMaxCore u v) = some w ∧ w ≈ .max u' v'
  have le {u v u' v'} (h : subsumes u v)
      (hu : VLevel.ofLevel Us u = some u')
      (hv : VLevel.ofLevel Us v = some v') : v'.LE u' := by
    simp [subsumes] at h
    obtain ⟨h1, h2⟩ | h := h
    · clear subsumes mkLevelMaxCore
      induction v generalizing u u' v' with simp [VLevel.ofLevel] at hv h2 ⊢
      | zero => subst v'; exact VLevel.zero_le
      | succ _ ih =>
        obtain ⟨_, hv, rfl⟩ := hv
        generalize eq : u.getOffset' = n at h2
        unfold Level.getOffset' at eq; split at eq <;> subst eq <;> [skip; cases h2]
        simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
        simp [Level.isExplicit] at h1
        exact VLevel.succ_le_succ (ih hu hv h1.2 (Nat.le_of_succ_le_succ h2))
      | _ => cases h1
    · split at h <;> [skip; cases h]
      simp [VLevel.ofLevel] at hu; obtain ⟨_, hu1, _, hu2, rfl⟩ := hu
      simp at h; obtain rfl | rfl := h
      · cases hv.symm.trans hu1
        exact VLevel.le_max_left
      · cases hv.symm.trans hu2
        exact VLevel.le_max_right
  simp only [mkLevelMaxCore]; split
  · simp_all; exact VLevel.max_self.symm
  split
  · let .zero := u; simp [VLevel.ofLevel] at h1; subst u'
    exact ⟨_, h2, VLevel.zero_le.max_eq_right.symm⟩
  split
  · let .zero := v; simp [VLevel.ofLevel] at h2; subst v'
    exact ⟨_, h1, VLevel.zero_le.max_eq_left.symm⟩
  split
  · exact ⟨_, h1, (le ‹_› h1 h2).max_eq_left.symm⟩
  split
  · exact ⟨_, h2, (le ‹_› h2 h1).max_eq_right.symm⟩
  split
  · rename_i h
    simp at h ⊢
    let rec lem1 {v : Level} {u' v'}
        (hu : VLevel.ofLevel Us v.getLevelOffset = some u')
        (hv : VLevel.ofLevel Us v = some v') : u'.LE v' := by
      unfold Level.getLevelOffset at hu; split at hu
      · simp [VLevel.ofLevel] at hv; obtain ⟨_, hv, rfl⟩ := hv
        exact VLevel.le_trans (lem1 hu hv) VLevel.le_succ
      · cases hu.symm.trans hv; exact VLevel.le_refl _
    let rec lem2 {u v : Level} {u' v'}
        (h1 : u.getLevelOffset = v.getLevelOffset)
        (h2 : u.getOffset' ≤ v.getOffset')
        (hu : VLevel.ofLevel Us u = some u')
        (hv : VLevel.ofLevel Us v = some v') : u'.LE v' := by
      revert h1 h2; unfold Level.getLevelOffset Level.getOffset'
      split <;> simp <;> split <;> (try simp)
      · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
        simp [VLevel.ofLevel] at hv; obtain ⟨_, hv, rfl⟩ := hv
        exact (VLevel.succ_le_succ <| lem2 · · hu hv)
      · rintro rfl; exact lem1 (v := .succ _) hu hv
      · rintro rfl; cases hu.symm.trans hv; exact VLevel.le_refl _
    split <;> rename_i h3
    · exact ⟨_, h1, (lem2 h.symm h3 h2 h1).max_eq_left.symm⟩
    · exact ⟨_, h2, (lem2 h (Nat.le_of_not_le h3) h1 h2).max_eq_right.symm⟩
  simp [VLevel.ofLevel]; exact ⟨_, ⟨_, h1, _, h2, rfl⟩, rfl⟩

theorem ofLevel_isNeverZero (h : VLevel.ofLevel Us u = some u') (H : u.isNeverZero) :
    u'.IsNeverZero := by
  induction u generalizing u' with simp [Level.isNeverZero, VLevel.ofLevel] at H h <;> intro ls
  | succ =>
    obtain ⟨_, h1, rfl⟩ := h
    exact Nat.succ_ne_zero _
  | max _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    intro h
    rw [VLevel.eval, ← Nat.le_zero, Nat.max_le] at h; simp at h
    exact H.elim (ih1 h1 · _ h.1) (ih2 h2 · _ h.2)
  | imax _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp [VLevel.eval, Lean.Nat.imax, ih2 h2 H ls]

theorem ofLevel_isAlwaysZero (h : VLevel.ofLevel Us u = some u') (H : u.isAlwaysZero) :
    u' ≈ .zero := by
  induction u generalizing u' with
    simp [Level.isAlwaysZero, VLevel.ofLevel] at H h <;> subst_vars <;>
    refine VLevel.equiv_def.2 fun ls => ?_
  | zero => rfl
  | max _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp [VLevel.eval, VLevel.equiv_def.1 (ih1 h1 H.1) ls, VLevel.equiv_def.1 (ih2 h2 H.2) ls]
  | imax _ _ _ ih2 =>
    obtain ⟨_, _, _, h2, rfl⟩ := h
    simp [VLevel.eval, Lean.Nat.imax, VLevel.equiv_def.1 (ih2 h2 H) ls]

theorem ofLevel_mkLevelIMax'
    (h1 : VLevel.ofLevel Us u = some u') (h2 : VLevel.ofLevel Us v = some v') :
    ∃ w, VLevel.ofLevel Us (mkLevelIMax' u v) = some w ∧ w ≈ .imax u' v' := by
  let mkLevelIMaxCore (u v : Level) :=
    if v.isNeverZero then mkLevelMax' u v
    else if v.isZero then v
    else if u.isZero then v
    else if u == v then u
    else .imax u v
  change ∃ w, VLevel.ofLevel Us (mkLevelIMaxCore u v) = some w ∧ w ≈ .imax u' v'
  simp only [mkLevelIMaxCore]; split
  · have ⟨_, a1, a2⟩ := ofLevel_mkLevelMax' h1 h2
    exact ⟨_, a1, .trans a2 (ofLevel_isNeverZero h2 ‹_›).imax_eq_max.symm⟩
  split
  · let .zero := v; simp [VLevel.ofLevel] at h2; subst v'
    exact ⟨.zero, rfl, rfl⟩
  split
  · let .zero := u; simp [VLevel.ofLevel] at h1; subst u'
    exact ⟨_, h2, VLevel.zero_imax.symm⟩
  split
  · simp_all; exact VLevel.imax_self.symm
  simp [VLevel.ofLevel]; exact ⟨_, ⟨_, h1, _, h2, rfl⟩, rfl⟩

section
variable {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)
  (eqF : (fun x => ((List.idxOf? x ps).bind fun x => ls[x]?).getD (Level.param x)) = F)
include Hls eq eqF

attribute [-simp] Bool.forall_bool in
theorem substParams_wf (red) (H : VLevel.ofLevel ps u = some u') :
    ∃ u₁, VLevel.ofLevel Us (u.substParams' F red) = some u₁ ∧ u₁ ≈ u'.inst ls' := by
  induction u generalizing u' red with simp_all [VLevel.ofLevel, Level.substParams']
  | zero => subst u'; rfl
  | succ _ ih =>
    obtain ⟨_, H, rfl⟩ := H
    exact let ⟨_, h1, h2⟩ := ih _ H; ⟨_, ⟨_, h1, rfl⟩, VLevel.succ_congr h2⟩
  | max _ _ ih1 ih2 =>
    obtain ⟨_, H1, _, H2, rfl⟩ := H
    generalize (_ && _) = red'
    let ⟨_, a1, a2⟩ := ih1 (red := red') H1
    let ⟨_, b1, b2⟩ := ih2 (red := red') H2
    split
    · have ⟨w, c1, c2⟩ := ofLevel_mkLevelMax' a1 b1
      exact ⟨_, c1, .trans c2 <| VLevel.max_congr a2 b2⟩
    · simp [VLevel.ofLevel]
      exact ⟨_, ⟨_, a1, _, b1, rfl⟩, VLevel.max_congr a2 b2⟩
  | imax _ _ ih1 ih2 =>
    obtain ⟨_, H1, _, H2, rfl⟩ := H
    generalize (_ && _) = red'
    let ⟨_, a1, a2⟩ := ih1 (red := red') H1
    let ⟨_, b1, b2⟩ := ih2 (red := red') H2
    split
    · have ⟨w, c1, c2⟩ := ofLevel_mkLevelIMax' a1 b1
      exact ⟨_, c1, .trans c2 <| VLevel.imax_congr a2 b2⟩
    · simp [VLevel.ofLevel]
      exact ⟨_, ⟨_, a1, _, b1, rfl⟩, VLevel.imax_congr a2 b2⟩
  | param x =>
    obtain ⟨H, rfl⟩ := H; subst eqF; simp
    have := List.idxOf_eq_getD_idxOf? x ps; unfold Option.getD at this; revert this
    split <;> simp [*, Nat.ne_of_lt, VLevel.inst]; rintro rfl; clear ‹_› eq
    generalize List.idxOf x ps = n at *
    rw [List.mapM_eq_some] at Hls
    induction Hls generalizing n with
    | nil => cases H
    | cons Hl _ ih =>
      obtain _|n := n <;> simp
      · exact ⟨_, Hl, rfl⟩
      · exact ih _ (Nat.lt_of_succ_lt_succ H)

theorem substParams_wf_list (red) {us us' : List _} (H : us.mapM (VLevel.ofLevel ps) = some us') :
    ∃ us₁, (us.map (Level.substParams' F red)).mapM (VLevel.ofLevel Us) = some us₁ ∧
      List.Forall₂ (· ≈ ·) us₁ (us'.map (·.inst ls')) := by
  induction us generalizing us' with simp_all
  | cons u us ih =>
    obtain ⟨_, H1, _, H2, rfl⟩ := H
    have ⟨_, h1, h2⟩ := ih H2
    have ⟨_, h3, h4⟩ := substParams_wf Hls eq eqF red H1
    refine ⟨_, ⟨_, h3, _, h1, rfl⟩, .cons h4 h2⟩

end

/-! ### Level-equivalent contexts -/

inductive VLocalDecl.LEquiv (U : Nat) : VLocalDecl → VLocalDecl → Prop
  | vlam : VExpr.LEquiv U A A' → VLocalDecl.LEquiv U (.vlam A) (.vlam A')
  | vlet : VExpr.LEquiv U A A' → VExpr.LEquiv U v v' →
    VLocalDecl.LEquiv U (.vlet A v) (.vlet A' v')

inductive VLCtx.LEquiv (U : Nat) : VLCtx → VLCtx → Prop
  | nil : VLCtx.LEquiv U [] []
  | cons : VLCtx.LEquiv U Δ₁ Δ₂ → VLocalDecl.LEquiv U d₁ d₂ →
    VLCtx.LEquiv U ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem VLocalDecl.LEquiv.refl : ∀ d, VLocalDecl.LEquiv U d d
  | .vlam _ => .vlam .refl
  | .vlet .. => .vlet .refl .refl

theorem VLCtx.LEquiv.refl : ∀ Δ, VLCtx.LEquiv U Δ Δ
  | [] => .nil
  | (_, d) :: Δ => .cons (.refl Δ) (.refl d)

theorem VLocalDecl.LEquiv.depth : VLocalDecl.LEquiv U d₁ d₂ → d₁.depth = d₂.depth
  | .vlam _ | .vlet .. => rfl

theorem VLocalDecl.LEquiv.value : VLocalDecl.LEquiv U d₁ d₂ → VExpr.LEquiv U d₁.value d₂.value
  | .vlam _ => .refl
  | .vlet _ h => h

theorem VLocalDecl.LEquiv.type : VLocalDecl.LEquiv U d₁ d₂ → VExpr.LEquiv U d₁.type d₂.type
  | .vlam h => h.liftN
  | .vlet h _ => h

theorem VLCtx.LEquiv.find? (H : VLCtx.LEquiv U Δ₁ Δ₂) (h : Δ₂.find? v = some (e, A)) :
    ∃ e₁ A₁, Δ₁.find? v = some (e₁, A₁) ∧ VExpr.LEquiv U e₁ e ∧ VExpr.LEquiv U A₁ A := by
  induction H generalizing v e A with
  | nil => cases h
  | cons _ hd ih =>
    revert h; unfold VLCtx.find?; split
    · rintro ⟨⟩; exact ⟨_, _, rfl, hd.value, hd.type⟩
    · simp; rintro e A h rfl rfl
      obtain ⟨e₁, A₁, h1, l1, l2⟩ := ih h
      exact ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, hd.depth ▸ l1.liftN, hd.depth ▸ l2.liftN⟩

end Lean4Lean
