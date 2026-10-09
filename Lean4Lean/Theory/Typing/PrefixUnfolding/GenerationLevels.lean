import Lean4Lean.Theory.Typing.PrefixUnfolding.LevelCongruence
import Lean4Lean.Theory.Inductive.QuotPrefixUnfolding
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Theory.Inductive.SingletonReconstruction
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation

namespace Lean4Lean.InductiveSignature.RecursorData
open VEnv VExpr

theorem supplyType_levels (ha : List.Forall₂ (EqUpToLevels U) args args')
    (ht : EqUpToLevels U type type') (H : supplyType args type = some output) :
    ∃ output', supplyType args' type' = some output' ∧ EqUpToLevels U output output' := by
  induction ha generalizing type type' output with
  | nil => cases H; exact ⟨_, rfl, ht⟩
  | cons ha hs ih =>
    cases ht <;> try contradiction
    rename_i hd hb
    exact ih (EqUpToLevels.instN ha hb) H

theorem takeForalls_levels (ht : EqUpToLevels U type type')
    (H : VExpr.takeForalls count type = some (domains, result)) :
    ∃ domains' result', VExpr.takeForalls count type' = some (domains', result') ∧
      List.Forall₂ (EqUpToLevels U) domains domains' ∧ EqUpToLevels U result result' := by
  induction count generalizing type type' domains result with
  | zero => cases H; exact ⟨[], _, rfl, .nil, ht⟩
  | succ n ih =>
    cases ht <;> try contradiction
    rename_i hd hb
    simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, htake, H⟩ := H
    cases H
    obtain ⟨ds', body', htake', hds, hbody⟩ := ih hb htake
    exact ⟨_, _, by simp only [VExpr.takeForalls, bind, htake', Option.bind_some]; rfl, .cons hd hds, hbody⟩

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

private theorem levels_getD {R : α → β → Prop} (H : List.Forall₂ R a b)
    (hd : R default₁ default₂) (i : Nat) : R (a[i]?.getD default₁) (b[i]?.getD default₂) := by
  induction H generalizing i with
  | nil => exact hd
  | cons h hs ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i

private theorem levels_vars (n k : Nat) : List.Forall₂ (EqUpToLevels U) (vars n k) (vars n k) := by
  unfold vars
  apply Lean4Lean.List.Forall₂.rfl
  intro e he
  simp only [List.mem_reverse, List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  exact .bvar

private theorem levels_lift (H : List.Forall₂ (EqUpToLevels U) args args') (n : Nat) :
    List.Forall₂ (EqUpToLevels U) (args.map (·.liftN n)) (args'.map (·.liftN n)) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN) H

end Lean4Lean.VEnv

namespace Lean4Lean.QuotPrefixUnfolding
open VEnv VExpr InductiveSignature InductiveSignature.RecursorData

theorem propInhabitant_levels (hl : l.WF U) (hl' : l'.WF U) (he : l ≈ l') :
    EqUpToLevels U (propInhabitant l) (propInhabitant l') := by
  have H := EqUpToLevels.instL_expr (propInhabitant (.param 0))
    (ls := [l]) (ls' := [l']) (by simpa) (by simpa) (.cons he .nil)
  simpa [propInhabitant, VExpr.instL_wrapLams, VExpr.instL_mkApps, VExpr.instL, VLevel.inst,
    VExpr.lift, VExpr.liftN] using H

theorem generate_levels {levels levels' : List VLevel}
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : generate levels args = some program) :
    ∃ program', generate levels' args' = some program' ∧ PrefixUnfolding.LevelEquiv U program program' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  have hargslen := Lean4Lean.List.Forall₂.length_eq ha
  unfold generate at H ⊢
  simp only [← hlen, ← hargslen]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, hbody, H⟩ := H
  cases H
  obtain ⟨residual', hsupply', hres⟩ := supplyType_levels ha
    (EqUpToLevels.instL_expr _ hl hl' he) hsupply
  obtain ⟨domains', result', htake', hdoms, hresult⟩ := takeForalls_levels hres htake
  let remaining := 6 - args.length
  have hall := List.Forall₂.append' (levels_lift ha remaining) (levels_vars (U := U) remaining 0)
  have hdefault : EqUpToLevels U (default : VExpr) default := .sort trivial trivial rfl
  have halpha := levels_getD hall hdefault 0
  have hrelation := levels_getD hall hdefault 1
  have hmajor := levels_getD hall hdefault 5
  have hlevel := levels_getD he (show VLevel.zero ≈ .zero from rfl) 0
  have hlevelWF : (levels[0]?.getD VLevel.zero).WF U := by
    cases hh : levels[0]? with
    | none => trivial
    | some u => exact hl u (List.mem_of_getElem? hh)
  have hlevelWF' : (levels'[0]?.getD VLevel.zero).WF U := by
    cases hh : levels'[0]? with
    | none => trivial
    | some u => exact hl' u (List.mem_of_getElem? hh)
  have hproof := EqUpToLevels.mkApps_args (propInhabitant_levels hlevelWF hlevelWF' hlevel)
    (.cons halpha (.cons hrelation (.cons hmajor .nil)))
  have hconstructor := EqUpToLevels.mkApps_args
    (EqUpToLevels.const (c := ``Quot.mk) (by simpa using hlevelWF) (by simpa using hlevelWF') (.cons hlevel .nil))
    (.cons halpha (.cons hrelation (.cons hproof .nil)))
  have hcaptures := List.Forall₂.append' (List.forall₂_take hall 5) (.cons hproof .nil)
  simp only [bind, hsupply', htake', hbody, Option.bind_some]
  exact ⟨_, rfl, ⟨hdoms, hresult, hconstructor, rfl, rfl, hcaptures, he, hl'⟩⟩

end Lean4Lean.QuotPrefixUnfolding


namespace Lean4Lean.InductiveSignature.RecursorData
open VEnv VExpr CaseSchema

theorem singletonUnfolding_levels {data : RecursorData} {levels levels' : List VLevel}
    {env : VEnv}
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : data.singletonUnfolding env U levels args = some program) :
    ∃ program', data.singletonUnfolding env U levels' args' = some program' ∧
      PrefixUnfolding.LevelEquiv U program program' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  have hargslen := Lean4Lean.List.Forall₂.length_eq ha
  unfold singletonUnfolding at H ⊢
  simp only [← hlen, ← hargslen]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  have hguard' := hguard
  simp at hguard'
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨recType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, hrecon, equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptures
  cases H
  obtain ⟨residual', hsupply', hres⟩ := supplyType_levels ha
    (EqUpToLevels.instL_expr _ hl hl' he) hsupply
  obtain ⟨domains', result', htake', hdoms, hresult⟩ := takeForalls_levels hres htake
  let remaining := data.majorOffset + 1 - args.length
  have hall := List.Forall₂.append' (levels_lift ha remaining) (levels_vars (U := U) remaining 0)
  obtain ⟨constructor', fields', hrecon', heconstructor, hefields⟩ :=
    singletonReconstruction_levels hl hl' he hall hrecon
  have hecaptures := List.Forall₂.append' (List.forall₂_take hall data.indexOffset) hefields
  dsimp only [remaining] at hrecon'
  simp only [bind, htype, hsupply', htake', hrecon', hequation, hbody, Option.bind_some]
  have hcaplen := Lean4Lean.List.Forall₂.length_eq hecaptures
  dsimp only [remaining] at hcaplen
  rw [← hcaplen, if_neg hcaptures]
  exact ⟨_, rfl, ⟨hdoms, hresult, heconstructor, rfl, rfl, hecaptures, he, hl'⟩⟩

end Lean4Lean.InductiveSignature.RecursorData
