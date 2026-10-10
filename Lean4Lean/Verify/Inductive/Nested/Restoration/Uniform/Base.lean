import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Heads

/-! # Parameter uniformity: base constants (owner: Restoration-A)

The `Old` section of the source branch's `Nested/Restoration/Uniform/Whnf.lean`: the constants
of a base environment with a model `ves.WF env₀` avoid a head set fresh in `env₀`, and project
only out of base structures. With ι rules registered as patterns (no stored equations), the
translation of every rule right-hand side of a visible recursor is `TrEnv'.rules_tr`, read off
the `AddInduct` step that installed the recursor (`AddInduct.rec_find`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- Every rule right-hand side of a visible recursor translates. -/
theorem TrEnv'.rules_tr {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName : Name} {rval : RecursorVal}
    (H : TrEnv' safety C Q venv)
    (hrec : C.find? recName = some (.recInfo rval))
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∀ rule ∈ rval.rules, ∃ rhs, TrExprS venv rval.levelParams [] rule.rhs rhs := by
  intro rule hrule
  induction H with
  | empty => simp at hrec
  | inductProjections _ _ ih =>
    obtain ⟨rhs, htr⟩ := ih hrec
    exact ⟨rhs, htr.mono VEnv.addProjections_le⟩
  | ignore h1 h2 h3 ih =>
    rw [h3.map_wf.find?_insert] at hrec; split at hrec
    · injection hrec with hrec; subst hrec; exact absurd hsafe h2
    · exact ih hrec
  | thm _ h2 _ _ h5 h6 ih =>
    rw [h6.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨rhs, htr⟩ := ih hrec
      exact ⟨rhs, htr.mono (VEnv.addConst_le h5)⟩
  | mutualDef _ hnd hfr _ hadd _ h7 ih =>
    rcases insertDefs_find? h7.map_wf hfr hnd hrec with hrec' | ⟨d, _, _, hd⟩
    · obtain ⟨rhs, htr⟩ := ih hrec'
      exact ⟨rhs, htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le)⟩
    · exact absurd hd (by nofun)
  | «axiom» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨rhs, htr⟩ := ih hrec
      exact ⟨rhs, htr.mono (VEnv.addConst_le h4)⟩
  | defn _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨rhs, htr⟩ := ih hrec
      exact ⟨rhs, htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le)⟩
  | «opaque» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨rhs, htr⟩ := ih hrec
      exact ⟨rhs, htr.mono (VEnv.addConst_le h4)⟩
  | quot _ h2 h3 ih =>
    obtain ⟨rhs, htr⟩ := ih (h2.pull h3.map_wf hrec)
    exact ⟨rhs, htr.mono h2.le⟩
  | induct _ hadd h3 ih =>
    rcases hadd.rec_find h3.map_wf hrec with hC | ⟨r, hr, -, -, -, -, -, -, hrules⟩
    · obtain ⟨rhs, htr⟩ := ih hC
      exact ⟨rhs, htr.mono hadd.le⟩
    · obtain ⟨ru, -, -, -, -, -, hrutr⟩ := hrules rule hrule
      exact ⟨ru.rhs, hrutr⟩

namespace VerifyInductive

/-! ### Base constants -/

section Old

variable {env₀ env₁ : Environment} {ves : VEnvs} {heads : List Name}

private theorem find_constants (wf : ves.WF env₀) {n : Name} {ci : ConstantInfo}
    (h : env₀.find? n = some ci) : env₀.constants.find? n = some ci := by
  have hwf := (wf.tr (safety := .unsafe)).map_wf
  rw [← hwf.find?'_eq_find?]; exact h

/-- A name absent from the kernel environment is absent from its unsafe
abstract model. -/
theorem _root_.Lean4Lean.VEnvs.WF.unsafe_fresh (wf : ves.WF env₀) {n : Name} (h : env₀.find? n = none) :
    (ves.venv .unsafe).constants n = none := by
  cases hc : (ves.venv .unsafe).constants n with
  | none => rfl
  | some ci =>
    obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := .unsafe)).find?_iff.2 ⟨ci, hc⟩
    rw [h] at hfind; cases hfind

/-- A constant of the unsafe abstract model is a constant of the kernel environment. -/
theorem _root_.Lean4Lean.VEnvs.WF.unsafe_present (wf : ves.WF env₀) {n : Name} {ci : VConstant}
    (h : (ves.venv .unsafe).constants n = some ci) : ∃ ci', env₀.find? n = some ci' := by
  obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := .unsafe)).find?_iff.2 ⟨ci, h⟩
  exact ⟨ci', hfind⟩

variable (wf : ves.WF env₀)
  (hpres : ∀ {n ci}, env₀.find? n = some ci → env₁.find? n = some ci)
  (hfresh : ∀ h ∈ heads, env₀.find? h = none)

include wf hpres hfresh in
/-- **Projections on base structures are compatible with the head set**: a base
structure is not a head, and its constructors (base constants as well) are not
heads. -/
theorem projParamUniformIn_of_old {s : Name} {ci : ConstantInfo} (hs : env₀.find? s = some ci) :
    projAvoidsHeads env₁ heads s := by
  refine ⟨fun hmem => (by rw [hfresh s hmem] at hs; cases hs), fun v hv c hc hmem => ?_⟩
  rw [hpres hs] at hv
  cases hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  obtain ⟨C⟩ := wf.inductiveConstructorsCoherent s v hs i hi
  have hl := C.lookup
  rw [hfresh _ hmem] at hl
  cases hl

include wf hpres hfresh in
/-- Projections in syntax translated in the unsafe model of the base environment. -/
theorem projsOK_of_unsafe_tr {Us : List Name} {e : Expr} {e' : VExpr}
    (H : TrExprS (ves.venv .unsafe) Us [] e e') :
    e.ProjsOK (projAvoidsHeads env₁ heads) := by
  have hvwf := (wf.tr (safety := .unsafe)).wf
  refine (H.projsRegistered hvwf.orderedStrong trivial).mono fun s ⟨info, hinfo⟩ => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
    hvwf.ordered.projectionShape hinfo
  obtain ⟨ci, hci⟩ := wf.unsafe_present hlookup
  exact projParamUniformIn_of_old wf hpres hfresh hci


include wf hpres hfresh in
/-- Projections in syntax translated in any abstract environment whose
registered projections are registered in some safety model of the base
environment. -/
theorem projsOK_of_tr_sub (sf : DefinitionSafety) {V : VEnv} (hV : V.OrderedStrong)
    (hsub : ∀ s info, V.projections s info → ∃ info', (ves.venv sf).projections s info')
    {Us : List Name} {e : Expr} {e' : VExpr} (H : TrExprS V Us [] e e') :
    e.ProjsOK (projAvoidsHeads env₁ heads) := by
  have hvwf := (wf.tr (safety := sf)).wf
  refine (H.projsRegistered hV trivial).mono fun s ⟨info, hinfo⟩ => ?_
  obtain ⟨info', hinfo'⟩ := hsub s info hinfo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
    hvwf.ordered.projectionShape hinfo'
  obtain ⟨ci, hci, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨_, hlookup⟩
  exact projParamUniformIn_of_old wf hpres hfresh hci

include wf hfresh in
theorem avoids_of_tr (sf : DefinitionSafety) {Us : List Name} {Δ : VLCtx} {e : Expr}
    {e' : VExpr} (H : TrExprS (ves.venv sf) Us Δ e e') : e.AvoidsConsts heads := by
  refine checkPositivityStep.TrExprS.sourceAvoidsFresh (fun h hh => ?_) H
  cases hc : (ves.venv sf).constants h with
  | none => rfl
  | some ci =>
    obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨ci, hc⟩
    rw [hfresh h hh] at hfind; cases hfind

include wf hfresh in
theorem avoids_of_unsafe_tr {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS (ves.venv .unsafe) Us Δ e e') : e.AvoidsConsts heads :=
  checkPositivityStep.TrExprS.sourceAvoidsFresh
    (fun h hh => wf.unsafe_fresh (hfresh h hh)) H

include wf hfresh in
/-- Base constant types translate in the unsafe model, so they avoid the heads. -/
theorem old_type_avoids {n : Name} {ci : ConstantInfo} (h : env₀.find? n = some ci) :
    ci.type.AvoidsConsts heads ∧ ∃ e', TrExprS (ves.venv .unsafe) ci.levelParams [] ci.type e' := by
  obtain ⟨ci', -, -, -, htr⟩ := (wf.tr (safety := .unsafe)).find? h DefinitionSafety.unsafe_le
  exact ⟨avoids_of_unsafe_tr wf hfresh htr, _, htr⟩

include wf hfresh in
theorem old_value_avoids {n : Name} {ci : ConstantInfo} {v : Expr}
    (h : env₀.find? n = some ci) (hv : ci.deltaValue? = some v) :
    v.AvoidsConsts heads ∧ ∃ e', TrExprS (ves.venv .unsafe) ci.levelParams [] v e' := by
  obtain ⟨e', htr, -⟩ := (wf.tr (safety := .unsafe)).of_value h DefinitionSafety.unsafe_le hv
  exact ⟨avoids_of_unsafe_tr wf hfresh htr, _, htr⟩

include wf hfresh in
theorem old_rules_avoid {n : Name} {r : RecursorVal}
    (h : env₀.find? n = some (.recInfo r)) {rule : RecursorRule} (hrule : rule ∈ r.rules) :
    rule.rhs.AvoidsConsts heads ∧
      ∃ e', TrExprS (ves.venv .unsafe) r.levelParams [] rule.rhs e' := by
  obtain ⟨e', he'⟩ := TrEnv'.rules_tr (wf.tr (safety := .unsafe)) (find_constants wf h)
    DefinitionSafety.unsafe_le rule hrule
  exact ⟨avoids_of_unsafe_tr wf hfresh he', _, he'⟩

include wf hpres hfresh in
/-- The major family of a base recursor is a base inductive, so neither it nor
its constructors are heads. -/
theorem old_rec_major {n : Name} {r : RecursorVal} (h : env₀.find? n = some (.recInfo r)) :
    r.getMajorInduct ∉ heads ∧
      ∀ v, env₁.find? r.getMajorInduct = some (.inductInfo v) → ∀ c ∈ v.ctors, c ∉ heads := by
  obtain ⟨info, hinfo', -⟩ := (wf.toVEnvAt .unsafe).toCheckerEnv.recursorMajorCtors h
  exact projParamUniformIn_of_old wf hpres hfresh hinfo'

end Old

end VerifyInductive
end Lean4Lean
