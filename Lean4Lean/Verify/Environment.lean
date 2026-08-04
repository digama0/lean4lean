import Lean4Lean.Verify.Environment.Extension

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf (.axiomInfo v) false hsafety).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hci, hn, hnonprim⟩ := h
  refine .pure <| addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (hnonprim rfl) fun _ _ htr hci hadd old => ?_
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr
      (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addNonrecursiveDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hunsafe : v.safety ≠ .unsafe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addDefinition
  split
  · contradiction
  refine (checkDefinition.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨allow, ci', hp, hu, ht, hname, hvalue, hci, hfresh, hnonprim⟩ := h
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  refine .pure <| addDef.WF wf v ci' v.safety ?_ htr (hci.mono hmono) hfresh ?_ ?_
  · simp [ConstantInfo.defnInfo_safety]
  · intro hnamePrim
    have hallow : allow = true := by
      cases allow
      · simp_all
      · rfl
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hp.safe hallow], hp.no_level_params hallow⟩
  · intro safety base hvisible hadd
    have hs : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have htr' : TrDefVal safety (ves.venv safety) (.defnInfo v) ci' := by
      have hsf : TrDefVal safety (ves.venv v.safety) (.defnInfo v) ci' :=
        ⟨⟨htr.1.1.sf_mono hs, htr.1.2⟩, htr.2⟩
      exact hsf.mono (wf.mono hs)
    have hci' := hci.mono (hmono.trans (wf.mono hs))
    cases allow with
    | false => exact (wf.hasPrimitives.addConst (hnonprim rfl) hadd).addDefEq
    | true =>
      exact hp.preserves (safety := safety) (venv := ves.venv safety)
        (env' := base) (ci' := ci') rfl (wf.mono DefinitionSafety.le_safe)
        (wf.tr (safety := safety)).wf wf.hasPrimitives htr' hci' hadd

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addTheorem
  refine (checkTheorem.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  refine .pure <| addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn hnonprim
    fun safety _ hheader _ hadd old => ?_
  have hle := wf.mono hheader.1
  have htr' : TrThmVal safety (ves.venv safety) v ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  unfold addOpaque
  refine (checkOpaque.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hci, hfresh, hnonprim, _⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci' :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  refine .pure <| addConst.WF wf (.opaqueInfo v) ci' checkSafety ?_ htr
    (hci.mono hmono) hfresh hnonprim fun _ _ htr hci hadd old => ?_
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · exact .opaque ⟨htr, hname⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => False := by
  -- `AddInduct` currently has no constructors, so the unsafe translation cannot contain
  -- the inductive `Eq` declaration required by quotient initialization. This case becomes
  -- constructive when the inductive-declaration verification boundary is implemented.
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    have hfind' : env.constants.find? ``Eq = some (.inductInfo info) := by
      rw [← (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?]
      exact hfind
    exact False.elim <| (wf.tr (safety := .unsafe)).no_inductInfo hfind'
  | _ => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

/-- This is currently vacuous in the non-initialized case: `TrEnv` cannot contain the
inductive `Eq` declaration until `AddInduct` is implemented. -/
theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold Environment.addQuot
  split
  · exact .pure ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  · exact (checkEqType.WF wf).bind fun _ h => False.elim h

/-- Declaration forms currently represented by `TrEnv`. Recursive unsafe definitions and
mutual definitions require a recursive-body relation, while inductives require a
constructive `AddInduct` model. -/
def _root_.Lean.Declaration.IsModelled : Declaration → Prop
  | .axiomDecl _ | .thmDecl _ | .opaqueDecl _ | .quotDecl => True
  | .defnDecl v => v.safety ≠ .unsafe
  | .mutualDefnDecl _ | .inductDecl .. => False

/-- Successful checked addition of a modelled declaration preserves well-formedness and
extends every safety-indexed abstract environment. Quotient initialization is vacuous
until inductive environments are represented, so this theorem currently applies only to
synthetic environments without inductive declarations. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration)
    (hdecl : decl.IsModelled) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => exact addAxiom.WF wf v
  | defnDecl v => exact addNonrecursiveDefinition.WF wf v (by simpa [Declaration.IsModelled] using hdecl)
  | thmDecl v => exact addTheorem.WF wf v
  | opaqueDecl v => exact addOpaque.WF wf v
  | mutualDefnDecl _ => simp [Declaration.IsModelled] at hdecl
  | quotDecl => exact addQuot.WF wf
  | inductDecl _ _ _ _ => simp [Declaration.IsModelled] at hdecl
