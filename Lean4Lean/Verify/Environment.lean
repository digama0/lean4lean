import Lean4Lean.Verify.Environment.Extension

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.axiomInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf (.axiomInfo v) false hsafety).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hci, hn, hnonprim⟩ := h
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (hnonprim rfl) fun _ _ htr hci hadd old => ?_
  · exact .pure ⟨ves', hwf, ci', hstep⟩
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety)) := by
  unfold addDefinition; split
  · refine checkConstantVal.WF wf (.defnInfo v) false DefinitionSafety.unsafe_le
      |>.run wf |>.bind fun _ ⟨ci0, htr, hwfc, hn, hnonprim⟩ => ?_
    refine (checkNoMVarNoFVar.WF _ _ _).bind fun _ h => ?_
    have ⟨vesA, wfA, hstepA⟩ := addConst.WF wf (.axiomInfo { v with isUnsafe := true }) ci0
      .unsafe (fun _ => id) ⟨⟨DefinitionSafety.unsafe_le, htr.1.2.1, htr.1.2.2⟩, htr.2⟩
      hwfc hn (hnonprim rfl) fun _ _ htr' hci' hadd' old =>
        .axiom htr' (by rwa [← old.map_wf.find?'_eq_find?]) hci' hadd' old
    have hadd := (hstepA .unsafe).2.2
    refine checkBodyCore.WF (wfA.toVEnvAt .unsafe) (.defnDecl v)
      v.levelParams v.type v.value ci0.type (htr.1.2.2.mono (VEnv.addConst_le hadd)) h
      |>.run1 _ |>.bind fun _ h3 => ?_
    obtain ⟨value', hvalue, hvalueType⟩ := h3
    have hciWF : (⟨ci0, value'⟩ : VDefVal).WF (vesA.venv .unsafe) := by
      show (vesA.venv .unsafe).HasType ci0.uvars [] value' ci0.type
      rw [← htr.1.2.1]; exact hvalueType
    have ⟨ves', hwf', hmono'⟩ := addUnsafeDef.WF wf v ⟨ci0, value'⟩ (vesA.venv .unsafe)
      ‹_› htr hwfc hadd hvalue hciWF hn (hnonprim rfl)
    exact .pure ⟨ves', hwf', hmono', (nomatch · ‹_›)⟩
  refine (checkDefinition.WF wf v).run wf |>.bind
    fun _ ⟨allow, ci', hp, hu, ht, hname, hvalue, hci, hfresh, hnonprim⟩ => ?_
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety ?_ htr (hci.mono hmono) hfresh ?_ ?_
  · exact .pure ⟨ves', hwf, (hstep · |>.le), fun _ => ⟨ci', hstep⟩⟩
  · simp [ConstantInfo.defnInfo_safety]
  · intro hnamePrim; have := mt hnonprim; simp [hnamePrim] at this
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hp.safe this], hp.no_level_params this⟩
  · intro safety base hvisible hadd
    have hs : safety ≤ v.safety := by simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hsf : TrDefVal safety (ves.venv v.safety) (.defnInfo v) ci' :=
      ⟨⟨htr.1.1.sf_mono hs, htr.1.2⟩, htr.2⟩
    have hci' := hci.mono (hmono.trans (wf.mono hs))
    cases allow
    · exact (wf.hasPrimitives.addConst (hnonprim rfl) hadd).addDefEq
    · exact hp.preserves rfl (wf.mono DefinitionSafety.le_safe) wf.tr.wf wf.hasPrimitives
        (hsf.mono (wf.mono hs)) (hci.mono (hmono.trans (wf.mono hs))) hadd

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.thmInfo v) ci'.toVConstant (ves'.venv safety) := by
  refine (checkTheorem.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn hnonprim
    fun safety _ hheader _ hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  have hle := wf.mono hheader.1
  have htr' : TrDefVal safety (ves.venv safety) (.thmInfo v) ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.opaqueInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  refine (checkOpaque.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hvalue, hciC, hci, hfresh, hnonprim⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci'.toVConstVal :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.opaqueInfo v) ci'.toVConstVal checkSafety ?_ htr
    (hciC.mono hmono) hfresh hnonprim fun safety _ htr hciW hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · have hvis : safety ≤ checkSafety := hsafety ▸ htr.1
    have hto := hmono.trans (wf.mono hvis)
    exact .opaque (ci' := ci') ⟨⟨htr, hname⟩, hvalue.mono hto⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) (hci.mono hto) hadd old

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

private theorem Except.WF.throw' {e : ε} {Q : α → Prop} : (throw e : Except ε α).WF Q :=
  fun _ h => nomatch h

private theorem Except.WF.throwBind {e : ε} {f : α → Except ε β} {Q : β → Prop} :
    ((throw e : Except ε α) >>= f).WF Q := fun _ h => nomatch h

theorem addMutual.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (vs : List DefinitionVal) :
    (addMutual env vs).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addMutual
  simp only [reduceIte]
  split <;> [rename_i _ v₀ rest; exact Except.WF.throw']
  split <;> [exact Except.WF.throwBind; skip]
  have hsf : v₀.safety ≤ (if v₀.safety == .unsafe then .unsafe else .safe) := by
    cases v₀.safety with
    | «partial» => exact DefinitionSafety.le_safe
    | _ => exact DefinitionSafety.le_rfl
  refine (TypeChecker.M.WF.run (Q := fun _ =>
    (∃ cis, (v₀ :: rest).Forall₂ (fun v ci =>
      TrMutualHeader v₀.safety (ves.venv v₀.safety) env v ci ∧
      v.safety = v₀.safety ∧ v.levelParams = v₀.levelParams) cis) ∧
    (((v₀ :: rest).map (·.name)).Nodup ∧
      ∀ v ∈ (v₀ :: rest), (∅ : NameSet).contains v.name = false)) wf ?_).bind fun _ h1 => ?_
  · refine (TypeChecker.M.WF.forInFresh fun v found s => ?_).bind fun _ _ _ h => .pure h
    split <;> [exact .bindThrow .throw; rename_i hsafety]
    split <;> [exact .bindThrow .throw; rename_i hlp]
    split <;> [exact .bindThrow .throw; rename_i hfound]
    simp at hsafety hlp hfound
    rw [← hlp]
    refine (checkConstantVal.WF wf (.defnInfo v) false ?_ s).bind ?_
    · rw [ConstantInfo.defnInfo_safety, hsafety]; exact DefinitionSafety.le_rfl
    refine fun _ _ _ ⟨ci', htr, hciw, hn, hnp⟩ => .pure ?_
    exact ⟨hfound, ⟨⟨ci', .bvar 0⟩, ⟨htr, hciw, hn, hnp rfl⟩, hsafety, rfl⟩, rfl⟩
  obtain ⟨⟨cis0, hQ0⟩, hnd, -⟩ := h1
  have hhdr := hQ0.imp fun _ _ h => h.1
  have hpull {P : DefinitionVal → VDefVal → Prop} (h : List.Forall₂ P (v₀ :: rest) cis0)
      {R : DefinitionVal → Prop} (H : ∀ v ci, P v ci → R v) : ∀ v ∈ v₀ :: rest, R v :=
    fun v hv => have ⟨ci, _, hp⟩ := h.forall_exists_l v hv; H v ci hp
  have hbs := hpull hQ0 fun _ _ h => h.2.1
  have hfresh := hpull hhdr fun _ _ h => h.2.2.1
  have hnonprim := hpull hhdr fun _ _ h => h.2.2.2
  have hnameeq : (v₀ :: rest).map (·.name) = cis0.map (·.name) := by
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hhdr.imp fun _ _ h => h.1.2
  have hpullr {P : DefinitionVal → VDefVal → Prop} (h : List.Forall₂ P (v₀ :: rest) cis0)
      {R : VDefVal → Prop} (H : ∀ v ci, P v ci → R ci) : ∀ ci ∈ cis0, R ci :=
    fun ci hc => have ⟨v, _, hp⟩ := h.forall_exists_r ci hc; H v ci hp
  obtain ⟨base, hbase0⟩ := (wf.tr (safety := v₀.safety)).exists_addConsts
    (hpullr hhdr fun _ _ h => h.1.2 ▸ h.2.2.1) (hnameeq ▸ hnd)
  have wfA := VEnvAt.addAxioms hsf (wf.toVEnvAt v₀.safety) hhdr hnd hbase0
  refine (TypeChecker.M.WF.run1 (Q := fun _ => ∃ cis',
    cis0.Forall₂ (fun (ci ci' : VDefVal) => ci.toVConstVal = ci'.toVConstVal) cis' ∧
    (v₀ :: rest).Forall₂ (fun v ci' => TrExprS base v.levelParams [] v.value ci'.value ∧
      ci'.WF base) cis') wfA ?_).bind fun _ h2 => ?_
  · refine (TypeChecker.M.WF.forInForall₂ (fun v ci s hd => ?_) hQ0).bind fun _ _ _ h => .pure h
    have hdecl := hd.1.1.1.2.2.mono (VEnv.addConsts_le hbase0)
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF _ v.name v.value)).bind fun _ _ _ hclosed => ?_
    have hclosed' : v.value.FVarsIn
        (· ∈ (TypeChecker.VContext.mk1 wfA v.levelParams).vlctx.fvars) := by
      simpa [TypeChecker.VContext.mk1] using hclosed
    refine hd.2.2 ▸ (TypeChecker.checkType.WF hclosed').bind
      fun valType _ _ ⟨value', valType', _, hval, hvalTy, hhasType⟩ => ?_
    refine (TypeChecker.isDefEq.WF hvalTy hdecl).bind fun equal _ _ hequal => ?_
    split <;> [exact .bindThrow .throw; rename_i heq]
    refine .pure ⟨⟨⟨ci.toVConstVal, value'⟩, rfl, hval, ?_⟩, rfl⟩
    rw [VDefVal.WF, ← hd.1.1.1.2.1]
    exact hhasType.defeqU_r wfA.tr.wf (by trivial) (hequal (by simpa using heq))
  obtain ⟨cis, hRR, hbody⟩ := h2
  rw [VEnv.addConsts_congr hRR] at hbase0
  have : List.Forall₂ (TrMutualHeader v₀.safety (ves.venv v₀.safety) env) (v₀ :: rest) cis :=
    hhdr.trans (h₂ := hRR) fun v ci ci' h1 h2 => by
      have hc : ci.toVConstant = ci'.toVConstant := congrArg VConstVal.toVConstant h2
      exact ⟨h2 ▸ h1.1, hc ▸ h1.2.1, h1.2.2.1, h1.2.2.2⟩
  refine .pure <| addMutualBlock.WF wf v₀.safety (v₀ :: rest) cis base hbs hnd hfresh hnonprim
    (fun ci hc => ?_) hbase0 ((this.and hbody).imp (fun _ _ h => ⟨h.1.1, h.2.1⟩)) (fun ci hc => ?_)
  · obtain ⟨v, -, h⟩ := this.forall_exists_r ci hc; exact h.2.1
  · obtain ⟨v, -, h⟩ := hbody.forall_exists_r ci hc; exact h.2

/-- Successful checked addition preserves well-formedness and extends every safety-indexed
abstract environment. The only declaration form still outstanding is inductives, which need a
constructive `AddInduct` model. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => exact (addAxiom.WF wf v).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | thmDecl v => exact (addTheorem.WF wf v).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | defnDecl v => exact (addDefinition.WF wf v).mono fun _ ⟨ves', hwf, h, _⟩ => ⟨ves', hwf, h⟩
  | opaqueDecl v =>
    exact (addOpaque.WF wf v).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | quotDecl => exact addQuot.WF wf
  | mutualDefnDecl vs => exact addMutual.WF wf vs
  | inductDecl _ _ _ _ => sorry
