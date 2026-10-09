import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Inductive
import Lean4Lean.Verify.QuotInit

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal)
    (fuel : FuelConfig := {})
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety) := by intro; trivial) :
    (addAxiom env v (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.axiomInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf (.axiomInfo v) false hsafety).run wf (hmode _)
    |>.bind fun _ ⟨ci', htr, hci, hn, hnonprim⟩ => ?_
  have hnonprim' :
      Environment.primitives.contains (ConstantInfo.axiomInfo v).name = false := by
    cases hprim : Environment.primitives.contains (ConstantInfo.axiomInfo v).name
    · rfl
    · have := hnonprim (by simp [hprim])
      contradiction
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; cases h) hnonprim'
    fun _ _ htr hci hadd old => ?_
  · exact .pure ⟨ves', hwf, ci', hstep⟩
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal)
    (fuel : FuelConfig := {})
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety) := by intro; trivial) :
    (addDefinition env v (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety)) := by
  unfold addDefinition; split
  · refine checkConstantVal.WF wf (.defnInfo v) false DefinitionSafety.unsafe_le
      |>.run wf (hmode _) |>.bind fun _ ⟨ci0, htr, hwfc, hn, hnonprim⟩ => ?_; simp at hnonprim
    refine (checkNoMVarNoFVar.WF _ _ _).bind fun _ h => ?_
    have ⟨vesA, wfA, hstepA⟩ := addConst.WF wf (.axiomInfo { v with isUnsafe := true }) ci0
      .unsafe (fun _ => id) ⟨⟨DefinitionSafety.unsafe_le, htr.1.2.1, htr.1.2.2⟩, htr.2⟩
      hwfc hn (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; cases h) hnonprim
      fun _ _ htr' hci' hadd' old =>
        .axiom htr' (by rwa [← old.map_wf.find?'_eq_find?]) hci' hadd' old
    have hadd := (hstepA .unsafe).2.2
    refine checkBodyCore.WF (wfA.toVEnvAt .unsafe) (.defnDecl v)
      v.levelParams v.type v.value ci0.type (htr.1.2.2.mono (VEnv.addConst_le hadd)) h
      |>.run1 _ ((hmode .unsafe).mono (VEnv.addConst_le hadd)) |>.bind fun _ h3 => ?_
    obtain ⟨value', hvalue, hvalueType⟩ := h3
    have hciWF : (⟨ci0, value'⟩ : VDefVal).WF (vesA.venv .unsafe) := by
      show (vesA.venv .unsafe).HasType ci0.uvars [] value' ci0.type
      rw [← htr.1.2.1]; exact hvalueType
    have ⟨ves', hwf', hmono'⟩ := addUnsafeDef.WF wf v ⟨ci0, value'⟩ (vesA.venv .unsafe)
      ‹_› htr hwfc hadd hvalue hciWF hn hnonprim
    exact .pure ⟨ves', hwf', hmono', (nomatch · ‹_›)⟩
  refine (checkDefinition.WF wf v).run wf (hmode _) |>.bind
    fun _ ⟨ci', hp, hu, ht, hname, hvalue, hci, hfresh⟩ => ?_
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety ?_ htr (hci.mono hmono) hfresh ?_ ?_
  · exact .pure ⟨ves', hwf, (hstep · |>.le),
      fun _ => ⟨ci', hstep⟩⟩
  · simp [ConstantInfo.defnInfo_safety]
  · exact fun h => ⟨by rw [ConstantInfo.defnInfo_safety, (hp h).safe], (hp h).no_level_params⟩
  · intro safety base hvisible hadd
    have hs : safety ≤ v.safety := by simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hsf : TrDefVal safety (ves.venv v.safety) (.defnInfo v) ci' :=
      ⟨⟨htr.1.1.sf_mono hs, htr.1.2⟩, htr.2⟩
    have hci' := hci.mono (hmono.trans (wf.mono hs))
    cases eq : Environment.primitives.contains v.name
    · exact (wf.hasPrimitives.addConst eq hadd).addDefEq
    · exact (hp eq).preserves (wf.mono DefinitionSafety.le_safe) wf.tr.wf wf.hasPrimitives
        (hsf.mono (wf.mono hs)) (hci.mono (hmono.trans (wf.mono hs))) hadd

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal)
    (fuel : FuelConfig := {})
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety) := by intro; trivial) :
    (addTheorem env v (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.thmInfo v) ci'.toVConstant (ves'.venv safety) := by
  refine (checkTheorem.WF wf v).run wf (hmode _) |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn
    (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; cases h) hnonprim
    fun safety _ hheader _ hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  have hle := wf.mono hheader.1
  have htr' : TrDefVal safety (ves.venv safety) (.thmInfo v) ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal)
    (fuel : FuelConfig := {})
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety) := by intro; trivial) :
    (addOpaque env v (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.opaqueInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  refine (checkOpaque.WF wf v).run wf (hmode _) |>.bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hvalue, hciC, hci, hfresh, hnonprim⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci'.toVConstVal :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.opaqueInfo v) ci'.toVConstVal checkSafety ?_ htr
    (hciC.mono hmono) hfresh (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; cases h) hnonprim
    fun safety _ htr hciW hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · have hvis : safety ≤ checkSafety := hsafety ▸ htr.1
    have hto := hmono.trans (wf.mono hvis)
    exact .opaque (ci' := ci') ⟨⟨htr, hname⟩, hvalue.mono hto⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) (hci.mono hto) hadd old

/-- Dispatch of an inductive declaration: `addDecl` satisfies `Q` if, for every result
`allowPrimitive` of the primitive-family precheck `Primitive.checkInductive`, the call to
`Environment.addInductive` with that bit does. The premise keeps the precheck so that the
verified continuation receives the same `allowPrimitive` bit as the executable branch. -/
theorem addInductiveDeclaration.WF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (Q : Environment → Prop)
    (Hadd : ∀ allowPrimitive,
      Primitive.checkInductive env lparams nparams types isUnsafe =
        .ok allowPrimitive →
      (Environment.addInductive env lparams nparams types isUnsafe
        allowPrimitive fuel).WF Q) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF Q := by
  have Hcheck :
      (Primitive.checkInductive env lparams nparams types
        isUnsafe).WF fun allowPrimitive =>
          (Environment.addInductive env lparams nparams types isUnsafe
            allowPrimitive fuel).WF Q := by
    intro allowPrimitive hallow
    exact Hadd allowPrimitive hallow
  have Hcombined := Hcheck.bind fun _ Hrun => Hrun
  simpa [addDecl] using Hcombined

/-- Complete checked declaration dispatch across the primitive, ordinary,
and nested execution paths, with the source-facing result: the output environment carries an
`InductiveExtension` of the submitted declaration.  The executable primitive precheck selects the
primitive branch; otherwise the verified lowering result selects the ordinary or the nested
continuation.  Inductive soundness does not depend on the presence or interpretation of the
prelude's `Eq`.
The source specification additionally assumes that the source
declaration has no loose bound variables; the executable only rejects
metavariables and free variables, and nested lowering would silently repair
loose bound variables while re-closing constructor types.  Environment
preservation itself (`WF_preserves`) does not need this hypothesis. -/
theorem addInductiveDeclaration.WF_spec
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (HsourcesB : VerifyInductive.SourceBVarClosed types) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (VerifyInductive.InductiveExtension env outEnv ves lparams
          nparams types isUnsafe) := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel
    (fun outEnv => Nonempty (VerifyInductive.InductiveExtension env outEnv ves
      lparams nparams types isUnsafe))
  intro allowPrimitive hallow
  cases allowPrimitive with
  | false =>
    exact VerifyInductive.Environment.addInductive.inductiveExtensionWF
      env lparams nparams types isUnsafe fuel ves wf hmode HsourcesB
  | true =>
    have Hprimitive : VerifyInductive.PrimitiveInductiveShape lparams
        nparams types isUnsafe :=
      (VerifyInductive.checkPrimitiveInductive_eq_true_iff env lparams
        nparams types isUnsafe).mp hallow
    exact
      VerifyInductive.Environment.addInductive.primitiveInductiveExtensionWF
        env lparams nparams types isUnsafe fuel ves wf hmode Hprimitive

/-- Environment preservation for the complete inductive declaration dispatch: the invariant
and monotonicity of every safety-indexed model.  It has no hypothesis on the source declaration: it is derived from the
well-formedness halves of the three execution branches, not from the
source-facing specification. -/
theorem addInductiveDeclaration.WF_preserves
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety)) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel
    (fun outEnv => ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety))
  intro allowPrimitive hallow
  cases allowPrimitive with
  | false =>
    apply VerifyInductive.Environment.addInductive.checkedLoweringClosedWF
      env lparams nparams types isUnsafe false fuel wf.inductivesClosed
      (VerifyInductive.VEnvs.WF.environmentTypesClosed wf)
    intro res Hsources Hlower
    by_cases haux : res.aux2nested.size = 0
    · exact VerifyInductive.Environment.addInductiveAfterLowering.ordinaryInstalledModelWF
        env lparams nparams types isUnsafe fuel res ves wf hmode Hlower.toResult haux
    · exact
        (VerifyInductive.Environment.addInductiveAfterLowering.nestedInductiveExtensionWF
          env lparams nparams types isUnsafe fuel res ves wf hmode Hsources Hlower
            haux).mono fun _ ⟨H⟩ => H.modelExtension
  | true =>
    have Hprimitive : VerifyInductive.PrimitiveInductiveShape lparams
        nparams types isUnsafe :=
      (VerifyInductive.checkPrimitiveInductive_eq_true_iff env lparams
        nparams types isUnsafe).mp hallow
    exact
      (VerifyInductive.Environment.addInductive.primitiveInductiveExtensionWF
        env lparams nparams types isUnsafe fuel ves wf hmode Hprimitive).mono
        fun _ ⟨H⟩ => H.modelExtension

private theorem Except.WF.throw' {e : ε} {Q : α → Prop} : (throw e : Except ε α).WF Q :=
  fun _ h => nomatch h

private theorem Except.WF.throwBind {e : ε} {f : α → Except ε β} {Q : β → Prop} :
    ((throw e : Except ε α) >>= f).WF Q := fun _ h => nomatch h

theorem addMutual.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (vs : List DefinitionVal)
    (fuel : FuelConfig := {})
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety) := by intro; trivial) :
    (addMutual env vs (fuel := fuel)).WF fun env' =>
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
      ∀ v ∈ (v₀ :: rest), (∅ : NameSet).contains v.name = false)) wf ?_ (hmode _)).bind
    fun _ h1 => ?_
  · refine (TypeChecker.M.WF.forInFresh fun v found s => ?_).bind fun _ _ _ h => .pure h
    split <;> [exact .bindThrow .throw; rename_i hsafety]
    split <;> [exact .bindThrow .throw; rename_i hlp]
    split <;> [exact .bindThrow .throw; rename_i hfound]
    simp at hsafety hlp hfound
    rw [← hlp]
    refine (checkConstantVal.WF wf (.defnInfo v) false ?_ s).bind ?_
    · rw [ConstantInfo.defnInfo_safety, hsafety]; exact DefinitionSafety.le_rfl
    refine fun _ _ _ ⟨ci', htr, hciw, hn, hnp⟩ => .pure ?_; simp at hnp
    exact ⟨hfound, ⟨⟨ci', .bvar 0⟩, ⟨htr, hciw, hn, hnp⟩, hsafety, rfl⟩, rfl⟩
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
      ci'.WF base) cis') wfA ?_ ((hmode _).mono (VEnv.addConsts_le hbase0))).bind fun _ h2 => ?_
  · refine (TypeChecker.M.WF.forInForall₂ (fun v ci s hd => ?_) hQ0).bind fun _ _ _ h => .pure h
    have hdecl := hd.1.1.1.2.2.mono (VEnv.addConsts_le hbase0)
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF _ v.name v.value)).bind fun _ _ _ hclosed => ?_
    have hclosed' : v.value.FVarsIn
        (· ∈ (TypeChecker.VContext.mk1 wfA v.levelParams fuel).vlctx.fvars) := by
      simpa [TypeChecker.VContext.mk1, TypeChecker.VContext.mkCheckingValid, TypeChecker.VContext.mkChecking] using hclosed
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
  have hwfc : ∀ ci ∈ cis, ci.toVConstant.WF (ves.venv v₀.safety) := fun ci hc => by
    obtain ⟨v, -, h⟩ := this.forall_exists_r ci hc; exact h.2.1
  have hciWF : ∀ ci ∈ cis, ci.WF base := fun ci hc => by
    obtain ⟨v, -, h⟩ := hbody.forall_exists_r ci hc; exact h.2
  obtain ⟨ves', wf', hle'⟩ := addMutualBlock.WF wf v₀.safety (v₀ :: rest) cis base hbs hnd
    hfresh hnonprim hwfc hbase0
    ((this.and hbody).imp (fun _ _ h => ⟨h.1.1, h.2.1⟩)) hciWF
  exact .pure ⟨ves', wf', hle'⟩

/-- `addDecl.WF_quotReadyAt` for any configuration whose cache mode is sound for the input
models (`CacheMode.Sound`: nothing in the scoped mode, canonical `Eq` in the global mode). -/
theorem addDecl.WF_quotReadyAt_fuel {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration)
    (hq : decl = .quotDecl → ∀ safety, (ves.venv safety).QuotReady)
    (fuel : FuelConfig) (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety)) :
    (addDecl env decl (check := true) (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) := by
  cases decl with
  | axiomDecl v =>
    exact (addAxiom.WF wf v fuel hmode).mono fun _ ⟨ves', hwf, _, h⟩ =>
      ⟨ves', hwf, (h · |>.le)⟩
  | thmDecl v =>
    exact (addTheorem.WF wf v fuel hmode).mono fun _ ⟨ves', hwf, _, h⟩ =>
      ⟨ves', hwf, (h · |>.le)⟩
  | defnDecl v =>
    exact (addDefinition.WF wf v fuel hmode).mono fun _ ⟨ves', hwf, h, _⟩ => ⟨ves', hwf, h⟩
  | opaqueDecl v =>
    exact (addOpaque.WF wf v fuel hmode).mono fun _ ⟨ves', hwf, _, h⟩ =>
      ⟨ves', hwf, (h · |>.le)⟩
  | quotDecl => exact addQuot.WF wf (hq rfl)
  | mutualDefnDecl vs =>
    exact addMutual.WF wf vs fuel hmode
  | inductDecl lparams nparams types isUnsafe =>
    exact addInductiveDeclaration.WF_preserves wf
      lparams nparams types isUnsafe fuel hmode

/-- `addDecl.WF` with quotient readiness assumed only for `quotDecl`, the one form whose
abstract rule needs it. This is the form a replay from the empty environment uses, since `Eq`
does not exist before the prelude declares it. -/
theorem addDecl.WF_quotReadyAt {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration)
    (hq : decl = .quotDecl → ∀ safety, (ves.venv safety).QuotReady) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) :=
  addDecl.WF_quotReadyAt_fuel wf decl hq {} fun _ => trivial

/-- `addDecl.WF` in either cache mode. In the global mode the hypothesis `hmode` is canonical
`Eq` at every safety level, from which the mode's `GlobalCacheLicense` gives the strengthening the
verification of global caches needs. -/
theorem addDecl.WF_mode {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hq : ∀ safety, (ves.venv safety).QuotReady)
    (decl : Declaration) (mode : CacheMode)
    (hmode : ∀ safety, mode.Sound (ves.venv safety)) :
    (addDecl env decl (check := true) (fuel := { cacheMode := mode })).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) :=
  addDecl.WF_quotReadyAt_fuel wf decl (fun _ => hq) _ hmode

/-- Successful checked addition of a declaration preserves the invariant and extends every
safety-indexed abstract environment. Quotient initialization needs the abstract `Eq` at every
safety level (`hq`). This is `addDecl.WF_mode` in the default, scoped cache mode. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hq : ∀ safety, (ves.venv safety).QuotReady)
    (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) :=
  addDecl.WF_mode wf hq decl .scoped fun _ => trivial

/-! ### The empty environment -/

theorem _root_.Lean.Kernel.Environment.empty_find? (m : Name) (s : Bool) (n : Name) :
    (Kernel.Environment.empty m s).find? n = none := by
  change ({ stage₁ := s } : ConstMap).find?' n = none
  rw [(SMap.WF.empty_stage s).find?'_eq_find?]; simp

/-- The model of the empty environment: the empty abstract environment at every safety level. -/
def VEnvs.empty : VEnvs := ⟨fun _ => .empty⟩

theorem VEnv.HasPrimitives.empty : VEnv.empty.HasPrimitives := by
  intro p _
  rcases p with ⟨n, spec⟩
  cases spec <;> simp [PrimSpec.Holds, VEnv.ReflectsNatNat, VEnv.ReflectsNatNatNat,
    VEnv.ReflectsNatNatBool, VEnv.ReflectsNatBitwise, VEnv.contains, VEnv.empty]

/-- **Base case.** The empty environment that a replay starts from (`Kernel.Environment.empty`,
in either stage) satisfies the invariant; every field but the translation is vacuous. -/
theorem VEnvs.WF.empty (m : Name) (s : Bool) :
    VEnvs.empty.WF (Kernel.Environment.empty m s) where
  tr := .empty
  hasPrimitives := VEnv.HasPrimitives.empty
  safePrimitives h := by simp [Kernel.Environment.empty_find?] at h
  blocks := .empty (by simp [Kernel.Environment.empty_find?])
  mono _ := VEnv.LE.rfl

/-! ### Canonical equality -/

/-- Canonical equality (`VEnv.HasCanonicalEq`) at every safety level. -/
def VEnvs.HasCanonicalEq (ves : VEnvs) : Prop :=
  ∀ safety, (ves.venv safety).HasCanonicalEq

theorem VEnvs.HasCanonicalEq.mono {ves ves' : VEnvs} (h : ves.HasCanonicalEq)
    (hle : ∀ safety, ves.venv safety ≤ ves'.venv safety) : ves'.HasCanonicalEq :=
  fun safety => (h safety).mono (hle safety)

/-- With canonical `Eq` every cache mode is sound: the scoped mode needs nothing, the global
mode needs exactly canonical `Eq` (`CacheMode.Sound`). -/
theorem CacheMode.sound_of_canonicalEq (mode : CacheMode) {venv : VEnv}
    (heq : venv.HasCanonicalEq) : mode.Sound venv := by
  cases mode <;> [trivial; exact heq]

/-- The top-level preservation theorem in the canonical-`Eq` formulation, for either cache mode
of the checker (`CacheMode`). Its hypotheses are the well-formedness of the current environment
(`VEnvs.WF`) and canonical equality at every safety level; the output environment again satisfies
`VEnvs.WF`. In the scoped mode (the default) the checker restores its caches when a binder is
closed, so no strengthening is needed. In the global mode the caches are kept across binders, as
in the C++ kernel, and the verification moves cached facts out of binders with the strengthening
that the mode's `GlobalCacheLicense` provides for the environment, which has canonical `Eq`. The
constructor telescope certificates cover the non-dependent fields walked by projection inference
in both modes. Canonical equality is otherwise used only for quotient initialization, whose
abstract rule types `Quot.lift` against `Eq` at every safety level
(`VEnv.HasCanonicalEq.quotReady`). -/
theorem addDecl.WF_of_canonicalEq_mode {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq) (decl : Declaration) (mode : CacheMode) :
    (addDecl env decl (check := true) (fuel := { cacheMode := mode })).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  addDecl.WF_mode wf (fun safety => (heq safety).quotReady) decl mode
    fun safety => mode.sound_of_canonicalEq (heq safety)

/-- The top-level preservation theorem in the canonical-`Eq` formulation: `WF_of_canonicalEq_mode`
in the default, scoped cache mode, in which the checker restores its caches when a binder is
closed, so no strengthening is needed. -/
theorem addDecl.WF_of_canonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq) (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  addDecl.WF_of_canonicalEq_mode wf heq decl .scoped

/-- Iterable form of `addDecl.WF_of_canonicalEq_mode`. -/
theorem addDecl.WFHasCanonicalEq_mode {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ves.HasCanonicalEq) (decl : Declaration) (mode : CacheMode) :
    (addDecl env decl (check := true) (fuel := { cacheMode := mode })).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ves'.HasCanonicalEq ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  (addDecl.WF_of_canonicalEq_mode wf heq decl mode).mono fun _ ⟨ves', wf', hle⟩ =>
    ⟨ves', wf', heq.mono hle, hle⟩

/-- Iterable form of `addDecl.WF_of_canonicalEq`: `VEnvs.WF` and canonical equality are
preserved by the output environments, so the theorem applies again to the next declaration of a
replay. -/
theorem addDecl.WFHasCanonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ves.HasCanonicalEq) (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ves'.HasCanonicalEq ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  (addDecl.WF_of_canonicalEq wf heq decl).mono fun _ ⟨ves', wf', hle⟩ =>
    ⟨ves', wf', heq.mono hle, hle⟩
