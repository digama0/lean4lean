import Lean4Lean.Verify.Environment.Checker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem TrEnv.exists_addConst (H : TrEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) : ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci => obtain ⟨ci, hci, _⟩ := H.find?_iff.2 ⟨ci, hfind⟩; cases hn ▸ hci

theorem TrEnv'.no_inductInfo (H : TrEnv' .unsafe C Q venv) :
    C.find? name ≠ some (.inductInfo info) := by
  induction H with
  | empty => simp [SMap.find?]
  | ignore hn hhidden H ih =>
    rename_i C' Q' env' ci
    exact False.elim <| hhidden (by cases ci.safety <;> rfl)
  | «axiom» _ _ _ _ H ih => rw [H.map_wf.find?_insert]; split <;> [simp; exact ih]
  | defn _ _ _ _ H ih => rw [H.map_wf.find?_insert]; split <;> [simp; exact ih]
  | thm _ _ _ _ _ H ih => rw [H.map_wf.find?_insert]; split <;> [simp; exact ih]
  | «opaque» _ _ _ _ H ih => rw [H.map_wf.find?_insert]; split <;> [simp; exact ih]
  | quot hready hadd H ih =>
    obtain ⟨lp₁, ty₁, env₁, _, hn₁, _,
      lp₂, ty₂, env₂, _, hn₂, _,
      lp₃, ty₃, env₃, _, hn₃, _,
      lp₄, ty₄, env₄, _, hn₄, _, rfl, _⟩ := hadd
    have wf₀ := H.map_wf
    have wf₁ := wf₀.insert ``Quot
      (.quotInfo { name := ``Quot, kind := .type, levelParams := lp₁, type := ty₁ }) hn₁
    have wf₂ := wf₁.insert ``Quot.mk
      (.quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := lp₂, type := ty₂ }) hn₂
    have wf₃ := wf₂.insert ``Quot.lift
      (.quotInfo { name := ``Quot.lift, kind := .lift, levelParams := lp₃, type := ty₃ }) hn₃
    rw [wf₃.find?_insert]; split <;> [simp; skip]
    rw [wf₂.find?_insert]; split <;> [simp; skip]
    rw [wf₁.find?_insert]; split <;> [simp; skip]
    rw [wf₀.find?_insert]; split <;> [simp; exact ih]
  | induct _ hadd => cases hadd

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addConst name ci = some env₁') (h₂ : env₂.addConst name ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  refine { constants {n a} := ?_, defeqs := H.defeqs }
  dsimp; split <;> [exact id; exact H.constants]

theorem VEnv.addDefEq_mono {env₁ env₂ : VEnv} (H : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df where
  constants := H.constants
  defeqs := by rintro d (rfl | hd) <;> [exact .inl rfl; exact .inr (H.defeqs hd)]

theorem VEnv.addConst_eq_of_ne
    {env env' : VEnv}
    (hadd : env.addConst name ci = some env') (hne : name ≠ n) :
    env'.constants n = env.constants n := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  simp [hne]

theorem VEnv.HasPrimitives.addConst {env env' : VEnv} (H : env.HasPrimitives)
    (hname : Environment.primitives.contains name = false)
    (hadd : env.addConst name ci = some env') : env'.HasPrimitives := by
  have le := VEnv.addConst_le hadd
  have same {n} (hp : Environment.primitives.contains n = true) :
      env'.constants n = env.constants n :=
    VEnv.addConst_eq_of_ne hadd fun h => by subst h; simp_all
  have oldContains {n} (hp : Environment.primitives.contains n = true) :
      env'.contains n → env.contains n := fun ⟨ci, hci⟩ => ⟨ci, (same hp) ▸ hci⟩
  have newContains {n} : env.contains n → env'.contains n := fun ⟨ci, hci⟩ => ⟨ci, le.constants hci⟩
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {n} : n ∈ prims → Environment.primitives.contains n := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  simp only [List.mem_cons, prims] at hprims
  constructor
  · intro h
    let ⟨h1, h2⟩ := H.bool (oldContains (hprims (by simp)) h)
    exact ⟨newContains h1, newContains h2⟩
  · intro ci h; apply H.boolFalse; rwa [← same (hprims (by simp))]
  · intro ci h; apply H.boolTrue; rwa [← same (hprims (by simp))]
  · intro h
    let ⟨h1, h2⟩ := H.nat (oldContains (hprims (by simp)) h)
    exact ⟨newContains h1, newContains h2⟩
  · intro ci h; apply H.natZero; rwa [← same (hprims (by simp))]
  · intro ci h; apply H.natSucc; rwa [← same (hprims (by simp))]
  · intro h a b; exact (H.natAdd (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natSub (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natMul (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natPow (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natGcd (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natMod (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natDiv (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natBEq (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natBLE (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natLAnd (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natLOr (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natXor (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natShiftLeft (oldContains (hprims (by simp)) h) a b).mono le
  · intro h a b; exact (H.natShiftRight (oldContains (hprims (by simp)) h) a b).mono le
  · intro ci h; apply H.charOfNat; rwa [← same (hprims (by simp))]
  · intro ci h
    obtain ⟨rfl, h2, h3⟩ := H.stringOfList (by rwa [← same (hprims (by simp))])
    exact ⟨rfl, h2.mono le, h3.mono le⟩

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} (H : env.HasPrimitives) :
    (env.addDefEq df).HasPrimitives :=
  { H with
    natAdd h a b := (H.natAdd h a b).mono VEnv.addDefEq_le
    natSub h a b := (H.natSub h a b).mono VEnv.addDefEq_le
    natMul h a b := (H.natMul h a b).mono VEnv.addDefEq_le
    natPow h a b := (H.natPow h a b).mono VEnv.addDefEq_le
    natGcd h a b := (H.natGcd h a b).mono VEnv.addDefEq_le
    natMod h a b := (H.natMod h a b).mono VEnv.addDefEq_le
    natDiv h a b := (H.natDiv h a b).mono VEnv.addDefEq_le
    natBEq h a b := (H.natBEq h a b).mono VEnv.addDefEq_le
    natBLE h a b := (H.natBLE h a b).mono VEnv.addDefEq_le
    natLAnd h a b := (H.natLAnd h a b).mono VEnv.addDefEq_le
    natLOr h a b := (H.natLOr h a b).mono VEnv.addDefEq_le
    natXor h a b := (H.natXor h a b).mono VEnv.addDefEq_le
    natShiftLeft h a b := (H.natShiftLeft h a b).mono VEnv.addDefEq_le
    natShiftRight h a b := (H.natShiftRight h a b).mono VEnv.addDefEq_le
    stringOfList h :=
      let ⟨h1, h2, h3⟩ := H.stringOfList h
      ⟨h1, h2.mono VEnv.addDefEq_le, h3.mono VEnv.addDefEq_le⟩ }

theorem VEnvs.WF.safePrimitives_add {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] := by
  have mapWF := (wf.tr (safety := .safe)).map_wf
  have hnone : env.constants.find? ci.name = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hfresh
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = some ci' at hfind
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert] at hfind
  split at hfind
  · cases hfind; cases LawfulBEq.eq_of_beq ‹_›; exact hok hp
  · refine wf.safePrimitives ?_ hp
    rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]

theorem addConstCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (hprim : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (preserves : ∀ safety venv', safety ≤ ci.safety →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      (ves.venv safety).HasPrimitives → venv'.HasPrimitives)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧
      ∀ safety, (ves.venv safety).AddConst safety ci ci'.toVConstant (ves'.venv safety) := by
  have hnMap : env.constants.find? ci.name = none := by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hn
  have visible_tr (safety) (hvisible : safety ≤ ci.safety) :
      TrConstant safety (ves.venv safety) ci ci'.toVConstant :=
    (htr.1.sf_mono (visible_le safety hvisible)).mono (wf.mono (visible_le safety hvisible))
  have visible_wf (safety) (hvisible : safety ≤ ci.safety) :
      ci'.toVConstant.WF (ves.venv safety) :=
    hci.mono (wf.mono (visible_le safety hvisible))
  have hves' safety : ∃ venv', (ves.venv safety).AddConst safety ci ci'.toVConstant venv' := by
    unfold VEnv.AddConst; split <;> [rename_i hvisible; exact ⟨ves.venv safety, rfl⟩]
    have ⟨venv', hadd⟩ := (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
    exact ⟨venv', visible_tr safety hvisible, visible_wf safety hvisible, hadd⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hves'
  have hadd (safety) (hvisible : safety ≤ ci.safety) :
      (ves.venv safety).addConst ci.name ci'.toVConstant = some (ves'.venv safety) := by
    have h := hves' safety; unfold VEnv.AddConst at h; rw [if_pos hvisible] at h; exact h.2.2
  have hsame (safety) (hvisible : ¬ safety ≤ ci.safety) : ves'.venv safety = ves.venv safety := by
    have h := hves' safety; unfold VEnv.AddConst at h; rwa [if_neg hvisible] at h
  refine ⟨ves', ?_, hves'⟩
  exact {
    tr {safety} := by
      by_cases hvisible : safety ≤ ci.safety
      · exact step safety _ (visible_tr safety hvisible) (visible_wf safety hvisible)
          (hadd safety hvisible) (wf.tr (safety := safety))
      · rw [hsame safety hvisible]
        exact TrEnv'.ignore (ci := ci) hnMap hvisible (wf.tr (safety := safety))
    hasPrimitives {safety} := by
      by_cases hvisible : safety ≤ ci.safety
      · exact preserves safety _ hvisible (hadd safety hvisible) (wf.hasPrimitives (safety := safety))
      · rw [hsame safety hvisible]; exact wf.hasPrimitives (safety := safety)
    safePrimitives := wf.safePrimitives_add ci hn hprim
    mono {safety safety'} hle := by
      by_cases hvisible' : safety' ≤ ci.safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        exact VEnv.addConst_mono (wf.mono hle) (hadd safety' hvisible') (hadd safety hvisible)
      rw [hsame safety' hvisible']
      by_cases hvisible : safety ≤ ci.safety
      · exact (wf.mono hle).trans (VEnv.addConst_le (hadd safety hvisible))
      · rw [hsame safety hvisible]; exact wf.mono hle }

theorem addConst.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (hnonprim : Environment.primitives.contains ci.name = false)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧
      ∀ safety, (ves.venv safety).AddConst safety ci ci'.toVConstant (ves'.venv safety) :=
  addConstCore.WF wf ci ci' checkSafety visible_le htr hci hn (by simp_all)
    (fun _ _ _ hadd hp => hp.addConst hnonprim hadd) step

theorem addDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ (ConstantInfo.defnInfo v).safety → safety ≤ checkSafety)
    (htr : TrDefVal checkSafety (ves.venv checkSafety) (.defnInfo v) ci')
    (hci : ci'.WF (ves.venv checkSafety))
    (hn : env.find? v.name = none)
    (hprim : Environment.primitives.contains v.name →
      (ConstantInfo.defnInfo v).safety = .safe ∧ v.levelParams = [])
    (preserves : ∀ safety base,
      safety ≤ (ConstantInfo.defnInfo v).safety →
      (ves.venv safety).addConst v.name ci'.toVConstant = some base →
      (base.addDefEq ci'.toDefEq).HasPrimitives) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety) := by
  have hnMap : env.constants.find? v.name = none := by
    rwa [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
  have visible_tr (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      TrDefVal safety (ves.venv safety) (.defnInfo v) ci' :=
    .mono (wf.mono (visible_le safety hvisible)) <|
      ⟨⟨htr.1.1.sf_mono (visible_le safety hvisible), htr.1.2⟩, htr.2⟩
  have visible_wf safety hvisible := hci.mono (wf.mono (visible_le safety hvisible))
  have hves' safety : ∃ venv', (ves.venv safety).AddDef safety (.defnInfo v) ci' venv' := by
    unfold VEnv.AddDef; split <;> [rename_i hvisible; exact ⟨ves.venv safety, rfl⟩]
    have ⟨base, hadd⟩ := (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
    exact ⟨base.addDefEq ci'.toDefEq,
      base, visible_tr safety hvisible, visible_wf safety hvisible, hadd, rfl⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hves'
  have hbase (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      ∃ base, (ves.venv safety).addConst v.name ci'.toVConstant = some base ∧
        ves'.venv safety = base.addDefEq ci'.toDefEq := by
    have h := hves' safety; unfold VEnv.AddDef at h; rw [if_pos hvisible] at h
    obtain ⟨base, _, _, hadd, heq⟩ := h; exact ⟨base, hadd, heq⟩
  have hsame (safety) (hvisible : ¬ safety ≤ (ConstantInfo.defnInfo v).safety) :
      ves'.venv safety = ves.venv safety := by
    have h := hves' safety; unfold VEnv.AddDef at h; rwa [if_neg hvisible] at h
  refine ⟨ves', ?_, hves'⟩
  refine {
    tr {safety} := by
      change TrEnv' safety (env.constants.insert v.name (.defnInfo v)) env.quotInit _
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        exact heq ▸ TrEnv'.defn (visible_tr safety hvisible)
          (by rwa [← (wf.tr (safety := safety)).map_wf.find?'_eq_find?])
          (visible_wf safety hvisible) hadd (wf.tr (safety := safety))
      · rw [hsame safety hvisible]
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
          TrEnv'.ignore (ci := .defnInfo v) hnMap hvisible (wf.tr (safety := safety))
    hasPrimitives {safety} := by
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        rw [heq]; exact preserves safety base hvisible hadd
      · rw [hsame safety hvisible]; exact wf.hasPrimitives (safety := safety)
    safePrimitives := wf.safePrimitives_add (.defnInfo v) hn hprim
    mono {safety safety'} hle := by
      by_cases hvisible' : safety' ≤ (ConstantInfo.defnInfo v).safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        obtain ⟨base', hadd', heq'⟩ := hbase safety' hvisible'
        obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        rw [heq', heq]
        exact VEnv.addDefEq_mono <| VEnv.addConst_mono (wf.mono hle) hadd' hadd
      rw [hsame safety' hvisible']
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        rw [heq]
        exact (wf.mono hle).trans <| (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
      · rw [hsame safety hvisible]; exact wf.mono hle }
