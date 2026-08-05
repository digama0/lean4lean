import Lean4Lean.Verify.Environment.Checker

namespace Lean4Lean
open Lean4Lean
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
  | mutualDef _ hnd hfr _ _ _ H ih =>
    intro h
    obtain h | ⟨_, _, _, h2⟩ := insertDefs_find? H.map_wf hfr hnd h <;> [exact ih h; cases h2]
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

theorem VEnv.addConsts_mono {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂) :
    ∀ {cis}, env₁.addConsts cis = some env₁' → env₂.addConsts cis = some env₂' → env₁' ≤ env₂'
  | [], h₁, h₂ => by cases h₁; cases h₂; exact H
  | _ :: _, h₁, h₂ => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h₁ h₂
    obtain ⟨_, e₁, h₁⟩ := h₁; obtain ⟨_, e₂, h₂⟩ := h₂
    exact VEnv.addConsts_mono (VEnv.addConst_mono H e₁ e₂) h₁ h₂

theorem VEnv.addDefEqs_mono {env₁ env₂ : VEnv} (H : env₁ ≤ env₂) :
    ∀ {cis}, env₁.addDefEqs cis ≤ env₂.addDefEqs cis
  | [] => H
  | _ :: _ => VEnv.addDefEqs_mono (VEnv.addDefEq_mono H)

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

theorem safePrimitives_add' {env : Environment} (mapWF : env.constants.WF)
    (old : ∀ {n : Name} {ci}, env.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name → ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] := by
  have hnone : env.constants.find? ci.name = none := by
    rw [← mapWF.find?'_eq_find?]; exact hfresh
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = some ci' at hfind
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert] at hfind
  split at hfind
  · cases hfind; cases LawfulBEq.eq_of_beq ‹_›; exact hok hp
  · refine old ?_ hp; rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]

theorem VEnvs.WF.safePrimitives_add {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] :=
  safePrimitives_add' (wf.tr (safety := .safe)).map_wf wf.safePrimitives ci hfresh hok hfind hp

theorem VEnvAt.safePrimitives_add {env : Environment} {venv : VEnv}
    (wf : VEnvAt env safety venv) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] :=
  safePrimitives_add' wf.tr.map_wf wf.safePrimitives ci hfresh hok hfind hp

theorem VEnv.HasPrimitives.addConsts {env env' : VEnv} : ∀ {cis : List VDefVal},
    env.HasPrimitives → (∀ ci ∈ cis, Environment.primitives.contains ci.name = false) →
    env.addConsts cis = some env' → env'.HasPrimitives
  | [], H, _, e => by cases e; exact H
  | _ :: _, H, hn, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    exact addConsts (H.addConst (hn _ (.head _)) h1) (fun c hc => hn c (.tail _ hc)) h2

theorem VEnv.HasPrimitives.addDefEqs {env : VEnv} : ∀ {cis : List VDefVal},
    env.HasPrimitives → (env.addDefEqs cis).HasPrimitives
  | [], H => H
  | _ :: cis, H => addDefEqs (cis := cis) H.addDefEq

theorem TrEnv.constants_eq_none (H : TrEnv safety env venv) (hn : env.find? name = none) :
    venv.constants name = none := by
  cases hfind : venv.constants name with
  | none => rfl
  | some ci => obtain ⟨ci, hci, _⟩ := H.find?_iff.2 ⟨ci, hfind⟩; cases hn ▸ hci

theorem TrEnv.exists_addConsts (H : TrEnv safety env venv) {cis : List VDefVal}
    (hfresh : ∀ ci ∈ cis, env.find? ci.name = none)
    (hnd : (cis.map (·.name)).Nodup) : ∃ venv', venv.addConsts cis = some venv' :=
  VEnv.exists_addConsts (fun ci hci => H.constants_eq_none (hfresh ci hci)) hnd

theorem insertDefs_wf : ∀ {cis : List DefinitionVal} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup → (insertDefs C cis).WF
  | [], _, hC, _, _ => hC
  | d :: ds, C, hC, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine insertDefs_wf (cis := ds) (hC.insert _ _ (hfr _ (.head _))) (fun e he => ?_) hnd.2
    rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

theorem Environment.constants_addDefs : ∀ {vs : List DefinitionVal} {env : Environment},
    (vs.foldl (fun e v => Lean.Kernel.Environment.add e (.defnInfo v)) env).constants =
    insertDefs env.constants vs
  | [], _ => rfl
  | v :: vs, env => Environment.constants_addDefs (vs := vs) (env := env.add (.defnInfo v))

theorem VEnvs.WF.safePrimitives_addDefs {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) {vs : List DefinitionVal}
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnd : (vs.map (·.name)).Nodup)
    (hnonprim : ∀ v ∈ vs, Environment.primitives.contains v.name = false)
    (hfind : (vs.foldl (fun e v => e.add (.defnInfo v)) env).find? n = some ci)
    (hp : Environment.primitives.contains n) : ci.safety = .safe ∧ ci.levelParams = [] := by
  have mapWF := (wf.tr (safety := .safe)).map_wf
  have hfr : ∀ d ∈ vs, env.constants.find? d.name = none := fun d hd => by
    rw [← mapWF.find?'_eq_find?]; exact hfresh d hd
  rw [Kernel.Environment.find?, Environment.constants_addDefs,
    (insertDefs_wf mapWF hfr hnd).find?'_eq_find?] at hfind
  rcases insertDefs_find? mapWF hfr hnd hfind with h | ⟨d, hd, rfl, rfl⟩
  · exact wf.safePrimitives (by rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]) hp
  · exact absurd hp (by simp [hnonprim d hd])

theorem Environment.quotInit_addDefs : ∀ {vs : List DefinitionVal} {env : Environment},
    (vs.foldl (fun e v => Lean.Kernel.Environment.add e (.defnInfo v)) env).quotInit =
    env.quotInit
  | [], _ => rfl
  | _ :: vs, _ => quotInit_addDefs (vs := vs)

/-- A block of definitions that is invisible at `safety` extends the constant map without
touching the model, one `TrEnv'.ignore` per member. -/
theorem TrEnv'.ignoreDefs : ∀ {vs : List DefinitionVal} {C : ConstMap},
    (∀ v ∈ vs, ¬ safety ≤ (ConstantInfo.defnInfo v).safety) →
    (∀ v ∈ vs, C.find? v.name = none) → (vs.map (·.name)).Nodup →
    TrEnv' safety C Q venv → TrEnv' safety (insertDefs C vs) Q venv
  | [], _, _, _, _, H => H
  | d :: ds, C, hvis, hfr, hnd, H => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have H' := TrEnv'.ignore (ci := .defnInfo d) (hfr _ (.head _)) (hvis _ (.head _)) H
    show TrEnv' safety (insertDefs (SMap.insert C d.name (.defnInfo d)) ds) Q _
    refine TrEnv'.ignoreDefs (fun e he => hvis e (.tail _ he)) (fun e he => ?_) hnd.2 H'
    rw [H.map_wf.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

theorem Environment.find?_add_of_ne {env : Environment} (mapWF : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none) {n : Name}
    (hne : ci.name ≠ n) (h : env.find? n = none) : (env.add ci).find? n = none := by
  have hnone : env.constants.find? ci.name = none := by rwa [← mapWF.find?'_eq_find?]
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = none
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert, if_neg (by simpa using hne)]
  rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?] at h

/-- Data produced by `addMutual`'s header loop for one block member. -/
def TrMutualHeader (bs : DefinitionSafety) (venv : VEnv) (env : Environment)
    (v : DefinitionVal) (ci : VDefVal) : Prop :=
  TrConstVal bs venv (.defnInfo v) ci.toVConstVal ∧
  ci.toVConstant.WF venv ∧ env.find? v.name = none ∧
  Environment.primitives.contains v.name = false

/-- A model of the temporary environment in which a mutual block's bodies are checked: every
member has been added as an axiom, so a body may refer to any member of the block (including
itself) but cannot delta-unfold it. -/
theorem VEnvAt.addAxioms {env : Environment} {venv : VEnv} {bs : DefinitionSafety}
    (hsf : bs ≤ (if bs == .unsafe then DefinitionSafety.unsafe else .safe)) :
    ∀ {vs : List DefinitionVal} {cis : List VDefVal} {venv' : VEnv},
      VEnvAt env bs venv →
      List.Forall₂ (TrMutualHeader bs venv env) vs cis →
      (vs.map (·.name)).Nodup →
      venv.addConsts cis = some venv' →
      VEnvAt (vs.foldl (fun e v => e.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) env)
        bs venv'
  | [], _, _, wf, .nil, _, e => by cases e; exact wf
  | v :: vs, ci :: cis, venv', wf, .cons hd tl, hnd, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h₁, h₂⟩ := e
    have hn : v.name = ci.name := hd.1.2
    have h₁' : venv.addConst v.name ci.toVConstant = some venv₁ := by rw [hn]; exact h₁
    have hle := VEnv.addConst_le h₁'
    have hax : (ConstantInfo.axiomInfo { v with isUnsafe := bs == .unsafe }).name = v.name := rfl
    have wf₁ : VEnvAt (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) bs venv₁ :=
      { tr := TrEnv'.axiom (ci := { v with isUnsafe := bs == .unsafe }) (ci' := ci.toVConstant)
          ⟨hsf, hd.1.1.2.1, hd.1.1.2.2⟩
          (by rw [← wf.tr.map_wf.find?'_eq_find?]; exact hd.2.2.1) hd.2.1 h₁' wf.tr
        hasPrimitives := wf.hasPrimitives.addConst hd.2.2.2 h₁'
        safePrimitives := wf.safePrimitives_add _ (hax ▸ hd.2.2.1)
          (by rw [hax]; simp [hd.2.2.2]) }
    show VEnvAt (vs.foldl (fun e v => e.add (.axiomInfo { v with isUnsafe := bs == .unsafe }))
      (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe }))) bs venv'
    refine VEnvAt.addAxioms hsf wf₁ ?_ hnd.2 h₂
    refine tl.and_mem.imp fun w cj h => ?_
    obtain ⟨h, hw, -⟩ := h
    have hne : v.name ≠ w.name := fun hh => hnd.1 (List.mem_map.2 ⟨w, hw, hh.symm⟩)
    exact ⟨⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.mono hle⟩, h.1.2⟩, h.2.1.mono hle,
      Environment.find?_add_of_ne wf.tr.map_wf _ (hax ▸ hd.2.2.1) (hax ▸ hne) h.2.2.1,
      h.2.2.2⟩

/-- Add a whole mutual block. The headers were checked in `env`, the bodies in the temporary
environment holding the entire block, which is `base` on the model side; `TrEnv'.mutualDef`
consumes exactly that split.

Like `addUnsafeDef.WF` this cannot conclude `VEnv.AddDef` for the members: the bodies may
refer to each other, so they do not translate before the block is added. -/
theorem addMutualBlock.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (bs : DefinitionSafety) (vs : List DefinitionVal) (cis : List VDefVal) (base : VEnv)
    (hbs : ∀ v ∈ vs, v.safety = bs)
    (hnd : (vs.map (·.name)).Nodup)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnonprim : ∀ v ∈ vs, Environment.primitives.contains v.name = false)
    (hwfc : ∀ ci ∈ cis, ci.toVConstant.WF (ves.venv bs))
    (hbase : (ves.venv bs).addConsts cis = some base)
    (htr : TrDefBlock bs (ves.venv bs) base vs cis)
    (hci : ∀ ci ∈ cis, ci.WF base) :
    ∃ ves' : VEnvs, ves'.WF (vs.foldl (fun e v => e.add (.defnInfo v)) env) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hname := htr.imp (fun _ _ h => h.1.2)
  have hmapeq : vs.map (·.name) = cis.map (·.name) := by
    rwa [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  have hndCis : (cis.map (·.name)).Nodup := hmapeq ▸ hnd
  have hpull {P : Name → Prop} (H : ∀ v ∈ vs, P v.name) : ∀ ci ∈ cis, P ci.name := by
    intro ci hc
    obtain ⟨v, hv, hn⟩ := hname.forall_exists_r ci hc
    exact hn ▸ H v hv
  have hfreshCis := hpull (P := fun n => env.find? n = none) hfresh
  have hnonprimCis := hpull (P := fun n => Environment.primitives.contains n = false) hnonprim
  have hfreshMap : ∀ v ∈ vs, env.constants.find? v.name = none := fun v hv => by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]; exact hfresh v hv
  have hvis_iff (sf) (hv : sf ≤ bs) (v) (hmem : v ∈ vs) :
      sf ≤ (ConstantInfo.defnInfo v).safety := by
    rw [ConstantInfo.defnInfo_safety, hbs v hmem]; exact hv
  -- the model at each visible safety level
  have hves' sf : ∃ venv',
      if sf ≤ bs then ∃ b, (ves.venv sf).addConsts cis = some b ∧ venv' = b.addDefEqs cis
      else venv' = ves.venv sf := by
    split <;> [skip; exact ⟨_, rfl⟩]
    obtain ⟨b, hb⟩ := (wf.tr (safety := sf)).exists_addConsts hfreshCis hndCis
    exact ⟨_, b, hb, rfl⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hves'
  have hbaseSf (sf) (hv : sf ≤ bs) : ∃ b, (ves.venv sf).addConsts cis = some b ∧
      ves'.venv sf = b.addDefEqs cis := by
    have h := hves' sf; rw [if_pos hv] at h; exact h
  have hsame (sf) (hv : ¬ sf ≤ bs) : ves'.venv sf = ves.venv sf := by
    have h := hves' sf; rwa [if_neg hv] at h
  refine ⟨ves', ?_, fun sf => by
    by_cases hv : sf ≤ bs
    · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
      exact heq ▸ (VEnv.addConsts_le hb).trans VEnv.addDefEqs_le
    · rw [hsame sf hv]; exact VEnv.LE.rfl⟩
  exact {
    tr {sf} := by
      show TrEnv sf _ _
      unfold TrEnv
      rw [Environment.constants_addDefs, Environment.quotInit_addDefs]
      by_cases hv : sf ≤ bs
      · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
        have hmono : ves.venv bs ≤ ves.venv sf := wf.mono hv
        have hbmono : base ≤ b := VEnv.addConsts_mono hmono hbase hb
        refine heq ▸ TrEnv'.mutualDef (env := ves.venv sf) (env' := b) ?_ hnd hfreshMap
          (fun ci hc => (hwfc ci hc).mono hmono) hb
          (fun ci hc => (hci ci hc).mono hbmono) (wf.tr (safety := sf))
        exact htr.imp fun _ _ h => ⟨⟨(h.1.1.sf_mono hv).mono hmono, h.1.2⟩, h.2.mono hbmono⟩
      · rw [hsame sf hv]
        exact TrEnv'.ignoreDefs
          (fun v hmem => fun h => hv (by rwa [ConstantInfo.defnInfo_safety, hbs v hmem] at h))
          hfreshMap hnd (wf.tr (safety := sf))
    hasPrimitives {sf} := by
      by_cases hv : sf ≤ bs
      · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
        exact heq ▸ ((wf.hasPrimitives (safety := sf)).addConsts hnonprimCis hb).addDefEqs
      · rw [hsame sf hv]; exact wf.hasPrimitives
    safePrimitives := wf.safePrimitives_addDefs hfresh hnd hnonprim
    mono {sf sf'} hle := by
      by_cases hv' : sf' ≤ bs
      · have hv : sf ≤ bs := DefinitionSafety.le_trans hle hv'
        obtain ⟨b', hb', heq'⟩ := hbaseSf sf' hv'
        obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
        rw [heq', heq]
        exact VEnv.addDefEqs_mono (VEnv.addConsts_mono (wf.mono hle) hb' hb)
      · rw [hsame sf' hv']
        by_cases hv : sf ≤ bs
        · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
          rw [heq]
          exact (wf.mono hle).trans ((VEnv.addConsts_le hb).trans VEnv.addDefEqs_le)
        · rw [hsame sf hv]; exact wf.mono hle }

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

/-- The unsafe branch of `addDefinition`. The constant is added to the environment as an axiom
*before* its body is checked, so the body is translated in the extended environment `base` and
the whole step is justified by `TrEnv'.mutualDef` with a one-element block.

Unlike `addDef.WF` this cannot conclude `VEnv.AddDef`: that would require the body to translate
in the environment *before* the addition, which is false for a recursive unsafe definition. -/
theorem addUnsafeDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal) (base : VEnv)
    (hunsafe : v.safety = .unsafe)
    (htr : TrConstVal .unsafe (ves.venv .unsafe) (.defnInfo v) ci'.toVConstVal)
    (hwfc : ci'.toVConstant.WF (ves.venv .unsafe))
    (hadd : (ves.venv .unsafe).addConst v.name ci'.toVConstant = some base)
    (hvalue : TrExprS base v.levelParams [] v.value ci'.value)
    (hci : ci'.WF base)
    (hn : env.find? v.name = none)
    (hnonprim : Environment.primitives.contains v.name = false) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hnMap : env.constants.find? v.name = none := by
    rwa [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
  have hle : ves.venv .unsafe ≤ base.addDefEq ci'.toDefEq :=
    (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hname : (ConstantInfo.defnInfo v).name = ci'.name := htr.2
  have hadd' : (ves.venv .unsafe).addConsts [ci'] = some base := by
    simp [VEnv.addConsts, ← hname]; exact hadd
  refine ⟨⟨fun | .unsafe => base.addDefEq ci'.toDefEq | sf => ves.venv sf⟩, ?_,
    by rintro ⟨⟩ <;> first | exact hle | exact .rfl⟩
  exact {
    tr {safety} := by
      change TrEnv' safety (env.constants.insert v.name (.defnInfo v)) env.quotInit _
      match safety with
      | .unsafe =>
        have := TrEnv'.mutualDef (safety := .unsafe) (cis := [v]) (cis' := [ci'])
          (C := env.constants) (Q := env.quotInit) (env := ves.venv .unsafe) (env' := base)
          (.cons ⟨htr, hvalue⟩ .nil) (by simp) (by simpa using hnMap) (by simpa using hwfc)
          hadd' (by simpa using hci) wf.tr
        simpa [insertDefs, VEnv.addDefEqs] using this
      | .safe | .partial =>
        refine TrEnv'.ignore (ci := .defnInfo v) hnMap ?_ wf.tr
        rw [ConstantInfo.defnInfo_safety, hunsafe]; decide
    hasPrimitives {safety} :=
      match safety with
      | .unsafe => ((wf.hasPrimitives (safety := .unsafe)).addConst hnonprim hadd).addDefEq
      | .safe | .partial => wf.hasPrimitives
    safePrimitives := wf.safePrimitives_add (.defnInfo v) hn
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, hnonprim])
    mono {safety safety'} hsf :=
      match safety, safety' with
      | .unsafe, .unsafe => .rfl
      | .unsafe, .safe | .unsafe, .partial => (wf.mono hsf).trans hle
      | .safe, .unsafe | .partial, .unsafe => absurd hsf (by decide)
      | .safe, .safe | .safe, .partial | .partial, .safe | .partial, .partial => wf.mono hsf }
