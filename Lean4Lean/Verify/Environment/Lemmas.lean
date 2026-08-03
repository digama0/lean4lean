import Lean4Lean.Std.SMap
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem VEnv.addConst_constants_of_ne {env env' : VEnv}
    (h : env.addConst n ci = some env') (hne : n ≠ m) :
    env'.constants m = env.constants m := by
  unfold VEnv.addConst at h
  split at h <;> cases h
  simp [hne]

private theorem VEnv.addMutualHeaders_le {env env' : VEnv} {vs : List VDefVal}
    (h : env.addMutualHeaders vs = some env') : env ≤ env' := by
  induction vs generalizing env with
  | nil =>
    simp [VEnv.addMutualHeaders] at h
    subst env'
    exact VEnv.LE.rfl
  | cons v vs ih =>
    cases hhead : env.addConst v.name v.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hhead] at h
    | some next =>
      simp [VEnv.addMutualHeaders, hhead] at h
      exact (VEnv.addConst_le hhead).trans (ih h)

private theorem VEnv.addMutualDefEqs_le {env : VEnv} {vs : List VDefVal} :
    env ≤ env.addMutualDefEqs vs := by
  induction vs generalizing env with
  | nil => exact VEnv.LE.rfl
  | cons v vs ih =>
    exact VEnv.addDefEq_le.trans (ih (env := env.addDefEq v.toDefEq))

private theorem VEnv.addMutualDefEqs_mem {env : VEnv} {vs : List VDefVal}
    {v : VDefVal} (h : v ∈ vs) :
    (env.addMutualDefEqs vs).defeqs v.toDefEq := by
  induction vs generalizing env with
  | nil => simp at h
  | cons head tail ih =>
    simp only [VEnv.addMutualDefEqs, List.foldl_cons]
    simp only [List.mem_cons] at h
    rcases h with hEq | h
    · subst v
      exact (VEnv.addMutualDefEqs_le (env := env.addDefEq head.toDefEq)
        (vs := tail)).defeqs VEnv.addDefEq_self
    · exact ih (env := env.addDefEq head.toDefEq) h

private theorem List.Forall₂.and {R S : α → β → Prop} {xs : List α} {ys : List β}
    (hR : List.Forall₂ R xs ys) (hS : List.Forall₂ S xs ys) :
    List.Forall₂ (fun x y => R x y ∧ S x y) xs ys := by
  induction hR with
  | nil => cases hS; exact .nil
  | cons hR hRs ih =>
    cases hS with
    | cons hS hSs => exact .cons ⟨hR, hS⟩ (ih hSs)

private theorem ConstMap.find?_insert_cases {C : ConstMap} {n name : Name}
    {ci ci' : ConstantInfo} (hC : C.WF)
    (h : (C.insert n ci').find? name = some ci) :
    C.find? name = some ci ∨ n = name ∧ ci' = ci := by
  rw [hC.find?_insert] at h
  simp at h ⊢
  split at h <;> simp_all

private theorem ConstMap.find?_addMutualDefinitions
    {C : ConstMap} {R : DefinitionVal → VDefVal → Prop}
    {vs : List DefinitionVal} {vs' : List VDefVal} {name : Name} {ci : ConstantInfo}
    (hC : C.WF)
    (hrel : List.Forall₂ R vs vs')
    (hfresh : ConstMap.MutualFresh C vs)
    (h : (ConstMap.addMutualDefinitions C vs).find? name = some ci) :
    C.find? name = some ci ∨
      ∃ v v', v ∈ vs ∧ v' ∈ vs' ∧ R v v' ∧
        v.name = name ∧ ci = .defnInfo v := by
  induction hrel generalizing C with
  | nil =>
    left
    simpa [ConstMap.addMutualDefinitions] using h
  | @cons v v' vs vs' hR hRs ih =>
    rcases hfresh with ⟨hfresh, hnodup⟩
    have hnone := hfresh v (by simp)
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hC' := hC.insert v.name (.defnInfo v) hnone
    have hfresh' : ConstMap.MutualFresh (C.insert v.name (.defnInfo v)) vs := by
      refine ⟨?_, hnodupPair.2⟩
      intro w hw
      rw [hC.find?_insert]
      split
      · rename_i heq
        have hmem : w.name ∈ vs.map (fun x => x.name) :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
      · exact hfresh w (by simp [hw])
    have h' : (ConstMap.addMutualDefinitions (C.insert v.name (.defnInfo v)) vs).find? name =
        some ci := by
      simpa [ConstMap.addMutualDefinitions] using h
    rcases ih hC' hfresh' h' with hold | ⟨w, w', hw, hw', hRw, hn, hci⟩
    · rcases ConstMap.find?_insert_cases hC hold with hold | ⟨hn, hci⟩
      · exact .inl hold
      · exact .inr ⟨v, v', by simp, by simp, hR, hn, hci.symm⟩
    · exact .inr ⟨w, w', by simp [hw], by simp [hw'], hRw, hn, hci⟩

private theorem ConstMap.find?_addMutualOpaqueHeaders
    {C : ConstMap} {vs : List DefinitionVal} {name : Name} {ci : ConstantInfo}
    (hC : C.WF) (hfresh : ConstMap.MutualFresh C vs)
    (h : (ConstMap.addMutualOpaqueHeaders C vs).find? name = some ci) :
    C.find? name = some ci ∨
      ∃ v, v ∈ vs ∧ v.name = name ∧ ci = .opaqueInfo (mutualOpaqueHeader v) := by
  induction vs generalizing C with
  | nil =>
    left
    simpa [ConstMap.addMutualOpaqueHeaders] using h
  | cons v vs ih =>
    rcases hfresh with ⟨hfresh, hnodup⟩
    have hnone := hfresh v (by simp)
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    have hC' := hC.insert v.name (.opaqueInfo (mutualOpaqueHeader v)) hnone
    have hfresh' : ConstMap.MutualFresh
        (C.insert v.name (.opaqueInfo (mutualOpaqueHeader v))) vs := by
      refine ⟨?_, hnodupPair.2⟩
      intro w hw
      rw [hC.find?_insert]
      split
      · rename_i heq
        have hmem : w.name ∈ vs.map (fun x => x.name) :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
      · exact hfresh w (by simp [hw])
    have h' : (ConstMap.addMutualOpaqueHeaders
        (C.insert v.name (.opaqueInfo (mutualOpaqueHeader v))) vs).find? name = some ci := by
      simpa [ConstMap.addMutualOpaqueHeaders] using h
    rcases ih hC' hfresh' h' with hold | ⟨w, hw, hn, hci⟩
    · rcases ConstMap.find?_insert_cases hC hold with hold | ⟨hn, hci⟩
      · exact .inl hold
      · exact .inr ⟨v, by simp, hn, hci.symm⟩
    · exact .inr ⟨w, by simp [hw], hn, hci⟩

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

theorem TrOpaqueVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrOpaqueVal safety env ci ci') : TrOpaqueVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih

private theorem Aligned.addMutualHeaders
    (H : Aligned safety C env)
    (hrel : List.Forall₂ (fun v v' =>
      TrConstVal safety base (.defnInfo v) v'.toVConstVal) vs vs')
    (hfresh : ConstMap.MutualFresh C vs)
    (hbase : base ≤ env)
    (hadd : env.addMutualHeaders vs' = some headers) :
    Aligned safety (ConstMap.addMutualDefinitions C vs) headers := by
  induction hrel generalizing C env headers with
  | nil =>
    simp [VEnv.addMutualHeaders] at hadd
    cases hadd
    simpa [ConstMap.addMutualDefinitions] using H
  | @cons v v' vs vs' htr hrel ih =>
    rcases hfresh with ⟨hfresh, hnodup⟩
    have hnone := hfresh v (by simp)
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    cases hhead : env.addConst v'.name v'.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hhead] at hadd
    | some env' =>
      simp [VEnv.addMutualHeaders, hhead] at hadd
      have hhead' : env.addConst v.name v'.toVConstant = some env' := by
        have hname : v.name = v'.name := by simpa using htr.2
        rw [hname]
        exact hhead
      have H' : Aligned safety (C.insert v.name (.defnInfo v)) env' :=
        H.const hnone (htr.1.mono hbase) hhead' rfl
      have hfresh' : ConstMap.MutualFresh
          (C.insert v.name (.defnInfo v)) vs := by
        refine ⟨?_, hnodupPair.2⟩
        intro v hv
        rw [H.map_wf.find?_insert]
        split
        · rename_i heq
          have : v.name ∈ vs.map (fun v => v.name) := by
            exact List.mem_map.mpr ⟨v, hv, rfl⟩
          exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ this)).elim
        · exact hfresh v (by simp [hv])
      simpa [ConstMap.addMutualDefinitions] using
        ih H' hfresh' (hbase.trans (VEnv.addConst_le hhead)) hadd

private theorem Aligned.addMutualOpaqueHeaders
    (H : Aligned safety C env)
    (hrel : List.Forall₂ (fun v v' =>
      TrConstVal safety base (.opaqueInfo (mutualOpaqueHeader v)) v'.toVConstVal) vs vs')
    (hfresh : ConstMap.MutualFresh C vs)
    (hbase : base ≤ env)
    (hadd : env.addMutualHeaders vs' = some headers) :
    Aligned safety (ConstMap.addMutualOpaqueHeaders C vs) headers := by
  induction hrel generalizing C env headers with
  | nil =>
    simp [VEnv.addMutualHeaders] at hadd
    cases hadd
    simpa [ConstMap.addMutualOpaqueHeaders] using H
  | @cons v v' vs vs' htr hrel ih =>
    rcases hfresh with ⟨hfresh, hnodup⟩
    have hnone := hfresh v (by simp)
    have hnodupPair := List.nodup_cons.mp (show
      (v.name :: vs.map (fun v => v.name)).Nodup by simpa using hnodup)
    cases hhead : env.addConst v'.name v'.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hhead] at hadd
    | some env' =>
      simp [VEnv.addMutualHeaders, hhead] at hadd
      have hname : v.name = v'.name := by simpa using htr.2
      have hhead' : env.addConst v.name v'.toVConstant = some env' := by
        rw [hname]
        exact hhead
      have H' : Aligned safety
          (C.insert v.name (.opaqueInfo (mutualOpaqueHeader v))) env' :=
        H.const hnone (htr.1.mono hbase) hhead' rfl
      have hfresh' : ConstMap.MutualFresh
          (C.insert v.name (.opaqueInfo (mutualOpaqueHeader v))) vs := by
        refine ⟨?_, hnodupPair.2⟩
        intro w hw
        rw [H.map_wf.find?_insert]
        split
        · rename_i heq
          have hmem : w.name ∈ vs.map (fun x => x.name) :=
            List.mem_map.mpr ⟨w, hw, rfl⟩
          exact (hnodupPair.1 ((LawfulBEq.eq_of_beq heq).symm ▸ hmem)).elim
        · exact hfresh w (by simp [hw])
      simpa [ConstMap.addMutualOpaqueHeaders] using
        ih H' hfresh' (hbase.trans (VEnv.addConst_le hhead)) hadd

private theorem Aligned.addMutualDefEqs
    (H : Aligned safety C env) :
    Aligned safety C (env.addMutualDefEqs vs) := by
  induction vs generalizing env with
  | nil => simpa [VEnv.addMutualDefEqs] using H
  | cons v vs ih =>
    simp only [VEnv.addMutualDefEqs, List.foldl_cons]
    exact ih H.defeq

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem Aligned.addInduct (H : AddInduct C₁ venv₁ decl C₂ venv₂) :
    Aligned safety C₁ env₁ → Aligned safety C₂ env₂ :=
  nomatch H

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | block h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «mutual» hrel hfresh _ hadd _ _ _ _ ih =>
    exact (ih.addMutualHeaders hrel hfresh VEnv.LE.rfl hadd).addMutualDefEqs
  | mutualCheck hrel hfresh _ hadd _ ih =>
    exact ih.addMutualOpaqueHeaders hrel hfresh VEnv.LE.rfl hadd
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | «theorem» h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | unsafeDefn h1 h2 _ h _ _ _ ih => exact (ih.const h2 h1.1 h rfl).defeq
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.value? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | block h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | «theorem» h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.theorem h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | unsafeDefn h2 h3 _ h1 hvalue _ H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have hdefeq := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.unsafeDefn h2 h3 (by assumption) h1 hvalue (by assumption)).wf.ordered.defEqWF
          VEnv.addDefEq_self
      let ⟨⟨_, blevels, _⟩, bname⟩ := h2
      refine ⟨_, hvalue.mono VEnv.addDefEq_le,
        blevels.symm ▸ bname.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | «mutual» htypesRel hfresh htypes hadd hcontains hbodies hwfs H ih =>
    rename_i env0 vs0 vs0' C0 headers Q0
    have hpairs := List.Forall₂.and htypesRel hbodies
    obtain hold | ⟨v, v', hvmem, hv'mem, ⟨htr, hbody⟩, _, hci⟩ :=
      ConstMap.find?_addMutualDefinitions H.map_wf hpairs hfresh h
    · exact (ih hold).mono <|
        (VEnv.addMutualHeaders_le hadd).trans VEnv.addMutualDefEqs_le
    · subst ci
      cases hv
      have hdf := VEnv.addMutualDefEqs_mem (env := headers) hv'mem
      have hfinalwf :=
        (H.mutual htypesRel hfresh htypes hadd hcontains hbodies hwfs).wf
      have hdefeq := VEnv.IsDefEq.extra0 hdf <| hfinalwf.ordered.defEqWF hdf
      let ⟨⟨_, blevels, _⟩, bname⟩ := htr
      refine ⟨_, hbody.mono VEnv.addMutualDefEqs_le,
        blevels.symm ▸ bname.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | mutualCheck _ hfresh _ hadd H ih =>
    obtain hold | ⟨v, _, _, hci⟩ :=
      ConstMap.find?_addMutualOpaqueHeaders H.map_wf hfresh h
    · exact (ih hold).mono (VEnv.addMutualHeaders_le hadd)
    · subst ci
      contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | induct _ h1 H ih => cases h1

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.value? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv
