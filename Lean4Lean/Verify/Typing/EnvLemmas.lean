import Lean4Lean.Std.SMap
import Lean4Lean.Verify.Environment

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

section

variable (safety : DefinitionSafety) (env : VEnv) in
inductive Aligned1 : ConstantInfo → Option VConstant → Prop where
  | block : ¬isAsSafeAs safety ci → Aligned1 ci none
  | const : TrConstant safety env ci ci' → Aligned1 ci (some ci')

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | const : Aligned C venv → Aligned1 safety venv ci ci' →
    venv.addConst n ci' = some venv' → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

theorem Aligned.map_wf' (H : Aligned safety C venv) :
    C.WF ∧ ∀ n, (C.find? n).isSome = (venv.constants n).isSome := by
  induction H with
  | empty => exact ⟨.empty, by simp [SMap.find?, VEnv.empty]⟩
  | @const _ _ _ _ n _ _ _ eq ih =>
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    have := ih.2 n; simp_all [-ih]
    refine ⟨.insert ih.1 _ _ this, fun n' => ?_⟩
    simp [ih.1.find?_insert]; split <;> simp [ih.2]
  | defeq _ ih => exact ih

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := H.map_wf'.1
theorem Aligned.find?_isSome (H : Aligned safety C venv) :
    (C.find? n).isSome = (venv.constants n).isSome := H.map_wf'.2 _

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, h1, h2, h3, h4⟩ := H2
  refine H1 _ _ (wf.const (.const ⟨by cases safety <;> rfl, h2.2⟩) h3) h4

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
  | block hs h _ ih => exact ih.const (.block hs) h
  | «axiom» h1 _ h _ ih => exact ih.const (.const h1) h
  | «opaque» h1 _ h _ ih => exact ih.const (.const h1.1.1) h
  | defn h1 _ h _ ih => exact (ih.const (.const h1.1.1) h).defeq
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : isAsSafeAs safety ci) :
    ∃ ci', venv.constants name = some (some ci') ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some (some ci') ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some (some ci') ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | const h1 h2 h3 ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; rename_i n _ h; simp at h; subst n
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      cases h2; · contradiction
      simp; rename_i h'; exact h'.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some (some ci')) :
    TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | const h1 h2 h3 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n
      let .const h2 := h2; exact h2.mono this
    · intro hs h; exact (ih h hs).mono this
  | defeq h1 ih => exact (ih h hs).mono VEnv.addDefEq_le

end

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci) ↔ ∃ oci, venv.constants name = some oci := by
  conv => enter [1,1,_,1]; apply H.map_wf.find?'_eq_find?
  erw [← Option.isSome_iff_exists, H.aligned.find?_isSome, Option.isSome_iff_exists]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : isAsSafeAs safety ci) :
    ∃ ci', venv.constants name = some (some ci') ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some (some ci')) :
    TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs
