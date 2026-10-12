import Lean4Lean.Theory.Typing.Confluence.SingletonAlign
import Lean4Lean.Theory.Typing.Confluence.History

/-! # Joins of definitional equalities of an earlier stage

A definitional equality of the environment that an inductive declaration's type formers are
added to, at a stage `env₀` of the environment's history, joins in the full presentation of the
environment, given coverage of the rules registered at that stage (`stage_types_joins`). The
types environment is well formed (`VEnv.WF.addConstVals`), so its derivations strengthen there,
and its rules are those of the stage. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

/-- Coverage of a registered rule at joinably typed instances. -/
def CoverageJ (p : Pattern) (r : p.RHS × p.Check) : Prop :=
  ∀ {Γ e m1 m2 A chk}, OnCtx Γ (env.IsType univs) → p.Matches e m1 m2 → Γ ⊢ e : A →
    HasTypeJ Γ e A → r.2.Realizes m1 m2 chk → (∀ t ∈ chk, Γ ⊢ t.1 ≡ t.2.1 : t.2.2) →
    ∃ left right, FullReduction Γ e left ∧ FullReduction Γ (r.1.apply m1 m2) right ∧
      NormalEq Γ left right

theorem stage_types_joins [FullEquationCoverage] {env₀ env₁ : VEnv} {decl : VInductDecl}
    (hstage : env₀ ∈ env.stages) (hdecl : decl.WF env₀)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    (hcov : ∀ {p r}, env₀.pats p r → CoverageJ p r) :
    ∀ {base E : VEnv}, base ≤ env₀ → base.addConstVals decl.typeConstants = some E →
      ∀ {A B : VExpr}, E.IsDefEqU decl.uvars [] A B → ∀ {Γ' : List VExpr} {cls : List VLevel},
        OnCtx Γ' (env.IsType univs) → (∀ l ∈ cls, l.WF univs) → cls.length = decl.uvars →
        Γ' ⊢ A.instL cls ≫≪ B.instL cls := by
  intro base E hbase hE A B hAB Γ' cls hΓ' hcls hclsl
  obtain ⟨ds, H⟩ := henv.stagesH
  have hW₀ : env₀.WF := (H.stage hstage).1
  obtain ⟨envT, envC, envR, hT, -, -, -⟩ := addInduct_stages hadd
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  have hWT : envT.WF := hW₀.addConstVals (fun ci hci => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hci
    exact hdecl.types_wf t ht) hT
  have hTle : envT ≤ env := by
    have h := addInduct_le hadd
    obtain ⟨envT', envC', envR', hT', hC', hR', hP'⟩ := addInduct_stages hadd
    rw [VInductDecl.addTypes_eq_addConstVals, hT] at hT'
    cases Option.some.inj hT'
    exact ((addCtors_le hC').trans (addProjs_le.trans ((addRecs_le hR').trans
      (addRules_le hP')))).trans hle
  have hET : E ≤ envT := addConstVals_le_target (hbase.trans (addConstVals_le hT)) hE
    (by
      intro value hvalue
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hvalue
      rw [← VInductDecl.addTypes_eq_addConstVals] at hT
      exact addTypes_find hT t ht)
  obtain ⟨T, hd⟩ := hAB
  have hd' : envT.IsDefEq univs [] (A.instL cls) (B.instL cls) (T.instL cls) := by
    simpa using (hd.mono hET).instL (U' := univs) hcls
  have hs := IsDefEq.strong hWT.orderedStrong (Γ := []) trivial hd'
  have hpats : envT.pats = env₀.pats := addConstVals_pats hT
  obtain ⟨hj, -, -⟩ := hs.church_rosserJ_of hTle
    (fun hΓ hp hm he hJ hr hall => hcov (hpats ▸ hp) hΓ hm he hJ hr hall) trivial
  have hcl := (hd'.closedN' hWT.ordered.closed ⟨⟩)
  have := hj.weakN (Ctx.LiftN.zero Γ' (n := Γ'.length) (Γ := []) rfl)
  simpa [hcl.1.liftN_eq (Nat.zero_le _), hcl.2.1.liftN_eq (Nat.zero_le _)] using this

end Lean4Lean.VEnv
