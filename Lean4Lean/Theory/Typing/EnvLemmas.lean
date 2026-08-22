import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

private theorem VEnv.addMutualHeaders_ordered
    (henv : Ordered env)
    (htypes : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (hadd : env.addMutualHeaders cis = some headers) :
    Ordered headers := by
  induction cis generalizing env headers with
  | nil =>
    simp [VEnv.addMutualHeaders] at hadd
    cases hadd
    exact henv
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addMutualHeaders, hci] at hadd
    | some env' =>
      simp [VEnv.addMutualHeaders, hci] at hadd
      have henv' : Ordered env' := .const henv (htypes ci (by simp)) hci
      apply ih henv' _ hadd
      intro ci' hci'
      exact (htypes ci' (by simp [hci'])).mono (VEnv.addConst_le hci)

private theorem VEnv.addMutualDefEqs_ordered
    (henv : Ordered headers)
    (hcontains : ∀ ci ∈ cis,
      headers.constants ci.name = some ci.toVConstant)
    (hbodies : ∀ ci ∈ cis, ci.WF headers) :
    Ordered (headers.addMutualDefEqs cis) := by
  have go : ∀ (rest : List VDefVal) (env : VEnv),
      rest ⊆ cis → headers ≤ env → Ordered env →
      Ordered (env.addMutualDefEqs rest) := by
    intro rest
    induction rest with
    | nil => intro env _ _ henv; exact henv
    | cons ci rest ih =>
      intro env hsub hle henv
      have hci : ci ∈ cis := hsub (by simp)
      have hlhs : env.HasType ci.uvars []
          (.const ci.name (VLevel.params ci.uvars)) ci.type := by
        rw [← (hbodies ci hci).levelWF ⟨⟩ |>.2.2.instL_id]
        exact .const (hle.constants (hcontains ci hci)) VLevel.id_WF (by simp)
      have hdf : ci.toDefEq.WF env := ⟨hlhs, (hbodies ci hci).mono hle⟩
      apply ih (env := env.addDefEq ci.toDefEq)
      · intro x hx; exact hsub (by simp [hx])
      · exact hle.trans VEnv.addDefEq_le
      · exact .defeq henv hdf
  exact go cis headers (fun _ => id) VEnv.LE.rfl henv

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H with
    | empty => exact .empty
    | decl h _ ih =>
      cases h with
      | block => exact ih
      | «axiom» h1 h2 => exact .const ih h1 h2
      | @«def» env env' ci h1 h2 =>
        refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
        · simp [VDefVal.toDefEq]
          rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
          exact .const (addConst_self h2) VLevel.id_WF (by simp)
        · exact h1.mono (addConst_le h2)
      | unsafeDef htype hadd hvalue =>
        have hordered := Ordered.const ih htype hadd
        refine .defeq hordered ⟨?_, hvalue⟩
        simp [VDefVal.toDefEq]
        rw [← (hvalue.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self hadd) VLevel.id_WF (by simp)
      | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
      | «mutual» htypes hadd hcontains hbodies =>
        exact addMutualDefEqs_ordered
          (addMutualHeaders_ordered ih htypes hadd) hcontains hbodies
      | «example» _ => exact ih
      | quot h1 h2 => exact addQuot_WF ih h1 h2
      | induct h1 h2 => exact addInduct_WF ih h1 h2

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩
