import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Typing.Interpretation
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.EnvLemmas

/-! The specification classifies constructor fields by their strictly positive normal form
(`InductiveSignature.Models.classifiedFields`). For `inductive N | z : N | s : N → N`, a
signature that marks the argument of `s` as `external`, and so generates a recursor whose
successor minor has no induction hypothesis, does not model `N`: the field type `N` is not
definitionally equal to any type that does not mention `N`. The proof interprets `N` once as
`Prop` and once as `Prop → Prop` in the empty environment (`VEnv.Interpretation`); a family-free
normal form is fixed by both, so `Prop ≡ Prop → Prop`, which head inversion refutes. The
signature with the argument marked recursive satisfies the clause. -/

namespace Lean4Lean.Tests.RecursiveFieldClassification
open Lean4Lean InductiveSignature

def natType : VExpr := .const `N []

def zeroCtor : VConstVal := { name := `N.z, uvars := 0, type := natType }
def succCtor : VConstVal := { name := `N.s, uvars := 0, type := .forallE natType natType }

def natHeader : VInductiveType :=
  { name := `N, uvars := 0, type := .sort (.succ .zero), numIndices := 0,
    resultLevel := .succ .zero, ctors := [zeroCtor, succCtor] }

def natDecl : VInductDecl := { uvars := 0, nparams := 0, types := [natHeader], isUnsafe := false }

/-- `N` with the argument of `s` given field kind `field`. -/
def natSignature (field : Field 1) : InductiveSignature where
  uvars := 0
  params := []
  families := #[{ name := `N, indices := [], resultLevel := .succ .zero }]
  constructors := #[
    { name := `N.z, owner := ⟨0, by decide⟩, fields := [], indices := [] },
    { name := `N.s, owner := ⟨0, by decide⟩, fields := [field], indices := [] }]

/-- The argument of `s` marked recursive, as Lean's recursor has it. -/
def recursiveSignature : InductiveSignature :=
  natSignature (.recursive natType { binders := [], target := ⟨0, by decide⟩, indices := [] })

/-- The argument of `s` marked external: no induction hypothesis. -/
def externalSignature : InductiveSignature := natSignature (.external natType)

def headerEnv : VEnv :=
  { VEnv.empty with constants := fun n => if `N = n then some natHeader.toVConstant else none }

theorem headerEnv_eq : VEnv.empty.addConstVals natDecl.typeConstants = some headerEnv := by
  simp [VInductDecl.typeConstants, natDecl, VEnv.addConstVals, VEnv.addConst, VEnv.empty,
    headerEnv]
  rfl

/-- Interpret `N` by the closed type `t`, keeping every other name. -/
def interpretN (t : VExpr) : VEnv.Interpretation where
  consts c := if c = `N then some t else none
  rename := id

theorem interpretN_fixed {t e : VExpr} (h : e.SourceConstFree [`N]) :
    (interpretN t).expr e = e := by
  induction h with
  | bvar | sort => rfl
  | const name levels fresh =>
    have : name ≠ `N := by simpa using fresh
    simp [VEnv.Interpretation.expr, interpretN, this]
  | proj _ _ _ ih =>
    change VExpr.proj (id _) _ ((interpretN t).expr _) = _
    rw [ih]; rfl
  | app _ _ ih1 ih2 => simp [VEnv.Interpretation.expr, ih1, ih2]
  | lam _ _ ih1 ih2 => simp [VEnv.Interpretation.expr, ih1, ih2]
  | forallE _ _ ih1 ih2 => simp [VEnv.Interpretation.expr, ih1, ih2]

theorem emptyWF : VEnv.empty.WF := ⟨[], .empty⟩

/-- Interpreting `N : Sort 1` by a closed type `t : Sort 1` of the empty environment is sound. -/
theorem interpretN_sound {t : VExpr} (hclosed : t.ClosedN)
    (htype : VEnv.empty.HasType 0 [] t (.sort (.succ .zero))) :
    (interpretN t).Sound VEnv.empty headerEnv (fun _ _ => True) where
  closed c t' h := by
    simp only [interpretN] at h
    split at h
    · cases h; exact hclosed
    · cases h
  ordered := emptyWF.orderedStrong
  constants c ci h := by
    simp only [headerEnv, VEnv.empty] at h
    split at h
    · rename_i hc
      subst hc
      cases h
      refine ⟨fun t' ht => ?_, fun hnone => by simp [interpretN] at hnone⟩
      simp only [interpretN] at ht
      cases ht
      simpa [natHeader, VEnv.Interpretation.expr] using htype
    · cases h
  defeqs df h := by cases h
  pats _ _ h := by cases h
  projections _ _ h := by cases h

theorem prop_typed {Γ : List VExpr} :
    VEnv.empty.HasType 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sort (by trivial)

theorem propArrow_typed :
    VEnv.empty.HasType 0 [] (.forallE (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) := by
  have h : VEnv.empty.HasType 0 [] (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) := .forallEDF prop_typed prop_typed
  exact .defeqDF (.sortDF (l := .imax (.succ .zero) (.succ .zero)) (l' := .succ .zero)
    (by trivial) (by trivial) VLevel.imax_self) h

/-- A type that does not mention `N` is not definitionally equal to `N` in the environment
with the header of `N`. -/
theorem not_defeq_familyFree {normalized : VExpr}
    (hfree : normalized.SourceConstFree [`N])
    (hdefeq : headerEnv.IsDefEqU 0 [] natType normalized) : False := by
  obtain ⟨A, hd⟩ := hdefeq
  have h1 := (interpretN_sound (t := .sort .zero) (by simp [VExpr.ClosedN]) prop_typed).isDefEq
    VEnv.CtxInvariant.any hd trivial
  have h2 := (interpretN_sound (t := .forallE (.sort .zero) (.sort .zero))
    (by simp [VExpr.ClosedN]) propArrow_typed).isDefEq VEnv.CtxInvariant.any hd trivial
  rw [interpretN_fixed hfree] at h1 h2
  simp only [natType, VEnv.Interpretation.expr, interpretN, if_pos, List.map_nil] at h1 h2
  have h12 : VEnv.empty.IsDefEqU 0 [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero)) :=
    VEnv.IsDefEqU.trans emptyWF trivial ⟨_, h1⟩ ⟨_, h2.symm⟩
  exact VEnv.IsDefEqU.sort_forallE_inv (Γ := []) emptyWF trivial h12

/-- **The specification rejects a recursive field marked external.** -/
theorem externalSignature_not_models : ¬ externalSignature.Models VEnv.empty natDecl := by
  intro H
  rcases H.classifiedFields with hunsafe | ⟨envTypes, htypes, hfields⟩
  · cases hunsafe
  rw [headerEnv_eq] at htypes
  cases htypes
  obtain ⟨normalized, hdefeq, hfree⟩ := hfields
    { name := `N.s, owner := ⟨0, by decide⟩, fields := [.external natType], indices := [] }
    (.tail _ (.head _)) 0 (by simp)
  exact not_defeq_familyFree hfree hdefeq

/-- The argument of `s` marked recursive meets the classification clause: `N` is its own
recursive normal form. -/
theorem recursiveSignature_classified :
    ∃ normalized, headerEnv.IsDefEqU 0 [] natType normalized ∧
      natDecl.ClassifiedFieldNormalForm (VLevel.params 0) 0 true normalized := by
  refine ⟨natType, ⟨.sort (.succ .zero), ?_⟩, [], natType, rfl, by simp, ?_, natHeader,
    by simp [natDecl], rfl⟩
  · have h := VEnv.HasType.const (env := headerEnv) (U := 0) (ls := []) (Γ := [])
      (c := `N) (ci := natHeader.toVConstant) (by simp [headerEnv]) (by simp) (by simp [natHeader])
    simp [natHeader, VExpr.instL, VLevel.inst] at h
    exact h
  · exact ⟨natHeader, by simp [natDecl], Or.inl rfl, [], rfl, rfl, by simp [natDecl, natHeader],
      by simp [natDecl, VInductDecl.paramVars], by simp⟩

end Lean4Lean.Tests.RecursiveFieldClassification
