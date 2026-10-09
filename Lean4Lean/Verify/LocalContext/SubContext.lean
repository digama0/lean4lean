import Lean4Lean.Verify.LocalContext

/-! Concrete local-context inclusion, ignoring declaration position indices. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Every declaration of `l` occurs in `l'` with the same content, up to its
position index. -/
def _root_.Lean.LocalContext.SubContextOf (l l' : LocalContext) : Prop :=
  ∀ fv d, l.find? fv = some d →
    ∃ d', l'.find? fv = some d' ∧ d'.setIndex 0 = d.setIndex 0

theorem _root_.Lean.LocalContext.SubContextOf.empty {l' : LocalContext} :
    ({} : LocalContext).SubContextOf l' := by
  intro fv d h
  rw [LocalContext.find?_empty] at h
  cases h

/-- Extending only the larger context by a fresh declaration keeps a
sub-context. -/
theorem _root_.Lean.LocalContext.SubContextOf.mkLocalDecl_right
    {l l' : LocalContext} {fv : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (h : l.SubContextOf l')
    (hwf : l'.fvarIdToDecl.WF) (hfresh : l'.find? fv = none) :
    l.SubContextOf (l'.mkLocalDecl fv name ty bi kind) := by
  intro fv' d hd
  rcases h fv' d hd with ⟨d', hd', heq⟩
  refine ⟨d', ?_, heq⟩
  rw [LocalContext.find?_mkLocalDecl hwf]
  have hne : (fv == fv') = false := by
    cases hb : fv == fv'
    · rfl
    · have : fv = fv' := LawfulBEq.eq_of_beq hb
      subst this
      rw [hfresh] at hd'
      cases hd'
  rw [hne]
  exact hd'

/-- Opening the same fresh declaration in both contexts keeps a
sub-context. -/
theorem _root_.Lean.LocalContext.SubContextOf.mkLocalDecl_both
    {l l' : LocalContext} {fv : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (h : l.SubContextOf l')
    (hwf : l.fvarIdToDecl.WF) (hwf' : l'.fvarIdToDecl.WF) :
    (l.mkLocalDecl fv name ty bi kind).SubContextOf
      (l'.mkLocalDecl fv name ty bi kind) := by
  intro fv' d hd
  rw [LocalContext.find?_mkLocalDecl hwf] at hd
  rw [LocalContext.find?_mkLocalDecl hwf']
  cases hb : fv == fv' with
  | true =>
    rw [hb] at hd
    cases hd
    exact ⟨_, rfl, rfl⟩
  | false =>
    rw [hb] at hd
    rw [if_neg (by simp)]
    exact h fv' d hd

/-- Closing over declarations of a sub-context gives the same result in the
larger context. -/
theorem _root_.Lean.LocalContext.SubContextOf.mkForall_eq {l l' : LocalContext}
    (H : l.SubContextOf l') {fvs : List FVarId}
    (hmem : ∀ fv ∈ fvs, ∃ d, l.find? fv = some d) (body : Expr) :
    l'.mkForall (fvs.map Expr.fvar).toArray body =
      l.mkForall (fvs.map Expr.fvar).toArray body := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkForall, LocalContext.mkBinding_eqN]
  apply LocalContext.mkBindingListN_congr_setIndex
  intro fv hfv
  obtain ⟨d, hd⟩ := hmem fv hfv
  obtain ⟨d', hd', heq⟩ := H fv d hd
  simp [hd, hd', heq]

theorem _root_.Lean.LocalContext.SubContextOf.refl (l : LocalContext) :
    l.SubContextOf l := fun _ d h => ⟨d, h, rfl⟩

/-- A declaration found under `fv` in a well-formed context is stored under
its own identifier. -/
theorem _root_.Lean.LocalContext.WF.find?_fvarId {l : LocalContext}
    (hwf : l.WF) (h : l.find? fv = some d) : d.fvarId = fv := by
  rw [hwf.find?_eq_find?_toList] at h
  have hp := _root_.List.find?_some h
  simp only [beq_iff_eq] at hp
  exact hp.symm

end VerifyInductive

end Lean4Lean
