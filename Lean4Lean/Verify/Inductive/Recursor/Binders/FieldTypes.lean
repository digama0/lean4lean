import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening

/-! Declaration types of the constructor fields opened by `loopCtorArgs`.

The executable field loop (`AddInductive.mkRecInfos.loopCtorArgs`) performs no
`whnf`: at each field binder `.forallE name dom body bi` it declares a fresh
local with the unannotated type
`dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper` and continues with
`body.instantiate1 (.fvar _)`. Consequently every syntactic predicate on
expressions that is inherited by the unannotated domain and by the instantiated
body of a forall holds of every field declaration type and of the terminal
expression, as soon as it holds of the traversed source. This file proves this
for the field-decision relation `RecursorFieldDecisions`. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Every expression of `fields` is a free variable of `c` declared as an
ordinary local whose type satisfies `P`. -/
def FieldDeclsSatisfy (P : Expr → Prop) (c : AddInductive.Context)
    (fields : Array Expr) : Prop :=
  ∀ e ∈ fields, ∃ fv index name type bi kind,
    e = .fvar fv ∧ fv ∈ c.lctx.fvars ∧
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧ P type

private theorem fieldDeclsSatisfy_push {P : Expr → Prop}
    (Hc : BindingContextWF c) (H : FieldDeclsSatisfy P c fields)
    (hdom : P dom) :
    FieldDeclsSatisfy P { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi }
      (fields.push (.fvar ⟨c.ngen.curr⟩)) := by
  intro e he
  simp only [Array.mem_push] at he
  have hnew : (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi).find? ⟨c.ngen.curr⟩ =
      some (.cdecl c.lctx.decls.size ⟨c.ngen.curr⟩ name dom bi .default) := by
    simp [LocalContext.mkLocalDecl, LocalContext.find?, Hc.wf.map_wf.find?_insert]
  have hmemNew : (⟨c.ngen.curr⟩ : FVarId) ∈
      (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi).fvars := by
    simp [LocalContext.fvars, LocalContext.mkLocalDecl_toList, LocalDecl.fvarId]
  have hmemOld : ∀ fv, fv ∈ c.lctx.fvars →
      fv ∈ (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi).fvars := by
    intro fv hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    exact Or.inr hfv
  rcases he with he | rfl
  · obtain ⟨fv, index, oldName, type, oldBi, kind, rfl, hmem, hfind, htype⟩ := H e he
    by_cases hfv : fv = ⟨c.ngen.curr⟩
    · subst fv
      exact ⟨_, _, _, _, _, _, rfl, hmemNew, hnew, hdom⟩
    · refine ⟨fv, index, oldName, type, oldBi, kind, rfl, hmemOld fv hmem, ?_, htype⟩
      simpa [LocalContext.mkLocalDecl, LocalContext.find?, Hc.wf.map_wf.find?_insert,
        Ne.symm hfv] using hfind
  · exact ⟨_, _, _, _, _, _, rfl, hmemNew, hnew, hdom⟩

/-- **Field declaration types.** Along a field-decision run
(`RecursorFieldDecisions`), any
predicate `P` that passes from a forall to its unannotated domain and to its body
instantiated with a free variable holds of the terminal expression and of the
declared type of every opened field. -/
theorem RecursorFieldDecisions.fieldDeclsSatisfy
    (H : RecursorFieldDecisions stats root source current terminal fields
      selected positions)
    (Hroot : BindingContextWF root) (P : Expr → Prop)
    (hstep : ∀ {ok : Name → Bool} {name : Name} {dom body : Expr} {bi : BinderInfo},
      P (.forallE name dom body bi) →
        P (dom.consumeTypeAnnotationsVerified ok) ∧
          ∀ fv : FVarId, P (body.instantiate1 (.fvar fv)))
    (hsource : P source) :
    P terminal ∧ FieldDeclsSatisfy P current fields := by
  induction H with
  | nil => exact ⟨hsource, by intro e he; simp at he⟩
  | @nonrecursive c name dom body bi fields selected positions H _ ih
  | @recursive c name dom body bi fields selected positions target H _ ih =>
    have Hc := (H.freshBindings Hroot).choose
    obtain ⟨hdom, hbody⟩ := hstep ih.1
    exact ⟨hbody _, fieldDeclsSatisfy_push Hc ih.2 hdom⟩

end VerifyInductive
end Lean4Lean
