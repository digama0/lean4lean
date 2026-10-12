import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.Inductive.Rules.RuleSyntax

/-! Opening of a constructor telescope by the field traversal of the recursor
construction: a field-decision run (`RecursorFieldDecisions`) determines the
fresh field variables, the alpha-closing equation of the opened telescope, and the
scoping of every expression it reaches. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The name-generator cursor of a binding context is absent from its local
context map.  This is the freshness fact used when two field
traversals extend an ordered alpha spine. -/
theorem BindingContextWF.currentFind?_eq_none
    (H : BindingContextWF c) :
    c.lctx.find? ⟨c.ngen.curr⟩ = none := by
  rw [H.wf.find?_eq_find?_toList]
  by_contra hne
  rcases Option.ne_none_iff_exists.mp hne with ⟨decl, hfind⟩
  apply H.current_not_mem
  rw [LocalContext.fvars]
  apply List.mem_map.2
  refine ⟨decl, List.mem_of_find?_eq_some hfind.symm, ?_⟩
  have hcursor := List.find?_some hfind.symm
  exact (LawfulBEq.eq_of_beq hcursor).symm

/-- A field-decision run determines the well-formed extension
context and the fresh free-variable array introduced by the traversal.
This is independent of the recursive/nonrecursive decisions:
both branches introduce the same local declaration before classifying it. -/
theorem RecursorFieldDecisions.freshBindings
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root) :
    ∃ _Hcurrent : BindingContextWF current,
      BindingContextLE root current ∧
      Nonempty (FVarArrayAfter root current all) := by
  induction H with
  | nil =>
      exact ⟨Hroot, BindingContextLE.refl root,
        ⟨FVarArrayAfter.empty root⟩⟩
  | @nonrecursive c name dom body bi bu u positions H _ ih =>
      rcases ih with ⟨Hc, HrootCurrent, ⟨Hbindings⟩⟩
      let Hnext := Hc.withCheckedLocalDecl (base := ctorFieldCheck c stats bu) name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
      let Hstep := BindingContextLE.withCheckedLocalDecl
          (base := ctorFieldCheck c stats bu) c Hc name
        (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
      exact ⟨Hnext, HrootCurrent.trans Hstep,
        ⟨Hbindings.pushCurrentChecked Hc HrootCurrent name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi⟩⟩
  | @recursive c name dom body bi bu u positions target H _ ih =>
      rcases ih with ⟨Hc, HrootCurrent, ⟨Hbindings⟩⟩
      let Hnext := Hc.withCheckedLocalDecl (base := ctorFieldCheck c stats bu) name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
      let Hstep := BindingContextLE.withCheckedLocalDecl
          (base := ctorFieldCheck c stats bu) c Hc name
        (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
      exact ⟨Hnext, HrootCurrent.trans Hstep,
        ⟨Hbindings.pushCurrentChecked Hc HrootCurrent name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi⟩⟩

/-- A field-decision run opens the source constructor telescope: it packages
the alpha-closing equation for the field identifiers chosen by the checker.
The run may cover only a prefix of the fields; the resulting opening has
exactly that prefix's arity. -/
theorem RecursorFieldDecisions.fieldOpening
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars)) :
    Nonempty (ConstructorFieldOpening source terminal all) := by
  have go : ∀ {current terminal all selected positions},
      RecursorFieldDecisions stats root source current terminal
        all selected positions →
      ∃ Hcurrent : BindingContextWF current,
        BindingContextLE root current ∧
        ∃ Hbindings : FVarArrayAfter root current all,
          Nonempty (ConstructorFieldOpening source terminal all) := by
    intro current terminal all selected positions Htrace
    induction Htrace with
    | nil =>
        exact ⟨Hroot, BindingContextLE.refl root,
          FVarArrayAfter.empty root,
          ⟨ConstructorFieldOpening.empty source⟩⟩
    | @nonrecursive c name dom body bi bu u positions Hprev _ ih =>
        rcases ih with ⟨Hc, HrootCurrent, Hbindings, ⟨Hopening⟩⟩
        let Hnext := Hc.withCheckedLocalDecl (base := ctorFieldCheck c stats bu) name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
        let Hstep := BindingContextLE.withCheckedLocalDecl
          (base := ctorFieldCheck c stats bu) c Hc name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
        have hopenFvars : Hopening.fvars = Hbindings.fvars :=
          Hopening.fvars_eq_bound Hbindings.toFVarArrayIn
        have hcurrentFresh :
            (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
          rw [hopenFvars]
          intro hmem
          exact Hc.current_not_mem
            (Hbindings.toFVarArrayIn.members _ hmem)
        have hbodyFresh : body.FVarsIn
            (fun fv => fv ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
          have hbodyScope := (Hopening.currentFVarsIn hsource).2
          apply hbodyScope.mono
          intro fv hfv heq
          subst fv
          rcases hfv with hopen | hroot
          · apply Hc.current_not_mem
            apply Hbindings.toFVarArrayIn.members
            rwa [← hopenFvars]
          · exact Hc.current_not_mem (HrootCurrent hroot)
        exact ⟨Hnext, HrootCurrent.trans Hstep,
          Hbindings.pushCurrentChecked Hc HrootCurrent name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi,
          ⟨Hopening.push hcurrentFresh hbodyFresh⟩⟩
    | @recursive c name dom body bi bu u positions target Hprev _ ih =>
        rcases ih with ⟨Hc, HrootCurrent, Hbindings, ⟨Hopening⟩⟩
        let Hnext := Hc.withCheckedLocalDecl (base := ctorFieldCheck c stats bu) name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
        let Hstep := BindingContextLE.withCheckedLocalDecl
          (base := ctorFieldCheck c stats bu) c Hc name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
        have hopenFvars : Hopening.fvars = Hbindings.fvars :=
          Hopening.fvars_eq_bound Hbindings.toFVarArrayIn
        have hcurrentFresh :
            (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
          rw [hopenFvars]
          intro hmem
          exact Hc.current_not_mem
            (Hbindings.toFVarArrayIn.members _ hmem)
        have hbodyFresh : body.FVarsIn
            (fun fv => fv ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
          have hbodyScope := (Hopening.currentFVarsIn hsource).2
          apply hbodyScope.mono
          intro fv hfv heq
          subst fv
          rcases hfv with hopen | hroot
          · apply Hc.current_not_mem
            apply Hbindings.toFVarArrayIn.members
            rwa [← hopenFvars]
          · exact Hc.current_not_mem (HrootCurrent hroot)
        exact ⟨Hnext, HrootCurrent.trans Hstep,
          Hbindings.pushCurrentChecked Hc HrootCurrent name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi,
          ⟨Hopening.push hcurrentFresh hbodyFresh⟩⟩
  rcases go H with ⟨_, _, _, Hopening⟩
  exact Hopening

/-- Every expression reached by a field-decision run is scoped by its
current local context.  This is the freshness input needed to open
paired forall bodies at the two independently generated cursors. -/
theorem RecursorFieldDecisions.currentFVarsIn
    (H : RecursorFieldDecisions stats root source current terminal
      all selected positions)
    (Hroot : BindingContextWF root)
    (hsource : source.FVarsIn (fun fv => fv ∈ root.lctx.fvars)) :
    terminal.FVarsIn (fun fv => fv ∈ current.lctx.fvars) := by
  rcases H.freshBindings Hroot with
    ⟨_Hcurrent, HrootCurrent, ⟨Hbindings⟩⟩
  rcases H.fieldOpening Hroot hsource with ⟨Hopening⟩
  have hopenFvars : Hopening.fvars = Hbindings.fvars :=
    Hopening.fvars_eq_bound Hbindings.toFVarArrayIn
  apply (Hopening.currentFVarsIn hsource).mono
  intro fv hfv
  rcases hfv with hopen | hroot
  · apply Hbindings.members
    rwa [← hopenFvars]
  · exact HrootCurrent hroot

end VerifyInductive
end Lean4Lean
