import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Lowering.ParameterOpening
import Lean4Lean.Verify.Inductive.Constructor.ParameterSyntacticTranslation

/-! # The lowering's parameter context (owner: Restoration-A)

The checker context in which `validateNestedAuxiliaries` runs: the lowering's local context
`res.lctx` is the opening of the first source header's parameter telescope
(`NestedLoweringOutput.params_opening`), so it is the local context of a well-formed checker
context in any model where that header translates (`LoweringParamOpening.toMLCtx`, ported from
the source branch), and that context supplies the premises of
`validateNestedAuxiliaries.WF` (`NestedLoweringOutput.parameterMLCtx`, the source branch's
`NestedLowering.resultParameterMLCtx`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The source parameter opening of nested lowering determines a
well-formed metacontext with the same local context. -/
theorem LoweringParamOpening.toMLCtx
    (henv : env.WF)
    (Hopen : LoweringParamOpening lctx params type n outLctx tail outParams)
    (houtWF : outLctx.WF)
    (mlctx : TypeChecker.MLCtx)
    (hmlctx : mlctx.lctx = lctx)
    (hmlctxWF : mlctx.WF env Us)
    (Htype : TrExprS env Us mlctx.vlctx type target) :
    ∃ outMLCtx : TypeChecker.MLCtx, ∃ targetTail,
      outMLCtx.lctx = outLctx ∧
      outMLCtx.WF env Us ∧
      TrExprS env Us outMLCtx.vlctx tail targetTail := by
  induction Hopen generalizing mlctx target with
  | done =>
    exact ⟨mlctx, target, hmlctx, hmlctxWF, Htype⟩
  | step Hnext ih =>
    rename_i n' outLctx' tail' outParams' lctx' params' id name dom body bi
    cases Htype with
    | forallE HdomainType HbodyType Hdomain Hbody =>
      rename_i domainTarget bodyTarget
      have hcurrentWF : lctx'.WF := hmlctx ▸ hmlctxWF.tr.1
      have hidFresh : lctx'.find? id = none := by
        rcases Hnext.context_extension with
          ⟨decls, hlctx, _hparams, _hlength⟩
        have hnodup := houtWF.nodup
        rw [hlctx, List.map_append] at hnodup
        simp only [LocalContext.mkLocalDecl_toList, List.map_cons,
          LocalDecl.fvarId] at hnodup
        have hidNotMem : id ∉ lctx'.toList.map (fun d => d.fvarId) := by
          exact (List.nodup_cons.mp
            (List.nodup_append.mp hnodup).2.1).1
        rw [hcurrentWF.find?_eq_find?_toList]
        exact List.find?_eq_none.mpr (by
          intro decl hdecl hmatch
          have hfv : decl.fvarId = id := (LawfulBEq.eq_of_beq hmatch).symm
          exact hidNotMem (List.mem_map.mpr ⟨decl, hdecl, hfv⟩))
      let nextMLCtx := TypeChecker.MLCtx.vlam id name dom domainTarget bi mlctx
      have hnextWF : nextMLCtx.WF env Us :=
        ⟨hmlctxWF, by simpa [nextMLCtx, hmlctx] using hidFresh,
          Hdomain, HdomainType⟩
      have Hbody' : TrExprS env Us nextMLCtx.vlctx
          (body.instantiate1 (.fvar id)) bodyTarget := by
        rw [Expr.instantiate1_eq]
        exact Hbody.inst_fvar henv.orderedStrong hnextWF.tr.wf
      apply ih houtWF nextMLCtx
      · simp [nextMLCtx, TypeChecker.MLCtx.lctx, hmlctx]
      · exact hnextWF
      · exact Hbody'


/-- **The premises of `validateNestedAuxiliaries.WF`** from the lowering output: a well-formed
checker context over `res.lctx`, fresh for the checker's name generator, in which every cached
nested occurrence is scoped, in any model where the first source header translates. -/
theorem NestedLoweringOutput.parameterMLCtx {env : Environment} {fuel nparams : Nat}
    {sourceTypes : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res)
    {venv : VEnv} {Us : List Name} (henv : venv.WF)
    (Hfirst : ∀ first rest, sourceTypes = first :: rest →
      ∃ target, TrExprS venv Us [] first.type target) :
    ∃ mlctx : TypeChecker.MLCtx, mlctx.WF venv Us ∧ mlctx.lctx = res.lctx ∧
      (∀ fv ∈ mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv) ∧
      ∀ n nested, res.aux2nested.find? n = some nested →
        nested.FVarsIn (· ∈ mlctx.vlctx.fvars) := by
  obtain ⟨first, rest, tail, htypes, Hopen, hwf, hfresh, -⟩ := H.params_opening
  obtain ⟨target, Htype⟩ := Hfirst first rest htypes
  obtain ⟨mlctx, -, hlctx, hmlctx, -⟩ :=
    LoweringParamOpening.toMLCtx henv Hopen hwf .nil rfl trivial Htype
  have hfv : mlctx.vlctx.fvars = res.lctx.fvars := by
    rw [← hmlctx.tr.fvars_eq, hlctx]
  refine ⟨mlctx, hmlctx, hlctx, fun fv h => hfresh fv (hfv ▸ h), ?_⟩
  intro n nested hfind
  obtain ⟨-, -, -, -, -, -, -, hin⟩ := H.nested_app n nested hfind
  refine hin.mono fun fv hmem => ?_
  rw [hfv, ← H.lctx_params.1]
  exact List.mem_map.mpr ⟨.fvar fv, List.mem_reverse.mpr hmem, rfl⟩

end VerifyInductive
end Lean4Lean
