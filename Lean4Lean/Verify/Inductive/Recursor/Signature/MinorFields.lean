import Lean4Lean.Verify.Inductive.Recursor.Signature.FieldDomains
import Lean4Lean.Verify.Typing.TelescopeTranslationLemmas

/-! Field domains of a generated minor premise, in the abstract contexts used by the generator.

The unannotated field telescope of a minor, closed over the parameters, mentions no free
variable at all, so abstracting any further binders only lifts it. Weakening it beneath the
motives and earlier minors therefore yields the generator's `insertBinders` form of the
minor's field domains. -/

namespace Lean4Lean

theorem FVarsIn.abstract1_eq_liftLooseBVars {e : Lean.Expr} {v : Lean.FVarId} {k : Nat}
    (h : FVarsIn (· ≠ v) e) : e.abstract1 v k = e.liftLooseBVars' k 1 := by
  induction e generalizing k with
  | fvar v' =>
    simp only [FVarsIn] at h
    simp [Lean.Expr.abstract1, Lean.Expr.liftLooseBVars', Ne.symm h]
  | _ => simp_all [FVarsIn, Lean.Expr.abstract1, Lean.Expr.liftLooseBVars']

theorem _root_.Lean.Expr.liftLooseBVars'_liftLooseBVars' (e : Lean.Expr) (k d₁ d₂ : Nat) :
    (e.liftLooseBVars' k d₁).liftLooseBVars' k d₂ = e.liftLooseBVars' k (d₁ + d₂) := by
  induction e generalizing k <;> simp_all [Lean.Expr.liftLooseBVars']
  split <;> (try split) <;> omega

/-- Abstracting variables that do not occur only shifts the loose bound
variables at and above the abstraction depth. -/
theorem FVarsIn.abstractList_eq_liftLooseBVars {e : Lean.Expr} {xs : List Lean.FVarId}
    {k : Nat} (h : FVarsIn (fun fv => fv ∉ xs) e) :
    e.abstractList xs k = e.liftLooseBVars' k xs.length := by
  induction xs generalizing e with
  | nil => simp
  | cons a as ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [Lean.Expr.abstractList, List.length_cons]
    rw [(h.mono fun _ hfv => hfv.1).abstract1_eq_liftLooseBVars,
      ih ((h.mono fun _ hfv => hfv.2).liftLooseBVars),
      Lean.Expr.liftLooseBVars'_liftLooseBVars', Nat.add_comm]

namespace VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The unannotated field domains of one minor (`declFieldDomains`, at the recursor's universe
levels), lifted beneath `inserted` binders placed between the parameters and the fields,
translate the executable field telescope abstracted over the parameters and any `extra` free
variables of the same count: the parameter-closed field telescope contains no free variable. -/
theorem RecursorConstruction.minorFieldsTemplate
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (inserted : List VExpr) (extra : List FVarId) (hextra : extra.length = inserted.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let fields := (H.declFieldDomains owner howner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
    TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted) [])
      ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList (H.params.fvars ++ extra))
      (VExpr.wrapForalls (InductiveSignature.insertBinders fields inserted.length) (.sort .zero)) := by
  intro S fields
  have Hsrc := (H.sourceFields_headerReplay owner howner localIndex hlocal).2.2
  have Hweak := Hsrc.weakBV H.recursorWF.checking.tr.wf.ordered
    (abstractForallContext.bvLift inserted
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []))
  have hfvars : VLCtx.fvars ([] : VLCtx) = [] := rfl
  have hnofvars : ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList
      H.params.fvars).FVarsIn (fun fv => fv ∉ extra) := by
    have h := Hsrc.fvarsIn
    simp only [abstractForallContext_fvars, hfvars] at h
    exact h.mono fun fv hfv => by simp at hfv
  have hsource : (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList
      (H.params.fvars ++ extra) =
      ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList
        H.params.fvars).liftLooseBVars' 0 inserted.length := by
    rw [Expr.abstractList_append, hnofvars.abstractList_eq_liftLooseBVars, hextra]
  rw [hsource, insertBinders_eq_prefix]
  rw [VExpr.liftN_wrapForalls] at Hweak
  simpa [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc,
    VExpr.liftN] using Hweak

end VerifyInductive
end Lean4Lean
