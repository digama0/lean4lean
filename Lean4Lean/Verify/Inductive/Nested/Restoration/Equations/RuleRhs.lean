import Lean4Lean.Verify.Inductive.Nested.Restoration.Recursors

/-! Translation of the restored rules of a validated nested run.

`Instance.restoredEquations` restores the left-hand side, right-hand side and
type of every generated equation. The right-hand side of a restored rule is
produced by the executable (`restoreRule`, whose right-hand side is
`restoreNested` of the lowered rule's right-hand side); this file proves that
its translation is the abstract restoration of the generated equation's
right-hand side, using the parameter uniformity of the lowered right-hand sides
(`NestedRun.recursorParamUniform_of_wfCore`, which needs nothing beyond the
run). The lowered right-hand side is a
lambda telescope, so we first prove the lambda analogue of
`restorationCommutes`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Commutation for lambda telescopes -/

theorem restoration_expr_wrapLams {r : Restoration} :
    ∀ {D₁ D₂ : List VExpr}, List.Forall₂ (fun x y => r.expr x = some y) D₁ D₂ →
      ∀ {body body' : VExpr}, r.expr body = some body' →
        r.expr (VExpr.wrapLams D₁ body) = some (VExpr.wrapLams D₂ body')
  | _, _, .nil, _, _, h => by simpa [VExpr.wrapLams] using h
  | _, _, .cons hd t, _, _, h => by
    have := restoration_expr_wrapLams t h
    simp only [VExpr.wrapLams, List.foldr_cons] at this ⊢
    exact restoration_expr_lam hd this

/-- A lambda telescope stripped by `LeadingBinders` is the telescope's
residual. -/
theorem Expr.LambdaTelescope.leadingBinders_eq {e suffix body : Expr} {n : Nat}
    (Htel : Expr.LambdaTelescope e n suffix) (Hlead : Expr.LeadingBinders n e body) :
    body = suffix := by
  induction Htel generalizing body with
  | nil => cases Hlead; rfl
  | cons _ ih => cases Hlead with | lam Hb => exact ih Hb

/-- `LeadingBinders` of a term translating to a lambda telescope at least as
long are lambda binders. -/
theorem _root_.Lean.Expr.LeadingBinders.lambdaTelescope_of_tr {env : VEnv} {Us : List Name}
    {n : Nat} {e body : Expr} (H : Expr.LeadingBinders n e body) :
    ∀ {Δ : VLCtx} {D : List VExpr} {X : VExpr},
      TrExprS env Us Δ e (VExpr.wrapLams D X) → n ≤ D.length →
      Expr.LambdaTelescope e n body := by
  induction H with
  | zero => intros; exact .nil _
  | forallE _ _ =>
    intro Δ D X Htr hn
    cases D with
    | nil => simp at hn
    | cons d D =>
      simp only [VExpr.wrapLams, List.foldr_cons] at Htr
      cases Htr
  | lam _ ih =>
    intro Δ D X Htr hn
    cases D with
    | nil => simp at hn
    | cons d D =>
      simp only [VExpr.wrapLams, List.foldr_cons] at Htr
      cases Htr with
      | lam _ _ hb =>
        exact .cons (ih (D := D) (X := X) (by simpa [VExpr.wrapLams] using hb)
          (by simpa using hn))

/-- The restored body of an opening of a lambda telescope is closed when its
residual is. -/
theorem NestedRestorationOpening.restoredBody_closed_lam {decl : VInductDecl}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name}
    (D : RestorationTablesAgree decl auxiliaries result env auxRec Us₀)
    {input output suffix : Expr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (hsuffix : Closed suffix result.nparams) : Closed Hopen.restoredBody := by
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have hparams : Hopen.params.toList = fvars.map Expr.fvar := by simpa using hAs
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    rcases List.mem_map.mp ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := by
    rw [← Array.length_toList, hparams, List.length_map, hlen]
  have hbodyClosed : Closed Hopen.body := by
    rw [hbody]
    apply Closed.instantiateRevList
    · intro b hb
      rcases List.mem_map.mp hb with ⟨fv, _, rfl⟩
      trivial
    · simpa [hlen] using hsuffix
  exact Hopen.replacement.closed
    (fun t out k h ht => restoreNestedNode_closed (D.restoreHead_closed HAs hsize) h ht)
    0 hbodyClosed

/-- A closed lambda telescope has a residual closed at the depth of its
binders. -/
theorem Expr.LambdaTelescope.closed_result {outer result : Expr} {arity depth : Nat}
    (H : Expr.LambdaTelescope outer arity result) (Houter : Closed outer depth) :
    Closed result (depth + arity) := by
  induction H generalizing depth with
  | nil => simpa using Houter
  | cons _ ih =>
    have Hresult := ih Houter.2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hresult

/-- **Parameter uniformity of every opening** of a stored lambda telescope
whose parameter prefix is parameter-uniform over bound variables. -/
theorem NestedRestorationOpening.paramUniform_of_lowered_lam
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {heads : List Name} {auxLevels : List Level}
    {input output suffix : Expr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (Hshape : Expr.ParamUniformTele heads result.nparams auxLevels input) :
    Hopen.body.ParamUniform heads Hopen.params.toList auxLevels := by
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have hparams : Hopen.params.toList = fvars.map Expr.fvar := by simpa using hAs
  obtain ⟨body, Hlead, HB⟩ := Hshape
  cases Htel.leadingBinders_eq Hlead
  rw [hbody, hparams]
  rw [← hlen] at HB
  exact HB.instantiateRevList_fvars

/-- A term translating to a nonempty lambda telescope is not a `forallE`. -/
theorem TrExprS.isForall_false_of_wrapLams {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {d : VExpr} {D : List VExpr} {X : VExpr}
    (H : TrExprS env Us Δ e (VExpr.wrapLams (d :: D) X)) : e.isForall = false := by
  cases e with
  | forallE => simp only [VExpr.wrapLams, List.foldr_cons] at H; cases H
  | _ => rfl

/-! ### The restored equation list -/

/-- **Translation of one restored equation.** The abstract equation `rule`
at generated constructor index `k` translates the executable restored rule: for
some generated owner, restoration step at the owner's lowered recursor name,
and position `j` of that step's restored rule list with `k` the flattened
index of the rule (`recursorMinorOffset` of the owner plus `j`),

* `rule.uvars` is the generated equation's universe count;
* `rule.rhs` is the translation, in `trEnv`, of the right-hand side of the
  executable restored rule (`restoreRule`, i.e. `restoreNested` of the lowered
  rule's right-hand side) at the restored recursor's level parameters;
* `rule.lhs` and `rule.type` are the abstract restorations of the generated
  equation's left-hand side and type. The executable `RecursorRule` carries
  no left-hand side or type, so these two components have no executable
  counterpart to be translated. -/
def NestedRun.TrRestoredRecursorRule
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (r : Restoration) (trEnv : VEnv)
    (k : Fin E.lowered.recursors.generationSignature.constructors.size)
    (rule : VDefEq) : Prop :=
  ∃ (owner : Fin E.lowered.recursors.generationSignature.families.size)
    (j : Nat) (s t : Environment)
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.lowered.recursors.canonicalGeneration.recursorName owner) s t)
    (hj : j < Hstep.restored.newInfo.rules.length),
    k.val = recursorMinorOffset E.lowered.indTypes owner.val + j ∧
    rule.uvars = (E.lowered.recursors.canonicalGeneration.equation k).uvars ∧
    TrExprS trEnv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs rule.rhs ∧
    r.expr (E.lowered.recursors.canonicalGeneration.equation k).lhs =
      some rule.lhs ∧
    r.expr (E.lowered.recursors.canonicalGeneration.equation k).type =
      some rule.type

/-! ### The restored block -/

end VerifyInductive
end Lean4Lean
