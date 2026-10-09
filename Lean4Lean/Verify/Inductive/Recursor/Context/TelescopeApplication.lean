import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope

/-! Applying a function to arguments along a translated forall telescope.

The de Bruijn lemmas identify the source-side instantiation of a forall body
(`Expr.instantiateForallBody`) with `instantiateRevList` for closed arguments.
`Expr.ForallTelescopeTypeTranslation.applyTranslatedArguments` then instantiates the source
and abstract telescopes of a type with translated arguments in lockstep and types the
abstract application at the instantiated residual. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Opening two closed terms at different de Bruijn depths commutes, with
the outer depth decreasing by one once the inner binder is instantiated. -/
theorem Expr.instantiate1'_instantiate1'_closed
    (e outer inner : Expr) (j d : Nat)
    (houter : outer.Closed 0) (hinner : inner.Closed 0) :
    (e.instantiate1' outer (j + d + 1)).instantiate1' inner j =
      (e.instantiate1' inner j).instantiate1' outer (j + d) := by
  induction e generalizing j with
  | bvar i =>
    simp only [Expr.instantiate1']
    repeat' first | split
    all_goals try simp only [Expr.instantiate1']
    all_goals repeat' first | split
    all_goals try rw [Expr.liftLooseBVars_eq_self
      houter.looseBVarRange_le]
    all_goals try rw [Expr.liftLooseBVars_eq_self
      hinner.looseBVarRange_le]
    all_goals try rfl
    all_goals try exact Expr.instantiate1'_eq_self (by
      simpa using houter)
    all_goals try exact (Expr.instantiate1'_eq_self (by
      simpa using hinner)).symm
    all_goals try { exfalso; omega }
    · have hclosed := hinner.looseBVarRange_le
      symm
      exact Expr.instantiate1'_eq_self
        (Nat.le_trans hclosed (Nat.zero_le (j + d)))
    · have hclosed := houter.looseBVarRange_le
      rw [Expr.liftLooseBVars_eq_self hclosed]
      exact Expr.instantiate1'_eq_self
        (Nat.le_trans hclosed (Nat.zero_le j))
  | fvar | mvar | sort | const | lit => rfl
  | app fn arg ihFn ihArg =>
    simp only [Expr.instantiate1']
    rw [ihFn, ihArg]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1']
    rw [ihDom]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ihBody (j + 1)
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1']
    rw [ihDom]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ihBody (j + 1)
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.instantiate1']
    rw [ihTy, ihValue]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ihBody (j + 1)
  | mdata md body ihBody =>
    simp only [Expr.instantiate1']
    rw [ihBody]
  | proj name idx body ihBody =>
    simp only [Expr.instantiate1']
    rw [ihBody]

/-- Opening one closed outer argument below a reverse simultaneous block of
closed inner arguments commutes with opening that block. -/
theorem Expr.instantiateRevList_instantiate1'_closed
    (e arg : Expr) (args : List Expr) (k d : Nat := 0)
    (harg : arg.Closed 0)
    (hargs : ∀ item ∈ args, item.Closed 0) :
    (e.instantiate1' arg (k + args.length + d)).instantiateRevList args k =
      (e.instantiateRevList args k).instantiate1' arg (k + d) := by
  induction args generalizing d with
  | nil => simp
  | cons head tail ih =>
    simp only [List.length_cons, Expr.instantiateRevList]
    rw [show k + (tail.length + 1) + d =
      k + tail.length + (d + 1) by omega]
    rw [ih (d + 1) (by
      intro item hitem
      exact hargs item (by simp [hitem]))]
    exact Expr.instantiate1'_instantiate1'_closed _ _ _ k d harg
      (hargs head (by simp))

/-- For closed arguments, the source-side instantiation of a forall body used along a
translated forall telescope is Lean's reverse simultaneous instantiation
`instantiateRevList`. -/
theorem Expr.instantiateForallBody_eq_instantiateRevList
    (body : Expr) (args : List Expr)
    (hargs : ∀ arg ∈ args, arg.Closed 0) :
    Expr.instantiateForallBody body args =
      body.instantiateRevList args := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.instantiateForallBody, Expr.instantiateRevList]
    have htail : ∀ item ∈ args, item.Closed 0 := by
      intro item hitem
      exact hargs item (by simp [hitem])
    calc
      Expr.instantiateForallBody
          (body.instantiate1' arg args.length) args =
        (body.instantiate1' arg args.length).instantiateRevList args :=
          ih _ htail
      _ = (body.instantiateRevList args).instantiate1' arg := by
        simpa using Expr.instantiateRevList_instantiate1'_closed
          body arg args 0 0 (hargs arg (by simp)) htail

/-- Substitute one translated argument, typed at the first domain, into a forall
telescope translation. The result is rebuilt from the instantiated whole type, so the
source and abstract residuals stay at the same binder depth. -/
theorem Expr.ForallTelescopeTypeTranslation.inst
    (henv : env.Ordered)
    (HargType : env.HasType Us.length Δ.toCtx argTarget domainTarget)
    (Harg : TrExprS env Us Δ arg argTarget)
    (H : Expr.ForallTelescopeTypeTranslation env Us
      ((none, .vlam domainTarget) :: Δ) source arity target) :
    Expr.ForallTelescopeTypeTranslation env Us Δ
      (source.instantiate1' arg) arity (target.inst argTarget) := by
  rcases H.telescope with ⟨residual, Htelescope⟩
  have Htelescope' := Htelescope.instantiate1' arg 0
  have Htranslation := H.translation.inst henv HargType Harg
  have Htype := H.isType.instN henv .zero HargType
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Htelescope' Htranslation Htype

/-- Apply a function of the translated type to translated dependent arguments,
instantiating the source and abstract forall telescopes in lockstep. The instantiated
source residual translates to the abstract residual type, and the abstract application
has that type. -/
theorem Expr.ForallTelescopeTypeTranslation.applyTranslatedArguments
    (henv : env.WF)
    (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (H : Expr.ForallTelescopeTypeTranslation env Us Δ sourceType
      sourceArgs.length targetType)
    (Htelescope : Expr.ForallTelescope sourceType sourceArgs.length
      sourceResidual)
    (Hfn : env.HasType Us.length Δ.toCtx fnTarget targetType)
    (Hargs : List.Forall₂ (TrExprS env Us Δ) sourceArgs targetArgs)
    (Happs : VExpr.WF env Us.length Δ.toCtx
      (VExpr.mkApps fnTarget targetArgs)) :
    TrExprS env Us Δ
        (Expr.instantiateForallBody sourceResidual sourceArgs)
        (VExpr.applyForallType targetType targetArgs) ∧
      env.HasType Us.length Δ.toCtx
        (VExpr.mkApps fnTarget targetArgs)
        (VExpr.applyForallType targetType targetArgs) := by
  induction Hargs generalizing sourceType targetType fnTarget sourceResidual with
  | nil =>
    cases H with
    | nil Htranslation _Htype =>
      cases Htelescope
      simpa [Expr.instantiateForallBody, VExpr.applyForallType,
        VExpr.mkApps] using And.intro Htranslation Hfn
  | @cons sourceArg targetArg sourceArgs targetArgs Harg Hargs ih =>
    cases H with
    | @cons _ domainSource domainTarget bodySource arity bodyTarget name bi
        Hdomain HdomainType Hbody =>
      cases Htelescope with
      | cons Htail =>
        have HargType := VEnv.HasType.mkApps_head henv hctx Hfn Happs
        have Hbody' := Hbody.inst henv.ordered HargType Harg
        have Htail' := Htail.instantiate1' sourceArg 0
        have Hfn' : env.HasType Us.length Δ.toCtx
            (.app fnTarget targetArg) (bodyTarget.inst targetArg) :=
          Hfn.app HargType
        have Happs' : VExpr.WF env Us.length Δ.toCtx
            (VExpr.mkApps (.app fnTarget targetArg) targetArgs) := by
          simpa [VExpr.mkApps] using Happs
        have Hresult := ih Hbody' Htail' Hfn' Happs'
        simpa [Expr.instantiateForallBody, VExpr.applyForallType,
          VExpr.mkApps] using Hresult

end VerifyInductive
end Lean4Lean
