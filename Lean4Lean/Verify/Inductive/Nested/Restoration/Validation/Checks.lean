import Lean4Lean.Verify.Inductive.Nested.Restoration.RestorationRun
import Lean4Lean.Verify.Inductive.Context

/-! # The validation passes, step by step (owner: Restoration-A)

Selection lemmas for the `forM` loops of the four validation passes of
`restoreNestedAfterInstall`, and the checker-facing content of a single successful step: a
successful `checkType`/`ensureSort` run in a `CheckerEnv` translates the checked expression
and types it in the model (`TypeChecker.checkType.WF`, `ensureSort.WF`,
`M.WF.runChecking`/`runCheckingMLC`). Ported from the source branch's
`Nested/Restoration/Validation/Checks.lean` and `Nested/Lowering/Basic.lean`
(`validateNestedAuxiliaries.WF`), with `CheckerEnv` in place of `CheckingEnv.Valid` and the
cache-mode premise. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- If `List.forM` succeeds, the step succeeds on every member of the list. -/
theorem listForM_eq_ok_of_mem {α ε : Type _} (step : α → Except ε Unit) :
    ∀ {items : List α}, items.forM step = .ok () →
      ∀ {item}, item ∈ items → step item = .ok () := by
  intro items hrun item hitem
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
    simp only [List.forM] at hrun
    cases hhead : step head with
    | error err =>
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
    | ok value =>
      rcases value with ⟨⟩
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact hhead
      · exact ih hrun htail

/-- A successful `x >>= f` in `Except` has a successful first step. -/
theorem except_bind_eq_ok {α β ε : Type _} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- The two `forM`s of a source-then-auxiliary recursor pass, as one membership statement. -/
theorem forM_append_names_eq_ok {ε : Type _} (step : Name → Except ε Unit)
    {types : List InductiveType} {auxRecNames : List Name}
    (h : (do types.forM fun type => step (mkRecName type.name)
             auxRecNames.forM step) = .ok ()) :
    ∀ recName ∈ types.map (mkRecName ·.name) ++ auxRecNames, step recName = .ok () := by
  obtain ⟨⟨⟩, h1, h2⟩ := except_bind_eq_ok h
  intro recName hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · obtain ⟨type, htype, rfl⟩ := List.mem_map.mp hmem
    exact listForM_eq_ok_of_mem (fun type : InductiveType => step (mkRecName type.name)) h1 htype
  · exact listForM_eq_ok_of_mem step h2 hmem

/-- `checkConstructorSources` rejects free variables in the constructor types. -/
theorem checkConstructorSources.closed {env : Environment} :
    ∀ {ctors : List Constructor}, checkConstructorSources env ctors = .ok () →
      ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False
  | [], _, _, h => by cases h
  | c :: cs, hctors, ctor, hctor => by
    unfold checkConstructorSources at hctors
    obtain ⟨⟨⟩, hc, hctors⟩ := except_bind_eq_ok hctors
    obtain ⟨⟨⟩, -, hcs⟩ := except_bind_eq_ok hctors
    rcases List.mem_cons.mp hctor with rfl | hctor
    · exact checkNoMVarNoFVar.closed hc
    · exact checkConstructorSources.closed hcs ctor hctor

/-- The source checks reject free variables in the constructor types. -/
theorem SourceSyntaxChecks.ctorTypesClosed {env : Environment} :
    ∀ {types : List InductiveType}, SourceSyntaxChecks env types →
      ∀ type ∈ types, ∀ ctor ∈ type.ctors, ctor.type.FVarsIn fun _ => False
  | [], _, _, h => by cases h
  | head :: tail, h, type, htype => by
    unfold SourceSyntaxChecks checkInductiveSources at h
    obtain ⟨⟨⟩, -, h⟩ := except_bind_eq_ok h
    obtain ⟨⟨⟩, hctors, htail⟩ := except_bind_eq_ok h
    rcases List.mem_cons.mp htype with rfl | htype
    · exact checkConstructorSources.closed hctors
    · exact SourceSyntaxChecks.ctorTypesClosed htail type htype

variable {safety : DefinitionSafety} {env : Environment} {venv : VEnv}

/-- A closed expression checked by `checkType` and `ensureSort` in the empty local context of
a checker environment translates to a type of the model. -/
theorem checkTypeSort.WF (C : CheckerEnv safety env venv) {lparams : List Name}
    {fuel : FuelConfig} {e : Expr} (hclosed : e.FVarsIn fun _ => False) :
    (TypeChecker.M.run env safety {} lparams fuel (do
        let type ← TypeChecker.checkType e
        TypeChecker.ensureSort type e)).WF fun _ =>
      ∃ T, TrExprS venv lparams [] e T ∧ venv.IsType lparams.length [] T := by
  have hfvars : e.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkChecking C lparams fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkChecking] using hclosed.mono fun _ h => False.elim h
  have Hcheck : (do
      let type ← TypeChecker.checkType e
      TypeChecker.ensureSort type e).WF
      (TypeChecker.VContext.mkChecking C lparams fuel) {}
      fun _ _ => ∃ T, TrExprS venv lparams [] e T ∧ venv.IsType lparams.length [] T := by
    refine (TypeChecker.checkType.WF hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype, ⟨_, hhasType.defeqU_r C.tr.wf (by trivial) hdefeq.symm⟩⟩
  exact TypeChecker.M.WF.runChecking Hcheck

/-- A closed expression checked by `checkType` in the empty local context of a checker
environment translates to a typed term of the model. -/
theorem checkTypeClosed.WF (C : CheckerEnv safety env venv) {lparams : List Name}
    {fuel : FuelConfig} {e : Expr} (hclosed : e.FVarsIn fun _ => False) :
    (TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType e)).WF fun _ =>
      ∃ e' T, TrExprS venv lparams [] e e' ∧ venv.HasType lparams.length [] e' T := by
  have hfvars : e.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkChecking C lparams fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkChecking] using hclosed.mono fun _ h => False.elim h
  refine TypeChecker.M.WF.runChecking ((TypeChecker.checkType.WF hfvars).mono ?_)
  rintro _ _ _ ⟨e', T, -, he, -, hT⟩
  exact ⟨e', T, he, hT⟩

/-- `TypeChecker.checkType` over a list of expressions in a verified context. -/
theorem checkTypeList.WF {c : TypeChecker.VContext} {s : TypeChecker.State}
    (items : List (Name × Expr))
    (hfvars : ∀ item ∈ items, item.2.FVarsIn (· ∈ c.vlctx.fvars)) :
    (items.forM fun item => do
      _ ← TypeChecker.checkType item.2).WF c s fun _ _ =>
        ∀ item ∈ items, ∃ ty e' ty', TrTyping c.venv c.lparams c.vlctx item.2 ty e' ty' := by
  induction items generalizing s with
  | nil =>
    rw [List.forM]
    exact .pure fun item hitem => by simp at hitem
  | cons head tail ih =>
    rw [List.forM]
    have Hhead : (do
        _ ← TypeChecker.checkType head.2).WF c s fun _ _ =>
          ∃ ty e' ty', TrTyping c.venv c.lparams c.vlctx head.2 ty e' ty' := by
      refine (TypeChecker.checkType.WF (hfvars head (by simp))).bind
        fun ty _ _ htyping => .pure ?_
      rcases htyping with ⟨e', ty', htyping⟩
      exact ⟨ty, e', ty', htyping⟩
    have htail : ∀ item ∈ tail, item.2.FVarsIn (· ∈ c.vlctx.fvars) :=
      fun item hitem => hfvars item (by simp [hitem])
    exact Hhead.bind fun _ _ _ hhead =>
      (ih htail).mono fun _ _ _ hall item hitem => by
        rcases List.mem_cons.mp hitem with heq | hitem
        · subst item; exact hhead
        · exact hall item hitem

end VerifyInductive
end Lean4Lean
