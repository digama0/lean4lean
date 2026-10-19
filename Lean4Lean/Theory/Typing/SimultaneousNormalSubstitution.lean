import Lean4Lean.Theory.Typing.ChurchRosser

namespace Lean4Lean.VEnv

open VExpr Params
variable [parameters : Params]

omit parameters in
private theorem substituteLift (expression : VExpr) (substitution : VExpr.Subst) :
    expression.lift.subst substitution.lift = (expression.subst substitution).lift := by
  rw [VExpr.lift_subst, VExpr.lift_eq_lift', VExpr.lift'_subst]
  congr 1
  funext index
  simp [VExpr.Subst.tail, VExpr.Subst.lift, VExpr.Subst.lift_r, ← VExpr.lift_eq_lift']

/-- A typed simultaneous substitution whose corresponding variable images are
normally equal. The lookup guard permits finite source contexts. -/
structure NormalSubstitution (target : List VExpr) (left right : VExpr.Subst)
    (source : List VExpr) : Prop where
  typed : Ctx.SubstEq env univs target left right source
  normal : ∀ {index type}, Lookup source index type → NormalEq target (left index) (right index)

theorem NormalSubstitution.lift_at
    (substitution : NormalSubstitution target left right source)
    (domainTyped : env.HasType univs source domain (.sort level))
    (domainEqual : env.IsDefEq univs target (domain.subst left) targetDomain (.sort level)) :
    NormalSubstitution (targetDomain :: target) left.lift right.lift (domain :: source) := by
  refine ⟨substitution.typed.lift_at henv.ordered domainTyped domainEqual, ?_⟩
  intro index type lookup
  cases lookup with
  | zero => exact .refl (HasType.bvar .zero)
  | succ lookup => exact (substitution.normal lookup).weakN Ctx.LiftN.one

theorem NormalSubstitution.lift
    (targetWF : OnCtx target (env.IsType univs))
    (substitution : NormalSubstitution target left right source)
    (domainTyped : env.HasType univs source domain (.sort level)) :
    NormalSubstitution (domain.subst left :: target) left.lift right.lift (domain :: source) :=
  substitution.lift_at domainTyped (domainTyped.subst henv.ordered substitution.typed.left targetWF)

/-- Reflexive terms may acquire different, normally equal variable images. -/
theorem NormalSubstitution.expression {expression type : VExpr}
    (targetWF : OnCtx target (env.IsType univs))
    (substitution : NormalSubstitution target left right source)
    (typed : env.HasType univs source expression type) :
    NormalEq target (expression.subst left) (expression.subst right) := by
  induction expression generalizing target source left right type with
  | bvar index =>
    obtain ⟨_, lookup⟩ := typed.bvar_inv henv.ordered substitution.typed.wf
    exact substitution.normal lookup
  | sort level => exact .refl (HasType.sort (typed.sort_inv henv.ordered))
  | const name levels =>
    obtain ⟨_, registered, levelsWF, arity⟩ := typed.const_inv henv.ordered substitution.typed.wf
    exact .refl (HasType.const registered levelsWF arity)
  | app function argument functionIH argumentIH =>
    obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv henv.ordered substitution.typed.wf
    have functionEqual := functionTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed
    have argumentEqual := argumentTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed
    exact .appDF functionEqual.hasType.1 functionEqual.hasType.2
      argumentEqual.hasType.1 argumentEqual.hasType.2
      (functionIH targetWF substitution functionTyped) (argumentIH targetWF substitution argumentTyped)
  | lam domain body domainIH bodyIH =>
    obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ := typed.lam_inv henv.ordered substitution.typed.wf
    have domainEqual := domainTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed
    exact .lamDF domainEqual.hasType.1 domainEqual
      (bodyIH ⟨targetWF, _, domainEqual.hasType.1⟩ (substitution.lift targetWF domainTyped) bodyTyped)
  | forallE domain body domainIH bodyIH =>
    obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ := typed.forallE_inv henv.ordered
    have domainEqual := domainTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed
    have extendedWF : OnCtx (domain.subst left :: target) (env.IsType univs) :=
      ⟨targetWF, _, domainEqual.hasType.1⟩
    have lifted := substitution.lift targetWF domainTyped
    exact .forallEDF domainEqual.hasType.1 (domainIH targetWF substitution domainTyped)
      (bodyTyped.subst henv.ordered lifted.typed.left extendedWF)
      (bodyIH extendedWF lifted bodyTyped)

/-- Simultaneously substitute related variable images into BOTH endpoints of
normal equality. This is direct congruence, with no normal transitivity or
inverse weakening. -/
theorem NormalEq.substDF
    (targetWF : OnCtx target (env.IsType univs))
    (substitution : NormalSubstitution target left right source)
    (normal : NormalEq source first second) :
    NormalEq target (first.subst left) (second.subst right) := by
  induction normal generalizing target left right with
  | refl typed => exact substitution.expression targetWF typed
  | sortDF firstWF secondWF equal => exact .sortDF firstWF secondWF equal
  | constDF registered firstWF secondWF arity equal => exact .constDF registered firstWF secondWF arity equal
  | appDF firstTyped secondTyped firstArgumentTyped secondArgumentTyped _ _ functionIH argumentIH =>
    exact .appDF
      (firstTyped.subst henv.ordered substitution.typed.left targetWF)
      (secondTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed).hasType.2
      (firstArgumentTyped.subst henv.ordered substitution.typed.left targetWF)
      (secondArgumentTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed).hasType.2
      (functionIH targetWF substitution) (argumentIH targetWF substitution)
  | lamDF firstDomainEqual secondDomainEqual _ bodyIH =>
    have leftDomainEqual := firstDomainEqual.subst henv.ordered substitution.typed.left targetWF
    have rightDomainEqual := secondDomainEqual.substDF henv.ordered substitution.typed.wf targetWF substitution.typed
    exact .lamDF leftDomainEqual rightDomainEqual
      (bodyIH ⟨targetWF, _, leftDomainEqual.hasType.1⟩
        (substitution.lift targetWF firstDomainEqual.hasType.1))
  | forallEDF domainEqual _ bodyTyped _ domainIH bodyIH =>
    have leftDomainEqual := domainEqual.subst henv.ordered substitution.typed.left targetWF
    have lifted := substitution.lift targetWF domainEqual.hasType.1
    have extendedWF : OnCtx (_ :: target) (env.IsType univs) := ⟨targetWF, _, leftDomainEqual.hasType.1⟩
    exact .forallEDF leftDomainEqual (domainIH targetWF substitution)
      (bodyTyped.subst henv.ordered lifted.typed.left extendedWF) (bodyIH extendedWF lifted)
  | etaL functionTyped _ bodyIH =>
    obtain ⟨_, typeTyped⟩ := functionTyped.isType henv.ordered substitution.typed.wf
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv henv.ordered
    have domainSubstituted := domainTyped.subst henv.ordered substitution.typed.left targetWF
    have functionSubstituted :=
      (functionTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed).hasType.2
    have extendedWF : OnCtx (_ :: target) (env.IsType univs) := ⟨targetWF, _, domainSubstituted⟩
    refine .etaL functionSubstituted ?_
    simpa only [VExpr.subst, substituteLift, VExpr.Subst.lift] using
      bodyIH extendedWF (substitution.lift targetWF domainTyped)
  | etaR functionTyped _ bodyIH =>
    obtain ⟨_, typeTyped⟩ := functionTyped.isType henv.ordered substitution.typed.wf
    obtain ⟨⟨_, domainTyped⟩, _, codomainTyped⟩ := typeTyped.forallE_inv henv.ordered
    have domainEqual := domainTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed
    have lifted := substitution.lift_at domainTyped domainEqual
    have extendedWF : OnCtx (_ :: target) (env.IsType univs) := ⟨targetWF, _, domainEqual.hasType.2⟩
    have functionSubstituted := functionTyped.subst henv.ordered substitution.typed.left targetWF
    have convertedFunction := IsDefEq.defeq (.forallEDF domainEqual
      (codomainTyped.subst henv.ordered (substitution.lift targetWF domainTyped).typed.left
        ⟨targetWF, _, domainEqual.hasType.1⟩)) functionSubstituted
    refine .etaR convertedFunction ?_
    simpa only [VExpr.subst, substituteLift, VExpr.Subst.lift] using
      bodyIH extendedWF lifted
  | proofIrrel propositionTyped firstTyped secondTyped =>
    exact .proofIrrel (propositionTyped.subst henv.ordered substitution.typed.left targetWF)
      (firstTyped.subst henv.ordered substitution.typed.left targetWF)
      (secondTyped.substDF henv.ordered substitution.typed.wf targetWF substitution.typed).hasType.2

theorem NormalSubstitution.id (localsWF : OnCtx locals (env.IsType univs)) :
    NormalSubstitution locals .id .id locals :=
  ⟨Ctx.SubstEq.id henv.ordered localsWF, fun lookup => .refl (HasType.bvar lookup)⟩

theorem NormalSubstitution.one
    (localsWF : OnCtx locals (env.IsType univs))
    (domainTyped : env.HasType univs locals domain (.sort level))
    (argumentTyped : env.HasType univs locals argument domain)
    (normal : NormalEq locals argument argument') :
    NormalSubstitution locals (.one argument) (.one argument') (domain :: locals) := by
  refine ⟨.cons (NormalSubstitution.id localsWF).typed domainTyped ?_, ?_⟩
  · simpa only [VExpr.Subst.cons_head, VExpr.Subst.cons_tail, VExpr.subst_id] using
      (normal.defeq localsWF).of_l henv localsWF argumentTyped
  · intro index type lookup
    cases lookup with
    | zero => exact normal
    | succ lookup => exact .refl (HasType.bvar lookup)

theorem NormalEq.instDF
    (localsWF : OnCtx locals (env.IsType univs))
    (domainTyped : env.HasType univs locals domain (.sort level))
    (argumentTyped : env.HasType univs locals argument domain)
    (argumentNormal : NormalEq locals argument argument')
    (bodyNormal : NormalEq (domain :: locals) body body') :
    NormalEq locals (body.inst argument) (body'.inst argument') := by
  simpa only [VExpr.inst_eq] using bodyNormal.substDF localsWF
    (NormalSubstitution.one localsWF domainTyped argumentTyped argumentNormal)

end Lean4Lean.VEnv
