import Lean4Lean.Verify.TypeChecker.Reduce

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

private theorem quotMkShape {expression : Expr}
    (shape : expression.isAppOfArity ``Quot.mk 3 = true) :
    ∃ levels : List Level, ∃ typeExpr relationExpr valueExpr,
      expression = Expr.app (Expr.app (Expr.app (.const ``Quot.mk levels) typeExpr) relationExpr) valueExpr := by
  cases expression with
  | app remaining firstArg =>
    cases remaining with
    | app remaining secondArg =>
      cases remaining with
      | app remaining thirdArg =>
        cases remaining with
        | const constructorName constructorLevels =>
          simp [Expr.isAppOfArity] at shape
          simp_all
        | _ => simp [Expr.isAppOfArity] at shape
      | _ => simp [Expr.isAppOfArity] at shape
    | _ => simp [Expr.isAppOfArity] at shape
  | _ => simp [Expr.isAppOfArity] at shape

private theorem quotArgumentBelow {context : VContext} {expression : Expr} (position : Nat)
    (bound : position < expression.getAppArgs.size) :
    context.FVarsBelow expression expression.getAppArgs[position] := by
  intro property hProperty hFreeVars
  rw [← expression.mkAppList_getAppArgsList] at hFreeVars
  have allArguments := (FVarsIn.mkAppList.mp hFreeVars).2
  have member : expression.getAppArgs[position] ∈ expression.getAppArgsList := by
    rw [← expression.getAppArgs_toList]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem bound)
  exact allArguments _ member

private theorem quotAppStackTranslatedArgument
    (stack : AppStack environment levels locals function functionSemantic arguments)
    (member : argument ∈ arguments) :
    ∃ semantic, TrExprS environment levels locals argument semantic := by
  induction stack generalizing argument with
  | head => cases member
  | app functionTyping argumentTyping functionTranslation argumentTranslation tail inductionHypothesis =>
    rcases List.mem_cons.mp member with same | remaining
    · subst argument
      exact ⟨_, argumentTranslation⟩
    · exact inductionHypothesis remaining

private theorem quotTranslatedApplicationArgument {context : VContext}
    (translated : context.TrExprS expression semantic)
    (bound : position < expression.getAppArgs.size) :
    ∃ result, context.TrExprS expression.getAppArgs[position] result := by
  obtain ⟨_, stack⟩ := AppStack.build (expression.mkAppList_getAppArgsList ▸ translated)
  apply quotAppStackTranslatedArgument stack
  rw [← Expr.getAppArgs_toList]
  exact Array.mem_toList_iff.mpr (Array.getElem_mem bound)

private theorem quotRangeBelow {context : VContext} {expression base : Expr} {start : Nat}
    (bound : start ≤ expression.getAppArgs.size)
    (baseBelow : context.FVarsBelow expression base) :
    context.FVarsBelow expression (mkAppRange base start expression.getAppArgs.size expression.getAppArgs) := by
  let args := expression.getAppArgs
  let pre := args.toList.take start
  let suffix := args.toList.drop start
  have split : args.toList = pre ++ suffix := by
    exact (List.take_append_drop start args.toList).symm
  have bound' : start ≤ args.size := by simpa [args] using bound
  have preLength : pre.length = start := by
    simp [pre, List.length_take, Nat.min_eq_left bound']
  have fullLength : (pre ++ suffix).length = args.size := by
    exact (congrArg List.length split).symm.trans (by simp [args])
  have split' : args.toList = pre ++ suffix ++ [] := by simpa using split
  rw [Expr.mkAppRange_eq (l₁ := pre) (l₂ := suffix) (l₃ := [])
    split' preLength fullLength]
  intro property hProperty hFreeVars
  apply FVarsIn.mkAppList.mpr
  refine ⟨baseBelow property hProperty hFreeVars, ?_⟩
  intro argument argumentMember
  have freeVarsInExpression : FVarsIn property
      (expression.getAppFn.mkAppList expression.getAppArgs.toList) := by
    rw [expression.getAppArgs_toList, expression.mkAppList_getAppArgsList]
    exact hFreeVars
  have allArguments := (FVarsIn.mkAppList.mp freeVarsInExpression).2
  have member : argument ∈ expression.getAppArgs.toList := by
    rw [split]
    exact List.mem_append_right _ argumentMember
  exact allArguments _ member

theorem quotReduceRec.fvarsBelow {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    RecM.WF context state (quotReduceRec expression whnf) fun outcome _ =>
      ∀ reduced, outcome = some reduced → context.FVarsBelow expression reduced := by
  intro methods valid
  unfold quotReduceRec
  cases head : expression.getAppFn <;> try exact .pure nofun
  rename_i name levels
  dsimp only
  have continuation (constructorPosition argumentPosition : Nat)
      (positionBound : argumentPosition < constructorPosition) :
      ((do
        let arguments := expression.getAppArgs
        if bound : constructorPosition < arguments.size then
          let constructor ← whnf arguments[constructorPosition]
          if !constructor.isAppOfArity ``Quot.mk 3 then return none
          let result := Expr.app arguments[argumentPosition]! constructor.appArg!
          let arity := constructorPosition + 1
          if arity < arguments.size then
            return some (mkAppRange result arity arguments.size arguments)
          else return some result
        else return none) methods).WF context state
        (fun outcome _ => ∀ reduced, outcome = some reduced →
          context.FVarsBelow expression reduced) := by
    dsimp only
    split
    · rename_i bound
      dsimp only [Bind.bind, ReaderT.bind, whnf]
      obtain ⟨_, constructorTranslation⟩ :=
        quotTranslatedApplicationArgument (context := context) translated ‹_›
      refine (valid.whnf constructorTranslation).bind fun normalized _ _ ⟨below, _⟩ => ?_
      split
      · exact .pure nofun
      · rename_i shape
        have shape' : normalized.isAppOfArity ``Quot.mk 3 = true := by
          simp at shape ⊢
          exact shape
        have constructorBelow : context.FVarsBelow expression
            (getElem expression.getAppArgs constructorPosition bound) :=
          quotArgumentBelow _ bound
        have payloadBelow : context.FVarsBelow expression normalized.appArg! := by
          obtain ⟨levels, typeExpr, relationExpr, valueExpr, rfl⟩ := quotMkShape shape'
          intro property hProperty hFreeVars
          have normalizedFreeVars :=
            below property hProperty (constructorBelow property hProperty hFreeVars)
          simpa [Expr.appArg!] using normalizedFreeVars.2
        have argumentBound : argumentPosition < expression.getAppArgs.size := by omega
        have argumentBelow : context.FVarsBelow expression
            (getElem expression.getAppArgs argumentPosition argumentBound) :=
          quotArgumentBelow _ argumentBound
        have resultBelow :
            context.FVarsBelow expression
              ((getElem expression.getAppArgs argumentPosition argumentBound).app normalized.appArg!) := by
          intro property hProperty hFreeVars
          exact ⟨argumentBelow property hProperty hFreeVars,
            payloadBelow property hProperty hFreeVars⟩
        split
        · change M.WF context _ (pure (some _)) _
          exact .pure (by
            rintro _ ⟨⟩
            rw [getElem!_pos expression.getAppArgs argumentPosition argumentBound]
            exact quotRangeBelow (by omega) resultBelow)
        · change M.WF context _ (pure (some _)) _
          exact .pure (by
            rintro _ ⟨⟩
            rw [getElem!_pos expression.getAppArgs argumentPosition argumentBound]
            exact resultBelow)
    · exact .pure nofun
  by_cases isLiftName : name == ``Quot.lift
  · simp only [isLiftName, if_true]
    exact continuation 5 3 (by omega)
  · simp only [Bool.eq_false_iff.mpr isLiftName, Bool.false_eq_true, if_false]
    by_cases isInductiveName : name == ``Quot.ind
    · simp only [isInductiveName, if_true]
      exact continuation 4 3 (by omega)
    · simp only [Bool.eq_false_iff.mpr isInductiveName, Bool.false_eq_true, if_false]
      exact .pure nofun

theorem reduceRecursor.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := sorry

theorem whnfFVar.WF {c : VContext} {s : VState} (he : c.TrExprS (.fvar fv) e') :
    RecM.WF c s (whnfFVar (.fvar fv) cheapProj) fun e₁ _ =>
      c.FVarsBelow (.fvar fv) e₁ ∧ c.TrExpr e₁ e' := by
  refine .getLCtx ?_
  simp [Expr.fvarId!]; split <;> [skip; exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, h2, _, h3, _⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  refine (whnfCore.WF h3).mono fun _ _ _ ⟨h4, h5⟩ => ?_
  refine ⟨h2.trans h4, h5.defeq c.Ewf c.Δwf ?_⟩
  refine (TrExprS.fvar h1).uniq c.Ewf ?_ he
  exact .refl c.Ewf c.Δwf

theorem whnfCore'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : full e → RecM.WF c s (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · let .mdata he := he
      exact hP ▸ whnfCore'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnfCore_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have hsave {e₁ s} (h1 : c.FVarsBelow e e₁) (h2 : c.TrExpr e₁ e') :
      (save e cheapProj e₁).WF c s P := by
    simp [save]
    split <;> [skip; exact hP ▸ .pure ⟨h1, h2⟩]
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (.eqv eq ?_) ?_ --_ (.eqv h2 eq BEq.rfl) (.eqv eq ?_) ?_
      · exact he.fvarsIn.mono wf.ngen_wf
      · exact h2.fvarsIn.mono wf.ngen_wf
    exact hP ▸ ⟨.rfl, { wf with whnfCore_wf := hic wf.whnfCore_wf }, h1, h2⟩
  split <;> cases hfull
  · exact hP ▸ whnfFVar.WF he
  · rename_i fn arg _; generalize eq : fn.app arg = e at *
    have ⟨_, stk⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
    refine (whnfCore.WF stk.tr).bind fun _ s _ ⟨h1, h2⟩ => ?_
    split <;> [rename_i name dom body bi _; split]
    · let rec loop.WF {e e' i rargs f} (H : LambdaBodyN i e' f) (hi : i ≤ rargs.size) :
        ∃ n f', LambdaBodyN n e' f' ∧ n ≤ rargs.size ∧
          loop e cheapProj rargs i f = loop.cont e cheapProj rargs n f' := by
        unfold loop; split
        · split
          · refine loop.WF (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
          · exact ⟨_, _, H, hi, rfl⟩
        · exact ⟨_, _, H, hi, rfl⟩
      refine
        let ⟨i, f, h3, h4, eq⟩ := loop.WF (e' := .lam name dom body bi) (.succ .zero) <| by
          simp [← eq, Expr.getAppRevArgs_eq, Expr.getAppArgsRevList]
        eq ▸ ?_; clear eq
      simp [Expr.getAppRevArgs_eq] at h4 ⊢
      obtain ⟨l₁, l₂, h5, rfl⟩ : ∃ l₁ l₂, e.getAppArgsRevList = l₁ ++ l₂ ∧ l₂.length = i :=
        ⟨_, _, (List.take_append_drop (e.getAppArgsRevList.length - i) ..).symm, by simp; omega⟩
      simp [loop.cont, h5, List.take_of_length_le]
      rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₂ := l₁) (l₃ := l₂) (by simp) (by rfl) (by rfl)]
      have br := BetaReduce.inst_reduce (l₁ := l₂.reverse)
        [] (by simpa using h3) (Expr.instantiateList_append ..) (h := by
          have := h5 ▸ (c.mlctx.noBV ▸ he.closed).getAppArgsRevList
          simp [or_imp, forall_and] at this ⊢
          exact this.2) |>.mkAppRevList (es := l₁)
      simp [← Expr.mkAppRevList_reverse, ← Expr.mkAppRevList_append, ← h5] at br
      have := h2.rebuild_mkAppRevList c.Ewf c.Δwf stk.tr <|
        e.mkAppRevList_getAppArgsRevList ▸ he
      have ⟨_, a1, a2⟩ := this.beta c.Ewf c.Δwf br
      refine (whnfCore.WF a1).bind fun _ _ _ ⟨b1, b2⟩ => ?_
      have hb := e.mkAppRevList_getAppArgsRevList ▸ h1.mkAppRevList
      exact hsave (hb.trans (.betaReduce br) |>.trans b1) <|
        b2.defeq c.Ewf c.Δwf a2
    · refine (reduceRecursor.WF he).bind fun _ _ _ h => ?_
      split <;> [skip; exact hid]
      let ⟨h1, _, h2, eq⟩ := h _ rfl
      refine hP ▸ (whnfCore.WF h2).mono fun _ _ _ ⟨h3, h4⟩ => ?_
      exact ⟨h1.trans h3, h4.defeq c.Ewf c.Δwf eq⟩
    · rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₃ := [])
        (by simp [Expr.getAppRevArgs_toList]; rfl) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
      have {e e₁ : Expr} (hb : c.FVarsBelow e e₁) {es e₀' e'}
          (hes : c.TrExprS (e.mkAppRevList es) e₀') (he : c.TrExprS e e') (he₁ : c.TrExpr e₁ e') :
          c.FVarsBelow (e.mkAppRevList es) (e₁.mkAppRevList es) ∧
          c.TrExpr (e₁.mkAppRevList es) e₀' := by
        induction es generalizing e₁ e₀' e' with
        | nil =>
          refine ⟨hb, he₁.defeq c.Ewf c.Δwf ?_⟩
          exact he.uniq c.Ewf (.refl c.Ewf c.Δwf) hes
        | cons _ _ ih =>
          have .app h1 h2 h3 h4 := hes
          have ⟨h5, h6⟩ := ih hb h3 he he₁
          exact ⟨fun _ hP he => ⟨h5 _ hP he.1, he.2⟩,
            .app c.Ewf c.Δwf h1 h2 h6 (h4.trExpr c.Ewf c.Δwf)⟩
      have eq := e.mkAppRevList_getAppArgsRevList
      let ⟨h3, _, h4, eq⟩ := eq ▸ this h1 (eq ▸ he) stk.tr h2
      refine (whnfCore.WF h4).bind fun _ _ _ ⟨h5, h6⟩ => ?_
      refine hsave (h3.trans h5) (h6.defeq c.Ewf c.Δwf eq)
  · let .letE h1 h2 h3 h4 := he
    refine (whnfCore.WF (h4.inst_let c.Ewf.ordered h3)).bind fun _ _ _ ⟨h1, h2⟩ => ?_
    exact hsave (.trans (fun _ _ he => he.2.2.instantiate1 he.2.1) h1) h2
  · refine (reduceProj.WF he).bind fun _ _ _ H => ?_
    split
    · let ⟨h1, _, h2, eq⟩ := H _ rfl
      refine (whnfCore.WF h2).bind fun _ _ _ ⟨h3, h4⟩ => ?_
      exact hsave (h1.trans h3) (h4.defeq c.Ewf c.Δwf eq)
    · exact hsave .rfl (he.trExpr c.Ewf c.Δwf)

theorem whnf'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnf'; extract_lets F
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : RecM.WF c s (F ()) P by
    split
    any_goals exact hid
    any_goals exact hF
    · let .mdata he := he
      exact hP ▸ whnf'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF]
  simp [F]; refine .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnf_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have {e e' s n} (he : c.TrExprS e e') : (loop e n).WF c s fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    induction n generalizing s e e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.WF he).bind fun e₁ s _ ⟨h1, _, he₁, eq⟩ => ?_
    refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h3 => ?_
    split <;> [cases h3 _ rfl; skip]
    refine (reduceNat.WF he₁).bind fun _ _ _ h3 => ?_; split
    · exact .pure ⟨.trans h1 (h3 _ rfl).1, (h3 _ rfl).2.defeq c.Ewf c.Δwf eq⟩
    refine (unfoldDefinition.WF he₁).bind fun _ _ _ H => ?_
    split <;> [skip; exact .pure ⟨h1, _, he₁, eq⟩]
    have ⟨a1, _, a2, eq'⟩ := H
    refine (ih a2).mono fun _ _ _ ⟨b1, b2⟩ => ?_
    exact ⟨h1.trans <| a1.trans b1, b2.defeq c.Ewf c.Δwf <| eq'.trans c.Ewf c.Δwf eq⟩
  refine .readThe <| (this he).bind fun e₁ s _ ⟨h1, h2⟩ => ?_
  rintro _ mwf wf a s' ⟨⟩
  refine let s' := _; ⟨s', rfl, ?_⟩
  have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
    intro _ _ h
    rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
    rename_i eq
    refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (.eqv eq ?_) ?_
    · exact he.fvarsIn.mono wf.ngen_wf
    · exact h2.fvarsIn.mono wf.ngen_wf
  exact hP ▸ ⟨.rfl, { wf with whnf_wf := hic wf.whnf_wf }, h1, h2⟩
