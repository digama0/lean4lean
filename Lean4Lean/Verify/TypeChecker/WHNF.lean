import Lean4Lean.Verify.TypeChecker.Reduce

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem reduceRecursor.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e cheapRec cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := sorry

theorem whnfFVar.WF {c : VContext} {s : VState} (he : c.TrExprS (.fvar fv) e') :
    RecM.WF c s (whnfFVar (.fvar fv) cheapRec cheapProj) fun e₁ _ =>
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

theorem reduceProj.WF {c : VContext} {s : VState} (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProj i e cheapRec cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := sorry

theorem whnfCore'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapRec cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnfCore'; extract_lets F G
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hG : full e → RecM.WF c s (G ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hG rfl
    · let .mdata he := he
      exact (whnfCore'.WF he).bind fun _ _ _ h => hP ▸ .pure h
    · refine .getLCtx ?_; split <;> [exact hid; exact hG rfl]
  simp [G]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnfCore_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have hsave {e₁ s} (h1 : c.FVarsBelow e e₁) (h2 : c.TrExpr e₁ e') :
      (save e cheapRec cheapProj e₁).WF c s P := by
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
  unfold F; split <;> cases hfull
  · simp; exact hP ▸ whnfFVar.WF he
  · rename_i fn arg _; generalize eq : fn.app arg = e at *
    rw [Expr.withRevApp_eq]
    have ⟨_, stk⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
    refine (whnfCore.WF stk.tr).bind fun _ s _ ⟨h1, h2⟩ => ?_
    split <;> [rename_i name dom body bi _; split]
    · let rec loop.WF {e e' i rargs f} (H : LambdaBodyN i e' f) (hi : i ≤ rargs.size) :
        ∃ n f', LambdaBodyN n e' f' ∧ n ≤ rargs.size ∧
          loop e cheapRec cheapProj rargs i f = loop.cont e cheapRec cheapProj rargs n f' := by
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
  · let .letE h1 h2 h3 h4 := he; simp
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
  unfold whnf'; extract_lets F G
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hG : RecM.WF c s (G ()) P by
    split
    any_goals exact hid
    any_goals exact hG
    · let .mdata he := he
      exact (whnf'.WF he).bind fun _ _ _ h => hP ▸ .pure h
    · refine .getLCtx ?_; split <;> [exact hid; exact hG]
  simp [G]; refine .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnf_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  unfold F
  have {e e' s n} (he : c.TrExprS e e') : (loop e n).WF c s fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    induction n generalizing s e e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.WF he).bind fun e₁ s _ ⟨h1, _, he₁, eq⟩ => ?_
    refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h3 => ?_
    extract_lets F1 F2; split <;> [cases h3 _ rfl; skip]
    refine .pureBind ?_; unfold F2
    refine (reduceNat.WF he₁).bind fun _ _ _ h3 => ?_; split
    · exact .pure ⟨.trans h1 (h3 _ rfl).1, (h3 _ rfl).2.defeq c.Ewf c.Δwf eq⟩
    refine .pureBind ?_; unfold F1; split <;> [skip; exact .pure ⟨h1, _, he₁, eq⟩]
    have ⟨a1, _, a2, eq'⟩ := (unfoldDefinition.WF he₁ ‹_› :)
    refine (ih a2).mono fun _ _ _ ⟨b1, b2⟩ => ?_
    exact ⟨h1.trans <| a1.trans b1, b2.defeq c.Ewf c.Δwf <| eq'.trans c.Ewf c.Δwf eq⟩
  refine (this he).bind fun e₁ s _ ⟨h1, h2⟩ => ?_
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
