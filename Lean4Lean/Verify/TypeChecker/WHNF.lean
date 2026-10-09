import Lean4Lean.Verify.TypeChecker.Recursor
import Lean4Lean.Verify.TypeChecker.ParamUniform
import Lean4Lean.Verify.TypeChecker.UniverseSupport

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem reduceRecursor.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceRecursor
  refine .getEnv ?_
  extract_lets jp
  have hjp : ∀ {s : State}, RecM.WF c s (jp ()) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    intro s
    simp only [jp]
    refine (inductiveReduceRec.WF he).bind fun oi _ _ hi => ?_
    split
    · exact .pure fun _ h => hi _ h
    · exact .pure nofun
  split
  · rename_i hq
    refine (quotReduceRec.WF he (c.quotCoherent hq)).bind fun oq _ _ hqq => ?_
    split
    · exact .pure fun _ h => hqq _ h
    · exact hjp
  · exact hjp

theorem reduceRecursor.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e) fun oe _ => ∀ e₁, oe = some e₁ → c.LevelsBelow e e₁ := by
  unfold reduceRecursor
  refine .getEnv ?_
  extract_lets jp
  have hjp : ∀ {s : State}, RecM.WF c s (jp ()) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.LevelsBelow e e₁ := by
    intro s
    simp only [jp]
    refine (inductiveReduceRec.WF_all he).bind fun oi _ _ hi => ?_
    split
    · exact .pure fun _ h => (hi _ h).2
    · exact .pure nofun
  split
  · refine (quotReduceRec.WF_levels he).bind fun oq _ _ hqq => ?_
    split
    · exact .pure fun _ h => hqq _ h
    · exact hjp
  · exact hjp

theorem reduceNat_eq_none (h : e.isApp = false) : reduceNat e = pure none := by
  have : e.getAppNumArgs = 0 := by
    rw [Expr.getAppNumArgs_eq]; cases e <;> simp_all [Expr.isApp, Expr.getAppArgsRevList]
  unfold reduceNat; simp [this]

theorem whnfFVar.WF_all {c : VContext} {s : State} (he : c.TrExprS (.fvar fv) e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (whnfFVar (.fvar fv) cheapProj) fun e₁ _ =>
      ((c.FVarsBelow (.fvar fv) e₁ ∧ c.TrExpr e₁ e' ∧
      (∀ A B, e' = .forallE A B → c.TrExprS e₁ e')) ∧ c.LevelsBelow (.fvar fv) e₁) ∧
      c.ParamUniformBelow pfx (.fvar fv) e₁ := by
  refine .getLCtx ?_
  simp [Expr.fvarId!]; split <;>
    [skip; exact .pure ⟨⟨⟨.rfl, he.trExpr c.Ewf c.Δwf, fun _ _ _ => he⟩, .rfl⟩, .rfl⟩]
  rename_i decl h
  have hfind := h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨v', ty', h1, h2, _, h3, _⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  have .fvar h1' := he
  cases h1.symm.trans h1'
  refine ((whnfCore.WF_below_of_fvarsIn h3).and (whnfCore.WF_paramUniform h3 hp)).mono
    fun _ _ _ ⟨⟨⟨h4, h5, h6⟩, h7⟩, h8⟩ => ⟨⟨⟨h2.trans h4, h5, h6⟩, ?_⟩, ?_⟩
  · intro Us P hs _ hP
    exact h7 Us P hs ((hs.2 _ _ hP hfind).2 _ LocalDecl.value?_ldecl_true) (h2 P hs.1 hP)
  · intro heads As ls P hs _ hP
    exact h8 heads As ls P hs ((hs.decls _ _ hP hfind).2 _ LocalDecl.value?_ldecl_true)
      (h2 P hs.up hP)

theorem whnfFVar.WF {c : VContext} {s : State} (he : c.TrExprS (.fvar fv) e') :
    RecM.WF c s (whnfFVar (.fvar fv) cheapProj) fun e₁ _ =>
      c.FVarsBelow (.fvar fv) e₁ ∧ c.TrExpr e₁ e' ∧
      (∀ A B, e' = .forallE A B → c.TrExprS e₁ e') :=
  (whnfFVar.WF_all he rfl).mono fun _ _ _ h => h.1.1

theorem whnfCore'.WF_all {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ =>
      ((c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧ (∀ A B, e' = .forallE A B → c.TrExprS e₁ e')) ∧
      c.LevelsBelow e e₁) ∧ c.ParamUniformBelow s.ngen.namePrefix e e₁ := by
  generalize hpfx : s.ngen.namePrefix = pfx
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : State) => _) = P
  have hid {s} : RecM.WF c s (pure e) P :=
    hP ▸ .pure ⟨⟨⟨.rfl, he.trExpr c.Ewf c.Δwf, fun _ _ _ => he⟩, .rfl⟩, .rfl⟩
  suffices hF : full e → RecM.WF c s (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · let .mdata he := he
      refine hP ▸ (whnfCore'.WF_all he).mono fun _ _ _ ⟨h1, h2⟩ => ⟨h1, ?_⟩
      subst hpfx
      exact fun heads As ls P hs hl hP => h2 heads As ls P hs hl.mdata_inv hP
    · refine .getLCtx ?_; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3, h5⟩ := (wf.whnfCore_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨⟨⟨h1, h3.defeq c.Ewf c.Δwf ?_, fun _ _ hAB =>
      (he.cacheKey_not_forall h5 hAB).elim⟩, wf.whnfCore_levels eq he.fvarsIn⟩,
      hpfx ▸ wf.whnfCore_paramUniform eq he.fvarsIn⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have hsave {e₁ s} (hs : s.ngen.namePrefix = pfx) (h1 : c.FVarsBelow e e₁)
      (h2 : c.TrExpr e₁ e') (h3 : ∀ A B, e' = .forallE A B → c.TrExprS e₁ e')
      (h4 : c.LevelsBelow e e₁) (h5 : c.ParamUniformBelow pfx e e₁) :
      (save e cheapProj e₁).WF c s P := by
    simp [save]
    split <;> [skip; exact hP ▸ .pure ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩]
    rename_i hcacheKey
    have hkey : whnfCacheKey e = true := by
      simpa only [Bool.and_eq_true] using hcacheKey |> And.right
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (by rw [← whnfCacheKey_eqv eq]; exact hkey) (.eqv eq ?_) ?_
      · exact he.fvarsIn.mono wf.ngen_wf
      · exact h2.fvarsIn.mono wf.ngen_wf
    have h5' := h5; rw [← hs] at h5'
    exact hP ▸ ⟨.rfl,
      { wf with
        whnfCore_wf := hic wf.whnfCore_wf
        whnfCore_levels := wf.whnfCore_levels.insert h4
        whnfCore_paramUniform := wf.whnfCore_paramUniform.insert h5' },
      ⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
  split <;> cases hfull
  · exact hP ▸ whnfFVar.WF_all he hpfx
  · have hne : ∀ A B, e' ≠ .forallE A B := by cases he; nofun
    rename_i fn arg _; generalize eq : fn.app arg = e at *
    have ⟨_, stk⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
    refine ((whnfCore.WF_below stk.tr).and (whnfCore.WF_paramUniform_const stk.tr hpfx)).bind
      fun f s le ⟨⟨h1, hl1, h2⟩, hh1, hc1⟩ => ?_
    have hs := State.LE.namePrefix_eq hpfx le
    have hhead : ∀ Us P, c.UniverseScope Us P → e.levelParamsIn Us = true → FVarsIn P e →
        ∀ f, c.LevelsBelow e.getAppFn f →
        (f.mkAppRevList e.getAppArgsRevList).levelParamsIn Us = true :=
      fun Us P hs hl hP _ hl1 => Expr.levelParamsIn_mkAppRevList
        (hl1 Us P hs (Expr.levelParamsIn_getAppFn hl) hP.getAppFn)
        (Expr.levelParamsIn_getAppArgsRevList hl)
    have hhead_hit : (∀ n us, e.getAppFn ≠ .const n us) → ∀ heads As ls P,
        c.ParamUniformScope pfx heads As ls P → e.ParamUniformIn c.env heads As ls → FVarsIn P e →
        (f.mkAppRevList e.getAppArgsRevList).ParamUniformIn c.env heads As ls := by
      intro hnc heads As ls P hs hl hP
      have hf := hh1 heads As ls P hs (hl.getAppFn_of_not_head fun c us h => absurd h (hnc c us))
        hP.getAppFn
      exact .mkAppRevList hf fun a ha => hl.of_mem_getAppArgsRevList hs.params.fvars ha
    split <;> [rename_i name dom body bi hflam; split]
    · have hnc : ∀ n us, e.getAppFn ≠ .const n us := by
        intro n us h; have := hc1 n us h; rw [h] at this; cases this
      let rec loop.WF {e e' i rargs f} (H : LambdaBodyN i e' f) (hi : i ≤ rargs.size) :
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
      refine ((whnfCore.WF_below a1).and (whnfCore.WF_paramUniform a1 hs)).bind
        fun _ s₂ le₂ ⟨⟨b1, bl, b2⟩, bh⟩ => ?_
      have hb := e.mkAppRevList_getAppArgsRevList ▸ h1.mkAppRevList
      refine hsave (State.LE.namePrefix_eq hs le₂) (hb.trans (.betaReduce br) |>.trans b1)
        (b2.defeq c.Ewf c.Δwf a2) (fun A B h => (hne A B h).elim) (fun Us P hs hl hP => ?_)
        (fun heads As ls P hs hl hP => ?_)
      · exact bl Us P hs (br.levelParamsIn (h5 ▸ hhead Us P hs hl hP _ hl1))
          ((hb.trans (.betaReduce br)) P hs.1 hP)
      · exact bh heads As ls P hs ((hhead_hit hnc heads As ls P hs hl hP).betaReduce
          hs.params.fvars br) ((hb.trans (.betaReduce br)) P hs.up hP)
    · refine (((reduceRecursor.WF he).and (reduceRecursor.WF_levels he)).and
        (reduceRecursor.WF_paramUniform he hs)).bind fun _ s₂ le₂ ⟨⟨h, hlr⟩, hhr⟩ => ?_
      split <;> [skip; exact hid]
      let ⟨h1, _, h2, eq⟩ := h _ rfl
      refine hP ▸ ((whnfCore.WF_below h2).and
        (whnfCore.WF_paramUniform h2 (State.LE.namePrefix_eq hs le₂))).mono
        fun _ _ _ ⟨⟨h3, hl3, h4⟩, hh3⟩ => ?_
      exact ⟨⟨⟨h1.trans h3, h4.defeq c.Ewf c.Δwf eq, fun A B h => (hne A B h).elim⟩,
        (hlr _ rfl).trans h1 hl3⟩, (hhr _ rfl).trans h1 hh3⟩
    · rename_i hneq
      have hnc : ∀ n us, e.getAppFn ≠ .const n us := by
        intro n us h; exact hneq (by rw [hc1 n us h]; exact BEq.rfl)
      rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₃ := [])
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
      refine ((whnfCore.WF_below h4).and (whnfCore.WF_paramUniform h4 hs)).bind
        fun _ _ le₂ ⟨⟨h5, hl5, h6⟩, hh5⟩ => ?_
      exact hsave (State.LE.namePrefix_eq hs le₂) (h3.trans h5) (h6.defeq c.Ewf c.Δwf eq)
        (fun A B h => (hne A B h).elim)
        (VContext.LevelsBelow.trans (fun Us P hs hl hP => hhead Us P hs hl hP _ hl1) h3 hl5)
        (VContext.ParamUniformBelow.trans (fun heads As ls P hs hl hP => hhead_hit hnc heads As ls P hs hl hP)
          h3 hh5)
  · let .letE h1 h2 h3 h4 := he
    refine ((whnfCore.WF_below_of_fvarsIn (h4.inst_let c.Ewf.ordered h3)).and
      (whnfCore.WF_paramUniform (h4.inst_let c.Ewf.ordered h3) hpfx)).bind
      fun _ _ le ⟨⟨⟨h1, h2, h5⟩, hl⟩, hh⟩ => ?_
    refine hsave (State.LE.namePrefix_eq hpfx le)
      (.trans (fun _ _ he => he.2.2.instantiate1 he.2.1) h1) h2 h5 ?_ ?_
    · refine VContext.LevelsBelow.trans (fun Us P hs hl' hP => ?_)
        (fun _ _ he => he.2.2.instantiate1 he.2.1) hl
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at hl'
      exact Expr.levelParamsIn_instantiate1 hl'.2 hl'.1.2
    · refine VContext.ParamUniformBelow.trans (fun heads As ls P hs hl' hP => ?_)
        (fun _ _ he => he.2.2.instantiate1 he.2.1) hh
      have ⟨_, hv, hb⟩ := hl'.letE_inv
      exact hb.instantiate1' hs.params.fvars hv 0
  · have hne : ∀ A B, e' ≠ .forallE A B := by cases he with | proj _ h2 => cases h2; nofun
    refine (((reduceProj.WF he).and (reduceProj.WF_levels he)).and (reduceProj.WF_paramUniform he hpfx)).bind
      fun _ _ le ⟨⟨H, HL⟩, HH⟩ => ?_
    have hs := State.LE.namePrefix_eq hpfx le
    split
    · let ⟨h1, _, h2, eq⟩ := H _ rfl
      refine ((whnfCore.WF_below h2).and (whnfCore.WF_paramUniform h2 hs)).bind
        fun _ _ le₂ ⟨⟨h3, hl3, h4⟩, hh3⟩ => ?_
      exact hsave (State.LE.namePrefix_eq hs le₂) (h1.trans h3) (h4.defeq c.Ewf c.Δwf eq)
        (fun A B h => (hne A B h).elim) ((HL _ rfl).trans h1 hl3) ((HH _ rfl).trans h1 hh3)
    · exact hsave hs .rfl (he.trExpr c.Ewf c.Δwf) (fun _ _ _ => he) .rfl .rfl

theorem whnfCore'.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧ (∀ A B, e' = .forallE A B → c.TrExprS e₁ e') :=
  (whnfCore'.WF_all he).mono fun _ _ _ h => h.1.1

theorem whnfCore'.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ => c.LevelsBelow e e₁ :=
  (whnfCore'.WF_all he).mono fun _ _ _ h => h.1.2

theorem whnfCore'.WF_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ => c.ParamUniformBelow s.ngen.namePrefix e e₁ :=
  (whnfCore'.WF_all he).mono fun _ _ _ h => h.2

theorem whnf'.WF_all {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ =>
      ((c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧ (∀ A B, e' = .forallE A B → c.TrExprS e₁ e')) ∧
      c.LevelsBelow e e₁) ∧ c.ParamUniformBelow s.ngen.namePrefix e e₁ := by
  generalize hpfx : s.ngen.namePrefix = pfx
  unfold whnf'; extract_lets F
  generalize hP : (fun e₁ (_ : State) => _) = P
  have hid {s} : RecM.WF c s (pure e) P :=
    hP ▸ .pure ⟨⟨⟨.rfl, he.trExpr c.Ewf c.Δwf, fun _ _ _ => he⟩, .rfl⟩, .rfl⟩
  suffices hF : RecM.WF c s (F ()) P by
    split
    any_goals exact hid
    any_goals exact hF
    · let .mdata he := he
      refine hP ▸ (whnf'.WF_all he).mono fun _ _ _ ⟨h1, h2⟩ => ⟨h1, ?_⟩
      subst hpfx
      exact fun heads As ls P hs hl hP => h2 heads As ls P hs hl.mdata_inv hP
    · refine .getLCtx ?_; split <;> [exact hid; exact hF]
  simp [F]; refine .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3, h5⟩ := (wf.whnf_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨⟨⟨h1, h3.defeq c.Ewf c.Δwf ?_, fun _ _ hAB =>
      (he.cacheKey_not_forall h5 hAB).elim⟩, wf.whnf_levels eq he.fvarsIn⟩,
      hpfx ▸ wf.whnf_paramUniform eq he.fvarsIn⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have {e e' s n} (he : c.TrExprS e e') (hs : s.ngen.namePrefix = pfx) : (loop e n).WF c s
      fun e₁ _ =>
      ((c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧ (∀ A B, e' = .forallE A B → c.TrExprS e₁ e')) ∧
      c.LevelsBelow e e₁) ∧ c.ParamUniformBelow pfx e e₁ := by
    induction n generalizing s e e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.WF_all he).bind
      fun e₁ s₁ le₁ ⟨⟨⟨h1, ⟨_, he₁, eq⟩, hs'⟩, hl1⟩, hh1⟩ => ?_
    rw [hs] at hh1
    have hs₁ := State.LE.namePrefix_eq hs le₁
    refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ le₂ h3 => ?_
    have hs₂ := State.LE.namePrefix_eq hs₁ le₂
    split <;> [cases h3 _ rfl; skip]
    by_cases hf : ∃ A B, e' = .forallE A B
    · obtain ⟨A, B, rfl⟩ := hf
      have hs' := hs' _ _ rfl
      have ⟨hna, hnc⟩ := hs'.forallE_shape
      rw [reduceNat_eq_none hna]; refine .pureBind ?_
      rw [unfoldDefinition_eq_none hna hnc]; refine .pureBind ?_
      exact .pure ⟨⟨⟨h1, ⟨_, he₁, eq⟩, fun _ _ _ => hs'⟩, hl1⟩, hh1⟩
    have hne : ∀ A B, e' ≠ .forallE A B := fun A B h => hf ⟨_, _, h⟩
    refine (reduceNat.WF_all he₁).bind fun _ _ le₃ h3 => ?_
    have hs₃ := State.LE.namePrefix_eq hs₂ le₃
    split
    · exact .pure ⟨⟨⟨.trans h1 (h3 _ rfl).1.1, (h3 _ rfl).1.2.defeq c.Ewf c.Δwf eq,
        fun A B h => (hne A B h).elim⟩, fun Us _ _ _ _ => (h3 _ rfl).2.1 Us⟩,
        fun heads As ls P hs _ _ => (h3 _ rfl).2.2.paramUniformIn hs.env⟩
    refine (((unfoldDefinition.WF he₁).and_forall fun Us (h : e₁.levelParamsIn Us = true) =>
      unfoldDefinition.WF_levelParams he₁ h).and (unfoldDefinition.WF_paramUniform (pfx := pfx))).bind
      fun _ _ le₄ ⟨⟨H, HL⟩, HH⟩ => ?_
    split <;> [skip; exact .pure ⟨⟨⟨h1, ⟨_, he₁, eq⟩, fun A B h => (hne A B h).elim⟩, hl1⟩, hh1⟩]
    have ⟨a1, _, a2, eq'⟩ := H
    refine (ih a2 (State.LE.namePrefix_eq hs₃ le₄)).mono fun _ _ _ ⟨⟨⟨b1, b2, _⟩, bl⟩, bh⟩ => ?_
    refine ⟨⟨⟨h1.trans <| a1.trans b1, b2.defeq c.Ewf c.Δwf <| eq'.trans c.Ewf c.Δwf eq,
      fun A B h => (hne A B h).elim⟩, fun Us P hs hl hP => ?_⟩, ?_⟩
    · exact bl Us P hs (HL Us (hl1 Us P hs hl hP) _ rfl) (a1 P hs.1 (h1 P hs.1 hP))
    · exact hh1.trans h1 ((HH _ rfl).trans a1 bh)
  refine .readThe <| (this he hpfx).bind fun e₁ s le ⟨⟨⟨h1, h2, h3⟩, hl⟩, hh⟩ => ?_
  have hs := State.LE.namePrefix_eq hpfx le
  split
  · rename_i hkey
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (by rw [← whnfCacheKey_eqv eq]; exact hkey) (.eqv eq ?_) ?_
      · exact he.fvarsIn.mono wf.ngen_wf
      · exact h2.fvarsIn.mono wf.ngen_wf
    have hh' := hh; rw [← hs] at hh'
    exact hP ▸ ⟨.rfl,
      { wf with
        whnf_wf := hic wf.whnf_wf
        whnf_levels := wf.whnf_levels.insert hl
        whnf_paramUniform := wf.whnf_paramUniform.insert hh' },
      ⟨⟨h1, h2, h3⟩, hl⟩, hh⟩
  · exact hP ▸ .pureBind (.pure ⟨⟨⟨h1, h2, h3⟩, hl⟩, hh⟩)

theorem whnf'.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧ (∀ A B, e' = .forallE A B → c.TrExprS e₁ e') :=
  (whnf'.WF_all he).mono fun _ _ _ h => h.1.1

theorem whnf'.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ => c.LevelsBelow e e₁ :=
  (whnf'.WF_all he).mono fun _ _ _ h => h.1.2

theorem whnf'.WF_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ => c.ParamUniformBelow s.ngen.namePrefix e e₁ :=
  (whnf'.WF_all he).mono fun _ _ _ h => h.2

/-- `whnfCore'` returns a constant unchanged. -/
theorem whnfCore'.WF_const {c : VContext} {s : State} :
    RecM.WF c s (whnfCore' (.const n us) cheapProj) fun e₁ _ => e₁ = .const n us := by
  unfold whnfCore'; exact .pure rfl

/-- `whnf'` returns a forall unchanged. -/
theorem whnf'.WF_forall {c : VContext} {s : State} :
    RecM.WF c s (whnf' (.forallE n t b bi)) fun e₁ _ => e₁ = .forallE n t b bi := by
  unfold whnf'; exact .pure rfl
