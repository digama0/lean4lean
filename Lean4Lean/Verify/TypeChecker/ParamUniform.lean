import Lean4Lean.Verify.TypeChecker.Recursor
import Lean4Lean.Verify.TypeChecker.UniverseSupport

/-!
# Parameter uniformity through the reduction steps of `whnfCore` and `whnf`

The parameter-uniformity clauses (`VContext.ParamUniformBelow`) of recursor reduction (quotient and inductive,
including the K-like and structure-eta conversions of the major premise) and of definition
unfolding. These steps do not write to the caches, so their parameter-uniformity clauses are proved
separately from the typing clauses (via `RecM.Post` where the tail of a run only decides between
results that are already known).
-/

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

variable {c : VContext} {s : State}

/-! ### Quotient reduction -/

theorem quotReduceRecCont.WF_paramUniform {e : Expr} {mkPos argPos : Nat} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) (hpos : argPos < mkPos) :
    RecM.WF c s (quotReduceRecCont e whnf mkPos argPos) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.ParamUniformBelow pfx e e₁ := by
  unfold quotReduceRecCont
  extract_lets args
  have hargs_eq : args = e.getAppArgs := rfl
  simp only [hargs_eq]
  split <;> [rename_i h5; exact .pure nofun]
  have ⟨_, ha⟩ := TrExprS.getAppArgs_get he _ h5
  refine (whnf.WF_and_paramUniform ha hp).bind fun mk _ _ ⟨⟨hmb, _⟩, hmh⟩ => ?_
  split <;> [exact .pure nofun; rename_i hnot]
  have hisApp : mk.isAppOfArity ``Quot.mk 3 = true := by simpa using hnot
  obtain ⟨lsm, a1, a2, a3, rfl⟩ := Expr.isAppOfArity_three_eq_true hisApp
  simp only [Expr.appArg!]
  have main : ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → e.ParamUniformIn c.env heads As ls →
      FVarsIn P e → (Expr.app e.getAppArgs[argPos]! a3).ParamUniformIn c.env heads As ls := by
    intro heads As ls P hs hl hP
    have hp' := hs.params.fvars
    have hall := fun a (h : a ∈ e.getAppArgs) => hl.of_mem_getAppArgs hp' h
    have hm := hmh heads As ls P hs (hall _ (Array.getElem_mem _)) (hP.of_mem_getAppArgsList (by
      rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _))
    refine .app ?_ (hm.of_mem_getAppArgsList hp' (by simp [Expr.getAppArgsList]))
    have h : argPos < e.getAppArgs.size := Nat.lt_trans hpos h5
    rw [getElem!_pos e.getAppArgs argPos h]; exact hall _ (Array.getElem_mem h)
  split
  · exact .pure fun _ h heads As ls P hs hl hP => Option.some.inj h ▸
      .mkAppRange (Nat.le_refl _) (main heads As ls P hs hl hP)
        fun a h => hl.of_mem_getAppArgs hs.params.fvars h
  · exact .pure fun _ h heads As ls P hs hl hP => Option.some.inj h ▸ main heads As ls P hs hl hP

theorem quotReduceRec.WF_paramUniform (he : c.TrExprS e e') (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ => ∀ e₁, oe = some e₁ → c.ParamUniformBelow pfx e e₁ := by
  unfold quotReduceRec
  split <;> [skip; exact .pure nofun]
  split
  · exact quotReduceRecCont.WF_paramUniform he hp (by decide)
  split
  · exact quotReduceRecCont.WF_paramUniform he hp (by decide)
  exact .pure nofun

/-! ### Inductive recursor reduction -/

/-- The final step of inductive recursor reduction keeps parameter uniformity: the rule's right-hand side
mentions no head, and the remaining pieces are arguments of the recursor application and of the
converted major premise. -/
theorem inductiveReduceRecCore.paramUniformIn {info : RecursorVal} {recFn : Name} {ls : List Level}
    {e major₂ : Expr} {heads As lv} {nparams} (H : EnvParamUniform c.env heads nparams lv)
    (hAs : ∀ a ∈ As, ∃ fv, a = .fvar fv)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hfirst : info.getFirstIndexIdx ≤ e.getAppArgs.size)
    (hl : e.ParamUniformIn c.env heads As lv) (hm : major₂.ParamUniformIn c.env heads As lv) :
    ∀ r, inductiveReduceRecCore info ls e.getAppArgs major₂ = some r →
      r.ParamUniformIn c.env heads As lv := by
  intro r hr
  unfold inductiveReduceRecCore at hr
  simp only [bind, Option.bind] at hr
  split at hr <;> [rename_i rule hrule; cases hr]
  unfold getRecRuleFor at hrule
  split at hrule <;> [rename_i fn lsc hmfn; cases hrule]
  have hmem := List.mem_of_find?_eq_some hrule
  split at hr <;> [cases hr; skip]
  split at hr <;> [cases hr; skip]
  have hrhs : (rule.rhs.instantiateLevelParams info.levelParams ls).ParamUniformIn c.env heads As lv :=
    .instantiateLevelParams_of_avoids (H.rules_avoid hinfo rule hmem) (H.rules_projs hinfo rule hmem)
  have hargs := fun a (h : a ∈ e.getAppArgs) => hl.of_mem_getAppArgs hAs h
  have hmargs := fun a (h : a ∈ major₂.getAppArgs) => hm.of_mem_getAppArgs hAs h
  split at hr <;> cases hr
  · exact .mkAppRange (Nat.le_refl _)
      (.mkAppRange (Nat.le_refl _) (.mkAppRange hfirst hrhs hargs) hmargs) hargs
  · exact .mkAppRange (Nat.le_refl _) (.mkAppRange hfirst hrhs hargs) hmargs

theorem getFirstCtor_eq_some {env : Environment} (h : getFirstCtor env I = some name) :
    ∃ v, env.find? I = some (.inductInfo v) ∧ name ∈ v.ctors := by
  unfold getFirstCtor at h
  split at h <;> [rename_i v hv; cases h]
  exact ⟨v, hv, List.mem_of_head? h⟩

theorem mkNullaryCtor_eq_some {env : Environment} {A : Expr}
    (h : mkNullaryCtor env A n = some r) :
    ∃ I ls name, A.getAppFn = .const I ls ∧ getFirstCtor env I = some name ∧
      r = mkAppRange (.const name ls) 0 n A.getAppArgs := by
  unfold mkNullaryCtor at h
  rw [Expr.withApp_eq] at h
  split at h <;> [rename_i I ls hfn; cases h]
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  cases hc : getFirstCtor env I with
  | none => simp [hc] at h
  | some name => simp [hc] at h; exact ⟨I, ls, name, hfn, hc, h.symm⟩

/-- The constructor application built by `toCtorWhenK` (from the major premise's type) is
parameter-uniform: recursors in the environment never eliminate families with head constructors. -/
theorem toCtorWhenK.Post_paramUniform {info : RecursorVal} {major : Expr} {m' : VExpr} (hk : info.k = true)
    (hrec : c.env.find? recFn = some (.recInfo info))
    (hK : ∃ ind ctorName, c.env.constants.find? info.getMajorInduct = some (.inductInfo ind) ∧
      ind.ctors = [ctorName] ∧ KLikeAlignment c.venv info ctorName)
    (he : c.TrExprS major m') (hp : s.ngen.namePrefix = pfx) :
    RecM.Post c s (toCtorWhenK c.env whnf inferType isDefEq info major) fun r =>
      c.ParamUniformBelow pfx major r := by
  unfold toCtorWhenK
  split <;> [skip; exact absurd hk ‹_›]
  refine RecM.Post.bind (inferType.WF_and_paramUniform he hp) fun T _ le ⟨⟨T', hfvT, _, hTS, hT'⟩, hT⟩ => ?_
  refine RecM.Post.bind (whnf.WF_and_paramUniform hTS (State.LE.namePrefix_eq hp le))
    fun A _ _ ⟨⟨hfvA, A', hAS, hAdefeq⟩, hA⟩ => ?_
  refine RecM.Res.post ?_
  have hid : ∀ {x : Expr}, x = major → c.ParamUniformBelow pfx major x := by rintro _ rfl; exact .rfl
  split <;> [rename_i I lsI hAfn; exact .pure (hid rfl)]
  split <;> [exact .pure (hid rfl); rename_i hI]
  split <;> [exact .pure (hid rfl); skip]
  split <;> [rename_i newCtorApp hnull; exact .pure (hid rfl)]
  simp only [bne_iff_ne, ne_eq, Classical.not_not] at hI
  have hnew : c.ParamUniformBelow pfx major newCtorApp := by
    intro heads As ls P hs hl hP
    have hAok := hA heads As ls P hs (hT.1 heads As ls P hs hl hP) (hfvT P hs.up hP)
    obtain ⟨I', ls', name, hfn', hfirst, rfl⟩ := mkNullaryCtor_eq_some hnull
    rw [hAfn] at hfn'; cases hfn'
    obtain ⟨v, hv, hname⟩ := getFirstCtor_eq_some hfirst
    rw [hI] at hv
    -- the type of the major premise is a type, so it supplies the parameters
    have hsize : info.numParams ≤ A.getAppArgs.size := by
      have ⟨_, hsortT⟩ := hT'.isType c.Ewf.orderedStrong c.Δwf.toCtx
      rw [toCtorWhenK.majorType_size hK hAS (hI ▸ hAfn)
        (hsortT.defeqU_l c.Ewf c.Δwf hAdefeq.symm)]
      omega
    refine .mkAppRange hsize (.const ((hs.env.rec_major hrec).2 v hv name hname)) fun a h =>
      hAok.of_mem_getAppArgs hs.params.fvars h
  refine RecM.Res.bind fun _ => RecM.Res.bind fun b => ?_
  split
  · exact .pure hnew
  · exact .pure (hid rfl)

theorem expandEtaStruct_eq {env : Environment} {eType e r : Expr}
    (h : expandEtaStruct env eType e = r) :
    r = e ∨ ∃ I ls sInfo ctor mkInfo, eType.getAppFn = .const I ls ∧
      env.find? I = some (.inductInfo sInfo) ∧ sInfo.ctors.head? = some ctor ∧
      env.find? ctor = some (.ctorInfo mkInfo) ∧
      r = (List.range mkInfo.numFields).foldl (fun result i => .app result (.proj I i e))
        (mkAppRange (.const ctor ls) 0 mkInfo.numParams eType.getAppArgs) := by
  subst h
  unfold expandEtaStruct
  rw [Expr.withApp_eq]
  split <;> [rename_i I ls hfn; exact .inl rfl]
  split <;> [rename_i sInfo hs; exact .inl rfl]
  split <;> [rename_i ctor hc; exact .inl rfl]
  split <;> [rename_i mkInfo hm; exact .inl rfl]
  exact .inr ⟨I, ls, sInfo, ctor, mkInfo, hfn, hs, hc, hm, rfl⟩

/-- The structure-eta expansion built by `toCtorWhenStruct` is parameter-uniform. -/
theorem toCtorWhenStruct.Post_paramUniform {w : Expr} {w' : VExpr}
    (hrec : c.env.find? recFn = some (.recInfo info))
    (he : c.TrExprS w w') (hp : s.ngen.namePrefix = pfx) :
    RecM.Post c s (toCtorWhenStruct c.env whnf inferType info.getMajorInduct w) fun r =>
      c.ParamUniformBelow pfx w r := by
  have hid : ∀ {x : Expr}, x = w → c.ParamUniformBelow pfx w x := by rintro _ rfl; exact .rfl
  unfold toCtorWhenStruct
  split <;> [exact .pure (hid rfl); rename_i hguard]
  have hnonrec : c.env.isNonRecStructure info.getMajorInduct = true := by
    revert hguard; cases c.env.isNonRecStructure info.getMajorInduct <;> simp
  refine RecM.Post.bind (inferType.WF_and_paramUniform he hp) fun T _ le ⟨⟨T', hfvT, _, hTS, hT'⟩, hT⟩ => ?_
  refine RecM.Post.bind (whnf.WF_and_paramUniform hTS (State.LE.namePrefix_eq hp le))
    fun A _ _ ⟨⟨hfvA, A', hAS, hAdefeq⟩, hA⟩ => ?_
  refine RecM.Res.post ?_
  split <;> [exact .pure (hid rfl); rename_i hisConst]
  have hisConst' : A.getAppFn.isConstOf info.getMajorInduct = true := by simpa using hisConst
  obtain ⟨lsI, hAfn⟩ := Expr.isConstOf_eq_true hisConst'
  have hnew : c.ParamUniformBelow pfx w (expandEtaStruct c.env A w) := by
    intro heads As ls P hs hl hP
    have hAok := hA heads As ls P hs (hT.1 heads As ls P hs hl hP) (hfvT P hs.up hP)
    have ⟨hInot, hctors⟩ := hs.env.rec_major hrec
    rcases expandEtaStruct_eq (env := c.env) (eType := A) (e := w) rfl with h | h
    · rw [h]; exact hl
    obtain ⟨I, ls', sInfo, ctor, mkInfo, hfn, hsI, hctor, hm, hr⟩ := h
    rw [hAfn] at hfn; cases hfn
    have hinduct : mkInfo.induct = info.getMajorInduct := by
      obtain ⟨_, hEq, h, -⟩ :=
        c.listedConstructors _ sInfo hsI ctor (List.mem_of_head? hctor) _ hm
      rw [ConstantInfo.ctorInfo.inj hEq]
      exact h
    have hsize : A.getAppArgs.size = mkInfo.numParams := by
      obtain ⟨sInfo', ctor', hfind', hsingle', hnind'⟩ :=
        Kernel.Environment.isNonRecStructure_inv hnonrec
      rw [hsI] at hfind'; cases hfind'
      rw [hsingle'] at hctor; cases hctor
      obtain ⟨_, hTsort⟩ := hT'.isType c.Ewf.orderedStrong c.Δwf.toCtx
      exact VContext.structTypeArgs hAS ⟨_, hTsort.defeqU_l c.Ewf c.Δwf hAdefeq.symm⟩ hAfn hsI
        hsingle' hnind' hm hinduct
    rw [hr, foldl_app_proj]
    refine .mkAppList (.mkAppRange (Nat.le_of_eq hsize.symm)
      (.const (hctors sInfo hsI ctor (List.mem_of_head? hctor))) fun a h =>
        hAok.of_mem_getAppArgs hs.params.fvars h) fun a ha => ?_
    simp only [List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact .proj ⟨hInot, fun v hv => by rw [hsI] at hv; cases hv; exact hctors sInfo hsI⟩ hl
  refine RecM.Res.bind fun _ => RecM.Res.bind fun u => ?_
  split <;> [skip; exact .pure (hid rfl)]
  split <;> [exact .pure hnew; exact .pure (hid rfl)]

/-- Inductive recursor reduction keeps parameter uniformity. -/
theorem inductiveReduceRec.Post_paramUniform (he : c.TrExprS e e') (hp : s.ngen.namePrefix = pfx) :
    RecM.Post c s (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe =>
      ∀ e₁, oe = some e₁ → c.ParamUniformBelow pfx e e₁ := by
  unfold inductiveReduceRec
  split <;> [rename_i recFn ls hfn; exact .pure nofun]
  split <;> [rename_i info hinfo; exact .pure nofun]
  extract_lets recArgs majorIdx jpTail jpMatch
  have hrecArgs : recArgs = e.getAppArgs := rfl
  have hmajorIdx : majorIdx = info.getMajorIdx := rfl
  simp only [hrecArgs, hmajorIdx]
  split <;> [rename_i major hmajor; exact .pure nofun]
  obtain ⟨hmaj, rfl⟩ := Array.getElem?_eq_some_iff.1 hmajor
  have ⟨m', hm'⟩ := TrExprS.getAppArgs_get he _ hmaj
  -- the K-like facts
  have he'' : c.TrExprS ((Expr.const recFn ls).mkAppList e.getAppArgsList) e' := by
    rw [← hfn, e.mkAppList_getAppArgsList]; exact he
  have ⟨fn', stk⟩ := AppStack.build he''
  have .const hlc _ _ := stk.tr
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hinfo hlc
  have hfindC : c.env.constants.find? recFn = some (.recInfo info) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  obtain ⟨-, hK⟩ := c.recursorRules hfindC hsafe
  have hmem : e.getAppArgs[info.getMajorIdx] ∈ e.getAppArgsList := by
    rw [← Expr.getAppArgs_toList]; exact Array.getElem_mem_toList _
  -- the tail
  have htail : ∀ (major₂ : Expr), c.FVarsBelow e.getAppArgs[info.getMajorIdx] major₂ →
      c.ParamUniformBelow pfx e.getAppArgs[info.getMajorIdx] major₂ →
      ∀ e₁, inductiveReduceRecCore info ls e.getAppArgs major₂ = some e₁ →
        c.ParamUniformBelow pfx e e₁ := by
    intro major₂ hfv hh e₁ h heads As lv P hs hl hP
    exact inductiveReduceRecCore.paramUniformIn hs.env hs.params.fvars hinfo
      (by simp only [RecursorVal.getMajorIdx, RecursorVal.getFirstIndexIdx] at hmaj ⊢; omega) hl
      (hh heads As lv P hs (hl.of_mem_getAppArgsList hs.params.fvars hmem)
        (hP.of_mem_getAppArgsList hmem)) e₁ h
  -- after the K conversion
  have hjp : ∀ {s₁ : State} (m₁ : Expr) {m₁' : VExpr}, s₁.ngen.namePrefix = pfx →
      c.FVarsBelow e.getAppArgs[info.getMajorIdx] m₁ →
      c.ParamUniformBelow pfx e.getAppArgs[info.getMajorIdx] m₁ → c.TrExprS m₁ m₁' →
      RecM.Post c s₁ (jpMatch () m₁) fun oe => ∀ e₁, oe = some e₁ → c.ParamUniformBelow pfx e e₁ := by
    intro s₁ m₁ m₁' hp₁ hfv₁ hh₁ hm₁S
    simp only [jpMatch, jpTail]
    refine RecM.Post.bind (whnf.WF_and_paramUniform hm₁S hp₁) fun w s₂ le ⟨⟨hfvw, w', hwS, _⟩, hhw⟩ => ?_
    have hp₂ := State.LE.namePrefix_eq hp₁ le
    split
    · rename_i n
      refine RecM.Post.pure fun e₁ h => htail _ (hfv₁.trans (hfvw.trans
        (fun _ _ _ => FVarsIn.natLitToConstructor))) ?_ e₁ h
      exact fun heads As lv P hs _ _ => .natLitToConstructor hs.env
    · rename_i str _
      cases hwS with | lit hcl hlit => ?_
      refine RecM.Post.bind (whnf.WF_and_paramUniform hlit hp₂) fun major₂ _ _ ⟨⟨hfv₂, _⟩, hh₂⟩ => ?_
      refine RecM.Post.pure fun e₁ h => htail _ (hfv₁.trans (hfvw.trans
        ((FVarsBelow.trans (e₂ := .strLitToConstructor str)
          (fun _ _ _ => FVarsIn.strLitToConstructor) hfv₂)))) ?_ e₁ h
      exact fun heads As lv P hs _ _ => hh₂ heads As lv P hs
        (.strLitToConstructor hs.env (c.strLitsDeclared hcl))
        FVarsIn.strLitToConstructor
    · refine RecM.Post.bind ((toCtorWhenStruct.WF_all hwS).and_post
        (toCtorWhenStruct.Post_paramUniform hinfo hwS hp₂)) fun major₂ _ _ ⟨⟨⟨hfv₂, _⟩, _⟩, hh₂⟩ => ?_
      refine RecM.Post.pure fun e₁ h => htail _ (hfv₁.trans (hfvw.trans hfv₂)) ?_ e₁ h
      exact (hh₁.trans hfv₁ hhw).trans (hfv₁.trans hfvw) hh₂
  split
  · rename_i hk
    refine RecM.Post.bind ((toCtorWhenK.WF_all hk (hK hk) hm').and_post
      (toCtorWhenK.Post_paramUniform hk hinfo (hK hk) hm' hp)) fun m₁ s₁ le ⟨⟨⟨h1, ⟨_, h2, _⟩⟩, _⟩, hh⟩ => ?_
    exact hjp m₁ (State.LE.namePrefix_eq hp le) h1 hh h2
  · exact hjp _ hp .rfl .rfl hm'

/-- Recursor reduction keeps parameter uniformity. -/
theorem reduceRecursor.WF_paramUniform (he : c.TrExprS e e') (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (reduceRecursor e) fun oe _ => ∀ e₁, oe = some e₁ → c.ParamUniformBelow pfx e e₁ := by
  unfold reduceRecursor
  refine .getEnv ?_
  extract_lets jp
  have hjp : ∀ {s : State}, s.ngen.namePrefix = pfx → RecM.WF c s (jp ()) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.ParamUniformBelow pfx e e₁ := by
    intro s hp
    simp only [jp]
    refine ((inductiveReduceRec.WF he).and_post (inductiveReduceRec.Post_paramUniform he hp)).bind
      fun oi _ _ ⟨_, hi⟩ => ?_
    split
    · exact .pure fun _ h => hi _ h
    · exact .pure nofun
  split
  · refine (quotReduceRec.WF_paramUniform he hp).bind fun oq _ le hqq => ?_
    split
    · exact .pure fun _ h => hqq _ h
    · exact hjp (State.LE.namePrefix_eq hp le)
  · exact hjp hp

/-! ### Definition unfolding -/

theorem instantiateDeltaValue_paramUniformIn {heads As lv} {nparams}
    (H : EnvParamUniform c.env heads nparams lv)
    (hlookup : c.env.find? name = some info) (hdelta : info.deltaValue? = some value) :
    (instantiateDeltaValue info levels).ParamUniformIn c.env heads As lv := by
  simp only [instantiateDeltaValue, hdelta, Option.get!_some]
  exact .instantiateLevelParams_of_avoids (H.value_avoids hlookup hdelta)
    (H.value_projs hlookup hdelta)

theorem unfoldDefinitionCore.WF_paramUniform :
    RecM.WF c s (unfoldDefinitionCore e) fun result _ => ∀ e', result = some e' →
      ∀ heads As lv nparams, EnvParamUniform c.env heads nparams lv → e'.ParamUniformIn c.env heads As lv := by
  dsimp [unfoldDefinitionCore]
  split <;> [refine .getEnv ?_; exact .pure nofun]
  split
  · rename_i name levels optInfo info hdelta
    obtain ⟨_, hlookup, ⟨_, hv⟩, _, ⟨⟩, hlen⟩ := isDelta_is_some.mp hdelta
    have hscope : ∀ heads As lv nparams, EnvParamUniform c.env heads nparams lv →
        (instantiateDeltaValue info levels).ParamUniformIn c.env heads As lv :=
      fun _ _ _ _ H => instantiateDeltaValue_paramUniformIn H hlookup hv
    split
    · refine .get ?_
      split
      · rename_i hcache
        refine .stateWF fun wf => .pure ?_
        obtain ⟨_, _, _, ⟨⟩, hc, rfl⟩ := wf.unfold_wf hcache
        cases hlookup.symm.trans hc
        exact fun _ h => Option.some.inj h ▸ hscope
      · refine .bind (Q := fun _ _ => True) ?_ fun _ _ _ _ =>
          .pure fun _ h => Option.some.inj h ▸ hscope
        rintro _ mwf wf _ _ ⟨⟩
        refine ⟨_, rfl, .rfl, { wf with unfold_wf := ?_ }, ⟨⟩⟩
        intro e e'
        simp only [Std.HashMap.getElem?_insert]
        split <;> [rintro ⟨⟩; exact (wf.unfold_wf ·)]
        rename_i eq
        rw [BEq.comm, Expr.eqv_const] at eq
        exact ⟨_, _, _, eq, hlookup, rfl⟩
    · exact .pure fun _ h => Option.some.inj h ▸ hscope
  · exact .pure nofun

theorem unfoldDefinition.WF_paramUniform :
    RecM.WF c s (unfoldDefinition e) fun result _ => ∀ e', result = some e' →
      c.ParamUniformBelow pfx e e' := by
  simp [unfoldDefinition]
  split
  · refine unfoldDefinitionCore.WF_paramUniform.bind fun result _ _ hresult => ?_
    cases result with
    | none => exact .pure nofun
    | some body =>
      refine .pure ?_
      intro out hout heads As lv P hs hl _
      cases Option.some.inj hout
      exact .mkAppRevRange (Nat.le_refl _) (hresult _ rfl heads As lv _ hs.env) fun a h =>
        hl.of_mem_getAppArgsRevList hs.params.fvars (by
          rw [← Expr.getAppRevArgs_toList]; exact Array.mem_toList_iff.2 h)
  · exact unfoldDefinitionCore.WF_paramUniform.mono fun _ _ _ H e' h heads As lv P hs _ _ =>
      H e' h heads As lv _ hs.env

end Lean4Lean.TypeChecker.Inner

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

/-- The parameter-uniformity clause of `whnfCore` together with the fact that a constant is returned
unchanged. -/
theorem whnfCore.WF_paramUniform_const {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ =>
      c.ParamUniformBelow pfx e e₁ ∧ ∀ n us, e = .const n us → e₁ = e := by
  by_cases hc : ∃ n us, e = .const n us
  · obtain ⟨n, us, rfl⟩ := hc
    exact ((whnfCore.WF_paramUniform he hp).and whnfCore.WF_const).mono fun _ _ _ ⟨h1, h2⟩ =>
      ⟨h1, fun _ _ _ => h2⟩
  · exact (whnfCore.WF_paramUniform he hp).mono fun _ _ _ h1 =>
      ⟨h1, fun n us h => absurd ⟨n, us, h⟩ hc⟩

end Lean4Lean.TypeChecker.Inner
