import Lean4Lean.Verify.TypeChecker.FrameInfer

/-!
# Frame lemma: weak-head normalization
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

namespace Inner

theorem quotReduceRec.framed (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (quotReduceRec e Inner.whnf) (OptionGhostFree G) := by
  have hargs := he.getAppArgs
  have hcont : ∀ mkPos argPos, RecM.PreservesGhostRestriction G (quotReduceRecCont e Inner.whnf mkPos argPos)
      (OptionGhostFree G) := by
    intro mkPos argPos
    unfold quotReduceRecCont; dsimp only
    split
    · refine (RecM.PreservesGhostRestriction.whnf (hargs.getElem _)).bind fun mk hmk => ?_
      split
      · exact .pure OptionGhostFree.none
      · have h1 : GhostFree G (Expr.app e.getAppArgs[argPos]! mk.appArg!) :=
          ⟨hargs.getElem! _, hmk.appArg!⟩
        split
        · exact .pure (OptionGhostFree.some (h1.mkAppRange hargs))
        · exact .pure (OptionGhostFree.some h1)
    · exact .pure OptionGhostFree.none
  unfold quotReduceRec
  split
  · split
    · exact hcont _ _
    · split
      · exact hcont _ _
      · exact .pure OptionGhostFree.none
  · exact .pure OptionGhostFree.none

theorem mkNullaryCtor_gf (ht : GhostFree G type) :
    OptionGhostFree G (mkNullaryCtor env type n) := by
  unfold mkNullaryCtor
  rw [Expr.withApp_eq]
  split
  · rename_i dName ls h
    have hls : GhostFree G (.const dName ls) := h ▸ ht.getAppFn
    intro r hr
    simp only [Option.bind_eq_bind] at hr
    cases h' : getFirstCtor env dName <;> simp [h'] at hr
    subst hr
    exact GhostFree.mkAppRange (f := .const _ ls) hls ht.getAppArgs
  · nofun

theorem toCtorWhenK.framed (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (toCtorWhenK env Inner.whnf (fun e => Inner.inferType e) Inner.isDefEq info e)
      (GhostFree G) := by
  unfold toCtorWhenK
  split
  · refine (RecM.PreservesGhostRestriction.inferType he).bind fun _ h => (RecM.PreservesGhostRestriction.whnf h).bind fun appType ht => ?_
    split <;> [skip; exact .pure he]
    split <;> [exact .pure he; skip]
    split <;> [exact .pure he; skip]
    split <;> [skip; exact .pure he]
    rename_i c hc
    have hc := mkNullaryCtor_gf ht hc
    refine (RecM.PreservesGhostRestriction.inferType hc).bind fun _ h => (RecM.PreservesGhostRestriction.isDefEq ht h).bind fun _ _ => ?_
    split <;> [exact .pure hc; exact .pure he]
  · exact .panic GhostFree.default

theorem expandEtaStruct_gf (ht : GhostFree G eType) (he : GhostFree G e) :
    GhostFree G (expandEtaStruct env eType e) := by
  unfold expandEtaStruct
  rw [Expr.withApp_eq]
  simp only [Id.run]
  split <;> [skip; exact he]
  rename_i I ls h
  have hls : GhostFree G (.const I ls) := h ▸ ht.getAppFn
  split <;> [skip; exact he]
  split <;> [skip; exact he]
  split <;> [skip; exact he]
  have hfold : ∀ (l : List Nat) (r : Expr), GhostFree G r →
      GhostFree G (l.foldl (fun result i => result.app (.proj I i e)) r) := by
    intro l; induction l with
    | nil => exact fun _ h => h
    | cons i l ih => exact fun r h => ih _ ⟨h, he⟩
  exact hfold _ _ (GhostFree.mkAppRange (f := .const _ ls) hls ht.getAppArgs)

theorem toCtorWhenStruct.framed (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (toCtorWhenStruct env Inner.whnf (fun e => Inner.inferType e) n e) (GhostFree G) := by
  unfold toCtorWhenStruct
  split
  · exact .pure he
  refine (RecM.PreservesGhostRestriction.inferType he).bind fun _ h => (RecM.PreservesGhostRestriction.whnf h).bind fun eType ht => ?_
  split <;> [exact .pure he; skip]
  refine (RecM.PreservesGhostRestriction.inferType ht).bind fun _ h => (RecM.PreservesGhostRestriction.whnf h).bind fun _ _ => ?_
  split <;> [skip; exact .pure he]
  split <;> [exact .pure (expandEtaStruct_gf ht he); exact .pure he]

theorem inductiveReduceRecTail_gf {info : RecursorVal} (hrules : ∀ r ∈ info.rules, GhostFree G r.rhs)
    (hls : ∀ l ∈ ls, l.hasMVar' = false) (hargs : GhostFreeArr G recArgs) (hmajor : GhostFree G major) :
    OptionGhostFree G (inductiveReduceRecTail info ls recArgs major) := by
  intro r hr
  unfold inductiveReduceRecTail at hr
  simp only [getRecRuleFor, Option.bind_eq_bind] at hr
  split at hr
  · rename_i rule hrule
    have hmem : rule ∈ info.rules := by
      split at hrule
      · exact List.mem_of_find?_eq_some hrule
      · cases hrule
    have h0 := (hrules _ hmem).instantiateLevelParams (ps := info.levelParams) hls
    repeat' split at hr
    all_goals first
      | (simp at hr; done)
      | (cases hr
         repeat (first | refine GhostFree.mkAppRange ?_ hargs | refine GhostFree.mkAppRange ?_ hmajor.getAppArgs)
         exact h0)
  · cases hr

theorem inductiveReduceRec.framed (henv : EnvGhostFree G env) (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (inductiveReduceRec env e Inner.whnf (fun e => Inner.inferType e) Inner.isDefEq)
      (OptionGhostFree G) := by
  unfold inductiveReduceRec
  split <;> [skip; exact .pure OptionGhostFree.none]
  rename_i recFn ls hfn
  have hls : ∀ l ∈ ls, l.hasMVar' = false := by
    have := he.getAppFn; rw [hfn] at this; exact this
  split <;> [skip; exact .pure OptionGhostFree.none]
  rename_i info hinfo
  have hrules := (henv hinfo).rules rfl
  have hargs := he.getAppArgs
  dsimp only
  split <;> [skip; exact .pure OptionGhostFree.none]
  rename_i major hmajor
  have hmajor := hargs.getElem? hmajor
  have tail : ∀ m, GhostFree G m → OptionGhostFree G (inductiveReduceRecTail info ls e.getAppArgs m) :=
    fun _ hm => inductiveReduceRecTail_gf hrules hls hargs hm
  have k : ∀ major, GhostFree G major → RecM.PreservesGhostRestriction G (do
      let __do_lift ← Inner.whnf major
      match __do_lift with
        | Expr.lit (Literal.natVal n) =>
          pure (inductiveReduceRecTail info ls e.getAppArgs (Expr.natLitToConstructor n))
        | Expr.lit (Literal.strVal s) => do
          let major ← Inner.whnf (Expr.strLitToConstructor s)
          pure (inductiveReduceRecTail info ls e.getAppArgs major)
        | e_1 => do
          let major ← toCtorWhenStruct env Inner.whnf (fun e => Inner.inferType e)
            info.getMajorInduct e_1
          pure (inductiveReduceRecTail info ls e.getAppArgs major)) (OptionGhostFree G) := by
    intro major hmajor
    refine (RecM.PreservesGhostRestriction.whnf hmajor).bind fun m hm => ?_
    split
    · exact .pure (tail _ FVarsIn.natLitToConstructor)
    · exact (RecM.PreservesGhostRestriction.whnf FVarsIn.strLitToConstructor).bind fun _ h => .pure (tail _ h)
    · exact (toCtorWhenStruct.framed hm).bind fun _ h => .pure (tail _ h)
  split
  · exact (toCtorWhenK.framed hmajor).bind fun _ h => k _ h
  · exact k _ hmajor

theorem reduceRecursor.framed (he : GhostFree G e) : RecM.PreservesGhostRestriction G (reduceRecursor e) (OptionGhostFree G) := by
  unfold reduceRecursor
  refine RecM.PreservesGhostRestriction.getEnv_ghostFree.bind fun env henv => ?_
  have k := (inductiveReduceRec.framed henv he).bind fun o (ho : OptionGhostFree G o) =>
    (show RecM.PreservesGhostRestriction G (match o with | some r => pure (some r) | _ => pure none) (OptionGhostFree G) by
      split
      · exact .pure (OptionGhostFree.some (ho rfl))
      · exact .pure OptionGhostFree.none)
  split
  · refine (quotReduceRec.framed he).bind fun o ho => ?_
    split
    · exact .pure (OptionGhostFree.some (ho rfl))
    · exact k
  · exact k

theorem isLetFVar_congr {l₁ l₂ : LocalContext} {id : FVarId}
    (h : (l₁.find? id).map (·.setIndex 0) = (l₂.find? id).map (·.setIndex 0)) :
    isLetFVar l₁ id = isLetFVar l₂ id := by
  unfold isLetFVar
  revert h
  cases l₁.find? id with
  | none => cases l₂.find? id <;> simp
  | some d₁ =>
    cases l₂.find? id with
    | none => simp
    | some d₂ => cases d₁ <;> cases d₂ <;> simp [LocalDecl.setIndex]

theorem whnfFVar.framed {id : FVarId} (hid : ¬ G id) :
    RecM.PreservesGhostRestriction G (whnfFVar (.fvar id) cheapProj) (GhostFree G) := by
  unfold whnfFVar
  refine RecM.PreservesGhostRestriction.getLCtx_find hid (fun l₁ l₂ h => ?_) fun l hl => ?_
  · revert h
    simp only [Expr.fvarId!]
    cases l₁.find? id with
    | none => cases l₂.find? id with
      | none => simp
      | some d₂ => simp
    | some d₁ =>
      cases l₂.find? id with
      | none => simp
      | some d₂ =>
        cases d₁ <;> cases d₂ <;> simp [LocalDecl.setIndex]
        all_goals (intros; subst_vars; rfl)
  · simp only [Expr.fvarId!]
    split
    · rename_i h; exact RecM.PreservesGhostRestriction.whnfCore ((hl h).2 value?_ldecl)
    · exact .pure hid

theorem reduceProjCoreCont.framed (hc : GhostFree G c) :
    RecM.PreservesGhostRestriction G (reduceProjCoreCont structName idx c) (OptionGhostFree G) := by
  unfold reduceProjCoreCont
  rw [Expr.withApp_eq]
  have hargs := hc.getAppArgs
  split <;> [skip; exact .pure OptionGhostFree.none]
  refine RecM.PreservesGhostRestriction.getEnv.bind fun env _ => ?_
  refine (RecM.PreservesGhostRestriction.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  repeat (split <;> [skip; exact .pure OptionGhostFree.none])
  exact .pure fun _ h => hargs.getElem? h

theorem reduceProjCore.framed (hs : GhostFree G struct) :
    RecM.PreservesGhostRestriction G (reduceProjCore structName idx struct) (OptionGhostFree G) := by
  unfold reduceProjCore; dsimp only
  split
  · exact (RecM.PreservesGhostRestriction.whnf FVarsIn.strLitToConstructor).bind fun _ hc =>
      reduceProjCoreCont.framed hc
  · exact (RecM.PreservesGhostRestriction.pure hs).bind fun _ hc => reduceProjCoreCont.framed hc

theorem reduceProj.framed (hs : GhostFree G struct) :
    RecM.PreservesGhostRestriction G (reduceProj structName idx struct cheapProj) (OptionGhostFree G) := by
  unfold reduceProj
  refine RecM.PreservesGhostRestriction.bind (P := GhostFree G) ?_ fun c hc => reduceProjCore.framed hc
  split
  · exact RecM.PreservesGhostRestriction.whnfCore hs
  · exact RecM.PreservesGhostRestriction.whnf hs

theorem whnfCore'.save.framed (hr : GhostFree G r) :
    RecM.PreservesGhostRestriction G (whnfCore'.save e cheapProj r) (GhostFree G) := by
  unfold whnfCore'.save; dsimp only
  split
  · refine RecM.PreservesGhostRestriction.bind (RecM.PreservesGhostRestriction.modify ?_) fun _ _ => .pure hr
    intro s hs
    refine ⟨⟨hs.1, hs.2, ?_, hs.4, hs.5, hs.6⟩, .rfl⟩
    intro a b h
    simp only [Std.HashMap.getElem?_insert] at h; split at h
    · cases h; exact hr
    · exact hs.3 h
  · exact .pure hr

theorem whnfCore'.loop.framed (hrargs : GhostFreeArr G rargs) :
    ∀ m f, GhostFree G f → RecM.PreservesGhostRestriction G (whnfCore'.loop e cheapProj rargs m f) (GhostFree G) := by
  have hcont : ∀ m f, GhostFree G f → RecM.PreservesGhostRestriction G (whnfCore'.loop.cont e cheapProj rargs m f) (GhostFree G) := by
    intro m f hf
    unfold whnfCore'.loop.cont; dsimp only
    exact (RecM.PreservesGhostRestriction.whnfCore ((hf.instantiateRange hrargs).mkAppRevRange hrargs)).bind
      fun _ h => save.framed h
  intro m f hf
  induction f generalizing m with
  | lam _ _ body _ _ ih =>
    unfold whnfCore'.loop
    split
    · exact ih _ hf.2
    · exact hcont _ _ hf
  | _ => unfold whnfCore'.loop; exact hcont _ _ hf

theorem whnfCore'.framed : ∀ {e : Expr} (cheapProj : Bool), GhostFree G e →
    RecM.PreservesGhostRestriction G (whnfCore' e cheapProj) (GhostFree G)
  | e, cheapProj, he => by
    unfold whnfCore'
    extract_lets jp
    have hjp : RecM.PreservesGhostRestriction G (jp ()) (GhostFree G) := by
      dsimp only [jp]
      refine RecM.PreservesGhostRestriction.get.bind fun st hst => ?_
      split
      · rename_i r hr; exact .pure (hst.whnfCore hr)
      split
      any_goals exact .panic GhostFree.default
      · rename_i id _; exact whnfFVar.framed he
      · rw [Expr.withRevApp_eq]
        have hrargs := he.getAppRevArgs
        refine (RecM.PreservesGhostRestriction.whnfCore he.getAppFn).bind fun f hf => ?_
        split
        · exact whnfCore'.loop.framed hrargs _ _ hf.2
        · split
          · refine (reduceRecursor.framed he).bind fun o ho => ?_
            split
            · exact RecM.PreservesGhostRestriction.whnfCore (ho rfl)
            · exact .pure he
          · exact (RecM.PreservesGhostRestriction.whnfCore (hf.mkAppRevRange hrargs)).bind fun _ h =>
              save.framed h
      · exact (RecM.PreservesGhostRestriction.whnfCore (GhostFree.instantiate1 he.2.2 he.2.1)).bind fun _ h =>
          save.framed h
      · rename_i _ _ s _
        refine (reduceProj.framed (struct := s) he).bind fun o ho => ?_
        split
        · exact (RecM.PreservesGhostRestriction.whnfCore (ho rfl)).bind fun _ h => save.framed h
        · exact save.framed he
    split
    any_goals exact .pure he
    · rename_i _ e'; exact whnfCore'.framed (e := e') cheapProj he
    · rename_i id _
      refine RecM.PreservesGhostRestriction.getLCtx_find he (fun l₁ l₂ h => by rw [isLetFVar_congr h]) fun _ _ => ?_
      split
      · exact .pure he
      · exact hjp
    all_goals exact hjp

theorem isDelta_gf (henv : EnvGhostFree G env) (h : isDelta env e = some d) :
    ∀ ⦃v⦄, d.deltaValue? = some v → GhostFree G v := by
  unfold isDelta at h
  split at h <;> [skip; cases h]
  split at h <;> [skip; cases h]
  rename_i ci hci
  split at h <;> [cases h; cases h]
  exact (henv hci).deltaValue

theorem instantiateDeltaValue_gf (hd : ∀ ⦃v⦄, d.deltaValue? = some v → GhostFree G v)
    (hls : ∀ l ∈ ls, l.hasMVar' = false) : GhostFree G (instantiateDeltaValue d ls) := by
  unfold instantiateDeltaValue
  cases h : d.deltaValue? with
  | none => exact GhostFree.default.instantiateLevelParams hls
  | some v => exact (hd h).instantiateLevelParams hls

theorem unfoldDefinitionCore.framed (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (unfoldDefinitionCore e) (OptionGhostFree G) := by
  unfold unfoldDefinitionCore
  split <;> [skip; exact .pure OptionGhostFree.none]
  rename_i ls
  refine RecM.PreservesGhostRestriction.getEnv_ghostFree.bind fun env henv => ?_
  split <;> [skip; exact .pure OptionGhostFree.none]
  rename_i d hd
  have hv := instantiateDeltaValue_gf (isDelta_gf henv hd) he
  split
  · refine RecM.PreservesGhostRestriction.get.bind fun st hst => ?_
    split
    · rename_i r hr; exact .pure (OptionGhostFree.some (hst.unfold hr))
    · refine RecM.PreservesGhostRestriction.bind (RecM.PreservesGhostRestriction.modify ?_) fun _ _ => .pure (OptionGhostFree.some hv)
      intro s hs
      refine ⟨⟨hs.1, hs.2, hs.3, hs.4, ?_, hs.6⟩, .rfl⟩
      intro a b h
      simp only [Std.HashMap.getElem?_insert] at h; split at h
      · cases h; exact hv
      · exact hs.5 h
  · exact .pure (OptionGhostFree.some hv)

theorem unfoldDefinition.framed (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (unfoldDefinition e) (OptionGhostFree G) := by
  unfold unfoldDefinition
  split
  · refine (unfoldDefinitionCore.framed he.getAppFn).bind fun o ho => ?_
    split
    · exact .pure (OptionGhostFree.some ((ho rfl).mkAppRevRange he.getAppRevArgs))
    · exact .pure OptionGhostFree.none
  · exact unfoldDefinitionCore.framed he

theorem reduceNative_gf : (reduceNative env e).WF (OptionGhostFree G) := by
  unfold reduceNative
  split
  · split
    · exact .throw
    · split
      · exact .throw
      · exact .pure OptionGhostFree.none
  · exact .pure OptionGhostFree.none

theorem GhostFree.natLit : GhostFree G (.lit (.natVal n)) := trivial

theorem reduceBinNatOp.framed (ha : GhostFree G a) (hb : GhostFree G b) :
    RecM.PreservesGhostRestriction G (reduceBinNatOp f a b) (OptionGhostFree G) := by
  unfold reduceBinNatOp
  refine (RecM.PreservesGhostRestriction.whnf ha).bind fun _ _ => ?_
  split <;> [skip; exact .pure OptionGhostFree.none]
  refine (RecM.PreservesGhostRestriction.whnf hb).bind fun _ _ => ?_
  split <;> [exact .pure (OptionGhostFree.some GhostFree.natLit); exact .pure OptionGhostFree.none]

theorem reducePow.framed (ha : GhostFree G a) (hb : GhostFree G b) :
    RecM.PreservesGhostRestriction G (reducePow a b) (OptionGhostFree G) := by
  unfold reducePow
  refine (RecM.PreservesGhostRestriction.whnf ha).bind fun _ _ => ?_
  split <;> [skip; exact .pure OptionGhostFree.none]
  refine (RecM.PreservesGhostRestriction.whnf hb).bind fun _ _ => ?_
  split <;> [skip; exact .pure OptionGhostFree.none]
  split <;> [exact .pure OptionGhostFree.none; exact .pure (OptionGhostFree.some GhostFree.natLit)]

theorem reduceBinNatPred.framed (ha : GhostFree G a) (hb : GhostFree G b) :
    RecM.PreservesGhostRestriction G (reduceBinNatPred f a b) (OptionGhostFree G) := by
  unfold reduceBinNatPred
  refine (RecM.PreservesGhostRestriction.whnf ha).bind fun _ _ => ?_
  split <;> [skip; exact .pure OptionGhostFree.none]
  refine (RecM.PreservesGhostRestriction.whnf hb).bind fun _ _ => ?_
  split <;> [exact .pure (OptionGhostFree.some FVarsIn.boolLit); exact .pure OptionGhostFree.none]

theorem reduceNat.framed (he : GhostFree G e) : RecM.PreservesGhostRestriction G (Inner.reduceNat e) (OptionGhostFree G) := by
  unfold Inner.reduceNat
  extract_lets nargs jp f
  by_cases h1 : (nargs == 1) = true
  · rw [if_pos h1]
    by_cases h2 : (f == Expr.const `Nat.succ []) = true
    · rw [if_pos h2]
      refine (RecM.PreservesGhostRestriction.whnf he.appArg!).bind fun _ _ => ?_
      split
      · exact .pure (OptionGhostFree.some GhostFree.natLit)
      · exact .pure OptionGhostFree.none
    · rw [if_neg h2]; exact .pure OptionGhostFree.none
  · rw [if_neg h1]
    by_cases h2 : (nargs == 2) = true
    · rw [if_pos h2]
      split
      · have ha := he.1.2; have hb := he.2
        exact .ite (reduceBinNatOp.framed ha hb) <| .ite (reduceBinNatOp.framed ha hb) <|
          .ite (reduceBinNatOp.framed ha hb) <| .ite (reducePow.framed ha hb) <|
          .ite (reduceBinNatOp.framed ha hb) <| .ite (reduceBinNatOp.framed ha hb) <|
          .ite (reduceBinNatOp.framed ha hb) <| .ite (reduceBinNatPred.framed ha hb) <|
          .ite (reduceBinNatPred.framed ha hb) <| .ite (reduceBinNatOp.framed ha hb) <|
          .ite (reduceBinNatOp.framed ha hb) <| .ite (reduceBinNatOp.framed ha hb) <|
          .ite (reduceBinNatOp.framed ha hb) <| .ite (reduceBinNatOp.framed ha hb) <|
          .pure OptionGhostFree.none
      · exact .pure OptionGhostFree.none
    · rw [if_neg h2]; exact .pure OptionGhostFree.none

theorem whnf'.loop.framed : ∀ (fuel : Nat) (t : Expr), GhostFree G t →
    RecM.PreservesGhostRestriction G (whnf'.loop t fuel) (GhostFree G) := by
  intro fuel
  induction fuel with
  | zero => intro t _; unfold whnf'.loop; exact .throw
  | succ fuel ih =>
    intro t ht
    unfold whnf'.loop
    refine RecM.PreservesGhostRestriction.getEnv.bind fun env _ => ?_
    refine (whnfCore'.framed false ht).bind fun t ht => ?_
    refine (RecM.PreservesGhostRestriction.liftExcept (reduceNative_gf (G := G))).bind fun o ho => ?_
    split
    · exact .pure (ho rfl)
    refine (reduceNat.framed ht).bind fun o ho => ?_
    split
    · exact .pure (ho rfl)
    refine (unfoldDefinition.framed ht).bind fun o ho => ?_
    split
    · exact ih _ (ho rfl)
    · exact .pure ht

theorem whnf'.framed : ∀ {e : Expr}, GhostFree G e → RecM.PreservesGhostRestriction G (whnf' e) (GhostFree G)
  | e, he => by
    unfold whnf'
    extract_lets jp
    have hjp : RecM.PreservesGhostRestriction G (jp ()) (GhostFree G) := by
      dsimp only [jp]
      refine RecM.PreservesGhostRestriction.get.bind fun st hst => ?_
      split
      · rename_i r hr; exact .pure (hst.whnf hr)
      refine RecM.PreservesGhostRestriction.read (fun _ _ h => by rw [h.ctx_eq.2.2.1, h.ctx_eq.2.2.2.2]) fun _ _ _ => ?_
      refine (whnf'.loop.framed _ _ he).bind fun r hr => ?_
      split
      · refine RecM.PreservesGhostRestriction.bind (RecM.PreservesGhostRestriction.modify ?_) fun _ _ => .pure hr
        intro s hs
        refine ⟨⟨hs.1, hs.2, hs.3, ?_, hs.5, hs.6⟩, .rfl⟩
        intro a b h
        simp only [Std.HashMap.getElem?_insert] at h; split at h
        · cases h; exact hr
        · exact hs.4 h
      · exact .pure hr
    split
    any_goals exact .pure he
    · rename_i _ e'; exact whnf'.framed (e := e') he
    · rename_i id
      refine RecM.PreservesGhostRestriction.getLCtx_find he (fun l₁ l₂ h => by rw [isLetFVar_congr h]) fun _ _ => ?_
      split
      · exact .pure he
      · exact hjp
    all_goals exact hjp

end Inner
end Lean4Lean.TypeChecker
