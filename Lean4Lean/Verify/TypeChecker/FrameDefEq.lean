import Lean4Lean.Verify.TypeChecker.FrameWHNF

/-!
# Frame lemma: definitional equality
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

theorem RecM.PreservesGhostRestriction.orM {x y : RecM Bool} (hx : RecM.PreservesGhostRestriction G x fun _ => True)
    (hy : RecM.PreservesGhostRestriction G y fun _ => True) : RecM.PreservesGhostRestriction G (x <||> y) fun _ => True := by
  unfold _root_.orM
  refine hx.bind fun b _ => ?_
  split
  · exact .pure trivial
  · exact hy

theorem RecM.PreservesGhostRestriction.toLBoolM {x : RecM Bool} (hx : RecM.PreservesGhostRestriction G x fun _ => True) :
    RecM.PreservesGhostRestriction G (toLBoolM x) fun _ => True := by
  unfold Lean.toLBoolM
  exact hx.bind fun _ _ => .pure trivial

theorem Inner.OptionGhostFree.get! {o : Option Expr} (h : Inner.OptionGhostFree G o) : GhostFree G o.get! := by
  cases o with
  | none => simp only [Option.get!]; exact GhostFree.panic
  | some e => exact h rfl

/-- The expressions carried by a reduction status are ghost-free. -/
def ReductionStatusGhostFree (G : FVarId → Prop) : ReductionStatus → Prop
  | .continue tn sn | .unknown tn sn | .false tn sn => GhostFree G tn ∧ GhostFree G sn
  | .true => True

namespace Inner

theorem isDefEqLambda.framed : ∀ {t s : Expr} {subst : Array Expr}, GhostFree G t → GhostFree G s →
    GhostFreeArr G subst → RecM.PreservesGhostRestriction G (isDefEqLambda t s subst) fun _ => True
  | t, s, subst, ht, hs, hsub => by
    unfold isDefEqLambda
    split
    · rename_i tDom tBody _ name sDom sBody bi
      have hsT : GhostFree G (sDom.instantiateRev subst) := hs.1.instantiateRev hsub
      have k : ∀ o : Option Expr, OptionGhostFree G o → RecM.PreservesGhostRestriction G
          (do
            if (← readThe Context).fuel.cacheMode.isGlobal && !tBody.hasLooseBVars &&
                !sBody.hasLooseBVars then
              isDefEqLambda tBody sBody (subst.push default)
            else
              let sType := o.getD (sDom.instantiateRev subst)
              withLocalDecl name bi sType fun fv => isDefEqLambda tBody sBody (subst.push fv)
            : RecM Bool) fun _ => True := by
        intro o ho
        refine .read (fun _ _ h => by rw [h.ctx_eq.2.2.2.2]) fun _ _ _ => .ite ?_ ?_
        · exact isDefEqLambda.framed ht.2 hs.2 (GhostFreeArr.push hsub GhostFree.default)
        refine .withLocalDecl ?_ fun id hid =>
          isDefEqLambda.framed ht.2 hs.2 (GhostFreeArr.push hsub (show GhostFree G (.fvar id) from hid))
        cases o with
        | none => exact hsT
        | some x => exact ho rfl
      split
      · exact (RecM.PreservesGhostRestriction.pure OptionGhostFree.none).bind k
      · refine (RecM.PreservesGhostRestriction.isDefEq (ht.1.instantiateRev hsub) hsT).bind fun _ _ => ?_
        split
        · exact .pure trivial
        · exact (RecM.PreservesGhostRestriction.pure (OptionGhostFree.some hsT)).bind k
    · exact RecM.PreservesGhostRestriction.isDefEq (ht.instantiateRev hsub) (hs.instantiateRev hsub)

theorem isDefEqForall.framed : ∀ {t s : Expr} {subst : Array Expr}, GhostFree G t → GhostFree G s →
    GhostFreeArr G subst → RecM.PreservesGhostRestriction G (isDefEqForall t s subst) fun _ => True
  | t, s, subst, ht, hs, hsub => by
    unfold isDefEqForall
    split
    · rename_i tDom tBody _ name sDom sBody bi
      have hsT : GhostFree G (sDom.instantiateRev subst) := hs.1.instantiateRev hsub
      have k : ∀ o : Option Expr, OptionGhostFree G o → RecM.PreservesGhostRestriction G
          (do
            if (← readThe Context).fuel.cacheMode.isGlobal && !tBody.hasLooseBVars &&
                !sBody.hasLooseBVars then
              isDefEqForall tBody sBody (subst.push default)
            else
              let sType := o.getD (sDom.instantiateRev subst)
              withLocalDecl name bi sType fun fv => isDefEqForall tBody sBody (subst.push fv)
            : RecM Bool) fun _ => True := by
        intro o ho
        refine .read (fun _ _ h => by rw [h.ctx_eq.2.2.2.2]) fun _ _ _ => .ite ?_ ?_
        · exact isDefEqForall.framed ht.2 hs.2 (GhostFreeArr.push hsub GhostFree.default)
        refine .withLocalDecl ?_ fun id hid =>
          isDefEqForall.framed ht.2 hs.2 (GhostFreeArr.push hsub (show GhostFree G (.fvar id) from hid))
        cases o with
        | none => exact hsT
        | some x => exact ho rfl
      split
      · exact (RecM.PreservesGhostRestriction.pure OptionGhostFree.none).bind k
      · refine (RecM.PreservesGhostRestriction.isDefEq (ht.1.instantiateRev hsub) hsT).bind fun _ _ => ?_
        split
        · exact .pure trivial
        · exact (RecM.PreservesGhostRestriction.pure (OptionGhostFree.some hsT)).bind k
    · exact RecM.PreservesGhostRestriction.isDefEq (ht.instantiateRev hsub) (hs.instantiateRev hsub)

theorem quickIsDefEq.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (quickIsDefEq t s useHash) fun _ => True := by
  unfold quickIsDefEq
  refine RecM.PreservesGhostRestriction.bind (RecM.PreservesGhostRestriction.modifyGet ?_) fun b _ => ?_
  · intro st hst
    obtain ⟨⟩ := st
    exact ⟨⟨hst.1, hst.2, hst.3, hst.4, hst.5, hst.6⟩, .rfl⟩
  split
  · exact .pure trivial
  split
  · exact .toLBoolM (isDefEqLambda.framed ht hs GhostFreeArr.empty)
  · exact .toLBoolM (isDefEqForall.framed ht hs GhostFreeArr.empty)
  · exact .pure trivial
  · exact .toLBoolM (RecM.PreservesGhostRestriction.isDefEq ht hs)
  · exact .panic trivial
  · exact .pure trivial
  · exact .pure trivial

theorem isDefEqArgs.framed : ∀ {t s : Expr}, GhostFree G t → GhostFree G s →
    RecM.PreservesGhostRestriction G (isDefEqArgs t s) fun _ => True
  | t, s, ht, hs => by
    unfold isDefEqArgs
    split
    · rename_i tf ta sf sa
      refine (RecM.PreservesGhostRestriction.isDefEq ht.2 hs.2).bind fun _ _ => ?_
      split
      · exact .pure trivial
      · exact isDefEqArgs.framed (t := tf) (s := sf) ht.1 hs.1
    all_goals exact .pure trivial

theorem tryEtaExpansionCore.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (tryEtaExpansionCore t s) fun _ => True := by
  unfold tryEtaExpansionCore
  split
  · refine (RecM.PreservesGhostRestriction.inferType hs).bind fun _ h => (RecM.PreservesGhostRestriction.whnf h).bind fun _ h => ?_
    split
    · exact RecM.PreservesGhostRestriction.isDefEq ht ⟨h.1, hs, trivial⟩
    · exact .pure trivial
  · exact .pure trivial

theorem tryEtaExpansion.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (tryEtaExpansion t s) fun _ => True :=
  .orM (tryEtaExpansionCore.framed ht hs) (tryEtaExpansionCore.framed hs ht)

theorem tryEtaStructCore.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (tryEtaStructCore t s) fun _ => True := by
  unfold tryEtaStructCore
  split <;> try exact .pure trivial
  refine RecM.PreservesGhostRestriction.getEnv.bind fun env _ => ?_
  refine (RecM.PreservesGhostRestriction.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  rename_i fInfo
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  refine (RecM.PreservesGhostRestriction.inferType ht).bind fun tType htT => ?_
  refine (RecM.PreservesGhostRestriction.inferType hs).bind fun _ hsT => ?_
  refine (RecM.PreservesGhostRestriction.isDefEq htT hsT).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  refine (RecM.PreservesGhostRestriction.inferType htT).bind fun _ h => (RecM.PreservesGhostRestriction.whnf h).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  have hargs := hs.getAppArgs
  dsimp only
  generalize fInfo.numParams = i
  induction i using tryEtaStructCore.loop.induct (args := s.getAppArgs) with
  | case1 i h ih =>
    unfold tryEtaStructCore.loop; rw [dif_pos h]
    refine (RecM.PreservesGhostRestriction.isDefEq (t := .proj _ _ t) ht (hargs.getElem h)).bind fun _ _ => ?_
    split <;> first | exact .pure trivial | exact ih
  | case2 i h => unfold tryEtaStructCore.loop; rw [dif_neg h]; exact .pure trivial

theorem tryEtaStruct.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (tryEtaStruct t s) fun _ => True :=
  .orM (tryEtaStructCore.framed ht hs) (tryEtaStructCore.framed hs ht)

theorem isDefEqApp.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (isDefEqApp t s) fun _ => True := by
  unfold isDefEqApp
  split <;> try exact .pure trivial
  rw [Expr.withApp_eq, Expr.withApp_eq]
  have htA := ht.getAppArgs
  have hsA := hs.getAppArgs
  split <;> try exact .pure trivial
  rename_i hsz
  refine (RecM.PreservesGhostRestriction.isDefEq ht.getAppFn hs.getAppFn).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  generalize 0 = i
  induction i using isDefEqApp.loop.induct (tArgs := t.getAppArgs) (sArgs := s.getAppArgs) (_h := hsz) with
  | case1 i h ih =>
    unfold isDefEqApp.loop; rw [dif_pos h]
    refine (RecM.PreservesGhostRestriction.isDefEq (htA.getElem h) (hsA.getElem (hsz ▸ h))).bind fun _ _ => ?_
    split <;> first | exact .pure trivial | exact ih
  | case2 i h => unfold isDefEqApp.loop; rw [dif_neg h]; exact .pure trivial

theorem isDefEqProofIrrel.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (isDefEqProofIrrel t s) fun _ => True := by
  unfold isDefEqProofIrrel
  refine (RecM.PreservesGhostRestriction.inferType ht).bind fun _ htT => (isProp.framed htT).bind fun _ _ => ?_
  split <;> first
    | exact .pure trivial
    | exact (RecM.PreservesGhostRestriction.inferType hs).bind fun _ h => .toLBoolM (RecM.PreservesGhostRestriction.isDefEq htT h)

theorem cacheFailure.framed : M.PreservesGhostRestriction G (cacheFailure t s) fun _ => True := by
  unfold cacheFailure
  refine M.PreservesGhostRestriction.modify fun st hst => ⟨⟨hst.1, hst.2, hst.3, hst.4, hst.5, hst.6⟩, .rfl⟩

theorem tryUnfoldProjApp.framed (he : GhostFree G e) :
    RecM.PreservesGhostRestriction G (tryUnfoldProjApp e) (OptionGhostFree G) := by
  unfold tryUnfoldProjApp; dsimp only
  split
  · exact .pure OptionGhostFree.none
  · refine (RecM.PreservesGhostRestriction.whnfCore he).bind fun _ h => .pure ?_
    split
    · exact OptionGhostFree.some h
    · exact OptionGhostFree.none

theorem lazyDeltaReductionStep.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (lazyDeltaReductionStep t s) (ReductionStatusGhostFree G) := by
  unfold lazyDeltaReductionStep
  refine RecM.PreservesGhostRestriction.getEnv.bind fun env _ => ?_
  extract_lets delta cont
  have hdelta : ∀ e, GhostFree G e → RecM.PreservesGhostRestriction G (delta e) (GhostFree G) := fun e he =>
    (unfoldDefinition.framed he).bind fun _ h => RecM.PreservesGhostRestriction.whnfCore h.get!
  have hcont : ∀ tn sn, GhostFree G tn → GhostFree G sn → RecM.PreservesGhostRestriction G (cont tn sn) (ReductionStatusGhostFree G) :=
    fun tn sn htn hsn => (quickIsDefEq.framed htn hsn).bind fun _ _ => .pure (by
      split
      · exact ⟨htn, hsn⟩
      · trivial
      · exact ⟨htn, hsn⟩)
  split
  · exact .pure ⟨ht, hs⟩
  · refine (tryUnfoldProjApp.framed hs).bind fun o ho => ?_
    split
    · exact hcont _ _ ht (ho rfl)
    · exact (hdelta _ ht).bind fun _ h => hcont _ _ h hs
  · refine (tryUnfoldProjApp.framed ht).bind fun o ho => ?_
    split
    · exact hcont _ _ (ho rfl) hs
    · exact (hdelta _ hs).bind fun _ h => hcont _ _ ht h
  · extract_lets hts hss
    split
    · exact (hdelta _ hs).bind fun _ h => hcont _ _ ht h
    split
    · exact (hdelta _ ht).bind fun _ h => hcont _ _ h hs
    refine RecM.PreservesGhostRestriction.get.bind fun _ _ => ?_
    have hjp := (hdelta _ ht).bind fun _ h1 => (hdelta _ hs).bind fun _ h2 => hcont _ _ h1 h2
    have hjp' := (RecM.PreservesGhostRestriction.lift (cacheFailure.framed (G := G) (t := t) (s := s))).bind
      fun _ _ => hjp
    split
    · split
      · refine (isDefEqArgs.framed ht hs).bind fun _ _ => ?_
        split <;> first | exact .pure trivial | exact hjp'
      · exact hjp'
    · exact hjp

theorem isDefEqOffset.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (isDefEqOffset t s) fun _ => True := by
  unfold isDefEqOffset
  split
  · exact .pure trivial
  split
  · rename_i t' s' h1 h2
    have gf : ∀ {e e' : Expr}, GhostFree G e → isNatSuccOf? e = some e' → GhostFree G e' := by
      intro e e' he h
      unfold isNatSuccOf? at h
      split at h
      · cases h; trivial
      · cases h; exact he.2
      · cases h
    exact .toLBoolM (RecM.PreservesGhostRestriction.isDefEqCore (gf ht h1) (gf hs h2))
  · exact .pure trivial

theorem _root_.Lean4Lean.TypeChecker.ReductionStatusGhostFree.bool (ht : GhostFree G t) (hs : GhostFree G s) :
    ReductionStatusGhostFree G (ReductionStatus.bool t s b) := by
  cases b
  · exact ⟨ht, hs⟩
  · trivial

theorem lazyDeltaReduction.loop.framed : ∀ (fuel : Nat) {t s : Expr}, GhostFree G t → GhostFree G s →
    RecM.PreservesGhostRestriction G (lazyDeltaReduction.loop t s fuel) (ReductionStatusGhostFree G) := by
  intro fuel
  induction fuel with
  | zero => intro t s _ _; unfold lazyDeltaReduction.loop; exact .throw
  | succ fuel ih =>
    intro t s ht hs
    unfold lazyDeltaReduction.loop
    refine (isDefEqOffset.framed ht hs).bind fun r _ => ?_
    split
    · exact .pure (.bool ht hs)
    refine RecM.PreservesGhostRestriction.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.1]) fun _ _ _ => ?_
    have hjp : RecM.PreservesGhostRestriction G (do
        let env ← liftM getEnv
        let __do_lift ← liftM (reduceNative env t)
        match __do_lift with
          | some tn' => do
            let __do_lift ← isDefEqCore tn' s
            pure (ReductionStatus.bool tn' s __do_lift)
          | x => do
            let __do_lift ← liftM (reduceNative env s)
            match __do_lift with
              | some sn' => do
                let __do_lift ← isDefEqCore t sn'
                pure (ReductionStatus.bool t sn' __do_lift)
              | x => do
                let __do_lift ← lazyDeltaReductionStep t s
                match __do_lift with
                  | ReductionStatus.continue tn sn => lazyDeltaReduction.loop tn sn fuel
                  | r => pure r) (ReductionStatusGhostFree G) := by
      refine RecM.PreservesGhostRestriction.getEnv.bind fun env _ => ?_
      refine (RecM.PreservesGhostRestriction.liftExcept (reduceNative_gf (G := G))).bind fun o ho => ?_
      split
      · exact (RecM.PreservesGhostRestriction.isDefEqCore (ho rfl) hs).bind fun _ _ => .pure (.bool (ho rfl) hs)
      refine (RecM.PreservesGhostRestriction.liftExcept (reduceNative_gf (G := G))).bind fun o ho => ?_
      split
      · exact (RecM.PreservesGhostRestriction.isDefEqCore ht (ho rfl)).bind fun _ _ => .pure (.bool ht (ho rfl))
      refine (lazyDeltaReductionStep.framed ht hs).bind fun r hr => ?_
      split
      · exact ih hr.1 hr.2
      · exact .pure hr
    split
    · refine (reduceNat.framed ht).bind fun o ho => ?_
      split
      · exact (RecM.PreservesGhostRestriction.isDefEqCore (ho rfl) hs).bind fun _ _ => .pure (.bool (ho rfl) hs)
      refine (reduceNat.framed hs).bind fun o ho => ?_
      split
      · exact (RecM.PreservesGhostRestriction.isDefEqCore ht (ho rfl)).bind fun _ _ => .pure (.bool ht (ho rfl))
      · exact hjp
    · exact hjp

theorem lazyDeltaReduction.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (lazyDeltaReduction t s) (ReductionStatusGhostFree G) := by
  unfold lazyDeltaReduction
  exact RecM.PreservesGhostRestriction.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.2.2]) fun _ _ _ =>
    lazyDeltaReduction.loop.framed _ ht hs

theorem lazyDeltaProjReduction.finish.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (lazyDeltaProjReduction.finish structName idx t s) fun _ => True := by
  unfold lazyDeltaProjReduction.finish
  refine (reduceProjCore.framed ht).bind fun o ho => ?_
  have k := RecM.PreservesGhostRestriction.isDefEqCore (G := G) ht hs
  split
  · refine (reduceProjCore.framed hs).bind fun o' ho' => ?_
    split
    · exact RecM.PreservesGhostRestriction.isDefEqCore (ho rfl) (ho' rfl)
    · exact k
  · exact k

theorem lazyDeltaProjReduction.loop.framed : ∀ (fuel : Nat) {t s : Expr}, GhostFree G t → GhostFree G s →
    RecM.PreservesGhostRestriction G (lazyDeltaProjReduction.loop structName idx t s fuel) fun _ => True := by
  intro fuel
  induction fuel with
  | zero => intro t s _ _; unfold lazyDeltaProjReduction.loop; exact .throw
  | succ fuel ih =>
    intro t s ht hs
    unfold lazyDeltaProjReduction.loop
    refine (lazyDeltaReductionStep.framed ht hs).bind fun r hr => ?_
    split
    · exact ih hr.1 hr.2
    · exact .pure trivial
    · exact finish.framed hr.1 hr.2
    · exact finish.framed hr.1 hr.2

theorem lazyDeltaProjReduction.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (lazyDeltaProjReduction structName t s idx) fun _ => True := by
  unfold lazyDeltaProjReduction
  exact RecM.PreservesGhostRestriction.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.2.2]) fun _ _ _ =>
    lazyDeltaProjReduction.loop.framed _ ht hs

theorem tryStringLitExpansionCore.framed (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (tryStringLitExpansionCore t s) fun _ => True := by
  unfold tryStringLitExpansionCore
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  exact .toLBoolM (RecM.PreservesGhostRestriction.isDefEqCore FVarsIn.strLitToConstructor hs)

theorem tryStringLitExpansion.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (tryStringLitExpansion t s) fun _ => True := by
  unfold tryStringLitExpansion
  refine (tryStringLitExpansionCore.framed hs).bind fun _ _ => ?_
  split
  · exact tryStringLitExpansionCore.framed ht
  · exact .pure trivial

theorem isDefEqUnitLike.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (isDefEqUnitLike t s) fun _ => True := by
  unfold isDefEqUnitLike
  refine (RecM.PreservesGhostRestriction.inferType ht).bind fun _ h => (RecM.PreservesGhostRestriction.whnf h).bind fun tType htT => ?_
  split <;> try exact .pure trivial
  refine RecM.PreservesGhostRestriction.getEnv.bind fun env _ => ?_
  refine (RecM.PreservesGhostRestriction.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  refine (RecM.PreservesGhostRestriction.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  repeat (split <;> [skip; exact .pure trivial])
  exact (RecM.PreservesGhostRestriction.inferType hs).bind fun _ h => RecM.PreservesGhostRestriction.isDefEqCore htT h

theorem isDefEqCore'.framed (ht : GhostFree G t) (hs : GhostFree G s) :
    RecM.PreservesGhostRestriction G (isDefEqCore' t s) fun _ => True := by
  unfold isDefEqCore'
  refine (quickIsDefEq.framed ht hs).bind fun _ _ => ?_
  split
  · exact .pure trivial
  refine RecM.PreservesGhostRestriction.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.1]) fun _ _ _ => ?_
  extract_lets jp1
  have hjp1 : RecM.PreservesGhostRestriction G (jp1 ()) fun _ => True := by
    dsimp (config := {zeta := false}) only [jp1]
    refine (RecM.PreservesGhostRestriction.whnfCore ht).bind fun tn htn =>
      (RecM.PreservesGhostRestriction.whnfCore hs).bind fun sn hsn => ?_
    extract_lets jp2
    have hjp2 : RecM.PreservesGhostRestriction G (jp2 ()) fun _ => True := by
      dsimp (config := {zeta := false}) only [jp2]
      refine (isDefEqProofIrrel.framed htn hsn).bind fun _ _ => ?_
      split
      · exact .pure trivial
      refine (lazyDeltaReduction.framed htn hsn).bind fun r hr => ?_
      split
      · exact .panic trivial
      · exact .pure trivial
      · exact .pure trivial
      rename_i tn sn
      have htn : GhostFree G tn := hr.1
      have hsn : GhostFree G sn := hr.2
      extract_lets jp3
      have hjp3 : RecM.PreservesGhostRestriction G (jp3 ()) fun _ => True := by
        dsimp (config := {zeta := false}) only [jp3]
        refine (RecM.PreservesGhostRestriction.whnfCore htn).bind fun _ htnn =>
          (RecM.PreservesGhostRestriction.whnfCore hsn).bind fun _ hsnn => ?_
        split
        · exact RecM.PreservesGhostRestriction.isDefEqCore htnn hsnn
        refine (isDefEqApp.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (tryEtaExpansion.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (tryEtaStruct.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (tryStringLitExpansion.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (isDefEqUnitLike.framed htn hsn).bind fun _ _ => ?_
        split <;> exact .pure trivial
      split
      · split
        · exact .pure trivial
        · exact hjp3
      · split
        · exact .pure trivial
        · exact hjp3
      · split
        · rename_i _ _ te _ _ se _
          refine (lazyDeltaProjReduction.framed (t := te) (s := se) htn hsn).bind fun _ _ => ?_
          split
          · exact .pure trivial
          · exact hjp3
        · exact hjp3
      · exact hjp3
    split
    · refine (quickIsDefEq.framed htn hsn).bind fun _ _ => ?_
      split
      · exact .pure trivial
      · exact hjp2
    · exact hjp2
  split
  · refine (RecM.PreservesGhostRestriction.whnf ht).bind fun _ _ => ?_
    split
    · exact .pure trivial
    · exact hjp1
  · exact hjp1

end Inner
end Lean4Lean.TypeChecker
