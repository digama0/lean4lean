import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; have := he.eqv h; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

theorem checkNatSize.WF {c : VContext} {s : VState} :
    (checkNatSize n).WF c s fun _ _ => True := by
  unfold checkNatSize; refine .read ?_; split <;> [exact .throw; exact .pure trivial]

theorem checkNatResult.WF {c : VContext} {s : VState} :
    (checkNatResult r).WF c s fun _ _ => True := checkNatSize.WF

theorem checkNatPow.WF {c : VContext} {s : VState} :
    (checkNatPow base exp).WF c s fun _ _ => True := by
  unfold checkNatPow
  refine (M.WF.liftExcept (Q := fun _ => True) fun _ _ => ⟨⟩).bind fun _ _ _ _ => .read ?_
  split <;> [exact .throw; exact .pure trivial]

theorem checkNatShiftLeft.WF {c : VContext} {s : VState} :
    (checkNatShiftLeft v shift).WF c s fun _ _ => True := by
  unfold checkNatShiftLeft
  split <;> [exact .pure trivial; skip]
  exact (M.WF.liftExcept (Q := fun _ => True) fun _ _ => ⟨⟩).bind fun _ _ _ _ => checkNatSize.WF

theorem reduceBinNatOp.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f)
    (hpre : ∀ v₁ v₂ s, (pre v₁ v₂).WF c s fun _ _ => True)
    (hpost : ∀ r s, (post r).WF c s fun _ _ => True) :
    RecM.WF c s (reduceBinNatOp f a b pre post) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatOp
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  refine (hpre v1 v2 _).lift.bind fun _ _ _ _ => (hpost _ _).lift.bind fun _ _ _ _ => ?_
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := (heval ⟨_, h1⟩).2 v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact ⟨_, .appDF this b3⟩

theorem reduceBinNatPred.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatBool fc f) :
    RecM.WF c s (reduceBinNatPred f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatPred
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]; cases (rawNatLitExt?.WF h a2).2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]; cases (rawNatLitExt?.WF h b2).2
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => .boolLit, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  have := (heval ⟨_, h1⟩).2 v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine ⟨_, (TrExprS.boolLit c.hasPrimitives ?_ _).1, ?_⟩
  · let ⟨_, H⟩ := this
    exact VExpr.WF.boolLit_has_type c.Ewf c.hasPrimitives (Γ := []) trivial ⟨_, H.hasType.2⟩
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact  ⟨_, .appDF this b3⟩

theorem reduceNat.WF {c : VContext} (he : c.TrExprS e e') :
    RecM.WF c s (reduceNat e) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  generalize hP : (fun oe => _) = P
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {a} : Environment.primitives.contains a ↔ a ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  unfold reduceNat; extract_lets nargs F1 fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> [exact hP ▸ .pure nofun; simp only [↓reduceIte]]
    split <;> [rename_i f ls a b; exact hP ▸ .pure nofun]
    have hfun {g fc G pre post} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g)
        (hpre : ∀ v₁ v₂ s, (pre v₁ v₂).WF c s fun _ _ => True)
        (hpost : ∀ r s, (post r).WF c s fun _ _ => True) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOp g a b pre post}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOp.WF he (hprims.2 hprim) heval hpre hpost
    have nop₂ v₁ v₂ s : ((fun _ _ => pure () : Nat → Nat → M Unit) v₁ v₂).WF c s
      fun _ _ => True := .pure trivial
    have nop₁ r s : ((fun _ => pure () : Nat → M Unit) r).WF c s fun _ _ => True := .pure trivial
    have hpred {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval
    apply hfun (by simp [prims]) c.hasPrimitives.natAdd nop₂ fun _ _ => checkNatResult.WF
    apply hfun (by simp [prims]) c.hasPrimitives.natSub nop₂ nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natMul nop₂ fun _ _ => checkNatResult.WF
    apply hfun (by simp [prims]) c.hasPrimitives.natPow (fun _ _ _ => checkNatPow.WF) nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natGcd nop₂ nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natMod nop₂ nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natDiv nop₂ nop₁
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
    apply hfun (by simp [prims]) c.hasPrimitives.natLAnd nop₂ nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natLOr nop₂ nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natXor nop₂ nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natShiftLeft 
      (fun _ _ _ => checkNatShiftLeft.WF) nop₁
    apply hfun (by simp [prims]) c.hasPrimitives.natShiftRight nop₂ nop₁
    exact hP ▸ .pure nofun
  · split <;> [rename_i h2; exact hP ▸ .pure nofun]
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.eqv_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ checkNatResult.WF.lift.map fun _ _ _ _ => ?_
    rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩

theorem reduceProjCore.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProjCore i e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := sorry

theorem reduceProj.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProj i e cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceProj
  have .proj (e' := s) a1 a2 := he
  refine .bind (Q := fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ s) ?_ fun _ _ _ ⟨h1, h2⟩ => ?_
  · split <;> [exact whnfCore.WF a1; exact whnf.WF a1]
  have ⟨_, b1, b2⟩ := h2.proj c.Ewf c.Δwf a2
  refine (reduceProjCore.WF b1).mono fun _ _ _ H _ eq => ?_
  have ⟨c1, c2⟩ := H _ eq; exact ⟨h1.trans c1, c2.defeq c.Ewf c.Δwf b2⟩
