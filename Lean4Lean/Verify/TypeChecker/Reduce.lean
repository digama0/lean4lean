import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem reduceNative.WF :
    (reduceNative env e).WF fun oe => ∀ e₁, oe = some e₁ → False := by
  unfold reduceNative; split <;> [skip; exact .pure nofun]
  split <;> [exact .throw; skip]; split <;> [exact .throw; exact .pure nofun]

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; exact .lit (he.eqv h)
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type c.Ewf c.hasPrimitives
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

def reduceBinNatOpG (guard : Nat → Nat → Prop) [DecidableRel guard]
    (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if guard v1 v2 then return none
  return some <| .lit <| .natVal <| f v1 v2

theorem reduceBinNatOpG.WF {guard} [DecidableRel guard] {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f) :
    RecM.WF c s (reduceBinNatOpG guard f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatOpG
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  split <;> [exact .pure nofun; rename_i h]
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
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
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
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
  unfold reduceNat
  extract_lets nargs F1 fn F2
  split <;> [exact hP ▸ .pure nofun; refine .pureBind ?_]
  unfold F2; split <;> (split <;> [skip; exact hP ▸ .pure nofun])
  · rename_i _ h1 h2
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.eqv_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩
  · split <;> [rename_i f ls a b _ _ h2; exact hP ▸ .pure nofun]
    have hfun guard {g fc G} [DecidableRel guard] (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOpG guard g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOpG.WF he (hprims.2 hprim) heval
    have hpred {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natAdd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natSub
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMul
    apply hfun _ (by simp [prims]) c.hasPrimitives.natPow
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natGcd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMod
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natDiv
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLAnd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLOr
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natXor
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftLeft
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftRight
    exact hP ▸ .pure nofun
