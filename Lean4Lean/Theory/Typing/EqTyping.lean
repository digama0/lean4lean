import Lean4Lean.Theory.Typing.IotaLemmas
import Lean4Lean.Theory.CanonicalEq

/-! # Typing of canonical equality terms

Syntax and typing of `Eq`, `Eq.refl`, `Eq.rec` applications in an environment with
canonical equality (`VEnv.HasCanonicalEq`), and the *type cast* along an equation
between types,

```text
typeCast u X Y e x := @Eq.rec.{u, u+1} (Sort u) X (fun T _ => T) x Y e : Y
```

for `e : @Eq (Sort u) X Y` and `x : X`. When `X ≡ Y`, the cast computes to `x`: the
equation proof is proof-irrelevantly `Eq.refl X`, and the stored `Eq.rec` iota rule
fires. This is the K-like computation used by singleton eta. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

namespace VExpr

/-- `@Eq.{w} α a b`. -/
def eqApp (w : VLevel) (α a b : VExpr) : VExpr :=
  .app (.app (.app (.const ``Eq [w]) α) a) b

/-- `@Eq.refl.{w} α a`. -/
def eqReflApp (w : VLevel) (α a : VExpr) : VExpr :=
  .app (.app (.const ``Eq.refl [w]) α) a

/-- `@Eq.rec.{v, w} α a motive minor b h`. -/
def eqRecApp (v w : VLevel) (α a motive minor b h : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.app (.const ``Eq.rec [v, w]) α) a) motive) minor) b) h

/-- The cast motive `fun (T : Sort u) (_ : @Eq (Sort u) X T) => T`. -/
def castMotive (u : VLevel) (X : VExpr) : VExpr :=
  .lam (.sort u) (.lam (eqApp (.succ u) (.sort u) X.lift (.bvar 0)) (.bvar 1))

/-- Cast `x : X` along `e : @Eq (Sort u) X Y`. -/
def typeCast (u : VLevel) (X Y e x : VExpr) : VExpr :=
  eqRecApp u (.succ u) (.sort u) X (castMotive u X) x Y e

end VExpr

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Normalize instantiations and lifts of equality syntax. -/
local macro "eqnorm" : tactic => `(tactic| simp [VEnv.HasType, VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift])
local macro "eqnorm" " at " h:ident : tactic =>
  `(tactic| simp [VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift] at $h:ident)

theorem HasType.app_of_eq (h1 : env.HasType U Γ f T) (hT : T = .forallE A B)
    (h2 : env.HasType U Γ a A) : env.HasType U Γ (.app f a) (B.inst a) := by
  subst hT; exact h1.app h2

theorem HasType.eqApp (heq : env.HasCanonicalEq) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α) (hb : env.HasType U Γ b α) :
    env.HasType U Γ (VExpr.eqApp w α a b) (.sort .zero) := by
  have hc := HasType.const (Γ := Γ) heq.1 (ls := [w]) (by simpa using hw) rfl
  have h1 := hc.app_of_eq (by simp [canonicalEqType, VExpr.instL, VLevel.inst]; rfl) hα
  have h2 := h1.app_of_eq (by simp [VExpr.inst, VExpr.instL]; rfl) ha
  have h3 := h2.app_of_eq (by simp [VExpr.inst, VExpr.instL, VExpr.inst_lift]; rfl) hb
  simpa [VExpr.eqApp, VExpr.inst] using h3

theorem HasType.eqReflApp (heq : env.HasCanonicalEq) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α) :
    env.HasType U Γ (VExpr.eqReflApp w α a) (VExpr.eqApp w α a a) := by
  have hc := HasType.const (Γ := Γ) heq.2.1 (ls := [w]) (by simpa using hw) rfl
  have h1 := hc.app_of_eq (by simp [canonicalEqReflType, VExpr.instL, VLevel.inst]; rfl) hα
  have h2 := h1.app_of_eq (by simp [VExpr.inst]; rfl) ha
  simpa [VExpr.eqReflApp, VExpr.eqApp, VExpr.inst, VExpr.instL, VLevel.inst,
    VExpr.inst_lift] using h2

theorem HasType.app_dom (h1 : env.HasType U Γ f (.forallE A' B)) (hA : A' = A)
    (h2 : env.HasType U Γ a A) : env.HasType U Γ (.app f a) (B.inst a) := by
  subst hA; exact h1.app h2

/-- `@Eq.rec α a motive minor`, before the endpoint and the proof are supplied. -/
theorem HasType.eqRec4 (heq : env.HasCanonicalEq) (hv : v.WF U) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hM : env.HasType U Γ motive
      (.forallE α (.forallE (VExpr.eqApp w α.lift a.lift (.bvar 0)) (.sort v))))
    (hm : env.HasType U Γ minor (.app (.app motive a) (VExpr.eqReflApp w α a))) :
    env.HasType U Γ
      (.app (.app (.app (.app (.const ``Eq.rec [v, w]) α) a) motive) minor)
      (.forallE α (.forallE (VExpr.eqApp w α.lift a.lift (.bvar 0))
        (.app (.app motive.lift.lift (.bvar 1)) (.bvar 0)))) := by
  have hc := HasType.const (U := U) (Γ := Γ) heq.2.2.1 (ls := [v, w]) (by simp; exact ⟨hv, hw⟩) rfl
  have hc' : env.HasType U Γ (.const ``Eq.rec [v, w])
      (.forallE (.sort w) <| .forallE (.bvar 0) <|
        .forallE (.forallE (.bvar 1) (.forallE (VExpr.eqApp w (.bvar 2) (.bvar 1) (.bvar 0))
          (.sort v))) <|
        .forallE (.app (.app (.bvar 0) (.bvar 1)) (VExpr.eqReflApp w (.bvar 2) (.bvar 1))) <|
        .forallE (.bvar 3) <| .forallE (VExpr.eqApp w (.bvar 4) (.bvar 3) (.bvar 0)) <|
        .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) := hc
  have h1 := hc'.app_dom (by eqnorm) hα
  eqnorm at h1
  have h2 := h1.app_dom (by eqnorm) ha
  eqnorm at h2
  have h3 := h2.app_dom (by eqnorm) hM
  eqnorm at h3
  have h4 := h3.app_dom (by eqnorm) hm
  simpa [VEnv.HasType, VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, liftN_liftN, inst_liftN_lo,
    inst_lift] using h4

theorem HasType.eqRecApp (heq : env.HasCanonicalEq) (hv : v.WF U) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hM : env.HasType U Γ motive
      (.forallE α (.forallE (VExpr.eqApp w α.lift a.lift (.bvar 0)) (.sort v))))
    (hm : env.HasType U Γ minor (.app (.app motive a) (VExpr.eqReflApp w α a)))
    (hb : env.HasType U Γ b α) (hh : env.HasType U Γ h (VExpr.eqApp w α a b)) :
    env.HasType U Γ (VExpr.eqRecApp v w α a motive minor b h) (.app (.app motive b) h) := by
  have h4 := HasType.eqRec4 heq hv hw hα ha hM hm
  have h5 := h4.app_dom (by eqnorm) hb
  eqnorm at h5
  have h6 := h5.app_dom (by eqnorm) hh
  simpa [VEnv.HasType, VExpr.eqRecApp, VExpr.inst, VExpr.liftN, instVar, liftN_liftN,
    inst_liftN_lo, inst_lift] using h6

/-- The cast motive is a motive for `Eq.rec` at `α := Sort u`, `a := X`. -/
theorem HasType.castMotive (henv : env.Ordered) (heq : env.HasCanonicalEq) (hu : u.WF U)
    (hX : env.HasType U Γ X (.sort u)) :
    env.HasType U Γ (VExpr.castMotive u X)
      (.forallE (.sort u) (.forallE (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0)) (.sort u))) := by
  have hs : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have hs' : env.HasType U (.sort u :: Γ) (.sort u) (.sort (.succ u)) := .sort hu
  have hE : env.HasType U (.sort u :: Γ) (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0))
      (.sort .zero) :=
    HasType.eqApp heq hu hs' (hX.weak henv) (.bvar .zero)
  have hv : env.HasType U (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0) :: .sort u :: Γ)
      (.bvar 1) (.sort u) := .bvar (.succ .zero)
  exact .lam hs (.lam hE hv)

/-- Two beta steps: `castMotive u X Y e ≡ Y`. -/
theorem IsDefEq.castMotive_app (henv : env.Ordered) (heq : env.HasCanonicalEq) (hu : u.WF U)
    (hX : env.HasType U Γ X (.sort u)) (hY : env.HasType U Γ Y (.sort u))
    (he : env.HasType U Γ e (VExpr.eqApp (.succ u) (.sort u) X Y)) :
    env.IsDefEq U Γ (.app (.app (VExpr.castMotive u X) Y) e) Y (.sort u) := by
  have hs' : env.HasType U (.sort u :: Γ) (.sort u) (.sort (.succ u)) := .sort hu
  have hE : env.HasType U (.sort u :: Γ) (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0))
      (.sort .zero) :=
    HasType.eqApp heq hu hs' (hX.weak henv) (.bvar .zero)
  have hv : env.HasType U (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0) :: .sort u :: Γ)
      (.bvar 1) (.sort u) := .bvar (.succ .zero)
  have hinner : env.HasType U (.sort u :: Γ)
      (.lam (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0)) (.bvar 1))
      (.forallE (VExpr.eqApp (.succ u) (.sort u) X.lift (.bvar 0)) (.sort u)) := .lam hE hv
  have hb1 := IsDefEq.beta hinner hY
  simp [VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift] at hb1
  have hb2 := IsDefEq.appDF hb1 (by simpa [VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift, VEnv.HasType] using he)
  have hb3 := IsDefEq.beta (hY.weak henv (B := VExpr.eqApp (.succ u) (.sort u) X Y))
    (by simpa [VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift, VEnv.HasType] using he)
  simp [VExpr.inst, VExpr.liftN, instVar, VExpr.eqApp, VExpr.eqReflApp, liftN_liftN, inst_liftN_lo, inst_lift] at hb2 hb3
  exact hb2.trans hb3

theorem HasType.typeCast (henv : env.Ordered) (heq : env.HasCanonicalEq) (hu : u.WF U)
    (hX : env.HasType U Γ X (.sort u)) (hY : env.HasType U Γ Y (.sort u))
    (he : env.HasType U Γ e (VExpr.eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType U Γ x X) :
    env.HasType U Γ (VExpr.typeCast u X Y e x) Y := by
  have hsu : (VLevel.succ u).WF U := hu
  have hs : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have hM := HasType.castMotive henv heq hu hX
  have hrefl := HasType.eqReflApp heq hsu hs hX
  have hmX := IsDefEq.castMotive_app henv heq hu hX hX hrefl
  have hm : env.HasType U Γ x
      (.app (.app (VExpr.castMotive u X) X) (VExpr.eqReflApp (.succ u) (.sort u) X)) :=
    hmX.symm.defeq hx
  have hr := HasType.eqRecApp heq hu hsu hs hX (by simpa [VExpr.liftN] using hM) hm hY he
  exact (IsDefEq.castMotive_app henv heq hu hX hY he).defeq hr

/-- Partial application `@Eq α a`. -/
theorem HasType.eqApp2 (heq : env.HasCanonicalEq) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α) :
    env.HasType U Γ (.app (.app (.const ``Eq [w]) α) a) (.forallE α (.sort .zero)) := by
  have hc := HasType.const (Γ := Γ) heq.1 (ls := [w]) (by simpa using hw) rfl
  have h1 := hc.app_of_eq (by simp [canonicalEqType, VExpr.instL, VLevel.inst]; rfl) hα
  have h2 := h1.app_of_eq (by simp [VExpr.inst, VExpr.instL]; rfl) ha
  simpa [VExpr.inst, inst_lift] using h2

/-- Congruence of `@Eq α a b` in the right endpoint. -/
theorem IsDefEq.eqApp_r (heq : env.HasCanonicalEq) (hw : w.WF U)
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hb : env.IsDefEq U Γ b b' α) :
    env.IsDefEq U Γ (VExpr.eqApp w α a b) (VExpr.eqApp w α a b') (.sort .zero) := by
  have := IsDefEq.appDF (HasType.eqApp2 heq hw hα ha) hb
  simpa [VExpr.eqApp, VExpr.inst] using this

/-- K for type casts: along an equation between definitionally equal types, the cast
computes to its argument. In `VEnv.IsDefEq` this is proof irrelevance (the equation proof
is `Eq.refl`) followed by the stored `Eq.rec` iota rule. -/
theorem IsDefEq.typeCast_refl (henv : env.WF) (heq : env.HasCanonicalEq) (hu : u.WF U)
    (hΓ : OnCtx Γ (env.IsType U))
    (hXY : env.IsDefEq U Γ X Y (.sort u))
    (he : env.HasType U Γ e (VExpr.eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType U Γ x X) :
    env.IsDefEq U Γ (VExpr.typeCast u X Y e x) x Y := by
  have hsu : (VLevel.succ u).WF U := hu
  have hs : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have hX := hXY.hasType.1
  have hY := hXY.hasType.2
  have hM := HasType.castMotive henv.ordered heq hu hX
  have hrefl := HasType.eqReflApp heq hsu hs hX
  -- the equation proof is `Eq.refl X`
  have hP := HasType.eqApp heq hsu hs hX hY
  have hreflY : env.HasType U Γ (VExpr.eqReflApp (.succ u) (.sort u) X)
      (VExpr.eqApp (.succ u) (.sort u) X Y) :=
    (IsDefEq.eqApp_r heq hsu hs hX hXY).defeq hrefl
  have hirr : env.IsDefEq U Γ e (VExpr.eqReflApp (.succ u) (.sort u) X)
      (VExpr.eqApp (.succ u) (.sort u) X Y) := .proofIrrel hP he hreflY
  have hmX := IsDefEq.castMotive_app henv.ordered heq hu hX hX hrefl
  have hm : env.HasType U Γ x
      (.app (.app (VExpr.castMotive u X) X) (VExpr.eqReflApp (.succ u) (.sort u) X)) :=
    hmX.symm.defeq hx
  -- congruence in the endpoint and the proof
  have h4 := HasType.eqRec4 heq hu hsu hs hX (by simpa [VExpr.liftN] using hM) hm
  have hc1 := IsDefEq.appDF h4 hXY.symm
  eqnorm at hc1
  have hc2 := IsDefEq.appDF hc1 (by simpa [VExpr.eqApp] using hirr)
  eqnorm at hc2
  -- `hc2 : typeCast … ≡ Eq.rec … X (Eq.refl X) : castMotive Y e`
  have hiota := IsDefEq.extra_instOuter henv hΓ heq.2.2.2 (ls := [u, .succ u])
    (doms := [.sort (.param 1), .bvar 0, canonicalEqRecMotive, canonicalEqRecMinor])
    (lhsBody := .app (.app (.app (.app (.app (.app (.const ``Eq.rec [.param 0, .param 1])
      (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2))
      (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2)))
    (rhsBody := .bvar 0)
    (typeBody := .app (.app (.bvar 1) (.bvar 2))
      (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2)))
    (by simp; exact ⟨hu, hsu⟩) rfl rfl rfl rfl
    (args := [.sort u, X, VExpr.castMotive u X, x]) rfl (by
      intro j hj _
      match j, hj with
      | 0, _ => simpa [VExpr.instL, VLevel.inst, VExpr.instOuter] using hs
      | 1, _ => simpa [VExpr.instL, VExpr.instOuter, VExpr.inst, instVar] using hX
      | 2, _ => simpa [canonicalEqRecMotive, VExpr.instL, VLevel.inst, VExpr.instOuter,
          VExpr.inst, instVar, VExpr.eqApp, VExpr.liftN, liftN_liftN, inst_liftN_lo, inst_lift]
          using hM
      | 3, _ => simpa [canonicalEqRecMinor, VExpr.instL, VLevel.inst, VExpr.instOuter,
          VExpr.inst, instVar, VExpr.eqReflApp, VExpr.liftN, liftN_liftN, inst_liftN_lo,
          inst_lift] using hm)
  simp [VExpr.instL, VLevel.inst, VExpr.instOuter, VExpr.inst, instVar, VExpr.liftN,
    liftN_liftN, inst_liftN_lo, inst_lift] at hiota
  have hY' := IsDefEq.castMotive_app henv.ordered heq hu hX hY he
  have h1 : env.IsDefEq U Γ (VExpr.typeCast u X Y e x) _ Y := .defeqDF hY' (by
    simpa [VExpr.typeCast, VExpr.eqRecApp, VExpr.eqApp, VExpr.eqReflApp] using hc2)
  have h2 : env.IsDefEq U Γ _ x Y := .defeqDF (hmX.trans hXY) (by
    simpa [VExpr.eqReflApp] using hiota)
  exact h1.trans h2

end VEnv
end Lean4Lean
