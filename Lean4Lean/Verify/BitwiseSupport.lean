import Lean4Lean.Verify.Primitive

namespace Lean4Lean.Environment
open Lean VEnv

/-- Semantic interface exported by the checked `Condition.natEq`
implementation.  Keeping the function expression explicit lets certificate
translations be related to calls occurring below unrelated local binders. -/
def VEnv.ReflectsNatEqDecide (env : VEnv) (decide : VExpr) : Prop :=
  env.HasType 0 [] decide (.forallE .nat <| .forallE .nat .bool) ∧
  ∀ a b, env.IsDefEqU 0 []
    (.app (.app decide (.natLit a)) (.natLit b))
    (.boolLit (a == b))

theorem VEnv.ReflectsNatEqDecide.mono {env env' : VEnv} {decide : VExpr}
    (h : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env decide)
    (le : env ≤ env') :
    Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env' decide :=
  ⟨h.1.mono le, fun a b => (h.2 a b).mono le⟩

/-- Relate a translated occurrence of `Condition.natEq.decide` to an
application of the translated closed decision function.  This is the bridge
between occurrences embedded under certificate binders and the closed
semantic interface above. -/
theorem Condition.natEqDecideFn.call_eq {env : VEnv} (wf : env.WF)
    {Δ : VLCtx} (hΔ : Δ.WF env 0)
    {x y : Expr} {x' y' out decide : VExpr}
    (hdecide : TrExprS env [] Δ Condition.natEqDecideFn decide)
    (hx : TrExprS env [] Δ x x') (hy : TrExprS env [] Δ y y')
    (hxT : env.HasType 0 Δ.toCtx x' .nat)
    (hyT : env.HasType 0 Δ.toCtx y' .nat)
    (hcall : TrExprS env [] Δ (Condition.natEq.decide #[x, y]) out) :
    env.IsDefEqU 0 Δ.toCtx out (.app (.app decide x') y') := by
  unfold Condition.natEqDecideFn at hdecide
  cases hdecide with
  | lam hnatTy₁ hnatS₁ hinnerS =>
    cases hinnerS with
    | lam hnatTy₂ hnatS₂ hbodyS =>
      rename_i natTy₁ natTy₂ body
      have hnatCanon (Δ' : VLCtx) : TrExprS env [] Δ' q(Nat) .nat := by
        obtain ⟨_, hnatCi, _, hnatLen⟩ :=
          (hxT.isType wf hΔ.toCtx).choose_spec.const_inv wf hΔ.toCtx
        exact .const hnatCi rfl (by simpa using hnatLen)
      have hctx : VLCtx.IsDefEq env 0 Δ Δ := .refl wf hΔ
      have hnatEq₁ := TrExprS.uniq (Us := []) wf hctx hnatS₁ (hnatCanon Δ)
      have hxT' := hxT.defeqU_r wf hΔ.toCtx hnatEq₁.symm
      have hinnerS' : TrExprS env []
          ((none, .vlam natTy₁) :: Δ)
          (.lam0 q(Nat) <|
            Condition.natEq.decide #[.bvar 1, .bvar 0])
          (.lam natTy₂ body) := .lam hnatTy₂ hnatS₂ hbodyS
      have hinnerInst := TrExprS.inst (env := env) (Us := []) (Δ := Δ)
        (e₀' := x') (A₀ := natTy₁) wf.ordered hxT' hinnerS' hx
      cases hinnerInst with
      | lam hnatTy₂' hnatS₂' hbodyInstS =>
        have hnatEq₂ := TrExprS.uniq (Us := []) wf hctx hnatS₂'
          (hnatCanon Δ)
        have hyT' := hyT.defeqU_r wf hΔ.toCtx hnatEq₂.symm
        have hbodyInst₂ := TrExprS.inst (env := env) (Us := []) (Δ := Δ)
          (e₀' := y') wf.ordered hyT' hbodyInstS hy
        have hbodyInst₂' : TrExprS env [] Δ
            (Condition.natEq.decide #[x, y])
            ((body.inst x' 1).inst y') := by
          simpa [Condition.natEqDecideFn, Condition.decide,
            Condition.ite, Condition.natEq, VExpr.inst,
            Lean.mkAppN, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
            Expr.instantiate1', Expr.instantiate1'_instantiate1',
            Expr.instantiate1'_liftLooseBVars_0] using hbodyInst₂
        have houtEq := TrExprS.uniq (Us := []) wf hctx hcall hbodyInst₂'
        obtain ⟨_, hfnT⟩ :=
          (show TrExprS env [] Δ
            (.lam0 q(Nat) <| .lam0 q(Nat) <|
              Condition.natEq.decide #[.bvar 1, .bvar 0])
            (.lam natTy₁ <| .lam natTy₂ body) from
              .lam hnatTy₁ hnatS₁ (.lam hnatTy₂ hnatS₂ hbodyS)).wf
            wf.ordered (Us := []) (Δ := Δ) hΔ
        obtain ⟨⟨_, hnatSort₁⟩, _, hinnerT⟩ :=
          hfnT.hasType.1.lam_inv wf hΔ.toCtx
        have hbeta₁ : env.IsDefEqU 0 Δ.toCtx
            (.app (VExpr.lam natTy₁ (VExpr.lam natTy₂ body)) x')
            ((VExpr.lam natTy₂ body).inst x') :=
          ⟨_, .beta hinnerT hxT'⟩
        have hinnerInstT := hinnerT.instN wf.ordered hxT'
          (.zero : Ctx.InstN Δ.toCtx x' natTy₁ 0
            (natTy₁ :: Δ.toCtx) Δ.toCtx)
        have hΔ₂ : VLCtx.WF env 0
            ((none, .vlam (natTy₂.inst x')) :: Δ) :=
          ⟨hΔ, nofun, hnatTy₂'⟩
        obtain ⟨_, hbodyInstWF⟩ := hbodyInstS.wf wf.ordered
          (Us := []) (Δ := ((none, .vlam (natTy₂.inst x')) :: Δ)) hΔ₂
        obtain ⟨_, hnatSort₂⟩ := hnatTy₂'
        have hrightPrefixT := VEnv.HasType.lam hnatSort₂
          hbodyInstWF.hasType.1
        have hbeta₂ : env.IsDefEqU 0 Δ.toCtx
            (.app ((VExpr.lam natTy₂ body).inst x') y')
            ((body.inst x' 1).inst y') := by
          exact ⟨_, .beta hbodyInstWF.hasType.1 hyT'⟩
        have hprefixT :=
          (hbeta₁.of_r wf hΔ.toCtx hrightPrefixT).hasType.1
        have happ := hbeta₁.app_same wf hΔ.toCtx hprefixT hyT'
        exact houtEq.trans wf hΔ.toCtx (happ.trans wf hΔ.toCtx hbeta₂).symm

/- `VEnv.IsDefEqU.lam_instU_hetero` and `VEnv.finish_bitwise_proof_equation`
now live in `Lean4Lean.Verify.Primitive`, where the gcd semantics share
them; they remain visible here (and to every consumer of this file) under
their original short names. -/

/-- Peel one binder from a checked closed lambda equation at an argument
inhabiting a common definitional type of the two binder domains.  Iterating
this step instantiates a checked binder telescope of any length: the
bitwise equations below use three and four ordinary binders, and a
five-binder telescope is one further application.  A trailing dependent
proof binder is discharged afterwards by
`VEnv.finish_bitwise_proof_equation`. -/
theorem VEnv.instantiate_lamU_step {env : VEnv} (wf : env.WF)
    {AL AR eL eR T x : VExpr}
    (heq : env.IsDefEqU 0 [] (.lam AL eL) (.lam AR eR))
    (hAL : env.IsDefEqU 0 [] AL T)
    (hAR : env.IsDefEqU 0 [] AR T)
    (hxT : env.HasType 0 [] x T) :
    env.HasType 0 [] x AL ∧ env.HasType 0 [] x AR ∧
      env.IsDefEqU 0 [] (eL.inst x) (eR.inst x) := by
  have heqD := heq
  obtain ⟨_, heqD⟩ := heqD
  obtain ⟨⟨_, hALSort⟩, _, hbodyLT⟩ := heqD.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hbodyRT⟩ := heqD.hasType.2.lam_inv wf trivial
  have hxL := hxT.defeqU_r wf trivial hAL.symm
  have hxR := hxT.defeqU_r wf trivial hAR.symm
  exact ⟨hxL, hxR, VEnv.IsDefEqU.lam_instU₂ wf trivial heq hALSort
    hbodyLT hbodyRT (hAL.trans wf trivial hAR.symm) hxL⟩

/-- The semantic result of instantiating the common `(Bool → Bool → Bool) →
Nat → Nat →` prefix of a checked bitwise equation.  The translated source
bodies and their original local contexts are retained for subsequent
constructor-specific reasoning. -/
inductive VEnv.BitwiseLam3Instantiation (env : VEnv)
    (leftBody rightBody : Expr) (op : VExpr) (a b : Nat) : Prop where
  | intro (funTyL natTyL₁ natTyL₂ bodyL : VExpr)
      (funTyR natTyR₁ natTyR₂ bodyR : VExpr)
      (hfunTyL : env.IsType 0 [] funTyL)
      (hnatTyL₁ : env.IsType 0 [funTyL] natTyL₁)
      (hnatTyL₂ : env.IsType 0 [natTyL₁, funTyL] natTyL₂)
      (hfunTyR : env.IsType 0 [] funTyR)
      (hnatTyR₁ : env.IsType 0 [funTyR] natTyR₁)
      (hnatTyR₂ : env.IsType 0 [natTyR₁, funTyR] natTyR₂)
      (hnatEqL₁ : env.IsDefEqU 0 [funTyL] natTyL₁ .nat)
      (hnatEqL₂ : env.IsDefEqU 0 [natTyL₁, funTyL] natTyL₂ .nat)
      (hnatEqR₁ : env.IsDefEqU 0 [funTyR] natTyR₁ .nat)
      (hnatEqR₂ : env.IsDefEqU 0 [natTyR₁, funTyR] natTyR₂ .nat)
      (hopL : env.HasType 0 [] op funTyL)
      (hopR : env.HasType 0 [] op funTyR)
      (haT : env.HasType 0 [] (.natLit a) .nat)
      (hbT : env.HasType 0 [] (.natLit b) .nat)
      (haL : env.HasType 0 [] (.natLit a) (natTyL₁.inst op))
      (haR : env.HasType 0 [] (.natLit a) (natTyR₁.inst op))
      (hbL : env.HasType 0 [] (.natLit b)
        ((natTyL₂.inst op 1).inst (.natLit a)))
      (hbR : env.HasType 0 [] (.natLit b)
        ((natTyR₂.inst op 1).inst (.natLit a)))
      (leftS : TrExprS env []
        [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
          (none, .vlam funTyL)] leftBody bodyL)
      (rightS : TrExprS env []
        [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
          (none, .vlam funTyR)] rightBody bodyR)
      (eq : env.IsDefEqU 0 []
        (((bodyL.inst op 2).inst (.natLit a) 1).inst (.natLit b))
        (((bodyR.inst op 2).inst (.natLit a) 1).inst (.natLit b))) :
      BitwiseLam3Instantiation env leftBody rightBody op a b

/-- Instantiate the common three-lambda prefix of a checked bitwise equation
with an arbitrary semantic Boolean operation and two concrete naturals. -/
theorem VEnv.instantiate_bitwise_lam3_equation {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {leftBody rightBody : Expr} {l r : VExpr}
    (hl : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) leftBody) l)
    (hr : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) rightBody) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hop : env.HasType 0 [] op
      (.forallE .bool <| .forallE .bool .bool)) :
    VEnv.BitwiseLam3Instantiation env leftBody rightBody op a b := by
  cases hl with
  | lam hfunTyL hfunSL hl₁ =>
    cases hl₁ with
    | lam hnatTyL₁ hnatSL₁ hl₂ =>
      cases hl₂ with
      | lam hnatTyL₂ hnatSL₂ hl₃ =>
        cases hr with
        | lam hfunTyR hfunSR hr₁ =>
          cases hr₁ with
          | lam hnatTyR₁ hnatSR₁ hr₂ =>
            cases hr₂ with
            | lam hnatTyR₂ hnatSR₂ hr₃ =>
              rename_i funTyL natTyL₁ natTyL₂ bodyL
                funTyR natTyR₁ natTyR₂ bodyR
              obtain ⟨_, hopSort⟩ := hop.isType wf trivial
              obtain ⟨hboolTy, hboolRestTy⟩ := hopSort.forallE_inv wf
              obtain ⟨hboolTy₁, hboolTy₂⟩ :=
                hboolRestTy.forallE_inv wf
              let ⟨_, hboolSort⟩ := hboolTy
              obtain ⟨_, hboolCi, _, hboolLen⟩ :=
                hboolSort.const_inv wf trivial
              have hboolS (Δ : VLCtx) :
                  TrExprS env [] Δ q(Bool) .bool :=
                .const hboolCi rfl (by simpa using hboolLen)
              have hboolBinS : TrExprS env [] []
                  q(Bool → Bool → Bool)
                  (.forallE .bool <| .forallE .bool .bool) :=
                .forallE hboolTy hboolRestTy (hboolS []) <|
                  .forallE hboolTy₁ hboolTy₂
                    (hboolS [(none, .vlam .bool)])
                    (hboolS [(none, .vlam .bool), (none, .vlam .bool)])
              have hfunEqL := hfunSL.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hboolBinS
              have hfunEqR := hfunSR.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hboolBinS
              obtain ⟨hopL, hopR, houter⟩ :=
                VEnv.instantiate_lamU_step wf heq hfunEqL hfunEqR hop
              simp only [VExpr.inst] at houter
              have hzT :=
                (hctors.natZeroS (Us := []) (Δ := [])).2
              obtain ⟨_, hnatSort⟩ := hzT.isType wf trivial
              obtain ⟨_, hnatCi, _, hnatLen⟩ :=
                hnatSort.const_inv wf trivial
              have hnatS (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat :=
                .const hnatCi rfl (by simpa using hnatLen)
              have hctxL : VLCtx.IsDefEq env 0
                  [(none, .vlam funTyL)] [(none, .vlam funTyL)] :=
                .refl wf ⟨trivial, nofun, hfunTyL⟩
              have hctxR : VLCtx.IsDefEq env 0
                  [(none, .vlam funTyR)] [(none, .vlam funTyR)] :=
                .refl wf ⟨trivial, nofun, hfunTyR⟩
              have hnatEqLCtx := TrExprS.uniq (Us := []) wf hctxL hnatSL₁
                (hnatS [(none, .vlam funTyL)])
              have hnatEqRCtx := TrExprS.uniq (Us := []) wf hctxR hnatSR₁
                (hnatS [(none, .vlam funTyR)])
              have hnatEqL := hnatEqLCtx.instN wf.ordered
                (.zero : Ctx.InstN [] op funTyL 0 [funTyL] []) hopL
              have hnatEqR := hnatEqRCtx.instN wf.ordered
                (.zero : Ctx.InstN [] op funTyR 0 [funTyR] []) hopR
              have hnatEqL' : env.IsDefEqU 0 [] (natTyL₁.inst op) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqL
              have hnatEqR' : env.IsDefEqU 0 [] (natTyR₁.inst op) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqR
              have haT :=
                (hctors.natLitS a (Us := []) (Δ := [])).2
              obtain ⟨haL, haR, hmiddle⟩ :=
                VEnv.instantiate_lamU_step wf houter hnatEqL' hnatEqR' haT
              simp only [VExpr.inst] at hmiddle
              have hctxL₂ : VLCtx.IsDefEq env 0
                  [(none, .vlam natTyL₁), (none, .vlam funTyL)]
                  [(none, .vlam natTyL₁), (none, .vlam funTyL)] :=
                .refl wf ⟨⟨trivial, nofun, hfunTyL⟩, nofun, hnatTyL₁⟩
              have hctxR₂ : VLCtx.IsDefEq env 0
                  [(none, .vlam natTyR₁), (none, .vlam funTyR)]
                  [(none, .vlam natTyR₁), (none, .vlam funTyR)] :=
                .refl wf ⟨⟨trivial, nofun, hfunTyR⟩, nofun, hnatTyR₁⟩
              have hnatEqL₂Ctx := TrExprS.uniq (Us := []) wf hctxL₂
                hnatSL₂ (hnatS [(none, .vlam natTyL₁),
                  (none, .vlam funTyL)])
              have hnatEqR₂Ctx := TrExprS.uniq (Us := []) wf hctxR₂
                hnatSR₂ (hnatS [(none, .vlam natTyR₁),
                  (none, .vlam funTyR)])
              have hnatEqL₂Op := hnatEqL₂Ctx.instN wf.ordered
                (.succ (.zero : Ctx.InstN [] op funTyL 0 [funTyL] [])) hopL
              have hnatEqR₂Op := hnatEqR₂Ctx.instN wf.ordered
                (.succ (.zero : Ctx.InstN [] op funTyR 0 [funTyR] [])) hopR
              have hnatEqL₂ := hnatEqL₂Op.instN wf.ordered
                (.zero : Ctx.InstN [] (.natLit a) (natTyL₁.inst op) 0
                  [natTyL₁.inst op] []) haL
              have hnatEqR₂ := hnatEqR₂Op.instN wf.ordered
                (.zero : Ctx.InstN [] (.natLit a) (natTyR₁.inst op) 0
                  [natTyR₁.inst op] []) haR
              have hnatEqL₂' : env.IsDefEqU 0 []
                  ((natTyL₂.inst op 1).inst (.natLit a)) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqL₂
              have hnatEqR₂' : env.IsDefEqU 0 []
                  ((natTyR₂.inst op 1).inst (.natLit a)) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqR₂
              have hbT :=
                (hctors.natLitS b (Us := []) (Δ := [])).2
              obtain ⟨hbL, hbR, hfinal⟩ :=
                VEnv.instantiate_lamU_step wf hmiddle hnatEqL₂' hnatEqR₂' hbT
              exact .intro funTyL natTyL₁ natTyL₂ bodyL
                funTyR natTyR₁ natTyR₂ bodyR
                hfunTyL hnatTyL₁ hnatTyL₂ hfunTyR hnatTyR₁ hnatTyR₂
                hnatEqLCtx hnatEqL₂Ctx hnatEqRCtx hnatEqR₂Ctx
                hopL hopR haT hbT haL haR hbL hbR hl₃ hr₃ hfinal

/-- Substitute the semantic bitwise prefix while preserving one dependent
local binder at the head of the context. -/
theorem VEnv.IsDefEqU.inst_bitwise_outer3 {env : VEnv}
    (wf : env.WF)
    {funTy natTy₁ natTy₂ proofTy op x y : VExpr} {a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (ha : env.HasType 0 [] (.natLit a) (natTy₁.inst op))
    (hb : env.HasType 0 [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)))
    (h : env.IsDefEqU 0 [proofTy, natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0
      [((proofTy.inst op 2).inst (.natLit a) 1).inst (.natLit b)]
      (((x.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1)
      (((y.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] [])))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      (natTy₁.inst op) 0 [natTy₁.inst op] []))) ha
  exact h₂.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)) 0
      [((natTy₂.inst op 1).inst (.natLit a))] [])) hb

/-- Typing counterpart of `IsDefEqU.inst_bitwise_outer3`. -/
theorem VEnv.HasType.inst_bitwise_outer3 {env : VEnv}
    (wf : env.WF)
    {funTy natTy₁ natTy₂ proofTy op x A : VExpr} {a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (ha : env.HasType 0 [] (.natLit a) (natTy₁.inst op))
    (hb : env.HasType 0 [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)))
    (h : env.HasType 0 [proofTy, natTy₂, natTy₁, funTy] x A) :
    env.HasType 0
      [((proofTy.inst op 2).inst (.natLit a) 1).inst (.natLit b)]
      (((x.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1)
      (((A.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] [])))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      (natTy₁.inst op) 0 [natTy₁.inst op] []))) ha
  exact h₂.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)) 0
      [((natTy₂.inst op 1).inst (.natLit a))] [])) hb

/-- Substitute the three semantic bitwise arguments from a three-entry local
context, discharging the context completely. -/
theorem VEnv.IsDefEqU.inst_bitwise3 {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ op x y : VExpr} {a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (ha : env.HasType 0 [] (.natLit a) (natTy₁.inst op))
    (hb : env.HasType 0 [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)))
    (h : env.IsDefEqU 0 [natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0 []
      (((x.inst op 2).inst (.natLit a) 1).inst (.natLit b))
      (((y.inst op 2).inst (.natLit a) 1).inst (.natLit b)) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] op funTy 0 [funTy] []))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit a)
      (natTy₁.inst op) 0 [natTy₁.inst op] [])) ha
  exact h₂.instN wf.ordered
    (.zero : Ctx.InstN [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)) 0
      [((natTy₂.inst op 1).inst (.natLit a))] []) hb

/-- Substitute the four semantic successor-equation binders while preserving
the dependent proof binder at the head of the context. -/
theorem VEnv.IsDefEqU.inst_bitwise_outer4 {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op x y : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (h : env.IsDefEqU 0
      [proofTy, natTy₃, natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)]
      ((((x.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1)
      ((((y.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] []))))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] (.natLit fuel)
      (natTy₁.inst op) 0 [natTy₁.inst op] [])))) hf
  have h₃ := h₂.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)) 0
      [((natTy₂.inst op 1).inst (.natLit fuel))] []))) ha
  exact h₃.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)) 0
      [(((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a))] [])) hb

theorem VEnv.HasType.inst_bitwise_outer4 {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op x A : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (h : env.HasType 0
      [proofTy, natTy₃, natTy₂, natTy₁, funTy] x A) :
    env.HasType 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)]
      ((((x.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1)
      ((((A.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] []))))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] (.natLit fuel)
      (natTy₁.inst op) 0 [natTy₁.inst op] [])))) hf
  have h₃ := h₂.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)) 0
      [((natTy₂.inst op 1).inst (.natLit fuel))] []))) ha
  exact h₃.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)) 0
      [(((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a))] [])) hb

/-- Semantic instantiation of the four ordinary binders of a certified
successor/successor bitwise equation. -/
inductive VEnv.BitwiseLam4Instantiation (env : VEnv)
    (leftBody rightBody : Expr) (op : VExpr)
    (fuel a b : Nat) : Prop where
  | intro (funTyL natTyL₁ natTyL₂ natTyL₃ bodyL : VExpr)
      (funTyR natTyR₁ natTyR₂ natTyR₃ bodyR : VExpr)
      (hfunTyL : env.IsType 0 [] funTyL)
      (hnatTyL₁ : env.IsType 0 [funTyL] natTyL₁)
      (hnatTyL₂ : env.IsType 0 [natTyL₁, funTyL] natTyL₂)
      (hnatTyL₃ : env.IsType 0 [natTyL₂, natTyL₁, funTyL] natTyL₃)
      (hfunTyR : env.IsType 0 [] funTyR)
      (hnatTyR₁ : env.IsType 0 [funTyR] natTyR₁)
      (hnatTyR₂ : env.IsType 0 [natTyR₁, funTyR] natTyR₂)
      (hnatTyR₃ : env.IsType 0 [natTyR₂, natTyR₁, funTyR] natTyR₃)
      (hnatEqL₁ : env.IsDefEqU 0 [funTyL] natTyL₁ .nat)
      (hnatEqL₂ : env.IsDefEqU 0 [natTyL₁, funTyL] natTyL₂ .nat)
      (hnatEqL₃ : env.IsDefEqU 0 [natTyL₂, natTyL₁, funTyL]
        natTyL₃ .nat)
      (hnatEqR₁ : env.IsDefEqU 0 [funTyR] natTyR₁ .nat)
      (hnatEqR₂ : env.IsDefEqU 0 [natTyR₁, funTyR] natTyR₂ .nat)
      (hnatEqR₃ : env.IsDefEqU 0 [natTyR₂, natTyR₁, funTyR]
        natTyR₃ .nat)
      (hopL : env.HasType 0 [] op funTyL)
      (hopR : env.HasType 0 [] op funTyR)
      (hfT : env.HasType 0 [] (.natLit fuel) .nat)
      (haT : env.HasType 0 [] (.natLit a) .nat)
      (hbT : env.HasType 0 [] (.natLit b) .nat)
      (hfL : env.HasType 0 [] (.natLit fuel) (natTyL₁.inst op))
      (hfR : env.HasType 0 [] (.natLit fuel) (natTyR₁.inst op))
      (haL : env.HasType 0 [] (.natLit a)
        ((natTyL₂.inst op 1).inst (.natLit fuel)))
      (haR : env.HasType 0 [] (.natLit a)
        ((natTyR₂.inst op 1).inst (.natLit fuel)))
      (hbL : env.HasType 0 [] (.natLit b)
        (((natTyL₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
      (hbR : env.HasType 0 [] (.natLit b)
        (((natTyR₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
      (leftS : TrExprS env []
        [(none, .vlam natTyL₃), (none, .vlam natTyL₂),
          (none, .vlam natTyL₁), (none, .vlam funTyL)] leftBody bodyL)
      (rightS : TrExprS env []
        [(none, .vlam natTyR₃), (none, .vlam natTyR₂),
          (none, .vlam natTyR₁), (none, .vlam funTyR)] rightBody bodyR)
      (eq : env.IsDefEqU 0 []
        ((((bodyL.inst op 3).inst (.natLit fuel) 2).inst
          (.natLit a) 1).inst (.natLit b))
        ((((bodyR.inst op 3).inst (.natLit fuel) 2).inst
          (.natLit a) 1).inst (.natLit b))) :
      BitwiseLam4Instantiation env leftBody rightBody op fuel a b

theorem VEnv.instantiate_bitwise_lam4_equation {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {leftBody rightBody : Expr} {l r : VExpr}
    (hl : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) <| .lam0 q(Nat) leftBody) l)
    (hr : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) <| .lam0 q(Nat) rightBody) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hop : env.HasType 0 [] op
      (.forallE .bool <| .forallE .bool .bool)) :
    VEnv.BitwiseLam4Instantiation env leftBody rightBody op fuel a b := by
  have h₃ := VEnv.instantiate_bitwise_lam3_equation wf hctors
    (a := fuel) (b := a) hl hr heq hop
  cases h₃ with
  | intro funTyL natTyL₁ natTyL₂ bodyL
      funTyR natTyR₁ natTyR₂ bodyR
      hfunTyL hnatTyL₁ hnatTyL₂ hfunTyR hnatTyR₁ hnatTyR₂
      hnatEqL₁ hnatEqL₂ hnatEqR₁ hnatEqR₂
      hopL hopR hfT haT hfL hfR haL haR hleftS hrightS hmiddle =>
    cases hleftS with
    | lam hnatTyL₃ hnatSL₃ hbodyL =>
      cases hrightS with
      | lam hnatTyR₃ hnatSR₃ hbodyR =>
        rename_i natTyL₃ bodyLFinal natTyR₃ bodyRFinal
        have hnatZeroT :=
          (hctors.natZeroS (Us := []) (Δ := [])).2
        obtain ⟨_, hnatSort⟩ := hnatZeroT.isType wf trivial
        obtain ⟨_, hnatCi, _, hnatLen⟩ :=
          hnatSort.const_inv wf trivial
        have hnatS (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat :=
          .const hnatCi rfl (by simpa using hnatLen)
        have hctxL : VLCtx.IsDefEq env 0
            [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
              (none, .vlam funTyL)]
            [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
              (none, .vlam funTyL)] :=
          .refl wf ⟨⟨⟨trivial, nofun, hfunTyL⟩, nofun, hnatTyL₁⟩,
            nofun, hnatTyL₂⟩
        have hctxR : VLCtx.IsDefEq env 0
            [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
              (none, .vlam funTyR)]
            [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
              (none, .vlam funTyR)] :=
          .refl wf ⟨⟨⟨trivial, nofun, hfunTyR⟩, nofun, hnatTyR₁⟩,
            nofun, hnatTyR₂⟩
        have hnatSLCtx := TrExprS.uniq (Us := []) wf hctxL hnatSL₃
          (hnatS [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
            (none, .vlam funTyL)])
        have hnatSRCtx := TrExprS.uniq (Us := []) wf hctxR hnatSR₃
          (hnatS [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
            (none, .vlam funTyR)])
        have hnatEqL := VEnv.IsDefEqU.inst_bitwise3 wf hopL hfL haL
          hnatSLCtx
        have hnatEqR := VEnv.IsDefEqU.inst_bitwise3 wf hopR hfR haR
          hnatSRCtx
        have hnatEqL' : env.IsDefEqU 0 []
            (((natTyL₃.inst op 2).inst (.natLit fuel) 1).inst
              (.natLit a)) .nat := by
          simpa [VExpr.nat, VExpr.inst] using hnatEqL
        have hnatEqR' : env.IsDefEqU 0 []
            (((natTyR₃.inst op 2).inst (.natLit fuel) 1).inst
              (.natLit a)) .nat := by
          simpa [VExpr.nat, VExpr.inst] using hnatEqR
        have hbT :=
          (hctors.natLitS b (Us := []) (Δ := [])).2
        obtain ⟨hbL, hbR, hfinal⟩ :=
          VEnv.instantiate_lamU_step wf hmiddle hnatEqL' hnatEqR' hbT
        exact .intro funTyL natTyL₁ natTyL₂ natTyL₃ bodyLFinal
          funTyR natTyR₁ natTyR₂ natTyR₃ bodyRFinal
          hfunTyL hnatTyL₁ hnatTyL₂ hnatTyL₃
          hfunTyR hnatTyR₁ hnatTyR₂ hnatTyR₃
          hnatEqL₁ hnatEqL₂ hnatSLCtx
          hnatEqR₁ hnatEqR₂ hnatSRCtx
          hopL hopR hfT haT hbT hfL hfR haL haR hbL hbR
          hbodyL hbodyR hfinal

/-- Weaken a closed translation under the four bitwise equation binders. -/
theorem bitwise_weak4
    {env : VEnv} (wf : env.WF) {src : Expr}
    {closedV funTy natTy₁ natTy₂ proofTy : VExpr}
    (hS : TrExprS env [] [] src closedV) :
    TrExprS env []
      [(none, .vlam proofTy), (none, .vlam natTy₂),
        (none, .vlam natTy₁), (none, .vlam funTy)] src
      (closedV.liftN 4) := by
  have hlift : src.liftLooseBVars' 0 4 = src :=
    Expr.liftLooseBVars_eq_self hS.closed.looseBVarRange_le
  simpa [VLocalDecl.depth, hlift] using hS.weakBV wf.ordered
    (.skip (.vlam proofTy) <| .skip (.vlam natTy₂) <|
      .skip (.vlam natTy₁) <| .skip (.vlam funTy) <|
        (.refl : VLCtx.BVLift [] [] 0 0 0 0))

/-- Weaken a closed translation under the five successor-equation binders. -/
theorem bitwise_weak5
    {env : VEnv} (wf : env.WF) {src : Expr}
    {closedV funTy natTy₁ natTy₂ natTy₃ proofTy : VExpr}
    (hS : TrExprS env [] [] src closedV) :
    TrExprS env []
      [(none, .vlam proofTy), (none, .vlam natTy₃),
        (none, .vlam natTy₂), (none, .vlam natTy₁),
        (none, .vlam funTy)] src
      (closedV.liftN 5) := by
  have hlift : src.liftLooseBVars' 0 5 = src :=
    Expr.liftLooseBVars_eq_self hS.closed.looseBVarRange_le
  simpa [VLocalDecl.depth, hlift] using hS.weakBV wf.ordered
    (.skip (.vlam proofTy) <| .skip (.vlam natTy₃) <|
      .skip (.vlam natTy₂) <| .skip (.vlam natTy₁) <|
        .skip (.vlam funTy) <|
          (.refl : VLCtx.BVLift [] [] 0 0 0 0))

/-- Instantiate a local occurrence of a closed expression under the three
semantic bitwise binders, discarding the vanishing instantiations on the
closed side. -/
theorem bitwise_local_closed_eq
    {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ proofTy op localV closedV : VExpr} {n₁ n₂ : Nat}
    (hop : env.HasType 0 [] op funTy)
    (h₁ : env.HasType 0 [] (.natLit n₁) (natTy₁.inst op))
    (h₂ : env.HasType 0 [] (.natLit n₂)
      ((natTy₂.inst op 1).inst (.natLit n₁)))
    (hclosed : closedV.ClosedN)
    (hctxEq : env.IsDefEqU 0 [proofTy, natTy₂, natTy₁, funTy]
      localV (closedV.liftN 4)) :
    env.IsDefEqU 0
      [((proofTy.inst op 2).inst (.natLit n₁) 1).inst (.natLit n₂)]
      (((localV.inst op 3).inst (.natLit n₁) 2).inst (.natLit n₂) 1)
      closedV := by
  simpa [hclosed.liftN_eq (Nat.zero_le _),
    hclosed.instN_eq (Nat.zero_le _)] using
    VEnv.IsDefEqU.inst_bitwise_outer3 wf hop h₁ h₂ hctxEq

/-- Instantiate a local occurrence of a closed expression under the four
semantic successor-equation binders, discarding the vanishing
instantiations on the closed side. -/
theorem bitwise_local_closed_eq4
    {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op localV closedV : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hclosed : closedV.ClosedN)
    (hctxEq : env.IsDefEqU 0 [proofTy, natTy₃, natTy₂, natTy₁, funTy]
      localV (closedV.liftN 5)) :
    env.IsDefEqU 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)]
      ((((localV.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1)
      closedV := by
  simpa [hclosed.liftN_eq (Nat.zero_le _),
    hclosed.instN_eq (Nat.zero_le _)] using
    VEnv.IsDefEqU.inst_bitwise_outer4 wf hop hf ha hb hctxEq

/-- Substitute the four semantic successor-equation binders and the
dependent proof value, discharging the local context completely. -/
theorem bitwise_root_eq {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op hpV x y : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hp : env.HasType 0 [] hpV
      ((((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)))
    (h : env.IsDefEqU 0 [proofTy, natTy₃, natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0 []
      (((((x.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV)
      (((((y.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV) :=
  (VEnv.IsDefEqU.inst_bitwise_outer4 wf hop hf ha hb h).instN wf.ordered
    (.zero : Ctx.InstN [] hpV
      ((((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)) 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)] []) hp

/-- `bitwise_root_eq` against a weakened closed expression, discarding the
vanishing instantiations on the closed side. -/
theorem bitwise_root_closed_eq {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op hpV localV closedV : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hp : env.HasType 0 [] hpV
      ((((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)))
    (hclosed : closedV.ClosedN)
    (hctxEq : env.IsDefEqU 0 [proofTy, natTy₃, natTy₂, natTy₁, funTy]
      localV (closedV.liftN 5)) :
    env.IsDefEqU 0 []
      (((((localV.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV)
      closedV := by
  simpa [hclosed.liftN_eq (Nat.zero_le _),
    hclosed.instN_eq (Nat.zero_le _)] using
    bitwise_root_eq wf hop hf ha hb hp hctxEq

/-- Evaluate a fully decomposed `boolNatITE` structure against reflected
condition and branch values. -/
theorem bitwise_struct_eval
    {env : VEnv} (wf : env.WF)
    {e iteV iteFinal condFinal thenFinal zeroFinal A : VExpr}
    {c : Bool} {t z : Nat}
    (hite : env.ReflectsBoolNatITE iteV)
    (heT : env.HasType 0 [] e A)
    (he : env.IsDefEqU 0 [] e
      (.app (.app (.app iteFinal condFinal) thenFinal) zeroFinal))
    (hiteEq : env.IsDefEqU 0 [] iteFinal iteV)
    (hcond : env.IsDefEqU 0 [] condFinal (.boolLit c))
    (hthen : env.IsDefEqU 0 [] thenFinal (.natLit t))
    (hzeroEq : env.IsDefEqU 0 [] zeroFinal (.natLit z)) :
    env.IsDefEqU 0 [] e (.natLit (if c then t else z)) := by
  have hstructT := (he.of_l wf trivial heT).hasType.2
  obtain ⟨_, _, hTwoT, hzT⟩ := hstructT.app_inv wf.ordered trivial
  obtain ⟨_, _, hOneT, hthenT⟩ := hTwoT.app_inv wf.ordered trivial
  obtain ⟨_, _, hiteT, hcondT⟩ := hOneT.app_inv wf.ordered trivial
  have h₁ := hiteEq.app_both wf trivial hcond hiteT hcondT
  have h₂ := h₁.app_both wf trivial hthen hOneT hthenT
  have h₃ := h₂.app_both wf trivial hzeroEq hTwoT hzT
  exact he.trans wf trivial (h₃.trans wf trivial (hite.2 c t z))

/-- Canonical translation and typing of a `g (Nat.succ x) 2` call for a
reflected binary `Nat` primitive, from a translated `Nat`-typed argument.
The successor-transition semantics uses this for its `Nat.mod` bit tests
and its `Nat.div` recursion arguments. -/
theorem VEnv.ReflectsNatNatNat.succ_two_canonS
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {g : Name} {G : Nat → Nat → Nat}
    (hg : env.ReflectsNatNatNat g G) (hgC : env.contains g)
    {Δ : VLCtx} {x : Expr} {x' : VExpr}
    (hx : TrExprS env [] Δ x x')
    (hxT : env.HasType 0 Δ.toCtx x' .nat) :
    TrExprS env [] Δ
      (mkApp2 (.const g []) (mkApp q(Nat.succ) x)
        (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero))))
      (.app (.app (.const g []) (.app .natSucc x')) (.natLit 2)) ∧
    env.HasType 0 Δ.toCtx
      (.app (.app (.const g []) (.app .natSucc x')) (.natLit 2)) .nat := by
  have ⟨hgT, _⟩ := hg hgC
  obtain ⟨_, hgCi, _, hgLen⟩ := (hgT 0 []).const_inv wf trivial
  have hgS : TrExprS env [] Δ (.const g []) (.const g []) :=
    .const hgCi rfl (by simpa using hgLen)
  have hsuccS := (hctors.natSuccS (Us := []) (Δ := Δ)).1
  have hsuccT := (hctors.natSuccS (Us := []) (Δ := Δ)).2
  have hzeroS := (hctors.natZeroS (Us := []) (Δ := Δ)).1
  have hzeroT := (hctors.natZeroS (Us := []) (Δ := Δ)).2
  have hsxS : TrExprS env [] Δ (mkApp q(Nat.succ) x)
      (.app .natSucc x') := .app hsuccT hxT hsuccS hx
  have hsxT := VEnv.HasType.app hsuccT hxT
  have honeS : TrExprS env [] Δ (mkApp q(Nat.succ) q(Nat.zero))
      (.natLit 1) := .app hsuccT hzeroT hsuccS hzeroS
  have htwoS : TrExprS env [] Δ
      (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero)))
      (.natLit 2) :=
    .app hsuccT (VEnv.HasType.app hsuccT hzeroT) hsuccS honeS
  have htwoT := (hctors.natLitS 2 (Us := []) (Δ := Δ)).2
  exact ⟨.app (VEnv.HasType.app (hgT 0 Δ.toCtx) hsxT) htwoT
      (.app (hgT 0 Δ.toCtx) hsxT hgS hsxS) htwoS,
    .app (.app (hgT 0 Δ.toCtx) hsxT) htwoT⟩

end Lean4Lean.Environment
