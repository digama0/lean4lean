import Lean4Lean.Primitive
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

theorem VEnv.addConst_constants_of_ne {env env' : VEnv}
    (h : env.addConst n ci = some env') (hne : n ≠ m) :
    env'.constants m = env.constants m := by
  unfold VEnv.addConst at h
  split at h <;> cases h
  simp [hne]

theorem VEnv.ReflectsNatNatNat.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNatNat fc f) :
    (env.addDefEq df).ReflectsNatNatNat fc f := by
  intro hfc
  let ⟨hty, heval⟩ := h hfc
  exact ⟨fun U Γ => (hty U Γ).mono VEnv.addDefEq_le,
    fun a b => (heval a b).mono VEnv.addDefEq_le⟩

theorem VEnv.ReflectsNatNat.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNat fc f) :
    (env.addDefEq df).ReflectsNatNat fc f := by
  intro hfc
  let ⟨hty, heval⟩ := h hfc
  exact ⟨fun U Γ => (hty U Γ).mono VEnv.addDefEq_le,
    fun a => (heval a).mono VEnv.addDefEq_le⟩

theorem VEnv.ReflectsNatNatBool.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNatBool fc f) :
    (env.addDefEq df).ReflectsNatNatBool fc f := by
  intro hfc
  let ⟨hty, heval⟩ := h hfc
  exact ⟨fun U Γ => (hty U Γ).mono VEnv.addDefEq_le,
    fun a b => (heval a b).mono VEnv.addDefEq_le⟩

theorem VEnv.ReflectsNatBitwise.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatBitwise fc) :
    (env.addDefEq df).ReflectsNatBitwise fc := by
  intro hfc
  let ⟨hty, heval⟩ := h hfc
  refine ⟨fun U Γ => (hty U Γ).mono VEnv.addDefEq_le, ?_⟩
  intro env' hle hwf op f hop a b
  exact heval env' (VEnv.addDefEq_le.trans hle) hwf op f hop a b

theorem VEnv.ReflectsNatNatNat.addConst {env env' : VEnv}
    (h : env.ReflectsNatNatNat fc f) (hadd : env.addConst n ci = some env')
    (hne : n ≠ fc) : env'.ReflectsNatNatNat fc f := by
  intro hfc
  have hsame := VEnv.addConst_constants_of_ne hadd hne
  let ⟨ci, hfc⟩ := hfc
  let ⟨hty, heval⟩ := h ⟨ci, by rwa [hsame] at hfc⟩
  exact ⟨fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd),
    fun a b => (heval a b).mono (VEnv.addConst_le hadd)⟩

theorem VEnv.ReflectsNatNat.addConst {env env' : VEnv}
    (h : env.ReflectsNatNat fc f) (hadd : env.addConst n ci = some env')
    (hne : n ≠ fc) : env'.ReflectsNatNat fc f := by
  intro hfc
  have hsame := VEnv.addConst_constants_of_ne hadd hne
  let ⟨ci, hfc⟩ := hfc
  let ⟨hty, heval⟩ := h ⟨ci, by rwa [hsame] at hfc⟩
  exact ⟨fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd),
    fun a => (heval a).mono (VEnv.addConst_le hadd)⟩

theorem VEnv.ReflectsNatNatBool.addConst {env env' : VEnv}
    (h : env.ReflectsNatNatBool fc f) (hadd : env.addConst n ci = some env')
    (hne : n ≠ fc) : env'.ReflectsNatNatBool fc f := by
  intro hfc
  have hsame := VEnv.addConst_constants_of_ne hadd hne
  let ⟨ci, hfc⟩ := hfc
  let ⟨hty, heval⟩ := h ⟨ci, by rwa [hsame] at hfc⟩
  exact ⟨fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd),
    fun a b => (heval a b).mono (VEnv.addConst_le hadd)⟩

theorem VEnv.ReflectsNatBitwise.addConst {env env' : VEnv}
    (h : env.ReflectsNatBitwise fc) (hadd : env.addConst n ci = some env')
    (hne : n ≠ fc) : env'.ReflectsNatBitwise fc := by
  intro hfc
  have hsame := VEnv.addConst_constants_of_ne hadd hne
  let ⟨ci, hfc⟩ := hfc
  let ⟨hty, heval⟩ := h ⟨ci, by rwa [hsame] at hfc⟩
  refine ⟨fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd), ?_⟩
  intro env'' hle hwf op f hop a b
  exact heval env'' ((VEnv.addConst_le hadd).trans hle) hwf op f hop a b

theorem VEnv.ReflectsBoolBin.mono {env env' : VEnv}
    (h : env.ReflectsBoolBin op f) (hle : env ≤ env') :
    env'.ReflectsBoolBin op f :=
  ⟨h.1.mono hle, fun a b => (h.2 a b).mono hle⟩

def VEnv.ReflectsBoolNatITE (env : VEnv) (ite : VExpr) :=
  env.HasType 0 [] ite (.forallE .bool <| .forallE .nat <| .forallE .nat .nat) ∧
  ∀ b x y, env.IsDefEqU 0 []
    (.app (.app (.app ite (.boolLit b)) (.natLit x)) (.natLit y))
    (.natLit (if b then x else y))

theorem VEnv.ReflectsBoolNatITE.of_equations {env : VEnv} {ite : VExpr}
    (henv : env.WF)
    (hboolT : ∀ b, env.HasType 0 [] (.boolLit b) .bool)
    (hnatTy₀ : env.IsType 0 [] .nat)
    (hnatTy₁ : env.IsType 0 [.nat] .nat)
    (hnatT : ∀ n Γ, env.HasType 0 Γ (.natLit n) .nat)
    (hite : env.HasType 0 [] ite
      (.forallE .bool <| .forallE .nat <| .forallE .nat .nat))
    (htrue : env.IsDefEqU 0 [] (.app ite .boolTrue)
      (.lam .nat <| .lam .nat <| .bvar 1))
    (hfalse : env.IsDefEqU 0 [] (.app ite .boolFalse)
      (.lam .nat <| .lam .nat <| .bvar 0)) :
    env.ReflectsBoolNatITE ite := by
  refine ⟨hite, fun b x y => ?_⟩
  have app_same {f g a A B}
      (hf : env.IsDefEqU 0 [] f g)
      (hft : env.HasType 0 [] f (.forallE A B))
      (ha : env.HasType 0 [] a A) :
      env.IsDefEqU 0 [] (.app f a) (.app g a) :=
    ⟨_, .appDF (hf.of_l henv trivial hft) ha⟩
  have hnatClosed : VExpr.nat.ClosedN := by
    exact ((hnatT 0 []).closedN' henv.ordered.closed trivial).2.2
  have hnatLitClosed (n) : (VExpr.natLit n).ClosedN := by
    exact ((hnatT n []).closedN' henv.ordered.closed trivial).1
  have hiteB : env.HasType 0 [] (.app ite (.boolLit b))
      (.forallE .nat <| .forallE .nat .nat) := .app hite (hboolT b)
  have hiteBX : env.HasType 0 [] (.app (.app ite (.boolLit b)) (.natLit x))
      (.forallE .nat .nat) := .app hiteB (hnatT x [])
  have hbranch : env.IsDefEqU 0 [] (ite.app (.boolLit b))
      (if b then (.lam .nat <| .lam .nat <| .bvar 1)
        else (.lam .nat <| .lam .nat <| .bvar 0)) := by
    cases b with
    | false => simpa [VExpr.boolLit] using hfalse
    | true => simpa [VExpr.boolLit] using htrue
  have happ₁ := app_same hbranch hiteB (hnatT x [])
  have happ₂ := app_same happ₁ hiteBX (hnatT y [])
  cases b with
  | false =>
    have hinner : env.HasType 0 [.nat] (.lam .nat <| .bvar 0)
        (.forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₁
      exact .lam hnatSort (.bvar .zero)
    have houter : env.HasType 0 [] (.lam .nat <| .lam .nat <| .bvar 0)
        (.forallE .nat <| .forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₀
      exact .lam hnatSort hinner
    have houterApp : env.HasType 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 0) (.natLit x))
        (.forallE .nat .nat) := .app houter (hnatT x [])
    have hbeta₁ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 0) (.natLit x))
        (.lam .nat <| .bvar 0) :=
      ⟨_, VEnv.IsDefEq.beta hinner (hnatT x [])⟩
    have hbeta₂ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .bvar 0) (.natLit y)) (.natLit y) :=
      by simpa [VExpr.inst] using
        (show env.IsDefEqU 0 []
          (.app (.lam .nat <| .bvar 0) (.natLit y))
          ((VExpr.bvar 0).inst (.natLit y)) from
            ⟨_, VEnv.IsDefEq.beta (.bvar (.zero)) (hnatT y [])⟩)
    have hbeta₁App := app_same hbeta₁ houterApp (hnatT y [])
    exact happ₂.trans henv trivial (hbeta₁App.trans henv trivial hbeta₂)
  | true =>
    have hinner : env.HasType 0 [.nat] (.lam .nat <| .bvar 1)
        (.forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₁
      exact .lam hnatSort (.bvar (.succ .zero))
    have houter : env.HasType 0 [] (.lam .nat <| .lam .nat <| .bvar 1)
        (.forallE .nat <| .forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₀
      exact .lam hnatSort hinner
    have houterApp : env.HasType 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit x))
        (.forallE .nat .nat) := .app houter (hnatT x [])
    have hbeta₁ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit x))
        (.lam .nat <| .natLit x) := by
      simpa [VExpr.inst, VExpr.inst_lift,
        hnatClosed.instN_eq, (hnatLitClosed x).lift_eq,
        (hnatLitClosed x).instN_eq] using (show env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit x))
        ((VExpr.lam .nat <| .bvar 1).inst (.natLit x)) from
          ⟨_, VEnv.IsDefEq.beta hinner (hnatT x [])⟩)
    have hbody : env.HasType 0 [.nat] (.natLit x) .nat := hnatT x [.nat]
    have hbeta₂ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .natLit x) (.natLit y)) (.natLit x) :=
      by simpa [VExpr.inst, hnatClosed.instN_eq,
          (hnatLitClosed x).instN_eq] using
        (show env.IsDefEqU 0 []
          (.app (.lam .nat <| .natLit x) (.natLit y))
          ((VExpr.natLit x).inst (.natLit y)) from
            ⟨_, VEnv.IsDefEq.beta hbody (hnatT y [])⟩)
    have hbeta₁App := app_same hbeta₁ houterApp (hnatT y [])
    exact happ₂.trans henv trivial (hbeta₁App.trans henv trivial hbeta₂)

/-- A closed, level-free constant whose declared type is definitionally equal
to `A` can be used at type `A` in every universe and local context. -/
theorem VEnv.HasType.const_of_type_defeq (henv : VEnv.WF env)
    (hci : env.constants n = some ci) (hu : ci.uvars = 0)
    (hty : env.IsDefEqU 0 [] ci.type A) :
  ∀ U Γ, env.HasType U Γ (.const n []) A := by
  intro U Γ
  obtain ⟨B, hty⟩ := hty
  have htyU := (show env.IsDefEqU 0 [] ci.type A from ⟨B, hty⟩).instL
    (ls := []) (U' := U) nofun
  have hlevels := hty.levelWF trivial
  rw [show [] = VLevel.params 0 by rfl, hlevels.1.instL_id,
    hlevels.2.1.instL_id] at htyU
  have hc := HasType.const (U := U) (Γ := []) (ls := []) hci (by simp)
    (by simpa using hu.symm)
  rw [show [] = VLevel.params 0 by rfl, hlevels.1.instL_id] at hc
  exact (HasType.defeqU_r henv trivial htyU hc).weak0 henv

theorem VEnv.IsDefEqU.app_same (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ f g)
    (hft : env.HasType U Γ f (.forallE A B))
    (ha : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app g a) :=
  ⟨_, .appDF (hf.of_l henv hΓ hft) ha⟩

theorem VEnv.IsDefEqU.app_arg (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.IsDefEqU U Γ a b)
    (hf : env.HasType U Γ f (.forallE A B))
    (hat : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app f b) :=
  ⟨_, .appDF hf (ha.of_l henv hΓ hat)⟩

theorem VEnv.IsDefEqU.app_both (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ f g)
    (ha : env.IsDefEqU U Γ a b)
    (hft : env.HasType U Γ f (.forallE A B))
    (hat : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app g b) :=
  ⟨_, .appDF (hf.of_l henv hΓ hft) (ha.of_l henv hΓ hat)⟩

theorem VEnv.boolNatITE_same_of_true_equation {env : VEnv}
    {ite cond A B : VExpr} {n : Nat} (henv : env.WF)
    (hnatTy₀ : env.IsType 0 [] .nat)
    (hnatTy₁ : env.IsType 0 [.nat] .nat)
    (hnatT : ∀ n Γ, env.HasType 0 Γ (.natLit n) .nat)
    (hiteT : env.HasType 0 [] ite (.forallE A B))
    (htrueT : env.HasType 0 [] .boolTrue A)
    (hcond : env.IsDefEqU 0 [] cond .boolTrue)
    (htrue : env.IsDefEqU 0 [] (.app ite .boolTrue)
      (.lam .nat <| .lam .nat <| .bvar 1)) :
    env.IsDefEqU 0 []
      (.app (.app (.app ite cond) (.natLit n)) (.natLit n)) (.natLit n) := by
  have hcond' := hcond.of_r henv trivial htrueT
  have hiteCond : env.IsDefEqU 0 [] (.app ite cond) (.app ite .boolTrue) :=
    ⟨_, .appDF hiteT hcond'⟩
  have hselect := hiteCond.trans henv trivial htrue
  have ⟨_, hnatSort⟩ := hnatTy₀
  have ⟨_, hnatSort₁⟩ := hnatTy₁
  have hinner : env.HasType 0 [.nat] (.lam .nat <| .bvar 1)
      (.forallE .nat .nat) := .lam hnatSort₁ (.bvar (.succ .zero))
  have hselector : env.HasType 0 [] (.lam .nat <| .lam .nat <| .bvar 1)
      (.forallE .nat <| .forallE .nat .nat) := .lam hnatSort hinner
  have hselectT := hselect.of_r henv trivial hselector
  have h₁ : env.IsDefEq 0 []
      (.app (.app ite cond) (.natLit n))
      (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
      (.forallE .nat .nat) := by
    simpa [VExpr.inst] using
      (VEnv.IsDefEq.appDF hselectT (hnatT n []))
  have h₂ : env.IsDefEqU 0 []
      (.app (.app (.app ite cond) (.natLit n)) (.natLit n))
      (.app (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
        (.natLit n)) := ⟨_, .appDF h₁ (hnatT n [])⟩
  have hnatClosed : VExpr.nat.ClosedN :=
    ((hnatT 0 []).closedN' henv.ordered.closed trivial).2.2
  have hnatLitClosed : (VExpr.natLit n).ClosedN :=
    ((hnatT n []).closedN' henv.ordered.closed trivial).1
  have hbeta₁ : env.IsDefEqU 0 []
      (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
      (.lam .nat <| .natLit n) := by
    simpa [VExpr.inst, VExpr.inst_lift, hnatClosed.instN_eq,
      hnatLitClosed.lift_eq, hnatLitClosed.instN_eq] using
      (show env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
        ((VExpr.lam .nat <| .bvar 1).inst (.natLit n)) from
          ⟨_, VEnv.IsDefEq.beta hinner (hnatT n [])⟩)
  have hbeta₁App := hbeta₁.app_same henv trivial
    (.app hselector (hnatT n [])) (hnatT n [])
  have hbody : env.HasType 0 [.nat] (.natLit n) .nat := hnatT n [.nat]
  have hbeta₂ : env.IsDefEqU 0 []
      (.app (.lam .nat <| .natLit n) (.natLit n)) (.natLit n) :=
    by simpa [VExpr.inst, hnatClosed.instN_eq, hnatLitClosed.instN_eq] using
      (show env.IsDefEqU 0 []
        (.app (.lam .nat <| .natLit n) (.natLit n))
        ((VExpr.natLit n).inst (.natLit n)) from
          ⟨_, VEnv.IsDefEq.beta hbody (hnatT n [])⟩)
  exact h₂.trans henv trivial <| hbeta₁App.trans henv trivial hbeta₂

/-- A concrete eager fuel reduces to its numeral once its Boolean condition is
known to be reflexive.  This is the semantic use of the open eager equation
retained by the well-founded recursion certificate. -/
theorem VEnv.eager_natLit_of_equation {env : VEnv} {ite eager : VExpr}
    (henv : env.WF)
    (hnatT : ∀ n, env.HasType 0 [] (.natLit n) .nat)
    (hbeq : env.ReflectsNatNatBool ``Nat.beq Nat.beq)
    (hbeqC : env.contains ``Nat.beq)
    (hite : env.ReflectsBoolNatITE ite)
    (heager : env.IsDefEqU 0 [] (.app eager (.natLit n))
      (.app (.app (.app ite
        (.app (.app (.const ``Nat.beq []) (.natLit n)) (.natLit n)))
        (.natLit n)) (.natLit n))) :
    env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
  let ⟨hbeqT, hbeqEval⟩ := hbeq hbeqC
  have hcondT : env.HasType 0 []
      (.app (.app (.const ``Nat.beq []) (.natLit n)) (.natLit n)) .bool :=
    .app (.app (hbeqT 0 []) (hnatT n)) (hnatT n)
  have hcond := hbeqEval n n
  have h₁ := hcond.app_arg henv trivial hite.1 hcondT
  have hiteCond : env.HasType 0 []
      (.app ite (.app (.app (.const ``Nat.beq []) (.natLit n)) (.natLit n)))
      (.forallE .nat <| .forallE .nat .nat) := .app hite.1 hcondT
  have h₂ := h₁.app_same henv trivial hiteCond (hnatT n)
  have hiteCondN : env.HasType 0 []
      (.app (.app ite
        (.app (.app (.const ``Nat.beq []) (.natLit n)) (.natLit n)))
        (.natLit n)) (.forallE .nat .nat) := .app hiteCond (hnatT n)
  have h₃ := h₂.app_same henv trivial hiteCondN (hnatT n)
  exact heager.trans henv trivial <| h₃.trans henv trivial <| by
    simpa using hite.2 true n n

theorem VEnv.IsDefEqU.lam_inst (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A e₁) (.lam A e₂))
    (hA : env.HasType U Γ A (.sort u))
    (h₁ : env.HasType U (A :: Γ) e₁ B)
    (h₂ : env.HasType U (A :: Γ) e₂ B)
    (ha : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ : env.IsDefEq U Γ (.app (.lam A e₁) a) (.app (.lam A e₂) a) (B.inst a) :=
    .appDF (h.of_l henv hΓ (.lam hA h₁)) ha
  exact ⟨_, (VEnv.IsDefEq.beta h₁ ha).symm.trans
    (happ.trans (VEnv.IsDefEq.beta h₂ ha))⟩

/-- Instantiate definitionally equal lambdas without requiring the two body
typing derivations to expose the same result type syntactically. -/
theorem VEnv.IsDefEqU.lam_instU (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A e₁) (.lam A e₂))
    (hA : env.HasType U Γ A (.sort u))
    (h₁ : env.HasType U (A :: Γ) e₁ B₁)
    (h₂ : env.HasType U (A :: Γ) e₂ B₂)
    (ha : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ := h.app_same henv hΓ (.lam hA h₁) ha
  have hbeta₁ : env.IsDefEqU U Γ (.app (.lam A e₁) a) (e₁.inst a) :=
    ⟨_, .beta h₁ ha⟩
  have hbeta₂ : env.IsDefEqU U Γ (.app (.lam A e₂) a) (e₂.inst a) :=
    ⟨_, .beta h₂ ha⟩
  exact hbeta₁.symm.trans henv hΓ happ |>.trans henv hΓ hbeta₂

theorem VEnv.IsDefEqU.lam_instU₂ (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A₁ e₁) (.lam A₂ e₂))
    (hA₁ : env.HasType U Γ A₁ (.sort u₁))
    (hbody₁ : env.HasType U (A₁ :: Γ) e₁ B₁)
    (hbody₂ : env.HasType U (A₂ :: Γ) e₂ B₂)
    (hA : env.IsDefEqU U Γ A₁ A₂)
    (ha : env.HasType U Γ a A₁) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ := h.app_same henv hΓ (.lam hA₁ hbody₁) ha
  have ha₂ := ha.defeqU_r henv hΓ hA
  have hbeta₁ : env.IsDefEqU U Γ (.app (.lam A₁ e₁) a) (e₁.inst a) :=
    ⟨_, .beta hbody₁ ha⟩
  have hbeta₂ : env.IsDefEqU U Γ (.app (.lam A₂ e₂) a) (e₂.inst a) :=
    ⟨_, .beta hbody₂ ha₂⟩
  exact hbeta₁.symm.trans henv hΓ happ |>.trans henv hΓ hbeta₂

/-- Instantiate both sides of a checked source lambda equation while retaining
translations of the instantiated source bodies. -/
theorem VEnv.instantiate_lam_equation {env : VEnv}
    (wf : env.WF) (huniq : TrExprS.IsUnique ty)
    (hl : TrExprS env Us Δ (.lam name ty body bi) l)
    (hr : TrExprS env Us Δ (.lam name' ty body' bi') r)
    (heq : env.IsDefEqU Us.length Δ.toCtx l r)
    (htyCanon : TrExprS env Us Δ ty A)
    (haS : TrExprS env Us Δ a a')
    (haT : env.HasType Us.length Δ.toCtx a' A)
    (hΔ : Δ.WF env Us.length) :
    ∃ l' r',
      TrExprS env Us Δ (body.instantiate1' a) l' ∧
      TrExprS env Us Δ (body'.instantiate1' a) r' ∧
      env.IsDefEqU Us.length Δ.toCtx l' r' := by
  cases hl with
  | lam hAT htyL hbodyL =>
    cases hr with
    | lam hAT' htyR hbodyR =>
      cases htyL.unique huniq htyCanon
      cases htyR.unique huniq htyCanon
      have hl' := TrExprS.inst wf.ordered haT hbodyL haS
      have hr' := TrExprS.inst wf.ordered haT hbodyR haS
      obtain ⟨BL, hbodyLT⟩ := hbodyL.wf wf.ordered
        (Us := Us) (Δ := (none, .vlam A) :: Δ) ⟨hΔ, nofun, hAT⟩
      obtain ⟨BR, hbodyRT⟩ := hbodyR.wf wf.ordered
        (Us := Us) (Δ := (none, .vlam A) :: Δ) ⟨hΔ, nofun, hAT⟩
      obtain ⟨u, hASort⟩ := hAT
      have hi := VEnv.IsDefEqU.lam_instU wf hΔ.toCtx heq hASort
        hbodyLT hbodyRT haT
      exact ⟨_, _, hl', hr', hi⟩

theorem VEnv.ReflectsNatNatNat.nat_of_contains (henv : VEnv.WF env)
    (h : env.ReflectsNatNatNat fc f) (hc : env.contains fc) :
    env.contains ``Nat := by
  have hfun := (h hc).1 0 []
  have ⟨_, H⟩ := hfun.isType henv trivial
  let ⟨⟨_, H⟩, _⟩ := H.forallE_inv henv
  let ⟨_, H, _⟩ := H.const_inv henv trivial
  exact ⟨_, H⟩

theorem VDefVal.const_defeq_value {env : VEnv} {v : VDefVal}
    (henv : (env.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0) :
    (env.addDefEq v.toDefEq).IsDefEqU 0 [] (.const v.name []) v.value := by
  have hwf := henv.ordered.defEqWF VEnv.addDefEq_self
  have h := VEnv.IsDefEq.extra0 VEnv.addDefEq_self hwf
  simpa [VDefVal.toDefEq, hu] using h.toU

theorem VEnv.ReflectsNatNat.of_pred_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.pred []) (.forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.pred []) f)
    (hz : env.IsDefEqU 0 [] (.app f .natZero) .natZero)
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .app f (.app .natSucc (.bvar 0)))
      (.lam .nat <| .bvar 0)) :
    env.ReflectsNatNat ``Nat.pred Nat.pred := by
  intro _
  refine ⟨hf, fun a => ?_⟩
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hfv₁ : env.HasType 0 [.nat] f (.forallE .nat .nat) :=
    (hf 0 [.nat]).defeqU_l henv ⟨trivial, ⟨_, hNatSort⟩⟩ (hcf.weak0 henv)
  have hbody₁ : env.HasType 0 [.nat] (.app f (.app .natSucc (.bvar 0))) .nat :=
    .app hfv₁ (.app (hsuccT _) (.bvar .zero))
  have hbody₂ : env.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
  cases a with
  | zero =>
    have hcf0 := hcf.app_same henv trivial (hf 0 []) (hzeroT [])
    exact hcf0.trans henv trivial hz
  | succ a =>
    have hcfSucc := hcf.app_same henv trivial (hf 0 []) (.app (hsuccT []) (hlit a []))
    have hs' := hs.lam_inst henv trivial hNatSort hbody₁ hbody₂ (hlit a [])
    simp [VExpr.inst, VExpr.natSucc, hfClosed.instN_eq] at hs'
    exact hcfSucc.trans henv trivial hs'

theorem VEnv.ReflectsNatNatNat.of_add_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.add [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.add []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app .natSucc (.app (.app f (.bvar 1)) (.bvar 0)))) :
    env.ReflectsNatNatNat ``Nat.add Nat.add := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) :=
    ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.add []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have hbody₂ : env.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
    have hz' :=
      hz.lam_inst henv trivial hNatSort hbody₁ hbody₂ (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at hz'
    simpa [VExpr.inst, VExpr.natLit] using (hcfApp a 0).trans henv trivial hz'
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) (.app (hsuccT _) hbvar0)
    have hright : env.HasType 0 [.nat, .nat]
        (.app .natSucc (.app (.app f (.bvar 1)) (.bvar 0))) .nat :=
      .app (hsuccT _) (.app (.app (hfv _ hctx₂) hbvar1) hbvar0)
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <|
          .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <|
          .app .natSucc (.app (.app f (.bvar 1)) (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit a [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
      (hlit b [])
    simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
    have hcongr := ih.app_arg henv trivial (hsuccT [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    have hback := (hcfApp a b).symm.app_arg henv trivial (hsuccT [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    exact (hcfApp a (b+1)).trans henv trivial <|
      hstep.trans henv trivial <| hback.trans henv trivial hcongr

theorem VEnv.ReflectsNatNatNat.of_sub_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hpred : env.ReflectsNatNat ``Nat.pred Nat.pred)
    (hpredC : env.contains ``Nat.pred)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.sub [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.sub []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.const ``Nat.pred []) (.app (.app f (.bvar 1)) (.bvar 0)))) :
    env.ReflectsNatNatNat ``Nat.sub Nat.sub := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  let ⟨hpredT, hpredEval⟩ := hpred hpredC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.sub []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have hbody₂ : env.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
    have hz' := hz.lam_inst henv trivial hNatSort hbody₁ hbody₂ (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at hz'
    simpa [VExpr.natLit] using (hcfApp a 0).trans henv trivial hz'
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) (.app (hsuccT _) hbvar0)
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.const ``Nat.pred []) (.app (.app f (.bvar 1)) (.bvar 0))) .nat :=
      .app (hpredT 0 _) (.app (.app (hfv _ hctx₂) hbvar1) hbvar0)
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.const ``Nat.pred [])
          (.app (.app f (.bvar 1)) (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit a [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
      (hlit b [])
    simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
    have hback := (hcfApp a b).symm.app_arg henv trivial (hpredT 0 [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    have hcongr := ih.app_arg henv trivial (hpredT 0 [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    exact (hcfApp a (b+1)).trans henv trivial <| hstep.trans henv trivial <|
      hback.trans henv trivial <| hcongr.trans henv trivial (hpredEval (a - b))

theorem VEnv.ReflectsNatNatNat.of_mul_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hadd : env.ReflectsNatNatNat ``Nat.add Nat.add)
    (haddC : env.contains ``Nat.add)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.mul [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.mul []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.add [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    env.ReflectsNatNatNat ``Nat.mul Nat.mul := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  let ⟨haddT, haddEval⟩ := hadd haddC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.mul []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have hz' := hz.lam_inst henv trivial hNatSort hbody₁ (hzeroT _) (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at hz'
    exact (hcfApp a 0).trans henv trivial hz'
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
    have hfbody : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.bvar 0)) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) hbvar0
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) (.app (hsuccT _) hbvar0)
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.app (.const ``Nat.add [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1)) .nat :=
      .app (.app (haddT 0 _) hfbody) hbvar1
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app (.const ``Nat.add [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit a [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
      (hlit b [])
    simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
    have hback₁ := (hcfApp a b).symm.app_arg henv trivial (haddT 0 [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    have hback := hback₁.app_same henv trivial
      (.app (haddT 0 []) (.app (.app (hfv [] trivial) (hlit a [])) (hlit b [])))
      (hlit a [])
    have hcongr₁ := ih.app_arg henv trivial (haddT 0 [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    have hcongr := hcongr₁.app_same henv trivial
      (.app (haddT 0 []) (.app (.app (hf 0 []) (hlit a [])) (hlit b [])))
      (hlit a [])
    exact (hcfApp a (b+1)).trans henv trivial <| hstep.trans henv trivial <|
      hback.trans henv trivial <| hcongr.trans henv trivial (haddEval (a * b) a)

theorem VEnv.ReflectsNatNatNat.of_pow_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hmul : env.ReflectsNatNatNat ``Nat.mul Nat.mul)
    (hmulC : env.contains ``Nat.mul)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.pow [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.pow []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .app .natSucc .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.mul [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    env.ReflectsNatNatNat ``Nat.pow Nat.pow := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  let ⟨hmulT, hmulEval⟩ := hmul hmulC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.pow []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have honeT : env.HasType 0 [.nat] (.app .natSucc .natZero) .nat :=
      .app (hsuccT [.nat]) (hzeroT [.nat])
    have hz' := hz.lam_inst henv trivial hNatSort hbody₁ honeT (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at hz'
    exact (hcfApp a 0).trans henv trivial hz'
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
    have hfbody : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.bvar 0)) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) hbvar0
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) (.app (hsuccT _) hbvar0)
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.app (.const ``Nat.mul [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1)) .nat :=
      .app (.app (hmulT 0 _) hfbody) hbvar1
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app (.const ``Nat.mul [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit a [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
      (hlit b [])
    simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
    have hback₁ := (hcfApp a b).symm.app_arg henv trivial (hmulT 0 [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    have hback := hback₁.app_same henv trivial
      (.app (hmulT 0 []) (.app (.app (hfv [] trivial) (hlit a [])) (hlit b [])))
      (hlit a [])
    have hcongr₁ := ih.app_arg henv trivial (hmulT 0 [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    have hcongr := hcongr₁.app_same henv trivial
      (.app (hmulT 0 []) (.app (.app (hf 0 []) (hlit a [])) (hlit b [])))
      (hlit a [])
    exact (hcfApp a (b+1)).trans henv trivial <| hstep.trans henv trivial <|
      hback.trans henv trivial <| hcongr.trans henv trivial (hmulEval (a ^ b) a)

/-- The four constructor equations checked for `Nat.beq` and `Nat.ble`
determine a Boolean-valued operation on naturals. -/
theorem VEnv.ReflectsNatNatBool.of_rec_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hboolT : ∀ b Γ, env.HasType 0 Γ (.boolLit b) .bool)
    (hf : ∀ U Γ, env.HasType U Γ (.const fc [])
      (.forallE .nat <| .forallE .nat .bool))
    (hcf : env.IsDefEqU 0 [] (.const fc []) f)
    (h00 : env.IsDefEqU 0 []
      (.app (.app f .natZero) .natZero) (.boolLit r00))
    (h0s : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f .natZero) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .boolLit r0s))
    (hs0 : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.app .natSucc (.bvar 0))) .natZero)
      (.lam .nat <| .boolLit rs0))
    (hss : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <| .app (.app f (.bvar 1)) (.bvar 0)))
    (hg00 : g 0 0 = r00) (hg0s : ∀ b, g 0 (b+1) = r0s)
    (hgs0 : ∀ a, g (a+1) 0 = rs0)
    (hgss : ∀ a b, g (a+1) (b+1) = g a b) :
    env.ReflectsNatNatBool fc g := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .bool) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const fc []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [hg00] using (hcfApp 0 0).trans henv trivial h00
    | succ b =>
      have hbody : env.HasType 0 [.nat]
          (.app (.app f .natZero) (.app .natSucc (.bvar 0))) .bool :=
        .app (.app (hfv _ hctx₁) (hzeroT _)) (.app (hsuccT _) (.bvar .zero))
      have heq := h0s.lam_inst henv trivial hNatSort hbody (hboolT r0s _) (hlit b [])
      cases r0s <;>
        simp [VExpr.inst, VExpr.natLit, VExpr.natZero, VExpr.natSucc, VExpr.boolLit,
          VExpr.boolFalse, VExpr.boolTrue, hfClosed.instN_eq, hg0s] at heq ⊢ <;>
        exact (hcfApp 0 (b+1)).trans henv trivial heq
  | succ a ih =>
    cases b with
    | zero =>
      have hbody : env.HasType 0 [.nat]
          (.app (.app f (.app .natSucc (.bvar 0))) .natZero) .bool :=
        .app (.app (hfv _ hctx₁) (.app (hsuccT _) (.bvar .zero))) (hzeroT _)
      have heq := hs0.lam_inst henv trivial hNatSort hbody (hboolT rs0 _) (hlit a [])
      cases rs0 <;>
        simp [VExpr.inst, VExpr.natLit, VExpr.natZero, VExpr.natSucc, VExpr.boolLit,
          VExpr.boolFalse, VExpr.boolTrue, hfClosed.instN_eq, hgs0] at heq ⊢ <;>
        exact (hcfApp (a+1) 0).trans henv trivial heq
    | succ b =>
      have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hleft : env.HasType 0 [.nat, .nat]
          (.app (.app f (.app .natSucc (.bvar 1)))
            (.app .natSucc (.bvar 0))) .bool :=
        .app (.app (hfv _ hctx₂) (.app (hsuccT _) hbvar1))
          (.app (hsuccT _) hbvar0)
      have hright : env.HasType 0 [.nat, .nat]
          (.app (.app f (.bvar 1)) (.bvar 0)) .bool :=
        .app (.app (hfv _ hctx₂) hbvar1) hbvar0
      have hinner₁ : env.HasType 0 [.nat]
          (.lam .nat <| .app (.app f (.app .natSucc (.bvar 1)))
            (.app .natSucc (.bvar 0))) (.forallE .nat .bool) :=
        .lam (hNatSort.weak0 henv) hleft
      have hinner₂ : env.HasType 0 [.nat]
          (.lam .nat <| .app (.app f (.bvar 1)) (.bvar 0))
          (.forallE .nat .bool) := .lam (hNatSort.weak0 henv) hright
      have houter := hss.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit a [])
      have heq := houter.lam_inst henv trivial hNatSort
        (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
        (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
        (hlit b [])
      simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at heq
      rw [hgss]
      exact (hcfApp (a+1) (b+1)).trans henv trivial <|
        heq.trans henv trivial <| (hcfApp a b).symm.trans henv trivial (ih b)

theorem VEnv.ReflectsNatNatNat.of_gcd_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hmodC : env.contains ``Nat.mod)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.gcd []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f .natZero) (.bvar 0))
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.app .natSucc (.bvar 1))) (.bvar 0))
      (.lam .nat <| .lam .nat <|
        .app (.app f
          (.app (.app (.const ``Nat.mod []) (.bvar 0))
            (.app .natSucc (.bvar 1))))
          (.app .natSucc (.bvar 1)))) :
    env.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  let ⟨hmodT, hmodEval⟩ := hmod hmodC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.gcd []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction a, b using Nat.gcd.induction with
  | H0 b =>
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f .natZero) (.bvar 0)) .nat :=
      .app (.app (hfv _ hctx₁) (hzeroT _)) (.bvar .zero)
    have hbody₂ : env.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
    have heq := hz.lam_inst henv trivial hNatSort hbody₁ hbody₂ (hlit b [])
    simp [VExpr.inst, hfClosed.instN_eq] at heq
    simpa using (hcfApp 0 b).trans henv trivial heq
  | H1 m b hm ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
      have hsucc : env.HasType 0 [.nat, .nat]
          (.app .natSucc (.bvar 1)) .nat := .app (hsuccT _) hbvar1
      have hleft : env.HasType 0 [.nat, .nat]
          (.app (.app f (.app .natSucc (.bvar 1))) (.bvar 0)) .nat :=
        .app (.app (hfv _ hctx₂) hsucc) hbvar0
      have hmodBody : env.HasType 0 [.nat, .nat]
          (.app (.app (.const ``Nat.mod []) (.bvar 0))
            (.app .natSucc (.bvar 1))) .nat :=
        .app (.app (hmodT 0 _) hbvar0) hsucc
      have hright : env.HasType 0 [.nat, .nat]
          (.app (.app f
            (.app (.app (.const ``Nat.mod []) (.bvar 0))
              (.app .natSucc (.bvar 1))))
            (.app .natSucc (.bvar 1))) .nat :=
        .app (.app (hfv _ hctx₂) hmodBody) hsucc
      have hinner₁ : env.HasType 0 [.nat]
          (.lam .nat <| .app (.app f (.app .natSucc (.bvar 1))) (.bvar 0))
          (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
      have hinner₂ : env.HasType 0 [.nat]
          (.lam .nat <| .app (.app f
            (.app (.app (.const ``Nat.mod []) (.bvar 0))
              (.app .natSucc (.bvar 1))))
            (.app .natSucc (.bvar 1)))
          (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
      have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit m [])
      have hstep := houter.lam_inst henv trivial hNatSort
        (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit m []))
        (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit m []))
        (hlit b [])
      simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
      have hmodEq := hmodEval b (m+1)
      have harg := hmodEq.app_arg henv trivial (hfv [] trivial)
        (.app (.app (hmodT 0 []) (hlit b [])) (hlit (m+1) []))
      have hrec : env.IsDefEqU 0 []
          (.app (.app f (.natLit (b % (m+1)))) (.natLit (m+1)))
          (.natLit (Nat.gcd (b % (m+1)) (m+1))) := by
        exact (hcfApp (b % (m+1)) (m+1)).symm.trans henv trivial ih
      exact (hcfApp (m+1) b).trans henv trivial <| hstep.trans henv trivial <|
        harg.app_same henv trivial
          (.app (hfv [] trivial)
            (.app (.app (hmodT 0 []) (hlit b [])) (hlit (m+1) [])))
          (hlit (m+1) []) |>.trans henv trivial <| by
            simpa [Nat.gcd_succ] using hrec

/-- Fuel-level equations for the compiled `WellFounded.Nat.fix.go` used by
`Nat.gcd` suffice for reflection.  The proof argument carried by `go` is
existential, just as for the lower-level `Nat.modCore.go` certificate: proof
irrelevance makes its identity immaterial, while the decreasing fuel is the
piece needed for the semantic induction. -/
theorem VEnv.ReflectsNatNatNat.of_gcd_fix_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.gcd []) f)
    (go : Nat → VExpr → VExpr → VExpr) (state : Nat → Nat → VExpr)
    (htop : ∀ a b, ∃ hp, env.IsDefEqU 0 []
      (.app (.app f (.natLit a)) (.natLit b)) (go (a + 1) (state a b) hp))
    (hgo : ∀ fuel a b hp,
      env.IsDefEqU 0 [] (go (fuel + 1) (state a b) hp)
        (go (fuel + 1) (state a b) hp) →
      if a = 0 then
        env.IsDefEqU 0 [] (go (fuel + 1) (state a b) hp) (.natLit b)
      else
        ∃ hp', env.IsDefEqU 0 []
          (go (fuel + 1) (state a b) hp) (go fuel (state (b % a) a) hp')) :
    env.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.gcd []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  have goEval : ∀ fuel a b hp,
      env.IsDefEqU 0 [] (go fuel (state a b) hp) (go fuel (state a b) hp) →
      a < fuel → env.IsDefEqU 0 []
        (go fuel (state a b) hp) (.natLit (Nat.gcd a b)) := by
    intro fuel
    induction fuel with
    | zero => simp
    | succ fuel ih =>
      intro a b hp hgoTy ha
      by_cases ha0 : a = 0
      · subst a
        simpa using hgo fuel 0 b hp hgoTy
      · obtain ⟨hp', hstep⟩ := by
          simpa [ha0] using hgo fuel a b hp hgoTy
        have hapos : 0 < a := Nat.zero_lt_of_ne_zero ha0
        have hmod : b % a < fuel :=
          Nat.lt_of_lt_of_le (Nat.mod_lt b hapos) (Nat.lt_succ_iff.mp ha)
        have hrec := ih (b % a) a hp'
          (hstep.symm.trans henv trivial hstep) hmod
        cases a with
        | zero => contradiction
        | succ a =>
          exact hstep.trans henv trivial <| by
            simpa [Nat.gcd_succ] using hrec
  obtain ⟨hp, htop⟩ := htop a b
  exact (hcfApp a b).trans henv trivial <|
    htop.trans henv trivial (goEval (a + 1) a b hp
      (htop.symm.trans henv trivial htop) (by omega))

/-- Relational form of the fuel-level gcd argument.  This is the natural
interface for checked source equations: independently translated recursive
calls need only belong to the same semantic call relation, rather than be
syntactically generated by one chosen translation. -/
theorem VEnv.ReflectsNatNatNat.of_gcd_fix_relation (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.gcd []) f)
    (G : Nat → Nat → Nat → VExpr → Prop)
    (htop : ∀ a b, ∃ e, G (a + 1) a b e ∧ env.IsDefEqU 0 []
      (.app (.app f (.natLit a)) (.natLit b)) e)
    (hgo : ∀ fuel a b e, G (fuel + 1) a b e →
      env.IsDefEqU 0 [] e e →
      if a = 0 then env.IsDefEqU 0 [] e (.natLit b)
      else ∃ e', G fuel (b % a) a e' ∧ env.IsDefEqU 0 [] e e') :
    env.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.gcd []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x []))
      (hlit y [])
  have goEval : ∀ fuel a b e, G fuel a b e →
      env.IsDefEqU 0 [] e e → a < fuel →
      env.IsDefEqU 0 [] e (.natLit (Nat.gcd a b)) := by
    intro fuel
    induction fuel with
    | zero => simp
    | succ fuel ih =>
      intro a b e hG heTy ha
      by_cases ha0 : a = 0
      · subst a
        simpa using hgo fuel 0 b e hG heTy
      · obtain ⟨e', hG', hstep⟩ := by
          simpa [ha0] using hgo fuel a b e hG heTy
        have hapos : 0 < a := Nat.zero_lt_of_ne_zero ha0
        have hmod : b % a < fuel :=
          Nat.lt_of_lt_of_le (Nat.mod_lt b hapos) (Nat.lt_succ_iff.mp ha)
        have hrec := ih (b % a) a e' hG'
          (hstep.symm.trans henv trivial hstep) hmod
        cases a with
        | zero => contradiction
        | succ a =>
          exact hstep.trans henv trivial <| by
            simpa [Nat.gcd_succ] using hrec
  obtain ⟨e, hG, htop⟩ := htop a b
  exact (hcfApp a b).trans henv trivial <|
    htop.trans henv trivial (goEval (a + 1) a b e hG
      (htop.symm.trans henv trivial htop) (by omega))

/-- A guarded subtraction equation characterizes natural-number remainder.
This is the semantic boundary used by the lower-level `Nat.modCore.go`
verification. -/
theorem VEnv.ReflectsNatNatNat.of_mod_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.mod [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.mod []) f)
    (hstep : ∀ a b,
      if 0 < b ∧ b ≤ a then
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b))
          (.app (.app f (.natLit (a - b))) (.natLit b))
      else
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b)) (.natLit a)) :
    env.ReflectsNatNatNat ``Nat.mod Nat.mod := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.mod []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have heq : a.mod b = if 0 < b ∧ b ≤ a then (a - b).mod b else a := by
      simpa using Nat.mod_eq a b
    rw [heq]
    split
    · rename_i hab
      have hlt : a - b < a := Nat.sub_lt_self hab.1 hab.2
      have hs := hstep a b
      simp [hab] at hs
      exact (hcfApp a b).trans henv trivial <|
        hs.trans henv trivial <|
          (hcfApp (a - b) b).symm.trans henv trivial (ih (a - b) hlt)
    · rename_i hab
      have hs := hstep a b
      simp [hab] at hs
      exact (hcfApp a b).trans henv trivial hs

/-- The corresponding guarded subtraction equation for natural-number
division. -/
theorem VEnv.ReflectsNatNatNat.of_div_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.div [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.div []) f)
    (hstep : ∀ a b,
      if 0 < b ∧ b ≤ a then
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b))
          (.app .natSucc
            (.app (.app f (.natLit (a - b))) (.natLit b)))
      else
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b)) .natZero) :
    env.ReflectsNatNatNat ``Nat.div Nat.div := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hft : env.HasType 0 [] f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 []).defeqU_l henv trivial hcf
  have hfApp (x y) : env.HasType 0 []
      (.app (.app f (.natLit x)) (.natLit y)) .nat :=
    .app (.app hft (hlit x [])) (hlit y [])
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.div []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have heq : a.div b =
        if 0 < b ∧ b ≤ a then (a - b).div b + 1 else 0 := by
      simpa using Nat.div_eq a b
    rw [heq]
    split
    · rename_i hab
      have hlt : a - b < a := Nat.sub_lt_self hab.1 hab.2
      have hs := hstep a b
      simp [hab] at hs
      have hrec := (hcfApp (a - b) b).symm.trans henv trivial (ih (a - b) hlt)
      have hsucc := hrec.app_arg henv trivial (hsuccT [])
        (hfApp (a - b) b)
      simpa [VExpr.natLit] using
        (hcfApp a b).trans henv trivial (hs.trans henv trivial hsucc)
    · rename_i hab
      have hs := hstep a b
      simp [hab] at hs
      simpa using (hcfApp a b).trans henv trivial hs

def VExpr.natModGo (y fuel x : Nat) (hy hfuel : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Nat.modCore.go []) (.natLit y)) hy)
    (.natLit fuel)) (.natLit x)) hfuel

/-- The fuel-level equations checked for `Nat.modCore.go` imply semantic
remainder reflection.  The proof arguments are intentionally existential:
their identity is irrelevant, while their presence records the dependent
applications produced by the checker. -/
theorem VEnv.ReflectsNatNatNat.of_modCore_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.mod [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.mod []) f)
    (htop : ∀ a b,
      if 0 < b ∧ b ≤ a then
        ∃ hy hfuel, env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b))
          (.natModGo b (a + 1) a hy hfuel)
      else
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b)) (.natLit a))
    (hgo : ∀ y fuel x hy hfuel,
      if y ≤ x then
        ∃ hy' hfuel', env.IsDefEqU 0 []
          (.natModGo y (fuel + 1) x hy hfuel)
          (.natModGo y fuel (x - y) hy' hfuel')
      else
        env.IsDefEqU 0 []
          (.natModGo y (fuel + 1) x hy hfuel) (.natLit x)) :
    env.ReflectsNatNatNat ``Nat.mod Nat.mod := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.mod []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  have goEval (y : Nat) (hypos : 0 < y) :
      ∀ fuel x hy hfuel, x < fuel → env.IsDefEqU 0 []
        (.natModGo y fuel x hy hfuel) (.natLit (x.mod y)) := by
    intro fuel
    induction fuel with
    | zero => intro x _ _ hlt; omega
    | succ fuel ih =>
      intro x hy hfuel hlt
      have hg := hgo y fuel x hy hfuel
      split at hg
      · rename_i hyx
        obtain ⟨hy', hfuel', hg⟩ := hg
        have hsubx : x - y < x := Nat.sub_lt_self hypos hyx
        have hsubfuel : x - y < fuel := by omega
        have hrec := ih (x - y) hy' hfuel' hsubfuel
        have heq : x.mod y = (x - y).mod y := by
          simpa [hypos, hyx] using Nat.mod_eq x y
        rw [heq]
        exact hg.trans henv trivial hrec
      · rename_i hyx
        have heq : x.mod y = x := by
          simpa [hyx] using Nat.mod_eq x y
        rw [heq]
        exact hg
  have ht := htop a b
  split at ht
  · rename_i hab
    obtain ⟨hy, hfuel, ht⟩ := ht
    exact (hcfApp a b).trans henv trivial <|
      ht.trans henv trivial (goEval b hab.1 (a + 1) a hy hfuel (by omega))
  · rename_i hab
    have heq : a.mod b = a := by
      simpa [hab] using Nat.mod_eq a b
    rw [heq]
    exact (hcfApp a b).trans henv trivial ht

def VExpr.natDivGo (y fuel x : Nat) (hy hfuel : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Nat.div.go []) (.natLit y)) hy)
    (.natLit fuel)) (.natLit x)) hfuel

/-- Fuel adequacy for the checked `Nat.div.go` equation, and hence semantic
reflection of natural-number division. -/
theorem VEnv.ReflectsNatNatNat.of_divCore_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.div [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.div []) f)
    (hgoT : ∀ y fuel x hy hfuel,
      env.HasType 0 [] (.natDivGo y fuel x hy hfuel) .nat)
    (htop : ∀ a b,
      if 0 < b then
        ∃ hy hfuel, env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b))
          (.natDivGo b (a + 1) a hy hfuel)
      else
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b)) .natZero)
    (hgo : ∀ y fuel x hy hfuel,
      if y ≤ x then
        ∃ hy' hfuel', env.IsDefEqU 0 []
          (.natDivGo y (fuel + 1) x hy hfuel)
          (.app .natSucc (.natDivGo y fuel (x - y) hy' hfuel'))
      else
        env.IsDefEqU 0 []
          (.natDivGo y (fuel + 1) x hy hfuel) .natZero) :
    env.ReflectsNatNatNat ``Nat.div Nat.div := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.div []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  have goEval (y : Nat) (hypos : 0 < y) :
      ∀ fuel x hy hfuel, x < fuel → env.IsDefEqU 0 []
        (.natDivGo y fuel x hy hfuel) (.natLit (x.div y)) := by
    intro fuel
    induction fuel with
    | zero => intro x _ _ hlt; omega
    | succ fuel ih =>
      intro x hy hfuel hlt
      have hg := hgo y fuel x hy hfuel
      split at hg
      · rename_i hyx
        obtain ⟨hy', hfuel', hg⟩ := hg
        have hsubx : x - y < x := Nat.sub_lt_self hypos hyx
        have hsubfuel : x - y < fuel := by omega
        have hrec := ih (x - y) hy' hfuel' hsubfuel
        have hsucc := hrec.app_arg henv trivial (hsuccT [])
          (hgoT y fuel (x - y) hy' hfuel')
        have heq : x.div y = (x - y).div y + 1 := by
          simpa [hypos, hyx] using Nat.div_eq x y
        rw [heq]
        simpa [VExpr.natLit] using hg.trans henv trivial hsucc
      · rename_i hyx
        have heq : x.div y = 0 := by
          have hformula : x.div y =
              if 0 < y ∧ y ≤ x then (x - y).div y + 1 else 0 := by
            simpa using Nat.div_eq x y
          rw [hformula]
          simp [hyx]
        rw [heq]
        exact hg
  have ht := htop a b
  split at ht
  · rename_i hb
    obtain ⟨hy, hfuel, ht⟩ := ht
    exact (hcfApp a b).trans henv trivial <|
      ht.trans henv trivial (goEval b hb (a + 1) a hy hfuel (by omega))
  · rename_i hb
    have heq : a.div b = 0 := by
      have hformula : a.div b =
          if 0 < b ∧ b ≤ a then (a - b).div b + 1 else 0 := by
        simpa using Nat.div_eq a b
      rw [hformula]
      simp [hb]
    rw [heq]
    exact (hcfApp a b).trans henv trivial ht

theorem VEnv.ReflectsNatNatNat.of_bitwise_specialization (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hbitwise : env.ReflectsNatBitwise ``Nat.bitwise)
    (hbitwiseC : env.contains ``Nat.bitwise)
    (hf : ∀ U Γ, env.HasType U Γ (.const fc [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const fc [])
      (.app (.const ``Nat.bitwise []) op))
    (hop : env.ReflectsBoolBin op f)
    (hg : g = Nat.bitwise f) : env.ReflectsNatNatNat fc g := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
  have h₂ := h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  have heval := (hbitwise hbitwiseC).2 env .rfl henv op f hop a b
  exact h₂.trans henv trivial <| by simpa [hg] using heval

/-- Fuel adequacy for a relational presentation of the compiled
`Nat.bitwise` fixpoint.  The transition interface leaves the recursive result
abstract; its continuation is what turns the induction hypothesis into the
guarded bitwise result. -/
theorem VEnv.evalNatBitwise_of_fix_relation (henv : VEnv.WF env)
    (G : Nat → Nat → Nat → VExpr → Prop)
    (htop : ∀ a b, ∃ e, G (a + 1) a b e ∧ env.IsDefEqU 0 []
      (.app (.app (.app g op) (.natLit a)) (.natLit b)) e)
    (hgo : ∀ fuel a b e, G (fuel + 1) a b e →
      env.IsDefEqU 0 [] e e →
      if a = 0 then
        env.IsDefEqU 0 [] e (.natLit (if f false true then b else 0))
      else if b = 0 then
        env.IsDefEqU 0 [] e (.natLit (if f true false then a else 0))
      else ∃ e', G fuel (a / 2) (b / 2) e' ∧
        env.IsDefEqU 0 [] e' e' ∧
        ∀ q, env.IsDefEqU 0 [] e' (.natLit q) →
          env.IsDefEqU 0 [] e
            (.natLit (if f (a % 2 = 1) (b % 2 = 1)
              then q + q + 1 else q + q))) :
    ∀ a b, env.IsDefEqU 0 []
      (.app (.app (.app g op) (.natLit a)) (.natLit b))
      (.natLit (Nat.bitwise f a b)) := by
  have goEval : ∀ fuel a b e, G fuel a b e →
      env.IsDefEqU 0 [] e e → a < fuel →
      env.IsDefEqU 0 [] e (.natLit (Nat.bitwise f a b)) := by
    intro fuel
    induction fuel with
    | zero => simp
    | succ fuel ih =>
      intro a b e hG heTy haFuel
      by_cases ha : a = 0
      · subst a
        simpa [Nat.bitwise] using hgo fuel 0 b e hG heTy
      · by_cases hb : b = 0
        · subst b
          simpa [Nat.bitwise, ha] using hgo fuel a 0 e hG heTy
        · obtain ⟨e', hG', he'Ty, hfinish⟩ := by
            simpa [ha, hb] using hgo fuel a b e hG heTy
          have haPos : 0 < a := Nat.zero_lt_of_ne_zero ha
          have haHalf : a / 2 < fuel :=
            Nat.lt_of_lt_of_le (Nat.bitwise_rec_lemma ha)
              (Nat.lt_succ_iff.mp haFuel)
          have hrec := ih (a / 2) (b / 2) e' hG' he'Ty haHalf
          have hresult : Nat.bitwise f a b =
              if f (a % 2 = 1) (b % 2 = 1) then
                Nat.bitwise f (a / 2) (b / 2) +
                  Nat.bitwise f (a / 2) (b / 2) + 1
              else
                Nat.bitwise f (a / 2) (b / 2) +
                  Nat.bitwise f (a / 2) (b / 2) := by
            rw [Nat.bitwise]
            simp [ha, hb]
          rw [hresult]
          exact hfinish _ hrec
  intro a b
  obtain ⟨e, hG, ht⟩ := htop a b
  exact ht.trans henv trivial <| goEval (a + 1) a b e hG
    (ht.symm.trans henv trivial ht) (by omega)

/-- The checked division-by-two recursion equation characterizes
`Nat.bitwise`.  It is stated Kripke-style so that Boolean operators introduced
after `Nat.bitwise` can be supplied in a future environment. -/
theorem VEnv.ReflectsNatBitwise.of_equations
    (henv : VEnv.WF env) (hprim : env.HasPrimitives)
    (haddC : env.contains ``Nat.add)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.bitwise [])
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.bitwise []) g)
    (hstep : ∀ env', env ≤ env' → ∀ op f, env'.ReflectsBoolBin op f →
      ∀ a b,
      if a = 0 then
        env'.IsDefEqU 0 []
          (.app (.app (.app g op) (.natLit a)) (.natLit b))
          (.natLit (if f false true then b else 0))
      else if b = 0 then
        env'.IsDefEqU 0 []
          (.app (.app (.app g op) (.natLit a)) (.natLit b))
          (.natLit (if f true false then a else 0))
      else
        let r := .app (.app (.app g op) (.natLit (a / 2))) (.natLit (b / 2))
        if f (a % 2 = 1) (b % 2 = 1) then
          env'.IsDefEqU 0 []
            (.app (.app (.app g op) (.natLit a)) (.natLit b))
            (.app (.app (.const ``Nat.add [])
              (.app (.app (.const ``Nat.add []) r) r)) (.natLit 1))
        else
          env'.IsDefEqU 0 []
            (.app (.app (.app g op) (.natLit a)) (.natLit b))
            (.app (.app (.const ``Nat.add []) r) r)) :
    env.ReflectsNatBitwise ``Nat.bitwise := by
  intro _
  refine ⟨hf, fun env' le hwf op f hop a b => ?_⟩
  have hf' (U Γ) := (hf U Γ).mono le
  have hcf' := hcf.mono le
  have ⟨haddT, haddEval⟩ := hprim.natAdd haddC
  have haddT' (U Γ) := (haddT U Γ).mono le
  have haddEval' (x y) := (haddEval x y).mono le
  have hnat := hprim.natAdd.nat_of_contains henv haddC
  have hzero (Γ) : env'.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env'.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc hprim hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hlit (n) (Γ) : env'.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzero Γ
    | succ n ih => exact .app (hsucc Γ) ih
  have hgT : env'.HasType 0 [] g
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat) :=
    (hf' 0 []).defeqU_l hwf trivial hcf'
  have hgopT : env'.HasType 0 [] (.app g op)
      (.forallE .nat <| .forallE .nat .nat) := .app hgT hop.1
  have hgAppT (x y) : env'.HasType 0 []
      (.app (.app (.app g op) (.natLit x)) (.natLit y)) .nat :=
    .app (.app hgopT (hlit x [])) (hlit y [])
  have hcfApp (x y) : env'.IsDefEqU 0 []
      (.app (.app (.app (.const ``Nat.bitwise []) op) (.natLit x)) (.natLit y))
      (.app (.app (.app g op) (.natLit x)) (.natLit y)) := by
    have h₁ := hcf'.app_same hwf trivial (hf' 0 []) hop.1
    have h₂ := h₁.app_same hwf trivial (.app (hf' 0 []) hop.1) (hlit x [])
    exact h₂.app_same hwf trivial (.app (.app (hf' 0 []) hop.1) (hlit x []))
      (hlit y [])
  have doubleEval (r : VExpr) (hrT : env'.HasType 0 [] r .nat)
      (q : Nat) (hr : env'.IsDefEqU 0 [] r (.natLit q)) :
      env'.IsDefEqU 0 []
        (.app (.app (.const ``Nat.add []) r) r) (.natLit (q + q)) := by
    have hleft := hr.app_arg hwf trivial (haddT' 0 []) hrT
    have hleftApp := hleft.app_same hwf trivial
      (.app (haddT' 0 []) hrT) hrT
    have hright := hr.app_arg hwf trivial
      (.app (haddT' 0 []) (hlit q [])) hrT
    exact hleftApp.trans hwf trivial <| hright.trans hwf trivial (haddEval' q q)
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    have hs := hstep env' le op f hop a b
    split at hs
    · rename_i ha
      subst a
      simpa [Nat.bitwise] using (hcfApp 0 b).trans hwf trivial hs
    · rename_i ha
      split at hs
      · rename_i hb
        subst b
        simpa [Nat.bitwise, ha] using (hcfApp a 0).trans hwf trivial hs
      · rename_i hb
        have haPos : 0 < a := Nat.zero_lt_of_ne_zero ha
        have haHalf : a / 2 < a := Nat.bitwise_rec_lemma ha
        have hrec := (hcfApp (a / 2) (b / 2)).symm.trans hwf trivial
          (ih (a / 2) haHalf (b / 2))
        have hdoub := doubleEval _ (hgAppT (a / 2) (b / 2))
          (Nat.bitwise f (a / 2) (b / 2)) hrec
        split at hs
        · rename_i hbit
          have hresult : Nat.bitwise f a b =
              Nat.bitwise f (a / 2) (b / 2) +
                Nat.bitwise f (a / 2) (b / 2) + 1 := by
            rw [Nat.bitwise]
            simp only [ha, hb, if_false, hbit, if_true]
          rw [hresult]
          have hplus := hdoub.app_arg hwf trivial (haddT' 0 [])
            (.app (.app (haddT' 0 []) (hgAppT (a / 2) (b / 2)))
              (hgAppT (a / 2) (b / 2)))
          have hplusOne := hplus.app_same hwf trivial
            (.app (haddT' 0 [])
              (.app (.app (haddT' 0 []) (hgAppT (a / 2) (b / 2)))
                (hgAppT (a / 2) (b / 2)))) (hlit 1 [])
          exact (hcfApp a b).trans hwf trivial <| hs.trans hwf trivial <|
            hplusOne.trans hwf trivial
              (haddEval'
                (Nat.bitwise f (a / 2) (b / 2) +
                  Nat.bitwise f (a / 2) (b / 2)) 1)
        · rename_i hbit
          have hresult : Nat.bitwise f a b =
              Nat.bitwise f (a / 2) (b / 2) +
                Nat.bitwise f (a / 2) (b / 2) := by
            rw [Nat.bitwise]
            simp [ha, hb, hbit]
          rw [hresult]
          exact (hcfApp a b).trans hwf trivial <| hs.trans hwf trivial hdoub

/-- Constructor-specialized equations suffice for the guarded equation used
by `ReflectsNatBitwise.of_equations`.  This is the form emitted by the
primitive checker, since constructor specialization computes the Nat equality
guards before semantic reasoning begins. -/
theorem VEnv.ReflectsNatBitwise.of_constructor_equations
    (henv : VEnv.WF env) (hprim : env.HasPrimitives)
    (haddC : env.contains ``Nat.add)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.bitwise [])
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.bitwise []) g)
    (hz : ∀ env', env ≤ env' → ∀ op f, env'.ReflectsBoolBin op f →
      ∀ b, env'.IsDefEqU 0 []
        (.app (.app (.app g op) .natZero) (.natLit b))
        (.natLit (if f false true then b else 0)))
    (hzr : ∀ env', env ≤ env' → ∀ op f, env'.ReflectsBoolBin op f →
      ∀ a, env'.IsDefEqU 0 []
        (.app (.app (.app g op) (.natLit (a + 1))) .natZero)
        (.natLit (if f true false then a + 1 else 0)))
    (hss : ∀ env', env ≤ env' → ∀ op f, env'.ReflectsBoolBin op f →
      ∀ a b,
      let a' := a + 1
      let b' := b + 1
      let r := .app (.app (.app g op) (.natLit (a' / 2))) (.natLit (b' / 2))
      if f (a' % 2 = 1) (b' % 2 = 1) then
        env'.IsDefEqU 0 []
          (.app (.app (.app g op) (.natLit a')) (.natLit b'))
          (.app (.app (.const ``Nat.add [])
            (.app (.app (.const ``Nat.add []) r) r)) (.natLit 1))
      else
        env'.IsDefEqU 0 []
          (.app (.app (.app g op) (.natLit a')) (.natLit b'))
          (.app (.app (.const ``Nat.add []) r) r)) :
    env.ReflectsNatBitwise ``Nat.bitwise := by
  apply VEnv.ReflectsNatBitwise.of_equations henv hprim haddC hf hcf
  intro env' le op f hop a b
  cases a with
  | zero => simpa using hz env' le op f hop b
  | succ a =>
    cases b with
    | zero => simpa [Nat.succ_eq_add_one] using hzr env' le op f hop a
    | succ b => simpa [Nat.succ_eq_add_one] using hss env' le op f hop a b

theorem VEnv.ReflectsBoolBin.of_table {env : VEnv}
    (hop : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hff : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolFalse) (.boolLit (f false false)))
    (hft : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolTrue) (.boolLit (f false true)))
    (htf : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolFalse) (.boolLit (f true false)))
    (htt : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolTrue) (.boolLit (f true true))) :
    env.ReflectsBoolBin op f := by
  refine ⟨hop, fun a b => ?_⟩
  cases a <;> cases b <;> assumption

theorem VEnv.ReflectsBoolBin.of_and_equations {env : VEnv} (henv : env.WF)
    (hboolT : ∀ b Γ, env.HasType 0 Γ (.boolLit b) .bool)
    (hop : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool .boolFalse))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool <| .bvar 0)) : env.ReflectsBoolBin op and := by
  have ⟨_, hBoolSort⟩ := (hboolT false []).isType henv trivial
  have hopClosed : op.ClosedN :=
    (hop.closedN' henv.ordered.closed trivial).2.1
  have hfalseL : env.HasType 0 [.bool]
      (.app (.app op .boolFalse) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT false _)) (.bvar .zero)
  have htrueL : env.HasType 0 [.bool]
      (.app (.app op .boolTrue) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT true _)) (.bvar .zero)
  have hfalse (b) := hf.lam_inst henv trivial hBoolSort hfalseL
    (hboolT false _) (hboolT b [])
  have htrue (b) := ht.lam_inst henv trivial hBoolSort htrueL
    (.bvar .zero) (hboolT b [])
  have hff := hfalse false
  have hft := hfalse true
  have htf := htrue false
  have htt := htrue true
  simp [VExpr.inst, hopClosed.instN_eq] at hff hft htf htt
  exact .of_table hop hff hft htf htt

theorem VEnv.ReflectsBoolBin.of_or_equations {env : VEnv} (henv : env.WF)
    (hboolT : ∀ b Γ, env.HasType 0 Γ (.boolLit b) .bool)
    (hop : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool <| .bvar 0))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool .boolTrue)) : env.ReflectsBoolBin op or := by
  have ⟨_, hBoolSort⟩ := (hboolT false []).isType henv trivial
  have hopClosed : op.ClosedN :=
    (hop.closedN' henv.ordered.closed trivial).2.1
  have hfalseL : env.HasType 0 [.bool]
      (.app (.app op .boolFalse) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT false _)) (.bvar .zero)
  have htrueL : env.HasType 0 [.bool]
      (.app (.app op .boolTrue) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT true _)) (.bvar .zero)
  have hfalse (b) := hf.lam_inst henv trivial hBoolSort hfalseL
    (.bvar .zero) (hboolT b [])
  have htrue (b) := ht.lam_inst henv trivial hBoolSort htrueL
    (hboolT true _) (hboolT b [])
  have hff := hfalse false
  have hft := hfalse true
  have htf := htrue false
  have htt := htrue true
  simp [VExpr.inst, hopClosed.instN_eq] at hff hft htf htt
  exact .of_table hop hff hft htf htt

theorem VEnv.ReflectsNatNatNat.of_shiftLeft_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hmul : env.ReflectsNatNatNat ``Nat.mul Nat.mul)
    (hmulC : env.contains ``Nat.mul)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.shiftLeft [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.shiftLeft []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 0)) (.app .natSucc (.bvar 1)))
      (.lam .nat <| .lam .nat <|
        .app (.app f
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0))) (.bvar 1))) :
    env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  let ⟨hmulT, hmulEval⟩ := hmul hmulC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.shiftLeft []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b generalizing a with
  | zero =>
    have hbody : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have heq := hz.lam_inst henv trivial hNatSort hbody (.bvar .zero) (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at heq
    exact (hcfApp a 0).trans henv trivial heq
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 0)) (.app .natSucc (.bvar 1))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar0) (.app (hsuccT _) hbvar1)
    have hmulBody : env.HasType 0 [.nat, .nat]
        (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)) .nat :=
      .app (.app (hmulT 0 _) (hlit 2 _)) hbvar0
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.app f
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0))) (.bvar 1)) .nat :=
      .app (.app (hfv _ hctx₂) hmulBody) hbvar1
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 0)) (.app .natSucc (.bvar 1)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0))) (.bvar 1))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit b [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit b []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit b []))
      (hlit a [])
    simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
    have hmulEq := hmulEval 2 a
    have harg := hmulEq.app_arg henv trivial (hfv [] trivial)
      (.app (.app (hmulT 0 []) (hlit 2 [])) (hlit a []))
    have hfa : env.HasType 0 []
        (.app f (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.natLit a)))
        (.forallE .nat .nat) :=
      .app (hfv [] trivial) (.app (.app (hmulT 0 []) (hlit 2 [])) (hlit a []))
    have hargs := harg.app_same henv trivial hfa (hlit b [])
    exact (hcfApp a (b+1)).trans henv trivial <| hstep.trans henv trivial <|
      hargs.trans henv trivial <| (hcfApp (2*a) b).symm.trans henv trivial (ih (a := 2*a))

theorem VEnv.ReflectsNatNatNat.of_shiftRight_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hdiv : env.ReflectsNatNatNat ``Nat.div Nat.div)
    (hdivC : env.contains ``Nat.div)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.shiftRight [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.shiftRight []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 0)) (.app .natSucc (.bvar 1)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.div [])
          (.app (.app f (.bvar 0)) (.bvar 1))) (.natLit 2))) :
    env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  let ⟨hdivT, hdivEval⟩ := hdiv hdivC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) := ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.shiftRight []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    have hbody : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have heq := hz.lam_inst henv trivial hNatSort hbody (.bvar .zero) (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at heq
    exact (hcfApp a 0).trans henv trivial heq
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat := .bvar (.succ .zero)
    have hfbody : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 0)) (.bvar 1)) .nat :=
      .app (.app (hfv _ hctx₂) hbvar0) hbvar1
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 0)) (.app .natSucc (.bvar 1))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar0) (.app (hsuccT _) hbvar1)
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.app (.const ``Nat.div [])
          (.app (.app f (.bvar 0)) (.bvar 1))) (.natLit 2)) .nat := by
      exact .app (.app (hdivT 0 _) hfbody) (hlit 2 _)
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 0)) (.app .natSucc (.bvar 1)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app (.const ``Nat.div [])
          (.app (.app f (.bvar 0)) (.bvar 1))) (.natLit 2))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂ (hlit b [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit b []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit b []))
      (hlit a [])
    simp [VExpr.inst, VExpr.natSucc, VExpr.inst_lift, hfClosed.instN_eq] at hstep
    have hback₁ := (hcfApp a b).symm.app_arg henv trivial (hdivT 0 [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    have hback := hback₁.app_same henv trivial
      (.app (hdivT 0 []) (.app (.app (hfv [] trivial) (hlit a [])) (hlit b [])))
      (hlit 2 [])
    have hcongr₁ := ih.app_arg henv trivial (hdivT 0 [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    have hcongr := hcongr₁.app_same henv trivial
      (.app (hdivT 0 []) (.app (.app (hf 0 []) (hlit a [])) (hlit b [])))
      (hlit 2 [])
    exact (hcfApp a (b+1)).trans henv trivial <| hstep.trans henv trivial <|
      hback.trans henv trivial <| hcongr.trans henv trivial
        (hdivEval (Nat.shiftRight a b) 2)

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.HasPrimitives) : (env.addDefEq df).HasPrimitives where
  bool := h.bool
  boolType := h.boolType
  boolFalse := h.boolFalse
  boolTrue := h.boolTrue
  nat := h.nat
  natType := h.natType
  natZero := h.natZero
  natSucc := h.natSucc
  natPred := h.natPred.addDefEq
  natAdd := h.natAdd.addDefEq
  natSub := h.natSub.addDefEq
  natMul := h.natMul.addDefEq
  natPow := h.natPow.addDefEq
  natGcd := h.natGcd.addDefEq
  natMod := h.natMod.addDefEq
  natDiv := h.natDiv.addDefEq
  natBEq := h.natBEq.addDefEq
  natBLE := h.natBLE.addDefEq
  natBitwise := h.natBitwise.addDefEq
  natLAnd := h.natLAnd.addDefEq
  natLOr := h.natLOr.addDefEq
  natXor := h.natXor.addDefEq
  natShiftLeft := h.natShiftLeft.addDefEq
  natShiftRight := h.natShiftRight.addDefEq
  charOfNat hci :=
    let ⟨hu, hty⟩ := h.charOfNat hci
    ⟨hu, fun U Γ => (hty U Γ).mono VEnv.addDefEq_le⟩
  stringOfList hci :=
    let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList hci
    ⟨hu, fun U Γ => (hty U Γ).mono VEnv.addDefEq_le,
      hnil.mono VEnv.addDefEq_le, hcons.mono VEnv.addDefEq_le⟩

theorem VEnv.HasPrimitives.bool_hasType {env : VEnv}
    (h : env.HasPrimitives) (hbool : env.contains ``Bool) :
    env.HasType 0 [] .bool (.sort (.succ .zero)) := by
  obtain ⟨ci, hci⟩ := hbool
  have hshape := h.boolType hci
  subst ci
  exact .const hci nofun rfl

theorem VEnv.HasPrimitives.nat_hasType {env : VEnv}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat) :
    env.HasType 0 [] .nat (.sort (.succ .zero)) := by
  obtain ⟨ci, hci⟩ := hnat
  have hshape := h.natType hci
  subst ci
  exact .const hci nofun rfl

theorem VEnv.HasPrimitives.empty : VEnv.empty.HasPrimitives := by
  constructor <;> simp [VEnv.contains, VEnv.empty,
    VEnv.ReflectsNatNat, VEnv.ReflectsNatNatNat, VEnv.ReflectsNatNatBool,
    VEnv.ReflectsNatBitwise]

theorem VEnv.HasPrimitives.addConst_of_not_primitive {env env' : VEnv}
    (h : env.HasPrimitives) (hadd : env.addConst n ci = some env')
    (hn : ¬Environment.primitives.contains n) : env'.HasPrimitives := by
  have fresh (p : Name) (hp : Environment.primitives.contains p) : n ≠ p := by
    rintro rfl
    exact hn hp
  have same (p : Name) (hp : Environment.primitives.contains p) :=
    VEnv.addConst_constants_of_ne hadd (fresh p hp)
  have oldContains {p : Name} (hp : Environment.primitives.contains p)
      (H : env'.contains p) : env.contains p := by
    let ⟨ci, hci⟩ := H
    exact ⟨ci, by rwa [same p hp] at hci⟩
  have newContains {p : Name} (H : env.contains p) : env'.contains p :=
    let ⟨_, hci⟩ := H; ⟨_, (VEnv.addConst_le hadd).constants hci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]) H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by
      rwa [same ``Bool (by simp [Environment.primitives,
        NameSet.contains, NameSet.ofList])] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]) H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by
      rwa [same ``Nat (by simp [Environment.primitives,
        NameSet.contains, NameSet.ofList])] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])] at H)
    natPred := h.natPred.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natAdd := h.natAdd.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natSub := h.natSub.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natMul := h.natMul.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natPow := h.natPow.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natGcd := h.natGcd.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natMod := h.natMod.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natDiv := h.natDiv.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natBEq := h.natBEq.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natBLE := h.natBLE.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natBitwise := h.natBitwise.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natLAnd := h.natLAnd.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natLOr := h.natLOr.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natXor := h.natXor.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natShiftLeft := h.natShiftLeft.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    natShiftRight := h.natShiftRight.addConst hadd (fresh _ (by simp [Environment.primitives, NameSet.contains, NameSet.ofList]))
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat
        (by rwa [same ``Char.ofNat (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd)⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList
        (by rwa [same ``String.ofList (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd),
        hnil.mono (VEnv.addConst_le hadd), hcons.mono (VEnv.addConst_le hadd)⟩ }

theorem VEnv.HasPrimitives.addDef_of_not_primitive {env env' : VEnv}
    (h : env.HasPrimitives) (hadd : env.addConst n ci = some env')
    (hn : ¬Environment.primitives.contains n) :
    (env'.addDefEq df).HasPrimitives :=
  (h.addConst_of_not_primitive hadd hn).addDefEq

/-- Adding `Bool` and both canonical constructors is atomic from the point of
view of `HasPrimitives`: the intermediate environment containing only `Bool`
does not itself satisfy the invariant. -/
theorem VEnv.HasPrimitives.addBoolInductive {env env₁ env₂ env₃ : VEnv}
    (h : env.HasPrimitives)
    (hbool : env.addConst ``Bool { uvars := 0, type := .sort (.succ .zero) } = some env₁)
    (hfalse : env₁.addConst ``Bool.false { uvars := 0, type := .bool } = some env₂)
    (htrue : env₂.addConst ``Bool.true { uvars := 0, type := .bool } = some env₃) :
    env₃.HasPrimitives := by
  have le₁ : env ≤ env₁ := VEnv.addConst_le hbool
  have le₂ : env₁ ≤ env₂ := VEnv.addConst_le hfalse
  have le₃ : env₂ ≤ env₃ := VEnv.addConst_le htrue
  have le : env ≤ env₃ := le₁.trans (le₂.trans le₃)
  have same (p : Name) (hb : ``Bool ≠ p) (hf : ``Bool.false ≠ p)
      (ht : ``Bool.true ≠ p) : env₃.constants p = env.constants p := by
    rw [VEnv.addConst_constants_of_ne htrue ht,
      VEnv.addConst_constants_of_ne hfalse hf,
      VEnv.addConst_constants_of_ne hbool hb]
  have oldContains {p : Name} (hb : ``Bool ≠ p) (hf : ``Bool.false ≠ p)
      (ht : ``Bool.true ≠ p) (H : env₃.contains p) : env.contains p := by
    let ⟨ci, hci⟩ := H
    exact ⟨ci, by rwa [same p hb hf ht] at hci⟩
  have newContains {p : Name} (H : env.contains p) : env₃.contains p :=
    let ⟨_, hci⟩ := H; ⟨_, le.constants hci⟩
  refine {
    bool := fun _ =>
      ⟨⟨_, le₃.constants (VEnv.addConst_self hfalse)⟩,
        ⟨_, VEnv.addConst_self htrue⟩⟩
    boolType := fun H => by
      rw [VEnv.addConst_constants_of_ne htrue (by decide),
        VEnv.addConst_constants_of_ne hfalse (by decide),
        VEnv.addConst_self hbool] at H
      exact Option.some.inj H.symm
    boolFalse := fun H => by
      rw [VEnv.addConst_constants_of_ne htrue (by decide),
        VEnv.addConst_self hfalse] at H
      exact Option.some.inj H.symm
    boolTrue := fun H => by
      rw [VEnv.addConst_self htrue] at H
      exact Option.some.inj H.symm
    nat := fun H =>
      let ⟨hz, hs⟩ := h.nat (oldContains (by decide) (by decide) (by decide) H)
      ⟨newContains hz, newContains hs⟩
    natType := fun H => h.natType (by
      rwa [same ``Nat (by decide) (by decide) (by decide)] at H)
    natZero := fun H => h.natZero (by
      rwa [same ``Nat.zero (by decide) (by decide) (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      rwa [same ``Nat.succ (by decide) (by decide) (by decide)] at H)
    natPred := h.natPred.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natAdd := h.natAdd.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natSub := h.natSub.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natMul := h.natMul.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natPow := h.natPow.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natGcd := h.natGcd.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natMod := h.natMod.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natDiv := h.natDiv.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natBEq := h.natBEq.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natBLE := h.natBLE.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natBitwise := h.natBitwise.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natLAnd := h.natLAnd.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natLOr := h.natLOr.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natXor := h.natXor.addConst hbool (by decide) |>.addConst hfalse (by decide)
      |>.addConst htrue (by decide)
    natShiftLeft := h.natShiftLeft.addConst hbool (by decide)
      |>.addConst hfalse (by decide) |>.addConst htrue (by decide)
    natShiftRight := h.natShiftRight.addConst hbool (by decide)
      |>.addConst hfalse (by decide) |>.addConst htrue (by decide)
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat (by
        rwa [same ``Char.ofNat (by decide) (by decide) (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList (by
        rwa [same ``String.ofList (by decide) (by decide) (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le, hnil.mono le, hcons.mono le⟩ }

/-- The analogous atomic extension lemma for the canonical `Nat` inductive. -/
theorem VEnv.HasPrimitives.addNatInductive {env env₁ env₂ env₃ : VEnv}
    (h : env.HasPrimitives)
    (hnat : env.addConst ``Nat { uvars := 0, type := .sort (.succ .zero) } = some env₁)
    (hzero : env₁.addConst ``Nat.zero { uvars := 0, type := .nat } = some env₂)
    (hsucc : env₂.addConst ``Nat.succ
      { uvars := 0, type := .forallE .nat .nat } = some env₃) :
    env₃.HasPrimitives := by
  have le₁ : env ≤ env₁ := VEnv.addConst_le hnat
  have le₂ : env₁ ≤ env₂ := VEnv.addConst_le hzero
  have le₃ : env₂ ≤ env₃ := VEnv.addConst_le hsucc
  have le : env ≤ env₃ := le₁.trans (le₂.trans le₃)
  have same (p : Name) (hn : ``Nat ≠ p) (hz : ``Nat.zero ≠ p)
      (hs : ``Nat.succ ≠ p) : env₃.constants p = env.constants p := by
    rw [VEnv.addConst_constants_of_ne hsucc hs,
      VEnv.addConst_constants_of_ne hzero hz,
      VEnv.addConst_constants_of_ne hnat hn]
  have oldContains {p : Name} (hn : ``Nat ≠ p) (hz : ``Nat.zero ≠ p)
      (hs : ``Nat.succ ≠ p) (H : env₃.contains p) : env.contains p := by
    let ⟨ci, hci⟩ := H
    exact ⟨ci, by rwa [same p hn hz hs] at hci⟩
  have newContains {p : Name} (H : env.contains p) : env₃.contains p :=
    let ⟨_, hci⟩ := H; ⟨_, le.constants hci⟩
  refine {
    bool := fun H =>
      let ⟨hf, ht⟩ := h.bool (oldContains (by decide) (by decide) (by decide) H)
      ⟨newContains hf, newContains ht⟩
    boolType := fun H => h.boolType (by
      rwa [same ``Bool (by decide) (by decide) (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by
      rwa [same ``Bool.false (by decide) (by decide) (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      rwa [same ``Bool.true (by decide) (by decide) (by decide)] at H)
    nat := fun _ =>
      ⟨⟨_, le₃.constants (VEnv.addConst_self hzero)⟩,
        ⟨_, VEnv.addConst_self hsucc⟩⟩
    natType := fun H => by
      rw [VEnv.addConst_constants_of_ne hsucc (by decide),
        VEnv.addConst_constants_of_ne hzero (by decide),
        VEnv.addConst_self hnat] at H
      exact Option.some.inj H.symm
    natZero := fun H => by
      rw [VEnv.addConst_constants_of_ne hsucc (by decide),
        VEnv.addConst_self hzero] at H
      exact Option.some.inj H.symm
    natSucc := fun H => by
      rw [VEnv.addConst_self hsucc] at H
      exact Option.some.inj H.symm
    natPred := h.natPred.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natAdd := h.natAdd.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natSub := h.natSub.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natMul := h.natMul.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natPow := h.natPow.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natGcd := h.natGcd.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natMod := h.natMod.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natDiv := h.natDiv.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natBEq := h.natBEq.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natBLE := h.natBLE.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natBitwise := h.natBitwise.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natLAnd := h.natLAnd.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natLOr := h.natLOr.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natXor := h.natXor.addConst hnat (by decide) |>.addConst hzero (by decide)
      |>.addConst hsucc (by decide)
    natShiftLeft := h.natShiftLeft.addConst hnat (by decide)
      |>.addConst hzero (by decide) |>.addConst hsucc (by decide)
    natShiftRight := h.natShiftRight.addConst hnat (by decide)
      |>.addConst hzero (by decide) |>.addConst hsucc (by decide)
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat (by
        rwa [same ``Char.ofNat (by decide) (by decide) (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList (by
        rwa [same ``String.ofList (by decide) (by decide) (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le, hnil.mono le, hcons.mono le⟩ }

/-- Common bookkeeping for adding a primitive definition whose name is not one
of the constructor/type fields stored syntactically in `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addPrimitiveDefEq {env env' : VEnv}
    (h : env.HasPrimitives) (hadd : env.addConst n ci = some env')
    (hneBool : n ≠ ``Bool) (hneFalse : n ≠ ``Bool.false)
    (hneTrue : n ≠ ``Bool.true) (hneNat : n ≠ ``Nat)
    (hneZero : n ≠ ``Nat.zero) (hneSucc : n ≠ ``Nat.succ)
    (hneChar : n ≠ ``Char.ofNat) (hneString : n ≠ ``String.ofList)
    (natPred : (env'.addDefEq df).ReflectsNatNat ``Nat.pred Nat.pred)
    (natAdd : (env'.addDefEq df).ReflectsNatNatNat ``Nat.add Nat.add)
    (natSub : (env'.addDefEq df).ReflectsNatNatNat ``Nat.sub Nat.sub)
    (natMul : (env'.addDefEq df).ReflectsNatNatNat ``Nat.mul Nat.mul)
    (natPow : (env'.addDefEq df).ReflectsNatNatNat ``Nat.pow Nat.pow)
    (natGcd : (env'.addDefEq df).ReflectsNatNatNat ``Nat.gcd Nat.gcd)
    (natMod : (env'.addDefEq df).ReflectsNatNatNat ``Nat.mod Nat.mod)
    (natDiv : (env'.addDefEq df).ReflectsNatNatNat ``Nat.div Nat.div)
    (natBEq : (env'.addDefEq df).ReflectsNatNatBool ``Nat.beq Nat.beq)
    (natBLE : (env'.addDefEq df).ReflectsNatNatBool ``Nat.ble Nat.ble)
    (natBitwise : (env'.addDefEq df).ReflectsNatBitwise ``Nat.bitwise)
    (natLAnd : (env'.addDefEq df).ReflectsNatNatNat ``Nat.land Nat.land)
    (natLOr : (env'.addDefEq df).ReflectsNatNatNat ``Nat.lor Nat.lor)
    (natXor : (env'.addDefEq df).ReflectsNatNatNat ``Nat.xor Nat.xor)
    (natShiftLeft : (env'.addDefEq df).ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft)
    (natShiftRight : (env'.addDefEq df).ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : n ≠ p) : env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_constants_of_ne hadd hne
  have oldContains {p : Name} (hne : n ≠ p)
      (H : env''.contains p) : env.contains p := by
    let ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p :=
    let ⟨_, hpci⟩ := H; ⟨_, le.constants hpci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains hneBool H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool hneBool] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false hneFalse] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true hneTrue] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains hneNat H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by rwa [same ``Nat hneNat] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero hneZero] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ hneSucc] at H)
    natPred := natPred
    natAdd := natAdd
    natSub := natSub
    natMul := natMul
    natPow := natPow
    natGcd := natGcd
    natMod := natMod
    natDiv := natDiv
    natBEq := natBEq
    natBLE := natBLE
    natBitwise := natBitwise
    natLAnd := natLAnd
    natLOr := natLOr
    natXor := natXor
    natShiftLeft := natShiftLeft
    natShiftRight := natShiftRight
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat (by rwa [same ``Char.ofNat hneChar] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList
        (by rwa [same ``String.ofList hneString] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le, hnil.mono le, hcons.mono le⟩ }

theorem VEnv.HasPrimitives.addNatPred {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.pred ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNat ``Nat.pred Nat.pred) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.pred ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_constants_of_ne hadd hne
  have oldContains {p : Name} (hne : ``Nat.pred ≠ p)
      (H : env''.contains p) : env.contains p := by
    let ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p :=
    let ⟨_, hpci⟩ := H; ⟨_, le.constants hpci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true (by decide)] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by rwa [same ``Nat (by decide)] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ (by decide)] at H)
    natPred := href
    natAdd := h.natAdd.addConst hadd (by decide) |>.addDefEq
    natSub := h.natSub.addConst hadd (by decide) |>.addDefEq
    natMul := h.natMul.addConst hadd (by decide) |>.addDefEq
    natPow := h.natPow.addConst hadd (by decide) |>.addDefEq
    natGcd := h.natGcd.addConst hadd (by decide) |>.addDefEq
    natMod := h.natMod.addConst hadd (by decide) |>.addDefEq
    natDiv := h.natDiv.addConst hadd (by decide) |>.addDefEq
    natBEq := h.natBEq.addConst hadd (by decide) |>.addDefEq
    natBLE := h.natBLE.addConst hadd (by decide) |>.addDefEq
    natBitwise := h.natBitwise.addConst hadd (by decide) |>.addDefEq
    natLAnd := h.natLAnd.addConst hadd (by decide) |>.addDefEq
    natLOr := h.natLOr.addConst hadd (by decide) |>.addDefEq
    natXor := h.natXor.addConst hadd (by decide) |>.addDefEq
    natShiftLeft := h.natShiftLeft.addConst hadd (by decide) |>.addDefEq
    natShiftRight := h.natShiftRight.addConst hadd (by decide) |>.addDefEq
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat
        (by rwa [same ``Char.ofNat (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList
        (by rwa [same ``String.ofList (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le, hnil.mono le, hcons.mono le⟩ }

theorem VEnv.HasPrimitives.addNatPredDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = ``Nat.pred)
    (hadd : env.addConst ``Nat.pred v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type (.forallE .nat .nat))
    (hz : env.IsDefEqU 0 [] (.app v.value .natZero) .natZero)
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .app v.value (.app .natSucc (.bvar 0)))
      (.lam .nat <| .bvar 0)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.pred []) (.forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.pred = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have href := VEnv.ReflectsNatNat.of_pred_equations hwf hzero hsucc hf hcf
    (hz.mono le) (hs.mono le)
  exact h.addNatPred hadd href

theorem VEnv.HasPrimitives.addNatAdd {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.add ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.add Nat.add) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.add ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_constants_of_ne hadd hne
  have oldContains {p : Name} (hne : ``Nat.add ≠ p)
      (H : env''.contains p) : env.contains p := by
    let ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p :=
    let ⟨_, hpci⟩ := H; ⟨_, le.constants hpci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true (by decide)] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by rwa [same ``Nat (by decide)] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ (by decide)] at H)
    natPred := h.natPred.addConst hadd (by decide) |>.addDefEq
    natAdd := href
    natSub := h.natSub.addConst hadd (by decide) |>.addDefEq
    natMul := h.natMul.addConst hadd (by decide) |>.addDefEq
    natPow := h.natPow.addConst hadd (by decide) |>.addDefEq
    natGcd := h.natGcd.addConst hadd (by decide) |>.addDefEq
    natMod := h.natMod.addConst hadd (by decide) |>.addDefEq
    natDiv := h.natDiv.addConst hadd (by decide) |>.addDefEq
    natBEq := h.natBEq.addConst hadd (by decide) |>.addDefEq
    natBLE := h.natBLE.addConst hadd (by decide) |>.addDefEq
    natBitwise := h.natBitwise.addConst hadd (by decide) |>.addDefEq
    natLAnd := h.natLAnd.addConst hadd (by decide) |>.addDefEq
    natLOr := h.natLOr.addConst hadd (by decide) |>.addDefEq
    natXor := h.natXor.addConst hadd (by decide) |>.addDefEq
    natShiftLeft := h.natShiftLeft.addConst hadd (by decide) |>.addDefEq
    natShiftRight := h.natShiftRight.addConst hadd (by decide) |>.addDefEq
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat
        (by rwa [same ``Char.ofNat (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList
        (by rwa [same ``String.ofList (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le, hnil.mono le, hcons.mono le⟩ }

theorem VEnv.HasPrimitives.addNatAddDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = ``Nat.add)
    (hadd : env.addConst ``Nat.add v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app .natSucc (.app (.app v.value (.bvar 1)) (.bvar 0)))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.add [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.add = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have href := VEnv.ReflectsNatNatNat.of_add_equations hwf hzero hsucc hf hcf
    (hz.mono le) (hs.mono le)
  exact h.addNatAdd hadd href

theorem VEnv.HasPrimitives.addNatSub {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.sub ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.sub Nat.sub) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.sub ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_constants_of_ne hadd hne
  have oldContains {p : Name} (hne : ``Nat.sub ≠ p)
      (H : env''.contains p) : env.contains p := by
    let ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p :=
    let ⟨_, hpci⟩ := H; ⟨_, le.constants hpci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true (by decide)] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by rwa [same ``Nat (by decide)] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ (by decide)] at H)
    natPred := h.natPred.addConst hadd (by decide) |>.addDefEq
    natAdd := h.natAdd.addConst hadd (by decide) |>.addDefEq
    natSub := href
    natMul := h.natMul.addConst hadd (by decide) |>.addDefEq
    natPow := h.natPow.addConst hadd (by decide) |>.addDefEq
    natGcd := h.natGcd.addConst hadd (by decide) |>.addDefEq
    natMod := h.natMod.addConst hadd (by decide) |>.addDefEq
    natDiv := h.natDiv.addConst hadd (by decide) |>.addDefEq
    natBEq := h.natBEq.addConst hadd (by decide) |>.addDefEq
    natBLE := h.natBLE.addConst hadd (by decide) |>.addDefEq
    natBitwise := h.natBitwise.addConst hadd (by decide) |>.addDefEq
    natLAnd := h.natLAnd.addConst hadd (by decide) |>.addDefEq
    natLOr := h.natLOr.addConst hadd (by decide) |>.addDefEq
    natXor := h.natXor.addConst hadd (by decide) |>.addDefEq
    natShiftLeft := h.natShiftLeft.addConst hadd (by decide) |>.addDefEq
    natShiftRight := h.natShiftRight.addConst hadd (by decide) |>.addDefEq
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat
        (by rwa [same ``Char.ofNat (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList
        (by rwa [same ``String.ofList (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono le, hnil.mono le, hcons.mono le⟩ }

theorem VEnv.HasPrimitives.addNatSubDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF) (hpredC : env.contains ``Nat.pred)
    (hname : v.name = ``Nat.sub)
    (hadd : env.addConst ``Nat.sub v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.const ``Nat.pred []) (.app (.app v.value (.bvar 1)) (.bvar 0)))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.sub [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.sub = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hnat : env.contains ``Nat := by
    have hfun := (h.natPred hpredC).1 0 []
    have ⟨_, H⟩ := hfun.isType henv trivial
    let ⟨⟨_, H⟩, _⟩ := H.forallE_inv henv
    let ⟨_, H, _⟩ := H.const_inv henv trivial
    exact ⟨_, H⟩
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hpred : env''.ReflectsNatNat ``Nat.pred Nat.pred :=
    (h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hpredC' : env''.contains ``Nat.pred :=
    let ⟨_, hp⟩ := hpredC; ⟨_, le.constants hp⟩
  have href := VEnv.ReflectsNatNatNat.of_sub_equations hwf hzero hsucc
    hpred hpredC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addNatSub hadd href

theorem VEnv.HasPrimitives.addNatMulDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF) (haddC : env.contains ``Nat.add)
    (hname : v.name = ``Nat.mul)
    (hadd : env.addConst ``Nat.mul v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.add [])
          (.app (.app v.value (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.mul [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.mul = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hnat := h.natAdd.nat_of_contains henv haddC
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hadd' : env''.ReflectsNatNatNat ``Nat.add Nat.add :=
    (h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have haddC' : env''.contains ``Nat.add :=
    let ⟨_, ha⟩ := haddC; ⟨_, le.constants ha⟩
  have href := VEnv.ReflectsNatNatNat.of_mul_equations hwf hzero hsucc
    hadd' haddC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatPowDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF) (hmulC : env.contains ``Nat.mul)
    (hname : v.name = ``Nat.pow)
    (hadd : env.addConst ``Nat.pow v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .app .natSucc .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.mul [])
          (.app (.app v.value (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.pow [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.pow = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hnat := h.natMul.nat_of_contains henv hmulC
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hmul' : env''.ReflectsNatNatNat ``Nat.mul Nat.mul :=
    (h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hmulC' : env''.contains ``Nat.mul :=
    let ⟨_, hm⟩ := hmulC; ⟨_, le.constants hm⟩
  have href := VEnv.ReflectsNatNatNat.of_pow_equations hwf hzero hsucc
    hmul' hmulC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatGcdDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF) (hmodC : env.contains ``Nat.mod)
    (hname : v.name = ``Nat.gcd)
    (hadd : env.addConst ``Nat.gcd v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value .natZero) (.bvar 0))
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.app .natSucc (.bvar 1))) (.bvar 0))
      (.lam .nat <| .lam .nat <|
        .app (.app v.value
          (.app (.app (.const ``Nat.mod []) (.bvar 0))
            (.app .natSucc (.bvar 1))))
          (.app .natSucc (.bvar 1)))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hnat := h.natMod.nat_of_contains henv hmodC
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.gcd = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hmod := (h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hmodC' : env''.contains ``Nat.mod :=
    let ⟨_, hm⟩ := hmodC; ⟨_, le.constants hm⟩
  have href := VEnv.ReflectsNatNatNat.of_gcd_equations hwf hzero hsucc
    hmod hmodC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatModDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.mod v.toVConstant = some env')
    (href : (env'.addDefEq v.toDefEq).ReflectsNatNatNat ``Nat.mod Nat.mod) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatDivDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.div v.toVConstant = some env')
    (href : (env'.addDefEq v.toDefEq).ReflectsNatNatNat ``Nat.div Nat.div) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatBEqDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (hname : v.name = ``Nat.beq)
    (hadd : env.addConst ``Nat.beq v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .bool))
    (h00 : env.IsDefEqU 0 []
      (.app (.app v.value .natZero) .natZero) .boolTrue)
    (h0s : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value .natZero) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .boolFalse))
    (hs0 : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.app .natSucc (.bvar 0))) .natZero)
      (.lam .nat <| .boolFalse))
    (hss : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <| .app (.app v.value (.bvar 1)) (.bvar 0))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.beq [])
      (.forallE .nat <| .forallE .nat .bool) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.beq = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hboolLit (b) (Γ) : env''.HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit h hbool b (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have href := VEnv.ReflectsNatNatBool.of_rec_equations hwf hzero hsucc hboolLit
    hf hcf (h00.mono le) (h0s.mono le) (hs0.mono le) (hss.mono le)
    (g := Nat.beq) (r00 := true) (r0s := false) (rs0 := false)
    (by rfl) (by intro b; rfl) (by intro a; rfl) (by intro a b; rfl)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatBLEDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (hname : v.name = ``Nat.ble)
    (hadd : env.addConst ``Nat.ble v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .bool))
    (h00 : env.IsDefEqU 0 []
      (.app (.app v.value .natZero) .natZero) .boolTrue)
    (h0s : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value .natZero) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .boolTrue))
    (hs0 : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.app .natSucc (.bvar 0))) .natZero)
      (.lam .nat <| .boolFalse))
    (hss : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <| .app (.app v.value (.bvar 1)) (.bvar 0))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.ble [])
      (.forallE .nat <| .forallE .nat .bool) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.ble = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hboolLit (b) (Γ) : env''.HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit h hbool b (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have href := VEnv.ReflectsNatNatBool.of_rec_equations hwf hzero hsucc hboolLit
    hf hcf (h00.mono le) (h0s.mono le) (hs0.mono le) (hss.mono le)
    (g := Nat.ble) (r00 := true) (r0s := true) (rs0 := false)
    (by rfl) (by intro b; rfl) (by intro a; rfl) (by intro a b; rfl)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatShiftLeftDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF) (hmulC : env.contains ``Nat.mul)
    (hname : v.name = ``Nat.shiftLeft)
    (hadd : env.addConst ``Nat.shiftLeft v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 0)) (.app .natSucc (.bvar 1)))
      (.lam .nat <| .lam .nat <|
        .app (.app v.value
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0))) (.bvar 1))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.shiftLeft [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.shiftLeft = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hnat := h.natMul.nat_of_contains henv hmulC
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hmul' : env''.ReflectsNatNatNat ``Nat.mul Nat.mul :=
    (h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hmulC' : env''.contains ``Nat.mul :=
    let ⟨_, hm⟩ := hmulC; ⟨_, le.constants hm⟩
  have href := VEnv.ReflectsNatNatNat.of_shiftLeft_equations hwf hzero hsucc
    hmul' hmulC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatShiftRightDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF) (hdivC : env.contains ``Nat.div)
    (hname : v.name = ``Nat.shiftRight)
    (hadd : env.addConst ``Nat.shiftRight v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 0)) (.app .natSucc (.bvar 1)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.div [])
          (.app (.app v.value (.bvar 0)) (.bvar 1))) (.natLit 2))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.shiftRight [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.shiftRight = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hnat := h.natDiv.nat_of_contains henv hdivC
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hdiv' : env''.ReflectsNatNatNat ``Nat.div Nat.div :=
    (h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hdivC' : env''.contains ``Nat.div :=
    let ⟨_, hd⟩ := hdivC; ⟨_, le.constants hd⟩
  have href := VEnv.ReflectsNatNatNat.of_shiftRight_equations hwf hzero hsucc
    hdiv' hdivC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href

theorem VEnv.HasPrimitives.addNatBitwiseDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.bitwise v.toVConstant = some env')
    (href : (env'.addDefEq v.toDefEq).ReflectsNatBitwise ``Nat.bitwise) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatXorDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives)
    (hnat : env.contains ``Nat) (hbitwiseC : env.contains ``Nat.bitwise)
    (hname : v.name = ``Nat.xor)
    (hadd : env.addConst ``Nat.xor v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hopTy : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hff : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolFalse) .boolFalse)
    (htf : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolFalse) .boolTrue)
    (hft : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolTrue) .boolTrue)
    (htt : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolTrue) .boolFalse) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.xor [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.xor = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname, hvalue] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hbitwise' := (h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hbitwiseC' : env''.contains ``Nat.bitwise :=
    let ⟨_, hb⟩ := hbitwiseC; ⟨_, le.constants hb⟩
  have hop : env.ReflectsBoolBin op bne :=
    VEnv.ReflectsBoolBin.of_table hopTy hff hft htf htt
  have href := VEnv.ReflectsNatNatNat.of_bitwise_specialization hwf hzero hsucc
    hbitwise' hbitwiseC' hf hcf (hop.mono le) (g := Nat.xor) rfl
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) hbitwise'
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatLandDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (hbitwiseC : env.contains ``Nat.bitwise)
    (hname : v.name = ``Nat.land)
    (hadd : env.addConst ``Nat.land v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hopTy : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool .boolFalse))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool <| .bvar 0)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hfun (U Γ) : env''.HasType U Γ (.const ``Nat.land [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.land = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname, hvalue] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hboolT (b) (Γ) : env.HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit h hbool b (Us := []) (Δ := [])).2.weak0 henv
  have hop := VEnv.ReflectsBoolBin.of_and_equations henv hboolT hopTy hf ht
  have hbitwise' := (h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hbitwiseC' : env''.contains ``Nat.bitwise :=
    let ⟨_, hb⟩ := hbitwiseC; ⟨_, le.constants hb⟩
  have href := VEnv.ReflectsNatNatNat.of_bitwise_specialization hwf hzero hsucc
    hbitwise' hbitwiseC' hfun hcf (hop.mono le) (g := Nat.land) rfl
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) hbitwise' href
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addNatLorDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (hbitwiseC : env.contains ``Nat.bitwise)
    (hname : v.name = ``Nat.lor)
    (hadd : env.addConst ``Nat.lor v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hopTy : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool <| .bvar 0))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool .boolTrue)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hfun (U Γ) : env''.HasType U Γ (.const ``Nat.lor [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.lor = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname, hvalue] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hboolT (b) (Γ) : env.HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit h hbool b (Us := []) (Δ := [])).2.weak0 henv
  have hop := VEnv.ReflectsBoolBin.of_or_equations henv hboolT hopTy hf ht
  have hbitwise' := (h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hbitwiseC' : env''.contains ``Nat.bitwise :=
    let ⟨_, hb⟩ := hbitwiseC; ⟨_, le.constants hb⟩
  have href := VEnv.ReflectsNatNatNat.of_bitwise_specialization hwf hzero hsucc
    hbitwise' hbitwiseC' hfun hcf (hop.mono le) (g := Nat.lor) rfl
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) hbitwise'
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

theorem VEnv.HasPrimitives.addCharOfNat {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Char.ofNat ci = some env') (hwf : env'.WF)
    (hu : ci.uvars = 0)
    (hty : env.IsDefEqU 0 [] ci.type (.forallE .nat .char)) :
    env'.HasPrimitives := by
  have same (p : Name) (hne : ``Char.ofNat ≠ p) :=
    VEnv.addConst_constants_of_ne hadd hne
  have oldContains {p : Name} (hne : ``Char.ofNat ≠ p)
      (H : env'.contains p) : env.contains p := by
    let ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env'.contains p :=
    let ⟨_, hpci⟩ := H; ⟨_, (VEnv.addConst_le hadd).constants hpci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true (by decide)] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by rwa [same ``Nat (by decide)] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ (by decide)] at H)
    natPred := h.natPred.addConst hadd (by decide)
    natAdd := h.natAdd.addConst hadd (by decide)
    natSub := h.natSub.addConst hadd (by decide)
    natMul := h.natMul.addConst hadd (by decide)
    natPow := h.natPow.addConst hadd (by decide)
    natGcd := h.natGcd.addConst hadd (by decide)
    natMod := h.natMod.addConst hadd (by decide)
    natDiv := h.natDiv.addConst hadd (by decide)
    natBEq := h.natBEq.addConst hadd (by decide)
    natBLE := h.natBLE.addConst hadd (by decide)
    natBitwise := h.natBitwise.addConst hadd (by decide)
    natLAnd := h.natLAnd.addConst hadd (by decide)
    natLOr := h.natLOr.addConst hadd (by decide)
    natXor := h.natXor.addConst hadd (by decide)
    natShiftLeft := h.natShiftLeft.addConst hadd (by decide)
    natShiftRight := h.natShiftRight.addConst hadd (by decide)
    charOfNat := fun H => by
      rw [VEnv.addConst_self hadd] at H
      cases H
      exact ⟨hu, VEnv.HasType.const_of_type_defeq hwf (VEnv.addConst_self hadd) hu
        (hty.mono (VEnv.addConst_le hadd))⟩
    stringOfList := fun H =>
      let ⟨hu, hty, hnil, hcons⟩ := h.stringOfList
        (by rwa [same ``String.ofList (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd),
        hnil.mono (VEnv.addConst_le hadd), hcons.mono (VEnv.addConst_le hadd)⟩ }

theorem VEnv.HasPrimitives.addStringOfList {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``String.ofList ci = some env') (hwf : env'.WF)
    (hu : ci.uvars = 0)
    (hty : env.IsDefEqU 0 [] ci.type (.forallE .listChar .string))
    (hnil : env.HasType 0 [] .listCharNil .listChar)
    (hcons : env.HasType 0 [] .listCharCons
      (.forallE .char <| .forallE .listChar .listChar)) :
    env'.HasPrimitives := by
  have same (p : Name) (hne : ``String.ofList ≠ p) :=
    VEnv.addConst_constants_of_ne hadd hne
  have oldContains {p : Name} (hne : ``String.ofList ≠ p)
      (H : env'.contains p) : env.contains p := by
    let ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env'.contains p :=
    let ⟨_, hpci⟩ := H; ⟨_, (VEnv.addConst_le hadd).constants hpci⟩
  refine {
    bool := fun H =>
      let ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by rwa [same ``Bool.true (by decide)] at H)
    nat := fun H =>
      let ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      ⟨newContains hzero, newContains hsucc⟩
    natType := fun H => h.natType (by rwa [same ``Nat (by decide)] at H)
    natZero := fun H => h.natZero (by rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by rwa [same ``Nat.succ (by decide)] at H)
    natPred := h.natPred.addConst hadd (by decide)
    natAdd := h.natAdd.addConst hadd (by decide)
    natSub := h.natSub.addConst hadd (by decide)
    natMul := h.natMul.addConst hadd (by decide)
    natPow := h.natPow.addConst hadd (by decide)
    natGcd := h.natGcd.addConst hadd (by decide)
    natMod := h.natMod.addConst hadd (by decide)
    natDiv := h.natDiv.addConst hadd (by decide)
    natBEq := h.natBEq.addConst hadd (by decide)
    natBLE := h.natBLE.addConst hadd (by decide)
    natBitwise := h.natBitwise.addConst hadd (by decide)
    natLAnd := h.natLAnd.addConst hadd (by decide)
    natLOr := h.natLOr.addConst hadd (by decide)
    natXor := h.natXor.addConst hadd (by decide)
    natShiftLeft := h.natShiftLeft.addConst hadd (by decide)
    natShiftRight := h.natShiftRight.addConst hadd (by decide)
    charOfNat := fun H =>
      let ⟨hu, hty⟩ := h.charOfNat
        (by rwa [same ``Char.ofNat (by decide)] at H)
      ⟨hu, fun U Γ => (hty U Γ).mono (VEnv.addConst_le hadd)⟩
    stringOfList := fun H => by
      rw [VEnv.addConst_self hadd] at H
      cases H
      exact ⟨hu,
        VEnv.HasType.const_of_type_defeq hwf (VEnv.addConst_self hadd) hu
          (hty.mono (VEnv.addConst_le hadd)),
        hnil.mono (VEnv.addConst_le hadd), hcons.mono (VEnv.addConst_le hadd)⟩ }

namespace Environment

theorem withLambda.WF {c : VContext} {s : VState}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' body' : VExpr}
    {fail : ∀ {α}, M α} {k : Expr → Expr → M α} {Q}
    (he : c.TrExprS (.lam name dom body bi) (.lam dom' body'))
    (H : ∀ id cwf' s', s ≤ s' → ¬s.ngen.Reserves id →
      let c' := c.withMLC (.vlam id name dom dom' bi c.mlctx) (wf := cwf')
      c'.TrExprS (body.instantiate1 (.fvar id)) body' →
      M.WF c' s' (k (.fvar id) (body.instantiate1 (.fvar id))) Q) :
    M.WF c s (withLambda (.lam name dom body bi) fail k) Q := by
  let .lam hdomTy hdom hbody := he
  simp only [withLambda]
  have hw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl name bi dom fun fv => k fv (body.instantiate1 fv)) Q := by
    refine .withLocalDecl hdom hdomTy .rfl fun id cwf' s' hs' hres => ?_
    have hbody' := hbody.inst_fvar c.Ewf.ordered cwf'.1.tr.wf
    rw [← Expr.instantiate1_eq] at hbody'
    exact H id cwf' s' hs' hres hbody'
  simpa using hw

theorem withForall.WF {c : VContext} {s : VState}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' body' : VExpr}
    {fail : ∀ {α}, M α} {k : Expr → Expr → M α} {Q}
    (he : c.TrExprS (.forallE name dom body bi) (.forallE dom' body'))
    (H : ∀ id cwf' s', s ≤ s' → ¬s.ngen.Reserves id →
      let c' := c.withMLC (.vlam id name dom dom' bi c.mlctx) (wf := cwf')
      c'.TrExprS (body.instantiate1 (.fvar id)) body' →
      M.WF c' s' (k (.fvar id) (body.instantiate1 (.fvar id))) Q) :
    M.WF c s (withForall (.forallE name dom body bi) fail k) Q := by
  let .forallE hdomTy _ hdom hbody := he
  simp only [withForall]
  have hw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl name bi dom fun fv => k fv (body.instantiate1 fv)) Q := by
    refine .withLocalDecl hdom hdomTy .rfl fun id cwf' s' hs' hres => ?_
    have hbody' := hbody.inst_fvar c.Ewf.ordered cwf'.1.tr.wf
    rw [← Expr.instantiate1_eq] at hbody'
    exact H id cwf' s' hs' hres hbody'
  simpa using hw

/-- The explicit unfold/WHNF sequence used for a compiled well-founded
definition preserves the meaning of a one-binder equation left-hand side. -/
theorem reduceNatWellFoundedLam1.WF {c : VContext} {s : VState}
    {name : Name} {ty body : Expr} {bi : BinderInfo} {ty' body' : VExpr}
    {fail : ∀ {α}, M α}
    (he : c.TrExprS (.lam name ty body bi) (.lam ty' body')) :
    M.WF c s (reduceNatWellFoundedLam1 (.lam name ty body bi) fail)
      fun out _ => c.TrExpr out (.lam ty' body') := by
  simp only [reduceNatWellFoundedLam1]
  refine withLambda.WF he ?_
  intro id cwf' s' hs' hres c' hbody
  refine (whnfCore.WF hbody).bind fun _ _ _ h₁ => ?_
  refine (unfoldDefinition.WF' h₁).bind fun _ _ _ h₂ => ?_
  refine (whnfCore.WF' h₂).bind fun _ _ _ h₃ => ?_
  refine (unfoldDefinition.WF' h₃).bind fun _ _ _ h₄ => ?_
  refine (whnfCore.WF' h₄).bind fun out _ _ hout => ?_
  refine getLCtx.WF.bind fun lctx _ _ hctx => ?_
  obtain ⟨rfl, rfl⟩ := hctx
  let ⟨_, _, heq⟩ := hout
  let ⟨_, heq'⟩ := heq
  have hlen : 1 ≤ c'.mlctx.length := by simp [c', VContext.withMLC]
  have hclosed := cwf'.1.mkLambda_tr c.Ewf hout heq'.hasType.2 1 hlen
  have hlctx : c'.lctx'.mkLambda #[.fvar id] out =
      c'.mlctx.mkLambda 1 hlen out := by
    apply cwf'.1.mkLambda_eq
    simp
  rw [hlctx]
  exact .pure (by simpa [c', VContext.withMLC] using hclosed.1)

theorem reduceNatWellFoundedLam2.WF {c : VContext} {s : VState}
    {name₁ name₂ : Name} {ty₁ ty₂ body : Expr}
    {bi₁ bi₂ : BinderInfo} {ty₁' ty₂' body' : VExpr}
    {fail : ∀ {α}, M α}
    (he : c.TrExprS (.lam name₁ ty₁ (.lam name₂ ty₂ body bi₂) bi₁)
      (.lam ty₁' <| .lam ty₂' body')) :
    M.WF c s
      (reduceNatWellFoundedLam2
        (.lam name₁ ty₁ (.lam name₂ ty₂ body bi₂) bi₁) fail)
      fun out _ => c.TrExpr out (.lam ty₁' <| .lam ty₂' body') := by
  simp only [reduceNatWellFoundedLam2]
  refine withLambda.WF he ?_
  intro id cwf' s' hs' hres c' hbody
  simp at hbody ⊢
  refine (reduceNatWellFoundedLam1.WF hbody).bind fun out _ _ hout => ?_
  rw [map_eq_pure_bind]
  refine getLCtx.WF.bind fun lctx _ _ hctx => ?_
  obtain ⟨rfl, rfl⟩ := hctx
  let ⟨_, _, heq⟩ := hout
  let ⟨_, heq'⟩ := heq
  have hlen : 1 ≤ c'.mlctx.length := by simp [c', VContext.withMLC]
  have hclosed := cwf'.1.mkLambda_tr c.Ewf hout heq'.hasType.2 1 hlen
  have hlctx : c'.lctx'.mkLambda #[.fvar id] out =
      c'.mlctx.mkLambda 1 hlen out := by
    apply cwf'.1.mkLambda_eq
    simp
  rw [hlctx]
  exact .pure (by simpa [c', VContext.withMLC] using hclosed.1)

theorem checkNatBitwiseZero.WF {c : VContext} {s : VState}
    {bitwise : Expr} {fail : ∀ {α}, M α}
    (hlhs : c.TrExprS (natBitwiseZeroEquation bitwise).1 lhs')
    (hrhs : c.TrExprS (natBitwiseZeroEquation bitwise).2 rhs')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (checkNatBitwiseZero bitwise fail) fun _ _ =>
      c.IsDefEqU lhs' rhs' := by
  simp only [checkNatBitwiseZero]
  obtain ⟨A, B, e, rfl⟩ : ∃ A B e, lhs' = .lam A (.lam B e) := by
    cases hlhs with
    | lam _ _ hbody =>
      cases hbody
      exact ⟨_, _, _, rfl⟩
  refine (reduceNatWellFoundedLam2.WF hlhs).bind fun _ _ _ hred => ?_
  let ⟨_, hredS, hredEq⟩ := hred
  exact (isDefEq.WF hredS hrhs).bind fun b _ _ heq => by
    split
    · exact .pure (hredEq.symm.trans c.Ewf c.Δwf (heq (by assumption)))
    · exact hfail.mono fun _ _ _ h => h.elim

private theorem closedExpr_fvarsIn {c : VContext} {e : Expr}
    (hf : e.hasFVar = false) (hm : e.hasMVar = false) :
    e.FVarsIn (· ∈ c.vlctx.fvars) := by
  apply fvarsIn_iff.mpr
  refine ⟨?_, fvarsIn_iff_hasMVar.mpr hm⟩
  intro fv hfv
  rw [fvarsList_eq_nil.mpr hf] at hfv
  simp at hfv

/-- Proof-relevant alpha-equivalence corresponding to `exprShapeEq`.  Binder
names and annotations (and metadata payloads) are intentionally irrelevant,
matching the information discarded by `TrExprS`. -/
inductive ExprShapeEq : Expr → Expr → Prop
  | bvar : ExprShapeEq (.bvar i) (.bvar i)
  | fvar : ExprShapeEq (.fvar i) (.fvar i)
  | mvar : ExprShapeEq (.mvar i) (.mvar i)
  | sort : ExprShapeEq (.sort u) (.sort u)
  | const : ExprShapeEq (.const n us) (.const n us)
  | app : ExprShapeEq f f' → ExprShapeEq a a' →
      ExprShapeEq (.app f a) (.app f' a')
  | lam : ExprShapeEq ty ty' → ExprShapeEq body body' →
      ExprShapeEq (.lam n ty body bi) (.lam n' ty' body' bi')
  | forallE : ExprShapeEq ty ty' → ExprShapeEq body body' →
      ExprShapeEq (.forallE n ty body bi) (.forallE n' ty' body' bi')
  | letE : ExprShapeEq ty ty' → ExprShapeEq val val' →
      ExprShapeEq body body' →
      ExprShapeEq (.letE n ty val body nondep)
        (.letE n' ty' val' body' nondep')
  | lit : ExprShapeEq (.lit l) (.lit l)
  | mdata : ExprShapeEq e e' → ExprShapeEq (.mdata d e) (.mdata d' e')
  | proj : ExprShapeEq e e' → ExprShapeEq (.proj s i e) (.proj s i e')

theorem exprShapeEq_sound (h : exprShapeEq e e' = true) : ExprShapeEq e e' := by
  induction e generalizing e' with
  | bvar i =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .bvar
  | fvar i =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .fvar
  | mvar i =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .mvar
  | sort u =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .sort
  | const n us =>
    cases e' <;> simp [exprShapeEq] at h
    rcases h with ⟨rfl, rfl⟩; exact .const
  | app f a ihf iha =>
    cases e' <;> simp [exprShapeEq] at h
    exact .app (ihf h.1) (iha h.2)
  | lam n ty body bi ihty ihbody =>
    cases e' <;> simp [exprShapeEq] at h
    exact .lam (ihty h.1) (ihbody h.2)
  | forallE n ty body bi ihty ihbody =>
    cases e' <;> simp [exprShapeEq] at h
    exact .forallE (ihty h.1) (ihbody h.2)
  | letE n ty val body nondep ihty ihval ihbody =>
    cases e' <;> simp [exprShapeEq] at h
    exact .letE (ihty h.1.1) (ihval h.1.2) (ihbody h.2)
  | lit l =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .lit
  | mdata d e ih =>
    cases e' <;> simp [exprShapeEq] at h
    exact .mdata (ih h)
  | proj s i e ih =>
    cases e' <;> simp [exprShapeEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, he⟩
    exact .proj (ih he)

theorem ExprShapeEq.eq_const (h : ExprShapeEq e (.const n us)) :
    e = .const n us := by
  cases e <;> cases h
  rfl

theorem TrExprS.of_exprShapeEq {env : VEnv} {Us Δ e e' v}
    (hs : ExprShapeEq e e') (h : TrExprS env Us Δ e v) :
    TrExprS env Us Δ e' v := by
  induction hs generalizing Δ v with
  | bvar | fvar | mvar | sort | const | lit => exact h
  | app _ _ ihf iha =>
    cases h with
    | app hft hat hf ha => exact .app hft hat (ihf hf) (iha ha)
  | lam _ _ ihty ihbody =>
    cases h with
    | lam hty htrTy hbody => exact .lam hty (ihty htrTy) (ihbody hbody)
  | forallE _ _ ihty ihbody =>
    cases h with
    | forallE hty hbodyTy htrTy hbody =>
      exact .forallE hty hbodyTy (ihty htrTy) (ihbody hbody)
  | letE _ _ _ ihty ihval ihbody =>
    cases h with
    | letE hvalTy htrTy htrVal hbody =>
      exact .letE hvalTy (ihty htrTy) (ihval htrVal) (ihbody hbody)
  | mdata _ ih =>
    cases h with
    | mdata he => exact .mdata (ih he)
  | proj _ ih =>
    cases h with
    | proj he hp => exact .proj (ih he) hp

theorem checkNatWellFoundedEquation.WF {c : VContext} {s : VState}
    {lhs rhs : Expr} :
    M.WF c s (checkNatWellFoundedEquation lhs rhs) fun _ _ =>
      ∃ lhs' rhs', c.TrExprS lhs lhs' ∧ c.TrExprS rhs rhs' ∧
        c.IsDefEqU lhs' rhs' := by
  simp only [checkNatWellFoundedEquation]
  split
  · rename_i hclosed
    simp only [Bool.and_eq_true] at hclosed
    simp only [pure_bind]
    have hlhs := closedExpr_fvarsIn (c := c)
      (by simpa using hclosed.1.1.1) (by simpa using hclosed.1.1.2)
    have hrhs := closedExpr_fvarsIn (c := c)
      (by simpa using hclosed.1.2) (by simpa using hclosed.2)
    refine (checkType.WF hlhs).bind fun _ _ _ hl => ?_
    let ⟨lhs', _, _, hlhs', _, _⟩ := hl
    refine (checkType.WF hrhs).bind fun _ _ _ hr => ?_
    let ⟨rhs', _, _, hrhs', _, _⟩ := hr
    refine (isDefEq.WF hlhs' hrhs').bind fun b _ _ heq => ?_
    split
    · exact .pure ⟨lhs', rhs', hlhs', hrhs', heq (by assumption)⟩
    · exact .throw
  · exact .throw

def NatWellFoundedCoreResult.Valid (c : VContext)
    (r : NatWellFoundedCoreResult) : Prop :=
      r.auxShape = true ∧
      (∃ lhs' rhs', c.TrExprS r.callLhs lhs' ∧ c.TrExprS r.callRhs rhs' ∧
        c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.entryLhs lhs' ∧ c.TrExprS r.entryRhs rhs' ∧
        c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.topLhs lhs' ∧ c.TrExprS r.topRhs rhs' ∧
        c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.eagerLhs lhs' ∧ c.TrExprS r.eagerRhs rhs' ∧
        c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.boolTrueLhs lhs' ∧
        c.TrExprS r.boolTrueRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.boolFalseLhs lhs' ∧
        c.TrExprS r.boolFalseRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.stepLhs lhs' ∧ c.TrExprS r.stepRhs rhs' ∧
        c.IsDefEqU lhs' rhs') ∧
      (∃ lhs' rhs', c.TrExprS r.specStepLhs lhs' ∧
        c.TrExprS r.specStepRhs rhs' ∧
        c.IsDefEqU lhs' rhs')

def NatWellFoundedCoreResult.AuxValid (c : VContext)
    (r : NatWellFoundedCoreResult) : Prop :=
    (∃ lhs' rhs', c.TrExprS r.expectedEagerLhs lhs' ∧
      c.TrExprS r.expectedEagerRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedBoolTrueLhs lhs' ∧
      c.TrExprS r.expectedBoolTrueRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedBoolFalseLhs lhs' ∧
      c.TrExprS r.expectedBoolFalseRhs rhs' ∧ c.IsDefEqU lhs' rhs')

theorem NatWellFoundedCoreResult.Valid.normalizeAux {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) : r.AuxValid c := by
  rcases hv with ⟨hs, _, _, _, heager, htrue, hfalse, _, _⟩
  rcases heager with ⟨el, er, hel, her, heeq⟩
  rcases htrue with ⟨tl, tr, htl, htr, hteq⟩
  rcases hfalse with ⟨fl, fr, hfl, hfr, hfeq⟩
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  rcases hs with
    ⟨⟨⟨⟨⟨⟨⟨hels, hers⟩, htls⟩, htrs⟩, hfls⟩, hfrs⟩, _⟩, _⟩
  refine ⟨⟨el, er, ?_, ?_, heeq⟩, ⟨tl, tr, ?_, ?_, hteq⟩,
    ⟨fl, fr, ?_, ?_, hfeq⟩⟩
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hels) hel
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hers) her
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound htls) htl
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound htrs) htr
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hfls) hfl
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hfrs) hfr

/-- The eager implementation extracted from the compiled fixpoint is the
canonical `WellFounded.Nat.eager` constant. -/
theorem NatWellFoundedCoreResult.Valid.eagerFn_eq {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) :
    r.eagerFn = q(WellFounded.Nat.eager) := by
  have hs := hv.1
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  exact (exprShapeEq_sound hs.1.2).eq_const

theorem NatWellFoundedCoreResult.Valid.goFn_closed {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) :
    r.goFn.hasLooseBVars = false := by
  have hs := hv.1
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  cases h : r.goFn.hasLooseBVars <;> simp_all

/-- Instantiate the certified eager-fuel equation at a concrete numeral.
The translated eager implementation itself is instantiated too: the
certificate only places it beneath the equation's outer lambda. -/
theorem VEnv.instantiate_eager_natLit_equation {env : VEnv}
    {r : NatWellFoundedCoreResult} {l rr : VExpr}
    (henv : env.WF)
    (hl : TrExprS env [] [] r.expectedEagerLhs l)
    (hr : TrExprS env [] [] r.expectedEagerRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hnatS : TrExprS env [] [] (.natLitToConstructor n) (.natLit n))
    (hnatT : ∀ n Γ, env.HasType 0 Γ (.natLit n) .nat) :
    ∃ eager ite cond A B,
      TrExprS env [] [] (r.eagerFn.instantiate1' (.natLitToConstructor n)) eager ∧
      TrExprS env [] [] Condition.bool.boolNatITE ite ∧
      TrExprS env [] []
        (mkApp2 (.const ``Nat.beq []) (.natLitToConstructor n)
          (.natLitToConstructor n)) cond ∧
      env.HasType 0 [] ite (.forallE A B) ∧
      env.HasType 0 [] cond A ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n))
        (.app (.app (.app ite cond) (.natLit n)) (.natLit n)) := by
  unfold NatWellFoundedCoreResult.expectedEagerLhs at hl
  unfold NatWellFoundedCoreResult.expectedEagerRhs at hr
  cases hl with
  | lam hnatTy hnat hbodyL =>
    cases hr with
    | lam _ hnat' hbodyR =>
      cases hnat
      case const =>
       rename_i ci us hc hus hlen
       simp at hus
       subst us
       have hu : ci.uvars = 0 := hlen.symm
       cases hnat'
       case const =>
        rename_i ci' us' hc' hus' hlen' htype
        simp at hus'
        subst us'
        have hu' : ci'.uvars = 0 := hlen'.symm
        cases hbodyL with
      | app heagerT hbvarT heager hbvar =>
        cases hbvar with
        | bvar hb =>
          simp [VLCtx.find?, VLCtx.next] at hb
          rcases hb with ⟨rfl, rfl⟩
          cases hbodyR with
          | app hR2T hbvar2T hR2 hbvar2 =>
            cases hbvar2 with
            | bvar hb2 =>
              simp [VLCtx.find?, VLCtx.next] at hb2
              rcases hb2 with ⟨rfl, rfl⟩
              cases hR2 with
              | app _ _ hR1 hbvar1 =>
                cases hbvar1 with
                | bvar hb1 =>
                  simp [VLCtx.find?, VLCtx.next] at hb1
                  rcases hb1 with ⟨rfl, rfl⟩
                  cases hR1 with
                  | app hiteT hcondT hite hcond =>
                    rename_i eagerV eagerA eagerB outerA outerB midA midB
                      midArgT iteV iteA iteB condV innerAppT
                    have ⟨_, hnatSort⟩ := (hnatT 0 []).isType henv trivial
                    have hbodyLT := VEnv.HasType.app heagerT hbvarT
                    have hbodyRT := VEnv.HasType.app hR2T hbvar2T
                    have happ := heq.app_same henv trivial
                      (.lam hnatSort hbodyLT) (hnatT n [])
                    have hbetaL : env.IsDefEqU 0 []
                        (.app (.lam .nat (.app eagerV (.bvar 0))) (.natLit n))
                        ((VExpr.app eagerV (.bvar 0)).inst (.natLit n)) :=
                      ⟨_, .beta hbodyLT (hnatT n [])⟩
                    have hbetaR : env.IsDefEqU 0 []
                        (.app (.lam .nat
                          (.app (.app (.app iteV condV) (.bvar 0)) (.bvar 0)))
                          (.natLit n))
                        ((VExpr.app (.app (.app iteV condV) (.bvar 0))
                          (.bvar 0)).inst (.natLit n)) :=
                      ⟨_, .beta hbodyRT (hnatT n [])⟩
                    have hi := hbetaL.symm.trans henv trivial happ
                      |>.trans henv trivial hbetaR
                    have heager' := TrExprS.inst (Us := []) (Δ := [])
                      (A₀ := .nat) (e₀' := .natLit n) henv.ordered
                      (hnatT n []) heager hnatS
                    have hite' := TrExprS.inst (Us := []) (Δ := [])
                      (A₀ := .nat) (e₀' := .natLit n) henv.ordered
                      (hnatT n []) hite hnatS
                    have hcond' := TrExprS.inst (Us := []) (Δ := [])
                      (A₀ := .nat) (e₀' := .natLit n) henv.ordered
                      (hnatT n []) hcond hnatS
                    have hiteT' := hiteT.instN henv.ordered .zero (hnatT n [])
                    have hcondT' := hcondT.instN henv.ordered .zero (hnatT n [])
                    refine ⟨eagerV.inst (.natLit n), iteV.inst (.natLit n),
                      condV.inst (.natLit n), iteA.inst (.natLit n),
                      iteB.inst (.natLit n) 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · exact heager'
                    · simpa [Condition.boolNatITE, Condition.bool,
                        Expr.instantiate1', Expr.looseBVarRange'] using hite'
                    · simpa [mkApp2, mkApp, Expr.instantiate1',
                        Expr.looseBVarRange'] using hcond'
                    · simpa [VExpr.inst] using hiteT'
                    · simpa [VExpr.inst] using hcondT'
                    · simpa [VExpr.inst, VExpr.inst_lift] using hi

/-- Normalize the checked `Bool.true` selector equation to the particular
translation of `boolNatITE` used by the eager-fuel equation. -/
theorem VEnv.boolNatITE_true_of_equation {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat)
    {l r ite : VExpr}
    (hl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(true)) l)
    (hr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hite : TrExprS env [] [] Condition.bool.boolNatITE ite) :
    ∃ A B, env.HasType 0 [] ite (.forallE A B) ∧
      env.HasType 0 [] .boolTrue A ∧
      env.IsDefEqU 0 [] (.app ite .boolTrue)
        (.lam .nat <| .lam .nat <| .bvar 1) := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have hnatS' (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat := by
    cases hnatS with
    | const hci hus hlen => exact .const hci hus hlen
  have hselector : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1)
      (.lam .nat <| .lam .nat <| .bvar 1) := by
    obtain ⟨u, hNatSort⟩ := hnatTy
    apply TrExprS.lam ⟨u, hNatSort⟩ (hnatS' [])
    apply TrExprS.lam ⟨u, hNatSort.weak0 wf⟩ (hnatS' _)
    exact TrExprS.bvar (A := .nat) (by
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth, VLocalDecl.value,
        VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat, liftVar])
  have hrEq := hr.uniq wf
    (.refl wf (U := 0) (Δ := []) (by trivial)) hselector
  cases hl with
  | app hiteT htrueT hite' htrue =>
    rename_i iteCert iteA iteB trueCert
    cases htrue with
    | const hci hus hlen =>
      rename_i ci us
      simp at hus
      subst us
      have hciEq := hprim.boolTrue hci
      subst ci
      have hiteEq := hite.uniq wf
        (.refl wf (U := 0) (Δ := []) (by trivial)) hite'
      have hlTrue : env.IsDefEqU 0 [] (.app ite .boolTrue)
          (.app iteCert .boolTrue) := by
        have hi := hiteEq.of_r wf trivial hiteT
        exact ⟨_, .appDF hi htrueT⟩
      refine ⟨iteA, iteB, ?_, ?_, ?_⟩
      · exact (hiteEq.of_r wf trivial hiteT).hasType.1
      · exact htrueT
      · exact hlTrue.trans wf trivial <| heq.trans wf trivial hrEq

/-- Normalize the checked `Bool.false` selector equation to the particular
translation of `boolNatITE` used by a certified bitwise equation. -/
theorem VEnv.boolNatITE_false_of_equation {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat)
    {l r ite : VExpr}
    (hl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(false)) l)
    (hr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hite : TrExprS env [] [] Condition.bool.boolNatITE ite) :
    ∃ A B, env.HasType 0 [] ite (.forallE A B) ∧
      env.HasType 0 [] .boolFalse A ∧
      env.IsDefEqU 0 [] (.app ite .boolFalse)
        (.lam .nat <| .lam .nat <| .bvar 0) := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have hnatS' (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat := by
    cases hnatS with
    | const hci hus hlen => exact .const hci hus hlen
  have hselector : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0)
      (.lam .nat <| .lam .nat <| .bvar 0) := by
    obtain ⟨u, hNatSort⟩ := hnatTy
    apply TrExprS.lam ⟨u, hNatSort⟩ (hnatS' [])
    apply TrExprS.lam ⟨u, hNatSort.weak0 wf⟩ (hnatS' _)
    exact TrExprS.bvar (A := .nat) (by
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type,
        VExpr.lift, VExpr.liftN, VExpr.nat])
  have hrEq := hr.uniq wf
    (.refl wf (U := 0) (Δ := []) (by trivial)) hselector
  cases hl with
  | app hiteT hfalseT hite' hfalse =>
    rename_i iteCert iteA iteB falseCert
    cases hfalse with
    | const hci hus hlen =>
      rename_i ci us
      simp at hus
      subst us
      have hciEq := hprim.boolFalse hci
      subst ci
      have hiteEq := hite.uniq wf
        (.refl wf (U := 0) (Δ := []) (by trivial)) hite'
      have hlFalse : env.IsDefEqU 0 [] (.app ite .boolFalse)
          (.app iteCert .boolFalse) := by
        have hi := hiteEq.of_r wf trivial hiteT
        exact ⟨_, .appDF hi hfalseT⟩
      refine ⟨iteA, iteB, ?_, ?_, ?_⟩
      · exact (hiteEq.of_r wf trivial hiteT).hasType.1
      · exact hfalseT
      · exact hlFalse.trans wf trivial <| heq.trans wf trivial hrEq

/-- The two equations emitted by `Condition.bool.check` give the reusable
semantic Boolean selector needed by certified bitwise transitions. -/
theorem VEnv.reflectsBoolNatITE_of_equations {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hnat : env.contains ``Nat)
    {ite tl tr fl fr : VExpr}
    (hiteS : TrExprS env [] [] Condition.bool.boolNatITE ite)
    (hiteT : env.HasType 0 [] ite
      (.forallE .bool <| .forallE .nat <| .forallE .nat .nat))
    (htl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(true)) tl)
    (htr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1) tr)
    (hteq : env.IsDefEqU 0 [] tl tr)
    (hfl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(false)) fl)
    (hfr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0) fr)
    (hfeq : env.IsDefEqU 0 [] fl fr) :
    env.ReflectsBoolNatITE ite := by
  obtain ⟨_, _, _, _, htrue⟩ :=
    VEnv.boolNatITE_true_of_equation wf hprim hnat htl htr hteq hiteS
  obtain ⟨_, _, _, _, hfalse⟩ :=
    VEnv.boolNatITE_false_of_equation wf hprim hnat hfl hfr hfeq hiteS
  have hnatT (n Γ) : env.HasType 0 Γ (.natLit n) .nat :=
    (TrExprS.natLit hprim hnat n (Us := []) (Δ := [])).2.weak0 wf
  have hnatTy₀ := (hnatT 0 []).isType wf trivial
  obtain ⟨u, hnatSort⟩ := hnatTy₀
  have hnatTy₁ : env.IsType 0 [.nat] .nat :=
    ⟨u, hnatSort.weak0 wf⟩
  exact VEnv.ReflectsBoolNatITE.of_equations wf
    (fun b => (TrExprS.boolLit hprim hbool b (Us := []) (Δ := [])).2)
    ⟨u, hnatSort⟩ hnatTy₁ hnatT hiteT htrue hfalse

/-- The eager fuel retained by a normalized auxiliary certificate evaluates
to every concrete numeral. -/
theorem VEnv.eager_natLit_of_aux_equations {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) (hbeqC : env.contains ``Nat.beq)
    {r : NatWellFoundedCoreResult} {el er tl tr : VExpr}
    (hel : TrExprS env [] [] r.expectedEagerLhs el)
    (her : TrExprS env [] [] r.expectedEagerRhs er)
    (heeq : env.IsDefEqU 0 [] el er)
    (htl : TrExprS env [] [] r.expectedBoolTrueLhs tl)
    (htr : TrExprS env [] [] r.expectedBoolTrueRhs tr)
    (hteq : env.IsDefEqU 0 [] tl tr) :
    ∃ eager,
      TrExprS env [] [] (r.eagerFn.instantiate1'
        (.natLitToConstructor n)) eager ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
  have ⟨hnatLitS, _hnatT0⟩ :=
    TrExprS.natLit hprim hnat n (Us := []) (Δ := [])
  cases hnatLitS with
  | lit _ hnatS =>
    have hnatT (n Γ) : env.HasType 0 Γ (.natLit n) .nat :=
      (TrExprS.natLit hprim hnat n (Us := []) (Δ := [])).2.weak0 wf
    obtain ⟨eager, ite, cond, A, B, heagerS, hiteS, hcondS,
      hiteT, hcondT, heagerEq⟩ :=
      VEnv.instantiate_eager_natLit_equation wf hel her heeq hnatS hnatT
    obtain ⟨A', B', hiteT', htrueT, htrueEq⟩ :=
      VEnv.boolNatITE_true_of_equation wf hprim hnat htl htr hteq hiteS
    have ⟨hbeqT, hbeqEval⟩ := hprim.natBEq hbeqC
    obtain ⟨ci, hci, _, hlen⟩ := (hbeqT 0 []).const_inv wf trivial
    have hbeqS : TrExprS env [] [] (.const ``Nat.beq [])
        (.const ``Nat.beq []) := .const hci rfl hlen
    have hbeqNS : TrExprS env [] []
        (mkApp (.const ``Nat.beq []) (.natLitToConstructor n))
        (.app (.const ``Nat.beq []) (.natLit n)) :=
      .app (hbeqT 0 []) (hnatT n []) hbeqS hnatS
    have hbeqNT := VEnv.HasType.app (hbeqT 0 []) (hnatT n [])
    have hcondCanon : TrExprS env [] []
        (mkApp2 (.const ``Nat.beq []) (.natLitToConstructor n)
          (.natLitToConstructor n))
        (.app (.app (.const ``Nat.beq []) (.natLit n)) (.natLit n)) :=
      .app hbeqNT (hnatT n []) hbeqNS hnatS
    have hcondEq := hcondS.uniq wf
      (.refl wf (U := 0) (Δ := []) (by trivial)) hcondCanon
    have hcondTrue := hcondEq.trans wf trivial
      (by simpa using hbeqEval n n)
    have hnatTy₀ := (hnatT 0 []).isType wf trivial
    obtain ⟨u, hNatSort⟩ := hnatTy₀
    have hnatTy₁ : env.IsType 0 [.nat] .nat := ⟨u, hNatSort.weak0 wf⟩
    have hselected := VEnv.boolNatITE_same_of_true_equation (n := n) wf
      ⟨u, hNatSort⟩ hnatTy₁ hnatT hiteT' htrueT hcondTrue htrueEq
    exact ⟨eager, heagerS, heagerEq.trans wf trivial hselected⟩

/-- Semantic relation represented by the translated recursive calls retained
in a gcd fixpoint certificate. -/
def VEnv.GcdGoCall (env : VEnv) (r : NatGcdFixCertificate)
    (fuel a b : Nat) (e : VExpr) : Prop :=
  ∃ goV fuelV stateV hpE hpV,
    TrExprS env [] [] r.core.goFn goV ∧
    TrExprS env [] []
      (r.stateExpr (.natLitToConstructor a) (.natLitToConstructor b)) stateV ∧
    TrExprS env [] [] hpE hpV ∧
    env.IsDefEqU 0 [] fuelV (.natLit fuel) ∧
    e = .app (.app (.app (.app (.app goV .natZero) .natZero) fuelV) stateV) hpV

/-- Semantic relation represented by the translated recursive calls retained
in a bitwise fixpoint certificate.  The Boolean operation is semantic rather
than source-translated, which is essential for the Kripke quantifier in
`ReflectsNatBitwise`. -/
def VEnv.BitwiseGoCall (env : VEnv) (r : NatBitwiseFixCertificate)
    (op : VExpr) (fuel a b : Nat) (e : VExpr) : Prop :=
  ∃ callV fuelV hpV,
    TrExprS env [] [] r.callFn callV ∧
    env.IsDefEqU 0 [] fuelV (.natLit fuel) ∧
    env.IsDefEqU 0 [] e
      (.app (.app (.app (.app (.app callV op) fuelV)
        (.natLit a)) (.natLit b)) hpV)

theorem VEnv.BitwiseGoCall.mono {env env' : VEnv}
    (h : VEnv.BitwiseGoCall env r op fuel a b e) (le : env ≤ env') :
    VEnv.BitwiseGoCall env' r op fuel a b e := by
  rcases h with ⟨callV, fuelV, hpV, hcall, hfuel, he⟩
  exact ⟨callV, fuelV, hpV, hcall.mono le, hfuel.mono le, he.mono le⟩

/-- The normalized top equation places each candidate gcd application in the
certified recursive-call relation at fuel `a + 1`. -/
theorem NatGcdFixCertificate.top_semantics {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {r : NatGcdFixCertificate} {gcd : Expr}
    (hgoClosedFlag : r.core.goFn.hasLooseBVars = false) {l rr f : VExpr}
    (hl : TrExprS env [] [] (r.expectedTopLhs gcd) l)
    (hr : TrExprS env [] [] r.expectedTopRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hgcd : TrExprS env [] [] gcd f)
    (hf : env.HasType 0 [] f (.forallE .nat <| .forallE .nat .nat))
    (heager : ∀ n, ∃ eager,
      TrExprS env [] [] q(WellFounded.Nat.eager) eager ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n)) :
    ∀ a b, ∃ e, VEnv.GcdGoCall env r (a+1) a b e ∧
      env.IsDefEqU 0 [] (.app (.app f (.natLit a)) (.natLit b)) e := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have lit (n) := TrExprS.natLit hprim hnat n (Us := []) (Δ := [])
  intro a b
  have haT := (lit a).2
  have hbT := (lit b).2
  have haLitS := (lit a).1
  have hbLitS := (lit b).1
  cases haLitS with
  | lit _ haS =>
   cases hbLitS with
   | lit _ hbS =>
    simp only [NatGcdFixCertificate.expectedTopLhs] at hl
    unfold NatGcdFixCertificate.expectedTopRhs at hr
    obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ := VEnv.instantiate_lam_equation wf
      (ty := q(Nat)) (by trivial) hl hr heq hnatS haS haT (by trivial)
    obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ := VEnv.instantiate_lam_equation wf
      (ty := q(Nat)) (by trivial) hl₁ hr₁ heq₁ hnatS hbS hbT (by trivial)
    have hgoClosed : r.core.goFn.looseBVarRange' = 0 := by
      simpa [Expr.hasLooseBVars, Expr.looseBVarRange'] using hgoClosedFlag
    cases hr₂ with
    | app h4T hpT h4 hp =>
      cases h4 with
      | app h3T stateT h3 state =>
        cases h3 with
        | app h2T fuelT h2 fuel =>
          cases h2 with
          | app h1T hz2T h1 hz2 =>
            cases h1 with
            | app hgoT hz1T hgo hz1 =>
              rename_i hpA hpB hpV stateA stateB stateV fuelA fuelB fuelV
                z2A z2B z2V goV goA goB z1V
              have hgoLe : r.core.goFn.looseBVarRange' ≤ 1 :=
                hgoClosed ▸ Nat.zero_le 1
              rw [Expr.instantiate1'_eq_self hgoLe,
                Expr.instantiate1_eq_self hgoClosed] at hgo
              have hzCanon :=
                (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).1
              have hz1' : TrExprS env [] [] q(Nat.zero) z1V := by
                simpa using hz1
              have hz2' : TrExprS env [] [] q(Nat.zero) z2V := by
                simpa using hz2
              cases hz1'.unique (by trivial) hzCanon
              cases hz2'.unique (by trivial) hzCanon
              have haLift : (Expr.natLitToConstructor a).liftLooseBVars' 0 1 =
                  Expr.natLitToConstructor a :=
                Expr.liftLooseBVars_eq_self
                  (Closed.natLitToConstructor
                    (n := a) (k := 0)).looseBVarRange_le
              have haInst : (Expr.natLitToConstructor a).instantiate1'
                  (Expr.natLitToConstructor b) = Expr.natLitToConstructor a :=
                Expr.instantiate1_eq_self
                  (Closed.natLitToConstructor
                    (n := a) (k := 0)).looseBVarRange_zero
              have hstate : TrExprS env [] []
                  (r.stateExpr (.natLitToConstructor a)
                    (.natLitToConstructor b)) stateV := by
                simpa [Literal.toConstructor, haLift, haInst, Expr.instantiate1',
                  Expr.looseBVarRange', NatGcdFixCertificate.stateExpr] using state
              obtain ⟨eager, heagerS, heagerEq⟩ := heager (a+1)
              have hsuccS :=
                (TrExprS.natSucc hprim hnat (Us := []) (Δ := [])).1
              have hsuccT :=
                (TrExprS.natSucc hprim hnat (Us := []) (Δ := [])).2
              have hsaS : TrExprS env [] []
                  (mkApp q(Nat.succ) (.natLitToConstructor a))
                  (.natLit (a+1)) := .app hsuccT haT hsuccS haS
              have hfuelCanon : TrExprS env [] []
                  (mkApp q(WellFounded.Nat.eager)
                    (mkApp q(Nat.succ) (.natLitToConstructor a)))
                  (.app eager (.natLit (a+1))) := by
                obtain ⟨_, heagerAppEq⟩ := heagerEq
                obtain ⟨_, _, heagerT, heagerArgT⟩ :=
                  heagerAppEq.hasType.1.app_inv wf.ordered trivial
                exact .app heagerT heagerArgT heagerS hsaS
              have hfuel : TrExprS env [] []
                  (mkApp q(WellFounded.Nat.eager)
                    (mkApp q(Nat.succ) (.natLitToConstructor a))) fuelV := by
                simpa [Literal.toConstructor, haLift, haInst, Expr.instantiate1',
                  Expr.looseBVarRange'] using fuel
              have hfuelEq := hfuel.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hfuelCanon
              have hfuelEval := hfuelEq.trans wf trivial heagerEq
              refine ⟨.app (.app (.app (.app (.app goV .natZero) .natZero)
                fuelV) stateV) hpV, ?_, ?_⟩
              · refine ⟨goV, fuelV, stateV, _, hpV, hgo, hstate, hp,
                  hfuelEval, rfl⟩
              · have hgcdClosed := hgcd.closed.looseBVarRange_zero
                have hgcdLe : gcd.looseBVarRange' ≤ 1 :=
                  hgcdClosed ▸ Nat.zero_le 1
                have hcall : TrExprS env [] []
                    (mkApp2 gcd (.natLitToConstructor a)
                      (.natLitToConstructor b))
                    (.app (.app f (.natLit a)) (.natLit b)) := by
                  have hfaS : TrExprS env [] []
                      (mkApp gcd (.natLitToConstructor a))
                      (.app f (.natLit a)) := .app hf haT hgcd haS
                  exact .app (VEnv.HasType.app hf haT) hbT hfaS hbS
                have hl₂' : TrExprS env [] []
                    (mkApp2 gcd (.natLitToConstructor a)
                      (.natLitToConstructor b)) l₂ := by
                  simpa [Literal.toConstructor, haLift, haInst,
                    Expr.instantiate1', Expr.looseBVarRange',
                    Expr.instantiate1'_eq_self hgcdLe,
                    Expr.instantiate1_eq_self hgcdClosed] using hl₂
                have hcallEq := hcall.uniq wf
                  (.refl wf (U := 0) (Δ := []) (by trivial)) hl₂'
                exact hcallEq.trans wf trivial heq₂

/-- A certified zero equation reduces every well-typed semantic gcd call
with zero as its first state component to the second component. -/
theorem NatGcdFixCertificate.zero_semantics {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) {r : NatGcdFixCertificate}
    {l rr : VExpr}
    (hl : TrExprS env [] [] r.expectedZeroLhs l)
    (hr : TrExprS env [] [] r.expectedZeroRhs rr)
    (heq : env.IsDefEqU 0 [] l rr) :
    ∀ fuel b e, VEnv.GcdGoCall env r (fuel+1) 0 b e →
      env.IsDefEqU 0 [] e e → env.IsDefEqU 0 [] e (.natLit b) := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have lit (n) := TrExprS.natLit hprim hnat n (Us := []) (Δ := [])
  intro fuel b e hG heSelf
  rcases hG with ⟨goV, fuelV, stateV, hpE, hpV, hgo, hstate, hpS,
    hfuelEq, rfl⟩
  have hfT := (lit fuel).2
  have hbT := (lit b).2
  have hfLitS := (lit fuel).1
  have hbLitS := (lit b).1
  cases hfLitS with
  | lit _ hfS =>
   cases hbLitS with
   | lit _ hbS =>
    unfold NatGcdFixCertificate.expectedZeroLhs at hl
    unfold NatGcdFixCertificate.expectedZeroRhs at hr
    obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ := VEnv.instantiate_lam_equation wf
      (ty := q(Nat)) (by trivial) hl hr heq hnatS hfS hfT (by trivial)
    obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ := VEnv.instantiate_lam_equation wf
      (ty := q(Nat)) (by trivial) hl₁ hr₁ heq₁ hnatS hbS hbT (by trivial)
    cases hl₂ with
    | lam hptyL hptySL hbodyL =>
      cases hr₂ with
      | lam hptyR hptySR hbodyR =>
        have hbodyLS := hbodyL
        cases hbodyL with
        | app hprefixCertT hbvarT hprefixCert hbvar =>
          cases hbvar with
          | bvar hb =>
            simp [VLCtx.find?, VLCtx.next] at hb
            rcases hb with ⟨rfl, rfl⟩
            rename_i proofTyL bodyL proofTyR bodyR prefixCert certA certB
            obtain ⟨_, heSelfD⟩ := heSelf
            have heT := heSelfD.hasType.1
            obtain ⟨hpA, hpB, hprefixT, hpT⟩ :=
              heT.app_inv wf.ordered trivial
            obtain ⟨stateA, stateB, hfuelPrefixT, hstateT⟩ :=
              hprefixT.app_inv wf.ordered trivial
            obtain ⟨fuelA, fuelB, hgoZerosT, hfuelT⟩ :=
              hfuelPrefixT.app_inv wf.ordered trivial
            have hnatFuelT := (hfuelEq.of_l wf trivial hfuelT).hasType.2
            have hcanonFuelPrefixT := VEnv.HasType.app hgoZerosT hnatFuelT
            have hfuelPrefixEq := hfuelEq.app_arg wf trivial hgoZerosT hfuelT
            have hcanonFuelPrefixT' :=
              (hfuelPrefixEq.of_l wf trivial hfuelPrefixT).hasType.2
            have hprefixRootT := VEnv.HasType.app hcanonFuelPrefixT' hstateT
            obtain ⟨z2A, z2B, hgoZ1T, hz2T⟩ :=
              hgoZerosT.app_inv wf.ordered trivial
            obtain ⟨z1A, z1B, hgoT, hz1T⟩ :=
              hgoZ1T.app_inv wf.ordered trivial
            have hzS := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).1
            have hgoZ1S : TrExprS env [] []
                (mkApp r.core.goFn q(Nat.zero)) (.app goV .natZero) :=
              .app hgoT hz1T hgo hzS
            have hgoZerosS : TrExprS env [] []
                (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                (.app (.app goV .natZero) .natZero) :=
              .app hgoZ1T hz2T hgoZ1S hzS
            have hsuccS :=
              (TrExprS.natSucc hprim hnat (Us := []) (Δ := [])).1
            have hsuccT :=
              (TrExprS.natSucc hprim hnat (Us := []) (Δ := [])).2
            have hsfS : TrExprS env [] []
                (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                (.natLit (fuel+1)) := .app hsuccT hfT hsuccS hfS
            have hgoFuelS : TrExprS env [] []
                (mkApp (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel)))
                (.app (.app (.app goV .natZero) .natZero) (.natLit (fuel+1))) :=
              .app hgoZerosT hnatFuelT hgoZerosS hsfS
            have hprefixRootS : TrExprS env [] []
                (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                  (r.stateExpr (.natLitToConstructor 0)
                    (.natLitToConstructor b)))
                (.app (.app (.app (.app goV .natZero) .natZero)
                  (.natLit (fuel+1))) stateV) :=
              .app hcanonFuelPrefixT' hstateT hgoFuelS hstate
            have hprefixClosed :=
              (hprefixRootT.closedN' wf.ordered.closed trivial).1
            have hprefixWeak : TrExprS env [] [(none, .vlam bodyL)]
                (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                  (r.stateExpr (.natLitToConstructor 0)
                    (.natLitToConstructor b)))
                (.app (.app (.app (.app goV .natZero) .natZero)
                  (.natLit (fuel+1))) stateV) := by
              have hw := hprefixRootS.weakBV wf.ordered
                (.skip (.vlam bodyL) (.refl : VLCtx.BVLift [] [] 0 0 0 0))
              simp only [Nat.zero_add, VLocalDecl.depth] at hw
              have hsourceLift :
                  (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                    (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                    (r.stateExpr (.natLitToConstructor 0)
                      (.natLitToConstructor b))).liftLooseBVars' 0 1 =
                    mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                      (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                      (r.stateExpr (.natLitToConstructor 0)
                        (.natLitToConstructor b)) :=
                Expr.liftLooseBVars_eq_self
                  hprefixRootS.closed.looseBVarRange_le
              rw [hsourceLift] at hw
              simpa [hprefixClosed.lift_eq] using hw
            have hprefixCert' : TrExprS env [] [(none, .vlam bodyL)]
                (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                  (r.stateExpr (.natLitToConstructor 0)
                    (.natLitToConstructor b))) prefixCert := by
              have hgoClosed := hgo.closed.looseBVarRange_zero
              have hgoLe2 : r.core.goFn.looseBVarRange' ≤ 2 :=
                hgoClosed ▸ Nat.zero_le 2
              have hgoLe1 : r.core.goFn.looseBVarRange' ≤ 1 :=
                hgoClosed ▸ Nat.zero_le 1
              have hfLift : (Expr.natLitToConstructor fuel).liftLooseBVars'
                  0 2 = Expr.natLitToConstructor fuel :=
                Expr.liftLooseBVars_eq_self
                  (Closed.natLitToConstructor
                    (n := fuel) (k := 0)).looseBVarRange_le
              have hfInst : (Expr.natLitToConstructor fuel).instantiate1'
                  (Expr.natLitToConstructor b) 1 =
                  Expr.natLitToConstructor fuel :=
                Expr.instantiate1'_eq_self (by
                  have h := (Closed.natLitToConstructor
                    (n := fuel) (k := 0)).looseBVarRange_le
                  omega)
              have hbLift : (Expr.natLitToConstructor b).liftLooseBVars'
                  0 1 = Expr.natLitToConstructor b :=
                Expr.liftLooseBVars_eq_self
                  (Closed.natLitToConstructor
                    (n := b) (k := 0)).looseBVarRange_le
              simpa [Literal.toConstructor, hfLift, hfInst, hbLift,
                Expr.instantiate1', Expr.looseBVarRange',
                Expr.instantiate1'_eq_self hgoLe2,
                Expr.instantiate1'_eq_self hgoLe1,
                Expr.instantiate1_eq_self hgoClosed,
                NatGcdFixCertificate.stateExpr] using hprefixCert
            have hctx : OnCtx [bodyL] (env.IsType 0) := ⟨trivial, hptyL⟩
            have hprefixEq := TrExprS.uniq (Us := [])
              (Δ₁ := [(none, .vlam bodyL)])
              (Δ₂ := [(none, .vlam bodyL)]) wf
              (.refl wf (U := 0) (Δ := [(none, .vlam bodyL)])
                ⟨trivial, nofun, hptyL⟩) hprefixCert' hprefixWeak
            have hprefixRightT :=
              (hprefixEq.of_l wf hctx hprefixCertT).hasType.2
            have hcanonicalPrefixEq := hfuelPrefixEq.app_same wf trivial
              hfuelPrefixT hstateT
            have hcanonicalPrefixT :=
              (hcanonicalPrefixEq.of_l wf trivial hprefixT).hasType.2
            have hprefixRootWeakT := hcanonicalPrefixT.weak0
              (Γ := [bodyL]) wf
            have hforallEq := hprefixRightT.uniqU wf hctx hprefixRootWeakT
            obtain ⟨_, hdomainEq⟩ := (hforallEq.forallE_inv wf hctx).1
            obtain ⟨uTy, hbodySort⟩ := hptyL
            have hbodyClosed :=
              (hbodySort.closedN' wf.ordered.closed trivial).1
            have hbvarCanon : env.HasType 0 [bodyL] (.bvar 0) bodyL := by
              simpa [hbodyClosed.lift_eq] using
                (show env.HasType 0 [bodyL] (.bvar 0) bodyL.lift from .bvar .zero)
            have hbvarTyEq := hbvarT.uniqU wf hctx hbvarCanon
            have hpTypeEqCtx : env.IsDefEqU 0 [bodyL] hpA bodyL :=
              hdomainEq.symm.toU.trans wf hctx hbvarTyEq
            have hpAClosed : hpA.ClosedN :=
              (hpT.closedN' wf.ordered.closed trivial).2.2
            have hpTypeEq : env.IsDefEqU 0 [] hpA bodyL := by
              apply (VEnv.IsDefEqU.weakN_iff wf hctx
                (Ctx.LiftN.one : Ctx.LiftN 1 0 [] [bodyL])).1
              simpa [hpAClosed.lift_eq, hbodyClosed.lift_eq] using hpTypeEqCtx
            have hpTL := hpT.defeqU_r wf trivial hpTypeEq
            have hproofTyEq := hptySL.uniq wf
              (.refl wf (U := 0) (Δ := []) (by trivial)) hptySR
            obtain ⟨BL, hbodyLT⟩ := hbodyLS.wf wf.ordered
              (Us := []) (Δ := [(none, .vlam bodyL)])
              ⟨trivial, nofun, ⟨uTy, hbodySort⟩⟩
            obtain ⟨BR, hbodyRT⟩ := hbodyR.wf wf.ordered
              (Us := []) (Δ := [(none, .vlam proofTyR)])
              ⟨trivial, nofun, hptyR⟩
            have hinst := VEnv.IsDefEqU.lam_instU₂ wf trivial heq₂ hbodySort
              hbodyLT hbodyRT hproofTyEq hpTL
            have hprefixAppEqCtx := hprefixEq.app_same wf hctx
              hprefixCertT hbvarT
            have hprefixAppEq := hprefixAppEqCtx.instN wf.ordered
              (.zero : Ctx.InstN [] hpV bodyL 0 [bodyL] []) hpTL
            have hcanonicalCallEq := hcanonicalPrefixEq.app_same wf trivial
              hprefixT hpT
            have hleftEq : env.IsDefEqU 0 []
                (.app (.app (.app (.app (.app goV .natZero) .natZero)
                  fuelV) stateV) hpV)
                ((prefixCert.app (.bvar 0)).inst hpV) := by
              have hclosedPrefix :
                  (VExpr.app (VExpr.app (VExpr.app
                    (VExpr.app goV .natZero) .natZero)
                    (.natLit (fuel+1))) stateV).ClosedN := hprefixClosed
              have hprefixAppEq' : env.IsDefEqU 0 []
                  ((prefixCert.app (.bvar 0)).inst hpV)
                  (.app (.app (.app (.app (.app goV .natZero) .natZero)
                    (.natLit (fuel+1))) stateV) hpV) := by
                have hi := hprefixAppEq
                have hgoVClosed : goV.ClosedN :=
                  (hgoT.closedN' wf.ordered.closed trivial).1
                have hzVClosed : VExpr.natZero.ClosedN :=
                  (hz1T.closedN' wf.ordered.closed trivial).1
                have hfVClosed : (VExpr.natLit (fuel+1)).ClosedN :=
                  (hnatFuelT.closedN' wf.ordered.closed trivial).1
                have hstateVClosed : stateV.ClosedN :=
                  (hstateT.closedN' wf.ordered.closed trivial).1
                simpa [VLocalDecl.value, VExpr.inst, VExpr.instVar,
                  hgoVClosed.instN_eq, hzVClosed.instN_eq,
                  hfVClosed.instN_eq, hstateVClosed.instN_eq] using hi
              exact hcanonicalCallEq.trans wf trivial hprefixAppEq'.symm
            have hpTR := hpTL.defeqU_r wf trivial hproofTyEq
            have hrightInstS := TrExprS.inst (Us := []) (Δ := [])
              wf.ordered hpTR hbodyR hpS
            have hrightS : TrExprS env [] []
                (.natLitToConstructor b) (bodyR.inst hpV) := by
              have hbLift : (Expr.natLitToConstructor b).liftLooseBVars'
                  0 1 = Expr.natLitToConstructor b :=
                Expr.liftLooseBVars_eq_self
                  (Closed.natLitToConstructor
                    (n := b) (k := 0)).looseBVarRange_le
              have hbInst : (Expr.natLitToConstructor b).instantiate1'
                  hpE = Expr.natLitToConstructor b :=
                Expr.instantiate1_eq_self
                  (Closed.natLitToConstructor
                    (n := b) (k := 0)).looseBVarRange_zero
              simpa [Literal.toConstructor, hbLift, hbInst,
                Expr.instantiate1', Expr.looseBVarRange'] using hrightInstS
            have hrightEq := hrightS.uniq wf
              (.refl wf (U := 0) (Δ := []) (by trivial)) hbS
            exact hleftEq.trans wf trivial hinst |>.trans wf trivial hrightEq

/-- A certified successor equation turns a well-typed semantic gcd call
into the Euclidean recursive call at one less unit of fuel. -/
theorem NatGcdFixCertificate.succ_semantics {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) (hmodC : env.contains ``Nat.mod)
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod)
    {r : NatGcdFixCertificate}
    {l rr : VExpr}
    (hl : TrExprS env [] [] r.expectedSuccLhs l)
    (hr : TrExprS env [] [] r.expectedSuccRhs rr)
    (heq : env.IsDefEqU 0 [] l rr) :
    ∀ fuel a b e, VEnv.GcdGoCall env r (fuel+1) (a+1) b e →
      env.IsDefEqU 0 [] e e →
      ∃ e', VEnv.GcdGoCall env r fuel (b % (a+1)) (a+1) e' ∧
        env.IsDefEqU 0 [] e e' := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have lit (n) := TrExprS.natLit hprim hnat n (Us := []) (Δ := [])
  intro fuel a b e hG heSelf
  rcases hG with ⟨goV, fuelV, stateV, hpE, hpV, hgo, hstate, hpS,
    hfuelEq, rfl⟩
  have hfT := (lit fuel).2
  have haT := (lit a).2
  have hbT := (lit b).2
  have hfLitS := (lit fuel).1
  have haLitS := (lit a).1
  have hbLitS := (lit b).1
  cases hfLitS with
  | lit _ hfS =>
   cases haLitS with
   | lit _ haS =>
    cases hbLitS with
    | lit _ hbS =>
      unfold NatGcdFixCertificate.expectedSuccLhs at hl
      unfold NatGcdFixCertificate.expectedSuccRhs at hr
      obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ := VEnv.instantiate_lam_equation wf
        (ty := q(Nat)) (by trivial) hl hr heq hnatS hfS hfT (by trivial)
      obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ := VEnv.instantiate_lam_equation wf
        (ty := q(Nat)) (by trivial) hl₁ hr₁ heq₁ hnatS haS haT (by trivial)
      obtain ⟨l₃, r₃, hl₃, hr₃, heq₃⟩ := VEnv.instantiate_lam_equation wf
        (ty := q(Nat)) (by trivial) hl₂ hr₂ heq₂ hnatS hbS hbT (by trivial)
      cases hl₃ with
      | lam hptyL hptySL hbodyL =>
        cases hr₃ with
        | lam hptyR hptySR hbodyR =>
          have hbodyLS := hbodyL
          cases hbodyL with
          | app hprefixCertT hbvarT hprefixCert hbvar =>
            cases hbvar with
            | bvar hb =>
              simp [VLCtx.find?, VLCtx.next] at hb
              rcases hb with ⟨rfl, rfl⟩
              rename_i bodyL proofTyR bodyR prefixCert certA certB
              obtain ⟨_, heSelfD⟩ := heSelf
              have heT := heSelfD.hasType.1
              obtain ⟨hpA, hpB, hprefixT, hpT⟩ :=
                heT.app_inv wf.ordered trivial
              obtain ⟨stateA, stateB, hfuelPrefixT, hstateT⟩ :=
                hprefixT.app_inv wf.ordered trivial
              obtain ⟨fuelA, fuelB, hgoZerosT, hfuelT⟩ :=
                hfuelPrefixT.app_inv wf.ordered trivial
              have hnatFuelT := (hfuelEq.of_l wf trivial hfuelT).hasType.2
              have hcanonFuelPrefixT := VEnv.HasType.app hgoZerosT hnatFuelT
              have hfuelPrefixEq := hfuelEq.app_arg wf trivial hgoZerosT hfuelT
              have hcanonFuelPrefixT' :=
                (hfuelPrefixEq.of_l wf trivial hfuelPrefixT).hasType.2
              have hprefixRootT := VEnv.HasType.app hcanonFuelPrefixT' hstateT
              obtain ⟨z2A, z2B, hgoZ1T, hz2T⟩ :=
                hgoZerosT.app_inv wf.ordered trivial
              obtain ⟨z1A, z1B, hgoT, hz1T⟩ :=
                hgoZ1T.app_inv wf.ordered trivial
              have hzS := (TrExprS.natZero hprim hnat
                (Us := []) (Δ := [])).1
              have hgoZ1S : TrExprS env [] []
                  (mkApp r.core.goFn q(Nat.zero)) (.app goV .natZero) :=
                .app hgoT hz1T hgo hzS
              have hgoZerosS : TrExprS env [] []
                  (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (.app (.app goV .natZero) .natZero) :=
                .app hgoZ1T hz2T hgoZ1S hzS
              have hsuccS := (TrExprS.natSucc hprim hnat
                (Us := []) (Δ := [])).1
              have hsuccT := (TrExprS.natSucc hprim hnat
                (Us := []) (Δ := [])).2
              have hsfS : TrExprS env [] []
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                  (.natLit (fuel+1)) := .app hsuccT hfT hsuccS hfS
              have hsaS : TrExprS env [] []
                  (mkApp q(Nat.succ) (.natLitToConstructor a))
                  (.natLit (a+1)) := .app hsuccT haT hsuccS haS
              obtain ⟨stateCanon, hstateSucc, hstateEq, hstateCanonT⟩ :
                  ∃ stateCanon,
                    TrExprS env [] []
                      (r.stateExpr
                        (mkApp q(Nat.succ) (.natLitToConstructor a))
                        (.natLitToConstructor b)) stateCanon ∧
                    env.IsDefEqU 0 [] stateV stateCanon ∧
                    env.HasType 0 [] stateCanon stateA := by
                have hstateShape := hstate
                cases hstateShape with
                | app hstateAT hbStateT hstateA hbState =>
                  cases hstateA with
                  | app hmkT haStateT hmk haState =>
                    rename_i bA bB bV stateFn aA aB aV
                    have hsaLitS := (lit (a+1)).1
                    cases hsaLitS with
                    | lit _ hsaCtorS =>
                      have haEq := haState.uniq wf
                        (.refl wf (U := 0) (Δ := []) (by trivial)) hsaCtorS
                      have hbEq := hbState.uniq wf
                        (.refl wf (U := 0) (Δ := []) (by trivial)) hbS
                      have haCanonT :=
                        (haEq.of_l wf trivial haStateT).hasType.2
                      have hmkAEq := haEq.app_arg wf trivial hmkT haStateT
                      have hmkACanonT :=
                        (hmkAEq.of_l wf trivial hstateAT).hasType.2
                      have hbCanonT :=
                        (hbEq.of_l wf trivial hbStateT).hasType.2
                      let stateCanon := VExpr.app
                        (VExpr.app stateFn (.natLit (a+1))) (.natLit b)
                      have hstateLitCanon : TrExprS env [] []
                          (r.stateExpr (.natLitToConstructor (a+1))
                            (.natLitToConstructor b)) stateCanon :=
                        .app hmkACanonT hbCanonT
                          (.app hmkT haCanonT hmk hsaCtorS) hbS
                      have hstateSucc : TrExprS env [] []
                          (r.stateExpr
                            (mkApp q(Nat.succ) (.natLitToConstructor a))
                            (.natLitToConstructor b)) stateCanon :=
                        .app hmkACanonT hbCanonT
                          (.app hmkT haCanonT hmk hsaS) hbS
                      have hstateEq := hstate.uniq wf
                        (.refl wf (U := 0) (Δ := []) (by trivial))
                        hstateLitCanon
                      have hstateCanonT :=
                        (hstateEq.of_l wf trivial hstateT).hasType.2
                      exact ⟨stateCanon, hstateSucc, hstateEq,
                        hstateCanonT⟩
              have hgoFuelS : TrExprS env [] []
                  (mkApp (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                    (mkApp q(Nat.succ) (.natLitToConstructor fuel)))
                  (.app (.app (.app goV .natZero) .natZero)
                    (.natLit (fuel+1))) :=
                .app hgoZerosT hnatFuelT hgoZerosS hsfS
              have hprefixRootS : TrExprS env [] []
                  (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                    (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                    (r.stateExpr
                      (mkApp q(Nat.succ) (.natLitToConstructor a))
                      (.natLitToConstructor b)))
                  (.app (.app (.app (.app goV .natZero) .natZero)
                    (.natLit (fuel+1))) stateCanon) :=
                .app hcanonFuelPrefixT' hstateCanonT hgoFuelS hstateSucc
              have hprefixRootCanonT :=
                VEnv.HasType.app hcanonFuelPrefixT' hstateCanonT
              have hprefixClosed :=
                (hprefixRootCanonT.closedN' wf.ordered.closed trivial).1
              have hprefixWeak : TrExprS env [] [(none, .vlam bodyL)]
                  (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                    (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                    (r.stateExpr
                      (mkApp q(Nat.succ) (.natLitToConstructor a))
                      (.natLitToConstructor b)))
                  (.app (.app (.app (.app goV .natZero) .natZero)
                    (.natLit (fuel+1))) stateCanon) := by
                have hw := hprefixRootS.weakBV wf.ordered
                  (.skip (.vlam bodyL)
                    (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                simp only [Nat.zero_add, VLocalDecl.depth] at hw
                have hsourceLift :
                    (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                      (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                      (r.stateExpr
                        (mkApp q(Nat.succ) (.natLitToConstructor a))
                        (.natLitToConstructor b))).liftLooseBVars' 0 1 =
                      mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                        (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                        (r.stateExpr
                          (mkApp q(Nat.succ) (.natLitToConstructor a))
                          (.natLitToConstructor b)) :=
                  Expr.liftLooseBVars_eq_self
                    hprefixRootS.closed.looseBVarRange_le
                rw [hsourceLift] at hw
                simpa [hprefixClosed.lift_eq] using hw
              have hprefixCert' : TrExprS env [] [(none, .vlam bodyL)]
                  (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                    (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                    (r.stateExpr
                      (mkApp q(Nat.succ) (.natLitToConstructor a))
                      (.natLitToConstructor b))) prefixCert := by
                have hgoClosed := hgo.closed.looseBVarRange_zero
                have hgoLe3 : r.core.goFn.looseBVarRange' ≤ 3 :=
                  hgoClosed ▸ Nat.zero_le 3
                have hgoLe2 : r.core.goFn.looseBVarRange' ≤ 2 :=
                  hgoClosed ▸ Nat.zero_le 2
                have hgoLe1 : r.core.goFn.looseBVarRange' ≤ 1 :=
                  hgoClosed ▸ Nat.zero_le 1
                have hfLift3 : (Expr.natLitToConstructor fuel).liftLooseBVars'
                    0 3 = Expr.natLitToConstructor fuel :=
                  Expr.liftLooseBVars_eq_self
                    (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_le
                have hfInst2 : (Expr.natLitToConstructor fuel).instantiate1'
                    (Expr.natLitToConstructor a) 2 =
                    Expr.natLitToConstructor fuel :=
                  Expr.instantiate1'_eq_self (by
                    have h := (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_le
                    omega)
                have hfInst1 : (Expr.natLitToConstructor fuel).instantiate1'
                    (Expr.natLitToConstructor b) 1 =
                    Expr.natLitToConstructor fuel :=
                  Expr.instantiate1'_eq_self (by
                    have h := (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_le
                    omega)
                have haLift2 : (Expr.natLitToConstructor a).liftLooseBVars'
                    0 2 = Expr.natLitToConstructor a :=
                  Expr.liftLooseBVars_eq_self
                    (Closed.natLitToConstructor
                      (n := a) (k := 0)).looseBVarRange_le
                have haInst1 : (Expr.natLitToConstructor a).instantiate1'
                    (Expr.natLitToConstructor b) 1 =
                    Expr.natLitToConstructor a :=
                  Expr.instantiate1'_eq_self (by
                    have h := (Closed.natLitToConstructor
                      (n := a) (k := 0)).looseBVarRange_le
                    omega)
                have hbLift1 : (Expr.natLitToConstructor b).liftLooseBVars'
                    0 1 = Expr.natLitToConstructor b :=
                  Expr.liftLooseBVars_eq_self
                    (Closed.natLitToConstructor
                      (n := b) (k := 0)).looseBVarRange_le
                simp [Literal.toConstructor, hfLift3, hfInst2, hfInst1,
                  haLift2, haInst1, hbLift1, Expr.instantiate1',
                  Expr.instantiate1'_eq_self hgoLe3,
                  Expr.instantiate1'_eq_self hgoLe2,
                  Expr.instantiate1'_eq_self hgoLe1,
                  NatGcdFixCertificate.stateExpr] at hprefixCert ⊢
                exact hprefixCert
              have hctx : OnCtx [bodyL] (env.IsType 0) := ⟨trivial, hptyL⟩
              have hprefixEq := TrExprS.uniq (Us := [])
                (Δ₁ := [(none, .vlam bodyL)])
                (Δ₂ := [(none, .vlam bodyL)]) wf
                (.refl wf (U := 0) (Δ := [(none, .vlam bodyL)])
                  ⟨trivial, nofun, hptyL⟩) hprefixCert' hprefixWeak
              have hprefixRightT :=
                (hprefixEq.of_l wf hctx hprefixCertT).hasType.2
              have hcanonicalPrefixEq := hfuelPrefixEq.app_both wf trivial
                hstateEq hfuelPrefixT hstateT
              have hcanonicalPrefixT :=
                (hcanonicalPrefixEq.of_l wf trivial hprefixT).hasType.2
              have hprefixRootWeakT := hcanonicalPrefixT.weak0
                (Γ := [bodyL]) wf
              have hforallEq := hprefixRightT.uniqU wf hctx hprefixRootWeakT
              obtain ⟨_, hdomainEq⟩ := (hforallEq.forallE_inv wf hctx).1
              obtain ⟨uTy, hbodySort⟩ := hptyL
              have hbodyClosed :=
                (hbodySort.closedN' wf.ordered.closed trivial).1
              have hbvarCanon : env.HasType 0 [bodyL] (.bvar 0) bodyL := by
                simpa [hbodyClosed.lift_eq] using
                  (show env.HasType 0 [bodyL] (.bvar 0) bodyL.lift from
                    .bvar .zero)
              have hbvarTyEq := hbvarT.uniqU wf hctx hbvarCanon
              have hpTypeEqCtx : env.IsDefEqU 0 [bodyL] hpA bodyL :=
                hdomainEq.symm.toU.trans wf hctx hbvarTyEq
              have hpAClosed : hpA.ClosedN :=
                (hpT.closedN' wf.ordered.closed trivial).2.2
              have hpTypeEq : env.IsDefEqU 0 [] hpA bodyL := by
                apply (VEnv.IsDefEqU.weakN_iff wf hctx
                  (Ctx.LiftN.one : Ctx.LiftN 1 0 [] [bodyL])).1
                simpa [hpAClosed.lift_eq, hbodyClosed.lift_eq] using
                  hpTypeEqCtx
              have hpTL := hpT.defeqU_r wf trivial hpTypeEq
              have hproofTyEq := hptySL.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hptySR
              obtain ⟨BL, hbodyLT⟩ := hbodyLS.wf wf.ordered
                (Us := []) (Δ := [(none, .vlam bodyL)])
                ⟨trivial, nofun, ⟨uTy, hbodySort⟩⟩
              obtain ⟨BR, hbodyRT⟩ := hbodyR.wf wf.ordered
                (Us := []) (Δ := [(none, .vlam proofTyR)])
                ⟨trivial, nofun, hptyR⟩
              have hinst := VEnv.IsDefEqU.lam_instU₂ wf trivial heq₃
                hbodySort hbodyLT hbodyRT hproofTyEq hpTL
              have hprefixAppEqCtx := hprefixEq.app_same wf hctx
                hprefixCertT hbvarT
              have hprefixAppEq := hprefixAppEqCtx.instN wf.ordered
                (.zero : Ctx.InstN [] hpV bodyL 0 [bodyL] []) hpTL
              have hcanonicalCallEq := hcanonicalPrefixEq.app_same wf trivial
                hprefixT hpT
              have hleftEq : env.IsDefEqU 0 []
                  (.app (.app (.app (.app (.app goV .natZero) .natZero)
                    fuelV) stateV) hpV)
                  ((prefixCert.app (.bvar 0)).inst hpV) := by
                have hprefixAppEq' : env.IsDefEqU 0 []
                    ((prefixCert.app (.bvar 0)).inst hpV)
                    (.app (.app (.app (.app (.app goV .natZero) .natZero)
                      (.natLit (fuel+1))) stateCanon) hpV) := by
                  have hgoVClosed : goV.ClosedN :=
                    (hgoT.closedN' wf.ordered.closed trivial).1
                  have hzVClosed : VExpr.natZero.ClosedN :=
                    (hz1T.closedN' wf.ordered.closed trivial).1
                  have hfVClosed : (VExpr.natLit (fuel+1)).ClosedN :=
                    (hnatFuelT.closedN' wf.ordered.closed trivial).1
                  have hstateVClosed : stateCanon.ClosedN :=
                    (hstateCanonT.closedN' wf.ordered.closed trivial).1
                  simpa [VLocalDecl.value, VExpr.inst, VExpr.instVar,
                    hgoVClosed.instN_eq, hzVClosed.instN_eq,
                    hfVClosed.instN_eq, hstateVClosed.instN_eq] using
                    hprefixAppEq
                exact hcanonicalCallEq.trans wf trivial hprefixAppEq'.symm
              have hpTR := hpTL.defeqU_r wf trivial hproofTyEq
              have hrightInstS := TrExprS.inst (Us := []) (Δ := [])
                wf.ordered hpTR hbodyR hpS
              have hleftToRight := hleftEq.trans wf trivial hinst
              let proofSpec :=
                (((r.succProof.instantiate1' (.natLitToConstructor fuel) 3)
                    |>.instantiate1' (.natLitToConstructor a) 2)
                    |>.instantiate1' (.natLitToConstructor b) 1)
                    |>.instantiate1' hpE
              have hrightS : TrExprS env [] []
                  (mkAppN (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                    #[.natLitToConstructor fuel,
                      r.stateExpr
                        (mkApp2 q(Nat.mod) (.natLitToConstructor b)
                          (mkApp q(Nat.succ) (.natLitToConstructor a)))
                        (mkApp q(Nat.succ) (.natLitToConstructor a)),
                      proofSpec])
                  (bodyR.inst hpV) := by
                have hgoClosed := hgo.closed.looseBVarRange_zero
                have hgoLe3 : r.core.goFn.looseBVarRange' ≤ 3 :=
                  hgoClosed ▸ Nat.zero_le 3
                have hgoLe2 : r.core.goFn.looseBVarRange' ≤ 2 :=
                  hgoClosed ▸ Nat.zero_le 2
                have hgoLe1 : r.core.goFn.looseBVarRange' ≤ 1 :=
                  hgoClosed ▸ Nat.zero_le 1
                have hfLift3 : (Expr.natLitToConstructor fuel).liftLooseBVars'
                    0 3 = Expr.natLitToConstructor fuel :=
                  Expr.liftLooseBVars_eq_self
                    (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_le
                have hfInst2 : (Expr.natLitToConstructor fuel).instantiate1'
                    (Expr.natLitToConstructor a) 2 =
                    Expr.natLitToConstructor fuel :=
                  Expr.instantiate1'_eq_self (by
                    have h := (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_le
                    omega)
                have hfInst1 : (Expr.natLitToConstructor fuel).instantiate1'
                    (Expr.natLitToConstructor b) 1 =
                    Expr.natLitToConstructor fuel :=
                  Expr.instantiate1'_eq_self (by
                    have h := (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_le
                    omega)
                have hfInst0 : (Expr.natLitToConstructor fuel).instantiate1'
                    hpE = Expr.natLitToConstructor fuel :=
                  Expr.instantiate1_eq_self
                    (Closed.natLitToConstructor
                      (n := fuel) (k := 0)).looseBVarRange_zero
                have haLift2 : (Expr.natLitToConstructor a).liftLooseBVars'
                    0 2 = Expr.natLitToConstructor a :=
                  Expr.liftLooseBVars_eq_self
                    (Closed.natLitToConstructor
                      (n := a) (k := 0)).looseBVarRange_le
                have haInst1 : (Expr.natLitToConstructor a).instantiate1'
                    (Expr.natLitToConstructor b) 1 =
                    Expr.natLitToConstructor a :=
                  Expr.instantiate1'_eq_self (by
                    have h := (Closed.natLitToConstructor
                      (n := a) (k := 0)).looseBVarRange_le
                    omega)
                have haInst0 : (Expr.natLitToConstructor a).instantiate1'
                    hpE = Expr.natLitToConstructor a :=
                  Expr.instantiate1_eq_self
                    (Closed.natLitToConstructor
                      (n := a) (k := 0)).looseBVarRange_zero
                have hbLift1 : (Expr.natLitToConstructor b).liftLooseBVars'
                    0 1 = Expr.natLitToConstructor b :=
                  Expr.liftLooseBVars_eq_self
                    (Closed.natLitToConstructor
                      (n := b) (k := 0)).looseBVarRange_le
                have hbInst0 : (Expr.natLitToConstructor b).instantiate1'
                    hpE = Expr.natLitToConstructor b :=
                  Expr.instantiate1_eq_self
                    (Closed.natLitToConstructor
                      (n := b) (k := 0)).looseBVarRange_zero
                simpa [mkAppN, proofSpec, Literal.toConstructor,
                  NatGcdFixCertificate.stateExpr, Expr.instantiate1',
                  hfLift3, hfInst2,
                  hfInst1, hfInst0, haLift2, haInst1, haInst0,
                  hbLift1, hbInst0,
                  Expr.instantiate1'_eq_self hgoLe3,
                  Expr.instantiate1'_eq_self hgoLe2,
                  Expr.instantiate1'_eq_self hgoLe1,
                  Expr.instantiate1_eq_self hgoClosed] using hrightInstS
              generalize heRight : bodyR.inst hpV = rightV at hrightS hleftToRight ⊢
              cases hrightS with
              | app hrightPrefixT hproofSpecT hrightPrefix hproofSpecS =>
                cases hrightPrefix with
                | app hrightFuelT hrightStateT hrightFuel hrightState =>
                  cases hrightFuel with
                  | app hrightZerosT hrightFuelArgT hrightZeros hrightFuelArg =>
                    simp at hproofSpecS hrightState hrightFuelArg
                    cases hrightZeros with
                    | app hrightGoZ1T hrightZ2T hrightGoZ1 hrightZ2 =>
                      cases hrightGoZ1 with
                      | app hrightGoT hrightZ1T hrightGo hrightZ1 =>
                        rename_i proofArgA proofArgB proofV
                          stateArgA stateArgB stateR
                          fuelArgA fuelArgB fuelR
                          z2ArgA z2ArgB z2V
                          goR z1ArgA z1ArgB z1V
                        cases hrightZ1.unique (by trivial) hzS
                        cases hrightZ2.unique (by trivial) hzS
                        have hrightFuelEq := hrightFuelArg.uniq wf
                          (.refl wf (U := 0) (Δ := []) (by trivial)) hfS
                        have ⟨hmodT, hmodEval⟩ := hmod hmodC
                        obtain ⟨modCi, hmodCi, _, hmodLen⟩ :=
                          (hmodT 0 []).const_inv wf trivial
                        have hmodS : TrExprS env [] [] q(Nat.mod)
                            (.const ``Nat.mod []) :=
                          .const hmodCi rfl hmodLen
                        have hsaT := VEnv.HasType.app hsuccT haT
                        have hmodBS : TrExprS env [] []
                            (mkApp q(Nat.mod) (.natLitToConstructor b))
                            (.app (.const ``Nat.mod []) (.natLit b)) :=
                          .app (hmodT 0 []) hbT hmodS hbS
                        have hmodCallS : TrExprS env [] []
                            (mkApp2 q(Nat.mod) (.natLitToConstructor b)
                              (mkApp q(Nat.succ) (.natLitToConstructor a)))
                            (.app (.app (.const ``Nat.mod []) (.natLit b))
                              (.natLit (a+1))) :=
                          .app (VEnv.HasType.app (hmodT 0 []) hbT) hsaT
                            hmodBS hsaS
                        obtain ⟨stateNext, hstateNextS, hstateNextEq,
                            hstateNextT⟩ :
                            ∃ stateNext,
                              TrExprS env [] []
                                (r.stateExpr
                                  (.natLitToConstructor (b % (a+1)))
                                  (.natLitToConstructor (a+1))) stateNext ∧
                              env.IsDefEqU 0 [] stateR stateNext ∧
                              env.HasType 0 [] stateNext stateArgA := by
                          have hstateShape := hrightState
                          cases hstateShape with
                          | app hstateAT hbStateT hstateA hbState =>
                            cases hstateA with
                            | app hmkT hmodStateT hmk hmodState =>
                              rename_i saA saB saV stateFn modA modB modV
                              have hmodTrEq := hmodState.uniq wf
                                (.refl wf (U := 0) (Δ := []) (by trivial))
                                hmodCallS
                              have hmodValueEq := hmodTrEq.trans wf trivial
                                (hmodEval b (a+1))
                              have hsaEq := hbState.uniq wf
                                (.refl wf (U := 0) (Δ := []) (by trivial))
                                hsaS
                              have hstateFnEq := hmodValueEq.app_arg wf trivial
                                hmkT hmodStateT
                              have hstateValueEq := hstateFnEq.app_both wf trivial
                                hsaEq hstateAT hbStateT
                              have hremT :=
                                (hmodValueEq.of_l wf trivial hmodStateT).hasType.2
                              have hstateFnRemT :=
                                (hstateFnEq.of_l wf trivial hstateAT).hasType.2
                              have hsaCanonT :=
                                (hsaEq.of_l wf trivial hbStateT).hasType.2
                              have hremLitS := (lit (b % (a+1))).1
                              have hsaLitS := (lit (a+1)).1
                              cases hremLitS with
                              | lit _ hremS =>
                               cases hsaLitS with
                               | lit _ hsaCtorS =>
                                let stateNext := VExpr.app
                                  (VExpr.app stateFn (.natLit (b % (a+1))))
                                  (.natLit (a+1))
                                have hstateNextS : TrExprS env [] []
                                    (r.stateExpr
                                      (.natLitToConstructor (b % (a+1)))
                                      (.natLitToConstructor (a+1))) stateNext :=
                                  .app hstateFnRemT hsaCanonT
                                    (.app hmkT hremT hmk hremS) hsaCtorS
                                have hstateNextT :=
                                  (hstateValueEq.of_l wf trivial
                                    hrightStateT).hasType.2
                                exact ⟨stateNext, hstateNextS,
                                  hstateValueEq, hstateNextT⟩
                        have hrightFuelPrefixEq := hrightFuelEq.app_arg wf
                          trivial hrightZerosT hrightFuelArgT
                        have hrightStatePrefixEq :=
                          hrightFuelPrefixEq.app_both wf trivial hstateNextEq
                            hrightFuelT hrightStateT
                        have hrightCallEq := hrightStatePrefixEq.app_same wf
                          trivial hrightPrefixT hproofSpecT
                        let e' := VExpr.app (VExpr.app (VExpr.app
                          (VExpr.app (VExpr.app goR .natZero) .natZero)
                            (.natLit fuel)) stateNext) proofV
                        have hfuelSelf := hrightFuelEq.symm.trans wf trivial
                          hrightFuelEq
                        refine ⟨e', ?_, hleftToRight.trans wf trivial
                          hrightCallEq⟩
                        exact ⟨goR, .natLit fuel, stateNext, proofSpec, proofV,
                          hrightGo, hstateNextS, hproofSpecS, hfuelSelf, rfl⟩

theorem checkNatWellFoundedCertificate.WF {c : VContext} {s : VState}
    {r : NatWellFoundedCoreResult} :
    M.WF c s (checkNatWellFoundedCertificate r) fun _ _ => r.Valid c := by
  simp only [checkNatWellFoundedCertificate]
  split
  · rename_i hshape
    exact checkNatWellFoundedEquation.WF.bind fun _ _ _ hcall =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hentry =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ htop =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ heager =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hboolTrue =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hboolFalse =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hstep =>
      checkNatWellFoundedEquation.WF.mono fun _ _ _ hspecStep =>
        ⟨hshape, hcall, hentry, htop, heager, hboolTrue, hboolFalse,
          hstep, hspecStep⟩
  · exact .throw

def NatGcdFixCertificate.Valid (c : VContext) (r : NatGcdFixCertificate) : Prop :=
    r.core.Valid c ∧
    (∃ lhs' rhs', c.TrExprS r.topLhs lhs' ∧ c.TrExprS r.topRhs rhs' ∧
      c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.zeroLhs lhs' ∧ c.TrExprS r.zeroRhs rhs' ∧
      c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.succLhs lhs' ∧ c.TrExprS r.succRhs rhs' ∧
      c.IsDefEqU lhs' rhs')

/-- The independently checked gcd equations, transported to the canonical
source shapes retained in the certificate. -/
def NatGcdFixCertificate.NormalizedValid (c : VContext)
    (r : NatGcdFixCertificate) (gcd : Expr) : Prop :=
    r.core.Valid c ∧
    (∃ lhs' rhs', c.TrExprS (r.expectedTopLhs gcd) lhs' ∧
      c.TrExprS r.expectedTopRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedZeroLhs lhs' ∧
      c.TrExprS r.expectedZeroRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedSuccLhs lhs' ∧
      c.TrExprS r.expectedSuccRhs rhs' ∧ c.IsDefEqU lhs' rhs')

theorem NatGcdFixCertificate.Valid.normalize {c : VContext}
    {r : NatGcdFixCertificate} {gcd : Expr} (hv : r.Valid c)
    (hs : r.shape gcd = true) : r.NormalizedValid c gcd := by
  rcases hv with ⟨hcore, htop, hzero, hsucc⟩
  rcases htop with ⟨tl, tr, htl, htr, hteq⟩
  rcases hzero with ⟨zl, zr, hzl, hzr, hzeq⟩
  rcases hsucc with ⟨sl, sr, hsl, hsr, hseq⟩
  simp only [NatGcdFixCertificate.shape, Bool.and_eq_true] at hs
  rcases hs with ⟨⟨⟨⟨⟨htls, htrs⟩, hzls⟩, hzrs⟩, hsls⟩, hsrs⟩
  refine ⟨hcore, ⟨tl, tr, ?_, ?_, hteq⟩,
    ⟨zl, zr, ?_, ?_, hzeq⟩, ⟨sl, sr, ?_, ?_, hseq⟩⟩
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound htls) htl
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound htrs) htr
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hzls) hzl
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hzrs) hzr
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hsls) hsl
  · exact TrExprS.of_exprShapeEq (exprShapeEq_sound hsrs) hsr

theorem NatGcdFixCertificate.NormalizedValid.reflects
    {c : TypeChecker.VContext} {r : NatGcdFixCertificate} {gcd : Expr} {f : VExpr}
    (hv : r.NormalizedValid c gcd)
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (hmodC : c.venv.contains ``Nat.mod)
    (hmod : c.venv.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hgcd : TrExprS c.venv [] [] gcd f)
    (hf : ∀ U Γ, c.venv.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : c.venv.IsDefEqU 0 [] (.const ``Nat.gcd []) f) :
    c.venv.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by
  rcases hv with ⟨hcore, htop, hzero, hsucc⟩
  rcases hcore.normalizeAux with ⟨heager, htrue, _hfalse⟩
  rcases heager with ⟨el, er, hel, her, heeq⟩
  rcases htrue with ⟨tl, tr, htl, htr, hteq⟩
  rcases htop with ⟨topL, topR, htopL, htopR, htopEq⟩
  rcases hzero with ⟨zeroL, zeroR, hzeroL, hzeroR, hzeroEq⟩
  rcases hsucc with ⟨succL, succR, hsuccL, hsuccR, hsuccEq⟩
  change TrExprS c.venv c.lparams c.vlctx r.core.expectedEagerLhs el at hel
  change TrExprS c.venv c.lparams c.vlctx r.core.expectedEagerRhs er at her
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx el er at heeq
  change TrExprS c.venv c.lparams c.vlctx r.core.expectedBoolTrueLhs tl at htl
  change TrExprS c.venv c.lparams c.vlctx r.core.expectedBoolTrueRhs tr at htr
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx tl tr at hteq
  change TrExprS c.venv c.lparams c.vlctx (r.expectedTopLhs gcd) topL at htopL
  change TrExprS c.venv c.lparams c.vlctx r.expectedTopRhs topR at htopR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx topL topR at htopEq
  change TrExprS c.venv c.lparams c.vlctx r.expectedZeroLhs zeroL at hzeroL
  change TrExprS c.venv c.lparams c.vlctx r.expectedZeroRhs zeroR at hzeroR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx zeroL zeroR at hzeroEq
  change TrExprS c.venv c.lparams c.vlctx r.expectedSuccLhs succL at hsuccL
  change TrExprS c.venv c.lparams c.vlctx r.expectedSuccRhs succR at hsuccR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx succL succR at hsuccEq
  rw [hlparams, hvlctx] at hel her heeq htl htr hteq htopL htopR htopEq hzeroL hzeroR hzeroEq hsuccL hsuccR hsuccEq
  have hprim := c.hasPrimitives
  have wf := c.Ewf
  have heager' (n) := VEnv.eager_natLit_of_aux_equations wf hprim hnat
    hbeqC hel her heeq htl htr hteq (n := n)
  have heagerCanon (n) : ∃ eager,
      TrExprS c.venv [] [] q(WellFounded.Nat.eager) eager ∧
      c.venv.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
    simpa [hcore.eagerFn_eq, Expr.instantiate1'] using heager' n
  have hfValue := (hcf.of_l wf trivial (hf 0 [])).hasType.2
  have htop' := NatGcdFixCertificate.top_semantics wf hprim hnat
    hcore.goFn_closed htopL htopR htopEq hgcd hfValue heagerCanon
  have hzero' := NatGcdFixCertificate.zero_semantics wf hprim hnat
    hzeroL hzeroR hzeroEq
  have hsucc' := NatGcdFixCertificate.succ_semantics wf hprim hnat
    hmodC hmod hsuccL hsuccR hsuccEq
  have hzeroT (Γ) : c.venv.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2.weak0 wf
  have hsuccT (Γ) : c.venv.HasType 0 Γ .natSucc
      (.forallE .nat .nat) :=
    (TrExprS.natSucc hprim hnat (Us := []) (Δ := [])).2.weak0 wf
  apply VEnv.ReflectsNatNatNat.of_gcd_fix_relation wf hzeroT hsuccT
    hf hcf (VEnv.GcdGoCall c.venv r) htop'
  intro fuel a b e hG he
  by_cases ha : a = 0
  · subst a
    simpa using hzero' fuel b e hG he
  · cases a with
    | zero => contradiction
    | succ a =>
      simpa using hsucc' fuel a b e hG he

theorem checkNatGcdFixCertificate.WF {c : VContext} {s : VState}
    {core : NatWellFoundedCoreResult} {gcd : Expr} {fail : ∀ {α}, M α} :
    M.WF c s (checkNatGcdFixCertificate core gcd fail) fun out _ =>
      out.Valid c ∧ out.shape gcd = true := by
  simp only [checkNatGcdFixCertificate]
  refine M.WF.sandbox.bind fun cert _ _ _ => ?_
  split
  · rename_i hshape
    simp only [pure_bind]
    exact checkNatWellFoundedCertificate.WF.bind fun _ _ _ hcore =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ htop =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hzero =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hsucc =>
        .pure ⟨⟨hcore, htop, hzero, hsucc⟩, hshape⟩
  · exact .throw

def NatBitwiseFixCertificate.Valid
    (c : VContext) (r : NatBitwiseFixCertificate) : Prop :=
  r.core.Valid c ∧
    (∃ lhs' rhs', c.TrExprS r.topLhs lhs' ∧ c.TrExprS r.topRhs rhs' ∧
      c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.zeroLhs lhs' ∧ c.TrExprS r.zeroRhs rhs' ∧
      c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.zeroRightLhs lhs' ∧
      c.TrExprS r.zeroRightRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.succLhs lhs' ∧ c.TrExprS r.succRhs rhs' ∧
      c.IsDefEqU lhs' rhs') ∧
    ∃ goV A, c.TrExprS r.callFn goV ∧ c.HasType goV A

def NatBitwiseFixCertificate.NormalizedValid
    (c : VContext) (r : NatBitwiseFixCertificate) (bitwise : Expr) : Prop :=
  r.core.Valid c ∧
    (∃ lhs' rhs', c.TrExprS (r.expectedTopLhs bitwise) lhs' ∧
      c.TrExprS r.expectedTopRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedZeroLhs lhs' ∧
      c.TrExprS r.expectedZeroRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedZeroRightLhs lhs' ∧
      c.TrExprS r.expectedZeroRightRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    (∃ lhs' rhs', c.TrExprS r.expectedSuccLhs lhs' ∧
      c.TrExprS r.expectedSuccRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
    ∃ goV A, c.TrExprS r.callFn goV ∧ c.HasType goV A

theorem NatBitwiseFixCertificate.Valid.normalize {c : VContext}
    {r : NatBitwiseFixCertificate} {bitwise : Expr} (hv : r.Valid c)
    (hs : r.shape bitwise = true) : r.NormalizedValid c bitwise := by
  rcases hv with ⟨hcore, htop, hzero, hzeroRight, hsucc, hgo⟩
  rcases htop with ⟨tl, tr, htl, htr, hteq⟩
  rcases hzero with ⟨zl, zr, hzl, hzr, hzeq⟩
  rcases hzeroRight with ⟨zrl, zrr, hzrl, hzrr, hzreq⟩
  rcases hsucc with ⟨sl, sr, hsl, hsr, hseq⟩
  simp only [NatBitwiseFixCertificate.shape, Bool.and_eq_true] at hs
  rcases hs with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨htls, htrs⟩, hzls⟩, hzrs⟩, hzrls⟩, hzrrs⟩,
      hsls⟩, hsrs⟩, _hnoFVar⟩, _hnoMVar⟩
  exact ⟨hcore,
    ⟨tl, tr, TrExprS.of_exprShapeEq (exprShapeEq_sound htls) htl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound htrs) htr, hteq⟩,
    ⟨zl, zr, TrExprS.of_exprShapeEq (exprShapeEq_sound hzls) hzl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hzrs) hzr, hzeq⟩,
    ⟨zrl, zrr, TrExprS.of_exprShapeEq (exprShapeEq_sound hzrls) hzrl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hzrrs) hzrr, hzreq⟩,
    ⟨sl, sr, TrExprS.of_exprShapeEq (exprShapeEq_sound hsls) hsl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hsrs) hsr, hseq⟩, hgo⟩

theorem checkNatBitwiseFixCertificate.WF {c : VContext} {s : VState}
    {core : NatWellFoundedCoreResult} {bitwise : Expr}
    {fail : ∀ {α}, M α} :
    M.WF c s (checkNatBitwiseFixCertificate core bitwise fail) fun out _ =>
      out.Valid c ∧ out.shape bitwise = true := by
  simp only [checkNatBitwiseFixCertificate]
  refine M.WF.sandbox.bind fun cert _ _ _ => ?_
  split
  · rename_i hshape
    simp only [pure_bind]
    have hflags := hshape
    simp only [NatBitwiseFixCertificate.shape, Bool.and_eq_true] at hflags
    have hnoFVar : cert.callFn.hasFVar = false := by
      simpa using hflags.1.2
    have hnoMVar : cert.callFn.hasMVar = false := by
      simpa using hflags.2
    have hgoFVars : cert.callFn.FVarsIn (· ∈ c.vlctx.fvars) := by
      apply fvarsIn_iff.mpr
      refine ⟨?_, fvarsIn_iff_hasMVar.mpr hnoMVar⟩
      intro fv hmem
      rw [fvarsList_eq_nil.mpr hnoFVar] at hmem
      contradiction
    exact (checkType.WF hgoFVars).bind fun _ _ _ hgo =>
      checkNatWellFoundedCertificate.WF.bind fun _ _ _ hcore =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ htop =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hzero =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hzeroRight =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hsucc =>
        let ⟨goV, A, _, hgoS, _, hgoT⟩ := hgo
        .pure ⟨⟨hcore, htop, hzero, hzeroRight, hsucc,
          ⟨goV, A, hgoS, hgoT⟩⟩, hshape⟩
  · exact .throw

theorem unfoldNatWellFoundedCert.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fvs : Array Expr} {fail : ∀ {α}, M α}
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s (unfoldNatWellFoundedCert e fvs eq_def fail) fun out _ =>
      out.equation == equation ∧ out.Valid c := by
  simp only [unfoldNatWellFoundedCert, heq]
  refine M.WF.sandbox.bind fun cert _ _ _ => ?_
  split
  · rename_i hequation
    simp only [pure_bind]
    exact checkNatWellFoundedCertificate.WF.bind fun _ _ _ hvalid =>
      .pure ⟨hequation, hvalid⟩
  · exact .throw

theorem unfoldNatWellFoundedNat2Cert.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fail : ∀ {α}, M α}
    (hnat : c.TrExprS q(Nat) .nat) (hnatTy : c.IsType .nat)
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s (unfoldNatWellFoundedNat2Cert e eq_def fail) fun out _ =>
      out.equation == equation ∧ out.Valid c := by
  simp only [unfoldNatWellFoundedNat2Cert, heq]
  have hraw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl `m .default q(Nat) fun m =>
        withLocalDecl `n .default q(Nat) fun n =>
          M.sandbox (unfoldNatWellFoundedCore e #[m, n] eq_def fail))
      (fun _ _ => True) := by
    refine .withLocalDecl hnat hnatTy .rfl fun m cwf₁ s₁ hs₁ hres₁ => ?_
    let c₁ := c.withMLC (.vlam m `m q(Nat) .nat .default c.mlctx) (wf := cwf₁)
    have hnat₁ : c₁.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₁ : c₁.IsType .nat :=
      hnatTy.weakN c.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₁ hnatTy₁ .rfl fun n cwf₂ s₂ hs₂ hres₂ => ?_
    exact M.WF.sandbox.mono fun _ _ _ _ => trivial
  have hraw' : M.WF c s
      (withLocalDecl `m .default q(Nat) fun m =>
        withLocalDecl `n .default q(Nat) fun n =>
          M.sandbox (unfoldNatWellFoundedCore e #[m, n] eq_def fail))
      (fun _ _ => True) := by simpa using hraw
  refine hraw'.bind fun cert _ _ _ => ?_
  split
  · rename_i hequation
    simp only [pure_bind]
    exact checkNatWellFoundedCertificate.WF.bind fun _ _ _ hvalid =>
      .pure ⟨hequation, hvalid⟩
  · exact .throw

theorem unfoldNatWellFoundedBoolNat2Cert.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fail : ∀ {α}, M α}
    (hfun : c.TrExprS q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool))
    (hfunTy : c.IsType (.forallE .bool <| .forallE .bool .bool))
    (hnat : c.TrExprS q(Nat) .nat) (hnatTy : c.IsType .nat)
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s (unfoldNatWellFoundedBoolNat2Cert e eq_def fail) fun out _ =>
      out.equation == equation ∧ out.Valid c := by
  simp only [unfoldNatWellFoundedBoolNat2Cert, heq]
  have hraw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
        withLocalDecl `n .default q(Nat) fun n =>
          withLocalDecl `m .default q(Nat) fun m =>
            M.sandbox (unfoldNatWellFoundedCore e #[f, n, m] eq_def fail))
      (fun _ _ => True) := by
    refine .withLocalDecl hfun hfunTy .rfl fun f cwf₁ s₁ hs₁ hres₁ => ?_
    let c₁ := c.withMLC
      (.vlam f `f q(Bool → Bool → Bool)
        (.forallE .bool <| .forallE .bool .bool) .default c.mlctx) (wf := cwf₁)
    have hnat₁ : c₁.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₁ : c₁.IsType .nat :=
      hnatTy.weakN c.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₁ hnatTy₁ .rfl fun n cwf₂ s₂ hs₂ hres₂ => ?_
    let c₂ := c.withMLC
      (.vlam n `n q(Nat) .nat .default
        (.vlam f `f q(Bool → Bool → Bool)
          (.forallE .bool <| .forallE .bool .bool) .default c.mlctx)) (wf := cwf₂)
    have hnat₂ : c₂.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₂ : c₂.IsType .nat :=
      hnatTy₁.weakN c₁.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₂ hnatTy₂ .rfl fun m cwf₃ s₃ hs₃ hres₃ => ?_
    exact M.WF.sandbox.mono fun _ _ _ _ => trivial
  have hraw' : M.WF c s
      (withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
        withLocalDecl `n .default q(Nat) fun n =>
          withLocalDecl `m .default q(Nat) fun m =>
            M.sandbox (unfoldNatWellFoundedCore e #[f, n, m] eq_def fail))
      (fun _ _ => True) := by simpa using hraw
  refine hraw'.bind fun cert _ _ _ => ?_
  split
  · rename_i hequation
    simp only [pure_bind]
    exact checkNatWellFoundedCertificate.WF.bind fun _ _ _ hvalid =>
      .pure ⟨hequation, hvalid⟩
  · exact .throw

/-- The transactional well-founded-recursion validator has no verifier-state
proof obligation of its own.  Once the equation lambda reconstructed from
`eq_def` is known to translate, that is also the translation of the helper's
successful result. -/
theorem unfoldNatWellFounded.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fvs : Array Expr}
    {fail : ∀ {α}, M α} {out' : VExpr}
    (heq : natWellFoundedEquation e eq_def = some equation)
    (hout : c.TrExprS equation out') :
    M.WF c s (unfoldNatWellFounded e fvs eq_def fail) fun out _ =>
      c.TrExprS out out' := by
  simp only [unfoldNatWellFounded, heq]
  exact (unfoldNatWellFoundedCert.WF heq).bind fun _ _ _ _ => .pure hout

theorem unfoldNatWellFounded.fvarsIn.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fvs : Array Expr}
    {fail : ∀ {α}, M α}
    (heq : natWellFoundedEquation e eq_def = some equation)
    (hout : equation.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (unfoldNatWellFounded e fvs eq_def fail) fun out _ =>
      out.FVarsIn (· ∈ c.vlctx.fvars) := by
  simp only [unfoldNatWellFounded, heq]
  exact (unfoldNatWellFoundedCert.WF heq).bind fun _ _ _ _ => .pure hout

theorem unfoldNatWellFounded.eq.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fvs : Array Expr}
    {fail : ∀ {α}, M α}
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s (unfoldNatWellFounded e fvs eq_def fail) fun out _ =>
      out = equation := by
  simp only [unfoldNatWellFounded, heq]
  exact (unfoldNatWellFoundedCert.WF heq).bind fun _ _ _ _ => .pure rfl

theorem unfoldNatWellFounded.nat2.eq.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fail : ∀ {α}, M α}
    (hnat : c.TrExprS q(Nat) .nat) (hnatTy : c.IsType .nat)
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s
      (withLocalDecl `m .default q(Nat) fun m =>
        withLocalDecl `n .default q(Nat) fun n =>
          unfoldNatWellFounded e #[m, n] eq_def fail)
      fun out _ => out = equation := by
  have hw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl `m .default q(Nat) fun m =>
        withLocalDecl `n .default q(Nat) fun n =>
          unfoldNatWellFounded e #[m, n] eq_def fail)
      (fun out _ => out = equation) := by
    refine .withLocalDecl hnat hnatTy .rfl fun m cwf₁ s₁ hs₁ hres₁ => ?_
    let c₁ := c.withMLC (.vlam m `m q(Nat) .nat .default c.mlctx) (wf := cwf₁)
    have hnat₁ : c₁.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₁ : c₁.IsType .nat :=
      hnatTy.weakN c.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₁ hnatTy₁ .rfl fun n cwf₂ s₂ hs₂ hres₂ => ?_
    exact unfoldNatWellFounded.eq.WF heq
  simpa using hw

theorem unfoldNatWellFounded.boolNat2.eq.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fail : ∀ {α}, M α}
    (hfun : c.TrExprS q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool))
    (hfunTy : c.IsType (.forallE .bool <| .forallE .bool .bool))
    (hnat : c.TrExprS q(Nat) .nat) (hnatTy : c.IsType .nat)
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s
      (withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
        withLocalDecl `n .default q(Nat) fun n =>
          withLocalDecl `m .default q(Nat) fun m =>
            unfoldNatWellFounded e #[f, n, m] eq_def fail)
      fun out _ => out = equation := by
  have hw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
        withLocalDecl `n .default q(Nat) fun n =>
          withLocalDecl `m .default q(Nat) fun m =>
            unfoldNatWellFounded e #[f, n, m] eq_def fail)
      (fun out _ => out = equation) := by
    refine .withLocalDecl hfun hfunTy .rfl fun f cwf₁ s₁ hs₁ hres₁ => ?_
    let c₁ := c.withMLC
      (.vlam f `f q(Bool → Bool → Bool)
        (.forallE .bool <| .forallE .bool .bool) .default c.mlctx) (wf := cwf₁)
    have hnat₁ : c₁.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₁ : c₁.IsType .nat :=
      hnatTy.weakN c.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₁ hnatTy₁ .rfl fun n cwf₂ s₂ hs₂ hres₂ => ?_
    let c₂ := c.withMLC
      (.vlam n `n q(Nat) .nat .default
        (.vlam f `f q(Bool → Bool → Bool)
          (.forallE .bool <| .forallE .bool .bool) .default c.mlctx)) (wf := cwf₂)
    have hnat₂ : c₂.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₂ : c₂.IsType .nat :=
      hnatTy₁.weakN c₁.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₂ hnatTy₂ .rfl fun m cwf₃ s₃ hs₃ hres₃ => ?_
    exact unfoldNatWellFounded.eq.WF heq
  simpa using hw

theorem checkTypeIsDefEq.WF {c : VContext} {s : VState}
    (he : c.TrExprS e e') (he_unique : TrExprS.IsUnique e)
    (hA : c.TrExprS A A') :
    M.WF c s (do TypeChecker.isDefEq (← TypeChecker.checkType e) A) fun b _ =>
      b → c.HasType e' A' := by
  refine (checkType.WF he.fvarsIn).bind fun _ _ _ h => ?_
  let ⟨_, _, _, he', hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).mono fun _ _ _ hEq htrue => ?_
  cases he'.unique he_unique he
  exact VEnv.HasType.defeqU_r c.Ewf c.Δwf (hEq htrue) hhas

theorem checkTypeIsDefEqGuard.WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α}
    (he : c.TrExprS e e') (he_unique : TrExprS.IsUnique e)
    (hA : c.TrExprS A A')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (do unless ← TypeChecker.isDefEq (← TypeChecker.checkType e) A do fail)
      fun _ _ => c.HasType e' A' := by
  refine (checkType.WF he.fvarsIn).bind fun _ _ _ h => ?_
  let ⟨_, _, _, he'', hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).bind fun b s' _ hEq => ?_
  split
  · have hEq := hEq (by assumption)
    cases he''.unique he_unique he
    exact .pure (VEnv.HasType.defeqU_r c.Ewf c.Δwf hEq hhas)
  · exact (hfail (s' := s')).mono nofun

/-- Variant for dynamically synthesized expressions: free-variable safety is
enough to discover a translation with `checkType`; the following equality
guard then establishes its requested type. -/
theorem checkTypeIsDefEqGuard.fvarsIn.WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α}
    (he : e.FVarsIn (· ∈ c.vlctx.fvars)) (hA : c.TrExprS A A')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (do unless ← TypeChecker.isDefEq (← TypeChecker.checkType e) A do fail)
      fun _ _ => ∃ e', c.TrExprS e e' ∧ c.HasType e' A' := by
  refine (checkType.WF he).bind fun _ _ _ h => ?_
  let ⟨e', _, _, he', hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).bind fun b s' _ hEq => ?_
  split
  · exact .pure ⟨e', he', hhas.defeqU_r c.Ewf c.Δwf (hEq (by assumption))⟩
  · exact (hfail (s' := s')).mono nofun

theorem checkTypeIsDefEqGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he : c.TrExprS e e') (he_unique : TrExprS.IsUnique e)
    (hA : c.TrExprS A A')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', c.HasType e' A' → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isDefEq (← TypeChecker.checkType e) A do fail
      next) Q := by
  refine (checkType.WF he.fvarsIn).bind fun _ _ _ h => ?_
  let ⟨_, _, _, he'', hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).bind fun b s' _ hEq => ?_
  split
  · have hEq := hEq (by assumption)
    cases he''.unique he_unique he
    exact hnext s' (VEnv.HasType.defeqU_r c.Ewf c.Δwf hEq hhas)
  · exact (hfail (s' := s')).bind nofun

theorem isDefEqGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', c.IsDefEqU e₁' e₂' → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isDefEq e₁ e₂ do fail
      next) Q := by
  refine (isDefEq.WF he₁ he₂).bind fun b s' _ hEq => ?_
  split
  · exact hnext s' (hEq (by assumption))
  · exact (hfail (s' := s')).bind nofun

theorem isDefEqGuard.WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (do unless ← TypeChecker.isDefEq e₁ e₂ do fail)
      fun _ _ => c.IsDefEqU e₁' e₂' := by
  refine (isDefEq.WF he₁ he₂).bind fun b s' _ hEq => ?_
  split
  · exact .pure (hEq (by assumption))
  · exact (hfail (s' := s')).mono nofun

theorem inferTypeIsDefEqGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he : c.TrExprS e e') (hA : c.TrExprS A A')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', c.HasType e' A' → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isDefEq (← TypeChecker.inferType e) A do fail
      next) Q := by
  refine (inferType.WF he).bind fun _ _ _ h => ?_
  let ⟨_, _, _, hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).bind fun b s' _ hEq => ?_
  split
  · exact hnext s' (hhas.defeqU_r c.Ewf c.Δwf (hEq (by assumption)))
  · exact (hfail (s' := s')).bind nofun

theorem checkTypeDiscard.bind_WF {c : VContext} {s : VState}
    {next : M β} {Q : β → VState → Prop}
    (he : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hnext : ∀ s', M.WF c s' next Q) :
    M.WF c s (do _ ← TypeChecker.checkType e; next) Q :=
  (checkType.WF he).bind fun _ s' _ _ => hnext s'

theorem inferTypeIsPropGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he : c.TrExprS e e')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s',
      (∃ ty', c.HasType e' ty' ∧ c.HasType ty' (.sort .zero)) → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isProp (← TypeChecker.inferType e) do fail
      next) Q := by
  refine (inferType.WF he).bind fun _ _ _ h => ?_
  let ⟨ty', _, _, hty, hhas⟩ := h
  refine (isProp.WF hty).bind fun b s' _ hprop => ?_
  split
  · exact hnext s' ⟨ty', hhas, hprop (by assumption)⟩
  · exact (hfail (s' := s')).bind nofun

theorem Reflection.check.WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hr : c.TrExprS r.type rtype) (hr_unique : TrExprS.IsUnique r.type)
    (hcanon : c.TrExprS q(Prop → Bool → Prop) canon)
    (hfail : ∀ {α} {s'}, s ≤ s' →
      M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.check fail) fun _ _ => c.HasType rtype canon := by
  simp only [Reflection.check]
  refine (checkType.WF hr.fvarsIn).bind fun _ _ le₁ h => ?_
  let ⟨_, _, _, hr', hty, hhas⟩ := h
  refine (isDefEq.WF hty hcanon).bind fun b s' le₂ hEq => ?_
  split
  · have hEq := hEq (by assumption)
    cases hr'.unique hr_unique hr
    exact .pure (VEnv.HasType.defeqU_r c.Ewf c.Δwf hEq hhas)
  · exact (hfail (le₁.trans le₂)).mono nofun

theorem Reflection.check.bind_WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α} {next : M β} {Q}
    (hr : c.TrExprS r.type rtype) (hr_unique : TrExprS.IsUnique r.type)
    (hcanon : c.TrExprS q(Prop → Bool → Prop) canon)
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', M.WF c s' next Q) :
    M.WF c s (do r.check fail; next) Q := by
  exact (Reflection.check.WF hr hr_unique hcanon (fun _ => hfail)).bind
    fun _ s' _ _ => hnext s'

theorem Reflection.checkITE.WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hite : c.TrExprS r.ite ite') (hite_unique : TrExprS.IsUnique r.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) falseR')
    (hfail : ∀ {α} {s'}, s ≤ s' →
      M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.checkITE fail) fun _ _ =>
      c.HasType ite' iteTy' ∧ c.IsDefEqU trueL' trueR' ∧
        c.IsDefEqU falseL' falseR' := by
  simp only [Reflection.checkITE, pure_bind]
  refine (checkType.WF hite.fvarsIn).bind fun _ _ le₁ h => ?_
  let ⟨_, _, _, hite'', hty, hhas⟩ := h
  refine (isDefEq.WF hty hiteTy).bind fun b _ le₂ htyEq => ?_
  split
  · have htyEq := htyEq (by assumption)
    cases hite''.unique hite_unique hite
    have hiteHas := VEnv.HasType.defeqU_r c.Ewf c.Δwf htyEq hhas
    exact (isDefEq.WF htrueL htrueR).bind fun b _ le₃ htrueEq => by
      split
      · have htrueEq := htrueEq (by assumption)
        exact (isDefEq.WF hfalseL hfalseR).bind fun b _ le₄ hfalseEq => by
          split
          · exact .pure ⟨hiteHas, htrueEq, hfalseEq (by assumption)⟩
          · exact (hfail (((le₁.trans le₂).trans le₃).trans le₄)).mono nofun
      · exact (hfail ((le₁.trans le₂).trans le₃)).bind nofun
  · exact (hfail (le₁.trans le₂)).bind nofun

theorem Reflection.checkITE.bind_WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α} {next : M β} {Q}
    (hite : c.TrExprS r.ite ite') (hite_unique : TrExprS.IsUnique r.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s',
      (c.HasType ite' iteTy' ∧ c.IsDefEqU trueL' trueR' ∧
        c.IsDefEqU falseL' falseR') → M.WF c s' next Q) :
    M.WF c s (do _ ← r.checkITE fail; next) Q := by
  exact (Reflection.checkITE.WF hite hite_unique hiteTy htrueL htrueR
    hfalseL hfalseR (fun _ => hfail)).bind fun _ s' _ h => hnext s' h

theorem Reflection.checkNatDITE.WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hnot : c.TrExprS q(Not) not') (hnot_unique : TrExprS.IsUnique q(Not))
    (hnotTy : c.TrExprS q(Prop → Prop) notTy')
    (hdite : c.TrExprS r.natDITE dite') (hdite_unique : TrExprS.IsUnique r.natDITE)
    (hditeTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
      .arrow (.arrow (.bvar 2) q(Nat)) <|
      .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy')
    (hofTrue : c.TrExprS r.ofTrue ofTrue')
    (hofTrue_unique : TrExprS.IsUnique r.ofTrue)
    (hofTrueTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) ofTrueTy')
    (hofFalse : c.TrExprS r.ofFalse ofFalse')
    (hofFalse_unique : TrExprS.IsUnique r.ofFalse)
    (hofFalseTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) ofFalseTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.checkNatDITE fail) fun _ _ =>
      c.IsDefEqU trueL' trueR' ∧ c.IsDefEqU falseL' falseR' := by
  simp only [Reflection.checkNatDITE, pure_bind]
  refine checkTypeIsDefEqGuard.bind_WF hnot hnot_unique hnotTy hfail fun _ _ => ?_
  refine checkTypeIsDefEqGuard.bind_WF hdite hdite_unique hditeTy hfail fun _ _ => ?_
  refine checkTypeIsDefEqGuard.bind_WF hofTrue hofTrue_unique hofTrueTy hfail fun _ _ => ?_
  refine checkTypeIsDefEqGuard.bind_WF hofFalse hofFalse_unique hofFalseTy hfail fun _ _ => ?_
  refine isDefEqGuard.bind_WF htrueL htrueR hfail fun _ htrueEq => ?_
  exact (isDefEqGuard.WF hfalseL hfalseR hfail).mono fun _ _ _ hfalseEq =>
    ⟨htrueEq, hfalseEq⟩

theorem Reflection.checkNatDITE.bind_WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α} {next : M β} {Q}
    (hnot : c.TrExprS q(Not) not') (hnot_unique : TrExprS.IsUnique q(Not))
    (hnotTy : c.TrExprS q(Prop → Prop) notTy')
    (hdite : c.TrExprS r.natDITE dite') (hdite_unique : TrExprS.IsUnique r.natDITE)
    (hditeTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
      .arrow (.arrow (.bvar 2) q(Nat)) <|
      .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy')
    (hofTrue : c.TrExprS r.ofTrue ofTrue')
    (hofTrue_unique : TrExprS.IsUnique r.ofTrue)
    (hofTrueTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) ofTrueTy')
    (hofFalse : c.TrExprS r.ofFalse ofFalse')
    (hofFalse_unique : TrExprS.IsUnique r.ofFalse)
    (hofFalseTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) ofFalseTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s',
      (c.IsDefEqU trueL' trueR' ∧ c.IsDefEqU falseL' falseR') →
        M.WF c s' next Q) :
    M.WF c s (do _ ← r.checkNatDITE fail; next) Q := by
  exact (Reflection.checkNatDITE.WF hnot hnot_unique hnotTy hdite hdite_unique
    hditeTy hofTrue hofTrue_unique hofTrueTy hofFalse hofFalse_unique hofFalseTy
    htrueL htrueR hfalseL hfalseR hfail).bind fun _ s' _ h => hnext s' h

theorem Condition.check.reflectNatNat_ite.WF {c : VContext} {s : VState}
    {cond : Condition} {asBool : Expr} {reflect : Reflection} {proof : Expr}
    {fail : ∀ {α}, M α} {Rite : Prop}
    (himpl : cond.impl = .reflectNatNat asBool reflect proof)
    (hdec : c.TrExprS cond.dec dec')
    (hprop : c.TrExprS cond.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hreflect : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', M.WF c s'' next Q) →
      M.WF c s' (do reflect.check fail; next) Q)
    (hcheckITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkITE fail; next) Q)
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)) decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS asBool asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS proof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (cond.check fail (ite := true)) fun _ _ =>
      Rite ∧ c.IsDefEqU e' dec' := by
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine hreflect fun _ => ?_
  refine hcheckITE fun _ hite => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hdecide hdecideTy hfail fun _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hasBool hasBoolTy hfail fun _ _ => ?_
  refine inferTypeIsPropGuard.bind_WF hproof hfail fun _ _ => ?_
  exact (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq => ⟨hite, heq⟩

theorem Condition.check.reflectNatNat_dite.WF {c : VContext} {s : VState}
    {cond : Condition} {asBool : Expr} {reflect : Reflection} {proof : Expr}
    {fail : ∀ {α}, M α} {Rdite : Prop}
    (himpl : cond.impl = .reflectNatNat asBool reflect proof)
    (hdec : c.TrExprS cond.dec dec')
    (hprop : c.TrExprS cond.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hreflect : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', M.WF c s'' next Q) →
      M.WF c s' (do reflect.check fail; next) Q)
    (hcheckDITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rdite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkNatDITE fail; next) Q)
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)) decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS asBool asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS proof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (cond.check fail (dite := true)) fun _ _ =>
      Rdite ∧ c.IsDefEqU e' dec' := by
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine hreflect fun _ => ?_
  refine hcheckDITE fun _ hdite => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hdecide hdecideTy hfail fun _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hasBool hasBoolTy hfail fun _ _ => ?_
  refine inferTypeIsPropGuard.bind_WF hproof hfail fun _ _ => ?_
  exact (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq => ⟨hdite, heq⟩

theorem Condition.check.reflectNatNat_ite_dite.WF {c : VContext} {s : VState}
    {cond : Condition} {asBool : Expr} {reflect : Reflection} {proof : Expr}
    {fail : ∀ {α}, M α} {Rite Rdite : Prop}
    (himpl : cond.impl = .reflectNatNat asBool reflect proof)
    (hdec : c.TrExprS cond.dec dec')
    (hprop : c.TrExprS cond.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hreflect : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', M.WF c s'' next Q) →
      M.WF c s' (do reflect.check fail; next) Q)
    (hcheckITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkITE fail; next) Q)
    (hcheckDITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rdite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkNatDITE fail; next) Q)
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)) decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS asBool asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS proof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (cond.check fail (ite := true) (dite := true)) fun _ _ =>
      Rite ∧ Rdite ∧ c.IsDefEqU e' dec' := by
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine hreflect fun _ => ?_
  refine hcheckITE fun _ hite => ?_
  refine hcheckDITE fun _ hdite => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hdecide hdecideTy hfail fun _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hasBool hasBoolTy hfail fun _ _ => ?_
  refine inferTypeIsPropGuard.bind_WF hproof hfail fun _ _ => ?_
  exact (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq => ⟨hite, hdite, heq⟩

theorem Condition.bool.check.WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α}
    (hdec : c.TrExprS Condition.bool.dec dec')
    (hprop : c.TrExprS Condition.bool.prop prop')
    (hpropTy : c.TrExprS q(Bool → Prop) propTy')
    (hnatITE : c.TrExprS Condition.bool.boolNatITE natITE')
    (hnatITE_unique : TrExprS.IsUnique Condition.bool.boolNatITE)
    (hnatITETy : c.TrExprS q(Bool → Nat → Nat → Nat) natITETy')
    (htrueL : c.TrExprS
      (mkApp Condition.bool.boolNatITE q(true)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (mkApp Condition.bool.boolNatITE q(false)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (Condition.bool.check fail (ite := true)) fun _ _ =>
      c.HasType natITE' natITETy' ∧
      c.IsDefEqU trueL' trueR' ∧ c.IsDefEqU falseL' falseR' := by
  simp [Condition.check, Condition.bool, Condition.boolNatITE]
  refine (checkType.WF hdec.fvarsIn).bind fun _ _ _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine checkTypeIsDefEqGuard.bind_WF hnatITE hnatITE_unique hnatITETy hfail fun _ hnatITEHas => ?_
  refine isDefEqGuard.bind_WF htrueL htrueR hfail fun _ htrueEq => ?_
  exact (isDefEqGuard.WF hfalseL hfalseR hfail).mono fun _ _ _ hfalseEq =>
    ⟨hnatITEHas, htrueEq, hfalseEq⟩

theorem checkPrimitiveDef.charOfNat.WF {c : VContext} {s : VState}
    (hname : v.name = ``Char.ofNat) (hty : c.TrExprS v.type ty')
    (hchar : c.TrExprS q(Char) .char)
    (hcanon : c.TrExprS q(Nat → Char) (.forallE .nat .char)) :
    M.WF c s (checkPrimitiveDef v) fun b _ =>
      b → v.levelParams = [] ∧ c.IsDefEqU ty' (.forallE .nat .char) := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (ensureType.WF hchar).bind fun _ _ _ _ =>
      (isDefEq.WF hty hcanon).bind fun b _ _ hb => by
        split
        · exact .pure fun _ => ⟨hlparams, hb (by assumption)⟩
        · exact .throw
  · exact .throw

theorem checkPrimitiveDef.stringOfList.WF {c : VContext} {s : VState}
    (hname : v.name = ``String.ofList) (hty : c.TrExprS v.type ty')
    (hchar : c.TrExprS q(Char) .char)
    (hlistChar : c.TrExprS q(List Char) .listChar)
    (hnil : c.TrExprS q(List.nil (α := Char)) .listCharNil)
    (hcons : c.TrExprS q(List.cons (α := Char)) .listCharCons)
    (hconsTy : c.TrExprS q(Char → List Char → List Char)
      (.forallE .char <| .forallE .listChar .listChar))
    (hcanon : c.TrExprS q(List Char → String) (.forallE .listChar .string)) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .listChar .string) ∧
      c.HasType .listCharNil .listChar ∧
      c.HasType .listCharCons
        (.forallE .char <| .forallE .listChar .listChar) := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hparams
    have hlparams : v.levelParams = [] := by simpa using hparams
    simp only [pure_bind]
    exact (ensureType.WF hchar).bind fun _ _ _ _ =>
      (ensureType.WF hlistChar).bind fun _ _ _ _ =>
      by
      rw [← bind_assoc]
      exact (checkTypeIsDefEq.WF hnil (by trivial) hlistChar).bind fun b _ _ hb => by
        split
        · have hnilTy := hb (by assumption)
          rw [← bind_assoc]
          exact (checkTypeIsDefEq.WF hcons (by trivial) hconsTy).bind fun b _ _ hb => by
            split
            · have hconsTy' := hb (by assumption)
              exact (isDefEq.WF hty hcanon).bind fun b _ _ hb => by
                split
                · exact .pure fun _ =>
                    ⟨hlparams, hb (by assumption), hnilTy, hconsTy'⟩
                · exact .throw
            · exact .throw
        · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natAdd.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.add) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (.bvar 0) q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 1) (mkApp q(Nat.succ) (.bvar 0))) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp q(Nat.succ) (mkApp2 v.value (.bvar 1) (.bvar 0))) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ =>
                  ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natPred.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.pred) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat) (.forallE .nat .nat))
    (hz₁ : c.TrExprS (mkApp v.value q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS q(Nat.zero) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp v.value (mkApp q(Nat.succ) (.bvar 0))) s₁)
    (hs₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧ c.IsDefEqU ty' (.forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ => ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natSub.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.sub) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (.bvar 0) q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 1) (mkApp q(Nat.succ) (.bvar 0))) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp q(Nat.pred) (mkApp2 v.value (.bvar 1) (.bvar 0))) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ => ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natMul.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.mul) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (.bvar 0) q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) q(Nat.zero)) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 1) (mkApp q(Nat.succ) (.bvar 0))) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 q(Nat.add) (mkApp2 v.value (.bvar 1) (.bvar 0)) (.bvar 1)) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ => ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natPow.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.pow) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (.bvar 0) q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) q(Nat.succ Nat.zero)) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 1) (mkApp q(Nat.succ) (.bvar 0))) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 q(Nat.mul) (mkApp2 v.value (.bvar 1) (.bvar 0)) (.bvar 1)) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ => ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natGcd.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.gcd) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (heq : natWellFoundedEquation v.value q(type_of% Nat.gcd.eq_def) =
      some equation)
    (hequation : c.TrExprS equation equation')
    (hequnique : TrExprS.IsUnique equation)
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 equation q(Nat.zero) (.bvar 0)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 equation (mkApp q(Nat.succ) (.bvar 1)) (.bvar 0)) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value
          (mkApp2 q(Nat.mod) (.bvar 0) (mkApp q(Nat.succ) (.bvar 1)))
          (mkApp q(Nat.succ) (.bvar 1))) s₂)
    (hvz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value q(Nat.zero) (.bvar 0)) vz₁) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ ∧
      c.IsDefEqU vz₁ z₂ ∧ ∃ cert : NatGcdFixCertificate,
        cert.Valid c ∧ cert.shape v.value = true := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        let .forallE hnatTy _ hnat _ := hcanon
        exact (unfoldNatWellFoundedNat2Cert.WF hnat hnatTy heq).bind
          fun core _ _ hcore =>
          checkNatGcdFixCertificate.WF.bind fun gcdCert _ _ hgcd => by
          simp only [heq]
          exact (checkType.WF hequation.fvarsIn).bind fun _ _ _ h => by
            let ⟨_, _, _, hequation', hequationTy, hequationHas⟩ := h
            cases hequation'.unique hequnique hequation
            exact (isDefEq.WF hequationTy hcanon).bind fun b _ _ hequationTyEq => by
              split
              · have hequationTyEq := hequationTyEq (by assumption)
                exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
                  split
                  · have hzEq := hzEq (by assumption)
                    exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
                      split
                      · have hsEq := hsEq (by assumption)
                        obtain ⟨A, e, rfl⟩ : ∃ A e, vz₁ = .lam A e := by
                          cases hvz₁
                          exact ⟨_, _, rfl⟩
                        exact (reduceNatWellFoundedLam1.WF hvz₁).bind
                          fun _ _ _ hred => by
                          let ⟨_, hredS, hredEq⟩ := hred
                          exact (isDefEq.WF hredS hz₂).bind fun b _ _ hvzEq => by
                            split
                            · have hvzEq := hredEq.symm.trans c.Ewf c.Δwf
                                  (hvzEq (by assumption))
                              exact .pure fun _ =>
                                ⟨hlparams, htyEq, hzEq, hsEq, hvzEq,
                                  gcdCert, hgcd⟩
                            · exact .throw
                      · exact .throw
                  · exact .throw
              · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natBEq.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.beq) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool))
    (h00₁ : c.TrExprS (mkApp2 v.value q(Nat.zero) q(Nat.zero)) e00₁)
    (h00₂ : c.TrExprS q(true) e00₂)
    (h0s₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value q(Nat.zero) (mkApp q(Nat.succ) (.bvar 0))) e0s₁)
    (h0s₂ : c.TrExprS (.lam0 q(Nat) q(false)) e0s₂)
    (hs0₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (mkApp q(Nat.succ) (.bvar 0)) q(Nat.zero)) es0₁)
    (hs0₂ : c.TrExprS (.lam0 q(Nat) q(false)) es0₂)
    (hss₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (mkApp q(Nat.succ) (.bvar 1))
          (mkApp q(Nat.succ) (.bvar 0))) ess₁)
    (hss₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 1) (.bvar 0)) ess₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .bool) ∧
      c.IsDefEqU e00₁ e00₂ ∧ c.IsDefEqU e0s₁ e0s₂ ∧
      c.IsDefEqU es0₁ es0₂ ∧ c.IsDefEqU ess₁ ess₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF h00₁ h00₂).bind fun b _ _ h00Eq => by
          split
          · have h00Eq := h00Eq (by assumption)
            exact (isDefEq.WF h0s₁ h0s₂).bind fun b _ _ h0sEq => by
              split
              · have h0sEq := h0sEq (by assumption)
                exact (isDefEq.WF hs0₁ hs0₂).bind fun b _ _ hs0Eq => by
                  split
                  · have hs0Eq := hs0Eq (by assumption)
                    exact (isDefEq.WF hss₁ hss₂).bind fun b _ _ hssEq => by
                      split
                      · exact .pure fun _ =>
                          ⟨hlparams, htyEq, h00Eq, h0sEq, hs0Eq, hssEq (by assumption)⟩
                      · exact .throw
                  · exact .throw
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natBLE.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.ble) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool))
    (h00₁ : c.TrExprS (mkApp2 v.value q(Nat.zero) q(Nat.zero)) e00₁)
    (h00₂ : c.TrExprS q(true) e00₂)
    (h0s₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value q(Nat.zero) (mkApp q(Nat.succ) (.bvar 0))) e0s₁)
    (h0s₂ : c.TrExprS (.lam0 q(Nat) q(true)) e0s₂)
    (hs0₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (mkApp q(Nat.succ) (.bvar 0)) q(Nat.zero)) es0₁)
    (hs0₂ : c.TrExprS (.lam0 q(Nat) q(false)) es0₂)
    (hss₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (mkApp q(Nat.succ) (.bvar 1))
          (mkApp q(Nat.succ) (.bvar 0))) ess₁)
    (hss₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 1) (.bvar 0)) ess₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .bool) ∧
      c.IsDefEqU e00₁ e00₂ ∧ c.IsDefEqU e0s₁ e0s₂ ∧
      c.IsDefEqU es0₁ es0₂ ∧ c.IsDefEqU ess₁ ess₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF h00₁ h00₂).bind fun b _ _ h00Eq => by
          split
          · have h00Eq := h00Eq (by assumption)
            exact (isDefEq.WF h0s₁ h0s₂).bind fun b _ _ h0sEq => by
              split
              · have h0sEq := h0sEq (by assumption)
                exact (isDefEq.WF hs0₁ hs0₂).bind fun b _ _ hs0Eq => by
                  split
                  · have hs0Eq := hs0Eq (by assumption)
                    exact (isDefEq.WF hss₁ hss₂).bind fun b _ _ hssEq => by
                      split
                      · exact .pure fun _ =>
                          ⟨hlparams, htyEq, h00Eq, h0sEq, hs0Eq, hssEq (by assumption)⟩
                      · exact .throw
                  · exact .throw
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natBitwise.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.bitwise) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q((Bool → Bool → Bool) → Nat → Nat → Nat)
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat))
    (hfun : c.TrExprS q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool))
    (hfunTy : c.IsType (.forallE .bool <| .forallE .bool .bool))
    (hnat : c.TrExprS q(Nat) .nat) (hnatTy : c.IsType .nat)
    (heq : natWellFoundedEquation v.value q(type_of% Nat.bitwise.eq_def) =
      some equation)
    (hequation : c.TrExprS equation equation')
    (hequnique : TrExprS.IsUnique equation)
    (hbody : c.TrExprS (natBitwiseEquation v.value) body')
    (hz₁ : c.TrExprS (natBitwiseZeroEquation (natBitwiseEquation v.value)).1 z₁)
    (hz₂ : c.TrExprS (natBitwiseZeroEquation (natBitwiseEquation v.value)).2 z₂)
    (hzr₁ : c.TrExprS
      (natBitwiseZeroRightEquation (natBitwiseEquation v.value)).1 zr₁)
    (hzr₂ : c.TrExprS
      (natBitwiseZeroRightEquation (natBitwiseEquation v.value)).2 zr₂)
    (hs₁ : c.TrExprS
      (natBitwiseSuccEquation (natBitwiseEquation v.value) v.value).1 s₁)
    (hs₂ : c.TrExprS
      (natBitwiseSuccEquation (natBitwiseEquation v.value) v.value).2 s₂)
    (hvz₁ : c.TrExprS (natBitwiseZeroEquation v.value).1 vz₁)
    (hvz₂ : c.TrExprS (natBitwiseZeroEquation v.value).2 vz₂)
    (hnatCheck : ∀ {fail : ∀ {α}, M α} {s'},
      (∀ {α} {s''}, M.WF c s'' (fail : M α) fun _ _ => False) →
      M.WF c s' (Condition.natEq.check fail (ite := true)) fun _ _ => Rnat)
    (hboolCheck : ∀ {fail : ∀ {α}, M α} {s'},
      (∀ {α} {s''}, M.WF c s'' (fail : M α) fun _ _ => False) →
      M.WF c s' (Condition.bool.check fail (ite := true)) fun _ _ => Rbool) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty'
        (.forallE (.forallE .bool <| .forallE .bool .bool) <|
          .forallE .nat <| .forallE .nat .nat) ∧
      ∃ cert : NatBitwiseFixCertificate,
        cert.NormalizedValid c v.value ∧ Rnat ∧ Rbool ∧
        c.IsDefEqU equation' body' ∧
        c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU zr₁ zr₂ ∧ c.IsDefEqU s₁ s₂ ∧
        c.IsDefEqU vz₁ vz₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  by_cases hdeps :
      (c.env.contains ``Nat && c.env.contains ``Bool && v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      by_cases hb : b = true
      · rw [if_pos hb]
        have htyEq := htyEq hb
        exact (unfoldNatWellFoundedBoolNat2Cert.WF
          hfun hfunTy hnat hnatTy heq).bind fun core _ _ _ => by
          simp only [heq]
          exact (checkNatBitwiseFixCertificate.WF (bitwise := v.value)).bind
              fun cert _ _ hcert =>
            (checkType.WF hequation.fvarsIn).bind fun _ _ _ h => by
            let ⟨_, _, _, hequation', hequationTy, hequationHas⟩ := h
            cases hequation'.unique hequnique hequation
            exact (isDefEq.WF hequationTy hcanon).bind fun b _ _ hequationTyEq => by
              split
              · have hequationTyEq := hequationTyEq (by assumption)
                exact (hnatCheck (fun {_} {_} => .throw)).bind
                  fun _ _ _ hnatCert =>
                  (hboolCheck (fun {_} {_} => .throw)).bind
                    fun _ _ _ hboolCert =>
                    (checkType.WF hbody.fvarsIn).bind fun _ _ _ _ =>
                    (isDefEq.WF hequation hbody).bind fun b _ _ hbodyEq => by
                      split
                      · have hbodyEq := hbodyEq (by assumption)
                        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
                          split
                          · have hzEq := hzEq (by assumption)
                            exact (isDefEq.WF hzr₁ hzr₂).bind fun b _ _ hzrEq => by
                              split
                              · have hzrEq := hzrEq (by assumption)
                                exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
                                  split
                                  · have hsEq := hsEq (by assumption)
                                    exact (checkNatBitwiseZero.WF hvz₁ hvz₂
                                      (fun {_} {_} => .throw)).bind fun _ _ _ hvzEq =>
                                      .pure fun _ =>
                                        ⟨hlparams, htyEq, cert,
                                          hcert.1.normalize hcert.2,
                                          hnatCert, hboolCert,
                                          hbodyEq, hzEq, hzrEq, hsEq, hvzEq⟩
                                  · exact .throw
                              · exact .throw
                          · exact .throw
                      · exact .throw
              · exact .throw
      · rw [if_neg hb]
        exact .throw
  · rw [if_neg hdeps]
    exact .throw

theorem checkPrimitiveDef.natShiftLeft.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.shiftLeft) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (.bvar 0) q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 0) (mkApp q(Nat.succ) (.bvar 1))) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value
          (mkApp2 q(Nat.mul) q(Nat.succ (Nat.succ Nat.zero)) (.bvar 0))
          (.bvar 1)) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ => ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

theorem checkPrimitiveDef.natShiftRight.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.shiftRight) (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hz₁ : c.TrExprS
      (.lam0 q(Nat) <| mkApp2 v.value (.bvar 0) q(Nat.zero)) z₁)
    (hz₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0) z₂)
    (hs₁ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 v.value (.bvar 0) (mkApp q(Nat.succ) (.bvar 1))) s₁)
    (hs₂ : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <|
        mkApp2 q(Nat.div) (mkApp2 v.value (.bvar 0) (.bvar 1))
          q(Nat.succ (Nat.succ Nat.zero))) s₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.IsDefEqU z₁ z₂ ∧ c.IsDefEqU s₁ s₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        exact (isDefEq.WF hz₁ hz₂).bind fun b _ _ hzEq => by
          split
          · have hzEq := hzEq (by assumption)
            exact (isDefEq.WF hs₁ hs₂).bind fun b _ _ hsEq => by
              split
              · exact .pure fun _ => ⟨hlparams, htyEq, hzEq, hsEq (by assumption)⟩
              · exact .throw
          · exact .throw
      · exact .throw
  · exact .throw

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natXor.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.xor)
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hop : c.TrExprS op op')
    (hopCanon : c.TrExprS q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool))
    (hff₁ : c.TrExprS (mkApp2 op q(false) q(false)) ff₁)
    (hff₂ : c.TrExprS q(false) ff₂)
    (htf₁ : c.TrExprS (mkApp2 op q(true) q(false)) tf₁)
    (htf₂ : c.TrExprS q(true) tf₂)
    (hft₁ : c.TrExprS (mkApp2 op q(false) q(true)) ft₁)
    (hft₂ : c.TrExprS q(true) ft₂)
    (htt₁ : c.TrExprS (mkApp2 op q(true) q(true)) tt₁)
    (htt₂ : c.TrExprS q(false) tt₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.HasType op' (.forallE .bool <| .forallE .bool .bool) ∧
      c.IsDefEqU ff₁ ff₂ ∧ c.IsDefEqU tf₁ tf₂ ∧
      c.IsDefEqU ft₁ ft₂ ∧ c.IsDefEqU tt₁ tt₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        rw [hvalue]
        refine (inferType.WF hop).bind fun _ _ _ hOpTy => ?_
        let ⟨_, _, _, hOpTyTr, hOpHas⟩ := hOpTy
        refine (isDefEq.WF hOpTyTr hopCanon).bind fun b _ _ hOpEq => ?_
        split
        · have hopTy := hOpHas.defeqU_r c.Ewf c.Δwf (hOpEq (by assumption))
          exact (isDefEq.WF hff₁ hff₂).bind fun b _ _ hffEq => by
            split
            · have hffEq := hffEq (by assumption)
              exact (isDefEq.WF htf₁ htf₂).bind fun b _ _ htfEq => by
                split
                · have htfEq := htfEq (by assumption)
                  exact (isDefEq.WF hft₁ hft₂).bind fun b _ _ hftEq => by
                    split
                    · have hftEq := hftEq (by assumption)
                      exact (isDefEq.WF htt₁ htt₂).bind fun b _ _ httEq => by
                        split
                        · exact .pure fun _ =>
                            ⟨hlparams, htyEq, hopTy, hffEq, htfEq, hftEq, httEq (by assumption)⟩
                        · exact .throw
                    · exact .throw
                · exact .throw
            · exact .throw
        · exact .throw
      · exact .throw
  · exact .throw

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natLand.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.land)
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hop : c.TrExprS op op')
    (hopCanon : c.TrExprS q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool))
    (hf₁ : c.TrExprS
      (.lam0 q(Bool) <| mkApp2 op q(false) (.bvar 0)) f₁)
    (hf₂ : c.TrExprS (.lam0 q(Bool) q(false)) f₂)
    (ht₁ : c.TrExprS
      (.lam0 q(Bool) <| mkApp2 op q(true) (.bvar 0)) t₁)
    (ht₂ : c.TrExprS (.lam0 q(Bool) <| .bvar 0) t₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.HasType op' (.forallE .bool <| .forallE .bool .bool) ∧
      c.IsDefEqU f₁ f₂ ∧ c.IsDefEqU t₁ t₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        rw [hvalue]
        refine (inferType.WF hop).bind fun _ _ _ hOpTy => ?_
        let ⟨_, _, _, hOpTyTr, hOpHas⟩ := hOpTy
        refine (isDefEq.WF hOpTyTr hopCanon).bind fun b _ _ hOpEq => ?_
        split
        · have hopTy := hOpHas.defeqU_r c.Ewf c.Δwf (hOpEq (by assumption))
          exact (isDefEq.WF hf₁ hf₂).bind fun b _ _ hfEq => by
            split
            · have hfEq := hfEq (by assumption)
              exact (isDefEq.WF ht₁ ht₂).bind fun b _ _ htEq => by
                split
                · exact .pure fun _ =>
                    ⟨hlparams, htyEq, hopTy, hfEq, htEq (by assumption)⟩
                · exact .throw
            · exact .throw
        · exact .throw
      · exact .throw
  · exact .throw

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natLor.WF {c : VContext} {s : VState}
    (hname : v.name = ``Nat.lor)
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hty : c.TrExprS v.type ty')
    (hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat))
    (hop : c.TrExprS op op')
    (hopCanon : c.TrExprS q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool))
    (hf₁ : c.TrExprS
      (.lam0 q(Bool) <| mkApp2 op q(false) (.bvar 0)) f₁)
    (hf₂ : c.TrExprS (.lam0 q(Bool) <| .bvar 0) f₂)
    (ht₁ : c.TrExprS
      (.lam0 q(Bool) <| mkApp2 op q(true) (.bvar 0)) t₁)
    (ht₂ : c.TrExprS (.lam0 q(Bool) q(true)) t₂) :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      c.HasType op' (.forallE .bool <| .forallE .bool .bool) ∧
      c.IsDefEqU f₁ f₂ ∧ c.IsDefEqU t₁ t₂ := by
  simp only [checkPrimitiveDef, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hlparams : v.levelParams = [] := by
      simp at hdeps
      simpa using hdeps.2
    simp only [pure_bind]
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        rw [hvalue]
        refine (inferType.WF hop).bind fun _ _ _ hOpTy => ?_
        let ⟨_, _, _, hOpTyTr, hOpHas⟩ := hOpTy
        refine (isDefEq.WF hOpTyTr hopCanon).bind fun b _ _ hOpEq => ?_
        split
        · have hopTy := hOpHas.defeqU_r c.Ewf c.Δwf (hOpEq (by assumption))
          exact (isDefEq.WF hf₁ hf₂).bind fun b _ _ hfEq => by
            split
            · have hfEq := hfEq (by assumption)
              exact (isDefEq.WF ht₁ ht₂).bind fun b _ _ htEq => by
                split
                · exact .pure fun _ =>
                    ⟨hlparams, htyEq, hopTy, hfEq, htEq (by assumption)⟩
                · exact .throw
            · exact .throw
        · exact .throw
      · exact .throw
  · exact .throw

end Environment

def PrimitiveInductive.Valid (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  lparams = [] ∧ nparams = 0 ∧ isUnsafe = false ∧
  ∃ type, types = [type] ∧ type.type = .sort (.succ .zero) ∧
    ((type.name = ``Bool ∧
      type.ctors = [⟨``Bool.false, .const ``Bool []⟩,
        ⟨``Bool.true, .const ``Bool []⟩]) ∨
     (∃ name bi, type.name = ``Nat ∧
      type.ctors = [⟨``Nat.zero, .const ``Nat []⟩,
        ⟨``Nat.succ, .forallE name (.const ``Nat []) (.const ``Nat []) bi⟩]))

set_option maxHeartbeats 800000 in
theorem checkPrimitiveInductive.WF :
    (Environment.checkPrimitiveInductive env lparams nparams types isUnsafe).WF fun b =>
      b → PrimitiveInductive.Valid lparams nparams types isUnsafe := by
  intro b hrun hb
  subst b
  unfold Environment.checkPrimitiveInductive at hrun
  simp only [bind, Except.bind] at hrun
  split at hrun
  · rename_i hguard
    have ⟨⟨hunsafe, hlparams⟩, hnparams⟩ :
        (isUnsafe = false ∧ lparams = []) ∧ nparams = 0 := by
      simpa using hguard
    subst isUnsafe
    subst lparams
    subst nparams
    cases types with
    | nil => simp [pure, Except.pure] at hrun
    | cons type types =>
      cases types with
      | cons type' types => simp [pure, Except.pure] at hrun
      | nil =>
        simp [pure, Except.pure] at hrun
        split at hrun
        · rename_i htype
          have htypeEq : type.type = .sort (.succ .zero) :=
            Expr.eqv_sort.mp htype
          split at hrun
          · rename_i hname
            split at hrun
            · rename_i hctors
              exact ⟨rfl, rfl, rfl, type, rfl, htypeEq, .inl ⟨hname, hctors⟩⟩
            · simp at hrun
          · rename_i hnotBool hname
            split at hrun
            · rename_i name bi hctors
              exact ⟨rfl, rfl, rfl, type, rfl, htypeEq,
                .inr ⟨name, bi, hname, hctors⟩⟩
            · simp at hrun
          · simp at hrun
        · simp at hrun
  · simp [pure, Except.pure] at hrun

/-- The corrected lambda encoding used for open primitive equations is accepted
by the existing verified `isDefEq` interface once its open bodies translate. -/
theorem TypeChecker.isDefEqLam1.WF {c : VContext} {s : VState}
    (hty : c.IsType ty') (htrTy : c.TrExprS ty ty')
    (h₁ : TrExprS c.venv c.lparams ((none, .vlam ty') :: c.vlctx) e₁ e₁')
    (h₂ : TrExprS c.venv c.lparams ((none, .vlam ty') :: c.vlctx) e₂ e₂') :
    M.WF c s (isDefEq (.lam0 ty e₁) (.lam0 ty e₂)) fun b _ =>
      b → c.IsDefEqU (.lam ty' e₁') (.lam ty' e₂') :=
  TypeChecker.isDefEq.WF (.lam hty htrTy h₁) (.lam hty htrTy h₂)

end Lean4Lean
