import Lean4Lean.Theory.Typing.ProjectionLemmas

/-!
# Applying stored equations

Iota rules are stored as closed lambda-wrapped equations. Applying such an equation to actual
arguments and beta-reducing yields the instantiated body; this is what the checker's recursor
reduction refines.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Typing inversion for lambdas that retains the codomain. -/
theorem HasType.lam_inv_forallE (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.lam A body) V) :
    ∃ B, env.IsDefEqU U Γ (.forallE A B) V ∧ env.HasType U (A::Γ) body B := by
  replace H := (H.strong henv.ordered hΓ).hasType'.1
  generalize eq : true = b, eq' : A.lam body = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih =>
    obtain ⟨B, hB, hb⟩ := ih hΓ rfl eq'
    exact ⟨B, hB.trans henv hΓ ⟨_, h2.defeq⟩, hb⟩
  | base H =>
    subst eq'
    let .lam _ _ _ _ h2 h4 := H
    exact ⟨_, ⟨_, h4.hasType⟩, h2.hasType⟩

theorem _root_.Lean4Lean.VExpr.wrapLams_inst (doms : List VExpr) (body a : VExpr) (k : Nat) :
    (VExpr.wrapLams doms body).inst a k =
      VExpr.wrapLams (VExpr.instDomains doms a k) (body.inst a (k + doms.length)) := by
  induction doms generalizing k with
  | nil => rfl
  | cons d ds ih =>
    show (VExpr.lam d (VExpr.wrapLams ds body)).inst a k =
      VExpr.lam (d.inst a k) (VExpr.wrapLams (VExpr.instDomains ds a (k + 1))
        (body.inst a (k + (ds.length + 1))))
    simp only [VExpr.inst]
    rw [ih, Nat.add_assoc, Nat.add_comm 1]

/-- Applying a lambda-wrapped term to a full argument list beta-reduces to the instantiated body. -/
theorem IsDefEq.mkApps_wrapLams (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {args : List VExpr} {doms : List VExpr} {body T : VExpr},
      env.HasType U Γ (VExpr.wrapLams doms body) (VExpr.wrapForalls doms T) →
      args.length = doms.length →
      (∀ j (hj : j < args.length) (hj' : j < doms.length),
        env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) →
      env.IsDefEq U Γ (VExpr.mkApps (VExpr.wrapLams doms body) args) (body.instOuter args)
        (T.instOuter args) := by
  intro args
  induction args with
  | nil =>
    intro doms body T hf hlen _
    cases doms with
    | nil => exact hf
    | cons => simp at hlen
  | cons a as ih =>
    intro doms body T hf hlen hargs
    cases doms with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hf' : env.HasType U Γ (.lam d (VExpr.wrapLams ds body))
          (.forallE d (VExpr.wrapForalls ds T)) := hf
      have ha : env.HasType U Γ a d := hargs 0 (by simp) (by simp)
      -- the body of the lambda is typed at the wrapped telescope
      obtain ⟨B', hB', hbody⟩ := HasType.lam_inv_forallE henv hΓ hf'
      have ⟨⟨_, hd⟩, _, hBB⟩ := hB'.forallE_inv henv hΓ
      have hΓ' : OnCtx (d :: Γ) (env.IsType U) := ⟨hΓ, _, hd.hasType.1⟩
      have hbody' : env.HasType U (d :: Γ) (VExpr.wrapLams ds body) (VExpr.wrapForalls ds T) :=
        hbody.defeqU_r henv hΓ' ⟨_, hBB⟩
      have hbeta := IsDefEq.beta hbody' ha
      rw [VExpr.wrapLams_inst, VExpr.wrapForalls_inst] at hbeta
      simp only [Nat.zero_add] at hbeta
      have hargs' : ∀ j (hj : j < as.length) (hj' : j < (VExpr.instDomains ds a 0).length),
          env.HasType U Γ as[j] ((VExpr.instDomains ds a 0)[j].instOuter (as.take j)) := by
        intro j hj hj'
        have := hargs (j + 1) (by simpa using hj) (by simpa using hj')
        simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
          List.length_take] at this
        have hj0 : j < as.length := by simpa using hj
        rw [Nat.min_eq_left (Nat.le_of_lt hj0)] at this
        simpa [VExpr.instDomains_getElem ds a 0 j (by simpa using hj')] using this
      have hcongr := IsDefEq.mkApps_congr (args := as) (args' := as) hbeta
        (by simpa using hlen) rfl fun j hj hj' _ => hargs' j hj hj'
      have hih := ih (doms := VExpr.instDomains ds a 0) (body := body.inst a ds.length)
        (T := T.inst a ds.length) hbeta.hasType.2 (by simpa using hlen) hargs'
      have := hcongr.trans hih
      simp only [VExpr.instOuter_cons, hlen]
      exact this

theorem _root_.Lean4Lean.VExpr.instL_wrapLams (doms : List VExpr) (body : VExpr) (ls : List VLevel) :
    (VExpr.wrapLams doms body).instL ls =
      VExpr.wrapLams (doms.map (VExpr.instL ls)) (body.instL ls) := by
  induction doms with
  | nil => rfl
  | cons d ds ih => simp [VExpr.wrapLams, VExpr.instL] at ih ⊢; exact ih

/-- A stored lambda-wrapped equation, instantiated at universe levels and applied to a full list of
arguments typed at its telescope, yields the instantiated bodies. -/
theorem IsDefEq.extra_instOuter (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hdf : env.defeqs df) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars)
    (hlhs : df.lhs = VExpr.wrapLams doms lhsBody) (hrhs : df.rhs = VExpr.wrapLams doms rhsBody)
    (htype : df.type = VExpr.wrapForalls doms typeBody)
    (hargs : args.length = doms.length)
    (hty : ∀ j (hj : j < args.length) (hj' : j < doms.length),
      env.HasType U Γ args[j] (((doms[j]).instL ls).instOuter (args.take j))) :
    env.IsDefEq U Γ ((lhsBody.instL ls).instOuter args) ((rhsBody.instL ls).instOuter args)
      ((typeBody.instL ls).instOuter args) := by
  have hex := IsDefEq.extra (env := env) (Γ := Γ) hdf hls hlen
  rw [hlhs, hrhs, htype, VExpr.instL_wrapLams, VExpr.instL_wrapLams, VExpr.instL_wrapForalls] at hex
  have hex' := hex
  have hty' : ∀ j (hj : j < args.length) (hj' : j < (doms.map (VExpr.instL ls)).length),
      env.HasType U Γ args[j] ((doms.map (VExpr.instL ls))[j].instOuter (args.take j)) := by
    intro j hj hj'
    rw [List.getElem_map]
    exact hty j hj (by simpa using hj')
  have hcongr := IsDefEq.mkApps_congr (args := args) (args' := args) hex'
    (by simpa using hargs) rfl fun j hj hj' _ => hty' j hj hj'
  have h1 := IsDefEq.mkApps_wrapLams henv hΓ hex'.hasType.1 (by simpa using hargs) hty'
  have h2 := IsDefEq.mkApps_wrapLams henv hΓ hex'.hasType.2 (by simpa using hargs) hty'
  exact h1.symm.trans (hcongr.trans h2)

end VEnv
end Lean4Lean
