import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaLead

/-! # Validity of an ι rule from its static data

`PatValid.of_rule`: a registered ι rule is valid in the model (`PatValid`) given its static data
(`IotaStatic`, uniqueness of the rule per head and constructor, coverage of the template's
binders, rigidity facts), for every instantiation of its levels the family facts of its major
(`MajorFam`, the mode C facts) and the semantic typing of its reduct template, and for every
instance the relation of the instance's arguments to the template (`IotaArgRel`, established for
ordinary blocks by `iotaArgRel_of`). An instance is decomposed by its match
(`SimplePattern.iotaRHS_apply_of_matches`), typed through the pattern rule (`IsDefEq.pat`), and
sound by `iota_inst_sound`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem HTS.const_levels (H : HTS env U Δ Γ e T) (he : e = .const c ls) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars := by
  induction H with
  | const hci hls hlen => cases he; exact ⟨_, hci, hls, hlen⟩
  | conv _ _ ih => exact ih he
  | other h => exact absurd he (h c ls [])
  | bvar | app | lam | forallE | proj => cases he

theorem HTS.spine_levels : ∀ {args : List VExpr} {T : VExpr},
    HTS env U Δ Γ (.mkApps (.const c ls) args) T →
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars := by
  intro args
  induction args using List.reverseRecOn with
  | nil => intro T H; exact H.const_levels rfl
  | snoc pre a ih =>
    intro T H
    obtain ⟨_, _, _, _, h, -⟩ := H.app_const_inv' rfl
    exact ih h


/-- **Validity of an ι rule** from its static data. -/
theorem PatValid.of_rule (henv : env.OrderedStrong)
    {n ctor : Name} {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    {doms : List VExpr} {body : VExpr}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true))
    (hr : rhs = .wrapLams doms body)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs lead ms : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (huniq : PatUniq env n ctor k nind cnp nf rhs)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ iotaFs nf)
    (hIrig : env.Rigid I) (hcf : CtorFam env ctor I) (hcis : IsCtor env ctor)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (hms : ms.length = cnp)
    (hlev : ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (env.IsType U) → ∀ m1 : List VLevel,
      (∀ l ∈ m1, l.WF U) → m1.length = ci.uvars →
      MajorFam env U Δ [] I ctor doms lead ms (iotaFs nf) m1 lsI ∧
      (∀ keys : List Key, keys.length = lead.length →
        Obs env U Δ .id .empty (ci.type.instL m1) (piCodChain keys
          (.piDomOb (.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length fun _ => 0))) →
        (∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
          ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
            h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true)) ∧
        ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
          ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL m1)).reverse ++ []) →
          TV env U Δ ((doms.map (·.instL m1)).reverse ++ []) v vS →
          (∃ P, TyCls env U Δ ((binderTy doms m1 x).subst v) P ∧
            env.HasType U Δ P (.sort .zero)) ∧
          ∀ τ, Obs env U Δ v vS (binderTy doms m1 x) τ →
            ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0]) ∧
      ∃ T, HTS env U Δ [] (rhs.instL m1) T ∧ SoundAt env U Δ [] (rhs.instL m1) (rhs.instL m1) T)
    (hrel : ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (env.IsType U) →
      ∀ (Γ : List VExpr) (m1 lsC : List VLevel) (recArgs ctorArgs : List VExpr) (A : VExpr),
      recArgs.length = k + nind → ctorArgs.length = cnp + nf →
      HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A →
      ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
        IotaArgRel env U Δ Γ n ctor m1 lsC cnp nf doms lead recArgs ctorArgs
          (recArgs.take k ++ ctorArgs.drop cnp) σ S ∧
        List.Forall₂ (· ≈ ·) lsC (lsI.map (·.inst m1))) :
    PatValid env (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true) := by
  intro U Δ Γ e A m1 m2 chk hΔ hm hr' he ihe hred ihred hall
  have heq : env.IsDefEq U Γ e ((SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc).apply m1 m2) A :=
    .pat hp hm he.defeq.hasType.1 hred.defeq.hasType.1 hr' (fun t ht => (hall t ht).1.defeq)
  obtain ⟨recArgs, ctorArgs, lsC, hrA, hcA, rfl, hred_eq⟩ :=
    SimplePattern.iotaRHS_apply_of_matches hm
  have e : Pattern.RHS.apply m1 m2 (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc) =
      (rhs.instL m1).mkApps (recArgs.take k ++ ctorArgs.drop cnp) := hred_eq
  rw [e] at heq ihred ⊢
  obtain ⟨ci', hci', hlw, hlen⟩ := ihe.2.spine_levels
  cases hci.symm.trans hci'
  obtain ⟨hfam, hC, T, hRH, hRS⟩ := hlev U Δ hΔ m1 hlw hlen
  exact iota_inst_sound henv hΔ hp hr hci hstat hstat.leadUniq huniq hcov hIrig hcf hcis hcrig
    hctor hpctor hnodf hms hfam hC hrA hcA rfl ihe ihred.1 heq hRH hRS
    (hrel U Δ hΔ Γ m1 lsC recArgs ctorArgs A hrA hcA ihe.2)


/-- **Validity of an ι rule whose reduct has no observations** (elimination into `Prop`). -/
theorem PatValid.of_rule_empty (henv : env.OrderedStrong)
    {n ctor : Name} {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    {doms : List VExpr} {body : VExpr}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true))
    (hr : rhs = .wrapLams doms body)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs lead : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (huniq : PatUniq env n ctor k nind cnp nf rhs)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (hfam : MajorFamEntry env I ctor)
    (hlev : ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (env.IsType U) → ∀ m1 : List VLevel,
      (∀ l ∈ m1, l.WF U) → m1.length = ci.uvars →
      (∃ T, HTS env U Δ [] (rhs.instL m1) T ∧ SoundAt env U Δ [] (rhs.instL m1) (rhs.instL m1) T) ∧
      ∀ o, ¬ Obs env U Δ .id .empty (rhs.instL m1) o)
    (hrel : ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (env.IsType U) →
      ∀ (Γ : List VExpr) (m1 lsC : List VLevel) (recArgs ctorArgs : List VExpr) (A : VExpr),
      recArgs.length = k + nind → ctorArgs.length = cnp + nf →
      HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A →
      ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
        IotaArgRel env U Δ Γ n ctor m1 lsC cnp nf doms lead recArgs ctorArgs
          (recArgs.take k ++ ctorArgs.drop cnp) σ S ∧
        List.Forall₂ (· ≈ ·) lsC (lsI.map (·.inst m1))) :
    PatValid env (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true) := by
  intro U Δ Γ e A m1 m2 chk hΔ hm hr' he ihe hred ihred hall
  obtain ⟨recArgs, ctorArgs, lsC, hrA, hcA, rfl, hred_eq⟩ :=
    SimplePattern.iotaRHS_apply_of_matches hm
  have e : Pattern.RHS.apply m1 m2 (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc) =
      (rhs.instL m1).mkApps (recArgs.take k ++ ctorArgs.drop cnp) := hred_eq
  rw [e] at ihred ⊢
  obtain ⟨ci', hci', hlw, hlen⟩ := ihe.2.spine_levels
  cases hci.symm.trans hci'
  obtain ⟨⟨T, hRH, hRS⟩, hE⟩ := hlev U Δ hΔ m1 hlw hlen
  have hRcl : (rhs.instL m1).ClosedN := (show rhs.ClosedN from hc).instL
  have empty : ∀ σ' S', ∀ o, ¬ Obs env U Δ σ' S' ((rhs.instL m1).mkApps (recArgs.take k ++ ctorArgs.drop cnp)) o := by
    intro σ' S' o ho
    obtain ⟨keys, -, hw⟩ := wrap_of_obs_mkApps ho
    exact hE _ ((Obs.closed_iff_id hRcl).1 hw)
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  obtain ⟨⟨Wv, tvv, hlead, -⟩, -⟩ := hrel U Δ hΔ Γ m1 lsC recArgs ctorArgs A hrA hcA ihe.2 σ' S W' tv'
  have hLR := iota_lhs_sub_inst henv hΔ hp hr hci hstat hstat.leadUniq huniq hcrig hctor hpctor
    hnodf hfam (lsC := lsC) hrA hcA rfl hRH hRS (σ := σ') rfl rfl Wv tvv
    (fun i x h1 h2 h3 => let ⟨a, ha, hd, _, hs, _⟩ := hlead i x h1 h2 h3; ⟨a, ha, hd, hs⟩)
  refine ⟨fun o ho => ?_, fun o ho => absurd ho (empty _ _ o), (ihe.1 σ σ S W.left tv tv).2.2.1,
    (ihred.1 σ' σ' S W' tv' tv').2.2.1⟩
  obtain ⟨o₁, ho₁, -⟩ := (ihe.1 σ σ' S W tv tv').1 o ho
  obtain ⟨o₂, ho₂, -⟩ := hLR o₁ ho₁
  exact absurd ho₂ (empty _ _ o₂)

end Model
end VEnv
end Lean4Lean
