import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleSound

/-! # The quotient rule as a pattern rule

The syntactic facts of `quotDefEq` needed by `sound_pat`: its pattern
(`Quot.lift α r β f c (Quot.mk α r a) ≡ f a`, lead `α r β f c`, major `Quot.mk α r a` with
field `a`), the family `Quot` of the major domain of `Quot.lift`'s type, and, at levels at
which `Quot` is a proposition (mode C), the propositional typing of the field `a`. They
hold whenever the quotient constants are the ones installed by `addQuot`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The leading lambdas of a term. -/
def lamDoms : VExpr → List VExpr
  | .lam d b => d :: lamDoms b
  | _ => []

def quotDoms : List VExpr := lamDoms quotDefEq.lhs

def quotLead : List VExpr := [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]

theorem quotDefEq_lhs : quotDefEq.lhs = .wrapLams quotDoms (.mkApps
    (.const `Quot.lift [.param 0, .param 1])
    (quotLead ++ [.mkApps (.const `Quot.mk [.param 0]) ([.bvar 5, .bvar 4] ++ [0].map .bvar)])) :=
  rfl

theorem quotDefEq_rhs : quotDefEq.rhs = .wrapLams quotDoms (.app (.bvar 2) (.bvar 0)) := rfl

theorem quotDefEq_ctorMajor : quotDefEq.HasConstructorMajor ``Quot.mk :=
  ⟨.mkApps (.const `Quot.lift [.param 0, .param 1]) quotLead, [.param 0],
    [.bvar 5, .bvar 4, .bvar 0], rfl⟩

theorem quotDoms_length : quotDoms.length = 6 := rfl

theorem quot_cov : ∀ x < quotDoms.length, VExpr.bvar x ∈ quotLead ∨ x ∈ [0] := by
  intro x hx; rw [quotDoms_length] at hx
  match x, hx with
  | 0, _ => exact .inr (by simp)
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => exact .inl (by simp [quotLead])

/-- The quotient constants as installed by `addQuot`. -/
def QuotConsts (env : VEnv) : Prop :=
  env.constants ``Quot = some quotConst ∧ env.constants ``Quot.mk = some quotMkConst ∧
    env.constants ``Quot.lift = some quotLiftConst

def quotLiftDoms : List VExpr := [.sort (.param 0),
  .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort (.param 1),
  .forallE (.bvar 2) (.bvar 1),
  .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.const `Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
      (.app (.bvar 3) (.bvar 1))))),
  .mkApps (.const `Quot [.param 0]) [.bvar 4, .bvar 3]]

theorem quotLiftConst_type : quotLiftConst.type = .wrapForalls quotLiftDoms (.bvar 3) := rfl

/-- The innermost observation of a typed chain at a telescope ending in a sort is typed at
that sort only. -/
theorem chain_terminal_sort : ∀ {ds : List VExpr} {keys : List Key} {o : Ob} {τs : List Ob},
    keys.length = ds.length → TypedOb env U Δ cv (wrap keys o) τs →
    (∀ τ ∈ τs, ∃ σ S, Obs' σ S (.wrapForalls ds (.sort w)) τ) →
    ∃ τc cv', (∀ τ ∈ τc, τ = .sort w.eval) ∧ TypedOb env U Δ cv' o τc
  | [], [], o, τs, _, ho, hτ => ⟨τs, _, fun τ h => let ⟨_, _, h⟩ := hτ τ h; Obs.sort_mem h, ho⟩
  | A :: ds, k :: keys, o, τs, hl, ho, hτ => by
    obtain ⟨D, c, K⟩ := k
    simp only [wrap_cons] at ho
    cases ho with
    | app hD hd hkt hb hc hC hcod hty' =>
      refine chain_terminal_sort (Nat.succ.inj hl) hty' fun x hx => ?_
      obtain ⟨K₀, hm, -⟩ := hcod x hx
      obtain ⟨σ, S, h⟩ := hτ _ hm
      obtain ⟨-, -, z, -, hxR⟩ := Obs.piCodOb_mem h
      exact ⟨_, _, hxR⟩

theorem quot_lead_x (hx : x < quotDoms.length)
    (hnb : ∀ i : Nat, quotLead[i]? ≠ some (VExpr.bvar x)) : x = 0 := by
  rw [quotDoms_length] at hx
  match x, hx with
  | 0, _ => rfl
  | 1, _ => exact absurd rfl (hnb 4)
  | 2, _ => exact absurd rfl (hnb 3)
  | 3, _ => exact absurd rfl (hnb 2)
  | 4, _ => exact absurd rfl (hnb 1)
  | 5, _ => exact absurd rfl (hnb 0)

theorem quot_binderTy0 : binderTy quotDoms ls 0 = .bvar 5 := rfl

theorem quot_binderTy5 : binderTy quotDoms ls 5 = .sort ((VLevel.param 0).inst ls) := rfl

theorem tele_obs_inv : ∀ {ds : List VExpr} {keys : List Key} {σ : VExpr.Subst} {S : ObSets}
    {x : Ob}, keys.length = ds.length →
    Obs' σ S (.wrapForalls ds R) (piCodChain keys x) → ∃ σ' S', Obs' σ' S' R x
  | [], [], σ, S, _, _, h => ⟨σ, S, h⟩
  | _ :: _, _ :: _, _, _, _, hl, h => by
    obtain ⟨-, -, _, -, h⟩ := Obs.piCodOb_mem h
    exact tele_obs_inv (Nat.succ.inj hl) h

/-- The quotient rule in mode C: the zero-sort rigid observation of `Quot α r` at the major
domain forces `Quot`'s level to vanish at `ls`, so the field `a` is a proof. -/
theorem quot_C_level (hq : QuotConsts env) (hrigQ : env.Rigid ``Quot) {keys : List Key}
    (hkl : keys.length = quotLead.length)
    (h : Obs' .id .empty (quotLiftConst.type.instL ls) (piCodChain keys
      (.piDomOb (.rigid ``Quot (([VLevel.param 0].map (·.inst ls)).map (·.eval)) 2 fun _ => 0)))) :
    ((VLevel.param 0).inst ls).eval = fun _ => 0 := by
  have eT : quotLiftConst.type.instL ls = .wrapForalls ((quotLiftDoms.take 5).map (·.instL ls))
      (.forallE ((VExpr.mkApps (.const ``Quot [.param 0]) [.bvar 4, .bvar 3]).instL ls)
        ((VExpr.bvar 3).instL ls)) := rfl
  rw [eT] at h
  obtain ⟨σ', S', h⟩ := tele_obs_inv (by simpa [quotLead, quotLiftDoms] using hkl) h
  have h := Obs.piDomOb_mem h
  simp only [VExpr.instL_mkApps, VExpr.instL] at h
  obtain ⟨keys', -, hc⟩ := wrap_of_obs_mkApps h
  rcases Obs.const_iff.1 hc with ⟨ci, τs, keys'', r, e, -, hci, hτ, hty, hr⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys'', r, e, -, -, -, -, -, hr, -⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, keys'', r, e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys'', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys'', _, _, _, _, _, _, e, _⟩
  · obtain ⟨rfl, rfl⟩ := wrap_inj e trivial hr.notApp
    cases hq.1.symm.trans hci
    have hlen : keys'.length = 2 := by
      rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩
      · injection h with _ _ h; exact h.symm
      · cases h
    obtain ⟨τc, _, hτc, hty'⟩ := chain_terminal_sort (ds := [.sort ((VLevel.param 0).inst ls),
        .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))]) (w := (VLevel.param 0).inst ls)
      (by simpa using hlen) hty fun τ hτ' => ⟨_, _, hτ τ hτ'⟩
    cases hty' with
    | rigid h1 =>
      have := hτc _ h1
      injection this with this
      exact this.symm
  · exact absurd (by rw [hlhs]; rfl) (hrigQ df hdf _)
  · obtain ⟨rfl, rfl⟩ := wrap_inj e trivial (by
      rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial)
    rcases hr with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrigQ df hdf lsP)
  · obtain ⟨rfl, h⟩ := wrap_inj e trivial trivial; cases h
  · obtain ⟨rfl, h⟩ := wrap_inj e trivial trivial; cases h
  · obtain ⟨rfl, h⟩ := wrap_inj e trivial trivial; cases h

/-- In mode C (the quotient is a proposition at `ls`), the field `a` is a proof. -/
theorem quot_pf (hlsw : ∀ l ∈ ls, l.WF U) (e0 : ((VLevel.param 0).inst ls).eval = fun _ => 0) :
    ∀ x < quotDoms.length,
      (∀ i : Nat, quotLead[i]? ≠ some (VExpr.bvar x)) →
      ∀ v vS, Ctx.SubstEq env U Δ v v ((quotDoms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((quotDoms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy quotDoms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy quotDoms ls x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0] := by
  intro x hx hnb v vS Wv tvv
  obtain rfl := quot_lead_x hx hnb
  have hL := lookup_binderTy (Γ := Γ) (ls := ls) (doms := quotDoms) (x := 5) (by decide)
  rw [quot_binderTy5] at hL
  have hv5 := (Wv.lookup hL).hasType.1
  have hw : ((VLevel.param 0).inst ls).WF U := .inst hlsw
  have hsz : env.IsDefEq U Δ (.sort ((VLevel.param 0).inst ls)) (.sort .zero)
      (.sort (.succ ((VLevel.param 0).inst ls))) := .sortDF hw trivial e0
  rw [quot_binderTy0]
  refine ⟨⟨v 5, .self, hsz.defeqDF hv5⟩, fun τ hτ => ?_⟩
  have := tvv.2 5 _ hL τ (Obs.bvar_iff.1 hτ)
  have := typedAt_sort_iff.1 this
  rw [e0] at this
  exact ⟨_, this⟩

/-- Uniqueness of the quotient rule for its head and constructor, from its uniqueness per
head. -/
theorem quot_uniq (hqu : ∀ df' ls', env.defeqs df' →
      df'.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift ls' → df' = quotDefEq) :
    ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const ``Quot.lift lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = quotLead.length ∧ (ctor' = ``Quot.mk → df' = quotDefEq) := by
  intro df' doms' lsP' lead' ctor' lsC' ms' fs' body' hdf hl _
  have := hqu df' lsP' hdf (by rw [hl]; exact VExpr.stripLams_wrapLams_mkApps_head)
  subst this
  obtain ⟨-, -, -, h, -⟩ := wrapLams_pat_inj (hl.symm.trans quotDefEq_lhs)
  exact ⟨by rw [h], fun _ => rfl⟩

end Model
end VEnv
end Lean4Lean
