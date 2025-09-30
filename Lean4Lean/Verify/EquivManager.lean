import Batteries.Data.UnionFind.Lemmas
import Lean4Lean.Verify.Typing.EnvLemmas
import Lean4Lean.EquivManager
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.EquivManager
open Lean hiding Environment Exception
open Batteries Kernel

inductive RelevantEq : Expr → Expr → Prop
  | bvar : RelevantEq (.bvar i) (.bvar i)
  | fvar : RelevantEq (.fvar i) (.fvar i)
  | mvar : RelevantEq (.mvar i) (.mvar i)
  | sort : RelevantEq (.sort u) (.sort u)
  | const : RelevantEq (.const n ls) (.const n ls)
  | app : RelevantEq f₁ f₂ → RelevantEq a₁ a₂ → RelevantEq (.app f₁ a₁) (.app f₂ a₂)
  | lam : RelevantEq d₁ d₂ → RelevantEq b₁ b₂ → RelevantEq (.lam _ d₁ b₁ _) (.lam _ d₂ b₂ _)
  | forallE : RelevantEq d₁ d₂ → RelevantEq b₁ b₂ →
    RelevantEq (.forallE _ d₁ b₁ _) (.forallE _ d₂ b₂ _)
  | letE : RelevantEq t₁ t₂ → RelevantEq v₁ v₂ → RelevantEq b₁ b₂ →
    RelevantEq (.letE _ t₁ v₁ b₁ _) (.letE _ t₂ v₂ b₂ _)
  | lit : RelevantEq (.lit l) (.lit l)
  | mdata : RelevantEq e₁ e₂ → RelevantEq (.mdata _ e₁) (.mdata _ e₂)
  | proj : RelevantEq e₁ e₂ → RelevantEq (.proj _ i e₁) (.proj _ i e₂)

theorem RelevantEq.rfl : RelevantEq e e := by
  induction e with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | mvar => exact .mvar
  | sort => exact .sort
  | const => exact .const
  | lit => exact .lit
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ _ ih => exact .mdata ih
  | proj _ _ _ ih => exact .proj ih

theorem RelevantEq.symm (H1 : RelevantEq e₁ e₂) : RelevantEq e₂ e₁ := by
  induction H1 with
  | bvar | fvar | mvar | sort | const | lit => exact .rfl
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

theorem RelevantEq.of_eqv : e₁ == e₂ → RelevantEq e₁ e₂ := by
  simp [(· == ·)]; induction e₁ generalizing e₂
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [Expr.eqv']; intros; subst_vars; try simp [rfl, *]
  all_goals grind [RelevantEq]

theorem RelevantEq.trans (H1 : RelevantEq e₁ e₂) (H2 : RelevantEq e₂ e₃) : RelevantEq e₁ e₃ := by
  induction H1 generalizing e₃ with
  | bvar | fvar | mvar | sort | const | lit => exact H2
  | app h1 h2 ih1 ih2 => let .app r1 r2 := H2; exact .app (ih1 r1) (ih2 r2)
  | lam h1 h2 ih1 ih2 => let .lam r1 r2 := H2; exact .lam (ih1 r1) (ih2 r2)
  | forallE h1 h2 ih1 ih2 => let .forallE r1 r2 := H2; exact .forallE (ih1 r1) (ih2 r2)
  | letE h1 h2 h3 ih1 ih2 ih3 => let .letE r1 r2 r3 := H2; exact .letE (ih1 r1) (ih2 r2) (ih3 r3)
  | mdata h1 ih => let .mdata r1 := H2; exact .mdata (ih r1)
  | proj h1 ih => let .proj r1 := H2; exact .proj (ih r1)

variable {env : VEnv} {Us : List Name} {Δ : VLCtx}

theorem IsDefEqE.relevant (H : RelevantEq e₁ e₂) : IsDefEqE env us Δ e₁ e₂ := by
  induction H with
  | bvar | fvar | mvar | sort | const | lit => exact .rfl
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! (henv : VEnv.WF env) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem RelevantEq.uniq (eq : RelevantEq e₁ e₂)
    (H1 : TrExprS env Us Δ₁ e₁ e₁') (H2 : TrExprS env Us Δ₂ e₂ e₂') :
    env.IsDefEqU Us.length Δ₁.toCtx e₁' e₂' := by
  induction H1 generalizing e₂ Δ₂ e₂' with
  | bvar l1 => cases eq; let .bvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 => cases eq; let .fvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 =>
    cases eq; let .sort r1 := H2; cases l1.symm.trans r1
    exact ⟨_, VEnv.HasType.sort (.of_ofLevel l1)⟩
  | const l1 l2 l3 =>
    cases eq; let .const r1 r2 r3 := H2; cases l1.symm.trans r1; cases l2.symm.trans r2
    exact (TrExprS.const l1 l2 l3).wf henv hΔ.wf
  | app l1 l2 _ _ ih3 ih4 =>
    let .app eq1 eq2 := eq; let .app _ _ r3 r4 := H2
    exact ⟨_, .appDF
      (ih3 hΔ eq1 r3 |>.of_l henv hΔ.wf.toCtx l1)
      (ih4 hΔ eq2 r4 |>.of_l henv hΔ.wf.toCtx l2)⟩
  | lam l1 _ _ ih2 ih3 =>
    let .lam eq1 eq2 := eq; let ⟨_, l1⟩ := l1; let .lam _ r2 r3 := H2
    have hA := ih2 hΔ eq1 r2 |>.of_l henv hΔ.wf.toCtx l1
    have ⟨_, hb⟩ := ih3 (hΔ.cons nofun <| .vlam hA) eq2 r3
    exact ⟨_, .lamDF hA hb⟩
  | forallE l1 l2 _ _ ih3 ih4 =>
    let .forallE eq1 eq2 := eq; let ⟨_, l1'⟩ := l1; let ⟨_, l2⟩ := l2; let .forallE _ _ r3 r4 := H2
    have hA := ih3 hΔ eq1 r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (hΔ.cons nofun <| .vlam hA) eq2 r4 |>.of_l (Γ := _::_) henv ⟨hΔ.wf.toCtx, l1⟩ l2
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    let .letE eq1 eq2 eq3 := eq; have hΓ := hΔ.wf.toCtx; let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    refine ih4 (hΔ.cons nofun ?_) eq3 r4
    exact .vlet (ih3 hΔ eq2 r3 |>.of_l henv hΓ l1) (ih2 hΔ eq1 r2 |>.of_l henv hΓ hb)
  | lit _ ih1 => cases eq; let .lit r1 := H2; exact ih1 hΔ .rfl r1
  | mdata _ ih1 => let .mdata eq := eq; let .mdata r1 := H2; exact ih1 hΔ eq r1
  | proj _ l2 ih1 =>
    let .proj eq := eq; let .proj r1 r2 := H2
    exact l2.uniq henv hΔ.defeqCtx r2 (ih1 hΔ eq r1)

theorem IsDefEqE.trExpr
    (henv : env.WF) (noBV : Δ.NoBV) (H1 : IsDefEqE env Us Δ r₁ r₂) (hΔ : Δ'.WF env Us.length)
    (W : Δ.BVLift Δ' dn 0 n 0) (hr : RelevantEq r₁ e₁) (he : TrExprS env Us Δ' e₁ e') :
    ∃ e₂, RelevantEq r₂ e₂ ∧ TrExpr env Us Δ' e₂ e' := by
  induction H1 generalizing e₁ Δ' e' dn n with
  | rfl => exact ⟨_, hr, he.trExpr henv hΔ⟩
  | trans _ _ ih1 ih2 =>
    let ⟨em, a1, _, a2, a3⟩ := ih1 hΔ W hr he
    have ⟨_, b1, b2⟩ := ih2 hΔ W a1 a2
    exact ⟨_, b1, b2.defeq henv hΔ a3⟩
  | defeq h1 h2 =>
    have h1' := h1.weakBV henv W; have h2' := h2.weakBV henv W
    rw [Expr.liftLooseBVars_eq_self (noBV ▸ h1.closed.looseBVarRange_le)] at h1'
    rw [Expr.liftLooseBVars_eq_self (noBV ▸ h2.closed.looseBVarRange_le)] at h2'
    exact ⟨_, .rfl, h2'.defeq henv hΔ (hr.uniq henv (.refl henv hΔ) h1' he)⟩
  | app _ _ ih1 ih2 =>
    let .app hr1 hr2 := hr; let .app a1 a2 a3 a4 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a3
    let ⟨_, c1, c2⟩ := ih2 hΔ W hr2 a4
    exact ⟨_, .app b1 c1, .app henv hΔ.toCtx a1 a2 b2 c2⟩
  | lam _ _ ih1 ih2 =>
    let .lam hr1 hr2 := hr; let .lam a1 a2 a3 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a2
    let ⟨_, c1, c2⟩ := ih2 (by exact ⟨hΔ, nofun, a1⟩) (.skip _ W) hr2 a3
    exact ⟨_, .lam b1 c1, .lam (name := default) (bi := default) henv hΔ a1 b2 c2⟩
  | forallE _ _ ih1 ih2 =>
    let .forallE hr1 hr2 := hr; let .forallE a1 a2 a3 a4 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a3
    let ⟨_, c1, c2⟩ := ih2 (by exact ⟨hΔ, nofun, a1⟩) (.skip _ W) hr2 a4
    exact ⟨_, .forallE b1 c1, .forallE (name := default) (bi := default) henv hΔ a1 a2 b2 c2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    let .letE hr1 hr2 hr3 := hr; let .letE a1 a2 a3 a4 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a2
    let ⟨_, c1, c2⟩ := ih2 hΔ W hr2 a3
    let ⟨_, d1, d2⟩ := ih3 (by exact ⟨hΔ, nofun, a1⟩) (.skip _ W) hr3 a4
    exact ⟨_, .letE b1 c1 d1, .letE (name := default) (nd := default) henv hΔ a1 b2 c2 d2⟩
  | mdata _ ih =>
    let .mdata hr := hr; let .mdata a1 := he; let ⟨_, b1, b2⟩ := ih hΔ W hr a1
    exact ⟨_, .mdata b1, .mdata (d := default) b2⟩
  | proj _ ih =>
    let .proj hr := hr; let .proj a1 a2 := he
    have ⟨_, b1, b2⟩ := ih hΔ W hr a1
    exact ⟨_, .proj b1, .proj henv hΔ b2 a2⟩

theorem IsDefEqE.uniq (henv : env.WF) (noBV : Δ.NoBV) (hΔ : Δ.WF env Us.length)
    (he₁ : TrExprS env Us Δ e₁ e₁') (he₂ : TrExprS env Us Δ e₂ e₂')
    (eq : IsDefEqE env Us Δ e₁ e₂) : env.IsDefEqU Us.length Δ.toCtx e₁' e₂' := by
  have ⟨_, a1, _, a2, a3⟩ := eq.trExpr henv noBV hΔ .refl .rfl he₁
  exact .symm <| a1.uniq henv (.refl henv hΔ) he₂ a2 |>.trans henv hΔ a3

protected structure LE (m₁ m₂ : EquivManager) where
  uf : m₁.uf.Equiv i₁ i₂ → m₂.uf.Equiv i₁ i₂
  toNodeMap {e : Expr} : m₁.toNodeMap[e]? = some i → m₂.toNodeMap[e]? = some i

instance : LE EquivManager := ⟨EquivManager.LE⟩

theorem LE.rfl {m : EquivManager} : m ≤ m := ⟨id, id⟩

theorem LE.trans {m₁ m₂ m₃ : EquivManager} (h1 : m₁ ≤ m₂) (h2 : m₂ ≤ m₃) : m₁ ≤ m₃ :=
 ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2⟩

variable (env Us Δ) in
def M.WF (m : EquivManager) (x : StateM EquivManager α) (P : α → EquivManager → Prop) :=
  m.WF env Us Δ → ∀ ⦃a m'⦄, x.run m = (a, m') → m'.WF env Us Δ ∧ m ≤ m' ∧ P a m'

theorem M.WF.stateWF {P : α → EquivManager → Prop}
    (H : m.WF env Us Δ → M.WF env Us Δ m x P) :
    M.WF env Us Δ m x P := fun h => H h h

protected theorem M.WF.pure {a : α} {P : α → EquivManager → Prop} (H : P a m) :
    M.WF env Us Δ m (pure a) P := by
  rintro wf _ _ ⟨⟩; exact ⟨wf, .rfl, H⟩

protected theorem M.WF.bind {x : StateM EquivManager β} {f : β → StateM EquivManager γ}
    (h1 : M.WF env Us Δ m x P) (h2 : ∀ a m', m ≤ m' → P a m' → M.WF env Us Δ m' (f a) Q) :
    M.WF env Us Δ m (x >>= f) Q := by
  intro wf a m₁; simp [bind, StateT.run, StateT.bind]; split; intro eq
  have ⟨wf, a1, a2⟩ := (h1 wf ‹_› :)
  have ⟨wf, b1, b2⟩ := h2 _ _ a1 a2 wf eq
  exact ⟨wf, a1.trans b1, b2⟩

protected theorem M.WF.mono {x : StateM EquivManager β}
    (h1 : M.WF env Us Δ m x P) (h2 : ∀ a m', m ≤ m' → P a m' → Q a m') :
    M.WF env Us Δ m x Q := by
  simpa using h1.bind fun _ _ a1 a2 => .pure (h2 _ _ a1 a2)

protected theorem M.WF.bind_le {x : StateM EquivManager β} {f : β → StateM EquivManager γ}
    (h1 : M.WF env Us Δ m x P) (le : m₀ ≤ m)
    (h2 : ∀ a m', m₀ ≤ m' → P a m' → M.WF env Us Δ m' (f a) Q) :
    M.WF env Us Δ m (x >>= f) Q := h1.bind fun _ _ a1 => h2 _ _ (le.trans a1)

protected theorem M.WF.andM {x y : StateM EquivManager Bool}
    (h1 : M.WF env Us Δ m x fun b _ => b → P)
    (h2 : ∀ {m}, M.WF env Us Δ m y fun b _ => b → Q) :
    M.WF env Us Δ m (x <&&> y) fun b _ => b → P ∧ Q := by
  refine h1.bind fun b _ _ h1 => ?_; cases b <;> [exact .pure nofun; skip]
  refine h2.mono fun _ _ _ h2 h => ⟨h1 rfl, h2 h⟩

theorem find.WF : M.WF env Us Δ m (EquivManager.find i) fun j m => m.uf.Equiv i j := by
  intro wf a m'; simp [StateT.run, find]; split <;> rintro ⟨⟩
  · refine ⟨⟨?_, ?_⟩, ⟨by simp [UnionFind.equiv_find], id⟩, ?_⟩
    · simp; exact wf.wf
    · simp [UnionFind.equiv_find]; exact wf.defeq
    · simp [UnionFind.equiv_find]; exact .rfl
  · exact ⟨wf, .rfl, .rfl⟩

theorem merge.WF (wf : m.WF env Us Δ)
    (he : IsDefEqE env Us Δ e₁ e₂)
    (hi : m.toNodeMap[e₁]? = some i) (hj : m.toNodeMap[e₂]? = some j) :
    (merge m i j).WF env Us Δ ∧ m ≤ merge m i j := by
  simp [merge]; iterate 2 split <;> [skip; exact ⟨wf, .rfl⟩]
  refine ⟨⟨?_, ?_⟩, ⟨by simp [UnionFind.equiv_union]; exact .inl, by simp⟩⟩
  · simp; exact wf.wf
  · simp [UnionFind.equiv_union]
    rintro _ _ _ _ h1 h2 (h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩)
    · exact wf.defeq h1 h2 h3
    · refine (wf.defeq h1 hi h3).trans he |>.trans (wf.defeq hj h2 h4)
    · exact (wf.defeq h1 hj h3).trans he.symm |>.trans (wf.defeq hi h2 h4)

theorem toNode.WF :
    M.WF env Us Δ m (EquivManager.toNode e) fun n m => m.toNodeMap[e]? = some n := by
  intro wf a m'; simp [StateT.run, toNode]; split <;> rintro ⟨⟩ <;> [exact ⟨wf, .rfl, ‹_›⟩; skip]
  refine ⟨{ wf {i} := ?_, defeq h1 h2 h3 := ?_ }, ⟨by simp, ?_⟩, by simp⟩
  · simp [Std.HashMap.getElem?_insert]
    refine ⟨fun h => ?_, fun ⟨_, h⟩ => ?_⟩
    · obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 h
      · have ⟨e', h⟩ := wf.wf.1 h
        exists e'; rwa [if_neg]; intro eq
        rename_i hn _ _; exact hn _ (Std.HashMap.getElem?_congr eq ▸ h)
      · exact ⟨e, by simp⟩
    · split at h
      · cases h; apply Nat.lt_succ_self
      · exact Nat.lt_succ_of_lt (wf.wf.2 ⟨_, h⟩)
  · simp [Std.HashMap.getElem?_insert] at h1 h2 h3
    split at h1 <;> split at h2 <;> rename_i a1 a2
    · exact .relevant <| .of_eqv <| BEq.trans (BEq.symm a1) a2
    · cases h1; cases Nat.ne_of_gt (wf.wf.2 ⟨_, h2⟩) (h3.eq_of_ge_size (Nat.le_refl _))
    · cases h2; cases Nat.ne_of_gt (wf.wf.2 ⟨_, h1⟩) (h3.symm.eq_of_ge_size (Nat.le_refl _))
    · exact wf.defeq h1 h2 h3
  · simp [Std.HashMap.getElem?_insert]
    intro _ _ h; rwa [if_neg]; rename_i h' _ _
    exact fun eq => h' _ (Std.HashMap.getElem?_congr eq ▸ h)

theorem isEquiv.WF :
    M.WF env Us Δ m (isEquiv useHash e₁ e₂) fun b _ => b → IsDefEqE env Us Δ e₁ e₂ := by
  unfold isEquiv; extract_lets F1 F2 F3
  split <;> [exact .pure fun _ => ptrEqExpr_eq ‹_› ▸ .rfl; skip]
  simp [F3]; split <;> [exact .pure nofun; skip]
  simp [F2]; split
  · rename_i h; refine .pure ?_
    unfold Expr.isBVar at h; split at h <;> cases h.1; split at h <;> cases h.2
    simp [Expr.bvarIdx!]; rintro ⟨⟩; exact .rfl
  unfold F1
  refine toNode.WF.bind fun i₁ _ _ a1 => find.WF.bind fun j₁ _ le₁ a2 => ?_
  refine toNode.WF.bind fun i₂ _ le₂ b1 => find.WF.bind fun j₂ m₀ le₃ b2 => ?_
  refine .stateWF fun wf => ?_
  replace a1 := le₁.trans le₂ |>.trans le₃ |>.toNodeMap a1
  replace a2 := le₂.trans le₃ |>.uf a2
  replace b1 := le₃.toNodeMap b1
  extract_lets F4 F5
  split
  · rename_i h; simp at h; cases h; refine .pure fun _ => wf.defeq a1 b1 (a2.trans b2.symm)
  have {m b} (le₄ : m₀ ≤ m) (H : b = true → IsDefEqE env Us Δ e₁ e₂) :
      M.WF env Us Δ m (F4 b) fun b _ => b → IsDefEqE env Us Δ e₁ e₂ := by
    dsimp only [F4]; split <;> [skip; exact .pure H]
    intro wf a _; simp; rintro ⟨⟩
    replace a1 := le₄.toNodeMap a1; replace a2 := le₄.uf a2
    replace b1 := le₄.toNodeMap b1; replace b2 := le₄.uf b2
    have ⟨r₁, hr₁⟩ := wf.wf.1 <| a2.lt_size.1 <| wf.wf.2 ⟨_, a1⟩
    have ⟨r₂, hr₂⟩ := wf.wf.1 <| b2.lt_size.1 <| wf.wf.2 ⟨_, b1⟩
    suffices IsDefEqE env Us Δ r₁ r₂ from have ⟨wf, h⟩ := merge.WF wf this hr₁ hr₂; ⟨wf, h, H⟩
    exact (wf.defeq a1 hr₁ a2).symm.trans <| .trans (H ‹_›) (wf.defeq b1 hr₂ b2)
  simp; unfold F5; split
  · apply this .rfl; simp; rintro rfl rfl; exact .rfl
  · apply this .rfl; simp; rintro rfl; exact .rfl
  · apply this .rfl; simp; rintro rfl; exact .rfl
  · apply this .rfl; simp; rintro rfl; exact .rfl
  · apply this .rfl; simp; rintro rfl; exact .rfl
  · exact .bind (.andM isEquiv.WF isEquiv.WF) fun _ _ le H =>
      this le fun hb => .app (H hb).1 (H hb).2
  · exact .bind (.andM isEquiv.WF isEquiv.WF) fun _ _ le H =>
      this le fun hb => .lam (H hb).1 (H hb).2
  · exact .bind isEquiv.WF fun _ _ le H => this le fun hb => .mdata (H hb)
  · exact .bind (.andM isEquiv.WF isEquiv.WF) fun _ _ le H =>
      this le fun hb => .forallE (H hb).1 (H hb).2
  · exact .bind (.andM (.pure id) isEquiv.WF) fun _ _ le H =>
      this le fun hb => (by simpa using (H hb).1) ▸ .proj (H hb).2
  · exact .bind (.andM isEquiv.WF <| .andM isEquiv.WF isEquiv.WF) fun _ _ le H =>
      this le fun hb => .letE (H hb).1 (H hb).2.1 (H hb).2.2
  · exact .pure nofun

end EquivManager

namespace TypeChecker.Inner

open EquivManager in
theorem addEquiv.WF {c : VContext} {s : VState} (he₁ : c.TrExprS e₁ e') (he₂ : c.TrExpr e₂ e') :
    RecM.WF c s (modify fun st => { st with eqvManager := st.eqvManager.addEquiv e₁ e₂ })
      fun _ _ => True := by
  rintro _ mwf wf _ _ ⟨⟩
  let ⟨_, _, a1, a2, ewf, a4⟩ := wf.ectx
  refine ⟨{ s with toState := _ }, rfl, .rfl, { wf with ectx := ⟨_, _, a1, a2, ?_, a4⟩ }, trivial⟩
  simp [addEquiv]; split; rename_i h1; split; rename_i h2
  have ⟨ewf, b2, b3⟩ := toNode.WF ewf h1
  have ⟨ewf, c2, c3⟩ := toNode.WF ewf h2
  refine (merge.WF ewf ?_ (c2.toNodeMap b3) c3).1
  exact .defeq (he₁.weakFV' c.Ewf a2 a1) (he₂.weakFV' c.Ewf a2 a1)

theorem isDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  refine (isDefEqCore.WF he₁ he₂).bind fun b _ _ hb => ?_
  simp; split
  · exact (addEquiv.WF he₁ ⟨_, he₂, (hb ‹_›).symm⟩).map fun _ _ _ _ => hb
  · exact .pure hb
