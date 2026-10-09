import Lean4Lean.Theory.Typing.PrefixUnfolding.Arity
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr CaseSchema
variable {levels : List VLevel}

def openedArguments (data : RecursorData) (args : List VExpr) : List VExpr :=
  let remaining := data.majorOffset + 1 - args.length
  args.map (·.liftN remaining) ++ vars remaining 0

/-- The fields reconstructed by the singleton unfolding at the supplied arguments. -/
noncomputable def singletonFields (data : RecursorData) (S : SingletonLayout) (E : PropElim)
    (levels : List VLevel) (args : List VExpr) : List VExpr :=
  (PropElim.occ S (data.propParams levels) E ((data.openedArguments args).take data.numParams)
    (((data.openedArguments args).drop data.indexOffset).take data.numIndices) (.bvar 0)
    S.fields.length).2

theorem singletonUnfolding_layout {data : RecursorData} {env : VEnv}
    (H : data.singletonUnfolding env U levels args = some program) :
    ∃ S E, data.singletonLayout env levels = some S ∧ data.propElim levels = some E ∧
      program.domains.length = data.majorOffset + 1 - args.length ∧
      program.constructor = VExpr.mkApps E.ctor
        ((data.openedArguments args).take data.numParams ++ data.singletonFields S E levels args) ∧
      program.captures = (data.openedArguments args).take data.indexOffset ++
        data.singletonFields S E levels args := by
  unfold singletonUnfolding at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, residual, _, ⟨domains, result⟩, htake,
    ⟨ctor, fields⟩, hrecon, equation, heq, body, hbody, H⟩ := H
  split at H <;> try contradiction
  cases H
  unfold singletonReconstruction at hrecon
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hrecon
  obtain ⟨S, hS, E, hE, hctor, hfields⟩ := hrecon
  refine ⟨S, E, hS, hE, VExpr.takeForalls_domains_length htake, ?_, ?_⟩
  · rw [← hctor, ← hfields]; rfl
  · rw [← hfields]; rfl

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

theorem mkApps_arguments_wf (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (mkApps fn args)) :
    VExpr.WF env U Γ fn ∧ ∀ arg ∈ args, VExpr.WF env U Γ arg := by
  induction args generalizing fn with
  | nil => exact ⟨H, by simp⟩
  | cons a args ih =>
    obtain ⟨hf, hargs⟩ := ih H
    obtain ⟨_, _, hf', ha⟩ := hf.app_inv henv.ordered hΓ
    refine ⟨⟨_, hf'⟩, ?_⟩
    intro arg hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ha⟩
    · exact hargs arg hm

private theorem rel_getD_typed {R : VExpr → VExpr → Prop} {l l' : List VExpr} {P : VExpr → Prop}
    (H : List.Forall₂ R l l') (hd : P default → R default default) (k : Nat)
    (hp : P (l.getD k default)) : R (l.getD k default) (l'.getD k default) := by
  induction H generalizing k with
  | nil => exact hd hp
  | cons h _ ih => cases k with
    | zero => exact h
    | succ k => exact ih k hp

private theorem forall₂_of_cond {R : VExpr → VExpr → Prop} {P : VExpr → Prop} {l l' : List VExpr}
    (H : List.Forall₂ (fun e e' => P e → R e e') l l') (hp : ∀ e ∈ l, P e) :
    List.Forall₂ R l l' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h (hp _ (by simp))) (ih fun e he => hp e (by simp [he]))

/-- The singleton reconstruction transports along any relation of its arguments
that is a typed congruence: every reconstructed term that is typed is related. -/
theorem occ_rel {R : VExpr → VExpr → Prop} (henv : env.WF) (hΔ : OnCtx Δ (env.IsType U))
    (refl : ∀ {e A}, HasType env U Δ e A → R e e)
    (mkApps : ∀ {f f' as as' T}, R f f' → List.Forall₂ R as as' →
      HasType env U Δ (VExpr.mkApps f as) T → R (VExpr.mkApps f as) (VExpr.mkApps f' as'))
    (inst : ∀ {cs cs' e T}, List.Forall₂ R cs cs' →
      HasType env U Δ (instantiateParams e cs) T → R (instantiateParams e cs) (instantiateParams e cs'))
    (hps : List.Forall₂ R ps ps') (hidx : List.Forall₂ R idx idx') :
    ∀ i, List.Forall₂ (fun e e' => VExpr.WF env U Δ e → R e e')
        (PropElim.occ S P E ps idx m i).1 (PropElim.occ S P E ps' idx' m i).1 ∧
      List.Forall₂ (fun e e' => VExpr.WF env U Δ e → R e e')
        (PropElim.occ S P E ps idx m i).2 (PropElim.occ S P E ps' idx' m i).2 := by
  intro i
  induction i with
  | zero => exact ⟨.nil, .nil⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [PropElim.occ]
    split
    · rename_i k _
      refine ⟨List.Forall₂.append' ih1 (.cons ?_ .nil), List.Forall₂.append' ih2 (.cons ?_ .nil)⟩
      · rintro ⟨_, ht⟩
        have hw := mkApps_arguments_wf (fn := .const ``Eq.refl _) (args := [_, _]) henv hΔ ⟨_, ht.hasType.1⟩
        obtain ⟨_, hhead⟩ := hw.1
        obtain ⟨_, hα⟩ := hw.2 _ (List.mem_cons_self ..)
        obtain ⟨_, hX⟩ := hw.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        refine mkApps (f := .const ``Eq.refl _) (as := [_, _]) (refl hhead.hasType.1)
          (.cons (refl hα.hasType.1) (.cons ?_ .nil)) ht.hasType.1
        have hX' := hX.hasType.1
        rw [← instantiateParams_eq_instOuter] at hX' ⊢
        rw [← instantiateParams_eq_instOuter]
        exact inst (List.Forall₂.append' hps (List.forall₂_take hidx k)) hX'
      · intro hw
        exact rel_getD_typed (P := VExpr.WF env U Δ) hidx
          (fun ⟨_, h⟩ => refl h.hasType.1) k hw
    · have hnew : (fun e e' => VExpr.WF env U Δ e → R e e')
          (VExpr.mkApps (PropElim.value S P E i) (ps ++ idx ++ [m] ++ (PropElim.occ S P E ps idx m i).1))
          (VExpr.mkApps (PropElim.value S P E i) (ps' ++ idx' ++ [m] ++ (PropElim.occ S P E ps' idx' m i).1)) := by
        rintro ⟨_, ht⟩
        have hw := mkApps_arguments_wf henv hΔ ⟨_, ht.hasType.1⟩
        refine mkApps (refl hw.1.choose_spec.hasType.1) ?_ ht.hasType.1
        refine List.Forall₂.append' (List.Forall₂.append' (List.Forall₂.append' hps hidx)
          (.cons (refl (hw.2 m (by simp)).choose_spec.hasType.1) .nil)) ?_
        exact forall₂_of_cond ih1 fun e he => hw.2 e (by simp [he])
      exact ⟨List.Forall₂.append' ih1 (.cons hnew .nil), List.Forall₂.append' ih2 (.cons hnew .nil)⟩


open RecursorData in
/-- Related supplied arguments give related singleton captures and constructors,
for any typed congruence relation closed under weakening. -/
theorem UnfoldingCheck.singleton_rel_components {R : List VExpr → VExpr → VExpr → Prop}
    (refl : ∀ {Γ e A}, OnCtx Γ (env.IsType U) → HasType env U Γ e A → R Γ e e)
    (weakN : ∀ {n k Γ Γ' a b}, Ctx.LiftN n k Γ Γ' → R Γ a b → R Γ' (a.liftN n k) (b.liftN n k))
    (mkApps : ∀ {Γ f f' as as' T}, OnCtx Γ (env.IsType U) → R Γ f f' →
      List.Forall₂ (R Γ) as as' → HasType env U Γ (VExpr.mkApps f as) T →
      R Γ (VExpr.mkApps f as) (VExpr.mkApps f' as'))
    (inst : ∀ {Γ cs cs' e T}, OnCtx Γ (env.IsType U) →
      List.Forall₂ (R Γ) cs cs' → HasType env U Γ (instantiateParams e cs) T →
      R Γ (instantiateParams e cs) (instantiateParams e cs'))
    {data : RecursorData} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : UnfoldingCheck env U Γ (VExpr.mkApps (.const data.name levels) args) program)
    (hg : data.singletonUnfolding env U levels args = some program)
    (hg' : data.singletonUnfolding env U levels args' = some program')
    (ha : List.Forall₂ (R Γ) args args') :
    List.Forall₂ (R (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      R (program.domains.reverse ++ Γ) program.constructor program'.constructor := by
  obtain ⟨S, E, hS, hE, hlen, hctor, hcapture⟩ := singletonUnfolding_layout hg
  obtain ⟨S', E', hS', hE', hlen', hctor', hcapture'⟩ := singletonUnfolding_layout hg'
  cases hS.symm.trans hS'
  cases hE.symm.trans hE'
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W : Ctx.LiftN (data.majorOffset + 1 - args.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  have hall : List.Forall₂ (R (program.domains.reverse ++ Γ))
      (data.openedArguments args) (data.openedArguments args') := by
    unfold openedArguments
    rw [← halen]
    apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => weakN W h) ha
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he
      have hi' : 0 + i < (program.domains.reverse ++ Γ).length := by
        simp only [List.length_append, List.length_reverse]; omega
      exact refl hctx (.bvar (Lookup.ofLt hi').2)
  have hdrop : ∀ n, List.Forall₂ (R (program.domains.reverse ++ Γ))
      ((data.openedArguments args).drop n) ((data.openedArguments args').drop n) :=
    fun n => List.forall₂_drop hall n
  have hocc := occ_rel (R := R (program.domains.reverse ++ Γ)) (P := data.propParams levels)
    (S := S) (E := E) (m := .bvar 0) henv hctx (refl hctx) (mkApps hctx) (inst hctx)
    (List.forall₂_take hall data.numParams) (List.forall₂_take (hdrop data.indexOffset) data.numIndices)
    S.fields.length
  have hfieldsTyped : ∀ e ∈ data.singletonFields S E levels args,
      VExpr.WF env U (program.domains.reverse ++ Γ) e := by
    intro e he
    have hmem : e ∈ program.captures := by rw [hcapture]; exact List.mem_append_right _ he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    exact ⟨_, H.captures_typed i hi (by rw [← H.captures_length]; exact hi)⟩
  have hfields : List.Forall₂ (R (program.domains.reverse ++ Γ))
      (data.singletonFields S E levels args) (data.singletonFields S E levels args') :=
    forall₂_of_cond hocc.2 hfieldsTyped
  constructor
  · rw [hcapture, hcapture']
    exact List.Forall₂.append' (List.forall₂_take hall _) hfields
  · obtain ⟨proposition, hp, hm, hc⟩ := H.major_prop
    rw [hctor] at hc
    rw [hctor, hctor']
    have hw := mkApps_arguments_wf henv hctx ⟨_, hc⟩
    exact mkApps hctx (refl hctx hw.1.choose_spec.hasType.1)
      (List.Forall₂.append' (List.forall₂_take hall _) hfields) hc

end Lean4Lean.VEnv
