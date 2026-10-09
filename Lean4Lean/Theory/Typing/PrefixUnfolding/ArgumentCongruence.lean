import Lean4Lean.Theory.Typing.PrefixUnfolding.NormalCongruence

/-! # Prefix unfoldings along related supplied arguments

The singleton and quotient prefix unfoldings are re-checked after the supplied arguments
are changed by any relation with the properties collected in `ArgRel`: typed
reflexivity, weakening, soundness for definitional equality, and congruence
for application spines and simultaneous substitution. Normal equality and each
parallel reduction have these properties. The generated right-hand sides are
lambda telescopes whose bodies are related; their domains are definitionally
equal.
-/

namespace Lean4Lean.VEnv
open VExpr Params InductiveSignature InductiveSignature.RecursorData
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- Untyped congruence relations closed under weakening. -/
structure CongrRel (R : List VExpr → VExpr → VExpr → Prop) : Prop where
  rfl : ∀ {Γ e}, R Γ e e
  app : ∀ {Γ f f' a a'}, R Γ f f' → R Γ a a' → R Γ (.app f a) (.app f' a')
  proj : ∀ {Γ s i m m'}, R Γ m m' → R Γ (.proj s i m) (.proj s i m')
  lam : ∀ {Γ A A' b b'}, R Γ A A' → R (A :: Γ) b b' → R Γ (.lam A b) (.lam A' b')
  forallE : ∀ {Γ A A' b b'}, R Γ A A' → R (A :: Γ) b b' → R Γ (.forallE A b) (.forallE A' b')
  weakN : ∀ {n k Γ Γ' a b}, Ctx.LiftN n k Γ Γ' → R Γ a b → R Γ' (a.liftN n k) (b.liftN n k)

/-- The properties of a relation on arguments used to re-check a prefix unfolding. -/
structure ArgRel (R : List VExpr → VExpr → VExpr → Prop) : Prop where
  refl : ∀ {Γ e A}, OnCtx Γ (env.IsType univs) → Γ ⊢ e : A → R Γ e e
  weakN : ∀ {n k Γ Γ' a b}, Ctx.LiftN n k Γ Γ' → R Γ a b → R Γ' (a.liftN n k) (b.liftN n k)
  defeq : ∀ {Γ a b A}, OnCtx Γ (env.IsType univs) → R Γ a b → Γ ⊢ a : A → Γ ⊢ a ≡ b : A
  mkApps : ∀ {Γ f f' as as' T}, OnCtx Γ (env.IsType univs) → R Γ f f' →
    List.Forall₂ (R Γ) as as' → Γ ⊢ VExpr.mkApps f as : T →
    R Γ (VExpr.mkApps f as) (VExpr.mkApps f' as')
  instantiateParams : ∀ {Γ cs cs' e T}, OnCtx Γ (env.IsType univs) →
    List.Forall₂ (R Γ) cs cs' → Γ ⊢ instantiateParams e cs : T →
    R Γ (instantiateParams e cs) (instantiateParams e cs')

section Congr
variable {R : List VExpr → VExpr → VExpr → Prop}

omit [Params] in
theorem CongrRel.subst_args (I : CongrRel R) {e : VExpr} {σ σ' : VExpr.Subst}
    (hs : ∀ i, σ i = σ' i ∨ R Γ (σ i) (σ' i)) : R Γ (e.subst σ) (e.subst σ') := by
  induction e generalizing Γ σ σ' with
  | bvar i =>
    rcases hs i with he | he
    · rw [VExpr.subst, VExpr.subst, ← he]; exact I.rfl
    · exact he
  | sort | const | elim => exact I.rfl
  | app fn arg ihf iha => exact I.app (ihf hs) (iha hs)
  | proj family index major ih => exact I.proj (ih hs)
  | lam domain body ihd ihb =>
    refine I.lam (ihd hs) (ihb ?_)
    intro i
    cases i with
    | zero => exact .inl (Eq.refl _)
    | succ i =>
      rcases hs i with he | he
      · exact .inl (congrArg VExpr.lift he)
      · exact .inr (I.weakN .one he)
  | forallE domain body ihd ihb =>
    refine I.forallE (ihd hs) (ihb ?_)
    intro i
    cases i with
    | zero => exact .inl (Eq.refl _)
    | succ i =>
      rcases hs i with he | he
      · exact .inl (congrArg VExpr.lift he)
      · exact .inr (I.weakN .one he)

omit [Params] in
theorem CongrRel.instantiateParams_args (I : CongrRel R)
    (hs : List.Forall₂ (R Γ) args args') :
    R Γ (instantiateParams e args) (instantiateParams e args') := by
  apply I.subst_args
  intro i
  have hlen := Lean4Lean.List.Forall₂.length_eq hs
  simp only [← hlen]
  split
  · rename_i hi
    exact .inr (List.forall₂_getElem hs _ (by omega) (by omega))
  · exact .inl (Eq.refl _)

omit [Params] in
theorem CongrRel.mkApps (I : CongrRel R) (hf : R Γ f f')
    (hs : List.Forall₂ (R Γ) args args') : R Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') := by
  induction hs generalizing f f' with
  | nil => exact hf
  | cons h _ ih => exact ih (I.app hf h)

omit [Params] in
theorem CongrRel.wrapLams (I : CongrRel R) (H : R (domains.reverse ++ Γ) body body') :
    R Γ (VExpr.wrapLams domains body) (VExpr.wrapLams domains body') := by
  induction domains generalizing Γ with
  | nil => exact H
  | cons domain domains ih =>
    apply I.lam I.rfl
    apply ih
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H

theorem CongrRel.argRel (I : CongrRel R)
    (hdefeq : ∀ {Γ a b A}, OnCtx Γ (env.IsType univs) → R Γ a b → Γ ⊢ a : A → Γ ⊢ a ≡ b : A) :
    ArgRel R where
  refl _ _ := I.rfl
  weakN := I.weakN
  defeq := hdefeq
  mkApps _ hf hs _ := I.mkApps hf hs
  instantiateParams _ hs _ := I.instantiateParams_args hs

end Congr

section Native
variable {R : List VExpr → VExpr → VExpr → Prop}

private theorem rel_vars (I : ArgRel R) (hΓ : OnCtx Γ (env.IsType univs)) (hn : n ≤ Γ.length) :
    List.Forall₂ (R Γ) (vars n 0) (vars n 0) := by
  apply Lean4Lean.List.Forall₂.rfl
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact I.refl hΓ (.bvar (Lookup.ofLt (by omega)).2)

/-- Related arguments of a typed spine are definitionally equal. -/
theorem ArgRel.forall₂_defeq (I : ArgRel R) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : Γ ⊢ VExpr.mkApps fn args : T) (ha : List.Forall₂ (R Γ) args args') :
    List.Forall₂ (IsDefEqU env univs Γ) args args' := by
  have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, ht⟩
  clear ht
  induction ha with
  | nil => exact .nil
  | cons h _ ih =>
    obtain ⟨_, h1⟩ := hwf _ (List.mem_cons_self ..)
    exact .cons ⟨_, I.defeq hΓ h h1.hasType.1⟩ (ih fun a hm => hwf a (List.mem_cons_of_mem _ hm))

theorem UnfoldingCheck.rel_components (I : ArgRel R) {data : RecursorData}
    {levels : List VLevel} (hΓ : OnCtx Γ (env.IsType univs))
    (H : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (hg' : data.singletonUnfolding env univs levels args' = some program')
    (ha : List.Forall₂ (R Γ) args args') :
    List.Forall₂ (R (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      R (program.domains.reverse ++ Γ) program.constructor program'.constructor :=
  H.singleton_rel_components I.refl I.weakN I.mkApps I.instantiateParams henv hΓ hg hg' ha

theorem ConstSpineDefEq.instOuter_defeq {name : Name} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hhead : e = mkApps (.const name levels) templates)
    (hc : ∀ {template T : VExpr}, Γ ⊢ template.instOuter captures : T →
      Γ ⊢ template.instOuter captures ≡ template.instOuter captures')
    (ht : HasType env univs Γ (e.instOuter captures) type) :
    ConstSpineDefEq env univs Γ (e.instOuter captures) (e.instOuter captures') := by
  subst e
  simp only [instOuter_mkApps, instOuter_const] at ht ⊢
  obtain ⟨_, hconst⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv.ordered hΓ hconst
  refine ⟨name, levels, levels, _, _, rfl, rfl, hw, hw,
    Lean4Lean.List.Forall₂.rfl (fun _ _ => show _ ≈ _ from rfl), ?_⟩
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply Lean4Lean.List.Forall₂.rfl
  intro template hm
  have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, ht⟩ _ (List.mem_map.mpr ⟨template, hm, rfl⟩)
  obtain ⟨A, hA⟩ := hwf
  exact hc hA.hasType.1

private theorem rel_eta_match {domains : List VExpr} (hpos : 0 < domains.length)
    (_hΓ : OnCtx Γ (env.IsType univs))
    {name : Name} {levels : List VLevel}
    (hlevels : ∀ l ∈ levels, l.WF univs)
    (hargs : List.Forall₂ (IsDefEqU env univs Γ) args args')
    (hctor : IsDefEqU env univs (domains.reverse ++ Γ) ctor ctor')
    (_hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    ConstSpineDefEq env univs (domains.reverse ++ Γ)
      (.app (etaOpen (domains.length - 1) (mkApps (.const name levels) args)).lift ctor)
      (.app (etaOpen (domains.length - 1) (mkApps (.const name levels) args')).lift ctor') := by
  rw [etaOpen_spine, etaOpen_spine]
  simp only [lift, liftN_mkApps, liftN]
  refine ⟨name, levels, levels,
    (args.map (·.liftN (domains.length - 1)) |>.map (·.liftN 1)) ++
      (vars (domains.length - 1) 0).map (·.liftN 1) ++ [ctor],
    (args'.map (·.liftN (domains.length - 1)) |>.map (·.liftN 1)) ++
      (vars (domains.length - 1) 0).map (·.liftN 1) ++ [ctor'],
    by simp only [mkApps_append]; rfl, by simp only [mkApps_append]; rfl, hlevels, hlevels,
    Lean4Lean.List.Forall₂.rfl (fun _ _ => show _ ≈ _ from rfl), ?_⟩
  apply List.Forall₂.append'
  · apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      have he : domains.length - 1 + 1 = domains.length := by omega
      simpa only [liftN_liftN, Nat.zero_add, he] using
       Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN henv.ordered
        (show Ctx.LiftN domains.length 0 Γ (domains.reverse ++ Γ) from
          .zero _ (by simp))) hargs
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [List.mem_map, vars, List.mem_reverse, List.mem_range] at he
      obtain ⟨e, ⟨i, hi, rfl⟩, rfl⟩ := he
      exact ⟨_, .bvar (Lookup.ofLt (by simp only [List.length_append, List.length_reverse,
        liftVar, Nat.zero_add, Nat.not_lt_zero, ↓reduceIte]; omega)).2⟩
  · exact .cons hctor .nil

/-- Re-check the unfolding of a fixed installed recursor equation after related changes to its
supplied arguments. -/
theorem UnfoldingCheck.congr_rel (I : ArgRel R) {name : Name} {levels : List VLevel}
    {p p' : PrefixUnfolding} (hΓ : OnCtx Γ (env.IsType univs))
    (H : UnfoldingCheck env univs Γ (mkApps (.const name levels) args) p)
    (hlen : p.domains.length = p'.domains.length)
    (heq : p.equation = p'.equation) (hbody : p.equationBody = p'.equationBody)
    (hlevels : p.levels = p'.levels)
    (ha : List.Forall₂ (R Γ) args args')
    (hcaptures : List.Forall₂ (R (p.domains.reverse ++ Γ)) p.captures p'.captures)
    (hctor : R (p.domains.reverse ++ Γ) p.constructor p'.constructor)
    (hsource : HasType env univs Γ (mkApps (.const name levels) args') p'.type)
    (hhead : ∃ n ls as, p.equationBody.lhs = mkApps (.const n ls) as) :
    UnfoldingCheck env univs Γ (mkApps (.const name levels) args') p' ∧
      IsDefEqU env univs Γ (VExpr.wrapForalls p.domains p.result)
        (VExpr.wrapForalls p'.domains p'.result) ∧
      R (p.domains.reverse ++ Γ)
        (instantiateParams (p.equationBody.rhs.instL p.levels) p.captures)
        (instantiateParams (p'.equationBody.rhs.instL p'.levels) p'.captures) := by
  obtain ⟨_, hh⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, H.source_typed⟩
  have hs := I.mkApps hΓ (I.refl hΓ hh) ha H.source_typed
  have htypes := ((I.defeq hΓ hs H.source_typed).hasType.2).uniqU henv hΓ hsource
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W := IsDefEqU.wrapForalls_context henv hΓ (.zero : IsDefEqCtx env univs Γ Γ Γ) hlen htypes
  have hcLength := Lean4Lean.List.Forall₂.length_eq hcaptures
  have hpos : 0 < p.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  obtain ⟨hl, hr, ht⟩ := CaseSchema.EquationBody.extract_sound H.equation_body
  have hiota := IsDefEq.extra_instOuter henv hctx H.equation_present H.levels_wf
    H.levels_length hl.symm hr.symm ht.symm H.captures_length H.captures_typed
  have hcapDefeq : ∀ {template T : VExpr},
      (p.domains.reverse ++ Γ) ⊢ template.instOuter p.captures : T →
      (p.domains.reverse ++ Γ) ⊢ template.instOuter p.captures ≡
        template.instOuter p'.captures := by
    intro template T hT
    have hT' : (p.domains.reverse ++ Γ) ⊢ instantiateParams template p.captures : T := by
      rwa [instantiateParams_eq_instOuter]
    have := I.defeq hctx (I.instantiateParams hctx hcaptures hT') hT'
    simp only [instantiateParams_eq_instOuter] at this
    exact ⟨_, this⟩
  obtain ⟨P, hp, hm, hc⟩ := H.major_prop
  have hctorDefeq : IsDefEqU env univs (p.domains.reverse ++ Γ) p.constructor p'.constructor :=
    ⟨_, I.defeq hctx hctor hc⟩
  refine ⟨?_, htypes, ?_⟩
  · refine {
      source_typed := hsource
      remaining_nonempty := ?_
      equation_present := heq ▸ H.equation_present
      equation_body := ?_
      levels_wf := hlevels ▸ H.levels_wf
      levels_length := ?_
      captures_length := ?_
      captures_typed := ?_
      major_prop := ?_
      recursor_lhs := ?_ }
    · intro hn
      apply H.remaining_nonempty
      apply List.eq_nil_of_length_eq_zero
      simpa only [hn, List.length_nil] using hlen
    · rw [← heq, ← hbody]
      exact H.equation_body
    · rw [← heq, ← hlevels]
      exact H.levels_length
    · rw [← hcLength, ← hbody]
      exact H.captures_length
    · intro j hj hd
      have hj₀ : j < p.captures.length := by omega
      have hd₀ : j < p.equationBody.domains.length := by simpa only [hbody] using hd
      have hold := H.captures_typed j hj₀ hd₀
      obtain ⟨u, hdom⟩ := hold.isType henv hctx
      have hdom' : (p.domains.reverse ++ Γ) ⊢
          instantiateParams (p.equationBody.domains[j].instL p.levels) (p.captures.take j) :
            .sort u := by
        simpa only [instantiateParams_eq_instOuter] using hdom
      have hn := I.defeq hctx (I.instantiateParams hctx (List.forall₂_take hcaptures j) hdom') hdom'
      have ht := I.defeq hctx (List.forall₂_getElem hcaptures j hj₀ hj) hold
      have hn' : IsDefEqU env univs _ _ _ := ⟨_, hn⟩
      simp only [instantiateParams_eq_instOuter] at hn'
      have hnew := ht.hasType.2.defeqU_r henv hctx hn'
      apply HasType.defeqDFC henv W
      simpa only [← hbody, ← hlevels] using hnew
    · exact ⟨P, hp.defeqDFC henv W, hm.defeqDFC henv W,
        ((I.defeq hctx hctor hc).hasType.2).defeqDFC henv W⟩
    · apply ConstSpineDefEq.defeqDFC henv W
      rw [← hlen, ← hbody, ← hlevels]
      obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv.ordered hΓ hh
      have hleft := rel_eta_match (name := name) hpos hΓ hw
        (I.forall₂_defeq hΓ H.source_typed ha) hctorDefeq hctx
      obtain ⟨n, ls, as, hhead⟩ := hhead
      have hright := ConstSpineDefEq.instOuter_defeq hctx
        (by rw [hhead, instL_mkApps]; rfl) hcapDefeq hiota.hasType.1
      exact (hleft.symm.trans hctx H.recursor_lhs).trans hctx hright
  · have hrhs := hiota.hasType.2
    rw [← instantiateParams_eq_instOuter] at hrhs
    have hn := I.instantiateParams hctx hcaptures hrhs
    rw [← hbody, ← hlevels]
    exact hn

/-- The unfolding of an installed recursor equation transports along related supplied
arguments; its right-hand side is a lambda telescope with related body. -/
theorem PrefixUnfold.congr_rel (I : ArgRel R) {name : Name} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs registry Γ name levels args rhs)
    (ha : List.Forall₂ (R Γ) args args') :
    ∃ rhs', PrefixUnfold env univs registry Γ name levels args' rhs' ∧
      ∃ ds ds' body body' res res', rhs = VExpr.wrapLams ds body ∧
        rhs' = VExpr.wrapLams ds' body' ∧ ds.length = ds'.length ∧
        IsDefEqU env univs Γ (VExpr.wrapForalls ds res) (VExpr.wrapForalls ds' res') ∧
        R (ds.reverse ++ Γ) body body' := by
  cases H with
  | @intro data program hlookup hregistered hname hlarge hw hz hg replay =>
    obtain ⟨program', hg'⟩ := singletonUnfolding_sameArity hg (Lean4Lean.List.Forall₂.length_eq ha).symm
    obtain ⟨_, _, hl, _, he, hb, _⟩ := singletonUnfolding_spec hg
    obtain ⟨_, _, hl', _, he', hb', _⟩ := singletonUnfolding_spec hg'
    have heq : program.equation = program'.equation := Option.some.inj (he.symm.trans he')
    have hbody : program.equationBody = program'.equationBody := by
      rw [heq] at hb
      exact Option.some.inj (hb.symm.trans hb')
    obtain ⟨_, _, _, _, hlen, _, _⟩ := singletonUnfolding_layout hg
    obtain ⟨_, _, _, _, hlen', _, _⟩ := singletonUnfolding_layout hg'
    have hlength : program.domains.length = program'.domains.length := by
      rw [hlen, hlen', Lean4Lean.List.Forall₂.length_eq ha]
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, replay.source_typed⟩
    have hs := I.mkApps hΓ (I.refl hΓ hhead) ha replay.source_typed
    have hsource := hregistered.prefixType henv hΓ hw hg'
      (by simpa only [hname] using
        (show VExpr.WF env univs Γ _ from
          ⟨_, (I.defeq hΓ hs replay.source_typed).hasType.2⟩))
    have replayData : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program := by
      simpa only [hname] using replay
    obtain ⟨hcaptures, hctor⟩ := replayData.rel_components I hΓ hg hg' ha
    have hnative := hregistered.singletonEquation_body_head he hb
    obtain ⟨replay', htypes, hrel⟩ := replay.congr_rel I hΓ hlength heq hbody (hl.trans hl'.symm)
      ha hcaptures hctor (by simpa only [hname] using hsource) hnative
    exact ⟨_, .intro hlookup hregistered hname hlarge hw hz hg' replay', _, _, _, _, _, _,
      rfl, rfl, hlength, htypes, hrel⟩

theorem UnfoldingCheck.quot_rel_components (I : ArgRel R) {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : UnfoldingCheck env univs Γ (mkApps (.const ``Quot.lift levels) args) program)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (hg' : QuotPrefixUnfolding.generate levels args' = some program')
    (ha : List.Forall₂ (R Γ) args args') :
    List.Forall₂ (R (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      R (program.domains.reverse ++ Γ) program.constructor program'.constructor := by
  obtain ⟨hlen, hctor, hcaptures⟩ := QuotPrefixUnfolding.generate_layout hg
  obtain ⟨hlen', hctor', hcaptures'⟩ := QuotPrefixUnfolding.generate_layout hg'
  have hargs := (QuotPrefixUnfolding.generate_spec hg).2.1
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  have W : Ctx.LiftN (6 - args.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  have hall : List.Forall₂ (R (program.domains.reverse ++ Γ))
      (QuotPrefixUnfolding.openedArguments args) (QuotPrefixUnfolding.openedArguments args') := by
    unfold QuotPrefixUnfolding.openedArguments
    rw [← halen]
    apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => I.weakN W h) ha
    · exact rel_vars I hctx (by simp only [List.length_append, List.length_reverse]; omega)
  have hnorm (i : Nat) (hi : i < 6) :
      R (program.domains.reverse ++ Γ)
        ((QuotPrefixUnfolding.openedArguments args)[i]?.getD default)
        ((QuotPrefixUnfolding.openedArguments args')[i]?.getD default) := by
    have hil : i < (QuotPrefixUnfolding.openedArguments args).length := by
      rw [QuotPrefixUnfolding.openedArguments_length (by omega)]
      exact hi
    have hir : i < (QuotPrefixUnfolding.openedArguments args').length := by
      rw [← Lean4Lean.List.Forall₂.length_eq hall]
      exact hil
    simpa only [List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hir, Option.getD_some] using
      List.forall₂_getElem hall i hil hir
  have hp : R (program.domains.reverse ++ Γ)
      (QuotPrefixUnfolding.prefixProof levels args) (QuotPrefixUnfolding.prefixProof levels args') := by
    have hm : QuotPrefixUnfolding.prefixProof levels args ∈ program.captures := by
      rw [hcaptures]
      simp
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    have ht := H.captures_typed i hi (by rw [← H.captures_length]; exact hi)
    rw [he] at ht
    unfold QuotPrefixUnfolding.prefixProof at ht ⊢
    obtain ⟨_, hfn⟩ := VExpr.WF.of_mkApps henv.ordered hctx
      (show VExpr.WF env univs _ _ from ⟨_, ht⟩)
    exact I.mkApps hctx (I.refl hctx hfn)
      (.cons (hnorm 0 (by decide)) (.cons (hnorm 1 (by decide)) (.cons (hnorm 5 (by decide)) .nil))) ht
  constructor
  · rw [hcaptures, hcaptures']
    exact List.Forall₂.append' (List.forall₂_take hall 5) (.cons hp .nil)
  · obtain ⟨proposition, _, _, hc⟩ := H.major_prop
    rw [hctor] at hc
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hctx
      (show VExpr.WF env univs _ _ from ⟨_, hc⟩)
    rw [hctor, hctor']
    exact I.mkApps hctx (I.refl hctx hhead)
      (.cons (hnorm 0 (by decide)) (.cons (hnorm 1 (by decide)) (.cons hp .nil))) hc

theorem QuotPrefixUnfold.congr_rel (I : ArgRel R) {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (ha : List.Forall₂ (R Γ) args args') :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels args' rhs' ∧
      ∃ ds ds' body body' res res', rhs = VExpr.wrapLams ds body ∧
        rhs' = VExpr.wrapLams ds' body' ∧ ds.length = ds'.length ∧
        IsDefEqU env univs Γ (VExpr.wrapForalls ds res) (VExpr.wrapForalls ds' res') ∧
        R (ds.reverse ++ Γ) body body' := by
  cases H with
  | @intro program hr hw hz hg replay =>
    have halen := Lean4Lean.List.Forall₂.length_eq ha
    obtain ⟨program', hg'⟩ := QuotPrefixUnfolding.generate_sameArity hg halen.symm
    obtain ⟨_, _, _, hl, he, hb, _⟩ := QuotPrefixUnfolding.generate_spec hg
    obtain ⟨_, _, _, hl', he', hb', _⟩ := QuotPrefixUnfolding.generate_spec hg'
    have hlen : program.domains.length = program'.domains.length := by
      rw [(QuotPrefixUnfolding.generate_layout hg).1,
        (QuotPrefixUnfolding.generate_layout hg').1, halen]
    have heq : program.equation = program'.equation := he.trans he'.symm
    have hbody : program.equationBody = program'.equationBody := by
      rw [heq] at hb
      exact Option.some.inj (hb.symm.trans hb')
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, replay.source_typed⟩
    have hs := I.mkApps hΓ (I.refl hΓ hhead) ha replay.source_typed
    have ht := hr.prefixType henv hΓ hw hg'
      ⟨_, (I.defeq hΓ hs replay.source_typed).hasType.2⟩
    obtain ⟨hcaptures, hctor⟩ := replay.quot_rel_components I hΓ hg hg' ha
    have hnative : ∃ n ls as, program.equationBody.lhs = mkApps (.const n ls) as := by
      rw [he] at hb
      exact QuotPrefixUnfolding.equationBody_head hb
    obtain ⟨replay', htypes, hrel⟩ := replay.congr_rel I hΓ hlen heq hbody (hl.trans hl'.symm)
      ha hcaptures hctor ht hnative
    exact ⟨_, .intro hr hw hz hg' replay', _, _, _, _, _, _, rfl, rfl, hlen, htypes, hrel⟩

end Native

end Lean4Lean.VEnv
