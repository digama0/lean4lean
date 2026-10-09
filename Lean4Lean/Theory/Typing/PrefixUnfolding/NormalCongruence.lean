import Lean4Lean.Theory.Typing.PrefixUnfolding.Layout
import Lean4Lean.Theory.Typing.NormalSubstitution
import Lean4Lean.Theory.Typing.PrefixUnfolding.Abstraction
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.PrefixUnfolding.Arity

namespace Lean4Lean.VEnv
open VExpr Params InductiveSignature InductiveSignature.RecursorData
variable [Params]

omit [Params] in
theorem etaOpen_spine (n : Nat) (fn : VExpr) :
    etaOpen n fn = mkApps (fn.liftN n) (vars n 0) := by
  induction n generalizing fn with
  | zero => simp [etaOpen, vars, mkApps, liftN_zero]
  | succ n ih =>
    rw [etaOpen, ih]
    have hv : vars (n+1) 0 = .bvar n :: vars n 0 := by
      simp only [vars, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, Nat.zero_add]
    rw [hv]
    simp only [lift, liftN, liftN_liftN, Nat.add_comm 1]
    rfl

omit [Params] in
theorem ConstSpineDefEq.symm {env : VEnv} (H : ConstSpineDefEq env U Γ actual expected) :
    ConstSpineDefEq env U Γ expected actual := by
  obtain ⟨n, ls, ls', a, a', ha, ha', hw, hw', he, hs⟩ := H
  exact ⟨n, ls', ls, a', a, ha', ha, hw', hw,
    Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip he),
    Lean4Lean.List.Forall₂.imp (fun _ _ h => IsDefEqU.symm h) (Lean4Lean.List.Forall₂.flip hs)⟩

theorem ConstSpineDefEq.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstSpineDefEq env univs Γ a b)
    (H' : ConstSpineDefEq env univs Γ b c) : ConstSpineDefEq env univs Γ a c := by
  obtain ⟨n, ls, ls', as, bs, ha, hb, hw, hw', he, hs⟩ := H
  obtain ⟨n', ls₁, ls₂, bs', cs, hb', hc, hw₁, hw₂, he', hs'⟩ := H'
  have hh := congrArg VExpr.getAppFnArgs (hb.symm.trans hb')
  rw [spine_mkApps_exact _ _ rfl, spine_mkApps_exact _ _ rfl] at hh
  have ⟨hh, hargs⟩ := Prod.mk.inj hh
  cases hh
  subst bs'
  exact ⟨n, ls, ls₂, as, cs, ha, hc, hw, hw₂,
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ h h' => h.trans h') he he',
    Lean4Lean.List.Forall₂.trans (T := env.IsDefEqU univs Γ)
      (fun _ _ _ h h' => h.trans henv hΓ h') hs hs'⟩

theorem ConstSpineDefEq.instOuter_normal {name : Name} {levels : List VLevel} (hΓ : OnCtx Γ (env.IsType univs))
    (hhead : e = mkApps (.const name levels) templates)
    (hc : List.Forall₂ (NormalEqF η Γ) captures captures')
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
  have hA : HasType env univs Γ (InductiveSignature.instantiateParams template captures) A := by
    rw [instantiateParams_eq_instOuter]
    exact hA
  simpa only [instantiateParams_eq_instOuter] using (NormalEqF.instantiateParams_args hΓ hc hA).defeq hΓ


private theorem etaOpen_match {domains : List VExpr} (hpos : 0 < domains.length) (_hΓ : OnCtx Γ (env.IsType univs))
    {name : Name} {levels : List VLevel}
    (hlevels : ∀ l ∈ levels, l.WF univs)
    (hargs : List.Forall₂ (NormalEqF η Γ) args args')
    (hctor : NormalEqF η (domains.reverse ++ Γ) ctor ctor')
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
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
       Lean4Lean.List.Forall₂.imp (fun _ _ h => (h.weakN
        (show Ctx.LiftN domains.length 0 Γ (domains.reverse ++ Γ) from
          .zero _ (by simp))).defeq hctx) hargs
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [List.mem_map, vars, List.mem_reverse, List.mem_range] at he
      obtain ⟨e, ⟨i, hi, rfl⟩, rfl⟩ := he
      exact ⟨_, .bvar (Lookup.ofLt (by simp only [List.length_append, List.length_reverse, liftVar, Nat.zero_add, Nat.not_lt_zero, ↓reduceIte]; omega)).2⟩
  · exact .cons (hctor.defeq hctx) .nil


/-- Re-check the unfolding of a fixed installed recursor equation after normal changes to its
supplied arguments. The concrete constant head is preserved, and every
capture and reconstructed constructor remains tied to the generated unfolding. -/
theorem UnfoldingCheck.congr_normal {name : Name} {levels : List VLevel}
    {p p' : PrefixUnfolding} (hΓ : OnCtx Γ (env.IsType univs))
    (H : UnfoldingCheck env univs Γ (mkApps (.const name levels) args) p)
    (hlen : p.domains.length = p'.domains.length)
    (heq : p.equation = p'.equation) (hbody : p.equationBody = p'.equationBody)
    (hlevels : p.levels = p'.levels)
    (ha : List.Forall₂ (NormalEqF η Γ) args args')
    (hcaptures : List.Forall₂ (NormalEqF η (p.domains.reverse ++ Γ)) p.captures p'.captures)
    (hctor : NormalEqF η (p.domains.reverse ++ Γ) p.constructor p'.constructor)
    (hsource : HasType env univs Γ (mkApps (.const name levels) args') p'.type)
    (hhead : ∃ n ls as, p.equationBody.lhs = mkApps (.const n ls) as) :
    UnfoldingCheck env univs Γ (mkApps (.const name levels) args') p' ∧
      NormalEqF η Γ p.rhs p'.rhs := by
  obtain ⟨_, hh⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, H.source_typed⟩
  have hs := NormalEqF.mkApps_spine hΓ (.refl hh) ha H.source_typed
  have htypes := (((hs.defeq hΓ).of_l henv hΓ H.source_typed).hasType.2).uniqU henv hΓ hsource
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W := IsDefEqU.wrapForalls_context henv hΓ (.zero : IsDefEqCtx env univs Γ Γ Γ) hlen htypes
  have hcLength := Lean4Lean.List.Forall₂.length_eq hcaptures
  have hpos : 0 < p.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  obtain ⟨hl, hr, ht⟩ := CaseSchema.EquationBody.extract_sound H.equation_body
  have hiota := IsDefEq.extra_instOuter henv hctx H.equation_present H.levels_wf
    H.levels_length hl.symm hr.symm ht.symm H.captures_length H.captures_typed
  constructor
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
      have hn := NormalEqF.instantiateParams_args
        (e := p.equationBody.domains[j].instL p.levels) hctx (List.forall₂_take hcaptures j)
        (by simpa only [instantiateParams_eq_instOuter] using hdom)
      have ht := ((List.forall₂_getElem hcaptures j hj₀ hj).defeq hctx).of_l henv hctx hold
      have hnew := ht.hasType.2.defeqU_r henv hctx (by
        simpa only [instantiateParams_eq_instOuter] using hn.defeq hctx)
      apply HasType.defeqDFC henv W
      simpa only [← hbody, ← hlevels] using hnew
    · obtain ⟨P, hp, hm, hc⟩ := H.major_prop
      exact ⟨P, hp.defeqDFC henv W, hm.defeqDFC henv W,
        (((hctor.defeq hctx).of_l henv hctx hc).hasType.2).defeqDFC henv W⟩
    · apply ConstSpineDefEq.defeqDFC henv W
      rw [← hlen, ← hbody, ← hlevels]
      obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv.ordered hΓ hh
      have hleft := etaOpen_match (name := name) hpos hΓ hw ha hctor hctx
      obtain ⟨n, ls, as, hhead⟩ := hhead
      have hright := ConstSpineDefEq.instOuter_normal hctx
        (by rw [hhead, instL_mkApps]; rfl) hcaptures hiota.hasType.1
      exact (hleft.symm.trans hctx H.recursor_lhs).trans hctx hright
  · have hn := NormalEqF.instantiateParams_args
      (e := p.equationBody.rhs.instL p.levels) hctx hcaptures
      (by simpa only [instantiateParams_eq_instOuter] using hiota.hasType.2)
    unfold PrefixUnfolding.rhs
    rw [← hbody, ← hlevels]
    exact NormalEqF.wrapLams_congr hΓ hlen htypes hn

/-- The unfolding of an installed recursor equation transports along normal equality of
its supplied arguments; no new capture or index-alignment certificate is needed. -/
theorem PrefixUnfold.congr_normal {name : Name} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs registry Γ name levels args rhs)
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    ∃ rhs', PrefixUnfold env univs registry Γ name levels args' rhs' ∧ NormalEqF η Γ rhs rhs' := by
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
    have hs := NormalEqF.mkApps_spine hΓ (.refl hhead) ha replay.source_typed
    have hsource := hregistered.prefixType henv hΓ hw hg'
      (by simpa only [hname] using
        (show VExpr.WF env univs Γ _ from
          ⟨_, ((hs.defeq hΓ).of_l henv hΓ replay.source_typed).hasType.2⟩))
    have replayData : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program := by
      simpa only [hname] using replay
    obtain ⟨hcaptures, hctor⟩ := replayData.singleton_rel_components (R := NormalEqF η)
      (fun _ h => .refl h) (fun W h => h.weakN W)
      (fun hΓ hf hs ht => NormalEqF.mkApps_spine hΓ hf hs ht)
      (fun hΓ hs ht => NormalEqF.instantiateParams_args hΓ hs ht) henv hΓ hg hg' ha
    have hnative := hregistered.singletonEquation_body_head he hb
    obtain ⟨replay', hnormal⟩ := replay.congr_normal hΓ hlength heq hbody (hl.trans hl'.symm)
      ha hcaptures hctor (by simpa only [hname] using hsource) hnative
    exact ⟨_, .intro hlookup hregistered hname hlarge hw hz hg' replay', hnormal⟩

end Lean4Lean.VEnv

namespace Lean4Lean.QuotPrefixUnfolding
open VExpr InductiveSignature InductiveSignature.RecursorData
variable {levels : List VLevel}

def openedArguments (args : List VExpr) : List VExpr :=
  args.map (·.liftN (6 - args.length)) ++ vars (6 - args.length) 0

def prefixProof (levels : List VLevel) (args : List VExpr) : VExpr :=
  let all := openedArguments args
  mkApps (propInhabitant (levels[0]?.getD .zero))
    [all[0]?.getD default, all[1]?.getD default, all[5]?.getD default]

theorem openedArguments_length (h : args.length ≤ 6) : (openedArguments args).length = 6 := by
  simp [openedArguments, vars]
  omega

theorem equationBody_head
    (H : CaseSchema.EquationBody.extract quotDefEq.lhs quotDefEq.rhs quotDefEq.type = some body) :
    ∃ n ls as, body.lhs = mkApps (.const n ls) as := by
  cases H
  exact ⟨``Quot.lift, VLevel.params 2,
    [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
      mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]], rfl⟩

theorem generate_layout (H : generate levels args = some program) :
    program.domains.length = 6 - args.length ∧
    program.constructor = mkApps (.const ``Quot.mk [levels[0]?.getD .zero])
      [(openedArguments args)[0]?.getD default, (openedArguments args)[1]?.getD default,
        prefixProof levels args] ∧
    program.captures = (openedArguments args).take 5 ++ [prefixProof levels args] := by
  unfold generate at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, _, ⟨domains, result⟩, htake, body, _, H⟩ := H
  cases H
  exact ⟨VExpr.takeForalls_domains_length htake, rfl, rfl⟩

/-- The six displayed binders of Quot.lift fix prefix generation independently
of the supplied terms. This is only generation; the unfolding check retains its typing checks. -/
theorem generate_sameArity (H : generate levels args = some program)
    (hlen : args'.length = args.length) :
    ∃ program', generate levels args' = some program' := by
  obtain ⟨hlevels, hargs, _⟩ := generate_spec H
  obtain ⟨domains, body, hshape, hcount⟩ : ∃ domains body,
      quotLiftConst.type = wrapForalls domains body ∧ domains.length = 6 := by
    exact ⟨(quotLiftConst.type.takeForalls 6).getD ([], .bvar 0) |>.1,
      (quotLiftConst.type.takeForalls 6).getD ([], .bvar 0) |>.2, by decide, by decide⟩
  have hbound : args'.length ≤ (domains.map (VExpr.instL levels)).length := by
    simp only [List.length_map, hcount, hlen]
    omega
  obtain ⟨residual, remaining, result, hsupply, hresidual, hremaining⟩ :=
    supplyType_wrapForalls_exists (body := body.instL levels) hbound
  have hremaining' : remaining.length = 6 - args'.length := by
    simpa only [List.length_map, hcount] using hremaining
  have htake := RecursorData.takeForalls_wrapForalls remaining result
  rw [hremaining'] at htake
  unfold generate
  rw [if_neg (by simp [hlevels, hlen, hargs])]
  rw [hshape, VExpr.instL_wrapForalls]
  simp only [bind, hsupply, Option.bind_some, hresidual, htake]
  exact ⟨_, rfl⟩

end Lean4Lean.QuotPrefixUnfolding

namespace Lean4Lean.VEnv
open VExpr Params InductiveSignature InductiveSignature.RecursorData

/-- The fixed quotient telescope determines the type of every successful
generated prefix whose actual source occurrence is well formed. -/
theorem QuotRegistered.prefixType {env : VEnv} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotRegistered env) (hw : ∀ level ∈ levels, level.WF U)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift levels) args)) :
    env.HasType U Γ (mkApps (.const ``Quot.lift levels) args) program.type := by
  have hlen := (QuotPrefixUnfolding.generate_spec hg).1
  unfold QuotPrefixUnfolding.generate at hg
  split at hg <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, _, hg⟩ := hg
  cases hg
  have hf : env.HasType U Γ (.const ``Quot.lift levels) (quotLiftConst.type.instL levels) :=
    .const H.lift hw hlen
  have hh := hf.supply henv hΓ ht hsupply
  rw [takeForalls_sound htake] at hh
  exact hh

variable [Params]

/-- The concrete quotient selector and every installed-equation capture
respect normal equality of supplied arguments, in the original open telescope. -/
theorem UnfoldingCheck.quot_normal_components {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : UnfoldingCheck env univs Γ (mkApps (.const ``Quot.lift levels) args) program)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (hg' : QuotPrefixUnfolding.generate levels args' = some program')
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      NormalEqF η (program.domains.reverse ++ Γ) program.constructor program'.constructor := by
  obtain ⟨hlen, hctor, hcaptures⟩ := QuotPrefixUnfolding.generate_layout hg
  obtain ⟨hlen', hctor', hcaptures'⟩ := QuotPrefixUnfolding.generate_layout hg'
  have hargs := (QuotPrefixUnfolding.generate_spec hg).2.1
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W : Ctx.LiftN (6 - args.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  have hall : List.Forall₂ (NormalEqF η (program.domains.reverse ++ Γ))
      (QuotPrefixUnfolding.openedArguments args) (QuotPrefixUnfolding.openedArguments args') := by
    unfold QuotPrefixUnfolding.openedArguments
    rw [← halen]
    apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN W) ha
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact .refl (.bvar (Lookup.ofLt (by simp only [List.length_append, List.length_reverse]; omega)).2)
  have hnorm (i : Nat) (hi : i < 6) :
      NormalEqF η (program.domains.reverse ++ Γ)
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
  have hp : NormalEqF η (program.domains.reverse ++ Γ)
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
    exact NormalEqF.mkApps_spine hctx (.refl hfn)
      (.cons (hnorm 0 (by decide)) (.cons (hnorm 1 (by decide)) (.cons (hnorm 5 (by decide)) .nil))) ht
  constructor
  · rw [hcaptures, hcaptures']
    exact List.Forall₂.append' (List.forall₂_take hall 5) (.cons hp .nil)
  · obtain ⟨proposition, _, _, hc⟩ := H.major_prop
    rw [hctor] at hc
    obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv.ordered hctx
      (show VExpr.WF env univs _ _ from ⟨_, hc⟩)
    rw [hctor, hctor']
    exact NormalEqF.mkApps_spine hctx (.refl hhead)
      (.cons (hnorm 0 (by decide)) (.cons (hnorm 1 (by decide)) (.cons hp .nil))) hc

/-- Normal changes to the actual supplied quotient arguments preserve the
generated delta rule and relate its two resulting lambda telescopes. -/
theorem QuotPrefixUnfold.congr_normal {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (ha : List.Forall₂ (NormalEqF η Γ) args args') :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels args' rhs' ∧ NormalEqF η Γ rhs rhs' := by
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
    have hs := NormalEqF.mkApps_spine hΓ (.refl hhead) ha replay.source_typed
    have ht := hr.prefixType henv hΓ hw hg'
      ⟨_, ((hs.defeq hΓ).of_l henv hΓ replay.source_typed).hasType.2⟩
    obtain ⟨hcaptures, hctor⟩ := replay.quot_normal_components hΓ hg hg' ha
    have hnative : ∃ n ls as, program.equationBody.lhs = mkApps (.const n ls) as := by
      rw [he] at hb
      exact QuotPrefixUnfolding.equationBody_head hb
    obtain ⟨replay', hnormal⟩ := replay.congr_normal hΓ hlen heq hbody (hl.trans hl'.symm)
      ha hcaptures hctor ht hnative
    exact ⟨_, .intro hr hw hz hg' replay', hnormal⟩

end Lean4Lean.VEnv
