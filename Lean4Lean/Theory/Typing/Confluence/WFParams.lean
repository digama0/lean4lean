import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.Confluence.QuotCoverage
import Lean4Lean.Theory.Typing.Confluence.SingletonPatCoverage
import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.CanonicalEq

/-! # Confluence of a well-formed environment

The `Params` instance of a well-formed environment (`VEnv.WF.params`), its coverage of the
stored equations (`VEnv.WF.equationCoverage`: the δ rules of the definitions and the quotient
rule) and of the registered ι rules (`VEnv.WF.patCoverage`), and the confluence theorem
`VEnv.WF.church_rosser` for every well-formed environment with canonical `Eq`.

A registered ι rule (`IsDefEq.pat`) fired at a typed instance is a pattern step of the engine
(`ParRed.extra`) unless its recursor is large-eliminating and the source of the instance's
major is `Prop`; that instance is covered by the singleton prefix unfolding
(`VEnv.WF.singletonPatCoverageJ`), proved by an induction along the environment's history
(`VEnv.WF.patCoverageJ`). -/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The stored quotient rule is installed only with the quotient declaration. -/
theorem WF'.quotRegistered {env : VEnv} {ds : List VDecl} (H : env.WF' ds)
    (hq : env.defeqs quotDefEq) : QuotRegistered env := by
  induction H with
  | empty => cases hq
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    exact (ihCtors (by simpa using hq)).mono addProjections_le
  | @decl d env' ds env hd H ih =>
    have old : env.defeqs quotDefEq → QuotRegistered env' := fun h => (ih h).mono hd.le
    have notDef : ∀ ci : VDefVal, quotDefEq ≠ ci.toDefEq := fun ci h => by
      have := congrArg VDefEq.lhs h
      simp [quotDefEq, VDefVal.toDefEq] at this
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 => rw [addConst_defeqs h2] at hq; exact old hq
    | «example» _ => exact ih hq
    | «def» _ h2 =>
      rcases hq with h | h
      · exact (notDef _ h).elim
      · rw [addConst_defeqs h2] at h; exact old h
    | mutualDef _ h2 _ =>
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hq
      rcases hq with hm | h
      · obtain ⟨ci, -, h⟩ := List.mem_map.1 hm; exact (notDef _ h.symm).elim
      · rw [addConsts_defeqs h2] at h; exact old h
    | quot _ h2 =>
      exact ⟨addQuot_quot h2, addQuot_quotMk h2, addQuot_quotLift h2, addQuot_quotInd h2,
        addQuot_defeq h2⟩
    | induct _ h2 => rw [addInduct_defeqs h2] at hq; exact old hq

section
variable {env : VEnv} (henv : env.WF) (U : Nat)

private theorem PatternReductionTrace.of_definition
    (H : PatternReductionTrace env U (DefinitionPattern env.definitionRegistry) Γ left right) :
    PatternReductionTrace env U (ConcretePattern env) Γ left right := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih ih' => exact .trans ih ih'
  | pattern hp hm hc => exact .pattern (.inl hp) hm hc
  | beta => exact .beta
  | app _ _ ih ih' => exact .app ih ih'
  | lam _ ih => exact .lam ih

/-- **Coverage of the stored equations**: the δ rule of a definition and the quotient rule
join at every universe specialization. -/
theorem WF.equationCoverage : @FullEquationCoverage (henv.params U) := by
  letI := henv.params U
  refine ⟨fun {Γ equation levels} hΓ hdf hw hl => ?_⟩
  obtain ⟨ds, H⟩ := henv
  rcases H.defeqs_origin hdf with rfl | ⟨value, hv, rfl⟩
  · have hr := H.quotRegistered hdf
    exact QuotRegistered.equation_covered hΓ hr (.inr (.inl (.intro hr))) hw hl
  · have hlookup := WF.definitionRegistry_of_defeq ⟨ds, H⟩ hv
    have htrace := (DefinitionPattern.equation_trace (U := U) (Γ := Γ) hlookup
      (hv.closed ⟨ds, H⟩) hl).of_definition
    exact ⟨_, _, htrace.parRedS.full, .rfl,
      .refl (IsDefEq.extra (Γ := Γ) hdf hw hl).hasType.2⟩

theorem _root_.Lean4Lean.InductiveSignature.RecursorData.guard_OK {data : RecursorData}
    {p : Pattern} {df : VExpr → VExpr → Prop} {m1 : List VLevel} {m2 : p.Path → VExpr} :
    (data.guard p).OK df m1 m2 ↔
      ¬(data.largeTarget = true ∧ (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero) := by
  unfold RecursorData.guard
  split <;> simp_all [Pattern.Check.OK]

/-- The stage at which a recursor is installed is later than every stage registering a rule of
an earlier recursor: the earlier recursor is a constant of that stage, fresh where it is installed. -/
theorem WF.stage_rank_lt {ds : List VDecl} (H : env.WFH ds env.stages) {p : Pattern}
    {r : p.RHS × p.Check} {i j : Nat} (hi : i < env.stages.length) (hj : j < env.stages.length)
    (hp : env.stages[i].pats p r) {decl : VInductDecl} {env₁ : VEnv} {rec : VRecursor}
    (hadd : env.stages[j].addInduct decl = some env₁) (hrec : rec ∈ decl.recs)
    (hname : rec.name = p.headConst) : i < j := by
  refine Nat.lt_of_not_le fun hji => ?_
  have hle := H.chain hj hi hji
  obtain ⟨c, hc⟩ := (H.stage (List.getElem_mem hi)).1.pat_head_declared hp
  have := hle.constants hc
  rw [← hname, addInduct_rec_fresh hadd hrec] at this
  cases this

/-- **Coverage of the registered ι rules at joinably typed instances**: every such instance
joins its reduct, by one pattern step where the universe guard of its recursor holds, and by
the singleton prefix unfolding where the source of its major is `Prop`. The latter needs the
joins of the definitional equalities of the stage its declaration was installed at, which
cover the rules of earlier stages: the proof is an induction along the environment's chosen
history (`WF.stage_rank_lt`). -/
theorem WF.patCoverageJ (heq : env.HasCanonicalEq) : @FullPatCoverageJ (henv.params U) := by
  letI := henv.params U
  haveI := henv.equationCoverage U
  obtain ⟨ds, H⟩ := henv.stagesH
  -- the rank of a pattern bounds the stages of the installations of its recursor
  let Rank (p : Pattern) (n : Nat) : Prop :=
    ∀ {data decl env₀ env₁ rec i} (hi : i < env.stages.length),
      RecursorRegisteredAt env data decl env₀ env₁ → rec ∈ decl.recs →
      rec.name = p.headConst → env.stages[i] = env₀ → env.stages.length ≤ n + i
  have key : ∀ n, ∀ {p : Pattern} {r : p.RHS × p.Check}, env.pats p r → Rank p n →
      CoverageJ p r := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro p r hp hrank Γ e m1 m2 A chk hΓ hm he hJ hr hall
    obtain ⟨recN, major, ctor, fields, data, rfl, hl, -, -, hG⟩ := henv.pats_guarded hp
    have hred := IsDefEq.pat hp hm he (henv.iotaReductTyped hΓ hp hm he) hr hall
    by_cases hzero : data.largeTarget = true ∧
        (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero
    · refine WF.singletonPatCoverageJ henv U heq hΓ hp
        (by rw [SimplePattern.iota_headConst]; exact hl) hzero.1 hzero.2 hm hred hJ ?_
      intro decl env₀ env₁ rec hAt hstage hrec hrname
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hstage
      have hbound := hrank hi hAt hrec hrname hie
      obtain ⟨base, expanded, g, auxiliaries, block, -, -, -, -, -, -, -, -, hdecl, hadd, -, hle,
        -⟩ := hAt
      have hcov : ∀ {p' : Pattern} {r' : p'.RHS × p'.Check}, env₀.pats p' r' → CoverageJ p' r' := by
        intro p' r' hp'
        have hp'E : env.pats p' r' := (H.stage_le hstage).pats hp'
        have hn : 0 < n := by omega
        have hrk : Rank p' (n - 1) := by
          intro data' decl' env₀' env₁' rec' j hj hAt' hrec' hname' hje
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hadd', -, -, -⟩ := hAt'
          have hlt := WF.stage_rank_lt H hi hj (hie ▸ hp') (hje ▸ hadd') hrec' hname'
          omega
        intro Γ' e' m1' m2' A' chk' hΓ' hm' he' hJ' hr' hall'
        exact ih (n - 1) (by omega) hp'E hrk hΓ' hm' he' hJ' hr' hall'
      intro base E
      exact stage_types_joins hstage hdecl hadd hle hcov
    · have hok : (data.guard _).OK (IsDefEqU env U Γ) m1 m2 := RecursorData.guard_OK.mpr hzero
      have hstep : ParRed Γ e (r.1.apply m1 m2) :=
        ParRed.extra (r := (r.1, data.guard _)) (.inr (.inr hG)) hm hok fun _ => .rfl
      exact ⟨_, _, .tail .rfl (.core hstep), .rfl, .refl hred.hasType.2⟩
  exact ⟨fun hΓ hp hm he hJ hr hall =>
    key env.stages.length hp (fun _ _ _ _ _ => by omega) hΓ hm he hJ hr hall⟩

/-- **Coverage of the registered ι rules**, from coverage at joinably typed instances. -/
theorem WF.patCoverage (heq : env.HasCanonicalEq) : @FullPatCoverage (henv.params U) := by
  letI := henv.params U
  haveI := henv.equationCoverage U
  haveI := henv.patCoverageJ U heq
  exact FullPatCoverageJ.toFull

end

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv

/-- **Church-Rosser for definitional equality.** In a well-formed environment with canonical
`Eq`, two definitionally equal terms reduce, in the full presentation, to normally equal terms:
terms equal up to universe levels, proof irrelevance and eta.

Canonical `Eq` types the singleton prefix unfolding at a universe specialization whose source
is `Prop` (`WF.singletonPatCoverage`): the proof fields of the reconstructed constructor are
extracted by the recursor itself into `Prop`, with the earlier data fields cast along `Eq`. -/
theorem WF.church_rosser {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂' := by
  letI := henv.params U
  haveI := henv.equationCoverage U
  haveI := henv.patCoverage U heq
  obtain ⟨-, -, h⟩ := IsDefEq.full_church_rosser (Γ := Γ) hΓ H
  exact h

end Lean4Lean.VEnv
