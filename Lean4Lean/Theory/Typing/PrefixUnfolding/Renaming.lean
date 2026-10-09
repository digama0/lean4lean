import Lean4Lean.Theory.Typing.SingletonExtraction.Recursor
import Lean4Lean.Theory.Inductive.RecursorPrefixUnfolding
import Lean4Lean.Theory.Typing.PrefixUnfolding.Generation
import Lean4Lean.Theory.Typing.PrefixUnfolding.SpineDefEq

/-! Term renaming of the actual singleton prefix generator and its remaining
binder telescope. -/

namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr CaseSchema
variable {levels : List VLevel} {args : List VExpr} {type : VExpr}

/-- Rename only the outer context of a telescope, fixing each preceding
binder as its domain is visited. -/
def renameDomains : Lift → List VExpr → List VExpr
  | _, [] => []
  | ρ, d :: ds => d.lift' ρ :: renameDomains ρ.cons ds

@[simp] theorem renameDomains_length (ρ : Lift) (ds : List VExpr) :
    (renameDomains ρ ds).length = ds.length := by
  induction ds generalizing ρ <;> simp [renameDomains, *]

private theorem consN_cons (ρ : Lift) (n : Nat) :
    ρ.cons.consN n = ρ.consN (n + 1) := by
  change (ρ.consN 1).consN n = _
  rw [Lift.consN_consN, Nat.add_comm]

theorem supplyType_lift' (H : supplyType args type = some output) :
    supplyType (args.map (·.lift' ρ)) (type.lift' ρ) = some (output.lift' ρ) := by
  induction args generalizing type with
  | nil => cases H; rfl
  | cons arg args ih =>
    cases type <;> try contradiction
    simp only [supplyType, List.map_cons, lift']
    rw [← lift'_inst_hi]
    exact ih H

theorem takeForalls_lift' (H : VExpr.takeForalls count type = some (domains, result)) :
    VExpr.takeForalls count (type.lift' ρ) =
      some (renameDomains ρ domains, result.lift' (ρ.consN count)) := by
  induction count generalizing type domains result ρ with
  | zero => cases H; rfl
  | succ count ih =>
    cases type <;> try contradiction
    simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, hb, he⟩ := H
    cases he
    simp only [lift', VExpr.takeForalls, bind, ih hb, Option.bind_some, Option.pure_def,
      renameDomains, consN_cons]


/-- Every term field records its exact position relative to the remaining
telescope. The stored equation and universe occurrence stay fixed. -/
def PrefixUnfolding.rename (program : PrefixUnfolding) (ρ : Lift) : PrefixUnfolding :=
  { program with
    domains := renameDomains ρ program.domains
    result := program.result.lift' (ρ.consN program.domains.length)
    constructor := program.constructor.lift' (ρ.consN program.domains.length)
    captures := program.captures.map (·.lift' (ρ.consN program.domains.length)) }

private theorem liftN_lift'_consN (e : VExpr) (n : Nat) (ρ : Lift) :
    (e.lift' ρ).liftN n = (e.liftN n).lift' (ρ.consN n) := by
  simp only [← lift'_consN_skipN (k := 0), Lift.consN]
  rw [← lift'_comp, ← lift'_comp, Lift.skipN_comp_consN]
  simp only [Lift.comp_skipN, Lift.refl_comp, Lift.comp]

private theorem vars_lift'_consN (n : Nat) (ρ : Lift) :
    (vars n 0).map (·.lift' (ρ.consN n)) = vars n 0 := by
  have hfix : (ρ.consN n).Fixes n := by
    induction n <;> simp [Lift.consN, Lift.Fixes, *]
  conv => rhs; rw [← List.map_id (l := vars n 0)]
  apply List.map_congr_left
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  apply VExpr.ClosedN.lift'_eq (k := n)
  · simpa only [VExpr.ClosedN, Nat.zero_add] using hi
  · exact hfix

theorem singletonUnfolding_lift' {data : RecursorData} {recType : VExpr} {env : VEnv}
    {packed : List VLevel} (henv : env.WF) (hr : VEnv.RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (htype : data.recursorType = some recType) (hclosed : recType.Closed)
    (H : data.singletonUnfolding env U levels args = some program) :
    data.singletonUnfolding env U levels (args.map (·.lift' ρ)) = some (program.rename ρ) := by
  unfold singletonUnfolding at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, htype, Option.bind_some, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, ⟨constructor, fields⟩, hrecon,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptureCount
  cases H
  have hlen := VExpr.takeForalls_domains_length htake
  have hsupply' := supplyType_lift' (ρ := ρ) hsupply
  rw [(hclosed.instL (ls := levels)).lift'_eq Lift.Fixes.zero] at hsupply'
  have htake' := takeForalls_lift' (ρ := ρ) htake
  have hn : args.length ≤ data.majorOffset := by
    by_cases hn : args.length ≤ data.majorOffset
    · exact hn
    · exact (hguard (by simp [show data.majorOffset < args.length by omega])).elim
  let remaining := data.majorOffset + 1 - args.length
  have hall :
      (args.map (·.lift' ρ)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (·.lift' (ρ.consN remaining)) := by
    simp only [List.map_append, List.map_map, Function.comp_def,
      liftN_lift'_consN, vars_lift'_consN]
  have hallLen : (args.map (·.liftN remaining) ++ vars remaining 0).length = data.majorOffset + 1 := by
    simp only [List.length_append, List.length_map, InductiveSignature.length_vars]; omega
  have hrecon' := singletonReconstruction_lift' (ρ := ρ) (n := remaining) henv hr hlarge hzero hallLen (by omega) hrecon
  rw [← hall] at hrecon'
  dsimp only [remaining] at hrecon'
  simp only [bind, htype, Option.bind_some, hsupply', htake', hrecon', hequation, hbody,
    List.length_map, List.length_append, List.length_take, InductiveSignature.length_vars] at hcaptureCount ⊢
  rw [if_neg hcaptureCount]
  simp only [Option.pure_def, Option.some.injEq, PrefixUnfolding.rename, PrefixUnfolding.mk.injEq,
    hlen, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_take]

theorem wrapLams_renameDomains (domains : List VExpr) (body : VExpr) (ρ : Lift) :
    (wrapLams domains body).lift' ρ =
      wrapLams (renameDomains ρ domains) (body.lift' (ρ.consN domains.length)) := by
  induction domains generalizing ρ with
  | nil => rfl
  | cons domain domains ih =>
    change VExpr.lam (domain.lift' ρ) ((wrapLams domains body).lift' ρ.cons) =
      VExpr.lam (domain.lift' ρ) (wrapLams (renameDomains ρ.cons domains)
        (body.lift' (ρ.consN (domains.length + 1))))
    rw [ih, consN_cons]

theorem wrapForalls_renameDomains (domains : List VExpr) (body : VExpr) (ρ : Lift) :
    (wrapForalls domains body).lift' ρ =
      wrapForalls (renameDomains ρ domains) (body.lift' (ρ.consN domains.length)) := by
  induction domains generalizing ρ with
  | nil => rfl
  | cons domain domains ih =>
    change VExpr.forallE (domain.lift' ρ) ((wrapForalls domains body).lift' ρ.cons) =
      VExpr.forallE (domain.lift' ρ) (wrapForalls (renameDomains ρ.cons domains)
        (body.lift' (ρ.consN (domains.length + 1))))
    rw [ih, consN_cons]

theorem PrefixUnfolding.rename_type (program : PrefixUnfolding) (ρ : Lift) :
    (program.rename ρ).type = program.type.lift' ρ := by
  simp only [PrefixUnfolding.rename, PrefixUnfolding.type, wrapForalls_renameDomains]

theorem PrefixUnfolding.rename_rhs {program : PrefixUnfolding}
    (hbody : program.equationBody.rhs.ClosedN program.captures.length) :
    (program.rename ρ).rhs = program.rhs.lift' ρ := by
  simp only [PrefixUnfolding.rename, PrefixUnfolding.rhs, wrapLams_renameDomains]
  rw [instantiateParams_lift' (hbody.instL (ls := program.levels))]

/-- Context renaming follows exactly the generated residual telescope. -/
theorem renameDomains_context (domains : List VExpr) (W : Ctx.Lift' ρ Γ Γ') :
    Ctx.Lift' (ρ.consN domains.length)
      (domains.reverse ++ Γ) ((renameDomains ρ domains).reverse ++ Γ') := by
  induction domains generalizing ρ Γ Γ' with
  | nil => exact W
  | cons domain domains ih =>
    simpa only [renameDomains, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, consN_cons] using ih (ρ := ρ.cons) W.cons

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.RecursorData

theorem etaOpen_lift' (n : Nat) (e : VExpr) (ρ : Lift) :
    etaOpen n (e.lift' ρ) = (etaOpen n e).lift' (ρ.consN n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [etaOpen_succ, etaOpen_succ, ih]
    simp only [VExpr.lift', Lift.consN, Lift.liftVar]
    exact congrArg (fun fn => fn.app (.bvar 0)) (liftN_lift'_consN _ 1 _)

end Lean4Lean.VEnv
