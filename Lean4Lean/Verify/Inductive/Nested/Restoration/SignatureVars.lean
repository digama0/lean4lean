import Lean4Lean.Theory.Inductive.RestorationNames


/-! (Ported from the source branch's `Theory/Typing/SignatureVars.lean`, without the case
schema.) Syntactic facts about the bvar spines `InductiveSignature.vars`, their
restoration and lifting, and the generic universe levels of a case schema. -/

namespace Lean4Lean.InductiveSignature

@[simp] theorem length_vars (n k : Nat) : (vars n k).length = n := by simp [vars]

theorem vars_zero (nf : Nat) :
    vars nf 0 = ((List.range nf).reverse).map VExpr.bvar := by
  simp [vars]

theorem mem_vars {count below x : Nat} (h1 : below ≤ x) (h2 : x < below + count) :
    VExpr.bvar x ∈ vars count below := by
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range]
  exact ⟨x - below, by omega, by congr 1; omega⟩

theorem vars_map_liftN_hi (count below n k : Nat) (h : k ≤ below) :
    (vars count below).map (fun e => e.liftN n k) = vars count (below + n) := by
  simp only [vars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  simp only [VExpr.liftN, liftVar]
  rw [if_neg (by omega)]
  congr 1; omega

theorem vars_map_liftN_lo (count below n k : Nat) (h : below + count ≤ k) :
    (vars count below).map (fun e => e.liftN n k) = vars count below := by
  simp only [vars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  simp only [VExpr.liftN, liftVar]
  rw [if_pos (by omega)]

theorem vars_inst_last (n : Nat) (arg : VExpr) :
    (vars (n + 1) 0).map (·.inst arg n) = arg.liftN n :: vars n 0 := by
  simp only [vars, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, List.map_map, Function.comp_def,
    Nat.zero_add, VExpr.inst]
  rw [show VExpr.instVar n arg n = arg.liftN n by simp [VExpr.instVar]]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi : i < n := List.mem_range.mp (List.mem_reverse.mp hi)
  simp [VExpr.instVar, show i < n by omega]

theorem Restoration.mapM_expr_vars (r : Restoration) (count below : Nat) :
    (vars count below).mapM r.expr = some (vars count below) := by
  unfold vars
  generalize (List.range count).reverse = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    simpa [List.mapM_cons, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using ih

theorem Restoration.expr_bvar_mkApps {r : Restoration} {i : Nat} {args : List VExpr}
    {out : VExpr} (h : r.expr (.mkApps (.bvar i) args) = some out) :
    ∃ args', args.mapM r.expr = some args' ∧ out = .mkApps (.bvar i) args' := by
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [bind, Option.bind_eq_some_iff, List.append_nil] at h
  obtain ⟨args', hargs, h⟩ := h
  simp only [Restoration.expr.go, Option.some.injEq] at h
  exact ⟨args', hargs, h.symm⟩

end Lean4Lean.InductiveSignature
