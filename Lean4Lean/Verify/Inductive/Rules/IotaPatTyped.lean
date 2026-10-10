import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.Inductive.SignatureData

/-! # Generated equations as typed ι rules

`VInductDecl.WF.rules_wf` types every recursor rule as a schematic ι rule (`VEnv.PatTyped` of
`SimplePattern.iota` with reduct `SimplePattern.iotaRHS`): a *generic* redex, whose holes used
by the reduct are exactly the variables of a context, and the reduct, at a common type. The
generator's equation for a constructor (`InductiveSignature.Instance.equation`) is the closed
λ-wrapped form of exactly that judgment: its domains are the parameters, motives, minors and
fields; its left-hand side body is the recursor applied to the variables of the first three
groups, the constructor indices and the constructor applied to parameter and field variables;
its right-hand side is a closed template. This file restates `VDefEq.WF` of a generated
equation as `PatTyped` (PORT_PLAN section 2.3): open the λ-telescope (`HasType.wrapLams_inv`)
for the redex, and apply the closed reduct to the variables of the telescope
(`HasType.mkApps_wrapForalls_bvarSpine`) for the reduct. -/

namespace Lean4Lean

open VExpr

/-! ### Variables -/

namespace InductiveSignature

theorem vars_length (count below : Nat) : (vars count below).length = count := by
  simp [vars]

theorem vars_getElem (count below i : Nat) (hi : i < (vars count below).length) :
    (vars count below)[i] = .bvar (below + (count - 1 - i)) := by
  simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]

theorem vars_append (a b : Nat) : vars a b ++ vars b 0 = vars (a + b) 0 := by
  apply List.ext_getElem
  · simp [vars_length]
  · intro i h1 h2
    simp only [vars_length] at h1 h2
    rw [vars_getElem _ _ _ (by simp [vars_length]; omega)]
    by_cases hi : i < a
    · rw [List.getElem_append_left (by simp [vars_length]; omega), vars_getElem]
      congr 1; omega
    · rw [List.getElem_append_right (by simp [vars_length]; omega), vars_getElem]
      simp only [vars_length]; congr 1; omega

theorem vars_zero_eq (n : Nat) : vars n 0 = (List.range n).reverse.map .bvar := by
  simp [vars]

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

end InductiveSignature

/-! ### Generic instances of a reduct -/

theorem Pattern.RHS.uses_foldl_var {p : Pattern} {x : p.Path} :
    ∀ (l : List p.Path) (f : p.RHS),
      ((l.map Pattern.RHS.var).foldl Pattern.RHS.app f).Uses x ↔ f.Uses x ∨ x ∈ l
  | [], f => by simp
  | y :: l, f => by
    rw [List.map_cons, List.foldl_cons, uses_foldl_var l]
    simp only [Pattern.RHS.Uses, List.mem_cons]
    constructor
    · rintro ((h | rfl) | h)
      · exact .inl h
      · exact .inr (.inl rfl)
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inl h)
      · exact .inl (.inr rfl)
      · exact .inr h

/-- A template applied to holes whose values are, in order, the variables of a context of
length `n` (`#(n-1) .. #0`) is a generic instance over that context. -/
theorem Pattern.RHS.generic_foldl_var {p : Pattern} {c : VExpr} {hc : c.Closed}
    {m2 : p.Path → VExpr} {l : List p.Path} {n : Nat}
    (hl : l.map m2 = InductiveSignature.vars n 0) :
    ((l.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed c hc)).Generic m2 n := by
  have hlen : l.length = n := by
    have := congrArg List.length hl; simpa [InductiveSignature.vars_length] using this
  have hval : ∀ i (hi : i < l.length), m2 l[i] = .bvar (n - 1 - i) := by
    intro i hi
    have := List.getElem_of_eq hl (by simpa using hi)
    rw [List.getElem_map, InductiveSignature.vars_getElem] at this
    simpa using this
  have huses : ∀ x, ((l.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed c hc)).Uses x ↔
      x ∈ l := fun x => by
    rw [Pattern.RHS.uses_foldl_var]; simp [Pattern.RHS.Uses]
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun i hi => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ((huses x).1 hx)
    exact ⟨n - 1 - i, by omega, hval i hi⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ((huses x).1 hx)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ((huses y).1 hy)
    rw [hval i hi, hval j hj] at hxy
    have : i = j := by injection hxy; omega
    subst this; rfl
  · refine ⟨l[n - 1 - i]'(by omega), (huses _).2 (List.getElem_mem _), ?_⟩
    rw [hval _ (by omega)]; congr 1; omega

/-- The holes of an ι reduct, read through a match of the redex, are the recursor prefix
followed by the constructor's fields. -/
theorem SimplePattern.iotaPaths_map {r c : Name} {k nind cnp nf : Nat}
    {m2 : (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern.Path → VExpr}
    {recArgs ctorArgs : List VExpr} (h1 : recArgs.length = k + nind)
    (h2 : ctorArgs.length = cnp + nf)
    (hg1 : ∀ i (hi : i < k + nind),
      m2 (Sum.inl (Pattern.varN_pathOf (k+nind) i hi)) = recArgs[i]'(h1 ▸ hi))
    (hg2 : ∀ i (hi : i < cnp + nf),
      m2 (Sum.inr (Pattern.varN_pathOf (cnp+nf) i hi)) = ctorArgs[i]'(h2 ▸ hi)) :
    (iotaPaths r c k nind cnp nf).map m2 = recArgs.take k ++ ctorArgs.drop cnp := by
  have e1 : (iotaPaths r c k nind cnp nf).map m2 =
      (List.range k).pmap
        (fun i (hi : i < k+nind) => m2 (Sum.inl (Pattern.varN_pathOf (k+nind) i hi)))
        (fun _ hi => by have := List.mem_range.1 hi; omega) ++
      (List.range nf).pmap
        (fun j (hj : cnp+j < cnp+nf) => m2 (Sum.inr (Pattern.varN_pathOf (cnp+nf) (cnp+j) hj)))
        (fun _ hj => by have := List.mem_range.1 hj; omega) := by
    unfold iotaPaths
    exact (List.map_append ..).trans
      (congr (congrArg (· ++ ·) (List.map_pmap ..)) (List.map_pmap ..))
  rw [e1]
  congr 1
  · apply List.ext_getElem
    · simp [List.length_take]; omega
    · intro t ht1 ht2
      simp only [List.getElem_pmap, List.getElem_range, List.getElem_take]
      exact hg1 t _
  · apply List.ext_getElem
    · simp [List.length_drop]; omega
    · intro t ht1 ht2
      simp only [List.getElem_pmap, List.getElem_range, List.getElem_drop]
      exact hg2 (cnp + t) _

open InductiveSignature in
/-- The closed λ-wrapped form of an ι rule types it as a schematic rule. The left-hand side
is `λ doms. r (vars k) idx (c cps (vars nf))` — the recursor applied to the variables of the
first `k` domains, `nind` arbitrary index terms and the constructor applied to `cnp` arbitrary
parameter terms and the variables of the last `nf` domains — and the right-hand side is a
closed template, both at the type `∀ doms. T`. Then the generic redex (the open left-hand
side) and the reduct (the template applied to all `k + nf` variables) share the type `T`
in the context of the domains. -/
theorem VEnv.patTyped_iota_of_wrapped {env : VEnv} (henv : env.WF) {U : Nat}
    {doms : List VExpr} {T : VExpr} {r c : Name} {k nind cnp nf : Nat} {ls : List VLevel}
    {idx cps : List VExpr} {rhs : VExpr} (hc : rhs.Closed)
    (hdoms : doms.length = k + nf) (hidx : idx.length = nind) (hcps : cps.length = cnp)
    (hlhs : env.HasType U []
      (wrapLams doms (mkApps (.const r (VLevel.params U))
        (vars k nf ++ idx ++ [mkApps (.const c ls) (cps ++ vars nf 0)])))
      (wrapForalls doms T))
    (hrhs : env.HasType U [] rhs (wrapForalls doms T)) :
    env.PatTyped (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern
      (SimplePattern.iotaRHS' r c k nind cnp nf rhs hc, .true) := by
  have hrec : (vars k nf ++ idx).length = k + nind := by simp [vars_length, hidx]
  have hctor : (cps ++ vars nf 0).length = cnp + nf := by simp [vars_length, hcps]
  obtain ⟨g1, hm1, hg1⟩ := Pattern.matches_varN_const (c := r) (ls := VLevel.params U)
    (k + nind) _ hrec
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := c) (ls := ls) (cnp + nf) _ hctor
  have hmatch := Pattern.Matches.app hm1 hm2
  have hpaths := SimplePattern.iotaPaths_map (m2 := Sum.elim g1 g2) hrec hctor hg1 hg2
  have hargs : (vars k nf ++ idx).take k ++ (cps ++ vars nf 0).drop cnp = vars (k + nf) 0 := by
    rw [List.take_append_of_le_length (by simp [vars_length]),
      List.take_of_length_le (by simp [vars_length]),
      List.drop_append_of_le_length (by simp [hcps]),
      List.drop_of_length_le (by simp [hcps]), List.nil_append, vars_append]
  rw [hargs] at hpaths
  have hopen := (VerifyInductive.VEnv.HasType.wrapLams_inv henv (ctx := []) trivial hlhs).2
  have hred := VerifyInductive.VEnv.HasType.mkApps_wrapForalls_bvarSpine henv.ordered hrhs
  rw [hc.liftN_eq (Nat.zero_le _)] at hred
  have hlw : rhs.LevelWF U := (IsDefEq.levelWF hrhs trivial).1
  refine ⟨U, doms.reverse ++ [], _, Sum.elim g1 g2, T, ?_, ?_, hopen, ?_⟩
  · rw [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil]
    exact hmatch
  · simp only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero, hdoms]
    exact Pattern.RHS.generic_foldl_var hpaths
  · have happ := SimplePattern.iotaRHS'_apply r c k nind cnp nf rhs hc (VLevel.params U)
      (Sum.elim g1 g2) hrec hctor hg1 hg2
    rw [hargs, hlw.instL_id, ← hdoms, vars_zero_eq] at happ
    rw [happ]
    exact hred

namespace InductiveSignature.Instance

variable {s : InductiveSignature}

theorem equationDomains_length (g : Instance s) (index : Fin s.constructors.size) :
    (g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + s.constructors.size)).length =
      s.params.length + s.families.size + s.constructors.size +
        s.constructors[index].fields.length := by
  simp [params, motives, minors, insertBinders, fieldTypes]; omega

/-- The generated equation of a constructor, when well formed, is a typed ι rule of the
recursor of its owner (`VInductDecl.WF.rules_wf`'s judgment), with the generated counts:
`np` parameters, one motive per family, one minor per constructor, the constructor's indices,
and the constructor's own parameter and field counts. -/
theorem equation_patTyped (g : Instance s) {env : VEnv} (henv : env.WF)
    (index : Fin s.constructors.size) (hwf : (g.equation index).WF env)
    (hc : (g.equation index).rhs.Closed) :
    env.PatTyped
      (SimplePattern.iota (g.recursorName s.constructors[index].owner)
        (s.params.length + s.families.size + s.constructors.size +
          s.constructors[index].indices.length)
        s.constructors[index].name
        (s.params.length + s.constructors[index].fields.length)).toPattern
      (SimplePattern.iotaRHS (g.recursorName s.constructors[index].owner)
        s.constructors[index].name s.params.length s.families.size s.constructors.size
        s.constructors[index].indices.length s.params.length
        s.constructors[index].fields.length (g.equation index).rhs hc, .true) := by
  obtain ⟨hlhs, hrhs⟩ := hwf
  simp only [equation, constructorApp, recursorHead, Nat.add_zero] at hlhs hrhs hc ⊢
  rw [← Nat.add_assoc] at hlhs
  exact VEnv.patTyped_iota_of_wrapped henv hc (equationDomains_length g index)
    (by simp) (by simp [vars_length]) hlhs hrhs

end InductiveSignature.Instance

end Lean4Lean
