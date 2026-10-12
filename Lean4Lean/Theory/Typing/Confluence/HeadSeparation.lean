import Lean4Lean.Theory.Typing.ProjectionRigidity
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.StoredRuleHeads

/-! # Separation of rule heads along the history

The facts about the rule heads of a well-formed environment that the pattern table of the
confluence engine (`Confluence/Patterns.lean`) needs to be non-overlapping, proved along the
declaration history: a stored equation (the δ rule of a definition or the quotient rule) is
never headed by the head of a registered ι pattern (`WF.defeq_pat_heads`), and no definition
is named `Quot.lift` once the quotient rule is stored (`WF.quotLift_not_definition`). Both hold
because every rule is installed with a head that is fresh at its step, and every earlier rule
head is a declared constant. -/

namespace Lean4Lean.VEnv

variable {env : VEnv}

private def HeadsDisjoint (env : VEnv) : Prop :=
  ∀ df, env.defeqs df → ∀ (p : Pattern) (r : p.RHS × p.Check), env.pats p r →
    ∀ ls, df.lhs.stripLams.getAppFnArgs.1 ≠ .const p.headConst ls

private theorem toDefEq_head (ci : VDefVal) {n : Name} {ls : List VLevel}
    (h : ci.toDefEq.lhs.stripLams.getAppFnArgs.1 = .const n ls) : ci.name = n := by
  simp only [VDefVal.toDefEq, VExpr.stripLams, VExpr.getAppFnArgs] at h
  exact (VExpr.const.inj h).1

private theorem headsDisjoint {ds : List VDecl} (H : env.WF' ds) : HeadsDisjoint env := by
  induction H with
  | empty => intro _ h; cases h
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    intro df hdf p r hp ls
    exact ihCtors df (by simpa using hdf) p r (by simpa using hp) ls
  | @decl d env' ds env hd H ih =>
    have hW : env.WF := ⟨ds, H⟩
    -- a head fresh in `env` is not the head of a pattern of `env`
    have freshPat : ∀ {n : Name}, env.constants n = none → ∀ (p : Pattern)
        (r : p.RHS × p.Check), env.pats p r → n ≠ p.headConst := by
      intro n hn p r hp heq
      obtain ⟨c, hc⟩ := hW.pat_head_declared hp
      rw [← heq, hn] at hc; cases hc
    intro df hdf p r hp ls heq
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 =>
      rw [addConst_defeqs h2] at hdf; rw [addConst_pats h2] at hp
      exact ih df hdf p r hp ls heq
    | «example» _ => exact ih df hdf p r hp ls heq
    | @«def» _ _ ci _ h2 =>
      rw [addDefEq_pats, addConst_pats h2] at hp
      rcases hdf with rfl | hdf
      · exact freshPat (addConst_fresh h2) p r hp (toDefEq_head ci heq)
      · rw [addConst_defeqs h2] at hdf; exact ih df hdf p r hp ls heq
    | mutualDef _ h2 _ =>
      rw [addDefEqs_pats, addConsts_pats h2] at hp
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hdf
      rcases hdf with hm | hdf
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
        exact freshPat (addConst_foldlM_fresh h2 ci hci) p r hp (toDefEq_head ci heq)
      · rw [addConsts_defeqs h2] at hdf; exact ih df hdf p r hp ls heq
    | quot h1 h2 =>
      obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
      rw [addDefEq_pats, addConst_pats a4, addConst_pats a3, addConst_pats a2,
        addConst_pats a1] at hp
      rcases hdf with rfl | hdf
      · have hlift : env.constants ``Quot.lift = none :=
          ((addConst_le a1).trans (addConst_le a2)).constants_eq_none_left (addConst_fresh a3)
        have : quotDefEq.lhs.stripLams.getAppFnArgs.1 =
            .const ``Quot.lift [.param 0, .param 1] := rfl
        rw [this] at heq
        exact freshPat hlift p r hp (VExpr.const.inj heq).1
      · rw [addConst_defeqs a4, addConst_defeqs a3, addConst_defeqs a2,
          addConst_defeqs a1] at hdf
        exact ih df hdf p r hp ls heq
    | induct _ h2 =>
      rw [addInduct_defeqs h2] at hdf
      rcases addInduct_pats_origin h2 hp with hold | ⟨rec, hrec, ru, hru, rfl⟩
      · exact ih df hdf p r hold ls heq
      · rw [SimplePattern.iota_headConst] at heq
        obtain ⟨ci, hci⟩ := hW.defeq_head_declared hdf heq
        rw [addInduct_rec_fresh h2 hrec] at hci; cases hci

/-- **Stored equations and registered patterns have different heads.** -/
theorem WF.defeq_pat_heads (henv : env.WF) {df : VDefEq} (hdf : env.defeqs df)
    {p : Pattern} {r : p.RHS × p.Check} (hp : env.pats p r) (ls : List VLevel) :
    df.lhs.stripLams.getAppFnArgs.1 ≠ .const p.headConst ls :=
  let ⟨_, H⟩ := henv; headsDisjoint H df hdf p r hp ls

/-- A constant heading a stored equation heads no registered pattern. -/
theorem WF.defeq_head_not_pat (henv : env.WF) {df : VDefEq} (hdf : env.defeqs df)
    (hhead : df.lhs.stripLams.getAppFnArgs.1 = .const n ls)
    {p : Pattern} {r : p.RHS × p.Check} (hp : env.pats p r) : p.headConst ≠ n := by
  intro h
  exact henv.defeq_pat_heads hdf hp ls (by rw [hhead, h])

private def QuotLiftUnique (env : VEnv) : Prop :=
  env.defeqs quotDefEq → ∀ df, env.defeqs df → ∀ ls, df.lhs ≠ .const ``Quot.lift ls

private theorem quotLiftUnique {ds : List VDecl} (H : env.WF' ds) : QuotLiftUnique env := by
  induction H with
  | empty => intro h; cases h
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    intro hq df hdf ls
    exact ihCtors (by simpa using hq) df (by simpa using hdf) ls
  | @decl d env' ds env hd H ih =>
    have hW : env.WF := ⟨ds, H⟩
    -- the quotient rule's head is declared
    have liftDeclared : env.defeqs quotDefEq → env.constants ``Quot.lift ≠ none := by
      intro hq hn
      obtain ⟨ci, hci⟩ := hW.defeq_head_declared hq
        (show quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift [.param 0, .param 1]
          from rfl)
      rw [hn] at hci; cases hci
    intro hq df hdf ls heq
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 =>
      rw [addConst_defeqs h2] at hdf hq; exact ih hq df hdf ls heq
    | «example» _ => exact ih hq df hdf ls heq
    | @«def» _ _ ci _ h2 =>
      have hq' : env.defeqs quotDefEq := by
        rcases hq with h | h
        · exact absurd (congrArg VDefEq.lhs h) (by simp [quotDefEq, VDefVal.toDefEq])
        · rwa [addConst_defeqs h2] at h
      rcases hdf with rfl | hdf
      · simp only [VDefVal.toDefEq] at heq
        rw [(VExpr.const.inj heq).1] at h2
        exact liftDeclared hq' (addConst_fresh h2)
      · rw [addConst_defeqs h2] at hdf; exact ih hq' df hdf ls heq
    | mutualDef _ h2 _ =>
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hdf hq
      have hq' : env.defeqs quotDefEq := by
        rcases hq with hm | h
        · obtain ⟨ci, -, h⟩ := List.mem_map.1 hm
          exact absurd (congrArg VDefEq.lhs h) (by simp [quotDefEq, VDefVal.toDefEq])
        · rwa [addConsts_defeqs h2] at h
      rcases hdf with hm | hdf
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
        simp only [VDefVal.toDefEq] at heq
        have hfresh := addConst_foldlM_fresh h2 ci hci
        rw [(VExpr.const.inj heq).1] at hfresh
        exact liftDeclared hq' hfresh
      · rw [addConsts_defeqs h2] at hdf; exact ih hq' df hdf ls heq
    | quot h1 h2 =>
      obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
      rcases hdf with rfl | hdf
      · cases heq
      · rw [addConst_defeqs a4, addConst_defeqs a3, addConst_defeqs a2,
          addConst_defeqs a1] at hdf
        have hlift : env.constants ``Quot.lift = none :=
          ((addConst_le a1).trans (addConst_le a2)).constants_eq_none_left (addConst_fresh a3)
        obtain ⟨ci, hci⟩ := hW.defeq_head_declared hdf
          (show df.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift ls by
            rw [heq]; rfl)
        rw [hlift] at hci; cases hci
    | induct _ h2 =>
      rw [addInduct_defeqs h2] at hdf hq; exact ih hq df hdf ls heq

/-- **No definition is named `Quot.lift` once the quotient rule is stored.** -/
theorem WF.quotLift_not_definition (henv : env.WF) (hq : env.defeqs quotDefEq)
    {df : VDefEq} (hdf : env.defeqs df) (ls : List VLevel) : df.lhs ≠ .const ``Quot.lift ls :=
  let ⟨_, H⟩ := henv; quotLiftUnique H hq df hdf ls

end Lean4Lean.VEnv
