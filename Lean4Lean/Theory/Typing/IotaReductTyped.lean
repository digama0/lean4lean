import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.IotaShapes
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NestedFacts
import Lean4Lean.Theory.Typing.PatsIota

/-! # The reducts of the registered ι rules are typed

`IsDefEq.pat` carries the typing of the reduct as a premise. `VEnv.WF.iotaReductTyped` is the
theorem that makes the premise available: in a well-formed environment and a well-formed
context, the reduct of a typed instance of a registered ι rule is typed at the redex's type.

A registered rule is the ι rule of a rule `ru` of a recursor `rec` of an installed declaration
(`WF'.pats_origin`), read off a restored generated equation `df` of the declaration's
compilation (`VInductDecl.WF.rule_block`), which is typed (`VInductDecl.WF.block_rules_wf`).
The recursor, constructor and equation shapes of the rule (`CompilationData.iota_shapes`) and
the rule's counts (`Model.Nested.rule_counts`) put the instance in the form of
`VIotaRuleTyped.reduct_typed`: the rule's arguments are typed along the equation's telescope
by inversion of the redex's typing (head inversion and uniqueness of typing, weak conclusions),
and the reduct shares the type of the instantiated left-hand side. -/

namespace Lean4Lean

theorem VExpr.forallResult_mkApps_const (c : Name) (ls : List VLevel) (args : List VExpr) :
    (VExpr.mkApps (.const c ls) args).forallResult = VExpr.mkApps (.const c ls) args := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append, VExpr.mkApps_snoc]; rfl

namespace VEnv
open InductiveSignature

/-- **The reducts of the registered ι rules are typed.** -/
theorem WF.iotaReductTyped {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2}
    (hpat : env.pats p r) (hm : p.Matches e m1 m2) (hty : env.HasType U Γ e A) :
    env.HasType U Γ (r.1.apply m1 m2) A := by
  obtain ⟨ds, H⟩ := henv
  have henv : env.WF := ⟨ds, H⟩
  obtain ⟨decl, ds₀, env₀, env₁, -, -, hdecl, hadd, hle, rec, hrec, ru, hru, hc, rfl, rfl⟩ :=
    H.pats_origin hpat
  have hpat' := hpat
  obtain ⟨block, base, expanded, s, g, aux, hcomp, hrecsOf, hbwf, hbase, C, hcont, df, hdf,
    hof⟩ := hdecl.rule_block hrec hru
  -- the generated equation behind the rule
  obtain ⟨gen, hgen, hres⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (List.mapM_eq_some.mp C.equations) df hdf
  obtain ⟨index, -, rfl⟩ := List.mem_map.mp hgen
  -- its constructor's specialization and the rule's counts
  obtain ⟨c0, lvf, Ds0, hS⟩ : ∃ c0 lvf Ds0, Model.Nested.Spec (compilationRestoration decl aux)
      s.constructors[index].name s.params.length c0 lvf Ds0 := by
    obtain ⟨-, -, ⟨t, -, fc, -, -, hcn, -, -, -, hsc⟩ | ⟨a, -, c, -, T, -, hcn, -, -, -, -, -, -,
      hsc⟩⟩ := Model.Nested.ctor_cases C index
    · exact ⟨_, _, _, hcn ▸ hsc⟩
    · exact ⟨_, _, _, hcn ▸ hsc⟩
  obtain ⟨hname, -, hrhs, hk, hnind, -, hnf, -⟩ :=
    Model.Nested.rule_counts hdecl hrecsOf C hrec hru index hS hres hof
  -- the equation is typed
  have hwf : df.WF env := by
    unfold VEnv.addInduct at hadd
    obtain ⟨envR, hR, hrules⟩ := Option.bind_eq_some_iff.1 hadd
    have hle' : envR ≤ env := (addRules_le hrules).trans hle
    have hw := VInductDecl.WF.block_rules_wf hcomp hrecsOf hbwf hR df hdf
    exact ⟨hw.1.mono hle', hw.2.mono hle'⟩
  obtain ⟨head, ⟨Hrec⟩, ⟨fields, ⟨Hctor⟩⟩, ⟨I⟩⟩ :=
    C.iota_shapes henv hcont hbase hrecsOf hadd hle hrec index hname hres hwf
  -- the constructor of the rule is the equation's
  obtain ⟨-, -, -, major, hmajor, hmc, hml⟩ := hof
  rw [I.lhs_eq, VExpr.lamBody_wrapLams, I.lhs_pattern, VExpr.lamBody_mkApps_const,
    VExpr.getAppArgs_mkApps] at hmajor
  simp only [VExpr.getAppArgs, List.nil_append, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at hmajor
  subst hmajor
  rw [VExpr.headConst?_eq_some] at hmc
  obtain ⟨_, hmc⟩ := hmc
  simp only [VExpr.getAppFn_mkApps, VExpr.getAppFn, VExpr.const.injEq] at hmc
  obtain ⟨hctor, -⟩ := hmc
  rw [VExpr.getAppArgs_mkApps] at hml
  simp only [VExpr.getAppArgs, List.nil_append, List.length_append, List.length_map,
    VExpr.bvarRange_length] at hml
  -- the major family is rigid
  have hrigid : env.Rigid head.name := by
    obtain ⟨ci, hci, F, ls, hF, -, hFr⟩ :=
      Model.Nested.patCtor_resultRigid H ⟨_, _, _, _, _, hpat', rfl⟩
    rw [← hctor, Hctor.const] at hci
    cases hci
    rw [Hctor.type_eq, VExpr.forallResult_wrapForalls, VExpr.forallResult_mkApps_const,
      VExpr.getAppFnArgs_mkApps_head] at hF
    simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at hF
    cases hF
    exact hFr
  have hfields := VIotaRuleTyped.fieldCount henv I hwf Hrec Hctor hrigid
  subst hfields
  -- the instance
  have hm' : (SimplePattern.iota rec.name
      (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern.Matches e m1 m2 := hm
  show env.HasType U Γ (Pattern.RHS.apply (p := (SimplePattern.iota rec.name
      (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern) m1 m2
    (SimplePattern.iotaRHS' rec.name ru.ctor (rec.numParams + rec.numMotives + rec.numMinors)
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc)) A
  obtain ⟨recArgs, ctorArgs, lsC, hrA, hcA, rfl, hred⟩ :=
    SimplePattern.iotaRHS_apply_of_matches (hc := hc) hm'
  rw [hred, hrhs]
  have hcp : ru.ctorParams = head.arguments.length := by omega
  rw [hk, hcp]
  have hpre : recArgs.length = s.params.length + s.families.size + s.constructors.size +
      s.families[s.constructors[index].owner].indices.length := by
    omega
  -- the levels of the recursor and the constructor
  have hwfE : VExpr.WF env U Γ ((VExpr.const rec.name m1).mkApps
      (recArgs ++ [(VExpr.const ru.ctor lsC).mkApps ctorArgs])) := ⟨_, hty⟩
  obtain ⟨_, hc0⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ hwfE
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.orderedStrong hΓ hc0
  rw [Hrec.const] at hci
  cases hci
  have hfa : VExpr.WF env U Γ (.app ((VExpr.const rec.name m1).mkApps recArgs)
      ((VExpr.const ru.ctor lsC).mkApps ctorArgs)) := by
    rw [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil] at hwfE; exact hwfE
  obtain ⟨_, _, _, hMt⟩ := hfa.app_inv henv.orderedStrong hΓ
  obtain ⟨_, hcc⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ (⟨_, hMt⟩ :
    VExpr.WF env U Γ ((VExpr.const ru.ctor lsC).mkApps ctorArgs))
  obtain ⟨cci, hcci, hcw, hcl⟩ := HasType.const_inv henv.orderedStrong hΓ hcc
  rw [← hctor, Hctor.const] at hcci
  cases hcci
  have hmaj : env.IsDefEqU U Γ ((VExpr.const ru.ctor lsC).mkApps ctorArgs)
      ((VExpr.const ru.ctor lsC).mkApps
        (ctorArgs.take head.arguments.length ++ ctorArgs.drop head.arguments.length)) := by
    rw [List.take_append_drop]; exact ⟨_, hMt⟩
  rw [← hctor] at hmaj hty
  rw [← Nat.add_assoc]
  exact I.reduct_typed henv hΓ Hrec Hctor hrigid rfl hw hl hpre hty hcl hcw
    (by simp only [List.length_take]; omega) (by simp only [List.length_drop]; omega) hmaj

end VEnv
end Lean4Lean
