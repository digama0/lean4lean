import Lean4Lean.Theory.Typing.Confluence.SingletonCoverage
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Compiled
import Lean4Lean.Theory.Typing.EqTyping

/-! # The generated equation of a registered recursor, as a registered rule

On the ι pattern calculus the generated equations of a compiled block are not stored: each is
registered as the ι pattern of its recursor rule. This file proves what the singleton prefix
unfolding needs of such an equation: it is typed (`RecursorRegistered.equation_typed`, from the
block's typing `VInductBlock.WF`), and, for a declaration without nested auxiliaries, it is
realised by its registered rule at every typed instance of its telescope
(`RecursorRegistered.patEquation_of_empty`: the instance is an instance of the rule's pattern,
`IsDefEq.pat` applies, and the rule's reduct is the equation's right-hand side applied to the
telescope, which beta-reduces to its body). -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

variable {env : VEnv}

/-- **The generated equations of a registered recursor are typed.** -/
theorem RecursorRegistered.equation_typed {data : RecursorData} (H : RecursorRegistered env data)
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    (hgen : data.equation index = some equation) :
    env.HasType equation.uvars [] equation.lhs equation.type ∧
      env.HasType equation.uvars [] equation.rhs equation.type := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hr, _, hu, hl, ht, _, hadd, hrecs, he, hbwf⟩ := H
  have hinst := RecursorRegistered.recursorInstance_eq hdata hu hl ht
  have hg : (compilationRestoration source auxiliaries).equation (g.equation index) =
      some equation := by
    simpa only [RecursorData.equation, hinst, hr] using hgen
  have hmem := RecursorRegistered.equation_mem_rules hdata index hg
  have hcomp : source.CompilesTo installBase block := .replay (.intro hdata hprior) hbase hbwf
  unfold VEnv.addInduct at hadd
  obtain ⟨envR, hR, hrules⟩ := Option.bind_eq_some_iff.1 hadd
  have hle : envR ≤ env := (addRules_le hrules).trans he
  have hwf := VInductDecl.WF.block_rules_wf hcomp hrecs hbwf hR equation hmem
  exact ⟨hwf.1.mono hle, hwf.2.mono hle⟩

theorem _root_.Lean4Lean.VExpr.lamArity_wrapLams_app (domains : List VExpr) (f a : VExpr) :
    (VExpr.wrapLams domains (.app f a)).lamArity = domains.length := by
  induction domains with
  | nil => rfl
  | cons _ _ ih => simp [VExpr.wrapLams, VExpr.lamArity] at ih ⊢; exact ih

theorem _root_.Lean4Lean.VExpr.lamArity_wrapLams_mkApps_bvar (domains : List VExpr) (k : Nat)
    (args : List VExpr) :
    (VExpr.wrapLams domains (VExpr.mkApps (.bvar k) args)).lamArity = domains.length := by
  induction domains with
  | nil =>
    rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
    · rfl
    · rw [List.concat_eq_append, VExpr.mkApps_append]; rfl
  | cons _ _ ih => simp [VExpr.wrapLams, VExpr.lamArity] at ih ⊢; exact ih

theorem _root_.Lean4Lean.VExpr.instOuter_app' (f a : VExpr) :
    ∀ args : List VExpr, (VExpr.app f a).instOuter args = .app (f.instOuter args) (a.instOuter args)
  | [] => rfl
  | b :: bs => by simp only [VExpr.instOuter_cons, VExpr.inst]; exact instOuter_app' _ _ bs

/-- **The generated equation of a registered recursor without nested auxiliaries is realised
by its registered rule.** -/
theorem RecursorRegistered.patEquation_of_empty (henv : env.WF) {data : RecursorData}
    (H : RecursorRegistered env data) (hrest : data.schema.restoration = {})
    {index : Fin data.schema.signature.constructors.size}
    {equation : VDefEq} (hgen : data.equation index = some equation) :
    env.PatEquation equation := by
  obtain ⟨hlT, hrT⟩ := H.equation_typed hgen
  have hlc : equation.lhs.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env equation.uvars [] _ from ⟨_, hlT⟩) trivial
  have hrc : equation.rhs.Closed :=
    VExpr.WF.closedN henv.ordered (show VExpr.WF env equation.uvars [] _ from ⟨_, hrT⟩) trivial
  have htc : equation.type.Closed := by
    obtain ⟨u, ht⟩ := hlT.isType henv.ordered (show OnCtx [] (env.IsType equation.uvars) from trivial)
    exact VExpr.WF.closedN henv.ordered (show VExpr.WF env equation.uvars [] _ from ⟨_, ht⟩) trivial
  refine ⟨hlc, hrc, htc, ?_⟩
  intro U Γ ls body T args hΓ hls hlen hbody hlenArgs hargs hT
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hr, _, hu, hl, ht, hwf, hadd, hrecs, he, hbwf⟩ := H
  have hinst := RecursorRegistered.recursorInstance_eq hdata hu hl ht
  have hg : (compilationRestoration source auxiliaries).equation (g.equation index) =
      some equation := by
    simpa only [RecursorData.equation, hinst, hr] using hgen
  have hmem := RecursorRegistered.equation_mem_rules hdata index hg
  obtain ⟨r, hrm, ru, hru, hof⟩ := hrecs.rules_total equation hmem
  obtain ⟨hc, hp⟩ := addInduct_pats_of_rule hadd hrm hru
  have hp' := he.pats hp
  -- the explicit generated equation
  have hres0 : compilationRestoration source auxiliaries = {} := hr.symm.trans hrest
  rw [hres0, Restoration.equation_empty] at hg
  cases Option.some.inj hg
  subst hinst
  generalize hgdef : data.recursorInstance = g at *
  let s := data.schema.signature
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length
  let D := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let idx := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  let fn := VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (np + extra) nf ++ idx)
  let major := VExpr.mkApps (.const ctor.name g.levels) (vars np (extra + nf) ++ vars nf 0)
  let lb := VExpr.app fn major
  have hlb : (g.equation index).lhs = VExpr.wrapLams D lb := by
    simp only [Instance.equation, Instance.recursorHead, Instance.constructorApp, D, lb, fn,
      major, idx, ctor, s, np, nf, extra, Nat.add_zero]
    rw [List.append_assoc (vars _ _), ← List.append_assoc, VExpr.mkApps_append]; rfl
  obtain ⟨rb, hrb, krb, argsrb, hrbShape⟩ : ∃ rb, (g.equation index).rhs = VExpr.wrapLams D rb ∧
      ∃ k args', rb = VExpr.mkApps (.bvar k) args' :=
    ⟨_, rfl, _, _, rfl⟩
  obtain ⟨tb, htb⟩ : ∃ tb, (g.equation index).type = VExpr.wrapForalls D tb := ⟨_, rfl⟩
  have hDlen : D.length = np + extra + nf := by
    simp only [D, Instance.params, Instance.motives, Instance.minors, insertBinders,
      InductiveSignature.fieldTypes, List.length_append, List.length_map, List.length_zipIdx,
      Array.length_toList, np, nf, extra, s, ctor]
    omega
  -- the extracted body is the generated telescope
  have hext := InductiveSignature.extract_wrap_const (lhs := lb) (rhs := rb) (type := tb)
    (name := g.recursorName ctor.owner) (levels := VLevel.params g.uvars)
    (by simp [lb, fn, VExpr.getAppFnArgs_app, getAppFnArgs_mkApps_head]) D
  rw [hlb, hrb, htb, hext] at hbody
  have hbd : body = ⟨D, lb, rb, tb⟩ := (Option.some.inj hbody).symm
  rw [hbd] at hlenArgs hargs hT ⊢
  simp only at hlenArgs hargs hT ⊢
  -- the rule's counts
  have hof1 := hof.1
  have hof2 := hof.2.1
  have hof3 := hof.2.2.1
  obtain ⟨maj, hmaj1, hmaj2, hmaj3⟩ := hof.2.2.2
  rw [hlb, VExpr.lamBody_wrapLams_app] at hof2 hof3 hmaj1
  have hrname : r.name = g.recursorName ctor.owner := by
    simp only [lb, VExpr.headConst?, VExpr.getAppFn_app, fn, VExpr.getAppFn_mkApps,
      VExpr.getAppFn] at hof2
    exact (Option.some.inj hof2).symm
  simp only [lb, VExpr.getAppArgs_app, fn, VExpr.getAppArgs_mkApps, VExpr.getAppArgs,
    List.nil_append, List.length_append, List.length_singleton] at hof3 hmaj1
  have hmajEq : maj = major := by
    simpa using hmaj1.symm
  subst hmajEq
  have hctorName : ru.ctor = ctor.name := by
    simp only [major, VExpr.headConst?, VExpr.getAppFn_mkApps, VExpr.getAppFn] at hmaj2
    exact (Option.some.inj hmaj2).symm
  have hcpnf : ru.ctorParams + ru.nfields = np + nf := by
    simp only [major, VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append,
      List.length_append] at hmaj3
    simpa [vars] using hmaj3.symm
  have hvl : ∀ n k, (vars n k).length = n := fun n k => by simp [vars]
  have hmajorIdx : r.getMajorIdx = np + extra + idx.length := by
    rw [hvl] at hof3; omega
  -- the constructor's parameters are the declaration's
  have hnp : np = source.nparams := hdata.model.nparams.trans hdata.nparams
  have hcp : ru.ctorParams = np := by
    rcases hwf.rules_ctorParams r hrm ru hru with ⟨c, hcm, hcn, hcp⟩ | ⟨D', hD', c, hcm, hcn, hcp⟩
    · rw [hcp, hnp]
    · exfalso
      -- without auxiliaries the rule's constructor is a constructor of the declaration, fresh
      -- where its containers are installed
      have haux : auxiliaries = [] := by
        have h := congrArg Restoration.recursors hres0
        simp only [compilationRestoration] at h
        cases auxiliaries with
        | nil => rfl
        | cons a as => simp at h
      rcases hdata.constructor_name_cases index with ⟨c', hc'm, hc'n⟩ | ⟨a, ha, -⟩
      · rw [hres0] at hc'n
        simp only [Restoration.headName, Restoration.recursorName] at hc'n
        have hcn' : c.name = c'.name := by
          rw [← hcn, hctorName]; exact hc'n
        obtain ⟨type', htype', hctor'⟩ := List.mem_flatMap.1 hc'm
        have hfresh := addInduct_ctor_fresh hadd htype' hctor'
        obtain ⟨type, htype, hctor⟩ := List.mem_flatMap.1 hcm
        cases hD' with
        | intro _ _ _ _ _ hadd' hle' =>
          have := hle'.constants (addInduct_ctor_find hadd' htype hctor)
          rw [hcn', hfresh] at this
          cases this
      · rw [haux] at ha; cases ha
  have hnf' : ru.nfields = nf := by omega
  -- the rule's binder count is the telescope's
  have hk : r.numParams + r.numMotives + r.numMinors = np + extra := by
    obtain ⟨j, hj, A, -, -, -, hshape⟩ := hwf.rule_shape r hrm ru hru
    have h1 := hshape.1
    rw [← hof1, hrb, hrbShape, VExpr.lamArity_wrapLams_mkApps_bvar, hDlen, hnf'] at h1
    omega
  -- the instance of the left side
  have hlsU : ls.length = g.uvars := hlen
  let f : VExpr → VExpr := fun a => (a.instL ls).instOuter args
  have hargsLen : args.length = np + extra + nf := hlenArgs.trans hDlen
  have hvars : ∀ n k, n + k ≤ args.length →
      (vars n k).map f = (args.drop (args.length - (n + k))).take n := by
    intro n k h
    have : (vars n k).map f = ((vars n k).map (VExpr.instL ls)).map (·.instOuter args) := by
      simp [f, List.map_map, Function.comp_def]
    rw [this, vars_instL, map_instOuter_vars _ _ _ h]
  let A' := (vars (np + extra) nf ++ idx).map f
  let B' := (vars np (extra + nf) ++ vars nf 0).map f
  have he : (lb.instL ls).instOuter args =
      .app (VExpr.mkApps (.const r.name ls) A')
        (VExpr.mkApps (.const ru.ctor (g.levels.map (·.inst ls))) B') := by
    simp only [lb, fn, major, VExpr.instL, VExpr.instL_mkApps, VExpr.instOuter_mkApps,
      VExpr.instOuter_const, A', B', f, List.map_map, Function.comp_def, hrname, hctorName]
    simp only [VExpr.instOuter_app', VExpr.instOuter_mkApps, VExpr.instOuter_const,
      VLevel.inst_map_id hlsU, List.map_map, Function.comp_def]
  have hA'len : A'.length = r.getMajorIdx := by
    simp only [A', List.length_map, List.length_append, hvl]
    omega
  have hB'len : B'.length = ru.ctorParams + ru.nfields := by
    simp only [B', List.length_map, List.length_append, hvl]
    omega
  obtain ⟨g1, hm1, hg1⟩ := Pattern.matches_varN_const (c := r.name) (ls := ls) _ A' hA'len
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := ru.ctor)
    (ls := g.levels.map (·.inst ls)) _ B' hB'len
  let m2 : (SimplePattern.iota r.name r.getMajorIdx ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern.Path → VExpr := Sum.elim g1 g2
  have hm : (SimplePattern.iota r.name r.getMajorIdx ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern.Matches ((lb.instL ls).instOuter args) ls m2 := by
    rw [he]; exact .app hm1 hm2
  have hpat := IsDefEq.pat (chk := []) hp' hm hT (henv.iotaReductTyped hΓ hp' hm hT) trivial
    (by simp)
  -- the rule's reduct is the right side applied to the telescope
  have happly := SimplePattern.iotaRHS'_apply r.name ru.ctor
    (r.numParams + r.numMotives + r.numMinors) r.numIndices ru.ctorParams ru.nfields ru.rhs hc ls m2
    (recArgs := A') (ctorArgs := B') hA'len hB'len (fun i hi => hg1 i hi) (fun i hi => hg2 i hi)
  have htake : A'.take (r.numParams + r.numMotives + r.numMinors) = args.take (np + extra) := by
    rw [hk]
    simp only [A', List.map_append]
    rw [List.take_left' (by simp [hvl]), hvars _ _ (by omega)]
    simp [show args.length - (np + extra + nf) = 0 by omega]
  have hdrop : B'.drop ru.ctorParams = args.drop (np + extra) := by
    rw [hcp]
    simp only [B', List.map_append]
    rw [List.drop_left' (by simp [hvl]), hvars _ _ (by omega), show args.length - (nf + 0) =
      np + extra by omega]
    exact List.take_of_length_le (by simp; omega)
  rw [htake, hdrop, List.take_append_drop] at happly
  have hrhs : ru.rhs.instL ls = VExpr.wrapLams (D.map (VExpr.instL ls)) (rb.instL ls) := by
    rw [← hof1, hrb, VExpr.instL_wrapLams]
  rw [hrhs] at happly
  have hsim := SimAt.mkApps_wrapLams henv hΓ (args := args) (doms := D.map (VExpr.instL ls))
    (body := rb.instL ls) (by simp [hargsLen, hDlen])
  have hred : env.IsDefEq U Γ ((lb.instL ls).instOuter args)
      (VExpr.mkApps (VExpr.wrapLams (D.map (VExpr.instL ls)) (rb.instL ls)) args) T := by
    have e : (SimplePattern.iotaRHS r.name ru.ctor r.numParams r.numMotives r.numMinors
        r.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply ls m2 =
        VExpr.mkApps (VExpr.wrapLams (D.map (VExpr.instL ls)) (rb.instL ls)) args := happly
    rw [e] at hpat
    exact hpat
  exact ⟨T, hred.trans (hsim T hred.hasType.2)⟩

end Lean4Lean.VEnv
