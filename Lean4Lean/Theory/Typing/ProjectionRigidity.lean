import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.PatsIota
import Lean4Lean.Theory.Typing.Strong

/-! Rigidity of registered structure heads and of inductive type formers, from declaration
history.

A constant is rigid (`VEnv.Rigid`) when no definitional axiom and no registered pattern is
headed by it. Every rule head of a well-formed environment is a declared constant: a
definitional axiom is closed and typed (`HasType.head_const_lookup`), a pattern is an ι redex
headed by a recursor constant (`VEnv.PatsIota`). So a fresh name is rigid
(`VEnv.WF.rigid_of_absent`), and rigidity of a declared constant survives every declaration
step, since each step adds rules headed by names fresh at that step (`VEnv.Rigid.step`). The
history induction then gives rigidity of every projection-registered structure and its
constructor (`VEnv.WF.projectionRigid`) and of every type former and constructor of an
inductive declaration of the history (`VEnv.WF'.inductTypeRigid`, `inductCtorRigid`).

This proof requires no injectivity, uniqueness, or confluence theorem. -/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- A constant at the head of a typed expression, after leading lambdas are
removed, must be declared in the environment. -/
theorem HasType.head_const_lookup (henv : env.OrderedStrong)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {e type : VExpr} (H : env.HasType U Γ e type)
    (hhead : e.stripLams.getAppFnArgs.1 = .const name levels) :
    ∃ ci, env.constants name = some ci := by
  induction e generalizing Γ type with
  | const n ls =>
    have heq : n = name ∧ ls = levels := by simpa [VExpr.stripLams] using hhead
    rcases heq with ⟨hn, hls⟩
    subst n
    rcases H.const_inv henv hΓ with ⟨ci, hci, _⟩
    exact ⟨ci, hci⟩
  | app fn arg ihfn _ =>
    rcases H.app_inv henv hΓ with ⟨A, B, hf, _⟩
    have hh : fn.getAppFnArgs.1 = .const name levels := by
      simpa [VExpr.stripLams] using hhead
    exact ihfn hΓ hf (by rw [VExpr.stripLams_of_head_const hh]; exact hh)
  | lam domain body _ ihbody =>
    rcases H.lam_inv henv hΓ with ⟨hdomain, type', hbody⟩
    exact ihbody (Γ := domain :: Γ) ⟨hΓ, hdomain⟩ hbody hhead
  | bvar | sort | proj | forallE => cases hhead

/-! ### Pattern heads -/

theorem _root_.Lean4Lean.Pattern.headConst_varN (p : Pattern) :
    ∀ n, (p.varN n).headConst = p.headConst
  | 0 => rfl
  | n + 1 => Pattern.headConst_varN p n

/-- The head of an ι redex pattern is its recursor. -/
@[simp] theorem _root_.Lean4Lean.SimplePattern.iota_headConst (r : Name) (m : Nat) (c : Name)
    (n : Nat) : (SimplePattern.iota r m c n).toPattern.headConst = r := by
  simp [SimplePattern.toPattern, Pattern.headConst, Pattern.headConst_varN]

/-- The head of a term matching a pattern is the pattern's head constant, at the
pattern's level match. -/
theorem _root_.Lean4Lean.Pattern.Matches.getAppFnArgs_fst {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) : e.getAppFnArgs.1 = .const p.headConst m1 := by
  induction H with
  | const => rfl
  | var _ ih => simpa [VExpr.getAppFnArgs_app, Pattern.headConst] using ih
  | app _ _ ih _ => simpa [VExpr.getAppFnArgs_app, Pattern.headConst] using ih

/-- Every pattern of a well-formed environment is headed by a declared constant. -/
theorem WF.pat_head_declared (henv : env.WF) {p : Pattern} {r : p.RHS × p.Check}
    (hp : env.pats p r) : ∃ c, env.constants p.headConst = some c := by
  obtain ⟨recN, M, ctorN, N, c, rfl, hc, -⟩ := henv.patsIota.shape hp
  exact ⟨c, by simpa using hc⟩

/-- Every definitional axiom of a well-formed environment headed by a constant has that
constant declared. -/
theorem WF.defeq_head_declared (henv : env.WF) {df : VDefEq} (hdf : env.defeqs df)
    (hhead : df.lhs.stripLams.getAppFnArgs.1 = .const name levels) :
    ∃ ci, env.constants name = some ci :=
  (henv.ordered.defEqWF hdf).1.head_const_lookup henv.orderedStrong (Γ := []) ⟨⟩ hhead

/-- A name not declared in a well-formed environment heads none of its rules. -/
theorem WF.rigid_of_absent (henv : env.WF) (habsent : env.constants name = none) :
    env.Rigid name where
  defeqs df hdf levels hhead := by
    obtain ⟨ci, hci⟩ := henv.defeq_head_declared hdf hhead
    rw [habsent] at hci; cases hci
  pats p r hp heq := by
    obtain ⟨c, hc⟩ := henv.pat_head_declared hp
    rw [heq, habsent] at hc; cases hc

/-- Rigidity reads only the rules. -/
theorem Rigid.of_eq {env env' : VEnv} {c : Name} (H : env.Rigid c)
    (hd : env'.defeqs = env.defeqs) (hp : env'.pats = env.pats) : env'.Rigid c where
  defeqs df hdf := by rw [hd] at hdf; exact H.defeqs df hdf
  pats p r hpr := by rw [hp] at hpr; exact H.pats p r hpr

theorem Rigid.addProjections {entries : List VProjectionEntry} (H : env.Rigid c) :
    (env.addProjections entries).Rigid c :=
  H.of_eq (addProjections_defeqs _ _) (addProjections_pats _ _)

theorem Rigid.addConst {env env' : VEnv} (H : env.Rigid c) (h : env.addConst n ci = some env') :
    env'.Rigid c :=
  H.of_eq (addConst_defeqs h) (addConst_pats h)

/-- Adding a definitional axiom headed by a constant other than `c` keeps `c` rigid. -/
theorem Rigid.addDefEq {df : VDefEq} (H : env.Rigid c)
    (hne : ∀ levels, df.lhs.stripLams.getAppFnArgs.1 ≠ .const c levels) :
    (env.addDefEq df).Rigid c where
  defeqs df' hdf' levels := by
    rcases hdf' with rfl | hdf'
    · exact hne levels
    · exact H.defeqs df' hdf' levels
  pats p r hp := H.pats p r hp

/-- The defining equation of a constant other than `c` keeps `c` rigid. -/
theorem Rigid.addDefEq_toDefEq {ci : VDefVal} (H : env.Rigid c) (hne : ci.name ≠ c) :
    (env.addDefEq ci.toDefEq).Rigid c :=
  H.addDefEq fun _ h => by
    simp [VDefVal.toDefEq, VExpr.stripLams] at h
    exact hne h.1

/-- The defining equations of constants other than `c` keep `c` rigid. -/
theorem Rigid.addDefEqs {env : VEnv} {c : Name} : ∀ {cis : List VDefVal}, env.Rigid c →
    (∀ ci ∈ cis, ci.name ≠ c) → (env.addDefEqs cis).Rigid c
  | [], H, _ => H
  | ci :: cis, H, hne => by
    show ((env.addDefEq ci.toDefEq).addDefEqs cis).Rigid c
    exact Rigid.addDefEqs (H.addDefEq_toDefEq (hne ci (.head _))) fun c' h => hne c' (.tail _ h)

/-- A declaration step keeps a declared constant rigid: the rules it adds are headed by
names fresh at that step (a definition's own name, `Quot.lift`, the new recursors). -/
theorem Rigid.step {env env' : VEnv} {d : VDecl} {c : Name} {ci : VConstant}
    (H : env.Rigid c) (hc : env.constants c = some ci) (hstep : VDecl.WF env d env') :
    env'.Rigid c := by
  have hne_of_fresh : ∀ {n}, env.constants n = none → n ≠ c := fun hn heq => by
    rw [heq, hc] at hn; cases hn
  cases hstep with
  | «axiom» _ h2 | «opaque» _ h2 => exact H.addConst h2
  | «example» _ => exact H
  | @«def» _ _ ci' _ h2 => exact (H.addConst h2).addDefEq_toDefEq (hne_of_fresh (addConst_fresh h2))
  | mutualDef _ h1 _ =>
    have fresh := addConst_foldlM_fresh (nm := fun c : VDefVal => c.name)
      (ci := fun c : VDefVal => c.toVConstant) h1
    exact (H.of_eq (addConsts_defeqs h1) (addConsts_pats h1)).addDefEqs
      fun c' hc' => hne_of_fresh (fresh c' hc')
  | quot h1 h2 =>
    obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
    have hlift : env.constants ``Quot.lift = none :=
      ((addConst_le a1).trans (addConst_le a2)).constants_eq_none_left (addConst_fresh a3)
    refine ((((H.addConst a1).addConst a2).addConst a3).addConst a4).addDefEq fun levels h => ?_
    have : quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift [.param 0, .param 1] := rfl
    rw [this] at h
    exact hne_of_fresh hlift (VExpr.const.inj h).1
  | induct _ h2 =>
    refine ⟨fun df hdf => ?_, fun p r hp heq => ?_⟩
    · rw [addInduct_defeqs h2] at hdf; exact H.defeqs df hdf
    · rcases addInduct_pats_origin h2 hp with hold | ⟨rec, hrec, ru, hru, rfl⟩
      · exact H.pats p r hold heq
      · rw [SimplePattern.iota_headConst] at heq
        exact hne_of_fresh (addInduct_rec_fresh h2 hrec) heq

/-- A name fresh before a well-formed inductive declaration, and distinct from its recursors,
is rigid after it: the declaration adds no definitional axiom, and its patterns are headed by
its recursors. -/
theorem WF.addInduct_rigid_of_fresh {env env' : VEnv} {decl : VInductDecl} {n : Name}
    (henv : env.WF) (hadd : env.addInduct decl = some env')
    (habsent : env.constants n = none) (hrecs : ∀ rec ∈ decl.recs, rec.name ≠ n) :
    env'.Rigid n where
  defeqs df hdf := by rw [addInduct_defeqs hadd] at hdf; exact (henv.rigid_of_absent habsent).defeqs df hdf
  pats p r hp heq := by
    rcases addInduct_pats_origin hadd hp with hold | ⟨rec, hrec, ru, hru, rfl⟩
    · exact (henv.rigid_of_absent habsent).pats p r hold heq
    · rw [SimplePattern.iota_headConst] at heq
      exact hrecs rec hrec heq

/-- Each `VDecl.WF` step either leaves `projections` unchanged or is the `addInduct` of a
well-formed declaration. -/
theorem _root_.Lean4Lean.VDecl.WF.projections_eq_or_induct {env d env'}
    (h : VDecl.WF env d env') :
    env'.projections = env.projections ∨
      ∃ decl, decl.WF env ∧ env.addInduct decl = some env' := by
  cases h with
  | «axiom» _ h2 | «opaque» _ h2 => exact .inl (addConst_projections h2)
  | «def» _ h2 => exact .inl (by rw [addDefEq_projections]; exact addConst_projections h2)
  | mutualDef _ h2 _ => exact .inl (by rw [addDefEqs_projections]; exact addConsts_projections h2)
  | «example» _ => exact .inl rfl
  | quot _ h2 => exact .inl (addQuot_projections h2)
  | induct h1 h2 => exact .inr ⟨_, h1, h2⟩

/-! ### Rigidity of registered structures -/

private def ProjectionRigid (env : VEnv) : Prop :=
  ∀ name info, env.projections name info → env.Rigid name ∧ env.Rigid info.ctorName

private theorem projectionRigid_aux : ∀ {ds : List VDecl} {env : VEnv}, VEnv.WF' ds env →
    ProjectionRigid env := by
  intro ds env H
  induction H with
  | empty => intro _ _ h; cases h
  | @decl d env' ds env hd H ih =>
    have henv : env.WF := ⟨ds, H⟩
    intro name info hinfo
    rcases hd.projections_eq_or_induct with heq | ⟨decl, hwf, hadd⟩
    · rw [heq] at hinfo
      obtain ⟨h1, h2⟩ := ih name info hinfo
      obtain ⟨c1, hc1⟩ := henv.ordered.projectionConstant hinfo
      exact ⟨h1.step hc1 hd, h2.step (henv.ordered.projectionConstructor hinfo) hd⟩
    · rcases (addInduct_projections_iff hadd).1 hinfo with ⟨entry, hentry, rfl, rfl⟩ | hold
      · obtain ⟨type, htype, ctor, hctors, rfl⟩ := VInductDecl.projectionEntries_origin hentry
        have hctor : ctor ∈ type.ctors := by rw [hctors]; exact List.mem_singleton_self _
        exact ⟨henv.addInduct_rigid_of_fresh hadd (addInduct_type_fresh hadd htype)
            fun rec hrec => addInduct_rec_ne_type hadd hrec htype,
          henv.addInduct_rigid_of_fresh hadd (addInduct_ctor_fresh hadd htype hctor)
            fun rec hrec => addInduct_rec_ne_ctor hadd hrec htype hctor⟩
      · obtain ⟨h1, h2⟩ := ih name info hold
        obtain ⟨c1, hc1⟩ := henv.ordered.projectionConstant hold
        exact ⟨h1.step hc1 hd, h2.step (henv.ordered.projectionConstructor hold) hd⟩
  | @inductProjections baseDecls ds base envTypes envCtors decl block
      hbase _ _ _ _ _ _ _ htypesSource hctorsSource hprojections htypes hctors ihBase ihCtors =>
    intro name info hinfo
    rw [VEnv.addProjections_iff] at hinfo
    rcases hinfo with ⟨entry, hentry, rfl, rfl⟩ | hold
    · rw [hprojections] at hentry
      obtain ⟨type, htype, ctor, hctor, rfl⟩ := VInductDecl.projectionEntries_origin hentry
      have hbaseWF : base.WF := ⟨baseDecls, hbase⟩
      have hfreshT : base.constants type.name = none :=
        VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
          rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      have hc : ctor ∈ block.ctors := by
        rw [hctorsSource]
        exact List.mem_flatMap.mpr ⟨type, htype, by rw [hctor]; exact List.mem_singleton_self _⟩
      have hfreshC : base.constants ctor.name = none :=
        (VEnv.addConstVals_le htypes).constants_eq_none_left
          (VEnv.addConstVals_names_fresh hctors ctor hc)
      have hd : (envCtors.addProjections block.projections).defeqs = base.defeqs := by
        rw [addProjections_defeqs, VEnv.addConstVals_defeqs hctors, VEnv.addConstVals_defeqs htypes]
      have hp : (envCtors.addProjections block.projections).pats = base.pats := by
        rw [addProjections_pats, VEnv.addConstVals_pats hctors, VEnv.addConstVals_pats htypes]
      exact ⟨(hbaseWF.rigid_of_absent hfreshT).of_eq hd hp,
        (hbaseWF.rigid_of_absent hfreshC).of_eq hd hp⟩
    · obtain ⟨h1, h2⟩ := ihCtors name info hold
      exact ⟨h1.addProjections, h2.addProjections⟩

/-- Registered structure heads remain rigid through every declaration
extension. -/
theorem WF.projectionRigid {env : VEnv} (H : env.WF)
    {name : Name} {info : VProjectionInfo} (hinfo : env.projections name info) :
    env.Rigid name :=
  (projectionRigid_aux H.choose_spec name info hinfo).1

/-- The constructor of a registered structure remains rigid through every declaration
extension. -/
theorem WF.projectionCtorRigid {env : VEnv} (H : env.WF)
    {name : Name} {info : VProjectionInfo} (hinfo : env.projections name info) :
    env.Rigid info.ctorName :=
  (projectionRigid_aux H.choose_spec name info hinfo).2

/-! ### Rigidity of inductive type formers and constructors -/

private theorem inductRigid_aux : ∀ {ds : List VDecl} {env : VEnv}, VEnv.WF' ds env →
    ∀ decl, VDecl.induct decl ∈ ds → ∀ t ∈ decl.types,
      (env.Rigid t.name ∧ ∃ ci, env.constants t.name = some ci) ∧
      ∀ c ∈ t.ctors, env.Rigid c.name ∧ ∃ ci, env.constants c.name = some ci := by
  intro ds env H
  induction H with
  | empty => intro _ h; cases h
  | @decl d env' ds env hd H ih =>
    have henv : env.WF := ⟨ds, H⟩
    intro decl hd' t ht
    rcases List.mem_cons.1 hd' with rfl | hmem
    · cases hd with
      | induct hwf hadd =>
        refine ⟨⟨henv.addInduct_rigid_of_fresh hadd (addInduct_type_fresh hadd ht)
            fun rec hrec => addInduct_rec_ne_type hadd hrec ht, _, addInduct_type_find hadd ht⟩,
          fun c hc => ⟨henv.addInduct_rigid_of_fresh hadd (addInduct_ctor_fresh hadd ht hc)
            fun rec hrec => addInduct_rec_ne_ctor hadd hrec ht hc, _, addInduct_ctor_find hadd ht hc⟩⟩
    · obtain ⟨⟨h1, c1, hc1⟩, h2⟩ := ih decl hmem t ht
      refine ⟨⟨h1.step hc1 hd, _, hd.le.constants hc1⟩, fun c hc => ?_⟩
      obtain ⟨h3, c3, hc3⟩ := h2 c hc
      exact ⟨h3.step hc3 hd, _, hd.le.constants hc3⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    intro decl hd' t ht
    obtain ⟨⟨h1, c1, hc1⟩, h2⟩ := ihCtors decl hd' t ht
    refine ⟨⟨h1.addProjections, _, by simpa using hc1⟩, fun c hc => ?_⟩
    obtain ⟨h3, c3, hc3⟩ := h2 c hc
    exact ⟨h3.addProjections, _, by simpa using hc3⟩

/-- A type former of an inductive declaration of a well-formed history is rigid. -/
theorem WF'.inductTypeRigid {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {decl : VInductDecl} (hd : VDecl.induct decl ∈ ds) {t : VInductiveType} (ht : t ∈ decl.types) :
    env.Rigid t.name :=
  ((inductRigid_aux H decl hd t ht).1).1

/-- A constructor of an inductive declaration of a well-formed history is rigid. -/
theorem WF'.inductCtorRigid {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {decl : VInductDecl} (hd : VDecl.induct decl ∈ ds) {t : VInductiveType} (ht : t ∈ decl.types)
    {c : VConstVal} (hc : c ∈ t.ctors) : env.Rigid c.name :=
  ((inductRigid_aux H decl hd t ht).2 c hc).1

end VEnv
end Lean4Lean
