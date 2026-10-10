import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Rules.IotaPatTyped
import Lean4Lean.Theory.Typing.RestorationShapes

/-! # The restored rules are the restored generated equations, count for count

Every rule `ru` of a restored recursor `r` is read off a block equation `df`
(`VInductDecl.RecsOf`, `VRecRule.OfEquation`), which is the restoration of a generated
equation of the lowered run's generator (`CompilationData.equations`). `OfEquation` only
records sums of counts (the major index, the constructor's argument count); this file
recovers the split the ι rule needs (`r.numParams + r.numMotives + r.numMinors` leading
arguments, `r.numIndices` indices, `ru.ctorParams` constructor parameters, `ru.nfields`
fields) from the shape of the restored equation, the restored recursor type (`rec_shape`'s
arity and motive application) and the reduct's λ-arity (`rule_shape`), and states the restored
equation in the λ-wrapped form of `VEnv.patTyped_iota_of_wrapped`
(`RestoredBlock.ruleEquation`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace InductiveSignature

theorem Restoration.expr_wrapLams (r : Restoration) (doms : List VExpr) (body : VExpr) :
    r.expr (VExpr.wrapLams doms body) =
      (doms.mapM r.expr).bind fun doms' =>
        (r.expr body).map (VExpr.wrapLams doms') := by
  induction doms with
  | nil => cases hb : r.expr body <;> simp [VExpr.wrapLams, hb]
  | cons d ds ih =>
    change Restoration.expr.go r (.lam d (VExpr.wrapLams ds body)) [] = _
    simp only [Restoration.expr.go, List.mapM_cons]
    rw [← Restoration.expr_eq_go, ← Restoration.expr_eq_go, ih]
    cases hd : r.expr d <;> cases hds : ds.mapM r.expr <;>
      cases hb : r.expr body <;> simp [VExpr.mkApps, VExpr.wrapLams]

theorem vars_bvars (n below : Nat) : ∀ e ∈ vars n below, ∃ i, e = .bvar i := by
  simp only [vars, List.mem_map]
  rintro e ⟨a, _, rfl⟩
  exact ⟨_, rfl⟩

theorem mapM_some_length {α β : Type _} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : l'.length = l.length :=
  (List.Forall₂.length_eq (List.mapM_eq_some.mp h)).symm

/-- Restoration of a constructor application whose parameter and field arguments are
variables: the restored constructor (`headName`) applied to restored parameters and the same
field variables, when every restoration head of that name takes exactly those parameters. -/
theorem Restoration.expr_ctorApp {r : Restoration} {c : Name} {ls : List VLevel}
    {pre post : List VExpr} {out : VExpr}
    (hpre : ∀ e ∈ pre, ∃ i, e = .bvar i) (hpost : ∀ e ∈ post, ∃ i, e = .bvar i)
    (hnp : ∀ h, r.heads.find? (fun h => h.auxiliary == c) = some h → h.nparams = pre.length)
    (h : r.expr (VExpr.mkApps (.const c ls) (pre ++ post)) = some out) :
    ∃ lv cps, out = VExpr.mkApps (.const (r.headName c) lv) (cps ++ post) := by
  rw [Restoration.expr_mkApps, r.mapM_expr_bvars _ (by
      intro e he
      rcases List.mem_append.1 he with he | he
      exacts [hpre e he, hpost e he])] at h
  simp only [Option.bind_some, Restoration.expr.go] at h
  unfold Restoration.headName
  split at h
  · next hd hf =>
    simp only [hf]
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      rw [hnp hd hf, List.drop_left]
      exact ⟨_, _, rfl⟩
  · next hf =>
    simp only [hf]
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨ls, pre, rfl⟩

/-- Restoration of an ι left-hand side `rec pre idx (c cpre post)` whose recursor is not a
restoration head and whose variable arguments are variables. -/
theorem Restoration.expr_iotaLhs {r : Restoration} {recN c : Name} {lsR lsC : List VLevel}
    {pre idx cpre post : List VExpr} {out : VExpr}
    (hrec : r.heads.find? (fun h => h.auxiliary == recN) = none)
    (hpre : ∀ e ∈ pre, ∃ i, e = .bvar i) (hcpre : ∀ e ∈ cpre, ∃ i, e = .bvar i)
    (hpost : ∀ e ∈ post, ∃ i, e = .bvar i)
    (hnp : ∀ h, r.heads.find? (fun h => h.auxiliary == c) = some h → h.nparams = cpre.length)
    (h : r.expr (VExpr.mkApps (.const recN lsR)
      (pre ++ idx ++ [VExpr.mkApps (.const c lsC) (cpre ++ post)])) = some out) :
    ∃ idx' lv cps, idx'.length = idx.length ∧
      out = VExpr.mkApps (.const (r.recursorName recN) lsR)
        (pre ++ idx' ++ [VExpr.mkApps (.const (r.headName c) lv) (cps ++ post)]) := by
  rw [Restoration.expr_mkApps, List.mapM_append, List.mapM_append,
    r.mapM_expr_bvars pre hpre] at h
  cases hidx : idx.mapM r.expr with
  | none => simp [hidx] at h
  | some idx' =>
    cases hmaj : r.expr (VExpr.mkApps (.const c lsC) (cpre ++ post)) with
    | none => simp [hidx, hmaj, List.mapM_cons] at h
    | some maj =>
      obtain ⟨lv, cps, rfl⟩ := Restoration.expr_ctorApp hcpre hpost hnp hmaj
      simp only [hidx, hmaj, List.mapM_cons, List.mapM_nil] at h
      simp [Restoration.expr.go, hrec] at h
      exact ⟨idx', lv, cps, mapM_some_length hidx, by rw [← h, List.append_assoc]⟩

theorem compilationRestoration_heads_nparams {source : VInductDecl}
    {auxiliaries : List ContainerSpecialization} :
    ∀ h ∈ (compilationRestoration source auxiliaries).heads, h.nparams = source.nparams := by
  intro h hh
  simp only [compilationRestoration, List.mem_flatMap, ContainerSpecialization.heads,
    List.mem_cons, List.mem_map] at hh
  obtain ⟨a, -, rfl | ⟨ctor, -, rfl⟩⟩ := hh <;> rfl

/-- A generated recursor name is not a restoration head: the heads are the auxiliary families
and their constructors, names of the expanded declaration, from which the generated recursor
names are distinct (`CompilationData.generatedNames`). -/
theorem CompilationData.recursorName_not_head {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block) (owner : Fin s.families.size) :
    (compilationRestoration source auxiliaries).heads.find?
      (fun h => h.auxiliary == g.recursorName owner) = none := by
  apply Restoration.heads_find?_eq_none
  intro hmem
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  rw [compilationRestoration_heads_names (H.model.nparams.trans H.nparams) hdirect] at hmem
  have hnames := RestoresFamily.familyNames hfamilies
  have hnd : (expanded.sourceNames ++ g.recursors.map (·.name)).Nodup := by
    simpa only [VInductDecl.sourceNames, List.map_append, List.append_assoc] using
      H.generatedNames
  have he : g.recursorName owner ∈ familyNames expanded.types := by
    rw [← H.model.familyNames, hnames]
    simpa only [familyNames, List.flatMap_append] using
      List.mem_append_right (familyNames source.types) hmem
  have he' : g.recursorName owner ∈ expanded.sourceNames := by
    have := (familyNames_perm expanded.types).mem_iff.mp he
    simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
      using this
  have hr : g.recursorName owner ∈ g.recursors.map (·.name) :=
    List.mem_map.2 ⟨g.recursor owner,
      List.mem_map.2 ⟨owner, List.mem_finRange _, rfl⟩, rfl⟩
  exact (List.nodup_append.mp hnd).2.2 _ he' _ hr rfl

end InductiveSignature

namespace VExpr

theorem lamArity_wrapLams (doms : List VExpr) (body : VExpr) :
    (VExpr.wrapLams doms body).lamArity = doms.length + body.lamArity := by
  induction doms with
  | nil => simp [VExpr.wrapLams]
  | cons d ds ih =>
    show (VExpr.lam d (VExpr.wrapLams ds body)).lamArity = _
    simp only [VExpr.lamArity, ih, List.length_cons]; omega

theorem lamBody_wrapLams_of_lamArity (doms : List VExpr) {body : VExpr}
    (h : body.lamArity = 0) : (VExpr.wrapLams doms body).lamBody = body := by
  induction doms with
  | nil => cases body <;> simp_all [VExpr.wrapLams, VExpr.lamBody, VExpr.lamArity]
  | cons d ds ih => exact ih

theorem piArity_wrapForalls (doms : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls doms body).piArity = doms.length + body.piArity := by
  induction doms with
  | nil => simp [VExpr.wrapForalls]
  | cons d ds ih =>
    show (VExpr.forallE d (VExpr.wrapForalls ds body)).piArity = _
    simp only [VExpr.piArity, ih, List.length_cons]; omega

theorem piBody_wrapForalls (doms : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls doms body).piBody = body.piBody := by
  induction doms with
  | nil => rfl
  | cons d ds ih => exact ih

theorem mkApps_spine_arity : ∀ (args : List VExpr) {f : VExpr},
    (∀ A b, f ≠ .lam A b) → (∀ A b, f ≠ .forallE A b) →
    (VExpr.mkApps f args).lamArity = 0 ∧ (VExpr.mkApps f args).piArity = 0 ∧
      (VExpr.mkApps f args).piBody = VExpr.mkApps f args
  | [], f, hl, hp => by
    cases f <;> simp_all [VExpr.mkApps, VExpr.lamArity, VExpr.piArity, VExpr.piBody]
  | a :: as, f, _, _ => by
    rw [VExpr.mkApps_cons]
    exact mkApps_spine_arity as (by intros; exact VExpr.noConfusion)
      (by intros; exact VExpr.noConfusion)

theorem mkApps_bvar_spine (i : Nat) (args : List VExpr) :
    (VExpr.mkApps (.bvar i) args).lamArity = 0 ∧ (VExpr.mkApps (.bvar i) args).piArity = 0 ∧
      (VExpr.mkApps (.bvar i) args).piBody = VExpr.mkApps (.bvar i) args :=
  mkApps_spine_arity args (by intros; exact VExpr.noConfusion)
    (by intros; exact VExpr.noConfusion)

theorem mkApps_const_spine (c : Name) (ls : List VLevel) (args : List VExpr) :
    (VExpr.mkApps (.const c ls) args).lamArity = 0 :=
  (mkApps_spine_arity args (by intros; exact VExpr.noConfusion)
    (by intros; exact VExpr.noConfusion)).1

end VExpr

open InductiveSignature

namespace VerifyInductive
namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- **Every restored rule is a restored generated equation in λ-wrapped ι form**, with the
counts of the rule and of its recursor. -/
theorem ruleEquation (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    {r : VRecursor} {ru : VRecRule} (hr : r ∈ B.decl.recs) (hru : ru ∈ r.rules) :
    ∃ df ∈ B.block.rules, ∃ (D : List VExpr) (T : VExpr) (idx cps : List VExpr)
      (lv : List VLevel),
      D.length = r.numParams + r.numMotives + r.numMinors + ru.nfields ∧
      idx.length = r.numIndices ∧ cps.length = ru.ctorParams ∧
      df.lhs = VExpr.wrapLams D (VExpr.mkApps (.const r.name (VLevel.params df.uvars))
        (vars (r.numParams + r.numMotives + r.numMinors) ru.nfields ++ idx ++
          [VExpr.mkApps (.const ru.ctor lv) (cps ++ vars ru.nfields 0)])) ∧
      df.rhs = ru.rhs ∧ df.type = VExpr.wrapForalls D T := by
  obtain ⟨df, hdf, hof, k, hk⟩ := B.rules_ofRestoredEquation hr hru
  refine ⟨df, hdf, ?_⟩
  have H := B.compiled
  generalize hg : L.recursors.generation = g at hk H
  obtain ⟨hl, hrr, ht⟩ := Restoration.equation_parts hk
  have huv : df.uvars = g.uvars := by
    simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at hk
    obtain ⟨_, _, _, _, _, _, h⟩ := hk
    cases h; rfl
  -- the generated equation, unfolded
  have hlhs0 : (g.equation k).lhs = VExpr.wrapLams
      (g.params ++ g.motives ++ g.minors ++
        insertBinders ((L.recursors.signature.fieldTypes L.recursors.signature.constructors[k]).map (·.instL g.levels))
          (L.recursors.signature.families.size + L.recursors.signature.constructors.size))
      (VExpr.mkApps (.const (g.recursorName L.recursors.signature.constructors[k].owner) (VLevel.params g.uvars))
        (vars (L.recursors.signature.params.length + (L.recursors.signature.families.size + L.recursors.signature.constructors.size))
            L.recursors.signature.constructors[k].fields.length ++
          L.recursors.signature.constructors[k].indices.map (fun e => (e.instL g.levels).liftN
            (L.recursors.signature.families.size + L.recursors.signature.constructors.size) L.recursors.signature.constructors[k].fields.length) ++
          [VExpr.mkApps (.const L.recursors.signature.constructors[k].name g.levels)
            (vars L.recursors.signature.params.length (L.recursors.signature.families.size + L.recursors.signature.constructors.size +
              L.recursors.signature.constructors[k].fields.length + 0) ++
              vars L.recursors.signature.constructors[k].fields.length 0)])) := rfl
  obtain ⟨rb0, hrhs0⟩ : ∃ rb0, (g.equation k).rhs = VExpr.wrapLams
      (g.params ++ g.motives ++ g.minors ++
        insertBinders ((L.recursors.signature.fieldTypes L.recursors.signature.constructors[k]).map (·.instL g.levels))
          (L.recursors.signature.families.size + L.recursors.signature.constructors.size))
      (VExpr.mkApps (.bvar (L.recursors.signature.constructors[k].fields.length + L.recursors.signature.constructors.size - 1 - k.val))
        rb0) := ⟨_, rfl⟩
  obtain ⟨tb0, htype0⟩ : ∃ tb0, (g.equation k).type = VExpr.wrapForalls
      (g.params ++ g.motives ++ g.minors ++
        insertBinders ((L.recursors.signature.fieldTypes L.recursors.signature.constructors[k]).map (·.instL g.levels))
          (L.recursors.signature.families.size + L.recursors.signature.constructors.size)) tb0 := ⟨_, rfl⟩
  rw [hlhs0, Restoration.expr_wrapLams] at hl
  rw [hrhs0, Restoration.expr_wrapLams] at hrr
  rw [htype0, Restoration.expr_wrapForalls] at ht
  have hDlen0 := Instance.equationDomains_length g k
  generalize (g.params ++ g.motives ++ g.minors ++
        insertBinders ((L.recursors.signature.fieldTypes L.recursors.signature.constructors[k]).map (·.instL g.levels))
          (L.recursors.signature.families.size + L.recursors.signature.constructors.size)) = domains at hl hrr ht hDlen0
  cases hD : domains.mapM (compilationRestoration B.decl B.auxiliaries).expr with
  | none => simp [hD] at hl
  | some D =>
  simp only [hD, Option.bind_some, Option.map_eq_some_iff] at hl hrr ht
  obtain ⟨lb, hlb, hlhs⟩ := hl
  obtain ⟨rb, hrb, hrhs⟩ := hrr
  obtain ⟨T, -, htype⟩ := ht
  have hDlen : D.length = L.recursors.signature.params.length + L.recursors.signature.families.size + L.recursors.signature.constructors.size +
      L.recursors.signature.constructors[k].fields.length := (mapM_some_length hD).trans hDlen0
  -- the restored left-hand side
  have hnpS : L.recursors.signature.params.length = B.decl.nparams := by
    exact H.model.nparams.trans H.nparams
  have hnot := H.recursorName_not_head L.recursors.signature.constructors[k].owner
  obtain ⟨idx', lv, cps, hidx, rfl⟩ := Restoration.expr_iotaLhs hnot
    (vars_bvars _ _) (vars_bvars _ _) (vars_bvars _ _)
    (fun h hf => by
      rw [compilationRestoration_heads_nparams h (List.mem_of_find?_eq_some hf), vars_length,
        hnpS])
    hlb
  -- the restored right-hand side is a variable spine
  rw [Restoration.expr_mkApps_bvar] at hrb
  obtain ⟨args', -, rfl⟩ := Option.map_eq_some_iff.1 hrb
  -- what `OfEquation` reads off the restored equation
  obtain ⟨hrhsEq, hhead, hlen, major, hlast, hmh, hmlen⟩ := hof
  rw [← hlhs, VExpr.lamBody_wrapLams_of_lamArity _ (VExpr.mkApps_const_spine _ _ _)] at hhead hlen hlast
  simp only [VExpr.headConst?, VExpr.getAppFn_mkApps, VExpr.getAppFn, Option.some.injEq]
    at hhead
  simp only [VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append, List.length_append,
    vars_length, List.length_singleton, hidx, List.length_map, VRecursor.getMajorIdx] at hlen
  simp only [VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hlast
  subst hlast
  simp only [VExpr.headConst?, VExpr.getAppFn_mkApps, VExpr.getAppFn, Option.some.injEq]
    at hmh
  simp only [VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append, List.length_append,
    vars_length] at hmlen
  -- the restored recursor's type: arity and motive application
  have hmemB : r.toVConstVal ∈ B.block.recursors :=
    B.recsOf.recursors ▸ List.mem_map_of_mem hr
  have hrecs := List.mapM_eq_some.mp H.recursors
  obtain ⟨v, hv, hvr⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrecs _ hmemB
  obtain ⟨owner', -, rfl⟩ := List.mem_map.1 hv
  simp only [Restoration.recursor, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hvr
  obtain ⟨t, ht', heq⟩ := hvr
  have hrt : r.type = t := by rw [← heq]
  obtain ⟨pre, maj', hpre, -, htyp⟩ := Restoration.expr_recursorType_eq_some _ ht'
  have hpl : pre.length = L.recursors.signature.params.length + L.recursors.signature.families.size + L.recursors.signature.constructors.size +
      L.recursors.signature.families[owner'].indices.length :=
    (mapM_some_length hpre).trans (g.recursorPrefix_length owner')
  obtain ⟨hpa, -, -, j, -, -, hbody⟩ := B.rec_shape r hr
  rw [hrt, htyp, VExpr.piArity_wrapForalls] at hpa
  rw [hrt, htyp, VExpr.piBody_wrapForalls] at hbody
  simp only [Instance.recursorBody] at hpa hbody
  rw [(VExpr.mkApps_bvar_spine _ _).2.1] at hpa
  rw [(VExpr.mkApps_bvar_spine _ _).2.2] at hbody
  have hbl := congrArg (fun e => e.getAppArgs.length) hbody
  simp only [VExpr.getAppArgs_mkApps, VExpr.getAppArgs, List.nil_append, List.length_append,
    vars_length, List.length_singleton, VExpr.bvarsDesc_length] at hbl hpa
  -- the rule's reduct
  obtain ⟨j', -, A, -, -, -, hrs⟩ := B.rule_shape r hr ru hru
  have hla := hrs.1
  rw [← hrhsEq, ← hrhs, VExpr.lamArity_wrapLams, (VExpr.mkApps_bvar_spine _ _).1] at hla
  -- the counts
  simp only [List.length_map] at hidx
  have hindices : idx'.length = r.numIndices := by omega
  have hk' : L.recursors.signature.params.length + (L.recursors.signature.families.size + L.recursors.signature.constructors.size) =
      r.numParams + r.numMotives + r.numMinors := by omega
  have hnf : L.recursors.signature.constructors[k].fields.length = ru.nfields := by omega
  have hcps : cps.length = ru.ctorParams := by omega
  refine ⟨D, T, idx', cps, lv, by omega, hindices, hcps, ?_, hrhsEq, htype.symm⟩
  rw [← hlhs, huv, hhead, hmh, hk', hnf]

end RestoredBlock
end VerifyInductive
end Lean4Lean
